"""The telescoping cell-tree algorithm, end to end - the candidate
polynomial-time algorithm for l-inf contraction fixed points.

STRUCTURE. Cells of X_t form an exact TREE: a cell of X_t is (cell of
X_{t-1}) ∩ (one pyramid of the new cut), and each cell is a convex polytope
with O(d t) facets (Lean: convex_cell). The algorithm maintains the complete
list of nonempty cells with per-cell weights and sample points:

  per round:
    1. Fermat-Weber balanced apex of the weighted sample (LP) -> query.
    2. Split every tracked cell by the new cut: children that inherit sample
       points get weight ∝ counts; children with NO surviving point are
       checked nonempty by LP and REVIVED at their Chebyshev center with a
       Laplace mass floor - so no cell is ever silently lost (the v1
       telescoping sampler leaked 1-5%/round exactly this way).
    3. Refill each cell to its weight quota by hit-and-run inside the cell
       polytope (exact chords).
  cap: if #cells exceeds CAP, lowest-weight cells are dropped and their
  weight added to a DECLARED leak - the only unproven step, and its
  boundedness is precisely conjecture (*).

Cost per round: poly(d, t, #cells, N). No 2^{-t} rejection tax, so the
instrument measures PAST the exact-rejection ceiling (t <= ~14) after being
validated against exact rejection in-window (leak vs exact-sample cells,
cell-mass TV).

Oracles: "ssg" (random-SSG operator, known x* -> convergence curve),
"adversary" (the certified-realizable shattering adversary), "toward".

Usage: python telescope_algo.py [quick]
"""
import sys
import numpy as np
from scipy.optimize import linprog
import adversary_game as G
from common import make_ssg, fixed_point

CAP = 12000         # hard safety cap on tracked cells
WMIN = 2e-6         # weight-threshold pruning (mass-based, not count-based)
RATIO_K = 60        # fresh parent samples for revival-ratio estimation
RATIO_WMIN = 5e-4   # parents above this weight get ratio-estimated revivals
FLOOR_TOKENS = 4    # sample points given to a revived cell


# ---------- cell polytope machinery ----------
def pyramid_rows(c, s, i, d):
    """Constraints of pyramid i (sign s[i]) at apex c, as (A, b): A y >= b."""
    sg = s[i]
    A, b = [], []
    for j in range(d):
        if j == i:
            continue
        a1 = np.zeros(d); a1[i] = sg; a1[j] = -1.0
        A.append(a1); b.append(sg * c[i] - c[j])
        a2 = np.zeros(d); a2[i] = sg; a2[j] = 1.0
        A.append(a2); b.append(sg * c[i] + c[j])
    return A, b


def box_rows(d):
    A, b = [], []
    for i in range(d):
        e = np.zeros(d); e[i] = 1.0
        A.append(e.copy()); b.append(0.0)
        A.append(-e); b.append(-1.0)
    return A, b


class Cell:
    """A convex cell: pyramid index per cut, constraint system, points, weight."""
    __slots__ = ("A", "b", "pts", "w")

    def __init__(self, A, b, pts, w):
        self.A, self.b, self.pts, self.w = A, b, pts, w

    def child(self, c, s, i, pts, w):
        Ar, br = pyramid_rows(c, s, i, len(c))
        return Cell(np.vstack([self.A, Ar]), np.concatenate([self.b, br]),
                    pts, w)


def chebyshev_center(A, b):
    """Largest inscribed ball: max r s.t. A y - r*||a_row|| >= b. None if
    the cell is empty (or degenerate below tolerance)."""
    m, d = A.shape
    norms = np.linalg.norm(A, axis=1)
    Aub = np.hstack([-A, norms[:, None]])          # -A y + r||a|| <= -b
    res = linprog(np.concatenate([np.zeros(d), [-1.0]]), A_ub=Aub, b_ub=-b,
                  bounds=[(None, None)] * d + [(0, None)], method="highs")
    if not res.success or res.x[d] < 1e-9:
        return None
    return res.x[:d]


def hitrun_cell(A, b, start, n_new, rng, burn=60, thin=10):
    p = start.copy()
    d = len(p)
    out = []
    total = burn + n_new * thin
    for step in range(total):
        u = rng.normal(size=d)
        u /= np.linalg.norm(u)
        Au = A @ u
        Ap = A @ p
        with np.errstate(divide="ignore", invalid="ignore"):
            tb = (b - Ap) / Au
        tlo = tb[Au > 1e-13].max(initial=-np.inf)
        thi = tb[Au < -1e-13].min(initial=np.inf)
        if not (np.isfinite(tlo) and np.isfinite(thi)) or thi <= tlo:
            continue
        p = p + rng.uniform(tlo, thi) * u
        if step >= burn and (step - burn) % thin == 0:
            out.append(p.copy())
    while len(out) < n_new:
        out.append(p.copy())
    return np.array(out[:n_new])


# ---------- weighted Fermat-Weber apex ----------
def fw_apex_weighted(S, wts):
    """argmin_c sum_j w_j ||S_j - c||_inf  (weighted l-inf Fermat-Weber LP)."""
    from scipy.optimize import linprog as lp
    N, d = S.shape
    cobj = np.concatenate([np.zeros(d), wts])
    rows, rhs = [], []
    for m in range(d):
        Am = np.zeros((N, d + N)); Am[:, m] = 1.0
        Am[np.arange(N), d + np.arange(N)] = -1.0
        rows.append(Am); rhs.append(S[:, m])
        Bm = np.zeros((N, d + N)); Bm[:, m] = -1.0
        Bm[np.arange(N), d + np.arange(N)] = -1.0
        rows.append(Bm); rhs.append(-S[:, m])
    res = lp(cobj, A_ub=np.vstack(rows), b_ub=np.concatenate(rhs),
             bounds=[(None, None)] * d + [(0, None)] * N, method="highs")
    return res.x[:d]


def weighted_draw(cells, m, rng):
    """m points drawn cell ∝ w, uniform within cell: an approx-uniform
    sample of X_t regardless of per-cell point counts."""
    w = np.array([C.w for C in cells])
    w = w / w.sum()
    picks = rng.choice(len(cells), m, p=w)
    out = np.empty((m, cells[0].pts.shape[1]))
    for k, j in enumerate(picks):
        C = cells[j]
        out[k] = C.pts[rng.integers(len(C.pts))]
    return out


# ---------- the round update ----------
def split_cells(cells, c, s, d, rng):
    """Split every tracked cell by the new cut; revive point-less nonempty
    children by LP + Chebyshev center, with revival weights estimated by
    RATIO SAMPLING of the parent (fresh hit-and-run draws bucketed under the
    new cut) rather than a blind Laplace floor - this keeps the weight
    profile honest under adversarial shattering. Pruning is mass-based
    (w < WMIN), not count-based. Returns (new_cells, leak_declared)."""
    act = [int(i) for i in np.where(s != 0)[0]]
    out = []
    for C in cells:
        pts = C.pts
        if len(pts):
            W = s[None, :] * (pts - c[None, :])
            W = np.where((s != 0)[None, :], W, -np.inf)
            marks = W.max(1) >= np.abs(pts - c[None, :]).max(1) - 1e-12
            kept = pts[marks]
        else:
            kept = pts
        if len(kept):
            Wk = s[None, :] * (kept - c[None, :])
            Wk = np.where((s != 0)[None, :], Wk, -np.inf)
            idx = Wk.argmax(1)
        else:
            idx = np.array([], dtype=int)
        counts = {i: int((idx == i).sum()) for i in act}
        n_par = max(len(pts), 1)
        n_den = n_par
        fresh, fidx, fin = None, None, None
        # ratio sampling: only when a significant parent has an unseen child
        if C.w >= RATIO_WMIN and any(counts[i] == 0 for i in act) and len(pts):
            fresh = hitrun_cell(C.A, C.b, pts[rng.integers(len(pts))],
                                RATIO_K, rng, burn=40, thin=6)
            Wf = s[None, :] * (fresh - c[None, :])
            Wf = np.where((s != 0)[None, :], Wf, -np.inf)
            fin = Wf.max(1) >= np.abs(fresh - c[None, :]).max(1) - 1e-12
            fidx = Wf.argmax(1)
            for i in act:
                counts[i] += int(((fidx == i) & fin).sum())
            n_den = n_par + RATIO_K
        for i in act:
            child_pts = kept[idx == i] if len(kept) else kept
            if fresh is not None:
                fp = fresh[(fidx == i) & fin]
                if len(fp):
                    child_pts = np.vstack([child_pts, fp]) if len(child_pts) \
                        else fp
            if len(child_pts):
                w = C.w * (counts[i] if counts[i] else 0.25) / n_den
                out.append(C.child(c, s, i, child_pts, w))
            else:
                # still unseen: LP-check and revive with a small estimate
                if C.w < 1e-7:
                    continue
                Ar, br = pyramid_rows(c, s, i, d)
                A2 = np.vstack([C.A, Ar]); b2 = np.concatenate([C.b, br])
                ctr = chebyshev_center(A2, b2)
                if ctr is not None:
                    tok = hitrun_cell(A2, b2, ctr, FLOOR_TOKENS, rng,
                                      burn=25, thin=6)
                    out.append(Cell(A2, b2, tok, C.w * 0.25 / n_den))
    # mass-based pruning + hard safety cap
    leak = sum(C.w for C in out if C.w < WMIN)
    out = [C for C in out if C.w >= WMIN]
    if len(out) > CAP:
        out.sort(key=lambda C: -C.w)
        leak += sum(C.w for C in out[CAP:])
        out = out[:CAP]
    tot = sum(C.w for C in out)
    for C in out:
        C.w /= tot
    return out, leak


def refill(cells, N, rng):
    for C in cells:
        quota = max(int(round(N * C.w)), 1)
        extra = quota - len(C.pts)
        if extra > 0:
            start = C.pts[rng.integers(len(C.pts))]
            new = hitrun_cell(C.A, C.b, start, extra, rng)
            C.pts = np.vstack([C.pts, new])
        elif extra < 0:
            sel = rng.choice(len(C.pts), quota, replace=False)
            C.pts = C.pts[sel]


def pool(cells, rng, m=None):
    """Weighted sample pool: draw cells ∝ w, points within."""
    P = np.vstack([C.pts for C in cells])
    rng.shuffle(P)
    return P if m is None else P[:m]


# ---------- validation (in-window) ----------
def cell_sig(S, cuts):
    sigs = []
    for (c, s) in cuts:
        act = s != 0
        W = s[None, :] * (S - c[None, :])
        W = np.where(act[None, :], W, -np.inf)
        sigs.append(W.argmax(1))
    return np.stack(sigs, 1)


def validate(cells, cuts, d, rng):
    R, _ = G.rejection_sample(cuts, d, rng, want=2400, cap=4e8)
    if len(R) < 500:
        return None
    sigR = cell_sig(R, cuts)
    uR, invR = np.unique(sigR, axis=0, return_inverse=True)
    cR = np.bincount(invR) / len(R)
    reps = np.vstack([C.pts[:1] for C in cells])
    sigP = cell_sig(reps, cuts)
    wP = np.array([C.w for C in cells])
    keyP = {}
    for row, w in zip(sigP, wP):
        keyP[tuple(row)] = keyP.get(tuple(row), 0.0) + w
    leak = sum(m for u, m in zip(uR, cR) if tuple(u) not in keyP)
    mR = {tuple(u): m for u, m in zip(uR, cR)}
    keys = set(keyP) | set(mR)
    tv = 0.5 * sum(abs(keyP.get(k, 0.0) - mR.get(k, 0.0)) for k in keys)
    return leak, tv


# ---------- one full run ----------
def run(d, T, mode, seed, N=3000, validate_until=12, comps_every=5):
    rng = np.random.default_rng(seed)
    xstar, f = None, None
    if mode == "ssg":
        f, _ = make_ssg(d, 1e-4, seed)
        xstar = fixed_point(f, d)
    elif mode == "toward":
        xstar = rng.uniform(0.3, 0.7, size=d)
    Ab, bb = box_rows(d)
    cells = [Cell(np.array(Ab), np.array(bb), rng.random((N, d)), 1.0)]
    cuts, hist = [], []
    leak_total = 0.0
    print(f"--- d={d} T={T} mode={mode} seed={seed} N={N} CAP={CAP} ---")
    for t in range(1, T + 1):
        P = weighted_draw(cells, 3000, rng)
        Wfw = weighted_draw(cells, 350, rng)
        c = np.clip(fw_apex_weighted(Wfw, np.full(len(Wfw), 1.0 / len(Wfw))),
                    1e-6, 1 - 1e-6)
        if mode == "ssg":
            v = f(c) - c
        elif mode == "toward":
            v = (1 - G.LAM) * (xstar - c)
        else:
            # mode in {"adversary", "cellmax", "depthmax"}
            lo, hi = G.v_interval(c, hist, d)
            menu = G.sign_menu(lo, hi)
            cands = [[]]
            for opts in menu:
                cands = [pre + [o] for pre in cands for o in opts]
            if len(cands) > 128:
                cands = [cands[i] for i in
                         rng.choice(len(cands), 128, replace=False)]
            Ssub = P[:1000]
            eta = 2 * (np.abs(c - hist[-1][0]).max() if hist else 0.05)
            best, bestscore = None, None
            for cand in cands:
                s_c = np.array(cand)
                if not (s_c != 0).any():
                    continue
                surv_c = Ssub[G.K_ok(Ssub, c, s_c)]
                if len(surv_c) < 25:
                    continue
                if mode == "cellmax":
                    ncell, ent = G.cell_score(surv_c, cuts + [(c, s_c)])
                    score = (ncell, ent)
                elif mode == "depthmax":
                    A2 = np.abs(surv_c - c[None, :])
                    A2.sort(1)
                    within = (A2 >= (A2[:, -1] - eta)[:, None]).sum(1)
                    score = (float((within >= 4).mean()),
                             float((within >= 3).mean()),
                             float(within.mean()))
                else:
                    nc, _, pock = G.fresh_components(
                        surv_c, cuts + [(c, s_c)])
                    score = (nc, pock)
                v_c = G.v_from_sign(s_c, lo, hi)
                okv = np.all(v_c >= lo - 1e-18) and np.all(v_c <= hi + 1e-18) \
                    and G.verify_pairwise(c, v_c, hist)
                if okv and (bestscore is None or score > bestscore):
                    bestscore = score
                    best = v_c
            v = best if best is not None else np.clip(np.zeros(d), lo, hi)
        hist.append((c.copy(), v.copy()))
        s_cut = np.sign(v)
        s_cut[np.abs(v) < G.TAU / 2] = 0.0
        if not (s_cut != 0).any():
            print(f"  t={t}: zero displacement, stopping")
            break
        cuts.append((c.copy(), s_cut.copy()))
        kept = G.K_ok(P, c, s_cut).mean()   # P is weighted-uniform
        cells, leak_cap = split_cells(cells, c, s_cut, d, rng)
        leak_total += leak_cap
        refill(cells, N, rng)
        ncomp = ""
        if t % comps_every == 0 or t == T:
            Pn = weighted_draw(cells, 1500, rng)
            nc, sizes, _ = G.fresh_components(Pn, cuts)
            prof = "/".join(f"{x/sizes.sum():.2f}" for x in sizes[:3])
            ncomp = f" comps={nc}[{prof}]"
        val = ""
        if t <= validate_until and (t % 2 == 0):
            r = validate(cells, cuts, d, rng)
            if r is not None:
                val = f" exleak={r[0]:.3f} cellTV={r[1]:.3f}"
        err = f" |c-x*|={np.abs(c - xstar).max():.4f}" if xstar is not None else ""
        if len(hist) >= 2:
            eta_r = 2 * np.abs(hist[-1][0] - hist[-2][0]).max()
            Pd = weighted_draw(cells, 1200, rng)
            Ad = np.abs(Pd - hist[-1][0][None, :])
            Ad.sort(1)
            within = (Ad >= (Ad[:, -1] - eta_r)[:, None]).sum(1)
            err += (f" D={within.mean():.2f} m3={float((within>=3).mean()):.2f}"
                    f" m4={float((within>=4).mean()):.2f}"
                    f" m5={float((within>=5).mean()):.2f}")
        wmax = max(C.w for C in cells)
        print(f"  t={t:>2} kept={kept:.3f} cells={len(cells):>5} "
              f"wmax={wmax:.3f} capleak={leak_total:.3f}{err}{val}{ncomp}",
              flush=True)
    return cuts, cells


if __name__ == "__main__":
    quick = "quick" in sys.argv[1:]
    if quick:
        run(5, 10, "ssg", 1, N=2000, validate_until=8)
    else:
        run(6, 55, "depthmax", 1, validate_until=10)
        run(6, 55, "cellmax", 1, validate_until=10)
