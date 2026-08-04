"""Certified-realizable adversarial oracle vs the balanced-cut algorithm:
can an actual l-inf contraction shatter X_t into many components?

WHY THIS EXPERIMENT IS DIFFERENT. Every prior experiment in this repo ran the
algorithm against *random* SSG/topical instances and found X_t essentially
star-shaped (k=1-2). But the open conjecture (* in FINAL_REPORT.md) quantifies
over *realizable* trajectories, i.e. adversarial contractions. This script
plays the true game:

  ALGORITHM: exact-rejection sample X_t -> Fermat-Weber balanced apex (LP)
             -> query.
  ADVERSARY: answer with a displacement v^t whose sign vector maximises the
             number of connected components of X_t within K(c^t, s), subject to
             REALIZABILITY.

Realizability is exact, not heuristic (notes/adversarial_components.md,
Tfnp/Realizability.lean): since l-inf-valued McShane extension is coordinate-
wise, a history (c^r, v^r) is realizable by an actual lambda-contraction with
a genuine fixed point iff

  || (c^r + v^r) - (c^q + v^q) ||_inf <= lambda * || c^r - c^q ||_inf,  all r,q,

and because the norm is a max these conditions DECOUPLE PER COORDINATE: at a
new query c, the feasible v_i form an interval
  [ max_q (-lam*D_q - a_i^q + v_i^q),  min_q (lam*D_q - a_i^q + v_i^q) ],
  a^q = c - c^q,  D_q = ||a^q||_inf,
so the adversary's freedom each round is exactly a per-coordinate SIGN MENU.
Cut validity for the extension's fixed point is then guaranteed by
fixedPoint_mem_pyrUnion_apex - no explicit x* needed.

Output per round: #components of X_t (segment-checked sample graph), component
mass profile, kept fraction, sign menu size, rank of the chosen sign vector.
Control mode ("toward"): responses from the explicit contraction
f(y) = x* + lam*(y - x*); components must stay 1 (Lean: starshaped_of_toward).

Usage: python adversary_game.py [d_list]
"""
import sys
import numpy as np
from scipy.optimize import linprog
from scipy.spatial import cKDTree

LAM = 1 - 1e-9      # contraction factor (hard regime: 1-lam tiny)
RHO = 0.5           # global cap on displacement magnitude (real bound: cube)
TAU = 1e-13         # min displacement magnitude for a nonzero sign
NCHK = 9            # checkpoints per edge for segment membership
KNN = 8


# ---------- membership (progressive, vectorised) ----------
def K_ok(P, c, s):
    act = s != 0
    D = P - c[None, :]
    A = np.abs(D).max(1)
    if not act.any():
        return np.zeros(len(P), bool)  # empty union: keeps nothing
    W = np.where(act[None, :], s[None, :] * D, -np.inf).max(1)
    return W >= A - 1e-12


def in_X(P, cuts):
    """Progressive filtering: returns boolean mask on P."""
    ok = (P.min(1) >= -1e-12) & (P.max(1) <= 1 + 1e-12)
    idx = np.where(ok)[0]
    sub = P[idx]
    for (c, s) in cuts:
        m = K_ok(sub, c, s)
        idx = idx[m]
        sub = sub[m]
        if len(idx) == 0:
            break
    out = np.zeros(len(P), bool)
    out[idx] = True
    return out


def rejection_sample(cuts, d, rng, want=2200, cap=1.5e8, batch=3_000_000):
    got, drawn = [], 0
    n = 0
    while n < want and drawn < cap:
        P = rng.random((batch, d))
        drawn += batch
        keep = P[in_X(P, cuts)]
        if len(keep):
            got.append(keep)
            n += len(keep)
    if not got:
        return np.empty((0, d)), drawn
    return np.vstack(got)[:want], drawn


# ---------- Fermat-Weber balanced apex ----------
def fw_apex(S):
    N, d = S.shape
    cobj = np.concatenate([np.zeros(d), np.ones(N)])
    rows, rhs = [], []
    for m in range(d):
        Am = np.zeros((N, d + N)); Am[:, m] = 1.0
        Am[np.arange(N), d + np.arange(N)] = -1.0
        rows.append(Am); rhs.append(S[:, m])
        Bm = np.zeros((N, d + N)); Bm[:, m] = -1.0
        Bm[np.arange(N), d + np.arange(N)] = -1.0
        rows.append(Bm); rhs.append(-S[:, m])
    res = linprog(cobj, A_ub=np.vstack(rows), b_ub=np.concatenate(rhs),
                  bounds=[(None, None)] * d + [(0, None)] * N, method="highs")
    return res.x[:d]


# ---------- components of the sample graph ----------
class UF:
    def __init__(self, n):
        self.p = list(range(n))
    def find(self, x):
        while self.p[x] != x:
            self.p[x] = self.p[self.p[x]]
            x = self.p[x]
        return x
    def union(self, a, b):
        ra, rb = self.find(a), self.find(b)
        if ra != rb:
            self.p[ra] = rb


def build_graph(S, cuts):
    """kNN edges whose full segment lies in X_t; returns edges + per-edge
    checkpoint block (E, NCHK, d) for later re-filtering by a candidate cut."""
    N, d = S.shape
    tree = cKDTree(S)
    _, nn = tree.query(S, k=min(KNN + 1, N))
    pairs = set()
    for i in range(N):
        for j in nn[i][1:]:
            if i != j:
                pairs.add((min(i, int(j)), max(i, int(j))))
    E = np.array(sorted(pairs))
    ts = np.linspace(0, 1, NCHK + 2)[1:-1]
    chk = S[E[:, 0]][:, None, :] * (1 - ts)[None, :, None] \
        + S[E[:, 1]][:, None, :] * ts[None, :, None]          # (E, NCHK, d)
    flat = chk.reshape(-1, d)
    ok = in_X(flat, cuts).reshape(len(E), NCHK).all(1)
    return E[ok], chk[ok]


def comp_profile(N, E, alive_nodes, alive_edges):
    uf = UF(N)
    for (a, b), al in zip(E, alive_edges):
        if al and alive_nodes[a] and alive_nodes[b]:
            uf.union(a, b)
    roots = {}
    for i in range(N):
        if alive_nodes[i]:
            r = uf.find(i)
            roots[r] = roots.get(r, 0) + 1
    sizes = np.array(sorted(roots.values(), reverse=True))
    live = alive_nodes.sum()
    big = sizes[sizes >= max(3, 0.005 * live)] if len(sizes) else sizes
    return len(big), sizes


def fresh_components(P, cutlist):
    """Components + pocket count of P within X(cutlist): kNN graph REBUILT on
    P, edges dropped when the segment leaves the body. Returns
    (ncomp_big, sizes, n_pocket_edges)."""
    N, d = P.shape
    if N < 10:
        return 1, np.array([N]), 0
    tree = cKDTree(P)
    _, nn = tree.query(P, k=min(KNN + 1, N))
    pairs = set()
    for i in range(N):
        for j in nn[i][1:]:
            if i != j:
                pairs.add((min(i, int(j)), max(i, int(j))))
    E = np.array(sorted(pairs))
    ts = np.linspace(0, 1, NCHK + 2)[1:-1]
    chk = P[E[:, 0]][:, None, :] * (1 - ts)[None, :, None] \
        + P[E[:, 1]][:, None, :] * ts[None, :, None]
    ok = in_X(chk.reshape(-1, d), cutlist).reshape(len(E), NCHK).all(1)
    nc, sizes = comp_profile(N, E, np.ones(N, bool), ok)
    return nc, sizes, int((~ok).sum())


# ---------- realizability: per-coordinate interval + sign menu ----------
def v_interval(c, hist, d):
    lo = np.maximum(np.full(d, -RHO), -c + 1e-9)
    hi = np.minimum(np.full(d, RHO), 1 - c - 1e-9)
    for (cq, vq) in hist:
        a = c - cq
        D = np.abs(a).max()
        lo = np.maximum(lo, -LAM * D - a + vq)
        hi = np.minimum(hi, LAM * D - a + vq)
    return lo, hi


def sign_menu(lo, hi):
    """Feasible signs per coordinate: subset of {+1,-1,0}."""
    menu = []
    for l, h in zip(lo, hi):
        opts = []
        if h >= TAU:
            opts.append(1.0)
        if l <= -TAU:
            opts.append(-1.0)
        if not opts and l <= 0 <= h:
            opts.append(0.0)
        if not opts:      # numerically wedged: take whatever the interval allows
            opts.append(1.0 if h > 0 else (-1.0 if l < 0 else 0.0))
        menu.append(opts)
    return menu


MAG = 1e-4          # target displacement scale: >> (1-lam)*diam, << apex gaps


def v_from_sign(s, lo, hi):
    """Pick the displacement of magnitude ~MAG with the requested sign,
    clipped into the exact feasibility interval. MAG sits far above the
    forced pairwise increments (1-lam)*D and far below apex separations,
    so neither the far-pair pinning nor the near-pair locking triggers."""
    v = np.zeros(len(s))
    for i, si in enumerate(s):
        if si > 0:
            v[i] = min(max(MAG, lo[i] + TAU), hi[i])
        elif si < 0:
            v[i] = max(min(-MAG, hi[i] - TAU), lo[i])
        else:
            v[i] = min(max(0.0, lo[i]), hi[i])
    return v


def verify_pairwise(c, v, hist):
    for (cq, vq) in hist:
        D = np.abs(c - cq).max()
        if np.abs(c + v - cq - vq).max() > LAM * D + 1e-15:
            return False
    return True


# ---------- cell-signature scoring (mode="cellmax") ----------
def cell_score(S, cuts_plus):
    """(#distinct cells, cell-mass entropy) of S under the cut list."""
    sigs = []
    for (c, s) in cuts_plus:
        act = s != 0
        W = s[None, :] * (S - c[None, :])
        W = np.where(act[None, :], W, -np.inf)
        sigs.append(W.argmax(1))
    sig = np.stack(sigs, 1)
    _, inv = np.unique(sig, axis=0, return_inverse=True)
    counts = np.bincount(inv)
    p = counts / counts.sum()
    ent = float(-(p * np.log(p + 1e-12)).sum())
    return len(counts), ent


# ---------- one game ----------
def play(d, seed, T, mode="adversary", verbose=True):
    rng = np.random.default_rng(seed)
    cuts, hist = [], []
    xstar = rng.uniform(0.3, 0.7, size=d)   # used only in "toward" mode
    rows = []
    for t in range(1, T + 1):
        S, drawn = rejection_sample(cuts, d, rng)
        if len(S) < 300:
            if verbose:
                print(f"  t={t}: sampler exhausted ({len(S)} pts / {drawn:.0f} draws)")
            break
        ncomp, sizes, npock = fresh_components(S, cuts)
        c = np.clip(fw_apex(S[:400]), 1e-6, 1 - 1e-6)
        if mode == "free":
            lo = np.full(d, -1e-4)
            hi = np.full(d, 1e-4)
        else:
            lo, hi = v_interval(c, hist, d)
        menu = sign_menu(lo, hi)
        menu_size = int(np.prod([len(m) for m in menu]))
        if mode == "toward":
            v = (1 - LAM) * (xstar - c)
            s = np.sign(v)
            rank, best_next = 0, None
        elif mode == "randbal":
            # random balanced sign vector, realizability-clipped
            lo, hi = v_interval(c, hist, d)
            perm = rng.permutation(d)
            s = np.ones(d)
            s[perm[: d // 2]] = -1.0
            v = v_from_sign(s, lo, hi)
            rank, best_next, menu_size = 0, None, 0
        else:
            # enumerate the sign menu; score each candidate on a FRESH survivor
            # graph (mode="adversary": component count; mode="cellmax": cell
            # count + entropy - the (*)-falsification objective)
            cands = [[]]
            for opts in menu:
                cands = [pre + [o] for pre in cands for o in opts]
            if len(cands) > 256:
                cands = [cands[i] for i in
                         rng.choice(len(cands), 256, replace=False)]
            Ssub = S[:1400]
            scored = []
            for cand in cands:
                s_c = np.array(cand)
                if not (s_c != 0).any():
                    continue
                surv = Ssub[K_ok(Ssub, c, s_c)]
                kept = len(surv) / len(Ssub)
                if mode == "cellmax":
                    if len(surv) < 20:
                        continue
                    ncell, ent = cell_score(surv, cuts + [(c, s_c)])
                    scored.append((ncell, ent, 0.0, -abs(kept - 0.5), kept, s_c))
                else:
                    nc, sz, pock = fresh_components(surv, cuts + [(c, s_c)])
                    ent = 0.0
                    if len(sz) and sz.sum() > 0:
                        p = sz / sz.sum()
                        ent = float(-(p * np.log(p + 1e-12)).sum())
                    scored.append((nc, pock, ent, -abs(kept - 0.5), kept, s_c))
            scored.sort(key=lambda x: (-x[0], -x[1], -x[2], -x[3]))
            rank = 0
            s, v, best_next = None, None, -1
            for cand in scored:
                s_c = cand[5]
                v_c = v_from_sign(s_c, lo, hi)
                if mode == "free" or (np.all(v_c >= lo - 1e-18)
                        and np.all(v_c <= hi + 1e-18)
                        and verify_pairwise(c, v_c, hist)):
                    s, v = s_c, v_c
                    best_next = (cand[0], cand[1])
                    break
                rank += 1
            if s is None:   # total wedge: fall back to the McShane value
                v = np.clip(np.zeros(d), lo, hi)
                s = np.sign(v)
        hist.append((c.copy(), v.copy()))
        s_cut = np.sign(v)
        s_cut[np.abs(v) < TAU / 2] = 0.0
        cuts.append((c.copy(), s_cut.copy()))
        kept_frac = K_ok(S, c, s_cut).mean()
        top = "/".join(f"{x/ max(1,sizes.sum()):.2f}" for x in sizes[:4])
        rows.append((t, len(S), ncomp, npock, kept_frac, menu_size, rank))
        if verbose:
            print(f"  t={t:>2} N={len(S):>5} comps={ncomp:>3} pockets={npock:>4} "
                  f"sizes[{top}] kept={kept_frac:.3f} menu={menu_size:>4} "
                  f"rank={rank} next={best_next}")
    return rows, cuts


def main():
    args = sys.argv[1:]
    free = "free" in args
    ds = [int(x) for x in args if x.isdigit()] or [4, 5, 6]
    for d in ds:
        T = min(int(2.5 * d), 14)
        if free:
            for seed in (1, 2, 3):
                print(f"=== d={d} seed={seed} FREE adversary, no realizability "
                      f"(T={T}) ===")
                play(d, seed=seed, T=T, mode="free")
        else:
            print(f"=== d={d} control (toward-oracle): components must stay 1 ===")
            play(d, seed=100 + d, T=T, mode="toward")
            for seed in (1, 2):
                print(f"=== d={d} seed={seed} ADVERSARY (T={T}) ===")
                play(d, seed=seed, T=T, mode="adversary")


if __name__ == "__main__":
    main()
