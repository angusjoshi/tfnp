"""Lazy-splitting variant of the cell-tree telescoping sampler.

The full tree (telescope_algo.py) splits every cell by every cut - even when
the cell lies entirely inside the kept set K(c,s), where no split is needed.
Here a cell C is split ONLY if the cut boundary actually passes through it:

  - if every sample point of C survives, run at most 2d - |active| small LPs
    to check whether any DISAGREEING pyramid meets C with positive inradius;
    if none does, C ⊆ K: keep C whole, no constraint added, no split;
  - otherwise split as in v2 (children by active pyramid index, point-less
    children revived via Chebyshev LP).

Regions stay pairwise disjoint and cover X_t by induction; each region is a
convex polytope whose description only carries the cuts that actually cut it.
The region count is the honest convex-cover-style size, lower than the
full-history cell count - never higher.

Usage: python telescope_lazy.py [quick]
"""
import sys
import numpy as np
import adversary_game as G
from common import make_ssg, fixed_point
from telescope_algo import (Cell, box_rows, pyramid_rows, chebyshev_center,
                            hitrun_cell, fw_apex_weighted, weighted_draw,
                            refill, CAP, FLOOR_TOKENS)


def region_split(cells, c, s, d, rng):
    """Split only regions the cut boundary passes through."""
    act = np.where(s != 0)[0]
    out = []
    for C in cells:
        W = s[None, :] * (C.pts - c[None, :])
        W = np.where((s != 0)[None, :], W, -np.inf)
        inK = W.max(1) >= np.abs(C.pts - c[None, :]).max(1) - 1e-12
        if inK.all():
            # every sample survives; is C entirely inside K?
            crossed = False
            for j in range(d):
                for sg in (1.0, -1.0):
                    if sg == s[j]:
                        continue          # kept pyramid, no need to test
                    s_dis = np.zeros(d); s_dis[j] = sg
                    Ar, br = pyramid_rows(c, s_dis, j, d)
                    A2 = np.vstack([C.A, Ar])
                    b2 = np.concatenate([C.b, br])
                    if chebyshev_center(A2, b2) is not None:
                        crossed = True
                        break
                if crossed:
                    break
            if not crossed:
                out.append(C)             # C ⊆ K: survives whole, unsplit
                continue
        # the cut passes through C: split by active pyramid index
        kept = C.pts[inK]
        if len(kept):
            Wk = s[None, :] * (kept - c[None, :])
            Wk = np.where((s != 0)[None, :], Wk, -np.inf)
            idx = Wk.argmax(1)
        else:
            idx = np.array([], dtype=int)
        n_par = max(len(C.pts), 1)
        for i in act:
            child_pts = kept[idx == i] if len(kept) else kept
            if len(child_pts):
                out.append(C.child(c, s, i, child_pts,
                                   C.w * len(child_pts) / n_par))
            else:
                if C.w < 1e-7:
                    continue
                Ar, br = pyramid_rows(c, s, i, d)
                A2 = np.vstack([C.A, Ar])
                b2 = np.concatenate([C.b, br])
                ctr = chebyshev_center(A2, b2)
                if ctr is not None:
                    tok = hitrun_cell(A2, b2, ctr, FLOOR_TOKENS, rng,
                                      burn=25, thin=6)
                    out.append(Cell(A2, b2, tok, C.w * 0.5 / n_par))
    leak = 0.0
    if len(out) > CAP:
        out.sort(key=lambda C: -C.w)
        leak = sum(C.w for C in out[CAP:])
        out = out[:CAP]
    tot = sum(C.w for C in out)
    for C in out:
        C.w /= tot
    return out, leak


def validate_regions(cells, cuts, d, rng):
    """Exact-rejection cross-check: leak = exact mass in no region; TV over
    region masses. Membership by each region's own constraint system."""
    R, _ = G.rejection_sample(cuts, d, rng, want=1200, cap=4e8)
    if len(R) < 400:
        return None
    counts = np.zeros(len(cells))
    unassigned = 0
    for y in R:
        hit = False
        for j, C in enumerate(cells):
            if np.all(C.A @ y >= C.b - 1e-9):
                counts[j] += 1
                hit = True
                break
        if not hit:
            unassigned += 1
    leak = unassigned / len(R)
    mR = counts / len(R)
    wP = np.array([C.w for C in cells])
    tv = 0.5 * (np.abs(mR - wP).sum() + leak)
    return leak, tv


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
    print(f"--- LAZY d={d} T={T} mode={mode} seed={seed} N={N} CAP={CAP} ---")
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
            lo, hi = G.v_interval(c, hist, d)
            menu = G.sign_menu(lo, hi)
            cands = [[]]
            for opts in menu:
                cands = [pre + [o] for pre in cands for o in opts]
            if len(cands) > 128:
                cands = [cands[i] for i in
                         rng.choice(len(cands), 128, replace=False)]
            Ssub = P[:1000]
            best, bestscore = None, (-1, -1)
            for cand in cands:
                s_c = np.array(cand)
                if not (s_c != 0).any():
                    continue
                surv_c = Ssub[G.K_ok(Ssub, c, s_c)]
                nc, _, pock = G.fresh_components(surv_c, cuts + [(c, s_c)])
                v_c = G.v_from_sign(s_c, lo, hi)
                okv = np.all(v_c >= lo - 1e-18) and np.all(v_c <= hi + 1e-18) \
                    and G.verify_pairwise(c, v_c, hist)
                if okv and (nc, pock) > bestscore:
                    bestscore = (nc, pock)
                    best = v_c
            v = best if best is not None else np.clip(np.zeros(d), lo, hi)
        hist.append((c.copy(), v.copy()))
        s_cut = np.sign(v)
        s_cut[np.abs(v) < G.TAU / 2] = 0.0
        if not (s_cut != 0).any():
            print(f"  t={t}: zero displacement, stopping")
            break
        cuts.append((c.copy(), s_cut.copy()))
        kept = G.K_ok(P, c, s_cut).mean()
        cells, leak_cap = region_split(cells, c, s_cut, d, rng)
        leak_total += leak_cap
        refill(cells, N, rng)
        ncomp = ""
        if t % comps_every == 0 or t == T:
            Pn = weighted_draw(cells, 1500, rng)
            nc, sizes, _ = G.fresh_components(Pn, cuts)
            prof = "/".join(f"{x/sizes.sum():.2f}" for x in sizes[:3])
            ncomp = f" comps={nc}[{prof}]"
        val = ""
        if t <= validate_until and (t % 3 == 0):
            r = validate_regions(cells, cuts, d, rng)
            if r is not None:
                val = f" exleak={r[0]:.3f} regTV={r[1]:.3f}"
        err = f" |c-x*|={np.abs(c - xstar).max():.4f}" if xstar is not None else ""
        wmax = max(C.w for C in cells)
        print(f"  t={t:>2} kept={kept:.3f} regions={len(cells):>5} "
              f"wmax={wmax:.3f} capleak={leak_total:.3f}{err}{val}{ncomp}",
              flush=True)
    return cuts, cells


if __name__ == "__main__":
    quick = "quick" in sys.argv[1:]
    if quick:
        run(5, 10, "ssg", 1, N=2000, validate_until=9)
    else:
        run(6, 40, "ssg", 1)
        run(6, 40, "adversary", 1)
        run(8, 24, "ssg", 1, validate_until=9)
