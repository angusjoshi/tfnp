"""The (liveness, progress) Pareto frontier over apexes, on realizable X_t.

Theory (notes/progress_convexity.md, Tfnp/Progress.lean):
  L(c) = # live coordinates at c (coordinates attaining the l-inf argmax on X);
  p(c) = worst-case removal = sum_m min(n_m^+, n_m^-) / N   (minority count).

  * L(c) <= 2  =>  the retained region lies in a HALFSPACE => the round is
    convex and poly-time (cut_inter_subset_halfspace).
  * L(c) >= 3  =>  conv(K) = R^d; no convex/quasiconcave relaxation loses a
    single point (eq_univ_of_convex_of_three, le_of_quasiconcave_majorant),
    and the convex cover number of the cut is exactly L (>= 3).
  * p(c) = 1/2 exactly at a balanced apex (card_removed_le_sum_min).

So a poly-time round needs an apex with L <= 2 AND p >= 1/poly.  This searches
the apex space for one: balanced apex, the anisotropic construction, apexes
pulled toward each coordinate axis, and random apexes -- reporting for each
round the best progress attainable at each liveness level.

Usage: python live_progress_pareto.py
"""
import numpy as np
from common import make_ssg, fixed_point, make_cut, in_X


def rejection_sample(cuts, d, rng, want=3000, cap=6_000_000):
    if not cuts:
        return rng.random((want, d))
    out, tried = [], 0
    while sum(len(o) for o in out) < want and tried < cap:
        P = rng.random((40000, d))
        tried += 40000
        keep = P[in_X(P, cuts)]
        if len(keep):
            out.append(keep)
    if not out:
        return np.empty((0, d))
    return np.vstack(out)[:want]


def live_progress(S, c):
    D = S - c[None, :]
    arg = np.abs(D).argmax(1)
    sgn = np.sign(D[np.arange(len(S)), arg])
    d = S.shape[1]
    npos = np.array([np.sum((arg == m) & (sgn > 0)) for m in range(d)])
    nneg = np.array([np.sum((arg == m) & (sgn <= 0)) for m in range(d)])
    live = int(np.sum((npos + nneg) > 0))
    prog = float(np.minimum(npos, nneg).sum()) / len(S)
    return live, prog


def balanced_apex(S):
    from scipy.optimize import linprog
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


def apex_candidates(S, cb, rng, n_rand=3000):
    """Balanced apex, axis-pulled apexes (inside AND outside the box), random."""
    d = S.shape[1]
    lo, hi = S.min(0), S.max(0)
    cands = [cb]
    mid = 0.5 * (lo + hi)
    for m in range(d):
        for t in (0.0, 0.25, 0.5, 0.75, 1.0, 1.5, 2.0, -0.5, -1.0):
            c = mid.copy()
            c[m] = lo[m] + t * (hi[m] - lo[m])
            cands.append(c.copy())
            c2 = mid.copy()
            c2[m] = hi[m] + t
            cands.append(c2)
    # random apexes, allowed to leave the box (upper bound on what's achievable)
    cands.extend(list(rng.uniform(-1.0, 2.0, size=(n_rand, d))))
    return cands


def main():
    rng = np.random.default_rng(7)
    print("Legend: L = #live coords, p = worst-case removal fraction.")
    print("best p at each liveness level, over ~3k apexes (box AND outside box)")
    print(f"{'d':>2} {'sd':>3} {'t':>2} {'|S|':>5} {'L_bal':>5} {'p_bal':>6} "
          f"{'p|L=1':>6} {'p|L=2':>6} {'p|L=3':>6} {'p|L<=2':>7} {'Lmin(p>.05)':>11}")
    for d in (3, 4, 5, 6):
        for seed in (1, 2):
            f, _ = make_ssg(d, 1e-4, seed)
            _ = fixed_point(f, d)
            cuts = []
            for t in range(1, 2 * d + 1):
                S = rejection_sample(cuts, d, rng)
                if len(S) < 400:
                    print(f"{d:>2} {seed:>3} {t:>2}   -- sampler exhausted --")
                    break
                Ssub = S[:1500]
                cb = balanced_apex(S[:200])
                Lb, pb = live_progress(Ssub, cb)
                best = {L: 0.0 for L in range(1, d + 1)}
                Lmin = d
                for c in apex_candidates(Ssub, cb, rng):
                    L, p = live_progress(Ssub, c)
                    if p > best[L]:
                        best[L] = p
                    if p >= 0.05:
                        Lmin = min(Lmin, L)
                pl2 = max(best[1], best[2])
                print(f"{d:>2} {seed:>3} {t:>2} {len(S):>5} {Lb:>5} {pb:>6.3f} "
                      f"{best[1]:>6.3f} {best[2]:>6.3f} {best[3]:>6.3f} {pl2:>7.3f} "
                      f"{Lmin:>11}")
                c, s, _ = make_cut(f, np.clip(cb, 0, 1))
                cuts.append((c, s))
            print()


if __name__ == "__main__":
    main()
