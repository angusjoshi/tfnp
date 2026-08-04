"""Anisotropic-apex convex cut: does the progress/convexity trade-off have a
usable corner?

Theory (notes/progress_convexity.md, Tfnp/Progress.lean):
  * worst-case removal at apex c is  sum_m min(n_m^+, n_m^-)  (minority count),
    maximised (= N/2) exactly at a balanced apex;
  * the retained region is contained in a HALFSPACE iff at most two coordinates
    are "live" at c (i.e. attain the l-inf argmax on X);
  * three live coordinates => conv(K) = R^d, no convex/quasiconcave surrogate.

So a poly-time round needs an apex with <= 2 live coordinates AND positive
guaranteed removal.  The construction below places
    c_i = median of the widest coordinate i,
    c_j = just outside the range of the narrowest coordinate j,
    c_m = midpoint for every other m,
which forces every argmax into {i,j}.  It has guaranteed removal iff coordinate
i's spread dominates -- i.e. iff X is l-inf ANISOTROPIC.

This measures, on realizable SSG trajectories:
  (A) the anisotropy ratio w1/w2 of X_t,
  (B) whether the construction actually achieves live<=2 with 4-sign removal,
  (C) the same numbers at the balanced apex (control).

Usage: python anisotropic_cut.py
"""
import numpy as np
from common import make_ssg, fixed_point, make_cut, in_X

TOL = 1e-12


def rejection_sample(cuts, d, rng, want=4000, cap=4_000_000):
    """Exact uniform samples of X_t = box ∩ ⋂ K(c,s) by rejection from the box."""
    out, tried = [], 0
    while len(out) < want and tried < cap:
        P = rng.random((20000, d))
        tried += 20000
        keep = P[in_X(P, cuts)]
        if len(keep):
            out.append(keep)
    if not out:
        return np.empty((0, d)), tried
    return np.vstack(out)[:want], tried


def live_and_progress(S, c):
    """Live coordinates, worst-case pyramid removal (minority count / N)."""
    D = S - c[None, :]
    A = np.abs(D)
    arg = A.argmax(1)
    sgn = np.sign(D[np.arange(len(S)), arg])
    d = S.shape[1]
    npos = np.array([np.sum((arg == m) & (sgn > 0)) for m in range(d)])
    nneg = np.array([np.sum((arg == m) & (sgn <= 0)) for m in range(d)])
    live = np.where((npos + nneg) > 0)[0]
    two_sided = np.where((npos > 0) & (nneg > 0))[0]
    prog = np.minimum(npos, nneg).sum() / len(S)
    return live, two_sided, prog


def aniso_apex(S):
    """The anisotropic-apex construction. Returns (c, i, j) or None if the
    j-coordinate has no room inside the unit box."""
    lo, hi = S.min(0), S.max(0)
    w = hi - lo
    d = S.shape[1]
    i = int(np.argmax(w))
    rest = [m for m in range(d) if m != i]
    j = int(rest[int(np.argmin(w[rest]))])
    others = [m for m in range(d) if m not in (i, j)]
    W = max([w[m] for m in others], default=0.0)
    Dg = W / 2 + 1e-6
    c = np.empty(d)
    for m in others:
        c[m] = 0.5 * (lo[m] + hi[m])
    c[i] = float(np.median(S[:, i]))
    if lo[j] - Dg >= 0.0:
        c[j] = lo[j] - Dg
    elif hi[j] + Dg <= 1.0:
        c[j] = hi[j] + Dg
    else:
        return None
    return c, i, j


def halfspace_removals(S, c, i, j):
    """Removal fraction of each of the 4 sign patterns' halfspaces."""
    ui, uj = S[:, i] - c[i], S[:, j] - c[j]
    out = {}
    for si in (1, -1):
        for sj in (1, -1):
            out[(si, sj)] = float(np.mean(si * ui + sj * uj < 0))
    return out


def balanced_apex(S):
    """Fermat-Weber (l-inf) minimiser of the sample set, by LP."""
    from scipy.optimize import linprog
    N, d = S.shape
    # vars: c (d), t (N).  min sum t  s.t.  t_n >= +-(S[n,m]-c[m])
    cobj = np.concatenate([np.zeros(d), np.ones(N)])
    rows, rhs = [], []
    for m in range(d):
        Am = np.zeros((N, d + N)); Am[:, m] = 1.0; Am[np.arange(N), d + np.arange(N)] = -1.0
        rows.append(Am); rhs.append(S[:, m])          # c_m - t_n <= S[n,m]
        Bm = np.zeros((N, d + N)); Bm[:, m] = -1.0; Bm[np.arange(N), d + np.arange(N)] = -1.0
        rows.append(Bm); rhs.append(-S[:, m])         # -c_m - t_n <= -S[n,m]
    A = np.vstack(rows); b = np.concatenate(rhs)
    res = linprog(cobj, A_ub=A, b_ub=b, bounds=[(None, None)] * d + [(0, None)] * N,
                  method="highs")
    return res.x[:d]


def main():
    rng = np.random.default_rng(0)
    print(f"{'d':>2} {'seed':>4} {'t':>2} {'|S|':>5} "
          f"{'w1/w2':>7} {'live_a':>6} {'2sid_a':>6} {'minHS':>7} {'prog_a':>7} "
          f"{'live_b':>6} {'prog_b':>7}")
    for d in (3, 4, 5):
        for seed in (1, 2, 3):
            f, _ = make_ssg(d, 1e-4, seed)
            xs = fixed_point(f, d)
            cuts = []
            for t in range(1, 2 * d + 1):
                S, _ = rejection_sample(cuts, d, rng, want=3000) if cuts else (
                    rng.random((3000, d)), 0)
                if len(S) < 400:
                    print(f"{d:>2} {seed:>4} {t:>2}  -- sampler exhausted --")
                    break
                # --- the balanced apex (control) ---
                cb = balanced_apex(S[:250])
                live_b, _, prog_b = live_and_progress(S, cb)
                # --- the anisotropic apex (the new construction) ---
                aa = aniso_apex(S)
                if aa is None:
                    la, ta, pa, mh, ratio = [], [], 0.0, 0.0, np.nan
                else:
                    ca, i, j = aa
                    la, ta, pa = live_and_progress(S, ca)
                    mh = min(halfspace_removals(S, ca, i, j).values())
                w = S.max(0) - S.min(0)
                ws = np.sort(w)[::-1]
                ratio = ws[0] / max(ws[1], 1e-12)
                print(f"{d:>2} {seed:>4} {t:>2} {len(S):>5} "
                      f"{ratio:>7.2f} {len(la):>6} {len(ta):>6} {mh:>7.3f} {pa:>7.3f} "
                      f"{len(live_b):>6} {prog_b:>7.3f}")
                # advance the real algorithm with the balanced cut
                c, s, _ = make_cut(f, np.clip(cb, 0, 1))
                cuts.append((c, s))
            print()


if __name__ == "__main__":
    main()
