"""The cell-spine hypothesis: do the mass-carrying cells of X_t line up
along a single line?

Motivation (cell_sampler.md, entropy law): effective cell counts are ~linear
in d*t, which is exactly the count of arrangement cells that a LINE meets
(t*d*(d-1) hyperplanes cut a line into <= t*d*(d-1)+1 pieces - rigorous and
poly). If a line exists whose touched cells carry 1-1/poly of the mass, then
(*) reduces to a "spine lemma", and the algorithm could enumerate the spine
cells directly. Connects the entropy law to the OLD anisotropy findings
(persistent long axes / dumbbells): the anisotropy that killed mixing would
be what keeps the cell count linear.

Method: per trajectory prefix, exact-rejection sample S; candidate lines =
(top principal axes through the centroid) + (line through the two most
distant sample points); walk each line densely, collect the cell signatures
of its in-body points; spine mass = fraction of S whose signature appears on
the line. Report the best line's spine mass, plus 2- and 3-line greedy cover.

Also: d=8 entropy check (H_t vs log(dt)) for the entropy law's d-scaling.

Usage: python spine_test.py
"""
import numpy as np
import adversary_game as G
from cells_adversarial import cell_sig, ssg_cuts


def sig_set(P, cuts):
    if len(P) == 0:
        return set()
    return {tuple(r) for r in cell_sig(P, cuts)}


def line_pts(a, b, m=2500):
    ts = np.linspace(-0.15, 1.15, m)
    return a[None, :] * (1 - ts)[:, None] + b[None, :] * ts[:, None]


def spine_masses(S, cuts, d):
    """Best single-line spine mass over candidate lines, + greedy 2/3-line."""
    sigS = cell_sig(S, cuts)
    keys = [tuple(r) for r in sigS]
    ctr = S.mean(0)
    cov = np.cov(S.T)
    w, V = np.linalg.eigh(cov)
    span = S.max(0) - S.min(0)
    cands = []
    for k in range(1, min(4, d) + 1):        # top principal axes
        u = V[:, -k]
        L = np.abs(S @ u - ctr @ u).max()
        cands.append((ctr - 1.1 * L * u, ctr + 1.1 * L * u))
    D = np.abs(S[:, None, :] - S[None, ::40, :]).max(-1)   # coarse diameter pair
    i, j = np.unravel_index(D.argmax(), D.shape)
    cands.append((S[i], S[j * 40]))
    covers = []
    for (a, b) in cands:
        P = line_pts(a, b)
        P = P[G.in_X(P, cuts)]
        covers.append(sig_set(P, cuts))
    frac = lambda cover: np.mean([k in cover for k in keys])
    singles = [frac(c) for c in covers]
    best1 = int(np.argmax(singles))
    # greedy 2- and 3-line covers
    cur = set(covers[best1])
    out = [singles[best1]]
    for _ in range(2):
        gains = [frac(cur | c) for c in covers]
        cur = cur | covers[int(np.argmax(gains))]
        out.append(frac(cur))
    ncells = len(set(keys))
    nspine = len(covers[best1])
    return out, ncells, nspine, np.sqrt(w[::-1][:4])


def main():
    rng = np.random.default_rng(777)
    for label, d, T, mk in [
        ("ssg  d=6", 6, 14, lambda: ssg_cuts(6, 1, 14, np.random.default_rng(7))),
        ("adv  d=6", 6, 14,
         lambda: G.play(6, 1, 14, mode="adversary", verbose=False)[1]),
        ("cellmax d=6", 6, 14,
         lambda: G.play(6, 1, 14, mode="cellmax", verbose=False)[1]),
        ("toward d=6", 6, 14,
         lambda: G.play(6, 106, 14, mode="toward", verbose=False)[1]),
    ]:
        cuts = mk()
        print(f"=== {label}: spine mass (best line / 2 lines / 3 lines) ===")
        for t in (6, 10, 14):
            if t > len(cuts):
                continue
            S, _ = G.rejection_sample(cuts[:t], d, rng, want=2200)
            if len(S) < 400:
                print(f"  t={t}: exhausted")
                break
            (m1, m2, m3), nc, ns, sv = spine_masses(S, cuts[:t], d)
            print(f"  t={t:>2} spine={m1:.3f}/{m2:.3f}/{m3:.3f} "
                  f"cells={nc:>4} spinecells={ns:>4} "
                  f"sqrt-eigs={np.array2string(sv, precision=3)}", flush=True)
    # ---- d=8 entropy-law scaling check ----
    print("=== d=8 entropy check: H_t vs log(d*t) ===")
    d = 8
    cuts = ssg_cuts(d, 1, 10, np.random.default_rng(7))
    for t in (4, 7, 10):
        S, _ = G.rejection_sample(cuts[:t], d, rng, want=2200, cap=4e8)
        if len(S) < 400:
            print(f"  t={t}: exhausted")
            break
        sig = cell_sig(S, cuts[:t])
        _, inv = np.unique(sig, axis=0, return_inverse=True)
        p = np.bincount(inv) / len(S)
        H = float(-(p * np.log(p + 1e-12)).sum())
        print(f"  t={t:>2} H={H:.2f}  log(dt)={np.log(d*t):.2f}  "
              f"t*log(d)={t*np.log(d):.2f}", flush=True)


if __name__ == "__main__":
    main()
