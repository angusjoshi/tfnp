"""Cell-count / cell-mass profile of X_t on ADVERSARIAL trajectories.

The telescoping convex-cover algorithm (FINAL_REPORT addendum) is complete
modulo conjecture (*): poly-many convex cells carry 1-1/poly of vol(X_t).
All prior cell measurements (cc_measure, cellcount, k_eff ~ 60/141/250)
used RANDOM instances. This measures the same objects on the certified-
realizable shattering trajectories of adversary_game.py - the hardest known
instances - plus toward-oracle and random-SSG controls in the same harness.

Cell = tuple over cuts r of the index of the pyramid of K(c^r,s^r) containing
y (argmax over active coords of s_i(y_i - c_i)); each cell is a CONVEX
polytope (Lean: convex_cell in Tfnp/Progress.lean).

Reported per prefix t: #distinct cells among N exact-rejection samples, mass
shares of the top cells, and the discovery curve n_cells(n) (saturating curve
=> small true cell support; linear => heavy tail, (*) in trouble).

Usage: python cells_adversarial.py
"""
import numpy as np
import adversary_game as G
from common import make_ssg


def cell_sig(S, cuts):
    sigs = []
    for (c, s) in cuts:
        act = s != 0
        W = s[None, :] * (S - c[None, :])
        W = np.where(act[None, :], W, -np.inf)
        sigs.append(W.argmax(1))
    return np.stack(sigs, 1)


def profile(S, cuts, label):
    sig = cell_sig(S, cuts)
    _, inv, counts = np.unique(sig, axis=0, return_inverse=True,
                               return_counts=True)
    counts = np.sort(counts)[::-1]
    n, tot = len(S), counts.sum()
    top1 = counts[0] / tot
    d = S.shape[1]
    t = len(cuts)
    m = d * t
    topm = counts[:m].sum() / tot
    curve = []
    for nn in (n // 8, n // 4, n // 2, n):
        sub = sig[:nn]
        curve.append(len(np.unique(sub, axis=0)))
    print(f"  {label}: t={t:>2} N={n} cells={len(counts):>4} "
          f"top1={top1:.3f} top(d*t)={topm:.3f} "
          f"curve(N/8,N/4,N/2,N)={curve}")
    return len(counts), topm


def ssg_cuts(d, seed, T, rng):
    """Random-SSG control inside the same balanced-cut harness."""
    f, _ = make_ssg(d, 1e-4, seed)
    cuts = []
    for _ in range(T):
        S, _ = G.rejection_sample(cuts, d, rng)
        if len(S) < 300:
            break
        c = np.clip(G.fw_apex(S[:400]), 1e-6, 1 - 1e-6)
        v = f(c) - c
        s = np.sign(v)
        s[np.abs(v) < 1e-12] = 0.0
        cuts.append((c.copy(), s.copy()))
    return cuts


def main():
    rng = np.random.default_rng(2024)
    for d, seed, T in [(5, 1, 12), (6, 1, 14)]:
        print(f"=== d={d} seed={seed} ===")
        _, cuts_adv = G.play(d, seed=seed, T=T, mode="adversary", verbose=False)
        _, cuts_tow = G.play(d, seed=100 + d, T=T, mode="toward", verbose=False)
        cuts_ssg = ssg_cuts(d, seed, T, rng)
        for name, cuts in [("ADVERSARY", cuts_adv), ("toward   ", cuts_tow),
                           ("random-SSG", cuts_ssg)]:
            for tp in (T // 2, 3 * T // 4, T):
                S, _ = G.rejection_sample(cuts[:tp], d, rng, want=2400)
                if len(S) < 400:
                    print(f"  {name}: t={tp} sampler exhausted")
                    continue
                profile(S, cuts[:tp], name)
        print()


if __name__ == "__main__":
    main()
