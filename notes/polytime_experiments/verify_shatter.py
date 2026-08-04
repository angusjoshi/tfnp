"""Verify the adversarial shattering is not a sampling artifact: replay the
adversarial games, then re-measure component structure of prefix bodies at 4x
sample density, 2.2x edge degree, finer segment checks. Real disconnections
persist; kNN artifacts merge."""
import numpy as np
import adversary_game as G

G_KNN, G_NCHK = G.KNN, G.NCHK


def dense_measure(cuts, d, rng, want=9000, knn=18, nchk=19):
    G.KNN, G.NCHK = knn, nchk
    S, drawn = G.rejection_sample(cuts, d, rng, want=want, cap=6e8)
    if len(S) < 500:
        print(f"    (exhausted: {len(S)} pts)")
        G.KNN, G.NCHK = G_KNN, G_NCHK
        return
    nc, sizes, pock = G.fresh_components(S, cuts)
    G.KNN, G.NCHK = G_KNN, G_NCHK
    tot = sizes.sum()
    prof = "/".join(f"{x/tot:.3f}" for x in sizes[:6])
    print(f"    N={len(S)} comps={nc} sizes[{prof}] pockets={pock}")


for d, seed, T in [(5, 1, 12), (6, 1, 14)]:
    print(f"=== replaying d={d} seed={seed} adversary ===")
    rows, cuts = G.play(d, seed=seed, T=T, mode="adversary", verbose=False)
    rng = np.random.default_rng(777)
    for tprefix in (max(1, T - 6), T - 3, T):
        print(f"  dense recount at t={tprefix}  (game-N=2200/knn=8 above)")
        dense_measure(cuts[:tprefix], d, rng)
