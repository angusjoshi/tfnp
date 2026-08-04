"""Does the certified-realizable shattering adversary disconnect at d=3, 4?
(d=2 provably cannot: the body stays convex.) Smallest-d disconnection =
target instance for the exact-rational certificate."""
import numpy as np
import adversary_game as G

for d, T, seeds in [(3, 12, (1, 2, 3, 4)), (4, 12, (1, 2))]:
    for seed in seeds:
        print(f"=== d={d} seed={seed} adversary ===")
        rows, cuts = G.play(d, seed=seed, T=T, mode="adversary", verbose=False)
        rng = np.random.default_rng(42)
        for t in (T // 2, T):
            S, _ = G.rejection_sample(cuts[:t], d, rng, want=2500)
            if len(S) < 300:
                print(f"  t={t}: exhausted")
                continue
            nc, sizes, pock = G.fresh_components(S, cuts[:t])
            prof = "/".join(f"{x/sizes.sum():.2f}" for x in sizes[:4])
            print(f"  t={t}: comps={nc} sizes[{prof}] pockets={pock}",
                  flush=True)
