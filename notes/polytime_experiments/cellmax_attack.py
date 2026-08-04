"""The (*)-falsification attempt: a certified-realizable adversary that
maximises the CELL count / cell-mass entropy of X_t (rather than components).
If any realizable adversary can force mass to equidistribute over super-poly
cells, the telescoping algorithm dies; this is the strongest known objective
for doing so. Exact-rejection window (t <= ~14)."""
import numpy as np
import adversary_game as G
from cells_adversarial import profile

rng = np.random.default_rng(99)
for d, T in [(5, 12), (6, 14)]:
    for seed in (1, 2):
        print(f"=== CELLMAX d={d} seed={seed} T={T} ===")
        _, cuts = G.play(d, seed=seed, T=T, mode="cellmax", verbose=False)
        for tp in (T // 2, 3 * T // 4, T):
            S, _ = G.rejection_sample(cuts[:tp], d, rng, want=2400)
            if len(S) < 400:
                print(f"  t={tp}: sampler exhausted")
                continue
            profile(S, cuts[:tp], f"CELLMAX d={d}s{seed}")
