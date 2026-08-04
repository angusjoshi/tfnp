"""The near-common-fan hypothesis: with only d(d-1) normal directions, if the
balanced apexes cluster, all cut pencils nearly coincide, and the mass of X_t
should occupy FEW CONES of one reference fan (at the mean apex), with the
t-dependence confined to delta-neighbourhoods of cone boundaries.

Measures per trajectory prefix:
  - apex dispersion: max/median pairwise l-inf distance of apexes, vs body
    diameter;
  - #mass-carrying cones of the reference fan: distinct sign patterns of the
    d(d-1) comparisons (y_i - y_j vs mean-apex differences, y_i + y_j vs
    sums) among exact samples; mass of top cones;
  - conditional cell entropy: H(cell signature | cone) - if small, the cone
    plus O(1) extra bits determines the cell, explaining the entropy law.

Usage: python fan_cone_test.py
"""
import numpy as np
import adversary_game as G
from cells_adversarial import cell_sig, ssg_cuts


def cone_sig(S, chat):
    """Sign pattern of all pairwise comparisons at reference apex chat."""
    d = S.shape[1]
    cols = []
    for i in range(d):
        for j in range(i + 1, d):
            cols.append(np.sign(S[:, i] - S[:, j] - (chat[i] - chat[j])))
            cols.append(np.sign(S[:, i] + S[:, j] - (chat[i] + chat[j])))
    return np.stack(cols, 1)


def H_of(rows):
    _, inv = np.unique(rows, axis=0, return_inverse=True)
    p = np.bincount(inv) / len(rows)
    return float(-(p * np.log(p + 1e-12)).sum()), len(p)


def main():
    rng = np.random.default_rng(1234)
    for label, d, T, mk in [
        ("ssg  d=6", 6, 14, lambda: ssg_cuts(6, 1, 14, np.random.default_rng(7))),
        ("adv  d=6", 6, 14,
         lambda: G.play(6, 1, 14, mode="adversary", verbose=False)[1]),
        ("cellmax d=6", 6, 14,
         lambda: G.play(6, 1, 14, mode="cellmax", verbose=False)[1]),
    ]:
        cuts = mk()
        print(f"=== {label} ===")
        for t in (6, 10, 14):
            if t > len(cuts):
                continue
            S, _ = G.rejection_sample(cuts[:t], d, rng, want=2200)
            if len(S) < 400:
                print(f"  t={t}: exhausted")
                break
            apexes = np.array([c for (c, s) in cuts[:t]])
            pw = np.abs(apexes[:, None, :] - apexes[None, :, :]).max(-1)
            disp_max = pw.max()
            disp_med = np.median(pw[np.triu_indices(t, 1)])
            diam = (S.max(0) - S.min(0)).max()
            chat = apexes.mean(0)
            cones = cone_sig(S, chat)
            Hcone, ncones = H_of(cones)
            cells = cell_sig(S, cuts[:t])
            Hcell, ncells = H_of(cells)
            # conditional entropy H(cell | cone)
            joint = np.hstack([cones, cells])
            Hjoint, _ = H_of(joint)
            print(f"  t={t:>2} apexdisp med/max={disp_med:.3f}/{disp_max:.3f} "
                  f"diam={diam:.3f} cones={ncones:>4} H(cone)={Hcone:.2f} "
                  f"cells={ncells:>4} H(cell)={Hcell:.2f} "
                  f"H(cell|cone)={Hjoint - Hcone:.2f}", flush=True)


if __name__ == "__main__":
    main()
