"""d-scaling of the cone-count lemma: effective mass-carrying cones of the
single mean-apex fan at d=8 vs d=6. Poly(d) predicts ~d^3-d^4 (1300-4100 at
d=8 vs 340-1800 at d=6); 2^{Theta(d)} predicts ~4x the d=6 value."""
import numpy as np
import adversary_game as G
from cells_adversarial import cell_sig, ssg_cuts
from fan_cone_test import cone_sig, H_of

rng = np.random.default_rng(1234)
d = 8
for label, cuts in [
    ("ssg  d=8", ssg_cuts(d, 1, 10, np.random.default_rng(7))),
    ("adv  d=8", G.play(d, 1, 10, mode="adversary", verbose=False)[1]),
]:
    print(f"=== {label} ===")
    for t in (5, 8, 10):
        if t > len(cuts):
            continue
        S, _ = G.rejection_sample(cuts[:t], d, rng, want=2200, cap=5e8)
        if len(S) < 400:
            print(f"  t={t}: exhausted")
            break
        apexes = np.array([c for (c, s) in cuts[:t]])
        pw = np.abs(apexes[:, None, :] - apexes[None, :, :]).max(-1)
        disp = np.median(pw[np.triu_indices(t, 1)])
        chat = apexes.mean(0)
        Hcone, ncones = H_of(cone_sig(S, chat))
        Hcell, ncells = H_of(cell_sig(S, cuts[:t]))
        joint = np.hstack([cone_sig(S, chat), cell_sig(S, cuts[:t])])
        Hj, _ = H_of(joint)
        print(f"  t={t:>2} disp={disp:.3f} cones={ncones} H(cone)={Hcone:.2f} "
              f"effcones={np.exp(Hcone):.0f} cells={ncells} "
              f"H(cell|cone)={Hj - Hcone:.2f}", flush=True)
