"""The multi-tie measurement that frames the endgame.

Cell trichotomy (notes/CHAIN.md, being proved): every survivor point is
  (a) 1-deep  (top gap > 2*drift)        -> <= 2d cells, total;
  (b) 2-simple (exactly one near-tied top pair, rest 2*drift below top)
                                          -> <= O(d^2 t^2) cells, total;
  (c) multi-tied (>= 3 coords within 2*drift of top) or near-apex.
(a)+(b) cells are provably poly. (*) holds iff the type-(c) mass has poly
cell structure -- and if m3 := mu(type c) is small, that is immediate.
This measures the top-k tie profile: m_k = mass with >= k coords within
2*drift of the top, per round, per trajectory.

Usage: python multitie_mass.py
"""
import numpy as np
import adversary_game as G
from cells_adversarial import ssg_cuts


def tie_profile(S, c, delta):
    A = np.abs(S - c[None, :])
    A.sort(1)
    top = A[:, -1]
    within = (A >= (top - 2 * delta)[:, None]).sum(1)   # coords within 2δ of top
    return [float((within >= kk).mean()) for kk in (2, 3, 4)] + \
        [float((top <= 2 * delta).mean())]


def main():
    rng = np.random.default_rng(909)
    for label, d, mk in [
        ("ssg  d=6", 6, lambda: ssg_cuts(6, 1, 14, np.random.default_rng(7))),
        ("adv  d=6", 6,
         lambda: G.play(6, 1, 14, mode="adversary", verbose=False)[1]),
        ("cellmax d=6", 6,
         lambda: G.play(6, 1, 14, mode="cellmax", verbose=False)[1]),
        ("ssg  d=8", 8, lambda: ssg_cuts(8, 1, 10, np.random.default_rng(7))),
    ]:
        cuts = mk()
        print(f"=== {label} ===")
        print(f"{'t':>3} {'drift':>7} {'m2':>6} {'m3':>6} {'m4':>6} {'apexball':>8}")
        for t in range(2, len(cuts) + 1, 2):
            S, _ = G.rejection_sample(cuts[:t], d, rng, want=2200, cap=5e8)
            if len(S) < 400:
                print(f"{t:>3}  exhausted")
                break
            c_prev = cuts[t - 1][0]
            drift = np.abs(cuts[t - 1][0] - cuts[t - 2][0]).max()
            m2, m3, m4, ab = tie_profile(S, c_prev, drift)
            print(f"{t:>3} {drift:>7.4f} {m2:>6.3f} {m3:>6.3f} {m4:>6.3f} "
                  f"{ab:>8.3f}", flush=True)


if __name__ == "__main__":
    main()
