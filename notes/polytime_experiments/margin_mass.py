"""The last quantitative link: top-gap margin mass per round.

Machine-checked (Tfnp/Margin.lean): a cut can split a cell only inside the
top-gap margin {gap(y) <= 2*drift}, gap(y) = |w|_(1) - |w|_(2) at the previous
apex. So the per-round cell growth -- all that remains of (*) -- is governed by
  m_r = mu_t( gap(y, c^{r-1}) <= 2*||c^r - c^{r-1}||_inf ).
This measures m_r and the top-gap distribution over the known trajectories.
If m_r stays O(1/poly) and gaps anti-concentrate, (*) follows along the
machine-checked chain; if m_r ~ 1, the margin IS the problem.

Usage: python margin_mass.py
"""
import numpy as np
import adversary_game as G
from cells_adversarial import ssg_cuts


def gaps(S, c):
    A = np.abs(S - c[None, :])
    A.sort(1)
    return A[:, -1] - A[:, -2]


def main():
    rng = np.random.default_rng(555)
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
        print(f"{'t':>3} {'drift':>7} {'m_r':>6} "
              f"{'gap q10':>8} {'gap med':>8}")
        for t in range(2, len(cuts) + 1, 2):
            S, _ = G.rejection_sample(cuts[:t], d, rng, want=2200, cap=5e8)
            if len(S) < 400:
                print(f"{t:>3}  exhausted")
                break
            c_prev = cuts[t - 1][0]
            drift = np.abs(cuts[t - 1][0] - cuts[t - 2][0]).max()
            g = gaps(S, c_prev)
            m_r = float((g <= 2 * drift).mean())
            print(f"{t:>3} {drift:>7.4f} {m_r:>6.3f} "
                  f"{np.quantile(g, 0.1):>8.4f} {np.median(g):>8.4f}",
                  flush=True)


if __name__ == "__main__":
    main()
