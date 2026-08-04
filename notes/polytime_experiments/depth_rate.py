"""THE decisive rate: how fast does tie-depth grow under balanced cuts?

The diagonal recursion (notes/CHAIN.md, cycle 18): survival conditions mass
onto ties (fixed-argmax points die at rate 1/2; tie points dodge by flipping
argmax), and each exhausted tie level pushes the process one level deeper.
Cell count ~ (d^2 t^2)^depth, so:
  depth ~ O(1)      -> poly cells      -> (*) and SSG in P (this method)
  depth ~ O(log t)  -> quasi-poly      -> beats best known SSG bounds
  depth ~ t/const   -> method capped   -> (*) false along these trajectories
Measured: mean and 90th-pct tie-depth (coords within 2*drift of top) per
round, all oracles.

Usage: python depth_rate.py
"""
import numpy as np
import adversary_game as G
from cells_adversarial import ssg_cuts

rng = np.random.default_rng(2718)


def depth_stats(S, c, delta):
    A = np.abs(S - c[None, :])
    A.sort(1)
    within = (A >= (A[:, -1] - 2 * delta)[:, None]).sum(1)
    return float(within.mean()), float(np.quantile(within, 0.9)), \
        int(within.max())


for label, d, mk in [
    ("ssg     d=6", 6, lambda: ssg_cuts(6, 1, 14, np.random.default_rng(7))),
    ("adv     d=6", 6,
     lambda: G.play(6, 1, 14, mode="adversary", verbose=False)[1]),
    ("cellmax d=6", 6,
     lambda: G.play(6, 1, 14, mode="cellmax", verbose=False)[1]),
    ("randbal d=6", 6,
     lambda: G.play(6, 1, 14, mode="randbal", verbose=False)[1]),
    ("randbal d=8", 8,
     lambda: G.play(8, 1, 10, mode="randbal", verbose=False)[1]),
]:
    cuts = mk()
    print(f"=== {label}: tie-depth per round ===")
    print(f"{'t':>3} {'drift':>8} {'mean':>6} {'p90':>5} {'max':>4}")
    for t in range(2, len(cuts) + 1, 2):
        dd = cuts[0][0].shape[0]
        S, _ = G.rejection_sample(cuts[:t], dd, rng, want=2200, cap=5e8)
        if len(S) < 400:
            print(f"{t:>3}  exhausted")
            break
        drift = np.abs(cuts[t - 1][0] - cuts[t - 2][0]).max()
        mn, p90, mx = depth_stats(S, cuts[t - 1][0], drift)
        print(f"{t:>3} {drift:>8.5f} {mn:>6.2f} {p90:>5.1f} {mx:>4}",
              flush=True)
