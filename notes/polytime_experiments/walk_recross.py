"""Offset-walk level-recrossing counter - the cycle-39 open quantity.

The annealed theorem's last piece reduced (smoothed.md #4g) to the
OFFSET-WALK RECROSSING BUDGET: immigration into a pencil's straddler stack
is gated by the pencil's offset walk re-crossing past offset levels. This
instrument needs NO sampling - it is pure walk analysis of the apex
sequence: for each pencil form phi(y) = y_i + sg*y_j, the walk is
v_t = phi(c_t); a RECROSSING at time t is a past level v_r (r < t-1)
lying strictly between v_{t-1} and v_t that the walk has already crossed
an odd number of... simpler and monotone-normalized: for each level v_r,
count the number of times the walk crosses it after r; a monotone walk
crosses each level <= 1 time. Report per-pencil totals:

  cross_mean / cross_max - mean/max crossings per level (prediction:
      O(1) for annealed/benign; higher if the adversary curves the path);
  scaled  - same but only counting crossings at |step| >= level-age decay
      (crossings within the noise floor of shrinking steps are cheap:
      they concern only the finest scale).

Usage: [venv]/python walk_recross.py
"""
import numpy as np
import adversary_game as G
from cells_adversarial import ssg_cuts


def recross_stats(cuts, d):
    T = len(cuts)
    offs = []
    for i in range(d):
        for j in range(i + 1, d):
            for sg in (1.0, -1.0):
                offs.append([c[i] + sg * c[j] for c, _ in cuts])
    tot_cross, per_level_max, n_levels = 0, 0, 0
    for v in offs:
        for r in range(T - 1):
            level = v[r]
            crossings = 0
            for t in range(r + 1, T - 1):
                lo, hi = min(v[t], v[t + 1]), max(v[t], v[t + 1])
                if lo < level < hi:
                    crossings += 1
            tot_cross += crossings
            per_level_max = max(per_level_max, crossings)
            n_levels += 1
    return tot_cross / max(n_levels, 1), per_level_max, n_levels


if __name__ == "__main__":
    d, T = 6, 20
    rng = np.random.default_rng(39)
    for label, cuts in [
        ("ssg", ssg_cuts(d, 1, T, np.random.default_rng(7))),
        ("randbal", G.play(d, 1, T, mode="randbal", verbose=False)[1]),
        ("adversary", G.play(d, 1, T, mode="adversary", verbose=False)[1]),
        ("cellmax", G.play(d, 1, T, mode="cellmax", verbose=False)[1]),
    ]:
        mu, mx, n = recross_stats(cuts, d)
        print(f"{label:>10}: T={len(cuts)} levels={n} "
              f"recross/level mean={mu:.2f} max={mx}", flush=True)
