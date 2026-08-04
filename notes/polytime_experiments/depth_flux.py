"""Depth flux: the one-round accounting the flooding supermartingale must
match. Per round, per oracle:
  kappa(m) = kept fraction of the depth-m class (extinction vs protection);
  the post-cut depth distribution re-measured at the NEXT apex (graduation
  + refill after re-centering).
The supermartingale claim: E[depth] returns to ~3 whatever the schedule does
- the flux table shows the return mechanism class by class.

Usage: python depth_flux.py
"""
import numpy as np
import adversary_game as G
from cells_adversarial import ssg_cuts


def depths(S, c, eta):
    A = np.abs(S - c[None, :])
    A.sort(1)
    return (A >= (A[:, -1] - eta)[:, None]).sum(1)


for label, d, mk in [
    ("ssg     d=6", 6, lambda: ssg_cuts(6, 1, 14, np.random.default_rng(7))),
    ("adv     d=6", 6,
     lambda: G.play(6, 1, 14, mode="adversary", verbose=False)[1]),
    ("cellmax d=6", 6,
     lambda: G.play(6, 1, 14, mode="cellmax", verbose=False)[1]),
]:
    cuts = mk()
    rng = np.random.default_rng(4321)
    print(f"=== {label}: per-class kept fraction kappa(m), then next-apex "
          f"depth mean ===")
    print(f"{'t':>3} {'k(1)':>6} {'k(2)':>6} {'k(3)':>6} {'k(4+)':>6} "
          f"{'E[D]pre':>8} {'E[D]post':>9}")
    for t in range(3, len(cuts), 3):
        S, _ = G.rejection_sample(cuts[:t], d, rng, want=2400, cap=5e8)
        if len(S) < 500:
            print(f"{t:>3}  exhausted")
            break
        c_t, s_t = cuts[t]                    # the round-(t+1) cut
        drift = np.abs(c_t - cuts[t - 1][0]).max()
        D_pre = depths(S, c_t, 2 * drift)
        kept = G.K_ok(S, c_t, s_t)
        row = f"{t:>3}"
        for m in (1, 2, 3):
            cls = D_pre == m
            row += f" {kept[cls].mean() if cls.sum() > 25 else float('nan'):>6.2f}"
        cls = D_pre >= 4
        row += f" {kept[cls].mean() if cls.sum() > 25 else float('nan'):>6.2f}"
        # post: survivors re-measured at the NEXT apex (re-centering included)
        surv = S[kept]
        if t + 1 < len(cuts) and len(surv) > 100:
            c_next = cuts[t + 1][0]
            drift2 = np.abs(c_next - c_t).max()
            D_post = depths(surv, c_next, 2 * drift2)
            row += f" {D_pre.mean():>8.2f} {D_post.mean():>9.2f}"
        else:
            row += f" {D_pre.mean():>8.2f} {'-':>9}"
        print(row, flush=True)
