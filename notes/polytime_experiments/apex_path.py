"""Apex-path geometry: how collinear are consecutive balanced apexes?

The line-epoch idea (CHAIN cycle 21): if e consecutive apexes lie within rho
of a common line, all pencil thresholds in that epoch form 1-parameter
families and per-epoch cell growth is additive O(d^2 e) (line-zone +
margin machinery, delta = rho). Total cells ~ (d^2 e)^{t/e}: quasi-poly if
e ~ t/polylog is feasible. This measures, for each window length e, the
best-line residual (max apex distance to the window's PCA line) relative to
the window's drift scale: residual << drift means the epoch behaves as a
line; residual ~ window extent means the path is genuinely curved.

Usage: python apex_path.py
"""
import numpy as np
import adversary_game as G
from cells_adversarial import ssg_cuts


def line_residual(P):
    """Max distance of points to their best-fit line (PCA)."""
    c = P.mean(0)
    Q = P - c
    U, S, Vt = np.linalg.svd(Q, full_matrices=False)
    proj = np.outer(Q @ Vt[0], Vt[0])
    resid = np.linalg.norm(Q - proj, axis=1)
    return resid.max(), np.linalg.norm(Q, axis=1).max()


for label, d, mk in [
    ("ssg     d=6", 6, lambda: ssg_cuts(6, 1, 14, np.random.default_rng(7))),
    ("adv     d=6", 6,
     lambda: G.play(6, 1, 14, mode="adversary", verbose=False)[1]),
    ("cellmax d=6", 6,
     lambda: G.play(6, 1, 14, mode="cellmax", verbose=False)[1]),
    ("ssg     d=8", 8, lambda: ssg_cuts(8, 1, 10, np.random.default_rng(7))),
]:
    cuts = mk()
    A = np.array([c for (c, s) in cuts])
    T = len(A)
    print(f"=== {label} (T={T}) ===")
    print(f"{'e':>3} {'worst resid':>11} {'worst r/ext':>11} "
          f"{'median r/ext':>12}")
    for e in (3, 4, 6, 8, min(12, T)):
        if e > T:
            continue
        ratios, resids = [], []
        for start in range(T - e + 1):
            r, ext = line_residual(A[start:start + e])
            resids.append(r)
            ratios.append(r / max(ext, 1e-12))
        print(f"{e:>3} {max(resids):>11.4f} {max(ratios):>11.3f} "
              f"{np.median(ratios):>12.3f}", flush=True)
