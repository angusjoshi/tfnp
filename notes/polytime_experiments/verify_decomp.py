import os
"""Verify the total-variance decomposition for a balanced cut (two equal halves):
   Sigma(X') = 2 Sigma(X) - Sigma(N) - (1/2) Delta Delta^T,  Delta = m_K - m_N,
and its corollary lambda_max(X') <= 2 lambda_max(X). Uses exact rejection samples.
"""
import numpy as np, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import in_X, balanced

def K_ok_one(P, c, s):
    from common import K_ok
    return K_ok(P, c, s)

for d in [4, 6]:
    rng = np.random.default_rng(d)
    X = rng.uniform(0, 1, size=(200000, d))          # uniform on box = X
    c = balanced(X[:80], d)                            # balanced center (subsample)
    s = np.ones(d)
    keep = K_ok_one(X, c, s)
    K = X[keep]; N = X[~keep]
    fracK = len(K) / len(X)
    SX = np.cov(X.T); SK = np.cov(K.T); SN = np.cov(N.T)
    mK = K.mean(0); mN = N.mean(0); Delta = mK - mN
    rhs = 2 * SX - SN - 0.5 * np.outer(Delta, Delta)
    err = np.abs(SK - rhs).max()
    lam_max_ratio = np.linalg.eigvalsh(SK).max() / np.linalg.eigvalsh(SX).max()
    print(f"d={d}: fracK={fracK:.3f} (want .5)  decomp max|SK-rhs|={err:.2e}  "
          f"lam_max(X')/lam_max(X)={lam_max_ratio:.3f} (<=2 always)")
print("done")
