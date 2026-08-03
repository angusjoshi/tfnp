"""Verify the symmetric-case per-cut theorem:
  If X is symmetric about its center c (rho_c(X)=X) and the cut is balanced,
  then Sigma(X cap K) = Sigma(X) - m_K m_K^T   (rank-1 downdate along kept mean).
Consequences tested: (i) lambda_max does NOT grow; (ii) only the m_K direction
loses variance; (iii) even for VERY anisotropic symmetric boxes the cut keeps
kappa controlled. This is the crux: does an already-elongated symmetric body get
worse under a balanced cone-cut?
"""
import os, sys
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import K_ok

def rej_sym_box(halfwidths, N, rng):
    d = len(halfwidths)
    P = (rng.uniform(-1, 1, size=(N, d))) * halfwidths[None, :]   # centered box, symmetric about 0
    return P

def test(halfwidths, seed=0, N=400000):
    rng = np.random.default_rng(seed)
    d = len(halfwidths)
    X = rej_sym_box(halfwidths, N, rng)
    c = np.zeros(d)                      # FW center of a symmetric box is 0
    s = np.ones(d)
    keep = K_ok(X, c, s)
    K = X[keep]
    fracK = keep.mean()
    SX = np.cov(X.T)
    SK = np.cov(K.T)
    mK = K.mean(0)
    downdate = SX - np.outer(mK, mK)
    err = np.abs(SK - downdate).max() / SX.max()
    kX = np.linalg.eigvalsh(SX); kK = np.linalg.eigvalsh(SK)
    kapX = kX.max()/kX.min(); kapK = kK.max()/kK.min()
    # variance along mK before/after
    mhat = mK/ (np.linalg.norm(mK)+1e-12)
    varX_m = mhat @ SX @ mhat; varK_m = mhat @ SK @ mhat
    print(f"  hw={np.round(halfwidths,2)} fracK={fracK:.3f}  rel_err(downdate)={err:.1e}  "
          f"kappa: {kapX:.2f}->{kapK:.2f}  lam_max: {kX.max():.3f}->{kK.max():.3f}  "
          f"var(mK): {varX_m:.3f}->{varK_m:.3f}")

if __name__ == "__main__":
    print("symmetric-box balanced cut: Sigma(K)=Sigma(X)-mK mK^T ?  and kappa growth")
    for d in [4, 6, 8]:
        print(f" d={d} isotropic:")
        test(np.ones(d))
    print(" anisotropic (one long axis):")
    for r in [2, 5, 10, 30]:
        hw = np.ones(6); hw[0] = r
        test(hw)
    print(" anisotropic (graded spectrum):")
    for d in [6, 8]:
        hw = np.array([2.0**k for k in range(d)])  # geometric halfwidths
        test(hw)
    print("done")
