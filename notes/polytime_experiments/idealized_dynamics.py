"""Priority A: the IDEALIZED symmetric multi-cut dynamics.
Model: the body is kept a symmetric PRODUCT BOX with variances lam=(lam_1..lam_d)
(half-widths a_i=sqrt(3 lam_i)). One balanced cut = rank-1 downdate by m_K, and we
RE-SYMMETRIZE to a product box, i.e. lam_i <- lam_i - m_{K,i}^2, then renormalize
(the volume-halving rescales all coords by a constant, irrelevant to kappa).
m_{K,i} = E[y_i | max_j y_j + min_j y_j >= 0] estimated by MC on the box.

Goal: does kappa stay bounded (attractor)? Which Lyapunov is monotone?
Candidates: kappa=lmax/lmin; spread=sum (log lam_i - mean)^2; lmax*tr(1/lam).
"""
import os, sys
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

def mK(lam, rng, N=200000):
    d = len(lam)
    a = np.sqrt(3.0 * lam)                      # half-widths -> Var = a^2/3 = lam
    Y = rng.uniform(-1, 1, size=(N, d)) * a[None, :]
    keep = (Y.max(1) + Y.min(1)) >= 0
    K = Y[keep]
    return K.mean(0), keep.mean()

def potentials(lam):
    l = np.sort(lam)
    kappa = l[-1] / l[0]
    lg = np.log(lam); spread = float(((lg - lg.mean())**2).sum())
    lmtr = lam.max() * (1.0/lam).sum()
    return kappa, spread, lmtr

def run(lam0, rounds, rng, label):
    lam = np.array(lam0, float)
    lam = lam / np.exp(np.mean(np.log(lam)))   # normalize geomean=1
    traj = []
    for t in range(rounds):
        m, frac = mK(lam, rng)
        kap, spr, lmtr = potentials(lam)
        traj.append((kap, spr, lmtr))
        lam = lam - m**2                        # re-symmetrized downdate (diagonal)
        lam = np.maximum(lam, 1e-9)
        lam = lam / np.exp(np.mean(np.log(lam)))  # renormalize (halving is a global scale)
    kap, spr, lmtr = potentials(lam)
    traj.append((kap, spr, lmtr))
    ks = [x[0] for x in traj]; ss = [x[1] for x in traj]
    mono_spread = all(ss[i+1] <= ss[i] + 1e-9 for i in range(len(ss)-1))
    print(f"[{label}] kappa: {ks[0]:.1f} -> {ks[-1]:.2f} (max {max(ks):.1f})  "
          f"spread: {ss[0]:.2f} -> {ss[-1]:.2f} monotone_dec={mono_spread}")
    return traj

def main():
    rng = np.random.default_rng(0)
    for d in [4, 6, 8, 12]:
        print(f"##### d={d} #####")
        run(np.ones(d), 20, rng, f"d{d} isotropic")
        v = np.ones(d); v[0] = 100.0
        run(v, 25, rng, f"d{d} one-LONG(100x)")
        v = np.ones(d); v[0] = 0.01
        run(v, 25, rng, f"d{d} one-SHORT(0.01x)")
        run(np.array([10.0**k for k in range(d)]), 25, rng, f"d{d} graded(10^k)")
    print("done")

if __name__ == "__main__":
    main()
