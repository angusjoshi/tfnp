import os
"""Priority-3 support: does bounded kappa rule out a bottleneck (in the star
regime)? Generate many STAR-SHAPED bodies (cuts toward a common x0), measure
kappa AND isotropic 1-D Cheeger h_iso on EXACT rejection-uniform samples.
Report: (a) correlation, (b) the min h_iso among bodies with kappa<=Kbound.
If min h_iso stays Omega(1) whenever kappa is bounded => 'kappa poly => h poly'
in the star regime."""
import sys
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import in_X, marginal_cheeger, candidate_directions

def valid_toward(c, x0):
    s = np.sign(x0 - c); s[s == 0] = 1.0
    return (c.copy(), s)

def rej(cuts, d, N, rng, maxtries=300):
    out = []; tries = 0
    while len(out) < N and tries < maxtries:
        P = rng.uniform(0, 1, size=(4 * N, d))
        out.extend(list(P[in_X(P, cuts)])); tries += 1
    return (np.array(out[:N]) if out else np.empty((0, d)),
            len(out) / (tries * 4 * N) if tries else 0)

def kap(S):
    w = np.linalg.eigvalsh(np.cov(S.T))
    return float(w.max() / max(w.min(), 1e-18))

def main():
    for d in [5, 7, 9]:
        pts = []
        for trial in range(40):
            rng = np.random.default_rng(1000 * d + trial)
            x0 = rng.uniform(0.3, 0.7, size=d)
            ncuts = rng.integers(d, 3 * d)
            scale = rng.uniform(0.05, 0.4)     # vary how far apexes are (anisotropy knob)
            apexes = [np.clip(x0 + rng.normal(scale=scale, size=d), 0.02, 0.98)
                      for _ in range(ncuts)]
            # occasionally bias apexes along one axis to induce anisotropy/spikes
            if trial % 3 == 0:
                for a in apexes:
                    a[0] = np.clip(rng.uniform(0.05, 0.95), 0.02, 0.98)
            cuts = [valid_toward(c, x0) for c in apexes]
            S, frac = rej(cuts, d, 8000, rng)
            if len(S) < 1500:
                continue
            k = kap(S)
            dirs = candidate_directions(S, xstar=x0, n_random=200, rng=rng)
            h, _, _ = marginal_cheeger(S, dirs, min_side=0.03, isotropic=True)
            pts.append((k, h, frac))
        pts = np.array(pts)
        if len(pts) == 0:
            print(f"d={d}: no bodies"); continue
        for Kb in [3, 5, 10]:
            sub = pts[pts[:, 0] <= Kb]
            if len(sub):
                print(f"d={d}: bodies with kappa<= {Kb:2d}: n={len(sub):2d}  "
                      f"min h_iso={sub[:,1].min():.3f}  median h_iso={np.median(sub[:,1]):.3f}")
        # global correlation
        lk, lh = np.log(pts[:,0]), np.log(pts[:,1] + 1e-6)
        cc = np.corrcoef(lk, lh)[0,1]
        print(f"   corr(log kappa, log h_iso) = {cc:.2f}  "
              f"(kappa range {pts[:,0].min():.1f}-{pts[:,0].max():.1f}, "
              f"h_iso range {pts[:,1].min():.2f}-{pts[:,1].max():.2f})")
    print("done", flush=True)

if __name__ == "__main__":
    main()
