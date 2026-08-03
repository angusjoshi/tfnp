import os
"""Two tests on real SSG bodies:
 (1) DELTA SWEEP: does the hard regime (delta -> 0, weak contraction) induce a
     mixing bottleneck? Report TRAP vs delta at fixed d.
 (2) WELL-ROUNDEDNESS / SPIKE test: from x*, ray-shoot in many directions to get
     the radial function R(u); report inradius/diam and the spike ratio
     (max R / median R). Also fraction of hit-run samples VISIBLE from x*
     (star-shapedness deficit). Spikes are the obstruction that defeats generic
     star-shaped Cheeger bounds; if absent, the body is genuinely well-behaved.
"""
import sys, time
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import make_ssg, fixed_point, run_algo, hitrun, in_X
from mixing_test import probe

def rayshoot_l2(p0, u, cuts, Rmax=3.0):
    lo, hi = 0.0, Rmax
    if not in_X(p0 + hi * u, cuts)[0]:
        for _ in range(50):
            mid = (lo + hi) / 2
            if in_X(p0 + mid * u, cuts)[0]:
                lo = mid
            else:
                hi = mid
        return lo
    return Rmax

def visible_frac(p0, pts, cuts, nt=200):
    """fraction of pts p for which segment [p0,p] is in X (star-visible from p0)."""
    vis = 0
    for p in pts:
        ts = np.linspace(0, 1, nt)[:, None]
        seg = p0[None, :] * (1 - ts) + p[None, :] * ts
        if in_X(seg, cuts).all():
            vis += 1
    return vis / len(pts)

def roundness(f, d, cuts, xstar, rng, ndir=400):
    U = rng.normal(size=(ndir, d)); U /= np.linalg.norm(U, axis=1, keepdims=True)
    R = np.array([rayshoot_l2(xstar.copy(), U[k], cuts) for k in range(ndir)])
    inrad = R.min()
    diam = 2 * R.max()   # crude; sample-based diam better but ok
    spike = R.max() / (np.median(R) + 1e-12)
    # visibility on a hit-run sample
    S = hitrun(cuts, d, xstar.copy(), nsamp=120, thin=15, burn=1500, rng=rng, nt=2000)
    vf_vis = visible_frac(xstar, S, cuts)
    return dict(inrad=inrad, Rmed=float(np.median(R)), Rmax=float(R.max()),
                spike=float(spike), inrad_over_med=float(inrad/(np.median(R)+1e-12)),
                vis=vf_vis)

def main():
    mode = sys.argv[1]  # "delta" or "round"
    d = int(sys.argv[2])
    seed = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    if mode == "delta":
        for delta in [1e-2, 1e-3, 1e-4, 1e-6, 1e-9]:
            rng = np.random.default_rng(seed)
            f, _ = make_ssg(d, delta, seed)
            xstar = fixed_point(f, d)
            cuts, hist = run_algo(f, d, 2 * d, rng, nsamp=60, xstar=xstar)
            r = probe(f, d, cuts, xstar, rng)
            if r:
                print(f"  delta={delta:.0e} spread={xstar.max()-xstar.min():.2f} "
                      f"TRAP={r['trap']:.3f} h_iso={r['h_iso']:.2e} kappa={r['kappa']:.1f} "
                      f"err={hist[-1]['err']:.2e}", flush=True)
    elif mode == "round":
        for dd in ([d] if d else [6, 9, 12]):
            rng = np.random.default_rng(seed)
            f, _ = make_ssg(dd, 1e-3, seed)
            xstar = fixed_point(f, dd)
            cuts, hist = run_algo(f, dd, 3 * dd, rng, nsamp=60, xstar=xstar)
            for t in sorted(set([dd, 2 * dd, len(cuts)])):
                if t < 1 or t > len(cuts):
                    continue
                r = roundness(f, dd, cuts[:t], xstar, rng)
                print(f"  d={dd} X_{t}: inrad={r['inrad']:.3f} Rmed={r['Rmed']:.3f} "
                      f"Rmax={r['Rmax']:.3f} spike(max/med)={r['spike']:.2f} "
                      f"inrad/med={r['inrad_over_med']:.2f} star-visible={r['vis']:.2f}",
                      flush=True)
    print("done", flush=True)

if __name__ == "__main__":
    main()
