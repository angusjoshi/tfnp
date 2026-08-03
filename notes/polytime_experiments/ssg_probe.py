import os
"""Gold-standard test: run the ACTUAL algorithm on a proper SSG value operator
(spread x*), record real cut history, and probe X_t for bottlenecks."""
import sys, time
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import make_ssg, fixed_point, run_algo, hitrun, in_X
from probe import probe_round

def main():
    d = int(sys.argv[1]); delta = float(sys.argv[2]); seed = int(sys.argv[3])
    rng = np.random.default_rng(seed)
    f, types = make_ssg(d, delta, seed)
    xstar = fixed_point(f, d)
    spread = xstar.max() - xstar.min()
    print(f"[SSG d={d} delta={delta} seed={seed}] x*={np.round(xstar,3)} "
          f"spread={spread:.3f} types={types}", flush=True)
    R = int(sys.argv[4]) if len(sys.argv) > 4 else 3 * d
    cuts, hist = run_algo(f, d, R, rng, nsamp=70, xstar=xstar)
    print(f"  algo: {len(cuts)} cuts, final err={hist[-1]['err']:.2e} "
          f"vmag={hist[-1]['vmag']:.2e}", flush=True)
    t0 = time.time()
    for t in sorted(set([d, min(len(cuts), 2*d), len(cuts)])):
        if t < 1 or t > len(cuts):
            continue
        res = probe_round(f, d, cuts[:t], xstar, rng)
        print(f"  X_{t:2d}: trap={res['trap']:.3f}  h_hat={res['h']:.3e}  "
              f"diam={res['diam']:.2f}  fr(.05,.1,.2)="
              f"{res['fr'][0.05]:.3f},{res['fr'][0.1]:.3f},{res['fr'][0.2]:.3f}  "
              f"[{time.time()-t0:.0f}s]", flush=True)
    print("done", flush=True)

if __name__ == "__main__":
    main()
