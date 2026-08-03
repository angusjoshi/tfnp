import os
"""Disentangle 'real bottleneck' from 'under-budgeted sampler' at higher d.
Take a fixed healthy body X_t and run the TRAP diagnostic at ESCALATING
hit-and-run budgets. If TRAP -> 0 as budget grows, the body mixes (no
bottleneck) and prior high TRAP was sampler weakness. If TRAP plateaus high,
it is a genuine conductance bottleneck (a real barrier)."""
import sys, time
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import make_ssg, fixed_point, run_algo, hitrun, in_X
from mixing_test import extreme_starts, trap_metric

def escalate(cuts, d, xstar, rng, label):
    # explorer to find extremes
    expl = hitrun(cuts, d, xstar.copy(), nsamp=500, thin=15, burn=3000, rng=rng, nt=3000)
    starts = extreme_starts(expl, k=6)
    print(f"  [{label}] explorer n={len(expl)} diam={float((expl.max(0)-expl.min(0)).max()):.2f}", flush=True)
    for (burn, thin, nsamp, nt) in [(1500, 20, 120, 2500),
                                    (5000, 40, 150, 3000),
                                    (15000, 80, 200, 4000),
                                    (40000, 150, 250, 6000)]:
        t0 = time.time()
        chains = [hitrun(cuts, d, s.copy(), nsamp=nsamp, thin=thin, burn=burn, rng=rng, nt=nt)
                  for s in starts]
        trap = trap_metric(chains)
        # also: do the two extreme chains' means along top PCA dir separate?
        pooled = np.vstack(chains)
        C = np.cov(pooled.T); w, V = np.linalg.eigh(C)
        pc = V[:, -1]
        cm = [float(c.mean(0) @ pc) for c in chains]
        sep = (max(cm) - min(cm)) / (pooled @ pc).std()
        print(f"    budget(burn={burn},thin={thin},ns={nsamp},nt={nt}): "
              f"TRAP={trap:.3f}  PCsep={sep:.2f}  [{time.time()-t0:.0f}s]", flush=True)

def main():
    d = int(sys.argv[1]); delta = float(sys.argv[2]); seed = int(sys.argv[3])
    rng = np.random.default_rng(seed)
    f, _ = make_ssg(d, delta, seed)
    xstar = fixed_point(f, d)
    # heavier algo sampling so cuts are genuine balanced cuts
    cuts, hist = run_algo(f, d, 3 * d, rng, nsamp=90, xstar=xstar)
    print(f"[escalate d={d} delta={delta} seed={seed}] {len(cuts)} cuts "
          f"err={hist[-1]['err']:.2e} spread={xstar.max()-xstar.min():.2f}", flush=True)
    for t in [d, 2 * d]:
        if t <= len(cuts):
            escalate(cuts[:t], d, xstar, rng, f"X_{t}")
    print("done", flush=True)

if __name__ == "__main__":
    main()
