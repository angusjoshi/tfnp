import os
"""Detect geometric bottlenecks in the ACTUAL algorithm-produced bodies X_t on
hard topical instances. Three diagnostics per round:
  (1) multi-start chain trapping (independent chains disagree => low conductance)
  (2) 1-D marginal Cheeger (certified sparse-cut upper bound on h(X_t))
  (3) fraction of vol in L_inf balls around x* (is x* in a thin lobe?)
"""
import sys, time
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import (make_topical, fixed_point, run_algo, hitrun, in_X,
                    marginal_cheeger, candidate_directions)

def feasible_starts(cuts, d, xstar, rng, k=8):
    """Diverse feasible starting points: x*, and points found by short
    hit-and-run from random box points that land in X_t."""
    starts = [xstar.copy()]
    tries = 0
    while len(starts) < k and tries < 400:
        p = rng.uniform(0, 1, size=d)
        if in_X(p, cuts)[0]:
            starts.append(p)
        tries += 1
    # if too few, jitter x*
    while len(starts) < k:
        starts.append(np.clip(xstar + rng.normal(scale=0.1, size=d), 0, 1))
    return starts[:k]

def trapping_metric(chains):
    """Between-chain / total variance ratio per coordinate, max over coords.
    ~0 => well mixed; ->1 => chains trapped in separate regions."""
    means = np.array([c.mean(0) for c in chains])      # (K,d)
    allpts = np.vstack(chains)
    tot = allpts.var(0) + 1e-15
    btw = means.var(0)
    return float((btw / tot).max()), means

def probe_round(f, d, cuts, xstar, rng, nchain=6, nsamp=110, nt=2500):
    starts = feasible_starts(cuts, d, xstar, rng, k=nchain)
    chains = [hitrun(cuts, d, s, nsamp=nsamp, thin=22, burn=1200, rng=rng, nt=nt)
              for s in starts]
    trap, means = trapping_metric(chains)
    pooled = np.vstack(chains)
    dirs = candidate_directions(pooled, xstar=xstar, n_random=250, rng=rng)
    h, bestdir, info = marginal_cheeger(pooled, dirs, min_side=0.02)
    # x* thin-lobe test: vol fraction within L_inf ball of x*
    diam = float((pooled.max(0) - pooled.min(0)).max())
    fr = {}
    for rad in [0.05, 0.1, 0.2]:
        fr[rad] = float((np.abs(pooled - xstar[None, :]).max(1) <= rad).mean())
    return dict(trap=trap, h=h, bestdir=bestdir, info=info, diam=diam,
                fr=fr, npool=len(pooled))

def main():
    d = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    delta = float(sys.argv[2]) if len(sys.argv) > 2 else 1e-3
    seed = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    Ralgo = int(sys.argv[4]) if len(sys.argv) > 4 else None
    rng = np.random.default_rng(seed)
    f, types = make_topical(d, delta, seed)
    xstar = fixed_point(f, d)
    if Ralgo is None:
        Ralgo = 3 * d
    print(f"[d={d} delta={delta} seed={seed}] x*={np.round(xstar,3)} types={types}", flush=True)
    cuts, hist = run_algo(f, d, Ralgo, rng, nsamp=70, xstar=xstar)
    print(f"  ran algo for {len(cuts)} cuts; final err={hist[-1]['err']:.2e} "
          f"vmag={hist[-1]['vmag']:.2e}", flush=True)
    t0 = time.time()
    for t in sorted(set([d, min(len(cuts), 2*d)])):
        if t > len(cuts):
            continue
        res = probe_round(f, d, cuts[:t], xstar, rng)
        print(f"  X_{t:2d}: trap={res['trap']:.3f}  h_hat(marg-Cheeger)={res['h']:.3e}  "
              f"diam={res['diam']:.2f}  fr(0.05,0.1,0.2)="
              f"{res['fr'][0.05]:.3f},{res['fr'][0.1]:.3f},{res['fr'][0.2]:.3f}  "
              f"[{time.time()-t0:.0f}s]", flush=True)
    print("done", flush=True)

if __name__ == "__main__":
    main()
