import os
"""Decisive mixing/bottleneck test on REAL SSG algorithm bodies.
Design: (1) long explorer hit-and-run from x* to map the body; (2) pick starts
at the EXTREMES of the explorer cloud (top PCA directions) + x*; (3) run
independent chains from those extremes; (4) do opposite-end chains reconcile?
Trap = between/total variance of chain means (R-hat-like). Also whitened
(isotropic) marginal-Cheeger, GATED on the body being full-dimensional."""
import sys, time
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import (make_ssg, fixed_point, run_algo, hitrun, in_X,
                    marginal_cheeger, candidate_directions, whiten)

def extreme_starts(explorer, k=6):
    """Starts at the extremes of the cloud along top principal directions."""
    mu = explorer.mean(0)
    C = np.cov(explorer.T) + 1e-12 * np.eye(explorer.shape[1])
    w, V = np.linalg.eigh(C)
    starts = [explorer[np.argmax(explorer @ V[:, -1])],
              explorer[np.argmin(explorer @ V[:, -1])],
              explorer[np.argmax(explorer @ V[:, -2])],
              explorer[np.argmin(explorer @ V[:, -2])]]
    starts.append(mu.copy())
    return starts[:k]

def trap_metric(chains):
    means = np.array([c.mean(0) for c in chains])
    allp = np.vstack(chains)
    return float((means.var(0) / (allp.var(0) + 1e-15)).max())

def cond_number(S):
    C = np.cov(S.T)
    w = np.linalg.eigvalsh(C)
    return float(w.max() / max(w.min(), 1e-18)), float(w.min())

def probe(f, d, cuts, xstar, rng):
    # explorer
    expl = hitrun(cuts, d, xstar.copy(), nsamp=400, thin=15, burn=2000, rng=rng, nt=2500)
    if len(expl) < 50:
        return None
    starts = extreme_starts(expl)
    # verify starts feasible (they are explorer points => feasible)
    chains = [hitrun(cuts, d, s.copy(), nsamp=120, thin=20, burn=1500, rng=rng, nt=2500)
              for s in starts]
    trap = trap_metric(chains)
    pooled = np.vstack(chains + [expl])
    kappa, mineig = cond_number(pooled)
    dirs = candidate_directions(pooled, xstar=xstar, n_random=250, rng=rng)
    h_raw, _, _ = marginal_cheeger(pooled, dirs, min_side=0.03)
    # isotropic only trustworthy if full-dimensional (kappa not huge)
    h_iso, bd, info = marginal_cheeger(pooled, dirs, min_side=0.03, isotropic=True)
    diam = float((pooled.max(0) - pooled.min(0)).max())
    fr = {r: float((np.abs(pooled - xstar).max(1) <= r).mean()) for r in [0.05, 0.1, 0.2]}
    return dict(trap=trap, h_raw=h_raw, h_iso=h_iso, kappa=kappa, mineig=mineig,
                diam=diam, fr=fr, n=len(pooled))

def main():
    d = int(sys.argv[1]); delta = float(sys.argv[2]); seed = int(sys.argv[3])
    rng = np.random.default_rng(seed)
    f, types = make_ssg(d, delta, seed)
    xstar = fixed_point(f, d)
    print(f"[SSG d={d} delta={delta} seed={seed}] spread={xstar.max()-xstar.min():.3f} "
          f"x*={np.round(xstar,2)}", flush=True)
    cuts, hist = run_algo(f, d, 3 * d, rng, nsamp=70, xstar=xstar)
    print(f"  algo: {len(cuts)} cuts err={hist[-1]['err']:.2e}", flush=True)
    t0 = time.time()
    for t in sorted(set([d, min(len(cuts), 2 * d), len(cuts)])):
        if t < 1 or t > len(cuts):
            continue
        r = probe(f, d, cuts[:t], xstar, rng)
        if r is None:
            print(f"  X_{t}: explorer failed", flush=True); continue
        print(f"  X_{t:2d}: TRAP={r['trap']:.3f}  h_iso={r['h_iso']:.3e} "
              f"h_raw={r['h_raw']:.3e}  kappa={r['kappa']:.1f} mineig={r['mineig']:.1e} "
              f"diam={r['diam']:.2f} fr.2={r['fr'][0.2]:.2f}  [{time.time()-t0:.0f}s]",
              flush=True)
    print("done", flush=True)

if __name__ == "__main__":
    main()
