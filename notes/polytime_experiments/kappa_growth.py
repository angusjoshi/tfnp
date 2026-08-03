import os
"""C2 empirics: growth law of the covariance condition number kappa(X_t) under
REALIZABLE balanced cuts. Uses a warm-start sequential sampler that exploits the
exact halving of a balanced cut: keep a large uniform pool of X_t; to advance,
(1) pick balanced FW center c from a subsample, (2) cut with the real sign, (3)
survivors (~half) are exactly uniform on X_{t+1}, (4) replenish to full size by
short hit-and-run seeded at survivors. kappa is measured on the full pool.
Budget-escalation control: rerun with 2x replenish budget, kappa must be stable.
"""
import sys, time
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import (make_ssg, make_topical, fixed_point, in_X, chord_ts,
                    balanced, make_cut, whiten)

def kappa(S):
    C = np.cov(S.T)
    w = np.linalg.eigvalsh(C)
    return float(w.max() / max(w.min(), 1e-18)), float(w.min()), float(w.max())

def rej_box(d, N, rng):
    P = rng.uniform(0, 1, size=(N, d))
    return P

def hr_step(p, cuts, d, rng, nstep, nt=3000):
    for _ in range(nstep):
        u = rng.normal(size=d); u /= np.linalg.norm(u)
        fts = chord_ts(p, u, cuts, nt=nt)
        if len(fts) > 0:
            p = p + rng.choice(fts) * u
    return p

def replenish(pool, cuts, d, target, rng, nstep):
    """Grow 'pool' (uniform on X) up to 'target' by short hit-and-run from
    randomly chosen existing pool points."""
    out = list(pool)
    while len(out) < target:
        seed = out[rng.integers(len(out))].copy()
        out.append(hr_step(seed, cuts, d, rng, nstep, nt=3000))
    return np.array(out[:target])

def run(f, d, rounds, rng, N=1500, nstep=25, sub=70, label=""):
    # start: uniform on box
    pool = rej_box(d, N, rng)
    cuts = []
    hist = []
    for t in range(rounds):
        sub_idx = rng.choice(len(pool), size=min(sub, len(pool)), replace=False)
        c = balanced(pool[sub_idx], d)
        c_, s_, vmag = make_cut(f, c)
        k, lo, hi = kappa(pool)
        hist.append((t, k, lo, hi, vmag))
        if vmag < 1e-11:
            break
        cuts.append((c_, s_))
        surv = pool[in_X(pool, cuts)]           # survivors ~ uniform on X_{t+1}
        if len(surv) < 20:
            hist.append((t + 1, float('nan'), 0, 0, -1)); break
        pool = replenish(surv, cuts, d, N, rng, nstep)
    return cuts, hist

def main():
    kind = sys.argv[1]        # 'ssg' or 'topical'
    d = int(sys.argv[2]); delta = float(sys.argv[3]); seed = int(sys.argv[4])
    rounds = int(sys.argv[5]) if len(sys.argv) > 5 else 3 * d
    rng = np.random.default_rng(seed)
    mk = make_ssg if kind == 'ssg' else make_topical
    f, _ = mk(d, delta, seed)
    xstar = fixed_point(f, d)
    print(f"[{kind} d={d} delta={delta} seed={seed}] spread={xstar.max()-xstar.min():.2f}",
          flush=True)
    t0 = time.time()
    cuts, hist = run(f, d, rounds, rng, label=kind)
    for (t, k, lo, hi, vmag) in hist:
        ratio = ""
        print(f"  t={t:3d}  kappa={k:8.2f}  lam_min={lo:.2e} lam_max={hi:.2e}  "
              f"vmag={vmag:.2e}", flush=True)
    ks = [h[1] for h in hist if not np.isnan(h[1])]
    if len(ks) > 2:
        # per-cut multiplicative ratios
        rr = [ks[i+1]/ks[i] for i in range(len(ks)-1) if ks[i] > 0]
        print(f"  SUMMARY kappa: start={ks[0]:.2f} end={ks[-1]:.2f} max={max(ks):.2f}  "
              f"median per-cut ratio={np.median(rr):.3f}  [{time.time()-t0:.0f}s]", flush=True)
    print("done", flush=True)

if __name__ == "__main__":
    main()
