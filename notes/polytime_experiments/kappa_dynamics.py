import os
"""C2 crux: is kappa an ATTRACTOR (bounded, self-correcting) under balanced cuts,
or does it compound (C^t)? Two tests:

(A) SELF-CORRECTION: start from an ARTIFICIALLY ELONGATED realizable body (apply
    several same-sign shifted cuts to stretch it), then apply balanced FW cuts and
    watch kappa. If kappa DECREASES toward O(1), balanced cuts are self-correcting
    => absolute bound. If it stays high / grows, compounding.

(B) LONG TRAJECTORY: real SSG, track kappa and lam_min/diam^2 over many rounds,
    with a 2x-budget escalation re-check at the end to rule out sampler inflation.

Warm-start sequential sampler (exact halving); escalation control included.
"""
import sys, time
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import make_ssg, fixed_point, in_X, chord_ts, balanced, make_cut

def kap(S):
    w = np.linalg.eigvalsh(np.cov(S.T))
    diam2 = float(((S.max(0) - S.min(0)) ** 2).sum())
    return float(w.max() / max(w.min(), 1e-18)), float(w.min()), float(w.max()), float(w.min())/max(diam2,1e-18)

def hr(p, cuts, d, rng, nstep, nt):
    for _ in range(nstep):
        u = rng.normal(size=d); u /= np.linalg.norm(u)
        fts = chord_ts(p, u, cuts, nt=nt)
        if len(fts) > 0:
            p = p + rng.choice(fts) * u
    return p

def replenish(surv, cuts, d, N, rng, nstep, nt):
    out = list(surv)
    while len(out) < N:
        out.append(hr(out[rng.integers(len(out))].copy(), cuts, d, rng, nstep, nt))
    return np.array(out[:N])

def elongate_cuts(d, k):
    """k cuts, all sign +1, apexes stepped along the main diagonal -> stretches
    the surviving body along the diagonal (a controlled anisotropy)."""
    cuts = []
    for i in range(k):
        c = np.full(d, 0.15 + 0.5 * i / max(k, 1))
        cuts.append((c, np.ones(d)))
    return cuts

def measure_pool(cuts, d, rng, N, nstep, nt):
    # seed a pool by rejection if feasible else hit-run from a feasible point
    P = rng.uniform(0, 1, size=(30 * N, d))
    good = P[in_X(P, cuts)]
    if len(good) >= 50:
        pool = replenish(list(good[:N]), cuts, d, N, rng, nstep, nt)
    else:
        # find one feasible via hit-run from box center projected
        p = np.full(d, 0.5)
        pool = replenish([hr(p, cuts, d, rng, 200, nt)], cuts, d, N, rng, nstep, nt)
    return pool

def testA(d, seed, nballanced=12):
    rng = np.random.default_rng(seed)
    f, _ = make_ssg(d, 1e-3, seed)
    xstar = fixed_point(f, d)
    N, nstep, nt = 1200, 15, 2000
    for k in [3, 5]:
        cuts = elongate_cuts(d, k)
        pool = measure_pool(cuts, d, rng, N, nstep, nt)
        k0, lo, hi, r0 = kap(pool)
        traj = [k0]
        # now apply balanced FW cuts (toward-sign for control star regime, x0=center)
        x0 = np.full(d, 0.5)
        for t in range(nballanced):
            sub = pool[rng.choice(len(pool), size=min(70, len(pool)), replace=False)]
            c = balanced(sub, d)
            s = np.sign(x0 - c); s[s == 0] = 1.0     # balanced toward-cut (star regime)
            cuts = cuts + [(c, s)]
            surv = pool[in_X(pool, cuts)]
            if len(surv) < 20:
                break
            pool = replenish(list(surv), cuts, d, N, rng, nstep, nt)
            traj.append(kap(pool)[0])
        print(f"  [A d={d}] elongated with {k} cuts -> kappa0={k0:.2f}; "
              f"after balanced cuts: {' '.join(f'{x:.1f}' for x in traj)}", flush=True)

def testB(d, seed, rounds):
    rng = np.random.default_rng(seed)
    f, _ = make_ssg(d, 1e-3, seed)
    xstar = fixed_point(f, d)
    N, nstep, nt = 1200, 15, 2000
    pool = rng.uniform(0, 1, size=(N, d))
    cuts = []
    print(f"  [B d={d}] real SSG trajectory (kappa | lam_min/diam^2):", flush=True)
    row = []
    for t in range(rounds):
        sub = pool[rng.choice(len(pool), size=min(70, len(pool)), replace=False)]
        c = balanced(sub, d)
        c_, s_, vmag = make_cut(f, c)
        k, lo, hi, rr = kap(pool)
        row.append((t, k, rr))
        if vmag < 1e-11: break
        cuts.append((c_, s_))
        surv = pool[in_X(pool, cuts)]
        if len(surv) < 20: break
        pool = replenish(list(surv), cuts, d, N, rng, nstep, nt)
    print("    " + "  ".join(f"t{t}:k={k:.1f},r={rr:.1e}" for (t,k,rr) in row), flush=True)
    # escalation re-check on final body at 2x budget
    if cuts:
        pool2 = replenish([pool[i] for i in range(min(200,len(pool)))], cuts, d, N, rng, nstep*3, nt+1000)
        k2 = kap(pool2)[0]
        print(f"    escalation check final kappa: base={kap(pool)[0]:.2f}  2x-budget={k2:.2f}", flush=True)

def main():
    mode = sys.argv[1]; d = int(sys.argv[2]); seed = int(sys.argv[3])
    if mode == "A":
        testA(d, seed, int(sys.argv[4]) if len(sys.argv) > 4 else 12)
    else:
        testB(d, seed, int(sys.argv[4]) if len(sys.argv) > 4 else 3 * d)
    print("done", flush=True)

if __name__ == "__main__":
    main()
