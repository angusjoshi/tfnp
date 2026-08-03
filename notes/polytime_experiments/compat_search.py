import os
"""Barrier search over REALIZABLE-STRUCTURE cut families: every cut points from
its apex c toward a common point x0 (sign s = sign(x0 - c)), so x0 is always
kept (this is exactly the cut-validity structure of a real contraction whose
fixed point is x0). Vary the apex distribution adversarially and measure the
marginal-Cheeger via exact rejection sampling. Looking for h -> 2^{-Omega(d)}."""
import numpy as np, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import in_X, marginal_cheeger, candidate_directions

def valid_cut(c, x0):
    s = np.sign(x0 - c)
    s[s == 0] = 0.0
    return c.copy(), s

def rej_uniform(cuts, d, N, rng, maxtries=250):
    out = []; tries = 0
    while len(out) < N and tries < maxtries:
        P = rng.uniform(0, 1, size=(4 * N, d))
        out.extend(list(P[in_X(P, cuts)])); tries += 1
    frac = (len(out) / (tries * 4 * N)) if tries else 0.0
    return (np.array(out[:N]) if out else np.empty((0, d))), frac

def measure(cuts, d, x0, seed, N=10000):
    rng = np.random.default_rng(seed)
    S, frac = rej_uniform(cuts, d, N, rng)
    if len(S) < 800:
        return None, frac, len(S)
    dirs = candidate_directions(S, xstar=x0, n_random=250, rng=rng)
    h, bd, info = marginal_cheeger(S, dirs, min_side=0.02)
    hs, _, _ = marginal_cheeger(S, dirs, min_side=0.003)
    return dict(h=h, hs=hs, frac=frac, n=len(S), bd=bd, info=info), frac, len(S)

def strategy_apexes(name, d, ncuts, rng, x0):
    """Return a list of apexes according to an adversarial strategy."""
    if name == "iso":            # isotropic small jitter around x0
        return [np.clip(x0 + rng.normal(scale=0.2, size=d), 0.02, 0.98) for _ in range(ncuts)]
    if name == "axis":           # apexes strung along coordinate-1 axis (try axial pinch)
        A = []
        for _ in range(ncuts):
            c = x0 + rng.normal(scale=0.05, size=d)
            c[0] = rng.uniform(0.05, 0.95)          # spread apex along axis 1
            A.append(np.clip(c, 0.02, 0.98))
        return A
    if name == "shell":          # apexes on a shell far from x0 (strong cones)
        A = []
        for _ in range(ncuts):
            u = rng.normal(size=d); u /= np.linalg.norm(u)
            A.append(np.clip(x0 + 0.45 * u, 0.02, 0.98))
        return A
    if name == "twoclust":       # apexes in two antipodal clusters (try to split)
        A = []
        for k in range(ncuts):
            base = x0 + (0.3 if k % 2 else -0.3) * np.eye(d)[0]
            A.append(np.clip(base + rng.normal(scale=0.08, size=d), 0.02, 0.98))
        return A
    raise ValueError(name)

if __name__ == "__main__":
    strategies = ["iso", "axis", "shell", "twoclust"]
    for d in [5, 7, 9, 12]:
        x0 = np.full(d, 0.5)
        print(f"\n##### d={d} #####", flush=True)
        for strat in strategies:
            best_h = np.inf; best_info = None
            for trial in range(4):
                rng = np.random.default_rng(100 * d + 7 * trial + hash(strat) % 1000)
                for ncuts in [d, 2 * d, 3 * d]:
                    apexes = strategy_apexes(strat, d, ncuts, rng, x0)
                    cuts = [valid_cut(c, x0) for c in apexes]
                    assert in_X(x0, cuts).all(), "x0 must be kept"
                    res, frac, n = measure(cuts, d, x0, seed=trial)
                    if res is None:
                        continue
                    if res["h"] < best_h:
                        best_h = res["h"]; best_info = (ncuts, frac, res["hs"], n)
            if best_info:
                nc, fr, hs, n = best_info
                print(f"  [{strat:9s}] min h_hat={best_h:.3e}  (hs={hs:.3e}) "
                      f"@ncuts={nc} volfrac={fr:.3f} n={n}", flush=True)
            else:
                print(f"  [{strat:9s}] all families ~empty", flush=True)
    print("done", flush=True)
