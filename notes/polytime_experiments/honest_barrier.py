import os
"""Honest per-cut barrier search. A real contraction's cut at apex c only
guarantees x* in K(c,s) (i.e. max_i w_i + min_i w_i >= 0, w_i=s_i(x*_i-c_i)),
NOT that s points toward x* on every coord. Coord i may point AWAY from x*
whenever |x*_i - c_i| < lam*r (r = ||x*-c||_inf). We search adversarially over
such honest signs to try to build a bottleneck (small marginal-Cheeger).
"""
import numpy as np, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import in_X, marginal_cheeger, candidate_directions

def xstar_kept(c, s, xstar):
    w = s * (xstar - c)
    return w.max() + w.min() >= -1e-12

def honest_sign(c, xstar, mode, rng, lam=0.999, target=None):
    """Return a ternary sign s with x* in K(c,s). 'mode' picks adversariality."""
    g = xstar - c
    r = np.abs(g).max()
    j = int(np.argmax(np.abs(g)))
    toward = np.sign(g); toward[toward == 0] = 1.0
    can_flip = np.abs(g) < lam * r - 1e-9      # coords allowed to point away
    can_flip[j] = False
    s = toward.copy()
    if mode == "away":                          # point away wherever allowed
        s[can_flip] = -toward[can_flip]
    elif mode == "rand":
        flip = can_flip & (rng.random(len(c)) < 0.5)
        s[flip] = -toward[flip]
    elif mode == "target":                      # push toward a fixed target pattern
        want = np.where(target >= 0, 1.0, -1.0)  # desired sign
        s[can_flip] = want[can_flip]
    # safety: ensure x* still kept (flipping only 'can_flip' coords keeps it,
    # since worst-case min becomes -max_{i!=j}|g_i| >= -r = -w_j)
    if not xstar_kept(c, s, xstar):
        s = toward.copy()
    return s

def rej_uniform(cuts, d, N, rng, maxtries=250):
    out = []; tries = 0
    while len(out) < N and tries < maxtries:
        P = rng.uniform(0, 1, size=(4 * N, d))
        out.extend(list(P[in_X(P, cuts)])); tries += 1
    frac = (len(out) / (tries * 4 * N)) if tries else 0.0
    return (np.array(out[:N]) if out else np.empty((0, d))), frac

def measure(cuts, d, xstar, seed, N=10000):
    rng = np.random.default_rng(seed)
    S, frac = rej_uniform(cuts, d, N, rng)
    if len(S) < 800:
        return None, frac, len(S)
    dirs = candidate_directions(S, xstar=xstar, n_random=300, rng=rng)
    h, bd, info = marginal_cheeger(S, dirs, min_side=0.02)
    hiso, _, _ = marginal_cheeger(S, dirs, min_side=0.02, isotropic=True)  # TRUE bottleneck
    return dict(h=h, hiso=hiso, frac=frac, n=len(S), bd=bd), frac, len(S)

def apex_strategy(name, d, ncuts, rng, xstar):
    if name == "iso":
        return [np.clip(xstar + rng.normal(scale=0.2, size=d), 0.02, 0.98) for _ in range(ncuts)]
    if name == "close":   # apexes CLOSE to x* -> r small -> most coords can flip
        return [np.clip(xstar + rng.normal(scale=0.06, size=d), 0.02, 0.98) for _ in range(ncuts)]
    if name == "shell":
        A = []
        for _ in range(ncuts):
            u = rng.normal(size=d); u /= np.linalg.norm(u)
            A.append(np.clip(xstar + rng.uniform(0.2,0.45) * u, 0.02, 0.98))
        return A
    raise ValueError(name)

if __name__ == "__main__":
    for d in [5, 7, 9, 12, 15]:
        rng0 = np.random.default_rng(d)
        xstar = rng0.uniform(0.25, 0.75, size=d)   # SPREAD fixed point (not diagonal)
        print(f"\n##### d={d}  x*={np.round(xstar,2)} #####", flush=True)
        for apex in ["iso", "close", "shell"]:
            for mode in ["away", "rand", "target"]:
                best = np.inf; binfo = None
                for trial in range(4):
                    rng = np.random.default_rng(1000*d + 17*trial + hash((apex,mode))%997)
                    target = rng.choice([-1.,1.], size=d)   # random target pattern for 'target'
                    for ncuts in [d, 2*d, 3*d]:
                        apexes = apex_strategy(apex, d, ncuts, rng, xstar)
                        cuts = [(c.copy(), honest_sign(c, xstar, mode, rng, target=target)) for c in apexes]
                        assert in_X(xstar, cuts).all()
                        res, frac, n = measure(cuts, d, xstar, seed=trial)
                        if res and res["hiso"] < best:
                            best = res["hiso"]; binfo = (ncuts, frac, res["h"], n)
                if binfo:
                    nc, fr, hs, n = binfo
                    print(f"  [{apex:6s}/{mode:6s}] min h_ISO={best:.3e} (raw h={hs:.3e}) "
                          f"@nc={nc} vf={fr:.3f} n={n}", flush=True)
                else:
                    print(f"  [{apex:6s}/{mode:6s}] empty", flush=True)
    print("done", flush=True)
