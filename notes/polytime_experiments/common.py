"""Shared machinery: topical instances, cut generation, membership, hit-and-run,
and bottleneck diagnostics for X_t = box ∩ ⋂_r K(c^r,s^r)."""
import numpy as np
from scipy.optimize import linprog

# ---------- hard topical (Shapley / SSG-style) instance ----------
def make_topical(d, delta, seed):
    rng = np.random.default_rng(seed)
    types = rng.integers(0, 3, size=d)                      # 0 max,1 min,2 avg
    nbrs = [rng.choice(d, size=rng.integers(2, min(5, d) + 1), replace=False)
            for _ in range(d)]
    r = rng.uniform(0, 1, size=d)
    def G(x):
        out = np.empty(d)
        for i in range(d):
            xs = x[nbrs[i]]
            out[i] = xs.max() if types[i] == 0 else xs.min() if types[i] == 1 else xs.mean()
        return out
    def f(x):
        return np.clip((1 - delta) * G(x) + delta * r, 0.0, 1.0)
    return f, types

def make_ssg(d, delta, seed):
    """Discounted simple-stochastic-game value operator. Two sinks (values 0,1),
    d interior MAX/MIN/AVG states with random successors and rewards. gamma=1-delta.
    Fixed point x* is genuinely SPREAD across [0,1] (the hard SSG regime)."""
    rng = np.random.default_rng(seed)
    gamma = 1 - delta
    types = rng.integers(0, 3, size=d)
    rew = rng.uniform(0, 1, size=d)
    # successors: indices in [0,d-1] interior, -1 = sink0 (val 0), -2 = sink1 (val 1)
    succ = []
    for i in range(d):
        k = int(rng.integers(2, min(5, d + 2) + 1))
        cand = list(range(d)) + [-1, -2]
        succ.append(rng.choice(cand, size=k, replace=False))
    def val(x, j):
        return x[j] if j >= 0 else (0.0 if j == -1 else 1.0)
    def f(x):
        out = np.empty(d)
        for i in range(d):
            vs = np.array([val(x, j) for j in succ[i]])
            op = vs.max() if types[i] == 0 else vs.min() if types[i] == 1 else vs.mean()
            out[i] = min(1.0, max(0.0, (1 - gamma) * rew[i] + gamma * op))
        return out
    return f, types

def make_ssg_full(d, delta, seed):
    """Identical construction to make_ssg (same seed -> same instance), but also
    returns the internals needed for the value-separation gap delta:
      returns (f, types, succ, rew, gamma).
    Kept byte-for-byte in sync with make_ssg's RNG draw order so the operator f
    here is the SAME operator make_ssg(d,delta,seed) produces."""
    rng = np.random.default_rng(seed)
    gamma = 1 - delta
    types = rng.integers(0, 3, size=d)
    rew = rng.uniform(0, 1, size=d)
    succ = []
    for i in range(d):
        k = int(rng.integers(2, min(5, d + 2) + 1))
        cand = list(range(d)) + [-1, -2]
        succ.append(rng.choice(cand, size=k, replace=False))
    def val(x, j):
        return x[j] if j >= 0 else (0.0 if j == -1 else 1.0)
    def f(x):
        out = np.empty(d)
        for i in range(d):
            vs = np.array([val(x, j) for j in succ[i]])
            op = vs.max() if types[i] == 0 else vs.min() if types[i] == 1 else vs.mean()
            out[i] = min(1.0, max(0.0, (1 - gamma) * rew[i] + gamma * op))
        return out
    return f, types, succ, rew, gamma

def ssg_value_gap(xstar, types, succ):
    """Value-separation gap delta at the fixed point x*. For each MAX interior
    state: (largest successor value) - (2nd largest); for MIN: (2nd smallest) -
    (smallest); AVG states skipped. delta = min over MAX/MIN states (smallest
    decision margin). Sink values: -1 -> 0.0, -2 -> 1.0. Returns (delta, gaps)."""
    def val(j):
        return xstar[j] if j >= 0 else (0.0 if j == -1 else 1.0)
    gaps = []
    for i in range(len(types)):
        if types[i] == 2:                     # AVG: no decision, skip
            continue
        vs = np.sort(np.array([val(j) for j in succ[i]]))
        if len(vs) < 2:
            continue
        if types[i] == 0:                     # MAX: top - second
            gaps.append(float(vs[-1] - vs[-2]))
        else:                                 # MIN: second - bottom
            gaps.append(float(vs[1] - vs[0]))
    delta = float(min(gaps)) if gaps else float('nan')
    return delta, gaps

def fixed_point(f, d, it=3_000_000, tol=1e-13):
    x = np.full(d, 0.5)
    for _ in range(it):
        y = f(x)
        if np.max(np.abs(y - x)) < tol:
            return y
        x = y
    return x

# ---------- cut construction (ternary sign, essential) ----------
TOL = 1e-9
def make_cut(f, c):
    v = f(c) - c
    s = np.sign(v)
    s[np.abs(v) <= TOL] = 0.0
    return c.copy(), s.copy(), float(np.max(np.abs(v)))

def in_box(P):
    return (P.min(axis=1) >= -1e-9) & (P.max(axis=1) <= 1 + 1e-9)

def K_ok(P, c, s):
    """y∈K iff max_{active} s_i(y_i-c_i) >= ||y-c||_inf (=max over ALL coords)."""
    act = s != 0
    if not act.any():
        return np.ones(len(P), bool)
    D = P - c[None, :]
    W = s[None, :] * D
    lhs = np.where(act[None, :], W, -np.inf).max(1)
    rhs = np.abs(D).max(1)
    return lhs >= rhs - 1e-9

def in_X(P, cuts):
    P = np.atleast_2d(P)
    ok = in_box(P)
    for (c, s) in cuts:
        ok &= K_ok(P, c, s)
    return ok

# ---------- hit-and-run (fine chords, hops between intervals) ----------
def chord_ts(p, u, cuts, nt=4000, span=3.0):
    ts = np.linspace(-span, span, nt)
    P = p[None, :] + ts[:, None] * u[None, :]
    ok = in_X(P, cuts)
    return ts[ok]

def hitrun(cuts, d, start, nsamp=100, thin=25, burn=1500, rng=None, nt=4000):
    if rng is None:
        rng = np.random.default_rng()
    p = start.copy()
    out = []
    k = 0
    cap = burn + thin * nsamp * 8
    while len(out) < nsamp and k < cap:
        u = rng.normal(size=d); u /= np.linalg.norm(u)
        fts = chord_ts(p, u, cuts, nt=nt)
        if len(fts) > 0:
            p = p + rng.choice(fts) * u
        k += 1
        if k >= burn and k % thin == 0:
            out.append(p.copy())
    return np.array(out) if out else start[None, :].copy()

# ---------- balanced point (Fermat-Weber LP) ----------
def balanced(S, d):
    N = len(S)
    cobj = np.concatenate([np.zeros(d), np.ones(N)])
    A = []; b = []
    for j, y in enumerate(S):
        for i in range(d):
            row = np.zeros(d + N); row[i] = 1;  row[d + j] = -1; A.append(row); b.append(y[i])
            row = np.zeros(d + N); row[i] = -1; row[d + j] = -1; A.append(row); b.append(-y[i])
    res = linprog(cobj, A_ub=np.array(A), b_ub=np.array(b),
                  bounds=[(0, 1)] * d + [(0, None)] * N, method='highs')
    return res.x[:d] if res.success else S.mean(0)

# ---------- run the algorithm, record cut history ----------
def run_algo(f, d, R, rng, nsamp=80, verbose=False, xstar=None):
    cuts = []
    start = np.full(d, 0.5)
    hist = []
    for t in range(R):
        S = hitrun(cuts, d, start, nsamp=nsamp, rng=rng)
        bp = balanced(S, d)
        c_, s_, vmag = make_cut(f, bp)
        err = np.max(np.abs(bp - xstar)) if xstar is not None else float('nan')
        spread = float((np.max(S, 0) - np.min(S, 0)).max())
        hist.append(dict(t=t, bp=bp, vmag=vmag, err=err, spread=spread,
                         nactive=int((s_ != 0).sum())))
        if verbose:
            print(f"  r{t:3d} err={err:.2e} spread={spread:.2e} "
                  f"||f(bp)-bp||={vmag:.2e} nact={int((s_!=0).sum())}", flush=True)
        if vmag < 1e-11:
            break
        cuts.append((c_, s_))
        start = bp.copy()
    return cuts, hist

# ---------- 1-D marginal Cheeger (certified sparse-cut upper bound on h) ----------
def _smooth(c, k=3):
    if k <= 1:
        return c
    ker = np.ones(k) / k
    return np.convolve(c, ker, mode='same')

def whiten(samples):
    """Transform to identity covariance (isotropic position). Returns whitened
    samples and the map W such that whitened = (samples-mu) @ W."""
    mu = samples.mean(0)
    C = np.cov(samples.T) + 1e-9 * np.eye(samples.shape[1])
    vals, vecs = np.linalg.eigh(C)
    W = vecs @ np.diag(1.0 / np.sqrt(np.maximum(vals, 1e-12))) @ vecs.T
    return (samples - mu) @ W, W

def marginal_cheeger(samples, directions, min_side=0.02, nbins=160, smooth=5,
                     isotropic=False):
    """For each unit direction a, min over threshold b of rho_a(b)/min(F,1-F),
    the Cheeger constant of the 1-D projected density (histogram est.).
    If isotropic=True, first whiten to identity covariance so ELONGATION does
    not masquerade as a bottleneck (this is the mixing-relevant quantity).
    Returns (best_h, best_dir, info). An UPPER bound on h of the (whitened) body."""
    n = len(samples)
    if isotropic:
        samples, _ = whiten(samples)
        d = samples.shape[1]
        rng = np.random.default_rng(0)
        extra = rng.normal(size=(200, d))
        directions = list(directions) + [e for e in np.eye(d)] + list(extra)
    D = np.array([a / (np.linalg.norm(a) + 1e-15) for a in directions])  # (m,d)
    proj_all = samples @ D.T                                             # (n,m)
    best = (np.inf, None, None)
    for j in range(D.shape[0]):
        proj = proj_all[:, j]
        lo, hi = proj.min(), proj.max()
        if hi - lo < 1e-9:
            continue
        edges = np.linspace(lo, hi, nbins + 1)
        cnt, _ = np.histogram(proj, bins=edges)
        w = edges[1] - edges[0]
        dens = _smooth(cnt.astype(float), smooth) / (n * w)     # density at bin centers
        F = np.cumsum(cnt) / n                                   # CDF at right edges
        # align: use bin centers; F at center ~ cumcount up to center
        Fc = (np.cumsum(cnt) - 0.5 * cnt) / n
        side = np.minimum(Fc, 1 - Fc)
        mask = side >= min_side
        if not mask.any():
            continue
        ratio = np.where(mask, dens / np.maximum(side, 1e-12), np.inf)
        idx = int(np.argmin(ratio))
        h = ratio[idx]
        if h < best[0]:
            centers = 0.5 * (edges[:-1] + edges[1:])
            best = (h, D[j].copy(), dict(b=centers[idx], F=Fc[idx], rho=dens[idx]))
    return best

def candidate_directions(samples, xstar=None, d=None, n_random=200, rng=None):
    if rng is None:
        rng = np.random.default_rng(0)
    dirs = []
    d = samples.shape[1]
    for i in range(d):                      # coordinate axes
        e = np.zeros(d); e[i] = 1; dirs.append(e)
    mu = samples.mean(0)
    C = np.cov(samples.T) + 1e-12 * np.eye(d)
    w, V = np.linalg.eigh(C)
    for i in range(d):                      # principal axes
        dirs.append(V[:, i])
    if xstar is not None:                   # toward x*
        v = xstar - mu
        if np.linalg.norm(v) > 1e-9:
            dirs.append(v)
    for _ in range(n_random):               # random
        dirs.append(rng.normal(size=d))
    return dirs
