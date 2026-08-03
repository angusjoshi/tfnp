"""fearnley_mdp.py -- Fearnley's binary-counter MDP (the FAST FILTER for Idea D),
with the exact-value LP certificate and a value-space policy read-off.

WHY THIS FILE FIRST (rogue's point).  Before the two-player Friedmann family
(friedmann.py -> Melekopoglou-Condon here), test the value-space FW-center pivot on
Fearnley's ONE-PLAYER MDP:
    J. Fearnley, "Exponential Lower Bounds for Policy Iteration", ICALP 2010,
    arXiv:1003.3418 -- an adaptation of O. Friedmann, "A super-polynomial lower
    bound for the parity game strategy improvement algorithm as we know it",
    LICS 2009.
It is the ideal filter because:
  * 1-player  => simplest to encode and to sample (only MAX + the single
    probabilistic action a_i; no min/max interplay);
  * GREEDY (switch-all / Howard) policy iteration takes >= 2^n iterations on it
    (Fearnley Thm 17/18) -- a STRONGER adversary than Melekopoglou-Condon, which
    only defeats single-switch rules;
  * the value is LP/linear-solve computable, so the certificate + decision margin
    are exactly verifiable;
  * the total-reward value operator is monotone piecewise-linear, so the
    FW-center cutting method applies verbatim to a uniformly-rescaled box version.

If the FW-center pivot is EXP even here, Idea D dies cheaply.  If it is poly here,
escalate to friedmann.py (the two-player game) -- because MDPs are in P (LP), so
poly-FW on this MDP is NECESSARY-NOT-SUFFICIENT: it only shows "FW is not fooled
by a Howard-hard instance", not that FW solves SSG.  Friedmann is the real test.

CONSTRUCTION (faithful to arXiv:1003.3418; total-reward criterion).  n bits.
Per bit i in 1..n, states b_i, g_i, r_i, c_i, f_i; a deceleration lane
d_0..d_{2n}; global states x, y; absorbing sink c_{n+1} (value 0).  All controller
states MAXimize expected total reward.  Actions (reward on the action; a_i is the
ONLY probabilistic action):
  b_i : a_i  = prob action, reward 0, ->g_i w.p. 1/((10n+4)2^n) else ->b_i
              (Prop 2: if chosen, Val(b_i)=Val(g_i); Prop 4: if NOT chosen,
               Appeal(b_i,a_i) < Val(b_i)+1 -- the tiny prob is ESSENTIAL and is
               kept exact, never collapsed to a deterministic edge);
        (b_i,x) r=0 ; (b_i,y) r=1 ; (b_i,d_k) r=2k for k=1..2i ;
        (b_i,f_k) r=4n+1 for k=i+1..n .
  g_i : (g_i,r_i) r=(10n+4)2^i .
  r_i : (r_i,c_k) r=-1 for k=i+1..n+1 .
  c_i : (c_i,f_i) r=4n+1 ; (c_i,r_i) r=0 .
  f_i : (f_i,b_i) r=-(10n+4)2^{i-1} - 4n .
  d_0 : (d_0,y) r=4n+1 ; (d_0,x) r=4n+1 .
  d_k : (d_k,d_{k-1}) r=-1 ; (d_k,y) r=0 ; (d_k,x) r=0   (k=1..2n).
  x   : (x,f_i) r=0 for i=1..n ; (x,c_{n+1}) r=-1 .
  y   : (y,c_i) r=0 for i=1..n+1 .
States: 7n+4.  Initial policy pi^emptyset_0 (Fearnley Thm 17): every d_k->y,
every b_i->y, c_i->r_i, r_i->c_{n+1}, y->c_{n+1}, x->c_{n+1}.

REGIME.  Fearnley's theorem is the total-reward (gamma=1) criterion; the sink makes
policy values finite and LP-computable there (Ye 2011: fixed discount => Howard is
strongly poly, so the hard behaviour must be gamma->1).  We compute the certificate
and Howard baseline at gamma=1 (matches the theorem exactly, self-verified to give
>= 2^n).  The FW-center cutting method needs a strict ell_inf-contraction, so it
runs on `f_box`, the total-reward operator DISCOUNTED at gamma=1-delta and
uniformly rescaled into [0,1]^d (uniform scaling preserves the ell_inf-contraction
factor exactly).  delta must be small enough (~2^{-(n+c)}) that the discounted
optimum's greedy policy equals the total-reward optimum; the certificate is checked
at gamma=1 so the stopping test is the true Fearnley optimum.

NOTE ON REPRESENTATION vs common.py.  Fearnley needs per-ACTION rewards (large and
negative) and one probabilistic action, which common.make_ssg's single per-state
reward + fixed max/min/mean operator cannot express.  So this file uses a general
reward-MDP structure; the FW-facing `f_box: [0,1]^d -> [0,1]^d` is exactly the
interface `common.run_algo` consumes, with `to_value`/`from_value` converters.
"""
import numpy as np

try:
    from common import balanced, hitrun, make_cut
except Exception:
    balanced = hitrun = make_cut = None


# ============================================================================
# 1. BUILD THE MDP
# ============================================================================
class MDP:
    """General reward-MDP.  states: list of names; act[s] = list of actions, each
    {'r': reward, 'dist': [(prob, succ_idx), ...], 'label': (...)};
    ctrl[s] = True if a controller (MAX) state (>1 action or genuinely chosen);
    sink = index of the absorbing value-0 sink."""
    def __init__(self, n):
        self.n = n
        self.name2idx = {}
        self.names = []
        self.act = []
        self.ctrl = []
        self.sink = None

    def add(self, name, ctrl=True):
        i = len(self.names)
        self.name2idx[name] = i
        self.names.append(name)
        self.act.append([])
        self.ctrl.append(ctrl)
        return i

    def action(self, s, reward, dist, label):
        """dist: list of (prob, succ_name)."""
        d = [(p, self.name2idx[t]) for (p, t) in dist]
        self.act[s].append(dict(r=float(reward), dist=d, label=label))

    @property
    def d(self):
        return len(self.names)


def build_fearnley(n):
    """Construct Fearnley's total-reward MDP with n bits.  Returns an MDP."""
    assert n >= 1
    m = MDP(n)
    P = (10 * n + 4)                                   # base multiplier
    # --- create states first (so names resolve) ---
    for i in range(1, n + 1):
        m.add(f"b{i}"); m.add(f"g{i}", ctrl=False)
        m.add(f"r{i}"); m.add(f"c{i}"); m.add(f"f{i}", ctrl=False)
    for k in range(0, 2 * n + 1):
        m.add(f"d{k}")
    m.add("x"); m.add("y")
    m.sink = m.add(f"c{n+1}", ctrl=False)
    # --- actions ---
    p_ai = 1.0 / (P * (2 ** n))                        # tiny prob to g_i
    for i in range(1, n + 1):
        b = m.name2idx[f"b{i}"]
        m.action(b, 0.0, [(p_ai, f"g{i}"), (1.0 - p_ai, f"b{i}")], ("a", i))
        m.action(b, 0.0, [(1.0, "x")], ("x",))
        m.action(b, 1.0, [(1.0, "y")], ("y",))
        for k in range(1, 2 * i + 1):
            m.action(b, 2 * k, [(1.0, f"d{k}")], ("d", k))
        for k in range(i + 1, n + 1):
            m.action(b, 4 * n + 1, [(1.0, f"f{k}")], ("f", k))
        g = m.name2idx[f"g{i}"]
        m.action(g, P * (2 ** i), [(1.0, f"r{i}")], ("r",))
        r = m.name2idx[f"r{i}"]
        for k in range(i + 1, n + 2):
            tgt = f"c{k}"
            m.action(r, -1.0, [(1.0, tgt)], ("c", k))
        c = m.name2idx[f"c{i}"]
        m.action(c, 4 * n + 1, [(1.0, f"f{i}")], ("f", i))
        m.action(c, 0.0, [(1.0, f"r{i}")], ("r",))
        f = m.name2idx[f"f{i}"]
        m.action(f, -(P * (2 ** (i - 1))) - 4 * n, [(1.0, f"b{i}")], ("b",))
    d0 = m.name2idx["d0"]
    m.action(d0, 4 * n + 1, [(1.0, "y")], ("y",))
    m.action(d0, 4 * n + 1, [(1.0, "x")], ("x",))
    for k in range(1, 2 * n + 1):
        dk = m.name2idx[f"d{k}"]
        m.action(dk, -1.0, [(1.0, f"d{k-1}")], ("d", k - 1))
        m.action(dk, 0.0, [(1.0, "y")], ("y",))
        m.action(dk, 0.0, [(1.0, "x")], ("x",))
    x = m.name2idx["x"]
    for i in range(1, n + 1):
        m.action(x, 0.0, [(1.0, f"f{i}")], ("f", i))
    m.action(x, -1.0, [(1.0, f"c{n+1}")], ("c", n + 1))
    y = m.name2idx["y"]
    for i in range(1, n + 2):
        m.action(y, 0.0, [(1.0, f"c{i}")], ("c", i))
    # sink: single self-loop reward 0 (value pinned to 0 in the solver)
    m.action(m.sink, 0.0, [(1.0, f"c{n+1}")], ("loop",))
    return m


def initial_policy_empty(m):
    """pi^emptyset_0 of Fearnley Thm 17 (from which Howard takes >= 2^n steps)."""
    sigma = np.zeros(m.d, dtype=int)
    def pick(s, label):
        for a, act in enumerate(m.act[s]):
            if act['label'] == label:
                return a
        raise KeyError(f"{m.names[s]} has no action {label}")
    n = m.n
    for i in range(1, n + 1):
        sigma[m.name2idx[f"b{i}"]] = pick(m.name2idx[f"b{i}"], ("y",))
        sigma[m.name2idx[f"c{i}"]] = pick(m.name2idx[f"c{i}"], ("r",))
        sigma[m.name2idx[f"r{i}"]] = pick(m.name2idx[f"r{i}"], ("c", n + 1))
    for k in range(0, 2 * n + 1):
        sigma[m.name2idx[f"d{k}"]] = pick(m.name2idx[f"d{k}"], ("y",))
    sigma[m.name2idx["x"]] = pick(m.name2idx["x"], ("c", n + 1))
    sigma[m.name2idx["y"]] = pick(m.name2idx["y"], ("c", n + 1))
    return sigma


# ============================================================================
# 2. CERTIFICATE LAYER  (exact policy value by linear solve; Bellman optimality)
# ============================================================================
def policy_eval(m, sigma, gamma=1.0):
    """Exact value of policy sigma: solve (I - gamma P_sigma) V = r_sigma over the
    transient states (sink pinned to V=0).  Rows are normalised by their diagonal
    for conditioning (the b_i self-loop under a_i has diagonal = tiny prob p, whose
    normalised row becomes exactly V(b_i) - V(g_i) = 0, cf. Prop 2).  Returns full
    V (length d) with V[sink] = 0."""
    d = m.d
    sink = m.sink
    tr = [s for s in range(d) if s != sink]
    pos = {s: t for t, s in enumerate(tr)}
    mt = len(tr)
    A = np.zeros((mt, mt))
    b = np.zeros(mt)
    for s in tr:
        act = m.act[s][int(sigma[s])]
        b[pos[s]] = act['r']
        A[pos[s], pos[s]] += 1.0
        for (p, sp) in act['dist']:
            if sp == sink:
                continue
            A[pos[s], pos[sp]] -= gamma * p
    diag = np.diag(A).copy()
    diag[np.abs(diag) < 1e-300] = 1.0
    A = A / diag[:, None]
    b = b / diag
    Vt = np.linalg.solve(A, b)
    V = np.zeros(d)
    for s in tr:
        V[pos[s] if False else s] = 0.0
    for s in tr:
        V[s] = Vt[pos[s]]
    return V


def appeal(m, V, s, a, gamma=1.0):
    """Appeal of action a at state s under value V: r(s,a) + gamma * E[V(succ)]."""
    act = m.act[s][a]
    tot = act['r']
    for (p, sp) in act['dist']:
        tot += gamma * p * (0.0 if sp == m.sink else V[sp])
    return tot


def greedy_policy(m, V, gamma=1.0):
    """Most-appealing action at every controller state given V."""
    sigma = np.zeros(m.d, dtype=int)
    for s in range(m.d):
        if s == m.sink or len(m.act[s]) <= 1:
            continue
        ap = [appeal(m, V, s, a, gamma) for a in range(len(m.act[s]))]
        sigma[s] = int(np.argmax(ap))
    return sigma


def is_optimal(m, sigma, V, gamma=1.0, tol=1e-6):
    """Bellman optimality: no action beats the chosen one by more than tol."""
    for s in range(m.d):
        if s == m.sink or len(m.act[s]) <= 1:
            continue
        chosen = appeal(m, V, s, int(sigma[s]), gamma)
        best = max(appeal(m, V, s, a, gamma) for a in range(len(m.act[s])))
        if best - chosen > tol:
            return False
    return True


def certify(m, sigma, gamma=1.0, tol=1e-6):
    """Sampler-free optimality certificate: (is_optimal, V_sigma)."""
    V = policy_eval(m, sigma, gamma)
    return is_optimal(m, sigma, V, gamma, tol), V


# ============================================================================
# 3. GREEDY (HOWARD) POLICY ITERATION  -- the >= 2^n baseline (self-certifying)
# ============================================================================
def howard_pi(m, sigma0=None, gamma=1.0, max_iters=None, tol=1e-9):
    """Switch-ALL greedy policy iteration (Fearnley's algorithm): each iteration,
    switch every controller state to its most-appealing action.  Returns
    (n_iters, sigma, V).  From pi^emptyset_0 this takes >= 2^n iterations."""
    if sigma0 is None:
        sigma0 = initial_policy_empty(m)
    if max_iters is None:
        max_iters = 8 * (2 ** min(m.n, 24)) + 100
    sigma = np.array(sigma0, dtype=int)
    for k in range(max_iters):
        V = policy_eval(m, sigma, gamma)
        new = sigma.copy()
        changed = False
        for s in range(m.d):
            if s == m.sink or len(m.act[s]) <= 1:
                continue
            ap = [appeal(m, V, s, a, gamma) for a in range(len(m.act[s]))]
            g = int(np.argmax(ap))
            if ap[g] - ap[int(sigma[s])] > tol:
                new[s] = g
                changed = True
        if not changed:
            return k, sigma, V
        sigma = new
    return max_iters, sigma, policy_eval(m, sigma, gamma)


# ============================================================================
# 4. VALUE OPERATOR + BOX EMBEDDING  (so the FW-center method applies verbatim)
# ============================================================================
def value_bounds(m):
    """Generous static [V_lo, V_hi] containing every value in Sequence(B)
    (Val(g_i) <= (10n+4)2^n by Assumption 3; the negative rewards bottom out near
    -(4n+1))."""
    n = m.n
    hi = (10 * n + 4) * (2 ** n) + 4 * n + 2
    lo = -(4 * n + 2)
    return float(lo), float(hi)


def bellman(m, V, gamma):
    """One application of the optimal total-reward operator T(V)_s =
    max_a (r(s,a) + gamma E[V(succ)]);  sink stays 0."""
    out = np.zeros(m.d)
    for s in range(m.d):
        if s == m.sink:
            out[s] = 0.0
            continue
        out[s] = max(appeal(m, V, s, a, gamma) for a in range(len(m.act[s])))
    return out


def make_box_operator(m, gamma_c):
    """Return (f_box, to_value, from_value):
      f_box: [0,1]^d -> [0,1]^d, the gamma_c-DISCOUNTED Fearnley operator
             uniformly rescaled into the unit box -- a strict ell_inf-contraction
             with factor gamma_c (uniform scaling preserves the factor), unique
             fixed point = rescaled discounted values.  This is exactly the
             interface `common.run_algo` consumes.
      to_value(x)   = V_lo + (V_hi - V_lo) * x
      from_value(V) = (V - V_lo) / (V_hi - V_lo)
    """
    lo, hi = value_bounds(m)
    R = hi - lo

    def to_value(x):
        return lo + R * np.asarray(x)

    def from_value(V):
        return (np.asarray(V) - lo) / R

    def f_box(x):
        V = to_value(x)
        TV = bellman(m, V, gamma_c)
        return np.clip(from_value(TV), 0.0, 1.0)
    return f_box, to_value, from_value


def policy_from_value(m, V, gamma=1.0):
    """The policy INDUCED by a value vector V (our FW-center query point, mapped
    back to value scale via to_value): the one-step greedy (most-appealing) action
    at every controller state.  This is how the FW-center bp becomes a policy that
    the certificate then tests.  (Read-off is by argmax appeal -- the white-box
    action, strictly more informative than the residual cut sign.)"""
    return greedy_policy(m, V, gamma)


# ============================================================================
# 5. FW-CENTER DRIVER WITH THE CERTIFICATE  (rounds-to-stabilize)
# ============================================================================
def run_certified(m, gamma_c=None, R=None, rng=None, center="exact",
                  gamma_cert=1.0, tol=1e-6, nsamp=40, verbose=False):
    """Drive the value-space cutting method on f_box, reading a policy off the
    FW-center each round and CERTIFYING it (sampler-free) at gamma_cert.  Stops at
    the first round whose read-off policy is Bellman-optimal.  Returns
    dict(rounds, certified, sigma, hist).  `rounds` is THE metric to compare with
    howard_pi's >= 2^n.

    center:
      "exact"  -- exact-rejection uniform samples of X_t (small n; removes the
                  sampler confound, as team lead requested), then FW LP.  Requires
                  common.py.
      callable(cuts, d, f, prev, rng) -> center point, for a light estimator.

    gamma_c defaults to a HARD-REGIME discount 1 - 2^{-(n+6)} so the discounted
    optimum's greedy policy matches the total-reward (gamma=1) optimum that the
    certificate checks.  float64 caps this near n ~ 30 (values ~2^n, delta ~2^-n).
    """
    if rng is None:
        rng = np.random.default_rng(0)
    if gamma_c is None:
        gamma_c = 1.0 - 2.0 ** (-(m.n + 6))
    if R is None:
        R = 8 * m.d + 50
    d = m.d
    f_box, to_value, _ = make_box_operator(m, gamma_c)

    def exact_center(cuts, dd, f, prev, rng):
        if hitrun is None:
            raise RuntimeError("center='exact' needs common.py (experiments venv)")
        if not cuts:
            return np.full(dd, 0.5)
        S = _exact_reject(cuts, dd, nsamp, rng)
        return balanced(S, dd) if S is not None and len(S) else prev

    cen = exact_center if center == "exact" else center
    cuts = []
    prev = np.full(d, 0.5)
    hist = []
    for t in range(R):
        bp = cen(cuts, d, f_box, prev, rng)
        V = to_value(bp)
        sigma = policy_from_value(m, V, gamma_cert)
        opt, _ = certify(m, sigma, gamma_cert, tol)
        resid = float(np.max(np.abs(f_box(bp) - bp)))
        hist.append(dict(t=t, opt=bool(opt), resid=resid))
        if verbose:
            print(f"  r{t:4d} certified_optimal={opt} ||f(bp)-bp||={resid:.2e}",
                  flush=True)
        if opt:
            return dict(rounds=t + 1, certified=True, sigma=sigma, hist=hist)
        c_, s_, _ = make_cut(f_box, bp)
        cuts.append((c_, s_))
        prev = bp
    return dict(rounds=R, certified=False, sigma=None, hist=hist)


def _exact_reject(cuts, d, nsamp, rng, batch=50000, cap=3_000_000):
    """Exact-rejection uniform samples of X_t = box ∩ ⋂ K(c,s) (small n)."""
    from common import in_X
    out = []
    drawn = 0
    while len(out) < nsamp and drawn < cap:
        P = rng.random((batch, d))
        ok = in_X(P, cuts)
        for row in P[ok]:
            out.append(row)
            if len(out) >= nsamp:
                break
        drawn += batch
    return np.array(out) if out else None


# ============================================================================
# 6. SELF-TEST  (cheap; validates the encoding is genuinely Howard-hard)
# ============================================================================
def _selftest(nmax=4):
    """For n = 1..nmax: run Howard PI from pi^emptyset_0 at gamma=1; assert the
    iteration count is >= 2^n and (n>=2) roughly doubles; assert the terminal
    policy is Bellman-optimal (certificate).  Prints a table."""
    print(f"{'n':>2} {'states':>7} {'howard_iters':>13} {'>=2^n':>7} {'opt':>4}")
    prev = None
    for n in range(1, nmax + 1):
        m = build_fearnley(n)
        k, sigma, V = howard_pi(m, gamma=1.0)
        opt = is_optimal(m, sigma, V, gamma=1.0, tol=1e-6)
        assert k >= 2 ** n, f"n={n}: Howard did {k} iters, expected >= {2**n}"
        assert opt, f"n={n}: Howard terminal policy not Bellman-optimal"
        if prev is not None and n >= 3:
            assert k > prev, f"n={n}: iters not increasing ({prev}->{k})"
        print(f"{n:>2} {m.d:>7} {k:>13} {2**n:>7} {'PASS':>4}")
        prev = k
    print("selftest PASS")


if __name__ == "__main__":
    _selftest(4)
