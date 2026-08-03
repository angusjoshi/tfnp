"""friedmann.py -- exponential-lower-bound SSG/MDP instances for policy iteration,
plus a SAMPLER-FREE optimality CERTIFICATE and a white-box policy read-off.

PURPOSE (Idea D).  Test whether the value-space FW-center cutting method (our
`common.run_algo`) escapes the exponential lower bounds that defeat *strategy-
space* policy iteration.  Concretely: on an instance family where standard policy
iteration provably takes 2^Theta(n) improvements, does the policy *read off our
FW-center query point* become BELLMAN-OPTIMAL after only poly(n) cutting rounds?
The certificate below decides optimality with one linear solve + a Bellman check
-- no near-uniform sampler and no isoperimetry -- so `lambdamin` can push n large.
The metric is ROUNDS-TO-STABILIZE (first round at which the read-off policy
certifies optimal), NOT sample quality; the certificate tolerates crude centers.

WHICH FAMILY IS ENCODED, AND WHY (correctness matters -- a wrong encoding voids
the experiment).  We implement the **Melekopoglou-Condon (1994)** family:
    M. Melekopoglou and A. Condon, "On the Complexity of the Policy Improvement
    Algorithm for Markov Decision Processes", ORSA J. on Computing 6(2):188-192,
    1994.  (UW-Madison CS TR; verified here against the paper's own value
    recurrences, Def. 2.1 / Lemmas 2.1-2.2 / Thm 2.8 / Cor. 2.9-2.10.)
It is a turn-based MIN + AVG Markov decision process with two sinks; the cost of a
policy is the probability of reaching the 1-sink (Condon's SSG value convention,
"The Complexity of Stochastic Games", Inf.&Comp. 1992).  On the basic graph G_n:
    * the SIMPLE PI rule (switch the highest-numbered switchable MIN vertex) and
      the TOPOLOGICAL rule take 2^n - 1 switches from the all-0 policy (Cor. 2.10,
      2.9); with the difference-gadgets added, the DIFFERENCE rule does too
      (Thm 2.8).
Why this family rather than Friedmann/Fearnley: it is the *cleanest exactly-
encodable* policy-iteration lower bound, and it defeats exactly the deterministic
"pick one switchable vertex by a local score" rules -- the closest strategy-space
analogue of reading a policy off a single geometric center.  The modern
strengthenings, which also defeat the switch-ALL (Howard) and optimal rules, are:
    O. Friedmann, "An Exponential Lower Bound for the Latest Deterministic
      Strategy Iteration Algorithms" / "Exponential Lower Bounds for Policy
      Iteration", ICALP 2009/2010 (parity, mean-payoff, discounted, and SSG);
    J. Fearnley, "Exponential Lower Bounds for Policy Iteration", ICALP 2010 (MDPs,
      Howard's rule).
Encoding one of those faithfully is far more error-prone (priority/cycle-gate
gadgets), so we take the MC family as the validated adversary and CITE Friedmann/
Fearnley as the harder follow-ups.  IMPORTANT: the hardness of every instance here
is *self-certifying* -- `simple_pi()` below measures the actual switch count, so
lambdamin can confirm 2^n-1 before trusting the comparison (see `_selftest`).

WHY THE HARD REGIME NEEDS gamma -> 1.  For a FIXED discount, Howard's PI is
strongly polynomial (Ye 2011, Math. OR), so any exponential family must live at
gamma = 1 - 2^{-poly}; this is exactly the SSG-reduction regime (`notes/polytime.md`
Sec.0).  We therefore build with gamma = 1 - delta, delta = 2^{-k} small.  Small
delta preserves the MC switching dynamics (values are continuous in delta and the
strict switchability inequalities survive); the discount only guarantees f is a
genuine ell_inf-contraction with a unique fixed point, as our machinery requires.

Representation is byte-compatible with common.py `make_ssg_full`:
    types[i] in {0:MAX, 1:MIN, 2:AVG};  succ[i] = list of successor indices, where
    j>=0 is interior vertex j, j==-1 is the 0-sink (value 0), j==-2 the 1-sink
    (value 1);  rew[i] in [0,1];  gamma = 1 - delta.  The value operator is
    f(x)_i = clip((1-gamma)*rew[i] + gamma*op_i(successor values), 0, 1),
    op = max/min/mean for MAX/MIN/AVG -- identical to common.make_ssg.
"""
import numpy as np

try:
    from common import balanced, hitrun, make_cut, in_X, fixed_point
except Exception:                              # allow import without common.py present
    balanced = hitrun = make_cut = in_X = fixed_point = None

SINK0, SINK1 = -1, -2                           # value 0, value 1  (as in common.py)
MAX, MIN, AVG = 0, 1, 2


# ============================================================================
# 1. INSTANCE GENERATORS  (Melekopoglou-Condon 1994)
# ============================================================================
def mc_basic(n, delta=2.0 ** -20):
    """Basic graph G_n of Melekopoglou-Condon, Fig. 2.1 (NO gadgets).

    MIN vertices 1..n and AVG vertices 0'..n' (n+1 of them), two sinks; a
    minimizing MDP whose value = discounted prob. of reaching the 1-sink.
    Layout (d = 2n+1):  MIN k -> index k-1 (k=1..n);  AVG k' -> index n+k (k=0..n).

    Edges (decision 0 listed first so the "all-0 policy" = succ index 0 everywhere,
    matching MC's initial 0-vector):
      MIN 1 : [0'(=avg 0), 1'(=avg 1)]                 # S=0 -> 0',  S=1 -> 1'
      MIN k>=2 : [MIN(k-1), AVG k']                    # S=0 -> k-1, S=1 -> k'
      AVG 0': avg(1-sink, MIN n)        -> V(0') = 1/2 (1 + V(n))          [Fig 2.1]
      AVG 1': avg(0-sink, 1-sink)       -> V(1') = 1/2  (constant)         [forced by
                                            Lemma 2.2: V(1')=V(0')+V(n)a(1), a(1)=-1/2]
      AVG 2': avg(1', 0')               -> V(2') = 1/2 (V(1')+V(0'))
      AVG k'>=3: avg((k-1)', MIN(k-2))  -> reproduces Def. 2.1's a(k)=(1/2 - S_{k-1})
                                            a(k-1) recurrence (verified algebraically).

    The all-0 policy has cost 1 at every MIN vertex; the optimum is S=0...01 with
    cost 1/2; simple/topological PI take 2^n - 1 switches to get there (Cor. 2.9/2.10).

    Returns (types, succ, rew, gamma, meta) with meta describing the vertex indexing
    and the analytically-known optimal policy (for cross-checks).
    """
    assert n >= 1 and 0.0 < delta < 1.0
    d = 2 * n + 1
    mn = lambda k: k - 1                         # MIN k  (1<=k<=n)  -> index
    av = lambda k: n + k                         # AVG k' (0<=k<=n)  -> index
    types = np.empty(d, dtype=int)
    succ = [None] * d
    for k in range(1, n + 1):
        types[mn(k)] = MIN
    for k in range(0, n + 1):
        types[av(k)] = AVG
    # MIN vertices
    succ[mn(1)] = [av(0), av(1)]                 # S=0 -> 0', S=1 -> 1'
    for k in range(2, n + 1):
        succ[mn(k)] = [mn(k - 1), av(k)]         # S=0 -> MIN(k-1), S=1 -> AVG k'
    # AVG vertices
    succ[av(0)] = [SINK1, mn(n)]                 # avg(1-sink, MIN n)
    succ[av(1)] = [SINK0, SINK1]                 # avg(0-sink, 1-sink) == 1/2
    if n >= 2:
        succ[av(2)] = [av(1), av(0)]             # avg(1', 0')
    for k in range(3, n + 1):
        succ[av(k)] = [av(k - 1), mn(k - 2)]     # avg((k-1)', MIN(k-2))
    rew = np.zeros(d)
    gamma = 1.0 - delta
    # analytic optimum: S_k = 0 for k>=2, S_1 = 1  (edge to 1' at vertex 1)
    opt_sigma = np.zeros(d, dtype=int)
    opt_sigma[mn(1)] = 1
    meta = dict(kind="mc_basic", n=n, d=d, delta=delta,
                min_idx=[mn(k) for k in range(1, n + 1)],
                avg_idx=[av(k) for k in range(0, n + 1)],
                opt_sigma=opt_sigma, exp_simple_switches=2 ** n - 1,
                init_sigma=np.zeros(d, dtype=int))
    return types, succ, rew, gamma, meta


def mc_gadget_graph(n, delta=2.0 ** -20):
    """Full G_n = basic graph + the difference-defeating gadgets g_{2(n-k)}
    (MC Fig. 2.2), placed on BOTH out-edges of each MIN vertex k (1<k<n) and on
    the (1,1') edge.  Gadget g_L between MIN j and target m: L AVG vertices
    g1..gL with g_i = avg(MIN j, g_{i-1})  and  g_1 = avg(MIN j, m); the edge
    (j -> m) is rerouted to (j -> gL).  Property (MC p.5): a policy using (j,gL)
    gives V(j)=V(m), and otherwise the child-cost difference at j is <= 2^{-L},
    so the DIFFERENCE / TOPOLOGICAL rules are forced to behave like SIMPLE.

    NOTE ON CONFIDENCE: the basic graph already makes SIMPLE and TOPOLOGICAL PI
    exponential (Cor. 2.9/2.10) -- that is the *validated* adversary for the
    FW-center experiment.  The gadgets matter only for the DIFFERENCE and
    BEST-DECREASE rules.  This builder follows Fig. 2.2 as faithfully as the text
    allows, but its exponential-ness for those rules should be CONFIRMED by a
    difference-PI baseline before use; for the headline experiment, prefer
    `mc_basic` + `simple_pi` (both proven and self-checked in `_selftest`).

    Returns (types, succ, rew, gamma, meta).  Kept structurally parallel to
    mc_basic so `certify`, `policy_from_point`, `simple_pi` all work unchanged.
    """
    assert n >= 2 and 0.0 < delta < 1.0
    # Start from the basic graph, then splice gadgets onto MIN out-edges.
    types_b, succ_b, rew_b, gamma, meta_b = mc_basic(n, delta)
    types = list(types_b)
    succ = [list(s) for s in succ_b]
    rew = list(rew_b)
    mn = lambda k: k - 1
    av = lambda k: n + k

    def add_avg(children):
        idx = len(types)
        types.append(AVG); succ.append(list(children)); rew.append(0.0)
        return idx

    def gadget(j_idx, m_target, L):
        """Insert g_L between MIN j_idx and target m_target; return top index gL."""
        prev = m_target                          # g_1 -> m
        top = None
        for _ in range(L):
            g = add_avg([j_idx, prev])           # g_i = avg(MIN j, g_{i-1}/m)
            prev = g
            top = g
        return top                                # gL

    # Reroute each MIN vertex's two decisions through gadgets (MC: g_{2(n-k)}).
    for k in range(2, n):                         # 1 < k < n : both edges gadgeted
        L = 2 * (n - k)
        if L >= 1:
            s0, s1 = succ[mn(k)]
            succ[mn(k)][0] = gadget(mn(k), s0, L)
            succ[mn(k)][1] = gadget(mn(k), s1, L)
    # vertex 1: gadget g_{2(n-1)} on the (1,1') edge (MC: "vertex 1 switched once")
    L1 = 2 * (n - 1)
    if L1 >= 1:
        s0, s1 = succ[mn(1)]
        succ[mn(1)][1] = gadget(mn(1), s1, L1)

    d = len(types)
    types = np.array(types, dtype=int)
    rew = np.array(rew, dtype=float)
    opt = np.zeros(d, dtype=int); opt[mn(1)] = 1
    meta = dict(kind="mc_gadget", n=n, d=d, delta=delta,
                min_idx=[mn(k) for k in range(1, n + 1)],
                exp_simple_switches=2 ** n - 1,
                init_sigma=np.zeros(d, dtype=int),
                note="gadget wiring; validate difference-PI hardness before trusting")
    return types, succ, rew, gamma, meta


def make_operator(types, succ, rew, gamma):
    """Return f: R^d -> R^d, the EXACT common.py value operator for this instance.
    (Byte-identical semantics to common.make_ssg's inner f, so `common.run_algo`,
    `common.fixed_point`, etc. accept it directly.)"""
    d = len(types)
    rew = np.asarray(rew, dtype=float)

    def val(x, j):
        return x[j] if j >= 0 else (0.0 if j == SINK0 else 1.0)

    def f(x):
        out = np.empty(d)
        for i in range(d):
            vs = np.array([val(x, j) for j in succ[i]])
            t = types[i]
            op = vs.max() if t == MAX else vs.min() if t == MIN else vs.mean()
            out[i] = min(1.0, max(0.0, (1.0 - gamma) * rew[i] + gamma * op))
        return out
    return f


# ============================================================================
# 2. CERTIFICATE LAYER  (sampler-free: one linear solve + Bellman check)
# ============================================================================
def _sink_val(j):
    return 0.0 if j == SINK0 else 1.0


def policy_eval(sigma, types, succ, rew, gamma):
    """Exact value x_sigma of policy sigma by solving (I - gamma P_sigma) x
    = (1-gamma) rew + gamma c_sigma  (rew folded in; c = one-step sink mass).

    sigma[i] in {0,1,...}: for MAX/MIN vertices, the index INTO succ[i] that is
    chosen; ignored for AVG vertices (which split 1/|succ| over their successors).
    Returns x_sigma in R^d (values on interior vertices; sinks are constants)."""
    d = len(types)
    rew = np.asarray(rew, dtype=float)
    P = np.zeros((d, d))
    c = np.zeros(d)                              # immediate sink contribution
    for i in range(d):
        if types[i] == AVG:
            outs = succ[i]; p = 1.0 / len(outs)
            for j in outs:
                if j >= 0:
                    P[i, j] += p
                else:
                    c[i] += p * _sink_val(j)
        else:                                    # controlled MAX/MIN vertex
            j = succ[i][int(sigma[i])]
            if j >= 0:
                P[i, j] += 1.0
            else:
                c[i] += _sink_val(j)
    A = np.eye(d) - gamma * P
    b = (1.0 - gamma) * rew + gamma * c
    return np.linalg.solve(A, b)


def greedy_actions(x, types, succ):
    """greedy[i] = optimal succ-index at vertex i given values x (argmin for MIN,
    argmax for MAX; -1 for AVG)."""
    def val(j):
        return x[j] if j >= 0 else _sink_val(j)
    greedy = np.full(len(types), -1, dtype=int)
    for i in range(len(types)):
        if types[i] == AVG:
            continue
        vs = np.array([val(j) for j in succ[i]])
        greedy[i] = int(np.argmin(vs)) if types[i] == MIN else int(np.argmax(vs))
    return greedy


def is_bellman_optimal(sigma, x, types, succ, tol=1e-9):
    """True iff sigma is greedy w.r.t. its own values x (no improving deviation
    at any controlled vertex, within tol on the achieved value)."""
    def val(j):
        return x[j] if j >= 0 else _sink_val(j)
    for i in range(len(types)):
        if types[i] == AVG:
            continue
        vs = np.array([val(j) for j in succ[i]])
        best = vs.min() if types[i] == MIN else vs.max()
        chosen = val(succ[i][int(sigma[i])])
        if abs(chosen - best) > tol:
            return False
    return True


def certify(sigma, types, succ, rew, gamma, tol=1e-9):
    """Sampler-free optimality certificate for a candidate policy sigma.
    Returns (is_optimal, x_sigma):
      x_sigma = policy_eval(sigma)                       (one linear solve)
      is_optimal = no improving one-step deviation       (Bellman check).
    When is_optimal, x_sigma equals the game value/fixed point x* (up to tol)."""
    x = policy_eval(sigma, types, succ, rew, gamma)
    return is_bellman_optimal(sigma, x, types, succ, tol), x


# ============================================================================
# 3. POLICY READ-OFF FROM A VALUE POINT  (white-box, greedy)
# ============================================================================
def policy_from_point(x, types, succ):
    """The policy INDUCED by a value point x (our FW-center query point bp): at
    each controlled vertex take the successor that looks best AT x -- argmin over
    successor values for MIN, argmax for MAX.  AVG vertices get sigma[i]=0 (unused).

    HOW THE FW-CENTER MAPS TO A POLICY.  `common.run_algo` queries f at the
    Fermat-Weber balanced center bp of X_t and forms a ternary cut from
    sign(f(bp)-bp).  That residual sign only tells you the coordinate is moving
    up/down; the WHITE-BOX read-off here is strictly more informative -- it uses
    the game structure (succ, types) to name the actual greedy action at bp, i.e.
    the one-step-greedy policy w.r.t. the value estimate bp.  This is the policy
    whose optimality we then certify; ROUNDS-TO-STABILIZE = first t with
    certify(policy_from_point(bp_t)) optimal.  (For a sanity cross-check, the
    ternary cut sign at a MIN/MAX vertex i agrees with the greedy switch direction
    once bp is close enough to x*, cf. Lemma 1 of notes/hitrun.md.)"""
    def val(j):
        return x[j] if j >= 0 else _sink_val(j)
    sigma = np.zeros(len(types), dtype=int)
    for i in range(len(types)):
        if types[i] == AVG:
            continue
        vs = np.array([val(j) for j in succ[i]])
        sigma[i] = int(np.argmin(vs)) if types[i] == MIN else int(np.argmax(vs))
    return sigma


# ============================================================================
# 4. STANDARD POLICY-ITERATION BASELINES  (ground-truth hardness)
# ============================================================================
def simple_pi(types, succ, rew, gamma, sigma0=None, max_iters=None):
    """Melekopoglou-Condon SIMPLE policy improvement: each iteration switch the
    single switchable MIN/MAX vertex with the LARGEST index.  Returns
    (n_switches, sigma_final, x_final).  On mc_basic(n) from the all-0 policy this
    returns exactly 2^n - 1 (Cor. 2.10) -- this call is the self-certification that
    the instance really is hard for strategy iteration."""
    d = len(types)
    sigma = np.zeros(d, dtype=int) if sigma0 is None else np.array(sigma0, dtype=int)
    if max_iters is None:
        max_iters = 4 * (2 ** min(d, 30))
    def val(x, j):
        return x[j] if j >= 0 else _sink_val(j)
    k = 0
    while k < max_iters:
        x = policy_eval(sigma, types, succ, rew, gamma)
        best_i = -1
        for i in range(d):                        # largest index first
            if types[i] == AVG:
                continue
            vs = np.array([val(x, j) for j in succ[i]])
            g = int(np.argmin(vs)) if types[i] == MIN else int(np.argmax(vs))
            if g != int(sigma[i]) and abs(val(x, succ[i][g]) - val(x, succ[i][int(sigma[i])])) > 1e-12:
                best_i = i                         # keep last (=largest index)
        if best_i < 0:
            return k, sigma, x
        vs = np.array([val(x, j) for j in succ[best_i]])
        sigma[best_i] = int(np.argmin(vs)) if types[best_i] == MIN else int(np.argmax(vs))
        k += 1
    return k, sigma, policy_eval(sigma, types, succ, rew, gamma)


def howard_pi(types, succ, rew, gamma, sigma0=None, max_iters=10_000):
    """Switch-ALL (Howard) policy iteration: switch every improvable vertex to its
    greedy action each iteration.  Returns (n_iters, sigma, x).  Included for
    comparison -- MC's basic graph is NOT hard for switch-all; Friedmann 2009 /
    Fearnley 2010 are needed to defeat this rule (see module docstring)."""
    d = len(types)
    sigma = np.zeros(d, dtype=int) if sigma0 is None else np.array(sigma0, dtype=int)
    for k in range(max_iters):
        x = policy_eval(sigma, types, succ, rew, gamma)
        greedy = greedy_actions(x, types, succ)
        new = sigma.copy()
        for i in range(d):
            if types[i] != AVG:
                new[i] = greedy[i]
        if is_bellman_optimal(sigma, x, types, succ):
            return k, sigma, x
        sigma = new
    return max_iters, sigma, policy_eval(sigma, types, succ, rew, gamma)


# ============================================================================
# 5. FW-CENTER DRIVER WITH THE CERTIFICATE  (light center; rounds-to-stabilize)
# ============================================================================
def cheap_center(cuts, d, f, prev, rng, nsamp=16, thin=8, burn=200):
    """LIGHT FW-center estimate for large n: a short, low-budget hit-and-run on
    X_t warm-started at `prev` (always in X_{t+1}), then the Fermat-Weber LP on
    the few samples.  Far cheaper than exact rejection; the certificate tolerates
    a crude center, so a handful of samples suffices to move the read-off policy.
    Even cruder surrogates are fine to try (see RECOMMENDATION below)."""
    if hitrun is None or balanced is None:
        raise RuntimeError("needs common.py (run under the experiments venv)")
    if not cuts:
        return np.full(d, 0.5)
    S = hitrun(cuts, d, prev, nsamp=nsamp, thin=thin, burn=burn, rng=rng)
    return balanced(S, d)


def run_certified(types, succ, rew, gamma, R, rng=None,
                  center=cheap_center, tol=1e-7, verbose=False):
    """Drive the value-space cutting method with the SAMPLER-FREE certificate as
    the stopping test.  Each round: estimate FW-center bp of X_t (light), read the
    greedy policy off bp, CERTIFY it.  Stop at the first round whose read-off
    policy is Bellman-optimal.  Returns dict(rounds, certified, sigma, xstar,
    hist).  `rounds` (rounds-to-stabilize) is THE metric to compare against
    simple_pi's 2^n-1 switch count.

    RECOMMENDATION (light center, so lambdamin can push n large without exponential
    rejection sampling):
      * Default `cheap_center` = short hit-and-run (nsamp~16) + FW LP.  The
        certificate only needs bp to induce the right greedy actions, not a
        well-mixed sample, so keep nsamp small and let it grow only if `rounds`
        plateaus without certifying.
      * Even lighter surrogates worth trying as `center=...`:
          - damped value-iterate: bp <- clip((bp + f(bp))/2) projected into X_t
            (a few steps), then read off -- no sampling at all;
          - Chebyshev center of the LP outer-approximation box of X_t;
          - the previous center reflected through the last apex (the cut's removed
            set is the point reflection of the kept set, notes/polytime.md 3.2).
        All are O(poly) per round; the certificate is the ground truth regardless.
      * Record BOTH the round index and cumulative f-queries; the claim of Idea D
        is poly(n) rounds where simple_pi needs 2^n-1.

    NUMERICAL CAVEAT.  On mc_basic(n) the smallest decision margin is ~V(n)/2^n ~
    2^{-(n+2)} (MC Cor. 2.3); set `tol` BELOW it (e.g. tol = 2^{-(n+4)}) or the
    Bellman check can false-certify a non-optimal policy.  float64 caps reliable
    runs near n ~ 40 regardless (2^{-42} ~ machine eps on values ~1); the FW-center
    method needs only poly rounds, so this bites simple_pi's baseline, not the
    experiment -- but keep delta from being so tiny that gamma-scaling pushes the
    margins under eps (delta ~ 2^{-20} with n <~ 30 is a safe window).
    """
    if rng is None:
        rng = np.random.default_rng(0)
    f = make_operator(types, succ, rew, gamma)
    d = len(types)
    cuts = []
    prev = np.full(d, 0.5)
    hist = []
    for t in range(R):
        bp = center(cuts, d, f, prev, rng)
        sigma = policy_from_point(bp, types, succ)
        opt, xhat = certify(sigma, types, succ, rew, gamma, tol=tol)
        hist.append(dict(t=t, opt=bool(opt),
                         resid=float(np.max(np.abs(f(bp) - bp)))))
        if verbose:
            print(f"  r{t:4d} certified_optimal={opt} "
                  f"||f(bp)-bp||={hist[-1]['resid']:.2e}", flush=True)
        if opt:
            return dict(rounds=t + 1, certified=True, sigma=sigma,
                        xstar=xhat, hist=hist)
        c_, s_, _ = make_cut(f, bp)
        cuts.append((c_, s_))
        prev = bp
    return dict(rounds=R, certified=False, sigma=None, xstar=None, hist=hist)


# ============================================================================
# 6. SELF-TEST  (cheap; lambdamin should run this before the real experiment)
# ============================================================================
def _selftest(nmax=6):
    """Verify the encoding on small n WITHOUT any sampling:
      (a) simple_pi from the all-0 policy takes exactly 2^n - 1 switches
          (Melekopoglou-Condon Cor. 2.10) -- confirms the instance is genuinely
          hard for strategy iteration;
      (b) the certified optimal policy's value == value-iteration fixed point
          (common.fixed_point) within tol -- confirms policy_eval / the operator;
      (c) the analytic optimum opt_sigma certifies optimal.
    Prints a table; raises AssertionError on any mismatch."""
    print(f"{'n':>2} {'d':>4} {'simple_pi':>10} {'2^n-1':>8} {'ok':>4} "
          f"{'||x_cert-x_vi||':>16}")
    for n in range(1, nmax + 1):
        types, succ, rew, gamma, meta = mc_basic(n, delta=2.0 ** -18)
        k, sigma, x = simple_pi(types, succ, rew, gamma)
        exp = 2 ** n - 1
        assert k == exp, f"n={n}: simple_pi did {k} switches, expected {exp}"
        opt, xc = certify(sigma, types, succ, rew, gamma, tol=1e-6)
        assert opt, f"n={n}: simple_pi terminal policy not certified optimal"
        assert certify(meta['opt_sigma'], types, succ, rew, gamma, tol=1e-6)[0], \
            f"n={n}: analytic opt_sigma not certified optimal"
        diff = float('nan')
        if fixed_point is not None:
            f = make_operator(types, succ, rew, gamma)
            xvi = fixed_point(f, len(types))
            diff = float(np.max(np.abs(xc - xvi)))
            assert diff < 1e-4, f"n={n}: certified value != value-iteration ({diff})"
        print(f"{n:>2} {len(types):>4} {k:>10} {exp:>8} {'PASS':>4} {diff:>16.2e}")
    print("selftest PASS")


if __name__ == "__main__":
    _selftest(6)
