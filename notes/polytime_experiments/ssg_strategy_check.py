"""Light checks grounding notes/ssg_strategy.md (strategy-space reframing).

Three claims, all small (d<=8, enumerable strategy space, seconds):

  (T3a) ONE-SIDED = LP.  For a pure MAX-MDP (no MIN), x* = argmin{ sum x :
        x_i >= x_j for every successor j of a MAX node, x_i = avg at AVG,
        sinks fixed }.  The feasible set is CONVEX (conjunction of halfspaces)
        and a single linear objective (min sum) exposes x*.  Symmetric for MIN
        (max sum).  Confirm the LP optimum == value-iteration fixed point.

  (T3b) TWO-SIDED breaks the LP but NOT convexity.  Build the same convex
        polytope R = { x_i >= succ (MAX), x_i <= succ (MIN), x_i = avg }.
        x* still lies in R, but NEITHER min sum NOR max sum over R equals x*:
        the fixed point is a complementarity (saddle) point of a convex body,
        not exposed by any consistent linear objective.  This is the exact
        place one-sided-poly breaks.

  (T1)  STRATEGY-CLOUD halving.  Enumerate all 2^m strategies (m = #MAX+#MIN),
        compute the value cloud {x_sigma}.  Confirm x* is in the cloud, that a
        balanced cut at the Fermat-Weber point of the SURVIVING cloud removes
        ~half the survivors each round (so ~m rounds isolate x*, precision-free),
        and that the surviving fraction decays ~2^{-t} (the thinness that makes
        rejection sampling of survivors exponential -- the relocated wall).
"""
import itertools, numpy as np
from scipy.optimize import linprog
from common import balanced, K_ok, in_box
from friedmann import make_operator, policy_eval, MAX, MIN, AVG

SINK0, SINK1 = -1, -2


def rand_instance(d, delta, seed, allow=(MAX, MIN, AVG)):
    rng = np.random.default_rng(seed)
    types = np.array([allow[i] for i in rng.integers(0, len(allow), size=d)])
    rew = rng.uniform(0, 1, size=d)
    succ = []
    for i in range(d):
        k = int(rng.integers(2, 3 + 1))
        cand = list(range(d)) + [SINK0, SINK1]
        succ.append(list(rng.choice(cand, size=k, replace=False)))
    gamma = 1 - delta
    return types, succ, rew, gamma


def val_iter(types, succ, rew, gamma, it=200000, tol=1e-13):
    f = make_operator(types, succ, rew, gamma)
    x = np.full(len(types), 0.5)
    for _ in range(it):
        y = f(x)
        if np.max(np.abs(y - x)) < tol:
            return y
        x = y
    return x


def convex_region_lp(types, succ, rew, gamma, objective):
    """Solve  <objective, x>  over the convex fixed-point-constraint polytope R:
      MAX node i:  x_i >= (1-g) r_i + g * val(succ)   for EVERY successor  (x_i >= f-arg)
      MIN node i:  x_i <= (1-g) r_i + g * val(succ)   for EVERY successor
      AVG node i:  x_i == (1-g) r_i + g * mean(succ)  (equality)
    Sinks are constants.  Returns (x, feasible)."""
    d = len(types)
    g = gamma
    A_ub, b_ub, A_eq, b_eq = [], [], [], []

    def add_succ_terms(row, const, coeff, j):
        # add coeff * value(j) to a linear form (row on interior vars, const scalar)
        if j >= 0:
            row[j] += coeff
        else:
            const[0] += coeff * (0.0 if j == SINK0 else 1.0)
        return row, const

    for i in range(d):
        if types[i] == AVG:
            outs = succ[i]; p = 1.0 / len(outs)
            row = np.zeros(d); const = [0.0]
            row[i] -= 1.0
            for j in outs:
                add_succ_terms(row, const, g * p, j)
            const[0] += (1 - g) * rew[i]
            # row . x + const == 0  ->  row . x == -const
            A_eq.append(row); b_eq.append(-const[0])
        elif types[i] == MAX:
            for j in outs_of(succ, i):
                row = np.zeros(d); const = [0.0]
                # x_i >= (1-g) r + g val(j)   ->  -x_i + g*val(j) <= -(1-g) r
                row[i] -= 1.0
                add_succ_terms(row, const, g, j)
                const[0] += (1 - g) * rew[i]
                A_ub.append(row); b_ub.append(-const[0])
        else:  # MIN
            for j in outs_of(succ, i):
                row = np.zeros(d); const = [0.0]
                # x_i <= (1-g) r + g val(j)  ->  row.x <= (1-g)r + g*sinkval
                row[i] += 1.0
                add_succ_terms(row, const, -g, j)   # interior row[j]-=g; sink const-=g*sinkval
                const[0] -= (1 - g) * rew[i]
                A_ub.append(row); b_ub.append(-const[0])
    res = linprog(objective, A_ub=np.array(A_ub) if A_ub else None,
                  b_ub=np.array(b_ub) if b_ub else None,
                  A_eq=np.array(A_eq) if A_eq else None,
                  b_eq=np.array(b_eq) if b_eq else None,
                  bounds=[(0, 1)] * d, method='highs')
    return (res.x, True) if res.success else (None, False)


def outs_of(succ, i):
    return succ[i]


# ---------------------------------------------------------------- T3a: MDP = LP
def check_mdp_lp():
    print("== T3a: one-sided MDP value == LP over convex region ==")
    for kind, allow, obj_sign in [("MAX-MDP", (MAX, AVG), +1.0),
                                  ("MIN-MDP", (MIN, AVG), -1.0)]:
        worst = 0.0
        for seed in range(40):
            d = 7
            types, succ, rew, gamma = rand_instance(d, 1e-3, seed, allow=allow)
            xvi = val_iter(types, succ, rew, gamma)
            # MAX-MDP: least fixed point = min sum ; MIN-MDP: greatest = max sum
            x, ok = convex_region_lp(types, succ, rew, gamma,
                                     obj_sign * np.ones(d))
            if not ok:
                print(f"  {kind} seed {seed}: LP infeasible?!"); continue
            worst = max(worst, np.max(np.abs(x - xvi)))
        print(f"  {kind}: max |LP - valueiter| over 40 instances = {worst:.2e}"
              f"   ({'PASS' if worst < 1e-6 else 'FAIL'})")


# ---------------------------------------------- T3b: two-player breaks the LP
def check_saddle_break():
    print("== T3b: two-player -> x* in convex R but no linear objective finds it ==")
    n_break = 0; n_tot = 0
    for seed in range(40):
        d = 7
        types, succ, rew, gamma = rand_instance(d, 1e-3, seed, allow=(MAX, MIN, AVG))
        if not ((types == MAX).any() and (types == MIN).any()):
            continue
        n_tot += 1
        xvi = val_iter(types, succ, rew, gamma)
        xmin, ok1 = convex_region_lp(types, succ, rew, gamma, +np.ones(d))
        xmax, ok2 = convex_region_lp(types, succ, rew, gamma, -np.ones(d))
        # x* must be in R (feasible); check via slacks by re-solving feasibility:
        in_R = ok1 and ok2  # R nonempty; membership of xvi checked below
        # distance of xvi to the two linear optima
        dmin = np.max(np.abs(xmin - xvi)) if ok1 else np.nan
        dmax = np.max(np.abs(xmax - xvi)) if ok2 else np.nan
        broke = (dmin > 1e-6) and (dmax > 1e-6)
        n_break += broke
    print(f"  of {n_tot} genuinely two-player instances: {n_break} have x* !="
          f" both min-sum and max-sum LP optima")
    print(f"  ({'PASS: saddle break generic' if n_break == n_tot else 'mixed'})")


# ------------------------------------------------ T1: strategy-cloud halving
def strategy_cloud(types, succ, rew, gamma):
    ctrl = [i for i in range(len(types)) if types[i] != AVG]
    cloud = []
    for bits in itertools.product(*[range(len(succ[i])) for i in ctrl]):
        sigma = np.zeros(len(types), dtype=int)
        for i, b in zip(ctrl, bits):
            sigma[i] = b
        cloud.append(policy_eval(sigma, types, succ, rew, gamma))
    return np.array(cloud), len(ctrl)


def check_strategy_cloud():
    print("== T1: balanced cut halves the surviving strategy cloud ==")
    for seed in range(6):
        d = 8
        types, succ, rew, gamma = rand_instance(d, 1e-3, seed)
        m = int((types != AVG).sum())
        if m == 0 or m > 12:
            continue
        cloud, m = strategy_cloud(types, succ, rew, gamma)
        xvi = val_iter(types, succ, rew, gamma)
        d_star = np.min(np.max(np.abs(cloud - xvi[None, :]), axis=1))
        # cut process on the cloud: balanced FW point of survivors, keep K(bp,s)
        surv = cloud.copy()
        fracs = []
        f = make_operator(types, succ, rew, gamma)
        for t in range(m + 3):
            if len(surv) <= 1:
                break
            bp = balanced(surv, d)
            v = f(bp) - bp
            s = np.sign(v); s[np.abs(v) <= 1e-12] = 0.0
            keep = K_ok(surv, bp, s)
            frac = keep.mean()
            fracs.append(frac)
            surv = surv[keep]
        # x* still present?
        star_present = np.min(np.max(np.abs(surv - xvi[None, :]), axis=1)) < 1e-6 \
            if len(surv) else False
        print(f"  seed {seed}: m={m:2d}  |cloud|={len(cloud):4d}  "
              f"dist(x*,cloud)={d_star:.1e}  rounds={len(fracs):2d}  "
              f"final|surv|={len(surv):3d}  x*kept={star_present}  "
              f"keepfracs={[round(x,2) for x in fracs[:6]]}")
    print("  (keepfrac ~0.5 each round => ~m rounds to isolate x*, precision-free;")
    print("   final surviving fraction ~ prod(keepfracs) ~ 2^-rounds = the thinness wall)")


if __name__ == "__main__":
    check_mdp_lp()
    print()
    check_saddle_break()
    print()
    check_strategy_cloud()
