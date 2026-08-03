# Attacking SSG through the value operator's structure (strategy space)

Mandate (from `main`): do NOT black-box `f` as an `ℓ∞`-contraction and reduce to
"sample the non-convex leftover body `X_t`" (that route is exhaustively mapped in
`FINAL_REPORT.md` / `core_analysis.md` and terminates on one wall). Instead use
the **real** structure of the SSG value operator — each `f_i(x)` is
`max(x_j,x_k)`, `min(x_j,x_k)`, `½(x_j+x_k)`, or a `0/1` sink — and either produce
a genuinely new reduction/algorithm that USES it, or report honestly that it does
not help and say precisely why. Anti-repackaging is the standing instruction.

**Bottom line, up front.**

- **Task 1 (strategy-space reframe): honest negative, with a precise reason and one
  genuinely-new structural bridge.** The candidate region *does* correspond to a set
  of surviving strategies, and the balanced point over a *given* finite set of
  strategy-values *is* an LP (no volume integral). But (a) the surviving set is
  exponential and cannot be enumerated; (b) approximating the balanced point needs a
  near-uniform **survivor sample**, whose fraction is exponentially small — the exact
  discrete mirror of `vol(X_t)=2^{-t}`, i.e. the **same** sampling wall; and (c) the
  discrete balanced cut does not even cleanly halve the strategy cloud — it **stalls**
  (verified). The *new* structural content is that the natural discrete sampler is a
  random walk on the strategy hypercube, so the project's isoperimetry wall and the
  classical **Friedmann/Fearnley** policy-iteration lower bounds are the **same wall**
  seen from two sides — which corrects the repo's recurring "value-space ⟹ immune to
  Friedmann" framing.

- **Task 2 (geometric-center pivot vs Friedmann): partial, sharply delimited.** The
  balanced-center rule is *provably* non-local and outside the Melekopoglou–Condon /
  Friedmann / Fearnley family — those bound **local improvement step counts**, and an
  unconditional volume-halving cut is not a local improvement step. So those bounds do
  **not** bound its **round count** (which is `poly` by volume-halving, for any
  contraction — not special to max/min/avg). But this is *not* a poly algorithm: the
  escape only relocates the cost into the per-round center computation = the survivor
  sampler of Task 1, whose discrete form re-meets Friedmann-type hardness. The
  max/min/avg structure does **not** provably make total work poly. This explains the
  earlier empirical negative on Melekopoglou–Condon (`idea_d_mc.md`).

- **Task 3 (where one-sided-poly breaks): concrete new reduction + a decisive
  anti-repackaging finding.** The exact break is **complementarity**: one-sided value
  `x*` is the optimum of a single **linear objective** over a **convex** polytope `R`
  (verified LP == value-iteration for both MAX- and MIN-MDPs); two-sided `x*` lies in
  the *same* convex `R` but is exposed by **no** linear objective — it is the LCP
  saddle point (verified on 34/34 mixed instances). This is exactly Jurdziński–Savani's
  P-matrix LCP. **The value-space pyramid geometry does NOT address this break — it
  discards it:** the black-box CLY cut has full support `Θ(d)` and is a *non-convex*
  pyramid-union **even on a pure MDP** that is LP-solvable (verified: support `8/8` at
  `d=8`). The operator's one-sided convexity — the very thing that makes MDPs easy — is
  invisible to the `ℓ∞`-contraction abstraction. Using the structure means working on
  the convex `R` and confronting P-LCP, not sampling a non-convex body.

Light checks backing every "verified" above: `polytime_experiments/ssg_strategy_check.py`
(seconds; `d≤8`, enumerable strategy space). Heavier experiments are flagged to `main`
in §5.

---

## 0. Setup and the one structural fact everything turns on

SSG graph, vertices `V`, `d=|V|`, each interior vertex a MAX / MIN / AVG node with
two successors; two sinks (values `0,1`); discount `γ=1−δ`, hard regime `δ=2^{−poly}`.
Value operator `f:[0,1]^d→[0,1]^d`, `f_i` = `max`/`min`/`avg` of successor values,
folded with reward and discount. `x*` = unique fixed point = game value.

A **(combined) strategy** `σ` fixes the choice at every MAX and MIN node
(`m := #MAX+#MIN` binary choices). Under `σ` the game is a Markov chain (AVG nodes
random): `f_σ(x)=M_σx+b_σ`, `M_σ` substochastic, so

> `x_σ = (I−M_σ)^{-1} b_σ`  is **exactly poly-computable** (one linear solve).

and `x* = x_{σ*}` for the optimal `σ*`. So `x*` is one of `≤2^m` poly-computable
**strategy-values**; the problem is **combinatorial** — find `σ*`. SSG ∈ NP∩coNP∩UP∩coUP
(Condon 1992; Jurdziński 1998): certify `σ` by solving `x_σ` and checking no controlled
node has a profitable one-step switch. All-MAX (or all-MIN) = an MDP = **poly by LP**
(§3). Hardness = mixing MAX **and** MIN.

The **value cloud** `𝒞 = {x_σ : σ∈{0,1}^m} ⊆ [0,1]^d` is the finite object the whole
note is about. Its minimum spacing along a controlled coordinate is the
**value-separation gap** `δ_gap` (`common.ssg_value_gap`): the smallest decision margin
between the best and second-best successor at any MAX/MIN node, at `x*`. In the hard
regime `δ_gap = 2^{−poly}`.

---

## 1. Task 1 — the balanced-point / candidate-region method in strategy space

### 1.1 The reframe (clean, and correct as far as it goes)

The value-space method maintains `X_t = [0,1]^d ∩ ⋂_{r≤t} K(c^r,s^r)`, `K` a union of
`ℓ∞` pyramids, and each cut provably retains `x*`. Intersect with the cloud:

> **surviving strategies** `S_t := 𝒞 ∩ X_t = { σ : x_σ ∈ ⋂_{r≤t} K(c^r,s^r) }`.

Because every cut retains `x*` and `x*∈𝒞`, we have `σ*∈S_t` for all `t`. So the
continuous body `X_t` is a **fattened proxy** for the finite set `S_t` that actually
matters. Two immediate consequences that look like progress:

1. **The balanced point of a *given* finite set is an LP, not a volume integral.**
   `polytime.md` §2.2 already proved this: for `T={y^1,…,y^N}`,
   `min_c Σ_j‖y^j−c‖_∞` is a linear program (`N+d` vars, `2dN` constraints;
   `common.balanced`). If `S_t` were in hand, its balanced point is one LP solve on
   `N=|S_t|` points — **no sampling of a continuous body**. This is exactly the
   "combinatorial step, not volume-sampling" the mandate asked about.

2. **A discrete target ⟹ the precision axis is bounded by `δ_gap`, not `ε`.** `x*` is
   an isolated cloud point; its nearest cloud neighbour is `≥ δ_gap` away. One never
   needs resolution finer than `δ_gap`: once the candidate region has diameter `<δ_gap`
   it contains a single strategy-value, which is read off and certified exactly
   (`friedmann.certify`). So `log(1/ε)` collapses to `log(1/δ_gap)`.

### 1.2 Why it does not dissolve the wall (three reasons, one verified)

**(a) `S_t` is exponential and the LP needs it explicitly.** To *write* the
Fermat–Weber LP you need the points of `S_t`; there are up to `2^m` of them. Computing
`μ(P_i^±(c)) = #{σ∈S_t : x_σ∈P_i^±(c)}` for a candidate apex is
**counting strategies whose (matrix-inverse) value lands in a pyramid** — a
`#P`-flavoured problem. (Even the *extreme* of the cloud in a coordinate is
`max_σ (x_σ)_i` = a best-response value ≈ the game value; counting is at least as hard.)
So the "it's just an LP" is an LP **only after** you have solved the enumeration/counting
problem, which is the hard part.

**(b) Approximating it needs a survivor sample, which is exponentially thin — the
same wall.** The value-space route already replaces exact balance by a balanced point
of `N=Õ(d²/α²)` **samples** (`polytime.md` Thm B). The discrete analogue is: draw
near-uniform **surviving strategies** `σ∼Unif(S_t)`, estimate pyramid counts, solve the
finite LP. But `|S_t|/2^m` shrinks toward `2^{−Θ(m)}` as the region isolates `σ*`, so
**rejection sampling** (draw `σ∈{0,1}^m` uniformly, accept iff `x_σ∈X_t`) has
exponentially small acceptance — the exact discrete mirror of `vol(X_t)=2^{−t}`. This is
the identical thinness barrier `core_analysis.md` §2 identified for the continuous body,
now on a finite point cloud. No gain.

**(c) The discrete balanced cut does not even cleanly halve the cloud — it stalls
(verified).** One might hope that a balanced cut removes a constant fraction of `S_t`,
isolating `σ*` in `O(m)` rounds. It does not. `ssg_strategy_check.py` (`check_strategy_cloud`,
`d=8`, full enumeration) computes the true FW balanced point of the surviving cloud each
round and applies the actual oracle cut. Measured keep-fractions:

```
seed0 m=7 |𝒞|=288  keepfracs=[.75,.67,.97,1.0,1.0,1.0]  final|surv|=140
seed2 m=6 |𝒞|=216  keepfracs=[.54,.58,.60,.73,1.0,1.0]  final|surv|= 30
seed5 m=5 |𝒞|= 72  keepfracs=[.68,.73,.75,.74,.55,.91]  final|surv|= 10
```

`x*` is always kept (correct), but the cut **stops removing strategies**
(`keepfrac→1`) long before isolating `σ*`. Reason: the volume-halving guarantee is a
statement about **Lebesgue measure** (`Thm A`: at the balanced point `μ(K(c,s))≥½` for
every `s`; complementation makes it `=½` *for the continuous body*). It does **not**
transfer to the **counting** measure on a clustered finite cloud, and once `bp` is a
near-fixed-point the residual `f(bp)−bp→0`, the ternary sign zeroes out, and the cut
becomes vacuous. So the discrete view offers no clean combinatorial halving; you are
back to shrinking *volume* to sub-`δ_gap` scale, i.e. `log(1/δ_gap)=poly` **rounds** —
the same round count as the continuous method, with the same per-round sampler.

### 1.3 The one genuinely-new thing: the discrete sampler IS a strategy-hypercube walk

This is the part worth keeping. A near-uniform sampler for `S_t` cannot be rejection
(thin, (b)); the standard alternative is **MCMC on `{0,1}^m`** with single-node policy
flips (Glauber / lazy random walk on the strategy hypercube), stationary distribution
`Unif(S_t)`. Its mixing time is the **conductance of `S_t` under flip moves**. But a
random walk on the strategy hypercube that prefers improving flips **is** policy
iteration; and Melekopoglou–Condon / Friedmann / Fearnley construct instances where the
improvement dynamics traverse an **exponentially long, poorly-connected** path through
the hypercube. So:

> **Bridge (new).** The continuous isoperimetry wall (`hit-and-run mixes on X_t?`) and
> the classical strategy-iteration lower bounds (Friedmann/Fearnley) are the **same
> obstruction** viewed in two coordinate systems: bad conductance of the surviving set,
> continuous (`X_t`) or discrete (`S_t⊆{0,1}^m`). The value-space cut geometry is the
> *continuous relaxation* of the strategy-hypercube walk.

This **qualifies** the repo's standing claim ("our method is value-space, so
Friedmann's strategy-space bounds do not apply", `ssg_directions.md` §0, §3;
`FINAL_REPORT.md` §5). That claim is correct **only for the round count** (§2 below).
For the **per-round sampler cost** — the actual open wall — the strategy-space hardness
is not evaded; it is the same object. This is the honest structural finding of Task 1,
and it is *not* repackaging: it is a new identification of two previously-separated walls.

**Verdict (Task 1): honest negative.** The reframe is real and removes the `ε`-precision
axis (already implicitly available), but it relocates the balanced-point computation to
survivor sampling, which is (i) exponentially thin under rejection = the same wall,
(ii) governed under MCMC by strategy-hypercube conductance = Friedmann's wall, and
(iii) not even a clean halving (stalls, verified). The structural fact needed to break
it: **a poly-time near-uniform sampler of `S_t` that is not a local-flip walk** — e.g.
one exploiting the rational structure `σ↦(I−M_σ)^{-1}b_σ` or a self-reducible counting
scheme. None is known, and it would be `SSG∈P`.

---

## 2. Task 2 — is the balanced-center pivot provably poly, or does Friedmann apply?

### 2.1 The rule is provably outside the Friedmann/Fearnley/MC family

Melekopoglou–Condon (1994), Friedmann (2009/2010) and Fearnley (2010) are lower bounds
on **local improvement rules**: maintain a current strategy `σ`, compute the set of
single-node switches that improve `x_σ`, pick one by a fixed pivot (simple/highest-index,
Bland, greatest-improvement, random-edge, random-facet, switch-all/Howard), repeat. The
constructions force the *improvement path* to have exponential (or `2^{Ω(√n)}`) length.

The balanced-center rule is structurally different: it does **not** maintain or switch a
strategy. It computes the Fermat–Weber center of the surviving candidate distribution,
queries `f` there, and cuts. The next query depends on the **global** geometry of the
candidate set, not on local switches at a current `σ`. It is therefore **not a member of
the family those theorems bound** — a genuine, citable point (already noted in the repo).

### 2.2 …and this genuinely bounds its ROUND count — but that was never the wall

Because a balanced cut halves `vol(X_t)` **unconditionally** (whatever sign the oracle
returns), the round count is `O(d·log(1/δ_gap)) = poly` regardless of the pivot lower
bounds. Friedmann cannot make the *number of rounds* exponential, because there is no
improvement path to lengthen — halving is not a local switch. This is the correct
content of "value-space evades Friedmann," and it is real.

**But it is empty as a poly-time claim**, for two reasons the repo already half-states:

- **Poly rounds hold for *any* `ℓ∞`-contraction**, from volume-halving alone — nothing
  about max/min/avg is used. So the operator structure does **not** add a provable poly
  bound here; the contraction does all the work, and the contraction was the black-box
  the mandate says to move past.
- **The cost is in the per-round center**, which is the survivor sampler of §1. A *true*
  balanced center needs the (open) sampler; a *cheap* surrogate center degrades into a
  local, policy-read-off rule — and then Melekopoglou–Condon bites. This is exactly the
  measured behaviour in `idea_d_mc.md`: with `cheap_center`, rounds-to-stabilize on
  `mc_basic(n)` climb `8/15 → 28/31 → (fail at n=6)`, drifting toward the `2^n−1` PI
  count. The advisor's ruling "D trades walls, doesn't skip one" is precisely this: the
  non-locality that evades Friedmann on rounds is bought back as sampler cost.

### 2.3 Does the center's *integration* provably differ from the pivots Friedmann defeats?

Yes in kind (global vs local), no in consequence. The balanced center integrates over
the candidate region, so a *single* center reflects many strategies at once — that is
why the round count is Friedmann-immune. But Friedmann-type hardness does not live in
the round count; it lives in **computing that integral over an adversarially-shaped
candidate set**, which §1.3 shows is the same conductance obstruction. The construction
that defeats local pivots is not "defeated" by integration; it **re-appears as the
region on which the integral is hard to estimate.** So the max/min/avg structure does
not provably make rounds-to-`σ*` poly-**work**; it makes rounds-to-`σ*` poly-**count**
(trivially, via halving) and leaves the work in the sampler.

**Verdict (Task 2): partial / delimited.** The balanced-center rule is provably not in
the Melekopoglou–Condon/Friedmann/Fearnley family and its round count is poly — a real
escape at the round-count level, correctly citable. It is **not** a poly algorithm: the
escape relocates all cost into the per-round survivor sampler, where Friedmann-type
hardness returns (§1.3), and the empirical MC test confirms the cheap-center bypass does
not escape. The operator structure adds nothing to this that the bare contraction did not.

---

## 3. Task 3 — where exactly one-sided-poly (the MDP LP) breaks, and does our geometry touch it

### 3.1 One-sided = a single linear objective over a convex polytope (verified)

Consider the constraint polytope built directly from the operator (not from pyramids):

```
R = { x∈[0,1]^d :  x_i ≥ f_i-arg   for every successor of each MAX node i
                   x_i ≤ f_i-arg   for every successor of each MIN node i
                   x_i = ½(x_j+x_k) (+reward/discount)  at AVG nodes,  sinks fixed }
```

Each MAX row `x_i ≥ γ·max(x_j,x_k)+…` is the **conjunction** `x_i≥γx_j+…` ∧ `x_i≥γx_k+…`
— a pair of halfspaces (the epigraph of a max is convex). Likewise `x_i≤min(...)` for
MIN. So **`R` is convex** (intersection of `O(d)` halfspaces).

- **MAX-MDP** (no MIN): `R={x≥f(x)}`, and `x*` is its **least** element, so
  `x* = argmin{Σx : x∈R}` — one LP. **Verified:** `ssg_strategy_check.py` `check_mdp_lp`,
  `max|LP−valueiter| = 1.0e-10` over 40 instances (`d=7`).
- **MIN-MDP**: `R={x≤f(x)}`, `x*` is the **greatest** element, `x*=argmax{Σx:x∈R}`.
  **Verified:** same, `1.0e-10`.

This is the standard MDP LP (d'Epenoux 1963; Puterman), re-derived in operator form. It
is poly because a *single* linear objective (min for the maximizer, max for the minimizer)
exposes the fixed point as a vertex of a convex polytope.

### 3.2 Two-sided: same convex `R`, but `x*` is exposed by NO linear objective (verified)

With both node types, `R` is **still convex** and **still contains `x*`** (all the
inequalities hold at the fixed point). What breaks is *selection*: minimizing `Σx` pins
the MAX-node inequalities tight but drives MIN nodes to their lower bound (the wrong
tightness); maximizing does the reverse. The two node types demand **opposite optimization
senses**, and a single LP has one sense. `x*` is the point of `R` where **every**
controlled inequality is tight on its chosen successor — a **complementarity** solution,
not a linear optimum.

**Verified:** `check_saddle_break`, on all **34/34** genuinely-two-player instances
(`d=7`), `x*` differs from **both** `argmin Σx` and `argmax Σx` over `R` (each by
`>10^{-6}`). So no consistent linear objective finds `x*`.

This is exactly **Jurdziński–Savani (CiE 2008)**: the values of a (binary, discounted)
two-player game are the solution of a **P-matrix LCP**, whose induced USO of the cube is
the strategy-valuation USO. The break "LP → LCP" is the precise place one-sided poly dies,
and it is the honest home of SSG's difficulty (UEOPL ⊇ P-LCP; Fearnley–Gordon–Savani–
Sørensen, ICALP 2019). It also re-explains Ye (2011): fixed discount ⟹ PI strongly poly,
so the hard LCP needs `γ=1−2^{−poly}`.

### 3.3 The decisive point: our value-space geometry does NOT address this break — it discards it

Here is the anti-repackaging crux the mandate asked for. The CLY cut `x*∈K(c,s)`,
`s=sign(f(c)−c)`, is derived treating `f` as a **black-box `ℓ∞`-contraction**. It is
therefore blind to the coordinate convexity of §3.1. Concretely:

> **Verified:** on a **pure MAX-MDP** (`d=8`), the black-box CLY cut has active support
> `8/8` at *every* tested point (`ssg_strategy_check.py`, support check) — i.e. it is a
> union of `d` pyramids, a **non-convex** `K(c,s)` with `conv K=ℝ^d` (`polytime.md` §3.2),
> **even though the instance is LP-solvable in one shot.**

So the value-space method would run its full non-convex-sampling machinery on a problem
that the operator structure solves by a single LP. The property that makes one-sided
easy — `{x_i≥max(succ)}` convex — is **exactly** what the contraction abstraction throws
away, replacing a halfspace by a `Θ(d)`-support pyramid union. This is the team lead's
suspicion, made rigorous: the black-boxing did not merely repackage one obstacle; it
manufactured a *harder* geometry (non-convex) than the operator actually has (convex on
one side), and it cannot even see the MAX/MIN interface where the true LCP hardness sits.

### 3.4 The structure-using direction (what it would take)

To *use* the structure, keep the convex `R` and cut with **operator-aware, convex** cuts.
`R` has `O(d)` facets and contains `x*`; the whole hardness is: **find the complementarity
vertex of a known convex polytope** = solve the P-LCP. An oracle query at `c` returns the
greedy action at each node (which successor is `max`/`min`), i.e. a **candidate face** of
`R`; a cutting-plane/pivot method on `R` guided by these is a P-LCP algorithm, and stays
**convex throughout** (no sampling, no isoperimetry). Whether it is poly is `P-LCP∈P` —
open, and a major independent result — but it is a **strictly better-posed** question than
"sample the non-convex `X_t`": convex body + complementarity separation, versus a
`2^{−t}`-thin non-convex body. The value-space work set this aside by black-boxing; the
operator-aware `R` is where the structure actually lives.

**Verdict (Task 3): concrete new reduction + diagnosis.** One-sided/two-sided break is
LP → P-LCP over the *same* convex `R` (both directions verified). Our pyramid geometry
does not address it and in fact discards the one-sided convexity (non-convex cut even on
an MDP, verified). The structure-using reformulation is cutting-plane/pivoting on the
convex `R` (= P-LCP), which is the honest UEOPL home — not a black-box sampling problem.

---

## 4. Synthesis against the mandate

- The prior "sample `X_t`" reduction is **faithful but operator-blind**: it black-boxes
  `f`, so it (i) cannot exploit one-sided convexity (Task 3 — it even non-convex-cuts an
  MDP), and (ii) buries the per-round cost in a sampler that is the *continuous
  relaxation* of the strategy-hypercube walk (Task 1), where Friedmann's hardness lives.
- The repo's "value-space ⟹ Friedmann does not apply" is **true for round count, false
  for total cost.** Rounds are poly by volume-halving (any contraction); the work is in
  the sampler, and the sampler = strategy-hypercube conductance = Friedmann (Tasks 1–2).
- The genuinely-structural home of SSG's hardness is **P-LCP over the convex operator
  polytope `R`** (Task 3, Jurdziński–Savani), not isoperimetry of a non-convex body.
  These are the same complexity (both `=SSG∈P`), but `R` is the formulation that *uses*
  the max/min/avg structure and keeps everything convex; the non-convexity in the
  value-space route is an artifact of black-boxing.
- **What would break it** (the only levers that use structure, none repackaging):
  (i) a survivor sampler for `S_t` that is not a local-flip walk (Task 1);
  (ii) a poly cutting-plane/pivot on the convex `R` = `P-LCP∈P` (Task 3);
  (iii) a proof that the discrete strategy-hypercube conductance is `1/poly` on
  *realizable* (balanced-apex) trajectories — the discrete twin of the `k(X_t)=poly`
  conjecture in `FINAL_REPORT.md`.

---

## 5. Experiments flagged to `main` (no heavy local compute done here)

All are `poly`-per-instance and decide structural questions the `d≤8` enumeration cannot:

1. **Survivor-sampling conductance vs Friedmann (tests §1.3).** On `mc_basic(n)` /
   Friedmann instances, run a lazy flip-walk on the strategy hypercube restricted to
   `S_t` (survivors after `t` real cuts) and measure its spectral gap / conductance vs
   `t`. Prediction: gap collapses exactly on the instances where `simple_pi` is
   exponential — confirming the two walls coincide. Reuses `friedmann.py`
   (`simple_pi`, `policy_eval`) + a flip-walk; no continuous sampling.

2. **Operator-aware convex cutting on `R` (tests §3.4).** Implement a cutting-plane /
   Lemke-style pivot on the convex `R` (facets from `succ`, greedy face from an `f`
   query) and compare iteration count to `simple_pi`'s `2^n−1` and to the value-space
   round count, on `mc_basic(n)` and random two-player instances. Question: does staying
   convex + LCP-separation beat the non-convex sampler empirically? (This is a P-LCP
   solver — subexponential at best in theory, but the *shape* of its hardness on
   realizable instances is the useful measurement.)

3. **δ_gap vs discrete-cut stall depth (tests §1.2c).** Extend `check_strategy_cloud`
   to record the round at which `keepfrac→1` (the stall) as a function of `δ_gap`.
   Prediction: stall depth `~ log(1/δ_gap)`, confirming the discrete view inherits the
   `log(1/δ_gap)` round requirement and offers no round-count gain.

---

## 5b. Is the SSG P-LCP over `R` poly-time-special? (the open core, surveyed)

Task 3 relocated `SSG∈P` to "solve the P-matrix LCP over the convex `R`." The honest
follow-up: is that LCP poly-special given SSG's structure (substochastic `M` with
`I−γM` a P-matrix; fixed bounded-degree graph; AVG = mean-of-2), or is it the open
P-LCP wall? **Answer: it is the open wall, and the natural convex-side algorithm hits it
at a precisely-known quantity.**

**What is known.**

- **The reductions.** Jurdziński–Savani (CiE 2008): discounted (deterministic-transition)
  games → P-matrix LCP. Gärtner–Rüst (FCT 2005): *general* SSG (incl. AVG/stochastic) →
  P-matrix **generalized** LCP. So the avg-of-2 is covered; the target is a genuine
  P-(G)LCP.
- **Interior-point on that LCP is poly *in the handicap `κ`*.** Kojima–Megiddo–Noma–Yoshise
  (1991) unified IPM solves a `P_*(κ)`-LCP in `O((1+κ)n^{3.5}L)`. This is the "work on the
  convex `R`" algorithm in its strongest form.
- **…but the SSG handicap is `Θ(n/(1−γ)²)` — exponential in the hard regime (decisive).**
  **Hansen–Ibsen-Jensen (2013, arXiv:1304.1888)** compute it: for a 2-player turn-based
  discounted game the unified IPM runs in `O((1+κ)n^{3.5}L)` with `κ=Θ(n/(1−γ)²)`, and a
  potential-reduction variant in `O((−δ/θ)n⁴log 1/ε)` with `−δ=Θ(√n/(1−γ))`,
  `1/θ=Θ(n/(1−γ)²)`. Poly for **fixed** `γ`; at `γ=1−2^{−poly}` (the SSG-reduction regime)
  **`κ` is exponential**. So IPM on the SSG P-LCP is *exactly* poly-for-fixed-discount,
  exponential-in-the-hard-regime — the same `1/(1−γ)` wall as value iteration.
- **Strategy iteration agrees.** Ye (2011) + Hansen–Miltersen–Zwick (JACM 2013,
  arXiv:1008.0530): Howard's PI is strongly poly for 2-player turn-based games with a
  **constant** discount, terminating in `O(m/(1−γ)·log(n/(1−γ)))` — again `1/(1−γ)`,
  exponential at `γ=1−2^{−poly}`.
- **One-player is LP because the LCP degenerates.** For a single controller `R={x≥f(x)}`
  (or `≤`) and the LCP matrix is a **hidden-K / Z-related (M-matrix) LCP**, solvable as an
  LP (§3.1). The two-player min∧max coupling is exactly the loss of that Z/K structure,
  leaving a matrix that is `P` but not hidden-K — the LCP-language form of "opposite
  optimization senses" (§3.2).

**Does working on `R` (IPM / pivot / cutting-plane) give new traction?** No — it lands
*exactly* on "poly P-LCP is open," now quantified: poly ⟺ handicap `κ≤poly`, and the known
`κ=Θ(n/(1−γ)²)` is exponential in the hard regime. General P-LCP has no poly algorithm
(UEOPL; Lemke is exponential, Morris 1994; USO sink-finding `2^{O(√n)}`). The gain over
the non-convex `X_t` route is *conceptual and better-posed* (a convex body + a well-studied
`P_*(κ)`-IPM toolbox, no isoperimetry) but **not** a complexity escape.

**The one unused structural lever a P-LCP specialist would try next (named, not a new
escape).** Hansen–Ibsen-Jensen's `κ=Θ(n/(1−γ)²)` is a **worst-case** bound driven by the
discount. The open question — the algebraic twin of `ssg_directions.md §7` — is whether the
*actual* handicap of a **non-degenerate** SSG-LCP is controlled by the **value gap `δ_gap`**
rather than `(1−γ)`:

> **(H) Handicap–gap transfer.** `κ(SSG-LCP) ≤ poly(n, 1/δ_gap)` on instances with value
> separation `δ_gap`. If true, the unified IPM is poly whenever `δ_gap≥1/poly` — a *single*
> convex algorithm recovering the smoothed (Manthey et al.), few-random-vertices
> (Gimbert–Horn) and ergodic (Akian–Gaubert–Hochart) regimes.

Why it is the right next target and not repackaging: (H) is about the **algebraic** handicap
of a standard LCP class with an existing IPM theory — a *different* quantity from the
geometric `κ(X_t)`/Cheeger the repo already tested, and one that the tropical/nonarchimedean
**condition-number** line (Allamigeon–Gaubert–Katz–Skomra, arXiv:1802.07712 — mean-payoff =
a condition number for nonarchimedean feasibility; complexity poly in it) treats as a
first-class object. **Honest caution:** the repo already found the *geometric* condition
number decoupled from `δ` (`condition_transfer`, `FINAL_REPORT §3`: `κ,h` flat across 4
decades of `δ`). Whether the *algebraic* handicap behaves differently is untested and is the
single measurement that would decide (H). **Newer convex home, same fate:** Bodwin/…
(*Reducing Stochastic Games to SDP*, ICALP 2025, arXiv:2411.09646) reduce SSG to SDP
feasibility — `SDP∈P ⟹ SSG∈P` — i.e. the LP→LCP→SDP convex ladder consistently lands on an
open convex-feasibility wall, not a poly algorithm.

**Verdict.** The SSG-structure push is **terminal as a new-escape hunt**: the correct home is
the open P-LCP over convex `R`, and every convex-side algorithm (IPM, PI, SDP) is poly in a
**condition number** — handicap `κ=Θ(n/(1−γ)²)`, PI's `1/(1−γ)`, the nonarchimedean
condition number, the smoothed `δ`, our geometric `κ(X_t)` — that are all avatars of the
**value-separation/discount gap**, which is `2^{−poly}` exactly in the hard regime. The one
concrete, un-run experiment that could reopen it is testing (H) (handicap vs `δ_gap`);
spec below.

**Experiment for `main` (capped).** Build the Jurdziński–Savani / Gärtner–Rüst P-LCP for
small SSGs; on instances where `(1−γ)` and `δ_gap` are **decoupled** (fix `γ=1−2^{−k}` large,
vary `δ_gap` via reward spread), measure the unified-IPM iteration count (and a handicap
proxy `max_x min_i x_i(Mx)_i/‖x‖²`) against both `1/(1−γ)` and `1/δ_gap`. Predicts (H) iff
iterations track `1/δ_gap`, not `1/(1−γ)`. Reuses `friedmann.make_operator`/`policy_eval`
for ground truth; cap at `d≤20`, `k≤30` (float64 margin floor). This is the algebraic analog
of the `act_cells.py` diam-vs-`δ_gap` check and would settle whether the convex/LCP home
adds anything the geometric route did not.

## 6. Sources

- Condon, *The complexity of stochastic games*, Inf. & Comp. 1992 (SSG, NP∩coNP,
  the value operator and strategy certification).
- Jurdziński, Savani, *A Simple P-Matrix LCP for Discounted Games*, CiE 2008 — the
  LP→P-LCP break of §3, and the USO identification.
- Melekopoglou, Condon, *On the Complexity of the Policy Improvement Algorithm for
  MDPs*, ORSA J. Comp. 1994 — the `2^n−1` simple-PI family (`friedmann.mc_basic`).
- Friedmann, *Exponential Lower Bounds for Policy Iteration*, ICALP 2009/2010; Fearnley,
  *Exponential Lower Bounds for Policy Iteration*, ICALP 2010 — local-rule lower bounds
  (Task 2's family).
- Ludwig, *A subexponential randomized algorithm for SSG*, Inf. & Comp. 1995 —
  `2^{O(√n)}`, the strategy-space record.
- Ye, *The simplex and policy-iteration methods are strongly polynomial for the MDP with
  a fixed discount*, Math. OR 2011 — why the hard regime needs `γ=1−2^{−poly}`.
- Gimbert, Horn, *SSG with Few Random Vertices Are Easy to Solve*, STACS 2008 —
  the tractable regime where the cloud has few permutation-values.
- Fearnley, Gordon, Savani, Sørensen, *Unique End of Potential Line*, ICALP 2019 —
  SSG / P-LCP / PL-contraction fixpoints in UEOPL (the honest home of §3).
- Chen, Li, Yannakakis, STOC 2024 (`ℓ∞`-contraction query complexity = the CLY cut this
  note argues is operator-blind).
- d'Epenoux 1963 / Puterman, *Markov Decision Processes* — the MDP LP of §3.1.
- Gärtner, Rüst, *Simple Stochastic Games and P-Matrix Generalized LCPs*, FCT 2005 —
  general SSG (incl. AVG) → P-matrix GLCP (§5b).
- Kojima, Megiddo, Noma, Yoshise, *A Unified Approach to Interior Point Algorithms for
  LCPs*, LNCS 538, 1991 — `O((1+κ)n^{3.5}L)` for `P_*(κ)`-LCP.
- Hansen, Ibsen-Jensen, *The Complexity of Interior Point Methods for Solving Discounted
  Turn-Based Stochastic Games*, CiE 2013 / arXiv:1304.1888 — handicap `κ=Θ(n/(1−γ)²)` (§5b).
- Hansen, Miltersen, Zwick, *Strategy Iteration Is Strongly Polynomial for 2-Player
  Turn-Based Stochastic Games with a Constant Discount Factor*, JACM 2013 / arXiv:1008.0530;
  Ye 2011 — PI bound `O(m/(1−γ)·log(n/(1−γ)))`.
- Allamigeon, Gaubert, Katz, Skomra, *Condition numbers of stochastic mean payoff games…*,
  arXiv:1802.07712 — mean-payoff as a nonarchimedean condition number.
- *Reducing Stochastic Games to Semidefinite Programming*, ICALP 2025 / arXiv:2411.09646 —
  SSG → SDP feasibility (`SDP∈P ⟹ SSG∈P`).
- Morris, *Lemke paths on simple polytopes*, 1994 — Lemke exponential on P-LCP.
- Repo cross-refs: `polytime.md` (balanced-point-as-LP, `conv K=ℝ^d`),
  `core_analysis.md`/`FINAL_REPORT.md` (`vol(X_t)=2^{−t}` thinness, the terminal wall),
  `idea_d_mc.md` (cheap-center negative on Melekopoglou–Condon), `ssg_directions.md`
  (the value-space/strategy-space framing this note qualifies).
```
