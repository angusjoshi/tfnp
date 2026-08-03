# Monotonicity + the max/min/avg form of the SSG value operator

Deliverable for the mandate "exploit **monotonicity** + the specific
`max/min/avg-of-2` structure of the SSG value operator, do **not** rename the
sampling obstacle." Read alongside `notes/polytime.md` (balanced point = LP; the
reduction to sampling), `notes/isoperimetry_summary.md` (the sampling wall),
`notes/ssg_directions.md` (routes map), `Tfnp/HitRun.lean` (Kernel Theorem).

**Verdict in one line.** The exact program — "use monotonicity **and**
contraction" — is a *published, active line* (Batziou–Fearnley–Gordon–Mehta–
Savani, **"Monotone Contractions," STOC'25**, arXiv 2411.10107). It pins what
generic monotonicity buys: **UEOPL membership + an exponent improvement
`⌈d/2⌉+1 → ⌈d/3⌉`, still exponential in `d`, NOT `P`.** All three of my concrete
tasks come back **honest-negative**, each with a precise structural reason, and
the reasons compose into a single clean statement (§4): *monotonicity acts on the
axis directions `e_i`; the CLY cut's non-convexity lives entirely in the
difference directions `e_i ± e_j`; the two families are orthogonal, so
monotonicity provably cannot convexify `X_t`.* The only leverage left is the
**algebraic form** (substochastic avg-of-2, out-degree-2 graph), which is
`SSG ∈ P` proper. One concrete lead + one experiment for `main` at the end.

---

## 0. The load-bearing external fact (BFGMS'25) — read this first

`f:[0,1]^d→[0,1]^d` **monotone** (`x≤y ⟹ f(x)≤f(y)`) **and** an `ℓ∞`-contraction
is *exactly* the object my mandate names, and it was studied head-on in STOC'25.
What they prove (arXiv 2411.10107, verified from the PDF):

| structure used | complexity of `ε`-fixed point | source |
|---|---|---|
| monotone only (Tarski) | `O((c·log 1/ε)^{⌈d/2⌉+1})` queries, **poly time OPEN** | Dang et al.; Chen et al. |
| contraction only (`ℓ∞`) | `O(d² log 1/ε)` queries but **time not poly**; best *poly-time-per-step* is `O(log^d(1/ε))` queries | CLY STOC'24; Shellman–Sikorski |
| **monotone + contraction** | `O((c·log 1/ε)^{⌈d/3⌉})` queries, **each step poly time**; problem ∈ **UEOPL** | **BFGMS STOC'25** |

Key points for us:

1. **Monotonicity genuinely helps — but only by a constant in the exponent.**
   The 3-D base case improves from `Θ(log² n)` (monotone-only) to `O(log n)`
   queries *because of contraction*; a decomposition/gluing theorem
   (`T(d₁+d₂) = T(d₁)·T(d₂)`) lifts it to exponent `⌈d/3⌉`. In the hard SSG
   regime `log(1/ε)=poly(bits)` and `d=#vertices`, `(poly)^{⌈d/3⌉}` is
   **exponential in `d`**. So this route does **not** put SSG/Shapley in `P`.
2. **The query model is essentially pinned.** They do *not* beat CLY's poly
   *query* count (the open problem was always **time**, not queries — see
   `polytime.md §0`). Their contribution is *poly-time-per-step* with a better
   query exponent, plus UEOPL. A matching-flavoured lower-bound line exists
   (Brânzei–Phillips–Recker, "Tarski lower bounds from multi-dimensional
   herringbones," 2025). So **generic monotone+contraction is close to exhausted.**
3. **They use monotonicity as a *dimension* handle, not a geometric one.** Their
   levers are (i) Tarski *least* fixed point for UEOPL uniqueness, made
   *verifiable in poly time* by contraction (verifying least-fixed-point is
   coNP-complete for monotone-only — contraction is what rescues it), and (ii)
   3-coordinate decomposition. Neither touches the CLY balanced-cut / sampling
   pipeline. So they do **not** use the `avg-of-2 / out-degree-2` algebraic form
   at all — that gap is real but is the whole problem (§4).

**Consequence for the mandate.** "Use monotonicity" as a *generic* order handle
is already banked (UEOPL + `d/3`). Beating it requires the SSG-specific algebraic
form, i.e. exactly `SSG ∈ P`. This reframes all three tasks: they are tests of
whether generic monotonicity offers anything the geometric method can use *beyond
what BFGMS already extracted from it* — and the answer is no, for a reason (§4).

---

## 1. Task 1 — the order bracket `[L,U]`  ⟹  honest negative

**Setup.** Maintain `x* ∈ [L,U]`, `L = sup` of found **sub-solutions**
(`f(c)≥c ⟹ x*≥c`), `U = inf` of found **super-solutions** (`f(c)≤c ⟹ x*≤c`).
The implications are Knaster–Tarski: `f(c)≥c ⟹ c≤f(c)≤f²(c)≤…→x*`, an increasing
sequence with limit `x*`, so `c≤x*` (`f` monotone + contraction; proof is
one line, `notes/ssg_monotone` scratch). One query certifies each.

**Can we FORCE sub/super-solutions and shrink `U−L` poly-fast?** There are
exactly **three** ways to advance a bracket endpoint, and every one is a *named
known wall*:

- **(a) Cheap monotone certificate, advanced by iterating `f`.** If `f(c)≥c`
  then `f(c)` is a *larger* sub-solution (`f(f(c))≥f(c)`). Iterating is
  **value iteration**; each step gains a factor `(1−δ)`. Width shrinks at rate
  `δ = 2^{−poly}` — **useless** in the hard regime. ("Weakly poly buys nothing,"
  `polytime.md §0`.)
- **(b) Exact order test "is `x*≥t`?"** This is *precisely the SSG value
  decision problem* (NP∩coNP, not known poly). Lattice binary search using it
  would solve the game — because it **is** the game. Not an algorithm.
- **(c) LP-per-strategy order advance = policy iteration.** For a fixed MAX
  strategy `σ`, the induced game is an MDP; `val(σ)` solves an LP and satisfies
  `val(σ) ≤ x*`, and `val(σ)` is *itself a sub-solution* (`f(val(σ)) ≥
  f_σ(val(σ)) = val(σ)`). Advancing `L` through the `val(σ)` as `σ` improves is
  **exactly Hoffman–Karp policy iteration**, which has **Friedmann's exponential
  lower bounds** (and `2^{Ω(√n)}` for random-facet, tight per Friedmann–Hansen–
  Zwick). `ssg_directions.md §3`.

**Why there is no fourth ("free geometric") option.** A sub-solution point needs
`f(c)_i ≥ c_i` on **all `d` coordinates simultaneously**. The prior M1
experiment already found the ternary displacement sign **mixed most rounds** —
i.e. a generic query point is *neither* sub- nor super-solution. The sub-solution
set `S₊={c:f(c)≥c}` is a sub-lattice (closed under `∨`, `sup = x*`) but is **not
ray-connected toward `x*`** (`max/min` pieces break monotonicity of the predicate
along a segment), so you cannot binary-search a line for the largest sub-solution.

**Verdict (Task 1).** The order bracket is **value iteration in disguise**
(rate `δ`) under any elementary lattice/bisection scheme; the only ways to make
it *query*-efficient are (b) [= the problem] or (c) [= policy iteration,
exponential] or the BFGMS decomposition [= exponential in `d`]. As a *width*-
shrinking process it is *Tarski fixed-point search* (monotone-only: `Θ(log^d)`
queries, poly time open — the mandate's explicit "beware" case). **It does not
shrink `U−L` poly-fast.**

---

## 2. Task 2 — monotone + LP, and the geometric handle  ⟹  honest negative + redirect

**Does "MDP-LP + monotone iteration" compose into something beating policy
iteration?** No — *that composition **is** policy iteration.* One iteration =
solve one player's best-response MDP by LP, then monotonically improve the other
player's strategy (value increases monotonically). This is Hoffman–Karp verbatim,
hence Friedmann-exponential. Survey (grounded, `ssg_directions.md §§3–5`):
Hoffman–Karp / Condon (NP∩coNP); Ludwig `2^{O(√n)}` (random-facet, tight);
Gimbert–Horn (FPT in `#random vertices`); Auger–Coucheney–Strozecki (Bland's
rule); Akian–Gaubert–Hochart (bounded-return-time strongly poly);
Manthey et al. smoothed-poly (**deterministic only** — Christ–Yannakakis kills
the stochastic case). None composes with monotone-LP into a poly algorithm; the
monotone iteration *is* the strategy-improvement step they already contain.

**Does monotonicity give an unused handle for OUR geometric (value-space cut)
method?** The honest read, now that BFGMS is on the table:

- Monotonicity's *only* new geometric cut is the **order half-space**: on a
  single-signed round (`f(c)−c` all `≥0` or all `≤0`) we may cut with `x*≥c`
  (resp. `≤c`), a **convex, axis-aligned** cut that keeps `X_t` an order box.
  This is strictly stronger than the CLY pyramid cut *when it fires*. But by M1
  it **fires rarely** (mixed most rounds), and a mixed round admits no order
  cut, only the (non-convex) pyramid cut. So order cuts do not, by themselves,
  keep `X_t` convex.
- BFGMS show monotonicity's *real* algorithmic value is **UEOPL + dimension
  decomposition (`d/3`)**, which is *orthogonal* to the CLY balanced-cut sampler:
  it solves `3` coordinates at a time and glues, rather than sampling the full-`d`
  body. This is the productive way to spend monotonicity — and it is already
  exponential in `d`.

**Verdict (Task 2).** Direct composition = policy iteration (Friedmann). The
geometric method's monotone handle is the order half-space, which is confined to
the rare single-signed / flat-gap rounds. The genuinely useful monotone lever is
BFGMS's **`3`-D-base + decomposition**, which is *not* a booster for the full-`d`
sampler and is *not* poly-in-`d`. **New-angle-but-bounded redirect:** if one
insists on the geometric route, combine value-space cutting with a *`3`-coordinate
decomposition* (BFGMS-style) rather than sampling the full body — but budget for
exponent `d/3`, not `P`.

---

## 3. Task 3 — is `X_t` order-convex / star-shaped / a union of few order intervals?  ⟹  honest negative WITH the precise reason (the new content)

`X_t = box ∩ ⋂_r K(c^r,s^r)`, `K(c,s)=⋃_{i∈S} P_i^{s_i}(c)`; membership
`y∈K ⟺ max_i w_i + min_i w_i ≥ 0`, `w_i=s_i(y_i−c_i)` (`isoperimetry_summary.md §1`).

**(3a) Is `K(c,s)` up-set or down-set (order-convex)?** **No.** Take `y∈K` with
witness `i`, `s_i=+1`: `y_i−c_i ≥ |y_j−c_j| ∀j`. Raising `y ↑ y'` grows the LHS
but also grows `|y'_j−c_j|` for coords moving *away* from `c_j`; membership can be
lost. So `K` is neither upward- nor downward-closed; `X_t` is not an order
interval. (Consistent with "genuinely non-convex," the whole point of the wall.)

**(3b) Union of *few* order intervals?** **No.** Distributing,
`X_t = ⋃_{π∈[d]^t} ⋂_r P_{π(r)}` — up to `d^t` cells, and each cell is **not** an
order box: a pyramid `P_i^+(c)` has facet normals **`e_i − e_j`** (from
`y_i−c_i ≥ y_j−c_j`) and **`e_i + e_j`** (from `y_i−c_i ≥ −(y_j−c_j)`), *not* the
axis normals `e_i` of an order box (confirmed against the repo:
`notes/hitrun.md:75`, `Tfnp/HitRun.lean` kernel is pairwise
`σᵢ(zᵢ−cᵢ)+σⱼ(zⱼ−cⱼ)≥0`).

**(3c) Order-convex about a *computable* center?** Order-convexity of `X_t` about
`c` is *exactly* the **toward-cut / flat-gap regime**: it needs
`s_i = sign(x*_i − c_i)` for all `i` (displacement sign = direction-to-fixed-point
sign), which is **Theorem A**'s hypothesis (`isoperimetry_summary.md §2`, machine-
checked, formalised `starshaped_of_toward`). Prior work established this **fails
generically** past the flat-gap regime — that *is* the anisotropy wall. So
monotonicity does not supply a new computable star-center; the star regime is the
already-known easy case.

### The precise structural reason (this is the deliverable's new content)

Assemble (3a)–(3c) into **one** statement that explains *why* monotonicity is
powerless here and is not a rename of the sampling obstacle:

> **Orthogonality of the monotone handle to the CLY non-convexity.**
> Monotonicity of `f` produces information **only in the axis directions `e_i`**:
> every consequence is of the form "if the deviations are consistently signed
> then `x*` lies on one side of an *axis-aligned* half-space" (the order cut /
> orthant). The CLY cut's non-convexity lives **entirely in the difference
> directions `e_i ± e_j`**: `K(c,s)` is a union of cones whose facets are
> `e_i±e_j` and whose non-convexity is the `OR_i` over "signed deviation `i`
> **out-ranks** all others" — a statement about the *relative order of the
> `|y_j−c_j|`*, i.e. the difference coordinates. The families `{e_i}` and
> `{e_i±e_j}` are orthogonal (distinct root directions). Therefore **no amount of
> order/monotone information can convexify `X_t`**: order cuts control the `e_i`
> directions; the bottleneck (dumbbell) always opens in an `e_i±e_j` direction
> the order structure does not see.

This is *why* the mandate's instinct meets a wall, stated at the level of the
geometry, and it is new: it says the prior "one wall = anisotropic/dumbbell"
(`isoperimetry_summary.md §4`) is specifically a **difference-direction**
phenomenon, and monotonicity is constitutionally the wrong tool for it. It also
predicts (testable, §5) that the thin/dumbbell axis of a realizable `X_t` is
always aligned with some `e_i±e_j`, never a pure `e_i`.

### Two corollary facts worth recording

- **The discounted operator is NOT topical.** `max/min/avg-of-2` are additively
  homogeneous (`g(x+λ1)=g(x)+λ`), but the constant sinks (`0/1`) and the discount
  `γ<1` **break** homogeneity — that broken homogeneity is *exactly* what makes
  `f` a strict contraction in the hard regime. So max-plus / tropical-convexity
  spectral theory (Gaubert–Gunawardena, Akian–Gaubert–Guterman) does **not**
  apply to convexify the discounted body; it applies only in the undiscounted
  `γ=1` (mean-payoff) limit, which is not our regime.
- **`f` factors through `d` binary comparisons.** Out-degree 2 means the strategy
  at `c` is fixed by the `d` sign tests `y_{a(i)} ≷ y_{b(i)}` (one per max/min
  node). So `c ↦ s(c)` is piecewise-constant on the arrangement of the **`d`
  specific difference-hyperplanes** `{y_{a(i)}=y_{b(i)}}` — sparse (`d`, not
  `\binom d2`). This sparsity is *unused* by both CLY (whose pyramid still
  compares all pairs) and BFGMS (generic monotone). It is the one place the
  algebraic form is genuinely untouched — see the lead in §5.

**Verdict (Task 3).** `X_t` is **not** order-convex, not star-shaped about a new
computable center, not a union of few order intervals. The precise reason —
monotone info ⟂ `e_i±e_j` non-convexity — is the honest structural explanation,
and it subsumes/sharpens the prior "dumbbell" wall to a **difference-direction**
wall.

---

## 4. Synthesis: the three tasks are one wall, restated in transferable terms

- **Task 1** dies because a sub-solution needs *all* `d` axis-signs to agree
  (rare); forcing agreement = value iteration / policy iteration / the decision
  problem.
- **Task 2** dies because monotone-LP composition *is* policy iteration, and the
  only real monotone lever (BFGMS) is dimension-decomposition, exponential.
- **Task 3** dies because the CLY non-convexity is in `e_i±e_j`, orthogonal to the
  `e_i` directions monotonicity controls.

All three are the **same fact**: *monotonicity is an axis-direction
(`e_i`) resource; both the value operator's hardness (min–max interleaving) and
the geometric body's non-convexity are difference-direction (`e_i±e_j`)
phenomena.* Generic monotonicity is therefore essentially spent by BFGMS
(`UEOPL`, `d/3`), and what remains — the substochastic `avg-of-2`, out-degree-2
**algebraic** structure in the difference directions — **is** `SSG ∈ P`. This is
a negative, but a *localised* one: it says where to point the remaining effort
(the `e_i±e_j` / difference-direction algebra), and it certifies that the
"black-boxed contraction, sample the leftover body" framing was not merely
repackaged — monotonicity was a genuinely different tool, and we can now say
precisely why it does not open the body.

---

## 5. One concrete lead + one experiment for `main`

*(Results in `notes/ssg_experiments.md`. EXP-1 confirmed the orthogonality
prediction directionally — thin-axis difference-overlap `0.76–0.98` >
axis-overlap `0.56–0.75` — so axis/order/monotone cuts provably cannot fix the
thinness; the wall is a difference-direction one. EXP-2 confirmed
`#distinctPairs ≈ d ≪ d·t`, BUT with a correction to the lead below.)*

**Lead — corrected.** The original inference here ("`poly(d)` distinct
hyperplanes ⟹ `poly(d)` cells ⟹ poly sampling") was **half wrong** and is
retracted. What is true: the operator branches on only `O(d)` **fixed**
comparison hyperplanes `{y_{a(i)} = y_{b(i)}}` (out-degree 2, fixed game graph),
**`t`-independent** — so the `d^t` cell blow-up of the ℓ∞ method is an *artifact*,
not intrinsic. What is false: `O(d)` hyperplanes of the form `x_a = x_b` in `ℝ^d`
still cut out **`exp(d)`** cells — their region count is the number of **acyclic
orientations** of the game graph (Stanley), e.g. `2^{m}` for a tree with `m`
edges — and this equals the number of **strategy profiles**, i.e. the SSG
hardness itself. Two distinct arrangements were conflated: the `O(d)` **fixed
strategy hyperplanes** vs. the **moving pyramid cuts** `K(c^r,s^r)` that define
`X_t`. So EXP-2 argues for the **strategy-space** view, not the pyramid-sampling
view, and does **not** give poly sampling.

**The residual wall is the `exp(d)` strategy count** (I agree with `main`). The
`t`-independence is a genuine gain but leaves the intrinsic `d`-dependence intact.

**The genuinely-new, measurable refinement (this is where the specific form is
still unused).** The right quantity is not the *total* cell count but the number
of strategy cells the **realizable, shrinking** body `X_t` actually **intersects**
as `t` grows. Once `diam(X_t)` drops below the value-separation gap `δ` (the
`ssg_directions.md §7` condition number: `min_i |x*_{a(i)} − x*_{b(i)}|` over
non-tied nodes), `X_t` can only straddle the hyperplanes of **tied/indifferent**
nodes, so `#active cells ≤ 2^{#tied nodes at x*}`. Thus:

> **#strategy cells meeting `X_t`  ≤  2^{#nodes indifferent at `x*`}  (once
> `diam(X_t) ≲ δ`).**

If the realizable trajectory activates only `poly(d)` cells (⟺ few tied nodes ⟺
`δ ≥ 1/poly`), sampling reduces to `poly(d)` convex pieces and the geometry
becomes tractable — but this is **not new physics**: it is exactly the
**condition-number transfer** (`ssg_directions.md §7`), now sharpened to a
concrete *countable* quantity. It is `= SSG ∈ P` only in full generality; its
value is that "#active strategy cells vs `δ`" is directly measurable and hands
`ssg-strategy` a strategy-space target. Do **not** read this as poly sampling.

**EXP-1 / EXP-2 above are done** (`ssg_experiments.md`). The **follow-up
experiment** that tests the corrected refinement — the go/no-go on the
condition-number bridge in its sharpened, countable form:

> **EXP-3 (active strategy cells vs `δ`).** For each realizable instance, as the
> body `X_t` shrinks, count `A(t)` = number of distinct sign-patterns of the
> `O(d)` comparisons `y_{a(i)} ≷ y_{b(i)}` realized by uniform samples of `X_t`
> (bin samples by their comparison sign-vector; `A(t)` = #nonempty bins). Also
> compute `δ = min_i |x*_{a(i)} − x*_{b(i)}|` over non-tied nodes and
> `#tied = #{i : |x*_{a(i)} − x*_{b(i)}| ≤ tol}`. **Predictions:** (i) `A(t)`
> **plateaus at `≈ 2^{#tied}`**, not growing toward `exp(d)`, once
> `diam(X_t) ≲ δ`; (ii) `A(t)` is `poly(d)` exactly on the `δ ≥ 1/poly`
> instances. If `A(t)` stays `poly(d)` and tracks `δ`, the condition-number
> bridge has a concrete checkable core; if `A(t) → exp(d)` while `δ` is bounded,
> the bridge is refuted for those instances. Reuses the same sampler + the
> successor-pair recorder from EXP-2. **This is a strategy-space quantity — hand
> to `ssg-strategy`.**

---

## 6. Does the difference-direction structure translate to the P-LCP home? (terminal)

`ssg-strategy`'s converging finding is that the correct object is the **P-matrix
LCP over the convex polytope `R`** (Jurdziński–Savani), not the ℓ∞ pyramid body
(the ℓ∞ abstraction *manufactures* non-convexity even on a convex MAX-MDP —
verified by `team-lead`). The focused question: does my difference-direction
localization give a usable lever there, or is the complementarity full-dimensional
(= open P-LCP core)?

**Exact algebraic localization (clean, and it vindicates §3).** Every decision
node decomposes as
```
max(x_a, x_b) = x_b + (x_a − x_b)^+ ,   min(x_a, x_b) = x_b + (x_a − x_b)^− ,
```
so the **entire nonlinearity of `f` is a sum of `ReLU`s of the scalar differences
`x_{a(i)} − x_{b(i)}`, one per max/min node.** AVG and SINK nodes are affine (no
complementarity). Hence the LCP has **one complementary pair per decision node**,
`z_i = (x_{a(i)}−x_{b(i)})^+`, `w_i = (x_{a(i)}−x_{b(i)})^−`, `z_i w_i = 0`,
`x_{a(i)}−x_{b(i)} = z_i − w_i`. **The complementarity lives exactly in the
difference subspace**
```
V = span{ e_{a(i)} − e_{b(i)} : i ∈ MAX ∪ MIN }.
```
This is §3 made exact — and sharper: it is the *differences* `e_i − e_j` (not
sums), restricted to the `O(d)` **graph edges**, not all pairs.

**Is `V` low-dimensional? No — generically `dim V = Θ(d)` (full).** `dim V` =
rank of the decision-edge incidence, up to `d−1` when the max/min edges connect
all coordinates. So there is **no automatic low-dim reduction**; the
complementarity is full-dimensional in general.

**But dimension of `V` is the wrong hardness parameter.** A MAX-MDP has `n_max`
complementary pairs (`V_max` can be full-dim) yet is **poly** by LP. So *many
complementary pairs is not the hardness.* The hardness is the **min–max
coupling** between `V_max = span{e_{a}−e_{b}: MAX}` and `V_min` (analogous). Two
facts pin this:

- **Fixing either side collapses to LP.** Fix the MIN strategy ⟹ residual is a
  MAX-MDP ⟹ LP over `R` ⟹ poly (symmetric for MAX). So `V_min` is "free" once
  `V_max` is resolved and vice versa; the irreducible object is the **saddle
  coupling `V_max ↔ V_min`.**
- **The hard dimension is the coupling rank, not `dim V`.** The saddle lives in
  an `O(min(n_max, n_min))`-dimensional arena (fix the smaller side: `2^{min}`
  profiles, then LP). More refined: the **interface/alternation** between the
  MAX-controlled and MIN-controlled difference subspaces — a graph-cut/treewidth
  parameter of the game graph.

**Verdict (terminal for the monotone / difference-direction angle).**
- The difference-direction structure translates **exactly** to the P-LCP: the
  complementarity is confined to `V = span{e_{a(i)}−e_{b(i)}}`. This confirms and
  sharpens the localization.
- **It does not, by itself, give a poly-dim lever.** `dim V = Θ(d)` generically,
  and even the reduced saddle is `min(n_max, n_min)`-dimensional — **full-
  dimensional / the open P-LCP core** when both players densely control `Θ(d)`
  nodes with dense alternation.
- **What it does buy** (honest partial credit): it names the *correct* hardness
  parameter — the **min–max coupling rank** between `V_max` and `V_min` — and
  recovers every known tractable regime as "coupling is poly-small":
  `min(n_max,n_min)=O(log d)` (few controlled vertices of one type), bounded
  alternation/interface (a graph parameter), or the `δ`-gap regime of §5 (few
  *tied* decision nodes at `x*`, which is where the coupling is actually
  exercised). Combining §5 and §7: **the residual saddle is over the *tied*
  decision nodes at `x*`; it is one-sided (⟹ LP ⟹ poly) iff those tied nodes are
  almost all MAX or almost all MIN.**

So: the monotone/difference-direction line **bottoms out at the P-LCP core**, as
expected, but leaves behind a concrete, checkable parameter (min–max coupling
rank / two-sidedness of the tied set at `x*`) rather than a vague "sample the
body." That parameter is the clean interface to `ssg-strategy`'s P-LCP work.

**Check to spec (sharpens EXP-3, hand to `ssg-strategy`/`main`).** On the
realizable instances, among the `#tied` decision nodes at `x*` (§5), report the
split `(#tied-MAX, #tied-MIN)`. Prediction of the tractable regime:
`min(#tied-MAX, #tied-MIN)` is small (residual saddle one-sided ⟹ LP). If it is
`Θ(d)` on hard instances with bounded `δ`, that is the open P-LCP core, full-dim,
and the honest terminal.

---

## 7. Sources

- Batziou, Fearnley, Gordon, Mehta, Savani, **Monotone Contractions**, STOC 2025
  — https://arxiv.org/abs/2411.10107 (UEOPL; 3-D `O(log 1/ε)`; decomposition to
  `⌈d/3⌉`; Shapley games placed in UEOPL). *The load-bearing reference.*
- Brânzei, Phillips, Recker, **Tarski lower bounds from multi-dimensional
  herringbones**, 2025 (query lower bounds for Tarski / monotone).
- Chen, Li, Yannakakis, STOC 2024 (`ℓ∞`-contraction, `O(d² log 1/ε)` queries);
  Dang et al. / Etessami et al. / Chen et al. (Tarski, `log^d`); Shellman–
  Sikorski (poly-time contraction, `log^d` queries).
- Condon 1992 (SSG ∈ NP∩coNP); Friedmann 2010, Friedmann–Hansen–Zwick 2011
  (policy-iteration / random-facet lower bounds); Ludwig 1995 (`2^{O(√n)}`);
  Gimbert–Horn 2008; Akian–Gaubert–Hochart 2013; Manthey et al. 2024 +
  Christ–Yannakakis (smoothed, deterministic only). Full bibliography in
  `notes/ssg_directions.md §Source list`.
