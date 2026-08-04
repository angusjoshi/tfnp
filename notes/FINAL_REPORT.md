# Poly-time `ℓ∞`-contraction fixed points (⟹ SSG ∈ P): a consolidated report

A self-contained account of a sustained attack on computing an `ε`-approximate
fixed point of an `ℓ∞`-contraction `f:[0,1]^d→[0,1]^d` in `poly(d, log 1/ε)`
**time** — equivalent to putting simple stochastic games in **P**, a ~40-year
open problem. **The problem is not solved.** What this reports is the durable
output: machine-checked partial results, a precise reduction, a systematic map of
which attack routes die and *why*, and the single surviving lead with its exact
open proof target. Everything below is either machine-checked (Lean, `sorry`-free)
or explicitly marked as proof / empirical-in-window / conjecture. No result is
dressed as more than it is — a genuine closure here would be `SSG ∈ P`.

Detail and code: `notes/{hitrun,polytime,isoperimetry_summary,isoperimetry_attack,
isoperimetry_conditioning,crux_scalefree,repair_attack,condition_transfer,
idea_d_mc,m1_orderinterval,star_cover}.md` and `notes/polytime_experiments/`.
Running index: `notes/RESEARCH_LOG.md`.

---

## 0. Most important correction (SSG-structure push): the abstraction was operator-blind

A later push that *used the SSG operator's structure* (monotone; each coord = max/min/avg of
fixed successors; fixed game graph) — rather than black-boxing `f` as an ℓ∞-contraction —
produced the sharpest correction of the whole investigation:

- **The ℓ∞-pyramid abstraction manufactures non-convexity the operator does not have.**
  Verified: on a pure MAX-MDP (one-sided, poly-solvable — `x*` = convex LP over `R`, matches
  value iteration to `1e-16`), the CLY pyramid cut still has *full support* `|S|=d` (non-convex,
  `|S|≥3`). So the entire ℓ∞-geometry / leftover-body-sampling route (§§1–4, addendum) was in
  part fighting *self-inflicted* hardness.
- **The correct structural home is a P-matrix LCP over the convex polytope**
  `R = {x_i ≥ succ (MAX), x_i ≤ succ (MIN), x_i = avg}` (Jurdziński–Savani; the UEOPL home of
  SSG). One-sided (MDP) = LP over `R` (poly); two-sided = the P-LCP saddle exposed by no linear
  objective (open = SSG-hard). This is convex and better-posed than the `2⁻ᵗ`-thin non-convex
  `X_t` — but its poly-solvability *is* `SSG∈P`.
- **Monotonicity is spent** (BFGMS "Monotone Contractions" STOC'25: monotone+contraction ∈
  UEOPL, `O((log 1/ε)^⌈d/3⌉)`, still exp in d) and is *orthogonal* to the difficulty: the
  non-convexity lives in difference directions `e_i±e_j`, monotonicity acts on axes `e_i`.
- **Value-space does not evade Friedmann** (corrects an earlier repo claim): poly round count
  holds for any contraction, but the per-round survivor-sampler cost = strategy-hypercube
  conductance = the Friedmann/Fearnley policy-iteration wall — the same wall as the isoperimetry
  one, in a different coordinate system.

- **The correct hardness parameter is the min–max coupling rank.** f's nonlinearity is one
  ReLU per decision node on the edge-difference `x_{a(i)}−x_{b(i)}`, so the LCP complementarity
  lives in `V = span{e_{a(i)}−e_{b(i)}}` (difference directions, on graph edges). `V` is
  generically full-dim, but that is *not* the hardness (a MAX-MDP has full-dim `V` yet is poly);
  the irreducible object is the **coupling between max- and min-controlled directions** (fixing
  either side ⟹ MDP ⟹ LP ⟹ poly). This single parameter **recovers every known tractable
  regime** as "coupling poly-small": one-sided; `min(n_max,n_min)=O(log d)`; bounded
  alternation; δ-gap (few contested decision nodes at `x*`). Hard SSG = dense two-sided coupling
  = open poly-P-LCP core. (Verified: strategy-cell count `A(t)=2^{#decision nodes}` on the
  adversarial Melekopoglou–Condon family — exponential — while it collapses to `2–4` only on
  sink-dominated *easy* random instances.)

- **The unifying wall is a CONDITION NUMBER.** SSG = P-LCP is poly *in the handicap* `κ`
  (Kojima–Megiddo–Noma–Yoshise IPM), and Hansen–Ibsen-Jensen (2013) computed the SSG handicap
  `κ = Θ(n/(1−γ)²)` — poly for fixed `γ`, `exp` at `γ=1−2⁻ᵖᵒˡʸ`. Every convex-side algorithm is
  poly in *some* condition number — the `P_*(κ)` handicap, policy-iteration's `1/(1−γ)`, the
  nonarchimedean condition number, the smoothed `δ`, our geometric `κ(X_t)` — **all avatars of
  the value-gap/discount, `= 2⁻ᵖᵒˡʸ` in the hard regime.** The LP→LCP→SDP ladder (incl. the
  ICALP'25 SDP reduction) all land on the same open convex-feasibility wall. `SSG∈P ⟺ break the
  condition-number/value-gap dependence` — the open core. (One documented un-pursued lever:
  whether the *algebraic* handicap tracks `δ_gap` rather than `(1−γ)` — but even if so it yields
  only condition-number-parameterized poly, not worst-case `SSG∈P`, and is predicted no-go.)

Takeaway: the honest object is **SSG = P-matrix LCP over convex `R`**, poly-time open, whose
hardness is a single **condition number** (= min–max coupling rank = value-gap/discount); the
ℓ∞-geometry route below is a faithful *but operator-blind* reduction that adds artificial
non-convexity, and every escape tried in this project reduces to that one condition-number wall.
Detail: `notes/ssg_experiments.md`, `notes/ssg_strategy.md`, `notes/ssg_monotone.md`.

## 1. The reduction (what closing the problem requires)

Following CLY (arXiv:2403.19911), the algorithm maintains a candidate body
`X_t = [0,1]^d ∩ ⋂_{r≤t} K(c^r,s^r)`, where `K(c,s)=⋃_{i∈S}𝒫_i^{s_i}(c)` is a
union of `ℓ∞` "pyramid" cones and `c^r` is a **balanced point** of `X_{r-1}`.
Each balanced cut halves the volume and provably retains the fixed point `x*`.

**Reduction (formalized skeleton).** With `O(d·log 1/ε)` rounds, each doing one
oracle query + one balanced-point computation, an `ε`-fixed point is obtained.
Everything is `poly(d, log 1/ε)` **except** producing a balanced point, which
requires (near-)uniform sampling of the non-convex `X_t`. So:

> **poly-time ⟸ a poly-time near-uniform sampler for `X_t`.**  Everything else is
> elementary and machine-checked.

This is the entire game: the balanced point is a Fermat–Weber minimizer
(existence = compactness, formalized), computable by an LP on a *sample*; the only
open ingredient is the sampler.

---

## 2. Machine-checked results (Lean 4, `sorry`-free; axioms `propext`,
`Classical.choice`, `Quot.sound` only)

- **`Tfnp/Contraction.lean`** — `exists_balanced_point_box`: balanced points exist
  as `ℓ∞` Fermat–Weber minimizers (Brouwer-free; compactness + first-order
  optimality). The `sgnSup`/`mem_pyramidUnion_iff`/`linfDist_eq_max_sgnSup`
  machinery.
- **`Tfnp/HitRun.lean`** —
  - `fixedPoint_mem_pyrUnion_apex`: apex cut validity (`x*` is retained by the cut
    anchored at *any* query point `c≠x*`; no shift, no threshold).
  - `linfDist_self_map_le`, `isApproxFixedPoint_of_near`: extraction (proximity to
    `x*` ⟹ approximate fixed point).
  - `starshaped_of_toward`, `starshaped_of_kernel` (+ `_family`): the **star
    regime** — a cut pointing toward `x*` (resp. any center satisfying the kernel
    condition) makes `X_t` star-shaped, hence *exactly* ray-shootable, no
    isoperimetry needed.
  - `pyrUnion_subset_halfspace`, `exists_pair_pyrUnion_subset_halfspace`: the
    **convex regime** — support `≤2` (in particular `d≤2`) ⟹ every cut is a
    halfspace ⟹ `X_t` convex ⟹ poly-time by cutting planes.
- **`Tfnp/PolyTime.lean`** — a unit-cost meter over the query model (stated
  caveat: RAM-like, not bit-complexity): `costedRun_le`, `hitrun_time_poly`
  (total cost ≤ poly given poly oracle costs), and `endToEnd` (correctness **and**
  poly-time given a "good sampler" — the sampler is the one visible hypothesis).

These are real, citable contributions independent of the open problem: a
Brouwer-free balanced-point existence proof, and a machine-checked reduction of
the poly-time question to a single sampling hypothesis, with the star and convex
sub-regimes fully closed.

Separately (a distinct deliverable): `writeup/balanced.tex` — a Brouwer-free
proof of balanced-point existence via the `ℓ∞` Fermat–Weber functional, with a
Makefile and gitignored build dir.

---

## 3. The one wall, reached from every direction

Every attack reduces to the same obstruction: a **realizable anisotropic /
dumbbell `X_t`**, equivalently the **sign-pattern (strategy) trajectory** of the
cuts. The routes and how each dies:

| Route | Mechanism | Outcome |
|---|---|---|
| Cheeger `h ≥ 1/poly` | hit-and-run mixing | **REFUTED REALIZABLY** (post-consolidation, cycle 11): a certified-realizable adversary drives `X_t` to 17–23 mass-comparable components (`h = 0`) at d=5,6 within 2.5d rounds — `notes/adversarial_components.md`. Earlier status "Open Lemma = SSG-hard; unrestricted version false but non-realizable" is superseded |
| Conditioning `κ ≤ poly` | whiten + hit-and-run | `μ_W≤1` kills κ-blowup but is **necessary-not-sufficient** (poly-κ⟹mixing smuggles convexity; ball-minus-central-slab has κ≈1, Cheeger→0) |
| mean-reversion of `κ` | blind long axis is transient | **empirically false**: persistent blind axis realized (κ 3→15.6 over 5 rounds) |
| well-roundedness `vol(X_t)≤poly·vol(B)` | fill central valleys | **insufficient**: far-corridor dumbbell (vol-ratio O(1), Cheeger→0) |
| value-gap `δ` → `κ` transfer | game margin controls geometry | **soft no-go**: κ,h flat across 4 decades of δ; conditioning set by sign-pattern, not δ |
| Idea D (policy certificate) | sampler-free endgame | certificate is sound; cheap-center bypass **negative** (rounds→2ⁿ−1 on Melekopoglou–Condon); accurate center needs the sampler ("trades walls") |
| M1 (monotone convex cuts) | all-one-sign ⟹ convex orthant | **dead**: only 0–9% signed-consistent rounds; order-interval doesn't shrink |
| Corollary C (narrow to 2 coords) | small active set | **dead**: active set is Θ(d), max=d |
| L (spectral independence) | Glauber on cell-path | same dumbbell wall (`λ_max(influence)` breaks on a dumbbell) |

Unifying statement (from `crux-prover` + `condition-transfer`): κ, well-roundedness,
guard-count, and policy-convergence are **different functionals of one object —
the sign-pattern/strategy sequence** — and that object carries the SSG-hardness.

---

## 4. The surviving lead: Q (fat star-cover)

The one route **provably not equivalent** to the dumbbell wall. Cover
`X_t = ⋃_{j≤k} S_j` by `k` star-shaped pieces (each exactly ray-shootable);
union-sample by Karp–Luby in `poly(k)`. So **poly-time ⟺ star-cover number
`k(X_t) = poly(d,t)`**.

- **Provable orthogonality:** a dumbbell is Q-*easy* (`k≈2-3`) but Cheeger-hard; a
  comb is Q-*hard* (`k=Θ(teeth)`) but Cheeger-easy. Since the dumbbell was the
  *only* realizable counterexample the isoperimetry work ever produced, Q escapes
  that wall — it relocates hardness to a **combinatorial arrangement piece-count**.
- **Bounds:** `k ≤ (d²t)^d` (poly in t, **exp only in d**); `d≤2 ⟹ k=1` (convex).
- **Kernel reconciliation (proved):** `certifiable-kernel ⊆ true-kernel`, so C3's
  "kernel collapse" killed only the *certifiable* kernel — actual star-shapedness
  survives.
- **Empirics (exact rejection, in-window):** realizable `X_t` has `k=1` at t=d and
  `k=1–2` at t=2d for d=3,4,5 (robust to coverage target 0.999 and visibility
  resolution) — essentially star-shaped from one point, where the sampler is
  trivially poly. Calibration validated (dumbbell→2, comb(m)→m).
- **Terminal obstruction (honest):** the d-scaling of `k` — the *only* thing that
  decides Q — is **unmeasurable past d≈6–7** (deep-t bodies have volume `2⁻²ᵈ`,
  needing the very sampler we're building — circular; one unconfirmable outlier
  k=12 at d=7,t=2d on an under-sampled body). And on paper: reflex *hyperplanes*
  are additive `O(d²t)` but reflex *pieces* (= guard classes) blow up to
  `(d²t)^{d-1}`; balancedness controls new-pocket location but not far-pocket
  splitting by the infinite cones. No lever found to force the reflex arrangement
  into few-piece position; a bent-dumbbell-chain counterexample is plausible but
  not certified realizable (same "false-but-non-realizable" barrier as the Cheeger
  sliver).

**Open proof target (the crux of Q, hence of the whole problem):**
> prove `k(X_t) = poly(d,t)` for balanced-cut intersections — equivalently, that
> balanced ("central") cuts keep the reflex-boundary pieces `poly(d,t)`-many
> (a non-interacting-reflex-ridge / "pinwheel" bound). This is the Q-analog of the
> asymmetric-repair question and the one statement that would close the sampler.

---

## 5. Cross-field connections (the problem's mathematical neighbors)

Surfaced and vetted during the push (survivors only): geometry of MCMC / sampling
non-convex (star-shaped, bounded-non-convexity) bodies — beyond convex KLS;
nonlinear Perron–Frobenius / **topical (max-plus) maps** (the value operator *is*
topical) → mean-payoff & stochastic games; approximate counting (`vol(X_t)` as a
partition function on the cell-path space `[d]^t`); art-gallery / guard number
(Q); UEOPL placement (our `ℓ∞`-contraction fixpoint is a named UEOPL problem).
Framing worth keeping: our method is a **value-space** cutting-plane algorithm,
so the **strategy-space** lower bounds (Friedmann, Fearnley, Christ–Yannakakis)
do not directly apply — the one plausible way past the smoothed-analysis barrier,
though not a free pass.

---

## 6. Honest bottom line

`SSG ∈ P` is not solved and was never likely to be in one session; it is the
target, and every route independently reconverges on its known hardness — which
is itself the strongest evidence that the reduction is *faithful* (a genuine
route to the real problem, not an artifact). Concretely banked:

1. **Machine-checked** reduction + star/convex sub-regimes + Brouwer-free balanced
   points (all `sorry`-free).
2. **A dozen routes cleanly eliminated with reasons**, each traced to the same
   sign-pattern/isoperimetry core — a map that saves the next attempt from the
   dead ends.
3. **One live lead (Q)**, provably orthogonal to that core, with encouraging
   in-window empirics and a single, sharply-stated open proof target
   (`k(X_t)=poly` via non-interacting reflex ridges).
4. A recurring **measurement ceiling** (`d≲6–7`, `t≲2d`, volume `2⁻ᵗ`) that bounds
   what any exact-rejection experiment can decide — so further progress is a
   *proof* question, not a measurement one.

Recommended next step, if resumed: attack the Q proof target (or its
bent-dumbbell-chain counterexample) — the only door left that a purely
combinatorial technique, unavailable to the analytic routes, might open.

---

# Addendum: the convex-cover route (deepest push) — a complete algorithm modulo one conjecture

A later multi-agent push (see `core_analysis.md`, `sigma_scaling.md`, `convex_cell.md`)
assembled a **complete randomized poly-time algorithm** for the `ℓ∞` fixed point, reducing
`SSG∈P` to a single combinatorial conjecture. Not solved — but the sharpest reduction here.

## The structure (proved)
- `X_t = box ∖ (dt convex cones)` (verified exactly) = `box ∩ F⁻¹(P)`, `P` convex, `F` a
  piecewise-linear order-statistics map with only **σ** distinct orientations (σ = #distinct
  cut-sign vectors; σ ≤ #rounds = poly, empirically small).
- On each **active-pair cell** (fix argmax/argmin coord per cut), `X_t ∩ cell` is an
  intersection of halfspaces = **convex** (hence KLS-samplable). So `X_t` is a union of
  convex cells, and its **convex-cover number `CC`** satisfies `k(guards) ≤ CC ≤ k'(cells)`.
- σ=1 ⟹ `X_t` star-shaped about a known corner (Lean: `starshaped_of_single_sign`).

## The algorithm (assembled; poly iff the conjecture holds)
Each round: **telescope-sample** `X_t` from `X_{t-1}`'s convex cover (keep the ½ surviving
the cut — acceptance ½, *not* `2⁻ᵗ`) → **fresh greedy convex cover** of `X_t` → **Karp–Luby**
over the convex pieces (each KLS-samplable) → **Fermat–Weber LP** for the balanced point →
cut → recurse. This **removes all three walls**: identification (cover, don't identify),
thinness (telescoping resamples off the cover, never the box), mixing (pieces are convex).

## The single open conjecture (canonical form — where ALL routes converged)
> **(★) Volume-concentration lemma.** For realizable balanced-apex trajectories, at most
> `poly(σ,d)` of the (convex, KLS-samplable) active-pair cells of `X_t` carry `1−1/poly` of
> `vol(X_t)`.

This is the sharpest statement of the wall — not an isoperimetry constant, not a fragile
guard set, not an NP-hard min-cover: a concrete, falsifiable, self-contained
*volume-concentration* claim about which arrangement cells hold the mass. It comes with a
**poly-time algorithm that provably works whenever it holds** (greedy cell-discovery:
sample `X_t` → bucket by active-pair cell π(y)=(argmaxᵣ,argminᵣ) → each nonempty bucket is a
convex polytope, KLS-samplable → keep buckets by volume to `1−1/poly` → Karp–Luby). Poly
**iff** poly-many cells carry the volume = (★).
Empirically TRUE (greedy uses `~σ` pieces); worst-case FALSE (exp cells); the realizable-vs-
worst-case gap is `= SSG∈P`, unmeasurable-clean past `d≈6`.

Earlier equivalent phrasings (all shown to reduce to (★)): `X_t` admits a poly-size
poly-constructible convex cover; `CC ≤ poly(σ,d)`; guard/star-cover `k ≤ poly`; the
dominant-coordinate assignment is low-complexity across realizable rounds.

Equivalent forms surfaced: `CC ≤ poly(σ,d)`; the per-round `straddle`/split-count stays
poly; the dominant-coordinate assignment is low-complexity across realizable balanced rounds;
apex-spread stays `≤ 1/poly` under the contracting balanced cuts.

## Status (honest)
- **Empirically (★) holds:** `CC ~ σ` (small, flat in d), min-ties O(1), greedy achieves it —
  across the whole d≤6 exact-rejection window.
- **Every explicit/provable route to (★) FAILED:** σ-corners-cover (marginal), deep⟹kernel
  (0.0 at d=6), DoubleBind-thin (Δ-sensitive/inconclusive), uncovered⊆DoubleBind (contradicted,
  43% uncovered by near-corner guards), inductive-split (multiplicative, straddle≈CC),
  MutualBlock≪DoubleBind (false, they're equal). Only *unguaranteed* greedy attains `~σ`.
- So: **a small convex cover EXISTS empirically but has no proven poly construction** — which
  is exactly the realizability-vs-worst-case core, unmeasurable-clean past d≈6, and equal to
  `SSG∈P`.

**Deliverable:** a complete algorithm whose sole gap is the crisp, empirically-true,
provably-open conjecture (★). The identification, thinness, and mixing obstructions — which
sank every prior approach — are genuinely eliminated.

### The unifying result: four independent paths, one wall
The strongest evidence that (★) is the true core: **four independently-developed routes all
converge on the same reflex-piece count.**
1. **Cheeger / isoperimetry** (hit-and-run mixing) → dumbbell = many reflex pieces.
2. **Conditioning κ** (whiten + hit-and-run) → κ-blowup ⟺ reflex-piece proliferation.
3. **Guard / star-cover count `k`** (art-gallery) → guard number = reflex-piece classes.
4. **Convex-cover via telescoping** (this route) → convex pieces = reflex pieces.

All four equal: **is the reflex-piece count of `X_t` poly(d,t) on realizable trajectories?**
The order-statistic structure makes the reflex *hyperplanes* additive `O(d²t)`, but the
*pieces* multiply to `(d²t)^{d-1}` via global cone interaction (a reflex facet's exposure —
hence cell mergeability — is position-dependent, set by the other cuts' infinite cones). That
additive-hyperplanes / multiplicative-pieces gap is the hardness, and it is the realizable-vs-
worst-case core `= SSG∈P`. Convergence of four independent methods on it is strong evidence it
is the genuine wall, not an artifact of any one approach.

### Durable advance worth keeping (convex_cell §16)
The **telescoping-via-convex-cover** sampler is a real methodological advance: it resurrects
the telescoping sampler (dismissed in §3 for compounding `2⁻ᵗ` rejection) by replenishing
from a *maintained convex cover* — per-round acceptance `½` off the cover (never the box, so
**thinness removed**) with **convex** pieces (KLS-mixing, so **mixing removed**). It reduces
the entire problem to the single sharpest algorithmic question: *does `X_t` admit a poly-size,
poly-time-constructible convex cover?* — i.e. (★).

**Correction / final terminal state (§15).** The constructor is NOT closed: the merge-free
"sample-and-group by assignment cell" constructor is poly but produces a LARGE count
(`k_eff ≈ k'`, mass spread over ~all cells — measured 60/141/250 at d=4/5/6, growing with N).
The small cover `CC~σ` exists ONLY via greedy MERGING of cells, which is NP-hard /
approximation-guarantee-free. So (★) splits honestly into: *a small convex cover exists*
(empirical, `CC~σ`) but *has no proven poly construction* — merge-free is large, merge is
NP-hard. Every explicit construction and clean bound tried (σ-corners, deep⟹kernel,
DoubleBind, MutualBlock, inductive-split, k_eff-concentration) was **refuted empirically**;
only unguaranteed greedy attains `~σ`. The existence-vs-construction gap is the realizability
core `= SSG∈P`, unmeasurable-clean past `d≈6`. This is the honest terminal state.
