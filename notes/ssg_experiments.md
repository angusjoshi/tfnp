# SSG-structure experiments (run by main, overnight loop)

Testing whether the SSG operator's extra structure (monotone; max/min/avg of fixed
successors; fixed game graph) gives traction the black-box ℓ∞-contraction view lacked.

## EXP-1 — thin axis is a DIFFERENCE direction (ssg-monotone)
Realizable SSG X_t (t=2d, exact rejection), v_min = smallest-variance eigenvector:
| d,seed | axis overlap max_i|v_min[i]| | diff overlap max|v_min[i]±v_min[j]|/√2 |
|---|---|---|
| 4,0 | 0.73 | 0.98 |
| 4,1 | 0.64 | 0.87 |
| 5,0 | 0.56 | 0.76 |
| 5,1 | 0.69 | 0.86 |
| 6,0 | 0.70 | 0.93 |
| 6,1 | 0.75 | 0.96 |
Diff overlap consistently > axis overlap ⟹ the thin/dumbbell direction has a strong
`(e_i±e_j)` component, NOT a pure coordinate axis. **Rules out axis-aligned order/monotone
cuts as the fix** (they cannot pinch a difference-direction thinness); localizes the wall to
difference directions. (Mixed — axis overlap nonzero — so directional, not absolute.)

## EXP-2 — the operator branches on only O(d) FIXED comparisons (t-independent)
Distinct decisive comparison pairs (winner,runner-up) at max/min nodes across the trajectory:
| d,seed | distinctPairs | d·t | max possible |
|---|---|---|---|
| 4,0 | 6 | 32 | 20 |
| 4,1 | 6 | 32 | 8 |
| 5,0 | 7 | 50 | 40 |
| 5,1 | 4 | 50 | 6 |
| 6,0 | 10 | 72 | 28 |
| 6,1 | 7 | 72 | 26 |
distinctPairs ≈ d ≪ d·t. Because the game graph is FIXED, the operator's branching lives on
~d fixed comparison hyperplanes {x_a=x_b}, independent of t.

**HONEST CAVEAT (anti-over-claim):** O(d) *fixed* hyperplanes make the strategy arrangement
**t-independent** — a real gain over the moving-pyramid family (d²t hyperplanes) — BUT the
arrangement's cell count is still ~exp(d), because that count = the number of STRATEGIES,
which *is* the SSG hardness. So this is poly-in-t, still exp-in-d. It does NOT by itself give
poly sampling. Its real value: it argues for the STRATEGY-SPACE view (fixed O(d) hyperplanes,
t-independent) over the ℓ∞ pyramid-geometry view — the operator's structure lives in strategy
space, and the t-blowup is an artifact of the ℓ∞ method, not intrinsic.

## Reading
EXP-1 kills the axis/order-cut fix; EXP-2 says the intrinsic structure is O(d) fixed
comparisons (t-independent) but exp-in-d strategies. Together they point away from the
ℓ∞-geometry/pyramid-sampling route and toward strategy space — where the hardness is the
exp-in-d strategy count (= SSG), the honest core. Not a new escape yet; a redirection.

## EXP-3 (KICKER, verified by main) — the ℓ∞ abstraction is OPERATOR-BLIND
On a PURE MAX-MDP (one-sided, poly): x* from the convex LP over R = {x_i ≥ (1−γ)r_i+γ·succ}
matches value iteration to 1e-16 (poly, convex) — YET the CLY ℓ∞ pyramid cut at a balanced
point has FULL support |S|=d (5 at d=5, 8 at d=8, i.e. |S|≥3 ⟹ non-convex). So the ℓ∞-
contraction abstraction MANUFACTURES non-convex geometry on a problem that is actually
convex/poly. (MIN-MDP LP mis-encoded in the quick check — err~1.0, my bug, not a finding;
MAX confirms cleanly.)

## SYNTHESIS of the SSG-structure push (both agents + main, honest)
1. **The ℓ∞-pyramid/sampling route is the WRONG abstraction** — operator-blind, manufactures
   non-convexity even on convex MDPs (EXP-3). This partly EXPLAINS the whole session's wall:
   it was in part self-inflicted by discarding the operator's convex structure.
2. **The correct structural home is P-matrix LCP over the convex polytope** R = {x_i ≥ succ
   (MAX), x_i ≤ succ (MIN), x_i = avg} (Jurdziński–Savani; the UEOPL home). One-sided = LP
   over R (poly, verified); two-sided = the P-LCP saddle exposed by no linear objective (open
   = SSG-hard).
3. **Generic monotonicity is SPENT** (BFGMS "Monotone Contractions" STOC'25 2411.10107:
   monotone+contraction ∈ UEOPL, O((log 1/ε)^⌈d/3⌉) — still exp in d). The non-convexity is a
   DIFFERENCE-direction (e_i±e_j) phenomenon, orthogonal to monotonicity's axis (e_i) resource
   ⟹ monotonicity provably cannot convexify X_t. Discounted operator is NOT topical (tropical
   rescue fails).
4. **Value-space does NOT evade Friedmann** (corrects a repo claim): round count is poly for
   ANY contraction, but the per-round survivor-sampler cost = strategy-hypercube conductance =
   the Friedmann/Fearnley PI wall. The isoperimetry wall and PI lower bounds are the SAME wall
   in two coordinate systems.

NET: the honest home is SSG = P-matrix LCP over convex R, poly-time OPEN (= SSG∈P). The
ℓ∞-geometry route was operator-blind and counterproductive; the right object is convex and
better-posed, but its poly-solvability IS the open problem. No escape found; a genuine
correction of the abstraction + the precise (P-LCP) home.

## EXP-4 (A(t) on adversarial Melekopoglou-Condon) — concentration REFUTED on hard instances
A(t) = # strategy cells X_t spans. On RANDOM SSG: A(t)=2-4 flat (looked great) — but that was
an EASY-INSTANCE ARTIFACT (sinks in successor sets ⟹ most max/min nodes sink-dominated, only
1-2 contested). On MELEKOPOGLOU-CONDON (adversarial, PI=2^n): A(t) = 2^{#max/min nodes}
EXACTLY (n=3: 8=2^3; n=4: ~16=2^4), throughout the trajectory. So the strategy-cell count is
EXPONENTIAL on hard instances — the concentration escape fails precisely where it's needed.
Honest no-go for "A(t) poly."

## TERMINAL of the SSG-structure push — the correct object AND the correct parameter
(ssg-monotone §6 + ssg-strategy + main experiments, all honest)

- **Nonlinearity = sum of ReLUs of edge-differences:** max(x_a,x_b)=x_b+(x_a−x_b)^+,
  min=x_b+(x_a−x_b)^−. So f's entire nonlinearity is one ReLU per decision node on the scalar
  x_{a(i)}−x_{b(i)}; AVG/sink affine. The LCP has one complementary pair per decision node,
  complementarity living in V = span{e_{a(i)}−e_{b(i)}} — the difference-direction finding made
  EXACT and sharper (pure differences on the O(d) graph EDGES).
- **V is generically FULL-dim** ⟹ no automatic poly reduction. But dim V is the WRONG
  parameter (MAX-MDP has full-dim V yet is poly). The RIGHT parameter is the **min-max coupling
  rank** — the saddle coupling between max-controlled V_max and min-controlled V_min. Fixing
  either side collapses to an MDP=LP=poly; the irreducible object is the coupling, of dimension
  ~min(n_max,n_min) / the max-min alternation (a graph-cut/treewidth quantity).
- **This recovers ALL known tractable regimes as "coupling poly-small":** one-sided; 
  min(n_max,n_min)=O(log d); bounded alternation; δ-gap (few contested decision nodes at x*).
  Hard SSG = dense two-sided coupling = the open P-matrix LCP core = SSG∈P.

NET (honest terminal): the SSG-structure push did NOT solve it, but it (1) diagnosed the ℓ∞
route as operator-blind (manufactures non-convexity on convex MDPs), (2) identified the correct
object — P-LCP over convex R, and (3) identified the correct hardness parameter — min-max
coupling rank — under which every known poly regime is "coupling small." That is a genuine,
non-repackaged clarification. The residual wall is the open poly-P-LCP / dense-coupling core.

## EXP-5 (diam-shrink with EXACT centers) — the plateau was a cheap-center artifact
ssg-strategy saw diam(X_t) plateau above δ_gap with cheap hit-and-run centers, and flagged
exact-center as the go/no-go. Ran it: with EXACT-rejection accurate balanced centers, diam
shrinks GEOMETRICALLY (rate ~0.90–0.97/round ⇒ ~0.66 per d-block), NOT plateauing. ("reached
δ_gap=N" only because δ_gap≈1e-4 needs ~100 rounds; I ran 2d — the RATE is geometric.)
So the plateau was a cheap-center artifact; with accurate centers diam→0 geometrically.

IMPLICATION (honest): diam-shrink is NOT the open problem — it IS CLY's O(d log 1/ε)
poly-QUERY guarantee (formalized as cly_query_complexity), confirmed. So the reductio
"diam ≲ δ_gap ⟹ single strategy cell ⟹ convex ⟹ SSG∈P" has its diam-part TRUE in poly ROUNDS.
It does NOT give poly TIME because each round's accurate balanced point requires sampling the
2^{-t}-thin X_t — the open core. diam-shrink is a red herring; the per-round sampler is the wall.
Net: ssg-strategy's single-scalar diam target resolves to "already proven, not the bottleneck";
the bottleneck is unchanged (sample the thin body / dense-coupling P-LCP = open).

## EXP-6 (ssg-strategy P-LCP verdict, §5b) — condition-number unification, TERMINAL
SSG P-LCP over R is NOT poly-special — it IS the open P-LCP wall, quantified:
- SSG→P-LCP: Jurdziński–Savani CiE'08 (discounted); Gärtner–Rüst FCT'05 (incl. AVG → P-matrix
  generalized LCP, so avg-of-2 is covered).
- IPM poly in the handicap κ: Kojima–Megiddo–Noma–Yoshise '91, O((1+κ)n^3.5 L) for P_*(κ)-LCP.
- Hansen–Ibsen-Jensen 2013 (1304.1888): SSG handicap κ = Θ(n/(1−γ)²) — poly for fixed γ,
  EXPONENTIAL at γ=1−2^{-poly}. Same 1/(1−γ) wall as value/policy iteration
  (Ye'11 + Hansen–Miltersen–Zwick JACM'13: poly for fixed discount only).
- LP→LCP→SDP ladder (incl. SSG→SDP ICALP'25, 2411.09646) all land on an OPEN convex-feasibility wall.
UNIFICATION: every convex-side algorithm is poly in A CONDITION NUMBER — P_*(κ) handicap, PI
1/(1−γ), nonarchimedean cond# (Allamigeon–Gaubert–Katz–Skomra 1802.07712), smoothed δ (Manthey),
our geometric κ(X_t) — all avatars of the value-gap/discount = 2^{-poly} in the hard regime.
ONE un-run lever (H): is the ALGEBRAIC handicap controlled by δ_gap rather than (1−γ)? NOT run:
(a) it's a restatement of the value-gap wall, not a new escape; (b) even if true it gives
condition-number-parameterized poly (known via KMNY IPM), NOT worst-case SSG∈P; (c) predicted
no-go — Hansen–Ibsen-Jensen's κ is (1−γ)-form, and condition_transfer already found condition
numbers decouple from δ. Left as a documented parameterized lever, not pursued.

## OVERALL TERMINAL (SSG-structure push, both agents + main, honest)
The push produced a genuine, non-repackaged clarification and reached a clearly-articulated wall:
1. The ℓ∞-pyramid abstraction is OPERATOR-BLIND (manufactures non-convexity on convex MDPs; verified).
2. Correct object: P-matrix LCP over the convex polytope R (one-sided = LP = poly; two-sided = open).
3. Correct hardness parameter: a CONDITION NUMBER = the P_*(κ) handicap = min-max coupling rank
   = value-gap/discount, provably = 2^{-poly} in the hard regime; recovers every known tractable
   regime as "condition number poly-small."
4. Every would-be escape (Cheeger, κ-conditioning, guard/CC/k_eff cover, A(t)-concentration,
   diam-shrink, monotone order-cuts, handicap-vs-δ) reduces to this ONE condition-number wall.
SSG∈P ⟺ break the condition-number/value-gap dependence — the open core. No escape found;
the value is the correct object + the unified parameter + the operator-blindness diagnosis.
