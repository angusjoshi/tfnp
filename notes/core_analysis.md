# Working the core directly: the "box minus dt convex cones" reformulation

Direct attack on the load-bearing core (poly-time sampler / balanced point for `X_t`
= `SSG∈P`). Result: **not cracked** (it's the open problem), but the cleanest
reformulation yet, plus a *rigorous* account of why the natural convex reductions
fail — which pins the difficulty to one precise quantity.

## 1. The reformulation (verified exactly, d≤8, 0 mismatches)

In sign-folded coords `w_i = s_i(y_i−c_i)`, the removed half of a cut is
`N(c,s) = {y : max_i w_i + min_i w_i < 0}`. Taking `k=argmin_i w_i`:
`max_i w_i < −w_k ⟺ w_k + w_j < 0 ∀j`. Hence

> `N(c,s) = ⋃_{k=1}^d C_k`,  `C_k = {y : s_k(y_k−c_k)+s_j(y_j−c_j) < 0  ∀j}`,

each `C_k` an intersection of `d` linear halfspaces = a **convex** polyhedral cone
(apex `c`, ≤d facets). Therefore

> **`X_t = box ∖ ⋃_{r=1}^t ⋃_{k=1}^d C_k^r`** — a box with `dt` convex cones removed.

This is strictly cleaner than "intersection of pyramid-unions": the removed set is a
union of `dt` **convex** pieces. Equivalently, `X_t` is the union of the arrangement
cells of `dt` cones that avoid all of them.

## 2. What the convex structure buys — and the exact barrier

The structure makes several things *poly-time computable* that look decisive but
are not, all defeated by one fact: **`vol(X_t) = 2^{−t}·vol(box)` exactly** (balanced
cuts halve, proven), so `X_t` is an **exponentially thin** fraction of every convex
object we can compute with.

- **Volume of the removed set:** `⋃_{r,k} C_k^r ∩ box` is a union of `dt` convex
  bodies ⟹ Karp–Luby estimates `vol(⋃ cones)` in poly time (each convex piece has
  poly-time approx-volume (Dyer–Frieze–Kannan) and hit-and-run sampler (KLS)).
- **The Fermat–Weber functional and its subgradient:**
  `Φ(c)=∫_{X_t}‖y−c‖_∞ = Φ_box(c) − ∫_{⋃cones}‖y−c‖_∞`, and the second term is
  poly-estimable by union-sampling; `∂Φ/∂c_i = μ(P_i^-∩X_t) − μ(P_i^+∩X_t)` where
  each `P_i^±∩C_k^r∩box` is **convex** ⟹ Karp–Luby gives the pyramid masses.

**So the balanced point is the minimizer of a convex `Φ` whose value and subgradient
are individually poly-time-estimable — yet this does NOT give a poly algorithm**,
because every needed quantity over `X_t` is a difference of two `O(1)` convex
quantities (over the box and over the cones) whose gap is `~2^{−t}`. Resolving a
`2^{−t}` difference by Karp–Luby (multiplicative `(1±ε)` on each `O(1)` term) needs
`ε < 2^{−t}` ⟹ `2^{t}` samples. **Exponential.** The exponential thinness of `X_t`
defeats every "compute on the convex ambient and subtract" method.

## 3. Why intrinsic (sample-within) methods all reduce to the same wall

- **Telescoping rejection:** sample `X_{t−1}`, keep the `½` in `K_t`. Acceptance `½`
  per step ⟹ `2^{−t}` overall (compounds). Needs replenishment = MCMC-within = mixing.
- **Sequential Monte Carlo:** `N` particles `~X_r`, filter to `X_{r+1}` (half survive),
  rejuvenate by an MCMC move within `X_{r+1}` — the rejuvenation is poly iff hit-and-run
  mixes on `X_{r+1}` = isoperimetry.
- **Hit-and-run directly:** along a line, each convex cone removes ≤1 interval, so
  `line ∩ X_t` = ≤`dt+1` sub-intervals; mixing = conductance = Cheeger of `X_t`.

All three need **poly mixing on `X_t`**, i.e. **Cheeger(`X_t`) ≥ 1/poly** — the open core.

## 4. The core, stated in its cleanest form

> **Open core (= poly-time SSG).** Does `X_t = box ∖ (union of dt convex cones)`, with
> the cones being reflected pyramids whose apexes `c^r` are balanced points of the
> nested `X_{r−1}`, have isoperimetric (Cheeger) constant `≥ 1/poly(d,t)` — equivalently,
> is it the union of only `poly`-many "sampleable" cells / does hit-and-run mix in poly?

Equivalent combinatorial form: `X_t` is a union of arrangement cells of `dt` cones;
the count of nonempty cells is worst-case `(d²t)^{Θ(d)}` (exp-in-d), but empirically
`O(1)` guard-classes on realizable trajectories (star_cover.md). The gap between
worst-case and realizable is the whole problem, and it lives — as everything in this
project does — on the **sign-pattern/strategy combinatorics** of the cut sequence.

## 5. Honest status

Genuinely new here: the exact "box minus `dt` convex cones" reformulation and the
**rigorous barrier** — the natural convex/Karp–Luby reduction is poly *per convex piece*
but needs `2^t`-precision because `X_t` is exponentially thin, so it cannot escape to a
poly algorithm. This unifies and sharpens the whole investigation: the difficulty is not
non-convexity per se (the pieces are convex and computable) but the **exponential
thinness of the intersection**, which forces intrinsic sampling, which forces
isoperimetry. No crack found; the core remains `SSG∈P`. The cleanest remaining target is
Cheeger of a box minus `dt` centrally-apexed convex cones — a concrete, self-contained
question in the isoperimetry of non-convex bodies with special (arrangement) structure.

## §6 The sign-count parameter σ, and the convex-cell lever (user's "nice subset" hint)

Two new results pushing on the core.

**(a) σ = # distinct sign vectors is the difficulty parameter, and it is poly.**
Measured on realizable SSG trajectories: the number of *distinct* sign vectors s^r is
FAR below 2^d and heavily repeats — d=4: 4–11, d=5: **2**–10, d=6: 7–10, d=8: 15 (vs
2^d=16/32/64/256). Trivially σ ≤ #rounds = O(d log 1/ε) = **poly**. And σ tightly controls
geometric difficulty (exact, no-sampling metric = fraction of cuts with x* in the cut's
kernel):

| σ | 2 | 4 | 6 | 9–11 |
|---|---|---|---|---|
| x*-in-kernel frac | 0.93 | 0.75–0.87 | 0.75 | 0.31–0.47 |

Small σ ⟺ near-star-shaped/well-conditioned; large σ ⟺ blind axes / κ-blowup. This
unifies the whole project's "difficulty = sign-pattern combinatorics" theme into a single
measurable, always-poly parameter.

**(b) The arrangement cell containing x* is a CONVEX subset of X_t (the CLY-style "nice
subset with a provable target").** Since the removed cones are bounded by the hyperplanes
{w_k^r + w_j^r = 0}, X_t is a union of cells of this hyperplane arrangement, and every cell
is convex (an intersection of halfspaces). x* lies in one cell `Y* ⊆ X_t`, convex, and
`x* ∈ Y*` is provable (cut validity). So — exactly in CLY's spirit of restricting to a
subset in which a target provably lives — `Y*` is a convex region we could sample in poly
time IF we could identify it. Identifying `Y*` = knowing x*'s signs against the O(d²t)
facet-hyperplanes; with σ poly, only poly-many distinct facet-orientations arise.

**Refined core conjecture (the sharpest target):**
> `Cheeger(X_t) ≥ 1/poly(σ, d)` (equivalently the guard/cell count is poly(σ,d)). Since
> `σ ≤ #rounds = poly`, this would give a poly-time sampler ⟹ SSG∈P.

Status: strong CORRELATION (σ↔difficulty, exact metric) but NOT a proof; and κ numbers at
this scale are light-sampler-inflated (unreliable), so only the σ↔x*-kernel-fraction link
is clean. The convex-cell lever is a genuine new algorithmic direction (track a convex
region containing x*) whose obstruction is identifying x*'s pyramid each round (= the
dominant-coordinate/Corollary-C problem, Θ(d) active set) — but the freedom to choose the
subset + poly σ may make a branch/prune or extra-query identification affordable. Not an
algorithm yet; the most promising open lead.

## §7 σ-verdict + dominant-coord ID (experiments run by main)

**σ-scaling verdict (fixed d=5, t=10, spread/max-Hamming signs — the stress test):**
star-cover k vs σ = 1→1, 2→1, 3→2–9, 5→6–8, 8→9–11; κ = 2–17. **k grows ~linearly
(sub-exponentially) in σ** (σ=8 gives k≈10, not 2⁸). σ=1 gives k=1 (matches the proof
X_t star about a known corner). Since k star-pieces ⟹ Karp–Luby poly sampler (NO mixing
needed), **k is the load-bearing quantity and it is poly in σ** — the most positive
structural signal of the project. (h_iso read 0.000 = known coarse-histogram artifact,
irrelevant since k, not Cheeger, is what the star-cover sampler needs.)

**Remaining gaps for SSG∈P via this route:** (A) is k = poly in **d** too? (the exp-in-d
worst case (d²t)^d vs empirical small k — the separate open scaling); (B) is the k-piece
cover poly-time constructible with each piece sampleable (nonempty kernel via virtual
constraints)?

**Dominant-coord ID (convex-cell's cell-tracking):** clean DICHOTOMY by instance —
easy: margin ~0.2, 1-query ID-rate 0.73–0.85, lock-M=1; hard: margin→0, ID-rate
0.05–0.36, lock-M grows 40→99 as 1/δ grows 1e2→1e4 (the value-iteration wall). So
SINGLE-pyramid cell-tracking ≡ core on hard instances — but the star-COVER route
(cover all k relevant cells, k~poly(σ)) sidesteps the "identify one pyramid" obstruction.
The two leads converge: **star-cover with k=poly is the route; identifying x*'s single
cell is unnecessary.**

## §8 d-scaling of k (gap A) — POLY (run by main)
Fixed small σ, vary d (t=2d, spread/stress signs, exact rejection, acceptance ~2^{−t} =
fat non-sliver bodies): star-cover k vs d = for σ=2: 1,1,1,1,1,2,1,1 (d=3..6); for σ=3:
1,1,2,1,4,3,3,4. **k stays ~σ and FLAT in d (3→6) — no blow-up**, κ small (3–13). Combined
with §7 (k ~ linear in σ): **k ≈ O(σ), polynomial in BOTH σ and d** across the whole
measurable window, even under adversarial spread signs. Since k star-pieces ⟹ Karp–Luby
poly sampler (no mixing), this is the strongest evidence for SSG∈P via the star-cover route.
Caveats: d≤6 exact-rejection ceiling (the (d²t)^d worst case lives at large d, unseen);
controlled-σ synthetic (spread=conservative). Remaining = PROOF k≤poly(σ,d) (sigma-scaling)
+ cover constructibility/sampleability (convex-cell). Empirics ≠ proof, but both gaps now poly.

## §9 GUARDS vs CELLS — the decisive disambiguation (run by main)

Measured the two counts on realizable SSG (t=2d, exact rejection):
- **Cell count k' (disjoint convex cells):** LARGE — k'_lb keeps growing with sample size
  (d=5: 148→293→466→716 at nsamp 200→2000; ratio→ stays high), d-trend ~exp
  (d=3:~50, d=6:~460+ /500 saturating). ⟹ the `(d²t)^d` worst case is REAL for cells.
- **Guard count k (star-cover, volume 99.9%):** SMALL, ~σ (1–11), flat in d (§7,§8).

Consistent: ONE guard sees across MANY cells. Decisive consequences:
1. **Cell-enumeration (convex_cell Part II) is NOT poly** — k' is exp. The route must be
   GUARD-based star-cover (k~σ), not cell-based.
2. **Approximate sampling (TV 1/poly, which suffices — weak centerpoint ⟹ poly rounds)
   needs only guards covering (1−1/poly) of the VOLUME = small k~σ, NOT all k' cells.**
3. **Guard-finding dodges the thinness barrier**: ray-shoot within star(z)⊆X_t (each ray
   exits at first cone hit — poly), never rejection-sample the thin X_t. So greedy guard
   selection (maximize new visible volume, all via ray-shot integrals + segment membership)
   is poly; Karp–Luby over the k OVERLAPPING star-pieces (each ray-shootable + measurable +
   membership-testable) gives an approx-uniform sampler in poly(k).

**⟹ The whole algorithm is poly IF the guard number k (to cover 1−1/poly volume) ≤ poly(σ,d).**
Candidate guards: the σ known corners ĉ_ℓ (sigma-scaling) + poly interior points. Empirics:
k~σ, poly in both axes (d≤6). THE crux, cleanest form: prove k_guard(X_t) ≤ poly(σ,d).
Everything else (construct cover, sample, balance, cut, recurse) is assembled and poly,
dodging BOTH the thinness and identification walls. Empirics ≠ proof; d≤6 ceiling remains.

## §10 Proof-mechanism validation (run by main) — supports k ≤ c·σ

sigma-scaling's theory: X_t = box ∩ F^{-1}(P), P convex, F a PL order-statistics map with
σ nonlinearity types; proof target k ≤ c·σ via "O(1) min-pockets per class". Three read-offs
(d=5,t=10 spread unless noted, exact rejection):
1. GUARDS: k=1,3,4,11 for σ=2,3,5,8 (~σ). Guards INTERIOR (not corners — corners ∉ X_t) but
   corner-DIRECTION aligned (align 0.95–0.97 small σ). ⟹ guards ≈ σ corner-directions.
2. MIN-TIE multiplicity (coords achieving the class-min): mean 1.06→1.13 as d:3→6, p90≈1,
   max 3–4 — **FLAT in d**. Direct mechanism for d-flatness: class-min hit by ~1 coord ⟹
   obstructions are 2-D not d-D ⟹ k independent of d. Strongest evidence for the d-flat conjecture.
3. NONEMPTY F-cells: 64,124,110,251 for σ=2,3,5,8 vs worst d^{2σ}=6e2,2e4,1e7,2e11 —
   realizability collapses cells ~9 orders at σ=8; grows mildly, not d^{2σ}.
All three support the k ≤ c·σ proof (min-pockets O(1), flat in d). Proof is now the sole gap.

## §11 The correction (convex-cell) + CC measurement — route survives

**convex-cell's correction (important, caught a real error):** the GUARD/star-cover route
is NOT automatically poly — star-pieces are NON-convex, and sampling them fails both ways:
ray-shoot radial volume is EXP-variance in d even for a cube (R^d spans d^{d/2}), and
hit-and-run on a non-convex star needs isoperimetry (KLS is convex-only). So k~σ guards is
necessary-not-sufficient; the operative quantity is the CONVEX-COVER number CC ∈ [k, k'],
because only CONVEX pieces are provably poly-samplable (KLS mixing + DFK volume).
[This retracts the earlier "ray-shoot the star pieces, poly" claim — it was wrong in high d.]

**CC measured (greedy convex cover, SSG t=2d, exact rejection):** CC ≈ σ, small (1–11),
flat-ish in d (d:3→5 at σ=2,3 gives CC=1,1,2 and 1,3,6). Between k (guards) and k' (cells,
exp), conservatively OVER-counted, and greedily CONSTRUCTED — so a small convex cover both
EXISTS and is findable in-window. ⟹ the route SURVIVES the correction empirically: the
operative CC is ~σ = poly.

**Lean:** `starshaped_of_single_sign` formalized (σ=1 ⟹ star about known corner), sorry-free.

Remaining gaps (both = the realizability wall, unmeasurable past d≈6): (i) PROVE CC ≤
poly(σ,d); (ii) PROVE a poly constructor — the inductive "intersect each convex piece with
the new cut" splits a piece into O(d) sub-pieces ⟹ ×O(d)/round = d^t unless splits don't
proliferate (the non-interacting-reflex-ridge / additive-not-multiplicative crux). Empirics
(CC~σ, greedy finds it) are positive but ≠ proof.

## §12 The DoubleBind lemma (decisive crux) — INCONCLUSIVE

sigma-scaling reduced k_guard ≤ σ (and, via the synthesis "≤1-binding region is convex",
also CC ≤ poly) to ONE lemma: vol(DoubleBind = {y binding ≥2 classes}) ≤ 1/poly, predicted
codim-2 (~Δ²), flat in d. Measured (exact rejection):
- CAVEAT found: margins are tiny (median 0.008–0.044), so absolute Δ=0.05 was a MIS-SCALED
  artifact (made ~everything bind). Redone with Δ relative to median margin.
- Margin-relative result (d=5, controlled σ): at Δ=0.1×med, DoubleBind THIN (0.02–0.08) and
  < single-bind (0.18–0.40) — supports codim-2. BUT grows fast with Δ and σ (σ=8:
  0.06→0.36→0.82 as Δ:0.1→0.5×med). Not the clean tiny-Δ² the proof needs; not refuted.
- Honest: the decisive lemma is Δ-scaling-sensitive and INCONCLUSIVE at d≤6/finite samples.
  Also the containment uncovered ⊆ DoubleBind is LOOSE (k~σ says uncovered IS small even
  though DoubleBind isn't tiny) — so a fat DoubleBind does NOT refute k~σ; it means
  sigma-scaling's specific proof route (bound uncovered via DoubleBind) is too loose.

NET: empirics (k~σ, CC~σ, greedy finds them) remain positive; but the PROOF route through
DoubleBind is not cleanly supported, and the decisive number is unmeasurable-clean at this
scale. Same realizability wall, now at the level of the single crux lemma.

## §13 Constructor: split is multiplicative, but fresh-greedy survives; two terminal gaps

- **sub-lemma 1 (deep⟹kernel) REFUTED:** deep-in-class ⟹ in-class-kernel fraction is
  0.05–0.29 (d=5), 0.000 (d=6) — because "max+min large" (deep) ≠ "two-smallest-sum ≥0"
  (kernel). So sigma-scaling's CC ≤ σd² decomposition via kernels does NOT hold; CC≤poly
  needs a different argument.
- **convex-cell's constructor advance (§16):** telescoping replenishment via a convex cover
  removes BOTH thinness (resample X_{t-1} through its cover, acceptance ½ not 2^{-t}) AND
  mixing (convex pieces, KLS) — the two walls that killed earlier samplers. Real.
- **straddle_t measured ≈ CC_{t-1}** (constant fraction of pieces straddle the next cut) ⟹
  the INDUCTIVE maintain-and-split constructor is MULTIPLICATIVE (CC_t ~ d·CC_{t-1} → d^t).
  So that variant dies. BUT the fresh-greedy re-cover of X_t each round still gets CC~σ
  (§11), so the working constructor is **telescope-sample + FRESH-greedy-cover** (not split).

**Terminal state of the route (honest):** complete poly algorithm =
telescope-sample X_t via X_{t-1}'s convex cover (½ acceptance) → fresh greedy convex cover
of X_t → Karp–Luby sample → balanced-point LP → cut → recurse. Poly IFF two bounds, BOTH
empirically true (~σ) but UNPROVEN, both = the realizability wall (= SSG∈P):
  (G1) CC(X_t) ≤ poly(σ,d)   [existence of a small convex cover; measured ~σ]
  (G2) fresh greedy achieves O(CC) on these bodies  [greedy convex cover is NP-hard in
       general / no approximation guarantee; empirically hits ~σ].
The clean-decomposition proofs (deep⟹kernel; DoubleBind-thin; inductive-additive) all
FAILED empirically; the existence CC~σ stands but its proof is exactly the SSG-hard
realizability question. Identification, thinness, and mixing walls are all genuinely removed;
the sole surviving wall is "a small convex cover exists AND is greedily constructible."

## §14 Explicit-guard construction REFUTED — only unguaranteed greedy survives

Measured MutualBlock (sigma-scaling's tightened uncovered characterization) with the explicit
near-corner guards g_ℓ=(1−η)ĉ_ℓ+η·p_0:
- MutualBlock == DoubleBind EXACTLY (0.033, 0.287, 0.267...) — the "tightening" gives nothing.
- Actual uncovered (0.43, 0.59) ≫ DoubleBind (0.03, 0.29) — CONTRADICTS the theorem
  uncovered ⊆ DoubleBind. Cause: near-corner guards are BAD (corners are marginal / on ∂X_t,
  so g_ℓ sees only 40–60% of X_t) — consistent with the deep⟹kernel refutation.
- Hamming: |B|=1 pairs contribute 0 (the one prediction that held).

So the EXPLICIT k_guard ≤ σ+1 construction (near-corner guards) is REFUTED. Yet GREEDY guards
cover 99% with ~σ pieces — a good ~σ cover EXISTS, just not this explicit one.

## Terminal synthesis of the whole star-cover / convex-cover route
Every EMPIRICAL quantity is small (k~σ, CC~σ, min-ties O(1), flat in d) ⟹ route looks poly.
Every EXPLICIT/PROVABLE construction or bound FAILED: σ-corners-cover (marginal),
deep⟹kernel (0.0 at d=6), DoubleBind-thin (Δ-sensitive/inconclusive), uncovered⊆DoubleBind
(contradicted, 43% uncovered), inductive-split-additive (multiplicative, straddle≈CC),
near-corner-guards (40–60% uncovered). Only UNGUARANTEED greedy achieves ~σ. So:
the small cover EXISTS empirically but has NO proven poly construction — exactly the
realizability wall = SSG∈P, and unmeasurable-clean past d≈6. The algorithm is fully
assembled (identification/thinness/mixing removed); the sole gap is "small convex cover
exists AND is poly-constructible," empirically true, provably open.

## §15 k_eff (mass concentration) REFUTED — the free constructor fails too

convex-cell's §19 free constructor (sample, group by assignment vector, no merging) is poly
iff k_eff = #cells holding 99% of MASS is poly. Measured: k_eff = 60 (d=4), 141 (d=5), 250
(d=6) at N=2000, STILL GROWING with N, and k_eff/k'_lb = 0.80–0.97 (k_eff ≈ k', not ≪). So
the MASS IS SPREAD over ~all cells, NOT concentrated in a poly head. The "rare tail vs
saturating head" hope is false — there is no small head. So sample-and-group yields ~k_eff
(large) pieces, not the small CC~σ.

RESOLUTION of the CC-vs-k_eff tension: CC~σ is small ONLY because greedy MERGES many
assignment-cells into few convex pieces (crossing interior non-reflex boundaries). The
merge-FREE constructor (k_eff) gives the large un-merged count. So:
- small convex cover EXISTS (CC~σ) — but only via merging = NP-hard / greedy-unguaranteed;
- merge-free construction (k_eff) is poly but LARGE (mass genuinely spread).
Both constructive paths fail. This DOUBLY confirms the terminal wall: no proven poly
constructor of a small cover, from either direction.

## FINAL terminal assessment (this route)
The convex-cover / telescoping algorithm is assembled and removes identification, thinness,
and mixing. It is poly iff a small convex cover is poly-CONSTRUCTIBLE. Empirically the cover
EXISTS small (CC~σ), but: greedy-merge to reach it is NP-hard/unguaranteed, and merge-free
sample-and-group gives a large count (k_eff≈k', mass spread). Every explicit construction and
every clean bound (corners, deep⟹kernel, DoubleBind, MutualBlock, inductive-split, k_eff)
has been REFUTED empirically; only unguaranteed greedy attains ~σ. The existence-vs-poly-
construction gap IS the realizability core = SSG∈P, unmeasurable-clean past d≈6. This is the
honest terminal state of the deepest route.
