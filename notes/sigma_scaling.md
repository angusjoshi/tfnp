# σ-scaling: does the difficulty of X_t grow poly or exp in σ?

**Question (the crux).** σ = number of *distinct sign vectors* `s^r` used by the cut
trajectory. Measured σ is always ≤ #rounds = poly, and empirically small (2–15). If the
geometric difficulty of `X_t` is `poly(σ,d)` then (since σ ≤ #rounds = poly) hit-and-run /
star-cover sampling is poly ⟹ **SSG ∈ P**. If it is `2^{Ω(σ)}` the lead is dead in the
hard regime. This note gives (1) a rigorous structural reduction, (2) a **proved** σ=1
result, (3) the sharp σ≥2 open question and what is known/conjectured, (4) task-3 analysis
of σ vs #rounds, (5) the decisive experiment spec sent to `main`.

Honesty ledger: §1–§3 are **proved** (elementary, machine-checkable). §4–§5 are
conjecture/experiment. Nothing here closes SSG∈P.

---

## 1. Structural reduction (PROVED): X_t = intersection of exactly σ monotone up-sets

Recall (MEM) the kept half of cut `r` is `K_r = {y : max_i w_i^r + min_i w_i^r ≥ 0}`,
`w_i^r = s_i^r(y_i − c_i^r)`, and the removed half `N_r = {max+min < 0}`. Fold coordinates
by the orthant reflection `u = T_s(y)`, `u_i = s_i y_i` (an isometry). Then
`w_i^r = u_i − a_i^r` with `a_i^r = s_i^r c_i^r`, so in folded coordinates

> `K_r = { u : max_i(u_i − a^r_i) + min_i(u_i − a^r_i) ≥ 0 }`.

**Monotonicity.** `f(u) = max_i(u_i−a_i) + min_i(u_i−a_i)` is coordinatewise
non-decreasing (both max and min weakly increase when any `u_i` increases). Hence:

* each **kept** set `K_r` is an **up-set** (up-closed) in the orientation `s^r`;
* each **removed** set `N_r = {f < 0}` is a **down-set** in that orientation.

Group the `t` cuts into their σ orientation classes. The removed sets within a class share
one orientation, so their union is again a down-set:
`D_ℓ := ⋃_{r∈class ℓ} N_r` is a down-set (orientation `s^{(ℓ)}`). Therefore

> **`X_t = box ∖ ⋃_{r} N_r = ⋂_{ℓ=1}^{σ} U_ℓ`, where `U_ℓ = box ∖ D_ℓ` is a
> corner-monotone up-set (up-closed in orientation `s^{(ℓ)}`).**

This is strictly sharper than "box minus `dt` convex cones" (core_analysis §1): the `dt`
cones **collapse into exactly σ monotone bodies**, one per orientation class. It is the
clean formal statement that **σ, not `dt`, is the complexity parameter of the geometry**.
The whole σ-question becomes:

> **Core σ-question.** What is the star-cover `k` / Cheeger `h` of an intersection of σ
> corner-monotone up-sets in `[0,1]^d`? Is `k ≤ poly(σ,d)` (⟹ SSG∈P via Karp–Luby) or
> `2^{Ω(σ)}` (dumbbell/lobe blow-up)?

---

## 2. σ = 1 (PROVED): X_t is star-shaped about a box corner ⟹ poly-time, no isoperimetry

If all cuts share one sign vector `s`, then `X_t = U_1`, a single up-set. Let
`ĉ_s ∈ {0,1}^d` be the corner with `(ĉ_s)_i = 1` if `s_i=+1`, else `0` (the max corner of
the folded box).

**Claim.** `X_t` is star-shaped about `ĉ_s`.

*Proof.* (i) `ĉ_s ∈ K_r` for every cut: `w_i^r(ĉ_s) = s_i((ĉ_s)_i − c_i^r) = 1−c_i^r ≥ 0`
if `s_i=+1`, and `= c_i^r ≥ 0` if `s_i=−1` (apexes `c^r ∈` box); so all `w_i ≥ 0`, hence
`max+min ≥ 0`. (ii) For any `y ∈ X_t`, the segment `[y, ĉ_s]` in folded coordinates only
*increases* each coordinate toward the max corner `u* = T_s(ĉ_s)`; since each `K_r` is
up-closed, the whole segment stays in every `K_r`, and in the (convex) box. ∎

Consequences:

* **σ=1 ⟹ exact ray-shooting sampler from `ĉ_s`** (Thin-Partitions / star-shaped sampling,
  Chandrasekaran–Dadush–Vempala arXiv:0904.0583) ⟹ **poly-time, isoperimetry-free.**
* The star center is a **known box corner** — no need to *find* it, unlike the general
  kernel route (C3). This is a strict strengthening of Theorem A (which needed cuts to
  point toward `x*`): here **no condition on `x*` is required at all**.
* Consistent with star-cover's `k=1` in-window finding and with "small σ ⟺ well-conditioned."

This is the cleanest positive result of the σ program and it is airtight and cheap to
machine-check (worth a Lean lemma: `starshaped_of_single_sign`, a corollary of the existing
`starshaped_of_kernel` family in `Tfnp/HitRun.lean`).

---

## 3. σ ≥ 2: the sharp open question, and what is known

For σ ≥ 2 the intersection `⋂_ℓ U_ℓ` mixes **different orientations**. The classical tool
for monotone sets — **FKG / the recent monotone-hypercube spectral-gap bound**
(arXiv:2505.02685) — applies only to up-sets in a **common** orientation (their intersection
is again an up-set, still `k=1`). **Different orientations is exactly the regime FKG does not
cover**, and is the entire σ-difficulty. So σ, precisely, counts the number of
FKG-incompatible orientation classes.

**Partial facts (proved / elementary):**

* **`d ≤ 2`: convex for all σ.** In 2-D `max+min = sum`, so every `K_r` is a halfspace and
  `X_t` is a polytope — poly for any σ. σ-difficulty needs `d ≥ 3`.
* **Agreement coordinates factor out.** If all σ orientations agree on a coordinate set
  `A`, all classes are up-closed on `A`; the geometry on `A` is monotone (star) and the
  interaction lives only on the **disagreement coordinates** `B = [d]∖A`. Effective
  difficulty dimension = spread of the σ corners, not `d` per se. (⟹ difficulty should be
  measured against *both* σ and the Hamming spread of `{ĉ_ℓ}`.)
* **σ=2, realizability vs sliver.** Two opposite centered cuts give
  `X = {φ ≥ −2η} ∩ {φ ≤ 2η}`, `φ(y)=max(y−½)+min(y−½)` — a slab `{|φ| ≤ 2η}` of width
  `~η` around a saddle surface. At `η→0` (exactly-opposite balanced cuts) it degenerates to
  the measure-zero sliver `{φ=0}`; **balancedness forbids exactly-opposite centers, forcing
  `η>0`**. So the σ-level obstruction is the *same* sliver-vs-realizable dichotomy found in
  isoperimetry_summary §3: the cheap 2^σ counterexamples are non-realizable slivers. Whether
  the *positive-width* saddle-band is a dumbbell (bad `h`) or fat (good `h`) is the crux —
  **exactly what the experiment must decide.**

**Why a single class cannot create a bottleneck (intuition for a poly bound).** One class
removes one down-set `D_ℓ` = one "corner bite" (half the box for the first cut); the
remainder `U_ℓ` is star-shaped (§2), so a single class *never* splits the body. A bottleneck
requires ≥2 classes whose bites face different corners and pinch a neck between them. This is
why difficulty is `0` at σ=1 and the question is how fast it can grow.

**The exp-in-σ obstruction to hunt for.** A realizable trajectory whose `X_t` is a
`2^{Ω(σ)}`-lobe body: σ classes each contributing an *independent* pinch (a binary
choice) so the lobes multiply. The candidate is σ classes toward "spread" corners
(pairwise-far in Hamming distance) creating independent saddle-bands whose intersection has
exponentially many pockets — the star-cover FINAL_REPORT's `(d²t)^{d−1}` arrangement blow-up,
but re-indexed by σ. If realizable bodies **cap the pairwise-independence** of the pinches
(e.g. balancedness couples them), difficulty stays poly(σ). This is the decisive unknown.

---

## 4. Task 3: is σ provably smaller than #rounds in the hard regime?

σ ≤ #rounds trivially, and #rounds = `O(d log(1/ε))` = poly. Is there a *better* bound?

* **No obvious sub-poly bound.** `s^r` is the sign pattern of the SSG/topical improvement
  at center `c^r` (which coordinate-direction each strategy wants to move). As `c^r → x*`,
  the residual `f(c^r)−c^r` can point in many directions, so a-priori σ can be `Θ(#rounds)`.
* **The measurable dichotomy that matters:** does σ **saturate** (plateau at a constant as
  `t` grows) or grow **linearly** with `t`?
  * σ plateaus at `O(1)` ⟹ difficulty `poly(O(1))` = trivially easy (huge).
  * σ ~ `c·t` (constant fraction) ⟹ σ = poly, and poly-vs-exp-in-σ is still decisive.
  This is directly measurable (σ(t) curve) and is part of the experiment.
* **Structural hope (unproved):** near `x*` the *relevant* sign patterns are those of the
  finitely many optimal-strategy-pair boundaries active around `x*`; if only `poly` strategy
  pairs are ever active (value-space, ssg_directions framing) then σ = poly independent of ε.
  This is the "combinatorial transfer object" flagged in condition_transfer.md — the right
  invariant is the **strategy/sign trajectory**, not ε or δ.

Net: σ is provably poly (≤#rounds) but not obviously `o(#rounds)`; the plateau-vs-linear
behaviour is an empirical question folded into the experiment.

---

## 5. DECISIVE experiment (spec sent to `main`)

**Goal:** measure reliable (exact-rejection ground-truth) star-cover `k`, isotropic Cheeger
`h_iso`, and condition number `κ` of `X_t` **as a function of σ, with d and t held fixed**,
to read off poly(σ) vs exp(σ). Holding `d` fixed removes the exp-in-`d` arrangement
confound; holding `t` fixed removes the `2^{−t}` thinness confound; so any growth is
attributable to σ.

**Design B (decisive — controlled σ).** Build synthetic *geometry-realizable* trajectories
with a **prescribed** number σ of distinct sign vectors:
1. Fix `d ∈ {5,6}`, `t = 2d`.
2. Choose σ sign vectors `s^{(1)},…,s^{(σ)} ∈ {±1}^d`. Two selection modes:
   (a) **spread** — pairwise Hamming distance maximized (the stress test for exp blow-up);
   (b) **random** distinct signs (baseline).
3. Generate `t` cuts by cycling through the σ signs (⌈t/σ⌉ each). Each cut's apex `c^r` =
   **exact balanced (Fermat–Weber) center** of the current `X_{r-1}` from an exact-rejection
   sample (keeps bodies non-sliver, volume `~2^{−t}`, in the realizable geometric family).
4. Sweep `σ ∈ {1,2,3,5,8,2d}`; seeds `= 4` each.

**Design A (natural — SSG-realizable correlation).** Run real SSG + topical instances at
fixed `d=5,6`, `t=2d`; measure the *emergent* σ per instance; bin difficulty by σ. Also
record `σ(t)` to test §4 plateau-vs-linear. This checks that Design-B synthetic signs are not
an artifact and that the σ↔difficulty law holds on genuinely realizable bodies.

**Metrics per (d,t,σ,mode,seed), all from exact rejection (N ≤ 400/round):**
* `vol` (acceptance rate) — confirm not collapsed to a sliver (`vol ≳ 2^{−t}`, not `η^σ`).
* `k` = star-cover (calibrated `star_cover.py`, coverage target 0.999, nseg=120).
* `h_iso` = isotropic Cheeger (whiten by `Σ`, min-conductance over sampled cuts).
* `κ` = `λmax/λmin` of fresh-sample covariance.
* kernel nonempty? (true-kernel visibility) — ties to §2/§3.

**Reliability guards (from prior cycles):** exact rejection only (no Markov-chain confound);
isotropic (whitened) `h` to avoid flagging elongation; report `vol`/acceptance so
under-sampled deep-`t` bodies are quarantined; keep per-round draws ≤ 3M (⟹ prefer
`d=5,t=10` primary, `d=6,t=12` only if acceptance stays healthy).

**Verdict test.** At fixed `(d,t)`, regress `log k`, `log(1/h_iso)`, `log κ` on σ:
* **slope > 0 in σ (linear in σ) ⟹ EXPONENTIAL in σ ⟹ lead dead** (σ not small enough in
  the hard regime to save it).
* **flat, or linear in `log σ` (poly) ⟹ POLYNOMIAL ⟹ SSG∈P route alive.**
Cross-check against Hamming spread (spread vs random modes): if only *spread* corners blow
up, difficulty is governed by corner-geometry, and realizability's control of spread becomes
the remaining gap.

---

## 6. Verdict (current)

* **PROVED:** σ=1 ⟹ star-shaped about a known box corner ⟹ poly, isoperimetry-free (§2);
  and `X_t = ⋂_{ℓ=1}^σ` corner-monotone up-sets (§1). These make σ *the* parameter, rigorously.
* **OPEN (the crux):** poly(σ,d) vs 2^{Ω(σ)} star-cover/Cheeger of an intersection of σ
  monotone up-sets in ≥2 orientations. FKG covers only σ=1 (one orientation). The cheap
  2^σ counterexamples are non-realizable slivers; realizable width is forced positive — so
  the question is genuinely about the *fat* intersection and must be decided empirically
  (§5) before any proof attempt.
* **Task 3:** σ ≤ #rounds = poly, no proven better bound; plateau-vs-linear is measurable.

**Headline:** the geometry provably reduces to σ monotone bodies and is *free* at σ=1;
whether it stays poly through σ≥2 is the single remaining decidable question, and the §5
experiment is built to answer it under the strict compute caps.

---

## 7. After the experiment: k ~ linear in σ (verdict POLY). Toward k ≤ poly(σ,d)

**Experiment verdict (main, d=5, t=10, SPREAD/max-Hamming = stress test):** star-cover
`k` grows **sub-exponentially, ~linearly** in σ: `σ=1→k=1`, `2→1`, `3→2–9`, `5→6–8`,
`8→9–11`; `κ=2–17`. (`h_iso` read 0 = coarse-histogram artifact, IGNORE — `k` is
load-bearing: `k` star-pieces ⟹ Karp–Luby poly sampler, no mixing needed.) So difficulty
is **POLY in σ**, matching §2 (`σ=1⟹k=1`). Below: what this now lets us prove, the sharp
remaining gap, and the reframing that σ is *not* the true enemy.

### 7.1 (PROVED) Orthogonal structure: ≤ σ+1 intervals per axis line

Each removed down-set `D_ℓ` is **orthogonally convex**: fix all coordinates but `u_j`;
`f_ℓ(u)=max_i(u_i−a_i)+min_i(u_i−a_i)` is non-decreasing in `u_j`, so
`D_ℓ = {f_ℓ<0}` meets the line in a single (down-)interval, and the within-class union
stays one interval (same orientation). Hence any **axis-parallel** line meets
`X_t = box ∖ ⋃_{ℓ} D_ℓ` in **≤ σ+1 sub-intervals** (box interval minus σ removed
intervals). This is far stronger than the generic "≤ `dt`+1 pieces per line" and is the
exact object a **coordinate/Gibbs hit-and-run** needs: resampling one coordinate draws
from ≤ σ+1 intervals, each computable in poly time. (A promising secondary route the
σ-structure *enables*: mixing of coordinate-HAR on an orthogonally-convex-complement body
with ≤ σ intervals per line — not pursued here, flagged.)

### 7.2 (PROVED) The centered case: X_t is a CONE ⟹ star-shaped for ALL σ

**Key reframing.** Suppose all cuts share a common apex `c*` (all `c^r = c*`). Then each
`K_r = {y : max_i w_i + min_i w_i ≥ 0}` with `w = ε^r∘(y−c*)` is **positively homogeneous**
in `(y−c*)`: `K_r = c* + cone`. An intersection of cones with a common apex is a cone about
`c*`, hence **star-shaped about `c*` — regardless of σ.** So `k=1` for any number of
orientation classes *when the apexes coincide*.

**Consequence: σ is not the true driver of `k`; the APEX SPREAD is.** Star-cover grows only
because the balanced apexes `c^r` are *offset* from each other; with zero offset, arbitrarily
many orientations cost nothing. This explains why `k` stays small: balanced centers `c^r` are
Fermat–Weber centers of the *nested, shrinking* bodies `X_{r−1}`, so `c^r → x*` — the apex
spread **contracts** over rounds. Late cuts are near-common-apex (≈ `x*`), and only the few
early cuts on the large body are meaningfully offset.

This also reconciles with the experiment: at fixed `t` the SPREAD-sign runs increase `k`
with σ because more orientations *amplify* a fixed apex offset into more reflex features —
the growth is in the **(σ × apex-spread) interaction**, not σ alone. The right composite
difficulty parameter is therefore `(σ, apex-spread)`, and the proof target sharpens to:

> **Sharpened proof target.** Bound `k(X_t)` as a *perturbation of the common-apex cone*:
> `k ≤ 1 + F(σ, spread, d)` with `F` poly. Base case (spread 0) `k=1` is proved (§7.2);
> the claim is that offsetting apexes by `spread` adds only poly-many reflex features that
> a poly-size guard set covers.

### 7.3 (PARTIAL) σ=2 is star-shaped in the homogeneous/symmetric case

For σ=2 with a common center (WLOG `½1`), `X = {|max(y−½)+min(y−½)| ≤ c}` is a cone about
`½1` (φ homogeneous), hence star-shaped — the direct reason the experiment shows `σ=2⟹k=1`.
General offset σ=2 (star-shaped or `k`=O(1)) is consistent with the data but **not yet
proved**; it is the cleanest next lemma (2 up-sets, one offset).

### 7.4 The honest gap for k ≤ poly(σ,d)

The order-theoretic sufficient condition "`g ⪰_ℓ y` in every class ℓ" (which would make `g`
a guard) is **too weak**: on coordinates where the σ orientations disagree it forces
`g_i=y_i`, so no finite guard set covers via monotonicity alone. A real bound **must use the
staircase geometry** (segments stay in `U_ℓ` above its boundary without being monotone —
exactly the σ=2 cone phenomenon). So `k ≤ poly(σ,d)` does not follow from order theory; the
promising handle is the §7.2 perturbation-of-a-cone picture. **Status: conjectured
`k ≤ poly(σ,d)`, strongly supported empirically (linear in σ at d=5), proved at spread=0 for
all σ and at σ=1 for all spread; the (σ×spread) interaction and the d-scaling are open.**

### 7.5 d-scaling (task 2): the separate open axis

The empirics fix `d=5`. Worst-case guard count is `(d²t)^{d−1}` (exp-in-d, FINAL_REPORT), so
`k` poly-in-`d` at fixed σ is **not** automatic and must be measured. Experiment spec (sent
to main): fix σ∈{2,3}, vary `d=3..6`, exact rejection, measure `k` vs `d` (and vs
apex-spread, to test §7.2). Flat/poly ⟹ route closes with task 1; exp-in-d ⟹ the realizable
apex-contraction of §7.2 is what must be invoked to avoid the worst case.

### 7.6 Lean lemma (task 3): exact statement for σ=1

The σ=1 result is a direct corollary of the existing `starshaped_of_kernel_family`
(`Tfnp/HitRun.lean`), whose hypothesis is a common center `z` with all `w_i(z) ≥ 0`. Feeder
fact: the corner `ĉ_s` satisfies, for every cut `r` of the single-sign family and every `i`,
`s_i·((ĉ_s)_i − c^r_i) ≥ 0` — because `s_i=+1 ⟹ (ĉ_s)_i=1 ≥ c^r_i`, and
`s_i=−1 ⟹ (ĉ_s)_i=0` so `s_i(0−c^r_i)=c^r_i ≥ 0` (apexes in the box). So `z=ĉ_s` meets the
kernel hypothesis. Statement to bank:

```
theorem starshaped_of_single_sign
    (s : Fin d → ℝ) (hs : ∀ i, s i = 1 ∨ s i = -1)
    (ĉ : Fin d → ℝ) (hĉ : ∀ i, ĉ i = if s i = 1 then 1 else 0)
    (apexes : ι → (Fin d → ℝ)) (hbox : ∀ r i, apexes r i ∈ Set.Icc (0:ℝ) 1) :
    StarShapedAbout ((box d) ∩ ⋂ r, K (apexes r) s) ĉ
```
Proof: apply `starshaped_of_kernel_family` with `z := ĉ`; discharge its per-cut, per-coord
nonneg hypothesis by the feeder fact (case split on `s i`). No new geometry needed.

### 7.7 Verdict (updated)

* **PROVED:** `X_t = ⋂_{ℓ=1}^σ` monotone up-sets (§1); `σ=1 ⟹ k=1` (§2, Lean-ready §7.6);
  **≤ σ+1 intervals per axis line** (§7.1); **common-apex ⟹ cone ⟹ k=1 for all σ** (§7.2);
  symmetric σ=2 ⟹ k=1 (§7.3).
* **EMPIRICAL:** `k` ~ linear in σ at d=5 (POLY, not exp) ⟹ route alive.
* **OPEN (the two axes to close SSG∈P via this route):** (i) `k ≤ poly(σ,d)` — reframed as
  perturbation of the common-apex cone by apex-spread (§7.2/7.4); (ii) `k` poly-in-`d` at
  fixed σ (§7.5 experiment). The deep reframing: **σ is harmless at zero apex-spread; the
  real difficulty variable is the (σ × apex-spread) interaction, which the *balanced,
  shrinking* trajectory keeps small by contracting apexes toward `x*`.**

---

## 8. Toward k ≤ poly(σ,d): the order-statistics preimage picture (d-flatness explained)

Both empirical gaps are POLY: k ~ linear in σ (§7), and (d-scaling, main) **k stays flat in
d** (σ=2⟹k=1 all d; σ=3⟹k=1–4, ~flat). So k ≈ O(σ), poly in both, even for stress signs.
The proof must now explain **why k is essentially d-independent.** The mechanism:

### 8.1 (PROVED) X_t is the preimage of a CONVEX polyhedron under a PL order-statistics map

Membership in each kept set depends on the point **only through two order statistics**:
`K_r = {y : M_r(y) + m_r(y) ≥ 0}` with `M_r(y)=max_i w_i^r`, `m_r(y)=min_i w_i^r`,
`w_i^r=ε^{(ℓ)}_i(y_i−a^r_i)` (ℓ = class of cut r). Define the map

> `F : ℝ^d → ℝ^{2t}`, `F(y) = (M_r(y), m_r(y))_{r=1..t}`, and
> `P = { (M_r,m_r) : M_r + m_r ≥ 0 ∀ r } ⊂ ℝ^{2t}` — an intersection of `t` halfspaces,
> **convex**. Then **`X_t = box ∩ F^{-1}(P)`.**

**All non-convexity of `X_t` is pushed into the map `F`, none into the target `P`.** And `F`
uses only **σ distinct folding orientations** `ε^{(ℓ)}` — within a class the apexes `a^r` are
mere translations that shift `F` but add no new nonlinearity type. So the PL nonlinearity of
`F` has exactly σ "types." This is the structural core: **σ counts the nonlinearity types of
the order-statistics map whose convex preimage is `X_t`.**

### 8.2 Why this forces near-d-independence (the mechanism, matching flat-in-d)

Along any segment `z(s)=(1−s)y + s·p`, each `w_i^r(z(s))` is **linear in s**, so
`M_r(z(s))=max_i(linear)` is **convex in s** and `m_r(z(s))=min_i(linear)` is **concave in
s**. Hence `F_r(z(s)) = M_r+m_r = convex + concave`:
* If `F` were linear (single argmax/argmin regime throughout the segment), the segment maps
  into the convex `P` automatically ⟹ **any center is a guard ⟹ k=1**. This is exactly the
  **common-apex cone** case (§7.2): one argmax/argmin regime governs, no d-dependence.
* Non-convexity of `X_t` arises **only** where the concave part `m_r` (the min order
  statistic) dips below `−M_r`: the visibility obstruction is a **2-dimensional (M_r, m_r)
  event per cut**, not a d-dimensional one. So the *kinds* of obstruction are governed by σ
  (orientation types); the ambient `d` only sets how many coordinates can *tie* for the min —
  which balanced apexes keep from proliferating. This is the precise reason the data is **flat
  in d**: obstructions live in the σ two-dimensional sketches, not in `ℝ^d`.

### 8.3 (PROVED) The k=1 criterion, and what the guards really are

`k=1 ⟺ ⋂_r ker(K_r) ≠ ∅` (star about any common kernel point; = Theorem A /
`starshaped_of_kernel`). Common-apex ⟹ the apex is in every kernel ⟹ k=1 (§7.2). So k>1
exactly when the σ kernels have empty common intersection. **The corners `ĉ_ℓ` are NOT the
guards** (proved): `ĉ_ℓ` is the extreme point toward class ℓ and generically lies in the
*removed* cone of an opposing class (`g_{ℓ'}(ĉ_ℓ)<0`), so `ĉ_ℓ ∉ X_t`. The true guards are
**interior points pulled in from the corner directions** — consistent with k≈σ but ruling out
the literal "the σ corners cover" hypothesis.

### 8.4 The honest remaining gap and the sharpest attackable target

* **Worst-case caveat.** `X_t` is the union of the linearity cells of `F` clipped to the
  convex `P`; the cell count is `≤ d^{2σ}` (poly-in-d for fixed σ, but exp-in-σ) and the
  generic arrangement bound is `(d²t)^{d-1}` (exp-in-d). So **`k ≤ poly(σ,d)` is likely FALSE
  in the worst case**; the empirical poly(σ,d) with d-flatness is a **realizability**
  phenomenon (balanced apexes keep min-ties and nonempty cells from proliferating — §7.2 apex
  contraction + §8.2 2-D sketch).
* **Sharpest target (what a proof must show).** Reduce k to the **σ two-dimensional
  (M_ℓ,m_ℓ) obstructions** and show each contributes O(1) guards under balanced apexes:
  > **Conjecture (d-flat star-cover).** For balanced (Fermat–Weber) apexes, `k(X_t) ≤ c·σ`
  > with `c` absolute (independent of d). Equivalently: the concave dip of the class-ℓ min
  > order statistic along a guard ray creates ≤ O(1) blocked pockets, because balancedness
  > prevents many coordinates from simultaneously tying for the class-ℓ minimum.
  This is the same realizability wall as the rest of the project, but **localized to a crisp
  2-D statement per class** (min-order-statistic ties under balanced cuts) rather than a
  d-dimensional arrangement — the most tractable form the wall has taken.

### 8.5 σ plateau in t (task, restated)

No proof that σ plateaus. The preimage picture sharpens it: σ = number of distinct folding
orientations = distinct cut sign vectors. Near `x*` the sign vector is the orthant of the
improvement residual; whether these orthants saturate to O(1) or keep appearing is exactly
the "strategy/sign trajectory" combinatorial object (ssg_directions). Measurable via σ(t);
not provably below #rounds.

### 8.6 Verdict (updated)

* **PROVED (worst-case, all σ,d):** `X_t = box ∩ F^{-1}(P)`, P convex, F a PL order-statistics
  map with σ nonlinearity types (§8.1); k=1 ⟺ common kernel nonempty & common-apex ⟹ k=1
  (§8.3); corners are NOT the guards (§8.3); ≤ σ+1 intervals per axis line (§7.1).
* **EMPIRICAL:** k ≈ O(σ), **flat in d** — poly in both axes across the whole window.
* **OPEN (the theorem to close SSG∈P):** `k ≤ c·σ` (d-flat), reduced to the crisp 2-D
  conjecture that each orientation class's min order statistic creates O(1) blocked pockets
  under balanced apexes (§8.4). This is the realizability wall in its most localized,
  2-dimensional form.

---

## 9. Retarget: GUARD number k_guard (not cell count). Toward k_guard ≤ poly(σ,d)

**Disambiguation (main).** The **cell** count k' is large/exp (d=5: 148→716 growing with
nsamp; saturating by d=6) — the intersection of σ up-sets genuinely has exp-many convex
cells. But the **guard/volume star-cover** k_guard (min guards whose visible stars cover
`1−1/poly` of `vol(X_t)`) is SMALL (~σ, flat in d). One guard sees many cells. The poly
sampler needs **k_guard**, not cells (Karp–Luby over k_guard ray-shootable star-pieces +
approximate sampling suffices). Also: the common-apex `k=1` cone (§7.2) is **non-realizable**
(forcing coincident apexes collapses volume — main measured); so it is retained only as
intuition, NOT as a base case. The realizable theorem is **k_guard ≤ poly(σ,d)**.

### 9.1 Correct object and the corner-marginality fact

`X_t = ⋂_{ℓ=1}^σ U_ℓ`, each `U_ℓ` star about the KNOWN corner `ĉ_ℓ`, and the removed
`D_ℓ = box∖U_ℓ` is a "corner bite" — a union of convex cones with apexes `a^r` (r∈ℓ) opening
toward the **anti-corner** `−ĉ_ℓ`. Whether the corner itself lies in `X_t`:
`g_{ℓ'}(ĉ_ℓ) = (max over ℓ,ℓ'-agreement coords, ≥0) + (min over disagreement coords, ≤0)`,
and for balanced apexes `a≈½` this is `≈ +½ + (−½) = 0` — **the corners are MARGINAL (on
`∂X_t`)**, tipping just in/out with the apex offset toward `x*`. So the guards are
**near-corner interior points** `g_ℓ = (1−η)ĉ_ℓ + η·p_0` (η small, `p_0` a deep center), not
the corners themselves. This is fully consistent with k_guard ≈ σ and refines the lead's
"σ corners cover" into "**σ near-corner interior guards cover `1−1/poly` of the volume**."

### 9.2 (PROVED) Shadow reduction: k_guard ≤ 1 + Σ_ℓ (guards to clear D_ℓ's shadow)

Take a central guard `p_0 ∈ X_t` (e.g. FW center). A point `y∈X_t` is *uncovered by `p_0`*
iff `[p_0,y] ⊄ X_t` iff `[p_0,y]` enters some removed bite `D_ℓ`. Hence

> **`Uncovered(p_0) ⊆ ⋃_{ℓ=1}^σ Sh_ℓ`,** where `Sh_ℓ = {y∈X_t : [p_0,y] ∩ D_ℓ ≠ ∅}` is the
> **shadow** of bite `D_ℓ` from `p_0`. Therefore
> **`k_guard(X_t) ≤ 1 + Σ_{ℓ=1}^σ k_guard(Sh_ℓ)`.**

So it suffices to clear each of the **σ** shadows. This is the rigorous form of "one guard
per orientation class," and it makes the target additive in σ. Two ways each shadow closes:

* **(Thin shadow)** `vol(Sh_ℓ ∩ X_t) ≤ (1/poly)·vol(X_t)`: then `p_0` alone already covers
  `1−σ/poly` volume ⟹ **k_guard = 1** for the volume version, up to a `1/poly` tail. The
  geometry supports this: `D_ℓ` is a bite toward `−ĉ_ℓ`, so its shadow within `X_t` (which
  excludes `D_ℓ`) is a **thin rind hugging `∂D_ℓ`**, not a bulk region — its width is set by
  the apex offset, and `X_t` has been thinned there already.
* **(Corner-cleared shadow)** each `Sh_ℓ` is star-visible from `g_ℓ` (near-corner): moving
  toward `ĉ_ℓ` **monotonically increases every `w_i^ℓ`**, so `g_ℓ` sees all of `Sh_ℓ`
  *through class ℓ* (that constraint can never re-block). Then `k_guard ≤ 1 + σ`.

### 9.3 The precise remaining gap

For the **corner-cleared** route, the one unproved step is that `g_ℓ` (which clears class ℓ)
does not itself violate **another** class `ℓ'` along `[g_ℓ, y]`: moving toward `ĉ_ℓ`
*decreases* `w_i^{ℓ'}` on ℓ↔ℓ' disagreement coords, so `m_{ℓ'}` (min statistic) can dip and
`g_{ℓ'}` fall below 0. This is exactly the §8.2 concave-min-dip, now on the *guard* ray. So
the corner-cleared bound needs: **the dip of `m_{ℓ'}` along `[g_ℓ,y]` is dominated by
`M_{ℓ'}` for all but a `1/poly` tail of `y`** — a 2-D (max/min) statement per class pair,
matching §8.4. For the **thin-shadow** route, the gap is bounding `vol(Sh_ℓ∩X_t)` — a direct
volume estimate that avoids pointwise visibility entirely and is the cleaner target.

**Status:** the reduction `k_guard ≤ 1 + Σ_ℓ k_guard(Sh_ℓ)` is PROVED (§9.2); each shadow
closes if either thin (volume bound) or corner-cleared (2-D dip bound); both are `1/poly`-tail
statements per orientation class ⟹ if either holds, **k_guard ≤ 1+σ (volume) or ≤ 1/poly
tail ⟹ SSG∈P.** Not yet proved; but the target is now additive-in-σ and per-class 2-D.

### 9.4 DECISIVE experiment (theorem-in-empirical-form) — spec to main

Directly test the two closable forms with a FIXED, explicit guard set (no greedy art-gallery):
1. Guards `G = {p_0} ∪ {g_ℓ = (1−η)ĉ_ℓ + η·p_0 : ℓ=1..σ}` (η∈{0.05,0.1,0.2}), `p_0` = FW
   center. Measure **fraction of vol(X_t) covered** by `⋃_{g∈G} star(g)` (a point y is
   covered if `[g,y]⊆X_t` for some g; estimate by exact-rejection sample + segment check).
   PREDICT: coverage `≥ 1−1/poly` with just these `σ+1` guards ⟹ validates `k_guard ≤ σ+1`.
2. **Shadow volumes:** for the central `p_0` alone, measure `vol(Sh_ℓ∩X_t)/vol(X_t)` per class
   (fraction of sampled y whose segment to `p_0` hits `D_ℓ`). PREDICT: each small / a `1/poly`
   tail (⟹ thin-shadow route) — and whether the tail shrinks with t (thinner rind deeper in).
3. **Per-pair dip:** along `[g_ℓ, y]` for uncovered y, record which class `ℓ'` blocks and the
   `m_{ℓ'}` dip magnitude — tests the §9.3 2-D dip statement and tells us which route to prove.
All are read-offs from the exact-rejection samples already drawn (d=5,t=10 and the d-sweep).

---

## 10. The proof: k_guard ≤ σ+1 reduced to ONE clean lemma (double-occlusion is thin)

**Experiment confirmed all three predictions (main):** guards ~σ, interior, corner-DIRECTION
aligned (0.95–0.97); **min-tie multiplicity FLAT in d** (mean 1.06→1.13, p90≈1, max 3–4 as
d:3→6) — the class-min is a ~single coordinate, so obstructions are genuinely 2-D; nonempty
F-cells collapse ~9 orders below `d^{2σ}`. The proof below is built on these.

**Guards.** `g_ℓ := (1−η)ĉ_ℓ + η·p_0` (η small, `p_0` = a deep interior point, e.g. FW
center). Guard set `G = {g_1,…,g_σ}` (optionally + `p_0`).

**Lemma 1 (PROVED — own class never blocks).** `g_ℓ ∈ ker(U_ℓ)` (for η small): each
`w_i^ℓ(ĉ_ℓ) = ε^ℓ_i((ĉ_ℓ)_i − a_i) ≥ 0` since `ĉ_ℓ` is the ℓ-top corner, and the interior
mix keeps `w_i^ℓ(g_ℓ) ≥ 0`. So `g_ℓ` sees *all* of `U_ℓ` (hence all of `X_t ⊆ U_ℓ`) through
class ℓ: moving from any `y` toward `ĉ_ℓ` **monotonically raises every `w_i^ℓ`**, so
`M_ℓ,m_ℓ` rise and class ℓ can *never* re-block `[g_ℓ,y]`. ∎

Consequently `[g_ℓ,y] ⊄ X_t` only because some **foreign** class `ℓ'≠ℓ` blocks it (segment
enters `D_{ℓ'}`).

**Definition (binding).** `y` is *binding* for class `ℓ'` if its margin `g_{ℓ'}(y)=M_{ℓ'}(y)+
m_{ℓ'}(y)` is small (within the maximal one-segment drop `Δ` defined below); `y` is deep in
`ℓ'` otherwise.

**Lemma 2 (PROVED — single-binding points are covered by their own guard).** Suppose `y` is
binding for exactly one class `ℓ'` and **deep** in every other class (margin `> Δ`). Then
`g_{ℓ'}` covers `y`: by Lemma 1 class `ℓ'` never blocks; every other class `ℓ''` had margin
`>Δ ≥` its drop along `[g_{ℓ'},y]`, so stays `≥0`. Hence `y` is covered. ∎

(`Δ` = the max decrease of any `g_{ℓ''}` along a guard segment; it is `O(‖disagreement
movement‖)`, and — the realizability input — small because balanced apexes keep the segment's
disagreement-coordinate travel bounded, and O(1) min-ties make the drop a **single-coordinate**
event, not a sum over d coordinates. This is where flat-in-d enters the proof.)

**Theorem (CONDITIONAL).** `vol(uncovered by G) ≤ vol(DoubleBind)`, where
`DoubleBind = {y∈X_t : y is binding for ≥2 classes}`. Hence if `vol(DoubleBind) ≤
(1/poly)·vol(X_t)` then **`σ` guards cover `1−1/poly` of the volume, i.e. `k_guard ≤ σ`**
(⟹ Karp–Luby over σ ray-shootable stars ⟹ poly sampler ⟹ SSG∈P).

*Proof.* By Lemma 2 the complement of `DoubleBind` (points binding for ≤1 class) is covered:
deep-everywhere points are covered by any `g_ℓ` (all classes stay `≥0`), single-binding points
by their own guard. So uncovered `⊆ DoubleBind`. ∎

### 10.1 The sole remaining gap (precisely what resists)

Everything reduces to:

> **Double-occlusion lemma (OPEN).** For balanced (Fermat–Weber) apex trajectories,
> `vol{y∈X_t : g_{ℓ'}(y) ≤ Δ and g_{ℓ''}(y) ≤ Δ for two classes ℓ'≠ℓ''} ≤ (1/poly)·vol(X_t)`,
> where `Δ` is the one-segment guard drop.

Why it is *plausible and the right target*: `{g_{ℓ'} ≤ Δ}` is a **rind** of width `~Δ`
around `∂D_{ℓ'}` — a `(1/poly)`-fraction of volume when `Δ` is small (thin rind). The
intersection of two such rinds (two classes binding at once) is **codimension-2-like**, hence
`~(Δ)²` — even smaller. The O(1) min-tie fact (proved-in-effect by the experiment: min
achieved by ≈1 coordinate, flat in d) makes each rind a *single-coordinate* threshold event,
so its width `Δ` does **not** grow with d — this is exactly why `k_guard` is flat in d.

Why it **resists** a fully unconditional proof: `Δ` (the guard-segment drop of a non-binding
class) is `O(1)` in the worst case (adversarial apex spread can make one segment traverse a
large disagreement distance), so `{g_{ℓ'} ≤ Δ}` need not be a thin rind without the
realizability bound on apex travel. So the lemma is **true under balanced/contracting apexes
(empirically confirmed: uncovered volume `→` the tiny `DoubleBind` set) but reduces, once
more, to the project-wide realizability wall** — now in its tightest, lowest-dimensional form:
*a codimension-2 volume bound on the set where two orientation classes simultaneously bind,
with per-class width controlled by a single-coordinate (O(1) min-tie) threshold.*

### 10.2 Status

* **PROVED (unconditional):** the guard construction (Lemma 1); single-binding ⟹ covered
  (Lemma 2); **uncovered ⊆ DoubleBind** (Theorem); the reduction of `k_guard ≤ σ` to the
  double-occlusion volume lemma.
* **OPEN (the one lemma):** `vol(DoubleBind) ≤ (1/poly)vol(X_t)` — a codim-2 rind bound, true
  under balanced apexes (matching all data), unproven in worst case (the realizability wall).
* **Assembled conditional on it:** σ guards → σ ray-shooting stars → Karp–Luby →
  poly-time near-uniform sampler → poly-time ℓ∞-contraction fixed point → **SSG ∈ P.**

This is the closest the whole program has come: the entire remaining gap is a **single,
concretely-stated, low-dimensional volume inequality** (`DoubleBind` thin), with the
mechanism (per-class single-coordinate rind; codim-2 intersection; flat in d) empirically
nailed. A proof of the double-occlusion lemma under balanced apexes closes SSG∈P via this
route; a realizable counterexample (fat `DoubleBind`) kills it.

---

## 11. Retarget to CC (convex-cover number): the operative, KLS-samplable quantity

**Reframing (main, convex-cell — correct).** The guard number `k` is **necessary but not
sufficient**: star-pieces are non-convex, ray-shooting has exp-in-d variance, and hit-and-run
on a non-convex star-piece still needs isoperimetry. Only **convex** pieces are poly-samplable
(KLS / Dyer–Frieze–Kannan). So the operative quantity is the **convex-cover number**
`CC(X_t)` = fewest convex pieces covering `1−1/poly` of `vol(X_t)`, with `k ≤ CC ≤ k'` (cell
count). Measured `CC ~ σ` (1–11, ~flat in d, greedily constructible). Target:
**`CC(X_t) ≤ poly(σ,d)`.** My `F^{-1}(P)` structure (§8) is built for exactly this.

### 11.1 (PROVED) The convex pieces are the argmax/argmin cells; each is convex

`X_t = box ∩ F^{-1}(P)`, `P` convex (§8.1). Partition by the **active pair pattern**: a cell
fixes, for every cut `r`, `p_r = argmax_i w_i^r` and `q_r = argmin_i w_i^r`. On a cell,
`M_r = w_{p_r}^r` and `m_r = w_{q_r}^r` are **linear**, so

> `X_t ∩ cell = {w_i^r ≤ w_{p_r}^r ∀i,r} ∩ {w_i^r ≥ w_{q_r}^r ∀i,r} ∩ {w_{p_r}^r+w_{q_r}^r ≥ 0 ∀r} ∩ box`

is an intersection of halfspaces — **CONVEX and KLS-samplable.** Hence
**`CC(X_t) ≤ (#nonempty active-pair cells)`.** Worst case `≤ d^{2t}`, but the measured
nonempty count is 64–251 (≈ 9 orders below `d^{2σ}`) — realizability collapses it. So the
proof job is to bound the *nonempty* cells (or a covering subfamily) by `poly(σ,d)`.

### 11.2 (PARTIAL) Binding decomposition: CC ≤ σ·d² + CC(DoubleBind)

Reuse §10's binding structure (margin `g_ℓ(y)=M_ℓ+m_ℓ`, threshold `Δ`):

* **Deep in class ℓ' (`g_{ℓ'} > Δ`)** ⟹ the class-ℓ' constraint is *slack*; it needs no
  active-pair subdivision. Formally, if a region is deep in ℓ' and lies in the **convex
  kernel** `ker(K_{ℓ'}) = {w_i^{ℓ'}+w_j^{ℓ'} ≥ 0 ∀i,j}` (convex, `O(d²)` facets), that kernel
  factor can be intersected in **without** subdividing by ℓ'’s active pair.
* **Single-binding-in-ℓ region** `S_ℓ`: only class ℓ's active pair `(p,q)` need be resolved
  (`d²` choices); the other σ−1 classes enter through their convex kernels. So `S_ℓ` is covered
  by `≤ d²` convex pieces `cell_ℓ(p,q) ∩ ⋂_{ℓ'≠ℓ} ker(K_{ℓ'})`. Summing over ℓ (and the
  deep-everywhere region, which needs `⋂_ℓ ker(K_ℓ)`, one convex piece): `≤ σ·d² + 1` pieces.
* **DoubleBind** (`≥2` classes binding) is the leftover.

> **CC(X_t) ≤ σ·d² + 1 + CC(DoubleBind).** So `CC ≤ poly(σ,d)` follows from **either**
> DoubleBind being `1/poly`-volume (§10's lemma — drop it) **or** DoubleBind decomposing into
> `poly` convex pieces.

### 11.3 The two sub-lemmas that resist (precise)

1. **(deep ⟹ kernel-coverable)** In `S_ℓ`, every slack class `ℓ'` is coverable by `O(1)`
   convex kernel pieces — i.e. "`g_{ℓ'}` large" is (up to `O(1)` convex pieces) `ker(K_{ℓ'})`.
   *Gap:* `g_{ℓ'}=w_max+w_min` large does **not** imply all pairwise `w_i+w_j ≥ 0`; the deep
   set is a superlevel set of `max+min`, non-convex, so a priori `>O(1)` pieces. *Why it should
   hold:* with O(1) min-ties the min is a single coordinate `q`, so `max+min ≥ 0` is
   effectively the single linear constraint `w_p+w_q ≥ 0` — one convex piece per (p,q), and
   deep ⟹ `w_q` comfortably above the others ⟹ `q` stable ⟹ O(1) pieces.
2. **(DoubleBind thin/decomposable)** `vol(DoubleBind) ≤ (1/poly)vol(X_t)` — the same
   double-occlusion lemma (§10.1): codim-2 rind, single-coordinate width (flat in d).

**Both are the realizability wall in convex-cover form**, and both are pinned to the **measured
O(1)-min-tie structure** — which is precisely why `CC~σ`, flat in d, holds empirically.

### 11.4 Status & deciding measurements (to main)

* **PROVED:** convex pieces = active-pair cells, each convex, `CC ≤ #nonempty cells` (§11.1);
  decomposition `CC ≤ σd²+1+CC(DoubleBind)` **modulo** sub-lemma (1) (§11.2).
* **OPEN:** (1) deep⟹O(1)-kernel-pieces, (2) DoubleBind thin — both realizability, both tied to
  O(1) min-ties.
* **Assembled conditional:** `poly(σ,d)` convex pieces → KLS-sample each → Karp–Luby union →
  poly near-uniform sampler → **SSG ∈ P.**

Deciding measurements (reuse existing samples): (a) **CC decomposition** — of the greedy convex
pieces, how many are single-binding vs DoubleBind; is single-binding ≤ σ·(small)? (b)
**deep⟹kernel fraction** — for points deep in class ℓ', what fraction lie in `ker(K_{ℓ'})`?
(tests sub-lemma 1; high ⟹ deep ≈ kernel). (c) **DoubleBind convex-piece count / volume** vs
(Δ,σ,d) (tests sub-lemma 2). (d) **split-rate** — does CC grow *additively* (≈+O(1)) per new
orientation class? Additive-per-class ⟹ `CC=O(σ)` directly.

---

## 12. Tightening: uncovered ≪ DoubleBind (mutual blocking), and it ties to apex-spread

**Measurement (main).** DoubleBind is *not* cleanly `~Δ²`-tiny — with `Δ` relative to the tiny
median margins, DoubleBind grows fast with `Δ` and `σ` (σ=8: 0.06→0.36→0.82 as Δ:0.1→0.5×med).
BUT k_guard ~ σ (guards cover 99%): **uncovered is small even though DoubleBind is not.** So the
containment `uncovered ⊆ DoubleBind` (§10) is **LOOSE** — a DoubleBind point is usually still
covered by *one* of its two binding-classes' guards. The over-approximation must be tightened.

### 12.1 (PROVED) The tight characterization: mutual blocking

Fix a DoubleBind point `y` binding in exactly classes `ℓ, ℓ'` (deep elsewhere). By Lemma 1+2,
the only guards that can fail on `y` are `g_ℓ` and `g_{ℓ'}` (deep classes never block them, and
`g_ℓ` never self-blocks). So:

> **`y` uncovered ⟺ `g_ℓ` is blocked by `ℓ'` AND `g_{ℓ'}` is blocked by `ℓ`** (mutual
> blocking) — strictly stronger than "binding in 2 classes." Hence
> **`uncovered(G) ⊆ ⋃_{pairs {ℓ,ℓ'}} MutualBlock(ℓ,ℓ')`**, `MutualBlock =` {binding in `ℓ,ℓ'`
> ∧ moving toward `ĉ_ℓ` sinks `g_{ℓ'}` below 0 ∧ moving toward `ĉ_{ℓ'}` sinks `g_ℓ` below 0}.

### 12.2 (PROVED) The two-coordinate structure ⟹ MutualBlock is thin (and apex-spread-controlled)

Fold so `ε^ℓ = +1` (class ℓ wants all coords up); let `B = B_{ℓℓ'}` = disagreement coords
(there `ε^{ℓ'} = −1`), `A` = agreement. Then `w_i^ℓ = y_i − a_i^ℓ`; `w_i^{ℓ'} = y_i − a_i^{ℓ'}`
on `A`, `= a_i^{ℓ'} − y_i` on `B`. Moving `y→ĉ_ℓ` raises all `y_i`, dropping `w^{ℓ'}` only on
`B`; moving `y→ĉ_{ℓ'}` lowers `y_i` on `B`, dropping `w^ℓ` only on `B`. So both blocks are driven
by the **same disagreement set `B`**, and:

* **`g_ℓ` blocked by `ℓ'`** ⟹ class-ℓ' argmin `q_{ℓ'} ∈ B` with `w_{q_{ℓ'}}^{ℓ'}=a^{ℓ'}−y < 0`
  ⟹ `y_{q_{ℓ'}} > a_{q_{ℓ'}}^{ℓ'}` (a **large-y** B-coord).
* **`g_{ℓ'}` blocked by `ℓ`** ⟹ class-ℓ argmin `q_ℓ ∈ B` with `w_{q_ℓ}^{ℓ}=y−a^ℓ < 0` ⟹
  `y_{q_ℓ} < a_{q_ℓ}^{ℓ}` (a **small-y** B-coord).

Two consequences, both making `MutualBlock` far thinner than `DoubleBind`:

1. **`|B|=1` pairs are essentially free.** One coord `j` must be *both* argmins ⟹ `y_j <
   a_j^ℓ` **and** `y_j > a_j^{ℓ'}` ⟹ `MutualBlock ⊆ {a_j^{ℓ'} < y_j < a_j^ℓ}` — a **slab of
   width `|a_j^ℓ − a_j^{ℓ'}| = the apex gap on coord j`.** For balanced/contracting apexes this
   width `→ 0`, so **Hamming-adjacent class pairs (disagree in 1 coord) contribute a
   `1/poly`-thin slab.**
2. **`|B|≥2` pairs are codim-2.** The two blocks need *distinct* B-coords in *opposite*
   extremal roles (one large-y argmin of ℓ', one small-y argmin of ℓ), each with a tight
   margin — a genuine codimension-2 event (`~Δ²`), and with O(1) min-ties each role is a single
   coordinate (so no d-blowup).

> **Tightened target (replaces DoubleBind).** `vol(uncovered) ≤ Σ_{pairs} vol(MutualBlock)`,
> where each `MutualBlock(ℓ,ℓ')` is confined to (|B|=1) a slab of width = the apex gap, or
> (|B|≥2) a codim-2 rind. Both are controlled by **apex spread** — closing the loop with §7.2:
> *the true driver is apex spread, and the balanced, contracting trajectory keeps it `1/poly`.*

This is strictly tighter than DoubleBind and matches the empirics (uncovered ≪ DoubleBind,
k_guard~σ): DoubleBind counts points near two boundaries; `MutualBlock` additionally requires
the two boundaries to be *mutually occluding*, which pins `y` to a slab/codim-2 set of width =
apex gap. And it re-derives that **apex-spread, not σ, is the volume of the bad set** — so the
`CC ≤ poly(σ,d)` bound rests on the (realizable, contracting) apex spread being small, the
sharpest and most defensible form of the wall.

### 12.3 Status & the deciding measurement (to main)

* **PROVED:** `uncovered(G) ⊆ ⋃_{pairs} MutualBlock` (tight, §12.1); `|B|=1` ⟹ MutualBlock ⊆
  apex-gap slab; `|B|≥2` ⟹ codim-2 (§12.2). So uncovered is governed by **apex spread**, not
  raw DoubleBind volume.
* **OPEN:** `Σ_pairs vol(MutualBlock) ≤ 1/poly` — now a sum of apex-gap slabs / codim-2 rinds;
  reduces to "apex spread `≤ 1/poly` (balanced, contracting)" — the §7.2 realizability claim.
* **Measurement (main):** measure `vol(MutualBlock(ℓ,ℓ'))` directly — fraction of `y` binding in
  `{ℓ,ℓ'}` for which BOTH `g_ℓ` and `g_{ℓ'}` are blocked (segment-check to each corner). PREDICT:
  (i) `≈ uncovered ≪ DoubleBind`; (ii) for `|B|=1` pairs it scales with the **apex gap** `|a^ℓ−
  a^{ℓ'}|` (not with `Δ`); (iii) `|B|≥2` pairs dominate and are codim-2. Also report per-pair
  MutualBlock vs Hamming distance `|B|` — predict `|B|=1` pairs contribute ~nothing.

---

## 13. Explicit near-corner guards REFUTED; the route survives as greedy cell-discovery

**Measurement (main, honest negative).** (i) `MutualBlock == DoubleBind` exactly (every
double-binding point *is* mutually blocked) — no tightening. (ii) actual uncovered by
`{g_ℓ}∪{p_0}` is 0.43–0.59 `≫` DoubleBind — **contradicting `uncovered ⊆ DoubleBind`.** (iii)
`|B|=1` pairs contribute 0 (the one prediction that held).

**Root cause (accepted).** The near-corner guards `g_ℓ=(1−η)ĉ_ℓ+η·p_0` are **bad guards** — the
corner-marginality problem (§9.1) biting fatally, and it is a **dichotomy with no escape**:
* small η ⟹ `g_ℓ ∈ ker(U_ℓ)` (sees through class ℓ) but `g_ℓ` sits at the marginal corner ⟹
  `g_ℓ ∉ X_t` (ejected by other classes) ⟹ sees *nothing*;
* large η ⟹ `g_ℓ ∈ X_t` but `g_ℓ ∉ ker(U_ℓ)` ⟹ Lemma 1 fails, class ℓ re-blocks.
No η is both in-body and class-deep, so **Lemma 1's hypothesis is unsatisfiable by a near-corner
point for σ≥2** and the explicit `k_guard ≤ σ+1` construction (§9–§12) **collapses.** (Consistent
with the deep⟹kernel refutation, 0.0 at d=6.) I retract it.

### 13.1 What survives, and the correct vehicle

* **`σ=1` is still fully proved** (§2): the corner `ĉ_s` works because there are *no other classes
  to eject it* — the one case where corner-marginality doesn't bite. Unconditional win.
* **`CC~σ` STANDS** (greedy covers 99% with ~σ convex pieces): a small convex cover **exists**,
  just not the closed-form near-corner one.
* **The correct vehicle is not closed-form guards but GREEDY CELL-DISCOVERY**, which *is*
  poly-time-constructible (no closed form needed):
  > **Algorithm.** Sample `X_t`; bucket each sample by its **active-pair cell**
  > `π(y)=(argmax_r w_i^r, argmin_r w_i^r)_r`; each nonempty bucket is a **convex polytope**
  > `X_t ∩ cell(π)` (§11.1, KLS-samplable); keep buckets by decreasing volume until `1−1/poly`
  > covered; Karp–Luby over them.

This is what greedy does, and it is **poly-time iff poly-many cells carry the volume.** The whole
route thus reduces, finally, to **one realizability statement:**

> **Volume-concentration lemma (the wall).** For balanced (Fermat–Weber) apex trajectories,
> `≤ poly(σ,d)` active-pair cells carry `1−1/poly` of `vol(X_t)`.

Empirically TRUE (greedy uses ~σ; nonempty cells 64–251, volume concentrates on ~σ). Worst-case
FALSE (exp cells). This is the realizability core in its **final, correct form** — a statement
purely about volume concentration of the *realizable* body, with no fragile explicit construction.

### 13.2 Honest verdict (the lead's question: provable construction, or the wall?)

* **No provable *closed-form* guard/cell construction** — refuted (corner-marginality; and
  deep⟹kernel + worst-case-exp-cells rule out an a-priori enumerable poly family).
* **But the route is NOT dead:** it survives as **greedy cell-discovery**, a poly-time
  *algorithm* (not a closed form) that provably yields a correct sampler **whenever
  volume-concentration holds** — empirically robust (`CC~σ`, flat in d, greedy 99%). The gap is
  no longer a construction; it is the single **volume-concentration lemma** above.
* **This IS the terminal wall:** every route (Cheeger, κ, star-cover `k`, guard `k_guard`,
  convex-cover `CC`) has converged to the *same* realizability core — but §13.1 states it as
  sharply as it can be: *not* an isoperimetry constant, *not* a fragile guard set, but "**the
  realizable `X_t`'s volume sits on poly-many convex arrangement cells**," a concrete, falsifiable
  conjecture about the SSG cut trajectory that a proof (or realizable counterexample) must address.

**Bottom line:** the explicit `k_guard≤σ+1` construction is refuted and retracted; the poly
sampler survives as **greedy cell-discovery, conditional on the volume-concentration lemma**, the
terminal realizability wall, now stated at maximum sharpness. `σ=1` is the one unconditional win.
The lasting σ-program contributions stand: `X_t = ⋂_{ℓ=1}^σ` monotone up-sets (§1); `σ=1 ⟹`
star-about-corner ⟹ poly, Lean-ready (§2, §7.6); `X_t = F^{-1}(P)`, P convex, active-pair cells
convex/KLS-samplable (§8, §11.1); and the reduction of the entire route to volume-concentration.
