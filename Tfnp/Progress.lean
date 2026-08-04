/-
Copyright (c) 2026 Angus Joshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Angus Joshi
-/
import Tfnp.HitRun
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.PathConnected

/-!
# The progress–convexity trade-off for `ℓ∞` pyramid cuts

Companion to `notes/progress_convexity.md`. The CLY-style algorithm cuts the
candidate body `X` by a **pyramid union** `K(c,s) = ⋃ᵢ 𝒫ᵢ(c, sᵢ)` anchored at a
query point `c`. Cut *validity* holds for **every** apex `c ≠ x*`
(`fixedPoint_mem_pyrUnion_apex`), so the apex is entirely ours to choose. The
two things we want from that choice are in direct conflict, and this file makes
the conflict precise.

Say a coordinate `i` is **live** at `c` for `X` if some point of `X` has its
`ℓ∞`-argmax at `i` (i.e. `𝒫ᵢ(c,φ) ∩ X ≠ ∅` for some sign `φ`), and **two-sided**
if that happens for *both* signs.

* `exists_sign_vacuous_cut` — **progress needs a two-sided coordinate.** If no
  coordinate is two-sided then some sign vector `s` makes the cut *vacuous*:
  `X ⊆ K(c,s)`, nothing is removed. Since the oracle picks `s`, worst-case
  progress is `0`.
* `card_removed_le_sum_min` — the quantitative form: some sign vector leaves at
  most `∑ᵢ min(nᵢ⁺, nᵢ⁻)` points removed, where `nᵢ^φ` counts the points whose
  argmax is `(i,φ)`. Worst-case progress is exactly the "minority count", which
  is maximised (`= |T|/2`) precisely at a balanced point.
* `apex_between_of_two_sided` — a two-sided coordinate **traps the apex**: `cᵢ`
  lies between two points of `X`, and *every* coordinate offset of those points
  is bounded by the coordinate-`i` offset. Progressive apexes are interior; a
  far apex cannot make progress.

On the other side, low activity is exactly what convexity needs:

* `cut_inter_subset_halfspace` — **two live coordinates ⟹ the cut is a
  halfspace on `X`**, so the candidate body stays convex and the round is
  poly-time. This strictly generalises the `k ≤ 2` base case
  (`exists_pair_pyrUnion_subset_halfspace`) to *any* dimension whose body is
  `ℓ∞`-dominated by two coordinates.
* `exists_three_pyramid_centroid` — **three live coordinates ⟹ nothing is
  lost.** Every point of `ℝ^k` whatsoever is the centroid of three points, one
  in each of any three distinct-index pyramids at `c`. Hence
  `eq_univ_of_convex_of_three`: a convex set containing three such pyramids is
  everything; `le_of_quasiconcave_majorant`: no quasiconcave (in particular no
  log-concave) surrogate `h ≥ 1_K` is anywhere below `1`; and
  `exists_injective_of_convex_cover`: covering `K` by convex pieces needs `≥ k`
  of them.

Together: guaranteed progress forces a two-sided (hence interior) apex, and —
once three coordinates are live — no convex or quasiconcave relaxation of the
cut loses a single point. That is the precise reason a first-order method cannot
be run on a convex surrogate, and it identifies the **convex cover number** as
the operative complexity measure. None of this closes the problem; it says where
a closure cannot come from.
-/

set_option autoImplicit false

namespace Tfnp.Contraction

variable {k : ℕ} [NeZero k]

/-- The cut at apex `c` with (full-support, `Bool`) sign vector `s`: the union
of the `k` pyramids `𝒫ᵢ(c, sᵢ)`. Padding a ternary sign vector to full support
only enlarges the cut, so the negative statements proved here for `Cut` are the
strongest form. -/
def Cut (s : Fin k → Bool) (c : Vec k) : Set (Vec k) :=
  { y | ∃ i : Fin k, y ∈ Pyramid i (s i) c }

lemma mem_Cut {s : Fin k → Bool} {c y : Vec k} :
    y ∈ Cut s c ↔ ∃ i : Fin k, y ∈ Pyramid i (s i) c := Iff.rfl

/-- Every point lies in *some* pyramid at every apex: the `2k` pyramids cover
`ℝ^k`. -/
lemma exists_mem_pyramid (c y : Vec k) : ∃ (i : Fin k) (φ : Bool), y ∈ Pyramid i φ c := by
  obtain ⟨i, hi⟩ := exists_coord_eq_linfDist y c
  rcases le_total (c i) (y i) with h | h
  · exact ⟨i, true, by rw [mem_pyramid_true_iff, ← hi, abs_of_nonneg (by linarith)]⟩
  · refine ⟨i, false, ?_⟩
    rw [mem_pyramid_false_iff, ← hi, abs_of_nonpos (by linarith)]
    ring

/-! ## Progress needs a two-sided coordinate -/

/-- **Vacuous cut.** If at every coordinate `i` at most one sign `φ` occurs as
the argmax-sign of a point of `X` (no coordinate is *two-sided*), then the sign
vector picking those signs makes the cut retain all of `X`: the round removes
nothing.

Since the oracle, not the algorithm, chooses the sign vector, this is the
worst-case-progress statement: **a cut with a guaranteed positive removal must
have a two-sided coordinate.** -/
theorem exists_sign_vacuous_cut {c : Vec k} {X : Set (Vec k)}
    (hone : ∀ i : Fin k, ∃ φ : Bool,
      ∀ ψ : Bool, (∃ y ∈ X, y ∈ Pyramid i ψ c) → ψ = φ) :
    ∃ s : Fin k → Bool, X ⊆ Cut s c := by
  choose s hs using hone
  refine ⟨s, fun y hy => ?_⟩
  obtain ⟨i, φ, hiφ⟩ := exists_mem_pyramid c y
  have h : φ = s i := hs i φ ⟨y, hy, hiφ⟩
  exact ⟨i, h ▸ hiφ⟩

/-- **A two-sided coordinate traps the apex.** If `y` has argmax `(i,+)` and `z`
has argmax `(i,−)`, then `cᵢ` is sandwiched between `zᵢ` and `yᵢ`, and *every*
coordinate offset of `y` (resp. `z`) from `c` is bounded by its coordinate-`i`
offset. So an apex that can make progress at coordinate `i` is within the
coordinate-`i` reach of `X` in **every** coordinate: progressive apexes are
interior, and a far apex cannot make progress. -/
theorem apex_between_of_two_sided {c y z : Vec k} {i : Fin k}
    (hy : y ∈ Pyramid i true c) (hz : z ∈ Pyramid i false c) :
    z i ≤ c i ∧ c i ≤ y i ∧ (∀ m, |y m - c m| ≤ y i - c i) ∧
      (∀ m, |z m - c m| ≤ c i - z i) := by
  rw [mem_pyramid_true_iff] at hy
  rw [mem_pyramid_false_iff] at hz
  refine ⟨by linarith [linfDist_nonneg z c], by linarith [linfDist_nonneg y c],
    fun m => ?_, fun m => ?_⟩
  · rw [hy]; exact abs_sub_le_linfDist y c m
  · rw [hz]; exact abs_sub_le_linfDist z c m

/-! ### Quantitative form: worst-case progress is the minority count

Assign to each point its argmax coordinate and sign (`hubIdx`, `hubSgn`); this
partitions a finite candidate set `T`. Choosing the majority sign at every
coordinate retains all majorities, so the removed set is contained in the union
of the minorities. -/

/-- A choice of argmax coordinate for `y` about `c`. -/
noncomputable def hubIdx (c y : Vec k) : Fin k := (exists_coord_eq_linfDist y c).choose

/-- The sign of `y` at its argmax coordinate about `c`. -/
noncomputable def hubSgn (c y : Vec k) : Bool :=
  decide (0 ≤ y (hubIdx c y) - c (hubIdx c y))

lemma hubIdx_spec (c y : Vec k) :
    |y (hubIdx c y) - c (hubIdx c y)| = linfDist y c :=
  (exists_coord_eq_linfDist y c).choose_spec

/-- Every point lies in the pyramid selected by its own argmax data. -/
lemma mem_pyramid_hub (c y : Vec k) : y ∈ Pyramid (hubIdx c y) (hubSgn c y) c := by
  have h := hubIdx_spec c y
  by_cases hle : 0 ≤ y (hubIdx c y) - c (hubIdx c y)
  · have hs : hubSgn c y = true := by simp [hubSgn, hle]
    rw [hs, mem_pyramid_true_iff, ← h, abs_of_nonneg hle]
  · have hs : hubSgn c y = false := by simp [hubSgn, hle]
    rw [hs, mem_pyramid_false_iff, ← h, abs_of_nonpos (by linarith)]
    ring

attribute [local instance] Classical.propDecidable

/-- The number of points of `T` whose argmax data about `c` is `(i, φ)`. -/
noncomputable def hubCount (T : Finset (Vec k)) (c : Vec k) (i : Fin k) (φ : Bool) : ℕ :=
  (T.filter (fun y => hubIdx c y = i ∧ hubSgn c y = φ)).card

/-- **Worst-case progress is the minority count.** Some sign vector `s` leaves
at most `∑ᵢ min(nᵢ⁺, nᵢ⁻)` points of `T` removed, where `nᵢ^φ = hubCount T c i φ`.

Since `∑ᵢ (nᵢ⁺ + nᵢ⁻) = |T|`, this is at most `|T|/2`, with equality exactly at
a **balanced** point (`nᵢ⁺ = nᵢ⁻` for all `i`). So balancedness is not merely
*sufficient* for halving — it is the unique maximiser of guaranteed progress,
and every coordinate that is not two-sided contributes `0`. -/
theorem card_removed_le_sum_min (T : Finset (Vec k)) (c : Vec k) :
    ∃ s : Fin k → Bool,
      (T.filter (fun y => y ∉ Cut s c)).card
        ≤ ∑ i : Fin k, min (hubCount T c i true) (hubCount T c i false) := by
  classical
  set s : Fin k → Bool :=
    fun i => decide (hubCount T c i false ≤ hubCount T c i true) with hsdef
  refine ⟨s, ?_⟩
  -- A removed point must disagree with `s` at its own argmax coordinate.
  have hsub : T.filter (fun y => y ∉ Cut s c)
      ⊆ T.filter (fun y => hubSgn c y ≠ s (hubIdx c y)) := by
    intro y hy
    simp only [Finset.mem_filter] at hy ⊢
    refine ⟨hy.1, fun hcon => hy.2 ?_⟩
    exact ⟨hubIdx c y, hcon ▸ mem_pyramid_hub c y⟩
  refine le_trans (Finset.card_le_card hsub) ?_
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun y => hubIdx c y) (t := (Finset.univ : Finset (Fin k)))
    (fun y _ => Finset.mem_univ _)]
  refine Finset.sum_le_sum fun i _ => ?_
  -- On the fibre over `i`, the disagreeing points are exactly the minority.
  have hfib : (T.filter (fun y => hubSgn c y ≠ s (hubIdx c y))).filter
        (fun y => hubIdx c y = i)
      = T.filter (fun y => hubIdx c y = i ∧ hubSgn c y = !(s i)) := by
    ext y
    simp only [Finset.mem_filter, and_assoc]
    constructor
    · rintro ⟨hyT, hne, hi⟩
      refine ⟨hyT, hi, ?_⟩
      rw [hi] at hne
      revert hne
      cases hubSgn c y <;> cases s i <;> simp
    · rintro ⟨hyT, hi, hb⟩
      refine ⟨hyT, ?_, hi⟩
      rw [hi, hb]
      cases s i <;> simp
  rw [hfib]
  have hcount : (T.filter (fun y => hubIdx c y = i ∧ hubSgn c y = !(s i))).card
      = hubCount T c i (!(s i)) := rfl
  rw [hcount]
  by_cases hle : hubCount T c i false ≤ hubCount T c i true
  · have hsi : s i = true := by simp only [hsdef]; exact decide_eq_true hle
    rw [hsi]
    simp only [Bool.not_true]
    omega
  · have hsi : s i = false := by
      simp only [hsdef]; exact decide_eq_false hle
    rw [hsi]
    simp only [Bool.not_false]
    omega

/-! ## Two live coordinates ⟹ a halfspace cut (the convex regime) -/

/-- **Two live coordinates make the cut convex.** If only coordinates `i` and
`j` are *live* on `X` — no point of `X` has its `ℓ∞`-argmax at any other
coordinate — then on `X` the cut is contained in the linear halfspace
`{y : σᵢ(yᵢ−cᵢ) + σⱼ(yⱼ−cⱼ) ≥ 0}` through `c`.

Consequently the candidate body stays a **convex polytope** and the round is
poly-time by classical cutting planes. This strictly generalises the `k ≤ 2`
base case (`exists_pair_pyrUnion_subset_halfspace`): what matters is not the
ambient dimension but how many coordinates the body can put at its `ℓ∞`-argmax.
Together with `apex_between_of_two_sided` this is the whole trade-off — two live
coordinates buy convexity, guaranteed progress buys a third. -/
theorem cut_inter_subset_halfspace {s : Fin k → Bool} {c : Vec k} {i j : Fin k}
    {X : Set (Vec k)}
    (hlive : ∀ (m : Fin k) (φ : Bool), (∃ y ∈ X, y ∈ Pyramid m φ c) → m = i ∨ m = j) :
    X ∩ Cut s c ⊆
      { y | 0 ≤ signR (s i) * (y i - c i) + signR (s j) * (y j - c j) } := by
  rintro y ⟨hyX, m, hm⟩
  have hmij : m = i ∨ m = j := hlive m (s m) ⟨y, hyX, hm⟩
  rw [mem_pyramid_iff_sign] at hm
  -- every coordinate's signed offset is at least `−‖y−c‖∞`
  have lb : ∀ n : Fin k, -(signR (s n) * (y n - c n)) ≤ linfDist y c := by
    intro n
    have h1 : signR (s n) * (-(y n - c n)) ≤ |(-(y n - c n))| :=
      signR_mul_le_abs (s n) _
    rw [mul_neg, abs_neg] at h1
    exact h1.trans (abs_sub_le_linfDist y c n)
  simp only [Set.mem_setOf_eq]
  rcases hmij with rfl | rfl
  · have := lb j; linarith
  · have := lb i; linarith

/-! ## Three live coordinates ⟹ no convex relaxation loses anything -/

/-- Pushing a point out by `2R` (signed) at coordinate `m`, while perturbing
every other coordinate by at most `R`, lands it in `𝒫ₘ(c, φ)` as soon as
`R ≥ 2‖y−c‖∞`. -/
lemma mem_pyramid_of_push {c y w : Vec k} {m : Fin k} {φ : Bool} {R : ℝ}
    (hR : 2 * linfDist y c ≤ R) (hw : ∀ n, n ≠ m → |w n| ≤ R)
    (hwm : signR φ * w m = 2 * R) :
    (fun n => y n + w n) ∈ Pyramid m φ c := by
  have hD0 : 0 ≤ linfDist y c := linfDist_nonneg y c
  have hR0 : 0 ≤ R := by linarith
  have hkey : signR φ * ((y m + w m) - c m) = signR φ * (y m - c m) + 2 * R := by
    have h : signR φ * ((y m + w m) - c m)
        = signR φ * (y m - c m) + signR φ * w m := by ring
    rw [h, hwm]
  have hlowm : -linfDist y c + 2 * R ≤ signR φ * ((y m + w m) - c m) := by
    rw [hkey]
    have h2 : -linfDist y c ≤ signR φ * (y m - c m) := by
      have h1 : signR φ * (-(y m - c m)) ≤ |(-(y m - c m))| := signR_mul_le_abs φ _
      rw [mul_neg, abs_neg] at h1
      have h3 := h1.trans (abs_sub_le_linfDist y c m)
      linarith
    linarith
  rw [mem_pyramid_iff_sign]
  refine le_antisymm ?_ ?_
  · have hle := abs_sub_le_linfDist (fun n => y n + w n) c m
    exact (signR_mul_le_abs φ ((y m + w m) - c m)).trans hle
  refine linfDist_le fun n => ?_
  by_cases hn : n = m
  · rw [hn]
    change |(y m + w m) - c m| ≤ signR φ * ((y m + w m) - c m)
    have hnn : (0:ℝ) ≤ signR φ * ((y m + w m) - c m) := by linarith
    rw [← abs_signR_mul φ ((y m + w m) - c m), abs_of_nonneg hnn]
  · change |(y n + w n) - c n| ≤ signR φ * ((y m + w m) - c m)
    have h1 := abs_le.mp (abs_sub_le_linfDist y c n)
    have h2 := abs_le.mp (hw n hn)
    rw [abs_le]
    constructor <;> linarith

/-- **The centroid lemma.** For *any* three distinct coordinates `i, j, l`, any
signs, any apex `c` and any target point `y` whatsoever, `y` is the centroid of
three points, one in each of `𝒫ᵢ(c,a)`, `𝒫ⱼ(c,b)`, `𝒫ₗ(c,e)`.

The three points push `y` out by `2R` along their own coordinate and `−R` along
the other two, so the three pushes cancel. This is the sharp form of the
`|S| ≥ 3` non-convexity of `ℓ∞` cuts: three pyramids at a common apex already
generate everything, with the constant `3`. -/
theorem exists_three_pyramid_centroid (c y : Vec k) {i j l : Fin k}
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) (a b e : Bool) :
    ∃ z₁ z₂ z₃ : Vec k,
      z₁ ∈ Pyramid i a c ∧ z₂ ∈ Pyramid j b c ∧ z₃ ∈ Pyramid l e c ∧
      ∀ n, (z₁ n + z₂ n + z₃ n) / 3 = y n := by
  classical
  set R : ℝ := 2 * linfDist y c + 1 with hRdef
  have hR : 2 * linfDist y c ≤ R := by rw [hRdef]; linarith
  have hR0 : 0 ≤ R := le_trans (by linarith [linfDist_nonneg y c]) hR
  -- the common sign profile subtracted by all three points
  set g : Vec k := fun n =>
    if n = i then signR a else if n = j then signR b else if n = l then signR e else 0
    with hgdef
  have hgabs : ∀ n, |g n| ≤ 1 := by
    intro n
    simp only [hgdef]
    split_ifs
    · cases a <;> norm_num [signR]
    · cases b <;> norm_num [signR]
    · cases e <;> norm_num [signR]
    · norm_num
  have hgi : g i = signR a := by simp [hgdef]
  have hgj : g j = signR b := by simp [hgdef, Ne.symm hij]
  have hgl : g l = signR e := by simp [hgdef, Ne.symm hil, Ne.symm hjl]
  -- the perturbation carried by the point associated with coordinate `m`
  have key : ∀ (m : Fin k) (φ : Bool), g m = signR φ →
      (fun n => y n + R * ((if n = m then 3 * signR φ else 0) - g n)) ∈ Pyramid m φ c := by
    intro m φ hgm
    refine mem_pyramid_of_push (w := fun n => R * ((if n = m then 3 * signR φ else 0) - g n))
      hR (fun n hn => ?_) ?_
    · change |R * ((if n = m then 3 * signR φ else 0) - g n)| ≤ R
      rw [if_neg hn, zero_sub, mul_neg, abs_neg, abs_mul, abs_of_nonneg hR0]
      calc R * |g n| ≤ R * 1 := mul_le_mul_of_nonneg_left (hgabs n) hR0
        _ = R := by ring
    · change signR φ * (R * ((if m = m then 3 * signR φ else 0) - g m)) = 2 * R
      rw [if_pos rfl, hgm]
      have hsq : signR φ * signR φ = 1 := signR_sq φ
      linear_combination (2 * R) * hsq
  refine ⟨_, _, _, key i a hgi, key j b hgj, key l e hgl, fun n => ?_⟩
  -- the three pushes cancel coordinatewise
  by_cases hni : n = i
  · rw [hni, if_pos rfl, if_neg hij, if_neg hil, hgi]; ring
  · by_cases hnj : n = j
    · rw [hnj, if_neg (Ne.symm hij), if_pos rfl, if_neg hjl, hgj]; ring
    · by_cases hnl : n = l
      · rw [hnl, if_neg (Ne.symm hil), if_neg (Ne.symm hjl), if_pos rfl, hgl]; ring
      · have hg0 : g n = 0 := by simp only [hgdef]; rw [if_neg hni, if_neg hnj, if_neg hnl]
        rw [if_neg hni, if_neg hnj, if_neg hnl, hg0]; ring

/-- **Three pyramids fill space.** Any convex set containing three pyramids at a
common apex, with distinct coordinate indices and arbitrary signs, is all of
`ℝ^k`. In particular for `k ≥ 3` the convex hull of a cut is everything: no
convex outer approximation of a cut loses a single point. -/
theorem eq_univ_of_convex_of_three {C : Set (Vec k)} (hC : Convex ℝ C) {c : Vec k}
    {i j l : Fin k} (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) {a b e : Bool}
    (h₁ : Pyramid i a c ⊆ C) (h₂ : Pyramid j b c ⊆ C) (h₃ : Pyramid l e c ⊆ C) :
    C = Set.univ := by
  refine Set.eq_univ_of_forall fun y => ?_
  obtain ⟨z₁, z₂, z₃, hz₁, hz₂, hz₃, havg⟩ :=
    exists_three_pyramid_centroid c y hij hil hjl a b e
  have hm₁ : z₁ ∈ C := h₁ hz₁
  have hm₂ : z₂ ∈ C := h₂ hz₂
  have hm₃ : z₃ ∈ C := h₃ hz₃
  have hmid : ((1:ℝ)/2) • z₁ + ((1:ℝ)/2) • z₂ ∈ C :=
    hC hm₁ hm₂ (by norm_num) (by norm_num) (by norm_num)
  have hy : y = ((2:ℝ)/3) • (((1:ℝ)/2) • z₁ + ((1:ℝ)/2) • z₂) + ((1:ℝ)/3) • z₃ := by
    funext n
    have h := havg n
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  rw [hy]
  exact hC hmid hm₃ (by norm_num) (by norm_num) (by norm_num)

/-- **No quasiconcave surrogate.** If `h` is quasiconcave (all superlevel sets
convex) and dominates the indicator of a cut (`h ≥ 1` on `K`), then `h ≥ 1`
**everywhere**. So no log-concave / convex / entropic smoothing of the cut
indicator integrates to less than the whole box: such a potential can never
decrease, and there is no convex surrogate on which to run a first-order method.
Any usable surrogate must itself have non-convex superlevel sets — which is why
the operative complexity measure is the *convex cover number* of the cut rather
than any convexity constant. -/
theorem le_of_quasiconcave_majorant {h : Vec k → ℝ}
    (hq : ∀ a : ℝ, Convex ℝ { y | a ≤ h y }) {s : Fin k → Bool} {c : Vec k}
    {i j l : Fin k} (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (hmaj : ∀ y ∈ Cut s c, 1 ≤ h y) (y : Vec k) : 1 ≤ h y := by
  have hsub : ∀ m : Fin k, Pyramid m (s m) c ⊆ { z | 1 ≤ h z } :=
    fun m z hz => hmaj z ⟨m, hz⟩
  have huniv := eq_univ_of_convex_of_three (hq 1) hij hil hjl (hsub i) (hsub j) (hsub l)
  have hy : y ∈ { z : Vec k | 1 ≤ h z } := huniv ▸ Set.mem_univ y
  exact hy

/-! ## Splitting needs the apex outside: pyramids are convex and share the apex

The adversarial-components experiment (`notes/adversarial_components.md`)
observes that predicted splits of the candidate body evaporate on resampling.
The mechanism is provable: every pyramid of a cut **contains the apex**, and
pyramids are **convex**, so a convex lobe containing the apex meets the cut in a
union of convex sets sharing a point — connected. A cut can only split a lobe
the apex is *not* in (compare `apex_between_of_two_sided`: progressive apexes
are trapped *inside*). -/

/-- The apex belongs to every pyramid anchored at it. -/
lemma apex_mem_pyramid (i : Fin k) (φ : Bool) (c : Vec k) : c ∈ Pyramid i φ c := by
  have h0 : linfDist c c = 0 := by
    rw [linfDist_eq_dist]; exact dist_self _
  cases φ
  · rw [mem_pyramid_false_iff, h0, sub_self]
  · rw [mem_pyramid_true_iff, h0, sub_self]

/-- Pyramids are convex: on the segment, the signed offset at `i` is the convex
combination of the endpoints' offsets, which equal their `linfDist`s; convexity
of `linfDist` in its first argument closes the sandwich. -/
lemma convex_pyramid (i : Fin k) (φ : Bool) (c : Vec k) :
    Convex ℝ (Pyramid i φ c) := by
  intro y hy z hz a b ha hb hab
  rw [mem_pyramid_iff_sign] at hy hz ⊢
  set m : Vec k := a • y + b • z with hm
  have hmj : ∀ j, m j = a * y j + b * z j := fun j => rfl
  -- the signed offset at `i` interpolates
  have hoff : signR φ * (m i - c i)
      = a * (signR φ * (y i - c i)) + b * (signR φ * (z i - c i)) := by
    rw [hmj i]; linear_combination (signR φ * c i) * hab
  -- `linfDist m c` is at most the interpolated value…
  have hle : linfDist m c ≤ a * linfDist y c + b * linfDist z c := by
    refine linfDist_le fun j => ?_
    have h1 : |y j - c j| ≤ linfDist y c := abs_sub_le_linfDist y c j
    have h2 : |z j - c j| ≤ linfDist z c := abs_sub_le_linfDist z c j
    have he : m j - c j = a * (y j - c j) + b * (z j - c j) := by
      rw [hmj j]; linear_combination (c j) * hab
    rw [he]
    calc |a * (y j - c j) + b * (z j - c j)|
        ≤ |a * (y j - c j)| + |b * (z j - c j)| := abs_add_le _ _
      _ = a * |y j - c j| + b * |z j - c j| := by
          rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * linfDist y c + b * linfDist z c := by nlinarith
  -- …and at least the offset, which equals it.
  have hge : signR φ * (m i - c i) ≤ linfDist m c :=
    (signR_mul_le_abs _ _).trans (abs_sub_le_linfDist m c i)
  rw [hoff, hy, hz] at *
  linarith

/-- **A convex lobe containing the apex cannot be split.** If `X` is convex and
the apex `c` lies in `X`, then `X ∩ Cut s c` is preconnected: the pieces
`X ∩ 𝒫ᵢ(c, sᵢ)` are convex and all contain `c`. Splits of the candidate body
can only occur in lobes the apex is *not* in — which is why balanced (interior,
by `apex_between_of_two_sided`) apexes are observed not to shatter the body. -/
theorem cut_inter_convex_isPreconnected {X : Set (Vec k)} (hX : Convex ℝ X)
    {c : Vec k} (hc : c ∈ X) (s : Fin k → Bool) :
    IsPreconnected (X ∩ Cut s c) := by
  have hrw : X ∩ Cut s c = ⋃ i : Fin k, (X ∩ Pyramid i (s i) c) := by
    ext y
    simp only [Set.mem_inter_iff, mem_Cut, Set.mem_iUnion]
    tauto
  rw [hrw]
  refine isPreconnected_iUnion ⟨c, ?_⟩ fun i => ?_
  · simp only [Set.mem_iInter]
    exact fun i => ⟨hc, apex_mem_pyramid i (s i) c⟩
  · exact (hX.inter (convex_pyramid i (s i) c)).isPreconnected

/-! ## Cells of a cut trajectory are convex

The pyramid-index decomposition underlying the telescoping convex-cover
algorithm (`notes/FINAL_REPORT.md` addendum, `notes/cell_sampler.md`): fixing,
for each cut `r`, the index `π r` of the pyramid containing the point, the
resulting cell is an intersection of pyramids — convex, and (being an
intersection of `O(d·t)` halfspace-pairs with the box) a polytope. The
candidate body is the union of its nonempty cells, so a uniform sampler for
the mass-carrying cells is a uniform sampler for the body — conjecture (★) is
precisely that `poly(d,t)` of these cells carry the mass. -/

/-- **Cells are convex.** For any family of cuts `(cs r, ss r)` and any choice
`π` of a pyramid index per cut, the cell
`⋂ r, 𝒫_{π r}(cs r, ss r (π r))` is convex. -/
theorem convex_cell {ι : Type*} (cs : ι → Vec k) (ss : ι → (Fin k → Bool))
    (π : ι → Fin k) :
    Convex ℝ (⋂ r, Pyramid (π r) (ss r (π r)) (cs r)) :=
  convex_iInter fun r => convex_pyramid (π r) (ss r (π r)) (cs r)

/-! ## The convex cover number of a single cut is exactly `k` -/

/-- The `k` **mutually invisible** witnesses of a cut: `pᵐ` sits at signed
offset `+1` on coordinate `m` and `−1` on every other coordinate. Each lies in
the cut (in `𝒫ₘ(c, sₘ)`), but the midpoint of any two has *all* signed offsets
`≤ 0` while some offset is `−1`, so it leaves the cut. -/
noncomputable def coverWitness (s : Fin k → Bool) (c : Vec k) (m : Fin k) : Vec k :=
  fun n => c n + signR (s n) * (if n = m then 1 else -1)

lemma coverWitness_offset (s : Fin k → Bool) (c : Vec k) (m n : Fin k) :
    signR (s n) * (coverWitness s c m n - c n) = (if n = m then 1 else -1) := by
  have hsq : signR (s n) * signR (s n) = 1 := signR_sq (s n)
  simp only [coverWitness]
  linear_combination (if n = m then (1:ℝ) else -1) * hsq

lemma coverWitness_abs (s : Fin k → Bool) (c : Vec k) (m n : Fin k) :
    |coverWitness s c m n - c n| = 1 := by
  have h := coverWitness_offset s c m n
  have h2 : |signR (s n) * (coverWitness s c m n - c n)| = 1 := by
    rw [h]; split_ifs <;> norm_num
  rwa [abs_signR_mul] at h2

lemma linfDist_coverWitness (s : Fin k → Bool) (c : Vec k) (m : Fin k) :
    linfDist (coverWitness s c m) c = 1 :=
  le_antisymm (linfDist_le fun n => (coverWitness_abs s c m n).le)
    ((coverWitness_abs s c m m).symm.trans_le (abs_sub_le_linfDist _ _ m))

lemma coverWitness_mem (s : Fin k → Bool) (c : Vec k) (m : Fin k) :
    coverWitness s c m ∈ Cut s c := by
  refine ⟨m, ?_⟩
  rw [mem_pyramid_iff_sign, coverWitness_offset, if_pos rfl, linfDist_coverWitness]

/-- The midpoint of two distinct witnesses leaves the cut, provided `k ≥ 3` (so
that some third coordinate keeps its offset at `−1`). -/
lemma coverWitness_midpoint_notMem (hk : 3 ≤ k) (s : Fin k → Bool) (c : Vec k)
    {m n : Fin k} (hmn : m ≠ n) :
    ((1:ℝ)/2) • coverWitness s c m + ((1:ℝ)/2) • coverWitness s c n ∉ Cut s c := by
  classical
  set q : Vec k := ((1:ℝ)/2) • coverWitness s c m + ((1:ℝ)/2) • coverWitness s c n with hq
  obtain ⟨r, hr⟩ : ∃ r : Fin k, r ∉ ({m, n} : Finset (Fin k)) := by
    by_contra hcon
    push_neg at hcon
    have h1 : (Finset.univ : Finset (Fin k)) ⊆ {m, n} := fun x _ => hcon x
    have h2 := Finset.card_le_card h1
    have h3 : ({m, n} : Finset (Fin k)).card ≤ 2 :=
      le_trans (Finset.card_insert_le _ _) (by simp)
    simp only [Finset.card_univ, Fintype.card_fin] at h2
    omega
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hr
  obtain ⟨hrm, hrn⟩ := hr
  have hoff : ∀ p : Fin k, signR (s p) * (q p - c p)
      = ((if p = m then (1:ℝ) else -1) + (if p = n then 1 else -1)) / 2 := by
    intro p
    have hm := coverWitness_offset s c m p
    have hn := coverWitness_offset s c n p
    simp only [hq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (1/2 : ℝ) * hm + (1/2 : ℝ) * hn
  have hle0 : ∀ p : Fin k, signR (s p) * (q p - c p) ≤ 0 := by
    intro p
    rw [hoff p]
    by_cases h1 : p = m
    · by_cases h2 : p = n
      · exact absurd (h1.symm.trans h2) hmn
      · rw [if_pos h1, if_neg h2]; norm_num
    · rw [if_neg h1]; split_ifs <;> norm_num
  have hrval : signR (s r) * (q r - c r) = -1 := by
    rw [hoff r, if_neg hrm, if_neg hrn]; norm_num
  have hdist : (1:ℝ) ≤ linfDist q c := by
    have habs : |signR (s r) * (q r - c r)| = 1 := by rw [hrval]; norm_num
    rw [abs_signR_mul] at habs
    exact habs ▸ abs_sub_le_linfDist q c r
  rintro ⟨p, hp⟩
  rw [mem_pyramid_iff_sign] at hp
  have := hle0 p
  rw [hp] at this
  linarith

/-- **The convex cover number of a cut is at least `k`.** Any family of convex
subsets of the cut that covers it admits an injection from `Fin k`, i.e. has at
least `k` members: the `k` witnesses are pairwise non-co-convex, so no piece can
contain two of them. Since the `k` pyramids themselves are a convex cover, the
number is *exactly* `k`.

This is the quantitative replacement for "the convex hull is everything": a cut
is not merely non-convex, it costs `k` convex pieces. Over `t` rounds the
candidate body is an intersection of `t` such cuts, and whether *its* cover
number stays polynomial is exactly the open sampling question. -/
theorem exists_injective_of_convex_cover (hk : 3 ≤ k) {s : Fin k → Bool} {c : Vec k}
    {ι : Type*} (F : ι → Set (Vec k)) (hconv : ∀ x, Convex ℝ (F x))
    (hsub : ∀ x, F x ⊆ Cut s c) (hcov : Cut s c ⊆ ⋃ x, F x) :
    ∃ g : Fin k → ι, Function.Injective g := by
  choose g hg using fun m => Set.mem_iUnion.mp (hcov (coverWitness_mem s c m))
  refine ⟨g, fun m n hmn => ?_⟩
  by_contra hne
  have h1 : coverWitness s c m ∈ F (g m) := hg m
  have h2 : coverWitness s c n ∈ F (g m) := hmn ▸ hg n
  have hmid := hconv (g m) h1 h2 (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num)
  exact coverWitness_midpoint_notMem hk s c hne (hsub (g m) hmid)

end Tfnp.Contraction
