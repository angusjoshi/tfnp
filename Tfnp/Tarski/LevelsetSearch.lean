/-
Copyright (c) 2026 Angus Joshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Angus Joshi
-/
import Tfnp.Tarski.Levelset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Tfnp.Shrinking

/-!
# The Haslebacher–Lill search space, and Lemmas 3.5 and 3.12

HL §3.1–3.2.  The levelset subprocedure maintains six bounding points — an
`i`-upward `u⁽ⁱ⁾` and an `i`-downward `d⁽ⁱ⁾` for each of the three dimensions,
with `u⁽ⁱ⁾ᵢ ≤ d⁽ⁱ⁾ᵢ` (HL Definition 3.4) — and shrinks the induced search space

`S = {x ∈ L_k | u⁽ⁱ⁾ᵢ ≤ xᵢ ≤ d⁽ⁱ⁾ᵢ for all i}`

until some `diam(S)ᵢ ≤ 1`, at which point one of three configurations must be
present among the six points (HL Lemma 3.12).

## The extents of the search space

`S` is cut out of a *levelset*, so its extent in coordinate `i` is not simply
`[ℓᵢ, rᵢ]`: the level constraint `|x| = k` also binds.  `sLo` and `sHi` give the
true extents,

`sLoᵢ = max(ℓᵢ, k + rᵢ − |r|)`,  `sHiᵢ = min(rᵢ, k + ℓᵢ − |ℓ|)`,

and `sLo_attained` / `sHi_attained` show they really are attained — which needs
`exists_lev_between`, i.e. that no level is skipped.

## Main results

* `mem_SSet_bounds`, `sLo_attained`, `sHi_attained` — `sLo`/`sHi` are the extents.
* `sDiam_cases` — the arithmetic core of HL Lemma 3.12: if no pair
  `(u⁽ⁱ⁾, d⁽ⁱ⁾)` is in third configuration and some `diam(S)ᵢ ≤ 1`, then
  `k ≤ |ℓ| + 1` or `|r| ≤ k + 1`.  This is what HL's "either `Tu` or `Td` consists
  of at most 3 points" amounts to.
* `fin3_config_exists` — the combinatorics: three points whose deviations from `ℓ`
  have zero diagonal and row sums at most one always contain a first or second
  configuration pattern.  Proved by `decide` over all `2⁹` sign patterns.
* `hasProgress_or_config3` — **HL Lemma 3.12**, combined with HL Observations 3.9
  and 3.10: a search space with a small diameter yields either progress outright,
  or a third configuration among the bounding points.

A remark on the argument.  HL justify the step above by counting points of the
"triangle" `Tu = {x ∈ L_k | u⁽ⁱ⁾ᵢ ≤ xᵢ ∀ i}`, which needs each `u⁽ⁱ⁾` to lie in
`Tu`, i.e. `u⁽ⁱ⁾ⱼ ≥ u⁽ʲ⁾ⱼ` — a condition not in Definition 3.4 and not preserved
by the shrinking step.  It turns out not to be needed: the *level* constraint
`|u⁽ⁱ⁾| = k` together with `k ≤ |ℓ| + 1` already forces at most one coordinate of
`u⁽ⁱ⁾` to exceed `ℓ` (two would overshoot the level by two), and that is the only
consequence the configuration argument uses.  So Definition 3.4 is sufficient
exactly as stated, with deviations from `ℓ` allowed to be negative.
-/

namespace Tfnp.Tarski

variable {d : ℕ}

/-! ### Coordinates versus levels -/

lemma coord_le_lev (x : Pt d) (i : Fin d) : x i ≤ lev x :=
  Finset.single_le_sum (f := fun j => x j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

lemma lev_update (x : Pt d) (i : Fin d) (v : ℕ) :
    lev (Function.update x i v) + x i = lev x + v := by
  unfold lev
  have key : ∀ g : Fin d → ℕ,
      ∑ j, g j = g i + ∑ j ∈ (Finset.univ : Finset (Fin d)).erase i, g j :=
    fun g => (Finset.add_sum_erase _ g (Finset.mem_univ i)).symm
  rw [key (Function.update x i v), key x]
  have hcong : ∑ j ∈ (Finset.univ : Finset (Fin d)).erase i, Function.update x i v j
      = ∑ j ∈ (Finset.univ : Finset (Fin d)).erase i, x j :=
    Finset.sum_congr rfl fun j hj => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [hcong, Function.update_self]
  omega

/-- The sum of the *other* coordinates is monotone.  Equivalently
`lev ℓ - ℓ i ≤ lev r - r i`, phrased without truncated subtraction.  This is the
fact that `lev`-monotonicity alone does not give, and that the search-space
extents need. -/
lemma sumOther_mono {ℓ r : Pt d} (hlr : ℓ ≤ r) (i : Fin d) :
    lev ℓ + r i ≤ lev r + ℓ i := by
  have hup : Function.update ℓ i (r i) ≤ r := by
    refine coord_le fun j => ?_
    by_cases hj : j = i
    · subst hj; simp
    · rw [Function.update_of_ne hj]; exact le_coord hlr j
  have h1 := lev_update ℓ i (r i)
  have h2 : lev (Function.update ℓ i (r i)) ≤ lev r := lev_mono hup
  omega

/-- In three dimensions the level splits over any listing of the coordinates. -/
lemma lev_three (x : Pt 3) {i j p : Fin 3} (hij : i ≠ j) (hip : i ≠ p) (hjp : j ≠ p) :
    lev x = x i + x j + x p := by
  have h0 : lev x = x 0 + x 1 + x 2 := by simp [lev, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> fin_cases p <;> simp_all <;> omega

/-- Every coordinate of `Fin 3` has two others. -/
lemma fin3_others : ∀ i : Fin 3, ∃ j p : Fin 3, i ≠ j ∧ i ≠ p ∧ j ≠ p := by decide

/-! ### The search space and its extents -/

/-- HL Definition 3.4: the remaining search space, cut out of the levelset `L_k`. -/
def SSet (ℓ r : Pt d) (k : ℕ) : Set (Pt d) := {x | lev x = k ∧ ℓ ≤ x ∧ x ≤ r}

/-- The lower extent of the search space in coordinate `i`. -/
def sLo (ℓ r : Pt d) (k : ℕ) (i : Fin d) : ℕ := max (ℓ i) (k + r i - lev r)

/-- The upper extent of the search space in coordinate `i`. -/
def sHi (ℓ r : Pt d) (k : ℕ) (i : Fin d) : ℕ := min (r i) (k + ℓ i - lev ℓ)

/-- HL's `diam(S)ᵢ`. -/
def sDiam (ℓ r : Pt d) (k : ℕ) (i : Fin d) : ℕ := sHi ℓ r k i - sLo ℓ r k i

section Extents

variable {ℓ r : Pt d} {k : ℕ}

lemma sLo_le_sHi (hlr : ℓ ≤ r) (hlk : lev ℓ ≤ k) (hkr : k ≤ lev r) (i : Fin d) :
    sLo ℓ r k i ≤ sHi ℓ r k i := by
  have h1 : ℓ i ≤ r i := le_coord hlr i
  have h2 := sumOther_mono hlr i
  have h3 : ℓ i ≤ lev ℓ := coord_le_lev ℓ i
  have h4 : r i ≤ lev r := coord_le_lev r i
  simp only [sLo, sHi, max_le_iff, le_min_iff]
  refine ⟨⟨h1, ?_⟩, ?_, ?_⟩ <;> omega

/-- Every point of the search space lies between the extents. -/
lemma mem_SSet_bounds {x : Pt d} (hx : x ∈ SSet ℓ r k) (i : Fin d) :
    sLo ℓ r k i ≤ x i ∧ x i ≤ sHi ℓ r k i := by
  obtain ⟨hlev, hlx, hxr⟩ := hx
  have h1 : ℓ i ≤ x i := le_coord hlx i
  have h2 : x i ≤ r i := le_coord hxr i
  have h3 := sumOther_mono hxr i
  have h4 := sumOther_mono hlx i
  have h5 : x i ≤ lev x := coord_le_lev x i
  subst hlev
  constructor
  · simp only [sLo, max_le_iff]; omega
  · simp only [sHi, le_min_iff]; omega

/-- Every value between the extents is attained by a point of the search space.
Sliding both corners to `v` in coordinate `i` gives a box straddling level `k`, so
`exists_lev_between` — no level is skipped — produces the point. -/
lemma exists_mem_SSet_coord (hlr : ℓ ≤ r) (hlk : lev ℓ ≤ k) (i : Fin d)
    {v : ℕ} (h1 : sLo ℓ r k i ≤ v) (h2 : v ≤ sHi ℓ r k i) :
    ∃ x, x ∈ SSet ℓ r k ∧ x i = v := by
  have hv_l : ℓ i ≤ v := le_trans (le_max_left _ _) h1
  have hv_r : v ≤ r i := le_trans h2 (min_le_left _ _)
  have hv_lo : k + r i - lev r ≤ v := le_trans (le_max_right _ _) h1
  have hv_hi : v ≤ k + ℓ i - lev ℓ := le_trans h2 (min_le_right _ _)
  have hli : ℓ i ≤ lev ℓ := coord_le_lev ℓ i
  have hri : r i ≤ lev r := coord_le_lev r i
  have hab : Function.update ℓ i v ≤ Function.update r i v := by
    refine coord_le fun j => ?_
    by_cases hj : j = i
    · subst hj; simp
    · rw [Function.update_of_ne hj, Function.update_of_ne hj]; exact le_coord hlr j
  have hlev_a : lev (Function.update ℓ i v) ≤ k := by
    have := lev_update ℓ i v; omega
  have hlev_b : k ≤ lev (Function.update r i v) := by
    have := lev_update r i v; omega
  obtain ⟨q, hqa, hqb, hqlev⟩ := exists_lev_between hab hlev_a hlev_b
  have hqi : q i = v := by
    have ha := le_coord hqa i
    have hb := le_coord hqb i
    rw [Function.update_self] at ha hb
    omega
  refine ⟨q, ⟨hqlev, coord_le fun j => ?_, coord_le fun j => ?_⟩, hqi⟩
  · by_cases hj : j = i
    · subst hj; omega
    · have := le_coord hqa j; rwa [Function.update_of_ne hj] at this
  · by_cases hj : j = i
    · subst hj; omega
    · have := le_coord hqb j; rwa [Function.update_of_ne hj] at this

lemma sLo_attained (hlr : ℓ ≤ r) (hlk : lev ℓ ≤ k) (hkr : k ≤ lev r) (i : Fin d) :
    ∃ x, x ∈ SSet ℓ r k ∧ x i = sLo ℓ r k i :=
  exists_mem_SSet_coord hlr hlk i le_rfl (sLo_le_sHi hlr hlk hkr i)

lemma sHi_attained (hlr : ℓ ≤ r) (hlk : lev ℓ ≤ k) (hkr : k ≤ lev r) (i : Fin d) :
    ∃ x, x ∈ SSet ℓ r k ∧ x i = sHi ℓ r k i :=
  exists_mem_SSet_coord hlr hlk i (sLo_le_sHi hlr hlk hkr i) le_rfl

end Extents

/-! ### The arithmetic core of HL Lemma 3.12 -/

/-- If no pair `(u⁽ⁱ⁾, d⁽ⁱ⁾)` is in third configuration — i.e. `rᵢ ≥ ℓᵢ + 2` for
every `i` — and some extent of the search space has diameter at most one, then the
level `k` is within one of `|ℓ|` or of `|r|`.

This is the content of HL's "either `Tu` or `Td` consists of at most 3 points".
The fourth of the four ways `sHi` and `sLo` can be attained is excluded because it
would make the diameter the sum of the *other two* widths, each at least two. -/
theorem sDiam_cases {ℓ r : Pt 3} {k : ℕ}
    (hwide : ∀ i, ℓ i + 2 ≤ r i) {i : Fin 3} (hsmall : sDiam ℓ r k i ≤ 1) :
    k ≤ lev ℓ + 1 ∨ lev r ≤ k + 1 := by
  obtain ⟨j, p, hij, hip, hjp⟩ := fin3_others i
  have hlev_l : lev ℓ = ℓ i + ℓ j + ℓ p := lev_three ℓ hij hip hjp
  have hlev_r : lev r = r i + r j + r p := lev_three r hij hip hjp
  have h1 := hwide i
  have h2 := hwide j
  have h3 := hwide p
  simp only [sDiam, sLo, sHi] at hsmall
  omega

/-! ### The combinatorics of the three configurations

Write `P i j` for "`u⁽ⁱ⁾` strictly exceeds `ℓ` in coordinate `j`".  Then

* `P i i` is false, since `u⁽ⁱ⁾ᵢ = ℓᵢ`;
* at most one `j ≠ i` has `P i j`, since two would push `|u⁽ⁱ⁾|` at least two above
  `|ℓ|`, whereas `|u⁽ⁱ⁾| = k ≤ |ℓ| + 1`;
* a first configuration between `i` and `j` is exactly `¬P j i ∧ ¬P i j`;
* a second configuration on `(i, j, p)` is exactly `¬P j i ∧ ¬P p j ∧ ¬P i p`.

The following says one of the last two always happens.  Three pairs each need a
positive entry, each of the three rows supplies at most one, so the positives form
a fixed-point-free map hitting each pair once — which is a 3-cycle, and a 3-cycle
gives the second configuration. -/
private lemma bool_of_ne_false {b : Bool} (h : ¬ b = false) : b = true := by
  cases b <;> simp_all

theorem fin3_config_exists (P : Fin 3 → Fin 3 → Bool)
    (hrow : ∀ i j p : Fin 3, j ≠ i → p ≠ i → j ≠ p → ¬(P i j = true ∧ P i p = true)) :
    (∃ i j : Fin 3, i ≠ j ∧ P j i = false ∧ P i j = false)
      ∨ (∃ i j p : Fin 3, i ≠ j ∧ i ≠ p ∧ j ≠ p ∧
          P j i = false ∧ P p j = false ∧ P i p = false) := by
  by_cases hc : ∃ i j : Fin 3, i ≠ j ∧ P j i = false ∧ P i j = false
  · exact Or.inl hc
  push Not at hc
  -- No first configuration: every unordered pair carries at least one `true`.
  have pair : ∀ i j : Fin 3, i ≠ j → P j i = true ∨ P i j = true := by
    intro i j hij
    cases hji : P j i
    · exact Or.inr (bool_of_ne_false (hc i j hij hji))
    · exact Or.inl rfl
  have r0 := hrow 0 1 2 (by decide) (by decide) (by decide)
  have r1 := hrow 1 0 2 (by decide) (by decide) (by decide)
  have r2 := hrow 2 0 1 (by decide) (by decide) (by decide)
  -- Each row carries at most one `true`, so the three `true`s form a 3-cycle, and
  -- either 3-cycle is a second configuration.
  cases h01 : P 0 1
  · have h10 : P 1 0 = true := by
      rcases pair 0 1 (by decide) with h | h
      · exact h
      · rw [h01] at h; exact absurd h (by simp)
    have h12 : P 1 2 = false := by
      cases h : P 1 2
      · rfl
      · exact absurd ⟨h10, h⟩ r1
    have h21 : P 2 1 = true := by
      rcases pair 1 2 (by decide) with h | h
      · exact h
      · rw [h12] at h; exact absurd h (by simp)
    have h20 : P 2 0 = false := by
      cases h : P 2 0
      · rfl
      · exact absurd ⟨h, h21⟩ r2
    exact Or.inr ⟨0, 2, 1, by decide, by decide, by decide, h20, h12, h01⟩
  · have h02 : P 0 2 = false := by
      cases h : P 0 2
      · rfl
      · exact absurd ⟨h01, h⟩ r0
    have h20 : P 2 0 = true := by
      rcases pair 0 2 (by decide) with h | h
      · exact h
      · rw [h02] at h; exact absurd h (by simp)
    have h21 : P 2 1 = false := by
      cases h : P 2 1
      · rfl
      · exact absurd ⟨h20, h⟩ r2
    have h12 : P 1 2 = true := by
      rcases pair 1 2 (by decide) with h | h
      · rw [h21] at h; exact absurd h (by simp)
      · exact h
    have h10 : P 1 0 = false := by
      cases h : P 1 0
      · rfl
      · exact absurd ⟨h, h12⟩ r1
    exact Or.inr ⟨0, 1, 2, by decide, by decide, by decide, h10, h21, h02⟩

/-! ### HL Definition 3.4 and Lemma 3.12 -/

/-- HL Definition 3.4: the six bounding points. -/
structure LBounds (F : Pt 3 → Pt 3) (lo hi : Pt 3) (k : ℕ) : Type where
  /-- The `i`-upward bounding points. -/
  u : Fin 3 → Pt 3
  /-- The `i`-downward bounding points. -/
  dn : Fin 3 → Pt 3
  /-- All lie in the ambient box. -/
  u_mem : ∀ i, u i ∈ Box lo hi
  /-- All lie in the ambient box. -/
  dn_mem : ∀ i, dn i ∈ Box lo hi
  /-- All lie on the levelset. -/
  u_lev : ∀ i, lev (u i) = k
  /-- All lie on the levelset. -/
  dn_lev : ∀ i, lev (dn i) = k
  /-- `u⁽ⁱ⁾` is `i`-upward. -/
  u_up : ∀ i, IUp F (u i) i
  /-- `d⁽ⁱ⁾` is `i`-downward. -/
  dn_down : ∀ i, IDown F (dn i) i
  /-- HL Definition 3.4's ordering condition. -/
  ord : ∀ i, u i i ≤ dn i i

namespace LBounds

variable {F : Pt 3 → Pt 3} {lo hi : Pt 3} {k : ℕ} (B : LBounds F lo hi k)

/-- The lower corner `ℓᵢ = u⁽ⁱ⁾ᵢ`. -/
def lowC : Pt 3 := fun i => B.u i i

/-- The upper corner `rᵢ = d⁽ⁱ⁾ᵢ`. -/
def hiC : Pt 3 := fun i => B.dn i i

@[simp] lemma lowC_apply (i : Fin 3) : B.lowC i = B.u i i := rfl
@[simp] lemma hiC_apply (i : Fin 3) : B.hiC i = B.dn i i := rfl

lemma lowC_le_hiC : B.lowC ≤ B.hiC := coord_le fun i => B.ord i

end LBounds

/-- **HL Lemma 3.12**, combined with HL Observations 3.9 and 3.10.  Once some
extent of the search space has diameter at most one, either the bounding points
already yield progress — a first or second configuration, via `hasProgress_of_…` —
or one of the pairs `(u⁽ⁱ⁾, d⁽ⁱ⁾)` is in third configuration, which HL Lemma 3.13
then handles. -/
theorem hasProgress_or_config3 {F : Pt 3 → Pt 3} {lo hi : Pt 3} {k : ℕ}
    (B : LBounds F lo hi k)
    {i₀ : Fin 3} (hsmall : sDiam B.lowC B.hiC k i₀ ≤ 1) :
    HasProgress F lo hi k ∨ ∃ i, Config3 F i (B.u i) (B.dn i) := by
  -- Either some pair is in third configuration, or every width is at least two.
  by_cases hthird : ∃ i, B.dn i i ≤ B.u i i + 1
  · obtain ⟨i, hi⟩ := hthird
    exact Or.inr ⟨i, ⟨B.u_up i, B.dn_down i, B.ord i, hi⟩⟩
  push Not at hthird
  have hwide : ∀ i, B.lowC i + 2 ≤ B.hiC i := fun i => by
    have := hthird i; simp only [LBounds.lowC_apply, LBounds.hiC_apply]; omega
  refine Or.inl ?_
  rcases sDiam_cases hwide hsmall with hcase | hcase
  · -- `k ≤ |ℓ| + 1`: work with the upward points.
    have hrow : ∀ i j p : Fin 3, j ≠ i → p ≠ i → j ≠ p →
        ¬(decide (B.lowC j < B.u i j) = true ∧ decide (B.lowC p < B.u i p) = true) := by
      intro i j p hji hpi hjp ⟨h1, h2⟩
      simp only [decide_eq_true_eq, LBounds.lowC_apply] at h1 h2
      have hlev_u : lev (B.u i) = B.u i i + B.u i j + B.u i p :=
        lev_three _ (Ne.symm hji) (Ne.symm hpi) hjp
      have hlev_l : lev B.lowC = B.lowC i + B.lowC j + B.lowC p :=
        lev_three _ (Ne.symm hji) (Ne.symm hpi) hjp
      simp only [LBounds.lowC_apply] at hlev_l
      have := B.u_lev i
      omega
    rcases fin3_config_exists _ hrow with ⟨i, j, hij, h1, h2⟩ | ⟨i, j, p, hij, hip, hjp, h1, h2, h3⟩
    · simp only [decide_eq_false_iff_not, not_lt, LBounds.lowC_apply] at h1 h2
      exact hasProgress_of_config1Up (B.u_mem i) (B.u_mem j) (B.u_lev i)
        ⟨hij, B.u_up i, B.u_up j, h1, h2⟩
    · simp only [decide_eq_false_iff_not, not_lt, LBounds.lowC_apply] at h1 h2 h3
      exact hasProgress_of_config2Up (B.u_mem i) (B.u_mem j) (B.u_mem p) (B.u_lev i)
        ⟨hij, hip, hjp, B.u_up i, B.u_up j, B.u_up p, h1, h2, h3⟩
  · -- `|r| ≤ k + 1`: work with the downward points, symmetrically.
    have hrow : ∀ i j p : Fin 3, j ≠ i → p ≠ i → j ≠ p →
        ¬(decide (B.dn i j < B.hiC j) = true ∧ decide (B.dn i p < B.hiC p) = true) := by
      intro i j p hji hpi hjp ⟨h1, h2⟩
      simp only [decide_eq_true_eq, LBounds.hiC_apply] at h1 h2
      have hlev_d : lev (B.dn i) = B.dn i i + B.dn i j + B.dn i p :=
        lev_three _ (Ne.symm hji) (Ne.symm hpi) hjp
      have hlev_r : lev B.hiC = B.hiC i + B.hiC j + B.hiC p :=
        lev_three _ (Ne.symm hji) (Ne.symm hpi) hjp
      simp only [LBounds.hiC_apply] at hlev_r
      have := B.dn_lev i
      omega
    rcases fin3_config_exists _ hrow with ⟨i, j, hij, h1, h2⟩ | ⟨i, j, p, hij, hip, hjp, h1, h2, h3⟩
    · simp only [decide_eq_false_iff_not, not_lt, LBounds.hiC_apply] at h1 h2
      exact hasProgress_of_config1Down (B.dn_mem i) (B.dn_mem j) (B.dn_lev i)
        ⟨hij, B.dn_down i, B.dn_down j, h1, h2⟩
    · simp only [decide_eq_false_iff_not, not_lt, LBounds.hiC_apply] at h1 h2 h3
      exact hasProgress_of_config2Down (B.dn_mem i) (B.dn_mem j) (B.dn_mem p) (B.dn_lev i)
        ⟨hij, hip, hjp, B.dn_down i, B.dn_down j, B.dn_down p, h1, h2, h3⟩

/-! ### HL Lemma 3.5: the shrinking query point

A query point must be *deep* in the search space in **every** coordinate at once,
since the answer decides only afterwards which coordinate gets cut.  The slack
`⌈diamᵢ/6⌉` per coordinate is what makes the level constraint satisfiable: the
three slacks together consume at most the largest diameter, and there is always a
point of `L_k` that far inside.

The two sum bounds below are the crux, and each comes from *one* attained extent:
pushing coordinate `i₀` to its upper extent shows `Σⱼ sLoⱼ + diam_{i₀} ≤ k`, and
pushing it to its lower extent shows `k + diam_{i₀} ≤ Σⱼ sHiⱼ`. -/

lemma lev_eq_three (x : Pt 3) : lev x = x 0 + x 1 + x 2 := by
  simp [lev, Fin.sum_univ_three]

section Deep

variable {ℓ r : Pt 3} {k : ℕ}

/-- Pushing one coordinate to its upper extent bounds the sum of the lower
extents. -/
lemma sum_sLo_add_sDiam_le (hlr : ℓ ≤ r) (hlk : lev ℓ ≤ k) (hkr : k ≤ lev r) (i₀ : Fin 3) :
    sLo ℓ r k 0 + sLo ℓ r k 1 + sLo ℓ r k 2 + sDiam ℓ r k i₀ ≤ k := by
  obtain ⟨x, hx, hxi⟩ := sHi_attained hlr hlk hkr i₀
  have h0 := mem_SSet_bounds hx 0
  have h1 := mem_SSet_bounds hx 1
  have h2 := mem_SSet_bounds hx 2
  have hlev : x 0 + x 1 + x 2 = k := by rw [← lev_eq_three]; exact hx.1
  have hd : sDiam ℓ r k i₀ = sHi ℓ r k i₀ - sLo ℓ r k i₀ := rfl
  have hle := sLo_le_sHi hlr hlk hkr i₀
  fin_cases i₀ <;> simp_all <;> omega

/-- Pushing one coordinate to its lower extent bounds the sum of the upper
extents. -/
lemma le_sum_sHi_sub_sDiam (hlr : ℓ ≤ r) (hlk : lev ℓ ≤ k) (hkr : k ≤ lev r) (i₀ : Fin 3) :
    k + sDiam ℓ r k i₀ ≤ sHi ℓ r k 0 + sHi ℓ r k 1 + sHi ℓ r k 2 := by
  obtain ⟨x, hx, hxi⟩ := sLo_attained hlr hlk hkr i₀
  have h0 := mem_SSet_bounds hx 0
  have h1 := mem_SSet_bounds hx 1
  have h2 := mem_SSet_bounds hx 2
  have hlev : x 0 + x 1 + x 2 = k := by rw [← lev_eq_three]; exact hx.1
  have hd : sDiam ℓ r k i₀ = sHi ℓ r k i₀ - sLo ℓ r k i₀ := rfl
  have hle := sLo_le_sHi hlr hlk hkr i₀
  fin_cases i₀ <;> simp_all <;> omega

/-- HL's slack `⌈diamᵢ/6⌉`. -/
def slack (ℓ r : Pt 3) (k : ℕ) (i : Fin 3) : ℕ := (sDiam ℓ r k i + 5) / 6

/-- **HL Lemma 3.5.**  If every extent has diameter at least two and some extent has
diameter at least six, there is a point of the search space at least `⌈diamᵢ/6⌉`
from both ends in every coordinate `i`.  Querying it therefore cuts whichever
coordinate the answer implicates down to at most `5/6` of its diameter
(`sDiam_shrink_up`, `sDiam_shrink_down`). -/
theorem exists_deep_query (hlr : ℓ ≤ r) (hlk : lev ℓ ≤ k) (hkr : k ≤ lev r)
    {D : ℕ} (hD : ∀ i, sDiam ℓ r k i ≤ D) (hD6 : 6 ≤ D)
    {i₀ : Fin 3} (hattained : D ≤ sDiam ℓ r k i₀)
    (hbig : ∀ i, 2 ≤ sDiam ℓ r k i) :
    ∃ q, q ∈ SSet ℓ r k ∧ ∀ i,
      sLo ℓ r k i + slack ℓ r k i ≤ q i ∧ q i + slack ℓ r k i ≤ sHi ℓ r k i := by
  -- the two straddling corners
  set a : Pt 3 := fun i => sLo ℓ r k i + slack ℓ r k i with ha
  set b : Pt 3 := fun i => sHi ℓ r k i - slack ℓ r k i with hb
  have hslack : ∀ i, 2 * slack ℓ r k i ≤ sDiam ℓ r k i := by
    intro i
    have := hbig i
    simp only [slack]
    omega
  have hdiam : ∀ i, sDiam ℓ r k i = sHi ℓ r k i - sLo ℓ r k i := fun _ => rfl
  have hle : ∀ i, sLo ℓ r k i ≤ sHi ℓ r k i := fun i => sLo_le_sHi hlr hlk hkr i
  have hab : a ≤ b := by
    refine coord_le fun i => ?_
    have h1 := hslack i
    have h2 := hdiam i
    have h3 := hle i
    simp only [ha, hb]
    omega
  -- the slacks together consume at most the largest diameter
  have hslack_sum : slack ℓ r k 0 + slack ℓ r k 1 + slack ℓ r k 2 ≤ D := by
    have h0 := hD 0
    have h1 := hD 1
    have h2 := hD 2
    simp only [slack]
    omega
  have hlev_a : lev a ≤ k := by
    have hsum := sum_sLo_add_sDiam_le hlr hlk hkr i₀
    have := hattained
    rw [lev_eq_three]
    simp only [ha]
    omega
  have hlev_b : k ≤ lev b := by
    have hsum := le_sum_sHi_sub_sDiam hlr hlk hkr i₀
    have := hattained
    have h0 := hslack 0
    have h1 := hslack 1
    have h2 := hslack 2
    have g0 := hdiam 0
    have g1 := hdiam 1
    have g2 := hdiam 2
    rw [lev_eq_three]
    simp only [hb]
    omega
  obtain ⟨q, hqa, hqb, hqlev⟩ := exists_lev_between hab hlev_a hlev_b
  refine ⟨q, ⟨hqlev, coord_le fun i => ?_, coord_le fun i => ?_⟩, fun i => ?_⟩
  · -- `ℓ i ≤ sLo i ≤ a i ≤ q i`
    have h1 : ℓ i ≤ sLo ℓ r k i := le_max_left _ _
    have h2 := le_coord hqa i
    simp only [ha] at h2
    omega
  · -- `q i ≤ b i ≤ sHi i ≤ r i`
    have h1 : sHi ℓ r k i ≤ r i := min_le_left _ _
    have h2 := le_coord hqb i
    simp only [hb] at h2
    omega
  · have h1 := le_coord hqa i
    have h2 := le_coord hqb i
    have h3 := hslack i
    have h4 := hdiam i
    have h5 := hle i
    simp only [ha] at h1
    simp only [hb] at h2
    omega

end Deep

/-! ### The effect of a cut

Replacing `u⁽ⁱ⁾` by the queried point `q` raises `ℓᵢ` to `qᵢ` and leaves everything
else alone.  In coordinate `i` the upper extent is *unchanged* — raising `ℓᵢ` and
raising `|ℓ|` by the same amount cancel in `k + ℓᵢ − |ℓ|` — so the diameter there
drops to `sHiᵢ − qᵢ ≤ diamᵢ − ⌈diamᵢ/6⌉`.  In the other coordinates the extents can
only move inwards. -/

section Cut

variable {ℓ r : Pt 3} {k : ℕ}

/-- Raising `ℓ` in coordinate `i` leaves `k + ℓᵢ − |ℓ|` unchanged. -/
lemma sHi_update_self (i : Fin 3) (v : ℕ) (_hv : ℓ i ≤ v) :
    sHi (Function.update ℓ i v) r k i = sHi ℓ r k i := by
  have h := lev_update ℓ i v
  have hli : ℓ i ≤ lev ℓ := coord_le_lev ℓ i
  simp only [sHi, Function.update_self]
  congr 1
  omega

lemma sLo_update_self (i : Fin 3) (v : ℕ) (hv : k + r i - lev r ≤ v) :
    sLo (Function.update ℓ i v) r k i = v := by
  simp only [sLo, Function.update_self]
  omega

/-- In the other coordinates a cut can only shrink the extents. -/
lemma sDiam_update_other (i j : Fin 3) (hij : j ≠ i) (v : ℕ) (_hv : ℓ i ≤ v) :
    sDiam (Function.update ℓ i v) r k j ≤ sDiam ℓ r k j := by
  have h := lev_update ℓ i v
  have hli : ℓ i ≤ lev ℓ := coord_le_lev ℓ i
  simp only [sDiam, sLo, sHi, Function.update_of_ne hij]
  omega

/-- **The 5/6 shrink.**  Cutting at a deep query point reduces the diameter in the
cut coordinate to at most five sixths of its former value. -/
theorem sDiam_shrink (hlr : ℓ ≤ r) (hlk : lev ℓ ≤ k) (hkr : k ≤ lev r) (i : Fin 3)
    {q : Pt 3} (hq : q ∈ SSet ℓ r k)
    (hdeep : sLo ℓ r k i + slack ℓ r k i ≤ q i) :
    6 * sDiam (Function.update ℓ i (q i)) r k i ≤ 5 * sDiam ℓ r k i := by
  have hqlo := (mem_SSet_bounds hq i).1
  have hqhi := (mem_SSet_bounds hq i).2
  have hli : ℓ i ≤ q i := le_trans (le_max_left _ _) hqlo
  have hlo : k + r i - lev r ≤ q i := le_trans (le_max_right _ _) hqlo
  rw [sDiam, sHi_update_self i (q i) hli, sLo_update_self i (q i) hlo]
  have hd : sDiam ℓ r k i = sHi ℓ r k i - sLo ℓ r k i := rfl
  have hs : slack ℓ r k i = (sDiam ℓ r k i + 5) / 6 := rfl
  have hle := sLo_le_sHi hlr hlk hkr i
  omega


/-! #### The dual: lowering the upper corner

A cut at an `i`-*downward* point lowers `r i` instead.  Now it is the *lower*
extent in coordinate `i` that is unchanged — lowering `r i` and `|r|` by the same
amount cancels in `k + r i − |r|` — and the diameter drops to `q i − sLoᵢ`. -/

/-- Lowering `r` in coordinate `i` leaves `k + rᵢ − |r|` unchanged. -/
lemma sLo_update_self_down (i : Fin 3) (v : ℕ) (_hv : v ≤ r i) :
    sLo ℓ (Function.update r i v) k i = sLo ℓ r k i := by
  have h := lev_update r i v
  have hri : r i ≤ lev r := coord_le_lev r i
  simp only [sLo, Function.update_self]
  congr 1
  omega

lemma sHi_update_self_down (i : Fin 3) (v : ℕ) :
    sHi ℓ (Function.update r i v) k i = min v (k + ℓ i - lev ℓ) := by
  simp only [sHi, Function.update_self]

/-- In the other coordinates a downward cut can only shrink the extents. -/
lemma sDiam_update_other_down (i j : Fin 3) (hij : j ≠ i) (v : ℕ) (_hv : v ≤ r i) :
    sDiam ℓ (Function.update r i v) k j ≤ sDiam ℓ r k j := by
  have h := lev_update r i v
  have hri : r i ≤ lev r := coord_le_lev r i
  simp only [sDiam, sLo, sHi, Function.update_of_ne hij]
  omega

/-- **The 5/6 shrink, downward form.** -/
theorem sDiam_shrink_down (hlr : ℓ ≤ r) (hlk : lev ℓ ≤ k) (hkr : k ≤ lev r) (i : Fin 3)
    {q : Pt 3} (hq : q ∈ SSet ℓ r k)
    (hdeep : q i + slack ℓ r k i ≤ sHi ℓ r k i) :
    6 * sDiam ℓ (Function.update r i (q i)) k i ≤ 5 * sDiam ℓ r k i := by
  have hqlo := (mem_SSet_bounds hq i).1
  have hqhi := (mem_SSet_bounds hq i).2
  have hri : q i ≤ r i := le_trans hqhi (min_le_left _ _)
  have hup : q i ≤ k + ℓ i - lev ℓ := le_trans hqhi (min_le_right _ _)
  rw [sDiam, sHi_update_self_down i (q i), sLo_update_self_down i (q i) hri]
  have hd : sDiam ℓ r k i = sHi ℓ r k i - sLo ℓ r k i := rfl
  have hs : slack ℓ r k i = (sDiam ℓ r k i + 5) / 6 := rfl
  have hle := sLo_le_sHi hlr hlk hkr i
  have hmin : min (q i) (k + ℓ i - lev ℓ) = q i := min_eq_left hup
  rw [hmin]
  omega

end Cut

/-! ### The product measure, and `Shrinking.lean`

A single cut shrinks one diameter by `5/6` and cannot grow the others, so the
product `Πᵢ (diamᵢ + 1)` shrinks by `8/9`: for `d ≥ 2` and `6d' ≤ 5d` one has
`9(d' + 1) ≤ 8(d + 1)`.  That is exactly the hypothesis of `Tfnp.iterate_shrinking`
with `p = 9`, which then bounds the number of cuts logarithmically. -/

/-- The measure driving HL's shrinking loop. -/
def sMeasure (ℓ r : Pt 3) (k : ℕ) : ℕ :=
  (sDiam ℓ r k 0 + 1) * (sDiam ℓ r k 1 + 1) * (sDiam ℓ r k 2 + 1)

/-- A cut shrinks the product measure by a factor `8/9`. -/
theorem sMeasure_shrink {ℓ ℓ' r : Pt 3} {k : ℕ} {i : Fin 3}
    (hcut : 6 * sDiam ℓ' r k i ≤ 5 * sDiam ℓ r k i)
    (hother : ∀ j, j ≠ i → sDiam ℓ' r k j ≤ sDiam ℓ r k j)
    (hbig : 2 ≤ sDiam ℓ r k i) :
    9 * sMeasure ℓ' r k ≤ 8 * sMeasure ℓ r k := by
  -- the cut coordinate gains the factor `8/9`, the others do not grow
  have key : 9 * (sDiam ℓ' r k i + 1) ≤ 8 * (sDiam ℓ r k i + 1) := by omega
  have hmul : ∀ A' A B' B C' C : ℕ, 9 * (A' + 1) ≤ 8 * (A + 1) → B' ≤ B → C' ≤ C →
      9 * ((A' + 1) * (B' + 1) * (C' + 1)) ≤ 8 * ((A + 1) * (B + 1) * (C + 1)) := by
    intro A' A B' B C' C h1 h2 h3
    calc 9 * ((A' + 1) * (B' + 1) * (C' + 1))
        = (9 * (A' + 1)) * ((B' + 1) * (C' + 1)) := by ring
      _ ≤ (8 * (A + 1)) * ((B + 1) * (C + 1)) := by
          exact Nat.mul_le_mul h1 (Nat.mul_le_mul (by omega) (by omega))
      _ = 8 * ((A + 1) * (B + 1) * (C + 1)) := by ring
  -- reduce to the three coordinates, with `i` in the cut position
  fin_cases i
  · exact hmul _ _ _ _ _ _ key (hother 1 (by decide)) (hother 2 (by decide))
  · have h := hmul (sDiam ℓ' r k 1) (sDiam ℓ r k 1) (sDiam ℓ' r k 0) (sDiam ℓ r k 0)
      (sDiam ℓ' r k 2) (sDiam ℓ r k 2) key (hother 0 (by decide)) (hother 2 (by decide))
    simp only [sMeasure]
    calc 9 * ((sDiam ℓ' r k 0 + 1) * (sDiam ℓ' r k 1 + 1) * (sDiam ℓ' r k 2 + 1))
        = 9 * ((sDiam ℓ' r k 1 + 1) * (sDiam ℓ' r k 0 + 1) * (sDiam ℓ' r k 2 + 1)) := by ring
      _ ≤ 8 * ((sDiam ℓ r k 1 + 1) * (sDiam ℓ r k 0 + 1) * (sDiam ℓ r k 2 + 1)) := h
      _ = 8 * ((sDiam ℓ r k 0 + 1) * (sDiam ℓ r k 1 + 1) * (sDiam ℓ r k 2 + 1)) := by ring
  · have h := hmul (sDiam ℓ' r k 2) (sDiam ℓ r k 2) (sDiam ℓ' r k 0) (sDiam ℓ r k 0)
      (sDiam ℓ' r k 1) (sDiam ℓ r k 1) key (hother 0 (by decide)) (hother 1 (by decide))
    simp only [sMeasure]
    calc 9 * ((sDiam ℓ' r k 0 + 1) * (sDiam ℓ' r k 1 + 1) * (sDiam ℓ' r k 2 + 1))
        = 9 * ((sDiam ℓ' r k 2 + 1) * (sDiam ℓ' r k 0 + 1) * (sDiam ℓ' r k 1 + 1)) := by ring
      _ ≤ 8 * ((sDiam ℓ r k 2 + 1) * (sDiam ℓ r k 0 + 1) * (sDiam ℓ r k 1 + 1)) := h
      _ = 8 * ((sDiam ℓ r k 0 + 1) * (sDiam ℓ r k 1 + 1) * (sDiam ℓ r k 2 + 1)) := by ring

/-- The number of cuts is logarithmic: this is `Tfnp.iterate_shrinking` at `p = 9`,
applied to `sMeasure`. -/
theorem sMeasure_iterate {α : Type} (a₀ : α) (step : α → α) (μ : α → ℕ)
    (h : ∀ a, 9 * μ (step a) ≤ 8 * μ a) (N : ℕ) :
    9 ^ N * μ (step^[N] a₀) ≤ 8 ^ N * μ a₀ := by
  have := Tfnp.iterate_shrinking 9 a₀ step μ (by intro a; have := h a; omega) N
  simpa using this

/-! ### HL Lemma 3.6: the constant-size endgame

Lemma 3.5 needs some diameter at least six.  When all three are between two and
five the search space is too small for that, and HL query three explicit *corner*
points instead: `cornerPt i` sits at the lower extent in coordinate `i` and one
above it in the other two.  Each lies on the levelset precisely when
`k = Σⱼ sLoⱼ + 2`, which is exactly what being stuck forces (`stuck_levels`).

If some corner fails to be `i`-upward the algorithm can cut; and if all three *are*
`i`-upward, their join is an upward point one level above `k` — the endgame. -/

section Small

variable {F : Pt 3 → Pt 3} {lo hi : Pt 3} {ℓ r : Pt 3} {k : ℕ}

/-- HL's corner point `q⁽ⁱ⁾`: at the lower extent in coordinate `i`, one above it in
the other two. -/
def cornerPt (ℓ r : Pt 3) (k : ℕ) (i : Fin 3) : Pt 3 :=
  fun j => if j = i then sLo ℓ r k i else sLo ℓ r k j + 1

/-- The join of the three corner points: one above the lower extent everywhere. -/
def cornerJoin (ℓ r : Pt 3) (k : ℕ) : Pt 3 := fun j => sLo ℓ r k j + 1

/-- The corner points lie on the levelset exactly when `k = Σⱼ sLoⱼ + 2`. -/
lemma lev_cornerPt (i : Fin 3) :
    lev (cornerPt ℓ r k i) = sLo ℓ r k 0 + sLo ℓ r k 1 + sLo ℓ r k 2 + 2 := by
  rw [lev_eq_three]
  fin_cases i <;> simp [cornerPt] <;> omega

lemma cornerPt_le_cornerJoin (i : Fin 3) : cornerPt ℓ r k i ≤ cornerJoin ℓ r k := by
  refine coord_le fun j => ?_
  by_cases hj : j = i
  · subst hj; simp [cornerPt, cornerJoin]
  · simp [cornerPt, cornerJoin, hj]

/-- **Being stuck pins down the level.**  If no point of the search space is
strictly inside every extent, then `k` is two above the sum of the lower extents,
or two below the sum of the upper ones.

The forward direction of HL's deduction: the failure gives one of the two
inequalities, and `sum_sLo_add_sDiam_le` (resp. `le_sum_sHi_sub_sDiam`) with any
coordinate — whose diameter is at least two — supplies the converse. -/
theorem stuck_levels (hlr : ℓ ≤ r) (hlk : lev ℓ ≤ k) (hkr : k ≤ lev r)
    (hbig : ∀ i, 2 ≤ sDiam ℓ r k i)
    (hstuck : ¬ ∃ q, q ∈ SSet ℓ r k ∧ ∀ i, sLo ℓ r k i < q i ∧ q i < sHi ℓ r k i) :
    k = sLo ℓ r k 0 + sLo ℓ r k 1 + sLo ℓ r k 2 + 2
      ∨ k + 2 = sHi ℓ r k 0 + sHi ℓ r k 1 + sHi ℓ r k 2 := by
  have hb0 := hbig 0
  have hb1 := hbig 1
  have hb2 := hbig 2
  have hd : ∀ i, sDiam ℓ r k i = sHi ℓ r k i - sLo ℓ r k i := fun _ => rfl
  have hle : ∀ i, sLo ℓ r k i ≤ sHi ℓ r k i := fun i => sLo_le_sHi hlr hlk hkr i
  have hlow := sum_sLo_add_sDiam_le hlr hlk hkr 0
  have hhigh := le_sum_sHi_sub_sDiam hlr hlk hkr 0
  have h0 := hd 0
  have h1 := hd 1
  have h2 := hd 2
  -- if `k` were strictly between, a strictly interior point would exist
  by_contra hcon
  push Not at hcon
  obtain ⟨hne1, hne2⟩ := hcon
  refine hstuck ?_
  have hmid : ∀ i, sLo ℓ r k i + 1 ≤ sHi ℓ r k i - 1 := by
    intro i; have := hbig i; have := hd i; have := hle i; omega
  have hab : (fun i => sLo ℓ r k i + 1 : Pt 3) ≤ (fun i => sHi ℓ r k i - 1 : Pt 3) :=
    coord_le fun i => hmid i
  have hlev_a : lev (fun i => sLo ℓ r k i + 1 : Pt 3) ≤ k := by
    rw [lev_eq_three]; omega
  have hlev_b : k ≤ lev (fun i => sHi ℓ r k i - 1 : Pt 3) := by
    rw [lev_eq_three]; omega
  obtain ⟨q, hqa, hqb, hqlev⟩ := exists_lev_between hab hlev_a hlev_b
  refine ⟨q, ⟨hqlev, coord_le fun i => ?_, coord_le fun i => ?_⟩, fun i => ?_⟩
  · have h := le_coord hqa i
    have h' : ℓ i ≤ sLo ℓ r k i := le_max_left _ _
    simp only at h
    omega
  · have h := le_coord hqb i
    have h' : sHi ℓ r k i ≤ r i := min_le_left _ _
    simp only at h
    omega
  · have ha := le_coord hqa i
    have hb := le_coord hqb i
    have := hmid i
    simp only at ha hb
    omega

/-- **The endgame of HL Lemma 3.6.**  If every corner point is `i`-upward in its own
coordinate, their join is an upward point at level `k + 1` — so progress.  (In the
total setting, unless one of the three monotonicity steps exposes a violation.) -/
theorem hasProgress_of_corner_up (hlo : lo ≤ ℓ) (hr : r ≤ hi)
    (hbig : ∀ i, 2 ≤ sDiam ℓ r k i) (hlr : ℓ ≤ r) (hlk : lev ℓ ≤ k) (hkr : k ≤ lev r)
    (hk : k = sLo ℓ r k 0 + sLo ℓ r k 1 + sLo ℓ r k 2 + 2)
    (hcorner : ∀ i, IUp F (cornerPt ℓ r k i) i) :
    HasProgress F lo hi k := by
  set J := cornerJoin ℓ r k with hJ
  have hJmem : J ∈ Box lo hi := by
    refine mem_Box.mpr ⟨coord_le fun j => ?_, coord_le fun j => ?_⟩
    · have h1 : lo j ≤ ℓ j := le_coord hlo j
      have h2 : ℓ j ≤ sLo ℓ r k j := le_max_left _ _
      simp only [hJ, cornerJoin]; omega
    · have h1 : r j ≤ hi j := le_coord hr j
      have h2 : sHi ℓ r k j ≤ r j := min_le_left _ _
      have h3 := hbig j
      have h4 : sDiam ℓ r k j = sHi ℓ r k j - sLo ℓ r k j := rfl
      have h5 : sLo ℓ r k j ≤ sHi ℓ r k j := sLo_le_sHi hlr hlk hkr j
      simp only [hJ, cornerJoin]; omega
  have hcmem : ∀ i, cornerPt ℓ r k i ∈ Box lo hi := by
    intro i
    refine mem_Box.mpr ⟨coord_le fun j => ?_,
      (cornerPt_le_cornerJoin i).trans (mem_Box.mp hJmem).2⟩
    have h1 : lo j ≤ ℓ j := le_coord hlo j
    have h2 : ℓ j ≤ sLo ℓ r k j := le_max_left _ _
    have h3 : cornerPt ℓ r k i j = sLo ℓ r k j ∨ cornerPt ℓ r k i j = sLo ℓ r k j + 1 := by
      by_cases hj : j = i
      · subst hj; exact Or.inl (by simp [cornerPt])
      · exact Or.inr (by simp [cornerPt, hj])
    rcases h3 with h3 | h3 <;> omega
  -- monotonicity at each corner, or a violation
  by_cases hviol : ∃ i, ¬ F (cornerPt ℓ r k i) ≤ F J
  · obtain ⟨i, hi⟩ := hviol
    exact Or.inr (Or.inr ⟨cornerPt ℓ r k i, J, hcmem i, hJmem,
      ⟨cornerPt_le_cornerJoin i, hi⟩⟩)
  push Not at hviol
  refine Or.inl ⟨J, hJmem, ?_, mem_Up.mpr (coord_le fun j => ?_)⟩
  · -- the join sits at level `k + 1`
    have hlev : lev J = sLo ℓ r k 0 + sLo ℓ r k 1 + sLo ℓ r k 2 + 3 := by
      rw [lev_eq_three]; simp only [hJ, cornerJoin]; omega
    omega
  · -- coordinate `j`: the `j`-th corner already pushes `F` past `J j`
    have h1 := (hcorner j).1
    have h2 : cornerPt ℓ r k j j = sLo ℓ r k j := by simp [cornerPt]
    have h3 := le_coord (hviol j) j
    have h4 : J j = sLo ℓ r k j + 1 := rfl
    omega

end Small

end Tfnp.Tarski
