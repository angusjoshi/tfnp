/-
Copyright (c) 2026 Angus Joshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Angus Joshi
-/
import Tfnp.Margin

/-!
# The walk lemma and the pair-record theorem: 2-simple cells are `O(d²t)`

The counting engine behind the measured cell law (`notes/CHAIN.md`). Two
results:

* `ncard_range_signPattern_le` — **the walk lemma**: the ternary sign pattern
  of a real number against `t` thresholds takes at most `2t + 1` values.
  (The thresholds are the pair-form values of the trajectory's apexes — the
  "marching offsets"; a point's relation to the whole walk is an interval
  datum.)

* `pair_membership_iff` — **the pair-record theorem**: for a 2-simple point
  (tied pair `{i₁, i₂}` with signs `(ε₁, ε₂)`, both pair offsets above `2δ`,
  all other coordinates `2δ` below the pair's top), membership in the
  `i₁`-pyramid of ANY apex within `δ` is decided by the single inequality
  `ε₂(yᵢ₂ − c'ᵢ₂) ≤ ε₁(yᵢ₁ − c'ᵢ₁)` — that is, by the sign of
  `φ(y) − φ(c')` for the ONE linear form `φ(z) = ε₁ zᵢ₁ − ε₂ zᵢ₂`.

**Composite count (the two lemmas together).** Fix a cut trajectory with
apexes within `δ` of a reference and any ternary sign vectors. For 2-simple
survivors with pair `{i₁,i₂}` and pattern `(ε₁,ε₂)`: by `pair_membership_iff`
(with `pyr_index_mem_pair_of_2simple` confining the argmax to the pair),
the full membership record over all `t` cuts is a function of
`(sgnR (φ(y) − φ(c_r)))_{r≤t}` — a sign pattern against `t` thresholds — so
by the walk lemma it takes at most `2t + 1` values. Summing over the
`d(d−1)/2` pairs and `4` sign patterns:

> **2-simple survivors of a `t`-cut trajectory occupy at most
> `2·d(d−1)·(2t+1) = O(d²t)` cells** — matching the measured `≈ 2–3·d·t`
> effective-cell law almost exactly, and improving the earlier paper
> bookkeeping (`O(d²t²)`): given the sign pattern, ONE form decides
> everything.

With `cell_eq_of_onedeep` (1-deep points: ≤ `2d` cells) this makes the
trichotomy's provable levels fully machine-checked; the open remainder of
(★) is exactly the sub-threshold shedding ledger (`notes/CHAIN.md`, (SHED)).
-/

set_option autoImplicit false

namespace Tfnp.Contraction

/-! ## The walk lemma -/

/-- **The walk lemma.** The ternary sign pattern of `x` against `t`
thresholds takes at most `2t + 1` values as `x` ranges over `ℝ`: the pattern
is determined by the position of `x` in the sorted threshold list. -/
theorem ncard_range_signPattern_le {t : ℕ} (a : Fin t → ℝ) :
    Set.ncard (Set.range fun x : ℝ => fun r => sgnR (x - a r)) ≤ 2 * t + 1 := by
  classical
  set n : ℝ → ℕ := fun x =>
    (Finset.univ.filter fun r => a r < x).card
      + (Finset.univ.filter fun r => a r ≤ x).card with hn
  -- the pattern is a function of the count `n x`
  have main : ∀ x y : ℝ, x ≤ y → n x = n y →
      ∀ r, sgnR (x - a r) = sgnR (y - a r) := by
    intro x y hxy hnn r
    have hsub1 : (Finset.univ.filter fun r => a r < x)
        ⊆ (Finset.univ.filter fun r => a r < y) := by
      intro s hs
      simp only [Finset.mem_filter] at hs ⊢
      exact ⟨hs.1, lt_of_lt_of_le hs.2 hxy⟩
    have hsub2 : (Finset.univ.filter fun r => a r ≤ x)
        ⊆ (Finset.univ.filter fun r => a r ≤ y) := by
      intro s hs
      simp only [Finset.mem_filter] at hs ⊢
      exact ⟨hs.1, le_trans hs.2 hxy⟩
    have hc1 := Finset.card_le_card hsub1
    have hc2 := Finset.card_le_card hsub2
    have he1 : (Finset.univ.filter fun r => a r < x).card
        = (Finset.univ.filter fun r => a r < y).card := by
      simp only [hn] at hnn; omega
    have he2 : (Finset.univ.filter fun r => a r ≤ x).card
        = (Finset.univ.filter fun r => a r ≤ y).card := by
      simp only [hn] at hnn; omega
    have hq1 := Finset.eq_of_subset_of_card_le hsub1 he1.ge
    have hq2 := Finset.eq_of_subset_of_card_le hsub2 he2.ge
    have hmem1 : a r < x ↔ a r < y := by
      constructor <;> intro h
      · have : r ∈ Finset.univ.filter fun r => a r < x := by
          simp only [Finset.mem_filter]; exact ⟨Finset.mem_univ r, h⟩
        rw [hq1] at this
        simpa using this
      · have : r ∈ Finset.univ.filter fun r => a r < y := by
          simp only [Finset.mem_filter]; exact ⟨Finset.mem_univ r, h⟩
        rw [← hq1] at this
        simpa using this
    have hmem2 : a r ≤ x ↔ a r ≤ y := by
      constructor <;> intro h
      · have : r ∈ Finset.univ.filter fun r => a r ≤ x := by
          simp only [Finset.mem_filter]; exact ⟨Finset.mem_univ r, h⟩
        rw [hq2] at this
        simpa using this
      · have : r ∈ Finset.univ.filter fun r => a r ≤ y := by
          simp only [Finset.mem_filter]; exact ⟨Finset.mem_univ r, h⟩
        rw [← hq2] at this
        simpa using this
    rcases lt_trichotomy (a r) x with h | h | h
    · rw [sgnR_of_pos (by linarith), sgnR_of_pos (by linarith [hmem1.mp h])]
    · have h1 : a r ≤ y := hmem2.mp h.le
      have h2 : ¬(a r < y) := by
        intro hc
        have h3 : a r < x := hmem1.mpr hc
        rw [h] at h3
        exact lt_irrefl x h3
      have hy_eq : a r = y := le_antisymm h1 (not_lt.mp h2)
      have e1 : x - a r = 0 := by rw [h]; ring
      have e2 : y - a r = 0 := by rw [hy_eq]; ring
      rw [e1, e2]
    · have h1 : ¬(a r ≤ x) := not_le.mpr h
      have h2 : ¬(a r ≤ y) := fun hc => h1 (hmem2.mpr hc)
      have hy_gt : y < a r := not_le.mp h2
      rw [sgnR_of_neg (by linarith), sgnR_of_neg (by linarith)]
  have hdet : ∀ x y : ℝ, n x = n y →
      (fun r => sgnR (x - a r)) = fun r => sgnR (y - a r) := by
    intro x y hnn
    rcases le_total x y with h | h
    · funext r; exact main x y h hnn r
    · funext r; exact (main y x h hnn.symm r).symm
  have hbound : ∀ x, n x < 2 * t + 1 := by
    intro x
    have h1 : (Finset.univ.filter fun r => a r < x).card ≤ t := by
      refine le_trans (Finset.card_filter_le _ _) ?_
      simp
    have h2 : (Finset.univ.filter fun r => a r ≤ x).card ≤ t := by
      refine le_trans (Finset.card_filter_le _ _) ?_
      simp
    simp only [hn]; omega
  set g : ℕ → (Fin t → ℝ) := fun m =>
    if h : ∃ x : ℝ, n x = m
    then (fun r => sgnR (Classical.choose h - a r))
    else fun _ => 0 with hg
  have hfact : ∀ x : ℝ, (fun r => sgnR (x - a r)) = g (n x) := by
    intro x
    have hex : ∃ z : ℝ, n z = n x := ⟨x, rfl⟩
    simp only [hg, dif_pos hex]
    exact (hdet _ _ (Classical.choose_spec hex)).symm
  have hsubset : (Set.range fun x : ℝ => fun r => sgnR (x - a r))
      ⊆ ↑((Finset.range (2 * t + 1)).image g) := by
    rintro v ⟨x, rfl⟩
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe,
      Finset.mem_range]
    exact ⟨n x, hbound x, (hfact x).symm⟩
  calc Set.ncard (Set.range fun x : ℝ => fun r => sgnR (x - a r))
      ≤ Set.ncard (↑((Finset.range (2 * t + 1)).image g) : Set (Fin t → ℝ)) :=
        Set.ncard_le_ncard hsubset (Finset.finite_toSet _)
    _ = ((Finset.range (2 * t + 1)).image g).card := Set.ncard_coe_finset _
    _ ≤ (Finset.range (2 * t + 1)).card := Finset.card_image_le
    _ = 2 * t + 1 := Finset.card_range _

/-! ## The pair-record theorem -/

variable {k : ℕ} [NeZero k]

/-- **The pair-record theorem.** For a 2-simple point at pair `{i₁, i₂}` with
signs `(ε₁, ε₂)`, membership in the `i₁`-pyramid of any apex within `δ` is
decided by the single linear comparison `ε₂(yᵢ₂ − c'ᵢ₂) ≤ ε₁(yᵢ₁ − c'ᵢ₁)` —
the sign of `φ(y) − φ(c')` for `φ(z) = ε₁ zᵢ₁ − ε₂ zᵢ₂`. With the walk lemma,
the entire `t`-cut record of the 2-simple stratum is `O(d²t)` classes. -/
theorem pair_membership_iff {c c' y : Vec k} {i₁ i₂ : Fin k} {ε₁ ε₂ : ℝ}
    (hε₁ : ε₁ = 1 ∨ ε₁ = -1) (hε₂ : ε₂ = 1 ∨ ε₂ = -1) {δ : ℝ}
    (hδ : linfDist c' c ≤ δ)
    (hy₁ : 2 * δ < ε₁ * (y i₁ - c i₁)) (hy₂ : 2 * δ < ε₂ * (y i₂ - c i₂))
    (hgap : ∀ j, j ≠ i₁ → j ≠ i₂ →
      |y j - c j| + 2 * δ < max (|y i₁ - c i₁|) (|y i₂ - c i₂|))
    {τ : ℝ} (hτ : τ = 1 ∨ τ = -1) :
    y ∈ Pyr i₁ τ c' ↔
      (τ = ε₁ ∧ ε₂ * (y i₂ - c' i₂) ≤ ε₁ * (y i₁ - c' i₁)) := by
  have hδ0 : 0 ≤ δ := le_trans (linfDist_nonneg c' c) hδ
  have hshift : ∀ m, |c' m - c m| ≤ δ :=
    fun m => (abs_sub_le_linfDist c' c m).trans hδ
  -- signed pair offsets at the perturbed apex stay above δ
  have hstab : ∀ (ε : ℝ) (m : Fin k), (ε = 1 ∨ ε = -1) →
      2 * δ < ε * (y m - c m) → δ < ε * (y m - c' m) := by
    intro ε m hε hbig
    have he : ε * (y m - c' m) = ε * (y m - c m) + ε * (c m - c' m) := by ring
    have h3 : |ε * (c m - c' m)| ≤ δ := by
      have habs : |ε * (c m - c' m)| = |c m - c' m| := by
        rcases hε with h | h <;> simp [h, abs_mul, abs_neg, abs_sub_comm]
      rw [habs, abs_sub_comm]; exact hshift m
    have := (abs_le.mp h3).1
    linarith [he ▸ (by linarith : 2 * δ - δ < ε * (y m - c m) + ε * (c m - c' m))]
  have h1' : δ < ε₁ * (y i₁ - c' i₁) := hstab ε₁ i₁ hε₁ hy₁
  have h2' : δ < ε₂ * (y i₂ - c' i₂) := hstab ε₂ i₂ hε₂ hy₂
  -- signed offsets equal absolute offsets at the pair coordinates
  have habs₁ : ε₁ * (y i₁ - c' i₁) = |y i₁ - c' i₁| := by
    have h : |ε₁ * (y i₁ - c' i₁)| = |y i₁ - c' i₁| := by
      rcases hε₁ with h | h <;> simp [h, abs_mul, abs_neg, abs_sub_comm]
    rw [← h, abs_of_pos (by linarith)]
  have habs₂ : ε₂ * (y i₂ - c' i₂) = |y i₂ - c' i₂| := by
    have h : |ε₂ * (y i₂ - c' i₂)| = |y i₂ - c' i₂| := by
      rcases hε₂ with h | h <;> simp [h, abs_mul, abs_neg, abs_sub_comm]
    rw [← h, abs_of_pos (by linarith)]
  -- every non-pair coordinate is dominated by the pair's larger offset
  have hdom : ∀ j, j ≠ i₁ → j ≠ i₂ →
      |y j - c' j| < max (ε₁ * (y i₁ - c' i₁)) (ε₂ * (y i₂ - c' i₂)) := by
    intro j hj1 hj2
    have hstep : |y j - c' j| ≤ |y j - c j| + δ := by
      calc |y j - c' j| = |(y j - c j) + (c j - c' j)| := by ring_nf
        _ ≤ |y j - c j| + |c j - c' j| := abs_add_le _ _
        _ ≤ |y j - c j| + δ := by
            have := hshift j; rw [abs_sub_comm] at this; linarith
    have hmax' : max (|y i₁ - c i₁|) (|y i₂ - c i₂|) - δ
        ≤ max (ε₁ * (y i₁ - c' i₁)) (ε₂ * (y i₂ - c' i₂)) := by
      have e₁ : |y i₁ - c i₁| = ε₁ * (y i₁ - c i₁) := by
        have h : |ε₁ * (y i₁ - c i₁)| = |y i₁ - c i₁| := by
          rcases hε₁ with h | h <;> simp [h, abs_mul, abs_neg, abs_sub_comm]
        rw [← h, abs_of_pos (by linarith)]
      have e₂ : |y i₂ - c i₂| = ε₂ * (y i₂ - c i₂) := by
        have h : |ε₂ * (y i₂ - c i₂)| = |y i₂ - c i₂| := by
          rcases hε₂ with h | h <;> simp [h, abs_mul, abs_neg, abs_sub_comm]
        rw [← h, abs_of_pos (by linarith)]
      have s₁ : ε₁ * (y i₁ - c i₁) - δ ≤ ε₁ * (y i₁ - c' i₁) := by
        have he : ε₁ * (y i₁ - c' i₁)
            = ε₁ * (y i₁ - c i₁) + ε₁ * (c i₁ - c' i₁) := by ring
        have h3 : |ε₁ * (c i₁ - c' i₁)| ≤ δ := by
          have habs : |ε₁ * (c i₁ - c' i₁)| = |c i₁ - c' i₁| := by
            rcases hε₁ with h | h <;> simp [h, abs_mul, abs_neg, abs_sub_comm]
          rw [habs, abs_sub_comm]; exact hshift i₁
        linarith [(abs_le.mp h3).1, he ▸ le_refl (ε₁ * (y i₁ - c' i₁))]
      have s₂ : ε₂ * (y i₂ - c i₂) - δ ≤ ε₂ * (y i₂ - c' i₂) := by
        have he : ε₂ * (y i₂ - c' i₂)
            = ε₂ * (y i₂ - c i₂) + ε₂ * (c i₂ - c' i₂) := by ring
        have h3 : |ε₂ * (c i₂ - c' i₂)| ≤ δ := by
          have habs : |ε₂ * (c i₂ - c' i₂)| = |c i₂ - c' i₂| := by
            rcases hε₂ with h | h <;> simp [h, abs_mul, abs_neg, abs_sub_comm]
          rw [habs, abs_sub_comm]; exact hshift i₂
        linarith [(abs_le.mp h3).1, he ▸ le_refl (ε₂ * (y i₂ - c' i₂))]
      rcases le_total (|y i₁ - c i₁|) (|y i₂ - c i₂|) with hle | hle
      · calc max (|y i₁ - c i₁|) (|y i₂ - c i₂|) - δ
            = |y i₂ - c i₂| - δ := by rw [max_eq_right hle]
          _ = ε₂ * (y i₂ - c i₂) - δ := by rw [e₂]
          _ ≤ ε₂ * (y i₂ - c' i₂) := s₂
          _ ≤ _ := le_max_right _ _
      · calc max (|y i₁ - c i₁|) (|y i₂ - c i₂|) - δ
            = |y i₁ - c i₁| - δ := by rw [max_eq_left hle]
          _ = ε₁ * (y i₁ - c i₁) - δ := by rw [e₁]
          _ ≤ ε₁ * (y i₁ - c' i₁) := s₁
          _ ≤ _ := le_max_left _ _
    calc |y j - c' j| ≤ |y j - c j| + δ := hstep
      _ < max (|y i₁ - c i₁|) (|y i₂ - c i₂|) - δ := by
          linarith [hgap j hj1 hj2]
      _ ≤ _ := hmax'
  constructor
  · intro hmem
    have hL : τ * (y i₁ - c' i₁) = linfDist y c' := hmem
    have hpos : 0 < linfDist y c' := by
      calc (0:ℝ) < ε₂ * (y i₂ - c' i₂) := by linarith
        _ ≤ |y i₂ - c' i₂| := habs₂ ▸ le_refl _
        _ ≤ linfDist y c' := abs_sub_le_linfDist y c' i₂
    have hne0 : y i₁ - c' i₁ ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hL
      linarith [hL ▸ hpos]
    have hτε : τ = ε₁ := by
      have hLa : |y i₁ - c' i₁| ≤ linfDist y c' := abs_sub_le_linfDist y c' i₁
      have hτabs : |τ * (y i₁ - c' i₁)| = |y i₁ - c' i₁| := by
        rcases hτ with h | h <;> simp [h, abs_mul, abs_neg, abs_sub_comm]
      have h1 : τ * (y i₁ - c' i₁) = |y i₁ - c' i₁| := by
        refine le_antisymm ((le_abs_self _).trans_eq hτabs) ?_
        rw [hL]; exact hLa
      have h2 : ε₁ * (y i₁ - c' i₁) = |y i₁ - c' i₁| := habs₁
      exact mul_right_cancel₀ hne0 (h1.trans h2.symm)
    refine ⟨hτε, ?_⟩
    calc ε₂ * (y i₂ - c' i₂) = |y i₂ - c' i₂| := habs₂
      _ ≤ linfDist y c' := abs_sub_le_linfDist y c' i₂
      _ = τ * (y i₁ - c' i₁) := hL.symm
      _ = ε₁ * (y i₁ - c' i₁) := by rw [hτε]
  · rintro ⟨hτε, hcmp⟩
    rw [hτε]
    show ε₁ * (y i₁ - c' i₁) = linfDist y c'
    refine le_antisymm ((le_abs_self _).trans ?_) ?_
    · have hτabs : |ε₁ * (y i₁ - c' i₁)| = |y i₁ - c' i₁| := by
        rcases hε₁ with h | h <;> simp [h, abs_mul, abs_neg, abs_sub_comm]
      rw [hτabs]
      exact abs_sub_le_linfDist y c' i₁
    · refine linfDist_le fun j => ?_
      by_cases hj1 : j = i₁
      · rw [hj1, ← habs₁]
      · by_cases hj2 : j = i₂
        · rw [hj2, ← habs₂] at *
          linarith [hcmp]
        · have := hdom j hj1 hj2
          have hmax_le : max (ε₁ * (y i₁ - c' i₁)) (ε₂ * (y i₂ - c' i₂))
              = ε₁ * (y i₁ - c' i₁) := max_eq_left hcmp
          rw [hmax_le] at this
          exact this.le

end Tfnp.Contraction
