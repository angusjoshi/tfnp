/-
Copyright (c) 2026 Angus Joshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Angus Joshi
-/
import Tfnp.Fan

/-!
# Margin stability: cells split only in the top-gap margin

The last machine-checked link of the reduction chain in `notes/cell_sampler.md`
§4. A point's cell coordinate for a cut is its `ℓ∞`-argmax relative to the
cut's apex (that is the definition of the pyramids). Here we prove that this
argmax — index *and* sign — is **stable under apex perturbation smaller than
half the top gap**:

* `pyr_stable_of_gap` — if `y ∈ Pyr i σ c` and every other coordinate's offset
  is smaller than `|yᵢ − cᵢ| − 2δ`, then `y ∈ Pyr i σ c'` for every `c'` with
  `‖c' − c‖∞ ≤ δ`;
* `pyr_unique_of_gap` — under the same gap, `(i, σ)` is the **only** pyramid
  of `c'` containing `y`;
* `mem_pyrUnion_iff_of_gap` — hence for any ternary sign vector `s`, membership
  in the cut `⋃_{sⱼ≠0} 𝒫ⱼ(c', sⱼ)` is decided by the single equation `s i = σ`.

**Consequence (the no-split theorem, immediate from the above):** two points
of a common cell that are both gap-deep relative to the apex drift `δ` receive
*identical* treatment from every new cut with a nearby apex — both kept in the
same pyramid piece (`s i = σ`) or both removed (`s i ≠ σ`). A cut can split a
cell **only inside the top-gap margin** `{|w_(1)| − |w_(2)| ≤ 2δ}`. Combined
with `deep_cell_factorization` (`Tfnp/Fan.lean`), all growth of the cell
structure — hence all of conjecture (★) — is confined to the margin: the one
remaining open question is quantitative top-gap anti-concentration of the
balanced-cut measure (measured by `notes/polytime_experiments/margin_mass.py`).
-/

set_option autoImplicit false

namespace Tfnp.Contraction

variable {k : ℕ} [NeZero k]

/-- **Argmax stability.** If `y`'s `ℓ∞`-argmax relative to `c` is `(i, σ)`
(`σ = ±1`) with top gap exceeding `2δ` — every other coordinate offset at
least `2δ` below `|yᵢ − cᵢ|`, and `2δ < |yᵢ − cᵢ|` — then `y` has the same
argmax relative to every apex within `δ`. -/
theorem pyr_stable_of_gap {c c' y : Vec k} {i : Fin k} {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hy : y ∈ Pyr i σ c) {δ : ℝ}
    (hδ : linfDist c' c ≤ δ)
    (hgap : ∀ j, j ≠ i → |y j - c j| + 2 * δ < |y i - c i|)
    (hgap0 : 2 * δ < |y i - c i|) :
    y ∈ Pyr i σ c' := by
  have hδ0 : 0 ≤ δ := le_trans (linfDist_nonneg c' c) hδ
  have habsσ : ∀ x : ℝ, |σ * x| = |x| := by
    intro x; rcases hσ with h | h <;> simp [h, abs_mul, abs_sub_comm, abs_neg]
  have htop : σ * (y i - c i) = linfDist y c := hy
  have hA : σ * (y i - c i) = |y i - c i| := by
    refine le_antisymm ((le_abs_self _).trans_eq (habsσ _)) ?_
    rw [htop]; exact abs_sub_le_linfDist y c i
  -- the perturbed signed offset stays within δ of the unperturbed one
  have hshift : ∀ j, |c' j - c j| ≤ δ :=
    fun j => (abs_sub_le_linfDist c' c j).trans hδ
  have hlow : |y i - c i| - δ ≤ σ * (y i - c' i) := by
    have he : σ * (y i - c' i) = σ * (y i - c i) + σ * (c i - c' i) := by ring
    have h2 : -δ ≤ σ * (c i - c' i) := by
      have h3 : |σ * (c i - c' i)| ≤ δ := by
        rw [habsσ (c i - c' i), abs_sub_comm]; exact hshift i
      linarith [(abs_le.mp h3).1]
    rw [he, hA] at *
    linarith
  have hpos : 0 < σ * (y i - c' i) := by linarith
  -- coordinate `i`'s signed offset equals its absolute offset…
  have heq_i : σ * (y i - c' i) = |y i - c' i| := by
    have h1 : |σ * (y i - c' i)| = |y i - c' i| := habsσ _
    rw [← h1, abs_of_pos hpos]
  -- …and strictly dominates every other coordinate's offset.
  have hdom : ∀ j, j ≠ i → |y j - c' j| < σ * (y i - c' i) := by
    intro j hj
    calc |y j - c' j| ≤ |y j - c j| + |c j - c' j| := by
          have := abs_sub_le (y j - c j) (c j - c' j)
          calc |y j - c' j| = |(y j - c j) + (c j - c' j)| := by ring_nf
            _ ≤ |y j - c j| + |c j - c' j| := abs_add_le _ _
      _ ≤ |y j - c j| + δ := by
          have := hshift j; rw [abs_sub_comm] at this; linarith
      _ < |y i - c i| - δ := by linarith [hgap j hj]
      _ ≤ σ * (y i - c' i) := hlow
  show σ * (y i - c' i) = linfDist y c'
  refine le_antisymm (heq_i ▸ abs_sub_le_linfDist y c' i) ?_
  refine linfDist_le fun j => ?_
  by_cases hj : j = i
  · rw [hj]; exact heq_i.ge
  · exact (hdom j hj).le

/-- **Argmax uniqueness.** Under the same gap, `(i, σ)` is the *only* pyramid
of the perturbed apex containing `y`: any `y ∈ Pyr j τ c'` with `τ = ±1` has
`j = i` and `τ = σ`. -/
theorem pyr_unique_of_gap {c c' y : Vec k} {i : Fin k} {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hy : y ∈ Pyr i σ c) {δ : ℝ}
    (hδ : linfDist c' c ≤ δ)
    (hgap : ∀ j, j ≠ i → |y j - c j| + 2 * δ < |y i - c i|)
    (hgap0 : 2 * δ < |y i - c i|)
    {j : Fin k} {τ : ℝ} (hτ : τ = 1 ∨ τ = -1) (hyj : y ∈ Pyr j τ c') :
    j = i ∧ τ = σ := by
  have hδ0 : 0 ≤ δ := le_trans (linfDist_nonneg c' c) hδ
  have hstable := pyr_stable_of_gap hσ hy hδ hgap hgap0
  have htop' : σ * (y i - c' i) = linfDist y c' := hstable
  have hshift : ∀ m, |c' m - c m| ≤ δ :=
    fun m => (abs_sub_le_linfDist c' c m).trans hδ
  have hA : σ * (y i - c i) = |y i - c i| := by
    have habsσ : |σ * (y i - c i)| = |y i - c i| := by
      rcases hσ with h | h <;> simp [h, abs_mul, abs_neg, abs_sub_comm]
    refine le_antisymm ((le_abs_self _).trans_eq habsσ) ?_
    rw [show σ * (y i - c i) = linfDist y c from hy]
    exact abs_sub_le_linfDist y c i
  have hlow : |y i - c i| - δ ≤ σ * (y i - c' i) := by
    have he : σ * (y i - c' i) = σ * (y i - c i) + σ * (c i - c' i) := by ring
    have h3 : |σ * (c i - c' i)| ≤ δ := by
      have habs : |σ * (c i - c' i)| = |c i - c' i| := by
        rcases hσ with h | h <;> simp [h, abs_mul, abs_neg, abs_sub_comm]
      rw [habs, abs_sub_comm]; exact hshift i
    rw [he, hA]
    linarith [(abs_le.mp h3).1]
  have hpos : 0 < linfDist y c' := by rw [← htop']; linarith
  have hji : j = i := by
    by_contra hne
    -- a non-`i` coordinate cannot reach the (strictly dominant) top value
    have hdom : |y j - c' j| < σ * (y i - c' i) := by
      calc |y j - c' j| = |(y j - c j) + (c j - c' j)| := by ring_nf
        _ ≤ |y j - c j| + |c j - c' j| := abs_add_le _ _
        _ ≤ |y j - c j| + δ := by
            have := hshift j; rw [abs_sub_comm] at this; linarith
        _ < |y i - c i| - δ := by linarith [hgap j hne]
        _ ≤ σ * (y i - c' i) := hlow
    have hτle : τ * (y j - c' j) ≤ |y j - c' j| := by
      have habs : |τ * (y j - c' j)| = |y j - c' j| := by
        rcases hτ with h | h <;> simp [h, abs_mul, abs_neg, abs_sub_comm]
      exact (le_abs_self _).trans_eq habs
    have := hyj
    rw [mem_Pyr] at this
    rw [this, ← htop'] at hτle
    linarith [hdom, hτle]
  subst hji
  refine ⟨rfl, ?_⟩
  -- same coordinate, positive top value: the signs must agree
  have h1 : τ * (y j - c' j) = σ * (y j - c' j) := by
    have h2 := hyj
    rw [mem_Pyr] at h2
    rw [h2, htop']
  have hne0 : y j - c' j ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at htop'
    linarith [htop' ▸ hpos]
  exact mul_right_cancel₀ hne0 h1

/-- **The no-split characterization.** For a gap-deep point, membership in any
ternary cut at a nearby apex is decided by one equation: `y ∈ ⋃_{sⱼ≠0} 𝒫ⱼ(c',
sⱼ)` iff `s i = σ`. Hence two points of a common gap-deep class are never
separated by a new cut — both kept in the same pyramid piece or both removed —
and **cells split only inside the top-gap margin**. -/
theorem mem_pyrUnion_iff_of_gap {c c' y : Vec k} {i : Fin k} {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hy : y ∈ Pyr i σ c) {δ : ℝ}
    (hδ : linfDist c' c ≤ δ)
    (hgap : ∀ j, j ≠ i → |y j - c j| + 2 * δ < |y i - c i|)
    (hgap0 : 2 * δ < |y i - c i|)
    {s : Fin k → ℝ} (hs : IsTernary s) :
    y ∈ PyrUnion s c' ↔ s i = σ := by
  constructor
  · rintro ⟨j, hj0, hjmem⟩
    have hjt : s j = 1 ∨ s j = -1 := by
      rcases hs j with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h hj0
    obtain ⟨hji, hτσ⟩ := pyr_unique_of_gap hσ hy hδ hgap hgap0 hjt hjmem
    rw [← hji, hτσ]
  · intro hsi
    have hσ0 : σ ≠ 0 := by rcases hσ with h | h <;> simp [h]
    exact ⟨i, hsi ▸ hσ0, hsi ▸ pyr_stable_of_gap hσ hy hδ hgap hgap0⟩

end Tfnp.Contraction

namespace Tfnp.Contraction

variable {k : ℕ} [NeZero k]

/-- Pyramid membership at a perturbed apex, for a gap-deep point, in full:
`y ∈ 𝒫ⱼ(c', τ)` iff `(j, τ) = (i, σ)`. Stability and uniqueness together. -/
theorem mem_pyr_iff_of_gap {c c' y : Vec k} {i : Fin k} {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hy : y ∈ Pyr i σ c) {δ : ℝ}
    (hδ : linfDist c' c ≤ δ)
    (hgap : ∀ j, j ≠ i → |y j - c j| + 2 * δ < |y i - c i|)
    (hgap0 : 2 * δ < |y i - c i|)
    {j : Fin k} {τ : ℝ} (hτ : τ = 1 ∨ τ = -1) :
    y ∈ Pyr j τ c' ↔ (j = i ∧ τ = σ) := by
  constructor
  · exact pyr_unique_of_gap hσ hy hδ hgap hgap0 hτ
  · rintro ⟨rfl, rfl⟩
    exact pyr_stable_of_gap hσ hy hδ hgap hgap0

/-- **The 1-deep cell-collapse theorem.** Two points that are gap-deep at the
same argmax `(i, σ)` relative to a reference point receive identical treatment
from **every** cut of a whole trajectory whose apexes stay within `δ`: same
membership in every pyramid of every cut, hence the same cell and the same
survival history. Counting corollary (immediate): the 1-deep survivors of any
`t`-cut trajectory occupy at most `2k` distinct cells — **independent of `t`**. -/
theorem cell_eq_of_onedeep {ι : Type*} {cstar : Vec k} {δ : ℝ}
    {cs : ι → Vec k} (hδ : ∀ r, linfDist (cs r) cstar ≤ δ)
    {i : Fin k} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    {y z : Vec k} (hy : y ∈ Pyr i σ cstar) (hz : z ∈ Pyr i σ cstar)
    (hgy : ∀ j, j ≠ i → |y j - cstar j| + 2 * δ < |y i - cstar i|)
    (hgy0 : 2 * δ < |y i - cstar i|)
    (hgz : ∀ j, j ≠ i → |z j - cstar j| + 2 * δ < |z i - cstar i|)
    (hgz0 : 2 * δ < |z i - cstar i|) :
    ∀ (r : ι) (j : Fin k) (τ : ℝ), (τ = 1 ∨ τ = -1) →
      (y ∈ Pyr j τ (cs r) ↔ z ∈ Pyr j τ (cs r)) := by
  intro r j τ hτ
  rw [mem_pyr_iff_of_gap hσ hy (hδ r) hgy hgy0 hτ,
      mem_pyr_iff_of_gap hσ hz (hδ r) hgz hgz0 hτ]

/-- **Pair confinement for 2-simple points.** If the two leading coordinates
`i₁, i₂` of `y` (relative to `c`) dominate every other coordinate by more than
`2δ`, then at any apex within `δ`, every pyramid containing `y` has index `i₁`
or `i₂`: the argmax can flip only within the tied pair. This is the dominance
half of the `O(d²t²)` bound for 2-simple cells (the other half — the record is
a cell of the arrangement of the `2t` threshold lines in the plane of the two
pair forms `yᵢ₁ ± yᵢ₂` — is arithmetic bookkeeping recorded in
`notes/CHAIN.md`). -/
theorem pyr_index_mem_pair_of_2simple {c c' y : Vec k} {i₁ i₂ : Fin k}
    {δ : ℝ} (hδ : linfDist c' c ≤ δ)
    (hgap : ∀ j, j ≠ i₁ → j ≠ i₂ →
      |y j - c j| + 2 * δ < max (|y i₁ - c i₁|) (|y i₂ - c i₂|))
    (hgap0 : 2 * δ < max (|y i₁ - c i₁|) (|y i₂ - c i₂|))
    {j : Fin k} {τ : ℝ} (hτ : τ = 1 ∨ τ = -1)
    (hyj : y ∈ Pyr j τ c') : j = i₁ ∨ j = i₂ := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hne1, hne2⟩ := hcon
  have hδ0 : 0 ≤ δ := le_trans (linfDist_nonneg c' c) hδ
  have hshift : ∀ m, |c' m - c m| ≤ δ :=
    fun m => (abs_sub_le_linfDist c' c m).trans hδ
  -- the leading coordinate (whichever of the pair it is) keeps a big offset at c'
  have hlead : max (|y i₁ - c i₁|) (|y i₂ - c i₂|) - δ ≤ linfDist y c' := by
    rcases le_total (|y i₁ - c i₁|) (|y i₂ - c i₂|) with hle | hle
    · have h1 : |y i₂ - c' i₂| ≥ |y i₂ - c i₂| - δ := by
        have h2 : |y i₂ - c i₂| ≤ |y i₂ - c' i₂| + |c' i₂ - c i₂| := by
          calc |y i₂ - c i₂| = |(y i₂ - c' i₂) + (c' i₂ - c i₂)| := by ring_nf
            _ ≤ |y i₂ - c' i₂| + |c' i₂ - c i₂| := abs_add_le _ _
        linarith [hshift i₂]
      calc max (|y i₁ - c i₁|) (|y i₂ - c i₂|) - δ
          = |y i₂ - c i₂| - δ := by rw [max_eq_right hle]
        _ ≤ |y i₂ - c' i₂| := h1
        _ ≤ linfDist y c' := abs_sub_le_linfDist y c' i₂
    · have h1 : |y i₁ - c' i₁| ≥ |y i₁ - c i₁| - δ := by
        have h2 : |y i₁ - c i₁| ≤ |y i₁ - c' i₁| + |c' i₁ - c i₁| := by
          calc |y i₁ - c i₁| = |(y i₁ - c' i₁) + (c' i₁ - c i₁)| := by ring_nf
            _ ≤ |y i₁ - c' i₁| + |c' i₁ - c i₁| := abs_add_le _ _
        linarith [hshift i₁]
      calc max (|y i₁ - c i₁|) (|y i₂ - c i₂|) - δ
          = |y i₁ - c i₁| - δ := by rw [max_eq_left hle]
        _ ≤ |y i₁ - c' i₁| := h1
        _ ≤ linfDist y c' := abs_sub_le_linfDist y c' i₁
  -- but coordinate j is too small to be the argmax at c'
  have hj_small : |y j - c' j| < max (|y i₁ - c i₁|) (|y i₂ - c i₂|) - δ := by
    calc |y j - c' j| = |(y j - c j) + (c j - c' j)| := by ring_nf
      _ ≤ |y j - c j| + |c j - c' j| := abs_add_le _ _
      _ ≤ |y j - c j| + δ := by
          have := hshift j; rw [abs_sub_comm] at this; linarith
      _ < max (|y i₁ - c i₁|) (|y i₂ - c i₂|) - δ := by
          linarith [hgap j hne1 hne2]
  have hτle : τ * (y j - c' j) ≤ |y j - c' j| := by
    have habs : |τ * (y j - c' j)| = |y j - c' j| := by
      rcases hτ with h | h <;> simp [h, abs_mul, abs_neg, abs_sub_comm]
    exact (le_abs_self _).trans_eq habs
  have hmem := hyj
  rw [mem_Pyr] at hmem
  rw [hmem] at hτle
  linarith

end Tfnp.Contraction

namespace Tfnp.Contraction

variable {k : ℕ} [NeZero k]

/-- **The deep-extinction theorem.** A point that is gap-deep at `(i, σ)`
relative to a reference `c*` is kept by a (nearby-apex) cut **iff** the cut's
sign at `i` is `σ` — so it cannot survive two rounds whose signs at `i`
differ. Consequences, both rigorous: (1) once the sign sequence has played
both signs at every coordinate, every survivor was argmax-mobile (tied at the
relevant scale) at some pair of rounds — survival conditions the measure onto
ties, which is the mechanism behind the measured gap collapse; (2) in the
deepening schedule analysis (`notes/CHAIN.md`), the double-disagree rounds
that graduate tie depth necessarily keep the complementary-signed shallow
mass — deepening one sign pattern floods the measure with the others. -/
theorem deep_extinction {cstar c₁ c₂ y : Vec k} {i : Fin k} {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hy : y ∈ Pyr i σ cstar) {δ : ℝ}
    (hδ₁ : linfDist c₁ cstar ≤ δ) (hδ₂ : linfDist c₂ cstar ≤ δ)
    (hgap : ∀ j, j ≠ i → |y j - cstar j| + 2 * δ < |y i - cstar i|)
    (hgap0 : 2 * δ < |y i - cstar i|)
    {s₁ s₂ : Fin k → ℝ} (hs₁ : IsTernary s₁) (hs₂ : IsTernary s₂)
    (hflip : s₁ i ≠ s₂ i) :
    ¬(y ∈ PyrUnion s₁ c₁ ∧ y ∈ PyrUnion s₂ c₂) := by
  rintro ⟨h1, h2⟩
  rw [mem_pyrUnion_iff_of_gap hσ hy hδ₁ hgap hgap0 hs₁] at h1
  rw [mem_pyrUnion_iff_of_gap hσ hy hδ₂ hgap hgap0 hs₂] at h2
  exact hflip (h1.trans h2.symm)

end Tfnp.Contraction

namespace Tfnp.Contraction

variable {k : ℕ} [NeZero k]

/-- **Pyramid disjointness, quantitative form.** A point lying in two distinct
signed pyramids at a common apex is degenerate: either it is the apex itself
(`‖y−c‖∞ = 0`), or the two pyramids have different coordinates and both
coordinates achieve the norm — the point is *exactly 2-tied*. -/
theorem tie_of_mem_two_pyr {c y : Vec k} {i j : Fin k} {σ τ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hτ : τ = 1 ∨ τ = -1)
    (hi : y ∈ Pyr i σ c) (hj : y ∈ Pyr j τ c) (hne : (i, σ) ≠ (j, τ)) :
    linfDist y c = 0 ∨
      (i ≠ j ∧ |y i - c i| = linfDist y c ∧ |y j - c j| = linfDist y c) := by
  have hLi : σ * (y i - c i) = linfDist y c := hi
  have hLj : τ * (y j - c j) = linfDist y c := hj
  have habs : ∀ (ρ : ℝ) (x : ℝ), ρ = 1 ∨ ρ = -1 → |ρ * x| = |x| := by
    intro ρ x h; rcases h with h | h <;> simp [h, abs_mul, abs_neg]
  by_cases hij : i = j
  · subst hij
    have hστ : σ ≠ τ := fun hcon => hne (by rw [hcon])
    left
    have h1 : σ * (y i - c i) = τ * (y i - c i) := by rw [hLi, hLj]
    have h0 : y i - c i = 0 := by
      by_contra hcon
      exact hστ (mul_right_cancel₀ hcon h1)
    rw [← hLi, h0, mul_zero]
  · right
    refine ⟨hij, ?_, ?_⟩
    · refine le_antisymm (abs_sub_le_linfDist y c i) ?_
      calc linfDist y c = σ * (y i - c i) := hLi.symm
        _ ≤ |σ * (y i - c i)| := le_abs_self _
        _ = |y i - c i| := habs σ _ hσ
    · refine le_antisymm (abs_sub_le_linfDist y c j) ?_
      calc linfDist y c = τ * (y j - c j) := hLj.symm
        _ ≤ |τ * (y j - c j)| := le_abs_self _
        _ = |y j - c j| := habs τ _ hτ

/-- **One-sidedness of the kept measure.** A point kept by the cut
`⋃_{sⱼ≠0} 𝒫ⱼ(c, sⱼ)` that also lies in a *disagreeing* pyramid `𝒫ᵢ(c, −sᵢ)`
is degenerate: it is the apex or exactly 2-tied. So, off the tie set, the
kept measure is completely one-sided at every coordinate pair — each cut
fully resets the pyramid composition, and deepening state cannot be carried
between rounds outside the tie margins (the flooding obstruction of
`notes/CHAIN.md`, structural half). -/
theorem one_sided_of_kept {c y : Vec k} {s : Fin k → ℝ} (hs : IsTernary s)
    {i : Fin k} (hi0 : s i ≠ 0) (hkept : y ∈ PyrUnion s c)
    (hdis : y ∈ Pyr i (-(s i)) c) :
    linfDist y c = 0 ∨ ∃ j, j ≠ i ∧ |y j - c j| = linfDist y c := by
  obtain ⟨j, hj0, hjmem⟩ := hkept
  have hsj : s j = 1 ∨ s j = -1 := by
    rcases hs j with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hj0
  have hsi : -(s i) = 1 ∨ -(s i) = -1 := by
    rcases hs i with h | h | h
    · exact Or.inr (by rw [h])
    · exact Or.inl (by rw [h]; norm_num)
    · exact absurd h hi0
  have hne : (j, s j) ≠ (i, -(s i)) := by
    intro hcon
    have h1 : j = i := congrArg Prod.fst hcon
    have h2 : s j = -(s i) := congrArg Prod.snd hcon
    rw [h1] at h2
    rcases hs i with h | h | h
    · rw [h] at h2; norm_num at h2
    · rw [h] at h2; norm_num at h2
    · exact hi0 h
  rcases tie_of_mem_two_pyr hsj hsi hjmem hdis hne with h0 | ⟨hji, hja, _⟩
  · exact Or.inl h0
  · exact Or.inr ⟨j, hji, hja⟩

end Tfnp.Contraction

namespace Tfnp.Contraction

variable {k : ℕ} [NeZero k]

/-- **Forced graduation: the double-disagree round kills the whole pattern.**
Let `y` be 2-simple at the pair `{i₁, i₂}` with sign pattern `(ε₁, ε₂)` (both
pair offsets exceed `2δ` with those signs, every other coordinate is `2δ`
below the pair's top). If a cut at a nearby apex plays the double-disagree
signs `s i₁ = −ε₁`, `s i₂ = −ε₂`, then `y` is removed — *regardless of which
of the two tied coordinates is its current argmax*. Together with
`deep_extinction` this makes the deepening schedule's cost structure fully
rigorous: graduating tie depth at a pattern requires a round that keeps only
the complementary-signed mass (`one_sided_of_kept`). -/
theorem double_disagree_kills {c c' y : Vec k} {i₁ i₂ : Fin k} {ε₁ ε₂ : ℝ}
    (hε₁ : ε₁ = 1 ∨ ε₁ = -1) (hε₂ : ε₂ = 1 ∨ ε₂ = -1) {δ : ℝ}
    (hδ : linfDist c' c ≤ δ)
    (hy₁ : 2 * δ < ε₁ * (y i₁ - c i₁)) (hy₂ : 2 * δ < ε₂ * (y i₂ - c i₂))
    (hgap : ∀ j, j ≠ i₁ → j ≠ i₂ →
      |y j - c j| + 2 * δ < max (|y i₁ - c i₁|) (|y i₂ - c i₂|))
    {s : Fin k → ℝ} (hs : IsTernary s)
    (hs₁ : s i₁ = -ε₁) (hs₂ : s i₂ = -ε₂) :
    y ∉ PyrUnion s c' := by
  have hδ0 : 0 ≤ δ := le_trans (linfDist_nonneg c' c) hδ
  have hshift : ∀ m, |c' m - c m| ≤ δ :=
    fun m => (abs_sub_le_linfDist c' c m).trans hδ
  -- the pair offsets keep their signs (with margin δ) at the perturbed apex
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
  -- absolute pair offsets exceed 2δ (for the pair-confinement hypothesis)
  have habs₁ : 2 * δ < |y i₁ - c i₁| := by
    have h : ε₁ * (y i₁ - c i₁) ≤ |y i₁ - c i₁| := by
      have habs : |ε₁ * (y i₁ - c i₁)| = |y i₁ - c i₁| := by
        rcases hε₁ with h | h <;> simp [h, abs_mul, abs_neg, abs_sub_comm]
      exact (le_abs_self _).trans_eq habs
    linarith
  rintro ⟨m, hm0, hmmem⟩
  have hmτ : s m = 1 ∨ s m = -1 := by
    rcases hs m with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hm0
  have hpair := pyr_index_mem_pair_of_2simple hδ hgap
    (lt_of_lt_of_le habs₁ (le_max_left _ _)) hmτ hmmem
  have hL : (0 : ℝ) ≤ linfDist y c' := linfDist_nonneg y c'
  rcases hpair with rfl | rfl
  · -- argmax at i₁, but its sign at c' is ε₁ while s m = −ε₁
    have hmem := hmmem
    rw [mem_Pyr, hs₁] at hmem
    have hpos : δ < ε₁ * (y m - c' m) := hstab ε₁ m hε₁ hy₁
    have : -ε₁ * (y m - c' m) = -(ε₁ * (y m - c' m)) := by ring
    rw [this] at hmem
    linarith [hmem ▸ hL]
  · have hmem := hmmem
    rw [mem_Pyr, hs₂] at hmem
    have hpos : δ < ε₂ * (y m - c' m) := hstab ε₂ m hε₂ hy₂
    have : -ε₂ * (y m - c' m) = -(ε₂ * (y m - c' m)) := by ring
    rw [this] at hmem
    linarith [hmem ▸ hL]

end Tfnp.Contraction
