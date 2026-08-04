/-
Copyright (c) 2026 Angus Joshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Angus Joshi
-/
import Tfnp.Walk

/-!
# The shedding geometry: slabs and the motion budget

The machine-checked geometric half of the (SHED) lemma (`notes/CHAIN.md`).
For the pair form `φ(z) = ε₁ zᵢ₁ − ε₂ zᵢ₂` (`pairComb`):

* `abs_pairComb_sub_le` — **the marching bound**: an apex step of `ℓ∞`-size
  `δ` moves every pencil offset by at most `2δ`;
* `shed_slab` — **the shed-slab theorem**: a 2-simple point that was on the
  kept `i₁`-side of an old cut and falls off the `i₁`-side of a new cut lies
  in the slab `φ(c_old) ≤ φ(y) < φ(c_new)` — of width at most
  `2‖c_new − c_old‖∞`. Shed pieces are marching slabs;
* `pencil_energy` — **the motion budget**: for any apex step `u`,
  `∑ᵢ∑ⱼ ((uᵢ−uⱼ)² + (uᵢ+uⱼ)²) = 4·k·∑ᵢ uᵢ²` — the total squared pencil
  motion per round is fixed, so at most `O(k)` of the `k²` pencils can move
  at the full step scale in any round.

What remains of (SHED) after this file is purely measure-theoretic: the mass
of the (provably slab-shaped, provably budgeted) shed regions, with the apex
nudge as a free parameter. No geometry is left unformalized.
-/

set_option autoImplicit false

namespace Tfnp.Contraction

variable {k : ℕ} [NeZero k]

/-- The signed pair form `φ(z) = ε₁ zᵢ₁ − ε₂ zᵢ₂` deciding the 2-simple
record (`pair_membership_iff`). -/
def pairComb (ε₁ ε₂ : ℝ) (i₁ i₂ : Fin k) (z : Vec k) : ℝ :=
  ε₁ * z i₁ - ε₂ * z i₂

/-- **The marching bound.** An apex step of `ℓ∞`-size `δ` moves every pencil
offset by at most `2δ`. -/
theorem abs_pairComb_sub_le {ε₁ ε₂ : ℝ} (hε₁ : ε₁ = 1 ∨ ε₁ = -1)
    (hε₂ : ε₂ = 1 ∨ ε₂ = -1) (i₁ i₂ : Fin k) {c c' : Vec k} {δ : ℝ}
    (hδ : linfDist c' c ≤ δ) :
    |pairComb ε₁ ε₂ i₁ i₂ c' - pairComb ε₁ ε₂ i₁ i₂ c| ≤ 2 * δ := by
  have h1 : |c' i₁ - c i₁| ≤ δ := (abs_sub_le_linfDist c' c i₁).trans hδ
  have h2 : |c' i₂ - c i₂| ≤ δ := (abs_sub_le_linfDist c' c i₂).trans hδ
  have he : pairComb ε₁ ε₂ i₁ i₂ c' - pairComb ε₁ ε₂ i₁ i₂ c
      = ε₁ * (c' i₁ - c i₁) - ε₂ * (c' i₂ - c i₂) := by
    simp only [pairComb]; ring
  have ha : |ε₁ * (c' i₁ - c i₁)| ≤ δ := by
    have habs : |ε₁ * (c' i₁ - c i₁)| = |c' i₁ - c i₁| := by
      rcases hε₁ with h | h <;> simp [h, abs_mul, abs_neg, abs_sub_comm]
    rw [habs]; exact h1
  have hb : |ε₂ * (c' i₂ - c i₂)| ≤ δ := by
    have habs : |ε₂ * (c' i₂ - c i₂)| = |c' i₂ - c i₂| := by
      rcases hε₂ with h | h <;> simp [h, abs_mul, abs_neg, abs_sub_comm]
    rw [habs]; exact h2
  calc |pairComb ε₁ ε₂ i₁ i₂ c' - pairComb ε₁ ε₂ i₁ i₂ c|
      = |ε₁ * (c' i₁ - c i₁) - ε₂ * (c' i₂ - c i₂)| := by rw [he]
    _ ≤ |ε₁ * (c' i₁ - c i₁)| + |ε₂ * (c' i₂ - c i₂)| := abs_sub _ _
    _ ≤ 2 * δ := by linarith

/-- **The shed-slab theorem.** Let `y` be 2-simple (relative to reference `c`
at scale `2δ`, pair `{i₁,i₂}`, signs `(ε₁,ε₂)`) and let two apexes `c₁, c₂`
lie within `δ` of `c`. If `y` was on the kept `i₁`-side of the cut at `c₁`
(`y ∈ Pyr i₁ ε₁ c₁`) but is **not** on the `i₁`-side of the cut at `c₂`, then
`y` lies in the marching slab

  `φ(c₁) ≤ φ(y) < φ(c₂)`, of width `φ(c₂) − φ(c₁) ≤ 2‖c₂ − c₁‖∞`,

where `φ = pairComb ε₁ ε₂ i₁ i₂`. Shed pieces are slabs between consecutive
pencil offsets. -/
theorem shed_slab {c c₁ c₂ y : Vec k} {i₁ i₂ : Fin k} {ε₁ ε₂ : ℝ}
    (hε₁ : ε₁ = 1 ∨ ε₁ = -1) (hε₂ : ε₂ = 1 ∨ ε₂ = -1) {δ : ℝ}
    (hδ₁ : linfDist c₁ c ≤ δ) (hδ₂ : linfDist c₂ c ≤ δ)
    (hy₁ : 2 * δ < ε₁ * (y i₁ - c i₁)) (hy₂ : 2 * δ < ε₂ * (y i₂ - c i₂))
    (hgap : ∀ j, j ≠ i₁ → j ≠ i₂ →
      |y j - c j| + 2 * δ < max (|y i₁ - c i₁|) (|y i₂ - c i₂|))
    (hold : y ∈ Pyr i₁ ε₁ c₁) (hnew : y ∉ Pyr i₁ ε₁ c₂) :
    pairComb ε₁ ε₂ i₁ i₂ c₁ ≤ pairComb ε₁ ε₂ i₁ i₂ y ∧
      pairComb ε₁ ε₂ i₁ i₂ y < pairComb ε₁ ε₂ i₁ i₂ c₂ ∧
      pairComb ε₁ ε₂ i₁ i₂ c₂ - pairComb ε₁ ε₂ i₁ i₂ c₁
        ≤ 2 * linfDist c₂ c₁ := by
  have h1 := (pair_membership_iff hε₁ hε₂ hδ₁ hy₁ hy₂ hgap hε₁).mp hold
  have h2 : ¬(ε₂ * (y i₂ - c₂ i₂) ≤ ε₁ * (y i₁ - c₂ i₁)) := by
    intro hc
    exact hnew ((pair_membership_iff hε₁ hε₂ hδ₂ hy₁ hy₂ hgap hε₁).mpr
      ⟨rfl, hc⟩)
  push_neg at h2
  refine ⟨?_, ?_, ?_⟩
  · have := h1.2
    simp only [pairComb]
    linarith
  · simp only [pairComb]
    linarith
  · have := abs_pairComb_sub_le hε₁ hε₂ i₁ i₂
      (le_refl (linfDist c₂ c₁))
    have h3 := (abs_le.mp this).2
    linarith

/-- **The motion budget.** For any apex step `u : Vec k`, the total squared
motion of all `2k²` signed pencils is exactly `4k·∑ uᵢ²`: no round can move
more than `O(k)` pencils at the full step scale. -/
theorem pencil_energy (u : Vec k) :
    ∑ i : Fin k, ∑ j : Fin k, ((u i - u j) ^ 2 + (u i + u j) ^ 2)
      = 4 * (k : ℝ) * ∑ i : Fin k, (u i) ^ 2 := by
  have h2 : ∑ j : Fin k, 2 * (u j) ^ 2 = 2 * ∑ j : Fin k, (u j) ^ 2 :=
    (Finset.mul_sum _ _ _).symm
  have hrow : ∀ i : Fin k,
      ∑ j : Fin k, ((u i - u j) ^ 2 + (u i + u j) ^ 2)
        = (k : ℝ) * (2 * (u i) ^ 2) + 2 * ∑ j : Fin k, (u j) ^ 2 := by
    intro i
    have hexp : ∀ j : Fin k, (u i - u j) ^ 2 + (u i + u j) ^ 2
        = 2 * (u i) ^ 2 + 2 * (u j) ^ 2 := fun j => by ring
    rw [Finset.sum_congr rfl fun j _ => hexp j, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, h2]
  rw [Finset.sum_congr rfl fun i _ => hrow i, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h3 : ∑ i : Fin k, (k : ℝ) * (2 * (u i) ^ 2)
      = (k : ℝ) * (2 * ∑ i : Fin k, (u i) ^ 2) := by
    rw [← Finset.mul_sum, h2]
  rw [h3]; ring

end Tfnp.Contraction

namespace Tfnp.Contraction

variable {k : ℕ} [NeZero k]

/-- **m-set confinement.** If the coordinates in `M` dominate: some member's
offset exceeds `2δ`, and every coordinate outside `M` is more than `2δ`
below the best member — then at any apex within `δ`, every pyramid
containing `y` has its index in `M`. The deep stratum's splits are decided
entirely by the tie set's own forms: the m-ary generalization of
`pyr_index_mem_pair_of_2simple`, and the structural base of the deep-stratum
ledger (the (ZONE) analysis of `notes/CHAIN.md`). -/
theorem pyr_index_mem_of_mset {c c' y : Vec k} {M : Finset (Fin k)}
    (hM : M.Nonempty) {δ : ℝ} (hδ : linfDist c' c ≤ δ)
    (hgap : ∀ j, j ∉ M → |y j - c j| + 2 * δ < M.sup' hM fun i => |y i - c i|)
    (hgap0 : 2 * δ < M.sup' hM fun i => |y i - c i|)
    {m : Fin k} {τ : ℝ} (hτ : τ = 1 ∨ τ = -1)
    (hym : y ∈ Pyr m τ c') : m ∈ M := by
  by_contra hcon
  have hδ0 : 0 ≤ δ := le_trans (linfDist_nonneg c' c) hδ
  have hshift : ∀ j, |c' j - c j| ≤ δ :=
    fun j => (abs_sub_le_linfDist c' c j).trans hδ
  -- some member of M realises the sup
  obtain ⟨i₀, hi₀M, hi₀⟩ := Finset.exists_mem_eq_sup' hM fun i => |y i - c i|
  -- that member keeps a large offset at the perturbed apex
  have hlead : (M.sup' hM fun i => |y i - c i|) - δ ≤ linfDist y c' := by
    have h1 : |y i₀ - c i₀| ≤ |y i₀ - c' i₀| + |c' i₀ - c i₀| := by
      calc |y i₀ - c i₀| = |(y i₀ - c' i₀) + (c' i₀ - c i₀)| := by ring_nf
        _ ≤ |y i₀ - c' i₀| + |c' i₀ - c i₀| := abs_add_le _ _
    have h2 : |y i₀ - c i₀| - δ ≤ |y i₀ - c' i₀| := by
      linarith [hshift i₀]
    calc (M.sup' hM fun i => |y i - c i|) - δ
        = |y i₀ - c i₀| - δ := by rw [hi₀]
      _ ≤ |y i₀ - c' i₀| := h2
      _ ≤ linfDist y c' := abs_sub_le_linfDist y c' i₀
  -- but the outside coordinate m is too small to achieve the norm
  have hm_small : |y m - c' m| < (M.sup' hM fun i => |y i - c i|) - δ := by
    calc |y m - c' m| = |(y m - c m) + (c m - c' m)| := by ring_nf
      _ ≤ |y m - c m| + |c m - c' m| := abs_add_le _ _
      _ ≤ |y m - c m| + δ := by
          have := hshift m; rw [abs_sub_comm] at this; linarith
      _ < (M.sup' hM fun i => |y i - c i|) - δ := by
          linarith [hgap m hcon]
  have hτle : τ * (y m - c' m) ≤ |y m - c' m| := by
    have habs : |τ * (y m - c' m)| = |y m - c' m| := by
      rcases hτ with h | h <;> simp [h, abs_mul, abs_neg, abs_sub_comm]
    exact (le_abs_self _).trans_eq habs
  have hmem := hym
  rw [mem_Pyr] at hmem
  rw [hmem] at hτle
  linarith

end Tfnp.Contraction
