/-
Copyright (c) 2026 Angus Joshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Angus Joshi
-/
import Tfnp.Walk

/-!
# The annealed half-kept law

Base identity of the smoothed/average-case track (cycle 33). The *annealed
model* replaces the oracle's sign answers by uniformly random **balanced**
sign vectors (`k = 2m` coordinates, exactly `m` positive) independent of the
cell structure — the `randbal` null model of
`notes/polytime_experiments/adversary_game.py`, measured to match random-SSG
trajectories on every axis (depth, entropy, flux, ledger).

**Theorem (`annealed_half_kept`).** Under the uniform balanced sign model,
a point with a strict `ℓ∞`-argmax relative to the apex is kept by the cut
for **exactly half** of the sign vectors.

The proof needs no binomial identities: a gap-deep point is kept iff the
sign at its argmax coordinate agrees (`mem_pyrUnion_iff_of_gap` at `δ = 0`),
and complementation `A ↦ Aᶜ` is an involution of the balanced vectors that
exchanges agreement with disagreement.

This is the formal root of the measured flux law `κ(m) ≈ ½` (cycle 20): in
the annealed model every gap-deep stratum is kept at rate exactly `½`, and
the unnormalized cell volumes `2^t · vol_t(C)` become martingales — the
Doob bound on the emergence channel in `notes/smoothed.md` starts here.
-/

set_option autoImplicit false

namespace Tfnp.Contraction

open Finset
open scoped Classical

variable {k : ℕ} [NeZero k]

/-- The sign vector of a coordinate set: `+1` on `A`, `−1` off `A`. -/
def signOfSet (A : Finset (Fin k)) : Fin k → ℝ :=
  fun i => if i ∈ A then 1 else -1

lemma isTernary_signOfSet (A : Finset (Fin k)) : IsTernary (signOfSet A) := by
  intro i
  unfold signOfSet
  by_cases h : i ∈ A <;> simp [h]

/-- Complementation is a bijection of the balanced coordinate sets that
exchanges `i ∈ A` with `i ∉ A`: the two agreement classes are equinumerous. -/
lemma card_balanced_mem_eq_not_mem {m : ℕ} (hk : k = 2 * m) (i : Fin k) :
    (((univ : Finset (Fin k)).powersetCard m).filter (fun A => i ∈ A)).card =
      (((univ : Finset (Fin k)).powersetCard m).filter (fun A => i ∉ A)).card := by
  have hcompl : ∀ A : Finset (Fin k), A.card = m → Aᶜ.card = m := by
    intro A hA
    rw [card_compl, Fintype.card_fin, hA]
    omega
  refine Finset.card_bij (fun A _ => Aᶜ) ?_ ?_ ?_
  · intro A hA
    rw [mem_filter, mem_powersetCard] at hA
    rw [mem_filter, mem_powersetCard]
    exact ⟨⟨subset_univ _, hcompl A hA.1.2⟩, by simpa using hA.2⟩
  · intro A hA B hB hAB
    have := congrArg compl hAB
    simpa using this
  · intro B hB
    rw [mem_filter, mem_powersetCard] at hB
    refine ⟨Bᶜ, ?_, compl_compl B⟩
    rw [mem_filter, mem_powersetCard]
    exact ⟨⟨subset_univ _, hcompl B hB.1.2⟩, by simpa using hB.2⟩

/-- **The annealed half-kept law.** Let `y` have a strict argmax `(i, σ)`
relative to the apex `c` (positive top offset, all other coordinates
strictly smaller). Then over the uniform balanced sign model (`k = 2m`
coordinates, exactly `m` positive), the cut keeps `y` for **exactly half**
of the sign vectors. In the annealed model every gap-deep point survives
each round with probability exactly `½` — the flux law, machine-checked. -/
theorem annealed_half_kept {m : ℕ} (hk : k = 2 * m)
    {c y : Vec k} {i : Fin k} {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hy : y ∈ Pyr i σ c)
    (hgap : ∀ j, j ≠ i → |y j - c j| < |y i - c i|)
    (h0 : 0 < |y i - c i|) :
    2 * (((univ : Finset (Fin k)).powersetCard m).filter
          (fun A => y ∈ PyrUnion (signOfSet A) c)).card =
      ((univ : Finset (Fin k)).powersetCard m).card := by
  have hδ : linfDist c c ≤ 0 := by
    refine linfDist_le fun j => ?_
    simp
  have hgap' : ∀ j, j ≠ i → |y j - c j| + 2 * 0 < |y i - c i| := by
    intro j hj
    simpa using hgap j hj
  have hgap0 : 2 * 0 < |y i - c i| := by simpa using h0
  -- membership is decided by the sign at the argmax coordinate
  have hmem : ∀ A : Finset (Fin k),
      (y ∈ PyrUnion (signOfSet A) c) ↔ signOfSet A i = σ := fun A =>
    mem_pyrUnion_iff_of_gap hσ hy hδ hgap' hgap0 (isTernary_signOfSet A)
  have hfilter : (((univ : Finset (Fin k)).powersetCard m).filter
      (fun A => y ∈ PyrUnion (signOfSet A) c)).card =
      (((univ : Finset (Fin k)).powersetCard m).filter
        (fun A => signOfSet A i = σ)).card := by
    congr 1
    apply filter_congr
    intro A _
    exact hmem A
  rw [hfilter]
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := univ.powersetCard m) (p := fun A : Finset (Fin k) => i ∈ A)
  have hswap := card_balanced_mem_eq_not_mem hk i
  rcases hσ with rfl | rfl
  · have heq : (((univ : Finset (Fin k)).powersetCard m).filter
        (fun A => signOfSet A i = (1 : ℝ))).card =
        (((univ : Finset (Fin k)).powersetCard m).filter (fun A => i ∈ A)).card := by
      congr 1
      apply filter_congr
      intro A _
      unfold signOfSet
      by_cases h : i ∈ A <;> simp [h] <;> norm_num
    rw [heq]
    omega
  · have heq : (((univ : Finset (Fin k)).powersetCard m).filter
        (fun A => signOfSet A i = (-1 : ℝ))).card =
        (((univ : Finset (Fin k)).powersetCard m).filter (fun A => i ∉ A)).card := by
      congr 1
      apply filter_congr
      intro A _
      unfold signOfSet
      by_cases h : i ∈ A <;> simp [h] <;> norm_num
    rw [heq]
    omega

/-- **The straddle–dodge dichotomy.** A 2-simple point at pair `{i₁, i₂}`
with pattern `(ε₁, ε₂)` that is **strictly on the `i₁` side** of the pair
form at an apex `c'` within `δ` (i.e. `ε₂(yᵢ₂ − c'ᵢ₂) < ε₁(yᵢ₁ − c'ᵢ₁)`,
equivalently `φ(y) > φ(c')`) has a **strict argmax** `(i₁, ε₁)` at `c'` —
the exact hypothesis of `annealed_survival_pow`. Consequence: in the
annealed model, tie-front cells that do NOT straddle the current pair
offset die at rate exactly `½` per round like gap-deep cells; **the
argmax-dodging advantage of the front is confined to the straddling cells,
which the walk lemma counts** (`notes/smoothed.md` §4c). -/
theorem strict_argmax_of_one_sided {c c' y : Vec k} {i₁ i₂ : Fin k}
    {ε₁ ε₂ : ℝ} (hε₁ : ε₁ = 1 ∨ ε₁ = -1) (hε₂ : ε₂ = 1 ∨ ε₂ = -1) {δ : ℝ}
    (hδ : linfDist c' c ≤ δ)
    (hy₁ : 2 * δ < ε₁ * (y i₁ - c i₁)) (hy₂ : 2 * δ < ε₂ * (y i₂ - c i₂))
    (hgap : ∀ j, j ≠ i₁ → j ≠ i₂ →
      |y j - c j| + 2 * δ < max (|y i₁ - c i₁|) (|y i₂ - c i₂|))
    (hside : ε₂ * (y i₂ - c' i₂) < ε₁ * (y i₁ - c' i₁)) :
    y ∈ Pyr i₁ ε₁ c' ∧ (∀ j, j ≠ i₁ → |y j - c' j| < |y i₁ - c' i₁|) ∧
      0 < |y i₁ - c' i₁| := by
  have hδ0 : 0 ≤ δ := le_trans (linfDist_nonneg c' c) hδ
  have hshift : ∀ m, |c' m - c m| ≤ δ :=
    fun m => (abs_sub_le_linfDist c' c m).trans hδ
  -- signed pair offsets stay above δ at the perturbed apex
  have hstab : ∀ (ε : ℝ) (m : Fin k), (ε = 1 ∨ ε = -1) →
      2 * δ < ε * (y m - c m) → δ < ε * (y m - c' m) := by
    intro ε m hε hbig
    have he : ε * (y m - c' m) = ε * (y m - c m) + ε * (c m - c' m) := by ring
    have h3 : |ε * (c m - c' m)| ≤ δ := by
      have habs : |ε * (c m - c' m)| = |c m - c' m| := by
        rcases hε with h | h <;> simp [h, abs_mul, abs_neg, abs_sub_comm]
      rw [habs, abs_sub_comm]; exact hshift m
    have := (abs_le.mp h3).1
    linarith [he ▸ (by linarith :
      2 * δ - δ < ε * (y m - c m) + ε * (c m - c' m))]
  have h1' : δ < ε₁ * (y i₁ - c' i₁) := hstab ε₁ i₁ hε₁ hy₁
  have h2' : δ < ε₂ * (y i₂ - c' i₂) := hstab ε₂ i₂ hε₂ hy₂
  have habs₁ : ε₁ * (y i₁ - c' i₁) = |y i₁ - c' i₁| := by
    have h : |ε₁ * (y i₁ - c' i₁)| = |y i₁ - c' i₁| := by
      rcases hε₁ with h | h <;> simp [h, abs_mul, abs_neg, abs_sub_comm]
    rw [← h, abs_of_pos (by linarith)]
  have habs₂ : ε₂ * (y i₂ - c' i₂) = |y i₂ - c' i₂| := by
    have h : |ε₂ * (y i₂ - c' i₂)| = |y i₂ - c' i₂| := by
      rcases hε₂ with h | h <;> simp [h, abs_mul, abs_neg, abs_sub_comm]
    rw [← h, abs_of_pos (by linarith)]
  have h0' : 0 < |y i₁ - c' i₁| := by rw [← habs₁]; linarith
  -- the top offset at c' cannot have dropped more than δ below the pair max
  have hlead : max (|y i₁ - c i₁|) (|y i₂ - c i₂|) - δ ≤ |y i₁ - c' i₁| := by
    have ha : |y i₁ - c i₁| - δ ≤ |y i₁ - c' i₁| := by
      have h : |y i₁ - c i₁| ≤ |y i₁ - c' i₁| + |c' i₁ - c i₁| := by
        calc |y i₁ - c i₁| = |(y i₁ - c' i₁) + (c' i₁ - c i₁)| := by ring_nf
          _ ≤ |y i₁ - c' i₁| + |c' i₁ - c i₁| := abs_add_le _ _
      linarith [hshift i₁]
    have hb : |y i₂ - c i₂| - δ ≤ |y i₁ - c' i₁| := by
      have h : |y i₂ - c i₂| ≤ |y i₂ - c' i₂| + |c' i₂ - c i₂| := by
        calc |y i₂ - c i₂| = |(y i₂ - c' i₂) + (c' i₂ - c i₂)| := by ring_nf
          _ ≤ |y i₂ - c' i₂| + |c' i₂ - c i₂| := abs_add_le _ _
      have h2 : |y i₂ - c' i₂| < |y i₁ - c' i₁| := by
        rw [← habs₁, ← habs₂]; exact hside
      linarith [hshift i₂]
    rcases max_cases (|y i₁ - c i₁|) (|y i₂ - c i₂|) with ⟨hm, -⟩ | ⟨hm, -⟩ <;>
      rw [hm]
    · exact ha
    · exact hb
  -- strict dominance over every other coordinate
  have hdom : ∀ j, j ≠ i₁ → |y j - c' j| < |y i₁ - c' i₁| := by
    intro j hj1
    by_cases hj2 : j = i₂
    · subst hj2
      rw [← habs₁, ← habs₂]; exact hside
    · have hstep : |y j - c' j| ≤ |y j - c j| + δ := by
        have h : |y j - c' j| ≤ |y j - c j| + |c j - c' j| := by
          calc |y j - c' j| = |(y j - c j) + (c j - c' j)| := by ring_nf
            _ ≤ |y j - c j| + |c j - c' j| := abs_add_le _ _
        have := hshift j; rw [abs_sub_comm] at this; linarith
      have := hgap j hj1 hj2
      linarith
  refine ⟨?_, hdom, h0'⟩
  show ε₁ * (y i₁ - c' i₁) = linfDist y c'
  refine le_antisymm (habs₁ ▸ abs_sub_le_linfDist y c' i₁) ?_
  refine linfDist_le fun j => ?_
  by_cases hj : j = i₁
  · rw [hj]
    exact habs₁.ge
  · exact ((hdom j hj).trans_eq habs₁.symm).le

/-- **The birth round: an agree–agree cut keeps the whole 2-simple pattern
cell — on both sides of the pair form.** If the cut's signs agree with the
pattern at both pair coordinates (`s i₁ = ε₁`, `s i₂ = ε₂`), every 2-simple
point of the pattern is kept: points on the `i₁` side of the pair form land
in the `i₁`-pyramid, points on the `i₂` side in the `i₂`-pyramid
(`pair_membership_iff`, both orientations). For a cell straddling the
offset this is the BIRTH event — the cell survives whole but is split into
two cells of the refined partition. With `pair_membership_iff` (single
agree keeps exactly the agreeing side) and `double_disagree_kills` (double
disagree kills everything), the annealed straddler's offspring distribution
`(2, 1, 1, 0)` with probability `≈ ¼` each is machine-checked pointwise:
straddlers are exactly critical, the bulk is subcritical at `½` —
the population-balance theorem of `notes/smoothed.md` §4d. -/
theorem both_agree_keeps {c c' y : Vec k} {i₁ i₂ : Fin k} {ε₁ ε₂ : ℝ}
    (hε₁ : ε₁ = 1 ∨ ε₁ = -1) (hε₂ : ε₂ = 1 ∨ ε₂ = -1) {δ : ℝ}
    (hδ : linfDist c' c ≤ δ)
    (hy₁ : 2 * δ < ε₁ * (y i₁ - c i₁)) (hy₂ : 2 * δ < ε₂ * (y i₂ - c i₂))
    (hgap : ∀ j, j ≠ i₁ → j ≠ i₂ →
      |y j - c j| + 2 * δ < max (|y i₁ - c i₁|) (|y i₂ - c i₂|))
    {s : Fin k → ℝ} (hs₁ : s i₁ = ε₁) (hs₂ : s i₂ = ε₂) :
    y ∈ PyrUnion s c' := by
  rcases le_total (ε₂ * (y i₂ - c' i₂)) (ε₁ * (y i₁ - c' i₁)) with hside | hside
  · -- the point is on the i₁ side of the pair form: kept in the i₁-pyramid
    refine ⟨i₁, ?_, ?_⟩
    · rw [hs₁]; rcases hε₁ with h | h <;> simp [h]
    · rw [hs₁]
      exact (pair_membership_iff hε₁ hε₂ hδ hy₁ hy₂ hgap hε₁).mpr ⟨rfl, hside⟩
  · -- the point is on the i₂ side: kept in the i₂-pyramid (symmetric)
    refine ⟨i₂, ?_, ?_⟩
    · rw [hs₂]; rcases hε₂ with h | h <;> simp [h]
    · rw [hs₂]
      have hgap' : ∀ j, j ≠ i₂ → j ≠ i₁ →
          |y j - c j| + 2 * δ < max (|y i₂ - c i₂|) (|y i₁ - c i₁|) := by
        intro j h2 h1
        rw [max_comm]
        exact hgap j h1 h2
      exact (pair_membership_iff hε₂ hε₁ hδ hy₂ hy₁ hgap' hε₂).mpr ⟨rfl, hside⟩

/-- **The annealed survival theorem (the survival half of lemma (A1),
`notes/smoothed.md` §4).** A point that has a strict argmax at every one of
`a` rounds (gap-deep throughout, so kept-or-killed whole each round —
`deep_extinction`) survives all `a` independent balanced cuts for **exactly
a `2^{-a}` fraction** of the sign tuples. Counting form: `2^a` times the
number of surviving tuples equals the total number of tuples.

Corollary (paper): the expected lifetime of a gap-deep tracked lineage in
the annealed model is `Σ_a 2^{-a} = 2` rounds, while its mass doubles per
surviving round — survival × growth is a martingale, and any stacked deep
population pays `2^{-age}` survival for its `2^{age}` required growth. -/
theorem annealed_survival_pow {m a : ℕ} (hk : k = 2 * m)
    {cs : Fin a → Vec k} {y : Vec k} {is : Fin a → Fin k} {σs : Fin a → ℝ}
    (hσ : ∀ r, σs r = 1 ∨ σs r = -1)
    (hy : ∀ r, y ∈ Pyr (is r) (σs r) (cs r))
    (hgap : ∀ r, ∀ j, j ≠ is r → |y j - cs r j| < |y (is r) - cs r (is r)|)
    (h0 : ∀ r, 0 < |y (is r) - cs r (is r)|) :
    2 ^ a * ((Fintype.piFinset (fun _ : Fin a =>
        ((univ : Finset (Fin k)).powersetCard m))).filter
        (fun f => ∀ r, y ∈ PyrUnion (signOfSet (f r)) (cs r))).card
      = ((univ : Finset (Fin k)).powersetCard m).card ^ a := by
  -- the surviving tuples factor as a product of per-round surviving sets
  have hfact : (Fintype.piFinset (fun _ : Fin a =>
        ((univ : Finset (Fin k)).powersetCard m))).filter
        (fun f => ∀ r, y ∈ PyrUnion (signOfSet (f r)) (cs r)) =
      Fintype.piFinset (fun r : Fin a =>
        ((univ : Finset (Fin k)).powersetCard m).filter
          (fun A => y ∈ PyrUnion (signOfSet A) (cs r))) := by
    ext f
    simp only [Finset.mem_filter, Fintype.mem_piFinset]
    constructor
    · rintro ⟨h1, h2⟩
      exact fun r => ⟨h1 r, h2 r⟩
    · intro h
      exact ⟨fun r => (h r).1, fun r => (h r).2⟩
  rw [hfact, Fintype.card_piFinset]
  calc 2 ^ a * ∏ r : Fin a, (((univ : Finset (Fin k)).powersetCard m).filter
        (fun A => y ∈ PyrUnion (signOfSet A) (cs r))).card
      = ∏ r : Fin a, 2 * (((univ : Finset (Fin k)).powersetCard m).filter
          (fun A => y ∈ PyrUnion (signOfSet A) (cs r))).card := by
        rw [Finset.prod_mul_distrib, Finset.prod_const]
        simp [Finset.card_univ]
    _ = ∏ _r : Fin a, ((univ : Finset (Fin k)).powersetCard m).card := by
        refine Finset.prod_congr rfl fun r _ => ?_
        exact annealed_half_kept hk (hσ r) (hy r) (hgap r) (h0 r)
    _ = ((univ : Finset (Fin k)).powersetCard m).card ^ a := by
        rw [Finset.prod_const]
        simp [Finset.card_univ]

end Tfnp.Contraction
