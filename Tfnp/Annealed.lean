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

/-- **The eviction lemma (definitional at every depth).** A point kept in
pyramid `(i, σ)` of a cut lies in EVERY pencil halfspace of that cut's
apex: `σ(yᵢ − cᵢ) ≥ ±(yⱼ − cⱼ)` for every coordinate `j`. Hence every split
of a cell by a cut evicts every pair-form offset of the apex to the
boundary of every kept piece simultaneously — a straddled offset never
remains interior after its split. This is the renewal mechanism of the
occupancy frame (`notes/smoothed.md` §4e): birth-grade re-straddling
requires fresh offset penetration, budgeted at `2δ` per round by the
marching bound (`abs_pairComb_sub_le`). -/
theorem pyr_mem_halfspace {c y : Vec k} {i : Fin k} {σ : ℝ}
    (hy : y ∈ Pyr i σ c) (j : Fin k) :
    y j - c j ≤ σ * (y i - c i) ∧ -(y j - c j) ≤ σ * (y i - c i) := by
  have htop : σ * (y i - c i) = linfDist y c := hy
  have habs : |y j - c j| ≤ linfDist y c := abs_sub_le_linfDist y c j
  constructor
  · calc y j - c j ≤ |y j - c j| := le_abs_self _
      _ ≤ linfDist y c := habs
      _ = σ * (y i - c i) := htop.symm
  · calc -(y j - c j) ≤ |y j - c j| := neg_le_abs _
      _ ≤ linfDist y c := habs
      _ = σ * (y i - c i) := htop.symm

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

/-- **Resolved-cell extinction (the stacking dichotomy's decay half,
`notes/smoothed.md` §4f).** Let `y` be `m`-simple on the tie set `M`
(pattern signs, positive signed offsets on `M`, every outside coordinate
strictly below every `M` coordinate) with **all pairwise comparisons on `M`
strictly resolved** (no two signed offsets equal — the cell straddles none
of its tie set's offsets). Then `y` has a strict argmax, so
`annealed_half_kept` applies: fully-resolved deep cells die at rate exactly
`½` per round in the annealed model. Combined with the interval geometry
(at most ONE cell per form straddles that form's offset), this yields the
per-tie-set population balance: at most `C(m,2)` cells of a tie set escape
the `½`-death regime at any time. -/
theorem strict_argmax_of_resolved {c y : Vec k} {M : Finset (Fin k)}
    (hM : M.Nonempty) {εs : Fin k → ℝ}
    (hε : ∀ i ∈ M, εs i = 1 ∨ εs i = -1)
    (hpos : ∀ i ∈ M, 0 < εs i * (y i - c i))
    (hres : ∀ i ∈ M, ∀ j ∈ M, i ≠ j →
      εs i * (y i - c i) ≠ εs j * (y j - c j))
    (hdom : ∀ j, j ∉ M → ∀ i ∈ M, |y j - c j| < |y i - c i|) :
    ∃ i ∈ M, (εs i = 1 ∨ εs i = -1) ∧
      (∀ j, j ≠ i → |y j - c j| < |y i - c i|) ∧ 0 < |y i - c i| := by
  -- absolute offsets on M equal the signed offsets
  have habs : ∀ i ∈ M, εs i * (y i - c i) = |y i - c i| := by
    intro i hi
    have h1 : |εs i * (y i - c i)| = |y i - c i| := by
      rcases hε i hi with h | h <;> simp [h, abs_sub_comm]
    rw [← h1, abs_of_pos (hpos i hi)]
  -- take the maximizer of the signed offset over M
  obtain ⟨i, hiM, hi⟩ := Finset.exists_mem_eq_sup' hM
    (fun i => εs i * (y i - c i))
  refine ⟨i, hiM, hε i hiM, ?_, ?_⟩
  · intro j hj
    by_cases hjM : j ∈ M
    · -- within M: the maximizer is strict because values are distinct
      have hle : εs j * (y j - c j) ≤ εs i * (y i - c i) := by
        rw [← hi]
        exact Finset.le_sup' (f := fun i => εs i * (y i - c i)) hjM
      have hne : εs j * (y j - c j) ≠ εs i * (y i - c i) :=
        hres j hjM i hiM hj
      rw [← habs j hjM, ← habs i hiM]
      exact lt_of_le_of_ne hle hne
    · exact hdom j hjM i hiM
  · rw [← habs i hiM]
    exact hpos i hiM

/-- **The escape fence (deterministic half of the recrossing budget,
`notes/smoothed.md` §4g).** A walk whose remaining travel budget is `B`
(per-step bounds `Δ s` summing to at most `B` over any window) can never
recross a level it has escaped by more than `B`: if `v t − ℓ > B`, then
`v s > ℓ` for every `s ≥ t`. Hence recrossings of a level are confined to
the rounds when the walk is inside its escape band — for geometrically
shrinking steps (`Δ` ratio `q`), the band is `Δ_t/(1−q)` wide, and the
probabilistic half of the budget only has to control band residence. -/
theorem walk_no_recross {v : ℕ → ℝ} {Δ : ℕ → ℝ} {ℓ B : ℝ} {t : ℕ}
    (hstep : ∀ s, t ≤ s → |v (s + 1) - v s| ≤ Δ s)
    (hbud : ∀ s, (Finset.Ico t s).sum Δ ≤ B)
    (hesc : B < v t - ℓ) :
    ∀ s, t ≤ s → ℓ < v s := by
  have key : ∀ s, t ≤ s → v t - (Finset.Ico t s).sum Δ ≤ v s := by
    intro s hs
    induction s with
    | zero =>
        have ht : t = 0 := Nat.le_zero.mp hs
        subst ht
        simp
    | succ n ih =>
        rcases Nat.lt_or_ge t (n + 1) with hlt | hge
        · have htn : t ≤ n := Nat.lt_succ_iff.mp hlt
          have h1 := ih htn
          have h2 : |v (n + 1) - v n| ≤ Δ n := hstep n htn
          have h3 : v n - Δ n ≤ v (n + 1) := by
            have := (abs_le.mp h2).1
            linarith
          have h4 : (Finset.Ico t (n + 1)).sum Δ
              = (Finset.Ico t n).sum Δ + Δ n :=
            Finset.sum_Ico_succ_top htn Δ
          rw [h4]
          linarith
        · have ht : t = n + 1 := le_antisymm hs hge
          subst ht
          simp
  intro s hs
  have h1 := key s hs
  have h2 := hbud s
  linarith

/-! ### The crossing toll (cycle 41)

The probabilistic half of the recrossing budget concerns the *fair-coin walk
model*: a real-valued walk whose round-`s` step is `±μ s` according to an
independent fair coin (the abstraction of the FW-apex offset walk under
annealed signs; the conditional fairness of the apex-step directions is a
model hypothesis, not a theorem about FW). The toll identity below converts
crossings to band residence EXACTLY: a crossing of a level requires being
within one step of it (a past-measurable event) plus one specific fresh
coin, so over all coin tuples

  `2 · Σ #crossings = Σ #{rounds strictly inside the one-step band}`.

Combined with `walk_no_recross` (band rounds are confined to the escape
band), the entire recrossing budget is equivalent to a band-residence
(anticoncentration) bound — where the cycle-41 no-go shows the abstract
model has a `√(flat-window)` Littlewood–Offord floor, so the `O(1)` budget
must come from FW/dynamics structure, not from coin fairness alone. -/

/-- The fair-coin walk: from `v0`, round `s` moves by `+μ s` if the coin
`f s` is true, else `−μ s`; `coinWalk v0 μ f t` is the position after the
first `t` rounds. -/
def coinWalk {a : ℕ} (v0 : ℝ) (μ : Fin a → ℝ) (f : Fin a → Bool) (t : ℕ) : ℝ :=
  v0 + ∑ s ∈ Finset.univ.filter (fun s : Fin a => (s : ℕ) < t),
    (if f s = true then μ s else -μ s)

lemma coinWalk_succ {a : ℕ} (v0 : ℝ) (μ : Fin a → ℝ) (f : Fin a → Bool)
    (t : Fin a) :
    coinWalk v0 μ f ((t : ℕ) + 1) =
      coinWalk v0 μ f t + (if f t = true then μ t else -μ t) := by
  unfold coinWalk
  have hset : Finset.univ.filter (fun s : Fin a => (s : ℕ) < (t : ℕ) + 1) =
      insert t (Finset.univ.filter (fun s : Fin a => (s : ℕ) < (t : ℕ))) := by
    ext s
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | h
      · exact Or.inr h
      · exact Or.inl (Fin.ext h)
    · rintro (rfl | h)
      · exact Nat.lt_succ_of_le le_rfl
      · exact Nat.lt_succ_of_lt h
  rw [hset, Finset.sum_insert (by simp)]
  ring

/-- The walk position after `t` rounds does not depend on coins at rounds
`≥ t`. -/
lemma coinWalk_update_of_le {a : ℕ} (v0 : ℝ) (μ : Fin a → ℝ)
    (f : Fin a → Bool) (r : Fin a) (b : Bool) {t : ℕ} (h : t ≤ (r : ℕ)) :
    coinWalk v0 μ (Function.update f r b) t = coinWalk v0 μ f t := by
  unfold coinWalk
  congr 1
  refine Finset.sum_congr rfl fun s hs => ?_
  have hsr : s ≠ r := by
    intro hsr
    subst hsr
    have := (Finset.mem_filter.mp hs).2
    omega
  rw [Function.update_of_ne hsr]

/-- Crossing arithmetic: for a nonnegative step `μ`, the walk at signed
distance `w` from the level crosses it iff it is strictly inside the
one-step band AND the step points at the level. -/
lemma cross_iff_band_aux {w μ : ℝ} (hμ : 0 ≤ μ) :
    (w * (w + μ) < 0 ↔ (0 < |w| ∧ |w| < μ) ∧ w < 0) ∧
    (w * (w - μ) < 0 ↔ (0 < |w| ∧ |w| < μ) ∧ 0 < w) := by
  constructor
  · rw [mul_neg_iff]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact absurd h2 (by linarith)
      · refine ⟨⟨?_, ?_⟩, h1⟩
        · rw [abs_pos]; exact ne_of_lt h1
        · rw [abs_of_neg h1]; linarith
    · rintro ⟨⟨h0, hb⟩, hneg⟩
      right
      refine ⟨hneg, ?_⟩
      rw [abs_of_neg hneg] at hb
      linarith
  · rw [mul_neg_iff]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · refine ⟨⟨?_, ?_⟩, h1⟩
        · rw [abs_pos]; exact ne_of_gt h1
        · rw [abs_of_pos h1]; linarith
      · exact absurd h2 (by linarith)
    · rintro ⟨⟨h0, hb⟩, hpos⟩
      left
      refine ⟨hpos, ?_⟩
      rw [abs_of_pos hpos] at hb
      linarith

/-- One round of the toll: a crossing at round `t` is exactly band residence
(a past-measurable event) plus the one coin value pointing at the level. -/
lemma coinWalk_cross_iff {a : ℕ} (v0 ℓ : ℝ) (μ : Fin a → ℝ)
    (hμ : ∀ t, 0 ≤ μ t) (f : Fin a → Bool) (t : Fin a) :
    (coinWalk v0 μ f t - ℓ) * (coinWalk v0 μ f ((t : ℕ) + 1) - ℓ) < 0 ↔
      ((0 < |coinWalk v0 μ f t - ℓ| ∧ |coinWalk v0 μ f t - ℓ| < μ t) ∧
        ((f t = true) ↔ coinWalk v0 μ f t - ℓ < 0)) := by
  have hrec := coinWalk_succ v0 μ f t
  cases hft : f t with
  | false =>
      rw [hrec, hft]
      simp only [Bool.false_eq_true, if_false]
      have halg : coinWalk v0 μ f t + -μ t - ℓ =
          (coinWalk v0 μ f t - ℓ) - μ t := by ring
      rw [halg, (cross_iff_band_aux (hμ t)).2]
      constructor
      · rintro ⟨hb, hpos⟩
        exact ⟨hb, iff_of_false (by simp) (by linarith)⟩
      · rintro ⟨hb, hiff⟩
        refine ⟨hb, ?_⟩
        have hne : coinWalk v0 μ f t - ℓ ≠ 0 := by
          have := hb.1; rwa [abs_pos] at this
        rcases lt_or_gt_of_ne hne with h' | h'
        · exact absurd (hiff.mpr h') (by simp)
        · exact h'
  | true =>
      rw [hrec, hft]
      simp only [if_true]
      have halg : coinWalk v0 μ f t + μ t - ℓ =
          (coinWalk v0 μ f t - ℓ) + μ t := by ring
      rw [halg, (cross_iff_band_aux (hμ t)).1]
      constructor
      · rintro ⟨hb, hneg⟩
        exact ⟨hb, iff_of_true (by trivial) hneg⟩
      · rintro ⟨hb, hiff⟩
        exact ⟨hb, hiff.mp (by trivial)⟩

/-- Round-`t` toll: over all coin tuples, exactly half of the step-band
residents cross — the coin at the crossing round is fresh and fair. -/
lemma crossing_toll_at {a : ℕ} (v0 ℓ : ℝ) (μ : Fin a → ℝ)
    (hμ : ∀ t, 0 ≤ μ t) (t : Fin a) :
    2 * ((Finset.univ : Finset (Fin a → Bool)).filter
        (fun f => (coinWalk v0 μ f t - ℓ) *
          (coinWalk v0 μ f ((t : ℕ) + 1) - ℓ) < 0)).card
      = ((Finset.univ : Finset (Fin a → Bool)).filter
        (fun f => 0 < |coinWalk v0 μ f t - ℓ| ∧
          |coinWalk v0 μ f t - ℓ| < μ t)).card := by
  classical
  have hwalk : ∀ (f : Fin a → Bool) (b : Bool),
      coinWalk v0 μ (Function.update f t b) t = coinWalk v0 μ f t :=
    fun f b => coinWalk_update_of_le v0 μ f t b le_rfl
  -- the crossing set is the band set intersected with the fresh-coin event
  have hcross : (Finset.univ : Finset (Fin a → Bool)).filter
      (fun f => (coinWalk v0 μ f t - ℓ) *
        (coinWalk v0 μ f ((t : ℕ) + 1) - ℓ) < 0)
      = ((Finset.univ : Finset (Fin a → Bool)).filter
          (fun f => 0 < |coinWalk v0 μ f t - ℓ| ∧
            |coinWalk v0 μ f t - ℓ| < μ t)).filter
          (fun f => (f t = true) ↔ coinWalk v0 μ f t - ℓ < 0) := by
    rw [Finset.filter_filter]
    apply Finset.filter_congr
    intro f _
    exact coinWalk_cross_iff v0 ℓ μ hμ f t
  -- flipping the round-t coin is an involution of the band set exchanging
  -- the two coin events
  have hbij : (((Finset.univ : Finset (Fin a → Bool)).filter
        (fun f => 0 < |coinWalk v0 μ f t - ℓ| ∧
          |coinWalk v0 μ f t - ℓ| < μ t)).filter
        (fun f => (f t = true) ↔ coinWalk v0 μ f t - ℓ < 0)).card
      = (((Finset.univ : Finset (Fin a → Bool)).filter
        (fun f => 0 < |coinWalk v0 μ f t - ℓ| ∧
          |coinWalk v0 μ f t - ℓ| < μ t)).filter
        (fun f => ¬((f t = true) ↔ coinWalk v0 μ f t - ℓ < 0))).card := by
    have hQflip : ∀ f : Fin a → Bool,
        ((Function.update f t (!(f t)) t = true) ↔
          coinWalk v0 μ (Function.update f t (!(f t))) t - ℓ < 0) ↔
        ¬((f t = true) ↔ coinWalk v0 μ f t - ℓ < 0) := by
      intro f
      rw [hwalk f, Function.update_self]
      cases hb : f t <;> simp
    refine Finset.card_bij' (fun f _ => Function.update f t (!(f t)))
        (fun f _ => Function.update f t (!(f t))) ?_ ?_ ?_ ?_
    · intro f hf
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
      refine ⟨by rw [hwalk f]; exact hf.1, ?_⟩
      rw [hQflip f]
      exact not_not_intro hf.2
    · intro f hf
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
      refine ⟨by rw [hwalk f]; exact hf.1, ?_⟩
      rw [hQflip f]
      exact hf.2
    · intro f _
      simp [Function.update_idem, Function.update_self, Bool.not_not,
        Function.update_eq_self]
    · intro f _
      simp [Function.update_idem, Function.update_self, Bool.not_not,
        Function.update_eq_self]
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin a → Bool)).filter
      (fun f => 0 < |coinWalk v0 μ f t - ℓ| ∧
        |coinWalk v0 μ f t - ℓ| < μ t))
    (p := fun f => (f t = true) ↔ coinWalk v0 μ f t - ℓ < 0)
  rw [hcross]
  omega

/-- **The crossing-toll identity (the probabilistic half of the recrossing
budget, made exact — `notes/smoothed.md` §4g/§4h).** For the fair-coin walk
with nonnegative step sizes, summed over ALL coin tuples:

  `2 × (total level crossings) = total strict step-band residence`,

i.e. the expected number of crossings of any fixed level is EXACTLY half
the expected number of rounds the walk spends strictly inside the one-step
band around the level. With `walk_no_recross` (which confines band rounds
to the escape band), the recrossing budget is EQUIVALENT to a band-residence
anticoncentration bound. The cycle-41 no-go (flat steps inside a geometric
envelope of ratio `1 − Θ(1/d)` give `Θ(√d)` expected band-residence per
own-level by Littlewood–Offord) shows coin fairness plus step shrinkage
alone cannot deliver the `O(1)` budget: the missing ingredient is a
transience property of the FW-apex dynamics, or an algorithmic apex rule —
not more coin combinatorics. -/
theorem annealed_crossing_toll {a : ℕ} (v0 ℓ : ℝ) (μ : Fin a → ℝ)
    (hμ : ∀ t, 0 ≤ μ t) :
    2 * ∑ f : Fin a → Bool, ((Finset.univ : Finset (Fin a)).filter
        (fun t : Fin a => (coinWalk v0 μ f (t : ℕ) - ℓ) *
          (coinWalk v0 μ f ((t : ℕ) + 1) - ℓ) < 0)).card
      = ∑ f : Fin a → Bool, ((Finset.univ : Finset (Fin a)).filter
        (fun t : Fin a => 0 < |coinWalk v0 μ f (t : ℕ) - ℓ| ∧
          |coinWalk v0 μ f (t : ℕ) - ℓ| < μ t)).card := by
  classical
  have lhs_eq : ∑ f : Fin a → Bool, ((Finset.univ : Finset (Fin a)).filter
        (fun t : Fin a => (coinWalk v0 μ f (t : ℕ) - ℓ) *
          (coinWalk v0 μ f ((t : ℕ) + 1) - ℓ) < 0)).card
      = ∑ t : Fin a, ((Finset.univ : Finset (Fin a → Bool)).filter
        (fun f => (coinWalk v0 μ f (t : ℕ) - ℓ) *
          (coinWalk v0 μ f ((t : ℕ) + 1) - ℓ) < 0)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have rhs_eq : ∑ f : Fin a → Bool, ((Finset.univ : Finset (Fin a)).filter
        (fun t : Fin a => 0 < |coinWalk v0 μ f (t : ℕ) - ℓ| ∧
          |coinWalk v0 μ f (t : ℕ) - ℓ| < μ t)).card
      = ∑ t : Fin a, ((Finset.univ : Finset (Fin a → Bool)).filter
        (fun f => 0 < |coinWalk v0 μ f (t : ℕ) - ℓ| ∧
          |coinWalk v0 μ f (t : ℕ) - ℓ| < μ t)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  rw [lhs_eq, rhs_eq, Finset.mul_sum]
  exact Finset.sum_congr rfl fun t _ => crossing_toll_at v0 ℓ μ hμ t

end Tfnp.Contraction
