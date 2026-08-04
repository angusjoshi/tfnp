/-
Copyright (c) 2026 Angus Joshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Angus Joshi
-/
import Tfnp.HitRun

/-!
# The fan factorization: cells are functions of one sign pattern

Companion to the "common fan" mechanism of `notes/cell_sampler.md`
(`fan_cone_test.py`: `H(cell | cone) ≈ 0`). Every pyramid membership test is a
conjunction of sign conditions on the `pair forms` `±(yᵢ−cᵢ) ± (yⱼ−cⱼ)`, whose
normals `±eᵢ ± eⱼ` do not depend on the apex. Consequently:

* `mem_pyramid_iff_pairForms` — pyramid membership is exactly a sign condition
  on the pair forms at the pyramid's own apex;
* `pairForm_shift` / `abs_pairForm_le` — moving the apex by `δ` (in `ℓ∞`)
  perturbs every pair form by at most `2δ`;
* `deep_cell_factorization` — **the theorem**: if all apexes of a cut family
  lie within `δ` of a reference point `c*`, then for points that are
  `2δ`-**deep** (every pair form at `c*` exceeds `2δ` in absolute value), the
  entire cell signature — membership in every pyramid of every cut — is a
  function of the **cone datum**: the sign pattern of the pair forms at `c*`
  alone. Two deep points with the same cone datum lie in exactly the same
  pyramids of every cut.

Interpretation. The cone datum takes at most `3^{4k²}` values and — decisive
for conjecture (★) — is **independent of `t`**: outside the union of the
`O(k²t)` margin slabs `{|pair form at c*| ≤ 2δ}`, the number of distinct cells
of a `t`-cut trajectory is bounded by the number of full-dimensional cones of
a single fan (`≤ 2^k·k!`), however many cuts are made. All `t`-dependence of
the cell structure lives inside the margin slabs, whose total width is
governed by the apex dispersion `δ`. This is the machine-checked half of the
mechanism; the quantitative halves (apex clustering, cone-mass concentration)
are the measured open lemmas of `notes/cell_sampler.md` §4.
-/

set_option autoImplicit false

namespace Tfnp.Contraction

variable {k : ℕ} [NeZero k]

/-- The **pair form** `signR s₁ · (yᵢ − cᵢ) + signR s₂ · (yⱼ − cⱼ)`: the linear
functionals (with apex-dependent offset) whose signs decide every pyramid
membership. Their normals `±eᵢ ± eⱼ` are apex-independent. -/
def pairForm (s₁ s₂ : Bool) (i j : Fin k) (c y : Vec k) : ℝ :=
  signR s₁ * (y i - c i) + signR s₂ * (y j - c j)

/-- Pyramid membership is exactly a conjunction of pair-form sign conditions
at the pyramid's own apex: `y ∈ 𝒫ᵢ(c,φ)` iff for every `j` both
`signR φ·(yᵢ−cᵢ) + (yⱼ−cⱼ) ≥ 0` and `signR φ·(yᵢ−cᵢ) − (yⱼ−cⱼ) ≥ 0`. -/
lemma mem_pyramid_iff_pairForms (i : Fin k) (φ : Bool) (c y : Vec k) :
    y ∈ Pyramid i φ c ↔
      ∀ j, 0 ≤ pairForm φ true i j c y ∧ 0 ≤ pairForm φ false i j c y := by
  rw [mem_pyramid_iff_sign]
  constructor
  · intro h j
    have hj : |y j - c j| ≤ linfDist y c := abs_sub_le_linfDist y c j
    have h1 := abs_le.mp hj
    constructor
    · simp only [pairForm, signR_true, one_mul]
      linarith [h1.1, h.ge]
    · simp only [pairForm, signR_false, neg_one_mul]
      linarith [h1.2, h.ge]
  · intro h
    refine le_antisymm ((signR_mul_le_abs _ _).trans (abs_sub_le_linfDist y c i)) ?_
    refine linfDist_le fun j => ?_
    obtain ⟨h1, h2⟩ := h j
    simp only [pairForm, signR_true, one_mul, signR_false, neg_one_mul] at h1 h2
    rw [abs_le]
    constructor <;> linarith

/-- Changing the apex shifts a pair form by the same form of the apex
difference: `pairForm s₁ s₂ i j c y = pairForm s₁ s₂ i j c* y − pairForm s₁ s₂
i j c* c` … stated additively. -/
lemma pairForm_shift (s₁ s₂ : Bool) (i j : Fin k) (cstar c y : Vec k) :
    pairForm s₁ s₂ i j c y
      = pairForm s₁ s₂ i j cstar y
        - (signR s₁ * (c i - cstar i) + signR s₂ * (c j - cstar j)) := by
  simp only [pairForm]; ring

/-- The apex-shift term is at most `2δ` when `‖c − c*‖∞ ≤ δ`. -/
lemma abs_shift_le {cstar c : Vec k} {δ : ℝ}
    (hc : linfDist c cstar ≤ δ) (s₁ s₂ : Bool) (i j : Fin k) :
    |signR s₁ * (c i - cstar i) + signR s₂ * (c j - cstar j)| ≤ 2 * δ := by
  have hi : |c i - cstar i| ≤ δ := (abs_sub_le_linfDist c cstar i).trans hc
  have hj : |c j - cstar j| ≤ δ := (abs_sub_le_linfDist c cstar j).trans hc
  calc |signR s₁ * (c i - cstar i) + signR s₂ * (c j - cstar j)|
      ≤ |signR s₁ * (c i - cstar i)| + |signR s₂ * (c j - cstar j)| :=
        abs_add_le _ _
    _ = |c i - cstar i| + |c j - cstar j| := by
        rw [abs_signR_mul, abs_signR_mul]
    _ ≤ 2 * δ := by linarith

/-- A point is **`2δ`-deep** (relative to the reference apex `c*`) when every
pair form at `c*` exceeds `2δ` in absolute value: it avoids all margin slabs. -/
def Deep (cstar : Vec k) (δ : ℝ) (y : Vec k) : Prop :=
  ∀ (s₁ s₂ : Bool) (i j : Fin k), 2 * δ < |pairForm s₁ s₂ i j cstar y|

/-- Two deep reals with equal ternary sign lie strictly on the same side of
the whole `[−2δ, 2δ]` margin. -/
lemma same_side {a b δ : ℝ} (hδ : 0 ≤ δ) (hs : sgnR a = sgnR b)
    (ha : 2 * δ < |a|) (hb : 2 * δ < |b|) :
    (2 * δ < a ∧ 2 * δ < b) ∨ (a < -(2 * δ) ∧ b < -(2 * δ)) := by
  rcases lt_trichotomy a 0 with hneg | hzero | hpos
  · have hsa : sgnR a = -1 := sgnR_of_neg hneg
    have hsb : sgnR b = -1 := hs ▸ hsa
    have hbneg : b < 0 := by
      by_contra hcon
      push_neg at hcon
      rcases eq_or_lt_of_le hcon with heq | hlt
      · rw [← heq] at hsb; simp [sgnR] at hsb
      · rw [sgnR_of_pos hlt] at hsb; norm_num at hsb
    refine Or.inr ⟨?_, ?_⟩
    · rw [abs_of_neg hneg] at ha; linarith
    · rw [abs_of_neg hbneg] at hb; linarith
  · exfalso; rw [hzero, abs_zero] at ha; linarith
  · have hsa : sgnR a = 1 := sgnR_of_pos hpos
    have hsb : sgnR b = 1 := hs ▸ hsa
    have hbpos : 0 < b := by
      by_contra hcon
      push_neg at hcon
      rcases eq_or_lt_of_le hcon with heq | hlt
      · rw [heq] at hsb; simp [sgnR] at hsb
      · rw [sgnR_of_neg hlt] at hsb; norm_num at hsb
    refine Or.inl ⟨?_, ?_⟩
    · rw [abs_of_pos hpos] at ha; linarith
    · rw [abs_of_pos hbpos] at hb; linarith

/-- **The fan factorization theorem.** Let every apex of the cut family
`cs : ι → Vec k` lie within `δ` (in `ℓ∞`) of a reference point `c*`. If `y`
and `z` are `2δ`-deep and have the **same cone datum** — equal ternary signs
of every pair form at `c*` — then `y` and `z` belong to exactly the same
pyramids of every cut: the entire cell signature of a deep point is a function
of its cone datum, a `t`-independent object with at most `3^{4k²}` values
(and at most `2^k·k!` full-dimensional cones). All `t`-dependence of the cell
structure is confined to the margin slabs `{|pair form at c*| ≤ 2δ}`. -/
theorem deep_cell_factorization {ι : Type*} {cstar : Vec k} {δ : ℝ}
    (hδ0 : 0 ≤ δ) {cs : ι → Vec k} (hδ : ∀ r, linfDist (cs r) cstar ≤ δ)
    {y z : Vec k} (hy : Deep cstar δ y) (hz : Deep cstar δ z)
    (hsame : ∀ (s₁ s₂ : Bool) (i j : Fin k),
      sgnR (pairForm s₁ s₂ i j cstar y) = sgnR (pairForm s₁ s₂ i j cstar z)) :
    ∀ (r : ι) (i : Fin k) (φ : Bool),
      y ∈ Pyramid i φ (cs r) ↔ z ∈ Pyramid i φ (cs r) := by
  intro r i φ
  rw [mem_pyramid_iff_pairForms, mem_pyramid_iff_pairForms]
  refine forall_congr' fun j => ?_
  have key : ∀ s₂ : Bool,
      (0 ≤ pairForm φ s₂ i j (cs r) y ↔ 0 ≤ pairForm φ s₂ i j (cs r) z) := by
    intro s₂
    have hshift := abs_shift_le (hδ r) φ s₂ i j
    obtain ⟨hs1, hs2⟩ := abs_le.mp hshift
    rcases same_side hδ0 (hsame φ s₂ i j) (hy φ s₂ i j) (hz φ s₂ i j) with
      ⟨hya, hza⟩ | ⟨hya, hza⟩
    · -- both forms strictly above the margin: both memberships hold
      constructor <;> intro _ <;>
        · rw [pairForm_shift (cstar := cstar)]
          linarith
    · -- both strictly below: both memberships fail
      constructor <;> intro hcon <;>
        · rw [pairForm_shift (cstar := cstar)] at hcon
          linarith
  exact and_congr (key true) (key false)

end Tfnp.Contraction
