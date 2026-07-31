import Mathlib.Topology.MetricSpace.Contracting
import Tfnp.Contraction

/-!
# The Chen–Li–Yannakakis algorithm

Sections 3 and 4 of [arXiv:2403.19911](https://arxiv.org/abs/2403.19911).

* `pyrUnion_disjoint_pyramid` — their Lemma 4
* `around_subset_pyrUnion` — their Lemma 3
* `fixedPoint_mem_pyrUnion` — their Lemma 2
* `clyStep` — Algorithm 1, with Observation 1 folded in: every oracle response
  is damped by `(1 − ε/2)`, which makes the map a `(1 − ε/2)`-contraction
  whatever its own contraction factor was
* `clyStep_correct` — their Lemma 5
* `clyAlgorithm_isApproxFixedPoint`, `clyAlgorithm_queries_le`,
  `cly_query_complexity` — their Theorem 1
-/

set_option autoImplicit false

namespace Tfnp.Contraction

variable {k : ℕ}

attribute [local instance] Classical.propDecidable

section Geometry

variable [NeZero k]

/-! ## `ℓ∞` helpers -/

lemma exists_coord_eq_linfDist (x y : Vec k) : ∃ i, |x i - y i| = linfDist x y := by
  obtain ⟨i, _, hi⟩ :=
    Finset.exists_mem_eq_sup' (univ_nonempty_fin (k := k)) (fun j => |x j - y j|)
  refine ⟨i, ?_⟩
  unfold linfDist
  rw [dif_pos (univ_nonempty_fin (k := k))]
  exact hi.symm

lemma linfDist_triangle (x y z : Vec k) : linfDist x z ≤ linfDist x y + linfDist y z := by
  simp only [linfDist_eq_dist]
  exact dist_triangle x y z

/-! ## Ternary sign vectors -/

/-- The real-valued sign function: `1`, `-1` or `0`. -/
noncomputable def sgnR (t : ℝ) : ℝ := if 0 < t then 1 else if t < 0 then -1 else 0

lemma sgnR_spec (t : ℝ) : sgnR t = 1 ∨ sgnR t = -1 ∨ sgnR t = 0 := by
  unfold sgnR; split_ifs <;> simp

lemma sgnR_mul_self_pos {t : ℝ} (h : sgnR t ≠ 0) : sgnR t * t = |t| := by
  unfold sgnR at h ⊢
  split_ifs at h ⊢ with h1 h2
  · rw [one_mul, abs_of_pos h1]
  · rw [neg_one_mul, abs_of_neg h2]
  · exact absurd rfl h

lemma sgnR_eq_zero_iff {t : ℝ} : sgnR t = 0 ↔ t = 0 := by
  unfold sgnR
  constructor
  · intro h; split_ifs at h with h1 h2 <;> [linarith; linarith; skip]
    rcases lt_trichotomy t 0 with h3 | h3 | h3
    · exact absurd h3 h2
    · exact h3
    · exact absurd h3 h1
  · rintro rfl; simp

/-- `s` takes values in `{±1, 0}`. -/
def IsTernary (s : Fin k → ℝ) : Prop := ∀ i, s i = 1 ∨ s i = -1 ∨ s i = 0

lemma IsTernary.sq_of_ne {s : Fin k → ℝ} (hs : IsTernary s) {i : Fin k} (h : s i ≠ 0) :
    s i * s i = 1 := by
  rcases hs i with h1 | h1 | h1
  · rw [h1]; norm_num
  · rw [h1]; norm_num
  · exact absurd h1 h

lemma IsTernary.abs_le_one {s : Fin k → ℝ} (hs : IsTernary s) (i : Fin k) : |s i| ≤ 1 := by
  rcases hs i with h1 | h1 | h1 <;> rw [h1] <;> norm_num

lemma IsTernary.mul_le_abs {s : Fin k → ℝ} (hs : IsTernary s) (i : Fin k) (x : ℝ) :
    s i * x ≤ |x| := by
  calc s i * x ≤ |s i * x| := le_abs_self _
    _ = |s i| * |x| := abs_mul _ _
    _ ≤ 1 * |x| := by nlinarith [hs.abs_le_one i, abs_nonneg x]
    _ = |x| := one_mul _

lemma IsTernary.abs_mul_eq {s : Fin k → ℝ} (hs : IsTernary s) {i : Fin k} (h : s i ≠ 0) (x : ℝ) :
    |s i * x| = |x| := by
  rw [abs_mul]
  rcases hs i with h1 | h1 | h1
  · rw [h1]; norm_num
  · rw [h1]; norm_num
  · exact absurd h1 h

/-! ## Pyramids with real signs -/

/-- `𝒫ᵢ(x, σ) = { y : σ (yᵢ − xᵢ) = ‖y − x‖∞ }`, for a real sign `σ`. -/
def Pyr (i : Fin k) (σ : ℝ) (x : Vec k) : Set (Vec k) :=
  { y | σ * (y i - x i) = linfDist y x }

@[simp] lemma mem_Pyr {i : Fin k} {σ : ℝ} {x y : Vec k} :
    y ∈ Pyr i σ x ↔ σ * (y i - x i) = linfDist y x := Iff.rfl

/-- `⋃_{i : sᵢ ≠ 0} 𝒫ᵢ(x, sᵢ)`. -/
def PyrUnion (s : Fin k → ℝ) (x : Vec k) : Set (Vec k) :=
  { y | ∃ i, s i ≠ 0 ∧ y ∈ Pyr i (s i) x }

/-- Translate `x` by `c · s`. -/
def shiftVec (x : Vec k) (c : ℝ) (s : Fin k → ℝ) : Vec k := fun i => x i + c * s i

@[simp] lemma shiftVec_apply (x : Vec k) (c : ℝ) (s : Fin k → ℝ) (i : Fin k) :
    shiftVec x c s i = x i + c * s i := rfl

lemma linfDist_shiftVec_le {s : Fin k → ℝ} (hs : IsTernary s) (x : Vec k) {c : ℝ}
    (hc : 0 ≤ c) : linfDist (shiftVec x c s) x ≤ c := by
  refine linfDist_le fun i => ?_
  simp only [shiftVec_apply, add_sub_cancel_left, abs_mul, abs_of_nonneg hc]
  nlinarith [hs.abs_le_one i, abs_nonneg (s i)]

/-- The basic displacement identity: moving the apex from `x` to `shiftVec x c s`
shifts the signed coordinate by exactly `c` (at indices where `sᵢ ≠ 0`). -/
lemma signed_shift {s : Fin k → ℝ} (hs : IsTernary s) {i : Fin k} (hi : s i ≠ 0)
    (x y : Vec k) (c : ℝ) :
    s i * (y i - x i) = s i * (y i - shiftVec x c s i) + c := by
  have hsq := hs.sq_of_ne hi
  have e : s i * (y i - shiftVec x c s i) + c
      = s i * (y i - x i) - c * (s i * s i) + c := by
    simp only [shiftVec_apply]; ring
  rw [e, hsq]; ring

/-! ## Lemma 4 -/

/-- **CLY Lemma 4.** For every coordinate `j` there is a sign `φ ∈ {±1}` with
`𝒫ⱼ(a, φ) ∩ ⋃_{i : sᵢ ≠ 0} 𝒫ᵢ(a + 2s, sᵢ) = ∅`. -/
theorem pyrUnion_disjoint_pyramid (a : Vec k) {s : Fin k → ℝ} (hs : IsTernary s)
    (j : Fin k) :
    ∃ φ : Bool, ∀ y ∈ PyrUnion s (shiftVec a 2 s), y ∉ Pyramid j φ a := by
  set b := shiftVec a 2 s with hb
  have key : ∀ y ∈ PyrUnion s b, linfDist y b + 2 ≤ linfDist y a := by
    rintro y ⟨i₀, hi₀, hy⟩
    rw [mem_Pyr] at hy
    have h1 : s i₀ * (y i₀ - a i₀) = linfDist y b + 2 := by
      rw [signed_shift hs hi₀ a y 2, ← hb, hy]
    have h2 : s i₀ * (y i₀ - a i₀) ≤ |y i₀ - a i₀| := hs.mul_le_abs i₀ _
    have h3 : |y i₀ - a i₀| ≤ linfDist y a := abs_sub_le_linfDist y a i₀
    linarith
  by_cases hj : s j = 0
  · -- `s j = 0`: both signs work, since `b j = a j` caps `|y j − a j|` by `‖y − b‖∞`.
    refine ⟨true, fun y hy hmem => ?_⟩
    have hba : b j = a j := by simp [hb, hj]
    rw [mem_pyramid_iff_sign] at hmem
    have h1 : linfDist y a ≤ |y j - a j| := by
      rw [← hmem]
      exact (le_abs_self _).trans_eq (abs_signR_mul _ _)
    have h2 : |y j - a j| = |y j - b j| := by rw [hba]
    have h3 : |y j - b j| ≤ linfDist y b := abs_sub_le_linfDist y b j
    linarith [key y hy]
  · -- `s j ≠ 0`: the opposite sign `−sⱼ` works.
    refine ⟨decide (s j = -1), fun y hy hmem => ?_⟩
    have hsig : signR (decide (s j = -1)) = -s j := by
      rcases hs j with h1 | h1 | h1
      · rw [h1]; norm_num [signR]
      · rw [h1]; norm_num [signR]
      · exact absurd h1 hj
    rw [mem_pyramid_iff_sign, hsig] at hmem
    have hsq := hs.sq_of_ne hj
    have h1 : -s j * (y j - b j) = linfDist y a + 2 := by
      simp only [hb, shiftVec_apply]
      nlinarith [hmem, hsq]
    have h2 : -s j * (y j - b j) ≤ |y j - b j| := by
      calc -s j * (y j - b j) ≤ |(-s j) * (y j - b j)| := le_abs_self _
        _ = |s j * (y j - b j)| := by rw [neg_mul, abs_neg]
        _ = |y j - b j| := hs.abs_mul_eq hj _
    have h3 : |y j - b j| ≤ linfDist y b := abs_sub_le_linfDist y b j
    linarith [key y hy]

/-! ## Lemma 3 -/

/-- **CLY Lemma 3.** Every `x ∈ ⋃_{i : sᵢ ≠ 0} 𝒫ᵢ(b + 2s, sᵢ)` has its unit
`ℓ∞`-ball contained in `⋃_{i : sᵢ ≠ 0} 𝒫ᵢ(b, sᵢ)`. -/
theorem around_subset_pyrUnion (b : Vec k) {s : Fin k → ℝ} (hs : IsTernary s)
    {x : Vec k} (hx : x ∈ PyrUnion s (shiftVec b 2 s)) :
    Around 1 x ⊆ PyrUnion s b := by
  set c := shiftVec b 2 s with hc
  obtain ⟨i₀, hi₀, hxc⟩ := hx
  rw [mem_Pyr] at hxc
  set M := linfDist x c with hM
  have hM0 : 0 ≤ M := linfDist_nonneg _ _
  have hF1 : ∀ i, |x i - c i| ≤ M := fun i => abs_sub_le_linfDist x c i
  have hF2 : s i₀ * (x i₀ - b i₀) = M + 2 := by
    rw [signed_shift hs hi₀ b x 2, ← hc, hxc]
  intro y hy
  have hy1 : ∀ i, |y i - x i| ≤ 1 := by
    intro i
    have := abs_sub_le_linfDist y x i
    exact this.trans hy
  have hF3 : M + 1 ≤ s i₀ * (y i₀ - b i₀) := by
    have hsplit : s i₀ * (y i₀ - b i₀) = s i₀ * (x i₀ - b i₀) + s i₀ * (y i₀ - x i₀) := by ring
    have hlow : -|y i₀ - x i₀| ≤ s i₀ * (y i₀ - x i₀) := by
      have := hs.mul_le_abs i₀ (-(y i₀ - x i₀))
      rw [abs_neg] at this
      nlinarith [this]
    rw [hsplit, hF2]
    linarith [hy1 i₀]
  have hsupp : (Finset.univ.filter (fun i => s i ≠ 0)).Nonempty :=
    ⟨i₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi₀⟩⟩
  obtain ⟨j, hj_mem, hj_max⟩ :=
    Finset.exists_max_image (Finset.univ.filter (fun i => s i ≠ 0))
      (fun i => s i * (y i - b i)) hsupp
  have hjs : s j ≠ 0 := (Finset.mem_filter.mp hj_mem).2
  set V := s j * (y j - b j) with hV
  have hVge : M + 1 ≤ V := by
    refine le_trans hF3 ?_
    exact hj_max i₀ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi₀⟩)
  have hVabs : |y j - b j| = V := by
    have : |V| = |y j - b j| := hs.abs_mul_eq hjs _
    rw [hV, ← this, abs_of_nonneg (by linarith : (0:ℝ) ≤ s j * (y j - b j))]
  have hdom : ∀ i, |y i - b i| ≤ V := by
    intro i
    by_cases hi : s i = 0
    · -- `sᵢ = 0`, so `cᵢ = bᵢ` and `|xᵢ − bᵢ| ≤ M`.
      have hcb : c i = b i := by simp [hc, hi]
      have h1 : |x i - b i| ≤ M := by rw [← hcb]; exact hF1 i
      calc |y i - b i| ≤ |y i - x i| + |x i - b i| := abs_sub_le _ _ _
        _ ≤ 1 + M := by linarith [hy1 i]
        _ ≤ V := by linarith
    · rcases le_or_gt 0 (s i * (y i - b i)) with hpos | hneg
      · -- Same side: maximality of `j` applies.
        have h1 : |y i - b i| = s i * (y i - b i) := by
          have : |s i * (y i - b i)| = |y i - b i| := hs.abs_mul_eq hi _
          rw [← this, abs_of_nonneg hpos]
        rw [h1]
        exact hj_max i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
      · -- Opposite side: then `|yᵢ − bᵢ| ≤ M − 1`.
        have h1 : |y i - b i| = -(s i * (y i - b i)) := by
          have : |s i * (y i - b i)| = |y i - b i| := hs.abs_mul_eq hi _
          rw [← this, abs_of_neg hneg]
        have h2 : -(s i * (y i - b i)) = -(s i * (y i - c i)) - 2 := by
          have := signed_shift hs hi b y 2
          rw [← hc] at this
          linarith
        have h3 : -(s i * (y i - c i)) ≤ |y i - c i| := by
          have := hs.mul_le_abs i (-(y i - c i))
          rw [abs_neg] at this
          nlinarith [this]
        have h4 : |y i - c i| ≤ |y i - x i| + |x i - c i| := abs_sub_le _ _ _
        rw [h1, h2]
        linarith [hy1 i, hF1 i]
  exact ⟨j, hjs, by rw [mem_Pyr, ← hV]; exact (le_antisymm (linfDist_le hdom) (hVabs ▸ abs_sub_le_linfDist y b j)).symm⟩

/-! ## Lemma 2 -/

/-- **CLY Lemma 2.** If `a` is far from being a fixed point of the
`(1−γ)`-contraction `g` — namely `‖g(a) − a‖∞ > 16/γ` — and `sᵢ = sgn(g(a)ᵢ − aᵢ)`,
then the fixed point of `g` lies in `⋃_{i : sᵢ ≠ 0} 𝒫ᵢ(a + 4s, sᵢ)`. -/
theorem fixedPoint_mem_pyrUnion {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (g : Vec k → Vec k) (D : Set (Vec k))
    (hcontract : ∀ x ∈ D, ∀ y ∈ D, linfDist (g x) (g y) ≤ (1 - γ) * linfDist x y)
    {a xs : Vec k} (ha : a ∈ D) (hxs : xs ∈ D) (hfix : g xs = xs)
    (hfar : 16 / γ < linfDist (g a) a)
    {s : Fin k → ℝ} (hsdef : ∀ i, s i = sgnR (g a i - a i)) :
    xs ∈ PyrUnion s (shiftVec a 4 s) := by
  have hs : IsTernary s := fun i => by rw [hsdef i]; exact sgnR_spec _
  set c := shiftVec a 4 s with hc
  have hca : linfDist c a ≤ 4 := linfDist_shiftVec_le hs a (by norm_num)
  have hxa : 8 / γ < linfDist xs a := by
    by_contra hcon
    push_neg at hcon
    have h1 : linfDist (g a) (g xs) ≤ (1 - γ) * linfDist a xs :=
      hcontract a ha xs hxs
    have h2 : linfDist (g a) a ≤ linfDist (g a) (g xs) + linfDist (g xs) a :=
      linfDist_triangle _ _ _
    rw [hfix] at h1 h2
    rw [linfDist_comm a xs] at h1
    have h3 : (0 : ℝ) ≤ linfDist xs a := linfDist_nonneg _ _
    have h4 : 16 / γ = 2 * (8 / γ) := by ring
    nlinarith [hfar, hcon, h1, h2, h3]
  have hγxa : 8 < γ * linfDist xs a := by
    rw [div_lt_iff₀ hγ] at hxa
    linarith [hxa]
  by_contra hout
  obtain ⟨j, hj⟩ := exists_coord_eq_linfDist xs c
  have hcontr_j : |g xs j - g a j| ≤ (1 - γ) * linfDist xs a := by
    calc |g xs j - g a j| ≤ linfDist (g xs) (g a) := abs_sub_le_linfDist _ _ j
      _ ≤ (1 - γ) * linfDist xs a := hcontract xs hxs a ha
  have hgfix : g xs j = xs j := by rw [hfix]
  have htri : linfDist xs a ≤ linfDist xs c + linfDist c a := linfDist_triangle _ _ _
  by_cases hsj : s j = 0
  · -- Part 1: `sⱼ = 0`, so `g(a)ⱼ = aⱼ = cⱼ`.
    have hga : g a j = a j := by
      have := hsdef j
      rw [hsj] at this
      have := sgnR_eq_zero_iff.mp this.symm
      linarith
    have hcj : c j = a j := by simp [hc, hsj]
    have habs : |xs j - c j| = linfDist xs c := hj
    have hb1 : |g xs j - a j| ≤ (1 - γ) * linfDist xs a := by rw [← hga]; exact hcontr_j
    have hb2 := abs_le.mp hb1
    rcases abs_cases (xs j - c j) with ⟨heq, _⟩ | ⟨heq, _⟩
    · -- `xs j ≥ c j`
      rw [heq] at habs
      nlinarith [hb2.2, habs, htri, hca, hγxa, hgfix, hcj]
    · -- `xs j ≤ c j`
      rw [heq] at habs
      nlinarith [hb2.1, habs, htri, hca, hγxa, hgfix, hcj]
  · -- Part 2: `sⱼ ≠ 0`.
    have hsq := hs.sq_of_ne hsj
    have hnotj : ¬ (s j * (xs j - c j) = linfDist xs c) := fun h => hout ⟨j, hsj, h⟩
    have hopp : s j * (xs j - c j) = -linfDist xs c := by
      have habs : |s j * (xs j - c j)| = |xs j - c j| := hs.abs_mul_eq hsj _
      rw [hj] at habs
      rcases abs_cases (s j * (xs j - c j)) with ⟨he, _⟩ | ⟨he, _⟩
      · exact absurd (by linarith [habs, he]) hnotj
      · linarith [habs, he]
    have hsa : s j * (xs j - a j) = 4 - linfDist xs c := by
      have := signed_shift hs hsj a xs 4
      rw [← hc] at this
      linarith [hopp, this]
    have hxc4 : 4 ≤ linfDist xs c := by
      by_contra hcon
      push_neg at hcon
      have : linfDist xs a ≤ 8 := by linarith [htri, hca]
      have h8 : (8 : ℝ) ≤ 8 / γ := by
        rw [le_div_iff₀ hγ]; nlinarith [hγ1, hγ]
      linarith [hxa]
    have hsign_contr : s j * (g a j - g xs j) ≤ (1 - γ) * linfDist xs a := by
      calc s j * (g a j - g xs j) ≤ |g a j - g xs j| := hs.mul_le_abs j _
        _ = |g xs j - g a j| := abs_sub_comm _ _
        _ ≤ (1 - γ) * linfDist xs a := hcontr_j
    have hpos : 0 < s j * (g a j - a j) := by
      rw [hsdef j]
      have hne : sgnR (g a j - a j) ≠ 0 := by rw [← hsdef j]; exact hsj
      rw [sgnR_mul_self_pos hne]
      exact abs_pos.mpr (fun h => hne (sgnR_eq_zero_iff.mpr h))
    have hfinal : s j * (g xs j) > s j * (xs j) := by
      nlinarith [hsign_contr, hγxa, htri, hca, hsa, hpos]
    rw [hgfix] at hfinal
    exact lt_irrefl _ hfinal

/-! ## Supporting facts -/

/-- Clamping into a box is `1`-Lipschitz coordinatewise. -/
lemma abs_clamp_sub_clamp_le {lo hi : ℝ} (a b : ℝ) :
    |max lo (min hi a) - max lo (min hi b)| ≤ |a - b| := by
  have hmin : |min hi a - min hi b| ≤ |a - b| := by
    rw [min_comm hi a, min_comm hi b]
    calc |min a hi - min b hi| ≤ max |a - b| |hi - hi| := abs_min_sub_min_le_max _ _ _ _
      _ = |a - b| := by simp
  calc |max lo (min hi a) - max lo (min hi b)|
      = |max (min hi a) lo - max (min hi b) lo| := by rw [max_comm lo, max_comm lo]
    _ ≤ |min hi a - min hi b| := abs_max_sub_max_le_abs _ _ _
    _ ≤ |a - b| := hmin

lemma linfDist_clampBox_mono (lo hi : ℝ) (x y : Vec k) :
    linfDist (clampBox lo hi x) (clampBox lo hi y) ≤ linfDist x y :=
  linfDist_le fun i =>
    (abs_clamp_sub_clamp_le _ _).trans (abs_sub_le_linfDist x y i)

lemma clampBox_eq_self {lo hi : ℝ} {z : Vec k} (hz : ∀ i, lo ≤ z i ∧ z i ≤ hi) :
    clampBox lo hi z = z := by
  funext i
  simp only [clampBox]
  rw [min_eq_right (hz i).2, max_eq_right (hz i).1]

/-- **Banach.** A contraction of the unit cube into itself has a fixed point in
the cube, obtained by extending the map to all of `ℝ^k` through the clamp. -/
lemma exists_fixedPoint_of_contraction {lam : ℝ} {h : Vec k → Vec k}
    (hmaps : ∀ x, InUnitCube x → InUnitCube (h x))
    (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    (hcontract : ∀ x y, InUnitCube x → InUnitCube y →
      linfDist (h x) (h y) ≤ lam * linfDist x y) :
    ∃ x, InUnitCube x ∧ h x = x := by
  have hcube : ∀ z : Vec k, InUnitCube (clampBox 0 1 z) := by
    intro z i
    exact Set.mem_Icc.mpr (clampBox_mem 0 1 (by norm_num) z i)
  set H : Vec k → Vec k := fun z => h (clampBox 0 1 z) with hH
  have hlip : ∀ x y : Vec k, dist (H x) (H y) ≤ (⟨lam, hlam0⟩ : NNReal) * dist x y := by
    intro x y
    simp only [hH, ← linfDist_eq_dist]
    calc linfDist (h (clampBox 0 1 x)) (h (clampBox 0 1 y))
        ≤ lam * linfDist (clampBox 0 1 x) (clampBox 0 1 y) :=
          hcontract _ _ (hcube x) (hcube y)
      _ ≤ lam * linfDist x y := by
          have := linfDist_clampBox_mono (k := k) 0 1 x y
          nlinarith [linfDist_nonneg (clampBox (0:ℝ) 1 x) (clampBox (0:ℝ) 1 y)]
  have hcon : ContractingWith (⟨lam, hlam0⟩ : NNReal) H := by
    refine ⟨?_, LipschitzWith.of_dist_le_mul hlip⟩
    rw [← NNReal.coe_lt_coe]
    simpa using hlam1
  obtain ⟨y, hy, -, -⟩ := hcon.exists_fixedPoint 0 (edist_ne_top _ _)
  have hyfix : h (clampBox 0 1 y) = y := hy
  have hycube : InUnitCube y := by rw [← hyfix]; exact hmaps _ (hcube y)
  refine ⟨y, hycube, ?_⟩
  rw [clampBox_eq_self (fun i => Set.mem_Icc.mp (hycube i))] at hyfix
  exact hyfix

/-- Scaling a pair of vectors scales their `ℓ∞` distance. -/
lemma linfDist_smul (c : ℝ) (x y : Vec k) :
    linfDist (fun i => c * x i) (fun i => c * y i) = |c| * linfDist x y := by
  refine le_antisymm (linfDist_le fun i => ?_) ?_
  · have : |c * x i - c * y i| = |c| * |x i - y i| := by rw [← abs_mul]; ring_nf
    rw [this]
    nlinarith [abs_nonneg c, abs_sub_le_linfDist x y i]
  · obtain ⟨i, hi⟩ := exists_coord_eq_linfDist x y
    have h1 : |c| * |x i - y i| = |c * x i - c * y i| := by rw [← abs_mul]; ring_nf
    rw [← hi, h1]
    exact abs_sub_le_linfDist (fun i => c * x i) (fun i => c * y i) i

lemma shiftVec_shiftVec (a : Vec k) (s : Fin k → ℝ) :
    shiftVec (shiftVec a 2 s) 2 s = shiftVec a 4 s := by
  funext i; simp only [shiftVec_apply]; ring

/-! ## The rescaled, damped map -/

/-- `g(x) = n · (1−δ) · f(x/n)`, a `(1−δ)`-contraction of `[0,n]^k`. -/
noncomputable def gMap (n : ℕ) (δ : ℝ) (f : Vec k → Vec k) : Vec k → Vec k :=
  fun x i => (n : ℝ) * ((1 - δ) * f (fun j => x j / (n : ℝ)) i)

lemma gMap_contract {n : ℕ} (hn : 0 < n) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {f : Vec k → Vec k} {lam : ℝ} (hf : IsLInfContraction f lam)
    (x y : Vec k) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ (n : ℝ)) (hy : ∀ i, 0 ≤ y i ∧ y i ≤ (n : ℝ)) :
    linfDist (gMap n δ f x) (gMap n δ f y) ≤ (1 - δ) * linfDist x y := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hxc : InUnitCube (fun j => x j / (n : ℝ)) := by
    intro i
    exact Set.mem_Icc.mpr ⟨div_nonneg (hx i).1 hnR.le, (div_le_one hnR).mpr (hx i).2⟩
  have hyc : InUnitCube (fun j => y j / (n : ℝ)) := by
    intro i
    exact Set.mem_Icc.mpr ⟨div_nonneg (hy i).1 hnR.le, (div_le_one hnR).mpr (hy i).2⟩
  have hscale : linfDist x y
      = (n : ℝ) * linfDist (fun j => x j / (n : ℝ)) (fun j => y j / (n : ℝ)) := by
    have h := linfDist_smul (k := k) ((n : ℝ)⁻¹) x y
    rw [show (fun j => x j / (n : ℝ)) = (fun j => (n : ℝ)⁻¹ * x j) by funext j; ring,
      show (fun j => y j / (n : ℝ)) = (fun j => (n : ℝ)⁻¹ * y j) by funext j; ring, h,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (n:ℝ)⁻¹)]
    field_simp
  have hgeq : ∀ z : Vec k, gMap n δ f z
      = fun i => ((n : ℝ) * (1 - δ)) * f (fun j => z j / (n : ℝ)) i := by
    intro z; funext i; simp only [gMap]; ring
  rw [hgeq x, hgeq y, linfDist_smul,
    abs_of_nonneg (by nlinarith : (0:ℝ) ≤ (n:ℝ) * (1 - δ))]
  have hcon := hf.contracts _ _ hxc hyc
  have hS : (0:ℝ) ≤ linfDist (fun j => x j / (n : ℝ)) (fun j => y j / (n : ℝ)) :=
    linfDist_nonneg _ _
  have hL : (0:ℝ) ≤ linfDist (f fun j => x j / (n:ℝ)) (f fun j => y j / (n:ℝ)) :=
    linfDist_nonneg _ _
  have hc0 : (0:ℝ) ≤ (n:ℝ) * (1 - δ) := by nlinarith
  rw [hscale]
  calc (n:ℝ) * (1 - δ) * linfDist (f fun j => x j / (n:ℝ)) (f fun j => y j / (n:ℝ))
      ≤ (n:ℝ) * (1 - δ) * (lam * linfDist (fun j => x j / (n:ℝ)) (fun j => y j / (n:ℝ))) := by
        exact mul_le_mul_of_nonneg_left hcon hc0
    _ ≤ (n:ℝ) * (1 - δ) * (1 * linfDist (fun j => x j / (n:ℝ)) (fun j => y j / (n:ℝ))) := by
        exact mul_le_mul_of_nonneg_left
          (by nlinarith [hS, hf.lam_lt_one.le]) hc0
    _ = (1 - δ) * ((n:ℝ) * linfDist (fun j => x j / (n:ℝ)) (fun j => y j / (n:ℝ))) := by ring

/-! ## The algorithm -/

/-- The CLY algorithm (their Algorithm 1), with CLY's Observation 1 folded in:
the oracle response is damped by `(1−δ)` before use, which makes the map a
`(1−δ)`-contraction whatever its original contraction factor was.

`n` is the grid scale, `δ` the accuracy (half the final `ε`), `N` the round
budget and `T` the candidate set. -/
noncomputable def clyStep {k : ℕ} (n : ℕ) (δ : ℝ) :
    ℕ → Finset (Vec k) → CQueryAlg k (Vec k)
  | 0, _ => QueryAlg.pure 0
  | N + 1, T =>
    let a : Vec k := clyChooseBalanced n T
    let qp : Vec k := fun i => a i / (n : ℝ)
    do
      let resp ← QueryAlg.ask qp
      let hresp : Vec k := fun i => (1 - δ) * resp i
      if linfDist qp hresp ≤ δ then
        QueryAlg.pure qp
      else
        let s : Fin k → ℝ := fun i => sgnR ((n : ℝ) * hresp i - a i)
        clyStep n δ N (T.filter (fun y => y ∈ PyrUnion s (shiftVec a 2 s)))

omit [NeZero k] in
/-- The algorithm makes at most `N` queries. -/
theorem clyStep_queries (n : ℕ) (δ : ℝ) (N : ℕ) (f : Vec k → Vec k)
    (T : Finset (Vec k)) : (clyStep n δ N T).queries f ≤ N := by
  induction N generalizing T with
  | zero => simp [clyStep]
  | succ N ih =>
    rw [clyStep]
    simp only [QueryAlg.queries_bind, QueryAlg.queries_ask, QueryAlg.run_ask]
    rw [show (N + 1 : ℕ) = 1 + N from Nat.add_comm N 1]
    apply Nat.add_le_add_left
    split_ifs
    · simp [QueryAlg.queries_pure]
    · exact ih _

/-- Halving: the new candidate set is at most half the old one. -/
theorem clyStep_halving [NeZero k] (n : ℕ) (T : Finset (Vec k))
    (hTsub : T ⊆ grid n k) {s : Fin k → ℝ} (hs : IsTernary s)
    (a : Vec k) (ha : a = clyChooseBalanced n T) :
    2 * (T.filter (fun y => y ∈ PyrUnion s (shiftVec a 2 s))).card ≤ T.card := by
  subst ha
  choose φ hφ using fun j =>
    pyrUnion_disjoint_pyramid (k := k) (clyChooseBalanced n T) hs j
  have hbal := clyChooseBalanced_spec n T hTsub φ
  set A := T.filter
    (fun y => ∃ i, y ∈ Pyramid i (φ i) (clyChooseBalanced n T)) with hA
  set B := T.filter
    (fun y => y ∈ PyrUnion s (shiftVec (clyChooseBalanced n T) 2 s)) with hB
  have hcardA : T.card ≤ 2 * A.card := hbal
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro y hyA hyB
    obtain ⟨-, i, hi⟩ := Finset.mem_filter.mp hyA
    obtain ⟨-, hmem⟩ := Finset.mem_filter.mp hyB
    exact hφ i _ hmem hi
  have hsum : A.card + B.card ≤ T.card := by
    have hsub : A ∪ B ⊆ T :=
      Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    have := Finset.card_le_card hsub
    rwa [Finset.card_union_of_disjoint hdisj] at this
  omega

/-- The point returned always lies in the unit cube. -/
theorem clyStep_run_in_unit_cube (n : ℕ) (δ : ℝ) (N : ℕ) (T : Finset (Vec k))
    (f : Vec k → Vec k) (hn : 0 < n) : InUnitCube ((clyStep n δ N T).run f) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  induction N generalizing T with
  | zero => intro i; simp [clyStep, QueryAlg.run_pure]
  | succ N ih =>
    rw [clyStep]
    simp only [QueryAlg.run_bind, QueryAlg.run_ask]
    split_ifs
    · simp only [QueryAlg.run_pure]
      intro i
      obtain ⟨h1, h2⟩ := clyChooseBalanced_mem_cube n T i
      exact Set.mem_Icc.mpr ⟨div_nonneg h1 hnR.le, (div_le_one hnR).mpr h2⟩
    · exact ih _

/-! ## Correctness -/

/-- **CLY Lemma 5 + Theorem 1.** With the grid fine enough for the accuracy
(`16/δ ≤ n·δ`) and enough rounds, the algorithm returns a `2δ`-fixed point of
the oracle `f`.

The induction carries CLY's two invariants: the candidate set always contains
every even grid point within `ℓ∞`-distance `1` of the fixed point of `g`
(so it is never empty), and it halves each round (so the budget runs out
first). -/
theorem clyStep_correct [NeZero k] {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {n : ℕ} (hn : 0 < n) (hnδ : 16 / δ ≤ (n : ℝ) * δ)
    {f : Vec k → Vec k} {lam : ℝ} (hf : IsLInfContraction f lam)
    {xs : Vec k} (hxs_cube : ∀ i, 0 ≤ xs i ∧ xs i ≤ (n : ℝ))
    (hxs_fix : gMap n δ f xs = xs) :
    ∀ (N : ℕ) (T : Finset (Vec k)), T ⊆ grid n k →
      (∀ y ∈ grid n k, linfDist y xs ≤ 1 → y ∈ T) →
      T.card < 2 ^ N →
      linfDist ((clyStep n δ N T).run f) (f ((clyStep n δ N T).run f)) ≤ 2 * δ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hne : ∀ T : Finset (Vec k),
      (∀ y ∈ grid n k, linfDist y xs ≤ 1 → y ∈ T) → T.Nonempty := by
    intro T hTinv
    obtain ⟨y, hy, hyd⟩ := exists_grid_near (n := n) hxs_cube
    exact ⟨y, hTinv y hy hyd⟩
  intro N
  induction N with
  | zero =>
    intro T _ hTinv hTcard
    rw [pow_zero, Nat.lt_one_iff, Finset.card_eq_zero] at hTcard
    exact absurd hTcard (Finset.nonempty_iff_ne_empty.mp (hne T hTinv))
  | succ N ih =>
    intro T hTsub hTinv hTcard
    rw [clyStep]
    simp only [QueryAlg.run_bind, QueryAlg.run_ask]
    set a : Vec k := clyChooseBalanced n T with ha
    set qp : Vec k := fun i => a i / (n : ℝ) with hqp
    have ha_cube : ∀ i, 0 ≤ a i ∧ a i ≤ (n : ℝ) := clyChooseBalanced_mem_cube n T
    have hqp_cube : InUnitCube qp := by
      intro i
      exact Set.mem_Icc.mpr
        ⟨div_nonneg (ha_cube i).1 hnR.le, (div_le_one hnR).mpr (ha_cube i).2⟩
    have hfqp_cube : InUnitCube (f qp) := hf.preserves_cube qp hqp_cube
    split_ifs with htest
    · -- Success: `qp` is a `2δ`-fixed point of `f`.
      simp only [QueryAlg.run_pure]
      have hdamp : linfDist (fun i => (1 - δ) * f qp i) (f qp) ≤ δ := by
        refine linfDist_le fun i => ?_
        have h1 := Set.mem_Icc.mp (hfqp_cube i)
        have : (1 - δ) * f qp i - f qp i = -(δ * f qp i) := by ring
        rw [this, abs_neg, abs_of_nonneg (by nlinarith [h1.1, hδ0.le])]
        nlinarith [h1.1, h1.2, hδ0.le]
      calc linfDist qp (f qp)
          ≤ linfDist qp (fun i => (1 - δ) * f qp i)
              + linfDist (fun i => (1 - δ) * f qp i) (f qp) := linfDist_triangle _ _ _
        _ ≤ δ + δ := add_le_add htest hdamp
        _ = 2 * δ := by ring
    · -- Failure: the candidate set halves and the invariants persist.
      set s : Fin k → ℝ := fun i => sgnR ((n : ℝ) * ((1 - δ) * f qp i) - a i) with hs_def
      have hs : IsTernary s := fun i => sgnR_spec _
      have hga : ∀ i, gMap n δ f a i = (n : ℝ) * ((1 - δ) * f qp i) := by
        intro i; simp only [gMap, hqp]
      have haqp : a = fun i => (n : ℝ) * qp i := by
        funext i; simp only [hqp]; field_simp
      have hfar : 16 / δ < linfDist (gMap n δ f a) a := by
        push_neg at htest
        have hrw : linfDist (gMap n δ f a) a
            = (n : ℝ) * linfDist (fun i => (1 - δ) * f qp i) qp := by
          rw [show gMap n δ f a = fun i => (n : ℝ) * ((1 - δ) * f qp i) by funext i; exact hga i,
            haqp, linfDist_smul, abs_of_nonneg hnR.le]
        rw [hrw, linfDist_comm]
        nlinarith [htest, hnδ, hnR]
      have hlem2 : xs ∈ PyrUnion s (shiftVec a 4 s) := by
        refine fixedPoint_mem_pyrUnion hδ0 hδ1 (gMap n δ f)
          {z : Vec k | ∀ i, 0 ≤ z i ∧ z i ≤ (n : ℝ)}
          (fun x hx y hy => gMap_contract hn hδ0 hδ1 hf x y hx hy)
          ha_cube hxs_cube hxs_fix hfar (fun i => by rw [hs_def, hga i])
      have hlem3 : Around 1 xs ⊆ PyrUnion s (shiftVec a 2 s) :=
        around_subset_pyrUnion (shiftVec a 2 s) hs
          (by rw [shiftVec_shiftVec]; exact hlem2)
      refine ih _ (Finset.filter_subset _ _ |>.trans hTsub) ?_ ?_
      · -- Invariant preserved.
        intro y hy hyd
        refine Finset.mem_filter.mpr ⟨hTinv y hy hyd, hlem3 ?_⟩
        exact hyd
      · -- Budget: the candidate set at least halves.
        show (T.filter (fun y => y ∈ PyrUnion s (shiftVec a 2 s))).card < 2 ^ N
        have hhalve := clyStep_halving n T hTsub hs a ha
        have hpow : (2 : ℕ) ^ (N + 1) = 2 * 2 ^ N := by ring
        omega

/-- The damped map `(1−δ)·f` has a fixed point in the cube; rescaling by `n`
gives a fixed point of `gMap n δ f` in `[0, n]^k`. -/
lemma exists_gMap_fixedPoint [NeZero k] {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {n : ℕ} (hn : 0 < n) {f : Vec k → Vec k} {lam : ℝ} (hf : IsLInfContraction f lam) :
    ∃ xs : Vec k, (∀ i, 0 ≤ xs i ∧ xs i ≤ (n : ℝ)) ∧ gMap n δ f xs = xs := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmaps : ∀ x, InUnitCube x → InUnitCube (fun i => (1 - δ) * f x i) := by
    intro x hx i
    have h1 := Set.mem_Icc.mp (hf.preserves_cube x hx i)
    exact Set.mem_Icc.mpr ⟨by nlinarith [h1.1, hδ1], by nlinarith [h1.1, h1.2, hδ0.le]⟩
  have hcontract : ∀ x y, InUnitCube x → InUnitCube y →
      linfDist (fun i => (1 - δ) * f x i) (fun i => (1 - δ) * f y i)
        ≤ (1 - δ) * linfDist x y := by
    intro x y hx hy
    rw [linfDist_smul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - δ)]
    have h1 := hf.contracts x y hx hy
    have h2 : (0 : ℝ) ≤ 1 - δ := by linarith
    calc (1 - δ) * linfDist (f x) (f y) ≤ (1 - δ) * (lam * linfDist x y) :=
          mul_le_mul_of_nonneg_left h1 h2
      _ ≤ (1 - δ) * linfDist x y :=
          mul_le_mul_of_nonneg_left
            (by nlinarith [hf.lam_lt_one.le, linfDist_nonneg x y]) h2
  obtain ⟨x1, hx1cube, hx1fix⟩ :=
    exists_fixedPoint_of_contraction hmaps (by linarith : (0:ℝ) ≤ 1 - δ)
      (by linarith : (1:ℝ) - δ < 1) hcontract
  refine ⟨fun i => (n : ℝ) * x1 i, fun i => ?_, ?_⟩
  · have := Set.mem_Icc.mp (hx1cube i)
    exact ⟨by nlinarith [this.1], by nlinarith [this.2]⟩
  · funext i
    have hdiv : (fun j => ((n : ℝ) * x1 j) / (n : ℝ)) = x1 := by
      funext j; field_simp
    simp only [gMap, hdiv]
    have := congrFun hx1fix i
    simp only at this
    rw [this]

/-! ## The instantiation -/

/-- Grid scale `n ≍ 1/ε²`: fine enough that `16/δ ≤ n·δ` for `δ = ε/2`. -/
noncomputable def clyGrid (ε : ℝ) : ℕ := ⌈64 / ε ^ 2⌉₊

/-- Round budget `O(k log(1/ε))`. -/
noncomputable def clyBudget (k : ℕ) (ε : ℝ) : ℕ := k * (Nat.log 2 (clyGrid ε) + 2) + 1

lemma clyGrid_pos {ε : ℝ} (hε : 0 < ε) : 0 < clyGrid ε := by
  rw [clyGrid, Nat.lt_ceil]
  push_cast
  positivity

lemma clyGrid_ge {ε : ℝ} (hε : 0 < ε) : 64 / ε ^ 2 ≤ (clyGrid ε : ℝ) := Nat.le_ceil _

lemma clyGrid_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) : (clyGrid ε : ℝ) ≤ 65 / ε ^ 2 := by
  have h1 : (clyGrid ε : ℝ) < 64 / ε ^ 2 + 1 := Nat.ceil_lt_add_one (by positivity)
  have h2 : (1 : ℝ) ≤ 1 / ε ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have : (64 : ℝ) / ε ^ 2 + 1 ≤ 65 / ε ^ 2 := by
    rw [div_add' _ _ _ (by positivity), div_le_div_iff_of_pos_right (by positivity)]
    nlinarith [h2]
  linarith

/-- The round budget exhausts the grid. -/
lemma grid_card_lt (n k : ℕ) : (grid n k).card < 2 ^ (k * (Nat.log 2 n + 2) + 1) := by
  have hstep : n + 1 ≤ 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  calc (grid n k).card = (n + 1) ^ k := grid_card n k
    _ ≤ (2 ^ (Nat.log 2 n + 1)) ^ k := Nat.pow_le_pow_left hstep k
    _ = 2 ^ ((Nat.log 2 n + 1) * k) := by rw [← pow_mul]
    _ < 2 ^ (k * (Nat.log 2 n + 2) + 1) := Nat.pow_lt_pow_right one_lt_two (by nlinarith)

lemma natLog_clyGrid_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (Nat.log 2 (clyGrid ε) : ℝ)
      ≤ (Real.log 65 + 2 * Real.log (1 / ε)) * (1 / Real.log 2) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hn0 : clyGrid ε ≠ 0 := (clyGrid_pos hε).ne'
  have hpow : ((2 : ℝ)) ^ (Nat.log 2 (clyGrid ε)) ≤ (clyGrid ε : ℝ) := by
    have := Nat.pow_log_le_self 2 hn0
    exact_mod_cast this
  have hle : ((2 : ℝ)) ^ (Nat.log 2 (clyGrid ε)) ≤ 65 / ε ^ 2 :=
    hpow.trans (clyGrid_le hε hε1)
  have hlog := Real.log_le_log (by positivity) hle
  rw [Real.log_pow] at hlog
  have hrhs : Real.log (65 / ε ^ 2) = Real.log 65 + 2 * Real.log (1 / ε) := by
    rw [Real.log_div (by norm_num) (by positivity), Real.log_pow,
      Real.log_div one_ne_zero (ne_of_gt hε), Real.log_one]
    push_cast
    ring
  rw [hrhs] at hlog
  rw [← le_div_iff₀ hlog2] at hlog
  calc (Nat.log 2 (clyGrid ε) : ℝ)
      ≤ (Real.log 65 + 2 * Real.log (1 / ε)) / Real.log 2 := hlog
    _ = (Real.log 65 + 2 * Real.log (1 / ε)) * (1 / Real.log 2) := by ring

/-! ## Main theorem -/

/-- The assembled algorithm: grid scale `⌈64/ε²⌉`, accuracy `δ = ε/2`,
`O(k log(1/ε))` rounds, starting from the full even grid. -/
noncomputable def clyAlgorithm (k : ℕ) (ε : ℝ) : CQueryAlg k (Vec k) :=
  clyStep (clyGrid ε) (ε / 2) (clyBudget k ε) (grid (clyGrid ε) k)

/-- **Correctness of the concrete algorithm.** For every dimension `k`, accuracy
`ε ∈ (0, 1]` and `ℓ∞`-contraction `f` of any contraction factor, `clyAlgorithm k ε`
returns an `ε`-approximate fixed point of `f`. -/
theorem clyAlgorithm_isApproxFixedPoint (k : ℕ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {lam : ℝ} (f : Vec k → Vec k) (hf : IsLInfContraction f lam) :
    IsApproxFixedPoint f ε ((clyAlgorithm k ε).run f) := by
  have hnpos : 0 < clyGrid ε := clyGrid_pos hε
  rcases Nat.eq_zero_or_pos k with hk | hk
  · -- `k = 0`: the cube is a point and `linfDist` is `0`.
    subst hk
    refine ⟨fun i => i.elim0, ?_⟩
    unfold linfDist
    rw [dif_neg (by simp)]
    exact hε.le
  · haveI : NeZero k := ⟨hk.ne'⟩
    have hδ0 : (0 : ℝ) < ε / 2 := by linarith
    have hδ1 : ε / 2 ≤ 1 := by linarith
    have hnδ : 16 / (ε / 2) ≤ (clyGrid ε : ℝ) * (ε / 2) := by
      have h1 : (64 : ℝ) / ε ^ 2 ≤ (clyGrid ε : ℝ) := clyGrid_ge hε
      rw [div_le_iff₀ (by linarith : (0:ℝ) < ε / 2)]
      rw [div_le_iff₀ (by positivity : (0:ℝ) < ε ^ 2)] at h1
      nlinarith [h1, hε]
    obtain ⟨xs, hxs_cube, hxs_fix⟩ := exists_gMap_fixedPoint hδ0 hδ1 hnpos hf
    have hmain := clyStep_correct hδ0 hδ1 hnpos hnδ hf hxs_cube hxs_fix
      (clyBudget k ε) (grid (clyGrid ε) k) (Finset.Subset.refl _) (fun y hy _ => hy)
      (grid_card_lt (clyGrid ε) k)
    exact ⟨clyStep_run_in_unit_cube _ _ _ _ _ hnpos, by
      have : linfDist ((clyAlgorithm k ε).run f) (f ((clyAlgorithm k ε).run f))
          ≤ 2 * (ε / 2) := hmain
      linarith [this]⟩

/-- **Query bound for the concrete algorithm**, in closed form: at most
`k · (⌊log₂ ⌈64/ε²⌉⌋ + 2) + 1` queries, whatever the oracle. -/
theorem clyAlgorithm_queries_le (k : ℕ) (ε : ℝ) (f : Vec k → Vec k) :
    (clyAlgorithm k ε).queries f ≤ k * (Nat.log 2 ⌈64 / ε ^ 2⌉₊ + 2) + 1 :=
  clyStep_queries _ _ _ _ _

/-- The closed-form budget is `O(k log(1/ε))`, with the explicit constant
`C = 3 + (2 + log 65)/log 2 < 12`. -/
theorem clyBudget_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (k : ℕ) :
    (clyBudget k ε : ℝ)
      ≤ (3 + 2 * (1 / Real.log 2) + Real.log 65 * (1 / Real.log 2))
          * ((k : ℝ) + 1) * (Real.log (1/ε) + 1) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog65 : (0 : ℝ) ≤ Real.log 65 := Real.log_nonneg (by norm_num)
  set Λ := Real.log (1 / ε) with hΛ_def
  have hΛ : (0 : ℝ) ≤ Λ := by
    rw [hΛ_def]; apply Real.log_nonneg; rw [le_div_iff₀ hε]; linarith
  set β := 1 / Real.log 2 with hβ_def
  have hβ : (0 : ℝ) < β := by rw [hβ_def]; positivity
  set n := clyGrid ε with hn_def
  have hsq : (k : ℝ) ≤ (k : ℝ) + 1 := by linarith
  have hL := natLog_clyGrid_le hε hε1
  rw [← hn_def, ← hΛ_def, ← hβ_def] at hL
  have hexp : (clyBudget k ε : ℝ) = (k : ℝ) * ((Nat.log 2 n : ℝ) + 2) + 1 := by
    unfold clyBudget; rw [← hn_def]; push_cast; ring
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hsq0 : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
  have hone : (1 : ℝ) ≤ ((k : ℝ) + 1) * (Λ + 1) := by
    nlinarith [hΛ, Nat.cast_nonneg (α := ℝ) k]
  have hA : (k : ℝ) * ((Nat.log 2 n : ℝ) + 2) + 1
      ≤ (k : ℝ) * ((Real.log 65 * β + 2 * Λ * β) + 2) + 1 := by
    nlinarith [hL, hk0]
  have hB : (Real.log 65 * β + 2 * Λ * β) + 2
      ≤ (2 + 2 * β + Real.log 65 * β) * (1 + Λ) := by
    nlinarith [hΛ, hβ, hlog65, mul_nonneg (mul_nonneg hlog65 hβ.le) hΛ]
  have hC : (k : ℝ) * ((Real.log 65 * β + 2 * Λ * β) + 2)
      ≤ ((k : ℝ) + 1) * ((2 + 2 * β + Real.log 65 * β) * (1 + Λ)) := by
    have hXnn : (0:ℝ) ≤ (Real.log 65 * β + 2 * Λ * β) + 2 := by
      nlinarith [hΛ, hβ, hlog65, mul_nonneg hlog65 hβ.le, mul_nonneg hΛ hβ.le]
    calc (k : ℝ) * ((Real.log 65 * β + 2 * Λ * β) + 2)
        ≤ ((k : ℝ) + 1) * ((Real.log 65 * β + 2 * Λ * β) + 2) := by
          nlinarith [hsq, hXnn]
      _ ≤ ((k : ℝ) + 1) * ((2 + 2 * β + Real.log 65 * β) * (1 + Λ)) :=
          mul_le_mul_of_nonneg_left hB hsq0
  rw [hexp]
  nlinarith [hA, hC, hone]

/--
**Main theorem (Chen–Li–Yannakakis, STOC 2024), existential form.** There is a
uniform constant `C` and a family of query algorithms `A k ε` such that for every
dimension `k`, accuracy `ε ∈ (0, 1]` and every `ℓ∞`-contraction
`f : [0,1]^k → [0,1]^k` — with *any* contraction constant `λ ∈ [0,1)` — running
`A k ε` on `f` returns an `ε`-approximate fixed point using at most
`C · k · log(1/ε)` queries.

For most uses `clyAlgorithm_isApproxFixedPoint` and `clyAlgorithm_queries_le`
are more convenient: they name the algorithm and give the bound in closed form.
-/
theorem cly_query_complexity :
    ∃ (A : (k : ℕ) → ℝ → CQueryAlg k (Vec k)) (C : ℝ),
      0 ≤ C ∧
      ∀ (k : ℕ) (ε : ℝ), 0 < ε → ε ≤ 1 →
        ∀ {lam : ℝ} (f : Vec k → Vec k), IsLInfContraction f lam →
          IsApproxFixedPoint f ε ((A k ε).run f) ∧
          ((A k ε).queries f : ℝ) ≤ C * ((k : ℝ) + 1) * (Real.log (1/ε) + 1) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog65 : (0 : ℝ) ≤ Real.log 65 := Real.log_nonneg (by norm_num)
  refine ⟨clyAlgorithm, 3 + 2 * (1 / Real.log 2) + Real.log 65 * (1 / Real.log 2),
    by positivity, fun k ε hε hε1 lam f hf =>
      ⟨clyAlgorithm_isApproxFixedPoint k hε hε1 f hf, ?_⟩⟩
  refine le_trans ?_ (clyBudget_le hε hε1 k)
  exact_mod_cast clyStep_queries (clyGrid ε) (ε / 2) (clyBudget k ε) f
    (grid (clyGrid ε) k)

end Geometry
