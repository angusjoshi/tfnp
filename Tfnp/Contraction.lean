import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Tactic.Positivity
import Tfnp.QueryModel
import Tfnp.Box

/-!
# `ℓ∞`-contraction fixpoints: geometry and balanced points

Supporting material for the main result of

> Xi Chen, Yuhao Li and Mihalis Yannakakis.
> *Computing a Fixed Point of Contraction Maps in Polynomial Queries.*
> STOC 2024. [arXiv:2403.19911](https://arxiv.org/abs/2403.19911)

The algorithm and its correctness are in `Tfnp/Algorithm.lean`.

The one deviation from the paper: a balanced point of `T` is obtained as a
minimiser of the `ℓ∞` Fermat–Weber functional `Φ(c) = ∑_{y ∈ T} ‖y − c‖∞`
(`exists_balanced_point_box`), so existence is compactness rather than Brouwer.
The candidate set is then the full integer `grid`, with no parity condition:
that condition exists in the paper only to support its rounding step, which
this route does not use.
-/

set_option autoImplicit false

namespace Tfnp.Contraction

variable {k : ℕ}

/-- A vector in `ℝ^k`. -/
abbrev Vec (k : ℕ) : Type := Fin k → ℝ

/-- A vector lies in the closed unit cube `[0,1]^k`. -/
def InUnitCube (x : Vec k) : Prop := ∀ i, x i ∈ Set.Icc (0 : ℝ) 1

/-- The `ℓ∞` distance `max_i |x i - y i|`, returning `0` on the empty index set. -/
noncomputable def linfDist (x y : Vec k) : ℝ :=
  if h : (Finset.univ : Finset (Fin k)).Nonempty then
    Finset.univ.sup' h (fun i => |x i - y i|)
  else 0

lemma linfDist_comm (x y : Vec k) : linfDist x y = linfDist y x := by
  unfold linfDist
  split_ifs with h
  · have : (fun i : Fin k => |x i - y i|) = fun i => |y i - x i| := by
      funext i; exact abs_sub_comm _ _
    rw [this]
  · rfl

lemma linfDist_nonneg (x y : Vec k) : 0 ≤ linfDist x y := by
  unfold linfDist
  split_ifs with h
  · obtain ⟨i, hi⟩ := h
    exact (abs_nonneg _).trans (Finset.le_sup' (f := fun j => |x j - y j|) hi)
  · rfl

/-- For any coordinate `i`, the difference at coordinate `i` is bounded by the
`ℓ∞` distance. -/
lemma abs_sub_le_linfDist {k : ℕ} [NeZero k] (x y : Vec k) (i : Fin k) :
    |x i - y i| ≤ linfDist x y := by
  have hne : (Finset.univ : Finset (Fin k)).Nonempty :=
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne k)⟩, Finset.mem_univ _⟩
  unfold linfDist
  rw [dif_pos hne]
  exact Finset.le_sup' (f := fun j => |x j - y j|) (Finset.mem_univ i)

/-- A uniform coordinate bound gives an `ℓ∞` bound. -/
lemma linfDist_le {k : ℕ} [NeZero k] {x y : Vec k} {r : ℝ}
    (h : ∀ i, |x i - y i| ≤ r) : linfDist x y ≤ r := by
  have hne : (Finset.univ : Finset (Fin k)).Nonempty :=
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne k)⟩, Finset.mem_univ _⟩
  unfold linfDist
  rw [dif_pos hne]
  exact Finset.sup'_le _ _ fun i _ => h i

/-- A function `f : Vec k → Vec k` is a `λ`-contraction in the `ℓ∞` norm on the
unit cube. We require:

* `f` maps the cube into itself;
* `0 ≤ λ < 1`;
* `linfDist (f x) (f y) ≤ λ * linfDist x y` for all `x y` in the cube.
-/
structure IsLInfContraction (f : Vec k → Vec k) (lam : ℝ) : Prop where
  preserves_cube : ∀ x, InUnitCube x → InUnitCube (f x)
  lam_nonneg : 0 ≤ lam
  lam_lt_one : lam < 1
  contracts : ∀ x y, InUnitCube x → InUnitCube y →
    linfDist (f x) (f y) ≤ lam * linfDist x y

/-- A point `x` is an `ε`-approximate fixed point of `f` if it lies in the cube
and `‖x - f x‖∞ ≤ ε`. -/
def IsApproxFixedPoint (f : Vec k → Vec k) (ε : ℝ) (x : Vec k) : Prop :=
  InUnitCube x ∧ linfDist x (f x) ≤ ε

/-- Specialisation of `QueryAlg` to oracles of type `Vec k → Vec k` (the CLY
setting: query at a point in `ℝ^k`, receive back a vector in `ℝ^k`). -/
abbrev CQueryAlg (k : ℕ) (α : Type) : Type := QueryAlg (Vec k) (Vec k) α

/-! ## Pyramids -/

/-- The CLY pyramid `𝒫_i(x, ϕ)`: points `y` for which the `ℓ∞` distance from
`y` to `x` is realised by coordinate `i` with sign `ϕ` (`true ↦ +`, `false ↦ −`).

`𝒫_i(x, true)  = { y | y i − x i = ‖y − x‖∞ }`
`𝒫_i(x, false) = { y | x i − y i = ‖y − x‖∞ }` -/
def Pyramid (i : Fin k) (ϕ : Bool) (x : Vec k) : Set (Vec k) :=
  { y | (if ϕ then y i - x i else x i - y i) = linfDist y x }

/-- The closed `ℓ∞`-ball of radius `r` around `x`. CLY use this with `r = 1` on
the integer grid as the "neighbourhood of the fixed point" (one discretisation
step). -/
def Around (r : ℝ) (x : Vec k) : Set (Vec k) := { y | linfDist y x ≤ r }

@[simp] lemma mem_pyramid_true_iff {k : ℕ} (i : Fin k) (x y : Vec k) :
    y ∈ Pyramid i true x ↔ y i - x i = linfDist y x := by
  simp [Pyramid]

@[simp] lemma mem_pyramid_false_iff {k : ℕ} (i : Fin k) (x y : Vec k) :
    y ∈ Pyramid i false x ↔ x i - y i = linfDist y x := by
  simp [Pyramid]

/-- The real ±1 corresponding to a `Bool` sign: `true ↦ +1`, `false ↦ -1`. -/
def signR (b : Bool) : ℝ := if b then 1 else -1

@[simp] lemma signR_true : signR true = 1 := rfl
@[simp] lemma signR_false : signR false = -1 := rfl

@[simp] lemma signR_sq (b : Bool) : signR b * signR b = 1 := by
  cases b <;> simp [signR]

/-- Uniform reformulation of pyramid membership using `signR`. -/
lemma mem_pyramid_iff_sign {k : ℕ} (i : Fin k) (ϕ : Bool) (x y : Vec k) :
    y ∈ Pyramid i ϕ x ↔ signR ϕ * (y i - x i) = linfDist y x := by
  cases ϕ
  · rw [mem_pyramid_false_iff, signR_false, neg_one_mul, neg_sub]
  · rw [mem_pyramid_true_iff, signR_true, one_mul]

/-! ## Balanced points -/

attribute [local instance] Classical.propDecidable

section Balanced

variable [NeZero k]

/-- `Fin k` is nonempty when `k ≠ 0`. -/
lemma univ_nonempty_fin : (Finset.univ : Finset (Fin k)).Nonempty :=
  ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne k)⟩, Finset.mem_univ _⟩

/-- Multiplying by a `±1` sign does not change the absolute value. -/
lemma abs_signR_mul (b : Bool) (x : ℝ) : |signR b * x| = |x| := by
  rw [abs_mul]; cases b <;> simp [signR]

/-- `signR b * x ≤ |x|`. -/
lemma signR_mul_le_abs (b : Bool) (x : ℝ) : signR b * x ≤ |x| :=
  (le_abs_self _).trans_eq (abs_signR_mul b x)

/-- Adding a constant commutes with a nonempty finite `sup'`. -/
lemma sup'_add_const {ι : Type*} (s : Finset ι) (H : s.Nonempty) (f : ι → ℝ) (a : ℝ) :
    s.sup' H (fun i => f i + a) = s.sup' H f + a := by
  refine le_antisymm (Finset.sup'_le _ _ fun i hi => ?_) ?_
  · linarith [Finset.le_sup' f hi]
  · have hstep : ∀ i ∈ s, f i ≤ s.sup' H (fun j => f j + a) - a := by
      intro i hi
      have := Finset.le_sup' (fun j => f j + a) hi
      linarith
    have := Finset.sup'_le H f hstep
    linarith

/-- The **signed support function** `maxᵢ σᵢ (yᵢ − cᵢ)`, where `σᵢ = ±1` is the
sign selected by `s`. With the arguments in the other order,
`sgnSup s y c = maxᵢ σᵢ (cᵢ − yᵢ)`. -/
noncomputable def sgnSup (s : Fin k → Bool) (c y : Vec k) : ℝ :=
  Finset.univ.sup' univ_nonempty_fin (fun i => signR (s i) * (y i - c i))

lemma le_sgnSup (s : Fin k → Bool) (c y : Vec k) (i : Fin k) :
    signR (s i) * (y i - c i) ≤ sgnSup s c y :=
  Finset.le_sup' (f := fun j => signR (s j) * (y j - c j)) (Finset.mem_univ i)

lemma sgnSup_le {s : Fin k → Bool} {c y : Vec k} {r : ℝ}
    (h : ∀ i, signR (s i) * (y i - c i) ≤ r) : sgnSup s c y ≤ r :=
  Finset.sup'_le _ _ fun i _ => h i

lemma exists_eq_sgnSup (s : Fin k → Bool) (c y : Vec k) :
    ∃ i : Fin k, signR (s i) * (y i - c i) = sgnSup s c y := by
  obtain ⟨i, _, hi⟩ :=
    Finset.exists_mem_eq_sup' (univ_nonempty_fin (k := k))
      (fun j => signR (s j) * (y j - c j))
  exact ⟨i, hi.symm⟩

/-- **Identity 1.** The `ℓ∞` distance splits along any sign vector:
`‖y − c‖∞ = max (maxᵢ σᵢ (yᵢ − cᵢ)) (maxᵢ σᵢ (cᵢ − yᵢ))`. -/
lemma linfDist_eq_max_sgnSup (s : Fin k → Bool) (c y : Vec k) :
    linfDist y c = max (sgnSup s c y) (sgnSup s y c) := by
  have hne := univ_nonempty_fin (k := k)
  have habs0 : ∀ i : Fin k, |y i - c i| = max (y i - c i) (c i - y i) := by
    intro i
    rcases le_total (c i) (y i) with h' | h'
    · rw [abs_of_nonneg (by linarith), max_eq_left (by linarith)]
    · rw [abs_of_nonpos (by linarith), max_eq_right (by linarith)]; ring
  have habs : ∀ i : Fin k,
      |y i - c i| = max (signR (s i) * (y i - c i)) (signR (s i) * (c i - y i)) := by
    intro i
    cases h : s i
    · simp only [signR_false, neg_one_mul, neg_sub]
      rw [max_comm]; exact habs0 i
    · simp only [signR_true, one_mul]; exact habs0 i
  refine le_antisymm ?_ ?_
  · unfold linfDist
    rw [dif_pos hne]
    refine Finset.sup'_le _ _ fun i _ => ?_
    rw [habs i]
    exact max_le_max (le_sgnSup s c y i) (le_sgnSup s y c i)
  · refine max_le (sgnSup_le fun i => ?_) (sgnSup_le fun i => ?_)
    · exact (signR_mul_le_abs _ _).trans (abs_sub_le_linfDist y c i)
    · have hcy := abs_sub_le_linfDist y c i
      rw [abs_sub_comm] at hcy
      exact (signR_mul_le_abs _ _).trans hcy

/-- **Identity 2.** A point is captured by the pyramid union `⋃ᵢ 𝒫ᵢ(c, sᵢ)`
exactly when the `+`-side signed support dominates the `−`-side one. -/
lemma mem_pyramidUnion_iff (s : Fin k → Bool) (c y : Vec k) :
    (∃ i : Fin k, y ∈ Pyramid i (s i) c) ↔ sgnSup s y c ≤ sgnSup s c y := by
  constructor
  · rintro ⟨i, hi⟩
    rw [mem_pyramid_iff_sign, linfDist_eq_max_sgnSup s c y] at hi
    have h1 : sgnSup s y c ≤ max (sgnSup s c y) (sgnSup s y c) := le_max_right _ _
    rw [← hi] at h1
    exact h1.trans (le_sgnSup s c y i)
  · intro hBA
    obtain ⟨i, hi⟩ := exists_eq_sgnSup s c y
    refine ⟨i, ?_⟩
    rw [mem_pyramid_iff_sign, linfDist_eq_max_sgnSup s c y, max_eq_left hBA]
    exact hi

/-- Translating the base point by `−h·σ`. -/
noncomputable def shiftBase (s : Fin k → Bool) (c : Vec k) (h : ℝ) : Vec k :=
  fun i => c i - h * signR (s i)

lemma sgnSup_shiftBase_left (s : Fin k → Bool) (c y : Vec k) (h : ℝ) :
    sgnSup s (shiftBase s c h) y = sgnSup s c y + h := by
  have key : ∀ i : Fin k,
      signR (s i) * (y i - shiftBase s c h i) = signR (s i) * (y i - c i) + h := by
    intro i
    have hsq := signR_sq (s i)
    have e : signR (s i) * (y i - shiftBase s c h i)
        = signR (s i) * (y i - c i) + h * (signR (s i) * signR (s i)) := by
      simp only [shiftBase]; ring
    rw [e, hsq, mul_one]
  unfold sgnSup
  rw [Finset.sup'_congr univ_nonempty_fin rfl (fun i _ => key i)]
  exact sup'_add_const _ _ _ _

lemma sgnSup_shiftBase_right (s : Fin k → Bool) (c y : Vec k) (h : ℝ) :
    sgnSup s y (shiftBase s c h) = sgnSup s y c - h := by
  have key : ∀ i : Fin k,
      signR (s i) * (shiftBase s c h i - y i) = signR (s i) * (c i - y i) + (-h) := by
    intro i
    have hsq := signR_sq (s i)
    have e : signR (s i) * (shiftBase s c h i - y i)
        = signR (s i) * (c i - y i) + (-(h * (signR (s i) * signR (s i)))) := by
      simp only [shiftBase]; ring
    rw [e, hsq, mul_one]
  unfold sgnSup
  rw [Finset.sup'_congr univ_nonempty_fin rfl (fun i _ => key i), sup'_add_const]
  ring

/-- **Identity 3.** The effect of the translation on a single distance term. -/
lemma linfDist_shiftBase (s : Fin k → Bool) (c y : Vec k) (h : ℝ) :
    linfDist y (shiftBase s c h) = max (sgnSup s c y + h) (sgnSup s y c - h) := by
  rw [linfDist_eq_max_sgnSup s (shiftBase s c h) y, sgnSup_shiftBase_left,
    sgnSup_shiftBase_right]

/-! ### The Fermat–Weber functional -/

/-- `Φ(c) = ∑_{y ∈ T} ‖y − c‖∞`, the `ℓ∞` Fermat–Weber functional of `T`. -/
noncomputable def fermatWeber (T : Finset (Vec k)) (c : Vec k) : ℝ :=
  ∑ y ∈ T, linfDist y c

/-- `linfDist` is the metric of the sup-metric product `Fin k → ℝ`. -/
lemma linfDist_eq_dist (x y : Vec k) : linfDist x y = dist x y := by
  refine le_antisymm ?_ ?_
  · unfold linfDist
    rw [dif_pos (univ_nonempty_fin (k := k))]
    refine Finset.sup'_le _ _ fun i _ => ?_
    rw [← Real.dist_eq]
    exact dist_le_pi_dist x y i
  · refine (dist_pi_le_iff (linfDist_nonneg x y)).mpr fun i => ?_
    rw [Real.dist_eq]
    unfold linfDist
    rw [dif_pos (univ_nonempty_fin (k := k))]
    exact Finset.le_sup' (f := fun j => |x j - y j|) (Finset.mem_univ i)

lemma continuous_linfDist_right (y : Vec k) :
    Continuous (fun c : Vec k => linfDist y c) := by
  have he : (fun c : Vec k => linfDist y c) = fun c : Vec k => dist y c := by
    funext c; exact linfDist_eq_dist y c
  rw [he]
  exact continuous_const.dist continuous_id

lemma continuous_fermatWeber (T : Finset (Vec k)) : Continuous (fermatWeber T) := by
  unfold fermatWeber
  exact continuous_finsetSum _ fun y _ => continuous_linfDist_right y

omit [NeZero k] in
/-- The box `[lo, hi]^k` is compact. -/
lemma isCompact_cubeBox (lo hi : ℝ) : IsCompact (CubeBox lo hi k) := by
  have hpi : CubeBox lo hi k = Set.univ.pi (fun _ : Fin k => Set.Icc lo hi) := by
    ext x
    simp only [CubeBox, Set.mem_setOf_eq, Set.mem_univ_pi, Set.mem_Icc]
  rw [hpi]
  exact isCompact_univ_pi fun _ => isCompact_Icc

/-- Clamping a point into `[lo, hi]^k` coordinatewise. -/
noncomputable def clampBox (lo hi : ℝ) (z : Vec k) : Vec k :=
  fun i => max lo (min hi (z i))

omit [NeZero k] in
lemma clampBox_mem (lo hi : ℝ) (hlohi : lo ≤ hi) (z : Vec k) :
    clampBox lo hi z ∈ CubeBox lo hi k :=
  fun _ => ⟨le_max_left _ _, max_le hlohi (min_le_left _ _)⟩

/-- Clamping moves a point no further from any point already inside the box. -/
lemma abs_sub_clamp_le {lo hi a t : ℝ} (h1 : lo ≤ a) (h2 : a ≤ hi) :
    |a - max lo (min hi t)| ≤ |a - t| := by
  rcases le_total t lo with hlo | hlo
  · rw [min_eq_right (hlo.trans (h1.trans h2)), max_eq_left hlo,
      abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith
  · rcases le_total hi t with hhi | hhi
    · rw [min_eq_left hhi, max_eq_right (h1.trans h2),
        abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
      linarith
    · rw [min_eq_right hhi, max_eq_right hlo]

lemma linfDist_clampBox_le {lo hi : ℝ} {y : Vec k} (hy : ∀ i, lo ≤ y i ∧ y i ≤ hi)
    (z : Vec k) : linfDist y (clampBox lo hi z) ≤ linfDist y z := by
  have hne := univ_nonempty_fin (k := k)
  unfold linfDist
  rw [dif_pos hne, dif_pos hne]
  refine Finset.sup'_le _ _ fun i _ => ?_
  refine le_trans ?_ (Finset.le_sup' (f := fun j => |y j - z j|) (Finset.mem_univ i))
  exact abs_sub_clamp_le (hy i).1 (hy i).2

/-- The Fermat–Weber functional attains a **global** minimum at a point of any
box containing `T`: minimising over the (compact) box suffices, because
clamping into the box never increases any term. -/
lemma exists_global_min_fermatWeber (lo hi : ℝ) (hlohi : lo ≤ hi) (T : Finset (Vec k))
    (hT : ∀ y ∈ T, ∀ i, lo ≤ y i ∧ y i ≤ hi) :
    ∃ c ∈ CubeBox lo hi k, ∀ z : Vec k, fermatWeber T c ≤ fermatWeber T z := by
  have hne : (CubeBox lo hi k).Nonempty :=
    ⟨fun _ => lo, fun _ => ⟨le_refl _, hlohi⟩⟩
  obtain ⟨c, hc_mem, hc_min⟩ :=
    (isCompact_cubeBox (k := k) lo hi).exists_isMinOn hne
      (continuous_fermatWeber T).continuousOn
  refine ⟨c, hc_mem, fun z => ?_⟩
  refine le_trans (isMinOn_iff.mp hc_min _ (clampBox_mem lo hi hlohi z)) ?_
  unfold fermatWeber
  exact Finset.sum_le_sum fun y hy => linfDist_clampBox_le (hT y hy) z

/-- **Balanced point, Brouwer-free.** For any finite `T` inside the box
`[lo, hi]^k` there is a point `c` of that box such that, for *every* sign
vector `s`, the pyramid union `⋃ᵢ 𝒫ᵢ(c, sᵢ)` captures at least half of `T`.

`c` is any minimiser of the `ℓ∞` Fermat–Weber functional of `T`; the proof is
the first-order optimality condition in the `2^k` directions `−σ`. -/
theorem exists_balanced_point_box (lo hi : ℝ) (hlohi : lo ≤ hi) (T : Finset (Vec k))
    (hT : ∀ y ∈ T, ∀ i, lo ≤ y i ∧ y i ≤ hi) :
    ∃ c ∈ CubeBox lo hi k, ∀ s : Fin k → Bool,
      T.card ≤ 2 * (T.filter (fun y => ∃ i, y ∈ Pyramid i (s i) c)).card := by
  obtain ⟨c, hc_mem, hc_min⟩ := exists_global_min_fermatWeber lo hi hlohi T hT
  refine ⟨c, hc_mem, fun s => ?_⟩
  set K := T.filter (fun y => ∃ i, y ∈ Pyramid i (s i) c) with hK_def
  have hKT : K ⊆ T := Finset.filter_subset _ _
  set Bad := T \ K with hBad_def
  have hsplit : Bad.card + K.card = T.card := Finset.card_sdiff_add_card_eq_card hKT
  have hK_mem : ∀ y ∈ K, sgnSup s y c ≤ sgnSup s c y := fun y hy =>
    (mem_pyramidUnion_iff s c y).mp (Finset.mem_filter.mp hy).2
  have hBad_mem : ∀ y ∈ Bad, sgnSup s c y < sgnSup s y c := by
    intro y hy
    rw [hBad_def, Finset.mem_sdiff] at hy
    have hnot : ¬ ∃ i, y ∈ Pyramid i (s i) c := by
      intro hex
      exact hy.2 (Finset.mem_filter.mpr ⟨hy.1, hex⟩)
    rw [mem_pyramidUnion_iff s c y] at hnot
    exact lt_of_not_ge hnot
  suffices hBK : Bad.card ≤ K.card by omega
  rcases Finset.eq_empty_or_nonempty Bad with hBad_empty | hBad_ne
  · simp [hBad_empty]
  set h : ℝ := (Bad.inf' hBad_ne (fun y => sgnSup s y c - sgnSup s c y)) / 2 with hh_def
  have hinf_pos : 0 < Bad.inf' hBad_ne (fun y => sgnSup s y c - sgnSup s c y) := by
    rw [Finset.lt_inf'_iff]
    intro y hy
    linarith [hBad_mem y hy]
  have hh_pos : 0 < h := by rw [hh_def]; linarith
  have hh_le : ∀ y ∈ Bad, 2 * h ≤ sgnSup s y c - sgnSup s c y := by
    intro y hy
    have hle := Finset.inf'_le (f := fun z => sgnSup s z c - sgnSup s c z) hy
    rw [hh_def]
    linarith
  have hterm_K : ∀ y ∈ K, linfDist y (shiftBase s c h) = linfDist y c + h := by
    intro y hy
    have hba := hK_mem y hy
    rw [linfDist_shiftBase, linfDist_eq_max_sgnSup s c y, max_eq_left hba,
      max_eq_left (by linarith : sgnSup s y c - h ≤ sgnSup s c y + h)]
  have hterm_Bad : ∀ y ∈ Bad, linfDist y (shiftBase s c h) = linfDist y c - h := by
    intro y hy
    have hlt := hBad_mem y hy
    have hgap := hh_le y hy
    rw [linfDist_shiftBase, linfDist_eq_max_sgnSup s c y, max_eq_right hlt.le,
      max_eq_right (by linarith : sgnSup s c y + h ≤ sgnSup s y c - h)]
  have hsum : fermatWeber T (shiftBase s c h)
      = fermatWeber T c + h * K.card - h * Bad.card := by
    unfold fermatWeber
    rw [← Finset.sum_sdiff (f := fun y => linfDist y (shiftBase s c h)) hKT,
      ← Finset.sum_sdiff (f := fun y => linfDist y c) hKT,
      ← hBad_def,
      Finset.sum_congr rfl hterm_K, Finset.sum_congr rfl hterm_Bad,
      Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul]
    ring
  have hmin := hc_min (shiftBase s c h)
  rw [hsum] at hmin
  have hmul : h * (Bad.card : ℝ) ≤ h * (K.card : ℝ) := by linarith
  exact_mod_cast le_of_mul_le_mul_left hmul hh_pos

end Balanced

/-! ## Algorithm assembly

The CLY algorithm is a `QueryAlg` defined by well-founded recursion on the
candidate set's cardinality. At each step it picks a balanced point of `T`
via `Classical.choose exists_balanced_point_real`, queries the oracle at the
rescaled point `c / n`, and either returns (if the response is close
enough) or shrinks `T` using `halving_from_balanced` (with the shifted base
`b = c + 2·σ(s)`). The cardinality strictly decreases — termination.

The full construction also involves the continuous→discrete *rescaling
bridge*: a query to the continuous `f : [0,1]^k → [0,1]^k` at point `q/n`
corresponds to a query to the rescaled `g : [0,n]^k → [0,n]^k`, `g x = n · f (x/n)`,
at `q`. CLY's "Observation 1" black-box reduction also eliminates the
`γ`-dependence by mapping `(ε, γ) → (ε/2, ε/2)`. -/

attribute [local instance] Classical.propDecidable

/-! ## The grid -/

/-- The integer points of `[0, n]^k`, as real vectors. This is the algorithm's
initial candidate set. Unlike CLY we do not restrict to *even* integers: their
parity condition exists only to support the rounding step of their Lemma 8, and
`exists_balanced_point_box` needs no such condition. -/
noncomputable def grid (n k : ℕ) : Finset (Vec k) :=
  Fintype.piFinset fun _ : Fin k => (Finset.range (n + 1)).image (fun m : ℕ => (m : ℝ))

lemma mem_grid {n k : ℕ} {x : Vec k} :
    x ∈ grid n k ↔ ∀ i, ∃ m : ℕ, m ≤ n ∧ x i = (m : ℝ) := by
  simp only [grid, Fintype.mem_piFinset, Finset.mem_image, Finset.mem_range]
  exact forall_congr' fun i => ⟨fun ⟨m, hm, he⟩ => ⟨m, by omega, he.symm⟩,
    fun ⟨m, hm, he⟩ => ⟨m, by omega, he.symm⟩⟩

lemma grid_mem_cube {n k : ℕ} {x : Vec k} (hx : x ∈ grid n k) (i : Fin k) :
    0 ≤ x i ∧ x i ≤ (n : ℝ) := by
  obtain ⟨m, hm, he⟩ := mem_grid.mp hx i
  rw [he]
  exact ⟨Nat.cast_nonneg m, by exact_mod_cast hm⟩

@[simp] lemma grid_card (n k : ℕ) : (grid n k).card = (n + 1) ^ k := by
  rw [grid, Fintype.card_piFinset]
  simp [Finset.card_image_of_injective _ Nat.cast_injective]

/-- Every point of `[0, n]^k` has a grid point within `ℓ∞`-distance `1`
(indeed `1/2`): round each coordinate. -/
lemma exists_grid_near {n k : ℕ} [NeZero k] {x : Vec k}
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ (n : ℝ)) :
    ∃ y ∈ grid n k, linfDist y x ≤ 1 := by
  refine ⟨fun i => (⌊x i + 1 / 2⌋₊ : ℝ), mem_grid.mpr fun i => ⟨⌊x i + 1 / 2⌋₊, ?_, rfl⟩, ?_⟩
  · have hle : ((⌊x i + 1 / 2⌋₊ : ℕ) : ℝ) ≤ x i + 1 / 2 :=
      Nat.floor_le (by linarith [(hx i).1])
    by_contra hcon
    have : ((n : ℕ) : ℝ) + 1 ≤ ((⌊x i + 1 / 2⌋₊ : ℕ) : ℝ) := by
      exact_mod_cast (by omega : n + 1 ≤ ⌊x i + 1 / 2⌋₊)
    linarith [(hx i).2]
  · refine linfDist_le fun i => ?_
    have h1 : ((⌊x i + 1 / 2⌋₊ : ℕ) : ℝ) ≤ x i + 1 / 2 :=
      Nat.floor_le (by linarith [(hx i).1])
    have h2 : x i + 1 / 2 < ((⌊x i + 1 / 2⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
    rw [abs_le]
    constructor <;> linarith

/-! ## Choosing a balanced point -/

/-- A balanced point of `T`, defaulting to `0` when none is known to exist. -/
noncomputable def clyChooseBalanced (n : ℕ) (T : Finset (Vec k)) : Vec k :=
  if h : ∃ c : Vec k, (∀ i, 0 ≤ c i ∧ c i ≤ (n : ℝ)) ∧ ∀ s : Fin k → Bool,
      T.card ≤ 2 * (T.filter fun y => ∃ i, y ∈ Pyramid i (s i) c).card
    then h.choose else 0

lemma clyChooseBalanced_mem_cube (n : ℕ) (T : Finset (Vec k)) (i : Fin k) :
    0 ≤ clyChooseBalanced n T i ∧ clyChooseBalanced n T i ≤ (n : ℝ) := by
  unfold clyChooseBalanced
  split_ifs with h
  · exact h.choose_spec.1 i
  · exact ⟨le_refl _, Nat.cast_nonneg n⟩

lemma clyChooseBalanced_spec [NeZero k] (n : ℕ) (T : Finset (Vec k))
    (hT : T ⊆ grid n k) (s : Fin k → Bool) :
    T.card ≤ 2 * (T.filter fun y => ∃ i, y ∈ Pyramid i (s i) (clyChooseBalanced n T)).card := by
  have hex : ∃ c : Vec k, (∀ i, 0 ≤ c i ∧ c i ≤ (n : ℝ)) ∧ ∀ s : Fin k → Bool,
      T.card ≤ 2 * (T.filter fun y => ∃ i, y ∈ Pyramid i (s i) c).card := by
    obtain ⟨c, hc, hbal⟩ :=
      exists_balanced_point_box (k := k) 0 n (Nat.cast_nonneg n) T
        (fun y hy i => grid_mem_cube (hT hy) i)
    exact ⟨c, hc, hbal⟩
  unfold clyChooseBalanced
  rw [dif_pos hex]
  exact hex.choose_spec.2 s

end Tfnp.Contraction
