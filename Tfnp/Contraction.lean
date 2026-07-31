/-
Copyright (c) 2026 Angus Joshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Angus Joshi
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Tactic.Positivity
import Tfnp.QueryModel
import Tfnp.Shrinking
import Tfnp.Box

/-!
# Query complexity of `ℓ∞`-contraction map fixpoint computation

This file begins a formalization of the main result of

> Xi Chen, Yuhao Li and Mihalis Yannakakis.
> *Computing a Fixed Point of Contraction Maps in Polynomial Queries.*
> STOC 2024 / Journal of the ACM 2025.

The paper exhibits a deterministic query-efficient algorithm for finding an
`ε`-approximate fixed point of an `ℓ∞`-contraction `f : [0,1]^k → [0,1]^k`,
making `O(k² log(1/ε))` queries to `f`. The query bound is independent of the
contraction constant `λ`.

The follow-up paper of Haslebacher, Lill, Schnider, Weber
([arXiv:2503.16089](https://arxiv.org/abs/2503.16089)) generalises this to
`ℓ_p`-norms with `O(k² (log(1/ε) + log(1/(1 - λ))))` queries.

## A rough glossary

- `Vec k`, `InUnitCube`: vectors in `ℝ^k` and the unit cube `[0,1]^k`.
- `linfDist`: the `ℓ∞` distance `max_i |x i - y i|`.
- `IsLInfContraction`: a `λ`-contraction in the `ℓ∞` norm, from the unit cube to itself.
- `IsApproxFixedPoint`: an `ε`-approximate fixed point.
- `QueryAlg`: the oracle/query model — a (possibly infinitely branching) decision
  tree that asks the oracle for `f x` and continues with the response.
- `Pyramid i ϕ x`: the CLY "pyramid" — points `y` where coordinate `i` (with
  sign `ϕ`) realises the `ℓ∞` distance `‖y − x‖∞`.
- `fermatWeber T`: `Φ(c) = ∑_{y ∈ T} ‖y − c‖∞`, the `ℓ∞` Fermat–Weber
  functional. Its minimisers are exactly the balanced points of `T`, which is
  how `exists_balanced_point_box` avoids Brouwer entirely.
- `Around r x`: the closed `ℓ∞`-ball of radius `r` around `x`.
- `pyramid_cover`: every point lies in some pyramid based at every other point.
- `cly_query_complexity` (in `Tfnp/Algorithm.lean`): CLY's main theorem.

## References

* [arXiv:2403.19911](https://arxiv.org/abs/2403.19911) : CLY, contains all content formalized here.
* [arXiv:2503.16089](https://arxiv.org/abs/2503.16089) (follow-up to all `ℓ_p`)
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

@[simp] lemma linfDist_self (x : Vec k) : linfDist x x = 0 := by
  unfold linfDist
  split_ifs with h
  · have : (fun i : Fin k => |x i - x i|) = fun _ => 0 := by funext i; simp
    rw [this, Finset.sup'_const]
  · rfl

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

@[simp] lemma linfDist_eq_zero {x y : Vec k} : linfDist x y = 0 ↔ x = y := by
  unfold linfDist
  split_ifs with h
  · refine ⟨fun hsup => funext fun i => ?_, fun hxy => ?_⟩
    · have hle : |x i - y i| ≤ Finset.univ.sup' h (fun j => |x j - y j|) :=
        Finset.le_sup' (f := fun j => |x j - y j|) (Finset.mem_univ i)
      rw [hsup] at hle
      have habs : |x i - y i| = 0 := le_antisymm hle (abs_nonneg _)
      have : x i - y i = 0 := abs_eq_zero.mp habs
      linarith
    · subst hxy
      have : (fun i : Fin k => |x i - x i|) = fun _ => 0 := by funext; simp
      rw [this, Finset.sup'_const]
  · refine ⟨fun _ => funext fun i => ?_, fun _ => rfl⟩
    exact absurd (⟨i, Finset.mem_univ i⟩ : (Finset.univ : Finset (Fin k)).Nonempty) h

/-- For any coordinate `i`, the difference at coordinate `i` is bounded by the
`ℓ∞` distance. -/
lemma abs_sub_le_linfDist {k : ℕ} [NeZero k] (x y : Vec k) (i : Fin k) :
    |x i - y i| ≤ linfDist x y := by
  have hne : (Finset.univ : Finset (Fin k)).Nonempty :=
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne k)⟩, Finset.mem_univ _⟩
  unfold linfDist
  rw [dif_pos hne]
  exact Finset.le_sup' (f := fun j => |x j - y j|) (Finset.mem_univ i)

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

/-! ## Query model (factored out)

The algorithm's oracle-access model is captured by the generic `QueryAlg`
from `Tfnp.QueryModel`. For CLY, both queries and responses are vectors
in `Vec k`. We use the type alias `CQueryAlg k := QueryAlg (Vec k) (Vec k)`
for brevity. -/

/-- Specialisation of `QueryAlg` to oracles of type `Vec k → Vec k` (the CLY
setting: query at a point in `ℝ^k`, receive back a vector in `ℝ^k`). -/
abbrev CQueryAlg (k : ℕ) (α : Type) : Type := QueryAlg (Vec k) (Vec k) α

/-! ## Pyramids (CLY's geometric primitive)

CLY work directly in `ℓ∞` without halfspace language. Their algorithm operates
on the integer-scaled grid `EVEN(n,k)` and maintains a *candidate set* `Cand^t`
of grid points still believed to contain the (rescaled) fixed point. The
geometric primitive is the **pyramid**

`𝒫_i(x, ϕ) := { y : ϕ · (y_i − x_i) = ‖y − x‖∞ }`,

the set of points `y` for which coordinate `i`, with sign `ϕ ∈ {+1, −1}`,
realises the `ℓ∞` distance to `x`. (For `ℓ_2` the analogous "directional cone"
would be a halfspace; in `ℓ∞` the analogue is a pyramid because the distance
function is itself a max over coordinates.)

The algorithm picks a *balanced point* `a` of `Cand^(t−1)` — analogue of a
centerpoint — queries `g(a)`, and from the response it identifies a sign
vector `s` such that the true fixed point lies in `⋃_{i : s_i ≠ 0} 𝒫_i(b, s_i)`
where `b = a + 2s`. The defining property of balancedness then guarantees the
candidate set at least halves at every step, yielding the bound. See
[arXiv:2403.19911](https://arxiv.org/abs/2403.19911), Algorithm 1 and Lemma 5. -/

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

/-- A point in `Pyramid i true x` is `≥ x i` at coordinate `i`. -/
lemma coord_ge_of_mem_pyramid_true {k : ℕ} {i : Fin k} {x y : Vec k}
    (h : y ∈ Pyramid i true x) : x i ≤ y i := by
  rw [mem_pyramid_true_iff] at h
  linarith [linfDist_nonneg y x]

/-- A point in `Pyramid i false x` is `≤ x i` at coordinate `i`. -/
lemma coord_le_of_mem_pyramid_false {k : ℕ} {i : Fin k} {x y : Vec k}
    (h : y ∈ Pyramid i false x) : y i ≤ x i := by
  rw [mem_pyramid_false_iff] at h
  linarith [linfDist_nonneg y x]

/-- **Shifted-pyramid disjointness (CLY).** The `−` pyramid at `a` and the `+`
pyramid at `b` are disjoint whenever `b` is strictly past `a` along coordinate
`i`. Combined with the balanced-point lemma at `a`, this is the bridge that
turns "captures `≥` half" at `a` into "captures `≤` half" at `b = a + 2s`. -/
lemma pyramid_disjoint_of_lt {k : ℕ} (a b : Vec k) (i : Fin k) (h : a i < b i) :
    Disjoint (Pyramid i false a) (Pyramid i true b) := by
  rw [Set.disjoint_iff_inter_eq_empty]
  ext y
  refine ⟨fun ⟨hya, hyb⟩ => ?_, fun h => h.elim⟩
  exact absurd (le_trans (coord_ge_of_mem_pyramid_true hyb)
                          (coord_le_of_mem_pyramid_false hya)) (not_le.mpr h)

/-- The real ±1 corresponding to a `Bool` sign: `true ↦ +1`, `false ↦ -1`. -/
def signR (b : Bool) : ℝ := if b then 1 else -1

@[simp] lemma signR_true : signR true = 1 := rfl
@[simp] lemma signR_false : signR false = -1 := rfl

@[simp] lemma signR_sq (b : Bool) : signR b * signR b = 1 := by
  cases b <;> simp [signR]

@[simp] lemma signR_not (b : Bool) : signR (!b) = -signR b := by
  cases b <;> simp [signR]

/-- Uniform reformulation of pyramid membership using `signR`. -/
lemma mem_pyramid_iff_sign {k : ℕ} (i : Fin k) (ϕ : Bool) (x y : Vec k) :
    y ∈ Pyramid i ϕ x ↔ signR ϕ * (y i - x i) = linfDist y x := by
  cases ϕ
  · rw [mem_pyramid_false_iff, signR_false, neg_one_mul, neg_sub]
  · rw [mem_pyramid_true_iff, signR_true, one_mul]

/-- **Pyramid-union disjointness with shifted base (CLY geometric core).**
The union of "flipped-sign" pyramids at `q` and the union of "original-sign"
pyramids at the shifted base `b = q + 2σ(s)` are disjoint, where `σ(s) i = ±1`
is the real sign corresponding to `s i : Bool`.

Proof outline: a point `y` in both unions has indices `i₀, i₁` realising the
respective pyramid conditions. Algebra (using `σᵢ² = 1`) gives
`‖y − q‖∞ ≥ ‖y − b‖∞ + 2` and `‖y − b‖∞ ≥ ‖y − q‖∞ + 2`. Combined: `0 ≥ 4`. -/
lemma pyramid_union_disjoint_shifted {k : ℕ} (q : Vec k) (s : Fin k → Bool) :
    Disjoint (⋃ i, Pyramid i (!s i) q)
      (⋃ i, Pyramid i (s i) (q + fun i => 2 * signR (s i))) := by
  set b : Vec k := q + fun i => 2 * signR (s i) with hb_def
  rw [Set.disjoint_iff_inter_eq_empty]
  ext y
  refine ⟨?_, fun h => h.elim⟩
  rintro ⟨hq_pyr, hb_pyr⟩
  rw [Set.mem_iUnion] at hq_pyr hb_pyr
  obtain ⟨i₀, hi₀⟩ := hq_pyr
  obtain ⟨i₁, hi₁⟩ := hb_pyr
  haveI : NeZero k := ⟨by intro hk; subst hk; exact i₀.elim0⟩
  rw [mem_pyramid_iff_sign, signR_not] at hi₀
  rw [mem_pyramid_iff_sign] at hi₁
  have hbi₀ : b i₀ = q i₀ + 2 * signR (s i₀) := by simp [b]
  have hbi₁ : b i₁ = q i₁ + 2 * signR (s i₁) := by simp [b]
  have hi₀' : signR (s i₀) * (y i₀ - q i₀) = -linfDist y q := by linarith
  -- Algebra step 1: σᵢ₁ · (yᵢ₁ − qᵢ₁) = linfDist y b + 2.
  have key1 : signR (s i₁) * (y i₁ - q i₁) = linfDist y b + 2 := by
    have hsq := signR_sq (s i₁)
    have e : signR (s i₁) * (y i₁ - q i₁)
           = signR (s i₁) * (y i₁ - b i₁) + signR (s i₁) * (b i₁ - q i₁) := by ring
    rw [e, hi₁, hbi₁]; nlinarith
  -- Algebra step 2: σᵢ₀ · (yᵢ₀ − bᵢ₀) = −linfDist y q − 2.
  have key2 : signR (s i₀) * (y i₀ - b i₀) = -linfDist y q - 2 := by
    have hsq := signR_sq (s i₀)
    have e : signR (s i₀) * (y i₀ - b i₀)
           = signR (s i₀) * (y i₀ - q i₀) - signR (s i₀) * (b i₀ - q i₀) := by ring
    rw [e, hi₀', hbi₀]; nlinarith
  -- |σᵢ * x| = |x| when σᵢ ∈ {±1}.
  have abs_signR_mul : ∀ (b : Bool) (x : ℝ), |signR b * x| = |x| := fun b x => by
    rw [abs_mul]; cases b <;> simp [signR]
  -- linfDist y q ≥ |yᵢ₁ − qᵢ₁| ≥ σᵢ₁ · (yᵢ₁ − qᵢ₁) = linfDist y b + 2.
  have lb1 : linfDist y q ≥ linfDist y b + 2 := by
    have ha : |y i₁ - q i₁| ≤ linfDist y q := abs_sub_le_linfDist y q i₁
    have hb_le : signR (s i₁) * (y i₁ - q i₁) ≤ |y i₁ - q i₁| := by
      calc signR (s i₁) * (y i₁ - q i₁)
          ≤ |signR (s i₁) * (y i₁ - q i₁)| := le_abs_self _
        _ = |y i₁ - q i₁| := abs_signR_mul _ _
    linarith
  -- linfDist y b ≥ |yᵢ₀ − bᵢ₀| ≥ −(σᵢ₀ · (yᵢ₀ − bᵢ₀)) = linfDist y q + 2.
  have lb2 : linfDist y b ≥ linfDist y q + 2 := by
    have ha : |y i₀ - b i₀| ≤ linfDist y b := abs_sub_le_linfDist y b i₀
    have hb_le : -(signR (s i₀) * (y i₀ - b i₀)) ≤ |y i₀ - b i₀| := by
      calc -(signR (s i₀) * (y i₀ - b i₀))
          ≤ |signR (s i₀) * (y i₀ - b i₀)| := neg_le_abs _
        _ = |y i₀ - b i₀| := abs_signR_mul _ _
    linarith
  linarith

@[simp] lemma mem_Around_self {r : ℝ} (hr : 0 ≤ r) (x : Vec k) :
    x ∈ Around r x := by
  simp [Around, linfDist_self, hr]

/-- **Pyramid cover.** Every point `y` lies in some pyramid `𝒫_i(x, ϕ)` — the
coordinate `i` where the `ℓ∞` distance `‖y − x‖∞` is attained, with the
appropriate sign. This is immediate from `Finset.sup'` reaching its maximum on
the index set. -/
theorem pyramid_cover {k : ℕ} [NeZero k] (x y : Vec k) :
    ∃ (i : Fin k) (ϕ : Bool), y ∈ Pyramid i ϕ x := by
  have hne : (Finset.univ : Finset (Fin k)).Nonempty :=
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne k)⟩, Finset.mem_univ _⟩
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' hne (fun j => |y j - x j|)
  have hlin : linfDist y x = |y i - x i| := by
    unfold linfDist; rw [dif_pos hne]; exact hi
  by_cases hsign : 0 ≤ y i - x i
  · refine ⟨i, true, ?_⟩
    change (if (true : Bool) then y i - x i else x i - y i) = linfDist y x
    rw [show (if (true : Bool) then y i - x i else x i - y i) = y i - x i from rfl,
        hlin, abs_of_nonneg hsign]
  · rw [not_le] at hsign
    refine ⟨i, false, ?_⟩
    change (if (false : Bool) then y i - x i else x i - y i) = linfDist y x
    rw [show (if (false : Bool) then y i - x i else x i - y i) = x i - y i from rfl,
        hlin, abs_of_neg hsign, neg_sub]

/-- **Pyramid lemma (CLY, continuous form).** Suppose `f` is an `ℓ∞`-contraction
with a fixed point `x*` in the cube, and the queried point `a` is *not* itself a
fixed point (so the response `f a` differs from `a`). Then there is a coordinate
`i` with `f(a)_i ≠ a_i` such that

`x* ∈ Pyramid i (sgn ((f a)_i − a_i)) a`,

i.e. the displacement `f a − a` correctly points toward the side of `a` that
contains `x*`, with the magnitude realised at coordinate `i`.

CLY use a *shifted* base `b = a + 2 s` on the integer grid `EVEN(n,k)`; the
continuous-limit base is `a` itself (the shift `2/n → 0`). This is the
continuous shadow of CLY Lemma 2. -/
theorem fixed_point_in_pyramids
    (f : Vec k → Vec k) {lam : ℝ} (hf : IsLInfContraction f lam)
    (a x_star : Vec k) (ha_cube : InUnitCube a)
    (hx_star_cube : InUnitCube x_star) (hx_star_fix : f x_star = x_star)
    (hne : f a ≠ a) :
    ∃ i : Fin k, (f a) i ≠ a i ∧
      x_star ∈ Pyramid i (decide (0 < (f a) i - a i)) a := by
  -- A fixed point of `a` would force `a = x*`, but `f a ≠ a` rules that out.
  have hax : a ≠ x_star := fun h => hne (by rw [h, hx_star_fix])
  -- `k > 0`, else `Vec k` is a subsingleton and `f a = a`.
  have hk_pos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · exact absurd (funext fun i => by simp [hk] at i; exact i.elim0) hne
    · exact hk
  have hne_univ : (Finset.univ : Finset (Fin k)).Nonempty :=
    ⟨⟨0, hk_pos⟩, Finset.mem_univ _⟩
  -- `linfDist a x* > 0`.
  have hd_pos : 0 < linfDist a x_star :=
    (linfDist_nonneg a x_star).lt_of_ne fun h => hax (linfDist_eq_zero.mp h.symm)
  -- Pick `j` realising the max in `linfDist a x*`.
  obtain ⟨j, _, hj⟩ :=
    Finset.exists_mem_eq_sup' hne_univ (fun i => |a i - x_star i|)
  have hj_eq : |a j - x_star j| = linfDist a x_star := by
    unfold linfDist; rw [dif_pos hne_univ]; exact hj.symm
  -- Strict contraction: `linfDist (f a) x* < linfDist a x*`.
  have hcontract : linfDist (f a) x_star ≤ lam * linfDist a x_star := by
    have := hf.contracts a x_star ha_cube hx_star_cube
    rwa [hx_star_fix] at this
  have hstrict : linfDist (f a) x_star < linfDist a x_star := by
    calc linfDist (f a) x_star
        ≤ lam * linfDist a x_star := hcontract
      _ < 1 * linfDist a x_star :=
          mul_lt_mul_of_pos_right hf.lam_lt_one hd_pos
      _ = linfDist a x_star := one_mul _
  -- At coord `j`: `|f(a)_j − x*_j| < |a_j − x*_j|`.
  haveI : NeZero k := ⟨hk_pos.ne'⟩
  have hkey : |f a j - x_star j| < |a j - x_star j| :=
    (abs_sub_le_linfDist (f a) x_star j).trans_lt (hj_eq ▸ hstrict)
  -- Therefore `f(a)_j ≠ a_j` and `f(a)_j`, `x*_j` lie on the same side of `a_j`.
  refine ⟨j, ?_, ?_⟩
  · intro hfaj
    rw [hfaj] at hkey
    exact lt_irrefl _ hkey
  · -- We show `x_star ∈ Pyramid j (decide (0 < f(a)_j − a_j)) a`.
    -- Split on the sign of `x*_j − a_j` (which is nonzero since `linfDist a x* > 0`
    -- and `j` realises the max).
    have hax_j : a j ≠ x_star j := by
      intro h
      have : |a j - x_star j| = 0 := by rw [h]; simp
      rw [hj_eq] at this
      exact hd_pos.ne' this
    rcases lt_or_gt_of_ne hax_j with hlt | hgt
    · -- a_j < x*_j, so x*_j - a_j > 0 and `|a_j - x*_j| = x*_j - a_j = linfDist`.
      -- Need f(a)_j > a_j (so decide(0 < f a j - a j) = true).
      have hxstar_gt : a j < x_star j := hlt
      have habs_a : |a j - x_star j| = x_star j - a j := by
        rw [abs_sub_comm, abs_of_pos (by linarith)]
      have hfa_gt : a j < f a j := by
        by_contra hcontra
        rw [not_lt] at hcontra
        -- f(a)_j ≤ a_j < x*_j, so |f(a)_j - x*_j| = x*_j - f(a)_j ≥ x*_j - a_j
        have : x_star j - f a j ≥ x_star j - a j := by linarith
        have habs_fa : |f a j - x_star j| = x_star j - f a j := by
          rw [abs_sub_comm, abs_of_pos (by linarith)]
        linarith [habs_a, habs_fa, hkey]
      change (if decide (0 < f a j - a j) then x_star j - a j else a j - x_star j)
        = linfDist x_star a
      rw [decide_eq_true (by linarith : (0 : ℝ) < f a j - a j),
          if_pos rfl, linfDist_comm, ← hj_eq, habs_a]
    · -- a_j > x*_j: symmetric.
      have habs_a : |a j - x_star j| = a j - x_star j := abs_of_pos (by linarith)
      have hfa_lt : f a j < a j := by
        by_contra hcontra
        rw [not_lt] at hcontra
        have habs_fa : |f a j - x_star j| = f a j - x_star j :=
          abs_of_nonneg (by linarith)
        linarith [habs_a, habs_fa, hkey]
      change (if decide (0 < f a j - a j) then x_star j - a j else a j - x_star j)
        = linfDist x_star a
      rw [decide_eq_false (by linarith : ¬ (0 : ℝ) < f a j - a j),
          if_neg Bool.false_ne_true, linfDist_comm, ← hj_eq, habs_a]

/-! ## Integer grid `EVEN(n, k)`

The CLY algorithm operates on the integer grid `EVEN(n, k)`, the set of points
in `{0, 2, 4, …}^k ⊆ ℤ^k` with each coordinate in `[0, n]`. We embed this into
`Vec k` via `Int.cast` so the pyramid/distance API on `Vec k` applies. -/

/-- An integer vector in `ℤ^k`. -/
abbrev IntVec (k : ℕ) : Type := Fin k → ℤ

/-- Embed an integer vector into `Vec k = Fin k → ℝ` via `Int.cast`. -/
def IntVec.toVec {k : ℕ} (y : IntVec k) : Vec k := fun i => (y i : ℝ)

@[simp] lemma IntVec.toVec_apply {k : ℕ} (y : IntVec k) (i : Fin k) :
    y.toVec i = (y i : ℝ) := rfl

/-- The lattice cube: integer points in `[0, n]^k`. -/
noncomputable def IntCube (n k : ℕ) : Finset (IntVec k) :=
  Fintype.piFinset (fun _ : Fin k => Finset.Icc (0 : ℤ) n)

@[simp] lemma mem_IntCube {n k : ℕ} (y : IntVec k) :
    y ∈ IntCube n k ↔ ∀ i, 0 ≤ y i ∧ y i ≤ n := by
  unfold IntCube
  simp [Fintype.mem_piFinset, Finset.mem_Icc]

/-- The CLY candidate set: even-integer points in the lattice cube. -/
noncomputable def EVEN (n k : ℕ) : Finset (IntVec k) :=
  (IntCube n k).filter (fun y => ∀ i, Even (y i))

@[simp] lemma mem_EVEN {n k : ℕ} (y : IntVec k) :
    y ∈ EVEN n k ↔ (∀ i, 0 ≤ y i ∧ y i ≤ n) ∧ ∀ i, Even (y i) := by
  unfold EVEN
  simp [Finset.mem_filter]

/-! ### Balanced points via convex minimisation

CLY obtain their balanced point from Brouwer's fixed-point theorem applied to
an auxiliary self-map built out of signed pyramid volumes (their Lemma 6),
followed by a limit argument (Lemma 7) and a parity-aware rounding step
(Lemma 8).

None of that is necessary. The balanced point is exactly a minimiser of the
**`ℓ∞` Fermat–Weber functional**

`Φ(c) = ∑_{y ∈ T} ‖y − c‖∞`,

a convex, piecewise-linear function of `c`. Existence is compactness, not
Brouwer, and the balance property is the first-order optimality condition. The
underlying reason this works in `ℓ∞` specifically is that the subgradients of
`‖·‖∞` are the vertices `±eᵢ` of the dual (cross-polytope) ball, so the
"direction from `c` to `y`" is quantised into exactly the `2k` pyramid classes.

The proof below avoids subdifferential calculus entirely. Writing
`σᵢ = signR (s i) ∈ {±1}` and

* `A(y) = maxᵢ σᵢ (yᵢ − cᵢ)`  (`sgnSup s c y`),
* `B(y) = maxᵢ σᵢ (cᵢ − yᵢ)`  (`sgnSup s y c`),

there are three identities:

* `‖y − c‖∞ = max (A y) (B y)`                     (`linfDist_eq_max_sgnSup`)
* `y ∈ ⋃ᵢ 𝒫ᵢ(c, sᵢ) ↔ B y ≤ A y`                   (`mem_pyramidUnion_iff`)
* `‖y − (c − h·σ)‖∞ = max (A y + h) (B y − h)`     (`linfDist_shiftBase`)

so translating `c` by `−h·σ` moves each term of `Φ` by exactly `+h` (if `y` is
captured by the pyramid union) or `−h` (if not, and `h` is below the finite gap
`min (B y − A y) / 2`). Minimality of `Φ` at `c` then says immediately that at
least half of `T` is captured — for every one of the `2^k` sign vectors at
once. -/

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

/-! #### The Fermat–Weber functional -/

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
  -- Split `T` into the captured part `K` and the rest `Bad = T \ K`.
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
  -- It suffices to show `|Bad| ≤ |K|`.
  suffices hBK : Bad.card ≤ K.card by omega
  rcases Finset.eq_empty_or_nonempty Bad with hBad_empty | hBad_ne
  · simp [hBad_empty]
  -- Translation strength: half the smallest gap over `Bad`.
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
  -- Each term of `Φ` moves by exactly `+h` (captured) or `−h` (not captured).
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
  -- Add up: `Φ(c − hσ) = Φ(c) + h·|K| − h·|Bad|`, and `Φ(c)` is minimal.
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


/-- **CLY Lemma 8 (rounding).** Given any real point `p* ∈ [−1/4, n+1/4]^k`,
there is an integer point `q* ∈ IntCube n k` with `|p*ᵢ − q*ᵢ| ≤ 1/2` for every
coordinate. (Ties — when `p*ᵢ` is a half-integer — are broken to make `q*ᵢ`
odd, but this is not needed for the bound below.) -/
theorem cly_rounding {k : ℕ} (n : ℕ) (p : Vec k)
    (hp : p ∈ CubeBox (-1 / 4) (n + 1 / 4) k) :
    ∃ q : IntVec k, q ∈ IntCube n k ∧ ∀ i, |p i - (q i : ℝ)| ≤ 1/2 := by
  -- Set `q i := ⌊p i + 1/2⌋` (round-to-nearest).
  refine ⟨fun i => ⌊p i + 1/2⌋, ?_, ?_⟩
  · -- `q i ∈ [0, n]` from `-1/4 ≤ p i ≤ n + 1/4`.
    rw [mem_IntCube]
    intro i
    obtain ⟨h1, h2⟩ := hp i
    refine ⟨?_, ?_⟩
    · rw [Int.floor_nonneg]; linarith
    · have hlt : p i + 1/2 < (((n : ℤ) + 1 : ℤ) : ℝ) := by push_cast; linarith
      have h := Int.floor_lt.mpr hlt
      omega
  · -- `|p i - q i| ≤ 1/2` from `Int.floor_le` and `Int.lt_floor_add_one`.
    intro i
    have h1 : (⌊p i + 1/2⌋ : ℝ) ≤ p i + 1/2 := Int.floor_le _
    have h2 : p i + 1/2 < (⌊p i + 1/2⌋ : ℝ) + 1 := Int.lt_floor_add_one _
    rw [abs_sub_le_iff]
    constructor <;> linarith

/-- Coordinate-wise distance bound for rounded points: `|y_i - q_i| ≤
|y_i - p_i| + 1/2` whenever `|p_i - q_i| ≤ 1/2`. Triangle inequality. -/
lemma abs_diff_le_of_rounded {k : ℕ} (p : Vec k) (q : IntVec k)
    (hpq : ∀ i, |p i - (q i : ℝ)| ≤ 1 / 2) (y : Vec k) (i : Fin k) :
    |y i - (q i : ℝ)| ≤ |y i - p i| + 1 / 2 :=
  calc |y i - (q i : ℝ)|
      ≤ |y i - p i| + |p i - (q i : ℝ)| := abs_sub_le _ _ _
    _ ≤ |y i - p i| + 1 / 2 := by linarith [hpq i]

/-- Reverse direction: `|y_i - q_i| ≥ |y_i - p_i| - 1/2`. -/
lemma abs_diff_ge_of_rounded {k : ℕ} (p : Vec k) (q : IntVec k)
    (hpq : ∀ i, |p i - (q i : ℝ)| ≤ 1 / 2) (y : Vec k) (i : Fin k) :
    |y i - p i| - 1 / 2 ≤ |y i - (q i : ℝ)| := by
  have h1 : |y i - p i| ≤ |y i - (q i : ℝ)| + |(q i : ℝ) - p i| := abs_sub_le _ _ _
  have h2 : |(q i : ℝ) - p i| = |p i - (q i : ℝ)| := abs_sub_comm _ _
  linarith [hpq i]

/-- For integer-valued vectors `y` and `q`, `|y i - q i|` (as a real number) is a
non-negative integer — specifically, `(|y i - q i|.toNat : ℝ)`. -/
lemma abs_intVec_sub_eq_nat {k : ℕ} (y q : IntVec k) (i : Fin k) :
    ∃ m : ℕ, |y.toVec i - q.toVec i| = (m : ℝ) :=
  ⟨(|y i - q i|).toNat, by
    rw [IntVec.toVec_apply, IntVec.toVec_apply, ← Int.cast_sub, ← Int.cast_abs]
    exact_mod_cast (Int.toNat_of_nonneg (abs_nonneg _)).symm⟩

/-- `linfDist` upper bound under rounding: `linfDist y q.toVec ≤ linfDist y p + 1/2`. -/
lemma linfDist_le_of_rounded {k : ℕ} [NeZero k] (p : Vec k) (q : IntVec k)
    (hpq : ∀ i, |p i - (q i : ℝ)| ≤ 1 / 2) (y : Vec k) :
    linfDist y q.toVec ≤ linfDist y p + 1 / 2 := by
  have hne : (Finset.univ : Finset (Fin k)).Nonempty :=
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne k)⟩, Finset.mem_univ _⟩
  unfold linfDist
  rw [dif_pos hne, dif_pos hne]
  refine Finset.sup'_le _ _ ?_
  intro i _
  have h := abs_diff_le_of_rounded p q hpq y i
  have hsup : |y i - p i| ≤ Finset.univ.sup' hne (fun j => |y j - p j|) :=
    Finset.le_sup' (f := fun j => |y j - p j|) (Finset.mem_univ i)
  rw [IntVec.toVec_apply]
  linarith

/-- `linfDist` lower bound under rounding: `linfDist y p - 1/2 ≤ linfDist y q.toVec`. -/
lemma linfDist_ge_of_rounded {k : ℕ} [NeZero k] (p : Vec k) (q : IntVec k)
    (hpq : ∀ i, |p i - (q i : ℝ)| ≤ 1 / 2) (y : Vec k) :
    linfDist y p - 1 / 2 ≤ linfDist y q.toVec := by
  have hne : (Finset.univ : Finset (Fin k)).Nonempty :=
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne k)⟩, Finset.mem_univ _⟩
  -- Pick j achieving max in linfDist y p.
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup' hne (fun i => |y i - p i|)
  have hjeq : linfDist y p = |y j - p j| := by
    unfold linfDist; rw [dif_pos hne]; exact hj
  have hjlow : |y j - p j| - 1 / 2 ≤ |y j - q.toVec j| := abs_diff_ge_of_rounded p q hpq y j
  have hjle : |y j - q.toVec j| ≤ linfDist y q.toVec := by
    unfold linfDist; rw [dif_pos hne]
    exact Finset.le_sup' (f := fun i => |y i - q.toVec i|) (Finset.mem_univ j)
  linarith

/-- The `ℓ∞` distance between two integer vectors is a natural number when cast
to `ℝ`. Useful for the parity argument in pyramid containment under rounding. -/
lemma linfDist_intVec_eq_nat {k : ℕ} [NeZero k] (y q : IntVec k) :
    ∃ m : ℕ, linfDist y.toVec q.toVec = (m : ℝ) := by
  have hne : (Finset.univ : Finset (Fin k)).Nonempty :=
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne k)⟩, Finset.mem_univ _⟩
  refine ⟨Finset.univ.sup' hne (fun i => (|y i - q i|).toNat), ?_⟩
  unfold linfDist
  rw [dif_pos hne]
  -- Both sides are sup over a finite nonempty set of `|y i - q i|` values,
  -- compared as ℝ vs Nat.
  have hcast : ∀ i ∈ Finset.univ,
      |y.toVec i - q.toVec i| = ((|y i - q i|).toNat : ℝ) := by
    intro i _
    rw [IntVec.toVec_apply, IntVec.toVec_apply, ← Int.cast_sub, ← Int.cast_abs]
    exact_mod_cast (Int.toNat_of_nonneg (abs_nonneg _)).symm
  rw [Finset.sup'_congr hne rfl hcast]
  -- Now `(Nat.cast ∘ f).sup' = Nat.cast (f.sup')` since `Nat.cast` is monotone.
  exact (Finset.comp_sup'_eq_sup'_comp hne (fun n : ℕ => (n : ℝ))
    (fun _ _ => by simp [Nat.cast_max])).symm

/-- The signed coordinate difference at the pyramid-realising coordinate `i`,
after rounding to `q`, sits in the interval `[M_p − 1/2, M_p + 1/2]` where
`M_p = linfDist y p` is the original max distance. -/
lemma signed_coord_diff_bounds {k : ℕ} (p : Vec k) (q : IntVec k)
    (hpq : ∀ i, |p i - (q i : ℝ)| ≤ 1 / 2) (y : Vec k) (i : Fin k) (ϕ : Bool)
    (hypyr : y ∈ Pyramid i ϕ p) :
    linfDist y p - 1 / 2 ≤ signR ϕ * (y i - (q i : ℝ)) ∧
    signR ϕ * (y i - (q i : ℝ)) ≤ linfDist y p + 1 / 2 := by
  rw [mem_pyramid_iff_sign] at hypyr
  have h1 : signR ϕ * (y i - (q i : ℝ)) = linfDist y p + signR ϕ * (p i - (q i : ℝ)) := by
    have e : signR ϕ * (y i - (q i : ℝ)) =
             signR ϕ * (y i - p i) + signR ϕ * (p i - (q i : ℝ)) := by ring
    rw [e, hypyr]
  have habs_signR : |signR ϕ| = 1 := by cases ϕ <;> simp [signR]
  have h2 : |signR ϕ * (p i - (q i : ℝ))| ≤ 1 / 2 := by
    rw [abs_mul, habs_signR, one_mul]
    exact hpq i
  rw [h1]
  have := abs_le.mp h2
  constructor <;> linarith

/-- **Balanced-point existence, Brouwer-free.** For any finite candidate set
`T ⊆ EVEN(n, k)` there is a *real* point `c ∈ [0, n]^k` such that for every
sign vector `s`,

`|T| ≤ 2 · |T ∩ {y : y.toVec ∈ ⋃ᵢ 𝒫ᵢ(c, sᵢ)}|`.

This is `exists_balanced_point_box` transported along the injection
`IntVec.toVec`. Two things vanish relative to CLY's route:

* Brouwer, the thickening `Sᵗ` and the `t → ∞` limit (their Lemmas 6, 7) are
  replaced by "a convex continuous function on a compact box has a minimum";
* the parity-aware rounding (their Lemma 8) is not needed at all. It exists
  only to transfer a *volume* balance to a *counting* balance; here the balance
  is obtained for the counting measure on `T` directly, and the ties it is
  designed to handle are absorbed by the `max` in `sgnSup`.

The price is that the balanced point is a real point rather than an odd
integer point — which is harmless, since `halving_from_balanced` and the
algorithm only ever use it as a base for pyramids. -/
theorem exists_balanced_point_real (n : ℕ) {k : ℕ} [NeZero k] (T : Set (IntVec k))
    (hTfin : T.Finite) (hTsub : ∀ y ∈ T, y ∈ EVEN n k) :
    ∃ c : Vec k, c ∈ CubeBox 0 n k ∧ ∀ s : Fin k → Bool,
      T.ncard ≤ 2 *
        (T ∩ {y : IntVec k | ∃ i, y.toVec ∈ Pyramid i (s i) c}).ncard := by
  have hinj : Function.Injective (IntVec.toVec (k := k)) := by
    intro x y hxy
    funext i
    have h := congrFun hxy i
    rw [IntVec.toVec_apply, IntVec.toVec_apply] at h
    exact_mod_cast h
  set S : Finset (Vec k) := hTfin.toFinset.image IntVec.toVec with hS_def
  have hS_bound : ∀ y ∈ S, ∀ i, (0 : ℝ) ≤ y i ∧ y i ≤ (n : ℝ) := by
    intro y hy i
    rw [hS_def, Finset.mem_image] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    have hz' := hTsub z (hTfin.mem_toFinset.mp hz)
    rw [mem_EVEN] at hz'
    obtain ⟨h1, h2⟩ := hz'.1 i
    rw [IntVec.toVec_apply]
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  obtain ⟨c, hc_mem, hc_bal⟩ :=
    exists_balanced_point_box (k := k) 0 n (Nat.cast_nonneg n) S hS_bound
  refine ⟨c, hc_mem, fun s => ?_⟩
  have hcard_S : S.card = T.ncard := by
    rw [hS_def, Finset.card_image_of_injective _ hinj,
      Set.ncard_eq_toFinset_card T hTfin]
  have himg : S.filter (fun y => ∃ i, y ∈ Pyramid i (s i) c)
      = (hTfin.toFinset.filter
          (fun z : IntVec k => ∃ i, z.toVec ∈ Pyramid i (s i) c)).image IntVec.toVec := by
    rw [hS_def]
    ext y
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hp⟩; exact ⟨z, ⟨hz, hp⟩, rfl⟩
    · rintro ⟨z, ⟨hz, hp⟩, rfl⟩; exact ⟨⟨z, hz, rfl⟩, hp⟩
  have hfin2 : (T ∩ {y : IntVec k | ∃ i, y.toVec ∈ Pyramid i (s i) c}).Finite :=
    hTfin.subset Set.inter_subset_left
  have hfilter : (S.filter (fun y => ∃ i, y ∈ Pyramid i (s i) c)).card
      = (T ∩ {y : IntVec k | ∃ i, y.toVec ∈ Pyramid i (s i) c}).ncard := by
    rw [himg, Finset.card_image_of_injective _ hinj,
      Set.ncard_eq_toFinset_card _ hfin2]
    congr 1
    ext z
    simp [Set.Finite.mem_toFinset, Finset.mem_filter]
  rw [← hcard_S, ← hfilter]
  exact hc_bal s


/-- **Halving lemma (CLY Lemma 5, geometric core).** Given a balanced point `q`
of `T`, the *shifted* base `b = q.toVec + 2·s.toReal` (where `s.toReal i` is `+1`
or `−1`) and the corresponding pyramid union captures **at most** half of `T`:

`|T ∩ {y : y.toVec ∈ ⋃ᵢ 𝒫ᵢ(b, sᵢ)}| ≤ |T|/2`.

Proof: combine the balanced-point hypothesis at `q` (captures `≥ |T|/2` with
*flipped* signs) with `pyramid_disjoint_of_lt` (which makes the two pyramid
unions disjoint), giving complementary halves of `T`. -/
theorem halving_from_balanced {k : ℕ} (T : Set (IntVec k))
    (hTfin : T.Finite) (c : Vec k)
    (hbal : ∀ s : Fin k → Bool, T.ncard ≤ 2 *
      (T ∩ {y : IntVec k | ∃ i, y.toVec ∈ Pyramid i (s i) c}).ncard)
    (s : Fin k → Bool) :
    let b : Vec k := c + fun i => if s i then 2 else -2
    2 * (T ∩ {y : IntVec k | ∃ i, y.toVec ∈ Pyramid i (s i) b}).ncard ≤ T.ncard := by
  intro b
  have hb_eq : b = c + fun i => 2 * signR (s i) := by
    funext i
    simp only [b, Pi.add_apply]
    cases s i <;> simp [signR]
  set A : Set (IntVec k) := T ∩ {y | ∃ i, y.toVec ∈ Pyramid i (!s i) c} with hA_def
  set B : Set (IntVec k) := T ∩ {y | ∃ i, y.toVec ∈ Pyramid i (s i) b} with hB_def
  have hA_fin : A.Finite := hTfin.subset Set.inter_subset_left
  have hB_fin : B.Finite := hTfin.subset Set.inter_subset_left
  -- Disjointness of A and B follows from `pyramid_union_disjoint_shifted` on Vec k.
  have h_disj : Disjoint A B := by
    rw [Set.disjoint_left]
    intro y hyA hyB
    obtain ⟨_, i₀, hi₀⟩ := hyA
    obtain ⟨_, i₁, hi₁⟩ := hyB
    have h_disj_vec := pyramid_union_disjoint_shifted c s
    rw [Set.disjoint_left] at h_disj_vec
    refine h_disj_vec (Set.mem_iUnion.mpr ⟨i₀, hi₀⟩) ?_
    rw [← hb_eq]
    exact Set.mem_iUnion.mpr ⟨i₁, hi₁⟩
  -- A ∪ B ⊆ T, so |A ∪ B| ≤ |T|. Disjointness gives |A ∪ B| = |A| + |B|.
  have h_AB_sub : A ∪ B ⊆ T := Set.union_subset Set.inter_subset_left Set.inter_subset_left
  have h_card_union : (A ∪ B).ncard = A.ncard + B.ncard :=
    Set.ncard_union_eq h_disj hA_fin hB_fin
  have h_card_AB_le : (A ∪ B).ncard ≤ T.ncard := Set.ncard_le_ncard h_AB_sub hTfin
  have h_sum : A.ncard + B.ncard ≤ T.ncard := by rw [← h_card_union]; exact h_card_AB_le
  -- Balanced point applied to the flipped sign vector lower-bounds |A|.
  have h_flipped : T.ncard ≤ 2 * A.ncard := hbal (fun i => !s i)
  omega

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

/-- Auxiliary: choose a balanced point of `T`, defaulting to `0` if `T` isn't
known to be a subset of `EVEN(n, k)`. Encapsulated so the conditional is not
visible to `split_ifs` in algorithm proofs. -/
noncomputable def clyChooseBalanced {k : ℕ} (n : ℕ) (T : Finset (IntVec k)) : Vec k :=
  if h : ∃ c : Vec k, c ∈ CubeBox 0 n k ∧ ∀ s : Fin k → Bool,
      (T : Set (IntVec k)).ncard ≤ 2 *
        ((T : Set (IntVec k)) ∩ {y : IntVec k | ∃ i, y.toVec ∈ Pyramid i (s i) c}).ncard
    then h.choose else 0

/-- `clyChooseBalanced` always returns a point of the box `[0, n]^k`. -/
lemma clyChooseBalanced_mem_cubeBox {k : ℕ} (n : ℕ) (T : Finset (IntVec k)) :
    clyChooseBalanced n T ∈ CubeBox 0 n k := by
  unfold clyChooseBalanced
  split_ifs with h
  · exact h.choose_spec.1
  · intro _; exact ⟨le_refl _, Nat.cast_nonneg n⟩

/-- The defining property of `clyChooseBalanced`, available whenever `k ≠ 0`
and `T` really is a set of even grid points. -/
lemma clyChooseBalanced_spec {k : ℕ} [NeZero k] (n : ℕ) (T : Finset (IntVec k))
    (h : ∀ y ∈ (T : Set (IntVec k)), y ∈ EVEN n k) (s : Fin k → Bool) :
    (T : Set (IntVec k)).ncard ≤ 2 *
      ((T : Set (IntVec k)) ∩
        {y : IntVec k | ∃ i, y.toVec ∈ Pyramid i (s i) (clyChooseBalanced n T)}).ncard := by
  have hex : ∃ c : Vec k, c ∈ CubeBox 0 n k ∧ ∀ s : Fin k → Bool,
      (T : Set (IntVec k)).ncard ≤ 2 *
        ((T : Set (IntVec k)) ∩ {y : IntVec k | ∃ i, y.toVec ∈ Pyramid i (s i) c}).ncard :=
    exists_balanced_point_real (k := k) n (T : Set (IntVec k)) T.finite_toSet h
  unfold clyChooseBalanced
  rw [dif_pos hex]
  exact hex.choose_spec.2 s

/-! ## The algorithm

The recursive algorithm, its correctness (CLY Lemma 5) and the query bound live
in `Tfnp/Algorithm.lean`, which builds on `exists_balanced_point_real` above
together with the three geometric lemmas of CLY Section 3. -/

end Tfnp.Contraction
