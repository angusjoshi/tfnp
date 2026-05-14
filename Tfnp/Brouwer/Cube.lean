/-
Copyright (c) 2026 Angus Joshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Angus Joshi
-/
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Constructions
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Tfnp.Brouwer.Brouwer_product

/-!
# Brouwer's fixed-point theorem on a closed cube `[a, b]^k`

Derived from `Brouwer_Product` (the product-of-simplices form proved via Scarf's
combinatorial lemma in `Tfnp/Brouwer/Brouwer_product.lean`) by the affine
homeomorphism `[a, b] ≃ stdSimplex ℝ (Fin 2)`, `t ↦ ((t-a)/(b-a), (b-t)/(b-a))`.

`brouwer_cube` is exposed for use as a replacement for the previous axiom in
`Tfnp/Contraction.lean`.
-/

open Filter Topology

/-- The closed `k`-dimensional box `[a, b]^k`. -/
def CubeBox (a b : ℝ) (k : ℕ) : Set (Fin k → ℝ) :=
  { x | ∀ i, a ≤ x i ∧ x i ≤ b }

/-- **Brouwer's fixed-point theorem on a closed cube.** Every continuous self-map
of `[a, b]^k` (with `a ≤ b`) has a fixed point in the cube. -/
theorem brouwer_cube {k : ℕ} {a b : ℝ} (hab : a ≤ b) (f : (Fin k → ℝ) → (Fin k → ℝ))
    (hcont : ContinuousOn f (CubeBox a b k))
    (hmaps : Set.MapsTo f (CubeBox a b k) (CubeBox a b k)) :
    ∃ x ∈ CubeBox a b k, f x = x := by
  -- Edge case 1: `k = 0`.  The cube has a unique element (the empty function).
  rcases Nat.eq_zero_or_pos k with rfl | hk_pos
  · refine ⟨0, fun i => i.elim0, ?_⟩
    funext i; exact i.elim0
  -- Edge case 2: `a = b`.  The cube is the singleton `{fun _ => a}`.
  rcases lt_or_eq_of_le hab with hab_lt | hab_eq
  swap
  · subst hab_eq
    refine ⟨fun _ => a, fun _ => ⟨le_refl _, le_refl _⟩, ?_⟩
    have hpt : (fun _ : Fin k => a) ∈ CubeBox a a k := fun _ => ⟨le_refl _, le_refl _⟩
    funext i
    have hf_i := hmaps hpt i
    exact le_antisymm hf_i.2 hf_i.1
  -- Main case: `k ≥ 1` and `a < b`.  Reduce to `Brouwer_Product` on the product
  -- of `k` copies of `stdSimplex ℝ (Fin 2)`.
  have hba : (0 : ℝ) < b - a := sub_pos.mpr hab_lt
  haveI : NeZero k := ⟨Nat.pos_iff_ne_zero.mp hk_pos⟩
  -- The clipping `max 0 (min 1 ·)`; used to make the embedding total-and-continuous.
  let clip01 : ℝ → ℝ := fun t => max 0 (min 1 t)
  have clip01_nn : ∀ t, 0 ≤ clip01 t := fun _ => le_max_left _ _
  have clip01_le : ∀ t, clip01 t ≤ 1 := fun _ => max_le (by norm_num) (min_le_left _ _)
  have clip01_cont : Continuous clip01 :=
    continuous_const.max (continuous_const.min continuous_id)
  have clip01_eq : ∀ {t : ℝ}, 0 ≤ t → t ≤ 1 → clip01 t = t := by
    intro t h0 h1
    change max 0 (min 1 t) = t
    rw [min_eq_right h1, max_eq_right h0]
  -- One-dimensional embedding `[a, b] ↪ stdSimplex ℝ (Fin 2)` (extended by
  -- clipping outside `[a, b]`).
  let toSx : ℝ → stdSimplex ℝ (Fin 2) := fun y =>
    ⟨![clip01 ((y - a) / (b - a)), 1 - clip01 ((y - a) / (b - a))], by
      refine ⟨fun j => ?_, ?_⟩
      · fin_cases j
        · exact clip01_nn _
        · change 0 ≤ 1 - clip01 ((y - a) / (b - a))
          linarith [clip01_le ((y - a) / (b - a))]
      · rw [Fin.sum_univ_two]
        change ![_, _] 0 + ![_, _] 1 = 1
        simp⟩
  -- One-dimensional projection `stdSimplex ℝ (Fin 2) → [a, b]`.
  let frSx : stdSimplex ℝ (Fin 2) → ℝ := fun x => a + x.1 0 * (b - a)
  have frSx_mem : ∀ x : stdSimplex ℝ (Fin 2), a ≤ frSx x ∧ frSx x ≤ b := by
    intro x
    have h0 : 0 ≤ x.1 0 := x.2.1 0
    have hsum := x.2.2
    rw [Fin.sum_univ_two] at hsum
    have h_other : 0 ≤ x.1 1 := x.2.1 1
    have h1 : x.1 0 ≤ 1 := by linarith
    refine ⟨?_, ?_⟩
    · change a ≤ a + x.1 0 * (b - a); nlinarith
    · change a + x.1 0 * (b - a) ≤ b; nlinarith
  have frSx_toSx : ∀ y, a ≤ y → y ≤ b → frSx (toSx y) = y := by
    intro y hy1 hy2
    have hmem : 0 ≤ (y - a) / (b - a) ∧ (y - a) / (b - a) ≤ 1 :=
      ⟨div_nonneg (sub_nonneg.mpr hy1) hba.le,
       (div_le_one hba).mpr (sub_le_sub_right hy2 a)⟩
    change a + (toSx y).1 0 * (b - a) = y
    have h0 : (toSx y).1 0 = (y - a) / (b - a) := by
      change (![clip01 ((y - a) / (b - a)), 1 - clip01 ((y - a) / (b - a))] : Fin 2 → ℝ) 0
            = (y - a) / (b - a)
      simp [clip01_eq hmem.1 hmem.2]
    rw [h0]
    field_simp
    ring
  have toSx_cont : Continuous toSx := by
    refine Continuous.subtype_mk ?_ _
    refine continuous_pi (fun j => ?_)
    have hclip : Continuous (fun y : ℝ => clip01 ((y - a) / (b - a))) :=
      clip01_cont.comp ((continuous_id.sub continuous_const).div_const _)
    fin_cases j
    · change Continuous (fun y => (![clip01 ((y - a) / (b - a)),
                    1 - clip01 ((y - a) / (b - a))] : Fin 2 → ℝ) 0)
      simp only [Matrix.cons_val_zero]
      exact hclip
    · change Continuous (fun y => (![clip01 ((y - a) / (b - a)),
                    1 - clip01 ((y - a) / (b - a))] : Fin 2 → ℝ) 1)
      simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]
      exact continuous_const.sub hclip
  have frSx_cont : Continuous frSx :=
    continuous_const.add
      (((continuous_apply 0).comp continuous_subtype_val).mul continuous_const)
  -- The lifted self-map on `ProductSimplices`.
  let card : Fin k → ℕ+ := fun _ => 2
  let extract : ProductSimplices card → (Fin k → ℝ) := fun x j => frSx (x j)
  have extract_cont : Continuous extract :=
    continuous_pi (fun j => frSx_cont.comp (continuous_apply j))
  have extract_in : ∀ x : ProductSimplices card, extract x ∈ CubeBox a b k :=
    fun x j => frSx_mem (x j)
  let F : ProductSimplices card → ProductSimplices card :=
    fun x i => toSx (f (extract x) i)
  have F_cont : Continuous F := by
    refine continuous_pi (fun i => ?_)
    refine toSx_cont.comp ((continuous_apply i).comp ?_)
    exact hcont.comp_continuous extract_cont extract_in
  obtain ⟨x_star, hx_star⟩ := Brouwer_Product card F F_cont
  refine ⟨extract x_star, extract_in x_star, ?_⟩
  have fy_in : f (extract x_star) ∈ CubeBox a b k := hmaps (extract_in x_star)
  funext i
  have hF_at_i : F x_star i = x_star i := congr_fun hx_star i
  have h_apply_frSx : frSx (F x_star i) = frSx (x_star i) := congr_arg frSx hF_at_i
  change f (extract x_star) i = extract x_star i
  -- `F x_star i = toSx (f (extract x_star) i)`, so `frSx (F x_star i) = f (extract x_star) i`.
  have h_round : frSx (F x_star i) = f (extract x_star) i :=
    frSx_toSx _ (fy_in i).1 (fy_in i).2
  rw [h_round] at h_apply_frSx
  exact h_apply_frSx
