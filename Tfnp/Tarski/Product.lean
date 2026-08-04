/-
Copyright (c) 2026 Angus Joshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Angus Joshi
-/
import Tfnp.Tarski.Basic

/-!
# The product lattice `ℕ^(a+b) = ℕ^a × ℕ^b`

FPS's decomposition theorem (their Section 5) rests on the observation that the
`k`-dimensional grid factors as a product `A × B` for any `a + b = k`.  This file
provides that factorisation: `cat`, `pr1`, `pr2`, and the fact that the
componentwise order on `Pt (a + b)` is the product order.

It also provides the *slice* function `sliceFun f x`, the `b`-dimensional
function obtained by freezing the first `a` coordinates at `x` — FPS's `f_{s_x}`
projected onto the free coordinates.
-/

namespace Tfnp.Tarski

variable {a b : ℕ}

/-! ### Concatenation and projection -/

/-- Concatenate an `a`-dimensional point and a `b`-dimensional point. -/
def cat (u : Pt a) (v : Pt b) : Pt (a + b) := Fin.append u v

/-- The first `a` coordinates. -/
def pr1 (x : Pt (a + b)) : Pt a := fun i => x (Fin.castAdd b i)

/-- The last `b` coordinates. -/
def pr2 (x : Pt (a + b)) : Pt b := fun i => x (Fin.natAdd a i)

@[simp] lemma cat_castAdd (u : Pt a) (v : Pt b) (i : Fin a) :
    cat u v (Fin.castAdd b i) = u i := Fin.append_left u v i

@[simp] lemma cat_natAdd (u : Pt a) (v : Pt b) (i : Fin b) :
    cat u v (Fin.natAdd a i) = v i := Fin.append_right u v i

@[simp] lemma pr1_cat (u : Pt a) (v : Pt b) : pr1 (cat u v) = u := funext fun _ => by simp [pr1]
@[simp] lemma pr2_cat (u : Pt a) (v : Pt b) : pr2 (cat u v) = v := funext fun _ => by simp [pr2]

@[simp] lemma cat_pr (x : Pt (a + b)) : cat (pr1 x) (pr2 x) = x := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simp [pr1]
  · simp [pr2]

/-- The componentwise order on `Pt (a + b)` is the product order. -/
lemma cat_le_cat {u u' : Pt a} {v v' : Pt b} :
    cat u v ≤ cat u' v' ↔ u ≤ u' ∧ v ≤ v' := by
  constructor
  · intro h
    exact ⟨coord_le fun i => by simpa using le_coord h (Fin.castAdd b i),
           coord_le fun i => by simpa using le_coord h (Fin.natAdd a i)⟩
  · intro ⟨h1, h2⟩
    refine coord_le fun j => ?_
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simpa using le_coord h1 i
    · simpa using le_coord h2 i

lemma le_iff_pr {x y : Pt (a + b)} : x ≤ y ↔ pr1 x ≤ pr1 y ∧ pr2 x ≤ pr2 y := by
  rw [← cat_pr x, ← cat_pr y, cat_le_cat, pr1_cat, pr1_cat, pr2_cat, pr2_cat]

lemma pr1_mono {x y : Pt (a + b)} (h : x ≤ y) : pr1 x ≤ pr1 y := (le_iff_pr.mp h).1
lemma pr2_mono {x y : Pt (a + b)} (h : x ≤ y) : pr2 x ≤ pr2 y := (le_iff_pr.mp h).2

lemma cat_mono {u u' : Pt a} {v v' : Pt b} (h1 : u ≤ u') (h2 : v ≤ v') :
    cat u v ≤ cat u' v' := cat_le_cat.mpr ⟨h1, h2⟩

lemma mem_Box_cat {loA hiA : Pt a} {loB hiB : Pt b} {u : Pt a} {v : Pt b} :
    cat u v ∈ Box (cat loA loB) (cat hiA hiB) ↔ u ∈ Box loA hiA ∧ v ∈ Box loB hiB := by
  simp only [mem_Box, cat_le_cat]
  tauto

/-! ### Slices

`sliceFun f x` is the `b`-dimensional function obtained from `f : Pt (a+b) →
Pt (a+b)` by freezing the first `a` coordinates at `x` and reading off the last
`b` coordinates of the result.  A fixed point of `sliceFun f x` is exactly a
point that FPS call "a fixed point of the slice `s_x`". -/

/-- Freeze the first `a` coordinates at `x`: the `b`-dimensional slice function. -/
def sliceFun (f : Pt (a + b) → Pt (a + b)) (x : Pt a) : Pt b → Pt b :=
  fun v => pr2 (f (cat x v))

@[simp] lemma sliceFun_apply (f : Pt (a + b) → Pt (a + b)) (x : Pt a) (v : Pt b) :
    sliceFun f x v = pr2 (f (cat x v)) := rfl

/-- If `f` maps the product box into itself then each slice function maps the
`B`-box into itself. -/
lemma sliceFun_mapsTo {f : Pt (a + b) → Pt (a + b)} {loA hiA : Pt a} {loB hiB : Pt b}
    (hmap : ∀ z ∈ Box (cat loA loB) (cat hiA hiB), f z ∈ Box (cat loA loB) (cat hiA hiB))
    {x : Pt a} (hx : x ∈ Box loA hiA) :
    ∀ v ∈ Box loB hiB, sliceFun f x v ∈ Box loB hiB := by
  intro v hv
  have := hmap (cat x v) (mem_Box_cat.mpr ⟨hx, hv⟩)
  rw [← cat_pr (f (cat x v))] at this
  exact (mem_Box_cat.mp this).2

/-- A violation of order preservation in a slice is a violation in the whole
instance (FPS, Section 2, "Slices"). -/
lemma isVop_of_slice {f : Pt (a + b) → Pt (a + b)} {x : Pt a} {v w : Pt b}
    (h : IsVop (sliceFun f x) v w) :
    IsVop f (cat x v) (cat x w) :=
  ⟨cat_mono le_rfl h.1, fun hle => h.2 (pr2_mono hle)⟩

/-- A solution of a slice instance lifts to the ambient instance, except that a
slice *fixed point* only becomes a fixed point of `f` once the `A`-coordinates
are also fixed; that residual condition is what the outer algorithm handles. -/
lemma isSol_slice_vop {f : Pt (a + b) → Pt (a + b)} {x : Pt a} {loB hiB : Pt b}
    {v w : Pt b} (h : IsSol (sliceFun f x) loB hiB (.inr (v, w))) :
    IsVop f (cat x v) (cat x w) := isVop_of_slice h.2.2

end Tfnp.Tarski
