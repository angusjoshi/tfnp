/-
Copyright (c) 2026 Angus Joshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Angus Joshi
-/
import Tfnp.Tarski.Basic
import Tfnp.Tarski.Simulation
import Mathlib.Data.Nat.Log

/-!
# `Tarski*`, and the framework of Chen–Li–Yannakakis 2026

> Xi Chen, Yuhao Li, Mihalis Yannakakis.
> *The Mystery Deepens: On the Query Complexity of Tarski Fixed Points.*
> [arXiv:2604.00268](https://arxiv.org/abs/2604.00268)

That paper gives an `O(log² n)`-query algorithm for `Tarski(n,4)`, matching the
`Ω(log² n)` lower bound of Etessami–Papadimitriou–Rubinstein–Yannakakis, and an
`O(log^(⌈(k-1)/3⌉+1) n)` algorithm for general constant `k`.  Its engine is an
`O(log n)`-query algorithm for the *three*-dimensional `Tarski*` problem, plus two
older ingredients:

* the reduction from `Tarski(n,k+1)` to `Tarski*(n,k)`, costing a factor `O(log n)`
  (Chen–Li, Lemma 3.2), and
* Chen–Li's decomposition theorem for `Tarski*`, which multiplies query
  complexities across a product of lattices — the `Tarski*` analogue of
  Fearnley–Pálvölgyi–Savani's Theorem 18 (see `Tfnp/Tarski/Decomposition.lean`).

## What is proved here

* `IsStarSol`, `StarInstance` — `Tarski*(n,k)` (Chen–Li; Definition 1 of CLY26).
* `StarInstance.exists_sol` — **totality of `Tarski*`**: a fixed point of the
  value part is a solution whatever the sign says, and monotone self-maps of a box
  have fixed points.
* `mapsTo_of_down`, `mapsTo_of_up` — the halving step: a point where a monotone `g`
  goes down (resp. up) confines the search to a sub-box.  This is the whole
  content of the reduction.
* `starOfSlice` — the `Tarski*(n,k)` instance built from a `Tarski(n,k+1)`
  instance on its middle slice, and `starOfSlice_sol_gives_halving` — **the
  Chen–Li reduction**: a `Tarski*` solution for it halves the last dimension.

## What is stated but not proved

The two genuinely algorithmic results of the recent literature are given as
explicit `Prop`s rather than as `theorem`s with `sorry`, so that nothing in this
development claims a proof it does not have:

* `Tarski3StarInLogQueries` — CLY26's Theorem 1 (`Tarski*(n,3)` in `O(log n)`).
* `StarDecompositionTheorem` — Chen–Li's decomposition theorem for `Tarski*`.

`Tfnp/Tarski/PIFunction.lean` develops the partial-information machinery CLY26
use to attack the first of these.
-/

namespace Tfnp.Tarski

variable {k : ℕ}

/-! ### Fixed points of monotone maps of a box

`exists_sol_of_mapsTo` produces a fixed point *or* a violation; monotonicity rules
out the violation. -/

/-- `f` is monotone on the box `Box lo hi`. -/
def MonotoneOn' (f : Pt k → Pt k) (lo hi : Pt k) : Prop :=
  ∀ x ∈ Box lo hi, ∀ y ∈ Box lo hi, x ≤ y → f x ≤ f y

/-- **Tarski's fixed point theorem on a box.**  A monotone self-map of a
non-empty box has a fixed point in it. -/
theorem exists_fixedPoint_of_monotoneOn {f : Pt k → Pt k} {lo hi : Pt k} (h : lo ≤ hi)
    (hmono : MonotoneOn' f lo hi) (hmap : ∀ x ∈ Box lo hi, f x ∈ Box lo hi) :
    ∃ x ∈ Box lo hi, f x = x := by
  obtain ⟨ans, hans⟩ := exists_sol_of_mapsTo h hmap
  cases ans with
  | inl x => exact ⟨x, hans.1, hans.2⟩
  | inr p =>
    obtain ⟨hx, hy, hxy, hvop⟩ := hans
    exact absurd (hmono _ hx _ hy hxy) hvop

/-! ### The halving step (Chen–Li, Lemma 3.2)

The point of `Tarski*` is that its solutions need not be fixed points: it suffices
to find a point at which `f` goes weakly up, *or* weakly down, in a controlled
way.  Either outcome shrinks the search space, because of the following two
lemmas. -/

/-- If `g` is monotone on `Box lo hi` and `z` in that box satisfies `g z ≤ z`, then
`g` maps `Box lo z` into itself — so a fixed point may be sought there. -/
lemma mapsTo_of_down {g : Pt k → Pt k} {lo hi z : Pt k}
    (hmono : MonotoneOn' g lo hi) (hmap : ∀ x ∈ Box lo hi, g x ∈ Box lo hi)
    (hz : z ∈ Box lo hi) (hdown : g z ≤ z) :
    ∀ x ∈ Box lo z, g x ∈ Box lo z := by
  intro x hx
  obtain ⟨hlox, hxz⟩ := mem_Box.mp hx
  have hxbox : x ∈ Box lo hi := mem_Box.mpr ⟨hlox, hxz.trans (mem_Box.mp hz).2⟩
  exact mem_Box.mpr ⟨(mem_Box.mp (hmap x hxbox)).1, (hmono x hxbox z hz hxz).trans hdown⟩

/-- Dual of `mapsTo_of_down`: a point where `g` goes up confines the search to the
upper sub-box. -/
lemma mapsTo_of_up {g : Pt k → Pt k} {lo hi z : Pt k}
    (hmono : MonotoneOn' g lo hi) (hmap : ∀ x ∈ Box lo hi, g x ∈ Box lo hi)
    (hz : z ∈ Box lo hi) (hup : z ≤ g z) :
    ∀ x ∈ Box z hi, g x ∈ Box z hi := by
  intro x hx
  obtain ⟨hzx, hxhi⟩ := mem_Box.mp hx
  have hxbox : x ∈ Box lo hi := mem_Box.mpr ⟨(mem_Box.mp hz).1.trans hzx, hxhi⟩
  exact mem_Box.mpr ⟨hup.trans (hmono z hz x hxbox hzx), (mem_Box.mp (hmap x hxbox)).2⟩

/-! ### `Tarski*` -/

/-- An instance of `Tarski*(n,k)` on the box `Box lo hi` (Chen–Li; CLY26
Definition 1): a monotone map `x ↦ (val x, sgn x)` into `Pt k × Bool`, where
`true` stands for `+1`.  Both components must be monotone. -/
structure StarInstance (k : ℕ) (lo hi : Pt k) : Type where
  /-- The first `k` coordinates of the output. -/
  val : Pt k → Pt k
  /-- The `(k+1)`-st coordinate: `true` is `+1`, `false` is `-1`. -/
  sgn : Pt k → Bool
  /-- The box is non-empty. -/
  le : lo ≤ hi
  /-- `val` is monotone on the box. -/
  mono_val : MonotoneOn' val lo hi
  /-- `sgn` is monotone on the box. -/
  mono_sgn : ∀ x ∈ Box lo hi, ∀ y ∈ Box lo hi, x ≤ y → sgn x ≤ sgn y
  /-- `val` maps the box into itself. -/
  mapsTo : ∀ x ∈ Box lo hi, val x ∈ Box lo hi

namespace StarInstance

variable {lo hi : Pt k} (T : StarInstance k lo hi)

/-- A solution of `Tarski*`: a point at which `val` goes weakly up and the sign is
`+1`, or weakly down and the sign is `-1`.

Crucially this does *not* require a fixed point — which is exactly why `Tarski*`
can be easier than `Tarski`. -/
def IsStarSol (x : Pt k) : Prop :=
  x ∈ Box lo hi ∧ ((x ≤ T.val x ∧ T.sgn x = true) ∨ (T.val x ≤ x ∧ T.sgn x = false))

/-- A fixed point of `val` is a `Tarski*` solution, whichever way the sign
falls. -/
lemma isStarSol_of_fixed {x : Pt k} (hx : x ∈ Box lo hi) (hfix : T.val x = x) :
    T.IsStarSol x := by
  refine ⟨hx, ?_⟩
  cases hs : T.sgn x
  · exact Or.inr ⟨hfix.le, rfl⟩
  · exact Or.inl ⟨hfix.ge, rfl⟩

/-- **`Tarski*` is total.**  By Tarski's theorem `val` has a fixed point in the
box, and that is a solution. -/
theorem exists_sol : ∃ x, T.IsStarSol x := by
  obtain ⟨x, hx, hfix⟩ := exists_fixedPoint_of_monotoneOn T.le T.mono_val T.mapsTo
  exact ⟨x, T.isStarSol_of_fixed hx hfix⟩

end StarInstance

/-! ### The Chen–Li reduction `Tarski(n,k+1) → Tarski*(n,k)`

Split off the *last* coordinate.  Given a monotone `g` on a `(k+1)`-dimensional
box and a level `m` for the last coordinate, the `Tarski*` instance on the
`k`-dimensional slice `{z | z (last k) = m}` records, for each `x`, the first `k`
coordinates of `g` on the slice together with the *direction* in which `g` moves
the last coordinate.

A `Tarski*` solution then supplies a point of the slice at which `g` goes weakly
up or weakly down in *all* `k+1` coordinates, and `mapsTo_of_up` /
`mapsTo_of_down` halve the last dimension. -/

/-- Attach a value in the last coordinate. -/
def snocPt (x : Pt k) (m : ℕ) : Pt (k + 1) := Fin.snoc x m

/-- Forget the last coordinate. -/
def initPt (z : Pt (k + 1)) : Pt k := Fin.init z

@[simp] lemma snocPt_castSucc (x : Pt k) (m : ℕ) (i : Fin k) :
    snocPt x m (Fin.castSucc i) = x i := by simp [snocPt]

@[simp] lemma snocPt_last (x : Pt k) (m : ℕ) : snocPt x m (Fin.last k) = m := by simp [snocPt]

@[simp] lemma initPt_apply (z : Pt (k + 1)) (i : Fin k) : initPt z i = z (Fin.castSucc i) := rfl

@[simp] lemma initPt_snocPt (x : Pt k) (m : ℕ) : initPt (snocPt x m) = x := by
  funext i; simp

lemma snocPt_le_snocPt {x y : Pt k} {m m' : ℕ} (h : x ≤ y) (hm : m ≤ m') :
    snocPt x m ≤ snocPt y m' := by
  refine coord_le fun l => ?_
  refine Fin.lastCases ?_ ?_ l
  · simpa using hm
  · intro i; simpa using le_coord h i

lemma initPt_mono {z w : Pt (k + 1)} (h : z ≤ w) : initPt z ≤ initPt w :=
  coord_le fun i => le_coord h (Fin.castSucc i)

/-- A point of `Pt (k+1)` is `≤` another iff the last coordinates and the initial
segments compare. -/
lemma le_iff_init_last {z w : Pt (k + 1)} :
    z ≤ w ↔ initPt z ≤ initPt w ∧ z (Fin.last k) ≤ w (Fin.last k) := by
  refine ⟨fun h => ⟨initPt_mono h, le_coord h _⟩, fun ⟨h1, h2⟩ => coord_le fun l => ?_⟩
  refine Fin.lastCases ?_ ?_ l
  · exact h2
  · intro i; exact le_coord h1 i

section Reduction

variable {g : Pt (k + 1) → Pt (k + 1)} {LO HI : Pt (k + 1)} {m : ℕ}

/-- The `Tarski*(n,k)` instance carved out of a `Tarski(n,k+1)` instance by
freezing the last coordinate at `m`. -/
noncomputable def starOfSlice (hLOHI : LO ≤ HI)
    (hmono : MonotoneOn' g LO HI) (hmap : ∀ z ∈ Box LO HI, g z ∈ Box LO HI)
    (hm_lo : LO (Fin.last k) ≤ m) (hm_hi : m ≤ HI (Fin.last k)) :
    StarInstance k (initPt LO) (initPt HI) where
  val x := initPt (g (snocPt x m))
  sgn x := decide (m ≤ g (snocPt x m) (Fin.last k))
  le := initPt_mono hLOHI
  mono_val := by
    intro x hx y hy hxy
    refine initPt_mono (hmono _ ?_ _ ?_ (snocPt_le_snocPt hxy le_rfl))
    · exact mem_Box.mpr
        ⟨le_iff_init_last.mpr ⟨by simpa using (mem_Box.mp hx).1, by simpa using hm_lo⟩,
         le_iff_init_last.mpr ⟨by simpa using (mem_Box.mp hx).2, by simpa using hm_hi⟩⟩
    · exact mem_Box.mpr
        ⟨le_iff_init_last.mpr ⟨by simpa using (mem_Box.mp hy).1, by simpa using hm_lo⟩,
         le_iff_init_last.mpr ⟨by simpa using (mem_Box.mp hy).2, by simpa using hm_hi⟩⟩
  mono_sgn := by
    intro x hx y hy hxy
    have hg : g (snocPt x m) ≤ g (snocPt y m) :=
      hmono _ (mem_Box.mpr
          ⟨le_iff_init_last.mpr ⟨by simpa using (mem_Box.mp hx).1, by simpa using hm_lo⟩,
           le_iff_init_last.mpr ⟨by simpa using (mem_Box.mp hx).2, by simpa using hm_hi⟩⟩)
        _ (mem_Box.mpr
          ⟨le_iff_init_last.mpr ⟨by simpa using (mem_Box.mp hy).1, by simpa using hm_lo⟩,
           le_iff_init_last.mpr ⟨by simpa using (mem_Box.mp hy).2, by simpa using hm_hi⟩⟩)
        (snocPt_le_snocPt hxy le_rfl)
    have := le_coord hg (Fin.last k)
    simp only [decide_eq_true_eq, Bool.le_iff_imp, decide_eq_true_eq]
    omega
  mapsTo := by
    intro x hx
    have hz : snocPt x m ∈ Box LO HI := mem_Box.mpr
      ⟨le_iff_init_last.mpr ⟨by simpa using (mem_Box.mp hx).1, by simpa using hm_lo⟩,
       le_iff_init_last.mpr ⟨by simpa using (mem_Box.mp hx).2, by simpa using hm_hi⟩⟩
    have := hmap _ hz
    exact mem_Box.mpr ⟨initPt_mono (mem_Box.mp this).1, initPt_mono (mem_Box.mp this).2⟩

@[simp] lemma starOfSlice_val (hLOHI : LO ≤ HI)
    (hmono : MonotoneOn' g LO HI) (hmap : ∀ z ∈ Box LO HI, g z ∈ Box LO HI)
    (hm_lo : LO (Fin.last k) ≤ m) (hm_hi : m ≤ HI (Fin.last k)) (x : Pt k) :
    (starOfSlice hLOHI hmono hmap hm_lo hm_hi).val x = initPt (g (snocPt x m)) := rfl

@[simp] lemma starOfSlice_sgn (hLOHI : LO ≤ HI)
    (hmono : MonotoneOn' g LO HI) (hmap : ∀ z ∈ Box LO HI, g z ∈ Box LO HI)
    (hm_lo : LO (Fin.last k) ≤ m) (hm_hi : m ≤ HI (Fin.last k)) (x : Pt k) :
    (starOfSlice hLOHI hmono hmap hm_lo hm_hi).sgn x
      = decide (m ≤ g (snocPt x m) (Fin.last k)) := rfl

/-- **The Chen–Li reduction.**  A solution of the sliced `Tarski*` instance yields a
point `z` of the middle slice at which `g` goes weakly up or weakly down in *every*
coordinate — and hence, by `mapsTo_of_up` / `mapsTo_of_down`, a sub-box in which
the last dimension has been cut at `m` and which still contains a fixed point.

Repeating this `O(log n)` times shrinks the last dimension to a point, which is
why `Tarski(n,k+1)` costs at most `O(log n)` times `Tarski*(n,k)`. -/
theorem starOfSlice_sol_gives_halving (hLOHI : LO ≤ HI)
    (hmono : MonotoneOn' g LO HI) (hmap : ∀ z ∈ Box LO HI, g z ∈ Box LO HI)
    (hm_lo : LO (Fin.last k) ≤ m) (hm_hi : m ≤ HI (Fin.last k))
    {x : Pt k} (hsol : (starOfSlice hLOHI hmono hmap hm_lo hm_hi).IsStarSol x) :
    (snocPt x m ∈ Box LO HI) ∧
      ((snocPt x m ≤ g (snocPt x m) ∧
          ∀ w ∈ Box (snocPt x m) HI, g w ∈ Box (snocPt x m) HI) ∨
       (g (snocPt x m) ≤ snocPt x m ∧
          ∀ w ∈ Box LO (snocPt x m), g w ∈ Box LO (snocPt x m))) := by
  obtain ⟨hx, hcase⟩ := hsol
  have hz : snocPt x m ∈ Box LO HI := mem_Box.mpr
    ⟨le_iff_init_last.mpr ⟨by simpa using (mem_Box.mp hx).1, by simpa using hm_lo⟩,
     le_iff_init_last.mpr ⟨by simpa using (mem_Box.mp hx).2, by simpa using hm_hi⟩⟩
  refine ⟨hz, ?_⟩
  rcases hcase with ⟨hup, hsgn⟩ | ⟨hdown, hsgn⟩
  · -- `val x ≥ x` and the sign is `+1`: `g` goes up in all `k+1` coordinates.
    have hlast : m ≤ g (snocPt x m) (Fin.last k) := by
      simpa using hsgn
    have hzu : snocPt x m ≤ g (snocPt x m) := by
      refine le_iff_init_last.mpr ⟨?_, by simpa using hlast⟩
      simpa using hup
    exact Or.inl ⟨hzu, mapsTo_of_up hmono hmap hz hzu⟩
  · -- `val x ≤ x` and the sign is `-1`: `g` goes down in all `k+1` coordinates.
    have hlast : g (snocPt x m) (Fin.last k) < m := by
      have : ¬ (m ≤ g (snocPt x m) (Fin.last k)) := by simpa using hsgn
      omega
    have hzd : g (snocPt x m) ≤ snocPt x m := by
      refine le_iff_init_last.mpr ⟨?_, by simpa using hlast.le⟩
      simpa using hdown
    exact Or.inr ⟨hzd, mapsTo_of_down hmono hmap hz hzd⟩

end Reduction

/-! ### The results of the recent literature, as statements

These two are stated but not proved.  They are given as `Prop`s, rather than as
`theorem`s closed by `sorry`, so that nothing here claims a proof it lacks. -/

/-- **CLY26 Theorem 1.**  There is an `O(log n)`-query algorithm for
`Tarski*(n,3)`: a family of query algorithms, one per grid width, and a constant
`C` with query count at most `C · (log₂ n + 1)`, correct on every `Tarski*`
instance over `[0,n]³`.

Combined with `StarDecompositionTheorem` this gives `O(log^⌈k/3⌉ n)` for
`Tarski*(n,k)`, and via the Chen–Li reduction (`starOfSlice_sol_gives_halving`)
the bound `O(log^(⌈(k-1)/3⌉+1) n)` for `Tarski(n,k)` — CLY26's Corollary 1. -/
def Tarski3StarInLogQueries : Prop :=
  ∃ (A : ℕ → QueryAlg (Pt 3) (Pt 3 × Bool) (Pt 3)) (C : ℕ),
    ∀ n : ℕ, ∀ T : StarInstance 3 0 (fun _ => n),
      T.IsStarSol ((A n).run (fun x => (T.val x, T.sgn x)))
        ∧ QueryAlg.Bounded (C * (Nat.log 2 n + 1)) (A n)

/-- **Chen–Li's decomposition theorem for `Tarski*`.**  The query complexity of
`Tarski*(n, a+b)` is bounded, up to a constant, by the product of those of
`Tarski*(n,a)` and `Tarski*(n,b)`.

This is the `Tarski*` analogue of Fearnley–Pálvölgyi–Savani's Theorem 18, which
*is* proved here — see `decompAlg_isSol` and `decompAlg_bounded` in
`Tfnp/Tarski/Decomposition.lean`.  Stating it in the same style as the FPS theorem
would require porting `SolvesMapsTo`/`SolvesUpDown` to the `Tarski*` output type;
we record only the shape of the claim. -/
def StarDecompositionTheorem : Prop :=
  ∀ a b : ℕ, ∃ C : ℕ, ∀ qa qb : ℕ,
    (∃ _A : QueryAlg (Pt a) (Pt a × Bool) (Pt a), QueryAlg.Bounded qa _A) →
    (∃ _B : QueryAlg (Pt b) (Pt b × Bool) (Pt b), QueryAlg.Bounded qb _B) →
    ∃ _L : QueryAlg (Pt (a + b)) (Pt (a + b) × Bool) (Pt (a + b)),
      QueryAlg.Bounded (C * qa * qb) _L

end Tfnp.Tarski
