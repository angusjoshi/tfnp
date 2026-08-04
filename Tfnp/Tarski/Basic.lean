/-
Copyright (c) 2026 Angus Joshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Angus Joshi
-/
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Linarith
import Tfnp.QueryModel

/-!
# The Tarski fixed-point search problem, à la Fearnley–Pálvölgyi–Savani

This file sets up the version of the Tarski problem used by

> John Fearnley, Dömötör Pálvölgyi, Rahul Savani.
> *A faster algorithm for finding Tarski fixed points.*
> ACM Trans. Algorithms 2022, [arXiv:2010.02618](https://arxiv.org/abs/2010.02618)

and by the follow-up literature (Chen–Li, Chen–Li–Yannakakis).  The essential
difference from `Tfnp/Tarski.lean` is that **monotonicity is not a hypothesis**:
an instance is an arbitrary `f`, and a *solution* is either a fixed point or a
witnessed violation of order preservation (FPS Definition 2):

* `(T1)` a point `x` with `f x = x`;
* `(T2)` two points `x ≼ y` with `f x ⋠ f y`.

By Tarski's theorem an instance with no `(T2)` solution has a `(T1)` solution,
so the problem is total.  Carrying `(T2)` explicitly is *not* a technicality: the
FPS decomposition theorem (`Tfnp/Tarski/Decomposition.lean`) runs an algorithm
against a *simulated* oracle which is not monotone even when the real one is, so
the sub-algorithms must be allowed to report violations.

## Main definitions

* `Pt k` — a point of the integer grid `ℕ^k`, ordered componentwise.
  We work over all of `ℕ^k` and confine attention to a *box* `Box lo hi`
  (`Set.Icc`), which is FPS's sub-instance `L_{lo,hi}`.
* `Up f`, `Down f` — the up and down sets, `{x | x ≤ f x}` and `{x | f x ≤ x}`.
  Their intersection is the set of fixed points (`up_inter_down`).
* `Answer k` and `IsSol f lo hi` — the solution type and its correctness
  predicate, i.e. `(T1)`/`(T2)` relativised to a box.

## Main results

* `up_step` — FPS Lemma 21: from `x ∈ Up f` with `x i < f x i`, the point
  `x + e i` is again in `Up f` unless it witnesses a violation with `x`.
* `exists_sol_of_up_down` — **FPS Lemma 4**: if `a ≤ b` with `a ∈ Up f` and
  `b ∈ Down f`, then the box `Box a b` contains a solution.  This is the engine
  of every FPS argument, and needs no monotonicity whatsoever.
* `intervalAlg` and `intervalAlg_isSol`, `intervalAlg_queries_le` — the
  algorithmic form of Lemma 4: a `QueryAlg` finding such a solution in at most
  `boxSize a b + 1` queries, where `boxSize a b = ∑ i, (b i - a i)`.
-/

namespace Tfnp.Tarski

/-- A point of the `k`-dimensional integer grid, ordered componentwise.

We deliberately use all of `ℕ^k` rather than a bounded `Fin (n+1)^k`: FPS's
algorithms all operate on a *box* `Box lo hi` inside an ambient lattice, and the
running points may be compared with, or momentarily step outside, that box.
Bounded side lengths are recovered by taking `lo = 0` and `hi = fun _ => n`. -/
abbrev Pt (k : ℕ) : Type := Fin k → ℕ

variable {k : ℕ}

/-! ### Coordinatewise access

`Pt k` carries the `Pi` order, so `x ≤ y` unfolds to `∀ i, x i ≤ y i` — but the
`Nat` order instance appearing there is `(fun _ => instLENat) i`, which is not
*syntactically* `instLENat`.  `omega` and `linarith` match on the instance, so
applying an order hypothesis directly (`h i`) yields a hypothesis they silently
ignore.  Everything below goes through these two lemmas instead, whose stated
types pin the plain `Nat` instances. -/

/-- Project `x ≤ y` to a coordinate, with the plain `Nat` order instance. -/
lemma le_coord {x y : Pt k} (h : x ≤ y) (i : Fin k) : x i ≤ y i := h i

/-- Coordinatewise comparison implies comparison. -/
lemma coord_le {x y : Pt k} (h : ∀ i, x i ≤ y i) : x ≤ y := h

/-- A failure of `≤` is a strict failure in some coordinate. -/
lemma exists_lt_of_not_le {x y : Pt k} (h : ¬ x ≤ y) : ∃ i, y i < x i := by
  by_contra hc
  push Not at hc
  exact h (coord_le fun i => hc i)

/-- Comparison of grid points is decidable — the `Pi` order does not come with a
`Decidable` instance, but the index type is a `Fintype`. -/
instance instDecidableLePt (x y : Pt k) : Decidable (x ≤ y) :=
  decidable_of_iff (∀ i, x i ≤ y i) ⟨coord_le, fun h i => le_coord h i⟩

/-! ### Boxes -/

/-- FPS's sub-instance `L_{lo,hi} = {x | lo ≼ x ≼ hi}`. -/
def Box (lo hi : Pt k) : Set (Pt k) := Set.Icc lo hi

lemma mem_Box {lo hi x : Pt k} : x ∈ Box lo hi ↔ lo ≤ x ∧ x ≤ hi := Set.mem_Icc

lemma mem_Box_self_left {lo hi : Pt k} (h : lo ≤ hi) : lo ∈ Box lo hi :=
  mem_Box.mpr ⟨le_rfl, h⟩

lemma mem_Box_self_right {lo hi : Pt k} (h : lo ≤ hi) : hi ∈ Box lo hi :=
  mem_Box.mpr ⟨h, le_rfl⟩

/-- Boxes are monotone in their endpoints: shrinking a box keeps you inside the
bigger one. -/
lemma Box_subset {lo hi lo' hi' : Pt k} (hl : lo ≤ lo') (hh : hi' ≤ hi) :
    Box lo' hi' ⊆ Box lo hi := fun _ hx =>
  mem_Box.mpr ⟨hl.trans (mem_Box.mp hx).1, (mem_Box.mp hx).2.trans hh⟩

/-- `boxSize lo hi = ∑ i, (hi i - lo i)`, the `ℓ¹` diameter of the box.  This is
the termination measure for FPS's Lemma 4 walk. -/
def boxSize (lo hi : Pt k) : ℕ := ∑ i, (hi i - lo i)

lemma boxSize_eq_zero_iff {lo hi : Pt k} (h : lo ≤ hi) :
    boxSize lo hi = 0 ↔ lo = hi := by
  unfold boxSize
  refine ⟨fun hs => funext fun i => ?_, fun hs => by simp [hs]⟩
  have h1 := (Finset.sum_eq_zero_iff (s := (Finset.univ : Finset (Fin k)))
    (f := fun i => hi i - lo i)).mp hs i (Finset.mem_univ i)
  have h2 : lo i ≤ hi i := le_coord h i
  omega

/-! ### The up and down sets -/

/-- FPS's up set `Up(f) = {x | x ≼ f x}`. -/
def Up (f : Pt k → Pt k) : Set (Pt k) := {x | x ≤ f x}

/-- FPS's down set `Down(f) = {x | f x ≼ x}`. -/
def Down (f : Pt k → Pt k) : Set (Pt k) := {x | f x ≤ x}

@[simp] lemma mem_Up {f : Pt k → Pt k} {x : Pt k} : x ∈ Up f ↔ x ≤ f x := Iff.rfl
@[simp] lemma mem_Down {f : Pt k → Pt k} {x : Pt k} : x ∈ Down f ↔ f x ≤ x := Iff.rfl

/-- The fixed points of `f` are exactly `Up f ∩ Down f`. -/
lemma up_inter_down (f : Pt k → Pt k) :
    Up f ∩ Down f = {x | f x = x} := by
  ext x
  exact ⟨fun h => le_antisymm h.2 h.1, fun h => ⟨h.ge, h.le⟩⟩

/-! ### Solutions -/

/-- `(T2)`: the pair `(x, y)` witnesses a violation of order preservation. -/
def IsVop (f : Pt k → Pt k) (x y : Pt k) : Prop := x ≤ y ∧ ¬ f x ≤ f y

/-- A violation in one coordinate is a violation. -/
lemma isVop_of_coord {f : Pt k → Pt k} {x y : Pt k} (hxy : x ≤ y) (i : Fin k)
    (hi : f y i < f x i) : IsVop f x y := by
  refine ⟨hxy, fun h => ?_⟩
  have := le_coord h i
  omega

/-- An answer returned by a Tarski algorithm: either a candidate fixed point
(`(T1)`) or a candidate violating pair (`(T2)`). -/
abbrev Answer (k : ℕ) : Type := Pt k ⊕ (Pt k × Pt k)

/-- `IsSol f lo hi ans` says `ans` really is a solution of the Tarski instance
`f` restricted to the box `Box lo hi`, in the sense of FPS Definition 2. -/
def IsSol (f : Pt k → Pt k) (lo hi : Pt k) : Answer k → Prop
  | .inl x => x ∈ Box lo hi ∧ f x = x
  | .inr (x, y) => x ∈ Box lo hi ∧ y ∈ Box lo hi ∧ IsVop f x y

/-- A solution of a sub-box is a solution of the ambient box. -/
lemma IsSol.mono {f : Pt k → Pt k} {lo hi lo' hi' : Pt k} (hl : lo ≤ lo') (hh : hi' ≤ hi)
    {ans : Answer k} (h : IsSol f lo' hi' ans) : IsSol f lo hi ans := by
  cases ans with
  | inl x => exact ⟨Box_subset hl hh h.1, h.2⟩
  | inr p => exact ⟨Box_subset hl hh h.1, Box_subset hl hh h.2.1, h.2.2⟩

/-! ### The unit step (FPS Lemma 21) -/

/-- `succAt x i` is FPS's `x + e_i`. -/
def succAt (x : Pt k) (i : Fin k) : Pt k := Function.update x i (x i + 1)

@[simp] lemma succAt_self (x : Pt k) (i : Fin k) : succAt x i i = x i + 1 := by
  simp [succAt]

lemma succAt_of_ne (x : Pt k) {i j : Fin k} (h : j ≠ i) : succAt x i j = x j := by
  simp [succAt, h]

lemma le_succAt (x : Pt k) (i : Fin k) : x ≤ succAt x i := by
  intro j
  by_cases h : j = i
  · subst h; simp
  · simp [succAt_of_ne x h]

lemma succAt_le {x y : Pt k} {i : Fin k} (hxy : x ≤ y) (hi : x i < y i) : succAt x i ≤ y := by
  intro j
  by_cases h : j = i
  · subst h; simpa using hi
  · simpa [succAt_of_ne x h] using hxy j

lemma boxSize_succAt {x b : Pt k} {i : Fin k} (hi : x i < b i) :
    boxSize (succAt x i) b + 1 = boxSize x b := by
  unfold boxSize
  have key : ∀ g : Fin k → ℕ, ∑ j, g j = g i + ∑ j ∈ (Finset.univ : Finset (Fin k)).erase i, g j :=
    fun g => (Finset.add_sum_erase _ g (Finset.mem_univ i)).symm
  rw [key (fun j => b j - succAt x i j), key (fun j => b j - x j)]
  have hcong : ∑ j ∈ (Finset.univ : Finset (Fin k)).erase i, (b j - succAt x i j)
      = ∑ j ∈ (Finset.univ : Finset (Fin k)).erase i, (b j - x j) :=
    Finset.sum_congr rfl fun j hj => by rw [succAt_of_ne x (Finset.ne_of_mem_erase hj)]
  rw [hcong, succAt_self]
  omega

/-- **FPS Lemma 21.** If `x` is in the up set and `f` strictly increases `x` in
coordinate `i`, then either `x` and `x + e_i` witness a violation of order
preservation, or `x + e_i` is again in the up set.

Stated contrapositively (which is the form the algorithm needs): if `x + e_i`
leaves the up set, the pair `(x, x + e_i)` is a violation. -/
lemma up_step {f : Pt k → Pt k} {x : Pt k} (hx : x ∈ Up f) {i : Fin k} (hi : x i < f x i) :
    succAt x i ∉ Up f → IsVop f x (succAt x i) := by
  intro hbad
  obtain ⟨j, hj⟩ : ∃ j, f (succAt x i) j < succAt x i j :=
    exists_lt_of_not_le hbad
  refine isVop_of_coord (le_succAt x i) j ?_
  by_cases h : j = i
  · subst h
    rw [succAt_self] at hj
    omega
  · rw [succAt_of_ne x h] at hj
    exact lt_of_lt_of_le hj (le_coord hx j)

/-! ### FPS Lemma 4

If `a ≼ b` with `a` in the up set and `b` in the down set, the box `Box a b`
contains a solution.  The proof walks up from `a`, one coordinate at a time,
using `up_step`; the walk either reaches a fixed point, leaves the up set (a
violation with the previous point), or bumps into the boundary of the box in some
coordinate `i` — in which case `f b i ≤ b i = a i < f a i` gives a violation
between the current point and `b`. -/

/-- **FPS Lemma 4** (existence form).  No monotonicity is assumed. -/
theorem exists_sol_of_up_down {f : Pt k → Pt k} {a b : Pt k}
    (hab : a ≤ b) (ha : a ∈ Up f) (hb : b ∈ Down f) :
    ∃ ans : Answer k, IsSol f a b ans := by
  -- Strong induction on the ℓ¹ diameter, generalising the left endpoint.
  suffices H : ∀ n (a' : Pt k), boxSize a' b ≤ n → a ≤ a' → a' ≤ b → a' ∈ Up f →
      ∃ ans : Answer k, IsSol f a b ans by
    exact H (boxSize a b) a le_rfl le_rfl hab ha
  intro n
  induction n with
  | zero =>
    intro a' hsize haa' ha'b ha'
    -- `boxSize a' b = 0` forces `a' = b`, and then `f a' ≤ a' ≤ f a'`.
    have ha'eq : a' = b := (boxSize_eq_zero_iff ha'b).mp (Nat.le_zero.mp hsize)
    refine ⟨.inl a', mem_Box.mpr ⟨haa', ha'b⟩, le_antisymm ?_ ha'⟩
    rw [ha'eq]; exact hb
  | succ n ih =>
    intro a' hsize haa' ha'b ha'
    by_cases hfix : ∃ i, a' i < f a' i
    · obtain ⟨i, hi⟩ := hfix
      by_cases hbnd : b i ≤ a' i
      · -- The walk has reached the boundary in coordinate `i`: violation with `b`.
        refine ⟨.inr (a', b), mem_Box.mpr ⟨haa', ha'b⟩, mem_Box.mpr ⟨haa'.trans ha'b, le_rfl⟩,
          isVop_of_coord ha'b i ?_⟩
        have h1 : f b i ≤ b i := le_coord hb i
        have h2 : b i = a' i := Nat.le_antisymm hbnd (le_coord ha'b i)
        omega
      · -- Step to `a' + e_i`.
        push Not at hbnd
        by_cases hup : succAt a' i ∈ Up f
        · refine ih (succAt a' i) ?_ (haa'.trans (le_succAt a' i)) (succAt_le ha'b hbnd) hup
          have := boxSize_succAt (b := b) hbnd
          omega
        · exact ⟨.inr (a', succAt a' i),
            mem_Box.mpr ⟨haa', ha'b⟩,
            mem_Box.mpr ⟨haa'.trans (le_succAt a' i), succAt_le ha'b hbnd⟩,
            up_step ha' hi hup⟩
    · -- No coordinate strictly increases, so `a'` is a fixed point.
      push Not at hfix
      exact ⟨.inl a', mem_Box.mpr ⟨haa', ha'b⟩,
        funext fun i => le_antisymm (hfix i) (ha' i)⟩

/-- Specialisation of `exists_sol_of_up_down` to the whole ambient box: a Tarski
instance on a box that `f` maps into itself always has a solution.  (Totality of
the Tarski search problem.) -/
theorem exists_sol_of_mapsTo {f : Pt k → Pt k} {lo hi : Pt k} (h : lo ≤ hi)
    (hmap : ∀ x ∈ Box lo hi, f x ∈ Box lo hi) :
    ∃ ans : Answer k, IsSol f lo hi ans :=
  exists_sol_of_up_down h
    (mem_Up.mpr (mem_Box.mp (hmap lo (mem_Box_self_left h))).1)
    (mem_Down.mpr (mem_Box.mp (hmap hi (mem_Box_self_right h))).2)

/-! ### The algorithmic form of Lemma 4

`intervalAlg b n prev a` runs the walk of `exists_sol_of_up_down` as a query
algorithm.  The extra parameter `prev` is the previous point of the walk: it is
needed because if the current point `a` turns out to leave the up set, the
violation to report is `(prev, a)`.

The invariant carried by `intervalAlg_isSol` is exactly what `up_step` supplies:
`¬ (a ∈ Up f) → IsVop f prev a`. -/

open Classical in
/-- The walk of FPS Lemma 4 as a query algorithm.  `b` is the (fixed) upper
endpoint, `n` a query budget, `prev` the previous point and `a` the current one. -/
noncomputable def intervalAlg (b : Pt k) : ℕ → Pt k → Pt k → QueryAlg (Pt k) (Pt k) (Answer k)
  | 0, _, a => .pure (.inl a)
  | n + 1, prev, a =>
      QueryAlg.ask a >>= fun fa =>
        if ¬ a ≤ fa then .pure (.inr (prev, a))
        else if h : ∃ i, a i < fa i then
          if b h.choose ≤ a h.choose then .pure (.inr (a, b))
          else intervalAlg b n a (succAt a h.choose)
        else .pure (.inl a)

/-- `intervalAlg` makes at most `n` queries, whatever the oracle. -/
lemma intervalAlg_queries_le (b : Pt k) :
    ∀ (n : ℕ) (prev a : Pt k) (f : Pt k → Pt k), (intervalAlg b n prev a).queries f ≤ n := by
  intro n
  induction n with
  | zero => intro prev a f; exact le_rfl
  | succ n ih =>
    intro prev a f
    change (QueryAlg.ask a >>= _).queries f ≤ n + 1
    rw [QueryAlg.queries_bind, QueryAlg.queries_ask, QueryAlg.run_ask]
    by_cases h0 : ¬ a ≤ f a
    · simp only [if_pos h0]; simp [QueryAlg.queries]
    · rw [if_neg h0]
      by_cases h : ∃ i, a i < f a i
      · rw [dif_pos h]
        by_cases hb : b h.choose ≤ a h.choose
        · simp only [if_pos hb]; simp [QueryAlg.queries]
        · rw [if_neg hb]
          have := ih a (succAt a h.choose) f
          omega
      · rw [dif_neg h]; simp [QueryAlg.queries]

/-- **Correctness of `intervalAlg`.**  The hypotheses are the loop invariant:
`prev` and `a` lie in the box, `prev ≤ a`, `b` is in the down set, and if `a`
should turn out to leave the up set then `(prev, a)` is a violation — which is
exactly what `up_step` guarantees after each step. -/
lemma intervalAlg_isSol (f : Pt k → Pt k) {lo b : Pt k} (hb : b ∈ Down f) :
    ∀ (n : ℕ) (prev a : Pt k), boxSize a b < n → lo ≤ prev → prev ≤ a → a ≤ b →
      (a ∉ Up f → IsVop f prev a) →
      IsSol f lo b ((intervalAlg b n prev a).run f) := by
  intro n
  induction n with
  | zero => intro _ _ h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro prev a hsize hlo hpa hab hinv
    have hloa : lo ≤ a := hlo.trans hpa
    change IsSol f lo b ((QueryAlg.ask a >>= _).run f)
    rw [QueryAlg.run_bind, QueryAlg.run_ask]
    by_cases h0 : ¬ a ≤ f a
    · -- `a` left the up set: report `(prev, a)`.
      rw [if_pos h0]
      exact ⟨mem_Box.mpr ⟨hlo, hpa.trans hab⟩, mem_Box.mpr ⟨hloa, hab⟩, hinv h0⟩
    · rw [if_neg h0]
      push Not at h0
      have hup : a ∈ Up f := h0
      by_cases h : ∃ i, a i < f a i
      · rw [dif_pos h]
        set i := h.choose with hi_def
        have hi : a i < f a i := h.choose_spec
        by_cases hbnd : b i ≤ a i
        · -- Boundary in coordinate `i`: violation with `b`.
          rw [if_pos hbnd]
          refine ⟨mem_Box.mpr ⟨hloa, hab⟩, mem_Box.mpr ⟨hloa.trans hab, le_rfl⟩,
            isVop_of_coord hab i ?_⟩
          have h1 : f b i ≤ b i := le_coord hb i
          have h2 : b i = a i := Nat.le_antisymm hbnd (le_coord hab i)
          omega
        · -- Step to `a + e_i`, re-establishing the invariant by `up_step`.
          rw [if_neg hbnd]
          push Not at hbnd
          refine ih a (succAt a i) ?_ hloa (le_succAt a i) (succAt_le hab hbnd)
            (fun hnot => up_step hup hi hnot)
          have := boxSize_succAt (b := b) hbnd
          omega
      · -- `a` is a fixed point.
        rw [dif_neg h]
        push Not at h
        exact ⟨mem_Box.mpr ⟨hloa, hab⟩, funext fun j => le_antisymm (h j) (hup j)⟩

/-- The interval algorithm on the box `Box a b`, with its own budget. -/
noncomputable def intervalAlgorithm (a b : Pt k) : QueryAlg (Pt k) (Pt k) (Answer k) :=
  intervalAlg b (boxSize a b + 1) a a

/-- **FPS Lemma 4** (algorithmic form).  Given `a ∈ Up f`, `b ∈ Down f` and
`a ≤ b`, the algorithm `intervalAlgorithm a b` returns a solution in the box
`Box a b`. -/
theorem intervalAlgorithm_isSol {f : Pt k → Pt k} {a b : Pt k}
    (hab : a ≤ b) (ha : a ∈ Up f) (hb : b ∈ Down f) :
    IsSol f a b ((intervalAlgorithm a b).run f) :=
  intervalAlg_isSol f hb _ a a (Nat.lt_succ_self _) le_rfl le_rfl hab
    (fun hnot => absurd ha hnot)

/-- The interval algorithm makes at most `boxSize a b + 1` queries. -/
theorem intervalAlgorithm_queries_le (a b : Pt k) (f : Pt k → Pt k) :
    (intervalAlgorithm a b).queries f ≤ boxSize a b + 1 :=
  intervalAlg_queries_le b _ a a f

end Tfnp.Tarski
