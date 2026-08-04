/-
Copyright (c) 2026 Angus Joshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Angus Joshi
-/
import Tfnp.Tarski.Outer

/-!
# The Fearnley–Pálvölgyi–Savani inner algorithm: witnesses and their lemmas

FPS Section 4, the technical heart of their `O(log² n)` algorithm for
three-dimensional Tarski.  This file formalises the structural results the inner
algorithm rests on — FPS Definitions 6, 8, 10 and Lemmas 7, 9, 11, 12 — all fully
proved.

Throughout, the ambient instance is `k`-dimensional but the arguments only ever
use three distinguished coordinates: two *free* ones `i ≠ j` and one *frozen* one
`c`.  The hypothesis `Covers i j c` says these are all the coordinates, which is
FPS's `k = 3`.  Keeping `i`, `j` as parameters rather than fixing them to `1`, `2`
is exactly FPS's remark that "the formal definition of a down set witness
abstracts over dimensions 1 and 2": their top-boundary and right-boundary
witnesses are the two instantiations, and each lemma is proved once for both.

## Main results

* `exists_solOn` — FPS Lemma 4 relativised to a set `S` of free coordinates: from
  a point that goes up on `S` and one above it that goes down on `S`, one finds
  either a point fixed on all of `S` (and unchanged off `S`), or a violation.
  With `S = univ` this is `exists_sol_of_up_down`; the inner-algorithm lemmas use
  it with `S` a singleton (Lemmas 7 and 9) and a pair (Lemma 11).
* `HasInnerSol` — FPS Definition 3's guarantee, as a proposition about a box.
* `DownWitness`, `UpWitness` — FPS Definitions 6 and 8.
* `downWitness_dichotomy` — **FPS Lemma 7**.
* `upWitness_dichotomy` — **FPS Lemma 9**.
* `InnerInv` — FPS Definition 10, the inner algorithm invariant.
* `hasInnerSol_of_slice_updown` — the engine of FPS Lemma 11.
* `hasInnerSol_of_innerInv` — **FPS Lemma 11**: the invariant guarantees the box
  contains something the inner algorithm may return.  This is what makes the
  halving loop of the inner algorithm sound.
* `hasInnerSol_of_escape_upper`, `hasInnerSol_of_escape_lower` — **FPS Lemma 12**,
  the special case where `f` pushes a boundary point out of the box.  FPS's four
  cases are these two lemmas, each instantiated at the two free dimensions.
-/

namespace Tfnp.Tarski

variable {k : ℕ}

/-! ### FPS Lemma 4 on a set of free coordinates -/

/-- The unit step of `exists_solOn`: `up_step` relativised to a coordinate set. -/
lemma upOn_step {f : Pt k → Pt k} {S : Finset (Fin k)} {x : Pt k}
    (hx : ∀ l ∈ S, x l ≤ f x l) {i : Fin k} (hiS : i ∈ S) (hi : x i < f x i) :
    (¬ ∀ l ∈ S, succAt x i l ≤ f (succAt x i) l) → IsVop f x (succAt x i) := by
  intro hbad
  push Not at hbad
  obtain ⟨l, hlS, hl⟩ := hbad
  refine isVop_of_coord (le_succAt x i) l ?_
  by_cases h : l = i
  · subst h
    rw [succAt_self] at hl
    omega
  · rw [succAt_of_ne x h] at hl
    exact lt_of_lt_of_le hl (hx l hlS)

/-- **FPS Lemma 4, relativised to a coordinate set.**  If `a ≤ b`, and `f` weakly
increases `a` on `S` and weakly decreases `b` on `S`, then the box `[a, b]`
contains either a point fixed by `f` on all of `S` (and agreeing with `a` off
`S`), or a violation of order preservation.

Taking `S = Finset.univ` recovers `exists_sol_of_up_down`.  The inner-algorithm
lemmas below use `S` of size one and two: a one-dimensional slice of a
three-dimensional instance, and a two-dimensional one. -/
theorem exists_solOn (S : Finset (Fin k)) (f : Pt k → Pt k) {a b : Pt k}
    (hab : a ≤ b) (ha : ∀ l ∈ S, a l ≤ f a l) (hb : ∀ l ∈ S, f b l ≤ b l) :
    (∃ p, p ∈ Box a b ∧ (∀ l ∈ S, f p l = p l) ∧ ∀ l ∉ S, p l = a l)
      ∨ (∃ x y, x ∈ Box a b ∧ y ∈ Box a b ∧ IsVop f x y) := by
  suffices H : ∀ n (a' : Pt k), boxSize a' b ≤ n → a ≤ a' → a' ≤ b →
      (∀ l ∈ S, a' l ≤ f a' l) → (∀ l ∉ S, a' l = a l) →
      (∃ p, p ∈ Box a b ∧ (∀ l ∈ S, f p l = p l) ∧ ∀ l ∉ S, p l = a l)
        ∨ (∃ x y, x ∈ Box a b ∧ y ∈ Box a b ∧ IsVop f x y) by
    exact H (boxSize a b) a le_rfl le_rfl hab ha (fun _ _ => rfl)
  intro n
  induction n with
  | zero =>
    intro a' hsize haa' ha'b ha' hoff
    -- `boxSize a' b = 0` forces `a' = b`, so `f` both increases and decreases on `S`.
    have ha'eq : a' = b := (boxSize_eq_zero_iff ha'b).mp (Nat.le_zero.mp hsize)
    refine Or.inl ⟨a', mem_Box.mpr ⟨haa', ha'b⟩, fun l hlS => ?_, hoff⟩
    have h1 : f a' l ≤ a' l := by rw [ha'eq]; exact hb l hlS
    exact Nat.le_antisymm h1 (ha' l hlS)
  | succ n ih =>
    intro a' hsize haa' ha'b ha' hoff
    by_cases hstep : ∃ i ∈ S, a' i < f a' i
    · obtain ⟨i, hiS, hi⟩ := hstep
      by_cases hbnd : b i ≤ a' i
      · -- The walk hit the boundary in a free coordinate: violation with `b`.
        refine Or.inr ⟨a', b, mem_Box.mpr ⟨haa', ha'b⟩,
          mem_Box.mpr ⟨haa'.trans ha'b, le_rfl⟩, isVop_of_coord ha'b i ?_⟩
        have h1 : f b i ≤ b i := hb i hiS
        have h2 : b i = a' i := Nat.le_antisymm hbnd (le_coord ha'b i)
        omega
      · push Not at hbnd
        by_cases hup : ∀ l ∈ S, succAt a' i l ≤ f (succAt a' i) l
        · refine ih (succAt a' i) ?_ (haa'.trans (le_succAt a' i)) (succAt_le ha'b hbnd) hup ?_
          · have := boxSize_succAt (b := b) hbnd
            omega
          · intro l hlS
            have hne : l ≠ i := fun h => hlS (h ▸ hiS)
            rw [succAt_of_ne a' hne]
            exact hoff l hlS
        · exact Or.inr ⟨a', succAt a' i, mem_Box.mpr ⟨haa', ha'b⟩,
            mem_Box.mpr ⟨haa'.trans (le_succAt a' i), succAt_le ha'b hbnd⟩,
            upOn_step ha' hiS hi hup⟩
    · -- No free coordinate strictly increases: `a'` is fixed on `S`.
      push Not at hstep
      refine Or.inl ⟨a', mem_Box.mpr ⟨haa', ha'b⟩, fun l hlS => ?_, hoff⟩
      exact Nat.le_antisymm (hstep l hlS) (ha' l hlS)

/-! ### The three distinguished coordinates -/

/-- `Covers i j c`: the coordinates `i`, `j`, `c` are distinct and exhaust the
ambient dimensions.  This is FPS's three-dimensional setting, with `i` and `j` the
free dimensions of the principal slice and `c` the frozen one; leaving `i`, `j` as
parameters is what lets a single proof cover both of FPS's boundary cases. -/
structure Covers (i j c : Fin k) : Prop where
  /-- The two free coordinates are distinct. -/
  ij : i ≠ j
  /-- The first free coordinate differs from the frozen one. -/
  ic : i ≠ c
  /-- The second free coordinate differs from the frozen one. -/
  jc : j ≠ c
  /-- There are no other coordinates. -/
  cover : ∀ l : Fin k, l = i ∨ l = j ∨ l = c

/-- Membership in `Up f` reduces to the three coordinates. -/
lemma mem_Up_of_three {f : Pt k → Pt k} {i j c : Fin k} (hcov : Covers i j c) {x : Pt k}
    (hi : x i ≤ f x i) (hj : x j ≤ f x j) (hc : x c ≤ f x c) : x ∈ Up f := by
  refine mem_Up.mpr (coord_le fun l => ?_)
  rcases hcov.cover l with rfl | rfl | rfl <;> assumption

/-- Membership in `Down f` reduces to the three coordinates. -/
lemma mem_Down_of_three {f : Pt k → Pt k} {i j c : Fin k} (hcov : Covers i j c) {x : Pt k}
    (hi : f x i ≤ x i) (hj : f x j ≤ x j) (hc : f x c ≤ x c) : x ∈ Down f := by
  refine mem_Down.mpr (coord_le fun l => ?_)
  rcases hcov.cover l with rfl | rfl | rfl <;> assumption

/-- Comparison reduces to the three coordinates. -/
lemma le_of_three {i j c : Fin k} (hcov : Covers i j c) {x y : Pt k}
    (hi : x i ≤ y i) (hj : x j ≤ y j) (hc : x c ≤ y c) : x ≤ y := by
  refine coord_le fun l => ?_
  rcases hcov.cover l with rfl | rfl | rfl <;> assumption

/-! ### What the inner algorithm may return -/

/-- `HasInnerSol f a b`: the box `[a, b]` contains something an inner algorithm is
allowed to return (FPS Definition 3) — a point of `Up f ∪ Down f`, or a pair
witnessing a violation of order preservation.

Note that the point is *not* required to be in a slice: when `a` and `b` already
lie in a common principal slice, every point of `[a, b]` does too. -/
def HasInnerSol (f : Pt k → Pt k) (a b : Pt k) : Prop :=
  (∃ p, p ∈ Box a b ∧ (p ∈ Up f ∨ p ∈ Down f))
    ∨ (∃ u v, u ∈ Box a b ∧ v ∈ Box a b ∧ IsVop f u v)

lemma HasInnerSol.mono {f : Pt k → Pt k} {a b x y : Pt k} (hax : a ≤ x) (hyb : y ≤ b)
    (h : HasInnerSol f x y) : HasInnerSol f a b := by
  rcases h with ⟨p, hp, hpd⟩ | ⟨u, v, hu, hv, hvop⟩
  · exact Or.inl ⟨p, Box_subset hax hyb hp, hpd⟩
  · exact Or.inr ⟨u, v, Box_subset hax hyb hu, Box_subset hax hyb hv, hvop⟩

/-- A point that goes up in both free dimensions — FPS's `Up(f_s)` for the
principal slice `s` frozen at `c`. -/
def UpSlice (f : Pt k → Pt k) (i j : Fin k) (x : Pt k) : Prop := x i ≤ f x i ∧ x j ≤ f x j

/-- A point that goes down in both free dimensions — FPS's `Down(f_s)`. -/
def DownSlice (f : Pt k → Pt k) (i j : Fin k) (x : Pt k) : Prop := f x i ≤ x i ∧ f x j ≤ x j

/-! ### Witnesses (FPS Definitions 6 and 8) -/

/-- **FPS Definition 6** (down set witness), for the slice frozen at coordinate
`c` with free coordinates `i` (in which `d` and `b` agree) and `j` (in which they
point towards each other).

FPS's *top-boundary* witness is the instantiation where `i` is dimension 2, and
their *right-boundary* witness the one where `i` is dimension 1. -/
structure DownWitness (f : Pt k → Pt k) (i j c : Fin k) (d b : Pt k) : Prop where
  /-- `f` weakly increases `d` in the frozen dimension. -/
  d_c : d c ≤ f d c
  /-- `f` weakly increases `b` in the frozen dimension. -/
  b_c : b c ≤ f b c
  /-- Both lie in the same slice. -/
  same_c : d c = b c
  /-- They agree in the free dimension `i`. -/
  same_i : d i = b i
  /-- `d` lies below `b` in the free dimension `j`. -/
  le_j : d j ≤ b j
  /-- `f` weakly increases `d` in dimension `j`. -/
  up_j : d j ≤ f d j
  /-- `f` weakly decreases `b` in dimension `j`. -/
  down_j : f b j ≤ b j

/-- **FPS Definition 8** (up set witness): a down set witness with all
inequalities flipped. -/
structure UpWitness (f : Pt k → Pt k) (i j c : Fin k) (a u : Pt k) : Prop where
  /-- `f` weakly decreases `a` in the frozen dimension. -/
  a_c : f a c ≤ a c
  /-- `f` weakly decreases `u` in the frozen dimension. -/
  u_c : f u c ≤ u c
  /-- Both lie in the same slice. -/
  same_c : a c = u c
  /-- They agree in the free dimension `i`. -/
  same_i : a i = u i
  /-- `a` lies below `u` in the free dimension `j`. -/
  le_j : a j ≤ u j
  /-- `f` weakly increases `a` in dimension `j`. -/
  up_j : a j ≤ f a j
  /-- `f` weakly decreases `u` in dimension `j`. -/
  down_j : f u j ≤ u j

lemma DownWitness.le {f : Pt k → Pt k} {i j c : Fin k} (hcov : Covers i j c) {d b : Pt k}
    (hw : DownWitness f i j c d b) : d ≤ b :=
  le_of_three hcov hw.same_i.le hw.le_j hw.same_c.le

lemma UpWitness.le {f : Pt k → Pt k} {i j c : Fin k} (hcov : Covers i j c) {a u : Pt k}
    (hw : UpWitness f i j c a u) : a ≤ u :=
  le_of_three hcov hw.same_i.le hw.le_j hw.same_c.le

/-! ### FPS Lemmas 7 and 9

`d` and `b` agree in every coordinate except `j`, so they lie in a common
one-dimensional slice; `d` goes up in it and `b` goes down, so `exists_solOn {j}`
produces a point `p` fixed in dimension `j`.  The dichotomy then comes from
casing on `p` in dimensions `i` and `c`. -/

/-- **FPS Lemma 7.**  Between the two halves of a down set witness there is either
something the inner algorithm may return, or a point that goes down in *both* free
dimensions — a point of `Down(f_s)` for the slice `s`. -/
theorem downWitness_dichotomy {f : Pt k → Pt k} {i j c : Fin k} (hcov : Covers i j c)
    {d b : Pt k} (hw : DownWitness f i j c d b) :
    HasInnerSol f d b ∨ ∃ p, p ∈ Box d b ∧ DownSlice f i j p := by
  rcases exists_solOn {j} f (hw.le hcov)
      (fun l hl => by
        have hlj : l = j := Finset.mem_singleton.mp hl
        subst hlj; exact hw.up_j)
      (fun l hl => by
        have hlj : l = j := Finset.mem_singleton.mp hl
        subst hlj; exact hw.down_j) with
    ⟨p, hpbox, hpfix, hpoff⟩ | h
  · have hpj : f p j = p j := hpfix j (Finset.mem_singleton_self j)
    have hpc : p c = d c := hpoff c (by simp [Ne.symm hcov.jc])
    by_cases hi : p i ≤ f p i
    · by_cases hc : p c ≤ f p c
      · -- `p` goes up in all three coordinates.
        exact Or.inl (Or.inl ⟨p, hpbox, Or.inl (mem_Up_of_three hcov hi hpj.ge hc)⟩)
      · -- `f p c < p c = d c ≤ f d c`, so `d` and `p` violate order preservation.
        push Not at hc
        refine Or.inl (Or.inr ⟨d, p, mem_Box_self_left (hw.le hcov), hpbox,
          isVop_of_coord (mem_Box.mp hpbox).1 c ?_⟩)
        have h1 := hw.d_c
        omega
    · push Not at hi
      exact Or.inr ⟨p, hpbox, ⟨hi.le, hpj.le⟩⟩
  · exact Or.inl (Or.inr h)

/-- **FPS Lemma 9**, the dual of Lemma 7.  Between the two halves of an up set
witness there is either something the inner algorithm may return, or a point that
goes up in both free dimensions. -/
theorem upWitness_dichotomy {f : Pt k → Pt k} {i j c : Fin k} (hcov : Covers i j c)
    {a u : Pt k} (hw : UpWitness f i j c a u) :
    HasInnerSol f a u ∨ ∃ p, p ∈ Box a u ∧ UpSlice f i j p := by
  rcases exists_solOn {j} f (hw.le hcov)
      (fun l hl => by
        have hlj : l = j := Finset.mem_singleton.mp hl
        subst hlj; exact hw.up_j)
      (fun l hl => by
        have hlj : l = j := Finset.mem_singleton.mp hl
        subst hlj; exact hw.down_j) with
    ⟨p, hpbox, hpfix, hpoff⟩ | h
  · have hpj : f p j = p j := hpfix j (Finset.mem_singleton_self j)
    have hpc : p c = a c := hpoff c (by simp [Ne.symm hcov.jc])
    by_cases hi : f p i ≤ p i
    · by_cases hc : f p c ≤ p c
      · exact Or.inl (Or.inl ⟨p, hpbox, Or.inr (mem_Down_of_three hcov hi hpj.le hc)⟩)
      · -- `f u c ≤ u c = a c = p c < f p c`, so `p` and `u` violate order preservation.
        push Not at hc
        refine Or.inl (Or.inr ⟨p, u, hpbox, mem_Box_self_right (hw.le hcov),
          isVop_of_coord (mem_Box.mp hpbox).2 c ?_⟩)
        have h1 := hw.u_c
        have h2 := hw.same_c
        omega
    · push Not at hi
      exact Or.inr ⟨p, hpbox, ⟨hi.le, hpj.ge⟩⟩
  · exact Or.inl (Or.inr h)

/-! ### FPS Definition 10 and Lemma 11 -/

/-- **FPS Definition 10** (the inner algorithm invariant) on the box `[a, b]`.

Each side is satisfied either directly or by a witness inside the box, and when
both are witnesses they are required to be ordered, `u ≼ d`.  The invariant is
what guarantees (FPS Lemma 11) that `[a, b]` still contains something the inner
algorithm may return, which is what makes its halving loop sound. -/
structure InnerInv (f : Pt k → Pt k) (i j c : Fin k) (a b : Pt k) : Prop where
  /-- The box is non-empty. -/
  le : a ≤ b
  /-- Both endpoints lie in the same principal slice. -/
  same_c : a c = b c
  /-- Either `a ∈ Up(f_s)`, or there is a known up set witness `(a, u)` with
  `u ≼ b`, ordered below every down set witness. -/
  lower : UpSlice f i j a
    ∨ ∃ u, u ≤ b ∧ UpWitness f i j c a u ∧ ∀ d, DownWitness f i j c d b → u ≤ d
  /-- Either `b ∈ Down(f_s)`, or there is a known down set witness `(d, b)` with
  `a ≼ d`. -/
  upper : DownSlice f i j b ∨ ∃ d, a ≤ d ∧ DownWitness f i j c d b

/-- The engine of FPS Lemma 11: from `x ≼ y` with `x` going up and `y` going down
in both free dimensions, `exists_solOn {i, j}` yields a point fixed in both free
dimensions, and casing on the frozen dimension puts it in `Up f` or `Down f`. -/
theorem hasInnerSol_of_slice_updown {f : Pt k → Pt k} {i j c : Fin k} (hcov : Covers i j c)
    {x y : Pt k} (hxy : x ≤ y) (hx : UpSlice f i j x) (hy : DownSlice f i j y) :
    HasInnerSol f x y := by
  rcases exists_solOn {i, j} f hxy
      (fun l hl => by
        rcases Finset.mem_insert.mp hl with rfl | hl'
        · exact hx.1
        · have : l = j := Finset.mem_singleton.mp hl'
          subst this; exact hx.2)
      (fun l hl => by
        rcases Finset.mem_insert.mp hl with rfl | hl'
        · exact hy.1
        · have : l = j := Finset.mem_singleton.mp hl'
          subst this; exact hy.2) with
    ⟨p, hpbox, hpfix, _⟩ | h
  · have hpi : f p i = p i := hpfix i (Finset.mem_insert_self _ _)
    have hpj : f p j = p j := hpfix j (by simp)
    refine Or.inl ⟨p, hpbox, ?_⟩
    by_cases hc : p c ≤ f p c
    · exact Or.inl (mem_Up_of_three hcov hpi.ge hpj.ge hc)
    · push Not at hc
      exact Or.inr (mem_Down_of_three hcov hpi.le hpj.le hc.le)
  · exact Or.inr h

/-- **FPS Lemma 11.**  If `[a, b]` satisfies the inner algorithm invariant then it
contains something the inner algorithm may return.

The proof extracts from the invariant a pair `x ≼ y` in `[a, b]` with `x` going up
and `y` going down in the slice — using Lemmas 9 and 7 when the sides are given by
witnesses, and the invariant's `u ≼ d` clause to order them — and then applies
`hasInnerSol_of_slice_updown`. -/
theorem hasInnerSol_of_innerInv {f : Pt k → Pt k} {i j c : Fin k} (hcov : Covers i j c)
    {a b : Pt k} (hinv : InnerInv f i j c a b) : HasInnerSol f a b := by
  rcases hinv.upper with hDownB | ⟨d, had, hwd⟩
  · -- `b` itself goes down in the slice.
    rcases hinv.lower with hUpA | ⟨u, hub, hwu, _⟩
    · exact hasInnerSol_of_slice_updown hcov hinv.le hUpA hDownB
    · rcases upWitness_dichotomy hcov hwu with hsol | ⟨p, hp, hpup⟩
      · exact hsol.mono le_rfl hub
      · have hpb : p ≤ b := (mem_Box.mp hp).2.trans hub
        exact (hasInnerSol_of_slice_updown hcov hpb hpup hDownB).mono
          (mem_Box.mp hp).1 le_rfl
  · -- A down set witness `(d, b)`: FPS Lemma 7 turns it into a point of `Down(f_s)`.
    rcases downWitness_dichotomy hcov hwd with hsol | ⟨q, hq, hqdown⟩
    · exact hsol.mono had le_rfl
    · rcases hinv.lower with hUpA | ⟨u, hub, hwu, hud⟩
      · -- `a ≼ d ≼ q`, the invariant's promise on the down side.
        have haq : a ≤ q := had.trans (mem_Box.mp hq).1
        exact (hasInnerSol_of_slice_updown hcov haq hUpA hqdown).mono le_rfl
          (mem_Box.mp hq).2
      · rcases upWitness_dichotomy hcov hwu with hsol | ⟨p, hp, hpup⟩
        · exact hsol.mono le_rfl hub
        · -- `p ≼ u ≼ d ≼ q`, using the invariant's `u ≼ d` clause.
          have hpq : p ≤ q := ((mem_Box.mp hp).2.trans (hud d hwd)).trans (mem_Box.mp hq).1
          exact (hasInnerSol_of_slice_updown hcov hpq hpup hqdown).mono
            (mem_Box.mp hp).1 (mem_Box.mp hq).2

/-! ### FPS Lemma 12

The special case: a point `p` on a boundary of the box, in the free dimension `i`
where the down set witness has `d i = b i`, which `f` pushes further out of the
box.  If `b ∈ Down(f_s)` then `p` and `b` violate order preservation directly.  If
instead the invariant is witnessed by a down set witness `(d, b)` with `p ≼ d`,
then either `d ∈ Up f` — a solution — or `f d i < d i` and `p`, `d` violate order
preservation.

FPS's four cases are these two lemmas, each instantiated at the two free
dimensions. -/

/-- **FPS Lemma 12** (upper boundary).  `p` lies on the upper boundary in
dimension `i` and `f` pushes it further up. -/
theorem hasInnerSol_of_escape_upper {f : Pt k → Pt k} {i j c : Fin k} (hcov : Covers i j c)
    {a b p : Pt k} (hpbox : p ∈ Box a b)
    (hboundary : p i = b i) (hescape : p i < f p i)
    (hupper : DownSlice f i j b ∨ ∃ d, p ≤ d ∧ d ≤ b ∧ DownWitness f i j c d b) :
    HasInnerSol f a b := by
  obtain ⟨hap, hpb⟩ := mem_Box.mp hpbox
  rcases hupper with hDown | ⟨d, hpd, hdb, hwit⟩
  · -- `f b i ≤ b i = p i < f p i`.
    refine Or.inr ⟨p, b, hpbox, mem_Box_self_right (hap.trans hpb),
      isVop_of_coord hpb i ?_⟩
    have := hDown.1
    omega
  · by_cases hd : d i ≤ f d i
    · -- `d` goes up in all three coordinates, so `d ∈ Up f`.
      exact Or.inl ⟨d, mem_Box.mpr ⟨hap.trans hpd, hdb⟩,
        Or.inl (mem_Up_of_three hcov hd hwit.up_j hwit.d_c)⟩
    · -- `f d i < d i = b i = p i < f p i` gives a violation between `p` and `d`.
      push Not at hd
      refine Or.inr ⟨p, d, hpbox, mem_Box.mpr ⟨hap.trans hpd, hdb⟩,
        isVop_of_coord hpd i ?_⟩
      have h1 := hwit.same_i
      omega

/-- **FPS Lemma 12** (lower boundary), the dual: `p` lies on the lower boundary in
dimension `i` and `f` pushes it further down. -/
theorem hasInnerSol_of_escape_lower {f : Pt k → Pt k} {i j c : Fin k} (hcov : Covers i j c)
    {a b p : Pt k} (hpbox : p ∈ Box a b)
    (hboundary : p i = a i) (hescape : f p i < p i)
    (hlower : UpSlice f i j a ∨ ∃ u, a ≤ u ∧ u ≤ p ∧ UpWitness f i j c a u) :
    HasInnerSol f a b := by
  obtain ⟨hap, hpb⟩ := mem_Box.mp hpbox
  rcases hlower with hUp | ⟨u, hau, hup, hwit⟩
  · -- `f p i < p i = a i ≤ f a i`.
    refine Or.inr ⟨a, p, mem_Box_self_left (hap.trans hpb), hpbox,
      isVop_of_coord hap i ?_⟩
    have := hUp.1
    omega
  · by_cases hu : f u i ≤ u i
    · -- `u` goes down in all three coordinates, so `u ∈ Down f`.
      exact Or.inl ⟨u, mem_Box.mpr ⟨hau, hup.trans hpb⟩,
        Or.inr (mem_Down_of_three hcov hu hwit.down_j hwit.u_c)⟩
    · -- `f p i < p i = a i = u i < f u i` gives a violation between `u` and `p`.
      push Not at hu
      refine Or.inr ⟨u, p, mem_Box.mpr ⟨hau, hup.trans hpb⟩, hpbox,
        isVop_of_coord hup i ?_⟩
      have h1 := hwit.same_i
      omega

end Tfnp.Tarski
