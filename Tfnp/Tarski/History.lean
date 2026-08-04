/-
Copyright (c) 2026 Angus Joshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Angus Joshi
-/
import Tfnp.Tarski.Product

/-!
# The history of a decomposition run, and FPS Lemmas 16 & 17

This file contains the combinatorial heart of the Fearnley–Pálvölgyi–Savani
decomposition theorem (FPS Section 5), separated from the query-algorithm
plumbing that assembles it (`Tfnp/Tarski/Decomposition.lean`).

Setting: we are solving Tarski on a product box `Box (cat loA loB) (cat hiA hiB)`
inside `ℕ^(a+b)`, by running an `a`-dimensional algorithm `A` whose oracle we
simulate.  Whenever `A` queries `x : Pt a` we must produce a point `y : Pt b`
which is a fixed point of the slice `sliceFun f x`, and — crucially — the
assignment `x ↦ y` must be **monotone**, since otherwise a violation reported by
`A` does not lift to a violation of `f`.

FPS achieve this by recording the pairs produced so far in a set `P` and calling
the `b`-dimensional algorithm on the sub-box `[l, u]`, where

* `l = lowB P loB x` is the join of the `y`s recorded at keys `≤ x`;
* `u = highB P hiB x` is the meet of the `y`s recorded at keys `≥ x`.

## Main results

* `Good` — the invariant maintained on the history: recorded `y`s lie in the
  `B`-box, are fixed points of their slices, and are monotone in their keys.
* `lowB_le_highB` — **FPS Lemma 16**: `l ≼ u`, so the sub-box is non-empty.
* `up_lowB_or_vop`, `down_highB_or_vop` — **FPS Lemma 17**: either `l` is in the
  up set of the slice at `x` (resp. `u` in the down set), or an explicit pair
  drawn from the history witnesses a violation of order preservation of `f`.

Both directions of Lemma 17 name their witness explicitly (`lowWitness`,
`highWitness`), because the algorithm has to *return* it.
-/

namespace Tfnp.Tarski

variable {a b : ℕ}

/-! ### `List.foldr max` / `List.foldr min`

`lowB` and `highB` are defined coordinatewise as folds of `max`/`min` over a
list of naturals.  These three facts — the fold dominates the initial value,
dominates every element, and *is* either the initial value or an element — are
exactly the "least upper bound" reasoning FPS use. -/

namespace Fold

lemma le_foldr_max (init : ℕ) : ∀ L : List ℕ, init ≤ L.foldr max init := by
  intro L
  induction L with
  | nil => exact le_rfl
  | cons v L ih => exact le_trans ih (le_max_right v _)

lemma le_foldr_max_of_mem (init : ℕ) : ∀ (L : List ℕ) {v : ℕ}, v ∈ L → v ≤ L.foldr max init := by
  intro L
  induction L with
  | nil => intro v hv; exact absurd hv (by simp)
  | cons w L ih =>
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv'
    · exact le_max_left _ _
    · exact le_trans (ih hv') (le_max_right _ _)

lemma foldr_max_eq_or_mem (init : ℕ) :
    ∀ L : List ℕ, L.foldr max init = init ∨ L.foldr max init ∈ L := by
  intro L
  induction L with
  | nil => exact Or.inl rfl
  | cons v L ih =>
    have hcons : (v :: L).foldr max init = max v (L.foldr max init) := rfl
    rcases le_total v (L.foldr max init) with hle | hle
    · rw [hcons, max_eq_right hle]
      rcases ih with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (List.mem_cons_of_mem _ h1)
    · rw [hcons, max_eq_left hle]
      exact Or.inr (by simp)

lemma foldr_min_le (init : ℕ) : ∀ L : List ℕ, L.foldr min init ≤ init := by
  intro L
  induction L with
  | nil => exact le_rfl
  | cons v L ih => exact le_trans (min_le_right v _) ih

lemma foldr_min_le_of_mem (init : ℕ) : ∀ (L : List ℕ) {v : ℕ}, v ∈ L → L.foldr min init ≤ v := by
  intro L
  induction L with
  | nil => intro v hv; exact absurd hv (by simp)
  | cons w L ih =>
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv'
    · exact min_le_left _ _
    · exact le_trans (min_le_right _ _) (ih hv')

lemma foldr_min_eq_or_mem (init : ℕ) :
    ∀ L : List ℕ, L.foldr min init = init ∨ L.foldr min init ∈ L := by
  intro L
  induction L with
  | nil => exact Or.inl rfl
  | cons v L ih =>
    have hcons : (v :: L).foldr min init = min v (L.foldr min init) := rfl
    rcases le_total v (L.foldr min init) with hle | hle
    · rw [hcons, min_eq_left hle]
      exact Or.inr (by simp)
    · rw [hcons, min_eq_right hle]
      rcases ih with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (List.mem_cons_of_mem _ h1)

end Fold

/-! ### The history -/

/-- The history maintained by the decomposition algorithm: the pairs `(x, y)`
such that the outer algorithm queried `x` and the inner algorithm answered with
the slice fixed point `y`.  FPS's set `P`. -/
abbrev Hist (a b : ℕ) : Type := List (Pt a × Pt b)

/-- Look up a key in the history.  Earlier entries win, so appending never
changes an existing answer (`memo_append`) — that is what makes the simulated
oracle a genuine function of its argument. -/
def memo (P : Hist a b) (x : Pt a) : Option (Pt b) :=
  (P.find? fun p => p.1 = x).map Prod.snd

lemma memo_append {P Q : Hist a b} {x : Pt a} {y : Pt b} (h : memo P x = some y) :
    memo (P ++ Q) x = some y := by
  unfold memo at h ⊢
  rcases hf : P.find? (fun p => p.1 = x) with _ | p
  · rw [hf] at h; exact absurd h (by simp)
  · rw [List.find?_append, hf]
    rw [hf] at h
    simpa using h

lemma memo_append_singleton {P : Hist a b} {x : Pt a} (h : memo P x = none) (y : Pt b) :
    memo (P ++ [(x, y)]) x = some y := by
  unfold memo at h ⊢
  rcases hf : P.find? (fun p => p.1 = x) with _ | p
  · rw [List.find?_append, hf]; simp
  · rw [hf] at h; exact absurd h (by simp)

lemma mem_of_memo {P : Hist a b} {x : Pt a} {y : Pt b} (h : memo P x = some y) :
    (x, y) ∈ P := by
  unfold memo at h
  rcases hf : P.find? (fun p => p.1 = x) with _ | p
  · rw [hf] at h; exact absurd h (by simp)
  · have hmem : p ∈ P := List.mem_of_find?_eq_some hf
    have hkey : p.1 = x := by simpa using List.find?_some hf
    rw [hf] at h
    have hsnd : p.2 = y := by simpa using h
    have : p = (x, y) := Prod.ext hkey hsnd
    exact this ▸ hmem

/-- `memoD P loB x` is the history's answer at `x`, defaulting to `loB`. -/
def memoD (P : Hist a b) (loB : Pt b) (x : Pt a) : Pt b := (memo P x).getD loB

lemma memoD_eq_of_memo {P : Hist a b} {loB : Pt b} {x : Pt a} {y : Pt b}
    (h : memo P x = some y) : memoD P loB x = y := by simp [memoD, h]

/-! ### The join `l` and the meet `u` -/

/-- `lowB P loB x` is FPS's point `l`: the least upper bound of `loB` together
with all `y` recorded at keys `≼ x`.  Defined coordinatewise as a `max`-fold. -/
def lowB (P : Hist a b) (loB : Pt b) (x : Pt a) : Pt b := fun i =>
  (P.filterMap fun p => if p.1 ≤ x then some (p.2 i) else none).foldr max (loB i)

/-- `highB P hiB x` is FPS's point `u`: the greatest lower bound of `hiB`
together with all `y` recorded at keys `≽ x`. -/
def highB (P : Hist a b) (hiB : Pt b) (x : Pt a) : Pt b := fun i =>
  (P.filterMap fun p => if x ≤ p.1 then some (p.2 i) else none).foldr min (hiB i)

section LowHigh

variable {P : Hist a b} {loB hiB : Pt b} {x : Pt a}

/-- Unfolding lemma: `lowB` is a coordinatewise `max`-fold. -/
lemma lowB_apply (i : Fin b) :
    lowB P loB x i
      = (P.filterMap fun p : Pt a × Pt b => if p.1 ≤ x then some (p.2 i) else none).foldr
          max (loB i) := rfl

/-- Unfolding lemma: `highB` is a coordinatewise `min`-fold. -/
lemma highB_apply (i : Fin b) :
    highB P hiB x i
      = (P.filterMap fun p : Pt a × Pt b => if x ≤ p.1 then some (p.2 i) else none).foldr
          min (hiB i) := rfl

lemma le_lowB (i : Fin b) : loB i ≤ lowB P loB x i := by
  rw [lowB_apply]; exact Fold.le_foldr_max _ _

lemma highB_le (i : Fin b) : highB P hiB x i ≤ hiB i := by
  rw [highB_apply]; exact Fold.foldr_min_le _ _

lemma loB_le_lowB : loB ≤ lowB P loB x := coord_le fun i => le_lowB i

lemma highB_le_hiB : highB P hiB x ≤ hiB := coord_le fun i => highB_le i

/-- `l` is an upper bound of the recorded values at keys below `x`. -/
lemma le_lowB_of_mem {p : Pt a × Pt b} (hp : p ∈ P) (hkey : p.1 ≤ x) :
    p.2 ≤ lowB P loB x := by
  refine coord_le fun i => ?_
  rw [lowB_apply]
  refine Fold.le_foldr_max_of_mem _ _ ?_
  exact List.mem_filterMap.mpr ⟨p, hp, by simp [hkey]⟩

/-- `u` is a lower bound of the recorded values at keys above `x`. -/
lemma highB_le_of_mem {p : Pt a × Pt b} (hp : p ∈ P) (hkey : x ≤ p.1) :
    highB P hiB x ≤ p.2 := by
  refine coord_le fun i => ?_
  rw [highB_apply]
  refine Fold.foldr_min_le_of_mem _ _ ?_
  exact List.mem_filterMap.mpr ⟨p, hp, by simp [hkey]⟩

/-- Coordinatewise attainment: in each coordinate, `l` equals either `loB` or
some recorded value at a key below `x`.  This is FPS's "let `y ∈ D` be a point
such that `yᵢ = lᵢ`, which must exist since otherwise `l` would not be the least
upper bound of `D`". -/
lemma lowB_attained (i : Fin b) :
    lowB P loB x i = loB i ∨ ∃ p ∈ P, p.1 ≤ x ∧ p.2 i = lowB P loB x i := by
  rw [lowB_apply]
  rcases Fold.foldr_max_eq_or_mem (loB i)
      (P.filterMap fun p : Pt a × Pt b => if p.1 ≤ x then some (p.2 i) else none) with h | h
  · exact Or.inl h
  · obtain ⟨p, hp, hpv⟩ := List.mem_filterMap.mp h
    by_cases hkey : p.1 ≤ x
    · rw [if_pos hkey] at hpv
      exact Or.inr ⟨p, hp, hkey, Option.some.inj hpv⟩
    · rw [if_neg hkey] at hpv; exact absurd hpv (by simp)

/-- Dual of `lowB_attained`. -/
lemma highB_attained (i : Fin b) :
    highB P hiB x i = hiB i ∨ ∃ p ∈ P, x ≤ p.1 ∧ p.2 i = highB P hiB x i := by
  rw [highB_apply]
  rcases Fold.foldr_min_eq_or_mem (hiB i)
      (P.filterMap fun p : Pt a × Pt b => if x ≤ p.1 then some (p.2 i) else none) with h | h
  · exact Or.inl h
  · obtain ⟨p, hp, hpv⟩ := List.mem_filterMap.mp h
    by_cases hkey : x ≤ p.1
    · rw [if_pos hkey] at hpv
      exact Or.inr ⟨p, hp, hkey, Option.some.inj hpv⟩
    · rw [if_neg hkey] at hpv; exact absurd hpv (by simp)

end LowHigh

/-! ### The invariant -/

/-- The invariant maintained on the history by the decomposition algorithm.

`keyA`  — every recorded key lies in the `A`-box;
`memB`  — every recorded value lies in the `B`-box;
`slice` — every recorded value is a fixed point of its own slice function
          (it was returned as such by the inner algorithm);
`mono`  — the record is monotone: `x₁ ≼ x₂` implies `y₁ ≼ y₂`.

`mono` is what makes a violation found by the outer algorithm lift, `slice` is
what makes FPS Lemma 17 work, and `keyA`/`memB` are what put the returned points
inside the box, as `IsSol` demands. -/
structure Good (f : Pt (a + b) → Pt (a + b)) (loA hiA : Pt a) (loB hiB : Pt b)
    (P : Hist a b) : Prop where
  keyA : ∀ p ∈ P, p.1 ∈ Box loA hiA
  memB : ∀ p ∈ P, p.2 ∈ Box loB hiB
  slice : ∀ p ∈ P, sliceFun f p.1 p.2 = p.2
  mono : ∀ p ∈ P, ∀ q ∈ P, p.1 ≤ q.1 → p.2 ≤ q.2

lemma Good.nil {f : Pt (a + b) → Pt (a + b)} {loA hiA : Pt a} {loB hiB : Pt b} :
    Good f loA hiA loB hiB ([] : Hist a b) := ⟨by simp, by simp, by simp, by simp⟩

/-- Extending the history with a new pair preserves the invariant, provided the
new value lies between `l` and `u`, is a slice fixed point, and both components
lie in their boxes.  Monotonicity is re-established exactly because `l` dominates
everything below `x` and `u` is dominated by everything above `x`. -/
lemma Good.append {f : Pt (a + b) → Pt (a + b)} {loA hiA : Pt a} {loB hiB : Pt b}
    {P : Hist a b} (hP : Good f loA hiA loB hiB P) {x : Pt a} {y : Pt b}
    (hxA : x ∈ Box loA hiA) (hyB : y ∈ Box loB hiB) (hyfix : sliceFun f x y = y)
    (hly : lowB P loB x ≤ y) (hyu : y ≤ highB P hiB x) :
    Good f loA hiA loB hiB (P ++ [(x, y)]) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp
    rcases List.mem_append.mp hp with h | h
    · exact hP.keyA p h
    · simp only [List.mem_singleton] at h; subst h; exact hxA
  · intro p hp
    rcases List.mem_append.mp hp with h | h
    · exact hP.memB p h
    · simp only [List.mem_singleton] at h; subst h; exact hyB
  · intro p hp
    rcases List.mem_append.mp hp with h | h
    · exact hP.slice p h
    · simp only [List.mem_singleton] at h; subst h; exact hyfix
  · intro p hp q hq hpq
    rcases List.mem_append.mp hp with hp' | hp' <;>
      rcases List.mem_append.mp hq with hq' | hq'
    · exact hP.mono p hp' q hq' hpq
    · -- `q = (x, y)`: `p.2 ≤ l ≤ y`.
      simp only [List.mem_singleton] at hq'; subst hq'
      exact (le_lowB_of_mem hp' hpq).trans hly
    · -- `p = (x, y)`: `y ≤ u ≤ q.2`.
      simp only [List.mem_singleton] at hp'; subst hp'
      exact hyu.trans (highB_le_of_mem hq' hpq)
    · simp only [List.mem_singleton] at hp' hq'; subst hp'; subst hq'; exact le_rfl

/-! ### FPS Lemma 16 -/

/-- **FPS Lemma 16.**  `l ≼ u`, so the sub-box handed to the inner algorithm is
non-empty.

The four cases of the proof are the four ways `lᵢ` and `uᵢ` can be attained: at
the box endpoints (where `loB ≼ hiB` suffices), at one endpoint and one recorded
value (where `Good.memB` suffices), or at two recorded values `y₁, y₂` with keys
`x₁ ≼ x ≼ x₂` — and then `Good.mono` gives `y₁ ≼ y₂`. -/
theorem lowB_le_highB {f : Pt (a + b) → Pt (a + b)} {loA hiA : Pt a} {loB hiB : Pt b}
    {P : Hist a b} (hP : Good f loA hiA loB hiB P) (hlohi : loB ≤ hiB) (x : Pt a) :
    lowB P loB x ≤ highB P hiB x := by
  refine coord_le fun i => ?_
  rcases lowB_attained (P := P) (loB := loB) (x := x) i with hl | ⟨p, hp, hpx, hpi⟩
  · rcases highB_attained (P := P) (hiB := hiB) (x := x) i with hu | ⟨q, hq, hxq, hqi⟩
    · rw [hl, hu]; exact le_coord hlohi i
    · rw [hl, ← hqi]
      exact le_coord (mem_Box.mp (hP.memB q hq)).1 i
  · rcases highB_attained (P := P) (hiB := hiB) (x := x) i with hu | ⟨q, hq, hxq, hqi⟩
    · rw [hu, ← hpi]
      exact le_coord (mem_Box.mp (hP.memB p hp)).2 i
    · rw [← hpi, ← hqi]
      exact le_coord (hP.mono p hp q hq (hpx.trans hxq)) i

/-! ### FPS Lemma 17

Either `l` lies in the up set of the slice at `x`, or a pair drawn from the
history witnesses a violation of order preservation of `f`.  We must produce the
witness explicitly, since the algorithm returns it — and the *selection rule*
must mention only data the algorithm has: the history, `x`, and the coordinate in
which the check failed.  Hence `lowWitnessOf` takes that coordinate as an
argument rather than deriving it from `f`. -/

/-- The coordinate in which a `≤` check failed. -/
noncomputable def failCoord {k : ℕ} {v w : Pt k} (h : ¬ v ≤ w) : Fin k :=
  (exists_lt_of_not_le h).choose

lemma failCoord_spec {k : ℕ} {v w : Pt k} (h : ¬ v ≤ w) : w (failCoord h) < v (failCoord h) :=
  (exists_lt_of_not_le h).choose_spec

open Classical in
/-- The history entry witnessing FPS Lemma 17 for `l`, in the coordinate `i`. -/
noncomputable def lowWitnessOf (P : Hist a b) (loB : Pt b) (x : Pt a) (i : Fin b) : Pt a × Pt b :=
  if hw : ∃ p ∈ P, p.1 ≤ x ∧ p.2 i = lowB P loB x i then hw.choose else (x, lowB P loB x)

open Classical in
/-- The history entry witnessing FPS Lemma 17 for `u`, in the coordinate `i`. -/
noncomputable def highWitnessOf (P : Hist a b) (hiB : Pt b) (x : Pt a) (i : Fin b) : Pt a × Pt b :=
  if hw : ∃ p ∈ P, x ≤ p.1 ∧ p.2 i = highB P hiB x i then hw.choose else (x, highB P hiB x)

/-- **FPS Lemma 17** (up-set half).  If `f` at `cat x l` goes strictly below `l`
in coordinate `i`, then `lowWitnessOf P loB x i` together with `cat x l`
witnesses a violation of order preservation of `f`.

Contrapositively: unless a violation is exposed, `l` is in the up set of the
slice at `x`, which is the precondition for calling the inner algorithm.

The hypothesis `hlo` says `f` does not send `cat x l` below the box; it rules out
the case where `lᵢ` is attained at `loB`, a step FPS leave implicit. -/
theorem up_lowB_or_vop {f : Pt (a + b) → Pt (a + b)} {loB hiB : Pt b}
    {loA hiA : Pt a} {P : Hist a b} (hP : Good f loA hiA loB hiB P) {x : Pt a} {i : Fin b}
    (hlo : loB ≤ pr2 (f (cat x (lowB P loB x))))
    (hi : pr2 (f (cat x (lowB P loB x))) i < lowB P loB x i) :
    IsVop f (cat (lowWitnessOf P loB x i).1 (lowWitnessOf P loB x i).2)
      (cat x (lowB P loB x)) := by
  -- `lᵢ` cannot be attained at `loB`, since `f` does not go below the box.
  have hattain : ∃ p ∈ P, p.1 ≤ x ∧ p.2 i = lowB P loB x i := by
    rcases lowB_attained (P := P) (loB := loB) (x := x) i with hcase | hcase
    · exact absurd (le_coord hlo i) (by omega)
    · exact hcase
  have hw : lowWitnessOf P loB x i = hattain.choose := by rw [lowWitnessOf, dif_pos hattain]
  obtain ⟨hmem, hkey, hval⟩ := hattain.choose_spec
  rw [hw]
  refine isVop_of_coord (cat_mono hkey (le_lowB_of_mem hmem hkey)) (Fin.natAdd a i) ?_
  -- `f` fixes the slice at the witness, so its `i`-th `B`-coordinate is `p.2 i = lᵢ`.
  have hR : f (cat hattain.choose.1 hattain.choose.2) (Fin.natAdd a i)
      = lowB P loB x i := by
    have hs := congrFun (hP.slice _ hmem) i
    change f (cat hattain.choose.1 hattain.choose.2) (Fin.natAdd a i)
        = hattain.choose.2 i at hs
    rw [hs, hval]
  have hL : f (cat x (lowB P loB x)) (Fin.natAdd a i)
      = pr2 (f (cat x (lowB P loB x))) i := rfl
  omega

/-- **FPS Lemma 17** (down-set half), dual to `up_lowB_or_vop`. -/
theorem down_highB_or_vop {f : Pt (a + b) → Pt (a + b)} {loB hiB : Pt b}
    {loA hiA : Pt a} {P : Hist a b} (hP : Good f loA hiA loB hiB P) {x : Pt a} {i : Fin b}
    (hhi : pr2 (f (cat x (highB P hiB x))) ≤ hiB)
    (hi : highB P hiB x i < pr2 (f (cat x (highB P hiB x))) i) :
    IsVop f (cat x (highB P hiB x))
      (cat (highWitnessOf P hiB x i).1 (highWitnessOf P hiB x i).2) := by
  have hattain : ∃ p ∈ P, x ≤ p.1 ∧ p.2 i = highB P hiB x i := by
    rcases highB_attained (P := P) (hiB := hiB) (x := x) i with hcase | hcase
    · exact absurd (le_coord hhi i) (by omega)
    · exact hcase
  have hw : highWitnessOf P hiB x i = hattain.choose := by rw [highWitnessOf, dif_pos hattain]
  obtain ⟨hmem, hkey, hval⟩ := hattain.choose_spec
  rw [hw]
  refine isVop_of_coord (cat_mono hkey (highB_le_of_mem hmem hkey)) (Fin.natAdd a i) ?_
  have hR : f (cat hattain.choose.1 hattain.choose.2) (Fin.natAdd a i)
      = highB P hiB x i := by
    have hs := congrFun (hP.slice _ hmem) i
    change f (cat hattain.choose.1 hattain.choose.2) (Fin.natAdd a i)
        = hattain.choose.2 i at hs
    rw [hs, hval]
  have hL : f (cat x (highB P hiB x)) (Fin.natAdd a i)
      = pr2 (f (cat x (highB P hiB x))) i := rfl
  omega

/-! ### The oracle presented to the outer algorithm -/

/-- The oracle the decomposition presents to the outer, `a`-dimensional
algorithm: look up `x` in the history and read off the `A`-coordinates of `f` at
the resulting product point.  Because `memo` is stable under extension of the
history, this is a genuine *function* of `x` — which is what lets us invoke the
outer algorithm's correctness. -/
def outerOracle (f : Pt (a + b) → Pt (a + b)) (loB : Pt b) (P : Hist a b) : Pt a → Pt a :=
  fun x => pr1 (f (cat x (memoD P loB x)))

lemma memoD_mem_Box {f : Pt (a + b) → Pt (a + b)} {loA hiA : Pt a} {loB hiB : Pt b}
    {P : Hist a b} (hP : Good f loA hiA loB hiB P) (hloB : loB ≤ hiB) (x : Pt a) :
    memoD P loB x ∈ Box loB hiB := by
  rcases h : memo P x with _ | y
  · rw [memoD, h]; exact mem_Box_self_left hloB
  · rw [memoD, h]; exact hP.memB (x, y) (mem_of_memo h)

lemma memoD_append {P Q : Hist a b} {loB : Pt b} {x : Pt a} {y : Pt b}
    (h : memo P x = some y) : memoD (P ++ Q) loB x = y := by
  rw [memoD, memo_append h]; rfl

/-- The simulated oracle maps the `A`-box into itself, so the outer algorithm's
correctness hypothesis is satisfied. -/
lemma outerOracle_mapsTo {f : Pt (a + b) → Pt (a + b)} {loA hiA : Pt a} {loB hiB : Pt b}
    {P : Hist a b} (hP : Good f loA hiA loB hiB P) (hloB : loB ≤ hiB)
    (hmap : ∀ z ∈ Box (cat loA loB) (cat hiA hiB), f z ∈ Box (cat loA loB) (cat hiA hiB)) :
    ∀ x ∈ Box loA hiA, outerOracle f loB P x ∈ Box loA hiA := by
  intro x hx
  have hz : cat x (memoD P loB x) ∈ Box (cat loA loB) (cat hiA hiB) :=
    mem_Box_cat.mpr ⟨hx, memoD_mem_Box hP hloB x⟩
  have := hmap _ hz
  rw [← cat_pr (f (cat x (memoD P loB x)))] at this
  exact (mem_Box_cat.mp this).1


/-! ### Box membership, and Lemma 17 packaged as a solution

The algorithm returns the Lemma 17 witnesses, and `IsSol` demands that returned
points lie in the box.  These lemmas supply that, so the algorithm's correctness
proof never has to reason about boxes again. -/

lemma lowWitnessOf_mem_or (P : Hist a b) (loB : Pt b) (x : Pt a) (i : Fin b) :
    lowWitnessOf P loB x i ∈ P ∨ lowWitnessOf P loB x i = (x, lowB P loB x) := by
  classical
  unfold lowWitnessOf
  by_cases hw : ∃ p ∈ P, p.1 ≤ x ∧ p.2 i = lowB P loB x i
  · rw [dif_pos hw]; exact Or.inl hw.choose_spec.1
  · rw [dif_neg hw]; exact Or.inr rfl

lemma highWitnessOf_mem_or (P : Hist a b) (hiB : Pt b) (x : Pt a) (i : Fin b) :
    highWitnessOf P hiB x i ∈ P ∨ highWitnessOf P hiB x i = (x, highB P hiB x) := by
  classical
  unfold highWitnessOf
  by_cases hw : ∃ p ∈ P, x ≤ p.1 ∧ p.2 i = highB P hiB x i
  · rw [dif_pos hw]; exact Or.inl hw.choose_spec.1
  · rw [dif_neg hw]; exact Or.inr rfl

variable {f : Pt (a + b) → Pt (a + b)} {loA hiA : Pt a} {loB hiB : Pt b} {P : Hist a b}

lemma lowB_mem_Box (hP : Good f loA hiA loB hiB P) (hloB : loB ≤ hiB) (x : Pt a) :
    lowB P loB x ∈ Box loB hiB :=
  mem_Box.mpr ⟨loB_le_lowB, (lowB_le_highB hP hloB x).trans highB_le_hiB⟩

lemma highB_mem_Box (hP : Good f loA hiA loB hiB P) (hloB : loB ≤ hiB) (x : Pt a) :
    highB P hiB x ∈ Box loB hiB :=
  mem_Box.mpr ⟨loB_le_lowB.trans (lowB_le_highB hP hloB x), highB_le_hiB⟩

/-- The `cat`-image of a Lemma 17 witness lies in the product box. -/
lemma lowWitness_mem_Box (hP : Good f loA hiA loB hiB P) (hloB : loB ≤ hiB)
    {x : Pt a} (hx : x ∈ Box loA hiA) (i : Fin b) :
    cat (lowWitnessOf P loB x i).1 (lowWitnessOf P loB x i).2
      ∈ Box (cat loA loB) (cat hiA hiB) := by
  rcases lowWitnessOf_mem_or P loB x i with h | h
  · exact mem_Box_cat.mpr ⟨hP.keyA _ h, hP.memB _ h⟩
  · rw [h]; exact mem_Box_cat.mpr ⟨hx, lowB_mem_Box hP hloB x⟩

lemma highWitness_mem_Box (hP : Good f loA hiA loB hiB P) (hloB : loB ≤ hiB)
    {x : Pt a} (hx : x ∈ Box loA hiA) (i : Fin b) :
    cat (highWitnessOf P hiB x i).1 (highWitnessOf P hiB x i).2
      ∈ Box (cat loA loB) (cat hiA hiB) := by
  rcases highWitnessOf_mem_or P hiB x i with h | h
  · exact mem_Box_cat.mpr ⟨hP.keyA _ h, hP.memB _ h⟩
  · rw [h]; exact mem_Box_cat.mpr ⟨hx, highB_mem_Box hP hloB x⟩

/-- **FPS Lemma 17** (up-set half) packaged as a solution of the whole instance. -/
theorem sol_of_lowB_fail (hP : Good f loA hiA loB hiB P) (hloB : loB ≤ hiB)
    (hmap : ∀ z ∈ Box (cat loA loB) (cat hiA hiB), f z ∈ Box (cat loA loB) (cat hiA hiB))
    {x : Pt a} (hx : x ∈ Box loA hiA) {i : Fin b}
    (hi : pr2 (f (cat x (lowB P loB x))) i < lowB P loB x i) :
    IsSol f (cat loA loB) (cat hiA hiB)
      (.inr (cat (lowWitnessOf P loB x i).1 (lowWitnessOf P loB x i).2,
             cat x (lowB P loB x))) := by
  have hxl : cat x (lowB P loB x) ∈ Box (cat loA loB) (cat hiA hiB) :=
    mem_Box_cat.mpr ⟨hx, lowB_mem_Box hP hloB x⟩
  have hlo : loB ≤ pr2 (f (cat x (lowB P loB x))) := by
    have hfz := hmap _ hxl
    rw [← cat_pr (f (cat x (lowB P loB x)))] at hfz
    exact (mem_Box.mp (mem_Box_cat.mp hfz).2).1
  exact ⟨lowWitness_mem_Box hP hloB hx i, hxl, up_lowB_or_vop hP hlo hi⟩

/-- **FPS Lemma 17** (down-set half) packaged as a solution of the whole instance. -/
theorem sol_of_highB_fail (hP : Good f loA hiA loB hiB P) (hloB : loB ≤ hiB)
    (hmap : ∀ z ∈ Box (cat loA loB) (cat hiA hiB), f z ∈ Box (cat loA loB) (cat hiA hiB))
    {x : Pt a} (hx : x ∈ Box loA hiA) {i : Fin b}
    (hi : highB P hiB x i < pr2 (f (cat x (highB P hiB x))) i) :
    IsSol f (cat loA loB) (cat hiA hiB)
      (.inr (cat x (highB P hiB x),
             cat (highWitnessOf P hiB x i).1 (highWitnessOf P hiB x i).2)) := by
  have hxu : cat x (highB P hiB x) ∈ Box (cat loA loB) (cat hiA hiB) :=
    mem_Box_cat.mpr ⟨hx, highB_mem_Box hP hloB x⟩
  have hhi : pr2 (f (cat x (highB P hiB x))) ≤ hiB := by
    have hfz := hmap _ hxu
    rw [← cat_pr (f (cat x (highB P hiB x)))] at hfz
    exact (mem_Box.mp (mem_Box_cat.mp hfz).2).2
  exact ⟨hxu, highWitness_mem_Box hP hloB hx i, down_highB_or_vop hP hhi hi⟩

end Tfnp.Tarski
