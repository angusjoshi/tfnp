/-
Copyright (c) 2026 Angus Joshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Angus Joshi
-/
import Tfnp.Tarski.Outer
import Tfnp.Tarski.Decomposition

/-!
# The Haslebacher–Lill levelset algorithm: levelsets and configurations

> Sebastian Haslebacher, Jonas Lill.
> *A Levelset Algorithm for 3D-Tarski.*
> [arXiv:2510.14777](https://arxiv.org/abs/2510.14777)

HL give an `O(log² N)`-query algorithm for `Tarski` on a three-dimensional grid,
matching Fearnley–Pálvölgyi–Savani but avoiding their intricate inner algorithm.
Where FPS binary-search over two-dimensional *slices* `{x | x₁ = k}`, HL search
over *levelsets* `{x | x₁ + x₂ + x₃ = k}`.  Levelsets treat all three dimensions
symmetrically, at the cost that no two of their points are comparable.

This file sets up levelsets and proves the parts of HL §3 that are pure order
theory; `Tfnp/Tarski/LevelsetSearch.lean` does the search-space shrinking, and
`Tfnp/Tarski/LevelsetMain.lean` assembles the algorithm.

## The total setting

HL present the algorithm under the promise that `F` is monotone, remarking (§2)
that it adapts to the total setting, "because our algorithm only exploits
monotonicity locally: if a certain step of the algorithm should fail, then a
violation of monotonicity must be present among a constant set of previous
queries."

We take them up on that and formalize the **total** version throughout: every
conclusion is "… or an explicit violation of order preservation", and every appeal
to monotonicity in a proof becomes a case split which, in the bad case, produces
that violation.  This costs a `by_cases` per monotonicity use and buys two things:
the results compose with the rest of this development, and — decisively — the
resulting three-dimensional algorithm is a `SolvesUpDown` family, so it plugs
straight into the already-proved FPS decomposition theorem
(`Tfnp/Tarski/Decomposition.lean`) to give a bound for every dimension.

## Main definitions

* `lev x = ∑ i, x i` — HL's `|x|`; `boxSize lo hi = lev hi - lev lo`
  (`boxSize_eq_lev_sub`), so the `ℓ¹` diameter of a box *is* the range of levels
  it spans.
* `IUp F x i`, `IDown F x i` — HL Definition 3.3.
* `HasProgress F lo hi k` — what the levelset subprocedure must achieve: an upward
  point at level `≥ k`, a downward point at level `≤ k`, or a violation.
* `IsLevelsetSol`, `SolvesLevelset` — the subprocedure interface.

## Main results

* `up_or_down_or_iUpDown` — the observation after HL Definition 3.3, and the
  reason the method is special to `d = 3`: a point that is neither upward nor
  downward is `i`-upward or `i`-downward for some `i`.
* `hasProgress_of_config1Up` / `Down` — **HL Observation 3.9**.
* `hasProgress_of_config2Up` / `Down` — **HL Observation 3.10**.
* `levelsetOuter_isSol`, `levelsetOuter_bounded` — **HL Lemma 3.2**: a levelset
  subprocedure making `q` queries yields a Tarski algorithm making
  `⌈log₂ (boxSize lo hi)⌉ · q + 2` queries.  Unlike the rest of HL §3 this is
  dimension-independent.
-/

namespace Tfnp.Tarski

open QueryAlg (Bounded)

variable {d : ℕ}

/-! ### Levels -/

/-- HL's `|x|`: the `ℓ¹` norm of a grid point. -/
def lev (x : Pt d) : ℕ := ∑ i, x i

lemma lev_mono {x y : Pt d} (h : x ≤ y) : lev x ≤ lev y :=
  Finset.sum_le_sum fun i _ => le_coord h i

/-- The `ℓ¹` diameter of a box is exactly the range of levels it spans.  This is
what lets HL's binary search over levels double as a halving of `boxSize`. -/
lemma boxSize_eq_lev_sub {lo hi : Pt d} (h : lo ≤ hi) : boxSize lo hi = lev hi - lev lo := by
  have hsum : boxSize lo hi + lev lo = lev hi := by
    unfold boxSize lev
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by have := le_coord h i; omega
  omega

lemma lev_le_lev_of_mem_Box {lo hi x : Pt d} (h : x ∈ Box lo hi) :
    lev lo ≤ lev x ∧ lev x ≤ lev hi :=
  ⟨lev_mono (mem_Box.mp h).1, lev_mono (mem_Box.mp h).2⟩

lemma lev_succAt (x : Pt d) (i : Fin d) : lev (succAt x i) = lev x + 1 := by
  unfold lev
  have key : ∀ g : Fin d → ℕ,
      ∑ j, g j = g i + ∑ j ∈ (Finset.univ : Finset (Fin d)).erase i, g j :=
    fun g => (Finset.add_sum_erase _ g (Finset.mem_univ i)).symm
  rw [key (succAt x i), key x]
  have hcong : ∑ j ∈ (Finset.univ : Finset (Fin d)).erase i, succAt x i j
      = ∑ j ∈ (Finset.univ : Finset (Fin d)).erase i, x j :=
    Finset.sum_congr rfl fun j hj => by rw [succAt_of_ne x (Finset.ne_of_mem_erase hj)]
  rw [hcong, succAt_self]
  omega

/-- **Every level between those of the endpoints is realised in the box.**  Walking
up from `a` one coordinate at a time raises the level by exactly one each step, so
no level is skipped.

This is what makes HL's binary search over levels well defined: the levelset `L_k`
of a box is non-empty for every `k` between `lev lo` and `lev hi`. -/
theorem exists_lev_between {a b : Pt d} (hab : a ≤ b) {k : ℕ}
    (h1 : lev a ≤ k) (h2 : k ≤ lev b) :
    ∃ q, a ≤ q ∧ q ≤ b ∧ lev q = k := by
  suffices H : ∀ n (a' : Pt d), k - lev a' ≤ n → a ≤ a' → a' ≤ b → lev a' ≤ k →
      ∃ q, a ≤ q ∧ q ≤ b ∧ lev q = k by
    exact H (k - lev a) a le_rfl le_rfl hab h1
  intro n
  induction n with
  | zero =>
    intro a' hn haa' ha'b hlev
    exact ⟨a', haa', ha'b, by omega⟩
  | succ n ih =>
    intro a' hn haa' ha'b hlev
    by_cases heq : lev a' = k
    · exact ⟨a', haa', ha'b, heq⟩
    · -- `lev a' < k ≤ lev b`, so `a'` falls short of `b` in some coordinate
      have hlt : lev a' < k := by omega
      obtain ⟨i, hi⟩ : ∃ i, a' i < b i := by
        by_contra hc
        push Not at hc
        have hba : lev b ≤ lev a' := lev_mono (coord_le hc)
        omega
      refine ih (succAt a' i) ?_ (haa'.trans (le_succAt a' i)) (succAt_le ha'b hi) ?_
      · rw [lev_succAt]; omega
      · rw [lev_succAt]; omega

/-- The levelset of a box is non-empty at every level it spans. -/
theorem exists_mem_levelset {lo hi : Pt d} (hlohi : lo ≤ hi) {k : ℕ}
    (h1 : lev lo ≤ k) (h2 : k ≤ lev hi) :
    ∃ q, q ∈ Box lo hi ∧ lev q = k := by
  obtain ⟨q, h1', h2', h3'⟩ := exists_lev_between hlohi h1 h2
  exact ⟨q, mem_Box.mpr ⟨h1', h2'⟩, h3'⟩

/-! ### Meet and join

HL's `GLB` and `LUB`.  Spelled out rather than taken from the `Pi` lattice
instance, so that coordinate reasoning stays in reach of `omega`. -/

/-- Coordinatewise minimum — HL's `GLB`. -/
def glb (x y : Pt d) : Pt d := fun i => min (x i) (y i)

/-- Coordinatewise maximum — HL's `LUB`. -/
def lub (x y : Pt d) : Pt d := fun i => max (x i) (y i)

@[simp] lemma glb_apply (x y : Pt d) (i : Fin d) : glb x y i = min (x i) (y i) := rfl
@[simp] lemma lub_apply (x y : Pt d) (i : Fin d) : lub x y i = max (x i) (y i) := rfl

lemma glb_le_left (x y : Pt d) : glb x y ≤ x := coord_le fun _ => min_le_left _ _
lemma glb_le_right (x y : Pt d) : glb x y ≤ y := coord_le fun _ => min_le_right _ _
lemma left_le_lub (x y : Pt d) : x ≤ lub x y := coord_le fun _ => le_max_left _ _
lemma right_le_lub (x y : Pt d) : y ≤ lub x y := coord_le fun _ => le_max_right _ _

lemma le_glb {z x y : Pt d} (hx : z ≤ x) (hy : z ≤ y) : z ≤ glb x y :=
  coord_le fun i => le_min (le_coord hx i) (le_coord hy i)

lemma lub_le {x y z : Pt d} (hx : x ≤ z) (hy : y ≤ z) : lub x y ≤ z :=
  coord_le fun i => max_le (le_coord hx i) (le_coord hy i)

lemma glb_mem_Box {lo hi x y : Pt d} (hx : x ∈ Box lo hi) (hy : y ∈ Box lo hi) :
    glb x y ∈ Box lo hi :=
  mem_Box.mpr ⟨le_glb (mem_Box.mp hx).1 (mem_Box.mp hy).1,
    (glb_le_left x y).trans (mem_Box.mp hx).2⟩

lemma lub_mem_Box {lo hi x y : Pt d} (hx : x ∈ Box lo hi) (hy : y ∈ Box lo hi) :
    lub x y ∈ Box lo hi :=
  mem_Box.mpr ⟨(mem_Box.mp hx).1.trans (left_le_lub x y),
    lub_le (mem_Box.mp hx).2 (mem_Box.mp hy).2⟩

/-! ### `i`-upward and `i`-downward points (HL Definition 3.3) -/

/-- HL Definition 3.3: `x` is `i`-upward if `F` strictly increases the `i`-th
coordinate and weakly decreases all others. -/
def IUp (F : Pt d → Pt d) (x : Pt d) (i : Fin d) : Prop :=
  x i < F x i ∧ ∀ j ≠ i, F x j ≤ x j

/-- HL Definition 3.3: `x` is `i`-downward if `F` strictly decreases the `i`-th
coordinate and weakly increases all others. -/
def IDown (F : Pt d → Pt d) (x : Pt d) (i : Fin d) : Prop :=
  F x i < x i ∧ ∀ j ≠ i, x j ≤ F x j

private lemma fin_val_ne {n : ℕ} {a b : Fin n} (h : a ≠ b) : (a : ℕ) ≠ (b : ℕ) :=
  fun he => h (Fin.val_inj.mp he)

/-- Three distinct coordinates exhaust `Fin 3`. -/
lemma fin3_cover {i j p : Fin 3} (hij : i ≠ j) (hip : i ≠ p) (hjp : j ≠ p) (l : Fin 3) :
    l = i ∨ l = j ∨ l = p := by
  by_contra hc
  push Not at hc
  obtain ⟨h1, h2, h3⟩ := hc
  have := fin_val_ne hij
  have := fin_val_ne hip
  have := fin_val_ne hjp
  have := fin_val_ne h1
  have := fin_val_ne h2
  have := fin_val_ne h3
  have : (l : ℕ) < 3 := l.isLt
  have : (i : ℕ) < 3 := i.isLt
  have : (j : ℕ) < 3 := j.isLt
  have : (p : ℕ) < 3 := p.isLt
  omega

/-- **The observation after HL Definition 3.3**, and the reason the levelset method
is special to `d = 3`: a point that is neither upward nor downward must be
`i`-upward or `i`-downward for some `i`.

In three dimensions a sign pattern with both a strict `+` and a strict `−` has
either exactly one `+` or exactly one `−`; with four or more coordinates it can
have two of each, and the argument fails. -/
theorem up_or_down_or_iUpDown (F : Pt 3 → Pt 3) (x : Pt 3) :
    x ∈ Up F ∨ x ∈ Down F ∨ (∃ i, IUp F x i) ∨ (∃ i, IDown F x i) := by
  by_cases hup : x ∈ Up F
  · exact Or.inl hup
  by_cases hdown : x ∈ Down F
  · exact Or.inr (Or.inl hdown)
  -- `x` fails both, so some coordinate strictly decreases and some strictly increases.
  obtain ⟨j, hj⟩ : ∃ j, F x j < x j := exists_lt_of_not_le hup
  obtain ⟨l, hl⟩ : ∃ l, x l < F x l := exists_lt_of_not_le hdown
  by_cases hiu : ∃ i, IUp F x i
  · exact Or.inr (Or.inr (Or.inl hiu))
  by_cases hid : ∃ i, IDown F x i
  · exact Or.inr (Or.inr (Or.inr hid))
  -- Otherwise the strict `+` at `l` has a companion, and so does the strict `−` at `j`.
  exfalso
  push Not at hiu hid
  obtain ⟨l', hl'ne, hl'⟩ : ∃ l', l' ≠ l ∧ x l' < F x l' := by
    by_contra hcon
    push Not at hcon
    refine hiu l ⟨hl, fun m hm => ?_⟩
    have := hcon m hm
    omega
  obtain ⟨j', hj'ne, hj'⟩ : ∃ j', j' ≠ j ∧ F x j' < x j' := by
    by_contra hcon
    push Not at hcon
    refine hid j ⟨hj, fun m hm => ?_⟩
    have := hcon m hm
    omega
  -- `l, l'` strictly increase and `j, j'` strictly decrease: four distinct coordinates.
  have h1 : l ≠ j := fun h => by rw [h] at hl; omega
  have h2 : l ≠ j' := fun h => by rw [h] at hl; omega
  have h3 : l' ≠ j := fun h => by rw [h] at hl'; omega
  have h4 : l' ≠ j' := fun h => by rw [h] at hl'; omega
  have := fin_val_ne h1
  have := fin_val_ne h2
  have := fin_val_ne h3
  have := fin_val_ne h4
  have := fin_val_ne hl'ne
  have := fin_val_ne hj'ne
  have : (l : ℕ) < 3 := l.isLt
  have : (l' : ℕ) < 3 := l'.isLt
  have : (j : ℕ) < 3 := j.isLt
  have : (j' : ℕ) < 3 := j'.isLt
  omega

/-! ### Progress -/

/-- What HL's levelset subprocedure must achieve: an upward point at level at least
`k`, a downward point at level at most `k`, or (in the total setting) a witnessed
violation of order preservation.

Either of the first two halves the search space, by `Basic.lean`'s Lemma 4. -/
def HasProgress (F : Pt d → Pt d) (lo hi : Pt d) (k : ℕ) : Prop :=
  (∃ x, x ∈ Box lo hi ∧ k ≤ lev x ∧ x ∈ Up F)
    ∨ (∃ x, x ∈ Box lo hi ∧ lev x ≤ k ∧ x ∈ Down F)
    ∨ (∃ u v, u ∈ Box lo hi ∧ v ∈ Box lo hi ∧ IsVop F u v)

lemma HasProgress.mono {F : Pt d → Pt d} {lo hi lo' hi' : Pt d} (hl : lo ≤ lo') (hh : hi' ≤ hi)
    {k : ℕ} (h : HasProgress F lo' hi' k) : HasProgress F lo hi k := by
  rcases h with ⟨x, hx, hk, hu⟩ | ⟨x, hx, hk, hu⟩ | ⟨u, v, hu, hv, hvop⟩
  · exact Or.inl ⟨x, Box_subset hl hh hx, hk, hu⟩
  · exact Or.inr (Or.inl ⟨x, Box_subset hl hh hx, hk, hu⟩)
  · exact Or.inr (Or.inr ⟨u, v, Box_subset hl hh hu, Box_subset hl hh hv, hvop⟩)

/-! ### HL Observation 3.9 (first configuration) -/

/-- HL Definition 3.7, upward form: `x` is `i`-upward, `y` is `j`-upward, and they
"cross" in the two dimensions, `yᵢ ≤ xᵢ` and `xⱼ ≤ yⱼ`. -/
structure Config1Up (F : Pt 3 → Pt 3) (i j : Fin 3) (x y : Pt 3) : Prop where
  /-- The two dimensions are distinct. -/
  ne : i ≠ j
  /-- `x` is `i`-upward. -/
  hx : IUp F x i
  /-- `y` is `j`-upward. -/
  hy : IUp F y j
  /-- They cross in dimension `i`. -/
  cross_i : y i ≤ x i
  /-- They cross in dimension `j`. -/
  cross_j : x j ≤ y j

/-- HL Definition 3.7, downward form. -/
structure Config1Down (F : Pt 3 → Pt 3) (i j : Fin 3) (x y : Pt 3) : Prop where
  /-- The two dimensions are distinct. -/
  ne : i ≠ j
  /-- `x` is `i`-downward. -/
  hx : IDown F x i
  /-- `y` is `j`-downward. -/
  hy : IDown F y j
  /-- They cross in dimension `i`. -/
  cross_i : x i ≤ y i
  /-- They cross in dimension `j`. -/
  cross_j : y j ≤ x j

/-- **HL Observation 3.9**, upward form.  From a first configuration the meet is a
downward point at level at most `k` — unless one of the two monotonicity steps
fails, which exhibits a violation.

HL state the conclusion as a disjunction ("either `GLB` is downward or `LUB` is
upward"); the argument in fact always delivers the meet in the upward form of the
configuration, and always the join in the downward form. -/
theorem hasProgress_of_config1Up {F : Pt 3 → Pt 3} {lo hi : Pt 3} {i j : Fin 3} {x y : Pt 3}
    (hxbox : x ∈ Box lo hi) (hybox : y ∈ Box lo hi) {k : ℕ} (hxk : lev x = k)
    (h : Config1Up F i j x y) : HasProgress F lo hi k := by
  have hmbox : glb x y ∈ Box lo hi := glb_mem_Box hxbox hybox
  by_cases hmx : ¬ F (glb x y) ≤ F x
  · exact Or.inr (Or.inr ⟨glb x y, x, hmbox, hxbox, ⟨glb_le_left x y, hmx⟩⟩)
  by_cases hmy : ¬ F (glb x y) ≤ F y
  · exact Or.inr (Or.inr ⟨glb x y, y, hmbox, hybox, ⟨glb_le_right x y, hmy⟩⟩)
  push Not at hmx hmy
  -- The meet is downward: in dimension `i` use `y`, in dimension `j` use `x`, and
  -- in the third dimension both bounds are available.
  refine Or.inr (Or.inl ⟨glb x y, hmbox, ?_, mem_Down.mpr (coord_le fun l => ?_)⟩)
  · rw [← hxk]; exact lev_mono (glb_le_left x y)
  · have hbx : F (glb x y) l ≤ F x l := le_coord hmx l
    have hby : F (glb x y) l ≤ F y l := le_coord hmy l
    simp only [glb_apply]
    by_cases hli : l = i
    · subst hli
      have h1 := h.hy.2 l h.ne
      have h2 := h.cross_i
      omega
    · by_cases hlj : l = j
      · subst hlj
        have h1 := h.hx.2 l hli
        have h2 := h.cross_j
        omega
      · have h1 := h.hx.2 l hli
        have h2 := h.hy.2 l hlj
        omega

/-- **HL Observation 3.9**, downward form: the join is an upward point at level at
least `k`. -/
theorem hasProgress_of_config1Down {F : Pt 3 → Pt 3} {lo hi : Pt 3} {i j : Fin 3} {x y : Pt 3}
    (hxbox : x ∈ Box lo hi) (hybox : y ∈ Box lo hi) {k : ℕ} (hxk : lev x = k)
    (h : Config1Down F i j x y) : HasProgress F lo hi k := by
  have hmbox : lub x y ∈ Box lo hi := lub_mem_Box hxbox hybox
  by_cases hmx : ¬ F x ≤ F (lub x y)
  · exact Or.inr (Or.inr ⟨x, lub x y, hxbox, hmbox, ⟨left_le_lub x y, hmx⟩⟩)
  by_cases hmy : ¬ F y ≤ F (lub x y)
  · exact Or.inr (Or.inr ⟨y, lub x y, hybox, hmbox, ⟨right_le_lub x y, hmy⟩⟩)
  push Not at hmx hmy
  refine Or.inl ⟨lub x y, hmbox, ?_, mem_Up.mpr (coord_le fun l => ?_)⟩
  · rw [← hxk]; exact lev_mono (left_le_lub x y)
  · have hbx : F x l ≤ F (lub x y) l := le_coord hmx l
    have hby : F y l ≤ F (lub x y) l := le_coord hmy l
    simp only [lub_apply]
    by_cases hli : l = i
    · subst hli
      have h1 := h.hy.2 l h.ne
      have h2 := h.cross_i
      omega
    · by_cases hlj : l = j
      · subst hlj
        have h1 := h.hx.2 l hli
        have h2 := h.cross_j
        omega
      · have h1 := h.hx.2 l hli
        have h2 := h.hy.2 l hlj
        omega

/-! ### HL Observation 3.10 (second configuration) -/

/-- HL Definition 3.8, upward form: a cyclic crossing of three `i`-upward points. -/
structure Config2Up (F : Pt 3 → Pt 3) (i j p : Fin 3) (x y z : Pt 3) : Prop where
  /-- `i ≠ j`. -/
  ij : i ≠ j
  /-- `i ≠ p`. -/
  ip : i ≠ p
  /-- `j ≠ p`. -/
  jp : j ≠ p
  /-- `x` is `i`-upward. -/
  hx : IUp F x i
  /-- `y` is `j`-upward. -/
  hy : IUp F y j
  /-- `z` is `p`-upward. -/
  hz : IUp F z p
  /-- `yᵢ ≤ xᵢ`. -/
  cross_i : y i ≤ x i
  /-- `zⱼ ≤ yⱼ`. -/
  cross_j : z j ≤ y j
  /-- `x_p ≤ z_p`. -/
  cross_p : x p ≤ z p

/-- HL Definition 3.8, downward form. -/
structure Config2Down (F : Pt 3 → Pt 3) (i j p : Fin 3) (x y z : Pt 3) : Prop where
  /-- `i ≠ j`. -/
  ij : i ≠ j
  /-- `i ≠ p`. -/
  ip : i ≠ p
  /-- `j ≠ p`. -/
  jp : j ≠ p
  /-- `x` is `i`-downward. -/
  hx : IDown F x i
  /-- `y` is `j`-downward. -/
  hy : IDown F y j
  /-- `z` is `p`-downward. -/
  hz : IDown F z p
  /-- `xᵢ ≤ yᵢ`. -/
  cross_i : x i ≤ y i
  /-- `yⱼ ≤ zⱼ`. -/
  cross_j : y j ≤ z j
  /-- `z_p ≤ x_p`. -/
  cross_p : z p ≤ x p

/-- **HL Observation 3.10**, upward form: from a second configuration the meet of
the three points is downward at level at most `k`, unless a monotonicity step
fails. -/
theorem hasProgress_of_config2Up {F : Pt 3 → Pt 3} {lo hi : Pt 3} {i j p : Fin 3} {x y z : Pt 3}
    (hxbox : x ∈ Box lo hi) (hybox : y ∈ Box lo hi) (hzbox : z ∈ Box lo hi)
    {k : ℕ} (hxk : lev x = k) (h : Config2Up F i j p x y z) : HasProgress F lo hi k := by
  set m := glb (glb x y) z with hm
  have hmx : m ≤ x := (glb_le_left _ _).trans (glb_le_left x y)
  have hmy : m ≤ y := (glb_le_left _ _).trans (glb_le_right x y)
  have hmz : m ≤ z := glb_le_right _ _
  have hmbox : m ∈ Box lo hi := glb_mem_Box (glb_mem_Box hxbox hybox) hzbox
  by_cases hbx : ¬ F m ≤ F x
  · exact Or.inr (Or.inr ⟨m, x, hmbox, hxbox, ⟨hmx, hbx⟩⟩)
  by_cases hby : ¬ F m ≤ F y
  · exact Or.inr (Or.inr ⟨m, y, hmbox, hybox, ⟨hmy, hby⟩⟩)
  by_cases hbz : ¬ F m ≤ F z
  · exact Or.inr (Or.inr ⟨m, z, hmbox, hzbox, ⟨hmz, hbz⟩⟩)
  push Not at hbx hby hbz
  refine Or.inr (Or.inl ⟨m, hmbox, ?_, mem_Down.mpr (coord_le fun l => ?_)⟩)
  · rw [← hxk]; exact lev_mono hmx
  · have h1 : F m l ≤ F x l := le_coord hbx l
    have h2 : F m l ≤ F y l := le_coord hby l
    have h3 : F m l ≤ F z l := le_coord hbz l
    have hml : m l = min (min (x l) (y l)) (z l) := rfl
    rcases fin3_cover h.ij h.ip h.jp l with rfl | rfl | rfl
    · -- dimension `i`: use `y` and `z`, and `yᵢ ≤ xᵢ`
      have hy' := h.hy.2 l h.ij
      have hz' := h.hz.2 l h.ip
      have := h.cross_i
      omega
    · -- dimension `j`: use `x` and `z`, and `zⱼ ≤ yⱼ`
      have hx' := h.hx.2 l (Ne.symm h.ij)
      have hz' := h.hz.2 l h.jp
      have := h.cross_j
      omega
    · -- dimension `p`: use `x` and `y`, and `x_p ≤ z_p`
      have hx' := h.hx.2 l (Ne.symm h.ip)
      have hy' := h.hy.2 l (Ne.symm h.jp)
      have := h.cross_p
      omega

/-- **HL Observation 3.10**, downward form: the join of the three points is upward
at level at least `k`. -/
theorem hasProgress_of_config2Down {F : Pt 3 → Pt 3} {lo hi : Pt 3} {i j p : Fin 3} {x y z : Pt 3}
    (hxbox : x ∈ Box lo hi) (hybox : y ∈ Box lo hi) (hzbox : z ∈ Box lo hi)
    {k : ℕ} (hxk : lev x = k) (h : Config2Down F i j p x y z) : HasProgress F lo hi k := by
  set M := lub (lub x y) z with hM
  have hxM : x ≤ M := (left_le_lub x y).trans (left_le_lub _ _)
  have hyM : y ≤ M := (right_le_lub x y).trans (left_le_lub _ _)
  have hzM : z ≤ M := right_le_lub _ _
  have hMbox : M ∈ Box lo hi := lub_mem_Box (lub_mem_Box hxbox hybox) hzbox
  by_cases hbx : ¬ F x ≤ F M
  · exact Or.inr (Or.inr ⟨x, M, hxbox, hMbox, ⟨hxM, hbx⟩⟩)
  by_cases hby : ¬ F y ≤ F M
  · exact Or.inr (Or.inr ⟨y, M, hybox, hMbox, ⟨hyM, hby⟩⟩)
  by_cases hbz : ¬ F z ≤ F M
  · exact Or.inr (Or.inr ⟨z, M, hzbox, hMbox, ⟨hzM, hbz⟩⟩)
  push Not at hbx hby hbz
  refine Or.inl ⟨M, hMbox, ?_, mem_Up.mpr (coord_le fun l => ?_)⟩
  · rw [← hxk]; exact lev_mono hxM
  · have h1 : F x l ≤ F M l := le_coord hbx l
    have h2 : F y l ≤ F M l := le_coord hby l
    have h3 : F z l ≤ F M l := le_coord hbz l
    have hMl : M l = max (max (x l) (y l)) (z l) := rfl
    rcases fin3_cover h.ij h.ip h.jp l with rfl | rfl | rfl
    · have hy' := h.hy.2 l h.ij
      have hz' := h.hz.2 l h.ip
      have := h.cross_i
      omega
    · have hx' := h.hx.2 l (Ne.symm h.ij)
      have hz' := h.hz.2 l h.jp
      have := h.cross_j
      omega
    · have hx' := h.hx.2 l (Ne.symm h.ip)
      have hy' := h.hy.2 l (Ne.symm h.jp)
      have := h.cross_p
      omega

/-! ### HL Definition 3.11 (third configuration)

Unlike the first two, this one does not immediately produce a point; HL Lemma 3.13
extracts progress from it with a further `O(log N)` binary search.  See
`Tfnp/Tarski/LevelsetSearch.lean`. -/

/-- HL Definition 3.11: `x` is `i`-upward, `y` is `i`-downward, and they are within
one of each other in dimension `i`. -/
structure Config3 (F : Pt 3 → Pt 3) (i : Fin 3) (x y : Pt 3) : Prop where
  /-- `x` is `i`-upward. -/
  hx : IUp F x i
  /-- `y` is `i`-downward. -/
  hy : IDown F y i
  /-- `xᵢ ≤ yᵢ`. -/
  le : x i ≤ y i
  /-- `yᵢ ≤ xᵢ + 1`. -/
  close : y i ≤ x i + 1

/-! ### The levelset subprocedure interface -/

/-- Correctness of a levelset subprocedure on the box `[lo, hi]` at level `k`. -/
def IsLevelsetSol (F : Pt d → Pt d) (lo hi : Pt d) (k : ℕ) : InnerAnswer d → Prop
  | .up p => p ∈ Box lo hi ∧ k ≤ lev p ∧ p ∈ Up F
  | .down p => p ∈ Box lo hi ∧ lev p ≤ k ∧ p ∈ Down F
  | .vop x y => x ∈ Box lo hi ∧ y ∈ Box lo hi ∧ IsVop F x y

lemma hasProgress_of_isLevelsetSol {F : Pt d → Pt d} {lo hi : Pt d} {k : ℕ}
    {ans : InnerAnswer d} (h : IsLevelsetSol F lo hi k ans) : HasProgress F lo hi k := by
  cases ans with
  | up p => exact Or.inl ⟨p, h.1, h.2.1, h.2.2⟩
  | down p => exact Or.inr (Or.inl ⟨p, h.1, h.2.1, h.2.2⟩)
  | vop x y => exact Or.inr (Or.inr ⟨x, y, h.1, h.2.1, h.2.2⟩)

/-- A levelset subprocedure family for the ambient box `[LO, HI]`. -/
def SolvesLevelset (algOf : Pt d → Pt d → ℕ → QueryAlg (Pt d) (Pt d) (InnerAnswer d))
    (LO HI : Pt d) : Prop :=
  ∀ (F : Pt d → Pt d) (lo hi : Pt d) (k : ℕ),
    LO ≤ lo → lo ≤ hi → hi ≤ HI → lo ∈ Up F → hi ∈ Down F → lev lo ≤ k → k ≤ lev hi →
      IsLevelsetSol F lo hi k ((algOf lo hi k).run F)

/-! ### HL Lemma 3.2: the outer recursion

Given the subprocedure, binary-search on the level.  Cutting at
`k = lev lo + ⌈span/2⌉` makes *both* outcomes shrink `boxSize` to at most
`⌈span/2⌉`, since `boxSize` is exactly the range of levels
(`boxSize_eq_lev_sub`).  Note this argument is dimension-independent. -/

/-- The terminal call: once `boxSize lo hi ≤ 1`, two queries suffice. -/
noncomputable def levTerminal (lo hi : Pt d) : QueryAlg (Pt d) (Pt d) (Answer d) :=
  intervalAlg hi 2 lo lo

lemma levTerminal_bounded (lo hi : Pt d) : Bounded 2 (levTerminal lo hi) :=
  intervalAlg_bounded hi 2 lo lo

lemma levTerminal_isSol {F : Pt d → Pt d} {lo hi : Pt d} (hlohi : lo ≤ hi)
    (hlo : lo ∈ Up F) (hhi : hi ∈ Down F) (hsmall : boxSize lo hi ≤ 1) :
    IsSol F lo hi ((levTerminal lo hi).run F) :=
  intervalAlg_isSol F hhi 2 lo lo (by omega) le_rfl le_rfl hlohi (fun hnot => absurd hlo hnot)

/-- The outer recursion of HL Lemma 3.2, with an explicit budget on the number of
halvings. -/
noncomputable def levelsetOuterAux
    (algOf : Pt d → Pt d → ℕ → QueryAlg (Pt d) (Pt d) (InnerAnswer d)) :
    ℕ → Pt d → Pt d → QueryAlg (Pt d) (Pt d) (Answer d)
  | 0, lo, hi => levTerminal lo hi
  | n + 1, lo, hi =>
      if 2 ≤ boxSize lo hi then
        algOf lo hi (lev lo + (boxSize lo hi + 1) / 2) >>= fun ans =>
          match ans with
          | .vop x y => QueryAlg.pure (.inr (x, y))
          | .up p => levelsetOuterAux algOf n p hi
          | .down p => levelsetOuterAux algOf n lo p
      else levTerminal lo hi

lemma levelsetOuterAux_succ
    (algOf : Pt d → Pt d → ℕ → QueryAlg (Pt d) (Pt d) (InnerAnswer d))
    (n : ℕ) (lo hi : Pt d) :
    levelsetOuterAux algOf (n + 1) lo hi =
      (if 2 ≤ boxSize lo hi then
        algOf lo hi (lev lo + (boxSize lo hi + 1) / 2) >>= fun ans =>
          match ans with
          | .vop x y => QueryAlg.pure (.inr (x, y))
          | .up p => levelsetOuterAux algOf n p hi
          | .down p => levelsetOuterAux algOf n lo p
      else levTerminal lo hi) := rfl

/-- The algorithm: `⌈log₂ (boxSize lo hi)⌉` halvings suffice. -/
noncomputable def levelsetOuter
    (algOf : Pt d → Pt d → ℕ → QueryAlg (Pt d) (Pt d) (InnerAnswer d)) (lo hi : Pt d) :
    QueryAlg (Pt d) (Pt d) (Answer d) :=
  levelsetOuterAux algOf (Nat.clog 2 (boxSize lo hi)) lo hi

lemma levelsetOuterAux_bounded
    {algOf : Pt d → Pt d → ℕ → QueryAlg (Pt d) (Pt d) (InnerAnswer d)} {q : ℕ}
    (hq : ∀ lo hi k, Bounded q (algOf lo hi k)) :
    ∀ (n : ℕ) (lo hi : Pt d), Bounded (n * q + 2) (levelsetOuterAux algOf n lo hi) := by
  intro n
  induction n with
  | zero => intro lo hi; simpa using levTerminal_bounded lo hi
  | succ n ih =>
    intro lo hi
    rw [levelsetOuterAux_succ]
    by_cases h : 2 ≤ boxSize lo hi
    · rw [if_pos h]
      refine Bounded.mono (n := q + (n * q + 2)) ((hq _ _ _).bind fun ans => ?_)
        (by rw [Nat.succ_mul]; omega)
      cases ans with
      | vop x y => exact Bounded.pure' _ _
      | up p => exact ih p hi
      | down p => exact ih lo p
    · rw [if_neg h]
      exact (levTerminal_bounded lo hi).mono (by omega)

/-- **HL Lemma 3.2** (query bound). -/
theorem levelsetOuter_bounded
    {algOf : Pt d → Pt d → ℕ → QueryAlg (Pt d) (Pt d) (InnerAnswer d)} {q : ℕ}
    (hq : ∀ lo hi k, Bounded q (algOf lo hi k)) (lo hi : Pt d) :
    Bounded (Nat.clog 2 (boxSize lo hi) * q + 2) (levelsetOuter algOf lo hi) :=
  levelsetOuterAux_bounded hq _ lo hi

lemma levelsetOuterAux_isSol {F : Pt d → Pt d}
    {algOf : Pt d → Pt d → ℕ → QueryAlg (Pt d) (Pt d) (InnerAnswer d)}
    {LO HI : Pt d} (hLS : SolvesLevelset algOf LO HI) :
    ∀ (n : ℕ) (lo hi : Pt d), Nat.clog 2 (boxSize lo hi) ≤ n → LO ≤ lo → lo ≤ hi → hi ≤ HI →
      lo ∈ Up F → hi ∈ Down F →
      IsSol F lo hi ((levelsetOuterAux algOf n lo hi).run F) := by
  intro n
  induction n with
  | zero =>
    intro lo hi hsize _ hlohi _ hlo hhi
    refine levTerminal_isSol hlohi hlo hhi ?_
    -- `⌈log₂ span⌉ = 0` forces `span ≤ 1`
    by_contra hc
    push Not at hc
    have hpos : 0 < Nat.clog 2 (boxSize lo hi) := Nat.clog_pos (by norm_num) (by omega)
    omega
  | succ n ih =>
    intro lo hi hsize hLO hlohi hHI hlo hhi
    rw [levelsetOuterAux_succ]
    by_cases h : 2 ≤ boxSize lo hi
    · rw [if_pos h]
      set t := (boxSize lo hi + 1) / 2 with ht
      set k := lev lo + t with hk
      have hspan : boxSize lo hi = lev hi - lev lo := boxSize_eq_lev_sub hlohi
      have hlevle : lev lo ≤ lev hi := lev_mono hlohi
      have hkbounds : lev lo ≤ k ∧ k ≤ lev hi := by
        rw [hk, ht]; omega
      -- The halving: `⌈log₂ ⌈span/2⌉⌉ < ⌈log₂ span⌉`.
      have hclog : Nat.clog 2 t < Nat.clog 2 (boxSize lo hi) := by
        have harg : (boxSize lo hi + 2 - 1) / 2 = t := by rw [ht]; omega
        have hrec := Nat.clog_of_two_le (b := 2) (n := boxSize lo hi) (by norm_num) h
        rw [harg] at hrec
        omega
      have hans := hLS F lo hi k hLO hlohi hHI hlo hhi hkbounds.1 hkbounds.2
      rw [QueryAlg.run_bind]
      rcases hres : (algOf lo hi k).run F with p | p | ⟨u, v⟩
      · -- upward point at level ≥ k: recurse on `[p, hi]`
        rw [hres] at hans
        obtain ⟨hpbox, hpk, hpup⟩ := hans
        obtain ⟨hlop, hphi⟩ := mem_Box.mp hpbox
        have hnew : boxSize p hi ≤ t := by
          rw [boxSize_eq_lev_sub hphi]
          have := lev_mono hphi
          rw [hk] at hpk
          omega
        refine IsSol.mono hlop le_rfl
          (ih p hi ?_ (hLO.trans hlop) hphi hHI hpup hhi)
        have := Nat.clog_mono_right 2 hnew
        omega
      · -- downward point at level ≤ k: recurse on `[lo, p]`
        rw [hres] at hans
        obtain ⟨hpbox, hpk, hpdown⟩ := hans
        obtain ⟨hlop, hphi⟩ := mem_Box.mp hpbox
        have hnew : boxSize lo p ≤ t := by
          rw [boxSize_eq_lev_sub hlop]
          have := lev_mono hlop
          rw [hk] at hpk
          omega
        refine IsSol.mono le_rfl hphi
          (ih lo p ?_ hLO hlop (hphi.trans hHI) hlo hpdown)
        have := Nat.clog_mono_right 2 hnew
        omega
      · -- a violation
        rw [hres] at hans
        exact hans
    · rw [if_neg h]
      exact levTerminal_isSol hlohi hlo hhi (by omega)

/-- **HL Lemma 3.2** (correctness).  A levelset subprocedure yields a Tarski
algorithm.  The recursion is dimension-independent: only the subprocedure is
special to `d = 3`. -/
theorem levelsetOuter_isSol {F : Pt d → Pt d}
    {algOf : Pt d → Pt d → ℕ → QueryAlg (Pt d) (Pt d) (InnerAnswer d)}
    {lo hi : Pt d} (hLS : SolvesLevelset algOf lo hi) (hlohi : lo ≤ hi)
    (hlo : lo ∈ Up F) (hhi : hi ∈ Down F) :
    IsSol F lo hi ((levelsetOuter algOf lo hi).run F) :=
  levelsetOuterAux_isSol hLS _ lo hi le_rfl le_rfl hlohi le_rfl hlo hhi

/-- A levelset subprocedure family gives a `SolvesUpDown` family — the interface
the FPS decomposition theorem consumes. -/
theorem solvesUpDown_levelsetOuter
    {algOf : Pt d → Pt d → ℕ → QueryAlg (Pt d) (Pt d) (InnerAnswer d)} {LO HI : Pt d}
    (hLS : SolvesLevelset algOf LO HI) :
    SolvesUpDown (fun l u => levelsetOuter algOf l u) LO HI := by
  intro F l u hLl hlu huH hl hu
  exact levelsetOuterAux_isSol (LO := LO) (HI := HI) hLS _ l u le_rfl hLl hlu huH hl hu

/-! ### A uniform-budget variant

`levelsetOuter` sizes its own budget from `boxSize lo hi`, so its `Bounded` bound
depends on the box.  For composing with the decomposition theorem — whose
hypothesis is a *single* bound valid for every sub-box — we need a fixed budget. -/

/-- The outer recursion with an externally supplied budget. -/
noncomputable def levelsetSolver
    (algOf : Pt d → Pt d → ℕ → QueryAlg (Pt d) (Pt d) (InnerAnswer d)) (budget : ℕ)
    (lo hi : Pt d) : QueryAlg (Pt d) (Pt d) (Answer d) :=
  levelsetOuterAux algOf budget lo hi

lemma levelsetSolver_bounded
    {algOf : Pt d → Pt d → ℕ → QueryAlg (Pt d) (Pt d) (InnerAnswer d)} {q : ℕ}
    (hq : ∀ lo hi k, Bounded q (algOf lo hi k)) (budget : ℕ) (lo hi : Pt d) :
    Bounded (budget * q + 2) (levelsetSolver algOf budget lo hi) :=
  levelsetOuterAux_bounded hq budget lo hi

/-- With a budget covering every sub-box, the levelset recursion is a
`SolvesUpDown` family — exactly what the FPS decomposition theorem consumes. -/
theorem solvesUpDown_levelsetSolver
    {algOf : Pt d → Pt d → ℕ → QueryAlg (Pt d) (Pt d) (InnerAnswer d)} {LO HI : Pt d}
    {budget : ℕ} (hLS : SolvesLevelset algOf LO HI)
    (hbud : ∀ l u : Pt d, LO ≤ l → l ≤ u → u ≤ HI → Nat.clog 2 (boxSize l u) ≤ budget) :
    SolvesUpDown (levelsetSolver algOf budget) LO HI := by
  intro F l u hLl hlu huH hl hu
  exact levelsetOuterAux_isSol (LO := LO) (HI := HI) hLS budget l u
    (hbud l u hLl hlu huH) hLl hlu huH hl hu

end Tfnp.Tarski
