/-
Copyright (c) 2026 Angus Joshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Angus Joshi
-/
import Mathlib
import Tfnp.QueryModel

/-!
# The Tarski fixed-point problem

The Tarski problem (Etessami–Papadimitriou–Rubinstein–Yannakakis, [arXiv:1909.03210];
clean presentation in Fearnley–Savani, [arXiv:2202.05913]):

> Given black-box query access to a **monotone** map `f : [0..N]^d → [0..N]^d`
> (componentwise order), find a fixed point `x : f x = x`.

By Tarski–Knaster, such a fixed point always exists — in fact `f.lfp ∈ fixedPoints f`
(mathlib's `OrderHom.lfp` discharges this immediately).  The problem is interesting
in the **query model**: how many oracle queries to `f` are needed to find a fixed
point?

## What this file contains

1. **Problem definition.**  The grid `L N d := Fin d → Fin (N+1)`, the structure
   `TarskiInstance` bundling a monotone `f`, and `IsFixedPt`. Tarski's existence
   theorem `exists_fixedPt` follows from `OrderHom.lfp`.

2. **Iterative algorithm** (`iterativeQuery`): query `f` at `x`, replace `x` by
   the response, repeat from `x = ⊥`. We prove the worst-case query bound
   `d · N + 1` via the coordinate-sum potential.

3. **Recursive binary-search algorithm** (Dang–Qi–Ye, [DQY 1999]; `dqyBox`,
   `dqyQuery`): operates on a *subbox* `[lo, hi]` of `L N d`.  In dimension
   `d+1`, binary-search on coordinate 0 with midpoint `m`; the slice
   subroutine `dqyBox d` (on `[Fin.tail lo, Fin.tail hi]`, lifted via
   `liftToSlice`) returns a slice fixed point `z`; query `f (cons m z)` and
   either return or recurse on a strictly smaller subbox `[lo, fz]` (descending
   halving) or `[fz, hi]` (ascending halving).  The framework lemma
   `MapsToBox.{upper,lower}_of_{asc,desc}Mono` proves the subbox invariant is
   maintained.

   * **Query bound** `(Nat.log 2 (N + 1) + 2)^d` (i.e. `O((log N)^d)`) —
     **proved** (`dqyBox_queries_succ_le`, `dqyQuery_queries_le`).
   * **Correctness** (`dqyBox_isFixedPt`, `dqyQuery_isFixedPt`) —
     **proved** by dimension induction on `d` (base case via `Subsingleton
     (L N 0)`), then budget induction on `dqyBoxAux` (base case pinned-coord
     via `dqyProbe_isFixedPt_pinned`; inductive case by case-split on
     `fz 0` vs midpoint, using `MapsToBox.{upper,lower}_of_{asc,desc}Mono`
     to maintain the subbox invariant and the strict-halving identity
     `(r + 1) / 2 ≤ 2^b` to track the budget).

4. **Lower bound** (Etessami–Papadimitriou–Rubinstein–Yannakakis): any
   deterministic adaptive query algorithm needs `Ω((log (N+1))^d)` queries on
   the worst-case instance. Stated; proof sketch + `sorry`.

References:
* K. Etessami, C. Papadimitriou, A. Rubinstein, M. Yannakakis.
  *Tarski's theorem, supermodular games, and the complexity of equilibria.*
  arXiv:1909.03210 (2019).
* J. Fearnley, R. Savani. *A faster algorithm for finding Tarski fixed points.*
  arXiv:2202.05913 (2022).
* C. Dang, Q. Qi, Y. Ye. *Computational models and complexities of Tarski's
  fixed points.* (1999).
-/

namespace Tfnp
namespace Tarski

/-- The `d`-dimensional integer grid `{0, 1, …, N}^d`, encoded as `Fin d → Fin (N+1)`.
The componentwise order makes it a finite complete lattice with `⊥ = (fun _ => 0)`
and `⊤ = (fun _ => N)`. -/
abbrev L (N d : ℕ) : Type := Fin d → Fin (N + 1)

variable {N d : ℕ}

/-- An instance of the Tarski fixed-point problem: a monotone self-map of the grid. -/
structure TarskiInstance (N d : ℕ) where
  /-- The monotone self-map. -/
  f : L N d → L N d
  /-- Monotonicity (componentwise). -/
  mono : Monotone f

namespace TarskiInstance

variable (T : TarskiInstance N d)

/-- `x` is a fixed point of `T.f`. -/
def IsFixedPt (x : L N d) : Prop := T.f x = x

end TarskiInstance

/-! ### Existence (Tarski–Knaster) -/

/-- **Tarski's fixed-point theorem.** Every monotone map on the finite grid
`[0..N]^d` has a fixed point. Inherited from `OrderHom.lfp`. -/
theorem exists_fixedPt (T : TarskiInstance N d) :
    ∃ x : L N d, T.IsFixedPt x :=
  let f' : L N d →o L N d := ⟨T.f, T.mono⟩
  ⟨f'.lfp, f'.map_lfp⟩

/-! ### Subboxes and monotone points

A **subbox** is a `Set.Icc lo hi`.  A point `x` is an *ascending* monotone
point of `f` if `x ≤ f x`, and a *descending* monotone point if `f x ≤ x`.

**Key restriction lemma** (`Monotone.mapsToBox_upper` / `_lower`): when `f` is
monotone, maps `[lo, hi]` to `[lo, hi]`, and `x ∈ [lo, hi]` is ascending (resp.
descending), then `f` maps `[x, hi]` (resp. `[lo, x]`) to itself.

This is the inductive engine of DQY: each binary-search step produces a
monotone point, and the recursion proceeds on a strictly smaller subbox. -/

/-- `f` maps the subbox `[lo, hi]` into itself. -/
def MapsToBox (f : L N d → L N d) (lo hi : L N d) : Prop :=
  ∀ x, lo ≤ x → x ≤ hi → lo ≤ f x ∧ f x ≤ hi

/-- `x` is an *ascending* monotone point of `f`: `x ≤ f x`. -/
def IsAscMono (f : L N d → L N d) (x : L N d) : Prop := x ≤ f x

/-- `x` is a *descending* monotone point of `f`: `f x ≤ x`. -/
def IsDescMono (f : L N d → L N d) (x : L N d) : Prop := f x ≤ x

/-- **Restriction at an ascending point.**  If `f` maps `[lo, hi]` to itself
and `x ∈ [lo, hi]` is ascending, then `f` maps `[x, hi]` to itself. -/
lemma MapsToBox.upper_of_ascMono {f : L N d → L N d} (hf : Monotone f)
    {lo hi x : L N d} (hxlo : lo ≤ x) (_hxhi : x ≤ hi)
    (hbox : MapsToBox f lo hi) (hx_asc : IsAscMono f x) :
    MapsToBox f x hi := by
  intro y hxy hyhi
  refine ⟨?_, ?_⟩
  · exact hx_asc.trans (hf hxy)
  · exact (hbox y (le_trans hxlo hxy) hyhi).2

/-- **Restriction at a descending point.**  If `f` maps `[lo, hi]` to itself
and `x ∈ [lo, hi]` is descending, then `f` maps `[lo, x]` to itself. -/
lemma MapsToBox.lower_of_descMono {f : L N d → L N d} (hf : Monotone f)
    {lo hi x : L N d} (_hxlo : lo ≤ x) (hxhi : x ≤ hi)
    (hbox : MapsToBox f lo hi) (hx_desc : IsDescMono f x) :
    MapsToBox f lo x := by
  intro y hloy hyx
  refine ⟨?_, ?_⟩
  · exact (hbox y hloy (le_trans hyx hxhi)).1
  · exact (hf hyx).trans hx_desc

/-- Pointwise comparison `Fin.cons m y ≤ x` iff coord-0 and tail comparisons hold. -/
lemma cons_le_iff {m : Fin (N + 1)} {y : L N d} {x : L N (d + 1)} :
    Fin.cons m y ≤ x ↔ m ≤ x 0 ∧ y ≤ Fin.tail x := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun ⟨h0, htail⟩ i => Fin.cases ?_ ?_ i⟩
  · simpa using h 0
  · intro j; simpa [Fin.tail] using h j.succ
  · simpa using h0
  · intro j; simpa [Fin.tail] using htail j

/-- Pointwise comparison `x ≤ Fin.cons m y` iff coord-0 and tail comparisons hold. -/
lemma le_cons_iff {x : L N (d + 1)} {m : Fin (N + 1)} {y : L N d} :
    x ≤ Fin.cons m y ↔ x 0 ≤ m ∧ Fin.tail x ≤ y := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun ⟨h0, htail⟩ i => Fin.cases ?_ ?_ i⟩
  · simpa using h 0
  · intro j; simpa [Fin.tail] using h j.succ
  · simpa using h0
  · intro j; simpa [Fin.tail] using htail j

/-! #### The lifted oracle and its properties

For the slice-at-coordinate-0 step of DQY, we need the lifted oracle
`g_m(y) := Fin.tail (f (Fin.cons m y))`.  It inherits monotonicity from `f`
and maps the slice subbox `[Fin.tail lo, Fin.tail hi]` to itself whenever
`f` maps `[lo, hi]` to itself with `m ∈ [lo 0, hi 0]`. -/

/-- The slice-lifted oracle. -/
private def liftedOracle (m : Fin (N + 1)) (f : L N (d + 1) → L N (d + 1)) : L N d → L N d :=
  fun y => Fin.tail (f (Fin.cons m y))

private lemma liftedOracle_monotone {m : Fin (N + 1)} {f : L N (d + 1) → L N (d + 1)}
    (hf : Monotone f) : Monotone (liftedOracle m f) := by
  intro y1 y2 hy
  unfold liftedOracle
  intro i
  simp only [Fin.tail]
  apply hf
  intro j
  refine Fin.cases ?_ ?_ j
  · simp only [Fin.cons_zero]; exact le_refl _
  · intro k; simp only [Fin.cons_succ]; exact hy k

private lemma liftedOracle_mapsToBox {m : Fin (N + 1)} {f : L N (d + 1) → L N (d + 1)}
    {lo hi : L N (d + 1)} (hbox : MapsToBox f lo hi)
    (hm_lo : (lo 0 : ℕ) ≤ (m : ℕ)) (hm_hi : (m : ℕ) ≤ (hi 0 : ℕ)) :
    MapsToBox (liftedOracle m f) (Fin.tail lo) (Fin.tail hi) := by
  intro y hy_lo hy_hi
  have h_cons_lo : lo ≤ Fin.cons m y :=
    le_cons_iff.mpr ⟨Fin.le_iff_val_le_val.mpr hm_lo, hy_lo⟩
  have h_cons_hi : Fin.cons m y ≤ hi :=
    cons_le_iff.mpr ⟨Fin.le_iff_val_le_val.mpr hm_hi, hy_hi⟩
  have hfcons := hbox (Fin.cons m y) h_cons_lo h_cons_hi
  exact ⟨fun i => hfcons.1 i.succ, fun i => hfcons.2 i.succ⟩

/-! ### The iterative algorithm

Starting from `⊥`, repeatedly apply `f`. The sequence is monotone increasing,
the **coordinate sum** is monotone, and each strict step increases the sum by
at least 1. Since the sum is bounded by `d · N`, after at most `d · N + 1`
applications we reach a fixed point. -/

/-- The iterative sequence: `iter T k = T.f^[k] ⊥`. -/
noncomputable def iter (T : TarskiInstance N d) (k : ℕ) : L N d := T.f^[k] ⊥

@[simp] lemma iter_zero (T : TarskiInstance N d) : iter T 0 = ⊥ := rfl

lemma iter_succ (T : TarskiInstance N d) (k : ℕ) :
    iter T (k + 1) = T.f (iter T k) :=
  Function.iterate_succ_apply' _ _ _

lemma iter_le_iter_succ (T : TarskiInstance N d) (k : ℕ) :
    iter T k ≤ iter T (k + 1) := by
  induction k with
  | zero => rw [iter_zero, iter_succ, iter_zero]; exact bot_le
  | succ k ih =>
    have h := T.mono ih
    rwa [← iter_succ T k, ← iter_succ T (k + 1)] at h

lemma iter_mono (T : TarskiInstance N d) : Monotone (iter T) :=
  monotone_nat_of_le_succ (iter_le_iter_succ T)

/-- The coordinate sum `∑ i, x i : ℕ`, a potential function for the iteration. -/
def coordSum (x : L N d) : ℕ := ∑ i, (x i : ℕ)

lemma coordSum_le (x : L N d) : coordSum x ≤ d * N := by
  unfold coordSum
  calc ∑ i, (x i : ℕ)
      ≤ ∑ _i : Fin d, N := Finset.sum_le_sum (fun i _ => Nat.lt_succ_iff.mp (x i).isLt)
    _ = d * N := by simp [Finset.sum_const, Finset.card_univ, mul_comm]

lemma coordSum_bot : coordSum (⊥ : L N d) = 0 := by
  unfold coordSum
  apply Finset.sum_eq_zero
  intro i _
  rfl

lemma coordSum_mono : Monotone (coordSum (N := N) (d := d)) := by
  intro x y hxy
  exact Finset.sum_le_sum (fun i _ => hxy i)

/-- If `iter T k ≠ iter T (k+1)` then the coordinate sum strictly increases.
Combined with `coordSum_le`, this bounds the number of non-fixed-point steps. -/
lemma coordSum_iter_lt_of_ne (T : TarskiInstance N d) {k : ℕ}
    (h : iter T k ≠ iter T (k + 1)) :
    coordSum (iter T k) < coordSum (iter T (k + 1)) := by
  have hle : iter T k ≤ iter T (k + 1) := iter_le_iter_succ T k
  -- Componentwise: there is some `i` with strict inequality.
  have hexists : ∃ i, iter T k i < iter T (k + 1) i := by
    by_contra hno
    push Not at hno
    apply h
    funext i
    exact le_antisymm (hle i) (hno i)
  obtain ⟨i, hi⟩ := hexists
  unfold coordSum
  refine Finset.sum_lt_sum (fun j _ => hle j) ⟨i, Finset.mem_univ i, ?_⟩
  exact hi

/-- After `d · N + 1` iterations from `⊥`, the sequence has stabilized: some
intermediate step is a fixed point. -/
theorem exists_fixedPt_within (T : TarskiInstance N d) :
    ∃ k ≤ d * N, T.IsFixedPt (iter T k) := by
  -- Suppose for contradiction every `iter T k` for `k = 0, …, d·N` fails to be
  -- a fixed point. Then `coordSum ∘ iter T` is strictly increasing on this
  -- range, so `coordSum (iter T (d·N + 1)) ≥ d·N + 1`, contradicting the
  -- bound `coordSum ≤ d·N`.
  by_contra hcontra
  push Not at hcontra
  have hstrict : ∀ k ≤ d * N, coordSum (iter T k) + 1 ≤ coordSum (iter T (k + 1)) := by
    intro k hk
    have hne : iter T k ≠ iter T (k + 1) := by
      intro heq
      apply hcontra k hk
      change T.f (iter T k) = iter T k
      rw [← iter_succ]; exact heq.symm
    exact coordSum_iter_lt_of_ne T hne
  -- Inductively: `coordSum (iter T k) ≥ k` for `k ≤ d · N + 1`.
  have hbnd : ∀ k ≤ d * N + 1, k ≤ coordSum (iter T k) := by
    intro k hk
    induction k with
    | zero => exact Nat.zero_le _
    | succ k ih =>
      have hk' : k ≤ d * N := by omega
      have hk'' : k ≤ d * N + 1 := by omega
      have := hstrict k hk'
      have ih' := ih hk''
      omega
  -- `coordSum ≤ d·N`, but `coordSum (iter T (d·N + 1)) ≥ d·N + 1`.
  have := hbnd (d * N + 1) (le_refl _)
  have := coordSum_le (iter T (d * N + 1))
  omega

/-- The iterative query algorithm: budget `b`, current state `x`. Asks the oracle
at `x`; if the response equals `x`, returns it; otherwise recurses on the
response. -/
noncomputable def iterativeAux : ℕ → L N d → QueryAlg (L N d) (L N d) (L N d)
  | 0,       x => pure x
  | budget + 1, x => do
      let y ← QueryAlg.ask x
      if y = x then pure x else iterativeAux budget y

/-- The iterative Tarski algorithm: start at `⊥`, run up to `d · N + 1` iterations. -/
noncomputable def iterativeQuery (N d : ℕ) : QueryAlg (L N d) (L N d) (L N d) :=
  iterativeAux (d * N + 1) ⊥

/-- Running `iterativeAux` against a monotone `f` from state `iter T k` returns
`iter T k`'s eventual fixpoint, provided the budget exceeds the remaining strict
steps. -/
lemma iterativeAux_run_eq_of_fixed (T : TarskiInstance N d) (x : L N d)
    (hfix : T.f x = x) (b : ℕ) :
    (iterativeAux b x).run T.f = x := by
  cases b with
  | zero => rfl
  | succ b =>
    change ((QueryAlg.ask x).bind (fun y => if y = x then pure x else iterativeAux b y)).run T.f = x
    simp [QueryAlg.ask, QueryAlg.bind, QueryAlg.run, hfix]

/-- Correctness: the iterative algorithm finds a fixed point, given a sufficient
budget. -/
theorem iterativeQuery_isFixedPt (T : TarskiInstance N d) :
    T.IsFixedPt ((iterativeQuery N d).run T.f) := by
  -- Unfold iterativeQuery and show that within d·N+1 steps we reach a fixed point.
  obtain ⟨k, hk, hfix⟩ := exists_fixedPt_within T
  -- Strong invariant for iterativeAux: starting at `iter T j` with budget `b`,
  -- if `j + b ≥ k` then we find the fixed point.
  suffices h : ∀ b j, j + b = d * N + 1 → j ≤ k →
      (iterativeAux b (iter T j)).run T.f = iter T k by
    have hrun : (iterativeAux (d * N + 1) (⊥ : L N d)).run T.f = iter T k :=
      h (d * N + 1) 0 (Nat.zero_add _) (by omega)
    change T.f ((iterativeAux (d * N + 1) (⊥ : L N d)).run T.f)
        = (iterativeAux (d * N + 1) (⊥ : L N d)).run T.f
    rw [hrun]
    exact hfix
  intro b
  induction b with
  | zero =>
    intro j hj hjk
    -- j = d·N + 1; but j ≤ k ≤ d·N, contradiction.
    omega
  | succ b ih =>
    intro j hj hjk
    -- Run a single step
    change ((QueryAlg.ask (iter T j)).bind
        (fun y => if y = iter T j then pure (iter T j) else iterativeAux b y)).run T.f
        = iter T k
    rw [show ((QueryAlg.ask (iter T j)).bind _).run T.f
          = ((fun y : L N d => if y = iter T j then pure (iter T j) else iterativeAux b y)
              (T.f (iter T j))).run T.f from rfl]
    rw [show T.f (iter T j) = iter T (j + 1) from (iter_succ T j).symm]
    by_cases hjeq : iter T (j + 1) = iter T j
    · -- iter T j is a fixed point ⇒ iter T k = iter T j (since iter is monotone and stable)
      simp only [hjeq]
      -- Show iter T k = iter T j when iter T j = iter T (j+1) and j ≤ k.
      symm
      have : ∀ m, j ≤ m → iter T m = iter T j := by
        intro m hjm
        induction m, hjm using Nat.le_induction with
        | base => rfl
        | succ m _ ih =>
          rw [iter_succ, ih, show T.f (iter T j) = iter T (j + 1) from (iter_succ T j).symm,
              hjeq]
      exact this k hjk
    · simp only [if_neg hjeq]
      apply ih (j + 1) (by omega) ?_
      -- Need j + 1 ≤ k. We have j ≤ k. If j = k, then iter T (j+1) = T.f (iter T j) = iter T j
      -- contradicting hjeq.
      by_contra hjk'
      push Not at hjk'
      have hj_eq_k : j = k := by omega
      apply hjeq
      rw [hj_eq_k, iter_succ T k]
      exact hfix

/-- The iterative algorithm uses at most `d · N + 1` queries on any input. -/
theorem iterativeQuery_queries_le (T : TarskiInstance N d) :
    (iterativeQuery N d).queries T.f ≤ d * N + 1 := by
  -- iterativeAux b uses at most b queries (each recursive call costs 1 ask).
  suffices h : ∀ b (x : L N d), (iterativeAux b x).queries T.f ≤ b by
    exact h _ _
  intro b
  induction b with
  | zero => intro x; exact le_refl 0
  | succ b ih =>
    intro x
    -- Unfold the do-notation: `do y ← ask x; …` becomes `query x (κ)`.
    have hstep : (iterativeAux (b + 1) x).queries T.f
        = 1 + (if T.f x = x then 0 else (iterativeAux b (T.f x)).queries T.f) := by
      by_cases hyx : T.f x = x
      · simp [iterativeAux, QueryAlg.ask, QueryAlg.queries, QueryAlg.run, hyx]
      · simp [iterativeAux, QueryAlg.ask, QueryAlg.queries, QueryAlg.run, hyx]
    rw [hstep]
    by_cases hyx : T.f x = x
    · simp [hyx]
    · have := ih (T.f x)
      simp [hyx]; omega

/-! ### The Dang–Qi–Ye recursive binary-search algorithm

DQY does dimension-by-dimension binary search.  In dimension `d+1`, we pick a
midpoint `m` of coordinate `0`, run the `d`-dimensional DQY recursively on the
slice `{x : x 0 = m}` (each query `y : L N d` is "lifted" to `Fin.cons m y` and
the response is projected back via `Fin.tail`), then make one more query at the
returned slice-fixed-point and use the value of coordinate `0` of the response
to halve the range.

Recurrence: `T(d+1, N) ≤ (log_2(N+1) + 1) · (T(d, N) + 1)` and `T(0, N) = 0`,
giving `T(d, N) = O((log(N+1))^d)`. -/

/-- The 0-dim grid is a singleton: `Fin 0 → Fin (N+1)`. -/
instance : Unique (L N 0) := Pi.uniqueOfIsEmpty _

/-- Lift a `d`-dim query algorithm to operate on the slice `{x : Fin (d+1) →
Fin (N+1) | x 0 = m}`. Each inner query `y : L N d` is translated into the
ambient `Fin.cons m y : L N (d+1)`; each ambient response is projected back by
`Fin.tail`. -/
def liftToSlice {α : Type} (m : Fin (N + 1)) :
    QueryAlg (L N d) (L N d) α → QueryAlg (L N (d + 1)) (L N (d + 1)) α
  | .pure a => .pure a
  | .query y κ =>
      .query (Fin.cons m y) (fun resp => liftToSlice m (κ (Fin.tail resp)))

@[simp] lemma liftToSlice_queries {α : Type} (m : Fin (N + 1))
    (alg : QueryAlg (L N d) (L N d) α) (f : L N (d + 1) → L N (d + 1)) :
    (liftToSlice m alg).queries f = alg.queries (liftedOracle m f) := by
  induction alg with
  | pure _ => rfl
  | query y κ ih =>
    change 1 + (liftToSlice m (κ (liftedOracle m f y))).queries f
        = 1 + (κ (liftedOracle m f y)).queries (liftedOracle m f)
    rw [ih]

@[simp] lemma liftToSlice_run {α : Type} (m : Fin (N + 1))
    (alg : QueryAlg (L N d) (L N d) α) (f : L N (d + 1) → L N (d + 1)) :
    (liftToSlice m alg).run f = alg.run (liftedOracle m f) := by
  induction alg with
  | pure _ => rfl
  | query y κ ih =>
    change (liftToSlice m (κ (liftedOracle m f y))).run f
        = (κ (liftedOracle m f y)).run (liftedOracle m f)
    exact ih _

/-- A "slice probe" at coordinate-0 fixed at `m`: run `sliceAlg` on the
`(d)`-dim slice subbox `[lo_tail, hi_tail]` and prepend `m` to the result. -/
noncomputable def dqyProbe
    (sliceAlg : (lo' hi' : L N d) → QueryAlg (L N d) (L N d) (L N d))
    (m : Fin (N + 1)) (lo_tail hi_tail : L N d) :
    QueryAlg (L N (d + 1)) (L N (d + 1)) (L N (d + 1)) :=
  liftToSlice m (sliceAlg lo_tail hi_tail) >>= fun z => pure (Fin.cons m z)

/-- Binary-search inner loop of DQY on a subbox `[lo, hi] ⊆ L N (d+1)`.

At each level: pick the midpoint of `[lo 0, hi 0]`, run the `(d)`-dim slice
subroutine `sliceAlg` on `[Fin.tail lo, Fin.tail hi]` to find a *slice fixed
point* `z`, query `f (cons m z)` to get `fz`, and either return `cons m z`
(if `fz 0 = m`, which under the invariant means `fz = cons m z` is a fixed
point of `f`), or halve the subbox.

For **descending halving** (`fz 0 < m`): `fz` is a descending monotone point
(`f fz ≤ fz` by monotonicity composed with `fz ≤ cons m z`).  By
`MapsToBox.lower_of_descMono`, `f` maps `[lo, fz]` to itself; recurse there.

For **ascending halving** (`fz 0 > m`): symmetric.

Termination: each strict halving reduces `(hi 0) - (lo 0)`. The `budget`
parameter is a syntactic decreasing argument; `log_2(N+1) + 1` suffices. -/
noncomputable def dqyBoxAux
    (sliceAlg : (lo' hi' : L N d) → QueryAlg (L N d) (L N d) (L N d)) :
    (budget : ℕ) → (lo hi : L N (d + 1))
      → QueryAlg (L N (d + 1)) (L N (d + 1)) (L N (d + 1))
  | 0,     lo, hi => dqyProbe sliceAlg (lo 0) (Fin.tail lo) (Fin.tail hi)
  | b + 1, lo, hi =>
      if (hi 0 : ℕ) ≤ (lo 0 : ℕ) then
        -- Coord 0 effectively pinned (under invariant: `lo 0 = hi 0`).
        dqyProbe sliceAlg (lo 0) (Fin.tail lo) (Fin.tail hi)
      else
        let m_nat : ℕ := ((lo 0 : ℕ) + (hi 0 : ℕ) + 1) / 2
        let m : Fin (N + 1) :=
          ⟨min N m_nat, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩
        liftToSlice m (sliceAlg (Fin.tail lo) (Fin.tail hi)) >>= fun z =>
          QueryAlg.ask (Fin.cons m z) >>= fun fz =>
            if (fz 0 : ℕ) = m_nat then pure (Fin.cons m z)
            else if (fz 0 : ℕ) < m_nat then dqyBoxAux sliceAlg b lo fz
            else dqyBoxAux sliceAlg b fz hi

/-- The full DQY algorithm on a subbox `[lo, hi]`, recursive on dimension. -/
noncomputable def dqyBox : (d : ℕ) → (lo hi : L N d) → QueryAlg (L N d) (L N d) (L N d)
  | 0,     _, _   => .pure default
  | d + 1, lo, hi =>
      dqyBoxAux (fun lo' hi' => dqyBox d lo' hi') (Nat.log 2 (N + 1) + 1) lo hi

/-- DQY query on the full grid `[⊥, ⊤]`. -/
noncomputable def dqyQuery (N d : ℕ) : QueryAlg (L N d) (L N d) (L N d) := dqyBox d ⊥ ⊤

/-! #### Query-count bound for DQY

`B` denotes the binary-search budget `Nat.log 2 (N+1) + 1`. The bound:

* `(dqyBinSearch sliceAlg b lo hi).queries f ≤ (b + 1) · (1 + (sliceAlg.queries _))`
  where the inner `queries _` is the worst case across lifted oracles.
* `(dqyDim N d).queries f ≤ (B + 1)^d` (by induction on `d`).

Below we prove these. -/

/-- Query bound for a single `dqyProbe` step: at most `K` queries, where `K`
bounds the slice algorithm's queries (uniformly over slice subbox bounds). -/
lemma dqyProbe_queries_le
    (sliceAlg : (lo' hi' : L N d) → QueryAlg (L N d) (L N d) (L N d)) (K : ℕ)
    (hK : ∀ (lo' hi' : L N d) (f' : L N d → L N d), (sliceAlg lo' hi').queries f' ≤ K)
    (f : L N (d + 1) → L N (d + 1)) (m : Fin (N + 1)) (lo_tail hi_tail : L N d) :
    (dqyProbe sliceAlg m lo_tail hi_tail).queries f ≤ K := by
  unfold dqyProbe
  rw [QueryAlg.queries_bind, liftToSlice_queries]
  have h_pure : ∀ z : L N d,
      ((pure (Fin.cons m z) :
        QueryAlg (L N (d + 1)) (L N (d + 1)) (L N (d + 1))).queries f) = 0 :=
    fun _ => rfl
  simp only [h_pure, Nat.add_zero]
  exact hK lo_tail hi_tail _

/-- The tight bound on `dqyBoxAux`: `queries + 1 ≤ (b+1) · (K+1)`, where `K`
bounds the slice algorithm's queries.  Equivalent to `queries ≤
(b+1)·(K+1) - 1`. -/
lemma dqyBoxAux_queries_succ_le
    (sliceAlg : (lo' hi' : L N d) → QueryAlg (L N d) (L N d) (L N d)) (K : ℕ)
    (hK : ∀ (lo' hi' : L N d) (f' : L N d → L N d), (sliceAlg lo' hi').queries f' ≤ K)
    (f : L N (d + 1) → L N (d + 1)) (b : ℕ) (lo hi : L N (d + 1)) :
    (dqyBoxAux sliceAlg b lo hi).queries f + 1 ≤ (b + 1) * (K + 1) := by
  induction b generalizing lo hi with
  | zero =>
    change (dqyProbe sliceAlg (lo 0) (Fin.tail lo) (Fin.tail hi)).queries f + 1
        ≤ (0 + 1) * (K + 1)
    have := dqyProbe_queries_le sliceAlg K hK f (lo 0) (Fin.tail lo) (Fin.tail hi)
    nlinarith
  | succ b ih =>
    change (if (hi 0 : ℕ) ≤ (lo 0 : ℕ)
        then dqyProbe sliceAlg (lo 0) (Fin.tail lo) (Fin.tail hi)
        else _).queries f + 1 ≤ (b + 1 + 1) * (K + 1)
    by_cases hcase : (hi 0 : ℕ) ≤ (lo 0 : ℕ)
    · rw [if_pos hcase]
      have := dqyProbe_queries_le sliceAlg K hK f (lo 0) (Fin.tail lo) (Fin.tail hi)
      nlinarith
    · rw [if_neg hcase]
      set m_nat : ℕ := ((lo 0 : ℕ) + (hi 0 : ℕ) + 1) / 2 with hm_nat
      set m : Fin (N + 1) :=
        ⟨min N m_nat, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩ with hm
      change (liftToSlice m (sliceAlg (Fin.tail lo) (Fin.tail hi)) >>= fun z =>
              QueryAlg.ask (Fin.cons m z) >>= fun fz =>
                if (fz 0 : ℕ) = m_nat then pure (Fin.cons m z)
                else if (fz 0 : ℕ) < m_nat then dqyBoxAux sliceAlg b lo fz
                else dqyBoxAux sliceAlg b fz hi).queries f + 1
            ≤ (b + 1 + 1) * (K + 1)
      rw [QueryAlg.queries_bind, liftToSlice_queries]
      have hslice :
          (sliceAlg (Fin.tail lo) (Fin.tail hi)).queries (liftedOracle m f) ≤ K :=
        hK _ _ _
      have hrest : ∀ z : L N d,
          (QueryAlg.ask (Fin.cons m z) >>= fun fz =>
              if (fz 0 : ℕ) = m_nat then pure (Fin.cons m z)
              else if (fz 0 : ℕ) < m_nat then dqyBoxAux sliceAlg b lo fz
              else dqyBoxAux sliceAlg b fz hi).queries f
            ≤ (b + 1) * (K + 1) := by
        intro z
        rw [QueryAlg.queries_bind]
        simp only [QueryAlg.queries_ask, QueryAlg.run_ask]
        by_cases h₁ : (f (Fin.cons m z) 0 : ℕ) = m_nat
        · simp only [h₁, if_true]
          have h0 : (pure (Fin.cons m z) :
              QueryAlg (L N (d + 1)) (L N (d + 1)) (L N (d + 1))).queries f = 0 := rfl
          rw [h0]
          have : 0 < (b + 1) * (K + 1) :=
            Nat.mul_pos (Nat.succ_pos b) (Nat.succ_pos K)
          omega
        · simp only [h₁, if_false]
          by_cases h₂ : (f (Fin.cons m z) 0 : ℕ) < m_nat
          · simp only [h₂, if_true]
            have := ih lo (f (Fin.cons m z))
            linarith
          · simp only [h₂, if_false]
            have := ih (f (Fin.cons m z)) hi
            linarith
      have hz_eq : (liftToSlice m (sliceAlg (Fin.tail lo) (Fin.tail hi))).run f
          = (sliceAlg (Fin.tail lo) (Fin.tail hi)).run (liftedOracle m f) :=
        liftToSlice_run _ _ _
      rw [hz_eq]
      have htotal := Nat.add_le_add hslice
        (hrest ((sliceAlg (Fin.tail lo) (Fin.tail hi)).run (liftedOracle m f)))
      have heq : K + (b + 1) * (K + 1) + 1 = (b + 1 + 1) * (K + 1) := by ring
      omega

/-- The query bound for the recursive DQY on a subbox: `(dqyBox d lo hi).queries
f + 1 ≤ (log_2(N+1) + 2)^d`. -/
lemma dqyBox_queries_succ_le (N : ℕ) :
    ∀ (d : ℕ) (lo hi : L N d) (f : L N d → L N d),
      (dqyBox d lo hi).queries f + 1 ≤ (Nat.log 2 (N + 1) + 2) ^ d := by
  intro d
  induction d with
  | zero =>
    intro lo hi f
    change 0 + 1 ≤ (Nat.log 2 (N + 1) + 2) ^ 0
    simp
  | succ d ih =>
    intro lo hi f
    change (dqyBoxAux (fun lo' hi' => dqyBox d lo' hi') (Nat.log 2 (N + 1) + 1) lo hi).queries f + 1
        ≤ (Nat.log 2 (N + 1) + 2) ^ (d + 1)
    have hinner :=
      dqyBoxAux_queries_succ_le (fun lo' hi' => dqyBox d lo' hi')
        ((Nat.log 2 (N + 1) + 2) ^ d - 1)
        (fun lo' hi' f' => by
          change (dqyBox d lo' hi').queries f' ≤ _
          have := ih lo' hi' f'; omega)
        f (Nat.log 2 (N + 1) + 1) lo hi
    have hKpos : 1 ≤ (Nat.log 2 (N + 1) + 2) ^ d := Nat.one_le_iff_ne_zero.mpr
      (pow_ne_zero _ (by omega))
    calc (dqyBoxAux _ (Nat.log 2 (N + 1) + 1) lo hi).queries f + 1
        ≤ (Nat.log 2 (N + 1) + 1 + 1) * ((Nat.log 2 (N + 1) + 2) ^ d - 1 + 1) := hinner
      _ = (Nat.log 2 (N + 1) + 2) * (Nat.log 2 (N + 1) + 2) ^ d := by
            congr 1; omega
      _ = (Nat.log 2 (N + 1) + 2) ^ (d + 1) := by ring

/-- **DQY query bound:** at most `(log_2(N+1) + 2)^d` queries. -/
theorem dqyQuery_queries_le (T : TarskiInstance N d) :
    (dqyQuery N d).queries T.f ≤ (Nat.log 2 (N + 1) + 2) ^ d := by
  change (dqyBox d ⊥ ⊤).queries T.f ≤ (Nat.log 2 (N + 1) + 2) ^ d
  have := dqyBox_queries_succ_le N d (⊥ : L N d) (⊤ : L N d) T.f
  omega

/-! #### Correctness of DQY

The proof structure:

* `dqyProbe_run` computes the run of a probe as `Fin.cons m (slice-run)`.
* `dqyProbe_isFixedPt_pinned` proves correctness of the probe at a pinned
  coordinate (`hi 0 ≤ lo 0`), given slice correctness.
* `dqyBox_isFixedPt` is the top-level theorem (d=0 case proved; d+1 case is
  a sorry; the remaining work is to write the budget induction).

The DQY recursion at `d+1` makes a slice call (via `liftToSlice`), then
queries `f` once, then either returns or recurses on a strictly smaller
subbox using `MapsToBox.{upper,lower}_of_{asc,desc}Mono`. -/

/-- The run of `dqyProbe` reduces to a `Fin.cons` of the slice-algorithm's
run against the lifted oracle. -/
private lemma dqyProbe_run
    (sliceAlg : (lo' hi' : L N d) → QueryAlg (L N d) (L N d) (L N d))
    (m : Fin (N + 1)) (lo_tail hi_tail : L N d) (f : L N (d + 1) → L N (d + 1)) :
    (dqyProbe sliceAlg m lo_tail hi_tail).run f
      = Fin.cons m ((sliceAlg lo_tail hi_tail).run (liftedOracle m f)) := by
  unfold dqyProbe
  rw [QueryAlg.run_bind, liftToSlice_run]
  rfl

/-- Correctness of `dqyProbe` at a pinned coordinate-0 (`hi 0 ≤ lo 0`), given
slice correctness.  The slice IH delivers `z` with
`Fin.tail (f (cons (lo 0) z)) = z` and `z ∈ [Fin.tail lo, Fin.tail hi]`, and
the pinned-coord-0 box invariant forces `(f (cons (lo 0) z)) 0 = lo 0`. -/
private lemma dqyProbe_isFixedPt_pinned
    (sliceAlg : (lo' hi' : L N d) → QueryAlg (L N d) (L N d) (L N d))
    (slice_correct : ∀ (lo' hi' : L N d) (g : L N d → L N d),
        Monotone g → MapsToBox g lo' hi' → lo' ≤ hi' →
        g ((sliceAlg lo' hi').run g) = (sliceAlg lo' hi').run g ∧
        lo' ≤ (sliceAlg lo' hi').run g ∧ (sliceAlg lo' hi').run g ≤ hi')
    (lo hi : L N (d + 1)) (f : L N (d + 1) → L N (d + 1))
    (_hf : Monotone f) (hbox : MapsToBox f lo hi) (hle : lo ≤ hi)
    (hpin : (hi 0 : ℕ) ≤ (lo 0 : ℕ)) :
    f ((dqyProbe sliceAlg (lo 0) (Fin.tail lo) (Fin.tail hi)).run f) =
        (dqyProbe sliceAlg (lo 0) (Fin.tail lo) (Fin.tail hi)).run f ∧
      lo ≤ (dqyProbe sliceAlg (lo 0) (Fin.tail lo) (Fin.tail hi)).run f ∧
      (dqyProbe sliceAlg (lo 0) (Fin.tail lo) (Fin.tail hi)).run f ≤ hi := by
  -- Slice IH gives z = sliceAlg.run with g_{lo 0}(z) = z and z ∈ slice subbox.
  obtain ⟨hz_fp, hz_lo, hz_hi⟩ := slice_correct (Fin.tail lo) (Fin.tail hi)
      (liftedOracle (lo 0) f) (liftedOracle_monotone _hf)
      (liftedOracle_mapsToBox hbox (le_refl _) (Fin.le_iff_val_le_val.mp (hle 0)))
      (fun i => hle i.succ)
  set z := (sliceAlg (Fin.tail lo) (Fin.tail hi)).run (liftedOracle (lo 0) f) with _hz_def
  rw [dqyProbe_run]
  have hresult_lo : lo ≤ Fin.cons (lo 0) z := le_cons_iff.mpr ⟨le_refl _, hz_lo⟩
  have hresult_hi : Fin.cons (lo 0) z ≤ hi := cons_le_iff.mpr ⟨hle 0, hz_hi⟩
  have hfcons := hbox _ hresult_lo hresult_hi
  refine ⟨?_, hresult_lo, hresult_hi⟩
  funext i
  refine Fin.cases ?_ ?_ i
  · -- coord 0: (f cons) 0 ∈ [lo 0, hi 0] = {lo 0} (pinned).
    simp only [Fin.cons_zero]
    exact le_antisymm ((hfcons.2 0).trans (Fin.le_iff_val_le_val.mpr hpin)) (hfcons.1 0)
  · intro j
    simp only [Fin.cons_succ]
    have h_tail_eq : (liftedOracle (lo 0) f) z = z := hz_fp
    exact congr_fun h_tail_eq j

/-- Correctness of `dqyBoxAux` by induction on the budget.

The budget hypothesis `(hi 0 : ℕ) - (lo 0 : ℕ) + 1 ≤ 2^b` says that `2^b`
is at least the current coordinate-0 range plus 1, which is enough for the
strict halving to reach a pinned coord-0 within budget.

Inductive structure:
* `b = 0`: forces `hi 0 ≤ lo 0` (pinned), uses `dqyProbe_isFixedPt_pinned`.
* `b + 1`:
  - If pinned, uses `dqyProbe_isFixedPt_pinned`.
  - Else, run slice + ask, case-split on `fz 0` vs the midpoint `m`:
    + Equality ⇒ `cons m z = fz` is a fixed point.
    + Descending ⇒ `fz` is also descending, `f` maps `[lo, fz]` to itself
      (via `MapsToBox.lower_of_descMono` at `fz`); recurse with budget `b`.
    + Ascending ⇒ symmetric, recurse on `[fz, hi]`.

The budget invariant transfers via the strict-halving bound
`fz 0 - lo 0 ≤ (r + 1) / 2 ≤ 2^(b+1) / 2 = 2^b`. -/
private lemma dqyBoxAux_isFixedPt
    (sliceAlg : (lo' hi' : L N d) → QueryAlg (L N d) (L N d) (L N d))
    (slice_correct : ∀ (lo' hi' : L N d) (g : L N d → L N d),
        Monotone g → MapsToBox g lo' hi' → lo' ≤ hi' →
        g ((sliceAlg lo' hi').run g) = (sliceAlg lo' hi').run g ∧
        lo' ≤ (sliceAlg lo' hi').run g ∧ (sliceAlg lo' hi').run g ≤ hi') :
    ∀ (b : ℕ) (lo hi : L N (d + 1)) (f : L N (d + 1) → L N (d + 1)),
      Monotone f → MapsToBox f lo hi → lo ≤ hi →
      (hi 0 : ℕ) - (lo 0 : ℕ) + 1 ≤ 2 ^ b →
      f ((dqyBoxAux sliceAlg b lo hi).run f) = (dqyBoxAux sliceAlg b lo hi).run f ∧
      lo ≤ (dqyBoxAux sliceAlg b lo hi).run f ∧
      (dqyBoxAux sliceAlg b lo hi).run f ≤ hi := by
  intro b
  induction b with
  | zero =>
    intro lo hi f hf hbox hle hbudget
    have hpin : (hi 0 : ℕ) ≤ (lo 0 : ℕ) := by
      simp only [pow_zero] at hbudget; omega
    -- dqyBoxAux 0 lo hi = dqyProbe sliceAlg (lo 0) (Fin.tail lo) (Fin.tail hi)
    exact dqyProbe_isFixedPt_pinned sliceAlg slice_correct lo hi f hf hbox hle hpin
  | succ b ih =>
    intro lo hi f hf hbox hle hbudget
    by_cases hpin : (hi 0 : ℕ) ≤ (lo 0 : ℕ)
    · -- Pinned case.
      have hunfold : dqyBoxAux sliceAlg (b + 1) lo hi
          = dqyProbe sliceAlg (lo 0) (Fin.tail lo) (Fin.tail hi) := by
        change (if (hi 0 : ℕ) ≤ (lo 0 : ℕ)
              then dqyProbe sliceAlg (lo 0) (Fin.tail lo) (Fin.tail hi)
              else _) = _
        rw [if_pos hpin]
      rw [hunfold]
      exact dqyProbe_isFixedPt_pinned sliceAlg slice_correct lo hi f hf hbox hle hpin
    · -- Recursive case: slice + ask + halve.
      push Not at hpin
      set m_nat : ℕ := ((lo 0 : ℕ) + (hi 0 : ℕ) + 1) / 2 with _hm_nat_def
      have hm_nat_ge : (lo 0 : ℕ) < m_nat := by
        change (lo 0 : ℕ) < ((lo 0 : ℕ) + (hi 0 : ℕ) + 1) / 2; omega
      have hm_nat_le : m_nat ≤ (hi 0 : ℕ) := by
        change ((lo 0 : ℕ) + (hi 0 : ℕ) + 1) / 2 ≤ (hi 0 : ℕ); omega
      have hm_nat_le_N : m_nat ≤ N := by
        have := Nat.lt_succ_iff.mp (hi 0).isLt; omega
      set m : Fin (N + 1) :=
        ⟨min N m_nat, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩ with _hm_def
      have hm_val : (m : ℕ) = m_nat := min_eq_right hm_nat_le_N
      have hm_lo : (lo 0 : ℕ) ≤ (m : ℕ) := hm_val ▸ hm_nat_ge.le
      have hm_hi : (m : ℕ) ≤ (hi 0 : ℕ) := hm_val ▸ hm_nat_le
      obtain ⟨hz_fp, hz_lo, hz_hi⟩ := slice_correct (Fin.tail lo) (Fin.tail hi)
          (liftedOracle m f) (liftedOracle_monotone hf)
          (liftedOracle_mapsToBox hbox hm_lo hm_hi)
          (fun i => hle i.succ)
      set z := (sliceAlg (Fin.tail lo) (Fin.tail hi)).run (liftedOracle m f)
        with _hz_def
      -- cons m z ∈ [lo, hi]
      have hcons_lo : lo ≤ Fin.cons m z :=
        le_cons_iff.mpr ⟨Fin.le_iff_val_le_val.mpr hm_lo, hz_lo⟩
      have hcons_hi : Fin.cons m z ≤ hi :=
        cons_le_iff.mpr ⟨Fin.le_iff_val_le_val.mpr hm_hi, hz_hi⟩
      have hfcons := hbox _ hcons_lo hcons_hi
      set fz := f (Fin.cons m z) with hfz_def
      have hfz_tail_eq_z : Fin.tail fz = z := hz_fp
      have hfz_lo : lo ≤ fz := hfcons.1
      have hfz_hi : fz ≤ hi := hfcons.2
      -- Unfold the algorithm at the recursive branch.
      have hunfold : (dqyBoxAux sliceAlg (b + 1) lo hi).run f
          = (liftToSlice m (sliceAlg (Fin.tail lo) (Fin.tail hi)) >>= fun z' =>
              QueryAlg.ask (Fin.cons m z') >>= fun fz' =>
                if (fz' 0 : ℕ) = m_nat then pure (Fin.cons m z')
                else if (fz' 0 : ℕ) < m_nat then dqyBoxAux sliceAlg b lo fz'
                else dqyBoxAux sliceAlg b fz' hi).run f := by
        congr 1
        change (if (hi 0 : ℕ) ≤ (lo 0 : ℕ) then _ else _) = _
        rw [if_neg (not_le.mpr hpin)]
      rw [hunfold, QueryAlg.run_bind, liftToSlice_run, QueryAlg.run_bind]
      simp only [QueryAlg.run_ask]
      -- Set up the budget arithmetic shared between desc/asc cases.
      have hpin_lt : (lo 0 : ℕ) < (hi 0 : ℕ) := hpin
      have h_mnat_def : m_nat = ((lo 0 : ℕ) + (hi 0 : ℕ) + 1) / 2 := rfl
      have hpow : 2 ^ (b + 1) = 2 * 2 ^ b := by ring
      -- Now goal: f (... if ... then ... else ...).run f) = ...
      -- The if-then-else is on fz 0.
      by_cases h_eq : (fz 0 : ℕ) = m_nat
      · -- Equality case: cons m z = fz, fp.
        rw [if_pos h_eq]
        have hcons_eq_fz : Fin.cons m z = fz := by
          rw [show fz = Fin.cons (fz 0) (Fin.tail fz) from (Fin.cons_self_tail fz).symm,
              hfz_tail_eq_z]
          congr 1
          exact Fin.ext (hm_val.trans h_eq.symm)
        refine ⟨?_, hcons_lo, hcons_hi⟩
        change f (Fin.cons m z) = Fin.cons m z
        exact hfz_def.symm.trans hcons_eq_fz.symm
      · rw [if_neg h_eq]
        by_cases h_lt : (fz 0 : ℕ) < m_nat
        · -- Descending: fz < cons m z (strict in coord 0).
          rw [if_pos h_lt]
          -- fz is descending: f fz ≤ fz, via fz ≤ cons m z and monotonicity.
          have hfz_desc : IsDescMono f fz := by
            have h_fz_le_cons : fz ≤ Fin.cons m z :=
              le_cons_iff.mpr
                ⟨by rw [Fin.le_iff_val_le_val, hm_val]; omega, hfz_tail_eq_z.le⟩
            intro i; exact (hf h_fz_le_cons i).trans (le_refl _)
          have hbox' : MapsToBox f lo fz :=
            MapsToBox.lower_of_descMono hf hfz_lo hfz_hi hbox hfz_desc
          have hbudget' : (fz 0 : ℕ) - (lo 0 : ℕ) + 1 ≤ 2 ^ b := by
            rw [h_mnat_def] at h_lt; rw [hpow] at hbudget; omega
          obtain ⟨h_ih_fp, h_ih_lo, h_ih_hi⟩ := ih lo fz f hf hbox' hfz_lo hbudget'
          exact ⟨h_ih_fp, h_ih_lo, h_ih_hi.trans hfz_hi⟩
        · -- Ascending: fz > cons m z.
          rw [if_neg h_lt]
          push Not at h_lt
          have h_gt : m_nat < (fz 0 : ℕ) := lt_of_le_of_ne h_lt (Ne.symm h_eq)
          have hfz_asc : IsAscMono f fz := by
            have h_cons_le_fz : Fin.cons m z ≤ fz :=
              cons_le_iff.mpr
                ⟨by rw [Fin.le_iff_val_le_val, hm_val]; omega, hfz_tail_eq_z.ge⟩
            intro i; exact le_refl _ |>.trans (hf h_cons_le_fz i)
          have hbox' : MapsToBox f fz hi :=
            MapsToBox.upper_of_ascMono hf hfz_lo hfz_hi hbox hfz_asc
          have hbudget' : (hi 0 : ℕ) - (fz 0 : ℕ) + 1 ≤ 2 ^ b := by
            rw [h_mnat_def] at h_gt; rw [hpow] at hbudget; omega
          obtain ⟨h_ih_fp, h_ih_lo, h_ih_hi⟩ := ih fz hi f hf hbox' hfz_hi hbudget'
          exact ⟨h_ih_fp, hfz_lo.trans h_ih_lo, h_ih_hi⟩

theorem dqyBox_isFixedPt :
    ∀ (d : ℕ) (lo hi : L N d) (f : L N d → L N d),
      Monotone f → MapsToBox f lo hi → lo ≤ hi →
      f ((dqyBox d lo hi).run f) = (dqyBox d lo hi).run f ∧
      lo ≤ (dqyBox d lo hi).run f ∧ (dqyBox d lo hi).run f ≤ hi
  | 0, _, _, _, _, _, _ => by
    refine ⟨Subsingleton.elim _ _,
            le_of_eq (Subsingleton.elim _ _),
            le_of_eq (Subsingleton.elim _ _)⟩
  | d + 1, lo, hi, f, hf, hbox, hle => by
    -- Apply `dqyBoxAux_isFixedPt` with slice IH = `dqyBox_isFixedPt d` and the
    -- budget bound `2^(Nat.log 2 (N+1) + 1) ≥ (hi 0 - lo 0) + 1`.
    have h_budget : (hi 0 : ℕ) - (lo 0 : ℕ) + 1 ≤ 2 ^ (Nat.log 2 (N + 1) + 1) := by
      have h_range_le_N : (hi 0 : ℕ) - (lo 0 : ℕ) ≤ N := by
        have := Nat.lt_succ_iff.mp (hi 0).isLt
        omega
      have h_pow_ge : N + 1 ≤ 2 ^ (Nat.log 2 (N + 1) + 1) :=
        Nat.le_of_lt (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (N + 1))
      omega
    exact dqyBoxAux_isFixedPt (fun lo' hi' => dqyBox d lo' hi')
            (fun lo' hi' g hg hbox' hle' => dqyBox_isFixedPt d lo' hi' g hg hbox' hle')
            (Nat.log 2 (N + 1) + 1) lo hi f hf hbox hle h_budget

/-- The DQY query algorithm finds a fixed point. Wrapper around
`dqyBox_isFixedPt` applied at the full grid `[⊥, ⊤]`. -/
theorem dqyQuery_isFixedPt (T : TarskiInstance N d) :
    T.IsFixedPt ((dqyQuery N d).run T.f) := by
  change T.f ((dqyBox d ⊥ ⊤).run T.f) = (dqyBox d ⊥ ⊤).run T.f
  exact (dqyBox_isFixedPt d ⊥ ⊤ T.f T.mono (fun _ _ _ => ⟨bot_le, le_top⟩) bot_le).1

/-! ### Lower bound (Etessami–Papadimitriou–Rubinstein–Yannakakis)

Etessami et al. (arXiv:1909.03210) prove that every deterministic adaptive
query algorithm needs `Ω((log(N+1))^d)` queries to find a Tarski fixed point on
the `d`-dimensional grid in the worst case.

The proof goes by an adversary argument:

1. The adversary maintains a "candidate set" `S ⊆ L N d` of grid points such
   that any answer pattern to the queries so far is consistent with some
   monotone `f` whose unique fixed point lies in `S`.

2. When the algorithm queries a point `q`, the adversary picks the response
   that keeps `|S|` as large as possible.

3. Each query reduces `|S|` by a factor of at most `2^d` (roughly).

4. To pin down the fixed point, `|S| = 1` is needed, which requires
   `Ω((log(N+1))^d)` queries because `|S|` starts at roughly `(N+1)^d`.

A clean formalization needs:

* The query algorithm's "decision-tree depth" lower bound, defined in terms of
  `QueryAlg`.
* A construction of two monotone instances that agree on the first `k` queries
  but have different fixed points (for any `k = o(log^d N)`).

For now this is a stated theorem with `sorry`. -/

/-- The deterministic query complexity of Tarski on the `[0..N]^d` grid, defined
as the maximum number of queries the algorithm needs in the worst case. -/
noncomputable def queryComplexity (N d : ℕ) (alg : QueryAlg (L N d) (L N d) (L N d)) : ℕ :=
  ⨆ T : TarskiInstance N d, alg.queries T.f

/-- **Etessami et al. lower bound:** any deterministic algorithm that correctly
finds a fixed point on every monotone instance issues `Ω((log(N+1))^d)` queries
on some instance.

Formally: there exists `c > 0` such that for every algorithm `alg` whose run
is always a fixed point, `queryComplexity N d alg ≥ c · (log(N+1))^d` for all
sufficiently large `N`.

Proof: adversary argument as above. -/
theorem etessami_lowerBound :
    ∃ c : ℝ, 0 < c ∧ ∀ (d : ℕ), ∀ᶠ N in Filter.atTop, ∀
      (alg : QueryAlg (L N d) (L N d) (L N d))
      (_hcorrect : ∀ T : TarskiInstance N d, T.IsFixedPt (alg.run T.f)),
      (c * (Real.log (N + 1)) ^ d : ℝ) ≤ (queryComplexity N d alg : ℝ) := by
  sorry

end Tarski
end Tfnp
