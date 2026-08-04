/-
Copyright (c) 2026 Angus Joshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Angus Joshi
-/
import Tfnp.Tarski.Basic
import Tfnp.Tarski.Simulation
import Mathlib.Data.Nat.Log

/-!
# The Fearnley–Pálvölgyi–Savani outer algorithm

FPS Section 3.  The outer algorithm maintains a sub-box `[lo, hi]` with
`lo ∈ Up f` and `hi ∈ Down f` — by FPS Lemma 4 (`exists_sol_of_up_down`) such a
box always contains a solution — and repeatedly halves it by calling an *inner
algorithm* on a principal slice through the midpoint of some wide dimension.

> **FPS Definition 3 (inner algorithm).**  Given a sub-instance `L_{a,b}` with
> `a ∈ Up(f)`, `b ∈ Down(f)`, and a principal slice `s` of that sub-instance, an
> inner algorithm outputs either a point `x ∈ L_{a,b} ∩ L_s` with `x ∈ Up(f)` or
> `x ∈ Down(f)`, or two points of `L_{a,b}` witnessing a violation of order
> preservation.

> **FPS Theorem 5.**  If there is an inner algorithm making at most `q` queries,
> a solution to Tarski can be found in `O(q·k·log n + k)` queries.

## Main definitions

* `InnerAnswer` and `IsInnerSol` — FPS Definition 3.  We let the inner algorithm
  report *which* of `Up f` / `Down f` its point lies in, as FPS's own inner
  algorithm does; otherwise the outer algorithm would need one extra query per
  iteration just to find out.
* `SolvesInner` — an inner algorithm family for an ambient box.
* `outerAlg` — the outer algorithm.

## Main results

* `outerAlg_isSol` — correctness (FPS Theorem 5).
* `outerAlg_bounded` — the query bound, in the explicit form
  `logSize lo hi * q + (k + 1)` where `logSize lo hi = ∑ i, ⌈log₂ (hi i - lo i)⌉`.
  On the cube `[0, n]^k` this is `k · ⌈log₂ n⌉ · q + k + 1`, i.e. FPS's
  `O(q·k·log n + k)`.

The termination measure is `logSize`, the sum over dimensions of the *ceiling*
binary logarithm of the width.  Ceiling is what makes it work: halving `[0,2]`
gives width `1`, and `⌈log₂ 2⌉ = 1 > 0 = ⌈log₂ 1⌉`, whereas the floor logarithm
does not drop.  `Nat.clog_of_two_le` is exactly the recurrence needed.
-/

namespace Tfnp.Tarski

open QueryAlg (Bounded)

variable {k : ℕ}

/-! ### A worst-case bound for the interval algorithm -/

lemma intervalAlg_bounded (b : Pt k) :
    ∀ (n : ℕ) (prev a : Pt k), Bounded n (intervalAlg b n prev a) := by
  intro n
  induction n with
  | zero => intro prev a; exact .pure
  | succ n ih =>
    intro prev a
    change Bounded (n + 1) (QueryAlg.ask a >>= _)
    refine Bounded.mono (n := 1 + n) ((Bounded.ask a).bind fun fa => ?_) (by omega)
    by_cases h0 : ¬ a ≤ fa
    · rw [if_pos h0]; exact .pure
    · rw [if_neg h0]
      by_cases h : ∃ i, a i < fa i
      · rw [dif_pos h]
        by_cases hb : b h.choose ≤ a h.choose
        · rw [if_pos hb]; exact .pure
        · rw [if_neg hb]; exact ih a _
      · rw [dif_neg h]; exact .pure

/-- The terminal call of the outer algorithm: `k + 1` queries suffice once every
dimension of the box has width at most one, since then `boxSize ≤ k`. -/
noncomputable def terminalAlg (lo hi : Pt k) : QueryAlg (Pt k) (Pt k) (Answer k) :=
  intervalAlg hi (k + 1) lo lo

lemma terminalAlg_bounded (lo hi : Pt k) : Bounded (k + 1) (terminalAlg lo hi) :=
  intervalAlg_bounded hi _ lo lo

lemma boxSize_le_of_widths_le_one {lo hi : Pt k} (h : ∀ i, hi i - lo i ≤ 1) :
    boxSize lo hi ≤ k := by
  calc boxSize lo hi = ∑ i, (hi i - lo i) := rfl
    _ ≤ ∑ _i : Fin k, 1 := Finset.sum_le_sum fun i _ => h i
    _ = k := by simp

lemma terminalAlg_isSol {f : Pt k → Pt k} {lo hi : Pt k} (hlohi : lo ≤ hi)
    (hlo : lo ∈ Up f) (hhi : hi ∈ Down f) (hw : ∀ i, hi i - lo i ≤ 1) :
    IsSol f lo hi ((terminalAlg lo hi).run f) :=
  intervalAlg_isSol f hhi _ lo lo
    (Nat.lt_succ_of_le (boxSize_le_of_widths_le_one hw)) le_rfl le_rfl hlohi
    (fun hnot => absurd hlo hnot)

/-! ### Inner algorithms (FPS Definition 3) -/

/-- What an inner algorithm may return. -/
inductive InnerAnswer (k : ℕ) : Type
  /-- A point of the slice lying in the up set of the *whole* instance. -/
  | up (p : Pt k) : InnerAnswer k
  /-- A point of the slice lying in the down set of the *whole* instance. -/
  | down (p : Pt k) : InnerAnswer k
  /-- A witnessed violation of order preservation. -/
  | vop (x y : Pt k) : InnerAnswer k

/-- **FPS Definition 3.**  Correctness of an inner algorithm's output on the
sub-box `[lo, hi]` and the principal slice `{z | z i = m}`.

The essential point, which FPS stress, is that `Up f` and `Down f` refer to the
*whole* instance, not to the slice: a point where `f` goes up within the slice but
down in the frozen dimension is not an acceptable answer. -/
def IsInnerSol (f : Pt k → Pt k) (lo hi : Pt k) (i : Fin k) (m : ℕ) :
    InnerAnswer k → Prop
  | .up p => p ∈ Box lo hi ∧ p i = m ∧ p ∈ Up f
  | .down p => p ∈ Box lo hi ∧ p i = m ∧ p ∈ Down f
  | .vop x y => x ∈ Box lo hi ∧ y ∈ Box lo hi ∧ IsVop f x y

/-- An inner algorithm family, correct on every sub-box of `[LO, HI]` satisfying
the up/down invariant and every principal slice through it. -/
def SolvesInner (innerOf : Pt k → Pt k → Fin k → ℕ → QueryAlg (Pt k) (Pt k) (InnerAnswer k))
    (LO HI : Pt k) : Prop :=
  ∀ (f : Pt k → Pt k) (lo hi : Pt k) (i : Fin k) (m : ℕ),
    LO ≤ lo → lo ≤ hi → hi ≤ HI → lo ∈ Up f → hi ∈ Down f → lo i ≤ m → m ≤ hi i →
      IsInnerSol f lo hi i m ((innerOf lo hi i m).run f)

/-! ### The termination measure -/

/-- `logSize lo hi = ∑ i, ⌈log₂ (hi i - lo i)⌉`: the number of halvings the box
can still undergo.  Each iteration of the outer algorithm decreases it. -/
def logSize (lo hi : Pt k) : ℕ := ∑ i, Nat.clog 2 (hi i - lo i)

lemma widths_le_one_of_logSize_zero {lo hi : Pt k} (h : logSize lo hi = 0) :
    ∀ i, hi i - lo i ≤ 1 := by
  intro i
  by_contra hc
  have h2 : 2 ≤ hi i - lo i := by omega
  have hpos : 0 < Nat.clog 2 (hi i - lo i) := Nat.clog_pos (by norm_num) (by omega)
  have := (Finset.sum_eq_zero_iff (s := (Finset.univ : Finset (Fin k)))
    (f := fun i => Nat.clog 2 (hi i - lo i))).mp h i (Finset.mem_univ i)
  omega

/-- Halving one dimension strictly decreases `logSize`, provided no dimension
widens.  This is the key arithmetic step; `Nat.clog_of_two_le` supplies exactly
the recurrence `⌈log₂ w⌉ = ⌈log₂ ⌈w/2⌉⌉ + 1`. -/
lemma logSize_lt {lo hi lo' hi' : Pt k} (i : Fin k)
    (hmono : ∀ j, hi' j - lo' j ≤ hi j - lo j)
    (hw : 2 ≤ hi i - lo i)
    (hhalf : hi' i - lo' i ≤ (hi i - lo i + 1) / 2) :
    logSize lo' hi' < logSize lo hi := by
  refine Finset.sum_lt_sum (fun j _ => Nat.clog_mono_right 2 (hmono j))
    ⟨i, Finset.mem_univ i, ?_⟩
  have hrec : Nat.clog 2 (hi i - lo i) = Nat.clog 2 ((hi i - lo i + 1) / 2) + 1 := by
    have := Nat.clog_of_two_le (b := 2) (n := hi i - lo i) (by norm_num) hw
    simpa using this
  calc Nat.clog 2 (hi' i - lo' i)
      ≤ Nat.clog 2 ((hi i - lo i + 1) / 2) := Nat.clog_mono_right 2 hhalf
    _ < Nat.clog 2 (hi i - lo i) := by omega

/-! ### The outer algorithm -/

/-- The outer algorithm on a sub-box, with an explicit budget on the number of
halvings.  While some dimension has width at least two, halve it by calling the
inner algorithm on the principal slice through its midpoint; the answer either
witnesses a violation, or replaces one endpoint of the box. -/
noncomputable def outerAux
    (innerOf : Pt k → Pt k → Fin k → ℕ → QueryAlg (Pt k) (Pt k) (InnerAnswer k)) :
    ℕ → Pt k → Pt k → QueryAlg (Pt k) (Pt k) (Answer k)
  | 0, lo, hi => terminalAlg lo hi
  | n + 1, lo, hi =>
      if h : ∃ i : Fin k, lo i + 2 ≤ hi i then
        innerOf lo hi h.choose ((lo h.choose + hi h.choose) / 2) >>= fun ans =>
          match ans with
          | .vop x y => QueryAlg.pure (.inr (x, y))
          | .up p => outerAux innerOf n p hi
          | .down p => outerAux innerOf n lo p
      else terminalAlg lo hi

lemma outerAux_succ
    (innerOf : Pt k → Pt k → Fin k → ℕ → QueryAlg (Pt k) (Pt k) (InnerAnswer k))
    (n : ℕ) (lo hi : Pt k) :
    outerAux innerOf (n + 1) lo hi =
      (if h : ∃ i : Fin k, lo i + 2 ≤ hi i then
        innerOf lo hi h.choose ((lo h.choose + hi h.choose) / 2) >>= fun ans =>
          match ans with
          | .vop x y => QueryAlg.pure (.inr (x, y))
          | .up p => outerAux innerOf n p hi
          | .down p => outerAux innerOf n lo p
      else terminalAlg lo hi) := rfl

/-- The outer algorithm on the box `[lo, hi]`. -/
noncomputable def outerAlg
    (innerOf : Pt k → Pt k → Fin k → ℕ → QueryAlg (Pt k) (Pt k) (InnerAnswer k))
    (lo hi : Pt k) : QueryAlg (Pt k) (Pt k) (Answer k) :=
  outerAux innerOf (logSize lo hi) lo hi

/-! ### Query bound -/

lemma outerAux_bounded
    {innerOf : Pt k → Pt k → Fin k → ℕ → QueryAlg (Pt k) (Pt k) (InnerAnswer k)} {q : ℕ}
    (hq : ∀ lo hi i m, Bounded q (innerOf lo hi i m)) :
    ∀ (n : ℕ) (lo hi : Pt k), Bounded (n * q + (k + 1)) (outerAux innerOf n lo hi) := by
  intro n
  induction n with
  | zero => intro lo hi; simpa using terminalAlg_bounded lo hi
  | succ n ih =>
    intro lo hi
    rw [outerAux_succ]
    by_cases h : ∃ i : Fin k, lo i + 2 ≤ hi i
    · rw [dif_pos h]
      refine Bounded.mono (n := q + (n * q + (k + 1)))
        ((hq _ _ _ _).bind fun ans => ?_) (by rw [Nat.succ_mul]; omega)
      cases ans with
      | vop x y => exact Bounded.pure' _ _
      | up p => exact ih p hi
      | down p => exact ih lo p
    · rw [dif_neg h]
      exact (terminalAlg_bounded lo hi).mono (by omega)

/-- **FPS Theorem 5** (query bound).  With an inner algorithm making at most `q`
queries, the outer algorithm makes at most `logSize lo hi * q + (k + 1)`. -/
theorem outerAlg_bounded
    {innerOf : Pt k → Pt k → Fin k → ℕ → QueryAlg (Pt k) (Pt k) (InnerAnswer k)} {q : ℕ}
    (hq : ∀ lo hi i m, Bounded q (innerOf lo hi i m)) (lo hi : Pt k) :
    Bounded (logSize lo hi * q + (k + 1)) (outerAlg innerOf lo hi) :=
  outerAux_bounded hq _ lo hi

/-! ### Correctness -/

lemma outerAux_isSol {f : Pt k → Pt k}
    {innerOf : Pt k → Pt k → Fin k → ℕ → QueryAlg (Pt k) (Pt k) (InnerAnswer k)}
    {LO HI : Pt k} (hInner : SolvesInner innerOf LO HI) :
    ∀ (n : ℕ) (lo hi : Pt k), logSize lo hi ≤ n → LO ≤ lo → lo ≤ hi → hi ≤ HI →
      lo ∈ Up f → hi ∈ Down f →
      IsSol f lo hi ((outerAux innerOf n lo hi).run f) := by
  intro n
  induction n with
  | zero =>
    intro lo hi hsize _ hlohi _ hlo hhi
    exact terminalAlg_isSol hlohi hlo hhi
      (widths_le_one_of_logSize_zero (Nat.le_zero.mp hsize))
  | succ n ih =>
    intro lo hi hsize hLO hlohi hHI hlo hhi
    rw [outerAux_succ]
    by_cases h : ∃ i : Fin k, lo i + 2 ≤ hi i
    · rw [dif_pos h]
      set i := h.choose with hi_def
      have hwide : lo i + 2 ≤ hi i := h.choose_spec
      set m := (lo i + hi i) / 2 with hm_def
      have hm_lo : lo i ≤ m := by rw [hm_def]; omega
      have hm_hi : m ≤ hi i := by rw [hm_def]; omega
      have hwidth : 2 ≤ hi i - lo i := by omega
      have hans := hInner f lo hi i m hLO hlohi hHI hlo hhi hm_lo hm_hi
      rw [QueryAlg.run_bind]
      rcases hres : (innerOf lo hi i m).run f with p | p | ⟨x, y⟩
      · -- `p ∈ Up f`: recurse on `[p, hi]`.
        rw [hres] at hans
        obtain ⟨hpbox, hpi, hpup⟩ := hans
        obtain ⟨hlop, hphi⟩ := mem_Box.mp hpbox
        have hdec : logSize p hi < logSize lo hi :=
          logSize_lt i (fun j => by have := le_coord hlop j; omega) hwidth
            (by rw [hpi, hm_def]; omega)
        exact IsSol.mono hlop le_rfl
          (ih p hi (by omega) (hLO.trans hlop) hphi hHI hpup hhi)
      · -- `p ∈ Down f`: recurse on `[lo, p]`.
        rw [hres] at hans
        obtain ⟨hpbox, hpi, hpdown⟩ := hans
        obtain ⟨hlop, hphi⟩ := mem_Box.mp hpbox
        have hdec : logSize lo p < logSize lo hi :=
          logSize_lt i (fun j => by have := le_coord hphi j; omega) hwidth
            (by rw [hpi, hm_def]; omega)
        exact IsSol.mono le_rfl hphi
          (ih lo p (by omega) hLO hlop (hphi.trans hHI) hlo hpdown)
      · -- A violation: return it.
        rw [hres] at hans
        exact hans
    · rw [dif_neg h]
      refine terminalAlg_isSol hlohi hlo hhi fun i => ?_
      push Not at h
      have := h i
      omega

/-- **FPS Theorem 5** (correctness).  An inner algorithm yields a Tarski
algorithm on the whole box. -/
theorem outerAlg_isSol {f : Pt k → Pt k}
    {innerOf : Pt k → Pt k → Fin k → ℕ → QueryAlg (Pt k) (Pt k) (InnerAnswer k)}
    {lo hi : Pt k} (hInner : SolvesInner innerOf lo hi) (hlohi : lo ≤ hi)
    (hlo : lo ∈ Up f) (hhi : hi ∈ Down f) :
    IsSol f lo hi ((outerAlg innerOf lo hi).run f) :=
  outerAux_isSol hInner _ lo hi le_rfl le_rfl hlohi le_rfl hlo hhi

end Tfnp.Tarski
