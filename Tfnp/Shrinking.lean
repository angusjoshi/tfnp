/-
Copyright (c) 2026 Angus Joshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Angus Joshi
-/

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Log

/-!
# Iterated `1/p` shrinking

If an iterative procedure shrinks some non-negative integer-valued measure
by a factor of at least `1/p` at every step, then after `N` steps the
measure is at most `((p-1)/p)^N` of the original. This is the abstract
"each iteration removes a `1/poly` fraction of the search space" pattern
that appears in many TFNP query algorithms.

## Main results

* `iterate_shrinking`: the multiplicative iterate bound,
  `p^N · measure(step^[N] a₀) ≤ (p-1)^N · measure a₀`.

* `measure_zero_of_iterate_shrinking`: the "becomes empty" corollary —
  if `(p-1)^N · measure a₀ < p^N`, then `measure(step^[N] a₀) = 0`.

## Specialisations

* `p = 2` (halving): `2^N · measure ≤ measure a₀`; empty after
  `N ≥ Nat.log₂ (measure a₀) + 1`.
* `p = poly(n)` (1/poly shrinking): `N = O(poly · log measure)` iterations
  suffice for emptiness.

All statements live in `ℕ`, so they apply to combinatorial measures like
`Finset.card`, `Set.ncard`, list length, etc. without any real-number
machinery.
-/

namespace Tfnp

/-- **Iterated 1/p shrinking.** If `p · measure (step a) ≤ (p - 1) · measure a`
for every `a`, then after `N` iterations the measure has decayed by a factor
of `(p/(p-1))^N`:

`p^N · measure (step^[N] a₀) ≤ (p - 1)^N · measure a₀`.

The halving case `p = 2` reads `2^N · measure (step^[N] a₀) ≤ measure a₀`. -/
theorem iterate_shrinking {α : Type*} (p : ℕ) (a₀ : α) (step : α → α)
    (measure : α → ℕ) (h : ∀ a, p * measure (step a) ≤ (p - 1) * measure a)
    (N : ℕ) :
    p ^ N * measure (step^[N] a₀) ≤ (p - 1) ^ N * measure a₀ := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Function.iterate_succ', Function.comp_apply, pow_succ, pow_succ]
    calc p ^ N * p * measure (step (step^[N] a₀))
        = p ^ N * (p * measure (step (step^[N] a₀))) := by ring
      _ ≤ p ^ N * ((p - 1) * measure (step^[N] a₀)) :=
          Nat.mul_le_mul_left _ (h (step^[N] a₀))
      _ = (p - 1) * (p ^ N * measure (step^[N] a₀)) := by ring
      _ ≤ (p - 1) * ((p - 1) ^ N * measure a₀) := Nat.mul_le_mul_left _ ih
      _ = (p - 1) ^ N * (p - 1) * measure a₀ := by ring

/-- **Emptiness after enough iterations.** Under the same 1/p shrinking
hypothesis, the measure reaches zero as soon as `(p - 1)^N · measure a₀ < p^N`.

For `p = 2` (halving), the condition simplifies to `measure a₀ < 2^N`. For
general `p ≥ 2`, taking `N ≈ p · log (measure a₀)` suffices. -/
theorem measure_zero_of_iterate_shrinking {α : Type*} (p : ℕ) (a₀ : α)
    (step : α → α) (measure : α → ℕ)
    (h : ∀ a, p * measure (step a) ≤ (p - 1) * measure a) (N : ℕ)
    (hN : (p - 1) ^ N * measure a₀ < p ^ N) :
    measure (step^[N] a₀) = 0 := by
  have hbound := iterate_shrinking p a₀ step measure h N
  by_contra hne
  have hpos : 1 ≤ measure (step^[N] a₀) := Nat.one_le_iff_ne_zero.mpr hne
  have hple : p ^ N ≤ p ^ N * measure (step^[N] a₀) :=
    Nat.le_mul_of_pos_right _ hpos
  omega

/-- **Halving specialisation (`p = 2`).** A `Finset` whose card halves at each
step is emptied by any `N ≥ Nat.log2 (initial card) + 1` iterations. Direct
corollary of `measure_zero_of_iterate_shrinking` with `p = 2`. -/
theorem finset_card_zero_of_halving {α : Type*} (T₀ : Finset α)
    (step : Finset α → Finset α) (h : ∀ T, 2 * (step T).card ≤ T.card)
    (N : ℕ) (hN : Nat.log2 T₀.card + 1 ≤ N) :
    (step^[N] T₀).card = 0 := by
  apply measure_zero_of_iterate_shrinking 2 T₀ step Finset.card
  · intro T; have := h T; omega
  · show (2 - 1) ^ N * T₀.card < 2 ^ N
    rw [show (2 - 1 : ℕ) = 1 from rfl, one_pow, one_mul]
    rcases eq_or_ne T₀.card 0 with h0 | h0
    · rw [h0]; positivity
    · calc T₀.card
          < 2 ^ (Nat.log2 T₀.card + 1) := by
            rw [Nat.log2_eq_log_two]
            exact Nat.lt_pow_succ_log_self (by norm_num) _
        _ ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) hN

end Tfnp
