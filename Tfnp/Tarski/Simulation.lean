/-
Copyright (c) 2026 Angus Joshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Angus Joshi
-/
import Tfnp.QueryModel

/-!
# Worst-case query bounds

`QueryAlg.queries f` counts the queries made *against a particular oracle*.  For
composing algorithms one needs the worst case over all oracles, i.e. the depth of
the decision tree.  Since the response type may be infinite the depth is not a
`Finset.sup`, so we define it as an inductive predicate instead:

* `QueryAlg.Bounded n alg` — every root-to-leaf path of `alg` has at most `n`
  queries.

`Bounded` implies the pointwise bound (`Bounded.queries_le`) and is closed under
`bind` (`Bounded.bind`), which is what makes it usable for the simulation
arguments in `Tfnp/Tarski/Decomposition.lean`: an algorithm that answers each of
its `n` queries by running a sub-algorithm of depth `c` has depth `n * c`.
-/

namespace Tfnp
namespace QueryAlg

variable {Q R α β : Type}

/-- `Bounded n alg` says `alg` makes at most `n` queries on **every** branch of
its decision tree, i.e. against every oracle.  This is the worst-case query
complexity of `alg`, phrased so as to avoid needing `R` to be finite. -/
inductive Bounded : ℕ → QueryAlg Q R α → Prop
  | pure {n : ℕ} {a : α} : Bounded n (.pure a)
  | query {n : ℕ} {q : Q} {κ : R → QueryAlg Q R α} :
      (∀ r, Bounded n (κ r)) → Bounded (n + 1) (.query q κ)

namespace Bounded

/-- A worst-case bound is in particular a bound against each oracle. -/
lemma queries_le {n : ℕ} {alg : QueryAlg Q R α} (h : Bounded n alg) (f : Q → R) :
    alg.queries f ≤ n := by
  induction h with
  | pure => exact Nat.zero_le _
  | @query n q κ _ ih =>
    have := ih (f q)
    change 1 + (κ (f q)).queries f ≤ n + 1
    omega

lemma mono {n m : ℕ} {alg : QueryAlg Q R α} (h : Bounded n alg) (hnm : n ≤ m) :
    Bounded m alg := by
  induction h generalizing m with
  | pure => exact .pure
  | @query n q κ _ ih =>
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    exact .query fun r => ih r (by omega)

lemma pure' (a : α) (n : ℕ) : Bounded n (Pure.pure a : QueryAlg Q R α) := .pure

lemma ask (q : Q) : Bounded 1 (ask q : QueryAlg Q R R) := .query fun _ => .pure

/-- Sequencing adds worst-case bounds. -/
lemma bind {n m : ℕ} {alg : QueryAlg Q R α} {g : α → QueryAlg Q R β}
    (h : Bounded n alg) (hg : ∀ a, Bounded m (g a)) : Bounded (n + m) (alg >>= g) := by
  induction h with
  | @pure n a =>
    exact (hg a).mono (Nat.le_add_left m n)
  | @query n q κ _ ih =>
    have : n + 1 + m = (n + m) + 1 := by omega
    rw [this]
    exact .query fun r => ih r

/-- Iterated sequencing: `n` steps each of depth at most `c`. -/
lemma bind_const {n c : ℕ} {alg : QueryAlg Q R α} {g : α → QueryAlg Q R β}
    (h : Bounded n alg) (hg : ∀ a, Bounded c (g a)) : Bounded (n + c) (alg >>= g) :=
  bind h hg

end Bounded

end QueryAlg
end Tfnp
