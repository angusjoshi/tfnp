/-
Copyright (c) 2026 Angus Joshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Angus Joshi
-/

import Mathlib.Tactic.Linarith
import Mathlib.Control.Lawful

/-!
# A generic query model of computation

This file defines `QueryAlg Q R α`, a free monad over the operation
"ask the oracle at point `q : Q` and continue with the response `r : R`".

It models *adaptive black-box query algorithms* abstractly. A term of
`QueryAlg Q R α` is a (possibly infinitely branching) decision tree:
* `pure a` returns the value `a : α` without any queries;
* `query q κ` asks the oracle for the value at `q`, then continues with
  the continuation `κ : R → QueryAlg Q R α` applied to the response.

The algorithm is *adaptive* because the continuation `κ` is a function of
the response.

## Main definitions

* `QueryAlg.bind` and `Monad (QueryAlg Q R)`, `LawfulMonad (QueryAlg Q R)`
  instances — `do`-notation works.
* `QueryAlg.ask q : QueryAlg Q R R` — the primitive "ask the oracle for `q`
  and return the response" operation.
* `QueryAlg.run f : QueryAlg Q R α → α` — execute the algorithm against
  oracle `f : Q → R`.
* `QueryAlg.queries f : QueryAlg Q R α → ℕ` — count queries on a specific
  run.

The model is fully generic in the query type `Q` and response type `R`.
Specializations:
* Boolean decision oracles: `QueryAlg α Bool`.
* Set membership: `QueryAlg α Bool` (same as above).
* Value queries (e.g. CLY's contraction-map fixpoint): `QueryAlg α α`.
-/

namespace Tfnp

/-- A deterministic adaptive query algorithm with black-box access to an
oracle `Q → R`, producing a value of type `α`.

* `pure a` returns `a` with no queries.
* `query q κ` asks the oracle for the value at `q` and continues with `κ`
  applied to the oracle's response. -/
inductive QueryAlg (Q : Type) (R : Type) (α : Type) : Type
  | pure (a : α) : QueryAlg Q R α
  | query (q : Q) (κ : R → QueryAlg Q R α) : QueryAlg Q R α

namespace QueryAlg

variable {Q R α β : Type}

/-- Sequencing for `QueryAlg`. `pure a >>= f = f a`; `query q κ >>= f` asks
at `q` and continues with `κ resp >>= f`. This is the free monad bind. -/
protected def bind : QueryAlg Q R α → (α → QueryAlg Q R β) → QueryAlg Q R β
  | .pure a, f => f a
  | .query q κ, f => .query q (fun resp => (κ resp).bind f)

instance : Monad (QueryAlg Q R) where
  pure := QueryAlg.pure
  bind := QueryAlg.bind

/-- The primitive oracle query: asks for `f q` and returns the response. -/
def ask (q : Q) : QueryAlg Q R R := .query q .pure

/-- Execute a query algorithm against an oracle `f`, returning its final value. -/
def run (f : Q → R) : QueryAlg Q R α → α
  | .pure a => a
  | .query q κ => run f (κ (f q))

/-- The number of queries the algorithm makes when run against oracle `f`. -/
def queries (f : Q → R) : QueryAlg Q R α → ℕ
  | .pure _ => 0
  | .query q κ => 1 + queries f (κ (f q))

@[simp] lemma run_pure (f : Q → R) (a : α) :
    (QueryAlg.pure a : QueryAlg Q R α).run f = a := rfl

@[simp] lemma run_query (f : Q → R) (q : Q) (κ : R → QueryAlg Q R α) :
    (QueryAlg.query q κ).run f = (κ (f q)).run f := rfl

@[simp] lemma queries_pure (f : Q → R) (a : α) :
    (QueryAlg.pure a : QueryAlg Q R α).queries f = 0 := rfl

@[simp] lemma queries_query (f : Q → R) (q : Q) (κ : R → QueryAlg Q R α) :
    (QueryAlg.query q κ).queries f = 1 + (κ (f q)).queries f := rfl

@[simp] lemma run_bind (f : Q → R) (m : QueryAlg Q R α) (g : α → QueryAlg Q R β) :
    (m >>= g).run f = (g (m.run f)).run f := by
  induction m with
  | pure a => rfl
  | query q κ ih => simp only [Bind.bind, QueryAlg.bind, run]; exact ih (f q)

@[simp] lemma queries_bind (f : Q → R) (m : QueryAlg Q R α) (g : α → QueryAlg Q R β) :
    (m >>= g).queries f = m.queries f + (g (m.run f)).queries f := by
  induction m with
  | pure a => simp [Bind.bind, QueryAlg.bind, queries, run]
  | query q κ ih =>
    have h := ih (f q)
    simp only [Bind.bind, QueryAlg.bind, queries, run] at h ⊢
    omega

@[simp] lemma run_ask (f : Q → R) (q : Q) : (ask q : QueryAlg Q R R).run f = f q := rfl
@[simp] lemma queries_ask (f : Q → R) (q : Q) :
    (ask q : QueryAlg Q R R).queries f = 1 := by
  simp [ask, queries]

instance : LawfulMonad (QueryAlg Q R) := .mk'
  (id_map := fun x => by
    induction x with
    | pure a => rfl
    | query q κ ih =>
      show (id <$> _ : QueryAlg Q R _) = _
      simp only [Functor.map, QueryAlg.bind]
      congr 1
      funext resp
      exact ih resp)
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := fun m _ _ => by
    induction m with
    | pure a => rfl
    | query q κ ih =>
      change ((QueryAlg.query q κ).bind _).bind _ = (QueryAlg.query q κ).bind _
      simp only [QueryAlg.bind]
      congr 1
      funext resp
      exact ih resp)

end QueryAlg

end Tfnp
