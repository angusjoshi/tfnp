/-
Copyright (c) 2026 Angus Joshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Angus Joshi
-/

import Tfnp.Circuit
import Tfnp.PPAD

/-!
# End-of-Line with succinctly represented instances

`Tfnp/PPAD.lean` states `EndOfLine` with the successor and predecessor given as
arbitrary functions. That is the right *mathematical* object but not
Papadimitriou's problem: his instances are **circuits**, which is what makes the
input polynomially sized and the class non-trivial.

This file gives that version, `CircuitEndOfLine`, and connects the two:

* `circuitEndOfLine_isTotal` — totality, straight from the same parity argument;
* `circuitToTable` — the succinct version reduces to the tabular one, so
  `CircuitEndOfLine` sits inside `PPAD` for any `ReductionClass` containing this
  (very simple) reduction.

The reduction in the other direction is not available and cannot be: passing
from a function to a circuit computing it is exactly the step that needs the
function to be succinctly describable. That asymmetry is the whole point of the
succinct representation.
-/

set_option autoImplicit false

namespace Tfnp.PPAD

open Tfnp Tfnp.Circuit

/-- Read an `n`-bit input as a wire assignment. -/
def ofFin {n : ℕ} (x : Fin n → Bool) : ℕ → Bool :=
  fun j => if h : j < n then x ⟨j, h⟩ else false

/-- Run a multi-output circuit as a map on `n`-bit strings. Outputs beyond the
circuit's output list read as `false`, keeping this total. -/
def evalFin (c : MultiCircuit) (n : ℕ) (x : Fin n → Bool) : Fin n → Bool :=
  fun i => (c.eval (ofFin x)).getD i.val false

/-- **Papadimitriou's End-of-Line instance**: the successor and predecessor maps
are given by circuits, so the instance has size polynomial in `n` even though
the graph has `2^n` vertices. -/
structure CircuitEOL where
  /-- Number of bits; the graph has `2^n` vertices. -/
  n : ℕ
  /-- Circuit computing the successor. -/
  succ : MultiCircuit
  /-- Circuit computing the predecessor. -/
  pred : MultiCircuit
  /-- The all-`false` string has no predecessor. -/
  pred_zero : evalFin pred n (fun _ => false) = (fun _ => false)
  /-- The all-`false` string has a successor, so it is a source. -/
  succ_zero : evalFin succ n (fun _ => false) ≠ (fun _ => false)

/-- End-of-Line on succinctly represented instances. -/
def CircuitEndOfLine : SearchProblem where
  Inst := CircuitEOL
  Sol := fun x => Fin x.n → Bool
  Valid := fun x v =>
    evalFin x.pred x.n (evalFin x.succ x.n v) ≠ v ∨
      (evalFin x.succ x.n (evalFin x.pred x.n v) ≠ v ∧ v ≠ fun _ => false)

/-- Totality, from the same parity argument as the tabular version. -/
theorem circuitEndOfLine_isTotal : CircuitEndOfLine.IsTotal := by
  rintro ⟨n, S, P, hpz, hsz⟩
  exact exists_other_end (evalFin S n) (evalFin P n) (fun _ => false) hpz hsz

/-- **The succinct version reduces to the tabular one**: evaluate the circuits.
Note the reduction does no work on solutions at all — a solution of the tabular
instance *is* a solution of the circuit instance. -/
def circuitToTable : Reduction CircuitEndOfLine EndOfLine where
  inst := fun x =>
    { n := x.n
      succ := evalFin x.succ x.n
      pred := evalFin x.pred x.n
      pred_zero := x.pred_zero
      succ_zero := x.succ_zero }
  sol := fun _ v => v
  valid := fun _ _ h => h

/-- Consequently `CircuitEndOfLine` is in `PPAD`, for any reduction class that
admits `circuitToTable`. -/
theorem circuitEndOfLine_inPPAD (𝓡 : ReductionClass) (h : 𝓡.Ok circuitToTable) :
    InPPAD 𝓡 CircuitEndOfLine := ⟨circuitToTable, h⟩

end Tfnp.PPAD
