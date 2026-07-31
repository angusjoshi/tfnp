/-
Copyright (c) 2026 Angus Joshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Angus Joshi
-/

import Mathlib.Data.Real.Basic

/-!
# The closed box `[a, b]^k`

A one-definition file, split out so that consumers of `CubeBox` (notably
`Tfnp.Contraction` and `Tfnp.BalancedPoint`) do not have to import the Brouwer
development.
-/

/-- The closed `k`-dimensional box `[a, b]^k`. -/
def CubeBox (a b : ℝ) (k : ℕ) : Set (Fin k → ℝ) :=
  { x | ∀ i, a ≤ x i ∧ x i ≤ b }
