/-
Copyright (c) 2026 Angus Joshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Angus Joshi
-/
import Tfnp.Tarski.Bound
import Tfnp.Tarski.LevelsetLoop

/-!
# The Haslebacher–Lill bound for `Tarski(n, d)`, unconditionally

`Tfnp/Tarski/Bound.lean` reduced the Tarski problem on `[0,n]^d` to a levelset
subprocedure in dimension three (`tarski_cube_bound_dim3`), leaving that
subprocedure as a hypothesis.  `Tfnp/Tarski/LevelsetLoop.lean` supplies it
(`solvesLevelset_lsInner`, `lsInner_bounded`), so the hypothesis can now be
discharged.

Putting the two together:

* `solvesLevelset_hl` — the levelset problem on `[0,n]³` is solved in
  `61⌈log₂(n+1)⌉ + 29` queries.
* `tarski_cube_bound_hl` — hence `Tarski(n, d)` for `d = b + 3m` is solved in
  `iterBudget qbase (⌈log₂ 3n⌉ · q₃ + 5) m` queries, which `iterBudget_le` puts in
  the closed form `(qbase + 2) · (⌈log₂ 3n⌉ · q₃ + 6)^m` with
  `q₃ = O(log n)`, i.e. `O(log^(2⌈d/3⌉) n)`.
* `tarski_cube_bound_all` — the same with the base block discharged too, so every
  dimension is covered: take `b = d % 3` and `m = d / 3`.

Nothing in this chain is assumed: `Tfnp/Tarski/Decomposition.lean` proves the
Fearnley–Pálvölgyi–Savani decomposition theorem, and `Tfnp/Tarski/Levelset*.lean`
proves all of Haslebacher–Lill §3.
-/

namespace Tfnp.Tarski

open QueryAlg (Bounded)

/-- The budget the levelset subprocedure needs on the cube `[0, n]³`: enough that
`2 ^ budget` dominates the side length. -/
def hlBudget (n : ℕ) : ℕ := Nat.clog 2 (n + 1)

lemma hlBudget_spec (n : ℕ) :
    ∀ j : Fin 3, cubeHi 3 n j - cubeLo 3 j + 1 ≤ 2 ^ hlBudget n := by
  intro j
  have h : n + 1 ≤ 2 ^ Nat.clog 2 (n + 1) := Nat.le_pow_clog (by omega) _
  simpa [cubeHi, cubeLo, hlBudget] using h

/-- **The levelset problem in dimension three is solved in `O(log n)` queries.**
This is Haslebacher–Lill §3, adapted to the total setting. -/
theorem solvesLevelset_hl (n : ℕ) :
    SolvesLevelset (lsInner (hlBudget n)) (cubeLo 3) (cubeHi 3 n) :=
  solvesLevelset_lsInner (hlBudget_spec n)

/-- The query count of the levelset subprocedure, uniform over sub-boxes and
levels. -/
theorem hl_bounded (n : ℕ) (lo hi : Pt 3) (k : ℕ) :
    Bounded (61 * hlBudget n + 29) (lsInner (hlBudget n) lo hi k) :=
  lsInner_bounded _ _ _ _

/-- **A fully proved `O(log^(2⌈d/3⌉) n)` query upper bound for `Tarski(n, d)`.**
Blocks of three, each solved by the Haslebacher–Lill levelset recursion, composed
with the FPS decomposition theorem. -/
theorem tarski_cube_bound_hl (n : ℕ) (b : ℕ)
    {algBase : QueryAlg (Pt b) (Pt b) (Answer b)} {qbase : ℕ}
    (hBase : SolvesMapsTo algBase (cubeLo b) (cubeHi b n))
    (hBaseq : Bounded qbase algBase) :
    ∀ m : ℕ, ∃ alg : QueryAlg (Pt (dimOf b 3 m)) (Pt (dimOf b 3 m)) (Answer (dimOf b 3 m)),
      SolvesMapsTo alg (cubeLo (dimOf b 3 m)) (cubeHi (dimOf b 3 m) n)
        ∧ Bounded (iterBudget qbase
            (Nat.clog 2 (3 * n) * (61 * hlBudget n + 29) + 2 + 3) m) alg :=
  tarski_cube_bound_dim3 n (solvesLevelset_hl n) (hl_bounded n) b hBase hBaseq

/-- The same, with the base block discharged as well, so that every dimension is
covered: `d = b + 3 * m` with `b = d % 3` and `m = d / 3` (see `dimOf_eq`). -/
theorem tarski_cube_bound_all (n b : ℕ) (hb : b < 3) (m : ℕ) :
    ∃ (alg : QueryAlg (Pt (dimOf b 3 m)) (Pt (dimOf b 3 m)) (Answer (dimOf b 3 m))) (qbase : ℕ),
      SolvesMapsTo alg (cubeLo (dimOf b 3 m)) (cubeHi (dimOf b 3 m) n)
        ∧ Bounded (iterBudget qbase
            (Nat.clog 2 (3 * n) * (61 * hlBudget n + 29) + 2 + 3) m) alg := by
  obtain ⟨algBase, qbase, hBase, hBaseq⟩ := exists_base_solver n b hb
  obtain ⟨alg, hsol, hbd⟩ := tarski_cube_bound_hl n b hBase hBaseq m
  exact ⟨alg, qbase, hsol, hbd⟩

end Tfnp.Tarski
