/-
Copyright (c) 2026 Angus Joshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Angus Joshi
-/

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith

/-!
# PPAD, abstractly

The class `PPAD` of Papadimitriou (*On the complexity of the parity argument and
other inefficient proofs of existence*, JCSS 1994), set up so that the
combinatorial content is separated from the model of computation.

## Design

Complexity classes of search problems are defined by two ingredients: a notion
of *reduction*, and a *complete problem*. Only the second is mathematics; the
first is a choice of computational model, and Mathlib currently has no usable
notion of polynomial time. So we parameterise:

* `Reduction P Q` is the combinatorial data of a many-one reduction — an
  instance map and a solution back-map — with no efficiency condition;
* `ReductionClass` is an abstract predicate selecting which reductions "count",
  required only to contain the identity and be closed under composition.

`PPAD` is then defined relative to a `ReductionClass 𝓡`. Instantiating `𝓡`
with poly-time-computable maps recovers the textbook class; every theorem below
holds for any instantiation.

## Main results

* `exists_other_end` — the parity argument: in a directed graph of in- and
  out-degree at most one, an unbalanced vertex forces a second one. This is the
  entire mathematical content of `PPAD`'s totality.
* `endOfLine_isTotal` — `EndOfLine` is a total search problem.
* `InPPAD.isTotal` — `PPAD ⊆ TFNP`: every problem in `PPAD` is total. Note this
  is derived from the single parity argument, not assumed.
* `ppadHard_iff_endOfLine_reduces` — `Q` is `PPAD`-hard iff `EndOfLine` reduces
  to it, so hardness proofs only ever need one reduction.
* `endOfLine_ppadComplete` — `EndOfLine` is `PPAD`-complete.
-/

set_option autoImplicit false

namespace Tfnp.PPAD

/-! ## Total search problems -/

/-- A search problem: a type of instances, a type of candidate solutions for
each instance, and a validity relation. -/
structure SearchProblem where
  /-- Instances of the problem. -/
  Inst : Type
  /-- Candidate solutions for a given instance. -/
  Sol : Inst → Type
  /-- Which candidates are actual solutions. -/
  Valid : (x : Inst) → Sol x → Prop

/-- A search problem is *total* when every instance has a solution. Total search
problems (with an efficiency condition on `Valid`) are the class `TFNP`. -/
def SearchProblem.IsTotal (P : SearchProblem) : Prop := ∀ x, ∃ s, P.Valid x s

/-! ## Reductions -/

/-- A many-one reduction from `P` to `Q`: map instances forward, map solutions
back. This is the combinatorial content; efficiency is imposed separately by a
`ReductionClass`. -/
structure Reduction (P Q : SearchProblem) where
  /-- Forward map on instances. -/
  inst : P.Inst → Q.Inst
  /-- Backward map on solutions. -/
  sol : (x : P.Inst) → Q.Sol (inst x) → P.Sol x
  /-- Solutions really do pull back to solutions. -/
  valid : ∀ x s, Q.Valid (inst x) s → P.Valid x (sol x s)

/-- The identity reduction. -/
def Reduction.refl (P : SearchProblem) : Reduction P P where
  inst := id
  sol := fun _ s => s
  valid := fun _ _ h => h

/-- Reductions compose. -/
def Reduction.trans {P Q R : SearchProblem} (f : Reduction P Q) (g : Reduction Q R) :
    Reduction P R where
  inst := g.inst ∘ f.inst
  sol := fun x s => f.sol x (g.sol (f.inst x) s)
  valid := fun x s h => f.valid x _ (g.valid (f.inst x) s h)

/-- Totality transfers backwards along a reduction: if `P` reduces to `Q` and
`Q` is total, so is `P`. -/
theorem SearchProblem.IsTotal.of_reduction {P Q : SearchProblem} (f : Reduction P Q)
    (hQ : Q.IsTotal) : P.IsTotal := by
  intro x
  obtain ⟨s, hs⟩ := hQ (f.inst x)
  exact ⟨f.sol x s, f.valid x s hs⟩

/-- An abstract notion of "efficient reduction": any predicate on reductions
containing the identity and closed under composition. Instantiate with
poly-time computability, log-space, or anything else with those closure
properties. -/
structure ReductionClass where
  /-- Which reductions count as efficient. -/
  Ok : {P Q : SearchProblem} → Reduction P Q → Prop
  /-- The identity reduction is efficient. -/
  ok_refl : ∀ P, Ok (Reduction.refl P)
  /-- Efficient reductions compose. -/
  ok_trans : ∀ {P Q R : SearchProblem} (f : Reduction P Q) (g : Reduction Q R),
    Ok f → Ok g → Ok (f.trans g)

/-- `P` reduces to `Q` within the class `𝓡`. -/
def Reduces (𝓡 : ReductionClass) (P Q : SearchProblem) : Prop :=
  ∃ f : Reduction P Q, 𝓡.Ok f

theorem Reduces.refl (𝓡 : ReductionClass) (P : SearchProblem) : Reduces 𝓡 P P :=
  ⟨Reduction.refl P, 𝓡.ok_refl P⟩

theorem Reduces.trans {𝓡 : ReductionClass} {P Q R : SearchProblem}
    (h₁ : Reduces 𝓡 P Q) (h₂ : Reduces 𝓡 Q R) : Reduces 𝓡 P R := by
  obtain ⟨f, hf⟩ := h₁
  obtain ⟨g, hg⟩ := h₂
  exact ⟨f.trans g, 𝓡.ok_trans f g hf hg⟩

theorem SearchProblem.IsTotal.of_reduces {𝓡 : ReductionClass} {P Q : SearchProblem}
    (h : Reduces 𝓡 P Q) (hQ : Q.IsTotal) : P.IsTotal := by
  obtain ⟨f, -⟩ := h
  exact hQ.of_reduction f


/-! ## Where the content actually lives

A warning, formalised. Without an efficiency condition the *combinatorial* data
of a reduction carries no information: any total problem reduces to any problem
with an instance, by mapping every instance to a fixed one and using totality
(and choice) to produce a solution. -/

/-- **The bare notion of reduction is vacuous.** If `P` is total and `Q` has at
least one instance, a `Reduction P Q` always exists.

Consequently every theorem about `PPAD` that has real content must go through
`𝓡.Ok`, and `PPAD` is only as meaningful as the `ReductionClass` instantiating
it. In particular, taking `Ok := fun _ => True` makes every total problem
`PPAD`-complete. Formalising the classical hardness results therefore requires
first building a genuine model of polynomial-time computation. -/
theorem nonempty_reduction_of_isTotal (P Q : SearchProblem) (hP : P.IsTotal)
    (q : Q.Inst) : Nonempty (Reduction P Q) :=
  ⟨{ inst := fun _ => q
     sol := fun x _ => (hP x).choose
     valid := fun x _ _ => (hP x).choose_spec }⟩

/-- The degenerate reduction class, in which everything counts. -/
def trivialClass : ReductionClass where
  Ok := fun _ => True
  ok_refl := fun _ => trivial
  ok_trans := fun _ _ _ _ => trivial

/-! ## The parity argument

The mathematical heart of `PPAD`. Consider the directed graph on `V` with an
edge `u → v` exactly when `succ u = v` and `pred v = u`. Every vertex has
out-degree at most one (via `succ`) and in-degree at most one (via `pred`), so
the graph is a disjoint union of paths and cycles, and the endpoints of paths
come in pairs. Hence one known endpoint forces another. -/

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Vertices with a genuine outgoing edge. -/
private def hasOut (succ pred : V → V) : Finset V :=
  Finset.univ.filter (fun v => pred (succ v) = v)

/-- Vertices with a genuine incoming edge. -/
private def hasIn (succ pred : V → V) : Finset V :=
  Finset.univ.filter (fun v => succ (pred v) = v)

/-- `succ` is a bijection from the vertices with an outgoing edge to those with
an incoming edge, with inverse `pred`. Hence the two sets have equal size. -/
private theorem card_hasOut_eq_card_hasIn (succ pred : V → V) :
    (hasOut succ pred).card = (hasIn succ pred).card := by
  refine Finset.card_bij (fun v _ => succ v) ?_ ?_ ?_
  · -- `succ` lands in `hasIn`.
    intro v hv
    rw [hasOut, Finset.mem_filter] at hv
    rw [hasIn, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by rw [hv.2]⟩
  · -- injective, because `pred` undoes `succ` on `hasOut`.
    intro v₁ h₁ v₂ h₂ hEq
    simp only at hEq
    rw [hasOut, Finset.mem_filter] at h₁ h₂
    have h3 : pred (succ v₁) = pred (succ v₂) := by rw [hEq]
    rw [h₁.2, h₂.2] at h3
    exact h3
  · -- surjective, because `pred w` is an outgoing vertex mapping to `w`.
    intro w hw
    rw [hasIn, Finset.mem_filter] at hw
    refine ⟨pred w, ?_, hw.2⟩
    rw [hasOut, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by rw [hw.2]⟩

/-- **The parity argument.** If `v₀` is a source — no incoming edge
(`pred v₀ = v₀`) but a genuine outgoing one (`succ v₀ ≠ v₀`) — then some vertex
is an endpoint other than `v₀`: either it has no outgoing edge, or it has no
incoming edge and is not `v₀`.

This is the totality of `EndOfLine`, and hence of all of `PPAD`. -/
theorem exists_other_end (succ pred : V → V) (v₀ : V)
    (hpred : pred v₀ = v₀) (hsucc : succ v₀ ≠ v₀) :
    ∃ v, pred (succ v) ≠ v ∨ (succ (pred v) ≠ v ∧ v ≠ v₀) := by
  by_contra hcon
  push_neg at hcon
  -- No solution means: every vertex has an outgoing edge, and every vertex
  -- other than `v₀` has an incoming edge.
  have hout : hasOut succ pred = Finset.univ := by
    rw [hasOut, Finset.filter_eq_self]
    intro v _
    exact (hcon v).1
  -- `|hasIn| = |hasOut| = |V|`, so every vertex has an incoming edge — `v₀` too.
  have hcard : (hasIn succ pred).card = Fintype.card V := by
    rw [← card_hasOut_eq_card_hasIn, hout, Finset.card_univ]
  have hin : hasIn succ pred = Finset.univ := Finset.eq_univ_of_card _ hcard
  have hv₀ : succ (pred v₀) = v₀ := by
    have : v₀ ∈ hasIn succ pred := hin ▸ Finset.mem_univ v₀
    rw [hasIn, Finset.mem_filter] at this
    exact this.2
  -- But `pred v₀ = v₀`, so `succ v₀ = v₀` — contradiction.
  rw [hpred] at hv₀
  exact hsucc hv₀

/-! ## End-of-Line -/

/-- An `EndOfLine` instance on `n`-bit vertices: successor and predecessor
circuits (here, arbitrary functions — the efficiency of the *instance* is the
`ReductionClass`'s business, not ours) together with the promise that the
all-`false` string is a source. -/
structure EOLInstance where
  /-- Number of bits. -/
  n : ℕ
  /-- Successor map. -/
  succ : (Fin n → Bool) → (Fin n → Bool)
  /-- Predecessor map. -/
  pred : (Fin n → Bool) → (Fin n → Bool)
  /-- The all-`false` string has no predecessor. -/
  pred_zero : pred (fun _ => false) = (fun _ => false)
  /-- The all-`false` string has a successor, so it really is a source. -/
  succ_zero : succ (fun _ => false) ≠ (fun _ => false)

/-- **End-of-Line**, the canonical `PPAD`-complete problem: given a source of an
implicit graph with in- and out-degree at most one, find another endpoint. -/
def EndOfLine : SearchProblem where
  Inst := EOLInstance
  Sol := fun x => Fin x.n → Bool
  Valid := fun x v =>
    x.pred (x.succ v) ≠ v ∨ (x.succ (x.pred v) ≠ v ∧ v ≠ fun _ => false)

theorem endOfLine_isTotal : EndOfLine.IsTotal := by
  rintro ⟨n, succ, pred, hpz, hsz⟩
  exact exists_other_end succ pred (fun _ => false) hpz hsz

/-! ## The class -/

variable (𝓡 : ReductionClass)

/-- `P ∈ PPAD`: `P` reduces to `EndOfLine`. -/
def InPPAD (P : SearchProblem) : Prop := Reduces 𝓡 P EndOfLine

/-- `Q` is `PPAD`-hard: everything in `PPAD` reduces to `Q`. -/
def PPADHard (Q : SearchProblem) : Prop := ∀ P, InPPAD 𝓡 P → Reduces 𝓡 P Q

/-- `Q` is `PPAD`-complete. -/
def PPADComplete (Q : SearchProblem) : Prop := InPPAD 𝓡 Q ∧ PPADHard 𝓡 Q

/-- **`PPAD ⊆ TFNP`.** Every problem in `PPAD` is total — a consequence of the
single parity argument `exists_other_end`, not an extra assumption. -/
theorem InPPAD.isTotal {P : SearchProblem} (h : InPPAD 𝓡 P) : P.IsTotal :=
  SearchProblem.IsTotal.of_reduces h endOfLine_isTotal

theorem endOfLine_inPPAD : InPPAD 𝓡 EndOfLine := Reduces.refl 𝓡 EndOfLine

/-- Hardness only ever requires one reduction: `Q` is `PPAD`-hard exactly when
`EndOfLine` reduces to `Q`. -/
theorem ppadHard_iff_endOfLine_reduces {Q : SearchProblem} :
    PPADHard 𝓡 Q ↔ Reduces 𝓡 EndOfLine Q := by
  constructor
  · intro h
    exact h EndOfLine (endOfLine_inPPAD 𝓡)
  · intro h P hP
    exact Reduces.trans hP h

theorem endOfLine_ppadHard : PPADHard 𝓡 EndOfLine :=
  (ppadHard_iff_endOfLine_reduces 𝓡).mpr (Reduces.refl 𝓡 EndOfLine)

theorem endOfLine_ppadComplete : PPADComplete 𝓡 EndOfLine :=
  ⟨endOfLine_inPPAD 𝓡, endOfLine_ppadHard 𝓡⟩

/-- A `PPAD`-complete problem is total. -/
theorem PPADComplete.isTotal {Q : SearchProblem} (h : PPADComplete 𝓡 Q) : Q.IsTotal :=
  InPPAD.isTotal 𝓡 h.1

/-- Making the warning concrete: under `trivialClass`, every total problem with
an instance is `PPAD`-complete. Any instantiation of `ReductionClass` used for
real hardness statements must therefore be checked to be non-degenerate. -/
theorem trivialClass_degenerate (Q : SearchProblem) (hQ : Q.IsTotal) (q : Q.Inst) :
    PPADComplete trivialClass Q := by
  constructor
  · exact ⟨(nonempty_reduction_of_isTotal Q EndOfLine hQ
      ⟨1, fun _ _ => true, fun v => v, rfl, by
        intro h
        have := congrFun h ⟨0, by norm_num⟩
        simp at this⟩).some, trivial⟩
  · intro P hP
    exact ⟨(nonempty_reduction_of_isTotal P Q (hP.isTotal trivialClass) q).some, trivial⟩

end Tfnp.PPAD
