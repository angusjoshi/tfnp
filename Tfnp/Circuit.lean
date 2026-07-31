/-
Copyright (c) 2026 Angus Joshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Angus Joshi
-/

import Mathlib.Data.List.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Linarith

/-!
# Boolean circuits

A straight-line-program model of Boolean circuits, built so that `PPAD` can be
stated the way Papadimitriou stated it: instances are *succinctly represented*
by circuits, not by exponential truth tables.

Circuits are directed acyclic graphs, not formulas. Using DAGs is not a detail:
poly-size *formulas* compute a strictly weaker class than poly-size *circuits*,
so a tree-based model would define the wrong complexity class.

## Wire numbering

A computation carries a list of wire values, starting as the input bits, with
each gate appending its output. So wire `i` is uniformly `wires.getD i false` —
inputs and gate outputs are not distinguished. That uniformity makes
`Gate.shiftAll` plain addition, which is what makes composition (`comp`,
`eval_comp`) provable without index case-splits.

## Main definitions

* `Gate`, `evalWires`, `MultiCircuit`, `MultiCircuit.eval`, `size`
* `MultiCircuit.comp`, `eval_comp`, `size_comp` — composition
* `PolySize` — polynomially bounded families, closed under sums
-/

set_option autoImplicit false

namespace Tfnp.Circuit

/-- A gate of a straight-line program. Operands are wire indices; a well-formed
circuit refers only to strictly earlier wires, but evaluation is total either
way (out-of-range reads are `false`). -/
inductive Gate : Type
  | const (b : Bool) : Gate
  | not (i : ℕ) : Gate
  | and (i j : ℕ) : Gate
  | or (i j : ℕ) : Gate
  deriving DecidableEq, Repr

/-- Evaluate one gate against the wires computed so far. -/
def evalGate (acc : List Bool) : Gate → Bool
  | .const b => b
  | .not i => !(acc.getD i false)
  | .and i j => (acc.getD i false) && (acc.getD j false)
  | .or i j => (acc.getD i false) || (acc.getD j false)

/-- Run a gate list, starting from the input wires and appending each output. -/
def evalWires (w : List Bool) (gs : List Gate) : List Bool :=
  gs.foldl (fun acc g => acc ++ [evalGate acc g]) w

@[simp] lemma evalWires_nil (w : List Bool) : evalWires w [] = w := rfl

@[simp] lemma evalWires_cons (w : List Bool) (g : Gate) (gs : List Gate) :
    evalWires w (g :: gs) = evalWires (w ++ [evalGate w g]) gs := rfl

lemma evalWires_append (w : List Bool) (gs hs : List Gate) :
    evalWires w (gs ++ hs) = evalWires (evalWires w gs) hs := by
  unfold evalWires; rw [List.foldl_append]

/-- Wire lists grow by exactly one per gate. -/
theorem length_evalWires (w : List Bool) (gs : List Gate) :
    (evalWires w gs).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp only [evalWires_cons, ih, List.length_append,
      List.length_cons, List.length_nil]; omega

/-- Shift every wire reference by a constant. -/
def Gate.shiftAll (p : ℕ) : Gate → Gate
  | .const b => .const b
  | .not i => .not (p + i)
  | .and i j => .and (p + i) (p + j)
  | .or i j => .or (p + i) (p + j)

/-- Reading past a prefix. -/
theorem getD_append_add (pre y : List Bool) (i : ℕ) :
    (pre ++ y).getD (pre.length + i) false = y.getD i false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (Nat.le_add_right _ _)]
  simp

theorem getD_append_left {pre : List Bool} (y : List Bool) {i : ℕ}
    (h : i < pre.length) : (pre ++ y).getD i false = pre.getD i false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_left h]

theorem evalGate_shiftAll (pre y : List Bool) (g : Gate) :
    evalGate (pre ++ y) (g.shiftAll pre.length) = evalGate y g := by
  cases g <;> simp only [evalGate, Gate.shiftAll, getD_append_add]

/-- **Relocation.** A shifted gate list run after a prefix computes exactly what
the unshifted list computes, left in place after the prefix. This is the lemma
that makes circuit composition work. -/
theorem evalWires_shiftAll (pre y : List Bool) (gs : List Gate) :
    evalWires (pre ++ y) (gs.map (Gate.shiftAll pre.length))
      = pre ++ evalWires y gs := by
  induction gs generalizing y with
  | nil => simp
  | cons g gs ih =>
    rw [List.map_cons, evalWires_cons, evalGate_shiftAll, evalWires_cons,
      List.append_assoc, ih]

/-! ## Multi-output circuits -/

/-- A circuit with several outputs sharing one gate list. -/
structure MultiCircuit where
  /-- Number of input wires. -/
  inputs : ℕ
  /-- The gates, in topological order. -/
  gates : List Gate
  /-- Output wire indices. -/
  outputs : List ℕ
  deriving Repr

namespace MultiCircuit

/-- The initial wire list for an input assignment. -/
def initWires (n : ℕ) (x : ℕ → Bool) : List Bool := (List.range n).map x

@[simp] lemma length_initWires (n : ℕ) (x : ℕ → Bool) : (initWires n x).length = n := by
  simp [initWires]

/-- Evaluate all outputs. -/
def eval (c : MultiCircuit) (x : ℕ → Bool) : List Bool :=
  (c.outputs.map (fun o => (evalWires (initWires c.inputs x) c.gates).getD o false))

/-- Size: the number of gates. -/
def size (c : MultiCircuit) : ℕ := c.gates.length

@[simp] lemma length_eval (c : MultiCircuit) (x : ℕ → Bool) :
    (c.eval x).length = c.outputs.length := by simp [eval]

/-- The identity circuit on `n` bits. -/
def id (n : ℕ) : MultiCircuit where
  inputs := n
  gates := []
  outputs := List.range n

@[simp] lemma size_id (n : ℕ) : (id n).size = 0 := rfl

theorem eval_id (n : ℕ) (x : ℕ → Bool) : (id n).eval x = (List.range n).map x := by
  simp only [eval, id, evalWires_nil, initWires]
  refine List.map_congr_left fun i hi => ?_
  rw [List.mem_range] at hi
  simp [List.getD_eq_getElem?_getD, hi]

/-- Composition `d ∘ c`: run `c`, copy its outputs onto consecutive fresh wires
(with `or o o` gates, which just re-read wire `o`), then run `d` shifted onto
them. -/
def comp (c d : MultiCircuit) : MultiCircuit where
  inputs := c.inputs
  gates := c.gates ++ c.outputs.map (fun o => Gate.or o o)
              ++ d.gates.map (Gate.shiftAll (c.inputs + c.gates.length))
  outputs := d.outputs.map (fun o => c.inputs + c.gates.length + o)

@[simp] theorem size_comp (c d : MultiCircuit) :
    (comp c d).size = c.size + c.outputs.length + d.size := by
  simp [comp, size]
  omega

/-- Running a block of `or o o` gates appends the values of those wires. -/
theorem evalWires_copies (os : List ℕ) (pre : List Bool)
    (hos : ∀ o ∈ os, o < pre.length) :
    evalWires pre (os.map (fun o => Gate.or o o))
      = pre ++ os.map (fun o => pre.getD o false) := by
  induction os generalizing pre with
  | nil => simp
  | cons o os ih =>
    have hg : evalGate pre (Gate.or o o) = pre.getD o false := by simp [evalGate]
    have hos' : ∀ p ∈ os, p < (pre ++ [pre.getD o false]).length := by
      intro p hp
      have := hos p (by simp [hp])
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    rw [List.map_cons, evalWires_cons, hg, ih _ hos', List.append_assoc]
    congr 1
    rw [List.map_cons, List.singleton_append]
    congr 1
    refine List.map_congr_left fun p hp => ?_
    exact getD_append_left _ (hos p (by simp [hp]))

/-- **Composition computes the composite.** -/
theorem eval_comp (c d : MultiCircuit) (x : ℕ → Bool)
    (hd : d.inputs = c.outputs.length)
    (hwf : ∀ o ∈ c.outputs, o < c.inputs + c.gates.length) :
    (comp c d).eval x = d.eval (fun j => (c.eval x).getD j false) := by
  set w := evalWires (initWires c.inputs x) c.gates with hw
  have hlen : w.length = c.inputs + c.gates.length := by
    rw [hw, length_evalWires, length_initWires]
  have hcopies : evalWires (initWires c.inputs x)
      (c.gates ++ c.outputs.map (fun o => Gate.or o o)) = w ++ c.eval x := by
    rw [evalWires_append, ← hw, evalWires_copies _ _ (by
      intro o ho; rw [hlen]; exact hwf o ho)]
    rfl
  have hinit : initWires d.inputs (fun j => (c.eval x).getD j false) = c.eval x := by
    rw [hd]
    simp only [initWires]
    refine List.ext_getElem (by simp) fun i h1 h2 => ?_
    rw [List.getElem_map, List.getElem_range, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by simpa using h2)]
    rfl
  have hRHS : d.eval (fun j => (c.eval x).getD j false)
      = d.outputs.map (fun o => (evalWires (c.eval x) d.gates).getD o false) := by
    show d.outputs.map (fun o => (evalWires
      (initWires d.inputs (fun j => (c.eval x).getD j false)) d.gates).getD o false) = _
    rw [hinit]
  have hLHS : (comp c d).eval x
      = d.outputs.map
          (fun o => (w ++ evalWires (c.eval x) d.gates).getD (w.length + o) false) := by
    unfold eval comp
    dsimp only
    rw [evalWires_append, hcopies, ← hlen, evalWires_shiftAll, List.map_map]
    rfl
  rw [hLHS, hRHS]
  refine List.map_congr_left fun o _ => ?_
  rw [getD_append_add]

end MultiCircuit

/-! ## Polynomially sized families -/

/-- A family of circuits, one per input length, of polynomially bounded size. -/
def PolySize (c : ℕ → MultiCircuit) : Prop :=
  ∃ a k b : ℕ, ∀ n, (c n).size ≤ a * (n + 1) ^ k + b

theorem polySize_of_const {c : ℕ → MultiCircuit} {m : ℕ} (h : ∀ n, (c n).size ≤ m) :
    PolySize c := ⟨0, 0, m, fun n => by simpa using h n⟩

theorem polySize_id : PolySize MultiCircuit.id :=
  polySize_of_const (m := 0) fun _ => le_refl 0

/-- Polynomial bounds are closed under sums. With `size_comp` this gives
closure of the class under composition. -/
theorem polySize_add {c d e : ℕ → MultiCircuit} (hc : PolySize c) (hd : PolySize d)
    (he : ∀ n, (e n).size ≤ (c n).size + (d n).size) : PolySize e := by
  obtain ⟨a₁, k₁, b₁, h₁⟩ := hc
  obtain ⟨a₂, k₂, b₂, h₂⟩ := hd
  refine ⟨a₁ + a₂, max k₁ k₂, b₁ + b₂, fun n => ?_⟩
  have p1 : (n + 1) ^ k₁ ≤ (n + 1) ^ (max k₁ k₂) :=
    Nat.pow_le_pow_right (by omega) (le_max_left _ _)
  have p2 : (n + 1) ^ k₂ ≤ (n + 1) ^ (max k₁ k₂) :=
    Nat.pow_le_pow_right (by omega) (le_max_right _ _)
  have q1 : a₁ * (n + 1) ^ k₁ ≤ a₁ * (n + 1) ^ (max k₁ k₂) := Nat.mul_le_mul_left _ p1
  have q2 : a₂ * (n + 1) ^ k₂ ≤ a₂ * (n + 1) ^ (max k₁ k₂) := Nat.mul_le_mul_left _ p2
  have hsum : (a₁ + a₂) * (n + 1) ^ (max k₁ k₂)
      = a₁ * (n + 1) ^ (max k₁ k₂) + a₂ * (n + 1) ^ (max k₁ k₂) := Nat.add_mul _ _ _
  have e₁ := h₁ n
  have e₂ := h₂ n
  have := he n
  omega

end Tfnp.Circuit
