/-
Copyright (c) 2026 Angus Joshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Angus Joshi
-/
import Tfnp.HitRun

/-!
# Polynomial time, given a sampler oracle

`Tfnp/HitRun.lean` reduces the poly-**time** question to sampling the non-convex
candidate body. This file makes the *time* accounting explicit and proves the
reduction is polynomial-time **given an oracle to the sampler**.

The pure query model (`QueryAlg`) counts only oracle calls, so it cannot by
itself express a running-time bound. We therefore add a **unit-cost measure** on
top of it (this is the "outside the query model" step): every round is charged

* `1` for the query to the contraction `f`;
* `samplerCost h` for one call to the sampler oracle on the current cut history;
* `balancedCost S` for the Fermat–Weber LP that turns the sample `S` into a
  balanced point (a genuine balanced point exists by `exists_balanced_point_box`,
  and minimising `Σ_{y∈S} ‖y−c‖∞` over a *finite* `S` is a linear program —
  poly-time in the standard model);
* `k + 1` for forming the cut vector `(c, sgn(f c − c))`.

The number of rounds is the CLY round count `k·(log₂⌈64/ε²⌉ + 2) + 1`
(`clyAlgorithm_queries_le`). The main theorem, `hitrun_time_poly`, bounds the
total cost by the **product** of the (polynomial) round count and the
(polynomial, if the oracles are polynomial) per-round cost — i.e. the algorithm
runs in `poly(k, log 1/ε)` time whenever the sampler and the LP do.

`endToEnd` wires correctness and time together: given a "good sampler" that
drives a geometric per-round contraction toward the fixed point, the output is an
`ε`-approximate fixed point **and** the run is polynomial-cost.

**CAVEAT — unit-cost model.** All bounds here are in the **unit-cost (RAM-like)
model**: one arithmetic operation, comparison, or real-vector coordinate touch
counts as `1`, and the oracles are charged by explicit meters. This is *not* a
bit-complexity / Turing-machine bound (we do not track number bit-lengths). This
is a deliberate, stated simplification: a polynomial-time algorithm *even in the
unit-cost model* would already be a major breakthrough (it would put simple
stochastic games in P), so the model is not what makes the problem open — the
polynomial-time **sampler** is (the open isoperimetry problem,
`notes/hitrun.md`). The pure **query model** (`Tfnp/Algorithm.lean`,
`cly_query_complexity`) is untouched and remains independently viewable; this
file only adds a cost layer on top of it. Everything here is `sorry`-free.
-/

set_option autoImplicit false

namespace Tfnp.Contraction

variable {k : ℕ}

/-! ## A unit-cost model for iterated computation -/

/-- Run `step` for `R` rounds from state `s`, accumulating the per-round costs
(the second component of `step`). This is the cost meter the query model lacks. -/
def costedRun {S : Type} (step : S → S × ℕ) : ℕ → S → ℕ
  | 0, _ => 0
  | (n + 1), s => (step s).2 + costedRun step n (step s).1

/-- **The core time bound.** If every round costs at most `B`, then `R` rounds
cost at most `R · B`. (Query model gives `R`; this gives per-round `B`.) -/
theorem costedRun_le {S : Type} (step : S → S × ℕ) (B : ℕ)
    (hB : ∀ s, (step s).2 ≤ B) : ∀ (R : ℕ) (s : S), costedRun step R s ≤ R * B := by
  intro R
  induction R with
  | zero => intro s; simp [costedRun]
  | succ n ih =>
      intro s
      have e : costedRun step (n + 1) s = (step s).2 + costedRun step n (step s).1 := rfl
      rw [e]
      calc (step s).2 + costedRun step n (step s).1
          ≤ B + n * B := Nat.add_le_add (hB s) (ih (step s).1)
        _ = (n + 1) * B := by ring

/-! ## The sampler oracle and one round of the algorithm -/

/-- The history a round sees: the cuts made so far, each a `(center, sign)`. -/
abbrev CutHist (k : ℕ) := List (Vec k × (Fin k → ℝ))

/-- The oracles the polynomial-time algorithm is given, each with a cost meter.
`sampler` returns `~uniform` points of the current candidate region; `balanced`
is the Fermat–Weber LP that returns a balanced point of a finite sample. Their
costs `samplerCost`, `balancedCost` are what must be polynomial. -/
structure Oracles (k : ℕ) where
  /-- The contraction being solved (one unit-cost query per round). -/
  f : Vec k → Vec k
  /-- Sampler: cut history → a finite sample of the candidate region. -/
  sampler : CutHist k → Finset (Vec k)
  /-- Cost of one sampler call. -/
  samplerCost : CutHist k → ℕ
  /-- Fermat–Weber LP: a finite point set → its balanced point. -/
  balanced : Finset (Vec k) → Vec k
  /-- Cost of one LP solve. -/
  balancedCost : Finset (Vec k) → ℕ

/-- The next cut history after one round: sample, take the balanced point `c`,
query `f`, append the ternary-sign cut `(c, sgn(f c − c))`. -/
noncomputable def roundNext (O : Oracles k) (h : CutHist k) : CutHist k :=
  let c := O.balanced (O.sampler h)
  h ++ [(c, fun i => sgnR (O.f c i - c i))]

/-- The unit cost of one round: `f`-query `+` sampler `+` LP `+` forming the cut. -/
def roundCost (O : Oracles k) (h : CutHist k) : ℕ :=
  1 + O.samplerCost h + O.balancedCost (O.sampler h) + (k + 1)

/-- One costed round, as a `costedRun` step. -/
noncomputable def round (O : Oracles k) (h : CutHist k) : CutHist k × ℕ :=
  (roundNext O h, roundCost O h)

/-- With polynomial per-call oracle costs, each round costs a bounded amount. -/
theorem round_cost_le (O : Oracles k) {pS pB : ℕ}
    (hS : ∀ h, O.samplerCost h ≤ pS) (hB : ∀ S, O.balancedCost S ≤ pB) (h : CutHist k) :
    (round O h).2 ≤ 1 + pS + pB + (k + 1) := by
  have h1 := hS h
  have h2 := hB (O.sampler h)
  simp only [round, roundCost]
  omega

/-! ## Main results -/

/-- **Total cost = rounds × per-round.** Running the algorithm for `R` rounds
from any initial history costs at most `R · (1 + pS + pB + (k+1))`, given
per-call oracle cost bounds `pS` (sampler) and `pB` (LP). -/
theorem hitrun_cost_le (O : Oracles k) (init : CutHist k) {pS pB : ℕ}
    (hS : ∀ h, O.samplerCost h ≤ pS) (hB : ∀ S, O.balancedCost S ≤ pB) (R : ℕ) :
    costedRun (round O) R init ≤ R * (1 + pS + pB + (k + 1)) :=
  costedRun_le (round O) _ (fun h => round_cost_le O hS hB h) R init

/-- **Polynomial time given the oracles.** With the CLY round count
`R ≤ k·(log₂⌈64/ε²⌉ + 2) + 1` (`clyAlgorithm_queries_le`) and polynomial
per-call costs `pS` (sampler) and `pB` (Fermat–Weber LP), the total unit cost of
the algorithm is bounded by

  `(k·(log₂⌈64/ε²⌉ + 2) + 1) · (1 + pS + pB + (k + 1))`,

a polynomial in `k` and `log(1/ε)`. Thus a polynomial-time sampler (`pS`, and the
sample size feeding `pB`, polynomial in `k`) yields a polynomial-time algorithm. -/
theorem hitrun_time_poly (O : Oracles k) (init : CutHist k) {pS pB : ℕ}
    (hS : ∀ h, O.samplerCost h ≤ pS) (hB : ∀ S, O.balancedCost S ≤ pB)
    (ε : ℝ) (R : ℕ) (hR : R ≤ k * (Nat.log 2 ⌈64 / ε ^ 2⌉₊ + 2) + 1) :
    costedRun (round O) R init
      ≤ (k * (Nat.log 2 ⌈64 / ε ^ 2⌉₊ + 2) + 1) * (1 + pS + pB + (k + 1)) := by
  refine (hitrun_cost_le O init hS hB R).trans ?_
  gcongr

/-! ## Wiring correctness and time together -/

/-- Geometric decay: if `ρ (t+1) ≤ q · ρ t` with `0 ≤ q`, then `ρ R ≤ q^R · ρ 0`. -/
theorem dist_geom_decay {q : ℝ} (hq : 0 ≤ q) (ρ : ℕ → ℝ)
    (hstep : ∀ t, ρ (t + 1) ≤ q * ρ t) : ∀ R, ρ R ≤ q ^ R * ρ 0 := by
  intro R
  induction R with
  | zero => simp
  | succ n ih =>
      calc ρ (n + 1) ≤ q * ρ n := hstep n
        _ ≤ q * (q ^ n * ρ 0) := mul_le_mul_of_nonneg_left ih hq
        _ = q ^ (n + 1) * ρ 0 := by ring

/-- **End-to-end: correct and polynomial-cost, given a good sampler.**

Model the algorithm's output after `t` rounds by `out t`, and package what a
*good* sampler achieves as a geometric per-round contraction toward the fixed
point `xs`: `‖out (t+1) − xs‖∞ ≤ q · ‖out t − xs‖∞` with `0 ≤ q < 1`. If `R`
rounds bring the output within `ε/(1+λ)` of `xs` (`hclose`), then:

* **correctness** — `out R` is an `ε`-approximate fixed point of `f`
  (`isApproxFixedPoint_of_near`, i.e. `HitRun`'s extraction lemma, applied to the
  geometric decay); and
* **time** — with the CLY round count and polynomial oracle costs, the run costs
  `≤ (k·(log₂⌈64/ε²⌉+2)+1)·(1+pS+pB+(k+1))` unit operations (`hitrun_time_poly`).

The one hypothesis carrying the open problem is `hshrink` (that the sampler
actually drives the geometric contraction in poly time); everything else is
proved. The pure query model is not referenced here. -/
theorem endToEnd [NeZero k]
    {lam ε : ℝ} {f : Vec k → Vec k} (hf : IsLInfContraction f lam)
    {xs : Vec k} (hxs : InUnitCube xs) (hfix : f xs = xs)
    (out : ℕ → Vec k) (hout : ∀ t, InUnitCube (out t))
    {q : ℝ} (hq0 : 0 ≤ q)
    (hshrink : ∀ t, linfDist (out (t + 1)) xs ≤ q * linfDist (out t) xs)
    (R : ℕ) (hclose : (1 + lam) * (q ^ R * linfDist (out 0) xs) ≤ ε)
    (O : Oracles k) {pS pB : ℕ}
    (hS : ∀ h, O.samplerCost h ≤ pS) (hB : ∀ S, O.balancedCost S ≤ pB)
    (init : CutHist k) (hR : R ≤ k * (Nat.log 2 ⌈64 / ε ^ 2⌉₊ + 2) + 1) :
    IsApproxFixedPoint f ε (out R) ∧
      costedRun (round O) R init
        ≤ (k * (Nat.log 2 ⌈64 / ε ^ 2⌉₊ + 2) + 1) * (1 + pS + pB + (k + 1)) := by
  refine ⟨?_, hitrun_time_poly O init hS hB ε R hR⟩
  have hdecay : linfDist (out R) xs ≤ q ^ R * linfDist (out 0) xs :=
    dist_geom_decay hq0 (fun t => linfDist (out t) xs) hshrink R
  have h1lam : (0 : ℝ) ≤ 1 + lam := by have := hf.lam_nonneg; linarith
  have hnear : (1 + lam) * linfDist (out R) xs ≤ ε :=
    (mul_le_mul_of_nonneg_left hdecay h1lam).trans hclose
  exact isApproxFixedPoint_of_near hf (hout R) hxs hfix hnear

end Tfnp.Contraction
