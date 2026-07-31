# tfnp

Lean 4 formalization of query-complexity results for total-function NP problems.

## Status

Contains a complete formalization of the main theorem of

> Xi Chen, Yuhao Li, Mihalis Yannakakis.
> *Computing a Fixed Point of Contraction Maps in Polynomial Queries.*
> STOC 2024 / Journal of the ACM 2025. [arXiv:2403.19911](https://arxiv.org/abs/2403.19911)

in `Tfnp/Contraction.lean` (geometry, balanced points) and
`Tfnp/Algorithm.lean` (the algorithm and its correctness), on top of a generic
query-model framework in `Tfnp/QueryModel.lean` that can be reused for any
black-box query problem.

**The main theorem `cly_query_complexity` is fully proved**, with no `sorry` and
no axioms beyond `propext`, `Classical.choice`, `Quot.sound`:

```lean
theorem cly_query_complexity :
    ∃ (A : (k : ℕ) → ℝ → CQueryAlg k (Vec k)) (C : ℝ),
      0 ≤ C ∧
      ∀ (k : ℕ) (ε : ℝ), 0 < ε → ε ≤ 1 →
        ∀ {lam : ℝ} (f : Vec k → Vec k), IsLInfContraction f lam →
          IsApproxFixedPoint f ε ((A k ε).run f) ∧
          ((A k ε).queries f : ℝ) ≤ C * ((k : ℝ) + 1) * (Real.log (1/ε) + 1)
```

`QueryAlg Q R α` is a free monad over "ask the oracle for `q : Q`, get back
`r : R`" — a decision tree — so `A` really is a black-box algorithm: its only
access to `f` is through `ask`, and `queries` counts the nodes actually visited.
The bound is independent of the contraction factor `λ`.

### Using it

The existential above is the faithful rendering of CLY's Theorem 1, but for
actual use prefer the concrete pair, which names the algorithm and gives the
bound in closed form:

```lean
noncomputable def clyAlgorithm (k : ℕ) (ε : ℝ) : CQueryAlg k (Vec k)

theorem clyAlgorithm_isApproxFixedPoint (k : ℕ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {lam : ℝ} (f : Vec k → Vec k) (hf : IsLInfContraction f lam) :
    IsApproxFixedPoint f ε ((clyAlgorithm k ε).run f)

theorem clyAlgorithm_queries_le (k : ℕ) (ε : ℝ) (f : Vec k → Vec k) :
    (clyAlgorithm k ε).queries f ≤ k * (Nat.log 2 ⌈64 / ε ^ 2⌉₊ + 2) + 1
```

The query bound holds unconditionally — no hypotheses on `ε`, `f` or `λ` — since
it is a fact about the shape of the decision tree. `clyBudget_le` turns the
closed form into the asymptotic one, with explicit constant
`C = 3 + (2 + log 65)/log 2 < 12`.

```lean
example (k : ℕ) (f : Vec k → Vec k) (hf : IsLInfContraction f (1/2)) :
    IsApproxFixedPoint f (1/10) ((clyAlgorithm k (1/10)).run f) :=
  clyAlgorithm_isApproxFixedPoint k (by norm_num) (by norm_num) f hf
```

Note `clyAlgorithm` is `noncomputable`: the balanced point is obtained by
`Classical.choose`. That is inherent to a query-complexity result — see
`notes/polytime.md` for what computing it would take.

### What is where

`Tfnp/Contraction.lean`:

* `linfDist`, `Pyramid`, `Around`, the integer `grid`;
* `fermatWeber`, `exists_balanced_point_box` — balanced points, by convex
  minimisation (see below);
* `grid`, `exists_grid_near`, `clyChooseBalanced`.

`Tfnp/Algorithm.lean`, following CLY Sections 3–4:

* `pyrUnion_disjoint_pyramid` — their Lemma 4;
* `around_subset_pyrUnion` — their Lemma 3;
* `fixedPoint_mem_pyrUnion` — their Lemma 2;
* `clyStep` — Algorithm 1, with Observation 1 (the `γ`-elimination) folded in by
  damping every oracle response by `(1 − ε/2)`;
* `clyStep_correct` — their Lemma 5: the induction carrying both invariants
  (the candidate set always contains a grid point within distance `1` of the
  fixed point, so is never empty; and it halves each round);
* `cly_query_complexity` — Theorem 1, at grid scale `⌈64/ε²⌉` and
  `k(log₂ n + 2) + 1` rounds.

### Balanced points without Brouwer

Balanced-point existence — CLY's Lemma 6 (Brouwer on an auxiliary self-map built
from signed pyramid volumes) + Lemma 7 (`t → ∞`) + Lemma 8 (parity-aware
rounding) — is replaced here by a single convexity argument:

> A *balanced point* of `T` is exactly a minimiser of the `ℓ∞` Fermat–Weber
> functional `Φ(c) = ∑_{y ∈ T} ‖y − c‖∞` (`fermatWeber`).

Existence is then compactness rather than Brouwer, and the balance property is
first-order optimality: the directional derivative of `Φ` at a minimiser in
direction `−σ` equals `#captured − #not-captured`, so it being `≥ 0` says
directly that every one of the `2^k` pyramid unions captures at least half of
`T`. The reason this works in `ℓ∞` specifically is that the subgradients of
`‖·‖∞` are the vertices `±eᵢ` of the dual (cross-polytope) ball, so "direction
from `c` to `y`" is quantised into exactly the `2k` pyramid classes.

Consequences: `Tfnp/Contraction.lean` does not depend on `Tfnp/Brouwer/` at all,
the thickening/volume machinery is gone, and the parity rounding is unnecessary
— it exists only to transfer a *volume* balance to a *counting* balance, and the
argument above gives the counting balance directly. With the rounding step gone
the candidate set needs no parity condition either, so CLY's even-integer set is
replaced by the full integer `grid`. See `notes/polytime.md`.

## PPAD

`Tfnp/PPAD.lean` defines the class abstractly: `SearchProblem`, `Reduction`
(the combinatorial data of a many-one reduction), and `ReductionClass` (an
abstract predicate on reductions, closed under identity and composition).
`PPAD` is defined relative to a `ReductionClass`, so instantiating it with
poly-time computability is orthogonal to everything proved here.

* `exists_other_end` — the parity argument, the entire mathematical content of
  `PPAD`'s totality;
* `endOfLine_isTotal`, `endOfLine_ppadComplete`;
* `InPPAD.isTotal` — `PPAD ⊆ TFNP`, *derived* from the parity argument;
* `ppadHard_iff_endOfLine_reduces` — hardness needs only one reduction.

**Guard rail.** `nonempty_reduction_of_isTotal` proves that the bare notion of
reduction is vacuous: any total problem reduces to any problem with an instance,
by a constant instance map plus choice. `trivialClass_degenerate` makes the
consequence explicit — under `Ok := fun _ => True`, every total problem is
`PPAD`-complete. So all the content of a hardness result lives in the
`ReductionClass`.

### Black-box lower bounds (`Tfnp/BlackBox.lean`)

The reusable core of every deterministic query lower bound:

* `QueryAlg.queried` — the points an algorithm actually looks at;
* `QueryAlg.run_eq_of_agree` — oracles agreeing there give the same output *and*
  the same query list;
* `QueryAlg.not_valid_of_agree` — the two-instance template.

Applied to End-of-Line: `eol_must_query_endpoint` shows a correct algorithm has
to *query* the endpoint of the path — it cannot deduce it. The witness pair is
the path `0 → 1` against `0 → 1 → a → b`, which agree off `{1, a, b}` but have
different unique solutions. `exists_unqueried` supplies the two spare vertices
whenever the algorithm leaves room.

### The circuit model (`Tfnp/Circuit.lean`, `Tfnp/CircuitEOL.lean`)

Straight-line-program Boolean circuits — DAGs, not formulas, since poly-size
formulas compute a strictly weaker class and would define the wrong complexity
class. Wire numbering is uniform (the wire list starts as the inputs and each
gate appends), which is what makes `Gate.shiftAll` plain addition and hence
makes composition provable without index case-splits:

* `evalWires_shiftAll` — relocation: a shifted gate list run after a prefix
  computes what the unshifted list computes, in place after the prefix;
* `MultiCircuit.comp` with **`eval_comp`** — composition computes the composite
  (given the first circuit's outputs are in range) — and `size_comp`, giving
  `size (comp c d) = size c + |outputs c| + size d`;
* `PolySize`, closed under sums, hence under composition.

`CircuitEOL` is then Papadimitriou's actual problem: the successor and
predecessor are given by *circuits*, so an instance is polynomially sized even
though the graph has `2^n` vertices. `circuitEndOfLine_isTotal` follows from the
same parity argument, and `circuitToTable` reduces the succinct version to the
tabular one. There is deliberately no reduction back: going from a function to a
circuit computing it is precisely what succinctness forbids.

## Acknowledgements

* `Tfnp/Brouwer/` vendors the Brouwer fixed-point formalization from
  [math-xmum/Brouwer](https://github.com/math-xmum/Brouwer)
  (Copyright (c) 2025 Math_XMUM, MIT License — see `LICENSE-Brouwer`).
  The four files (`Simplex.lean`, `Scarf.lean`, `Brouwer.lean`,
  `Brouwer_product.lean`) provide a Brouwer fixed point theorem via Scarf's
  combinatorial lemma. We exclude their `Nash.lean` (Nash equilibrium
  application, out of scope here).

  These files are ported to this project's toolchain and build, and
  `Tfnp/Brouwer/Cube.lean` derives `brouwer_cube` (Brouwer on a closed box)
  from them. Nothing in `Tfnp/Contraction.lean` uses it any more — see
  "Balanced points without Brouwer" above — so they are kept only as a
  standalone result.

## Building

```
lake update
lake build
```
