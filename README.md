# tfnp

Lean 4 formalization of query-complexity results for total-function NP problems.

## Status

Currently contains a partial formalization of

> Xi Chen, Yuhao Li, Mihalis Yannakakis.
> *Computing a Fixed Point of Contraction Maps in Polynomial Queries.*
> STOC 2024 / Journal of the ACM 2025. [arXiv:2403.19911](https://arxiv.org/abs/2403.19911)

in `Tfnp/Contraction.lean`, on top of a generic query-model framework in
`Tfnp/QueryModel.lean` that can be reused for any black-box query
problem. The main theorem `cly_query_complexity` is
structurally assembled; the proof reduces to four named CLY sub-results, each
marked as `sorry`:

1. Continuity of the auxiliary self-map (dominated convergence on a
   parameter-dependent indicator).
2. Pyramid containment under parity-aware rounding (CLY Lemma 8 + parity
   argument).
3. Discrete count from volume balance (CLY Lemma 7, `t → ∞` limit).
4. Candidate-set invariant ruling out the default branch (CLY Lemma 5).

The framework is in place: the `QueryAlg Q R α` model is a free monad over
the operation "ask the oracle for `q : Q`, get back `r : R`" with full
`Monad`/`LawfulMonad` instances, `ask` primitive, and `run`/`queries`
extractors with bind-distribution lemmas. CLY-specific content
(`Tfnp/Contraction.lean`) builds on this: all geometric primitives (pyramids,
halving, shifted-pyramid disjointness, pyramid cover), the integer grid
`EVEN(n,k)`, the rounding lemma, the recursive algorithm (using
`do`-notation), the query bound, the in-cube property, and the final
assembly are all proved.

Brouwer's fixed-point theorem on a closed cube is taken as an `axiom`
(`brouwer_cube`) — it is a long-standing gap in mathlib and is itself the
natural next target (provable via Sperner's lemma).

## Building

```
lake update
lake build
```
