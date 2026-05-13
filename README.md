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

Brouwer's fixed-point theorem on a closed cube is currently taken as an
`axiom` (`brouwer_cube`) — it is a long-standing gap in mathlib. The natural
next target is to discharge it via the vendored Brouwer formalization (below),
once the porting from upstream's mathlib pin to ours is complete.

## Acknowledgements

* `Tfnp/Brouwer/` vendors the Brouwer fixed-point formalization from
  [math-xmum/Brouwer](https://github.com/math-xmum/Brouwer)
  (Copyright (c) 2025 Math_XMUM, MIT License — see `LICENSE-Brouwer`).
  The four files (`Simplex.lean`, `Scarf.lean`, `Brouwer.lean`,
  `Brouwer_product.lean`) provide a Brouwer fixed point theorem via Scarf's
  combinatorial lemma. We exclude their `Nash.lean` (Nash equilibrium
  application, out of scope here).

  **Porting status:** the upstream targets Lean `v4.22.0` with a corresponding
  mathlib pin (`29675b2a…`); this project tracks `v4.30.0-rc2` with mathlib
  `6cf3ab1c…`. `Simplex.lean` ports cleanly with two patches
  (`mul_le_mul_left.mpr` → `mul_le_mul_of_nonneg_left`); the remaining three
  files need similar mechanical fixes (`Finset.card_sdiff` →
  `Finset.card_sdiff_of_subset`, etc.) before they build. Until then they are
  vendored but not imported by `Tfnp.lean`; `brouwer_cube` remains an axiom.

## Building

```
lake update
lake build
```
