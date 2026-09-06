# `Tfnp/Tarski/` — query complexity of Tarski fixed points

A formalization of the Fearnley–Pálvölgyi–Savani line of work on the query
complexity of finding a Tarski fixed point, and of the framework of the recent
Chen–Li–Yannakakis paper.

References, in dependency order:

* C. Dang, Q. Qi, Y. Ye. *Computations and complexities of Tarski's fixed points
  and supermodular games.* (2011/2020) — the `O(logᵏ n)` recursive binary search,
  formalized separately in `Tfnp/Tarski.lean`.
* K. Etessami, C. Papadimitriou, A. Rubinstein, M. Yannakakis. *Tarski's theorem,
  supermodular games, and the complexity of equilibria.* [arXiv:1909.03210] — the
  `Ω(log² n)` lower bound for `k = 2`.
* J. Fearnley, D. Pálvölgyi, R. Savani. *A faster algorithm for finding Tarski
  fixed points.* [arXiv:2010.02618] — **the main subject of this directory**.
* X. Chen, Y. Li. *Improved upper bounds for finding Tarski fixed points.* (CL22)
  — `Tarski*`, and the decomposition theorem for it.
* X. Chen, Y. Li, M. Yannakakis. *The Mystery Deepens: On the Query Complexity of
  Tarski Fixed Points.* [arXiv:2604.00268] (CLY26) — `Tarski*(n,3)` in `O(log n)`,
  hence `Tarski(n,4)` in `O(log² n)`.
* S. Haslebacher, J. Lill. *A Levelset Algorithm for 3D-Tarski.*
  [arXiv:2510.14777] (HL) — a second `O(log² n)` algorithm for `d = 3`, searching
  over *levelsets* rather than slices, with a far smaller case analysis.

Everything below is **fully proved, no `sorry`**, with axiom dependencies
`propext`, `Classical.choice`, `Quot.sound` only. The exceptions are stated
explicitly in "Not proved" at the end.

## Design: the search problem, not the promise problem

`Tfnp/Tarski.lean` bundles monotonicity into `TarskiInstance`. This directory
deliberately does not: an instance is an arbitrary `f : Pt k → Pt k`, and a
*solution* is either

* `(T1)` a fixed point `f x = x`, or
* `(T2)` a witnessed violation `x ≼ y` with `f x ⋠ f y`

(`Answer`, `IsSol` in `Basic.lean`; FPS Definition 2). This is not pedantry. The
decomposition theorem runs an algorithm against a *simulated* oracle that need not
be monotone even when the real one is, so the sub-algorithms must be permitted to
report violations. Totality is `exists_sol_of_mapsTo`.

Points live in all of `ℕ^k` (`Pt k`), with attention confined to a *box*
`Box lo hi = Set.Icc lo hi`. Bounded grids are `lo = 0`, `hi = fun _ => n`.

One practical wrinkle worth knowing: `Pt k` carries the `Pi` order, whose `Nat`
instance is `(fun _ => instLENat) i`, not syntactically `instLENat`. `omega` and
`linarith` match on the instance and silently ignore hypotheses of the wrong
shape. Everything therefore goes through `le_coord` / `coord_le`
(`Basic.lean`), whose stated types pin the plain instances.

## Files

| file | contents |
| --- | --- |
| `Basic.lean` | `Pt`, `Box`, `Up`/`Down`, `Answer`/`IsSol`, `up_step` (FPS L21), **`exists_sol_of_up_down` (FPS Lemma 4)**, `intervalAlgorithm` with correctness and a `boxSize + 1` query bound |
| `Simulation.lean` | `QueryAlg.Bounded n` — worst-case query depth as an inductive predicate (the response type is infinite, so it is not a `Finset.sup`), closed under `bind` |
| `Product.lean` | `ℕ^(a+b) = ℕ^a × ℕ^b`: `cat`, `pr1`, `pr2`, `sliceFun` |
| `History.lean` | The combinatorics of the decomposition: `lowB`/`highB` (FPS's `l` and `u`), the `Good` invariant, **`lowB_le_highB` (FPS Lemma 16)**, **`up_lowB_or_vop` / `down_highB_or_vop` (FPS Lemma 17)** |
| `Decomposition.lean` | **FPS Theorem 18**: `decompAlg`, `decompAlg_isSol`, `decompAlg_bounded` |
| `Outer.lean` | FPS Definition 3 (`InnerAnswer`, `IsInnerSol`, `SolvesInner`) and **FPS Theorem 5**: `outerAlg_isSol`, `outerAlg_bounded` |
| `Inner.lean` | `exists_solOn` (FPS Lemma 4 on a coordinate subset), FPS Definitions 6/8/10 and **Lemmas 7, 9, 11, 12** |
| `Star.lean` | `Tarski*` (CL22 / CLY26 Definition 1), its totality, and **the Chen–Li reduction** `Tarski(n,k+1) → Tarski*(n,k)` |
| `PIFunction.lean` | CLY26's monotone partial-information functions, candidate sets, safe functions, and the counting argument behind their `O(k log n)` |
| `Levelset.lean` | HL's levelsets: `lev`, `exists_lev_between`, `IUp`/`IDown`, the `d = 3` trichotomy, **HL Observations 3.9 and 3.10**, and **HL Lemma 3.2** (the outer recursion) |
| `LevelsetSearch.lean` | HL's search space: `sLo`/`sHi`/`sDiam` with attainment, **Lemma 3.5** (`exists_deep_query`), the 5/6 shrink both ways and its product measure, **Lemma 3.6** (`stuck_levels`, `hasProgress_of_corner_up`), and **Lemma 3.12** (`hasProgress_or_config3`) |
| `LevelsetSegment.lean` | `upOrVop`/`downOrVop` — monotonicity-or-violation, once and for all — plus levelset segments and the binary-search combinator `segSearch` |
| `Config3.lean` | **HL Lemma 3.13**: `config3Alg`, `config3Alg_isSol`, `config3Alg_bounded` |
| `LevelsetWitness.lean` | HL Observations 3.9/3.10 and the Lemma 3.6 endgame restated so the algorithm *returns* the witness: `alg_config1Up/Down`, `alg_config2Up/Down`, `alg_corner_up/down` |
| `LevelsetInit.lean` | **HL Lemma 3.14**, both halves: `initUpAlg_isSol`, `initDownAlg_isSol` |
| `LevelsetLoop.lean` | **The loop, and the whole subprocedure**: `configResolve` (Lemma 3.12 made algorithmic), `lsLoop`, and **`solvesLevelset_lsInner`** with `lsInner_bounded` |
| `Bound.lean` | **Query upper bounds for `Tarski(n,d)`**: the dimension-1 primitive, the block recursion, and the assembled bounds |
| `BoundHL.lean` | The `d = 3` hypothesis of `Bound.lean` discharged: **`tarski_cube_bound_hl`**, `tarski_cube_bound_all` |
| `GeneralDim.lean` | **Dimension-uniform progress**: `exists_covering`, `exists_meet_progress`, **`meet_progress_of_no_crossing`**, `slack_sum_le`, and the `d = 3` subsumption check |

## The decomposition theorem (FPS Theorem 18)

```lean
theorem decompAlg_isSol (hA : SolvesMapsTo algA loA hiA) (hB : SolvesUpDown algB loB hiB)
    (hloA : loA ≤ hiA) (hloB : loB ≤ hiB) :
    SolvesMapsTo (decompAlg algA algB loA hiA loB hiB) (cat loA loB) (cat hiA hiB)

theorem decompAlg_bounded (hAq : Bounded qa algA) (hBq : ∀ l u, Bounded qb (algB l u)) :
    Bounded ((qa + 2) * (qb + 3)) (decompAlg algA algB loA hiA loB hiB)
```

Two solver interfaces, and which one goes where is what makes the theorem
*compose*:

* `SolvesMapsTo alg lo hi` — correct whenever the oracle maps the box into itself.
  The **outer** factor needs only this, and it is what the theorem **produces**.
* `SolvesUpDown algOf lo hi` — correct on every sub-box whose endpoints lie in the
  up and down sets. This is FPS Lemma 4's interface, hence the interface of the
  FPS outer algorithm, and it is what the **inner** factor needs.

`SolvesUpDown.solvesMapsTo` gives the implication, so iterating along
`k = (k-3) + 3` — inner factor always the fixed 3-dimensional algorithm — is FPS
Theorem 19. `intervalAlgorithm_solvesUpDown` is the base case in every dimension.

### Three honest divergences from the paper

FPS state `qₐ · (q_b + 2)`; the proved bound is `(qₐ + 2) · (q_b + 3)`. Same
asymptotics, and each difference is a real gap in the paper's accounting rather
than a formalization artifact:

1. **`q_b + 3`, not `q_b + 2`, per simulated query.** Two probes check
   `l ∈ Up`/`u ∈ Down` (Lemma 17), the inner algorithm costs `q_b`, and *one more
   probe* is needed to read off the response to the outer algorithm: the inner
   algorithm returns a slice fixed point `y` but is not obliged to have queried
   it, so `f(x, y)` must be asked for. FPS implicitly assume it was queried.
2. **`qₐ + 2`, not `qₐ`.** FPS translate the outer algorithm's answer using the
   `y` recorded for it — but the outer algorithm may return a point it never
   queried, for which no `y` is on record. `finalize` runs one more simulated step
   at each returned point.
3. **Outer queries are clamped into the box** (`clamp`). Nothing stops the outer
   algorithm from probing outside its own lattice, and a recorded key outside the
   box would break the invariant that returned witnesses lie inside it. Invisible
   on the box where correctness is asserted.

### The simulated oracle really is a function

The subtlety FPS pass over. `algA.run g` needs a genuine `g : Pt a → Pt a`, but
the simulation's response depends on the history. The fix: the history is appended
to and looked up with `List.find?` from the front, so `memo` is *stable* under
extension (`memo_append`). `StepOk.resp` therefore says the response equals
`outerOracle` of **any** later extension of the history, and `SimOut.resp`
propagates that through the whole run. At the end, `algA`'s correctness is invoked
for the oracle built from the *final* history — the one that also covers the points
`finalize` probed.

## The outer algorithm (FPS Theorem 5)

```lean
theorem outerAlg_isSol (hInner : SolvesInner innerOf lo hi) (hlohi : lo ≤ hi)
    (hlo : lo ∈ Up f) (hhi : hi ∈ Down f) :
    IsSol f lo hi ((outerAlg innerOf lo hi).run f)

theorem outerAlg_bounded (hq : ∀ lo hi i m, Bounded q (innerOf lo hi i m)) (lo hi : Pt k) :
    Bounded (logSize lo hi * q + (k + 1)) (outerAlg innerOf lo hi)
```

`logSize lo hi = ∑ i, Nat.clog 2 (hi i - lo i)`. On `[0, n]^k` that is
`k · ⌈log₂ n⌉`, so the bound is FPS's `O(q · k · log n + k)`.

The **ceiling** logarithm is what makes the measure work. Halving `[0,2]` gives
width `1`, and `⌈log₂ 2⌉ = 1 > 0 = ⌈log₂ 1⌉`, whereas the floor logarithm does not
drop; `Nat.clog_of_two_le` is exactly the recurrence needed. FPS's "reduce the
number of points by a factor of two" is loose — the product of widths does *not*
strictly halve (width `2 → 1` sends `3` to `2`).

`InnerAnswer` lets the inner algorithm report *which* of `Up f` / `Down f` its
point lies in, as FPS's own inner algorithm does. Without that the outer algorithm
would need an extra query per iteration just to find out.

## The inner algorithm's lemmas

`exists_solOn S f` is FPS Lemma 4 relativised to a set `S` of free coordinates:
from a point going up on `S` and one above it going down on `S`, one gets either a
point fixed on all of `S` *and unchanged off `S`*, or a violation. `S = univ` is
Lemma 4; the inner-algorithm lemmas use `|S| = 1` (Lemmas 7 and 9) and `|S| = 2`
(Lemma 11).

Coordinates are kept as parameters `i`, `j` (free) and `c` (frozen), with
`Covers i j c` saying they exhaust the dimensions — this is FPS's `k = 3`. That is
precisely their remark that the definition of a down set witness "abstracts over
dimensions 1 and 2": their top-boundary and right-boundary witnesses are the two
instantiations, and each lemma is proved once for both. Likewise FPS's four cases
of Lemma 12 are two lemmas, each instantiated at the two free dimensions.

| FPS | here |
| --- | --- |
| Definition 6 (down set witness) | `DownWitness` |
| Definition 8 (up set witness) | `UpWitness` |
| Lemma 7 | `downWitness_dichotomy` |
| Lemma 9 | `upWitness_dichotomy` |
| Definition 10 (invariant) | `InnerInv` |
| Lemma 11 | `hasInnerSol_of_innerInv` |
| Lemma 12 | `hasInnerSol_of_escape_upper`, `hasInnerSol_of_escape_lower` |

## `Tarski*` and CLY26

`StarInstance k lo hi` is a monotone `x ↦ (val x, sgn x)` into `Pt k × Bool`
(`true` = `+1`); a solution is a point where `val` goes weakly up with sign `+1`,
or weakly down with sign `-1` — *not* necessarily a fixed point, which is why
`Tarski*` can be easier. `StarInstance.exists_sol` is totality.

`starOfSlice` builds the `Tarski*(n,k)` instance from a `Tarski(n,k+1)` instance by
freezing the last coordinate at `m`, and `starOfSlice_sol_gives_halving` is the
Chen–Li reduction: a `Tarski*` solution yields a point of the middle slice at which
`g` moves weakly up or weakly down in *all* `k+1` coordinates, and then
`mapsTo_of_up` / `mapsTo_of_down` confine the search to a sub-box with the last
dimension cut at `m`. Repeating `O(log n)` times is the factor-`log n` reduction.

`PIFunction.lean` has CLY26's framework: `Sign`, `PIVal` (their
`{-1, 0, 1, ≤, ≥, ⋄}`), `PIFun`, `PIFun.Consistent`, `IsCandidateSet`, and `SafeOn`
(CLY23's safe functions — a unique fixed point in every slice). Proved:
`isCandidateSet_univ` (the whole box is always a candidate set — their Objective 1
met trivially and uselessly), `nonempty_of_isCandidateSet` (the invariant that
makes the shrinking argument end in a solution rather than a contradiction), and
`queries_le_of_halving` (their §2 remark that Objectives 1 + 2 give `O(k log n)`).

## The Haslebacher–Lill levelset algorithm

Where FPS binary-search over two-dimensional *slices* `{x | x₁ = k}`, HL search
over *levelsets* `{x | x₁ + x₂ + x₃ = k}`. Levelsets treat all three dimensions
symmetrically — which is what collapses FPS's intricate inner algorithm — at the
cost that no two points of a levelset are comparable.

Everything here is in the **total** setting. HL present the algorithm under the
promise that `F` is monotone, remarking (§2) that it adapts because "our algorithm
only exploits monotonicity locally: if a certain step of the algorithm should fail,
then a violation of monotonicity must be present among a constant set of previous
queries". We take them up on it: every conclusion is "… or an explicit violation",
and every appeal to monotonicity becomes a `by_cases` that in the bad case produces
the violation. That costs one case split per monotonicity use and buys the
decisive property that the `d = 3` algorithm is a `SolvesUpDown` family, so it
plugs straight into the already-proved FPS decomposition theorem.

| HL | here | status |
| --- | --- | --- |
| Definition 3.1 (levelset) | `lev`, `exists_mem_levelset` | proved |
| Lemma 3.2 (outer recursion) | `levelsetOuter_isSol`, `levelsetOuter_bounded` | **proved** |
| Definition 3.3 (`i`-up/`i`-down) | `IUp`, `IDown` | — |
| observation after Def 3.3 | `up_or_down_or_iUpDown` | **proved** |
| Definition 3.4 (search space) | `SSet`, `LBounds`, `sLo`/`sHi`/`sDiam` | proved (extents attained) |
| **Lemma 3.5** (shrinking I) | `exists_deep_query`, `sDiam_shrink`, `sMeasure_shrink` | **proved** |
| **Lemma 3.6** (shrinking II) | `stuck_levels`, `hasProgress_of_corner_up` | **proved** |
| Definitions 3.7, 3.8 | `Config1Up/Down`, `Config2Up/Down` | — |
| Observation 3.9 | `hasProgress_of_config1Up/Down` | **proved** |
| Observation 3.10 | `hasProgress_of_config2Up/Down` | **proved** |
| Definition 3.11 | `Config3` | — |
| **Lemma 3.12** (small diam ⇒ config) | `hasProgress_or_config3` | **proved** |
| **Lemma 3.13** (config 3 ⇒ progress) | `config3Alg_isSol`, `config3Alg_bounded` | **proved** |
| **Lemma 3.14** (initialization) | `initUpAlg_isSol`, `initDownAlg_isSol` | **proved** |
| the loop (§3.4) | `lsLoop_isSol`, **`solvesLevelset_lsInner`** | **proved** |


### HL §3.1: the shrinking step

`exists_deep_query` is **Lemma 3.5**. The point is that a query must be deep in
*every* coordinate at once, since only the answer decides which coordinate gets
cut; the slack `⌈diamᵢ/6⌉` per coordinate is what keeps the level constraint
satisfiable. The two sum bounds that make it work each come from *one* attained
extent: pushing coordinate `i₀` up gives `Σⱼ sLoⱼ + diam_{i₀} ≤ k`, pushing it down
gives `k + diam_{i₀} ≤ Σⱼ sHiⱼ`, and the three slacks together consume at most the
largest diameter.

`sDiam_shrink` is the payoff. Replacing `u⁽ⁱ⁾` by the queried point raises `ℓᵢ` to
`qᵢ` and leaves the *upper* extent in coordinate `i` untouched — raising `ℓᵢ` and
`|ℓ|` by the same amount cancels in `k + ℓᵢ − |ℓ|` — so `6·diam'ᵢ ≤ 5·diamᵢ`, and
`sDiam_update_other` shows the other extents only move inwards.

This is where **`Tfnp/Shrinking.lean`** comes in. With the product measure

`sMeasure = Πᵢ (diamᵢ + 1)`,

`sMeasure_shrink` proves `9·sMeasure' ≤ 8·sMeasure`: a cut coordinate with
`6d' ≤ 5d` and `d ≥ 2` satisfies `9(d'+1) ≤ 8(d+1)`, and the other two factors do
not grow. That is exactly the hypothesis of `Tfnp.iterate_shrinking` at `p = 9`, so
`sMeasure_iterate` gives `9^N · μ_N ≤ 8^N · μ_0` and hence a logarithmic bound on
the number of cuts. (The `8/9` rather than `5/6` is the price of the product: the
worst ratio `(d'+1)/(d+1)` over `d ≥ 2` is `8/9`, attained at `d = 2`.)

### HL §3.2: the constant-size endgame

`stuck_levels` is the deduction in **Lemma 3.6**: if no point of the search space is
strictly inside every extent, then `k = Σⱼ sLoⱼ + 2` or `k + 2 = Σⱼ sHiⱼ`. One
direction is the failure itself; the converse is `sum_sLo_add_sDiam_le` at any
coordinate, whose diameter is at least two.

`hasProgress_of_corner_up` is the endgame. In the first case the three *corner*
points `cornerPt i` — at the lower extent in coordinate `i`, one above it in the
other two — lie on the levelset (`lev_cornerPt`), and if each is `i`-upward then
their join is an upward point at level `k + 1`: `cornerPt j ≤ join`, and
`cornerPt j` being `j`-upward pushes `F` past `join j` in coordinate `j`.


### HL §3.3: the third configuration (Lemma 3.13)

The only configuration that does not hand over a point. `config3Alg_isSol` proves
it, and `config3Alg_bounded` gives `⌈log₂ (x j − y j)⌉ + 5` queries.

Two reusable pieces make this affordable in the total setting. First, **every**
step of HL §3 that concludes "…so this point is upward" argues by monotonicity from
already-queried points; `upOrVop` and `downOrVop` package that once: given
witnesses `wit l` known to force `z l ≤ F (wit l) l`, one further query at `z`
either confirms `z ∈ Up F` or names the violation `(wit l, z)` at the failing
coordinate `l`. Every monotonicity appeal in the file goes through those two
lemmas. Second, `segSearch` is the binary search along a segment of the levelset,
parametrised by a classification function that may return a whole sub-algorithm —
which is exactly what lets a terminal branch spend the extra query `upOrVop` needs.

The case analysis: `x ≠ y` (a point cannot be both `i`-upward and `i`-downward)
forces `y j < x j` for some other coordinate, and then `x p ≤ y p`. If `F x j = x j`
the join is upward; if `F x j ≤ y j` the meet is downward (this also swallows the
degenerate `x j = y j + 1`, where the search interval would be empty); if
`F y j = y j` the meet is downward again. Otherwise the segment freezes coordinate
`i` at `y i` and runs `j` over `[y j, x j − 1]`, whose bottom point *is* `y`. Each
segment point falls into one of four sign patterns: two give progress, two are HL's
types (1) and (2). Adjacent endpoints of opposite type give the meet or the join
according to the sign at `p`.

One gap in the paper worth recording: HL initialise the upper endpoint at
`x j − 1` and remark parenthetically that if it is "not of type (1)" then progress
follows "by our previous observation". That observation covers the two progress
patterns but *not* type (2), which the earlier argument leaves open. It is
nonetheless fine, and for a reason specific to the top index: at `t = x j − 1` the
meet `x ⊓ seg t` is downward with coordinate `j` witnessed by `x` itself, since
`F x j ≤ x j − 1 = t` is exactly what the case assumption gives.
`c3_glb_top_isSol` is that step, and the algorithm dispatches on the sign at `i`
alone, which covers type (2) and the third progress pattern together.

### HL §3.4: initialization (Lemma 3.14) and the loop

**Lemma 3.14** (`LevelsetInit.lean`) starts the six bounding points. For the
`i`-downward point it freezes coordinate `i` at its *largest attainable* value
`M = sHi lo hi k i` and binary-searches along the resulting segment; dually for the
`i`-upward point at `m = sLo lo hi k i`. The paper's argument becomes three
statements:

* `initDownStep_isSol` / `initDownStep_dir` — the seven-way classification of a
  segment point: `F` leaving the box is a violation against an endpoint
  (`vop_hi_isSol`, `vop_lo_isSol` — the ambient hypotheses are only
  `lo ∈ Up F` and `hi ∈ Down F`, *not* that `F` maps the box into itself, which the
  outer recursion would not preserve); then upward, then downward, then the four
  sign patterns in the two free coordinates, the last of which is impossible
  because coordinate `i` is already maximal.
* `initPhi_T0_false` / `initPlo_T1_false` — at the bottom of the segment the
  classification cannot come out "type hi", and dually at the top. With
  `initPlo_initPhi_ne` (the two invariants are incompatible at a single index) this
  gives `T0 < T1`, which `segSearch` needs.
* `initDownFinal_isSol` — adjacent endpoints of opposite type give a downward meet.

**The loop** (`LevelsetLoop.lean`) threads the state `u, dn : Fin 3 → Pt 3` under
the invariant `LInv`: Definition 3.4 plus `lev ℓ ≤ k ≤ lev r` for the two corners
`ℓᵢ = u⁽ⁱ⁾ᵢ`, `rᵢ = d⁽ⁱ⁾ᵢ`. Each round:

1. if some `diam(S)ᵢ ≤ 1`, hand over to `configResolve`;
2. else, if a deep query point exists, query it;
3. else every diameter is between two and five (contrapositive of Lemma 3.5), so
   `stuck_levels` pins the level and the three corner points of Lemma 3.6 are
   queried in turn.

In cases 2 and 3 the observed value is fed to `dispatch`, which by
`up_or_down_or_iUpDown` either answers outright (`q ∈ Up F` or `q ∈ Down F`, at
level exactly `k`) or finds an `l` with `IUp F q l` / `IDown F q l` and cuts:
`LInv.cut_up` / `LInv.cut_down` re-establish the invariant, and `measure_shrink_up`
/ `measure_shrink_down` give `9·μ' ≤ 8·μ`.

Two things make the three cut sites share one measure argument. First, the corner
queries are *also* deep cuts: when all diameters are in `[2,5]` the slack
`⌈diamᵢ/6⌉` is exactly `1`, so "strictly inside every extent" and "deep" coincide,
and a corner is one step inside in every coordinate but its own — and its own
coordinate is precisely the case in which the corner *passes* the test and no cut is
attempted (`cornerPt_deep_up`, `cornerPtD_deep_down`). Second, `sMeasure_shrink'`
generalizes `sMeasure_shrink` to let *either* endpoint move, since only the three
diameters enter.

Termination is fuel: `lsLoop` recurses on a counter and the correctness proof
carries `8ⁿ · μ ≤ 26 · 9ⁿ`. At `n = 0` that reads `μ ≤ 26`, and `μ ≥ 27` whenever
all three diameters are at least two — so some diameter is at most one and
`configResolve` applies. `fuel_step` is the induction step. The initial fuel is
`18·budget`, which suffices because six rounds at least halve the measure
(`2·8⁶ ≤ 9⁶`, `fuel_init`), so `3·budget` halvings cover `μ₀ ≤ 2^(3·budget)`.

`configResolve` is Lemma 3.12 turned into code: five decidable patterns on the six
points, tested in order (third configuration, then first/second among the upward
points, then first/second among the downward points), each dispatching to the
matching `alg_config*` from `LevelsetWitness.lean` or to `config3Alg`. A sixth
branch is unreachable, and `configResolve_isSol` closes it with `sDiam_cases` and
`fin3_config_exists`.

The result:

```lean
theorem solvesLevelset_lsInner (hbud : ∀ j, HI j - LO j + 1 ≤ 2 ^ budget) :
    SolvesLevelset (lsInner budget) LO HI

theorem lsInner_bounded (budget : ℕ) (lo hi : Pt 3) (k : ℕ) :
    Bounded (61 * budget + 29) (lsInner budget lo hi k)
```

With `budget = ⌈log₂(n+1)⌉` on the cube `[0,n]³` this is `O(log n)` queries for the
levelset problem, hence `O(log² n)` for `Tarski(n,3)` through HL Lemma 3.2. The
constant `61` is not optimized: six initialization searches at `budget + 4` each,
plus `18·budget` loop rounds at three queries each, plus `budget + 5` to resolve.

### Two remarks the formalization turned up

**HL Lemma 3.2's measure.** `boxSize lo hi = ∑ᵢ (hiᵢ - loᵢ)` is *exactly* the range
of levels the box spans (`boxSize_eq_lev_sub`), so a binary search on the level is
literally a halving of `boxSize`. Cutting at `k = lev lo + ⌈span/2⌉` makes both
outcomes leave a box of `boxSize ≤ ⌈span/2⌉`, and `Nat.clog 2` (the *ceiling*
logarithm) then strictly decreases — `Nat.clog_of_two_le` is the recurrence. HL's
"the subgrid has size at most half of G" needs this ceiling: the floor logarithm
does not drop when a width goes from 2 to 1. The argument is also entirely
dimension-independent, which is what makes it reusable for `d = 1` below.

**HL Lemma 3.12 needs no invariant beyond Definition 3.4.** Their proof argues from
`|Tu| ≤ 3`, where `Tu = {x ∈ L_k | u⁽ⁱ⁾ᵢ ≤ xᵢ ∀ i}`, to conclude that the three
points `u⁽¹⁾, u⁽²⁾, u⁽³⁾` are close together. Read literally that step wants
`u⁽ⁱ⁾ ∈ Tu`, i.e. `u⁽ⁱ⁾ⱼ ≥ u⁽ʲ⁾ⱼ` — which is *not* in Definition 3.4, and is *not*
preserved by the shrinking step (when a query `q` replaces `u⁽ⁱ⁾`, the other
`u⁽ᵐ⁾` need not satisfy `u⁽ᵐ⁾ᵢ ≥ qᵢ`). But the condition turns out to be
unnecessary, so Definition 3.4 is sufficient exactly as stated.

Write `ℓᵢ = u⁽ⁱ⁾ᵢ`, `rᵢ = d⁽ⁱ⁾ᵢ`. Two steps:

* `sDiam_cases`: `diam(S)ᵢ = min(rᵢ, k + ℓᵢ − |ℓ|) − max(ℓᵢ, k + rᵢ − |r|)`, and the
  four ways the `min` and `max` can be attained give — when `rᵢ − ℓᵢ ≥ 2` for every
  `i`, i.e. no third configuration — that `k ≤ |ℓ| + 1` or `|r| ≤ k + 1`. (The
  fourth case is excluded because there the diameter is the sum of the *other two*
  widths, each at least two.) This is what "`Tu` or `Td` has at most 3 points"
  amounts to.
* `fin3_config_exists`: in the first case, the *level* constraint `|u⁽ⁱ⁾| = k` with
  `k ≤ |ℓ| + 1` forces at most one coordinate of `u⁽ⁱ⁾` to exceed `ℓ` — two would
  overshoot the level by two. Writing `P i j` for "`u⁽ⁱ⁾ⱼ > ℓⱼ`", a first
  configuration between `i` and `j` is exactly `¬P j i ∧ ¬P i j`, and a second on
  `(i,j,p)` is exactly `¬P j i ∧ ¬P p j ∧ ¬P i p`. Three pairs each need a positive
  entry and each of the three rows supplies at most one, so the positives form a
  fixed-point-free map hitting each pair once — a 3-cycle — and either 3-cycle is a
  second configuration.

The point is that **no sign condition on `u⁽ⁱ⁾ⱼ − ℓⱼ` is used**: the row-sum bound
alone does the work, with the deviations free to be negative. A brute-force sweep
over all such deviation matrices confirms it — every one contains a first or second
configuration. So `Tu`-membership was a red herring, and the lemma is proved here
under Definition 3.4 alone.

## Query upper bounds for `Tarski(n, d)`

`Bound.lean` assembles a bound for **every** dimension by cutting the cube
`[0,n]^d` into blocks with the FPS decomposition theorem.

**Dimension 1 comes for free from HL Lemma 3.2.** A one-dimensional levelset is a
*single point*, so the subprocedure is one query — is that point upward or
downward? — and HL's recursion degenerates to plain binary search:

```lean
theorem solvesLevelset_dim1 (LO HI : Pt 1) : SolvesLevelset dim1Levelset LO HI
theorem dim1Solver_solvesUpDown (n : ℕ) : SolvesUpDown (dim1Solver n) (cubeLo 1) (cubeHi 1 n)
theorem dim1Solver_bounded (n : ℕ) (l u : Pt 1) :
    Bounded (Nat.clog 2 (1 * n) * 1 + 2) (dim1Solver n l u)
```

**The block recursion.** `exists_cube_solver` iterates the decomposition: from a
solver for dimension `b` and a `SolvesUpDown` family for blocks of size `c`, it
builds a solver for dimension `dimOf b c m = b + c·m`, with budget
`iterBudget qbase (q_c + 3) m`, and `iterBudget_le` puts that in closed form
`(qbase + 2)·(q_c + 4)^m`.

(`dimOf` exists because `b + c·(m+1)` is *not* definitionally `(b + c·m) + c` for
variable `c` — `Nat.add` recurses on its second argument, so `x + (y + c)` is
stuck. `dimOf`'s successor equation holds by `rfl`, so the induction needs no
transport between `Pt`-types; `dimOf_eq` recovers `dimOf b c m = b + c·m`, and for
concrete dimensions it simply computes: `dimOf 1 3 2 = 7` by `rfl`.)

Two instantiations:

```lean
-- unconditional: `d` blocks of size 1 — the Dang–Qi–Ye `O(log^d n)` bound
theorem tarski_cube_bound_dim1 (n : ℕ) : ∀ d : ℕ,
    ∃ alg : QueryAlg (Pt (dimOf 0 1 d)) (Pt (dimOf 0 1 d)) (Answer (dimOf 0 1 d)),
      SolvesMapsTo alg (cubeLo (dimOf 0 1 d)) (cubeHi (dimOf 0 1 d) n)
        ∧ Bounded (iterBudget 0 (Nat.clog 2 (1 * n) * 1 + 2 + 3) d) alg

-- HL's levelset subprocedure for `d = 3`: blocks of size 3, `O(log^(2⌈d/3⌉) n)`
theorem tarski_cube_bound_dim3 (n : ℕ)
    (hls3 : SolvesLevelset ls3 (cubeLo 3) (cubeHi 3 n))
    (hq3 : ∀ lo hi k, Bounded q3 (ls3 lo hi k))
    (b : ℕ) (hBase : SolvesMapsTo algBase (cubeLo b) (cubeHi b n)) (hBaseq : Bounded qbase algBase) :
    ∀ m : ℕ, ∃ alg, SolvesMapsTo alg (cubeLo (dimOf b 3 m)) (cubeHi (dimOf b 3 m) n)
        ∧ Bounded (iterBudget qbase (Nat.clog 2 (3 * n) * q3 + 2 + 3) m) alg
```

The first is a complete `O(log^d n)` query upper bound for `Tarski(n,d)` with an
explicit constant. The second is the same recursion with blocks of three, taking
the levelset subprocedure as a hypothesis; `BoundHL.lean` discharges it with
`solvesLevelset_lsInner`:

```lean
theorem tarski_cube_bound_hl (n b : ℕ)
    (hBase : SolvesMapsTo algBase (cubeLo b) (cubeHi b n)) (hBaseq : Bounded qbase algBase) :
    ∀ m : ℕ, ∃ alg, SolvesMapsTo alg (cubeLo (dimOf b 3 m)) (cubeHi (dimOf b 3 m) n)
        ∧ Bounded (iterBudget qbase
            (Nat.clog 2 (3 * n) * (61 * hlBudget n + 29) + 2 + 3) m) alg
```

with `hlBudget n = ⌈log₂(n+1)⌉`, so the step budget is `O(log² n)` and the whole
bound is `O(log^(2⌈d/3⌉) n)` — matching HL and FPS, and **unconditional**.
`exists_base_solver` supplies the three base cases `b ∈ {0, 1, 2}`, and
`tarski_cube_bound_all` packages them so that `d = b + 3m` covers every dimension.

## Towards `Tarski(n,d) ∈ O_d(log² n)`

`levelsetOuter` is dimension-independent, so it already reduces the whole
fixed-parameter question to the levelset subprocedure:

> **`LEVELSET(d)`** — on a box with `lo ∈ Up F`, `hi ∈ Down F` and a level `κ`, find
> an `Up` point at level `≥ κ`, a `Down` point at level `≤ κ`, or a violation.
>
> `LEVELSET(d) ∈ O_d(log n)` ⟹ `Tarski(n,d) ∈ O_d(log² n)`.

That implication is `solvesUpDown_levelsetSolver` + `levelsetSolver_bounded`, both
proved: a levelset cut halves `boxSize` *as a whole*, so there are only `O(log n)`
outer rounds however large `d` is.  This would match the `Ω̃(d log² n)` lower bound
of Brânzei–Phillips–Recker, and needs no decomposition theorem, no `Tarski*` and no
candidate sets.  For context, the state of the art is Chen–Li–Yannakakis's
`O(log^(⌈(d−1)/3⌉+1) n)`, via `Tarski*(n,3) ∈ O(log n)`; `LEVELSET(5) ∈ O(log n)`
alone would already improve `d = 5` from `log³` to `log²`.

`GeneralDim.lean` removes one of the two `d = 3` dependencies.

**`exists_covering`.** Write `ℓ_j = u⁽ʲ⁾_j`.  Being on the levelset (`lev u⁽ⁱ⁾ = κ`)
and being stuck (`κ ≤ lev ℓ + 1`) say exactly `Σ_j u⁽ⁱ⁾_j ≤ (Σ_j ℓ_j) + 1` for each
`i`.  Then some subfamily `T`, `|T| ≥ 2`, has in each of its coordinates `l` a member
`t ≠ l` with `u⁽ᵗ⁾_l ≤ ℓ_l` — which is precisely what makes the meet of `T` a `Down`
point.  Proof: otherwise peel from each subfamily an element strictly exceeded by all
the others; the last survivor exceeds everyone, giving a row with `d − 1 ≥ 2` strict
excesses, contradicting the row bound.

Two things.  The proof is a short induction, uniform in `d`, replacing HL's
`d = 3` fixed-point-free-map / 3-cycle analysis (`fin3_config_exists`).  And the
usable hypothesis is the row *sum* bound, **not** "at most one excess per row": at
`d ≥ 4` a row may carry two excesses offset by a deficit, so the `d = 3` phrasing
does not generalize even though the conclusion does.  `exists_meet_progress` packages
this with the meet/violation dichotomy, subsuming Observations 3.9 and 3.10 and the
upward half of Lemma 3.12 in one statement; `hasProgress_of_lbounds_up` checks that
it really does reprove the `d = 3` version from `LBounds`.

**Phase 1 generalizes too.** HL's deep query (Lemma 3.5) uses slack `⌈diamᵢ/6⌉`, and
its proof needs `Σⱼ slackⱼ ≤ max diam`, i.e. `d·⌈D/6⌉ ≤ D` — which **fails for
`d ≥ 6`**.  Slack `⌈diamⱼ/(2d)⌉` works in every dimension once the largest diameter is
at least `2d` (`slack_sum_le`), at the cost of a `1 − 1/(2d)` shrink per cut instead of
`5/6`.  That is affordable: a `1/poly(d)` shrink still gives `f(d)·log n` iterations.
More generally the budget for a fixed-parameter result is generous — `g(d)` queries
per iteration with a `1 − 1/f(d)` multiplicative shrink yields `f(d) log² n` overall,
so `g(d)` may be exponential in `d`.  Phase 1 therefore drives every diameter below
`2d` in `O(d² log n)` queries, in any dimension.

**But extra queries do not buy the endgame.**  Three separate attempts to exploit that
budget were refuted, each by validating against `d = 3` first, and all for the same
reason.  The search space `S = L_κ ∩ [ℓ,r]` is an **antichain**, so monotonicity
imposes no constraint whatsoever between its points: knowing `F` on all of `S` — or
even on the whole sublattice `[sLo, sHi]` — leaves an adversary who blocks every
derivation, already at `d = 3` where HL's algorithm demonstrably works.  The force in
HL's argument comes entirely from the *witnessed* extents `ℓᵢ = u⁽ⁱ⁾ᵢ`, `rᵢ = d⁽ⁱ⁾ᵢ`,
i.e. from the invariant, not from query volume.  Adding queries helps only insofar as
they become witnesses.

**What is left, and why the levelset route is barred at `d ≥ 4`.**

The endgame consumes `exists_meet_progress`, whose hypothesis is
`∀ t l, l ≠ t → F (u t) l ≤ u t l`: the witness `u⁽ᵗ⁾` must be weakly down at every
coordinate *other* than `t`, i.e. its **strict-up set must be contained in `{t}`**.
(Nothing is required at `t` itself — HL's `u⁽ᵗ⁾` is `t`-*upward*.)  Dually a high
witness needs its strict-down set inside `{t}`.  So a queried point whose strict-up
set `A` and strict-down set `B` both have size `≥ 2` is a valid witness for **no**
coordinate: it cannot enter the invariant at all.

At `d = 3` that cannot happen — `|A| + |B| ≤ 3` forces one of them to be a singleton,
which is exactly `up_or_down_or_iUpDown`.  At `d ≥ 4` an adversary may answer every
query with a balanced sign pattern (`|A| = |B| = 2` when `d = 4`), and then *no* query
ever contributes a witness.  Simulation of the full loop against such an adversary
(with the witness condition stated soundly) solves every `d = 3` instance in `O(log n)`
queries and stalls on every `d ≥ 4` instance with `n ≥ 16`, at every seed.

Two consequences.  The sign trichotomy is **load-bearing**, not a technicality to route
around — a claim to the contrary in an earlier draft of this file was wrong.  And the
obstruction is *informational, not budgetary*: it is unaffected by allowing `g(d)`
queries per iteration, because the adversary can withhold usable witnesses however many
queries are made.  This is a barrier against the *mechanism* — progress by meets and
joins of singleton-sign witnesses — rather than against `LEVELSET(d)` itself.

Capping the reported corners to keep every width `≥ 2` (which prevents a coordinate
from being pinned, and is sound, since it only lowers `lev ℓ` and raises `lev r` and
`sDiam_cases`' conclusions transfer to the witnessed corners) does *not* rescue this:
it removes the third configuration but stalls instead, occasionally even at `d = 3`,
where HL's Lemma 3.13 is what covers those states.

**The invariant can be weakened, twice, and the barrier still holds.**  The singleton
condition is *sufficient* dressed up as necessary.  What the meet actually needs is only
that whoever attains the minimum at each coordinate is weakly down there — and there is
a duality supplying that for free: a point failing to pin `l` from below is strictly up
at `l`, hence pins `l` from *above*.  So with `ℓ_l`/`r_l` the best low/high pins, any
family member at or below `ℓ_l` cannot be weakly up at `l` once `ℓ_l < r_l`.  That gives
`meet_progress_of_no_crossing`: no sign condition, no level bound, and — since
`lev z ≤ minₜ lev p⁽ᵗ⁾` — the family need not lie on the levelset at all, only **one**
member needs level `≤ κ`.  Balanced-sign points are therefore usable, and HL's co-level
requirement is far stronger than necessary.

Neither weakening breaks `d ≥ 4`: the adversary switches from withholding usable
witnesses to **forcing a crossing in every coordinate at once**, which is HL's third
configuration replicated `d` times.  The obstruction is stable, and now stated as one
condition rather than a sign pattern.

Nor does any *oblivious* query geometry help.  Crossing-freeness is automatic for a
**star** `{h − c·eₜ}` (each member the strict minimiser at its own coordinate), whose
meet lands on the levelset when `lev h = κ + cd`; HL's Lemma 3.6 corner star is the case
`c = 1`.  Sweeping anchors and dips beats a *randomly* balanced adversary at cost `~2^d`,
but is defeated outright — 0 of 8 seeds, every `n`, **including `d = 3`** — by three
explicit monotone instances: a fixed strict-up set, the "anti-star" map, and the
averaging map `F(x) = (⌊avg x⌋, …)`.  Each of those is individually trivial to solve, so
oblivious geometries have blind spots rather than the problem being hard.

The reason is worth recording.  Monotonicity lets one *lower* the non-`t` coordinates of
a strictly-down-at-`t` witness for free — `q ≤ w`, `q_t = w_t` gives
`F(q)_t ≤ F(w)_t < w_t = q_t` — so certificates are preserved downward.  But
crossing-freeness wants the other coordinates *high*.  The one direction the structure
hands you is the wrong one, which is why the pins have to be moved *adaptively* by the
observed signs, as HL do at `d = 3`.

So a fixed-parameter result needs a progress mechanism that extracts value from
balanced-sign points.  Chen–Li–Yannakakis's candidate sets are exactly that — they
track a *region* guaranteed to contain a solution rather than a family of witnesses,
and so are not restricted to singleton signs.  That is presumably why the candidate-set
method reaches `Tarski*(n,3)`, which is strictly harder than `LEVELSET(3)`:
`LEVELSET(d)` is precisely `Tarski*(n,d)` with the extra bit specialized to the linear
functional `lev x ≥ κ`.

## Not proved

Two things are stated as `Prop`-valued definitions rather than as `theorem`s
closed by `sorry`, so that nothing here claims a proof it does not have:

* `Tarski3StarInLogQueries` (`Star.lean`) — CLY26's Theorem 1, `Tarski*(n,3)` in
  `O(log n)`. Their algorithm is built on safe PI functions and the `k = 3`
  trimming of candidate sets.
* `StarDecompositionTheorem` (`Star.lean`) — CL22's decomposition theorem for
  `Tarski*`. The FPS analogue *is* proved here; porting it needs
  `SolvesMapsTo`/`SolvesUpDown` re-stated for the `Tarski*` output type.

One thing is deliberately left aside, since HL's `d = 3` algorithm supersedes it
for the bound:

* **FPS's inner algorithm** — the Step 1 and Step 2 case analysis plus the
  width-zero and width-one special cases. All its supporting lemmas are in place
  (`Inner.lean`), and `Outer.lean` supplies the interface (`SolvesInner`) and
  consumes it. Roughly twenty cases each maintaining `InnerInv` on a halved box.
  It would give a second, independent route to the same `O(log^(2⌈d/3⌉) n)` bound
  that `BoundHL.lean` now proves via HL.

`Tfnp/Tarski.lean`'s `etessami_lowerBound` remains a `sorry`; it is untouched here.
