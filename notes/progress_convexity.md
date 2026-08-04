# The progress–convexity trade-off

*Machine-checked in `Tfnp/Progress.lean` (sorry-free; axioms `propext`,
`Classical.choice`, `Quot.sound` only). Experiments:
`notes/polytime_experiments/live_progress_pareto.py`,
`notes/polytime_experiments/anisotropic_cut.py`.*

This note answers, precisely, the question "why can't we just run a first-order
method on the balanced-point program?". The answer is not that the objective is
non-convex — `Φ_μ(c) = ∫‖y−c‖∞ dμ` **is** convex in `c`. It is that the measure
`μ = uniform(X_t)` is supported on a set whose cut geometry admits **no convex or
quasiconcave surrogate whatsoever**, and that this is forced by the very thing
that makes the algorithm work.

## 0. Setup and the one degree of freedom

`X` is the candidate body, `c` the query apex, `s` the oracle's sign vector, and
the cut is `K(c,s) = ⋃ᵢ 𝒫ᵢ(c,sᵢ)` with `𝒫ᵢ(c,σ) = {y : σ(yᵢ−cᵢ) = ‖y−c‖∞}`.
Validity (`x* ∈ K(c,s)`) holds for **every** apex `c ≠ x*`
(`fixedPoint_mem_pyrUnion_apex`), so the apex is a free parameter. Two
definitions:

* coordinate `i` is **live** at `c` if some `y ∈ X` has its `ℓ∞`-argmax at `i`;
  write `L(c)` for the number of live coordinates;
* `i` is **two-sided** if that happens for *both* signs.

Guaranteed progress and convexity are both functions of the same object, `L(c)`,
and they pull in opposite directions.

## 1. Exact worst-case progress (`card_removed_le_sum_min`)

Because the `2d` pyramids at `c` partition `X` up to ties, assigning each point
its argmax `(i,φ)` gives counts `nᵢ^φ`, and the oracle — which picks `s` — will
pick the **majority** sign at every coordinate. Hence

> **Theorem 1.** Worst-case removal at `c` is exactly the *minority count*
> `p(c) = Σᵢ min(nᵢ⁺, nᵢ⁻)`.

Three immediate consequences, all sharp:

* `Σᵢ (nᵢ⁺+nᵢ⁻) = N`, so `p(c) ≤ N/2`, with equality **iff** `nᵢ⁺ = nᵢ⁻` for
  every `i` — i.e. **iff `c` is balanced.** Balancedness is not merely
  *sufficient* for halving; it is the unique maximiser of guaranteed progress.
  This is a second variational characterisation of the balanced point,
  complementing "minimiser of the Fermat–Weber functional".
* A coordinate that is not two-sided contributes exactly `0`. So
  **`p(c) > 0` requires a two-sided coordinate** (`exists_sign_vacuous_cut`: if
  none is two-sided, some sign vector makes the cut *vacuous*, `X ⊆ K(c,s)`).
* Progress is *not* a smooth function of the apex — it is a sum of minorities,
  and a coordinate switches from "contributes nothing" to "contributes" only
  when it becomes two-sided.

## 2. Progressive apexes are interior (`apex_between_of_two_sided`)

> **Theorem 2.** If `y` has argmax `(i,+)` and `z` has argmax `(i,−)` then
> `zᵢ ≤ cᵢ ≤ yᵢ` and, for **every** coordinate `m`,
> `|yₘ−cₘ| ≤ yᵢ−cᵢ` and `|zₘ−cₘ| ≤ cᵢ−zᵢ`.

So a two-sided coordinate traps the apex inside the coordinate-`i` reach of `X`
in *all* coordinates at once. A "far" apex — far enough that the body subtends a
small `ℓ∞` angle, which is exactly what would make the cut convex — provably has
`p(c) = 0`. This kills the natural idea "query far away, get a halfspace".

## 3. The sharp threshold at 2 vs 3 live coordinates

**Two live coordinates ⟹ convex** (`cut_inter_subset_halfspace`). If every
`y ∈ X` has its argmax in `{i,j}`, then on `X`

```
K(c,s) ∩ X ⊆ { y : σᵢ(yᵢ−cᵢ) + σⱼ(yⱼ−cⱼ) ≥ 0 }
```

— a genuine linear halfspace through `c`. The candidate body stays a convex
polytope and the round is poly-time by classical cutting planes. This strictly
generalises the `d ≤ 2` base case: what matters is not the ambient dimension but
how many coordinates the body can put at its `ℓ∞`-argmax.

**Three live coordinates ⟹ nothing convex survives.** The sharp form is a
one-line construction (`exists_three_pyramid_centroid`):

> **Theorem 3 (centroid lemma).** For *any* three distinct coordinates `i,j,l`,
> *any* signs, *any* apex `c` and *any* target `y ∈ ℝ^d`, `y` is the centroid of
> three points, one in each of `𝒫ᵢ(c,a)`, `𝒫ⱼ(c,b)`, `𝒫ₗ(c,e)`.
>
> *Proof.* Push `y` out by `R = 2‖y−c‖∞+1`: the point for coordinate `m` gets
> `+2Rσₘ` at `m` and `−Rσ` at the other two. The three pushes cancel, and
> `R ≥ 2‖y−c‖∞` makes the pushed coordinate dominate. ∎

Consequences, in increasing strength:

1. `eq_univ_of_convex_of_three`: any convex set containing three pyramids at a
   common apex is `ℝ^d`. (This re-proves the folklore `conv K = ℝ^d` for
   `|S| ≥ 3` with an explicit 3-point combination, replacing the ad-hoc
   sign-arithmetic in `polytime.md` §3.2.)
2. `le_of_quasiconcave_majorant`: **no quasiconcave surrogate.** If `h` is
   quasiconcave — in particular log-concave, hence any Gaussian/entropic/softmax
   smoothing, any convex-relaxation indicator, any barrier of a convex body —
   and `h ≥ 1` on `K`, then `h ≥ 1` *everywhere*. So `∫_box h ≥ vol(box)`: such a
   potential can never decrease, whatever the cut. **There is no convex surrogate
   on which to run a first-order method.** This is the precise statement of the
   obstruction, and it upgrades the set-level barrier (`conv K = ℝ^d`) to a
   function-level one, which is what a first-order method actually needs.
3. `exists_injective_of_convex_cover`: **the convex cover number of a single cut
   is exactly `d`.** The `d` witnesses `pᵐ` (signed offset `+1` at `m`, `−1`
   elsewhere) lie in `K`, but the midpoint of any two has all signed offsets
   `≤ 0` and some offset `−1`, so it leaves `K`. Hence no convex piece contains
   two witnesses, and `d` pieces are needed; the `d` pyramids give `d`. So a cut
   is not merely non-convex — it costs exactly `d` convex pieces, and the right
   complexity measure is the **convex cover number**, not any convexity constant.

## 4. Is the trade-off a curve or a cliff? (experiment)

The theory leaves one hope: buy convexity by giving up *some* progress. Formally,
is there an apex with `L(c) ≤ 2` and `p(c) ≥ 1/poly`? Such an apex exists in
principle — e.g. if the body is `ℓ∞`-**anisotropic** (one bounding-box side
dominating the rest), place `cⱼ` just outside the narrowest coordinate's range
and `cᵢ` at the median of the widest; every argmax is then forced into `{i,j}`
and all four sign patterns still cut off a constant fraction.

Two measurements, on realizable SSG trajectories (exact rejection sampling,
`d = 3..6`, `t ≤ 2d`, 3000 samples/round):

* **`anisotropic_cut.py` — the regime is never entered.** The bounding box of
  `X_t` stays essentially cubical at *every* round: `w₁/w₂ ∈ [1.00, 1.20]`
  throughout. `X_t` has volume `2^{−t}` but still reaches near every box face,
  because the cut cones are unbounded. So the anisotropic construction is never
  even feasible inside the unit box.
* **`live_progress_pareto.py` — the trade-off is a cliff.** Searching ~3000
  apexes per round (balanced apex, axis-pulled apexes, random apexes *allowed to
  leave the box*, which only over-states what is achievable):

  | d | best `p` at `L≤2` | best `p` at `L=3` | `p` at balanced apex (`L=d`) |
  |---|---|---|---|
  | 3 | 0.000–0.011 | 0.44–0.46 | 0.44–0.46 |
  | 4 | 0.000–0.005 | 0.000–0.048 | 0.41–0.48 |
  | 5 | 0.000–0.002 | 0.000–0.006 | 0.40–0.47 |
  | 6 | 0.000–0.001 | 0.000–0.011 | 0.37–0.47 |

  The minimum liveness attaining `p ≥ 0.05` is `d` in essentially every round.

So on realizable bodies the two regimes do not overlap even approximately:
**`L ≤ 2` gives progress `≈ 0`; progress `≈ 1/2` forces `L = d`.** Every
coordinate is live at the balanced apex — which is the *theorem* behind the
earlier empirical finding (`m1_orderinterval.md`) that "the active set is `Θ(d)`,
max `= d`", and it closes Corollary C (`polytime.md` §3.2) at balanced apexes: no
amount of extra querying can narrow the support to two, because narrowing it to
two is exactly what destroys the progress guarantee.

## 5. What this does and does not settle

**Settles.** The entire family "relax the cut to something convex and run a
first-order / cutting-plane / barrier method" is closed, at the level of
functions and not just sets. Any surrogate must have non-convex superlevel sets,
and the minimal honest surrogate class is *max of `k` log-concave functions* —
i.e. the convex cover. This is why every route in `FINAL_REPORT.md` reconverged
on a piece-count: the piece count is the only remaining parameter.

**Does not settle.** It says nothing about whether the cover number of the
*intersection* `X_t = ⋂_r K(c^r,s^r)` stays polynomial. A single cut costs
exactly `d` pieces; `t` cuts cost at most `d^t` and at least `d`; conjecture (★)
of `FINAL_REPORT.md` is the claim that the *volume-carrying* pieces are
`poly(d,t)`-many. Theorem 3 gives the base case of a possible induction (`t = 1`
costs exactly `d`, not more), and Theorem 1 gives an exact accounting of what
each round buys. Neither implies the other.

**One new, sharper open question.** The anisotropic construction of §4 is a
genuine convex-cut mechanism that fails only because realizable `X_t` is
`ℓ∞`-isotropic. The isoperimetry route (`isoperimetry_summary.md`) fails only
because realizable `X_t` can be *anisotropic* in the covariance sense (persistent
blind long axis, `κ: 3→15.6`). These are different notions of anisotropy —
bounding-box vs covariance — so the two failure modes are **not** obviously
complementary, but they are close enough that the question is worth asking:

> Is there a pair of apex rules such that, for every realizable `X_t`, at least
> one of them gives (convex cut with `1/poly` progress) or (`1/poly` Cheeger
> constant)?

A positive answer is a poly-time algorithm. The measurement above says the
bounding-box version of the dichotomy fails outright (`w₁/w₂ ≤ 1.2` always), so
any such pair must use a non-axis-aligned notion — and the `ℓ∞` geometry is
rigidly tied to the axes. Rescaling is not a way out: a general `ℓ∞`-contraction
need not contract in a weighted sup-norm `‖a‖_w = maxⱼ|aⱼ|/wⱼ` (for the SSG
operator `fᵢ(x) = max_{j ∈ succ(i)} xⱼ` this needs `max_{j ∈ succ(i)} wⱼ ≤ λwᵢ`,
a condition on the game graph that fails as soon as it has a cycle with
non-constant `w`), so one cannot whiten the body and keep the cut lemma. That
rigidity is, as far as this note goes, the reason the two routes cannot be
glued.
