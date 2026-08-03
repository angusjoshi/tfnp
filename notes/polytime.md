# Towards a polynomial-time algorithm for `ℓ∞`-contraction fixpoints

Status of the literature as of 2026-07, what the actual barrier is, and one
concrete new reduction: **the balanced point is the minimiser of a convex
function, and for a finite candidate set it is the solution of a linear
program.**

## 0. Where things stand

| result | queries | time |
|---|---|---|
| Banach / value iteration | `O(log(1/ε)/(1−λ))` | poly per query, pseudo-poly overall |
| Shellman–Sikorski `PFix` | `O(log^d(1/ε))` | `O(log^d(1/ε))` |
| Chen–Li–Yannakakis, STOC'24 | `O(d² log(1/ε))` | `Ω((1/ε)^d)` (brute force over the grid) |
| Haslebacher–Lill–Schnider–Weber '25 | `O(d²(log 1/ε + log 1/(1−λ)))`, all `ℓ_p` | not poly |
| Chen–Li–Yannakakis '26 | — | `O(log^{⌈d/2⌉}(1/ε))` |
| Feodorov–Haslebacher '26 | `O(d² log 1/ε)` | `(log 1/ε)^{O(d log d)}`, or `(log 1/ε)^{O(√d log d)}` w/ decomposition |

Polynomial time is **open**, and it is open for a reason: Shapley stochastic
games and Condon's simple stochastic games reduce to `ℓ∞`-contraction with
`λ = 1 − 2^{−poly}` and `ε = 2^{−poly}`, both of poly bit-size. So a
`poly(d, log(1/ε))`-time algorithm puts SSG in **P**. Feodorov–Haslebacher make
this concrete in the other direction: their `(log 1/ε)^{O(√d log d)}` bound is
currently the best *deterministic* SSG bound, `|G|^{O(√n log n)}`.

Note this also means **"weakly polynomial" buys nothing here**. The hard regime
is `λ = 1 − 2^{−poly(bits)}`, which is exactly what the SSG reduction produces;
poly dependence on the bit-size of the input is precisely the open problem.
Anything with `poly(1/(1−λ))` is just value iteration.

## 1. Notation

`P_i^σ(c) = { y : σ(y_i − c_i) = ‖y − c‖_∞ } = { y : σ(y_i − c_i) ≥ |y_j − c_j| ∀j }`
— a convex polyhedral cone with apex `c` and `2(d−1)` facets (`Pyramid` in
`Tfnp/Contraction.lean`). The `2d` pyramids at `c` cover `ℝ^d` and pairwise
intersect only inside `{|y_i − c_i| = |y_j − c_j|}`, a null set.

**Cut lemma** (CLY Lemma 2 = `fixed_point_in_pyramids`): with `v = f(c) − c ≠ 0`
and `s_i = sign(v_i)`, the fixed point satisfies

```
x* ∈ K(c,s) := ⋃_{i : v_i ≠ 0} P_i^{s_i}(c).
```

The algorithm maintains `X_t = [0,1]^d ∩ ⋂_{r≤t} K(c^r, s^r)`, and needs each
`c^t` to be a **centerpoint**: `μ(X_t ∩ K(c^t,s)) ≤ (1−α) μ(X_t)` for *every*
`s ∈ {±1}^d`, so the region shrinks whatever the oracle answers.

`c` is **balanced** for `μ` when `μ(P_i^+(c)) = μ(P_i^-(c))` for all `i`. Since
the `2d` pyramids partition up to null sets, balance gives `μ(K(c,s)) = μ/2`
exactly, for every `s`.

## 2. The balanced point is a convex program

This is the part I could not find in CLY, HLSW, or Feodorov–Haslebacher. CLY get
balance from **Brouwer** (their Lemma 6, on a thickening `S^t`, then `t → ∞` in
Lemma 7, then parity-aware rounding in Lemma 8). F–H get it from an ad-hoc local
search ("pulling") driven by the non-convex potential `Σ_i (π_i − vol(X)/d)²`,
about which they remark that the volume flow "seems difficult to control".

Both are unnecessary. Define

```
Φ_μ(c) = ∫ ‖y − c‖_∞ dμ(y)
```

the **`ℓ∞` Fermat–Weber functional** of `μ`. It is convex (an integral of
convex functions of `c`) and coercive. Where differentiable,

```
∂Φ_μ/∂c_i = μ(P_i^-(c)) − μ(P_i^+(c)),
```

so *stationary points of `Φ_μ` are exactly the balanced points of `μ`.* Existence
is now compactness, not Brouwer. The reason this works for `ℓ∞` specifically:
the subgradients of `‖·‖_∞` are the vertices `±e_i` of the dual (cross-polytope)
ball, so the "direction from `c` to `y`" is quantised into exactly the `2d`
pyramid classes.

### 2.1 The one-line proof, avoiding subdifferentials entirely

`‖y − c‖_∞ = max_{k,σ} σ(y_k − c_k)` is a max of `2d` affine functions of `c`.
The directional derivative of a finite max of affines is the max over the active
set, so for direction `u`:

```
D_u ‖y − ·‖_∞ (c) = max_{(k,σ) ∈ A(y,c)} (−σ u_k),   A(y,c) = argmax set.
```

Take `u = −s`. Then `−σ u_k = σ s_k ∈ {±1}`, and

* `y ∈ K(c,s)` ⟺ some `(i, s_i) ∈ A(y,c)` ⟺ the max is `+1`;
* `y ∉ K(c,s)` ⟺ every active `(k,σ)` has `σ = −s_k` ⟺ the max is `−1`.

Hence **exactly**

```
D_{−s} Φ_μ (c) = μ(K(c,s)) − μ(complement of K(c,s)).
```

> **Theorem A.** Let `μ` be a finite measure with `∫‖y‖dμ < ∞` and let `c`
> minimise `Φ_μ`. Then for every `s ∈ {±1}^d`,  `μ(K(c,s)) ≥ μ(ℝ^d)/2`.
>
> *Proof.* At a minimiser every directional derivative is `≥ 0`; apply the
> identity above in direction `−s`. ∎

Three remarks that matter for the formalisation:

1. **No boundary case.** A minimiser always exists inside the coordinatewise
   bounding box of `supp μ` (moving `c_i` back into `[min y_i, max y_i]` weakly
   decreases every term). So there is a minimiser in `[0,1]^d` and every
   direction `−s` is legitimate — no clipping, no `MapsTo`, no face analysis.
2. **Atoms are free.** The argument never assumes `μ` is atomless, so it applies
   directly to the *counting measure on the candidate set* `T`. This means CLY's
   thickening `S^t`, the `t → ∞` limit (Lemma 7), and the parity-aware rounding
   (Lemma 8) are all unnecessary — the ties that the parity trick exists to
   handle are absorbed by the `max` over the active set.
3. **It is not even a global minimiser that is needed** — any `c` with
   `D_{−s}Φ ≥ 0` for the `2^d` directions `s` works.

### 2.2 Finite `T`: it is a linear program

For `T = {y^1,…,y^N}` finite, minimising `Φ(c) = Σ_j ‖y^j − c‖_∞` is

```
min  Σ_j t_j
s.t. t_j ≥  y^j_i − c_i     ∀ i ∈ [d], j ∈ [N]
     t_j ≥ −y^j_i + c_i     ∀ i ∈ [d], j ∈ [N]
```

`N + d` variables, `2dN` constraints. Solvable exactly in poly time in the
bit-size (weakly poly by ellipsoid/IPM; strongly poly is not needed since all
data are grid rationals). Its optimum is an *exact* balanced point of `T`:
every one of the `2^d` pyramid unions captures `≥ N/2` of `T`.

So: **the balanced point of an explicitly-given candidate set is an LP.** CLY's
brute-force search over the grid is replaced by one LP solve.

## 3. What is actually left

With §2, the F–H pipeline is polynomial *except for one subroutine*.

> **Theorem B (reduction).** Suppose there is a routine that, given the cut
> history `(c^1,s^1),…,(c^t,s^t)`, outputs `N` points whose joint law is within
> total variation `δ` of `N` i.i.d. uniform samples from
> `X_t = [0,1]^d ∩ ⋂_r K(c^r,s^r)`, in time `poly(d, t, N, log(1/δ))`.
> Then there is an algorithm making `O(d log(1/ε))` queries and
> `poly(d, log(1/ε))` time that finds an `ε`-fixed point w.h.p.

*Why.* The class `{K(c,s)}` has VC dimension `O(d² log d)` (each pyramid is an
intersection of `2(d−1)` halfspaces with *fixed* normals `e_i ± e_j` and
`c`-dependent offsets; take a union of `d` of them). So `N = Õ(d²/α²)` uniform
samples `α`-approximate `vol(X_t ∩ K(c,s))/vol(X_t)` uniformly over all `c, s`.
Solve the LP of §2.2 on the sample: by Theorem A the empirical capture is
`≥ N/2` for every `s`, so by uniform convergence `c` is a `(1/2 − α)`-centerpoint
of `X_t`. Query, cut, repeat; `vol` shrinks by `(1/2 + α)` per round.

Everything else — the cut lemma, the LP, the shrinkage accounting, termination —
is elementary and polynomial. **The entire open problem is now a sampling
problem with no fixed points and no games in it.**

### 3.1 Equivalent combinatorial form of the gap

Because the pyramids at a common apex are measure-disjoint,

```
X_t  =  ⊔_{π ∈ [d]^t} P_π      (up to a null set),
P_π  =  [0,1]^d ∩ ⋂_{r≤t} P_{π(r)}^{s^r_{π(r)}}(c^r)
```

and each cell `P_π` is a **convex polyhedron with `≤ 2(d−1)t + 2d` facets** — so
each individual cell can be sampled and its volume estimated in poly time by
standard convex-body machinery. Therefore:

> Uniform sampling from `X_t` ≡ sampling `π ∈ [d]^t` with probability
> `∝ vol(P_π)`, i.e. a Gibbs-measure / partition-function problem on a product
> space whose weights are individually poly-time approximable.

The number of *nonempty* cells is `O((d²t)^d)` (cells of an arrangement of the
`O(d²t)` hyperplanes `y_i − c_i = ±(y_j − c_j)`), which is exactly F–H's
`(nd)^{O(d)}`. Enumerating them is the current algorithm. Poly time needs the
Gibbs sampler instead.

This opens the problem to the approximate-counting toolbox — MCMC over `π` with
volume-ratio Metropolis acceptance, sequential Monte Carlo with resampling
(the round structure is naturally sequential: each particle splits into `d`
children per cut), correlation-decay, Barvinok interpolation. None of these has
an obvious mixing/ESS proof here, but the target is now a clean, standard-shaped
question.

### 3.2 Why the ellipsoid/Vaidya route is *provably* unavailable

Work in `w_i = s_i(y_i − c_i)`; then `K(c,s) = ⋃_{i∈S} C_i` with
`C_i = {w : w_i ≥ |w_j| ∀j}`, and the removed set is `−K` (the point reflection
of the kept set through `c`). Two consequences:

* **Good news.** For *any* measure symmetric about `c`, the cut removes exactly
  half the mass. That is the ideal ellipsoid-method situation.
* **Bad news.** `cone(⋃_{i∈S} C_i) = ℝ^d` as soon as `|S| ≥ 3` and `d ≥ 3`
  (e.g. `(1,−1,−1) + (−1,1,−1) + (−1,−1,1) = −(1,1,1)`, and similarly with the
  coordinates outside `S` cancelled in pairs). So the convex hull of the kept
  region is everything: **no convex outer approximation loses any volume at
  all.** This is the `k ≥ 3` non-convexity barrier CLY point at, made
  quantitative.

But the threshold is sharp, and that is the useful part:

> For `|S| ≤ 2`, `⋃_{i∈S} C_i ⊆ {w : w_i + w_j ≥ 0}` — a genuine linear
> halfspace through `c`. (If `w ∈ C_i` then `w_i ≥ |w_j| ≥ −w_j`.)

> **Corollary C.** If extra queries can narrow the candidate index set from `[d]`
> down to **two** coordinates — i.e. certify `x* ∈ P_i^{s_i}(c) ∪ P_j^{s_j}(c)`
> for a known pair `{i,j}` — then every `X_t` is a convex polytope, and the
> classical centroid/Grünbaum (or Vaidya) cutting-plane machinery gives an
> outright `poly(d, log 1/ε)`-time algorithm.

This is a much weaker ask than identifying the single dominant coordinate, and
it is exactly why `d = 2` is easy (there `|S| = d = 2` always, and the cut *is*
a halfspace). We have query budget to spend: CLY use `O(d² log 1/ε)` and poly is
`poly(d, log 1/ε)`, so `poly(d)` extra queries per round are free. Whether
`poly(d)` queries around `c` suffice to eliminate `d − 2` coordinates is, I
think, the single most promising concrete question in this direction.

## 3.3 The star-kernel, its collapse, and a working hit-and-run algorithm

*(Added after a session of analysis + computation; scripts in
`notes/polytime_experiments/`. This supersedes parts of §4 below.)*

Since every convex-outer-approximation method is provably dead (§3.2,
`conv K = ℝ^d`), the entire problem is: **sample / estimate the volume of the
non-convex `X_t = box ∩ ⋂_r K(c^r,s^r)` in poly time.** Three findings.

### Clean membership and the Kernel Theorem

In sign-aligned coordinates `w_i = s_i(y_i − c_i)`, the cut set has a one-line
membership test:

```
y ∈ K(c,s)  ⟺  max_i w_i + min_i w_i ≥ 0
```

(the largest coordinate dominates the most-negative). Verified over 2·10⁵ random
points, all `d` (`verify_kernel.py`).

`K(c,s)` is **star-shaped about its apex `c`** (each pyramid is a convex cone
with apex `c`). Its kernel — the set of points that see all of `K` — is exactly:

> **Kernel Theorem.**
> `ker(K(c,s)) = { z : s_i(z_i−c_i) + s_j(z_j−c_j) ≥ 0  for all i≠j }`
> — an intersection of `\binom d2` halfspaces: a **convex polyhedral cone**,
> apex `c`, `O(d²)` facets.

*Proof of `⊇`:* for `z` with all pairwise `w`-sums `≥0` and any `y∈K`, along
`q=λz+(1−λ)y` pick `b=argmax_j y_j`; then `q_b+q_a = λ(w^z_a+w^z_b)+(1−λ)(y_a+y_b)
≥0` where `a=argmin q` (using `y_a+y_b ≥ min y+max y ≥ 0`), and a symmetric
argument covers `a=b`. So `q∈K`. `⊆` confirmed numerically: every violator, even
`w`-pair-sum `= −0.008`, exhibits a ray that exits and re-enters `K`.

**Consequence.** `⋂_r ker(K(c^r,s^r)) ∩ box` is an intersection of `O(td²)`
halfspaces — a **poly-size polytope**. So "is `X_t` star-shaped?" is a single
LP, and if feasible, `X_t` is star-shaped about any solution `p_0`; then `X_t` is
uniformly samplable *exactly* by ray-shooting from `p_0` (radial function
`ρ(u)=min_r ρ_r(u)`, each `ρ_r` a poly computation) — **no Markov mixing at
all**.

### The collapse (negative)

The catch: the kernel polytope **collapses** as cuts accumulate
(`starshape_collapse.py`). Querying at unconstrained balanced points, `⋂_r ker`
goes empty after `O(d)` rounds (`X_t` stops being star-shaped). Constraining the
query to stay in the kernel keeps star-shapedness but the kernel margin decays
`1.0 → 0.34 → 0.08 → 0.008 → 0` and the volume **stalls** — a kernel-confined
point is too peripheral to halve `X_t`. **Star-shapedness and progress are
incompatible past ~`O(d)` rounds**, so the exact ray-shooting sampler is only
valid early. Star-shapedness was only *sufficient* for sampling, not necessary.

### Hit-and-run: a concrete candidate randomised algorithm

Drop star-shapedness; sample `X_t` by **hit-and-run** (only needs
connectivity + conductance). Along a random line, `X_t ∩ line` is a union of
intervals — sample uniformly among the feasible `t`'s, which can hop between
cells. The full loop (`algo_linear.py`, `algo_topical.py`):

```
maintain cut list; each round:
  S  = hitrun(X_t)                       # ~50 samples, warm-started at the
  bp = argmin_c Σ_{y∈S} ‖y−c‖∞  (LP)     #   previous query pt (always ∈ X_{t+1})
  query f(bp); s = ternary sign(f(bp)−bp); append cut K(bp,s)
```

`bp` is always in `X_{t+1}` (apex of its own cut) — a free warm start. Empirics:

* **Easy (linear) `f=clip(λMx+b)`:** clean geometric convergence, `‖bp−x*‖∞:
  0.5 → 10⁻³` in `~10d` rounds, `d=4,5,6`. **Rate independent of `λ`**: identical
  trace at `λ=0.9995` and `λ=1−10⁻⁷` (where value iteration needs `~10⁷` steps).
  *Caveat:* linear fixed points are trivially poly (solve `(I−λM)x=b`), so this
  only validates the machinery.
* **Hard (topical min/max/avg, i.e. Shapley/SSG-style) `(1−δ)`-contractions:**
  genuine `δ`-independent progress and good approximate fixed points
  (`‖f(bp)−bp‖ ~ 10⁻⁴`), but convergence to `x*` is **slower and noisier**:
  `‖bp−x*‖∞` tracks the region diameter (so `x*` sits near the *edge* of `X_t`)
  and the region shrinks slower than the ideal `2^{1/d}`/round. With light
  hit-and-run the sample spread intermittently **collapses to a point** (mixing
  failure); heavier hit-and-run removes the collapse but the shrinkage is still
  sub-ideal within budget.

**The ternary sign is essential** (matches §5.2): forcing `s_i=1` on a
near-zero displacement makes invalid cuts that exclude `x*` and the algorithm
converges to the wrong point. Excluding `{i:|v_i|≤tol}` from the union fixes it.

### The distilled crux and its cross-field homes

The whole open problem is now a single, standard-shaped question:

> **Does hit-and-run (or the ball walk) mix in `poly(d,t)` time on
> `X_t = box ∩ ⋂_{r≤t} K(c^r,s^r)`, an intersection of `ℓ∞` pyramid-unions?**

If yes ⟹ a randomised `poly(d, log 1/ε)`-time algorithm (hence SSG ∈ BPP = P),
so a full proof is expected to be very hard — but the *shape* of the question is
now the well-developed geometry-of-Markov-chains kind, not "solve a game."
Structural handles to exploit: the body is star-shaped early (Kernel Theorem);
each cut's removed set is the **point reflection** of the kept set through `c`
(§3.2); the apexes are Fermat–Weber centers of nested, geometrically shrinking
regions (non-adversarial). The empirical spread-collapses on hard instances are
the honest warning sign that the isoperimetry may genuinely degrade.

**Reductions to other fields** (a question worth keeping in view):

1. **Geometry of MCMC / sampling non-convex bodies.** The direct target above.
   Convex-body sampling is the Dyer–Frieze–Kannan / Lovász–Vempala theory;
   here the frontier is sampling **unions/intersections of cones**, or
   **star-shaped / bounded-non-convexity** bodies — isoperimetry of such bodies
   is largely open and this is a clean, motivated instance.
2. **Nonlinear Perron–Frobenius / tropical (max-plus) spectral theory.**
   `ℓ∞`-nonexpansive *monotone* maps are exactly **topical functions**
   (Gaubert–Gunawardena, Nussbaum); their fixed points are tropical
   eigenproblems, and this is the field the whole problem is a special case of.
   Ties directly to **mean-payoff and stochastic games**.
3. **Approximate counting / statistical mechanics.** `vol(X_t)` is the partition
   function of a Gibbs measure on the product space `[d]^t` with weights =
   cell volumes (§3.1); sampling ≡ counting (JVV self-reducibility). A `#P`-style
   problem with special geometric weights.
4. **Stochastic games / CLS = PPAD∩PLS.** The complexity home
   (Condon; Fearnley–Goldberg–Hollender–Savani); poly-time here ⟹ SSG ∈ P.

## 4. Recommended next steps

**Research, in decreasing order of expected value:**

1. *Corollary C's hypothesis.* Can `poly(d)` queries near `c` narrow the pyramid
   union to two? Even narrowing to `O(1)` with a *randomised* guarantee, or to
   two out of `d` only `1/poly` of the time (with restarts), would do.
2. *The Gibbs sampler of §3.1.* Try SMC-with-rejuvenation first — it is
   implementable today and the cell volumes are computable, so it is directly
   testable on random instances to see whether effective sample size collapses.
3. *Structure of the cuts.* The apexes `c^t` are not adversarial — they are
   Fermat–Weber points of nested, geometrically shrinking regions. A purely
   adversarial version of §3.1 is surely hard, so a solution must use this. Are
   consecutive `X_t` "well-rounded" in a sense that gives mixing?
4. *Does `conv(X_t)` shrink over blocks?* A single cut does not shrink the
   convex hull (§3.2), but `d` consecutive cuts might. If
   `vol(conv(X_{t+d})) ≤ (1−1/poly) vol(conv(X_t))`, the ellipsoid method
   applies to `conv(X_t)` and we are done.

**Formalisation (this repo): done.**

Theorem A is formalised in `Tfnp/Contraction.lean` as
`exists_balanced_point_box` (finite `T ⊆ [lo,hi]^k`, real balanced point) and
`exists_balanced_point_real` (the `EVEN(n,k)` grid version used by the
algorithm). Both depend only on `propext`, `Classical.choice`, `Quot.sound`.

What it collapsed:

* `exists_continuous_balanced_point` — the only consumer of `brouwer_cube` —
  is gone, together with `Thickening`, `vol`, `auxMap` and the two boundary
  lemmas. `Tfnp/Contraction.lean` no longer imports `Tfnp/Brouwer/` at all
  (`CubeBox` moved to `Tfnp/Box.lean`).
* The `sorry` for continuity of `auxMap` (dominated convergence on a
  parameter-dependent indicator) disappeared: `Φ` is continuous because
  `linfDist = dist` for the sup metric on `Fin k → ℝ` (`linfDist_eq_dist`).
* `pyramid_containment_under_rounding` (the parity argument) is deleted;
  `cly_rounding` and the rounding lemmas remain but are off the critical path.
* `exists_balanced_point_int` → `exists_balanced_point_real`, returning
  `c : Vec k`. `halving_from_balanced` generalised from `q : IntVec k` to
  `c : Vec k` (its proof only ever used `q.toVec`); `clyChooseBalanced` and
  `clyAlgorithm` follow.

Net: `Contraction.lean` went from four `sorry`s to one — the candidate-set
invariant ruling out the algorithm's default branch (CLY Lemma 5), which is
unrelated to any of this.

## 5. Formalisation status: the query result is complete

The whole of CLY Theorem 1 is now formalised, `sorry`-free
(`cly_query_complexity` in `Tfnp/Algorithm.lean`; axioms `propext`,
`Classical.choice`, `Quot.sound` only).

Getting there needed three fixes to the earlier scaffolding, all found by trying
to discharge the last `sorry`:

1. **The grid scale was degenerate.** The assembled algorithm ran at `n = 1`,
   where `EVEN(1, k)` is the single point `0`, so `0` was the only point it
   could ever query or return — and the constant `0`-contraction `f ≡ 1` on
   `[0,1]^1` at `ε = 1/2` refuted correctness outright. CLY use
   `n = ⌈16/(γε)⌉`; here, after Observation 1 fixes `γ = ε/2`, that is
   `⌈64/ε²⌉` (`clyGrid`).
2. **The sign vector has to be ternary.** The old algorithm used
   `s : Fin k → Bool`, which silently classifies a *zero* displacement as `−`.
   CLY's `s ∈ {±1, 0}^k` with the union taken over `{i : sᵢ ≠ 0}` is essential:
   the `sᵢ = 0` case of their Lemma 4 is what excludes *both* signs at that
   coordinate.
3. **The shift is `4s`, and there are two lemmas, not one.** The old file had
   only the continuous unshifted statement `x* ∈ ⋃ᵢ 𝒫ᵢ(c, sᵢ)`. CLY need
   `x* ∈ ⋃ᵢ 𝒫ᵢ(a + 4s, sᵢ)` (Lemma 2) *and* the separate fact that a unit ball
   around any point of `⋃ᵢ 𝒫ᵢ(b + 2s, sᵢ)` sits inside `⋃ᵢ 𝒫ᵢ(b, sᵢ)`
   (Lemma 3). The two compose: cut at `b = a + 2s`, so `b + 2s = a + 4s`, and
   what survives is a whole unit ball around the fixed point — which is what
   keeps an even grid point in the candidate set.

`γ` is eliminated by CLY's Observation 1, folded directly into `clyStep`: every
oracle response is damped by `(1 − ε/2)` before use, which makes the map a
`(1 − ε/2)`-contraction whatever `f`'s own factor was, at the cost of a factor
`2` in the accuracy. Existence of the fixed point is Banach
(`exists_fixedPoint_of_contraction`), obtained by extending the damped map to
all of `ℝ^k` through the clamp — not Brouwer.

Everything in §§1–4 above about *time* complexity is unaffected: the
formalisation is of the query result, and the balanced point it uses is
`Classical.choose`n, not computed.

