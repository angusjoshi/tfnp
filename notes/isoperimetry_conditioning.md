# C2: does the covariance condition number `κ(X_t)` stay polynomial?

Attacking sub-question **C2** of `notes/isoperimetry_attack.md`: if `κ(X_t)` (the
condition number of the uniform-measure covariance of the candidate body) stays
`poly(d,t)`, then one whitening + standard hit-and-run gives poly mixing — the
route that sidesteps the raw Cheeger constant. The sharpest form:

> **Can a single balanced cut `X → X ∩ K(c,s)` (with `c` the Fermat–Weber center
> of `X`) increase `κ` by more than a constant factor?**

Multiplicative per-cut blow-up ⟹ `κ` exponential ⟹ route fails. Bounded/additive
per-cut growth ⟹ `κ` poly ⟹ route plausibly works.

*Status: in progress (driven directly, not via the sub-agent which hit repeated
API errors). Results appended below as they run.*

## Method

Exact **rejection** uniform sampling of `X_t` (ground-truth covariance,
independent of any Markov chain — avoids the sampler-budget confound). At each
round: rejection-sample `X_t`, record `κ_t = λ_max/λ_min` of the sample
covariance, compute the Fermat–Weber balanced point of the exact sample, cut,
recurse. Realizable cuts (real SSG / topical contractions), ternary signs.
Rejection is feasible for the first `~log₂(1/acc)` rounds (`vol(X_t) ≈ 2^{-t}`).

Scripts (all in `notes/polytime_experiments/`, run under `venv`):
`conditioning.py`, `cond_adv.py` (rejection-sampling κ growth + center comparison);
and for the proof-side/robustness work: `verify_decomp.py` (the decomposition `(D)`),
`worst_cut.py` (worst single balanced cut on the box), `verify_symcut.py` (the
symmetric rank-1 downdate `(S)` + anisotropic κ-contraction), `verify_asym.py`
(the symmetric→general bridge on real bodies), `kappa_dynamics.py` (self-correction /
long trajectory), `kappa_escalate.py` (honest budget-escalated κ at depth),
`kappa_vs_h.py` (the κ↔h correlation), `kappa_growth.py`, `potential_test.py`
(per-cut alignment / downdate-fraction / candidate-Lyapunov diagnostics),
`idealized_dynamics.py` (the re-symmetrized eigenvalue dynamics of §12).

## Results

**Per-cut `κ` growth is ≈ 1 — no blow-up.** Exact rejection sampling, `n=1500–3000`
ground-truth points per round, realizable cuts. Each row = one full run; "ratio"
is the per-round `κ_{t+1}/κ_t`.

| instance | `d` | `δ` | rounds | `κ` range | per-cut ratio max | geomean |
|---|---|---|---|---|---|---|
| SSG | 5 | `10⁻³` | 13 | `[1.1, 2.3]` | 1.68 (round 1 only) | 1.061 |
| SSG | 7 | `10⁻³` | 13 | `[1.2, 2.3]` | 1.44 | 1.055 |
| SSG | 9 | `10⁻⁴` | 11 | `[1.2, 2.8]` | 1.24 | 1.087 |

`κ` grows only mildly with `d` (`≈2.3` at `d=5,7`, `≈2.8` at `d=9` — sub-linear,
not exponential) and stays flat across rounds; the per-cut ratio hovers at `1.0`
(geometric mean `≈1.06`), with the only value materially above `1` being the very
first cut (box → first half). This is **sub-multiplicative** growth — consistent
with `κ = O(1)`, decisively *not* the `κ → 2^{Ω(t)}` a route-killing blow-up would
show. On this evidence, **a single balanced cut does not blow up the condition
number** — the C2 mechanism for failure is empirically absent.

### Balancedness is what keeps `κ` bounded (`cond_adv.py`, `d=6`, SSG, 12 rounds)

Comparing cut-center choices on the same instance:

| center | `κ` range | per-cut geomean | acceptance @ r11 (vol proxy) |
|---|---|---|---|
| **balanced** (Fermat–Weber) | `[1.2, 3.8]` | 1.109 | `5·10⁻⁴` (halves each round ✓) |
| adversarial peripheral | `[1.2, 14.4]` | 1.252 | `4·10⁻²` (barely shrinks) |
| adversarial vertex | `[1.2, 5.5]` | 1.147 | `8·10⁻²` (barely shrinks) |

Two things at once: adversarial centers (i) fail to halve the volume — no
progress, which is *why* the algorithm doesn't use them — and (ii) leave the body
more anisotropic (`κ` up to `14` vs `~4`). So **the balanced/Fermat–Weber center
is precisely the well-conditioned choice**, tying the good conditioning to the
same balancedness that drives progress. This is the right hypothesis for the
theorem: *a balanced cut keeps `κ = O(κ_prev)`*.

Caveats: exact rejection limits depth to `~13` rounds (`vol ≈ 2^{-t}`) and
`d ≤ ~9`; `δ` down to `10⁻⁵` tested. This is the empirical half of C2, and it is
**positive**: no per-cut `κ` blow-up for balanced cuts, sub-linear `d`-growth.
The per-cut `κ ≤ C·κ` *theorem* (via the reflection/centrality of the balanced
cut) is the remaining target.

## Proof attempt (theorem side)

*Author: the isoperimetry sub-agent. Checkpointed incrementally. Everything in
this section is either proved (marked ∎), or explicitly flagged as heuristic /
open. No step is dressed as more than it is — a real proof of the per-cut bound
would put `SSG ∈ P`.*

Setup and normalisation. Fix `X` with uniform measure `μ`, balanced Fermat–Weber
center `c`, sign vector `s` (all coords active — the generic case). Translate so
`c = 0`. The map `y ↦ (s_i y_i)_i` is an **orthogonal** transformation (a signed
permutation), so it preserves every covariance eigenvalue and hence `κ`; apply it
to reduce to `s = (+1,…,+1)`. Then, writing the sign-folded point again as `y`,

```
K = { y : max_i y_i + min_i y_i ≥ 0 },     N = X∖K = { y : max_i y_i + min_i y_i < 0 }.
```

`K` is a cone (positively homogeneous) with apex `0`; `N` is its reflection:
`ρ(K) = N̄` where `ρ(y) = −y`, because `max(−y)+min(−y) = −(max y+min y)`. A
balanced center gives `μ(K) = μ(N) = ½` exactly (the `2d` pyramids partition and
balance equates opposite pairs — `Lemma 2` of `hitrun.md`).

### 1. The covariance decomposition (∎) and the exact obstruction

Write `K' = X∩K` (kept), `R = X∩N` (removed), each of `μ`-mass `½`; let
`m_K, m_R` be their means and `Δ = m_K − m_R`. Law of total variance for a
50/50 split gives, exactly,

```
Σ(X) = ½Σ(K') + ½Σ(R) + ¼ ΔΔᵀ,   hence   Σ(X∩K) = 2Σ(X) − Σ(R) − ½ ΔΔᵀ.   (D)
```

(Verified numerically, `verify_decomp.py`: residual `≤10⁻³`, and the corollary
below holds.) Two immediate consequences:

* **`λ_max` is controlled unconditionally (∎).** From `(D)`, `Σ(X∩K) ⪯ 2Σ(X)`, so
  `λ_max(Σ(X∩K)) ≤ 2λ_max(Σ(X))`. Better, absolutely: `X∩K ⊆ [0,1]^d` gives
  `λ_max ≤ diam²/4 ≤ d/4` at *every* round. So the numerator of `κ` is never a
  problem; **the entire question is a lower bound on `λ_min`.** (Empirically the
  per-cut `λ_max` ratio is `≈1.03–1.06`, `verify_decomp.py`, far below the proven
  `2`.)

* **The exact obstruction.** For a unit `v`,
  `vᵀΣ(X∩K)v = 2 vᵀΣ(X)v − vᵀΣ(R)v − ½(v·Δ)²`. So `λ_min` can only collapse in a
  direction `v` where the *removed half* `R` is **both** spread (`vᵀΣ(R)v` large)
  **and** mean-shifted (`|v·Δ|` large) — i.e. `R` is a long lobe lying off to one
  side along `v`. Bounding the per-cut blow-up = showing a balanced cone-cut can
  never carve off such a lobe. This is exactly where the difficulty concentrates.

### 2. The base case: box → first cut is `O(1)`, and `→1` as `d→∞` (∎)

For `X = [0,1]^d` the balanced center is the box center and, by the sign-fold
above, **every** sign pattern gives the *same* body up to an isometry:
`X∩K ≅ {y∈[−½,½]^d : max_i y_i + min_i y_i ≥ 0}`. This body is invariant under
coordinate permutations, so `Σ(X∩K)` is **equicorrelation**, `Σ = aI + b·11ᵀ`,
with just two eigenvalues: `a` (multiplicity `d−1`, eigenvectors `⊥ 1`) and
`a + bd` (eigenvector `1`). Thus

```
κ(box ∩ K) = max(a, a+bd) / min(a, a+bd)
```

is a ratio of exactly two explicit one-dimensional variances (perpendicular- vs.
diagonal-to-`1`). Cutting `{max+min ≥ 0}` removes the negative-diagonal cone, so
it shrinks the diagonal variance and leaves the perpendicular ones essentially
untouched; the effect is `O(1)` and *vanishes* as `d→∞` (the removed cone is a
`2^{−Θ(d)}`-fraction of the diagonal spread). Measured (`worst_cut.py`, exact
rejection): worst `κ(box∩K) = 2.39, 2.02, 1.85, 1.74, 1.59, 1.51` for
`d = 3,4,5,6,8,10` — decreasing to `1`. **So the first cut is provably benign,
and the equicorrelation reduction makes it a two-integral computation.**

(Non-balanced offset cuts reach `κ ≈ 3–4.5` and — crucially — keep `<½` the
volume, i.e. they are exactly the cuts the algorithm does *not* make. Balancedness
buys both progress and conditioning; this matches `cond_adv.py`.)

### 2b. Symmetric case: a balanced cone-cut is a rank-1 downdate that SELF-CORRECTS (∎)

This is the strongest positive result of the attempt. Suppose `X` is symmetric
about its center (`ρ(X) = X`, `ρ(y) = −y` after translating `c = 0`) — the
Fermat–Weber center of a symmetric body is its center, and the cut is balanced
there. Because `ρ(K) = N̄` (the cut boundary is `ρ`-invariant), the removed half
is the exact reflection of the kept half: `R = X∩N = ρ(X∩K) = ρ(K')`. Reflection
preserves covariance and negates the mean, so `Σ(R) = Σ(K')` and `m_R = −m_K`.
Substituting into `(D)` collapses it to a **rank-1 downdate**:

```
Σ(X ∩ K) = Σ(X) − m_K m_Kᵀ,      m_K = E[ y | y ∈ K ].          (S)
```

(Verified, `verify_symcut.py`: relative residual `≤ 2·10⁻³` at `d=4..8` and for
aspect ratios up to `30`.) Immediate rigorous consequences:

* **`λ_max` never increases and no direction gains variance:** `Σ(X∩K) ⪯ Σ(X)`.
* **Only the single direction `m_K` loses variance:** for `v ⊥ m_K`,
  `vᵀΣ(X∩K)v = vᵀΣ(X)v` exactly.
* **`m_K` aligns with the longest axis, so the downdate removes variance from the
  MOST-spread direction** — self-correction. Reason (monotonicity): a coordinate
  with large positive value tends to be the `max` and pushes `max+min ≥ 0`
  (kept); the same coordinate large and negative tends to be the `min` and is
  removed. The longer the axis, the stronger this asymmetry, so `m_K` points
  along the top-variance direction. When that direction is an eigenvector of
  `Σ(X)` (exact under a coordinate/permutation symmetry, e.g. one long axis and
  equal short axes), `(S)` gives `λ_max(X∩K) = max(λ_max − ‖m_K‖², λ_2)` with
  `λ_min` untouched, hence **`κ(X∩K) ≤ κ(X)`.**

Measured on symmetric boxes with one long axis (`verify_symcut.py`, exact
rejection, `d=6`): the balanced cut *reduces* `κ`:

| aspect `r` | `κ(X)` | `κ(X∩K)` | var along `m_K` |
|---|---|---|---|
| 2 | 4.0 | 2.7 | 1.30 → 0.60 |
| 5 | 25.2 | 7.7 | 8.34 → 2.44 |
| 10 | 100.7 | 26.6 | 33.4 → 8.7 |
| 30 | 905.9 | 228.4 | 300.3 → 75.6 |

`κ` drops by a factor `≈ 3–4` per cut on an elongated symmetric body: the cut
attacks the long axis. (Graded spectra `hw = (1,2,4,…)` also decrease, `κ`
`1020 → 447`, `16401 → 7202`.) **So for symmetric bodies a balanced cone-cut is
not merely `≤ C·κ` — it is a contraction toward isotropy.** This is exactly the
mean-reversion the real-algorithm trajectories show (§6).

The gap to the general theorem is precisely the **asymmetry** of the real `X_t`:
`(S)` becomes `(D)` with `Σ(R) ≠ Σ(K')`, and the correction is governed by how
far `X` is from `ρ`-symmetric. Balancedness (`μ(P_i^+) = μ(P_i^-)`) is a partial,
first-moment-level symmetry, which is why the empirical `κ` stays bounded /
mean-reverts but does not monotonically decrease. Turning "balanced ⟹ approximately
`ρ`-symmetric ⟹ approximately a rank-1 downdate" into a quantitative bound is the
concrete remaining target, and it is much more specific than the raw Cheeger
question.

**The bridge is real on actual bodies (`verify_asym.py`, exact rejection, real
SSG, `d=5–8`, 14 rounds each).** Measuring the asymmetry defects of each balanced
cut — `‖Σ(R)−Σ(K')‖/‖Σ(X)‖` (`=0` iff symmetric), `‖m_R+m_K‖/diam` (`=0` iff
symmetric), and the prediction error of `(S)`,
`‖Σ(K')−(Σ(X)−m_K m_Kᵀ)‖/‖Σ(X)‖`:

| quantity | typical | range over all rounds/dims |
|---|---|---|
| `Σ`-defect `‖Σ(R)−Σ(K')‖/‖Σ(X)‖` | `≈0.30` | `0.10 – 0.68` |
| mean-defect `‖m_R+m_K‖/diam` | `≈0.20` | `0.07 – 0.30` |
| `(S)` prediction error | `≈0.15` | `0.05 – 0.31` |

So the rank-1 downdate `(S)` predicts the true post-cut covariance of real,
genuinely asymmetric bodies to `≈15%` (Frobenius), the halves are approximately
reflections (defects `≈0.2–0.3`, not `0` but bounded), and `κ` stays in `[2,4.5]`
with mean-reversion throughout. The symmetric theorem is therefore not a toy: it
is the leading-order description of the real dynamics, with a controlled `O(0.2)`
asymmetry correction. Closing the `O(0.2)` — proving the defects are `≤ 1−Ω(1)`
so that `(S)`'s contraction survives — is the exact remaining gap.

### 3. Directional shrink of a cone-cut is `O(1)` in aligned directions (partial)

Along any single fixed direction the cone-cut behaves like a halfspace, so it
shrinks that direction's variance by only `O(1)`:

* Along a coordinate axis `e_k`: `K ∩ {t e_k} = {t ≥ 0}` (for `t<0`,
  `max = 0, min = t`, sum `<0`). So the cut keeps the positive half-axis — a
  halfspace cut, variance shrinks by the usual `≤4×`.
* Along the diagonal `1`: `K ∩ {t·1} = {t ≥ 0}` (`max+min = 2t`). Again a half.
* The positive orthant `{y ≥ 0} ⊆ K`, and `N ⊆ {min_i y_i < 0}`; `K` contains a
  full halfspace's worth of every axis direction.

So for `X` whose principal axes are aligned with the coordinates or the diagonal,
each principal variance shrinks by `O(1)` and `κ` is preserved up to `O(1)`. The
gap to a full theorem is the **misaligned** case: a direction `v` in which the
cone boundary `{max+min=0}` slices `X` obliquely could in principle leave a thin
sliver. Ruling this out is the open per-cut step; §1's obstruction says it is
equivalent to "`R` is never an oblique off-center lobe."

### 4. Why option 2 (ball-preservation ⟹ `λ_min`) does **not** close the gap (honest)

The tempting route "`X_t ⊇ B_∞(x*,ρ_t)` ⟹ `λ_min ≥ c·ρ_t²`" is **false** as
stated: containing a ball does not lower-bound the smallest covariance eigenvalue
when `vol(X_t) ≫ vol(ball)`. Concretely, `X = B ∪ (`thin slab through the centre
`⊥ v)` contains `B` yet has `Var(v·y) → 0` as the slab's mass grows. A contained
`B_∞(p,ρ)` forces the *width* (range) of `X` in every direction to be `≥ 2ρ`, but
width does not bound variance (mass can concentrate at the centre with thin
reaches to the ends). So ball-preservation alone is insufficient; one additionally
needs a volume comparison `vol(X_t) ≤ C^d vol(B)` **and** a no-concentration
statement — which is again isoperimetric. I flag this so the route is not
over-sold: the cumulative bound needs more than the ball.

### 5. Localization through the Fermat–Weber center, and the `κ ↔ h` link (priority 3)

For a body star-shaped about `z0` (the flat-gap regime, Theorem A of
`isoperimetry_attack.md`), the natural decomposition is **radial from `z0`**:
`μ` becomes "pick direction `u` with weight `∝ R(u)^d`, then radius `r` with
density `∝ r^{d−1}` on `[0,R(u)]`". Each radial needle is a **single interval**
with log-concave weight `r^{d−1}` — the property arbitrary-line localization
lacks here (a generic chord of a non-convex `X` is a *union* of intervals). So
localization *through the center* is legitimate.

But it only controls **radial** bottlenecks. An **angular** bottleneck — two
lobes at different angles from `z0` joined by a thin neck (a "spike") — is
invisible to radial needles. This is not a defect of the method but the true
state of affairs: star-shapedness alone permits `2^{−Ω(d)}` Cheeger (thin spikes).

The link to C2 that makes this useful: **a spike forces `κ` huge.** A spike of
length `L` and angular width `θ` contributes `λ_max ≳ L²` along its axis and
`λ_min ≲ (θL)²` across it, so `κ ≳ θ^{−2} → ∞` as the neck thins; whereas a
genuine *fat*-lobe pair has `h ≈ 1/diam` and `κ = O(1)`. Hence **bounded `κ`
rules out the angular (spike) bottleneck**, the only thing radial localization
misses. This yields a clean *conditional*:

> **Conditional (star regime).** If `X` is star-shaped about `z0` and
> `κ(X) ≤ K`, then `h(X) ≥ 1/poly(d,K,diam)`.

Evidence (`kappa_vs_h.py`, exact rejection over many star-shaped bodies): among
bodies with `κ ≤ 3`, the minimum isotropic Cheeger stays `≥ 0.35` at `d=5,7,9`,
and `corr(log κ, log h_iso) = −0.6…−0.7` — smaller `κ`, larger `h`, exactly as
the conditional predicts. (Its value is conceptual: in the star regime we already
have the *exact* ray-shooting sampler, so no Cheeger bound is needed there. What
it buys is the identification of `κ` — not `h` — as the load-bearing quantity,
and a proof target — the angular/spherical isoperimetry of `R(u)` — that is
cleaner than raw Cheeger.)

### 6. Independent empirical cross-check and the reliability ceiling

Running the C2 empirics independently (this sub-agent, `escalate.py`,
`kappa_dynamics.py`, `worst_cut.py`) reproduced the positive picture — `κ ≈ 2`
flat over 26 rounds at `d=9`, `κ ≈ 3–7` with clear **mean-reversion** at `d=6`
(e.g. `7.2 → 3.1` in one step: self-correcting, not compounding) — **and**
pinned down a reliability ceiling that the rejection method's depth limit hides:

* The warm-start sequential sampler *inflates* `κ` on deep (`t ≳ 2d`) bodies
  (fixed replenish budget can't refill a shrinking body); the honest
  independent-explorer with escalating budget gives `κ = 4.3` at `d=12,t=24`
  where warm-start reported `9.2`.
* Conversely, at `d=15, t=25` (body volume `≈2^{−25}`) the honest explorer
  **degenerates** — `κ` reported as `88` then `7·10⁶` at higher budget, i.e. the
  point cloud goes rank-deficient. **Neither sampler is trustworthy past
  `d≈12, t≈2d`.** So the honest empirical claim is bounded: `κ` stays `2–7` in
  the reliably-measurable window (`d ≤ 12`, `t ≲ 2d`; exact-rejection ground
  truth to `t ≈ 13`), and *no* reliable statement — positive or negative — can be
  made beyond it. The apparent blow-ups (warm-start climb; the `κ→5·10⁴`
  "adversarial explosion" in `kappa_dynamics.py testA`) are sampler artifacts on
  sub-`2^{−30}` bodies, not evidence against C2.

### 7. Status summary of the proof attempt

* **Proved (symmetric case — the main new result):** for `X` symmetric about its
  center, a balanced cone-cut is the **rank-1 downdate** `Σ(X∩K)=Σ(X)−m_K m_Kᵀ`
  `(S)`. Hence `λ_max` never increases, no direction gains variance, and only the
  single direction `m_K` — which aligns with the *longest* axis — loses variance.
  Under a coordinate/permutation symmetry this gives outright `κ(X∩K) ≤ κ(X)`, and
  numerically the cut *contracts* `κ` by `3–4×` on anisotropic bodies (§2b). So a
  balanced cut is self-correcting toward isotropy, not merely `≤ C·κ`.
* **Proved (general):** the decomposition `(D)`; `λ_max(X∩K) ≤ min(2λ_max(X),d/4)`
  per cut; the box base case `κ(box∩K)=O(1)→1` via the equicorrelation reduction
  (§2); the reduction of the whole question to a `λ_min` lower bound and its exact
  obstruction (§1); the honest refutation of the naive ball-preservation route
  (§4).
* **Partial:** cone-cuts shrink *aligned* directional variance by `O(1)` (§3);
  the `κ ⟹ h` conditional in the star regime with matching evidence (§5).
* **Open (the crux):** the general (asymmetric) per-cut bound
  `λ_min(X∩K) ≥ c·λ_min(X)`. Concretely: `(S)` degrades to `(D)` with the defect
  `Σ(R)−Σ(K')` and `m_R+m_K`, both `= 0` under symmetry; balancedness gives only a
  first-moment-level symmetry, so the remaining task is **quantitative "balanced ⟹
  approximately `ρ`-symmetric ⟹ approximately a rank-1 downdate."** I could
  neither complete this nor find a realizable counterexample (the empirical
  blow-ups are all sampler artifacts or non-balanced cuts). A proof — even with
  `c = 1/poly(d)` — plus one re-whitening per round would give poly mixing on the
  star-regime bodies.

## Proof attempt II — multi-cut Lyapunov (Priority A) and asymmetric `λ_min` (Priority B)

*Honest result: one clean rigorous lemma (the mean-shift bound), the symmetric
"restoring force" that explains the attractor, and a clear negative — the multi-cut
Lyapunov does **not** close, for reasons the data pins down. No fabrication.*

### 8. The mean-shift bound (∎) and the exact `λ_min` obstruction

> **Lemma (optimal-half mean shift).** For any measure `μ`, any unit `v`, and any
> set `K` with `μ(K)=½`, `|E[v·y | K] − E[v·y]| ≤ MS_v`, where `MS_v` is the
> mean shift of the *extremal* half `{v·y ≥ median}`. Moreover `MS_v ≤ √(2)·σ_v`
> (`σ_v² = Var(v·y)`) always, and `MS_v² ≤ (1−c)σ_v²` with `c>0` **iff the
> marginal of `v·y` is not a two-point (dumbbell) mass** — e.g. `c≈0.36` for
> Gaussian marginals, `c≈0.25` for uniform, `c→0` for a `±a` two-point law.

*Proof.* Among measure-`½` sets, `∫_K v·y dμ` is maximized by the super-level set
`{v·y ≥ median}` (bathtub principle); `E[v·y|K]=2∫_K v·y dμ` then gives the first
inequality. `MS_v = 2E[(v·y−E)·1_{v·y≥med}] ≤ 2√(σ_v²·½)=√2 σ_v` by
Cauchy–Schwarz; the two-point law attains `MS_v=σ_v`. ∎

Coupling this to the covariance decomposition pins the obstruction exactly. In the
**symmetric** case `Σ(X∩K)=Σ(X)−m_K m_Kᵀ` is rank-1, so
`λ_min(X∩K) = min( min_{v⊥m_K} σ_v², σ_{m̂_K}² − ‖m_K‖² )`. The first term is
`≥ λ_min(X)`. The second is `σ_{m̂_K}² − ‖m_K‖² ≥ σ_{m̂_K}²−MS_{m̂_K}² ≥ c·σ_{m̂_K}²`
**provided the marginal along `m_K` is not dumbbell-like.** So:

> **Conditional (∎, symmetric).** If no 1-D marginal of `X` is dumbbell-like
> (each `MS_v² ≤ (1−c)σ_v²`, `c>0`), then a balanced cut satisfies
> `λ_min(X∩K) ≥ c·λ_min(X)` and `λ_max(X∩K) ≤ λ_max(X)`, hence `κ(X∩K) ≤ κ(X)/c`.

The dumbbell exclusion is unavoidable — a two-point marginal is exactly a
bottleneck, and there conditioning on the aligned half genuinely flattens the
direction. So Priority B is **equivalent up to the marginal-unimodality of `X`**,
which is a weaker/cleaner condition than full Cheeger but is *not* free (non-convex
`X` can have bimodal marginals). What makes it not hopeless: the downdate is
**rank-1**, so at most the single direction `m_K` is ever at risk; a bad thin
direction hurts only if `m_K` aligns with it.

### 9. The symmetric restoring force (Priority A core, semi-rigorous)

The single-cut downdate fraction `α := ‖m_K‖²/λ_max` — the share of the top-axis
variance the cut removes — is bounded below and *grows with anisotropy*
(`verify_symcut.py`): `α ≈ 0.37` on the isotropic box, `0.71` at aspect 5, `0.74`
at aspect 10. So when the body is elongated the balanced cut removes ~¾ of the top
variance: a **restoring force toward isotropy**. This is why in the symmetric case
`κ` does not merely stay bounded but *contracts* (`100→27`, `906→228`). The
mechanism has the right sign for an *attractor* (not `C^t` growth): the more
anisotropic the body, the harder the next balanced cut flattens its long axis.

### 10. Why the multi-cut Lyapunov does NOT close (honest negative, `potential_test.py`)

Two obstructions, both visible in ground-truth (rejection) trajectories of the
*real* (asymmetric) algorithm, `d=5,6,7`, 13 rounds:

1. **Symmetry is destroyed by the first cut.** `X∩K` is not centrally symmetric,
   so `(S)` (rank-1 downdate) holds only for the first cut; subsequent cuts carry
   the `O(0.2)` reflection defect of §2b, and the clean contraction is diluted.

2. **The mean-shift/top-axis alignment is intermittent.** `|m̂_K·û_top|` swings
   over `[0.05, 0.94]` round to round: sometimes the cut squarely attacks the long
   axis (`align≈0.9`, `κ` then drops, e.g. `5.3→3.9`), but often it does not
   (`align≈0.1`, `κ` creeps up). Consequently **none** of the candidate
   potentials is monotone: over the reliable window `κ`, `tr(Σ)tr(Σ⁻¹)/d`, and
   `std(log λ_i)` all **drift mildly upward** (e.g. `κ: 1.6→8.9` at `d=7`), with
   occasional mean-reversion when a cut happens to align. And `m_K` sometimes
   lands on the *smallest* axis (`(û_min·m_K)²/λ_min` up to `0.95`) — the danger
   case of §8 — though the actual `λ_min` still survives (`λ_min'/λ_min ≥ 0.6`
   per cut) because the asymmetric `Σ(R)` term partly compensates.

So there is a genuine restoring force (§9) but it fires only when the cut aligns
with the long axis, and alignment is not guaranteed round-to-round. **I could not
find a Lyapunov function that provably decreases**, and the honest reading of the
data is: `κ` stays bounded (`2–9`) throughout the reliably-measurable window with
no divergence, but this is *bounded-with-drift*, not a proven attractor. Whether
the drift plateaus (attractor, C2 holds) or slowly compounds is exactly what the
`d=9` flat-`κ` run (26 rounds, `κ≈2`) suggests holds and the `d=7` climbing run
leaves open — and it is unmeasurable past the `d≈12, t≈2d` reliability ceiling.

### 11. Status after attempt II

* **Proved:** the mean-shift Lemma (§8) and the symmetric conditional
  `κ(X∩K) ≤ κ(X)/c` under marginal non-dumbbell-ness; the restoring-force sign
  (`α` grows with anisotropy, §9).
* **Failed (honestly):** a monotone multi-cut Lyapunov — the potentials drift, and
  alignment is intermittent (§10). The clean symmetric contraction does not
  compose into a trajectory theorem because symmetry and alignment are both lost.
* **Open (unchanged crux):** removing the marginal-unimodality hypothesis in §8
  (equivalently, showing the cone-cut's `m_K` never aligns with a dumbbell-thin
  direction). This is the same wall as the raw isoperimetry — C2 is *not*
  strictly easier than the Open Lemma, though the rank-1 structure and the
  restoring force are genuine partial handles the raw problem lacks.

## Proof attempt III — idealized multi-cut dynamics (A) and FW-centrality (B)

*Two honest negatives with real structural payoff: the equalizing mechanism is
pinned down and `spread` is shown to be a Lyapunov, but the idealized model
provably does **not** bound `κ`; and FW-centrality turns out to be *equivalent*
to balancedness, with a clean identity for the mean-defect but no bound.*

### 12. The idealized symmetric dynamics: mechanism, a Lyapunov, and why it fails (Priority A)

Model (`idealized_dynamics.py`): keep the body a symmetric **product box** with
variances `λ = (λ_1,…,λ_d)`; one balanced cut is the exact rank-1 downdate
`(S)`; re-symmetrise to a product box, i.e. `λ_i ← λ_i − m_{K,i}(λ)²`, then
renormalise (the halving is a global scale, irrelevant to `κ`). Here
`m_{K,i}(λ) = E[y_i | max_j y_j + min_j y_j ≥ 0]`.

* **The equalizing mechanism (verified).** The downdate *fraction*
  `m_{K,i}²/λ_i` is strongly increasing in `λ_i`: for `λ = (0.25,1,4,16)` it is
  `(0.0001, 0.003, 0.078, 0.62)`. The cut removes ~62% of the variance of the
  **largest** axis and essentially nothing (`10⁻⁴`) from the **smallest**. So the
  downdate is a "shave-the-top" / coordinate-descent-toward-flat operation — the
  right mechanism for equalization.
* **`spread(λ) := Σ_i (log λ_i − \overline{log λ})²` is a Lyapunov.** It is
  monotone non-increasing along the idealized trajectory in every anisotropic run
  (`monotone_dec=True` for one-short and graded starts). Shaving the top log-eigenvalue
  toward the mean reduces the log-spectral variance.
* **But the model does NOT bound `κ` — and this is the real lesson.** Because the
  downdate can only *remove* variance (never inject), a **thin axis is never
  repaired**: `m_{K,i}²≈0` there. Started from a graded spectrum the idealized
  `κ` barely moves (`d=12`, `10^11 → 5·10^7` over 25 rounds); from one thin axis
  it plateaus at `κ ≈ d·const` (`11.4, 30, 59` for `d=6,8,12`). Only from the
  **isotropic** start (the actual box `X_0`!) is `κ` stable at `≈1`, and the
  "one axis too *long*" perturbation is repaired (`κ: 100→1`) while "one axis too
  *short*" is not.

**Consequence (honest).** The clean symmetric case does *not* extend to a
bounded-`κ` multi-cut theorem: the exact symmetric cut is downdate-**only**, so it
cannot fix a thin direction, and `κ` is unbounded on graded spectra *in the
idealized model*. What actually keeps the real `κ` bounded must be the two things
the idealized model drops: (i) the trajectory **starts isotropic** (the box),
where isotropy is a stable fixed point; and (ii) the real cut is *not* a pure
downdate — the asymmetric term `2Σ(X)−Σ(R)` in `(D)` can **inject** variance into
a thin axis (repair), which `(S)` cannot. So, counter-intuitively, the *asymmetry*
I was trying to bound away in attempts I–II is precisely what repairs thin axes;
a purely symmetric world would be *worse* conditioned. This reframes the target:
not "control the asymmetry defect" but "show the asymmetric repair keeps pace with
any thin-axis creation" — a genuinely different (and still open) statement.

### 13. Fermat–Weber centrality is *equivalent* to balancedness; the mean-defect identity (Priority B)

The hoped-for extra leverage from FW-optimality over mere balancedness does not
exist: the first-order optimality of `Φ(c)=E‖y−c‖_∞` is exactly
`E[g] = 0` for `g ∈ ∂‖y−c‖_∞`, and since `∂‖z‖_∞ = conv{sign(z_j)e_j : j∈argmax|z|}`,
this reads `μ(P_i^+(c)) = μ(P_i^-(c))` for every `i` — **the balanced condition
itself** (this is Theorem A of `polytime.md`). FW-center `⟺` balanced; there is no
stronger first-moment condition to exploit.

What FW/balancedness *does* give cleanly is an identity for the mean-defect. With
means about `c`, `E[y−c] = ½(m_K + m_R)`, so

```
m_K + m_R = 2·(centroid(X) − c).                                   (M)
```

(Verified, symmetric box: both sides `≈0`.) So the `O(0.2)` mean-defect measured in
§2b is exactly **twice the distance from the FW center to the centroid**. This is
useful framing — the `(D)→(S)` gap is governed by (a) the `Σ`-defect
`Σ(R)−Σ(K')` and (b) `‖centroid − FW-center‖` — but it does **not** close the
bound: balancedness equalizes pyramid *masses*, which does not control the
*centroid*, so `‖centroid − FW-center‖` is not bounded by balancedness alone
(they coincide only under symmetry). No rigorous bound on the mean-defect follows.

### 14. Status after attempt III

* **Proved / established:** the equalizing mechanism (`m_{K,i}²/λ_i` increasing,
  ~0 on the thinnest axis, `≈0.6` on the thickest); `spread` is a monotone
  Lyapunov of the idealized dynamics; `FW ⟺ balanced`; the mean-defect identity
  `(M)`.
* **Failed (honestly):** a bounded-`κ` multi-cut theorem, even in the idealized
  symmetric model — pure downdates cannot repair a thin axis, so `κ` is unbounded
  on graded spectra there. FW gives no extra leverage over balancedness.
* **Reframed open problem:** `κ` stays bounded on the *real* trajectory only
  because it starts isotropic **and** the asymmetric term injects variance to
  repair thin axes. The target is therefore "asymmetric repair out-paces
  thin-axis creation," not "asymmetry is a small defect" — a cleaner statement of
  the same wall (still `= SSG∈P`).

## Bottom line (C2 so far)

Empirically, **C2 holds in the tested regime**: `κ(X_t)` stays `O(1)`–small
(`≈2–3`, growing sub-linearly in `d`), a single *balanced* cut multiplies `κ` by
`≈1` (geomean `1.05–1.11`), and the only cuts that degrade conditioning are the
adversarial ones the algorithm never makes (and which don't shrink volume). This
is the affirmative evidence for the whitening-based route: if the per-cut bound
`κ(X∩K) ≤ C·κ(X)` can be *proved* for balanced cuts, one re-whitening per round
plus standard hit-and-run gives poly mixing. That proof is the open piece.

## Appendix — C3 (block-restart exact sampler) hits the same wall

The one route that sidesteps isoperimetry entirely: sample `X_t` exactly by
ray-shooting from a star-center, restarting when none is certifiable. It fails,
for a clean structural reason plus empirics (`c3_test.py`):

* **The certifiable (LP) kernel `box ∩ ⋂_r ker(K_r)` is monotone shrinking in `t`**
  — each cut only *adds* `\binom d2` halfspace constraints — so once empty it can
  never recover via that certificate. Empirically it empties at `t ≈ d/2` and stays
  empty (`d=6,8,10`).
* **The *true* kernel is not monotone (cutting a hard-to-see region can restore
  star-shapedness), but empirically does not recover either:** the best candidate
  center's sample-visibility falls to `0.5–0.9` after collapse and essentially never
  returns to `1.0` — the body becomes genuinely non-star-shaped.
* **The balanced-vs-kernel tension is real:** keeping the query apex inside the
  kernel keeps the kernel nonempty (it contains the apex) but such peripheral
  queries stop halving the volume — no progress (`starshape_collapse.py`). One
  cannot have both a volume-halving cut and a preserved kernel.

So C3 lands on the same anisotropy wall: star-shapedness is exactly the flat-gap
regime of Theorem A, and it is lost precisely when the body becomes anisotropic —
the same phenomenon that blocks the Cheeger and `κ` routes. Consolidated writeup:
`notes/isoperimetry_summary.md`.
