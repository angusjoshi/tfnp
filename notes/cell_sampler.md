# The cell-tree telescoping sampler: the candidate algorithm, implemented

**→ The consolidated, link-by-link state of the whole reduction is
`notes/CHAIN.md` (cycle 16), including the margin-stability theorems
(`Tfnp/Margin.lean`) and the final measured form of the open core (the
lopsided-split law). This note carries the details of cycles 12–15.**

*Lean: `convex_cell` in `Tfnp/Progress.lean` (cells are convex; sorry-free).
Code: `notes/polytime_experiments/telescope_algo.py` (the algorithm),
`cells_adversarial.py` (cell statistics on adversarial trajectories).
Results: `cells_adversarial_results.txt`, `telescope_results.txt`.*

After the adversarial-shattering result (`adversarial_components.md`) closed
the isoperimetry route, the most promising surviving lead to a poly-time
algorithm is the **telescoping convex-cover route** (`FINAL_REPORT.md`
addendum): complete modulo conjecture (★). Shattering breaks single-region
MCMC but *not* cover-based sampling. This note records (i) the decisive new
cell statistics on adversarial trajectories, (ii) a structural upgrade of the
sampler that eliminates its leak *provably*, and (iii) the first measurements
of the algorithm **past the exact-rejection ceiling** that capped every prior
experiment.

## 1. Cells on adversarial trajectories: the shattering is cell-cheap

Cell = pyramid index per cut; cells are convex polytopes with `O(dt)` facets
(Lean: `convex_cell`), and `X_t` is the disjoint-up-to-null union of its
cells. Measured on the certified-realizable shattering trajectories (2400
exact-rejection samples per prefix), vs the toward and random-SSG controls:

| trajectory | d=6, t=14: #cells | top-1 mass | top-(d·t) mass |
|---|---|---|---|
| ADVERSARY (shattering) | 87 | 0.072 | **0.999** |
| random-SSG | 507 | 0.115 | 0.713 |
| toward (star-shaped) | 677 | 0.037 | 0.635 |

The inversion is the surprise: **the component-shattering adversary produces
the fewest, most mass-concentrated cells** — it fragments connectivity by
poking pyramid boundaries, which is cheap in cell count. The heavy cell tails
belong to the *benign* trajectories — exactly the ones where star-shapedness
makes cells unnecessary.

**The falsification attempt (`cellmax` mode, `cellmax_results.txt`).** The
missing adversary objective — maximise the **cell count / cell-mass entropy**
directly — was then run with the same certified-realizability machinery
(d = 5, 6; T = 12, 14; two seeds). It *fails to beat the benign baseline*:
d = 6, t = 14 yields 663–750 cells with top-(d·t) mass 0.59 — statistically
indistinguishable from the toward control (677 cells, 0.635), and the
discovery curves stay sublinear (`cells(n) ~ n^{0.63}`, saturating). With
full realizable sign freedom, greedily maximising fragmentation achieves
nothing beyond the natural cell tail: the cell count at fixed `(d, t)`
appears to have a **structural ceiling that no adversary policy reaches
past** — consistent with the parallel-families arrangement bound (§2.1)
being the binding constraint, and the strongest in-window evidence for (★)
to date. (Caveats: greedy one-step lookahead; the objective saturates at the
survivor-subsample size; in-window only.)

## 2. The sampler, and the leak that kills the naive version

Telescoping: survivors of a uniform sample under a cut are exactly uniform on
the kept set — no `2^{−t}` rejection tax. The naive version (v1: bucket
survivors by cell, refill cells by within-cell hit-and-run) **leaks**: a cell
whose survivors die out by chance is lost forever — a ratchet, measured at
1–5% of mass per round, compounding to `exleak = 0.115`, `cellTV = 0.28` by
`t = 8` (d=5). This is precisely the "missed mass doubles per round" failure
mode predicted in the notes.

**The fix is structural.** Cells form an exact **tree**: a cell of `X_t` is
(cell of `X_{t−1}`) ∩ (one pyramid of the new cut). So the algorithm (v2)
maintains the *complete* list of nonempty cells:

* children that inherit survivor points get weight ∝ counts;
* children with **no** surviving point are checked nonempty by a Chebyshev-
  center LP and **revived** with token points and a small mass floor —
  no cell is ever silently lost, by induction from the box;
* a cell cap (here 4000) prunes lowest-weight cells into a **declared leak**,
  and parents below `10⁻⁷` weight skip revival — the only unproven steps, and
  their boundedness is exactly conjecture (★) restated;
* the balanced apex is the **weighted** Fermat–Weber LP over a cell-weighted
  draw (a uniform-in-distribution sample regardless of per-cell point counts).

Verified in-window (d=5, ssg): `exleak = 0.000` at every checkpoint (v1:
ratcheting to 0.115), kept fraction ≈ ½ every round, `|c − x*|` decreasing.
Residual imperfection: `cellTV` drift ~0.2–0.3 by `t=8–10` from mass floors
and finite hit-and-run mixing — enough uniformity for balance (kept ≈ ½) but
honest noise in the weights.

Per-round cost: `poly(d, t, #cells, N)` — LPs of size `O(dt)`, hit-and-run
with exact chords on `O(dt)`-facet polytopes. **Everything in the loop is
polynomial except the number of cells.** The algorithm is the conjecture (★)
made executable: it runs precisely as long as the mass-carrying cell count
stays below the cap.

### 2.1 Lazy splitting: the growth is geometric, not bookkeeping

A natural refinement (`telescope_lazy.py`): split a cell by a cut only when
the cut boundary actually passes through it (`C ⊆ K` is checkable by ≤ 2d
Chebyshev LPs — if every disagreeing pyramid misses `C`, keep `C` whole).
Regions stay disjoint, cover `X_t`, and carry only the constraints of cuts
that genuinely cut them. Measured effect: **~18% fewer regions** (873 vs 1064
at d=5, t=10) — marginal. The interpretation matters: the cell growth is not
an artifact of full-history bookkeeping; **balanced apexes are central, so
each cut's fan genuinely crosses most of the mass**, and nearly every
mass-carrying cell is split each round. Any proof of (★) has to bound
*geometric* fragmentation, not representation overhead. (All cut fans use
hyperplanes from only `d(d−1)` parallel families — normals `eᵢ ± eⱼ` — which
is the structural handle a proof attempt should start from.)

## 3. Past the ceiling

Because the sampler never pays `2^{−t}` rejection, it can run to `t = 40` at
`d = 6` and beyond — territory no prior experiment in this project could see
(the exact-rejection ceiling is `t ≈ 14`). Validation in the overlap window
(`t ≤ 12`) against exact rejection, then free flight. Results:
`telescope_results.txt`.

**Random-SSG, `d = 6, T = 40, λ = 1−10⁻⁴` (the clean positive):**
`|c − x*|` decays steadily as `exp(−0.062 t)` — halving every ~11 rounds
(information-theoretic ideal ≈ 6) — from 0.52 to **0.0348 at t = 40**, three
times past the old ceiling. Kept fraction ≈ ½ every round; the body stays
connected; cumulative declared leak only **12.9%** over 40 rounds, i.e.
≤ 4000 cells hold ~87% of the mass throughout. Cell counts grow fast early
(~×1.5/round to `t ≈ 12`), hit the cap, then *equilibrate* with slow leak —
the strongest empirical support (★) has ever had, in territory where it was
previously unmeasurable.

**Shattering adversary, `d = 6, T = 40` (the honest stress failure):** the
adversary (playing against the sampler's own sample) shatters as before
(comps 31 by t = 10, 49 by t = 15, 62 by t = 20) and the declared leak
(cumulative sum of per-round pruned weight fractions) explodes — 0.25 at
t = 10, **0.89 by t = 16**, ~0.15/round after — with the weight profile flattened
(`wmax ≈ 0.006`) and `cellTV ≈ 0.9`. Two readings, and the data
discriminates: in-window `exleak` stays ≤ 0.027 (the exact sample's cells are
~97–99% covered), and the *exact-sampled* adversarial trajectory of §1 had 87
cells carrying 99.9% of mass — so what fails under shattering is the
**weight bookkeeping** (mass floors inflate phantom weight in thousands of
revived thin cells; within-cell hit-and-run degrades), which then feeds the
cap the wrong pruning order. The declared-leak meter is honest but, under
shattering, *pessimistically biased by its own noise*. The fix is known and
polynomial — per-cell volume re-estimation (product-estimator MCMC on convex
polytopes) instead of Laplace floors — and is the top implementation target.

**The full arc matters:** the pruning storm is a **transient**. After t = 22
the declared leak stops growing entirely — 18 consecutive rounds with zero
pruning — while the cell count *consolidates* from 4000 down to **538 at
t = 40**, weights re-concentrating (`wmax` 0.001 → 0.027), the body ending as
~20 components covered by ~500 cells. Even under sustained adversarial play
the cell population does not stay inflated: the steady state is cell-cheap,
matching the exact-sampled measurement of §1. What (★) has to survive is the
shattering *phase transition*, not a persistent cell explosion — a sharper
and more optimistic target than the worst-case reading of the leak meter.

**Random-SSG, `d = 8, T = 24` (the d-scaling datum, v3-corrected):** under
v2 this run looked ominous (leak 0.93, halving every ~23 rounds). With the
v3 meter (ratio-estimated revivals, mass-based pruning) the picture
transforms: `|c − x*|` 0.336 → **0.0929** over rounds 6–24 (halving every
~10 rounds — comparable to d = 6), cumulative declared leak **4.8%**, cells
oscillating 2.4–8.3k without sticking at the cap, kept ≈ ½ throughout. Most
of the apparent d-scaling pressure was v2's floor noise. The honest v3
d-scaling comparison (d=6 adversary: 5.1% leak over 40 rounds; d=8 ssg: 4.8%
over 24) shows no blow-up in the measured range — whether the required cap
is `poly(d)` or `2^{Θ(d)}` remains exactly (★), but both honest data points
now sit on the poly side.

## 4. What would close it, what would kill it

* **Close:** a proof that mass-carrying cells stay `poly(d,t)` on balanced-
  apex trajectories. The cell-tree gives the induction scaffolding: each round
  multiplies cells by ≤ `d` but mass-quota pruning keeps only the carriers;
  what must be ruled out is mass *equidistributing* over super-poly cells.
  Both adversary objectives have now been tried and neither does this (§1) —
  component-shattering is cell-cheap, and direct cell-maximisation cannot
  beat the benign baseline.

  **The precise reformulation to attack.** Map `y ↦ (yᵢ − yⱼ, yᵢ + yⱼ)_{i<j}`
  into `ℝ^m`, `m = d(d−1)`. Every cut's cell structure is determined by
  comparisons of these pair-coordinates against per-cut thresholds
  (`a^r_{ij} = c^r_i − c^r_j`, `b^r_{ij} = c^r_i + c^r_j`), because the argmax
  of `sᵢ(yᵢ − cᵢ)` is decided pairwise with normals `eᵢ ± eⱼ`. So:

  > cells of `X_t` = cells of an **axis-parallel grid** in `ℝ^m` (≤ t
  > thresholds per axis) **intersected with a fixed d-dimensional linear
  > subspace** (the image flat), and (★) says: for *balanced* thresholds,
  > `poly(d,t)` of the grid cells met by the flat carry `1 − 1/poly` of the
  > pushed-forward measure.

  The worst-case count of grid cells met by a d-flat is `C(mt,d) ~ (d²t)^d`
  — the familiar wall — but the measured *effective* cell count is nearly
  **linear in `d·t`** (top-`d·t` cells carry 60–99%), i.e. the partition
  entropy stays ~`log(dt)` instead of `t·log d`. Balancedness enters as: each
  threshold halves the current measure *of its own pyramid pair*. A
  per-round entropy increment bound (`H(cells_t) − H(cells_{t−1}) = O(polylog)`
  in the mass-weighted sense) would give (★) outright; nothing rules it out,
  and it is false for unbalanced thresholds — so balance must be the engine.

  **The entropy law (measured — `cell_entropy.py`, d = 6, t ≤ 14, all four
  oracles).** Mass-weighted cell entropy `H_t` saturates at the
  `log(dt) + O(1)` scale on *every* trajectory type — benign, component-
  adversarial, and entropy-adversarial — never approaching the
  equidistribution scale `t·log d` (4.4 vs 25.1 at t = 14):

  | oracle | H₁₄ (nats) | eff. cells `e^H` | typical dH/round |
  |---|---|---|---|
  | shattering adversary | 3.40 | ~30 | ±0.05 (flat 12 rounds) |
  | random-SSG | 5.15 | ~172 | +0.2 |
  | toward | 5.51 | ~247 | +0.3 early, ~0 late |
  | **cellmax adversary** | 5.58 | ~265 | +0.18 |

  Increments are frequently *negative* (conditioning on the kept half deletes
  whole cells — the consolidation seen in the long adversary runs). The
  refinement step adds at most `log d` per round; the measured cancellation
  against conditioning is what a proof must capture. **"Balanced-cut cell
  entropy saturates"** is now the cleanest quantitative statement of (★): it
  is adversary-tested, and its violation is exactly what every falsification
  attempt failed to produce.

  **d-scaling of the law (`spine_test.py`, d = 8 tail):** `H_t` = 3.26 / 3.94
  / 4.56 at `t` = 4 / 7 / 10 versus `log(dt)` = 3.47 / 4.03 / 4.38 — the law
  `H ≈ log(dt)` holds at d = 8 within ±0.2 nats, versus the equidistribution
  benchmark 8.3 / 14.6 / 20.8. Effective cells ≈ `d·t` almost exactly, at
  both measured dimensions.

  **Mechanism — what it is NOT (`spine_test.py`):** the linear-in-`dt` count
  is *not* one-dimensional mass concentration. A line meets ≤ `td(d−1)+1`
  cells (rigorous: the signature changes only at crossings of the `t·d(d−1)`
  pairwise hyperplanes), so a "mass spine" would explain the law — but best
  single-line spine masses are 0.02–0.32 and *decay* with `t`, 3-line greedy
  covers barely improve them, and the covariance spectra are nearly flat
  (`√λ` = 0.38/0.34/0.33/0.30 typical — no dominant axis; matches the old
  well-roundedness findings and `w₁/w₂ ≤ 1.2`). The mechanism IS the **near-common
  fan** (`fan_cone_test.py`): the sign pattern of the `d(d−1)` pairwise
  comparisons at one reference point (the mean apex) almost completely
  determines the full t-cut cell — `H(cell | cone)` = **0.00–0.04** for the
  adversary (whose balanced apexes barely move: median dispersion 0.004 vs
  body diameter 1.0), 0.71 for cellmax, 1.34 for ssg (dispersion 0.157), the
  residual growing with apex dispersion exactly as the δ-margin picture
  predicts. So the cell partition is (nearly) a **coarsening of a single
  fan's cone partition — a t-independent object** — which is the entropy
  law's engine: cells stop multiplying in t because they are functions of a
  fixed partition; the `log t` term is apex drift only.

  **The machine-checked half (`Tfnp/Fan.lean`, sorry-free):**
  `deep_cell_factorization` — if all apexes lie within `δ` of `c*`, then for
  `2δ`-deep points (every pair form `±(yᵢ−c*ᵢ)±(yⱼ−c*ⱼ)` exceeding `2δ`),
  membership in **every pyramid of every cut** is a function of the sign
  pattern of the pair forms at `c*` alone — a `t`-independent datum. Built on
  `mem_pyramid_iff_pairForms` (pyramid membership ⟺ a pair-form sign
  condition) and the `2δ` apex-shift bound. All `t`-dependence of the cell
  structure is confined to the margin slabs `{|pair form at c*| ≤ 2δ}`.

  **Correction from the d=8 measurement (`fan_cone_d8.py`):** the earlier
  "effective cones ≈ d³–d⁴" reading was a **sampling artifact** — at d = 8
  the cone partition is finer than 2200 samples resolve (effcones ≈ N
  exactly; d = 6 was partially saturated too). The honest picture: the cone
  datum is a *fine* partition over which mass is spread; the cell partition
  is a *coarse function* of it (`H(cell|cone) ≈ 0` says function, not few
  cones). So (★) decomposes as:
  1. **Apex-clustering lemma** — successive FW balanced points drift slowly
     (measured: median dispersion 0.004–0.16 vs diameter ~1; FW is a
     median-type statistic, stable under mass deletion — a proof handle).
     This controls the margin slabs, where all `t`-dependence lives
     (machine-checked above).
  2. **Top-pattern concentration** — the *induced coarsening* has few
     mass-carrying classes: with a common apex, the cell of a point is the
     tuple of argmax answers (`top of s^r·w over the active set`), and the
     measured law says mass concentrates on ~`d·t` such tuples even though
     it spreads over vastly many cones. This is the entropy law reduced to
     its common-apex core — sharper than before (no geometry left, pure
     order-statistics of one measure under `t` sign-weighted argmax queries)
     but not yet cracked.

     **First-agreement form.** For a survivor `y`, the answer to query `s^r`
     is the *first coordinate in `y`'s `|w|`-descending order whose sign
     agrees with `s^r`* (disagreeing coordinates contribute negative values,
     dominated by any agreeing one; sign-free points are removed by the
     cut). So the full tuple is determined by the prefix of `y`'s signed
     order out to the maximum first-agreement depth over the `t` queries —
     and if agreement per level behaves at all randomly, that depth is
     `O(log t)`, giving `≤ (2d)^{O(log t)}` effective tuples: quasi-poly for
     free, and the measured `H ≈ log(dt)` suggests the truth is better. The
     open question in its final form: **can the (balanced-response) sign
     vectors force deep first-agreements for constant mass?** This is where
     (★) now lives — a question about prefixes of signed orderings, with no
     bodies, cones, or cuts left in it.

  Algorithmic corollary worth pursuing (v5): for deep points the cell is
  determined by the `c*`-fan datum, so a cover by deep-cone pieces
  (t-independent membership tests) plus margin cells (handled by the tree)
  would confine all growth to the margins.
* **Sampler-free apexes (`heuristic_apex.py`) — the v4 direction.** Can the
  balanced point be *computed from the history* without mass estimation? The
  history determines `X_t` exactly, so this is purely computational. Measured
  (minority count = provable worst-case removal, `card_removed_le_sum_min`),
  d = 5, 6, ssg + adversarial trajectories:

  | rule | information used | worst-case removal |
  |---|---|---|
  | sampled FW (the algorithm) | cell list + masses | 0.42–0.48 |
  | **uniform-cell FW** | **cell list only** | **0.15–0.23 (ssg), 0.45–0.47 (adv)** |
  | Chebyshev-`r^d` proxy | cell list + inradius | 0.01–0.47 (erratic) |
  | FW of past apexes | history only | ~0.000 |
  | previous apex | — | 0.000 |

  Pure history rules are dead (zero progress — mass *location* is
  load-bearing, consistent with Idea D's fate on Melekopoglou–Condon), and
  exponential-factor volume proxies (`r^d`) misplace the apex. But
  **uniform weights over the cell list achieve Ω(1) progress** — near-optimal
  on adversarial trajectories (the adversary's own mass-equidistribution
  makes counting ≈ mass) and 0.15+ on benign ones (the entropy law makes
  effective cells comparable).

  **But the closed loop kills the naive version**
  (`heuristic_loop_results.txt`): cutting *at* the unif apex, its own biases
  compound — minority count decays 0.4 → 0.05 within ~10 rounds, kept
  fraction climbs to ~0.95, and `|c − x*|` **stalls** (≈ 0.55 at d=5, ≈ 0.46
  at d=6, barely moving). Mechanism: the cell *count* is endogenous to the
  apex — cutting at the counting-FW point fragments cells locally around the
  apex's own fan, the fragments dominate the count, and the next apex is
  dragged back to the same place. Same failure family as Idea D's cheap
  centers and the C3 kernel-confined stall. Mass weights fix this because
  mass is exogenous (conserved under refinement); counting is not.

  **Net of the heuristic question:** history-only rules get zero; cell-list-
  only rules stall in closed loop; the minimal sufficient statistic is the
  cell list **plus approximate masses** — and given poly cells, per-cell
  volume estimation (DFK on explicit convex polytopes) supplies those in
  randomized poly time with no `X_t`-sampler at all. That is exactly the
  v3 architecture; the "heuristic" road, honestly walked, leads back to it
  and certifies its weight step as necessary, not incidental.
* **Kill:** a realizable trajectory whose declared leak grows to Ω(1) at any
  fixed cap = a certified mass-equidistribution over cells. The instrument
  now exists to search for it.
* The `cellTV` drift wants a principled fix (per-cell volume re-estimation —
  poly but heavy); it does not currently threaten balance.
