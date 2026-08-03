# Convex-cell tracking for `ℓ∞`-contraction fixed points — design + obstruction

Goal (team-lead task): avoid sampling the non-convex `X_t` by tracking a **convex**
region `R_t ∋ x*` that shrinks, exploiting that the arrangement cell `Y* ⊆ X_t`
containing `x*` is convex. A poly-time convex tracker ⟹ `SSG ∈ P`.

**Headline.** The framework is *sound and correct* and reduces the whole problem to
a single, sharply-stated step — **identify which of the `d` pyramids `x*` lives in**
(the "dominant coordinate" `k* = argmaxᵢ sᵢ(x*ᵢ−cᵢ)`). That step is not a side
difficulty: it provably splits into exactly the two walls the project already knows.
Doing it by *queries* reduces to the `1/(1−λ)=2^poly` value-iteration wall (verified
identity, below). Doing it by *branch/prune or inner-approximation* reduces to the
`(d²t)^d` arrangement-cell-count wall (= Route Q / star-cover, open). The team lead's
`1/poly`-centerpoint relaxation is real but **helps balance, not convexification**, so
it does not move either wall. Net: convex-cell tracking is the cleanest *statement* of
the core, not a bypass. One genuinely-new, cheap experiment is specified (§7) that
measures the exact quantity this algorithm lives or dies on — the *dominant-coordinate
identification margin* — which no prior experiment measured.

---

## 1. The framework (sound, correct, poly per round except one step)

Sign-folded coords `wᵢ(y) = sᵢ(yᵢ−cᵢ)`. Verified facts (MEM/KER, hitrun.md, core_analysis §1):

* Kept half `K(c,s) = {y : maxᵢwᵢ + minᵢwᵢ ≥ 0} = ⋃_{k=1}^d P_k`,
  `P_k = {y : w_k + w_j ≥ 0 ∀j}` — a **convex** pyramid cone, apex `c`, ≤`d` facets.
* Cut validity (Lean `fixedPoint_mem_pyrUnion_apex`): `x* ∈ K(c^r,s^r)` every round.

**The pyramid containing `x*` is the argmax pyramid.** Let `k* = argmaxᵢ wᵢ(x*)`.
Then `x* ∈ P_{k*}`: cut validity gives `min w(x*) ≥ −max w(x*) = −w_{k*}(x*)`, so
`w_j(x*) ≥ −w_{k*}(x*) ∀j`, i.e. the `P_{k*}` facets hold. ∎ (Machine-checkable; this is
the convex-cell analogue of Theorem A restricted to one cone.)

**Algorithm (CELL-TRACK).** `R_0 = box`. Round `t`:
1. compute a convex-computable center `c` of `R_{t-1}` (centroid / analytic center — poly);
2. query `v = f(c)−c`, `s = ternarySign(v)`;
3. **identify** `k*` (the only non-poly step — §2);
4. `R_t = R_{t-1} ∩ P_{k*}^{s}(c)` — convex ∩ convex = convex, and `x* ∈ R_t` (cut validity).

Correctness: `R_t` stays convex, contains `x*`. Terminate when `diam(R_t) ≤ ε`
(computable for convex `R_t`). Every step is poly **except step 3**.

**Volume drop is not the problem.** With `c` = centroid of `R_{t-1}`, keeping the single
argmax pyramid `P_{k*}` keeps at most `≈ 1/(2d)` of the mass of a `c`-symmetric body
(half is removed by the union, and `P_{k*}` is ≈`1/d` of the kept union near the apex),
so `vol` drops by a large factor each round — far better than the `1/poly` the lead
allows. The relaxation is not needed for balance and does not touch the real obstruction.

---

## 2. The one obstruction: identify `k*` = dominant coordinate of `x*`

`k* = argmaxᵢ wᵢ(x*) = argmaxᵢ |x*ᵢ−cᵢ|` (the largest-gap coordinate; the sign folding
makes the argmax gap positive). We do not know `x*`. This is exactly Corollary-C's
dominant-coordinate problem (isoperimetry_summary), whose active set is `Θ(d)` (M1 note).

Two structural refinements that make the obstruction precise:

**(2a) `f(c)` estimates the gap with error `= λ·‖x*−c‖∞` (verified, hitrun.md:42-47).**
`vⱼ = (f(c)−x*)ⱼ + (x*−c)ⱼ` and `|(f(c)−x*)ⱼ| ≤ λ‖x*−c‖∞`. So `vⱼ` is a measurement of
the gap `(x*−c)ⱼ` with **additive error `λr`, `r=‖x*−c‖∞`**. The signal on the top
coordinate is `r`; the error is `λr`; the **margin is `(1−λ)r`**. Hence
`argmaxⱼ|vⱼ|` correctly identifies `k*` iff the top gap beats the runner-up by more than
`~λr` — a `(1−λ)` margin. This `(1−λ)` is exactly the SSG hardness knob (`γ→1 ⟺ λ→1`).

**(2b) # of "safe" pyramids = anisotropy.** `x* ∈ P_k ⟺ w_k(x*) ≥ −minⱼwⱼ(x*)`. So the
number of pyramids whose choice is *safe* (does not drop `x*`) is
`#{k : w_k(x*) ≥ −minⱼ wⱼ(x*)}`. If `min w(x*) ≥ 0` (all-toward = star / flat-gap regime,
Theorem A) **every** positive-`w` pyramid is safe — identification is free, tracker is
trivially poly. If `min w(x*) < 0` (some coordinate points away = anisotropic regime)
only the top pyramids are safe, possibly just one. **So the identification difficulty is
literally the star-vs-anisotropic axis the whole project turns on.** Mis-ID is fatal
(drops `x*`) exactly in the anisotropic regime.

---

## 3. Every resolution of step 3 reduces to a known wall

**(1a) Extra queries near `c` / map iteration → the `1/(1−λ)` value-iteration wall.**
To break a near-tie between the top two gaps to relative margin `m`, one must resolve
`x*−c` to accuracy `m·r`. Iterating the map, `f^{(k)}(c)` gives accuracy `λ^k r`, so
`k = log(1/m)/log(1/λ) = Θ(log(1/m)/(1−λ))` queries. Over `poly(d)` rounds this is
`poly(d)·log(1/ε)/(1−λ)` — **strictly worse than plain value iteration**
`log(1/ε)/(1−λ)`, and `2^poly` in the hard regime `1−λ = 2^{−poly}`. No query-based
identifier can do better: the oracle only reveals `x*` through `f`, and an adversary
(SSG instance) can place a near-tie between the two largest gaps, which is precisely the
anisotropic direction. **1a is not a bypass; it re-imports the `1/(1−γ)` factor the CLY
cutting-plane approach exists to avoid.**

**(1b) Branch over the `d` pyramids and prune → the `(d²t)^d` cell-count wall.**
Branching gives `d^t` sequences; keep only nonempty branches. But the number of
nonempty `⋂_r P_{k^r}` = number of full-dim arrangement cells of the `dt` cones =
`(d²t)^d` worst-case (core_analysis §4; star_cover §1a) — **exp in `d`**. Pruning to
poly needs a *positive* certificate that a branch does/doesn't contain `x*`; the only
poly certificate available (Idea-D Bellman certificate, `certify`) is *per strategy* and
does not map a geometric cell to a single strategy, nor certify "`x* ∉ this cell`"
without already knowing `x*`'s signs against the `O(d²t)` facet hyperplanes = the
identification problem. So safe capping at poly branches ⟺ realizable cell count is poly
⟺ the **Route-Q / star-cover open conjecture** `k(X_t)=poly(d,t)` (could not be proved;
worst case is a comb, exp-in-`d`). 1b ≡ Q.

**(1c) Monotone/topical structure → M1 (dead) / Tarski (open).** The SSG operator is
monotone + topical. Using order structure to pin the dominant coordinate is exactly M1's
convex order-interval / active-set-flatness program, measured DEAD on hard SSG
(signed-consistent rounds 0–9%, active set `Θ(d)`, m1_orderinterval.md). A monotone
branch-search for the cell also risks reducing to **Tarski fixed point**, whose best
bound is `O(log^d)` (Dang–Qi–Ye) — *not* poly in `d`, itself open. No fresh handle here.

---

## 4. Why the `1/poly`-centerpoint relaxation does not help

The relaxation weakens "exact balanced cut" to "remove `≥1/poly` fraction." That is a
statement about **balance**. The obstruction here is **convexification**: the valid cut
`K(c,s) ∋ x*` is a *union* of `d` pyramids, and the only halfspace/convex cut through `c`
that stays inside `K` and keeps `x*` is the single pyramid `P_{k*}` — selecting it needs
`k*`. There is **no free convex cut**: `K` is non-convex, so no halfspace through `c`
lies in `K` except degenerately, and `f(c)−c` is not an `ℓ₂`-separating direction for
`x*` when `λ→1` (its angular error is `O(λ)`). Grünbaum/center-of-gravity would finish
*if* we had a separation oracle for `x*`; we do not, for the same `(1−λ)`-margin reason
(§2a). So the relaxation lowers the bar on the wrong axis. (It *would* matter if the
trouble were an unbalanced but convex cut — it is not.)

---

## 5. What is provable / what stands

* **Framework correctness (provable, Lean-adjacent):** `x* ∈ P_{k*}` (§1), so CELL-TRACK
  with a correct `k*`-oracle is a correct poly-time algorithm. This isolates *all*
  difficulty into step 3.
* **Bounded-contraction regime (provable poly):** if `λ ≤ 1 − 1/poly`, single-query
  `argmaxⱼ|vⱼ|` identifies `k*` whenever the top-gap margin `> λ`-fraction; iterating
  `O(log d/(1−λ)) = poly` times removes ties ⟹ CELL-TRACK is poly. (But this regime is
  already poly by value iteration — no gain; stated for honesty.)
* **Star / flat-gap regime (provable poly):** if `min w(x*) ≥ 0` every positive pyramid
  is safe (§2b) ⟹ identification is free ⟹ poly. This is Theorem A in convex-tracking
  clothing — same regime, no new territory.
* **`Y*` is existential, not constructive.** Cut validity proves `x* ∈ Y*` *exists* but
  does **not name** `Y*`: naming it = knowing `x*`'s side of all `O(d²t)` facet
  hyperplanes = the identification problem. This is the precise gap in the lead's
  "`x*∈Y*` provable" — provable as existence, not as a constructible object.

## 6. Trap audit (task 3)

* **Circular (secretly needs `x*`)?** YES for the naive tracker: step 3 needs
  `argmaxᵢ|x*ᵢ−cᵢ|`. Approximating it via `f` reintroduces `1/(1−γ)`. Honest: the
  framework is circular unless `λ` is bounded away from 1.
* **Reduces to Tarski-poly (also open)?** The monotone branch route (1c) risks exactly
  this; Tarski is not known poly-in-`d`. Flagged, not relied on.
* **Reduces to star-cover / Q (open)?** The branch/inner-approx routes (1b, task 2) do.
* **Inner-approximation (task 2) — circular.** A max-volume convex `R ⊆ X_t` need not
  contain `x*` (if `x*` sits in a thin cell while a fat convex chunk lies elsewhere);
  forcing `x* ∈ R` = knowing where `x*` is. Using `Y*` instead = naming `Y*` = §5 gap.
  `vol(Y*) ≥ vol(X_t)/poly` holds iff cell count is poly = Q again. No escape.

## 7. Experiment to run (new; cheap; exact; measures the load-bearing quantity)

No prior experiment measured the **dominant-coordinate identification margin**, which is
exactly what CELL-TRACK lives on. This refines M1's factor-2 active set to the decisive
top-two margin and the safe-pyramid count.

Spec (fits the cap: d≤6, exact rejection / direct `x*`, N≤400 — most of it needs **no
sampling**, only `x*` and `f`, both exact):

* Instances: `make_ssg` hard spread-`x*`, `d ∈ {4,5,6}`, `1−γ ∈ {1e−2,1e−3,1e−4}`,
  seeds 0,1,2. Trajectory: FW/balanced centers `c^r` (light center est ok), `t` up to `2d`.
* Per round `r`, using the **exact** `x*` (solve the SSG) and one oracle value `f(c^r)`:
  1. `gap_i = |x*_i − c^r_i|`; sort. Report **top-two margin** `m = (g₁−g₂)/g₁`.
  2. `k* = argmax_i gap_i` (truth). `k̂ = argmax_i |f(c^r)_i − c^r_i|` (single-query
     estimate). Report **single-query ID success** `1[k̂ = k*]`, aggregate rate.
  3. **safe-pyramid count** `#{k : w_k(x*) ≥ −min_j w_j(x*)}` and `min_j w_j(x*)` sign
     (star vs anisotropic).
  4. iterations to lock: smallest `M` with `argmax_i|f^{(M)}(c^r)_i−c^r_i|` stable `=k*`
     (cap `M ≤ 50`). Report distribution vs `1−γ`.
* **Predictions / decision rule.**
  - If margins `m` are `≥ 1/poly` bounded below AND single-query ID rate `→ 1` AND
    safe-count `> 1` on realizable trajectories ⟹ **positive signal**: identification is
    easy on realizable instances, CELL-TRACK may be poly *in practice* — escalate to a
    proof attempt of "realizable margin `≥ 1/poly(d,t)`."
  - If margins collapse (near-ties), ID rate `< 1`, safe-count `= 1`, and lock-`M` scales
    like `1/(1−γ)` ⟹ **wall confirmed** on realizable instances; CELL-TRACK ≡ core, close.
  - Expectation from M1 (active set `Θ(d)` = many coords near the max ⟹ near-ties common):
    likely the second outcome, but this pins it exactly and cheaply, and the first
    outcome would be the most positive result in the project.

## 8. Verdict

Convex-cell tracking is the **cleanest correct reformulation** of the core: it collapses
the entire non-convex sampling problem to one crisp step — identify `x*`'s pyramid — and
proves that step is the *only* obstruction. But the step is not free: by queries it is the
`1/(1−γ)` value-iteration wall (verified margin identity §2a); by branch/prune/inner-approx
it is the `(d²t)^d` cell-count wall (= Q/star-cover, open). The `1/poly` relaxation eases
balance, not convexification, so it does not cross either. Provable wins are confined to
`λ`-bounded and star regimes (already poly). Not a bypass — but the experiment in §7
measures the exact realizable quantity (identification margin) that would decide whether
the query-side wall actually bites on realizable SSG, which is the one thing still worth
measuring here.

---

# PART II — Cover route (post ID-experiment pivot)

The §7 experiment was run (team lead): clean dichotomy — easy instances margin ≈0.2,
1-query ID-rate 0.73–0.85, lock-M=1; hard instances margin→0, ID-rate 0.05–0.36, lock-M
grows 40→99 as 1/δ grows 1e2→1e4. **Confirmed: single-pyramid CELL-TRACK ≡ core on hard
instances (the query-side value-iteration wall, §3/1a).** Naive tracker dead as predicted.

The pivot (team lead): sigma-scaling proved `X_t = ⋂` of `σ` monotone up-sets and measured
the star-cover number `k ~ linear in σ` (`σ=8 → k≈10`, not `2^8`). Since a `k`-piece cover
gives a sampler with NO mixing, COVER all `k` relevant cells and we never need to know
which pyramid `x*` is in. Below: the cover-construction feasibility (gap B).

## 9. The right construction: arrangement-cell enumeration (beats greedy star-cover)

The proposed greedy-submodular star-cover (`star_cover.md §2`) has a real defect the lead
flagged: its coverage functional `F(Z)=vol(⋃ star(z))` is a **volume over `X_t`**, which
is exactly the exp-thin quantity Karp–Luby cannot compute (`core_analysis §2`); the
experimental greedy runs on a *rejection-sampled cloud*, and rejection sampling `X_t` is
`2^t` — not a poly algorithm, only a diagnostic. So greedy-star-cover does not, as stated,
give a poly *constructor*.

**A strictly better construction avoids volumes and stars entirely — use the CONVEX cells.**
Verified fact (`star_cover §1a`): the facet hyperplanes `{w_i^r = ± w_j^r}`, `H=O(d²t)`
total, cut space into arrangement cells; inside each cell every `K_r` is a *single
halfspace* (argmax/argmin coord of `w^r` is fixed), so `X_t ∩ cell` is a **convex
polytope**. Cells of a hyperplane arrangement are **disjoint** and partition space.
Therefore

> **`X_t = ⊔_{j=1}^{k'} C_j`, a DISJOINT union of `k'` convex polytopes** (`k'` = # nonempty
> cells of the arrangement lying in `X_t`; `k' ≥` guard number `k`, both conjecturally poly).

This decomposition makes all three sub-tasks clean:

**Sub-task 2 (sampleability) — SOLVED, provable, no obstruction.** Each `C_j` is a convex
polytope with `≤ H + t` explicit linear facets. Convex ⟹ trivially star; any interior
point (one LP) is a kernel ⟹ exact ray-shooting, and uniform sampling is poly (KLS
hit-and-run, or grid/rejection in the polytope). No virtual constraints, no Markov mixing
question. The kernel-emptying that killed C3 is irrelevant: we never need a *global* star
center, each cell is convex on its own.

**Sub-task 3 (union sampling) — SOLVED, and Karp–Luby is not even needed.** The cells are
**disjoint**, so `vol(X_t) = Σ_j vol(C_j)` and uniform sampling is: estimate each
`vol(C_j)` by Dyer–Frieze–Kannan (poly, relative `1±ε`), pick `j ∝ v_j`, sample uniform in
`C_j`. **This dodges the thinness barrier**: the barrier (`core_analysis §2`) is
catastrophic *cancellation* in `vol(box) − vol(cones)`; here we take a **SUM of positive
terms**, so relative `(1±ε)` per cell gives relative `(1±ε)` for `vol(X_t)` — no `2^t`
precision. Explicit enumeration converts the exp-precision *difference* into a poly-accuracy
*sum*. (This is the key point the greedy/Karp–Luby framing missed.)

**Sub-task 1 (constructibility) — poly-time given poly cell count, via reverse search.**
Do NOT sample to build the cover; enumerate cells combinatorially. The full arrangement's
cell-adjacency graph is **connected**, so Avis–Fukuda / Sleumer **reverse-search cell
enumeration** lists every nonempty cell of the `H`-hyperplane arrangement in
`O(#cells · H · LP(H,d))` time — **poly per cell**, single seed (box-center cell), no
sampling, exact (LP feasibility, no precision issue). Filter each enumerated cell by
`X_t`-membership (kept side of all `t` cuts — poly per cell). Output: the explicit list
`{C_j}`. **Cost = poly(d,t) · (# nonempty cells of the arrangement).**

**Identification is now genuinely dodged.** Global enumeration lists ALL cells and samples
`X_t` uniformly via the disjoint-sum — we never ask which cell `x*` is in, never seed from
`x*`, never iterate the map. The lead's "cover all `k`, don't identify" is realized exactly,
and correctly (uniform over all of `X_t`, so the FW/balanced center from the existing LP is
the true one). The value-iteration wall (Part I) is bypassed.

## 10. Where the poly-ness now rests — the single surviving condition (honest)

The entire route is poly-time ⟺

> **(★) the number of nonempty cells of the facet-hyperplane arrangement of `X_t` is
> `poly(d,t)` on realizable FW-balanced trajectories.**

This is exactly the open star-cover-type conjecture, now in its cleanest form (a pure
COMBINATORIAL COUNT, not an analytic isoperimetric inequality and not the identification
margin). Status:
- Worst case is `(d²t)^{d}` = exp-in-`d` (`star_cover §1a`, comb-of-pinwheels), unproven on
  realizable trajectories, unmeasurable past `d≈6` (the recurring ceiling).
- The lead's new `k ~ poly(σ)` (with `σ ≤ #rounds = poly`) is **supporting evidence** but
  (i) `k` is the guard number, a LOWER proxy for the cell count `k'` the runtime actually
  needs — `k' ≥ k` must ALSO be measured; (ii) it lives in the `d≤6` window that cannot see
  a `2^d` jump — same blind spot that made every prior empirical signal suggestive-not-
  decisive.

**So the honest status: the cover route is a genuine improvement — it removes TWO
obstructions (the identification/value-iteration wall AND the thinness/isoperimetry wall)
and concentrates ALL remaining risk in the single count (★).** It does not prove `SSG∈P`;
it reduces `SSG∈P` (on this method) to (★). No circularity: enumeration needs no knowledge
of `x*` (global reverse search from the box-center cell). No reduction to Tarski. The one
thing that can still kill it is (★) being false on realizable trajectories = the exp-in-`d`
arrangement blowup that `star_cover §5` could neither prove-poly nor refute.

**Two possible extra obstructions checked and cleared:**
- *Enumeration reachability:* fine — the full arrangement is connected, one seed suffices;
  we do NOT need to seed each component of `X_t` (which would reintroduce a coarse
  identification), because we enumerate the full arrangement and filter.
- *Seeding `x*`'s component:* not needed under global enumeration (only needed by the
  cheaper "track one component" variant, which DOES reintroduce a coarser component-ID and
  is why global enumeration is the right choice).

## 11. Experiment to run — measure (★) directly (cheaper & sharper than greedy-`k̂`)

Measure the exact runtime-determining quantity `k'` = # distinct nonempty cells, not the
visibility guard number. It needs NO visibility/segment test — each sample's cell is just
its sign vector against the `H` facet hyperplanes.

Spec (cap: d≤6, exact rejection, N≤400 — here `N` up to ~400 rejection points per body):
- Instances: realizable SSG (`make_ssg`, spread-`x*`) + a topical contraction, `d∈{3,4,5,6}`,
  `t` up to `min(2d, 12)` (push `t` high to get `σ` up to ~12; `σ ≤ t`).
- Per body: rejection-sample `M≤400` points of `X_t`. For each point `y` compute its **cell
  signature** = `( sign(w_i^r(y) − w_j^r(y)) )` over all rounds `r` and pairs `i<j` (i.e.
  which coord is argmax/argmin of `w^r` at `y`). `k'_lb` = # distinct signatures observed
  (exact lower bound on cell count; no visibility test, no volume).
- Also log: `σ` (# distinct sign vectors `s^r`), the guard number `k̂` if cheap (for the
  `k' ≥ k` relation), and # connected components of the sampled cloud (union-find on
  segment-adjacency) as a coarse component count.
- **Plots / decision:** `k'_lb` vs `σ` (linear/poly ⟹ (★) supported; super-poly ⟹ danger)
  and the decisive `k'_lb` vs `d` at fixed `t/d`. **Mild-in-`d` ⟹ cover route alive and now
  the leading candidate; visible `2^d`-type jump ⟹ (★) false, route dies with the rest.**
- Prior (honest): `k'_lb` will track `σ` in-window (consistent with lead's `k~σ`), but the
  `d`-scaling is unmeasurable past `d≈6`, so expect *suggestive, not decisive* — the same
  ceiling that limited κ and `k`. The value of this run over the greedy-`k̂` run: it measures
  the RUNTIME quantity `k'` exactly and cheaply (signatures, not volumes/visibility), and
  ties it to `σ` and `d` in one plot.

**Stronger than any experiment — the real target:** prove (★), `k'(X_t) = poly(σ,d,t)`, for
FW-balanced realizable trajectories. Candidate lever: `X_t = ⋂_{ℓ≤σ} U_ℓ` (σ monotone
up-sets); bound the cells of an intersection of `σ` up-sets of the special `max w+min w≥0`
type. If each up-set contributed `O(d)` new cells non-interactingly, `k'=O(σd)`; the open
crux (as in `star_cover §1c`) is whether the infinite cones make far cells SPLIT
(interaction) on realizable trajectories. This is the same terminal open crux, but now it is
the *only* thing between this construction and `SSG∈P`, with identification and isoperimetry
both removed.

---

# PART III — Guard/star-cover route: the samplability gap, and the fix (convex cover)

Cell-count experiment result (team lead): `k'` (cell count) is **exp/large** — `k'_lb`
keeps rising with sample size (`d=5`: 148→293→466→716 at nsamp 200→2000; `d=6` ~exp).
So Part II's arrangement-cell **enumeration is dead** (`k'` is the real `(d²t)^d`). BUT the
**guard number `k`** (star-cover to 99.9% vol) stays small (`~σ`, 1–11, flat in `d`): one
guard sees across many cells. Lead's proposal: use the small-`k` GUARD star-cover, ray-shoot
within each `star(z) ⊆ X_t` to sample+measure it (dodging thin rejection), Karp–Luby over
the `k` pieces. Below: this has a **real gap**, and the fix names the correct quantity.

## 12. The gap: star-pieces are poly-MANY but NOT poly-SAMPLABLE

`k~σ` (poly-many guards) is **necessary but not sufficient**. The lead's sub-tasks 2&3
require sampling and measuring each `star(z)` in poly time. `star(z)` is star-shaped but
**non-convex** (it is a union of `~k'/k` = exp-many convex cells). Every way to
sample/measure a star-shaped body hits a wall:

* **Radial ray-shoot (the proposed method) is exp-in-`d` — the curse of dimensionality,
  true even for a cube.** `vol(star(z)) = (1/d)∫_{S^{d−1}} R(u)^d du`, MC over directions.
  The estimator `R(u)^d` has relative variance `E[R^{2d}]/E[R^d]² − 1`, which is **exp-in-`d`
  whenever `R_max/R_min > 1`** (any non-spherical body). For the unit **cube from its
  center** `R` ranges `[½, √d/2]`, so `R^d` spans a factor `d^{d/2}` and radial-MC needs
  `exp(d)` samples — despite the cube being perfectly conditioned (`κ=1`). So a small
  covariance condition number does **not** rescue it. Empirically `X_t`'s radial function is
  "wildly spiky, max/median 60–320" (`isoperimetry_attack §3.5`) — even worse. Radial
  ray-shoot is fine for **membership** and for `R(u)` in **one** direction (both poly), but
  **not** for volume or uniform sampling. The `1/poly`-TV relaxation does not help: you
  cannot estimate an exp-relative-variance mean to `1/poly`, nor beat exp-small radial
  rejection acceptance, with poly samples.
* **Hit-and-run inside `star(z)`** would be poly **only** if `Cheeger(star(z)) ≥ 1/poly` —
  but `star(z)` is non-convex, so this is exactly the **isoperimetry wall** we were trying
  to leave. Convex-body mixing (KLS) does **not** apply to star-shaped bodies.
* **Cell-decomposition of `star(z)`** is poly per cell but `star(z)` has **exp-many** cells
  (just measured). Exp.

So the guard route **relocates the same three walls** (exp-radial-curse / isoperimetry /
exp-cells) from `X_t` onto `star(z)` — it does not escape them. Karp–Luby (sub-task 3) is a
valid poly *wrapper*, but its premises (per-piece uniform sample + volume) are the wall. Net:
covering was never the hard part; **sampling a non-convex piece is**, and star-pieces are
non-convex. We came full circle: sample non-convex `X_t` → cover by star pieces → sample
non-convex `star(z)`.

**The clean dichotomy (the crux, stated sharply):**
> poly-**MANY** pieces (guards, `k~σ`) are each non-convex ⟹ not poly-samplable;
> poly-**SAMPLABLE** pieces (convex cells) are exp-**many** (`k'` exp).
> A working sampler needs pieces that are BOTH poly-many AND convex.

## 13. The fix: cover by poly-many CONVEX pieces (the right quantity is CC, not k, not k')

Only **convex** pieces are poly-samplable (hit-and-run/KLS provably mixes; DFK volume;
membership) — and with convex pieces every wall is genuinely dodged (no radial curse:
hit-and-run not radial; no isoperimetry-of-`X_t`: each piece convex ⟹ Cheeger ≥ 1/diam by
KLS; no thinness: DFK relative-accurate + Karp–Luby ratio `1/CC` not `2^{−t}`). So define

> **CC(`X_t`) = convex cover number = min # of convex bodies `Q_j ⊆ X_t` with `⋃Q_j = X_t`.**

Then the algorithm WORKS and is poly **iff CC = poly**: hit-and-run-sample each `Q_j`,
DFK-measure it, Karp–Luby over the `CC` overlapping convex pieces (expected trials ≤ CC),
near-uniform on `X_t`, feed the existing FW-center LP. Identification, thinness, and
isoperimetry all removed.

**CC is the Goldilocks quantity, and it is exactly what was NOT measured:**
`k (guard) ≤ CC ≤ k' (cells)`, i.e. `σ ≲ CC ≲ exp`. (Convex ⟹ star, so a convex cover is a
star cover ⟹ `CC ≥ k`; cells are convex ⟹ `CC ≤ k'`.) The lead measured the two ends —
`k~σ` (too weak: star pieces unsamplable) and `k'` exp (too strong: convex *cells*, but a
convex piece may span many cells by crossing interior non-reflex `{w_i=w_j}` boundaries).
**CC in the middle is the true runtime driver and is unmeasured.**

## 14. Honest status — two open pieces, both = the same terminal crux

* **(i) Is CC poly?** Unproven; lies strictly between the small guard number and the exp
  cell count, so neither measurement settles it. Plausibly poly (a convex piece absorbs many
  cells), but could be exp.
* **(ii) Poly-time CONSTRUCTOR (even given CC poly).** Min convex cover is NP-hard in
  general; we need a poly *heuristic* constructor. The natural one is **inductive**: keep a
  convex cover of `X_{t−1}`; a new cut `K_t` intersects each convex `Q_j` with `box ∖ d`
  cones, splitting `Q_j` into `O(d)` convex sub-pieces. This grows the cover by a factor
  `O(d)` per round ⟹ `CC ≤ d^t` = **exp** — UNLESS splits do not proliferate (pieces from
  different cuts don't multiply). That "additive-not-multiplicative piece growth" is
  **exactly the non-interacting-reflex-ridge crux** (`star_cover §5`) — the same terminal
  open question, now phrased for convex pieces: *do FW-balanced cuts keep convex-piece growth
  additive `O(dt)` rather than multiplicative `d^t`?*

So the corrected route is the cleanest yet — it removes identification, thinness, and
isoperimetry-of-`X_t`, and concentrates everything into one quantity CC and one crux
(additive vs multiplicative piece growth). It still does **not** prove `SSG∈P`; it reduces
it (on this method) to **CC(`X_t`) = poly** on realizable trajectories, which is the same
sign-pattern/non-interaction crux the whole project reduces to — but now attached to the
*only* functional (convex-cover number) for which sampling is actually poly.

## 15. Experiment — measure CC (the true driver), bracketed and split-rate

The lead measured `k` and `k'`; measure the middle quantity CC and the per-cut split factor.
Spec (cap: d≤6, exact rejection, N≤400):
- Instances: `make_ssg` spread-`x*` + one topical, `d∈{3,4,5,6}`, `t` up to `min(2d,12)`.
- **CC upper bound (greedy convex cover):** rejection-sample `M≤400` pts of `X_t`. Greedily
  build convex pieces: pick an uncovered point `p`, grow a convex region `Q` = convex hull of
  a set of sampled points all of whose pairwise segments lie in `X_t` (add points greedily
  while `conv(Q∪{q}) ⊆ X_t`, checked on the sample by segment-membership); remove covered
  points; repeat. `CC_ub` = # pieces to cover 99% of the cloud. Report `CC_ub` vs `σ` and —
  decisive — vs `d` at fixed `t/d`.
- **Split rate:** track `CC_ub(X_{t}) / CC_ub(X_{t−1})` per round. **≈ constant (additive,
  →+O(d)) ⟹ CC poly, route alive; growing ~`d`× (multiplicative) ⟹ CC exp, route dies.**
- Bracket check: confirm `k ≤ CC_ub ≤ k'` on each body (sanity).
- Prior (honest): `CC_ub` likely tracks `σ` in-window (like `k`), but the split rate and the
  `d`-scaling are the deciders and are unmeasurable past `d≈6` — same ceiling, so expect
  *suggestive not decisive*. The unique value: `CC` is the FIRST quantity measured that is
  simultaneously the true runtime driver AND attached to a poly-samplable piece type.

**Bottom line for the lead:** the star/guard cover as proposed is not poly (star pieces are
non-convex ⟹ ray-shoot is exp-radial, hit-and-run is isoperimetry). The route survives only
if reformulated with **convex** pieces, whose count `CC` is unmeasured and whose poly-time
construction is the additive-vs-multiplicative crux. Redesign delivered on that basis; the
sole open piece is `CC = poly` (⟸ sigma-scaling would have to bound convex-cover, not guard,
number).

---

# PART IV — CC measured `~σ`; the two proofs (constructor CLOSED mod CC-poly; CC-poly = crux)

Team lead measured CC via greedy convex cover (exact rejection, SSG `t=2d`): **CC `≈ σ`**
(`d=3`: 1,1; `d=4`: 3,11; `d=5`: 2,6), flat-ish in `d`, bracketed `k ≤ CC ≤ k'`, and
greedily constructed in-window. So a small convex cover both exists and is findable in the
measurable window. The two asks: (1) prove `CC ≤ poly(σ,d)`; (2) prove a poly constructor.

## 16. The constructor: the thinness/mixing chicken-egg is RESOLVED by induction

`core_analysis §3` dismissed telescoping: "sample `X_{t−1}`, keep the ½ in `K_t`; acceptance
½ per step ⟹ `2^{−t}` overall (compounds); needs replenishment = MCMC-within = mixing."
**The convex cover IS the replenishment-without-mixing** — this rescues telescoping exactly.

**Inductive sampler/constructor (poly per round given CC poly, no `x*`, no rejection of the
box, no Markov mixing):**
- *Invariant:* after round `t−1`, hold a convex cover `{Q_j} ` of `X_{t−1}`, size `CC_{t−1}`,
  each `Q_j` a convex polytope.
- *Sample `X_{t−1}`:* Karp–Luby over the convex `Q_j` (hit-and-run per piece = poly by KLS
  since **convex**; DFK volumes; membership) — poly given `CC_{t−1}` poly. **No mixing on the
  non-convex body**; convex pieces need no isoperimetry.
- *Cut:* FW/balanced center `c^t` from those samples (existing LP); oracle → `K_t`;
  `X_t = X_{t−1} ∩ K_t`.
- *Replenish `X_t`:* keep the `X_{t−1}` samples lying in `K_t` (membership poly). Acceptance
  `= vol(X_t)/vol(X_{t−1}) = ½` (balanced-cut halving, proven `hitrun §2.2`). **`½`, not
  `2^{−t}`** — because we resample from `X_{t−1}` (via its cover), never from the box. This
  is precisely the "replenishment" §3 said was missing; it is poly, not MCMC.
- *Rebuild cover of `X_t`:* greedy convex cover on the `O(poly)` fresh `X_t` samples → `{Q'_j}`,
  size `CC_t`.
- Base: `X_0 = box`, cover `{box}`, `CC_0 = 1`. No circularity; `x*` never used.

**So the thinness barrier AND the isoperimetry/mixing barrier are BOTH genuinely removed**
(the two walls that killed every earlier sampler): thinness by per-round `½` acceptance off
the maintained cover; mixing by convex pieces (KLS, no Cheeger of `X_t`). The entire sampler
is poly **iff** two things hold each round: **(G1)** `CC_t` stays poly, and **(G2)** greedy
actually finds an `O(CC_t)`-size cover from poly samples.

**(G2) honest status:** greedy convex-cover has **no clean approximation guarantee** —
"grow a convex piece" is not submodular max-coverage, and maximum convex subset is NP-hard.
So (G2) is not proved; it is empirically fine (`~σ`). A guaranteed fallback exists but is
weaker: the **pure-piece cover** `X_t = ⋃_{(k_r)∈[d]^t} Q_{(k_r)}`, `Q_{(k_r)} = box ∩ ⋂_r
P_{k_r}^r` (each convex, explicit polytope, constructed with NO sampling), whose *nonempty*
pieces are reverse-search-enumerable — but their count is `~k'` (exp). So the guaranteed
constructor gives exp size; the poly-size constructor is greedy, which lacks a guarantee.
**(G2) is a real, separate open gap from (G1).**

## 17. `CC ≤ poly(σ,d)`: what is provable, and the exact reduction to the crux

Using `X_t = ⋃_{(k_r)} Q_{(k_r)}` (distribute `⋂_r (⋃_k P_k^r)` over the unions):

**Provable bounds.**
- **`CC ≤ d^t`** (each of the `d^t` assignment pieces is convex). Trivial, exp.
- **Same-orientation reduction (clean, using sigma-scaling).** For rounds sharing sign
  vector `s`, put `W_i := s_i y_i` (common coords); then round `j`'s pyramid `k` is
  `P_k^j = {W_k + W_i ≥ a_k^j + a_i^j ∀i}`, a **translate of the fixed cone**
  `C_k = {W_k + W_i ≥ 0 ∀i}` (facet normals `e_k+e_i`, independent of `j`). Hence
  `⋂_{j: same s} P_k^j = {W_k + W_i ≥ max_j(a_k^j+a_i^j) ∀i}` is **a single cone** per `k`.
  So the `m` same-`s` cuts, restricted to a **fixed argmax coordinate `k` across those
  rounds**, collapse to `d` convex "pure" cones — *no multiplication within an orientation
  if the argmax is stable*. This is the structural reason CC can be `≪ d^t`.
- Consequently **`CC ≤ d^σ`** *iff within every orientation the same-`s` cuts are argmax-
  nested* (one effective cut per orientation). Still exp in `σ`, and far above the measured
  `CC~σ`.

**The exact gap (= the crux).** `CC ~ σ` (linear, `≪ d^σ`) requires that the needed pieces
are those where the argmax coordinate `k_r` is **stable across rounds**, and that
cross-orientation assignments do **not** multiply. Formally: a point `y∈X_t` needs a convex
piece only if *some* single assignment vector `(k_r)` with `y∈Q_{(k_r)}` is shared by a
`1/poly` fraction; the blow-up happens exactly when the **argmax/dominant coordinate switches
across rounds** (the anisotropic/blind-axis regime — the SAME object as the Part-I
identification wall, `condition_transfer`'s "conditioning = sign-pattern trajectory", and
`star_cover`'s reflex-ridge interaction). **I cannot prove `CC ≤ poly(σ,d)`**; it is
equivalent to "the dominant-coordinate assignment is stable / low-complexity across rounds on
realizable balanced trajectories," which is the project's terminal non-interaction crux.

**Sharpest recurrence (the measurable form).** With a cover `{Q_j}` of `X_{t−1}`,
`X_t = ⋃_j (Q_j ∩ K_t)` and `Q_j ∩ K_t = ⋃_k (Q_j ∩ P_k^t)` (≤ `d` sub-pieces). Let
`straddle_t = #{j : Q_j meets ≥ 2 pyramids of K_t}` (the pieces the new pinwheel actually
splits). Then
> **`CC_t ≤ CC_{t−1} + (d−1)·straddle_t`.**
**Additive (`CC = O(dt) = poly`) iff `straddle_t = O(poly)` each round** (equivalently the
new cut's reflex ridge crosses only poly existing pieces — pieces far from `c^t` are sliced
by a single pyramid boundary = a hyperplane locally, so stay convex; only pieces meeting the
round-`t` ridge split). Multiplicative (`straddle_t = Ω(CC_{t−1})`) ⟹ `d^t`. This is the
precise, directly-measurable crux — and it is exactly `star_cover §1c`'s "do the infinite
cones split far lobes" question, now on convex pieces.

## 18. Verdict + the experiment that matters

**Closed this round:** the constructor's sampling problem — the thinness AND mixing walls are
removed by the inductive convex-cover replenishment (`§16`); this is a genuine advance (it
resurrects telescoping, which `core_analysis §3` had dismissed). **Not closed:** `(G1)`
`CC=poly` (= the terminal crux, `§17`) and `(G2)` greedy attains poly size (separate, no
approximation guarantee). Both are honestly open; neither is fabricated-provable.

**Experiment (measure the recurrence, not just the ratio):** the ratio `CC_t/CC_{t−1}`
conflates; measure **`straddle_t` directly** = # existing cover pieces the new cut splits into
≥2. Spec (cap d≤6, exact rejection): build `{Q_j}` for `X_{t−1}` (greedy on rejection
samples, as lead already does); for the new cut `K_t`, count `#{j : Q_j` contains sample
points in ≥2 different pyramids `P_k^t}`. Report `straddle_t` vs round, vs `d`, vs `σ`.
**`straddle_t = O(d)` flat in round ⟹ additive ⟹ `CC=O(dt)` poly ⟹ (G1) supported;
`straddle_t` growing with `CC_{t−1}` ⟹ multiplicative ⟹ dies.** Also log whether the argmax
coordinate of the cover-piece centroids is stable across rounds (the `§17` mechanism). Same
`d≤6` ceiling caveat, but `straddle_t` is the cleanest single number that decides (G1).

**Net:** the convex-cover sampler is now a *complete poly algorithm modulo the single
combinatorial bound `CC=poly`* (and greedy's size, G2). Identification, thinness, and mixing
are all removed. `SSG∈P` on this method ⟺ `CC(X_t)=poly(σ,d)` on realizable balanced
trajectories ⟺ `straddle_t=poly` per round — the terminal non-interacting-reflex-ridge crux,
supported by `CC~σ` empirics but unproven and unmeasurable past `d≈6`.

---

# PART V — `straddle≈CC` kills maintain-and-split; reframe CC → `k_eff` gives a FREE constructor

Team lead measured `straddle_t ≈ CC_{t−1}` (a constant fraction of pieces straddle each new
cut: `straddle 1,5,7,7` vs `CC 3,5,9,11`, `d=4`). So the recurrence `§17` is **multiplicative
(`≈ d·CC` → `d^t`)** — the **maintain-and-split constructor DIES**. But **fresh** greedy
re-cover of `X_t` still gets `CC~σ`. Why the gap: split sub-pieces from *different* parents
**merge** in a fresh cover; split-and-accumulate cannot merge across parents. So the working
constructor is my `§16` telescoping SAMPLE step (which stands) + a **fresh** re-cover — not
maintain-and-split. Also (lead): sigma-scaling's `deep ⟹ kernel` sub-lemma is **empirically
refuted** (fraction 0.0 at `d=6`), so the `σd²` decomposition is gone; `CC≤poly` needs a new
argument. Asks: (a) prove fresh-greedy poly on these bodies; (b) a non-greedy poly constructor.

## 19. The right move: don't minimize a convex cover (NP-hard) — cover the VOLUME by frequent CELLS

Both asks presuppose constructing a *minimum-ish* convex cover, which is **NP-hard** (max
convex subset / min convex cover) and has no approximation guarantee — the wall (a)/(b) hit.
**Sidestep it entirely.** We only need an **approximate** sampler (TV `1/poly`) ⟹ we only
need to cover **`(1−1/poly)` of the VOLUME**, and we can use the **cells** (assignment
polytopes) directly — no merging, no greedy, no NP-hardness.

**Definition.** Assignment cell `Q_v = box ∩ ⋂_r P_{v_r}^r` for `v∈[d]^t` (the dominant-coord
`argmax_i|w_i^r|` vector); cells are **disjoint & convex**, `X_t = ⊔_v Q_v` over nonempty `v`.
Let `p_v = vol(Q_v)/vol(X_t)` and define the **effective cell count**
> **`k_eff(δ) = #{ smallest set of cells whose total mass ≥ 1−δ }`** (cells holding the bulk).

**The FREE constructor (no greedy, no merging, no NP-hard step):**
1. Draw `N=poly` uniform samples of `X_t` via the `§16` telescoping step (sample `X_{t−1}`
   through its stored cover, keep the `½` in `K_t` — poly, acceptance `½`, no mixing).
2. For each sample compute its assignment vector `v` (`d·t` argmaxes). **Group** samples by `v`.
3. Output the distinct cells `{Q_v}` seen — each an explicit convex polytope. `≤ N` pieces.
4. Sample `X_t` (approx-uniform) = volume-weighted pick among the `{Q_v}` (disjoint ⟹ no
   Karp–Luby) + per-cell hit-and-run. Feed the FW-center LP.

**This closes (G2)** — construction is just *grouping samples*, trivially poly, zero
NP-hardness. **It also revives Part II**: Part II died because *enumerating all* `k'` cells is
exp; here sampling **surfaces only the frequent cells**, never the exp tail.

## 20. The exact guarantee (occupancy bound) — poly iff `k_eff` is poly

**Lemma (coverage).** With `N` iid uniform samples of `X_t`, the expected uncovered mass is
`E[U] = Σ_v p_v(1−p_v)^N ≤ Σ_v p_v e^{−N p_v}`. If the top `m` cells hold mass `≥1−δ` and
each has mass `≥ (1−δ)/m`, then `N = O((m/(1−δ))·log(m/δ'))` samples cover `≥ 1−δ−δ'` of the
mass whp. **So the sample-and-group constructor is poly ⟺ `k_eff(1/poly) = poly`.** (Honest
converse: if the mass is spread over `k'` cells of near-equal size, `N∼k'` = exp — the bound
is tight, so `k_eff` poly is genuinely necessary, not an artifact.)

**`k_eff` is the correct operative quantity — strictly better than CC or `k'`:**
- vs `k'` (total cells, exp, measured `148→716`): `k_eff ≤ k'` and can be `≪` — the tail of
  rare cells inflates `k'` but carries negligible mass. **`k'` growing with sample size is
  NOT evidence against `k_eff`** (the lead's `k'_lb` growth is the rare tail; `k_eff` is the
  saturating head).
- vs CC (min convex cover, `~σ`): CC needs NP-hard merging to *construct*; `k_eff` comes with
  the **free** sample-and-group constructor. `k_eff` may exceed CC (cells don't span), but it
  is poly-constructible, which CC is not. For a poly *algorithm*, `k_eff` poly is what matters.

## 21. Why `k_eff` poly is plausible — the persistence reframing (new, honest)

`crux_experiment.md` found **blind long axes PERSIST** (`d6 s1`: 5 rounds, `κ 3→15.6`) — the
finding that **killed the κ route** (non-persistence lemma false). **The same persistence
HELPS the cover route:** the dominant coordinate `argmax_i|w_i^r|` persisting across rounds
means the assignment vector `v` is *stable / low-complexity* along the high-mass region ⟹ the
bulk of the mass sits in **few** cells ⟹ `k_eff` small. So the phenomenon the conditioning
route feared is exactly what the cover route wants. This is a genuine reframe (not a proof):
the two routes have **opposite** dependence on axis persistence, so the empirical persistence
is *positive* evidence for the cover route while it was negative for κ.

**Still unproven.** Per-region persistence does not formally bound the *number of distinct*
high-mass assignment vectors (two regions can differ in one coordinate). So `k_eff = poly` is
not proved — it is the crux, now in its cleanest and most measurable form: **is `vol(X_t)`
concentrated in `poly(σ,d)` assignment cells on realizable balanced trajectories?** This is a
volume-concentration statement (not an NP-hard cover-minimization, not an isoperimetric
inequality, not the identification margin) — the most tractable phrasing the crux has had.

## 22. Verdict + experiment

**Closed this round:** (G2) — the constructor is now a free sample-and-group (no greedy, no
NP-hard merging, no maintain-and-split); combined with `§16` telescoping the sampler is a
complete poly algorithm **modulo one condition**. **Reframed:** the condition is `k_eff=poly`
(volume concentration), replacing the NP-hard CC and the exp `k'`; it is measurable and
self-constructing. **Not closed:** `k_eff=poly` itself (the crux), and (a) fresh-greedy's
optimal size is moot now — we don't need optimal, we need `k_eff` poly.

**Experiment — measure `k_eff` saturation (the deciding quantity):** on realizable SSG
(`d∈{3,4,5,6}`, `t≤min(2d,12)`, exact rejection), draw increasing `N` samples; per `N` report
`k_eff(0.01)` = # distinct assignment cells needed to cover 99% of the *sampled mass* (sort
cells by sample-frequency, count until 99%). **Key plot: `k_eff` vs `N` — does it SATURATE
(poly, cover route alive) while `k'_lb` keeps growing (rare tail)?** Then `k_eff` vs `d` at
fixed `t/d` (the usual decider), and `k_eff` vs `σ`. Also log dominant-coordinate persistence
(avg # rounds the argmax coord is stable in the high-mass cells) to test the `§21` mechanism.
`k_eff` saturating small ⟹ the sample-and-group sampler provably works in-window; growing with
`N` or exp in `d` ⟹ the mass is genuinely spread ⟹ route dies. Same `d≤6` ceiling caveat.

**Bottom line for the lead:** stop trying to construct a *minimum* convex cover (NP-hard —
that's why (a)/(b) resist). Use `k_eff`: sample-and-group is a *free* poly constructor, and
the whole algorithm is poly iff `vol(X_t)` concentrates in poly cells (`k_eff=poly`) — a
measurable volume-concentration crux, supported by the (κ-killing) persistence, cleaner than
everything prior, but still unproven and ceiling-limited.

---

# PART VI — `k_eff` refuted; structured merge = the reflex-PIECE wall; TERMINAL read

Team lead ran the `k_eff` experiment: **NEGATIVE.** `k_eff` (cells for 99% of MASS) =
`60/141/250` at `d=4/5/6` (`N=2000`), **still growing with `N`**, and `k_eff/k'_lb =
0.80–0.97` ⟹ `k_eff ≈ k'`, NOT `≪`. **The mass is spread over ~all cells; no small
saturating head.** So `§19`'s merge-free constructor produces `~k' = exp` pieces. This
honestly resolves the CC-vs-`k_eff` tension: `CC~σ` is small **only** because greedy MERGES
many cells into few convex pieces; merge-free gives the large un-merged count. Both directions
fail: merge-free = poly-time but exp-many; merge-to-`σ` = small but NP-hard.

## 23. Direct answer: is a poly structured-merge possible? **No — it is the reflex-PIECE wall.**

The natural structured merge is: **group cells by reflex-facet signature and merge across
interior (non-exposed) reflex boundaries.** Work out its exact geometry:

- The genuine non-convexities of `X_t` are the **reflex facets** = the *argmin-switch*
  hyperplanes (removing the convex cones `C_k={w_k+w_j<0 ∀j}` makes the boundary concave-
  from-inside; `min` is the sole source of reflexivity). By `star_cover §5` these number
  **`O(d²t)` — additive**, which is exactly the order-statistic structure the lead hoped to
  exploit. So the *hyperplanes* are few and structured. **Good news, but not enough.**
- A convex piece may cross a reflex hyperplane **where that hyperplane is interior to `X_t`**
  (not exposed as `∂X_t`), and is blocked **only where the hyperplane is exposed** as actual
  boundary. **Whether a given reflex hyperplane is exposed is position-dependent** — it
  depends on whether the *other* `t−1` cuts' infinite cones have already removed that locale.
  So mergeability is a **global, position-dependent** predicate, not a local order-statistic
  test.
- The number of convex pieces = the number of **reflex PIECES** (maximal regions between
  exposed reflex facets) = **`(d²t)^{d−1}` worst case** (`star_cover §5`), because the
  infinite cones from different cuts *split far pieces* (§1c reflex-ridge interaction). So:

> **Structured merge ⟹ count = reflex-piece count = `(d²t)^{d−1}` (exp in `d`).** The
> order-statistic structure makes reflex *hyperplanes* additive `O(d²t)` but the *pieces*
> multiply through cone interaction — the exact `additive-hyperplanes / multiplicative-pieces`
> gap `star_cover §5` identified as terminal. Any "merge cells sharing an argmax/argmin-run"
> rule collapses to computing this piece count = min-convex-cover = NP-hard = the realizability
> core. There is no order-statistic shortcut, because exposure (hence mergeability) is set by
> the *global interaction* of all `t` cones, which is the very object carrying the hardness.

So the lead's two named candidates are both the same wall: "merge cells sharing an argmax-run"
= reflex-piece grouping = `(d²t)^{d−1}`; and it is not poly.

## 24. My honest read: **TERMINAL** (with a precise statement of what stands)

The convex-cover route has now been pushed to the same wall as every other route, and the
convergence is exact — it lands on `star_cover §5`'s reflex-piece count `(d²t)^{d−1}`, which
is the `FINAL_REPORT §4` open target `k(X_t)=poly`. Both constructive directions are dead:
- **merge-free** (cells / reflex-cells): poly-time, but exp-many pieces (`k_eff ≈ k'`,
  refuted §22–23);
- **merge** (to `CC~σ`): small, but NP-hard / position-dependent = reflex-piece wall (§23).

The existence of a small cover (`CC~σ`, empirical, in-window, `d≤6`) genuinely **does not**
yield a poly-time construction — from either side. This is the terminal state; I recommend
consolidation. One optional cheap residual check remains (measure `k_eff` under the
*reflex-facet* signature `sign(w_i^r+w_j^r)` rather than the argmax signature), but the
prediction from `star_cover §5` is that it too is exp (reflex pieces = `(d²t)^{d−1}`), so it
is low-value.

**What genuinely stands and is worth banking (durable, not defeated):**
1. **`§16` telescoping via convex-cover replenishment** — a real advance: it removes BOTH the
   thinness barrier (per-round acceptance `½` off the maintained cover, never off the box) AND
   the isoperimetry/mixing barrier (convex pieces, KLS), resurrecting the telescoping sampler
   `core_analysis §3` had dismissed. It reduces the **entire** open problem to a single crisp
   algorithmic question: *is there a poly-time-CONSTRUCTIBLE poly-size convex cover of `X_t`?*
   This is the cleanest statement of the wall and belongs in `FINAL_REPORT` alongside the Q
   framing (it is the same wall — reflex pieces — reached through sampling rather than
   art-gallery guards).
2. **Part I identification characterization** — single-pyramid tracking `≡` the `1/(1−γ)`
   value-iteration wall (verified margin identity + the lead's dichotomy experiment).
3. **The CC → `k_eff` → reflex-piece reduction chain** — a clean localization: the operative
   quantity is the reflex-piece count; `CC` (min convex cover) is NP-hard to construct and
   `k_eff` (volume concentration) is exp, so neither the optimization nor the sampling
   shortcut escapes; all three are functionals of the one sign-pattern/cone-interaction object.

**Net:** `SSG∈P` on this method `⟺` poly-time-constructible poly-size convex cover of `X_t`
`⟺` reflex-piece count `= poly` on realizable balanced trajectories = `star_cover §5` /
`FINAL_REPORT §4`'s terminal target. The convex-cover route is a *fourth independent path*
(after Cheeger, `κ`, guard-count) to the identical reflex-piece wall — strong confirmation the
wall is the real core, and, via `§16`, the sharpest algorithmic phrasing of it. Terminal.
