# HANDOFF: the SSG ∈ P campaign — complete state for the next agent

*Single entry point. Chronology: `RESEARCH_LOG.md` (cycles 1–29). Reduction
chain with per-link status: `CHAIN.md`. This file is the consolidated
inventory: read this first, then CHAIN.md, then the cycle logs as needed.*

## 0. Goal, bar, and honest status

**Goal:** worst-case poly(d, log 1/ε)-time ε-fixed points of ℓ∞-contractions
⟹ `SSG ∈ P` (classical Condon reduction).

**SOTA bar (checked, arXiv:2604.01006):** `(log 1/ε)^{O(√d log d)}` time.
Quasi-poly (`2^{polylog}`) would beat it decisively for SSG. On *queries*,
CLY v2 already has `O(d log 1/ε)` — matched by this repo's formalization
(`cly_query_complexity`), nothing to claim there. `polytime.md`'s table cites
CLY v1 and is outdated on this point.

**Status:** NOT solved. The open core after 36 cycles is a cumulative form
of the original conjecture (★): *balanced-cut dynamics creates only
polynomially many tracked (mass ≥ η) cells/lineages* — measured `O(d·t)`
under every adversary built; proved for two strata; resistant to every
reformulation because the missing ingredient is a genuinely new dynamical
inequality, not bookkeeping (see the churn no-go, §4 — quantified by the
cycle-31 stacking probe: geometric containment is total while actual births
are O(d)/round, so no static bound exists). Cycle 31 fenced re-stratification:
tie sets of 4δ-robust mass are trajectory invariants at every depth
(`Tfnp/Restrat.lean`), the robust-2-simple ledger is scale-free O(d²T), and
births are confined to the 4δ collar of the tie front. Everything around
the core — geometry, combinatorics, algorithms, instruments — is done and
machine-checked.

## 1. Machine-checked theorems (Lean 4, all sorry-free; axioms only propext / Classical.choice / Quot.sound)

Pre-campaign (already in repo): `cly_query_complexity` (O(d log 1/ε)
queries, full CLY Theorem 1), `exists_balanced_point_box` (Brouwer-free
balanced points via ℓ∞ Fermat–Weber), `fixedPoint_mem_pyrUnion_apex` (apex
cuts valid for every c ≠ x*), star/kernel theorems (`starshaped_of_toward`,
`starshaped_of_kernel(_family)`, `starshaped_of_single_sign`), halfspace/d≤2
convex regime, `PolyTime.endToEnd` scaffold (correctness + poly time given a
sampler hypothesis).

This campaign, by file:

**`Tfnp/Progress.lean`** — the progress–convexity trade-off:
`card_removed_le_sum_min` (worst-case removal = minority count; balanced ⟺
maximal), `exists_sign_vacuous_cut`, `apex_between_of_two_sided`,
`cut_inter_subset_halfspace` (2 live coords ⟹ convex round),
`exists_three_pyramid_centroid` (any point = centroid of 3 pyramid points),
`eq_univ_of_convex_of_three`, `le_of_quasiconcave_majorant` (**no
quasiconcave surrogate exists — kills all first-order/analytic-center
methods**), `exists_injective_of_convex_cover` (cover number of one cut =
exactly d), `apex_mem_pyramid`, `convex_pyramid`,
`cut_inter_convex_isPreconnected` (**apex-in-convex-lobe can't be split**),
`convex_cell` (cells are convex polytopes).

**`Tfnp/Realizability.lean`** — realizability is finite (ℓ∞ hyperconvexity /
coordinatewise McShane): `realizable_of_pairwise` (**a query history is
realized by an actual contraction iff the finite pairwise inequalities
hold**), `realizable_cuts_retain_fixedPoint`. Consequence: per-coordinate
sign menus; in the hard regime (λ = 1−2^{−poly}) a correctly-played
adversary has full sign freedom (magnitude policy matters — see
adversarial_components.md §2).

**`Tfnp/Fan.lean`** — `deep_cell_factorization` (**apexes within δ ⟹ the
entire cell record of 2δ-deep points is a function of the pair-form sign
pattern at one reference — a t-independent datum**), `mem_pyramid_iff_pairForms`.

**`Tfnp/Margin.lean`** — `pyr_stable_of_gap` / `pyr_unique_of_gap` /
`mem_pyrUnion_iff_of_gap` / `mem_pyr_iff_of_gap` (**argmax index+sign stable
under apex perturbation < half the top gap; cut membership = one equation**),
`cell_eq_of_onedeep` (**1-deep mass: ≤ 2d cells for the whole trajectory,
t-FREE**), `pyr_index_mem_pair_of_2simple` (pair confinement),
`tie_of_mem_two_pyr` / `one_sided_of_kept` (**each cut leaves the surviving
measure one-sided at every pair, off ties**), `deep_extinction` (a gap-deep
point cannot survive a sign flip at its coordinate),
`double_disagree_kills` (graduating a 2-tie pattern requires the
double-disagree round, which kills the whole pattern).

**`Tfnp/Walk.lean`** — `ncard_range_signPattern_le` (**walk lemma: sign
pattern vs t thresholds ≤ 2t+1 values**), `pair_membership_iff`
(**pair-record: a 2-simple point's membership decided by ONE linear form**).
Composite (paper, from these): **2-simple survivors ≤ 2d(d−1)(2t+1) =
O(d²t) cells** — matches the measured law.

**`Tfnp/Shed.lean`** — `abs_pairComb_sub_le` (marching bound: apex step δ
moves every pencil offset ≤ 2δ), `shed_slab` (**shed pieces are marching
slabs**), `pencil_energy` (**Σ pencil motions² = 4k‖u‖₂² exactly**),
`pyr_index_mem_of_mset` (**m-set confinement: deep strata split only by
their own tie set's forms**).

**`Tfnp/Restrat.lean`** (cycles 31–32) — `collar_of_near_top` (**the
transition atom: ties have no cold entries** — within 2δ of top at any apex
within δ ⟹ within 4δ at the reference), `tie_mem_pair_of_robust` /
`pair_invariant_of_robust` (**4δ-robust 2-simple mass cannot change its tied
pair; record = ONE form's walk, scale-free**), `tie_mem_mset_of_robust` /
`mset_invariant_of_robust` (**tie sets are robust trajectory invariants at
every trichotomy level; strata migration only via each level's 4δ collar**),
`gap_lipschitz` (**top-gaps are 2-Lipschitz in the apex: the [2δ,4δ] band
cannot be jumped — every tie entry costs ≥ 1 round of collar residence**).

**`Tfnp/Annealed.lean`** (cycles 33–35) — `annealed_half_kept` (**the
annealed half-kept law: a strict-argmax point is kept by exactly half of
the balanced sign vectors** — the measured flux law κ ≈ ½ as a theorem in
the annealed model; complementation-involution proof, no binomials),
`annealed_survival_pow` (**gap-deep throughout ⟹ survives `a` independent
balanced cuts for exactly a 2^{-a} fraction of sign tuples** — expected
deep-lineage lifetime 2 rounds; survival × doubling a martingale; the
survival half of lemma (A1)), `strict_argmax_of_one_sided` (**the
straddle–dodge dichotomy: non-straddling front cells have strict argmaxes
⟹ die at ½/round — dodging is a straddler-only privilege**, cycle 35), `both_agree_keeps` (**agree–agree
rounds keep the whole pattern cell split in two — the birth event;
completes the machine-checked straddler offspring table (2,1,1,0) at ¼
each**, cycle 36).

## 2. Assembled results (paper-level; every ingredient Lean-checked unless noted)

* **The trichotomy:** 1-deep ≤ 2d cells (t-free); 2-simple ≤ O(d²t);
  m-simple ≤ O(d^m t^{2(m−1)}) per level (paper bookkeeping).
* **The 2-simple shed ledger (cycle 26):** total 2-simple shed ≤ O(d²tη).
  **CAVEAT (cycle-29 audit): proved in the fixed-reference/fixed-dispersion
  regime only; cross-round re-stratification bookkeeping NOT done.** The
  shattering adversary (tightly clustered apexes, mass measured 2-simple,
  m₃ ≤ 0.001) is the regime where it honestly applies — that instance class
  (which refuted isoperimetry) is covered end-to-end.
* **Lineage lemma:** a φ-split child has the split offset as a φ-extent
  boundary ⟹ ≤ 1 mid-extent crossing per (lineage, pencil); re-entry (bulk)
  splits are once-per-coupon; only marching shaves shed.
* **Deep-creation-at-front:** top flips require top-gap ≤ 2δ
  (`pyr_stable_of_gap`) ⟹ deep lineage creation only at the moving tie front.
* **Marginal-density engine (imported, not Lean):** μ_t|cell is uniform on
  a convex polytope ⟹ marginals 1/(d−1)-concave (Borell–Brascamp–Lieb) ⟹
  slab mass ≤ d·(s/w)·cell mass: wide cells bleed ≤ 2dδ/w per shave.
* **Shed accounting:** shed ≤ O(d·t·L·η), L = tracked lineages ever.
  L ≤ poly ⟹ (SHED) ⟹ v3 correct+poly ⟹ SSG ∈ P. (One direction only —
  the ⟺ claim of cycle 28 was WITHDRAWN in the cycle-29 audit.)

## 3. Measured laws (instruments in `notes/polytime_experiments/`, results in `*_results.txt` there)

* **Entropy law:** H(cells) ≈ log(dt) ± 0.2 at d = 6 AND d = 8, all four
  oracle types (`cell_entropy.py`, `spine_test.py` tail). Effective cells
  ≈ 2–3·d·t (the additive law).
* **Multiplicity law:** splits are mult-1 dominant; new tracked cells
  O(d)/round; shattering adversary: 30/30 crossed, 30/30 mult-1, 0 new
  (`split_multiplicity.py`).
* **Flux law:** per-depth-class kept fraction κ(m) ≈ ½ ∀m; depth
  distribution ~stationary (`depth_flux.py`).
* **Depth dynamics:** adversarially excitable to ~d (depthmax reached
  D = 5.99) but MEAN-REVERTING limit cycle ≈ 3; 55-round marathon: three
  excursions, leak 14.7% total (`depth_rate.py`, `depth_horizon_results.txt`).
* **Margin mass ≈ 1** at drift scale — thin-margin hopes dead; gap
  distribution and drift CO-SCALE; the measure collapses onto the tie
  complex (`margin_mass.py`).
* **Multi-tie profile:** shattering adversary → pure 2-simple (m₃ ≤ 0.001);
  cellmax climbs (m₃ → 1, m₄ → 0.5) yet its cells never explode
  (`multitie_mass.py`).
* **Shed/leak:** ~0.3%/round under every adversary, including at maximal
  tie depth (v3 runs).
* **Adversarial cells:** shattering trajectories are cell-CHEAP (87 cells /
  99.9% mass at d=6,t=14); the dedicated cellmax adversary cannot beat the
  benign baseline (`cells_adversarial.py`, `cellmax_attack.py`).
* **Fan-cone:** H(cell | cone) ≈ 0 (cells are a coarse function of the
  one-reference pair-form pattern); **the d=8 "cone count" was a sampling
  SATURATION ARTIFACT — do not cite effective-cone counts**
  (`fan_cone_test.py`, `fan_cone_d8.py`).
* **Stacking law (cycle 31, `stacking_probe.py` → `stacking_results.txt`):**
  geometric containment is TOTAL (`geoKmax ≈ #mc`: the worst pencil's offset
  sits mid-extent of ~every tracked cell, every round, every oracle) while
  actual per-pencil crossings ≤ 27 and per-pencil tracked births ≤ 7, flat
  in t — **the (ZONE) bound must be dynamical; the geometry gives none.**
  All observed pair changes pass through the 4δ collar (viaCol = 1.000, the
  Restrat theorem's prediction). Shattering adversary: robust mass → 0.998,
  pair changes ≡ 0, births = 0. ssg/cellmax/randbal: robust 0.00–0.36 (the
  collar carries the bulk — the margin-mass law per-point).
* **Collar-ledger law (cycle 32, `collar_ledger.py` →
  `collar_ledger_results.txt`):** births 100% front-confined (667/668 at
  gap₂-front lineages); tie entries ~once per lineage (no oscillation churn
  under any oracle); shattering adversary completely static (0 births/12
  rounds). **L decomposes: ~60% front births + ~40% EMERGENCES**
  (sub-threshold cells re-crossing η by renormalization growth — a fully
  kept untracked cell doubles conditional mass per round). Emergence
  anatomy: detection mass < 2η (91–94%), but incubation ages reach 11
  rounds under cellmax — growth with memory, not flicker. Rates O(d)/round
  everywhere.
* **Heuristic apexes:** history-only rules: ZERO worst-case progress;
  cell-list-only (uniform-over-cells): Ω(1) open-loop but STALLS closed-loop
  (endogenous-counting mechanism); minimal sufficient statistic = cell list
  + approximate masses (`heuristic_apex.py`).
* **Apex paths:** benign = directionally coherent; cellmax can curve them
  (kills "line epochs" as a free property; survives as an algorithmic
  choice with open feasibility) (`apex_path.py`).

## 4. Negative results — the DO-NOT-PROVE list (each paid for)

1. **Isoperimetry / Cheeger / connectivity: REFUTED REALIZABLY.** Certified
   adversaries shatter X_t into mass-comparable components (17–23 at d=5–6,
   density-verified; d=3 also shatters). h(X_t) = 0 on realizable
   trajectories. Single-region MCMC is dead. (`adversarial_components.md`.)
2. **Pointwise depth bounds / conditional balance as exact law: REFUTED**
   (depthmax excursions to D = 5.99; κ(m) = ½ only ± 0.15 and transiently
   violated).
3. **Thin margins:** margin mass ≈ 1. **FW-drift ≤ spread/d:** false (d=1
   median check; measured ratio ~1). **Line-spine:** refuted.
   **Cone-count:** artifact.
4. **Quasiconcave surrogates:** impossible (Lean theorem). **Convex cover
   of one cut:** exactly d pieces (Lean).
5. **History-only heuristic apexes:** zero progress. **Cell-list-only:**
   closed-loop stall.
6. **Pure ledgers (combinatorial or mass-based) for the deep stratum:
   VACUOUS** — exponential create-die churn is consistent with every
   derivable inequality; balance adds nothing per-round (informal but
   thorough map, cycle 28).
7. **The repo's query bound does not beat SOTA** (CLY v2 = O(k log 1/ε)
   already).
8. Older campaign negatives (cycles 1–10 era): κ-conditioning ≡ open lemma;
   well-roundedness insufficient; Idea-D cheap centers die on
   Melekopoglou–Condon; M1/Corollary-C dead; C3 kernel collapse.

## 5. The algorithm and instruments (all in `notes/polytime_experiments/`)

* **`telescope_algo.py` (v3)** — the candidate algorithm: exact cell tree
  with Chebyshev-LP revival (coverage exact by induction; v1's 1–5%/round
  leak ratchet documented and fixed), ratio-estimated revival weights,
  mass-based pruning, weighted FW apex. Validated in-window
  (exleak = 0.000). Runs: d=6 T=40 ssg: |c−x*| 0.52 → 0.0348, leak 12.9%;
  d=8 T=24: 0.0929, leak 4.8%; adversary marathons ≤ 15%/55 rounds. Oracle
  modes: ssg / toward / adversary(components) / cellmax / depthmax / randbal.
* **`adversary_game.py`** — certified-realizable adversaries (menus via
  exact interval arithmetic; magnitude policy matters: MAG ~ 1e-4 keeps
  menus full at λ = 1−1e-9).
* **`exact_geom.py` + `certify_disconnect.py`** — exact-rational
  certification: Fraction cell trees with EXACT partition identities
  (verified through 12 rounds, root = box = 1), exact Farkas (≤4-row),
  certified 0.41-balanced realizable trajectories at d=3; slab-separation
  certificate implemented (no single slab found at seed 4, T ≤ 12 —
  piecewise certificate needed). PARKED, below the SOTA bar, but this is
  the verification tooling a paper will want.
* `telescope_lazy.py` (lazy splitting: only ~18% savings — growth is
  geometric, not bookkeeping).

## 6. The open core, precisely, with its proved fences

> **(★ / L):** balanced-cut dynamics creates only poly(d, t) tracked
> (mass ≥ η) cells/lineages over a trajectory. [Cumulative form of the
> original conjecture; measured O(d·t) under every adversary.]

Proved fences: 2-simple creations ≤ O(d²)/round (fixed-δ regime);
robust-2-simple lineage cells ≤ O(d²T) SCALE-FREE (cycle 31: tie-set
invariance kills re-stratification for 4δ-robust mass at every depth);
deep creations only at cells with top-gap ≤ 2δ (the moving tie front);
birth sites further confined to the 4δ collar (no cold tie entries,
`collar_of_near_top`); re-entries once per (lineage, pencil); per-shave
bleed ≤ 2dδ/w of the cell.
Missing: why the collar hosts only poly many births — a NEW dynamical
inequality; the cycle-31 probe PROVES no static/geometric bound exists
(containment total, births tiny). All reformulations (ZONE, stacking,
lineages) are equivalences, not reductions; do not expect vocabulary to
crack it.

## 7. Recommended next steps, in order

1. **Multi-scale re-stratification bookkeeping** — DONE for the robust
   stratum (cycle 31, `Tfnp/Restrat.lean`): 4δ-robust tie sets are
   trajectory invariants at every depth, per-epoch ledgers telescope
   additively, robust-2-simple lineage cells ≤ O(d²T) scale-free; the
   shattering class (measured 99.8% robust) is now covered by a scale-free
   PROOF, not a fixed-δ model. What remains of this item is the collar
   stratum (gap₃ ≤ 4δ_r) — which is the front-birth problem (item 4), not
   bookkeeping.
2. **Average-case / smoothed theorem — IN PROGRESS (cycle 33, user-chosen
   direction; full state in `notes/smoothed.md`):** the annealed model
   (uniform balanced signs = randbal) is the tractable core. DONE: the
   half-kept law (Lean); the incubator martingale + Doob bound (emergence
   channel self-financing in expectation; measured Doob ratios: neutral
   oracles ≈ 0.9–1.06, cellmax 2.5 — adversarial nurturing detected);
   **(A1)'s survival half (Lean, cycle 34: `annealed_survival_pow` —
   2^{-a} exact survival for gap-deep lineages)**; the straddle–dodge
   dichotomy (Lean, cycle 35: `strict_argmax_of_one_sided` — dodging is a
   straddler-only privilege) reducing (A1)-front to the **branching
   frame**: E[L] ≤ (init + emergences)/(1 − b). Cycle 36: the POPULATION-BALANCE
   theorem closed the 2-simple annealed process (straddlers exactly
   critical, ≤ 1 per channel, bulk ½-subcritical ⟹ E[N] ≤ 2/channel,
   E[L_2simple] ≤ L₀ + O(d²T)) — **the pure-2-simple annealed theorem is
   END-TO-END**. OPEN — the single remaining piece of the GENERAL annealed
   theorem: **(A1'') deep-straddler occupancy** — fully-straddling m-cells
   branch at m/2 (supercritical, m ≥ 3); bound expected fully-straddling
   rounds per deep lineage by O(1) (splits evict offsets to boundaries —
   lineage lemma; measured O(1); worst-case depthmax sustains it, so this
   is exactly the annealed/adversarial divergence point). Then v3 (or v4 with exact slab-crumb tracking,
   smoothed.md §4b — leak vanishes identically) is poly-time w.h.p.
   annealed; then bridge to random-SSG sign processes via per-stratum
   approximate balance (the measured flux law). THIS IS THE ACTIVE
   TRACK — attack (A1'') next.
3. **Amortized depth ⟹ quasi-poly track:** the limit-cycle data suggests
   the time-integral of depth excursions is small; depth ≤ O(log dt)
   amortized ⟹ L quasi-poly ⟹ randomized quasi-poly SSG, **beating the
   `(log 1/ε)^{O(√d log d)}` SOTA** — the realistic next summit.
4. **The front-birth inequality** (the true core): front confinement +
   marginal engine are the proved jaws; what's needed is a bound on births
   at the front. Expect to need new mathematics; do not expect ledgers.
   Cycle-31 sharpening: `collar_of_near_top` makes "collar entry" a
   well-defined event with NO cold entries, and the probe shows births are
   O(d)/round with single-digit per-pencil stacking while geometric
   containment is total — so the target statement is dynamical: bound
   collar entries per lineage (marching bounds collar traversal speed;
   a supermartingale on collar occupancy is the natural shape).
   Cycle-32 decomposition (collar ledger): the target splits into
   (i) front-birth rate ≤ poly — measured O(d)/round, no oscillation
   churn, tie entry ~once per lineage; and (ii) EMERGENCE rate ≤ poly —
   sub-threshold mass re-crossing η by renormalization ×2/round growth,
   measured O(d)/round with incubation up to 11 rounds (cellmax). Any
   proof must price both channels; counts are trivially poly, the content
   is the pruned-crumb MASS ledger where BBL is vacuous on front cells.
5. Consider writing up the standalone publishable units meanwhile:
   (a) realizability/Kirszbraun + certified adversarial shattering
   (kills isoperimetry approaches, machine-checked); (b) the
   progress–convexity trade-off + no-surrogate theorem; (c) the trichotomy
   + walk/pair-record cell bounds; (d) the v3 algorithm + beyond-ceiling
   measurements.

## 8. Repo map

* Lean: `Tfnp/{Progress,Realizability,Fan,Margin,Walk,Shed,Restrat}.lean`
  (this campaign) + pre-existing `{Contraction,Algorithm,HitRun,PolyTime,...}`.
  All wired into `Tfnp.lean`; `lake build` green (any failure in
  `Tfnp/Tarski/` is the user's separate in-progress work).
* Notes: `smoothed.md` (the annealed/smoothed track, cycle 33 —
  THE ACTIVE TRACK), `CHAIN.md` (the reduction chain, cycles 21–29 appended),
  `RESEARCH_LOG.md` (all cycles), `cell_sampler.md` (cycles 12–15 detail),
  `adversarial_components.md` (realizability + shattering),
  `progress_convexity.md`, `FINAL_REPORT.md` (pre-campaign consolidation;
  its Cheeger row is superseded — noted inline).
* Experiments + results: `notes/polytime_experiments/*.py`,
  `*_results.txt`. Python env: recreate venv with numpy/scipy (no repo venv).
