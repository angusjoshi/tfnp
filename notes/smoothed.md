# The smoothed/annealed track (cycles 33–)

*Goal (HANDOFF §7.2): an average-case / smoothed polynomial-time theorem —
random-SSG trajectories are measured benign on every axis; prove `L ≤ poly`
(η-free) w.h.p. for random instances, giving v3 correctness + poly time
w.h.p. Publishable on its own even without the worst-case core.*

## 1. The annealed model

Replace the oracle's sign answers by **uniformly random balanced sign
vectors**: `d = 2m` coordinates, exactly `m` positive, drawn fresh each
round, independent of the survivor structure. This is precisely the
`randbal` oracle of `adversary_game.py`, which is measured to match
random-SSG trajectories on every axis we have instruments for (depth flat
≈ 3, additive cell law, flux κ ≈ ½, collar-ledger channel rates —
cycles 18–32).

Two rigor grades:
* **annealed** — signs exactly uniform-balanced, independent of the past:
  every statement below is exact;
* **smoothed SSG** — random or perturbed game instances; the conjecture is
  that the induced sign process is "balanced enough" (κ ∈ ½ ± γ per
  stratum, measured; the flux law) for the annealed bounds to degrade
  gracefully. Bridging annealed → smoothed SSG is future work; the annealed
  theorems fix the target quantities.

## 2. The half-kept law (Lean, `Tfnp/Annealed.lean`, sorry-free)

**`annealed_half_kept`:** a point with a strict argmax `(i, σ)` relative to
the apex is kept by the cut for **exactly half** of the balanced sign
vectors. Proof: gap-deep membership is decided by the single sign `s i = σ`
(`mem_pyrUnion_iff_of_gap` at `δ = 0`), and complementation `A ↦ Aᶜ` is an
involution of the balanced vectors exchanging agreement with disagreement
(`card_balanced_mem_eq_not_mem`) — no binomial identities.

This is the annealed-model root of the measured flux law (`κ(m) ≈ ½` for
every depth class, every oracle — cycle 20): in the annealed model it is a
theorem, pointwise off the tie set.

## 3. The incubator martingale and the Doob emergence bound (paper-level)

Work with **unnormalized volumes**. Let `K_t` be round `t`'s kept set,
`X_t = X_{t-1} ∩ K_t`, and for a region `C` (a cell of the current
partition, tracked or not) write `v_t(C) = vol(C ∩ X_t)`.

**Balance.** With exactly balanced cuts, `vol(X_t) = 2^{-t}`; a cell is
tracked at threshold η iff `2^t v_t(C) ≥ η`. Define `M_t(C) = 2^t v_t(C)`
(the conditional mass under exact balance).

**Lemma (incubator martingale, annealed).** Let `C` be gap-deep at `(i,σ)`
at the current scale (kept whole iff `s_i = σ`, removed whole otherwise —
`deep_extinction`/no-split, PROVED). Under annealed signs,
`E[v_{t+1}(C) | 𝔉_t] = ½ · v_t(C)` (half-kept law), hence
`M_t(C)` is a **martingale**. For a cell in the margin (partially cut),
`v_{t+1}(C) ≤ v_t(C)` always, and the kept fraction of *any* fixed set has
expectation ½ pointwise (half-kept law integrated), so `M_t(C)` is a
martingale for gap-deep cells and a supermartingale never exceeding the
×2-per-round growth cap in general.

**Corollary (Doob bound on the emergence channel).** A sub-threshold crumb
born with conditional mass `m₀ < η` emerges (is ever tracked) with
probability at most `m₀/η`:

> `P[sup_t M_t(C) ≥ η] ≤ M_0(C)/η = m₀/η.`

Summing over the crumbs shed by the tracked ledger:

> **E[# emergences] ≤ (total shed conditional mass)/η.**

*The emergence channel is self-financing in expectation:* the incubator can
return at most the mass the ledger shed into it — no annealed amplification.
The cycle-32 anatomy (detection masses < 2η, i.e. caught within one
doubling) is exactly the martingale picture; the cellmax incubation tail
(ages to 11) is the adversarial-correlation effect the annealed model
excludes, and the ledger still measured its RATE at O(d)/round.

**Caveats (honest):**
1. The bound is stated for gap-deep crumbs; margin crumbs are
   supermartingales only up to the per-round ×2 cap — the assembly must
   split by stratum (the machinery exists: no-split, m-set confinement).
2. Splitting of an incubating crumb only *lowers* each piece's emergence
   probability (mass splits, threshold doesn't) — Doob is conservative
   here, in our favor.
3. Exact balance `vol(X_t) = 2^{-t}` is an idealization; approximate
   balance `κ_t ∈ ½ ± γ` turns the martingale into an
   `exp(O(γ))`-compensated supermartingale — the constants survive
   `γ = O(1/t)`.

## 4. The annealed system of inequalities — what closes, what doesn't

Let `L = L_birth + L_emerge` (the cycle-32 channel decomposition).

* `E[L_emerge] ≤ shed/η` — Doob (above).
* `shed ≤ O(d·t·L·η)` — the marching/crumb ledger (cycle 28, corrected
  cycle 29).
* Composing: `E[L_emerge] ≤ O(d·t·L)` — **vacuous as a closure** (constant
  ≥ 1 in front of `L`). The system does NOT close by these two alone: the
  Doob bound must be beaten by the typical crumb's mass being `≪ η`
  (measured: median crumb ≪ η, BBL engine for wide cells), or by counting
  crumb *splits* during incubation.
* `L_birth`: annealed births need the walk-lemma crossing + both sides ≥ η.
  The stacking residue is unchanged by annealing **as a worst-case count**,
  but annealed signs kill deep records at rate ½/round (`deep_extinction` +
  half-kept), so the *persistent* deep population that stacking needs decays
  geometrically — this is the quantitative-flooding mechanism (cycle 19) in
  its probabilistic home, and the right next lemma:

> **(A1) Annealed stacking decay.** Under annealed signs, the expected
> number of tracked deep lineages sharing one pencil's front gap is O(1):
> a stacked lineage's distinguishing record involves ≥ 1 coordinate whose
> sign must have agreed in every round since the records diverged —
> probability `2^{-age}` — while its mass must have grown `2^{age}`-fold to
> stay tracked. Stacking count × survival is a supermartingale.

**(A1) + the walk lemma + Doob would give `E[L] ≤ poly(d, t)` annealed** —
the full annealed theorem. (A1) is the concrete open lemma of this track;
it is a statement about ONE stochastic process with independent fair signs,
not about adversarial dynamics.

**(A1) status after cycle 34 — the survival half is machine-checked.**
`annealed_survival_pow` (Lean, `Tfnp/Annealed.lean`): a point gap-deep at
every one of `a` rounds survives all `a` independent balanced cuts for
exactly a `2^{-a}` fraction of sign tuples (piFinset factorization of the
half-kept law). Consequences, exact in the annealed model: expected
gap-deep lineage lifetime = 2 rounds; survival × mass-growth is a
martingale; any stacked deep population pays `2^{-age}` for its `2^{age}`.
**What remains of (A1) is the front half:** tie-front cells dodge (argmax
mobile within the tie set — survival > ½), so front stacking needs the
dodging cost accounting: a front lineage's distinguishing record still
contains ≥ 1 *resolved* (gap-deep) coordinate comparison per divergence
(`pair_membership_iff`: records differ in some form's walk position, and a
form's walk position is frozen while irrelevant), and resolved comparisons
decay by `annealed_survival_pow`. Making "divergence implies a resolved
coordinate paying 2^{-age}" precise is the remaining step — it is the
annealed version of the transverse-stacking residue (cycle 27).

## 4c. The branching frame (cycle 35) — (A1)-front as subcriticality

**The straddle–dodge dichotomy (Lean, `strict_argmax_of_one_sided`):** a
2-simple front cell strictly on one side of its pair's current offset has a
uniform strict argmax — so `annealed_survival_pow` applies to it verbatim:
**every tracked cell that is not straddling its pencil's offset dies at
rate exactly ½ per round.** The argmax-dodging advantage of the tie front
is confined to the straddling cells, which the walk lemma counts (`O(1)`
per (pair, pattern, record)).

**The frame.** The tracked-lineage population is a branching process with
immigration:
* immigration = initial cells + emergences (Doob: self-financing);
* offspring = tracked births, which occur ONLY at mid-extent crossings —
  once per (lineage, pencil) ever (lineage lemma), only while straddling;
* death = extinction at rate ½ per non-straddling round (Lean, both
  strata now).

Hence `E[L] ≤ (initial + E[emergences]) / (1 − b)` with
`b = E[tracked births per lineage lifetime]`, and the annealed theorem
reduces to:

> **(A1'') the subcriticality inequality: `b < 1` in the annealed model.**
> Structure: `b ≤ Σ_ψ P[lineage alive ∧ straddling ψ at ψ's (unique)
> mid-extent crossing]`. Each new relevant pencil costs ≥ 1 tolled collar
> round (`gap_lipschitz`) at ≤ ¾ survival; ½-per-round death off-straddle
> discounts every waiting round; acquiring many relevant pencils
> simultaneously means deep ties, which annealed flooding kills
> (`double_disagree_kills` at rate ¼ per pattern per round).

**Measured (already in the cycle-32 collar-ledger data): b is subcritical
under every oracle** — ssg `242/395 ≈ 0.61`, cellmax `146/388 ≈ 0.38`,
randbal `280/430 ≈ 0.65`, shattering `0/31 = 0`. Consistency check of the
frame: predicted `L ≈ (init + emerg)/(1 − b)` gives ssg
`(29 + 153)/0.39 ≈ 467` vs measured `395` — right ballpark with the
boundary effects expected at `t ≤ 13`.

What remains for the annealed theorem is exactly (A1''): an annealed proof
that `b < 1` — equivalently, that the survival discount to the (once-ever)
crossing events beats their count. All three mechanisms it needs are
machine-checked (once-ever crossings, ½-death off-straddle, collar tolls);
the missing step is the bookkeeping that combines them over one lineage's
lifetime without conditioning pitfalls (the crossing TIMES are not
independent of survival — the offsets are functions of the surviving
measure; this is where care is needed, and where a clean martingale/
optional-stopping argument should replace naive independence).

## 4d. The population-balance theorem (cycle 36) — the 2-simple annealed
## process is closed

**The straddler's offspring distribution, machine-checked pointwise.** For
a 2-simple pattern-`(ε₁,ε₂)` cell straddling its pair offset, the round's
outcome as a function of the cut's signs at the pair:

| `(s_{i₁}, s_{i₂})` | outcome | Lean |
|---|---|---|
| `(ε₁, ε₂)` | whole cell kept, split into TWO cells (birth) | `both_agree_keeps` |
| `(ε₁, −ε₂)` | exactly the `i₁`-side piece kept | `pair_membership_iff` |
| `(−ε₁, ε₂)` | exactly the `i₂`-side piece kept | `pair_membership_iff` |
| `(−ε₁, −ε₂)` | everything dies | `double_disagree_kills` |

Under balanced signs each combo has probability `¼ ∓ O(1/d)` (exact:
`P(agree,agree) = (m−1)/(2(2m−1))` when `ε₁ = ε₂` on the +/− split, etc.).
So a straddler's expected offspring is `¼·2 + ½·1 + ¼·0 = 1 ∓ O(1/d)`:
**exactly critical**; a non-straddler dies at `½` (`strict_argmax_of_
one_sided` + `annealed_survival_pow`): **subcritical**.

**Population balance.** Cells of one (pair, pattern) channel are disjoint
`φ`-intervals (pair-record theorem), so **at most ONE cell per channel
straddles the offset**. Hence per channel,
`E[N_{t+1}] ≤ 1·1 + (E[N_t] − 1)·½`, whose fixed point is `E[N] = 2`:

> **The annealed 2-simple population-balance theorem.** In the annealed
> model, each (pair, pattern) channel carries at most 2 expected tracked
> cells at any time, and produces at most `¼ + O(1/d)` expected births per
> round. Over `T` rounds: `E[L_{2-simple}] ≤ L₀ + (¼ + o(1))·2d(d−1)·T
> = L₀ + O(d²T)`.

Combined with the Doob emergence bound (§3) and the scale-free robust
ledger (cycle 31), **the annealed theorem is CLOSED for trajectories whose
tracked mass stays 2-simple at working scale** — the pure-2-simple annealed
theorem. This supersedes the per-lineage `b < 1` frame of §4c (which
remains as the empirical shadow: measured b = births/L ≈ 0.38–0.65).

**The honest deep caveat.** A fully-straddling `m`-tied cell (all its tie
set's offsets inside its extents) has expected offspring `m/2 − O(1/d)`:
**supercritical for m ≥ 3**. What limits it is occupancy, not branching:
sustaining full straddling requires all `C(m,2)` marching offsets inside
ever-shrinking pieces, and each split evicts the offset to a boundary
(lineage lemma) — the measured deep population stays O(1) per pencil
(stacking probe) and randbal's L stays linear. **The remaining open piece
of the general annealed theorem is the deep-straddler occupancy bound**
(expected fully-straddling rounds per deep lineage = O(1)) — (A1'') in its
final form. Note the worst case is genuinely different here: depthmax
SUSTAINED deep straddling (cycle 23) — occupancy is where annealed and
adversarial dynamics part ways.

## 4e. The occupancy verdict (cycle 37) — persistence, criticality, and the
## surviving formulation

**Machine-checked (`pyr_mem_halfspace`):** eviction is definitional at
every depth — a kept pyramid piece lies in ALL the cut's pencil halfspaces,
so every split evicts every offset of the apex to the piece's boundary.
Fresh penetration is budgeted at `2δ`/round (marching bound).

**Measured (`occupancy_probe.py` → `occupancy_results.txt`): the
transient-occupancy hope is FALSE at working scales.** Straddling is
persistent (runs spanning the whole measurement window under randbal —
the ANNEALED-model oracle), penetration/minority-fraction drifts UP for
survivors (mean +0.05, only 39% negative), and birth-grade straddling runs
long too (instrument caveat: run histograms count prefixes; read the max
and window-saturation, which are unambiguous). Deep-straddler counts are
substantial every round. The population stays balanced (births ≈ deaths,
L linear) not because straddling is scarce but because the population
process is critical.

**The criticality signature (the honest structural reading).** Everything
coupled to balance is EXACTLY critical: kept fraction ½ × renormalization
×2 = mass martingale (cycle 33); straddler offspring mean 1 (cycle 36);
birth-grade run mass-financing (each split halves the token, regrowth
doubles it) — critical again. Balance bakes criticality into every
population quantity; no subcriticality argument can close the deep case.
The theorem must come from **budgeted resources**, not decay rates. The
proved budgets: walk positions ≤ 2t+1 per channel; mid-extent crossings
once per (lineage, pencil); pencil energy `4k‖u‖²`. The cycle-36
population-balance theorem worked exactly because it paired criticality
with a budget (≤ 1 straddler per channel).

**The surviving formulation of (A1'').** At depth, the channel structure is
the other-forms record classes, and per-channel straddler uniqueness IS
transverse stacking — the campaign's original residue, now with the
annealed pricing tool: two stacked cells differ in a record entry acquired
`a` rounds ago, whose holder survived `a` rounds (`annealed_survival_pow`:
`2^{-a}` for the resolved rounds). **(A1''-final): E[number of distinct
other-form record classes among tracked cells of one tie set] = O(1) in
the annealed model, via survival-priced record divergences.** This is
(A1)-original made precise; the occupancy detour is closed (and its
falsification recorded so it is not re-attempted).

## 4f. The stacking dichotomy, decay half (cycle 38) — and an error caught

**Machine-checked (`strict_argmax_of_resolved`):** an m-simple point on tie
set `M` whose pairwise signed-offset comparisons on `M` are all strictly
resolved (it straddles NONE of its tie set's current offsets) has a strict
argmax — so `annealed_half_kept` applies: **fully-resolved deep cells die
at rate exactly ½ per round in the annealed model, at every depth.** The
dodge privilege belongs exclusively to cells straddling ≥ 1 of their own
tie forms.

**Error caught before commit (recorded so it is not re-attempted):** the
cycle-36 budget "≤ 1 straddler per channel" does NOT lift to depth as
"≤ 1 straddler per form". At depth, cells with different other-form
records can straddle the SAME form simultaneously — that is precisely
transverse stacking (and the stacking probe's geoK data shows containment
is plentiful). The interval argument closes the pure-2-simple case only
because there the record IS the φ-position. **The budget half of the deep
dichotomy is exactly the stacking count — unchanged, still the open
core.** No per-tie-set population balance is claimed.

**Net state of the general annealed theorem:** decay half proved at every
depth (resolved ⟹ ½-death); budget half = (A1''-final): E[#same-form
straddlers with distinct records] = O(1) annealed, to be proved by
survival-pricing the record divergences. The pure-2-simple theorem (§4d)
is unaffected.

## 4g. The recrossing reduction (cycle 39) — the last piece becomes a walk
## statement

**The shared-coin stack martingale.** All ψ-straddlers face the SAME two
coins each round: agree–agree ⟹ every member births (`both_agree_keeps`);
single-agree ⟹ every member halves to the agreeing side
(`pair_membership_iff`); double-disagree ⟹ **the whole stack dies together**
(`double_disagree_kills`). Stack size is a martingale with jumps
(×2, ×1, ×0) — E[S] constant except for **immigration**: lineages newly
entering ψ-straddlerhood.

**Immigration is walk geometry.** Extent boundaries are past offsets
(lineage lemma), so every entry into straddlerhood is a level-crossing of
the offset walk `v_t = φ_ψ(c_t)` over some past level `v_r`. A monotone
walk crosses each level once. Caveat (honest): one crossing can admit the
whole stack flanking that level, so admissions compose multiplicatively:

> `E[S] ≤ 2^{O(max per-level recrossings)}`, and total births per pencil
> `≤ ¼·Σ_t E[S_t]`.

**The reduction:** the general annealed theorem's last piece is now the

> **OFFSET-WALK RECROSSING BUDGET: for annealed FW-apex trajectories,
> the expected number of times a pencil's offset re-crosses any fixed past
> level is O(1) (O(log dt) suffices for the quasi-poly milestone).**

A statement about one real-valued walk (the FW apex functional of the
random surviving measure, steps shrinking with the diameter) — standard
probability toolkit shape (shrinking-step random walk level crossings),
no cells, no populations.

**Measured (`walk_recross.py`, d = 6, T = 20, all 30 pencils × both
signs):** recrossings per level — ssg **0.51**, randbal **0.70**,
adversary 1.09, cellmax **1.52** (max 8–10 over 570 levels). O(1) means
everywhere, including the path-curving adversary that cycle 21 feared.
The annealed/benign walks are effectively monotone at the per-level scale.

**Closure routes:** (a) prove the recrossing bound for annealed apex walks
(the steps' conditional sign-symmetry + geometric shrinkage ⟹ O(1)
expected crossings per level — the concrete probability lemma to attack);
(b) the algorithmic nudge (cycle-21 line-epoch lever): choose apexes
within the centerpoint region to keep every pencil's walk low-recrossing —
turns the bound into a design constraint rather than a theorem about FW.

## 4h. The crossing toll made exact; the abstract-walk no-go (cycle 41)

**Machine-checked (`annealed_crossing_toll`, Lean, sorry-free):** for the
fair-coin walk (round-`s` step `±μ_s` by an independent fair coin,
`μ_s ≥ 0`), summed over ALL coin tuples,

> `2 × (total crossings of any fixed level ℓ) = total strict step-band
> residence at ℓ` (rounds with `0 < |v_t − ℓ| < μ_t`).

Mechanism: a crossing requires being strictly inside the one-step band (a
past-measurable event) plus ONE specific fresh coin — exactly half the
band-resident tuples cross. With `walk_no_recross` (band rounds confined to
the escape band), the recrossing budget is now EQUIVALENT, machine-checked,
to a **band-residence bound**: the walk's position must anticoncentrate
relative to its own past levels.

**Empirical validation (`walk_recross_scaling.py`, d = 4,6,8,10, T = 20,
ssg/randbal/cellmax, randbal ×3 seeds):** on real FW-apex walks,
`2 × recross/level ≈ stepband/level` at every d and oracle (ratio
0.91–1.00) — the fair-coin pricing of crossings is exactly right for the
real dynamics. **All the smallness of the measured recrossings lives in the
smallness of band residence (1.2–3.3 rounds/level), not in any sign
bias.** And recross/level is **FLAT in d**: randbal pooled means
0.95/0.83/0.96/0.86 (d = 4/6/8/10 — a single-seed apparent √d trend was
seed noise, caught by replication), ssg 0.5–0.6, cellmax 1.4–1.6.

**The no-go (record as do-not-attempt):** coin fairness + a geometric step
envelope alone CANNOT give the budget. The measured envelopes have
`q̂ ≈ 0.89–0.99` (flat windows `n ≈ 1/(1−q̂) ≈ 10–76` rounds), and the
model admits `n` near-flat steps `μ_t ≈ Δ` (generic, incommensurate)
inside such an envelope; such a walk's expected strict residence within one
step of a generic level in its range is `Θ(√n)` (local CLT:
`P[|v_t − ℓ| < Δ] ~ t^{-1/2}`; for EXACTLY flat steps and the walk's own
lattice levels the strict count degenerates — genericity matters), hence
`Θ(√n) = Θ(√d)`-type recrossings per level — not `O(1)`, not even
`O(log)`. Through the §4g stack composition `E[S] ≤ 2^{O(recross)}` this is
super-polynomial: **the abstract walk model cannot even reach the
quasi-poly milestone.** The Littlewood–Offord obstruction is the same
anticoncentration floor that killed the pure-ledger routes (cycle 28): no
distribution-free counting argument beats `√t`.
Monte-Carlo check (`walk_floor_model.py`): near-flat fair walk, generic
level — `E[cross]/√n = 0.67–0.75` stable over `n = 16 → 1024` (the floor
is real) and `2·cross/band = 0.99–1.00` (the toll identity, on the nose).
Read against the floor: the REAL walks (0.5–1.6 recross/level at measured
flat-windows 10–76, whose coin-model floor would be ≈ 2.2–6) recross
**3–10× less than their own coin model** — the FW dynamics has genuine
per-level transience that fairness alone provably cannot supply.

**What survives (the two live closures, sharpened):**
1. **Dynamics route:** the band-residence bound must come from a
   transience property of the ACTUAL apex walk. Candidate mechanism, with
   its Lean-checked engine: `one_sided_of_kept` — every cut leaves the
   surviving measure one-sided at every pair, off ties — so each round
   evicts the mass (whose FW balanced point the next apex IS) from the
   current offset's neighborhood: the walk is mean-repelled from its own
   trace. The target lemma: E[rounds with `|φ(c_t) − ℓ| < μ_t`] = O(1)
   for the annealed FW dynamics (O(log dt) suffices for quasi-poly).
2. **Design route (cycle-21 lever):** choose apexes inside the centerpoint
   region so every pencil's offset walk is per-level monotone outside its
   escape band — turns the budget into an algorithmic constraint; open
   feasibility (progress vs monotonicity trade-off).

## 4b. The recycling insight (cycle 34)

The measured Doob ratios (~0.9–1.06 for neutral oracles) say the bound is
near-TIGHT in aggregate: **the shed mass largely returns** — the exact
dynamics runs a recycling flow tracked → crumbs → incubator (×2/round) →
emergence → tracked. The v3 algorithm PRUNES the crumbs and so declares
their mass as leak; the measured ~0.3%/round leak is precisely the
incubator's throughput. Algorithmic consequence worth pursuing: since
crumbs are marching slabs with exact polytope descriptions (`shed_slab`,
Lean), a v4 could track sub-threshold crumbs EXACTLY instead of pruning —
the leak then vanishes identically, and correctness no longer needs (SHED);
what it needs is the crumb population staying poly, which annealed
extinction (½/round death for deep crumbs, `annealed_survival_pow`) makes a
subcritical branching process off the front. The front-crumb branching rate
is the same open front half of (A1). Worst-case this is (★) again — but
for the ANNEALED/smoothed theorem, v4 + (A1)-front closes correctness AND
time simultaneously.

## 5. THE ANNEALED PURE-2-SIMPLE THEOREM (consolidated, cycle 40)

> **Theorem (annealed, pure-2-simple).** Consider balanced-cut dynamics on
> `[0,1]^d`, `d = 2m`, with oracle signs drawn each round uniformly from
> the balanced sign vectors, independently of the past, and suppose the
> tracked (mass ≥ η) cells remain 2-simple at working scale with
> `4δ`-robust tie gaps along the trajectory. Then over `T` rounds:
> (i) each (pair, pattern) channel holds at most 2 expected tracked cells
> at any time; (ii) the expected number of tracked lineages ever created
> is `L₀ + O(d²T)` + the emergence channel, which is self-financing
> (`E[emerged mass] ≤ shed mass`; `E[#emergences] ≤ shed/η`);
> (iii) consequently the v3 cell-tree algorithm runs in expected
> polynomial time with expected leak bounded by the shed ledger on this
> class.

**Proof structure, with machine-checked citations (all sorry-free):**
1. Channel structure: pair-record theorem (`pair_membership_iff`), walk
   lemma (`ncard_range_signPattern_le`); pair invariance of robust mass
   at every scale (`pair_invariant_of_robust`, cycle 31) — records
   telescope, channels don't multiply.
2. Offspring table of a straddler, pointwise: birth (`both_agree_keeps`),
   single-side survival (`pair_membership_iff`), death
   (`double_disagree_kills`) — mean offspring `1 ∓ O(1/d)` (balanced-sign
   pair probabilities `(m−1)/(2(2m−1))` etc.).
3. Non-straddlers die at exactly ½: `strict_argmax_of_one_sided` +
   `annealed_half_kept` (and at depth, `strict_argmax_of_resolved`);
   iterated: `annealed_survival_pow`.
4. ≤ 1 straddler per channel (interval disjointness of the pure-2-simple
   record classes) ⟹ per-channel population balance `E[N] ≤ 2`.
5. Emergences: incubator martingale + Doob (§3), with `pyr_mem_halfspace`
   and `gap_lipschitz` fencing entries and evictions.

**Caveats (honest):** the `O(1/d)` sign-correlation corrections are stated
but not yet carried through a full assembly; "pure-2-simple with robust
gaps" excludes the collar mass (the general theorem needs the recrossing
budget, §4g); exact balance `vol(X_t) = 2^{-t}` is an idealization
(approximate balance costs `exp(O(γt))` factors). The assembly into a
publishable statement is mechanical but real work; every load-bearing
pointwise fact is Lean-checked.

**General annealed theorem, remaining distance:** the offset-walk
recrossing budget (§4g), now reduced further (§4h, cycle 41): the
deterministic half is Lean-checked (`walk_no_recross`: recrossings confined
to the escape band) and the probabilistic half is Lean-EQUIVALENT to a
band-residence bound (`annealed_crossing_toll`: 2 × crossings = step-band
residence, exactly). The open piece, final form: **E[step-band residence
per past level] = O(1) for the annealed FW-apex walk** (O(log dt) for the
quasi-poly milestone) — and the §4h no-go shows this CANNOT follow from
coin fairness + step shrinkage alone (Θ(√flat-window) Littlewood–Offord
floor); it needs the dynamics' own transience (candidate engine:
`one_sided_of_kept`) or an algorithmic apex rule. Measured
(`walk_recross_scaling.py`, d = 4–10, randbal ×3 seeds): 0.5–1.6
recrossings/level, FLAT in d, matching the fair-coin toll on the nose —
and 3–10× BELOW the coin-model floor at the measured flat windows: the
required transience is real, d-robust, and dynamical.

## 5b. Instrument predictions (falsifiable, cycle 33)

1. **Emerged-vs-shed ratio:** cumulative unnormalized emerged mass ≤
   cumulative unnormalized mass that left the tracked set. Annealed/ssg:
   ratio ≤ 1; cellmax may exceed it only via sign-correlation (nurturing),
   bounded by its realizability menu.
   **MEASURED (cycle 33, d=6, t ≤ 13, in-window origin only):** ssg 0.909 ✓,
   shattering 0.016 ✓, randbal 1.061 (≤ 1 within instrument noise; the
   harness's randbal is realizability-clipped, hence not perfectly
   independent), **cellmax 2.501 — adversarial nurturing measured at ×2.5,
   the predicted annealed-model violation.** The discriminator works;
   random SSG sits on the annealed side (bridge evidence).
2. **Emergence-age decay:** annealed ages should be geometric(½) beyond
   the one-doubling minimum — measured cycle 32: randbal ages
   `{2:67, 3:30, 4:23, 5:10, 6:3, 7:2, 10:1}` — ratio ≈ 0.45–0.5/step ✓
   (cellmax's fat tail `{5:29, 6:22, 8:10}` is the adversarial correlation,
   as predicted).
3. **Half-kept per stratum:** κ(m) = ½ ± sampling error for randbal at
   every depth — already measured (flux law) ✓.
