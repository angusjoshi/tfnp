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

## 5. Instrument predictions (falsifiable, cycle 33)

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
