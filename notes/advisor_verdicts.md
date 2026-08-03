# Advisor verdicts — quality gate on rogue-ideas conjectures

Skeptical-advisor log for the poly-time `ℓ∞`-contraction (⟹ SSG∈P) push. Each
idea from `rogue-ideas` gets a verdict: **PROMISING** (+ concrete next step),
**FLAWED-BUT-FIXABLE** (+ the fix), or **DEAD** (+ the precise killing reason).
No claim is waved through without a mechanism; no refutation is fabricated — if a
claim can't be settled here, it's marked OPEN with exactly what would settle it.

## Standing obstructions every idea is checked against

1. **Hard-regime preservation.** The SSG reduction produces `1−λ = 2^{−poly}`,
   `ε = 2^{−poly}`, poly bit-size. Any "connection" that only helps when
   `1/(1−λ) = poly` is just value iteration — buys nothing (`polytime.md §0`).
2. **conv(X_t) = ℝ^d.** As soon as a cut's support `|S| ≥ 3` and `d ≥ 3`, the
   kept region's convex hull is everything (`polytime.md §3.2`). So *every*
   convex-outer-approximation / ellipsoid / cutting-plane method is provably dead
   unless the index set is first narrowed to ≤ 2 (Corollary C).
3. **Equal-hardness reductions.** Tarski fixed points, mean-payoff games,
   parity games poly-time are ALL open and ≡ₚ / related to SSG. A reduction TO
   any of these is not progress. SSG ∈ NP∩coNP∩UP∩coUP already known.
4. **Convexity smuggling.** KLS/localization/isoperimetry theory is convex-only.
   The body here is a non-convex union of cones. Any invocation of convex-body
   sampling theory must confront non-convexity explicitly.
5. **The one wall.** All three sampler routes (Cheeger `h`, conditioning `κ`,
   exact star-sampler) reduce to a realizable **anisotropic/dumbbell** `X_t`.
   Crossing it in any formulation = resolving SSG (`isoperimetry_summary.md §4`).

## Verdicts

### Batch 1 (rogue_ideas.md: D, A, B, C top; E–I stubs)

---

#### D — Policy/sign stabilization + exact optimality certificate. **FLAWED-BUT-FIXABLE → escalated (best in batch).**

The endgame certificate is *sound and genuinely sampler-free*: for a fixed policy
σ, solve `(I−γP_σ)x_σ = r_σ` (poly linear system) and check the full Bellman
optimality operator has zero improving deviation (one poly backup). If it passes,
`x_σ = x*` exactly — this is precisely the policy-iteration optimality certificate,
and it needs **no** sampler and tolerates **no** sampler error. That layer is correct.

Three corrections that reshape the idea:

1. **It requires WHITE-BOX SSG access, not the black-box ℓ∞ oracle.** `s^r =
   sign(f(c^r)−c^r)` is the Bellman-*residual* sign, not the argmax action; the
   contraction oracle returns `f(c)` only, never the underlying transitions/rewards,
   so you cannot form a candidate policy σ or run the certificate from black-box
   queries. D is therefore an approach to **SSG∈P** (white-box), abandoning the
   general contraction/sampler machinery. That's fine — SSG∈P is the headline — but
   it must be stated: D is not an approach to the general fixed-point problem.

2. **The "sampling-BYPASS" claim is only true for the endgame, not the whole run**
   — *unless* one uses the certificate to drop the mixing requirement entirely.
   This is the fixable/valuable reframing: with the exact certificate you no longer
   need the sampler to *provably mix* (the wall). You need only that the (free
   warm-started) center sequence **enters σ*'s optimality cell in poly rounds**,
   then certify. That trades the **isoperimetry wall** for a **strategy-improvement
   convergence** question — a genuinely *different* hard problem, sidestepping the
   anisotropy wall.

3. **"Poly rounds to σ*" = poly bound on a strategy-improvement pivot rule, and the
   two standard rules are REFUTED.** Friedmann 2009 (arXiv:1106.0778, and the parity
   paper) + Fearnley 2010 (arXiv:1003.3418) give **exponential** lower bounds for
   both standard deterministic pivots (local-improve-all and globally-optimal-
   improvement) on SSGs. Those lower-bound games are **valid, realizable SSGs**. The
   only poly escape — Hansen–Miltersen–Zwick, *Strategy Iteration is Strongly
   Polynomial for constant discount* (JACM, dl.acm.org/doi/10.1145/2432622.2432623)
   — needs **constant** discount, but our hard regime is `γ = 1−2^{−poly}` (standing
   obstruction #1). So D survives **only if** its FW-center-driven pivot is provably
   distinct from Friedmann's rules AND escapes his adversarial construction at
   discount→1.

**Decisive experiment (sent to main):** don't just log signs on random topical
instances (that only tests the easy regime). Run the FW-center algorithm on
**Friedmann's exponential-lower-bound SSG family** at `γ→1` and count
rounds-to-stabilize. Exp ⟹ D DEAD (the geometric pivot falls into Friedmann's
trap). Poly ⟹ genuinely new (geometric pivot escapes the known lower bounds) —
that would be a real result worth hard pursuit. Also test the certificate-on-crude-
center version to confirm correctness decouples from sampler accuracy.

*Why escalated:* it is the only idea that exploits the finite-policy structure the
sampling view discards, the certificate is sound, and it swaps the anisotropy wall
for a different (and specifically testable) wall.

---

#### A — Local stability of the isotropy fixed point (scale-free κ). **FLAWED-BUT-FIXABLE (skeptical); cheap decisive test.**

Legitimate reframing: local basin stability at isotropy (where the algorithm
starts, the box) instead of global bounded-κ (known false, symmetric model). Honest
about the asymmetric injection term being the only thing that can pull the Jacobian
eigenvalue `<1`. Two problems:

1. **O(1) per-cut steps ≠ linearization.** Each cut is a finite operation; the
   trajectory demonstrably leaves any tiny linear neighborhood (κ drifts to 8.9 at
   d=4). Local `ρ(J)<1` gives "stable if perturbations stay infinitesimal," which
   they don't. Need a finite-radius basin / Lyapunov argument, not a Jacobian.

2. **The mechanism A relies on is already measured ABSENT on hard instances.**
   `repair_attack.md` T2: on hard spread-`x*` SSG instances asymmetric injection
   does *not* repair (`asym_v>0` only 3–4/10, out-paces downdate 0–1/10); the thin
   axis survives by **downdate-orthogonality**, not injection. So even a favorable
   Jacobian at isotropy wouldn't cover the regime that matters.

**Cheap decisive test (sent to main):** finite-difference the full asymmetric
one-cut-+-renormalize Jacobian at near-isotropy, d=4..8, exact rejection (extends
`idealized_dynamics.py`). `ρ(J)≥1` on a non-trace direction ⟹ A DEAD. `ρ(J)<1` ⟹
a *local* result that still must confront the anisotropic regime where T2 says the
injection mechanism is off. Worth running because it's cheap and decisive for the
local claim.

---

#### B — Cell-graph conductance, canonical paths to Hamming graph. **DEAD as a bypass (≡ Route 1 / the wall); valuable reformulation, run the cheap test.**

The decomposition is sound machinery (Madras–Randall state decomposition): cells
`P_π` are convex (so within-cell mixing is poly after per-cell whitening; a convex
cell can't be a dumbbell), hence *all* non-convexity/bottleneck lives in the
inter-cell conductance `Φ(G_t)`. So B faithfully isolates the difficulty — arguably
the cleanest restatement. **But** the lemma it needs, "facet-adjacent cells have
vol ratio ≤ poly," is FALSE exactly in the dumbbell regime: a thin bridge cell
between two fat lobe-cells has an exponential adjacent-volume ratio, and that *is*
the Cheeger bottleneck (`isoperimetry_summary.md §4`). `Φ(G_t)≥1/poly` ⟺
`h(X_t)≥1/poly`. So B ≡ Route 1, not a bypass (standing obstruction #5).

*Salvage value:* the comparison-to-Hamming-expander is a concrete proof strategy
the raw Cheeger formulation lacks, and it is **computable**. Test worth running
(F–H already enumerate cells): build `G_t` for small d,t on **realizable
FW-center-driven** trajectories, measure `λ2/Φ` and max adjacent vol ratio + its
scaling. If realizable graphs are always "flat" (poly ratio) while adversarial cell
graphs aren't, that reproduces the sliver non-realizability dichotomy at the
cell-graph level — evidence, not proof.

---

#### C — RMT / Dyson-Brownian-motion with reflecting walls. **DEAD (category error); keep only the ESD plot as a cheap diagnostic.**

1. **RMT is an N→∞ theory for matrices with random/independent increments.** Here
   the covariance is `d×d` with fixed *modest* d, and the dynamics are
   **deterministic** (FW-center-driven) — no Gaussian noise to drive eigenvalue
   repulsion, no dimensional limit for an ESD to converge in. "ESD → t-independent
   ν*" has no meaning at fixed small d. Category error.

2. **"spread = Σ(logλ−mean)² = free entropy" is wrong.** Dyson free energy is the
   log-*repulsion* `Σ log|λ_i−λ_j|`; spread is the variance of the log-spectrum.
   Different functionals; the identification is unjustified.

3. **C's own refutation trigger already fired.** `idealized_dynamics.py`: the bottom
   edge DOES drift to 0 on graded spectra in the (symmetric) model; `repair_attack`
   T2: the asymmetric injection that would hold it up is absent on hard instances.

Keep only: plotting the ESD trajectory is a fine cheap sanity check, and the
qualitative "reflecting wall at top (downdate shaves λ_max), leak at bottom" picture
matches data — but that's description, not a convergence theorem.

---

#### E — Homotopy continuation in discount γ, bound optimal-policy switches on [0,1). **DEAD-leaning (reduces to open policy-count; hard regime is the endpoint).**

Same wall as D from the other side. The path `γ:0→1` ends *at* the hard regime
`γ→1`, exactly where HMZ's constant-discount poly bound fails. Bounding the number
of optimal-policy breakpoints along the discount axis by poly would essentially give
a poly SSG algorithm, so it is not easier. Needs a lit check (is the number of
discount-breakpoints provably exponential for some SSG family? if so, DEAD outright)
— low priority vs D, which is the same combinatorial structure with a better handle
(the certificate + non-adversarial geometric pivot).

---

#### F — Ollivier-Ricci / reflection coupling. **DEAD-leaning (≡ wall; negative curvature at reentrant corners).**

Positive coarse Ricci ⟹ fast mixing is essentially a Cheeger/log-Sobolev bound =
the wall. Worse, `conv K = ℝ^d` means `X_t` has **reentrant** (non-convex) corners
where two cone-unions meet; coarse Ricci curvature is *negative* there, and that is
precisely the bottleneck. The reflection structure (removed = point-reflection of
kept) is a real hook worth remembering, but reflection coupling won't give positive
curvature past the first cut. Low priority.

#### G — JKO / displacement-convex functional. **DEAD (convexity smuggling, obstruction #4).**

Displacement (geodesic) convexity requires a convex domain; `X_t` is non-convex
(`conv=ℝ^d`). The Wasserstein-gradient-flow contraction rate is exactly what fails
on non-convex domains. This is convexity smuggling.

#### H — Submodular coverage center. **UNCLEAR/low.** No stated link from a
submodular-coverage center to either the balanced/FW center (which is the
LP/Fermat–Weber minimizer, already characterized) or to a mixing bound. Speculative;
ask rogue for the concrete bridge before spending on it.

#### I — Tarski cut-guided bracketing. **DEAD as stated (obstruction #3).** SSG maps
are monotone (topical ⟹ monotone), so Tarski applies — but **poly-time Tarski is
open and ≡-hard**; reducing to it is not progress. The monotonicity IS a real
structural asset the sampling view ignores (worth remembering as a hook), but
bracketing via Tarski buys nothing on its own.

---

**Batch-1 bottom line.** One escalation: **D**, the only idea that leaves the
sampling/isoperimetry frame for the finite-policy frame, with a sound sampler-free
certificate and a specific decisive experiment (run on Friedmann's family at γ→1).
A gets a cheap decisive Jacobian test. B is the wall restated but its cell-graph
test is cheap and reproduces the realizability dichotomy. C/E/F/G/I are dead or
reduce to equally-open problems; the reusable crumbs are the monotonicity (I) and
reflection (F) structural hooks. Sources: Friedmann arXiv:1106.0778/1003.3418
(Fearnley), HMZ JACM 10.1145/2432622.2432623, Madras–Randall decomposition, KLS.

---

### D — CRUX RULING (value-space vs strategy-space: is D circular?)

Team-lead's sharp question: does "rounds-to-sign-stabilize" reduce to strategy/
policy-iteration convergence (Friedmann-hard), OR does the value-space vs
strategy-space distinction exempt D? **Ruling: the distinction is real but does NOT
give D a free pass — it lets you TRADE walls, not skip one.**

- **Value-space reading (accurate FW center each round):** the algorithm does
  cutting-plane localization of `x*` — each balanced cut halves volume, so it
  reaches the `2^{−poly}` optimality margin in **poly ROUNDS** by geometric
  shrinkage. This convergence is governed by volume-halving, NOT by a policy count,
  so **Friedmann/Fearnley do NOT apply** — D is *not circular* here. BUT computing
  the balanced/FW center needs a near-uniform sampler of `X_t` (the open wall). So
  in this reading D is the *existing* algorithm + a sound endgame certificate, **not
  a bypass**. It is stuck on the anisotropy/sampler wall.

- **Bypass reading (cheap centers, no accurate sampler — D's selling point):** drop
  the accurate center and the volume-halving guarantee is gone; the sign/candidate-
  policy dynamics is then a genuine strategy-improvement-like search, and **nothing
  shields it from Friedmann/Fearnley's exponential lower bounds** (their games are
  valid, realizable SSGs; HMZ's poly escape needs constant discount, but our regime
  is γ=1−2^{−poly}).

- **Net:** D does not escape a wall; it lets you *choose* which wall — sampler-
  mixing (value-space) or strategy-improvement-convergence (bypass). That choice has
  real value (a different, specifically-testable attack surface) but it is not free.

- **Two clarifications that strengthen the sound part:** (i) correctness need not
  rely on sign *stabilization* at all — near `x*` the residual sign encodes the
  *direction* of approach, not the policy; what matters is that `X_t` enters a
  single-policy linear cell (white-box detectable), then the exact certificate
  fires. (ii) The certificate is the one unambiguously sound, sampler-free
  contribution — keep it regardless of which reading wins.

Decisive experiment unchanged: run the FW-center pivot on **Friedmann's family at
γ→1**; poly rounds ⟹ the geometric/non-adversarial pivot escapes the lower bounds
(real); exp ⟹ D is the bypass wall, dead.

---

### Batch 2 (rogue_ideas.md: L, Q top; K, N, M, O support)

#### L — Spectral independence / round-resample (Glauber) dynamics on the cell distribution. **PROMISING → escalated (deepest, most-likely-to-close).**

The correct *modern* framework. Sample `π∈[d]^t` with `μ(π)∝vol(P_π)` (measure-
disjoint convex cells); round-resample = Glauber resampling `π_r | π_{−r}` (poly:
`d` convex volume-ratios per step). Mixing ⟸ **spectral independence** (Anari–Liu–
Oveis Gharan): `λ_max(influence matrix) = O(1)` ⟹ poly(d,t) mixing. Why this is
genuinely better than Route 1, not a restatement:

1. **Spectral independence tolerates elongation and holds past where conductance
   fails** (its whole raison d'être — it proves mixing up to phase-transition
   thresholds where Cheeger arguments break). This is exactly the tool that
   formalizes the notes' empirical "elongation is a harmless confound, only true
   dumbbells hurt" (`isoperimetry_summary §7`).
2. **Preserves the hard regime** (obstruction #1): parameters are `d, t`; `δ=2^{−
   poly}` enters only via bit-precision of volume computation. No `1/(1−λ)`.
3. **Dodges conv(X_t)=ℝ^d** (obstruction #2): works on the *discrete* cell-index
   distribution; each cell is convex, so no convex outer-approximation of the
   non-convex body is ever taken. Legitimate.
4. **It decomposes the wall into exactly the two obstructions the notes already
   localized, but WITH mixing theorems attached:** spectral-independence failure
   ⟺ a realizable **dumbbell** (high influence at a two-well split); marginal-
   boundedness failure ⟺ an exp-small essential cell = a **sliver**. So L is not an
   escape from the wall (a realizable dumbbell still gives `λ_max(I)=ω(1)`), but it
   is the *right* refinement — the same crux in a framework where a positive answer
   is an actual proof.

Honest caveats: (i) `λ_max(I)=O(1)` is still broken by a realizable dumbbell — same
wall, better shape. (ii) Need spectral independence under all *pinnings* + marginal
lower bounds (the sliver exclusion) — both match known obstructions. (iii) The
Lorentzian / down-up-for-free sub-claim (`Σ_π vol(P_π)∏z` log-concave) is a long
shot — volumes of arrangement cells are not known to be log-concave; **drop unless a
reason appears.** Influence-decay from "geometrically separated FW apexes" is
plausible but NOT rigorous (cells are global intersections; nested cuts are not
independent) — it's a conjecture to test, not a lemma.

Concrete next step (sent to main): enumerate cells for small d,t, estimate the t×t
influence matrix (perturb one round's conditioning, measure marginal shifts
elsewhere), compute `λ_max(I)` scaling in t on **realizable** trajectories. Stays
`O(1)` on realizable + blows up on adversarial/dumbbell ⟹ strong evidence,
reproduces the dichotomy in the modern framework. Grows with t on realizable ⟹ L
fails. This is the idea most likely to actually close if it holds; escalate.

#### Q — Fat star-cover (poly star pieces, union-sample). **PROMISING (2nd; genuinely different obstruction) → escalated.**

Non-star body = union of few star pieces, each LP-kernel-findable and exactly ray-
shot-sampleable; combine. Two corrections that improve it:

1. **The inclusion–exclusion worry is a non-issue.** Sampling a union of `k` sets
   needs NOT `2^k` terms — Karp–Luby union sampling is **poly(k)** given per-piece
   sampling + volume + membership (pick piece `∝vol`, sample, accept `1/#pieces
   containing point`). All available for star pieces. So the ONLY crux is `k`.
2. **The one open piece is the star-cover (illumination) number `k(X_t)=poly(d,t)?`**
   — a clean, well-defined geometric quantity. Crucially this is a **different
   obstruction from the dumbbell wall**: a dumbbell star-covers with ~2–3 pieces
   (a point in each lobe+neck sees its part), so Q may attack a regime the Cheeger/
   κ routes cannot. Q is **NOT** refuted by the C3 appendix (that killed the *single*
   kernel; a poly *cover* is a strictly weaker, untested question).

Honest caveats: `k` could blow up on a body with exp-many pockets/reflex features
(art-gallery-type blowup); no a-priori poly bound. Also FINDING a poly cover in poly
time (not just existence) is a second obligation (min star cover is NP-hard, but you
only need *some* poly cover — constructive question, also open). Single-star exact
sampling (sampling `∝ρ(u)^d` on the sphere) is asserted poly in `polytime.md §3.3`;
taken as given, not Q's burden.

Concrete next step (sent to main): greedily cover realizable `X_t` by nonempty-
kernel sub-bodies (add virtual constraints to restore a kernel), count pieces vs
d,t. Poly ⟹ genuine bypass of the dumbbell wall (pursue hard); exponential ⟹ Q has
its own (pocket-count) wall. This is the freshest possible-bypass in either batch.

#### N — Smoothed analysis of the γ=1 SSG as P-matrix LCP. **DEAD (existing program; hits the condition-number = hard-regime barrier).**

The search settles it: this is not new and it hits obstruction #1 head-on.
- Smoothed analysis of stochastic mean-payoff games is DONE — Boros–Elbassioni–
  Gurvich–Makino 2011 (link.springer.com/.../978-3-642-22006-7_13); condition
  numbers exist (Allamigeon–Benchimol–Gaubert–Joswig, arXiv:1802.07712, 2018;
  arXiv:2402.03975, 2024). Every bound is **poly IN THE CONDITION NUMBER / handicap**.
- P\*(κ)-LCP IPMs are poly in size AND in the handicap κ — confirmed. In the SSG
  hard regime the handicap/condition number is `2^{poly}` (it is the same quantity
  as `1/(1−λ)`), so "poly in condition number" = value-iteration/pseudo-poly
  territory. No worst-case poly.
- **The fatal tension (obstruction #1 in disguise):** smoothing needs perturbation
  `σ ≥ 1/poly` to give poly *expected* runtime, but rounding the perturbed solution
  back to the true exact rational needs `σ <` optimality margin `= 2^{−poly}`. These
  conflict in the hard regime: any σ small enough to round correctly gives runtime
  `poly(2^{poly})` = exponential. Smoothed = poly *expected over random instances*,
  not a worst-case algorithm for a fixed adversarial SSG.
DEAD as a path to SSG∈P; it is the existing weakly-poly frontier.

#### M — Tropical/max-plus Collatz–Wielandt bracket to pin optimal policy on 1/poly states/round. **FLAWED / DEAD-leaning (poly part is only the 1-player relaxation; the pinning fraction has no mechanism).**

- The poly-computable part (max-plus eigenvalue / min-mean-cycle via Karp) is real
  but only for the **deterministic (1-player)** skeleton; the 2-player mean-payoff
  value is open (obstruction #3), and stochastic mean-payoff condition-number bounds
  (Gaubert et al., above) are again condition-dependent, not poly.
- The load-bearing "pin optimal policy on 1/poly states/round" has **no mechanism**:
  Collatz–Wielandt gives a value *bracket*, not a per-state policy certificate, and
  nothing forces a 1/poly fraction to be tight each round.
- Fixable ONLY coupled to D (feed bracket-certified states as partial policies into
  D's exact certificate); standalone it pins nothing. Subsumed by D; low priority.

#### K — MSS / interlacing polynomials to certify a well-conditioned cut exists. **DEAD-leaning (no family to interlace over).**

MSS/interlacing needs a *rich family* of admissible choices to run the barrier
method. Here the cut is **oracle-forced** (sign `s=sign(f(c)−c)` fixed) and the
balanced center is essentially **unique** (FW minimizer); ties are measure-zero. So
there is no family to average — rogue's own caveat is the killer. Alive ONLY if
extra queries manufacture a family of admissible cuts at nearby centers — which
reduces to the **Corollary C** question (can poly(d) extra queries narrow the index
set), a separate open lead. Not independently promising.

#### O — Persistent homology of the −dist offset filtration. **DEAD (≡ Cheeger wall + false ball-preservation step + exp-cost PH).**

Triple-dead: (i) persistence of the erosion filtration *measures* neck width = the
Cheeger bottleneck — the wall restated as a certificate, not an escape (obstruction
#5). (ii) "ball-preservation ⟹ bounded erosion ⟹ h≥1/poly" is FALSE — ball-
preservation is local at `x*`; a dumbbell can be fat at `x*` yet have a thin neck to
a far lobe, unconstrained (same gap that killed ball-preservation⟹λ_min,
`isoperimetry_conditioning §4`). (iii) computing PH of a d-dim non-convex body needs
an exp-in-d mesh. Low.

---

**Batch-2 bottom line.** Two escalations: **L** (spectral independence — the right
modern framework, preserves the hard regime, dodges convexity, decomposes the wall
into the two known obstructions but WITH mixing theorems; most likely to *close* if
`λ_max(I)=O(1)` holds on realizable trajectories) and **Q** (fat star-cover — the
one route whose obstruction, the star-cover number, is *different* from the dumbbell
wall; inclusion–exclusion worry dissolved via Karp–Luby). N is dead (existing
condition-number program, hard-regime barrier). K/M/O dead or subsumed. Sources:
Anari–Liu–Oveis Gharan (spectral independence), Karp–Luby union sampling,
Boros–Elbassioni–Gurvich–Makino 2011, arXiv:1802.07712, arXiv:2402.03975, P\*(κ)-LCP
IPM literature.

**Cross-batch ranking (rogue's standing question — what to run first):**
1. Cheapest decisive (binary outcomes, already sent): **A** Jacobian, **D** Friedmann
   test.
2. Deepest / most likely to close: **L** influence-matrix experiment.
3. Freshest possible-bypass (different obstruction): **Q** star-cover count.
B's cell-graph test is cheap and worth folding into the same enumeration as L
(same cell machinery). C/E/F/G/I/K/M/N/O: dead or reduce to equally-open problems.

---

### RIGOR RULING (team-lead): does μ_W ≤ 1 (⟹ κ~√t poly) imply SSG∈P?

**Ruling: (b) — necessary but NOT sufficient. It needs an additional, precisely-
stated no-central-dumbbell (well-roundedness) lemma, which is itself open. And
`crux_scalefree.md` is internally inconsistent on exactly this point.**

1. **The internal inconsistency.** §8.3's reframing box asserts κ~√t "**suffices for
   SSG∈P**." But §11 of the *same file* lists "a well-roundedness volume-ratio
   bound" as a **second irreducible ingredient** alongside κ-control. §11 is
   correct; §8.3's parenthetical over-reaches. The μ_W framework is excellent as a
   statement *about κ*; it does not by itself give SSG∈P.

2. **Why poly κ ⊉ poly mixing here (obstruction #4, convexity smuggling).** "poly κ
   ⟹ one whitening + hit-and-run mixes" is a **convex-body** theorem (Lovász–Vempala
   isotropic hit-and-run / KLS). `X_t` is non-convex (`conv=ℝ^d`); invoking it
   smuggles convexity. `isoperimetry_summary §0` states the caveat explicitly: route
   2 works "**provided the whitened body isn't a dumbbell**."

3. **Explicit witness: bounded κ permits a central-valley dumbbell.** Take the unit
   ball and delete a thin central slab `{|x_1|<δ}` down to a thin bridge. The removed
   mass sits at the **center** (`x_1≈0`), so it is second-moment-light: `Σ ≈
   (1/(d+2))I`, `κ ≈ 1`. Yet the body is nearly two disconnected half-balls, so
   Cheeger → 0. So a non-convex body can have `κ=O(1)` and exponentially small
   conductance. Bounded κ does **not** rule out the central-valley dumbbell.

4. **What bounded κ DOES rule out:** angular **spikes** (`κ~θ^{−2}`, crux §5) and
   **far-lobe** dumbbells (a lobe at Ω(1) distance adds large `λ_max` ⟹ large κ). The
   residual — and it is exactly the residual — is the **central-valley** dumbbell,
   whose neck sits near `x*` precisely so it stays second-moment-light.

5. **The additional lemma needed, precisely.** A well-roundedness / volume-ratio
   bound `vol(X_t) ≤ poly(d,t)·vol(B_∞(x*,ρ_t))` (the preserved ball is a `1/poly`
   mass fraction, up to `(1+o(1))^d`). Via crux_scalefree **Lemma 10.1** (§10) — a
   contained ball dominates a *central symmetric unimodal bump* in **every** direction
   at relative mass `vol(B)/vol(X)` — this bound fills every central valley at
   `1/poly` mass, forbidding exactly the residual central-valley dumbbell. This is
   the **same well-roundedness wall** §10.2 / `conditioning §4` already isolated, and
   it is **open** (= the C2≡Open-Lemma wall in its well-roundedness form).

6. **Net.** μ_W ≤ 1 would be a real advance — it kills the *κ-blowup* (exponential-
   anisotropy) failure mode, converting "is the conditioning route viable?" into "does
   well-roundedness hold?". But it does **not** close SSG∈P; the volume-ratio bound is
   a genuinely separate, still-open co-requirement that none of the current κ-directed
   ideas (A/V/W/X) address. So the μ_W experiment, if favorable, **advances but does
   not close** the conditioning route — and the highest-value *un-attacked* target is
   now the well-roundedness volume ratio, not more κ work.

Note this is *not* simply option (c) (the earlier star-regime conditional): μ_W≤1
gives poly κ but **not** star-shapedness (the body isn't star past kernel collapse),
so the star conditional `star + κ≤K ⟹ h≥1/poly` (conditioning §5) does not fire. It
is genuinely (b): a new, precisely-stated, still-open lemma is required.

Sources: Lovász–Vempala (isotropic hit-and-run mixing), KLS/Chen (convex only),
`isoperimetry_summary §0/§4`, `crux_scalefree §10–11`.

---

### Batch 4 (rogue_ideas.md: V, W, X — all aimed at the κ residuals)

Context: rogue correctly conceded Idea R (crux §4 refutes clean per-cut alignment).
V/W/X target the two residuals (bound `a(v_min)`; non-persistence of "v_max blind ∧
v_min sensed"). **All three attack κ only — none addresses the well-roundedness
co-requirement the μ_W ruling exposes, so even best-case they advance, not close.**

#### V — Perron–Frobenius forces the long axis into the sensed cone. **FLAWED-BUT-FIXABLE (highest-leverage; one real gap) → escalate with the gap flagged.**

The genuine merit: it's the first *mechanism* (not a hope) for the §5/§9.3 SSG
lever. Chain: local linear piece `x↦γP_σx+r`, `P_σ≥0`; nonneg directions `v≥0` are
**sensed** (`g(av)=a(max v+min v)`, `max v>0,min v≥0` ⟹ `σ=sgn(a)` ⟹ `ρ` large) —
this step is **correct**; the nonneg orthant is in the sensed cone and the blind
anti-diagonals are far from it. **The gap:** the PF conclusion "leading eigenvector
nonneg" applies to **entrywise-nonnegative matrices**, but `Σ(X_t)` is a
**covariance**, whose off-diagonals `Cov(y_i,y_j)` can be **negative**. `P_σ≥0` does
**not** transfer to the sign structure of `Σ(X_t)`. So "PF ⟹ `u_max` nonneg" is a
non-sequitur as written. **The make-or-break sub-lemma:** the uniform measure on
`X_t` is **positively associated** (FKG-type, `Σ⪰0` entrywise), or directly `u_max ∈`
nonneg/near-diagonal cone. This is *not* given — SSG value coordinates can be
anti-correlated — and the cone/max-min coupling of the cut is not obviously FKG.
Also needed: `u_min` in the blind cone (preserved) for κ to actually contract, not
just `u_max` sensed. **Concrete next step (sent to main):** rogue's proposed
measurement is exactly the decisive test — log `‖u_max^+‖/‖u_max‖`, `∠(u_max,𝟙)`,
sign-mixedness `|max u_i + min u_i|` for `u_max` AND `u_min` on realizable SSG bodies,
correlated with κ-drops. If `u_max` is empirically nonneg/sensed and `u_min` blind on
realizable trajectories, that's strong support and the sub-lemma to prove is positive
association. If `u_max` is often anti-diagonal, V is dead. Escalate — but the PF-to-
covariance step is the crux and must be closed by a positive-association proof, not
asserted.

#### W — Furstenberg/Oseledets non-persistence via frame rotation. **DEAD-leaning (superseded by crux §9, which rogue may not have fully absorbed).**

W's mechanism is "recentering re-randomizes the active cells = **rotates the
frame**," giving a random matrix product whose projective chain mixes (Furstenberg).
But crux_scalefree **§9.1–9.2 (already proved)** says the exact opposite: the blind
cone is **axis-anchored and recentering-INVARIANT** — recentering is a *translation*
of the apex; `max`/`min` are over *fixed* coordinates, so no FW center rotates them.
So the frame does **not** rotate; W's premise is false. What §9.3 leaves is that any
non-persistence comes from the **discrete** sign/active-set reselection driven by the
**SSG operator** — i.e. V's/§5's question, not an independent random-matrix fact.
Two further problems: (i) Furstenberg needs **random / stationary-ergodic** products;
the SSG trajectory is **deterministic**, so the theory may not apply; (ii) the
operator sequence's strong-irreducibility/contraction is exactly what's unknown.
**W collapses into V.** Keep only its diagnostic (autocorrelation time of `ρ(u_max)`),
which pairs with V's test.

*Answer to W's linchpin — measure of the blind cone on the sphere:* the **exactly**-
blind set `{v: max v + min v = 0}` is codimension-1 (measure zero), but **strong
sensing (`ρ=Ω(1)`) requires alignment** with the structured directions (coordinate
axes, main diagonal, nonneg orthant). A **generic/random** direction is only
**weakly** sensed: for random `v`, `max v` and `min v` are both `≈ ±√(2ln d/d)` at
*different* coordinates, so `max v + min v` is a small random-sign quantity — neither
strongly sensed nor exactly blind. So "usually **strongly** sensed" is **false**;
sensing is an alignment property, which is precisely why everything hinges on V
(does the operator force `u_max` to align?) and *not* on genericity. This **undercuts
W's "genericity ⟹ non-persistence" hope** and reinforces V. (Clean cheap test:
sample random unit `v`, compute the `ρ(v)` distribution vs `d` — spec to main.)

#### X — Bound a(v_min) directly via skewness. **FLAWED-BUT-FIXABLE (hits the same volume-ratio wall); good clean refutation test.**

Correctly identifies `a(v_min)=E[s²σ]` as the sole crux (matches crux §2) and
proposes a **third-moment (skewness)** handle: `a` is nonzero only via a skew
coupling of `s²` with `σ`. Two issues: (i) "parity ⟹ `a≈0` for a symmetric/blind
marginal" is **heuristic** — `σ=sgn(g)` depends on *all* coordinates, not purely
odd/even in the single projection `s`, so the parity cancellation isn't exact. (ii)
The ball-preservation control of skewness is via Lemma 10.1's central bump, which is
symmetric but only carries mass `vol(B)/vol(X)` — so X bounds `a(v_min)` **only at
the well-roundedness floor**, hitting the **same volume-ratio wall** as the μ_W
ruling. So X is the `a(v_min)` crux re-expressed via skewness, **not** an independent
escape. Its refutation test is clean and worth running (already in the repair
harness): correlate `sign(a(v_min))` with thin-marginal skewness and sensed/blind
class; **large-negative `a` with a SYMMETRIC thin marginal ⟹ the skewness bound is
false.**

---

**Batch-4 bottom line.** **V** is the one to escalate (first real *mechanism* for the
SSG lever) but its PF→covariance step is a genuine gap requiring a **positive-
association (`Σ⪰0` entrywise)** proof — the make-or-break, testable by rogue's own
proposed measurement. **W** is superseded by crux §9 (recentering does not rotate the
axis-anchored frame) and collapses into V; the blind cone's exactly-blind set is
measure-zero but strong sensing is an *alignment* property, so genericity does not
help. **X** correctly re-expresses the `a(v_min)` crux via skewness but hits the same
well-roundedness wall. **Overarching redirect:** the μ_W ruling shows κ-control is
necessary-not-sufficient; the highest-value *un-attacked* target is now the
**well-roundedness volume-ratio bound `vol(X_t) ≤ poly·vol(B_∞(x*,ρ))`** (§10.2) —
rogue should aim ideas there, not only at κ. Sources: Perron–Frobenius, FKG/positive
association, Furstenberg–Oseledets, crux_scalefree §9–11.
