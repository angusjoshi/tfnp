# Research log — poly-time `ℓ∞`-contraction fixed points

Single catch-up index for the session. Newest first.

## Where the open problem stands

Goal: `poly(d, log 1/ε)`-**time** algorithm for `ℓ∞`-contraction fixed points
(⟹ `SSG ∈ P`, a famous open problem — so a full proof is a breakthrough, and no
proof here is fabricated). The whole thing has been reduced to **one** question,
now sharpened twice:

- **Reduction** (`notes/hitrun.md`): poly-time ⟸ poly-time uniform sampler for
  the non-convex `X_t = box ∩ ⋂_r K(c^r,s^r)`. Everything else is proved (and
  Lean-formalized, below).
- **Isoperimetry form** (`notes/isoperimetry_attack.md`): sampler is poly ⟸
  Cheeger `h(X_t) ≥ 1/poly`. Difficulty localized to **anisotropy**; the star
  regime is fully solved (Theorem A); the unrestricted lemma is false but
  non-realizable (sliver obstruction).
- **Conditioning form / C2** (`notes/isoperimetry_conditioning.md`): if the
  covariance condition number `κ(X_t)` stays poly, one whitening + hit-and-run
  gives poly mixing. **Empirically confirmed** (me, this session): `κ ≈ 2–3`,
  sub-linear in `d`, per-cut ratio `≈1` for *balanced* cuts; adversarial cuts
  both fail to shrink and worsen `κ`.
  **Theorem progress (agent, verified):** for `X` *symmetric* about its center, a
  balanced cut is exactly a **rank-1 downdate** `Σ(X∩K)=Σ(X)−m_K m_Kᵀ` — `λ_max`
  never grows, the lost direction `m_K` aligns with the *longest* axis, so the cut
  self-corrects (`κ` contracts; verified `100→27`, `906→228`). Also: `λ_max ≤
  min(2λ_max, d/4)` unconditional (whole question is a `λ_min` lower bound); box
  base case `κ=O(1)→1`; obstruction — `κ` blows up only if the removed half is an
  oblique off-center lobe. **Open:** the *asymmetric* per-cut bound (real bodies
  have `O(0.2)` reflection-defect) and the graded-spectrum multi-cut trajectory.
  Also: general decomposition `(D)`, box base case `κ=O(1)→1`, and a star-regime
  conditional `κ poly ⟹ h poly`. **Reliability caveat:** both samplers are
  trustworthy only to `d≈12, t≈2d` (exact rejection to `t≈13`); C2 is empirically
  positive *within* that window but genuinely unmeasured in the large-`d` hard
  regime — apparent blow-ups past the ceiling are sampler artifacts, not evidence.
  **Cycle 3 (important negative):** proved the mean-shift lemma (§8, bathtub
  bound: any ½-set's conditional-mean shift ≤ that of the extremal half), giving
  the conditional "no dumbbell 1-D marginal ⟹ `κ(X∩K) ≤ κ(X)/c`". But the
  Lyapunov attempt failed honestly (no monotone potential; `κ` bounded-*with-drift*
  `2–9`, top-axis alignment is intermittent). Key meta-result: **C2 ≡ the Open
  Lemma** — removing the non-dumbbell hypothesis = proving the cut's `m_K` never
  aligns with a thin direction = raw isoperimetry. So the conditioning route is
  *not* strictly easier. Genuine new handles gained: the rank-1 structure (only 1
  direction at risk per cut) and the anisotropy-growing restoring force.
  **Cycle 4 (reframing, both honest negatives):** (A) `spread = Σ(logλ_i−mean)²`
  IS a monotone Lyapunov for the idealized symmetric downdate dynamics — but it
  does *not* bound `κ`, because a pure downdate only *removes* variance and can
  never repair a thin axis (the symmetric idealization is actually *worse*
  conditioned). **Key insight:** what keeps the *real* `κ` bounded is exactly what
  the symmetric model drops — (i) the isotropic start (box `X_0`, a stable fixed
  point) and (ii) the *asymmetric* term `2Σ(X)−Σ(R)` which can *inject* variance
  into thin axes. So **asymmetry is the repair mechanism, not a defect** — the
  right target is "asymmetric repair out-paces thin-axis creation." (B) FW-optimality
  ≡ balancedness (no extra leverage; corrects an earlier premise), and identity
  `m_R+m_K = 2(centroid−c)` — the reflection-defect is twice the FW-center-to-centroid
  distance, uncontrolled since balancedness equates masses not centroids.
  Agent flags **diminishing returns** absent a genuinely new idea. C3 (block-restart
  exact sampler) queued as the last distinct route; else consolidate.
  **Cycle 5 — C3 dead, loop concluded.** C3 fails cleanly: the certifiable (LP)
  kernel is *monotone shrinking* (`kernel(X_{t+1}) ⊆ kernel(X_t)`, each cut only
  adds constraints), so it can never recover once empty (~`t=d/2`); the true
  kernel empirically doesn't recover either (0–1 lucky rounds, `d=6,8,10`). So C3
  ≡ the star/flat-gap regime — same anisotropy wall.
  **⇒ `notes/isoperimetry_summary.md`** (self-contained, 9 sections) is the
  consolidated deliverable. Organizing meta-result: the three routes to a sampler
  (Cheeger `h`, conditioning `κ`, exact star-sampler) all reduce to ONE
  obstruction — a realizable anisotropic/dumbbell `X_t` — each `≈ SSG∈P`. Loop
  wound down (diminishing returns, crux confirmed hard from every angle). Freshest
  un-pursued lead, if ever resumed: "asymmetric repair out-paces thin-axis creation."
  **Cycle 6 (λ_min empirics, `notes/repair_attack.md`, capped d≤6/t≤10, exact rejection):**
  T1: scale-free `1/κ` stays `[0.11,0.73]` over `t≤10` — bounded-with-drift, not a
  proven plateau. T2 (**corrects the Cycle-4 "asymmetry repairs" story**): asymmetric
  injection genuinely repairs only on isotropic-`x*` (topical) instances; on the HARD
  spread-`x*` SSG instances the thin axis survives instead by **downdate-orthogonality**
  (`¼ΔΔᵀ` aligns with the LONG axis, so the cut *misses* the thin axis). T3 (**clean
  positive**): `Var_R(v)+½(v·Δ)² ≤ (2−c)Var_X(v)` holds 60/60 cuts, worst `c=+0.70`
  (conservative). Confound caught & quarantined: same-split kept-half is Marchenko–Pastur
  biased (~30% small-eigenvalue deflation at d=6) — an apparent "thin-axis migration"
  ruled an artifact. **Sharpened target:** T3 alone gives only `κ ≤ (1/c)^t`; the real
  goal is scale-free `κ(X∩K) ≤ (1+o(1))κ(X)` ⟺ `Δ` aligns with the TOP eigenvector,
  never the bottom — T2 shows this is *intermittent*, hence still open (=SSG∈P).
  Lean: `starshaped_of_kernel`(`_family`) verified (build + axioms).

## Lean formalization (all `sorry`-free; builds; axioms `propext`/`Classical.choice`/`Quot.sound`)

- `Tfnp/HitRun.lean` — per-round correctness geometry: `fixedPoint_mem_pyrUnion_apex`
  (apex cut validity), `linfDist_self_map_le`/`isApproxFixedPoint_of_near`
  (extraction), and **Theorem A** `starshaped_of_toward`(`_family`) (toward-cuts ⟹
  star-shaped about `x*`), and `pyrUnion_subset_halfspace` (`|support| ≤ 2` ⟹ the
  cut is a halfspace ⟹ convex regime; the `d≤2` / post-narrowing poly-time basis),
  and `exists_pair_pyrUnion_subset_halfspace` (`d ≤ 2` ⟹ every cut is a halfspace ⟹
  candidate region convex ⟹ poly-time base case, complete), and `starshaped_of_kernel`
  (`_family`) — star-shapedness about an *arbitrary* center `z` satisfying the
  (diagonal-inclusive) kernel condition, generalizing `starshaped_of_toward` from
  `x*` to any all-nonneg center. NOTE: the `∀ i j` form = "all `wᵢ(z)≥0`" (same as
  toward); the genuinely-different **off-diagonal `ker K` (`∀ i≠j`, `k≥2`) iff is
  still open in Lean** (converse is false for the diagonal form — d=2 counterexample).
- `Tfnp/PolyTime.lean` — unit-cost model (stated caveat): `costedRun_le`,
  `round_cost_le`, `hitrun_time_poly` (total cost ≤ poly given poly oracles), and
  `endToEnd` (correctness **and** poly-time given a good sampler). Pure query model
  (`Tfnp/Algorithm.lean`, `cly_query_complexity`) kept separate and untouched.

## Notes / experiments

- `notes/hitrun.md` — the reduction + Lean status.
- `notes/polytime.md` §3.3 — kernel theorem, star-shape collapse, hit-and-run algo.
- `notes/isoperimetry_attack.md` — first agent pass: Theorem A, ball-preservation,
  sliver obstruction, dichotomy evidence, confound controls.
- `notes/isoperimetry_conditioning.md` — C2: `κ` growth (empirics done, positive;
  theorem in progress).
- `notes/polytime_experiments/` — all scripts (`venv` has numpy/scipy). C2:
  `conditioning.py`, `cond_adv.py`.

## Session activity

- Formalized Theorem A (star regime) into `HitRun.lean`.
- Ran C2 empirics directly (agent hit repeated API errors): exact-rejection `κ`
  measurement across `d=5,7,9`, `δ=10⁻³…10⁻⁵`, SSG + topical; balanced-vs-adversarial
  center comparison. Result: no per-cut `κ` blow-up for balanced cuts.
- Agent re-dispatched on the **C2 theorem** (`κ(X∩K) ≤ C·κ(X)` for balanced cuts)
  + needle-through-center localization. Will keep driving it on each report.

## Multi-agent solve-push (cycle 7+) — reasoning agents, zero laptop load

Four reasoning/literature agents (no local compute; heavy compute serialized through
main): `rogue-ideas` (wild cross-field connections) ↔ `advisor` (rigor gate);
`ssg-directions` (established SSG∈P routes); `crux-prover` (scale-free κ lemma).

- **`ssg-directions` (`notes/ssg_directions.md`) — delivered.** Key reframing: our
  method is a **value-space** cutting-plane algorithm; all classical routes (policy
  iteration, USO, P-LCP, random-facet) are **strategy-space**. So the strategy-space
  lower bounds (Friedmann exponential; Christ–Yannakakis smoothed) **do not apply**,
  and Manthey et al. ICALP'24 (smoothed-poly = value-gap condition number) holds only
  for *deterministic* games — our stochasticity-indifferent value-space κ is a
  plausible crossing of that barrier. Placement: SSG ∈ **UEOPL**; our ℓ∞-contraction
  fixpoint is a named UEOPL problem. Most promising bridge: **Condition-Number
  Transfer** — value-gap δ controls κ(X_t). CAVEAT (honest): worst-case hard SSG has
  δ=2^{−poly}, so this likely gives **condition-number/smoothed poly-time for stochastic
  games** (new, crosses Christ–Yannakakis), NOT worst-case SSG∈P. Go/no-go experiment
  (δ vs 1/κ, h_iso) dispatched to `lambdamin-explorer` (capped) → `notes/condition_transfer.md`.

- **`crux-prover` (`notes/crux_scalefree.md`) — 3 rigorous results.** Exact per-direction
  factor `c(v)=1+a(v)−ρ(v)²`; scale-free `ΔᵀΣ⁻¹Δ ≤ 4` (downdate alone can't make λ_min
  negative ⟹ the *sole* κ-risk is the scalar `a(v_min)`); blind-cone structure ⟹ the
  clean per-cut "Δ↔top-eigenvector" alignment is **provably not a theorem** (intermittency
  is structural). Wall reduced to: a diagonal (non-axis) dumbbell with a **blind long axis
  that persists**. Decisive experiment (ρ(v_max)-vs-κ mean-reversion) queued → `crux_experiment.md`.
- **`advisor` (`notes/advisor_verdicts.md`) — Batch 1 vetted; escalated Idea D.**
  **Idea D** = the one genuinely new direction: FW-center strategy-improvement pivot +
  **sampler-free certificate** (solve `(I−γP_σ)x_σ=r_σ`, check Bellman optimality ⟹ `x_σ=x*`
  exactly). Drops the isoperimetry wall; swaps it for a pivot-convergence wall. Caveat:
  standard pivots have exp lower bounds (Friedmann'09, Fearnley'10) at `γ→1` — **D lives
  iff the value-space FW-center pivot escapes Friedmann's construction.** Decisive test:
  encode Friedmann's family (ssg-directions authoring `friedmann.py`), measure
  rounds-to-stabilize vs n at γ→1 (lambdamin, light center estimation). Rest of Batch 1
  dead/reduces-to-open (B≡Cheeger, C RMT category error, I≡Tarski). Unused hooks flagged:
  SSG-map monotonicity, removed=reflection-of-kept.
- **Compute pipeline (one serial stream via `lambdamin`, laptop-safe):** condition_transfer
  → crux_experiment → Jacobian (idea A) → Friedmann pivot (idea D, top priority, pending
  `friedmann.py`). `rogue-ideas` on Batch 2 (sampling-bypass + monotonicity/reflection hooks).

- **Condition-Number-Transfer experiment (`notes/condition_transfer.md`) — soft NO-GO.**
  Over 4 decades of δ (value gap ∈ [2e-5, 0.33]), κ∈[2.1,10.9], h_iso∈[0.33,0.61], NO
  power-law (slopes ≈0, R²≤0.27); "dumbbell-width ≥ δ" mechanism contradicted (smallest-δ
  = best-conditioned). **Key redirect:** `X_t`'s conditioning is set by the **sign-pattern
  (orthant) trajectory of the cuts — a combinatorial object — not the scalar δ** (two
  instances at 57× different δ, same sign history ⇒ byte-identical κ,h). So the right
  transfer object is combinatorial (which strategy pairs stay active), reinforcing the
  Idea-D policy/sign frame. Soft (not hard) because reliable window t≤6 is pre-dumbbell.
  Added `make_ssg_full`+`ssg_value_gap` to common.py (pure additions).
- **`crux-prover` §8 — THE reduction (being measured):** shape-map symmetry is `S_d` ⟹
  fixed point is equicorrelation `Σ*`, Jacobian = 4 Schur scalars; symmetric part is
  **neutral** (`μ_std=μ_W=1`) on κ-dangerous modes ⟹ κ-drift is a mean-zero **random walk,
  κ~√t (poly, suffices for SSG∈P)** unless the asymmetric term makes `μ_W>1`. Whole crux ⟹
  **is `μ_W ≤ 1`?** μ_W finite-difference (§8.5, real cut body) dispatched to lambdamin as
  top priority → `notes/mu_W_experiment.md`. Open gaps under vetting: (i) local
  linearization (basin/global); (ii) does `μ_W≤1 ⟹ SSG∈P` or hit the C2 fat-dumbbell wall
  (advisor ruling).

- **`crux-prover` §9–11 + `advisor` Batch-2 — convergence + two new escalations.**
  crux non-persistence angles both resolve to rigorous NEGATIVES that converge: (1) the
  anti-diagonal blind cone is **recentering-invariant** (sensed/blind split anchored to
  ambient axes) ⟹ non-persistence must come from the **SSG operator** controlling `v_max`
  orientation; (2) ε-net is free (central-bump lemma) but insufficient ⟹ need a
  **volume-ratio well-roundedness** bound `vol(X_t) ≤ (1+o(1))^d vol(B)`. These + lambdamin's
  "conditioning = sign-pattern history, not δ" all point at ONE object: the SSG operator's
  sign/strategy dynamics — unifying the conditioning and Idea-D policy routes. Live targets:
  (a) SSG-operator orientation control (→ μ_W/mean-reversion experiment), (b) volume-ratio
  well-roundedness (crux, on paper).
  **advisor ruling on D:** trades walls (accurate centers ⟹ needs sampler; cheap centers ⟹
  strategy-improvement, exposed to Friedmann) — NOT a free bypass; keep the sound endgame
  certificate; Friedmann test decides. **advisor Batch-2 escalations:** **L** (spectral
  independence / Glauber round-resample on the discrete cell distribution — the modern tool;
  dodges conv=ℝ^d, tolerates elongation; λ_max(influence matrix)=O(1) ⟺ rapid mixing — top
  pick to *close*) and **Q** (fat star-cover — a DIFFERENT obstruction than the dumbbell;
  Karp-Luby union-sampling makes it poly-not-2^k). DEAD: N (smoothed LCP = poly-in-cond-number
  = 2^poly), M/K/O. Run-order: μ_W, D-Friedmann, L, Q (one serial compute stream).

## PIVOT (cycle 8): conditioning family exhausted → Idea D (policy certificate)

- **Conditioning/isoperimetry route THOROUGHLY BLOCKED.** (i) Mean-reversion experiment
  (`crux_experiment.md`): identities validate (`ΔᵀΣ⁻¹Δ≤4` confirmed) but persistent BLIND
  long axes are realized (d6 s1: 5 rounds, κ 3→15.6) ⟹ the non-persistence lemma is
  empirically false. (ii) advisor ruling: `μ_W≤1` is necessary-NOT-sufficient (poly-κ⟹mixing
  smuggles convexity; witness: ball minus central slab has κ≈1, Cheeger→0); reduces to a
  well-roundedness lemma. (iii) crux §12: well-roundedness ALSO insufficient (far-corridor
  counterexample: vol-ratio O(1), corridor bottleneck) ⟹ reconverges on the Open Lemma.
  Net: κ, well-roundedness, spectral — every sub-route of the geometric family reduces to
  genuine isoperimetry = SSG-hard. **Route effectively dead for worst-case.**
- **LIVE ROUTES now:** **Idea D** (sampler-free policy-certificate; `friedmann.py` ready —
  honest choice: validated **Melekopoglou–Condon 1994** exp PI lower bound, `simple_pi`=2ⁿ−1
  self-certifying). Decisive test RUNNING: `run_certified` on `mc_basic(n=6..14)`, FW-center
  pivot rounds-to-stabilize vs `2ⁿ−1` — poly ⟹ dodges the strategy-improvement wall (major),
  exp ⟹ dies cheap. **Q** (fat star-cover — its death-shape, exp pockets, is *orthogonal* to
  the corridor/dumbbell wall, so may survive where the rest died; submodular greedy cover).
  **M1** (monotone convex order-interval; cheap test running) + active-set flatness (Cor. C).
- Convergence theme: κ / well-roundedness / policy all live on the **sign-pattern (strategy)
  combinatorics** — conditioning↔policy are one object.

- **Idea D tested myself (no subagent) — preliminary NEGATIVE for the sampler-free bypass**
  (`notes/idea_d_mc.md`). On the validated Melekopoglou–Condon exp PI lower bound
  (`friedmann.py`; `simple_pi`=2ⁿ−1 confirmed), the cheap-center `run_certified`
  rounds-to-stabilize = 8, 28 for n=4,5 (vs 2ⁿ−1 = 15, 31; ratio climbing 0.53→0.90),
  and n=6 did not certify within 90 rounds. So the *cheap sampler-free center* does NOT
  give convincingly-poly rounds — consistent with the advisor's "D trades walls" ruling
  (accurate FW center ⟹ poly by volume-halving but needs the sampler; cheap center ⟹
  reverts toward strategy-improvement, MC adversary bites). Does NOT test the accurate-center
  version, so not a full refutation. The sound piece that stands: the sampler-free Bellman
  **certificate** (`certify`) — exact yes/no + exact x* on pass. (Ran capped/serial, laptop-safe.)

## Status after usage-limit reset — agent scorecard & conservative plan

Agents (now stopped on shared usage limit): **crux-prover** (MVP — all results verified),
**advisor** (essential rigor gate), **lambdamin** (clean confound-controlled experiments),
**ssg-directions** (value-space framing + friedmann.py), **rogue-ideas** (mostly killed;
surfaced D, M1). Going conservative: doing high-value experiments **myself** (one capped
serial compute stream), re-spawning agents only when a specific reasoning task needs it.

- **M1 + Corollary C tested myself — both DEAD** (`notes/m1_orderinterval.md`). On hard SSG
  (d=4,5,6, γ→1): all-one-sign (free convex cut) rounds only 0–9%; convex order-interval
  width shrink rate 0.95–1.00 (no gain, several never update); active-set |A(c)|=Θ(d)
  (max=d always). So monotonicity gives no usable convex bypass and the cut support can't be
  narrowed to two coords — the |S|≥3 non-convex regime is the norm. (Capped, laptop-safe.)
- **Q (fat star-cover) — one small agent (`star-cover`) assessing.** The last route whose
  death-shape (lobe/pocket proliferation) is *orthogonal* to the dumbbell wall; assessing
  whether k(X_t)=poly(d,t) or blows up, + a capped experiment spec. Team kept small.
  **Q assessment + experiment (I ran it, capped) — the session's most POSITIVE signal.**
  Provable orthogonality: dumbbell is Q-EASY (k≈2-3) but Cheeger-hard; comb is Q-HARD
  (k=Θ(teeth)) but Cheeger-easy ⟹ Q is NOT dumbbell-wall-equivalent (relocates hardness to
  the art-gallery count k; provable bound k≤(d²t)^d = poly-in-t, exp-in-d). Experiment
  (`notes/star_cover.md`, exact rejection): calibration valid (dumbbell k=2, comb m→k=m);
  **realizable SSG X_t has k=1 at t=d and k=1–2 at t=2d** (d=3,4,5), robust to coverage
  target 0.999 and visibility resolution nseg=120 — essentially **star-shaped from one
  point** in-window, so the Karp–Luby sampler is trivially poly there. TENSION with C3
  (certifiable kernel empties, best witness 50–90%): resolution = the TRUE kernel appears
  nonempty even when the CERTIFIABLE (pairwise-sum LP) kernel empties (star-cover proving).
  Caveats: d≤5 ceiling can't see the exp-in-d bound; suggestive not decisive.

## Honest bottom line (this session)
`SSG∈P` NOT solved (it's the target, genuinely hard). But: (1) real Lean partial results
banked (star regime, halfspace/d≤2, apex cut, extraction, endToEnd, all sorry-free); (2) a
dozen tempting shortcuts cleanly killed with reasons (conditioning/κ/μ_W, well-roundedness,
Idea-D cheap-center, M1, Corollary C — all reduce to the isoperimetry/sign-pattern core);
(3) ONE route (Q, fat star-cover) survives in-window with a positive signal and is provably
orthogonal to the wall that killed the rest — the live lead. Everything reduced to the
sign-pattern/strategy combinatorics.

## Q d-scaling — ceiling hit; route now rests on the proof
`cker ⊆ tker` proven (star-cover §4): C3 killed only the *certifiable* kernel, star-shapedness
survives. d-scaling probe (d=6,7,8): k(t=d)=1–3, k(t=2d) mostly 1–2, one unconfirmable
outlier (d=7 s1: k=12 on a vol≈2⁻¹⁴ under-sampled body — likely artifact). **The d-scaling
of k is unmeasurable past d≈6–7** (deep-t bodies need the very sampler we're building —
circular). So Q, like everything, ultimately rests on a PROOF: `k(X_t)=poly(d,t)` for
balanced cuts (pinwheel/non-interacting-reflex-ridge bound) — star-cover on it; if it can't
move, that's the terminal state. Net: Q remains the one route provably orthogonal to the
dumbbell wall, with encouraging-but-ceiling-limited empirics and an open proof target.

## TERMINAL (this session) — consolidated in notes/FINAL_REPORT.md
star-cover §5: cannot prove k=poly nor certify a realizable counterexample. Precise reason:
reflex HYPERPLANES additive O(d²t), but guard count = reflex PIECES = (d²t)^{d-1} (exp-in-d
arrangement blowup); d=2⟹k=1 (convex anchor); balancedness controls new-pocket LOCATION
but not far-pocket SPLITTING by the infinite cones. Q relocates the wall to the same
exp-in-d sign-pattern object via a different functional (guard count). All routes exhausted,
all reduce to the sign-pattern/strategy core = SSG-hardness; d-scaling unmeasurable past
d≈6. **Consolidated final report written: notes/FINAL_REPORT.md.** Not solved; durable
output = Lean partials (sorry-free) + killed-routes map + Q as the documented open lead
(proof target: k(X_t)=poly via non-interacting reflex ridges).

## Guardrails held

No fabricated proofs; unit-cost caveat stated; confounds controlled (isotropic
Cheeger, budget-escalated trapping); query model kept separate; no
permission/config edits.

## Direct core attack (cycle 9) — notes/core_analysis.md
Worked the core directly (myself, no agents). New reformulation, verified exactly (d≤8,
0 mismatches): the removed half of each cut is EXACTLY a union of d convex cones ⟹
**X_t = box ∖ (dt convex cones)** (reflected pyramids, balanced apexes). Consequence: Φ
(Fermat–Weber), its subgradient, and vol(⋃cones) are all poly-estimable per-convex-piece
via Karp–Luby — but this does NOT give poly, because every quantity over X_t is a 2^{−t}
difference of two O(1) convex quantities (box vs cones) ⟹ needs 2^t precision. **The
barrier is the exponential THINNESS of X_t (vol=2^{−t}), not non-convexity**; it forces
intrinsic sampling ⟹ isoperimetry (hit-and-run/SMC/telescoping all reduce to
Cheeger(X_t)≥1/poly). Cleanest core statement: Cheeger of a box minus dt centrally-apexed
convex cones. Not cracked (=SSG∈P); the reformulation + rigorous thinness-barrier is the gain.
