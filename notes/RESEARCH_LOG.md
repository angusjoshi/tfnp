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

## Cycle 10 — the progress–convexity trade-off (`notes/progress_convexity.md`, `Tfnp/Progress.lean`)

Attacked the "first-order method on the balanced-point program" angle head-on. `Φ_μ(c)` **is**
convex in `c`; the obstruction is that no convex/quasiconcave *surrogate for the cut* exists.
Eight new sorry-free theorems (axioms `propext`/`Classical.choice`/`Quot.sound` only):

- **Exact worst-case progress** `card_removed_le_sum_min`: removal at apex `c` is the *minority
  count* `Σᵢ min(nᵢ⁺,nᵢ⁻)` (`nᵢ^φ` = #points with `ℓ∞`-argmax `(i,φ)`). Hence `≤ N/2` with
  equality **iff balanced** — a second variational characterisation of the balanced point, and
  a proof that a coordinate contributes progress only if it is **two-sided**.
- **`exists_sign_vacuous_cut`**: no two-sided coordinate ⟹ some sign vector makes the cut
  vacuous (`X ⊆ K(c,s)`). **`apex_between_of_two_sided`**: a two-sided coordinate traps the
  apex — `cᵢ` is sandwiched and *every* coordinate offset is bounded by the `i`-offset. So
  "query far away to get a convex cut" provably has zero guaranteed progress.
- **Sharp threshold at 2 vs 3 live coordinates.** `cut_inter_subset_halfspace`: `L(c) ≤ 2` ⟹
  the cut is a **halfspace on `X`** ⟹ body stays convex ⟹ poly-time round (strictly
  generalises the `d ≤ 2` base case). `exists_three_pyramid_centroid` (**centroid lemma**):
  any point of `ℝ^d` is the centroid of three points, one in each of *any* three
  distinct-index pyramids at `c` — explicit 3-point combination, replacing the ad-hoc
  arithmetic behind `conv K = ℝ^d`.
- **`le_of_quasiconcave_majorant` (the headline barrier):** any quasiconcave — in particular
  log-concave, so any Gaussian/entropic/softmax smoothing or convex-body barrier — `h ≥ 1_K`
  satisfies `h ≥ 1` **everywhere**. This upgrades the set-level barrier to the *function*
  level, which is what a first-order method actually needs. **There is no convex surrogate.**
- **`exists_injective_of_convex_cover`:** the convex cover number of a single cut is *exactly*
  `d` (`d` mutually-invisible witnesses; the `d` pyramids match it). So the operative
  complexity measure is the convex cover number, not any convexity constant — which is why
  every earlier route reconverged on a piece count.

**Experiments (decisive, in-window).** `live_progress_pareto.py`: searching ~3000 apexes/round
(balanced, axis-pulled, random, *allowed outside the box*) on realizable SSG `X_t`, `d=3..6`,
`t≤2d`: best progress at `L ≤ 2` is `0.000–0.011`, while the balanced apex gets `0.37–0.48` at
`L = d`; min liveness attaining `p ≥ 0.05` is `d` in essentially every round. **The trade-off
is a cliff, not a curve.** `anisotropic_cut.py`: the one regime where a convex cut provably
exists (`ℓ∞`-anisotropic body) is **never entered** — `w₁/w₂ ∈ [1.00,1.20]` at every round,
since the unbounded cut cones keep `X_t` reaching every box face despite `vol = 2⁻ᵗ`.

**Net.** `SSG ∈ P` not closed. What is closed, with proof, is the convex-surrogate family:
first-order methods cannot be run on any relaxation of the cut, and `Corollary C` is dead at
balanced apexes *for a reason* (progress ⟺ `L = d`), not merely empirically. New sharper open
question recorded in §5 of the note: whether a *pair* of apex rules can guarantee
(convex cut with `1/poly` progress) **or** (`1/poly` Cheeger) on every realizable `X_t` — the
bounding-box version of that dichotomy is refuted above, and `ℓ∞` rigidity (no weighted
sup-norm rescaling preserves contraction) is what blocks gluing the two routes.

## Cycle 11 — realizability made finite; REALIZABLE SHATTERING of X_t (`notes/adversarial_components.md`)

The open conjectures quantify over *realizable* trajectories, always probed with random
instances only. This cycle made "realizable" finite and machine-checked, then played the
adversarial game — with a decisive negative result.

- **Lean (`Tfnp/Realizability.lean`, sorry-free):** `ℓ∞` is hyperconvex, so a partial
  λ-contraction on a finite query set extends totally (coordinatewise McShane).
  `realizable_of_pairwise`: a history `(c^r, w^r)` is realized by an actual
  `IsLInfContraction` iff the finite pairwise conditions `‖w^r−w^q‖ ≤ λ‖c^r−c^q‖` hold
  (responses in cube). `realizable_cuts_retain_fixedPoint`: any such history's apex cuts
  all retain a common fixed point. **"Realizable" = a finite inequality system**, which
  DECOUPLES PER COORDINATE → the adversary's per-round freedom is a per-coordinate sign
  menu (interval intersection). Magnitude policy governs the menus: tiny `|v|` ⟹ argmax
  pinning (monotone-potential rigidity), huge `|v|` ⟹ nearby-apex locking; in between
  (`(1−λ)·diam ≪ |v| ≪` apex gaps — always available in the hard regime `λ = 1−2^{−poly}`)
  menus stay at the full `2^d`.
- **THE NEGATIVE (adversary_game.py, magfix run):** a certified-realizable adversary
  (menus full, rank-0 choices, kept ≈ ½ every round — the algorithm gets its full volume
  halving) **shatters X_t**: d=5: 18–19 components, masses 0.17/0.12/0.08/…; d=6: 28
  components, masses 0.07/0.06/0.05/… by t ≤ 2.5d. Onset t ≈ d+2, self-reinforcing.
  Density-verified (×4 samples). Unconstrained-signs control produces identical
  trajectories — realizability costs a correctly-played adversary nothing.
- **Isoperimetry route CLOSED for good:** the Open Lemma (`h(X_t) ≥ 1/poly` realizable)
  is refuted — realizable trajectories reach h = 0 (disconnection) at d = 5, 6. (Even if
  an invisible bridge survives below sampling resolution, h ≤ 10⁻⁴-ish ≪ 1/poly.) The
  prior "realizable bodies are essentially star-shaped, k = 1–2" picture (star_cover.md)
  was a RANDOM-INSTANCE artifact. Any surviving sampler must be a union-sampler over
  components; single-region MCMC is dead even realizably.
- **The positive handle (Lean, `Tfnp/Progress.lean`):** `apex_mem_pyramid` +
  `convex_pyramid` + `cut_inter_convex_isPreconnected` — every pyramid contains the apex
  and is convex, so **a convex lobe containing the apex cannot be split**. The cascade
  must first expel the apex from the mass; afterwards disconnection is absorbing (FW apex
  of shattered mass sits in the gaps). New sharpest open question: is there a cut rule
  keeping the apex inside a mass-carrying convex core while retaining 1/poly progress?
  That would block the cascade at step one; a proof that none exists likely converts the
  shattering into a d-scaling counterexample schedule for (★).
- **(★)/Q status:** hit, not killed — components (≈28 at d=6, t=14) lower-bound every
  cover measure but are not yet superpolynomial; the d-ceiling still hides the answer.
  What changed: (★) can no longer lean on benign-realizable empirics.

## Cycle 12 — the candidate algorithm, implemented and run past the ceiling (`notes/cell_sampler.md`)

Chose the most promising surviving positive lead: the telescoping convex-cover route
("complete modulo (★)"), newly attackable because (i) the adversarial trajectories from
cycle 11 are the hardest known instances and (★) had never been measured on them, and
(ii) a cover-based sampler pays no `2^{−t}` rejection tax, so — once validated in-window —
it can measure *past* the exact-rejection ceiling that capped every prior experiment.

- **Adversarial cell statistics (`cells_adversarial.py`) — the inversion.** The
  component-shattering adversary is CELL-CHEAP: d=6, t=14: 87 cells, top-(d·t) mass
  0.999 (!). The heavy cell tails belong to the *benign* trajectories (toward: 677
  cells, top-(d·t) 0.635; random-SSG: 507 / 0.713) — exactly the star-shaped cases
  where cells are unnecessary. No measured trajectory endangers (★); the untested
  adversary objective is cell-mass-entropy (future work, same harness).
- **The sampler (`telescope_algo.py`).** v1 (bucket survivors by cell, refill in-cell)
  LEAKS 1–5%/round (cells whose survivors die by chance are lost forever — the ratchet
  the notes predicted). **v2 fix is structural: cells form an exact TREE** (cell of X_t =
  parent cell ∩ one pyramid of the new cut, convex — Lean `convex_cell`), so point-less
  children are LP-checked (Chebyshev center) and REVIVED: no cell is ever silently lost,
  by induction from the box. Only remaining unproven step: the cell CAP (4000), whose
  overflow is a *declared* leak — conjecture (★) made executable. Weighted Fermat–Weber
  apex over cell-weighted draws. In-window validation: `exleak = 0.000` at every
  checkpoint (v1: 0.115 by t=8); kept ≈ ½ every round.
- **Past the ceiling (d=6, T=40, random-SSG, λ = 1−10⁻⁴):** error `|c−x*|` decays
  steadily `exp(−0.062 t)` — halving every ~11 rounds (ideal ≈ 6) — from 0.52 to
  **0.0348 at t=40**, ~3× beyond the old t≈14 ceiling; cumulative declared leak 12.9%;
  body stays connected (comps 1–2); ≤ 4000 cells hold ~87% of mass throughout. Pre-cap
  growth is fast early (~×1.5/round to t≈12) then equilibrates at the cap with slow
  leak — the strongest empirical support (★) has: mass-concentration holds where it was
  never measurable before.
- **Lazy splitting (`telescope_lazy.py`):** splitting only cells the cut actually
  crosses saves just ~18% — the fragmentation is *geometric*, not bookkeeping: balanced
  apexes are central, so each cut's fan crosses most of the mass. Proof attempts must
  bound geometric fragmentation; the handle is that all fans use hyperplanes from only
  `d(d−1)` parallel families (normals `eᵢ ± eⱼ`), i.e. cells = grid cells of a
  `d(d−1)`-dim axis grid intersected with a d-flat.
- **Adversary stress test (d=6, T=40, certified-realizable shattering adversary vs the
  sampler):** shattering reappears (comps 9→31→49→62 by t=20); the declared leak storms
  to a cumulative 1.44 by t=22 with weight fidelity lost (cellTV ≈ 0.9, floors inflating
  phantom weight) — **but the storm is a transient**: 18 consecutive pruning-free rounds
  follow, cells consolidate 4000 → 538 at t=40, weights re-concentrate, final state = 20
  components covered by ~500 cells. Steady state is cell-cheap even under sustained
  adversarial play (matches the exact-sampled §1 measurement). (★) must survive the
  shattering *phase transition*, not a persistent explosion. In-window coverage
  (exleak ≤ 0.027) held throughout; the weight fix (per-cell volume re-estimation,
  poly) is the top implementation target.
- **d-scaling datum (d=8, T=24, random-SSG):** convergence continues (|c−x*|
  0.367 → 0.190, halving every ~20–23 rounds vs ~11 at d=6, kept ≈ ½, connected) but
  under continuous pruning: cap 4000 saturates by t=10 (vs t=16 at d=6) and leak accrues
  ~4%/round (cumulative 0.93 at t=24) — no equilibrium. The required cap grows steeply
  d=6 → d=8; whether it is poly(d) or 2^{Θ(d)} is exactly (★), now with two quantitative
  data points beyond the old ceiling instead of zero.

**Status:** the candidate algorithm now EXISTS as a validated instrument: every step
poly(d,t,#cells,N), correctness of coverage by construction, with the entire open
problem compressed into one on-line-measured scalar (declared leak at a poly cap). Next
targets, in order: (1) cell-entropy-maximizing adversary (same harness, new scoring) —
the honest attempt to falsify (★); (2) the parallel-families arrangement bound for
balanced apexes — the proof attempt; (3) per-cell volume re-estimation to fix the
cellTV drift (poly but heavy).

## Cycle 13 — falsification attempts, the entropy law, the v3 meter, heuristic apexes

- **cellmax adversary (the (★)-falsification attempt) FAILED:** a certified-realizable
  adversary directly maximising cell count/entropy cannot beat the *benign baseline*
  (d=6,t=14: 663–750 cells, top-(d·t) 0.59 vs toward's 677/0.635). Cell count at fixed
  (d,t) has a structural ceiling no adversary policy reaches past.
- **The entropy law (`cell_entropy.py`):** mass-weighted cell entropy saturates at
  `log(dt)+O(1)` on ALL four oracle types (H₁₄ ∈ [3.4, 5.6] vs equidistribution 25.1;
  shattering adversary flat at 3.4 for 12 rounds; even cellmax only 5.58). Effective
  cells 30–265. **"Balanced-cut cell entropy saturates"** = the cleanest quantitative
  (★), adversary-tested; refinement-vs-conditioning cancellation is what a proof must
  capture (increments often negative — consolidation).
- **v3 meter (ratio-estimated revivals + mass-based pruning) fixes the instrument:**
  d=6 adversary T=40: declared leak **5.1%** total (v2: 144% by t=22) — adversarial mass
  concentration is real, storm-then-consolidate confirmed under honest weights (peak
  12000 cells → 3778, 35 comps). d=8 ssg T=24: |c−x*| 0.336→**0.0929** (halving ~10
  rounds, comparable to d=6), leak **4.8%** (v2: 93%) — v2's alarming d-scaling was
  mostly floor noise; both honest data points sit on the poly side.
- **Heuristic (sampler-free) apexes (`heuristic_apex.py`), answering "can the balanced
  point be picked heuristically from the history?":** history determines X_t exactly, so
  it's purely computational. Open-loop: history-only rules get **zero** worst-case
  removal (mass location is load-bearing; Lean's `le_of_quasiconcave_majorant` already
  bars all quasiconcave-potential rules a priori); `r^d` proxies erratic; **uniform-over-
  cell-centers gets Ω(1)** (0.15–0.47). But **closed-loop, the cell-list-only rule
  STALLS** (minority 0.4→0.05, kept→0.95, |c−x*| frozen): the cell count is endogenous —
  cutting at the counting-FW point fragments cells around its own fan and drags the next
  apex back (same family as Idea-D cheap centers / C3 stall). Mass is exogenous under
  refinement; counting is not. **Minimal sufficient statistic = cell list + approximate
  masses** — which per-cell DFK volume estimation supplies in randomized poly given poly
  cells. The heuristic road, honestly walked, leads back to the v3 architecture and
  certifies its weight step as necessary.

## Cycle 14 — the entropy law's mechanism found: the common fan (`fan_cone_test.py`)

Attacked the structure behind the entropy law. Three measurements, one discovery:

- **d-scaling bullseye (`spine_test.py` tail):** at d=8, H_t = 3.26/3.94/4.56 vs
  log(dt) = 3.47/4.03/4.38 (±0.2 nats!) vs equidistribution 8.3/14.6/20.8. The law
  `H ≈ log(dt)` now holds at both measured dimensions, almost exactly.
- **Spine hypothesis REFUTED (`spine_test.py`):** the linear-in-dt effective cell count
  is NOT 1-dim mass concentration — best-line spine masses 0.02–0.32 and decaying,
  covariance spectra nearly flat (no dominant axis; matches w₁/w₂ ≤ 1.2). The rigorous
  half survives: a line meets ≤ td(d−1)+1 cells (signature changes only at pairwise-
  hyperplane crossings).
- **THE MECHANISM (`fan_cone_test.py`): cells ≈ coarsening of ONE fan's cones.**
  `H(cell | cone) = 0.00–0.04` for the adversary (apex dispersion 0.004 vs diameter 1!),
  0.71 cellmax, 1.34 ssg (dispersion 0.157) — residual grows with apex dispersion
  exactly as the δ-margin picture predicts. The full t-cut cell is (almost) a function
  of the sign pattern of the d(d−1) pairwise comparisons at the mean apex — a
  **t-independent partition**. The entropy law's engine: cells stop multiplying in t
  because they are functions of a fixed fan; the log t term is apex drift only.
- **(★) decomposes into two t-free lemmas:** (1) **apex clustering** — successive FW
  balanced points drift slowly (FW = median-type statistic, stable under mass deletion:
  a real proof handle); (2) **cone count** — mass-carrying cones of a single
  d(d−1)-hyperplane fan are poly(d) (measured e^{H(cone)} ≈ 340–1800 ≈ d³–d⁴ at d=6,
  of ~46k total). The latter is the repo's recurring sign-pattern/strategy core in its
  purest form: one fan, one measure, no trajectories, no games.
- **Algorithmic corollary (v5, unimplemented):** deep inside a cone (margins > apex
  offsets) every cut's membership is constant, so X_t ∩ deep-cone is convex-or-empty —
  a t-independent cover of deep cones + margin cells could replace the growing tree.

## Cycle 15 — the fan factorization PROVED (`Tfnp/Fan.lean`); the cone-count leg corrected

"Let's prove it": split the mechanism into its provable and quantitative halves and
delivered the provable half machine-checked.

- **`Tfnp/Fan.lean` (sorry-free, axioms propext/choice/quot):**
  - `mem_pyramid_iff_pairForms` — pyramid membership ⟺ a sign condition on the pair
    forms `±(yᵢ−cᵢ)±(yⱼ−cⱼ)` (normals apex-independent);
  - `deep_cell_factorization` — **the fan factorization theorem**: if all apexes lie
    within δ of `c*`, then for 2δ-deep points (all pair forms at `c*` exceed 2δ), the
    ENTIRE cell signature — membership in every pyramid of every cut — is a function of
    the sign pattern of the pair forms at `c*`: a t-INDEPENDENT datum. All t-dependence
    of the cell structure is confined to the margin slabs `{|pair form| ≤ 2δ}`. This is
    the machine-checked core of the mechanism found in cycle 14.
- **Correction (d=8 fan-cone run):** the "effective cones ≈ d³–d⁴" reading was a
  sampling artifact — the cone partition is finer than 2200 samples resolve
  (effcones ≈ N at d=8; d=6 partially saturated). Honest picture: cones are a FINE
  partition with spread mass; cells are a COARSE function of them. The (★)
  decomposition is now: (1) apex clustering (controls the margins — the FW-median
  stability handle stands), and (2) **top-pattern concentration** — the induced
  coarsening (tuple of sign-weighted argmax answers) has few mass-carrying classes:
  the entropy law reduced to its common-apex core, now free of all geometry — pure
  order statistics of one measure under t argmax queries. Sharpest known form of the
  remaining open problem; not yet cracked.

## Cycle 16 — margin stability PROVED; the chain consolidated (`notes/CHAIN.md`)

"Finish it off": completed the reduction chain so every link is machine-checked,
measured, or a precise open lemma. One link remains open.

- **`Tfnp/Margin.lean` (sorry-free):** `pyr_stable_of_gap` — a point's ℓ∞-argmax
  (index AND sign) is stable under apex perturbation below half its top gap;
  `pyr_unique_of_gap` — it is then the unique pyramid; `mem_pyrUnion_iff_of_gap` —
  cut membership for gap-deep points is decided by the single equation `s i = σ`.
  **No-split corollary:** a new cut treats all gap-deep points of a cell identically
  — CELLS SPLIT ONLY INSIDE THE TOP-GAP MARGIN `{gap ≤ 2·drift}`. With the fan
  factorization (cycle 15), all growth of the cell structure is confined to the
  margin, machine-checked.
- **Margin mass MEASURED — the thin-margin hope refuted, the core sharpened
  (`margin_mass.py`):** `m_r ≈ 0.94–1.00` everywhere — gap distribution and apex
  drift CO-SCALE (adversary: both → 0 geometrically; the balanced-cut measure
  collapses onto the tie complex — also explaining the no-bounding-box-anisotropy
  finding). The proved no-split theorem protects only the gap-deep sliver. Final
  form of the open core, **the lopsided-split law**: ~all mass is margin-eligible
  and ~80% of cells are crossed per round, yet the mass-weighted entropy increment
  stays O(polylog) — crossed cells shed only low-mass pieces. Measured at d=6 and
  d=8 against every adversary built; no proof, no counterexample. This is (★)'s
  irreducible core with the deep/margin structure fully mapped and machine-checked
  around it.
- **`notes/CHAIN.md`** — the consolidated chain, link by link, with status flags:
  SSG∈P ⟸ balanced-cut algorithm [query side Lean-checked] ⟸ cell-tree sampler
  [implemented, coverage exact] ⟸ (★) ⟸ entropy law [measured d=6,8] ⟸
  fan factorization [PROVED] ∧ apex clustering [measured, open] ∧ margin control
  [measured, THE open lemma].

## Cycle 17 — the trichotomy: the lopsided-split law proved level by level

"Solve it": found and proved the theorem inside the law. Points classified by tie
multiplicity m at the drift scale.

- **Lean (`Tfnp/Margin.lean` additions, sorry-free):** `mem_pyr_iff_of_gap` (full
  membership characterization for gap-deep points); `cell_eq_of_onedeep` — all 1-deep
  points with common argmax share ONE cell across the whole trajectory (≤ 2d cells,
  t-free); `pyr_index_mem_pair_of_2simple` — a 2-simple point's argmax can only flip
  within its tied pair. With the planar-arrangement bookkeeping (2t threshold lines in
  the pair-form plane): **2-simple cells ≤ O(d²t²), proved**. Level m: O(d^m t^{2(m−1)}),
  same argument.
- **Measurement (`multitie_mass.py`):** the SHATTERING adversary's mass is almost purely
  2-simple (m₃ ≤ 0.001 from t=6) ⟹ **the instance class that refuted isoperimetry is
  provably poly-celled**. The cellmax adversary climbs the ladder (m₃ → 0.998, m₄ → 0.54)
  yet its cells never exploded (~750) — climbing is possible, converting it to cell
  blow-up has defeated every adversary built.
- **The one open lemma, final form — tie-multiplicity decay:** balanced-cut measures
  cannot sustain Ω(1) mass on ω(1)-way ℓ∞-ties (the high-codim diagonal) while halving
  volume every round. Proving it finishes (★), the algorithm, and — up to classical
  links — SSG ∈ P. Everything else in the chain is machine-checked or measured.

## Cycle 18 — the diagonal recursion mapped; THE CLOSING DATUM: depth is flat

- **The escape route, analyzed (CHAIN.md):** survival conditions mass onto ties
  (fixed-argmax points die at rate ½ under mixed signs; tie points dodge via
  drift-flipped argmaxes) — explaining the measured gap collapse — and on a diagonal
  tube every mixed sign vector keeps the axis and recurses the process one tie level
  deeper on the perturbation coordinates. Cells ~ (d²t²)^depth: depth O(1) ⟹ P;
  O(log dt) ⟹ quasi-poly SSG (already beats state of the art); Ω(t) ⟹ method capped.
- **Measured (depth_rate.py): DEPTH IS FLAT.** Mean tie-depth t=2..14: ssg ≈3.0 no
  trend; shattering adversary CONVERGES TO 2.00 (pure 2-simplicity = the provably-poly
  regime); cellmax 2.7–3.7 no trend; random balanced signs no trend; d=8 = d=6. The
  diagonal recursion exists but does not compound, against every adversary built.
- **Terminal state of the programme:** one sentence remains — *balanced cuts keep the
  surviving mass's tie-depth bounded* — measured flat everywhere, provably sufficient
  (cycle-17 hierarchy), unproved. Its log(dt) weakening already implies randomized
  quasi-poly SSG. The mechanism for a proof (survival-dodging accounting: deepening
  needs per-level sign-flip investment that balance doesn't let compound) is stated in
  CHAIN.md.

## Cycle 19 — the depth lemma's proof skeleton; extinction PROVED; one inequality left

- **Lean (`deep_extinction`, sorry-free):** a gap-deep point at (i,σ) is kept by a
  nearby-apex cut iff s_i = σ ⟹ cannot survive a sign flip at its coordinate. Rigorous
  base of the schedule analysis: survivors of a fully-flipped schedule are tied
  (the measured gap collapse, now a theorem-mechanism), and deepening depth-2 mass at
  pattern ε REQUIRES the double-disagree round (−ε).
- **The flooding obstruction (structural):** balance keeps whole half-pyramids, which
  are shallow-dominated in the agreeing signs — the double-disagree rounds refill the
  measure with complementary shallow mass. Deepening one pattern un-deepens the others;
  the flip investment does not compound. Explains all flat-depth measurements and the
  shattering adversary's convergence to depth 2.00.
- **Scale renormalization:** resolved structure is inert (no-split, PROVED); refinement
  passes to finer scales; cells accumulate additively (~the measured dt law). Fresh-scale
  m-tie mass in a convex mass-carrying cell obeys the slab bound C(d,m)(η/spread)^{m−1}.
- **Candidate closing inequality (FW-drift ≤ spread/d) TESTED AND DISCARDED** by its own
  checks (d=1 median drift = a quartile; measured drift/spread ~ 1 at d=6–8): the decay
  is dynamical, not volumetric. **New structural handle:** pyramid disjointness ⟹
  P_i^{−s_i} ∩ K = ∅ ⟹ every cut leaves the surviving measure completely one-sided at
  every coordinate pair — deepening state cannot be hoarded outside tie margins.
- **THE OPEN LEMMA (final form — quantitative flooding supermartingale):** under any
  sign schedule vs balanced apexes, the balance-forced refill of complementary shallow
  mass keeps E[tie-depth] = O(1) (measured ≈3 flat; O(log dt) suffices for quasi-poly
  SSG). Deepening needs double-disagree rounds (deep_extinction, PROVED) whose kept
  halves are whole, one-sided, shallow-dominated pyramids — the investment dilutes.

## Cycle 20 — one-sidedness + forced graduation PROVED; the flux law: kappa(m) = 1/2

- **Lean (3 new, sorry-free):** `tie_of_mem_two_pyr` + `one_sided_of_kept` (kept ∩
  disagreeing pyramid = apex or exact 2-tie: every cut leaves the surviving measure
  one-sided at every pair, off ties); `double_disagree_kills` (a double-disagree round
  removes every 2-simple point of the targeted pattern regardless of current argmax).
  The deepening schedule's cost structure is now fully machine-checked.
- **The flux law (`depth_flux.py`):** per-depth-class kept fraction κ(m) ≈ ½ for ALL
  classes, rounds, oracles (0.35–0.62); post-cut re-centered depth mean = pre-cut mean
  ±0.3, no trend. The depth distribution is STATIONARY under the balanced-cut map —
  stronger than boundedness.
- **THE OPEN LEMMA (sharpest form — conditional balance):** the balanced-cut dynamics
  keeps each depth class individually balanced (the measured κ(m)=½), hence depth
  stationary. Candidate mechanism, now with proved ingredients: killing restores
  conditional balance (survivors of each class are one-sided — proved — and re-mixed by
  FW re-centering). One exchangeability-type statement about one Markov map. It implies
  the depth lemma ⟹ (★) ⟹ SSG ∈ P; polylog version ⟹ quasi-poly SSG.

## Cycle 21 — SOTA recalibration; exact certificates built and parked; the line-epoch route

- **The bar checked (arXiv:2604.01006):** SOTA time = (log 1/ε)^{O(√d log d)} (decomposition
  theorem). Repo's formalized O(d log 1/ε) QUERIES matches CLY-v2 (query axis fine); the
  interesting axis is TIME: quasi-poly beats 2^{O(√n log n)} for SSG; P is the ideal.
- **Exact-rational certification machinery (`exact_geom.py`, `certify_disconnect.py`):**
  Fraction-arithmetic cell trees with partition-identity-gated volumes (root = box = 1,
  children sum exactly to parents through 12 rounds), exact Farkas emptiness (≤4-row
  Caratheodory), exact realizability, certified 0.41-BALANCED realizable trajectories at
  d=3. Slab-separation certificate implemented; no single-slab separation found at
  seed 4 T≤12 (piecewise certificate would be needed). PARKED — rigorous but below the
  bar.
- **The line-epoch route (new):** apexes within ρ of a common line for e rounds ⟹ pencil
  thresholds are 1-parameter ⟹ additive per-epoch cell growth O(d²e) (provable-shaped
  with the margin machinery, δ=ρ); total (d²e)^{t/e} ⟹ quasi-poly if e ~ t/polylog
  feasible. Measured (`apex_path.py`): benign paths directionally coherent (residual
  ~25% of extent over 12 rounds; shattering adversary nearly collinear 0.08); cellmax
  CAN curve the path (0.97) ⟹ line-epochs must be an algorithmic projection choice; the
  open question is whether any adversary can drag the centerpoint region transverse
  faster than spread/poly per round.

## Cycle 22 — the atomic law + marching mechanism; P-decomposition; the depthmax gate

- **Atomic lopsidedness law (`split_multiplicity.py`):** per crossed mass-carrying cell,
  ~1 mass-carrying child. Shattering adversary: 30/30 crossed, 30/30 mult=1, ZERO new
  mc cells/round. cellmax: mult≥3 → 0, new → 2/round. ssg: new = O(d), declining.
- **Mechanism — the marching picture:** all cut surfaces share d² pair-form normals;
  offsets move ≤ 2δ/round (P2, trivial). Surfaces shave ≤2δ-slabs off parallel facets
  instead of crossing interiors; interior crossings confined to each pair's own
  interval-structured cells: O(1)/pair/round (P3, line-zone shaped). Reconciles
  global margin mass ≈ 1 with additive growth.
- **P-decomposition chosen as THE path to hard P:** (P1) trichotomy [proved except
  multi-ties] + (P2) marching [immediate] + (P3) interval crossing O(1) [provable-shaped]
  ⟹ mass-carrying cells O(dt), conditional on (P4) multi-tie mass sub-threshold — the
  gate. Direct attack running: the depthmax adversary (objective = tie depth itself) at
  d=6 T=55 via the v3 sampler; at t=10: m₄=0.44, m₅=0.27 CLIMBING — the sharpest threat
  to date. Verdict pending: saturation ⟹ (P4) is the last lemma; climb to Ω(d) ⟹ the
  cell route caps at quasi-poly worst-case.

## Cycle 23 — depthmax verdict: depth adversarially UNBOUNDED; the meter survives; (SHED)

- **Depth broken:** the depthmax adversary drives D → 5.3–5.7 (of 6) within 15 rounds,
  m₃ = 1.00, m₄ ≈ 0.97, m₅ ≈ 0.9 sustained. First invariant broken all session. All
  depth-based forms of (★) are dead worst-case (conditional balance, tie-decay).
- **Meter unbroken:** at full depth saturation the declared leak accrues ~0.1–0.2%/round
  (3.7% at t=19), cells at cap, kept ≈ ½. The protector is the MARCHING structure
  (shared d² normals; offsets step ≤ 2δ; shed pieces are ≤2δ facet slabs), not depth.
- **The recast: the (SHED) lemma** — mass-carrying cells ≤ 1/η trivially; the sole
  failure mode is sub-threshold shedding; marching bounds its geometry; the lemma is
  "per-round shed mass ≤ 1/poly", with apex-nudging (offsets are functions of OUR apex,
  free within the centerpoint region) as the lever. (SHED) ⟹ v3 correct + polynomial ⟹
  SSG ∈ P. One round, one measure, d² interval walks, one free parameter.
- Caveat: beyond t≈10 the sampler's weights carry noise (cellTV ~0.6 under attack);
  depth saturation is in-window-corroborated; long-run leak figures are instrument-grade,
  not certificate-grade.
- **Depthmax marathon COMPLETE (t=55):** depth is a LIMIT CYCLE, not a march — the
  adversary repeatedly excites D → ~5.6–5.7 and the flooding dynamics repeatedly erode
  it back to ~3.3 (arc: 5.7 → 4.0 → 3.3 → 5.6). Leak: **14.7% total over 55 rounds**
  (~0.27%/round steady), cells finish at 6416 (half the cap), kept ≈ ½ throughout.
  (SHED) held through three full depth excursions and complete diagonal concentration.
  Sharpened worst-case picture: depth excursions are transient/mean-reverting; a bounded
  time-integral of excursions is plausibly what (SHED)'s ledger needs, not a pointwise
  depth bound.

## Cycle 24 — proof mode: the walk lemma + pair-record theorem; 2-simple cells O(d²t) RIGOROUS

Scripts retired (three adversaries, 55+45 rounds: storms transient, ledger ~0.3%/round,
depth mean-reverting — nothing more to learn from them). The do-not-prove list is now
explicit in CHAIN; proof mode engaged.

- **Lean (`Tfnp/Walk.lean`, sorry-free):**
  - `ncard_range_signPattern_le` — THE WALK LEMMA: the ternary sign pattern of a real
    against t thresholds takes ≤ 2t+1 values (the marching offsets are the thresholds;
    a point's relation to the whole walk is an interval datum).
  - `pair_membership_iff` — THE PAIR-RECORD THEOREM: for a 2-simple point, membership
    in the i₁-pyramid of ANY apex within δ is decided by ONE linear form:
    y ∈ Pyr i₁ τ c' ↔ (τ = ε₁ ∧ φ(y) ≥ φ(c')), φ(z) = ε₁z_{i₁} − ε₂z_{i₂}.
- **Composite (rigorous, improving the paper bookkeeping):** the full t-cut membership
  record of the 2-simple stratum is a function of the walk pattern of ONE form per
  (pair, sign pattern): **2-simple survivors occupy ≤ 2·d(d−1)·(2t+1) = O(d²t) cells**
  — matching the measured ≈2–3·d·t law almost exactly (the earlier estimate was d²t²;
  the improvement: given ε, one form decides everything).
- With `cell_eq_of_onedeep` (≤ 2d cells for 1-deep), the trichotomy's provable levels
  are now fully machine-checked at the sharp exponent. The open remainder of (★) is
  exactly (SHED) — the sub-threshold shedding ledger.

## Cycle 25 — the shedding geometry machine-checked

- **Lean (`Tfnp/Shed.lean`, sorry-free):** `abs_pairComb_sub_le` (marching bound: apex
  step δ moves every pencil offset ≤ 2δ); `shed_slab` (shed pieces ARE marching slabs:
  kept-then-dropped 2-simple points lie in `[φ(c_old), φ(c_new))`, width ≤ 2‖Δapex‖);
  `pencil_energy` (motion budget: Σ pencil motions² = 4k‖u‖₂² exactly — only O(k) of k²
  pencils move at full scale per round).
- **(SHED) fully staged:** slab shape ✓, slab width ✓, slab count budget ✓, stratum
  counts ✓ (walk+pair-record: O(d²t); 1-deep: 2d), survivor structure ✓ (extinction,
  one-sidedness, no-split, fan factorization) — all machine-checked. The one remaining
  statement is the measure of the slabs' sub-threshold shed (measured ~0.3%/round under
  every adversary; the apex's pencil offsets are free parameters). 29 sorry-free
  theorems now ring the problem; (SHED)'s measure bound is the entire remaining
  distance to SSG ∈ P.

## Cycle 26 — THE 2-SIMPLE LEDGER THEOREM: (SHED) proved on the 2-simple stratum

- **The missed insight, found:** a 2-simple cell can only be split by ITS OWN pencil
  (pair_membership_iff: the new cut's partition of a ψ-pair cell is decided by ψ's form
  alone — other pencils' slabs are irrelevant). With the walk lemma (a pair's cells are
  φ-intervals, the front lands in O(1) of them), the shed-piece count per round is
  O(d²), not d/η.
- **Theorem (paper-level, every ingredient Lean-checked):** total 2-simple shed over t
  rounds ≤ O(d²tη); choosing η = ε/(d²t·poly) gives shed ≤ ε/poly with tracked cells
  ≤ poly/ε. Proof = own-pencil confinement (pair_membership_iff,
  pyr_index_mem_pair_of_2simple, pyr_stable_of_gap) + interval structure
  (ncard_range_signPattern_le) + slab geometry (shed_slab, abs_pairComb_sub_le,
  pencil_energy) + disjointness ledger.
- **Consequence:** (SHED), hence v3-correctness + polynomial time, holds for
  trajectories whose mass stays 2-simple at the working scale — including the
  shattering adversary (m₃ ≤ 0.001), the class that refuted isoperimetry: END-TO-END
  COVERED.
- **The reduced open problem — the deep-stratum ledger:** m-tied mass (m ≥ 3) escapes
  own-pencil confinement; its splits involve the tie set's C(m,2) forms. The tie-tube
  recursion (an m-tube = a lower-dim copy with its own 2-simple sub-stratum) is the
  proof shape; depthmax shows full-measure deep excursions occur, and its measured
  leak (~0.3%/round at maximal depth) says the deep ledger holds empirically exactly
  as the 2-simple one now does provably. SSG ∈ P = one stratum's ledger.

## Cycle 27 — the last mile: m-set confinement PROVED; the residue isolated

- **Lean (`pyr_index_mem_of_mset`, sorry-free):** m-set confinement at every tie depth —
  dominating coordinate sets capture all pyramid memberships at nearby apexes. The deep
  stratum's splits are decided by its own tie set's forms (the m-ary generalization of
  pair confinement; built first try on the established proof pattern).
- **The split taxonomy:** marching-front splits (only shed producers; ≤2δ slab pieces,
  shed_slab) vs re-entry splits (bulk pieces, tracked, paid once by 1/η disjointness).
  Deep forms are relevant only when the round's top is in their pair; irrelevant forms
  wander freely — re-entry is the price, and it is a tracked-cell price, not a shed one.
- **(ZONE)-deep final residue:** transverse stacking — how many tracked deep cells share
  one pencil's front gap, separated only by other forms' records? 2-simple: O(1) PROVED.
  Deep: measured O(1) everywhere (multiplicity law); proof needs cross-level measure
  bookkeeping in the tie-tube recursion. This is the entire remaining distance to
  SSG ∈ P. 31 sorry-free theorems.

## Cycle 28 — the long derivation: marginal bound, lineage lemma, churn no-go, THE EQUIVALENCE

- **Marginal-density ingredient:** μ_t|cell is UNIFORM on a convex polytope ⟹ its 1-D
  marginals are 1/(d−1)-concave (Borell–Brascamp–Lieb) ⟹ slab mass ≤ d·(s/w)·cell mass.
  Big cells provably bleed ≤ 2dδ/w per shave — the engine behind the measured 0.3%/round.
- **Lineage lemma:** a φ-split child has the split offset as a φ-extent boundary
  (immediate from pair_membership_iff) ⟹ ≤ 1 mid-extent crossing per (lineage, pencil);
  all later crossings are boundary-marching.
- **Churn no-go (proof-strategy negative, documented):** all purely combinatorial or
  mass-based deep ledgers are vacuous (exponential create-die churn is consistent with
  every such constraint; balance adds nothing per-round). The deep bound requires a
  genuine dynamical inequality — as it must, or this wouldn't be a 40-year problem.
- **THE FINAL EQUIVALENCE: (SHED) ⟺ L ≤ poly, where L = tracked lineages ever created
  — the measured additive law itself.** Split by stratum: L_2simple ≤ O(d²t) PROVED
  (cycle 26); L_deep OPEN with two proved fences: re-entry once per (lineage, pencil),
  and deep creation only at cells whose top-gap ≤ 2δ (pyr_stable_of_gap) — i.e., only
  at the moving tie front. Final form of SSG ∈ P: balanced-cut dynamics creates only
  poly many tracked deep lineages.

## Cycle 29 — audit on challenge: corrections to 26–28

- Withdrew the "(SHED) ⟺ L" equivalence (only ⟸ established; constant corrected to
  O(d·t·L·η)). Flagged the 2-simple ledger's fixed-dispersion regime assumption (the
  cross-round re-stratification bookkeeping is NOT done; the shattering class, with its
  tightly clustered apexes, is the regime where the theorem honestly applies). Churn
  no-go downgraded to an informal dead-strategies map.
- Honest arc: the open core is still (★) — "mass-carrying cells stay poly" — in a
  cumulative form. The cycles' real content: the machine-checked fence (31 theorems),
  two proved sub-cases, the instruments, and the eliminated-strategies map. Not a
  reduction of (★) to anything easier than (★).

## Cycle 30 — handoff written

`notes/HANDOFF.md` created: the single consolidated entry point — all 31 Lean theorems
by file, the assembled paper-level results with their audit caveats, the measured laws
with instruments, the full do-not-prove list, the algorithm/instrument map, the open
core with its proved fences, and recommended next steps in priority order (multi-scale
re-stratification; average-case theorem; amortized-depth quasi-poly track; the
front-birth inequality; standalone write-ups). README and CHAIN.md now point to it.

## Cycle 31 — re-stratification fenced: tie-set invariance (Lean); the stacking probe

Attacked HANDOFF §7.1 (multi-scale re-stratification — the cycle-29 Correction-2 gap).
Diagnosis first: the cross-epoch failure mode is a tracked point's tied PAIR changing
between scale-epochs, which would multiply per-epoch cell records instead of
telescoping them. That mechanism is now fenced.

- **Lean (`Tfnp/Restrat.lean`, 7 new sorry-free theorems, axioms propext/choice/quot):**
  - `collar_of_near_top` — THE TRANSITION ATOM (pure triangle inequalities, no
    continuity): a coordinate within 2δ of a point's ℓ∞-top at ANY apex within δ of c
    was already within 4δ of the top at c itself. Tie membership has no cold entries.
  - `tie_mem_pair_of_robust` / `pair_invariant_of_robust` — 4δ-robust 2-simple mass
    (third coordinate > 4δ below top) cannot change its tied pair at any apex within δ;
    along a whole trajectory its tie set AND all pyramid memberships stay in the pair.
    With `pair_membership_iff`, the entire record of the robust stratum is the walk of
    ONE form — the pair-record theorem holds scale-free on the robust stratum.
  - `tie_mem_mset_of_robust` / `mset_invariant_of_robust` — the m-ary generalization
    (same atom + `pyr_index_mem_of_mset`): tie SETS are robust trajectory invariants at
    EVERY level of the trichotomy; strata migration only through each level's 4δ collar.
  - Cross-boundary telescoping (paper, from the atom at the coarser scale): at an epoch
    boundary the new pair of still-2-simple robust mass satisfies new ⊆ old ∪ {top} =
    old — pairs persist ACROSS epochs too; per-(pair,ε) walks are global in the
    thresholds, so per-epoch ledgers add. Robust-2-simple lineage cells ≤ O(d²T),
    scale-free. The multi-scale gap for the robust stratum is CLOSED; what remains
    outside is exactly the collar mass (gap₃ ≤ 4δ_r).
- **The stacking probe (`stacking_probe.py`, results `stacking_results.txt`; d=6,
  four oracles, t ≤ 12, THRESH=0.002, in-window rejection sampling):**
  - **viaCol = 1.000 in every observed instance** — all pair changes pass through the
    4δ collar. (Forced by the theorem; instrument-classification sanity check.)
  - **The churn no-go, quantified:** geoKmax ≈ #mc everywhere (the worst pencil's
    offset sits mid-extent of essentially EVERY tracked cell) while actual per-pencil
    crossings dynK ≤ 27 and tracked births per pencil ≤ 7, flat in t. A static/
    volumetric proof of (ZONE) is impossible — the bound is dynamical or nothing.
  - **Shattering adversary = the theorem's home regime:** robust mass → 0.998,
    pairchg ≡ 0 from t=5, dynK → 0, births = 0 — all 30 cells crossed every round but
    purely by marching shaves (removal), zero mid-cell pencil crossings. Cycle-26's
    coverage of this class upgrades from "fixed-δ regime, measured" to "robust
    stratum, PROVED scale-free, carrying 99.8% of the measured mass".
  - ssg / cellmax / randbal: robust fraction 0.00–0.36 — the collar carries the bulk
    (the co-scaling/margin-mass law at per-point resolution); pairchg 0–11%, no trend;
    births/round 0–55, no growth trend (the additive law at per-pencil resolution).
- **Honest status:** the fence removes re-stratification as a blow-up mechanism for
  robust mass at every depth, and upgrades the shattering-class theorem to scale-free.
  The open core is unchanged in substance: on benign/deep trajectories the collar
  (≈ margin) mass hosts the births; birth rate measured O(d)/round with single-digit
  per-pencil stacking; unproved. Caveats: mass-carrying threshold 0.002; probe is
  in-window (t ≤ 12), 5000-point samples — birth counts near threshold carry
  sampling noise.

## Cycle 32 — collar kinematics (Lean); the collar ledger: births front-confined, no
## oscillation churn, and the SECOND channel (emergence) measured

- **Lean (`Tfnp/Restrat.lean`, +1 sorry-free): `gap_lipschitz`** — the per-coordinate
  top-gap `linfDist y c − |y m − c m|` is 2-Lipschitz in the apex. Strengthens the
  transition atom to two-sided form: with steps ≤ δ a lineage cannot jump the [2δ, 4δ]
  band in one round — every tie entry is preceded by ≥ 1 full round of collar
  residence. Collar entries are well-defined, tolled events.
- **The collar ledger (`collar_ledger.py` → `collar_ledger_results.txt`; d=6, four
  oracles, t ≤ 13, per-lineage accounting over the signature tree):**
  - **Births are 100% front-confined:** 667/668 birth events across all oracles hit
    lineages with median gap₂ ≤ 2δ (the no-split theorem's prediction at cell-median
    resolution); ≈ 0 births to gap₃-robust lineages.
  - **No oscillation churn:** tie-band entries are ~once per lineage (lineages with
    ≥ 2 entries: 3/395 ssg, 9/388 cellmax, 2/430 randbal, 0/31 shattering; max 4).
    The feared in-out oscillation scenario does not occur, even under cellmax. The
    front population is PERSISTENT: lineages are born on the front and stay there.
  - **Shattering adversary: perfectly static** — 31 lineages, 0 births, 0 deaths,
    0 entries over 12 rounds. The robust-stratum picture (cycle 31) end to end.
  - **NEW: the L-ledger has a second channel.** ssg: L = 395 ≈ 242 births + 153
    emergences — sub-threshold cells re-crossing η ("emergence") contribute ~40% of
    new lineages, comparable to front births (cellmax and randbal similar). The churn
    channel exists in the flesh — not as oscillation but as renormalization growth:
    an untracked cell fully kept while the cut halves everything else DOUBLES its
    conditional mass per round.
  - **Emergence anatomy:** at detection, emergent masses hug the threshold (med
    ≈ 1.2η, 91–94% < 2η — caught within one doubling of crossing, as the ×2/round
    renormalization-growth mechanism predicts). But the AGE distribution (rounds since
    last tracked ancestor) has a genuine incubation tail: ssg med 2 (54/124 age ≥ 3,
    max 6); cellmax med 3 (143/212 age ≥ 3, max 11); randbal med 3 (max 10). The
    cell-count adversary cultivates sub-threshold mass that resurfaces many rounds
    later — emergence is renormalization growth with MEMORY, not threshold flicker.
    Rate stays O(d)/round (~10–30) under every oracle; the shattering adversary has
    exactly 1 emergence in 12 rounds.
- **Clarification recorded (re-derived independently, consistent with the cycle-23
  recast):** tracked-cell COUNTS are trivially poly (≤ 1/η alive, ≤ poly created per
  round); the entire content of (★)/(SHED) is the pruned-crumb MASS ledger, for which
  the BBL engine is vacuous exactly on front cells (width ~ δ). The dynamical
  inequality must live there.

## Cycle 33 — the smoothed/annealed track opened: the half-kept law (Lean), the
## incubator martingale, and (A1) — the annealed theorem's one open lemma

Direction chosen by the user: smoothed. Model and targets in `notes/smoothed.md`.

- **The annealed model:** oracle signs = uniformly random BALANCED sign vectors,
  independent of the survivor structure — exactly the `randbal` null oracle, measured
  to match random-SSG trajectories on every instrumented axis. Annealed statements are
  exact; the bridge to random/perturbed SSG instances is the (conjectured, measured)
  approximate per-stratum balance of their sign processes.
- **Lean (`Tfnp/Annealed.lean`, sorry-free): `annealed_half_kept`** — a point with a
  strict argmax is kept by EXACTLY half of the balanced sign vectors (complementation
  involution `A ↦ Aᶜ` + `mem_pyrUnion_iff_of_gap` at δ=0; no binomials). The measured
  flux law κ(m) ≈ ½ (cycle 20) is now a THEOREM in the annealed model — its first
  machine-checked root.
- **The incubator martingale (paper, `notes/smoothed.md` §3):** with exact balance,
  `M_t(C) = 2^t·vol_t(C)` is a martingale for gap-deep cells (half-kept law +
  deep_extinction) ⟹ **Doob: a crumb of mass m₀ emerges with probability ≤ m₀/η —
  the emergence channel is self-financing in expectation.** Post-hoc confirmation
  found in cycle-32 data: randbal emergence ages decay geometrically at rate ≈ 0.5
  per round, the martingale/extinction prediction; cellmax's fat tail (ages to 11)
  is the adversarial correlation the annealed model excludes.
- **The honest system status (§4):** Doob + the crumb ledger alone do NOT close
  (`E[L_emerge] ≤ O(d·t·L)` — constant ≥ 1). The remaining annealed lemma isolated:
  > **(A1) annealed stacking decay** — under fair signs, a stacked deep lineage's
  > distinguishing record must have agreed with the coin flips in every round since
  > divergence (prob 2^{-age}) while its mass must have grown 2^{age}-fold to stay
  > tracked; stacking-count × survival is a supermartingale ⟹ E[stacking] = O(1).
  (A1) + walk lemma + Doob ⟹ **E[L] ≤ poly(d,t) annealed** — the full annealed
  theorem. (A1) is a statement about one stochastic process with independent fair
  coins, not adversarial dynamics: genuinely more tractable than (★).
- **Instrument (Doob check, `collar_ledger.py` v3):** unnormalized emerged-vs-outflow
  volume accounting with in-window/orphan split (initial-reservoir boundary effect
  identified and excluded). **VERDICTS (d=6, t ≤ 13): ssg 0.909 ✓, shattering
  0.016 ✓, randbal 1.061 (≤ 1 within instrument noise; caveat: harness randbal is
  realizability-clipped, so signs are not perfectly independent), cellmax 2.501 —
  the adversary VIOLATES self-financing by a factor 2.5, exactly the sign-correlation
  nurturing the annealed model excludes.** The instrument cleanly discriminates
  adversarial amplification from neutral dynamics; random-SSG sits on the annealed
  side — evidence for the bridge conjecture. Caveats: single realizations,
  near-threshold cells hold ~10 sample points at WANT=5000 — instrument-grade.

## Cycle 34 — (A1)'s survival half machine-checked; the recycling insight; v4 sketched

- **Lean (`Tfnp/Annealed.lean`, +1 sorry-free): `annealed_survival_pow`** — a point
  gap-deep at every one of `a` rounds survives all `a` independent balanced cuts for
  EXACTLY a 2^{-a} fraction of sign tuples (piFinset factorization of the half-kept
  law; built first try). Exact corollaries in the annealed model: expected gap-deep
  lineage lifetime = 2 rounds; survival × doubling is a martingale; stacked deep
  populations pay 2^{-age} against their required 2^{age} growth — **the survival
  half of (A1) is now a theorem.**
- **(A1) residue isolated (the front half):** tie-front cells dodge (argmax mobile ⟹
  survival > ½), so front stacking needs: "record divergence implies ≥ 1 resolved
  (gap-deep) coordinate comparison, which pays 2^{-age} by annealed_survival_pow."
  The walk-position freezing of irrelevant forms (lineage lemma) is the tool; making
  the divergence→resolved-comparison step precise is what remains.
- **The recycling insight:** the measured Doob ratios (≈ 0.9–1.06 neutral, 2.5
  cellmax) mean the emergence bound is near-tight — SHED MASS RETURNS. v3's declared
  leak (~0.3%/round) is exactly the incubator throughput that pruning discards.
  **v4 sketch:** track sub-threshold crumbs exactly as marching-slab polytopes
  (shed_slab gives their shape) instead of pruning ⟹ leak vanishes identically;
  correctness then rests on the crumb population staying poly — subcritical off the
  front by annealed extinction; the front branching rate is again (A1)-front. For
  the annealed/smoothed theorem, v4 + (A1)-front would close correctness and time
  together. Logged in notes/smoothed.md §4b.

## Cycle 35 — the straddle–dodge dichotomy (Lean); (A1)-front reduced to subcriticality;
## b measured < 1 under every oracle

- **Lean (`Tfnp/Annealed.lean`, +1 sorry-free): `strict_argmax_of_one_sided`** — a
  2-simple front point strictly on one side of its pair's offset has a strict argmax,
  i.e. satisfies `annealed_survival_pow`'s hypothesis exactly. **The front's dodging
  advantage is confined to straddling cells** (which the walk lemma counts O(1) per
  record); every non-straddling tracked cell — front or deep — dies at rate exactly ½
  per round in the annealed model.
- **The branching frame (smoothed.md §4c):** tracked lineages = branching process with
  immigration (initial + emergences, self-financing by Doob), offspring = births at
  once-ever-per-(lineage,pencil) mid-extent crossings, death = ½/round off-straddle.
  E[L] ≤ (init + emerg)/(1 − b). **The annealed theorem reduces to (A1''): b < 1.**
  Its three mechanisms are all machine-checked (once-ever crossings, ½-death,
  collar tolls); the open step is combining them over a lineage lifetime without
  independence pitfalls (crossing times correlate with survival via the apexes).
- **b is already measured, and subcritical everywhere** (cycle-32 ledger data read
  through the new frame): ssg 0.61, cellmax 0.38, randbal 0.65, shattering 0.
  Frame consistency: predicted L ≈ (init+emerg)/(1−b) ≈ 467 vs measured 395 (ssg,
  boundary effects expected). The measured worst b ≈ 0.65 leaves real margin —
  the inequality to prove is not tight.

## Cycle 36 — the population-balance theorem: the annealed 2-SIMPLE process is CLOSED;
## the deep residue is occupancy, not branching

- **Lean (`Tfnp/Annealed.lean`, +1 sorry-free): `both_agree_keeps`** — an agree-agree
  round keeps the ENTIRE 2-simple pattern cell, split across the two pyramids: the
  birth event. With `pair_membership_iff` (single-agree keeps exactly one side) and
  `double_disagree_kills` (double-disagree kills all), the annealed straddler's
  offspring distribution (2,1,1,0) at ¼ each is machine-checked pointwise.
- **The population-balance theorem (smoothed.md §4d):** straddlers are exactly
  CRITICAL (E[offspring] = 1 ∓ O(1/d)); non-straddlers subcritical (½ — cycle 35);
  ≤ 1 straddler per (pair, pattern) channel (interval structure). Per channel
  E[N] ≤ 2; births ≤ ¼/channel/round; **E[L_2simple] ≤ L₀ + O(d²T). The annealed
  theorem is CLOSED for trajectories whose tracked mass stays 2-simple** (with Doob
  emergences + the cycle-31 scale-free robust ledger). Supersedes the b < 1 frame.
- **The deep residue, honestly:** a FULLY-straddling m-tied cell has E[offspring] =
  m/2 — supercritical for m ≥ 3. The limiter is OCCUPANCY (all C(m,2) marching
  offsets inside shrinking pieces; splits evict offsets to boundaries — lineage
  lemma), measured O(1) everywhere. (A1'') final form: expected fully-straddling
  rounds per deep lineage = O(1) in the annealed model. This is also exactly where
  annealed and worst-case part ways: depthmax SUSTAINED deep straddling (cycle 23).

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
