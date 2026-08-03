# Route Q — fat star-cover of `X_t`: assessment

**Question.** Cover the non-convex body `X_t = box ∩ ⋂_{r≤t} K(c^r,s^r)` by
`k = k(X_t)` star-shaped pieces `S_1,…,S_k`, each with a nonempty (LP-findable)
kernel so each is *exactly* ray-shootable, then union-sample by Karp–Luby in
`poly(k)` (not `2^k`). Then **poly sampler ⟺ `k(X_t) = poly(d,t)`**. Q is worth a
careful look because its death-shape (pocket/comb proliferation) is *provably
orthogonal* to the dumbbell that killed the Cheeger/κ routes.

**Headline verdict: `k` blows up in the WORST CASE (exp in `d`), but the worst
case is a comb — a shape orthogonal to the dumbbell wall — so Q genuinely dodges
the *known* wall and hits a *different* one. Whether the realizable FW-balanced
trajectory produces combs is open and is the thing the capped experiment must
measure. Q does not reduce to isoperimetry; it reduces to a cleaner
*combinatorial* quantity — the art-gallery / arrangement-cell count of `X_t` —
which is the same sign-pattern object everything else landed on, but a different
functional of it.**

---

## 1. Is `k(X_t) ≤ poly(d,t)`?

### 1a. A rigorous free upper bound: `k(X_t) ≤ (d²t)^d` (poly in `t`, exp in `d`)

Every `K_r = K(c^r,s^r)` is a union of `d` `ℓ∞`-pyramids; its boundary lies in the
arrangement `A` of the pyramid-facet hyperplanes `{s^r_i(y_i−c^r_i) = ± s^r_j(y_j−c^r_j)}`,
`O(d²)` per round, `H = O(d²t)` total. **Inside each full-dimensional cell of `A`
the argmax/argmin coordinate of every `w^r = s^r(y−c^r)` is fixed, so via (MEM)
`y∈K_r ⟺ max w^r + min w^r ≥ 0` each `K_r` is a single halfspace there** ⟹
`X_t ∩ cell` is a convex polytope (`≤ 2(d−1)t+2d` facets, exactly the
`P_π` cells of `polytime.md §3.1`). Convex ⟹ star. Number of cells of an
arrangement of `H` hyperplanes in `ℝ^d` is `O(H^d) = O((d²t)^d)` — matching the
`O((d²t)^d)` nonempty-cell count already recorded (`polytime.md:179`). ∎

So Q hands you, for free, `k ≤ (d²t)^d`: **polynomial in `t` for fixed `d`,
exponential in `d`.** This is the honest ceiling. The whole game is whether a
*much smaller cover by fat star pieces* beats it.

### 1b. `k(X_t)` = the art-gallery guard number of `X_t`

The maximal star piece with witness `z` in its kernel is
`star(z) := {y∈X_t : [z,y] ⊆ X_t}`. `X_t = ⋃_j star(z_j)` iff every point is
visible from some `z_j` — i.e. `{z_j}` is a **guard set**. Hence
`k(X_t) = ` minimum guard (art-gallery) number of `X_t`. This is the precise
combinatorial object; its death-shape is a **comb** (each tooth needs its own
guard), *never* a dumbbell.

### 1c. Rogue's `k ≤ d·t` ("each cut adds ≤ d lobes") — where it holds and where it breaks

**The additive intuition (correct part).** `X_t = X_{t−1} ∖ N_t`, where the
removed set `N_t = ⋃_i P_i^{−s^r_i}(c^t)` is `d` convex cones with a common apex
`c^t`. Removing *one* convex cone from a convex body gives a Pac-Man — still star.
Far from `c^t`, only one cone-boundary passes through any given region, acting like
a single hyperplane, so distant lobes are sliced convexly and stay star. New
non-convexity (reflex ridges) is created only near the pinwheel apex `c^t`, `O(d)`
of them per cut. If reflex ridges never *interacted*, this would give `k = O(dt)`
— and would prove SSG ∈ P.

**Why it breaks — lobe-SPLITTING = ridge interaction (the real death).** The
cones are **infinite**, so cut `t+1`'s pinwheel boundary can pass through a lobe
that *already* carries a reflex ridge from an earlier cut. The intersection of two
reflex features creates new pockets, and the number of interaction cells is the
arrangement complexity `(d²t)^d` again — exponential in `d`. Concretely: one
cannot bound `k` additively because the same `(d²t)^d` cell count of 1a is a
genuine lower bound on the number of *distinct visibility classes* once the
`H = O(d²t)` cone-facets are in "general position." **The multiplicativity is real
in `d`; it is just capped polynomially in `t` for fixed `d`.** So rogue's `k≤d·t`
is *false in general* (the splitting counterexample is exactly an adversarial
arrangement of the `t` pinwheels), but it may be *approximately true on realizable
trajectories* — same status as "κ stays bounded."

### 1d. The KER handle, and why the single kernel emptying (C3) does NOT doom Q

`ker K_r = {z : s_i(z_i−c^r_i)+s_j(z_j−c^r_j) ≥ 0 ∀ i≠j}` is a convex cone
(apex `c^r`, `O(d²)` facets) that always contains `c^r`. The *single global*
kernel `box ∩ ⋂_r ker K_r` is monotone-shrinking and empties at `t ≈ d/2` (C3) —
this is why one star piece fails. **Q's point is precisely that emptiness of the
intersection-kernel says nothing about the guard number:** a body with empty
kernel (non-star) can still be `2`-guardable (any dumbbell). `k` is governed by
how the cone-boundaries *partition visibility*, i.e. by the arrangement of the
`ker`-cone facets — a cell count, `= (d²t)^d` worst case, same object as 1a.

### 1e. Relation to the sign-pattern combinatorics (the object everything reduced to)

`condition_transfer.md` found conditioning is set by the **sign-pattern (orthant)
trajectory of the cuts**, not the scalar gap `δ`. `k(X_t)` is *also* a pure
function of that sign-pattern/arrangement structure (1a–1d). So **Q relocates the
wall to the same combinatorial object** — but to a *different functional* of it
(guard count, not κ / Cheeger). Crucially the two functionals are **provably not
equal** (§3), so this is a relocation with genuine new leverage, not a tautology.

---

## 2. The greedy submodular cover + virtual-kernel construction (experiment spec)

### 2a. Submodularity (exact)

For a witness set `Z`, define the coverage `F(Z) = vol( ⋃_{z∈Z} star(z) )`
= visible volume. `F` is **monotone submodular** in `Z` (union of coverage sets):
`F(Z∪{z}) − F(Z) = vol( star(z) ∖ ⋃_{z'∈Z} star(z') )` is nonincreasing as `Z`
grows. Hence greedy (pick the `z` maximizing marginal covered volume) is a
`(1−1/e)`-approx per step; iterating to `(1−ε)` coverage uses
`O(k(X_t)·log(1/ε))` pieces. So the greedy cover size is a faithful (log-factor)
proxy for `k`.

### 2b. Each piece is exactly ray-shootable (no Markov chain)

`star(z)` needs no separate virtual constraints — it *is* the visibility star and
ray-shoots directly: along direction `u`, `R(u) = ` first exit of the segment from
`X_t`. Since `X_t = box ∩ ⋂_r K_r` and along a ray each
`max_i w^r_i(r) + min_i w^r_i(r)` is piecewise-linear (`O(d)` breakpoints/round),
the first violation of any constraint is computable in `O(d²t)`. Uniform sampling
of `star(z)`: draw `u ∈ S^{d−1}`, radius `∝ ρ^{d−1}` on `[0,R(u)]`; volume by the
same radial integral. **Equivalent explicit-kernel form** (for exact volumes):
per round commit `z` to the sub-union of pyramids of `K_r` it kernel-sees; the
piece is then `box ∩ ⋂_r K_r^{(z)}` with explicit LP kernel containing `z`.

### 2c. Karp–Luby union-sampling is `poly(k)`

Given (i) uniform sampling from each `S_j` (2b), (ii) `vol(S_j)` (radial estimate),
(iii) membership `y∈S_j` (check linear constraints): sample `j ∝ vol(S_j)`, draw
`y∼U(S_j)`, accept w.p. `1/#{j': y∈S_{j'}}`. Output is uniform on `⋃S_j = X_t`;
expected trials `= (Σ vol S_j)/vol(X_t) ≤ k`. **So the entire cost is `poly(k)` —
the whole route rests on `k = poly`.** (Clean reduction: nothing else can go wrong.)

### 2d. CAPPED experiment for `main` (laptop-safe, exact rejection)

Goal: measure the growth of `k̂(d,t)` (greedy-cover size to 99% volume) and,
decisively, its **`d`-dependence** (the exp-in-`d` ceiling is the danger).

- **Bodies.** Exact-rejection ground-truth points of `X_t` on realizable
  trajectories (real SSG + topical contractions), `d ∈ {2,3,4,5,6}`, `t` up to
  `min(2d,10)` (rejection is reliable to `t≈13`, `vol≈2^{−t}`).
- **Candidate witnesses.** The cut centers `{c^r}` (each in its own `ker K_r`) ∪
  a few hundred rejection-sampled points of `X_t`.
- **Greedy loop.** Maintain an uncovered point-cloud `U` (rejection sample, e.g.
  `N=3000`). For each candidate `z` estimate `star(z)` coverage = fraction of `U`
  visible from `z` (segment test: `z+ρ(y−z)∈X_t` for a grid of `ρ∈[0,1]`, all in
  ⟹ visible). Greedily add the max-marginal `z`; stop at 99% covered. Record
  `k̂(d,t)`.
- **Calibration (essential — validates the proxy).**
  (a) **Dumbbell** (two boxes + thin neck): expect `k̂≈2–3`, *independent of neck
  width* — confirms Q sees through the dumbbell (Cheeger→0) that kills hit-and-run.
  (b) **Comb** with `m` fat teeth: expect `k̂=Θ(m)` — confirms the proxy detects
  the blow-up, and that a comb is Cheeger/κ-*easy* but Q-*hard*.
- **Report.** `k̂` vs `t` (linear ~`dt`? poly? plateau?) and — the decisive plot —
  `k̂` vs `d` at fixed `t/d`. **Poly/mild-in-`d` ⟹ Q alive; visible exp-in-`d`
  jump ⟹ Q dies like the rest.** Also log a cheap lower bound: max antichain of
  pairwise-non-co-visible sampled points (greedy) — brackets `k` from below.

Cost: reuses the existing exact-rejection harness (`conditioning.py` machinery);
only adds a visibility/segment test. No Markov chain, no heavy compute.

---

## 3. Honest verdict: does Q dodge the wall?

**Q genuinely dodges the KNOWN (dumbbell) wall, and this is provable, not
hopeful.** The two failure modes are *orthogonal*:

| shape | Cheeger `h` / κ | star-cover `k` (Q) |
|---|---|---|
| **dumbbell** (2 lobes, thin neck) | `h→0`, `κ→∞` — **hard** | `k≈2–3` — **easy** |
| **comb** (`m` fat teeth) | `h,κ=Ω(1)` — **easy** | `k=Θ(m)` — **hard** |

Because the dumbbell (the *only* realizable counterexample the isoperimetry work
found) is Q-easy, Q is **not** wall-equivalent to Cheeger/κ. This is the real
content of "route Q's failure mode is orthogonal," and it is why Q was worth the
careful look.

**But Q does not escape the underlying combinatorics.** `k(X_t)` is the
art-gallery number, a functional of the very same sign-pattern / arrangement-cell
structure that κ and the condition-number transfer reduced to; its worst case is
`(d²t)^d` = exp in `d` (§1a), realized by an adversarial comb-of-pinwheels
(lobe-splitting, §1c). So the honest statement is:

- Q **relocates** the wall from an *analytic isoperimetric inequality* (`h≥1/poly`)
  to a *combinatorial counting bound* (`k=poly`) on the same object. A counting
  bound may be more tractable — we have the explicit cut/sign structure — and
  that is Q's upside over the analytic routes.
- The decisive open question becomes: **do FW-balanced realizable trajectories
  ever produce combs?** Priors both ways: *for poly-`k`* — balanced cuts each
  remove half the volume from the median center, which is a coarse operation ill-
  suited to carving many fine teeth (fine teeth want many small peripheral cuts,
  but balanced cuts are big and central); the trajectory starts at the box (`k=1`)
  just as κ starts isotropic. *Against* — the `(d²t)^d` ceiling is exp-in-`d`, and
  the reliable experimental window (`d≤6`) is far too small to see a `2^d`-type
  jump, exactly the blind spot that made the κ empirics inconclusive in the hard
  regime.

**Bottom line: needs the experiment, with a clear-eyed prior.** Q is the one live
route whose wall (comb / poly art-gallery number) is *provably different* from the
dumbbell, so a positive experimental signal here would be genuinely new — but the
worst-case ceiling is exp-in-`d` and the small-`d` window cannot settle the
`d`-dependence, which is the only thing that matters. My lean: **`k` likely grows
mildly in `t` but the `d`-scaling is the unknown that decides it; do not expect the
capped run to be decisive, expect it to be *suggestive* (as with κ).** A stronger
theoretical target than the experiment: prove that balanced-central pinwheel cuts
keep the reflex ridges "shallow/non-interacting" (an additive `O(dt)` reflex bound
on realizable trajectories) — that is the analog of "asymmetric repair," and it is
the only thing that would turn Q into a proof rather than evidence.

---

## 4. Reconciling the in-window `k≈1` signal with the C3 kernel-collapse

Main ran the capped experiment (exact rejection): calibration passes
(dumbbell→`k=2`, comb(3)→`k=3`, comb(5)→`k=5`); **realizable SSG `X_t` gives `k=1`
at `t=d` and `k=1–2` at `t=2d` for `d=3,4,5`, robust to coverage target `0.999`
and segment resolution `nseg∈{10,40,120}`.** So in-window `X_t` is essentially
star-shaped from ONE findable point. This must be reconciled with C3
(`isoperimetry_summary §5`), which reported the kernel "collapses" at `t≈d/2` and
best true-kernel visibility only `0.5–0.9`. **They do not conflict — here is the
precise reconciliation.**

### 4a. Rigorous: `cker ⊆ tker`, so C3 killed only the CERTIFIABLE kernel

Two distinct objects:
- **Certifiable kernel** `cker := box ∩ ⋂_r ker K_r`, the pairwise-`w`-sum LP cone
  (`{z : s^r_i(z_i−c^r_i)+s^r_j(z^r_j−c^r_j)≥0 ∀i≠j}`). Monotone shrinking (each
  cut only adds `\binom d2` halfspaces), empties at `t≈d/2` — this is C3.
- **True kernel** `tker := {z∈X_t : [z,y]⊆X_t ∀y∈X_t}`, the actual star-centers.

**Theorem. `cker ⊆ tker`.** *Proof.* Let `z∈cker`. Then `z∈ker K_r` for every `r`,
i.e. `z` sees all of `K_r`. Take any `y∈X_t`. For each `r`, `y∈X_t⊆K_r`, so
`[z,y]⊆K_r`; and `z,y∈box` (convex) so `[z,y]⊆box`. Hence
`[z,y]⊆box∩⋂_r K_r = X_t`, so `z∈tker`. ∎

So the monotone emptying of `cker` (C3) says **nothing** about `tker`. **Main's
belief is confirmed: C3 killed the certifiable-LP recovery, not actual
star-shapedness.** The containment is generally strict: `cker` demands seeing the
full *unbounded* cones `K_r`; `tker` demands seeing only the carved-down body
`X_t`. As cuts accumulate `X_t` shrinks toward `x*`, so visibility gets *easier*
exactly as `cker` empties — that is the mechanism by which the two diverge, and why
a witness outside the pairwise-sum cone can still see all of `X_t` (all its
visibility-blocking cone-points lie outside `box` or outside another cut).

### 4b. Why C3 *measured* low visibility — a narrow-search + regime artifact, not a contradiction

C3's `c3_test.py::true_kernel_proxy` tries only **9 candidate witnesses**
(`samples.mean(0)` + 8 random samples), on **hit-and-run** samples, at
**`d=6,8,10`**. Main's greedy tries **~300 rejection-sampled points + all cut
apexes `{c^r}`**, on **exact-rejection** ground truth, at **`d≤5`**. Three
differences, in order of likely importance:

1. **Candidate-pool breadth (9 vs 300+).** If `tker` is a positive- but
   modest-volume set, `centroid + 8 random` will usually miss it in `d≥6`, while
   `300 + apexes` + greedy finds it. This alone can turn "best of 9 sees 0.5–0.9"
   into "best of 300 sees ~1.0."
2. **Regime `d≤5` vs `d=6,8,10`.** Main's window is strictly below C3's. `k` could
   genuinely rise with `d` (the `(d²t)^d` ceiling turning on), so C3's `d=6,8,10`
   may be the first `d` where `k>1`.
3. **Sampler.** C3 uses hit-and-run; main uses exact rejection (ground truth).
   Note the hit-and-run bias runs the *safe* way here: if HR under-explored a hard
   lobe, `S` would concentrate and visibility from a central witness would look
   *higher*, not lower. C3 still measured `0.5–0.9`, so its low visibility is not
   an HR-under-exploration artifact making things look worse — it is genuinely "the
   9 candidates can't see 10–50% of the (well-sampled) mass." That is consistent
   with a *narrow candidate pool*, and is exactly what a 300-candidate greedy tests.

**These two experiments are not comparable as run.** The clean, cheap, decisive
test (for main): **rerun main's broad greedy witness search (300 rejection points +
apexes, exact rejection) on C3's own instances at `d=6,7,8`.**
- If a `~1.0`-visibility single witness appears → C3's "genuinely non-star-shaped"
  was a **narrow-search artifact** (9 candidates); `tker` is nonempty well past
  `t=d/2`; `k=O(1)`; **Q is strongly alive and C3 §5 needs a correction.**
- If best visibility stays `0.5–0.9` and greedy needs `k=2–3` → **mild, genuine**
  non-star-shapedness at `d≥6` (`k` rising with `d`). This still does **not** kill
  Q — `k=2–3` is poly and Karp–Luby-samplable. Q dies only if `k` *explodes* with
  `d`, which this would begin to reveal.

Either outcome is decisive and informative; **neither `k=O(1)` outcome kills Q.**

### 4c. Is `tker` nonempty provable? (task item 2 — honest)

**No, not in general — and it must not be, or SSG ∈ P.** `tker` nonempty is `k=1`
(single-point star-shapedness), strictly stronger than the `k=poly` Q needs. A
*bent/offset* dumbbell (two lobes at an angle, bent neck) is not star-shaped from
any point (`tker=∅`) yet needs only `k=2`; it is a realizable-shaped body. So a
theorem "`tker≠∅` for all balanced-cut intersections" is false. (Note a *straight*
collinear dumbbell IS star-shaped from its neck — which is why dumbbells are
`k=2–3`, and why the `k=1` in-window signal is unsurprising: the realizable `d≤5`
bodies are apparently *straight*, not bent.)

What *is* clean and worth stating:
- **Apex sub-question (main asked).** A single apex `c^r∈ker K_r` (always), but
  `c^r∈ker K_{r'}` for `r'≠r` is **not** guaranteed, so no single apex is a
  provable universal witness; the last apex `c^t` (balanced center of `X_{t-1}`,
  closest to `x*`) is the natural candidate but has no proof. The empirics'
  universal witness is as likely an *interior rejection point* as an apex — which
  is precisely why C3's apex/centroid-poor 9-candidate pool underperformed.
- **The provable target is `k=poly`, not `tker≠∅`.** The right theorem remains the
  §1c pinwheel bound: balanced-central cuts keep reflex ridges non-interacting ⟹
  additive `O(dt)` reflex features ⟹ `k=poly`. The `k=1` observation is a *stronger
  in-window fact* that will not survive to a general theorem (bent dumbbell), but it
  is strong evidence that the realizable trajectory sits far inside the `k=poly`
  regime in-window.

**Net.** The `k≈1` signal is real, is the best in-window evidence Q has, and is
fully consistent with C3 once you separate `cker` (certifiably empty, monotone)
from `tker` (nonempty, non-monotone). The one thing to nail is whether C3's
`0.5–0.9` at `d≥6` is a narrow-search artifact or the onset of `k>1` — a single
cheap rerun (§4b) decides it, and both answers keep Q alive as long as `k` stays
poly in `d`.

---

## 5. The proof target: is `k(X_t) = poly(d,t)` for balanced-cut intersections?

**Verdict up front: I cannot move it — this is the terminal state.** I can (i)
pin the fight to the `d`-direction only, (ii) prove the `d=2` anchor, (iii) locate
*exactly* why the additive intuition of §1c fails (it is wrong at the level of
connected reflex *pieces*, right only at the level of supporting hyperplanes), and
(iv) show precisely what balancedness does and does not buy. What remains — forcing
the `O(d²t)` reflex hyperplanes into "few-piece" (non-general) position — is a
genuine open combinatorial-geometry statement, unmeasurable past `d≈6` and, I
argue, as hard as the isoperimetry wall it was meant to bypass. No counterexample
either: the natural one (bent-dumbbell chain) I cannot certify as realizable, and a
*fixed-`d`* one would not even refute Q. Below is the full reasoning.

### 5a. The fight is entirely in `d`; poly-in-`t` is free

The free ceiling is `k ≤ (d²t)^d` (§1a): **polynomial in `t` for fixed `d`,
exponential only in `d`.** Consequences that discipline the whole question:
- **To PROVE Q** it suffices to show `k ≤ poly(d)·poly(t)` — i.e. defeat the
  exp-in-`d` factor. Any `t`-growth (even `t^d` at fixed `d`) is already fine.
- **To REFUTE Q** a construction must exhibit `k ≥ 2^{Ω(d)}` — genuine `d`-growth.
  A body whose `k` grows in `t` at fixed `d` (e.g. `k = Θ(t)` at `d=3`) is **not**
  a counterexample; it is consistent with `k = poly`. This is why the `d=7,s1`
  outlier (`k=12`), even if real, would not refute Q — it is one point at one `d`.

So both the proof and the refutation live in the `d`-dependence, which is exactly
the unmeasurable direction. Theory is the only instrument.

### 5b. Anchor: `d=2 ⟹ k=1` (proved)

For `d=2`, `max(w_1,w_2)+min(w_1,w_2) = w_1+w_2`, so every cut `K_r` is a
*halfspace*, `X_t` is convex, `k=1` (the known `d≤2` base case,
`HitRun.lean::exists_pair_pyrUnion_subset_halfspace`). The exp-in-`d` ceiling is
switched fully off at `d=2`; the whole question is how `k` leaves `1` as `d` grows.

### 5c. Where the additive intuition of §1c breaks (the precise error)

§1c hoped: each cut adds `O(d)` reflex features, total `O(dt)`, hence `k=poly`.
The correct accounting:

- **Reflex supporting-hyperplanes ARE additive: `O(d²t)`.** `∂X_t ⊆ ∂box ∪ ⋃_r ∂K_r`.
  Each `∂K_r` lives in the `O(d²)` hyperplanes `{s^r_a(y_a−c^r_a)=±s^r_b(y_b−c^r_b)}`
  (argmax `a`, argmin `b`). The reflex (concave-from-inside) ones — the argmin-switch
  ridges of the d.c. surface `{max w + min w = 0}` (max convex, min concave: the
  concavity of `min` is the sole source of reflexivity) — number `O(d²)` per cut.
  Total distinct reflex hyperplanes `≤ O(d²t)`. **This is genuinely additive.**

- **But guard number tracks reflex PIECES, not hyperplanes — and pieces are
  exp-in-`d`.** A single reflex facet of `K_r`, once intersected with the other
  `t−1` cuts and the box, is clipped into *multiple connected components*; the
  number of pieces on one facet is the arrangement complexity of the `O(d²t)`
  clipping hyperplanes restricted to it, `= (d²t)^{d−1}` worst case. Guards see
  *pieces*: two points behind two different pieces of the reflex boundary can
  require different centers. So `k` carries the full `(d²t)^d` arrangement blow-up.
  **The additive bound holds for hyperplanes and fails for pieces — this gap is the
  exp-in-`d` ceiling, restated.**

- **Why 2D was safe and `d≥3` is not.** In 2D reflex features are isolated points
  (vertices); guard number `≤ #reflex vertices + 1`, additive — the classical
  polygon regime, exactly the `d=2` anchor. In `d≥3` reflex features are
  `(d−2)`-surfaces that *intersect each other*; the intersection of two reflex
  ridges blocks visibility in a way attributable to neither alone (higher-dim art
  gallery is provably harder, guard number super-linear in facets). The pinwheel
  cones are **infinite**, so every cut's reflex ridges reach across the whole body
  and cross every earlier cut's ridges — maximal interaction, not additive.

### 5d. What balancedness buys, and what it does not

Balancedness gives two concrete facts; neither controls the piece count.

- **`c^r` is the volume-median (Fermat–Weber) center of `X_{r−1}`.** Consequence: a
  NEW deep pocket cannot be carved by placing the apex *inside a thin existing
  pocket* — thin pockets carry little volume, so the volume-median apex sits in the
  BULK. So balancedness controls *where the apex is* (central) ⟹ new indentations
  form in the main mass, not by subdividing thin old pockets *from within*. **This
  is real and it is the entire force of "centrality."**
- **Removed = point-reflection of kept through `c^r`** (`N_r = ρ_{c^r}(K_r)`) — the
  cut is centrally symmetric about the apex.

What neither controls: **the cone boundaries `∂N_r` are infinite and global.** Even
with the apex central, the `d` wedges of `∂N_{r+1}` sweep across the entire body and
slice *far* pockets from OUTSIDE. A convex pocket cut by `d` wedges from an external
apex splits into up to `d+1` pieces — a *multiplicative*, not additive, event, and
balancedness places the apex centrally precisely so its wedges reach *all*
peripheral pockets at once. So centrality, if anything, *maximises* the reach of the
slicing boundaries across existing pockets. **Balancedness controls new-pocket
location but not old-pocket splitting; the multiplicative mechanism survives it.** I
found no lever by which volume-median centrality or central symmetry forces the
`O(d²t)` reflex hyperplanes into non-general (few-piece) position — which is what a
`poly` bound requires.

### 5e. The counterexample attempt (bent-dumbbell chain) and why it too is inconclusive

Target: a balanced, realizable trajectory whose pocket/component count multiplies by
a constant `>1` per cut, reaching `2^{Ω(d)}`. The 5d mechanism is the engine:
maintain several peripheral lobes; each balanced central pinwheel slices *each* lobe,
roughly doubling the lobe count, while staying balanced (volume halves). Iterated
`Θ(d)` times this gives `2^{Ω(d)}` lobes ⟹ `k = 2^{Ω(d)}`.

Two honest obstacles, both fatal to making it decisive:
1. **Realizability.** The cut data `(c^r,s^r)` must arise from an actual
   `ℓ∞`-contraction (`s^r = sign(f(c^r)−c^r)`, `c^r` the *induced* balanced point,
   not a free adversary). I could not exhibit an `f` forcing the wedges to
   split-rather-than-shave every lobe every round; the same
   "unrestricted-lemma-false-but-non-realizable" barrier that defused the Cheeger
   counterexamples (`summary §3`) plausibly defuses this one, and I cannot show
   otherwise on paper.
2. **Even if realizable, a fixed-`d` version is not a refutation** (5a). A confirmed
   `2^{Ω(d)}` chain needs the `d`-scaling exhibited *as `d` grows* — the unmeasurable
   regime, requiring exactly the general-position piece-count lower bound I could not
   prove.

So the counterexample is as stuck as the proof: I can describe the engine but neither
certify it realizable nor rule it out.

### 5f. Terminal reduction and honest verdict

`k(X_t)` reduces to one clean open quantity: **the number of visibility (guard)
classes of `X_t` = the number of connected pieces of its reflex boundary = the
number of distinct kernel-classes of the sign-pattern trajectory.** This is:
- `= 1` at `d=2` (proved), `1–2` empirically for `d≤5` in-window;
- `≤ (d²t)^d` always (proved), poly-in-`t`, exp-in-`d`;
- controlled in its *hyperplane* count (`O(d²t)`, additive) but NOT in its *piece*
  count (the exp-in-`d` gap); balancedness does not close that gap (5d).

It is the **same exp-in-`d` sign-pattern combinatorial object** the
condition-number-transfer work isolated as the true hardness — Q reaches it via a
different functional (guard count vs κ/Cheeger), confirming §3's finding that Q
*relocates* rather than *dissolves* the wall. The relocation has genuine value: a
guard/piece-count bound is a purely combinatorial statement about arrangements of
the cut hyperplanes and might yield to a technique the analytic routes cannot use.
But I have no such technique, the decisive `d`-scaling is unmeasurable, and neither
the `poly` bound nor a realizable `2^{Ω(d)}` refutation is within reach on paper.

**Terminal state for route Q: `k = poly(d,t)` is neither proved nor refuted; it is
equivalent to a `d`-dimensional visibility-class count sitting at the same exp-in-`d`
wall as every other route, reached from a new and cleaner (combinatorial) angle.
Consolidate.**

## §6 Conjecture X ("x* is the universal guard") — REFUTED, both forms (run by main)

Fresh angle (main): k=1 (star-shaped) coexisting with high κ (anisotropic) suggested
X_t might always be star-shaped about x*. Tested two versions:
- STRONG (x* ∈ kernel of every cut K_r, i.e. two-smallest sign-folded w_i(x*) sum ≥0):
  FALSE — fraction of cuts with x*∈ker drops 0.93→0.10 as d:4→8; min two-smallest-sum
  →−0.77. (Validity smallest+largest ≥0 holds always, as formalized: x* ∈ each K_r.)
- CORRECT (x* SEES all of X_t, the carved body): also FALSE — x* sees 1.00 in many
  instances but only 0.38–0.69 in others (d=4 s1, d=5 s1). So x* is not a reliable guard.

CONCLUSION: the star-center of X_t (which broad-greedy finds, k=1 in-window) is NOT x*
and not any fixed/known point — consistent with the true kernel being nonempty in-window
but not equal to {x*}. Eliminates the "aim at x*" route to a guarantee; the guard's
existence at scale (d≳7) remains the unmeasurable/unproven k=poly crux. Fast clean negative.
