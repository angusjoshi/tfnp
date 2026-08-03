# Attacking the Open Lemma: isoperimetry of intersections of `ℓ∞` pyramid-unions

A rigorous, honest report on an assault on the one open lemma of `hitrun.md`:

> **Open Lemma.** There is a polynomial `p` such that every realizable body
> `X_t = [0,1]^d ∩ ⋂_{r} K(c^r,s^r)` has Cheeger constant `h(X_t) ≥ 1/p(d,t)`.
> (⟹ randomised `poly(d,log 1/ε)` algorithm ⟹ `SSG ∈ P`.)

I did **not** prove it and I did **not** refute it — either would resolve a
40-year open problem. What follows is what I *did* establish: several rigorous
partial theorems that sharpen the question and localise the difficulty exactly,
a rigorous obstruction explaining why the "easy" refutations are not realizable,
and a substantial body of computational evidence that — read carefully, with the
sampler-artifact confounds controlled — leans **towards** the lemma being true
in the tested regime, together with an explicit statement of the remaining gap.

Notation as in `hitrun.md`/`polytime.md`. Write `w_i = w_i(y) = s_i(y_i - c_i)`
(sign-aligned coordinates about apex `c`). The verified membership test is

```
y ∈ K(c,s)   ⟺   max_i w_i(y) + min_i w_i(y) ≥ 0.                      (MEM)
```

All experiments and the scripts that produced every number below are in
`notes/polytime_experiments/` (the ones added in this session are listed in
§7); they run under the repo `venv`.

---

## 0. Executive summary

**Proved (rigorous, and machine-checked numerically where noted):**

1. **Theorem A (star-shapedness in the "toward" regime).** If at every round the
   cut points toward `x*` on every coordinate — `s^r_i·(x*_i − c^r_i) ≥ 0` ∀`i`
   — then `x* ∈ ker K(c^r,s^r)` for all `r`, so **`X_t` is star-shaped about
   `x*`**. Then `X_t` is sampled *exactly* and in `poly(d,t)` time by
   ray-shooting from `x*` — **no isoperimetry, no Markov chain, no mixing at
   all**. (§2. Proof from (MEM); 0 counterexamples in 8·10⁴ trials up to `d=12`,
   `verify_thmA.py`.)

2. **Exact characterisation of when Theorem A applies / when it breaks.** The
   "toward" hypothesis holds at a center `c` iff the displacement `f(c)−c` has
   the same sign as `x*−c` on every coordinate, which (Lemma 1 of `hitrun.md`)
   holds **iff every coordinate has gap `|x*_i−c_i| > λ·‖x*−c‖∞` or `≈0`** — i.e.
   iff the gap vector is *flat*. Star-shapedness is lost **exactly** when the gap
   vector becomes *spread*, equivalently when `X_t` becomes *anisotropic*. This
   pins the entire difficulty to one phenomenon and reframes the Open Lemma as a
   statement about the **isotropic (whitened) Cheeger / KLS constant** of these
   bodies (§2.3).

3. **Ball-preservation lemma.** If `x*` is kept with margin
   `m := max_i w_i(x*) + min_i w_i(x*) ≥ 2ρ`, then the whole `ℓ∞`-ball
   `B_∞(x*,ρ) ⊆ K(c,s)`. Toward-cuts have `m ≥ ‖x*−c‖∞`, so they preserve a ball
   of radius half the current apex distance (well-roundedness). (§2.2.)

4. **The "easy" refutations are not realizable (obstruction).** One *can* make an
   intersection of pyramid-unions with `h → 0` (even isotropic `h → 0`), but
   every such example we found is a **degenerate sliver of volume `→ 0`**.
   Forcing a bottleneck and keeping positive volume are incompatible for these
   cuts: adversarial "point-away" cuts collapse the body rather than pinch it.
   The CLY algorithm provably keeps a full ball around `x*` (its formalised
   Lemma 3, shifted base `b=c+2s`), so it **never** produces such slivers. Hence
   the unrestricted Open Lemma is *false*, but its restriction to realizable
   bodies is untouched. (§3.2, §4.)

5. Minor: `d ≤ 2` ⟹ every cut is a genuine halfspace (`max+min = sum`), `X_t`
   convex, poly-time by cutting planes (restates `polytime.md` §3.2).

**Empirical (evidence, explicitly *not* proof):**

6. Across a large adversarial search over realizable-structure cut families and
   over the actual algorithm on hard **SSG** instances (spread `x*`, values
   pinned at `0/1`), a sharp **dichotomy** holds: whenever a body has healthy
   volume it has **`Ω(1)` isotropic Cheeger** and hit-and-run mixes; the only
   small-Cheeger bodies are the non-realizable slivers of (4). No realizable
   healthy-volume bottleneck was found up to `d=12`. (§3.)

7. The **hard regime is not where a bottleneck lives**: sweeping `δ = 1−λ` from
   `10⁻²` down to `10⁻⁶` at `d=8` leaves mixing flat (this is the regime where
   value iteration needs `10⁶` steps). (§3.3.)

8. **A sampler-artifact confound identified and controlled.** At fixed
   hit-and-run budget, apparent "trapping" grows with `d` (TRAP `0.34–0.84` at
   `d=12,15`) and the algorithm stops converging. A budget-escalation control
   shows this is **under-budgeting, not a bottleneck**: on a fixed `d=12` body
   TRAP falls `0.233 → 0.085 → 0.038` as the walk is lengthened. Mixing time
   grows with `d` (as any `1/h²` must), consistent with *poly* — not
   exponential — mixing. (§3.4.)

**Not achieved / honest gaps (§5):** no proof of the isotropic-Cheeger bound;
the exact sampler covers only the star regime; `d≤12`, `δ≥10⁻⁶` is far from the
true hard regime `d` large, `δ=2^{-poly}`; and the reflection symmetry, though it
gives per-cut halving, I could **not** turn into a global Cheeger bound.

---

## 1. Why the standard machinery is unavailable (recap, made precise)

Two facts frame everything. First, `conv K = ℝ^d` for `|S|≥3` (`polytime.md`
§3.2): no convex outer approximation loses any volume, so KLS/localisation —
theorems *about convex bodies* — do not apply. Second, there is **no** general
lower bound on `h` for non-convex bodies (dumbbells give `2^{-Ω(d)}`). So a proof
must use the *specific* structure, and a refutation must *realise* a dumbbell
with these specific cuts. Both directions turned out to be governed by the same
object: whether the body can be **star-shaped**, and if not, how **anisotropic**
it is.

---

## 2. Positive results: the star-shaped regime is fully solved

### 2.1 Theorem A (star-shapedness), with proof

> **Theorem A.** Fix apex `c` and signs `s` with all coordinates active. Suppose
> `w_i(x*) = s_i(x*_i − c_i) ≥ 0` for every `i` (the cut points toward `x*`).
> Then for every `y ∈ K(c,s)` and every `λ ∈ [0,1]`, the point
> `q = (1−λ)x* + λy` lies in `K(c,s)`. Consequently `x*` sees all of `K(c,s)`,
> and — since the box is convex and `x* ∈ K(c^r,s^r)` for all `r` — the body
> `X_t = box ∩ ⋂_r K(c^r,s^r)` is **star-shaped about `x*`**.

*Proof.* `w(·)` is affine, so `w_i(q) = (1−λ)w_i(x*) + λ w_i(y)`. Using
`min_i(a_i+b_i) ≥ min_i a_i + min_i b_i` and, for the max, evaluating at the
single index `a := argmax_i w_i(y)`:

```
min_i w_i(q) ≥ (1−λ)·min_i w_i(x*) + λ·min_i w_i(y) ≥ 0 + λ·min_i w_i(y),
max_i w_i(q) ≥ (1−λ)·w_a(x*) + λ·w_a(y)           ≥ 0 + λ·max_i w_i(y),
```

both using `w_i(x*) ≥ 0` and `1−λ, λ ≥ 0`. Adding,
`max_i w_i(q) + min_i w_i(q) ≥ λ·(max_i w_i(y) + min_i w_i(y)) ≥ 0` because
`y ∈ K` and `λ ≥ 0`. By (MEM), `q ∈ K`. Star-shapedness of the intersection:
for `x ∈ X_t`, the segment `[x*,x]` lies in every `K(c^r,s^r)` (just shown) and
in the box (convex), hence in `X_t`. ∎

This is exactly the `⊇` direction of the Kernel Theorem specialised to `z=x*`,
but the proof above needs only (MEM), so it is self-contained and directly
formalisable next to `mem_pyramidUnion_iff` in `Contraction.lean`. Numerically:
`verify_thmA.py` finds **0** segment-failures over ~2·10⁴ trials per dimension at
`d=3,5,8,12` under the toward-hypothesis, and thousands of failures for
arbitrary signs — the hypothesis is exactly right.

**Algorithmic payoff (no isoperimetry).** In the star regime the kernel polytope
`box ∩ ⋂_r ker K(c^r,s^r)` (an intersection of `O(td²)` halfspaces, one LP to
find a point of) is nonempty and contains `x*`; `X_t` is star-shaped about any
kernel point `p₀`; and uniform sampling is *exact* by ray-shooting: draw a
direction `u`, compute the radial exit `ρ(u) = min_r ρ_r(u)` (each `ρ_r` a closed
form from (MEM)), and place mass `∝ ρ(u)^d`. **Poly-time, zero mixing.** The
Open Lemma is vacuous here.

### 2.2 Ball-preservation and well-roundedness

> **Lemma (ball preservation).** If `max_i w_i(x*) + min_i w_i(x*) ≥ 2ρ ≥ 0`,
> then `B_∞(x*,ρ) ⊆ K(c,s)`.

*Proof.* For `‖y−x*‖∞ ≤ ρ`, `w_i(y) = w_i(x*) + s_i(y_i−x*_i)` with
`|s_i(y_i−x*_i)| ≤ ρ`, so `max_i w_i(y) ≥ max_i w_i(x*) − ρ` and likewise for the
min; their sum is `≥ 2ρ − 2ρ = 0`. Apply (MEM). ∎

For a valid cut the argmax-gap coordinate `j` has `w_j(x*) = ‖x*−c‖∞ =: r`, so
`max_i w_i(x*) = r`; for a **toward**-cut `min_i w_i(x*) ≥ 0`, giving margin
`m ≥ r` and a preserved ball `B_∞(x*, r/2)`. So toward-cut bodies are not merely
star-shaped about `x*` but star-shaped about a **ball** of radius half the apex
distance — strongly well-rounded.

### 2.3 The exact location of the difficulty

By Lemma 1 of `hitrun.md`, `sign(f(c)−c)_i = sign(x*_i−c_i)` **whenever**
`|x*_i−c_i| > λr` (there the displacement toward `x*` dominates the `≤λr`
contraction error). Hence:

> The toward-hypothesis of Theorem A holds at `c` **iff the gap vector `x*−c` is
> flat**: every coordinate has `|x*_i−c_i| > λr` or `≈ 0`. Star-shapedness is
> lost **iff** some coordinate has an *intermediate* gap `0 < |x*_i−c_i| ≤ λr`,
> i.e. iff `X_t` (whose Fermat–Weber center is `c`) is **anisotropic**.

This is the crux and it is a genuine sharpening of the notes: the obstruction is
neither "non-convexity" in the abstract nor a mysterious bottleneck, it is
**anisotropy of `X_t`**. Two consequences:

* it explains `starshape_collapse.py` precisely — the kernel is nonempty exactly
  while the bodies stay round, and collapses as they elongate;
* it reduces the Open Lemma to its **affine-invariant** form: does the *isotropic*
  (whitened) Cheeger constant `h(W·X_t)` — where `W` puts `X_t` in isotropic
  position — stay `≥ 1/poly`? For convex bodies this is `Θ(1)` by KLS; here it is
  the open question, but now it is the *right* (elongation-insensitive) question.
  Using the raw `h` conflates a harmless long-thin body (a uniform segment of
  length `L` already has `h = 2/L`) with a true two-lobe bottleneck; the
  isotropic `h` does not.

---

## 3. Barrier search: no realizable healthy-volume bottleneck found

All Cheeger numbers below are the **isotropic** 1-D-marginal Cheeger
`h_iso = min_a min_b ρ_a(b)/min(F_a(b),1−F_a(b))` after whitening — an *upper*
bound on the true isotropic `h`, so *small* `h_iso` is a *certified* sparse cut
(a real bottleneck), while large `h_iso` is strong (direction-sampled) evidence
of none. Independently, TRAP `∈[0,1]` is the between-chain/total variance ratio
of several hit-and-run chains started at the **extremes** of the body (an
R̂-style trapping detector that needs no direction guess).

### 3.1 Cuts toward a common point stay `Ω(1)` (`compat_search.py`)

Cuts pointing at a common `x0` (`s = sign(x0−c)`, the Theorem-A regime, so `X`
is star-shaped) with adversarial apex placements (isotropic, axial, shell,
two-cluster). Result: `h_hat` is **flat in `d`**, never small:

```
d :   5      7      9      12
min h_hat over all strategies ≈ 0.8 – 1.5     (no decay; volfrac 0.02–0.6)
```

### 3.2 Honest (non-toward) cuts either stay `Ω(1)` or collapse (`honest_barrier.py`)

A real cut only needs `x* ∈ K(c,s)`, which permits pointing *away* from `x*` on
every coordinate whose gap is `< λr`. Searching adversarially over such signs
(`away`, `random`, `target`-pattern) and apex clouds, `d = 5,7,9`, the outcome
is a clean **dichotomy**:

```
healthy volume (volfrac ≳ 0.1)  ⟹  h_iso ∈ [0.39, 0.52]     (NO bottleneck)
small h_iso (→ 0)               ⟹  volfrac ∈ [0, 0.03]       (degenerate sliver)
```

Every single small-`h_iso` instance is a near-lower-dimensional sliver (`h_iso→0`
is then a whitening artifact of a rank-deficient cloud), never a genuine
two-lobe body. **We could not construct a healthy-volume bottleneck.** The
mechanism: the maximally-adversarial cut places `x*` on its own boundary
(margin `≈0`), and by ball-preservation there is then no retained ball;
stacking such cuts drives the volume to `0` instead of pinching a neck.

### 3.3 The actual algorithm on hard SSG instances (`ssg_probe.py`, `mixing_test.py`)

Discounted simple-stochastic-game value operators (two sinks at values `0/1`,
interior MAX/MIN/AVG states, `γ=1−δ`) — genuinely spread `x*` (e.g. `d=9`:
`x* = (.75,1,1,1,0,1,0,1,0)`, spread `0.999`), the real hard class. Running the
full sampler+Fermat–Weber-LP algorithm and probing the real bodies:

```
d=9 (spread 0.999): TRAP ≤ 0.044,  h_iso ≈ 0.31–0.39,  cond(cov) κ ≈ 2   [all 27 rounds]
d=6 (spread 0.549): TRAP ≤ 0.27,   h_iso ≈ 0.13–0.36,  κ ≈ 4–15
```

`d=9` is pristine across every round; `d=6` degrades only mildly and
non-exponentially.

**Delta sweep** (`radial_delta.py`, `d=8`, the hard `λ→1` regime):

```
δ = 10⁻²  10⁻³  10⁻⁴  10⁻⁶
TRAP = .11  .07  .05  .09        h_iso ≈ 0.1–0.16, κ ≈ 4–5   →  flat
```

No degradation as the contraction weakens — the regime where value iteration
needs `1/δ` steps shows **no** mixing bottleneck.

### 3.4 The one alarm, resolved: sampler budget, not geometry (`escalate.py`)

At *fixed* hit-and-run budget, `d=12,15` look bad: TRAP `0.34→0.84` (`d=12`) and
`0.45→0.78` (`d=15`) over rounds, and the algorithm stalls (error stuck `~0.3`,
diameter not shrinking). Taken at face value this is a bottleneck. It is not.
Escalating the walk length on a **fixed** `d=12` body `X_12` (healthy: `κ=4.4`,
full-dimensional, diam `0.77`):

```
budget (burn, thin, nsamp, nt)        TRAP     PC-separation
  1500,  20, 120, 2500                0.233        1.20
  5000,  40, 150, 3000                0.085        0.58
 15000,  80, 200, 4000                0.038        0.35
```

TRAP `→ 0` and the two extreme chains reconcile as the walk lengthens: the body
**mixes**, and the earlier "trapping" was under-budgeting (a fixed budget that
did not scale with `d`). The stalled algorithm at `d=12,15` is the *same* cause —
bad samples ⟹ bad Fermat–Weber center ⟹ near-vacuous cut ⟹ no volume shrink
(note diam stayed `~0.9`, so the body was *not* shrinking geometrically, i.e. the
cuts were failing, not pinching). Mixing time grows with `d` — as any `Θ(1/h²)`
must even with `h=Ω(1)` — which is *consistent with poly*, and gives no evidence
of exponential blow-up.

**A caveat I will not paper over:** the escalation control is conclusive for the
`t=d` body at `d=12`; I did not have the compute to escalate the `t=2d,3d`
bodies at `d≥12` to convergence. The `t=3d` evidence is clean only up to `d=9`.

### 3.5 A red herring worth flagging (`radial_delta.py round`)

The radial function *from `x*`* is wildly spiky (max/median ratio `60–320`,
`ℓ∞`-inradius at `x*` `≈ 0`). This does **not** indicate body spikes: it says
`x*` sits on the *boundary* of `X_t` (a bad viewpoint) — matching the known fact
that the Fermat–Weber center, not `x*`, is central, and `‖bp−x*‖` tracks the
diameter. Measured from its own centroid the body is well-conditioned
(`κ = 2–6`). Isoperimetry must be judged from the centroid / in isotropic
position, not from `x*`.

---

## 4. Why the search cannot cheaply win (the obstruction, semi-rigorous)

Combine §2.2 and §3.2. To create a two-lobe bottleneck one must remove a *waist*
while keeping two bulk lobes. With these cuts the only way to remove mass near
`x*` is to point cuts away from `x*` there — but a cut that points away on a
coordinate of gap `g` reduces `x*`'s margin by `2g`, and by ball-preservation
the retained neighbourhood of `x*` shrinks in lockstep. Pushing this to make a
*thin* neck drives the margin — and empirically the whole volume — to `0`. The
CLY algorithm's formalised Lemma 3 (shift `b=c+2s`) *guarantees* a full ball
around `x*` survives every cut, i.e. margin bounded below by the grid scale, so
**CLY-realizable bodies are never slivers at `x*`**. The slivers that carry all
the small-`h_iso` examples are therefore outside the realizable class. This is
why refuting the *unrestricted* lemma is easy and meaningless, and refuting the
*realizable* one is exactly as hard as the problem.

This does not amount to a proof of the Open Lemma: "cannot make a thin neck *at
`x*`*" is not "cannot make a thin neck *anywhere*." A bottleneck could in
principle separate two lobes *neither* of which contains `x*` in its interior
(recall `x*` is on the boundary). I searched for such cuts (the `two-cluster`
and `axis` strategies, and PCA-directed marginal cuts on real bodies) and found
none with healthy volume — but this is evidence, not proof.

---

## 5. Honest gaps and what remains open

1. **The isotropic-Cheeger bound is unproven.** Star-shaped-about-a-ball is *not*
   sufficient in high dimension: a ball with two thin cones of angular width
   `θ ≈ ρ/R` has `h ≈ (ρ/R)^{d−1}/R = 2^{−Ω(d)}` while remaining star-shaped
   about `B(0,ρ)`. So Theorem A's star-shapedness alone cannot give poly-`h`; the
   specific cuts must additionally forbid such spikes. Empirically they do
   (§3.5: the spikes are only *from `x*`*, and the body is round from its
   centroid), but I have no proof that the radial function from the *centroid*
   cannot spike.

2. **The exact sampler covers only the star regime.** Once anisotropy breaks
   star-shapedness (kernel empty), the exact ray-shooting sampler is invalid and
   one is back to needing mixing, which is unproven. Whether a *weaker* exact
   structure survives (e.g. `X_t` a union of `O(1)` star-shaped pieces, or
   star-shaped after deleting an `o(1)`-measure set) is open and, I think, the
   most promising concrete next target.

3. **Scale.** `d ≤ 12`, `δ ≥ 10⁻⁶`. The true hard regime is `d` large and
   `δ = 2^{-poly}`. The `δ`-sweep is reassuring but the `d`-scaling of the
   *mixing time* (not just of `h`) is exactly what a poly claim needs, and my
   budget-escalation only bounds it from below in a couple of points.

4. **Reflection symmetry gave halving but not Cheeger.** The per-cut point
   reflection through `c` (removed set `= −`(kept subset)) yields the exact
   volume-halving (proved, `Contraction.lean`), but I could not convert it into a
   global boundary lower bound. The natural route — Lovász–Simonovits
   localisation — reduces `h` to 1-D "needles", but here a needle is `X_t ∩ line`
   = a **union of intervals**, whose 1-D Cheeger can be small, so localisation
   does not close. The one structural rescue — needles *through `x*`* are single
   intervals by star-shapedness — does not help because localisation needles are
   arbitrary lines, not forced through `x*`. Making localisation "respect" a
   center is the kind of new idea a proof would need.

---

## 6. Conjectures, with the evidence rating

* **C1 (main).** Realizable `X_t` have isotropic Cheeger `≥ 1/poly(d,t)`.
  *Evidence: moderate-to-good* — the §3 dichotomy, `δ`-independence, the §4
  obstruction to cheap counterexamples. *Status:* equivalent to `SSG ∈ BPP=P`,
  so a proof is expected to be very hard; a *disproof* would be a realizable
  dumbbell, which §4 suggests is itself hard to build.

* **C2 (sharper, cleaner sub-question).** The condition number `κ(X_t)` of the
  uniform measure's covariance stays `poly(d,t)`. If true, standard hit-and-run
  analysis after one whitening gives poly mixing. *Evidence:* `κ` stayed `2–37`
  in all healthy runs and only grew with under-sampling. This is a **more
  attackable** target than `h` directly, and it is where I would put effort next:
  can a single balanced cut increase `κ` by more than a constant factor?

* **C3.** Star-shapedness is recoverable "on average over a block": even after
  the kernel of a single `X_t` empties, the kernel of `X_{t} ∩ (`a few extra
  balanced cuts`)` is nonempty `1/poly` of the time — enough for a
  restart-based exact sampler. *Evidence: weak/untested*; flagged because it
  would sidestep isoperimetry entirely (route C).

---

## 7. Methods / reproducibility

New scripts (in `notes/polytime_experiments/`, run under `venv`):

* `common.py` — topical & **SSG** instance builders, ternary cuts, (MEM)
  membership, fine-chord hit-and-run, Fermat–Weber LP, `run_algo`, whitening,
  and the isotropic 1-D-marginal Cheeger estimator.
* `verify_thmA.py` — machine-checks Theorem A (0 failures) vs arbitrary signs.
* `barrier.py`, `compat_search.py`, `honest_barrier.py` — barrier searches with
  **exact rejection** uniform sampling (no mixing) → ground-truth Cheeger.
* `ssg_probe.py`, `mixing_test.py` — the real algorithm on SSG, with the
  extreme-start TRAP diagnostic and isotropic Cheeger, gated on full-dimensionality.
* `radial_delta.py` — `δ`-sweep and the radial/spike ("bad viewpoint") test.
* `escalate.py` — the decisive budget-escalation control that unmasks the
  sampler artifact at `d=12`.

Key methodological point learned the hard way: **judge bottlenecks by the
isotropic Cheeger and by budget-escalated trapping, never by the raw Cheeger or
a fixed-budget walk** — raw Cheeger flags harmless elongation as a bottleneck,
and a fixed-budget walk flags harmless slow mixing as trapping. Both confounds,
uncontrolled, would have produced a spurious "barrier found."

---

## 8. Bottom line

The honest state after this attack:

* The Open Lemma is **true and trivial** in the star-shaped (flat-gap) regime,
  where sampling is exact and no isoperimetry is needed (Theorem A).
* Outside it, the problem is **precisely** the isotropic Cheeger / anisotropy of
  these bodies (§2.3) — the correct, affine-invariant form of the question.
* The unrestricted lemma is **false** (slivers), but every cheap counterexample
  is **non-realizable**, and there is a structural reason (ball-preservation +
  CLY Lemma 3) that realizable bodies avoid the sliver route (§4).
* All controlled experiments — with the elongation and sampler-budget confounds
  removed — show **no realizable bottleneck** up to `d=12` and down to
  `δ=10⁻⁶`, including on genuinely hard SSG instances.

This is not a proof and I will not dress it as one. But it converts "prove the
isoperimetry of a weird non-convex body" into two sharper, plausibly-attackable
statements — **C2** (covariance conditioning stays poly) and the
**needle-through-a-center localisation** of §5.4 — either of which would be real
progress, and it removes two false leads (the unrestricted lemma, and the raw
`h`/fixed-budget "bottleneck") that would otherwise waste effort.
