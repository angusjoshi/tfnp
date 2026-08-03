# Rogue ideas — cross-field routes to poly-time ℓ∞-contraction fixpoints (SSG ∈ P)

Bold-but-concrete conjectural connections to other areas of math, each aimed at a
poly-time uniform sampler for `X_t = box ∩ ⋂_r K(c^r,s^r)` (⟹ SSG ∈ P), or at the
scale-free κ-contraction crux (`κ(X∩K) ≤ (1+o(1))κ(X)` for a balanced cut), or at a
route that **bypasses sampling entirely** by exploiting SSG's monotone + piecewise-linear
value operator.

Format per idea: (1) connection, (2) mechanism, (3) lemma/algorithm it would yield,
(4) how to test/refute. Advisor verdicts appended as `» ADVISOR:` under each.

Background already covered (do NOT re-propose vanilla forms): Cheeger `h`, covariance
`κ`, star-shaped/kernel exact sampler, SMC/Gibbs on `[d]^t`, topical/tropical framing,
Lovász–Simonovits localization. The notes localize the whole difficulty to a
**realizable anisotropic/dumbbell `X_t`**; the freshest un-closed lead is
"asymmetric repair out-paces thin-axis creation, from the isotropic (box) start."

---

## BATCH 1

### Idea A [TOP] — Local stability of the "isotropy" fixed point of the shape-renormalization flow
**(1) Connection.** Dynamical systems / Lyapunov stability & renormalization-group
fixed points. (Not global bounded-κ — which the notes show is FALSE for the idealized
symmetric downdate on graded spectra — but *local basin* stability.)

**(2) Mechanism.** Define the shape-renormalization map `S` on whitened bodies:
`shape → (balanced cut X∩K) → re-whiten to unit covariance trace`. The isotropic body
is a fixed point of `S` (box base case: a balanced cut of an isotropic body re-whitens
to ≈ isotropic; `κ(box∩K)→1`). The real algorithm **starts at the box = at/near this
fixed point.** So we do not need global bounded-κ; we need only that isotropy is a
*stable* fixed point of `S` and that the box lies in a basin where `κ` stays poly for
`poly` steps. Work in log-eigenvalue coordinates `ℓ_i = log λ_i` (the scale-free
coordinates). Linearize `S` at isotropy: by permutation symmetry the Jacobian `J` is
equicorrelation `aI + b·11ᵀ`, so it has just two eigenvalues; the relevant one is `a`
on the trace-perpendicular (anisotropy) subspace. If `|a| < 1`, anisotropy *decays* and
`κ = 1 + o(1)` is maintained along the trajectory.

**(3) Lemma/algorithm.** "The Jacobian of the balanced-cut+renormalize map at isotropy
has spectral radius `ρ < 1` on the trace-perp subspace. Hence ∃ `r > 0` s.t. any body
with log-spectral-spread `< r` keeps spread `< r/(1−ρ)` for ALL `t`; the box has spread
`0`, so `κ(X_t) ≤ poly` for all `t`." Even a *local* result with basin radius `1/poly`,
plus a proof the trajectory never leaves it, closes the scale-free-κ crux ⟹ SSG ∈ P.
This is the precise operationalization of the Cycle-4 reframing: the **asymmetric
injection term** `2Σ−Σ(R)` is exactly what could push the thin-axis eigenvalue of `J`
below 1 (the symmetric-only model has it neutral/≥1 — that's why the idealized model
fails). So the test isolates whether asymmetry stabilizes isotropy.

**(4) Test/refute.** Compute `J` by finite-differencing the *full* (asymmetric)
one-cut-then-renormalize map on near-isotropic bodies (perturb one `ℓ_i` by ε, measure
response of all `ℓ_j`), at `d = 4..8`, via exact rejection. Extends `idealized_dynamics.py`
which already has the symmetric-only version. **Refuted** if `ρ ≥ 1` on a non-trace
direction even WITH the asymmetric term — meaning isotropy is unstable and anisotropy
grows; **supported** if `ρ` is bounded below 1 uniformly in `d` (or `1 − 1/poly(d)`).
» ADVISOR: (pending)

### Idea B [TOP] — Sampling `X_t` ≡ conductance of a volume-weighted subgraph of the Hamming graph `[d]^t`
**(1) Connection.** Spectral graph theory / expansion of product graphs — a *discrete*
reformulation of the continuous isoperimetry.

**(2) Mechanism.** Measure-disjoint cell decomposition (polytime.md §3.1):
`X_t = ⊔_{π∈[d]^t} P_π`, each `P_π` a convex polytope (`≤ 2(d−1)t+2d` facets). Build the
cell graph `G_t`: nodes = nonempty cells, node-weight `vol(P_π)`; edge `π ~ π'` iff they
differ in exactly one round-coordinate `r` and share a `(d−1)`-facet, edge-weight =
shared facet area. A hit-and-run line crossing a facet is exactly a move on `G_t`, and
within each convex cell mixing is poly (KLS). So **poly mixing of `X_t` ⟸ conductance
`Φ(G_t) ≥ 1/poly`.** Crucially `G_t` is a *subgraph of the Hamming graph* `H(t,d)`
(differ in one coordinate), which is an excellent expander; the only way `Φ(G_t)` can be
small is a huge volume imbalance across an adjacent pair.

**(3) Lemma/algorithm.** "For facet-adjacent realizable cells,
`vol(P_π)/vol(P_{π'}) ≤ poly(d,t)`, and each nonempty cell keeps `≥1` nonempty neighbor
per round-coordinate ⟹ `Φ(G_t) ≥ Φ(H(t,d))/poly = 1/poly` by a Diaconis–Stroock /
canonical-paths comparison." Changing one cut's winning coordinate is a *geometrically
local* perturbation, so the bounded-ratio hypothesis is plausible and is the clean crux.

**(4) Test/refute.** On small `(d,t)` enumerate nonempty cells (F–H already do this in
their `(nd)^{O(d)}` enumeration), build `G_t`, compute `λ_2`/`Φ`, and measure the max
adjacent volume ratio and its scaling in `d,t`. **Refuted** if a realizable adjacent
pair shows exp-large volume ratio (a genuine combinatorial bottleneck). This turns the
open isoperimetry into an *enumerable, finite* graph-expansion question.
» ADVISOR: (pending)

### Idea C — Free-probability spectral fixed point / Dyson-BM-with-reflecting-walls for `Σ(X_t)`
**(1) Connection.** Random matrix theory / free probability — spectral dynamics under
repeated structured covariance updates.

**(2) Mechanism.** The covariance update `Σ(X∩K) = 2Σ − Σ(R) − ½ΔΔᵀ` (D) is, per cut, a
low-rank/structured perturbation. Over rounds the empirical spectral distribution (ESD)
of `Σ_t` (rescaled to fixed trace) evolves like an interacting particle system in the
log-eigenvalues: the balanced downdate is a "reflecting wall at the top" (shaves the
largest, `α = m_K²/λ_max ≈ 0.6–0.75` on the top axis) and the asymmetric injection is a
"push at the bottom." If this flow has a **free/RG stationary ESD** with support bounded
away from `0` and `∞` (independent of `t`, mild in `d`), then `κ = O(1)`.

**(3) Lemma/algorithm.** "The rescaled ESD of `Σ_t` converges to a fixed-point measure
`ν_*` with `supp ν_* ⊂ [1/poly, poly]`." Handle: the "spread `= Σ(logλ−mean)²` is a
Lyapunov" finding is exactly the *logarithmic energy / free entropy* of the spectral
measure decreasing — the standard object whose descent forces convergence to `ν_*`.
Quantifying the *reflecting* effect at the bottom (asymmetric injection) as a hard wall
at `1/poly` gives the `λ_min` lower bound the notes lack.

**(4) Test/refute.** From existing exact-rejection trajectories, plot the ESD of `Σ_t`
over rounds at fixed `d`; test convergence to a `t`-independent shape and check for
level-repulsion (β-ensemble signature) in the log-eigenvalue gaps. **Refuted** if the
ESD keeps spreading (no stationary support) — i.e., the bottom edge drifts to 0. Cheap:
reuses saved trajectories.
» ADVISOR: (pending)

### Idea D [TOP, sampling-bypass] — Policy/sign stabilization: identify the optimal SSG policy in poly rounds, exact early stop
**(1) Connection.** Combinatorial game theory + LCP / unique-sink-orientation structure,
exploiting the *monotone piecewise-linear* value operator directly.

**(2) Mechanism.** At balanced center `c^r`, the ternary sign `s^r = sign(f(c^r) − c^r)`
records, per coordinate, which action is currently *improving* (the Bellman-residual
direction). The value operator `T` of an SSG is monotone + PL; its graph is an
arrangement of policy-hyperplanes, and `x*` lies in the (open) optimality cell of the
*optimal policy pair* `σ*`, whose induced sign pattern is FIXED. Conjecture: once the
balanced center falls into that cell, all later signs equal `σ*`'s signs. `X_t` shrinks
geometrically (`2^{-1/d}`/round) around `x*`, and grid-rational data give `x*` a
`1/2^{poly}` optimality margin, so the center enters the cell after `O(d·poly)` rounds.

**(3) Lemma/algorithm.** "Sign-stabilization stopping rule": track the induced policy
`σ_r` from the sign history; when `σ_r` is locally optimal — checkable by ONE Bellman
step on the exact linear-system solution `x_{σ_r} = (I−γP_{σ_r})^{-1} r_{σ_r}`,
i.e. `T(x_{σ_r}) = x_{σ_r}` — output `x_{σ_r}` EXACTLY, bypassing the sampler for the
endgame. Correctness is the policy-iteration optimality certificate. Open piece: bound
rounds-to-stabilization by poly, using that centers are Fermat–Weber points (well-centered,
non-adversarial) of nested geometrically shrinking bodies all containing `x*`.

**(4) Test/refute.** Run the existing `algo_topical.py` loop on SSG instances; log
per-round signs and rounds-to-stabilization vs `d` and vs optimality margin `δ`.
**Refuted** if stabilization needs `2^{Ω(d)}` rounds, or if it requires the sampler to
already be accurate (chicken-and-egg: the center is only good if sampling is good).
Cheapest possible test of a genuine sampling-bypass; maximally uses SSG structure.
» ADVISOR: (pending)

### Idea E — Homotopy continuation in the discount `γ`: track `x*(γ)` from easy to hard
**(1) Connection.** Numerical algebraic geometry / real algebraic geometry / parametric
LP; the value is a semialgebraic function of the discount.

**(2) Mechanism.** `x*(γ)` = fixed point of the discounted operator `T_γ`; trivial at
`γ=0`, target as `γ→1`. On each policy cell, `x*(γ) = (I−γP_σ)^{-1} r_σ` — rational in
`γ` of poly degree. The path is piecewise-linear-fractional; breakpoints = policy
switches. Predictor–corrector continuation solves each segment exactly.

**(3) Lemma/algorithm.** "The number of optimal-policy switches along `γ ∈ [0,1)` is
`poly(n)`." Then continuation is poly. Reframes the classic "is there a short improving
path in the SSG USO" as *path length in the discount parameter* — a 1-D, ordered version
(monotone in `γ`) that may be far more controllable than the combinatorial cube.

**(4) Test/refute.** On SSG instances, finely discretize `γ∈[0,1)` and count
optimal-policy switches. **Refuted** if switches grow as `exp(Ω(n))`. Directly probes
whether the ordered-by-`γ` path is short.
» ADVISOR: (pending)

### Idea F — Ollivier–Ricci curvature of hit-and-run via a reflection coupling
**(1) Connection.** Discrete Ricci curvature / coarse geometry of Markov chains
(Ollivier, Joulin).

**(2) Mechanism.** Positive coarse Ricci curvature `⟹` poly mixing AND Gaussian
concentration. Construct an explicit coupling of two hit-and-run steps from nearby
`x, x' ∈ X_t` sharing the random direction `u`, and exploit the two structural gifts the
raw Cheeger route can't: (i) star-shapedness early (segments to a kernel point stay
inside), (ii) each cut's removed set is the exact point-reflection of the kept set
through `c`. Use a reflection/parallel coupling so the shared line's intersection
intervals in `X_t` are near-congruent for `x,x'`, contracting `E‖X_1 − X_1'‖`.

**(3) Lemma/algorithm.** "Coarse Ricci curvature of hit-and-run on realizable `X_t` is
`≥ 1/poly(d,t)`" via the reflection coupling ⟹ poly mixing. New handle: the coupling is
built from the reflection symmetry, an object localization can't use.

**(4) Test/refute.** Numerically estimate the `W_1` contraction of one-step distributions
from paired starts across the body; report min curvature. **Refuted** if curvature `→ 0`
at a neck (the dumbbell again) — but the coupling *construction* is the deliverable and
may certify curvature on realizable bodies where slivers are excluded.
» ADVISOR: (pending)

### Idea G — The balanced cut as a JKO/proximal step of a displacement-convex functional
**(1) Connection.** Optimal transport / Wasserstein gradient flows (JKO minimizing
movements).

**(2) Mechanism.** The sequence `μ_t = uniform(X_t)` is generated by conditioning on a
balanced half. Ask whether `μ_{t+1}` is (approximately) one JKO step of a functional
`F(μ) = Φ_μ(c*(μ))` (Fermat–Weber value at the balanced center) + a volume/entropy term.
If `F` is *displacement convex*, its gradient flow contracts in `W_2`, forcing `μ_t`
toward an isotropic profile ⟹ bounded κ.

**(3) Lemma/algorithm.** Identify `F`, show conditioning-on-balanced-half ≈ its JKO step,
and prove displacement convexity ⟹ geometric contraction of anisotropy.

**(4) Test/refute.** Check whether the cut update decreases a candidate `F` *geometrically*
(not just monotonically) on real trajectories. **Likely refuted** on hard spread-`x*`
instances (repair_attack shows bounded-with-drift, not geometric) — but a successful
functional identification would be the missing Lyapunov.
» ADVISOR: (pending)

### Idea H — Submodular coverage: reduce per-round center certification from `2^d` directions to poly
**(1) Connection.** Submodular optimization / combinatorial optimization.

**(2) Mechanism.** `μ(K(c,S)) = μ(⋃_{i∈S} P_i^{s_i}(c))` is a *coverage* function, hence
monotone submodular in the chosen `(i, s_i)` set. The centerpoint requirement
`μ(X_t∩K(c,s)) ≤ (1−α)μ` for ALL `2^d` signs `s` is then a submodular condition on the
worst direction.

**(3) Lemma/algorithm.** "`max_s μ(X_t∩K(c,s))` is computable / certifiable in poly time
(via SFM or the multilinear extension) given a volume oracle" — replacing the `2^d`
direction check by poly work. Doesn't remove the volume oracle but tightens the center
subroutine and may yield a *deterministic robust* balanced center.

**(4) Test/refute.** Verify submodularity numerically; compare the SFM-certified center to
the Fermat–Weber center. Modest but cheap.
» ADVISOR: (pending)

### Idea I [secondary] — Lattice/Tarski simultaneous over-under bracketing of `x*`
**(1) Connection.** Order theory / Tarski fixed-point lattice (repo already has Tarski
work) — monotonicity of the value operator.

**(2) Mechanism.** `T` monotone ⟹ iterates from `⊥` increase to `x*` and from `⊤`
decrease to `x*`, sandwiching it. The balanced cut is a `d`-dimensional generalized
median = lattice binary search. Ask whether combining the *interval* `[T^k⊥, T^k⊤]` with
the balanced-cut geometry collapses the bracket in `poly` (not `log^d`) steps by using
the contraction to certify which lattice octant contains `x*`.

**(3) Lemma/algorithm.** A Dang–Qi–Ye-style monotone binary search whose per-step branching
is guided by the ℓ∞-cut sign to avoid the `log^d` blow-up.

**(4) Test/refute.** Compare bracket width shrinkage of naive Tarski vs cut-guided on SSG.
Refuted if it collapses to the `log^d` bound (no gain over CLY/PFix).
» ADVISOR: (pending)

---

**Priority for testing (all cheap, reuse existing scripts/data):** D (sampling-bypass,
strongest), A (scale-free κ, isolates the asymmetric-repair Jacobian), B (discrete
expander reframing), C (ESD convergence from saved trajectories). E next (game-structure).

---

## BATCH 2

### Idea L [TOP] — Spectral independence / Lorentzian polynomials for the cell distribution on `[d]^t`
**(1) Connection.** The modern approximate-counting toolbox: spectral independence
(Anari–Liu–Oveis Gharan) and log-concave/Lorentzian polynomials
(Anari–Oveis Gharan–Vinzant, Brändén–Huh). This is the *replacement* for raw Cheeger
when Cheeger is hard: it proves poly mixing of local (Glauber / down-up) dynamics via
bounded pairwise influence, and often holds even at a bottleneck-free-but-not-expander
measure.

**(2) Mechanism.** Sampling `X_t` ≡ sampling `π ∈ [d]^t` with `μ(π) ∝ vol(P_π)` (§3.1),
then a poly convex-cell sample. Consider the natural **round-resample** dynamics: pick a
round `r`, resample its cell-index `π_r ∈ [d]` from `μ(· | π_{-r})` (a poly computation:
`d` cell-volume ratios, each an intersection of convex polytopes). Its mixing is governed
by the **influence matrix** `I_{r,r'}` = TV-influence of `π_r` on the marginal of `π_{r'}`.
If `λ_max(I) ≤ O(1)` (spectral independence), the resample walk mixes in `poly(d,t)`.
The influences should DECAY because cut `r` and cut `r'` are centered at Fermat–Weber
points of geometrically-separated, shrinking bodies — a *correlation-decay* structure the
adversarial version lacks.

**(3) Lemma/algorithm.** "The cell measure `μ` on `[d]^t` is spectrally independent with
constant `O(1)` (equivalently: its pairwise influences decay in `|r−r'|` / in the scale
ratio of the two cuts)." ⟹ poly-time sampler via the resample walk ⟹ SSG ∈ P. Even
better if `∑_π vol(P_π) ∏ z_{π_r,r}` is **Lorentzian** in the `z`'s — then the
basis-exchange/down-up walk mixes with no further work (AOV/ALOV).

**(4) Test/refute.** On small `(d,t)`: enumerate cells, estimate the `t×t` influence
matrix `I` (perturb one round's conditioning, measure marginal shifts of others),
compute `λ_max(I)` and its scaling in `d,t`; separately test approximate log-concavity of
the generating polynomial along random lines. **Refuted** if `λ_max(I)` grows with `t`
(long-range correlation ⟹ the dumbbell, again). Distinct from Idea B: L is the *local-dynamics*
/influence route, B is the *global-conductance* route; either suffices.
» ADVISOR: (pending)

### Idea Q [TOP] — Bounded star-cover number: `X_t = ⋃` of poly-many exactly-sampleable star pieces
**(1) Connection.** Combinatorial/computational geometry — the "art-gallery"/kernel-cover
number, extending the *already-solved* star-shaped exact-sampler regime.

**(2) Mechanism.** The exact ray-shooting sampler needs one nonempty kernel; the notes show
the single kernel collapses after `O(d)` rounds (star-shapedness lost). BUT a non-star body
can still be a union of a few star-shaped pieces, each with a nonempty (poly-LP-findable)
kernel and each *exactly* sampleable by ray-shooting. If `X_t` decomposes into
`g(d,t) = poly` star pieces with poly-time-computable volumes/overlaps, then
inclusion–exclusion (or volume-weighted piece selection) samples `X_t` exactly — **no
mixing at all**, even past the single-kernel collapse.

**(3) Lemma/algorithm.** "The star-cover number (min # of star-shaped pieces covering `X_t`)
of realizable bodies is `poly(d,t)`." Algorithm: greedily peel star pieces (each obtained by
choosing, per cut, which pyramid of the union `K(c^r,s^r)` to commit to — committing to a
single pyramid per cut makes the piece an intersection of CONVEX cones = convex ⊆ star!).
Indeed each cell `P_π` is convex, so trivially `X_t` is a union of `≤ (d²t)^d` convex
pieces — the point is to show a MUCH smaller cover by *fat* star pieces suffices, so the
inclusion–exclusion has poly terms.

**(4) Test/refute.** Greedily cover realizable `X_t` by nonempty-kernel sub-bodies (add
virtual constraints to restore a kernel); count pieces vs `d,t`. **Refuted** if the fat-cover
number grows exponentially. Directly extends the solved star regime and sidesteps
isoperimetry entirely if it holds.
» ADVISOR: (pending)

### Idea K — Method of interlacing polynomials (MSS/Kadison–Singer) to certify a good balanced cut
**(1) Connection.** Real-stable polynomials & interlacing families (Marcus–Spielman–
Srivastava), used to prove existence of well-conditioned partitions.

**(2) Mechanism.** The algorithm has freedom among near-balanced centers (and among tie-breaks).
View the characteristic polynomials `det(xI − Σ(X∩K(c,s)))` over that admissible family as an
*interlacing family*; the MSS root-barrier bound then certifies **existence** of an admissible
cut with `λ_min ≥ 1/poly` (bounded κ), even though we can't choose the oracle's sign `s`.

**(3) Lemma/algorithm.** "Over admissible centers, the mixed characteristic polynomial's
smallest root is `≥ 1/poly` ⟹ a poly-κ cut exists and is found by the MSS interlacing walk."
Turns the *existence* of a well-conditioned cut into a real-rootedness computation.

**(4) Test/refute.** Check whether, over a small admissible-center family, some cut keeps κ
bounded (it should, per empirics) and whether the char-polys interlace (necessary for the
method). **Refuted** if no admissible cut is well-conditioned, or interlacing fails.
Caveat the advisor should weigh: the oracle fixes `s`, so the "admissible family" must come
from center freedom / ties alone — is it rich enough?
» ADVISOR: (pending)

### Idea N — Smoothed analysis of the SSG P-matrix LCP (undiscounted)
**(1) Connection.** Smoothed analysis (Spielman–Teng) + LCP/interior-point theory. SSG value
solves a P-matrix LCP; the *undiscounted* (`γ=1`) LCP avoids the `1/(1−λ)` blowup that makes
weak-polynomiality worthless here.

**(2) Mechanism.** (i) Perturb payoffs by random `±2^{-poly}`; the LCP becomes well-conditioned
w.h.p. (smoothed condition number poly). (ii) Solve by IPM/Lemke in poly ops at the smoothed
condition number. (iii) Round to the EXACT value: SSG values are rationals with denominators
bounded by subdeterminants `≤ 2^{poly}`, so a `2^{-poly}`-accurate solution rounds via
continued fractions to the exact rational.

**(3) Lemma/algorithm.** "The SSG LCP has poly smoothed condition number, and a
`2^{-poly}`-accurate solve suffices to recover the exact value." ⟹ poly-time *randomized*
exact SSG. The crux/caveat: is the number of IPM iterations at the smoothed condition number
`poly(n)` and NOT `poly(bits)=poly` only weakly? The undiscounted framing is what could make
it strongly poly.

**(4) Test/refute.** Empirically measure the LCP condition number of random-perturbed SSG
instances vs `n`; check it's poly. **Refuted** if perturbation doesn't tame the condition
number (persistent near-degeneracy).
» ADVISOR: (pending)

### Idea M — Tropical (max-plus) spectral bracket via Collatz–Wielandt
**(1) Connection.** Tropical / max-plus spectral theory & nonlinear Perron–Frobenius
(Gaubert–Gunawardena, Akian–Bapat–Gaubert). The value operator is a min-max-plus map.

**(2) Mechanism.** For the *deterministic* skeleton (mean-payoff relaxation) the value is a
tropical eigenvalue, computable in poly time (MPG value via Karp/energy games). Use the
tropical eigenvalue as a poly-computable **bracket**: `x*_trop-lower ≤ x* ≤ x*_trop-upper`,
and the stochastic (AVG) states as a controlled perturbation refined by poly rounds of the
contraction. Collatz–Wielandt gives `x*` as an extremal ratio, yielding certified bounds
without sampling.

**(3) Lemma/algorithm.** "The tropical bracket has width `≤ diam·γ^{poly}`... " — actually the
useful target: the tropical relaxation identifies the optimal policy on a `1/poly` fraction of
states per round, shrinking the effective game (dovetails with Idea D's policy identification).

**(4) Test/refute.** Compute the tropical (mean-payoff) bracket on SSG instances; measure how
many states it pins vs `n`. **Refuted** if the bracket is vacuous (width ≈ diam) on stochastic
instances.
» ADVISOR: (pending)

### Idea O — Persistent homology of the offset filtration detects thin necks
**(1) Connection.** Topological data analysis / persistent homology.

**(2) Mechanism.** A dumbbell neck is a topological feature: in the erosion/offset filtration
of `X_t` (sublevel sets of `−dist(·, ∂X_t)`), a thin neck of width `w` appears as an `H_0`
merge that persists until scale `w/2`, then the body splits. So the smallest `1/poly`-relevant
persistence bar lower-bounds the neck width, hence controls Cheeger. Realizable bodies (no
slivers, ball-preservation) should have all neck-persistence `≥ 1/poly`.

**(3) Lemma/algorithm.** "Min neck-persistence of realizable `X_t` is `≥ 1/poly` ⟹
`h(X_t) ≥ 1/poly`." A geometric-topological restatement of the isoperimetry, but with a
*computable diagnostic* (persistence) and a possible route via the ball-preservation lemma
bounding erosion depth.

**(4) Test/refute.** Compute persistence of `−dist`-filtration on sampled realizable `X_t`;
correlate min-persistence with measured Cheeger/κ. **Refuted** if healthy-volume bodies show
short neck-persistence (would be a realizable bottleneck — the whole problem).
» ADVISOR: (pending)

---

**Batch-2 priority:** L (spectral independence — the current best tool for "sample when
Cheeger is hard", directly on `[d]^t`) and Q (bounded star-cover — extends the SOLVED exact
sampler, may bypass isoperimetry). Then K (existence of a good cut) and N (smoothed LCP,
a genuine sampling-free route). M and O are diagnostics/brackets.

---

## Self-triage of Batches 1–2 vs the advisor's 5 standing obstructions

Honest pre-screen (obstructions: 1=hard-regime `1−λ=2^{−poly}`; 2=`conv X_t=ℝ^d` kills
convex-outer methods unless narrowed to ≤2 coords; 3=reduction to Tarski/MPG/parity/SG is
NOT progress; 4=KLS/localization is convex-only; 5=the anisotropic/dumbbell wall = SSG).

- **DEAD by advisor criteria:** E (obstr. 1+3: `γ→1` path = USO path, open & ≡SSG),
  N (obstr. 1+3: weakly-poly IPM, LCP≡SSG), M (obstr. 3: mean-payoff≡SSG — only the
  "pin policy on some states" dovetail with D survives), I (obstr. 3: Tarski open & ≡).
  H (doesn't remove the volume oracle), G (drift, self-refuted).
- **WALL-EQUIVALENT reframings (honest — they don't cross the wall, they relocate it to a
  possibly-more-tractable object):** B (small conductance = dumbbell), C (bottom-edge drift
  = thin axis), F (curvature→0 = neck), O (short neck-persistence = neck), L (large influence
  = long-range correlation = dumbbell). VALUE: each imports a *tool* the raw problem lacks —
  L's spectral-independence machinery and B's Hamming-comparison are the two I'd still bet on.
- **SURVIVE as genuine attacks on the open leads:** A (scale-free κ via local stability —
  lead b), Q (bounded star-cover — sidesteps isoperimetry, doesn't smuggle convexity, extends
  the SOLVED regime), D (partial sampling-bypass; caveat: chicken-and-egg, needs sampler to
  place the center — I downgrade it accordingly), K (existence of a good cut; caveat below).

Confronting obstruction 2/4 head-on: Q and the cell-decomposition (B, L) are the only ideas
that face the non-convexity WITHOUT smuggling KLS — Q by cutting `X_t` into star/convex pieces,
B/L by using the `[d]^t` cell structure. Everything convex-outer is conceded dead.

---

## BATCH 3 — aimed directly at the advisor's three open leads (a), (b), (c)

### Idea R [TOP — lead (b), scale-free κ] — Order-statistics / extreme-value mechanism: Δ aligns with high-variance directions because the cut depends only on the EXTREME coordinates
**(1) Connection.** Extreme value theory / order statistics + a Chatterjee–Stein covariance
identity. This is aimed at the exact open target "Δ aligns with the TOP eigenvector, never the
bottom."

**(2) Mechanism.** Center at the balanced point, sign-fold (orthogonal, preserves the
covariance eigenbasis) so `K = {y : max_i y_i + min_i y_i ≥ 0}`. Balancedness ⟹ `P(K)=½`, and
with mean ≈ 0, `Δ = m_K − m_R = 4·E[y·1_K]`. Hence for each eigenpair `(λ_k,u_k)`:

```
⟨Δ, u_k⟩ = 4·Cov(u_k·y, 1_K),     1_K = 1{M(y) ≥ 0},  M(y) = max_i y_i + min_i y_i.
```

The cut indicator depends ONLY on the top and bottom **order statistics** of `y`. A
low-variance eigendirection `u_d` moves `y` little and — crucially — a coordinate with small
variance is almost **never the argmax or argmin**, so `u_d·y` is nearly **independent** of the
event `{M≥0}`. Therefore `Cov(u_d·y, 1_K) ≈ 0` ⟹ `Δ ⊥ u_d` ⟹ the rank-1 downdate `½ΔΔᵀ`
barely touches the thin axis, while it DOES shave the top axis (which dominates the extremes) —
exactly `λ_max` and `λ_min` shrink together ⟹ scale-free κ preserved. `∇M = e_{argmax}+e_{argmin}`
gives the coarea/boundary form: `Cov(u_k·y,1_K)` is a surface integral over `{M=0}` weighted by
`u_k·(e_{argmax}+e_{argmin})`, which is small precisely when `u_k` avoids the frequently-extreme
(= high-variance) coordinates.

**(3) Lemma/algorithm (the concrete target).** `⟨Δ,u_k⟩² ≤ C·(λ_k/λ_1)·‖Δ‖²` for all `k`
(alignment monotone in variance). Consequences: (i) thin axis `⟨Δ,u_d⟩² ≤ C(λ_d/λ_1)‖Δ‖² =
O(λ_d)` since `‖Δ‖²=O(λ_1)` (mean-shift ≤ top std, mean-shift lemma), so `λ_min` shaved by ≤
a constant fraction; (ii) top axis absorbs `Θ(‖Δ‖²)=Θ(λ_1)`, so `λ_max` shrinks in step ⟹
`κ(X∩K) ≤ (1+o(1))κ(X)`. This is EXACTLY lead (b), and the EVT independence is the missing
proof of "never the bottom." The needed EVT input: `P(coord i ∈ {argmax,argmin}) ` and
`E[|y_i|; i extreme]` scale with coordinate `i`'s range/variance — standard order-statistic
estimates for the coordinates of a body with covariance eigenvalues `λ_k`.

**(4) Test/refute.** From existing exact-rejection trajectories, directly measure the
alignment curve `⟨Δ,u_k⟩²/‖Δ‖²` vs `λ_k/λ_1` across all cuts; fit the claimed `∝ λ_k/λ_1`.
Separately measure `Cov(u_d·y,1_K)` and `P(argmax/argmin = low-variance coordinate)`.
**Refuted** if `⟨Δ,u_d⟩²` is `Ω(‖Δ‖²)` on realizable cuts (Δ hits the thin axis) — which
repair_attack's T2 hints is *intermittent*, so the honest question is whether the intermittent
mis-alignment is bounded by `O(λ_d/λ_1)` on AVERAGE (it need only hold in expectation over
the trajectory, not every cut). This is the sharpest, most-checkable form of lead (b) I can
produce, and it comes with a named theorem-machine (EVT + Chatterjee's covariance bound).
» ADVISOR: (pending)

### Idea S [lead (c)] — Spherical isoperimetry of `R(u)^d` via Lipschitz-of-`log R` + Lévy concentration; the 2nd-moment→sup gap is the crux
**(1) Connection.** Concentration of measure on the sphere (Lévy's lemma) + Poincaré/
spectral gap of the sphere under a density.

**(2) Mechanism.** In the star regime `μ` = (pick `u ∝ R(u)^d du` on `S^{d−1}`) × (radius). The
angular measure `ν(du) ∝ R(u)^d du` is the only residual bottleneck (radial needles are single
intervals — solved). `R(u) = min_r ρ_r(u)`, a min of piecewise-linear radial functions; in the
star regime the ray never re-enters, so `R` is single-valued and `ρ`-bounded above (diam) and
below (ball-preservation: `R ≥ r/2`). If `log R` is Lipschitz on the sphere with constant `L`,
then by Lévy, `R^d du` concentrates in a band of angular width `O(1/(L√d))` around the median —
UNLESS `L` is large. So the angular Cheeger of `ν` is `≥ 1/poly` ⟺ `L(log R) ≤ poly/√d`... but
the `R^d` weight amplifies oscillation by `d`, so the true requirement is `osc(log R) = O(1/d)`
in any small cap — i.e., `R` is nearly constant locally, which is the "no spike" condition.

**(3) Lemma/algorithm (the concrete target + where it bites).** "Bounded κ ⟹ `R(u)` has
angular oscillation `≤ f(κ)` controlled well enough that `ν ∝ R^d` has spectral gap `1/poly`."
The crux is a **2nd-moment→sup upgrade**: κ controls the *second moment* of the direction
(global aspect ratio), while a spike is a *sup* phenomenon (a rare direction with huge `R`).
The bridge is a reverse-Hölder / hypercontractivity-type inequality for `R` on the sphere. If
`R` were log-concave-ish this is automatic; it is not, so the honest sub-question is: does the
piecewise-linear `min_r ρ_r` structure forbid a single-direction spike while the bulk stays
isotropic (bounded κ)? A spike of angular width `θ` needs `κ ≳ θ^{−2}` (notes §5), so
**bounded κ already caps the spike width from below** — the remaining gap is only whether
`poly`-many spikes of `poly`-bounded aspect can still make `ν` disconnected, a *counting* of
spikes rather than their existence.

**(4) Test/refute.** On star-regime realizable bodies (exact ray-shooting is available):
sample `u`, compute `R(u)`, measure `osc(log R)` in caps and the spherical Cheeger of `R^d du`
vs κ. **Refuted** if a bounded-κ star body exhibits an angular bottleneck of `ν` (a genuine
two-lobe direction set) — that would be a realizable star-regime dumbbell.
» ADVISOR: (pending)

### Idea T [lead (a)] — Local-Jacobian + sparse recovery to narrow the pyramid union to 2 coords — with its honest refutation and a salvage
**(1) Connection.** Compressed sensing / sparse recovery, applied to the "which coordinates
dominate `x*−c`" question that Corollary C needs.

**(2) Mechanism.** `poly(d)` finite-difference queries `f(c+εe_k)−f(c)` reveal the LOCAL linear
piece `A` of the PL map near `c`; the local Newton direction `(I−A)^{−1}v` estimates `x*−c`
better than the single displacement `v=f(c)−c`. Narrowing the union to 2 coords = certifying
`x*−c` has its ℓ∞-mass in 2 coordinates (2-sparse-dominant). Sparse recovery (ℓ1/LASSO) from
the `poly(d)` local measurements would identify the top-2 support if `x*−c` is compressible.

**(3) Would-yield.** If the top-2 support is identifiable with `poly(d)` queries at a `1/poly`
fraction of rounds, then at those rounds the cut is a halfspace (|S|≤2), `X_t` is locally
convex, and cutting-plane machinery applies (Corollary C) — a restart-based poly algorithm.

**(4) Honest refutation + salvage.** The naive version DIES on the hard regime: the notes show
the difficulty is exactly when `x*−c` is *spread* (anisotropic), which is precisely *not*
2-sparse — so compressed sensing has no sparsity to exploit exactly when it's needed, AND in
the hard regime `1−λ=2^{−poly}` the dominant-coordinate signal `(1−λ)r` is swamped
(obstruction 1). **Salvage (the real question worth testing):** is the gap vector `x*−c` FLAT
(active-set size `O(1)`) at a `1/poly` fraction of the trajectory's rounds? If yes, those
rounds give free convex cuts. This is a cheap empirical question: track `|A(c^r)| = #{i :
|x*_i−c^r_i| ≥ ½ max}` along real runs. If `|A|` is usually `O(1)`, Corollary C is within reach;
if `|A|=Θ(d)` throughout (spread), (a) is wall-equivalent. I lean toward the latter but the
measurement is decisive and unmade.
» ADVISOR: (pending)

### Idea U [lead (b), the tool to EXECUTE Idea R] — Chatterjee's second-order Poincaré / Stein for the covariance `Cov(u_k·y, 1_K)`
**(1) Connection.** Stein's method / second-order Poincaré inequalities (Chatterjee, Nourdin–
Peccati) — the machinery that turns "the cut depends only on extremes" into a quantitative bound.

**(2) Mechanism.** `Cov(u_k·y, 1_K)` with `1_K=1{M≥0}`, `M=max+min`, is a covariance between a
linear statistic and a functional of order statistics. Stein/Poincaré bounds it by
`E[⟨∇(u_k·y), ∇M⟩ · (smoothing)] = E[(u_k·(e_{argmax}+e_{argmin}))·(density on {M=0})]`. Since
`u_k·e_i = u_{k,i}` and argmax/argmin concentrate on high-variance coordinates, this is
`O(√(λ_k/λ_1))·‖Δ‖` — the exact input Idea R needs.

**(3) Lemma.** The quantitative `⟨Δ,u_k⟩² ≤ C(λ_k/λ_1)‖Δ‖²` of R, delivered by a second-order
Poincaré bound on the sign-folded body (which, though non-convex, has a bounded-support density
where Stein-type bounds still apply — this SIDESTEPS the convex-only obstruction 4 because
Stein/Poincaré for bounded densities is not KLS).

**(4) Test/refute.** Numerically verify the Stein bound's RHS tracks the LHS `⟨Δ,u_k⟩²` across
cuts. Refuted if the second-order Poincaré constant of these bodies is not `poly`.
» ADVISOR: (pending)

**Batch-3 priority:** R (the centerpiece — a concrete, named-machine attack on lead (b) with a
cheap decisive test on SAVED data) and its executor U; then S (lead (c), reduces to a spike-
COUNTING question given κ bounds spike WIDTH); T (lead (a)) I present mostly to KILL the naive
version and extract the one cheap measurement (`active-set flatness`) that decides whether (a)
is reachable.

> **UPDATE (integrating `notes/crux_scalefree.md`, a teammate result):** the clean per-cut form
> of Idea R ("Δ aligns with the top eigenvector, never the bottom") is **refuted by mechanism**
> (crux_scalefree §4): the cut senses `v` only through `ρ(v)=Cov(ŝ,σ)`, and an *anti-diagonal*
> `v_max` (max vᵢ ≈ −min vᵢ) is **blind** (`ρ≈0`), so Δ is orthogonal to it — the opposite of
> alignment, and realizable. What survives and is now the RIGHT target: their exact identity
> `c(v)=vᵀΣ(K')v/vᵀΣ(X)v = 1 + a(v) − ρ(v)²` with `a(v)=E[s²σ]` (ASYM), and `ΔᵀΣ⁻¹Δ≤4`
> (downdate alone can't collapse the thin axis). The wall reduces to: **bound `a(v_min)`**, or
> **prove non-persistence of the "`v_max` blind ∧ `v_min` sensed" orientation**. My EVT/Stein
> machinery (R/U) is redirected to those residuals below (Batch 4). Their §3 `Δ=2Cov(w,σ) ⟂
> blind cone` is exactly the boundary/coarea form I proposed in R — so R's *mechanism* is
> confirmed; only its clean-theorem packaging was wrong.

---

## BATCH 4 — aimed at the SHARPENED residuals of `crux_scalefree.md` (§5–6)

### Idea V [TOP — the SSG lever of crux_scalefree §5] — Perron–Frobenius forces the long axis into the SENSED cone, excluding the bad orientation
**(1) Connection.** Perron–Frobenius / nonnegative-matrix theory, coupled to the monotone
value operator — a direct attack on "show the operator keeps the long axis in the sensed
(coordinate/near-diagonal) subspace, not the anti-diagonal blind cone" (crux_scalefree §5, §6).

**(2) Mechanism.** The SSG value operator is monotone ⟹ its local linear pieces are
`x ↦ γP_σ x + r` with `P_σ ≥ 0` row-substochastic (nonnegative Jacobian). Key sign fact:
a **nonnegative** direction `v ≥ 0` is SENSED — along `w=av`, `max w = a·max v > 0` and
`min w = a·min v ≥ 0`, so `g(av)=a(max v+min v)` has `sign = sgn(a)` ⟹ `ρ(v)` large. The
*blind* cone is the **anti-diagonal** (strongly sign-mixed) directions, which are FAR from the
nonnegative orthant. Perron–Frobenius: the leading eigenvector of a nonnegative matrix is
nonnegative. Conjecture: the coordinate-structured gaps SSG produces (values pinned `0/1` at
sinks, monotone PL propagation) bias the **top eigenvector of `Σ(X_t)` toward the nonnegative/
comonotone cone**, hence SENSED, hence shaved every round (`ρ(v_max)²` large ⟹ `c(v_max)<1`).
That **excludes the "`v_max` blind" bad orientation** and gives mean-reversion directly.

**(3) Lemma/algorithm.** "For realizable SSG bodies, `ρ(u_max(Σ(X_t))) ≥ 1/poly` (the long
axis is sensed)." Then `c(v_max)=1+a−ρ² < 1` shaves `λ_max` while Cor. 2′ bounds the `v_min`
downdate ⟹ `κ(X∩K) ≤ (1+o(1))κ(X)` — closes the scale-free crux for SSG. The PF structure is
the *reason* the sensed-long-axis event should hold, which crux_scalefree §5 flagged as the
"most promising unexplored SSG-specific lever" but left unmotivated.

**(4) Test/refute.** This SHARPENS the experiment crux_scalefree §6 already sent to `main`. In
addition to `ρ(v_max)`, log the **overlap of `u_max` with the nonnegative orthant** — e.g.
`‖u_max^+‖/‖u_max‖`, the angle to `𝟙/√d`, and a sign-mixedness score `|max u_i + min u_i|` —
across the trajectory. **Prediction (distinguishes the PF mechanism):** high-κ rounds have
`u_max` near the nonnegative/diagonal cone (sensed) and a κ-drop next round. **Refuted** if
healthy realizable `u_max` is frequently anti-diagonal/blind — that is exactly the persistent
bad orientation and the counterexample shape to hunt.
» ADVISOR: (pending)

### Idea W [the non-persistence residual of crux_scalefree §6] — Furstenberg/Oseledets: the top-eigendirection equidistributes, so it can't stay blind
**(1) Connection.** Multiplicative ergodic theorem / products of random matrices (Furstenberg
positivity, Oseledets) + Markov chains on projective space.

**(2) Mechanism.** Over rounds `Σ_t` evolves by the structured update `(D)`; the top-eigen
DIRECTION `u_max^{(t)} ∈ P^{d−1}` evolves like the leading Oseledets direction of a product of
FW-recentered cut-operators. Each round the Fermat–Weber recentering re-randomizes which
`(argmax,argmin)` coordinate cells are active, hence rotates the frame. If the induced chain on
`P^{d−1}` has a **spectral gap** (Furstenberg-type: the operator semigroup is strongly
irreducible + contracting ⟹ unique stationary measure with a gap), then
`P(u_max blind for k consecutive rounds) ≤ (1−β)^k`, `β = ` (stationary mass of the sensed
cone) `= Ω(1)`. So the bad orientation is **non-persistent** ⟹ amortized `κ` bounded.

**(3) Lemma/algorithm.** "The top-eigendirection chain has a spectral gap and stationary
measure with `Ω(1)` mass on the sensed cone" ⟹ `E[log κ(X_t)] = O(1)` over the trajectory —
precisely the non-persistence crux_scalefree §6 requires. Pairs with V: PF says the stationary
measure FAVORS the sensed cone; Furstenberg says the chain MIXES to it fast.

**(4) Test/refute.** Measure the round-to-round rotation angle `∠(u_max^{(t)}, u_max^{(t+1)})`
and the autocorrelation time of `ρ(u_max^{(t)})`. **Non-persistence holds** if `ρ(u_max)`
decorrelates in `O(1)` rounds. **Refuted / danger** if `u_max` is nearly *stationary* inside
the blind cone (a frozen bad orientation that compounds).
» ADVISOR: (pending)

### Idea X [bound the ASYM scalar `a(v_min)` — the sole crux of crux_scalefree §2] — skewness/parity control of `E[s²σ]`
**(1) Connection.** Third-moment / skewness analysis + Gaussian comparison (Stein again).

**(2) Mechanism.** `a(v_min)=E[s²σ]`: correlation between *being far out along the thin axis*
(`s²`, even) and *being on the removed side* (`σ`). By parity, if the thin-axis marginal is
symmetric and the thin axis is blind, `a≈0` (safe, `c≈1`). Danger (`a<0`, `c<1`) needs both
(i) thin axis SENSED and (ii) a `s²`–`σ` coupling = a *skew/asymmetry* of the sensed thin
marginal. So `|a(v_min)|` is bounded by the **skewness of the thin-axis marginal along the
sensed component**. Ball-preservation ⟹ coordinate marginals have a central mass band (not
skewed dumbbells), controlling `a` for coordinate-aligned thin axes; the residual is a
diagonal skew.

**(3) Lemma.** `a(v_min) ≥ −ε`, `ε = O(`skewness of the sensed thin-axis marginal`)`, bounded
via ball-preservation for the coordinate/near-diagonal (sensed) part. Combined with Cor. 2′
(`c(v_min)=1+a−ρ²`, and `ρ(v_min)` small unless the thin axis is sensed) this would give
`c(v_min) ≥ 1−ε−o(1)`, i.e. the thin axis is never collapsed by more than a `(1+o(1))` factor
even when sensed — the missing lower bound.

**(4) Test/refute.** Directly measure `a(v_min)` and its sign (already in `repair_measure.py`
T2/T3), and correlate with the thin-axis marginal skewness and the sensed/blind classification.
**Refuted** if large-negative `a(v_min)` occurs with a *symmetric* thin marginal (skewness
wouldn't explain it) — then the parity control fails and the crux is elsewhere.
» ADVISOR: (pending)

**Batch-4 priority:** V (the Perron–Frobenius reason the long axis should be sensed — closes the
SSG lever, sharpens main's already-queued §6 experiment with a distinguishing prediction), then
W (Furstenberg non-persistence — the amortized closure) and X (bound the ASYM scalar directly).
All three are cheap and measurable on the SAME exact-rejection harness crux_scalefree §6 uses.

---

## D-escape analysis (why the FW-center pivot should dodge Friedmann/Fearnley) + the decisive test

The advisor escalated D but flagged the killer risk: does "rounds-to-stabilize" collapse to a
strategy-improvement pivot count, for which Friedmann 2009 / Fearnley 2010 give EXPONENTIAL
lower bounds at `γ→1`? My analysis — the FW method is **not** a pivot rule, and the test really
probes something else:

**1. The FW outer loop is value-space BISECTION, oblivious to strategy space.** Each round:
`X_t ∋ x*`, cut at the balanced center `c^t`, `vol(X_t)=2^{−t}vol(box)` — a deterministic
volume halving. The sign `s^t` is a *byproduct* of the cut, not a strategy chosen by a local
improvement rule that determines the next iterate. Friedmann/Fearnley lower-bound the number of
distinct **strategies** a pivot rule visits by structuring the improvement DAG; volume halving
does not traverse that DAG. Rounds-to-localize `x*` to its optimality-cell inradius
`ρ* ≥ 2^{−poly}` (grid-rational margin) is `O(d·log(1/ρ*)) = poly`, **independent of the game's
strategy structure.** So the exponential-pivot adversary has no direct handle on the FW round
count.

**2. Therefore the Friedmann/Fearnley test actually probes whether the adversarial game induces
a hard-to-SAMPLE (dumbbell) `X_t`, not a long pivot sequence.** Two outcomes, both informative:
 - rounds POLY ⟹ the exponential strategy-improvement structure does NOT translate into slow
   value-bisection ⟹ strong evidence D's outer loop escapes the pivot lower bounds; the wall is
   then *entirely* the per-round sampler (studied separately).
 - rounds EXPONENTIAL ⟹ either the induced `X_t` is a genuine dumbbell (the sampling wall
   reappears — and now we have an *adversarial realizable* instance to dissect, valuable in
   itself) or the diameter fails to shrink even with a good center.

**3. Clean isolation (the decisive experiment).** To separate "does value-bisection escape the
pivot bound" from "can we sample," run FW-center with **exact-rejection** centers (feasible on
small instances) on a Howard-exponential instance, and count rounds-to-stabilize. This removes
the sampler confound entirely.

**4. Recommend Fearnley's MDP (1-player) as the FAST FILTER before Friedmann's 2-player SSG.**
Fearnley 2010 (arXiv:1003.3418) is a binary-counter **MDP** on which Howard's policy iteration
takes `2^{Ω(n)}` steps, yet (a) the value is exactly LP-computable ⟹ the certificate and margin
are verifiable, (b) the value operator is still monotone PL / topical ⟹ the FW machinery applies
verbatim, (c) 1-player ⟹ simplest to encode & sample. Run it at `γ→1` (where HMZ's poly bound
fails). NOTE: MDPs are in P (LP), so a poly FW result here proves only that FW is *not fooled by
Howard-hard instances* — necessary, not sufficient. If FW is EXPONENTIAL even here, D dies
immediately (cheap kill). If poly, escalate to Friedmann's 2-player family (ssg-directions is
encoding it). Fearnley's is the right first filter; Friedmann's is the real test.
[Retrieval note: I could not parse the PDFs/HTML for the exact gadget wiring — ssg-directions
already has the encoding task; the above is the strategic framing + which family to run first.]

---

## BATCH 5 (routed via main) — the two UNUSED hooks: monotonicity & reflection; all bypass-shaped

### Idea M1 [TOP — monotonicity ⇒ CONVEX orthant cuts, directly attacking obstruction 2]
**(1) Connection.** Order theory / monotone operators + sub-/super-solutions — the value
operator's monotonicity, flagged as completely unused.

**(2) Mechanism.** For a monotone map `T` with unique fixed point `x*`: if `T(c) ≥ c`
(coordinatewise — `c` is a **subsolution**) then iterating `c ≤ T(c) ≤ T²(c) ≤ … → x*`, so
`x* ≥ c`; dually `T(c) ≤ c` (supersolution) ⟹ `x* ≤ c`. Each is an **axis-aligned orthant
constraint = CONVEX**. Comparing `f(c^t)` to `c^t` is exactly the one oracle query we already
make. So **on every round where the Bellman residual `f(c^t)−c^t` is all-one-sign, we get a
free CONVEX cut** `x* ⪰ c^t` (or `⪯`), no pyramid non-convexity at all. The non-convex pyramid
cut is forced ONLY on mixed-sign rounds. This is the first genuine lever on the advisor's
obstruction 2 ("narrow to a convex regime"): monotonicity supplies convex cuts for free whenever
the residual is signed-consistent.

**(3) Lemma/algorithm.** Maintain a convex **order-interval** `[L_t, U_t] ∋ x*`: every
subsolution `c` updates `L_{t+1} = L_t ∨ c`, every supersolution updates `U_{t+1} = U_t ∧ c`
(coordinatewise max/min). Intersect the (convex) order-interval with `X_t` for free. If
`width(U_t − L_t)` shrinks geometrically, cutting-plane machinery on the CONVEX order-interval
finishes — **bypassing the non-convex sampler entirely.** Even a *partial* result — "a `1/poly`
fraction of rounds are signed-consistent" — gives that fraction of cuts for free as convex.

**(4) Test/refute.** On SSG/topical instances (and on Fearnley's MDP), log per round: is
`f(c^t)−c^t` all-one-sign? track `width(U_t−L_t)` and whether it shrinks geometrically.
**Refuted / weak** if residuals are essentially always mixed-sign (then monotone orthant cuts
never fire and the order-interval stalls). Decisive and cheap — reuses the existing algo loop.
» ADVISOR: (pending)

### Idea M3 [monotonicity ROBUSTIFIES D — the sampler need not mix, only order-place the center]
**(1) Connection.** Monotonicity again, aimed at D's chicken-and-egg (D needs a good center,
which needs sampling).

**(2) Mechanism.** The Bellman-residual sign is a **monotone** function of the center. So the
cut sign `s^t` is correct (matches `x*`'s pyramid) whenever the center lies in the correct
order-cell relative to `[L_t, U_t]` — NOT only at the exact Fermat–Weber point. An approximate/
heuristic center (analytic center, a few hit-and-run steps, even the previous query point) that
lands in the right order-cell yields the correct sign and certificate. So **D tolerates a
sampler that does not provably mix**; it needs only order-correct center placement, which the
shrinking convex `[L_t,U_t]` (Idea M1) helps guarantee.

**(3) Lemma/algorithm.** "If `c^t ∈ [L_t, U_t]` and the residual is signed-consistent, the sign
is `x*`-correct regardless of sampler quality." ⟹ D's per-round requirement drops from "mix on
a non-convex body" to "place a point in a convex order-interval" — a categorical weakening of
the wall, and the concrete reason D may sidestep the sampling obstruction the other routes hit.

**(4) Test/refute.** Measure sign-correctness (vs the known `x*`) as a function of center
accuracy / sampler budget. **Refuted** if correct signs require near-exact FW centers (then M3
gives no robustness). Cheap; directly tests whether D's bypass survives a weak sampler.
» ADVISOR: (pending)

### Idea M2 [reflection ⇒ antithetic center estimation + a reflection-coupled bracket]
**(1) Connection.** Variance reduction / antithetic coupling, using "removed = point-reflection
of kept through `c`."

**(2) Mechanism.** Balancedness `μ(P_i^+(c)) = μ(P_i^-(c))` is a reflection-symmetry condition;
estimate it with **antithetic pairs** `(y, 2c−y)`, whose pyramid memberships are perfectly
anti-correlated ⟹ half the sample variance to locate the balanced center. Separately, the
reflection through `c^t` maps (approximate) subsolutions to supersolutions, giving a symmetric
two-sided order-bracket around `c^t` for free (feeds M1's `[L_t,U_t]`).

**(3) Lemma/algorithm.** Antithetic Fermat–Weber estimation halves the center-subroutine sample
complexity; the reflection provides a matched super-/sub-solution pair per round.

**(4) Test/refute.** Compare antithetic vs i.i.d. sample counts to reach a fixed center accuracy.
Modest but concrete; refuted only if antithetic correlation is weak (it is exact by construction,
so this mainly quantifies the gain).
» ADVISOR: (pending)

**Batch-5 priority:** M1 is the one to run first — it's a cheap, decisive measurement (fraction
of signed-consistent rounds + order-interval width) that could hand back CONVEX cuts, the single
thing every dead convex-outer idea needed, and it uses the monotonicity hook the whole project
left on the table. M3 then tells us whether M1+monotonicity robustify D against a non-mixing
sampler (the crux of D's viability). Both piggyback on the existing `algo_topical.py` loop.

---

## REFINEMENTS (responding to advisor's Batch-2 verdicts: L & Q escalated, the make-or-break asks)

### L-refinement [the make-or-break]: target BOUNDED OPERATOR NORM `λ_max(I)`, not entrywise decay
The advisor's objection is correct and I withdraw "influences decay from apex separation" (cells
are global/nested — separation ≠ decay). But spectral independence needs `λ_max(I) = O(1)`, which
does **NOT** require entrywise decay: a `t×t` influence matrix with all entries `O(1/t)` still has
`λ_max = O(1)`. So the right target is the **operator norm / row sums**, and there is a real
mechanism for bounding them:

**(i) Balancedness bounds the per-round total influence (row sums).** Each cut is balanced —
`μ(π_r = i)` is a bounded distribution over `[d]` (no coordinate wins with probability `→1`; the
cut removes exactly half). Conditioning on `π_r`'s outcome injects at most `log d` bits and
reshapes the measure by a bounded total-variation budget. Concretely the row sum
`Σ_{r'} I_{r,r'}` is the total sensitivity of the whole measure to fixing cut `r`'s winner; if
this is `O(1)` per round (a balancedness/entropy accounting), then by Gershgorin
`λ_max(I) ≤ max_r Σ_{r'} I_{r,r'} = O(1)` — spectral independence, **even if `I` is dense.**

**(ii) The conditional law of `π_r` given `π_{-r}` is an "argmax within a CONVEX cell."** Fixing
`π_{-r}` restricts to the convex polytope `P_{π_{-r}}`; `π_r` is then the ℓ∞-argmax coordinate at
`c^r` over that convex body — a log-concave-marginal object with bounded sensitivity to a single
extra halfspace. This is where the cells being individually convex (advisor's own point) pays off:
influence = sensitivity of a convex-body argmax to one constraint, classically bounded.

**Revised test (for main):** don't test entrywise decay — estimate the full `I` and report
**`λ_max(I)` and its scaling in `t`** (flat in `t` ⟹ spectral independence holds), plus the
**max row sum**. Refuted only if `λ_max(I)` grows with `t`. (I keep the advisor's trim: DROP the
Lorentzian sub-claim — arrangement-cell volumes are not known log-concave.)

### Q-refinement [why star-cover might stay poly; the shape to hunt; and how to FIND the cover]
Advisor confirmed Karp–Luby dissolves inclusion–exclusion (union sampling is `poly(k)`), so the
sole crux is `k(X_t) = poly`. Three concrete additions:

**(i) A candidate poly bound.** `X_t = ⋂_r K(c^r,s^r)`, each `K` a union of `≤ d` convex cones
star-shaped about the single apex `c^r`. Non-convexity (reflex features / distinct "lobes") is
created only at pyramid-union boundaries; **each cut adds `≤ d` new potential lobes.** If lobes do
not repeatedly SPLIT, `k(X_t) ≤ d·t = poly`. The failure mode to hunt is exactly **lobe
proliferation** (a cut splitting many existing lobes at once), the art-gallery blowup.

**(ii) Why the dumbbell is Q-EASY (the orthogonal-obstruction point, sharpened).** A Cheeger
bottleneck (2 fat lobes + thin neck) has star-cover `k ≈ 2–3` (one witness per lobe sees its
lobe). So Q's death is NOT the dumbbell — it's a body with `exp`-many small pockets, a completely
different failure shape. This is why Q can attack the regime `h`/`κ` cannot: **the two routes fail
on disjoint instances**, so a poly bound on *both* `min(k, 1/h)`-type quantities would cover
everything. Worth stating as a dichotomy to test: is every realizable `X_t` EITHER low-`k` OR
high-`h`?

**(iii) Finding the cover is submodular (Idea H resurrected).** "Volume visible from a witness
set `W`" is a monotone **submodular** coverage function of `W`; greedy witness selection gives a
`(1−1/e)`-approx ⟹ if `k` is poly, greedy finds an `O(k log)` cover in poly time (each step: add
the point maximizing uncovered-visible-volume, estimable by sampling). So Idea H (scored UNCLEAR)
is not dead — it is the **cover-finding engine for Q**. Test (for main): greedy-cover realizable
`X_t`; report `k` vs `t,d` and whether growth is driven by pocket-splitting.

### V/W-refinement [honest status of the non-persistence PROOF the lead asked for]
The lead asked me to turn V into a proof that `u_max` can't stay anti-diagonal (non-persistence).
Honest status: **V is a genuine mechanism but not yet a forcing proof, for a specific reason** —
`Σ(X_t)` does NOT evolve as `P Σ Pᵀ` (the body is `X_{t-1}` *cut by a halfspace-union*, per
decomposition `(D)`, not the operator's image), so Perron–Frobenius acts only INDIRECTLY (through
where `x*` and the cuts sit), not as a clean spectral forcing on `Σ`. What survives rigorously:
nonneg directions are provably SENSED (§V), so IF the long axis is nonneg it self-corrects; the
gap is proving it stays near the nonneg cone.

**The partner-lemma that WOULD close it** (matching the `μ_W ≤ 1` measurement): a **projective
Dobrushin/Furstenberg contraction** — the FW-recentering induces a map on the top-eigendirection
`u_max ∈ P^{d−1}` that contracts toward the sensed cone with a spectral gap, so
`P(u_max blind for k rounds) ≤ (1−β)^k`. **Linchpin the advisor flagged (I now have a partial
answer):** a rough calc says a *uniformly random* direction is NOT reliably sensed — for random
`v`, `max_i v_i + min_i v_i` concentrates near `0` (both extremes `≈ ±√(2 log d/d)`), so the
anti-diagonal/blind set is **not** small under the uniform sphere measure. CONSEQUENCE:
non-persistence cannot come from genericity — it must come from the **dynamics** (the cut actively
pushing `u_max` out of the blind cone), which is exactly V's Perron bias. So V and W are
genuinely coupled: W's mixing needs V's drift. The decisive measurement is the one already folded
into the §6 run: **autocorrelation time of `u_max`'s sensed/blind status** — short ⟹ non-persistent
(route lives), frozen-blind ⟹ the counterexample.

### Corollary-C note (now subsumes K): the one measurement that decides it
K collapsed into Corollary C (need a family of admissible cuts = need `poly(d)` queries to narrow
the pyramid union to ≤2 coords). The decisive, unmade measurement is **active-set flatness** (my
Idea T salvage): track `|A(c^r)| = #{i : |x*_i − c^r_i| ≥ ½·max_j|x*_j − c^r_j|}` along real runs.
If `|A|` is usually `O(1)` (flat gap), Corollary C is within reach at those rounds (convex cuts,
cutting planes) — and it dovetails with M1 (signed-consistent rounds also give convexity). If
`|A| = Θ(d)` throughout (spread gap), Corollary C is wall-equivalent. One cheap log settles the
direction of the whole convex-narrowing program.

---

## Responses to Batch-4 verdicts + the BIG REDIRECT (volume ratio is the un-attacked co-requirement)

### V-gap (positive association): a PARTIAL proof, and exactly where it breaks
Advisor's gap is correct: `Σ(X_t)` is a covariance (off-diagonals can be negative), so "P_σ≥0 ⟹
u_max nonneg" is a non-sequitur; the make-or-break sub-lemma is **positive association (FKG ⟹
Σ⪰0 entrywise)**. Partial answer: **each single cut is a monotone (up-set) event.** After
sign-fold, `K = {max_i w_i + min_i w_i ≥ 0}` with `w` increasing in `y`; both `max` and `min` are
increasing, so `K` is an **up-set**. Conditioning a positively-associated measure on an up-set
preserves positive association (Harris/FKG). The box measure is positively associated (product).
So **as long as all cuts share a sign orientation, `X_t` stays positively associated ⟹ `Σ⪰0`
entrywise ⟹ `u_max` is nonneg (Perron now applies to `Σ`) ⟹ SENSED.** WHERE IT BREAKS: different
cuts sign-fold differently (`s^r` varies), so in the original coordinates the cuts are up-sets in
*different* twisted orders; positive association is not preserved across mixed orientations. So —
like everything — V's positive-association route holds in the consistent-orientation (toward/flat-
gap = star) regime and is open exactly in the mixed regime. Still, this converts "assert positive
association" into a concrete conditional theorem + identifies the precise obstruction (orientation
mixing), which is the right honest status. W: **conceded DEAD** (blind cone is axis-anchored /
recentering-invariant per crux §9, frame doesn't rotate; deterministic trajectory ≠ Furstenberg's
random products) — keep only the ρ(u_max) autocorrelation diagnostic. X: conceded it hits the same
volume-ratio wall (skewness controlled only at the well-roundedness floor).

### THE REDIRECT, reframed cleanly: the volume ratio has a simple per-cut form, and ball-preservation kills the advisor's own witness
Target: `vol(X_t) ≤ poly(d,t)·vol(B_∞(x*,ρ_t))`. Two clean simplifications:

**(1) It is exactly "inradius keeps pace with scale."** Balanced cuts halve volume, so
`vol(X_t) = 2^{−t}vol(box)`, and `vol(B_∞(x*,ρ_t)) = (2ρ_t)^d`. Hence
```
vol(X_t)/vol(B) = 2^{−t}/(2ρ_t)^d ≤ poly  ⟺  ρ_t ≥ 2^{−t/d}/poly^{1/d} ≈ (vol X_t)^{1/d}/2.
```
So the entire well-roundedness co-requirement is: **the ℓ∞-inradius at `x*`, `ρ_t`, decays no
faster than `vol^{1/d} = 2^{−t/d}` (the body's typical linear scale).** Per-cut form (analogous to
the per-cut κ target): **`ρ_{t+1} ≥ ρ_t · 2^{−1/d}/(1+o(1))`** — the inradius shrinks at the same
rate as the linear scale. And `ρ_t = ½·min_r m_r` where `m_r = max w_r(x*)+min w_r(x*)` is cut
`r`'s margin (ball-preservation lemma) — so this is a bound on the **worst cut margin**, a much
simpler object than `κ`.

**(2) Ball-preservation makes the advisor's central-valley witness NON-REALIZABLE.** The witness
"unit ball minus a thin central slab" (κ≈1, Cheeger→0, bad volume ratio) requires a cut passing
THROUGH the center. But ball-preservation guarantees `B_∞(x*,ρ_t) ⊆ X_t` — **no realizable cut
crosses the preserved ball at `x*`.** So the central-valley dumbbell is excluded for exactly the
same reason slivers are (CLY Lemma 3). This is strong: the very shape that shows "κ insufficient"
is forbidden by the structure — so the volume-ratio bound is not hopeless, it is another
realizable-vs-nonrealizable dichotomy to prove.

## BATCH 6 (routed via main) — cross-field angles on the well-roundedness volume ratio `ρ_t ≳ vol^{1/d}`

### Idea AA [TOP] — Balancedness forbids inradius collapse (the sliver tension, repurposed)
**(1) Connection.** Reverse isoperimetry + the project's own sliver obstruction, turned into a
positive tool.
**(2) Mechanism.** Excessive inradius loss (`ρ_{t+1} ≪ ρ_t·2^{−1/d}`) means the new cut passed
close to `x*` (small margin `m_r`). But `honest_barrier.py` already found: cuts that push `x*`
toward a cut boundary drive the body toward a **sliver** — volume drops by MORE than half. A
*balanced* cut removes EXACTLY half. So exact halving is incompatible with a too-close cut ⟹
**balancedness lower-bounds the per-cut margin, hence the inradius.** The same tension (pinch vs
halve) that blocks a realizable Cheeger bottleneck also blocks inradius collapse.
**(3) Lemma.** "For a balanced cone-cut, `m_r ≥ Ω(2^{−t/d})` (worst margin keeps pace with scale)"
⟹ `ρ_t ≥ Ω(vol^{1/d})` ⟹ the volume ratio is poly ⟹ (with bounded κ) hit-and-run mixes ⟹ SSG∈P.
**(4) Test/refute.** Track `ρ_t` (= ½·min_r m_r, exactly computable — it's an LP / min over cuts)
vs `2^{−t/d}` on realizable trajectories, and correlate inradius-loss rounds with volume-loss
fraction. **Refuted** if a balanced round shows large inradius loss with clean half-volume loss
(inradius and volume decoupled) — that's the realizable well-roundedness counterexample to hunt.
» ADVISOR: (pending)

### Idea EE — Log-volume-ratio potential `Φ_t = log vol(X_t) − d·log(2ρ_t)` and its per-cut increment
**(1) Connection.** Lyapunov/potential method (the tool that clarified κ via `spread`).
**(2) Mechanism.** `Φ_t = log(vol ratio)`; we need `Φ_t ≤ O(log dt)`. Per cut, `Δ(log vol) = −log2`
and `Δ(d log 2ρ) = d·log(ρ_{t+1}/ρ_t)`. So `ΔΦ_t = −log2 − d·log(ρ_{t+1}/ρ_t)`. Well-roundedness
⟺ `ΔΦ_t ≤ O(log dt)/t` on average ⟺ `d·log(ρ_t/ρ_{t+1}) ≤ log2 + o(1)` (inradius shrinks at the
volume rate). Unlike `spread` (which failed to be monotone), `Φ_t` starts at `O(1)` (box is round)
and we need only that it does not RUN AWAY — a boundedness, not monotonicity, claim, matching the
"isotropic start + don't drift" picture that worked conceptually for κ.
**(3) Lemma/algorithm.** Bound `Σ_t max(0, ΔΦ_t) = O(log dt)` (total inradius over-loss is small).
**(4) Test/refute.** Plot `Φ_t` over rounds; refuted if it grows linearly in `t` (volume ratio
exponential). Cheap (reuses `ρ_t` and `vol` already logged).
» ADVISOR: (pending)

### Idea BB — Radial `d`-th moment (star regime): `vol ratio = mean_u (R(u)/ρ)^d`, controlled by κ + spike-count
**(1) Connection.** Star-body / radial geometry, John-position analogue for non-convex bodies.
**(2) Mechanism.** In the star regime `vol(X_t)/vol(inball) = E_u[(R(u)/ρ)^d]` (a `d`-th moment of
the radial function). κ bounds the *aspect* (bulk `R/ρ`); a spike of angular width `θ` and length
`L` adds `≈ θ^{d−1}(L/ρ)^d` to the moment — and κ bounds `θ ≥ κ^{−1/2}` from BELOW (spike width),
so each spike's volume contribution is bounded PROVIDED the spike COUNT is poly. So the volume
ratio = (κ-bounded bulk) + (poly spikes × bounded each). This makes the vol-ratio the natural
partner to κ: κ handles the bulk/width, the residual is a **spike count**.
**(3) Lemma.** "`E_u[(R/ρ)^d] ≤ poly` given `κ ≤ poly` and `≤ poly` spikes." Reduces vol-ratio to
counting radial spikes — the same object as Q's lobe/pocket count (BATCH 5), unifying the two.
**(4) Test/refute.** In the star regime (exact ray-shooting), estimate `E_u[(R/ρ)^d]` and the spike
count vs `d,t,κ`. Refuted if the moment is exp with poly κ and poly spikes.
» ADVISOR: (pending)

### Idea CC — Thin-shell "peeling": each balanced cone-cut removes the point-reflection = far mass, keeping X_t concentrated
**(1) Connection.** Concentration of measure / thin-shell (Klartag-type), specialized to cut-bodies.
**(2) Mechanism.** The removed set is the point-reflection of the kept set through `c`; a balanced
cut removes a "far" symmetric region each round. Iterated, this **peels mass at large radii**,
preventing volume from escaping into thin far reaches while the inball stays small (the failure
mode of a bad volume ratio). Conjecture: the radial mass profile of `X_t` from `x*` stays
light-tailed (concentrated near `∼ρ_t`), so `vol` is dominated by the inball's scale.
**(3) Lemma.** "The radial mass CDF `F(r) = μ(‖y−x*‖_∞ ≤ r)/μ(X_t)` satisfies `F(C·ρ_t) ≥ 1−1/poly`
— most mass is within a poly factor of the inradius" ⟹ volume ratio poly.
**(4) Test/refute.** Plot the radial mass profile from `x*` on realizable `X_t`; refuted if a
`1/poly`-mass heavy tail sits at radius `≫ ρ_t` (volume escaping to far reaches).
» ADVISOR: (pending)

**Batch-6 priority:** AA is the centerpiece — it repurposes the project's OWN sliver obstruction to
attack the newly-identified co-requirement, has a one-line exact-computable test (`ρ_t` vs
`2^{−t/d}`), and (with ball-preservation excluding the central-valley witness) turns the volume
ratio into another realizable-dichotomy. EE gives the clean potential; BB unifies vol-ratio with
Q's spike/pocket count; CC is the concentration lens. The single cheapest run: **`ρ_t` vs
`2^{−t/d}` (and `Φ_t`) on the existing exact-rejection trajectories** — settles whether the
inradius keeps pace with scale, the whole ballgame for the co-requirement.
