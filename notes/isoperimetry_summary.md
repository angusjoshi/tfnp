# Sampling `X_t = box ∩ ⋂_r K(c^r,s^r)`: a consolidated technical note

Self-contained summary of the attack on the sampling problem that stands between
the CLY/hit-and-run reduction and a poly-time `ℓ∞`-contraction fixed-point
algorithm (hence `SSG ∈ P`). It collects the rigorous partial results, the
barrier results, and — the main organising finding — that the three genuinely
different routes to a poly-time sampler all reduce to **one** obstruction. Detail
and code live in `notes/isoperimetry_attack.md`, `notes/isoperimetry_conditioning.md`,
and `notes/polytime_experiments/`; this note is the map and the honest ledger.

Throughout, `f:[0,1]^d→[0,1]^d` is a `λ`-contraction in `ℓ∞`, `x*` its fixed
point, and the algorithm maintains the non-convex body
`X_t = [0,1]^d ∩ ⋂_{r≤t} K(c^r,s^r)`, `K(c,s)=⋃_{i∈S}P_i^{s_i}(c)` a union of
`ℓ∞` pyramid cones, `c^r` the Fermat–Weber (balanced) center of `X_{r-1}`. A
poly-time near-uniform sampler for `X_t` closes the problem (`hitrun.md`).

## 0. The three routes and the one wall

A poly-time sampler follows from **any** of:

1. **(Cheeger)** `h(X_t) ≥ 1/poly` ⟹ hit-and-run mixes (`isoperimetry_attack.md`).
2. **(Conditioning)** `κ(X_t) = λ_max/λ_min ≤ poly` ⟹ one whitening + hit-and-run,
   *provided the whitened body isn't a dumbbell* (`isoperimetry_conditioning.md`).
3. **(Exact)** `X_t` star-shaped about a *findable* center ⟹ exact ray-shooting,
   no Markov chain at all (this note §5, C3).

**Main finding.** All three reduce to the same obstruction — the body developing
an **anisotropic / thin (dumbbell) direction**, equivalently the loss of the
flat-gap/star regime. Route 3 needs star-shapedness, which *is* the flat-gap
regime (Theorem A). Route 1's only counterexamples are dumbbells. Route 2 is
literally **equivalent** to Route 1 (§4.3): `κ`-boundedness fails exactly when a
1-D marginal is a dumbbell, which is a Cheeger bottleneck. So none of the three
escapes the core hardness; each is `≈ SSG ∈ P`. What the work *does* deliver is a
precise localisation of that hardness, several rigorous partial theorems that hold
up to it, and a clean barrier explaining why the "easy" refutations are illusory.

## 1. Two verified structural facts

Let `w_i = s_i(y_i − c_i)` (sign-aligned coordinates about the apex).

* **(MEM)** `y ∈ K(c,s) ⟺ max_i w_i + min_i w_i ≥ 0`. (Verified; `verify_kernel.py`.)
* **(KER)** `ker K(c,s) = {z : s_i(z_i−c_i)+s_j(z_j−c_j) ≥ 0 ∀ i≠j}` — a convex
  cone, `O(d²)` facets. The removed set `N` is the point-reflection of `K` through
  `c` (`ρ(K)=N̄`), so a balanced cut removes exactly half of any `c`-symmetric mass.

## 2. Positive results (proved)

**Theorem A (star regime).** If every cut points toward `x*` on every coordinate
(`s^r_i(x*_i−c^r_i) ≥ 0`), then `x* ∈ ⋂_r ker K(c^r,s^r)`, so `X_t` is star-shaped
about `x*` and is sampled *exactly* by ray-shooting from any kernel point —
poly-time, no isoperimetry. Proof from (MEM); machine-checked 0 failures to `d=12`
(`verify_thmA.py`); formalised in `Tfnp/HitRun.lean` (`starshaped_of_toward`).
This hypothesis holds iff the gap vector `x*−c` is *flat* (every coord `>λr` or
`≈0`); it fails exactly when `X_t` is anisotropic — **localising the entire
difficulty to anisotropy.**

**Ball preservation.** If `max_i w_i(x*)+min_i w_i(x*) ≥ 2ρ` then
`B_∞(x*,ρ) ⊆ K(c,s)`; toward-cuts preserve `B_∞(x*, r/2)` (well-roundedness).

**Covariance decomposition (D).** For a balanced cut (kept/removed halves
`K',R`, means `m_K,m_R`, `Δ=m_K−m_R`): `Σ(X∩K) = 2Σ(X) − Σ(R) − ½ΔΔᵀ`. Hence
`λ_max(X∩K) ≤ min(2λ_max(X), diam²/4 ≤ d/4)` unconditionally — **the whole `κ`
question is a lower bound on `λ_min`.** Obstruction: `λ_min` collapses only in a
direction where the removed half `R` is both spread and mean-shifted (an oblique
off-center lobe).

**Symmetric rank-1 downdate.** If `X` is symmetric about `c`, the balanced cut is
`Σ(X∩K) = Σ(X) − m_K m_Kᵀ`: `λ_max` never grows, only the direction `m_K` loses
variance, and `m_K` aligns with the *longest* axis. So the cut is **self-correcting**
— `κ` contracts (verified `100→27`, `906→228`; `verify_symcut.py`). The downdate
*fraction* `m_{K,i}²/λ_i` rises from `≈0` (thinnest axis) to `≈0.6` (thickest):
a "shave the top" equalizer. On real (asymmetric) bodies `(S)` predicts `Σ(X∩K)`
to `≈15%` and `κ` stays bounded with mean-reversion (`verify_asym.py`).

**Mean-shift (bathtub) lemma.** For any measure-`½` set `K` and direction `v`,
`|E[v·y|K]−E[v·y]| ≤ MS_v`, the shift of the extremal half `{v·y≥median}`; and
`MS_v² ≤ (1−c)σ_v²` with `c>0` **iff the marginal of `v·y` is not a dumbbell**
(Gaussian `c=.36`, uniform `.25`, two-well `→0`; verified). ⟹ (symmetric)
conditional `κ(X∩K) ≤ κ(X)/c` under non-dumbbell marginals.

**Fermat–Weber = balanced**, and the identity `m_K + m_R = 2(centroid − c)`: the
reflection defect is twice the FW-center-to-centroid distance.

**`κ ⇒ h` (star regime).** Star-shaped `+ κ ≤ K ⟹ h ≥ 1/poly(d,K)`: bounded `κ`
rules out spikes (a spike has `κ→∞`); evidence `kappa_vs_h.py` (`κ≤3 ⟹ h_iso≥0.35`).

**`d ≤ 2`.** Every cut is a halfspace (`max+min = sum`), `X_t` convex — poly.

## 3. Barrier / negative results (why the easy wins are illusory)

* **The unrestricted Open Lemma is false but non-realizable.** Intersections of
  pyramid-unions *can* have `h → 0`, but every such example is a volume-`→0`
  **sliver**; forcing a bottleneck and keeping positive volume are incompatible
  for these cuts, and CLY's ball-preservation guarantees realizable bodies are
  never slivers at `x*`. So realizable bodies dodge the cheap counterexamples.
* **Empirical dichotomy (extensive search).** Healthy-volume body ⟹ `Ω(1)`
  isotropic Cheeger and good mixing; small Cheeger ⟹ collapsed sliver. No
  realizable healthy-volume bottleneck found to `d=12`, `δ→10⁻⁶`, including hard
  SSG instances with spread `x*`.
* **Idealized symmetric multi-cut dynamics does NOT bound `κ`.** A pure downdate
  only *removes* variance, so a thin axis is never repaired; `spread=Σ(logλ−mean)²`
  is a monotone Lyapunov yet `κ` stays huge on graded spectra. **The real `κ`
  stays bounded only because the trajectory starts isotropic (the box) and the
  *asymmetric* term `2Σ−Σ(R)` can *inject* variance to repair thin axes.** So the
  asymmetry is the repair mechanism, not a defect — a genuine reframing.

## 4. The meta-result: the three routes are the same wall

* **Route 3 ≡ flat-gap regime.** Star-shapedness (certifiable via the LP kernel)
  is exactly Theorem A's hypothesis; it is lost when the body turns anisotropic.
* **Route 2 ≡ Route 1.** The `κ` bound fails iff some whitened 1-D marginal is a
  dumbbell (mean-shift lemma), which is a Cheeger bottleneck. So `κ`-poly is *not*
  strictly easier than `h`-poly.
* **Route 1's realizable counterexample = a realizable dumbbell**, which is exactly
  a mixing bottleneck. Its existence ⟺ the algorithm fails ⟺ SSG hard.

So the problem has one wall — a realizable **anisotropic/dumbbell** `X_t` — and
crossing it in any of the three formulations is equivalent to resolving SSG.

## 5. C3 in detail (the exact-sampler route)

Exact ray-shooting needs a *findable* star-center. The certifiable (LP) kernel
`box ∩ ⋂_r ker K(c^r,s^r)` is **monotone shrinking in `t`** (each cut only adds
`\binom d2` constraints), so once empty (`t ≈ d/2`, empirically) it never recovers
via that certificate. The *true* kernel is not monotone — cutting a hard-to-see
region can restore star-shapedness — but empirically it does not recover either
(best-center sample-visibility falls to `0.5–0.9` and stays there: the body
becomes genuinely non-star-shaped; `c3_test.py`). And there is a hard
**balanced-vs-kernel tension**: keeping the apex in the kernel preserves it (the
kernel contains the apex) but such peripheral queries stop halving the volume
(`starshape_collapse.py`). So no block-restart scheme recovers exact sampling.

## 6. Exact open gaps (in decreasing order of promise)

1. **Asymmetric repair.** Show the asymmetric term `2Σ−Σ(R)` injects enough
   variance to keep pace with thin-axis creation, from the isotropic start. This
   is the reframed C2/`κ` target and the freshest lead — it is *not* the symmetric
   downdate (which cannot repair) but the deviation from it.
2. **Angular isoperimetry of the radial function.** Localisation through the FW
   center gives single-interval needles in the star regime; it controls radial but
   not *angular* (spike) bottlenecks. Bounded `κ` rules out spikes, so the residual
   is the spherical isoperimetry of `R(u)^d du` — a cleaner sub-question than raw `h`.
3. **Remove the non-dumbbell hypothesis** from the mean-shift conditional — but
   this *is* the wall (§4), so expect it to be as hard as SSG.

## 7. Empirical status and the reliability ceiling

Within the **reliably measurable window** — exact rejection to `t ≈ 13`, honest
budget-escalated hit-and-run to `d ≈ 12, t ≲ 2d` — all signals are positive:
`h_iso = Ω(1)`, `κ ≈ 2–7` with mean-reversion, no trapping, `δ`-independent. Two
confounds were identified and controlled: raw (non-isotropic) Cheeger flags
harmless *elongation* as a bottleneck; a fixed-budget walk flags slow mixing as
*trapping* (budget escalation drives it away). **Beyond the ceiling both samplers
fail** (warm-start inflates `κ`; the honest explorer degenerates on `2^{-25}`-volume
bodies), so no claim — positive or negative — is made in the true hard regime
(`d` large, `δ = 2^{-poly}`). The positive evidence is real but bounded; it is not
a proof, and a proof would be `SSG ∈ P`.

## 8. Scripts (`notes/polytime_experiments/`, run under `venv`)

`verify_kernel.py` (MEM/KER), `verify_thmA.py` (Theorem A), `verify_decomp.py`
(D), `verify_symcut.py` (rank-1 downdate `(S)`), `verify_asym.py` (S→general
bridge), `worst_cut.py` (single balanced cut on the box), `conditioning.py`/
`cond_adv.py` (κ growth; balanced vs adversarial), `kappa_dynamics.py`/
`kappa_escalate.py` (trajectory + honest escalation), `kappa_vs_h.py` (κ↔h),
`idealized_dynamics.py` (§3 symmetric dynamics), `potential_test.py` (Lyapunov
diagnostics), `c3_test.py` (kernel recovery), `starshape_collapse.py` (kernel
collapse), `barrier.py`/`compat_search.py`/`honest_barrier.py` (bottleneck
searches), `ssg_probe.py`/`mixing_test.py`/`radial_delta.py` (mixing/roundness).
