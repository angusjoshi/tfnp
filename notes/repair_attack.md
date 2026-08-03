# The λ_min-attractor / asymmetric-repair attack — empirical measurements

Attacking the reframed crux of C2 (see `notes/isoperimetry_conditioning.md` §12 and
`notes/isoperimetry_summary.md` §6.1): the real trajectory keeps `κ(X_t)` bounded
**only** because (i) it starts isotropic (the box) and (ii) the *asymmetric* term
`2Σ(X)−Σ(R)` in the covariance decomposition (D) can **inject** variance to repair
a thin axis, which the pure symmetric downdate `−m_K m_Kᵀ` cannot. Target: measure
whether asymmetric repair actually keeps `λ_min` from drifting to 0.

**This is `= SSG ∈ P`; the goal is clean measurement + a sharpened open question,
not a closure.** All numbers below are inside a small-`d`, shallow-`t` window where
exact rejection sampling is ground truth (no Markov-chain confound), and are
subject to the reliability caveats in the final section. Never extrapolated past
the window.

## Method (exact rejection ground truth)

`repair_measure.py`. At each round `t`: exact-rejection uniform sample of
`X_t = box ∩ ⋂_{r<t} K(c^r,s^r)` (realizable SSG/topical cuts, ternary signs,
Fermat–Weber balanced center from the exact sample). Covariance `Σ(X_t)`, ascending
spectrum, `v_min = argmin` eigenvector. The balanced cut splits `S` into kept
`K'=X∩K` and removed `R=X∩N` (both ≈ mass ½). The exact decomposition (D):

```
Σ(K') − Σ(X) = ½(Σ(K') − Σ(R))   −   ¼ Δ Δᵀ ,      Δ = m_K − m_R
               \___ ASYM injection __/     \__ DOWNDATE (rank-1, removes) __/
```

(In the symmetric case `Σ(K')=Σ(R)` so ASYM=0 and `¼ΔΔᵀ = m_K m_Kᵀ` — the pure
downdate.) Evaluated along `v = v_min`:
- **T1** — the `λ_min(X_t)` trajectory over rounds (absolute and `1/κ = λ_min/λ_max`).
- **T2** — `asym_v = ½(vᵀΣ(K')v − vᵀΣ(R)v)`, `down_v = ¼(v·Δ)²`; does `asym_v > 0`
  (repair), and does it out-pace the downdate (`asym_v > down_v`)?
- **T3** — the central-cut inequality `Var_R(v·y) + ½(v·Δ)² ≤ (2−c)·Var_X(v·y)`,
  equivalently `vᵀΣ(K')v ≥ c·λ_min` with `c = 2 − (Var_R+½(v·Δ)²)/Var_X`. Report the
  worst (min) `c` observed. `c` bounded away from 0 ⟺ a single balanced cut cannot
  collapse the current thinnest axis.

**Resource caps obeyed:** `d ≤ 6`, `t ≤ 10`, `N = 400` samples/round, rejection
batch `50k`, per-call draw cap `3M`, one foreground run at a time.

## Results

Runs: exact rejection, `N=400`/round, `δ=10⁻³`, `t=10`, within all caps. Six
instances (d=4,5,6; SSG spread-`x*` and topical near-isotropic-`x*`). The
`κ range` / `1/κ` / per-round κ-ratio columns are from the **fresh** 400-pt
rejection sample each round (the reliable measure). `T3 worst c` is the minimum
over all cuts of `c = 2 − (Var_R(v)+½(v·Δ)²)/Var_X(v)` along `v=v_min`.

| kind | d | seed | κ range | 1/κ min | fresh κ-ratio/rnd (geomean) | ASYM>0 | ASYM>down | **T3 worst c** |
|---|---|---|---|---|---|---|---|---|
| SSG | 6 | 0 | 1.50–3.78 | 0.264 | 1.108 | 3/10 | 1/10 | **+0.726** |
| SSG | 6 | 1 | 1.47–4.60 | 0.217 | 1.135 | 3/10 | 1/10 | **+0.734** |
| SSG | 5 | 2 | 1.38–2.77 | 0.361 | 1.081 | 4/10 | 0/10 | **+0.710** |
| SSG | 6 | 3 | 1.57–2.47 | 0.404 | 1.051 | 6/10 | 1/10 | **+0.696** |
| SSG | 4 | 0 | 1.31–8.94 | 0.112 | 1.235 | 3/10 | 1/10 | **+0.698** |
| topical | 6 | 0 | 1.50–4.03 | 0.248 | 1.116 | 5/10 | **5/10** | **+0.814** |

Identity residual of (D) along `v_min` is `≤2·10⁻⁴` throughout (decomposition
verified at `N=400`). **T3 holds in all 60 cuts; the global worst-case is
`c = +0.696`.**

### T1 — the λ_min trajectory

*Absolute* `λ_min(X_t)` declines every round — but this is trivially the body
shrinking (vol halves each cut, so linear scale drops `~2^{-1/d}`/round); it is not
conditioning loss. The scale-free quantity is `1/κ = λ_min/λ_max`. Across all six
runs `1/κ` stays bounded in `[0.11, 0.73]` (i.e. `κ ∈ [1.3, 8.9]`) over `t≤10`,
with two behaviours:
- **plateau** (most runs): `κ ≈ 2–4` and flat/mean-reverting (e.g. d=6 s3:
  1.57→2.47, essentially flat; d=5 s2: settles at `1/κ≈0.37`).
- **mild upward drift**: d=4 s0 climbs to `κ=8.9` (`1/κ=0.11`); d=6 s1 to 4.6.

Per-round fresh κ grows by geomean `1.05–1.24` (worst d=4 s0). No collapse; but
this is **bounded-with-drift, not a proven plateau** — consistent with the §6/§10
reliability caveat. Whether the drift plateaus (attractor / C2 holds) or slowly
compounds is exactly what is unmeasurable past the window.

### T2 — is the asymmetric term the repair mechanism? (a regime split)

The (D) decomposition splits each cut into `asym_v = ½(vᵀΣ(K')v − vᵀΣ(R)v)` (the
deviation from a pure symmetric downdate; `>0` ⟺ kept half more spread than removed
half along `v` ⟺ repair) and the rank-1 downdate `down_v = ¼(v·Δ)²` (always removes,
`= (m_K·v)²` in the symmetric case). Two clearly different regimes emerge — and the
headline is that **the §12 "asymmetric injection repairs thin axes" story is
confirmed on isotropic instances but is NOT the dominant mechanism on the hard
spread-`x*` SSG instances**:

- **Topical / near-isotropic `x*`:** asymmetric injection genuinely repairs.
  `asym_v > 0` in 5/10 cuts and out-paces the downdate in **5/10**; the variance
  along the *old thin axis* is frequently **raised** (newvar/old up to 1.36,
  geomean ≈ 1.00). This is §12's mechanism firing as hypothesised.
- **SSG / spread-`x*` (the hard regime):** asymmetric injection mostly does **not**
  repair — `asym_v > 0` in only 3–4/10 cuts, out-paces the downdate in 0–1/10, and
  is on average slightly *negative* along `v_min`. Yet the thin axis still survives
  (newvar/old geomean 0.81–0.89). The protective mechanism here is different: the
  rank-1 downdate `¼ΔΔᵀ` aligns with the **long** axis, so its projection onto
  `v_min` (`down_v`) is tiny — **the cut simply misses the thin axis**
  (downdate-orthogonality), rather than injecting variance into it.

So there are two distinct reasons `λ_min` survives, and which one operates depends
on the anisotropy/`x*`-spread of the instance. On the genuinely hard SSG instances
it is downdate-orthogonality, not asymmetric repair.

### T3 — the central cut cannot collapse the current thin axis (clean positive)

`Var_R(v·y) + ½(v·Δ)² ≤ (2−c)·Var_X(v·y)` holds along `v_min` in **60/60 cuts**,
worst-case `c = +0.696`, medians `c ≈ 0.77–0.98`. Equivalently
`vᵀΣ(X∩K)v ≥ c·λ_min` with `c ≥ 0.70`: **a single balanced (Fermat–Weber-centred)
cut provably preserves ≥ ~70% of the current thinnest-axis variance in the tested
window — it cannot collapse the pre-existing thin axis.** This `c` is a
*conservative* estimate: its denominator `Var_X(v_min)=λ_min` is the sample minimum
(fit to noise, MP-deflated at N=400), which biases the ratio up and `c` down, so the
true margin is if anything larger.

### Reliability caveat (a confound identified and quarantined)

The kept half `K'` has `≈N/2 = 200` points, so its sample covariance is
Marchenko–Pastur biased: at d=6, n=200 the *smallest* eigenvalue is deflated
`~30%`. Cross-check — the same-split `κ(K')` (e.g. 2.72, 2.07) systematically
exceeds the **fresh** next-round `κ` (1.97, 1.66) by `20–30%`. Therefore the
same-split per-cut `κ'/κ` (geomean ≈ 1.2) and the same-split `λ_min'/λ_min` (geomean
0.71–0.85) are **artefact-inflated / -deflated and are NOT reported as findings**
(in particular there is **no reliable evidence of thin-axis "migration"** — the
apparent gap is fully explained by the MP deflation of the 200-pt min eigenvalue).
The reliable signals are the fresh-sample κ trajectory (T1), the sign/decomposition
of `asym_v`/`down_v` (T2, scalar projected variances, robust), and the conservative
T3 margin.

## The sharpened open question

T3 gives a clean per-cut fact: **`c ≥ 0.70`, so no single balanced cut collapses
the current thin axis.** But `c ≈ 0.70` is `< 1` — a per-cut multiplicative *shave*
of the thin axis — so T3 alone yields only `κ ≤ (1/c)^t ≈ 1.43^t`, i.e. exponential;
**bounded `κ` does NOT follow from T3.** Yet the *fresh* trajectory grows far slower
(κ-ratio `≈1.06–1.11`/round, not 1.43), so something compensates the T3 worst-case
shave round-to-round. The measurements localise the compensation to two
instance-dependent mechanisms: (a) isotropic-`x*` — active asymmetric injection
(`c` can exceed 1); (b) spread-`x*` — the downdate hits the *long* axis, so `λ_max`
shrinks in step and the **ratio** `λ_min/λ_max` is roughly preserved even though
`λ_min` alone is shaved.

This reframes the target away from the scale-dependent "`λ_min(X∩K) ≥ c·λ_min(X)`,
`c>0`" (which T3 already gives, and which is *insufficient*) to the **scale-free**
statement:

> **Sharpened C2 target.** Show the per-cut condition-number ratio is controlled:
> `κ(X∩K) ≤ (1+o(1))·κ(X)` for a balanced cut — equivalently the per-cut `λ_min`
> shave is matched by the `λ_max` shave (`λ_min'/λ_min ≥ λ_max'/λ_max`), so that the
> cut acts as a near-isotropic contraction rather than an anisotropic one. The
> data shows this holds with the ratio `≈1.1` in the reliable window but is
> **bounded-with-drift**, and the honest gap is bounding (or plateauing) that
> drift over `t = poly` — which remains `= SSG ∈ P` and is unmeasurable past the
> `d≈12, t≈2d` reliability ceiling.

Concretely, the freshest handle the data hands us: on spread-`x*` (hard) instances
the mechanism is **downdate-alignment with the long axis** (T2), so the concrete
lemma to attempt is "`m_K` (equivalently `Δ`) aligns with the top eigenvector of
`Σ(X)`, and never with the bottom one," which would give `λ_max'/λ_max ≤ λ_min'/λ_min`
directly. This is the same wall as before but now with a specific, measurable
alignment claim rather than the diffuse "asymmetry repairs" framing — and the T2
data shows the alignment is **intermittent** (`down_v` on `v_min` is small but not
zero), so the claim as stated is not clean, which is precisely why it is still open.
