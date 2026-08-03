# The scale-free κ-contraction crux: an exact per-cut identity, a dimension-free mean-shift bound, and the sharpened wall

Attack on the sharpened C2 target (from `repair_attack.md` §"sharpened open question"
and `isoperimetry_conditioning.md` §12/§6): prove `κ(X∩K) ≤ (1+o(1))·κ(X)` for a
balanced Fermat–Weber cone-cut, equivalently that the cut is a near-isotropic (not
anisotropic) contraction.

**Verdict.** I did **not** close it (a real closure = `SSG ∈ P`). What is new and
rigorous here:

1. An **exact, coordinate-free per-direction identity** for the variance change of a
   balanced cut, `δ(v) = Cov(t̄², σ) − Cov(t̄, σ)²`, that unifies the ASYM and DOWNDATE
   terms of `(D)` into one clean formula (§1).
2. A **dimension-free, scale-free mean-shift bound** `Δᵀ Σ⁻¹ Δ ≤ 4` (⟺ `½ΔΔᵀ ⪯ 2Σ`),
   proving the downdate *alone* can never drive `λ_min` negative — it can at most zero
   out the thin axis, and only in the dumbbell limit. So **the ASYM term is the sole
   possible source of κ-blowup** (§2).
3. A **sensitivity / blind-cone structure** of the cut that pins down the mechanism and
   sharpens the wall: the cut senses direction `v` only through the correlation
   `ρ(v)=Cov(ŝ,σ)`; anti-diagonal directions (`v` with `max vᵢ ≈ −min vᵢ`) are *blind*
   (`ρ≈0`). This is simultaneously the thin-axis-protection mechanism **and** the
   obstruction, which is exactly why per-cut alignment (attack #1) is *intermittent* and
   is **provably not a clean theorem** (§3–4).
4. The wall, sharpened: κ-blowup requires a **dumbbell marginal along a cut-*sensed*
   direction**; anti-diagonal dumbbells are protected. Combined with CLY
   ball-preservation (which forbids dumbbells along *coordinate* axes near `x*`), this
   narrows the remaining danger to **diagonal-but-not-axis dumbbells**, and reframes the
   amortized (mean-reversion) hope as a concrete, testable persistence question (§5–6).

Notation as in the other notes. Sign-fold so `s=(+1,…,+1)`, translate the Fermat–Weber
center to `0`. `w = w(y)` are the sign-folded, apex-centered coordinates; `μ` uniform on
`X`; `g(w) = max_i w_i + min_i w_i`; `K={g≥0}` (kept), `N={g<0}` (removed), balanced so
`μ(K)=μ(N)=½`. `σ(w) := sgn(g(w)) = 1_K − 1_N` (so `E[σ]=0`, `E[σ²]=1`). `K'=X∩K`,
`R=X∩N`; `m_K,m_R` their means, `Δ=m_K−m_R`. `w̄ = E[w]` is the centroid (≠ 0 in general:
we centered the *FW center*, not the centroid). `Σ=Σ(X)`, `Σ'=Σ(K')`.

---

## 1. The exact per-direction change identity (∎)

For any fixed unit `v`, let `t = v·w` (scalar projection), `μ_v = v·w̄` its mean,
`t̄ = t − μ_v` the centered projection, `σ_v² = Var(t) = vᵀΣv`.

> **Identity 1.** `δ(v) := vᵀΣ(K')v − vᵀΣ(X)v = E[t̄²σ] − (E[t̄σ])²
>                = Cov(t̄², σ) − Cov(t̄, σ)².`
>
> The two summands are exactly the ASYM and DOWNDATE terms of `(D)` along `v`:
> `ASYM_v = ½(Var_{K'}(t) − Var_R(t)) = E[t̄²σ]`, and `DOWNDATE_v = ¼(v·Δ)² = (E[t̄σ])²`.

*Proof.* Balancedness gives the "sign trick": for any `f`, since
`E[f|K]=2E[f1_K]`, `E[f|R]=2E[f1_R]`, `1_K−1_N=σ`,
```
E[f|K] − E[f|R] = 2E[f·σ],        E[f|K] + E[f|R] = 2E[f].          (†)
```
Total variance for the 50/50 split: `Var(t) = ½Var(t|K)+½Var(t|R)+¼(v·Δ)²`, so
`δ(v)=Var(t|K)−Var(t) = ½(Var(t|K)−Var(t|R)) − ¼(v·Δ)²`. Expand the first term with (†):
`Var(t|K)−Var(t|R) = (E[t²|K]−E[t²|R]) − (E[t|K]²−E[t|R]²) = 2E[t²σ] − (v·Δ)(2μ_v)`,
using `E[t|K]−E[t|R]=v·Δ=2E[tσ]` and `E[t|K]+E[t|R]=2μ_v`. Hence
`ASYM_v = E[t²σ] − 2μ_v E[tσ]`. Substituting `t=t̄+μ_v` and `E[σ]=0` gives
`E[t²σ]=E[t̄²σ]+2μ_v E[t̄σ]` and `E[tσ]=E[t̄σ]`, so `ASYM_v = E[t̄²σ]`, and
`DOWNDATE_v = ¼(v·Δ)² = (E[tσ])² = (E[t̄σ])²`. ∎

**Why this is the right object.** Every prior formulation carried both a covariance
matrix `Σ(R)` and a mean vector `Δ`; Identity 1 collapses the entire per-direction
effect of the cut into two scalar correlations of the *standardized* projection with the
*fixed* cut sign `σ`. Standardizing (`s = t̄/σ_v`, unit variance), and writing
`a(v) := E[s²σ]` (ASYM) and `ρ(v) := E[sσ] = Cov(s,σ)` (SENSITIVITY):

> **Identity 1′ (the T3 factor, exactly).** The fraction of variance the cut preserves
> along `v` is
> `c(v) := vᵀΣ(K')v / vᵀΣ(X)v = 1 + a(v) − ρ(v)².`
>
> This *is* the empirical `T3` quantity (`repair_attack.md` measured worst `c≈0.70`).
> κ-blowup along a thin `v=v_min` ⟺ `c(v_min) → 0` ⟺ `ρ(v_min)² − a(v_min) → 1`.

Sanity checks. Symmetric `X` about the centroid ⟹ `σ` odd, `s` odd ⟹ `s²σ` odd ⟹
`a(v)=0`, recovering the pure rank-1 downdate `c(v)=1−ρ(v)²` `(S)`. And `|a(v)|≤1`,
`|ρ(v)|≤1` (Cauchy–Schwarz), giving `0 ≤ c(v) ≤ 2` (matches `λ_max' ≤ 2λ_max`).

---

## 2. The mean-shift is dimension-free and scale-free: `Δᵀ Σ⁻¹ Δ ≤ 4` (∎)

`ρ(v) = Cov(s,σ)` with `Var(s)=Var(σ)=1`, so `|ρ(v)|≤1`, i.e. `(v·Δ)²=4σ_v²ρ(v)² ≤ 4vᵀΣv`
for *every* `v`. Equivalently:

> **Lemma 2 (Mahalanobis mean-shift bound).** `½ΔΔᵀ ⪯ 2Σ`, i.e. `Δᵀ Σ⁻¹ Δ ≤ 4`. The
> mean-shift has Mahalanobis length `≤ 2`, with **no dependence on `d`, on scale, or on
> the shape of `X`.** It is tight in the dumbbell limit (a `±a` two-point marginal along
> a cut-sensed axis attains `ρ→1`).

*Proof.* `(v·Δ)² ≤ 4vᵀΣv ∀v` is exactly `ΔΔᵀ ⪯ 4Σ` ⟺ `‖Σ^{-1/2}Δ‖²≤4`. ∎

**Consequence — the downdate can never, by itself, collapse the thin axis.** Along
`v=v_min`, DOWNDATE `= ¼(v·Δ)² ≤ σ_v² = λ_min`. So the downdate removes *at most the
entire* thin-axis variance and never overshoots into negativity. Therefore in Identity 1′,
`c(v_min) = 1 + a(v_min) − ρ(v_min)²`, and since `ρ² ≤ 1`, **`c(v_min) < 0` is impossible
and `c(v_min)=0` requires `ρ(v_min)²=1` and `a(v_min)=0` simultaneously** — a perfect
dumbbell aligned with a fully-sensed direction. In every non-dumbbell case `ρ² ≤ 1−Ω(1)`
(bathtub lemma, `isoperimetry_conditioning.md` §8: Gaussian `ρ²≤1−0.36`, uniform
`≤1−0.25`), so:

> **Corollary 2′.** For a balanced cone-cut, `λ_min(X∩K) ≥ (a(v_min) + (1−ρ(v_min)²))·λ_min(X)`.
> The **downdate part** `1−ρ²` is controlled unconditionally *except* in the dumbbell
> limit; **the ASYM part `a(v_min)` is the sole uncontrolled term**, and it can be
> negative (removed half more spread along `v_min` than kept half — the "oblique
> off-center lobe" of `(D)`). Bounding `a(v_min)` from below is *the* crux.

This is strictly sharper than the previous framing ("control the asymmetry defect
`Σ(R)−Σ(K')`"): the crux is one scalar, `a(v_min) = E[s²σ]` along the current thinnest
axis — the correlation between *being far out along the thin axis* and *being on the
removed side of the cone*.

---

## 3. Sensitivity and the blind cone: the two-sided mechanism (∎ for the structure)

What determines `ρ(v)` and `a(v)`? The cut sign is `σ=sgn(g)`, `g=max_i w_i+min_i w_i`,
whose (sub)gradient is `∇g = e_{argmax} + e_{argmin}`. **The cut senses a direction `v`
only through how `g` covaries with `v·w`.** Decompose the sphere by sensitivity:

- **Sensed directions** (`ρ(v)` large): `v` correlated with `sgn(g)`. Prototypes:
  (a) a single dominant coordinate `v≈e_k` — large `+w_k` ⇒ `w_k` is the max ⇒ `g>0`;
  large `−w_k` ⇒ `w_k` is the min ⇒ `g<0`; so `σ≈sgn(w_k)`, `ρ` near the halfspace value;
  (b) the main diagonal `v≈𝟙/√d` — `g(a𝟙)=2a/√d`, so `σ=sgn(a)`, `ρ` large.
  Along sensed directions the downdate `ρ²` bites and `Δ` tilts toward them.

- **Blind directions** (`ρ(v)≈0`): **anti-diagonals**, `v` with `max_i v_i ≈ −min_i v_i`
  and the extremes carried by *different* coordinates. Prototype `v=(1,−1,0,…)/√2`:
  along `w=av`, `max=|a|/√2`, `min=−|a|/√2`, so `g(av)=0` — the cut is *first-order blind*
  to `v`; the sign is decided by the orthogonal (fatter) coordinates, hence independent of
  `a`, giving `ρ(v)≈0` **and** `a(v)=E[s²σ]≈0` (the odd/even parity kills it too). So
  `c(v)≈1`: **an anti-diagonal axis is neither shaved nor collapsed.**

`Δ = 2E[w σ] = 2Cov(w,σ)` is, by construction, the vector of covariances of each
coordinate with the cut sign — i.e. **`Δ points along the sensed subspace and is
orthogonal (to first order) to the blind cone.** This is the exact, mechanism-level
statement of the empirical "downdate-orthogonality" in `repair_attack.md` (T2): on hard
spread-`x*` instances the thin axis survives because it sits in the blind cone, so `Δ`
misses it — `ρ(v_min)≈0` and `a(v_min)≈0` ⇒ `c(v_min)≈1`.

**The blindness is two-sided, and that is the whole difficulty.** The same anti-diagonal
blindness that *protects* a thin axis (good) also *prevents shaving* a long axis that
happens to lie in the blind cone (bad: `κ` cannot self-correct that round). So the cut is
a contraction toward isotropy **only when the anisotropy lives in the sensed subspace**,
and is inert when the anisotropy is anti-diagonal.

---

## 4. Attack #1 (per-cut alignment) is *provably not* a clean theorem

The requested per-cut lemma — "`Δ` aligns with the top eigenvector of `Σ`, never the
bottom" — cannot hold as a clean per-cut statement, and §3 says exactly why: alignment is
governed by which eigenvectors fall in the *sensed* vs *blind* subspace, which is a
property of the current body's orientation relative to the fixed cone, not forced by
balancedness. Concretely:

- If `v_max` is anti-diagonal, `ρ(v_max)≈0`: `Δ` is (first-order) *orthogonal* to the top
  eigenvector — the opposite of the desired alignment. This is realizable (nothing forbids
  the long axis from being anti-diagonal), and it is exactly the intermittency
  `|m̂_K·û_top| ∈ [0.05,0.94]` measured in `isoperimetry_conditioning.md` §10.
- The only thing Lemma 2 forces is the *weak* one-sided fact
  `Δᵀ Σ⁻¹ Δ ≤ 4` (§2): the component of `Δ` on any direction is `≤ 2√(that direction's
  variance)`, so `Δ`'s bottom-eigenvector component is `≤ 2√λ_min` in *absolute* terms —
  automatically small — but not small as a *fraction* `‖Δ‖`, which is what attack #1 asked
  for and which is false when `‖Δ‖` itself is small (the hard regime).

So the honest status of attack #1: the requested alignment is **intermittent by
mechanism**, and the correct residual is not "prove alignment" but "prove the *blind*
long-axis event is non-persistent" (§6).

---

## 5. Attack #3 (SSG structure) sharpens the wall

Combine Corollary 2′ (blowup ⟺ dumbbell along a *sensed* direction) with the CLY
structural guarantees:

- **Ball-preservation** (`isoperimetry_attack.md` §2, `Tfnp/HitRun.lean`): toward-cuts
  keep `B_∞(x*, r/2) ⊆ X_t`. A contained `ℓ∞`-ball forces every **coordinate** marginal
  of `X_t` to have a solid central band of mass of width `≥ r` around `x*_i` — so **no
  coordinate marginal can be a two-point dumbbell.** By §3(a), coordinate axes are the
  prototypical *sensed* directions. Thus the most dangerous configuration (a dumbbell
  along a sensed *coordinate* axis, where Lemma 2 is tight and `c→0`) is **forbidden by
  ball-preservation.**
- The residual danger is a dumbbell along a **sensed non-coordinate** direction — chiefly
  the main **diagonal** `𝟙/√d` (also sensed, §3(b)) — that a small preserved ball does not
  rule out. So the wall narrows to: *can a realizable `X_t` develop a diagonal (or other
  sensed, non-axis) dumbbell thin marginal while keeping `Ω(1)`-mass and a preserved
  ball?* This is a strictly smaller target than "some thin dumbbell forms."
- SSG-specific bias worth exploiting: `x*` pinned at `0/1` on sink-adjacent coordinates
  puts the fixed point near a face/corner of the box, and the monotone piecewise-linear
  value operator tends to make the surviving gaps *coordinate-structured* (per-coordinate
  intervals) rather than diagonal. If one can show the operator keeps the long axis in the
  *sensed coordinate/near-diagonal* subspace (where the cut shaves it) rather than the
  anti-diagonal blind cone, mean-reversion follows. **This is the most promising unexplored
  SSG-specific lever and I flag it as such — I did not prove it.**

---

## 6. The amortized reframing and the precise remaining gap

The idealized symmetric dynamics does **not** bound κ (`isoperimetry_conditioning.md`
§12), so a naive per-cut argument is hopeless; the real trajectory stays bounded because
(i) it starts isotropic (the box, a stable fixed point) and (ii) `a(v)` can *inject*
variance. §§1–5 localize the amortized hope precisely.

> **Mean-reversion, made precise.** κ can grow in a round *only* via
> `c(v_min) = 1 + a(v_min) − ρ(v_min)² < 1`, and (Cor. 2′) this needs `ρ(v_min)²` large,
> i.e. **the thin axis must be *sensed*.** Symmetrically, κ self-corrects when `v_max` is
> *sensed* (then `Δ` shaves it). So:
>
> **The single remaining gap.** Rule out that the realizable SSG trajectory keeps the top
> eigenvector of `Σ(X_t)` in the cut's **blind (anti-diagonal) cone** — while the thin
> axis is in the **sensed** subspace — for `ω(log)` consecutive rounds. Equivalently: show
> the "bad orientation" (`v_max` blind ∧ `v_min` sensed) is **non-persistent**, because the
> FW-center recomputed each round re-randomizes which `(argmax,argmin)` coordinate cells
> are active and hence which subspace is sensed. Any such non-persistence bound turns the
> intermittent per-cut shave into a bounded amortized κ.

I could neither prove non-persistence nor exhibit a realizable persistent bad orientation
(consistent with the empirics: bounded-with-drift, no blowup in-window). This is the same
`SSG ∈ P` wall — but now attached to one concrete, geometric, *measurable* event
(orientation of `v_max`/`v_min` relative to the fixed cut's sensed/blind cones), rather
than the diffuse "asymmetric repair keeps pace."

### Proposed experiment (cheap; sent to `main`)

The linchpin — "high κ ⟹ long axis *sensed* (⇒ shaved next round)" vs "high κ ⟹ long axis
*blind* (⇒ persists/compounds)" — is directly testable within the existing exact-rejection
caps by adding four columns to the `repair_measure.py` harness. Spec in the message to
`main`. If high κ is *associated with `ρ(v_max)` large* (sensed) and a κ-drop next round,
mean-reversion is real and the target is non-persistence; if high κ co-occurs with
`ρ(v_max)≈0` (blind long axis) that persists, the route is in genuine danger and that is
the counterexample shape to hunt.

---

## 7. Status ledger

- **Proved (∎):** Identity 1 / 1′ (exact per-direction variance change `δ(v)=Cov(t̄²,σ)−Cov(t̄,σ)²`
  and the T3 factor `c(v)=1+a(v)−ρ(v)²`); Lemma 2 (`ΔᵀΣ⁻¹Δ≤4`, dimension/scale-free);
  Corollary 2′ (downdate can't collapse thin axis; ASYM `a(v_min)` is the sole crux);
  the sensitivity/blind-cone structure `Δ=2Cov(w,σ)` ⟂ blind cone (§3); the reduction of
  the wall to a *sensed* dumbbell and its exclusion on coordinate axes via ball-preservation (§5).
- **Established negative:** attack #1 (clean per-cut alignment) is false-by-mechanism —
  alignment is intermittent because `v_max` can be anti-diagonal/blind (§4).
- **Open (= SSG∈P), sharpened:** bound `a(v_min)` from below over the trajectory,
  equivalently prove non-persistence of the "`v_max` blind ∧ `v_min` sensed" orientation
  under FW-recentered cone-cuts (§6). SSG lever: show the value operator keeps the long
  axis in the sensed (coordinate/near-diagonal) subspace (§5).

All of §§1–3 are pure identities/inequalities (Cauchy–Schwarz + law of total variance +
the balancedness sign trick); they need no experiment. The numerical checks requested from
`main` are (a) a validation of Identity 1 and Lemma 2 (should hold to sampling tolerance),
and (b) the mean-reversion experiment of §6.

---

## 8. Local stability of the isotropy fixed point (the rogue-ideas lead) — a symmetry reduction

Lead (rogue-ideas, via team-lead): the algorithm *starts* at the box (near-isotropic), so
perhaps only **local** stability of the shape map at isotropy is needed, not a global
bound. Model one round as `Σ ↦ F(Σ) := renorm(Σ(X∩K))` (renorm = rescale to fixed trace or
det), linearize at the fixed point, and ask whether the Jacobian is a contraction on the
κ-relevant (traceless-symmetric) subspace. This turns out to reduce **almost entirely by
symmetry**, and the reduction both corrects the premise and produces a sharp, cheap,
falsifiable target. I develop the rigorous structure here; the one open sign is a 4-number
finite difference (spec below).

### 8.1 The fixed point is *not* `I` — it is equicorrelation (∎)

The cut `g = max_i w_i + min_i w_i` is **not** `O(d)`-invariant; its symmetry group is the
coordinate-permutation group `S_d` (max/min are symmetric functions), together with the
`ρ`-antisymmetry `g(−w)=−g(w)` that swaps `K↔N`. Consequently the shape map `F` is
**`S_d`-equivariant** (`F(PΣPᵀ)=P F(Σ) Pᵀ` for permutation `P`), but **not** `O(d)`-
equivariant. So its fixed point is the most general `S_d`-invariant covariance —
**equicorrelation** `Σ* = aI + b 𝟙𝟙ᵀ`, `b≠0` in general — *not* isotropy. (This is exactly
the box→first-cut computation of `isoperimetry_conditioning.md` §2: `Σ(box∩K)=aI+b𝟙𝟙ᵀ`,
two eigenvalues, `κ→1` as `d→∞`, i.e. `b→0`.) So the premise needs correcting: linearize at
`Σ*`, and the `𝟙`-axis carries a **permanent forced anisotropy** `κ(Σ*)=(a+bd)/a` of size
`O(1)` (vanishing as `d→∞`), which is harmless (`O(1)`) but is *not* zero.

### 8.2 The Jacobian block-diagonalizes into ~4 scalars by representation theory (∎)

`J := dF|_{Σ*}` is a linear, `S_d`-equivariant map on symmetric matrices `Sym²(ℝ^d)`. By
Schur's lemma it acts as a **scalar on each isotypic component**. `Sym²(ℝ^d)` under `S_d`
(conjugation) decomposes as:
```
  diagonal part      ℝ^d        = triv ⊕ std
  off-diagonal part  span{E_ij} = triv ⊕ std ⊕ W        (E_ij=e_ieⱼᵀ+eⱼe_iᵀ, W = irrep (d−2,2))
```
So the isotypic multiplicities are: **triv** ×2, **std** ×2, **W** ×1. Hence the entire
Jacobian is described by: a 2×2 block on triv, a 2×2 block on std, and a **single scalar
`μ_W`** on `W`. Quotient out the 1-D scale direction (renorm) inside triv → the κ-relevant
spectrum of `J` is **four numbers**: `μ_triv` (1 remaining), the two eigenvalues of the std
2×2 block, and `μ_W`. **Local stability ⟺ all four have modulus `≤ 1`.** This collapses a
`d(d+1)/2`-dimensional Jacobian to 4 scalars and makes it `d`-extrapolable.

Moreover (∎): **the std and W eigenvalues are independent of the renorm choice**
(trace vs det). A traceless, non-trivial-isotypic input sources no trivial-isotypic output
(Schur), so renorm — which acts only on the trivial/scale component — contributes nothing to
first order on std/W. The dangerous eigenvalues are renorm-invariant.

### 8.3 The symmetric part gives marginal (eigenvalue = 1) std/W modes — so the drift is neutral (∎ within the symmetric model)

Write `F = F_sym + F_asym` split by the `ρ`-symmetric vs `ρ`-asymmetric part of the body.
For any **centrally symmetric** body the cut is the pure rank-1 downdate `(S)`:
`Σ(X∩K)=Σ−m_K m_Kᵀ`. At an `S_d`-invariant `Σ`, the half-mean `m_K=E[w|K]` is an
`S_d`-invariant vector, hence `m_K ∝ 𝟙`, so the downdate `m_Km_Kᵀ ∝ 𝟙𝟙ᵀ` lives **entirely
in the trivial isotypic component.** Therefore the symmetric part of `J` acts as the
identity on std and W:
> **`μ_std = μ_W = 1` exactly for the symmetric part of the map.** (∎)

So the linearized dynamics on the κ-dangerous modes (std, W) is **marginal/neutral** — no
contraction, no expansion — in the symmetric model. This is the *local* face of §12's global
"symmetric dynamics does not bound κ": at isotropy there is simply no restoring force on the
non-`𝟙` anisotropy. Its immediate, and more optimistic, consequence:

> **Reframing of "bounded-with-drift" [CORRECTED — see §13].** The observed κ-drift is
> motion along **neutral (eigenvalue-1) modes**, driven by the per-cut *asymmetric*
> fluctuation. *If* that fluctuation were mean-zero the mode would be a random walk
> (`κ ~ √t`); the sign of `F_asym`'s contribution to `μ_std, μ_W` decides expand vs
> contract. **⚠ Two corrections (advisor ruling + the §13 experiment):** (i) even a
> favourable `μ_W ≤ 1` would only **advance** the conditioning route by removing the
> κ-blowup mode — it does **not** suffice for `SSG∈P`, because "poly κ ⟹ mixing" smuggles
> convexity (a `κ≈1` ball-minus-central-slab has Cheeger `→0`); closing additionally needs
> the §11 well-roundedness bound. (ii) The mean-zero hypothesis is **empirically false**:
> §13's experiment finds the asymmetric drift is **positive** during (persistent) blind
> spells, so `κ` climbs, not `√t`. So this box's original "suffices for SSG∈P" is
> retracted; the corrected statement is in §13.

### 8.4 The dangerous modes ARE the blind cone (∎ structural)

The off-diagonal mode `E_{12}=e_1e_2ᵀ+e_2e_1ᵀ` perturbs `Σ*` so its eigenvectors tilt to
`(e_1±e_2)/√2` — a **diagonal** axis `(e_1+e_2)/√2` (sensed, §3b) and an **anti-diagonal**
axis `(e_1−e_2)/√2` (**blind**, §3). So the `W` (pure off-diagonal) component *is* the
anti-diagonal / rotation subspace the cut is blind to. §8.3's `μ_W=1` (symmetric) is exactly
the linearized statement of §3's blindness: the cut cannot, to first order, correct
anti-diagonal anisotropy. The `std` diagonal modes ("one coordinate axis longer") are
*sensed* (§3a), so there `F_asym` has a real chance of pushing `μ_std<1`. **Prediction:**
`μ_std < 1` (sensed, contracting), `μ_W ≈ 1` (blind, marginal — the drift mode); the route
lives iff `μ_W ≤ 1`.

### 8.5 The finite-difference spec (cheap, faithful, `d`-extrapolable)

The Gaussian/ellipsoid body models are **degenerate for this purpose** — they are centrally
symmetric, so `F_asym=0` and they return `μ_std=μ_W=1` trivially (§8.3). The asymmetry that
sets the sign is a **multi-cut effect** (the fixed-point body `X*` is `ρ`-asymmetric, defect
`≈0.2`, §2b of the conditioning note). So the Jacobian must be measured on the **real cut
body** via a point-cloud shear perturbation — no re-sampling, hence very cheap:

1. **One** exact-rejection sample of a near-fixed-point body: take `X_t` at a round where
   `κ≈κ(Σ*)` (a few cuts in; rejection-feasible), `N ≥ 4000` points, sign-folded about the
   FW center. Call the cloud `Y` (rows = points).
2. Whiten once: `Y ← Y·Σ_t^{-1/2}` so the working covariance is `I` (isolates the shape
   response; the ambient cut `max+min≥0` is applied in the *original* frame, so store the
   inverse map — or equivalently apply the perturbation in the whitened frame and the cut in
   the original frame). Simplest faithful variant: keep `Y` in original coords and perturb
   in original coords (below); whitening is only for reading eigenvalues.
3. For each isotypic test perturbation `H ∈ {H_triv, H_std^{diag}=e_1e_1ᵀ−e_2e_2ᵀ,
   H_off=E_{12}}` and small `ε` (try `ε=0.05, 0.02`): form the sheared cloud
   `Y_± = Y·(I ± εH)`, recompute the balanced FW center of `Y_±` (keep balanced), apply the
   cut `max_i w + min_i w ≥ 0`, take the kept sub-cloud, its covariance `Σ_±`, renorm to
   fixed det. Central difference `J[H] = (Σ_+ − Σ_−)/(2ε)`, projected to traceless.
4. **Read the four isotypic eigenvalues:** project `J[H]` onto the isotypic component of `H`
   and report the ratio (that is the Schur scalar); confirm block structure by checking the
   cross-isotypic leakage is `O(ε)` (validates §8.2). Report `μ_triv`, the std-block
   eigenvalues, and **`μ_W` (from `H_off`)** — the decisive number.
5. Vary `d ∈ {4,5,6,8}`, several instances/seeds (reuse the hard spread-`x*` SSG seeds), and
   `ε` (Richardson-extrapolate `ε→0`). Report whether any std/W eigenvalue exceeds `1`, and
   the `d`-trend of `μ_W−1` (does it approach `0⁻`, `0`, or `0⁺`?).

Cost: one rejection sample per (instance, round); everything else is linear algebra on the
cloud (shear = matmul, cut = a comparison, cov = one pass). Well within the existing caps,
and it goes to higher `d`/`N` than the trajectory experiments because there is no
per-perturbation resampling.

**What the answer decides.** `μ_std<1` and `μ_W ≤ 1` ⟹ isotropy is locally stable on sensed
modes and neutral on blind modes ⟹ κ-drift is a poly (`√t`) random walk in a basin ⟹ strong
support for the whitening route (need only that the SSG trajectory stays in the basin, §5).
`μ_W>1` (uniformly in `d`) ⟹ local *instability* on the blind mode ⟹ the route is in real
danger and `H_off` at the fixed point is the counterexample shape to grow. Either way it is
a decisive, cheap measurement of the exact quantity §8.3 isolates.

### 8.6 Status of the local-stability lead

- **Proved (∎):** fixed point is equicorrelation not `I` (§8.1); Jacobian reduces to 4
  scalars by `S_d`-isotypic block-diagonalization (§8.2); std/W eigenvalues are
  renorm-invariant (§8.2); the symmetric part gives `μ_std=μ_W=1` exactly, so the drift is
  along **neutral** modes and is therefore *a priori* poly (`√t`), not exponential, unless
  `F_asym` supplies positive drift (§8.3); the dangerous `W` mode = the §3 anti-diagonal
  blind cone (§8.4).
- **Open (the one sign):** the sign of `F_asym`'s contribution to `μ_std, μ_W` — a 4-number
  finite difference (§8.5). This is a strict, quantitative sharpening of the whole crux:
  from "is κ bounded?" to "**is `μ_W ≤ 1`?**"
- **Basin caveat (to confront, per the lead):** local stability governs a neighborhood of
  `Σ*`; the data shows the trajectory wanders (bounded-with-drift), so one must also bound
  the basin radius and argue the structured-SSG cut sequence stays inside it. §8.3's
  neutral-mode/random-walk picture is consistent with wandering *within* a basin without
  leaving it, but that containment is not proved.

---

## 9. Does FW-recentering rotate the sensed subspace toward the long axis? (angle 1 — honest negative + redirect)

Hoped mechanism (team-lead): re-centering at the new Fermat–Weber center each round rotates
the sensed subspace toward the current long axis, so a blind long axis cannot persist. **This
mechanism is false as stated, for a structural reason worth stating precisely.**

> **Observation 9.1 (∎).** The sensed/blind decomposition is **anchored to the ambient
> coordinate axes**, not to the body. The cut is `g(w)=max_i w_i + min_i w_i` with
> `w=y−c` (sign-folded); `max`/`min` are taken over the **fixed** coordinates. The FW
> center `c` enters only as a **translation** of the apex (and the sign-fold `s` is a
> discrete signed permutation — still axis-aligned). A translation of the apex does **not
> rotate** the axes over which `max`/`min` are computed.

> **Corollary 9.2 (∎).** The *exact* first-order blind cone — directions `v` with
> `v_{argmax(w)} + v_{argmin(w)} = 0` on the body's mass, generated by the anti-diagonals
> `e_i − e_j` — is **recentering-invariant**. (Its generators depend only on which
> `(argmax,argmin)` cells carry mass, and the cell *labels* are axis-anchored.) So if the
> top eigenvector `v_max` of `Σ(X_t)` lies in this axis-anchored anti-diagonal cone,
> **no choice of FW center can move it into the sensed cone.** Recentering can only
> reweight the mass over the `(argmax,argmin)` cells (a soft change to the sensitivity
> *profile* `ρ(v)`), it cannot rotate the blind cone off `v_max`.

What recentering *does* change, per round, is (i) the mass distribution over cells and (ii),
via the algorithm's choice of sign pattern `s` and active set `S` (driven by the SSG map
toward `x*`), the **discrete octahedral orientation** of the cut among the `2^d` folds. So
any true non-persistence cannot be a continuous "rotation toward the long axis"; it must come
from this **discrete reselection**, which is governed by the value operator, not by the cut
geometry.

> **Redirect 9.3.** Angle 1 collapses into the SSG-structure lever (§5): the top eigenvector
> of `Σ(X_t)` is a direction in *ambient* space, the axes are fixed, and the cut can shave
> `v_max` iff `v_max` is *not* in the (fixed) anti-diagonal cone. So the non-persistence
> question is precisely: **does the SSG value operator prevent `v_max` from persistently
> occupying an anti-diagonal orientation relative to the fixed coordinate axes?** This is a
> statement about the *operator*, not the cut. (Consistency check: the box start is
> axis-aligned/isotropic and the first cut creates *diagonal* `𝟙`-anisotropy — a **sensed**
> mode, not anti-diagonal — so the trajectory does not begin in the blind cone; whether SSG
> cuts drive it there and keep it there is exactly what the queued `ρ(v_max)`-vs-κ experiment
> measures.)

This kills the "recentering rotates sensing" sub-idea cleanly and re-points at the operator.

## 10. Can ball-preservation be strengthened to an ε-net forbidding diagonal dumbbells? (angle 2 — the net is free; the gap is the volume ratio)

Hoped mechanism: extend ball-preservation from coordinate axes to an ε-net of directions to
forbid dumbbells along diagonals too. **The net is unnecessary — a single contained `ℓ∞`
ball already forbids central dumbbell gaps in *every* direction at once — but doing so
exposes that the true missing ingredient is a volume-ratio bound, not directional coverage.**

> **Lemma 10.1 (central-bump lemma, ∎).** Let `B = B_∞(x*,ρ) ⊆ X` (ball-preservation). For
> every unit `u`, the `u`-marginal of `X` **dominates a centered, symmetric, log-concave
> (unimodal) bump** of total mass `vol(B)/vol(X)`, peaked at `u·x*`. Concretely the bump is
> the law of `Σ_i u_i U_i`, `U_i ~ Unif[−ρ,ρ]` i.i.d. (the pushforward of uniform-on-`B`
> under `y↦u·y`), which is log-concave and symmetric about `0`.
>
> *Proof.* `B⊆X`, both carry uniform density `1/vol(X)` on `B`; the `u`-marginal of `X` is
> `≥` the `u`-pushforward of `Leb|_B / vol(X)`, which is `vol(B)/vol(X)` times the density of
> `Σ_i u_i U_i`. Independent-uniform sums are log-concave and symmetric. ∎

Two consequences:

- **The ε-net is redundant (∎).** A single convex, centrally-located `B` projects to a
  *central, unimodal* bump in **every** direction simultaneously — convexity gives the whole
  net for free. A dumbbell along `u` has its low-mass valley in the *center* of the
  `u`-marginal, which is exactly where Lemma 10.1's bump is *peaked*: so a contained ball
  fills a dumbbell's valley most strongly where it matters. No directional net is needed.
- **But protection is only at relative mass `vol(B)/vol(X)`.** The bump's contribution to the
  central valley is `vol(B)/vol(X)` (up to the `O(1)` peak-concentration factor `≈1/ρ_u`,
  `ρ_u = ρ‖u‖_1` the ball's `u`-width). So Lemma 10.1 forbids a dumbbell along `u` **only at
  scales `√Var(u·y) ≲ ρ_u`** (thin axis narrower than the ball reaches) **and only with
  relative-mass floor `vol(B)/vol(X)`**. When `vol(X) ≫ vol(B)` the floor is exponentially
  small and the dumbbell (lobes beyond the ball) survives — exactly the `§4` obstruction of
  `isoperimetry_conditioning.md`.

> **Redirect 10.2.** Angle 2 reduces to a **well-roundedness / volume-ratio** bound
> `vol(X_t) ≤ C^{o(d)}·vol(B_∞(x*,ρ_t))` (equivalently the ball is a `(1+o(1))^{-d}`
> fraction), which would upgrade Lemma 10.1's floor to `1/poly` and forbid dumbbells at
> *all* sensed scales. This is the missing ingredient — **not** directional coverage. It is
> the same well-roundedness wall flagged in `§4` of the conditioning note; the value of
> Angle 2 is proving the net is a distraction and isolating the volume ratio as the sole
> residual quantity. (SSG note: with `x*` pinned at a box corner/face, `B_∞(x*,ρ)` is
> clipped to a corner box `∏_i[x*_i, x*_i+ρ]` of side `ρ` — still a full-dimensional
> contained box, so Lemma 10.1 stands with `x*` at the corner; the volume-ratio question is
> unchanged.)

## 11. Consolidated status of the non-persistence attack (§§9–10)

Both angles the lead proposed resolve to **structural negatives that sharpen the target**:

- **Angle 1 (recentering rotates sensing): false.** The blind cone is axis-anchored and
  recentering-invariant (9.1–9.2); non-persistence must come from the **SSG value operator**
  keeping `v_max` out of the fixed anti-diagonal cone (9.3) — the same lever as §5.
- **Angle 2 (ε-net for diagonal dumbbells): the net is free from convexity (Lemma 10.1),
  but insufficient.** The residual is a **volume-ratio / well-roundedness** bound (10.2),
  the same wall as `conditioning §4`.

Net effect: the two independent leads **converge on the same two irreducible ingredients**
already isolated — (a) the SSG operator's control of `v_max`'s orientation (→ the queued
experiment and §8's `μ_W ≤ 1` question), and (b) a well-roundedness volume-ratio bound. No
new wall; two dead ends removed; the live theoretical target remains `μ_W ≤ 1` (§8) plus the
SSG-operator orientation control (§5, §9.3).

---

## 12. The volume-ratio ingredient (b), pushed on paper — reduction, and why it is not the poly route

Target (team-lead): bound `vol(X_t) ≤ (1+o(1))^d · vol(B_∞(x*, r/2))`, using ball-preservation
for the lower bound and the halving accounting for the upper. I develop it and reach an honest
verdict: **(b) reduces to a clean inradius statement, but is strictly weaker than κ and cannot
by itself give poly mixing (non-convexity caps it at exponential); it is governed by the same
sign-pattern combinatorics as (a).**

### 12.1 The exact reduction (∎)

Balanced cuts halve mass exactly: `vol(X_r) = μ(K)·vol(X_{r-1}) = ½vol(X_{r-1})`, so
```
vol(X_t) = 2^{-t}·vol([0,1]^d) = 2^{-t}   (exactly).
```
The inball `B_∞(x*,ρ_t) ⊆ X_t ⊆` (a `ℓ∞`-box of side `D_t := diam_∞(X_t)`) gives
`(2ρ_t)^d ≤ vol(X_t) ≤ D_t^d`, i.e. the **geometric-mean scale is pinned**:
```
2ρ_t ≤ 2^{-t/d} ≤ D_t     (always, purely from vol = 2^{-t}).
```
Therefore, with `ρ_t = r_t/2`,
> **Reduction 12.1.** `vol(X_t)/vol(B_∞(x*,ρ_t)) = (2^{-t/d}/2ρ_t)^d ≥ 1`, and it is `≤ C^d`
> **iff `ρ_t ≥ 2^{-t/d}/(2C)`** — i.e. iff the `ℓ∞`-**inradius achieves a constant fraction of
> the geometric-mean scale `2^{-t/d}`** (the body is "`ℓ∞`-fat"). This is a pure statement
> about the inradius; `vol = 2^{-t}` does all the accounting.

### 12.2 (b) is a *width* bound, strictly weaker than κ, and insufficient alone (∎)

The volume ratio controls **inradius vs geometric mean** only — a *width* anisotropy. Two
rigorous gaps to the poly-mixing goal:

1. **It does not bound the diameter/κ.** A **ball + thin spike** — `X = B_∞(x*,R) ∪` (a needle
   of length `L≫R`, cross-section `w^{d-1}`) — has `vol(B_∞(x*,R/2))` a constant fraction of
   `vol(X)`, so **bounded volume ratio**, yet its variance along the spike is
   `≳ (w^{d-1}L/vol)·L²`, making **κ (and the spike-neck Cheeger) unbounded.** So bounded (b)
   `⇏` bounded κ `⇏` mixing.
2. **Even two-sided width bounds don't give poly Cheeger for non-convex bodies.** Take
   **two boxes joined by a thin corridor** — `X = B_∞(p_1,R) ∪` corridor(`w^{d-1}×L`) `∪
   B_∞(p_2,R)`, `x*=p_1`. Then `B_∞(x*,R/2) ⊆` box 1, so `vol(X)/vol(B) ≈ 2 = O(1)`, but the
   corridor is a bottleneck of conductance `≈ (w/R)^{d-1}/R → 0`. **`O(1)` volume ratio,
   exp-small Cheeger, non-convex.** The `x*`-ball certifies its own lobe is fat and says
   nothing about a distant lobe. This is the `§4`/`§10.2` obstruction, made into a crisp
   counterexample.

The root cause: for a **convex** body a geometric-mean-scale inball already forces good
mixing (KLS/Cheeger); for a **non-convex** body it does not — there is no KLS bootstrap. So
the central-bump lemma (10.1) converts a `C^d` volume ratio only into conductance
`≥ vol(B)/vol(X) = C^{-d}` — **exponentially small.** (b) rigorously forbids only the
`x*`-central dumbbell class and gives at best exponential mixing.

> **Verdict 12.2.** Ingredient (b) is not an independent poly-sufficient ingredient. It is a
> *width* bound (weaker than the *variance* bound κ), and non-convexity caps what it can buy
> at **exponential** mixing. Upgrading it to poly requires a genuine isoperimetric inequality
> for the (non-convex) realizable `X_t` — i.e. **the Open Lemma itself.** So (b) does not
> escape the wall; it reconverges on it (consistent with `summary §4`).

### 12.3 What (b) *does* give, and the sign-pattern unification (∎ / redirect)

- **Star/flat-gap regime (consistency, ∎).** There CLY's diameter bookkeeping (`hitrun.md`
  Lemma 3: the shifted-base cut keeps an `ℓ∞`-ball about `x*`, `diam(X_t) ≤ (1−Ω(1/d))^t`)
  charges the volume-halving **evenly across the `d` coordinate directions**, so
  `ρ_t = Θ(2^{-t/d})` and **`vol ratio ≤ C^d`.** But this regime is exactly-samplable
  already (Theorem A), so the bound is a consistency check, not new power. (b) **collapses**
  precisely when the halving stops being evenly charged — when a cut concentrates the
  volume-halving on the current *thinnest* coordinate, dropping `ρ_t` below `2^{-t/d}`.
- **Sign-pattern unification (redirect).** `vol(X_t)=2^{-t}` is scale(`δ`)-free, and the (b)
  ratio `ρ_t/2^{-t/d}` is a pure geometric functional of `X_t`, which — per lambdamin's
  condition-transfer finding (κ, h byte-identical across `57×` different `δ` at fixed sign
  history) — **is fixed by the sign-pattern (orthant/strategy) history.** The (b)-collapse
  event ("a cut whose orthant `s^r` concentrates the halving on the thinnest axis") is the
  **same combinatorial object** as the (a)-collapse event ("`v_max` driven into the fixed
  anti-diagonal blind cone", §9.3). So (a) and (b) do **not** decouple into
  "experiment vs paper" — they are two readouts of one object, the **sign/strategy
  sequence** — matching the conditioning↔policy convergence the team-lead flagged.

### 12.4 Honest bottom line for (b)

`vol(X_t)=2^{-t}` makes (b) exactly an `ℓ∞`-inradius bound `ρ_t ≳ 2^{-t/d}` (12.1). But (b)
is *width*-anisotropy — weaker than κ, capped at exponential mixing by non-convexity (12.2),
and a functional of the same sign-pattern dynamics as (a) (12.3). **So the paper-track on (b)
does not open a new route.** The load-bearing quantity remains κ (ingredient a / `μ_W ≤ 1`,
§8) together with genuine isoperimetry, both now seen to live on the **sign-pattern /
strategy combinatorics** — which is where the conditioning and policy routes meet, and the
sharpest place to point the next theoretical push.
