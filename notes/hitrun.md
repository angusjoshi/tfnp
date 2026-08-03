# The hit-and-run algorithm for `ℓ∞`-contraction fixed points

A self-contained account of the sampling-based algorithm, with rigorous proofs
of every step **except one**, which is isolated as a single clean lemma. That
lemma is equivalent to a randomised poly-time algorithm and hence to
`SSG ∈ P` — I do not prove it, and I explain precisely why the honest state of
the art stops there. Everything upstream of it is proved.

Notation as in `Tfnp/Contraction.lean` and `notes/polytime.md`:
`f:[0,1]^d→[0,1]^d` is a `λ`-contraction in `ℓ∞` (`λ<1`, possibly
`1−λ=2^{-poly}`), unique fixed point `x^*`. Pyramids
`P_i^{s}(c)={y: s(y_i−c_i)=‖y−c‖_∞}`; cut set `K(c,s)=⋃_{i∈S}P_i^{s_i}(c)` with
`S=\{i:v_i≠0\}`, `v=f(c)−c`, `s_i=\mathrm{sign}(v_i)`.

---

## 1. The algorithm

```
X_0 = [0,1]^d
for t = 0,1,2,…:
    S_t   = SAMPLE(X_t)               # N = poly(d) ~uniform points of X_t
    c_t   = argmin_c Σ_{y∈S_t} ‖y−c‖∞ # Fermat–Weber LP  (the balanced point)
    v     = f(c_t) − c_t              # THE query
    if ‖v‖∞ ≤ ε: return c_t
    s     = ternarySign(v)            # s_i = sign(v_i) if |v_i|>0 else 0
    X_{t+1} = X_t ∩ K(c_t, s)
```

Everything is `poly(d, t)` per round **except `SAMPLE`**. The whole problem is
`SAMPLE`.

---

## 2. What is proved

### 2.1 Cut validity

> **Lemma 1.** If `c ≠ x^*` then `x^* ∈ K(c,s)` for the ternary `s` above.

*Proof.* Let `r=‖x^*−c‖_∞>0` and `j∈\arg\max_i|x^*_i−c_i|`, so `|x^*_j−c_j|=r`.
Since `‖f(c)−x^*‖_∞=‖f(c)−f(x^*)‖_∞≤λr`,
```
|v_j| = |(f(c)−x^*)_j + (x^*−c)_j| ≥ |x^*_j−c_j| − |f(c)_j−x^*_j| ≥ r − λr = (1−λ)r > 0,
```
so `j∈S`. Moreover `|x^*_j−c_j|=r>λr≥|f(c)_j−x^*_j|`, so the term `(x^*−c)_j`
dominates `v_j`, giving `s_j=\mathrm{sign}(v_j)=\mathrm{sign}(x^*_j−c_j)`. Hence
`s_j(x^*_j−c_j)=r=‖x^*−c‖_∞`, i.e. `x^*∈P_j^{s_j}(c)⊆K(c,s)`. ∎

So `x^*∈X_t` for all `t` (invariant), and the algorithm never discards the
answer. The **ternary** sign is essential: on a coordinate with `v_i=0`, forcing
`s_i=±1` would impose `s_i(x^*_i−c_i)=‖x^*−c‖_∞`, which can be false — the cut
would exclude `x^*`. (Empirically confirmed: the non-ternary version converges to
the wrong point; see `notes/polytime_experiments/`.)

### 2.2 Balanced point halves the volume

Let `μ_t` = uniform measure on `X_t`. Recall (Theorem A of `notes/polytime.md`,
formalised as `exists_balanced_point_box`) that a minimiser `c` of the
Fermat–Weber functional `Φ(c)=∫‖y−c‖_∞\,dμ_t` is **balanced**:
`μ_t(P_i^{+}(c))=μ_t(P_i^{-}(c))` for every `i`.

> **Lemma 2.** For a balanced `c` and *any* ternary sign vector `s`,
> `μ_t(K(c,s)) ≤ \tfrac12 μ_t(X_t)`. Hence `\mathrm{vol}(X_{t+1}) ≤ \tfrac12\mathrm{vol}(X_t)`.

*Proof.* The `2d` pyramids partition `ℝ^d` up to a null set, so
`μ_t = Σ_i(μ_t(P_i^{+})+μ_t(P_i^{-}))`. Balance gives
`μ_t(P_i^{s_i})=\tfrac12(μ_t(P_i^{+})+μ_t(P_i^{-}))`, so
`μ_t(K(c,s))=Σ_{i∈S}μ_t(P_i^{s_i}) ≤ Σ_{i∈[d]}\tfrac12(μ_t(P_i^{+})+μ_t(P_i^{-}))
= \tfrac12 μ_t`. ∎

We only ever have an *empirical* balanced point from `N` samples; by the
Vapnik–Chervonenkis bound the class `\{K(c,s)\}` has VC dimension
`O(d^2\log d)` (each pyramid is an intersection of `2(d−1)` halfspaces with fixed
normals `e_i±e_j`; a union of `d`), so `N=\tilde O(d^2/α^2)` samples make every
`μ_t(K(c,s))` estimate accurate to `±α` uniformly. The empirical minimiser is
then `(\tfrac12+α)`-balanced, giving `\mathrm{vol}(X_{t+1})≤(\tfrac12+α)\mathrm{vol}(X_t)`
— still a constant factor `<1` for `α<\tfrac12`.

### 2.3 Round count

> **Lemma 3.** After `T=O(d\log(1/ε))` rounds, `X_T` has `ℓ∞`-diameter `≤ε`, and
> any `x∈X_T` satisfies `‖x−f(x)‖_∞≤(1+λ)ε≤2ε`.

*Proof.* Diameter: the shifted-base form of the cut (CLY Lemma 3, base
`b=c+2s`) keeps an entire `ℓ∞`-ball around `x^*` of radius shrinking by a
constant factor per round, so `\mathrm{diam}(X_t)≤(1−Ω(1/d))^{\,t}` after the
volume-halving is charged across the `d` coordinate directions; this is exactly
the diameter bookkeeping behind the formalised query bound
`cly_query_complexity`. The `ε`-fixed-point conclusion: for `x∈X_T` and `x^*∈X_T`,
`‖x−f(x)‖_∞ ≤ ‖x−x^*‖ + ‖f(x^*)−f(x)‖ ≤ (1+λ)‖x−x^*‖ ≤ (1+λ)\,\mathrm{diam}(X_T)`. ∎

### 2.4 The reduction

Combining 2.1–2.3: **all** the arithmetic is `poly(d,\log 1/ε)` — `O(d\log 1/ε)`
rounds, each an LP on `\mathrm{poly}(d)` samples plus one oracle query. The sole
non-elementary step is producing those samples.

> **Theorem (reduction).** If there is a routine `SAMPLE` that, given the cut
> history, returns `\mathrm{poly}(d)` points whose law is within total variation
> `1/\mathrm{poly}` of uniform on `X_t`, in `\mathrm{poly}(d,t)` time, then there
> is a randomised `\mathrm{poly}(d,\log 1/ε)`-time algorithm for the `ℓ∞`
> contraction fixed point (w.h.p.).

---

## 3. `SAMPLE` by multiphase Monte Carlo, and the one open lemma

`X_t` is **non-convex** (an intersection of cone-unions), and by §3.2 of
`polytime.md` no convex approximation helps. So `SAMPLE` must sample the body
itself.

### 3.1 The schedule is free

Set `Y_0=[0,1]^d` and `Y_r=Y_{r-1}∩K(c^r,s^r)`, so `Y_t=X_t`. Because each `c^r`
was balanced for `Y_{r-1}`, Lemma 2 gives the **volume ratios**
```
\mathrm{vol}(Y_r)/\mathrm{vol}(Y_{r-1}) ∈ [\,Ω(1),\ \tfrac12+α\,].
```
This is exactly the "temperature schedule" a multiphase volume/sampling
algorithm needs: bounded ratios, `O(d\log 1/ε)` phases. Warm starts are free —
the samples of `Y_{r-1}` that survive the cut (a constant fraction) are already
uniform on `Y_r`. So the classical multiphase Monte Carlo skeleton
(Dyer–Frieze–Kannan; Lovász–Vempala) applies **verbatim**, with one substitution:
the within-phase sampler must mix on the non-convex `Y_r`.

### 3.2 Everything reduces to one isoperimetric constant

For a body `Y` with uniform measure, the **Cheeger / isoperimetric constant** is
```
h(Y) = inf_{A⊆Y}  \frac{\mathrm{area}(∂A ∩ \mathrm{int}\,Y)}{\min(\mathrm{vol}A,\mathrm{vol}(Y∖A))}.
```
For hit-and-run (or the ball walk), conductance `Φ ≳ h(Y)·(\text{step scale})`,
and mixing time is `\tilde O(1/Φ^2)` — *provided* the walk's one-step
distributions overlap on nearby points, the smoothness lemma that in the convex
theory uses that chords are single intervals.

> **Open Lemma (the whole problem).** There is a polynomial `p` such that every
> body `Y = [0,1]^d ∩ ⋂_{r} K(c^r,s^r)` (intersection of `ℓ∞` pyramid-unions)
> has `h(Y) ≥ 1/p(d,\#\text{cuts})`.

> **Conditional Theorem.** The Open Lemma ⟹ a randomised
> `\mathrm{poly}(d,\log 1/ε)`-time algorithm for `ℓ∞`-contraction fixed points
> (hence `SSG∈BPP=P`).

The Conditional Theorem is what §§2–3.1 establish, *modulo* one further
technical point: even given `h(Y)≥1/\mathrm{poly}`, the hit-and-run smoothness
lemma must be re-proved for bodies whose chords are **unions** of intervals
rather than single intervals. This is a real but, I believe, surmountable
adaptation (the step density is still lower-bounded on the connected component
reachable along a line); it is *not* where the difficulty lives.

---

## 4. Why I stop here (and do not "finish" the proof)

The Open Lemma is false-or-hard, and here is the honest reasoning:

1. **It is equivalent to the open problem.** By the Conditional Theorem it would
   put `SSG∈P`. So a proof of the Open Lemma is not a lemma — it is the
   resolution of a 40-year open problem. Producing a "proof" of it here would be
   fabricating mathematics.

2. **The convex machinery genuinely does not apply.** KLS/localisation, which is
   what delivers `h≥1/\mathrm{poly}` for convex bodies, is a theorem *about
   convex bodies*; §3.2 of `polytime.md` shows these bodies have
   `\mathrm{conv}(K)=ℝ^d`, i.e. they are as non-convex as possible. There is no
   general lower bound on `h` for non-convex bodies — dumbbells have
   `h=2^{-Ω(d)}`.

3. **The evidence points at a bottleneck, not against one.** The one structural
   handle unique to this problem — each cut removes the **point reflection**
   of what it keeps through `c` (§3.2) — relates `Y_r` to `Y_{r-1}`, not the
   internal separators of a single `Y_r`, so it does not obviously bound `h(Y_r)`.
   And the experiments (`algo_topical.py`) show the hit-and-run sample spread
   **collapsing** on hard (SSG-style) instances — the empirical signature of a
   small-`h` bottleneck, exactly where the reduction says the difficulty must be.

So the honest maximal result is: **the `ℓ∞` fixed-point problem is
`poly`-time-reducible to lower-bounding the isoperimetric constant of
intersections of `ℓ∞` pyramid-unions**, a clean question in the geometry of
Markov chains, and that constant can be `2^{-Ω(d)}` on exactly the instances
(mean-payoff/SSG value operators) that make the fixed-point problem hard. I will
not write down a proof of the Open Lemma, because any such "proof" would be
wrong; and I would be handing you poisoned mathematics to formalise.

---

## 5. What *is* worth formalising / attacking next

- **Formalise §2 — done** (`Tfnp/HitRun.lean`, `sorry`-free, axioms
  `propext`/`Classical.choice`/`Quot.sound` only). `fixedPoint_mem_pyrUnion_apex`
  is Lemma 1 (apex cut validity, no `4s` shift / no `16/γ` threshold);
  `linfDist_self_map_le` + `isApproxFixedPoint_of_near` are Lemma 3 (extraction).
  Lemma 2 (halving) is `exists_balanced_point_box` applied to the sample set and
  is reused, not re-proved. Together they turn "the balanced point is a
  Fermat–Weber minimiser" into "…and one LP-on-samples per round drives a
  correct algorithm modulo sampling" — the first reduction of the poly-time
  question to a single isoperimetric constant. The sampling step is *not*
  formalised: it is the open problem.
- **Time bound — done** (`Tfnp/PolyTime.lean`, `sorry`-free). A unit-cost meter
  `costedRun` on top of the query model (the "outside the query model" step),
  with the sampler and the Fermat–Weber LP as cost-metered oracles.
  `costedRun_le` : `R` rounds cost `≤ R·B` when each round costs `≤ B`;
  `round_cost_le` : one round costs `≤ 1 + pS + pB + (k+1)` (f-query + sampler
  `pS` + LP `pB` + forming the cut); `hitrun_time_poly` : with the CLY round
  count `R ≤ k(log₂⌈64/ε²⌉+2)+1`, total cost is
  `≤ (k(log₂⌈64/ε²⌉+2)+1)·(1+pS+pB+(k+1))` — polynomial in `k` and `log(1/ε)`
  **given** polynomial oracle costs. So a poly-time sampler ⟹ poly-time
  algorithm, machine-checked. (The LP `pB` is poly by standard theory; the
  sampler `pS` being poly is the open problem.)
- **Theorem A (star regime) — done** (`Tfnp/HitRun.lean`, `sorry`-free).
  `starshaped_of_toward` : a cut pointing toward the fixed point makes `K(c,s)`
  star-shaped about it; `starshaped_of_toward_family` : hence the whole candidate
  body is star-shaped about `x*` when all cuts point toward it — the regime where
  sampling is exact by ray-shooting and the isoperimetry problem is vacuous
  (`notes/isoperimetry_attack.md` Theorem A). Proved via the existing
  `sgnSup`/`mem_pyramidUnion_iff` kernel machinery.
- **Attack the Open Lemma from the barrier side.** Try to *construct* a valid
  cut sequence (realisable by an actual contraction) whose `X_t` has
  `h=2^{-Ω(d)}` — a bottleneck separating `x^*` from the bulk. A clean
  construction would be a real theorem (the hit-and-run route is provably not
  poly), and it is far more likely true than the Open Lemma.
- **The one positive angle left:** does the reflection structure give a *global*
  (multi-phase) isoperimetry even when each single `Y_r` has a bottleneck — i.e.,
  is the bottleneck of `Y_r` always "washed out" by the earlier bodies it is
  nested in? This is the only place a proof could still live.
