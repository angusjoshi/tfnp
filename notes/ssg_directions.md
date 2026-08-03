# Established routes to SSG ∈ P, and where our geometry can bridge

A prioritised map of the *known* attack routes on Simple Stochastic Games (SSG),
each with best-known result, the barrier, and — the deliverable — whether our
`ℓ∞`-contraction / balanced-point / star-regime / scale-free-`κ` machinery can
connect to it. Read alongside `notes/isoperimetry_summary.md` (the wall),
`notes/polytime.md` (balanced point = LP; the reduction to sampling),
`notes/hitrun.md` (the Open Lemma), `notes/repair_attack.md` (the `κ` trajectory).

Convention: our "machinery" = the CLY pipeline recast as a **value-space
cutting-plane method** — maintain `X_t = box ∩ ⋂_r K(c^r,s^r)` in value space
`[0,1]^d` (`d` = #vertices), cut at Fermat–Weber balanced centers (an LP), and
the whole open problem is a near-uniform sampler for the non-convex `X_t`
(⟺ isoperimetry `h(X_t) ≥ 1/poly` ⟺ geometric condition number `κ(X_t) ≤ poly`).

---

## 0. The one-paragraph headline (the single most promising bridge)

Every classical route lives in **strategy space** `{0,1}^n` (policy iteration,
USO, P-LCP, random-facet). Our method lives in **value space** `[0,1]^d`. This is
not cosmetic: it means the strongest lower bounds — Friedmann's exponential bound
for strategy improvement, and Christ–Yannakakis's proof that Howard's policy
iteration is **not** smoothed-polynomial on *stochastic* mean-payoff — are bounds
against strategy-space dynamics and **say nothing about our method.** Meanwhile
the best *positive* recent result, Boros–Manthey et al.'s smoothed-polynomial
algorithm (ICALP'24), turns on a **condition number** = value/valuation
separation `δ`, and holds only for **deterministic** games (it dies on stochastic
ones, Christ–Yannakakis). Our `κ(X_t)` is *also* a condition number, but a
**geometric one in value space**. 

> **The bridge (§7):** prove that the game's value-separation gap `δ` controls the
> geometry of `X_t` — `δ ≥ 1/poly ⟹ κ(X_t) ≤ poly` (equiv. `h(X_t) ≥ 1/poly`).
> This would (a) *recover* smoothed-poly and the few-random-vertices and
> ergodic/bounded-return tractable regimes through our sampler, and (b) — because
> our method is value-space — potentially do so for **stochastic** games, exactly
> where the strategy-space smoothed result provably fails. That asymmetry is the
> reason to prefer this bridge over all others below.

---

## 1. Complexity placement (route 4) — what it buys and forbids

| class | who | what it says |
|---|---|---|
| **NP ∩ coNP** | Condon 1992 | SSG value decision is in NP∩coNP → **not NP-hard unless NP=coNP**. So SSG is a "well-behaved" total problem; a poly algorithm is plausible. |
| **UP ∩ coUP** | Jurdziński '98 (parity, mean-payoff) | Unique certificates. SSG inherits the flavour via UEOPL uniqueness below. |
| **PPAD, PLS, CLS=PPAD∩PLS** | Daskalakis–Papadimitriou; Fearnley–Goldberg–Hollender–Savani STOC'21 (CLS=PPAD∩PLS) | SSG search is total; in PPAD (Brouwer/value fixpoint) *and* PLS (policy iteration = local search) ⟹ in **CLS**. |
| **UEOPL** (⊆ CLS ⊆ TFNP) | Fearnley–Gordon–Savani–Sørensen ICALP'19 (arXiv 1811.03841) | **Parity, mean-payoff, discounted, AND simple stochastic games all lie in UEOPL** — together with P-matrix LCP, USO, and *fixpoints of piecewise-linear contractions*. This is the tightest home and the one that touches us directly. |

**What this buys us.** UEOPL = "there is a **unique line** with a monotone
**potential**, and following it solves the problem." Our fixpoint problem
(`ℓ∞`-contraction) is *literally one of the named UEOPL problems*. So there
provably exists a potential-guided unique path to `x*`; our balanced-cut sequence
is one instantiation of "line following," and UEOPL membership is a certificate
that the total-search structure we exploit (invariant `x*∈X_t`, monotone volume
decrease) is real, not accidental.

**What it forbids / warns.** UEOPL-hardness of any of these games is open but
suspected; if SSG were UEOPL-complete, a poly algorithm would collapse USO and
P-LCP too — a *very* strong statement. So a poly SSG algorithm should be expected
to **use SSG-specific structure** (stochasticity, the value operator), not solve
UEOPL wholesale. Our machinery does use specifics (the `ℓ∞` pyramid geometry of
the *value* operator), which is the right instinct.

Refs: Condon, *The complexity of stochastic games*, Inf.&Comp. 1992;
Fearnley–Goldberg–Hollender–Savani, *The Complexity of Gradient Descent:
CLS=PPAD∩PLS*, STOC'21; Fearnley–Gordon–Savani–Sørensen, *Unique End of Potential
Line*, ICALP'19 / JCSS (https://arxiv.org/pdf/1811.03841).

---

## 2. Reduction chain & poly-time status (route 3)

The classical chain, all poly-time reductions, **none of the two-player links
known poly**:

```
parity  ≤ₚ  mean-payoff  ≤ₚ  discounted  ≤ₚ  simple stochastic
(Puri; Zwick–Paterson; Andersson–Miltersen 2009; and 2025's direct
 stochastic-parity → SSG, arXiv 2506.06223)
```

What is actually poly / tractable, and the lift question:

- **Deterministic mean-payoff, ONE player (a single graph / MDP-free): poly.**
  Karp's minimum-mean-cycle, `O(nm)` (Karp 1978). This is the "deterministic
  mean-payoff IS poly" fact in the brief. **Lift?** It is the *0-player* case;
  the two-player min–max destroys the single-cycle structure. Our analogue: the
  0-player case is `X_t` **convex** (one player ⟹ the value operator is affine on
  each region, cuts become halfspaces) — exactly our `d≤2` / Corollary-C regime
  where ellipsoid already wins. So Karp-poly ↔ our convex regime; the lift barrier
  is identical (the min–max makes the union genuinely non-convex, `conv K = ℝ^d`).
- **Two-player deterministic mean-payoff: pseudo-poly**, `O(n³·m·W)` (Zwick–Paterson
  1996), `W` = max weight. Poly iff weights unary/small. Decision ∈ NP∩coNP.
- **Discounted, FIXED discount `λ`: poly** by value iteration (contraction rate
  `1−λ` constant). The hardness is `λ = 1 − 2^{−poly}`. **This is precisely our
  regime and our selling point:** our empirics show geometric progress with a rate
  **independent of `λ`** (`algo_linear.py`; identical trace at `λ=0.9995` and
  `1−10⁻⁷`), i.e. the machinery is built to survive exactly the `1−λ=2^{−poly}`
  blow-up that kills value iteration and that the reductions produce.

**Our connection to route 3.** We do not go *through* the chain; we sit at its
top (SSG) via Condon's reduction SSG → `ℓ∞`-contraction, `λ=1−2^{−poly}`,
`ε=2^{−poly}` (`polytime.md` §0). The value of route 3 to us is diagnostic: the
subclasses that *are* poly (0-player/Karp; fixed discount) map exactly to the
regimes where our body is convex or our rate is `λ`-free. The wall is the same
one everywhere: two-player min–max ⟹ non-convex `X_t`.

---

## 3. Strategy / policy improvement (route 1)

**Best-known.** Hoffman–Karp policy iteration (1966) → Condon's variants for SSG.
Ludwig 1995 (*A subexponential randomized algorithm for SSG*, Inf.&Comp.):
**`2^{O(√n)}` expected**, the long-standing SSG record, via a Kalai / Matoušek–
Sharir–Welzl LP-type random-facet walk on the strategy hypercube. Björklund–
Vorobyov and Halman extended subexponential LP-type bounds to mean-payoff. Recent
constant-factor/derandomisation refinements (Auger–Coucheney–Strozecki, STACS'19,
Bland's rule; arXiv 2607.06334 random-action-removal 2026).

**Barrier — decisive, and it is why we should not chase this route directly:**
- Friedmann 2009 (*Exponential lower bounds for policy iteration*, arXiv 1003.3418):
  **exponential** lower bounds for the two standard deterministic strategy-
  improvement rules, on **all four** game types.
- Friedmann–Hansen–Zwick, SODA'11 / STOC'11: **subexponential `2^{Ω(√n)}`** lower
  bounds for **Random-Facet** and Random-Edge — i.e. Ludwig's `2^{O(√n)}` is
  essentially tight for this family; the random-facet approach *cannot* be pushed
  to poly.
- Fearnley 2010: exponential lower bound for Howard's PI on MDPs.

**Connection to us / verdict.** Strategy improvement is a **strategy-space** local
search; the above are all strategy-space lower bounds. Our method is
**value-space** and is *not* a member of this family, so **none of these bounds
apply to it** — this is a genuine, citable reason our route is not already dead.
Do **not** try to make policy iteration poly for our encoding; do use its lower
bounds as the argument for why value-space cutting is worth pursuing. (Our
balanced Fermat–Weber center is not a strategy pivot; it is a geometric
centerpoint of the value candidate set.)

---

## 4. LP / LCP / USO formulation (route 2)

**Best-known / structure.**
- **Discounted games = P-matrix LCP** (Jurdziński–Savani, CiE'08): the values of a
  binary discounted game are the solution of an LCP whose matrix is a **P-matrix**,
  with explicit data from the graph/discount/rewards. The LCP's induced **USO of
  the cube coincides with the strategy-valuation USO** of the game.
- **USO of cubes** (Szabó–Welzl; Gärtner): finding the sink solves the game; best
  USO sink-finding is `2^{O(√n)}` (Fibonacci seesaw etc.), matching Ludwig.
- **UEOPL** ties P-LCP + USO + the four games + PL-contraction fixpoints together
  (§1). ICALP'24 "*Two choices are enough for P-LCPs, USOs*" sharpens the P-LCP/USO
  frontier.

**Barrier.** P-matrix LCP has **no known poly algorithm** (it is in UEOPL, tightly
tied to USO). Grid/USO structure gives subexponential, not poly. A poly P-LCP
solver would be a major independent breakthrough.

**Connection to us — two links, one useful.**
1. *USO/P-LCP is strategy-space (cube `{0,1}^n`); our `X_t` is value-space
   (`[0,1]^d`).* They are different-parameter (`n` edges vs `d` vertices) and
   dual-flavoured; there is no clean direct identification, and the USO record is
   the same `2^{O(√n)}` wall.
2. **The useful link: our own balanced-point-as-LP (`polytime.md` §2).** We
   already replaced CLY's Brouwer existence of balanced centers with a **convex
   program / LP** (Fermat–Weber). That is our LP contribution and it is *clean and
   proved* (formalised: `exists_balanced_point_box`). It does **not** by itself
   give poly time (the LP is on *samples*; producing samples is the open problem),
   but it removes any need for the P-LCP machinery on the centerpoint side.

**Verdict.** Route 2's structure (P-matrix ⟹ unique solution, monotone potential)
is *why* UEOPL membership holds and thus *why* our monotone-shrinking-`X_t`
invariant is legitimate. But the USO/P-LCP algorithms themselves offer no poly
lever we don't already match. Skip as an algorithm; keep as structural
justification.

---

## 5. Parameterized / smoothed / average-case (route 5) — the richest vein

This is where the *positive* poly/tractable results live, and where our
condition-number `κ` most plausibly connects.

- **Few random vertices ⟹ poly (FPT).** Gimbert–Horn (2008 STACS / LMCS'09):
  optimal **permutation strategies**; running time `O(|V_R|! · (|V||E|+|p|))`, so
  **poly when the number of random (AVG) vertices `|V_R|` is fixed** — SSG is FPT
  in `#random vertices`. Improved constants: Auger–Coucheney–Strozecki STACS'19;
  Ibsen-Jensen–Miltersen (arXiv 1112.5255, "few coin-toss positions").
- **Bounded first-return-time / ergodic ⟹ strongly poly.** Policy iteration for
  perfect-information stochastic mean-payoff games with **bounded first return
  times is strongly polynomial** (Akian–Gaubert–Hochart, arXiv 1310.4953). This is
  the ergodic/"well-mixed Markov chain" regime.
- **Smoothed poly (deterministic only).** Boros et al. (2011, *Stochastic Mean
  Payoff Games: Smoothed Analysis*) and **Manthey et al., ICALP'24** (arXiv
  2402.03975): a **condition number** (essentially the **value/valuation
  separation** `δ` — the minimum gap between competing strategy valuations)
  controls policy iteration; under Gaussian perturbation `1/δ = poly` w.h.p., so
  **deterministic** discounted/mean-payoff are **smoothed-polynomial**.
- **The crucial caveat.** Christ–Yannakakis: Howard's policy iteration is
  **NOT** smoothed-polynomial on **stochastic** single-player mean-payoff (MDPs).
  So the smoothed positive result **stops at deterministic games** — the
  *stochasticity* is what breaks the strategy-space smoothed argument.

**Connection to us — direct and load-bearing.** Our `notes/repair_attack.md`
measures a **geometric condition number `κ(X_t)`** and finds it bounded-with-drift
(`κ ∈ [1.3, 8.9]`, mean-reverting) exactly in the reliable window; the entire
sampler question is "`κ(X_t) ≤ poly`?". The smoothed literature has an
**algebraic condition number `δ`** (value separation) that is `1/poly` under
smoothing / for fixed `#random vertices` / in the ergodic regime. **These are two
condition numbers for the same instance.** Nobody has connected them. That is the
opening.

---

## 6. Value / quasi-poly algorithms, and our query method's time-competitiveness (route 6)

- **Quasi-poly is a parity-only phenomenon.** Calude–Jain–Khoussainov–Li–Stephan
  2017: parity games in `n^{O(log n)}`. It **does not extend** to mean-payoff /
  discounted / SSG (universal-tree lower bounds, Czerwiński et al. 2018, explain
  why the technique is parity-specific). So there is no quasi-poly SSG to borrow.
- **Value iteration**: pseudo-poly, `poly(1/(1−λ))` — useless at `λ=1−2^{−poly}`
  ("weakly polynomial buys nothing," `polytime.md` §0).
- **Our query method IS already at the frontier — deterministically.** Chen–Li–
  Yannakakis STOC'24: `O(d² log 1/ε)` **queries** (optimal-ish), brute-force time.
  Feodorov–Haslebacher 2026: `(log 1/ε)^{O(√d log d)}` **time**, i.e.
  `|G|^{O(√n log n)}` — the **best known *deterministic* SSG bound**, matching
  Ludwig's *randomized* `2^{O(√n)}` up to logs. So the geometric method is not a
  toy: query-optimal, and its time already equals the subexponential wall.
  **To beat the wall it needs the poly sampler and nothing else** (`hitrun.md`
  reduction: poly sampler ⟹ `poly(d, log 1/ε)` ⟹ SSG∈BPP=P).

**Verdict.** We are time-competitive at the subexponential frontier *today* and
the only missing factor is sampling `X_t`. Everything reduces to §7.

---

## 7. THE bridge, made concrete (the single deliverable)

**Claim to attempt (Condition-Number Transfer).**

> Let `G` be an SSG with value-separation gap `δ` (the smoothed/Gimbert–Horn/
> ergodic condition number: the minimum nonzero gap between competing valuations,
> equivalently the least `1−λ`-scaled value margin). Let `X_t` be our value-space
> candidate body after `t = O(d log 1/ε)` balanced cuts. Then
> `κ(X_t) ≤ poly(d, 1/δ)`  (equivalently `h(X_t) ≥ 1/poly(d, 1/δ)`).

Why this is *the* bridge (dominates every alternative above):

1. **It imports three known tractable regimes into our sampler at once.** `δ =
   1/poly` holds (a) w.h.p. under smoothing (Manthey et al.), (b) for fixed
   `#random vertices` (Gimbert–Horn: the permutation valuations are well-separated),
   (c) in the bounded-return-time/ergodic regime (Akian–Gaubert–Hochart). Under
   the claim, each gives `κ(X_t)≤poly ⟹` our hit-and-run mixes `⟹` poly sampler
   `⟹` our algorithm is poly on that regime — a **unified** re-derivation via
   geometry.
2. **It can cross the Christ–Yannakakis barrier.** Their counterexample kills
   *strategy-space* policy iteration on *stochastic* games. Our sampler is
   value-space; if `κ(X_t)` is controlled by `δ` **regardless of stochasticity**,
   the geometric method could be smoothed-poly on **stochastic** SSG where policy
   iteration provably is not. Proving the claim *with the `d` = value dimension and
   no strategy dynamics* is exactly what sidesteps their obstruction. This is the
   one place our machinery could do something the established routes cannot.
3. **It matches what we already measure.** `repair_attack.md` found `κ` bounded and
   mean-reverting on realizable instances but could not *explain* why (the
   symmetric downdate cannot repair a thin axis; the "asymmetric injection" story
   is intermittent). A `δ`-control law would be the missing explanation: the thin
   (dumbbell) direction of `X_t` is a near-degeneracy of the value operator, whose
   size is exactly `δ`. **The realizable dumbbell (our one wall,
   `isoperimetry_summary.md` §4) should have width `≥ δ`** — no dumbbell narrower
   than the value gap can be *realized* by a game with separation `δ`.

**The precise sub-lemma to try first** (smallest true step toward the claim):

> **(Dumbbell ⇒ small gap.)** If `X_t` has an isoperimetric bottleneck of
> conductance `h` across a hyperplane with normal `u`, then the SSG that realized
> the cut history has two vertex-strategies whose valuations along `u` differ by
> `≤ g(h,d)` with `g→0` as `h→0`. Contrapositive: `δ ≥ 1/poly ⟹ h ≥ 1/poly`.

This is the honest crux restated in transferable terms: it says the *geometric*
bottleneck must be an *algebraic* near-tie of the value operator. It is plausibly
true (a bottleneck means two roughly-equal-mass value regions the cuts can't tell
apart — i.e. two near-equal strategies), it is **new** (nobody has related `h(X_t)`
to the game's value gap), and it is `= SSG∈P` only in full generality — but its
**restrictions to the three regimes in (1) are exactly the known tractable cases**,
so partial credit is real and checkable.

**Immediately actionable experiment** (for `main` to run; no heavy compute):
On the existing realizable SSG instances in `polytime_experiments/`, measure the
pair `(δ, 1/κ(X_t))` and `(δ, h_iso(X_t))` per instance and plot/regress. The
claim predicts `1/κ` and `h` are **lower-bounded by a poly in `δ`** and that the
instances with smallest `δ` are exactly the ones approaching a dumbbell. If the
data shows `h ≳ δ^{O(1)}` cleanly in the reliable window, the sub-lemma is worth a
real proof push; if `h` collapses while `δ` stays bounded, the bridge is refuted
and we save the effort. This directly reuses `repair_measure.py` /
`kappa_vs_h.py` plus a value-gap computation on the same instances.

---

## 8. Priority ranking of the routes (for effort allocation)

1. **§7 Condition-Number Transfer** (`δ ⟹ κ/h`). Highest: unifies three tractable
   regimes, can cross the stochastic smoothed barrier, explains our own data,
   value-space so immune to the strategy-space lower bounds. **The one to push.**
2. **§2 fixed-discount / `λ`-free rate** as the *setting*: our method's
   `λ`-independence is the concrete advantage over value iteration; keep as the
   headline framing, and make sure any `δ`-bound is stated `λ`-free.
3. **§5 few-random-vertices as a proving ground.** Cleanest place to *prove* a
   special case of §7 (finite `V_R` ⟹ finitely many permutation-valuation gaps ⟹
   bounded `κ`), and it is genuinely poly (Gimbert–Horn), so a geometric re-proof
   is a real, publishable check with no barrier risk.
4. **§1/§4 lower bounds & UEOPL** — *not* to attack, but to cite: they justify the
   value-space detour (strategy-space is provably stuck) and certify our
   total-search structure.
5. Everything else (quasi-poly, weakly-poly, USO algorithms): dead ends for SSG;
   documented so we don't revisit.

---

## 9. Flags raised to `main`

- **Actionable now:** the `(δ, 1/κ, h)` regression experiment in §7 on existing
  instances — decides go/no-go on the whole bridge without new theory.
- **Framing correction to propagate:** our contribution should be pitched as a
  **value-space condition-number** algorithm, explicitly contrasted with the
  strategy-space smoothed result (Manthey et al.) that *fails on stochastic games*
  (Christ–Yannakakis). That contrast is the strongest available argument that this
  line is not already subsumed.
- **Scope check for the formalizers:** the UEOPL placement (SSG ∈ UEOPL ⊆ CLS)
  means our monotone-`X_t` + unique-`x*` invariants are the "unique line +
  potential" of a *named* UEOPL problem — worth stating precisely if any writeup
  claims novelty of the total-search structure.

---

### Source list

- Condon, *The complexity of stochastic games*, Inf. & Comp. 1992.
- Fearnley, Goldberg, Hollender, Savani, *The Complexity of Gradient Descent:
  CLS = PPAD ∩ PLS*, STOC 2021.
- Fearnley, Gordon, Savani, Sørensen, *Unique End of Potential Line*, ICALP 2019 /
  JCSS — https://arxiv.org/pdf/1811.03841
- Ludwig, *A subexponential randomized algorithm for the simple stochastic game
  problem*, Inf. & Comp. 1995.
- Jurdziński, Savani, *A Simple P-Matrix LCP for Discounted Games*, CiE 2008 —
  https://www.dcs.warwick.ac.uk/~mju/Papers/JS08-CiE.pdf
- Gimbert, Horn, *Simple Stochastic Games with Few Random Vertices Are Easy to
  Solve*, STACS 2008 / LMCS 2009 — https://arxiv.org/abs/0712.1765
- Auger, Coucheney, Strozecki, *Solving SSG with Few Random Nodes Faster Using
  Bland's Rule*, STACS 2019.
- Ibsen-Jensen, Miltersen, *Solving SSG with few coin-toss positions*,
  https://arxiv.org/pdf/1112.5255
- Friedmann, *Exponential Lower Bounds for Policy Iteration*, ICALP 2010 —
  https://arxiv.org/pdf/1003.3418
- Friedmann, Hansen, Zwick, *Subexponential lower bounds for randomized pivoting
  rules / random-facet*, SODA & STOC 2011.
- Manthey et al., *Smoothed Analysis of Deterministic Discounted and Mean-Payoff
  Games*, ICALP 2024 — https://arxiv.org/abs/2402.03975 (Christ–Yannakakis
  counterexample for stochastic single-player therein).
- Boros, Elbassioni, Gurvich, Makino et al., *Stochastic Mean Payoff Games:
  Smoothed Analysis and Approximation Schemes*, ICALP 2011.
- Akian, Gaubert, Hochart, *Policy iteration for perfect-information stochastic
  mean-payoff games with bounded first return times is strongly polynomial*,
  https://arxiv.org/abs/1310.4953
- Zwick, Paterson, *The complexity of mean payoff games on graphs*, TCS 1996.
- Karp, *A characterization of the minimum cycle mean in a digraph*, 1978.
- Calude, Jain, Khoussainov, Li, Stephan, *Deciding parity games in
  quasipolynomial time*, STOC 2017; Czerwiński et al., universal-tree lower
  bounds, 2018.
- Chen, Li, Yannakakis, STOC 2024 (`ℓ∞`-contraction query complexity);
  Feodorov, Haslebacher 2026 (best deterministic SSG time) — see `polytime.md` §0.
- Direct reduction stochastic parity → SSG (2025) — https://arxiv.org/pdf/2506.06223
</content>
</invoke>
