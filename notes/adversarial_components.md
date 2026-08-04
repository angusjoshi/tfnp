# Realizability made finite, and the adversarial shattering of `X_t`

*Lean: `Tfnp/Realizability.lean`, plus `convex_pyramid` / `apex_mem_pyramid` /
`cut_inter_convex_isPreconnected` in `Tfnp/Progress.lean` (all sorry-free;
axioms `propext`, `Classical.choice`, `Quot.sound`). Experiments:
`notes/polytime_experiments/adversary_game.py`, results in
`adversary_results.txt` (midpoint policy), `free_adversary_results.txt`
(no realizability), `adversary_magfix_results.txt` (corrected policy),
`verify_shatter_results.txt` (density check). Run order matters — see §5.*

The surviving conjectures ((★) of `FINAL_REPORT.md`, the star-cover bound of
`star_cover.md`) quantify over **realizable** balanced-cut trajectories, and
every previous experiment probed them only with *random* SSG instances. This
note (i) makes "realizable" a finite, checkable, machine-verified condition,
(ii) extracts the combinatorial structure of that condition, and (iii) plays
the resulting game: a certified-realizable adversary steering the oracle's sign
answers to shatter `X_t` into many connected components. **It succeeds.** This
is the sharpest negative result of the project: the realizable candidate body
can be driven to `h(X_t) = 0` — literal disconnection with near-equidistributed
mass — while the algorithm receives its full volume-halving every round.

## 1. Realizability is a finite condition (machine-checked)

`ℓ∞^d` is hyperconvex, so partial contractions extend without loss — concretely,
by the coordinatewise McShane formula. Formalized:

> **Theorem (`realizable_of_pairwise`).** Let `(c^r, w^r)_{r≤t}` be query/
> response pairs with every `w^r` in the unit cube, `0 ≤ λ < 1`, and
> `‖w^r − w^q‖∞ ≤ λ‖c^r − c^q‖∞` for all `r, q`. Then there is an `f` with
> `IsLInfContraction f λ` and `f(c^r) = w^r` for every `r` — namely
> `clamp ∘ F` with `F(y)_i = min_r (w^r_i + λ‖y − c^r‖∞)`.

> **Corollary (`realizable_cuts_retain_fixedPoint`).** Any pairwise-consistent
> history admits a fixed point `x*` lying in **every** apex cut
> `⋃_{i:sᵢ≠0} 𝒫ᵢ(c^r, s^r)`, `s^r = sgn(w^r − c^r)`.

So an adversary answering queries subject *only* to the finite pairwise
inequalities can never be caught out: a genuine contraction stands behind the
answers, and its fixed point survives all the cuts. "Realizable trajectory" =
"balanced apexes + a solution of this inequality system". The game and the
operator are gone from the definition.

## 2. The structure of the condition: per-coordinate sign menus

Because `‖·‖∞` is a max, the pairwise inequalities **decouple by coordinate**:
at a new query `c` with history `(c^q, v^q)` (`v = w − c`, the displacement),
the feasible new displacement satisfies, independently for each `i`,

```
v_i ∈ [ max_q (−λD_q − a_i^q + v_i^q),  min_q (λD_q − a_i^q + v_i^q) ],
a^q = c − c^q,  D_q = ‖a^q‖∞,
```

intersected with the cube constraint `c + v ∈ [0,1]^d`. The adversary's entire
per-round freedom is the resulting **per-coordinate sign menu**, and only
near-argmax coordinates of each apex pair constrain anything (per coordinate,
`v_i` is a λ-Lipschitz-consistent potential on the apex set; feasibility is a
difference-constraint system whose consistency is the triangle inequality).

The displacement **magnitude policy** turns out to govern everything:

* `|v| ≲ (1−λ)·D` (tiny): every apex pair pins the sign on its argmax
  coordinate — menus collapse from `2^d` to 1–4 within `~d` rounds (observed).
* `|v| ≈ diam(X)` (large): nearby apexes force nearly identical answers —
  `menu = 1` stretches (observed with a midpoint policy).
* `(1−λ)·diam ≪ |v| ≪ apex separations` (e.g. `|v| ~ 10⁻⁴` at `λ = 1−10⁻⁹`):
  **menus stay at the full `2^d`** for the whole horizon. In the SSG-hard regime
  `λ = 1 − 2^{−poly}` this window always exists, so for poly-length trajectories
  a correctly-played adversary has *unrestricted* sign freedom: realizability
  constrains nothing that matters.

## 3. The game, and the shattering

Implemented exactly (`adversary_game.py`): the algorithm exact-rejection samples
`X_t`, takes the Fermat–Weber balanced apex (LP), queries; the adversary
enumerates its sign menu and picks the candidate maximising the number of
connected components of `X_t ∩ K(c,s)`, measured on a freshly-rebuilt
segment-checked kNN graph of the survivors (pocket count and mass entropy as
tie-breaks), taking the best candidate whose displacement fits its intervals.
Control mode answers from the explicit contraction `f(y) = x* + λ(y−x*)`;
components stay 1 throughout, as the Lean theorem `starshaped_of_toward`
requires — the pipeline validates.

**Result (corrected magnitude policy, `adversary_magfix_results.txt`; d = 5, 6,
t ≤ 2.5d, N = 2200/round, exact rejection, kept fraction ≈ ½ every round):**

| run | components over rounds | final mass profile |
|---|---|---|
| d=5 seed 1 | 1,…,1,5,9,14,19,18 | 0.17/0.12/0.08/0.07/… |
| d=5 seed 2 | stays 1–2 (greedy finds no cascade) | 0.98 in one piece |
| d=6 seed 1 | 1,…,1,3,8,18,23,25,28,28,28 | 0.07/0.06/0.05/0.05/… |
| d=6 seed 2 | 1,…,6,4,3,10,7,8 | 0.54/0.18/0.12/0.03 |

The unconstrained-signs control (`free` mode) produces the **same trajectories**
— with the right magnitudes, the realizable adversary's top choice is always
feasible (menus full, rank 0). Density verification (×4 samples, 18-NN, finer
segment checks — `verify_shatter_results.txt`) confirms the structure: a few
crumbs merge but the mass-comparable fragmentation stands —
`d=5, t=12`: **17 components, masses 0.111/0.105/0.096/0.086/0.072/…**
(near-perfect equidistribution); `d=6, t=14`: **23 components, top mass 0.14**;
and the onset is visible in the prefixes (1 component at t=6, 4 at t=9).

**Onset dynamics.** The cascade starts at `t ≈ d+2` and self-reinforces. The
mechanism matches the machine-checked geometry: every pyramid of a cut contains
its apex and is convex (`apex_mem_pyramid`, `convex_pyramid`), so **a convex
lobe containing the apex cannot be split** (`cut_inter_convex_isPreconnected`) —
but once the first split happens, the Fermat–Weber apex of the shattered mass
sits in the *gap between* lobes, every lobe is apex-free, and each round splits
them further. Disconnection is an absorbing regime.

## 4. What died, and what it redirects

* **The isoperimetry route is closed, permanently.** The Open Lemma of
  `isoperimetry_attack.md` — `h(X_t) ≥ 1/poly` on realizable trajectories — is
  **false**: realizable trajectories reach `h = 0` exactly (disconnection), at
  d = 5 and 6, within `2.5d` rounds, with certified realizability (§1) and the
  full volume-halving delivered. Hit-and-run, ball walks, and any
  single-connected-body sampler cannot serve the reduction. The earlier sliver
  obstruction was "false but non-realizable"; this one is realizable.
* **The random-instance optimism was an artifact.** `star_cover.md`'s `k = 1–2`
  and the "essentially star-shaped" picture hold for *random* SSG operators
  only. The conjectures' danger zone — adversarial trajectories — behaves in the
  opposite way.
* **(★)/Q are hit but not killed.** Components lower-bound every cover measure
  (star, convex, cell), so realizable `k` reaches ≈ 28 at `(d,t) = (6,14)` —
  but 28 is not superpolynomial, and the d-ceiling (unmeasurable past d ≈ 6–7)
  cuts both ways: the observed counts are consistent with both `poly(d,t)` and
  `2^{Θ(d)}`. What changes is the *status* of (★): it can no longer be supported
  by "realizable bodies look benign"; it now needs a proof that shattered
  realizable bodies have `poly(d,t)`-many mass-carrying pieces, or a refutation
  by an adversary with a growth schedule in `d`. The sampler an algorithm needs
  must be a **union sampler over components** (Karp–Luby style over a cover) —
  single-region MCMC is not an option even in the realizable case.
* **The apex-in-lobe lemma** (`cut_inter_convex_isPreconnected`) is the one
  positive structural handle the game surfaced: shattering requires first
  expelling the apex from the mass. A cut rule that *keeps the apex inside a
  mass-carrying convex core* would block the cascade at its first step — whether
  any such rule can coexist with balancedness (`apex_between_of_two_sided` says
  progressive apexes are interior in a weaker sense) is a precise open question,
  and now the most natural place to look for either a fix or a proof that none
  exists.

## 5. Honest scope and reproduction

* Run order: `adversary_results.txt` used a midpoint magnitude policy (menus
  locked, no shattering — superseded); `free_adversary_results.txt` dropped
  realizability (shattering); `adversary_magfix_results.txt` is the definitive
  run (realizable, `MAG = 10⁻⁴`, same shattering). Seeds 2 show the greedy
  adversary does not always find the cascade — the attack is sufficient, not
  necessary, evidence.
* Components are measured on segment-checked kNN graphs of exact-rejection
  samples, then re-measured at 4× density; they are certified as *realizable*
  (§1) but the disconnections themselves are sampled, not proven — a bridge of
  volume below ~10⁻⁴ of the body would be invisible. For the isoperimetry
  conclusion this distinction is immaterial: a bridge that thin already gives
  `h ≤ 10⁻⁴·poly ≪ 1/poly` at these dimensions… i.e. the Cheeger refutation
  stands with `h ≤ (invisible-bridge volume)`, disconnection or not.
* d ≤ 6, t ≤ 14 as always. Nothing here decides d-scaling; it decides which
  *hypotheses* about realizable trajectories were wrong, and it upgrades the
  adversary from "conjectured" to "implemented with a machine-checked
  realizability certificate".
