
---

## Experimental results (run by main, capped/exact-rejection)

Script: `q_run.py`, `q_deep.py`, `q_tail.py`, `q_res.py`.

**Calibration — the greedy-cover proxy is valid.** dumbbell(2D)→k=2; comb(m=3)→k=3;
comb(m=5)→k=5. The proxy correctly counts star-pieces / detects real multi-lobe structure.

**Realizable SSG X_t — star-cover number is TINY in the whole measurable window:**
- t=d: k=1 for d=3,4,5 (both seeds).
- t=2d (the regime where the *certifiable* kernel collapses, C3): k=1–2, d=3,4,5, 3 seeds.
- coverage-target sweep: k=1 even at target 0.999 — the tail is NOT hiding pockets.
- resolution control: k=1 and best-single-witness coverage 0.99–1.00 at nseg=10/40/120 —
  NOT a coarse-segment-visibility artifact.

**Reading.** In-window, realizable X_t is essentially **star-shaped from a single point**
(k≈1) even at t=2d — so the star-cover / Karp–Luby sampler would be *trivially* poly here.
This realizes the "star-shaped up to o(1)-measure defect" open case (summary §5.2).

**Tension with C3 (must reconcile):** C3 found the *certifiable* convex kernel
(box ∩ ⋂ ker(K), the pairwise-w-sum LP) empties at t≈d/2, and its best candidate saw only
50–90%. Here a witness (searched over cut-apexes + rejection-sampled points) sees ~100%.
Honest reconciliation: the **true** kernel (points seeing the body) is ⊇ the certifiable
one and appears **nonempty even when the certifiable kernel is empty** — i.e. C3 killed
*certifiable* recovery, not actual star-shapedness. This needs a proof, and the candidate
pool difference could matter.

**Caveats (the usual ceiling):** d≤5, t≤2d — cannot see the provable exp-in-d bound
k≤(d²t)^d turn on; k=1 in-window does not prove k=poly asymptotically. SUGGESTIVE, not
decisive — but it is the most *positive* in-window signal any route produced, and Q is
provably NOT dumbbell-wall-equivalent.

**Proof targets (for closing, beyond the window):** (a) show the *true* kernel of a
balanced-cut intersection is nonempty / k=O(1) (reconciling C3); (b) star-cover's
"balanced-central pinwheel cuts keep reflex ridges non-interacting ⟹ additive O(dt) reflex
count ⟹ k=poly" — the Q-analog of asymmetric repair.

## d-scaling probe (§4 rerun) — mostly small k, but the measurement CEILING bites

Broad greedy (apexes + ~120 rejection candidates, exact rejection, nseg=10, target 0.99),
`q_dscale.py`:

| d | seed | k(t=d) | k(t=2d) | best-witness(t=2d) |
|---|---|---|---|---|
| 6 | 0 | 1 | 2 | 0.97 |
| 6 | 1 | 3 | 2 | 0.98 |
| 7 | 0 | 1 | 1 | 0.99 |
| 7 | 1 | 1 | **12** | 0.75 |

(d=8 did not complete — build+visibility too slow within the cap.)

**Honest reading.** At t=d, k=1–3 (small). At t=2d, mostly k=1–2 — BUT one outlier
(d=7 s1) jumped to k=12 with best-witness 0.75. This is **most likely a thin-body /
under-sampling artifact**: at t=2d, vol(X_t) ≈ 2^{−2d}, so exact rejection yields very few
cloud points and poor candidates, and cannot be improved (needs ~2^{2d} draws, over the
safe cap). I cannot confirm whether k=12 is genuine mild pocket-proliferation or noise.

**This is the binding constraint on deciding Q.** The d-scaling of k — the ONLY thing that
decides the route (poly vs exp-in-d) — is not reliably measurable past d≈6–7, because the
deep-t bodies whose star-cover we need are exactly the ones that can't be sampled without
the poly-time sampler we are trying to build (circular). So the empirics are
**encouraging-but-ceiling-limited** (small k in the reliable window, one unresolved
outlier), and Q's fate rests on the PROOF target, not more measurement:
> prove k(X_t) = poly(d,t) for balanced-cut intersections (the pinwheel / non-interacting
> reflex-ridge bound, §1c) — the Q-analog of "asymmetric repair", and the only route past
> the ceiling.
