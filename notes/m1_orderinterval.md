# M1 (monotone convex order-interval) + active-set flatness — NEGATIVE

Test of rogue's M1 (monotonicity ⟹ free convex cuts) and Corollary-C's
active-set-flatness hypothesis, on hard spread-x* SSG (`make_ssg`, d=4,5,6,
1−γ=1e−3, seeds 0,1; light hit-and-run center, 22 rounds).

Per round logged: is the ternary sign all-one-sign (⟹ a convex sub/supersolution
orthant cut)?; width of the maintained convex order-interval `[L,U]∋x*` (L raised
by subsolutions `f(bp)≥bp`, U lowered by supersolutions); active-set size
`|A(c)| = #{i : |x*_i−c_i| ≥ ½ max_j|x*_j−c_j|}`.

| d | seed | 1-sign rounds | order-interval width shrink rate | mean\|A\| | max\|A\| |
|---|---|---|---|---|---|
| 4 | 0 | 9% | 0.96 | 3.0 | 4 |
| 4 | 1 | 5% | 0.98 | 3.0 | 4 |
| 5 | 0 | 0% | 1.00 (never updated) | 4.9 | 5 |
| 5 | 1 | 5% | 0.95 | 4.0 | 5 |
| 6 | 0 | 0% | 1.00 (never updated) | 4.4 | 6 |
| 6 | 1 | 9% | 0.97 | 3.6 | 6 |

(x* stayed inside [L,U] in all runs — the order-interval logic is sound.)

## Verdict — both hypotheses fail on hard SSG

- **M1 convex bypass DEAD.** Signed-consistent rounds are rare (0–9%), so free
  convex orthant cuts almost never occur; the convex order-interval barely shrinks
  (rate 0.95–1.00, i.e. no better than nothing — several instances never get a
  single sub/supersolution). Monotonicity does not hand back a usable convex
  region on hard instances: the query point is mixed-sign nearly every round (the
  non-convex pyramid cut is forced).
- **Corollary C two-coordinate narrowing DEAD.** The active set is **Θ(d)**, not
  O(1): `max|A| = d` in every instance, mean 3–5 of d. So the cut support cannot
  be narrowed to two coordinates by proximity — the |S|≥3 non-convex regime is
  the norm, not the exception.

Both were "bypass the sampler via convexity" hopes; both are refuted. Consistent
with the whole geometric family reducing to the isoperimetry wall. The monotone
structure does not rescue the algorithm on the hard (spread-x*, γ→1) regime.
Script: `m1_run.py`.
