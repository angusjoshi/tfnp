# Condition-Number Transfer: go/no-go on δ → κ / h

Testing the single most promising bridge of `notes/ssg_directions.md` §7: does the
SSG **value-separation gap δ** control our **geometric conditioning**? Concretely,
is `1/κ(X_t) ≳ δ^{O(1)}` and `h_iso(X_t) ≳ δ^{O(1)}`? If yes, the bridge is real
(imports smoothed / few-random-vertices / ergodic tractable regimes into our
sampler, and could cross the Christ–Yannakakis barrier for *stochastic* games). If
`κ` blows up / `h` collapses while `δ` stays bounded away from 0 (a dumbbell with a
healthy value gap) → bridge refuted, saving a proof push.

**Verdict up front: NO-GO for a proof push on the transfer as stated.** In the
reliably-measurable window the data gives **no positive signal** — the fitted
exponent is ≈ 0, `κ`/`h` are effectively **independent of δ** over 4 orders of
magnitude of δ, and the specific §7.3 mechanism ("dumbbell width ≥ δ") is
**contradicted** (the smallest-δ instances are the *best*-conditioned). The strict
one-directional lower bound is not literally *refuted* (no blown-`κ` instance
exists in-window at any δ), but δ is shown to be the wrong controlling variable, and
the regime where the bound could still bite is unmeasurable. Details and honest
caveats below.

## Method

`condition_transfer.py`, exact rejection ground truth, all caps obeyed (d ≤ 6,
t ≤ 6, N = 400, batch 50k, ≤ 3M draws/round, one foreground job). Added
`make_ssg_full` + `ssg_value_gap` to `common.py` (pure additions; `make_ssg_full`
reproduces `make_ssg` byte-for-byte — verified `x*` match = 0 — and also returns
`succ, rew, types, γ`).

- **δ (value-separation gap)** at `x*`: for each MAX interior state,
  `gap_i = (largest successor value) − (2nd largest)`; for MIN, `(2nd smallest) −
  (smallest)`; AVG skipped; `δ = min` over MAX/MIN states (smallest decision
  margin). Sinks: `-1→0, -2→1`.
- **Sweep**: `1−γ ∈ {1e-1, 1e-2, 1e-3}`, `d ∈ {4,5,6}`, multiple seeds — **15
  instances**, δ spanning `[2.07e-5, 3.32e-1]`.
- Per instance: run the real balanced-cut algorithm to `t=6`; at `t=3` and `t=6`
  measure `1/κ(X_t)` (scale-free) and `h_iso(X_t)` (isotropic 1-D Cheeger upper
  bound; coarse 24-bin/smoothed histogram — see caveat).

## Results

30 rows (15 instances × 2 rounds). δ range `[2.07e-5, 3.32e-1]`; **κ range
`[2.09, 10.91]`; h_iso range `[0.333, 0.611]`.**

Regression of `log(1/κ)` and `log(h_iso)` against `log(δ)`:

| subset | fit | slope (exponent) | R² | corr |
|---|---|---|---|---|
| all rows | log(1/κ) ~ log δ | **−0.027** | 0.05 | −0.23 |
| all rows | log(h_iso) ~ log δ | **+0.007** | 0.03 | +0.19 |
| t=6 only | log(1/κ) ~ log δ | **−0.043** | 0.11 | −0.33 |
| t=6 only | log(h_iso) ~ log δ | **+0.010** | 0.05 | +0.22 |
| t=6, δ≥1e-3 (drop near-ties) | log(1/κ) ~ log δ | −0.026 | 0.01 | −0.09 |
| t=6, δ≥1e-3 (drop near-ties) | log(h_iso) ~ log δ | +0.057 | 0.27 | +0.52 |

**The exponent is ≈ 0 everywhere.** Over δ spanning 2e-5 → 0.33 (4 decades), `1/κ`
moves within `[0.09, 0.48]` (κ ∈ [2.1, 10.9]) and `h_iso` within `[0.33, 0.61]`,
with no power-law dependence on δ. The `log(1/κ)` slope is even mildly *negative*
(smaller δ → slightly *better* 1/κ, the opposite of the transfer). Only h_iso on
the δ≥1e-3 subset shows a weak positive trend (slope +0.06, R²=0.27) — far too weak
and noisy to be a `h ≳ δ^{O(1)}` law.

### The two decisive observations

1. **Smallest-δ instances are the BEST-conditioned — §7.3's mechanism is
   contradicted.** The proposed intuition was "the thin/dumbbell direction of `X_t`
   has width ≥ δ, so small δ ⟹ near-dumbbell." The data says the reverse:

   | δ | t | κ | h_iso |
   |---|---|---|---|
   | 2.07e-5 | 6 | 2.83 | 0.526 |
   | 4.05e-5 | 6 | 2.74 | 0.442 |
   | 5.51e-5 | 6 | 4.23 | 0.559 |
   | **5.31e-3** (worst κ) | 6 | **10.91** | 0.333 |
   | 2.32e-1 (largest δ) | 6 | 4.58 | 0.549 |

   The near-degenerate value ties (δ ≈ 1e-5, `x*≈0.5` everywhere) produce perfectly
   healthy geometry (κ≈2.8, h≈0.5), **not** a dumbbell. The single worst-conditioned
   instance (κ=10.9) sits at a *middling* δ=5e-3, and the largest-δ instance
   (δ=0.23) is unremarkable (κ=4.6). So δ near 0 does not create a bottleneck.

2. **The geometry is determined by the SIGN-PATTERN (orthant) trajectory, not by
   δ.** Two instances (`d=5, seed=0`) at `1−γ = 0.1` (δ=1.54e-2) and `1−γ = 0.001`
   (δ=2.69e-4) — a 57× gap in δ, and different fixed points — produced **byte-for-
   byte identical** `1/κ` (0.4795 @ t3, 0.4441 @ t6) and `h_iso` (0.5347, 0.5454).
   Reason: the cut is `K(bp, sign(f(bp)−bp))`; when the two operators share the same
   sign (orthant) pattern at every balanced center, they produce the *same body*
   `X_t` regardless of the gap magnitudes. So `X_t`'s conditioning is a function of
   the combinatorial sign history, and δ (a scalar magnitude) is decoupled from it.

### Refuter scan

No instance with δ ≥ 0.03 and (κ > 6 or h < 0.3) — but equally, **no dumbbell /
blown-κ instance exists in the window at any δ** (max κ = 10.9). So the window
neither confirms the bridge (no δ-control signal) nor exhibits its failure mode
(no realizable dumbbell to check δ against).

## Honest caveats (why this is a soft, not hard, no-go)

- **The window is likely too shallow to reach the dumbbell regime.** The bridge
  concerns `X_t` at `t = O(d log 1/ε)`; the anisotropy/dumbbell that δ would
  putatively control forms deep (`t ≈ 2d`, `notes/isoperimetry_summary.md` §7). At
  `t ≤ 6` (forced by exact-rejection volume `≈2^{-t}` and the caps) `X_t` is in its
  benign early phase where κ is healthy for *every* instance. So the experiment
  tests the transfer only before it could bite; the deep regime is unmeasurable
  here (`d≈12,t≈2d` ceiling).
- **N=400 noise.** κ (esp. λ_min) and h_iso are noisy at N=400; h_iso is a coarse
  24-bin histogram upper bound (finer bins give spurious h=0 from empty interior
  bins — quarantined). Treat κ to ~±20%, h_iso to ~±0.1.
- **Near-tie δ (≈1e-5) instances** are near-trivial games (`x*≈½` uniformly), not
  the "hard SSG" regime; excluding them (δ≥1e-3 subset) does not rescue the
  transfer — the exponent stays ≈0 for 1/κ.

## Verdict and recommendation

**NO-GO on a proof push for `1/κ ≳ δ^{O(1)}` / `h ≳ δ^{O(1)}` as the bridge.** The
measurements give no positive support (exponent ≈ 0, corr ≈ 0), actively contradict
the §7.3 "dumbbell width ≥ δ" mechanism (smallest-δ instances are best-conditioned),
and show `X_t`'s conditioning is governed by the **combinatorial sign-pattern
trajectory**, with the scalar gap δ decoupled from it (identical geometry at 57×
different δ). The one-directional lower bound `δ≥1/poly ⟹ κ≤poly` is not literally
refuted (no counterexample dumbbell exists in-window), but it is untestable here and
δ is the wrong knob.

Concrete steer for the bridge: if conditioning is to be transferred from SSG
structure, the controlling quantity is **combinatorial (which orthant/sign patterns
the cut trajectory visits — i.e. which strategy pairs stay active)**, not the scalar
value gap δ. A transfer lemma should be phrased against the sign-pattern history,
not δ. Pursuing the δ-transfer proof as written is not warranted on this evidence.
