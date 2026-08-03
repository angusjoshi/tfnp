# Idea D on Melekopoglou–Condon: preliminary NEGATIVE for the sampler-free bypass

Test of Idea D (the value-space policy-certificate route) on the validated
Melekopoglou–Condon 1994 exponential policy-iteration lower bound
(`friedmann.py`, `mc_basic(n)`; `simple_pi` does exactly `2ⁿ−1` switches,
self-certifying — confirmed n=1..6). Driver: `run_certified` with the
**cheap sampler-free center** (`cheap_center` = short hit-and-run nsamp=16 + FW
LP), stopping at the first round whose read-off policy the Bellman certificate
declares optimal. Metric = rounds-to-stabilize vs `2ⁿ−1`.

## Data (cheap center, seed 0)

| n | d | 2ⁿ−1 | FW-center rounds | wall-clock |
|---|---|---|---|---|
| 4 | 9 | 15 | 8 | 1.8s |
| 5 | 11 | 31 | 28 | 26s |
| 6 | 13 | 63 | did **not** certify within 90 rounds / budget | >115s |

## Reading (honest, preliminary)

- Rounds are *below* `2ⁿ−1` but the **ratio climbs** (0.53 → 0.90), and at n=6 the
  crude center fails to stabilize within 90 rounds. With a *randomized/crude*
  center the read-off policy can oscillate and take **≥** the deterministic
  `2ⁿ−1`, so this is a **moderate negative for the sampler-free (cheap-center)
  bypass**: the round count does not look convincingly poly — it drifts toward
  (or past) the policy-iteration count.
- This is **consistent with the advisor's "D trades walls, doesn't skip one"
  ruling**: with an *accurate* FW center the outer loop is cutting-plane
  bisection (poly rounds by volume-halving `vol(X_t)=2⁻ᵗ`, Friedmann/MC do not
  apply) — but the accurate center **needs the sampler** (the open wall). Drop to
  a cheap center and you lose volume-halving; the sign/policy dynamics reverts
  toward strategy-improvement, and the MC adversary bites.

## What this does and does NOT show

- **Does not** test the accurate-FW-center version (poly by volume-halving, but
  sampler-bound) — so it is *not* a refutation of Idea D as a whole; it is
  evidence that the *cheap-center bypass* — D's actual selling point — does not
  cleanly escape.
- Small n (4–6), single seed, crude center; the certificate itself is sound
  (returns x* exactly, matches value iteration to 1e-16) — the negative is about
  round count, not correctness.
- Not pursued further: exact-rejection accurate centers to confirm the
  volume-halving poly baseline would settle the "trades walls" picture cleanly,
  but are compute-expensive (rejection ≈2⁻ᵗ) and were deferred under the
  laptop/usage constraints.

## Verdict

Preliminary **NEGATIVE** for the sampler-free Idea-D bypass: the cheap-center
value-space pivot does not exhibit poly rounds-to-stabilize on the MC lower-bound
family. Combined with the conditioning route's exhaustion, the sampler (an
accurate center) remains the load-bearing wall — exactly as the advisor's ruling
predicted. Idea D's one unambiguously sound contribution stands: the
**sampler-free Bellman certificate** (`certify`), which turns any candidate
policy into an exact yes/no with an exact `x*` when it passes.
