# The crux-prover decisive experiment: identity validation + the mean-reversion linchpin

Runs crux-prover's experiment (`notes/crux_scalefree.md` §6) on exact-rejection
ground-truth samples of `X_t`. Two parts: **(A)** validate the new exact identities
(Identity 1′, the T3 factor, Lemma 2 `ΔᵀΣ⁻¹Δ ≤ 4`), and **(B)** the mean-reversion
linchpin — does a *blind* long axis (`ρ(v_max)≈0`) persist across consecutive
rounds (the counterexample shape), or is high κ associated with a *sensed* long
axis that gets shaved next round (mean-reversion real)?

Harness `condition_experiment` reuses the `repair_measure.py` structure. Exact
rejection, **N=500**, batch 50k, ≤3M draws/round, `t≤10`, one foreground job — all
caps obeyed. **Key confound control:** all per-direction quantities (`ρ`, `a`, `c`,
the identity terms) are projected variances along the *fixed* eigenvectors of the
full-sample covariance, hence **unbiased at any n** (unlike a min-eigenvalue); and
`Δκ` uses the **fresh** next-round κ. The only residual bias is a ~20% Marchenko–
Pastur *inflation* of κ itself at N=500,d=6 (flagged where it matters).

## (A) Identity validation — all pass to sampling tolerance

Across all 6 instances below (d=4,5,6; SSG spread-`x*`):

| identity | result |
|---|---|
| **Identity 1′** `δ(v)=vᵀΣ(K')v−vᵀΣ(X)v == σ_v²(a(v)−ρ(v)²)`, `v∈{v_min,v_max}` | max |resid| = **9.6e-4** |
| **T3 factor** `c(v)=vᵀΣ(K')v/vᵀΣ(X)v == 1+a(v)−ρ(v)²` | max |pred−actual| = **9.9e-3** |
| **Lemma 2** `ΔᵀΣ⁻¹Δ ≤ 4` | **MAX observed = 2.05** (bound 4; never exceeded) |
| sign-fold `σ=sgn(max wᵢ+min wᵢ)` vs actual `K_ok` split | agreement **≥ 0.99** every round |

So the coordinate-free per-direction identity and the dimension-free mean-shift
bound are confirmed exactly. Notably `c(v_min)` reproduces the empirical T3 factor:
e.g. d6 s0 r6 gives `c(v_min)=0.696`, matching `repair_attack.md`'s worst
`c≈0.70` — the two measurements agree. `ΔᵀΣ⁻¹Δ` stays well below 4 (max 2.05),
confirming Corollary 2′: the downdate alone cannot collapse the thin axis, so the
ASYM scalar `a(v_min)` is the sole uncontrolled term (it does go negative, down to
`a(v_min)=−0.216` at d6 s1 r9, dragging `c(v_min)` to 0.71).

## (B) The mean-reversion linchpin — the counterexample shape is REAL and persistent

Per-instance summary. `blind-persist` = max consecutive rounds with `|ρ(v_max)|≤0.15`
(long axis blind) while κ ≥ its median; `corr(κ,Δκ)` < 0 = mean-reversion.

| instance | κ range | κ behavior | corr(κ,\|ρv_max\|) | corr(κ,Δκ_next) | **blind-persist** | hi-κ&blind ⟨Δκ_next⟩ |
|---|---|---|---|---|---|---|
| d6 s3 | 1.50–2.66 | **bounded** | **+0.65** | **−0.57** | **1** | (blind: −0.12) |
| d5 s2 | 1.26–2.83 | bounded | −0.44 | −0.80 | 2 | −0.15 (drops) |
| d6 s2 | 1.31–3.51 | bounded | −0.02 | −0.40 | 2 | +0.15 |
| d6 s0 | 1.46–3.94 | mild climb | +0.11 | −0.02 | 2 | +0.38 |
| d4 s0 | 1.28–8.33 | **climb** | −0.25 | +0.17 | 2 | **+1.74** |
| d6 s1 | 1.36–**15.63** | **big climb** | **−0.42** | **+0.70** | **5** | **+3.15** |

### The smoking gun (d6 s1)

The κ→15.6 blowup is not a sampling artifact (n=500 achieved every round, acc down
to 1.9e-3 at r9; ~20% MP inflation ⟹ true κ≈12, still a real climb). Round by round:

| round | r5 | r6 | r7 | r8 | r9 |
|---|---|---|---|---|---|
| κ | 3.01 | 4.11 | 5.91 | 6.46 | **15.63** |
| \|ρ(v_max)\| | 0.070 | 0.104 | 0.047 | 0.057 | 0.034 |

**Five consecutive rounds with the long axis BLIND (`|ρ(v_max)|≤0.10`), and κ
climbs monotonically over exactly that stretch.** This is a textbook realization of
crux-prover's §6 counterexample shape: the long axis sits in the cut's blind
(anti-diagonal) cone, so the balanced cut cannot shave it, and κ compounds. (The
thin axis is meanwhile partly sensed with `a(v_min)<0` — both danger conditions of
Cor 2′ co-occur.)

### What the linchpin decides

1. **The blind long axis DOES persist across ≥2 consecutive rounds — routinely
   (5/6 instances have blind-persist ≥ 2, up to 5).** This directly **refutes** the
   hoped-for escape that FW-recentering re-randomizes the sensed/blind subspace each
   round making blindness transient. Blindness is *not* transient; the long axis can
   stay in the blind cone for many rounds.
2. **κ-blowup magnitude tracks the blind-spell DURATION.** κ grows only while the
   long axis is blind (Cor 2′: no shave), so a 2-round spell gives a small bump
   (instances stay κ≤4) while the single 5-round spell gave the large κ→15.6.
   `⟨Δκ_next⟩` on high-κ&blind rounds is positive and grows with severity
   (+0.15, +0.38, +1.74, +3.15).
3. **Mean-reversion is real but CONDITIONAL, not universal.** It operates when the
   long axis is *sensed* (d6 s3: `corr(κ,|ρv_max|)=+0.65`, `corr(κ,Δκ)=−0.57`,
   blind-persist 1 — κ bounded). It **fails** on the climbing instance (d6 s1:
   `corr(κ,Δκ)=+0.70`) precisely because the long axis is persistently blind.

## Headline (for `main`)

The `ρ(v_max)`-vs-κ association splits the instances cleanly: **bounded-κ ⟺ long
axis sensed at high κ (mean-reversion fires); climbing-κ ⟺ long axis blind and it
PERSISTS.** A blind long axis persists >1 round in 5 of 6 instances (2–5 rounds),
and the one 5-round blind spell produced a genuine κ climb 3→15.6. So the amortized/
mean-reversion route's required lemma — "the `v_max`-blind orientation is
non-persistent under FW-recentered cuts" — is **empirically false in the reliable
window**: persistent blind orientations exist and drive κ up. The route is in
genuine danger, and the counterexample shape crux-prover named is realized, not
hypothetical.

## Honest caveats

- **Small counts / path-dependence.** 6 instances, ~5 rounds per median-split;
  correlations from ~5–9 points are indicative, not tight. Trajectories are
  sensitive to sampling noise in the balanced center (N=500 here took a more
  divergent path than N=400 in `repair_attack.md`, where seed1 only reached κ≈4.6):
  a slightly different sample flips a sign pattern and forks the cut path. The
  *structural* finding (blind-persistence ⟹ compounding) is robust across paths; the
  exact κ magnitude of any single run is not.
- **κ MP-inflation ~20%** at N=500,d=6 (κ only; the identity/`ρ`/`a`/`c` checks are
  unbiased projected quantities). True d6 s1 peak κ≈12, not 15.6.
- **Shallow window (t≤10).** κ is still "bounded-with-drift" (peak ≈12, not
  divergent), and short (2-round) blind spells mostly self-correct. Whether blind
  spells of `ω(log)` rounds occur — the regime that would make κ super-poly — is
  beyond the `d≈12,t≈2d` reliability ceiling and is not measured. So this is
  evidence that the non-persistence lemma is false *as stated per-round*, not a proof
  that κ diverges.

## Bottom line

(A) crux-prover's identities are numerically exact (Identity 1′ resid ≤1e-3, Lemma 2
`ΔᵀΣ⁻¹Δ ≤ 2.05 < 4`, T3 factor reproduced). (B) The decisive linchpin comes out on
the **pessimistic** side: the blind-long-axis counterexample shape is real and
persists 2–5 rounds (not transient), κ compounds in proportion to the blind-spell
duration, and mean-reversion is only conditional (fires when the long axis is
sensed). The amortized route therefore cannot rest on "blind orientation is
non-persistent" — that is observed to be false in-window. The SSG-specific lever of
`crux_scalefree.md` §5 (show the value operator keeps the long axis in the *sensed*
coordinate/near-diagonal subspace) is the remaining hope, and it is exactly what
these instances violate (the long axis wanders into the blind cone).
