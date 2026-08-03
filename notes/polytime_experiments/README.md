# Poly-time `ℓ∞`-contraction experiments

Supporting code for `notes/polytime.md` §3.3. Needs `numpy`, `scipy`.

```
python3 -m venv venv && ./venv/bin/pip install numpy scipy
```

- `verify_kernel.py` — verifies the membership test `y∈K ⟺ max+min ≥ 0` and the
  **Kernel Theorem** `ker(K) = {z : all pairwise w-sums ≥ 0}` (ray re-entry test).
- `starshape_collapse.py` — runs balanced cuts, shows the kernel polytope
  (`⋂_r ker`) collapses: star-shapedness is unmaintainable past ~O(d) rounds.
- `algo_linear.py  <d> <rounds> <lambda>` — the candidate algorithm
  (hit-and-run sampling + Fermat–Weber balanced-point LP) on **linear**
  contractions. Clean geometric, λ-independent convergence.
  e.g. `python algo_linear.py 4 40 0.9999999`
- `algo_topical.py <d> <rounds> <delta> [seed]` — same algorithm on **hard**
  piecewise-linear topical (Shapley/SSG-style min/max/avg) contractions, with the
  essential **ternary** sign cut. Progress + good approximate fixed points, but
  convergence to `x*` is slower/noisier (the mixing question surfacing).
  e.g. `python algo_topical.py 4 45 1e-4`

Bottom line: the open problem reduces to **rapid mixing of hit-and-run on an
intersection of `ℓ∞` pyramid-unions**. See `notes/polytime.md` §3.3.

## Isoperimetry attack (see `notes/isoperimetry_attack.md`)

Scripts added while attacking the Open Lemma. All import `common.py` (SSG/topical
instances, ternary cuts, hit-and-run, Fermat–Weber LP, whitening, isotropic
1-D-marginal Cheeger). Run under `venv`.

- `verify_thmA.py` — machine-checks **Theorem A**: cuts pointing toward `x*`
  (`s_i(x*_i−c_i)≥0`) make `X_t` star-shaped about `x*` (0 failures vs thousands
  for arbitrary signs).
- `barrier.py`, `compat_search.py`, `honest_barrier.py` — barrier searches over
  hand-designed / realizable-structure cut families using **exact rejection**
  uniform sampling → ground-truth Cheeger. Finding: healthy-volume ⟹ `Ω(1)`
  isotropic Cheeger; small Cheeger only on non-realizable slivers.
- `ssg_probe.py`, `mixing_test.py` — the real algorithm on **SSG** instances
  (spread `x*`), with extreme-start trapping and isotropic Cheeger.
- `radial_delta.py` — `δ`-sweep (hard `λ→1` regime) and the radial/"bad
  viewpoint" test.
- `escalate.py` — budget-escalation control proving the `d=12` "trapping" is a
  **sampler artifact**, not a bottleneck (TRAP `0.23→0.085→0.038`).

Methodological caution: judge bottlenecks by **isotropic** Cheeger and
**budget-escalated** trapping, never raw Cheeger (flags elongation) or a
fixed-budget walk (flags slow mixing).
