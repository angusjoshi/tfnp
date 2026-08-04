/-
Copyright (c) 2026 Angus Joshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Angus Joshi
-/
import Tfnp.HitRun

/-!
# Realizability: every pairwise-consistent history is a real contraction

Companion to `notes/adversarial_components.md`. The open conjectures about the
balanced-cut algorithm ((★) of `notes/FINAL_REPORT.md`, the star-cover bound of
`notes/star_cover.md`) quantify over *realizable* trajectories — cut histories
produced by an actual `ℓ∞`-contraction. This file makes "realizable" a finite,
checkable condition:

* `mcShaneExt` — the coordinatewise McShane extension of query/response data
  `(c r, w r)` over a finite index type: `F y i = min_r (w r i + λ‖y − c r‖∞)`.
  This is the finite-set Kirszbraun property of `ℓ∞` (a hyperconvex space):
  a partial λ-contraction extends to a **total** one with the same constant.

* `mcShaneExt_lipschitz` — the extension is λ-Lipschitz in `linfDist`
  everywhere (not just on the cube).

* `mcShaneExt_interpolates` — under the pairwise conditions
  `‖w r − w q‖∞ ≤ λ‖c r − c q‖∞`, the extension agrees with the data.

* `realizable_of_pairwise` — the packaged result: if moreover each `w r` lies
  in the unit cube and `0 ≤ λ < 1`, there is an `f` with
  `IsLInfContraction f λ` and `f (c r) = w r` for every `r` — obtained by
  clamping the extension to the cube, which fixes the data pointwise.

* `realizable_cuts_retain_fixedPoint` — the geometric payoff: any such history
  in the open cube with `w r ≠ c r` admits a fixed point `x*` lying in **every**
  apex cut `⋃_{i : sᵢ ≠ 0} 𝒫ᵢ(c r, s r)`, `s r = sgn(w r − c r)`. So the
  candidate body of a pairwise-consistent history is nonempty, whatever the
  history — no explicit fixed point or game is needed to certify a trajectory.

Consequence for the research programme: "realizable trajectory" = a finite
system of `ℓ∞` interpolation inequalities, which **decouple per coordinate**
(each `|w r i − w q i| ≤ λ‖c r − c q‖∞` involves one coordinate of `w`). The
adversary's per-round freedom is a per-coordinate interval of displacements —
the object `notes/polytime_experiments/adversary_game.py` searches over, and
the constraint system an eventual proof of (★) has to exploit.
-/

set_option autoImplicit false

namespace Tfnp.Contraction

variable {k : ℕ} [NeZero k]

section McShane

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The coordinatewise McShane extension of the finite data `(c r, w r)`:
`F y i = min_r (w r i + λ‖y − c r‖∞)`. -/
noncomputable def mcShaneExt (c w : ι → Vec k) (lam : ℝ) : Vec k → Vec k :=
  fun y i =>
    Finset.univ.inf' Finset.univ_nonempty (fun r => w r i + lam * linfDist y (c r))

lemma mcShaneExt_le (c w : ι → Vec k) (lam : ℝ) (y : Vec k) (i : Fin k) (r : ι) :
    mcShaneExt c w lam y i ≤ w r i + lam * linfDist y (c r) :=
  Finset.inf'_le _ (Finset.mem_univ r)

lemma le_mcShaneExt {c w : ι → Vec k} {lam : ℝ} {y : Vec k} {i : Fin k} {a : ℝ}
    (h : ∀ r, a ≤ w r i + lam * linfDist y (c r)) :
    a ≤ mcShaneExt c w lam y i :=
  Finset.le_inf' _ _ fun r _ => h r

lemma exists_eq_mcShaneExt (c w : ι → Vec k) (lam : ℝ) (y : Vec k) (i : Fin k) :
    ∃ r, mcShaneExt c w lam y i = w r i + lam * linfDist y (c r) := by
  obtain ⟨r, _, hr⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := ι))
    (fun r => w r i + lam * linfDist y (c r))
  exact ⟨r, hr⟩

/-- **The extension is a global λ-Lipschitz map** in `linfDist`: the minimum of
λ-Lipschitz functions is λ-Lipschitz, coordinatewise, hence in the sup metric. -/
theorem mcShaneExt_lipschitz (c w : ι → Vec k) {lam : ℝ} (hlam : 0 ≤ lam)
    (y z : Vec k) :
    linfDist (mcShaneExt c w lam y) (mcShaneExt c w lam z) ≤ lam * linfDist y z := by
  refine linfDist_le fun i => ?_
  rw [abs_sub_le_iff]
  constructor
  · -- F y i − F z i ≤ λ d(y,z), via the minimiser at z
    obtain ⟨r, hr⟩ := exists_eq_mcShaneExt c w lam z i
    have h1 : mcShaneExt c w lam y i ≤ w r i + lam * linfDist y (c r) :=
      mcShaneExt_le c w lam y i r
    have h2 : linfDist y (c r) ≤ linfDist y z + linfDist z (c r) :=
      linfDist_triangle _ _ _
    have h3 : lam * linfDist y (c r) ≤ lam * linfDist y z + lam * linfDist z (c r) := by
      nlinarith
    linarith [hr, h1]
  · -- symmetric direction
    obtain ⟨r, hr⟩ := exists_eq_mcShaneExt c w lam y i
    have h1 : mcShaneExt c w lam z i ≤ w r i + lam * linfDist z (c r) :=
      mcShaneExt_le c w lam z i r
    have h2 : linfDist z (c r) ≤ linfDist z y + linfDist y (c r) :=
      linfDist_triangle _ _ _
    have h3 : lam * linfDist z (c r) ≤ lam * linfDist z y + lam * linfDist y (c r) := by
      nlinarith
    have h4 : linfDist z y = linfDist y z := linfDist_comm _ _
    rw [h4] at h3
    linarith [hr, h1]

/-- **Interpolation.** Under the pairwise conditions
`‖w r − w q‖∞ ≤ λ‖c r − c q‖∞`, the extension agrees with the data. -/
theorem mcShaneExt_interpolates {c w : ι → Vec k} {lam : ℝ}
    (hpair : ∀ r q, linfDist (w r) (w q) ≤ lam * linfDist (c r) (c q)) (q : ι) :
    mcShaneExt c w lam (c q) = w q := by
  funext i
  refine le_antisymm ?_ (le_mcShaneExt fun r => ?_)
  · have h := mcShaneExt_le c w lam (c q) i q
    have h0 : linfDist (c q) (c q) = 0 := by
      rw [linfDist_eq_dist]; exact dist_self _
    rw [h0, mul_zero, add_zero] at h
    exact h
  · -- `w q i ≤ w r i + λ‖c q − c r‖`, from the pairwise condition at coordinate `i`
    have habs : |w q i - w r i| ≤ linfDist (w q) (w r) := abs_sub_le_linfDist _ _ i
    have h := (habs.trans (hpair q r))
    have h2 := abs_le.mp h
    linarith [h2.1, h2.2]

/-- **Realizability.** Pairwise-consistent data with responses in the unit cube
is realized by an actual `ℓ∞`-contraction: there is `f` with
`IsLInfContraction f λ` and `f (c r) = w r` for every `r`.

`f` is the McShane extension clamped to the cube; clamping is nonexpansive and
fixes the (in-cube) data. This is the finite Kirszbraun property of `ℓ∞`, and it
converts "there exists a contraction consistent with this query history" into a
finite system of inequalities that decouple per coordinate. -/
theorem realizable_of_pairwise {c w : ι → Vec k} {lam : ℝ}
    (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    (hpair : ∀ r q, linfDist (w r) (w q) ≤ lam * linfDist (c r) (c q))
    (hwcube : ∀ r, InUnitCube (w r)) :
    ∃ f : Vec k → Vec k,
      IsLInfContraction f lam ∧ ∀ r, f (c r) = w r := by
  refine ⟨fun y => clampBox 0 1 (mcShaneExt c w lam y), ⟨?_, hlam0, hlam1, ?_⟩, ?_⟩
  · intro x _ i
    exact Set.mem_Icc.mpr (clampBox_mem 0 1 (by norm_num) _ i)
  · intro x y _ _
    exact (linfDist_clampBox_mono 0 1 _ _).trans (mcShaneExt_lipschitz c w hlam0 x y)
  · intro r
    show clampBox 0 1 (mcShaneExt c w lam (c r)) = w r
    rw [mcShaneExt_interpolates hpair r]
    exact clampBox_eq_self fun i => Set.mem_Icc.mp (hwcube r i)

/-- **Geometric payoff: pairwise-consistent histories have nonempty candidate
bodies.** Given pairwise-consistent data `(c r, w r)` with apexes in the cube,
responses in the cube and `w r ≠ c r`, there is a single point `xs` (a fixed
point of the realizing contraction) that lies in **every** apex cut
`⋃_{i : sᵢ ≠ 0} 𝒫ᵢ(c r, s r)` with `s r i = sgn(w r i − c r i)`.

So an adversary who answers queries subject only to the finite pairwise
inequalities can never be caught out: some genuine contraction stands behind
the answers, and its fixed point survives all the cuts. -/
theorem realizable_cuts_retain_fixedPoint {c w : ι → Vec k} {lam : ℝ}
    (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    (hpair : ∀ r q, linfDist (w r) (w q) ≤ lam * linfDist (c r) (c q))
    (hccube : ∀ r, InUnitCube (c r)) (hwcube : ∀ r, InUnitCube (w r))
    (hne : ∀ r, w r ≠ c r) :
    ∃ xs : Vec k, InUnitCube xs ∧
      ∀ r, xs = c r ∨ xs ∈ PyrUnion (fun i => sgnR (w r i - c r i)) (c r) := by
  obtain ⟨f, hf, hinterp⟩ :=
    realizable_of_pairwise hlam0 hlam1 hpair hwcube
  obtain ⟨xs, hxs_cube, hxs_fix⟩ :=
    exists_fixedPoint_of_contraction hf.preserves_cube hlam0 hlam1 hf.contracts
  refine ⟨xs, hxs_cube, fun r => ?_⟩
  by_cases hxc : xs = c r
  · exact Or.inl hxc
  · refine Or.inr ?_
    have := fixedPoint_mem_pyrUnion_apex hf (hccube r) hxs_cube hxs_fix hxc
      (s := fun i => sgnR (f (c r) i - c r i)) (fun i => rfl)
    have he : (fun i => sgnR (f (c r) i - c r i))
        = fun i => sgnR (w r i - c r i) := by
      funext i; rw [hinterp r]
    exact he ▸ this

end McShane

end Tfnp.Contraction
