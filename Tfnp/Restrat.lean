/-
Copyright (c) 2026 Angus Joshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Angus Joshi
-/
import Tfnp.Shed

/-!
# Re-stratification confinement: the tied pair is a robust invariant

The multi-scale gap flagged in the cycle-29 audit (`notes/HANDOFF.md` §7.1):
the 2-simple ledger was proved in the fixed-reference, fixed-dispersion
regime, and the obstacle to making it scale-free is *re-stratification* — a
tracked point's tied pair changing between scale-epochs, which would let the
per-epoch cell records multiply instead of telescope. Here we prove that this
cannot happen outside a doubled-scale collar, by a purely discrete
triangle-inequality argument (no continuity, no interpolation):

* `collar_of_near_top` — **the transition atom**: if a coordinate comes
  within `2δ` of a point's `ℓ∞`-top at any apex within `δ` of `c`, then it
  was already within `4δ` of the top at `c` itself. Approaching the tie
  front at the working scale requires having been in the collar at the
  doubled scale — a coordinate cannot enter the tie from cold.
* `tie_mem_pair_of_robust` — **tie confinement**: a point whose pair
  `{i₁, i₂}` dominates every other coordinate by more than `4δ` cannot have
  any third coordinate within `2δ` of its top at any apex within `δ`. The
  tied pair of robustly 2-simple mass is *invariant* under apex perturbation.
* `pair_invariant_of_robust` — **the trajectory corollary (re-stratification
  no-split)**: along an entire trajectory of apexes within `δ` of a
  reference, a `4δ`-robust point's tie set and all its pyramid memberships
  stay confined to its pair. With `pair_membership_iff` (`Tfnp/Walk.lean`),
  the point's whole cut record is then the walk pattern of the *single* form
  `φ_ψ` of its (invariant) pair: the pair-record theorem holds scale-free on
  the robust stratum.

**Consequence for the ledger (paper-level, `notes/CHAIN.md` cycle 31):** the
per-epoch 2-simple ledgers telescope additively over the robust stratum —
re-stratification, the failure mode that threatened a multiplicative
cross-epoch blow-up, is confined to the `[2δ, 4δ]` collar of the tie front.
The remaining unfenced mass is exactly the 3-tie collar (the deep stratum's
gate), not the 2-simple bulk.
-/

set_option autoImplicit false

namespace Tfnp.Contraction

variable {k : ℕ} [NeZero k]

/-- The `ℓ∞` top offset is attained at some coordinate. -/
lemma exists_linfDist_eq (x y : Vec k) :
    ∃ i, |x i - y i| = linfDist x y := by
  have hne : (Finset.univ : Finset (Fin k)).Nonempty :=
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne k)⟩, Finset.mem_univ _⟩
  unfold linfDist
  rw [dif_pos hne]
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' hne (fun j => |x j - y j|)
  exact ⟨i, hi.symm⟩

/-- Moving the apex by `δ` lowers the top offset by at most `δ`. -/
lemma linfDist_le_linfDist_add_of_move {c c' y : Vec k} {δ : ℝ}
    (hδ : linfDist c' c ≤ δ) :
    linfDist y c ≤ linfDist y c' + δ := by
  refine linfDist_le fun i => ?_
  have h1 : |y i - c i| ≤ |y i - c' i| + |c' i - c i| := by
    calc |y i - c i| = |(y i - c' i) + (c' i - c i)| := by ring_nf
      _ ≤ |y i - c' i| + |c' i - c i| := abs_add_le _ _
  have h2 : |y i - c' i| ≤ linfDist y c' := abs_sub_le_linfDist y c' i
  have h3 : |c' i - c i| ≤ δ := (abs_sub_le_linfDist c' c i).trans hδ
  linarith

/-- **The transition atom.** If at some apex `c'` within `δ` of `c` the
coordinate `m` is within `2δ` of the point's top offset, then at `c` itself
`m` was already within `4δ` of the top. A coordinate cannot approach the tie
front at scale `2δ` without having been inside the `4δ` collar one apex-step
earlier: tie membership has no cold entries. -/
theorem collar_of_near_top {c c' y : Vec k} {δ : ℝ}
    (hδ : linfDist c' c ≤ δ)
    {m : Fin k} (hm : linfDist y c' ≤ |y m - c' m| + 2 * δ) :
    linfDist y c ≤ |y m - c m| + 4 * δ := by
  have h1 : linfDist y c ≤ linfDist y c' + δ := linfDist_le_linfDist_add_of_move hδ
  have h2 : |y m - c' m| ≤ |y m - c m| + δ := by
    have ha : |y m - c' m| ≤ |y m - c m| + |c m - c' m| := by
      calc |y m - c' m| = |(y m - c m) + (c m - c' m)| := by ring_nf
        _ ≤ |y m - c m| + |c m - c' m| := abs_add_le _ _
    have hb : |c m - c' m| ≤ δ := by
      rw [abs_sub_comm]; exact (abs_sub_le_linfDist c' c m).trans hδ
    linarith
  linarith

/-- **Tie confinement.** If `y`'s pair `{i₁, i₂}` dominates every other
coordinate by more than `4δ` at apex `c` (robust 2-simplicity), then at every
apex within `δ`, every coordinate within `2δ` of `y`'s top belongs to the
pair: the tied pair cannot change while robustness holds. Re-stratification
of the 2-simple stratum is confined to the doubled-scale collar. -/
theorem tie_mem_pair_of_robust {c c' y : Vec k} {i₁ i₂ : Fin k} {δ : ℝ}
    (hδ : linfDist c' c ≤ δ)
    (hgap : ∀ m, m ≠ i₁ → m ≠ i₂ → |y m - c m| + 4 * δ < linfDist y c)
    {m : Fin k} (hm : linfDist y c' ≤ |y m - c' m| + 2 * δ) :
    m = i₁ ∨ m = i₂ := by
  by_contra hcon
  push_neg at hcon
  exact absurd (collar_of_near_top hδ hm)
    (not_le.mpr (hgap m hcon.1 hcon.2))

/-- Under the `4δ`-robustness gap, the top offset is attained on the pair:
`max (|y i₁ - c i₁|) (|y i₂ - c i₂|) = linfDist y c`. -/
lemma max_pair_eq_linfDist_of_robust {c y : Vec k} {i₁ i₂ : Fin k} {δ : ℝ}
    (hδ0 : 0 ≤ δ)
    (hgap : ∀ m, m ≠ i₁ → m ≠ i₂ → |y m - c m| + 4 * δ < linfDist y c) :
    max (|y i₁ - c i₁|) (|y i₂ - c i₂|) = linfDist y c := by
  obtain ⟨m₀, hm₀⟩ := exists_linfDist_eq y c
  have hmem : m₀ = i₁ ∨ m₀ = i₂ := by
    by_contra hcon
    push_neg at hcon
    have := hgap m₀ hcon.1 hcon.2
    rw [hm₀] at this
    linarith
  refine le_antisymm (max_le (abs_sub_le_linfDist y c i₁)
    (abs_sub_le_linfDist y c i₂)) ?_
  rcases hmem with rfl | rfl
  · exact hm₀ ▸ le_max_left _ _
  · exact hm₀ ▸ le_max_right _ _

/-- **Pair invariance along a trajectory — the re-stratification no-split
theorem.** If `y`'s pair dominates all other coordinates by more than `4δ` at
a reference point, then along an entire trajectory of apexes within `δ` of
the reference: (i) every coordinate within `2δ` of `y`'s top is in the pair,
and (ii) every pyramid of every cut containing `y` has index in the pair.
The tied pair of the robust 2-simple stratum is a trajectory invariant; with
`pair_membership_iff`, the point's whole record is the walk of one form. -/
theorem pair_invariant_of_robust {ι : Type*} {cstar : Vec k} {δ : ℝ}
    {cs : ι → Vec k} (hδ : ∀ r, linfDist (cs r) cstar ≤ δ)
    {y : Vec k} {i₁ i₂ : Fin k}
    (hgap : ∀ m, m ≠ i₁ → m ≠ i₂ → |y m - cstar m| + 4 * δ < linfDist y cstar)
    (hgap0 : 4 * δ < linfDist y cstar) :
    ∀ r : ι,
      (∀ m, linfDist y (cs r) ≤ |y m - cs r m| + 2 * δ → m = i₁ ∨ m = i₂) ∧
      (∀ (j : Fin k) (τ : ℝ), (τ = 1 ∨ τ = -1) → y ∈ Pyr j τ (cs r) →
        j = i₁ ∨ j = i₂) := by
  intro r
  have hδ0 : 0 ≤ δ := le_trans (linfDist_nonneg (cs r) cstar) (hδ r)
  have hmax : max (|y i₁ - cstar i₁|) (|y i₂ - cstar i₂|) = linfDist y cstar :=
    max_pair_eq_linfDist_of_robust hδ0 hgap
  constructor
  · exact fun m hm => tie_mem_pair_of_robust (hδ r) hgap hm
  · intro j τ hτ hmem
    refine pyr_index_mem_pair_of_2simple (hδ r) ?_ ?_ hτ hmem
    · intro m hm₁ hm₂
      rw [hmax]
      have := hgap m hm₁ hm₂
      linarith
    · rw [hmax]; linarith

/-- **Collar kinematics: the top-gap is 2-Lipschitz in the apex.** For every
coordinate `m`, an apex step of `ℓ∞`-size `δ` moves the gap
`linfDist y c − |y m − c m|` by at most `2δ`. Strengthens the transition
atom (`collar_of_near_top` is the one-sided consequence): with steps ≤ δ a
lineage cannot jump the `[2δ, 4δ]` band in one round, so **every entry into
the tie (gap ≤ 2δ) is preceded by at least one full round of residence in
the collar** — collar entries are well-defined, tolled events, and the
front-birth question becomes: how many tolled entries can the balanced-cut
dynamics afford per lineage? -/
theorem gap_lipschitz {c c' y : Vec k} {δ : ℝ} (hδ : linfDist c' c ≤ δ)
    (m : Fin k) :
    |(linfDist y c' - |y m - c' m|) - (linfDist y c - |y m - c m|)| ≤ 2 * δ := by
  have h1 : linfDist y c ≤ linfDist y c' + δ := linfDist_le_linfDist_add_of_move hδ
  have h2 : linfDist y c' ≤ linfDist y c + δ := by
    refine linfDist_le_linfDist_add_of_move ?_
    rw [linfDist_comm]; exact hδ
  have hb : |c m - c' m| ≤ δ := by
    rw [abs_sub_comm]; exact (abs_sub_le_linfDist c' c m).trans hδ
  have h3 : |y m - c' m| ≤ |y m - c m| + δ := by
    have ha : |y m - c' m| ≤ |y m - c m| + |c m - c' m| := by
      calc |y m - c' m| = |(y m - c m) + (c m - c' m)| := by ring_nf
        _ ≤ |y m - c m| + |c m - c' m| := abs_add_le _ _
    linarith
  have h4 : |y m - c m| ≤ |y m - c' m| + δ := by
    have ha : |y m - c m| ≤ |y m - c' m| + |c' m - c m| := by
      calc |y m - c m| = |(y m - c' m) + (c' m - c m)| := by ring_nf
        _ ≤ |y m - c' m| + |c' m - c m| := abs_add_le _ _
    have hb' : |c' m - c m| ≤ δ := (abs_sub_le_linfDist c' c m).trans hδ
    linarith
  rw [abs_le]
  constructor <;> linarith

/-- **Tie-set confinement at every depth (the m-ary atom).** If the
coordinates of `M` dominate every coordinate outside `M` by more than `4δ`
at apex `c`, then at every apex within `δ`, every coordinate within `2δ` of
the top belongs to `M`: the tie SET of robustly `m`-tied mass is invariant
under apex perturbation, at every level of the trichotomy hierarchy. -/
theorem tie_mem_mset_of_robust {c c' y : Vec k} {M : Finset (Fin k)} {δ : ℝ}
    (hδ : linfDist c' c ≤ δ)
    (hgap : ∀ m, m ∉ M → |y m - c m| + 4 * δ < linfDist y c)
    {m : Fin k} (hm : linfDist y c' ≤ |y m - c' m| + 2 * δ) :
    m ∈ M := by
  by_contra hcon
  exact absurd (collar_of_near_top hδ hm) (not_le.mpr (hgap m hcon))

/-- Under the `4δ`-robustness gap, the top offset is attained on `M`. -/
lemma msup_eq_linfDist_of_robust {c y : Vec k} {M : Finset (Fin k)}
    (hM : M.Nonempty) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hgap : ∀ m, m ∉ M → |y m - c m| + 4 * δ < linfDist y c) :
    (M.sup' hM fun i => |y i - c i|) = linfDist y c := by
  obtain ⟨m₀, hm₀⟩ := exists_linfDist_eq y c
  have hmem : m₀ ∈ M := by
    by_contra hcon
    have := hgap m₀ hcon
    rw [hm₀] at this
    linarith
  refine le_antisymm (Finset.sup'_le _ _ fun i _ => abs_sub_le_linfDist y c i) ?_
  exact hm₀ ▸ Finset.le_sup' (f := fun i => |y i - c i|) hmem

/-- **Tie-set invariance along a trajectory, at every depth.** If `y`'s
coordinate set `M` dominates all others by more than `4δ` at a reference
point, then along an entire trajectory of apexes within `δ`: (i) every
coordinate within `2δ` of `y`'s top is in `M`, and (ii) every pyramid of
every cut containing `y` has index in `M` (via `pyr_index_mem_of_mset`).
The stratification's tie sets are robust trajectory invariants level by
level; only collar mass (within `4δ` of a deeper tie) can migrate between
strata of the trichotomy. -/
theorem mset_invariant_of_robust {ι : Type*} {cstar : Vec k} {δ : ℝ}
    {cs : ι → Vec k} (hδ : ∀ r, linfDist (cs r) cstar ≤ δ)
    {y : Vec k} {M : Finset (Fin k)} (hM : M.Nonempty)
    (hgap : ∀ m, m ∉ M → |y m - cstar m| + 4 * δ < linfDist y cstar)
    (hgap0 : 4 * δ < linfDist y cstar) :
    ∀ r : ι,
      (∀ m, linfDist y (cs r) ≤ |y m - cs r m| + 2 * δ → m ∈ M) ∧
      (∀ (j : Fin k) (τ : ℝ), (τ = 1 ∨ τ = -1) → y ∈ Pyr j τ (cs r) →
        j ∈ M) := by
  intro r
  have hδ0 : 0 ≤ δ := le_trans (linfDist_nonneg (cs r) cstar) (hδ r)
  have hsup : (M.sup' hM fun i => |y i - cstar i|) = linfDist y cstar :=
    msup_eq_linfDist_of_robust hM hδ0 hgap
  constructor
  · exact fun m hm => tie_mem_mset_of_robust (hδ r) hgap hm
  · intro j τ hτ hmem
    refine pyr_index_mem_of_mset hM (hδ r) ?_ ?_ hτ hmem
    · intro m hm
      rw [hsup]
      have := hgap m hm
      linarith
    · rw [hsup]; linarith

end Tfnp.Contraction
