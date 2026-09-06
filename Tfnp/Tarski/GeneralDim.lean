/-
Copyright (c) 2026 Angus Joshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Angus Joshi
-/
import Tfnp.Tarski.LevelsetSearch
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The levelset configuration argument in every dimension

`Tfnp/Tarski/LevelsetSearch.lean` proves Haslebacher–Lill's Lemma 3.12 in dimension
three, via `fin3_config_exists`: a case analysis producing a first or a second
configuration among the bounding points.  This file replaces that case analysis
with a single argument valid in **every** dimension.

## Why this matters

`levelsetOuter` (HL Lemma 3.2, proved) turns a levelset subprocedure making `q`
queries into a `Tarski(n,d)` algorithm making `O(log n · q)` queries, in *any*
dimension — a levelset cut halves `boxSize` as a whole, so there are only
`O(log n)` outer rounds however large `d` is.  So

  `LEVELSET(d) ∈ O_d(log n)`  ⟹  `Tarski(n,d) ∈ O_d(log² n)`,

which would match the `Ω̃(d log² n)` lower bound of Brânzei–Phillips–Recker, and is
the whole content of the fixed-parameter question.  Of HL's `d = 3` subprocedure,
every ingredient is dimension-uniform except two: the sign trichotomy
`up_or_down_or_iUpDown`, and this configuration argument.  The latter is dealt with
here; see the note at the end of the file for what remains.

## The argument

Write `ℓ_j = u⁽ʲ⁾_j` for the lower corner.  Since every bounding point lies on the
levelset, `lev u⁽ⁱ⁾ = κ`, and being stuck forces `κ ≤ lev ℓ + 1`; together these say

  `Σ_j u⁽ⁱ⁾_j ≤ (Σ_j ℓ_j) + 1`  for every `i`.

The meet of a subfamily `T` is a `Down` point as soon as every coordinate has a
member of `T` that is weakly down there *and* attains the meet, which amounts to
`∃ t ∈ T \ {l}` with `u⁽ᵗ⁾_l ≤ ℓ_l`.  `exists_covering` says such a `T` always
exists: otherwise one may peel off, from each subfamily, an element strictly
exceeded by all the others, and the last survivor exceeds everyone — a row with
`d − 1 ≥ 2` strict excesses, contradicting the row bound.

Two remarks.  The proof is a short induction, uniform in `d`, where HL's `d = 3`
argument is a fixed-point-free-map / 3-cycle analysis.  And the hypothesis is the
row *sum* bound, not "at most one excess per row": at `d ≥ 4` a row may well carry
two excesses offset by a deficit, so the `d = 3` phrasing does not generalize even
though the conclusion does.

## Main results

* `exists_covering` — the combinatorial core, in every dimension.
* `exists_meet_progress` — **HL Observations 3.9/3.10 and Lemma 3.12's upward core,
  unified and generalized**: the bounding points always yield a `Down` point at
  level at most `κ`, or a witnessed violation of order preservation.
-/

namespace Tfnp.Tarski

variable {d : ℕ}

/-! ### The combinatorial core -/

/-- **The covering lemma, in every dimension.**  If no row of `w` exceeds the
diagonal row-sum by more than one, then some subfamily `T` of size at least two has,
in each of its coordinates `l`, a member other than `l` that does not exceed the
diagonal entry `w l l` there.

At `d = 3` this subsumes HL's first and second configurations (`|T| = 2` and
`|T| = 3` respectively), and replaces `fin3_config_exists`. -/
theorem exists_covering (hd : 3 ≤ d) (w : Fin d → Fin d → ℕ)
    (hrow : ∀ i, ∑ j, w i j ≤ (∑ j, w j j) + 1) :
    ∃ T : Finset (Fin d), 2 ≤ T.card ∧ ∀ l ∈ T, ∃ t ∈ T.erase l, w t l ≤ w l l := by
  by_contra hcon
  push Not at hcon
  -- Peeling: every nonempty subfamily has a member exceeding all the others.
  have key : ∀ (n : ℕ) (T : Finset (Fin d)), T.card = n → T.Nonempty →
      ∃ a ∈ T, ∀ l ∈ T.erase a, w l l < w a l := by
    intro n
    induction n with
    | zero =>
      intro T hc hne
      rw [← Finset.card_pos, hc] at hne
      omega
    | succ m ih =>
      intro T hc hne
      rcases Nat.eq_zero_or_pos m with hm | hm
      · -- a singleton: the condition is vacuous
        subst hm
        obtain ⟨a, ha⟩ := hne
        refine ⟨a, ha, fun l hl => ?_⟩
        have h1 : (T.erase a).card = T.card - 1 := Finset.card_erase_of_mem ha
        have h2 : 0 < (T.erase a).card := Finset.card_pos.mpr ⟨l, hl⟩
        omega
      · obtain ⟨l₀, hl₀T, hl₀⟩ := hcon T (by omega)
        have hcard' : (T.erase l₀).card = m := by
          rw [Finset.card_erase_of_mem hl₀T, hc]; omega
        have hne' : (T.erase l₀).Nonempty := by
          rw [← Finset.card_pos, hcard']; omega
        obtain ⟨a, haT', ha⟩ := ih (T.erase l₀) hcard' hne'
        have hane : a ≠ l₀ := Finset.ne_of_mem_erase haT'
        refine ⟨a, Finset.mem_of_mem_erase haT', fun l hl => ?_⟩
        obtain ⟨hla, hlT⟩ := Finset.mem_erase.mp hl
        by_cases hll₀ : l = l₀
        · subst hll₀
          exact hl₀ a (Finset.mem_erase.mpr ⟨hane, Finset.mem_of_mem_erase haT'⟩)
        · exact ha l (Finset.mem_erase.mpr ⟨hla, Finset.mem_erase.mpr ⟨hll₀, hlT⟩⟩)
  -- The survivor's row is too big.
  have hne : (Finset.univ : Finset (Fin d)).Nonempty := by
    rw [← Finset.card_pos, Finset.card_univ, Fintype.card_fin]; omega
  obtain ⟨a, -, ha⟩ := key d Finset.univ (by simp) hne
  have hcard : ((Finset.univ : Finset (Fin d)).erase a).card = d - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, Fintype.card_fin]
  have h1 : ∑ l ∈ (Finset.univ : Finset (Fin d)).erase a, (w l l + 1)
      ≤ ∑ l ∈ (Finset.univ : Finset (Fin d)).erase a, w a l :=
    Finset.sum_le_sum fun l hl => by have := ha l hl; omega
  have h2 : ∑ l ∈ (Finset.univ : Finset (Fin d)).erase a, (w l l + 1)
      = (∑ l ∈ (Finset.univ : Finset (Fin d)).erase a, w l l)
        + ((Finset.univ : Finset (Fin d)).erase a).card := by
    rw [Finset.sum_add_distrib]; simp
  have h3 : ∑ j, w a j
      = w a a + ∑ l ∈ (Finset.univ : Finset (Fin d)).erase a, w a l :=
    (Finset.add_sum_erase _ (fun j => w a j) (Finset.mem_univ a)).symm
  have h4 : ∑ j, w j j
      = w a a + ∑ l ∈ (Finset.univ : Finset (Fin d)).erase a, w l l :=
    (Finset.add_sum_erase _ (fun j => w j j) (Finset.mem_univ a)).symm
  have h5 := hrow a
  omega

/-! ### The slack bound of HL Lemma 3.5, in every dimension

HL's deep query point sits `⌈diamᵢ/6⌉` from both ends in coordinate `i`, and the
level constraint is satisfiable because the slacks together consume at most the
largest diameter: `d · ⌈D/6⌉ ≤ D`.  That inequality holds at `d = 3` (given `D ≥ 6`)
but **fails for `d ≥ 6`**, so the constant `6` cannot simply be carried over.  Slack
`⌈diamⱼ/(2d)⌉` works in every dimension, as soon as the largest diameter is at least
`2d`; the shrink per cut is then a factor `1 − 1/(2d)` rather than `5/6`, which costs
only a `poly(d)` factor in the number of iterations. -/

/-- The generalized slack bound: `d` slacks of size `⌈Dⱼ/(2d)⌉` consume at most the
largest diameter. -/
theorem slack_sum_le {D : ℕ} (hd : 1 ≤ d) (hD : 2 * d ≤ D) (Dj : Fin d → ℕ)
    (hle : ∀ j, Dj j ≤ D) : ∑ j, (Dj j + 2 * d - 1) / (2 * d) ≤ D := by
  set m := (D + 2 * d - 1) / (2 * d) with hm
  have h1 : ∑ j, (Dj j + 2 * d - 1) / (2 * d) ≤ d * m := by
    calc ∑ j, (Dj j + 2 * d - 1) / (2 * d)
        ≤ ∑ _j : Fin d, m :=
          Finset.sum_le_sum fun j _ => Nat.div_le_div_right (by have := hle j; omega)
      _ = d * m := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            smul_eq_mul]
  have h2 : m * (2 * d) ≤ D + 2 * d - 1 := Nat.div_mul_le_self _ _
  have h3 : 2 * (d * m) = m * (2 * d) := by ring
  omega

/-! ### The meet of a subfamily -/

open Classical in
/-- The coordinatewise meet of the bounding points indexed by `T`. -/
noncomputable def infPt (T : Finset (Fin d)) (u : Fin d → Pt d) : Pt d :=
  fun l => if h : T.Nonempty then T.inf' h (fun t => u t l) else 0

lemma infPt_le {T : Finset (Fin d)} (hT : T.Nonempty) (u : Fin d → Pt d)
    {t : Fin d} (ht : t ∈ T) : infPt T u ≤ u t :=
  coord_le fun l => by
    simp only [infPt, dif_pos hT]
    exact Finset.inf'_le _ ht

lemma le_infPt {T : Finset (Fin d)} (hT : T.Nonempty) {u : Fin d → Pt d} {x : Pt d}
    (h : ∀ t ∈ T, x ≤ u t) : x ≤ infPt T u :=
  coord_le fun l => by
    simp only [infPt, dif_pos hT]
    exact Finset.le_inf' hT _ fun t ht => le_coord (h t ht) l

/-- The meet is attained, coordinate by coordinate. -/
lemma exists_infPt_eq {T : Finset (Fin d)} (hT : T.Nonempty) (u : Fin d → Pt d)
    (l : Fin d) : ∃ t ∈ T, infPt T u l = u t l := by
  simp only [infPt, dif_pos hT]
  exact Finset.exists_mem_eq_inf' hT _

/-! ### Progress from the bounding points -/

section Points

variable {F : Pt d → Pt d} {κ : ℕ} {u : Fin d → Pt d}

/-- **HL Observations 3.9/3.10 and Lemma 3.12's upward core, in every dimension.**
If each bounding point lies on the levelset and is weakly downward away from its own
coordinate, and the lower corner is within one level of `κ`, then some meet of
bounding points is a `Down` point at level at most `κ` — or one of the monotonicity
steps exhibits a violation of order preservation.

At `d = 3` this replaces `hasProgress_of_config1Up`, `hasProgress_of_config2Up` and
the upward half of `hasProgress_or_config3` all at once.  The downward statement is
the order dual. -/
theorem exists_meet_progress (hd : 3 ≤ d)
    (hlev : ∀ i, lev (u i) = κ) (hlow : κ ≤ lev (fun j => u j j) + 1)
    (hdown : ∀ t l, l ≠ t → F (u t) l ≤ u t l) :
    ∃ T : Finset (Fin d), T.Nonempty ∧ lev (infPt T u) ≤ κ ∧
      (infPt T u ∈ Down F ∨ ∃ t ∈ T, IsVop F (infPt T u) (u t)) := by
  -- the row bound is exactly `lev (u i) = κ ≤ lev ℓ + 1`
  have hrow : ∀ i, ∑ j, u i j ≤ (∑ j, u j j) + 1 := by
    intro i
    have h1 : ∑ j, u i j = κ := hlev i
    have h2 : lev (fun j => u j j) = ∑ j, u j j := rfl
    omega
  obtain ⟨T, hTcard, hT⟩ := exists_covering hd (fun i j => u i j) hrow
  have hTne : T.Nonempty := by rw [← Finset.card_pos]; omega
  obtain ⟨t₀, ht₀⟩ := id hTne
  refine ⟨T, hTne, ?_, ?_⟩
  · rw [← hlev t₀]
    exact lev_mono (infPt_le hTne u ht₀)
  -- in each coordinate, a member that is weakly down there and attains the meet
  have hwit : ∀ l, ∃ t ∈ T, F (u t) l ≤ infPt T u l := by
    intro l
    obtain ⟨s, hs, hseq⟩ := exists_infPt_eq hTne u l
    by_cases hsl : s = l
    · -- the meet at `l` is attained by `l` itself, so use the covering member
      subst hsl
      obtain ⟨t, ht, hle⟩ := hT s hs
      refine ⟨t, Finset.mem_of_mem_erase ht, ?_⟩
      have h1 := hdown t s (Ne.symm (Finset.ne_of_mem_erase ht))
      omega
    · exact ⟨s, hs, by have := hdown s l (Ne.symm hsl); omega⟩
  by_cases hmono : ∀ t ∈ T, F (infPt T u) ≤ F (u t)
  · refine Or.inl (mem_Down.mpr (coord_le fun l => ?_))
    obtain ⟨t, ht, hle⟩ := hwit l
    have h1 := le_coord (hmono t ht) l
    omega
  · push Not at hmono
    obtain ⟨t, ht, hbad⟩ := hmono
    exact Or.inr ⟨t, ht, infPt_le hTne u ht, hbad⟩

/-- **Progress from a crossing-free family, in every dimension.**  A far weaker
invariant than `exists_meet_progress`: no singleton-sign condition on the witnesses and
no level bound.  All that is asked is that the family be *crossing-free* — whenever a
member's `l`-coordinate is at most the `l`-th pin `p⁽ˡ⁾_l`, that member is strictly
down at `l`.

The point is a duality: a point failing to pin `l` from below is strictly up at `l`,
hence pins `l` from *above*, so it is numerically excluded as soon as the low and high
pins have not crossed.  Balanced sign patterns are therefore usable after all; what
obstructs progress is a *crossing*, not a sign pattern.

Note also that the family need not lie on the levelset: since `z ≤ p⁽ᵗ⁾` for every `t`,
`lev z ≤ minₜ lev p⁽ᵗ⁾`, so it is enough that **one** member has level at most `κ`.  The
witnesses may be drawn from anywhere in the box. -/
theorem meet_progress_of_no_crossing (hd : 0 < d) (p : Fin d → Pt d)
    (hlev : ∃ l, lev (p l) ≤ κ)
    (hcross : ∀ l t, (p t) l ≤ (p l) l → F (p t) l < (p t) l) :
    lev (infPt Finset.univ p) ≤ κ ∧
      (infPt Finset.univ p ∈ Down F ∨ ∃ t, IsVop F (infPt Finset.univ p) (p t)) := by
  have hTne : (Finset.univ : Finset (Fin d)).Nonempty :=
    ⟨⟨0, hd⟩, Finset.mem_univ _⟩
  refine ⟨?_, ?_⟩
  · obtain ⟨l₀, hl₀⟩ := hlev
    exact le_trans (lev_mono (infPt_le hTne p (Finset.mem_univ l₀))) hl₀
  by_cases hmono : ∀ t, F (infPt Finset.univ p) ≤ F (p t)
  · refine Or.inl (mem_Down.mpr (coord_le fun m => ?_))
    obtain ⟨s, -, hseq⟩ := exists_infPt_eq hTne p m
    -- the minimiser at `m` sits at or below the `m`-th pin, so it is strictly down there
    have hle : (p s) m ≤ (p m) m := by
      rw [← hseq]
      exact le_coord (infPt_le hTne p (Finset.mem_univ m)) m
    have h1 := hcross m s hle
    have h2 := le_coord (hmono s) m
    omega
  · push Not at hmono
    obtain ⟨t, hbad⟩ := hmono
    exact Or.inr ⟨t, infPt_le hTne p (Finset.mem_univ _), hbad⟩

end Points

/-! ### Consistency with the `d = 3` development

`exists_meet_progress` really does subsume the dimension-three argument: it reproves
the upward half of HL Lemma 3.12 from `LBounds` alone. -/

theorem hasProgress_of_lbounds_up {F : Pt 3 → Pt 3} {lo hi : Pt 3} {k : ℕ}
    (B : LBounds F lo hi k) (hlow : k ≤ lev B.lowC + 1) : HasProgress F lo hi k := by
  obtain ⟨T, hTne, hlevle, hcase⟩ :=
    exists_meet_progress (d := 3) (F := F) (u := B.u) (κ := k) (by omega) B.u_lev hlow
      (fun t l hl => (B.u_up t).2 l hl)
  have hmem : infPt T B.u ∈ Box lo hi := by
    obtain ⟨t₀, ht₀⟩ := id hTne
    refine mem_Box.mpr ⟨le_infPt hTne (fun t _ => (mem_Box.mp (B.u_mem t)).1), ?_⟩
    exact (infPt_le hTne B.u ht₀).trans (mem_Box.mp (B.u_mem t₀)).2
  rcases hcase with hdown | ⟨t, ht, hvop⟩
  · exact Or.inr (Or.inl ⟨infPt T B.u, hmem, hlevle, hdown⟩)
  · exact Or.inr (Or.inr ⟨infPt T B.u, B.u t, hmem, B.u_mem t, hvop⟩)

/-!
## What remains

With `exists_meet_progress` the `d = 3`-specific parts of HL's argument reduce to a
single one.  The loop of `Tfnp/Tarski/LevelsetLoop.lean` reaches its endgame in two
ways, and only one of them is still tied to three dimensions:

* *Some extent of the search space has diameter at most one, and every width is at
  least two.*  Then `sDiam_cases` — whose proof is dimension-uniform, the excluded
  case giving `Σ_{j≠i}(r_j − ℓ_j) ≥ 2(d−1)` — supplies `κ ≤ lev ℓ + 1` or
  `lev r ≤ κ + 1`, and `exists_meet_progress` (or its dual) finishes.  No
  three-dimensionality anywhere.

* *Some width is at most one* — a third configuration: an upward `x` and a downward
  `y` with `x_i ≤ y_i ≤ x_i + 1`.  Neither the meet nor the join is forced, and HL
  spend a further `O(log n)` queries binary-searching a *segment* of the levelset
  (`config3Alg`, HL Lemma 3.13).  At `d = 3` the segment is one-dimensional and four
  sign patterns suffice.  At `d ≥ 4` the search space of a third configuration is
  `(d−2)`-dimensional, and whether it can be resolved in `O_d(log n)` queries is
  open.  This is the single remaining obstruction to
  `Tarski(n,d) ∈ O_d(log² n)` by this route.

The other `d = 3` ingredient, the sign trichotomy `up_or_down_or_iUpDown`, is not
actually needed: a query whose strict-up set is `A` is weakly down off `A` and
weakly up off its strict-down set `B`, and since `A ∩ B = ∅` every coordinate is
covered by one of the two, so a deep query still shrinks every extent.  Only the
bookkeeping of `LevelsetLoop.lean`, which indexes bounding points by single
coordinates, assumes `|A| = 1`.
-/

end Tfnp.Tarski
