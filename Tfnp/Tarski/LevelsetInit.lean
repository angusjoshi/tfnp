/-
Copyright (c) 2026 Angus Joshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Angus Joshi
-/
import Tfnp.Tarski.LevelsetWitness

/-!
# HL Lemma 3.14: initialising the six bounding points

For each coordinate `i` we need an `i`-upward point at the *smallest* `i`-coordinate
the levelset attains, and an `i`-downward point at the *largest*.  The extremes
matter: they are what make `lev (lower corner) ≤ k ≤ lev (upper corner)`, which the
rest of HL §3 needs.

HL find the `i`-downward point by binary search along the *top* segment — coordinate
`i` frozen at its maximum `M = sHi lo hi k i`.  Every point `q` of that segment has
`F q i ≤ M` (`initKey`): either `M = hi i`, and `F q i ≤ hi i` because `F` cannot
leave the box; or `M < hi i`, which happens only when the *level* constraint binds,
and then the segment is the single point `(M, lo j, lo p)`, where `F` weakly
increases both free coordinates, so `q` is upward.

Given that, `q` falls into one of four patterns.  Two give progress, one *is* the
sought `i`-downward point, and the last is impossible.  The remaining two are the
search invariants, and adjacent endpoints of opposite type give a downward meet.

Since the ambient hypotheses are only `lo ∈ Up F` and `hi ∈ Down F` — not that `F`
maps the box into itself, which the outer recursion would not preserve — every
appeal to "F stays in the box" becomes a violation against an endpoint
(`vop_hi_isSol`, `vop_lo_isSol`).
-/

namespace Tfnp.Tarski

open QueryAlg (Bounded)

/-! ### Escaping the box is a violation -/

section Escape

variable {F : Pt 3 → Pt 3} {lo hi : Pt 3} {k : ℕ} {q : Pt 3}

/-- If `F q` exceeds `hi`, then `q` and `hi` violate order preservation. -/
theorem vop_hi_isSol (hhi : hi ∈ Down F) (hq : q ∈ Box lo hi) (hlohi : lo ≤ hi)
    (h : ¬ F q ≤ hi) : IsLevelsetSol F lo hi k (.vop q hi) := by
  obtain ⟨l, hl⟩ := exists_lt_of_not_le h
  refine ⟨hq, mem_Box_self_right hlohi, (mem_Box.mp hq).2, fun hle => ?_⟩
  have h1 := le_coord hhi l
  have h2 := le_coord hle l
  omega

/-- If `F q` falls below `lo`, then `lo` and `q` violate order preservation. -/
theorem vop_lo_isSol (hlo : lo ∈ Up F) (hq : q ∈ Box lo hi) (hlohi : lo ≤ hi)
    (h : ¬ lo ≤ F q) : IsLevelsetSol F lo hi k (.vop lo q) := by
  obtain ⟨l, hl⟩ := exists_lt_of_not_le h
  refine ⟨mem_Box_self_left hlohi, hq, (mem_Box.mp hq).1, fun hle => ?_⟩
  have h1 := le_coord hlo l
  have h2 := le_coord hle l
  omega

end Escape

/-! ### The top segment -/

/-- The lower end of the search range along the top segment. -/
def initT0 (lo hi : Pt 3) (k : ℕ) (i j p : Fin 3) : ℕ :=
  max (lo j) (k - sHi lo hi k i - hi p)

/-- The upper end of the search range along the top segment. -/
def initT1 (lo hi : Pt 3) (k : ℕ) (i j p : Fin 3) : ℕ :=
  min (hi j) (k - sHi lo hi k i - lo p)

section TopSeg

variable {lo hi : Pt 3} {k : ℕ} {i j p : Fin 3}

/-- All the arithmetic facts about the top segment, in one place. -/
structure TopFacts (lo hi : Pt 3) (k : ℕ) (i j p : Fin 3) : Prop where
  /-- `i ≠ j`. -/
  ij : i ≠ j
  /-- `i ≠ p`. -/
  ip : i ≠ p
  /-- `j ≠ p`. -/
  jp : j ≠ p
  /-- The box is non-empty. -/
  lohi : lo ≤ hi
  /-- The level is attainable from below. -/
  lk : lev lo ≤ k
  /-- The level is attainable from above. -/
  kr : k ≤ lev hi

namespace TopFacts

lemma L3 (h : TopFacts lo hi k i j p) : lev lo = lo i + lo j + lo p :=
  lev_three lo h.ij h.ip h.jp

lemma H3 (h : TopFacts lo hi k i j p) : lev hi = hi i + hi j + hi p :=
  lev_three hi h.ij h.ip h.jp

lemma coord_i (h : TopFacts lo hi k i j p) : lo i ≤ hi i := le_coord h.lohi i
lemma coord_j (h : TopFacts lo hi k i j p) : lo j ≤ hi j := le_coord h.lohi j
lemma coord_p (h : TopFacts lo hi k i j p) : lo p ≤ hi p := le_coord h.lohi p

lemma M_def (_h : TopFacts lo hi k i j p) :
    sHi lo hi k i = min (hi i) (k + lo i - lev lo) := rfl

lemma M_le (_h : TopFacts lo hi k i j p) : sHi lo hi k i ≤ hi i := min_le_left _ _

lemma le_M (h : TopFacts lo hi k i j p) : lo i ≤ sHi lo hi k i := by
  have := h.L3; have := h.lk; have := h.coord_i
  simp only [sHi]; omega

lemma M_add_lo (h : TopFacts lo hi k i j p) : sHi lo hi k i + lo j + lo p ≤ k := by
  have h1 := h.L3
  have h3 := h.lk
  have h10 : sHi lo hi k i = min (hi i) (k + lo i - lev lo) := rfl
  omega

lemma T0_le_T1 (h : TopFacts lo hi k i j p) :
    initT0 lo hi k i j p ≤ initT1 lo hi k i j p := by
  have h1 := h.L3
  have h2 := h.H3
  have h3 := h.lk
  have h4 := h.kr
  have h5 := h.coord_i
  have h6 := h.coord_j
  have h7 := h.coord_p
  have h8 := h.M_le
  have h9 := h.le_M
  have h10 : sHi lo hi k i = min (hi i) (k + lo i - lev lo) := rfl
  simp only [initT0, initT1, max_le_iff, le_min_iff]
  refine ⟨⟨h6, ?_⟩, ?_, ?_⟩ <;> omega

lemma M_add_le (h : TopFacts lo hi k i j p) {t : ℕ} (ht : t ≤ initT1 lo hi k i j p) :
    sHi lo hi k i + t ≤ k := by
  have hle : t ≤ k - sHi lo hi k i - lo p := le_trans ht (min_le_right _ _)
  have hml := h.M_add_lo
  omega

/-- Segment points lie in the box. -/
lemma seg_mem (h : TopFacts lo hi k i j p) {t : ℕ}
    (h1 : initT0 lo hi k i j p ≤ t) (h2 : t ≤ initT1 lo hi k i j p) :
    segPt i j (sHi lo hi k i) k t ∈ Box lo hi := by
  have hj1 : lo j ≤ t := le_trans (le_max_left _ _) h1
  have hj2 : t ≤ hi j := le_trans h2 (min_le_left _ _)
  have hp1 : k - sHi lo hi k i - hi p ≤ t := le_trans (le_max_right _ _) h1
  have hp2 : t ≤ k - sHi lo hi k i - lo p := le_trans h2 (min_le_right _ _)
  have hM := h.M_add_le h2
  have hml := h.M_add_lo
  exact segPt_mem_Box h.ij h.ip h.jp h.le_M h.M_le hj1 hj2 (by omega) (by omega)

lemma seg_i (_h : TopFacts lo hi k i j p) (t : ℕ) :
    segPt i j (sHi lo hi k i) k t i = sHi lo hi k i := segPt_i _ _ _ _ _

lemma seg_j (h : TopFacts lo hi k i j p) (t : ℕ) :
    segPt i j (sHi lo hi k i) k t j = t := segPt_j (Ne.symm h.ij) _ _ _

lemma seg_p (h : TopFacts lo hi k i j p) (t : ℕ) :
    segPt i j (sHi lo hi k i) k t p = k - sHi lo hi k i - t :=
  segPt_other (Ne.symm h.ip) (Ne.symm h.jp) _ _ _

/-- **The key fact.**  Along the top segment `F` cannot raise coordinate `i`, unless
it leaves the box (a violation) or the point is already upward. -/
lemma key (h : TopFacts lo hi k i j p) {F : Pt 3 → Pt 3} {t : ℕ}
    (h1 : initT0 lo hi k i j p ≤ t) (h2 : t ≤ initT1 lo hi k i j p)
    (hbox : F (segPt i j (sHi lo hi k i) k t) ≤ hi)
    (hbox' : lo ≤ F (segPt i j (sHi lo hi k i) k t)) :
    F (segPt i j (sHi lo hi k i) k t) i ≤ sHi lo hi k i
      ∨ segPt i j (sHi lo hi k i) k t ≤ F (segPt i j (sHi lo hi k i) k t) := by
  by_cases hM : sHi lo hi k i = hi i
  · left
    have h' := le_coord hbox i
    omega
  · -- the level constraint binds, so the segment is a single point at the corner
    have hml := h.M_add_lo
    have hL3 := h.L3
    have hlk := h.lk
    have hMle := h.M_le
    have hMdef : sHi lo hi k i = min (hi i) (k + lo i - lev lo) := rfl
    have hMval : sHi lo hi k i = k + lo i - lev lo := by omega
    have hp2 : t ≤ k - sHi lo hi k i - lo p := le_trans h2 (min_le_right _ _)
    have hj1 : lo j ≤ t := le_trans (le_max_left _ _) h1
    have htj : t = lo j := by omega
    have htp : k - sHi lo hi k i - t = lo p := by omega
    by_cases hi' : F (segPt i j (sHi lo hi k i) k t) i ≤ sHi lo hi k i
    · exact Or.inl hi'
    · refine Or.inr (coord_le fun l => ?_)
      rcases fin3_cover h.ij h.ip h.jp l with rfl | rfl | rfl
      · rw [h.seg_i t]; omega
      · rw [h.seg_j t]
        have h' := le_coord hbox' l
        omega
      · rw [h.seg_p t]
        have h' := le_coord hbox' l
        omega

end TopFacts

end TopSeg

/-! ### What the initialisation returns -/

/-- The result of the downward initialisation: either a solution of the levelset
problem, or an `i`-downward point at the largest attainable `i`-coordinate. -/
def IsInitDown (F : Pt 3 → Pt 3) (lo hi : Pt 3) (k : ℕ) (i : Fin 3) :
    InnerAnswer 3 ⊕ Pt 3 → Prop
  | .inl a => IsLevelsetSol F lo hi k a
  | .inr z => z ∈ Box lo hi ∧ lev z = k ∧ z i = sHi lo hi k i ∧ IDown F z i

/-- The result of the upward initialisation. -/
def IsInitUp (F : Pt 3 → Pt 3) (lo hi : Pt 3) (k : ℕ) (i : Fin 3) :
    InnerAnswer 3 ⊕ Pt 3 → Prop
  | .inl a => IsLevelsetSol F lo hi k a
  | .inr z => z ∈ Box lo hi ∧ lev z = k ∧ z i = sLo lo hi k i ∧ IUp F z i

/-! ### The downward initialisation -/

/-- One step of the top-segment search.  The first two tests catch `F` leaving the
box (a violation against an endpoint); then upward and downward are checked; then
the four sign patterns in the two free coordinates.  The last is impossible, so its
branch may return anything. -/
noncomputable def initDownStep (lo hi : Pt 3) (k : ℕ) (i j p : Fin 3) (t : ℕ) (v : Pt 3) :
    QueryAlg (Pt 3) (Pt 3) (InnerAnswer 3 ⊕ Pt 3) ⊕ Bool :=
  if ¬ v ≤ hi then .inl (QueryAlg.pure (.inl (.vop (segPt i j (sHi lo hi k i) k t) hi)))
  else if ¬ lo ≤ v then .inl (QueryAlg.pure (.inl (.vop lo (segPt i j (sHi lo hi k i) k t))))
  else if segPt i j (sHi lo hi k i) k t ≤ v then .inl (QueryAlg.pure (.inl (.up (segPt i j (sHi lo hi k i) k t))))
  else if v ≤ segPt i j (sHi lo hi k i) k t then .inl (QueryAlg.pure (.inl (.down (segPt i j (sHi lo hi k i) k t))))
  else if t ≤ v j then
    if k - sHi lo hi k i - t ≤ v p then .inl (QueryAlg.pure (.inr (segPt i j (sHi lo hi k i) k t)))
    else .inr true
  else
    if k - sHi lo hi k i - t ≤ v p then .inr false
    else .inl (QueryAlg.pure (.inl (.down (segPt i j (sHi lo hi k i) k t))))

/-- The endgame: adjacent endpoints of opposite type give a downward meet. -/
noncomputable def initDownFinal (lo hi : Pt 3) (k : ℕ) (i j p : Fin 3)
    (tlo thi : ℕ) (_v : Pt 3) : QueryAlg (Pt 3) (Pt 3) (InnerAnswer 3 ⊕ Pt 3) :=
  downOrVop (pick3 i j (segPt i j (sHi lo hi k i) k tlo) (segPt i j (sHi lo hi k i) k thi) (segPt i j (sHi lo hi k i) k tlo))
    (glb (segPt i j (sHi lo hi k i) k tlo) (segPt i j (sHi lo hi k i) k thi)) >>= fun a => QueryAlg.pure (.inl a)

/-- **HL Lemma 3.14**, downward half: classify both endpoints, then binary search. -/
noncomputable def initDownAlg (lo hi : Pt 3) (k : ℕ) (i j p : Fin 3) (b : ℕ) :
    QueryAlg (Pt 3) (Pt 3) (InnerAnswer 3 ⊕ Pt 3) :=
  QueryAlg.ask (segPt i j (sHi lo hi k i) k (initT0 lo hi k i j p)) >>= fun v0 =>
    match initDownStep lo hi k i j p (initT0 lo hi k i j p) v0 with
    | .inl alg => alg
    | .inr _ =>
      QueryAlg.ask (segPt i j (sHi lo hi k i) k (initT1 lo hi k i j p)) >>= fun v1 =>
        match initDownStep lo hi k i j p (initT1 lo hi k i j p) v1 with
        | .inl alg => alg
        | .inr _ =>
            segSearch (segPt i j (sHi lo hi k i) k) (initDownStep lo hi k i j p)
              (initDownFinal lo hi k i j p) b
              (initT0 lo hi k i j p) (initT1 lo hi k i j p)

lemma initDownStep_bounded (lo hi : Pt 3) (k : ℕ) (i j p : Fin 3) (t : ℕ) (v : Pt 3)
    {alg : QueryAlg (Pt 3) (Pt 3) (InnerAnswer 3 ⊕ Pt 3)}
    (h : initDownStep lo hi k i j p t v = .inl alg) : Bounded 1 alg := by
  unfold initDownStep at h
  repeat' split at h
  all_goals first
    | (rw [← Sum.inl.inj h]; exact Bounded.pure' _ _)
    | exact absurd h (by simp)

lemma initDownFinal_bounded (lo hi : Pt 3) (k : ℕ) (i j p : Fin 3) (tlo thi : ℕ) (v : Pt 3) :
    Bounded 1 (initDownFinal lo hi k i j p tlo thi v) := by
  unfold initDownFinal
  exact Bounded.mono (n := 1 + 0)
    ((downOrVop_bounded _ _).bind fun _ => Bounded.pure' _ _) (by omega)

theorem initDownAlg_bounded (lo hi : Pt 3) (k : ℕ) (i j p : Fin 3) (b : ℕ) :
    Bounded (b + 4) (initDownAlg lo hi k i j p b) := by
  unfold initDownAlg
  refine Bounded.mono (n := 1 + (b + 3)) ((Bounded.ask _).bind fun v0 => ?_) (by omega)
  rcases hs0 : initDownStep lo hi k i j p (initT0 lo hi k i j p) v0 with alg | d0
  · exact (initDownStep_bounded _ _ _ _ _ _ _ _ hs0).mono (by omega)
  · refine Bounded.mono (n := 1 + (b + 2)) ((Bounded.ask _).bind fun v1 => ?_) (by omega)
    rcases hs1 : initDownStep lo hi k i j p (initT1 lo hi k i j p) v1 with alg | d1
    · exact (initDownStep_bounded _ _ _ _ _ _ _ _ hs1).mono (by omega)
    · exact segSearch_bounded
        (fun t v alg hh => initDownStep_bounded lo hi k i j p t v hh)
        (fun tlo thi v => initDownFinal_bounded lo hi k i j p tlo thi v) b _ _

/-! ### Correctness of the downward initialisation -/

section DownCorrect

variable {F : Pt 3 → Pt 3} {lo hi : Pt 3} {k : ℕ} {i j p : Fin 3}

/-- The lower search invariant: `F` weakly increases the free coordinate `j` and
strictly decreases `p`. -/
def initPlo (F : Pt 3 → Pt 3) (lo hi : Pt 3) (k : ℕ) (i j p : Fin 3) (t : ℕ) : Prop :=
  lo ≤ F (segPt i j (sHi lo hi k i) k t) ∧ F (segPt i j (sHi lo hi k i) k t) ≤ hi ∧ ¬ F (segPt i j (sHi lo hi k i) k t) ≤ segPt i j (sHi lo hi k i) k t
    ∧ F (segPt i j (sHi lo hi k i) k t) i ≤ sHi lo hi k i ∧ t ≤ F (segPt i j (sHi lo hi k i) k t) j
    ∧ F (segPt i j (sHi lo hi k i) k t) p < k - sHi lo hi k i - t

/-- The upper search invariant. -/
def initPhi (F : Pt 3 → Pt 3) (lo hi : Pt 3) (k : ℕ) (i j p : Fin 3) (t : ℕ) : Prop :=
  lo ≤ F (segPt i j (sHi lo hi k i) k t) ∧ F (segPt i j (sHi lo hi k i) k t) ≤ hi ∧ ¬ F (segPt i j (sHi lo hi k i) k t) ≤ segPt i j (sHi lo hi k i) k t
    ∧ F (segPt i j (sHi lo hi k i) k t) i ≤ sHi lo hi k i ∧ F (segPt i j (sHi lo hi k i) k t) j < t
    ∧ k - sHi lo hi k i - t ≤ F (segPt i j (sHi lo hi k i) k t) p

lemma downward_of_three (h : TopFacts lo hi k i j p) {t : ℕ}
    (ci : F (segPt i j (sHi lo hi k i) k t) i ≤ sHi lo hi k i) (cj : F (segPt i j (sHi lo hi k i) k t) j ≤ t)
    (cp : F (segPt i j (sHi lo hi k i) k t) p ≤ k - sHi lo hi k i - t) : F (segPt i j (sHi lo hi k i) k t) ≤ segPt i j (sHi lo hi k i) k t := by
  refine coord_le fun l => ?_
  rcases fin3_cover h.ij h.ip h.jp l with rfl | rfl | rfl
  · rw [h.seg_i t]; exact ci
  · rw [h.seg_j t]; exact cj
  · rw [h.seg_p t]; exact cp

/-- Correctness of one step: every `.inl` branch returns a valid answer. -/
theorem initDownStep_isSol (h : TopFacts lo hi k i j p)
    (hlo : lo ∈ Up F) (hhi : hi ∈ Down F) {t : ℕ}
    (h1 : initT0 lo hi k i j p ≤ t) (h2 : t ≤ initT1 lo hi k i j p)
    {alg : QueryAlg (Pt 3) (Pt 3) (InnerAnswer 3 ⊕ Pt 3)}
    (hs : initDownStep lo hi k i j p t (F (segPt i j (sHi lo hi k i) k t)) = .inl alg) :
    IsInitDown F lo hi k i (alg.run F) := by
  have hq := h.seg_mem h1 h2
  have hqi := h.seg_i t
  have hqj := h.seg_j t
  have hqp := h.seg_p t
  have hMle := h.M_add_le h2
  have hlev : lev (segPt i j (sHi lo hi k i) k t) = k := lev_segPt h.ij h.ip h.jp hMle
  unfold initDownStep at hs
  by_cases c1 : ¬ F (segPt i j (sHi lo hi k i) k t) ≤ hi
  · rw [if_pos c1] at hs
    rw [← Sum.inl.inj hs]
    exact vop_hi_isSol (k := k) hhi hq h.lohi c1
  rw [if_neg c1] at hs
  push Not at c1
  by_cases c2 : ¬ lo ≤ F (segPt i j (sHi lo hi k i) k t)
  · rw [if_pos c2] at hs
    rw [← Sum.inl.inj hs]
    exact vop_lo_isSol (k := k) hlo hq h.lohi c2
  rw [if_neg c2] at hs
  push Not at c2
  by_cases c3 : segPt i j (sHi lo hi k i) k t ≤ F (segPt i j (sHi lo hi k i) k t)
  · rw [if_pos c3] at hs
    rw [← Sum.inl.inj hs]
    exact ⟨hq, by omega, mem_Up.mpr c3⟩
  rw [if_neg c3] at hs
  by_cases c4 : F (segPt i j (sHi lo hi k i) k t) ≤ segPt i j (sHi lo hi k i) k t
  · rw [if_pos c4] at hs
    rw [← Sum.inl.inj hs]
    exact ⟨hq, by omega, mem_Down.mpr c4⟩
  rw [if_neg c4] at hs
  have hkeyi : F (segPt i j (sHi lo hi k i) k t) i ≤ sHi lo hi k i := by
    rcases h.key h1 h2 c1 c2 with hk | hk
    · exact hk
    · exact absurd hk c3
  by_cases c5 : t ≤ F (segPt i j (sHi lo hi k i) k t) j
  · rw [if_pos c5] at hs
    by_cases c6 : k - sHi lo hi k i - t ≤ F (segPt i j (sHi lo hi k i) k t) p
    · rw [if_pos c6] at hs
      rw [← Sum.inl.inj hs]
      refine ⟨hq, hlev, hqi, ?_, fun l hl => ?_⟩
      · obtain ⟨l, hl⟩ := exists_lt_of_not_le c3
        rcases fin3_cover h.ij h.ip h.jp l with rfl | rfl | rfl
        · exact hl
        · omega
        · omega
      · rcases fin3_cover h.ij h.ip h.jp l with rfl | rfl | rfl
        · exact absurd rfl hl
        · rw [hqj]; exact c5
        · rw [hqp]; exact c6
    · rw [if_neg c6] at hs; exact absurd hs (by simp)
  · rw [if_neg c5] at hs
    by_cases c6 : k - sHi lo hi k i - t ≤ F (segPt i j (sHi lo hi k i) k t) p
    · rw [if_pos c6] at hs; exact absurd hs (by simp)
    · rw [if_neg c6] at hs
      exact absurd (downward_of_three h hkeyi (by omega) (by omega)) c4

/-- Correctness of the directions: they establish the two search invariants. -/
theorem initDownStep_dir (h : TopFacts lo hi k i j p)
    (hlo : lo ∈ Up F) (hhi : hi ∈ Down F) {t : ℕ}
    (h1 : initT0 lo hi k i j p ≤ t) (h2 : t ≤ initT1 lo hi k i j p) {d : Bool}
    (hs : initDownStep lo hi k i j p t (F (segPt i j (sHi lo hi k i) k t)) = .inr d) :
    (d = true → initPlo F lo hi k i j p t) ∧ (d = false → initPhi F lo hi k i j p t) := by
  unfold initDownStep at hs
  by_cases c1 : ¬ F (segPt i j (sHi lo hi k i) k t) ≤ hi
  · rw [if_pos c1] at hs; exact absurd hs (by simp)
  rw [if_neg c1] at hs
  push Not at c1
  by_cases c2 : ¬ lo ≤ F (segPt i j (sHi lo hi k i) k t)
  · rw [if_pos c2] at hs; exact absurd hs (by simp)
  rw [if_neg c2] at hs
  push Not at c2
  by_cases c3 : segPt i j (sHi lo hi k i) k t ≤ F (segPt i j (sHi lo hi k i) k t)
  · rw [if_pos c3] at hs; exact absurd hs (by simp)
  rw [if_neg c3] at hs
  by_cases c4 : F (segPt i j (sHi lo hi k i) k t) ≤ segPt i j (sHi lo hi k i) k t
  · rw [if_pos c4] at hs; exact absurd hs (by simp)
  rw [if_neg c4] at hs
  have hkeyi : F (segPt i j (sHi lo hi k i) k t) i ≤ sHi lo hi k i := by
    rcases h.key h1 h2 c1 c2 with hk | hk
    · exact hk
    · exact absurd hk c3
  by_cases c5 : t ≤ F (segPt i j (sHi lo hi k i) k t) j
  · rw [if_pos c5] at hs
    by_cases c6 : k - sHi lo hi k i - t ≤ F (segPt i j (sHi lo hi k i) k t) p
    · rw [if_pos c6] at hs; exact absurd hs (by simp)
    · rw [if_neg c6] at hs
      have hd : d = true := (Sum.inr.inj hs).symm
      subst hd
      exact ⟨fun _ => ⟨c2, c1, c4, hkeyi, c5, by omega⟩, by simp⟩
  · rw [if_neg c5] at hs
    by_cases c6 : k - sHi lo hi k i - t ≤ F (segPt i j (sHi lo hi k i) k t) p
    · rw [if_pos c6] at hs
      have hd : d = false := (Sum.inr.inj hs).symm
      subst hd
      exact ⟨by simp, fun _ => ⟨c2, c1, c4, hkeyi, by omega, c6⟩⟩
    · rw [if_neg c6] at hs; exact absurd hs (by simp)

end DownCorrect

/-! ### The endpoints are forced

At the bottom of the segment the classification cannot come out "type r", and at the
top it cannot come out "type ℓ" — otherwise the point would be downward, which the
classification has already ruled out. -/

section Endpoints

variable {F : Pt 3 → Pt 3} {lo hi : Pt 3} {k : ℕ} {i j p : Fin 3}

theorem initPhi_T0_false (h : TopFacts lo hi k i j p)
    (hphi : initPhi F lo hi k i j p (initT0 lo hi k i j p)) : False := by
  obtain ⟨hb1, hb2, hnd, hki, hj, hp⟩ := hphi
  have hqj := h.seg_j (initT0 lo hi k i j p)
  have hqp := h.seg_p (initT0 lo hi k i j p)
  have hlj := le_coord hb1 j
  have hphi' := le_coord hb2 p
  have hMle := h.M_add_le h.T0_le_T1
  have hT0 : initT0 lo hi k i j p = max (lo j) (k - sHi lo hi k i - hi p) := rfl
  exact hnd (downward_of_three h hki (by omega) (by omega))

theorem initPlo_T1_false (h : TopFacts lo hi k i j p)
    (hplo : initPlo F lo hi k i j p (initT1 lo hi k i j p)) : False := by
  obtain ⟨hb1, hb2, hnd, hki, hj, hp⟩ := hplo
  have hqj := h.seg_j (initT1 lo hi k i j p)
  have hqp := h.seg_p (initT1 lo hi k i j p)
  have hpp := le_coord hb1 p
  have hjj := le_coord hb2 j
  have hMle := h.M_add_le (le_refl _)
  have hT1 : initT1 lo hi k i j p = min (hi j) (k - sHi lo hi k i - lo p) := rfl
  exact hnd (downward_of_three h hki (by omega) (by omega))

/-- The two invariants are incompatible at the same index. -/
theorem initPlo_initPhi_ne (h : TopFacts lo hi k i j p) {t : ℕ}
    (hplo : initPlo F lo hi k i j p t) (hphi : initPhi F lo hi k i j p t) : False := by
  obtain ⟨-, -, -, -, -, hp1⟩ := hplo
  obtain ⟨-, -, -, -, -, hp2⟩ := hphi
  omega

end Endpoints

/-! ### The endgame -/

section Endgame

variable {F : Pt 3 → Pt 3} {lo hi : Pt 3} {k : ℕ} {i j p : Fin 3}

theorem initDownFinal_isSol (h : TopFacts lo hi k i j p)
    (hlo : lo ∈ Up F) (hhi : hi ∈ Down F) {tlo thi : ℕ}
    (g1 : initT0 lo hi k i j p ≤ tlo) (g2 : thi ≤ initT1 lo hi k i j p)
    (glt : tlo < thi) (gadj : thi ≤ tlo + 1)
    (hplo : initPlo F lo hi k i j p tlo) (hphi : initPhi F lo hi k i j p thi) :
    IsInitDown F lo hi k i
      ((initDownFinal lo hi k i j p tlo thi (F (segPt i j (sHi lo hi k i) k thi))).run F) := by
  obtain ⟨-, -, -, hki_lo, hj_lo, hp_lo⟩ := hplo
  obtain ⟨-, -, -, hki_hi, hj_hi, hp_hi⟩ := hphi
  have hL := h.seg_mem g1 (le_trans (by omega) g2)
  have hR := h.seg_mem (le_trans g1 (by omega)) g2
  have hLi := h.seg_i tlo
  have hLj := h.seg_j tlo
  have hLp := h.seg_p tlo
  have hRi := h.seg_i thi
  have hRj := h.seg_j thi
  have hRp := h.seg_p thi
  have hMle := h.M_add_le g2
  have hGi : glb (segPt i j (sHi lo hi k i) k tlo) (segPt i j (sHi lo hi k i) k thi) i = sHi lo hi k i := by
    rw [glb_apply, hLi, hRi]; omega
  have hGj : glb (segPt i j (sHi lo hi k i) k tlo) (segPt i j (sHi lo hi k i) k thi) j = tlo := by rw [glb_apply, hLj, hRj]; omega
  have hGp : glb (segPt i j (sHi lo hi k i) k tlo) (segPt i j (sHi lo hi k i) k thi) p = k - sHi lo hi k i - thi := by
    rw [glb_apply, hLp, hRp]; omega
  unfold initDownFinal
  rw [QueryAlg.run_bind, QueryAlg.run_pure]
  show IsLevelsetSol F lo hi k ((downOrVop (pick3 i j (segPt i j (sHi lo hi k i) k tlo) (segPt i j (sHi lo hi k i) k thi) (segPt i j (sHi lo hi k i) k tlo))
      (glb (segPt i j (sHi lo hi k i) k tlo) (segPt i j (sHi lo hi k i) k thi))).run F)
  refine downOrVop_isSol (fun l => ?_) (fun l => ?_) (glb_mem_Box hL hR) (fun l => ?_) ?_
  · rcases fin3_cover h.ij h.ip h.jp l with rfl | rfl | rfl
    · rw [pick3_i]; exact glb_le_left _ _
    · rw [pick3_j (Ne.symm h.ij)]; exact glb_le_right _ _
    · rw [pick3_other (Ne.symm h.ip) (Ne.symm h.jp)]; exact glb_le_left _ _
  · rcases fin3_cover h.ij h.ip h.jp l with rfl | rfl | rfl
    · rw [pick3_i, hGi]; exact hki_lo
    · rw [pick3_j (Ne.symm h.ij), hGj]; omega
    · rw [pick3_other (Ne.symm h.ip) (Ne.symm h.jp), hGp]; omega
  · rcases fin3_cover h.ij h.ip h.jp l with rfl | rfl | rfl
    · rw [pick3_i]; exact hL
    · rw [pick3_j (Ne.symm h.ij)]; exact hR
    · rw [pick3_other (Ne.symm h.ip) (Ne.symm h.jp)]; exact hL
  · have : lev (glb (segPt i j (sHi lo hi k i) k tlo) (segPt i j (sHi lo hi k i) k thi))
        = sHi lo hi k i + tlo + (k - sHi lo hi k i - thi) := by
      rw [lev_three _ h.ij h.ip h.jp, hGi, hGj, hGp]
    omega

end Endgame

/-! ### HL Lemma 3.14, downward half -/

section DownAlg

variable {F : Pt 3 → Pt 3} {lo hi : Pt 3} {k : ℕ} {i j p : Fin 3}

/-- **HL Lemma 3.14**, downward half.  Either a solution of the levelset problem, or
an `i`-downward point at the largest attainable `i`-coordinate. -/
theorem initDownAlg_isSol (h : TopFacts lo hi k i j p)
    (hlo : lo ∈ Up F) (hhi : hi ∈ Down F) {b : ℕ}
    (hb : initT1 lo hi k i j p - initT0 lo hi k i j p ≤ 2 ^ b) :
    IsInitDown F lo hi k i ((initDownAlg lo hi k i j p b).run F) := by
  have hT := h.T0_le_T1
  unfold initDownAlg
  rw [QueryAlg.run_bind, QueryAlg.run_ask]
  rcases hs0 : initDownStep lo hi k i j p (initT0 lo hi k i j p)
      (F (segPt i j (sHi lo hi k i) k (initT0 lo hi k i j p))) with alg | d0
  · exact initDownStep_isSol h hlo hhi le_rfl hT hs0
  · have hd0 := initDownStep_dir h hlo hhi le_rfl hT hs0
    have hplo : initPlo F lo hi k i j p (initT0 lo hi k i j p) := by
      cases d0
      · exact absurd (hd0.2 rfl) (fun hx => initPhi_T0_false h hx)
      · exact hd0.1 rfl
    rw [QueryAlg.run_bind, QueryAlg.run_ask]
    rcases hs1 : initDownStep lo hi k i j p (initT1 lo hi k i j p)
        (F (segPt i j (sHi lo hi k i) k (initT1 lo hi k i j p))) with alg | d1
    · exact initDownStep_isSol h hlo hhi hT le_rfl hs1
    · have hd1 := initDownStep_dir h hlo hhi hT le_rfl hs1
      have hphi : initPhi F lo hi k i j p (initT1 lo hi k i j p) := by
        cases d1
        · exact hd1.2 rfl
        · exact absurd (hd1.1 rfl) (fun hx => initPlo_T1_false h hx)
      have hlt : initT0 lo hi k i j p < initT1 lo hi k i j p := by
        rcases Nat.lt_or_ge (initT0 lo hi k i j p) (initT1 lo hi k i j p) with hh | hh
        · exact hh
        · exact absurd (initPlo_initPhi_ne h hplo (by
            have : initT1 lo hi k i j p = initT0 lo hi k i j p := by omega
            rw [← this]; exact hphi)) (by simp)
      exact segSearch_spec F (IsInitDown F lo hi k i)
        (initPlo F lo hi k i j p) (initPhi F lo hi k i j p)
        (initT0 lo hi k i j p) (initT1 lo hi k i j p)
        (fun t alg ha hb' hss => initDownStep_isSol h hlo hhi ha hb' hss)
        (fun t d ha hb' hss => initDownStep_dir h hlo hhi ha hb' hss)
        (fun tl th ha hb' hlt' hadj hpl hph =>
          initDownFinal_isSol h hlo hhi ha hb' hlt' hadj hpl hph)
        b _ _ hb le_rfl le_rfl hlt hplo hphi

end DownAlg

/-! ### The bottom segment, and the upward half

The mirror image: coordinate `i` is frozen at its *minimum* `m = sLo lo hi k i`, and
`F` cannot lower it below `m` unless the point is already downward.  Types A and B
swap roles: the *lower* end of the range carries "`F` raises `j`, weakly lowers `p`"
and the upper end the reverse. -/

/-- The lower end of the search range along the bottom segment. -/
def initU0 (lo hi : Pt 3) (k : ℕ) (i j p : Fin 3) : ℕ :=
  max (lo j) (k - sLo lo hi k i - hi p)

/-- The upper end of the search range along the bottom segment. -/
def initU1 (lo hi : Pt 3) (k : ℕ) (i j p : Fin 3) : ℕ :=
  min (hi j) (k - sLo lo hi k i - lo p)

namespace TopFacts

variable {lo hi : Pt 3} {k : ℕ} {i j p : Fin 3}

lemma le_m (h : TopFacts lo hi k i j p) : lo i ≤ sLo lo hi k i := le_max_left _ _

lemma m_le (h : TopFacts lo hi k i j p) : sLo lo hi k i ≤ hi i := by
  have := h.H3; have := h.kr; have := h.coord_i
  simp only [sLo]; omega

lemma m_add_lo (h : TopFacts lo hi k i j p) : sLo lo hi k i + lo j + lo p ≤ k := by
  have h1 := h.L3
  have h2 := h.H3
  have h3 := h.lk
  have h4 := h.kr
  have h6 := h.coord_j
  have h7 := h.coord_p
  have h10 : sLo lo hi k i = max (lo i) (k + hi i - lev hi) := rfl
  omega

lemma m_add_hi (h : TopFacts lo hi k i j p) : k ≤ sLo lo hi k i + hi j + hi p := by
  have h2 := h.H3
  have h4 := h.kr
  have h10 : sLo lo hi k i = max (lo i) (k + hi i - lev hi) := rfl
  omega

lemma m_add_le (h : TopFacts lo hi k i j p) {t : ℕ} (ht : t ≤ initU1 lo hi k i j p) :
    sLo lo hi k i + t ≤ k := by
  have hle : t ≤ k - sLo lo hi k i - lo p := le_trans ht (min_le_right _ _)
  have hml := h.m_add_lo
  omega

lemma U0_le_U1 (h : TopFacts lo hi k i j p) :
    initU0 lo hi k i j p ≤ initU1 lo hi k i j p := by
  have h6 := h.coord_j
  have h7 := h.coord_p
  have hml := h.m_add_lo
  have hmh := h.m_add_hi
  simp only [initU0, initU1, max_le_iff, le_min_iff]
  refine ⟨⟨h6, ?_⟩, ?_, ?_⟩ <;> omega

lemma segU_mem (h : TopFacts lo hi k i j p) {t : ℕ}
    (h1 : initU0 lo hi k i j p ≤ t) (h2 : t ≤ initU1 lo hi k i j p) :
    segPt i j (sLo lo hi k i) k t ∈ Box lo hi := by
  have hj1 : lo j ≤ t := le_trans (le_max_left _ _) h1
  have hj2 : t ≤ hi j := le_trans h2 (min_le_left _ _)
  have hp1 : k - sLo lo hi k i - hi p ≤ t := le_trans (le_max_right _ _) h1
  have hp2 : t ≤ k - sLo lo hi k i - lo p := le_trans h2 (min_le_right _ _)
  have hM := h.m_add_le h2
  have hml := h.m_add_lo
  exact segPt_mem_Box h.ij h.ip h.jp h.le_m h.m_le hj1 hj2 (by omega) (by omega)

lemma segU_i (_h : TopFacts lo hi k i j p) (t : ℕ) :
    segPt i j (sLo lo hi k i) k t i = sLo lo hi k i := segPt_i _ _ _ _ _

lemma segU_j (h : TopFacts lo hi k i j p) (t : ℕ) :
    segPt i j (sLo lo hi k i) k t j = t := segPt_j (Ne.symm h.ij) _ _ _

lemma segU_p (h : TopFacts lo hi k i j p) (t : ℕ) :
    segPt i j (sLo lo hi k i) k t p = k - sLo lo hi k i - t :=
  segPt_other (Ne.symm h.ip) (Ne.symm h.jp) _ _ _

/-- **The key fact**, mirrored: along the bottom segment `F` cannot lower coordinate
`i`, unless it leaves the box or the point is already downward. -/
lemma keyU (h : TopFacts lo hi k i j p) {F : Pt 3 → Pt 3} {t : ℕ}
    (h1 : initU0 lo hi k i j p ≤ t) (h2 : t ≤ initU1 lo hi k i j p)
    (hbox : F (segPt i j (sLo lo hi k i) k t) ≤ hi) (hbox' : lo ≤ F (segPt i j (sLo lo hi k i) k t)) :
    sLo lo hi k i ≤ F (segPt i j (sLo lo hi k i) k t) i ∨ F (segPt i j (sLo lo hi k i) k t) ≤ segPt i j (sLo lo hi k i) k t := by
  by_cases hm : sLo lo hi k i = lo i
  · left
    have h' := le_coord hbox' i
    omega
  · have hmh := h.m_add_hi
    have h2' := h.H3
    have h4 := h.kr
    have hmle := h.le_m
    have hmdef : sLo lo hi k i = max (lo i) (k + hi i - lev hi) := rfl
    have hmval : sLo lo hi k i = k + hi i - lev hi := by omega
    have hp1 : k - sLo lo hi k i - hi p ≤ t := le_trans (le_max_right _ _) h1
    have hj2 : t ≤ hi j := le_trans h2 (min_le_left _ _)
    have htj : t = hi j := by omega
    have htp : k - sLo lo hi k i - t = hi p := by omega
    by_cases hi' : sLo lo hi k i ≤ F (segPt i j (sLo lo hi k i) k t) i
    · exact Or.inl hi'
    · refine Or.inr (coord_le fun l => ?_)
      rcases fin3_cover h.ij h.ip h.jp l with rfl | rfl | rfl
      · rw [h.segU_i t]; omega
      · rw [h.segU_j t]
        have h' := le_coord hbox l
        omega
      · rw [h.segU_p t]
        have h' := le_coord hbox l
        omega

end TopFacts

/-! ### The upward algorithm -/

/-- One step of the bottom-segment search. -/
noncomputable def initUpStep (lo hi : Pt 3) (k : ℕ) (i j p : Fin 3) (t : ℕ) (v : Pt 3) :
    QueryAlg (Pt 3) (Pt 3) (InnerAnswer 3 ⊕ Pt 3) ⊕ Bool :=
  if ¬ v ≤ hi then .inl (QueryAlg.pure (.inl (.vop (segPt i j (sLo lo hi k i) k t) hi)))
  else if ¬ lo ≤ v then .inl (QueryAlg.pure (.inl (.vop lo (segPt i j (sLo lo hi k i) k t))))
  else if segPt i j (sLo lo hi k i) k t ≤ v then .inl (QueryAlg.pure (.inl (.up (segPt i j (sLo lo hi k i) k t))))
  else if v ≤ segPt i j (sLo lo hi k i) k t then .inl (QueryAlg.pure (.inl (.down (segPt i j (sLo lo hi k i) k t))))
  else if v j ≤ t then
    if v p ≤ k - sLo lo hi k i - t then .inl (QueryAlg.pure (.inr (segPt i j (sLo lo hi k i) k t)))
    else .inr false
  else
    if v p ≤ k - sLo lo hi k i - t then .inr true
    else .inl (QueryAlg.pure (.inl (.up (segPt i j (sLo lo hi k i) k t))))

/-- The endgame: adjacent endpoints of opposite type give an upward join. -/
noncomputable def initUpFinal (lo hi : Pt 3) (k : ℕ) (i j p : Fin 3)
    (tlo thi : ℕ) (_v : Pt 3) : QueryAlg (Pt 3) (Pt 3) (InnerAnswer 3 ⊕ Pt 3) :=
  upOrVop (pick3 i j (segPt i j (sLo lo hi k i) k tlo) (segPt i j (sLo lo hi k i) k tlo) (segPt i j (sLo lo hi k i) k thi))
    (lub (segPt i j (sLo lo hi k i) k tlo) (segPt i j (sLo lo hi k i) k thi)) >>= fun a => QueryAlg.pure (.inl a)

/-- **HL Lemma 3.14**, upward half. -/
noncomputable def initUpAlg (lo hi : Pt 3) (k : ℕ) (i j p : Fin 3) (b : ℕ) :
    QueryAlg (Pt 3) (Pt 3) (InnerAnswer 3 ⊕ Pt 3) :=
  QueryAlg.ask (segPt i j (sLo lo hi k i) k (initU0 lo hi k i j p)) >>= fun v0 =>
    match initUpStep lo hi k i j p (initU0 lo hi k i j p) v0 with
    | .inl alg => alg
    | .inr _ =>
      QueryAlg.ask (segPt i j (sLo lo hi k i) k (initU1 lo hi k i j p)) >>= fun v1 =>
        match initUpStep lo hi k i j p (initU1 lo hi k i j p) v1 with
        | .inl alg => alg
        | .inr _ =>
            segSearch (segPt i j (sLo lo hi k i) k) (initUpStep lo hi k i j p)
              (initUpFinal lo hi k i j p) b
              (initU0 lo hi k i j p) (initU1 lo hi k i j p)

lemma initUpStep_bounded (lo hi : Pt 3) (k : ℕ) (i j p : Fin 3) (t : ℕ) (v : Pt 3)
    {alg : QueryAlg (Pt 3) (Pt 3) (InnerAnswer 3 ⊕ Pt 3)}
    (h : initUpStep lo hi k i j p t v = .inl alg) : Bounded 1 alg := by
  unfold initUpStep at h
  repeat' split at h
  all_goals first
    | (rw [← Sum.inl.inj h]; exact Bounded.pure' _ _)
    | exact absurd h (by simp)

lemma initUpFinal_bounded (lo hi : Pt 3) (k : ℕ) (i j p : Fin 3) (tlo thi : ℕ) (v : Pt 3) :
    Bounded 1 (initUpFinal lo hi k i j p tlo thi v) := by
  unfold initUpFinal
  exact Bounded.mono (n := 1 + 0)
    ((upOrVop_bounded _ _).bind fun _ => Bounded.pure' _ _) (by omega)

theorem initUpAlg_bounded (lo hi : Pt 3) (k : ℕ) (i j p : Fin 3) (b : ℕ) :
    Bounded (b + 4) (initUpAlg lo hi k i j p b) := by
  unfold initUpAlg
  refine Bounded.mono (n := 1 + (b + 3)) ((Bounded.ask _).bind fun v0 => ?_) (by omega)
  rcases hs0 : initUpStep lo hi k i j p (initU0 lo hi k i j p) v0 with alg | d0
  · exact (initUpStep_bounded _ _ _ _ _ _ _ _ hs0).mono (by omega)
  · refine Bounded.mono (n := 1 + (b + 2)) ((Bounded.ask _).bind fun v1 => ?_) (by omega)
    rcases hs1 : initUpStep lo hi k i j p (initU1 lo hi k i j p) v1 with alg | d1
    · exact (initUpStep_bounded _ _ _ _ _ _ _ _ hs1).mono (by omega)
    · exact segSearch_bounded
        (fun t v alg hh => initUpStep_bounded lo hi k i j p t v hh)
        (fun tlo thi v => initUpFinal_bounded lo hi k i j p tlo thi v) b _ _

/-! ### Correctness of the upward initialisation -/

section UpCorrect

variable {F : Pt 3 → Pt 3} {lo hi : Pt 3} {k : ℕ} {i j p : Fin 3}

/-- The lower search invariant of the bottom segment (HL's type B). -/
def initUPlo (F : Pt 3 → Pt 3) (lo hi : Pt 3) (k : ℕ) (i j p : Fin 3) (t : ℕ) : Prop :=
  lo ≤ F (segPt i j (sLo lo hi k i) k t) ∧ F (segPt i j (sLo lo hi k i) k t) ≤ hi ∧ ¬ segPt i j (sLo lo hi k i) k t ≤ F (segPt i j (sLo lo hi k i) k t)
    ∧ sLo lo hi k i ≤ F (segPt i j (sLo lo hi k i) k t) i ∧ t < F (segPt i j (sLo lo hi k i) k t) j
    ∧ F (segPt i j (sLo lo hi k i) k t) p ≤ k - sLo lo hi k i - t

/-- The upper search invariant of the bottom segment (HL's type A). -/
def initUPhi (F : Pt 3 → Pt 3) (lo hi : Pt 3) (k : ℕ) (i j p : Fin 3) (t : ℕ) : Prop :=
  lo ≤ F (segPt i j (sLo lo hi k i) k t) ∧ F (segPt i j (sLo lo hi k i) k t) ≤ hi ∧ ¬ segPt i j (sLo lo hi k i) k t ≤ F (segPt i j (sLo lo hi k i) k t)
    ∧ sLo lo hi k i ≤ F (segPt i j (sLo lo hi k i) k t) i ∧ F (segPt i j (sLo lo hi k i) k t) j ≤ t
    ∧ k - sLo lo hi k i - t < F (segPt i j (sLo lo hi k i) k t) p

lemma upward_of_three (h : TopFacts lo hi k i j p) {t : ℕ}
    (ci : sLo lo hi k i ≤ F (segPt i j (sLo lo hi k i) k t) i) (cj : t ≤ F (segPt i j (sLo lo hi k i) k t) j)
    (cp : k - sLo lo hi k i - t ≤ F (segPt i j (sLo lo hi k i) k t) p) : segPt i j (sLo lo hi k i) k t ≤ F (segPt i j (sLo lo hi k i) k t) := by
  refine coord_le fun l => ?_
  rcases fin3_cover h.ij h.ip h.jp l with rfl | rfl | rfl
  · rw [h.segU_i t]; exact ci
  · rw [h.segU_j t]; exact cj
  · rw [h.segU_p t]; exact cp

theorem initUpStep_isSol (h : TopFacts lo hi k i j p)
    (hlo : lo ∈ Up F) (hhi : hi ∈ Down F) {t : ℕ}
    (h1 : initU0 lo hi k i j p ≤ t) (h2 : t ≤ initU1 lo hi k i j p)
    {alg : QueryAlg (Pt 3) (Pt 3) (InnerAnswer 3 ⊕ Pt 3)}
    (hs : initUpStep lo hi k i j p t (F (segPt i j (sLo lo hi k i) k t)) = .inl alg) :
    IsInitUp F lo hi k i (alg.run F) := by
  have hq := h.segU_mem h1 h2
  have hqi := h.segU_i t
  have hqj := h.segU_j t
  have hqp := h.segU_p t
  have hMle := h.m_add_le h2
  have hlev : lev (segPt i j (sLo lo hi k i) k t) = k := lev_segPt h.ij h.ip h.jp hMle
  unfold initUpStep at hs
  by_cases c1 : ¬ F (segPt i j (sLo lo hi k i) k t) ≤ hi
  · rw [if_pos c1] at hs
    rw [← Sum.inl.inj hs]
    exact vop_hi_isSol (k := k) hhi hq h.lohi c1
  rw [if_neg c1] at hs
  push Not at c1
  by_cases c2 : ¬ lo ≤ F (segPt i j (sLo lo hi k i) k t)
  · rw [if_pos c2] at hs
    rw [← Sum.inl.inj hs]
    exact vop_lo_isSol (k := k) hlo hq h.lohi c2
  rw [if_neg c2] at hs
  push Not at c2
  by_cases c3 : segPt i j (sLo lo hi k i) k t ≤ F (segPt i j (sLo lo hi k i) k t)
  · rw [if_pos c3] at hs
    rw [← Sum.inl.inj hs]
    exact ⟨hq, by omega, mem_Up.mpr c3⟩
  rw [if_neg c3] at hs
  by_cases c4 : F (segPt i j (sLo lo hi k i) k t) ≤ segPt i j (sLo lo hi k i) k t
  · rw [if_pos c4] at hs
    rw [← Sum.inl.inj hs]
    exact ⟨hq, by omega, mem_Down.mpr c4⟩
  rw [if_neg c4] at hs
  have hkeyi : sLo lo hi k i ≤ F (segPt i j (sLo lo hi k i) k t) i := by
    rcases h.keyU h1 h2 c1 c2 with hk | hk
    · exact hk
    · exact absurd hk c4
  by_cases c5 : F (segPt i j (sLo lo hi k i) k t) j ≤ t
  · rw [if_pos c5] at hs
    by_cases c6 : F (segPt i j (sLo lo hi k i) k t) p ≤ k - sLo lo hi k i - t
    · rw [if_pos c6] at hs
      rw [← Sum.inl.inj hs]
      refine ⟨hq, hlev, hqi, ?_, fun l hl => ?_⟩
      · obtain ⟨l, hl⟩ := exists_lt_of_not_le c4
        rcases fin3_cover h.ij h.ip h.jp l with rfl | rfl | rfl
        · exact hl
        · omega
        · omega
      · rcases fin3_cover h.ij h.ip h.jp l with rfl | rfl | rfl
        · exact absurd rfl hl
        · rw [hqj]; exact c5
        · rw [hqp]; exact c6
    · rw [if_neg c6] at hs; exact absurd hs (by simp)
  · rw [if_neg c5] at hs
    by_cases c6 : F (segPt i j (sLo lo hi k i) k t) p ≤ k - sLo lo hi k i - t
    · rw [if_pos c6] at hs; exact absurd hs (by simp)
    · rw [if_neg c6] at hs
      exact absurd (upward_of_three h hkeyi (by omega) (by omega)) c3

theorem initUpStep_dir (h : TopFacts lo hi k i j p)
    (hlo : lo ∈ Up F) (hhi : hi ∈ Down F) {t : ℕ}
    (h1 : initU0 lo hi k i j p ≤ t) (h2 : t ≤ initU1 lo hi k i j p) {d : Bool}
    (hs : initUpStep lo hi k i j p t (F (segPt i j (sLo lo hi k i) k t)) = .inr d) :
    (d = true → initUPlo F lo hi k i j p t) ∧ (d = false → initUPhi F lo hi k i j p t) := by
  unfold initUpStep at hs
  by_cases c1 : ¬ F (segPt i j (sLo lo hi k i) k t) ≤ hi
  · rw [if_pos c1] at hs; exact absurd hs (by simp)
  rw [if_neg c1] at hs
  push Not at c1
  by_cases c2 : ¬ lo ≤ F (segPt i j (sLo lo hi k i) k t)
  · rw [if_pos c2] at hs; exact absurd hs (by simp)
  rw [if_neg c2] at hs
  push Not at c2
  by_cases c3 : segPt i j (sLo lo hi k i) k t ≤ F (segPt i j (sLo lo hi k i) k t)
  · rw [if_pos c3] at hs; exact absurd hs (by simp)
  rw [if_neg c3] at hs
  by_cases c4 : F (segPt i j (sLo lo hi k i) k t) ≤ segPt i j (sLo lo hi k i) k t
  · rw [if_pos c4] at hs; exact absurd hs (by simp)
  rw [if_neg c4] at hs
  have hkeyi : sLo lo hi k i ≤ F (segPt i j (sLo lo hi k i) k t) i := by
    rcases h.keyU h1 h2 c1 c2 with hk | hk
    · exact hk
    · exact absurd hk c4
  by_cases c5 : F (segPt i j (sLo lo hi k i) k t) j ≤ t
  · rw [if_pos c5] at hs
    by_cases c6 : F (segPt i j (sLo lo hi k i) k t) p ≤ k - sLo lo hi k i - t
    · rw [if_pos c6] at hs; exact absurd hs (by simp)
    · rw [if_neg c6] at hs
      have hd : d = false := (Sum.inr.inj hs).symm
      subst hd
      exact ⟨by simp, fun _ => ⟨c2, c1, c3, hkeyi, c5, by omega⟩⟩
  · rw [if_neg c5] at hs
    by_cases c6 : F (segPt i j (sLo lo hi k i) k t) p ≤ k - sLo lo hi k i - t
    · rw [if_pos c6] at hs
      have hd : d = true := (Sum.inr.inj hs).symm
      subst hd
      exact ⟨fun _ => ⟨c2, c1, c3, hkeyi, by omega, c6⟩, by simp⟩
    · rw [if_neg c6] at hs; exact absurd hs (by simp)

theorem initUPhi_U0_false (h : TopFacts lo hi k i j p)
    (hphi : initUPhi F lo hi k i j p (initU0 lo hi k i j p)) : False := by
  obtain ⟨hb1, hb2, hnu, hki, hj, hp⟩ := hphi
  have hqj := h.segU_j (initU0 lo hi k i j p)
  have hqp := h.segU_p (initU0 lo hi k i j p)
  have hlj := le_coord hb1 j
  have hphi' := le_coord hb2 p
  have hMle := h.m_add_le h.U0_le_U1
  have hU0 : initU0 lo hi k i j p = max (lo j) (k - sLo lo hi k i - hi p) := rfl
  exact hnu (upward_of_three h hki (by omega) (by omega))

theorem initUPlo_U1_false (h : TopFacts lo hi k i j p)
    (hplo : initUPlo F lo hi k i j p (initU1 lo hi k i j p)) : False := by
  obtain ⟨hb1, hb2, hnu, hki, hj, hp⟩ := hplo
  have hqj := h.segU_j (initU1 lo hi k i j p)
  have hqp := h.segU_p (initU1 lo hi k i j p)
  have hpp := le_coord hb1 p
  have hjj := le_coord hb2 j
  have hMle := h.m_add_le (le_refl _)
  have hU1 : initU1 lo hi k i j p = min (hi j) (k - sLo lo hi k i - lo p) := rfl
  exact hnu (upward_of_three h hki (by omega) (by omega))

theorem initUPlo_initUPhi_ne (h : TopFacts lo hi k i j p) {t : ℕ}
    (hplo : initUPlo F lo hi k i j p t) (hphi : initUPhi F lo hi k i j p t) : False := by
  obtain ⟨-, -, -, -, -, hp1⟩ := hplo
  obtain ⟨-, -, -, -, -, hp2⟩ := hphi
  omega

theorem initUpFinal_isSol (h : TopFacts lo hi k i j p)
    (hlo : lo ∈ Up F) (hhi : hi ∈ Down F) {tlo thi : ℕ}
    (g1 : initU0 lo hi k i j p ≤ tlo) (g2 : thi ≤ initU1 lo hi k i j p)
    (glt : tlo < thi) (gadj : thi ≤ tlo + 1)
    (hplo : initUPlo F lo hi k i j p tlo) (hphi : initUPhi F lo hi k i j p thi) :
    IsInitUp F lo hi k i
      ((initUpFinal lo hi k i j p tlo thi (F (segPt i j (sLo lo hi k i) k thi))).run F) := by
  obtain ⟨-, -, -, hki_lo, hj_lo, hp_lo⟩ := hplo
  obtain ⟨-, -, -, hki_hi, hj_hi, hp_hi⟩ := hphi
  have hL := h.segU_mem g1 (le_trans (by omega) g2)
  have hR := h.segU_mem (le_trans g1 (by omega)) g2
  have hLi := h.segU_i tlo
  have hLj := h.segU_j tlo
  have hLp := h.segU_p tlo
  have hRi := h.segU_i thi
  have hRj := h.segU_j thi
  have hRp := h.segU_p thi
  have hMle := h.m_add_le g2
  have hUi : lub (segPt i j (sLo lo hi k i) k tlo) (segPt i j (sLo lo hi k i) k thi) i = sLo lo hi k i := by
    rw [lub_apply, hLi, hRi]; omega
  have hUj : lub (segPt i j (sLo lo hi k i) k tlo) (segPt i j (sLo lo hi k i) k thi) j = thi := by rw [lub_apply, hLj, hRj]; omega
  have hUp : lub (segPt i j (sLo lo hi k i) k tlo) (segPt i j (sLo lo hi k i) k thi) p = k - sLo lo hi k i - tlo := by
    rw [lub_apply, hLp, hRp]; omega
  unfold initUpFinal
  rw [QueryAlg.run_bind, QueryAlg.run_pure]
  show IsLevelsetSol F lo hi k ((upOrVop (pick3 i j (segPt i j (sLo lo hi k i) k tlo) (segPt i j (sLo lo hi k i) k tlo) (segPt i j (sLo lo hi k i) k thi))
      (lub (segPt i j (sLo lo hi k i) k tlo) (segPt i j (sLo lo hi k i) k thi))).run F)
  refine upOrVop_isSol (fun l => ?_) (fun l => ?_) (lub_mem_Box hL hR) (fun l => ?_) ?_
  · rcases fin3_cover h.ij h.ip h.jp l with rfl | rfl | rfl
    · rw [pick3_i]; exact left_le_lub _ _
    · rw [pick3_j (Ne.symm h.ij)]; exact left_le_lub _ _
    · rw [pick3_other (Ne.symm h.ip) (Ne.symm h.jp)]; exact right_le_lub _ _
  · rcases fin3_cover h.ij h.ip h.jp l with rfl | rfl | rfl
    · rw [pick3_i, hUi]; exact hki_lo
    · rw [pick3_j (Ne.symm h.ij), hUj]; omega
    · rw [pick3_other (Ne.symm h.ip) (Ne.symm h.jp), hUp]; omega
  · rcases fin3_cover h.ij h.ip h.jp l with rfl | rfl | rfl
    · rw [pick3_i]; exact hL
    · rw [pick3_j (Ne.symm h.ij)]; exact hL
    · rw [pick3_other (Ne.symm h.ip) (Ne.symm h.jp)]; exact hR
  · have : lev (lub (segPt i j (sLo lo hi k i) k tlo) (segPt i j (sLo lo hi k i) k thi))
        = sLo lo hi k i + thi + (k - sLo lo hi k i - tlo) := by
      rw [lev_three _ h.ij h.ip h.jp, hUi, hUj, hUp]
    omega

/-- **HL Lemma 3.14**, upward half.  Either a solution of the levelset problem, or
an `i`-upward point at the smallest attainable `i`-coordinate. -/
theorem initUpAlg_isSol (h : TopFacts lo hi k i j p)
    (hlo : lo ∈ Up F) (hhi : hi ∈ Down F) {b : ℕ}
    (hb : initU1 lo hi k i j p - initU0 lo hi k i j p ≤ 2 ^ b) :
    IsInitUp F lo hi k i ((initUpAlg lo hi k i j p b).run F) := by
  have hT := h.U0_le_U1
  unfold initUpAlg
  rw [QueryAlg.run_bind, QueryAlg.run_ask]
  rcases hs0 : initUpStep lo hi k i j p (initU0 lo hi k i j p)
      (F (segPt i j (sLo lo hi k i) k (initU0 lo hi k i j p))) with alg | d0
  · exact initUpStep_isSol h hlo hhi le_rfl hT hs0
  · have hd0 := initUpStep_dir h hlo hhi le_rfl hT hs0
    have hplo : initUPlo F lo hi k i j p (initU0 lo hi k i j p) := by
      cases d0
      · exact absurd (hd0.2 rfl) (fun hx => initUPhi_U0_false h hx)
      · exact hd0.1 rfl
    rw [QueryAlg.run_bind, QueryAlg.run_ask]
    rcases hs1 : initUpStep lo hi k i j p (initU1 lo hi k i j p)
        (F (segPt i j (sLo lo hi k i) k (initU1 lo hi k i j p))) with alg | d1
    · exact initUpStep_isSol h hlo hhi hT le_rfl hs1
    · have hd1 := initUpStep_dir h hlo hhi hT le_rfl hs1
      have hphi : initUPhi F lo hi k i j p (initU1 lo hi k i j p) := by
        cases d1
        · exact hd1.2 rfl
        · exact absurd (hd1.1 rfl) (fun hx => initUPlo_U1_false h hx)
      have hlt : initU0 lo hi k i j p < initU1 lo hi k i j p := by
        rcases Nat.lt_or_ge (initU0 lo hi k i j p) (initU1 lo hi k i j p) with hh | hh
        · exact hh
        · exact absurd (initUPlo_initUPhi_ne h hplo (by
            have : initU1 lo hi k i j p = initU0 lo hi k i j p := by omega
            rw [← this]; exact hphi)) (by simp)
      exact segSearch_spec F (IsInitUp F lo hi k i)
        (initUPlo F lo hi k i j p) (initUPhi F lo hi k i j p)
        (initU0 lo hi k i j p) (initU1 lo hi k i j p)
        (fun t alg ha hb' hss => initUpStep_isSol h hlo hhi ha hb' hss)
        (fun t d ha hb' hss => initUpStep_dir h hlo hhi ha hb' hss)
        (fun tl th ha hb' hlt' hadj hpl hph =>
          initUpFinal_isSol h hlo hhi ha hb' hlt' hadj hpl hph)
        b _ _ hb le_rfl le_rfl hlt hplo hphi

end UpCorrect

end Tfnp.Tarski
