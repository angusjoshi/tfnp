/-
Copyright (c) 2026 Angus Joshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Angus Joshi
-/
import Tfnp.Tarski.LevelsetSearch

/-!
# Segments of a levelset, and binary search along them

Both remaining Haslebacher–Lill lemmas — 3.13 (a third configuration yields
progress) and 3.14 (initialising the six bounding points) — are binary searches
along a *segment* of the levelset: the coordinate `i` is frozen, coordinate `j`
carries the search parameter, and coordinate `p` takes up the slack so that the
level stays `k`.  This file provides the two reusable ingredients.

## Monotonicity, or a violation

Every step of HL §3 that concludes "…so this point is upward" does so by
monotonicity from points already queried.  In the total setting each such step must
instead produce a violation when monotonicity fails.  `upOrVop` and `downOrVop`
package that once and for all: given witnesses `wit l` already known to satisfy
`z l ≤ F (wit l) l`, one further query at `z` either confirms `z ∈ Up F` or exhibits
a violation between `z` and whichever witness the failing coordinate names.

That single pattern discharges *all* of HL's monotonicity appeals, which is what
keeps the total-setting version of the paper roughly the same size as the
promise-setting one.

## Segments

`segPt i j c k t` is the point of the levelset `L_k` with coordinate `i` equal to
`c` and coordinate `j` equal to `t`.  `segSearch` is the binary search: it
maintains `tlo < thi`, halves the gap, and stops when they are adjacent.  Its
`stepFn` may return a whole sub-algorithm, which is what lets a terminal branch
spend the extra query `upOrVop`/`downOrVop` needs.
-/

namespace Tfnp.Tarski

open QueryAlg (Bounded)

/-! ### Monotonicity or a violation -/

open Classical in
/-- Confirm `z` as an upward point, or expose a violation.  `wit l` is a point
already known to force `z l ≤ F (wit l) l`; if `z` fails to be upward in coordinate
`l`, then `F (wit l) l ≥ z l > F z l` while `wit l ≤ z`, a violation. -/
noncomputable def upOrVop (wit : Fin 3 → Pt 3) (z : Pt 3) :
    QueryAlg (Pt 3) (Pt 3) (InnerAnswer 3) :=
  QueryAlg.ask z >>= fun fz =>
    if h : z ≤ fz then QueryAlg.pure (.up z)
    else QueryAlg.pure (.vop (wit (failCoord h)) z)

open Classical in
/-- Confirm `z` as a downward point, or expose a violation. -/
noncomputable def downOrVop (wit : Fin 3 → Pt 3) (z : Pt 3) :
    QueryAlg (Pt 3) (Pt 3) (InnerAnswer 3) :=
  QueryAlg.ask z >>= fun fz =>
    if h : fz ≤ z then QueryAlg.pure (.down z)
    else QueryAlg.pure (.vop z (wit (failCoord h)))

lemma upOrVop_bounded (wit : Fin 3 → Pt 3) (z : Pt 3) : Bounded 1 (upOrVop wit z) := by
  refine Bounded.mono (n := 1 + 0) ((Bounded.ask _).bind fun fz => ?_) (by omega)
  split <;> exact Bounded.pure' _ _

lemma downOrVop_bounded (wit : Fin 3 → Pt 3) (z : Pt 3) : Bounded 1 (downOrVop wit z) := by
  refine Bounded.mono (n := 1 + 0) ((Bounded.ask _).bind fun fz => ?_) (by omega)
  split <;> exact Bounded.pure' _ _

variable {F : Pt 3 → Pt 3} {lo hi : Pt 3} {k : ℕ}

theorem upOrVop_isSol {wit : Fin 3 → Pt 3} {z : Pt 3}
    (hwle : ∀ l, wit l ≤ z) (hwF : ∀ l, z l ≤ F (wit l) l)
    (hzmem : z ∈ Box lo hi) (hwmem : ∀ l, wit l ∈ Box lo hi) (hlev : k ≤ lev z) :
    IsLevelsetSol F lo hi k ((upOrVop wit z).run F) := by
  change IsLevelsetSol F lo hi k ((QueryAlg.ask z >>= _).run F)
  rw [QueryAlg.run_bind, QueryAlg.run_ask]
  by_cases h : z ≤ F z
  · rw [dif_pos h]
    exact ⟨hzmem, hlev, mem_Up.mpr h⟩
  · rw [dif_neg h]
    refine ⟨hwmem _, hzmem, hwle _, fun hle => ?_⟩
    have h1 : F z (failCoord h) < z (failCoord h) := failCoord_spec h
    have h2 := hwF (failCoord h)
    have h3 := le_coord hle (failCoord h)
    omega

theorem downOrVop_isSol {wit : Fin 3 → Pt 3} {z : Pt 3}
    (hwle : ∀ l, z ≤ wit l) (hwF : ∀ l, F (wit l) l ≤ z l)
    (hzmem : z ∈ Box lo hi) (hwmem : ∀ l, wit l ∈ Box lo hi) (hlev : lev z ≤ k) :
    IsLevelsetSol F lo hi k ((downOrVop wit z).run F) := by
  change IsLevelsetSol F lo hi k ((QueryAlg.ask z >>= _).run F)
  rw [QueryAlg.run_bind, QueryAlg.run_ask]
  by_cases h : F z ≤ z
  · rw [dif_pos h]
    exact ⟨hzmem, hlev, mem_Down.mpr h⟩
  · rw [dif_neg h]
    refine ⟨hzmem, hwmem _, hwle _, fun hle => ?_⟩
    have h1 : z (failCoord h) < F z (failCoord h) := failCoord_spec h
    have h2 := hwF (failCoord h)
    have h3 := le_coord hle (failCoord h)
    omega

/-! ### Segments -/

/-- The point of `L_k` with coordinate `i` equal to `c` and coordinate `j` equal to
`t`; the remaining coordinate takes up the slack. -/
def segPt (i j : Fin 3) (c k t : ℕ) : Pt 3 :=
  fun l => if l = i then c else if l = j then t else k - c - t

@[simp] lemma segPt_i (i j : Fin 3) (c k t : ℕ) : segPt i j c k t i = c := by simp [segPt]

@[simp] lemma segPt_j {i j : Fin 3} (hji : j ≠ i) (c k t : ℕ) : segPt i j c k t j = t := by
  simp [segPt, hji]

lemma segPt_other {i j l : Fin 3} (hli : l ≠ i) (hlj : l ≠ j) (c k t : ℕ) :
    segPt i j c k t l = k - c - t := by simp [segPt, hli, hlj]

lemma lev_segPt {i j p : Fin 3} (hij : i ≠ j) (hip : i ≠ p) (hjp : j ≠ p)
    {c k t : ℕ} (h : c + t ≤ k) : lev (segPt i j c k t) = k := by
  rw [lev_three _ hij hip hjp, segPt_i, segPt_j (Ne.symm hij),
    segPt_other (Ne.symm hip) (Ne.symm hjp)]
  omega

/-- A segment point lies in the box as soon as its three coordinates do. -/
lemma segPt_mem_Box {i j p : Fin 3} (hij : i ≠ j) (hip : i ≠ p) (hjp : j ≠ p)
    {c k t : ℕ} {lo hi : Pt 3}
    (h1 : lo i ≤ c) (h2 : c ≤ hi i) (h3 : lo j ≤ t) (h4 : t ≤ hi j)
    (h5 : lo p ≤ k - c - t) (h6 : k - c - t ≤ hi p) :
    segPt i j c k t ∈ Box lo hi := by
  refine mem_Box.mpr ⟨coord_le fun l => ?_, coord_le fun l => ?_⟩ <;>
    rcases fin3_cover hij hip hjp l with rfl | rfl | rfl
  · rwa [segPt_i]
  · rwa [segPt_j (Ne.symm hij)]
  · rwa [segPt_other (Ne.symm hip) (Ne.symm hjp)]
  · rwa [segPt_i]
  · rwa [segPt_j (Ne.symm hij)]
  · rwa [segPt_other (Ne.symm hip) (Ne.symm hjp)]

/-! ### Binary search along a segment

`stepFn t v` reads the oracle's value `v = F (seg t)` and either returns a
sub-algorithm producing the final answer, or a direction: `true` moves the lower
endpoint up to `t`, `false` moves the upper endpoint down to `t`.  `finalFn` is
called once the endpoints are adjacent, with the value at the upper one. -/

noncomputable def segSearch {α : Type} (seg : ℕ → Pt 3)
    (stepFn : ℕ → Pt 3 → QueryAlg (Pt 3) (Pt 3) α ⊕ Bool)
    (finalFn : ℕ → ℕ → Pt 3 → QueryAlg (Pt 3) (Pt 3) α) :
    ℕ → ℕ → ℕ → QueryAlg (Pt 3) (Pt 3) α
  | 0, tlo, thi => QueryAlg.ask (seg thi) >>= fun v => finalFn tlo thi v
  | b + 1, tlo, thi =>
      if thi ≤ tlo + 1 then QueryAlg.ask (seg thi) >>= fun v => finalFn tlo thi v
      else
        QueryAlg.ask (seg ((tlo + thi) / 2)) >>= fun v =>
          match stepFn ((tlo + thi) / 2) v with
          | .inl alg => alg
          | .inr true => segSearch seg stepFn finalFn b ((tlo + thi) / 2) thi
          | .inr false => segSearch seg stepFn finalFn b tlo ((tlo + thi) / 2)

lemma segSearch_succ {α : Type} (seg : ℕ → Pt 3)
    (stepFn : ℕ → Pt 3 → QueryAlg (Pt 3) (Pt 3) α ⊕ Bool)
    (finalFn : ℕ → ℕ → Pt 3 → QueryAlg (Pt 3) (Pt 3) α) (b tlo thi : ℕ) :
    segSearch seg stepFn finalFn (b + 1) tlo thi =
      (if thi ≤ tlo + 1 then QueryAlg.ask (seg thi) >>= fun v => finalFn tlo thi v
      else
        QueryAlg.ask (seg ((tlo + thi) / 2)) >>= fun v =>
          match stepFn ((tlo + thi) / 2) v with
          | .inl alg => alg
          | .inr true => segSearch seg stepFn finalFn b ((tlo + thi) / 2) thi
          | .inr false => segSearch seg stepFn finalFn b tlo ((tlo + thi) / 2)) := rfl

lemma segSearch_bounded {α : Type} {seg : ℕ → Pt 3}
    {stepFn : ℕ → Pt 3 → QueryAlg (Pt 3) (Pt 3) α ⊕ Bool}
    {finalFn : ℕ → ℕ → Pt 3 → QueryAlg (Pt 3) (Pt 3) α} {c : ℕ}
    (hstep : ∀ t v alg, stepFn t v = .inl alg → Bounded c alg)
    (hfinal : ∀ tlo thi v, Bounded c (finalFn tlo thi v)) :
    ∀ (b tlo thi : ℕ), Bounded (b + 1 + c) (segSearch seg stepFn finalFn b tlo thi) := by
  intro b
  induction b with
  | zero =>
    intro tlo thi
    exact Bounded.mono (n := 1 + c) ((Bounded.ask _).bind fun v => hfinal tlo thi v) (by omega)
  | succ b ih =>
    intro tlo thi
    rw [segSearch_succ]
    by_cases h : thi ≤ tlo + 1
    · rw [if_pos h]
      exact Bounded.mono (n := 1 + c) ((Bounded.ask _).bind fun v => hfinal tlo thi v) (by omega)
    · rw [if_neg h]
      refine Bounded.mono (n := 1 + (b + 1 + c)) ((Bounded.ask _).bind fun v => ?_) (by omega)
      rcases hs : stepFn ((tlo + thi) / 2) v with alg | dir
      · exact (hstep _ _ _ hs).mono (by omega)
      · cases dir
        · exact ih tlo ((tlo + thi) / 2)
        · exact ih ((tlo + thi) / 2) thi

set_option linter.unusedTactic false in
/-- **Correctness of the segment search.**  `Plo`/`Phi` are the invariants carried
by the two endpoints; the search preserves them, halves the gap, and hands adjacent
endpoints to `finalFn`. -/
theorem segSearch_spec {α : Type} {seg : ℕ → Pt 3}
    {stepFn : ℕ → Pt 3 → QueryAlg (Pt 3) (Pt 3) α ⊕ Bool}
    {finalFn : ℕ → ℕ → Pt 3 → QueryAlg (Pt 3) (Pt 3) α}
    (F : Pt 3 → Pt 3) (Good : α → Prop) (Plo Phi : ℕ → Prop) (T0 T1 : ℕ)
    (hstep : ∀ t alg, T0 ≤ t → t ≤ T1 → stepFn t (F (seg t)) = .inl alg → Good (alg.run F))
    (hdir : ∀ t dir, T0 ≤ t → t ≤ T1 → stepFn t (F (seg t)) = .inr dir →
        (dir = true → Plo t) ∧ (dir = false → Phi t))
    (hfinal : ∀ tlo thi, T0 ≤ tlo → thi ≤ T1 → tlo < thi → thi ≤ tlo + 1 →
        Plo tlo → Phi thi → Good ((finalFn tlo thi (F (seg thi))).run F)) :
    ∀ (b tlo thi : ℕ), thi - tlo ≤ 2 ^ b → T0 ≤ tlo → thi ≤ T1 → tlo < thi →
      Plo tlo → Phi thi → Good ((segSearch seg stepFn finalFn b tlo thi).run F) := by
  intro b
  induction b with
  | zero =>
    intro tlo thi hgap h0 h1 hlt hplo hphi
    change Good ((QueryAlg.ask (seg thi) >>= _).run F)
    rw [QueryAlg.run_bind, QueryAlg.run_ask]
    exact hfinal tlo thi h0 h1 hlt (by simp at hgap; omega) hplo hphi
    
  | succ b ih =>
    intro tlo thi hgap h0 h1 hlt hplo hphi
    rw [segSearch_succ]
    by_cases hadj : thi ≤ tlo + 1
    · rw [if_pos hadj]
      change Good ((QueryAlg.ask (seg thi) >>= _).run F)
      rw [QueryAlg.run_bind, QueryAlg.run_ask]
      exact hfinal tlo thi h0 h1 hlt hadj hplo hphi
    · rw [if_neg hadj]
      push Not at hadj
      set m := (tlo + thi) / 2 with hm
      have hmlt : tlo < m ∧ m < thi := by rw [hm]; omega
      have hmpow : (2 : ℕ) ^ (b + 1) = 2 * 2 ^ b := by ring
      rw [QueryAlg.run_bind, QueryAlg.run_ask]
      rcases hs : stepFn m (F (seg m)) with alg | dir
      · exact hstep m alg (by omega) (by omega) hs
      · have hd := hdir m dir (by omega) (by omega) hs
        cases dir
        · exact ih tlo m (by rw [hm]; omega) h0 (by omega) hmlt.1 hplo (hd.2 rfl)
        · exact ih m thi (by rw [hm]; omega) (by omega) h1 hmlt.2 (hd.1 rfl) hphi

end Tfnp.Tarski
