/-
Copyright (c) 2026 Angus Joshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Angus Joshi
-/
import Tfnp.Tarski.LevelsetSegment

/-!
# HL Lemma 3.13: a third configuration yields progress

The one configuration that does not immediately give a point.  `x` is `i`-upward,
`y` is `i`-downward, and they are within one of each other in coordinate `i` — so
neither the meet nor the join is forced to be monotone in coordinate `i`, and HL
spend `O(log N)` further queries.

Set-up.  Since `x ≠ y` (a point cannot be both `i`-upward and `i`-downward) and
both lie on `L_k` with `x i ≤ y i`, some other coordinate has `y j < x j`; the third
then satisfies `x p ≤ y p`.  Two easy cases dispose of the extremes:

* if `F x j = x j` the join `x ⊔ y` is upward;
* if `F y j = y j` the meet `x ⊓ y` is downward.

Otherwise `F x j < x j` and `y j < F y j`, and the search runs along the segment of
`L_k` with coordinate `i` frozen at `y i` and coordinate `j` ranging over
`[y j, x j - 1]`.  Every point `q` of that segment falls into one of four cases
according to the signs at `i` and `j`; two give progress outright (`q ⊔ y` upward,
`x ⊓ q` downward) and two are HL's types (1) and (2), which drive the binary
search.  Adjacent endpoints of opposite type then give the meet or the join
depending on the sign at `p`.

## Main results

* `config3Alg` — the algorithm.
* `config3Alg_isSol` — **HL Lemma 3.13**.
* `config3Alg_bounded` — `⌈log₂ (x j - y j)⌉ + 5` queries.
-/

namespace Tfnp.Tarski

open QueryAlg (Bounded)

/-! ### Choosing by coordinate -/

/-- Select one of three values according to which of `i`, `j` or the third
coordinate is given.  Used both for segment points and for witness families. -/
def pick3 {β : Type} (i j : Fin 3) (A B C : β) : Fin 3 → β :=
  fun l => if l = i then A else if l = j then B else C

@[simp] lemma pick3_i {β : Type} (i j : Fin 3) (A B C : β) : pick3 i j A B C i = A := by
  simp [pick3]

@[simp] lemma pick3_j {β : Type} {i j : Fin 3} (hji : j ≠ i) (A B C : β) :
    pick3 i j A B C j = B := by simp [pick3, hji]

lemma pick3_other {β : Type} {i j l : Fin 3} (hli : l ≠ i) (hlj : l ≠ j) (A B C : β) :
    pick3 i j A B C l = C := by simp [pick3, hli, hlj]

/-! ### The hypotheses of a third configuration -/

/-- The data HL Lemma 3.13 starts from, with the coordinates named. -/
structure C3 (F : Pt 3 → Pt 3) (lo hi : Pt 3) (k : ℕ) (i j p : Fin 3) (x y : Pt 3) : Prop where
  /-- `i ≠ j`. -/
  ij : i ≠ j
  /-- `i ≠ p`. -/
  ip : i ≠ p
  /-- `j ≠ p`. -/
  jp : j ≠ p
  /-- `x` lies in the box. -/
  xmem : x ∈ Box lo hi
  /-- `y` lies in the box. -/
  ymem : y ∈ Box lo hi
  /-- `x` lies on the levelset. -/
  xlev : lev x = k
  /-- `y` lies on the levelset. -/
  ylev : lev y = k
  /-- `x` is `i`-upward. -/
  xup : IUp F x i
  /-- `y` is `i`-downward. -/
  ydown : IDown F y i
  /-- `x i ≤ y i`. -/
  le_i : x i ≤ y i
  /-- `y i ≤ x i + 1`. -/
  close_i : y i ≤ x i + 1
  /-- `y` falls short of `x` in coordinate `j`. -/
  lt_j : y j < x j

namespace C3

variable {F : Pt 3 → Pt 3} {lo hi : Pt 3} {k : ℕ} {i j p : Fin 3} {x y : Pt 3}

lemma xlev' (h : C3 F lo hi k i j p x y) : lev x = x i + x j + x p :=
  lev_three x h.ij h.ip h.jp

lemma ylev' (h : C3 F lo hi k i j p x y) : lev y = y i + y j + y p :=
  lev_three y h.ij h.ip h.jp

/-- The third coordinate compensates: `x p ≤ y p`. -/
lemma le_p (h : C3 F lo hi k i j p x y) : x p ≤ y p := by
  have h1 := h.xlev'
  have h2 := h.ylev'
  have h3 := h.xlev
  have h4 := h.ylev
  have := h.le_i
  have := h.close_i
  have := h.lt_j
  omega

lemma Fx_j (h : C3 F lo hi k i j p x y) : F x j ≤ x j := h.xup.2 j (Ne.symm h.ij)
lemma Fx_p (h : C3 F lo hi k i j p x y) : F x p ≤ x p := h.xup.2 p (Ne.symm h.ip)
lemma Fx_i (h : C3 F lo hi k i j p x y) : x i + 1 ≤ F x i := h.xup.1
lemma Fy_j (h : C3 F lo hi k i j p x y) : y j ≤ F y j := h.ydown.2 j (Ne.symm h.ij)
lemma Fy_p (h : C3 F lo hi k i j p x y) : y p ≤ F y p := h.ydown.2 p (Ne.symm h.ip)
lemma Fy_i (h : C3 F lo hi k i j p x y) : F y i + 1 ≤ y i := h.ydown.1

end C3

/-! ### The two easy cases

`x ⊔ y = (y i, x j, y p)` and `x ⊓ y = (x i, y j, x p)`, using `x i ≤ y i`,
`y j < x j` and `x p ≤ y p`. -/

section Easy

variable {F : Pt 3 → Pt 3} {lo hi : Pt 3} {k : ℕ} {i j p : Fin 3} {x y : Pt 3}

/-- If `F` fixes `x` in coordinate `j`, the join is upward. -/
theorem lubXY_isSol (h : C3 F lo hi k i j p x y) (hfx : F x j = x j) :
    IsLevelsetSol F lo hi k ((upOrVop (pick3 i j x x y) (lub x y)).run F) := by
  have hi' := h.le_i
  have hj' := h.lt_j
  have hp := h.le_p
  have hlub_i : lub x y i = y i := by simp [lub]; omega
  have hlub_j : lub x y j = x j := by simp [lub]; omega
  have hlub_p : lub x y p = y p := by simp [lub]; omega
  refine upOrVop_isSol (fun l => ?_) (fun l => ?_) (lub_mem_Box h.xmem h.ymem)
    (fun l => ?_) ?_
  · rcases fin3_cover h.ij h.ip h.jp l with rfl | rfl | rfl
    · rw [pick3_i]; exact left_le_lub x y
    · rw [pick3_j (Ne.symm h.ij)]; exact left_le_lub x y
    · rw [pick3_other (Ne.symm h.ip) (Ne.symm h.jp)]; exact right_le_lub x y
  · rcases fin3_cover h.ij h.ip h.jp l with rfl | rfl | rfl
    · rw [pick3_i, hlub_i]
      have := h.Fx_i; have := h.close_i; omega
    · rw [pick3_j (Ne.symm h.ij), hlub_j]; omega
    · rw [pick3_other (Ne.symm h.ip) (Ne.symm h.jp), hlub_p]; exact h.Fy_p
  · rcases fin3_cover h.ij h.ip h.jp l with rfl | rfl | rfl
    · rw [pick3_i]; exact h.xmem
    · rw [pick3_j (Ne.symm h.ij)]; exact h.xmem
    · rw [pick3_other (Ne.symm h.ip) (Ne.symm h.jp)]; exact h.ymem
  · rw [← h.xlev]
    exact lev_mono (left_le_lub x y)

/-- If `F` weakly decreases `x` in coordinate `j` past `y j`, the meet is downward.
This covers both HL's `F y j = y j` case and the degenerate `x j = y j + 1`. -/
theorem glbXY_isSol (h : C3 F lo hi k i j p x y) (hfx : F x j ≤ y j) :
    IsLevelsetSol F lo hi k ((downOrVop (pick3 i j y x x) (glb x y)).run F) := by
  have hi' := h.le_i
  have hj' := h.lt_j
  have hp := h.le_p
  have hglb_i : glb x y i = x i := by simp [glb]; omega
  have hglb_j : glb x y j = y j := by simp [glb]; omega
  have hglb_p : glb x y p = x p := by simp [glb]; omega
  refine downOrVop_isSol (fun l => ?_) (fun l => ?_) (glb_mem_Box h.xmem h.ymem)
    (fun l => ?_) ?_
  · rcases fin3_cover h.ij h.ip h.jp l with rfl | rfl | rfl
    · rw [pick3_i]; exact glb_le_right x y
    · rw [pick3_j (Ne.symm h.ij)]; exact glb_le_left x y
    · rw [pick3_other (Ne.symm h.ip) (Ne.symm h.jp)]; exact glb_le_left x y
  · rcases fin3_cover h.ij h.ip h.jp l with rfl | rfl | rfl
    · rw [pick3_i, hglb_i]
      have := h.Fy_i; have := h.close_i; omega
    · rw [pick3_j (Ne.symm h.ij), hglb_j]; exact hfx
    · rw [pick3_other (Ne.symm h.ip) (Ne.symm h.jp), hglb_p]; exact h.Fx_p
  · rcases fin3_cover h.ij h.ip h.jp l with rfl | rfl | rfl
    · rw [pick3_i]; exact h.ymem
    · rw [pick3_j (Ne.symm h.ij)]; exact h.xmem
    · rw [pick3_other (Ne.symm h.ip) (Ne.symm h.jp)]; exact h.xmem
  · rw [← h.xlev]
    exact lev_mono (glb_le_left x y)

/-- The other easy case: if `F` fixes `y` in coordinate `j`, the meet is downward. -/
theorem glbXY_isSol' (h : C3 F lo hi k i j p x y) (hfy : F y j = y j) :
    IsLevelsetSol F lo hi k ((downOrVop (pick3 i j y y x) (glb x y)).run F) := by
  have hi' := h.le_i
  have hj' := h.lt_j
  have hp := h.le_p
  have hglb_i : glb x y i = x i := by simp [glb]; omega
  have hglb_j : glb x y j = y j := by simp [glb]; omega
  have hglb_p : glb x y p = x p := by simp [glb]; omega
  refine downOrVop_isSol (fun l => ?_) (fun l => ?_) (glb_mem_Box h.xmem h.ymem)
    (fun l => ?_) ?_
  · rcases fin3_cover h.ij h.ip h.jp l with rfl | rfl | rfl
    · rw [pick3_i]; exact glb_le_right x y
    · rw [pick3_j (Ne.symm h.ij)]; exact glb_le_right x y
    · rw [pick3_other (Ne.symm h.ip) (Ne.symm h.jp)]; exact glb_le_left x y
  · rcases fin3_cover h.ij h.ip h.jp l with rfl | rfl | rfl
    · rw [pick3_i, hglb_i]
      have := h.Fy_i; have := h.close_i; omega
    · rw [pick3_j (Ne.symm h.ij), hglb_j]; omega
    · rw [pick3_other (Ne.symm h.ip) (Ne.symm h.jp), hglb_p]; exact h.Fx_p
  · rcases fin3_cover h.ij h.ip h.jp l with rfl | rfl | rfl
    · rw [pick3_i]; exact h.ymem
    · rw [pick3_j (Ne.symm h.ij)]; exact h.ymem
    · rw [pick3_other (Ne.symm h.ip) (Ne.symm h.jp)]; exact h.xmem
  · rw [← h.xlev]
    exact lev_mono (glb_le_left x y)

end Easy

/-! ### Case C: the segment search

`F x j < x j` and `y j < F y j`.  The segment freezes coordinate `i` at `y i` and
lets coordinate `j` run over `[y j, x j - 1]`; its bottom point is `y` itself. -/

section CaseC

variable {F : Pt 3 → Pt 3} {lo hi : Pt 3} {k : ℕ} {i j p : Fin 3} {x y : Pt 3}

lemma c3seg_i (_h : C3 F lo hi k i j p x y) (t : ℕ) : segPt i j (y i) k t i = y i :=
  segPt_i _ _ _ _ _
lemma c3seg_j (h : C3 F lo hi k i j p x y) (t : ℕ) : segPt i j (y i) k t j = t :=
  segPt_j (Ne.symm h.ij) _ _ _
lemma c3seg_p (h : C3 F lo hi k i j p x y) (t : ℕ) : segPt i j (y i) k t p = k - y i - t :=
  segPt_other (Ne.symm h.ip) (Ne.symm h.jp) _ _ _

lemma c3_ylev (h : C3 F lo hi k i j p x y) : y i + y j + y p = k := by
  have := h.ylev'; have := h.ylev; omega

lemma c3_xlev (h : C3 F lo hi k i j p x y) : x i + x j + x p = k := by
  have := h.xlev'; have := h.xlev; omega

/-- The bottom of the search segment is `y` itself. -/
lemma c3seg_y (h : C3 F lo hi k i j p x y) : segPt i j (y i) k (y j) = y := by
  funext l
  rcases fin3_cover h.ij h.ip h.jp l with rfl | rfl | rfl
  · rw [c3seg_i h]
  · rw [c3seg_j h]
  · rw [c3seg_p h]; have := c3_ylev h; omega

/-- Segment points lie in the box. -/
lemma c3seg_mem (h : C3 F lo hi k i j p x y) {t : ℕ} (h1 : y j ≤ t) (h2 : t + 1 ≤ x j) :
    segPt i j (y i) k t ∈ Box lo hi := by
  have hy := mem_Box.mp h.ymem
  have hx := mem_Box.mp h.xmem
  have hyp := c3_ylev h
  have hxp := c3_xlev h
  have h3 := le_coord hy.2 p
  have h4 := le_coord hx.1 p
  have h5 := h.close_i
  refine segPt_mem_Box h.ij h.ip h.jp (le_coord hy.1 i) (le_coord hy.2 i)
    (le_trans (le_coord hy.1 j) h1) (le_trans (by omega) (le_coord hx.2 j)) (by omega) (by omega)

/-! #### The four rules -/

/-- A segment point that goes up in coordinates `i` and `j` gives an upward join
with `y`. -/
theorem c3_lub_isSol (h : C3 F lo hi k i j p x y) {t : ℕ} (h1 : y j ≤ t) (h2 : t + 1 ≤ x j)
    (hi' : y i ≤ F (segPt i j (y i) k t) i) (hj' : t ≤ F (segPt i j (y i) k t) j) :
    IsLevelsetSol F lo hi k
      ((upOrVop (pick3 i j (segPt i j (y i) k t) (segPt i j (y i) k t) y)
        (lub (segPt i j (y i) k t) y)).run F) := by
  have hq := c3seg_mem h h1 h2
  have hqi := c3seg_i h t
  have hqj := c3seg_j h t
  have hqp := c3seg_p h t
  have hyp := c3_ylev h
  have hL_i : lub (segPt i j (y i) k t) y i = y i := by rw [lub_apply, hqi]; omega
  have hL_j : lub (segPt i j (y i) k t) y j = t := by rw [lub_apply, hqj]; omega
  have hL_p : lub (segPt i j (y i) k t) y p = y p := by rw [lub_apply, hqp]; omega
  refine upOrVop_isSol (fun l => ?_) (fun l => ?_) (lub_mem_Box hq h.ymem) (fun l => ?_) ?_
  · rcases fin3_cover h.ij h.ip h.jp l with rfl | rfl | rfl
    · rw [pick3_i]; exact left_le_lub _ _
    · rw [pick3_j (Ne.symm h.ij)]; exact left_le_lub _ _
    · rw [pick3_other (Ne.symm h.ip) (Ne.symm h.jp)]; exact right_le_lub _ _
  · rcases fin3_cover h.ij h.ip h.jp l with rfl | rfl | rfl
    · rw [pick3_i, hL_i]; exact hi'
    · rw [pick3_j (Ne.symm h.ij), hL_j]; exact hj'
    · rw [pick3_other (Ne.symm h.ip) (Ne.symm h.jp), hL_p]; exact h.Fy_p
  · rcases fin3_cover h.ij h.ip h.jp l with rfl | rfl | rfl
    · rw [pick3_i]; exact hq
    · rw [pick3_j (Ne.symm h.ij)]; exact hq
    · rw [pick3_other (Ne.symm h.ip) (Ne.symm h.jp)]; exact h.ymem
  · rw [← h.ylev]; exact lev_mono (right_le_lub _ _)

/-- A segment point that goes down in coordinates `i` and `j` gives a downward meet
with `x`. -/
theorem c3_glb_isSol (h : C3 F lo hi k i j p x y) {t : ℕ} (h1 : y j ≤ t) (h2 : t + 1 ≤ x j)
    (hi' : F (segPt i j (y i) k t) i < y i) (hj' : F (segPt i j (y i) k t) j ≤ t) :
    IsLevelsetSol F lo hi k
      ((downOrVop (pick3 i j (segPt i j (y i) k t) (segPt i j (y i) k t) x)
        (glb x (segPt i j (y i) k t))).run F) := by
  have hq := c3seg_mem h h1 h2
  have hqi := c3seg_i h t
  have hqj := c3seg_j h t
  have hqp := c3seg_p h t
  have hxp := c3_xlev h
  have hci := h.close_i
  have hli := h.le_i
  have hG_i : glb x (segPt i j (y i) k t) i = x i := by rw [glb_apply, hqi]; omega
  have hG_j : glb x (segPt i j (y i) k t) j = t := by rw [glb_apply, hqj]; omega
  have hG_p : glb x (segPt i j (y i) k t) p = x p := by rw [glb_apply, hqp]; omega
  refine downOrVop_isSol (fun l => ?_) (fun l => ?_) (glb_mem_Box h.xmem hq) (fun l => ?_) ?_
  · rcases fin3_cover h.ij h.ip h.jp l with rfl | rfl | rfl
    · rw [pick3_i]; exact glb_le_right _ _
    · rw [pick3_j (Ne.symm h.ij)]; exact glb_le_right _ _
    · rw [pick3_other (Ne.symm h.ip) (Ne.symm h.jp)]; exact glb_le_left _ _
  · rcases fin3_cover h.ij h.ip h.jp l with rfl | rfl | rfl
    · rw [pick3_i, hG_i]; omega
    · rw [pick3_j (Ne.symm h.ij), hG_j]; exact hj'
    · rw [pick3_other (Ne.symm h.ip) (Ne.symm h.jp), hG_p]; exact h.Fx_p
  · rcases fin3_cover h.ij h.ip h.jp l with rfl | rfl | rfl
    · rw [pick3_i]; exact hq
    · rw [pick3_j (Ne.symm h.ij)]; exact hq
    · rw [pick3_other (Ne.symm h.ip) (Ne.symm h.jp)]; exact h.xmem
  · rw [← h.xlev]; exact lev_mono (glb_le_left _ _)

/-- At the *top* of the segment a point going down in coordinate `i` gives a
downward meet with `x`, whatever it does in coordinate `j`: coordinate `j` is
witnessed by `x` itself, since `F x j ≤ x j - 1` is exactly the top index. -/
theorem c3_glb_top_isSol (h : C3 F lo hi k i j p x y) (hfx : F x j + 1 ≤ x j)
    (h1 : y j + 1 ≤ x j - 1)
    (hi' : F (segPt i j (y i) k (x j - 1)) i < y i) :
    IsLevelsetSol F lo hi k
      ((downOrVop (pick3 i j (segPt i j (y i) k (x j - 1)) x x)
        (glb x (segPt i j (y i) k (x j - 1)))).run F) := by
  have hq := c3seg_mem (t := x j - 1) h (by omega) (by omega)
  have hqi := c3seg_i h (x j - 1)
  have hqj := c3seg_j h (x j - 1)
  have hqp := c3seg_p h (x j - 1)
  have hxp := c3_xlev h
  have hci := h.close_i
  have hli := h.le_i
  have hG_i : glb x (segPt i j (y i) k (x j - 1)) i = x i := by rw [glb_apply, hqi]; omega
  have hG_j : glb x (segPt i j (y i) k (x j - 1)) j = x j - 1 := by rw [glb_apply, hqj]; omega
  have hG_p : glb x (segPt i j (y i) k (x j - 1)) p = x p := by rw [glb_apply, hqp]; omega
  refine downOrVop_isSol (fun l => ?_) (fun l => ?_) (glb_mem_Box h.xmem hq) (fun l => ?_) ?_
  · rcases fin3_cover h.ij h.ip h.jp l with rfl | rfl | rfl
    · rw [pick3_i]; exact glb_le_right _ _
    · rw [pick3_j (Ne.symm h.ij)]; exact glb_le_left _ _
    · rw [pick3_other (Ne.symm h.ip) (Ne.symm h.jp)]; exact glb_le_left _ _
  · rcases fin3_cover h.ij h.ip h.jp l with rfl | rfl | rfl
    · rw [pick3_i, hG_i]; omega
    · rw [pick3_j (Ne.symm h.ij), hG_j]; omega
    · rw [pick3_other (Ne.symm h.ip) (Ne.symm h.jp), hG_p]; exact h.Fx_p
  · rcases fin3_cover h.ij h.ip h.jp l with rfl | rfl | rfl
    · rw [pick3_i]; exact hq
    · rw [pick3_j (Ne.symm h.ij)]; exact h.xmem
    · rw [pick3_other (Ne.symm h.ip) (Ne.symm h.jp)]; exact h.xmem
  · rw [← h.xlev]; exact lev_mono (glb_le_left _ _)

/-! #### The endgame: adjacent endpoints of opposite type -/

/-- Adjacent endpoints with `F` weakly decreasing the upper one in coordinate `p`:
the meet is downward. -/
theorem c3_end_glb (h : C3 F lo hi k i j p x y) {tlo thi : ℕ}
    (h1 : y j ≤ tlo) (h2 : thi + 1 ≤ x j) (hadj : thi = tlo + 1)
    (hlo2 : F (segPt i j (y i) k tlo) i < y i)
    (hhi1 : F (segPt i j (y i) k thi) j < thi)
    (hp' : F (segPt i j (y i) k thi) p ≤ k - y i - thi) :
    IsLevelsetSol F lo hi k
      ((downOrVop (pick3 i j (segPt i j (y i) k tlo) (segPt i j (y i) k thi)
        (segPt i j (y i) k thi))
        (glb (segPt i j (y i) k tlo) (segPt i j (y i) k thi))).run F) := by
  have hL := c3seg_mem h h1 (by omega)
  have hR := c3seg_mem h (by omega) h2
  have hLi := c3seg_i h tlo
  have hLj := c3seg_j h tlo
  have hLp := c3seg_p h tlo
  have hRi := c3seg_i h thi
  have hRj := c3seg_j h thi
  have hRp := c3seg_p h thi
  have hyp := c3_ylev h
  have hkey : y i + thi ≤ k := by
    have hxp := c3_xlev h
    have := h.close_i
    omega
  have hG_i : glb (segPt i j (y i) k tlo) (segPt i j (y i) k thi) i = y i := by
    rw [glb_apply, hLi, hRi]; omega
  have hG_j : glb (segPt i j (y i) k tlo) (segPt i j (y i) k thi) j = tlo := by
    rw [glb_apply, hLj, hRj]; omega
  have hG_p : glb (segPt i j (y i) k tlo) (segPt i j (y i) k thi) p = k - y i - thi := by
    rw [glb_apply, hLp, hRp]; omega
  refine downOrVop_isSol (fun l => ?_) (fun l => ?_) (glb_mem_Box hL hR) (fun l => ?_) ?_
  · rcases fin3_cover h.ij h.ip h.jp l with rfl | rfl | rfl
    · rw [pick3_i]; exact glb_le_left _ _
    · rw [pick3_j (Ne.symm h.ij)]; exact glb_le_right _ _
    · rw [pick3_other (Ne.symm h.ip) (Ne.symm h.jp)]; exact glb_le_right _ _
  · rcases fin3_cover h.ij h.ip h.jp l with rfl | rfl | rfl
    · rw [pick3_i, hG_i]; omega
    · rw [pick3_j (Ne.symm h.ij), hG_j]; omega
    · rw [pick3_other (Ne.symm h.ip) (Ne.symm h.jp), hG_p]; exact hp'
  · rcases fin3_cover h.ij h.ip h.jp l with rfl | rfl | rfl
    · rw [pick3_i]; exact hL
    · rw [pick3_j (Ne.symm h.ij)]; exact hR
    · rw [pick3_other (Ne.symm h.ip) (Ne.symm h.jp)]; exact hR
  · have : lev (glb (segPt i j (y i) k tlo) (segPt i j (y i) k thi))
        = y i + tlo + (k - y i - thi) := by
      rw [lev_three _ h.ij h.ip h.jp, hG_i, hG_j, hG_p]
    omega

/-- Adjacent endpoints with `F` strictly increasing the upper one in coordinate `p`:
the join is upward. -/
theorem c3_end_lub (h : C3 F lo hi k i j p x y) {tlo thi : ℕ}
    (h1 : y j ≤ tlo) (h2 : thi + 1 ≤ x j) (hadj : thi = tlo + 1)
    (hlo2 : tlo < F (segPt i j (y i) k tlo) j)
    (hhi1 : y i ≤ F (segPt i j (y i) k thi) i)
    (hp' : k - y i - thi < F (segPt i j (y i) k thi) p) :
    IsLevelsetSol F lo hi k
      ((upOrVop (pick3 i j (segPt i j (y i) k thi) (segPt i j (y i) k tlo)
        (segPt i j (y i) k thi))
        (lub (segPt i j (y i) k tlo) (segPt i j (y i) k thi))).run F) := by
  have hL := c3seg_mem h h1 (by omega)
  have hR := c3seg_mem h (by omega) h2
  have hLi := c3seg_i h tlo
  have hLj := c3seg_j h tlo
  have hLp := c3seg_p h tlo
  have hRi := c3seg_i h thi
  have hRj := c3seg_j h thi
  have hRp := c3seg_p h thi
  have hyp := c3_ylev h
  have hkey : y i + thi ≤ k := by
    have hxp := c3_xlev h
    have := h.close_i
    omega
  have hU_i : lub (segPt i j (y i) k tlo) (segPt i j (y i) k thi) i = y i := by
    rw [lub_apply, hLi, hRi]; omega
  have hU_j : lub (segPt i j (y i) k tlo) (segPt i j (y i) k thi) j = thi := by
    rw [lub_apply, hLj, hRj]; omega
  have hU_p : lub (segPt i j (y i) k tlo) (segPt i j (y i) k thi) p = k - y i - tlo := by
    rw [lub_apply, hLp, hRp]; omega
  refine upOrVop_isSol (fun l => ?_) (fun l => ?_) (lub_mem_Box hL hR) (fun l => ?_) ?_
  · rcases fin3_cover h.ij h.ip h.jp l with rfl | rfl | rfl
    · rw [pick3_i]; exact right_le_lub _ _
    · rw [pick3_j (Ne.symm h.ij)]; exact left_le_lub _ _
    · rw [pick3_other (Ne.symm h.ip) (Ne.symm h.jp)]; exact right_le_lub _ _
  · rcases fin3_cover h.ij h.ip h.jp l with rfl | rfl | rfl
    · rw [pick3_i, hU_i]; exact hhi1
    · rw [pick3_j (Ne.symm h.ij), hU_j]; omega
    · rw [pick3_other (Ne.symm h.ip) (Ne.symm h.jp), hU_p]; omega
  · rcases fin3_cover h.ij h.ip h.jp l with rfl | rfl | rfl
    · rw [pick3_i]; exact hR
    · rw [pick3_j (Ne.symm h.ij)]; exact hL
    · rw [pick3_other (Ne.symm h.ip) (Ne.symm h.jp)]; exact hR
  · have : lev (lub (segPt i j (y i) k tlo) (segPt i j (y i) k thi))
        = y i + thi + (k - y i - tlo) := by
      rw [lev_three _ h.ij h.ip h.jp, hU_i, hU_j, hU_p]
    omega

end CaseC

/-! ### The algorithm -/

/-- One step of the search: classify the queried segment point.  Two of the four
sign patterns give progress outright; the other two are HL's types (1) and (2),
which move the upper and lower endpoint respectively. -/
noncomputable def c3Step (i j : Fin 3) (k : ℕ) (x y : Pt 3) (t : ℕ) (v : Pt 3) :
    QueryAlg (Pt 3) (Pt 3) (InnerAnswer 3) ⊕ Bool :=
  if y i ≤ v i then
    if t ≤ v j then
      .inl (upOrVop (pick3 i j (segPt i j (y i) k t) (segPt i j (y i) k t) y)
        (lub (segPt i j (y i) k t) y))
    else .inr false
  else
    if v j ≤ t then
      .inl (downOrVop (pick3 i j (segPt i j (y i) k t) (segPt i j (y i) k t) x)
        (glb x (segPt i j (y i) k t)))
    else .inr true

/-- The endgame: adjacent endpoints of opposite type, resolved by the sign at the
third coordinate. -/
noncomputable def c3Final (i j p : Fin 3) (k : ℕ) (y : Pt 3) (tlo thi : ℕ) (v : Pt 3) :
    QueryAlg (Pt 3) (Pt 3) (InnerAnswer 3) :=
  if v p ≤ k - y i - thi then
    downOrVop (pick3 i j (segPt i j (y i) k tlo) (segPt i j (y i) k thi)
      (segPt i j (y i) k thi)) (glb (segPt i j (y i) k tlo) (segPt i j (y i) k thi))
  else
    upOrVop (pick3 i j (segPt i j (y i) k thi) (segPt i j (y i) k tlo)
      (segPt i j (y i) k thi)) (lub (segPt i j (y i) k tlo) (segPt i j (y i) k thi))

/-- **HL Lemma 3.13's algorithm.**  Two easy cases, then a binary search along the
segment. -/
noncomputable def config3Alg (i j p : Fin 3) (k : ℕ) (x y : Pt 3) (b : ℕ) :
    QueryAlg (Pt 3) (Pt 3) (InnerAnswer 3) :=
  QueryAlg.ask x >>= fun fx =>
    if fx j = x j then
      upOrVop (pick3 i j x x y) (lub x y)
    else if fx j ≤ y j then
      downOrVop (pick3 i j y x x) (glb x y)
    else
      QueryAlg.ask y >>= fun fy =>
        if fy j = y j then
          downOrVop (pick3 i j y y x) (glb x y)
        else
          QueryAlg.ask (segPt i j (y i) k (x j - 1)) >>= fun vr =>
            if y i ≤ vr i then
              if x j - 1 ≤ vr j then
                upOrVop (pick3 i j (segPt i j (y i) k (x j - 1))
                  (segPt i j (y i) k (x j - 1)) y) (lub (segPt i j (y i) k (x j - 1)) y)
              else
                segSearch (segPt i j (y i) k) (c3Step i j k x y) (c3Final i j p k y)
                  b (y j) (x j - 1)
            else
              downOrVop (pick3 i j (segPt i j (y i) k (x j - 1)) x x)
                (glb x (segPt i j (y i) k (x j - 1)))

lemma c3Step_bounded (i j : Fin 3) (k : ℕ) (x y : Pt 3) (t : ℕ) (v : Pt 3)
    {alg : QueryAlg (Pt 3) (Pt 3) (InnerAnswer 3)} (h : c3Step i j k x y t v = .inl alg) :
    Bounded 1 alg := by
  unfold c3Step at h
  split at h
  · split at h
    · rw [← Sum.inl.inj h]
      exact upOrVop_bounded _ _
    · exact absurd h (by simp)
  · split at h
    · rw [← Sum.inl.inj h]
      exact downOrVop_bounded _ _
    · exact absurd h (by simp)

lemma c3Final_bounded (i j p : Fin 3) (k : ℕ) (y : Pt 3) (tlo thi : ℕ) (v : Pt 3) :
    Bounded 1 (c3Final i j p k y tlo thi v) := by
  unfold c3Final
  split
  · exact downOrVop_bounded _ _
  · exact upOrVop_bounded _ _

theorem config3Alg_bounded (i j p : Fin 3) (k : ℕ) (x y : Pt 3) (b : ℕ) :
    Bounded (b + 5) (config3Alg i j p k x y b) := by
  unfold config3Alg
  refine Bounded.mono (n := 1 + (b + 4)) ((Bounded.ask _).bind fun fx => ?_) (by omega)
  split
  · exact (upOrVop_bounded _ _).mono (by omega)
  · split
    · exact (downOrVop_bounded _ _).mono (by omega)
    · refine Bounded.mono (n := 1 + (b + 3)) ((Bounded.ask _).bind fun fy => ?_) (by omega)
      split
      · exact (downOrVop_bounded _ _).mono (by omega)
      · refine Bounded.mono (n := 1 + (b + 2)) ((Bounded.ask _).bind fun vr => ?_) (by omega)
        split
        · split
          · exact (upOrVop_bounded _ _).mono (by omega)
          · exact segSearch_bounded (fun t v alg hh => c3Step_bounded i j k x y t v hh)
              (fun tlo thi v => c3Final_bounded i j p k y tlo thi v) b (y j) (x j - 1)
        · exact (downOrVop_bounded _ _).mono (by omega)

/-! ### Correctness -/

section Correct

variable {F : Pt 3 → Pt 3} {lo hi : Pt 3} {k : ℕ} {i j p : Fin 3} {x y : Pt 3}

/-- **HL Lemma 3.13.** -/
theorem config3Alg_isSol (h : C3 F lo hi k i j p x y) {b : ℕ}
    (hb : x j - 1 - y j ≤ 2 ^ b) :
    IsLevelsetSol F lo hi k ((config3Alg i j p k x y b).run F) := by
  have hFxj := h.Fx_j
  have hFyj := h.Fy_j
  have hltj := h.lt_j
  unfold config3Alg
  rw [QueryAlg.run_bind, QueryAlg.run_ask]
  by_cases hA : F x j = x j
  · rw [if_pos hA]; exact lubXY_isSol h hA
  rw [if_neg hA]
  by_cases hB : F x j ≤ y j
  · rw [if_pos hB]; exact glbXY_isSol h hB
  rw [if_neg hB]
  push Not at hB
  -- now `y j < F x j < x j`, so the segment `[y j, x j - 1]` is non-degenerate
  have hrange : y j + 1 ≤ x j - 1 := by omega
  rw [QueryAlg.run_bind, QueryAlg.run_ask]
  by_cases hC : F y j = y j
  · rw [if_pos hC]; exact glbXY_isSol' h hC
  rw [if_neg hC]
  have hFy : y j < F y j := by omega
  rw [QueryAlg.run_bind, QueryAlg.run_ask]
  by_cases hD : y i ≤ F (segPt i j (y i) k (x j - 1)) i
  · rw [if_pos hD]
    by_cases hE : x j - 1 ≤ F (segPt i j (y i) k (x j - 1)) j
    · rw [if_pos hE]
      exact c3_lub_isSol h (by omega) (by omega) hD hE
    · rw [if_neg hE]
      push Not at hE
      -- run the search, with type (2) at the bottom and type (1) at the top
      refine segSearch_spec F (IsLevelsetSol F lo hi k)
        (fun t => F (segPt i j (y i) k t) i < y i ∧ t < F (segPt i j (y i) k t) j)
        (fun t => y i ≤ F (segPt i j (y i) k t) i ∧ F (segPt i j (y i) k t) j < t)
        (y j) (x j - 1) ?_ ?_ ?_ b (y j) (x j - 1) hb le_rfl le_rfl (by omega) ?_ ⟨hD, hE⟩
      · -- progress branches
        intro t alg h1 h2 hs
        unfold c3Step at hs
        by_cases hs1 : y i ≤ F (segPt i j (y i) k t) i
        · rw [if_pos hs1] at hs
          by_cases hs2 : t ≤ F (segPt i j (y i) k t) j
          · rw [if_pos hs2] at hs
            rw [← Sum.inl.inj hs]
            exact c3_lub_isSol h h1 (by omega) hs1 hs2
          · rw [if_neg hs2] at hs; exact absurd hs (by simp)
        · rw [if_neg hs1] at hs
          by_cases hs2 : F (segPt i j (y i) k t) j ≤ t
          · rw [if_pos hs2] at hs
            rw [← Sum.inl.inj hs]
            push Not at hs1
            exact c3_glb_isSol h h1 (by omega) hs1 hs2
          · rw [if_neg hs2] at hs; exact absurd hs (by simp)
      · -- direction branches
        intro t dir h1 h2 hs
        unfold c3Step at hs
        by_cases hs1 : y i ≤ F (segPt i j (y i) k t) i
        · rw [if_pos hs1] at hs
          by_cases hs2 : t ≤ F (segPt i j (y i) k t) j
          · rw [if_pos hs2] at hs; exact absurd hs (by simp)
          · rw [if_neg hs2] at hs
            push Not at hs2
            have : dir = false := (Sum.inr.inj hs).symm
            subst this
            exact ⟨by simp, fun _ => ⟨hs1, hs2⟩⟩
        · rw [if_neg hs1] at hs
          push Not at hs1
          by_cases hs2 : F (segPt i j (y i) k t) j ≤ t
          · rw [if_pos hs2] at hs; exact absurd hs (by simp)
          · rw [if_neg hs2] at hs
            push Not at hs2
            have : dir = true := (Sum.inr.inj hs).symm
            subst this
            exact ⟨fun _ => ⟨hs1, hs2⟩, by simp⟩
      · -- endgame
        intro tlo thi h1 h2 hlt hadj hplo hphi
        unfold c3Final
        by_cases hz : F (segPt i j (y i) k thi) p ≤ k - y i - thi
        · rw [if_pos hz]
          exact c3_end_glb h h1 (by omega) (by omega) hplo.1 hphi.2 hz
        · rw [if_neg hz]
          push Not at hz
          exact c3_end_lub h h1 (by omega) (by omega) hplo.2 hphi.1 hz
      · -- type (2) at the bottom of the segment, since `seg (y j) = y`
        change F (segPt i j (y i) k (y j)) i < y i ∧ y j < F (segPt i j (y i) k (y j)) j
        rw [c3seg_y h]
        exact ⟨by have := h.Fy_i; omega, hFy⟩
  · rw [if_neg hD]
    push Not at hD
    exact c3_glb_top_isSol h (by omega) hrange hD

end Correct

end Tfnp.Tarski
