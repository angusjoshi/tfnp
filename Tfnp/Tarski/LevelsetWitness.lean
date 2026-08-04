/-
Copyright (c) 2026 Angus Joshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Angus Joshi
-/
import Tfnp.Tarski.Config3

/-!
# Returning the witnesses of HL Observations 3.9, 3.10 and Lemma 3.6

`hasProgress_of_config1Up` and friends assert that a configuration *has* progress.
An algorithm must **return** it, so this file restates each of them through
`downOrVop` / `upOrVop`: the witness point is computed from the configuration, and
one query either confirms it or exposes a violation.

The only wrinkle is which point witnesses each coordinate.  For a first
configuration the two crossing coordinates are witnessed by `y` and `x`
respectively; for the third, either will do, so `argMin2` picks whichever attains
the meet there.  For a second configuration each coordinate is witnessed by the two
of the three points that go *down* there.

`cornerJoin` needs no such care: coordinate `j` of the join is witnessed by the
`j`-th corner itself.
-/

namespace Tfnp.Tarski

/-! ### Choosing the extremal point in a coordinate -/

/-- Whichever of `a`, `b` is smaller in coordinate `l`. -/
def argMin2 (a b : Pt 3) (l : Fin 3) : Pt 3 := if a l ≤ b l then a else b

/-- Whichever of `a`, `b` is larger in coordinate `l`. -/
def argMax2 (a b : Pt 3) (l : Fin 3) : Pt 3 := if a l ≤ b l then b else a

lemma argMin2_apply (a b : Pt 3) (l : Fin 3) : argMin2 a b l l = min (a l) (b l) := by
  unfold argMin2; split <;> omega

lemma argMax2_apply (a b : Pt 3) (l : Fin 3) : argMax2 a b l l = max (a l) (b l) := by
  unfold argMax2; split <;> omega

lemma argMin2_cases (a b : Pt 3) (l : Fin 3) : argMin2 a b l = a ∨ argMin2 a b l = b := by
  unfold argMin2; split
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma argMax2_cases (a b : Pt 3) (l : Fin 3) : argMax2 a b l = a ∨ argMax2 a b l = b := by
  unfold argMax2; split
  · exact Or.inr rfl
  · exact Or.inl rfl

/-! ### Observation 3.9, returning the witness -/

section Obs39

variable {F : Pt 3 → Pt 3} {lo hi : Pt 3} {k : ℕ} {i j p : Fin 3} {x y : Pt 3}

/-- **HL Observation 3.9**, upward form, as an algorithm: the meet is downward. -/
theorem alg_config1Up (hij : i ≠ j) (hip : i ≠ p) (hjp : j ≠ p)
    (hx : x ∈ Box lo hi) (hy : y ∈ Box lo hi) (hxk : lev x = k)
    (h : Config1Up F i j x y) :
    IsLevelsetSol F lo hi k
      ((downOrVop (pick3 i j y x (argMin2 x y p)) (glb x y)).run F) := by
  have hci := h.cross_i
  have hcj := h.cross_j
  have hG_i : glb x y i = y i := by rw [glb_apply]; omega
  have hG_j : glb x y j = x j := by rw [glb_apply]; omega
  have hG_p : glb x y p = min (x p) (y p) := glb_apply x y p
  refine downOrVop_isSol (fun l => ?_) (fun l => ?_) (glb_mem_Box hx hy) (fun l => ?_) ?_
  · rcases fin3_cover hij hip hjp l with rfl | rfl | rfl
    · rw [pick3_i]; exact glb_le_right x y
    · rw [pick3_j (Ne.symm hij)]; exact glb_le_left x y
    · rw [pick3_other (Ne.symm hip) (Ne.symm hjp)]
      rcases argMin2_cases x y l with hc | hc
      · rw [hc]; exact glb_le_left x y
      · rw [hc]; exact glb_le_right x y
  · rcases fin3_cover hij hip hjp l with rfl | rfl | rfl
    · rw [pick3_i, hG_i]; exact h.hy.2 l hij
    · rw [pick3_j (Ne.symm hij), hG_j]; exact h.hx.2 l (Ne.symm hij)
    · rw [pick3_other (Ne.symm hip) (Ne.symm hjp), hG_p]
      have h1 := h.hx.2 l (Ne.symm hip)
      have h2 := h.hy.2 l (Ne.symm hjp)
      rcases argMin2_cases x y l with hc | hc
      · rw [hc]; have := argMin2_apply x y l; rw [hc] at this; omega
      · rw [hc]; have := argMin2_apply x y l; rw [hc] at this; omega
  · rcases fin3_cover hij hip hjp l with rfl | rfl | rfl
    · rw [pick3_i]; exact hy
    · rw [pick3_j (Ne.symm hij)]; exact hx
    · rw [pick3_other (Ne.symm hip) (Ne.symm hjp)]
      rcases argMin2_cases x y l with hc | hc
      · rw [hc]; exact hx
      · rw [hc]; exact hy
  · rw [← hxk]; exact lev_mono (glb_le_left x y)

/-- **HL Observation 3.9**, downward form, as an algorithm: the join is upward. -/
theorem alg_config1Down (hij : i ≠ j) (hip : i ≠ p) (hjp : j ≠ p)
    (hx : x ∈ Box lo hi) (hy : y ∈ Box lo hi) (hxk : lev x = k)
    (h : Config1Down F i j x y) :
    IsLevelsetSol F lo hi k
      ((upOrVop (pick3 i j y x (argMax2 x y p)) (lub x y)).run F) := by
  have hci := h.cross_i
  have hcj := h.cross_j
  have hU_i : lub x y i = y i := by rw [lub_apply]; omega
  have hU_j : lub x y j = x j := by rw [lub_apply]; omega
  have hU_p : lub x y p = max (x p) (y p) := lub_apply x y p
  refine upOrVop_isSol (fun l => ?_) (fun l => ?_) (lub_mem_Box hx hy) (fun l => ?_) ?_
  · rcases fin3_cover hij hip hjp l with rfl | rfl | rfl
    · rw [pick3_i]; exact right_le_lub x y
    · rw [pick3_j (Ne.symm hij)]; exact left_le_lub x y
    · rw [pick3_other (Ne.symm hip) (Ne.symm hjp)]
      rcases argMax2_cases x y l with hc | hc
      · rw [hc]; exact left_le_lub x y
      · rw [hc]; exact right_le_lub x y
  · rcases fin3_cover hij hip hjp l with rfl | rfl | rfl
    · rw [pick3_i, hU_i]; exact h.hy.2 l hij
    · rw [pick3_j (Ne.symm hij), hU_j]; exact h.hx.2 l (Ne.symm hij)
    · rw [pick3_other (Ne.symm hip) (Ne.symm hjp), hU_p]
      have h1 := h.hx.2 l (Ne.symm hip)
      have h2 := h.hy.2 l (Ne.symm hjp)
      rcases argMax2_cases x y l with hc | hc
      · rw [hc]; have := argMax2_apply x y l; rw [hc] at this; omega
      · rw [hc]; have := argMax2_apply x y l; rw [hc] at this; omega
  · rcases fin3_cover hij hip hjp l with rfl | rfl | rfl
    · rw [pick3_i]; exact hy
    · rw [pick3_j (Ne.symm hij)]; exact hx
    · rw [pick3_other (Ne.symm hip) (Ne.symm hjp)]
      rcases argMax2_cases x y l with hc | hc
      · rw [hc]; exact hx
      · rw [hc]; exact hy
  · rw [← hxk]; exact lev_mono (left_le_lub x y)

end Obs39

/-! ### Observation 3.10, returning the witness -/

section Obs310

variable {F : Pt 3 → Pt 3} {lo hi : Pt 3} {k : ℕ} {i j p : Fin 3} {x y z : Pt 3}

/-- **HL Observation 3.10**, upward form, as an algorithm: the meet of the three is
downward.  Each coordinate is witnessed by whichever of the two points that go down
there attains the meet. -/
theorem alg_config2Up (hx : x ∈ Box lo hi) (hy : y ∈ Box lo hi) (hz : z ∈ Box lo hi)
    (hxk : lev x = k) (h : Config2Up F i j p x y z) :
    IsLevelsetSol F lo hi k
      ((downOrVop (pick3 i j (argMin2 y z i) (argMin2 x z j) (argMin2 x y p))
        (glb (glb x y) z)).run F) := by
  have hci := h.cross_i
  have hcj := h.cross_j
  have hcp := h.cross_p
  have hmx : glb (glb x y) z ≤ x := (glb_le_left _ _).trans (glb_le_left x y)
  have hmy : glb (glb x y) z ≤ y := (glb_le_left _ _).trans (glb_le_right x y)
  have hmz : glb (glb x y) z ≤ z := glb_le_right _ _
  have hgi : glb (glb x y) z i = min (y i) (z i) := by
    simp only [glb_apply]; omega
  have hgj : glb (glb x y) z j = min (x j) (z j) := by
    simp only [glb_apply]; omega
  have hgp : glb (glb x y) z p = min (x p) (y p) := by
    simp only [glb_apply]; omega
  refine downOrVop_isSol (fun l => ?_) (fun l => ?_)
    (glb_mem_Box (glb_mem_Box hx hy) hz) (fun l => ?_) ?_
  · rcases fin3_cover h.ij h.ip h.jp l with rfl | rfl | rfl
    · rw [pick3_i]
      rcases argMin2_cases y z l with hc | hc
      · rw [hc]; exact hmy
      · rw [hc]; exact hmz
    · rw [pick3_j (Ne.symm h.ij)]
      rcases argMin2_cases x z l with hc | hc
      · rw [hc]; exact hmx
      · rw [hc]; exact hmz
    · rw [pick3_other (Ne.symm h.ip) (Ne.symm h.jp)]
      rcases argMin2_cases x y l with hc | hc
      · rw [hc]; exact hmx
      · rw [hc]; exact hmy
  · rcases fin3_cover h.ij h.ip h.jp l with rfl | rfl | rfl
    · rw [pick3_i, hgi]
      have h1 := h.hy.2 l h.ij
      have h2 := h.hz.2 l h.ip
      have h3 := argMin2_apply y z l
      rcases argMin2_cases y z l with hc | hc <;> rw [hc] <;> rw [hc] at h3 <;> omega
    · rw [pick3_j (Ne.symm h.ij), hgj]
      have h1 := h.hx.2 l (Ne.symm h.ij)
      have h2 := h.hz.2 l h.jp
      have h3 := argMin2_apply x z l
      rcases argMin2_cases x z l with hc | hc <;> rw [hc] <;> rw [hc] at h3 <;> omega
    · rw [pick3_other (Ne.symm h.ip) (Ne.symm h.jp), hgp]
      have h1 := h.hx.2 l (Ne.symm h.ip)
      have h2 := h.hy.2 l (Ne.symm h.jp)
      have h3 := argMin2_apply x y l
      rcases argMin2_cases x y l with hc | hc <;> rw [hc] <;> rw [hc] at h3 <;> omega
  · rcases fin3_cover h.ij h.ip h.jp l with rfl | rfl | rfl
    · rw [pick3_i]
      rcases argMin2_cases y z l with hc | hc
      · rw [hc]; exact hy
      · rw [hc]; exact hz
    · rw [pick3_j (Ne.symm h.ij)]
      rcases argMin2_cases x z l with hc | hc
      · rw [hc]; exact hx
      · rw [hc]; exact hz
    · rw [pick3_other (Ne.symm h.ip) (Ne.symm h.jp)]
      rcases argMin2_cases x y l with hc | hc
      · rw [hc]; exact hx
      · rw [hc]; exact hy
  · rw [← hxk]; exact lev_mono hmx

/-- **HL Observation 3.10**, downward form, as an algorithm. -/
theorem alg_config2Down (hx : x ∈ Box lo hi) (hy : y ∈ Box lo hi) (hz : z ∈ Box lo hi)
    (hxk : lev x = k) (h : Config2Down F i j p x y z) :
    IsLevelsetSol F lo hi k
      ((upOrVop (pick3 i j (argMax2 y z i) (argMax2 x z j) (argMax2 x y p))
        (lub (lub x y) z)).run F) := by
  have hci := h.cross_i
  have hcj := h.cross_j
  have hcp := h.cross_p
  have hmx : x ≤ lub (lub x y) z := (left_le_lub x y).trans (left_le_lub _ _)
  have hmy : y ≤ lub (lub x y) z := (right_le_lub x y).trans (left_le_lub _ _)
  have hmz : z ≤ lub (lub x y) z := right_le_lub _ _
  have hgi : lub (lub x y) z i = max (y i) (z i) := by simp only [lub_apply]; omega
  have hgj : lub (lub x y) z j = max (x j) (z j) := by simp only [lub_apply]; omega
  have hgp : lub (lub x y) z p = max (x p) (y p) := by simp only [lub_apply]; omega
  refine upOrVop_isSol (fun l => ?_) (fun l => ?_)
    (lub_mem_Box (lub_mem_Box hx hy) hz) (fun l => ?_) ?_
  · rcases fin3_cover h.ij h.ip h.jp l with rfl | rfl | rfl
    · rw [pick3_i]
      rcases argMax2_cases y z l with hc | hc
      · rw [hc]; exact hmy
      · rw [hc]; exact hmz
    · rw [pick3_j (Ne.symm h.ij)]
      rcases argMax2_cases x z l with hc | hc
      · rw [hc]; exact hmx
      · rw [hc]; exact hmz
    · rw [pick3_other (Ne.symm h.ip) (Ne.symm h.jp)]
      rcases argMax2_cases x y l with hc | hc
      · rw [hc]; exact hmx
      · rw [hc]; exact hmy
  · rcases fin3_cover h.ij h.ip h.jp l with rfl | rfl | rfl
    · rw [pick3_i, hgi]
      have h1 := h.hy.2 l h.ij
      have h2 := h.hz.2 l h.ip
      have h3 := argMax2_apply y z l
      rcases argMax2_cases y z l with hc | hc <;> rw [hc] <;> rw [hc] at h3 <;> omega
    · rw [pick3_j (Ne.symm h.ij), hgj]
      have h1 := h.hx.2 l (Ne.symm h.ij)
      have h2 := h.hz.2 l h.jp
      have h3 := argMax2_apply x z l
      rcases argMax2_cases x z l with hc | hc <;> rw [hc] <;> rw [hc] at h3 <;> omega
    · rw [pick3_other (Ne.symm h.ip) (Ne.symm h.jp), hgp]
      have h1 := h.hx.2 l (Ne.symm h.ip)
      have h2 := h.hy.2 l (Ne.symm h.jp)
      have h3 := argMax2_apply x y l
      rcases argMax2_cases x y l with hc | hc <;> rw [hc] <;> rw [hc] at h3 <;> omega
  · rcases fin3_cover h.ij h.ip h.jp l with rfl | rfl | rfl
    · rw [pick3_i]
      rcases argMax2_cases y z l with hc | hc
      · rw [hc]; exact hy
      · rw [hc]; exact hz
    · rw [pick3_j (Ne.symm h.ij)]
      rcases argMax2_cases x z l with hc | hc
      · rw [hc]; exact hx
      · rw [hc]; exact hz
    · rw [pick3_other (Ne.symm h.ip) (Ne.symm h.jp)]
      rcases argMax2_cases x y l with hc | hc
      · rw [hc]; exact hx
      · rw [hc]; exact hy
  · rw [← hxk]; exact lev_mono hmx

end Obs310

/-! ### Lemma 3.6's endgame, returning the witness -/

section Corner

variable {F : Pt 3 → Pt 3} {lo hi : Pt 3} {ℓ r : Pt 3} {k : ℕ}

/-- **HL Lemma 3.6**'s endgame as an algorithm: coordinate `l` of the join is
witnessed by the `l`-th corner itself. -/
theorem alg_corner_up (hlo : lo ≤ ℓ) (hr : r ≤ hi)
    (hbig : ∀ i, 2 ≤ sDiam ℓ r k i) (hlr : ℓ ≤ r) (hlk : lev ℓ ≤ k) (hkr : k ≤ lev r)
    (hk : k = sLo ℓ r k 0 + sLo ℓ r k 1 + sLo ℓ r k 2 + 2)
    (hcorner : ∀ i, IUp F (cornerPt ℓ r k i) i) :
    IsLevelsetSol F lo hi k
      ((upOrVop (fun l => cornerPt ℓ r k l) (cornerJoin ℓ r k)).run F) := by
  have hJmem : cornerJoin ℓ r k ∈ Box lo hi := by
    refine mem_Box.mpr ⟨coord_le fun j => ?_, coord_le fun j => ?_⟩
    · have h1 : lo j ≤ ℓ j := le_coord hlo j
      have h2 : ℓ j ≤ sLo ℓ r k j := le_max_left _ _
      simp only [cornerJoin]; omega
    · have h1 : r j ≤ hi j := le_coord hr j
      have h2 : sHi ℓ r k j ≤ r j := min_le_left _ _
      have h3 := hbig j
      have h4 : sDiam ℓ r k j = sHi ℓ r k j - sLo ℓ r k j := rfl
      have h5 : sLo ℓ r k j ≤ sHi ℓ r k j := sLo_le_sHi hlr hlk hkr j
      simp only [cornerJoin]; omega
  have hcmem : ∀ l, cornerPt ℓ r k l ∈ Box lo hi := by
    intro l
    refine mem_Box.mpr ⟨coord_le fun j => ?_,
      (cornerPt_le_cornerJoin l).trans (mem_Box.mp hJmem).2⟩
    have h1 : lo j ≤ ℓ j := le_coord hlo j
    have h2 : ℓ j ≤ sLo ℓ r k j := le_max_left _ _
    have h3 : cornerPt ℓ r k l j = sLo ℓ r k j ∨ cornerPt ℓ r k l j = sLo ℓ r k j + 1 := by
      by_cases hj : j = l
      · subst hj; exact Or.inl (by simp [cornerPt])
      · exact Or.inr (by simp [cornerPt, hj])
    rcases h3 with h3 | h3 <;> omega
  refine upOrVop_isSol (fun l => cornerPt_le_cornerJoin l) (fun l => ?_) hJmem hcmem ?_
  · have h1 := (hcorner l).1
    have h2 : cornerPt ℓ r k l l = sLo ℓ r k l := by simp [cornerPt]
    have h3 : cornerJoin ℓ r k l = sLo ℓ r k l + 1 := rfl
    omega
  · have hlev : lev (cornerJoin ℓ r k) = sLo ℓ r k 0 + sLo ℓ r k 1 + sLo ℓ r k 2 + 3 := by
      rw [lev_eq_three]; simp only [cornerJoin]; omega
    omega

/-- The dual corners: at the *upper* extent in coordinate `i`, one below it in the
other two. -/
def cornerPtD (ℓ r : Pt 3) (k : ℕ) (i : Fin 3) : Pt 3 :=
  fun j => if j = i then sHi ℓ r k i else sHi ℓ r k j - 1

/-- The meet of the dual corners. -/
def cornerMeet (ℓ r : Pt 3) (k : ℕ) : Pt 3 := fun j => sHi ℓ r k j - 1

lemma cornerMeet_le_cornerPtD (i : Fin 3) : cornerMeet ℓ r k ≤ cornerPtD ℓ r k i := by
  refine coord_le fun j => ?_
  by_cases hj : j = i
  · subst hj; simp [cornerPtD, cornerMeet]
  · simp [cornerPtD, cornerMeet, hj]

/-- The dual corner points lie on the levelset exactly when `k + 2 = Σⱼ sHiⱼ`. -/
lemma lev_cornerPtD (hbig : ∀ i, 2 ≤ sDiam ℓ r k i) (_hlr : ℓ ≤ r)
    (_hlk : lev ℓ ≤ k) (_hkr : k ≤ lev r) (i : Fin 3) :
    lev (cornerPtD ℓ r k i) + 2 = sHi ℓ r k 0 + sHi ℓ r k 1 + sHi ℓ r k 2 := by
  have h0 := hbig 0
  have h1 := hbig 1
  have h2 := hbig 2
  have g0 : sDiam ℓ r k 0 = sHi ℓ r k 0 - sLo ℓ r k 0 := rfl
  have g1 : sDiam ℓ r k 1 = sHi ℓ r k 1 - sLo ℓ r k 1 := rfl
  have g2 : sDiam ℓ r k 2 = sHi ℓ r k 2 - sLo ℓ r k 2 := rfl
  rw [lev_eq_three]
  fin_cases i <;> simp [cornerPtD] <;> omega

/-- **HL Lemma 3.6**'s endgame, dual form. -/
theorem alg_corner_down (hlo : lo ≤ ℓ) (hr : r ≤ hi)
    (hbig : ∀ i, 2 ≤ sDiam ℓ r k i) (_hlr : ℓ ≤ r) (_hlk : lev ℓ ≤ k) (_hkr : k ≤ lev r)
    (hk : k + 2 = sHi ℓ r k 0 + sHi ℓ r k 1 + sHi ℓ r k 2)
    (hcorner : ∀ i, IDown F (cornerPtD ℓ r k i) i) :
    IsLevelsetSol F lo hi k
      ((downOrVop (fun l => cornerPtD ℓ r k l) (cornerMeet ℓ r k)).run F) := by
  have hMmem : cornerMeet ℓ r k ∈ Box lo hi := by
    refine mem_Box.mpr ⟨coord_le fun j => ?_, coord_le fun j => ?_⟩
    · have h1 : lo j ≤ ℓ j := le_coord hlo j
      have h2 : ℓ j ≤ sLo ℓ r k j := le_max_left _ _
      have h3 := hbig j
      have h4 : sDiam ℓ r k j = sHi ℓ r k j - sLo ℓ r k j := rfl
      simp only [cornerMeet]; omega
    · have h1 : r j ≤ hi j := le_coord hr j
      have h2 : sHi ℓ r k j ≤ r j := min_le_left _ _
      simp only [cornerMeet]; omega
  have hcmem : ∀ l, cornerPtD ℓ r k l ∈ Box lo hi := by
    intro l
    refine mem_Box.mpr ⟨(mem_Box.mp hMmem).1.trans (cornerMeet_le_cornerPtD l),
      coord_le fun j => ?_⟩
    have h1 : r j ≤ hi j := le_coord hr j
    have h2 : sHi ℓ r k j ≤ r j := min_le_left _ _
    have h3 : cornerPtD ℓ r k l j = sHi ℓ r k j ∨ cornerPtD ℓ r k l j = sHi ℓ r k j - 1 := by
      by_cases hj : j = l
      · subst hj; exact Or.inl (by simp [cornerPtD])
      · exact Or.inr (by simp [cornerPtD, hj])
    rcases h3 with h3 | h3 <;> omega
  refine downOrVop_isSol (fun l => cornerMeet_le_cornerPtD l) (fun l => ?_) hMmem hcmem ?_
  · have h1 := (hcorner l).1
    have h2 : cornerPtD ℓ r k l l = sHi ℓ r k l := by simp [cornerPtD]
    have h3 : cornerMeet ℓ r k l = sHi ℓ r k l - 1 := rfl
    omega
  · have hlev : lev (cornerMeet ℓ r k) + 3 = sHi ℓ r k 0 + sHi ℓ r k 1 + sHi ℓ r k 2 := by
      have h0 := hbig 0
      have h1 := hbig 1
      have h2 := hbig 2
      have g0 : sDiam ℓ r k 0 = sHi ℓ r k 0 - sLo ℓ r k 0 := rfl
      have g1 : sDiam ℓ r k 1 = sHi ℓ r k 1 - sLo ℓ r k 1 := rfl
      have g2 : sDiam ℓ r k 2 = sHi ℓ r k 2 - sLo ℓ r k 2 := rfl
      rw [lev_eq_three]; simp only [cornerMeet]; omega
    omega

end Corner

end Tfnp.Tarski
