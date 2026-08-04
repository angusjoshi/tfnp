/-
Copyright (c) 2026 Angus Joshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Angus Joshi
-/
import Tfnp.Tarski.LevelsetInit

/-!
# The Haslebacher–Lill shrinking loop

Everything is in place; this file runs it.  The loop threads the six bounding
points of HL Definition 3.4, cutting the search space while some diameter is large
and resolving into a configuration once one diameter reaches one.

* `configResolve` — HL Lemma 3.12's dispatch, made algorithmic.  It tests five
  decidable patterns among the six points (a third configuration, then the four
  shapes of first/second configuration) and returns the corresponding witness.
  Exactly one must apply, which is the content of `sDiam_cases` and
  `fin3_config_exists`.
* `lsLoop` — the shrinking loop.  While some diameter is at least six it cuts at
  `exists_deep_query`; below that it falls through to the constant-size endgame of
  HL Lemma 3.6.  Either way `sMeasure` shrinks by `8/9`, so
  `Tfnp.iterate_shrinking` bounds the number of iterations.
* `lsInner` — the whole levelset subprocedure: six invocations of HL Lemma 3.14 to
  initialise, then the loop.
-/

namespace Tfnp.Tarski

open QueryAlg (Bounded)

/-! ### Choosing coordinates and pairs -/

/-- The coordinate of `Fin 3` other than `i` and `j`. -/
def third (i j : Fin 3) : Fin 3 := ⟨min 2 (3 - i.val - j.val), by omega⟩

lemma third_ne : ∀ i j : Fin 3, i ≠ j → i ≠ third i j ∧ j ≠ third i j := by decide

lemma third_eq : ∀ i j p : Fin 3, i ≠ j → i ≠ p → j ≠ p → p = third i j := by decide

lemma fin3_eq : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide

open Classical in
/-- Choose an element satisfying a predicate, if one exists. -/
noncomputable def pick {α : Type} [Inhabited α] (P : α → Prop) : α :=
  if h : ∃ a, P a then h.choose else default

lemma pick_spec {α : Type} [Inhabited α] {P : α → Prop} (h : ∃ a, P a) : P (pick P) := by
  rw [pick, dif_pos h]; exact h.choose_spec

/-- The largest of three numbers is attained. -/
lemma exists_max3 (f : Fin 3 → ℕ) : ∃ i, ∀ j, f j ≤ f i := by
  rcases le_total (f 0) (f 1) with h01 | h01
  · rcases le_total (f 1) (f 2) with h12 | h12
    · exact ⟨2, fun j => by rcases fin3_eq j with rfl | rfl | rfl <;> omega⟩
    · exact ⟨1, fun j => by rcases fin3_eq j with rfl | rfl | rfl <;> omega⟩
  · rcases le_total (f 0) (f 2) with h02 | h02
    · exact ⟨2, fun j => by rcases fin3_eq j with rfl | rfl | rfl <;> omega⟩
    · exact ⟨0, fun j => by rcases fin3_eq j with rfl | rfl | rfl <;> omega⟩

/-! ### The loop invariant -/

/-- The data and invariant carried by the shrinking loop: HL Definition 3.4 together
with the two level bounds that make the search space non-empty. -/
structure LInv (F : Pt 3 → Pt 3) (lo hi : Pt 3) (k : ℕ) (u dn : Fin 3 → Pt 3) : Prop where
  /-- The upward points lie in the box. -/
  u_mem : ∀ i, u i ∈ Box lo hi
  /-- The downward points lie in the box. -/
  dn_mem : ∀ i, dn i ∈ Box lo hi
  /-- The upward points lie on the levelset. -/
  u_lev : ∀ i, lev (u i) = k
  /-- The downward points lie on the levelset. -/
  dn_lev : ∀ i, lev (dn i) = k
  /-- `u i` is `i`-upward. -/
  u_up : ∀ i, IUp F (u i) i
  /-- `dn i` is `i`-downward. -/
  dn_down : ∀ i, IDown F (dn i) i
  /-- HL Definition 3.4's ordering condition. -/
  ord : ∀ i, u i i ≤ dn i i
  /-- The lower corner is below the level. -/
  lev_lo : lev (fun i => u i i) ≤ k
  /-- The upper corner is above the level. -/
  lev_hi : k ≤ lev (fun i => dn i i)

/-- The lower corner. -/
abbrev lc (u : Fin 3 → Pt 3) : Pt 3 := fun i => u i i

/-- The upper corner. -/
abbrev uc (dn : Fin 3 → Pt 3) : Pt 3 := fun i => dn i i


lemma lc_update (u : Fin 3 → Pt 3) (l : Fin 3) (q : Pt 3) :
    lc (Function.update u l q) = Function.update (lc u) l (q l) := by
  funext m
  by_cases hm : m = l
  · subst hm; simp [lc]
  · simp [lc, Function.update_of_ne hm]

lemma uc_update (dn : Fin 3 → Pt 3) (l : Fin 3) (q : Pt 3) :
    uc (Function.update dn l q) = Function.update (uc dn) l (q l) := by
  funext m
  by_cases hm : m = l
  · subst hm; simp [uc]
  · simp [uc, Function.update_of_ne hm]

namespace LInv

variable {F : Pt 3 → Pt 3} {lo hi : Pt 3} {k : ℕ} {u dn : Fin 3 → Pt 3}

lemma lc_le_uc (h : LInv F lo hi k u dn) : lc u ≤ uc dn := coord_le fun i => h.ord i

lemma lo_le_lc (h : LInv F lo hi k u dn) : lo ≤ lc u :=
  coord_le fun i => le_coord (mem_Box.mp (h.u_mem i)).1 i

lemma uc_le_hi (h : LInv F lo hi k u dn) : uc dn ≤ hi :=
  coord_le fun i => le_coord (mem_Box.mp (h.dn_mem i)).2 i

/-- Two distinct points of the same levelset, comparable in one coordinate, must
differ in another.  This is what supplies the coordinate `j` a third configuration
needs. -/
lemma exists_lt_coord (h : LInv F lo hi k u dn) (i : Fin 3) :
    ∃ j, j ≠ i ∧ dn i j < u i j := by
  by_contra hc
  push Not at hc
  have hle : u i ≤ dn i := by
    refine coord_le fun l => ?_
    by_cases hl : l = i
    · subst hl; exact h.ord l
    · exact hc l hl
  have hne : u i ≠ dn i := by
    intro he
    have h1 := (h.u_up i).1
    have h2 := (h.dn_down i).1
    rw [he] at h1
    omega
  obtain ⟨l, hl⟩ := exists_lt_of_not_le (fun hx => hne (le_antisymm hle hx))
  have h1 := h.u_lev i
  have h2 := h.dn_lev i
  have h4 : lev (u i) < lev (dn i) := by
    unfold lev
    exact Finset.sum_lt_sum (fun m _ => le_coord hle m) ⟨l, Finset.mem_univ l, hl⟩
  omega

/-- A point of the search space that is `l`-upward may replace `u⁽ˡ⁾`. -/
lemma cut_up (h : LInv F lo hi k u dn) {q : Pt 3} {l : Fin 3}
    (hq : q ∈ SSet (lc u) (uc dn) k) (hup : IUp F q l) :
    LInv F lo hi k (Function.update u l q) dn := by
  obtain ⟨hqlev, hlq, hqr⟩ := hq
  have hqmem : q ∈ Box lo hi :=
    mem_Box.mpr ⟨h.lo_le_lc.trans hlq, hqr.trans h.uc_le_hi⟩
  have hnew : lc (Function.update u l q) ≤ q := by
    rw [lc_update]
    refine coord_le fun m => ?_
    by_cases hm : m = l
    · subst hm; simp
    · rw [Function.update_of_ne hm]; exact le_coord hlq m
  refine ⟨fun i => ?_, h.dn_mem, fun i => ?_, h.dn_lev, fun i => ?_, h.dn_down,
    fun i => ?_, ?_, h.lev_hi⟩
  · by_cases hi : i = l
    · subst hi; rwa [Function.update_self]
    · rw [Function.update_of_ne hi]; exact h.u_mem i
  · by_cases hi : i = l
    · subst hi; rwa [Function.update_self]
    · rw [Function.update_of_ne hi]; exact h.u_lev i
  · by_cases hi : i = l
    · subst hi; rwa [Function.update_self]
    · rw [Function.update_of_ne hi]; exact h.u_up i
  · by_cases hi : i = l
    · subst hi; rw [Function.update_self]; exact le_coord hqr _
    · rw [Function.update_of_ne hi]; exact h.ord i
  · exact le_trans (lev_mono hnew) (le_of_eq hqlev)

/-- A point of the search space that is `l`-downward may replace `d⁽ˡ⁾`. -/
lemma cut_down (h : LInv F lo hi k u dn) {q : Pt 3} {l : Fin 3}
    (hq : q ∈ SSet (lc u) (uc dn) k) (hdown : IDown F q l) :
    LInv F lo hi k u (Function.update dn l q) := by
  obtain ⟨hqlev, hlq, hqr⟩ := hq
  have hqmem : q ∈ Box lo hi :=
    mem_Box.mpr ⟨h.lo_le_lc.trans hlq, hqr.trans h.uc_le_hi⟩
  have hnew : q ≤ uc (Function.update dn l q) := by
    rw [uc_update]
    refine coord_le fun m => ?_
    by_cases hm : m = l
    · subst hm; simp
    · rw [Function.update_of_ne hm]; exact le_coord hqr m
  refine ⟨h.u_mem, fun i => ?_, h.u_lev, fun i => ?_, h.u_up, fun i => ?_,
    fun i => ?_, h.lev_lo, ?_⟩
  · by_cases hi : i = l
    · subst hi; rwa [Function.update_self]
    · rw [Function.update_of_ne hi]; exact h.dn_mem i
  · by_cases hi : i = l
    · subst hi; rwa [Function.update_self]
    · rw [Function.update_of_ne hi]; exact h.dn_lev i
  · by_cases hi : i = l
    · subst hi; rwa [Function.update_self]
    · rw [Function.update_of_ne hi]; exact h.dn_down i
  · by_cases hi : i = l
    · subst hi; rw [Function.update_self]; exact le_coord hlq _
    · rw [Function.update_of_ne hi]; exact h.ord i
  · exact le_trans (le_of_eq hqlev.symm) (lev_mono hnew)

end LInv

/-! ### One query, then either an answer or a cut

`iUpAt q v i` is `IUp F q i` with the observed value `v = F q` substituted, so that
the algorithm — which has no access to `F` — can test it. -/

/-- `IUp F q i`, phrased in the observed value `v = F q`. -/
def iUpAt (q v : Pt 3) (i : Fin 3) : Prop := q i < v i ∧ ∀ j ≠ i, v j ≤ q j

/-- `IDown F q i`, phrased in the observed value `v = F q`. -/
def iDownAt (q v : Pt 3) (i : Fin 3) : Prop := v i < q i ∧ ∀ j ≠ i, q j ≤ v j

lemma iUpAt_eq (F : Pt 3 → Pt 3) (q : Pt 3) (i : Fin 3) : iUpAt q (F q) i = IUp F q i := rfl

lemma iDownAt_eq (F : Pt 3 → Pt 3) (q : Pt 3) (i : Fin 3) :
    iDownAt q (F q) i = IDown F q i := rfl

open Classical in
/-- Having queried `q` and seen `v`, either `q` itself is the answer, or it is
`l`-upward (resp. `l`-downward) for some `l` and the loop continues with `u⁽ˡ⁾`
(resp. `d⁽ˡ⁾`) replaced by `q`.  By `up_or_down_or_iUpDown` these cases are
exhaustive — that is the special feature of three dimensions. -/
noncomputable def dispatch
    (rec : (Fin 3 → Pt 3) → (Fin 3 → Pt 3) → QueryAlg (Pt 3) (Pt 3) (InnerAnswer 3))
    (u dn : Fin 3 → Pt 3) (q v : Pt 3) : QueryAlg (Pt 3) (Pt 3) (InnerAnswer 3) :=
  if q ≤ v then QueryAlg.pure (.up q)
  else if v ≤ q then QueryAlg.pure (.down q)
  else if ∃ i, iUpAt q v i then rec (Function.update u (pick (iUpAt q v)) q) dn
  else rec u (Function.update dn (pick (iDownAt q v)) q)

lemma dispatch_bounded {c : ℕ}
    {rec : (Fin 3 → Pt 3) → (Fin 3 → Pt 3) → QueryAlg (Pt 3) (Pt 3) (InnerAnswer 3)}
    (hrec : ∀ a b, Bounded c (rec a b)) (u dn : Fin 3 → Pt 3) (q v : Pt 3) :
    Bounded c (dispatch rec u dn q v) := by
  unfold dispatch
  split_ifs <;> first | exact Bounded.pure' _ _ | exact hrec _ _

section Dispatch

variable {F : Pt 3 → Pt 3} {lo hi : Pt 3} {k : ℕ} {u dn : Fin 3 → Pt 3} {q : Pt 3}
  {rec : (Fin 3 → Pt 3) → (Fin 3 → Pt 3) → QueryAlg (Pt 3) (Pt 3) (InnerAnswer 3)}

theorem dispatch_isSol (h : LInv F lo hi k u dn) (hq : q ∈ SSet (lc u) (uc dn) k)
    (hUp : ∀ l, IUp F q l →
      IsLevelsetSol F lo hi k ((rec (Function.update u l q) dn).run F))
    (hDown : ∀ l, IDown F q l →
      IsLevelsetSol F lo hi k ((rec u (Function.update dn l q)).run F)) :
    IsLevelsetSol F lo hi k ((dispatch rec u dn q (F q)).run F) := by
  have hqmem : q ∈ Box lo hi :=
    mem_Box.mpr ⟨h.lo_le_lc.trans hq.2.1, hq.2.2.trans h.uc_le_hi⟩
  unfold dispatch
  by_cases h1 : q ≤ F q
  · rw [if_pos h1]
    exact ⟨hqmem, le_of_eq hq.1.symm, mem_Up.mpr h1⟩
  rw [if_neg h1]
  by_cases h2 : F q ≤ q
  · rw [if_pos h2]
    exact ⟨hqmem, le_of_eq hq.1, mem_Down.mpr h2⟩
  rw [if_neg h2]
  by_cases h3 : ∃ i, iUpAt q (F q) i
  · rw [if_pos h3]
    exact hUp _ (pick_spec h3)
  rw [if_neg h3]
  have h4 : ∃ i, iDownAt q (F q) i := by
    rcases up_or_down_or_iUpDown F q with hc | hc | hc | hc
    · exact absurd hc h1
    · exact absurd hc h2
    · exact absurd hc h3
    · exact hc
  exact hDown _ (pick_spec h4)

end Dispatch

/-! ### Scanning the three corners of HL Lemma 3.6 -/

open Classical in
/-- Query the three corner points in turn.  If all three pass the test `ok`, the
join (or meet) is the answer; the first that fails is handed to `dispatch`. -/
noncomputable def cornerRun
    (rec : (Fin 3 → Pt 3) → (Fin 3 → Pt 3) → QueryAlg (Pt 3) (Pt 3) (InnerAnswer 3))
    (u dn : Fin 3 → Pt 3) (c : Fin 3 → Pt 3) (ok : Fin 3 → Pt 3 → Prop)
    (fin : QueryAlg (Pt 3) (Pt 3) (InnerAnswer 3)) : QueryAlg (Pt 3) (Pt 3) (InnerAnswer 3) :=
  QueryAlg.ask (c 0) >>= fun v0 =>
    if ok 0 v0 then
      QueryAlg.ask (c 1) >>= fun v1 =>
        if ok 1 v1 then
          QueryAlg.ask (c 2) >>= fun v2 =>
            if ok 2 v2 then fin else dispatch rec u dn (c 2) v2
        else dispatch rec u dn (c 1) v1
    else dispatch rec u dn (c 0) v0

lemma cornerRun_bounded {c : ℕ}
    {rec : (Fin 3 → Pt 3) → (Fin 3 → Pt 3) → QueryAlg (Pt 3) (Pt 3) (InnerAnswer 3)}
    (hrec : ∀ a b, Bounded c (rec a b)) (u dn : Fin 3 → Pt 3) (cpt : Fin 3 → Pt 3)
    (ok : Fin 3 → Pt 3 → Prop) {fin : QueryAlg (Pt 3) (Pt 3) (InnerAnswer 3)}
    (hfin : Bounded c fin) :
    Bounded (3 + c) (cornerRun rec u dn cpt ok fin) := by
  unfold cornerRun
  refine Bounded.mono (n := 1 + (1 + (1 + c))) ((Bounded.ask _).bind fun v0 => ?_) (by omega)
  split
  · refine Bounded.mono (n := 1 + (1 + c)) ((Bounded.ask _).bind fun v1 => ?_) (by omega)
    split
    · refine Bounded.mono (n := 1 + c) ((Bounded.ask _).bind fun v2 => ?_) (by omega)
      split
      · exact hfin
      · exact dispatch_bounded hrec _ _ _ _
    · exact (dispatch_bounded hrec _ _ _ _).mono (by omega)
  · exact (dispatch_bounded hrec _ _ _ _).mono (by omega)

theorem cornerRun_isSol {F : Pt 3 → Pt 3} {lo hi : Pt 3} {k : ℕ} {u dn : Fin 3 → Pt 3}
    {rec : (Fin 3 → Pt 3) → (Fin 3 → Pt 3) → QueryAlg (Pt 3) (Pt 3) (InnerAnswer 3)}
    {cpt : Fin 3 → Pt 3} {ok : Fin 3 → Pt 3 → Prop}
    {fin : QueryAlg (Pt 3) (Pt 3) (InnerAnswer 3)}
    (hall : (∀ i, ok i (F (cpt i))) → IsLevelsetSol F lo hi k (fin.run F))
    (hfail : ∀ i, ¬ ok i (F (cpt i)) →
      IsLevelsetSol F lo hi k ((dispatch rec u dn (cpt i) (F (cpt i))).run F)) :
    IsLevelsetSol F lo hi k ((cornerRun rec u dn cpt ok fin).run F) := by
  unfold cornerRun
  rw [QueryAlg.run_bind, QueryAlg.run_ask]
  by_cases h0 : ok 0 (F (cpt 0))
  · rw [if_pos h0, QueryAlg.run_bind, QueryAlg.run_ask]
    by_cases h1 : ok 1 (F (cpt 1))
    · rw [if_pos h1, QueryAlg.run_bind, QueryAlg.run_ask]
      by_cases h2 : ok 2 (F (cpt 2))
      · rw [if_pos h2]
        exact hall fun i => by rcases fin3_eq i with rfl | rfl | rfl <;> assumption
      · rw [if_neg h2]; exact hfail 2 h2
    · rw [if_neg h1]; exact hfail 1 h1
  · rw [if_neg h0]; exact hfail 0 h0

/-! ### The measure, and the fuel -/

/-- HL Lemma 3.5's query point: at least `⌈diamᵢ/6⌉` from both ends in every
coordinate. -/
def DeepP (l r : Pt 3) (k : ℕ) (q : Pt 3) : Prop :=
  q ∈ SSet l r k ∧
    ∀ i, sLo l r k i + slack l r k i ≤ q i ∧ q i + slack l r k i ≤ sHi l r k i

private lemma prod3_mul {A' A B' B C' C : ℕ} (h1 : 9 * (A' + 1) ≤ 8 * (A + 1))
    (h2 : B' ≤ B) (h3 : C' ≤ C) :
    9 * ((A' + 1) * (B' + 1) * (C' + 1)) ≤ 8 * ((A + 1) * (B + 1) * (C + 1)) := by
  calc 9 * ((A' + 1) * (B' + 1) * (C' + 1))
      = (9 * (A' + 1)) * ((B' + 1) * (C' + 1)) := by ring
    _ ≤ (8 * (A + 1)) * ((B + 1) * (C + 1)) :=
        Nat.mul_le_mul h1 (Nat.mul_le_mul (by omega) (by omega))
    _ = 8 * ((A + 1) * (B + 1) * (C + 1)) := by ring

/-- `sMeasure_shrink`, with *both* endpoints allowed to move: only the three
diameters matter. -/
theorem sMeasure_shrink' {l r l' r' : Pt 3} {k : ℕ} {i : Fin 3}
    (hcut : 6 * sDiam l' r' k i ≤ 5 * sDiam l r k i)
    (hother : ∀ j, j ≠ i → sDiam l' r' k j ≤ sDiam l r k j)
    (hbig : 2 ≤ sDiam l r k i) :
    9 * sMeasure l' r' k ≤ 8 * sMeasure l r k := by
  have key : 9 * (sDiam l' r' k i + 1) ≤ 8 * (sDiam l r k i + 1) := by omega
  fin_cases i
  · exact prod3_mul key (hother 1 (by decide)) (hother 2 (by decide))
  · have h := prod3_mul key (hother 0 (by decide)) (hother 2 (by decide))
    simp only [sMeasure]
    calc 9 * ((sDiam l' r' k 0 + 1) * (sDiam l' r' k 1 + 1) * (sDiam l' r' k 2 + 1))
        = 9 * ((sDiam l' r' k 1 + 1) * (sDiam l' r' k 0 + 1) * (sDiam l' r' k 2 + 1)) := by
          ring
      _ ≤ 8 * ((sDiam l r k 1 + 1) * (sDiam l r k 0 + 1) * (sDiam l r k 2 + 1)) := h
      _ = 8 * ((sDiam l r k 0 + 1) * (sDiam l r k 1 + 1) * (sDiam l r k 2 + 1)) := by ring
  · have h := prod3_mul key (hother 0 (by decide)) (hother 1 (by decide))
    simp only [sMeasure]
    calc 9 * ((sDiam l' r' k 0 + 1) * (sDiam l' r' k 1 + 1) * (sDiam l' r' k 2 + 1))
        = 9 * ((sDiam l' r' k 2 + 1) * (sDiam l' r' k 0 + 1) * (sDiam l' r' k 1 + 1)) := by
          ring
      _ ≤ 8 * ((sDiam l r k 2 + 1) * (sDiam l r k 0 + 1) * (sDiam l r k 1 + 1)) := h
      _ = 8 * ((sDiam l r k 0 + 1) * (sDiam l r k 1 + 1) * (sDiam l r k 2 + 1)) := by ring

section Shrink

variable {l r : Pt 3} {k : ℕ} {q : Pt 3} {j : Fin 3}

/-- Cutting upward at a point deep in coordinate `j` shrinks the measure. -/
theorem measure_shrink_up (hlr : l ≤ r) (hlk : lev l ≤ k) (hkr : k ≤ lev r)
    (hbig : ∀ i, 2 ≤ sDiam l r k i) (hq : q ∈ SSet l r k)
    (hdeep : sLo l r k j + slack l r k j ≤ q j) :
    9 * sMeasure (Function.update l j (q j)) r k ≤ 8 * sMeasure l r k := by
  have hlj : l j ≤ q j := le_coord hq.2.1 j
  exact sMeasure_shrink' (sDiam_shrink hlr hlk hkr j hq hdeep)
    (fun m hm => sDiam_update_other j m hm (q j) hlj) (hbig j)

/-- Cutting downward at a point deep in coordinate `j` shrinks the measure. -/
theorem measure_shrink_down (hlr : l ≤ r) (hlk : lev l ≤ k) (hkr : k ≤ lev r)
    (hbig : ∀ i, 2 ≤ sDiam l r k i) (hq : q ∈ SSet l r k)
    (hdeep : q j + slack l r k j ≤ sHi l r k j) :
    9 * sMeasure l (Function.update r j (q j)) k ≤ 8 * sMeasure l r k := by
  have hrj : q j ≤ r j := le_coord hq.2.2 j
  exact sMeasure_shrink' (sDiam_shrink_down hlr hlk hkr j hq hdeep)
    (fun m hm => sDiam_update_other_down j m hm (q j) hrj) (hbig j)

end Shrink

/-- The fuel bookkeeping: one `8/9` shrink consumes one unit of fuel. -/
lemma fuel_step {n μ μ' : ℕ} (hfuel : 8 ^ (n + 1) * μ ≤ 26 * 9 ^ (n + 1))
    (hshrink : 9 * μ' ≤ 8 * μ) : 8 ^ n * μ' ≤ 26 * 9 ^ n := by
  refine Nat.le_of_mul_le_mul_left ?_ (show 0 < 9 by omega)
  have e1 : (8 : ℕ) ^ (n + 1) = 8 ^ n * 8 := pow_succ 8 n
  have e2 : (9 : ℕ) ^ (n + 1) = 9 ^ n * 9 := pow_succ 9 n
  calc 9 * (8 ^ n * μ') = 8 ^ n * (9 * μ') := by ring
    _ ≤ 8 ^ n * (8 * μ) := Nat.mul_le_mul_left _ hshrink
    _ = 8 ^ (n + 1) * μ := by rw [e1]; ring
    _ ≤ 26 * 9 ^ (n + 1) := hfuel
    _ = 9 * (26 * 9 ^ n) := by rw [e2]; ring

/-- With no fuel left the measure is small, hence some diameter is at most one. -/
lemma fuel_zero {μ : ℕ} (hfuel : 8 ^ 0 * μ ≤ 26 * 9 ^ 0) : μ ≤ 26 := by simpa using hfuel

/-! ### HL Lemma 3.12, as an algorithm

The five patterns.  Each is a decidable condition on the six bounding points, and
`sDiam_cases` together with `fin3_config_exists` guarantees that one of them holds
as soon as some diameter of the search space is at most one. -/

/-- A third configuration at `i`. -/
def P3 (u dn : Fin 3 → Pt 3) (i : Fin 3) : Prop := dn i i ≤ u i i + 1

/-- The coordinate a third configuration searches along. -/
def PjOf (u dn : Fin 3 → Pt 3) (i j : Fin 3) : Prop := j ≠ i ∧ dn i j < u i j

/-- A first configuration among the upward points. -/
def P1A (u : Fin 3 → Pt 3) (z : Fin 3 × Fin 3) : Prop :=
  z.1 ≠ z.2 ∧ u z.2 z.1 ≤ u z.1 z.1 ∧ u z.1 z.2 ≤ u z.2 z.2

/-- A second configuration among the upward points. -/
def P2A (u : Fin 3 → Pt 3) (z : Fin 3 × Fin 3) : Prop :=
  z.1 ≠ z.2 ∧ u z.2 z.1 ≤ u z.1 z.1 ∧ u (third z.1 z.2) z.2 ≤ u z.2 z.2 ∧
    u z.1 (third z.1 z.2) ≤ u (third z.1 z.2) (third z.1 z.2)

/-- A first configuration among the downward points. -/
def P1B (dn : Fin 3 → Pt 3) (z : Fin 3 × Fin 3) : Prop :=
  z.1 ≠ z.2 ∧ dn z.1 z.1 ≤ dn z.2 z.1 ∧ dn z.2 z.2 ≤ dn z.1 z.2

/-- A second configuration among the downward points. -/
def P2B (dn : Fin 3 → Pt 3) (z : Fin 3 × Fin 3) : Prop :=
  z.1 ≠ z.2 ∧ dn z.1 z.1 ≤ dn z.2 z.1 ∧ dn z.2 z.2 ≤ dn (third z.1 z.2) z.2 ∧
    dn (third z.1 z.2) (third z.1 z.2) ≤ dn z.1 (third z.1 z.2)

/-- The third-configuration branch: HL Lemma 3.13. -/
noncomputable def branch3 (budget k : ℕ) (u dn : Fin 3 → Pt 3) (i j : Fin 3) :
    QueryAlg (Pt 3) (Pt 3) (InnerAnswer 3) :=
  config3Alg i j (third i j) k (u i) (dn i) budget

/-- The first-configuration branch, upward form: the meet. -/
noncomputable def branch1A (u : Fin 3 → Pt 3) (i j : Fin 3) :
    QueryAlg (Pt 3) (Pt 3) (InnerAnswer 3) :=
  downOrVop (pick3 i j (u j) (u i) (argMin2 (u i) (u j) (third i j))) (glb (u i) (u j))

/-- The second-configuration branch, upward form: the meet of the three. -/
noncomputable def branch2A (u : Fin 3 → Pt 3) (i j : Fin 3) :
    QueryAlg (Pt 3) (Pt 3) (InnerAnswer 3) :=
  downOrVop (pick3 i j (argMin2 (u j) (u (third i j)) i) (argMin2 (u i) (u (third i j)) j)
    (argMin2 (u i) (u j) (third i j))) (glb (glb (u i) (u j)) (u (third i j)))

/-- The first-configuration branch, downward form: the join. -/
noncomputable def branch1B (dn : Fin 3 → Pt 3) (i j : Fin 3) :
    QueryAlg (Pt 3) (Pt 3) (InnerAnswer 3) :=
  upOrVop (pick3 i j (dn j) (dn i) (argMax2 (dn i) (dn j) (third i j))) (lub (dn i) (dn j))

/-- The second-configuration branch, downward form. -/
noncomputable def branch2B (dn : Fin 3 → Pt 3) (i j : Fin 3) :
    QueryAlg (Pt 3) (Pt 3) (InnerAnswer 3) :=
  upOrVop (pick3 i j (argMax2 (dn j) (dn (third i j)) i) (argMax2 (dn i) (dn (third i j)) j)
    (argMax2 (dn i) (dn j) (third i j))) (lub (lub (dn i) (dn j)) (dn (third i j)))

open Classical in
/-- **HL Lemma 3.12** as an algorithm.  The last branch is unreachable. -/
noncomputable def configResolve (budget k : ℕ) (u dn : Fin 3 → Pt 3) :
    QueryAlg (Pt 3) (Pt 3) (InnerAnswer 3) :=
  if ∃ i, P3 u dn i then
    branch3 budget k u dn (pick (P3 u dn)) (pick (PjOf u dn (pick (P3 u dn))))
  else if ∃ z, P1A u z then branch1A u (pick (P1A u)).1 (pick (P1A u)).2
  else if ∃ z, P2A u z then branch2A u (pick (P2A u)).1 (pick (P2A u)).2
  else if ∃ z, P1B dn z then branch1B dn (pick (P1B dn)).1 (pick (P1B dn)).2
  else if ∃ z, P2B dn z then branch2B dn (pick (P2B dn)).1 (pick (P2B dn)).2
  else QueryAlg.pure (.up (u 0))

lemma configResolve_bounded (budget k : ℕ) (u dn : Fin 3 → Pt 3) :
    Bounded (budget + 5) (configResolve budget k u dn) := by
  unfold configResolve branch3 branch1A branch2A branch1B branch2B
  split_ifs <;>
    first
      | exact (config3Alg_bounded _ _ _ _ _ _ _).mono (by omega)
      | exact (downOrVop_bounded _ _).mono (by omega)
      | exact (upOrVop_bounded _ _).mono (by omega)
      | exact Bounded.pure' _ _

section ConfigResolve

variable {F : Pt 3 → Pt 3} {lo hi : Pt 3} {k : ℕ} {u dn : Fin 3 → Pt 3}

/-- Each upward point exceeds the lower corner in at most one coordinate: two would
overshoot the level. -/
lemma row_up (h : LInv F lo hi k u dn) (hcase : k ≤ lev (lc u) + 1) :
    ∀ a b c : Fin 3, b ≠ a → c ≠ a → b ≠ c →
      ¬(decide (u b b < u a b) = true ∧ decide (u c c < u a c) = true) := by
  intro a b c hba hca hbc hcon
  obtain ⟨h1, h2⟩ := hcon
  simp only [decide_eq_true_eq] at h1 h2
  have hu : lev (u a) = u a a + u a b + u a c :=
    lev_three _ (Ne.symm hba) (Ne.symm hca) hbc
  have hl : lev (lc u) = u a a + u b b + u c c :=
    lev_three (lc u) (Ne.symm hba) (Ne.symm hca) hbc
  have := h.u_lev a
  omega

/-- Dually for the downward points. -/
lemma row_down (h : LInv F lo hi k u dn) (hcase : lev (uc dn) ≤ k + 1) :
    ∀ a b c : Fin 3, b ≠ a → c ≠ a → b ≠ c →
      ¬(decide (dn a b < dn b b) = true ∧ decide (dn a c < dn c c) = true) := by
  intro a b c hba hca hbc hcon
  obtain ⟨h1, h2⟩ := hcon
  simp only [decide_eq_true_eq] at h1 h2
  have hu : lev (dn a) = dn a a + dn a b + dn a c :=
    lev_three _ (Ne.symm hba) (Ne.symm hca) hbc
  have hl : lev (uc dn) = dn a a + dn b b + dn c c :=
    lev_three (uc dn) (Ne.symm hba) (Ne.symm hca) hbc
  have := h.dn_lev a
  omega

/-- **HL Lemma 3.12.**  A search space with a diameter of at most one resolves into
one of the five patterns, and each returns a solution. -/
theorem configResolve_isSol (h : LInv F lo hi k u dn) {i₀ : Fin 3}
    (hsmall : sDiam (lc u) (uc dn) k i₀ ≤ 1) {budget : ℕ}
    (hbud : ∀ j, hi j - lo j ≤ 2 ^ budget) :
    IsLevelsetSol F lo hi k ((configResolve budget k u dn).run F) := by
  unfold configResolve
  by_cases hA : ∃ i, P3 u dn i
  · rw [if_pos hA]
    have h3 : P3 u dn (pick (P3 u dn)) := pick_spec hA
    obtain ⟨j₀, hj₀⟩ := h.exists_lt_coord (pick (P3 u dn))
    have hjex : ∃ j, PjOf u dn (pick (P3 u dn)) j := ⟨j₀, hj₀⟩
    obtain ⟨hji, hjlt⟩ : PjOf u dn (pick (P3 u dn)) (pick (PjOf u dn (pick (P3 u dn)))) :=
      pick_spec hjex
    unfold branch3
    have hne := third_ne _ _ (Ne.symm hji)
    refine config3Alg_isSol
      ⟨Ne.symm hji, hne.1, hne.2, h.u_mem _, h.dn_mem _, h.u_lev _, h.dn_lev _,
        h.u_up _, h.dn_down _, h.ord _, h3, hjlt⟩ ?_
    have e1 : u (pick (P3 u dn)) (pick (PjOf u dn (pick (P3 u dn))))
        ≤ hi (pick (PjOf u dn (pick (P3 u dn)))) :=
      le_coord (mem_Box.mp (h.u_mem _)).2 _
    have e2 : lo (pick (PjOf u dn (pick (P3 u dn))))
        ≤ dn (pick (P3 u dn)) (pick (PjOf u dn (pick (P3 u dn)))) :=
      le_coord (mem_Box.mp (h.dn_mem _)).1 _
    have e3 := hbud (pick (PjOf u dn (pick (P3 u dn))))
    omega
  rw [if_neg hA]
  have hwide : ∀ i, lc u i + 2 ≤ uc dn i := by
    intro i
    by_contra hc
    have e1 : lc u i = u i i := rfl
    have e2 : uc dn i = dn i i := rfl
    exact hA ⟨i, by simp only [P3]; omega⟩
  by_cases hB : ∃ z, P1A u z
  · rw [if_pos hB]
    obtain ⟨hz1, hz2, hz3⟩ : P1A u (pick (P1A u)) := pick_spec hB
    unfold branch1A
    have hne := third_ne _ _ hz1
    exact alg_config1Up hz1 hne.1 hne.2 (h.u_mem _) (h.u_mem _) (h.u_lev _)
      ⟨hz1, h.u_up _, h.u_up _, hz2, hz3⟩
  rw [if_neg hB]
  by_cases hC : ∃ z, P2A u z
  · rw [if_pos hC]
    obtain ⟨hz1, hz2, hz3, hz4⟩ : P2A u (pick (P2A u)) := pick_spec hC
    unfold branch2A
    have hne := third_ne _ _ hz1
    exact alg_config2Up (h.u_mem _) (h.u_mem _) (h.u_mem _) (h.u_lev _)
      ⟨hz1, hne.1, hne.2, h.u_up _, h.u_up _, h.u_up _, hz2, hz3, hz4⟩
  rw [if_neg hC]
  by_cases hD : ∃ z, P1B dn z
  · rw [if_pos hD]
    obtain ⟨hz1, hz2, hz3⟩ : P1B dn (pick (P1B dn)) := pick_spec hD
    unfold branch1B
    have hne := third_ne _ _ hz1
    exact alg_config1Down hz1 hne.1 hne.2 (h.dn_mem _) (h.dn_mem _) (h.dn_lev _)
      ⟨hz1, h.dn_down _, h.dn_down _, hz2, hz3⟩
  rw [if_neg hD]
  by_cases hE : ∃ z, P2B dn z
  · rw [if_pos hE]
    obtain ⟨hz1, hz2, hz3, hz4⟩ : P2B dn (pick (P2B dn)) := pick_spec hE
    unfold branch2B
    have hne := third_ne _ _ hz1
    exact alg_config2Down (h.dn_mem _) (h.dn_mem _) (h.dn_mem _) (h.dn_lev _)
      ⟨hz1, hne.1, hne.2, h.dn_down _, h.dn_down _, h.dn_down _, hz2, hz3, hz4⟩
  -- all five patterns fail, which `sDiam_cases` forbids
  exfalso
  rcases sDiam_cases hwide hsmall with hcase | hcase
  · rcases fin3_config_exists _ (row_up h hcase) with
      ⟨i, j, hij, h1, h2⟩ | ⟨i, j, p, hij, hip, hjp, h1, h2, h3⟩
    · simp only [decide_eq_false_iff_not, not_lt] at h1 h2
      exact hB ⟨(i, j), hij, h1, h2⟩
    · simp only [decide_eq_false_iff_not, not_lt] at h1 h2 h3
      obtain rfl := third_eq i j p hij hip hjp
      exact hC ⟨(i, j), hij, h1, h2, h3⟩
  · rcases fin3_config_exists _ (row_down h hcase) with
      ⟨i, j, hij, h1, h2⟩ | ⟨i, j, p, hij, hip, hjp, h1, h2, h3⟩
    · simp only [decide_eq_false_iff_not, not_lt] at h1 h2
      exact hD ⟨(i, j), hij, h1, h2⟩
    · simp only [decide_eq_false_iff_not, not_lt] at h1 h2 h3
      obtain rfl := third_eq i j p hij hip hjp
      exact hE ⟨(i, j), hij, h1, h2, h3⟩

end ConfigResolve

/-! ### The shrinking loop -/

open Classical in
/-- HL's shrinking loop.  While some diameter is large it cuts at a deep query point
(HL Lemma 3.5); when the search space is too small for that it queries the three
corner points (HL Lemma 3.6); and once some diameter reaches one it resolves into a
configuration (HL Lemma 3.12). -/
noncomputable def lsLoop (k budget : ℕ) (n : ℕ) (u dn : Fin 3 → Pt 3) :
    QueryAlg (Pt 3) (Pt 3) (InnerAnswer 3) :=
  match n with
  | 0 => configResolve budget k u dn
  | n + 1 =>
    if ∃ i, sDiam (lc u) (uc dn) k i ≤ 1 then configResolve budget k u dn
    else if ∃ q, DeepP (lc u) (uc dn) k q then
      QueryAlg.ask (pick (DeepP (lc u) (uc dn) k)) >>= fun v =>
        dispatch (fun a b => lsLoop k budget n a b) u dn
          (pick (DeepP (lc u) (uc dn) k)) v
    else if k = sLo (lc u) (uc dn) k 0 + sLo (lc u) (uc dn) k 1
        + sLo (lc u) (uc dn) k 2 + 2 then
      cornerRun (fun a b => lsLoop k budget n a b) u dn (cornerPt (lc u) (uc dn) k)
        (fun i v => iUpAt (cornerPt (lc u) (uc dn) k i) v i)
        (upOrVop (cornerPt (lc u) (uc dn) k) (cornerJoin (lc u) (uc dn) k))
    else
      cornerRun (fun a b => lsLoop k budget n a b) u dn (cornerPtD (lc u) (uc dn) k)
        (fun i v => iDownAt (cornerPtD (lc u) (uc dn) k i) v i)
        (downOrVop (cornerPtD (lc u) (uc dn) k) (cornerMeet (lc u) (uc dn) k))

lemma lsLoop_zero (k budget : ℕ) (u dn : Fin 3 → Pt 3) :
    lsLoop k budget 0 u dn = configResolve budget k u dn := rfl

open Classical in
lemma lsLoop_succ (k budget n : ℕ) (u dn : Fin 3 → Pt 3) :
    lsLoop k budget (n + 1) u dn =
      (if ∃ i, sDiam (lc u) (uc dn) k i ≤ 1 then configResolve budget k u dn
      else if ∃ q, DeepP (lc u) (uc dn) k q then
        QueryAlg.ask (pick (DeepP (lc u) (uc dn) k)) >>= fun v =>
          dispatch (fun a b => lsLoop k budget n a b) u dn
            (pick (DeepP (lc u) (uc dn) k)) v
      else if k = sLo (lc u) (uc dn) k 0 + sLo (lc u) (uc dn) k 1
          + sLo (lc u) (uc dn) k 2 + 2 then
        cornerRun (fun a b => lsLoop k budget n a b) u dn (cornerPt (lc u) (uc dn) k)
          (fun i v => iUpAt (cornerPt (lc u) (uc dn) k i) v i)
          (upOrVop (cornerPt (lc u) (uc dn) k) (cornerJoin (lc u) (uc dn) k))
      else
        cornerRun (fun a b => lsLoop k budget n a b) u dn (cornerPtD (lc u) (uc dn) k)
          (fun i v => iDownAt (cornerPtD (lc u) (uc dn) k i) v i)
          (downOrVop (cornerPtD (lc u) (uc dn) k) (cornerMeet (lc u) (uc dn) k))) := rfl

lemma lsLoop_bounded (k budget : ℕ) :
    ∀ (n : ℕ) (u dn : Fin 3 → Pt 3),
      Bounded (3 * n + (budget + 5)) (lsLoop k budget n u dn) := by
  intro n
  induction n with
  | zero => intro u dn; exact (configResolve_bounded budget k u dn).mono (by omega)
  | succ n ih =>
    intro u dn
    rw [lsLoop_succ]
    have hrec : ∀ a b, Bounded (3 * n + (budget + 5)) (lsLoop k budget n a b) := ih
    split_ifs
    · exact (configResolve_bounded budget k u dn).mono (by omega)
    · refine Bounded.mono (n := 1 + (3 * n + (budget + 5)))
        ((Bounded.ask _).bind fun v => dispatch_bounded hrec _ _ _ v) (by omega)
    · exact (cornerRun_bounded hrec _ _ _ _ ((upOrVop_bounded _ _).mono (by omega))).mono
        (by omega)
    · exact (cornerRun_bounded hrec _ _ _ _ ((downOrVop_bounded _ _).mono (by omega))).mono
        (by omega)

/-! ### The corner points of HL Lemma 3.6 in the search space -/

section CornerFacts

variable {l r : Pt 3} {k : ℕ}

lemma cornerPt_self (i : Fin 3) : cornerPt l r k i i = sLo l r k i := by simp [cornerPt]

lemma cornerPt_other {i j : Fin 3} (h : j ≠ i) :
    cornerPt l r k i j = sLo l r k j + 1 := by simp [cornerPt, h]

lemma cornerPtD_self (i : Fin 3) : cornerPtD l r k i i = sHi l r k i := by simp [cornerPtD]

lemma cornerPtD_other {i j : Fin 3} (h : j ≠ i) :
    cornerPtD l r k i j = sHi l r k j - 1 := by simp [cornerPtD, h]

variable (hlr : l ≤ r) (hlk : lev l ≤ k) (hkr : k ≤ lev r)
  (hbig : ∀ i, 2 ≤ sDiam l r k i)

include hlr hlk hkr hbig

lemma cornerPt_mem_SSet
    (hk : k = sLo l r k 0 + sLo l r k 1 + sLo l r k 2 + 2) (i : Fin 3) :
    cornerPt l r k i ∈ SSet l r k := by
  refine ⟨by rw [lev_cornerPt]; omega, coord_le fun m => ?_, coord_le fun m => ?_⟩
  · have h1 : l m ≤ sLo l r k m := le_max_left _ _
    by_cases hm : m = i
    · subst hm; rw [cornerPt_self]; omega
    · rw [cornerPt_other hm]; omega
  · have h1 : sHi l r k m ≤ r m := min_le_left _ _
    have h2 := hbig m
    have h3 : sDiam l r k m = sHi l r k m - sLo l r k m := rfl
    have h4 := sLo_le_sHi hlr hlk hkr m
    by_cases hm : m = i
    · subst hm; rw [cornerPt_self]; omega
    · rw [cornerPt_other hm]; omega

lemma cornerPtD_mem_SSet
    (hk : k + 2 = sHi l r k 0 + sHi l r k 1 + sHi l r k 2) (i : Fin 3) :
    cornerPtD l r k i ∈ SSet l r k := by
  refine ⟨?_, coord_le fun m => ?_, coord_le fun m => ?_⟩
  · have := lev_cornerPtD hbig hlr hlk hkr i
    omega
  · have h1 : l m ≤ sLo l r k m := le_max_left _ _
    have h2 := hbig m
    have h3 : sDiam l r k m = sHi l r k m - sLo l r k m := rfl
    have h4 := sLo_le_sHi hlr hlk hkr m
    by_cases hm : m = i
    · subst hm; rw [cornerPtD_self]; omega
    · rw [cornerPtD_other hm]; omega
  · have h1 : sHi l r k m ≤ r m := min_le_left _ _
    by_cases hm : m = i
    · subst hm; rw [cornerPtD_self]; omega
    · rw [cornerPtD_other hm]; omega

/-- A corner is deep enough for a *downward* cut in every coordinate. -/
lemma cornerPt_deep_down (hslack : ∀ m, slack l r k m = 1) (i j : Fin 3) :
    cornerPt l r k i j + slack l r k j ≤ sHi l r k j := by
  have h2 := hbig j
  have h3 : sDiam l r k j = sHi l r k j - sLo l r k j := rfl
  have h4 := sLo_le_sHi hlr hlk hkr j
  rw [hslack]
  by_cases hm : j = i
  · subst hm; rw [cornerPt_self]; omega
  · rw [cornerPt_other hm]; omega

/-- Dually, a dual corner is deep enough for an *upward* cut in every coordinate. -/
lemma cornerPtD_deep_up (hslack : ∀ m, slack l r k m = 1) (i j : Fin 3) :
    sLo l r k j + slack l r k j ≤ cornerPtD l r k i j := by
  have h2 := hbig j
  have h3 : sDiam l r k j = sHi l r k j - sLo l r k j := rfl
  have h4 := sLo_le_sHi hlr hlk hkr j
  rw [hslack]
  by_cases hm : j = i
  · subst hm; rw [cornerPtD_self]; omega
  · rw [cornerPtD_other hm]; omega

omit hlr hlk hkr hbig in
/-- In the coordinates other than its own, a corner is deep enough for an upward
cut.  Its own coordinate is exactly the case in which the corner passes the test. -/
lemma cornerPt_deep_up (hslack : ∀ m, slack l r k m = 1) {i j : Fin 3} (hij : j ≠ i) :
    sLo l r k j + slack l r k j ≤ cornerPt l r k i j := by
  rw [cornerPt_other hij, hslack]

omit hlr hlk hkr in
lemma cornerPtD_deep_down (hslack : ∀ m, slack l r k m = 1) {i j : Fin 3} (hij : j ≠ i) :
    cornerPtD l r k i j + slack l r k j ≤ sHi l r k j := by
  have h2 := hbig j
  have h3 : sDiam l r k j = sHi l r k j - sLo l r k j := rfl
  rw [cornerPtD_other hij, hslack]
  omega

end CornerFacts

/-! ### Correctness of the loop -/

/-- **The shrinking loop is correct.**  The fuel hypothesis is that `n` rounds of
`8/9` shrinking bring the measure below `27`, at which point some diameter is at
most one and HL Lemma 3.12 applies. -/
theorem lsLoop_isSol {F : Pt 3 → Pt 3} {lo hi : Pt 3} {k budget : ℕ}
    (hbud : ∀ j, hi j - lo j ≤ 2 ^ budget) :
    ∀ (n : ℕ) (u dn : Fin 3 → Pt 3), LInv F lo hi k u dn →
      8 ^ n * sMeasure (lc u) (uc dn) k ≤ 26 * 9 ^ n →
      IsLevelsetSol F lo hi k ((lsLoop k budget n u dn).run F) := by
  intro n
  induction n with
  | zero =>
    intro u dn h hfuel
    have hmu := fuel_zero hfuel
    have hsmall : ∃ i, sDiam (lc u) (uc dn) k i ≤ 1 := by
      by_contra hc
      push Not at hc
      have h0 : 3 ≤ sDiam (lc u) (uc dn) k 0 + 1 := by have := hc 0; omega
      have h1 : 3 ≤ sDiam (lc u) (uc dn) k 1 + 1 := by have := hc 1; omega
      have h2 : 3 ≤ sDiam (lc u) (uc dn) k 2 + 1 := by have := hc 2; omega
      have hbd : 3 * 3 * 3 ≤ sMeasure (lc u) (uc dn) k :=
        Nat.mul_le_mul (Nat.mul_le_mul h0 h1) h2
      omega
    obtain ⟨i₀, hi₀⟩ := hsmall
    rw [lsLoop_zero]
    exact configResolve_isSol h hi₀ hbud
  | succ n ih =>
    intro u dn h hfuel
    have hlr := h.lc_le_uc
    have hlk := h.lev_lo
    have hkr := h.lev_hi
    rw [lsLoop_succ]
    by_cases hs : ∃ i, sDiam (lc u) (uc dn) k i ≤ 1
    · rw [if_pos hs]
      obtain ⟨i₀, hi₀⟩ := hs
      exact configResolve_isSol h hi₀ hbud
    rw [if_neg hs]
    have hbig : ∀ i, 2 ≤ sDiam (lc u) (uc dn) k i := by
      intro i
      by_contra hc
      exact hs ⟨i, by omega⟩
    by_cases hd : ∃ q, DeepP (lc u) (uc dn) k q
    · rw [if_pos hd]
      have hq : DeepP (lc u) (uc dn) k (pick (DeepP (lc u) (uc dn) k)) := pick_spec hd
      rw [QueryAlg.run_bind, QueryAlg.run_ask]
      refine dispatch_isSol h hq.1 (fun j hup => ?_) (fun j hdown => ?_)
      · refine ih _ _ (h.cut_up hq.1 hup) (fuel_step hfuel ?_)
        rw [lc_update]
        exact measure_shrink_up hlr hlk hkr hbig hq.1 (hq.2 j).1
      · refine ih _ _ (h.cut_down hq.1 hdown) (fuel_step hfuel ?_)
        rw [uc_update]
        exact measure_shrink_down hlr hlk hkr hbig hq.1 (hq.2 j).2
    rw [if_neg hd]
    -- no deep query point: every diameter is between two and five
    have hsmall5 : ∀ i, sDiam (lc u) (uc dn) k i ≤ 5 := by
      intro i
      by_contra hc
      push Not at hc
      obtain ⟨i₁, hmax⟩ := exists_max3 (sDiam (lc u) (uc dn) k)
      have hD6 : 6 ≤ sDiam (lc u) (uc dn) k i₁ := by have := hmax i; omega
      obtain ⟨q, hq1, hq2⟩ := exists_deep_query hlr hlk hkr hmax hD6 le_rfl hbig
      exact hd ⟨q, hq1, hq2⟩
    have hslack : ∀ i, slack (lc u) (uc dn) k i = 1 := by
      intro i
      have := hbig i
      have := hsmall5 i
      simp only [slack]
      omega
    have hstuck : ¬ ∃ q, q ∈ SSet (lc u) (uc dn) k ∧
        ∀ i, sLo (lc u) (uc dn) k i < q i ∧ q i < sHi (lc u) (uc dn) k i := by
      intro hex
      obtain ⟨q, hq1, hq2⟩ := hex
      refine hd ⟨q, hq1, fun i => ?_⟩
      have := hq2 i
      rw [hslack i]
      omega
    have hlevels := stuck_levels hlr hlk hkr hbig hstuck
    by_cases hk : k = sLo (lc u) (uc dn) k 0 + sLo (lc u) (uc dn) k 1
        + sLo (lc u) (uc dn) k 2 + 2
    · rw [if_pos hk]
      refine cornerRun_isSol (fun hall => ?_) (fun i hfail => ?_)
      · exact alg_corner_up h.lo_le_lc h.uc_le_hi hbig hlr hlk hkr hk hall
      · refine dispatch_isSol h (cornerPt_mem_SSet hlr hlk hkr hbig hk i)
          (fun j hup => ?_) (fun j hdown => ?_)
        · have hji : j ≠ i := by
            intro he
            subst he
            exact hfail hup
          refine ih _ _ (h.cut_up (cornerPt_mem_SSet hlr hlk hkr hbig hk i) hup)
            (fuel_step hfuel ?_)
          rw [lc_update]
          exact measure_shrink_up hlr hlk hkr hbig
            (cornerPt_mem_SSet hlr hlk hkr hbig hk i) (cornerPt_deep_up hslack hji)
        · refine ih _ _ (h.cut_down (cornerPt_mem_SSet hlr hlk hkr hbig hk i) hdown)
            (fuel_step hfuel ?_)
          rw [uc_update]
          exact measure_shrink_down hlr hlk hkr hbig
            (cornerPt_mem_SSet hlr hlk hkr hbig hk i)
            (cornerPt_deep_down hlr hlk hkr hbig hslack i j)
    · rw [if_neg hk]
      have hk2 : k + 2 = sHi (lc u) (uc dn) k 0 + sHi (lc u) (uc dn) k 1
          + sHi (lc u) (uc dn) k 2 := by
        rcases hlevels with h' | h'
        · exact absurd h' hk
        · exact h'
      refine cornerRun_isSol (fun hall => ?_) (fun i hfail => ?_)
      · exact alg_corner_down h.lo_le_lc h.uc_le_hi hbig hlr hlk hkr hk2 hall
      · refine dispatch_isSol h (cornerPtD_mem_SSet hlr hlk hkr hbig hk2 i)
          (fun j hup => ?_) (fun j hdown => ?_)
        · refine ih _ _ (h.cut_up (cornerPtD_mem_SSet hlr hlk hkr hbig hk2 i) hup)
            (fuel_step hfuel ?_)
          rw [lc_update]
          exact measure_shrink_up hlr hlk hkr hbig
            (cornerPtD_mem_SSet hlr hlk hkr hbig hk2 i)
            (cornerPtD_deep_up hlr hlk hkr hbig hslack i j)
        · have hji : j ≠ i := by
            intro he
            subst he
            exact hfail hdown
          refine ih _ _ (h.cut_down (cornerPtD_mem_SSet hlr hlk hkr hbig hk2 i) hdown)
            (fuel_step hfuel ?_)
          rw [uc_update]
          exact measure_shrink_down hlr hlk hkr hbig
            (cornerPtD_mem_SSet hlr hlk hkr hbig hk2 i)
            (cornerPtD_deep_down hbig hslack hji)

/-! ### Initialisation

The six calls of HL Lemma 3.14.  Each either answers the levelset problem outright
or returns a bounding point; `bindInit` sequences that. -/

/-- Sequence an initialisation call. -/
noncomputable def bindInit (alg : QueryAlg (Pt 3) (Pt 3) (InnerAnswer 3 ⊕ Pt 3))
    (g : Pt 3 → QueryAlg (Pt 3) (Pt 3) (InnerAnswer 3)) :
    QueryAlg (Pt 3) (Pt 3) (InnerAnswer 3) :=
  alg >>= fun a => Sum.elim QueryAlg.pure g a

lemma bindInit_bounded {n c : ℕ} {alg : QueryAlg (Pt 3) (Pt 3) (InnerAnswer 3 ⊕ Pt 3)}
    (h : Bounded n alg) {g : Pt 3 → QueryAlg (Pt 3) (Pt 3) (InnerAnswer 3)}
    (hg : ∀ z, Bounded c (g z)) : Bounded (n + c) (bindInit alg g) := by
  unfold bindInit
  refine h.bind fun a => ?_
  rcases a with ans | z
  · exact Bounded.pure' _ _
  · exact hg z

section BindInit

variable {F : Pt 3 → Pt 3} {lo hi : Pt 3} {k : ℕ} {i : Fin 3}
  {alg : QueryAlg (Pt 3) (Pt 3) (InnerAnswer 3 ⊕ Pt 3)}
  {g : Pt 3 → QueryAlg (Pt 3) (Pt 3) (InnerAnswer 3)}

lemma bindInitUp_isSol (hs : IsInitUp F lo hi k i (alg.run F))
    (hg : ∀ z, z ∈ Box lo hi → lev z = k → z i = sLo lo hi k i → IUp F z i →
      IsLevelsetSol F lo hi k ((g z).run F)) :
    IsLevelsetSol F lo hi k ((bindInit alg g).run F) := by
  unfold bindInit
  rw [QueryAlg.run_bind]
  revert hs
  rcases alg.run F with ans | z
  · exact fun hs => hs
  · exact fun hs => hg z hs.1 hs.2.1 hs.2.2.1 hs.2.2.2

lemma bindInitDown_isSol (hs : IsInitDown F lo hi k i (alg.run F))
    (hg : ∀ z, z ∈ Box lo hi → lev z = k → z i = sHi lo hi k i → IDown F z i →
      IsLevelsetSol F lo hi k ((g z).run F)) :
    IsLevelsetSol F lo hi k ((bindInit alg g).run F) := by
  unfold bindInit
  rw [QueryAlg.run_bind]
  revert hs
  rcases alg.run F with ans | z
  · exact fun hs => hs
  · exact fun hs => hg z hs.1 hs.2.1 hs.2.2.1 hs.2.2.2

end BindInit

/-! ### The levelset subprocedure -/

/-- **The Haslebacher–Lill levelset subprocedure.**  Six calls of Lemma 3.14 to
initialise the bounding points, then the shrinking loop. -/
noncomputable def lsInner (budget : ℕ) (lo hi : Pt 3) (k : ℕ) :
    QueryAlg (Pt 3) (Pt 3) (InnerAnswer 3) :=
  bindInit (initUpAlg lo hi k 0 1 2 budget) fun z0 =>
    bindInit (initUpAlg lo hi k 1 0 2 budget) fun z1 =>
      bindInit (initUpAlg lo hi k 2 0 1 budget) fun z2 =>
        bindInit (initDownAlg lo hi k 0 1 2 budget) fun w0 =>
          bindInit (initDownAlg lo hi k 1 0 2 budget) fun w1 =>
            bindInit (initDownAlg lo hi k 2 0 1 budget) fun w2 =>
              lsLoop k budget (18 * budget) (pick3 0 1 z0 z1 z2) (pick3 0 1 w0 w1 w2)

theorem lsInner_bounded (budget : ℕ) (lo hi : Pt 3) (k : ℕ) :
    Bounded (61 * budget + 29) (lsInner budget lo hi k) := by
  have hloop : ∀ u dn, Bounded (55 * budget + 5) (lsLoop k budget (18 * budget) u dn) :=
    fun u dn => (lsLoop_bounded k budget (18 * budget) u dn).mono (by omega)
  unfold lsInner
  refine Bounded.mono (n := (budget + 4) + ((budget + 4) + ((budget + 4) +
    ((budget + 4) + ((budget + 4) + ((budget + 4) + (55 * budget + 5))))))) ?_ (by omega)
  refine bindInit_bounded (initUpAlg_bounded _ _ _ _ _ _ _) fun z0 => ?_
  refine bindInit_bounded (initUpAlg_bounded _ _ _ _ _ _ _) fun z1 => ?_
  refine bindInit_bounded (initUpAlg_bounded _ _ _ _ _ _ _) fun z2 => ?_
  refine bindInit_bounded (initDownAlg_bounded _ _ _ _ _ _ _) fun w0 => ?_
  refine bindInit_bounded (initDownAlg_bounded _ _ _ _ _ _ _) fun w1 => ?_
  refine bindInit_bounded (initDownAlg_bounded _ _ _ _ _ _ _) fun w2 => ?_
  exact hloop _ _

/-- Six rounds of `8/9` shrinking at least halve the measure: `2 · 8⁶ ≤ 9⁶`. -/
lemma fuel_init {b M : ℕ} (hM : M ≤ 2 ^ (3 * b)) :
    8 ^ (18 * b) * M ≤ 26 * 9 ^ (18 * b) := by
  have e6 : 6 * (3 * b) = 18 * b := by omega
  have e1 : ((8 : ℕ) ^ 6) ^ (3 * b) = 8 ^ (18 * b) := by rw [← pow_mul, e6]
  have e2 : ((9 : ℕ) ^ 6) ^ (3 * b) = 9 ^ (18 * b) := by rw [← pow_mul, e6]
  have h1 : 8 ^ (18 * b) * M ≤ 8 ^ (18 * b) * 2 ^ (3 * b) := Nat.mul_le_mul_left _ hM
  have h2 : (8 : ℕ) ^ (18 * b) * 2 ^ (3 * b) = (8 ^ 6 * 2) ^ (3 * b) := by
    rw [mul_pow, e1]
  have h3 : ((8 : ℕ) ^ 6 * 2) ^ (3 * b) ≤ ((9 : ℕ) ^ 6) ^ (3 * b) :=
    Nat.pow_le_pow_left (by norm_num) _
  have h4 : (9 : ℕ) ^ (18 * b) ≤ 26 * 9 ^ (18 * b) :=
    Nat.le_mul_of_pos_left _ (by omega)
  omega

/-- **The Haslebacher–Lill levelset subprocedure is correct.**  This is HL §3
assembled: Lemma 3.14 initialises, Lemma 3.5 or Lemma 3.6 cuts, and Lemma 3.12 with
Lemma 3.13 and Observations 3.9/3.10 finishes.

`budget` must cover the side lengths of the ambient box; `lsInner_bounded` then
gives `O(budget)` queries, i.e. `O(log n)` on `[0,n]³`. -/
theorem solvesLevelset_lsInner {LO HI : Pt 3} {budget : ℕ}
    (hbud : ∀ j, HI j - LO j + 1 ≤ 2 ^ budget) : SolvesLevelset (lsInner budget) LO HI := by
  intro F lo hi k hLlo hlohi hhiH hlo hhi hlk hkr
  have hbud1 : ∀ j, hi j - lo j + 1 ≤ 2 ^ budget := by
    intro j
    have h1 : LO j ≤ lo j := le_coord hLlo j
    have h2 : hi j ≤ HI j := le_coord hhiH j
    have h3 := hbud j
    omega
  have hbud2 : ∀ j, hi j - lo j ≤ 2 ^ budget := fun j => by have := hbud1 j; omega
  have hbU : ∀ i j p : Fin 3, initU1 lo hi k i j p - initU0 lo hi k i j p ≤ 2 ^ budget := by
    intro i j p
    have h1 : initU1 lo hi k i j p ≤ hi j := min_le_left _ _
    have h2 : lo j ≤ initU0 lo hi k i j p := le_max_left _ _
    have h3 := hbud2 j
    omega
  have hbT : ∀ i j p : Fin 3, initT1 lo hi k i j p - initT0 lo hi k i j p ≤ 2 ^ budget := by
    intro i j p
    have h1 : initT1 lo hi k i j p ≤ hi j := min_le_left _ _
    have h2 : lo j ≤ initT0 lo hi k i j p := le_max_left _ _
    have h3 := hbud2 j
    omega
  have tf : ∀ i j p : Fin 3, i ≠ j → i ≠ p → j ≠ p → TopFacts lo hi k i j p :=
    fun i j p a b c => ⟨a, b, c, hlohi, hlk, hkr⟩
  unfold lsInner
  refine bindInitUp_isSol
    (initUpAlg_isSol (tf 0 1 2 (by decide) (by decide) (by decide)) hlo hhi (hbU 0 1 2))
    (fun z0 m0 l0 c0 up0 => ?_)
  refine bindInitUp_isSol
    (initUpAlg_isSol (tf 1 0 2 (by decide) (by decide) (by decide)) hlo hhi (hbU 1 0 2))
    (fun z1 m1 l1 c1 up1 => ?_)
  refine bindInitUp_isSol
    (initUpAlg_isSol (tf 2 0 1 (by decide) (by decide) (by decide)) hlo hhi (hbU 2 0 1))
    (fun z2 m2 l2 c2 up2 => ?_)
  refine bindInitDown_isSol
    (initDownAlg_isSol (tf 0 1 2 (by decide) (by decide) (by decide)) hlo hhi (hbT 0 1 2))
    (fun w0 n0 v0 d0 dw0 => ?_)
  refine bindInitDown_isSol
    (initDownAlg_isSol (tf 1 0 2 (by decide) (by decide) (by decide)) hlo hhi (hbT 1 0 2))
    (fun w1 n1 v1 d1 dw1 => ?_)
  refine bindInitDown_isSol
    (initDownAlg_isSol (tf 2 0 1 (by decide) (by decide) (by decide)) hlo hhi (hbT 2 0 1))
    (fun w2 n2 v2 d2 dw2 => ?_)
  -- the six points, indexed
  have hU0 : (pick3 (0 : Fin 3) 1 z0 z1 z2) 0 = z0 := pick3_i 0 1 z0 z1 z2
  have hU1 : (pick3 (0 : Fin 3) 1 z0 z1 z2) 1 = z1 := pick3_j (by decide) z0 z1 z2
  have hU2 : (pick3 (0 : Fin 3) 1 z0 z1 z2) 2 = z2 :=
    pick3_other (by decide) (by decide) z0 z1 z2
  have hD0 : (pick3 (0 : Fin 3) 1 w0 w1 w2) 0 = w0 := pick3_i 0 1 w0 w1 w2
  have hD1 : (pick3 (0 : Fin 3) 1 w0 w1 w2) 1 = w1 := pick3_j (by decide) w0 w1 w2
  have hD2 : (pick3 (0 : Fin 3) 1 w0 w1 w2) 2 = w2 :=
    pick3_other (by decide) (by decide) w0 w1 w2
  set U := pick3 (0 : Fin 3) 1 z0 z1 z2 with hUdef
  set D := pick3 (0 : Fin 3) 1 w0 w1 w2 with hDdef
  have hlcU : ∀ i, U i i = sLo lo hi k i := by
    intro i
    rcases fin3_eq i with rfl | rfl | rfl
    · rw [hU0]; exact c0
    · rw [hU1]; exact c1
    · rw [hU2]; exact c2
  have hucD : ∀ i, D i i = sHi lo hi k i := by
    intro i
    rcases fin3_eq i with rfl | rfl | rfl
    · rw [hD0]; exact d0
    · rw [hD1]; exact d1
    · rw [hD2]; exact d2
  refine lsLoop_isSol hbud2 _ U D
    ⟨fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_,
      fun i => ?_, ?_, ?_⟩ ?_
  · rcases fin3_eq i with rfl | rfl | rfl
    · rw [hU0]; exact m0
    · rw [hU1]; exact m1
    · rw [hU2]; exact m2
  · rcases fin3_eq i with rfl | rfl | rfl
    · rw [hD0]; exact n0
    · rw [hD1]; exact n1
    · rw [hD2]; exact n2
  · rcases fin3_eq i with rfl | rfl | rfl
    · rw [hU0]; exact l0
    · rw [hU1]; exact l1
    · rw [hU2]; exact l2
  · rcases fin3_eq i with rfl | rfl | rfl
    · rw [hD0]; exact v0
    · rw [hD1]; exact v1
    · rw [hD2]; exact v2
  · rcases fin3_eq i with rfl | rfl | rfl
    · rw [hU0]; exact up0
    · rw [hU1]; exact up1
    · rw [hU2]; exact up2
  · rcases fin3_eq i with rfl | rfl | rfl
    · rw [hD0]; exact dw0
    · rw [hD1]; exact dw1
    · rw [hD2]; exact dw2
  · rw [hlcU i, hucD i]; exact sLo_le_sHi hlohi hlk hkr i
  · have e : lev (fun i => U i i) = sLo lo hi k 0 + sLo lo hi k 1 + sLo lo hi k 2 := by
      rw [lev_eq_three]
      simp only [hlcU]
    rw [e]
    have := sum_sLo_add_sDiam_le hlohi hlk hkr 0
    omega
  · have e : lev (fun i => D i i) = sHi lo hi k 0 + sHi lo hi k 1 + sHi lo hi k 2 := by
      rw [lev_eq_three]
      simp only [hucD]
    rw [e]
    have := le_sum_sHi_sub_sDiam hlohi hlk hkr 0
    omega
  · refine fuel_init ?_
    have hd : ∀ i, sDiam (lc U) (uc D) k i + 1 ≤ 2 ^ budget := by
      intro i
      have h1 : sHi (lc U) (uc D) k i ≤ uc D i := min_le_left _ _
      have h2 : lc U i ≤ sLo (lc U) (uc D) k i := le_max_left _ _
      have h3 : sDiam (lc U) (uc D) k i
          = sHi (lc U) (uc D) k i - sLo (lc U) (uc D) k i := rfl
      have h4 : uc D i = sHi lo hi k i := hucD i
      have h5 : lc U i = sLo lo hi k i := hlcU i
      have h6 : sHi lo hi k i ≤ hi i := min_le_left _ _
      have h7 : lo i ≤ sLo lo hi k i := le_max_left _ _
      have h8 := hbud1 i
      omega
    have hprod : sMeasure (lc U) (uc D) k ≤ 2 ^ budget * 2 ^ budget * 2 ^ budget :=
      Nat.mul_le_mul (Nat.mul_le_mul (hd 0) (hd 1)) (hd 2)
    have hpow : (2 : ℕ) ^ budget * 2 ^ budget * 2 ^ budget = 2 ^ (3 * budget) := by
      rw [← pow_add, ← pow_add]
      congr 1
      omega
    omega

end Tfnp.Tarski
