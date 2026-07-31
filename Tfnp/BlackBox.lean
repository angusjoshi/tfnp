/-
Copyright (c) 2026 Angus Joshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Angus Joshi
-/

import Tfnp.QueryModel
import Tfnp.PPAD

/-!
# Black-box lower bounds

Every query lower bound rests on one observation: a deterministic algorithm
cannot tell two oracles apart if they agree wherever it actually looks. This
file makes that precise once (`run_eq_of_agree`) and packages the standard
two-instance argument (`not_valid_of_agree`), then applies it to `EndOfLine`.

## Main results

* `QueryAlg.queried` — the list of points an algorithm actually queries.
* `QueryAlg.run_eq_of_agree` — oracles agreeing on the queried points give the
  same output *and* the same query list.
* `QueryAlg.not_valid_of_agree` — the two-instance template: if `f` and `g`
  agree on what the algorithm looks at, and no point is valid for both, then it
  is wrong on one of them.
* `eol_must_query_endpoint` — a correct `EndOfLine` algorithm must query the
  endpoint of the path. Non-trivial: it cannot deduce the answer, it has to look.
-/

set_option autoImplicit false

namespace Tfnp

namespace QueryAlg

variable {Q R α : Type}

/-- The points the algorithm actually queries when run against `f`, in order. -/
def queried (f : Q → R) : QueryAlg Q R α → List Q
  | .pure _ => []
  | .query q κ => q :: queried f (κ (f q))

@[simp] lemma queried_pure (f : Q → R) (a : α) :
    (QueryAlg.pure a : QueryAlg Q R α).queried f = [] := rfl

@[simp] lemma queried_query (f : Q → R) (q : Q) (κ : R → QueryAlg Q R α) :
    (QueryAlg.query q κ).queried f = q :: (κ (f q)).queried f := rfl

/-- The number of queries is the length of the query list. -/
theorem length_queried (f : Q → R) (A : QueryAlg Q R α) :
    (A.queried f).length = A.queries f := by
  induction A with
  | pure a => simp [queries]
  | query q κ ih =>
    simp only [queried_query, List.length_cons, queries]
    rw [ih (f q)]
    omega

/-- **Indistinguishability.** If two oracles agree on every point the algorithm
queries under `f`, then the run against `g` is identical: same output, same
query list. This is the whole content of a deterministic lower bound. -/
theorem run_eq_of_agree (A : QueryAlg Q R α) (f g : Q → R)
    (h : ∀ q ∈ A.queried f, f q = g q) :
    A.run g = A.run f ∧ A.queried g = A.queried f := by
  induction A with
  | pure a => exact ⟨rfl, rfl⟩
  | query q κ ih =>
    have hq : f q = g q := h q (by simp)
    have htail : ∀ p ∈ (κ (f q)).queried f, f p = g p := by
      intro p hp
      exact h p (by simp [hp])
    obtain ⟨hrun, hqu⟩ := ih (f q) htail
    refine ⟨?_, ?_⟩
    · show (κ (g q)).run g = (κ (f q)).run f
      rw [← hq]; exact hrun
    · show q :: (κ (g q)).queried g = q :: (κ (f q)).queried f
      rw [← hq, hqu]

/-- **The two-instance template.** If `f` and `g` agree on everything the
algorithm looks at under `f`, and no single answer is valid for both, then the
algorithm is wrong on at least one of them. -/
theorem not_valid_of_agree (A : QueryAlg Q R α) (f g : Q → R)
    (Valid : (Q → R) → α → Prop)
    (hagree : ∀ q ∈ A.queried f, f q = g q)
    (hdisj : ∀ a, ¬ (Valid f a ∧ Valid g a)) :
    ¬ Valid f (A.run f) ∨ ¬ Valid g (A.run g) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  rw [(run_eq_of_agree A f g hagree).1] at h2
  exact hdisj (A.run f) ⟨h1, h2⟩

end QueryAlg

/-! ## A lower bound for End-of-Line

The oracle answers a query `v` with the pair `(succ v, pred v)`. We compare two
instances over `Fin N`: the two-vertex path `0 → 1`, and the four-vertex path
`0 → 1 → a → b`. They differ only at `1`, `a` and `b`, and their (unique)
solutions are `1` and `b` respectively. So an algorithm that gets the short
instance right without querying `1` gets the long one wrong. -/

namespace EOLBound

variable {N : ℕ}

/-- `succ`/`pred` of the path `0 → 1`, everything else isolated. -/
def shortPath (N : ℕ) [NeZero N] (v : Fin N) : Fin N × Fin N :=
  (if v = 0 then 1 else v, if v = 1 then 0 else v)

/-- `succ`/`pred` of the path `0 → 1 → a → b`, everything else isolated. -/
def longPath (N : ℕ) [NeZero N] (a b : Fin N) (v : Fin N) : Fin N × Fin N :=
  (if v = 0 then 1 else if v = 1 then a else if v = a then b else v,
   if v = 1 then 0 else if v = a then 1 else if v = b then a else v)

/-- Being a solution of an `EndOfLine` instance presented as an oracle. -/
def IsSol [NeZero N] (o : Fin N → Fin N × Fin N) (v : Fin N) : Prop :=
  (o (o v).1).2 ≠ v ∨ ((o (o v).2).1 ≠ v ∧ v ≠ 0)

lemma zero_ne_one_fin [NeZero N] (h2 : 2 ≤ N) : (0 : Fin N) ≠ 1 := by
  intro h
  have := congrArg Fin.val h
  simp [Nat.mod_eq_of_lt (by omega : 1 < N)] at this

/-- On the short path the only solution is the endpoint `1`. -/
theorem isSol_shortPath [NeZero N] (h2 : 2 ≤ N) (v : Fin N) :
    IsSol (shortPath N) v ↔ v = 1 := by
  have h01 : (0 : Fin N) ≠ 1 := zero_ne_one_fin h2
  constructor
  · intro hv
    by_contra hne
    rcases eq_or_ne v 0 with rfl | hv0
    · exact absurd hv (by simp [IsSol, shortPath, h01.symm])
    · simp only [IsSol, shortPath, if_neg hv0, if_neg hne] at hv
      rcases hv with h | ⟨h, -⟩ <;> simp [if_neg hv0, if_neg hne] at h
  · rintro rfl
    left
    simp [shortPath, h01.symm, h01]


/-- On the long path, the short path's answer `1` is *not* a solution. -/
theorem not_isSol_longPath [NeZero N] (h2 : 2 ≤ N) {a b : Fin N}
    (ha0 : a ≠ 0) (ha1 : a ≠ 1) : ¬ IsSol (longPath N a b) 1 := by
  have h10 : (1 : Fin N) ≠ 0 := (zero_ne_one_fin h2).symm
  have h1 : longPath N a b 1 = (a, 0) := by
    simp [longPath, h10]
  have hA : (longPath N a b a).2 = 1 := by
    simp [longPath, ha1]
  have hB : (longPath N a b 0).1 = 1 := by
    simp [longPath]
  intro hcon
  simp only [IsSol, h1] at hcon
  rcases hcon with h | ⟨h, -⟩
  · exact h hA
  · exact h hB

/-- The two instances agree away from `1`, `a` and `b`. -/
theorem shortPath_eq_longPath [NeZero N] {a b : Fin N} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    {v : Fin N} (hv1 : v ≠ 1) (hva : v ≠ a) (hvb : v ≠ b) :
    shortPath N v = longPath N a b v := by
  rcases eq_or_ne v 0 with rfl | hv0
  · simp only [shortPath, longPath, if_pos rfl, if_neg hv1, if_neg hva, if_neg hvb]
  · simp only [shortPath, longPath, if_neg hv0, if_neg hv1, if_neg hva, if_neg hvb]

/-- **A correct `EndOfLine` algorithm has to look at the endpoint.**

If `A` is right on the two-vertex path `0 → 1` and on every four-vertex path
`0 → 1 → a → b`, and it leaves two vertices unqueried on the short instance,
then it must have queried `1`. Otherwise the two instances are indistinguishable
to it, yet their solutions differ. -/
theorem eol_must_query_endpoint [NeZero N]
    (A : QueryAlg (Fin N) (Fin N × Fin N) (Fin N))
    (h2 : 2 ≤ N)
    {a b : Fin N} (ha0 : a ≠ 0) (ha1 : a ≠ 1) (hb0 : b ≠ 0) (hb1 : b ≠ 1)
    (hna : a ∉ A.queried (shortPath N)) (hnb : b ∉ A.queried (shortPath N))
    (hshort : IsSol (shortPath N) (A.run (shortPath N)))
    (hlong : IsSol (longPath N a b) (A.run (longPath N a b))) :
    (1 : Fin N) ∈ A.queried (shortPath N) := by
  by_contra h1
  -- The oracles agree everywhere `A` looks.
  have hagree : ∀ q ∈ A.queried (shortPath N), shortPath N q = longPath N a b q := by
    intro q hq
    refine shortPath_eq_longPath ha0 hb0 ?_ ?_ ?_
    · rintro rfl; exact h1 hq
    · rintro rfl; exact hna hq
    · rintro rfl; exact hnb hq
  -- So `A` returns the same point on both, namely `1`.
  have hrun := (A.run_eq_of_agree (shortPath N) (longPath N a b) hagree).1
  have heq : A.run (shortPath N) = 1 := (isSol_shortPath h2 _).mp hshort
  rw [hrun, heq] at hlong
  exact not_isSol_longPath h2 ha0 ha1 hlong

/-- Room to hide: if the algorithm leaves at least two vertices outside
`{0, 1}` unqueried, the hypotheses of `eol_must_query_endpoint` can be met. -/
theorem exists_unqueried [NeZero N] (A : QueryAlg (Fin N) (Fin N × Fin N) (Fin N))
    (hroom : A.queries (shortPath N) + 4 ≤ N) :
    ∃ a b : Fin N, a ≠ b ∧ a ≠ 0 ∧ a ≠ 1 ∧ b ≠ 0 ∧ b ≠ 1 ∧
      a ∉ A.queried (shortPath N) ∧ b ∉ A.queried (shortPath N) := by
  classical
  set S : Finset (Fin N) :=
    (A.queried (shortPath N)).toFinset ∪ {0, 1} with hS
  have hcard : S.card ≤ A.queries (shortPath N) + 2 := by
    refine le_trans (Finset.card_union_le _ _) ?_
    have h1 : (A.queried (shortPath N)).toFinset.card ≤ A.queries (shortPath N) := by
      refine le_trans (List.toFinset_card_le _) ?_
      rw [QueryAlg.length_queried]
    have h2 : ({0, 1} : Finset (Fin N)).card ≤ 2 := Finset.card_insert_le _ _ |>.trans (by simp)
    omega
  have hfree : 2 ≤ (Finset.univ \ S).card := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < (Finset.univ \ S).card)
  rw [Finset.mem_sdiff] at ha hb
  simp only [hS, Finset.mem_union, List.mem_toFinset, Finset.mem_insert,
    Finset.mem_singleton, not_or] at ha hb
  exact ⟨a, b, hab, ha.2.2.1, ha.2.2.2, hb.2.2.1, hb.2.2.2, ha.2.1, hb.2.1⟩

end EOLBound

end Tfnp
