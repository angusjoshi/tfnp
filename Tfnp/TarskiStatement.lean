/-
Copyright (c) 2026 Angus Joshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Angus Joshi
-/

namespace Tfnp.TarskiStatement

inductive QueryAlg (Q R α : Type) : Type
  | pure (a : α) : QueryAlg Q R α
  | query (q : Q) (κ : R → QueryAlg Q R α) : QueryAlg Q R α

def QueryAlg.run {Q R α : Type} (f : Q → R) : QueryAlg Q R α → α
  | .pure a => a
  | .query q κ => run f (κ (f q))

abbrev Grid (N d : Nat) : Type := Fin d → Fin (N + 1)

variable {N d : Nat}

def Grid.le (x y : Grid N d) : Prop := ∀ i, (x i).val ≤ (y i).val

def IsMonotone (f : Grid N d → Grid N d) : Prop :=
  ∀ x y, Grid.le x y → Grid.le (f x) (f y)

/-! ### Basic `Fin` and `Grid` facts -/

theorem fin_eq {n : Nat} {a b : Fin n} (h : a.val = b.val) : a = b := by
  cases a; cases b; cases h; rfl

theorem fin_le {n : Nat} (a : Fin (n + 1)) : a.val ≤ n :=
  Nat.le_of_lt_succ a.isLt

/-- The all-zeroes point, the least element of the grid. -/
def bot (N d : Nat) : Grid N d := fun _ => ⟨0, Nat.zero_lt_succ N⟩

theorem bot_le (x : Grid N d) : Grid.le (bot N d) x := by
  intro i
  exact Nat.zero_le _

/-- If two grid points are comparable but distinct, they differ strictly somewhere. -/
theorem exists_lt_of_ne {x y : Grid N d} (hle : Grid.le x y) (hne : x ≠ y) :
    ∃ i : Fin d, (x i).val < (y i).val := by
  apply Classical.byContradiction
  intro hc
  apply hne
  funext i
  apply fin_eq
  have h1 : ¬ (x i).val < (y i).val := fun h => hc ⟨i, h⟩
  have h2 : (x i).val ≤ (y i).val := hle i
  omega

/-! ### A potential function on the grid

The sum of the coordinates.  It is bounded by `d * N`, is monotone, and increases
strictly along a strict increase in the grid order. -/

def sumUpto : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | n + 1, g => g n + sumUpto n g

theorem sumUpto_mono {g h : Nat → Nat} (hgh : ∀ i, g i ≤ h i) :
    ∀ n, sumUpto n g ≤ sumUpto n h := by
  intro n
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih =>
      simp only [sumUpto]
      exact Nat.add_le_add (hgh n) ih

theorem sumUpto_lt {g h : Nat → Nat} (hgh : ∀ i, g i ≤ h i) :
    ∀ (n j : Nat), j < n → g j < h j → sumUpto n g < sumUpto n h := by
  intro n
  induction n with
  | zero => intro j hj; exact absurd hj (Nat.not_lt_zero j)
  | succ n ih =>
      intro j hj hlt
      have hs : sumUpto n g ≤ sumUpto n h := sumUpto_mono hgh n
      have hn : g n ≤ h n := hgh n
      simp only [sumUpto]
      rcases Nat.lt_or_ge j n with h1 | h1
      · have h2 := ih j h1 hlt
        omega
      · have h2 : j = n := by omega
        subst h2
        omega

theorem sumUpto_bound {g : Nat → Nat} {c : Nat} (hg : ∀ i, g i ≤ c) :
    ∀ n, sumUpto n g ≤ n * c := by
  intro n
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
      have hn := hg n
      have hm : (n + 1) * c = n * c + c := Nat.succ_mul n c
      simp only [sumUpto]
      omega

/-- The `i`-th coordinate of `x`, as a natural number (junk value `0` out of range). -/
def coord (x : Grid N d) (i : Nat) : Nat := if h : i < d then (x ⟨i, h⟩).val else 0

theorem coord_le (x : Grid N d) (i : Nat) : coord x i ≤ N := by
  by_cases hi : i < d
  · simp only [coord, dif_pos hi]
    exact fin_le _
  · simp only [coord, dif_neg hi]
    exact Nat.zero_le N

theorem coord_mono {x y : Grid N d} (h : Grid.le x y) (i : Nat) : coord x i ≤ coord y i := by
  by_cases hi : i < d
  · simp only [coord, dif_pos hi]
    exact h ⟨i, hi⟩
  · simp only [coord, dif_neg hi]
    exact Nat.le_refl 0

/-- The sum of the coordinates of a grid point. -/
def pot (x : Grid N d) : Nat := sumUpto d (coord x)

theorem pot_le (x : Grid N d) : pot x ≤ d * N := by
  unfold pot
  exact sumUpto_bound (coord_le x) d

theorem pot_lt {x y : Grid N d} (hle : Grid.le x y) (hne : x ≠ y) : pot x < pot y := by
  obtain ⟨i, hi⟩ := exists_lt_of_ne hle hne
  unfold pot
  apply sumUpto_lt (coord_mono hle) d i.val i.isLt
  simp only [coord, dif_pos i.isLt]
  exact hi

/-! ### Iterating from the bottom

The algorithm is the decision tree that queries `f` at `⊥`, then at the answer, and so
on, `d * N + 1` times, returning the last answer. -/

def iter (f : Grid N d → Grid N d) : Nat → Grid N d → Grid N d
  | 0, x => x
  | n + 1, x => iter f n (f x)

theorem iter_succ (f : Grid N d → Grid N d) :
    ∀ (n : Nat) (x : Grid N d), iter f (n + 1) x = f (iter f n x) := by
  intro n
  induction n with
  | zero => intro x; rfl
  | succ n ih =>
      intro x
      have h := ih (f x)
      simp only [iter] at h ⊢
      exact h

/-- The decision tree following the orbit of `x` under `f` for `n` steps. -/
def chain : Nat → Grid N d → QueryAlg (Grid N d) (Grid N d) (Grid N d)
  | 0, x => .pure x
  | n + 1, x => .query x (fun y => chain n y)

theorem chain_run (f : Grid N d → Grid N d) :
    ∀ (n : Nat) (x : Grid N d), (chain n x).run f = iter f n x := by
  intro n
  induction n with
  | zero => intro x; rfl
  | succ n ih =>
      intro x
      simp only [chain, QueryAlg.run]
      exact ih (f x)

/-- The orbit of `⊥` is increasing, since `f` is monotone and `⊥ ≤ f ⊥`. -/
theorem le_iter_succ (f : Grid N d → Grid N d) (hf : IsMonotone f) :
    ∀ n : Nat, Grid.le (iter f n (bot N d)) (iter f (n + 1) (bot N d)) := by
  intro n
  induction n with
  | zero => exact bot_le _
  | succ n ih =>
      have h1 := iter_succ f n (bot N d)
      have h2 := iter_succ f (n + 1) (bot N d)
      rw [h1] at ih
      rw [h2, h1]
      exact hf _ _ ih

/-- Once the orbit stalls it stays put, so a fixed point at step `k` is one at step `k + 1`. -/
theorem fix_succ (f : Grid N d → Grid N d) (k : Nat)
    (h : f (iter f k (bot N d)) = iter f k (bot N d)) :
    f (iter f (k + 1) (bot N d)) = iter f (k + 1) (bot N d) := by
  rw [iter_succ f k, h]
  exact h

/-- Either the orbit of `⊥` has already reached a fixed point after `k` steps, or the
potential has increased at every one of those `k` steps. -/
theorem fix_or_pot (f : Grid N d → Grid N d) (hf : IsMonotone f) :
    ∀ k : Nat, f (iter f k (bot N d)) = iter f k (bot N d) ∨ k ≤ pot (iter f k (bot N d)) := by
  intro k
  induction k with
  | zero => exact Or.inr (Nat.zero_le _)
  | succ k ih =>
      rcases ih with hfix | hpot
      · exact Or.inl (fix_succ f k hfix)
      · rcases Classical.em (iter f (k + 1) (bot N d) = iter f k (bot N d)) with heq | hne
        · rw [iter_succ f k] at heq
          exact Or.inl (fix_succ f k heq)
        · refine Or.inr ?_
          have hlt := pot_lt (le_iter_succ f hf k) (fun h => hne h.symm)
          omega

theorem exists_tarski_query_algorithm (N d : Nat) :
    ∃ alg : QueryAlg (Grid N d) (Grid N d) (Grid N d),
      ∀ f : Grid N d → Grid N d, IsMonotone f → f (alg.run f) = alg.run f := by
  refine ⟨chain (d * N + 1) (bot N d), fun f hf => ?_⟩
  rw [chain_run]
  rcases fix_or_pot f hf (d * N + 1) with h | h
  · exact h
  · exact absurd (Nat.le_trans h (pot_le _)) (Nat.not_succ_le_self _)

end Tfnp.TarskiStatement
