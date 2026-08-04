/-
Copyright (c) 2026 Angus Joshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Angus Joshi
-/
import Tfnp.Tarski.Levelset

/-!
# Query upper bounds for `Tarski(n, d)`

Assembling the pieces: a query bound for the Tarski problem on the cube `[0,n]^d`
for **every** dimension `d`, obtained by splitting the cube into blocks with the
Fearnley–Pálvölgyi–Savani decomposition theorem
(`Tfnp/Tarski/Decomposition.lean`, proved) and solving each block.

Two instantiations, both assembled here:

* **Unconditional.** One-dimensional blocks.  A one-dimensional levelset is a
  *single point*, so Haslebacher–Lill's Lemma 3.2 degenerates to plain binary
  search and gives an `O(log n)` solver for `d = 1` (`dim1Levelset`).  Iterating
  the decomposition over `d` blocks gives `tarski_cube_bound_dim1`, a fully proved
  `O(log^d n)` bound — the Dang–Qi–Ye bound, with no assumptions.

* **Three-dimensional blocks.**  Given a levelset subprocedure for `d = 3` making
  `q₃` queries, blocks of three give `tarski_cube_bound_dim3`:
  `O(log^(2⌈d/3⌉) n)`, matching HL and FPS.  The subprocedure is left as a
  hypothesis *here* only to keep this file independent of the Haslebacher–Lill
  development; `Tfnp/Tarski/BoundHL.lean` discharges it with
  `solvesLevelset_lsInner`, so the bound is unconditional.

The two differ only in the block size fed to the same recursion, which is the
point of the decomposition theorem.

## Budgets

`iterBudget base step m` is the budget after `m` decomposition steps from a base
block; `iterBudget_le` gives the closed form `(base + 2) · (step + 1)^m`.  With
`base, step = O(log n)` and `m = d` this is `O(log^d n)`; with `step = O(log² n)`
and `m = ⌈d/3⌉` it is `O(log^(2⌈d/3⌉) n)`.
-/

namespace Tfnp.Tarski

open QueryAlg (Bounded)

/-! ### The cube `[0, n]^d` -/

/-- The bottom of the cube. -/
def cubeLo (d : ℕ) : Pt d := fun _ => 0

/-- The top of the cube `[0, n]^d`. -/
def cubeHi (d n : ℕ) : Pt d := fun _ => n

lemma cubeLo_le_cubeHi (d n : ℕ) : cubeLo d ≤ cubeHi d n := coord_le fun _ => Nat.zero_le n

@[simp] lemma cat_cubeLo (a b : ℕ) : cat (cubeLo a) (cubeLo b) = cubeLo (a + b) := by
  funext l
  refine Fin.addCases (fun i => ?_) (fun i => ?_) l <;> simp [cubeLo]

@[simp] lemma cat_cubeHi (a b n : ℕ) : cat (cubeHi a n) (cubeHi b n) = cubeHi (a + b) n := by
  funext l
  refine Fin.addCases (fun i => ?_) (fun i => ?_) l <;> simp [cubeHi]

lemma boxSize_le_of_mem_cube {d n : ℕ} {l u : Pt d} (_hl : cubeLo d ≤ l) (hu : u ≤ cubeHi d n) :
    boxSize l u ≤ d * n := by
  calc boxSize l u = ∑ i, (u i - l i) := rfl
    _ ≤ ∑ _i : Fin d, n := Finset.sum_le_sum fun i _ => by
        have := le_coord hu i
        simp only [cubeHi] at this
        omega
    _ = d * n := by simp

/-! ### Dimension 0 -/

/-- Everything in `Pt 0` is equal, so any answer is a solution. -/
theorem solvesMapsTo_dim0 (n : ℕ) :
    SolvesMapsTo (QueryAlg.pure (.inl (cubeLo 0))) (cubeLo 0) (cubeHi 0 n) := by
  intro g _
  exact ⟨mem_Box.mpr ⟨le_rfl, coord_le fun i => i.elim0⟩, funext fun i => i.elim0⟩

/-! ### Dimension 1: a levelset is a single point

In one dimension `lev x = x 0`, so the levelset `{x | lev x = k}` has exactly one
element, and the subprocedure is one query: the point is upward or downward
according to the answer.  Feeding this to HL Lemma 3.2 gives binary search. -/

lemma lev_dim1 (x : Pt 1) : lev x = x 0 := by simp [lev]

/-- The unique point of `Pt 1` at level `k`. -/
def pt1 (k : ℕ) : Pt 1 := fun _ => k

@[simp] lemma pt1_apply (k : ℕ) (i : Fin 1) : pt1 k i = k := rfl

@[simp] lemma lev_pt1 (k : ℕ) : lev (pt1 k) = k := by rw [lev_dim1]; rfl

/-- The one-dimensional levelset subprocedure: query the unique point at level `k`
and read off whether it is upward or downward. -/
noncomputable def dim1Levelset (_lo _hi : Pt 1) (k : ℕ) :
    QueryAlg (Pt 1) (Pt 1) (InnerAnswer 1) :=
  QueryAlg.ask (pt1 k) >>= fun fp =>
    if k ≤ fp 0 then QueryAlg.pure (.up (pt1 k)) else QueryAlg.pure (.down (pt1 k))

lemma dim1Levelset_bounded (_lo _hi : Pt 1) (k : ℕ) : Bounded 1 (dim1Levelset _lo _hi k) := by
  refine Bounded.mono (n := 1 + 0) ((Bounded.ask _).bind fun fp => ?_) (by omega)
  split <;> exact Bounded.pure' _ _

/-- In one dimension every point is upward or downward, so one query solves the
levelset. -/
theorem solvesLevelset_dim1 (LO HI : Pt 1) : SolvesLevelset dim1Levelset LO HI := by
  intro F lo hi k _ hlohi _ _ _ hklo hkhi
  -- the unique point at level `k` lies in the box
  have hmem : pt1 k ∈ Box lo hi := by
    rw [lev_dim1] at hklo hkhi
    refine mem_Box.mpr ⟨coord_le fun i => ?_, coord_le fun i => ?_⟩
    · rw [Subsingleton.elim i 0]; simpa using hklo
    · rw [Subsingleton.elim i 0]; simpa using hkhi
  change IsLevelsetSol F lo hi k ((QueryAlg.ask (pt1 k) >>= _).run F)
  rw [QueryAlg.run_bind, QueryAlg.run_ask]
  by_cases h : k ≤ F (pt1 k) 0
  · rw [if_pos h]
    refine ⟨hmem, by rw [lev_pt1], mem_Up.mpr (coord_le fun i => ?_)⟩
    rw [Subsingleton.elim i 0]
    simpa using h
  · rw [if_neg h]
    refine ⟨hmem, by rw [lev_pt1], mem_Down.mpr (coord_le fun i => ?_)⟩
    rw [Subsingleton.elim i 0]
    simp only [pt1_apply]
    omega

/-- The one-dimensional solver: `⌈log₂ n⌉` halvings of one query each, plus the
two-query terminal step. -/
noncomputable def dim1Solver (n : ℕ) : Pt 1 → Pt 1 → QueryAlg (Pt 1) (Pt 1) (Answer 1) :=
  levelsetSolver dim1Levelset (Nat.clog 2 (1 * n))

theorem dim1Solver_solvesUpDown (n : ℕ) :
    SolvesUpDown (dim1Solver n) (cubeLo 1) (cubeHi 1 n) :=
  solvesUpDown_levelsetSolver (solvesLevelset_dim1 _ _)
    (fun _ _ hl _ hu => Nat.clog_mono_right 2 (boxSize_le_of_mem_cube hl hu))

theorem dim1Solver_bounded (n : ℕ) (l u : Pt 1) :
    Bounded (Nat.clog 2 (1 * n) * 1 + 2) (dim1Solver n l u) :=
  levelsetSolver_bounded dim1Levelset_bounded _ l u

/-! ### The decomposition step

Splitting off a block: if the cube of dimension `e` is solvable and there is a
`SolvesUpDown` family for the cube of dimension `c`, then the cube of dimension
`e + c` is solvable.  This is `decompAlg` with the boxes recognised as cubes. -/

theorem solvesMapsTo_cat {e c n : ℕ}
    {algA : QueryAlg (Pt e) (Pt e) (Answer e)}
    {algB : Pt c → Pt c → QueryAlg (Pt c) (Pt c) (Answer c)}
    (hA : SolvesMapsTo algA (cubeLo e) (cubeHi e n))
    (hB : SolvesUpDown algB (cubeLo c) (cubeHi c n)) :
    SolvesMapsTo (decompAlg algA algB (cubeLo e) (cubeHi e n) (cubeLo c) (cubeHi c n))
      (cubeLo (e + c)) (cubeHi (e + c) n) := by
  have h := decompAlg_isSol hA hB (cubeLo_le_cubeHi e n) (cubeLo_le_cubeHi c n)
  rwa [cat_cubeLo, cat_cubeHi] at h

theorem bounded_cat {e c qa qb : ℕ} {loA hiA : Pt e} {loB hiB : Pt c}
    {algA : QueryAlg (Pt e) (Pt e) (Answer e)}
    {algB : Pt c → Pt c → QueryAlg (Pt c) (Pt c) (Answer c)}
    (hAq : Bounded qa algA) (hBq : ∀ l u, Bounded qb (algB l u)) :
    Bounded ((qa + 2) * (qb + 3)) (decompAlg algA algB loA hiA loB hiB) :=
  decompAlg_bounded hAq hBq

/-! ### Iterated budgets -/

/-- The budget after `m` decomposition steps from a base block. -/
def iterBudget (base step : ℕ) : ℕ → ℕ
  | 0 => base
  | m + 1 => (iterBudget base step m + 2) * step

/-- Closed form: `iterBudget base step m + 2 ≤ (base + 2) · (step + 1)^m`.  With
`base, step = O(log n)` this reads `O(log^m n)`. -/
theorem iterBudget_le (base step : ℕ) :
    ∀ m : ℕ, iterBudget base step m + 2 ≤ (base + 2) * (step + 1) ^ m := by
  intro m
  induction m with
  | zero => simp [iterBudget]
  | succ m ih =>
    have h1 : 1 ≤ (step + 1) ^ m := Nat.one_le_pow _ _ (by omega)
    set X := (base + 2) * (step + 1) ^ m with hX
    have hpos : 2 ≤ X := by
      have hle : (base + 2) * 1 ≤ X := by rw [hX]; exact Nat.mul_le_mul_left _ h1
      rw [Nat.mul_one] at hle
      omega
    have hstep : iterBudget base step (m + 1) = (iterBudget base step m + 2) * step := rfl
    have hmul : (iterBudget base step m + 2) * step ≤ X * step := Nat.mul_le_mul_right _ ih
    have hrhs : (base + 2) * (step + 1) ^ (m + 1) = X * step + X := by
      rw [hX, pow_succ, ← Nat.mul_assoc, Nat.mul_add, Nat.mul_one]
    omega

/-! ### The block dimension

`b + c * (m + 1)` is *not* definitionally `(b + c * m) + c` when `c` is a
variable: `Nat.add` recurses on its second argument, so `x + (y + c)` is stuck.
Indexing the recursion by `dimOf` — whose successor equation holds by `rfl` —
avoids any transport between `Pt`-types; `dimOf_eq` recovers the closed form. -/

/-- The dimension after `m` blocks of size `c` on top of a base of size `b`. -/
def dimOf (b c : ℕ) : ℕ → ℕ
  | 0 => b
  | m + 1 => dimOf b c m + c

@[simp] lemma dimOf_zero (b c : ℕ) : dimOf b c 0 = b := rfl

@[simp] lemma dimOf_succ (b c m : ℕ) : dimOf b c (m + 1) = dimOf b c m + c := rfl

lemma dimOf_eq (b c : ℕ) : ∀ m, dimOf b c m = b + c * m := by
  intro m
  induction m with
  | zero => simp
  | succ m ih => rw [dimOf_succ, ih, Nat.mul_succ]; omega

/-! ### The recursion

`b + 3 * (m + 1)` is *definitionally* `(b + 3 * m) + 3`, since `Nat.mul` and
`Nat.add` both recurse on their second argument.  So the induction below needs no
transport between `Pt (b + 3 * (m+1))` and `Pt ((b + 3 * m) + 3)`. -/

/-- Iterating the decomposition with blocks of size `c`: from a solver for
dimension `b`, get one for dimension `dimOf b c m = b + c * m`. -/
theorem exists_cube_solver (n c : ℕ)
    {algB : Pt c → Pt c → QueryAlg (Pt c) (Pt c) (Answer c)} {qb : ℕ}
    (hB : SolvesUpDown algB (cubeLo c) (cubeHi c n))
    (hBq : ∀ l u, Bounded qb (algB l u))
    (b : ℕ) {algBase : QueryAlg (Pt b) (Pt b) (Answer b)} {qbase : ℕ}
    (hBase : SolvesMapsTo algBase (cubeLo b) (cubeHi b n))
    (hBaseq : Bounded qbase algBase) :
    ∀ m : ℕ, ∃ alg : QueryAlg (Pt (dimOf b c m)) (Pt (dimOf b c m)) (Answer (dimOf b c m)),
      SolvesMapsTo alg (cubeLo (dimOf b c m)) (cubeHi (dimOf b c m) n)
        ∧ Bounded (iterBudget qbase (qb + 3) m) alg := by
  intro m
  induction m with
  | zero => exact ⟨algBase, hBase, hBaseq⟩
  | succ m ih =>
    obtain ⟨alg, hsol, hbd⟩ := ih
    exact ⟨decompAlg alg algB (cubeLo (dimOf b c m)) (cubeHi (dimOf b c m) n)
      (cubeLo c) (cubeHi c n), solvesMapsTo_cat hsol hB, bounded_cat hbd hBq⟩

/-! ### The unconditional bound: one-dimensional blocks -/

/-- **A fully proved query upper bound for `Tarski(n, d)`.**  Decomposing the cube
into `d` one-dimensional blocks, each solved by binary search, gives

`(⌈log₂ n⌉ + 4) · (⌈log₂ n⌉ + 6)^d`

queries (`iterBudget_le` puts the recursive budget in that closed form), i.e.
`O(log^d n)` — the Dang–Qi–Ye bound.  Nothing here is assumed.

Note the dimension is presented as `b + 1 * m`; take `b = 0`, `m = d`. -/
theorem tarski_cube_bound_dim1 (n : ℕ) :
    ∀ d : ℕ, ∃ alg : QueryAlg (Pt (dimOf 0 1 d)) (Pt (dimOf 0 1 d)) (Answer (dimOf 0 1 d)),
      SolvesMapsTo alg (cubeLo (dimOf 0 1 d)) (cubeHi (dimOf 0 1 d) n)
        ∧ Bounded (iterBudget 0 (Nat.clog 2 (1 * n) * 1 + 2 + 3) d) alg :=
  exists_cube_solver n 1 (dim1Solver_solvesUpDown n) (dim1Solver_bounded n) 0
    (solvesMapsTo_dim0 n) Bounded.pure

/-! ### The Haslebacher–Lill bound: three-dimensional blocks

Given a levelset subprocedure for `d = 3` — HL §3.1–3.4, proved in
`Tfnp/Tarski/Levelset*.lean` and plugged in by `Tfnp/Tarski/BoundHL.lean` — blocks
of three give `O(log^(2⌈d/3⌉) n)`.

The hypothesis is exactly `SolvesLevelset`: a procedure that, on a box and a level
`k`, returns an upward point at level `≥ k`, a downward point at level `≤ k`, or a
violation of order preservation.  HL achieve `q₃ = O(log n)`, whence
`levelsetSolver` gives `O(log² n)` for `d = 3` and this theorem gives
`O(log^(2⌈d/3⌉) n)` overall. -/
theorem tarski_cube_bound_dim3 (n : ℕ)
    {ls3 : Pt 3 → Pt 3 → ℕ → QueryAlg (Pt 3) (Pt 3) (InnerAnswer 3)} {q3 : ℕ}
    (hls3 : SolvesLevelset ls3 (cubeLo 3) (cubeHi 3 n))
    (hq3 : ∀ lo hi k, Bounded q3 (ls3 lo hi k))
    (b : ℕ) {algBase : QueryAlg (Pt b) (Pt b) (Answer b)} {qbase : ℕ}
    (hBase : SolvesMapsTo algBase (cubeLo b) (cubeHi b n))
    (hBaseq : Bounded qbase algBase) :
    ∀ m : ℕ, ∃ alg : QueryAlg (Pt (dimOf b 3 m)) (Pt (dimOf b 3 m)) (Answer (dimOf b 3 m)),
      SolvesMapsTo alg (cubeLo (dimOf b 3 m)) (cubeHi (dimOf b 3 m) n)
        ∧ Bounded (iterBudget qbase
            (Nat.clog 2 (3 * n) * q3 + 2 + 3) m) alg :=
  exists_cube_solver n 3
    (solvesUpDown_levelsetSolver hls3
      (fun _ _ hl _ hu => Nat.clog_mono_right 2 (boxSize_le_of_mem_cube hl hu)))
    (levelsetSolver_bounded hq3 _) b hBase hBaseq

/-- The three residues, so that `tarski_cube_bound_dim3` covers every dimension:
`d = b + 3 * m` with `b = d % 3` and `m = d / 3`.  Dimension `0` is trivial,
dimension `1` is binary search, and dimension `2` is two one-dimensional blocks
through the decomposition theorem. -/
theorem exists_base_solver (n : ℕ) :
    ∀ b : ℕ, b < 3 → ∃ (alg : QueryAlg (Pt b) (Pt b) (Answer b)) (q : ℕ),
      SolvesMapsTo alg (cubeLo b) (cubeHi b n) ∧ Bounded q alg := by
  intro b hb
  match b with
  | 0 => exact ⟨_, 0, solvesMapsTo_dim0 n, Bounded.pure⟩
  | 1 =>
    exact ⟨dim1Solver n (cubeLo 1) (cubeHi 1 n), _,
      (dim1Solver_solvesUpDown n).solvesMapsTo (cubeLo_le_cubeHi 1 n),
      dim1Solver_bounded n _ _⟩
  | 2 =>
    obtain ⟨alg, hsol, hbd⟩ := tarski_cube_bound_dim1 n 2
    exact ⟨alg, _, hsol, hbd⟩
  | (r + 3) => exact absurd hb (by omega)

end Tfnp.Tarski
