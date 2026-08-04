/-
Copyright (c) 2026 Angus Joshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Angus Joshi
-/
import Tfnp.Tarski.Star
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Fintype.Card

/-!
# Monotone partial-information functions and candidate sets (CLY26)

The framework of Sections 2–3 of

> Xi Chen, Yuhao Li, Mihalis Yannakakis.
> *The Mystery Deepens: On the Query Complexity of Tarski Fixed Points.*
> [arXiv:2604.00268](https://arxiv.org/abs/2604.00268)

After `t` queries an algorithm for `Tarski*` knows the answers `g(q¹), …, g(qᵗ)`
together with everything monotonicity lets it infer.  CLY26 package that as a
*monotone partial-information function* `p`, whose value at each point and
coordinate lies in `{-1, 0, 1, ≤, ≥, ⋄}`, and then measure progress not by the set
of points that could still be solutions — which a single query need not shrink at
all — but by a **candidate set**:

> `S ⊆ [n]^k` is a candidate set of `p` if every monotone `g` consistent with `p`
> has at least one `Tarski*` solution in `S`.

CLY26's two objectives are then: construct a candidate set for every `p`
(Objective 1), and show some query always shrinks it by a constant factor
(Objective 2).  Their §2 remark that this gives an `O(k log n)`-query algorithm is
`queries_le_of_halving` below, proved.

## Main definitions

* `Sign`, `PIVal`, `PIVal.Allows` — the value domains of CLY26 §3.1–3.2 and the
  consistency relation between them.
* `PIFun`, `PIFun.Consistent` — monotone partial-information functions and what it
  means for a sign function to be consistent with one.
* `IsCandidateSet` — the definition above, stated for an arbitrary set of
  still-possible instances (which is what a `p` denotes).
* `SafeOn` — the promise of CLY23's *safe* functions: a unique fixed point in
  every slice.  CLY26's contribution is to use *partial* information functions with
  this promise ("safe PI functions") to drive an algorithm directly.

## Main results

* `isCandidateSet_univ` — the whole box is always a candidate set (this is
  `Tarski*` totality), so Objective 1 is satisfiable, trivially and uselessly:
  CLY26's difficulty is meeting both objectives at once.
* `nonempty_of_isCandidateSet` — a candidate set of a *satisfiable* partial
  information is non-empty.  This is the invariant that makes the shrinking
  argument terminate in a solution rather than in a contradiction.
* `queries_le_of_halving` — if a candidate set is non-empty throughout and at least
  halves at each query, the number of queries is at most `log₂` of its initial
  size, i.e. `O(k log n)` when it starts at `n^k`.
-/

namespace Tfnp.Tarski

variable {k : ℕ}

/-! ### Sign values -/

/-- The value of a monotone sign function in one coordinate (CLY26 §3.1):
`g(x)_i = sgn(f(x)_i - x_i)`. -/
inductive Sign : Type
  /-- `f` strictly decreases the coordinate. -/
  | neg : Sign
  /-- `f` fixes the coordinate. -/
  | zero : Sign
  /-- `f` strictly increases the coordinate. -/
  | pos : Sign
  deriving DecidableEq, Repr

namespace Sign

/-- Numerical value, used to order signs. -/
def toInt : Sign → ℤ
  | .neg => -1
  | .zero => 0
  | .pos => 1

instance : LE Sign := ⟨fun a b => a.toInt ≤ b.toInt⟩

end Sign

/-- The sign function attached to a map `f`, coordinatewise. -/
def signOf (f : Pt k → Pt k) (x : Pt k) (i : Fin k) : Sign :=
  if f x i < x i then .neg else if x i < f x i then .pos else .zero

/-! ### Partial information -/

/-- The information an algorithm may hold about one coordinate of a monotone sign
function (CLY26 §3.2): an exact value, a one-sided bound (`≥` meaning "in
`{0, 1}`", `≤` meaning "in `{-1, 0}`"), or nothing at all (`⋄`). -/
inductive PIVal : Type
  /-- The value is known exactly. -/
  | exact (s : Sign) : PIVal
  /-- CLY26's `≥`: the value is `0` or `+1`. -/
  | atLeastZero : PIVal
  /-- CLY26's `≤`: the value is `-1` or `0`. -/
  | atMostZero : PIVal
  /-- CLY26's `⋄`: nothing is known. -/
  | unknown : PIVal
  deriving DecidableEq, Repr

/-- Which sign values a piece of partial information permits. -/
def PIVal.Allows : PIVal → Sign → Prop
  | .exact s, t => t = s
  | .atLeastZero, t => t = .zero ∨ t = .pos
  | .atMostZero, t => t = .neg ∨ t = .zero
  | .unknown, _ => True

@[simp] lemma PIVal.allows_unknown (t : Sign) : PIVal.unknown.Allows t := trivial

/-- `⋄` permits everything, so it is the least informative value. -/
lemma PIVal.exists_allows (v : PIVal) : ∃ t, v.Allows t := by
  cases v with
  | exact s => exact ⟨s, rfl⟩
  | atLeastZero => exact ⟨.zero, Or.inl rfl⟩
  | atMostZero => exact ⟨.zero, Or.inr rfl⟩
  | unknown => exact ⟨.zero, trivial⟩

/-- A **monotone partial-information function** on the box `Box lo hi`: for each
point, partial information about each of the `k` sign coordinates, together with
partial information (`some`/`none`) about the `(k+1)`-st sign coordinate. -/
structure PIFun (k : ℕ) : Type where
  /-- Partial information about the `k` sign coordinates. -/
  coord : Pt k → Fin k → PIVal
  /-- Partial information about the `(k+1)`-st coordinate; `none` is `⋄`. -/
  sign : Pt k → Option Bool

/-- The `Tarski*` instances consistent with a partial-information function: those
whose sign function and `(k+1)`-st coordinate respect everything `p` records. -/
def PIFun.Consistent {lo hi : Pt k} (p : PIFun k) (T : StarInstance k lo hi) : Prop :=
  (∀ x ∈ Box lo hi, ∀ i, (p.coord x i).Allows (signOf T.val x i))
    ∧ ∀ x ∈ Box lo hi, ∀ s, p.sign x = some s → T.sgn x = s

/-! ### Candidate sets

CLY26's definition, stated for the set of still-possible instances rather than for
a syntactic `p`; `PIFun.Consistent p` is the instantiation that a partial
information function denotes. -/

/-- **CLY26's candidate set.**  `S` is a candidate set for the collection `P` of
still-possible instances if every one of them has a `Tarski*` solution in `S`. -/
def IsCandidateSet {lo hi : Pt k} (P : Set (StarInstance k lo hi)) (S : Set (Pt k)) : Prop :=
  ∀ T ∈ P, ∃ x ∈ S, T.IsStarSol x

/-- The whole space is always a candidate set — this is exactly totality of
`Tarski*`.  CLY26 note that this trivially meets their Objective 1 while failing
Objective 2 completely; the difficulty is meeting both at once. -/
theorem isCandidateSet_univ {lo hi : Pt k} (P : Set (StarInstance k lo hi)) :
    IsCandidateSet P Set.univ := by
  intro T _
  obtain ⟨x, hx⟩ := T.exists_sol
  exact ⟨x, Set.mem_univ x, hx⟩

/-- Candidate sets shrink with the collection of possible instances: learning more
can only help. -/
theorem IsCandidateSet.mono {lo hi : Pt k} {P Q : Set (StarInstance k lo hi)}
    {S : Set (Pt k)} (hPQ : Q ⊆ P) (h : IsCandidateSet P S) : IsCandidateSet Q S :=
  fun T hT => h T (hPQ hT)

/-- **A candidate set of a satisfiable partial information is non-empty.**  This is
the invariant that makes CLY26's shrinking argument terminate: the candidate set
can never become empty, so once it is a singleton its element is a solution. -/
theorem nonempty_of_isCandidateSet {lo hi : Pt k} {P : Set (StarInstance k lo hi)}
    {S : Set (Pt k)} (hP : P.Nonempty) (h : IsCandidateSet P S) : S.Nonempty := by
  obtain ⟨T, hT⟩ := hP
  obtain ⟨x, hxS, _⟩ := h T hT
  exact ⟨x, hxS⟩

/-! ### Safe functions (CLY23)

The promise CLY23 introduced, and which CLY26 impose on *partial* information
functions to obtain their algorithm: a unique fixed point in every slice of the
grid.  A slice is obtained by freezing a subset `F` of the coordinates. -/

/-- `x` is a fixed point of `f` *within the slice that freezes `F`*: `f` fixes
every coordinate outside `F`. -/
def FixedOffSet (f : Pt k → Pt k) (F : Finset (Fin k)) (x : Pt k) : Prop :=
  ∀ i ∉ F, f x i = x i

/-- **Safe functions** (CLY23): `f` has a *unique* fixed point in every slice of
the box.  Given an algorithm for safe functions, CLY23 reduce the general problem
to it at no extra query cost; CLY26's advance is to apply the same notion to
partial information functions and design algorithms directly. -/
def SafeOn (f : Pt k → Pt k) (lo hi : Pt k) : Prop :=
  ∀ (F : Finset (Fin k)) (z : Pt k), z ∈ Box lo hi →
    ∃! x, x ∈ Box lo hi ∧ (∀ i ∈ F, x i = z i) ∧ FixedOffSet f F x

/-- On the full slice (`F = ∅`), safety says the function has a unique fixed point
in the box. -/
theorem SafeOn.unique_fixedPoint {f : Pt k → Pt k} {lo hi : Pt k} (h : SafeOn f lo hi)
    (hlohi : lo ≤ hi) :
    ∃! x, x ∈ Box lo hi ∧ f x = x := by
  obtain ⟨x, ⟨hxbox, _, hxfix⟩, huniq⟩ := h ∅ lo (mem_Box_self_left hlohi)
  refine ⟨x, ⟨hxbox, funext fun i => hxfix i (by simp)⟩, ?_⟩
  rintro y ⟨hybox, hyfix⟩
  exact huniq y ⟨hybox, by simp, fun i _ => congrFun hyfix i⟩

/-! ### Why candidate sets give an algorithm

CLY26 §2.1: "This follows from the two facts that (1) `Cand(p)` at the beginning is
at most `n^k` and (2) it can never become empty."  Made precise: -/

/-- If a quantity is positive throughout and at least halves at each of `T` steps,
then it started at at least `2^T`. -/
theorem pow_le_of_halving :
    ∀ (T : ℕ) (s : ℕ → ℕ), (∀ t ≤ T, 1 ≤ s t) → (∀ t < T, 2 * s (t + 1) ≤ s t) →
      2 ^ T ≤ s 0 := by
  intro T
  induction T with
  | zero => intro s hpos _; simpa using hpos 0 le_rfl
  | succ T ih =>
    intro s hpos hhalf
    -- Apply the induction hypothesis to the shifted sequence `t ↦ s (t + 1)`.
    have hshift : 2 ^ T ≤ s 1 :=
      ih (fun t => s (t + 1)) (fun t ht => hpos (t + 1) (by omega))
        (fun t ht => hhalf (t + 1) (by omega))
    have h0 : 2 * s 1 ≤ s 0 := hhalf 0 (by omega)
    have hp : (2 : ℕ) ^ (T + 1) = 2 ^ T * 2 := pow_succ 2 T
    omega

/-- **The query bound from a halving candidate set.**  If the candidate set stays
non-empty and at least halves at every query, the algorithm makes at most
`log₂ |Cand₀|` queries.  Since the candidate set starts inside `[0,n]^k` its size
is at most `(n+1)^k`, so this is `k · log₂ (n+1)` — CLY26's `O(k log n)`. -/
theorem queries_le_of_halving {s : ℕ → ℕ} {T : ℕ} (hpos : ∀ t ≤ T, 1 ≤ s t)
    (hhalf : ∀ t < T, 2 * s (t + 1) ≤ s t) : T ≤ Nat.log 2 (s 0) :=
  Nat.le_log_of_pow_le (by norm_num) (pow_le_of_halving T s hpos hhalf)

end Tfnp.Tarski
