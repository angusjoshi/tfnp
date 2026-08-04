/-
Copyright (c) 2026 Angus Joshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Angus Joshi
-/
import Tfnp.Tarski.History
import Tfnp.Tarski.Simulation

/-!
# The Fearnley–Pálvölgyi–Savani decomposition theorem

> **FPS Theorem 18.**  If `a`-dimensional Tarski can be solved in `qₐ` queries and
> `b`-dimensional Tarski can be solved in `q_b` queries, then `(a+b)`-dimensional
> Tarski can be solved in `qₐ · (q_b + 2)` queries.

(FPS write the conclusion for "`(a·b)`-dimensional" Tarski, but their proof — and
the use they make of it in their Theorem 19 — is for `a + b = k`; the `a · b` is a
slip.)

## What is formalised

`decompAlg` is the algorithm; `decompAlg_isSol` and `decompAlg_bounded` are its
correctness and query bound.  Three points of divergence from the paper, all
recorded in the statements rather than swept under the rug:

1. **The proved bound is `(qₐ + 2)(q_b + 3)`, not `qₐ(q_b + 2)`.**  Each simulated
   query costs two probes (to check `l ∈ Up` and `u ∈ Down`, FPS Lemma 17), the
   `q_b` queries of the inner algorithm, and one further probe to read off the
   response to the outer algorithm: the inner algorithm returns a slice fixed
   point `y` but is not obliged to have queried it, so `f (x, y)` must be asked
   for.  That is `q_b + 3` per step.  Same asymptotics, honest constant.

2. **The returned points are re-probed.**  FPS translate the outer algorithm's
   answer using the `y` recorded for it, but the outer algorithm is entitled to
   return a point it never queried, for which no `y` is on record.  `finalize`
   therefore runs one more simulated step at each returned point; that is the
   `+2` in `qₐ + 2`.

3. **Outer queries are clamped into the box.**  Nothing stops the outer algorithm
   from querying outside its own lattice, and a recorded key outside the box would
   break the invariant that returned witnesses lie in the box.  `step` therefore
   clamps, which is invisible on the box where correctness is asserted.

## The two solver interfaces

Which precondition a sub-algorithm needs is what makes the theorem compose:

* `SolvesMapsTo` — correct whenever the oracle maps the box into itself.  This is
  what the *outer* factor needs, and what the theorem *produces*.
* `SolvesUpDown` — correct on every sub-box whose endpoints lie in the up and down
  sets.  This is FPS Lemma 4's interface, hence the interface of the FPS outer
  algorithm; it is what the *inner* factor needs.

`SolvesUpDown.solvesMapsTo` shows the second implies the first, so iterating the
theorem along `k = (k-3) + 3` — inner factor always the fixed 3-dimensional
algorithm — is exactly FPS Theorem 19.
-/

namespace Tfnp.Tarski

open QueryAlg (Bounded)

variable {a b : ℕ}

/-! ### Clamping -/

/-- Clamp a point into a box, coordinatewise. -/
def clamp {k : ℕ} (lo hi : Pt k) (x : Pt k) : Pt k := fun i => max (lo i) (min (hi i) (x i))

lemma clamp_mem {k : ℕ} {lo hi : Pt k} (h : lo ≤ hi) (x : Pt k) : clamp lo hi x ∈ Box lo hi := by
  refine mem_Box.mpr ⟨coord_le fun i => ?_, coord_le fun i => ?_⟩
  · exact le_max_left _ _
  · have := le_coord h i
    simp only [clamp]
    omega

lemma clamp_eq_self {k : ℕ} {lo hi x : Pt k} (hx : x ∈ Box lo hi) : clamp lo hi x = x := by
  obtain ⟨h1, h2⟩ := mem_Box.mp hx
  funext i
  have := le_coord h1 i
  have := le_coord h2 i
  simp only [clamp]
  omega

/-! ### Lifting an algorithm into a slice -/

/-- Run a `b`-dimensional algorithm inside the slice `{z | pr1 z = x}`: each query
`v` becomes `cat x v`, and each response is projected by `pr2`. -/
def liftSlice {α : Type} (x : Pt a) :
    QueryAlg (Pt b) (Pt b) α → QueryAlg (Pt (a + b)) (Pt (a + b)) α
  | .pure r => .pure r
  | .query v κ => .query (cat x v) (fun z => liftSlice x (κ (pr2 z)))

@[simp] lemma liftSlice_run {α : Type} (x : Pt a) (alg : QueryAlg (Pt b) (Pt b) α)
    (f : Pt (a + b) → Pt (a + b)) : (liftSlice x alg).run f = alg.run (sliceFun f x) := by
  induction alg with
  | pure r => rfl
  | query v κ ih => exact ih (sliceFun f x v)

lemma liftSlice_bounded {α : Type} {n : ℕ} (x : Pt a) {alg : QueryAlg (Pt b) (Pt b) α}
    (h : Bounded n alg) : Bounded n (liftSlice x alg) := by
  induction h with
  | pure => exact .pure
  | query _ ih => exact .query fun z => ih (pr2 z)

/-! ### Solver interfaces -/

/-- `SolvesMapsTo alg lo hi`: `alg` solves the Tarski instance on `Box lo hi`
whenever the oracle maps that box into itself. -/
def SolvesMapsTo {k : ℕ} (alg : QueryAlg (Pt k) (Pt k) (Answer k)) (lo hi : Pt k) : Prop :=
  ∀ g : Pt k → Pt k, (∀ x ∈ Box lo hi, g x ∈ Box lo hi) → IsSol g lo hi (alg.run g)

/-- `SolvesUpDown algOf lo hi`: for every sub-box `[l, u]` of `[lo, hi]` with
`l ∈ Up g` and `u ∈ Down g`, the algorithm `algOf l u` finds a solution in it.
This is the interface of FPS Lemma 4. -/
def SolvesUpDown {k : ℕ} (algOf : Pt k → Pt k → QueryAlg (Pt k) (Pt k) (Answer k))
    (lo hi : Pt k) : Prop :=
  ∀ (g : Pt k → Pt k) (l u : Pt k), lo ≤ l → l ≤ u → u ≤ hi →
    l ∈ Up g → u ∈ Down g → IsSol g l u ((algOf l u).run g)

/-- The up/down interface is the stronger one: a `SolvesUpDown` family, applied at
the full box, is a `SolvesMapsTo` algorithm. -/
lemma SolvesUpDown.solvesMapsTo {k : ℕ}
    {algOf : Pt k → Pt k → QueryAlg (Pt k) (Pt k) (Answer k)}
    {lo hi : Pt k} (h : SolvesUpDown algOf lo hi) (hlohi : lo ≤ hi) :
    SolvesMapsTo (algOf lo hi) lo hi := by
  intro g hg
  exact h g lo hi le_rfl hlohi le_rfl
    (mem_Up.mpr (mem_Box.mp (hg lo (mem_Box_self_left hlohi))).1)
    (mem_Down.mpr (mem_Box.mp (hg hi (mem_Box_self_right hlohi))).2)

/-- `intervalAlgorithm` is a `SolvesUpDown` family in every dimension — FPS
Lemma 4, the base case of every FPS argument. -/
lemma intervalAlgorithm_solvesUpDown {k : ℕ} (lo hi : Pt k) :
    SolvesUpDown (fun l u => intervalAlgorithm l u) lo hi :=
  fun _ _ _ _ hlu _ hl hu => intervalAlgorithm_isSol hlu hl hu

/-! ### The simulation state -/

/-- State of the decomposition run: the history of `(x, y)` pairs, and a solution
if one has already been exposed. -/
structure SimState (a b : ℕ) : Type where
  /-- FPS's set `P` of past points. -/
  hist : Hist a b
  /-- A solution found while setting up a slice, if any. -/
  found : Option (Answer (a + b))

/-- The invariant on a simulation state. -/
structure SimOk (f : Pt (a + b) → Pt (a + b)) (loA hiA : Pt a) (loB hiB : Pt b)
    (s : SimState a b) : Prop where
  good : Good f loA hiA loB hiB s.hist
  sol : ∀ z, s.found = some z → IsSol f (cat loA loB) (cat hiA hiB) z

/-- The oracle presented to the outer algorithm, including the clamp. -/
def simOracle (f : Pt (a + b) → Pt (a + b)) (loA hiA : Pt a) (loB : Pt b) (P : Hist a b) :
    Pt a → Pt a :=
  fun x => outerOracle f loB P (clamp loA hiA x)

lemma simOracle_mapsTo {f : Pt (a + b) → Pt (a + b)} {loA hiA : Pt a} {loB hiB : Pt b}
    {P : Hist a b} (hP : Good f loA hiA loB hiB P) (hloB : loB ≤ hiB)
    (hmap : ∀ z ∈ Box (cat loA loB) (cat hiA hiB), f z ∈ Box (cat loA loB) (cat hiA hiB)) :
    ∀ x ∈ Box loA hiA, simOracle f loA hiA loB P x ∈ Box loA hiA := by
  intro x hx
  rw [simOracle, clamp_eq_self hx]
  exact outerOracle_mapsTo hP hloB hmap x hx

/-! ### One simulated query -/

open Classical in
/-- One simulated query of the outer algorithm at an in-box point `x`.

If a solution has already been found, or the key is already on record, this is
cheap.  Otherwise it probes `cat x l` and `cat x u` (FPS Lemma 17), runs the inner
algorithm on `[l, u]` (non-empty by FPS Lemma 16), and probes the resulting slice
fixed point to produce the response. -/
noncomputable def stepAt (algB : Pt b → Pt b → QueryAlg (Pt b) (Pt b) (Answer b))
    (loB hiB : Pt b) (s : SimState a b) (x : Pt a) :
    QueryAlg (Pt (a + b)) (Pt (a + b)) (Pt a × SimState a b) :=
  match s.found, memo s.hist x with
  | some _, _ => QueryAlg.pure (x, s)
  | none, some y => QueryAlg.ask (cat x y) >>= fun fz => QueryAlg.pure (pr1 fz, s)
  | none, none =>
      QueryAlg.ask (cat x (lowB s.hist loB x)) >>= fun fl =>
        if hl : ¬ lowB s.hist loB x ≤ pr2 fl then
          QueryAlg.pure (x, ((⟨s.hist, some (.inr
            (cat (lowWitnessOf s.hist loB x (failCoord hl)).1
                 (lowWitnessOf s.hist loB x (failCoord hl)).2,
             cat x (lowB s.hist loB x)))⟩ : SimState a b)))
        else
          QueryAlg.ask (cat x (highB s.hist hiB x)) >>= fun fu =>
            if hu : ¬ pr2 fu ≤ highB s.hist hiB x then
              QueryAlg.pure (x, ((⟨s.hist, some (.inr
                (cat x (highB s.hist hiB x),
                 cat (highWitnessOf s.hist hiB x (failCoord hu)).1
                     (highWitnessOf s.hist hiB x (failCoord hu)).2))⟩ : SimState a b)))
            else
              liftSlice x (algB (lowB s.hist loB x) (highB s.hist hiB x)) >>= fun ansB =>
                match ansB with
                | .inr (v, w) =>
                    QueryAlg.pure (x, ((⟨s.hist, some (.inr (cat x v, cat x w))⟩ : SimState a b)))
                | .inl y =>
                    QueryAlg.ask (cat x y) >>= fun fy =>
                      QueryAlg.pure (pr1 fy,
                        ((⟨s.hist ++ [(x, y)], none⟩ : SimState a b)))

/-- One simulated query, clamped into the outer box. -/
noncomputable def step (algB : Pt b → Pt b → QueryAlg (Pt b) (Pt b) (Answer b))
    (loA hiA : Pt a) (loB hiB : Pt b) (s : SimState a b) (x₀ : Pt a) :
    QueryAlg (Pt (a + b)) (Pt (a + b)) (Pt a × SimState a b) :=
  stepAt algB loB hiB s (clamp loA hiA x₀)

variable {algB : Pt b → Pt b → QueryAlg (Pt b) (Pt b) (Answer b)}
  {loA hiA : Pt a} {loB hiB : Pt b}

lemma stepAt_found {s : SimState a b} {x : Pt a} {z : Answer (a + b)} (h : s.found = some z) :
    stepAt algB loB hiB s x = QueryAlg.pure (x, s) := by
  unfold stepAt; rw [h]

lemma stepAt_memo {s : SimState a b} {x : Pt a} {y : Pt b} (hf : s.found = none)
    (h : memo s.hist x = some y) :
    stepAt algB loB hiB s x =
      (QueryAlg.ask (cat x y) >>= fun fz => QueryAlg.pure (pr1 fz, s)) := by
  unfold stepAt; rw [hf, h]

lemma stepAt_fresh {s : SimState a b} {x : Pt a} (hf : s.found = none)
    (h : memo s.hist x = none) :
    stepAt algB loB hiB s x =
      (QueryAlg.ask (cat x (lowB s.hist loB x)) >>= fun fl =>
        if hl : ¬ lowB s.hist loB x ≤ pr2 fl then
          QueryAlg.pure (x, ((⟨s.hist, some (.inr
            (cat (lowWitnessOf s.hist loB x (failCoord hl)).1
                 (lowWitnessOf s.hist loB x (failCoord hl)).2,
             cat x (lowB s.hist loB x)))⟩ : SimState a b)))
        else
          QueryAlg.ask (cat x (highB s.hist hiB x)) >>= fun fu =>
            if hu : ¬ pr2 fu ≤ highB s.hist hiB x then
              QueryAlg.pure (x, ((⟨s.hist, some (.inr
                (cat x (highB s.hist hiB x),
                 cat (highWitnessOf s.hist hiB x (failCoord hu)).1
                     (highWitnessOf s.hist hiB x (failCoord hu)).2))⟩ : SimState a b)))
            else
              liftSlice x (algB (lowB s.hist loB x) (highB s.hist hiB x)) >>= fun ansB =>
                match ansB with
                | .inr (v, w) =>
                    QueryAlg.pure (x, ((⟨s.hist, some (.inr (cat x v, cat x w))⟩ : SimState a b)))
                | .inl y =>
                    QueryAlg.ask (cat x y) >>= fun fy =>
                      QueryAlg.pure (pr1 fy,
                        ((⟨s.hist ++ [(x, y)], none⟩ : SimState a b)))) := by
  unfold stepAt; rw [hf, h]

/-- `stepAt` makes at most `q_b + 3` queries: two Lemma-17 probes, the inner
algorithm, and one probe to read off the response. -/
lemma stepAt_bounded {qb : ℕ} (hBq : ∀ l u, Bounded qb (algB l u))
    (s : SimState a b) (x : Pt a) :
    Bounded (qb + 3) (stepAt algB loB hiB s x) := by
  rcases hf : s.found with _ | z
  · rcases hm : memo s.hist x with _ | y
    · rw [stepAt_fresh hf hm]
      -- probe `l`, then probe `u`, then the inner algorithm, then one final probe
      refine Bounded.mono (n := 1 + (qb + 2)) ((Bounded.ask _).bind fun fl => ?_) (by omega)
      split
      · exact Bounded.pure' _ _
      · refine Bounded.mono (n := 1 + (qb + 1)) ((Bounded.ask _).bind fun fu => ?_) (by omega)
        split
        · exact Bounded.pure' _ _
        · refine Bounded.mono (n := qb + 1)
            ((liftSlice_bounded x (hBq _ _)).bind fun ansB => ?_) (by omega)
          cases ansB with
          | inl y =>
            exact Bounded.mono (n := 1 + 0)
              ((Bounded.ask _).bind fun _ => Bounded.pure' _ 0) (by omega)
          | inr q => exact Bounded.pure' _ 1
    · rw [stepAt_memo hf hm]
      exact Bounded.mono (n := 1 + 0)
        ((Bounded.ask _).bind fun _ => Bounded.pure' _ 0) (by omega)
  · rw [stepAt_found hf]; exact Bounded.pure' _ _

lemma step_bounded {qb : ℕ} (hBq : ∀ l u, Bounded qb (algB l u))
    (s : SimState a b) (x₀ : Pt a) :
    Bounded (qb + 3) (step algB loA hiA loB hiB s x₀) := stepAt_bounded hBq s _

/-! ### The specification of one step -/

/-- What one simulated step guarantees.  `resp` is the crucial clause: the
response handed to the outer algorithm is the value of `outerOracle` at `x` for
*every* later extension of the history — which is what makes the outer
algorithm's oracle a genuine function, and hence lets us invoke its correctness. -/
structure StepOk (f : Pt (a + b) → Pt (a + b)) (loA hiA : Pt a) (loB hiB : Pt b)
    (s s' : SimState a b) (x : Pt a) (r : Pt a) : Prop where
  ext : ∃ Q, s'.hist = s.hist ++ Q
  ok : SimOk f loA hiA loB hiB s'
  unfound : s'.found = none → s.found = none
  keyed : s'.found = none → ∃ y, memo s'.hist x = some y
  resp : s'.found = none → ∀ Q : Hist a b, r = outerOracle f loB (s'.hist ++ Q) x

variable {f : Pt (a + b) → Pt (a + b)}

/-- **The step lemma.**  This is where FPS Lemmas 16 and 17 are used, together
with the correctness of the inner algorithm. -/
theorem stepAt_spec (hB : SolvesUpDown algB loB hiB) (hloB : loB ≤ hiB)
    (hmap : ∀ z ∈ Box (cat loA loB) (cat hiA hiB), f z ∈ Box (cat loA loB) (cat hiA hiB))
    {s : SimState a b} (hs : SimOk f loA hiA loB hiB s) {x : Pt a} (hx : x ∈ Box loA hiA) :
    StepOk f loA hiA loB hiB s ((stepAt algB loB hiB s x).run f).2 x
      ((stepAt algB loB hiB s x).run f).1 := by
  rcases hf : s.found with _ | z
  · rcases hm : memo s.hist x with _ | y
    · -- The interesting case: a fresh key.
      rw [stepAt_fresh hf hm, QueryAlg.run_bind, QueryAlg.run_ask]
      by_cases hl : ¬ lowB s.hist loB x ≤ pr2 (f (cat x (lowB s.hist loB x)))
      · -- FPS Lemma 17 exposes a violation involving `l`.
        rw [dif_pos hl]
        refine ⟨⟨[], by simp⟩, ⟨hs.good, ?_⟩, by simp, by simp, by simp⟩
        intro z hz
        rw [← Option.some_inj.mp hz]
        exact sol_of_lowB_fail hs.good hloB hmap hx (failCoord_spec hl)
      · rw [dif_neg hl, QueryAlg.run_bind, QueryAlg.run_ask]
        push Not at hl
        by_cases hu : ¬ pr2 (f (cat x (highB s.hist hiB x))) ≤ highB s.hist hiB x
        · -- FPS Lemma 17 exposes a violation involving `u`.
          rw [dif_pos hu]
          refine ⟨⟨[], by simp⟩, ⟨hs.good, ?_⟩, by simp, by simp, by simp⟩
          intro z hz
          rw [← Option.some_inj.mp hz]
          exact sol_of_highB_fail hs.good hloB hmap hx (failCoord_spec hu)
        · rw [dif_neg hu, QueryAlg.run_bind, liftSlice_run]
          push Not at hu
          -- The inner algorithm is applicable: FPS Lemma 16 gives `l ≼ u`, and the
          -- two probes just made give `l ∈ Up` and `u ∈ Down` for the slice.
          have hlu : lowB s.hist loB x ≤ highB s.hist hiB x := lowB_le_highB hs.good hloB x
          have hsol := hB (sliceFun f x) (lowB s.hist loB x) (highB s.hist hiB x)
            loB_le_lowB hlu highB_le_hiB hl hu
          rcases hans : (algB (lowB s.hist loB x) (highB s.hist hiB x)).run (sliceFun f x)
            with y | ⟨v, w⟩
          · -- A slice fixed point: record it and answer the outer algorithm.
            rw [hans] at hsol
            obtain ⟨hymem, hyfix⟩ := hsol
            obtain ⟨hly, hyu⟩ := mem_Box.mp hymem
            have hyB : y ∈ Box loB hiB :=
              mem_Box.mpr ⟨loB_le_lowB.trans hly, hyu.trans highB_le_hiB⟩
            simp only [QueryAlg.run_bind, QueryAlg.run_ask, QueryAlg.run_pure]
            refine ⟨⟨[(x, y)], rfl⟩, ⟨hs.good.append hx hyB hyfix hly hyu, by simp⟩,
              fun _ => hf, fun _ => ⟨y, memo_append_singleton hm y⟩, fun _ Q => ?_⟩
            rw [outerOracle, memoD_append (memo_append_singleton hm y) (Q := Q)]
          · -- A slice violation: it is a violation of `f`.
            rw [hans] at hsol
            obtain ⟨hv, hw, hvop⟩ := hsol
            simp only [QueryAlg.run_pure]
            refine ⟨⟨[], by simp⟩, ⟨hs.good, ?_⟩, by simp, by simp, by simp⟩
            intro z hz
            rw [← Option.some_inj.mp hz]
            refine ⟨mem_Box_cat.mpr ⟨hx, ?_⟩, mem_Box_cat.mpr ⟨hx, ?_⟩, isVop_of_slice hvop⟩
            · exact mem_Box.mpr ⟨loB_le_lowB.trans (mem_Box.mp hv).1,
                (mem_Box.mp hv).2.trans highB_le_hiB⟩
            · exact mem_Box.mpr ⟨loB_le_lowB.trans (mem_Box.mp hw).1,
                (mem_Box.mp hw).2.trans highB_le_hiB⟩
    · -- The key is already on record: one probe suffices.
      rw [stepAt_memo hf hm]
      simp only [QueryAlg.run_bind, QueryAlg.run_ask, QueryAlg.run_pure]
      refine ⟨⟨[], by simp⟩, hs, fun _ => hf, fun _ => ⟨y, hm⟩, fun _ Q => ?_⟩
      rw [outerOracle, memoD_append hm (Q := Q)]
  · -- A solution was already found: nothing to do.
    rw [stepAt_found hf, QueryAlg.run_pure]
    exact ⟨⟨[], by simp⟩, hs, fun h => h,
      fun h => absurd (hf.symm.trans h) (by simp),
      fun h => absurd (hf.symm.trans h) (by simp)⟩

/-- `stepAt_spec` transported to `step`, which clamps its argument. -/
theorem step_spec (hB : SolvesUpDown algB loB hiB) (hloA : loA ≤ hiA) (hloB : loB ≤ hiB)
    (hmap : ∀ z ∈ Box (cat loA loB) (cat hiA hiB), f z ∈ Box (cat loA loB) (cat hiA hiB))
    {s : SimState a b} (hs : SimOk f loA hiA loB hiB s) (x₀ : Pt a) :
    StepOk f loA hiA loB hiB s ((step algB loA hiA loB hiB s x₀).run f).2 (clamp loA hiA x₀)
      ((step algB loA hiA loB hiB s x₀).run f).1 :=
  stepAt_spec hB hloB hmap hs (clamp_mem hloA x₀)

/-! ### Simulating the whole outer run -/

/-- Run the outer algorithm against the simulated oracle, threading the history. -/
noncomputable def simulate (algB : Pt b → Pt b → QueryAlg (Pt b) (Pt b) (Answer b))
    (loA hiA : Pt a) (loB hiB : Pt b) :
    QueryAlg (Pt a) (Pt a) (Answer a) → SimState a b →
      QueryAlg (Pt (a + b)) (Pt (a + b)) (Answer a × SimState a b)
  | .pure ans, s => QueryAlg.pure (ans, s)
  | .query x κ, s =>
      step algB loA hiA loB hiB s x >>= fun ps =>
        simulate algB loA hiA loB hiB (κ ps.1) ps.2

lemma simulate_bounded {qb : ℕ} (hBq : ∀ l u, Bounded qb (algB l u)) {qa : ℕ} :
    ∀ {alg : QueryAlg (Pt a) (Pt a) (Answer a)}, Bounded qa alg → ∀ s : SimState a b,
      Bounded (qa * (qb + 3)) (simulate algB loA hiA loB hiB alg s) := by
  intro alg h
  induction h with
  | pure => intro s; exact Bounded.pure' _ _
  | @query n x κ _ ih =>
    intro s
    refine Bounded.mono (n := (qb + 3) + n * (qb + 3))
      ((step_bounded hBq s x).bind fun ps => ih ps.1 ps.2) ?_
    rw [Nat.succ_mul]
    omega

/-- What a whole simulated outer run guarantees.  `resp` says the answer the
outer algorithm produced is exactly what it would produce against
`simOracle` built from the final history (or any extension of it). -/
structure SimOut (f : Pt (a + b) → Pt (a + b)) (loA hiA : Pt a) (loB hiB : Pt b)
    (alg : QueryAlg (Pt a) (Pt a) (Answer a)) (s : SimState a b)
    (out : Answer a × SimState a b) : Prop where
  ext : ∃ Q, out.2.hist = s.hist ++ Q
  ok : SimOk f loA hiA loB hiB out.2
  unfound : out.2.found = none → s.found = none
  resp : out.2.found = none → ∀ Q : Hist a b,
      out.1 = alg.run (simOracle f loA hiA loB (out.2.hist ++ Q))

lemma simulate_pure (ans : Answer a) (s : SimState a b) :
    (simulate algB loA hiA loB hiB (QueryAlg.pure ans) s).run f = (ans, s) := rfl

lemma simulate_query (x : Pt a) (κ : Pt a → QueryAlg (Pt a) (Pt a) (Answer a))
    (s : SimState a b) :
    (simulate algB loA hiA loB hiB (QueryAlg.query x κ) s).run f
      = (simulate algB loA hiA loB hiB (κ ((step algB loA hiA loB hiB s x).run f).1)
          ((step algB loA hiA loB hiB s x).run f).2).run f := by
  change ((step algB loA hiA loB hiB s x) >>= _).run f = _
  rw [QueryAlg.run_bind]

theorem simulate_spec (hB : SolvesUpDown algB loB hiB) (hloA : loA ≤ hiA) (hloB : loB ≤ hiB)
    (hmap : ∀ z ∈ Box (cat loA loB) (cat hiA hiB), f z ∈ Box (cat loA loB) (cat hiA hiB)) :
    ∀ (alg : QueryAlg (Pt a) (Pt a) (Answer a)) (s : SimState a b),
      SimOk f loA hiA loB hiB s →
      SimOut f loA hiA loB hiB alg s ((simulate algB loA hiA loB hiB alg s).run f) := by
  intro alg
  induction alg with
  | pure ans =>
    intro s hs
    rw [simulate_pure]
    exact ⟨⟨[], by simp⟩, hs, fun h => h, fun _ _ => rfl⟩
  | query x κ ih =>
    intro s hs
    rw [simulate_query]
    set ps := (step algB loA hiA loB hiB s x).run f with hps
    have hstep : StepOk f loA hiA loB hiB s ps.2 (clamp loA hiA x) ps.1 :=
      step_spec hB hloA hloB hmap hs x
    have hih := ih ps.1 ps.2 hstep.ok
    set qs := (simulate algB loA hiA loB hiB (κ ps.1) ps.2).run f with hqs
    obtain ⟨Q₁, hQ₁⟩ := hstep.ext
    obtain ⟨Q₂, hQ₂⟩ := hih.ext
    refine ⟨⟨Q₁ ++ Q₂, by rw [hQ₂, hQ₁, List.append_assoc]⟩, hih.ok,
      fun h => hstep.unfound (hih.unfound h), fun h Q => ?_⟩
    -- The response given at this query agrees with the final oracle, because
    -- `memo` is stable under extension of the history.
    have h2 : ps.2.found = none := hih.unfound h
    have hkey : simOracle f loA hiA loB (qs.2.hist ++ Q) x = ps.1 := by
      rw [simOracle, hQ₂, List.append_assoc]
      exact (hstep.resp h2 (Q₂ ++ Q)).symm
    rw [hih.resp h Q, QueryAlg.run_query, hkey]

/-! ### Finalisation

The outer algorithm may return a point it never queried, so we run one more
simulated step at each returned point to obtain its slice fixed point. -/

/-- How a one-point answer is translated once its slice fixed point is on
record. -/
def finishOne (loB : Pt b) (x : Pt a) (s : SimState a b) : Answer (a + b) :=
  match s.found with
  | some z => z
  | none => .inl (cat x (memoD s.hist loB x))

/-- How a two-point answer is translated once both slice fixed points are on
record. -/
def finishTwo (loB : Pt b) (x y : Pt a) (s : SimState a b) : Answer (a + b) :=
  match s.found with
  | some z => z
  | none => .inr (cat x (memoD s.hist loB x), cat y (memoD s.hist loB y))

lemma finishOne_of_found {loB : Pt b} {x : Pt a} {s : SimState a b} {z : Answer (a + b)}
    (h : s.found = some z) : finishOne loB x s = z := by unfold finishOne; rw [h]

lemma finishOne_of_none {loB : Pt b} {x : Pt a} {s : SimState a b} (h : s.found = none) :
    finishOne loB x s = .inl (cat x (memoD s.hist loB x)) := by unfold finishOne; rw [h]

lemma finishTwo_of_found {loB : Pt b} {x y : Pt a} {s : SimState a b} {z : Answer (a + b)}
    (h : s.found = some z) : finishTwo loB x y s = z := by unfold finishTwo; rw [h]

lemma finishTwo_of_none {loB : Pt b} {x y : Pt a} {s : SimState a b} (h : s.found = none) :
    finishTwo loB x y s
      = .inr (cat x (memoD s.hist loB x), cat y (memoD s.hist loB y)) := by
  unfold finishTwo; rw [h]

noncomputable def finalize (algB : Pt b → Pt b → QueryAlg (Pt b) (Pt b) (Answer b))
    (loA hiA : Pt a) (loB hiB : Pt b) (s : SimState a b) (ansA : Answer a) :
    QueryAlg (Pt (a + b)) (Pt (a + b)) (Answer (a + b)) :=
  match ansA with
  | .inl x =>
      step algB loA hiA loB hiB s x >>= fun ps => QueryAlg.pure (finishOne loB x ps.2)
  | .inr (x, y) =>
      step algB loA hiA loB hiB s x >>= fun ps₁ =>
        step algB loA hiA loB hiB ps₁.2 y >>= fun ps₂ =>
          QueryAlg.pure (finishTwo loB x y ps₂.2)

lemma finalize_inl_run (s : SimState a b) (x : Pt a) :
    (finalize algB loA hiA loB hiB s (.inl x)).run f
      = finishOne loB x ((step algB loA hiA loB hiB s x).run f).2 := by
  change ((step algB loA hiA loB hiB s x) >>= _).run f = _
  rw [QueryAlg.run_bind]; rfl

lemma finalize_inr_run (s : SimState a b) (x y : Pt a) :
    (finalize algB loA hiA loB hiB s (.inr (x, y))).run f
      = finishTwo loB x y ((step algB loA hiA loB hiB
          ((step algB loA hiA loB hiB s x).run f).2 y).run f).2 := by
  change ((step algB loA hiA loB hiB s x) >>= _).run f = _
  rw [QueryAlg.run_bind, QueryAlg.run_bind]; rfl

lemma finalize_bounded {qb : ℕ} (hBq : ∀ l u, Bounded qb (algB l u))
    (s : SimState a b) (ansA : Answer a) :
    Bounded (2 * (qb + 3)) (finalize algB loA hiA loB hiB s ansA) := by
  cases ansA with
  | inl x =>
    exact Bounded.mono (n := (qb + 3) + 0)
      ((step_bounded hBq s x).bind fun _ => Bounded.pure' _ 0) (by omega)
  | inr p =>
    obtain ⟨x, y⟩ := p
    refine Bounded.mono (n := (qb + 3) + ((qb + 3) + 0))
      ((step_bounded hBq s x).bind fun ps₁ =>
        (step_bounded hBq ps₁.2 y).bind fun _ => Bounded.pure' _ 0) (by omega)

/-! ### The algorithm and the theorem -/

/-- The decomposition algorithm: run the outer algorithm against the simulated
oracle, then finalise. -/
noncomputable def decompAlg (algA : QueryAlg (Pt a) (Pt a) (Answer a))
    (algB : Pt b → Pt b → QueryAlg (Pt b) (Pt b) (Answer b))
    (loA hiA : Pt a) (loB hiB : Pt b) : QueryAlg (Pt (a + b)) (Pt (a + b)) (Answer (a + b)) :=
  simulate algB loA hiA loB hiB algA ⟨[], none⟩ >>= fun ps =>
    match ps.2.found with
    | some z => QueryAlg.pure z
    | none => finalize algB loA hiA loB hiB ps.2 ps.1

/-- **Query bound for the decomposition** (FPS Theorem 18, query count).  If the
outer algorithm makes at most `qₐ` queries and the inner at most `q_b`, the
composite makes at most `(qₐ + 2)(q_b + 3)`. -/
theorem decompAlg_bounded {algA : QueryAlg (Pt a) (Pt a) (Answer a)} {qa qb : ℕ}
    (hAq : Bounded qa algA) (hBq : ∀ l u, Bounded qb (algB l u)) :
    Bounded ((qa + 2) * (qb + 3)) (decompAlg algA algB loA hiA loB hiB) := by
  refine Bounded.mono (n := qa * (qb + 3) + 2 * (qb + 3))
    ((simulate_bounded hBq hAq _).bind fun ps => ?_)
    (le_of_eq (Nat.add_mul qa 2 (qb + 3)).symm)
  split
  all_goals first
    | exact Bounded.pure' _ _
    | exact finalize_bounded hBq _ _

/-! ### Correctness -/

variable {algA : QueryAlg (Pt a) (Pt a) (Answer a)}

/-- Correctness of `finalize`, stated abstractly in the simulation state and the
outer algorithm's answer.  `hansA` is what `simulate_spec` delivers: the answer is
what the outer algorithm produces against the oracle of any extension of the
history. -/
theorem finalize_isSol (hA : SolvesMapsTo algA loA hiA) (hB : SolvesUpDown algB loB hiB)
    (hloA : loA ≤ hiA) (hloB : loB ≤ hiB)
    (hmap : ∀ z ∈ Box (cat loA loB) (cat hiA hiB), f z ∈ Box (cat loA loB) (cat hiA hiB))
    {s : SimState a b} (hs : SimOk f loA hiA loB hiB s)
    {ansA : Answer a}
    (hansA : ∀ Q : Hist a b, ansA = algA.run (simOracle f loA hiA loB (s.hist ++ Q))) :
    IsSol f (cat loA loB) (cat hiA hiB)
      ((finalize algB loA hiA loB hiB s ansA).run f) := by
  cases ansA with
  | inl x =>
    have hstep := step_spec hB hloA hloB hmap hs x
    rw [finalize_inl_run]
    rcases hfd : ((step algB loA hiA loB hiB s x).run f).2.found with _ | z
    · -- No solution exposed: the outer answer lifts using the recorded `y`.
      rw [finishOne_of_none hfd]
      obtain ⟨Q, hQ⟩ := hstep.ext
      obtain ⟨y, hy⟩ := hstep.keyed hfd
      -- the outer algorithm is correct against the oracle of the final history
      have hg := hA (simOracle f loA hiA loB ((step algB loA hiA loB hiB s x).run f).2.hist)
        (simOracle_mapsTo hstep.ok.good hloB hmap)
      have hEq : algA.run
          (simOracle f loA hiA loB ((step algB loA hiA loB hiB s x).run f).2.hist) = .inl x := by
        have h := hansA Q
        rw [← hQ] at h
        exact h.symm
      rw [hEq] at hg
      obtain ⟨hxbox, hgx⟩ := hg
      rw [clamp_eq_self hxbox] at hy
      have hmemoD : memoD ((step algB loA hiA loB hiB s x).run f).2.hist loB x = y :=
        memoD_eq_of_memo hy
      have hmem : (x, y) ∈ ((step algB loA hiA loB hiB s x).run f).2.hist := mem_of_memo hy
      have hyB : y ∈ Box loB hiB := hstep.ok.good.memB _ hmem
      have hslice : pr2 (f (cat x y)) = y := hstep.ok.good.slice _ hmem
      have hfst : pr1 (f (cat x y)) = x := by
        have hgo : simOracle f loA hiA loB ((step algB loA hiA loB hiB s x).run f).2.hist x
            = pr1 (f (cat x y)) := by
          simp only [simOracle, outerOracle, clamp_eq_self hxbox, hmemoD]
        rw [← hgo]; exact hgx
      rw [hmemoD]
      refine ⟨mem_Box_cat.mpr ⟨hxbox, hyB⟩, ?_⟩
      rw [← cat_pr (f (cat x y)), hfst, hslice]
    · rw [finishOne_of_found hfd]; exact hstep.ok.sol z hfd
  | inr p =>
    obtain ⟨x, y⟩ := p
    have hstep₁ := step_spec hB hloA hloB hmap hs x
    have hstep₂ := step_spec hB hloA hloB hmap hstep₁.ok y
    rw [finalize_inr_run]
    rcases hfd : ((step algB loA hiA loB hiB
        ((step algB loA hiA loB hiB s x).run f).2 y).run f).2.found with _ | z
    · -- No solution exposed: the outer violation lifts.
      rw [finishTwo_of_none hfd]
      obtain ⟨Q₁, hQ₁⟩ := hstep₁.ext
      obtain ⟨Q₂, hQ₂⟩ := hstep₂.ext
      have hfd₁ : ((step algB loA hiA loB hiB s x).run f).2.found = none :=
        hstep₂.unfound hfd
      obtain ⟨yx, hyx₁⟩ := hstep₁.keyed hfd₁
      obtain ⟨yy, hyy⟩ := hstep₂.keyed hfd
      have hyx : memo ((step algB loA hiA loB hiB
          ((step algB loA hiA loB hiB s x).run f).2 y).run f).2.hist (clamp loA hiA x)
          = some yx := by
        rw [hQ₂]; exact memo_append hyx₁
      have hg := hA (simOracle f loA hiA loB
        ((step algB loA hiA loB hiB ((step algB loA hiA loB hiB s x).run f).2 y).run f).2.hist)
        (simOracle_mapsTo hstep₂.ok.good hloB hmap)
      have hEq : algA.run (simOracle f loA hiA loB
          ((step algB loA hiA loB hiB
            ((step algB loA hiA loB hiB s x).run f).2 y).run f).2.hist) = .inr (x, y) := by
        have h := hansA (Q₁ ++ Q₂)
        rw [← List.append_assoc, ← hQ₁, ← hQ₂] at h
        exact h.symm
      rw [hEq] at hg
      obtain ⟨hxbox, hybox, hxy, hvop⟩ := hg
      rw [clamp_eq_self hxbox] at hyx
      rw [clamp_eq_self hybox] at hyy
      have hmemx := memoD_eq_of_memo (loB := loB) hyx
      have hmemy := memoD_eq_of_memo (loB := loB) hyy
      have hmemx' := mem_of_memo hyx
      have hmemy' := mem_of_memo hyy
      -- monotonicity of the record is what makes the lifted pair comparable
      have hyxy : yx ≤ yy := hstep₂.ok.good.mono _ hmemx' _ hmemy' hxy
      rw [hmemx, hmemy]
      refine ⟨mem_Box_cat.mpr ⟨hxbox, hstep₂.ok.good.memB _ hmemx'⟩,
        mem_Box_cat.mpr ⟨hybox, hstep₂.ok.good.memB _ hmemy'⟩,
        cat_mono hxy hyxy, fun hle => hvop ?_⟩
      simp only [simOracle, outerOracle, clamp_eq_self hxbox, clamp_eq_self hybox, hmemx, hmemy]
      exact pr1_mono hle
    · rw [finishTwo_of_found hfd]; exact hstep₂.ok.sol z hfd

/-- **FPS Theorem 18** (correctness).  Composing a `SolvesMapsTo` algorithm in
dimension `a` with a `SolvesUpDown` family in dimension `b` gives a
`SolvesMapsTo` algorithm in dimension `a + b`. -/
theorem decompAlg_isSol (hA : SolvesMapsTo algA loA hiA) (hB : SolvesUpDown algB loB hiB)
    (hloA : loA ≤ hiA) (hloB : loB ≤ hiB) :
    SolvesMapsTo (decompAlg algA algB loA hiA loB hiB) (cat loA loB) (cat hiA hiB) := by
  intro f hmap
  have hsim := simulate_spec hB hloA hloB hmap algA ⟨[], none⟩ ⟨Good.nil, by simp⟩
  have hrun : (decompAlg algA algB loA hiA loB hiB).run f
      = (match ((simulate algB loA hiA loB hiB algA ⟨[], none⟩).run f).2.found with
         | some z => QueryAlg.pure z
         | none => finalize algB loA hiA loB hiB
             ((simulate algB loA hiA loB hiB algA ⟨[], none⟩).run f).2
             ((simulate algB loA hiA loB hiB algA ⟨[], none⟩).run f).1).run f := by
    change ((simulate algB loA hiA loB hiB algA ⟨[], none⟩) >>= _).run f = _
    rw [QueryAlg.run_bind]
  rw [hrun]
  rcases hfd : ((simulate algB loA hiA loB hiB algA ⟨[], none⟩).run f).2.found with _ | z
  · exact finalize_isSol hA hB hloA hloB hmap hsim.ok (hsim.resp hfd)
  · exact hsim.ok.sol z hfd

end Tfnp.Tarski
