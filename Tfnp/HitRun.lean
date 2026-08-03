/-
Copyright (c) 2026 Angus Joshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Angus Joshi
-/
import Tfnp.Algorithm

/-!
# Per-round guarantees of the hit-and-run algorithm

Companion to `notes/hitrun.md`. The hit-and-run route to `ℓ∞`-contraction
fixed points cuts at the **balanced point of a sample set** — no integer grid,
no `4·s` shift. This file formalises, in its own namespace and reusing the
geometry of `Tfnp/Contraction.lean` and `Tfnp/Algorithm.lean`, the two per-round
facts that route relies on:

* `fixedPoint_mem_pyrUnion_apex` (note **Lemma 1**, *cut validity*) — the fixed
  point lies in the pyramid union anchored **at the query point itself**,
  `⋃_{i : sᵢ ≠ 0} 𝒫ᵢ(c, sᵢ)` with `sᵢ = sgn(f(c)ᵢ − cᵢ)`. Contrast CLY's
  Lemma 2 (`fixedPoint_mem_pyrUnion`), which anchors at the shifted base
  `c + 4·s` and needs `‖f(c) − c‖∞ > 16/γ`: for the *continuous* algorithm the
  apex cut is exact for **every** `c ≠ x*`, with no distance threshold.

* `linfDist_self_map_le` / `isApproxFixedPoint_of_near` (note **Lemma 3**,
  *extraction*) — proximity to the fixed point yields an approximate fixed
  point: `‖x − f x‖∞ ≤ (1 + λ)·‖x − x*‖∞`.

The volume-halving guarantee (note **Lemma 2**) is exactly
`exists_balanced_point_box` applied to the finite sample set — the balanced
point captures at most half of the samples in every pyramid union — and is not
re-proved here. The one remaining ingredient, sampling the non-convex candidate
body in polynomial time, is the open problem (`notes/hitrun.md` §3–4, and the
isoperimetry question) and is deliberately **not** formalised: it is equivalent
to `SSG ∈ P`.
-/

set_option autoImplicit false

namespace Tfnp.Contraction

variable {k : ℕ} [NeZero k]

/-! ## Sign helpers -/

lemma sgnR_of_pos {t : ℝ} (h : 0 < t) : sgnR t = 1 := by
  unfold sgnR; rw [if_pos h]

lemma sgnR_of_neg {t : ℝ} (h : t < 0) : sgnR t = -1 := by
  unfold sgnR; rw [if_neg (by linarith), if_pos h]

/-- If `|e| < |a|` then `e + a` has the same sign as `a`: the dominant term
`a` decides the sign. -/
lemma sgnR_add_of_abs_lt {a e : ℝ} (h : |e| < |a|) : sgnR (e + a) = sgnR a := by
  have ha : a ≠ 0 := by
    rintro rfl; rw [abs_zero] at h; linarith [abs_nonneg e]
  obtain ⟨h1, h2⟩ := abs_lt.mp h
  rcases lt_or_gt_of_ne ha with hneg | hpos
  · rw [abs_of_neg hneg] at h2
    rw [sgnR_of_neg (by linarith : e + a < 0), sgnR_of_neg hneg]
  · rw [abs_of_pos hpos] at h1
    rw [sgnR_of_pos (by linarith : 0 < e + a), sgnR_of_pos hpos]

/-! ## Lemma 1 — cut validity at the apex -/

/-- **Cut validity (note Lemma 1).** For an `ℓ∞`-contraction `f` with fixed
point `xs`, any query point `c ≠ xs` gives a valid cut *anchored at `c`*: with
`sᵢ = sgn(f(c)ᵢ − cᵢ)`, the fixed point lies in `⋃_{i : sᵢ ≠ 0} 𝒫ᵢ(c, sᵢ)`.
No shift and no `‖f(c) − c‖∞` threshold are required. -/
theorem fixedPoint_mem_pyrUnion_apex {lam : ℝ} {f : Vec k → Vec k}
    (hf : IsLInfContraction f lam) {c xs : Vec k}
    (hc : InUnitCube c) (hxs : InUnitCube xs) (hfix : f xs = xs) (hne : xs ≠ c)
    {s : Fin k → ℝ} (hsdef : ∀ i, s i = sgnR (f c i - c i)) :
    xs ∈ PyrUnion s c := by
  -- `r := ‖xs − c‖∞ > 0`, realised at some coordinate `j`.
  have hr : 0 < linfDist xs c := by rw [linfDist_eq_dist]; exact dist_pos.mpr hne
  obtain ⟨j, hj⟩ := exists_coord_eq_linfDist xs c
  -- The image displacement at `j` is at most `lam·r`.
  have he : |f c j - xs j| ≤ lam * linfDist xs c := by
    have h1 : |f c j - xs j| ≤ linfDist (f c) (f xs) := by
      have hx : xs j = f xs j := by rw [hfix]
      rw [hx]; exact abs_sub_le_linfDist (f c) (f xs) j
    have h2 : linfDist (f c) (f xs) ≤ lam * linfDist c xs := hf.contracts c xs hc hxs
    rw [linfDist_comm c xs] at h2; linarith
  have ha_ne : xs j - c j ≠ 0 := by
    intro h0; rw [h0, abs_zero] at hj; linarith
  -- `|f c j − xs j| < |xs j − c j|`, so the `(xs − c)` term dominates `f(c) − c`.
  have hlt : |f c j - xs j| < |xs j - c j| := by
    rw [hj]
    calc |f c j - xs j| ≤ lam * linfDist xs c := he
      _ < 1 * linfDist xs c := mul_lt_mul_of_pos_right hf.lam_lt_one hr
      _ = linfDist xs c := one_mul _
  have hdecomp : f c j - c j = (f c j - xs j) + (xs j - c j) := by ring
  have hsj : s j = sgnR (xs j - c j) := by
    rw [hsdef j, hdecomp, sgnR_add_of_abs_lt hlt]
  have hsgn_ne : sgnR (xs j - c j) ≠ 0 := by
    simp only [ne_eq, sgnR_eq_zero_iff]; exact ha_ne
  refine ⟨j, ?_, ?_⟩
  · rw [hsj]; exact hsgn_ne
  · rw [mem_Pyr, hsj, sgnR_mul_self_pos hsgn_ne]; exact hj

/-! ## Lemma 3 — extraction of an approximate fixed point -/

/-- **Extraction (note Lemma 3).** Proximity to the fixed point yields an
approximate fixed point: `‖x − f x‖∞ ≤ (1 + λ)·‖x − x*‖∞`. As the candidate
region shrinks around the (contained) fixed point, every point of it becomes an
approximate fixed point. -/
theorem linfDist_self_map_le {lam : ℝ} {f : Vec k → Vec k}
    (hf : IsLInfContraction f lam) {x xs : Vec k}
    (hx : InUnitCube x) (hxs : InUnitCube xs) (hfix : f xs = xs) :
    linfDist x (f x) ≤ (1 + lam) * linfDist x xs := by
  have htri : linfDist x (f x) ≤ linfDist x xs + linfDist xs (f x) :=
    linfDist_triangle _ _ _
  have hcon : linfDist xs (f x) ≤ lam * linfDist x xs := by
    have h := hf.contracts xs x hxs hx
    rw [hfix, linfDist_comm xs x] at h; exact h
  have hexp : (1 + lam) * linfDist x xs = linfDist x xs + lam * linfDist x xs := by ring
  rw [hexp]; linarith

/-- If `x` lies within `ε/(1+λ)` of the fixed point (i.e. `(1+λ)·‖x − x*‖∞ ≤ ε`)
then `x` is an `ε`-approximate fixed point. -/
theorem isApproxFixedPoint_of_near {lam ε : ℝ} {f : Vec k → Vec k}
    (hf : IsLInfContraction f lam) {x xs : Vec k}
    (hx : InUnitCube x) (hxs : InUnitCube xs) (hfix : f xs = xs)
    (hnear : (1 + lam) * linfDist x xs ≤ ε) : IsApproxFixedPoint f ε x :=
  ⟨hx, (linfDist_self_map_le hf hx hxs hfix).trans hnear⟩

/-! ## Theorem A — star-shapedness in the "toward" regime

If every round's cut points *toward* the fixed point, the candidate body is
star-shaped about it, and can be sampled exactly by ray-shooting — no Markov
chain, no isoperimetry (see `notes/isoperimetry_attack.md`). This is the
`z = x*` case of the Kernel Theorem, proved here directly from
`mem_pyramidUnion_iff`. -/

/-- **Theorem A.** If a cut `(c, s)` points toward `xs` on every coordinate
(`0 ≤ signR (sᵢ)·(xsᵢ − cᵢ)` for all `i`), then `K(c,s)` is star-shaped about
`xs`: the segment from `xs` to any `y ∈ K(c,s)` stays in `K(c,s)`. -/
theorem starshaped_of_toward {s : Fin k → Bool} {c xs : Vec k}
    (htoward : ∀ i, 0 ≤ signR (s i) * (xs i - c i))
    {y : Vec k} (hy : ∃ i, y ∈ Pyramid i (s i) c)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∃ i, (fun j => (1 - t) * xs j + t * y j) ∈ Pyramid i (s i) c := by
  have h1t : 0 ≤ 1 - t := by linarith
  set q : Vec k := fun j => (1 - t) * xs j + t * y j with hq
  have hqj : ∀ j, q j = (1 - t) * xs j + t * y j := fun j => by rw [hq]
  rw [mem_pyramidUnion_iff] at hy ⊢
  -- toward ⟹ `sgnSup s xs c ≤ 0`
  have hxs0 : sgnSup s xs c ≤ 0 := by
    apply sgnSup_le; intro i
    have e : signR (s i) * (c i - xs i) = -(signR (s i) * (xs i - c i)) := by ring
    rw [e]; linarith [htoward i]
  -- upper bound on the `−`-side at `q`
  have hqc : sgnSup s q c ≤ (1 - t) * sgnSup s xs c + t * sgnSup s y c := by
    apply sgnSup_le; intro i
    have e : signR (s i) * (c i - q i)
        = (1 - t) * (signR (s i) * (c i - xs i)) + t * (signR (s i) * (c i - y i)) := by
      rw [hqj i]; ring
    rw [e]
    nlinarith [le_sgnSup s xs c i, le_sgnSup s y c i, h1t, ht0]
  -- lower bound on the `+`-side at `q`, via the argmax of the `y`-side
  obtain ⟨a, ha⟩ := exists_eq_sgnSup s c y
  have hcq : t * sgnSup s c y ≤ sgnSup s c q := by
    have hle := le_sgnSup s c q a
    have e : signR (s a) * (q a - c a)
        = (1 - t) * (signR (s a) * (xs a - c a)) + t * (signR (s a) * (y a - c a)) := by
      rw [hqj a]; ring
    rw [e, ha] at hle
    nlinarith [htoward a, h1t, hle]
  calc sgnSup s q c
      ≤ (1 - t) * sgnSup s xs c + t * sgnSup s y c := hqc
    _ ≤ (1 - t) * 0 + t * sgnSup s c y := by nlinarith [hxs0, h1t, hy, ht0]
    _ = t * sgnSup s c y := by ring
    _ ≤ sgnSup s c q := hcq

/-- Star-shaped about `xs` for a whole family of toward-cuts: if every cut points
toward `xs` and `y` lies in every `K(c r, s r)`, the segment from `xs` to `y`
does too. Intersecting with the (convex) box gives: the candidate body is
star-shaped about the fixed point whenever all cuts point toward it. -/
theorem starshaped_of_toward_family {ι : Type*} {cs : ι → Vec k}
    {ss : ι → (Fin k → Bool)} {xs : Vec k}
    (htoward : ∀ r i, 0 ≤ signR (ss r i) * (xs i - cs r i))
    {y : Vec k} (hy : ∀ r, ∃ i, y ∈ Pyramid i (ss r i) (cs r))
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∀ r, ∃ i, (fun j => (1 - t) * xs j + t * y j) ∈ Pyramid i (ss r i) (cs r) :=
  fun r => starshaped_of_toward (htoward r) (hy r) ht0 ht1

/-! ## Halfspace cuts in low support — the convex regime -/

/-- **Halfspace cut (`|support| ≤ 2`).** If the cut's active set is contained in
`{i, j}`, the pyramid union lies in the linear halfspace
`{y : sᵢ(yᵢ−cᵢ) + sⱼ(yⱼ−cⱼ) ≥ 0}` through `c`. In particular for `d ≤ 2` every
cut is (contained in) a halfspace, so the candidate region stays **convex** and
the classical centroid/cutting-plane machinery gives a poly-time algorithm — the
easy low-dimensional case, and the target of Corollary C after narrowing the
support to two (`notes/polytime.md` §3.2). For `|support| ≥ 3` this fails
(`conv K = ℝ^d`), which is the whole difficulty. -/
theorem pyrUnion_subset_halfspace {s : Fin k → ℝ} (hs : IsTernary s)
    {i j : Fin k} (c : Vec k) (hsupp : ∀ l, s l ≠ 0 → l = i ∨ l = j) :
    PyrUnion s c ⊆ {y | 0 ≤ s i * (y i - c i) + s j * (y j - c j)} := by
  rintro y ⟨l, hl_ne, hl_mem⟩
  rw [mem_Pyr] at hl_mem
  -- every coordinate's signed offset is `≥ −‖y−c‖∞`
  have lb : ∀ m, -(s m * (y m - c m)) ≤ linfDist y c := by
    intro m
    have h1 : s m * (-(y m - c m)) ≤ |(-(y m - c m))| := hs.mul_le_abs m _
    rw [mul_neg, abs_neg] at h1
    exact h1.trans (abs_sub_le_linfDist y c m)
  simp only [Set.mem_setOf_eq]
  rcases hsupp l hl_ne with rfl | rfl
  · have := lb j; rw [hl_mem]; linarith
  · have := lb i; rw [hl_mem]; linarith

/-- **Low dimension is convex.** For `d ≤ 2` a cut's support is trivially `≤ 2`,
so by `pyrUnion_subset_halfspace` every pyramid union lies in a halfspace. Hence
in dimension `≤ 2` the candidate region `X_t` (box ∩ halfspaces) is convex and the
`ℓ∞` fixed point is poly-time by cutting planes — the easy base case, and a sanity
check that the `|support| ≥ 3` non-convexity is genuinely what makes `d ≥ 3` hard. -/
theorem exists_pair_pyrUnion_subset_halfspace (hk : k ≤ 2) {s : Fin k → ℝ}
    (hs : IsTernary s) (c : Vec k) :
    ∃ i j : Fin k, PyrUnion s c ⊆ {y | 0 ≤ s i * (y i - c i) + s j * (y j - c j)} := by
  have h0 : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  refine ⟨⟨0, h0⟩, ⟨min 1 (k - 1), by omega⟩, pyrUnion_subset_halfspace hs c ?_⟩
  intro l _
  have hlt := l.isLt
  rcases Nat.lt_or_ge l.val 1 with h | h
  · left;  apply Fin.ext; simp only [Fin.val_mk]; omega
  · right; apply Fin.ext; simp only [Fin.val_mk]; omega

/-! ## The Kernel Theorem — star-shapedness about any kernel point

`starshaped_of_toward` shows that a point `xs` *toward* which every coordinate
offset is nonnegative is a star-center. The **pairwise kernel condition**
`∀ i j, 0 ≤ σᵢ(zᵢ−cᵢ) + σⱼ(zⱼ−cⱼ)` (with `σᵢ = signR (s i)`) phrases the kernel
`ker K(c,s)` (note §1, **KER**) over *pairs* of coordinates and applies to an
arbitrary candidate center `z`, not only the fixed point. The theorem below shows
any such `z` is a star-center of the pyramid union `K(c,s)`.

The pairwise sum at the diagonal `i = j` reads `0 ≤ 2·σᵢ(zᵢ−cᵢ)`, so as a
predicate on `z` this `Bool`-sign form is equivalent to the all-nonneg
hypothesis of `starshaped_of_toward`; the genuine content is the extension from
the fixed point to an arbitrary center, phrased in the kernel's pairwise shape.
The strictly weaker off-diagonal-only kernel `∀ i ≠ j, …` (the true `ker` in
`ℝ^d`, `d ≥ 2`) would need a nontrivial argmax-coincidence (`a = b`) argument and
is deliberately not attempted here. -/

/-- **Kernel Theorem.** If `z` satisfies the pairwise kernel condition
`∀ i j, 0 ≤ σᵢ(zᵢ−cᵢ) + σⱼ(zⱼ−cⱼ)`, then `z` is a star-center of `K(c,s)`: for
every `y ∈ K(c,s)` and every `t ∈ [0,1]`, the point `(1−t)•z + t•y` lies in
`K(c,s)`. Generalizes `starshaped_of_toward` from the fixed point to an arbitrary
center. -/
theorem starshaped_of_kernel {s : Fin k → Bool} {c z : Vec k}
    (hkernel : ∀ i j, 0 ≤ signR (s i) * (z i - c i) + signR (s j) * (z j - c j))
    {y : Vec k} (hy : ∃ i, y ∈ Pyramid i (s i) c)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∃ i, (fun j => (1 - t) * z j + t * y j) ∈ Pyramid i (s i) c := by
  have h1t : 0 ≤ 1 - t := by linarith
  set q : Vec k := fun j => (1 - t) * z j + t * y j with hq
  have hqj : ∀ j, q j = (1 - t) * z j + t * y j := fun j => by rw [hq]
  rw [mem_pyramidUnion_iff] at hy ⊢
  -- `a` : argmax of the `+`-side of `y`; `b` : argmax of the `−`-side of `q`.
  obtain ⟨a, ha⟩ := exists_eq_sgnSup s c y
  obtain ⟨b, hb⟩ := exists_eq_sgnSup s q c
  -- The `(a, b)` pair of `+`-offsets at `y` is nonnegative (from `y ∈ K`):
  -- `−wᵦ(y) ≤ sgnSup s y c ≤ sgnSup s c y = wₐ(y)`.
  have hyab : 0 ≤ signR (s a) * (y a - c a) + signR (s b) * (y b - c b) := by
    have h3 : signR (s b) * (c b - y b) ≤ sgnSup s y c := le_sgnSup s y c b
    have e : signR (s b) * (c b - y b) = -(signR (s b) * (y b - c b)) := by ring
    rw [e] at h3
    linarith [ha, hy, h3]
  -- The `(a, b)` pair of `+`-offsets at `z` is nonnegative (kernel condition;
  -- the diagonal `a = b` case is covered since `hkernel` ranges over all pairs).
  have hzab := hkernel a b
  -- Reduce the goal `sgnSup s q c ≤ sgnSup s c q` to a single pairwise
  -- inequality at `q`, then combine the two nonnegative pairs with `t, 1−t`.
  rw [← hb]
  refine le_trans ?_ (le_sgnSup s c q a)
  have ea : signR (s a) * (q a - c a)
      = (1 - t) * (signR (s a) * (z a - c a)) + t * (signR (s a) * (y a - c a)) := by
    rw [hqj a]; ring
  have eb : signR (s b) * (c b - q b)
      = -((1 - t) * (signR (s b) * (z b - c b)) + t * (signR (s b) * (y b - c b))) := by
    rw [hqj b]; ring
  rw [ea, eb]
  nlinarith [mul_nonneg h1t hzab, mul_nonneg ht0 hyab]

/-- Kernel star-shapedness for a whole family of cuts: if `z` is a kernel point
of every cut `(c r, s r)` and `y` lies in every `K(c r, s r)`, then the segment
from `z` to `y` does too. Intersecting with the (convex) box gives that the
candidate body is star-shaped about any common kernel point. -/
theorem starshaped_of_kernel_family {ι : Type*} {cs : ι → Vec k}
    {ss : ι → (Fin k → Bool)} {z : Vec k}
    (hkernel : ∀ r i j,
      0 ≤ signR (ss r i) * (z i - cs r i) + signR (ss r j) * (z j - cs r j))
    {y : Vec k} (hy : ∀ r, ∃ i, y ∈ Pyramid i (ss r i) (cs r))
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∀ r, ∃ i, (fun j => (1 - t) * z j + t * y j) ∈ Pyramid i (ss r i) (cs r) :=
  fun r => starshaped_of_kernel (hkernel r) (hy r) ht0 ht1

/-! ## σ = 1: single-sign cuts are star-shaped about a known corner

If *every* cut uses the same sign vector `s` (the σ=1 regime of
`notes/sigma_scaling.md`), the candidate body is star-shaped about the **known**
box corner `ĉ` with `ĉ_i = 1` if `s_i` else `0` — for *any* apexes in the cube,
with no condition on the fixed point. Hence it is exactly ray-shootable
(poly-time samplable), isoperimetry-free. This is a direct corollary of
`starshaped_of_kernel_family`: `ĉ` is a universal kernel point because each
signed offset `signR(s_i)·(ĉ_i − c_i)` is `1 − c_i ≥ 0` (when `s_i`) or
`c_i ≥ 0` (when `¬s_i`). -/
theorem starshaped_of_single_sign {s : Fin k → Bool} {cc : Vec k}
    (hc : ∀ i, cc i = if s i then 1 else 0)
    {ι : Type*} {cs : ι → Vec k} (hbox : ∀ r, InUnitCube (cs r))
    {y : Vec k} (hy : ∀ r, ∃ i, y ∈ Pyramid i (s i) (cs r))
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∀ r, ∃ i, (fun j => (1 - t) * cc j + t * y j) ∈ Pyramid i (s i) (cs r) := by
  -- Each signed offset of `ĉ` from any cube apex is nonnegative.
  have hterm : ∀ r i, 0 ≤ signR (s i) * (cc i - cs r i) := by
    intro r i
    obtain ⟨hlo, hhi⟩ := Set.mem_Icc.mp (hbox r i)
    rw [hc i]
    unfold signR
    split_ifs with h
    · nlinarith [hhi]
    · nlinarith [hlo]
  exact starshaped_of_kernel_family (ss := fun _ => s) (z := cc)
    (fun r i j => by linarith [hterm r i, hterm r j]) hy ht0 ht1

end Tfnp.Contraction
