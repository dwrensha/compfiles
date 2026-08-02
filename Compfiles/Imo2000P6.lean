/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 2000, Problem 6

Let A₁A₂A₃ be an acute-angled triangle. The foot of the altitude from Aᵢ is Kᵢ
and the incircle touches the side opposite Aᵢ at Lᵢ. The line K₁K₂ is reflected
in the line L₁L₂. Similarly, the line K₂K₃ is reflected in L₂L₃ and K₃K₁ is
reflected in L₃L₁. Show that the three new lines form a triangle with vertices
on the incircle.
-/

namespace Imo2000P6

/-- The Euclidean plane. -/
abbrev E := EuclideanSpace ℝ (Fin 2)

snip begin

/-- Dot product, computed in coordinates. -/
def dotP (u v : E) : ℝ := u 0 * v 0 + u 1 * v 1

/-- 2-dimensional cross product (determinant), computed in coordinates. -/
def crossP (u v : E) : ℝ := u 0 * v 1 - u 1 * v 0

/-- The tangent lines to the unit circle at the unit vectors `Lj` and `Lk`
meet at the point `ptA Lj Lk`. This is a vertex of the triangle determined
by the three touch points. -/
noncomputable def ptA (Lj Lk : E) : E := (1 + dotP Lj Lk)⁻¹ • (Lj + Lk)

/-- The foot of the perpendicular from `Ai` to the line `⟨x, Li⟩ = 1`.
When `Li` is a unit vector, that line is the tangent line to the unit circle
at `Li`, i.e. the side of the triangle opposite the vertex `Ai`,
so `ptK Ai Li` is the foot of the altitude from `Ai`. -/
noncomputable def ptK (Ai Li : E) : E := Ai + (1 - dotP Ai Li) • Li

/-- Reflection of the point `x` in the line through `p` with normal vector `n`. -/
noncomputable def nrefl (p n x : E) : E := x - (2 * dotP (x - p) n / dotP n n) • n

/-- Reflection of the point `x` in the line through the unit vectors `Li` and `Lj`;
that chord line has normal `Li + Lj` because `|Li| = |Lj|`. -/
noncomputable def chordRefl (Li Lj x : E) : E := nrefl Li (Li + Lj) x

/-- The reflection of `Li` in the line through the origin and `ptA Lj Lk`
(the angle bisector at the corresponding vertex). These are the three points
that witness the conclusion of the problem. -/
noncomputable def ptM (Li Lj Lk : E) : E :=
  (2 * dotP Li (Lj + Lk) / dotP (Lj + Lk) (Lj + Lk)) • (Lj + Lk) - Li

/-- The vertex of the triangle opposite the touch point `L i`: the intersection
of the tangent lines at the other two touch points. -/
noncomputable def vtx (L : Fin 3 → E) (i : Fin 3) : E := ptA (L (i + 1)) (L (i + 2))

/-- The foot of the altitude from `vtx L i`. -/
noncomputable def foot (L : Fin 3 → E) (i : Fin 3) : E := ptK (vtx L i) (L i)

/-! ### Basic coordinate algebra -/

lemma ext2 {u v : E} (h0 : u 0 = v 0) (h1 : u 1 = v 1) : u = v := by
  apply PiLp.ext; intro i; fin_cases i
  · exact h0
  · exact h1

lemma dotP_comm (u v : E) : dotP u v = dotP v u := by simp [dotP]; ring

lemma dotP_add (u v w : E) : dotP (u + v) w = dotP u w + dotP v w := by
  simp [dotP, PiLp.add_apply]; ring

lemma dotP_add_right (u v w : E) : dotP u (v + w) = dotP u v + dotP u w := by
  simp [dotP, PiLp.add_apply]; ring

lemma dotP_sub (u v w : E) : dotP (u - v) w = dotP u w - dotP v w := by
  simp [dotP, PiLp.sub_apply]; ring

lemma dotP_sub_right (u v w : E) : dotP u (v - w) = dotP u v - dotP u w := by
  simp [dotP, PiLp.sub_apply]; ring

lemma dotP_smul (c : ℝ) (u v : E) : dotP (c • u) v = c * dotP u v := by
  simp [dotP, PiLp.smul_apply]; ring

lemma dotP_smul_right (c : ℝ) (u v : E) : dotP u (c • v) = c * dotP u v := by
  simp [dotP, PiLp.smul_apply]; ring

lemma dotP_neg (u v : E) : dotP (-u) v = -dotP u v := by
  simp [dotP, PiLp.neg_apply]; ring

lemma dotP_neg_right (u v : E) : dotP u (-v) = -dotP u v := by
  simp [dotP, PiLp.neg_apply]; ring

lemma crossP_comm (u v : E) : crossP u v = -crossP v u := by simp [crossP]; ring

lemma crossP_sub_left (u v w : E) : crossP (u - v) w = crossP u w - crossP v w := by
  simp [crossP, PiLp.sub_apply]; ring

lemma crossP_sub_right (u v w : E) : crossP u (v - w) = crossP u v - crossP u w := by
  simp [crossP, PiLp.sub_apply]; ring

lemma dotP_self_nonneg (u : E) : 0 ≤ dotP u u := by
  simp [dotP]; nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]

lemma dotP_self_eq_zero {u : E} (h : dotP u u = 0) : u = 0 := by
  simp [dotP] at h
  have h0 : u 0 = 0 := by nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]
  have h1 : u 1 = 0 := by nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]
  exact ext2 h0 h1

lemma norm_eq_one_of_dotP (u : E) (h : dotP u u = 1) : ‖u‖ = 1 := by
  have h2 : (u 0) ^ 2 + (u 1) ^ 2 = 1 := by
    simp only [dotP] at h; nlinarith [h]
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.norm_eq_abs, Real.norm_eq_abs,
    sq_abs, sq_abs, h2, Real.sqrt_one]

lemma dotP_of_norm_eq_one (u : E) (h : ‖u‖ = 1) : dotP u u = 1 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.norm_eq_abs, Real.norm_eq_abs,
    sq_abs, sq_abs] at h
  have h2 := congrArg (· ^ 2) h
  rw [Real.sq_sqrt (by positivity)] at h2
  simp only [dotP]; nlinarith [h2]

lemma dotP_eq_neg_one_iff {u v : E} (hu : dotP u u = 1) (hv : dotP v v = 1) :
    dotP u v = -1 ↔ v = -u := by
  constructor
  · intro h
    have hw : dotP (u + v) (u + v) = 0 := by
      simp only [dotP_add, dotP_add_right, hu, hv, dotP_comm v u, h]; ring
    have h2 : u + v = 0 := dotP_self_eq_zero hw
    rw [add_eq_zero_iff_eq_neg] at h2
    rw [h2, neg_neg]
  · intro h; rw [h, dotP_neg_right, hu]

lemma dotP_add_self {u v : E} (hu : dotP u u = 1) (hv : dotP v v = 1) :
    dotP (u + v) (u + v) = 2 + 2 * dotP u v := by
  simp only [dotP_add, dotP_add_right, hu, hv, dotP_comm v u]; ring

/-! ### Reflection and affine spans -/

lemma nrefl_twice {n : E} (hn : dotP n n ≠ 0) (p x : E) : nrefl p n (nrefl p n x) = x := by
  have h1 : 2 * dotP (nrefl p n x - p) n / dotP n n = -(2 * dotP (x - p) n / dotP n n) := by
    simp only [nrefl, dotP_sub, dotP_smul]
    rw [div_eq_iff hn, ← neg_div, div_mul_cancel₀ _ hn, div_mul_cancel₀ _ hn]
    ring
  conv_lhs => rw [nrefl, h1, nrefl]
  simp

lemma crossP_lin_smul_sub (d e n : E) (α β : ℝ) :
    crossP (d - α • n) (e - β • n) = crossP d e - α * crossP n e - β * crossP d n := by
  simp only [crossP, PiLp.sub_apply, PiLp.smul_apply]; ring

lemma nrefl_sub (p n u v : E) :
    nrefl p n u - nrefl p n v = (u - v) - (2 * dotP (u - v) n / dotP n n) • n := by
  apply ext2 <;>
    simp only [nrefl, dotP, PiLp.sub_apply, PiLp.smul_apply] <;>
    ring

lemma crossP_nrefl {n : E} (hn : dotP n n ≠ 0) (p u v w z : E) :
    crossP (nrefl p n u - nrefl p n v) (nrefl p n w - nrefl p n z) =
      -crossP (u - v) (w - z) := by
  have key : (2 * dotP (u - v) n) * crossP n (w - z) +
      (2 * dotP (w - z) n) * crossP (u - v) n =
      2 * dotP n n * crossP (u - v) (w - z) := by
    simp only [crossP, dotP, PiLp.sub_apply]; ring
  have g : (2 * dotP (u - v) n / dotP n n) * crossP n (w - z) +
      (2 * dotP (w - z) n / dotP n n) * crossP (u - v) n = 2 * crossP (u - v) (w - z) := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, key]
    field_simp
  rw [nrefl_sub, nrefl_sub, crossP_lin_smul_sub]
  linear_combination -g

lemma nrefl_combo (p n a v : E) (t : ℝ) :
    nrefl p n (a + t • v) = nrefl p n a + t • (nrefl p n (a + v) - nrefl p n a) := by
  apply ext2 <;>
    simp only [nrefl, dotP, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply] <;>
    ring

lemma lineMap_eq_add_smul (a b : E) (t : ℝ) :
    AffineMap.lineMap a b t = a + t • (b - a) := by
  rw [AffineMap.lineMap_apply, vadd_eq_add, vsub_eq_sub]; module

lemma mem_affineSpan_pair_of_cross {a b p : E} (h : crossP (b - a) (p - a) = 0)
    (hab : a ≠ b) : p ∈ affineSpan ℝ {a, b} := by
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
  have hne : (b - a) 0 ≠ 0 ∨ (b - a) 1 ≠ 0 := by
    by_contra hc; push Not at hc
    apply hab; apply ext2
    · have h0 : b 0 - a 0 = 0 := by
        have g := hc.1; rwa [PiLp.sub_apply] at g
      linarith
    · have h1 : b 1 - a 1 = 0 := by
        have g := hc.2; rwa [PiLp.sub_apply] at g
      linarith
  simp only [crossP, PiLp.sub_apply] at h
  rcases hne with h0 | h0
  · refine ⟨(p - a) 0 / (b - a) 0, ?_⟩
    rw [lineMap_eq_add_smul]
    simp only [PiLp.sub_apply] at h0
    have h' : (p 0 - a 0) * (b 1 - a 1) = (p 1 - a 1) * (b 0 - a 0) := by
      linear_combination -h
    apply ext2 <;>
      simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    · rw [div_mul_cancel₀ _ h0]; ring
    · rw [div_mul_eq_mul_div, h', mul_div_cancel_right₀ _ h0]; ring
  · refine ⟨(p - a) 1 / (b - a) 1, ?_⟩
    rw [lineMap_eq_add_smul]
    simp only [PiLp.sub_apply] at h0
    have h' : (p 1 - a 1) * (b 0 - a 0) = (p 0 - a 0) * (b 1 - a 1) := by
      linear_combination h
    apply ext2 <;>
      simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    · rw [div_mul_eq_mul_div, h', mul_div_cancel_right₀ _ h0]; ring
    · rw [div_mul_cancel₀ _ h0]; ring

lemma span_pair_le_of_mem {a b c d : E} (ha : a ∈ affineSpan ℝ {c, d})
    (hb : b ∈ affineSpan ℝ {c, d}) :
    affineSpan ℝ {a, b} ≤ affineSpan ℝ {c, d} := by
  rw [affineSpan_le, Set.pair_subset_iff]; exact ⟨ha, hb⟩

lemma span_pair_eq_span_pair_of_mem {a b c d : E} (hab : a ≠ b)
    (ha : a ∈ affineSpan ℝ {c, d}) (hb : b ∈ affineSpan ℝ {c, d}) :
    affineSpan ℝ {a, b} = affineSpan ℝ {c, d} := by
  apply le_antisymm
  · exact span_pair_le_of_mem ha hb
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq] at ha hb
  obtain ⟨t0, ha⟩ := ha
  obtain ⟨t1, hb⟩ := hb
  rw [← ha, ← hb] at hab
  have ht : t0 ≠ t1 := by rintro rfl; exact hab rfl
  have ht' : t0 - t1 ≠ 0 := sub_ne_zero.mpr ht
  rw [affineSpan_le, Set.pair_subset_iff]
  have key : ∀ (s : ℝ), s • (b -ᵥ a) +ᵥ a = AffineMap.lineMap c d (t0 + s * (t1 - t0)) := by
    intro s
    rw [← ha, ← hb]
    rw [AffineMap.lineMap_apply, AffineMap.lineMap_apply, AffineMap.lineMap_apply]
    apply ext2 <;>
      simp only [vadd_eq_add, vsub_eq_sub, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply] <;>
      ring
  constructor
  · rw [SetLike.mem_coe, mem_affineSpan_pair_iff_exists_lineMap_eq]
    refine ⟨t0 / (t0 - t1), ?_⟩
    rw [AffineMap.lineMap_apply, key]
    have h0 : t0 + t0 / (t0 - t1) * (t1 - t0) = 0 := by field_simp; ring
    rw [h0]
    simp [AffineMap.lineMap_apply]
  · rw [SetLike.mem_coe, mem_affineSpan_pair_iff_exists_lineMap_eq]
    refine ⟨(t0 - 1) / (t0 - t1), ?_⟩
    rw [AffineMap.lineMap_apply, key]
    have h1 : t0 + (t0 - 1) / (t0 - t1) * (t1 - t0) = 1 := by field_simp; ring
    rw [h1]
    simp [AffineMap.lineMap_apply]

lemma image_span_pair {Li Lj a b : E} :
    chordRefl Li Lj '' (affineSpan ℝ {a, b}) =
      affineSpan ℝ {chordRefl Li Lj a, chordRefl Li Lj b} := by
  ext x; constructor
  · rintro ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, mem_affineSpan_pair_iff_exists_lineMap_eq] at hy ⊢
    obtain ⟨t, rfl⟩ := hy
    refine ⟨t, ?_⟩
    rw [lineMap_eq_add_smul, lineMap_eq_add_smul]
    simp only [chordRefl]
    rw [nrefl_combo, show a + (b - a) = b from by module]
  · intro hx
    rw [SetLike.mem_coe, mem_affineSpan_pair_iff_exists_lineMap_eq] at hx
    obtain ⟨t, rfl⟩ := hx
    refine ⟨AffineMap.lineMap a b t, ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_affineSpan_pair_iff_exists_lineMap_eq]; exact ⟨t, rfl⟩
    · rw [lineMap_eq_add_smul, lineMap_eq_add_smul]
      simp only [chordRefl]
      rw [nrefl_combo, show a + (b - a) = b from by module]

lemma nrefl_image_image {n : E} (hn : dotP n n ≠ 0) (p : E) (s : Set E) :
    nrefl p n '' (nrefl p n '' s) = s := by
  ext x; constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, h2⟩
    rw [← h2, nrefl_twice hn]; exact hz
  · intro hx
    exact ⟨nrefl p n x, ⟨x, hx, rfl⟩, nrefl_twice hn p x⟩

lemma chordRefl_comm {Li Lj : E} (hi : dotP Li Li = 1) (hj : dotP Lj Lj = 1) (x : E) :
    chordRefl Li Lj x = chordRefl Lj Li x := by
  have h : dotP (x - Li) (Li + Lj) = dotP (x - Lj) (Li + Lj) := by
    simp only [dotP_sub, dotP_add_right, hi, hj, dotP_comm Lj Li]; ring
  simp only [chordRefl, nrefl, add_comm Lj Li, h]

lemma chordRefl_fun_comm {Li Lj : E} (hi : dotP Li Li = 1) (hj : dotP Lj Lj = 1) :
    chordRefl Li Lj = chordRefl Lj Li :=
  funext (chordRefl_comm hi hj)

lemma ptA_comm (u v : E) : ptA u v = ptA v u := by
  simp only [ptA, dotP_comm u v, add_comm u v]

lemma ptM_comm (Li Lj Lk : E) : ptM Li Lj Lk = ptM Li Lk Lj := by
  simp only [ptM, add_comm Lj Lk]

/-! ### Negation equivariance -/

lemma ptA_neg (u v : E) : ptA (-u) (-v) = -ptA u v := by
  simp only [ptA, dotP_neg, dotP_neg_right, neg_neg]
  module

lemma ptK_neg (A L : E) : ptK (-A) (-L) = -ptK A L := by
  simp only [ptK, dotP_neg, dotP_neg_right, neg_neg]
  module

lemma nrefl_neg (p n x : E) : nrefl (-p) (-n) (-x) = -nrefl p n x := by
  simp only [nrefl, sub_neg_eq_add, dotP_add, dotP_neg, dotP_neg_right, dotP_sub, neg_neg]
  module

lemma chordRefl_neg (Li Lj x : E) : chordRefl (-Li) (-Lj) (-x) = -chordRefl Li Lj x := by
  have h : -Li + -Lj = -(Li + Lj) := by module
  simp only [chordRefl, h, nrefl_neg]

lemma ptM_neg (Li Lj Lk : E) : ptM (-Li) (-Lj) (-Lk) = -ptM Li Lj Lk := by
  have h : -Lj + -Lk = -(Lj + Lk) := by module
  simp only [ptM, h, dotP_neg, dotP_neg_right, neg_neg]
  module

/-! ### The Cayley parametrization of the unit circle -/

/-- Stereographic parametrization of the unit circle minus `(-1, 0)`:
`LP t = ((1 - t²)/(1 + t²), 2t/(1 + t²))`. -/
noncomputable def LP (t : ℝ) : E := !₂[(1 - t^2) / (1 + t^2), 2 * t / (1 + t^2)]

lemma one_add_dotP_LP (s t : ℝ) :
    1 + dotP (LP s) (LP t) = 2 * (1 + s * t)^2 / ((1 + s^2) * (1 + t^2)) := by
  simp [LP, dotP]; field_simp; ring

lemma dotP_LP_add (s t : ℝ) :
    dotP (LP s + LP t) (LP s + LP t) = 4 * (1 + s * t)^2 / ((1 + s^2) * (1 + t^2)) := by
  simp only [dotP, PiLp.add_apply, LP, Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp; ring

lemma dotP_LP_self (t : ℝ) : dotP (LP t) (LP t) = 1 := by
  simp [LP, dotP]; field_simp; ring

lemma crossP_LP (s t : ℝ) :
    crossP (LP s) (LP t) = 2 * (t - s) * (1 + s * t) / ((1 + s^2) * (1 + t^2)) := by
  simp [LP, crossP]; field_simp; ring

lemma LP_inj {s t : ℝ} (h : LP s = LP t) : s = t := by
  have h0 := congrArg (· 0) h
  have h1 := congrArg (· 1) h
  simp only [LP, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  have g0 : (1 - s^2) * (1 + t^2) = (1 - t^2) * (1 + s^2) := by
    have h0' := h0
    field_simp at h0'
    linear_combination h0'
  have g1 : s * (1 + t^2) = t * (1 + s^2) := by
    have h1' := h1
    field_simp at h1'
    linear_combination h1'
  have h2 : t ^ 2 = s ^ 2 := by linarith [g0]
  have h3 : (s - t) * (1 - s * t) = 0 := by linarith [g1]
  rcases mul_eq_zero.mp h3 with hst | hst
  · linarith [hst]
  · by_cases hst2 : s = t
    · exact hst2
    · exfalso
      have ht : t = -s := by
        have h4 : (t - s) * (t + s) = 0 := by linarith [h2]
        rcases mul_eq_zero.mp h4 with h5 | h5
        · exact absurd (by linarith [h5] : s = t) hst2
        · linarith [h5]
      rw [ht] at hst
      nlinarith [hst, sq_nonneg s]

lemma exists_LP {p : E} (hp : dotP p p = 1) (hp0 : p 0 ≠ -1) : ∃ t, p = LP t := by
  have h1 : 1 + p 0 ≠ 0 := by intro h; apply hp0; linarith [h]
  have hs : (p 0) ^ 2 + (p 1) ^ 2 = 1 := by
    simp only [dotP] at hp; nlinarith [hp]
  refine ⟨p 1 / (1 + p 0), ?_⟩
  have h2 : (p 1) ^ 2 = (1 - p 0) * (1 + p 0) := by nlinarith [hs]
  have ht2 : (p 1 / (1 + p 0)) ^ 2 = (1 - p 0) / (1 + p 0) := by
    rw [div_pow, h2]
    field_simp
  apply ext2
  · simp only [LP, Matrix.cons_val_zero]
    rw [ht2]
    field_simp
    ring
  · simp only [LP, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [ht2]
    field_simp
    ring

lemma one_add_mul_ne_zero {p q : E} (hp : dotP p p = 1) (hq : dotP q q = 1)
    (hp0 : p 0 ≠ -1) (hq0 : q 0 ≠ -1) (h : q ≠ -p) :
    1 + (p 1 / (1 + p 0)) * (q 1 / (1 + q 0)) ≠ 0 := by
  have h1p : 1 + p 0 ≠ 0 := by intro hh; apply hp0; linarith [hh]
  have h1q : 1 + q 0 ≠ 0 := by intro hh; apply hq0; linarith [hh]
  simp only [dotP] at hp hq
  intro hh
  have key : (1 + p 0) * (1 + q 0) + p 1 * q 1 = 0 := by
    field_simp at hh
    linarith [hh]
  have hp1 : (p 1) ^ 2 = (1 - p 0) * (1 + p 0) := by nlinarith [hp]
  have hq1 : (q 1) ^ 2 = (1 - q 0) * (1 + q 0) := by nlinarith [hq]
  have hsq : (p 1 * q 1) ^ 2 = ((1 + p 0) * (1 + q 0)) ^ 2 := by
    have h9 : p 1 * q 1 = -((1 + p 0) * (1 + q 0)) := by linarith [key]
    rw [h9]; ring
  have e2 : (1 - p 0) * (1 - q 0) = (1 + p 0) * (1 + q 0) := by
    have e3 : (p 1) ^ 2 * (q 1) ^ 2 = ((1 + p 0) * (1 + q 0)) ^ 2 := by
      rw [← hsq]; ring
    rw [hp1, hq1] at e3
    have h4 : (1 + p 0) * (1 + q 0) ≠ 0 := mul_ne_zero h1p h1q
    have e4 : (1 - p 0) * (1 + p 0) * ((1 - q 0) * (1 + q 0)) =
        (1 + p 0) * (1 + q 0) * ((1 - p 0) * (1 - q 0)) := by ring
    have e5 : ((1 + p 0) * (1 + q 0)) ^ 2 =
        (1 + p 0) * (1 + q 0) * ((1 + p 0) * (1 + q 0)) := by ring
    rw [e4, e5] at e3
    exact mul_left_cancel₀ h4 e3
  have e6 : p 0 + q 0 = 0 := by linarith [e2]
  have e7 : q 0 = -p 0 := by linarith [e6]
  have e8 : p 1 * (q 1 + p 1) = 0 := by
    have h9 : p 1 * q 1 = -((1 + p 0) * (1 + q 0)) := by linarith [key]
    rw [e7] at h9
    linear_combination h9 + hp1
  rcases mul_eq_zero.mp e8 with hp10 | hq1p
  · have hp02 : (p 0) ^ 2 = 1 := by nlinarith [hp, hp10]
    have hpo : p 0 = 1 ∨ p 0 = -1 := by
      have h9 : (p 0 - 1) * (p 0 + 1) = 0 := by nlinarith [hp02]
      rcases mul_eq_zero.mp h9 with h9 | h9
      · left; linarith [h9]
      · right; linarith [h9]
    rcases hpo with hpp | hpp
    · exfalso; apply hq0; rw [e7, hpp]
    · exfalso; exact hp0 hpp
  · exfalso; apply h
    apply ext2
    · rw [e7]; simp [PiLp.neg_apply]
    · have h9 : q 1 = -p 1 := by linarith [hq1p]
      rw [h9]; simp [PiLp.neg_apply]

/-! ### The key algebraic identities (verified by computation) -/

/-- Closed form for the altitude foot `ptK (ptA (LP t1) (LP t3)) (LP t2)`. -/
lemma cf_ptK (t1 t2 t3 : ℝ) (h13 : 1 + t1 * t3 ≠ 0) :
    ptK (ptA (LP t1) (LP t3)) (LP t2) =
      !₂[-(t2^4*t1*t3 + t2^4 - 2*t2^3*t1 - 2*t2^3*t3 + 4*t2^2*t1*t3 - 4*t2^2 +
            2*t2*t1 + 2*t2*t3 - t1*t3 - 1) / ((t2^2+1)^2*(1+t1*t3)),
        (t2^4*t1 + t2^4*t3 + 4*t2^3 - 2*t2^2*t1 - 2*t2^2*t3 + 4*t2*t1*t3 + t1 + t3) /
          ((t2^2+1)^2*(1+t1*t3))] := by
  simp only [ptK, ptA]
  rw [one_add_dotP_LP]
  apply ext2 <;>
    simp only [dotP, PiLp.add_apply, PiLp.smul_apply, LP,
      Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul] <;>
    field_simp <;>
    ring

/-- Closed form for `ptM (LP t1) (LP t2) (LP t3)`. -/
lemma cf_ptM (t1 t2 t3 : ℝ) (h23 : 1 + t2 * t3 ≠ 0) :
    ptM (LP t1) (LP t2) (LP t3) =
      !₂[-((t1*t2*t3 - t1*t2 - t1*t3 - t1 + t2*t3 + t2 + t3 - 1) *
            (t1*t2*t3 + t1*t2 + t1*t3 - t1 - t2*t3 + t2 + t3 + 1)) /
          ((t1^2+1)*(t2^2+1)*(t3^2+1)),
        2*(t1*t2 + t1*t3 - t2*t3 + 1)*(t1*t2*t3 - t1 + t2 + t3) /
          ((t1^2+1)*(t2^2+1)*(t3^2+1))] := by
  have h23e : (1:ℝ) + t3 * t2 * 2 + t3 ^ 2 * t2 ^ 2 ≠ 0 := by
    have g : (1:ℝ) + t3 * t2 * 2 + t3 ^ 2 * t2 ^ 2 = (1 + t2 * t3)^2 := by ring
    rw [g]; exact pow_ne_zero 2 h23
  simp only [ptM]
  rw [dotP_LP_add]
  apply ext2 <;>
    simp only [dotP, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, LP,
      Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul] <;>
    field_simp <;>
    ring

/-- Closed form for the reflection of the altitude foot
`ptK (ptA (LP t1) (LP t3)) (LP t2)` in the chord line `LP t2 LP t3`. -/
lemma cf_refl_K (t1 t2 t3 : ℝ) (h13 : 1 + t1 * t3 ≠ 0) (h23 : 1 + t2 * t3 ≠ 0) :
    chordRefl (LP t2) (LP t3) (ptK (ptA (LP t1) (LP t3)) (LP t2)) =
      !₂[-(t1*t3 - 1)*(t2*t3 - t2 + t3 + 1)*(t2*t3 + t2 - t3 + 1) /
          ((t2^2+1)*(t3^2+1)*(1 + t1*t3)),
        (t1 + t3)*(t2*t3 - t2 + t3 + 1)*(t2*t3 + t2 - t3 + 1) /
          ((t2^2+1)*(t3^2+1)*(1 + t1*t3))] := by
  have h23e : (1:ℝ) + t3 * t2 * 2 + t3 ^ 2 * t2 ^ 2 ≠ 0 := by
    have g : (1:ℝ) + t3 * t2 * 2 + t3 ^ 2 * t2 ^ 2 = (1 + t2 * t3)^2 := by ring
    rw [g]; exact pow_ne_zero 2 h23
  rw [cf_ptK t1 t2 t3 h13]
  simp only [chordRefl, nrefl]
  rw [dotP_LP_add]
  apply ext2 <;>
    simp only [dotP, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, LP,
      Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul] <;>
    field_simp <;>
    ring

/-- First key identity: the reflection of `K₂` in the chord line `L₂L₃`
lies on the line `M₂M₃`. -/
lemma key_cross₁ (t1 t2 t3 : ℝ)
    (h12 : 1 + t1 * t2 ≠ 0) (h23 : 1 + t2 * t3 ≠ 0) (h13 : 1 + t1 * t3 ≠ 0) :
    crossP (chordRefl (LP t2) (LP t3) (ptK (ptA (LP t1) (LP t3)) (LP t2)) -
        ptM (LP t2) (LP t1) (LP t3))
      (ptM (LP t3) (LP t1) (LP t2) - ptM (LP t2) (LP t1) (LP t3)) = 0 := by
  rw [cf_refl_K t1 t2 t3 h13 h23, cf_ptM t2 t1 t3 h13, cf_ptM t3 t1 t2 h12]
  simp only [crossP, PiLp.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp
  ring

/-- Second key identity: the reflection of `K₃` in the chord line `L₂L₃`
lies on the line `M₂M₃`. -/
lemma key_cross₂ (t1 t2 t3 : ℝ)
    (h12 : 1 + t1 * t2 ≠ 0) (h23 : 1 + t2 * t3 ≠ 0) (h13 : 1 + t1 * t3 ≠ 0) :
    crossP (chordRefl (LP t2) (LP t3) (ptK (ptA (LP t1) (LP t2)) (LP t3)) -
        ptM (LP t2) (LP t1) (LP t3))
      (ptM (LP t3) (LP t1) (LP t2) - ptM (LP t2) (LP t1) (LP t3)) = 0 := by
  have hK3 : ptK (ptA (LP t1) (LP t2)) (LP t3) =
      !₂[-(t3^4*t1*t2 + t3^4 - 2*t3^3*t1 - 2*t3^3*t2 + 4*t3^2*t1*t2 - 4*t3^2 +
            2*t3*t1 + 2*t3*t2 - t1*t2 - 1) / ((t3^2+1)^2*(1+t1*t2)),
        (t3^4*t1 + t3^4*t2 + 4*t3^3 - 2*t3^2*t1 - 2*t3^2*t2 + 4*t3*t1*t2 + t1 + t2) /
          ((t3^2+1)^2*(1+t1*t2))] := cf_ptK t1 t3 t2 h12
  have hK3s : chordRefl (LP t2) (LP t3) (ptK (ptA (LP t1) (LP t2)) (LP t3)) =
      !₂[-(t1*t2 - 1)*(t2*t3 - t2 + t3 + 1)*(t2*t3 + t2 - t3 + 1) /
          ((t2^2+1)*(t3^2+1)*(1 + t1*t2)),
        (t1 + t2)*(t2*t3 - t2 + t3 + 1)*(t2*t3 + t2 - t3 + 1) /
          ((t2^2+1)*(t3^2+1)*(1 + t1*t2))] := by
    rw [hK3]
    simp only [chordRefl, nrefl]
    set D := dotP (LP t2 + LP t3) (LP t2 + LP t3) with hD
    have hd : D ≠ 0 := by
      rw [hD, dotP_LP_add]
      exact div_ne_zero (mul_ne_zero (by norm_num : (4:ℝ) ≠ 0) (pow_ne_zero 2 h23))
        (by positivity)
    apply ext2 <;>
      simp only [dotP, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, LP,
        Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul] <;>
      field_simp
    · rw [hD, dotP_LP_add]
      field_simp
      ring
    · rw [hD, dotP_LP_add]
      field_simp
      ring
  rw [hK3s, cf_ptM t2 t1 t3 h13, cf_ptM t3 t1 t2 h12]
  simp only [crossP, PiLp.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp
  ring

lemma key_M_norm (t1 t2 t3 : ℝ)
    (_h12 : 1 + t1 * t2 ≠ 0) (h23 : 1 + t2 * t3 ≠ 0) (_h13 : 1 + t1 * t3 ≠ 0) :
    dotP (ptM (LP t1) (LP t2) (LP t3)) (ptM (LP t1) (LP t2) (LP t3)) = 1 := by
  rw [cf_ptM t1 t2 t3 h23]
  simp only [dotP, Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp
  ring

lemma key_M_dist (t1 t2 t3 : ℝ)
    (h12 : 1 + t1 * t2 ≠ 0) (h23 : 1 + t2 * t3 ≠ 0) (h13 : 1 + t1 * t3 ≠ 0)
    (hd12 : t1 ≠ t2) :
    ptM (LP t1) (LP t2) (LP t3) ≠ ptM (LP t2) (LP t1) (LP t3) := by
  intro hM
  have hd : dotP (ptM (LP t1) (LP t2) (LP t3) - ptM (LP t2) (LP t1) (LP t3))
      (ptM (LP t1) (LP t2) (LP t3) - ptM (LP t2) (LP t1) (LP t3)) = 0 := by
    rw [hM]; simp [dotP]
  have hf : dotP (ptM (LP t1) (LP t2) (LP t3) - ptM (LP t2) (LP t1) (LP t3))
      (ptM (LP t1) (LP t2) (LP t3) - ptM (LP t2) (LP t1) (LP t3)) =
      16 * (t1 - t2)^2 * (1 + t1 * t2)^2 / (((t1^2+1)*(t2^2+1))^2) := by
    rw [cf_ptM t1 t2 t3 h23, cf_ptM t2 t1 t3 h13]
    simp only [dotP, PiLp.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp
    ring
  rw [hf] at hd
  have hne : 16 * (t1 - t2)^2 * (1 + t1 * t2)^2 / (((t1^2+1)*(t2^2+1))^2) ≠ 0 := by
    apply div_ne_zero
    · apply mul_ne_zero
      · apply mul_ne_zero (by norm_num : (16:ℝ) ≠ 0)
        exact pow_ne_zero 2 (sub_ne_zero.mpr hd12)
      · exact pow_ne_zero 2 h12
    · exact pow_ne_zero 2 (by positivity : ((t1^2+1)*(t2^2+1)) ≠ 0)
  exact hne hd

/-! ### Acuteness gives distinct altitude feet -/

lemma dotP_ptA {Lj Lk : E} (hj : dotP Lj Lj = 1) (hjk : dotP Lj Lk ≠ -1) :
    dotP (ptA Lj Lk) Lj = 1 := by
  have h1 : 1 + dotP Lj Lk ≠ 0 := by
    intro h0; exact hjk (by linarith [h0])
  show dotP ((1 + dotP Lj Lk)⁻¹ • (Lj + Lk)) Lj = 1
  rw [dotP_smul, dotP_add, hj, dotP_comm Lk Lj, inv_mul_cancel₀ h1]

lemma eq_of_dotP_eq_zero_of_crossP_ne_zero {w Li Lj : E}
    (hi : dotP w Li = 0) (hj : dotP w Lj = 0) (hc : crossP Li Lj ≠ 0) : w = 0 := by
  simp only [dotP, crossP] at hi hj hc
  have e0 : w 0 * (Li 0 * Lj 1 - Li 1 * Lj 0) =
      (w 0 * Li 0 + w 1 * Li 1) * Lj 1 - (w 0 * Lj 0 + w 1 * Lj 1) * Li 1 := by ring
  have e1 : w 1 * (Li 0 * Lj 1 - Li 1 * Lj 0) =
      (w 0 * Lj 0 + w 1 * Lj 1) * Li 0 - (w 0 * Li 0 + w 1 * Li 1) * Lj 0 := by ring
  rw [hi, hj] at e0 e1
  have h0 : w 0 = 0 := by
    have : w 0 * (Li 0 * Lj 1 - Li 1 * Lj 0) = 0 := by linear_combination e0
    exact (mul_eq_zero.mp this).resolve_right hc
  have h1 : w 1 = 0 := by
    have : w 1 * (Li 0 * Lj 1 - Li 1 * Lj 0) = 0 := by linear_combination e1
    exact (mul_eq_zero.mp this).resolve_right hc
  exact ext2 h0 h1

lemma dotP_ptA_right {Lj Lk : E} (hk : dotP Lk Lk = 1) (hjk : dotP Lj Lk ≠ -1) :
    dotP (ptA Lj Lk) Lk = 1 := by
  rw [ptA_comm]
  exact dotP_ptA hk (by rw [dotP_comm Lk Lj]; exact hjk)

lemma foot_ne_of_acute {l1 l2 l3 : E}
    (_h1 : dotP l1 l1 = 1) (h2 : dotP l2 l2 = 1) (h3 : dotP l3 l3 = 1)
    (hc23 : crossP l2 l3 ≠ 0)
    (hn12 : dotP l1 l2 ≠ -1) (_hn13 : dotP l1 l3 ≠ -1) (hn23 : dotP l2 l3 ≠ -1)
    (hD : 0 < dotP (ptA l1 l3 - ptA l2 l3) (ptA l1 l2 - ptA l2 l3)) :
    ptK (ptA l1 l3) l2 ≠ ptK (ptA l1 l2) l3 := by
  intro hK
  have hK2tan : dotP (ptK (ptA l1 l3) l2) l2 = 1 := by
    simp only [ptK, dotP_add, dotP_smul, h2]; ring
  have hK3tan : dotP (ptK (ptA l1 l2) l3) l3 = 1 := by
    simp only [ptK, dotP_add, dotP_smul, h3]; ring
  have hA1l2 : dotP (ptA l2 l3) l2 = 1 := dotP_ptA h2 hn23
  have hA1l3 : dotP (ptA l2 l3) l3 = 1 := dotP_ptA_right h3 hn23
  have hA3l2 : dotP (ptA l1 l2) l2 = 1 := dotP_ptA_right h2 hn12
  have hA1l2' : dotP l2 (ptA l2 l3) = 1 := by rw [dotP_comm]; exact hA1l2
  have hA3l2' : dotP l2 (ptA l1 l2) = 1 := by rw [dotP_comm]; exact hA3l2
  have hA1l3' : dotP l3 (ptA l2 l3) = 1 := by rw [dotP_comm]; exact hA1l3
  have hw2 : dotP (ptK (ptA l1 l2) l3 - ptA l2 l3) l2 = 0 := by
    rw [← hK, dotP_sub, hK2tan, hA1l2]; ring
  have hw3 : dotP (ptK (ptA l1 l2) l3 - ptA l2 l3) l3 = 0 := by
    rw [dotP_sub, hK3tan, hA1l3]; ring
  have hw := eq_of_dotP_eq_zero_of_crossP_ne_zero hw2 hw3 hc23
  have hP : ptK (ptA l1 l2) l3 = ptA l2 l3 := eq_of_sub_eq_zero hw
  have hA2 : ptA l1 l3 - ptA l2 l3 = (dotP (ptA l1 l3) l2 - 1) • l2 := by
    have h6 : ptK (ptA l1 l3) l2 = ptA l2 l3 := by rw [← hP, hK]
    simp only [ptK] at h6
    rw [← h6]; module
  have hD0 : dotP (ptA l1 l3 - ptA l2 l3) (ptA l1 l2 - ptA l2 l3) = 0 := by
    rw [hA2, dotP_smul, dotP_sub_right, hA3l2', hA1l2']; ring
  linarith [hD0, hD]

/-! ### Assembly -/

lemma line_image_eq_of_cross {Li Lj Ki Kj Mi Mj : E}
    (hn : dotP (Li + Lj) (Li + Lj) ≠ 0)
    (hc1 : crossP (chordRefl Li Lj Ki - Mi) (Mj - Mi) = 0)
    (hc2 : crossP (chordRefl Li Lj Kj - Mi) (Mj - Mi) = 0)
    (hM : Mi ≠ Mj) (hK : Ki ≠ Kj) :
    chordRefl Li Lj '' (affineSpan ℝ {Ki, Kj}) = affineSpan ℝ {Mi, Mj} := by
  have hc1' : crossP (Mj - Mi) (chordRefl Li Lj Ki - Mi) = 0 := by
    rw [crossP_comm, hc1, neg_zero]
  have hc2' : crossP (Mj - Mi) (chordRefl Li Lj Kj - Mi) = 0 := by
    rw [crossP_comm, hc2, neg_zero]
  have h1 : chordRefl Li Lj Ki ∈ affineSpan ℝ {Mi, Mj} :=
    mem_affineSpan_pair_of_cross hc1' hM
  have h2 : chordRefl Li Lj Kj ∈ affineSpan ℝ {Mi, Mj} :=
    mem_affineSpan_pair_of_cross hc2' hM
  have hne : chordRefl Li Lj Ki ≠ chordRefl Li Lj Kj := by
    intro hh
    apply hK
    have g := congrArg (chordRefl Li Lj) hh
    simp only [chordRefl, nrefl_twice hn] at g
    exact g
  have heq := span_pair_eq_span_pair_of_mem hne h1 h2
  rw [← heq]
  exact image_span_pair

lemma neg_image_span {a b : E} :
    (fun x : E => -x) '' (affineSpan ℝ {a, b}) = affineSpan ℝ {-a, -b} := by
  ext x; constructor
  · rintro ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, mem_affineSpan_pair_iff_exists_lineMap_eq] at hy ⊢
    obtain ⟨t, rfl⟩ := hy
    exact ⟨t, by rw [lineMap_eq_add_smul, lineMap_eq_add_smul]; module⟩
  · intro hx
    rw [SetLike.mem_coe, mem_affineSpan_pair_iff_exists_lineMap_eq] at hx
    obtain ⟨t, rfl⟩ := hx
    refine ⟨AffineMap.lineMap a b t, ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_affineSpan_pair_iff_exists_lineMap_eq]
      exact ⟨t, rfl⟩
    · rw [lineMap_eq_add_smul, lineMap_eq_add_smul]; module

lemma dotP_ne_neg_one_of_ne_neg {u v : E} (hu : dotP u u = 1) (hv : dotP v v = 1)
    (h : u ≠ -v) : dotP u v ≠ -1 := by
  intro hdot
  apply h
  have hv' := (dotP_eq_neg_one_iff hu hv).mp hdot
  rw [hv', neg_neg]

lemma one_add_mul_ne_zero_of_LP {s t : ℝ} (hdot : 1 + dotP (LP s) (LP t) ≠ 0) :
    1 + s * t ≠ 0 := by
  intro h0
  apply hdot
  rw [one_add_dotP_LP, h0]
  simp

lemma crossP_LP_ne_zero {s t : ℝ} (hd : s ≠ t) (h1 : 1 + s * t ≠ 0) :
    crossP (LP s) (LP t) ≠ 0 := by
  rw [crossP_LP]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (2:ℝ) ≠ 0)
    (sub_ne_zero.mpr (Ne.symm hd))) h1) (by positivity)

lemma dotP_LP_add_ne_zero {s t : ℝ} (h1 : 1 + s * t ≠ 0) :
    dotP (LP s + LP t) (LP s + LP t) ≠ 0 := by
  rw [dotP_LP_add]
  apply div_ne_zero
  · exact mul_ne_zero (by norm_num : (4:ℝ) ≠ 0) (pow_ne_zero 2 h1)
  · positivity

/-- The parametrized case of the main lemma: none of the touch points is `(-1, 0)`,
so the Cayley parametrization applies. -/
lemma main_aux_pos {l1 l2 l3 : E}
    (h1 : dotP l1 l1 = 1) (h2 : dotP l2 l2 = 1) (h3 : dotP l3 l3 = 1)
    (hd12 : l1 ≠ l2) (hd23 : l2 ≠ l3) (hd13 : l1 ≠ l3)
    (ha12 : l1 ≠ -l2) (ha23 : l2 ≠ -l3) (ha13 : l1 ≠ -l3)
    (hD1 : 0 < dotP (ptA l1 l3 - ptA l2 l3) (ptA l1 l2 - ptA l2 l3))
    (hD2 : 0 < dotP (ptA l2 l3 - ptA l1 l3) (ptA l1 l2 - ptA l1 l3))
    (hD3 : 0 < dotP (ptA l2 l3 - ptA l1 l2) (ptA l1 l3 - ptA l1 l2))
    (hp1 : l1 0 ≠ -1) (hp2 : l2 0 ≠ -1) (hp3 : l3 0 ≠ -1) :
    ∃ M1 M2 M3 : E,
      dotP M1 M1 = 1 ∧ dotP M2 M2 = 1 ∧ dotP M3 M3 = 1 ∧
      M1 ≠ M2 ∧ M2 ≠ M3 ∧ M1 ≠ M3 ∧
      chordRefl l2 l3 '' (affineSpan ℝ {ptK (ptA l1 l3) l2, ptK (ptA l1 l2) l3}) =
        affineSpan ℝ {M2, M3} ∧
      chordRefl l1 l3 '' (affineSpan ℝ {ptK (ptA l2 l3) l1, ptK (ptA l1 l2) l3}) =
        affineSpan ℝ {M1, M3} ∧
      chordRefl l1 l2 '' (affineSpan ℝ {ptK (ptA l2 l3) l1, ptK (ptA l1 l3) l2}) =
        affineSpan ℝ {M1, M2} := by
  obtain ⟨t1, rfl⟩ := exists_LP h1 hp1
  obtain ⟨t2, rfl⟩ := exists_LP h2 hp2
  obtain ⟨t3, rfl⟩ := exists_LP h3 hp3
  have hdot12 : 1 + dotP (LP t1) (LP t2) ≠ 0 := by
    have h9 := dotP_ne_neg_one_of_ne_neg h1 h2 ha12
    intro h0; exact h9 (by linarith [h0])
  have hdot23 : 1 + dotP (LP t2) (LP t3) ≠ 0 := by
    have h9 := dotP_ne_neg_one_of_ne_neg h2 h3 ha23
    intro h0; exact h9 (by linarith [h0])
  have hdot13 : 1 + dotP (LP t1) (LP t3) ≠ 0 := by
    have h9 := dotP_ne_neg_one_of_ne_neg h1 h3 ha13
    intro h0; exact h9 (by linarith [h0])
  have h12 : 1 + t1 * t2 ≠ 0 := one_add_mul_ne_zero_of_LP hdot12
  have h23 : 1 + t2 * t3 ≠ 0 := one_add_mul_ne_zero_of_LP hdot23
  have h13 : 1 + t1 * t3 ≠ 0 := one_add_mul_ne_zero_of_LP hdot13
  have ht12 : t1 ≠ t2 := by rintro rfl; exact hd12 rfl
  have ht23 : t2 ≠ t3 := by rintro rfl; exact hd23 rfl
  have ht13 : t1 ≠ t3 := by rintro rfl; exact hd13 rfl
  have hc23 : crossP (LP t2) (LP t3) ≠ 0 := crossP_LP_ne_zero ht23 h23
  have hc13 : crossP (LP t1) (LP t3) ≠ 0 := crossP_LP_ne_zero ht13 h13
  have hc12 : crossP (LP t1) (LP t2) ≠ 0 := crossP_LP_ne_zero ht12 h12
  have hn23 : dotP (LP t2) (LP t3) ≠ -1 := dotP_ne_neg_one_of_ne_neg h2 h3 ha23
  have hn12 : dotP (LP t1) (LP t2) ≠ -1 := dotP_ne_neg_one_of_ne_neg h1 h2 ha12
  have hn13 : dotP (LP t1) (LP t3) ≠ -1 := dotP_ne_neg_one_of_ne_neg h1 h3 ha13
  have hK23 : ptK (ptA (LP t1) (LP t3)) (LP t2) ≠ ptK (ptA (LP t1) (LP t2)) (LP t3) :=
    foot_ne_of_acute h1 h2 h3 hc23 hn12 hn13 hn23 hD1
  have hK13 : ptK (ptA (LP t2) (LP t3)) (LP t1) ≠ ptK (ptA (LP t1) (LP t2)) (LP t3) := by
    have g := foot_ne_of_acute h2 h1 h3 hc13
      (by rw [dotP_comm (LP t2) (LP t1)]; exact hn12) hn23 hn13
      (by rw [ptA_comm (LP t2) (LP t1)]; exact hD2)
    rw [ptA_comm (LP t2) (LP t1)] at g
    exact g
  have hK12 : ptK (ptA (LP t2) (LP t3)) (LP t1) ≠ ptK (ptA (LP t1) (LP t3)) (LP t2) := by
    have g := foot_ne_of_acute h3 h1 h2 hc12 (l1 := LP t3) (l2 := LP t1) (l3 := LP t2)
      (by rw [dotP_comm (LP t3) (LP t1)]; exact hn13)
      (by rw [dotP_comm (LP t3) (LP t2)]; exact hn23)
      hn12
      (by rw [ptA_comm (LP t3) (LP t1), ptA_comm (LP t3) (LP t2)]; exact hD3)
    rw [ptA_comm (LP t3) (LP t1), ptA_comm (LP t3) (LP t2)] at g
    exact g
  have hdM12' : ptM (LP t1) (LP t2) (LP t3) ≠ ptM (LP t2) (LP t1) (LP t3) :=
    key_M_dist t1 t2 t3 h12 h23 h13 ht12
  have hdM23' : ptM (LP t2) (LP t1) (LP t3) ≠ ptM (LP t3) (LP t1) (LP t2) := by
    rw [ptM_comm (LP t2) (LP t1) (LP t3), ptM_comm (LP t3) (LP t1) (LP t2)]
    exact key_M_dist t2 t3 t1 h23 (by rw [mul_comm t3 t1]; exact h13)
      (by rw [mul_comm t2 t1]; exact h12) ht23
  have hdM13' : ptM (LP t1) (LP t2) (LP t3) ≠ ptM (LP t3) (LP t1) (LP t2) := by
    rw [ptM_comm (LP t1) (LP t2) (LP t3)]
    exact key_M_dist t1 t3 t2 h13 (by rw [mul_comm t3 t2]; exact h23) h12 ht13
  have hc13c1 : crossP (chordRefl (LP t1) (LP t3) (ptK (ptA (LP t2) (LP t3)) (LP t1)) -
      ptM (LP t1) (LP t2) (LP t3))
      (ptM (LP t3) (LP t1) (LP t2) - ptM (LP t1) (LP t2) (LP t3)) = 0 := by
    rw [ptM_comm (LP t3) (LP t1) (LP t2)]
    exact key_cross₁ t2 t1 t3 (by rw [mul_comm t2 t1]; exact h12) h13 h23
  have hc13c2 : crossP (chordRefl (LP t1) (LP t3) (ptK (ptA (LP t1) (LP t2)) (LP t3)) -
      ptM (LP t1) (LP t2) (LP t3))
      (ptM (LP t3) (LP t1) (LP t2) - ptM (LP t1) (LP t2) (LP t3)) = 0 := by
    rw [ptA_comm (LP t1) (LP t2), ptM_comm (LP t3) (LP t1) (LP t2)]
    exact key_cross₂ t2 t1 t3 (by rw [mul_comm t2 t1]; exact h12) h13 h23
  have hc12c1 : crossP (chordRefl (LP t1) (LP t2) (ptK (ptA (LP t2) (LP t3)) (LP t1)) -
      ptM (LP t1) (LP t2) (LP t3))
      (ptM (LP t2) (LP t1) (LP t3) - ptM (LP t1) (LP t2) (LP t3)) = 0 := by
    rw [ptA_comm (LP t2) (LP t3), ptM_comm (LP t1) (LP t2) (LP t3),
      ptM_comm (LP t2) (LP t1) (LP t3)]
    exact key_cross₁ t3 t1 t2 (by rw [mul_comm t3 t1]; exact h13) h12
      (by rw [mul_comm t3 t2]; exact h23)
  have hc12c2 : crossP (chordRefl (LP t1) (LP t2) (ptK (ptA (LP t1) (LP t3)) (LP t2)) -
      ptM (LP t1) (LP t2) (LP t3))
      (ptM (LP t2) (LP t1) (LP t3) - ptM (LP t1) (LP t2) (LP t3)) = 0 := by
    rw [ptA_comm (LP t1) (LP t3), ptM_comm (LP t1) (LP t2) (LP t3),
      ptM_comm (LP t2) (LP t1) (LP t3)]
    exact key_cross₂ t3 t1 t2 (by rw [mul_comm t3 t1]; exact h13) h12
      (by rw [mul_comm t3 t2]; exact h23)
  refine ⟨ptM (LP t1) (LP t2) (LP t3), ptM (LP t2) (LP t1) (LP t3), ptM (LP t3) (LP t1) (LP t2),
    key_M_norm t1 t2 t3 h12 h23 h13,
    key_M_norm t2 t1 t3 (by rw [mul_comm t2 t1]; exact h12) h13 h23,
    key_M_norm t3 t1 t2 (by rw [mul_comm t3 t1]; exact h13) h12
      (by rw [mul_comm t3 t2]; exact h23),
    hdM12', hdM23', hdM13', ?_, ?_, ?_⟩
  · exact line_image_eq_of_cross (dotP_LP_add_ne_zero h23)
      (key_cross₁ t1 t2 t3 h12 h23 h13) (key_cross₂ t1 t2 t3 h12 h23 h13) hdM23' hK23
  · exact line_image_eq_of_cross (dotP_LP_add_ne_zero h13) hc13c1 hc13c2 hdM13' hK13
  · exact line_image_eq_of_cross (dotP_LP_add_ne_zero h12) hc12c1 hc12c2 hdM12' hK12

/-- Transport of a line equality through pointwise negation of the configuration. -/
lemma line_eq_neg_of_neg {l2 l3 K2 K3 M2 M3 : E}
    (h : chordRefl (-l2) (-l3) '' (affineSpan ℝ {-K2, -K3}) = affineSpan ℝ {M2, M3}) :
    chordRefl l2 l3 '' (affineSpan ℝ {K2, K3}) = affineSpan ℝ {-M2, -M3} := by
  have e1 : chordRefl (-l2) (-l3) '' (affineSpan ℝ {-K2, -K3}) =
      (fun z : E => -z) '' (chordRefl l2 l3 '' affineSpan ℝ {K2, K3}) := by
    ext z; constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : -y ∈ affineSpan ℝ {K2, K3} := by
        rw [← neg_image_span] at hy
        obtain ⟨z, hz, rfl⟩ := hy
        simpa using hz
      refine ⟨chordRefl l2 l3 (-y), ⟨-y, hy', rfl⟩, ?_⟩
      have e : chordRefl (-l2) (-l3) y = -chordRefl l2 l3 (-y) := by
        have g := chordRefl_neg l2 l3 (-y)
        rwa [neg_neg] at g
      exact e.symm
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨w, hw, rfl⟩ := hv
      refine ⟨-w, ?_, chordRefl_neg l2 l3 w⟩
      rw [← neg_image_span]
      exact ⟨w, hw, rfl⟩
  rw [e1] at h
  have hinj := congrArg (fun S : Set E => (fun z : E => -z) '' S) h
  rw [neg_image_span] at hinj
  simpa [Set.image_image] using hinj

lemma helper_coord_one {a b : E} (ha : dotP a a = 1) (hb : dotP b b = 1)
    (hab : a ≠ -b) (ha0 : a 0 = -1) : b 0 ≠ 1 := by
  intro hb0
  apply hab
  have ea1 : a 1 = 0 := by
    have hs : (a 0)^2 + (a 1)^2 = 1 := by simp only [dotP] at ha; nlinarith [ha]
    rw [ha0] at hs
    have h2' : (a 1)^2 = 0 := by nlinarith [hs]
    exact (pow_eq_zero_iff (by norm_num : (2:ℕ) ≠ 0)).mp h2'
  have eb1 : b 1 = 0 := by
    have hs : (b 0)^2 + (b 1)^2 = 1 := by simp only [dotP] at hb; nlinarith [hb]
    rw [hb0] at hs
    have h2' : (b 1)^2 = 0 := by nlinarith [hs]
    exact (pow_eq_zero_iff (by norm_num : (2:ℕ) ≠ 0)).mp h2'
  apply ext2
  · simp only [PiLp.neg_apply, ha0, hb0]
  · simp only [PiLp.neg_apply, ea1, eb1, neg_zero]

lemma main_aux {l1 l2 l3 : E}
    (h1 : dotP l1 l1 = 1) (h2 : dotP l2 l2 = 1) (h3 : dotP l3 l3 = 1)
    (hd12 : l1 ≠ l2) (hd23 : l2 ≠ l3) (hd13 : l1 ≠ l3)
    (ha12 : l1 ≠ -l2) (ha23 : l2 ≠ -l3) (ha13 : l1 ≠ -l3)
    (hD1 : 0 < dotP (ptA l1 l3 - ptA l2 l3) (ptA l1 l2 - ptA l2 l3))
    (hD2 : 0 < dotP (ptA l2 l3 - ptA l1 l3) (ptA l1 l2 - ptA l1 l3))
    (hD3 : 0 < dotP (ptA l2 l3 - ptA l1 l2) (ptA l1 l3 - ptA l1 l2)) :
    ∃ M1 M2 M3 : E,
      dotP M1 M1 = 1 ∧ dotP M2 M2 = 1 ∧ dotP M3 M3 = 1 ∧
      M1 ≠ M2 ∧ M2 ≠ M3 ∧ M1 ≠ M3 ∧
      chordRefl l2 l3 '' (affineSpan ℝ {ptK (ptA l1 l3) l2, ptK (ptA l1 l2) l3}) =
        affineSpan ℝ {M2, M3} ∧
      chordRefl l1 l3 '' (affineSpan ℝ {ptK (ptA l2 l3) l1, ptK (ptA l1 l2) l3}) =
        affineSpan ℝ {M1, M3} ∧
      chordRefl l1 l2 '' (affineSpan ℝ {ptK (ptA l2 l3) l1, ptK (ptA l1 l3) l2}) =
        affineSpan ℝ {M1, M2} := by
  by_cases hcase : l1 0 = -1 ∨ l2 0 = -1 ∨ l3 0 = -1
  · -- exceptional case: apply the parametrized case to the negated triple
    have hn1 : dotP (-l1) (-l1) = 1 := by rw [dotP_neg, dotP_neg_right, neg_neg, h1]
    have hn2 : dotP (-l2) (-l2) = 1 := by rw [dotP_neg, dotP_neg_right, neg_neg, h2]
    have hn3 : dotP (-l3) (-l3) = 1 := by rw [dotP_neg, dotP_neg_right, neg_neg, h3]
    have hnd12 : -l1 ≠ -l2 := fun hh => hd12 (neg_injective hh)
    have hnd23 : -l2 ≠ -l3 := fun hh => hd23 (neg_injective hh)
    have hnd13 : -l1 ≠ -l3 := fun hh => hd13 (neg_injective hh)
    have hna12 : -l1 ≠ -(-l2) := by
      rw [neg_neg]; intro hh; apply ha12; rw [← neg_neg l1, hh]
    have hna23 : -l2 ≠ -(-l3) := by
      rw [neg_neg]; intro hh; apply ha23; rw [← neg_neg l2, hh]
    have hna13 : -l1 ≠ -(-l3) := by
      rw [neg_neg]; intro hh; apply ha13; rw [← neg_neg l1, hh]
    have hnD1 : 0 < dotP (ptA (-l1) (-l3) - ptA (-l2) (-l3))
        (ptA (-l1) (-l2) - ptA (-l2) (-l3)) := by
      simp only [ptA_neg]
      rw [show (-ptA l1 l3) - -ptA l2 l3 = -(ptA l1 l3 - ptA l2 l3) from by module,
        show (-ptA l1 l2) - -ptA l2 l3 = -(ptA l1 l2 - ptA l2 l3) from by module,
        dotP_neg, dotP_neg_right, neg_neg]
      exact hD1
    have hnD2 : 0 < dotP (ptA (-l2) (-l3) - ptA (-l1) (-l3))
        (ptA (-l1) (-l2) - ptA (-l1) (-l3)) := by
      simp only [ptA_neg]
      rw [show (-ptA l2 l3) - -ptA l1 l3 = -(ptA l2 l3 - ptA l1 l3) from by module,
        show (-ptA l1 l2) - -ptA l1 l3 = -(ptA l1 l2 - ptA l1 l3) from by module,
        dotP_neg, dotP_neg_right, neg_neg]
      exact hD2
    have hnD3 : 0 < dotP (ptA (-l2) (-l3) - ptA (-l1) (-l2))
        (ptA (-l1) (-l3) - ptA (-l1) (-l2)) := by
      simp only [ptA_neg]
      rw [show (-ptA l2 l3) - -ptA l1 l2 = -(ptA l2 l3 - ptA l1 l2) from by module,
        show (-ptA l1 l3) - -ptA l1 l2 = -(ptA l1 l3 - ptA l1 l2) from by module,
        dotP_neg, dotP_neg_right, neg_neg]
      exact hD3
    have hnp1 : (-l1) 0 ≠ -1 := by
      intro hh
      simp only [PiLp.neg_apply] at hh
      have e1 : l1 0 = 1 := by linarith [hh]
      obtain h1e | h2e | h3e := hcase
      · linarith [h1e, e1]
      · exact helper_coord_one h2 h1 (by intro g; apply ha12; rw [← neg_neg l1, g]) h2e e1
      · exact helper_coord_one h3 h1 (by intro g; apply ha13; rw [← neg_neg l1, g]) h3e e1
    have hnp2 : (-l2) 0 ≠ -1 := by
      intro hh
      simp only [PiLp.neg_apply] at hh
      have e2 : l2 0 = 1 := by linarith [hh]
      obtain h1e | h2e | h3e := hcase
      · exact helper_coord_one h1 h2 ha12 h1e e2
      · linarith [h2e, e2]
      · exact helper_coord_one h3 h2 (by intro g; apply ha23; rw [← neg_neg l2, g]) h3e e2
    have hnp3 : (-l3) 0 ≠ -1 := by
      intro hh
      simp only [PiLp.neg_apply] at hh
      have e3 : l3 0 = 1 := by linarith [hh]
      obtain h1e | h2e | h3e := hcase
      · exact helper_coord_one h1 h3 ha13 h1e e3
      · exact helper_coord_one h2 h3 ha23 h2e e3
      · linarith [h3e, e3]
    obtain ⟨M1, M2, M3, hM1, hM2, hM3, hdM12, hdM23, hdM13, heq23, heq13, heq12⟩ :=
      main_aux_pos hn1 hn2 hn3 hnd12 hnd23 hnd13 hna12 hna23 hna13 hnD1 hnD2 hnD3 hnp1 hnp2 hnp3
    refine ⟨-M1, -M2, -M3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [dotP_neg, dotP_neg_right, neg_neg, hM1]
    · rw [dotP_neg, dotP_neg_right, neg_neg, hM2]
    · rw [dotP_neg, dotP_neg_right, neg_neg, hM3]
    · intro hh; apply hdM12; exact neg_injective hh
    · intro hh; apply hdM23; exact neg_injective hh
    · intro hh; apply hdM13; exact neg_injective hh
    · rw [ptA_neg, ptA_neg, ptK_neg, ptK_neg] at heq23
      exact line_eq_neg_of_neg heq23
    · rw [ptA_neg, ptA_neg, ptK_neg, ptK_neg] at heq13
      exact line_eq_neg_of_neg heq13
    · rw [ptA_neg, ptA_neg, ptK_neg, ptK_neg] at heq12
      exact line_eq_neg_of_neg heq12
  · push Not at hcase
    exact main_aux_pos h1 h2 h3 hd12 hd23 hd13 ha12 ha23 ha13 hD1 hD2 hD3
      hcase.1 hcase.2.1 hcase.2.2

snip end

set_option linter.unusedSimpArgs false
/-- The acuteness hypothesis, stated for a triangle given by the touch points
of its incircle: the angle at each vertex is acute. -/
problem imo2000_p6
    (L : Fin 3 → E)
    (hL : ∀ i, ‖L i‖ = 1)
    (hdist : ∀ i j, i ≠ j → L i ≠ L j)
    (hanti : ∀ i j, i ≠ j → L i ≠ -L j)
    (hacute : ∀ i, 0 < dotP (vtx L (i + 1) - vtx L i) (vtx L (i + 2) - vtx L i)) :
    ∃ M : Fin 3 → E,
      (∀ i, ‖M i‖ = 1) ∧
      (∀ i j, i ≠ j → M i ≠ M j) ∧
      (∀ i j, i ≠ j →
        chordRefl (L i) (L j) '' (affineSpan ℝ {foot L i, foot L j}) =
          affineSpan ℝ {M i, M j}) := by
  have h1 : dotP (L 0) (L 0) = 1 := dotP_of_norm_eq_one _ (hL 0)
  have h2 : dotP (L 1) (L 1) = 1 := dotP_of_norm_eq_one _ (hL 1)
  have h3 : dotP (L 2) (L 2) = 1 := dotP_of_norm_eq_one _ (hL 2)
  have e01 : (0 : Fin 3) + 1 = 1 := by decide
  have e02 : (0 : Fin 3) + 2 = 2 := by decide
  have e11 : (1 : Fin 3) + 1 = 2 := by decide
  have e12 : (1 : Fin 3) + 2 = 0 := by decide
  have e21 : (2 : Fin 3) + 1 = 0 := by decide
  have e22 : (2 : Fin 3) + 2 = 1 := by decide
  have hD1 : 0 < dotP (ptA (L 0) (L 2) - ptA (L 1) (L 2)) (ptA (L 0) (L 1) - ptA (L 1) (L 2)) := by
    have h := hacute 0
    rw [e01, e02] at h
    simp only [vtx, e11, e12, e01, e02, e21, e22] at h
    rw [ptA_comm (L 2) (L 0)] at h
    exact h
  have hD2 : 0 < dotP (ptA (L 1) (L 2) - ptA (L 0) (L 2)) (ptA (L 0) (L 1) - ptA (L 0) (L 2)) := by
    have h := hacute 1
    rw [e11, e12] at h
    simp only [vtx, e11, e12, e01, e02, e21, e22] at h
    rw [ptA_comm (L 2) (L 0)] at h
    rw [dotP_comm (ptA (L 0) (L 1) - ptA (L 0) (L 2)) (ptA (L 1) (L 2) - ptA (L 0) (L 2))] at h
    exact h
  have hD3 : 0 < dotP (ptA (L 1) (L 2) - ptA (L 0) (L 1)) (ptA (L 0) (L 2) - ptA (L 0) (L 1)) := by
    have h := hacute 2
    rw [e21, e22] at h
    simp only [vtx, e11, e12, e01, e02, e21, e22] at h
    rw [ptA_comm (L 2) (L 0)] at h
    exact h
  obtain ⟨M1, M2, M3, hM1, hM2, hM3, hdM12, hdM23, hdM13, heq23, heq13, heq12⟩ :=
    main_aux h1 h2 h3
      (hdist 0 1 (by decide)) (hdist 1 2 (by decide)) (hdist 0 2 (by decide))
      (hanti 0 1 (by decide)) (hanti 1 2 (by decide)) (hanti 0 2 (by decide))
      hD1 hD2 hD3
  have hM0 : ![M1, M2, M3] (0 : Fin 3) = M1 := rfl
  have hM1' : ![M1, M2, M3] (1 : Fin 3) = M2 := rfl
  have hM2' : ![M1, M2, M3] (2 : Fin 3) = M3 := rfl
  refine ⟨![M1, M2, M3], ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · simpa using norm_eq_one_of_dotP _ hM1
    · simpa using norm_eq_one_of_dotP _ hM2
    · simpa using norm_eq_one_of_dotP _ hM3
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij
    · exact hdM12
    · exact hdM13
    · exact hdM12.symm
    · exact hdM23
    · exact hdM13.symm
    · exact hdM23.symm
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij
    · show chordRefl (L 0) (L 1) '' (affineSpan ℝ {foot L 0, foot L 1}) =
        affineSpan ℝ {![M1, M2, M3] 0, ![M1, M2, M3] 1}
      simp only [foot, vtx, e01, e02, e11, e12, e21, e22, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, hM0, hM1', hM2']
      rw [ptA_comm (L 2) (L 0)]
      exact heq12
    · show chordRefl (L 0) (L 2) '' (affineSpan ℝ {foot L 0, foot L 2}) =
        affineSpan ℝ {![M1, M2, M3] 0, ![M1, M2, M3] 2}
      simp only [foot, vtx, e01, e02, e11, e12, e21, e22, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, hM0, hM1', hM2']
      exact heq13
    · show chordRefl (L 1) (L 0) '' (affineSpan ℝ {foot L 1, foot L 0}) =
        affineSpan ℝ {![M1, M2, M3] 1, ![M1, M2, M3] 0}
      rw [chordRefl_fun_comm h2 h1, Set.pair_comm (foot L 1) (foot L 0)]
      simp only [foot, vtx, e01, e02, e11, e12, e21, e22, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, hM0, hM1', hM2']
      rw [ptA_comm (L 2) (L 0), Set.pair_comm M2 M1]
      exact heq12
    · show chordRefl (L 1) (L 2) '' (affineSpan ℝ {foot L 1, foot L 2}) =
        affineSpan ℝ {![M1, M2, M3] 1, ![M1, M2, M3] 2}
      simp only [foot, vtx, e01, e02, e11, e12, e21, e22, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, hM0, hM1', hM2']
      rw [ptA_comm (L 2) (L 0)]
      exact heq23
    · show chordRefl (L 2) (L 0) '' (affineSpan ℝ {foot L 2, foot L 0}) =
        affineSpan ℝ {![M1, M2, M3] 2, ![M1, M2, M3] 0}
      rw [chordRefl_fun_comm h3 h1, Set.pair_comm (foot L 2) (foot L 0)]
      simp only [foot, vtx, e01, e02, e11, e12, e21, e22, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, hM0, hM1', hM2']
      rw [Set.pair_comm M3 M1]
      exact heq13
    · show chordRefl (L 2) (L 1) '' (affineSpan ℝ {foot L 2, foot L 1}) =
        affineSpan ℝ {![M1, M2, M3] 2, ![M1, M2, M3] 1}
      rw [chordRefl_fun_comm h3 h2, Set.pair_comm (foot L 2) (foot L 1)]
      simp only [foot, vtx, e01, e02, e11, e12, e21, e22, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, hM0, hM1', hM2']
      rw [ptA_comm (L 2) (L 0), Set.pair_comm M3 M2]
      exact heq23

end Imo2000P6
