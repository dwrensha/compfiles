/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Geometry.Euclidean.Incenter
public import ProblemExtraction

@[expose] public section

problem_file {
  tags := [.Geometry]
}

/-!
# International Mathematical Olympiad 2012, Problem 1

Let `ABC` be a triangle and `J` the centre of the excircle opposite the vertex `A`.
This excircle is tangent to the side `BC` at `M`, and to the lines `AB` and `AC` at `K`
and `L`, respectively. The lines `LM` and `BJ` meet at `F`, and the lines `KM` and `CJ`
meet at `G`. Let `S` be the point of intersection of the lines `AF` and `BC`, and let
`T` be the point of intersection of the lines `AG` and `BC`.
Prove that `M` is the midpoint of the segment `ST`.
-/

open Affine EuclideanGeometry

open scoped Affine RealInnerProductSpace

namespace Imo2012P1

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MetricSpace P] [NormedAddTorsor V P]

/-- The triangle of the problem, as a `Simplex ℝ P 2`. -/
noncomputable abbrev tri (A B C : P) (hABC : AffineIndependent ℝ ![A, B, C]) :
    Triangle ℝ P :=
  ⟨![A, B, C], hABC⟩

/-- The centre `J` of the `A`-excircle. -/
noncomputable abbrev J (A B C : P) (hABC : AffineIndependent ℝ ![A, B, C]) : P :=
  (tri A B C hABC).excenter {0}

/-- The tangency point `M` of the `A`-excircle with the side `BC`. -/
noncomputable abbrev M (A B C : P) (hABC : AffineIndependent ℝ ![A, B, C]) : P :=
  (tri A B C hABC).touchpoint {0} 0

/-- The tangency point `L` of the `A`-excircle with the line `AC`. -/
noncomputable abbrev L (A B C : P) (hABC : AffineIndependent ℝ ![A, B, C]) : P :=
  (tri A B C hABC).touchpoint {0} 1

/-- The tangency point `K` of the `A`-excircle with the line `AB`. -/
noncomputable abbrev K (A B C : P) (hABC : AffineIndependent ℝ ![A, B, C]) : P :=
  (tri A B C hABC).touchpoint {0} 2

snip begin

section

variable (A B C : P) (hABC : AffineIndependent ℝ ![A, B, C])

/-- `a = dist B C`. -/
noncomputable abbrev a (A B C : P) : ℝ := dist B C
/-- `b = dist A C`. -/
noncomputable abbrev b (A B C : P) : ℝ := dist A C
/-- `c = dist A B`. -/
noncomputable abbrev c (A B C : P) : ℝ := dist A B
/-- The semiperimeter `s = (a + b + c) / 2`. -/
noncomputable abbrev sp (A B C : P) : ℝ := (a A B C + b A B C + c A B C) / 2

/-- The strict triangle inequality for non-collinear points. -/
lemma triangle_lt (P₁ P₂ P₃ : P) (h : ¬ Collinear ℝ ({P₁, P₂, P₃} : Set P)) :
    dist P₁ P₃ < dist P₁ P₂ + dist P₂ P₃ := by
  rw [dist_eq_norm_vsub, dist_eq_norm_vsub, dist_eq_norm_vsub,
    ← vsub_add_vsub_cancel P₁ P₂ P₃]
  refine lt_of_le_of_ne (norm_add_le _ _) (fun heq ↦ h ?_)
  rw [norm_add_eq_iff_real] at heq
  have hs : SameRay ℝ (P₁ -ᵥ P₂) (P₂ -ᵥ P₃) := sameRay_iff_norm_smul_eq.mpr heq.symm
  have hs' := hs.neg
  rw [neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev] at hs'
  exact (wbtw_iff_sameRay_vsub.mpr hs').collinear

include hABC

lemma A_ne_B : A ≠ B := (hABC.injective).ne (by decide : (0 : Fin 3) ≠ 1)
lemma B_ne_C : B ≠ C := (hABC.injective).ne (by decide : (1 : Fin 3) ≠ 2)
lemma A_ne_C : A ≠ C := (hABC.injective).ne (by decide : (0 : Fin 3) ≠ 2)

lemma ha : 0 < a A B C := dist_pos.mpr (B_ne_C A B C hABC)
lemma hb : 0 < b A B C := dist_pos.mpr (A_ne_C A B C hABC)
lemma hc : 0 < c A B C := dist_pos.mpr (A_ne_B A B C hABC)

lemma not_collinear : ¬ Collinear ℝ ({A, B, C} : Set P) :=
  affineIndependent_iff_not_collinear_set.mp hABC

/-- `a < b + c`. -/
lemma hab : a A B C < b A B C + c A B C := by
  have hnc := not_collinear A B C hABC
  rw [Set.insert_comm A B] at hnc
  have h := triangle_lt B A C hnc
  rw [dist_comm B A] at h
  linarith

/-- `b < a + c`. -/
lemma hbc : b A B C < a A B C + c A B C := by
  have hnc := not_collinear A B C hABC
  rw [Set.pair_comm B C, Set.insert_comm A C, Set.pair_comm A B] at hnc
  have h := triangle_lt C B A hnc
  rw [dist_comm C A, dist_comm C B, dist_comm B A] at h
  linarith

/-- `c < a + b`. -/
lemma hca : c A B C < a A B C + b A B C := by
  have hnc := not_collinear A B C hABC
  rw [Set.pair_comm B C] at hnc
  have h := triangle_lt A C B hnc
  rw [dist_comm C B] at h
  linarith

lemma hsa : 0 < sp A B C - a A B C := by
  have h := hab A B C hABC
  simp only [sp]
  linarith

lemma hsb : 0 < sp A B C - b A B C := by
  have h := hbc A B C hABC
  simp only [sp]
  linarith

lemma hsc : 0 < sp A B C - c A B C := by
  have h := hca A B C hABC
  simp only [sp]
  linarith

/-! ### The three faces of the triangle, as affine subspaces -/

lemma faceBC : affineSpan ℝ (Set.range ((tri A B C hABC).faceOpposite 0).points) =
    line[ℝ, B, C] := by
  rw [Simplex.range_faceOpposite_points]
  have h1 : ({0}ᶜ : Set (Fin 3)) = {1, 2} := by
    ext i
    fin_cases i <;> simp
  rw [h1, Set.image_insert_eq, Set.image_singleton]
  simp [tri]

lemma faceAC : affineSpan ℝ (Set.range ((tri A B C hABC).faceOpposite 1).points) =
    line[ℝ, A, C] := by
  rw [Simplex.range_faceOpposite_points]
  have h1 : ({1}ᶜ : Set (Fin 3)) = {0, 2} := by
    ext i
    fin_cases i <;> simp
  rw [h1, Set.image_insert_eq, Set.image_singleton]
  simp [tri]

lemma faceAB : affineSpan ℝ (Set.range ((tri A B C hABC).faceOpposite 2).points) =
    line[ℝ, A, B] := by
  rw [Simplex.range_faceOpposite_points]
  have h1 : ({2}ᶜ : Set (Fin 3)) = {0, 1} := by
    ext i
    fin_cases i <;> simp
  rw [h1, Set.image_insert_eq, Set.image_singleton]
  simp [tri]

/-- The `A`-excenter exists. -/
lemma hex : (tri A B C hABC).ExcenterExists {0} :=
  (tri A B C hABC).excenterExists_singleton 0

/-! ### Tangency of the excircle, and equal tangent lengths -/

lemma tangM : ((tri A B C hABC).exsphere {0}).IsTangentAt (M A B C hABC) line[ℝ, B, C] := by
  rw [← faceBC]
  exact (hex A B C hABC).isTangentAt_touchpoint 0

lemma tangL : ((tri A B C hABC).exsphere {0}).IsTangentAt (L A B C hABC) line[ℝ, A, C] := by
  rw [← faceAC]
  exact (hex A B C hABC).isTangentAt_touchpoint 1

lemma tangK : ((tri A B C hABC).exsphere {0}).IsTangentAt (K A B C hABC) line[ℝ, A, B] := by
  rw [← faceAB]
  exact (hex A B C hABC).isTangentAt_touchpoint 2

/-- Tangent segments from `B` to the excircle have equal length. -/
lemma dist_BK_BM : dist B (K A B C hABC) = dist B (M A B C hABC) :=
  (tangK A B C hABC).dist_eq_of_mem_of_mem (tangM A B C hABC)
    (right_mem_affineSpan_pair ℝ A B) (left_mem_affineSpan_pair ℝ B C)

/-- Tangent segments from `C` to the excircle have equal length. -/
lemma dist_CM_CL : dist C (M A B C hABC) = dist C (L A B C hABC) :=
  (tangM A B C hABC).dist_eq_of_mem_of_mem (tangL A B C hABC)
    (right_mem_affineSpan_pair ℝ B C) (right_mem_affineSpan_pair ℝ A C)

/-- Tangent segments from `A` to the excircle have equal length. -/
lemma dist_AK_AL : dist A (K A B C hABC) = dist A (L A B C hABC) :=
  (tangK A B C hABC).dist_eq_of_mem_of_mem (tangL A B C hABC)
    (left_mem_affineSpan_pair ℝ A B) (left_mem_affineSpan_pair ℝ A C)

/-! ### Signs of the touchpoint weights -/

lemma wM_zero : (tri A B C hABC).touchpointWeights {0} 0 0 = 0 :=
  (tri A B C hABC).touchpointWeights_eq_zero 0

lemma wM_one_pos : 0 < (tri A B C hABC).touchpointWeights {0} 0 1 :=
  (tri A B C hABC).touchpointWeights_singleton_pos (by decide : (0 : Fin 3) ≠ 1)

lemma wM_two_pos : 0 < (tri A B C hABC).touchpointWeights {0} 0 2 :=
  (tri A B C hABC).touchpointWeights_singleton_pos (by decide : (0 : Fin 3) ≠ 2)

lemma wK_two : (tri A B C hABC).touchpointWeights {0} 2 2 = 0 :=
  (tri A B C hABC).touchpointWeights_eq_zero 2

lemma wK_zero_neg : (tri A B C hABC).touchpointWeights {0} 2 0 < 0 := by
  have h1 := (hex A B C hABC).sign_touchpointWeights (by decide : (2 : Fin 3) ≠ 0)
  rw [(tri A B C hABC).sign_excenterWeights_singleton_neg 0] at h1
  exact sign_eq_neg_one_iff.mp h1

lemma wK_one_pos : 0 < (tri A B C hABC).touchpointWeights {0} 2 1 := by
  have h1 := (hex A B C hABC).sign_touchpointWeights (by decide : (2 : Fin 3) ≠ 1)
  rw [(tri A B C hABC).sign_excenterWeights_singleton_pos
    (by decide : (0 : Fin 3) ≠ 1)] at h1
  exact sign_eq_one_iff.mp h1

lemma wL_one : (tri A B C hABC).touchpointWeights {0} 1 1 = 0 :=
  (tri A B C hABC).touchpointWeights_eq_zero 1

lemma wL_zero_neg : (tri A B C hABC).touchpointWeights {0} 1 0 < 0 := by
  have h1 := (hex A B C hABC).sign_touchpointWeights (by decide : (1 : Fin 3) ≠ 0)
  rw [(tri A B C hABC).sign_excenterWeights_singleton_neg 0] at h1
  exact sign_eq_neg_one_iff.mp h1

lemma wL_two_pos : 0 < (tri A B C hABC).touchpointWeights {0} 1 2 := by
  have h1 := (hex A B C hABC).sign_touchpointWeights (by decide : (1 : Fin 3) ≠ 2)
  rw [(tri A B C hABC).sign_excenterWeights_singleton_pos
    (by decide : (0 : Fin 3) ≠ 2)] at h1
  exact sign_eq_one_iff.mp h1

lemma wM_sum : (tri A B C hABC).touchpointWeights {0} 0 1 +
    (tri A B C hABC).touchpointWeights {0} 0 2 = 1 := by
  have h := (tri A B C hABC).sum_touchpointWeights {0} 0
  rw [Fin.sum_univ_three, wM_zero] at h
  linarith

lemma wK_sum : (tri A B C hABC).touchpointWeights {0} 2 0 +
    (tri A B C hABC).touchpointWeights {0} 2 1 = 1 := by
  have h := (tri A B C hABC).sum_touchpointWeights {0} 2
  rw [Fin.sum_univ_three, wK_two] at h
  linarith

lemma wL_sum : (tri A B C hABC).touchpointWeights {0} 1 0 +
    (tri A B C hABC).touchpointWeights {0} 1 2 = 1 := by
  have h := (tri A B C hABC).sum_touchpointWeights {0} 1
  rw [Fin.sum_univ_three, wL_one] at h
  linarith

/-! ### The touchpoints as points on their respective lines -/

lemma M_eq_lineMap : M A B C hABC =
    AffineMap.lineMap B C ((tri A B C hABC).touchpointWeights {0} 0 2) := by
  have h1 := (tri A B C hABC).affineCombination_touchpointWeights {0} 0
  rw [Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one _ _ _
    ((tri A B C hABC).sum_touchpointWeights {0} 0) B] at h1
  show (tri A B C hABC).touchpoint {0} 0 = _
  rw [← h1, Finset.weightedVSubOfPoint_apply, Fin.sum_univ_three]
  simp only [tri, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, wM_zero, zero_smul, vsub_self, smul_zero,
    add_zero, zero_add, AffineMap.lineMap_apply]

lemma K_eq_lineMap : K A B C hABC =
    AffineMap.lineMap A B ((tri A B C hABC).touchpointWeights {0} 2 1) := by
  have h1 := (tri A B C hABC).affineCombination_touchpointWeights {0} 2
  rw [Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one _ _ _
    ((tri A B C hABC).sum_touchpointWeights {0} 2) A] at h1
  show (tri A B C hABC).touchpoint {0} 2 = _
  rw [← h1, Finset.weightedVSubOfPoint_apply, Fin.sum_univ_three]
  simp only [tri, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, wK_two, zero_smul, vsub_self, smul_zero,
    add_zero, zero_add, AffineMap.lineMap_apply]

lemma L_eq_lineMap : L A B C hABC =
    AffineMap.lineMap A C ((tri A B C hABC).touchpointWeights {0} 1 2) := by
  have h1 := (tri A B C hABC).affineCombination_touchpointWeights {0} 1
  rw [Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one _ _ _
    ((tri A B C hABC).sum_touchpointWeights {0} 1) A] at h1
  show (tri A B C hABC).touchpoint {0} 1 = _
  rw [← h1, Finset.weightedVSubOfPoint_apply, Fin.sum_univ_three]
  simp only [tri, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, wL_one, zero_smul, vsub_self, smul_zero,
    add_zero, zero_add, AffineMap.lineMap_apply]

lemma dist_BM : dist B (M A B C hABC) =
    (tri A B C hABC).touchpointWeights {0} 0 2 * a A B C := by
  rw [M_eq_lineMap, dist_comm, dist_lineMap_left, Real.norm_eq_abs,
    abs_of_pos (wM_two_pos A B C hABC)]

lemma dist_MC : dist (M A B C hABC) C =
    (tri A B C hABC).touchpointWeights {0} 0 1 * a A B C := by
  rw [M_eq_lineMap, dist_lineMap_right, Real.norm_eq_abs]
  have h : 1 - (tri A B C hABC).touchpointWeights {0} 0 2 =
      (tri A B C hABC).touchpointWeights {0} 0 1 := by
    have := wM_sum A B C hABC
    linarith
  rw [h, abs_of_pos (wM_one_pos A B C hABC)]

lemma dist_AK : dist A (K A B C hABC) =
    (tri A B C hABC).touchpointWeights {0} 2 1 * c A B C := by
  rw [K_eq_lineMap, dist_comm, dist_lineMap_left, Real.norm_eq_abs,
    abs_of_pos (wK_one_pos A B C hABC)]

lemma dist_BK : dist B (K A B C hABC) =
    ((tri A B C hABC).touchpointWeights {0} 2 1 - 1) * c A B C := by
  rw [K_eq_lineMap, dist_comm, dist_lineMap_right, Real.norm_eq_abs]
  have h2 := wK_zero_neg A B C hABC
  have h3 := wK_sum A B C hABC
  rw [abs_of_neg (by linarith : 1 - (tri A B C hABC).touchpointWeights {0} 2 1 < 0)]
  show -(1 - (tri A B C hABC).touchpointWeights {0} 2 1) * dist A B =
    ((tri A B C hABC).touchpointWeights {0} 2 1 - 1) * dist A B
  ring

lemma dist_AL : dist A (L A B C hABC) =
    (tri A B C hABC).touchpointWeights {0} 1 2 * b A B C := by
  rw [L_eq_lineMap, dist_comm, dist_lineMap_left, Real.norm_eq_abs,
    abs_of_pos (wL_two_pos A B C hABC)]

lemma dist_CL : dist C (L A B C hABC) =
    ((tri A B C hABC).touchpointWeights {0} 1 2 - 1) * b A B C := by
  rw [L_eq_lineMap, dist_comm, dist_lineMap_right, Real.norm_eq_abs]
  have h2 := wL_zero_neg A B C hABC
  have h3 := wL_sum A B C hABC
  rw [abs_of_neg (by linarith : 1 - (tri A B C hABC).touchpointWeights {0} 1 2 < 0)]
  show -(1 - (tri A B C hABC).touchpointWeights {0} 1 2) * dist A C =
    ((tri A B C hABC).touchpointWeights {0} 1 2 - 1) * dist A C
  ring

/-! ### Solving for the touchpoint weights -/

lemma wM_two : (tri A B C hABC).touchpointWeights {0} 0 2 =
    (sp A B C - c A B C) / a A B C := by
  have h1 := dist_BK_BM A B C hABC
  rw [dist_BK, dist_BM] at h1
  have h2 := dist_AK_AL A B C hABC
  rw [dist_AK, dist_AL] at h2
  have h3 := dist_CM_CL A B C hABC
  rw [dist_comm C (M A B C hABC), dist_MC, dist_CL] at h3
  have h4 : (tri A B C hABC).touchpointWeights {0} 0 2 * a A B C +
      (tri A B C hABC).touchpointWeights {0} 0 1 * a A B C = a A B C := by
    rw [← add_mul, add_comm ((tri A B C hABC).touchpointWeights {0} 0 2), wM_sum, one_mul]
  have ha' := (ha A B C hABC).ne'
  field_simp [ha']
  ring_nf at h1 h2 h3 h4 ⊢
  linarith

lemma wK_one : (tri A B C hABC).touchpointWeights {0} 2 1 =
    sp A B C / c A B C := by
  have h1 := dist_BK_BM A B C hABC
  rw [dist_BK, dist_BM, wM_two, div_mul_cancel₀ _ (ha A B C hABC).ne'] at h1
  have hc' := (hc A B C hABC).ne'
  field_simp [hc']
  ring_nf at h1 ⊢
  linarith

lemma wL_two : (tri A B C hABC).touchpointWeights {0} 1 2 =
    sp A B C / b A B C := by
  have h2 := dist_AK_AL A B C hABC
  rw [dist_AK, dist_AL, wK_one, div_mul_cancel₀ _ (hc A B C hABC).ne'] at h2
  have hb' := (hb A B C hABC).ne'
  field_simp [hb']
  ring_nf at h2 ⊢
  linarith

lemma wM_one : (tri A B C hABC).touchpointWeights {0} 0 1 =
    (sp A B C - b A B C) / a A B C := by
  have h := wM_sum A B C hABC
  rw [wM_two] at h
  have ha' := (ha A B C hABC).ne'
  field_simp [ha'] at h ⊢
  ring_nf at h ⊢
  linarith

lemma wK_zero : (tri A B C hABC).touchpointWeights {0} 2 0 =
    -(sp A B C - c A B C) / c A B C := by
  have h := wK_sum A B C hABC
  rw [wK_one] at h
  have hc' := (hc A B C hABC).ne'
  field_simp [hc'] at h ⊢
  ring_nf at h ⊢
  linarith

lemma wL_zero : (tri A B C hABC).touchpointWeights {0} 1 0 =
    -(sp A B C - b A B C) / b A B C := by
  have h := wL_sum A B C hABC
  rw [wL_two] at h
  have hb' := (hb A B C hABC).ne'
  field_simp [hb'] at h ⊢
  ring_nf at h ⊢
  linarith

/-! ### The touchpoints as affine combinations of the vertices -/

lemma M_eq_comb : M A B C hABC = Finset.univ.affineCombination ℝ ![A, B, C]
    ![0, (sp A B C - b A B C) / a A B C, (sp A B C - c A B C) / a A B C] := by
  show (tri A B C hABC).touchpoint {0} 0 = _
  rw [← (tri A B C hABC).affineCombination_touchpointWeights {0} 0]
  congr 1
  funext i
  fin_cases i
  · exact wM_zero A B C hABC
  · exact wM_one A B C hABC
  · exact wM_two A B C hABC

lemma K_eq_comb : K A B C hABC = Finset.univ.affineCombination ℝ ![A, B, C]
    ![-(sp A B C - c A B C) / c A B C, sp A B C / c A B C, 0] := by
  show (tri A B C hABC).touchpoint {0} 2 = _
  rw [← (tri A B C hABC).affineCombination_touchpointWeights {0} 2]
  congr 1
  funext i
  fin_cases i
  · exact wK_zero A B C hABC
  · exact wK_one A B C hABC
  · exact wK_two A B C hABC

lemma L_eq_comb : L A B C hABC = Finset.univ.affineCombination ℝ ![A, B, C]
    ![-(sp A B C - b A B C) / b A B C, 0, sp A B C / b A B C] := by
  show (tri A B C hABC).touchpoint {0} 1 = _
  rw [← (tri A B C hABC).affineCombination_touchpointWeights {0} 1]
  congr 1
  funext i
  fin_cases i
  · exact wL_zero A B C hABC
  · exact wL_one A B C hABC
  · exact wL_two A B C hABC

/-! ### The excenter as an affine combination of the vertices -/

/-- `ds = b + c - a = 2 (s - a)`. -/
noncomputable abbrev ds (A B C : P) : ℝ := b A B C + c A B C - a A B C

/-- The weights of the `A`-excenter. -/
noncomputable abbrev wJ (A B C : P) : Fin 3 → ℝ :=
  ![-(a A B C) / ds A B C, b A B C / ds A B C, c A B C / ds A B C]

lemma hds : 0 < ds A B C := by
  have h := hab A B C hABC
  simp only [ds]
  linarith

lemma wJ_sum : ∑ i, wJ A B C i = 1 := by
  have h := (hds A B C hABC).ne'
  simp only [wJ, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  field_simp [h]
  ring

lemma inner_CB_self : ⟪C -ᵥ B, C -ᵥ B⟫ = a A B C ^ 2 := by
  rw [real_inner_self_eq_norm_sq, ← dist_eq_norm_vsub' V B C]

lemma inner_AB_self : ⟪A -ᵥ B, A -ᵥ B⟫ = c A B C ^ 2 := by
  rw [real_inner_self_eq_norm_sq, ← dist_eq_norm_vsub V A B]

lemma inner_BA_self : ⟪B -ᵥ A, B -ᵥ A⟫ = c A B C ^ 2 := by
  rw [real_inner_self_eq_norm_sq, ← dist_eq_norm_vsub' V A B]

lemma inner_AB_CB : ⟪A -ᵥ B, C -ᵥ B⟫ = (c A B C ^ 2 + a A B C ^ 2 - b A B C ^ 2) / 2 := by
  have h1 : b A B C ^ 2 = ‖(A -ᵥ B) - (C -ᵥ B)‖ ^ 2 := by
    rw [vsub_sub_vsub_cancel_right, ← dist_eq_norm_vsub V A C]
  rw [norm_sub_sq_real, ← dist_eq_norm_vsub V A B, ← dist_eq_norm_vsub' V B C] at h1
  linarith

lemma inner_BA_CA : ⟪B -ᵥ A, C -ᵥ A⟫ = (c A B C ^ 2 + b A B C ^ 2 - a A B C ^ 2) / 2 := by
  have h1 : a A B C ^ 2 = ‖(B -ᵥ A) - (C -ᵥ A)‖ ^ 2 := by
    rw [vsub_sub_vsub_cancel_right, ← dist_eq_norm_vsub V B C]
  rw [norm_sub_sq_real, ← dist_eq_norm_vsub' V A B, ← dist_eq_norm_vsub' V A C] at h1
  linarith

/-- A point on `BC` given by barycentric weights is a `lineMap`. -/
lemma affineComb_eq_lineMap_BC (x y : ℝ) (h : x + y = 1) :
    (Finset.univ.affineCombination ℝ ![A, B, C] ![0, x, y]) = AffineMap.lineMap B C y := by
  have hsum : ∑ i, ![0, x, y] i = 1 := by
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    linarith [h]
  rw [Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one _ _ _ hsum B,
    Finset.weightedVSubOfPoint_apply, Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, zero_smul, vsub_self, smul_zero, add_zero, zero_add,
    AffineMap.lineMap_apply]

/-- A point on `AB` given by barycentric weights is a `lineMap`. -/
lemma affineComb_eq_lineMap_AB (x y : ℝ) (h : x + y = 1) :
    (Finset.univ.affineCombination ℝ ![A, B, C] ![x, y, 0]) = AffineMap.lineMap A B y := by
  have hsum : ∑ i, ![x, y, 0] i = 1 := by
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    linarith [h]
  rw [Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one _ _ _ hsum A,
    Finset.weightedVSubOfPoint_apply, Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, zero_smul, vsub_self, smul_zero, add_zero, zero_add,
    AffineMap.lineMap_apply]

/-- A point on `AC` given by barycentric weights is a `lineMap`. -/
lemma affineComb_eq_lineMap_AC (x y : ℝ) (h : x + y = 1) :
    (Finset.univ.affineCombination ℝ ![A, B, C] ![x, 0, y]) = AffineMap.lineMap A C y := by
  have hsum : ∑ i, ![x, 0, y] i = 1 := by
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    linarith [h]
  rw [Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one _ _ _ hsum A,
    Finset.weightedVSubOfPoint_apply, Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, zero_smul, vsub_self, smul_zero, add_zero, zero_add,
    AffineMap.lineMap_apply]

lemma wJ_vsub_B : (Finset.univ.affineCombination ℝ ![A, B, C] (wJ A B C)) -ᵥ B =
    (-(a A B C) / ds A B C) • (A -ᵥ B) + (c A B C / ds A B C) • (C -ᵥ B) := by
  have h := Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one
    Finset.univ (wJ A B C) ![A, B, C] (wJ_sum A B C hABC) B
  rw [h, vadd_vsub, Finset.weightedVSubOfPoint_apply, Fin.sum_univ_three]
  simp only [wJ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, vsub_self, smul_zero, add_zero, zero_add]

lemma wJ_vsub_A : (Finset.univ.affineCombination ℝ ![A, B, C] (wJ A B C)) -ᵥ A =
    (b A B C / ds A B C) • (B -ᵥ A) + (c A B C / ds A B C) • (C -ᵥ A) := by
  have h := Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one
    Finset.univ (wJ A B C) ![A, B, C] (wJ_sum A B C hABC) A
  rw [h, vadd_vsub, Finset.weightedVSubOfPoint_apply, Fin.sum_univ_three]
  simp only [wJ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, vsub_self, smul_zero, add_zero, zero_add]

/-- The vector from the candidate touchpoint `M` to the candidate excenter is
orthogonal to `BC`. -/
lemma orth_JM : ⟪(Finset.univ.affineCombination ℝ ![A, B, C] (wJ A B C)) -ᵥ
    (Finset.univ.affineCombination ℝ ![A, B, C]
      ![0, (sp A B C - b A B C) / a A B C, (sp A B C - c A B C) / a A B C]), C -ᵥ B⟫ = 0 := by
  have hM : (Finset.univ.affineCombination ℝ ![A, B, C]
      ![0, (sp A B C - b A B C) / a A B C, (sp A B C - c A B C) / a A B C]) -ᵥ B =
      ((sp A B C - c A B C) / a A B C) • (C -ᵥ B) := by
    have hsum : ∑ i, ![0, (sp A B C - b A B C) / a A B C,
        (sp A B C - c A B C) / a A B C] i = 1 := by
      have ha' := (ha A B C hABC).ne'
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp [ha']
      ring
    have h := Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one
      Finset.univ _ ![A, B, C] hsum B
    rw [h, vadd_vsub, Finset.weightedVSubOfPoint_apply, Fin.sum_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, zero_smul, vsub_self, smul_zero, add_zero, zero_add]
  rw [← vsub_sub_vsub_cancel_right _ _ B, wJ_vsub_B A B C hABC, hM]
  rw [inner_sub_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
    real_inner_smul_left, inner_AB_CB A B C hABC, inner_CB_self A B C hABC]
  have ha' := (ha A B C hABC).ne'
  have hds' := (hds A B C hABC).ne'
  field_simp [ha', hds']
  ring

/-- The vector from the candidate touchpoint `K` to the candidate excenter is
orthogonal to `AB`. -/
lemma orth_JK : ⟪(Finset.univ.affineCombination ℝ ![A, B, C] (wJ A B C)) -ᵥ
    (Finset.univ.affineCombination ℝ ![A, B, C]
      ![-(sp A B C - c A B C) / c A B C, sp A B C / c A B C, 0]), B -ᵥ A⟫ = 0 := by
  have hK : (Finset.univ.affineCombination ℝ ![A, B, C]
      ![-(sp A B C - c A B C) / c A B C, sp A B C / c A B C, 0]) -ᵥ A =
      (sp A B C / c A B C) • (B -ᵥ A) := by
    have hsum : ∑ i, ![-(sp A B C - c A B C) / c A B C, sp A B C / c A B C, 0] i = 1 := by
      have hc' := (hc A B C hABC).ne'
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp [hc']
      ring
    have h := Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one
      Finset.univ _ ![A, B, C] hsum A
    rw [h, vadd_vsub, Finset.weightedVSubOfPoint_apply, Fin.sum_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, zero_smul, vsub_self, smul_zero, add_zero, zero_add]
  rw [← vsub_sub_vsub_cancel_right _ _ A, wJ_vsub_A A B C hABC, hK]
  rw [inner_sub_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
    real_inner_smul_left, inner_BA_self A B C hABC, ← real_inner_comm (C -ᵥ A) (B -ᵥ A),
    inner_BA_CA A B C hABC]
  have hc' := (hc A B C hABC).ne'
  have hds' := (hds A B C hABC).ne'
  field_simp [hc', hds']
  ring

/-- The candidate excenter is orthogonal to `BC` at the candidate touchpoint. -/
lemma dir_J'M : (Finset.univ.affineCombination ℝ ![A, B, C] (wJ A B C)) -ᵥ
    (Finset.univ.affineCombination ℝ ![A, B, C]
      ![0, (sp A B C - b A B C) / a A B C, (sp A B C - c A B C) / a A B C]) ∈
    (line[ℝ, B, C] : AffineSubspace ℝ P).directionᗮ := by
  rw [direction_affineSpan, vectorSpan_pair_rev,
    Submodule.mem_orthogonal_singleton_iff_inner_right, inner_eq_zero_symm]
  exact orth_JM A B C hABC

/-- The candidate excenter is orthogonal to `AB` at the candidate touchpoint. -/
lemma dir_J'K : (Finset.univ.affineCombination ℝ ![A, B, C] (wJ A B C)) -ᵥ
    (Finset.univ.affineCombination ℝ ![A, B, C]
      ![-(sp A B C - c A B C) / c A B C, sp A B C / c A B C, 0]) ∈
    (line[ℝ, A, B] : AffineSubspace ℝ P).directionᗮ := by
  rw [direction_affineSpan, vectorSpan_pair_rev,
    Submodule.mem_orthogonal_singleton_iff_inner_right, inner_eq_zero_symm]
  exact orth_JK A B C hABC

/-- The excenter is orthogonal to `BC` at `M`. -/
lemma dir_JM : J A B C hABC -ᵥ M A B C hABC ∈
    (line[ℝ, B, C] : AffineSubspace ℝ P).directionᗮ := by
  rw [← faceBC A B C hABC]
  exact vsub_orthogonalProjection_mem_direction_orthogonal _ _

/-- The excenter is orthogonal to `AB` at `K`. -/
lemma dir_JK : J A B C hABC -ᵥ K A B C hABC ∈
    (line[ℝ, A, B] : AffineSubspace ℝ P).directionᗮ := by
  rw [← faceAB A B C hABC]
  exact vsub_orthogonalProjection_mem_direction_orthogonal _ _

/-- The excenter is the affine combination with weights `(-a : b : c)`. -/
lemma J_eq : J A B C hABC = Finset.univ.affineCombination ℝ ![A, B, C] (wJ A B C) := by
  set J' := Finset.univ.affineCombination ℝ ![A, B, C] (wJ A B C) with hJ'def
  have hJM' := dir_JM A B C hABC
  rw [M_eq_comb A B C hABC] at hJM'
  have hJK' := dir_JK A B C hABC
  rw [K_eq_comb A B C hABC] at hJK'
  have h1 : J' -ᵥ J A B C hABC ∈ (line[ℝ, B, C] : AffineSubspace ℝ P).directionᗮ := by
    have hsub := Submodule.sub_mem _ (dir_J'M A B C hABC) hJM'
    rwa [vsub_sub_vsub_cancel_right] at hsub
  have h2 : J' -ᵥ J A B C hABC ∈ (line[ℝ, A, B] : AffineSubspace ℝ P).directionᗮ := by
    have hsub := Submodule.sub_mem _ (dir_J'K A B C hABC) hJK'
    rwa [vsub_sub_vsub_cancel_right] at hsub
  rw [direction_affineSpan, vectorSpan_pair_rev,
    Submodule.mem_orthogonal_singleton_iff_inner_right] at h1 h2
  have h3 : J' -ᵥ J A B C hABC ∈ vectorSpan ℝ (Set.range ![A, B, C]) := by
    rw [← direction_affineSpan]
    refine (AffineSubspace.vsub_left_mem_direction_iff_mem ?_ _).mpr ?_
    · exact affineCombination_mem_affineSpan (wJ_sum A B C hABC) _
    · show J A B C hABC ∈ affineSpan ℝ (Set.range ![A, B, C])
      exact (hex A B C hABC).excenter_mem_affineSpan_range
  have h4 : J' -ᵥ J A B C hABC ∈ (vectorSpan ℝ (Set.range ![A, B, C]))ᗮ := by
    rw [vectorSpan_eq_span_vsub_set_left ℝ
      (show A ∈ Set.range ![A, B, C] from Set.mem_range_self 0)]
    rw [Submodule.mem_orthogonal']
    intro u hu
    have hgen : ∀ v ∈ (fun x ↦ A -ᵥ x) '' (Set.range ![A, B, C]),
        v ∈ (ℝ ∙ (J' -ᵥ J A B C hABC))ᗮ := by
      rintro v ⟨w, ⟨i, rfl⟩, rfl⟩
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
      fin_cases i
      · simp
      · show ⟪J' -ᵥ J A B C hABC, A -ᵥ B⟫ = 0
        rw [← neg_vsub_eq_vsub_rev B A, inner_neg_right, inner_eq_zero_symm.mp h2, neg_zero]
      · show ⟪J' -ᵥ J A B C hABC, A -ᵥ C⟫ = 0
        rw [show A -ᵥ C = (A -ᵥ B) + (B -ᵥ C) from (vsub_add_vsub_cancel A B C).symm,
          inner_add_right, ← neg_vsub_eq_vsub_rev B A, ← neg_vsub_eq_vsub_rev C B,
          inner_neg_right, inner_neg_right, inner_eq_zero_symm.mp h1,
          inner_eq_zero_symm.mp h2, neg_zero, add_zero]
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp
      ((Submodule.span_le.mpr hgen) hu)
  have h5 : J' -ᵥ J A B C hABC = 0 := by
    have hmem : J' -ᵥ J A B C hABC ∈
        (vectorSpan ℝ (Set.range ![A, B, C])) ⊓ (vectorSpan ℝ (Set.range ![A, B, C]))ᗮ :=
      ⟨h3, h4⟩
    rw [Submodule.inf_orthogonal_eq_bot] at hmem
    exact (Submodule.mem_bot _).mp hmem
  exact (vsub_eq_zero_iff_eq.mp h5).symm

/-! ### Barycentric coordinates on the plane of the triangle -/

/-- An affine combination of two points is a line map. -/
lemma comb2_eq_lineMap (X Y : P) (w : Fin 2 → ℝ) (hw : ∑ i, w i = 1) :
    (Finset.univ.affineCombination ℝ ![X, Y] w) = AffineMap.lineMap X Y (w 1) := by
  rw [Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one _ _ _ hw X,
    Finset.weightedVSubOfPoint_apply, Fin.sum_univ_two]
  simp [AffineMap.lineMap_apply]

/-- The vector from `A` to an affine combination of the vertices. -/
lemma comb_vsub_A (w : Fin 3 → ℝ) (hw : ∑ i, w i = 1) :
    (Finset.univ.affineCombination ℝ ![A, B, C] w) -ᵥ A =
      w 1 • (B -ᵥ A) + w 2 • (C -ᵥ A) := by
  rw [Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one _ _ _ hw A,
    vadd_vsub, Finset.weightedVSubOfPoint_apply, Fin.sum_univ_three]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]

/-- Coordinates with respect to `(B -ᵥ A, C -ᵥ A)` are unique. -/
lemma coord_unique {x₁ x₂ y₁ y₂ : ℝ}
    (h : x₁ • (B -ᵥ A) + x₂ • (C -ᵥ A) = y₁ • (B -ᵥ A) + y₂ • (C -ᵥ A)) :
    x₁ = y₁ ∧ x₂ = y₂ := by
  have hw₁ : ∑ i, ![1 - x₁ - x₂, x₁, x₂] i = 1 := by
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    ring
  have hw₂ : ∑ i, ![1 - y₁ - y₂, y₁, y₂] i = 1 := by
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    ring
  have e1 := comb_vsub_A A B C hABC ![1 - x₁ - x₂, x₁, x₂] hw₁
  have e2 := comb_vsub_A A B C hABC ![1 - y₁ - y₂, y₁, y₂] hw₂
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons] at e1 e2
  rw [← e1, ← e2] at h
  have hX : (Finset.univ.affineCombination ℝ ![A, B, C] ![1 - x₁ - x₂, x₁, x₂]) =
      (Finset.univ.affineCombination ℝ ![A, B, C] ![1 - y₁ - y₂, y₁, y₂]) :=
    vsub_left_injective A h
  have hu := (affineIndependent_iff_eq_of_fintype_affineCombination_eq ℝ ![A, B, C]).mp hABC _ _ hw₁ hw₂ hX
  have h1 := congrFun hu 1
  have h2 := congrFun hu 2
  simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at h1 h2
  exact ⟨h1, h2⟩

/-- The range of a two-element family. -/
lemma range_pair (X Y : P) : Set.range ![X, Y] = {X, Y} := by
  rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
    Set.singleton_union]

/-! ### The intersection points -/

lemma wM_sum1 : ∑ i, ![0, (sp A B C - b A B C) / a A B C, (sp A B C - c A B C) / a A B C] i = 1 := by
  have ha' := (ha A B C hABC).ne'
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  field_simp [ha']
  ring

lemma wK_sum1 : ∑ i, ![-(sp A B C - c A B C) / c A B C, sp A B C / c A B C, 0] i = 1 := by
  have hc' := (hc A B C hABC).ne'
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  field_simp [hc']
  ring

/-- `M` relative to `A`. -/
lemma M_vsub_A : M A B C hABC -ᵥ A =
    ((sp A B C - b A B C) / a A B C) • (B -ᵥ A) + ((sp A B C - c A B C) / a A B C) • (C -ᵥ A) := by
  rw [M_eq_comb A B C hABC, comb_vsub_A A B C hABC _ (wM_sum1 A B C hABC)]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]

/-- `K` relative to `A`. -/
lemma K_vsub_A : K A B C hABC -ᵥ A = (sp A B C / c A B C) • (B -ᵥ A) := by
  rw [K_eq_comb A B C hABC, comb_vsub_A A B C hABC _ (wK_sum1 A B C hABC)]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]

/-- `J` relative to `A`. -/
lemma J_vsub_A : J A B C hABC -ᵥ A =
    (b A B C / ds A B C) • (B -ᵥ A) + (c A B C / ds A B C) • (C -ᵥ A) := by
  rw [J_eq A B C hABC, comb_vsub_A A B C hABC _ (wJ_sum A B C hABC)]
  simp [wJ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]

/-- The point `G = KM ∩ CJ`, as an affine combination of the vertices. -/
lemma G_eq_comb (G : P)
    (hG : G ∈ line[ℝ, K A B C hABC, M A B C hABC] ⊓ line[ℝ, C, J A B C hABC]) :
    G = Finset.univ.affineCombination ℝ ![A, B, C]
      ![1 / 2, -(b A B C) / (2 * a A B C), (a A B C + b A B C) / (2 * a A B C)] := by
  have ha' := (ha A B C hABC).ne'
  have hb' := (hb A B C hABC).ne'
  have hc' := (hc A B C hABC).ne'
  have hds' := (hds A B C hABC).ne'
  -- `G = lineMap C J ν` for some `ν`.
  obtain ⟨w, hw, hGw⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype
    (show G ∈ affineSpan ℝ (Set.range ![C, J A B C hABC]) by
      rw [range_pair A B C hABC]
      exact hG.2)
  rw [comb2_eq_lineMap A B C hABC _ _ _ hw] at hGw
  set ν := w 1 with hν
  -- `G -ᵥ K = μ • (M -ᵥ K)` for some `μ`.
  have hGK : G -ᵥ K A B C hABC ∈ (line[ℝ, K A B C hABC, M A B C hABC]).direction := by
    refine (AffineSubspace.vsub_right_mem_direction_iff_mem ?_ G).mpr hG.1
    exact left_mem_affineSpan_pair ℝ _ _
  rw [direction_affineSpan, vectorSpan_pair_rev] at hGK
  obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp hGK
  -- Two expressions for `G -ᵥ A`.
  have hGA₁ : G -ᵥ A = (ν * (b A B C / ds A B C)) • (B -ᵥ A) +
      (ν * (c A B C / ds A B C - 1) + 1) • (C -ᵥ A) := by
    have h1 : G -ᵥ A = (G -ᵥ C) + (C -ᵥ A) := (vsub_add_vsub_cancel G C A).symm
    have h2 : G -ᵥ C = ν • (J A B C hABC -ᵥ C) := by
      rw [hGw]
      exact AffineMap.lineMap_vsub_left _ _ _
    rw [h1, h2, show J A B C hABC -ᵥ C = (J A B C hABC -ᵥ A) - (C -ᵥ A) from
      (vsub_sub_vsub_cancel_right _ _ _).symm, J_vsub_A A B C hABC]
    module
  have hGA₂ : G -ᵥ A = (sp A B C / c A B C + μ * ((sp A B C - b A B C) / a A B C -
      sp A B C / c A B C)) • (B -ᵥ A) + (μ * ((sp A B C - c A B C) / a A B C)) • (C -ᵥ A) := by
    have h1 : G -ᵥ A = (G -ᵥ K A B C hABC) + (K A B C hABC -ᵥ A) :=
      (vsub_add_vsub_cancel G _ A).symm
    rw [h1, ← hμ, show M A B C hABC -ᵥ K A B C hABC =
      (M A B C hABC -ᵥ A) - (K A B C hABC -ᵥ A) from (vsub_sub_vsub_cancel_right _ _ _).symm,
      M_vsub_A A B C hABC, K_vsub_A A B C hABC]
    module
  obtain ⟨eq_u, eq_v⟩ := coord_unique A B C hABC (hGA₁.symm.trans hGA₂)
  -- Eliminate `ν`, solve for `μ`.
  have hM : μ * (a A B C + b A B C - c A B C) = a A B C + b A B C := by
    simp only [sp, ds] at eq_u eq_v
    field_simp [ha', hb', hc'] at eq_u eq_v
    have E3 : (b A B C + c A B C - a A B C) * μ * (a A B C + b A B C + c A B C - c A B C * 2) *
        b A B C * c A B C -
        (b A B C + c A B C - a A B C) * (a A B C * (a A B C + b A B C + c A B C) +
          μ * (c A B C * (a A B C + b A B C + c A B C - b A B C * 2) -
            a A B C * (a A B C + b A B C + c A B C))) *
          (c A B C - (b A B C + c A B C - a A B C)) =
        2 * a A B C * b A B C * c A B C * (b A B C + c A B C - a A B C) := by
      linear_combination (c A B C - (b A B C + c A B C - a A B C)) * eq_u -
        (b A B C * c A B C) * eq_v
    have E4 : μ * (b A B C * c A B C * (a A B C + b A B C + c A B C - c A B C * 2) -
        (c A B C * (a A B C + b A B C + c A B C - b A B C * 2) -
          a A B C * (a A B C + b A B C + c A B C)) *
          (c A B C - (b A B C + c A B C - a A B C))) =
        a A B C * (2 * b A B C * c A B C + (a A B C + b A B C + c A B C) *
          (c A B C - (b A B C + c A B C - a A B C))) := by
      have h4 : (b A B C + c A B C - a A B C) *
          (μ * (b A B C * c A B C * (a A B C + b A B C + c A B C - c A B C * 2) -
            (c A B C * (a A B C + b A B C + c A B C - b A B C * 2) -
              a A B C * (a A B C + b A B C + c A B C)) *
              (c A B C - (b A B C + c A B C - a A B C)))) =
          (b A B C + c A B C - a A B C) * (a A B C * (2 * b A B C * c A B C +
            (a A B C + b A B C + c A B C) * (c A B C - (b A B C + c A B C - a A B C)))) := by
        linear_combination E3
      exact mul_left_cancel₀ hds' h4
    have h5 : a A B C * (a A B C - b A B C + c A B C) *
        (μ * (a A B C + b A B C - c A B C) - (a A B C + b A B C)) = 0 := by
      linear_combination E4
    have hAB : (0 : ℝ) < a A B C - b A B C + c A B C := by
      have h := hsb A B C hABC
      simp only [sp] at h
      linarith
    have h6 : μ * (a A B C + b A B C - c A B C) - (a A B C + b A B C) = 0 := by
      rcases mul_eq_zero.mp h5 with h7 | h7
      · rcases mul_eq_zero.mp h7 with h8 | h8
        · exact absurd h8 ha'
        · exfalso; linarith
      · exact h7
    linarith
  have hμ : μ = (a A B C + b A B C) / (2 * (sp A B C - c A B C)) := by
    have h2sc : 2 * (sp A B C - c A B C) = a A B C + b A B C - c A B C := by
      simp only [sp]
      ring
    have h2 : a A B C + b A B C - c A B C ≠ 0 := by
      rw [← h2sc]
      exact mul_ne_zero two_ne_zero (hsc A B C hABC).ne'
    rw [h2sc, eq_div_iff h2]
    exact hM
  -- Coordinates of `G`.
  set yG := μ * ((sp A B C - c A B C) / a A B C) with hyG
  set xG := sp A B C / c A B C + μ * ((sp A B C - b A B C) / a A B C - sp A B C / c A B C)
    with hxG
  have hyG' : yG = (a A B C + b A B C) / (2 * a A B C) := by
    have h2sc : 2 * (sp A B C - c A B C) = a A B C + b A B C - c A B C := by
      simp only [sp]
      ring
    have hM2 : μ * (2 * (sp A B C - c A B C)) = a A B C + b A B C := by
      rw [h2sc]
      exact hM
    have hM3 : μ * (sp A B C - c A B C) = (a A B C + b A B C) / 2 := by linarith [hM2]
    rw [hyG, show μ * ((sp A B C - c A B C) / a A B C) =
      (μ * (sp A B C - c A B C)) / a A B C by ring, hM3]
    ring
  have hxG' : xG = -(b A B C) / (2 * a A B C) := by
    rw [hxG, hμ]
    have h2 : sp A B C - c A B C ≠ 0 := (hsc A B C hABC).ne'
    have h2' : (2 : ℝ) * (sp A B C - c A B C) ≠ 0 := mul_ne_zero two_ne_zero h2
    apply mul_left_cancel₀ h2'
    rw [mul_add, div_mul_eq_mul_div, mul_div_cancel₀ _ h2']
    simp only [sp] at h2' ⊢
    field_simp [ha', hc']
    ring
  -- Assemble `G` from its coordinates.
  have hw' : ∑ i, ![1 - xG - yG, xG, yG] i = 1 := by
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    ring
  have e := comb_vsub_A A B C hABC ![1 - xG - yG, xG, yG] hw'
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons] at e
  rw [← hGA₂] at e
  have hG' : G = Finset.univ.affineCombination ℝ ![A, B, C] ![1 - xG - yG, xG, yG] :=
    (vsub_left_injective A e).symm
  have hweights : ![1 - xG - yG, xG, yG] =
      ![1 / 2, -(b A B C) / (2 * a A B C), (a A B C + b A B C) / (2 * a A B C)] := by
    funext i
    fin_cases i
    · show 1 - xG - yG = 1 / 2
      rw [hxG', hyG']
      have h2a : (2 : ℝ) * a A B C ≠ 0 := mul_ne_zero two_ne_zero ha'
      field_simp [h2a]
      ring
    · show xG = -(b A B C) / (2 * a A B C)
      exact hxG'
    · show yG = (a A B C + b A B C) / (2 * a A B C)
      exact hyG'
  rw [hG', hweights]

/-- The point `T = AG ∩ BC` is the line map of `BC` at `(a + b) / a`. -/
lemma T_eq (G T : P)
    (hG : G ∈ line[ℝ, K A B C hABC, M A B C hABC] ⊓ line[ℝ, C, J A B C hABC])
    (hT : T ∈ line[ℝ, A, G] ⊓ line[ℝ, B, C]) :
    T = AffineMap.lineMap B C ((a A B C + b A B C) / a A B C) := by
  have hG' := G_eq_comb A B C hABC G hG
  have ha' := (ha A B C hABC).ne'
  obtain ⟨w, hw, hTw⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype
    (show T ∈ affineSpan ℝ (Set.range ![B, C]) by
      rw [range_pair A B C hABC]
      exact hT.2)
  rw [comb2_eq_lineMap A B C hABC _ _ _ hw] at hTw
  set τ := w 1 with hτ
  rw [hTw]
  congr 1
  have hTA : (AffineMap.lineMap B C τ) -ᵥ A = (1 - τ) • (B -ᵥ A) + τ • (C -ᵥ A) := by
    rw [AffineMap.lineMap_apply, vadd_vsub_assoc,
      show C -ᵥ B = (C -ᵥ A) - (B -ᵥ A) from (vsub_sub_vsub_cancel_right _ _ _).symm]
    module
  have hTd : (AffineMap.lineMap B C τ) -ᵥ A ∈ (line[ℝ, A, G]).direction := by
    refine (AffineSubspace.vsub_right_mem_direction_iff_mem ?_ _).mpr ?_
    · exact left_mem_affineSpan_pair ℝ A G
    · rw [← hTw]
      exact hT.1
  rw [direction_affineSpan, vectorSpan_pair_rev] at hTd
  obtain ⟨ρ, hρ⟩ := Submodule.mem_span_singleton.mp hTd
  have hwG : ∑ i, ![1 / 2, -(b A B C) / (2 * a A B C), (a A B C + b A B C) / (2 * a A B C)] i = 1 := by
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    field_simp [ha']
    ring
  have hGvA : G -ᵥ A = (-(b A B C) / (2 * a A B C)) • (B -ᵥ A) +
      ((a A B C + b A B C) / (2 * a A B C)) • (C -ᵥ A) := by
    rw [hG', comb_vsub_A A B C hABC _ hwG]
    simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons]
  have hTAρ : (AffineMap.lineMap B C τ) -ᵥ A =
      (ρ * (-(b A B C) / (2 * a A B C))) • (B -ᵥ A) +
        (ρ * ((a A B C + b A B C) / (2 * a A B C))) • (C -ᵥ A) := by
    rw [← hρ, hGvA]
    module
  obtain ⟨eq1, eq2⟩ := coord_unique A B C hABC (hTA.symm.trans hTAρ)
  have e1 : (1 - τ) * (2 * a A B C) = -ρ * b A B C := by
    field_simp [ha'] at eq1
    ring_nf at eq1 ⊢
    linarith [eq1]
  have e2 : τ * (2 * a A B C) = ρ * (a A B C + b A B C) := by
    field_simp [ha'] at eq2
    ring_nf at eq2 ⊢
    linarith [eq2]
  have e3 : 2 * a A B C = ρ * a A B C := by linear_combination e1 + e2
  have hρ2 : ρ = 2 := mul_right_cancel₀ ha' e3.symm
  rw [hρ2] at e2
  field_simp [ha']
  ring_nf at e2 ⊢
  linarith [e2]

end

snip end

problem imo2012_p1 (A B C : P) (hABC : AffineIndependent ℝ ![A, B, C])
    (F G S T : P)
    (hF : F ∈ line[ℝ, L A B C hABC, M A B C hABC] ⊓ line[ℝ, B, J A B C hABC])
    (hG : G ∈ line[ℝ, K A B C hABC, M A B C hABC] ⊓ line[ℝ, C, J A B C hABC])
    (hS : S ∈ line[ℝ, A, F] ⊓ line[ℝ, B, C])
    (hT : T ∈ line[ℝ, A, G] ⊓ line[ℝ, B, C]) :
    M A B C hABC = midpoint ℝ S T := by
  have hT' := T_eq A B C hABC G T hG hT
  -- The problem is symmetric in `B` and `C`: apply `T_eq` to the reindexed
  -- triangle `(A, C, B)` to compute `S`.
  have hABC' : AffineIndependent ℝ ![A, C, B] := by
    have h := hABC.comp_embedding (Equiv.swap 1 2).toEmbedding
    rwa [show (![A, B, C] ∘ (Equiv.swap 1 2).toEmbedding) = ![A, C, B] from
      funext (fun i ↦ by fin_cases i <;> rfl)] at h
  have htri : tri A C B hABC' = (tri A B C hABC).reindex (Equiv.swap 1 2) := by
    rw [Simplex.ext_iff]
    intro i
    fin_cases i <;> rfl
  have hJ_re : J A C B hABC' = J A B C hABC := by
    show (tri A C B hABC').excenter {0} = J A B C hABC
    rw [htri, Simplex.excenter_reindex]
    simp [Equiv.symm_swap, Equiv.swap_apply_of_ne_of_ne]
  have hM_re : M A C B hABC' = M A B C hABC := by
    show (tri A C B hABC').touchpoint {0} 0 = M A B C hABC
    rw [htri, Simplex.touchpoint_reindex]
    simp [Equiv.symm_swap, Equiv.swap_apply_of_ne_of_ne]
  have hL_re : K A C B hABC' = L A B C hABC := by
    show (tri A C B hABC').touchpoint {0} 2 = L A B C hABC
    rw [htri, Simplex.touchpoint_reindex]
    simp [Equiv.symm_swap, Equiv.swap_apply_of_ne_of_ne]
  have hS' : S = AffineMap.lineMap C B ((a A C B + b A C B) / a A C B) := by
    refine T_eq A C B hABC' F S ?_ ?_
    · rw [hL_re, hM_re, hJ_re]
      exact hF
    · rw [show line[ℝ, C, B] = line[ℝ, B, C] from by rw [Set.pair_comm C B]]
      exact hS
  have ha' := (ha A B C hABC).ne'
  have hr : (a A C B + b A C B) / a A C B = (a A B C + c A B C) / a A B C := by
    simp only [a, b, c, dist_comm C B]
  -- Coordinates of `S`, `M`, `T` relative to `A`.
  have hSA : S -ᵥ A = ((a A B C + c A B C) / a A B C) • (B -ᵥ A) +
      (-(c A B C) / a A B C) • (C -ᵥ A) := by
    rw [hS', hr, show (AffineMap.lineMap C B ((a A B C + c A B C) / a A B C)) -ᵥ A =
        ((AffineMap.lineMap C B ((a A B C + c A B C) / a A B C)) -ᵥ C) + (C -ᵥ A) from
        (vsub_add_vsub_cancel _ C A).symm,
      AffineMap.lineMap_vsub_left,
      show B -ᵥ C = (B -ᵥ A) - (C -ᵥ A) from (vsub_sub_vsub_cancel_right _ _ _).symm]
    have h1 : (1 : ℝ) - (a A B C + c A B C) / a A B C = -(c A B C) / a A B C := by
      field_simp [ha']
      ring
    rw [show ((a A B C + c A B C) / a A B C) • ((B -ᵥ A) - (C -ᵥ A)) + (C -ᵥ A) =
        ((a A B C + c A B C) / a A B C) • (B -ᵥ A) +
          (1 - (a A B C + c A B C) / a A B C) • (C -ᵥ A) by
      module, h1]
  have hTA : T -ᵥ A = (-(b A B C) / a A B C) • (B -ᵥ A) +
      ((a A B C + b A B C) / a A B C) • (C -ᵥ A) := by
    rw [hT', AffineMap.lineMap_apply, vadd_vsub_assoc,
      show C -ᵥ B = (C -ᵥ A) - (B -ᵥ A) from (vsub_sub_vsub_cancel_right _ _ _).symm]
    have h2 : (1 : ℝ) - (a A B C + b A B C) / a A B C = -(b A B C) / a A B C := by
      field_simp [ha']
      ring
    rw [show ((a A B C + b A B C) / a A B C) • ((C -ᵥ A) - (B -ᵥ A)) + (B -ᵥ A) =
        (1 - (a A B C + b A B C) / a A B C) • (B -ᵥ A) +
          ((a A B C + b A B C) / a A B C) • (C -ᵥ A) by
      module, h2]
  -- The key vector equality: `S -ᵥ M = M -ᵥ T`.
  have key : S -ᵥ M A B C hABC = M A B C hABC -ᵥ T := by
    rw [show S -ᵥ M A B C hABC = (S -ᵥ A) - (M A B C hABC -ᵥ A) from
        (vsub_sub_vsub_cancel_right _ _ _).symm,
      show M A B C hABC -ᵥ T = (M A B C hABC -ᵥ A) - (T -ᵥ A) from
        (vsub_sub_vsub_cancel_right _ _ _).symm,
      hSA, M_vsub_A A B C hABC, hTA]
    have h1 : (a A B C + c A B C) / a A B C - (sp A B C - b A B C) / a A B C =
        sp A B C / a A B C := by
      simp only [sp]
      field_simp [ha']
      ring
    have h2 : -(c A B C) / a A B C - (sp A B C - c A B C) / a A B C =
        -(sp A B C / a A B C) := by
      simp only [sp]
      field_simp [ha']
      ring
    have h3 : (sp A B C - b A B C) / a A B C - -(b A B C) / a A B C =
        sp A B C / a A B C := by
      simp only [sp]
      field_simp [ha']
      ring
    have h4 : (sp A B C - c A B C) / a A B C - (a A B C + b A B C) / a A B C =
        -(sp A B C / a A B C) := by
      simp only [sp]
      field_simp [ha']
      ring
    rw [show ((a A B C + c A B C) / a A B C) • (B -ᵥ A) + (-(c A B C) / a A B C) • (C -ᵥ A) -
        (((sp A B C - b A B C) / a A B C) • (B -ᵥ A) +
          ((sp A B C - c A B C) / a A B C) • (C -ᵥ A)) =
      ((a A B C + c A B C) / a A B C - (sp A B C - b A B C) / a A B C) • (B -ᵥ A) +
        (-(c A B C) / a A B C - (sp A B C - c A B C) / a A B C) • (C -ᵥ A) by
      module]
    rw [show ((sp A B C - b A B C) / a A B C) • (B -ᵥ A) +
        ((sp A B C - c A B C) / a A B C) • (C -ᵥ A) -
        ((-(b A B C) / a A B C) • (B -ᵥ A) +
          ((a A B C + b A B C) / a A B C) • (C -ᵥ A)) =
      ((sp A B C - b A B C) / a A B C - -(b A B C) / a A B C) • (B -ᵥ A) +
        ((sp A B C - c A B C) / a A B C - (a A B C + b A B C) / a A B C) • (C -ᵥ A) by
      module]
    rw [h1, h2, h3, h4]
  -- Conclude the midpoint.
  have hmid : midpoint ℝ S T -ᵥ T = M A B C hABC -ᵥ T := by
    rw [midpoint_vsub_right, ← key,
      show S -ᵥ T = (S -ᵥ M A B C hABC) + (M A B C hABC -ᵥ T) from
        (vsub_add_vsub_cancel S _ T).symm, ← key]
    rw [show (⅟2 : ℝ) • ((S -ᵥ M A B C hABC) + (S -ᵥ M A B C hABC)) =
        S -ᵥ M A B C hABC from by
      rw [← two_smul ℝ (S -ᵥ M A B C hABC), smul_smul, invOf_mul_self, one_smul]]
  exact (vsub_left_injective T hmid).symm

end Imo2012P1
