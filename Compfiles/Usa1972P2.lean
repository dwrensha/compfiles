/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.Convex.StrictConvexBetween
public import Mathlib.Analysis.InnerProductSpace.OfNorm
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# USA Mathematical Olympiad 1972, Problem 2

A tetrahedron has opposite sides equal. Show that all faces are acute-angled.
-/

namespace Usa1972P2

open scoped EuclideanGeometry InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {P : Type*} [MetricSpace P] [NormedAddTorsor V P]

snip begin

/-- Two nonzero vectors with positive inner product form an acute angle. -/
lemma angle_lt_pi_div_two_of_inner_pos {x y : V} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : 0 < ⟪x, y⟫_ℝ) : InnerProductGeometry.angle x y < Real.pi / 2 := by
  have hcos : 0 < Real.cos (InnerProductGeometry.angle x y) := by
    rw [InnerProductGeometry.cos_angle]
    exact div_pos h (mul_pos (norm_pos_iff.mpr hx) (norm_pos_iff.mpr hy))
  by_contra hle
  push Not at hle
  have hnonpos : Real.cos (InnerProductGeometry.angle x y) ≤ 0 :=
    Real.cos_nonpos_of_pi_div_two_le_of_le hle
      (le_trans (InnerProductGeometry.angle_le_pi x y) (by linarith [Real.pi_pos]))
  linarith

/-- The midpoint of `B C` as a vector from an arbitrary base point `A`. -/
lemma midpoint_vsub' (A B C : P) :
    midpoint ℝ B C -ᵥ A = (1 / 2 : ℝ) • ((B -ᵥ A) + (C -ᵥ A)) := by
  rw [← vsub_add_vsub_cancel (midpoint ℝ B C) B A, midpoint_vsub_left,
    ← vsub_sub_vsub_cancel_right C B A, show (⅟2 : ℝ) = 1 / 2 by norm_num [invOf_eq_inv]]
  module

/-- The distances from `A` and from `D` to the midpoint of `BC` are equal
(the algebraic content of the congruence of the triangles `ABC` and `DCB`). -/
lemma dist_midpoint_left_eq_right (A B C D : P)
    (hAB : dist A B = dist C D) (hAC : dist A C = dist B D) :
    dist A (midpoint ℝ B C) = dist D (midpoint ℝ B C) := by
  have key : 2 * ⟪D -ᵥ A, (B -ᵥ A) + (C -ᵥ A)⟫_ℝ = 2 * ‖D -ᵥ A‖ ^ 2 := by
    have e1 : ‖B -ᵥ A‖ ^ 2 = ‖(D -ᵥ A) - (C -ᵥ A)‖ ^ 2 := by
      have h := congrArg (· ^ 2) hAB
      rwa [dist_eq_norm_vsub', dist_eq_norm_vsub', ← vsub_sub_vsub_cancel_right D C A] at h
    have e2 : ‖C -ᵥ A‖ ^ 2 = ‖(D -ᵥ A) - (B -ᵥ A)‖ ^ 2 := by
      have h := congrArg (· ^ 2) hAC
      rwa [dist_eq_norm_vsub', dist_eq_norm_vsub', ← vsub_sub_vsub_cancel_right D B A] at h
    rw [norm_sub_sq_real] at e1 e2
    rw [inner_add_right]
    linarith
  rw [dist_eq_norm_vsub', dist_eq_norm_vsub', midpoint_vsub',
    ← vsub_sub_vsub_cancel_right (midpoint ℝ B C) D A, midpoint_vsub',
    ← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sub_sq_real, real_inner_smul_left]
  simp only [norm_smul, Real.norm_eq_abs]
  rw [abs_of_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num)]
  have hcomm : ⟪(B -ᵥ A) + (C -ᵥ A), D -ᵥ A⟫_ℝ = ⟪D -ᵥ A, (B -ᵥ A) + (C -ᵥ A)⟫_ℝ :=
    real_inner_comm _ _
  linarith

/-- In a genuine tetrahedron `A B C D`, the midpoint of `BC` is not on the
segment `AD` (so the triangle inequality `AM + MD ≥ AD` is strict). -/
lemma not_wbtw_midpoint (A B C D : P) (hind : AffineIndependent ℝ ![A, B, C, D]) :
    ¬ Wbtw ℝ A (midpoint ℝ B C) D := by
  have hAM : A ≠ midpoint ℝ B C := by
    intro h
    have h1 : midpoint ℝ B C ∈ affineSpan ℝ ({B, C} : Set P) :=
      AffineMap.lineMap_mem_affineSpan_pair (⅟2 : ℝ) B C
    rw [← h] at h1
    have h2 : ({B, C} : Set P) ⊆ ![A, B, C, D] '' (Set.univ \ {(0 : Fin 4)}) := by
      intro x hx
      rcases hx with rfl | rfl
      · exact ⟨1, by decide, by simp⟩
      · exact ⟨2, by decide, by simp⟩
    exact hind.notMem_affineSpan_sdiff 0 Set.univ (affineSpan_mono ℝ h2 h1)
  intro hw
  have hcol : Collinear ℝ ({A, midpoint ℝ B C, D} : Set P) := hw.collinear
  have hD : D ∈ affineSpan ℝ ({A, midpoint ℝ B C} : Set P) :=
    hcol.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hAM
  have hM : midpoint ℝ B C ∈ affineSpan ℝ ({B, C} : Set P) :=
    AffineMap.lineMap_mem_affineSpan_pair (⅟2 : ℝ) B C
  have hsub : ({A, midpoint ℝ B C} : Set P) ⊆ affineSpan ℝ ({A, B, C} : Set P) := by
    intro x hx
    rcases hx with rfl | rfl
    · exact mem_affineSpan ℝ (by simp)
    · exact affineSpan_mono ℝ (by intro y hy; rcases hy with rfl | rfl <;> simp) hM
  have hDABC : D ∈ affineSpan ℝ ({A, B, C} : Set P) := affineSpan_le.2 hsub hD
  have him : ({A, B, C} : Set P) ⊆ ![A, B, C, D] '' (Set.univ \ {(3 : Fin 4)}) := by
    intro x hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨0, by decide, by simp⟩
    · exact ⟨1, by decide, by simp⟩
    · exact ⟨2, by decide, by simp⟩
  exact hind.notMem_affineSpan_sdiff 3 Set.univ (affineSpan_mono ℝ him hDABC)

/-- Affine independence of a family of four points is preserved when the
family is permuted. -/
lemma hind_permute {A B C D : P} (hind : AffineIndependent ℝ ![A, B, C, D])
    {i₀ i₁ i₂ i₃ : Fin 4} (hi : Function.Injective ![i₀, i₁, i₂, i₃]) :
    AffineIndependent ℝ
      ![![A, B, C, D] i₀, ![A, B, C, D] i₁, ![A, B, C, D] i₂, ![A, B, C, D] i₃] := by
  have he : ![![A, B, C, D] i₀, ![A, B, C, D] i₁, ![A, B, C, D] i₂, ![A, B, C, D] i₃] =
      ![A, B, C, D] ∘ ![i₀, i₁, i₂, i₃] := by
    ext j
    fin_cases j <;> simp [Function.comp_apply]
  rw [he]
  exact hind.comp_embedding ⟨![i₀, i₁, i₂, i₃], hi⟩

/-- The angle at vertex `A` of the face `ABC` is acute. This is the key step:
`AM = DM` with `M` the midpoint of `BC`, the strict triangle inequality
`AM + MD > AD`, and `AD = BC` give `AM > MC`, which means that the inner
product of `B -ᵥ A` and `C -ᵥ A` is positive. -/
lemma angle_acute_at (A B C D : P) (hind : AffineIndependent ℝ ![A, B, C, D])
    (hAB : dist A B = dist C D) (hAC : dist A C = dist B D)
    (hAD : dist A D = dist B C) :
    ∠ B A C < Real.pi / 2 := by
  have hBA : B ≠ A := hind.injective.ne (by decide : (1 : Fin 4) ≠ 0)
  have hCA : C ≠ A := hind.injective.ne (by decide : (2 : Fin 4) ≠ 0)
  have hstrict : dist A D < dist A (midpoint ℝ B C) + dist (midpoint ℝ B C) D :=
    dist_lt_dist_add_dist_iff.mpr (not_wbtw_midpoint A B C D hind)
  have hmid : dist A (midpoint ℝ B C) = dist D (midpoint ℝ B C) :=
    dist_midpoint_left_eq_right A B C D hAB hAC
  have hlt : ‖D -ᵥ A‖ < ‖(B -ᵥ A) + (C -ᵥ A)‖ := by
    have h2 : dist A (midpoint ℝ B C) = (1 / 2) * ‖(B -ᵥ A) + (C -ᵥ A)‖ := by
      rw [dist_eq_norm_vsub', midpoint_vsub', norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num)]
    have h3 : dist (midpoint ℝ B C) D = (1 / 2) * ‖(B -ᵥ A) + (C -ᵥ A)‖ := by
      rw [dist_comm (midpoint ℝ B C) D, ← hmid, h2]
    rw [dist_eq_norm_vsub', h2, h3] at hstrict
    linarith
  have hsq : ‖D -ᵥ A‖ ^ 2 < ‖(B -ᵥ A) + (C -ᵥ A)‖ ^ 2 :=
    pow_lt_pow_left₀ hlt (norm_nonneg _) two_ne_zero
  rw [norm_add_sq_real] at hsq
  have hAD' : ‖D -ᵥ A‖ ^ 2 = ‖C -ᵥ A‖ ^ 2 - 2 * ⟪C -ᵥ A, B -ᵥ A⟫_ℝ + ‖B -ᵥ A‖ ^ 2 := by
    have h := congrArg (· ^ 2) hAD
    rw [dist_eq_norm_vsub', dist_eq_norm_vsub', ← vsub_sub_vsub_cancel_right C B A,
      norm_sub_sq_real] at h
    exact h
  have hcomm : ⟪C -ᵥ A, B -ᵥ A⟫_ℝ = ⟪B -ᵥ A, C -ᵥ A⟫_ℝ := real_inner_comm _ _
  have hinner : 0 < ⟪B -ᵥ A, C -ᵥ A⟫_ℝ := by linarith
  rw [EuclideanGeometry.angle]
  exact angle_lt_pi_div_two_of_inner_pos (vsub_ne_zero.mpr hBA) (vsub_ne_zero.mpr hCA) hinner

snip end

problem usa1972_p2 (A B C D : P) (hind : AffineIndependent ℝ ![A, B, C, D])
    (hAB : dist A B = dist C D) (hAC : dist A C = dist B D) (hAD : dist A D = dist B C) :
    (∠ B A C < Real.pi / 2 ∧ ∠ A B C < Real.pi / 2 ∧ ∠ B C A < Real.pi / 2) ∧
    (∠ B A D < Real.pi / 2 ∧ ∠ A B D < Real.pi / 2 ∧ ∠ B D A < Real.pi / 2) ∧
    (∠ C A D < Real.pi / 2 ∧ ∠ A C D < Real.pi / 2 ∧ ∠ C D A < Real.pi / 2) ∧
    (∠ C B D < Real.pi / 2 ∧ ∠ B C D < Real.pi / 2 ∧ ∠ B D C < Real.pi / 2) := by
  have h1 := angle_acute_at A B C D hind hAB hAC hAD
  have h2 := angle_acute_at B A C D
    (hind_permute (i₀ := 1) (i₁ := 0) (i₂ := 2) (i₃ := 3) hind (by decide))
    ((dist_comm B A).trans hAB) hAD.symm hAC.symm
  have h3 := angle_acute_at C B A D
    (hind_permute (i₀ := 2) (i₁ := 1) (i₂ := 0) (i₃ := 3) hind (by decide))
    ((dist_comm C B).trans hAD.symm) ((dist_comm C A).trans hAC)
    (hAB.symm.trans (dist_comm A B))
  have h4 := angle_acute_at A B D C
    (hind_permute (i₀ := 0) (i₁ := 1) (i₂ := 3) (i₃ := 2) hind (by decide))
    (hAB.trans (dist_comm C D)) hAD hAC
  have h5 := angle_acute_at B A D C
    (hind_permute (i₀ := 1) (i₁ := 0) (i₂ := 3) (i₃ := 2) hind (by decide))
    ((dist_comm B A).trans (hAB.trans (dist_comm C D))) hAC.symm
    hAD.symm
  have h6 := angle_acute_at D B A C
    (hind_permute (i₀ := 3) (i₁ := 1) (i₂ := 0) (i₃ := 2) hind (by decide))
    ((dist_comm D B).trans hAC.symm) ((dist_comm D A).trans hAD)
    ((dist_comm D C).trans (hAB.symm.trans (dist_comm A B)))
  have h7 := angle_acute_at A C D B
    (hind_permute (i₀ := 0) (i₁ := 2) (i₂ := 3) (i₃ := 1) hind (by decide))
    (hAC.trans (dist_comm B D)) (hAD.trans (dist_comm B C)) hAB
  have h8 := angle_acute_at C A D B
    (hind_permute (i₀ := 2) (i₁ := 0) (i₂ := 3) (i₃ := 1) hind (by decide))
    ((dist_comm C A).trans (hAC.trans (dist_comm B D))) hAB.symm
    ((dist_comm C B).trans hAD.symm)
  have h9 := angle_acute_at D C A B
    (hind_permute (i₀ := 3) (i₁ := 2) (i₂ := 0) (i₃ := 1) hind (by decide))
    ((dist_comm D C).trans hAB.symm) ((dist_comm D A).trans (hAD.trans (dist_comm B C)))
    ((dist_comm D B).trans (hAC.symm.trans (dist_comm A C)))
  have h10 := angle_acute_at B C D A
    (hind_permute (i₀ := 1) (i₁ := 2) (i₂ := 3) (i₃ := 0) hind (by decide))
    (hAD.symm.trans (dist_comm A D)) (hAC.symm.trans (dist_comm A C))
    ((dist_comm B A).trans hAB)
  have h11 := angle_acute_at C B D A
    (hind_permute (i₀ := 2) (i₁ := 1) (i₂ := 3) (i₃ := 0) hind (by decide))
    ((dist_comm C B).trans (hAD.symm.trans (dist_comm A D)))
    (hAB.symm.trans (dist_comm A B)) ((dist_comm C A).trans hAC)
  have h12 := angle_acute_at D B C A
    (hind_permute (i₀ := 3) (i₁ := 1) (i₂ := 2) (i₃ := 0) hind (by decide))
    ((dist_comm D B).trans (hAC.symm.trans (dist_comm A C)))
    ((dist_comm D C).trans (hAB.symm.trans (dist_comm A B))) ((dist_comm D A).trans hAD)
  exact ⟨⟨h1, h2, h3⟩, ⟨h4, h5, h6⟩, ⟨h7, h8, h9⟩, ⟨h10, h11, h12⟩⟩

end Usa1972P2
