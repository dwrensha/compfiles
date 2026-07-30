/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality
public import Mathlib.Geometry.Euclidean.Triangle
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# USA Mathematical Olympiad 1996, Problem 5

Triangle ABC has the following property: there is an interior point P
such that ∠PAB = 10°, ∠PBA = 20°, ∠PCA = 30° and ∠PAC = 40°.
Prove that triangle ABC is isosceles.
-/

namespace Usa1996P5

open scoped Affine EuclideanGeometry Real

snip begin

/-- Trigonometric form of Ceva's theorem. -/
theorem trigonometric_ceva
    (A B C P : EuclideanSpace ℝ (Fin 2))
    (hABC : AffineIndependent ℝ ![A, B, C])
    : Real.sin (∠ P A B) * Real.sin (∠ P B C) * Real.sin (∠ P C A)
      = Real.sin (∠ A B P) * Real.sin (∠ B C P) * Real.sin (∠ C A P) := by
  have hAneB := (hABC.injective.ne (by decide : (0 : Fin 3) ≠ 1))
  have hBneC := (hABC.injective.ne (by decide : (1 : Fin 3) ≠ 2))
  have hCneA := (hABC.injective.ne (by decide : (2 : Fin 3) ≠ 0))
  dsimp [-ne_eq] at hAneB hBneC hCneA
  by_cases! h : P = A ∨ P = B ∨ P = C
  · casesm* _ ∨ _
    · rw [h]
      rw [EuclideanGeometry.angle_self_of_ne hAneB]
      rw [EuclideanGeometry.angle_self_of_ne hCneA.symm]
      rw [Real.sin_zero]
      ring
    · rw [h]
      rw [EuclideanGeometry.angle_self_of_ne hBneC]
      rw [EuclideanGeometry.angle_self_of_ne hAneB.symm]
      simp only [Real.sin_zero, mul_zero, zero_mul]
    · rw [h]
      rw [EuclideanGeometry.angle_self_of_ne hCneA]
      rw [EuclideanGeometry.angle_self_of_ne hBneC.symm]
      simp only [Real.sin_zero, mul_zero, zero_mul]
  · rcases h with ⟨hPA, hPB, hPC⟩
    have hAB := EuclideanGeometry.law_sin A B P
    have hBC := EuclideanGeometry.law_sin B C P
    have hCA := EuclideanGeometry.law_sin C A P
    rw [dist_comm] at hAB hBC hCA
    rw [← dist_ne_zero] at hPA hPB hPC
    rw [← eq_div_iff hPB] at hAB
    rw [← eq_div_iff hPC] at hBC
    rw [← eq_div_iff hPA] at hCA
    rw [hAB, hBC, hCA]
    field

/-- Given a triangle `ABC` and an interior point `P`,
`∠ A B C = ∠ A B P + ∠ P B C`. -/
lemma angle_eq_angle_add_angle_of_mem_interior
    {A B C P : EuclideanSpace ℝ (Fin 2)}
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hP : P ∈ interior (convexHull ℝ {A, B, C}))
    : ∠ A B C = ∠ A B P + ∠ P B C := by
  have htot' : affineSpan ℝ (Set.range ![A, B, C]) = ⊤ := by
    rw [AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nontrivial]
    apply AffineIndependent.vectorSpan_eq_top_of_card_eq_finrank_add_one hABC
    rw [finrank_euclideanSpace]
    simp only [Nat.succ_eq_add_one, zero_add, Nat.reduceAdd, Fintype.card_fin]
  set basis := AffineBasis.mk _ hABC htot' with h_basis
  have h_range : {A, B, C} = Set.range basis := by
    rw [h_basis, DFunLike.coe, AffineBasis.instFunLike]
    simp
    rw [Set.pair_comm, Set.insert_comm, Set.pair_comm]
  rw [h_range, AffineBasis.interior_convexHull] at hP
  dsimp at hP
  repeat rw [EuclideanGeometry.angle]
  have hA : A = basis 0 := by
    rw [h_basis, DFunLike.coe, AffineBasis.instFunLike]
    simp
  have hB : B = basis 1 := by
    rw [h_basis, DFunLike.coe, AffineBasis.instFunLike]
    simp
  have hC : C = basis 2 := by
    rw [h_basis, DFunLike.coe, AffineBasis.instFunLike]
    simp
  have hPB : P -ᵥ B ≠ 0 := by
    rw [vsub_eq_zero_iff_eq.ne]
    contrapose! hP
    use 0
    rw [hP, hB, AffineBasis.coord_apply_ne basis (by norm_num)]
  rw [InnerProductGeometry.angle_eq_angle_add_angle_iff hPB]
  right
  rw [Submodule.mem_span_pair]
  have hsum := AffineBasis.linear_combination_coord_eq_self basis P
  have hsum' := AffineBasis.sum_coord_apply_eq_one basis P
  rw [Fin.sum_univ_three] at hsum hsum'
  use ⟨(basis.coord 0) P, le_of_lt (hP 0)⟩
  use ⟨(basis.coord 2) P, le_of_lt (hP 2)⟩
  set_option backward.isDefEq.respectTransparency false in
  rw [NNReal.smul_def, NNReal.smul_def, NNReal.toReal, Subtype.val, Subtype.val]
  dsimp
  nth_rw 3 [← hsum]
  rw [smul_sub, smul_sub]
  rw [← hA, ← hB, ← hC, ← sub_eq_zero]
  abel_nf
  rw [← add_assoc, ← add_assoc]
  rw [← smul_add, ← smul_add, ← add_smul, ← add_smul, add_right_comm]
  rw [hsum', one_smul, neg_smul, one_smul, neg_add_cancel]

lemma affineIndependent_rotate {A B C : EuclideanSpace ℝ (Fin 2)}
    (hABC : AffineIndependent ℝ ![A, B, C])
    : AffineIndependent ℝ ![B, C, A] := by
  rw [affineIndependent_iff_not_collinear_set] at hABC ⊢
  rw [Set.pair_comm, Set.insert_comm]
  exact hABC

/-- The sum of the six angles around an interior point of a triangle. -/
lemma sum_angle {A B C P : EuclideanSpace ℝ (Fin 2)}
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hP : P ∈ interior (convexHull ℝ {A, B, C}))
    : ∠ P A B + ∠ P B C + ∠ P C A + ∠ A B P + ∠ B C P + ∠ C A P = π := by
  rw [← EuclideanGeometry.angle_add_angle_add_angle_eq_pi
    C (hABC.injective.ne (by decide : (1 : Fin 3) ≠ 0))]
  dsimp
  rw [angle_eq_angle_add_angle_of_mem_interior hABC hP]
  apply affineIndependent_rotate at hABC
  rw [Set.insert_comm, Set.pair_comm] at hP
  rw [angle_eq_angle_add_angle_of_mem_interior hABC hP]
  apply affineIndependent_rotate at hABC
  rw [Set.insert_comm, Set.pair_comm] at hP
  rw [angle_eq_angle_add_angle_of_mem_interior hABC hP]
  ring

/-- The trigonometric identity behind the problem:
`sin 60° sin 30° sin 10° = sin² 20° sin 40°`. -/
lemma key_trig : Real.sin (π / 3) * Real.sin (π / 6) * Real.sin (π / 18)
    = Real.sin (π / 9) * Real.sin (π / 9) * Real.sin (2 * π / 9) := by
  have hsin_sin : ∀ a b : ℝ, Real.sin a * Real.sin b
      = (Real.cos (a - b) - Real.cos (a + b)) / 2 := by
    intro a b
    rw [Real.cos_sub, Real.cos_add]
    ring
  have e1 : Real.sin (π / 3) * Real.sin (π / 18)
      = (Real.sin (2 * π / 9) - Real.sin (π / 9)) / 2 := by
    rw [hsin_sin]
    rw [show π / 3 - π / 18 = π / 2 - 2 * π / 9 by ring,
      show π / 3 + π / 18 = π / 2 - π / 9 by ring,
      Real.cos_pi_div_two_sub, Real.cos_pi_div_two_sub]
  have e2 : Real.sin (π / 9) * Real.sin (2 * π / 9)
      = (Real.cos (π / 9) - 1 / 2) / 2 := by
    rw [hsin_sin]
    rw [show π / 9 - 2 * π / 9 = -(π / 9) by ring, Real.cos_neg,
      show π / 9 + 2 * π / 9 = π / 3 by ring, Real.cos_pi_div_three]
  have e3 : Real.sin (π / 9) * Real.cos (π / 9) = Real.sin (2 * π / 9) / 2 := by
    have h := Real.sin_two_mul (π / 9)
    rw [show (2 : ℝ) * (π / 9) = 2 * π / 9 by ring] at h
    linarith [h]
  rw [show Real.sin (π / 3) * Real.sin (π / 6) * Real.sin (π / 18)
      = Real.sin (π / 6) * (Real.sin (π / 3) * Real.sin (π / 18)) by ring]
  rw [e1, Real.sin_pi_div_six]
  rw [show Real.sin (π / 9) * Real.sin (π / 9) * Real.sin (2 * π / 9)
      = Real.sin (π / 9) * (Real.sin (π / 9) * Real.sin (2 * π / 9)) by ring]
  rw [e2]
  linarith [e3]

/-- Solving the trigonometric Ceva equation together with the angle sum
constraint: the only possibility is `x = 60°` and `y = 20°`. -/
lemma solve_angles {x y : ℝ} (hx0 : 0 ≤ x) (hy0 : 0 ≤ y)
    (hsum : x + y = 4 * π / 9)
    (hceva : Real.sin (π / 18) * Real.sin x * Real.sin (π / 6)
      = Real.sin (π / 9) * Real.sin y * Real.sin (2 * π / 9)) :
    x = π / 3 ∧ y = π / 9 := by
  have hπ := Real.pi_pos
  have s10 : 0 < Real.sin (π / 18) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have s20 : 0 < Real.sin (π / 9) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have s30 : 0 < Real.sin (π / 6) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have s40 : 0 < Real.sin (2 * π / 9) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hceva' : Real.sin x * (Real.sin (π / 18) * Real.sin (π / 6))
      = Real.sin y * (Real.sin (π / 9) * Real.sin (2 * π / 9)) := by
    linear_combination hceva
  have key : Real.sin (π / 3) * (Real.sin (π / 18) * Real.sin (π / 6))
      = Real.sin (π / 9) * (Real.sin (π / 9) * Real.sin (2 * π / 9)) := by
    linear_combination key_trig
  rcases lt_trichotomy x (π / 3) with h | h | h
  · exfalso
    have hsx : Real.sin x < Real.sin (π / 3) :=
      Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) (by linarith) h
    have hygt : π / 9 < y := by linarith
    have hsy : Real.sin (π / 9) < Real.sin y :=
      Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) (by linarith) hygt
    have step1 : Real.sin x * (Real.sin (π / 18) * Real.sin (π / 6))
        < Real.sin (π / 3) * (Real.sin (π / 18) * Real.sin (π / 6)) :=
      mul_lt_mul_of_pos_right hsx (mul_pos s10 s30)
    have step2 : Real.sin (π / 9) * (Real.sin (π / 9) * Real.sin (2 * π / 9))
        < Real.sin y * (Real.sin (π / 9) * Real.sin (2 * π / 9)) :=
      mul_lt_mul_of_pos_right hsy (mul_pos s20 s40)
    rw [key] at step1
    linarith
  · exact ⟨h, by linarith⟩
  · exfalso
    have hsx : Real.sin (π / 3) < Real.sin x :=
      Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) (by linarith) h
    have hylt : y < π / 9 := by linarith
    have hsy : Real.sin y < Real.sin (π / 9) :=
      Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) (by linarith) hylt
    have step1 : Real.sin (π / 3) * (Real.sin (π / 18) * Real.sin (π / 6))
        < Real.sin x * (Real.sin (π / 18) * Real.sin (π / 6)) :=
      mul_lt_mul_of_pos_right hsx (mul_pos s10 s30)
    have step2 : Real.sin y * (Real.sin (π / 9) * Real.sin (2 * π / 9))
        < Real.sin (π / 9) * (Real.sin (π / 9) * Real.sin (2 * π / 9)) :=
      mul_lt_mul_of_pos_right hsy (mul_pos s20 s40)
    rw [key] at step1
    linarith

snip end

problem usa1996_p5
    (A B C P : EuclideanSpace ℝ (Fin 2))
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hP : P ∈ interior (convexHull ℝ {A, B, C}))
    (hPAB : ∠ P A B = π / 18)
    (hPBA : ∠ P B A = π / 9)
    (hPCA : ∠ P C A = π / 6)
    (hPAC : ∠ P A C = 2 * π / 9) :
    dist A B = dist B C := by
  -- Trigonometric Ceva, specialised to the four given angles.
  have hceva := trigonometric_ceva A B C P hABC
  rw [hPAB, hPCA, EuclideanGeometry.angle_comm A B P, hPBA,
    EuclideanGeometry.angle_comm C A P, hPAC] at hceva
  -- The six small angles sum to `π`.
  have hsum := sum_angle hABC hP
  rw [hPAB, hPCA, EuclideanGeometry.angle_comm A B P, hPBA,
    EuclideanGeometry.angle_comm C A P, hPAC] at hsum
  -- Hence `∠ P B C = 60°` and `∠ B C P = 20°`.
  obtain ⟨_, hy⟩ := solve_angles
    (EuclideanGeometry.angle_nonneg P B C) (EuclideanGeometry.angle_nonneg B C P)
    (by linarith [hsum, Real.pi_pos]) hceva
  -- Rotate the triangle so that the angle-addition lemma applies at `A` and at `C`.
  have hP1 : P ∈ interior (convexHull ℝ {B, C, A}) := by
    have h := hP
    rw [Set.insert_comm, Set.pair_comm] at h
    exact h
  have hP2 : P ∈ interior (convexHull ℝ {C, A, B}) := by
    have h := hP1
    rw [Set.insert_comm, Set.pair_comm] at h
    exact h
  -- `∠ B A C = ∠ C A B = 40° + 10° = 50°`.
  have hA : ∠ C A B = 5 * π / 18 := by
    have h := angle_eq_angle_add_angle_of_mem_interior
      (affineIndependent_rotate (affineIndependent_rotate hABC)) hP2
    rw [h, EuclideanGeometry.angle_comm C A P, hPAC, hPAB]
    ring
  -- `∠ B C A = 20° + 30° = 50°`.
  have hC : ∠ B C A = 5 * π / 18 := by
    have h := angle_eq_angle_add_angle_of_mem_interior (affineIndependent_rotate hABC) hP1
    rw [h, hy, hPCA]
    ring
  have hAC : ∠ B A C = ∠ B C A := by
    rw [EuclideanGeometry.angle_comm B A C, hA, hC]
  -- The triangle is nondegenerate, so the angle at `B` is not `π`.
  have hpi : ∠ A B C ≠ π := by
    have hnotcol : ¬Collinear ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2))) :=
      affineIndependent_iff_not_collinear_set.1 hABC
    have hsin := EuclideanGeometry.sin_pos_of_not_collinear hnotcol
    intro h
    rw [h, Real.sin_pi] at hsin
    exact (lt_irrefl (0 : ℝ)) hsin
  -- Converse of pons asinorum: equal angles at `A` and `C` give `BA = BC`.
  have hdist : dist B A = dist B C :=
    EuclideanGeometry.dist_eq_of_angle_eq_angle_of_angle_ne_pi hAC hpi
  rw [dist_comm B A] at hdist
  exact hdist

end Usa1996P5
