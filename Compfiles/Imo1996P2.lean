/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Geometry.Euclidean.Angle.Sphere
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality
public import Mathlib.Geometry.Euclidean.Triangle
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import ProblemExtraction

@[expose] public section

problem_file {
  tags := [.Geometry]
}

/-!
# International Mathematical Olympiad 1996, Problem 2

Let P be a point inside the triangle ABC such that
∠APB - ∠ACB = ∠APC - ∠ABC. Let D, E be the incenters of
triangles APB, APC respectively. Show that AP, BD, CE meet
at a point.

-/

namespace Imo1996P2

open scoped Affine EuclideanGeometry Real RealInnerProductSpace

open EuclideanGeometry

snip begin

/-! ### Oriented-angle instances (as in `Imo2001P1`) -/

local instance planeFiniteDim :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) :=
  ⟨finrank_euclideanSpace_fin⟩

noncomputable local instance someOrientation :
    Module.Oriented ℝ (EuclideanSpace ℝ (Fin 2)) (Fin 2) :=
  ⟨Module.Basis.orientation (Module.finBasisOfFinrankEq _ _ planeFiniteDim.out)⟩

/-! ### Group A: barycentric coordinates of an interior point, nondegeneracy -/

/-- Packaging the affine-basis technique of `Imo1991P5`: for a point `P`
strictly inside a nondegenerate triangle, the barycentric coordinates are
strictly positive. -/
lemma coord_pos_of_mem_interior {A B C P : EuclideanSpace ℝ (Fin 2)}
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hP : P ∈ interior (convexHull ℝ {A, B, C})) :
    ∃ basis : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)),
      (∀ i, 0 < basis.coord i P) ∧ basis 0 = A ∧ basis 1 = B ∧ basis 2 = C := by
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
  have hA : basis 0 = A := by
    rw [h_basis, DFunLike.coe, AffineBasis.instFunLike]
    simp
  have hB : basis 1 = B := by
    rw [h_basis, DFunLike.coe, AffineBasis.instFunLike]
    simp
  have hC : basis 2 = C := by
    rw [h_basis, DFunLike.coe, AffineBasis.instFunLike]
    simp
  exact ⟨basis, hP, hA, hB, hC⟩

/-- An interior point of a triangle differs from each vertex. -/
lemma p_ne_a_of_mem_interior {A B C P : EuclideanSpace ℝ (Fin 2)}
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hP : P ∈ interior (convexHull ℝ {A, B, C})) : P ≠ A := by
  obtain ⟨basis, hpos, hA, _, _⟩ := coord_pos_of_mem_interior hABC hP
  intro h
  have h0 := hpos 2
  rw [h, ← hA, AffineBasis.coord_apply_ne basis (by decide : (2 : Fin 3) ≠ 0)] at h0
  exact lt_irrefl 0 h0

lemma p_ne_b_of_mem_interior {A B C P : EuclideanSpace ℝ (Fin 2)}
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hP : P ∈ interior (convexHull ℝ {A, B, C})) : P ≠ B := by
  obtain ⟨basis, hpos, _, hB, _⟩ := coord_pos_of_mem_interior hABC hP
  intro h
  have h0 := hpos 0
  rw [h, ← hB, AffineBasis.coord_apply_ne basis (by decide : (0 : Fin 3) ≠ 1)] at h0
  exact lt_irrefl 0 h0

lemma p_ne_c_of_mem_interior {A B C P : EuclideanSpace ℝ (Fin 2)}
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hP : P ∈ interior (convexHull ℝ {A, B, C})) : P ≠ C := by
  obtain ⟨basis, hpos, _, _, hC⟩ := coord_pos_of_mem_interior hABC hP
  intro h
  have h0 := hpos 0
  rw [h, ← hC, AffineBasis.coord_apply_ne basis (by decide : (0 : Fin 3) ≠ 2)] at h0
  exact lt_irrefl 0 h0

/-- An interior point does not lie on (the line through) a side. -/
lemma not_mem_span_of_mem_interior {A B C P : EuclideanSpace ℝ (Fin 2)}
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hP : P ∈ interior (convexHull ℝ {A, B, C})) : P ∉ affineSpan ℝ {A, B} := by
  obtain ⟨basis, hpos, hA, hB, _⟩ := coord_pos_of_mem_interior hABC hP
  intro hmem
  have h0 := hpos 2
  have hf : basis.coord 2 P ∈ (affineSpan ℝ ({A, B} : Set _)).map (basis.coord 2) :=
    AffineSubspace.mem_map.mpr ⟨P, hmem, rfl⟩
  rw [AffineSubspace.map_span] at hf
  have himg : (basis.coord 2) '' ({A, B} : Set _) = ({0} : Set ℝ) := by
    have h2A : basis.coord 2 A = 0 := by
      rw [← hA]
      exact AffineBasis.coord_apply_ne basis (by decide : (2 : Fin 3) ≠ 0)
    have h2B : basis.coord 2 B = 0 := by
      rw [← hB]
      exact AffineBasis.coord_apply_ne basis (by decide : (2 : Fin 3) ≠ 1)
    ext x
    simp [h2A, h2B]
    exact eq_comm
  rw [himg, AffineSubspace.mem_affineSpan_singleton] at hf
  rw [hf] at h0
  exact lt_irrefl 0 h0

lemma not_collinear_abp_of_mem_interior {A B C P : EuclideanSpace ℝ (Fin 2)}
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hP : P ∈ interior (convexHull ℝ {A, B, C})) : ¬Collinear ℝ {A, B, P} := by
  intro hcol
  have hAB : A ≠ B := hABC.injective.ne (by decide : (0 : Fin 3) ≠ 1)
  exact not_mem_span_of_mem_interior hABC hP
    (Collinear.mem_affineSpan_of_mem_of_ne hcol (by simp) (by simp) (by simp) hAB)

/-! ### Group B: feet of perpendiculars from `P`, and the diameter spheres -/

/-- The range of the point family `![A, B, C]` as a set. -/
lemma range_mat3 (A B C : EuclideanSpace ℝ (Fin 2)) :
    Set.range ![A, B, C] = ({A, B, C} : Set _) := by
  ext x
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
    · exact ⟨2, by simp⟩

/-- Foot of the perpendicular from `P` to the line through `U` and `V`. -/
noncomputable def foot (U V P : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  ↑(orthogonalProjection (affineSpan ℝ {U, V}) P)

lemma foot_mem (U V P : EuclideanSpace ℝ (Fin 2)) :
    foot U V P ∈ affineSpan ℝ {U, V} :=
  orthogonalProjection_mem _

lemma foot_vsub_mem_orthogonal (U V P : EuclideanSpace ℝ (Fin 2)) :
    foot U V P -ᵥ P ∈ (affineSpan ℝ {U, V}).directionᗮ :=
  orthogonalProjection_vsub_mem_direction_orthogonal _ _

/-- The foot-point vector `foot -ᵥ P` is perpendicular to the line's direction. -/
lemma inner_foot (U V P : EuclideanSpace ℝ (Fin 2)) :
    ⟪foot U V P -ᵥ P, V -ᵥ U⟫ = 0 := by
  have hdir : V -ᵥ U ∈ (affineSpan ℝ {U, V}).direction := by
    rw [direction_affineSpan]
    exact vsub_mem_vectorSpan ℝ (by simp : V ∈ ({U, V} : Set _))
      (by simp : U ∈ ({U, V} : Set _))
  exact Submodule.inner_left_of_mem_orthogonal hdir (foot_vsub_mem_orthogonal U V P)

/-- A point `x` with `⟪x -ᵥ a, x -ᵥ b⟫ = 0` lies on the sphere with diameter `ab`. -/
lemma dist_midpoint_eq_half_dist_of_inner {x a b : EuclideanSpace ℝ (Fin 2)}
    (h : ⟪x -ᵥ a, x -ᵥ b⟫ = 0) : dist x (midpoint ℝ a b) = dist a b / 2 := by
  have h0 : ⟪x -ᵥ b, x -ᵥ a⟫ = 0 := by
    rw [real_inner_comm]
    exact h
  have hmv : x -ᵥ midpoint ℝ a b = (⅟2 : ℝ) • ((x -ᵥ a) + (x -ᵥ b)) := by
    rw [← neg_vsub_eq_vsub_rev _ x, midpoint_vsub,
      ← neg_vsub_eq_vsub_rev x a, ← neg_vsub_eq_vsub_rev x b]
    module
  have hsq : ‖(x -ᵥ a) + (x -ᵥ b)‖ ^ 2 = ‖a -ᵥ b‖ ^ 2 := by
    have hvw : a -ᵥ b = (x -ᵥ b) - (x -ᵥ a) := (vsub_sub_vsub_cancel_left a b x).symm
    rw [hvw, norm_add_sq_real, norm_sub_sq_real, h, h0]
    ring
  have hn : ‖(x -ᵥ a) + (x -ᵥ b)‖ = ‖a -ᵥ b‖ :=
    (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
  rw [dist_eq_norm_vsub, hmv, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (invOf_nonneg.mpr (by norm_num : (0 : ℝ) ≤ 2)),
    dist_eq_norm_vsub, hn]
  linear_combination (‖a -ᵥ b‖ / 2) * invOf_mul_self (2 : ℝ)

/-- The foot of the perpendicular from `P` lies on every diameter sphere `(W, P)`
with `W` on the line. -/
lemma foot_mem_diam_sphere_of_mem {U V W P : EuclideanSpace ℝ (Fin 2)}
    (hW : W ∈ affineSpan ℝ {U, V}) :
    foot U V P ∈ (⟨midpoint ℝ W P, dist W P / 2⟩ : Sphere (EuclideanSpace ℝ (Fin 2))) := by
  rw [mem_sphere]
  show dist (foot U V P) (midpoint ℝ W P) = dist W P / 2
  apply dist_midpoint_eq_half_dist_of_inner
  have hdir : foot U V P -ᵥ W ∈ (affineSpan ℝ {U, V}).direction := by
    rw [direction_affineSpan]
    exact vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan (foot_mem U V P) hW
  have h0 := Submodule.inner_left_of_mem_orthogonal hdir (foot_vsub_mem_orthogonal U V P)
  rw [real_inner_comm]
  exact h0

lemma foot_mem_diam_sphere (U V P : EuclideanSpace ℝ (Fin 2)) :
    foot U V P ∈ (⟨midpoint ℝ U P, dist U P / 2⟩ : Sphere (EuclideanSpace ℝ (Fin 2))) :=
  foot_mem_diam_sphere_of_mem (mem_affineSpan ℝ (by simp))

lemma left_mem_diam_sphere (U P : EuclideanSpace ℝ (Fin 2)) :
    U ∈ (⟨midpoint ℝ U P, dist U P / 2⟩ : Sphere (EuclideanSpace ℝ (Fin 2))) := by
  rw [mem_sphere]
  show dist U (midpoint ℝ U P) = dist U P / 2
  rw [dist_eq_norm_vsub, left_vsub_midpoint, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (invOf_nonneg.mpr (by norm_num : (0 : ℝ) ≤ 2)),
    dist_eq_norm_vsub]
  linear_combination (‖U -ᵥ P‖ / 2) * invOf_mul_self (2 : ℝ)

lemma right_mem_diam_sphere (U P : EuclideanSpace ℝ (Fin 2)) :
    P ∈ (⟨midpoint ℝ U P, dist U P / 2⟩ : Sphere (EuclideanSpace ℝ (Fin 2))) := by
  rw [mem_sphere]
  show dist P (midpoint ℝ U P) = dist U P / 2
  rw [dist_comm U P, dist_eq_norm_vsub, right_vsub_midpoint, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (invOf_nonneg.mpr (by norm_num : (0 : ℝ) ≤ 2)),
    dist_eq_norm_vsub]
  linear_combination (‖P -ᵥ U‖ / 2) * invOf_mul_self (2 : ℝ)

/-- The foot differs from `P` when `P` is off the line. -/
lemma foot_ne_of_not_mem {U V P : EuclideanSpace ℝ (Fin 2)}
    (h : P ∉ affineSpan ℝ {U, V}) : foot U V P ≠ P := by
  intro heq
  exact h (heq ▸ foot_mem U V P)

/-- The directions from a vertex of a nondegenerate triangle span the plane. -/
lemma span_vsub_pair_eq_top {A B C : EuclideanSpace ℝ (Fin 2)}
    (hABC : AffineIndependent ℝ ![A, B, C]) :
    Submodule.span ℝ {B -ᵥ A, C -ᵥ A} = ⊤ := by
  have htop := AffineIndependent.vectorSpan_eq_top_of_card_eq_finrank_add_one hABC (by
    rw [finrank_euclideanSpace]
    simp)
  rw [← htop, vectorSpan_eq_span_vsub_set_right ℝ (p := A) (by simp : A ∈ Set.range ![A, B, C])]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact Submodule.subset_span ⟨B, by rw [range_mat3]; simp, rfl⟩
    · exact Submodule.subset_span ⟨C, by rw [range_mat3]; simp, rfl⟩
  · apply Submodule.span_le.mpr
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [range_mat3] at hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · change _ -ᵥ _ ∈ _
      rw [vsub_self]
      exact Submodule.zero_mem _
    · exact Submodule.subset_span (Set.mem_insert _ _)
    · exact Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton_iff.mpr rfl))

lemma affineIndependent_bac {A B C : EuclideanSpace ℝ (Fin 2)}
    (h : AffineIndependent ℝ ![A, B, C]) : AffineIndependent ℝ ![B, A, C] := by
  rw [affineIndependent_iff_not_collinear_set] at h ⊢
  have hset : ({B, A, C} : Set _) = {A, B, C} := by
    ext x
    simp
    tauto
  rwa [hset]

lemma affineIndependent_cab {A B C : EuclideanSpace ℝ (Fin 2)}
    (h : AffineIndependent ℝ ![A, B, C]) : AffineIndependent ℝ ![B, C, A] := by
  rw [affineIndependent_iff_not_collinear_set] at h ⊢
  have hset : ({B, C, A} : Set _) = {A, B, C} := by
    ext x
    simp
    tauto
  rwa [hset]

lemma affineIndependent_cba {A B C : EuclideanSpace ℝ (Fin 2)}
    (h : AffineIndependent ℝ ![A, B, C]) : AffineIndependent ℝ ![C, B, A] := by
  rw [affineIndependent_iff_not_collinear_set] at h ⊢
  have hset : ({C, B, A} : Set _) = {A, B, C} := by
    ext x
    simp
    tauto
  rwa [hset]

/-- An interior point is not on line `AC` either. -/
lemma not_mem_span_ac_of_mem_interior {A B C P : EuclideanSpace ℝ (Fin 2)}
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hP : P ∈ interior (convexHull ℝ {A, B, C})) : P ∉ affineSpan ℝ {A, C} := by
  have hset : ({A, C, B} : Set _) = {A, B, C} := by
    ext x
    simp
    tauto
  rw [← hset] at hP
  exact not_mem_span_of_mem_interior (affineIndependent_cab (affineIndependent_bac hABC)) hP

/-- An interior point is not on line `BC` either. -/
lemma not_mem_span_bc_of_mem_interior {A B C P : EuclideanSpace ℝ (Fin 2)}
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hP : P ∈ interior (convexHull ℝ {A, B, C})) : P ∉ affineSpan ℝ {B, C} := by
  have hset : ({B, C, A} : Set _) = {A, B, C} := by
    ext x
    simp
    tauto
  rw [← hset] at hP
  exact not_mem_span_of_mem_interior (affineIndependent_cab hABC) hP

/-- Feet on two different lines through a shared point differ. -/
lemma foot_ne_foot {S T₁ T₂ P : EuclideanSpace ℝ (Fin 2)}
    (htop : Submodule.span ℝ {T₁ -ᵥ S, T₂ -ᵥ S} = ⊤)
    (hnotmem : P ∉ affineSpan ℝ {S, T₁}) :
    foot S T₁ P ≠ foot S T₂ P := by
  intro h
  have h1 := inner_foot S T₁ P
  have h2 := inner_foot S T₂ P
  rw [h] at h1
  have key : ∀ u ∈ Submodule.span ℝ {T₁ -ᵥ S, T₂ -ᵥ S}, ⟪u, foot S T₂ P -ᵥ P⟫ = 0 := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · rw [real_inner_comm]
          exact h1
        · rw [real_inner_comm]
          exact h2
    | zero => rw [inner_zero_left]
    | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
    | smul a x _ hx => rw [inner_smul_left, hx, mul_zero]
  have hv : ⟪foot S T₂ P -ᵥ P, foot S T₂ P -ᵥ P⟫ = 0 :=
    key _ (htop.symm ▸ Submodule.mem_top)
  rw [inner_self_eq_zero] at hv
  have hPV : foot S T₁ P = P := h.trans (vsub_eq_zero_iff_eq.mp hv)
  exact hnotmem (hPV ▸ foot_mem S T₁ P)

/-! ### Group C: sine lemmas and chord formulas -/

/-- The sine of an unoriented angle via the area form (2D). -/
lemma sin_angle_eq_abs_areaForm_div {x y : EuclideanSpace ℝ (Fin 2)}
    (hx : x ≠ 0) (hy : y ≠ 0) :
    Real.sin (InnerProductGeometry.angle x y) =
      |positiveOrientation.areaForm x y| / (‖x‖ * ‖y‖) := by
  have hcos : Real.cos (InnerProductGeometry.angle x y) = ⟪x, y⟫ / (‖x‖ * ‖y‖) :=
    InnerProductGeometry.cos_angle x y
  have hsin : 0 ≤ Real.sin (InnerProductGeometry.angle x y) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (InnerProductGeometry.angle_nonneg _ _)
      (InnerProductGeometry.angle_le_pi _ _)
  have hkey := positiveOrientation.inner_sq_add_areaForm_sq x y
  have h2 : Real.sin (InnerProductGeometry.angle x y) ^ 2 =
      (positiveOrientation.areaForm x y / (‖x‖ * ‖y‖)) ^ 2 := by
    rw [div_pow, Real.sin_sq, hcos, div_pow]
    field_simp
    linarith [hkey]
  have h3 : Real.sin (InnerProductGeometry.angle x y) =
      |positiveOrientation.areaForm x y / (‖x‖ * ‖y‖)| :=
    (sq_eq_sq₀ hsin (abs_nonneg _)).mp (by rw [sq_abs]; exact h2)
  rw [h3, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖x‖ * ‖y‖)]

/-- Angles with mutually perpendicular sides have equal sines. -/
lemma sin_angle_perp_perp {x y u v : EuclideanSpace ℝ (Fin 2)}
    (hu : u ≠ 0) (hy : y ≠ 0) (hxu : ⟪x, u⟫ = 0) (hyv : ⟪y, v⟫ = 0)
    (hx : x ≠ 0) (hv : v ≠ 0) :
    Real.sin (InnerProductGeometry.angle x y) = Real.sin (InnerProductGeometry.angle u v) := by
  rw [sin_angle_eq_abs_areaForm_div hx hy, sin_angle_eq_abs_areaForm_div hu hv]
  have hux : ⟪u, x⟫ = 0 := by
    rw [real_inner_comm]
    exact hxu
  have hωx : |positiveOrientation.areaForm u x| = ‖u‖ * ‖x‖ := by
    rw [positiveOrientation.areaForm_swap, abs_neg,
      positiveOrientation.abs_areaForm_of_orthogonal hxu]
    ring
  have hωy : |positiveOrientation.areaForm y v| = ‖y‖ * ‖v‖ :=
    positiveOrientation.abs_areaForm_of_orthogonal hyv
  have hω1 := positiveOrientation.inner_mul_areaForm_sub u x y
  rw [hux, zero_mul, zero_sub] at hω1
  have hω2 := positiveOrientation.inner_mul_areaForm_sub y u v
  rw [hyv, mul_zero, sub_zero] at hω2
  have e1 : ‖u‖ ^ 2 * |positiveOrientation.areaForm x y| = ‖u‖ * ‖x‖ * |⟪u, y⟫| := by
    have h := congrArg abs hω1
    rw [abs_neg, abs_mul, hωx, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖u‖ ^ 2)] at h
    exact h.symm
  have e2 : ‖y‖ ^ 2 * |positiveOrientation.areaForm u v| = |⟪u, y⟫| * (‖y‖ * ‖v‖) := by
    have huy : |⟪y, u⟫| = |⟪u, y⟫| := by rw [real_inner_comm]
    have h := congrArg abs hω2
    rw [abs_mul, huy, hωy, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖y‖ ^ 2)] at h
    exact h.symm
  rw [div_eq_div_iff (by positivity : ‖x‖ * ‖y‖ ≠ 0) (by positivity : ‖u‖ * ‖v‖ ≠ 0)]
  have key : (‖u‖ * ‖y‖) * (|positiveOrientation.areaForm x y| * (‖u‖ * ‖v‖)) =
      (‖u‖ * ‖y‖) * (|positiveOrientation.areaForm u v| * (‖x‖ * ‖y‖)) := by
    linear_combination (‖v‖ * ‖y‖) * e1 + (-(‖x‖ * ‖u‖)) * e2
  exact mul_left_cancel₀ (by positivity : ‖u‖ * ‖y‖ ≠ 0) key

/-- Point version: the feet-to-`P` angle at `P` has the same sine as the angle at the
shared vertex. -/
lemma sin_angle_foot (U V W P : EuclideanSpace ℝ (Fin 2))
    (hVU : V ≠ U) (hWU : W ≠ U) (hZ : foot U V P ≠ P) (hY : foot U W P ≠ P) :
    Real.sin (∠ (foot U V P) P (foot U W P)) = Real.sin (∠ V U W) := by
  rw [EuclideanGeometry.angle, EuclideanGeometry.angle]
  exact sin_angle_perp_perp (vsub_ne_zero.mpr hVU) (vsub_ne_zero.mpr hY)
    (inner_foot U V P) (inner_foot U W P) (vsub_ne_zero.mpr hZ) (vsub_ne_zero.mpr hWU)

/-- The two feet and `P` are not collinear (nondegenerate case). -/
lemma not_collinear_feet {U V W P : EuclideanSpace ℝ (Fin 2)}
    (hspan : Submodule.span ℝ {V -ᵥ U, W -ᵥ U} = ⊤)
    (hZ : foot U V P ≠ P) (hY : foot U W P ≠ P) :
    ¬Collinear ℝ {foot U V P, P, foot U W P} := by
  intro hcol
  have hmem : foot U W P -ᵥ P ∈ vectorSpan ℝ {foot U V P, P} :=
    vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan
      (Collinear.mem_affineSpan_of_mem_of_ne hcol (by simp) (by simp) (by simp) hZ)
      (mem_affineSpan ℝ (by simp : P ∈ ({foot U V P, P} : Set _)))
  rw [vectorSpan_pair] at hmem
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hmem
  have h1 := inner_foot U V P
  have h2 := inner_foot U W P
  have h2' : r * ⟪foot U V P -ᵥ P, W -ᵥ U⟫ = 0 := by
    rw [← hr, inner_smul_left] at h2
    exact h2
  rcases mul_eq_zero.mp h2' with hr0 | hZCA
  · rw [hr0, zero_smul] at hr
    exact hY (vsub_eq_zero_iff_eq.mp hr.symm)
  · have key : ∀ u ∈ Submodule.span ℝ {V -ᵥ U, W -ᵥ U}, ⟪u, foot U V P -ᵥ P⟫ = 0 := by
      intro u hu
      induction hu using Submodule.span_induction with
      | mem x hx =>
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
          rcases hx with rfl | rfl
          · rw [real_inner_comm]
            exact h1
          · rw [real_inner_comm]
            exact hZCA
      | zero => rw [inner_zero_left]
      | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
      | smul a x _ hx => rw [inner_smul_left, hx, mul_zero]
    have hv : ⟪foot U V P -ᵥ P, foot U V P -ᵥ P⟫ = 0 :=
      key _ (hspan.symm ▸ Submodule.mem_top)
    rw [inner_self_eq_zero] at hv
    exact hZ (vsub_eq_zero_iff_eq.mp hv)

/-- Chord formula: two points on a diameter sphere. -/
lemma dist_eq_diam_mul_sin_angle {a b x y : EuclideanSpace ℝ (Fin 2)}
    (hx : x ∈ (⟨midpoint ℝ a b, dist a b / 2⟩ : Sphere (EuclideanSpace ℝ (Fin 2))))
    (hb : b ∈ (⟨midpoint ℝ a b, dist a b / 2⟩ : Sphere (EuclideanSpace ℝ (Fin 2))))
    (hy : y ∈ (⟨midpoint ℝ a b, dist a b / 2⟩ : Sphere (EuclideanSpace ℝ (Fin 2))))
    (hxb : x ≠ b) (hxy : x ≠ y) (hby : b ≠ y)
    (hnc : ¬Collinear ℝ {x, b, y}) :
    dist x y = dist a b * Real.sin (∠ x b y) := by
  have h := Sphere.dist_div_sin_oangle_eq_two_mul_radius hx hb hy hxb hxy hby
  have hs : Real.sin (∠ x b y) = |Real.Angle.sin (∡ x b y)| := by
    rw [angle_eq_abs_oangle_toReal hxb hby.symm]
    nth_rw 2 [← Real.Angle.coe_toReal (∡ x b y)]
    rw [Real.Angle.sin_coe]
    exact (Real.abs_sin_eq_sin_abs_of_abs_le_pi (Real.Angle.abs_toReal_le_pi _)).symm
  have hr : (⟨midpoint ℝ a b, dist a b / 2⟩ : Sphere (EuclideanSpace ℝ (Fin 2))).radius =
      dist a b / 2 := rfl
  rw [hr, ← hs] at h
  have hsin : 0 < Real.sin (∠ x b y) := sin_pos_of_not_collinear hnc
  field_simp [hsin.ne'] at h
  linarith [h]

/-- The distance between the two feet from `P` equals `UP` times the sine of the
angle at `U`. -/
lemma dist_feet_eq_mul_sin {U V W P : EuclideanSpace ℝ (Fin 2)}
    (hVU : V ≠ U) (hWU : W ≠ U) (hZ : foot U V P ≠ P) (hY : foot U W P ≠ P)
    (hZY : foot U V P ≠ foot U W P)
    (hnc : ¬Collinear ℝ {foot U V P, P, foot U W P}) :
    dist (foot U V P) (foot U W P) = dist U P * Real.sin (∠ V U W) := by
  rw [dist_eq_diam_mul_sin_angle (foot_mem_diam_sphere U V P) (right_mem_diam_sphere U P)
    (foot_mem_diam_sphere U W P) hZ hZY hY.symm hnc, sin_angle_foot U V W P hVU hWU hZ hY]

/-! ### Group D: the angle chase (oriented angles mod `π`) -/

/-- Twice an oriented right angle is `π`. -/
lemma two_zsmul_oangle_eq_pi_of_angle_eq_pi_div_two {a b c : EuclideanSpace ℝ (Fin 2)}
    (ha : a ≠ b) (hc : c ≠ b) (h : ∠ a b c = π / 2) : (2 : ℤ) • ∡ a b c = π := by
  rw [Real.Angle.two_zsmul_eq_pi_iff]
  rw [angle_eq_abs_oangle_toReal ha hc, abs_eq (by positivity : (0 : ℝ) ≤ π / 2)] at h
  rcases h with h | h
  · exact Or.inl ((Real.Angle.coe_toReal _).symm.trans (by rw [h]))
  · exact Or.inr ((Real.Angle.coe_toReal _).symm.trans (by rw [h, neg_div]))

/-- Two right angles have equal doubled oriented angles. -/
lemma two_zsmul_oangle_eq_of_angle_eq_pi_div_two {a b c d e f : EuclideanSpace ℝ (Fin 2)}
    (h1 : ∠ a b c = π / 2) (h2 : ∠ d e f = π / 2)
    (ha : a ≠ b) (hc : c ≠ b) (hd : d ≠ e) (hf : f ≠ e) :
    (2 : ℤ) • ∡ a b c = (2 : ℤ) • ∡ d e f := by
  rw [two_zsmul_oangle_eq_pi_of_angle_eq_pi_div_two ha hc h1,
    two_zsmul_oangle_eq_pi_of_angle_eq_pi_div_two hd hf h2]

/-- The angle at the foot between a line point and `P` is right. -/
lemma angle_foot_right {U V W P : EuclideanSpace ℝ (Fin 2)}
    (hW : W ∈ affineSpan ℝ {U, V}) :
    ∠ W (foot U V P) P = π / 2 := by
  rw [EuclideanGeometry.angle, ← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two]
  have hdir : W -ᵥ foot U V P ∈ (affineSpan ℝ {U, V}).direction := by
    rw [direction_affineSpan]
    exact vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan hW (foot_mem U V P)
  have h0 := Submodule.inner_left_of_mem_orthogonal hdir (foot_vsub_mem_orthogonal U V P)
  have h0' : ⟪W -ᵥ foot U V P, foot U V P -ᵥ P⟫ = 0 := by
    rw [real_inner_comm]
    exact h0
  rw [← neg_vsub_eq_vsub_rev (foot U V P) P, inner_neg_right, h0', neg_zero]

/-- When the foot is the vertex `W` itself, the angle at `W` is right. -/
lemma angle_pi_div_two_of_foot_eq_of_mem {U V W P : EuclideanSpace ℝ (Fin 2)}
    (hW : W ∈ affineSpan ℝ {U, V}) (hV : V ∈ affineSpan ℝ {U, V}) (h : foot U V P = W) :
    ∠ V W P = π / 2 := by
  rw [EuclideanGeometry.angle, ← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two]
  have hperp : W -ᵥ P ∈ (affineSpan ℝ {U, V}).directionᗮ :=
    h ▸ foot_vsub_mem_orthogonal U V P
  have hdir : V -ᵥ W ∈ (affineSpan ℝ {U, V}).direction := by
    rw [direction_affineSpan]
    exact vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan hV hW
  have h0 := Submodule.inner_left_of_mem_orthogonal hdir hperp
  have h0' : ⟪V -ᵥ W, W -ᵥ P⟫ = 0 := by
    rw [real_inner_comm]
    exact h0
  rw [← neg_vsub_eq_vsub_rev W P, inner_neg_right, h0', neg_zero]

/-- Incoherence of the doubled oriented angle with a point on a line. -/
lemma two_zsmul_oangle_eq_of_mem_span {X B C P : EuclideanSpace ℝ (Fin 2)}
    (hXB : X ≠ B) (hCB : C ≠ B) (hPB : P ≠ B)
    (hX : X ∈ affineSpan ℝ {B, C}) :
    (2 : ℤ) • ∡ X B P = (2 : ℤ) • ∡ C B P := by
  have hv : X -ᵥ B ∈ vectorSpan ℝ {B, C} :=
    vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan hX
      (mem_affineSpan ℝ (by simp : B ∈ ({B, C} : Set _)))
  rw [vectorSpan_pair] at hv
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hv
  have hr0 : r ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hr
    exact hXB (vsub_eq_zero_iff_eq.mp hr.symm)
  have ht : X -ᵥ B = (-r) • (C -ᵥ B) := by
    rw [← hr, (neg_vsub_eq_vsub_rev C B).symm, smul_neg, ← neg_smul]
  rw [oangle, oangle, ht]
  rcases lt_or_gt_of_ne hr0 with hr0' | hr0'
  · rw [Orientation.oangle_smul_left_of_pos _ (C -ᵥ B) (P -ᵥ B) (neg_pos.mpr hr0')]
  · rw [Orientation.oangle_smul_left_of_neg _ (C -ᵥ B) (P -ᵥ B) (by linarith : (-r : ℝ) < 0),
      Orientation.oangle_neg_left _ (vsub_ne_zero.mpr hCB) (vsub_ne_zero.mpr hPB),
      smul_add, Real.Angle.two_zsmul_eq_zero_iff.mpr (Or.inr rfl), add_zero]

/-- Four points on a diameter sphere are cospherical. -/
lemma cospherical_of_mem_diam_sphere {a b x y : EuclideanSpace ℝ (Fin 2)}
    (hx : x ∈ (⟨midpoint ℝ a b, dist a b / 2⟩ : Sphere (EuclideanSpace ℝ (Fin 2))))
    (hy : y ∈ (⟨midpoint ℝ a b, dist a b / 2⟩ : Sphere (EuclideanSpace ℝ (Fin 2)))) :
    Cospherical ({x, y, a, b} : Set (EuclideanSpace ℝ (Fin 2))) := by
  refine cospherical_iff_exists_sphere.mpr ⟨⟨midpoint ℝ a b, dist a b / 2⟩, ?_⟩
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact hx
  · exact hy
  · exact left_mem_diam_sphere _ _
  · exact right_mem_diam_sphere _ _

/-- Reordering the line points does not change the foot. -/
lemma foot_pair_comm (U V P : EuclideanSpace ℝ (Fin 2)) : foot U V P = foot V U P := by
  simp only [foot, Set.pair_comm]

/-- Variant with the moving point in the third argument. -/
lemma two_zsmul_oangle_eq_of_mem_span' {X B C P : EuclideanSpace ℝ (Fin 2)}
    (hXB : X ≠ B) (hCB : C ≠ B) (hPB : P ≠ B)
    (hX : X ∈ affineSpan ℝ {B, C}) :
    (2 : ℤ) • ∡ P B X = (2 : ℤ) • ∡ P B C := by
  have h1 : ∡ P B X = -∡ X B P := oangle_rev X B P
  have h2 : ∡ P B C = -∡ C B P := oangle_rev C B P
  rw [h1, h2, smul_neg, smul_neg, two_zsmul_oangle_eq_of_mem_span hXB hCB hPB hX]

/-- Feet on the two `A`-lines differ. -/
lemma foot_ab_ne_foot_ac {A B C P : EuclideanSpace ℝ (Fin 2)}
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hP : P ∈ interior (convexHull ℝ {A, B, C})) : foot A B P ≠ foot A C P :=
  foot_ne_foot (span_vsub_pair_eq_top hABC) (not_mem_span_of_mem_interior hABC hP)

/-- Feet on the two `B`-lines differ. -/
lemma foot_ba_ne_foot_bc {A B C P : EuclideanSpace ℝ (Fin 2)}
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hP : P ∈ interior (convexHull ℝ {A, B, C})) : foot B A P ≠ foot B C P := by
  apply foot_ne_foot (span_vsub_pair_eq_top (affineIndependent_bac hABC))
  rw [Set.pair_comm B A]
  exact not_mem_span_of_mem_interior hABC hP

/-- Feet on the two `C`-lines differ. -/
lemma foot_cb_ne_foot_ca {A B C P : EuclideanSpace ℝ (Fin 2)}
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hP : P ∈ interior (convexHull ℝ {A, B, C})) : foot C B P ≠ foot C A P := by
  apply foot_ne_foot (span_vsub_pair_eq_top (affineIndependent_cba hABC))
  rw [Set.pair_comm C B]
  exact not_mem_span_bc_of_mem_interior hABC hP

/-- `X = B` and `Z = B` cannot both happen. -/
lemma z_ne_b_of_x_eq_b {A B C P : EuclideanSpace ℝ (Fin 2)}
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hP : P ∈ interior (convexHull ℝ {A, B, C}))
    (hX : foot B C P = B) : foot A B P ≠ B := by
  intro hZ
  have h1 := foot_ba_ne_foot_bc hABC hP
  have h2 : foot B A P = foot A B P := foot_pair_comm B A P
  exact h1 (h2.trans (hZ.trans hX.symm))

/-- `Y = A` and `Z = A` cannot both happen. -/
lemma z_ne_a_of_y_eq_a {A B C P : EuclideanSpace ℝ (Fin 2)}
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hP : P ∈ interior (convexHull ℝ {A, B, C}))
    (hY : foot C A P = A) : foot A B P ≠ A := by
  intro hZ
  have h1 := foot_ab_ne_foot_ac hABC hP
  have h2 : foot A C P = foot C A P := foot_pair_comm A C P
  exact h1 (hZ.trans (hY.symm.trans h2.symm))

/-- `X = C` and `Y = C` cannot both happen. -/
lemma y_ne_c_of_x_eq_c {A B C P : EuclideanSpace ℝ (Fin 2)}
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hP : P ∈ interior (convexHull ℝ {A, B, C}))
    (hX : foot B C P = C) : foot C A P ≠ C := by
  intro hY
  have h1 := foot_cb_ne_foot_ca hABC hP
  have h2 : foot C B P = foot B C P := foot_pair_comm C B P
  exact h1 ((h2.trans hX).trans hY.symm)

/-- `Z = A` and `Y = A` cannot both happen. -/
lemma y_ne_a_of_z_eq_a {A B C P : EuclideanSpace ℝ (Fin 2)}
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hP : P ∈ interior (convexHull ℝ {A, B, C}))
    (hZ : foot A B P = A) : foot C A P ≠ A := by
  intro hY
  have h1 := foot_ab_ne_foot_ac hABC hP
  have h2 : foot A C P = foot C A P := foot_pair_comm A C P
  exact h1 (hZ.trans (hY.symm.trans h2.symm))

/-- Bundle of nondegeneracy facts for the pedal configuration. -/
lemma pedal_setup {A B C P : EuclideanSpace ℝ (Fin 2)}
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hP : P ∈ interior (convexHull ℝ {A, B, C})) :
    P ≠ A ∧ P ≠ B ∧ P ≠ C ∧ A ≠ B ∧ B ≠ C ∧ C ≠ A ∧
      foot A B P ≠ P ∧ foot B C P ≠ P ∧ foot C A P ≠ P ∧
      foot A B P ≠ foot C A P ∧ foot B C P ≠ foot A B P ∧ foot C A P ≠ foot B C P := by
  refine ⟨p_ne_a_of_mem_interior hABC hP, p_ne_b_of_mem_interior hABC hP,
    p_ne_c_of_mem_interior hABC hP, hABC.injective.ne (by decide : (0 : Fin 3) ≠ 1),
    hABC.injective.ne (by decide : (1 : Fin 3) ≠ 2), hABC.injective.ne (by decide : (2 : Fin 3) ≠ 0),
    foot_ne_of_not_mem (not_mem_span_of_mem_interior hABC hP),
    foot_ne_of_not_mem (not_mem_span_bc_of_mem_interior hABC hP), ?_, ?_, ?_, ?_⟩
  · apply foot_ne_of_not_mem
    rw [Set.pair_comm C A]
    exact not_mem_span_ac_of_mem_interior hABC hP
  · intro h
    exact foot_ab_ne_foot_ac hABC hP (h.trans (foot_pair_comm A C P).symm)
  · intro h
    exact foot_ba_ne_foot_bc hABC hP ((foot_pair_comm B A P).trans h.symm)
  · intro h
    exact foot_cb_ne_foot_ca hABC hP ((foot_pair_comm C B P).trans h.symm)

/-- When the foot is the line point `U` itself, `PU` is perpendicular to the line. -/
lemma angle_pi_div_two_of_foot_eq_vertex {U V P : EuclideanSpace ℝ (Fin 2)}
    (h : foot U V P = U) : ∠ P U V = π / 2 := by
  have h2 := inner_foot U V P
  rw [h] at h2
  rw [EuclideanGeometry.angle, ← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two,
    ← neg_vsub_eq_vsub_rev U P, inner_neg_left, h2, neg_zero]

/-- Chase, term 1: the `B`-circle. -/
lemma chase_t1 {A B C P : EuclideanSpace ℝ (Fin 2)}
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hP : P ∈ interior (convexHull ℝ {A, B, C})) :
    (2 : ℤ) • ∡ (foot B C P) (foot A B P) P = (2 : ℤ) • ∡ C B P := by
  obtain ⟨hPA, hPB, hPC, hAB, hBC, hCA, hZP, hXP, hYP, hZY, hXZ, hYX⟩ := pedal_setup hABC hP
  by_cases hX : foot B C P = B
  · rw [hX]
    exact two_zsmul_oangle_eq_of_angle_eq_pi_div_two
      (angle_foot_right (mem_affineSpan ℝ (by simp : B ∈ ({A, B} : Set _))))
      (by rw [angle_comm]; exact angle_pi_div_two_of_foot_eq_vertex hX)
      (z_ne_b_of_x_eq_b hABC hP hX).symm hZP.symm hBC.symm hPB
  · have hcosp : Cospherical ({foot B C P, foot A B P, B, P} : Set _) :=
      cospherical_of_mem_diam_sphere (foot_mem_diam_sphere B C P)
        (foot_mem_diam_sphere_of_mem (mem_affineSpan ℝ (by simp : B ∈ ({A, B} : Set _))))
    have h1 := Cospherical.two_zsmul_oangle_eq hcosp hXZ.symm hZP (Ne.symm hX) hPB.symm
    exact h1.trans (two_zsmul_oangle_eq_of_mem_span hX hBC.symm hPB (foot_mem B C P))

/-- Chase, term 2: the `A`-circle at `Z`. -/
lemma chase_t2 {A B C P : EuclideanSpace ℝ (Fin 2)}
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hP : P ∈ interior (convexHull ℝ {A, B, C})) :
    (2 : ℤ) • ∡ P (foot A B P) (foot C A P) = (2 : ℤ) • ∡ P A C := by
  obtain ⟨hPA, hPB, hPC, hAB, hBC, hCA, hZP, hXP, hYP, hZY, hXZ, hYX⟩ := pedal_setup hABC hP
  by_cases hY : foot C A P = A
  · rw [hY]
    exact two_zsmul_oangle_eq_of_angle_eq_pi_div_two
      (by rw [angle_comm]; exact angle_foot_right (mem_affineSpan ℝ (by simp : A ∈ ({A, B} : Set _))))
      (angle_pi_div_two_of_foot_eq_vertex ((foot_pair_comm A C P).trans hY))
      hZP.symm (z_ne_a_of_y_eq_a hABC hP hY).symm hPA hCA
  · have hset : ({foot C A P, foot A B P, A, P} : Set _) =
        {P, foot A B P, A, foot C A P} := by
      ext x; simp; tauto
    have hcosp : Cospherical ({P, foot A B P, A, foot C A P} : Set _) :=
      hset ▸ cospherical_of_mem_diam_sphere
        (foot_mem_diam_sphere_of_mem (mem_affineSpan ℝ (by simp : A ∈ ({C, A} : Set _))))
        (foot_mem_diam_sphere A B P)
    have h1 := Cospherical.two_zsmul_oangle_eq hcosp hZP hZY hPA.symm (Ne.symm hY)
    exact h1.trans (two_zsmul_oangle_eq_of_mem_span' hY hCA hPA
      (Set.pair_comm C A ▸ foot_mem C A P))

/-- Chase, term 3: the `C`-circle. -/
lemma chase_t3 {A B C P : EuclideanSpace ℝ (Fin 2)}
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hP : P ∈ interior (convexHull ℝ {A, B, C})) :
    (2 : ℤ) • ∡ (foot B C P) (foot C A P) P = (2 : ℤ) • ∡ B C P := by
  obtain ⟨hPA, hPB, hPC, hAB, hBC, hCA, hZP, hXP, hYP, hZY, hXZ, hYX⟩ := pedal_setup hABC hP
  by_cases hX : foot B C P = C
  · rw [hX]
    exact two_zsmul_oangle_eq_of_angle_eq_pi_div_two
      (angle_foot_right (mem_affineSpan ℝ (by simp : C ∈ ({C, A} : Set _))))
      (by rw [angle_comm]; exact angle_pi_div_two_of_foot_eq_vertex ((foot_pair_comm C B P).trans hX))
      (y_ne_c_of_x_eq_c hABC hP hX).symm hYP.symm hBC hPC
  · have hcosp : Cospherical ({foot B C P, foot C A P, C, P} : Set _) :=
      cospherical_of_mem_diam_sphere
        (foot_mem_diam_sphere_of_mem (mem_affineSpan ℝ (by simp : C ∈ ({B, C} : Set _))))
        (foot_mem_diam_sphere C A P)
    have h1 := Cospherical.two_zsmul_oangle_eq hcosp hYX hYP (Ne.symm hX) hPC.symm
    exact h1.trans (two_zsmul_oangle_eq_of_mem_span hX hBC hPC
      (Set.pair_comm B C ▸ foot_mem B C P))

/-- Chase, term 4: the `A`-circle at `Y`. -/
lemma chase_t4 {A B C P : EuclideanSpace ℝ (Fin 2)}
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hP : P ∈ interior (convexHull ℝ {A, B, C})) :
    (2 : ℤ) • ∡ P (foot C A P) (foot A B P) = (2 : ℤ) • ∡ P A B := by
  obtain ⟨hPA, hPB, hPC, hAB, hBC, hCA, hZP, hXP, hYP, hZY, hXZ, hYX⟩ := pedal_setup hABC hP
  by_cases hZ : foot A B P = A
  · rw [hZ]
    exact two_zsmul_oangle_eq_of_angle_eq_pi_div_two
      (by rw [angle_comm]; exact angle_foot_right (mem_affineSpan ℝ (by simp : A ∈ ({C, A} : Set _))))
      (angle_pi_div_two_of_foot_eq_vertex hZ)
      hYP.symm (y_ne_a_of_z_eq_a hABC hP hZ).symm hPA hAB.symm
  · have hset : ({foot C A P, foot A B P, A, P} : Set _) =
        {P, foot C A P, A, foot A B P} := by
      ext x; simp; tauto
    have hcosp : Cospherical ({P, foot C A P, A, foot A B P} : Set _) :=
      hset ▸ cospherical_of_mem_diam_sphere
        (foot_mem_diam_sphere_of_mem (mem_affineSpan ℝ (by simp : A ∈ ({C, A} : Set _))))
        (foot_mem_diam_sphere A B P)
    have h1 := Cospherical.two_zsmul_oangle_eq hcosp hYP hZY.symm hPA.symm (Ne.symm hZ)
    exact h1.trans (two_zsmul_oangle_eq_of_mem_span' hZ hAB.symm hPA (foot_mem A B P))

/-- Chase, part 1: the doubled angle at `Z` in the pedal triangle. -/
lemma chase_part1 {A B C P : EuclideanSpace ℝ (Fin 2)}
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hP : P ∈ interior (convexHull ℝ {A, B, C})) :
    (2 : ℤ) • ∡ (foot B C P) (foot A B P) (foot C A P) =
      (2 : ℤ) • ∡ C B P + (2 : ℤ) • ∡ P A C := by
  obtain ⟨hPA, hPB, hPC, hAB, hBC, hCA, hZP, hXP, hYP, hZY, hXZ, hYX⟩ := pedal_setup hABC hP
  have hadd : ∡ (foot B C P) (foot A B P) P + ∡ P (foot A B P) (foot C A P) =
      ∡ (foot B C P) (foot A B P) (foot C A P) :=
    oangle_add hXZ hZP.symm hZY.symm
  rw [← hadd, smul_add, chase_t1 hABC hP, chase_t2 hABC hP]

/-- Chase, part 2: the doubled angle at `Y` in the pedal triangle. -/
lemma chase_part2 {A B C P : EuclideanSpace ℝ (Fin 2)}
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hP : P ∈ interior (convexHull ℝ {A, B, C})) :
    (2 : ℤ) • ∡ (foot B C P) (foot C A P) (foot A B P) =
      (2 : ℤ) • ∡ B C P + (2 : ℤ) • ∡ P A B := by
  obtain ⟨hPA, hPB, hPC, hAB, hBC, hCA, hZP, hXP, hYP, hZY, hXZ, hYX⟩ := pedal_setup hABC hP
  have hadd : ∡ (foot B C P) (foot C A P) P + ∡ P (foot C A P) (foot A B P) =
      ∡ (foot B C P) (foot C A P) (foot A B P) :=
    oangle_add hYX.symm hYP.symm hZY
  rw [← hadd, smul_add, chase_t3 hABC hP, chase_t4 hABC hP]

/-! ### Group R: the concurrency reduction (angle bisector theorem) -/

/-- Three points whose convex hull has nonempty interior are affinely independent. -/
theorem l2_indep_of_mem_interior {U V W Q : EuclideanSpace ℝ (Fin 2)}
    (hQ : Q ∈ interior (convexHull ℝ {U, V, W})) : AffineIndependent ℝ ![U, V, W] := by
  have hne : (interior (convexHull ℝ ({U, V, W} : Set (EuclideanSpace ℝ (Fin 2))))).Nonempty :=
    ⟨Q, hQ⟩
  rw [interior_convexHull_nonempty_iff_affineSpan_eq_top] at hne
  rw [affineIndependent_iff_not_collinear_set]
  intro hcol
  have hle := hcol.finrank_le_one
  rw [← direction_affineSpan, hne, AffineSubspace.direction_top, finrank_top,
    finrank_euclideanSpace, Fintype.card_fin] at hle
  norm_num at hle

/-- Generalized angle bisector theorem: the bisector ray from `Y` in triangle `XYZ`
(witnessed by an interior point `Q` on it) meets segment `XZ` strictly between `X` and `Z`
at a point `M` with `XM : MZ = XY : YZ`. -/
theorem l2_bisector_ratio
    (X Y Z Q : EuclideanSpace ℝ (Fin 2))
    (hXYZ : AffineIndependent ℝ ![X, Y, Z])
    (hQ : Q ∈ interior (convexHull ℝ {X, Y, Z}))
    (hbis : ∠ X Y Q = ∠ Q Y Z) :
    ∃ M : EuclideanSpace ℝ (Fin 2),
      Sbtw ℝ X M Z ∧ Collinear ℝ {Y, Q, M} ∧ dist X M * dist Y Z = dist M Z * dist X Y := by
  -- (a) Barycentric coordinates of Q with respect to the basis X, Y, Z.
  have htot' : affineSpan ℝ (Set.range ![X, Y, Z]) = ⊤ := by
    rw [AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nontrivial]
    apply AffineIndependent.vectorSpan_eq_top_of_card_eq_finrank_add_one hXYZ
    rw [finrank_euclideanSpace]
    simp only [Nat.succ_eq_add_one, zero_add, Nat.reduceAdd, Fintype.card_fin]
  set basis := AffineBasis.mk _ hXYZ htot' with h_basis
  have h_range : {X, Y, Z} = Set.range basis := by
    rw [h_basis, DFunLike.coe, AffineBasis.instFunLike]
    simp
    rw [Set.pair_comm, Set.insert_comm, Set.pair_comm]
  rw [h_range, AffineBasis.interior_convexHull] at hQ
  dsimp at hQ
  have hX0 : X = basis 0 := by
    rw [h_basis, DFunLike.coe, AffineBasis.instFunLike]
    simp
  have hY1 : Y = basis 1 := by
    rw [h_basis, DFunLike.coe, AffineBasis.instFunLike]
    simp
  have hZ2 : Z = basis 2 := by
    rw [h_basis, DFunLike.coe, AffineBasis.instFunLike]
    simp
  have hsum := AffineBasis.linear_combination_coord_eq_self basis Q
  have hsum1 := AffineBasis.sum_coord_apply_eq_one basis Q
  rw [Fin.sum_univ_three] at hsum hsum1
  set qX := basis.coord 0 Q with hqX
  set qY := basis.coord 1 Q with hqY
  set qZ := basis.coord 2 Q with hqZ
  have hqX0 : 0 < qX := by rw [hqX]; exact hQ 0
  have hqZ0 : 0 < qZ := by rw [hqZ]; exact hQ 2
  have hXZpos : 0 < qX + qZ := add_pos hqX0 hqZ0
  have hXZne : qX + qZ ≠ 0 := ne_of_gt hXZpos
  -- (b) The meeting point M on segment XZ.
  set t := qZ / (qX + qZ) with ht
  have ht0 : 0 < t := div_pos hqZ0 hXZpos
  have ht1 : t < 1 := by
    rw [ht, div_lt_one hXZpos]
    linarith
  set M := AffineMap.lineMap X Z t with hM
  have hXZ : X ≠ Z := hXYZ.injective.ne (by decide : (0 : Fin 3) ≠ 2)
  have hsbtw : Sbtw ℝ X M Z := by
    rw [hM, sbtw_lineMap_iff]
    exact ⟨hXZ, ht0, ht1⟩
  -- (c) The key vector identity: Q - Y is a positive scalar multiple of M - Y.
  have htZ : (qX + qZ) * t = qZ := by
    rw [ht, ← mul_div_assoc, mul_div_cancel_left₀ qZ hXZne]
  have htX : (qX + qZ) * (1 - t) = qX := by
    have h1 : (qX + qZ) * (1 - t) = (qX + qZ) - (qX + qZ) * t := by ring
    rw [h1, htZ]; ring
  have hYc : qY = 1 - (qX + qZ) := by linarith
  have hkey : Q -ᵥ Y = (qX + qZ) • (M -ᵥ Y) := by
    simp only [vsub_eq_sub]
    rw [← hsum, hM, AffineMap.lineMap_apply_module, ← hX0, ← hY1, ← hZ2,
      smul_sub, smul_add, smul_smul, smul_smul, htX, htZ, hYc, sub_smul, one_smul]
    abel
  -- (d) The bisector condition transfers to M.
  have hang1 : ∠ X Y M = ∠ X Y Q :=
    (EuclideanGeometry.angle_smul_right_of_pos X hXZpos hkey.symm).symm
  have hang2 : ∠ M Y Z = ∠ Q Y Z :=
    (EuclideanGeometry.angle_smul_left_of_pos Z hXZpos hkey.symm).symm
  have hangle : ∠ X Y M = ∠ M Y Z := by rw [hang1, hbis, hang2]
  -- (e) Non-collinearities needed for the law of sines.
  have hnXYZ : ¬Collinear ℝ ({X, Y, Z} : Set (EuclideanSpace ℝ (Fin 2))) :=
    affineIndependent_iff_not_collinear_set.mp hXYZ
  have hMmem : M ∈ affineSpan ℝ ({X, Z} : Set (EuclideanSpace ℝ (Fin 2))) := by
    rw [hM]
    exact AffineMap.lineMap_mem_affineSpan_pair t X Z
  have hnXMY : ¬Collinear ℝ ({X, M, Y} : Set (EuclideanSpace ℝ (Fin 2))) := by
    intro hcol
    have hYmem : Y ∈ line[ℝ, X, M] := by
      rw [hcol.affineSpan_eq_of_ne (Set.mem_insert _ _) (by simp) hsbtw.left_ne]
      exact mem_affineSpan ℝ (by simp)
    have hle : line[ℝ, X, M] ≤ affineSpan ℝ ({X, Z} : Set (EuclideanSpace ℝ (Fin 2))) := by
      rw [affineSpan_le]
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl
      · exact mem_affineSpan ℝ (Set.mem_insert _ _)
      · exact hMmem
    have hcolYXZ : Collinear ℝ ({Y, X, Z} : Set (EuclideanSpace ℝ (Fin 2))) :=
      collinear_insert_of_mem_affineSpan_pair (hle hYmem)
    rw [Set.insert_comm] at hcolYXZ
    exact hnXYZ hcolYXZ
  have hnZMY : ¬Collinear ℝ ({Z, M, Y} : Set (EuclideanSpace ℝ (Fin 2))) := by
    intro hcol
    have hYmem : Y ∈ line[ℝ, Z, M] := by
      rw [hcol.affineSpan_eq_of_ne (Set.mem_insert _ _) (by simp) hsbtw.right_ne]
      exact mem_affineSpan ℝ (by simp)
    have hle : line[ℝ, Z, M] ≤ affineSpan ℝ ({X, Z} : Set (EuclideanSpace ℝ (Fin 2))) := by
      rw [affineSpan_le]
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl
      · exact mem_affineSpan ℝ (by simp)
      · exact hMmem
    have hcolYXZ : Collinear ℝ ({Y, X, Z} : Set (EuclideanSpace ℝ (Fin 2))) :=
      collinear_insert_of_mem_affineSpan_pair (hle hYmem)
    rw [Set.insert_comm] at hcolYXZ
    exact hnXYZ hcolYXZ
  -- (f) Law of sines in triangles XMY and ZMY.
  have hs1 := EuclideanGeometry.dist_eq_dist_mul_sin_angle_div_sin_angle
    (p₁ := X) (p₂ := M) (p₃ := Y) hnXMY
  have hs2 := EuclideanGeometry.dist_eq_dist_mul_sin_angle_div_sin_angle
    (p₁ := Z) (p₂ := M) (p₃ := Y) hnZMY
  rw [EuclideanGeometry.angle_comm M Y X] at hs1
  have hsumπ : ∠ Y M X + ∠ Y M Z = π :=
    EuclideanGeometry.angle_add_angle_eq_pi_of_angle_eq_pi Y hsbtw.angle₁₂₃_eq_pi
  have hsin : Real.sin (∠ Z M Y) = Real.sin (∠ X M Y) := by
    have h1 : ∠ Z M Y = π - ∠ X M Y := by
      have e1 := EuclideanGeometry.angle_comm Y M X
      have e2 := EuclideanGeometry.angle_comm Z M Y
      linarith
    rw [h1, Real.sin_pi_sub]
  rw [hsin] at hs2
  have hsinne : Real.sin (∠ X M Y) ≠ 0 :=
    ne_of_gt (EuclideanGeometry.sin_pos_of_not_collinear hnXMY)
  have hratio : dist X M * dist Y Z = dist M Z * dist X Y := by
    rw [dist_comm M Z, dist_comm X Y, hs1, hs2, hangle]
    field_simp [hsinne]
  -- (g) Y, Q, M are collinear.
  have hQeq : Q = AffineMap.lineMap Y M (qX + qZ) := by
    rw [AffineMap.lineMap_apply, ← hkey, vsub_vadd]
  have hQmem : Q ∈ line[ℝ, Y, M] := by
    rw [hQeq]
    exact AffineMap.lineMap_mem_affineSpan_pair (qX + qZ) Y M
  have hcolYQM : Collinear ℝ ({Q, Y, M} : Set (EuclideanSpace ℝ (Fin 2))) :=
    collinear_insert_of_mem_affineSpan_pair hQmem
  rw [Set.insert_comm] at hcolYQM
  exact ⟨M, hsbtw, hcolYQM, hratio⟩

/-- Concurrency reduction: the bisector lines `BD` and `CE` both meet `AP` at the same
point `W` (the two candidates coincide by the ratio hypothesis). -/
theorem l2_reduction
    (A B C P D E : EuclideanSpace ℝ (Fin 2))
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hP : P ∈ interior (convexHull ℝ {A, B, C}))
    (hD : D ∈ interior (convexHull ℝ {A, P, B}))
    (hAD : ∠ B A D = ∠ D A P)
    (hBD : ∠ A B D = ∠ D B P)
    (hE : E ∈ interior (convexHull ℝ {A, P, C}))
    (hAE : ∠ C A E = ∠ E A P)
    (hCE : ∠ A C E = ∠ E C P)
    (hratio : dist A B * dist C P = dist A C * dist B P) :
    ∃ W : EuclideanSpace ℝ (Fin 2),
      Collinear ℝ {A, P, W} ∧ Collinear ℝ {B, D, W} ∧ Collinear ℝ {C, E, W} := by
  have hD' : D ∈ interior (convexHull ℝ ({A, B, P} : Set (EuclideanSpace ℝ (Fin 2)))) := by
    rw [Set.pair_comm B P]; exact hD
  have hE' : E ∈ interior (convexHull ℝ ({A, C, P} : Set (EuclideanSpace ℝ (Fin 2)))) := by
    rw [Set.pair_comm C P]; exact hE
  have hABP : AffineIndependent ℝ ![A, B, P] := l2_indep_of_mem_interior hD'
  have hACP : AffineIndependent ℝ ![A, C, P] := l2_indep_of_mem_interior hE'
  obtain ⟨M₁, hM₁sbtw, hM₁col, hM₁dist⟩ := l2_bisector_ratio A B P D hABP hD' hBD
  obtain ⟨M₂, hM₂sbtw, hM₂col, hM₂dist⟩ := l2_bisector_ratio A C P E hACP hE' hCE
  have hAneP : A ≠ P := hABP.injective.ne (by decide : (0 : Fin 3) ≠ 2)
  have hAneB : A ≠ B := hABP.injective.ne (by decide : (0 : Fin 3) ≠ 1)
  have hBneP : B ≠ P := hABP.injective.ne (by decide : (1 : Fin 3) ≠ 2)
  have hAneC : A ≠ C := hACP.injective.ne (by decide : (0 : Fin 3) ≠ 1)
  have hCneP : C ≠ P := hACP.injective.ne (by decide : (1 : Fin 3) ≠ 2)
  have hap : 0 < dist A P := dist_pos.mpr hAneP
  have hab : 0 < dist A B := dist_pos.mpr hAneB
  have hbp : 0 < dist B P := dist_pos.mpr hBneP
  have hac : 0 < dist A C := dist_pos.mpr hAneC
  have hcp : 0 < dist C P := dist_pos.mpr hCneP
  have hsum1 : dist A M₁ + dist M₁ P = dist A P := hM₁sbtw.wbtw.dist_add_dist
  have hsum2 : dist A M₂ + dist M₂ P = dist A P := hM₂sbtw.wbtw.dist_add_dist
  -- Parametrize both meeting points as `lineMap A P tᵢ` with `tᵢ ∈ [0, 1]`.
  obtain ⟨t₁, ⟨ht₁0, -⟩, rfl⟩ := hM₁sbtw.wbtw
  obtain ⟨t₂, ⟨ht₂0, -⟩, rfl⟩ := hM₂sbtw.wbtw
  have hd1 : dist A (AffineMap.lineMap A P t₁) = t₁ * dist A P := by
    rw [dist_comm, dist_lineMap_left, Real.norm_eq_abs, abs_of_nonneg ht₁0]
  have hd2 : dist A (AffineMap.lineMap A P t₂) = t₂ * dist A P := by
    rw [dist_comm, dist_lineMap_left, Real.norm_eq_abs, abs_of_nonneg ht₂0]
  rw [hd1] at hsum1 hM₁dist
  rw [hd2] at hsum2 hM₂dist
  -- The two parameters coincide by the ratio hypothesis.
  have hfac : (0 : ℝ) < dist A P * (dist A B + dist B P) * (dist A C + dist C P) := by
    positivity
  have htt : t₁ = t₂ := by
    have e1 : t₁ * dist A P * (dist A B + dist B P) = dist A P * dist A B := by
      have hm₁ : dist (AffineMap.lineMap A P t₁) P = dist A P - t₁ * dist A P := by linarith
      rw [hm₁] at hM₁dist
      linear_combination hM₁dist
    have e2 : t₂ * dist A P * (dist A C + dist C P) = dist A P * dist A C := by
      have hm₂ : dist (AffineMap.lineMap A P t₂) P = dist A P - t₂ * dist A P := by linarith
      rw [hm₂] at hM₂dist
      linear_combination hM₂dist
    have e3 : t₁ * (dist A P * (dist A B + dist B P) * (dist A C + dist C P)) =
        t₂ * (dist A P * (dist A B + dist B P) * (dist A C + dist C P)) := by
      linear_combination (dist A C + dist C P) * e1 - (dist A B + dist B P) * e2 +
        dist A P * hratio
    exact mul_right_cancel₀ (ne_of_gt hfac) e3
  rw [← htt] at hM₂col
  refine ⟨AffineMap.lineMap A P t₁, ?_, hM₁col, hM₂col⟩
  rw [Set.pair_comm P (AffineMap.lineMap A P t₁), Set.insert_comm A (AffineMap.lineMap A P t₁)]
  exact collinear_insert_of_mem_affineSpan_pair (AffineMap.lineMap_mem_affineSpan_pair t₁ A P)

/-! ### Group E: the real arithmetic relation `(H')` -/

/-- Angles about an interior point split (copied from `Imo1991P5`). -/
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

/-- The angle condition, rewritten as a sum relation `(H')`. -/
lemma angle_sum_rel_of_angle_sub_eq {A B C P : EuclideanSpace ℝ (Fin 2)}
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hP : P ∈ interior (convexHull ℝ {A, B, C}))
    (hangle : ∠ A P B - ∠ A C B = ∠ A P C - ∠ A B C) :
    ∠ P B C + ∠ P A C = ∠ B C P + ∠ P A B := by
  have hset : ({B, C, A} : Set _) = {A, B, C} := by
    ext x
    simp
    tauto
  have hP' : P ∈ interior (convexHull ℝ {B, C, A}) := by
    rw [hset]
    exact hP
  have hsplitB : ∠ A B C = ∠ A B P + ∠ P B C :=
    angle_eq_angle_add_angle_of_mem_interior hABC hP
  have hsplitC : ∠ B C A = ∠ B C P + ∠ P C A :=
    angle_eq_angle_add_angle_of_mem_interior (affineIndependent_cab hABC) hP'
  have hsum1 : ∠ A P B + ∠ P B A + ∠ B A P = π :=
    angle_add_angle_add_angle_eq_pi B (p_ne_a_of_mem_interior hABC hP)
  have hsum2 : ∠ A P C + ∠ P C A + ∠ C A P = π :=
    angle_add_angle_add_angle_eq_pi C (p_ne_a_of_mem_interior hABC hP)
  have hcomm1 : ∠ A C B = ∠ B C A := angle_comm A C B
  have hcomm2 : ∠ P B A = ∠ A B P := angle_comm P B A
  have hcomm3 : ∠ B A P = ∠ P A B := angle_comm B A P
  have hcomm4 : ∠ C A P = ∠ P A C := angle_comm C A P
  linarith

/-! ### Group F: the finish -/

/-- Non-collinearity from a point off a line. -/
lemma not_collinear_of_not_mem_span {U V P : EuclideanSpace ℝ (Fin 2)}
    (hUV : U ≠ V) (h : P ∉ affineSpan ℝ {U, V}) : ¬Collinear ℝ {U, V, P} := by
  intro hcol
  exact h (Collinear.mem_affineSpan_of_mem_of_ne hcol (by simp) (by simp) (by simp) hUV)

/-- An interior point lies strictly between a vertex and the opposite side. -/
lemma exists_between_vertex_line_of_mem_interior {A B C P : EuclideanSpace ℝ (Fin 2)}
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hP : P ∈ interior (convexHull ℝ {A, B, C})) :
    ∃ Q : EuclideanSpace ℝ (Fin 2), ∃ t : ℝ,
      Q ∈ affineSpan ℝ {B, C} ∧ 0 < t ∧ t < 1 ∧ P = AffineMap.lineMap A Q t := by
  obtain ⟨basis, hpos, hA, hB, hC⟩ := coord_pos_of_mem_interior hABC hP
  have hsum := AffineBasis.sum_coord_apply_eq_one basis P
  have hsum' := AffineBasis.linear_combination_coord_eq_self basis P
  rw [Fin.sum_univ_three] at hsum hsum'
  set α := basis.coord 0 P with hα
  set β := basis.coord 1 P with hβ
  set γ := basis.coord 2 P with hγ
  have hα0 : 0 < α := hpos 0
  have hβ0 : 0 < β := hpos 1
  have hγ0 : 0 < γ := hpos 2
  have hβγ : 0 < β + γ := add_pos hβ0 hγ0
  have ht1 : β + γ < 1 := by linarith
  have htZ : (β + γ) * (γ / (β + γ)) = γ := by
    rw [← mul_div_assoc, mul_div_cancel_left₀ γ hβγ.ne']
  have htX : (β + γ) * (1 - γ / (β + γ)) = β := by
    have h1 : (β + γ) * (1 - γ / (β + γ)) = (β + γ) - (β + γ) * (γ / (β + γ)) := by ring
    rw [h1, htZ]; ring
  have hαc : α = 1 - (β + γ) := by linarith
  refine ⟨AffineMap.lineMap B C (γ / (β + γ)), β + γ,
    AffineMap.lineMap_mem_affineSpan_pair _ _ _, hβγ, ht1, ?_⟩
  have hkey : P -ᵥ A = (β + γ) • ((AffineMap.lineMap B C (γ / (β + γ))) -ᵥ A) := by
    simp only [vsub_eq_sub]
    rw [← hsum', AffineMap.lineMap_apply_module, hA, hB, hC,
      smul_sub, smul_add, smul_smul, smul_smul, htX, htZ, hαc, sub_smul, one_smul]
    abel
  rw [AffineMap.lineMap_apply, ← hkey, vsub_vadd]

/-- An interior point is strictly on the vertex's side of the opposite line. -/
lemma sSameSide_of_mem_interior {A B C P : EuclideanSpace ℝ (Fin 2)}
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hP : P ∈ interior (convexHull ℝ {A, B, C})) :
    (affineSpan ℝ {B, C}).SSameSide P A := by
  obtain ⟨Q, t, hQ, ht0, ht1, hPt⟩ := exists_between_vertex_line_of_mem_interior hABC hP
  have hPnot : P ∉ affineSpan ℝ {B, C} := not_mem_span_bc_of_mem_interior hABC hP
  have hAnot : A ∉ affineSpan ℝ {B, C} := by
    intro hAm
    exact (affineIndependent_iff_not_collinear_set.mp hABC)
      (collinear_insert_of_mem_affineSpan_pair hAm)
  have hvec : P -ᵥ Q = (1 - t) • (A -ᵥ Q) := by
    rw [hPt, AffineMap.lineMap_apply, vadd_vsub_assoc, (neg_vsub_eq_vsub_rev A Q).symm]
    module
  have hray : SameRay ℝ ((1 - t) • (A -ᵥ Q)) (A -ᵥ Q) := by
    by_cases hA' : A = Q
    · exact absurd (hA' ▸ hQ) hAnot
    · exact Or.inr (Or.inr ⟨1, 1 - t, one_pos, sub_pos.mpr ht1, by module⟩)
  exact ⟨⟨Q, hQ, Q, hQ, hvec ▸ hray⟩, hPnot, hAnot⟩

/-- Side fact at line `AC`. -/
lemma sSameSide_ac_of_mem_interior {A B C P : EuclideanSpace ℝ (Fin 2)}
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hP : P ∈ interior (convexHull ℝ {A, B, C})) :
    (affineSpan ℝ {A, C}).SSameSide P B := by
  have hset : ({B, A, C} : Set _) = {A, B, C} := by
    ext x
    simp
    tauto
  exact sSameSide_of_mem_interior (affineIndependent_bac hABC) (hset.symm ▸ hP)

/-- Side fact at line `AB`. -/
lemma sSameSide_ab_of_mem_interior {A B C P : EuclideanSpace ℝ (Fin 2)}
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hP : P ∈ interior (convexHull ℝ {A, B, C})) :
    (affineSpan ℝ {A, B}).SSameSide P C := by
  have hset : ({C, A, B} : Set _) = {A, B, C} := by
    ext x
    simp
    tauto
  exact sSameSide_of_mem_interior (affineIndependent_cab (affineIndependent_cab hABC)) (hset.symm ▸ hP)

/-- The pedal feet of an interior point are not collinear (Simson-line exclusion). -/
lemma feet_not_collinear {A B C P : EuclideanSpace ℝ (Fin 2)}
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hP : P ∈ interior (convexHull ℝ {A, B, C})) :
    ¬Collinear ℝ ({foot B C P, foot C A P, foot A B P} : Set _) := by
  obtain ⟨hPA, hPB, hPC, hAB, hBC, hCA, hZP, hXP, hYP, hZY, hXZ, hYX⟩ := pedal_setup hABC hP
  intro hcol
  have hcol' : Collinear ℝ ({foot B C P, foot A B P, foot C A P} : Set _) :=
    Collinear.subset (by intro x hx; simp at hx ⊢; tauto) hcol
  have h0orπ : ∡ (foot B C P) (foot A B P) (foot C A P) = 0 ∨
      ∡ (foot B C P) (foot A B P) (foot C A P) = π :=
    oangle_eq_zero_or_eq_pi_iff_collinear.mpr hcol'
  have h2z' : (2 : ℤ) • ∡ C B P + (2 : ℤ) • ∡ P A C = 0 := by
    have h2z : (2 : ℤ) • ∡ (foot B C P) (foot A B P) (foot C A P) = 0 := by
      rcases h0orπ with h0 | h0
      · rw [h0, smul_zero]
      · rw [h0, Real.Angle.two_zsmul_eq_zero_iff.mpr (Or.inr rfl)]
    rw [chase_part1 hABC hP] at h2z
    exact h2z
  have h2eq : (2 : ℤ) • ∡ C B P = (2 : ℤ) • ∡ C A P := by
    have h1 : ∡ C A P = -∡ P A C := oangle_rev P A C
    rw [h1, smul_neg, ← add_eq_zero_iff_eq_neg]
    exact h2z'
  have hnCBP : ¬Collinear ℝ ({C, B, P} : Set _) := by
    intro hcol''
    have hsub : ({B, C, P} : Set _) ⊆ {C, B, P} := by
      intro x hx
      simp at hx ⊢
      tauto
    exact (not_collinear_of_not_mem_span hBC (not_mem_span_bc_of_mem_interior hABC hP))
      (Collinear.subset hsub hcol'')
  have hcosp : Cospherical ({C, B, A, P} : Set _) :=
    cospherical_of_two_zsmul_oangle_eq_of_not_collinear h2eq hnCBP
  obtain ⟨s, hs⟩ := cospherical_iff_exists_sphere.mp hcosp
  let t : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2)) := ⟨![A, B, C], hABC⟩
  have htot : affineSpan ℝ (Set.range ![A, B, C]) = ⊤ := by
    rw [AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nontrivial]
    apply AffineIndependent.vectorSpan_eq_top_of_card_eq_finrank_add_one hABC
    rw [finrank_euclideanSpace]
    simp
  have hs_eq : s = t.circumsphere := by
    apply t.circumsphere_unique_dist_eq.2 s
    constructor
    · rw [htot]
      exact AffineSubspace.mem_top ℝ _ _
    · rw [range_mat3]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact hs (by simp)
      · exact hs (by simp)
      · exact hs (by simp)
  have hPsphere : P ∈ t.circumsphere := by
    rw [← hs_eq]
    exact hs (by simp)
  have hPrad : dist P t.circumcenter = t.circumradius := by
    have h1 := hPsphere
    rw [mem_sphere] at h1
    simpa using h1
  have hdisk : dist P t.circumcenter < t.circumradius := by
    have hvA : A ∈ Metric.closedBall t.circumcenter t.circumradius := by
      have h1 : dist t.circumcenter A = t.circumradius :=
        Affine.Simplex.dist_circumcenter_eq_circumradius' t 0
      rw [Metric.mem_closedBall, dist_comm]
      exact le_of_eq h1
    have hvB : B ∈ Metric.closedBall t.circumcenter t.circumradius := by
      have h1 : dist t.circumcenter B = t.circumradius :=
        Affine.Simplex.dist_circumcenter_eq_circumradius' t 1
      rw [Metric.mem_closedBall, dist_comm]
      exact le_of_eq h1
    have hvC : C ∈ Metric.closedBall t.circumcenter t.circumradius := by
      have h1 : dist t.circumcenter C = t.circumradius :=
        Affine.Simplex.dist_circumcenter_eq_circumradius' t 2
      rw [Metric.mem_closedBall, dist_comm]
      exact le_of_eq h1
    have hsub : convexHull ℝ {A, B, C} ⊆ Metric.closedBall t.circumcenter t.circumradius := by
      apply convexHull_min ?_ (convex_closedBall _ _)
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact hvA
      · exact hvB
      · exact hvC
    have hsub2 := interior_mono hsub hP
    rw [interior_closedBall _ t.circumradius_pos.ne'] at hsub2
    exact hsub2
  linarith

/-- `π` as a `Real.Angle` has `toReal = π`. -/
lemma toReal_pi' : (π : Real.Angle).toReal = Real.pi :=
  Real.Angle.toReal_coe_eq_self_iff.mpr ⟨by linarith [Real.pi_pos], le_refl Real.pi⟩

/-- An oriented angle of sign `1` is the coercion of the unoriented angle. -/
lemma oangle_eq_coe_angle_of_sign_eq_one {a b c : EuclideanSpace ℝ (Fin 2)}
    (h : (∡ a b c).sign = 1) : ∡ a b c = ↑(∠ a b c) := by
  rw [angle_eq_abs_oangle_toReal (left_ne_of_oangle_sign_eq_one h)
    (right_ne_of_oangle_sign_eq_one h)]
  exact (Real.Angle.coe_abs_toReal_of_sign_nonneg (by rw [h]; decide)).symm

/-- An oriented angle of sign `-1` is the negated coercion of the unoriented angle. -/
lemma oangle_eq_neg_coe_angle_of_sign_eq_neg_one {a b c : EuclideanSpace ℝ (Fin 2)}
    (h : (∡ a b c).sign = -1) : ∡ a b c = -↑(∠ a b c) := by
  rw [angle_eq_abs_oangle_toReal (left_ne_of_oangle_sign_eq_neg_one h)
    (right_ne_of_oangle_sign_eq_neg_one h)]
  exact (Real.Angle.neg_coe_abs_toReal_of_sign_nonpos (by rw [h]; decide)).symm

/-- Two oriented angles summing to `π` with nonzero sign have the same sign. -/
lemma sign_eq_of_add_eq_pi {θ ψ : Real.Angle} (h : θ + ψ = π)
    (hθ : θ.sign ≠ 0) (hψ : ψ.sign ≠ 0) : θ.sign = ψ.sign := by
  obtain (h1 | h1 | h1) := θ.sign.trichotomy
  · obtain (h2 | h2 | h2) := ψ.sign.trichotomy
    · exact h1.trans h2.symm
    · exact absurd h2 hψ
    · exfalso
      have ht := Real.Angle.toReal_add_of_sign_pos_sign_neg h2 h1
      rw [add_comm ψ θ, h, toReal_pi'] at ht
      have hθt : θ.toReal < 0 := Real.Angle.toReal_neg_iff_sign_neg.mpr h1
      obtain ⟨hψt0, hψt2⟩ := Set.mem_Ioo.mp (Real.Angle.toReal_mem_Ioo_iff_sign_pos.mpr h2)
      linarith
  · exact absurd h1 hθ
  · obtain (h2 | h2 | h2) := ψ.sign.trichotomy
    · exfalso
      have ht := Real.Angle.toReal_add_of_sign_pos_sign_neg h1 h2
      rw [h, toReal_pi'] at ht
      obtain ⟨hθt0, hθt2⟩ := Set.mem_Ioo.mp (Real.Angle.toReal_mem_Ioo_iff_sign_pos.mpr h1)
      have hψt : ψ.toReal < 0 := Real.Angle.toReal_neg_iff_sign_neg.mpr h2
      linarith
    · exact absurd h2 hψ
    · exact h1.trans h2.symm

/-- Sign of `∡ C B P`. -/
lemma oangle_cbp_sign {A B C P : EuclideanSpace ℝ (Fin 2)}
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hP : P ∈ interior (convexHull ℝ {A, B, C})) :
    (∡ C B P).sign = -(∡ A B C).sign := by
  have hside := AffineSubspace.sSameSide_comm.mp (sSameSide_of_mem_interior hABC hP)
  have h1 : (∡ C P B).sign = (∡ C A B).sign :=
    hside.oangle_sign_eq (mem_affineSpan ℝ (by simp : C ∈ ({B, C} : Set _)))
      (mem_affineSpan ℝ (by simp : B ∈ ({B, C} : Set _)))
  have h2 : -(∡ C B P).sign = (∡ C P B).sign := oangle_swap₂₃_sign C B P
  have h3 : (∡ A B C).sign = (∡ C A B).sign := oangle_rotate_sign C A B
  rw [h1, ← h3] at h2
  rw [← h2, neg_neg]

/-- Sign of `∡ P A C`. -/
lemma oangle_pac_sign {A B C P : EuclideanSpace ℝ (Fin 2)}
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hP : P ∈ interior (convexHull ℝ {A, B, C})) :
    (∡ P A C).sign = -(∡ A B C).sign := by
  have hside := AffineSubspace.sSameSide_comm.mp (sSameSide_ac_of_mem_interior hABC hP)
  have h1 : (∡ A P C).sign = (∡ A B C).sign :=
    hside.oangle_sign_eq (mem_affineSpan ℝ (by simp : A ∈ ({A, C} : Set _)))
      (mem_affineSpan ℝ (by simp : C ∈ ({A, C} : Set _)))
  have h2 : -(∡ A P C).sign = (∡ P A C).sign := oangle_swap₁₂_sign A P C
  rw [h1] at h2
  exact h2.symm

/-- Sign of `∡ B C P`. -/
lemma oangle_bcp_sign {A B C P : EuclideanSpace ℝ (Fin 2)}
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hP : P ∈ interior (convexHull ℝ {A, B, C})) :
    (∡ B C P).sign = (∡ A B C).sign := by
  have hside := AffineSubspace.sSameSide_comm.mp (sSameSide_of_mem_interior hABC hP)
  have h1 : (∡ B P C).sign = (∡ B A C).sign :=
    hside.oangle_sign_eq (mem_affineSpan ℝ (by simp : B ∈ ({B, C} : Set _)))
      (mem_affineSpan ℝ (by simp : C ∈ ({B, C} : Set _)))
  have h2 : -(∡ B C P).sign = (∡ B P C).sign := oangle_swap₂₃_sign B C P
  have h3 : -(∡ A B C).sign = (∡ B A C).sign := oangle_swap₁₂_sign A B C
  rw [h1, ← h3] at h2
  exact neg_inj.mp h2

/-- Sign of `∡ P A B`. -/
lemma oangle_pab_sign {A B C P : EuclideanSpace ℝ (Fin 2)}
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hP : P ∈ interior (convexHull ℝ {A, B, C})) :
    (∡ P A B).sign = (∡ A B C).sign := by
  have hside := AffineSubspace.sSameSide_comm.mp (sSameSide_ab_of_mem_interior hABC hP)
  have h1 : (∡ A P B).sign = (∡ A C B).sign :=
    hside.oangle_sign_eq (mem_affineSpan ℝ (by simp : A ∈ ({A, B} : Set _)))
      (mem_affineSpan ℝ (by simp : B ∈ ({A, B} : Set _)))
  have h2 : -(∡ A P B).sign = (∡ P A B).sign := oangle_swap₁₂_sign A P B
  have h3 : (∡ C B A).sign = (∡ A C B).sign := oangle_rotate_sign A C B
  have h4 : -(∡ A B C).sign = (∡ C B A).sign := oangle_swap₁₃_sign A B C
  rw [h1, ← h3, ← h4] at h2
  rw [← h2, neg_neg]

/-- The four oriented angles sum to zero (sign table + `(H')`). -/
lemma four_oangle_sum_eq_zero {A B C P : EuclideanSpace ℝ (Fin 2)}
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hP : P ∈ interior (convexHull ℝ {A, B, C}))
    (hangle : ∠ A P B - ∠ A C B = ∠ A P C - ∠ A B C) :
    ∡ C B P + ∡ P A C + ∡ B C P + ∡ P A B = 0 := by
  have hσ : (∡ A B C).sign ≠ 0 := by
    intro h0
    rw [oangle_sign_eq_zero_iff_collinear] at h0
    exact (affineIndependent_iff_not_collinear_set.mp hABC) h0
  have hH := angle_sum_rel_of_angle_sub_eq hABC hP hangle
  have hσ1 : (∡ A B C).sign = 1 ∨ (∡ A B C).sign = -1 := by
    obtain (h | h | h) := (Real.Angle.sign (∡ A B C)).trichotomy
    · exact Or.inr h
    · exact absurd h hσ
    · exact Or.inl h
  rcases hσ1 with hσ1 | hσ1
  · have e1 : ∡ C B P = -↑(∠ C B P) :=
      oangle_eq_neg_coe_angle_of_sign_eq_neg_one (by simp [oangle_cbp_sign hABC hP, hσ1])
    have e2 : ∡ P A C = -↑(∠ P A C) :=
      oangle_eq_neg_coe_angle_of_sign_eq_neg_one (by simp [oangle_pac_sign hABC hP, hσ1])
    have e3 : ∡ B C P = ↑(∠ B C P) :=
      oangle_eq_coe_angle_of_sign_eq_one (by simp [oangle_bcp_sign hABC hP, hσ1])
    have e4 : ∡ P A B = ↑(∠ P A B) :=
      oangle_eq_coe_angle_of_sign_eq_one (by simp [oangle_pab_sign hABC hP, hσ1])
    rw [e1, e2, e3, e4, angle_comm C B P,
      show -(↑(∠ P B C) : Real.Angle) + -(↑(∠ P A C) : Real.Angle) + ↑(∠ B C P) + ↑(∠ P A B) =
        (↑(∠ B C P) + ↑(∠ P A B)) - (↑(∠ P B C) + ↑(∠ P A C)) from by abel,
      ← Real.Angle.coe_add, ← Real.Angle.coe_add, sub_eq_zero]
    exact congrArg (fun x : ℝ => (x : Real.Angle)) hH.symm
  · have e1 : ∡ C B P = ↑(∠ C B P) :=
      oangle_eq_coe_angle_of_sign_eq_one (by simp [oangle_cbp_sign hABC hP, hσ1])
    have e2 : ∡ P A C = ↑(∠ P A C) :=
      oangle_eq_coe_angle_of_sign_eq_one (by simp [oangle_pac_sign hABC hP, hσ1])
    have e3 : ∡ B C P = -↑(∠ B C P) :=
      oangle_eq_neg_coe_angle_of_sign_eq_neg_one (by simp [oangle_bcp_sign hABC hP, hσ1])
    have e4 : ∡ P A B = -↑(∠ P A B) :=
      oangle_eq_neg_coe_angle_of_sign_eq_neg_one (by simp [oangle_pab_sign hABC hP, hσ1])
    rw [e1, e2, e3, e4, angle_comm C B P,
      show (↑(∠ P B C) : Real.Angle) + ↑(∠ P A C) + -(↑(∠ B C P) : Real.Angle) + -(↑(∠ P A B) : Real.Angle) =
        (↑(∠ P B C) + ↑(∠ P A C)) - (↑(∠ B C P) + ↑(∠ P A B)) from by abel,
      ← Real.Angle.coe_add, ← Real.Angle.coe_add, sub_eq_zero]
    exact congrArg (fun x : ℝ => (x : Real.Angle)) hH

/-- `foot B A P ≠ P` for interior `P`. -/
lemma foot_ba_ne_p {A B C P : EuclideanSpace ℝ (Fin 2)}
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hP : P ∈ interior (convexHull ℝ {A, B, C})) : foot B A P ≠ P := by
  rw [foot_pair_comm]
  exact foot_ne_of_not_mem (not_mem_span_of_mem_interior hABC hP)

/-- `foot C B P ≠ P` for interior `P`. -/
lemma foot_cb_ne_p {A B C P : EuclideanSpace ℝ (Fin 2)}
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hP : P ∈ interior (convexHull ℝ {A, B, C})) : foot C B P ≠ P := by
  rw [foot_pair_comm]
  exact foot_ne_of_not_mem (not_mem_span_bc_of_mem_interior hABC hP)

/-- The doubled angle relation in the pedal triangle. -/
lemma doubled_oangle_sum_eq_zero {A B C P : EuclideanSpace ℝ (Fin 2)}
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hP : P ∈ interior (convexHull ℝ {A, B, C}))
    (hangle : ∠ A P B - ∠ A C B = ∠ A P C - ∠ A B C) :
    (2 : ℤ) • (∡ (foot B C P) (foot A B P) (foot C A P) +
      ∡ (foot B C P) (foot C A P) (foot A B P)) = 0 := by
  have e := four_oangle_sum_eq_zero hABC hP hangle
  rw [smul_add, chase_part1 hABC hP, chase_part2 hABC hP, ← smul_add, ← smul_add, ← smul_add,
    add_assoc, ← add_assoc (∡ P A C) (∡ B C P) (∡ P A B),
    ← add_assoc (∡ C B P) (∡ P A C + ∡ B C P) (∡ P A B),
    ← add_assoc (∡ C B P) (∡ P A C) (∡ B C P), e, smul_zero]

/-- The metric core of the problem: the angle condition on `P` forces
`AB · CP = AC · BP`.

Proof plan (following https://prase.cz/kalva/imo/isoln/isoln962.html):
let X, Y, Z be the feet of the perpendiculars from `P` to `BC`, `CA`, `AB`.
The quadrilaterals `AYPZ`, `BZPX`, `CXPY` are cyclic (right angles at the
feet), with circumdiameters `AP`, `BP`, `CP` respectively, so the extended
law of sines (`EuclideanGeometry.Sphere.dist_div_sin_oangle_eq_two_mul_radius`,
cf. its use in `Imo2001P1`) gives
`YZ = AP * sin A`, `ZX = BP * sin B`, `XY = CP * sin C`.
A cyclic-quadrilateral angle chase gives
`∠XZY = ∠APB - ∠ACB` and `∠XYZ = ∠APC - ∠ABC`
(kalva: `∠XZY = ∠XZP + ∠YZP = ∠XBP + ∠YAP = (π/2 - ∠XPB) + (π/2 - ∠YPA)
= ∠APB - ∠C`); the hypothesis then yields `∠XZY = ∠XYZ`, hence
`XY = XZ`, i.e. `CP * sin C = BP * sin B`. The law of sines in `ABC`
(`EuclideanGeometry.law_sin`, cf. `Imo1991P5.trigonometric_ceva`) rewrites
this as `CP / BP = AC / AB`.

Useful existing ingredients for the angle manipulations:
`Imo1991P5.angle_eq_angle_add_angle_of_mem_interior` (splitting angles about
an interior point), `EuclideanGeometry.angle_add_angle_add_angle_eq_pi`,
`Mathlib/Geometry/Euclidean/Angle/Sphere.lean` (oriented angles on circles). -/
lemma dist_mul_eq_dist_mul_of_angle_sub_eq_angle_sub
    (A B C P : EuclideanSpace ℝ (Fin 2))
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hP : P ∈ interior (convexHull ℝ {A, B, C}))
    (hangle : ∠ A P B - ∠ A C B = ∠ A P C - ∠ A B C) :
    dist A B * dist C P = dist A C * dist B P := by
  obtain ⟨hPA, hPB, hPC, hAB, hBC, hCA, hZP, hXP, hYP, hZY, hXZ, hYX⟩ := pedal_setup hABC hP
  have key := doubled_oangle_sum_eq_zero hABC hP hangle
  -- Chord formulas at the three vertices.
  have chordXZ : dist (foot B C P) (foot A B P) = dist B P * Real.sin (∠ A B C) := by
    rw [foot_pair_comm A B P, dist_comm]
    exact dist_feet_eq_mul_sin hAB hBC.symm (foot_ba_ne_p hABC hP) hXP
      (foot_ba_ne_foot_bc hABC hP)
      (not_collinear_feet (span_vsub_pair_eq_top (affineIndependent_bac hABC))
        (foot_ba_ne_p hABC hP) hXP)
  have chordXY : dist (foot B C P) (foot C A P) = dist C P * Real.sin (∠ A C B) := by
    rw [dist_comm, ← foot_pair_comm C B P]
    exact dist_feet_eq_mul_sin hCA.symm hBC hYP (foot_cb_ne_p hABC hP)
      (foot_cb_ne_foot_ca hABC hP).symm
      (not_collinear_feet (span_vsub_pair_eq_top (affineIndependent_cab (affineIndependent_cab hABC))) hYP
        (foot_cb_ne_p hABC hP))
  -- Split the two cases for the sum of oriented angles.
  have hang : ∠ (foot B C P) (foot A B P) (foot C A P) =
      ∠ (foot B C P) (foot C A P) (foot A B P) := by
    rcases Real.Angle.two_zsmul_eq_zero_iff.mp key with hcase | hcase
    · have h0 : ∡ (foot B C P) (foot A B P) (foot C A P) =
        -∡ (foot B C P) (foot C A P) (foot A B P) := add_eq_zero_iff_eq_neg.mp hcase
      rw [angle_eq_abs_oangle_toReal hXZ hZY.symm, angle_eq_abs_oangle_toReal hYX.symm hZY,
        h0, Real.Angle.abs_toReal_neg]
    · exfalso
      have hsum : |(∡ (foot B C P) (foot A B P) (foot C A P)).toReal| +
          |(∡ (foot B C P) (foot C A P) (foot A B P)).toReal| = π := by
        by_cases h0 : (∡ (foot B C P) (foot A B P) (foot C A P)).sign = 0
        · rw [Real.Angle.sign_eq_zero_iff] at h0
          rcases h0 with h0 | h0
          · have hθ2 : ∡ (foot B C P) (foot C A P) (foot A B P) = π := by
              rw [h0, zero_add] at hcase
              exact hcase
            rw [h0, hθ2, Real.Angle.toReal_zero, abs_zero, toReal_pi',
              abs_of_nonneg Real.pi_pos.le, zero_add]
          · have hθ2 : ∡ (foot B C P) (foot C A P) (foot A B P) = 0 := by
              rw [h0] at hcase
              exact add_left_cancel_iff.mp (by rw [add_zero]; exact hcase)
            rw [h0, hθ2, toReal_pi', Real.Angle.toReal_zero, abs_zero,
              abs_of_nonneg Real.pi_pos.le, add_zero]
        · have h0' : (∡ (foot B C P) (foot C A P) (foot A B P)).sign ≠ 0 := by
            intro h0'
            rw [Real.Angle.sign_eq_zero_iff] at h0'
            rcases h0' with h0' | h0'
            · rw [h0', add_zero] at hcase
              exact h0 (by rw [Real.Angle.sign_eq_zero_iff]; exact Or.inr hcase)
            · rw [h0'] at hcase
              exact h0 (by rw [Real.Angle.sign_eq_zero_iff]; exact Or.inl (by
                exact add_left_cancel_iff.mp (by rw [add_zero, add_comm]; exact hcase)))
          have hse := sign_eq_of_add_eq_pi hcase h0 h0'
          exact Real.Angle.abs_toReal_add_abs_toReal_eq_pi_of_two_zsmul_add_eq_zero_of_sign_eq
            key hse h0
      have hsumtri : ∠ (foot B C P) (foot A B P) (foot C A P) +
          ∠ (foot A B P) (foot C A P) (foot B C P) + ∠ (foot C A P) (foot B C P) (foot A B P) = π :=
        angle_add_angle_add_angle_eq_pi (foot C A P) hXZ.symm
      have hzero : ∠ (foot A B P) (foot B C P) (foot C A P) = 0 := by
        have hA1 : ∠ (foot B C P) (foot A B P) (foot C A P) =
            |(∡ (foot B C P) (foot A B P) (foot C A P)).toReal| :=
          angle_eq_abs_oangle_toReal hXZ hZY.symm
        have hA2 : ∠ (foot B C P) (foot C A P) (foot A B P) =
            |(∡ (foot B C P) (foot C A P) (foot A B P)).toReal| :=
          angle_eq_abs_oangle_toReal hYX.symm hZY
        have hA3 : ∠ (foot A B P) (foot C A P) (foot B C P) =
            ∠ (foot B C P) (foot C A P) (foot A B P) := angle_comm _ _ _
        have hA4 : ∠ (foot C A P) (foot B C P) (foot A B P) =
            ∠ (foot A B P) (foot B C P) (foot C A P) := angle_comm _ _ _
        linarith [hsum, hsumtri, hA1, hA2, hA3, hA4]
      have hcol : Collinear ℝ ({foot A B P, foot B C P, foot C A P} : Set _) := by
        rcases (angle_eq_zero_iff_ne_and_wbtw.mp hzero) with ⟨_, hw⟩ | ⟨_, hw⟩
        · exact Collinear.subset (by intro x hx; simp at hx ⊢; tauto) hw.collinear
        · exact Collinear.subset (by intro x hx; simp at hx ⊢; tauto) hw.collinear
      exact feet_not_collinear hABC hP
        (Collinear.subset (by intro x hx; simp at hx ⊢; tauto) hcol)
  -- The pedal triangle is isosceles.
  have hiso : dist (foot B C P) (foot C A P) = dist (foot B C P) (foot A B P) := by
    have hpi : ∠ (foot A B P) (foot B C P) (foot C A P) ≠ π := by
      intro hpi'
      have hsbtw : Sbtw ℝ (foot A B P) (foot B C P) (foot C A P) := angle_eq_pi_iff_sbtw.mp hpi'
      have hcol : Collinear ℝ ({foot A B P, foot B C P, foot C A P} : Set _) := hsbtw.wbtw.collinear
      exact feet_not_collinear hABC hP
        (Collinear.subset (by intro x hx; simp at hx ⊢; tauto) hcol)
    exact (dist_eq_of_angle_eq_angle_of_angle_ne_pi hang hpi).symm
  -- Final algebra.
  have e1 : dist C P * Real.sin (∠ A C B) = dist B P * Real.sin (∠ A B C) :=
    chordXY.symm.trans (hiso.trans chordXZ)
  have e2 : Real.sin (∠ B C A) * dist C A = Real.sin (∠ A B C) * dist A B := law_sin B C A
  rw [angle_comm B C A, dist_comm C A] at e2
  have hncACB : ¬Collinear ℝ ({A, C, B} : Set _) := by
    intro hcol
    exact (affineIndependent_iff_not_collinear_set.mp hABC)
      (Collinear.subset (by intro x hx; simp at hx ⊢; tauto) hcol)
  have hsinC : 0 < Real.sin (∠ A C B) := sin_pos_of_not_collinear hncACB
  have key2 : Real.sin (∠ A C B) * (dist A B * dist C P) =
      Real.sin (∠ A C B) * (dist A C * dist B P) := by
    linear_combination (dist A B) * e1 - (dist B P) * e2
  exact mul_left_cancel₀ hsinC.ne' key2

/-- Reduction of the concurrency statement to the metric core.

Proof plan: from `hD`, `hAD`, `hBD` the point `D` lies on the internal angle
bisectors of triangle `APB` at `A` and `B`, so `D` is its incenter
(bridge unoriented bisector equalities to oriented ones using the interior
hypothesis, then `Affine.Simplex.eq_incenter_of_oangle_eq` from
`Mathlib/Geometry/Euclidean/Angle/Incenter.lean`; similarly `E` is the
incenter of `APC`). By `Affine.Simplex.incenter_eq_affineCombination` with
`excenterWeightsUnnorm_empty_apply`, `D` is the affine combination of
`![A, P, B]` with weights proportional to the opposite side lengths
`(dist P B, dist A B, dist A P)`. Hence the point
`W = (dist P B • A + dist A B • P) / (dist P B + dist A B)` of line `AP`
is collinear with `B` and `D` (this is the angle bisector theorem:
`AW : WP = AB : BP`). Symmetrically, `CE` meets `AP` in `W'` with
`AW' : W'P = AC : CP`. The hypothesis `dist A B * dist C P = dist A C * dist B P`
gives `W = W'` (affine coordinates on the line `AP` are unique, `A ≠ P`),
which is the required common point. -/
lemma exists_point_collinear_of_dist_mul_eq
    (A B C P D E : EuclideanSpace ℝ (Fin 2))
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hP : P ∈ interior (convexHull ℝ {A, B, C}))
    (hD : D ∈ interior (convexHull ℝ {A, P, B}))
    (hAD : ∠ B A D = ∠ D A P)
    (hBD : ∠ A B D = ∠ D B P)
    (hE : E ∈ interior (convexHull ℝ {A, P, C}))
    (hAE : ∠ C A E = ∠ E A P)
    (hCE : ∠ A C E = ∠ E C P)
    (hratio : dist A B * dist C P = dist A C * dist B P) :
    ∃ W : EuclideanSpace ℝ (Fin 2),
      Collinear ℝ {A, P, W} ∧ Collinear ℝ {B, D, W} ∧ Collinear ℝ {C, E, W} := by
  exact l2_reduction A B C P D E hABC hP hD hAD hBD hE hAE hCE hratio

snip end

problem imo1996_p2
    (A B C P D E : EuclideanSpace ℝ (Fin 2))
    (hABC : AffineIndependent ℝ ![A, B, C])
    -- `P` lies inside the triangle.
    (hP : P ∈ interior (convexHull ℝ {A, B, C}))
    -- `D` is the incenter of triangle `APB`: it lies inside the triangle
    -- and on the internal angle bisectors at `A` and `B`.
    (hD : D ∈ interior (convexHull ℝ {A, P, B}))
    (hAD : ∠ B A D = ∠ D A P)
    (hBD : ∠ A B D = ∠ D B P)
    -- `E` is the incenter of triangle `APC`.
    (hE : E ∈ interior (convexHull ℝ {A, P, C}))
    (hAE : ∠ C A E = ∠ E A P)
    (hCE : ∠ A C E = ∠ E C P)
    -- The angle condition.
    (hangle : ∠ A P B - ∠ A C B = ∠ A P C - ∠ A B C) :
    ∃ W : EuclideanSpace ℝ (Fin 2),
      Collinear ℝ {A, P, W} ∧ Collinear ℝ {B, D, W} ∧ Collinear ℝ {C, E, W} := by
  exact exists_point_collinear_of_dist_mul_eq A B C P D E hABC hP hD hAD hBD hE hAE hCE
    (dist_mul_eq_dist_mul_of_angle_sub_eq_angle_sub A B C P hABC hP hangle)

end Imo1996P2
