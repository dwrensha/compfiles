/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# USA Mathematical Olympiad 1987, Problem 2

The feet of the angle bisectors of the triangle ABC form a right-angled
triangle. If the right-angle is at X, where AX is the bisector of angle A,
find all possible values for angle A.
-/

open scoped InnerProductSpace EuclideanGeometry

namespace Usa1987P2

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MetricSpace P] [NormedAddTorsor V P]

snip begin

/-- `cos (2π/3) = -1/2`. -/
lemma cos_two_pi_div_three : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
  have h : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
  rw [h, Real.cos_pi_sub, Real.cos_pi_div_three]
  ring

/-- `arccos (-1/2) = 2π/3`. -/
lemma arccos_neg_one_half : Real.arccos (-1 / 2 : ℝ) = 2 * Real.pi / 3 := by
  rw [← cos_two_pi_div_three,
    Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])]

/-- The inner product `⟪Z - X, Y - X⟫`, with denominators cleared, as a
polynomial in the side lengths `a b c` and the inner products of the
vectors `u` and `w`.  Pure vector algebra. -/
lemma cleared_inner (u w : V) (a b c : ℝ)
    (hab : a + b ≠ 0) (hbc : b + c ≠ 0) (hca : c + a ≠ 0) :
    (a + b) * (a + c) * (b + c)^2 *
        ⟪(b/(a+b) - b/(b+c)) • u - (c/(b+c)) • w,
          (-(b/(b+c))) • u + (c/(c+a) - c/(b+c)) • w⟫_ℝ
      = b^2 * ⟪u, u⟫_ℝ * (a^2 - c^2) + c^2 * ⟪w, w⟫_ℝ * (a^2 - b^2) +
        2 * b * c * ⟪u, w⟫_ℝ * (a^2 + b*c) := by
  simp only [inner_sub_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, real_inner_comm w u]
  field_simp
  ring

/-- The cleared inner product factors as `a²bc(bc + 2⟪u,w⟫)` once the
law of cosines `a² = c² + b² - 2⟪u,w⟫` is taken into account. -/
lemma factor_cleared_inner {p : ℝ} {a b c : ℝ} (ha2 : a^2 = c^2 + b^2 - 2 * p) :
    b^2 * c^2 * (a^2 - c^2) + c^2 * b^2 * (a^2 - b^2) + 2 * b * c * p * (a^2 + b*c)
      = a^2 * b * c * (b * c + 2 * p) := by
  linear_combination b^2 * c^2 * ha2

/-- In a non-collinear triple, the first two points are distinct. -/
lemma ne_left_of_not_collinear {A B C : P} (hABC : ¬ Collinear ℝ ({A, B, C} : Set P)) :
    A ≠ B := by
  intro h
  apply hABC
  rw [h]
  simpa using collinear_pair ℝ B C

/-- In a non-collinear triple, the first and third points are distinct. -/
lemma ne_right_of_not_collinear {A B C : P} (hABC : ¬ Collinear ℝ ({A, B, C} : Set P)) :
    A ≠ C := by
  intro h
  apply hABC
  rw [h, Set.insert_eq_of_mem (show C ∈ ({B, C} : Set P) by simp)]
  exact collinear_pair ℝ B C

/-- In a non-collinear triple, the last two points are distinct. -/
lemma ne_mid_of_not_collinear {A B C : P} (hABC : ¬ Collinear ℝ ({A, B, C} : Set P)) :
    B ≠ C := by
  intro h
  apply hABC
  rw [h]
  simpa using collinear_pair ℝ A C

snip end

noncomputable determine solution : ℝ := 2 * Real.pi / 3

problem usa1987_p2
    {A B C X Y Z : P}
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set P))
    -- `X` is the foot of the internal bisector of `∠A` on `BC`:
    -- by the angle bisector theorem `BX : XC = AB : AC`.
    (hX : X = AffineMap.lineMap B C (dist A B / (dist A C + dist A B)))
    -- `Y` is the foot of the internal bisector of `∠B` on `CA`:
    -- `CY : YA = BC : BA`.
    (hY : Y = AffineMap.lineMap C A (dist B C / (dist A B + dist B C)))
    -- `Z` is the foot of the internal bisector of `∠C` on `AB`:
    -- `AZ : ZB = CA : CB`.
    (hZ : Z = AffineMap.lineMap A B (dist A C / (dist B C + dist A C))) :
    ∠ Y X Z = Real.pi / 2 ↔ ∠ B A C = solution := by
  show (∠ Y X Z = Real.pi / 2) ↔ (∠ B A C = 2 * Real.pi / 3)
  -- distinctness of the vertices, hence positivity of the side lengths
  have hAB : A ≠ B := ne_left_of_not_collinear hABC
  have hAC : A ≠ C := ne_right_of_not_collinear hABC
  have hBC : B ≠ C := ne_mid_of_not_collinear hABC
  set a : ℝ := dist B C with ha
  set b : ℝ := dist A C with hb
  set c : ℝ := dist A B with hc
  have hapos : 0 < a := by rw [ha]; exact dist_pos.mpr hBC
  have hbpos : 0 < b := by rw [hb]; exact dist_pos.mpr hAC
  have hcpos : 0 < c := by rw [hc]; exact dist_pos.mpr hAB
  -- vectors from A
  set u : V := B -ᵥ A with hu
  set w : V := C -ᵥ A with hw
  have hnormu : ‖u‖ = c := by rw [hu, ← dist_eq_norm_vsub' V A B, ← hc]
  have hnormw : ‖w‖ = b := by rw [hw, ← dist_eq_norm_vsub' V A C, ← hb]
  have hBCv : C -ᵥ B = w - u := by
    rw [hu, hw]
    exact (vsub_sub_vsub_cancel_right C B A).symm
  -- law of cosines
  have ha2 : a^2 = ‖u‖^2 + ‖w‖^2 - 2 * ⟪u, w⟫_ℝ := by
    rw [ha, dist_eq_norm_vsub' V B C, hBCv, norm_sub_sq_real, real_inner_comm u w]
    ring
  have ha2' : a^2 = c^2 + b^2 - 2 * ⟪u, w⟫_ℝ := by rw [ha2, hnormu, hnormw]
  -- the feet of the bisectors, as vectors from A
  have hXv : X -ᵥ A = (b/(b+c)) • u + (c/(b+c)) • w := by
    have hbc : (b : ℝ) + c ≠ 0 := ne_of_gt (add_pos hbpos hcpos)
    have h1 : X -ᵥ B = (c/(b+c)) • (C -ᵥ B) := by
      rw [hX]
      exact AffineMap.lineMap_vsub_left B C _
    calc X -ᵥ A = (X -ᵥ B) + (B -ᵥ A) := (vsub_add_vsub_cancel X B A).symm
      _ = (c/(b+c)) • (w - u) + u := by rw [h1, hBCv, ← hu]
      _ = (b/(b+c)) • u + (c/(b+c)) • w := by
            rw [smul_sub]
            have h3 : b/(b+c) = 1 - c/(b+c) := by field_simp; ring
            rw [h3, sub_smul, one_smul]
            abel
  have hYv : Y -ᵥ A = (c/(c+a)) • w := by
    have hca : (c : ℝ) + a ≠ 0 := ne_of_gt (add_pos hcpos hapos)
    have h1 : Y -ᵥ A = (1 - a/(c+a)) • (C -ᵥ A) := by
      rw [hY]
      exact AffineMap.lineMap_vsub_right C A _
    rw [h1, ← hw]
    have h2 : 1 - a/(c+a) = c/(c+a) := by field_simp; ring
    rw [h2]
  have hZv : Z -ᵥ A = (b/(a+b)) • u := by
    rw [hZ]
    exact AffineMap.lineMap_vsub_left A B _
  have hZX : Z -ᵥ X = (b/(a+b) - b/(b+c)) • u - (c/(b+c)) • w := by
    have h : Z -ᵥ X = (Z -ᵥ A) - (X -ᵥ A) := (vsub_sub_vsub_cancel_right Z X A).symm
    rw [h, hZv, hXv]
    module
  have hYX : Y -ᵥ X = (-(b/(b+c))) • u + (c/(c+a) - c/(b+c)) • w := by
    have h : Y -ᵥ X = (Y -ᵥ A) - (X -ᵥ A) := (vsub_sub_vsub_cancel_right Y X A).symm
    rw [h, hYv, hXv]
    module
  -- the right-angle condition, as a polynomial equation
  have hab : a + b ≠ 0 := ne_of_gt (add_pos hapos hbpos)
  have hbc' : b + c ≠ 0 := ne_of_gt (add_pos hbpos hcpos)
  have hca : c + a ≠ 0 := ne_of_gt (add_pos hcpos hapos)
  have key : (a+b) * (a+c) * (b+c)^2 * ⟪Z -ᵥ X, Y -ᵥ X⟫_ℝ
      = b^2 * ⟪u, u⟫_ℝ * (a^2 - c^2) + c^2 * ⟪w, w⟫_ℝ * (a^2 - b^2) +
        2 * b * c * ⟪u, w⟫_ℝ * (a^2 + b*c) := by
    rw [hZX, hYX]
    exact cleared_inner u w a b c hab hbc' hca
  have key0 : ⟪Z -ᵥ X, Y -ᵥ X⟫_ℝ = 0 ↔ ⟪u, w⟫_ℝ = -(b*c)/2 := by
    have hden : (0:ℝ) < (a+b) * (a+c) * (b+c)^2 := by positivity
    rw [← mul_eq_zero_iff_left (ne_of_gt hden), key,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hnormu, hnormw,
      factor_cleared_inner ha2']
    constructor
    · intro h
      have hne : a^2 * b * c ≠ 0 := ne_of_gt (by positivity)
      have h2 : b * c + 2 * ⟪u, w⟫_ℝ = 0 := (mul_eq_zero_iff_left hne).mp h
      linarith
    · intro h
      have h2 : b * c + 2 * ⟪u, w⟫_ℝ = 0 := by linarith
      rw [h2, mul_zero]
  -- the angle at A, as an arccos
  have hnorm : ‖u‖ * ‖w‖ = c * b := by rw [hnormu, hnormw]
  have habs : |⟪u, w⟫_ℝ / (c*b)| ≤ 1 := by
    have h := abs_real_inner_div_norm_mul_norm_le_one u w
    rwa [hnormu, hnormw] at h
  obtain ⟨hlo, hhi⟩ := abs_le.mp habs
  have hBAC : ∠ B A C = Real.arccos (⟪u, w⟫_ℝ / (c*b)) := by
    show Real.arccos (⟪u, w⟫_ℝ / (‖u‖ * ‖w‖)) = Real.arccos (⟪u, w⟫_ℝ / (c*b))
    rw [hnormu, hnormw]
  -- the right angle at X
  have hright : ∠ Y X Z = Real.pi / 2 ↔ ⟪Z -ᵥ X, Y -ᵥ X⟫_ℝ = 0 := by
    rw [show (∠ Y X Z = Real.pi / 2) ↔
        InnerProductGeometry.angle (Y -ᵥ X) (Z -ᵥ X) = Real.pi / 2 from Iff.rfl,
      ← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two, real_inner_comm]
  -- assemble the chain of equivalences
  calc (∠ Y X Z = Real.pi / 2)
      ↔ ⟪Z -ᵥ X, Y -ᵥ X⟫_ℝ = 0 := hright
    _ ↔ ⟪u, w⟫_ℝ = -(b*c)/2 := key0
    _ ↔ ⟪u, w⟫_ℝ / (c*b) = -1/2 := by
          have hcb : c * b ≠ 0 := mul_ne_zero (ne_of_gt hcpos) (ne_of_gt hbpos)
          rw [div_eq_iff hcb]
          have h3 : (-1:ℝ)/2 * (c*b) = -(b*c)/2 := by ring
          rw [h3]
    _ ↔ ∠ B A C = 2 * Real.pi / 3 := by
          rw [hBAC]
          constructor
          · intro h
            rw [h]
            exact arccos_neg_one_half
          · intro h
            have h1 : ⟪u, w⟫_ℝ / (c*b)
                = Real.cos (Real.arccos (⟪u, w⟫_ℝ / (c*b))) :=
              (Real.cos_arccos hlo hhi).symm
            rw [h1, h, cos_two_pi_div_three]

end Usa1987P2
