/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 1966, Problem 2

Let a, b, c be the lengths of the sides of a triangle, and α, β, γ, respectively,
the angles opposite these sides. Prove that if

  a + b = tan(γ/2) (a tan α + b tan β)

then the triangle is isosceles.
-/

namespace Imo1966P2

snip begin

/-- If the positive side lengths `a`, `b` of a triangle and the opposite angles
`A`, `B` (elements of `(0, π)`) satisfy the law of sines `a * sin B = b * sin A`
and additionally `a * cos B = b * cos A`, then `A = B`: the two relations combine
into `sin (A - B) = 0`, and `A - B` lies in `(-π, π)`. -/
lemma angle_eq_of_mul_cos_eq {a b A B : ℝ} (hb : 0 < b)
    (hA0 : 0 < A) (hApi : A < Real.pi) (hB0 : 0 < B) (hBpi : B < Real.pi)
    (hsine : a * Real.sin B = b * Real.sin A) (h : a * Real.cos B = b * Real.cos A) :
    A = B := by
  have key : b * (Real.sin A * Real.cos B - Real.cos A * Real.sin B) = 0 := by
    linear_combination Real.sin B * h - Real.cos B * hsine
  have h' : Real.sin A * Real.cos B - Real.cos A * Real.sin B = 0 :=
    (mul_eq_zero.mp key).resolve_left (ne_of_gt hb)
  have hs0 : Real.sin (A - B) = 0 := by
    rw [Real.sin_sub]
    exact h'
  have hAB : A - B = 0 :=
    (Real.sin_eq_zero_iff_of_lt_of_lt (by linarith) (by linarith)).mp hs0
  linarith

/-- If the angles `A`, `B`, `C` of a triangle (elements of `(0, π)` summing to `π`)
satisfy `cos (A + C / 2) = 0`, then `A = B`: strict monotonicity of `cos` on
`[0, π]` forces `A + C / 2 = π / 2`, which together with `A + B + C = π` gives
`A = B`. -/
lemma angle_eq_of_cos_eq_zero {A B C : ℝ} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hABC : A + B + C = Real.pi) (h : Real.cos (A + C / 2) = 0) : A = B := by
  have hAClt : A + C / 2 < Real.pi := by linarith
  have hAC : A + C / 2 = Real.pi / 2 :=
    Real.strictAntiOn_cos.injOn
      ⟨by linarith, le_of_lt hAClt⟩
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
      (by rw [h, Real.cos_pi_div_two])
  linarith

/-- In a triangle, equal angles `A = B` imply equal opposite sides `a = b`
(via the law of sines). -/
lemma side_eq_of_angle_eq {a b A B : ℝ} (hsinB : Real.sin B ≠ 0)
    (hsine : a * Real.sin B = b * Real.sin A) (hAB : A = B) : a = b := by
  subst hAB
  exact mul_right_cancel₀ hsinB hsine

snip end

problem imo1966_p2 (a b A B C : ℝ) (_ha : 0 < a) (hb : 0 < b)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hABC : A + B + C = Real.pi)
    (hcosA : Real.cos A ≠ 0) (hcosB : Real.cos B ≠ 0)
    (hsine : a * Real.sin B = b * Real.sin A)
    (h : a + b = Real.tan (C / 2) * (a * Real.tan A + b * Real.tan B)) :
    a = b := by
  have hApi : A < Real.pi := by linarith
  have hBpi : B < Real.pi := by linarith
  have hCpi : C < Real.pi := by linarith
  have hsinB : 0 < Real.sin B := Real.sin_pos_of_pos_of_lt_pi hB hBpi
  have hcosC2 : Real.cos (C / 2) ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos, hC], by linarith [Real.pi_pos, hCpi]⟩)
  -- Multiply the hypothesis by `cos A * cos B * cos (C / 2)` to clear denominators.
  have h1 : (a + b) * Real.cos A * Real.cos B * Real.cos (C / 2) =
      Real.sin (C / 2) * (a * Real.sin A * Real.cos B + b * Real.cos A * Real.sin B) := by
    rw [h, Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos]
    field_simp [hcosA, hcosB, hcosC2]
  -- Regroup, using `cos (x + y) = cos x * cos y - sin x * sin y`.
  have h2 : a * Real.cos B * Real.cos (A + C / 2) + b * Real.cos A * Real.cos (B + C / 2) = 0 := by
    rw [Real.cos_add, Real.cos_add]
    linear_combination h1
  -- The angles `A + C / 2` and `B + C / 2` sum to `π`, so their cosines are opposite.
  have h3 : Real.cos (B + C / 2) = -Real.cos (A + C / 2) := by
    have hsum : B + C / 2 = Real.pi - (A + C / 2) := by linarith
    rw [hsum, Real.cos_pi_sub]
  have h4 : (a * Real.cos B - b * Real.cos A) * Real.cos (A + C / 2) = 0 := by
    rw [h3] at h2
    linear_combination h2
  rcases mul_eq_zero.mp h4 with hcase | hcase
  · exact side_eq_of_angle_eq (ne_of_gt hsinB) hsine
      (angle_eq_of_mul_cos_eq hb hA hApi hB hBpi hsine (sub_eq_zero.mp hcase))
  · exact side_eq_of_angle_eq (ne_of_gt hsinB) hsine
      (angle_eq_of_cos_eq_zero hA hB hC hABC hcase)

end Imo1966P2
