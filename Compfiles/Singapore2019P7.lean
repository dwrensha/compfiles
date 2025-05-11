/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# Singapore Math Olympiad (Senior) 2019 (Round 1), Problem 7

http://www.realsutra.com/limjeck/SMO_Senior_2019.pdf

Suppose that $\tan x = 5$. Find the value of $\frac{6 + \sin 2x}{1 + \cos 2x}$.
-/
open Real

namespace Singapore2019R1P7

noncomputable determine solution : ℝ := 83

problem singapore2019_r1_p7 (x : ℝ) (hx : tan x = 5) :
    (6 + sin (2 * x)) / (1 + cos (2 * x)) = solution := by

  have h1 : cos x ≠ 0 := by
    by_contra h
    have htan : tan x = 0 := by
      rw [tan_eq_sin_div_cos]
      simp only [h, div_zero]
    linarith

  rw [tan_eq_sin_div_cos] at hx

  have h2 : sin x = 5 * cos x := by
    field_simp at hx
    exact hx

  have h4 : sin x ^ 2 = 25 * cos x ^ 2 := by
    rw [h2]
    ring

  have h5 : 26 * cos x ^ 2 = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq x]

  have hsin2x_val : sin (2 * x) = 5 / 13 := by
    rw [sin_two_mul]
    nlinarith

  have hcos2x_val : cos (2 * x) = -12 / 13 := by
    rw [cos_two_mul]
    nlinarith

  field_simp [hcos2x_val]
  unfold solution
  linarith
