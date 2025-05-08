/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# Singapore 2019, Round 1, Problem 2

http://www.realsutra.com/limjeck/SMO_Senior_2019.pdf

Simplify $(sqrt{10} - sqrt{2})^{1/3} * (sqrt{10} + sqrt{2})^{7/3}$.
-/
open Real

namespace Singapore2019R1P2

problem singapore2019_r1_p2 : (sqrt 10 - sqrt 2)^(1 / 3 : ℝ) * (sqrt 10 + sqrt 2)^(7 / 3 : ℝ) = 24 + 8 * sqrt 5 := by
  have h1 : (sqrt 10 - sqrt 2)^(1 / 3 : ℝ) * (sqrt 10 + sqrt 2)^(7 / 3 : ℝ) =
      ((sqrt 10 - sqrt 2) * (sqrt 10 + sqrt 2))^(1 / 3 : ℝ) * (sqrt 10 + sqrt 2)^(2 : ℝ) := by
    have h2 : (sqrt 10 - sqrt 2)^(1 / 3 : ℝ) * (sqrt 10 + sqrt 2)^(7 / 3 : ℝ) =
        (sqrt 10 - sqrt 2)^(1 / 3 : ℝ) * (sqrt 10 + sqrt 2)^(1 / 3 : ℝ) * (sqrt 10 + sqrt 2)^(2 : ℝ) := by
      rw [show (sqrt 10 + sqrt 2)^(7 / 3 : ℝ) = (sqrt 10 + sqrt 2)^(1 / 3 + 2 : ℝ) by norm_num, rpow_add (by positivity)]
      ring_nf
    rw [h2, ← mul_rpow (by norm_num)]
    positivity
  rw [h1]
  have h2 := calc
    (sqrt 10 - sqrt 2) * (sqrt 10 + sqrt 2)
      = ((sqrt 10) ^ 2 - (sqrt 2) ^ 2 : ℝ) := by ring
    _ = 8 := by simp [sq_sqrt] ; norm_num
  have h3 : ((sqrt 10 - sqrt 2) * (sqrt 10 + sqrt 2) : ℝ)^(1 / 3 : ℝ) = 2 := by
    rw [h2]
    have h4 : 8 ^ (1 / 3 : ℝ) = (2 : ℝ) := by
      rw [show 8 ^ (1 / 3 : ℝ) = ((2 : ℝ) ^ (3 : ℝ)) ^ (1 / 3 : ℝ) by norm_num, ← rpow_mul]
      repeat norm_num
    rw [h4]
  rw [h3]
  have h5 : (sqrt 10 + sqrt 2) ^ (2 : ℝ) = (12 + 4 * sqrt 5 : ℝ) := by
    norm_cast
    ring_nf
    have h8 : (sqrt 10) ^ 2 = (10 : ℝ) := sq_sqrt (by norm_num)
    have h9 : (sqrt 2) ^ 2 = (2 : ℝ) := sq_sqrt (by norm_num)
    have h10 : sqrt 10 * sqrt 2 = sqrt 20 := by
      rw [← sqrt_mul]
      repeat norm_num
    have h11 : sqrt 20 = 2 * sqrt 5 := by
      rw [sqrt_eq_iff_mul_self_eq] <;> norm_num
      ring_nf
      norm_num
    rw [h8, h9, h10, h11]
    ring
  rw [h5]
  ring
