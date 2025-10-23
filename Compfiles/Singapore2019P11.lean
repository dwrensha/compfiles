/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# Singapore Math Olympiad (Senior) 2019 (Round 1), Problem 11

http://www.realsutra.com/limjeck/SMO_Senior_2019.pdf

Find the value of 448 * (sin 12 degrees) * (sin 39 degrees) * (sin 51 degrees) / sin 24 degrees
-/
open Real

namespace Singapore2019R1P11

noncomputable determine solution : ℝ := 112

problem singapore2019_r1_p11 :
    448 * sin (12 * π / 180) * sin (39 * π / 180) * sin (51 * π / 180) /
     sin (24 * π / 180) = solution := by
  rw [show sin (51 * π / 180) = cos (39 * π / 180) by rw [← sin_pi_div_two_sub]; congr; ring]

  rw [mul_assoc]

  rw [show sin (39 * π / 180) * cos (39 * π / 180) = (1 / 2) * sin (78 * π / 180) by
      rw [show 78 * π / 180 = 2 * (39 * π / 180) by ring, sin_two_mul]; ring]

  rw [show sin (78 * π / 180) = cos (12 * π / 180) by rw [← sin_pi_div_two_sub]; congr; ring]

  rw [show sin (24 * π / 180) = 2 * sin (12 * π / 180) * cos (12 * π / 180) by
      rw [← sin_two_mul]; congr; ring]

  have h2 : 0 < sin (12 * π / 180) := by
    apply sin_pos_of_pos_of_lt_pi
    positivity
    linarith [Real.pi_pos]

  have h3 : 0 < cos (12 * π / 180) := by
    apply cos_pos_of_mem_Ioo
    constructor
    · linarith [Real.pi_pos]
    · linarith [Real.pi_gt_three]

  field_simp [h2, h3]
  norm_num

end Singapore2019R1P11
