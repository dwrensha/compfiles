/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# Singapore Math Olympiad (Senior) 2019 (Round 1), Problem 4

http://www.realsutra.com/limjeck/SMO_Senior_2019.pdf

If $\log_{21} 3 = x$, express $\log_7 9$ in terms of $x$.
-/

open Real

namespace Singapore2019R1P4

noncomputable determine solution (x : ℝ) : ℝ := 2*x / (1-x)

problem singapore2019_r1_p4 (x : ℝ) (hx : Real.logb 21 3 = x) :
    Real.logb 7 9 = solution x := by
  have h1 : Real.logb 7 9 = Real.logb 21 9 / Real.logb 21 7 := by
    field_simp [Real.logb]
  have h2 : Real.logb 21 9 = 2 * Real.logb 21 3 := by
    simp [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.logb_pow]
  have h3 : Real.logb 21 7 = 1 - Real.logb 21 3 := by
    have h5 : Real.logb 21 3 + Real.logb 21 7 = Real.logb 21 (3 * 7) := by
      rw [Real.logb_mul (by norm_num) (by norm_num)]
    have h4 : Real.logb 21 3 + Real.logb 21 7 = 1 := by
      rw [h5]
      norm_num [Real.logb_self_eq_one]
    linarith
  rw [h1, h2, h3, hx]
