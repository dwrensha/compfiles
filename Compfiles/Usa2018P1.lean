/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongyu Ouyang
-/

import Mathlib.Tactic
import Mathlib.Analysis.MeanInequalities

import ProblemExtraction

problem_file { tags := [.Algebra, .Inequality] }

/-!
# USA Mathematical Olympiad 2018, Problem 1

Given that a,b,c are positive real numbers such that

  a + b + c = 4 ∛(abc)

prove that 2(ab + bc + ca) + 4min(a²,b²,c²) ≥ a² + b² + c²
-/

namespace Usa2018P1

snip begin

lemma am_gm (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    2 * (a * b) ^ ((1 : ℝ) / 2) ≤ a + b := by
  have hw : (0 : ℝ) ≤ 1/2 := by norm_num
  rw [Real.mul_rpow ha hb]
  linarith [Real.geom_mean_le_arith_mean2_weighted hw hw ha hb (by norm_num)]

snip end


problem usa2018_p1 (a b c : ℝ) :
    a > 0 → b > 0 → c > 0 → a + b + c = 4 * (a * b * c) ^ ((1 : ℝ) / 3) →
    2 * (a * b + b * c + c * a) +
     4 * (min (min (a * a) (b * b)) (c * c)) ≥ a^2 + b^2 + c^2 := by
  -- solution 1 from
  -- https://artofproblemsolving.com/wiki/index.php/2018_USAMO_Problems/Problem_1
  intro ha hb hc heq
  wlog h1 : a ≤ b with H1
  · grind only [= min_def]
  · wlog h2 : a ≤ c with H2
    · move_add [←(c^2)]; move_add [(a^2)]
      convert (H2 c b a hc hb ha ?_ ?_ ?_) using 3
      · ring_nf
      · exact inf_left_right_swap _ _ _
      · linear_combination (norm := (ring_nf)) 1 * heq
      · linarith
      · linarith
    · wlog h3 : b ≤ c with H3
      · move_add [(b^2)]
        convert (H3 a c b ha hc hb ?_ h2 h1 ?_) using 3
        · linarith
        · rw [min_comm, ←min_assoc, min_comm (a*a)]
        · linear_combination (norm := (field_simp; ring_nf)) 1 * heq
        · linarith
      · have aabb : a * a ≤ b * b := mul_self_le_mul_self (le_of_lt ha) h1
        have aacc : a * a ≤ c * c := mul_self_le_mul_self (le_of_lt ha) h2
        simp only [aabb, aacc, min_eq_left]
        apply le_of_add_le_add_right (a := 2 * (a * b + b * c + c * a))
        convert_to (a + b + c) ^ 2 ≤ 4 * (a * (a + b + c) + b * c)
        · ring_nf
        · ring_nf
        rw [heq]
        have amgm := am_gm (a * ((4 : ℝ) * (a * b * c) ^ ((1 : ℝ) / 3))) (b * c)
                           (by positivity) (by positivity)
        rw [←mul_le_mul_iff_right₀ zero_lt_four] at amgm
        convert amgm
        ring_nf
        nth_rw 2 [(by simp : a * b * c = (a * b * c) ^ (1 : ℕ))]
        rw [←Real.rpow_two, ←Real.rpow_mul (by positivity)]
        rw [mul_comm ((a * b * c) ^ (1 : ℕ)), ←Real.rpow_add_natCast (by positivity)]
        norm_num
        nth_rw 2 [Real.mul_rpow (by positivity) (by positivity)]
        rw [←Real.rpow_mul (by positivity)]
        norm_num
        rw [(mul_assoc _ _ 8)]
        simp only [mul_eq_mul_left_iff]
        left
        norm_num1


end Usa2018P1
