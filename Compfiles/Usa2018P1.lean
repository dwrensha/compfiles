/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongyu Ouyang
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

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

lemma am_gm (a b : ℝ) : a > 0 → b > 0 → 2 * (a * b) ^ ((1 : ℝ) / 2) ≤ a + b := by
  intro ha hb
  have gsa := Real.sqrt_pos.mpr ha
  have gsb := Real.sqrt_pos.mpr hb
  set sa := Real.sqrt a with hsa
  set sb := Real.sqrt b with hsb
  have : a = sa * sa := by rw [hsa]; field_simp
  rw [this]
  have : b = sb * sb := by rw [hsb]; field_simp
  rw [this]
  have : (sa * sa * (sb * sb)) ^ ((1 : ℝ) / 2) = sa * sb := by
    simp only [one_div]
    rw [Real.mul_rpow, ←pow_two, ←pow_two, ←Real.rpow_two, ←Real.rpow_two]
    rw [Real.rpow_rpow_inv (by positivity), Real.rpow_rpow_inv (by positivity)]
    linarith
    linarith
    positivity
    positivity
  rw [this]
  rw [←pow_two, ←pow_two]
  rw [←mul_assoc]
  refine two_mul_le_add_sq sa sb

snip end


problem usa2018_p1 (a b c : ℝ) : a > 0 → b > 0 → c > 0 → a + b + c = 4 * (a * b * c) ^ ((1 : ℝ) / 3) →
  2 * (a * b + b * c + c * a) + 4 * (min (min (a * a) (b * b)) (c * c)) ≥ a^2 + b^2 + c^2 := by
  -- solution 1 from
  -- https://artofproblemsolving.com/wiki/index.php/2018_USAMO_Problems/Problem_1
  intro ha hb hc heq
  wlog h1 : a ≤ b with H1
  · have swap1 : (a * b + b * c + c * a) = (b * a + a * c + c * b) := by ring 
    have swap2 : (min (min (a * a) (b * b)) (c * c)) = (min (min (b * b) (a * a)) (c * c)) := by
      simp only [min_comm, min_assoc]
    have swap3 : a^2 + b^2 + c^2 = b^2 + a^2 + c^2 := by ring
    rw [swap1, swap2, swap3]
    refine H1 b a c hb ha hc ?_ ?_
    linear_combination (norm := (field_simp; ring_nf)) 1 * heq
    linarith
  · wlog h2 : a ≤ c with H2
    · have swap1 : (a * b + b * c + c * a) = (c * b + b * a + a * c) := by ring 
      have swap2 : (min (min (a * a) (b * b)) (c * c)) = (min (min (c * c) (b * b)) (a * a)) := by
        rw [min_comm, min_assoc, min_comm (a*a)]
      have swap3 : a^2 + b^2 + c^2 = c^2 + b^2 + a^2 := by ring
      rw [swap1, swap2, swap3]
      refine H2 c b a hc hb ha ?_ ?_ ?_
      linear_combination (norm := (field_simp; ring_nf)) 1 * heq
      linarith
      linarith
    · wlog h3 : b ≤ c with H3
      · have swap1 : (a * b + b * c + c * a) = (a * c + c * b + b * a) := by ring 
        have swap2 : (min (min (a * a) (b * b)) (c * c)) = (min (min (a * a) (c * c)) (b * b)) := by
          rw [min_assoc, min_comm (b*b), ←min_assoc]
        have swap3 : a^2 + b^2 + c^2 = a^2 + c^2 + b^2 := by ring
        rw [swap1, swap2, swap3]
        refine H3 a c b ha hc hb ?_ h2 h1 ?_
        linear_combination (norm := (field_simp; ring_nf)) 1 * heq
        linarith
      · have aabb : a * a ≤ b * b := by apply mul_self_le_mul_self; linarith; assumption
        have aacc : a * a ≤ c * c := by apply mul_self_le_mul_self; linarith; assumption
        simp only [aabb, aacc, min_eq_left]
        apply le_of_add_le_add_right (a := 2 * (a * b + b * c + c * a))
        have manual1 : (a + b + c) ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 + (2 : ℝ) * (a * b + b * c + c * a) := by ring
        rw [←manual1, heq]
        have manual2 : (2 : ℝ) * (a * b + b * c + c * a) + (4 : ℝ) * (a * a) + (2 : ℝ) * (a * b + b * c + c * a)
          = 4 * (a * (a + b + c) + b * c) := by ring_nf
        rw [manual2, heq]
        have amgm := am_gm (a * ((4 : ℝ) * (a * b * c) ^ ((1 : ℝ) / 3))) (b * c) (by positivity) (by positivity)
        rw [←(mul_le_mul_left (by norm_num : 0 < (4 : ℝ)))] at amgm
        suffices eq1 : (4 : ℝ) * ((2 : ℝ) * (a * ((4 : ℝ) * (a * b * c) ^ (1 / 3 : ℝ)) * (b * c)) ^ (1 / 2 : ℝ)) = ((4 : ℝ) * (a * b * c) ^ (1 / 3 : ℝ)) ^ (2 : ℕ)
        rw [←eq1]; exact amgm
        ring_nf
        rw [←Real.rpow_two, ←Real.rpow_mul]
        norm_num
        nth_rw 1 [(by simp : a * b * c = (a * b * c) ^ (1 : ℕ))]
        rw [mul_comm ((a * b * c) ^ (1 : ℕ)), ←Real.rpow_add_nat]
        norm_num
        rw [Real.mul_rpow]
        rw [←Real.rpow_mul]
        norm_num
        rw [mul_assoc]
        suffices manual3 : ((4 : ℝ) ^ (1 / 2 : ℝ) * (8 : ℝ)) = (16 : ℝ)
        rw [manual3]
        rotate_left
        positivity
        positivity
        positivity
        positivity
        positivity
        rw [←Real.sqrt_eq_rpow]
        rw [(by norm_num : (4 : ℝ) = (2 : ℝ) * (2 : ℝ))]
        rw [Real.sqrt_mul_self]
        norm_num
        positivity
