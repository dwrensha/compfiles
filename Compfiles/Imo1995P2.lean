/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zheng Yuan
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra, .Inequality] }

/-!
# International Mathematical Olympiad 1995, Problem 2

Let a, b, c be positive real numbers such that abc = 1. Show that

    1 / (a³(b + c)) + 1 / (b³(c + a)) + 1 / (c³(a + b)) ≥ 3/2.
-/

namespace Imo1995P2

open Finset

problem imo1995_p2 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    3 / 2 ≤ 1 / (a^3 * (b + c)) + 1 / (b^3 * (c + a)) + 1 / (c^3 * (a + b)) := by
  -- We follow the third solution from AoPS (https://artofproblemsolving.com/wiki/index.php/1995_IMO_Problems/Problem_2)

  have h1 : (1 / (a^3 * (b + c)) + 1 / (b^3 * (c + a)) + 1 / (c^3 * (a + b))) * (a * (b + c) + b * (c + a) + c * (a + b)) ≥ (1 / a + 1 / b + 1 / c) ^ 2 := by

    let f : Fin 3 → ℝ := fun i =>
      match i with
      | 0 => Real.sqrt (1 / (a^3 * (b + c)))
      | 1 => Real.sqrt (1 / (b^3 * (c + a)))
      | 2 => Real.sqrt (1 / (c^3 * (a + b)))

    let g : Fin 3 → ℝ := fun i =>
      match i with
      | 0 => Real.sqrt (a * (b + c))
      | 1 => Real.sqrt (b * (c + a))
      | 2 => Real.sqrt (c * (a + b))

    have cauchy := sum_mul_sq_le_sq_mul_sq {0, 1, 2} f g
    have lhs0 : 1 / (a^3 * (b + c)) + 1 / (b^3 * (c + a)) + 1 / (c^3 * (a + b)) = ∑ i ∈ {0, 1, 2}, f i ^ 2 := by
      have hbca' : (b + c)⁻¹ * (a ^ 3)⁻¹ ≥ 0 := by positivity
      have hcab' : (c + a)⁻¹ * (b ^ 3)⁻¹ ≥ 0 := by positivity
      have habc' : (a + b)⁻¹ * (c ^ 3)⁻¹ ≥ 0 := by positivity
      simp [sq, f, Real.mul_self_sqrt, hbca', hcab', habc', add_assoc]

    have lhs1 : a * (b + c) + b * (c + a) + c * (a + b) = ∑ i ∈ {0, 1, 2}, g i ^ 2 := by
      have habc : a * (b + c) ≥ 0 := by positivity
      have hbca : b * (c + a) ≥ 0 := by positivity
      have hcab : c * (a + b) ≥ 0 := by positivity
      simp only [Fin.isValue, sq, mem_insert, zero_ne_one, mem_singleton, Fin.reduceEq, or_self,
                 not_false_eq_true, sum_insert, habc, Real.mul_self_sqrt, hbca, sum_singleton, hcab, g]
      ring

    rw [lhs0, lhs1] at *

    have rhs : 1 / a + 1 / b + 1 / c = ∑ i ∈ {0, 1, 2}, f i * g i := by
      simp only [one_div, Fin.isValue, mul_inv_rev, mem_insert, zero_ne_one, mem_singleton,
                 Fin.reduceEq, or_self, not_false_eq_true, sum_insert, sum_singleton, f, g]
      have helper (x : ℝ) (hx : x > 0) : x * √x = √(x ^ 3) := by
        simp only [pow_three]
        have hx' : 0 ≤ x := le_of_lt hx
        have naive : x * x = x ^ 2 := (pow_two x).symm
        have naive' : x ^ 2 * x = x * (x * x) := by ring
        calc x * √x
          _ = (√x * √x) * √x := by field_simp [mul_assoc, mul_comm, mul_left_comm]
          _ = (√(x ^ 2)) * √x := by rw [← Real.sqrt_mul' x hx', naive]
          _ = √(x ^ 2) * √x := by ring_nf
          _ = √(x ^ 2 * x) := (Real.sqrt_mul' (x ^ 2) hx').symm
          _ = √(x * (x * x)) := by rw [naive']

      have ha' : √((b + c)⁻¹ * (a ^ 3)⁻¹) * √(a * (b + c)) = 1 / a := by
        rw [mul_comm]; field_simp [ha.ne', hb.ne', hc.ne', habc]
        have ha'' := by exact helper a ha
        rw [← ha''] at *; ring

      have hb' : √((c + a)⁻¹ * (b ^ 3)⁻¹) * √(b * (c + a)) = 1 / b := by
        rw [mul_comm]; field_simp [ha.ne', hb.ne', hc.ne', habc]
        have hb'' := helper b hb
        rw [← hb''] at *; ring

      have hc' : √((a + b)⁻¹ * (c ^ 3)⁻¹) * √(c * (a + b)) = 1 / c := by
        rw [mul_comm]; field_simp [ha.ne', hb.ne', hc.ne', habc]
        have hc'' := helper c hc
        rw [← hc''] at *; ring
      rw [ha', hb', hc']
      ring

    rw [rhs] at *
    exact cauchy

  have cauchy_helper (x y z : ℝ) (hy : 0 < y) (hmain : x * y ≥ z) : x ≥ z / y :=
    (div_le_iff₀ hy).mpr hmain

  have h1_div : 1 / (a^3 * (b + c)) + 1 / (b^3 * (c + a)) + 1 / (c^3 * (a + b)) ≥ (1 / a + 1 / b + 1 / c) ^ 2 / (a * (b + c) + b * (c + a) + c * (a + b)) := by
    let x := 1 / (a^3 * (b + c)) + 1 / (b^3 * (c + a)) + 1 / (c^3 * (a + b))
    let y := a * (b + c) + b * (c + a) + c * (a + b)
    let z := (1 / a + 1 / b + 1 / c) ^ 2
    apply cauchy_helper x y z (by positivity) h1

  have h2 : (1 / a + 1 / b + 1 / c) ^ 2 = (a * b + b * c + c * a) ^ 2 := by
    have ha' : 1 / a = b * c := by
      rw [← habc]; field_simp; ring
    have hb' : 1 / b = a * c := by
      rw [← habc]; field_simp; ring
    have hc' : 1 / c = a * b := (eq_one_div_of_mul_eq_one_left habc).symm
    rw [ha', hb', hc']
    ring

  have h3 : a * b + b * c + c * a ≥ 3 := by

    have amgm := Real.geom_mean_le_arith_mean3_weighted
      (show 0 ≤ 1 / 3 by norm_num)
      (show 0 ≤ 1 / 3 by norm_num)
      (show 0 ≤ 1 / 3 by norm_num)
      (show 0 ≤ a * b by positivity)
      (show 0 ≤ b * c by positivity)
      (show 0 ≤ c * a by positivity)
      (show 1 / 3 + 1 / 3 + 1 / 3 = 1 by norm_num)

    have exchange : a * b * (b * c) * (c * a) = a * b * c * (a * b * c) := by ring
    calc a * b + b * c + c * a
      _ = 3 * (1 / 3 * (a * b) + 1 / 3 * (b * c) + 1 / 3 * (c * a)) := by ring
      _ ≥ 3 * ((a * b) ^ (1 / 3:ℝ) * (b * c) ^ (1 / 3:ℝ) * (c * a) ^ (1 / 3:ℝ)) := by nlinarith only [amgm]
      _ = 3 * ((a * b * (b * c)) ^ (1 / 3:ℝ) * (c * a) ^ (1 / 3:ℝ)) := by rw [← Real.mul_rpow]; all_goals positivity
      _ = 3 * ((a * b * (b * c) * (c * a)) ^ (1 / 3:ℝ)) := by rw [← Real.mul_rpow]; all_goals positivity
      _ = 3 * (a * b * c * (a * b * c)) ^ (1 / 3:ℝ) := by rw [exchange]
      _ = 3 := by simp [habc]

  calc 1 / (a^3 * (b + c)) + 1 / (b^3 * (c + a)) + 1 / (c^3 * (a + b))
    _ ≥ (1 / a + 1 / b + 1 / c) ^ 2 / (a * (b + c) + b * (c + a) + c * (a + b)) := h1_div
    _ = (a * b + b * c + c * a) ^ 2 / (a * (b + c) + b * (c + a) + c * (a + b)) := by rw [h2]
    _ = (a * b + b * c + c * a) ^ 2 / (2 * (a * b + b * c + c * a)) := by field_simp; ring
    _ = 1 / 2 * (a * b + b * c + c * a) := by field_simp; ring
    _ ≥ 3 / 2 := by nlinarith only [h3]

end Imo1995P2
