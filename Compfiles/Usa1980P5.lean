/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Goedel-Prover-V2
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra, .Inequality] }

/-!
# USA Mathematical Olympiad 1980, Problem 5

Let x,y,z be real numbers in the closed interval [0,1]. Show that

 x/(y + z + 1) + y/(z + x + 1) + z/(x + y + 1) ≤ 1 + (1 - x)(1 - y)(1 - z).
-/

namespace Usa1980P5

problem usa1980_p5 (x y z : ℝ)
    (hx : x ∈ Set.Icc 0 1)
    (hy : y ∈ Set.Icc 0 1)
    (hz : z ∈ Set.Icc 0 1) :
    x / (y + z + 1) + y / (z + x + 1) + z / (x + y + 1) ≤
    1 + (1 - x) * (1 - y) * (1 - z) := by
  have h_nonneg : (1 - x) * (1 - y) * (1 - z) ≥ 0 := by
    have hx' : 0 ≤ x ∧ x ≤ 1 := hx
    have hy' : 0 ≤ y ∧ y ≤ 1 := hy
    have hz' : 0 ≤ z ∧ z ≤ 1 := hz
    have h₁ : 0 ≤ 1 - x := by linarith
    have h₂ : 0 ≤ 1 - y := by linarith
    have h₃ : 0 ≤ 1 - z := by linarith
    have h₄ : 0 ≤ (1 - x) * (1 - y) := by positivity
    exact Left.mul_nonneg h₄ h₃
  have h_sum_le_one : x / (y + z + 1) + y / (z + x + 1) + z / (x + y + 1) ≤ 1 := by
    have hx' : 0 ≤ x ∧ x ≤ 1 := hx
    have hy' : 0 ≤ y ∧ y ≤ 1 := hy
    have hz' : 0 ≤ z ∧ z ≤ 1 := hz
    have h₁ : 0 ≤ x := by linarith
    have h₂ : 0 ≤ y := by linarith
    have h₃ : 0 ≤ z := by linarith
    by_cases h₄ : (x + y + z : ℝ) = 0
    · have h₅ : x = 0 := by linarith
      have h₆ : y = 0 := by linarith
      have h₇ : z = 0 := by linarith
      rw [h₅, h₆, h₇]
      norm_num
    · have h₅ : 0 < x + y + z := by
        by_contra h
        have h₆ : x + y + z ≤ 0 := by linarith
        have h₇ : x + y + z = 0 := by linarith
        contradiction
      have h₆ : x / (y + z + 1) ≤ x / (x + y + z) := by
        have h₇ : 0 ≤ x := by linarith
        have h₈ : 0 < y + z + 1 := by linarith
        have h₉ : 0 < x + y + z := by linarith
        have h₁₀ : x + y + z ≤ y + z + 1 := by
          nlinarith [hx'.2, hy'.2, hz'.2]
        gcongr
      have h₇ : y / (z + x + 1) ≤ y / (x + y + z) := by
        have h₈ : 0 ≤ y := by linarith
        have h₉ : 0 < z + x + 1 := by linarith
        have h₁₀ : 0 < x + y + z := by linarith
        have h₁₁ : x + y + z ≤ z + x + 1 := by
          nlinarith [hx'.2, hy'.2, hz'.2]
        gcongr
      have h₈ : z / (x + y + 1) ≤ z / (x + y + z) := by
        have h₉ : 0 ≤ z := by linarith
        have h₁₀ : 0 < x + y + 1 := by linarith
        have h₁₁ : 0 < x + y + z := by linarith
        have h₁₂ : x + y + z ≤ x + y + 1 := by linarith [hx'.2, hy'.2, hz'.2]
        gcongr
      have h₉ : x / (y + z + 1) + y / (z + x + 1) + z / (x + y + 1) ≤ x / (x + y + z) + y / (x + y + z) + z / (x + y + z) := by
        linarith
      have h₁₀ : x / (x + y + z) + y / (x + y + z) + z / (x + y + z) = 1 := by
        have h₁₁ : x / (x + y + z) + y / (x + y + z) + z / (x + y + z) = (x + y + z) / (x + y + z) := by
          field_simp [h₅.ne']
        rw [h₁₁]
        exact (div_eq_one_iff_eq h₄).mpr rfl
      linarith
  exact le_add_of_le_of_nonneg h_sum_le_one h_nonneg

end Usa1980P5
