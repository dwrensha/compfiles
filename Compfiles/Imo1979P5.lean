/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InternLM-MATH LEAN Formalizer v0.1, Maximiliano Onofre-Martínez
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 1979, Problem 5

Find all real numbers a for which there exist
non-negative real numbers x1, x2, x3, x4, x5 satisfying:

x1 + 2x_2 + 3x_3 + 4x_4 + 5x_5 = a,
x1 + 2^3x_2 + 3^3x_3 + 4^3x_4 + 5^3x_5 = a^2,
x1 + 2^5x_2 + 3^5x_3 + 4^5x_4 + 5^5x_5 = a^3.
-/

namespace Imo1979P5

determine solution_set : Set ℝ := {0, 1, 4, 9, 16, 25}

problem imo1979_p5 (a : ℝ) :
  (∃ x1 x2 x3 x4 x5 : ℝ,
    x1 ≥ 0 ∧ x2 ≥ 0 ∧ x3 ≥ 0 ∧ x4 ≥ 0 ∧ x5 ≥ 0 ∧
    x1 + 2*x2 + 3*x3 + 4*x4 + 5*x5 = a ∧
    x1 + 2^3*x2 + 3^3*x3 + 4^3*x4 + 5^3*x5 = a^2 ∧
    x1 + 2^5*x2 + 3^5*x3 + 4^5*x4 + 5^5*x5 = a^3 ) ↔ a ∈ solution_set := by
  constructor
  · rintro ⟨x1, x2, x3, x4, x5, hx1, hx2, hx3, hx4, hx5, h₁, h₂, h₃⟩
    have h₀ :
      (a - 1)^2 * x1 + 2*(a - 4)^2 * x2 +
      3*(a - 9)^2 * x3 + 4*(a - 16)^2 * x4 +
      5*(a - 25)^2 * x5 = 0 := by
        linear_combination a^2 * h₁ + h₃ - 2 * a * h₂

    have t1 : 0 ≤ (a - 1)^2 * x1 := by positivity
    have t2 : 0 ≤ 2 * (a - 4)^2 * x2 := by positivity
    have t3 : 0 ≤ 3 * (a - 9)^2 * x3 := by positivity
    have t4 : 0 ≤ 4 * (a - 16)^2 * x4 := by positivity
    have t5 : 0 ≤ 5 * (a - 25)^2 * x5 := by positivity

    have h1 : (a + -1)^2 * x1 = 0 := by linarith
    have h2 : (a + -4)^2 * x2 = 0 := by linarith
    have h3 : (a + -9)^2 * x3 = 0 := by linarith
    have h4 : (a + -16)^2 * x4 = 0 := by linarith
    have h5 : (a + -25)^2 * x5 = 0 := by linarith
    rw [mul_eq_zero] at h1 h2 h3 h4 h5

    rcases h1 with h1 | h1
    · simp at h1; rw [add_neg_eq_zero] at h1
      exact Or.inr (Or.inl h1)
    rcases h2 with h2 | h2
    · simp at h2; rw [add_neg_eq_zero] at h2
      exact Or.inr (Or.inr (Or.inl h2))
    rcases h3 with h3 | h3
    · simp at h3; rw [add_neg_eq_zero] at h3
      exact Or.inr (Or.inr (Or.inr (Or.inl h3)))
    rcases h4 with h4 | h4
    · simp at h4; rw [add_neg_eq_zero] at h4
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h4))))
    rcases h5 with h5 | h5
    · simp at h5; rw [add_neg_eq_zero] at h5
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h5))))
    simp [h1, h2, h3, h4, h5] at h₁
    exact Or.inl (h₁.symm)

  intro h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl
  · use 0, 0, 0, 0, 0; norm_num
  · use 1, 0, 0, 0, 0; norm_num
  · use 0, 2, 0, 0, 0; norm_num
  · use 0, 0, 3, 0, 0; norm_num
  · use 0, 0, 0, 4, 0; norm_num
  · use 0, 0, 0, 0, 5; norm_num

end Imo1979P5
