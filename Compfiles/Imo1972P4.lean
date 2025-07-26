/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InternLM-MATH LEAN Formalizer v0.1, Maximiliano Onofre-Martínez
-/

import Mathlib.Tactic
import Mathlib.Algebra.GroupWithZero.Basic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 1972, Problem 4

Find all positive real solutions to:

(x_1^2 - x_3x_5)(x_2^2 - x_3x_5) ≤ 0
(x_2^2 - x_4x_1)(x_3^2 - x_4x_1) ≤ 0
(x_3^2 - x_5x_2)(x_4^2 - x_5x_2) ≤ 0
(x_4^2 - x_1x_3)(x_5^2 - x_1x_3) ≤ 0
(x_5^2 - x_2x_4)(x_1^2 - x_2x_4) ≤ 0
-/

namespace Imo1972P4

determine solution_set : Set (ℝ × ℝ × ℝ × ℝ × ℝ) :=
  {(a, b, c, d, e) | a = b ∧ b = c ∧ c = d ∧ d = e}

problem imo1972_p4 (a b c d e : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ 0 < e):
    (a^2 - c * e) * (b^2 - c * e) ≤ 0 ∧
    (b^2 - d * a) * (c^2 - d * a) ≤ 0 ∧
    (c^2 - e * b) * (d^2 - e * b) ≤ 0 ∧
    (d^2 - a * c) * (e^2 - a * c) ≤ 0 ∧
    (e^2 - b * d) * (a^2 - b * d) ≤ 0 ↔
      (a, b, c, d, e) ∈ solution_set := by
  constructor
  · intro _
    have : (a * b - a * d)^2 + (b * c - b * e)^2 +
           (c * d - c * a)^2 + (d * e - d * b)^2 +
           (e * a - e * c)^2 + (a * c - a * e)^2 +
           (b * d - b * a)^2 + (c * e - c * b)^2 +
           (d * a - d * c)^2 + (e * b - e * d)^2 ≤ 0 := by linarith

    have : 0 ≤ (a * b - a * d)^2 ∧ 0 ≤ (b * c - b * e)^2 ∧
           0 ≤ (c * d - c * a)^2 ∧ 0 ≤ (d * e - d * b)^2 ∧
           0 ≤ (e * a - e * c)^2 ∧ 0 ≤ (a * c - a * e)^2 ∧
           0 ≤ (b * d - b * a)^2 ∧ 0 ≤ (c * e - c * b)^2 ∧
           0 ≤ (d * a - d * c)^2 ∧ 0 ≤ (e * b - e * d)^2 := by simp [sq_nonneg]

    have bd : b = d := by
      have h₁ : (a * b - a * d)^2 = 0 := by linarith
      have h₂ : a * b - a * d = 0 := by rwa [sq_eq_zero_iff] at h₁
      have h₃ : a * b = a * d := by rwa [sub_eq_zero] at h₂
      exact mul_left_cancel₀ (ne_of_gt h₀.1) h₃

    have ce : c = e := by
      have h₁ : (b * c - b * e)^2 = 0 := by linarith
      have h₂ : b * c - b * e = 0 := by rwa [sq_eq_zero_iff] at h₁
      have h₃ : b * c = b * e := by rwa [sub_eq_zero] at h₂
      exact mul_left_cancel₀ (ne_of_gt h₀.2.1) h₃

    have da : d = a := by
      have h₁ : (c * d - c * a)^2 = 0 := by linarith
      have h₂ : c * d - c * a = 0 := by rwa [sq_eq_zero_iff] at h₁
      have h₃ : c * d = c * a := by rwa [sub_eq_zero] at h₂
      exact mul_left_cancel₀ (ne_of_gt h₀.2.2.1) h₃

    have eb : e = b := by
      have h₁ : (d * e - d * b)^2 = 0 := by linarith
      have h₂ : d * e - d * b = 0 := by rwa [sq_eq_zero_iff] at h₁
      have h₃ : d * e = d * b := by rwa [sub_eq_zero] at h₂
      exact mul_left_cancel₀ (ne_of_gt h₀.2.2.2.1) h₃

    have ab : a = b := by rw [<- da]; exact bd.symm
    have bc : b = c := by rw [<- eb]; exact ce.symm
    have cd : c = d := by rwa [<- bc]
    have de : d = e := by rwa [cd] at ce
    exact ⟨ab, bc, cd, de⟩
  · intro h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    ring_nf; trivial

end Imo1972P4
