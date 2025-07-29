/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 1963, Problem 4

Find all solutions x₁,x₂,x₃,x₄,x₅ of the system

  x₅ + x₂ = yx₁
  x₁ + x₃ = yx₂
  x₂ + x₄ = yx₃
  x₃ + x₅ = yx₄
  x₄ + x₁ = yx₅

where y is a parameter.
-/

namespace Imo1963P4

determine SolutionSet (y : ℝ) : Set (ℝ × ℝ × ℝ × ℝ × ℝ) :=
 {(x₁, x₂, x₃, x₄, x₅) |
  (x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0 ∧ x₄ = 0 ∧ x₅ = 0) ∨
  (x₁ = x₂ ∧ x₂ = x₃ ∧ x₃ = x₄ ∧ x₄ = x₅ ∧ y = 2) ∨
  (y^2 + y - 1 = 0 ∧ ∃ s t,
    x₁ = s ∧
    x₂ = t ∧
    x₃ = y * t - s ∧
    x₄ = -(y * t) - y * s ∧
    x₅ = y * s - t)}

problem imo1963_p4 (x₁ x₂ x₃ x₄ x₅ y : ℝ) :
    (x₁, x₂, x₃, x₄, x₅) ∈ SolutionSet y ↔
    (x₅ + x₂ = y * x₁ ∧
     x₁ + x₃ = y * x₂ ∧
     x₂ + x₄ = y * x₃ ∧
     x₃ + x₅ = y * x₄ ∧
     x₄ + x₁ = y * x₅) := by
  constructor
  · intro h
    rcases h with h₀ | h₁
    · obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h₀
      ring_nf; trivial
    rcases h₁ with heq | h₂
    · obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := heq
      ring_nf; trivial
    rcases h₂ with ⟨hy, hst⟩
    rcases hst with ⟨s, ⟨t, h⟩⟩
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
    have h' : y^2 = 1 - y := by linarith
    ring_nf
    refine ⟨trivial, trivial, ?_, ?_, ?_⟩ <;> rw [h'] <;> ring

  intro h
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := h
  by_cases hy : y ≠ 2
  · have hx₃ : x₃ = y * x₂ - x₁ := by linarith
    have hx₄ : x₄ = y * x₃ - x₂ := by linarith
    have hx₅ : x₅ = y * x₁ - x₂ := by linarith
    have hxy₁ : (y^2 + y - 1) * (x₂ - x₁) = 0 := by
      rw [hx₃] at hx₄
      rw [hx₄, hx₅] at h₅
      linarith
    have hx₄' : x₄ = (y^2 - 1) * x₂ - y * x₁ := by
      have h' : y * (y * x₂ - x₁) - x₂ = (y^2 - 1) * x₂ - y * x₁ := by ring
      rwa [hx₃, h'] at hx₄
    have hxy₂ : (y^2 + y - 1) * ((y-1) * x₂ - x₁) = 0 := by
      have : (y * x₂ - x₁) + (y * x₁ - x₂) = y * ((y^2 - 1) * x₂ - y * x₁) := by
        rwa [<- hx₃, <- hx₅, <- hx₄']
      linarith

    by_cases hy' : y^2 + y - 1 ≠ 0
    · sorry
    simp at hy'
    have h' : y^2 = 1 - y := by linarith
    simp [h'] at hx₄'
    right; right
    exact ⟨by assumption, by use x₁, x₂⟩

  simp at hy
  rw [hy] at h₁ h₂ h₃ h₄ h₅
  have h₆ : x₅ + x₂ = x₃ + x₄ := by linarith
  have h₇ : x₃ + x₄ + (x₅ + x₂) + x₁ = 5 * x₁ := by rw [<- h₆, h₁]; ring
  right; left; refine ⟨?_, ?_, ?_, ?_, hy⟩ <;> linarith

end Imo1963P4
