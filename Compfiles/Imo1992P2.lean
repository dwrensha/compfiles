/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 1992, Problem 2

Determine all functions f : ℝ → ℝ such that
for all x,y ∈ ℝ, f(x² + f(y)) = y + (f(x))².
-/

namespace Imo1992P2

determine solution_set : Set (ℝ → ℝ) := { fun x ↦ x }

problem imo1992_p2 (f : ℝ → ℝ) :
    f ∈ solution_set ↔
    ∀ x y, f (x^2 + f y) = y + (f x)^2 := by
  -- https://prase.cz/kalva/imo/isoln/isoln922.html
  constructor
  · rintro rfl x y; dsimp only; ac_rfl
  intro hf
  have h1 : f 0 = 0 := by
    have h0 := hf 0 0
    simp only [zero_pow two_ne_zero, zero_add] at h0
    let t := f 0
    have ht1 : f t = t^2 := h0
    have ht2 : ∀ x, f (x^2 + t) = (f x)^2 := fun x ↦ by
      have hf1 := hf x 0; rw [zero_add] at hf1
      exact hf1
    have ht3 : ∀ x, f (f x) = x + t^2 := fun x ↦ by
      have hf1 := hf 0 x
      simp only [zero_pow two_ne_zero, zero_add] at hf1
      exact hf1
    sorry
  sorry
