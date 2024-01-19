/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 2015, Problem 5

Determine all functions f : ℝ → ℝ that satisfy

  f(x + f(x + y)) + f(xy) = x + f(x + y) + yf(x)

for all x,y.
-/

namespace Imo2012P5

determine solution_set : Set (ℝ → ℝ) := { fun x ↦ x, fun x ↦ 2 - x }

problem imo2015_p5 (f : ℝ → ℝ) :
    f ∈ solution_set ↔
    ∀ x y, f (x + f (x + y)) + f (x * y) = x + f (x + y) + y * f x := by
  -- https://web.evanchen.cc/exams/IMO-2015-notes.pdf
  constructor
  · rintro (rfl | rfl) x y <;> ring
  · intro hf
    let P x y := f (x + f (x + y)) + f (x * y) = x + f (x + y) + y * f x
    let S : Set ℝ := {t | f t = t}
    have h1 : f (f 0) = 0 := by
      have := hf 0 0
      simp only [add_zero, zero_add, mul_zero, zero_mul, add_left_eq_self] at this
      exact this
    sorry
