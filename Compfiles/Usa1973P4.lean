/-
Copyright (c) 2025 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shalev Wengrowsky
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Tactic.LinearCombination

public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Algebra] }

/-!
# USA Mathematical Olympiad 1973, Problem 4

Find all complex numbers x, y, z which satisfy
  x + y + z = x² + y² + z² = x³ + y³ + z³ = 3.
-/

namespace Usa1973P4

determine solution_set : Set (ℂ × ℂ × ℂ) := { ⟨1, 1, 1⟩ }

problem usa1973_p4 (x y z : ℂ) :
    x + y + z = 3 ∧
    x ^ 2 + y ^ 2 + z ^ 2 = 3 ∧
    x ^ 3 + y ^ 3 + z ^ 3 = 3 ↔ ⟨x,y,z⟩ ∈ solution_set := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    have e2 : x*y + y*z + z*x = 3 := by
      linear_combination (1/2 : ℂ) * ((x+y+z+3) * h1 - h2)
    have e3 : x*y*z = 1 := by
      linear_combination (1/3 : ℂ) * (h3 - (x^2+y^2+z^2 - (x*y+y*z+z*x)) * h1 - 3 * h2 + 3 * e2)
    have key : ∀ t, t = x ∨ t = y ∨ t = z → t = 1 := by
      rintro t ht
      have : (t - 1)^3 = 0 := by
        rcases ht with rfl | rfl | rfl
        · linear_combination t^2 * h1 - t * e2 + e3
        · linear_combination t^2 * h1 - t * e2 + e3
        · linear_combination t^2 * h1 - t * e2 + e3
      exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp this)
    simp [solution_set, key x (by simp), key y (by simp), key z (by simp)]
  rintro _
  grind

end Usa1973P4
