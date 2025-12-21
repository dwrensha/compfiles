/-
Copyright (c) 2025 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shalev Wengrowsky
-/

import Mathlib.Data.Complex.Basic

import ProblemExtraction

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
  · intro
    ext <;> grind
  rintro _
  grind

end Usa1973P4
