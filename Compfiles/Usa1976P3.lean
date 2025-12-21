/-
Copyright (c) 2025 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maximiliano Onofre Martínez
-/

import Mathlib.Data.Int.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# USA Mathematical Olympiad 1976, Problem 3

Determine all integral solutions of a² + b² + c² = a²b².
-/

namespace Usa1976P3

determine solution_set : Set (ℤ × ℤ × ℤ) := { ⟨0, 0, 0⟩ }

problem usa1976_p3 (a b c : ℤ) :
    a^2 + b^2 + c^2 = a^2 * b^2 ↔ ⟨a,b,c⟩ ∈ solution_set := sorry

end Usa1976P3
