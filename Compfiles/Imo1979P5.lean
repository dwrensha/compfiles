/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InternLM-MATH LEAN Formalizer v0.1. This is auto-formalized by InternLM-MATH LEAN Formalizer v0.1, modified and verified by InternLM-MATH team members.
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 1979, Problem 5

Find all real numbers a for which there exist non-negative real numbers x1, x2, x3, x4, x5 satisfying:

x1 + 2x2 + 3x3 + 4x4 + 5x5 = a,  
  x1 + 23x2 + 33x3 + 43x4 + 53x5 = a2,  
  x1 + 25x2 + 35x3 + 45x4 + 55x5 = a3.
-/

namespace Imo1979P5

problem imo1979_p5 (a : ℝ) : (∃ x1 x2 x3 x4 x5 : ℝ, x1 ≥ 0 ∧ x2 ≥ 0 ∧ x3 ≥ 0 ∧ x4 ≥ 0 ∧ x5 ≥ 0 ∧ x1 + 2*x2 + 3*x3 + 4*x4 + 5*x5 = a ∧ x1 + 2^3*x2 + 3^3*x3 + 4^3*x4 + 5^3*x5 = a^2 ∧ x1 + 2^5*x2 + 3^5*x3 + 4^5*x4 + 5^5*x5 = a^3 ) ↔ a = 0 ∨ a = 1 ∨ a = 4 ∨ a = 9 ∨ a = 16 ∨ a = 25 := by sorry