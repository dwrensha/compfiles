/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Olympiad 1999, Problem 4

Determine all pairs of positive integers (x,p) such that p is
a prime and xᵖ⁻¹ is a divisor of (p-1)ˣ + 1.
-/

namespace Imo1999P4

determine SolutionSet : Set (ℕ × ℕ) := sorry

problem imo1999_p4 (x p : ℕ) :
    ⟨x,p⟩ ∈ SolutionSet ↔
    0 < x ∧ p.Prime ∧ x^(p - 1) ∣ (p - 1)^x + 1 := by
  sorry


end Imo1999P4
