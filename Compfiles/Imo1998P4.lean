/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InternLM-MATH LEAN Formalizer v0.1
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Olympiad 1998, Problem 4

Determine all pairs (a, b) of positive integers such that ab^2 + b + 7 divides a^2b + a + b.
-/

namespace Imo1998P4

determine solution_set : Set (ℕ × ℕ) := {(11, 1), (49, 1)} ∪ {(x,y) | ∃ k : ℕ , (x = 7 * k^2 ∧ y = 7 * k)}

problem imo1998_p4 (a b : ℕ) : a * b^2 + b + 7 ∣ a^2 * b + a + b ↔ (a, b) ∈ solution_set := by sorry
