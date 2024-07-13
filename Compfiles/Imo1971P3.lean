/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InternLM-MATH LEAN Formalizer v0.1
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Olympiad 1971, Problem 3

Prove that we can find an infinite set of positive integers of the form 2^n - 3
(where n is a positive integer) every pair of which are relatively prime.
-/

namespace Imo1971P3

problem imo1971_p3 : Set.Infinite
  {(n, m) : ℕ × ℕ | Nat.Coprime (2 ^ n - 3) (2 ^ m - 3)} := by sorry


end Imo1971P3
