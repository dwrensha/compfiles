/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 1996, Problem 3

Let S denote the set of nonnegative integers. Find
all functions f from S to itself such that

 f(m + f(n)) = f(f(m)) + f(n)

for all m,n in S.
-/

namespace Imo1996P3

determine SolutionSet : Set (ℕ → ℕ) := sorry

problem imo1996_p3 (f : ℕ → ℕ) :
    f ∈ SolutionSet ↔ ∀ m n, f (m + f n) = f (f m) + f n := by
  sorry
