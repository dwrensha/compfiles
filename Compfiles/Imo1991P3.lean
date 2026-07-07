/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Combinatorics, .NumberTheory] }

/-!
# International Mathematical Olympiad 1991, Problem 3

Let S = {1, 2, ..., 280}. Find the smallest natural number n such
that every n-element subset of S contains five numbers which are
pairwise relatively prime.
-/

namespace Imo1991P3

determine solution : ℕ := sorry

problem imo1991_p3 :
    IsLeast
      {n : ℕ | ∀ T ⊆ Finset.Icc 1 280, T.card = n →
        ∃ U ⊆ T, U.card = 5 ∧ (U : Set ℕ).Pairwise Nat.Coprime}
      solution := by
  sorry

end Imo1991P3
