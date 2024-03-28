/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# USA Mathematical Olympiad 2008, Problem 1

Prove that for each positive integer n, there are pairwise relatively prime
integers k₀,k₁,...,kₙ, all strictly greater than 1, such that k₀k₁...kₙ - 1
is a product of two consecutive integers.
-/

namespace Usa2008P1

open scoped BigOperators

problem usa2008_p1 (n : ℕ) (hn : 0 < n) :
    ∃ k : Fin (n + 1) → ℕ,
      (∀ i, 1 < k i) ∧
      ∃ m, ∏ i : Fin (n + 1), k i = 1 + m * (m + 1) := by
  sorry
