/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file

/-!
# International Mathematical Olympiad 2014, Problem 1

Let a₀ < a₁ < a₂ < ... an infinite sequence of positive integers.
Prove that there exists a unique integer n ≥ 1 such that

  aₙ < (a₀ + a₁ + ... + aₙ)/n ≤ aₙ₊₁.
-/

namespace Imo2014P1

open scoped BigOperators

problem imo2014_p1 (a : ℕ → ℤ) (apos : ∀ i, 0 < a i) (ha : ∀ i, a i < a (i + 1)) :
    ∃! n : ℕ, 0 < a ∧
              a n < (∑ i in Finset.range (n + 1), a i)/n ∧
              (∑ i in Finset.range (n + 1), a i)/n ≤ a (n + 1) := by
  sorry
