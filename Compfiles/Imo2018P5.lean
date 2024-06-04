/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Olympiad 2018, Problem 5

Let a₁, a₂, ... be an infinite sequence of positive integers.
Suppose that there is an integer N > 1 such that for each n ≥ N
the number

   a₁/a₂ + a₂/a₃ ... + aₙ₋₁/aₙ + aₙ/a₁

is an integer. Prove that there is a positive integer M such that
aₘ = aₘ₊₁ for all m ≥ M.
-/

namespace Imo2018P5

problem imo2018_p5
    (a : ℕ → ℤ)
    (apos : ∀ n, 0 < a n)
    (N : ℕ)
    (hN : 0 < N)
    (h : ∀ n, N ≤ n →
      ∃ z : ℤ,
        z = ∑ i in Finset.range n, (a i : ℚ) / a ((i + 1) % n))
    : ∃ M, ∀ m, M ≤ m → a m = a (m + 1) := by
  sorry
