/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib.Data.Set.Card
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Olympiad 2016, Problem 4

A set of positive integers is called *fragrant* if it contains
at least two elements and each of its elements has a prime
factor in common with at least one of the other elements.
Let P(n) = n² + n + 1. What is the least possible value of
positive integer b such that there exists a non-negative integer
a for which the set

  { P(a + 1), P(a + 2), ..., P(a + b) }

is fragrant?
-/

namespace Imo2016P4

abbrev Fragrant (s : Set ℕ+) : Prop :=
  2 ≤ s.ncard ∧ ∀ m ∈ s, ∃ n ∈ s, ¬Nat.Coprime m n

abbrev P (n : ℕ) : ℕ := n^2 + n + 1

determine Solution : ℕ+ := sorry

problem imo2016_p4 :
    IsLeast
      {b : ℕ+ | ∃ a : ℕ, Fragrant {p | ∃ i < b, p = P (a + 1 + i)}}
      Solution := by
  sorry


end Imo2016P4
