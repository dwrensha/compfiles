/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 2020, Problem 5

A deck of n > 1 cards is given. A positive integer is written on
each card. The deck has the property that the arithmetic mean of
the numbers on each pair of cards is also the geometric mean of
the numbers on some collection of one or more cards.

For which n does it follow that the numbers on the cards are all equal?
-/

namespace Imo2020P5

open scoped BigOperators

determine SolutionSet : Set ℕ := sorry

noncomputable def geometric_mean {α : Type} (f : α → ℕ+) (s : Finset α) : ℝ :=
  (∏ i ∈ s, (f i : ℝ))^((1:ℝ)/s.card)

problem imo2020_p5 (n : ℕ) :
    n ∈ SolutionSet ↔
    (1 < n ∧
     (∀ α : Type, [Fintype α] → Fintype.card α = n →
         ∀ f : α → ℕ+,
           (∀ a b, ∃ s : Finset α,
              geometric_mean f s = (((f a):ℝ) + f b) / 2)
           → ∃ y, ∀ a, f a = y )) := by
  sorry
