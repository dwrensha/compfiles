/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file

/-!
# International Mathematical Olympiad 2016, Problem 5

The equation

  (x - 1)(x - 2) ... (x - 2016)  = (x - 1)(x - 2) ... (x - 2016)

is written on the board. What is the least possible value of k
for which it is possible to erase exactly k of these 4032 factors
such that at least one factor remains on each side and the resulting
equation has no real solutions?
-/

namespace Imo2016P5

open scoped BigOperators

determine solution_value : ℕ := 2016

problem imo2015_p5 :
    IsLeast { k | ∃ L R : Finset ℕ,
                  L ⊂ Finset.Icc 1 2016 ∧
                  R ⊂ Finset.Icc 1 2016 ∧
                  R.card + L.card = k ∧
                  ¬∃ x : ℝ,
                   ∏ i in Finset.Icc 1 2016, (if i ∈ L then 1 else (x - (i : ℝ))) =
                   ∏ i in Finset.Icc 1 2016, (if i ∈ R then 1 else (x - (i : ℝ))) }
            solution_value := by
  constructor
  · rw [Set.mem_setOf_eq]
    sorry
  · rw [mem_lowerBounds]
    intro j hj
    by_contra' H
    sorry

