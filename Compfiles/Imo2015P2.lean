/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Olympiad 2015, Problem 2

Determine all triples of positive integers a, b, c such that each of
ab - c, bc - a, ca - b is a power of two.
-/

namespace Imo2012P2

determine solution_set : Set (ℤ × ℤ × ℤ) := sorry

def is_power_of_two (n : ℤ) : Prop := ∃ m : ℕ, n = 2 ^ m

problem imo2015_p2 (a b c : ℤ) :
    (a,b,c) ∈ solution_set ↔
      0 < a ∧ 0 < b ∧ 0 < c ∧
      is_power_of_two (a * b - c) ∧
      is_power_of_two (b * c - a) ∧
      is_power_of_two (c * a - b) := by
  sorry
