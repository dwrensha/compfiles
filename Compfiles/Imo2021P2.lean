/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Olympiad 2021, Problem 2

Let n be a natural number, and let x₁, ..., xₙ be real numbers.
Show that

     ∑ᵢ∑ⱼ √|xᵢ - xⱼ| ≤ ∑ᵢ∑ⱼ √|xᵢ + xⱼ|.

-/

namespace Imo2021P2

open scoped BigOperators

problem imo2021_p2 (n : ℕ) (x : Fin n → ℝ) :
    ∑ i, ∑ j, Real.sqrt |x i - x j| ≤ ∑ i, ∑ j, Real.sqrt |x i + x j| := by
  sorry
