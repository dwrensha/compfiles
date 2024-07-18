/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 2024, Problem 1

Determine all real numbers α such that, for every positive integer n, the
integer

     ⌊α⌋ + ⌊2α⌋ + ... + ⌊nα⌋

is a multiple of n.
-/

namespace Imo2024P1

determine SolutionSet : Set ℝ := sorry

problem imo2024_p1 (α : ℝ) :
    α ∈ SolutionSet ↔
    ∀ n : ℕ, (n : ℤ) ∣ ∑ i ∈ Finset.range n, ⌊i * α⌋ := by
  sorry

end Imo2024P1
