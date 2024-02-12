/-
Copyright (c) 2024 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 1962, Problem 2

Determine all real numbers x which satisfy

  √(3 - x) - √(x + 1) > 1/2.
-/

namespace Imo1962P2

determine SolutionSet : Set ℝ := Set.Icc (-1) (1 - Real.sqrt (31 / 8))

problem imo1962_p2 (x : ℝ) :
    x ∈ SolutionSet ↔
    x ≤ 3 ∧ -1 ≤ x ∧ 1/2 < Real.sqrt (3 - x) - Real.sqrt (x + 1) := by
  -- https://prase.cz/kalva/imo/isoln/isoln622.html
  rw [Set.mem_Icc]
  constructor
  · rintro ⟨hx1, hx2⟩
    refine ⟨?_, hx1, ?_⟩
    · linarith only [hx2, Real.sqrt_nonneg (31 / 8)]
    · sorry
  rintro ⟨hx1, hx2, hx3⟩
  refine ⟨hx2, ?_⟩
  sorry
