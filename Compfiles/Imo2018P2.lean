/-
Copyright (c) 2023 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 2018, Problem 2

Determine all integers n ≥ 3 such that there exist real numbers
a₁, a₂, ..., aₙ satisfying

  aᵢaᵢ₊₁ + 1 = aᵢ₊₂,

where the indices are taken mod n.
-/

namespace Imo2018P2

determine solution_set : Set ℕ := { n | 3 ≤ n ∧ 3 ∣ n }

problem imo2018_p2 (n : ℕ) :
    n ∈ solution_set ↔
      3 ≤ n ∧
      ∃ a : ZMod n → ℝ,
        a 0 = a n ∧
        a 1 = a (n + 1) ∧
        ∀ i, a i * a (i + 1) + 1 = a (i + 2) := by
  constructor
  · rintro ⟨hn1, hn2⟩
    refine ⟨hn1, ?_⟩
    sorry
  · sorry


end Imo2018P2
