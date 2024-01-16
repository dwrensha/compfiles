/-
Copyright (c) 2024 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file

/-!
# USA Mathematical Olympiad 2017, Problem 5

Determine the set of positive real numbers c such that there exists
a labeling of the lattice points in ℤ² with positive integers for which:

  1. only finitely many distinct labels occur, and
  2. for each label i, the distance between any two points labeled i
     is at most cⁱ.
-/

namespace Usa2017P5

determine solution_set : Set ℝ := sorry

noncomputable def dist : ℤ × ℤ → ℤ × ℤ → ℝ
| ⟨x1, y1⟩, ⟨x2, y2⟩ => Real.sqrt ((x2 - x1)^2 + (y2 - y1)^2)

problem usa2017_p5 (c : ℝ) :
    c ∈ solution_set ↔
    (0 < c ∧
     ∃ l : ℤ × ℤ → ℕ,
       (Set.range l).Finite ∧
       (∀ p, 0 < l p) ∧
       ∀ {p1 p2}, p1 ≠ p2 → (l p1 = l p2) →
            dist (l p1) (l p2) ≤ c ^ (l p1)) := by
  sorry
