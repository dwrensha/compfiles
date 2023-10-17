/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Positive.Field
import Mathlib.Tactic

import Compfiles.Meta.ProblemExtraction

problem_file

/-!
# International Mathematical Olympiad 2022, Problem 2

Let ℝ+ be the set of positive real numbers.
Determine all functions f: ℝ+ → ℝ+ such that
for each x ∈ ℝ+, there is exactly one y ∈ ℝ+
satisfying

  x·f(y) + y·f(x) ≤ 2
-/

namespace Imo2022P2

abbrev PosReal : Type := { x : ℝ // 0 < x }

notation "ℝ+" => PosReal

determine solution_set : Set (ℝ+ → ℝ+) := { fun x ↦ 1 / x }

problem imo2022_p2 (f : ℝ+ → ℝ+) :
    f ∈ solution_set ↔
    ∀ x, ∃! y, x * f y + y * f x ≤ ⟨2, two_pos⟩ := by
  constructor
  · intro hf
    simp only [Set.mem_singleton_iff] at hf
    intro x
    use x
    constructor
    · simp [hf]
      suffices h : (1:ℝ+) + 1 = ⟨2, two_pos⟩ by exact Eq.le h
      norm_num [Subtype.ext_iff]
    · intro y hy
      rw [hf] at hy
      sorry
  · sorry
