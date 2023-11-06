/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file

/-!
# International Mathematical Olympiad 1990, Problem 3

Find all integers n > 1 such that n² divides 2ⁿ + 1.
-/

namespace Imo1990P3

determine solution_set : Set ℕ := { 3 }

problem imo1990_p3 (n : ℕ) (hn : 1 < n) : n ∈ solution_set ↔ n^2 ∣ 2^n + 1 := by
  constructor
  · intro hs
    rw [Set.mem_singleton_iff] at hs
    rw [hs]
    norm_num
  · intro hnd
    sorry
