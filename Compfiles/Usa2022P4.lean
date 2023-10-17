/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import Compfiles.Meta.ProblemExtraction

problem_file

/-!
# USA Mathematical Olympiad 2022, Problem 4

Determine all pairs of primes (p, q) where p - q and pq - q are both perfect squares.
-/

namespace Usa2022P4

determine solution_set : Set (ℕ × ℕ) := sorry

problem usa2022_p4 (p q : ℕ) :
    (p, q) ∈ solution_set ↔
    p.Prime ∧ q.Prime ∧
    ∃ n, n^2 + q = p ∧ ∃ m, m^2 + q = p * q := by
  -- https://web.evanchen.cc/exams/USAMO-2022-notes.pdf
  sorry
