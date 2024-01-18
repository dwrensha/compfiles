/-
Copyright (c) 2024 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# Iberoamerican Interuniversity Mathematics Competition 2022, Problem 6

Given a positive integer m, let d(m) be the number of postive
divisors of m. Show that for every positive integer n, one
has
       d((n + 1)!) ≤ 2d(n!).
-/

namespace CIIM2022P6

def d : ℕ → ℕ
| m => (Nat.divisors m).card

problem ciim2022_p6 (n : ℕ) (hn : 0 < n) :
    d (Nat.factorial (n + 1)) ≤ 2 * d (Nat.factorial n) := by
  sorry
