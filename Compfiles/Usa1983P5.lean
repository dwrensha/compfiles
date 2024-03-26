/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib.Data.Set.Card
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# USA Mathematical Olympiad 1983, Problem 5

Consider an open interval of length 1/2 on the real number line, where
n is a positive integer. Prove that the number of irreducible fractions
p/q, with 1 ≤ q ≤ n, contained in the given interval is at most (n + 1) / 2.
-/

namespace Usa1983P5

problem usa1983_p5 (x : ℝ) (n : ℕ) (hn : 0 < n) :
    let fracs := { q : ℚ | q.den ≤ n ∧ ↑q ∈ Set.Ioo x (x + 1 / n)}
    fracs.Finite ∧ fracs.ncard ≤ (n + 1) / 2 := by
  sorry
