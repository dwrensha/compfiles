/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file {
  tags := [.Combinatorics]
}

/-!
# International Mathematical Olympiad 2020, Problem 3

There are 4n pebbles of weights 1,2,3,...,4n. Each pebble is colored
in one of n colors and there are four pebbles of each color. Show
that we can arrange the pebbles into two piles such that the total
weights of both piles are the same, and each pile contains two
pebbles of each color.
-/

namespace Imo2020P3

open scoped Finset

problem imo2020_p3 {n : ℕ} {c : Fin (4 * n) → Fin n} (h : ∀ i, #{j | c j = i} = 4) :
    ∃ S : Finset (Fin (4 * n)), ∑ i ∈ S, ((i : ℕ) + 1) = ∑ i ∈ Sᶜ, ((i : ℕ) + 1) ∧
      ∀ i, #{j ∈ S | c j = i} = 2 := by
  sorry

end Imo2020P3
