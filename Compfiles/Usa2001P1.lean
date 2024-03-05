/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Data.Finset.Card
import Mathlib.Order.Bounds.Basic
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 2001, Problem 1

Each of eight boxes contains six balls.
Each ball has been colored with one of n colors, such that no two balls
in the same box are the same color, and no two colors occur together in
more than one box. Determine, with justification, the smallest integer n
for which this is possible.
-/

namespace Usa2001P1

def possible_num_colors : Set ℕ :=
{ n : ℕ | ∃ f : Fin 8 → Finset (Fin n),
    (∀ i, (f i).card = 6) ∧
    (∀ x y : Fin n, ∀ i j : Fin 8,
      i ≠ j → x ∈ f i → y ∈ f i →
        (¬ (x ∈ f j ∧ y ∈ f j))) }

determine min_colors : ℕ := 23

problem usa2001_p1 : IsLeast possible_num_colors min_colors := by
  -- Informal solution from
  -- https://artofproblemsolving.com/wiki/index.php/2001_USAMO_Problems/Problem_1
  constructor
  · rw [Set.mem_def, possible_num_colors, Set.setOf_app_iff]
    let f : Fin 8 → Finset (Fin 23)
        | 0 => {1, 2, 3, 4, 5, 6}
        | 1 => {1, 7, 8, 9, 10, 11}
        | 2 => {1, 12, 13, 14, 15, 16}
        | 3 => {2, 7, 12, 17, 18, 19}
        | 4 => {3, 8, 13, 17, 20, 21}
        | 5 => {4, 9, 14, 17, 22, 23}
        | 6 => {5, 10, 15, 18, 20, 22}
        | 7 => {6, 11, 16, 19, 21, 23}
    use f
    constructor
    · intro i
      fin_cases i <;> simp (config := {decide := true}) [f]
    · intro x y i j hij hx hy
      sorry
  · sorry
