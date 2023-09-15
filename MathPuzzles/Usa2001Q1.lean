/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Data.Finset.Card
import Mathlib.Order.Bounds.Basic

import MathPuzzles.Meta.Attributes

#[problem_setup]/-!
# USA Mathematical Olympiad 2001, Problem 1

Each of eight boxes contains six balls.
Each ball has been colored with one of n colors, such that no two balls
in the same box are the same color, and no two colors occur together in
more than one box. Determine, with justification, the smallest integer n
for which this is possible.
-/

#[problem_setup] namespace Usa2001Q1

#[problem_setup]
def possible_num_colors : Set ℕ :=
{ n : ℕ | ∃ f : Fin 8 → Finset (Fin n),
    (∀ i, (f i).card = 6) ∧
    (∀ x y : Fin n, ∀ i j : Fin 8,
      i ≠ j → x ∈ f i → y ∈ f i →
        (¬ (x ∈ f j ∧ y ∈ f j))) }

#[solution_data]
def min_colors : ℕ := 23

#[problem_statement]
theorem usa2001_q1 : IsLeast possible_num_colors min_colors := by
  constructor
  · sorry
  · sorry
