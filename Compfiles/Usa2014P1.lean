/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Chen
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# USA Mathematical Olympiad 2014, Problem 1

Let $a$, $b$, $c$, $d$ be real numbers such that $b-d \ge 5$ and all zeros
$x_1$, $x_2$, $x_3$, and $x_4$ of the polynomial $P(x)=x^4+ax^3+bx^2+cx+d$ are real.
Find the smallest value the product $(x_1^2+1)(x_2^2+1)(x_3^2+1)(x_4^2+1)$ can take.
-/

namespace Usa2014P1

open Polynomial

noncomputable def Objective (x : Fin 4 → ℝ) : ℝ := ∏ i, ((x i)^2 + 1)

def Conditions (x : Fin 4 → ℝ) : Prop :=
  ∃ a b c d : ℝ, (b - d ≥ 5) ∧ (
    (X - C (x 0)) * (X - C (x 1)) * (X - C (x 2)) * (X - C (x 3))
    = X^4 + C a * X^3 + C b * X^2 + C c * X + C d)

snip begin

-- This follows the solution in
-- https://web.evanchen.cc/exams/USAMO-2014-notes.pdf

lemma construction_for_16 : exists x, Conditions x ∧ Objective x = 16 := by
  use fun _ => 1 -- Set every x_i to 1
  constructor
  · unfold Conditions
    use -4, 6, -4, 1 -- a=4, b=6, c=4, d=1
    constructor
    · norm_num -- Checks b-d=5
    · simp only [map_one]
      -- i can't figure out how to kill the C's without actually specifying them like this
      rw [show (C (-4 : ℝ) : ℝ[X]) = -4 by norm_cast]
      rw [show (C (6 : ℝ) : ℝ[X]) = 6 by norm_cast]
      ring
  · unfold Objective
    simp only [one_pow, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    norm_num -- (1+1)^4 = 16

lemma main_bound {x} (hx : Conditions x) : Objective x >= 16 := by
  sorry

snip end

noncomputable determine solution : ℝ := 16

problem usa2014_p1 : IsLeast (Objective '' { x | Conditions x } ) solution := by
  constructor
  · simp [construction_for_16]
  · rintro _ ⟨x, hcond, rfl⟩
    exact main_bound hcond
end Usa2014P1
