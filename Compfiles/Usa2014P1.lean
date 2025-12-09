/-
Copyright (c) 2025 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Chen
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# USA Mathematical Olympiad 2014, Problem 1

Let a, b, c, d be real numbers such that b-d ≥ 5 and all zeros
x₁, x₂, x₃, x₄ of x⁴+ax³+bx²+cx+d are real.
Find the smallest value the product $(x₁²+1)(x₂²+1)(x₃²+1)(x₄²+1)$ can take.
-/

namespace Usa2014P1

open Polynomial

noncomputable def Objective (x : Fin 4 → ℝ) : ℝ := ∏ i, ((x i)^2 + 1)

def Conditions (x : Fin 4 → ℝ) : Prop := ∃ a b c d : ℝ, (b - d ≥ 5) ∧
    ((X - C (x 0)) * (X - C (x 1)) * (X - C (x 2)) * (X - C (x 3))
    = X^4 + C a * X^3 + C b * X^2 + C c * X + C d)

snip begin

-- This follows the solution in
-- https://web.evanchen.cc/exams/USAMO-2014-notes.pdf
-- The basic idea is to show the desired product equals (b-d-1)^2 + (a-c)^2
-- which makes the problem obvious.

-- For construction, set all roots to 1 and check it gives 16
lemma construction_for_16 : exists x, Conditions x ∧ Objective x = 16 := by
  use fun _ => 1 -- Set every x_i to 1
  constructor
  · unfold Conditions
    use -4, 6, -4, 1 -- a=4, b=6, c=4, d=1
    constructor
    · -- Checks b-d=5
      norm_num
    · -- Checks (X-1)^4 = X^4 - 4X^3 + 6X^2 - 4X + 1
      simp only [map_one]
      -- i can't figure out how to kill the C's without actually specifying them like this
      rw [show (C (-4 : ℝ) : ℝ[X]) = -4 by norm_cast]
      rw [show (C (6 : ℝ) : ℝ[X]) = 6 by norm_cast]
      ring
  · unfold Objective
    simp only [one_pow, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    norm_num -- (1+1)^4 = 16

-- Vieta formulas for b and d (we don't actually need them for a and c)
lemma vieta (x: Fin 4 → ℝ) (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ)
    (hpoly : (X - C (x 0)) * (X - C (x 1)) * (X - C (x 2)) * (X - C (x 3))
    = X^4 + C a * X^3 + C b * X^2 + C c * X + C d) :
    d = (x 0) * (x 1) * (x 2) * (x 3) ∧ b = (x 0) * (x 1) + (x 0) * (x 2)
    + (x 0) * (x 3) + (x 1) * (x 2) + (x 1) * (x 3) + (x 2) * (x 3) := by
  constructor
  · apply_fun (·.eval 0) at hpoly
    simp_all
  · apply_fun (·.derivative.derivative.eval 0) at hpoly
    simp at hpoly -- this looks truly hideous when expanded
    linarith

-- Now use Vieta relation to prove the key bound
lemma main_bound {x} (hx : Conditions x) : Objective x >= 16 := by
  rcases hx with ⟨a, b, c, d, hbd, hpoly⟩
  -- we need the actual b and d from the condition, so we have b-d ≥ 5
  apply vieta at hpoly -- replace hpoly with the Vieta relations
  -- we'll just define a and c to be the Vieta ones we want
  -- since it's not actually needed to tie them to coeffs of polynomial
  clear a
  clear c
  let a := (x 0) + (x 1) + (x 2) + (x 3)
  let c := (x 0) * (x 1) * (x 2) + (x 1) * (x 2) * (x 3) + (x 2) * (x 3) * (x 0) + (x 3) * (x 0) * (x 1)
  have key_identity : Objective x = (b-d-1)^2 + (a-c)^2 := by
    unfold Objective
    rw [hpoly.1, hpoly.2] -- apply Vieta for b and d
    rw [Fin.prod_univ_four] -- thank god
    ring -- in the informal solution, this is proved using a trick with i = sqrt(-1)
  rw [key_identity]
  linarith [show (b-d-1)^2 ≥ 16 by nlinarith, show (a-c)^2 ≥ 0 by nlinarith]
snip end

noncomputable determine solution : ℝ := 16

problem usa2014_p1 : IsLeast (Objective '' { x | Conditions x }) solution := by
  constructor
  · simp [construction_for_16]
  · rintro _ ⟨x, hcond, rfl⟩
    exact main_bound hcond
end Usa2014P1
