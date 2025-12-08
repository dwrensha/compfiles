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

-- For construction, set all roots to 1 and check it gives 16
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

-- Vieta formulas for b and d (we don't actually need them for a and c)
lemma vieta (x: Fin 4 → ℝ) (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ)
    (hpoly : (X - C (x 0)) * (X - C (x 1)) * (X - C (x 2)) * (X - C (x 3))
    = X^4 + C a * X^3 + C b * X^2 + C c * X + C d) :
    b = (x 0) * (x 1) + (x 0) * (x 2) + (x 0) * (x 3) + (x 1) * (x 2)
    + (x 1) * (x 3) + (x 2) * (x 3) ∧ d = (x 0) * (x 1) * (x 2) * (x 3) := by
  constructor
  · sorry
  · have h := congr_arg (Polynomial.eval 0) hpoly
    --  the output of simp? here is impressive
    simp only [Fin.isValue, eval_mul, eval_sub, eval_X, eval_C, zero_sub, mul_neg, neg_mul,
      neg_neg, eval_add, eval_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, mul_zero, add_zero, zero_add] at h
    rw [h]

-- Now use Vieta relation to prove the key bound
lemma main_bound {x} (hx : Conditions x) : Objective x >= 16 := by
  rcases hx with ⟨_a, b, _c, d, hbd, hpoly⟩
  -- we'll just define a and c to be the Vieta ones we want
  -- since it's not actually needed to tie them to coeffs of polynomial
  let a := (x 0) + (x 1) + (x 2) + (x 3)
  let c := (x 0) * (x 1) * (x 2) + (x 1) * (x 2) * (x 3) + (x 2) * (x 3) * (x 0) + (x 3) * (x 0) * (x 1)
  apply vieta at hpoly -- replace hpoly with the Vieta relations
  have key_identity : Objective x = (b-d-1)^2 + (a-c)^2 := by
    unfold Objective
    rw [hpoly.1, hpoly.2] -- apply Vieta for b and d
    rw [Fin.prod_univ_four] -- thank god
    ring -- in the informal solution, this is proved using a trick with i = sqrt(-1)
  rw [key_identity]
  linarith [show (b-d-1)^2 ≥ 16 by nlinarith, show (a-c)^2 ≥ 0 by nlinarith]
snip end

noncomputable determine solution : ℝ := 16

problem usa2014_p1 : IsLeast (Objective '' { x | Conditions x } ) solution := by
  constructor
  · simp [construction_for_16]
  · rintro _ ⟨x, hcond, rfl⟩
    exact main_bound hcond
end Usa2014P1
