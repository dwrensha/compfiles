/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Algebra.Periodic
import Mathlib.Tactic

import ProblemExtraction

problem_file

/-!
# International Mathematical Olympiad 1968, Problem 5

Let f be a real-valued function defined for all real numbers x such that,
for some positive constant a, the equation

  f(x + a) = a/2 + √(f(x) - (f(x))²)

holds for all x.

(a) Prove that the function f is periodic.
(b) For a = 1, give an example of a non-constant function with the required properties.
-/

namespace Imo1968P5

abbrev P (a : ℝ) (f : ℝ → ℝ) : Prop :=
  0 < a ∧
  ∀ x, (f x)^2 ≤ f x ∧ f (x + a) = 1/2 + Real.sqrt (f x - (f x)^2)

determine solution_func : ℝ → ℝ := sorry

problem imo1968_p5a (f : ℝ → ℝ) (a : ℝ) (hf : P a f) :
    ∃ b, 0 < b ∧ f.Periodic b := by
  obtain ⟨hf1, hf2⟩ := hf
  use 2 * a
  constructor
  · positivity
  have h1 : ∀ x, 1 / 2 ≤ f (x + a) := fun x ↦ by
    rw [(hf2 x).2, le_add_iff_nonneg_right]
    exact Real.sqrt_nonneg (f x - f x ^ 2)
  have h2 : ∀ x, 0 ≤ f (x + a) - 1/2 := fun x ↦ by linarith [h1 x]
  have h3 : ∀ x, f (x + a) * (1 - f (x + a)) = (1/2 - f x) ^2 := fun x ↦ by
    sorry
  intro x
  obtain ⟨ha1, ha2⟩ := hf2 (x + a)
  have h4 : f (x + a) - f (x + a) ^ 2 = f (x + a) * (1 - f (x + a)) := by ring
  rw [two_mul, ←add_assoc, ha2, h4, h3]
  rw [Real.sqrt_sq_eq_abs]
  have h2' := abs_of_nonneg (h2 x)
  sorry

problem imo1968_p5b :
    P 1 solution_func ∧ ¬∃c, solution_func = Function.const ℝ c := by
  sorry
