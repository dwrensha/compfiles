/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Algebra.Periodic
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

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

problem imo1968_p5a (f : ℝ → ℝ) (a : ℝ) (hf : P a f) :
    ∃ b, 0 < b ∧ f.Periodic b := by
  -- https://artofproblemsolving.com/wiki/index.php/1968_IMO_Problems/Problem_5
  obtain ⟨hf1, hf2⟩ := hf
  use 2 * a
  constructor
  · positivity
  have h1 : ∀ x, 1 / 2 ≤ f (x + a) := fun x ↦ by
    rw [(hf2 x).2, le_add_iff_nonneg_right]
    exact Real.sqrt_nonneg (f x - f x ^ 2)
  have h2 : ∀ x, 0 ≤ f (x + a) - 1/2 := fun x ↦ by linarith [h1 x]
  have h3 : ∀ x, f (x + a) * (1 - f (x + a)) = (f x - 1/2) ^2 := fun x ↦ by
    have h6 : f (x + a) * (1 - f (x + a)) =
       -((f (x + a) - 1/2)^2  - (1/2)^2) := by ring
    rw [h6]
    obtain ⟨hf2x1, hf2x2⟩ := hf2 x
    rw [hf2x2, add_sub_cancel']
    have h7 : 0 ≤ f x - f x ^ 2 := sub_nonneg.mpr hf2x1
    rw [Real.sq_sqrt h7]
    ring
  intro x
  obtain ⟨_, ha2⟩ := hf2 (x + a)
  have h4 : f (x + a) - f (x + a) ^ 2 = f (x + a) * (1 - f (x + a)) := by ring
  rw [two_mul, ←add_assoc, ha2, h4]
  rw [h3]
  rw [Real.sqrt_sq_eq_abs]
  have h2' := abs_of_nonneg (h2 (x-a))
  rw [sub_add_cancel] at h2'
  rw [add_eq_of_eq_sub' h2']

noncomputable determine solution_func : ℝ → ℝ := fun x ↦
 if Even ⌊x⌋ then 1 else 1/2

problem imo1968_p5b :
    P 1 solution_func ∧ ¬∃c, solution_func = Function.const ℝ c := by
  -- https://artofproblemsolving.com/wiki/index.php/1968_IMO_Problems/Problem_5
  constructor
  · constructor
    · exact Real.zero_lt_one
    · intro x
      obtain heven | hodd :=  Classical.em (Even ⌊x⌋)
      · have h1 : ¬ Even (⌊x⌋ + 1) :=
          Int.odd_iff_not_even.mp (Even.add_one heven)
        simp [solution_func, h1, heven]
      · have h2 : Real.sqrt 4 = 2 := by
          rw [show (4 : ℝ) = 2^2 by norm_num, Real.sqrt_sq_eq_abs, abs_two]
        norm_num [solution_func, Int.even_add_one.mpr hodd, h2, hodd]
  · rintro ⟨c, hc⟩
    have h1 : Function.const ℝ c 0 = c := rfl
    rw [←hc] at h1
    have h1' : Function.const ℝ c 1 = c := rfl
    rw [←hc] at h1'
    have h2 : solution_func 0 = 1 := by simp
    have h3 : c = 1 := h1.symm.trans h2
    have h4 : solution_func 1 = 1/2 := by
      have h6 : ¬ Even ⌊(1:ℝ)⌋ := by simp
      simp [h6, solution_func]
    have h5 : c = 1/2 := h1'.symm.trans h4
    rw [h3] at h5
    norm_num at h5
