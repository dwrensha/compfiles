/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# USA Mathematical Olympiad 1990, Problem 2

A sequence of functions {fₙ(x)} is defined recursively as follows:

                  f₀(x) = 8
                fₙ₊₁(x) = √(x² + 6fₙ(x)).

For each nonnegative integer n, find all real solutions of the equation

                  fₙ(x) = 2x.
-/

namespace Usa1990P2

noncomputable def f : ℕ → ℝ → ℝ
|     0, _ => 8
| n + 1, x => Real.sqrt (x^2 + 6 * f n x)

determine solution_set (n : ℕ) : Set ℝ := { 4 }

problem usa1990_p2 (n : ℕ) (x : ℝ) : x ∈ solution_set n ↔ f n x = 2 * x := by
  -- based on solution from
  -- https://artofproblemsolving.com/wiki/index.php/1990_USAMO_Problems/Problem_2
  have hfnp : ∀ n x, 0 < f n x := fun n x ↦ by
    induction' n with n ih
    · norm_num [f]
    · unfold f
      positivity

  suffices H : ∀ x, 0 ≤ x → ((4 < x → f n x < 2 * x) ∧ (x = 4 → f n x = 2 * x) ∧
                     (x < 4 → 2 * x < f n x)) by grind
  induction n with
  | zero =>
    intro x hx5
    simp only [f]
    obtain h1 | rfl | h3 := lt_trichotomy x 4
    · exact ⟨fun h1' ↦ ((lt_asymm h1) h1').elim,
             fun h1' ↦ ((LT.lt.ne h1) h1').elim,
             fun _ ↦ by linarith only [h1]⟩
    · norm_num
    · exact ⟨fun _ ↦ by linarith only [h3],
             fun h1' ↦ by linarith,
             fun h1' ↦ by linarith⟩

  | succ n ih =>
    intro x hx5
    have h5 : Real.sqrt (4 * x^2) = 2 * x := by
        rw [show 4 * x^2 = (2 * x)^2 by ring]
        have h6 : 0 ≤ 2 * x := by positivity
        exact Real.sqrt_sq h6

    refine ⟨?_, ?_, ?_⟩
    · intro hx1
      have h2 : f n x < 2 * x := (ih x hx5).1 hx1
      have hc :=
        calc x ^ 2 + 6 * f n x < x ^ 2 + 6 * (2 * x) := by gcongr
             _ = x ^ 2 + 3 * (4 * x) := by ring
             _ < x ^ 2 + 3 * (x * x) := by gcongr
             _ = 4 * x^2 := by ring
      have hc' : Real.sqrt (x ^ 2 + 6 * f n x) < Real.sqrt (4 * x ^ 2) := by
        have h4 : 0 < 4 * x ^ 2 := by positivity
        exact (Real.sqrt_lt_sqrt_iff_of_pos h4).mpr hc
      rwa [h5] at hc'
    · grind [f]
    · intro hx1
      have h2 : 2 * x < f n x := (ih x hx5).2.2 hx1
      obtain rfl | hx6 := LE.le.eq_or_lt hx5
      · simp [hfnp]

      have hc :=
        calc 4 * x^2 = x ^ 2 + 3 * (x * x) := by ring
                   _ < x ^ 2 + 3 * (4 * x) := by gcongr
                   _ = x ^ 2 + 6 * (2 * x) := by ring
                   _ < x ^ 2 + 6 * f n x := by gcongr

      have hc' : Real.sqrt (4 * x ^ 2) < Real.sqrt (x ^ 2 + 6 * f n x) := by
        have h4 : 0 < x ^ 2 + 6 * f n x := by
          have := hfnp n x
          positivity
        exact (Real.sqrt_lt_sqrt_iff_of_pos h4).mpr hc
      rwa [h5] at hc'


end Usa1990P2
