/-
Copyright (c) 2025 Roozbeh Yousefzadeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Roozbeh Yousefzadeh
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file {
  tags := [.Algebra]
  importedFrom := "https://github.com/roozbeh-yz/IMO-Steps/blob/main/Lean_v20/imo_proofs/imo_1966_p5.lean"
}

/-!
# International Mathematical Olympiad 1966, Problem 5

Solve the system of equations

  |a_1 - a_2| x_2 +|a_1 - a_3| x_3 +|a_1 - a_4| x_4 = 1
  |a_2 - a_1| x_1 +|a_2 - a_3| x_3 +|a_2 - a_4| x_4 = 1
  |a_3 - a_1| x_1 +|a_3 - a_2| x_2 +|a_3 - a_4| x_4 = 1
  |a_4 - a_1| x_1 +|a_4 - a_2| x_2 +|a_4 - a_3| x_3 = 1

  where a_1, a_2, a_3, a_4 are four different real numbers.
-/

namespace Imo1966P5

noncomputable abbrev solution_fun : (ℝ×ℝ×ℝ×ℝ) → (ℝ×ℝ×ℝ×ℝ) :=
  fun (a0, a1, a2, a3) ↦
  let s : List ℝ := [a0, a1, a2, a3]
  let ai : ℝ := Option.get (List.min? s) rfl
  let al : ℝ := Option.get (List.max? s) rfl
  let i : ℕ := s.findIdx (. = ai)
  let l : ℕ := s.findIdx (. = al)
  let f : ℕ → ℝ := fun n ↦ if n = i ∨ n = l then (1 / (al - ai)) else 0
  (f 0, f 1, f 2, f 3)

problem imo1966_p5
  (x a : Fin 4 → ℝ)
  (h₀ : Function.Injective a)
  (h₁: ∀ i : Fin 4, ∑ j : Fin 4, abs (a i - a j) * x j = 1) :
  (x 0, x 1, x 2, x 3) = solution_fun (a 0, a 1, a 2, a 3) := by
  sorry
