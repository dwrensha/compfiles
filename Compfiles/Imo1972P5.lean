/-
Copyright (c) 2020 Ruben Van de Velde, Stanislas Polu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruben Van de Velde, Stanislas Polu
-/
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Normed.Module.Basic

import ProblemExtraction

problem_file {
  tags := [.Algebra]
  importedFrom :=
    "https://github.com/leanprover-community/mathlib4/blob/master/Archive/Imo/Imo1972Q5.lean"
}

/-!
# International Mathematical Olympiad 1972, Problem 5

`f` and `g` are real-valued functions defined on the real line. For all `x` and `y`,
`f(x + y) + f(x - y) = 2f(x)g(y)`. `f` is not identically zero and `|f(x)| ≤ 1` for all `x`.
Prove that `|g(x)| ≤ 1` for all `x`.
-/

namespace Imo1972P5

problem imo1972_p5 (f g : ℝ → ℝ) (hf1 : ∀ x, ∀ y, f (x + y) + f (x - y) = 2 * f x * g y)
    (hf2 : BddAbove (Set.range fun x => ‖f x‖)) (hf3 : ∃ x, f x ≠ 0) (y : ℝ) : ‖g y‖ ≤ 1 := by
  by_contra! H
  obtain ⟨x, hx⟩ := hf3
  set k := ⨆ x, ‖f x‖
  have h : ∀ x, ‖f x‖ ≤ k := le_ciSup hf2
  have hgy : 0 < ‖g y‖ := by linarith
  have k_pos : 0 < k := lt_of_lt_of_le (norm_pos_iff.mpr hx) (h x)
  have : k / ‖g y‖ < k := (div_lt_iff₀ hgy).mpr (lt_mul_of_one_lt_right k_pos H)
  have : k ≤ k / ‖g y‖ := by
    suffices ∀ x, ‖f x‖ ≤ k / ‖g y‖ from ciSup_le this
    intro x
    suffices 2 * (‖f x‖ * ‖g y‖) ≤ 2 * k by
      rwa [le_div_iff₀ hgy, ← mul_le_mul_left (zero_lt_two : (0 : ℝ) < 2)]
    calc
      2 * (‖f x‖ * ‖g y‖) = ‖2 * f x * g y‖ := by simp [mul_assoc]
      _ = ‖f (x + y) + f (x - y)‖ := by rw [hf1]
      _ ≤ ‖f (x + y)‖ + ‖f (x - y)‖ := (abs_add _ _)
      _ ≤ 2 * k := by linarith [h (x + y), h (x - y)]
  order


end Imo1972P5
