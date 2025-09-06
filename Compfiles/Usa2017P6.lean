/-
Copyright (c) 2025 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

import ProblemExtraction

problem_file { tags := [.Algebra, .Inequality] }

/-!
# USA Mathematical Olympiad 2017, Problem 6

Find the minimum possible value of
`a / (b³ + 4) + b / (c³ + 4) + c / (d³ + 4) + d / (a³ + 4)`
given that `a, b, c, d` are nonnegative real numbers such that `a + b + c + d = 4`.
-/

namespace Usa2017P6

noncomputable def f (x : Fin 4 → ℝ) : ℝ :=
  ∑ i, x i / (x (i + 1) ^ 3 + 4)

def Conditions (x : Fin 4 → ℝ) : Prop :=
  0 ≤ x ∧ ∑ i, x i = 4

snip begin

lemma one_direction : ∃ x, Conditions x ∧ f x = 2 / 3 := by
  use fun | 0 => 2 | 1 => 2 | 2 => 0 | 3 => 0
  rw [Conditions, f]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [Pi.le_def]; intro i; fin_cases i <;> norm_num
  all_goals rw [Fin.sum_univ_four]; simp; norm_num

lemma other_direction {x} (hx : Conditions x) : 2 / 3 ≤ f x := by
  obtain ⟨h₁, h₂⟩ := hx
  have aux₁ {k : ℝ} (hk : 0 ≤ k) : 1 / 4 - k / 12 ≤ 1 / (k ^ 3 + 4) := by
    rw [show 1 / 4 - k / 12 = (3 - k) / 12 by ring, div_le_div_iff₀ (by norm_num) (by positivity),
      one_mul, ← sub_nonneg, show 12 - (3 - k) * (k ^ 3 + 4) = k * (k + 1) * (k - 2) ^ 2 by ring]
    positivity
  have aux₂ : ∑ i, x i * x (i + 1) ≤ 4 := by
    rw [Fin.sum_univ_four]; simp only [Fin.reduceAdd]
    rw [show x 0 * x 1 + x 1 * x 2 + x 2 * x 3 + x 3 * x 0 = (x 0 + x 2) * (x 1 + x 3) by ring]
    have iden := four_mul_le_sq_add (x 0 + x 2) (x 1 + x 3)
    rw [show x 0 + x 2 + (x 1 + x 3) = x 0 + x 1 + x 2 + x 3 by ring,
      ← Fin.sum_univ_four, h₂] at iden
    linarith
  calc
    _ ≥ ∑ i, (x i / 4 - x i * x (i + 1) / 12) := by
      rw [f]; gcongr with i
      rw [mul_div_assoc, div_eq_mul_one_div, ← mul_sub, div_eq_mul_one_div (x i)]
      gcongr; · simpa using h₁ i
      exact aux₁ (by simpa using h₁ (i + 1))
    _ = 1 - (∑ i, x i * x (i + 1)) / 12 := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_div, h₂, ← Finset.sum_div, div_self four_ne_zero]
    _ ≥ _ := by linarith

snip end

problem usa2017_p6 : IsLeast (f '' {x | Conditions x}) (2 / 3) := by
  constructor
  · simp [one_direction]
  · simp_rw [lowerBounds, Set.mem_image, Set.mem_setOf, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
    exact fun x hx ↦ other_direction hx

end Usa2017P6
