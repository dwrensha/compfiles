/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InternLM-MATH LEAN Formalizer v0.1, Hongyu Ouyang
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

import ProblemExtraction

set_option backward.isDefEq.respectTransparency false

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 1984, Problem 1

Let $x$, $y$, $z$ be nonnegative real numbers with $x + y + z = 1$.
Show that $0 \leq xy+yz+zx-2xyz \leq \frac{7}{27}$
-/

namespace Imo1984P1

snip begin

lemma geom_mean_le_arith_mean_3 {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    a * b * c ≤ ((a + b + c) / 3) ^ (3 : ℝ) := by
  have abc_pos : 0 ≤ a * b * c := by positivity
  rw [show a * b * c = ((a * b * c) ^ ((1:ℝ) / 3)) ^ (3 : ℝ) by
        rw [←(Real.rpow_mul abc_pos ((1 : ℝ)/3) 3)]; simp]
  apply Real.rpow_le_rpow; rotate_right
  · norm_num
  · apply Real.rpow_nonneg abc_pos
  · let w := (1 : ℝ) / 3
    change (a * b * c) ^ w ≤ (a + b + c) / 3
    trans w * a + w * b + w * c; rotate_left
    · unfold w
      field_simp
      exact Std.IsPreorder.le_refl (a + b + c)
    rw [Real.mul_rpow (by positivity) hc]
    rw [Real.mul_rpow ha hb]
    apply Real.geom_mean_le_arith_mean3_weighted; all_goals try norm_num; try positivity

snip end

problem imo1984_p1  (x y z : ℝ)
  (h₀ : 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z)
  (h₁ : x + y + z = 1) :
    0 ≤ x * y + y * z + z * x - 2 * x * y * z ∧ x * y + y * z + z * x - 2 * x * y * z ≤
      (7:ℝ) / 27 := by
  rw [calc x * y + y * z + z * x - 2 * x * y * z
           = (1 : ℝ) / 4 * (4 * (y * z + z * x + x * y) - 8 * x * y * z) := by ring_nf
         _ = (1 : ℝ) / 4 * (4 * (y * z + z * x + x * y) -
             8 * x * y * z + 1 - 2 * (x + y + z) + 1) :=
             by rw [h₁]; ring_nf
         _ = (1 : ℝ) / 4 * ((1 - 2 * x) * (1 - 2 * y) * (1 - 2 * z) + 1) := by ring_nf]
  have hx0 : 0 ≤ x := h₀.1
  have hy0 : 0 ≤ y := h₀.2.1
  have hz0 : 0 ≤ z := h₀.2.2

  -- TODO: smarter wlog needed.
  wlog hxy : x ≤ y generalizing x y z
  · rw [show (1 - 2 * x) * (1 - 2 * y) * (1 - 2 * z) = (1 - 2 * y) * (1 - 2 * x) * (1 - 2 * z)
        by linarith]
    exact this y x z ⟨hy0, hx0, hz0⟩ (by rw [←h₁]; linarith) hy0 hx0 hz0 (by linarith)
  · wlog hxz : x ≤ z generalizing x y z
    · rw [show (1 - 2 * x) * (1 - 2 * y) * (1 - 2 * z) = (1 - 2 * z) * (1 - 2 * x) * (1 - 2 * y)
          by linarith]
      exact this z x y ⟨hz0, hx0, hy0⟩
            (by rw [←h₁]; linarith) hz0 hx0 hy0 (by linarith) ((le_of_not_ge hxz).trans hxy)
    · wlog hyz : y ≤ z generalizing x y z
      · rw [show (1 - 2 * x) * (1 - 2 * y) * (1 - 2 * z) = (1 - 2 * x) * (1 - 2 * z) * (1 - 2 * y)
            by linarith]
        exact this x z y ⟨hx0, hz0, hy0⟩ (by rw [←h₁]; linarith) hx0 hz0 hy0 hxz hxy (by linarith)
      · constructor
        · suffices habs : abs ((1 - 2 * x) * (1 - 2 * y) * (1 - 2 * z)) ≤ 1 by
            have ⟨i, _⟩ := abs_le.mp habs; linarith only [i]
          rw [abs_mul, abs_mul]
          refine mul_le_one₀ (mul_le_one₀ ?_ (by positivity) ?_) (by positivity) ?_ <;>
          (rw [abs_le]; constructor) <;> linarith
        · suffices habs : ((1 - 2 * x) * (1 - 2 * y) * (1 - 2 * z)) ≤ (1 : ℝ) / 27 by linarith [habs]
          conv => lhs; rw [← h₁]
          have h1 : 0 ≤ (x + y + z - 2 * x) := by linarith
          have h2 : 0 ≤ (x + y + z - 2 * y) := by linarith
          by_cases h3 : 0 ≤ (x + y + z - 2 * z); rotate_left
          · trans 0; rotate_left
            · norm_num
            apply nonpos_of_neg_nonneg
            rw [←mul_neg]
            apply mul_nonneg
            · positivity
            · linarith
          · apply le_trans (geom_mean_le_arith_mean_3 h1 h2 h3)
            rw [show (x + y + z - 2 * x + (x + y + z - 2 * y) + (x + y + z - 2 * z)) = 1
                by rw [←h₁]; ring_nf]
            norm_num

end Imo1984P1
