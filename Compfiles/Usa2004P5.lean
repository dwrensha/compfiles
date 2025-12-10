/-
Copyright (c) 2025 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Chen
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra, .Inequality] }

/-!
# USA Mathematical Olympiad 2004, Problem 5

Prove that for a,b,c > 0,
(a⁵ - a² + 3) (b⁵ - b² + 3) (c⁵ - c² + 3) ≥ (a + b + c)³.
-/

namespace Usa2004P5


snip begin

-- Main estimate that lets us convert into Holder
lemma poly_bound {x : ℝ} (hx : 0 < x) : x^5 - x^2 + 3 ≥ x^3 + 2 := by
  have h : (x-1)^2 * ((x+1) * (x^2+x+1)) ≥ 0 := by
    have h1 : (x-1)^2 ≥ 0 := by nlinarith
    have h2 : (x+1) * (x^2+x+1) ≥ 0 := by nlinarith
    apply mul_nonneg h1 h2
  linarith

-- It's not obvious a priori that x⁵ - x² + 3 is even positive
-- and this will make life annoying later when we try to multiply ineq's together
-- Thus, define a corollary that follows from the above
lemma poly_nonneg {x : ℝ} (hx : 0 < x) : x^5 - x^2 + 3 ≥ 0 := by
  have h1 := poly_bound hx
  have h2 : x ^ 3 + 2 ≥ 0 := by nlinarith
  linarith

lemma holder_nn (a b c : NNReal) : (a^3 + 2) * (b^3 + 2) * (c^3 + 2) ≥ (a+b+c)^3 := by
  let f1 : (Fin 3) → NNReal := fun | 0 => a^3 | 1 => 1 | 2 => 1
  let f2 : (Fin 3) → NNReal := fun | 0 => 1 | 1 => b^3 | 2 => 1
  let f3 : (Fin 3) → NNReal := fun | 0 => 1 | 1 => 1 | 2 => c^3
  sorry

lemma holder {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a^3 + 2) * (b^3 + 2) * (c^3 + 2) ≥ (a + b + c)^3 := by
  have ha_nn := Real.toNNReal_of_nonneg (show a ≥ 0 by positivity)
  have hb_nn := Real.toNNReal_of_nonneg (show b ≥ 0 by positivity)
  have hc_nn := Real.toNNReal_of_nonneg (show c ≥ 0 by positivity)
  have h := holder_nn a.toNNReal b.toNNReal c.toNNReal
  simp_all only [ge_iff_le]
  exact h

lemma multiplied_bound {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a^5 - a^2 + 3) * (b^5 - b^2 + 3) * (c^5 - c^2 + 3) ≥ (a^3 + 2) * (b^3 + 2) * (c^3 + 2) := by
  -- multiply first two ineq's together
  have h := mul_le_mul (poly_bound ha) (poly_bound hb) (by positivity) (poly_nonneg ha)
  -- multiply the third inequality on
  apply mul_le_mul h (poly_bound hc) (by positivity)
  apply mul_nonneg (poly_nonneg ha) (poly_nonneg hb)

snip end

problem usa2004_p5 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a^5 - a^2 + 3) * (b^5 - b^2 + 3) * (c^5 - c^2 + 3) ≥ (a + b + c) ^ 3 :=  by
  sorry
end Usa2004P5
