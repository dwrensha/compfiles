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

variable {a b c : ℝ}

snip begin

lemma poly_bound {x : ℝ} (hx : 0 < x) : x^5 - x^2 + 3 ≥ x^3 + 2 := by
  have h : (x-1)^2 * ((x+1) * (x^2+x+1)) ≥ 0 := by
    have h1 : (x-1)^2 ≥ 0 := by nlinarith
    have h2 : (x+1) * (x^2+x+1) ≥ 0 := by nlinarith
    apply mul_nonneg h1 h2
  linarith

lemma poly_nonneg {x : ℝ} (hx : 0 < x) : x^5 - x^2 + 3 ≥ 0 := by
  have h1 := poly_bound hx
  have h2 : x ^ 3 + 2 ≥ 0 := by nlinarith
  linarith

lemma holder (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a^3 + 2) * (b^3 + 2) * (c^3 + 2) ≥ (a+b+c)^3 := by
  sorry

lemma multiplied_bound (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a^5 - a^2 + 3) * (b^5 - b^2 + 3) * (c^5 - c^2 + 3) ≥ (a^3 + 2) * (b^3 + 2) * (c^3 + 2) := by
  -- multiply first two ineq's together
  have h1 := mul_le_mul (poly_bound ha) (poly_bound hb) (by positivity) (poly_nonneg ha)
  -- multiply the third inequality on
  apply mul_le_mul h1 (poly_bound hc) (by positivity)
  apply mul_nonneg (poly_nonneg ha) (poly_nonneg hb)

snip end

problem usa2004_p5 (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a^5 - a^2 + 3) * (b^5 - b^2 + 3) * (c^5 - c^2 + 3) ≥ (a + b + c) ^ 3 :=  by
  sorry
end Usa2004P5
