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
  have h1 : (x-1)^2 ≥ 0 := by nlinarith
  have h2 : (x+1) * (x^2+x+1) ≥ 0 := by nlinarith
  nlinarith

-- It's not obvious a priori that x⁵ - x² + 3 is even positive
-- and this will make life annoying later when we try to multiply ineq's together
-- Thus, define a corollary that follows from the above
lemma poly_nonneg {x : ℝ} (hx : 0 < x) : x^5 - x^2 + 3 ≥ 0 := by
  have h1 := poly_bound hx
  have h2 : x ^ 3 + 2 ≥ 0 := by nlinarith
  linarith

-- Multiply these all together to get to the intermediate (a³+2)(b³+2)(c³+2)
lemma multiplied_bound {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a^5 - a^2 + 3) * (b^5 - b^2 + 3) * (c^5 - c^2 + 3) ≥ (a^3 + 2) * (b^3 + 2) * (c^3 + 2) := by
  -- multiply first two ineq's together
  have h := mul_le_mul (poly_bound ha) (poly_bound hb) (by positivity) (poly_nonneg ha)
  -- multiply the third inequality on
  apply mul_le_mul h (poly_bound hc) (by positivity)
  exact mul_nonneg (poly_nonneg ha) (poly_nonneg hb)

-- 3-variable Holder inequality (the painful part...)
lemma holder_conjugate_2 : Real.HolderConjugate 2 2 := by
  rw [@Real.holderConjugate_iff 2 2]
  norm_num
lemma holder_conjugate_3 : Real.HolderConjugate (3/2 : ℝ) 3 := by
  rw [@Real.holderConjugate_iff (3/2 : ℝ) 3]
  norm_num
theorem triple_holder (S : Finset ℕ) (f1 f2 f3 : ℕ → NNReal) :
    (∑ i ∈ S, (f1 i) * (f2 i) * (f3 i)) ^ 3
    ≤ (∑ i ∈ S, (f1 i) ^ 3) * (∑ i ∈ S, (f2 i) ^ 3) * (∑ i ∈ S, (f3 i) ^ 3) := by
  have h1 := NNReal.inner_le_Lp_mul_Lq S (f1 * f2) f3 holder_conjugate_3
  have h2 := NNReal.inner_le_Lp_mul_Lq S (f1 ^ (3/2 : ℝ)) (f2 ^ (3/2 : ℝ)) holder_conjugate_2
  -- Cube both sides of h1, square both sides of h2
  replace h1 := NNReal.rpow_le_rpow h1 (by norm_num : (0 : ℝ) ≤ 3)
  replace h2 := NNReal.rpow_le_rpow h2 (by norm_num : (0 : ℝ) ≤ 2)
  -- Fight through exponent hell
  simp_all only [NNReal.mul_rpow, ← NNReal.rpow_natCast, ← NNReal.rpow_mul]
  norm_num at h1 h2 ⊢
  -- if at first you don't succeed, try try again
  -- (by which i mean copy paste the same two lines and pray to the mathlib gods)
  simp_all only [NNReal.mul_rpow, ← NNReal.rpow_natCast, ← NNReal.rpow_mul]
  norm_num at h1 h2 ⊢
  apply h1.trans (mul_le_mul_left h2 _)

lemma key_holder (a b c : NNReal) : (a^3 + 2) * (b^3 + 2) * (c^3 + 2) ≥ (a+b+c)^3 := by
  rw [ge_iff_le]
  -- only need values at 0 1 2 for these, the rest are junk values
  -- (the mathlib holder seems to demand you define the function on all of ℕ)
  have h := triple_holder (Finset.range 3)
    (fun | 0 => a | _ => 1) -- a, 1, 1
    (fun | 1 => b | _ => 1) -- 1, b, 1
    (fun | 2 => c | _ => 1) -- 1, 1, c
  simp only [← Fin.sum_univ_eq_sum_range, Fin.sum_univ_three] at h
  convert h using 1 <;> ring

lemma key_holder_real {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a^3 + 2) * (b^3 + 2) * (c^3 + 2) ≥ (a + b + c)^3 := by
  rw [← Real.coe_toNNReal a ha.le, ← Real.coe_toNNReal b hb.le, ← Real.coe_toNNReal c hc.le]
  exact key_holder a.toNNReal b.toNNReal c.toNNReal

snip end

problem usa2004_p5 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a^5 - a^2 + 3) * (b^5 - b^2 + 3) * (c^5 - c^2 + 3) ≥ (a + b + c) ^ 3 := by
  exact (multiplied_bound ha hb hc).trans' (key_holder_real ha hb hc)
end Usa2004P5
