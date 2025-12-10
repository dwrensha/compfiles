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

-- 3-variable Holder inequality
lemma holder_conjugate_2 : Real.HolderConjugate 2 2:= by
  rw [@Real.holderConjugate_iff 2 2]
  norm_num
lemma holder_conjugate_3 : Real.HolderConjugate 3 (3/2 : ℝ) := by
  rw [@Real.holderConjugate_iff 3 (3/2 : ℝ)]
  norm_num
theorem triple_holder (S : Finset ℕ) (f1 f2 f3 : ℕ → NNReal) :
    (∑ x ∈ S, (f1 x) * (f2 x) * (f3 x)) ^ 3
    ≤ (∑ x ∈ S, (f1 x) ^ 3) * (∑ x ∈ S, (f2 x) ^ 3) * (∑ x ∈ S, (f3 x) ^ 3) := by
  have h1 := NNReal.inner_le_Lp_mul_Lq S f1 (f2 * f3) holder_conjugate_3
  have h2 := NNReal.inner_le_Lp_mul_Lq S (f2 ^ (3/2 : ℝ)) (f3 ^ (3/2 : ℝ)) holder_conjugate_2
  -- Raise the mathlib Holder expressions to suitable powers
  replace h1 := NNReal.rpow_le_rpow h1 (by norm_num : (0 : ℝ) ≤ 3)
  replace h2 := NNReal.rpow_le_rpow h2 (by norm_num : (0 : ℝ) ≤ 2)
  -- Fight through exponent hell
  simp_all only [NNReal.mul_rpow, ← NNReal.rpow_natCast, ← NNReal.rpow_mul]
  norm_num at h1 h2 ⊢
  simp only [← mul_assoc] at h1
  simp_all only [NNReal.mul_rpow, ← NNReal.rpow_natCast, ← NNReal.rpow_mul]
  norm_num at h1 h2 ⊢
  have h := h1.trans (mul_le_mul_right h2 _)
  rw [← mul_assoc] at h
  exact h

lemma usamo_2004_holder_nn (a b c : NNReal) : (a^3 + 2) * (b^3 + 2) * (c^3 + 2) ≥ (a+b+c)^3 := by
  rw [ge_iff_le]
  let f1 : ℕ → NNReal := fun | 0 => a | _ => 1
  let f2 : ℕ → NNReal := fun | 1 => b | _ => 1
  let f3 : ℕ → NNReal := fun | 2 => c | _ => 1
  have h := triple_holder (Finset.range 3) f1 f2 f3
  -- now expand the sums
  simp only [← Fin.sum_univ_eq_sum_range, Fin.sum_univ_three, Fin.isValue, Fin.coe_ofNat_eq_mod,
      Nat.zero_mod, Nat.one_mod, Nat.mod_succ] at h
  unfold f1 at h
  unfold f2 at h
  unfold f3 at h
  simp only [mul_one, one_mul, one_pow] at h
  convert h using 1
  ring

lemma usamo_2004_holder {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a^3 + 2) * (b^3 + 2) * (c^3 + 2) ≥ (a + b + c)^3 := by
  have ha_nn := Real.toNNReal_of_nonneg (show a ≥ 0 by positivity)
  have hb_nn := Real.toNNReal_of_nonneg (show b ≥ 0 by positivity)
  have hc_nn := Real.toNNReal_of_nonneg (show c ≥ 0 by positivity)
  have h := usamo_2004_holder_nn a.toNNReal b.toNNReal c.toNNReal
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
