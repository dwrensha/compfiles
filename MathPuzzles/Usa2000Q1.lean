/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.GroupPower.Lemmas

/-!
USA Mathematical Olympiad 2000, Problem 1

A function f : ℝ → ℝ is called "very convex" if it satisfies

  ∀ x y : ℝ, (f(x) + f(y))/2 ≥  f((x + y)/2) + |x - y|.

Show that there exist no very convex functions.
-/

namespace Usa2000Q1

theorem usa2000_q1 :
    ¬∃ f : ℝ → ℝ,
      ∀ x y : ℝ, f ((x + y) / 2) + |x - y| ≤ (f x + f y) / 2 := by
  -- Informal solution from artofproblemsolving.com
  -- Suppose, for the sake of contradiction, that f is very convex.
  rw [not_exists]
  intros f hc

  -- Notice that f(x) is very convex if and only if f(x) + C is convex, where C
  -- is any constant. Thus, we can set f(0) = 0 for convenience.

  wlog hf0 : f 0 = 0 with H
  · apply H (fun x ↦ f x - f 0)
    · intros x y
      have := hc x y
      linarith
    · exact sub_self (f 0)

  -- Suppose that f(1) = A and f(-1) = B.

  let A := f 1
  let B := f (-1)

  -- By the very convex condition, (f(0) + f(2⁻ⁿ))/2 ≥ f(2⁻⁽ⁿ⁺¹⁾) + 1/2ⁿ
  have h1 : ∀ n : ℕ,
      f (2 ^ (-((n:ℝ) + 1))) + 1 / 2^n ≤ (f 0 + f (2 ^ (-(n:ℝ)))) / 2 := by
    intro n
    have h2 := hc 0 (2 ^ (-(n:ℝ)))
    have h2p : (0:ℝ) < 2 := by norm_num
    have h3 : ((0:ℝ) + (2:ℝ) ^ (-(n:ℝ))) / 2 = 2 ^ (-((n:ℝ) + 1)) := by
      rw[zero_add]
      have h4 : -((n : ℝ) + 1) = - (n : ℝ) - 1 := by ring
      rw[h4, div_eq_mul_one_div]
      have h5 : (1:ℝ) / 2 = 2 ^ (-(1:ℝ)) := by
         rw[Real.rpow_neg (by norm_num)]; norm_num
      rw[h5, ←Real.rpow_add h2p]
      congr
    rw[h3] at h2
    rw[←neg_eq_zero_sub, abs_neg] at h2
    have h6 : 0 < (2:ℝ) ^ (-(n:ℝ)) := Real.rpow_pos_of_pos h2p _
    rw[abs_of_pos h6] at h2
    have h7 : (2:ℝ) ^ (- (n : ℝ)) = 1 / 2^(n:ℝ) := by
      have h9 : (0:ℝ) ≤ (2:ℝ) := by norm_num
      rw[Real.rpow_neg h9]
      exact inv_eq_one_div _
    nth_rewrite 1 [h7] at h2
    exact h2

  have h1' : ∀ n : ℕ,
      f (-2 ^ (-((n:ℝ) + 1))) + 1 / 2^n ≤ (f 0 + f (-2 ^ (-(n:ℝ)))) / 2 := by
    intro n
    have h2 := hc 0 (-2 ^ (-(n:ℝ)))
    have h2p : (0:ℝ) < 2 := by norm_num
    have h3 : ((0:ℝ) + -(2:ℝ) ^ (-(n:ℝ))) / 2 = -2 ^ (-((n:ℝ) + 1)) := by
      rw[zero_add]
      have h4 : -((n : ℝ) + 1) = - (n : ℝ) - 1 := by ring
      rw[h4, div_eq_mul_one_div]
      have h5 : (1:ℝ) / 2 = 2 ^ (-(1:ℝ)) := by
         rw[Real.rpow_neg (by norm_num)]; norm_num
      rw[h5, neg_mul, ←Real.rpow_add h2p]
      congr
    rw[h3] at h2; clear h3
    rw[←neg_eq_zero_sub, abs_neg] at h2
    have h6 : -(2:ℝ) ^ (-(n:ℝ)) < 0 := neg_lt_zero.mpr (Real.rpow_pos_of_pos h2p _)
    rw[abs_of_neg h6, neg_neg] at h2
    have h7 : (2:ℝ) ^ (- (n : ℝ)) = 1 / 2^(n:ℝ) := by
      have h9 : (0:ℝ) ≤ (2:ℝ) := by norm_num
      rw[Real.rpow_neg h9]
      exact inv_eq_one_div _
    nth_rewrite 1 [h7] at h2
    exact h2

  -- A straightforward induction shows that f(2⁻ⁿ) ≤ (A - 2n) / 2ⁿ
  -- for all nonnegative integers n.
  have h2 : ∀ n : ℕ, f (2 ^ (- (n : ℝ))) ≤ (A - 2 * (n:ℝ)) / 2^(n:ℝ) := by
    intro n
    induction' n with n hpn
    · simp
    · have h6 : 2 ^ (n.succ : ℝ) = 2 ^ (n : ℝ) * 2 := by norm_cast
      replace hpn : f (2 ^ (-(n:ℝ)))/2 ≤ (A - 2 * ↑n) / 2 ^ ↑n.succ := by
         rw[h6, div_mul_eq_div_div]; linarith
      have h4 : f (2 ^ (-↑(Nat.succ n)))
            = f (2 ^ (-(↑n + 1))) := by congr; norm_cast
      rw[h4]
      have h2ne0 : (2: ℝ) ≠ 0 := by norm_num
      have h7 : (1:ℝ) / 2 ^ (n:ℝ) = 2 / 2 ^ (n.succ:ℝ) := by
        rw[h6, div_mul_left h2ne0]

      have h8' : (n.succ : ℝ) = (n:ℝ) + 1 := by norm_cast
      have h8 : A - 2 * ↑n - 2 = A - 2 * ↑n.succ := by
        rw[Nat.succ_eq_add_one, h8']; ring

      calc _ ≤ _ := le_sub_iff_add_le.mpr (h1 n)
           _ = _ := by rw[hf0, zero_add]
           _ ≤ (A - 2 * ↑n) / 2 ^ (n.succ:ℝ) - 1 / 2 ^ (n:ℝ) := sub_le_sub_right hpn _
           _ ≤ _ := by rw[h7, ←sub_div, h8]

  -- Using a similar line of reasoning as above, f(-2⁻ⁿ) ≤ (B - 2n)/2ⁿ.

  have h3 : ∀ n : ℕ, f (- 2 ^ (- (n : ℝ))) ≤ (B - 2 * (n:ℝ)) / 2^(n:ℝ) := by
    intro n
    induction' n with n hpn
    · simp
    · have h6 : 2 ^ (n.succ : ℝ) = 2 ^ (n : ℝ) * 2 := by norm_cast
      replace hpn : f (-2 ^ (-(n:ℝ)))/2 ≤ (B - 2 * ↑n) / 2 ^ ↑n.succ := by
         rw[h6, div_mul_eq_div_div]; linarith
      have h4 : f (-2 ^ (-↑(Nat.succ n)))
            = f (-2 ^ (-(↑n + 1))) := by congr; norm_cast
      rw[h4]
      have h2ne0 : (2: ℝ) ≠ 0 := by norm_num
      have h7 : (1:ℝ) / 2 ^ (n:ℝ) = 2 / 2 ^ (n.succ:ℝ) := by
        rw[h6, div_mul_left h2ne0]

      have h8' : (n.succ : ℝ) = (n:ℝ) + 1 := by norm_cast
      have h8 : B - 2 * ↑n - 2 = B - 2 * ↑n.succ := by
        rw[Nat.succ_eq_add_one, h8']; ring
      calc _ ≤ _ := le_sub_iff_add_le.mpr (h1' n)
           _ = _ := by rw[hf0, zero_add]
           _ ≤ (B - 2 * ↑n) / 2 ^ (n.succ:ℝ) - 1 / 2 ^ (n:ℝ) := sub_le_sub_right hpn _
           _ ≤ _ := by rw[h7, ←sub_div, h8]

  -- Therefore, for every nonnegative integer n, f(2⁻ⁿ) + f(-2⁻ⁿ) ≤ (A+B-4n)/2ⁿ.
  have h4 : ∀ n : ℕ,
      f (2^(-(n:ℝ))) + f (-2^(-(n:ℝ))) ≤ (A + B - 4 * n) / 2^(n:ℝ) := by
    intro n
    have h5 := add_le_add (h2 n) (h3 n)
    have h6 : A - 2 * ↑n + (B - 2 * ↑n) = A + B - 4 * ↑n := by ring
    rwa [←add_div, h6] at h5

  -- Now, we choose n large enough such that n > (A+B)/4 - 1.
  let N := Nat.ceil ((A + B) / 4)
  -- It follows that f(2⁻ⁿ) + f(-2⁻ⁿ) < 1/2ⁿ⁻².
  have h7 : f (2 ^ (-(N:ℝ))) + f (-2 ^ (-(N:ℝ))) < 1 / 2^((N:ℝ) - 2) := by
     have h10 : (0:ℝ) < 2 := by norm_num
     have h130 : (0:ℝ) ≤ (2:ℝ)^(N:ℝ) := by norm_num
     have h8' : (A + B) / 4 ≤ N := Nat.le_ceil _
     have h8 : A + B - 4 * ↑N ≤ 0 := by linarith
     have h9 : (A + B - 4 * ↑N) / 2 ^ (N : ℝ) ≤ 0 := div_nonpos_of_nonpos_of_nonneg h8 h130
     calc _ ≤ _ := h4 N
          _ ≤ 0 := h9
          _ < _ := by rw[one_div_pos]; exact Real.rpow_pos_of_pos h10 _

  -- However, by the very convex condition, f(2⁻ⁿ) + f(-2⁻ⁿ) ≥ 1/2ⁿ⁻².
  have h20 := hc (2 ^(-(N:ℝ))) (-2 ^(-(N:ℝ)))

  -- This is a contradiction.
  rw[add_neg_self, zero_div, hf0, zero_add, sub_neg_eq_add, ←two_mul] at h20
  nth_rewrite 1 [show (2:ℝ) = (2:ℝ) ^ (1:ℝ) by norm_num] at h20
  rw[←Real.rpow_add (by norm_num)] at h20
  have h21 := calc _ ≤ _ := le_abs_self ((2 : ℝ) ^ (1 + -(N : ℝ)))
               _ ≤ _ := h20
  replace h20 : (2:ℝ) * 2^(1 + -(N:ℝ)) ≤ f ((2:ℝ)^(-(N:ℝ))) + f (-(2:ℝ) ^ (-(N:ℝ))) := by linarith
  nth_rewrite 1 [show (2:ℝ) = (2:ℝ) ^ (1:ℝ) by norm_num] at h20
  rw[←Real.rpow_add (by norm_num)] at h20
  have h22 : (1 + (1 + -(N:ℝ))) = -((N : ℝ) - 2) := by ring
  have h23 : (0 :ℝ) ≤ 2 := by norm_num
  rw[h22, Real.rpow_neg h23, inv_eq_one_div] at h20
  exact not_lt.mpr h20 h7

