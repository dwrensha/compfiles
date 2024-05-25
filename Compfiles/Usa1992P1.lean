/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib.Data.Nat.Digits
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# USA Mathematical Olympiad 1992, Problem 1

Find, as a function of n, the sum of the digits of

     9 × 99 × 9999 × ... × (10^2ⁿ - 1),

where each factor has twice as many digits as the last one.
-/

namespace Usa1992P1
open BigOperators

snip begin

section digits

open Nat

theorem digits_append_zeroes_append_digits {b k m n : ℕ} (hm : 0 < m) (hb : 1 < b) :
    digits b n ++ List.replicate k 0 ++ digits b m =
    digits b (n + b ^ (k + (digits b n).length) * m) := by
  revert m
  induction' k with k ih
  · simp [digits_append_digits (zero_lt_of_lt hb)]
  intro m hm
  rw [List.replicate_succ']
  rw [List.append_assoc, List.append_assoc, List.singleton_append]
  have hmb : 0 < m * b := lt_mul_of_lt_of_one_lt' hm hb
  let h1 := digits_def' hb hmb
  have h2 : m * b / b = m := by
    have : b ≠ 0 := not_eq_zero_of_lt hb
    exact Eq.symm (Nat.eq_div_of_mul_eq_left this rfl)
  simp only [mul_mod_left, h2] at h1
  rw [←h1]
  have h3 := @ih (m * b)
  rw [List.append_assoc] at h3
  rw [h3 hmb]
  congr 2
  ring

end digits

lemma digits_sum (m x y : ℕ)
    (h1 : y < 10^m)
    (h2 : 0 < x) :
    (Nat.digits 10 (x * 10^m + y)).sum =
    (Nat.digits 10 (x * 10^m)).sum + (Nat.digits 10 y).sum := by
  -- choose k such that (digits 10 (y * 10^k).length = m
  --   rw [(Nat.digits 10 y).sum = (Nat.digits 10 (y * 10^k)).sum]
  -- (Nat.digits 10 x).sum + (Nat.digits 10 (y * 10^k)).sum
  -- (Nat.digits 10 (y * 10^k)).sum + (Nat.digits 10 x).sum
  -- (Nat.digits 10 (y * 10^k) ++ Nat.digits 10 x).sum
  --   rw [Nat.digits_append_digits]
  -- Nat.digits 10 ((y * 10^k) + 10^m * x).sum
  sorry

snip end

determine solution : ℕ → ℕ := fun n ↦ 9 * 2 ^ n

problem usa1992_p1 (n : ℕ) :
    (Nat.digits 10
     (∏ i ∈ Finset.range (n + 1), (10^(2^i) - 1))).sum = solution n := by
    -- we follow the informal proof from
    -- https://prase.cz/kalva/usa/usoln/usol921.html

    -- Induction on n.
    induction' n with n ih
    · simp; done

    -- Assume it is true for n-1.
    -- Obviously a_n < 10 to the power of 2^n
    let a i := 10^(2^i) - 1
    have h1 : ∀ i, a i < 10 ^ (2 ^ i) := fun i ↦ by
      dsimp [a]
      have h2 : 0 < 10 ^ 2 ^ i := by positivity
      omega

    have ha1 : ∀ i, 1 ≤ a i := fun i ↦ by
      dsimp [a]
      have h3 : 1 ≤ 2 ^ i := Nat.one_le_two_pow
      have h4 : 10 ^ 1 ≤ 10 ^ (2 ^ i) :=
        Nat.pow_le_pow_of_le_right (by norm_num) h3
      dsimp at h4
      calc
        _ < 10 - 1 := by norm_num
        _ = 10^1 - 1 := by omega
        _ ≤ 10^(2^i) - 1 := Nat.sub_le_sub_right h4 _

    let b : ℕ → ℕ := fun m ↦ ∏ i ∈ Finset.range (m + 1), a i
    -- So b_{n-1} < 10 to the power of (1 + 2 + 2^2 + ... + 2^{n-1}).
    have h2 : ∀ m, b m < 10^(∑ i ∈ Finset.range (m + 1), 2^i) := fun m ↦ by
      dsimp [b]
      rw [←Finset.prod_pow_eq_pow_sum]
      refine Finset.prod_lt_prod_of_nonempty ?_ ?_ Finset.nonempty_range_succ
      · intro i hi
        exact ha1 i
      · intro i hi
        exact h1 i

    -- ... < 10 to the power of 2^n.
    have h3 : ∀ m, 10^(∑ i ∈ Finset.range m, 2^i) < 10^(2^m) := fun m ↦ by
      have h4 : ∑ i ∈ Finset.range m, 2 ^ i < 2 ^ m :=
        Nat.geomSum_lt (le_refl _) fun _ hk ↦ Finset.mem_range.mp hk
      exact (Nat.pow_lt_pow_iff_right (by norm_num)).mpr h4

    -- Now b_n = b_{n-1}10^N - b_{n-1}, where N = 2^n.
    have h4 : b (n + 1) = b n * 10^(2^(n+1)) - b n := by
      nth_rewrite 2 [←mul_one (b n)]
      rw [←Nat.mul_sub_left_distrib]
      dsimp [b]
      rw [Finset.prod_range_succ]

    -- But b_{n-1} < 10^N,
    have h5 : b n < 10 ^ 2 ^ (n + 1) := by
      calc _ < 10 ^ ∑ i ∈ Finset.range (n + 1), 2 ^ i := h2 _
           _ < 10 ^ 2 ^ (n + 1) := by
             refine (Nat.pow_lt_pow_iff_right (by norm_num)).mpr ?_
             exact Nat.geomSum_lt (le_refl _) fun _ hk ↦ Finset.mem_range.mp hk

    -- so b_n = (b_{n-1} - 1)10^N + (10^N - b_{n-1})
    have h6 : b (n + 1) = (b n - 1) * 10 ^(2^(n+1)) + (10 ^(2^(n+1)) - b n) := by
      rw [h4]
      -- TODO: simpler version via zify
      have h7 : 1 ≤ b n := by
        dsimp [b]
        exact Finset.one_le_prod' fun i a ↦ ha1 i
      have h5' := h5.le
      have h8 : 10 ^ 2 ^ (n + 1) ≤ b n * 10 ^ 2 ^ (n + 1) :=
        Nat.le_mul_of_pos_left (10 ^ 2 ^ (n + 1)) h7
      rw [←Nat.add_sub_assoc h5']
      nth_rewrite 2 [add_comm]
      rw [Nat.mul_sub_right_distrib, one_mul, Nat.add_sub_of_le h8]

    -- and the digit sum of b_n is just
    -- the digit sum of (b_{n-1} - 1)10^N plus the digit sum of (10^N - b_{n-1}).
    have h7 : (Nat.digits 10 (b (n + 1))).sum =
              (Nat.digits 10 ((b n - 1) * 10 ^ 2 ^ (n+1))).sum +
              (Nat.digits 10 (10^2^(n+1) - b n)).sum := by
      sorry
    have := digits_sum (2^(n+1)) (b n - 1) (10^2^(n+1) - b n) -- ..
/-
    Now bn-1 is odd and so its last digit is non-zero, so the digit sum of bn-1 - 1 is one less than the digit sum of bn-1, and hence is 9·2n-1 - 1. Multiplying by 10N does not change the digit sum. (10N - 1) - bn-1 has 2n digits, each 9 minus the corresponding digit of bn-1, so its digit sum is 9·2n - 9·2n-1. bn-1 is odd, so its last digit is not 0 and hence the last digit of (10N - 1) - bn-1 is not 9. So the digit sum of 10N - bn-1 is 9·2n - 9·2n-1 + 1. Hence bn has digit sum (9·2n-1 - 1) + (9·2n - 9·2n-1 + 1) = 9·2n.
    -/
    sorry
