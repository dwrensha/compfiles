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

snip begin

section digits

open Nat

-- TODO add this to mathlib
theorem digits_append_zeroes_append_digits {b k m n : ℕ} (hm : 0 < m)
    (hb : 1 < b) :
    digits b n ++ List.replicate k 0 ++ digits b m =
    digits b (n + b ^ (k + (digits b n).length) * m) := by
  revert m
  induction' k with k ih
  · simp [digits_append_digits (zero_lt_of_lt hb)]
  intro m hm
  rw [List.replicate_succ', List.append_assoc, List.append_assoc, List.singleton_append]
  have hmb : 0 < m * b := lt_mul_of_lt_of_one_lt' hm hb
  let h1 := digits_def' hb hmb
  have h2 : m = m * b / b := by
    exact Nat.eq_div_of_mul_eq_left (not_eq_zero_of_lt hb) rfl
  simp only [mul_mod_left, ←h2] at h1
  rw [←h1, ←List.append_assoc, ih hmb]
  ring_nf

end digits

-- TODO add a generalization of this mathlib?
lemma digits_pow (m : ℕ) : (Nat.digits 10 (10^m)).length = m + 1 := by
  induction' m with m ih
  · simp
  rw [pow_succ]
  rw [Nat.digits_def' (by norm_num) (by positivity)]
  rw [mul_div_cancel_right₀ _ (by norm_num), List.length_cons]
  rw [ih]

lemma lemma2 {m y: ℕ} (hy : y < 10^m) :
    (Nat.digits 10 y).length < m + 1:= by
  revert y
  induction' m with m ih
  · intro y hy
    obtain rfl: y = 0 := by omega
    simp
  intro y hy
  obtain rfl | hyp := Nat.eq_zero_or_pos y
  · simp
  rw [Nat.digits_def' (by norm_num) hyp]
  rw [List.length_cons, add_lt_add_iff_right]
  have h2 : y / 10 < 10 ^ m := by omega
  exact ih h2

lemma digits_sum_mul_pow {m x : ℕ} :
    (Nat.digits 10 (x * 10 ^ m)).sum = (Nat.digits 10 x).sum := by
  cases' x with x
  · simp
  induction' m with m ih
  · simp
  rw [pow_succ]
  rw [Nat.digits_def' (by norm_num) (by positivity)]
  rw [←mul_assoc, Nat.mul_mod, Nat.mod_self, mul_zero, Nat.zero_mod]
  rw [List.sum_cons, zero_add]
  have h10 : 10 ≠ 0 := by norm_num
  rw [mul_div_cancel_right₀ _ h10]
  exact ih

lemma digits_sum (m x y : ℕ)
    (h1 : y < 10^m) :
    (Nat.digits 10 (x * 10^m + y)).sum =
    (Nat.digits 10 (x * 10^m)).sum + (Nat.digits 10 y).sum := by
  cases' x with x
  · simp
  -- choose k such that (digits 10 y).length + k = m
  have h3 : (Nat.digits 10 y).length ≤ m := by
    have h4 := lemma2 h1
    exact Nat.le_of_lt_succ h4
  have ⟨k, hk⟩ : ∃ k, k + (Nat.digits 10 y).length = m := by
    obtain ⟨k, hk⟩ := Nat.le.dest h3
    rw [add_comm] at hk
    exact ⟨k, hk⟩
  nth_rewrite 1 [add_comm, mul_comm]
  nth_rewrite 1 [←hk]
  have one_lt_ten : 1 < 10 := by norm_num
  have h5 := @digits_append_zeroes_append_digits 10 k _ y (Nat.zero_lt_succ x) one_lt_ten
  rw [←h5]
  simp only [List.sum_append]
  simp only [List.sum_replicate, smul_eq_mul, mul_zero, add_zero]
  rw [digits_sum_mul_pow]
  ring

lemma Finset.range_prod_odd
    {n : ℕ} {f : ℕ → ℕ} (hs : ∀ i ∈ Finset.range n, Odd (f i)) :
    Odd (∏ i ∈ Finset.range n, f i) := by
  revert hs
  induction n
  case zero => simp
  case succ n ih =>
    intro hs
    rw [Finset.prod_range_succ, Nat.odd_mul]
    constructor
    · apply ih
      intro i hi
      have : i ∈ Finset.range (n + 1) := by
        rw [Finset.mem_range] at *
        exact Nat.lt_add_right 1 hi
      exact hs i this
    · apply hs
      rw [Finset.mem_range]
      exact lt_add_one n

snip end

determine solution : ℕ → ℕ := fun n ↦ 9 * 2 ^ n

problem usa1992_p1 (n : ℕ) :
    (Nat.digits 10
     (∏ i ∈ Finset.range (n + 1), (10^(2^i) - 1))).sum = solution n := by
  -- we follow the informal proof from
  -- https://prase.cz/kalva/usa/usoln/usol921.html

  -- Induction on n.
  induction' n with n ih
  · simp

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

  have bn_ge_nine : 9 ≤ b n := by
    clear ih
    dsimp [b, a]
    induction n
    case zero => simp
    case succ n ih2 =>
      rw [Finset.prod_range_succ]
      have h10 : 1 ≤ (10 ^ 2 ^ (n + 1) - 1) := by
        have h11 : 2 ≤ 2 ^ (n + 1) := by
          rw [pow_add, pow_one]
          have h12 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
          exact Nat.le_mul_of_pos_left 2 h12
        have one_le_ten : 1 ≤ 10 := by norm_num
        have h13 : 10 ^ 2 ≤ 10 ^ 2 ^ (n + 1) :=
          Nat.pow_le_pow_of_le_right one_le_ten h11
        omega
      exact le_mul_of_le_of_one_le ih2 (ha1 (n + 1))

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

  have h7 : 1 ≤ b n := by
    dsimp [b]
    exact Finset.one_le_prod' fun i a ↦ ha1 i

  -- so b_n = (b_{n-1} - 1)10^N + (10^N - b_{n-1})
  have h6 : b (n + 1) = (b n - 1) * 10 ^(2^(n+1)) + (10 ^(2^(n+1)) - b n) := by
    rw [h4]
    -- TODO: simpler version via zify
    have h5' := h5.le
    have h8 : 10 ^ 2 ^ (n + 1) ≤ b n * 10 ^ 2 ^ (n + 1) :=
      Nat.le_mul_of_pos_left (10 ^ 2 ^ (n + 1)) h7
    rw [←Nat.add_sub_assoc h5']
    nth_rewrite 2 [add_comm]
    rw [Nat.mul_sub_right_distrib, one_mul, Nat.add_sub_of_le h8]

  -- and the digit sum of b_n is just
  -- the digit sum of (b_{n-1} - 1)10^N plus the digit sum of (10^N - b_{n-1}).
  have h8 : (Nat.digits 10 (b (n + 1))).sum =
            (Nat.digits 10 ((b n - 1) * 10 ^ 2 ^ (n+1))).sum +
            (Nat.digits 10 (10^2^(n+1) - b n)).sum := by
   have h9 : 0 < b n := h7
   have h10 := digits_sum (2^(n+1)) (b n - 1) (10^2^(n+1) - b n)
             (Nat.sub_lt_self h9 h5.le) -- ..
   rw [←h10, h4]
   congr 2
   omega

  -- Now b_{n-1} is odd
  have h9 : ∀ n, Odd (b n) := by
    intro n
    dsimp [b]
    suffices H : ∀ i ∈ Finset.range (n + 1), Odd (a i) from
      Finset.range_prod_odd H
    intro i hi
    dsimp [a]
    rw [Nat.odd_iff]
    zify
    have h10 : (((10 ^ 2 ^ i - 1):ℕ):ℤ) = ((10^2^i) : ℤ) - (1:ℤ) := by
      rw[Int.ofNat_sub (Nat.one_le_pow' (2 ^ i) 9)]
      norm_cast
    rw [h10]
    rw [Int.sub_emod, Int.one_emod_two]
    have h11 : (10:ℤ) ^ 2 ^ i % 2 = 0 := by
      have h12 : (10:ℤ) = 2 * 5 := by norm_num
      rw [h12, mul_pow]
      have h13 : 0 < 2^i := by positivity
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h13
      rw [hk, pow_add]
      simp only [Nat.succ_eq_add_one, zero_add, pow_one]
      rw [mul_assoc]
      exact Int.mul_emod_right _ _
    rw [h11]
    norm_num

  -- and so its last digit is non-zero

  have ten_ne_one : 10 ≠ 1 := by norm_num
  have h10 : (Nat.digits 10 (b n)).head! ≠ 0 := by
    rw [Nat.head!_digits ten_ne_one]
    intro h11
    have h12 : 10 ∣ b n := Nat.dvd_of_mod_eq_zero h11
    rw [show 10 = 2 * 5 by norm_num] at h12
    have h13 : 2 ∣ b n := by omega
    have h14 : ¬ 2 ∣ b n := Odd.not_two_dvd_nat (h9 _)
    contradiction

  -- consider Nat.digits 10 (b n)
  -- it's `d :: ds`, where d ≠ 0.
  -- the sum is d + ds.sum
  -- on the other hand, Nat.digits 10 (b n - 1) is (d - 1) :: ds.
  -- so its sum is (d - 1) + ds.sum

  -- Nat.digits 10 (b n) =
  -- List.head! (Nat.digits 10 (b n)) ::
  have one_lt_ten : 1 < 10 := by norm_num

  -- so the digit sum of b_{n-1} - 1 is one less than the digit sum of b_{n-1},
  have h11 : (Nat.digits 10 (b n - 1)).sum = (Nat.digits 10 (b n)).sum - 1 := by
    rw [Nat.digits_def' one_lt_ten (by omega)]
    nth_rewrite 2 [Nat.digits_def' one_lt_ten (by omega)]
    rw [List.sum_cons, List.sum_cons]
    have h13 : b n % 10 ≠ 0 := by
      intro h11
      have h12 : 10 ∣ b n := Nat.dvd_of_mod_eq_zero h11
      rw [show 10 = 2 * 5 by norm_num] at h12
      have h13 : 2 ∣ b n := by omega
      have h14 : ¬ 2 ∣ b n := Odd.not_two_dvd_nat (h9 _)
      contradiction

    have h12 : (b n - 1) / 10 = b n / 10 := by omega
    rw [h12]
    suffices H : (b n - 1) % 10 + 1 = b n % 10 by omega
    omega

  -- and hence is 9·2_{n-1} - 1
  rw [ih, solution] at h11

  -- Multiplying by 10N does not change the digit sum.
  rw [digits_sum_mul_pow, h11] at h8
  clear h11

  -- (10^N - 1) - b_{n-1} has 2^n digits,
  -- each 9 minus the corresponding digit of b_{n-1},

  -- so its digit sum is 9·2^n - 9·2^{n-1}.

  -- b_{n-1} is odd, so its last digit is not 0
  -- and hence the last digit of (10^N - 1) - b_{n-1} is not 9.

  -- So the digit sum of 10^N - b_{n-1} is 9·2^n - 9·2^{n-1} + 1.

  -- Hence b_n has digit sum (9·2^{n-1} - 1) + (9·2n - 9·2^{n-1} + 1) = 9·2^n.

  sorry


end Usa1992P1
