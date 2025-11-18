/-
Copyright (c) 2023 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# USA Mathematical Olympiad 1981, Problem 5

Show that for any positive real number x and any nonnegative
integer n,

    ∑ₖ (⌊kx⌋/k) ≤ ⌊nx⌋

where the sum goes from k = 1 to k = n, inclusive.
-/

namespace Usa1981P5

problem usa1981_p5 (x : ℝ) (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, ((⌊k * x⌋:ℝ)/k) ≤ ⌊n * x⌋ := by
  -- We follow the solution from
  -- https://artofproblemsolving.com/wiki/index.php/1981_USAMO_Problems/Problem_5

  simp_rw [←Int.self_sub_fract, sub_div, mul_div_right_comm]
  rw [Finset.sum_sub_distrib]
  have h1 : ∀ x1 ∈ Finset.Icc 1 n, (x1 : ℝ) / (x1 : ℝ) * x = x := fun x1 hx ↦ by
    rw [Finset.mem_Icc] at hx
    replace hx := hx.1;
    field_simp
  rw [Finset.sum_congr rfl h1]
  have h2 : ∑ _x ∈ Finset.Icc 1 n, x = n * x := by
    rw [Finset.sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul]
  rw [h2]
  suffices H : Int.fract (↑n * x) ≤
               ∑ x_1 ∈ Finset.Icc 1 n, Int.fract (↑x_1 * x) / ↑x_1 from
    sub_le_sub_left H (↑n * x)

  let a : ℕ → ℝ := fun k ↦ Int.fract (k * x)

  have h4 : ∀ k m, a (k + m) ≤ a k + a m := fun k m ↦ by
    dsimp only [a]
    have h5 : ↑(k + m) * x = ↑ k * x + ↑m * x := by
      push_cast; exact add_mul (↑k) (↑m) x
    rw [h5]
    exact Int.fract_add_le (↑k * x) (↑m * x)

  change a n ≤ ∑ ii ∈ Finset.Icc 1 n, a ii / ii

  clear h1 h2
  induction' n using Nat.strongRecOn with n ih
  obtain rfl | hn := Nat.eq_zero_or_pos n
  · simp [a]

  have : Nonempty (Finset.Icc 1 n) :=
    ⟨1, Finset.left_mem_Icc.mpr (Nat.succ_le_of_lt hn)⟩
  obtain ⟨⟨m, hm1⟩, hm2⟩ :=
    Finite.exists_min (fun (m : Finset.Icc 1 n) ↦ a m / m)

  rw [Finset.mem_Icc] at hm1
  obtain ⟨hm3, hm4⟩ := hm1
  have h9 := ih (n - m) (Nat.sub_lt hn hm3)

  have h11 := h4 (n - m) m
  rw [Nat.sub_add_cancel hm4] at h11
  have h12 : 1 ≤ n - m + 1 := Nat.le_add_left 1 (n - m)
  have h13 : n - m + 1 ≤ n + 1 := by
    rw [Nat.add_le_add_iff_right]
    exact Nat.sub_le n m
  rw [show Finset.Icc 1 n = Finset.Ico 1 (n + 1) by rfl]
  rw [show Finset.Icc 1 (n - m) = Finset.Ico 1 (n - m + 1) by rfl] at h9
  rw [←Finset.sum_Ico_consecutive _ h12 h13]
  have h14 : a m ≤ ∑ i ∈ Finset.Ico (n - m + 1) (n + 1), a i / ↑i := by
    have h15 : m ≠ 0 := Nat.pos_iff_ne_zero.mp hm3
    have h16 : (m:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h15
    have h17 : a m = m * a m / m := CancelDenoms.cancel_factors_eq_div rfl h16
    rw [h17]
    have h18 : ∀ ii ∈ Finset.Ico (n - m + 1) (n + 1), a m / m ≤ a ii / ii := fun ii hii ↦ by
      have h22 : ii ∈ Finset.Icc 1 n := by
        rw [Finset.mem_Ico] at hii
        obtain ⟨hii1, hii2⟩ := hii
        rw [Finset.mem_Icc]
        constructor
        · exact Nat.one_le_of_lt hii1
        · exact Nat.lt_succ_iff.mp hii2
      exact hm2 ⟨ii, h22⟩
    have h19 : ∑ _i ∈ Finset.Ico (n - m + 1) (n + 1), a m / ↑m ≤
               ∑ i ∈ Finset.Ico (n - m + 1) (n + 1), a i / ↑i := Finset.sum_le_sum h18
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul] at h19
    have h20 : n + 1 - (n - m + 1) = m := by
      rw [Nat.add_sub_add_right]
      exact Nat.sub_sub_self hm4
    rw [h20, ←mul_div_assoc] at h19
    exact h19
  calc _ ≤ a (n - m) + a m := h11
       _ ≤ _ := add_le_add h9 h14


end Usa1981P5
