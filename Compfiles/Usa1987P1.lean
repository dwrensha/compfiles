/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# USA Mathematical Olympiad 1987, Problem 1

Determine all solutions to

     (m² + n)(m + n²) = (m - n)³

where m and n are non-zero integers.
-/

namespace Usa1987P1

snip begin

lemma lemma2 {a b c : ℤ} (h : a * b^2 = c^2) : IsSquare a ∨ b = 0 := by
  obtain rfl | hb := eq_or_ne b 0
  · right; rfl
  simp only [hb, or_false]
  -- from Eric Wieser on Zulip
  -- https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/a.20*.20b.5E2.20.3D.20c.5E2.20implies.20IsSquare.20a/near/406203283
  have h1 : b^2 ∣ c^2 := Dvd.intro_left a h
  rw [Int.pow_dvd_pow_iff two_ne_zero] at h1
  obtain ⟨k, rfl⟩ := h1
  rw [mul_pow, mul_comm, mul_right_inj' (pow_ne_zero _ hb)] at h
  rw [h]
  exact ⟨k, sq k⟩

snip end

determine solution_set : Set (ℤ × ℤ) :=
  { (-1, -1), (8, -10), (9, -6), (9, -21) }

problem usa1987_p1 (m n : ℤ) :
    (m, n) ∈ solution_set ↔
    m ≠ 0 ∧ n ≠ 0 ∧ (m^2 + n) * (m + n^2) = (m - n)^3 := by
  -- Follows the informal solution at
  -- https://artofproblemsolving.com/wiki/index.php/1987_USAMO_Problems/Problem_1
  constructor
  · aesop
  · rintro ⟨h1, h2, h3⟩
    have h4 : n * (m  + m^2 * n + n^2) =
              n * (- 3* m^2 + 3 * m * n - n^2) := by linear_combination h3
    replace h4 : (m  + m^2 * n + n^2) =
              (- 3 * m^2 + 3 * m * n - n^2) := (Int.mul_eq_mul_left_iff h2).mp h4
    have h5 : 2 * (n * n)  + (m^2 - 3 * m) * n + (3 * m^2 + m) = 0 := by
      linarith
    have h6 := (quadratic_eq_zero_iff_discrim_eq_sq two_ne_zero n).mp h5
    have h7 : discrim 2 (m ^ 2 - 3 * m) (3 * m ^ 2 + m) =
              m * (m - 8) * (m + 1)^2 := by rw [discrim]; ring
    rw [h7] at h6; clear h7
    have h8 : IsSquare (m * (m - 8)) ∨ m + 1 = 0 := lemma2 h6
    obtain rfl | hm := eq_or_ne m (-1)
    · norm_num at h6
      obtain rfl : n = -1 := by linarith [pow_eq_zero h6.symm]
      simp only [Set.mem_insert_iff, true_or]
    have h9 : m + 1 ≠ 0 := fun hm1 ↦ hm (Int.sub_eq_zero.mp hm1)
    replace h8 := Or.resolve_right h8 h9
    obtain ⟨k, hk⟩ := h8
    have h11 : 1 * (m * m) + - 8 * m + - k * k = 0 := by linarith
    have h12 := (quadratic_eq_zero_iff_discrim_eq_sq one_ne_zero m).mp h11
    rw [discrim] at h12
    have h13 : 16 + (k * k) = (m -4) ^ 2 := by linarith only [h12]
    let m' := |m - 4|
    have hm' : (m - 4)^2 = m'^2 := (sq_abs _).symm
    have hm0' : 0 ≤ m' := abs_nonneg _

    let k' := |k|
    have hk' : k^2 = k'^2 := (sq_abs _).symm
    have hk0' : 0 ≤ k' := abs_nonneg _

    rw [ ←sq] at h13
    have h20 : k' < 8 := by
      by_contra! H
      rw [hm', hk'] at h13
      have h14 : k' < m' := by
        have h14' : k'^2 < m'^2 := by
          rw [←h13]; exact Int.lt_add_of_pos_left _ (by norm_num)
        exact lt_of_pow_lt_pow_left₀ 2 hm0' h14'
      have h15 : k' + 1 ≤ m' := h14
      have h16 : (k' + 1)^2 ≤ m'^2 := by gcongr
      rw [←h13] at h16
      have h17 : 2 * k' + 1 ≤ 16 := by linarith only [h16]
      have h18 : 2 * 8 + 1 ≤ 2 * k' + 1 := by gcongr
      have h19 := h18.trans h17
      norm_num at h19
    interval_cases k' <;> rw [hk'] at h13 <;> norm_num at h13
    · rw [hm'] at h13
      have h21 : m' = 4 := by nlinarith only [h13, hm0']
      obtain h25 | h25 := eq_or_eq_neg_of_abs_eq h21
      · obtain rfl : m = 8 := eq_add_of_sub_eq h25
        norm_num at h6
        obtain rfl : n = -10 := by linarith [pow_eq_zero h6.symm]
        simp only [Set.mem_insert_iff, true_or, or_true]
      · exact (h1 (sub_eq_neg_self.mp h25)).elim
    · rw [hm'] at h13
      have h21 : 4^2 < m'^2 := by rw [←h13]; norm_num
      have h23 : 4 < m' := lt_of_pow_lt_pow_left₀ 2 hm0' h21
      have h22 : m'^2 < 5^2 := by rw [←h13]; norm_num
      have h24 : m' < 5 := lt_of_pow_lt_pow_left₀ 2 (by norm_num) h22
      exact (Int.not_le.mpr h24 h23).elim
    · rw [hm'] at h13
      have h21 : 4^2 < m'^2 := by rw [←h13]; norm_num
      have h23 : 4 < m' := lt_of_pow_lt_pow_left₀ 2 hm0' h21
      have h22 : m'^2 < 5^2 := by rw [←h13]; norm_num
      have h24 : m' < 5 := lt_of_pow_lt_pow_left₀ 2 (by norm_num) h22
      exact (Int.not_le.mpr h24 h23).elim
    · rw [hm'] at h13
      have h21 : m' = 5 := by nlinarith only [hm0', h13]
      obtain h25 | h25 := eq_or_eq_neg_of_abs_eq h21
      · have h26 : m = 9 := eq_add_of_sub_eq h25
        rw [h26] at h6 ⊢
        norm_num at h6
        have h27 : (30:ℤ)^2 = (4 * n + 54) ^2 := by linear_combination h6
        obtain h28 | h28 := eq_or_eq_neg_of_sq_eq_sq _ _ h27
        · obtain rfl : n = -6 := by linarith only [h28]
          simp only [Set.mem_insert_iff, true_or, or_true]
        · obtain rfl : n = -21 := by linarith only [h28]
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_true]
      · omega
    · rw [hm'] at h13
      have h21 : 5^2 < m'^2 := by rw [←h13]; norm_num
      have h23 : 5 < m' := lt_of_pow_lt_pow_left₀ 2 hm0' h21
      have h22 : m'^2 < 6^2 := by rw [←h13]; norm_num
      have h24 : m' < 6 := lt_of_pow_lt_pow_left₀ 2 (by norm_num) h22
      exact (Int.not_le.mpr h24 h23).elim
    · rw [hm'] at h13
      have h21 : 6^2 < m'^2 := by rw [←h13]; norm_num
      have h23 : 6 < m' := lt_of_pow_lt_pow_left₀ 2 hm0' h21
      have h22 : m'^2 < 7^2 := by rw [←h13]; norm_num
      have h24 : m' < 7 := lt_of_pow_lt_pow_left₀ 2 (by norm_num) h22
      exact (Int.not_le.mpr h24 h23).elim
    · rw [hm'] at h13
      have h21 : 7^2 < m'^2 := by rw [←h13]; norm_num
      have h23 : 7 < m' := lt_of_pow_lt_pow_left₀ 2 hm0' h21
      have h22 : m'^2 < 8^2 := by rw [←h13]; norm_num
      have h24 : m' < 8 := lt_of_pow_lt_pow_left₀ 2 (by norm_num) h22
      exact (Int.not_le.mpr h24 h23).elim
    · rw [hm'] at h13
      have h21 : 8^2 < m'^2 := by rw [←h13]; norm_num
      have h23 : 8 < m' := lt_of_pow_lt_pow_left₀ 2 hm0' h21
      have h22 : m'^2 < 9^2 := by rw [←h13]; norm_num
      have h24 : m' < 9 := lt_of_pow_lt_pow_left₀ 2 (by norm_num) h22
      exact (Int.not_le.mpr h24 h23).elim


end Usa1987P1
