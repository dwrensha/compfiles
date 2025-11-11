/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw, Benpigchu
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Olympiad 2003, Problem 2

Determine all pairs of positive integers (a,b) such that

                  a²/(2ab² - b³ + 1)

is a positive integer.
-/

namespace Imo2003P2

snip begin

lemma aux₁ {n : ℤ} (hn : 0 < n) : 1 < 8 * n ^ 3 := by
  apply lt_of_lt_of_le (by norm_num : (1 : ℤ) < 8)
  nth_rw 1 [← mul_one 8]
  rw [mul_le_mul_iff_right₀ (by norm_num : _)]
  apply Int.le_of_lt_add_one
  rw [lt_add_iff_pos_left]
  positivity

snip end

determine solution_set : Set (ℤ × ℤ) := {(a, b) | ∃ n : ℤ, 0 < n ∧ a = 2 * n ∧ b = 1}
  ∪ {(a, b) | ∃ n : ℤ, 0 < n ∧ a = n ∧ b = 2 * n}
  ∪ {(a, b) | ∃ n : ℤ, 0 < n ∧ a = 8 * n ^ 4 - n ∧ b = 2 * n}

problem imo2003_p2 (a b : ℤ) :
    (a,b) ∈ solution_set ↔
    0 < a ∧ 0 < b ∧
    ∃ c, 0 < c ∧ c * (2 * a * b^2 - b^3 + 1) = a^2 := by
  constructor
  · rintro ((hab|hab)|hab) <;> rcases hab with ⟨n, hn, hna, hnb⟩ <;> rw [hna, hnb]
    · constructorm* _ ∧ _
      · positivity
      · norm_num
      · use n
        constructor
        · positivity
        · ring
    · constructorm* _ ∧ _
      · positivity
      · positivity
      · use n ^ 2
        constructor
        · positivity
        · ring
    · constructorm* _ ∧ _
      · rw [sub_pos]
        rw [(by ring : 8 * n ^ 4 = n * (8 * n ^ 3))]
        apply lt_mul_right hn
        apply aux₁ hn
      · positivity
      · use n ^ 2
        constructor
        · positivity
        · ring
  · rintro ⟨ha, hb, ⟨c, hc, habc⟩⟩
    have habc' : a * a - (2 * b ^ 2 * c) * a + (b ^ 3 - 1) * c = 0 := by
      rw [← pow_two, ← habc]
      ring
    rw [solution_set, Set.union_assoc]
    rcases vieta_formula_quadratic habc' with ⟨a', ha', haa'₀, haa'₁⟩
    by_cases! ha'0 : a' = 0
    · left
      rw [ha'0, mul_zero] at haa'₁
      symm at haa'₁
      rw [mul_eq_zero_iff_right (by cutsat : _), sub_eq_zero] at haa'₁
      rw [pow_eq_one_iff_of_ne_zero (by norm_num : _)] at haa'₁
      norm_num at haa'₁
      rw [ha'0, haa'₁] at haa'₀
      norm_num at haa'₀
      use c
    · right
      have ha'_pos : 0 < a' := by
        apply lt_of_le_of_ne _ ha'0.symm
        rw [← mul_nonneg_iff_of_pos_left ha, haa'₁]
        rw [mul_nonneg_iff_of_pos_right hc, sub_nonneg]
        apply Int.le_of_lt_add_one
        rw [lt_add_iff_pos_left]
        positivity
      wlog ha_le_a' : a ≤ a' generalizing a a'
      · have ha'bc : c * (2 * a' * b ^ 2 - b ^ 3 + 1) = a' ^ 2 := by
          rw [sub_add, sub_eq_zero] at ha'
          rw [pow_two a', ha']
          ring
        rw [add_comm] at haa'₀
        rw [mul_comm] at haa'₁
        have h := this a' ha'_pos ha'bc ha' a habc' haa'₀ haa'₁ (by cutsat : _) ha (by cutsat : _)
        rcases h with (ha'b|ha'b) <;> rcases ha'b with ⟨n, hn, hna', hnb⟩ <;> rw [hna', hnb] at haa'₀ ha'
        · right
          use n, hn
          have hc' : c = n ^ 2 := by
            rw [← add_zero c, ← ha']
            ring
          rw [hc'] at haa'₀
          constructor
          · apply @Int.add_left_cancel n
            rw [haa'₀]
            ring
          · exact hnb
        · left
          use n, hn
          have hn' : 0 < (8 * n ^ 3 - 1) ^ 2 := by
            apply pow_pos
            rw [sub_pos]
            apply aux₁ hn
          have hc' : c = n ^ 2 := by
            rw [← mul_right_cancel_iff_of_pos hn', ← add_zero (c * (8 * n ^ 3 - 1) ^ 2), ← ha']
            ring
          rw [hc'] at haa'₀
          constructor
          · apply @Int.add_left_cancel (8 * n ^ 4 - n)
            rw [haa'₀]
            ring
          · exact hnb
      left
      have hba : b ≤ 2 * a := by
        rw [← sub_nonneg, ← mul_nonneg_iff_of_pos_left (by positivity : 0 < b ^ 2)]
        rw [← add_le_add_iff_right 1, Int.add_one_le_iff, ← mul_pos_iff_of_pos_left hc]
        rw [(by ring : c * (b ^ 2 * (2 * a - b) + 1) = c * (2 * a * b ^ 2 - b ^ 3 + 1)), habc]
        positivity
      by_cases! hba' : b = 2 * a
      · use a
      · exfalso
        have h' := ha_le_a'
        rw [← mul_le_mul_iff_of_pos_left ha, ← pow_two, ← habc, haa'₁] at h'
        rw [mul_comm, mul_le_mul_iff_of_pos_right hc, ← sub_nonneg] at h'
        have hab : a < b := by
          rw [← sub_pos, ← mul_pos_iff_of_pos_left (by positivity : 0 < b ^ 2)]
          rw [← Int.add_one_le_iff, ← sub_nonneg]
          rw [← mul_nonneg_iff_of_pos_left (by positivity : (0 : ℤ) < 2)]
          rw [(by ring : 2 * (b ^ 2 * (b - a) - (0 + 1)) = b ^ 3 - 1 - (2 * a * b ^ 2 - b ^ 3 + 1))]
          exact h'
        have hba'' := lt_of_le_of_ne hba hba'
        have h'' :  b ^ 2 < 2 * a * b ^ 2 - b ^ 3 + 1 := by
          rw [← Int.add_one_le_iff, add_le_add_iff_right]
          rw [(by ring : 2 * a * b ^ 2 - b ^ 3 = b ^ 2 * (2 * a - b))]
          rw [le_mul_iff_one_le_right (by positivity : _), ← zero_add 1]
          rw [Int.add_one_le_iff, sub_pos]
          exact hba''
        contrapose! habc
        apply ne_of_gt
        calc a ^ 2
            < b ^ 2 := by
              rw [pow_lt_pow_iff_left₀ (by cutsat : _) (by cutsat : _) (by norm_num : _)]
              exact hab
          _ ≤ c * b ^ 2 := by
              rw [le_mul_iff_one_le_left (by positivity : _)]
              cutsat
          _ < c * (2 * a * b ^ 2 - b ^ 3 + 1) := by
              rw [mul_lt_mul_iff_of_pos_left hc]
              exact h''


end Imo2003P2
