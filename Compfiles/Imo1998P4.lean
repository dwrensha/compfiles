/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InternLM-MATH LEAN Formalizer v0.1, Benpigchu
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Olympiad 1998, Problem 4

Determine all pairs (a, b) of positive integers such that ab^2 + b + 7 divides a^2b + a + b.
-/

namespace Imo1998P4

determine solution_set : Set (ℤ × ℤ) := {(11, 1), (49, 1)} ∪
  {(x,y) | ∃ k : ℤ , (0 < k ∧ x = 7 * k^2 ∧ y = 7 * k)}

problem imo1998_p4 (a b : ℤ) :
    (0 < a ∧ 0 < b ∧ a * b^2 + b + 7 ∣ a^2 * b + a + b) ↔
    (a, b) ∈ solution_set := by
  constructor
  · rintro ⟨ha, hb, h⟩
    simp
    have h' := dvd_mul_of_dvd_left h b
    rw [← @Int.dvd_add_mul_self _ _ (-a)] at h'
    ring_nf at h'
    by_cases hab : -(a * 7) + b ^ 2 = 0
    · right
      have hk : 7 ∣ b ^ 2:= by
        rw [← sub_zero (b ^ 2), ← hab]
        ring_nf
        exact Int.dvd_mul_left a 7
      apply Prime.dvd_of_dvd_pow (Int.prime_ofNat_iff.mpr Nat.prime_seven) at hk
      rw [dvd_iff_exists_eq_mul_left] at hk
      rcases hk with ⟨k, hk⟩
      use k
      constructorm* _ ∧ _
      · lia
      · grind
      · grind
    · left
      by_cases hab' : 0 < -(a * 7) + b ^ 2
      · have hab'':= Int.le_of_dvd hab' h'
        exfalso
        rw [← lt_self_iff_false (-(a * 7) + b ^ 2)]
        calc -(a * 7) + b ^ 2
            < b ^ 2 := (add_lt_iff_neg_right _).mpr (neg_lt_zero.mpr (by positivity:_))
          _ ≤ a * b ^ 2 := le_mul_of_one_le_left (by positivity:_) (by lia:_)
          _ < 7 + a * b ^ 2 := (lt_add_iff_pos_left _).mpr (by norm_num:_)
          _ < 7 + a * b ^ 2 + b := (lt_add_iff_pos_right _).mpr hb
          _ ≤ -(a * 7) + b ^ 2 := hab''
      · have hab''' : 0 < -(-(a * 7) + b ^ 2) := by lia
        rw [← dvd_neg] at h'
        have hab'' := Int.le_of_dvd hab''' h'
        have hb' : b < 3 := by
          contrapose! hab''
          ring_nf
          calc a * 7 - b ^ 2
          _ < a * 7 := sub_lt_self _ (by positivity:_)
          _ ≤ a * 9 := (mul_le_mul_iff_right₀ ha).mpr (by norm_num:_)
          _ = a * 3 ^ 2 := by rw [(by norm_num:(3 : ℤ) ^ 2 = 9)]
          _ ≤ a * b ^ 2 := (mul_le_mul_iff_right₀ ha).mpr (pow_le_pow_left₀ (by norm_num:_) hab'' 2)
          _ < 7 + a * b ^ 2 := (lt_add_iff_pos_left _).mpr (by norm_num:_)
          _ < 7 + a * b ^ 2 + b := (lt_add_iff_pos_right _).mpr hb
        interval_cases b
        · have h'' := dvd_mul_of_dvd_left h' (-1)
          rw [← @Int.dvd_add_mul_self _ _ 7] at h''
          ring_nf at h''
          have ha'' := Int.le_of_dvd (by norm_num:_) h''
          have ha''' : a ≤ 49 := by lia
          interval_cases a <;> norm_num at h'' <;> norm_num
        · have h'' := dvd_mul_of_dvd_left h' (-4)
          rw [← @Int.dvd_add_mul_self _ _ 7] at h''
          ring_nf at h''
          have ha'' := Int.le_of_dvd (by norm_num:_) h''
          have ha''' : a ≤ 17 := by lia
          interval_cases a <;> norm_num at h''
  · intro h
    simp at h
    casesm* _ ∨ _
    · rcases h with ⟨ha, hb⟩
      rw [ha, hb]
      norm_num
    · rcases h with ⟨ha, hb⟩
      rw [ha, hb]
      norm_num
    · rcases h with ⟨k, hk, ha, hb⟩
      rw [ha, hb]
      constructorm* _ ∧ _
      · positivity
      · positivity
      · rw [dvd_iff_exists_eq_mul_left]
        use k
        ring

end Imo1998P4
