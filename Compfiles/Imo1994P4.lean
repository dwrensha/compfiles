/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benpigchu
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Olympiad 1994, Problem 4

Determine all ordered pairs of positive integers (m, n) such that

            (n³ + 1) / (mn - 1)

is an integer.
-/

namespace Imo1994P4

snip begin

lemma nonneg_mul_eq_two {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b)
  (hab: a * b = 2) : (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1) := by
  have ha_pos : 0 < a := by lia
  have hb' : b ≤ 2 := by
    rw [← hab]
    calc b
        = 1 * b := by rw [one_mul]
      _ ≤ a * b := by apply mul_le_mul <;> lia
  interval_cases b <;> lia

lemma aux₁ {a b c d : ℤ}
  (hc : 0 < c) (hd : 0 < d)
  (h₁ : a * b = c + d) (h₂ : a + b = c * d) (ha': a = 1) :
  (a = 1 ∧ b = 5 ∧ c = 3 ∧ d = 2) ∨ (a = 1 ∧ b = 5 ∧ c = 2 ∧ d = 3) := by
  rw [ha'] at h₁ h₂
  rw [one_mul] at h₁
  rw [h₁] at h₂
  have hcd : (c - 1) * (d - 1) = 2 := by grind
  have hcd' := by apply nonneg_mul_eq_two _ _ hcd <;> lia
  lia

lemma aux₂ {a b c d : ℤ}
  (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 2 ≤ d)
  (h₁ : a * b = c + d) (h₂ : a + b = c * d) (ha' : a ≠ 2): False := by
  rw [← lt_self_iff_false (a * b)]
  calc a * b
      = c + d := h₁
    _ ≤ c + d + ((c - 1) * (d - 1) - 1) := by
      apply le_add_of_nonneg_right
      rw [sub_nonneg]
      nth_rw 1 [← one_mul 1]
      apply mul_le_mul <;> lia
    _ = c * d := by ring
    _ = a + b := h₂.symm
    _ < a + b + ((a - 1) * (b - 1) - 1) := by
      apply lt_add_of_pos_right
      apply Int.lt_of_le_sub_one
      rw [sub_nonneg, le_sub_iff_add_le, ← mul_one (1 + 1)]
      apply mul_le_mul <;> lia
    _ = a * b := by ring

snip end

determine SolutionSet : Set (ℤ × ℤ) := {
  (2, 2), (5, 3), (5, 2), (1, 3), (1, 2),
  (3, 5), (2, 5), (3, 1), (2, 1)
}

problem imo1994_p4 (m n : ℤ) :
    (m, n) ∈ SolutionSet ↔
    0 < m ∧ 0 < n ∧ (m * n - 1) ∣ (n^3 + 1) := by
  constructor
  · intro hmn
    simp at hmn
    casesm* _ ∨ _ <;> rw [hmn.left, hmn.right] <;> norm_num
  · rintro ⟨hm, hn, hmn⟩
    rcases dvd_iff_exists_eq_mul_left.mp hmn with ⟨k, hk⟩
    rw [pow_three] at hk
    have hk'_pos : 0 < k * (m * n - 1) := by
      rw [← hk]
      positivity
    have hk_pos : 0 < k := by
      apply pos_of_mul_pos_left hk'_pos
      rw [sub_nonneg]
      calc 1
          = 1 * 1 := by norm_num
        _ ≤ m * n := by apply mul_le_mul <;> lia
    have hk' : k + 1 = n * (k * m - n * n) := by grind
    set s := k * m - n * n with hs
    have hs_pos' : 0 < n * s := by lia
    have hs_pos : 0 < s := pos_of_mul_pos_right hs_pos' (le_of_lt hn)
    have hs' : m + s = n * (s * m - n) := by grind
    set t := s * m - n with ht
    have ht_pos' : 0 < n * t := by lia
    have ht_pos : 0 < t := pos_of_mul_pos_right ht_pos' (le_of_lt hn)
    have ht' : m * s = n + t := by grind
    by_cases hmnst : m = 1 ∨ n = 1 ∨ s = 1 ∨ t = 1
    · casesm* _ ∨ _
      · have h := aux₁ hn ht_pos ht' hs' hmnst
        rcases h with (h'|h') <;> rcases h' with ⟨hm', _, hn', _⟩ <;> rw [hm', hn'] <;> simp
      · have h := aux₁ hm hs_pos hs'.symm ht'.symm hmnst
        rcases h with (h'|h') <;> rcases h' with ⟨hn', _, hm', _⟩ <;> rw [hn', hm'] <;> simp
      · rw [mul_comm] at ht'
        rw [add_comm] at hs'
        have h := aux₁ hn ht_pos ht' hs' hmnst
        rcases h with (h'|h') <;> rcases h' with ⟨_, hm', hn', _⟩ <;> rw [hn', hm'] <;> simp
      · rw [add_comm] at ht'
        rw [mul_comm] at hs'
        have h := aux₁ hm hs_pos hs'.symm ht'.symm hmnst
        rcases h with (h'|h') <;> rcases h' with ⟨_, hn', hm', _⟩ <;> rw [hn', hm'] <;> simp
    · push_neg at hmnst
      have hmnst'' : 2 ≤ m ∧ 2 ≤ n ∧ 2 ≤ s ∧ 2 ≤ t := by lia
      rcases hmnst'' with ⟨h'm, h'n, h's, h't⟩
      by_cases hmnst' : m ≠ 2 ∨ n ≠ 2
      · apply False.elim
        casesm* _ ∨ _
        · exact aux₂ h'm h's h'n h't ht' hs' hmnst'
        · exact aux₂ h'n h't h'm h's hs'.symm ht'.symm hmnst'
      · push_neg at hmnst'
        rcases hmnst' with ⟨hm2, hn2⟩
        rw [hm2, hn2]
        simp

end Imo1994P4
