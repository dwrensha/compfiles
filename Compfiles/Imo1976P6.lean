/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InternLM-MATH LEAN Formalizer v0.1, Aristotle-Harmonic, David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 1976, Problem 6

The sequence u_0, u_1, u_2, ... is defined by:
u_0 = 2, u_1 = 5/2, u_{n+1} = u_n(u_{n-1}^2 - 2) - u_1 for n = 1, 2, ... .
Prove that ⌊u_n⌋ = 2^(2^n - (-1)^n)/3 for all positive n,
where ⌊x⌋ denotes the greatest integer less than or equal to x.
-/

namespace Imo1976P6

problem imo1976_p6 (u : ℕ → ℝ)
    (h₀ : u 0 = 2)
    (h₁ : u 1 = 5 / 2)
    (h₂ : ∀ n, u (n + 2) = u (n + 1) * ((u n) ^ 2 - 2) - u 1) :
      ∀ n > 0, ⌊u n⌋  = (2 : ℝ) ^ ((2^n - (-1 : ℝ) ^ n) / 3) := by
  have h_ind : ∀ n, u n = 2 ^ ((2 ^ n - (-1) ^ n) / 3 : ℝ) +
                          2 ^ ((-2 ^ n + (-1) ^ n) / 3 : ℝ) := by
    intro n
    induction' n using Nat.strong_induction_on with n ih;
    rcases n with ( _ | _ | n ) <;> norm_num
    · exact h₀
    · exact h₁
    simp_all only [lt_add_iff_pos_left, add_pos_iff, Nat.ofNat_pos, or_true, pow_zero,
                   sub_self, zero_div, Real.rpow_zero, neg_add_cancel,
                   zero_lt_one, pow_one, sub_neg_eq_add, lt_add_iff_pos_right]
    ring_nf at * ; norm_num at *;
    rw [ih n (by lia)] ; ring_nf; norm_num [ sq, ← Real.rpow_add ] ; ring_nf;
    obtain h | h := Nat.even_or_odd n <;> norm_num [h.neg_one_pow] <;> ring_nf
  intro n hn_pos
  have h_int : ∃ k : ℤ, (2 : ℝ) ^ ((2 ^ n - (-1) ^ n) / 3 : ℝ) = k := by
    -- We need to show that $(2^n - (-1)^n) / 3$ is an integer.
    have h_int : ∃ k : ℤ, (2^n - (-1)^n) = 3 * k := sub_dvd_pow_sub_pow _ _ _
    simp_all only [pow_zero, sub_self, zero_div, Real.rpow_zero, neg_add_cancel,
                   pow_one, sub_neg_eq_add, gt_iff_lt, Int.reduceNeg]
    obtain ⟨w, h⟩ := h_int
    use 2 ^ w.natAbs
    obtain a | a := w <;> norm_num [ Real.rpow_def_of_pos ] at *
    · simp_all only [Int.reduceNeg]
      norm_num [ ← h, Real.exp_mul, Real.exp_log ];
      norm_num [ show ( 2 ^ n - ( -1 ) ^ n : ℝ ) = 3 * a by exact_mod_cast h ];
    · obtain ⟨w, h_1⟩ := Nat.even_or_odd' n
      simp_all only [Int.reduceNeg]
      cases h_1 with
      | inl h_2 =>
        subst h_2
        simp_all only [Nat.ofNat_pos, mul_pos_iff_of_pos_left, Int.reduceNeg, even_two,
                       Even.mul_right, Even.neg_pow, one_pow]
        lia
      | inr h_3 =>
        subst h_3
        simp_all only [lt_add_iff_pos_left, add_pos_iff, Nat.ofNat_pos, mul_pos_iff_of_pos_left,
                       zero_lt_one, or_true, Int.reduceNeg]
        norm_num [ Int.negSucc_eq ] at h
        linarith [ pow_pos Nat.zero_lt_two ( 2 * w + 1 ) ];
  simp_all only [pow_zero, sub_self, zero_div, Real.rpow_zero, neg_add_cancel,
                 pow_one, sub_neg_eq_add, gt_iff_lt]
  obtain ⟨w, h⟩ := h_int
  simp_all only [Int.floor_intCast_add, Int.cast_add, add_eq_left, Int.cast_eq_zero,
                 Int.floor_eq_zero_iff, Set.mem_Ico]
  apply And.intro
  · positivity
  · rw [ Real.rpow_lt_one_iff ] <;> norm_num
    rcases Nat.even_or_odd' n with ⟨ k, rfl | rfl ⟩ <;> norm_num [ pow_add, pow_mul ] at *;
    · linarith [ pow_le_pow_right₀ ( by norm_num : ( 1 : ℝ ) ≤ 4 ) hn_pos ];
    · linarith [ pow_pos ( by norm_num : ( 0 : ℝ ) < 4 ) k ]

end Imo1976P6
