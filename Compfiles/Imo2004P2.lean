/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benpigchu
-/

import Mathlib.Tactic

import ProblemExtraction

set_option backward.isDefEq.respectTransparency false

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 2004, Problem 2

Find all polynomials P with real coefficients such that
for all reals a,b,c such that ab + bc + ca = 0 we have

    P(a - b) + P(b - c) + P(c - a) = 2P(a + b + c).
-/

namespace Imo2004P2

open Polynomial

determine SolutionSet : Set (Polynomial ℝ) := {P | ∃ s t : ℝ, P = s • X ^ 4 + t • X ^ 2}

problem imo2004_p2 (P : Polynomial ℝ) :
    P ∈ SolutionSet ↔
    ∀ a b c, a * b + b * c + c * a = 0 →
      P.eval (a - b) + P.eval (b - c) + P.eval (c - a) =
      2 * P.eval (a + b + c) := by
  constructor
  · rintro ⟨s, t, hp⟩ a b c habc
    simp [hp]
    rw [← sub_eq_zero]
    rw [← zero_mul (- 6 * t - 6 * s * (a * b + b * c + c * a) - 12 * s * (a * a + b * b + c * c)), ← habc]
    ring
  · intro habc
    have hPaPbPc : ∀ Pa Pb Pc : Polynomial ℝ, Pa * Pb + Pb * Pc + Pc * Pa = 0 →
      P.comp (Pa - Pb) + P.comp (Pb - Pc) + P.comp (Pc - Pa) = 2 * P.comp (Pa + Pb + Pc) := by
      intro Pa Pb Pc hPaPbPc'
      apply Polynomial.funext
      intro r
      simp only [eval_add, eval_mul, eval_comp, eval_sub, eval_ofNat]
      apply habc (Pa.eval r) (Pb.eval r) (Pc.eval r)
      simp only [← eval_add, ← eval_mul, hPaPbPc', eval_zero]
    use P.coeff 4, P.coeff 2
    apply ext
    intro n
    by_cases! hn : n = 2 ∨ n = 4
    · rcases hn with (hn|hn) <;> rw [hn] <;> simp
    · simp
      repeat rw [if_neg (by tauto : _)]
      rw [add_zero]
      by_cases! hn'' : n = 0
      · have h := habc 0 0 0 (by ring : _)
        simp at h
        rw [← coeff_zero_eq_eval_zero] at h
        rw [← sub_eq_zero] at h
        ring_nf at h
        rw [hn'', h]
      · by_cases! hn' : ¬2 ∣ n
        · have h' := hPaPbPc X 0 0 (by ring : _)
          ring_nf at h'
          rw [ext_iff] at h'
          have h := h' n
          simp only [coeff_add, ← C_ofNat, coeff_mul_C] at h
          rw [neg_eq_neg_one_mul, ← C_1, ← C_neg, comp_C_mul_X_coeff] at h
          rw [comp_X, comp_zero, coeff_C_ne_zero hn'', ← sub_eq_zero, add_zero] at h
          nth_rw 1 [← mul_one (P.coeff n)] at h
          simp only [← mul_add, ← mul_sub] at h
          apply (mul_eq_zero_iff_right _).mp h
          contrapose! hn'
          ring_nf at hn'
          rw [neg_add_eq_sub, sub_eq_zero] at hn'
          rw [neg_one_pow_eq_one_iff_even (by norm_num : _), even_iff_two_dvd] at hn'
          exact hn'
        · have hn''' : 6 ≤ n := by
            contrapose! hn'
            interval_cases n <;> norm_num at *
          have h' := hPaPbPc (- 2 • X) (3 • X) (6 • X) (by ring : _)
          ring_nf at h'
          rw [ext_iff] at h'
          have h := h' n
          simp only [coeff_add, ← C_ofNat, coeff_mul_C, X_mul_C, ← neg_mul, ← C_neg, comp_C_mul_X_coeff] at h
          rw [← sub_eq_zero] at h
          simp only [← mul_add, mul_assoc, ← mul_sub] at h
          apply (mul_eq_zero_iff_right _).mp h
          apply ne_of_gt
          repeat rw [neg_pow, (neg_one_pow_eq_one_iff_even (by norm_num : _)).mpr (even_iff_two_dvd.mpr hn'), one_mul]
          rw [sub_pos]
          calc (7 : ℝ) ^ n * 2
              < 7 ^ n * (8 / 7) ^ 6 := by
                rw [mul_lt_mul_iff_of_pos_left (by positivity : _)]
                norm_num
            _ ≤ 7 ^ n * (8 / 7) ^ n := by
                rw [mul_le_mul_iff_of_pos_left (by positivity : _)]
                rw [pow_le_pow_iff_right₀ (by norm_num : _)]
                exact hn'''
            _ = 8 ^ n := by rw [← mul_pow, mul_div_cancel₀ 8 (by norm_num : _)]
            _ < 5 ^ n + 3 ^ n + 8 ^ n := by
                rw [lt_add_iff_pos_left]
                positivity


end Imo2004P2
