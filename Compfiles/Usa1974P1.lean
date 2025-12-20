/-
Copyright (c) 2025 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maximiliano Onofre Martínez
-/

import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Polynomial.Div

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# USA Mathematical Olympiad 1974, Problem 1

Let a, b, c be three distinct integers, and let P be a polynomial
with integer coefficients. Show that in this case the conditions
P (a) = b, P (b) = c, P (c) = a cannot be satisfied simultaneously.
-/

open Int

open Polynomial

namespace Usa1974P1

problem usa1974_p1 {P : Polynomial ℤ} (a b c : ℤ) (h_neq : a ≠ b ∧ b ≠ c ∧ c ≠ a) :
  ¬(P.eval a = b ∧ P.eval b = c ∧ P.eval c = a) := by
  intro h
  rcases h with ⟨h_a, h_b, h_c⟩

  have h_ab_bc : a - b ∣ b - c := by
    nth_rw 2 [← h_a]; rw [← h_b]
    exact sub_dvd_eval_sub a b P

  have h_bc_ca : b - c ∣ c - a := by
    nth_rw 2 [← h_b]; rw [← h_c]
    exact sub_dvd_eval_sub b c P

  have h_ca_ab : c - a ∣ a - b := by
    nth_rw 2 [← h_c]; rw [← h_a]
    exact sub_dvd_eval_sub c a P

  have h_ab_ca : a - b ∣ c - a := dvd_trans h_ab_bc h_bc_ca

  have h_abs_ac : (a - b).natAbs = (c - a).natAbs := natAbs_eq_of_dvd_dvd h_ab_ca h_ca_ab
  rw [natAbs_eq_natAbs_iff] at h_abs_ac

  rcases h_abs_ac with h_eq_ac | h_neg_ac
  · rw [h_eq_ac] at h_ab_bc
    have h_abs_bc : (c - a).natAbs = (b - c).natAbs := natAbs_eq_of_dvd_dvd h_ab_bc h_bc_ca
    rw [natAbs_eq_natAbs_iff] at h_abs_bc
    rcases h_abs_bc with h_eq_bc | h_neg_bc <;> grind
  aesop

end Usa1974P1
