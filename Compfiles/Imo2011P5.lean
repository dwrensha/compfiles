/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Francesco Cappetti
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Olympiad 2011, Problem 5

Let f be a function from the set of integers to the set
of positive integers. Suppose that, for any two integers
m and n, the difference f(m) - f(n) is divisible by
f (m - n). Prove that, for all integers m and n with
f(m) ≤ f(n), the number f(n) is divisible by f(m).
-/

namespace Imo2011P5

problem imo2011_p5 (f : ℤ → ℤ)
    (f_pos : ∀ n, 0 < f n)
    (h : ∀ m n, f (m - n) ∣ f m - f n)
    : ∀ m n, f m ≤ f n → f m ∣ f n := by
  -- Direct translation of the solution found at
  -- https://artofproblemsolving.com/community/c6h418981p2365084

  have f_n_dvd_f_zero : ∀ n, f n ∣ f 0 := by
    intro n
    have : f n ∣ f n - f 0 := by
      calc f n
        _ = f (n - 0) := by rw [sub_zero]
        _ ∣ f n - f 0 := h n 0
    exact (Int.dvd_iff_dvd_of_dvd_sub this).mp (dvd_refl (f n))

  have f_neg_n_eq_f_n : ∀ n, f (-n) = f n := by
    intro n

    have f_neg_n_dvd_f_n : f (-n) ∣ f n := by
      have :=
        calc f (-n)
          _ = f (0 - n) := by rw [zero_sub]
          _ ∣ f 0 - f n := h 0 n
      exact (Int.dvd_iff_dvd_of_dvd_sub this).mp (f_n_dvd_f_zero (-n))

    have f_n_dvd_f_neg_n : f n ∣ f (-n) := by
      have :=
        calc f n
          _ = f (0 - -n) := by rw [sub_neg_eq_add, zero_add]
          _ ∣ f 0 - f (-n) := h 0 (-n)
      exact (Int.dvd_iff_dvd_of_dvd_sub this).mp (f_n_dvd_f_zero n)

    have f_neg_n_nonneg : 0 ≤ f (-n) := le_of_lt (f_pos (-n))
    have f_n_nonneg : 0 ≤ f n := le_of_lt (f_pos n)

    exact Int.dvd_antisymm f_neg_n_nonneg f_n_nonneg f_neg_n_dvd_f_n f_n_dvd_f_neg_n

  intro m n f_m_le_f_n

  by_cases h0 : f m < f n ∧ ¬f m ∣ f n

  · have h1 : f (m + n) ≤ f n - f m := by
      have := by
        calc f (m + n)
          _ = f (m - -n) := by rw [Int.sub_neg]
          _ ∣ f m - f (-n) := h m (-n)
          _ = f m - f n := by rw [f_neg_n_eq_f_n]
          _ = -(f n - f m) := by rw [neg_sub]
          _ ∣ f n - f m := by rw [neg_dvd]
      have f_n_sub_f_m_pos : 0 < f n - f m := by linarith
      exact Int.le_of_dvd f_n_sub_f_m_pos this

    have h2 : ¬f m ∣ f (n + m) := by
      have :=
        calc f m
          _ = f (n + m - n) := by rw [add_tsub_cancel_left]
          _ ∣ f (n + m) - f n := h (n + m) n
      grind [Int.dvd_iff_dvd_of_dvd_sub]

    have h3 : |f (n + m) - f m| ≠ 0 := by
      intro abs_f_n_add_m_sub_f_m_eq_zero
      rw [abs_eq_zero, sub_eq_zero] at abs_f_n_add_m_sub_f_m_eq_zero
      simp [abs_f_n_add_m_sub_f_m_eq_zero] at h2

    have h4 : f n ≤ f (n + m) - f m ∨ f n ≤ f m - f (n + m) := by
      have :=
        calc f n
          _ = f (n + m - m) := by rw [Int.add_sub_cancel]
          _ ∣ f (n + m) - f m := h (n + m) m
          _ ∣ |f (n + m) - f m| := by rw [dvd_abs]
      have : f n ≤ |f (n + m) - f m| := Int.le_of_dvd (by grind) (by grind)
      rw [le_abs] at this
      cases this with
      | inl _ => grind
      | inr _ => grind

    cases h4 with
    | inl _ => grind
    | inr _ => grind

  · push_neg at h0
    by_cases f_m_eq_f_n : f m = f n
    · rw [f_m_eq_f_n]
    · grind


end Imo2011P5
