/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Kurkiewicz
-/

import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
Polish Mathematical Olympiad 2016, Stage 1, Problem 8
Author of the problem: Nguyen Hung Son
Source of the problem: https://om.sem.edu.pl/static/app_main/problems/om68_1r.pdf

Let a, b, c be integers. Show that there exists a positive integer n, such that

  n³ + an² + bn + c

is not a square of any integer.
-/

namespace Poland2016S1P8

snip begin

lemma even_of_add {a : ℤ} {b : ℤ} : Even a → Even (a + b) → Even (b) := by
  intro A
  obtain ⟨k, H⟩ := A
  intro A_B
  obtain ⟨k2, H2⟩ := A_B
  use (k2 - k)
  rw [H] at H2
  apply symm
  calc k2 - k + (k2 - k) = k2 + k2 - k - k := by ring
    _ = k + k + b - k -k := by rw[H2]
    _ = b := by ring

lemma div_4_mul_of_both_even {a b : ℤ } (H : Even a ∧ Even b) : 4 ∣ a * b := by
  obtain ⟨k, Hk⟩ := H.left
  obtain ⟨l, Hl⟩ := H.right
  use k * l
  rw[Hk]
  rw[Hl]
  ring

snip end

problem poland2016_s1_p8 (a b c : ℤ) : ∃ n : ℤ, n > 0 ∧ ¬ IsSquare (n^3 + a * n^2 + b * n + c) := by
  apply not_forall_not.mp
  intro H
  apply H 1
  refine ⟨by positivity, ?_⟩
  rintro ⟨k, H1⟩
  apply H 2
  refine ⟨by positivity, ?_⟩
  rintro ⟨l, H2⟩
  apply H 3
  refine ⟨by positivity, ?_⟩
  rintro ⟨m, H3⟩
  apply H 4
  refine ⟨by positivity, ?_⟩
  rintro ⟨n, H4⟩
  have m_square_minus_k_square : m * m - k * k = 2 * (13 + 4 * a + b) := by
    rw [←H3, ←H1]
    ring
  have n_square_minus_l_square : n * n - l * l = 2 * (28 + 6 * a + b) := by
    rw [←H4, ←H2]
    ring
  have difference_m_square_k_square_as_product : m * m - k * k = (m + k) * (m - k) := by ring
  have difference_n_square_l_square_as_product : n * n - l * l = (n + l) * (n - l) := by ring
  have even_m_square_minus_k_square : Even ((m + k) * (m - k)) := by
    use 13 + 4 * a + b
    rw [← difference_m_square_k_square_as_product, m_square_minus_k_square]
    ring
  have even_n_square_minus_l_square : Even ((n + l) * (n - l)) := by
    use 28 + 6 * a + b
    rw [← difference_n_square_l_square_as_product, n_square_minus_l_square]
    ring
  have four_divides_m_square_minus_k_square : 4 ∣ (m + k) * (m - k) := by
    have both_factors_even_m_k : Even (m + k) ∧ Even (m - k) := by
      have either_even : (Even (m + k) ∨ Even (m - k)) :=
        Int.even_mul.mp even_m_square_minus_k_square
      obtain m_plus_k_even | m_minus_k_even := either_even
      · have : Even ((m + k) + (m - k)) := by
          use m
          ring
        have m_minus_k_even : Even (m - k) := even_of_add m_plus_k_even this
        constructor
        · exact m_plus_k_even
        · exact m_minus_k_even
      · have : Even ((m - k) + (m + k)) := by
          use m
          ring
        have m_plus_k_even : Even (m + k) := even_of_add m_minus_k_even this
        constructor
        · exact m_plus_k_even
        · exact m_minus_k_even
    exact div_4_mul_of_both_even both_factors_even_m_k
  have four_divides_n_square_minus_l_square : 4 ∣ (n + l) * (n - l) := by
    have both_factors_even_n_l : Even (n + l) ∧ Even (n - l) := by
      have either_even : (Even (n + l) ∨ (Even (n - l))) :=
        Int.even_mul.mp even_n_square_minus_l_square
      obtain n_plus_l_even | n_minus_l_even := either_even
      · have : Even ((n + l) + (n - l)) := by
          use n
          ring
        have n_minus_l_even : Even (n - l) := even_of_add n_plus_l_even this
        constructor
        · exact n_plus_l_even
        · exact n_minus_l_even
      · have : Even ((n - l) + (n + l)) := by
          use n
          ring
        have n_plus_l_even : Even (n + l) := even_of_add n_minus_l_even this
        constructor
        · exact n_plus_l_even
        · exact n_minus_l_even
    exact div_4_mul_of_both_even both_factors_even_n_l
  have div_4_difference : 4 ∣ (n + l) * (n - l) - (m + k) * (m - k) := by
    · apply dvd_sub
      · exact four_divides_n_square_minus_l_square
      · exact four_divides_m_square_minus_k_square
  have div4_difference_abc : 4 ∣ 2 * (28 + 6 * a + b) - 2 * (13 + 4 * a + b) := by
    · rw[← difference_m_square_k_square_as_product] at div_4_difference
      rw[← difference_n_square_l_square_as_product] at div_4_difference
      rw[m_square_minus_k_square] at div_4_difference
      rw[n_square_minus_l_square] at div_4_difference
      exact div_4_difference
  have difference_simplification : 2 * (28 + 6 * a + b) - 2 * (13 + 4 * a + b) = 4 * (a + 7) + 2 :=
    by ring
  rw[difference_simplification] at div4_difference_abc
  have towards_contradiction : 4 ∣ 4 * (a + 7) + 2 - 4 * (a + 7) := by
    · have four_divides_term : 4 ∣ 4 * (a + 7) := by
        · use (a + 7)
      exact dvd_sub div4_difference_abc four_divides_term
  have difference_simplification_2 : 4 * (a + 7) + 2 - 4 * (a + 7) = 2 := by ring
  rw[difference_simplification_2] at towards_contradiction
  contradiction


end Poland2016S1P8
