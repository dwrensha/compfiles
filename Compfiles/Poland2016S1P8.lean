/-
Copyright (c) 2023 The Compfiles Contributors. All rights reserved.
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

is not a square of any integer

-/

namespace Poland2016S1P8

snip begin

def is_square (n : ℤ) : Prop :=
  ∃ k : ℤ, k^2 = n

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

problem poland2016_s1_p8 (a b c : ℤ) : ∃ n : ℤ, ¬ (n > 0 → is_square (n^3 + a * n^2 + b * n + c)) := by
  apply not_forall_not.mp
  intro H
  apply H 1
  intro H1
  have : (1 : ℤ) > 0 := by positivity
  obtain ⟨k, H1⟩ := H1 this
  apply H 2
  intro H2
  have : (2 : ℤ) > 0 := by positivity
  obtain ⟨l, H2⟩ := H2 this
  apply H 3
  intro H3
  have : (3 : ℤ) > 0 := by positivity
  obtain ⟨m, H3⟩ := H3 this
  apply H 4
  intro H4
  have : (4 : ℤ) > 0 := by positivity
  obtain ⟨n, H4⟩ := H4 this
  have m_square_minus_k_square : m^2 - k^2 = 2 * (13 + 4 * a + b) := by
    · rw [H3]
      rw [H1]
      ring
  have n_square_minus_l_square : n^2 - l^2 = 2 * (28 + 6 * a + b) := by
    · rw [H4]
      rw [H2]
      ring
  have difference_m_square_k_square_as_product : m^2 - k^2 = (m + k) * (m - k) := by ring
  have difference_k_square_l_square_as_product : n^2 - l^2 = (n + l) * (n - l) := by ring
  have even_m_square_minus_k_square : Even ((m + k) * (m - k)) := by
    · use 13 + 4 * a + b
      rw[← difference_m_square_k_square_as_product]
      rw[m_square_minus_k_square]
      ring
  have even_n_square_minus_l_square : Even ((n + l) * (n - l)) := by
    · use 28 + 6 * a + b
      rw[← difference_k_square_l_square_as_product]
      rw[n_square_minus_l_square]
      ring
  have both_factors_even_m_k : Even (m + k) ∧ Even (m - k) := by
    have either_even : (Even (m + k) ∨ (Even (m - k))) := by exact Int.even_mul.mp even_m_square_minus_k_square

    obtain m_plus_k_even | m_minus_k_even := either_even
    · have : Even ((m + k) + (m - k)) := by
        · use m
          ring
      have m_minus_k_even : Even (m - k) := even_of_add m_plus_k_even this
      constructor
      · exact m_plus_k_even
      · exact m_minus_k_even
    · have : Even ((m - k) + (m + k)) := by
        · use m
          ring
      have m_plus_k_even : Even (m + k) := even_of_add m_minus_k_even this
      constructor
      · exact m_plus_k_even
      · exact m_minus_k_even
  sorry
