/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Chen
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# USA Mathematical Olympiad 2008, Problem 1

Prove that for each positive integer n, there are pairwise relatively prime
integers k₀,k₁,...,kₙ, all strictly greater than 1, such that k₀k₁...kₙ - 1
is a product of two consecutive integers.
-/

namespace Usa2008P1

snip begin

-- This follows the ad-hoc second solution in
-- https://web.evanchen.cc/exams/USAMO-2008-notes.pdf

-- Define the two main sequences
def kseq (n : ℕ) : ℕ :=
  if n = 0 then 7 else 2 ^ (2 ^ n) - 2 ^ (2 ^ (n - 1)) + 1
def xseq (n : ℕ) : ℕ := (2 ^ (2 ^ n))

lemma k_greater_than_one (n : ℕ) : kseq n > 1 := by
  unfold kseq
  split_ifs -- split on i = 0 and i > 0
  · norm_num
  · have : 2^(2^(n-1)) < 2^(2^n) := by gcongr <;> omega
    omega

-- Pure ring lemma
lemma quartic_polynomial_identity (t : ℕ) :
    (1 + t * (t+1)) * (t^2 - t + 1) = 1 + t^2 * (t^2+1) := by
  zify [show t ≤ t^2 by nlinarith]
  ring

-- Main identity k₀k₁...kₙ - 1 = xₙ (xₙ + 1)
lemma main_identity (n : ℕ) :
  (∏ i : Fin (n+1), (kseq ↑i)) = 1 + (xseq n) * ((xseq n) + 1) := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [Fin.prod_univ_castSucc]
      simp
      rw [ih]
      simp only [kseq]
      simp
      rw [show 2 ^ 2 ^ (n + 1) = (xseq n)^2 by unfold xseq; ring]
      rw [show xseq (n + 1) = (xseq n)^2 by unfold xseq; ring]
      rw [show 2 ^ 2 ^ n = xseq n from rfl]
      exact quartic_polynomial_identity (xseq n)

-- Mod 7 crap because of the edge case when n = 0
lemma pow_two_pow_mod_seven (k : ℕ) : 2 ^ 2 ^ k % 7 = if k % 2 = 0 then 2 else 4 :=
  match k with
  | 0 => by decide
  | 1 => by decide
  | k + 2 => by
    rw [show 2 ^ 2 ^ (k + 2) = (2 ^ 2 ^ k) ^ 4 by ring, Nat.pow_mod]
    rw [pow_two_pow_mod_seven k]
    simp
    split_ifs <;> decide

lemma k_nonzero_mod_7 (j : ℕ) :
    0 < j → (2 ^ (2 ^ j) - 2 ^ (2 ^ (j - 1)) + 1) % 7 ≠ 0 := by
  intro -- j > 0
  have h1 := pow_two_pow_mod_seven j
  have h2 := pow_two_pow_mod_seven (j - 1)
  split_ifs at h1 h2 <;> omega

-- Show the main coprime lemma
lemma k_are_coprime (i j : ℕ) : i < j → Nat.Coprime (kseq i) (kseq j) := by
  intro
  unfold kseq
  simp [if_neg (show j ≠ 0 by omega)]
  have hj_pos : j > 0 := by omega
  split_ifs -- split on i = 0 and i > 0
  · rw [Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 7)]
    rw [Nat.dvd_iff_mod_eq_zero]
    apply k_nonzero_mod_7
    exact hj_pos
  · have hi_pos : i > 0 := by omega
    sorry
snip end

problem usa2008_p1 (n : ℕ) (hn : 0 < n) :
    ∃ k : Fin (n + 1) → ℕ,
      (∀ i, 1 < k i) ∧
      (∀ i j, i ≠ j → Nat.Coprime (k i) (k j)) ∧
      ∃ m, ∏ i : Fin (n + 1), k i = 1 + m * (m + 1) := by

  use fun i ↦ kseq i -- choose k

  constructor -- check kₙ > 1
  · intro i
    apply k_greater_than_one ↑i

  constructor -- check coprime
  · intro i j hij
    have hij' : (↑i : ℕ) ≠ ↑j := Fin.val_injective.ne hij
    rcases Nat.lt_or_gt_of_ne hij' with h | h
    · exact k_are_coprime ↑i ↑j h
    · exact (k_are_coprime ↑j ↑i h).symm

  use xseq n -- choose m = xₙ and finish up
  exact main_identity n

end Usa2008P1
