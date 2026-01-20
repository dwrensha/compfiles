/-
Copyright (c) 2025 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maximiliano Onofre Martínez
-/

import Mathlib.Tactic
import Mathlib.Data.Nat.GCD.Basic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# Russian Mathematical Olympiad 1995, problem 10

Let m, n be positive integers such that

gcd(m, n) + lcm(m, n) = m + n.

Show that one of the two numbers is divisible by the other.
-/

namespace Russia1995P10

problem russia1995_p10 {m n : ℕ} (h₀ : n ≠ 0 ∧ m ≠ 0)
  (h : gcd m n + lcm m n = m + n) :
  m ∣ n ∨ n ∣ m := by
  let g := gcd m n
  have h₁ : g + m * n / g = m + n := by aesop
  have h₂ : m * n + g^2 = g * (m + n) := by
    rw [← h₁]
    rw [Nat.left_distrib]
    rw [← pow_two]
    rw [Nat.mul_div_cancel']
    · rw [Nat.add_comm]
    exact dvd_trans (Nat.gcd_dvd_left m n) (Nat.dvd_mul_right m n)
  have h₃ : (m - g) * (n - g) = 0 := by zify at h₂; grind
  rw [Nat.mul_eq_zero] at h₃
  rcases h₃ with hm | hn
  · left
    have h_eq : m = g := by
      rw [Nat.sub_eq_zero_iff_le] at hm
      have h_div : g ∣ m := Nat.gcd_dvd_left m n
      have h_le : g ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero h₀.2) h_div
      exact le_antisymm hm h_le
    rw [h_eq]
    exact Nat.gcd_dvd_right m n
  right
  have h_eq : n = g := by
    rw [Nat.sub_eq_zero_iff_le] at hn
    have h_div : g ∣ n := Nat.gcd_dvd_right m n
    have h_le : g ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero h₀.1) h_div
    exact le_antisymm hn h_le
  rw [h_eq]
  exact Nat.gcd_dvd_left m n

end Russia1995P10
