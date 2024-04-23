/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongyu Ouyang
-/

import Mathlib.Tactic
import Mathlib.Data.Nat.Choose.Basic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Olympiad 1972, Problem 3

Let m and n be non-negative integers. Prove that

     (2m)!(2n)! / (m!n!(m + n)!)

is an integer.
-/

namespace Imo1972P3

open scoped Nat

problem imo1972_p3 (m n : ℕ) :
    m ! * n ! * (m + n)! ∣ (2 * m)! * (2 * n)! := by
  let f := fun m n => ((2 * m)! * (2 * n)!) / (m ! * n ! * (m + n)!)
  revert m
  induction' n with n ih
  · intro m
    simp only [Nat.zero_eq, Nat.factorial_zero, mul_one, add_zero, mul_zero]
    use Nat.choose (2*m) m
    rw [← Nat.choose_mul_factorial_mul_factorial (n := 2 * m) (k := m)]
    rw [show 2*m-m = m by omega]
    ring_nf
    omega
  · intro m
    zify
    use (4 * f m n - f (m + 1) n)
    rify
    unfold_let f; dsimp only
    rw [Nat.cast_div, Nat.cast_div]
    · rw [show 2 * Nat.succ n = Nat.succ (Nat.succ (2 * n)) by omega]
      rw [show m + Nat.succ n = Nat.succ (m + n) by omega]
      rw [show 2 * (m + 1) = Nat.succ (Nat.succ (2 * m)) by omega]
      rw [show (m + 1 + n) = Nat.succ (m + n) by omega]
      simp only [Nat.factorial_succ]
      push_cast
      field_simp
      ring
    · apply ih
    · positivity
    · apply ih
    · positivity
