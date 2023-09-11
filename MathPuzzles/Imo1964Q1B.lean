/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw, Anand Rao
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.GroupPower.Basic
import Mathlib.Tactic.Linarith

import MathPuzzles.Meta.Attributes

/-!
# International Mathematical Olympiad 1964, Problem 1b

Prove that there is no positive integer n for which 2ⁿ + 1 is divisible by 7.
-/

namespace Imo1964Q1

/-
Informal proof (credit to twitch.tv viewer int_fast64_t):
  let 2^n = 2^{3k + j},j < 3
  (i.e. write n as 3k + j)
  =>
    2^n mod 7 = (2^3 mod 7)^k * 2^j mod 7 = 1 mod 7 * 2^j mod 7,
  but 2^j < 5
-/
@[problem_statement]
theorem imo_1964_q1b (n : ℕ) : ¬ 7 ∣ (2^n + 1) := by
  intro h
  replace h := Nat.mod_eq_zero_of_dvd h
  rw[←Nat.div_add_mod n 3] at h

  have h := calc
     0 = (2 ^ (3 * (n / 3) + n % 3) + 1) % 7       := h.symm
     _ = ((2 ^ 3) ^ (n / 3) * 2 ^ (n % 3) + 1) % 7 := by rw[pow_add, pow_mul]
     _ = ((2 ^ 3 % 7) ^ (n / 3) % 7 * (2 ^ (n % 3) % 7) % 7 + 1 % 7) % 7 :=
                   by rw[Nat.add_mod, Nat.mul_mod, Nat.pow_mod]
     _ = (1 ^ (n / 3) % 7 * (2 ^ (n % 3) % 7) % 7 + 1 % 7) % 7 :=
                   by rw[show (2 ^ 3) % 7 = 1 by rfl]
     _ = (1 % 7 * (2 ^ (n % 3) % 7) % 7 + 1 % 7) % 7 := by rw[one_pow]
     _ = (2 ^ (n % 3) % 7 + 1) % 7 :=
                   by rw[show 1 % 7 = 1 by rfl, one_mul, Nat.mod_mod]

  cases hn' : n % 3 with
  | zero => rw[hn'] at h; norm_num at h
  | succ n' =>
    cases n' with
    | zero => rw[hn'] at h; norm_num at h
    | succ n' =>
      cases n' with
      | zero => rw[hn'] at h; norm_num at h
      | succ n' => have h5 : 3 > 0 := by norm_num
                   have h6 := Nat.mod_lt n h5
                   rw[hn'] at h6
                   linarith

/- An alternative proof, heavily golfed. The statement here is slightly modified from the original one. -/
theorem imo_1964_q1b' : ∀ (n : ℕ), (2 ^ n + 1) % 7 ≠ 0
    | 0 | 1 | 2 => by decide
    | n + 3 => by
      rw [pow_add, Nat.add_mod, Nat.mul_mod, show 2 ^ 3 % 7 = 1 from by rfl]
      simp [imo_1964_q1b' n]
