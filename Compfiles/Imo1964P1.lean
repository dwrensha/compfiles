/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw, Anand Rao, Harald Carlens
-/

import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Olympiad 1964, Problem 1

(a) Find all natural numbers n for which 2ⁿ - 1 is divisible by 7.
(b) Prove that there is no positive integer n for which 2ⁿ + 1 is divisible by 7.
-/

namespace Imo1964P1

determine solution_set : Set ℕ := { n | n % 3 = 0 }

problem imo_1964_p1a (n : ℕ) : n ∈ solution_set ↔ 2^n ≡ 1 [MOD 7] := by
  constructor
  · intro hn
    obtain ⟨m, hm⟩ := Nat.dvd_of_mod_eq_zero hn
    change 2^n % 7 = 1
    rw [hm, Nat.pow_mul, Nat.pow_mod]
    norm_num
  · intro hn
    change n % 3 = 0
    change 2^n % 7 = 1 at hn
    rw [(Nat.div_add_mod' n 3).symm] at hn
    rw [pow_add, pow_mul', Nat.mul_mod, Nat.pow_mod] at hn
    mod_cases H : n % 3
    · exact H
    · rw [H] at hn; norm_num at hn
    · rw [H] at hn; norm_num at hn

problem imo_1964_p1b (n : ℕ) : ¬ 7 ∣ (2^n + 1) := by
  /-
  Following https://prase.cz/kalva/imo/isoln/isoln641.html:
  Let n = 3m + k; k = 0, 1, or 2.
  2^3 = 1 (mod 7).
  Hence
  2^3m + 1 = 2 (mod 7),
  2^(3m+1) + 1 = 3 (mod 7), and
  2^(3m + 2) + 1 = 5 (mod 7).
  -/
  intro h
  apply Nat.mod_eq_zero_of_dvd at h
  have h1: 2 ^ 3 % 7 = 1 := by rfl
  mod_cases h2 : n % 3 <;> rw [←Nat.div_add_mod n 3, h2] at h
  · rw [Nat.zero_mod, add_zero, Nat.add_mod, Nat.pow_mod, pow_mul, Nat.pow_mod, h1, one_pow] at h
    contradiction
  · rw [Nat.add_mod, pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod, h1, one_pow] at h
    contradiction
  · rw [Nat.add_mod, pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod, h1, one_pow] at h
    contradiction

snip begin

/- An alternative proof, heavily golfed. The statement here is slightly modified from
   the original one. -/
theorem imo_1964_p1b' : ∀ (n : ℕ), (2 ^ n + 1) % 7 ≠ 0
    | 0 | 1 | 2 => by decide
    | n + 3 => by
      rw [pow_add, Nat.add_mod, Nat.mul_mod, show 2 ^ 3 % 7 = 1 by rfl]
      simp [imo_1964_p1b' n]

snip end

end Imo1964P1
