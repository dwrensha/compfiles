/-
Copyright (c) 2025 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shalev Wengrowsky
-/

import Mathlib.Data.Nat.Factorization.Basic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# USA Mathematical Olympiad 1972, Problem 1

Let (a, b, ... , k) denote the greatest common divisor of the integers a, b, ... k
and [a, b, ... , k] denote their least common multiple.

Show that for any positive integers a, b, c we have
(a, b, c)2 [a, b] [b, c] [c, a] = [a, b, c]2 (a, b) (b, c) (c, a).
-/

namespace Usa1972P1

open Nat

snip begin
/-
  implementation of the proof from https://prase.cz/kalva/usa/usoln/usol721.html

  If we express a, b, c as a product of primes then the gcd has each prime
  to the smallest power and the lcm has each prime to the largest power.

  So the equation given is equivalent to showing that
    2 * min(r, s, t) + max(r, s) + max(s, t) + max(t, r) = 2 * max(r, s, t) + min(r, s) + min(s, t) + min(t, r)
  for non-negative integers r, s, t. Assume r ≤ s ≤ t. Then each side is 2r + s + 2t.
-/
snip end

problem usa1972_p1 (a b c : ℕ) :
  (gcd a (gcd b c)) ^ 2 * lcm a b * lcm b c * lcm c a =
  (lcm a (lcm b c)) ^ 2 * gcd a b * gcd b c * gcd c a := by {
  -- if any of a, b, c are 0 the problem becomes trivial
  by_cases a_pos : a = 0
  · simp [a_pos]
  by_cases b_pos : b = 0
  · simp [b_pos]
  by_cases c_pos : c = 0
  · simp [c_pos]
  apply Nat.eq_of_factorization_eq (by simp; tauto) (by simp; tauto)
  intro p
  let r := a.factorization p
  let s := b.factorization p
  let t := c.factorization p
  repeat rw [factorization_mul (by simp; tauto) (by simp; tauto)]
  simp
  repeat rw [factorization_lcm (by simp; tauto) (by simp; tauto)]
  repeat rw [factorization_gcd (by simp; tauto) (by simp; tauto)]
  simp
  by_cases h_rs : r ≤ s
  · by_cases h_st : s ≤ t
    · omega
    · by_cases h_rt : r ≤ t
      repeat omega
  · by_cases h_rt : r ≤ t
    · repeat omega
    · omega
}

end Usa1972P1
