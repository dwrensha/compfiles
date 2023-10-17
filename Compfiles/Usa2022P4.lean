/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import Compfiles.Meta.ProblemExtraction

problem_file

/-!
# USA Mathematical Olympiad 2022, Problem 4

Determine all pairs of primes (p, q) where p - q and pq - q
are both perfect squares.
-/

namespace Usa2022P4

determine solution_set : Set (ℕ × ℕ) := {(3, 2)}

problem usa2022_p4 (p q : ℕ) :
    (p, q) ∈ solution_set ↔
    p.Prime ∧ q.Prime ∧
    ∃ a, a^2 + q = p ∧ ∃ b, b^2 + q = p * q := by
  constructor
  · -- easy direction
    intro hpq
    rw [Set.mem_singleton_iff, Prod.mk.injEq] at hpq
    obtain ⟨hp, hq⟩ := hpq
    rw [hp, hq]
    exact ⟨by norm_num, by norm_num, 1, by norm_num, 2, by norm_num⟩

  -- Informal proof outline taken from
  -- https://web.evanchen.cc/exams/USAMO-2022-notes.pdf
  rintro ⟨hpp, hpq, a, ha, b, hb⟩

  -- Note that 0 < p and 0 < q because they are prime.
  have hp_pos : 0 < p := Nat.Prime.pos hpp
  have hq_pos : 0 < q := Nat.Prime.pos hpq

  -- Note that we then have 0 < a < p, and 0 < b < p (because q ≤ p).
  have hqlep : q ≤ p := by
    have h1 : q ≤ a^2 + q := Nat.le_add_left q (a ^ 2)
    exact Eq.trans_ge ha h1

  /-
  have ha_pos : 0 < a := by
    by_contra H
    have h1 : a = 0 := Nat.eq_zero_of_nonpos a H
    rw [h1] at ha
    simp only [ne_eq, zero_pow', zero_add] at ha
    rw [ha] at hb
    sorry
  have hb_pos : 0 < b := by nlinarith
  -/
  have hap : a < p := by
    by_contra' H
    have h2 : p^2 ≤ a^2 := Nat.pow_le_pow_of_le_left H 2
    have h6 :=
      calc p < p * p := Nat.lt_mul_self_iff.mpr (Nat.Prime.one_lt hpp)
           _ = p^2 := (Nat.pow_two p).symm
           _ ≤ p^2 + q := Nat.le_add_right (p ^ 2) q
           _ ≤ _ := Nat.add_le_add_right h2 q
           _ = p := ha
    exact LT.lt.false h6

  have hbp : b < p := by
    by_contra' H
    have h2 : p^2 ≤ b^2 := Nat.pow_le_pow_of_le_left H 2
    have h6 :=
      calc p * p = p^2 := (Nat.pow_two p).symm
           _ < p^2 + q := Nat.lt_add_of_pos_right hq_pos
           _ ≤ _ := Nat.add_le_add_right h2 q
           _ = p * q := hb
    have h7 : p < q := (mul_lt_mul_left hp_pos).mp h6
    exact Nat.le_lt_antisymm hqlep h7

  have hab : a ≤ b := by zify at ha hb ⊢; sorry

  -- Subtracting our equations gives (b - a)(b + a) = b² - a² = p(q - 1),
  have h1 : (b - a) * (b + a) = p * (q - 1) := by
    sorry

  -- Since b - a < p and p is prime, we have that p divides b + a.
  -- Since and b + a < 2p, we have that a + b must in fact equal p.

  -- Hence q - 1 = b - a.

  -- Note that b - a and b + a have the same parity.
  -- Therefore p and q - 1 have the same parity.
  -- If they are both even, then q > p, contradiction.
  -- Therefore, they are both odd, and q = 2.

  -- Moreover, p ≡ 0 mod 3, so (3,2) is the only possibility.
  sorry
