/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# British Mathematical Olympiad 2024, Round 1, Problem 4

Find all positive integers n such that n × 2ⁿ + 1 is a square.

The answer is n = 2 and n = 3.

We follow the presentation by the problem author in https://eventuallyalmosteverywhere.wordpress.com/2024/01/10/finitely-many-solutions/, with modifications.
-/

namespace UK2024R1P4

determine SolutionSet : Set ℕ := {2, 3}

snip begin

/-- For n ≥ 5, n + 1 < 2^(n-2). -/
lemma two_pow_sub_two_gt (n : ℕ) (hn : 5 ≤ n) : n + 1 < 2 ^ (n - 2) := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    have h : k + 1 - 2 = (k - 2) + 1 := by omega
    rw [h, pow_succ]
    omega

/-- Key inequality (*): if n·2ⁿ + 1 is a perfect square and n ≥ 2, then
    2^(n-1) ≤ 2n + 2.

    Strategy: factor n·2ⁿ = (k-1)(k+1). Since n·2ⁿ is even, k² = n·2ⁿ+1
    is odd, so k is odd — write k = 2a+1. Then (k-1)(k+1) = 4a(a+1), so
    a(a+1) = n·2^(n-2). The integers a and a+1 are coprime with exactly
    one even, so the full factor 2^(n-2) lands on that even one. -/
lemma sq_bound (n : ℕ) (hn : 2 ≤ n) (h : IsSquare (n * 2 ^ n + 1)) :
    2 ^ (n - 1) ≤ 2 * n + 2 := by
  obtain ⟨k, hk⟩ := h
  have h_kk : k * k = n * 2 ^ n + 1 := hk.symm
  -- k is odd (since n·2ⁿ is even, k² = n·2ⁿ + 1 is odd).
  have h_k_odd : Odd k := by
    have h_even : Even (n * 2 ^ n) :=
      (Even.pow_of_ne_zero (even_two_mul 1) (by omega : n ≠ 0)).mul_left _
    have h_odd : Odd (k * k) := by
      rw [h_kk]; exact Even.add_one h_even
    exact Nat.Odd.of_mul_left h_odd
  /- Rewrite k as 2a+1. -/
  obtain ⟨a, rfl⟩ := h_k_odd
  -- Factorization: n·2ⁿ = (k-1)(k+1) = 4a(a+1), hence a(a+1) = n·2^(n-2).
  have h_pow : 2 ^ n = 4 * 2 ^ (n - 2) := by
    rw [show n = (n - 2) + 2 by omega]; grind
  have hab : a * (a + 1) = n * 2 ^ (n - 2) := by
    have h1 : 4 * (a * (a + 1)) + 1 = n * 2 ^ n + 1 := by linarith [h_kk]
    have h2 : 4 * (a * (a + 1)) = 4 * (n * 2 ^ (n - 2)) := by
      rw [h_pow] at h1; linarith
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h2
  -- a and a+1 are coprime; exactly one is even, so 2^(n-2) divides it.
  have h_dvd : 2 ^ (n - 2) ∣ a * (a + 1) := ⟨n, by grind ⟩
  have ha_pos : 0 < a := by
    by_contra h
    rw [show a = 0 by grind] at hab
    norm_num at hab
    grind
  have h_pow_expand : 2 ^ (n - 1) = 2 * 2 ^ (n - 2) := by
    rw [show n - 1 = (n - 2) + 1 by omega]; grind
  /- We now case on which factor 2^(n-2) lands on, or equivalently, whether a is even or odd. -/
  rcases Nat.even_or_odd a with he | ho
  · obtain ⟨ t, rfl ⟩ := he
    have h_a1_odd : Odd (2 * t + 1) := ⟨t, rfl⟩
    have h_cop_p : Nat.Coprime (2 ^ (n - 2)) (2 * t + 1) :=
      (Nat.coprime_two_left.mpr h_a1_odd).pow_left _
    have h_dvd_a : 2 ^ (n - 2) ∣ 2 * t := h_cop_p.dvd_of_dvd_mul_right (by grind)
    have h_a_ge : 2 ^ (n - 2) ≤ 2 * t := Nat.le_of_dvd (by grind) h_dvd_a
    nlinarith
  · obtain ⟨t, rfl⟩ := ho
    have h_a_odd : Odd (2 * t + 1) := ⟨t, rfl⟩
    have h_cop_p : Nat.Coprime (2 ^ (n - 2)) (2 * t + 1) :=
      (Nat.coprime_two_left.mpr h_a_odd).pow_left _
    have h_dvd_a1 : 2 ^ (n - 2) ∣ (2 * t + 1 + 1) :=
      h_cop_p.dvd_of_dvd_mul_right (by rw [mul_comm]; grind)
    have h_a1_ge : 2 ^ (n - 2) ≤ 2 * t + 1 + 1 := Nat.le_of_dvd (by omega) h_dvd_a1
    nlinarith

/-- For n ≥ 5, n·2ⁿ + 1 is not a perfect square: the bound (*) combined
    with `two_pow_sub_two_gt` is immediately contradictory. -/
lemma not_square_ge_five (n : ℕ) (hn : 5 ≤ n) : ¬ IsSquare (n * 2 ^ n + 1) := by
  intro h
  have h1 := sq_bound n (by omega) h
  have h2 := two_pow_sub_two_gt n hn
  have : 2 ^ (n - 1) = 2 * 2 ^ (n - 2) := by
    rw [show n - 1 = (n - 2) + 1 by omega]; grind
  omega

snip end

problem uk2024_r1_p4 (n : ℕ) (hn : 0 < n) :
    n ∈ SolutionSet ↔ IsSquare (n * 2 ^ n + 1) := by
  constructor
  · rintro (rfl | rfl) <;> norm_num
  · intro hsq
    by_cases h5 : 5 ≤ n
    · exact absurd hsq (not_square_ge_five n h5)
    · interval_cases n
      · norm_num at hsq
      · grind
      · grind
      · norm_num at hsq

end UK2024R1P4
