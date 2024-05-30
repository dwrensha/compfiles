/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/

import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Multiplicity
import Mathlib.Tactic

import ProblemExtraction

problem_file {
  tags := [.NumberTheory],
  importedFrom :=
    "https://github.com/leanprover-community/mathlib4/blob/master/Archive/Imo/Imo2019Q4.lean",
}

/-!
# International Mathematical Olympiad 2019, Problem 4

Determine all positive integers n,k that satisfy the equation

  k! = (2ⁿ - 2⁰)(2ⁿ - 2¹) ... (2ⁿ - 2ⁿ⁻¹).
-/

namespace Imo2019P4

open scoped Nat BigOperators

snip begin

/-
Proof sketch:
The idea of the proof is to count the factors of 2 on both sides. The LHS has less
than `k` factors of 2, and the RHS has exactly `n * (n - 1) / 2` factors of 2.
So we know that `n * (n - 1) / 2 < k`. Now for `n ≥ 6` we have
`RHS < 2 ^ (n ^ 2) < (n(n-1)/2)! < k!`. We then treat the cases `n < 6`
individually.
-/

theorem upper_bound {k n : ℕ} (hk : k > 0)
    (h : (k ! : ℤ) = ∏ i ∈ Finset.range n, ((2:ℤ) ^ n - (2:ℤ) ^ i)) : n < 6 := by
  have h2 : ∑ i ∈ Finset.range n, i < k := by
    suffices multiplicity 2 (k ! : ℤ) = ↑(∑ i ∈ Finset.range n, i : ℕ) by
      rw [← PartENat.coe_lt_coe, ← this]; change multiplicity ((2 : ℕ) : ℤ) _ < _
      simp_rw [multiplicity.Int.natCast_multiplicity,
               Nat.multiplicity_two_factorial_lt hk.lt.ne.symm]
    rw [h, multiplicity.Finset.prod Int.prime_two, Nat.cast_sum]
    apply Finset.sum_congr rfl; intro i hi
    rw [multiplicity.multiplicity_sub_of_gt,
        multiplicity.multiplicity_pow_self_of_prime Int.prime_two]
    rwa [multiplicity.multiplicity_pow_self_of_prime Int.prime_two,
         multiplicity.multiplicity_pow_self_of_prime Int.prime_two,
      PartENat.coe_lt_coe, ← Finset.mem_range]
  rw [← not_le]; intro hn
  apply _root_.ne_of_gt _ h
  calc ∏ i ∈ Finset.range n, ((2:ℤ) ^ n - (2:ℤ) ^ i) ≤ ∏ __ ∈ Finset.range n, (2:ℤ) ^ n := ?_
    _ < ↑ k ! := ?_
  · gcongr
    · intro i hi
      simp only [Finset.mem_range] at hi
      have : (2:ℤ) ^ i ≤ (2:ℤ) ^ n := by gcongr; norm_num
      omega
    · apply sub_le_self
      positivity
  norm_cast
  calc ∏ __ ∈ Finset.range n, 2 ^ n = 2 ^ (n * n) := by
         rw [Finset.prod_const, Finset.card_range, ← pow_mul]
    _ < (∑ i ∈ Finset.range n, i)! := ?_
    _ ≤ k ! := by gcongr
  clear h h2
  induction' n, hn using Nat.le_induction with n' hn' IH
  · decide
  let A := ∑ i ∈ Finset.range n', i
  have le_sum : ∑ i ∈ Finset.range 6, i ≤ A := by
    apply Finset.sum_le_sum_of_subset
    simpa using hn'
  calc 2 ^ ((n' + 1) * (n' + 1))
      ≤ 2 ^ (n' * n' + 4 * n') := by gcongr <;> linarith
    _ = 2 ^ (n' * n') * (2 ^ 4) ^ n' := by rw [← pow_mul, ← pow_add]
    _ < A ! * (2 ^ 4) ^ n' := by gcongr
    _ = A ! * (15 + 1) ^ n' := rfl
    _ ≤ A ! * (A + 1) ^ n' := by gcongr; exact le_sum
    _ ≤ (A + n')! := Nat.factorial_mul_pow_le_factorial
    _ = (∑ i ∈ Finset.range (n' + 1), i)! := by rw [Finset.sum_range_succ]

snip end

determine solution_set : Set (ℕ × ℕ) := { (1,1), (2,3) }

problem imo2018_p2 (n k : ℕ) :
    (n, k) ∈ solution_set ↔
    0 < n ∧ 0 < k ∧
    (k ! : ℤ) = ∏ i ∈ Finset.range n, ((2:ℤ)^n - (2:ℤ)^i) := by
  constructor
  · intro nk
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at nk
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := nk <;> decide
  rintro ⟨npos, kpos, h⟩
  -- We know that n < 6.
  have := Imo2019P4.upper_bound kpos h
  interval_cases n
  -- n = 1
  · left; congr; norm_num at h
    exact Nat.le_antisymm h kpos
  -- n = 2
  · right; congr; norm_num [Finset.prod_range_succ] at h; norm_cast at h
    rwa [← Nat.factorial_inj']; norm_num

  all_goals exfalso; norm_num [Finset.prod_range_succ] at h; norm_cast at h
  -- n = 3
  · refine Nat.monotone_factorial.ne_of_lt_of_lt_nat 5 ?_ ?_ _ h <;> decide
  -- n = 4
  · refine Nat.monotone_factorial.ne_of_lt_of_lt_nat 7 ?_ ?_ _ h <;> decide
  -- n = 5
  · refine Nat.monotone_factorial.ne_of_lt_of_lt_nat 10 ?_ ?_ _ h <;> decide
