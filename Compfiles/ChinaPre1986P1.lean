/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: sjfhsjfh
-/
import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# China Pre-CMO (National High School Math League, Second Round) 1986, Problem 1

已知数列 `a₀, a₁, a₂, …` 满足 `a₀ ≠ a₁` 且 `a_{i-1} + a_{i+1} = 2aᵢ`（`i = 1, 2, 3, …`）。
求证：对于任何自然数 `n`，
`p(x) = a₀ Cₙ⁰ (1−x)ⁿ + a₁ Cₙ¹ (1−x)ⁿ⁻¹ x + … + aₙ Cₙⁿ xⁿ`
是 `x` 的一次多项式。（注：当时自然数定义不含 0，即 n ≥ 1）

Let the sequence `a₀, a₁, a₂, …` satisfy `a₀ ≠ a₁` and `a_{i-1} + a_{i+1} = 2aᵢ`
for all `i ≥ 1`.
For any natural number `n` (note: at the time, 0 was not considered
a natural number),
define `p(x) = ∑_{k=0}^n a_k C(n,k) (1−x)^{n−k} x^k`.
Prove that `p(x)` is a linear polynomial in `x`.
-/

open Polynomial

namespace ChinaPre1986P1

noncomputable def p (a : ℕ → ℝ) (n : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (n + 1),
    C (a k) * C ((Nat.choose n k : ℕ) : ℝ) * ((1 - X) ^ (n - k)) * (X ^ k)

snip begin

lemma arithmetic_progression {a : ℕ → ℝ}
  (ha_rec : ∀ i : ℕ, a i + a (i + 2) = 2 * a (i + 1))
  : ∀ i : ℕ, a i = a 0 + i * (a 1 - a 0) := fun i ↦ by
  have hdiff : ∀ i : ℕ, a (i + 1) - a i = a 1 - a 0 := fun i ↦ by
    induction i with
    | zero => simp only [zero_add]
    | succ j ih =>
      have := ha_rec j; rewrite [add_comm, ← eq_sub_iff_add_eq] at this
      rewrite [this, two_mul, add_sub_assoc, ih, add_sub_cancel_left]; rfl
  induction i with
  | zero => simp only [CharP.cast_eq_zero, zero_mul, add_zero]
  | succ j ih =>
    have := hdiff j; rewrite [sub_eq_iff_eq_add] at this
    rewrite [this, ih, Nat.cast_add_one j, add_one_mul, add_comm _ (_ + _)]
    exact add_assoc (a 0) (↑j * (a 1 - a 0)) (a 1 - a 0)

lemma sum_eq_one {n : ℕ}
  : ∑ i ∈ Finset.range (n + 1), (↑(n.choose i) : ℝ[X]) * ((1 - X) ^ (n - i) * X ^ i)
    = 1 := by
  simp only [mul_comm (↑(Nat.choose _ _) : ℝ[X]) _, mul_comm ((_ - _) ^ _) _]
  rewrite [← add_pow, add_comm, sub_add_cancel, one_pow]; rfl

lemma sum_eq_nX {n : ℕ}
  : ∑ i ∈ Finset.range (n + 1), (↑i : ℝ[X])
    * ((↑(n.choose i) : ℝ[X]) * ((1 - X) ^ (n - i) * X ^ i)) = ↑n * X := by
  simp only [← mul_assoc, ← map_natCast C, ← map_mul, ← Nat.cast_mul]
  by_cases! hn : n = 0
  · subst hn; norm_num
  rewrite [Finset.sum_range_succ']
  simp only [CharP.cast_eq_zero, zero_mul, map_zero, add_zero]
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_one.mpr <| Nat.zero_lt_of_ne_zero hn
  subst hm; simp only [mul_comm _ (Nat.choose _ _), ← Nat.add_one_mul_choose_eq]
  simp only [Nat.reduceSubDiff]; simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  simp only [map_mul, map_natCast, map_add, map_one, mul_comm _ ((m : ℝ[X]) + 1)]
  simp only [mul_assoc]; rewrite [← Finset.mul_sum]
  simp only [pow_add, pow_one, ← mul_assoc]; rewrite [← Finset.sum_mul]
  simp only [mul_assoc]; rewrite [sum_eq_one, one_mul]; rfl

snip end

problem chinaPre1986_p1
  (a : ℕ → ℝ) (ha_ne : a 0 ≠ a 1)
  (ha_rec : ∀ i : ℕ, a i + a (i + 2) = 2 * a (i + 1))
  (n : ℕ) (hn : n ≥ 1) : (p a n).degree = 1 := by
  suffices h : p a n = C (a 0) + C (n * (a 1 - a 0)) * X by
    have hrhs : (C (n * (a 1 - a 0)) * X).degree = 1 := by
      rewrite [degree_mul]; simp only [degree_X]
      have : (C (n * (a 1 - a 0))).degree = 0 := degree_C <| by
        rewrite [ne_eq, mul_eq_zero, Nat.cast_eq_zero, not_or, sub_eq_zero]
        exact ⟨(Nat.zero_lt_of_lt hn).ne', ha_ne.symm⟩
      rewrite [this, zero_add]; rfl
    rewrite [h, ← hrhs]; refine degree_add_eq_right_of_degree_lt ?_
    rewrite [hrhs]; exact degree_C_lt
  have (p : ℝ[X]) (i : ℕ) : C (a i) * p = (C (a 0) + C (i * (a 1 - a 0))) * p := by
    rewrite [arithmetic_progression ha_rec i, C_add]; rfl
  simp only [p, this]; simp only [add_mul]; rewrite [Finset.sum_add_distrib]
  simp only [map_natCast, map_mul, mul_comm _ (C (a 1 - a 0)), mul_assoc]
  simp only [← Finset.mul_sum]; rewrite [sum_eq_one, mul_one, add_right_inj]
  rewrite [mul_eq_mul_left_iff]; exact Or.inl sum_eq_nX

end ChinaPre1986P1
