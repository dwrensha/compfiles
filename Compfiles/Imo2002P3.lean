/-
Copyright (c) 2025 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/

import Mathlib

import ProblemExtraction

problem_file {
  tags := [.Algebra]
  solutionImportedFrom :=
    "https://github.com/leanprover-community/mathlib4/blob/master/Archive/Imo/Imo2002Q3.lean"
}

/-!
# International Mathematical Olympiad 2002, Problem 3

Find all pairs of positive integers m,n ≥ 3 for which
there exist infinitely many positive integers a such that

   (aᵐ + a - 1) / (aⁿ + a² - 1)

is itself an integer.

-/

namespace Imo2002P3

snip begin

section
open Polynomial

lemma natDegree_numerpol {m : ℕ} (hm : 3 ≤ m) :
    (X ^ m + X - 1 : ℤ[X]).natDegree = m := by
  compute_degree <;> grind

lemma monic_numerpol {m : ℕ} (hm : 3 ≤ m) :
    (X ^ m + X - 1 : ℤ[X]).Monic := by
  apply Monic.sub_of_left
  · apply monic_X_pow_add
    rw [degree_X, Nat.one_lt_cast]
    lia
  · rw [degree_one, degree_add_eq_left_of_degree_lt]
    · simp_rw [degree_X_pow, Nat.cast_pos]
      lia
    · rw [degree_X_pow, degree_X, Nat.one_lt_cast]
      lia

lemma natDegree_denompol {n : ℕ} (hn : 3 ≤ n) :
    (X ^ n + X ^ 2 - 1 : ℤ[X]).natDegree = n := by
  compute_degree <;> grind

lemma monic_denompol {n : ℕ} (hn : 3 ≤ n) :
    (X ^ n + X ^ 2 - 1 : ℤ[X]).Monic := by
  apply Monic.sub_of_left
  · apply monic_X_pow_add
    rw [degree_X_pow, Nat.cast_lt]
    lia
  · rw [degree_one, degree_add_eq_left_of_degree_lt]
    · simp_rw [degree_X_pow, Nat.cast_pos]
      lia
    · simp_rw [degree_X_pow, Nat.cast_lt]
      lia

lemma proof_body {m n : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n)
    (h : {a : ℤ | 0 < a ∧ a ^ n + a ^ 2 - 1 ∣ a ^ m + a - 1}.Infinite) :
    m = 5 ∧ n = 3 := by
  replace h : (X ^ n + X ^ 2 - 1 : ℤ[X]) ∣ X ^ m + X - 1 :=
    dvd_of_infinite_eval_dvd_eval (monic_denompol hn) (h.mono (by simp))
  -- Algebraic part: `n ≤ m - n + 1`
  have db := natDegree_le_of_dvd h (monic_numerpol hm).ne_zero
  rw [natDegree_numerpol hm, natDegree_denompol hn] at db
  replace h := dvd_sub_self_right.mpr (dvd_mul_of_dvd_left h (X + 1))
  have rearr : ((X ^ m + X - 1) * (X + 1) - (X ^ n + X ^ 2 - 1) : ℤ[X]) =
      X ^ n * (X ^ (m - n + 1) + X ^ (m - n) - 1) := by
    nth_rw 1 [← Nat.sub_add_cancel db]
    ring
  rw [rearr] at h
  replace h : (X ^ n + X ^ 2 - 1 : ℤ[X]) ∣ X ^ (m - n + 1) + X ^ (m - n) - 1 := by
    refine (IsRelPrime.pow_right ?_).dvd_of_dvd_mul_left h
    nth_rw 1 [isRelPrime_comm, irreducible_X.isRelPrime_iff_not_dvd,
      show (X : ℤ[X]) = X - C 0 by simp, dvd_iff_isRoot]
    simp [show n ≠ 0 by lia]
  have de : (X ^ (m - n + 1) + X ^ (m - n) - 1 : ℤ[X]).natDegree = m - n + 1 := by
    compute_degree <;> lia
  have db₂ := natDegree_le_of_dvd h (ne_zero_of_natDegree_gt (n := 0) (by lia))
  rw [natDegree_denompol hn, de] at db₂
  -- Analytic part: given the above, `m - n ≤ 2`
  suffices m - n ≤ 2 by lia
  let hom := Int.castRingHom ℝ
  obtain ⟨r, br, hr⟩ : ∃ r ∈ Set.Ioo 0 1, (X ^ n + X ^ 2 - 1 : ℤ[X]).eval₂ hom r = 0 := by
    simp only [eval₂_sub, eval₂_add, eval₂_X_pow, eval₂_one]
    let f (r : ℝ) := r ^ n + r ^ 2 - 1
    have cf : ContinuousOn f (Set.Icc 0 1) := by fun_prop
    have ivt := intermediate_value_Ioo zero_le_one cf
    have f0 : f 0 = -1 := by simp [f]; lia
    have f1 : f 1 = 1 := by simp [f]
    rw [f0, f1] at ivt
    simpa using ivt (by simp)
  have hr₂ := eval₂_dvd hom r h
  simp only [eval₂_sub, eval₂_add, eval₂_X_pow, eval₂_one] at hr hr₂
  rw [hr, zero_dvd_iff, ← hr, sub_left_inj] at hr₂
  rw [← pow_le_pow_iff_right_of_lt_one₀ br.1 br.2] at db₂
  have fin : r ^ 2 ≤ r ^ (m - n) := by linarith
  rwa [pow_le_pow_iff_right_of_lt_one₀ br.1 br.2] at fin

end
snip end

determine solution : Set (ℕ × ℕ) := {⟨5, 3⟩}

problem imo2002_p3 {m n : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n) :
    ⟨m, n⟩ ∈ solution ↔
    {a : ℤ | 0 < a ∧ a ^ n + a ^ 2 - 1 ∣ a ^ m + a - 1}.Infinite := by
  simp only [solution, Set.mem_singleton_iff, Prod.mk.injEq]
  refine ⟨fun h ↦ ?_, proof_body hm hn⟩
  rw [h.1, h.2]
  conv =>
    enter [1, 1, a]
    rw [show a ^ 5 + a - 1 = (a ^ 2 - a + 1) * (a ^ 3 + a ^ 2 - 1) by ring]
  simp only [dvd_mul_left, and_true]; exact Set.Ioi_infinite 0

end Imo2002P3
