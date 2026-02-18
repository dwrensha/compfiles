/-
Copyright (c) 2026 Constantin Seebach. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Constantin Seebach
-/

import Mathlib.Tactic

import ProblemExtraction

set_option backward.isDefEq.respectTransparency false

problem_file

/-!
# International Mathematical Olympiad 1993, Problem 1

Let $f\left(x\right)=x^n+5x^{n-1}+3$, where $n>1$ is an integer.
Prove that $f\left(x\right)$ cannot be expressed as the product of two non-constant polynomials with integer coefficients.
-/

namespace Imo1993P1

open Polynomial

noncomputable def f (n : ℕ) : ℤ[X] := X^n + 5*X^(n-1) + 3

def isConstant {R : Type*} [Semiring R] (p : R[X]) : Prop := ∀ i > 0, p.coeff i = 0

problem imo1993_p1 : ∀ n > 1, ¬∃ p q : ℤ[X], f n = p*q ∧ ¬ isConstant p ∧ ¬ isConstant q := by
  -- We follow the solution of https://artofproblemsolving.com/wiki/index.php/1993_IMO_Problems/Problem_1

  intro n n_gt_1
  by_contra! t
  let ⟨b, c, fprod, bnc, cnc⟩ := t
  unfold f at fprod

  have h1 : (b.eval 0) * (c.eval 0) = 3 := by
    rw [←eval_mul, ←fprod]
    simp only [eval_add, eval_pow, eval_X, eval_mul, eval_ofNat, add_eq_right]
    rw [zero_pow, zero_pow]
    · simp
    · exact Nat.sub_ne_zero_iff_lt.mpr n_gt_1
    · exact Nat.ne_zero_of_lt n_gt_1

  have h1' : (b.coeff 0) * (c.coeff 0) = 3 := by
    repeat rw [coeff_zero_eq_eval_zero]
    exact h1

  wlog w : 3 ∣ b.coeff 0 generalizing b c
  · apply this c b
    · have : 3 ∣ (b.coeff 0) * (c.coeff 0) := by
        rw [h1']
      rw [Prime.dvd_mul (Int.prime_three)] at this
      grind
    · rw [mul_comm c b]
      exact fprod
    · exact cnc
    · exact bnc
    · rw [mul_comm]
      exact h1
    · rw [mul_comm]
      exact h1'

  wlog wc : c.coeff 0 = 1 generalizing b c
  · have u : IsUnit (c.coeff 0) := by
      have : Prime (b.coeff 0 * c.coeff 0) := by
        rw [h1']
        exact Int.prime_three
      rw [prime_mul_iff] at this
      apply this.by_cases
      · simp
      · rw [Int.isUnit_iff]
        grind
    apply this (-b) (-c)
    · rw [mul_neg, neg_mul, neg_neg]
      exact fprod
    · unfold isConstant
      simp_rw [coeff_neg, neg_eq_zero]
      exact bnc
    · unfold isConstant
      simp_rw [coeff_neg, neg_eq_zero]
      exact cnc
    · simp [h1]
    · simp [h1']
    · simp [w]
    · rw [Int.isUnit_iff] at u
      rw [coeff_neg]
      grind

  have h2 : ∀ i, 0 < i → i < n-1 → (b*c).coeff i = 0 := by
    intro i ibd1 ibd2
    rw [←fprod]
    simp only [coeff_add, coeff_X_pow, coeff_ofNat_mul, mul_ite, mul_one, mul_zero]
    rw [←C_ofNat, coeff_C]
    repeat rw [ite_eq_right_iff.mpr (by grind)]
    rfl

  have h3 : ∀ i, i < n-1 → 3 ∣ b.coeff i := by
    intro i ibd
    induction i using Nat.strong_induction_on with
    | h i ih =>
      match i with
      | 0 => exact w
      | i + 1 =>
        have h2 : _ := h2 (i+1) (by grind) (by grind)
        rw [mul_comm, coeff_mul, Finset.Nat.antidiagonal_succ] at h2
        simp only [Finset.cons_eq_insert, Finset.mem_map, Finset.mem_antidiagonal,
          Function.Embedding.coe_prodMap, Function.Embedding.coeFn_mk, Prod.exists, Prod.map_apply,
          Nat.succ_eq_add_one, Function.Embedding.refl_apply, Prod.mk.injEq, Nat.add_eq_zero_iff,
          one_ne_zero, and_false, false_and, exists_const, not_false_eq_true, Finset.sum_insert,
          Finset.sum_map, Prod.map_fst, Prod.map_snd] at h2
        rw [Int.dvd_iff_emod_eq_zero]
        calc
          _ = (c.coeff 0 * b.coeff (i + 1)) % 3 := by
            rw [Int.mul_emod, wc]
            simp
          _ = - (∑ x ∈ Finset.antidiagonal i, c.coeff (x.1 + 1) * b.coeff x.2) % 3 := by
            rw [add_eq_zero_iff_eq_neg] at h2
            rw [←h2]
          _ = (∑ x ∈ Finset.antidiagonal i, (- c.coeff (x.1 + 1)) * b.coeff x.2) % 3 := by
            rw [←Finset.sum_neg_distrib]
            simp_rw [neg_mul]
          _ = (∑ x ∈ Finset.antidiagonal i, ((- c.coeff (x.1 + 1)) * b.coeff x.2)%3) % 3 := by
            rw [←Finset.sum_int_mod]
          _ = (∑ x ∈ Finset.antidiagonal i, (((- c.coeff (x.1 + 1)) % 3) * (b.coeff x.2 % 3))%3) % 3 := by
            simp_rw [Int.mul_emod _ (b.coeff _)]
          _ = 0 % 3 := by
            congr 1
            apply Finset.sum_eq_zero
            intro x xh
            suffices b.coeff x.2 % 3 = 0 by simp [this]
            rw [←Int.dvd_iff_emod_eq_zero]
            rw [Finset.mem_antidiagonal] at xh
            apply ih <;> lia
          _ = _ := by simp

  have h4 : (b.coeff (n-1) * c.coeff 0) % 3 = 2 := by
    calc
      _ = (b*c).coeff (n-2+1) % 3 := by
        rw [mul_comm b c, coeff_mul, Finset.Nat.antidiagonal_succ]
        simp
        rw [Int.add_emod]
        suffices (∑ i ∈ Finset.antidiagonal (n - 2), c.coeff (i.1 + 1) * b.coeff i.2 % 3) = 0 by
          rw [Finset.sum_int_mod, this]
          grind
        apply Finset.sum_eq_zero
        intro x xh
        rw [Int.mul_emod]
        suffices b.coeff x.2 % 3 = 0 by simp [this]
        rw [←Int.dvd_iff_emod_eq_zero]
        apply h3
        rw [Finset.mem_antidiagonal] at xh
        grind
      _ = _ := by
        rw [←fprod]
        simp only [coeff_add, coeff_X_pow, coeff_ofNat_mul, mul_ite, mul_one, mul_zero,
          coeff_ofNat_succ, add_zero]
        rw [ite_eq_right_iff.mpr (by grind)]
        rw [ite_eq_left_iff.mpr (by grind)]
        simp

  have degb : ↑(n-1) ≤ b.degree := by
    apply le_degree_of_ne_zero
    contrapose! h4
    rw [h4]
    simp

  have degc : 1 ≤ c.degree := by
    unfold isConstant at cnc
    simp only [gt_iff_lt, not_forall] at cnc
    obtain ⟨i, ih1, ih2⟩ := cnc
    trans ↑i
    · exact Nat.one_le_cast.mpr ih1
    · apply le_degree_of_ne_zero
      exact ih2

  have degc : 1 ≤ c.natDegree := by
    rw [natDegree, WithBot.le_unbotD_iff]
    · simp [degc]
    · contrapose! degc
      rw [degc]
      exact compareOfLessAndEq_eq_lt.mp rfl

  have degbc : (b*c).degree = n := by
    rw [←fprod]
    rw [degree_add_eq_left_of_degree_lt, degree_add_eq_left_of_degree_lt]
    · exact degree_X_pow n
    · rw [degree_X_pow, degree_mul_X_pow]
      rw [←C_ofNat, degree_C (by simp)]
      simp [Nat.zero_lt_of_lt n_gt_1]
    · rw [←C_ofNat, degree_C (by simp)]
      rw [degree_add_eq_left_of_degree_lt]
      · simp [Nat.zero_lt_of_lt n_gt_1]
      · rw [degree_X_pow, degree_mul_X_pow]
        rw [←C_ofNat, degree_C (by simp)]
        simp [Nat.zero_lt_of_lt n_gt_1]

  have degbc : (b*c).natDegree = n := by
    rw [natDegree, WithBot.unbotD_eq_iff]
    simp [degbc, Nat.cast_withBot]

  have degc : c.degree = 1 := by
    suffices c.natDegree = 1 by
      unfold natDegree at this
      rw [WithBot.unbotD_eq_iff] at this
      simp only [WithBot.coe_one, degree_eq_bot, one_ne_zero, and_false, or_false] at this
      exact this
    rw [natDegree_mul] at degbc
    · have : n-1 ≤ b.natDegree := by
        rw [natDegree, WithBot.le_unbotD_iff]
        · simp [degb, ←Nat.cast_withBot]
        · contrapose! degb
          rw [degb]
          exact compareOfLessAndEq_eq_lt.mp rfl
      lia
    · exact ne_zero_of_coe_le_degree degb
    · exact ne_zero_of_natDegree_gt degc

  have mc : IsUnit c.leadingCoeff := by
    have : (b*c).leadingCoeff = 1 := by
      rw [←fprod]
      rw [leadingCoeff_add_of_degree_lt', leadingCoeff_add_of_degree_lt']
      · exact leadingCoeff_X_pow n
      · rw [degree_X_pow, degree_mul_X_pow]
        rw [←C_ofNat, degree_C (by simp)]
        simp [Nat.zero_lt_of_lt n_gt_1]
      · rw [←C_ofNat, degree_C (by simp)]
        rw [degree_add_eq_left_of_degree_lt]
        · simp [Nat.zero_lt_of_lt n_gt_1]
        · rw [degree_X_pow, degree_mul_X_pow]
          rw [←C_ofNat, degree_C (by simp)]
          simp [Nat.zero_lt_of_lt n_gt_1]
    rw [Int.isUnit_iff]
    rw [leadingCoeff_mul, Int.mul_eq_one_iff_eq_one_or_neg_one] at this
    grind

  obtain ⟨x, xr⟩ : ∃ x, c.eval x = 0 := by
    have : c = c.leadingCoeff * (X : ℤ[X]) + C (c.coeff 0) := by
      refine ext ?_
      intro i
      rw [coeff_add, coeff_C]
      simp only [coeff_intCast_mul, Int.cast_eq, coeff_X, mul_ite, mul_one, mul_zero]
      split_ifs with h1 h2 h3
      · subst h2
        contradiction
      · subst h1
        rw [leadingCoeff, natDegree_eq_of_degree_eq_some degc]
        simp [One.one]
      · subst h3
        simp
      · rw [coeff_eq_zero_of_degree_lt]
        · simp
        · rw [degc]
          refine Nat.one_lt_cast.mpr ?_
          grind
    use - (c.coeff 0) * mc.invertible.invOf
    nth_rw 4 [this]
    simp
    nth_rw 2 [mul_comm]
    rw [←mul_assoc]
    rw [Invertible.mul_invOf_self (self:=mc.invertible)]
    simp

  have : 0 = (1 : ℤ) := by
    calc
      _ = (b * c).eval x % 2 := by
        rw [eval_mul, xr]
        simp
      _ = (x ^ n + 5 * x ^ (n - 1) + 3) % 2 := by
        rw [←fprod]
        simp
      _ = (x * x ^ (n - 2) * (x+5) + 3) % 2 := by
        congr 1
        have : n - 2 = n - 1 - 1 := by lia
        rw [this, mul_add, mul_pow_sub_one, mul_comm _ x, mul_pow_sub_one]
        · ring
        · lia
        · lia
      _ = 1 % 2 := by
        rw [Int.add_emod]
        rw [Int.mul_emod]
        nth_rw 2 [Int.mul_emod]
        have : (x + 5) % 2 = 0 ∨ x % 2 = 0 := by lia
        apply this.by_cases <;> {
          intro h
          simp [h]
        }
      _ = _ := by simp

  contradiction


end Imo1993P1
