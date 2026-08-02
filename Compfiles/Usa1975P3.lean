/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.EuclideanDomain.Basic
public import Mathlib.Algebra.EuclideanDomain.Field
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Ring
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Algebra] }

/-!
# USA Mathematical Olympiad 1975, Problem 3

A polynomial p(x) of degree n satisfies p(0) = 0, p(1) = 1/2, p(2) = 2/3, ... ,
p(n) = n/(n+1). Find p(n+1).
-/

namespace Usa1975P3

open Polynomial

noncomputable determine answer (n : ℕ) : ℝ := if Odd n then 1 else (n : ℝ) / (n + 2)

snip begin

/-- The degree of `∏_{i < m} (X - i)` is `m`. -/
lemma natDegree_prod_X_sub_C (m : ℕ) :
    (∏ i ∈ Finset.range m, (X - C (i : ℝ))).natDegree = m := by
  have hdeg : (∏ i ∈ Finset.range m, (X - C (i : ℝ))).natDegree =
      ∑ i ∈ Finset.range m, (X - C (i : ℝ)).natDegree :=
    natDegree_prod _ _ fun i _ ↦ X_sub_C_ne_zero _
  rw [hdeg]
  trans ∑ i ∈ Finset.range m, (1 : ℕ)
  · exact Finset.sum_congr rfl fun x _ ↦ natDegree_X_sub_C _
  · simp

/-- `∏_{i < m} (i + 1) = m!`, cast to the reals. -/
lemma prod_range_add_one_cast (m : ℕ) :
    ∏ i ∈ Finset.range m, ((i : ℝ) + 1) = (Nat.factorial m : ℝ) := by
  exact_mod_cast Finset.prod_range_add_one_eq_factorial m

/-- `∏_{i < m} (X - i)` evaluated at `-1` equals `(-1)^m * m!`. -/
lemma eval_prod_X_sub_C_neg_one (m : ℕ) :
    (∏ i ∈ Finset.range m, (X - C (i : ℝ))).eval (-1 : ℝ) = (-1 : ℝ) ^ m * (Nat.factorial m : ℝ) := by
  rw [eval_prod]
  simp only [eval_sub, eval_X, eval_C]
  have h2 : ∀ i ∈ Finset.range m, ((-1 : ℝ) - (i : ℝ)) = (-1) * ((i : ℝ) + 1) :=
    fun i _ ↦ by ring
  rw [Finset.prod_congr rfl h2, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
    prod_range_add_one_cast]

/-- `∏_{i < m} (X - i)` evaluated at `m` equals `m!`. -/
lemma eval_prod_X_sub_C_self (m : ℕ) :
    (∏ i ∈ Finset.range m, (X - C (i : ℝ))).eval (m : ℝ) = (Nat.factorial m : ℝ) := by
  rw [eval_prod]
  simp only [eval_sub, eval_X, eval_C]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have e : ∏ i ∈ Finset.range m, ((m : ℝ) - (i : ℝ)) = ∏ i ∈ Finset.range m, ((i : ℝ) + 1) := by
      rw [← Finset.prod_range_reflect (fun i ↦ (i : ℝ) + 1) m]
      apply Finset.prod_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      show ((m : ℝ) - (j : ℝ)) = ((m - 1 - j : ℕ) : ℝ) + 1
      rw [Nat.cast_sub (by omega : j ≤ m - 1), Nat.cast_sub (by omega : 1 ≤ m)]
      push_cast
      ring
    rw [e, prod_range_add_one_cast]

snip end

problem usa1975_p3 (n : ℕ) (p : ℝ[X]) (hp : p.natDegree = n)
    (h : ∀ k ∈ Finset.range (n + 1), p.eval (k : ℝ) = (k : ℝ) / (k + 1)) :
    p.eval ((n : ℝ) + 1) = answer n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- If `n = 0` then `p` is constant with `p 0 = 0`, hence `p = 0`.
    have h0 : p.eval 0 = 0 := by
      have hh := h 0 (Finset.mem_range.mpr Nat.one_pos)
      simpa using hh
    have hpz : p = 0 := by
      have e := eq_C_of_natDegree_eq_zero hp
      rw [coeff_zero_eq_eval_zero, h0] at e
      rw [e, C_0]
    rw [hpz]
    simp [answer]
  · -- Consider `q(x) = (x + 1) * p(x) - x`, which vanishes at `0, 1, …, n`.
    have hp_ne : p ≠ 0 := by
      rintro rfl
      rw [natDegree_zero] at hp
      omega
    set q : ℝ[X] := (X + 1) * p - X with hq
    have hq_eval : ∀ k ∈ Finset.range (n + 1), q.eval (k : ℝ) = 0 := by
      intro k hk
      have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
      rw [hq, eval_sub, eval_mul, eval_add, eval_X, eval_one, h k hk, mul_div_assoc',
        mul_div_cancel_left₀ (k : ℝ) hk1, sub_self]
    -- The coefficient of `X ^ (n + 1)` in `q` is the leading coefficient of `p`,
    -- so `q` has degree `n + 1`.
    have hpn : p.coeff (n + 1) = 0 :=
      coeff_eq_zero_of_natDegree_lt (by rw [hp]; exact Nat.lt_add_one n)
    have hcoeff : q.coeff (n + 1) = p.leadingCoeff := by
      have hexp : (X + 1 : ℝ[X]) * p = X * p + p := by ring
      rw [hq, hexp, coeff_sub, coeff_add, coeff_X_mul, hpn, coeff_X,
        if_neg (by omega : (1 : ℕ) ≠ n + 1), add_zero, sub_zero, ← coeff_natDegree, hp]
    have hne : q.coeff (n + 1) ≠ 0 := by
      rw [hcoeff]
      exact leadingCoeff_ne_zero.mpr hp_ne
    have hq_ne : q ≠ 0 := by
      intro hq0
      rw [hq0, coeff_zero] at hne
      exact hne rfl
    have hq_deg : q.natDegree = n + 1 := by
      refine le_antisymm ?_ (le_natDegree_of_ne_zero hne)
      have hX1 : (X + 1 : ℝ[X]) = X + C 1 := by rw [C_1]
      have h1_ne : (X + 1 : ℝ[X]) ≠ 0 := by rw [hX1]; exact (monic_X_add_C _).ne_zero
      have hdeg1 : ((X + 1 : ℝ[X]) * p).natDegree = n + 1 := by
        rw [natDegree_mul h1_ne hp_ne, hX1, natDegree_X_add_C, hp, Nat.add_comm]
      calc q.natDegree = (((X + 1 : ℝ[X]) * p) - X).natDegree := by rw [hq]
        _ ≤ max (((X + 1 : ℝ[X]) * p).natDegree) (X : ℝ[X]).natDegree :=
            natDegree_sub_le ((X + 1 : ℝ[X]) * p) X
        _ = max (n + 1) 1 := by rw [hdeg1, natDegree_X]
        _ = n + 1 := max_eq_left (by omega)
    -- Hence `q` is a constant multiple of `∏_{i ≤ n} (X - i)`.
    have hdvd : (∏ i ∈ Finset.range (n + 1), (X - C (i : ℝ))) ∣ q := by
      refine Finset.prod_dvd_of_coprime ?_ ?_
      · intro i _ j _ hij
        exact pairwise_coprime_X_sub_C Nat.cast_injective hij
      · intro i hi
        exact dvd_iff_isRoot.mpr (IsRoot.def.mpr (hq_eval i hi))
    obtain ⟨r, hr⟩ := hdvd
    have hd_ne : (∏ i ∈ Finset.range (n + 1), (X - C (i : ℝ))) ≠ 0 := by
      intro hd0
      have hnd := natDegree_prod_X_sub_C (n + 1)
      rw [hd0, natDegree_zero] at hnd
      omega
    have hr_ne : r ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hr
      exact hq_ne hr
    have hr_deg : r.natDegree = 0 := by
      have h1 : q.natDegree =
          (∏ i ∈ Finset.range (n + 1), (X - C (i : ℝ))).natDegree + r.natDegree := by
        rw [hr, natDegree_mul hd_ne hr_ne]
      rw [hq_deg, natDegree_prod_X_sub_C] at h1
      omega
    obtain ⟨c, rfl⟩ : ∃ c : ℝ, r = C c := ⟨r.coeff 0, eq_C_of_natDegree_eq_zero hr_deg⟩
    have hc_ne : c ≠ 0 := by
      intro hcc
      rw [hcc, C_0] at hr_ne
      exact hr_ne rfl
    -- Evaluate `q` at `-1` to determine `c * (n + 1)!`.
    have hq_neg1 : q.eval (-1 : ℝ) = 1 := by
      rw [hq, eval_sub, eval_mul, eval_add, eval_X, eval_one]
      have h10 : (-1 : ℝ) + 1 = 0 := by norm_num
      rw [h10, zero_mul, zero_sub, neg_neg]
    have key1 : c * ((-1 : ℝ) ^ (n + 1) * (Nat.factorial (n + 1) : ℝ)) = 1 := by
      have e : q.eval (-1 : ℝ) = c * ((-1 : ℝ) ^ (n + 1) * (Nat.factorial (n + 1) : ℝ)) := by
        rw [hr, eval_mul, eval_C, eval_prod_X_sub_C_neg_one]
        ring
      rw [hq_neg1] at e
      exact e.symm
    have key2 : c * (Nat.factorial (n + 1) : ℝ) = (-1 : ℝ) ^ (n + 1) := by
      have h2 : (-1 : ℝ) ^ (n + 1) * (-1 : ℝ) ^ (n + 1) = 1 := by
        rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
      calc c * (Nat.factorial (n + 1) : ℝ)
          = c * (Nat.factorial (n + 1) : ℝ) * ((-1 : ℝ) ^ (n + 1) * (-1 : ℝ) ^ (n + 1)) := by
            rw [h2, mul_one]
        _ = (-1 : ℝ) ^ (n + 1) * (c * ((-1 : ℝ) ^ (n + 1) * (Nat.factorial (n + 1) : ℝ))) := by ring
        _ = (-1 : ℝ) ^ (n + 1) := by rw [key1, mul_one]
    -- Evaluate `q` at `n + 1` to get the value of `p (n + 1)`.
    have hq_succ : q.eval ((n : ℝ) + 1) =
        ((n : ℝ) + 2) * p.eval ((n : ℝ) + 1) - ((n : ℝ) + 1) := by
      rw [hq, eval_sub, eval_mul, eval_add, eval_X, eval_one]
      ring
    have key3 : q.eval ((n : ℝ) + 1) = c * (Nat.factorial (n + 1) : ℝ) := by
      have hde : (∏ i ∈ Finset.range (n + 1), (X - C (i : ℝ))).eval ((n : ℝ) + 1) =
          (Nat.factorial (n + 1) : ℝ) := by
        have e := eval_prod_X_sub_C_self (n + 1)
        push_cast at e
        exact e
      rw [hr, eval_mul, eval_C, hde]
      ring
    have hfinal : ((n : ℝ) + 2) * p.eval ((n : ℝ) + 1) = ((n : ℝ) + 1) + (-1 : ℝ) ^ (n + 1) := by
      rw [key3, key2] at hq_succ
      rw [hq_succ]
      ring
    have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have hsol : p.eval ((n : ℝ) + 1) =
        (((n : ℝ) + 1) + (-1 : ℝ) ^ (n + 1)) / ((n : ℝ) + 2) := by
      rw [eq_div_iff (ne_of_gt hn2)]
      linear_combination hfinal
    rw [hsol]
    rcases Nat.even_or_odd n with heven | hodd
    · -- `n` even: `(-1)^(n+1) = -1` and `p (n+1) = n / (n+2)`.
      have h1 : (-1 : ℝ) ^ (n + 1) = -1 := heven.add_one.neg_one_pow
      rw [h1]
      show ((n : ℝ) + 1 + -1) / ((n : ℝ) + 2) = if Odd n then (1 : ℝ) else (n : ℝ) / (n + 2)
      rw [if_neg (Nat.not_odd_iff_even.mpr heven)]
      congr 1
      ring
    · -- `n` odd: `(-1)^(n+1) = 1` and `p (n+1) = 1`.
      have h1 : (-1 : ℝ) ^ (n + 1) = 1 := hodd.add_one.neg_one_pow
      rw [h1]
      show ((n : ℝ) + 1 + 1) / ((n : ℝ) + 2) = if Odd n then (1 : ℝ) else (n : ℝ) / (n + 2)
      rw [if_pos hodd, div_eq_one_iff_eq (ne_of_gt hn2)]
      ring

end Usa1975P3
