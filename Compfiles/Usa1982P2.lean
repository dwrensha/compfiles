/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Data.Int.Star
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Algebra] }

/-!
# USA Mathematical Olympiad 1982, Problem 2

Show that if m, n are positive integers such that
(x^(m+n) + y^(m+n) + z^(m+n))/(m+n) =
((x^m + y^m + z^m)/m) ((x^n + y^n + z^n)/n)
for all real x, y, z with sum 0, then {m, n} = {2, 3} or {2, 5}.
-/

namespace Usa1982P2

open Polynomial

snip begin

/-- The polynomial `1 + X^k + (-1 - X)^k` over `ℝ`. It arises from substituting
`x = 1`, `y = t`, `z = -1 - t` into `x^k + y^k + z^k` (note `1 + t + (-1 - t) = 0`). -/
noncomputable def auxPoly (k : ℕ) : ℝ[X] := 1 + X ^ k + (C (-1) - X) ^ k

lemma auxPoly_eval (k : ℕ) (t : ℝ) :
    (auxPoly k).eval t = 1 + t ^ k + (-1 - t) ^ k := by
  simp [auxPoly]

lemma auxPoly_one : auxPoly 1 = 0 := by
  have hC : (C (-1) : ℝ[X]) = -1 := by simp
  show 1 + X ^ 1 + (C (-1) - X) ^ 1 = 0
  rw [pow_one, pow_one, hC]
  ring

/-- Rewrite `(-1 - X)^k` as `(-1)^k (1 + X)^k`. -/
lemma auxPoly_eq (k : ℕ) :
    auxPoly k = 1 + X ^ k + C ((-1 : ℝ) ^ k) * (1 + X) ^ k := by
  have h1 : (C (-1) - X : ℝ[X]) = -(1 + X) := by
    have hC : (C (-1) : ℝ[X]) = -1 := by simp
    rw [hC]; ring
  have h2 : ((-1 : ℝ[X]) ^ k) = C ((-1 : ℝ) ^ k) := by
    have h3 : ((-1 : ℝ[X])) = C (-1) := by simp
    rw [h3, ← map_pow]
  show 1 + X ^ k + (C (-1) - X) ^ k = 1 + X ^ k + C ((-1 : ℝ) ^ k) * (1 + X) ^ k
  rw [h1, neg_pow, h2]

lemma auxPoly_coeff_self {k : ℕ} (hk : 1 ≤ k) :
    (auxPoly k).coeff k = 1 + (-1 : ℝ) ^ k := by
  rw [auxPoly_eq, coeff_add, coeff_add, coeff_one, coeff_X_pow, coeff_C_mul,
    coeff_one_add_X_pow]
  have h1 : k ≠ 0 := by omega
  simp [h1, Nat.choose_self]

lemma auxPoly_coeff_pred {k : ℕ} (hk : 2 ≤ k) :
    (auxPoly k).coeff (k - 1) = (-1 : ℝ) ^ k * k := by
  rw [auxPoly_eq, coeff_add, coeff_add, coeff_one, coeff_X_pow, coeff_C_mul,
    coeff_one_add_X_pow]
  have h1 : k - 1 ≠ 0 := by omega
  have h2 : k - 1 ≠ k := by omega
  have h3 : (k.choose (k - 1) : ℝ) = k := by
    have h4 : k.choose (k - 1) = k := by
      rw [Nat.choose_symm (by omega : 1 ≤ k), Nat.choose_one_right]
    rw [h4]
  simp [h1, h2, h3]

lemma natDegree_auxPoly_le (k : ℕ) : (auxPoly k).natDegree ≤ k := by
  have hC : (C (-1) - X : ℝ[X]).natDegree ≤ 1 :=
    le_trans (natDegree_sub_le _ _)
      (by rw [natDegree_C, natDegree_X]; exact max_le (Nat.zero_le 1) (le_refl 1))
  have hCX : ((C (-1) - X : ℝ[X]) ^ k).natDegree ≤ k :=
    le_trans natDegree_pow_le
      (le_trans (Nat.mul_le_mul_left k hC) (le_of_eq (mul_one k)))
  have h1X : (1 + X ^ k : ℝ[X]).natDegree ≤ k := by
    have h1 : (1 : ℝ[X]).natDegree ≤ k := by rw [natDegree_one]; exact Nat.zero_le k
    have h2 := natDegree_add_le_of_le h1 (natDegree_X_pow_le k)
    rwa [max_self] at h2
  have h3 := natDegree_add_le_of_le h1X hCX
  rwa [max_self] at h3

/-- The polynomial identity obtained from the functional equation by substituting
`x = 1, y = t, z = -1 - t` and clearing denominators. -/
lemma auxPoly_mul_eq (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (h : ∀ x y z : ℝ, x + y + z = 0 →
      (x ^ (m + n) + y ^ (m + n) + z ^ (m + n)) / (m + n) =
        (x ^ m + y ^ m + z ^ m) / m * ((x ^ n + y ^ n + z ^ n) / n)) :
    auxPoly (m + n) * C ((m : ℝ) * n) = auxPoly m * auxPoly n * C ((m : ℝ) + n) := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hmnR : ((m : ℝ) + n) ≠ 0 := by positivity
  apply Polynomial.funext
  intro t
  have hh := h 1 t (-1 - t) (by ring)
  simp only [one_pow] at hh
  simp only [auxPoly_eval, eval_mul, eval_C]
  field_simp at hh
  linear_combination hh

/-- Comparison of the coefficients of `X ^ (m + n - 1)` in `auxPoly_mul_eq`. -/
lemma coeff_eq (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hid : auxPoly (m + n) * C ((m : ℝ) * n) = auxPoly m * auxPoly n * C ((m : ℝ) + n)) :
    (-1 : ℝ) ^ (m + n) * ((m : ℝ) + n) * ((m : ℝ) * n) =
      ((auxPoly m).coeff (m - 1) * (auxPoly n).coeff n +
        (auxPoly m).coeff m * (auxPoly n).coeff (n - 1)) * ((m : ℝ) + n) := by
  have hsum : ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal (m + n - 1),
      (auxPoly m).coeff ij.1 * (auxPoly n).coeff ij.2 =
      (auxPoly m).coeff (m - 1) * (auxPoly n).coeff n +
        (auxPoly m).coeff m * (auxPoly n).coeff (n - 1) := by
    have hsub : ({(m - 1, n), (m, n - 1)} : Finset (ℕ × ℕ)) ⊆
        Finset.HasAntidiagonal.antidiagonal (m + n - 1) := by
      rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      constructor
      · rw [Finset.HasAntidiagonal.mem_antidiagonal]; show m - 1 + n = m + n - 1; omega
      · rw [Finset.HasAntidiagonal.mem_antidiagonal]; show m + (n - 1) = m + n - 1; omega
    have hzero : ∀ ij ∈ Finset.HasAntidiagonal.antidiagonal (m + n - 1),
        ij ∉ ({(m - 1, n), (m, n - 1)} : Finset (ℕ × ℕ)) →
        (auxPoly m).coeff ij.1 * (auxPoly n).coeff ij.2 = 0 := by
      intro ij hij1 hij2
      rcases ij with ⟨i, j⟩
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij1
      have hij1' : i + j = m + n - 1 := hij1
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hij2
      by_cases hi : m < i
      · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (natDegree_auxPoly_le m) hi),
          zero_mul]
      · by_cases hj : n < j
        · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (natDegree_auxPoly_le n) hj),
            mul_zero]
        · push Not at hi hj
          have hcon : (i = m - 1 ∧ j = n) ∨ (i = m ∧ j = n - 1) := by omega
          rcases hcon with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact absurd rfl hij2.1
          · exact absurd rfl hij2.2
    rw [← Finset.sum_subset hsub hzero]
    have hne : (m - 1, n) ∉ ({(m, n - 1)} : Finset (ℕ × ℕ)) := by
      simp only [Finset.mem_singleton, Prod.ext_iff]
      omega
    rw [Finset.sum_insert hne, Finset.sum_singleton]
  have hc : (auxPoly (m + n) * C ((m : ℝ) * n)).coeff (m + n - 1) =
      (auxPoly m * auxPoly n * C ((m : ℝ) + n)).coeff (m + n - 1) := by rw [hid]
  rw [coeff_mul_C, auxPoly_coeff_pred (by omega : 2 ≤ m + n)] at hc
  rw [coeff_mul_C, coeff_mul, hsum] at hc
  push_cast at hc
  linear_combination hc

/-- With `n = 2` and `m` odd, evaluating the equation at `(x, y, z) = (1, 1, -2)`
forces `m ∈ {3, 5}`. -/
lemma final_odd (m n : ℕ) (hm : 0 < m) (hn : n = 2) (hmo : Odd m)
    (h : ∀ x y z : ℝ, x + y + z = 0 →
      (x ^ (m + n) + y ^ (m + n) + z ^ (m + n)) / (m + n) =
        (x ^ m + y ^ m + z ^ m) / m * ((x ^ n + y ^ n + z ^ n) / n)) :
    m = 3 ∨ m = 5 := by
  subst hn
  have hodd2 : Odd (m + 2) := hmo.add_even ⟨1, rfl⟩
  have h1 := h 1 1 (-2) (by norm_num)
  simp only [one_pow] at h1
  rw [hmo.neg_pow 2, hodd2.neg_pow 2] at h1
  norm_num at h1
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hm2R : (m : ℝ) + 2 ≠ 0 := by positivity
  field_simp at h1
  rw [pow_add] at h1
  norm_num at h1
  -- The equation reduces to `2 ^ m * (6 - m) = 4 * m + 12`.
  have key : (2 : ℝ) ^ m * (6 - m) = 4 * m + 12 := by linear_combination h1
  have hA : (0 : ℝ) < 2 ^ m := by positivity
  by_cases hm6 : m ≤ 6
  · interval_cases m
    · norm_num at key
    · norm_num at key
    · exact Or.inl rfl
    · norm_num at key
    · exact Or.inr rfl
    · norm_num at key
  · push Not at hm6
    have h1' : (6 : ℝ) - (m : ℝ) < 0 := by
      have h2 : (6 : ℝ) < (m : ℝ) := by exact_mod_cast hm6
      linarith
    have h3 : (2 : ℝ) ^ m * (6 - m) < 0 := mul_neg_of_pos_of_neg hA h1'
    have h4 : (0 : ℝ) < 4 * (m : ℝ) + 12 := by positivity
    linarith [key]

snip end

problem usa1982_p2 (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (h : ∀ x y z : ℝ, x + y + z = 0 →
      (x ^ (m + n) + y ^ (m + n) + z ^ (m + n)) / (m + n) =
        (x ^ m + y ^ m + z ^ m) / m * ((x ^ n + y ^ n + z ^ n) / n)) :
    (m = 2 ∧ n = 3) ∨ (m = 3 ∧ n = 2) ∨ (m = 2 ∧ n = 5) ∨ (m = 5 ∧ n = 2) := by
  -- solution following https://prase.cz/kalva/usa/usoln/usol822.html
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hmnR : ((m : ℝ) + n) ≠ 0 := by positivity
  -- Comparing the coefficients of `X ^ (m + n - 1)` after substituting
  -- `x = 1, y = t, z = -1 - t`.
  have eqB := coeff_eq m n hm hn (auxPoly_mul_eq m n hm hn h)
  -- Evaluating the equation at `(x, y, z) = (1, -1, 0)`.
  have eqA := h 1 (-1) 0 (by norm_num)
  simp only [one_pow] at eqA
  rw [zero_pow (Nat.ne_of_gt (Nat.add_pos_left hm n)), zero_pow (Nat.ne_of_gt hm),
    zero_pow (Nat.ne_of_gt hn), add_zero, add_zero, add_zero] at eqA
  -- `m = 1` is impossible: the left side of `eqB` is nonzero, but the right side
  -- vanishes since `auxPoly 1 = 0`.
  have hm1 : m ≠ 1 := by
    intro hm1
    subst hm1
    rw [auxPoly_one, coeff_zero, coeff_zero, zero_mul, zero_mul, add_zero, zero_mul] at eqB
    have hne : (-1 : ℝ) ^ (1 + n) * ((1 : ℝ) + (n : ℝ)) * ((1 : ℝ) * (n : ℝ)) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (by positivity))
        (mul_ne_zero one_ne_zero hnR)
    push_cast at eqB
    exact hne eqB
  -- Similarly `n = 1` is impossible.
  have hn1 : n ≠ 1 := by
    intro hn1
    subst hn1
    rw [auxPoly_one, coeff_zero, coeff_zero, mul_zero, mul_zero, add_zero, zero_mul] at eqB
    have hne : (-1 : ℝ) ^ (m + 1) * ((m : ℝ) + 1) * ((m : ℝ) * 1) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (by positivity))
        (mul_ne_zero hmR one_ne_zero)
    push_cast at eqB
    exact hne eqB
  have hm2 : 2 ≤ m := by omega
  have hn2 : 2 ≤ n := by omega
  rw [auxPoly_coeff_pred hm2, auxPoly_coeff_pred hn2,
    auxPoly_coeff_self (by omega : 1 ≤ m), auxPoly_coeff_self (by omega : 1 ≤ n)] at eqB
  rcases Nat.even_or_odd m with hme | hmo
  · rcases Nat.even_or_odd n with hne | hno
    · -- `m, n` both even: the equation at `(1, -1, 0)` forces `m = n = 4`,
      -- which fails at `(1, 1, -2)`.
      have hmn_ev : Even (m + n) := by
        obtain ⟨a, ha⟩ := hme
        obtain ⟨b, hb⟩ := hne
        exact ⟨a + b, by rw [ha, hb]; ring⟩
      rw [hmn_ev.neg_one_pow, hme.neg_one_pow, hne.neg_one_pow] at eqA
      have hmnR2 : (m : ℝ) * n = 2 * ((m : ℝ) + n) := by
        field_simp at eqA
        linarith [eqA]
      have hmnN : m * n = 2 * (m + n) := by exact_mod_cast hmnR2
      obtain ⟨M, rfl⟩ := hme
      obtain ⟨N, rfl⟩ := hne
      have hM : 1 ≤ M := by omega
      have hN : 1 ≤ N := by omega
      have h2 : ((M + M) * (N + N) : ℤ) = 2 * ((M + M) + (N + N)) := by exact_mod_cast hmnN
      have h3 : (M : ℤ) * N = M + N := by nlinarith [h2]
      have hMNz : ((M : ℤ) - 1) * ((N : ℤ) - 1) = 1 := by linear_combination h3
      have hM2 : (M : ℤ) - 1 = 1 :=
        Int.eq_one_of_dvd_one (by omega) ⟨(N : ℤ) - 1, hMNz.symm⟩
      have hN2 : (N : ℤ) - 1 = 1 :=
        Int.eq_one_of_dvd_one (by omega) ⟨(M : ℤ) - 1, by rw [mul_comm]; exact hMNz.symm⟩
      have hMe : M = 2 := by
        have h4 : (M : ℤ) = 2 := by linarith
        exact_mod_cast h4
      have hNe : N = 2 := by
        have h4 : (N : ℤ) = 2 := by linarith
        exact_mod_cast h4
      subst hMe
      subst hNe
      have hc := h 1 1 (-2) (by norm_num)
      norm_num at hc
    · -- `m` even, `n` odd: comparing coefficients of `X ^ (m + n - 1)` gives `m = 2`.
      have hmn_odd : Odd (m + n) := hme.add_odd hno
      rw [hmn_odd.neg_one_pow, hme.neg_one_pow, hno.neg_one_pow] at eqB
      have hkey : (n : ℝ) * ((m : ℝ) + n) * (2 - m) = 0 := by linear_combination eqB
      rcases mul_eq_zero.mp hkey with h1 | h1
      · rcases mul_eq_zero.mp h1 with h2 | h2
        · exact absurd h2 hnR
        · exact absurd h2 hmnR
      · have hm2R : (m : ℝ) = 2 := by linarith
        have hm2N : m = 2 := by exact_mod_cast hm2R
        have h' : ∀ x y z : ℝ, x + y + z = 0 →
            (x ^ (n + m) + y ^ (n + m) + z ^ (n + m)) / (n + m) =
              (x ^ n + y ^ n + z ^ n) / n * ((x ^ m + y ^ m + z ^ m) / m) := by
          intro x y z hh
          have h2 := h x y z hh
          rwa [Nat.add_comm m n, add_comm (m : ℝ) (n : ℝ), mul_comm] at h2
        rcases final_odd n m hn hm2N hno h' with hnf | hnf
        · exact Or.inl ⟨hm2N, hnf⟩
        · exact Or.inr (Or.inr (Or.inl ⟨hm2N, hnf⟩))
  · rcases Nat.even_or_odd n with hne | hno
    · -- `m` odd, `n` even: comparing coefficients of `X ^ (m + n - 1)` gives `n = 2`.
      have hmn_odd : Odd (m + n) := hmo.add_even hne
      rw [hmn_odd.neg_one_pow, hmo.neg_one_pow, hne.neg_one_pow] at eqB
      have hkey : (m : ℝ) * ((m : ℝ) + n) * (2 - n) = 0 := by linear_combination eqB
      rcases mul_eq_zero.mp hkey with h1 | h1
      · rcases mul_eq_zero.mp h1 with h2 | h2
        · exact absurd h2 hmR
        · exact absurd h2 hmnR
      · have hn2R : (n : ℝ) = 2 := by linarith
        have hn2N : n = 2 := by exact_mod_cast hn2R
        rcases final_odd m n hm hn2N hmo h with hmf | hmf
        · exact Or.inr (Or.inl ⟨hmf, hn2N⟩)
        · exact Or.inr (Or.inr (Or.inr ⟨hmf, hn2N⟩))
    · -- `m, n` both odd: impossible, since the left side of `eqA` is nonzero
      -- while the right side vanishes.
      have hmn_even : Even (m + n) := hmo.add_odd hno
      rw [hmn_even.neg_one_pow, hmo.neg_one_pow, hno.neg_one_pow] at eqA
      have h2 : ((1 : ℝ) + -1) = 0 := by norm_num
      rw [h2] at eqA
      simp only [zero_div, zero_mul] at eqA
      rw [div_eq_zero_iff] at eqA
      rcases eqA with h1 | h1
      · norm_num at h1
      · exact absurd h1 hmnR

end Usa1982P2
