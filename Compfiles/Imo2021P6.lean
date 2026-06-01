/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw, Markus Rydh
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 2021, Problem 6

Let m ≥ 2 be an integer, A a finite set of integers (not necessarily
positive) and B₁, B₂, ... Bₘ subsets of A. Suppose that for every
k = 1, 2, ..., m, the sum of the elements of Bₖ is m^k. Prove that
A contains at least m/2 elements.
-/

namespace Imo2021P6

snip begin

open Finset

attribute [local instance] Matrix.seminormedAddCommGroup

variable {m : ℕ} {A C : Finset ℤ} {a : ℤ} {k : Fin m} {B : Fin m → Finset ℤ} {t : Fin m → ℤ}

def incidenceCoeff (B : Fin m → Finset ℤ) (a : ℤ) (k : Fin m) : ℤ := if a ∈ B k then 1 else 0

lemma term_mul_subset_indicator : t k * (if a ∈ B k then a else 0) =
    a * (incidenceCoeff B a k * t k) := by grind [incidenceCoeff]

lemma small_coeffs_eq_zero_of_sum_pow_eq_zero (hm : 2 ≤ m) : ∀ n (c : Fin n → ℤ),
    (∀ i, |c i| < m) → (∑ i, c i * m ^ (i : ℕ) = 0) → ∀ i, c i = 0 := by
  intro n c hc hs i
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      simp only [Fin.sum_univ_succ, Fin.val_zero, pow_zero, mul_one] at hs
      have htail_dvd : (m : ℤ) ∣ ∑ x : Fin n, c x.succ * m ^ (x.succ : ℕ) := by
        apply dvd_sum
        intro x _
        have hpos : 1 ≤ (x.succ : ℕ) := by simp [Fin.val_succ]
        have hp : (m : ℤ) ∣ (m : ℤ) ^ (x.succ : ℕ) := by
          simpa only [pow_one] using (pow_dvd_pow (m : ℤ) hpos)
        exact dvd_mul_of_dvd_right hp (c x.succ)
      have hc0_dvd : (m : ℤ) ∣ c 0 := by
        have hc0_eq : c 0 = - (∑ x : Fin n, c x.succ * m ^ (x.succ : ℕ)) := by lia
        rw [hc0_eq]
        exact dvd_neg.mpr htail_dvd
      have hc0 : c 0 = 0 := Int.eq_zero_of_abs_lt_dvd hc0_dvd (hc 0)
      by_cases hi : i = 0
      · simp [hi, hc0]
      · have hfactor : (∑ x : Fin n, c x.succ * m ^ (x.succ : ℕ)) =
              m * ∑ x : Fin n, c x.succ * m ^ (x : ℕ) := by grind only [mul_sum, Fin.val_succ]
        have hinner : ∑ x : Fin n, c x.succ * m ^ (x : ℕ) = 0 := by
          have hmul : m * (∑ x : Fin n, c x.succ * m ^ (x : ℕ)) = 0 := by grind
          exact (mul_eq_zero.mp hmul).resolve_left (by lia)
        cases i using Fin.cases with
        | zero => contradiction
        | succ j => exact (ih (fun x : Fin n => c x.succ) (fun x => hc x.succ) hinner) j

lemma card_pos_of_sum_powers (hm : 2 ≤ m) (hB : ∀ k, B k ⊆ A)
    (hs : ∀ k, ∑ b ∈ B k, b = m ^ (k.val + 1)) : 0 < A.card := by
  by_contra hA_not
  have hB0empty : B ⟨0, by lia⟩ = ∅ := by grind
  grind

lemma subset_sum_eq_subtype_sum (hC : C ⊆ A) :
    (∑ a : A, if (a : ℤ) ∈ C then (a : ℤ) else 0) = ∑ c ∈ C, c := by
  have : (∑ a : A, if (a : ℤ) ∈ C then (a : ℤ) else 0) =
      ∑ a ∈ A, if (a : ℤ) ∈ C then (a : ℤ) else 0 := by
    simp [← Finset.sum_attach A (fun a => if (a : ℤ) ∈ C then (a : ℤ) else 0)]
  rw [this, ← sum_filter]
  congr 1
  grind

lemma siegel_incidence_relation (hm : 2 ≤ m) (hB : ∀ k, B k ⊆ A)
    (hs : ∀ k, ∑ b ∈ B k, b = m ^ (k.val + 1)) (hlt_two : 2 * A.card < m) :
    ∃ t : Fin m → ℤ, t ≠ 0 ∧ (∀ a : A, ∑ k, incidenceCoeff B a k * t k = 0) ∧
    ∀ k, |t k| < m := by
  let M : Matrix A (Fin m) ℤ := fun a k => incidenceCoeff B a k
  have hrows : Fintype.card A < Fintype.card (Fin m) := by
    simpa [Fintype.card_coe, Fintype.card_fin] using (show A.card < m by lia)
  have hApos := card_pos_of_sum_powers hm hB hs
  have hrowpos : 0 < Fintype.card A := by simpa [Fintype.card_coe] using hApos
  rcases Int.Matrix.exists_ne_zero_int_vec_norm_le M hrows hrowpos with
    ⟨t, htne, hMt, hnorm⟩
  have hrel : ∀ a : A, (∑ k, incidenceCoeff B a k * t k) = 0 := by
    intro a
    simpa [M, Matrix.mulVec, dotProduct] using congr_fun hMt a
  have hMnorm : ‖M‖ ≤ 1 := by
    rw [Matrix.norm_le_iff zero_le_one]
    intro a k
    by_cases h : (a : ℤ) ∈ B k <;> simp [M, incidenceCoeff, h]
  have hbound : ‖t‖ ≤ (m : ℝ) ^ ((A.card : ℝ) / ((m : ℝ) - A.card)) := by
    have hmax : max 1 ‖M‖ = 1 := max_eq_left hMnorm
    simpa [M, Fintype.card_fin, Fintype.card_coe, hmax, mul_one] using hnorm
  have hrpow_lt : (m : ℝ) ^ ((A.card : ℝ) / ((m : ℝ) - A.card)) < (m : ℝ) := by
    have hbase : (1 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hm)
    have hden : 0 < (m : ℝ) - A.card := by
      have : (A.card : ℝ) < m := by linarith [show (2 * A.card : ℝ) < m by exact_mod_cast hlt_two]
      linarith
    have hexp : (A.card : ℝ) / ((m : ℝ) - A.card) < 1 := by
      rw [div_lt_one hden]
      linarith [show (2 * A.card : ℝ) < m by exact_mod_cast hlt_two]
    exact Real.rpow_lt_self_of_one_lt hbase hexp
  have hsmall : ∀ k : Fin m, |t k| < m := by
    intro k
    have htk_real : ‖t k‖ < (m : ℝ) := by
      have ht_le := (pi_norm_le_iff_of_nonneg (norm_nonneg t)).mp le_rfl k
      exact lt_of_le_of_lt ht_le (lt_of_le_of_lt hbound hrpow_lt)
    have htk_abs_real : ((|t k| : ℤ) : ℝ) < (m : ℝ) := by simpa [Int.norm_eq_abs] using htk_real
    exact_mod_cast htk_abs_real
  exact ⟨t, htne, hrel, hsmall⟩

lemma incidence_relation_gives_power_relation (hB : ∀ k, B k ⊆ A)
    (hs : ∀ k, ∑ b ∈ B k, b = m ^ (k.val + 1))
    (hrel : ∀ a : A, (∑ k, incidenceCoeff B a k * t k) = 0) :
    ∑ k, t k * m ^ (k.val + 1) = 0 := by
  calc
    ∑ k, t k * m ^ (k.val + 1) = ∑ k, t k * (∑ a : A, if (a : ℤ) ∈ B k then (a : ℤ) else 0) := by
      exact sum_congr rfl fun k _ => by rw [subset_sum_eq_subtype_sum (hB k), hs k]
    _ = ∑ a : A, (a : ℤ) * (∑ k, incidenceCoeff B a k * t k) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => term_mul_subset_indicator
    _ = 0 := by
      have : ∑ a : A, a * (∑ k, incidenceCoeff B a k * t k) = ∑ a : A, 0 := by
        exact sum_congr rfl fun a _ => by grind [hrel a]
      simpa [this]

lemma small_relation_eq_zero (hm : 2 ≤ m) (hsmall : ∀ k : Fin m, |t k| < m)
    (hpoly : ∑ k, t k * m ^ (k.val + 1) = 0) : t = 0 := by
  have hpoly0 : ∑ k, t k * m ^ k.val = 0 := by
    have hfactor : ∑ k, t k * m ^ (k.val + 1) = m * ∑ k, t k * m ^ k.val := by grind [Finset.mul_sum]
    have hmul : m * ∑ k, t k * m ^ k.val = 0 := by grind
    exact (mul_eq_zero.mp hmul).resolve_left (by lia)
  funext k
  exact small_coeffs_eq_zero_of_sum_pow_eq_zero hm m t hsmall hpoly0 k

snip end

problem imo2021_p6 (m : ℕ) (hm : 2 ≤ m) (A : Finset ℤ)
    (B : Fin m → Finset ℤ) (hB : ∀ k, B k ⊆ A)
    (hs : ∀ k, ∑ b ∈ B k, b = (m : ℤ) ^ (k.val + 1))
    : m ≤ 2 * A.card := by
  by_contra! hnot
  rcases siegel_incidence_relation hm hB hs hnot with ⟨t, htne, hrel, hsmall⟩
  have hpoly := incidence_relation_gives_power_relation hB hs hrel
  exact htne (small_relation_eq_zero hm hsmall hpoly)

end Imo2021P6
