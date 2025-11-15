/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw, Benpigchu
-/

import Mathlib.Tactic
import Mathlib.Analysis.MeanInequalities

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 2012, Problem 2

Let a₂, a₃, ..., aₙ be positive reals with product 1, where n ≥ 3.
Show that
  (1 + a₂)²(1 + a₃)³...(1 + aₙ)ⁿ > nⁿ.
-/

namespace Imo2012P2

snip begin

universe u v

lemma Finset.prod_eq_prod_iff_of_pos_of_le {ι : Type u} {R : Type v}
  [CommMonoidWithZero R] [PartialOrder R] [ZeroLEOneClass R]
  [PosMulStrictMono R] [MulPosStrictMono R] [Nontrivial R]
  [DecidableEq ι] {f g : ι → R} {s : Finset ι}
  (h₀ : ∀ i ∈ s, 0 < f i) (h₁ : ∀ i ∈ s, f i ≤ g i) :
  ∏ i ∈ s, f i = ∏ i ∈ s, g i ↔ ∀ i ∈ s, f i = g i := by
  constructor
  · intro h i hi
    rw [← Finset.insert_erase hi] at h
    repeat rw [Finset.prod_insert (Finset.notMem_erase i s)] at h
    have h' : ∏ x ∈ s.erase i, f x ≤ ∏ x ∈ s.erase i, g x := by
      apply Finset.prod_le_prod
      · intro i' hi'
        exact le_of_lt (h₀ i' (Finset.mem_of_mem_erase hi'))
      · intro i' hi'
        exact h₁ i' (Finset.mem_of_mem_erase hi')
    have h'' : 0 < ∏ x ∈ s.erase i, g x := by
      apply lt_of_le_of_lt' h'
      apply Finset.prod_pos
      intro i' hi'
      exact h₀ i' (Finset.mem_of_mem_erase hi')
    rw [mul_eq_mul_iff_eq_and_eq_of_pos (h₁ i hi) h' (h₀ i hi) h''] at h
    exact h.left
  · intro h
    exact Finset.prod_congr (by rfl) h

lemma Real.geom_mean_eq_arith_mean2_weighted_iff
  {w₁ w₂ p₁ p₂ : ℝ} (hw₁ : 0 < w₁) (hw₂ : 0 < w₂)
  (hp₁ : 0 < p₁) (hp₂ : 0 < p₂) (hw : w₁ + w₂ = 1) :
  p₁ ^ w₁ * p₂ ^ w₂ = w₁ * p₁ + w₂ * p₂ ↔ p₁ = p₂ := by
  have h' := Real.geom_mean_eq_arith_mean_weighted_iff' Finset.univ ![w₁, w₂] ![p₁, p₂]
  simp at h'
  have h'' := h' hw₁ hw₂ hw (le_of_lt hp₁) (le_of_lt hp₂)
  rw [h'']
  constructor
  · intro h
    nth_rw 1 [h.left]
    nth_rw 2 [h.right]
  · intro h
    rw [h, ← add_mul, hw, one_mul]
    constructor <;> rfl

lemma aux₁ {n : ℕ} (hn : 2 ≤ n) : (n : ℝ) ^ n = ∏ i ∈ Finset.Icc 2 n, (i : ℝ) ^ i / ((i : ℝ) - 1) ^ (i - 1) := by
  induction' n, hn using Nat.le_induction with n' hn' h'
  · norm_num
  · nth_rw 3 [← Nat.succ_eq_add_one]
    rw [← Nat.succ_eq_succ, ← Finset.insert_Icc_right_eq_Icc_succ (by cutsat : 2 ≤ n'.succ)]
    rw [Finset.prod_insert (by simp), Nat.succ_eq_succ, Nat.succ_eq_add_one, ← h']
    push_cast
    field_simp
    ring

lemma aux₂ {i : ℕ} {x : ℝ} (hi : 2 ≤ i) (hx : 0 < x) : (i : ℝ) ^ i / ((i : ℝ) - 1) ^ (i - 1) * x
  = (i : ℝ) ^ i * (x ^ (1 / (i : ℝ)) * (1 / ((i : ℝ) - 1)) ^ (((i : ℝ) - 1) / (i : ℝ))) ^ i := by
  have hpos₁ : 0 < (i : ℝ) := by
    rw [Nat.cast_pos]
    cutsat
  have hpos₂ : 0 < (i : ℝ) - 1 := by
    rw [← Nat.cast_one, ← Nat.cast_sub (by cutsat), Nat.cast_pos]
    cutsat
  repeat rw [← Real.rpow_natCast]
  rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (by positivity)]
  rw [← Real.rpow_mul (by positivity), Real.div_rpow (by positivity) (by positivity)]
  rw [Real.one_rpow]
  repeat rw [div_mul_cancel₀ _ (by positivity)]
  field_simp
  rw [Real.rpow_one, mul_comm, Nat.cast_sub (by cutsat), Nat.cast_one]

lemma aux₃ {i : ℕ} {x : ℝ} (hi : 2 ≤ i) (hx : 0 < x) : (1 + x) ^ i =
    (i : ℝ) ^ i * ((1 / (i : ℝ)) * x + (((i : ℝ) - 1) / (i : ℝ)) * (1 / ((i : ℝ) - 1))) ^ i := by
  have hpos₁ : 0 < (i : ℝ) := by
    rw [Nat.cast_pos]
    cutsat
  have hpos₂ : 0 < (i : ℝ) - 1 := by
    rw [← Nat.cast_one, ← Nat.cast_sub (by cutsat), Nat.cast_pos]
    cutsat
  repeat rw [← Real.rpow_natCast]
  rw [← Real.mul_rpow (by positivity) (by positivity)]
  field
  ring

lemma aux₄ {i : ℕ} {x : ℝ} (hi : 2 ≤ i) (hx : 0 < x) :
  (i : ℝ) ^ i / ((i : ℝ) - 1) ^ (i - 1) * x ≤ (1 + x) ^ i := by
  have hpos₁ : 0 < (i : ℝ) := by
      rw [Nat.cast_pos]
      cutsat
  have hpos₂ : 0 < (i : ℝ) - 1 := by
    rw [← Nat.cast_one, ← Nat.cast_sub (by cutsat), Nat.cast_pos]
    cutsat
  rw [aux₂ hi hx, aux₃ hi hx, mul_le_mul_iff_right₀ (by positivity)]
  rw [pow_le_pow_iff_left₀ (by positivity) (by positivity) (by cutsat)]
  apply Real.geom_mean_le_arith_mean2_weighted (by positivity) (by positivity) (by positivity) (by positivity)
  field

lemma aux₅ {i : ℕ} {x : ℝ} (hi : 2 ≤ i) (hx : 0 < x) :
  (i : ℝ) ^ i / ((i : ℝ) - 1) ^ (i - 1) * x = (1 + x) ^ i ↔ x = 1 / ((i : ℝ) - 1) := by
  have hpos₁ : 0 < (i : ℝ) := by
      rw [Nat.cast_pos]
      cutsat
  have hpos₂ : 0 < (i : ℝ) - 1 := by
    rw [← Nat.cast_one, ← Nat.cast_sub (by cutsat), Nat.cast_pos]
    cutsat
  rw [aux₂ hi hx, aux₃ hi hx, mul_left_cancel_iff_of_pos (by positivity)]
  repeat rw [← Real.rpow_natCast]
  rw [Real.rpow_left_inj (by positivity) (by positivity) (by positivity)]
  apply Real.geom_mean_eq_arith_mean2_weighted_iff (by positivity) (by positivity) (by positivity) (by positivity)
  field

lemma aux₆ {n : ℕ} (hn : 2 ≤ n) : ∏ x ∈ Finset.Icc 2 n, ((x : ℝ) - 1) = Nat.factorial (n - 1) := by
  induction' n, hn using Nat.le_induction with n' hn' h'
  · norm_num
  · nth_rw 1 [← Nat.succ_eq_add_one]
    rw [← Nat.succ_eq_succ, ← Finset.insert_Icc_right_eq_Icc_succ (by cutsat : 2 ≤ n'.succ)]
    rw [Finset.prod_insert (by simp), Nat.succ_eq_succ, Nat.succ_eq_add_one, h']
    push_cast
    field_simp
    ring_nf
    norm_cast
    rw [Nat.mul_factorial_pred (by cutsat: _)]

snip end

problem imo2012_p2 (n : ℕ) (hn : 3 ≤ n) (a : Finset.Icc 2 n → ℝ)
    (apos : ∀ i, 0 < a i) (aprod : ∏ i, a i = 1) :
    (n:ℝ)^n < ∏ i, (1 + a i)^i.val := by
  set a' : ℕ → ℝ := fun i ↦ if hi : i ∈ Finset.Icc 2 n then a ⟨i, hi⟩ else 1
  have haa' : ∀ i : Finset.Icc 2 n, i ∈ Finset.univ → a i = a' i.val := by
    intro i hi
    simp only [a']
    rw [dif_pos]
  rw [Finset.prod_congr (by rfl) haa'] at aprod
  rw [← Finset.prod_subtype (Finset.Icc 2 n) (by simp)] at aprod
  have ha'i : ∀ i : Finset.Icc 2 n, i ∈ Finset.univ →
    (1 + a i) ^ i.val = (1 + a' i.val) ^ i.val := by
    intro i hi
    rw [haa' i hi]
  rw [Finset.prod_congr (by rfl) ha'i]
  rw [← Finset.prod_subtype (Finset.Icc 2 n) (by simp) (fun i : ℕ ↦ (1 + a' i) ^ i)]
  have hnn : ∀ (n : ℕ) (a' : ℕ → ℝ), 2 ≤ n → ∏ i ∈ Finset.Icc 2 n, a' i = 1 →
    (n : ℝ) ^ n = ∏ i ∈ Finset.Icc 2 n, (i : ℝ) ^ i / ((i : ℝ) - 1) ^ (i - 1) * a' i := by
    intro n a' hn ha'prod
    rw [Finset.prod_mul_distrib, ha'prod, mul_one]
    exact aux₁ hn
  rw [hnn n a' (by cutsat) aprod]
  have ha'pos : ∀ i : ℕ, 0 < a' i := by
    intro i
    simp only [a']
    by_cases! hi : i ∈ Finset.Icc 2 n
    · rw [dif_pos hi]
      apply apos
    · rw [dif_neg hi]
      norm_num
  have hnn' : ∀ i ∈ Finset.Icc 2 n, 0 < (i : ℝ) ^ i / ((i : ℝ) - 1) ^ (i - 1) * a' i := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    rw [mul_pos_iff_of_pos_right (ha'pos i)]
    rw [div_pos_iff_of_pos_left (pow_pos (Nat.cast_pos.mpr (by cutsat)) _)]
    apply pow_pos
    rw [← Nat.cast_one, ← Nat.cast_sub (by cutsat), Nat.cast_pos]
    cutsat
  have hnn'' : ∀ i ∈ Finset.Icc 2 n, 0 ≤ (i : ℝ) ^ i / ((i : ℝ) - 1) ^ (i - 1) * a' i := by
    intro i hi
    apply le_of_lt
    exact hnn' i hi
  have hann : ∀ i ∈ Finset.Icc 2 n, (i : ℝ) ^ i / ((i : ℝ) - 1) ^ (i - 1) * a' i ≤ (1 + a' i) ^ i := by
    intro i hi
    exact aux₄ (Finset.mem_Icc.mp hi).left (ha'pos i)
  apply lt_of_le_of_ne (Finset.prod_le_prod hnn'' hann)
  contrapose! aprod with h'
  rw [Finset.prod_eq_prod_iff_of_pos_of_le hnn' hann] at h'
  have hann' : ∀ i ∈ Finset.Icc 2 n,
    (i : ℝ) ^ i / ((i : ℝ) - 1) ^ (i - 1) * a' i = (1 + a' i) ^ i ↔ a' i = 1 / ((i : ℝ) - 1) := by
    intro i hi
    exact aux₅ (Finset.mem_Icc.mp hi).left (ha'pos i)
  have ha' : ∀ i ∈ Finset.Icc 2 n, a' i = 1 / ((i : ℝ) - 1) := by
    intro i hi
    rw [← hann' i hi]
    exact h' i hi
  rw [Finset.prod_congr (by rfl) ha', Finset.prod_div_distrib, Finset.prod_eq_one (by simp)]
  apply ne_of_lt
  rw [aux₆ (by cutsat : 2 ≤ n), div_lt_comm₀ (Nat.cast_pos.mpr (Nat.factorial_pos _)) (by norm_num)]
  rw [div_one, ← Nat.cast_one, Nat.cast_lt]
  apply lt_of_le_of_ne (Nat.one_le_iff_ne_zero.mpr (Nat.ne_zero_iff_zero_lt.mpr (Nat.factorial_pos _)))
  symm
  intro h''
  rw [Nat.factorial_eq_one] at h''
  cutsat


end Imo2012P2
