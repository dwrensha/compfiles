/-
Copyright (c) 2025 Roozbeh Yousefzadeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Roozbeh Yousefzadeh, Benpigchu
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file {
  tags := [.Algebra]
  importedFrom := "https://github.com/roozbeh-yz/IMO-Steps/blob/main/Lean_v20/imo_proofs/imo_1966_p5.lean"
}

/-!
# International Mathematical Olympiad 1966, Problem 5

Solve the system of equations

  |a_1 - a_2| x_2 +|a_1 - a_3| x_3 +|a_1 - a_4| x_4 = 1
  |a_2 - a_1| x_1 +|a_2 - a_3| x_3 +|a_2 - a_4| x_4 = 1
  |a_3 - a_1| x_1 +|a_3 - a_2| x_2 +|a_3 - a_4| x_4 = 1
  |a_4 - a_1| x_1 +|a_4 - a_2| x_2 +|a_4 - a_3| x_3 = 1

  where a_1, a_2, a_3, a_4 are four different real numbers.
-/

namespace Imo1966P5

snip begin

noncomputable def raw_order {n : ℕ} (a : Fin n → ℝ) : Fin n → ℕ :=
  fun i ↦ Finset.card {j | a j < a i}

lemma raw_order_lt {n : ℕ} (a : Fin n → ℝ) (i : Fin n)
  : raw_order a i < n := by
  rw [raw_order, ]
  apply lt_of_le_of_ne
  · apply card_finset_fin_le
  · simp only [← Finset.card_fin n]
    rw [ne_eq, Finset.card_filter_eq_iff]
    push_neg
    use i
    constructor
    · apply Finset.mem_univ
    · rfl

noncomputable def order {n : ℕ} (a : Fin n → ℝ) : Fin n → Fin n :=
  fun i ↦ ⟨raw_order a i, raw_order_lt a i⟩

lemma bijective_order {n : ℕ} {a : Fin n → ℝ} (ha : Function.Injective a)
  : Function.Bijective (order a) := by
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · intro i j hij
    contrapose! hij
    wlog hij' : a i < a j generalizing i j
    · symm
      apply this hij.symm
      lia
    apply ne_of_lt
    simp only [order, raw_order, Fin.mk_lt_mk]
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_exists_cons_subset]
    use i
    constructor
    · simp
      rw [Finset.insert_subset_iff]
      constructor
      · simp
        exact hij'
      · intro k hk
        simp at hk ⊢
        exact lt_trans hk hij'
    · simp
  · rfl

noncomputable def nth_smallest_index {n : ℕ} {a : Fin n → ℝ} (ha : Function.Injective a)
  : Fin n → Fin n :=
  Fintype.bijInv (bijective_order ha)

lemma bijective_nth_smallest_index {n : ℕ} {a : Fin n → ℝ} (ha : Function.Injective a)
  : Function.Bijective (nth_smallest_index ha) := by
  exact Fintype.bijective_bijInv (bijective_order ha)

lemma order_comp_nth_smallest_index_eq_id {n : ℕ} {a : Fin n → ℝ} (ha : Function.Injective a)
  : order a ∘ nth_smallest_index ha = id := by
  exact (Fintype.rightInverse_bijInv (bijective_order ha)).id

lemma nth_smallest_index_comp_order_eq_id {n : ℕ} {a : Fin n → ℝ} (ha : Function.Injective a)
  : nth_smallest_index ha ∘ order a = id := by
  exact (Fintype.leftInverse_bijInv (bijective_order ha)).id

noncomputable def nth_smallest {n : ℕ} {a : Fin n → ℝ} (ha : Function.Injective a)
  : Fin n → ℝ := a ∘ (nth_smallest_index ha)

lemma nth_smallest_strictMono {n : ℕ} {a : Fin n → ℝ} (ha : Function.Injective a)
  : StrictMono (nth_smallest ha) := by
  intro i j hij
  rw [nth_smallest, Function.comp_apply, Function.comp_apply]
  contrapose! hij
  rw [← id_eq j, ← id_eq i, ← order_comp_nth_smallest_index_eq_id ha]
  rw [Function.comp_apply, Function.comp_apply]
  set i' := nth_smallest_index ha i
  set j' := nth_smallest_index ha j
  rw [order, order, Fin.mk_le_mk, raw_order, raw_order]
  apply Finset.card_le_card
  intro k hk
  simp at hk ⊢
  exact lt_of_lt_of_le hk hij

lemma order_eq_id_of_strictMono {n : ℕ} {a : Fin n → ℝ} (ha : StrictMono a)
  : order a = id := by
  ext i
  rw [order, Fin.val_mk, id, raw_order, ← Fin.card_Iio]
  congr
  ext j
  simp
  exact ha.lt_iff_lt

lemma nth_smallest_index_eq_id_of_strictMono {n : ℕ} {a : Fin n → ℝ} (ha : StrictMono a)
  : nth_smallest_index ha.injective = id := by
  rw [nth_smallest_index]
  ext x
  have h := Fintype.leftInverse_bijInv (bijective_order ha.injective)
  rw [Function.LeftInverse] at h
  nth_rw 2 [← h x]
  congr
  rw [order_eq_id_of_strictMono ha]
  dsimp

lemma nth_smallest_nth_smallest_eq_nth_smallest {n : ℕ} {a : Fin n → ℝ} (ha : Function.Injective a)
  : nth_smallest (nth_smallest_strictMono ha).injective = nth_smallest ha := by
  rw [nth_smallest, nth_smallest_index_eq_id_of_strictMono (nth_smallest_strictMono ha)]
  rw [Function.comp_id]

lemma order_nth_smallest_eq_id {n : ℕ} {a : Fin n → ℝ} (ha : Function.Injective a)
  : order (nth_smallest ha) = id := by
  apply order_eq_id_of_strictMono
  exact nth_smallest_strictMono ha

snip end

noncomputable determine solution_set_generalized {n : ℕ} (hn : 2 ≤ n)
    {a : Fin n → ℝ} (ha : Function.Injective a) : Set ((Fin n → ℝ)) := {
    fun i : Fin n ↦
      if order a i = ⟨0, by lia⟩ ∨ order a i = ⟨n - 1, by lia⟩
      then 1 / (nth_smallest ha ⟨n - 1, by lia⟩ - nth_smallest ha ⟨0, by lia⟩)
      else 0
  }

snip begin

theorem imo1966_p5_generalized
  {n : ℕ}
  (hn : 2 ≤ n)
  (x a : Fin n → ℝ)
  (ha : Function.Injective a) :
  (∀ i : Fin n, ∑ j : Fin n, abs (a i - a j) * x j = 1)
  ↔ x ∈ solution_set_generalized hn ha := by
  wlog h_mono_a : StrictMono a generalizing a x
  · set a' := nth_smallest ha with ha'
    set x' := x ∘ nth_smallest_index ha with hx'
    have h_mono_a' : StrictMono a' := nth_smallest_strictMono ha
    have h' := this x' a' h_mono_a'.injective h_mono_a'
    have h_iff_left : (∀ (i : Fin n), ∑ j, |a' i - a' j| * x' j = 1)
      ↔ (∀ (i : Fin n), ∑ j, |a i - a j| * x j = 1) := by
      simp only [ha', hx', nth_smallest, Function.comp_apply]
      constructor <;> intro h i
      · rw [← Function.Bijective.sum_comp (bijective_nth_smallest_index ha)]
        rw [← id_eq i, ← nth_smallest_index_comp_order_eq_id ha, Function.comp_apply]
        exact h (order a i)
      · rw [← Function.Bijective.sum_comp (bijective_order ha)]
        simp only [← @Function.comp_apply _ _ _ (nth_smallest_index ha) (order a), nth_smallest_index_comp_order_eq_id]
        exact h (nth_smallest_index ha i)
    have h_iff_right : x' ∈ solution_set_generalized hn h_mono_a'.injective
      ↔ x ∈ solution_set_generalized hn ha := by
      rw [solution_set_generalized, solution_set_generalized, Set.mem_singleton_iff, Set.mem_singleton_iff]
      rw [nth_smallest_nth_smallest_eq_nth_smallest, hx']
      constructor <;> intro h <;> ext i
      · rw [← Function.comp_id x, ← nth_smallest_index_comp_order_eq_id ha]
        rw [← Function.comp_assoc, h, ha']
        rw [order_nth_smallest_eq_id]
        dsimp
      · rw [h, ha']
        dsimp
        rw [order_nth_smallest_eq_id, ← @Function.comp_apply _ _ _ (order a)]
        rw [order_comp_nth_smallest_index_eq_id ha]
    rw [h_iff_left, h_iff_right] at h'
    exact h'
  · rw [solution_set_generalized, Set.mem_singleton_iff]
    rw [order_eq_id_of_strictMono h_mono_a]
    rw [nth_smallest, nth_smallest_index_eq_id_of_strictMono h_mono_a]
    dsimp
    have h_abs : ∀ {i j : Fin n} , j ≤ i → |a i - a j|
      = a i - a j := by
      intro i j hij
      apply abs_of_nonneg
      rw [sub_nonneg]
      exact h_mono_a.monotone hij
    have h_abs' : ∀ {i j : Fin n} , i ≤ j → |a i - a j|
      = a j - a i := by
      intro i j hij
      rw [abs_sub_comm]
      exact h_abs hij
    have h_set : ({i : Fin n | i = ⟨0, by lia⟩ ∨ i = ⟨n - 1, by lia⟩} : Finset _) = {⟨0, by lia⟩, ⟨n - 1, by lia⟩} := by
      ext i
      rw [Finset.mem_insert, Finset.mem_singleton, Finset.mem_filter]
      rw [eq_true (Finset.mem_univ _), true_and]
    have h_0 : 0 < a ⟨n - 1, by lia⟩ - a ⟨0, by lia⟩ := by
      rw [sub_pos]
      apply h_mono_a
      rw [Fin.lt_def]
      lia
    constructor
    · intro h
      have h₁ : ∀ (i : Fin n) (hi : i < ⟨n - 1, by lia⟩),
        (a ⟨↑i + 1, by lia⟩ - a i) ≠ 0 := by
        intro i hi
        apply ne_of_gt
        rw [sub_pos]
        apply h_mono_a
        rw [Fin.lt_def]
        lia
      have h₂ : ∀ (i j : Fin n) (hi : i < ⟨n - 1, by lia⟩),
        |a i - a j| - |a ⟨↑i + 1, by lia⟩ - a j|
        = (a ⟨↑i + 1, by lia⟩ - a i) * (if j ≤ i then -1 else 1) := by
        intro i j hi
        by_cases! hij : j ≤ i
        · rw [h_abs hij, h_abs (by rw [Fin.le_def]; lia), if_pos hij]
          ring
        · rw [h_abs' (by rw [Fin.le_def]; lia), h_abs' (Fin.mk_le_of_le_val hij), if_neg (by rw [Fin.le_def]; lia)]
          ring
      have h₃ : ∀ (i : Fin n) (hi : i < ⟨n - 1, by lia⟩),
        ∑ j, (a ⟨↑i + 1, by lia⟩ - a i) * ((if j ≤ i then -1 else 1) * x j)
        = ∑ j, (|a i - a j| * x j - |a ⟨↑i + 1, by lia⟩ - a j| * x j) := by
        intro i hi
        apply Finset.sum_congr rfl
        intro j _
        rw [← mul_assoc, ← h₂ i j hi, sub_mul]
      have h₄ : ∀ (i : Fin n) (hi : i < ⟨n - 1, by lia⟩),
        ∑ j, (if j ≤ i then -1 else 1) * x j = 0 := by
        rintro i hi
        apply eq_zero_of_ne_zero_of_mul_left_eq_zero (h₁ i hi)
        rw [Finset.mul_sum, h₃ i hi, Finset.sum_sub_distrib]
        rw [h i, h ⟨i.val + 1, by lia⟩]
        norm_num
      have h₅ : ∀ (i : Fin n) (hi_min : ⟨0, by lia⟩ < i) (hi_max : i < ⟨n - 1, by lia⟩),
        ∑ j, ((if j ≤ ⟨i.val - 1, by lia⟩ then -1 else 1) * x j - (if j ≤ i then -1 else 1) * x j)
        = ∑ j, 2 *(if j = i then x j else 0) := by
        intro i hi_min hi_max
        apply Finset.sum_congr rfl
        intro j _
        by_cases! hij : j = i
        · rw [hij, if_neg (by rw [Fin.le_def]; lia), if_pos (by rfl), if_pos (by rfl)]
          ring
        · by_cases! hij' : j < i
          · rw [if_pos (by rw [Fin.le_def]; lia), if_pos (Fin.le_of_lt hij'), if_neg (by lia)]
            ring
          · rw [if_neg (by rw [Fin.le_def]; lia), if_neg (by rw [Fin.le_def]; lia), if_neg (by lia)]
            ring
      have h_mid : ∀ (i : Fin n) (hi_min : ⟨0, by lia⟩ < i) (hi_max : i < ⟨n - 1, by lia⟩),
        x i = 0 := by
        intro i hi_min hi_max
        apply eq_zero_of_ne_zero_of_mul_left_eq_zero (by norm_num : (2 : ℝ) ≠ 0)
        rw [← Fintype.sum_ite_eq' i x, Finset.mul_sum]
        rw [← h₅ i hi_min hi_max, Finset.sum_sub_distrib]
        rw [h₄ ⟨i.val - 1, by lia⟩ (by rw [Fin.lt_def]; lia), h₄ i hi_max]
        norm_num
      have h₆ : ∀ (i : Fin n), ∑ j, (if j = ⟨0, by lia⟩ ∨ j = ⟨n - 1, by lia⟩ then |a i - a j| * x j else 0) = 1 := by
        intro i
        rw [← h i]
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : j = ⟨0, by lia⟩ ∨ j = ⟨n - 1, by lia⟩
        · rw [if_pos hj]
        · rw [if_neg hj]
          symm
          apply mul_eq_zero_of_right
          rw [not_or, Fin.eq_mk_iff_val_eq, Fin.eq_mk_iff_val_eq] at hj
          apply h_mid <;> rw [Fin.lt_def] <;> lia
      ext i
      by_cases hi : i = ⟨0, by lia⟩ ∨ i = ⟨n - 1, by lia⟩
      · rw [if_pos hi]
        rcases hi with hi|hi
        · have h' := h₆ ⟨n - 1, by lia⟩
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero] at h'
          rw [h_set, Finset.sum_pair (by lia), sub_self] at h'
          rw [abs_zero, zero_mul, add_zero, abs_of_pos h_0] at h'
          rw [eq_div_iff (by positivity), hi, mul_comm]
          exact h'
        · have h' := h₆ ⟨0, by lia⟩
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero] at h'
          rw [h_set, Finset.sum_pair (by lia), sub_self] at h'
          rw [abs_zero, zero_mul, zero_add, abs_sub_comm, abs_of_pos h_0] at h'
          rw [eq_div_iff (by positivity), hi, mul_comm]
          exact h'
      · have hi' : ⟨0, by lia⟩ < i ∧ i < ⟨n - 1, by lia⟩ := by
          rw [not_or, Fin.eq_mk_iff_val_eq, Fin.eq_mk_iff_val_eq] at hi
          constructor <;> rw [Fin.lt_def] <;> lia
        rw [h_mid i hi'.left hi'.right, if_neg hi]
    · intro h i
      rw [h]
      dsimp
      simp only [mul_ite, mul_zero]
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
      rw [h_set, Finset.sum_pair (by lia)]
      have h_0 : ⟨0, by lia⟩ ≤ i := by
        rw [Fin.le_def]
        lia
      have h_max : i ≤ ⟨n - 1, by lia⟩ := by
        rw [Fin.le_def]
        lia
      rw [h_abs h_0]
      rw [h_abs' h_max]
      rw [← add_mul]
      field_simp
      ring

snip end

noncomputable determine solution_set {a : Fin 4 → ℝ}
    (ha : Function.Injective a) : Set ((Fin 4 → ℝ)) :=
  solution_set_generalized (by norm_num : 2 ≤ 4) ha

problem imo1966_p5
    (x a : Fin 4 → ℝ)
    (ha : Function.Injective a) :
    (∀ i : Fin 4, ∑ j : Fin 4, abs (a i - a j) * x j = 1)
    ↔ x ∈ solution_set ha := by
  exact imo1966_p5_generalized (by norm_num : 2 ≤ 4) x a ha

end Imo1966P5
