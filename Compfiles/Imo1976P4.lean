/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benpigchu
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Olympiad 1976, Problem 4

Determine, with proof, the largest number which is the product
of positive integers whose sum is 1976.
-/

namespace Imo1976P4

snip begin

def IsMaxProd (n₀ : ℕ) :=
  fun m ↦ IsGreatest
      { n | ∃ s : Multiset ℕ, s.sum = n₀ ∧ s.prod = n }
      m

def IsMaxProdSet (s : Multiset ℕ) :=
  IsMaxProd (s.sum) (s.prod)

def result : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | n + 3 => 3 * (result n)

lemma prod_le_sum_pow_sum (s : Multiset ℕ) : s.prod ≤ s.sum ^ s.sum := by
  induction' s using Multiset.induction with i s' hs'
  · simp
  · rw [Multiset.sum_cons, Multiset.prod_cons]
    by_cases hi : i = 0
    · rw [hi, zero_mul]
      apply Nat.zero_le
    · push_neg at hi
      rw [← Nat.one_le_iff_ne_zero] at hi
      calc i * s'.prod
          ≤ i * s'.sum ^ s'.sum := mul_le_mul_right hs' i
        _ ≤ (i + s'.sum) * s'.sum ^ s'.sum := mul_le_mul_left (Nat.le_add_right _ _) _
        _ ≤ (i + s'.sum) * (i + s'.sum) ^ s'.sum :=
            mul_le_mul_right (pow_le_pow_left' (Nat.le_add_left _ _) _) _
        _ = (i + s'.sum) ^ (s'.sum + 1) := by exact Nat.pow_add_one'.symm
        _ ≤ (i + s'.sum) ^ (i + s'.sum) := by
          apply pow_le_pow_right'
          · exact Nat.le_add_right_of_le hi
          · rw [add_comm]
            exact Nat.add_le_add_right hi s'.sum

lemma exists_mem_of_sum_lt_zero (s : Multiset ℕ) (hs: 0 < s.sum) :
  ∃ x: ℕ, x ∈ s := by
  have hs' : s ≠ 0 := by
    contrapose! hs
    rw [hs, Multiset.sum_zero]
  exact Multiset.exists_mem_of_ne_zero hs'

lemma prod_with_given_sum_bddAbove (n₀ : ℕ) :
  BddAbove {n | ∃ s : Multiset ℕ, s.sum = n₀ ∧ s.prod = n} := by
    use n₀ ^ n₀
    intro m hm
    rcases hm with ⟨s, ⟨hs_sum, hs_prod⟩⟩
    rw [← hs_sum, ← hs_prod]
    exact prod_le_sum_pow_sum s

lemma exists_max_prod (n : ℕ) :
  ∃ m : ℕ, IsMaxProd n m := by
  apply BddAbove.exists_isGreatest_of_nonempty
  · exact prod_with_given_sum_bddAbove n
  · use n
    use {n}
    constructor
    · rw [Multiset.sum_singleton]
    · rw [Multiset.prod_singleton]

lemma exists_max_prod_set {n m : ℕ} (hnm: IsMaxProd n m):
  ∃ s : Multiset ℕ, s.sum = n ∧ IsMaxProdSet s := by
  rcases hnm.left with ⟨s, ⟨hs_sum, hs_prod⟩⟩
  use s
  constructor
  · exact hs_sum
  · rw [IsMaxProdSet, hs_prod, hs_sum]
    exact hnm

lemma prod_le_max_prod {n m : ℕ} (hnm: IsMaxProd n m)
  {s : Multiset ℕ} (hs : s.sum = n) : s.prod ≤ m := by
  have h := hnm.right
  simp [upperBounds] at h
  exact h s hs

lemma not_max_prod_set_of_prod_lt_prod {s t: Multiset ℕ}
  (hst' : s.sum = t.sum) (hst : s.prod < t.prod) : ¬IsMaxProdSet s := by
  contrapose! hst
  have h' := hst.right
  simp [upperBounds] at h'
  exact h' t hst'.symm

lemma exists_cons_le_of_le_of_sum_lt_sum {s t : Multiset ℕ}
  (hst' : s ≤ t) (hst : s.sum < t.sum) : ∃ n : ℕ, s.cons n ≤ t := by
  have ht_sub_s : t - s ≠ 0 := by
    contrapose! hst
    apply le_of_eq
    calc t.sum
        = (t - s + s).sum := by rw [Multiset.sub_add_cancel hst']
      _ = (t - s).sum + s.sum := by rw [Multiset.sum_add]
      _ = 0 + s.sum := by rw [hst, Multiset.sum_zero]
      _ = s.sum := by rw [zero_add]
  rcases Multiset.exists_mem_of_ne_zero ht_sub_s with ⟨m, hm⟩
  use m
  rw [← Multiset.singleton_add, ← Multiset.sub_add_cancel hst']
  rw [Multiset.add_le_add_iff_right, Multiset.singleton_le]
  exact hm

lemma exists_le_of_mem_of_lt_sum {n : ℕ} {s : Multiset ℕ}
  (hns' : n ∈ s) (hns : n < s.sum) : ∃ m : ℕ, {n, m} ≤ s := by
  rcases Multiset.exists_cons_of_mem hns' with ⟨t, ht⟩
  have ht' : t ≠ 0 := by
    contrapose! hns
    rw [ht, hns, Multiset.sum_cons, Multiset.sum_zero, add_zero]
  rcases Multiset.exists_mem_of_ne_zero ht' with ⟨m, hm⟩
  use m
  rw [ht, Multiset.insert_eq_cons]
  exact Multiset.cons_le_cons n (Multiset.singleton_le.mpr hm)

lemma zero_not_in_max_prod_set {s : Multiset ℕ}
  (hs: IsMaxProdSet s) : 0 ∉ s := by
  contrapose! hs
  have ha : s.sum = (Multiset.replicate s.sum 1).sum := by
    rw [Multiset.sum_replicate, Nat.nsmul_eq_mul, mul_one]
  apply not_max_prod_set_of_prod_lt_prod ha
  rw [Multiset.prod_replicate, one_pow, Multiset.prod_eq_zero hs]
  norm_num

lemma max_prod_set_of_subset_of_max_prod_set {s t : Multiset ℕ}
  (hst : s ≤ t) (ht: IsMaxProdSet t) : IsMaxProdSet s := by
  constructor
  · use s
  · intro n hn
    rcases hn with ⟨s', ⟨hs'_sum, hs'_prod⟩⟩
    have ht_sub_s : (t - s).prod > 0 := by
      apply Nat.zero_lt_of_ne_zero
      apply Multiset.prod_ne_zero
      intro h'
      apply zero_not_in_max_prod_set ht
      rw [Multiset.mem_sub] at h'
      rw [← Multiset.count_pos]
      exact Nat.zero_lt_of_lt h'
    apply Nat.le_of_mul_le_mul_left _ ht_sub_s
    rw [← hs'_prod, ← Multiset.prod_add, ← Multiset.prod_add]
    rw [Multiset.sub_add_cancel hst]
    have h' := ht.right
    simp [upperBounds] at h'
    apply h' (t - s + s')
    calc (t - s + s').sum
        = (t - s).sum + s'.sum := by rw [Multiset.sum_add]
      _ = (t - s).sum + s.sum := by rw [hs'_sum]
      _ = (t - s + s).sum := by rw [Multiset.sum_add]
      _ = t.sum := by rw [Multiset.sub_add_cancel hst]

lemma one_not_in_max_prod_set_of_one_lt_sum {s : Multiset ℕ}
  (hs' : 1 < s.sum) (hs: IsMaxProdSet s) : 1 ∉ s := by
  intro h1s
  rcases exists_le_of_mem_of_lt_sum h1s hs' with ⟨n, hn⟩
  have h1n := max_prod_set_of_subset_of_max_prod_set hn hs
  contrapose! h1n
  have h1n' : ({1, n} : Multiset ℕ).sum = ({1 + n} : Multiset ℕ).sum := by
    rw [Multiset.sum_singleton, Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton]
  apply not_max_prod_set_of_prod_lt_prod h1n'
  rw [Multiset.prod_singleton, Multiset.insert_eq_cons, Multiset.prod_cons, Multiset.prod_singleton]
  omega

lemma not_in_max_prod_set_of_five_le {s : Multiset ℕ} {n : ℕ}
  (hn : 4 < n) (hs: IsMaxProdSet s) : n ∉ s := by
  intro hn'
  have hn'' := max_prod_set_of_subset_of_max_prod_set (Multiset.singleton_le.mpr hn') hs
  contrapose! hn''
  have hn_sub_2 : ({n} : Multiset ℕ).sum = ({n - 2, 2} : Multiset ℕ).sum := by
    rw [Multiset.sum_singleton, Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton]
    symm
    apply Nat.sub_add_cancel
    omega
  apply not_max_prod_set_of_prod_lt_prod hn_sub_2
  rw [Multiset.prod_singleton, Multiset.insert_eq_cons, Multiset.prod_cons, Multiset.prod_singleton]
  omega

lemma lt_and_gt_of_in_max_prod_set_of_four_lt_sum {s : Multiset ℕ} {n : ℕ}
  (hn : n ∈ s) (hs' : 4 < s.sum) (hs: IsMaxProdSet s) : 1 < n ∧  n < 5 := by
  have hn_ne_0 : n ≠ 0 := by
      contrapose! hn
      rw [hn]
      exact zero_not_in_max_prod_set hs
  have hn_ne_1 : n ≠ 1 := by
    contrapose! hn
    rw [hn]
    apply one_not_in_max_prod_set_of_one_lt_sum _ hs
    omega
  have hn_le_4 : n ≤ 4 := by
      contrapose! hn
      exact not_in_max_prod_set_of_five_le hn hs
  omega

lemma three_in_max_prod_set_of_four_lt_sum {s : Multiset ℕ}
  (hs' : 4 < s.sum) (hs: IsMaxProdSet s) : 3 ∈ s := by
  rw [← Multiset.count_ne_zero, Nat.ne_zero_iff_zero_lt]
  have h₁ : s.toFinset ⊆ {2, 3, 4} := by
    intro x hx
    rw [Multiset.mem_toFinset] at hx
    have hx' := lt_and_gt_of_in_max_prod_set_of_four_lt_sum hx hs' hs
    have hx'l := hx'.left
    have hx'r := hx'.right
    interval_cases x <;> simp
  simp [Finset.sum_multiset_count_of_subset _ _ h₁] at hs'
  have h₂ : Multiset.count 2 s < 3 := by
    by_contra! h2
    have h222 : ({2, 2, 2} : Multiset ℕ) ≤ s := by
      rw [Multiset.le_iff_count]
      intro n
      by_cases hn2 : n = 2
      · simp [hn2]
        exact h2
      · have hn' : n ∉ ({2, 2, 2} : Multiset ℕ) := by
          simp [← Multiset.mem_toFinset]
          exact hn2
        rw [Multiset.count_eq_zero_of_notMem hn']
        apply Nat.zero_le
    have h222' := max_prod_set_of_subset_of_max_prod_set h222 hs
    contrapose! h222'
    have h : ({2, 2, 2} : Multiset ℕ).sum = ({3, 3} : Multiset ℕ).sum := by
      simp [Multiset.sum_singleton, Multiset.insert_eq_cons, Multiset.sum_cons]
    apply not_max_prod_set_of_prod_lt_prod h
    simp [Multiset.prod_singleton, Multiset.insert_eq_cons, Multiset.prod_cons]
  have h₃ : Multiset.count 4 s < 2 := by
    by_contra! h4
    have h44 : ({4, 4} : Multiset ℕ) ≤ s := by
      rw [Multiset.le_iff_count]
      intro n
      by_cases hn4 : n = 4
      · simp [hn4]
        exact h4
      · have hn' : n ∉ ({4, 4} : Multiset ℕ) := by
          simp [← Multiset.mem_toFinset]
          exact hn4
        rw [Multiset.count_eq_zero_of_notMem hn']
        apply Nat.zero_le
    have h44' := max_prod_set_of_subset_of_max_prod_set h44 hs
    contrapose! h44'
    have h : ({4, 4} : Multiset ℕ).sum = ({3, 3, 2} : Multiset ℕ).sum := by
      simp [Multiset.sum_singleton, Multiset.insert_eq_cons, Multiset.sum_cons]
    apply not_max_prod_set_of_prod_lt_prod h
    simp [Multiset.prod_singleton, Multiset.insert_eq_cons, Multiset.prod_cons]
  have h₄ : Multiset.count 4 s < 1 ∨ Multiset.count 2 s < 1 := by
    by_contra! h'
    have h24 : ({2, 4} : Multiset ℕ) ≤ s := by
      rw [Multiset.le_iff_count]
      intro n
      by_cases hn4 : n = 4
      · simp [hn4]
        exact h'.left
      · by_cases hn2 : n = 2
        · simp [hn2]
          exact h'.right
        · have hn' : n ∉ ({2, 4} : Multiset ℕ) := by
            simp [← Multiset.mem_toFinset]
            exact ⟨hn2, hn4⟩
          rw [Multiset.count_eq_zero_of_notMem hn']
          apply Nat.zero_le
    have h24' := max_prod_set_of_subset_of_max_prod_set h24 hs
    contrapose! h24'
    have h : ({2, 4} : Multiset ℕ).sum = ({3, 3} : Multiset ℕ).sum := by
      simp [Multiset.sum_singleton, Multiset.insert_eq_cons, Multiset.sum_cons]
    apply not_max_prod_set_of_prod_lt_prod h
    simp [Multiset.prod_singleton, Multiset.insert_eq_cons, Multiset.prod_cons]
  omega

lemma max_prod_zero : IsMaxProd 0 1 := by
  constructor
  · use 0
    constructor <;> rfl
  · intro n hn
    rcases hn with ⟨s, ⟨s_sum, s_prod⟩⟩
    by_cases hs : s = 0
    · rw [← s_prod, hs, Multiset.prod_zero]
    · rcases Multiset.exists_mem_of_ne_zero hs with ⟨m, hm⟩
      have hm' := Multiset.le_sum_of_mem hm
      rw [s_sum] at hm'
      rw [Nat.eq_zero_of_le_zero hm'] at hm
      rw [← s_prod, Multiset.prod_eq_zero hm]
      omega

lemma max_prod_one : IsMaxProd 1 1 := by
  constructor
  · use {1}
    constructor <;> rfl
  · intro n hn
    rcases hn with ⟨s, ⟨s_sum, s_prod⟩⟩
    rcases exists_mem_of_sum_lt_zero s (by omega:_) with ⟨m, hm⟩
    have hm' : m ≤ 1 := by
      rw [← s_sum]
      exact Multiset.le_sum_of_mem hm
    rcases Multiset.exists_cons_of_mem hm with ⟨t, ht⟩
    have ht' : t.sum = 1 - m := by
      rw [← s_sum, ht, Multiset.sum_cons, add_comm, Nat.add_sub_cancel_right]
    rw [← s_prod, ht, Multiset.prod_cons]
    interval_cases m
    · rw [zero_mul]
      norm_num
    · have h := prod_le_max_prod max_prod_zero ht'
      omega

lemma max_prod_two : IsMaxProd 2 2 := by
  constructor
  · use {2}
    constructor <;> rfl
  · intro n hn
    rcases hn with ⟨s, ⟨s_sum, s_prod⟩⟩
    rcases exists_mem_of_sum_lt_zero s (by omega:_) with ⟨m, hm⟩
    have hm' : m ≤ 2 := by
      rw [← s_sum]
      exact Multiset.le_sum_of_mem hm
    rcases Multiset.exists_cons_of_mem hm with ⟨t, ht⟩
    have ht' : t.sum = 2 - m := by
      rw [← s_sum, ht, Multiset.sum_cons, add_comm, Nat.add_sub_cancel_right]
    rw [← s_prod, ht, Multiset.prod_cons]
    interval_cases m
    · rw [zero_mul]
      norm_num
    · have h := prod_le_max_prod max_prod_one ht'
      omega
    · have h := prod_le_max_prod max_prod_zero ht'
      omega

lemma max_prod_three : IsMaxProd 3 3 := by
  constructor
  · use {3}
    constructor <;> rfl
  · intro n hn
    rcases hn with ⟨s, ⟨s_sum, s_prod⟩⟩
    rcases exists_mem_of_sum_lt_zero s (by omega:_) with ⟨m, hm⟩
    have hm' : m ≤ 3 := by
      rw [← s_sum]
      exact Multiset.le_sum_of_mem hm
    rcases Multiset.exists_cons_of_mem hm with ⟨t, ht⟩
    have ht' : t.sum = 3 - m := by
      rw [← s_sum, ht, Multiset.sum_cons, add_comm, Nat.add_sub_cancel_right]
    rw [← s_prod, ht, Multiset.prod_cons]
    interval_cases m
    · rw [zero_mul]
      norm_num
    · have h := prod_le_max_prod max_prod_two ht'
      omega
    · have h := prod_le_max_prod max_prod_one ht'
      omega
    · have h := prod_le_max_prod max_prod_zero ht'
      omega

lemma max_prod_four : IsMaxProd 4 4 := by
  constructor
  · use {4}
    constructor <;> rfl
  · intro n hn
    rcases hn with ⟨s, ⟨s_sum, s_prod⟩⟩
    rcases exists_mem_of_sum_lt_zero s (by omega:_) with ⟨m, hm⟩
    have hm' : m ≤ 4 := by
      rw [← s_sum]
      exact Multiset.le_sum_of_mem hm
    rcases Multiset.exists_cons_of_mem hm with ⟨t, ht⟩
    have ht' : t.sum = 4 - m := by
      rw [← s_sum, ht, Multiset.sum_cons, add_comm, Nat.add_sub_cancel_right]
    rw [← s_prod, ht, Multiset.prod_cons]
    interval_cases m
    · rw [zero_mul]
      norm_num
    · have h := prod_le_max_prod max_prod_three ht'
      omega
    · have h := prod_le_max_prod max_prod_two ht'
      omega
    · have h := prod_le_max_prod max_prod_one ht'
      omega
    · have h := prod_le_max_prod max_prod_zero ht'
      omega

theorem generalized (n : ℕ) :
  IsMaxProd n (result n) := by
  fun_induction result with
  | case1 => exact max_prod_zero
  | case2 => exact max_prod_one
  | case3 => exact max_prod_two
  | case4 => exact max_prod_three
  | case5 => exact max_prod_four
  | case6 n n_ne_zero n_ne_one ih =>
    rw [imp_false, ← ne_eq] at *
    rcases exists_max_prod (n + 3) with ⟨m, hm⟩
    rcases exists_max_prod_set hm with ⟨s, ⟨hs_sum, hs⟩⟩
    have hs_sum' : 4 < s.sum := by
      rw [hs_sum]
      omega
    have hs3 := three_in_max_prod_set_of_four_lt_sum hs_sum' hs
    have hs3' := Multiset.singleton_le.mpr hs3
    have hs_without_3 : s - {3} ≤ s := Multiset.sub_le_self _ _
    have hs_without_3' := max_prod_set_of_subset_of_max_prod_set hs_without_3 hs
    have hs_without_3_sum : (s - {3}).sum = n := by
      calc (s - {3}).sum
          = (s - {3}).sum + ({3} : Multiset _).sum - ({3} : Multiset _).sum := by rfl
        _ = (s - {3} + {3}).sum - ({3} : Multiset _).sum := by rw [Multiset.sum_add]
        _ = s.sum - ({3} : Multiset _).sum := by rw [Multiset.sub_add_cancel hs3']
        _ = n + 3 - 3 := by rw [hs_sum, Multiset.sum_singleton]
        _ = n := by rfl
    rw [IsMaxProdSet, hs_without_3_sum] at hs_without_3'
    have hs_without_3_prod := IsGreatest.unique hs_without_3' ih
    have hs_prod : s.prod = (3 * result n) := by
      calc s.prod
          = (s - {3} + {3}).prod := by rw [Multiset.sub_add_cancel hs3']
        _ = (s - {3}).prod * ({3} : Multiset _).prod := by rw [Multiset.prod_add]
        _ = result n * 3 := by rw [hs_without_3_prod, Multiset.prod_singleton]
        _ = 3 * result n := by apply mul_comm
    rw [IsMaxProdSet, hs_prod, hs_sum] at hs
    exact hs

snip end

determine solution : ℕ := result 1976

problem imo1976_p4 :
    IsGreatest
      { n | ∃ s : Multiset ℕ, s.sum = 1976 ∧ s.prod = n }
      solution := by
  exact generalized 1976


end Imo1976P4
