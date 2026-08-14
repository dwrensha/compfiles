/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics, .Inequality] }

/-!
# USA Mathematical Olympiad 2012, Problem 6

For integer n ≥ 2, let x₁, x₂, ..., xₙ be real numbers satisfying
x₁ + x₂ + ... + xₙ = 0 and x₁² + x₂² + ... + xₙ² = 1.
For each subset A ⊆ {1, 2, ..., n}, define S_A = ∑_{i ∈ A} x_i.
(If A is the empty set, then S_A = 0.)
Prove that for any positive number λ, the number of sets A satisfying
S_A ≥ λ is at most 2^(n-3)/λ². For which choices of x₁, x₂, ..., xₙ, λ
does equality hold?
-/

open Finset

namespace Usa2012P6

/-- Equality holds iff `x` is a permutation of `(1 / √2, -1 / √2, 0, ..., 0)`
and `λ = 1 / √2`. -/
determine equality_cases {n : ℕ} (x : Fin n → ℝ) (lam : ℝ) : Prop :=
  ∃ i j : Fin n, i ≠ j ∧ x i = 1 / Real.sqrt 2 ∧ x j = -(1 / Real.sqrt 2) ∧
    (∀ k : Fin n, k ≠ i → k ≠ j → x k = 0) ∧ lam = 1 / Real.sqrt 2

snip begin

/-- The number of subsets of `s` containing a fixed sub-finset `t` is
`2 ^ (s.card - t.card)`. -/
lemma card_powerset_filter_subset {α : Type*} [DecidableEq α] {s t : Finset α}
    (hst : t ⊆ s) :
    (s.powerset.filter (fun A => t ⊆ A)).card = 2 ^ (s.card - t.card) := by
  have hcs : (s \ t).card = s.card - t.card := by
    rw [card_sdiff, inter_eq_left.mpr hst]
  rw [← hcs, ← card_powerset (s \ t)]
  apply card_bij (fun A _ => A \ t)
  · intro A hA
    rw [mem_filter, mem_powerset] at hA
    exact mem_powerset.mpr (sdiff_subset_sdiff hA.1 subset_rfl)
  · intro A hA B hB hAB
    rw [mem_filter] at hA hB
    have eA : A \ t ∪ t = A := sdiff_union_of_subset hA.2
    have eB : B \ t ∪ t = B := sdiff_union_of_subset hB.2
    rw [hAB] at eA
    rw [eB] at eA
    exact eA.symm
  · intro B hB
    rw [mem_powerset] at hB
    refine ⟨B ∪ t, ?_, ?_⟩
    · rw [mem_filter, mem_powerset]
      exact ⟨union_subset (Subset.trans hB sdiff_subset) hst, subset_union_right⟩
    · apply union_sdiff_cancel_right
      rw [disjoint_left]
      intro a ha
      exact (mem_sdiff.mp (hB ha)).2

/-- Bridge between natural-number powers `2 ^ (n - k)` and integer powers
`(2 : ℝ) ^ ((n : ℤ) - k)`. -/
lemma two_pow_sub (n k : ℕ) (hk : k ≤ n) :
    ((2 ^ (n - k) : ℕ) : ℝ) = (2 : ℝ) ^ ((n : ℤ) - k) := by
  have h1 : (n : ℤ) - k = ((n - k : ℕ) : ℤ) := by
    rw [Nat.cast_sub hk]
  rw [h1, zpow_natCast]
  norm_cast

/-- Master identity: the sum of `S_A ^ 2` over all subsets `A` equals `2 ^ (n - 2)`. -/
lemma sum_subsetSum_sq {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ)
    (hsum : ∑ i, x i = 0) (hsq : ∑ i, x i ^ 2 = 1) :
    ∑ A ∈ univ.powerset, (∑ i ∈ A, x i) ^ 2 = (2 : ℝ) ^ ((n : ℤ) - 2) := by
  have hexpand : ∀ A : Finset (Fin n), (∑ i ∈ A, x i) ^ 2 =
      ∑ i : Fin n, ∑ j : Fin n, if i ∈ A ∧ j ∈ A then x i * x j else 0 := by
    intro A
    have e : ∀ i j : Fin n, (if i ∈ A ∧ j ∈ A then x i * x j else 0) =
        (if i ∈ A then x i else 0) * (if j ∈ A then x j else 0) := by
      intro i j
      by_cases hi : i ∈ A <;> by_cases hj : j ∈ A <;> simp [hi, hj]
    calc (∑ i ∈ A, x i) ^ 2
        = (∑ i, if i ∈ A then x i else 0) * (∑ j, if j ∈ A then x j else 0) := by
          rw [pow_two]
          congr 1 <;> rw [sum_ite_mem, univ_inter]
      _ = ∑ i : Fin n, ∑ j : Fin n,
            (if i ∈ A then x i else 0) * (if j ∈ A then x j else 0) :=
          sum_mul_sum univ univ _ _
      _ = ∑ i : Fin n, ∑ j : Fin n, if i ∈ A ∧ j ∈ A then x i * x j else 0 :=
          sum_congr rfl fun i _ => sum_congr rfl fun j _ => (e i j).symm
  have hcount : ∀ i j : Fin n,
      ∑ A ∈ univ.powerset, (if i ∈ A ∧ j ∈ A then x i * x j else 0) =
        (2 : ℝ) ^ ((n : ℤ) - 2) * (x i * x j) * (if i = j then (2 : ℝ) else 1) := by
    intro i j
    have hset : univ.powerset.filter (fun A => i ∈ A ∧ j ∈ A) =
        univ.powerset.filter ({i, j} ⊆ ·) := by
      apply filter_congr
      intro A _
      constructor
      · intro h
        rw [insert_subset_iff, singleton_subset_iff]
        exact ⟨h.1, h.2⟩
      · intro h
        exact ⟨(insert_subset_iff.mp h).1, singleton_subset_iff.mp (insert_subset_iff.mp h).2⟩
    have hcard : (univ.powerset.filter (fun A => i ∈ A ∧ j ∈ A)).card =
        2 ^ (n - ({i, j} : Finset (Fin n)).card) := by
      rw [hset]
      have h := card_powerset_filter_subset (subset_univ ({i, j} : Finset (Fin n)))
      rwa [card_univ, Fintype.card_fin] at h
    have hcard2 : ({i, j} : Finset (Fin n)).card = if i = j then 1 else 2 := by
      by_cases hij : i = j
      · subst hij
        rw [ite_eq_left rfl, insert_eq_of_mem (mem_singleton_self i), card_singleton]
      · rw [ite_eq_right hij, card_pair hij]
    rw [← sum_filter, sum_const, nsmul_eq_mul, hcard, hcard2]
    by_cases hij : i = j
    · subst hij
      rw [ite_eq_left rfl, ite_eq_left rfl]
      rw [two_pow_sub n 1 (by omega)]
      push_cast
      have h : (2 : ℝ) ^ ((n : ℤ) - 1) = (2 : ℝ) ^ ((n : ℤ) - 2) * 2 := by
        have h1 := zpow_add_one₀ (two_ne_zero : (2 : ℝ) ≠ 0) ((n : ℤ) - 2)
        rwa [show ((n : ℤ) - 2) + 1 = (n : ℤ) - 1 by ring] at h1
      rw [h]
      ring
    · rw [ite_eq_right hij, ite_eq_right hij]
      rw [two_pow_sub n 2 hn]
      ring_nf
  calc ∑ A ∈ univ.powerset, (∑ i ∈ A, x i) ^ 2
      = ∑ A ∈ univ.powerset, ∑ i : Fin n, ∑ j : Fin n,
          if i ∈ A ∧ j ∈ A then x i * x j else 0 :=
        sum_congr rfl fun A _ => hexpand A
    _ = ∑ i : Fin n, ∑ j : Fin n, ∑ A ∈ univ.powerset,
          if i ∈ A ∧ j ∈ A then x i * x j else 0 := by
        rw [sum_comm]
        exact sum_congr rfl fun i _ => sum_comm
    _ = ∑ i : Fin n, ∑ j : Fin n,
          (2 : ℝ) ^ ((n : ℤ) - 2) * (x i * x j) * (if i = j then (2 : ℝ) else 1) :=
        sum_congr rfl fun i _ => sum_congr rfl fun j _ => hcount i j
    _ = ∑ i : Fin n, (2 : ℝ) ^ ((n : ℤ) - 2) * x i ^ 2 := by
        refine sum_congr rfl fun i _ => ?_
        have he : (2 : ℝ) ^ ((n : ℤ) - 2) * (x i * x i) * (if i = i then (2 : ℝ) else 1) +
            ∑ j ∈ univ.erase i, (2 : ℝ) ^ ((n : ℤ) - 2) * (x i * x j) *
              (if i = j then (2 : ℝ) else 1) =
            ∑ j : Fin n, (2 : ℝ) ^ ((n : ℤ) - 2) * (x i * x j) *
              (if i = j then (2 : ℝ) else 1) :=
          add_sum_erase univ
            (fun j => (2 : ℝ) ^ ((n : ℤ) - 2) * (x i * x j) *
              (if i = j then (2 : ℝ) else 1)) (mem_univ i)
        rw [← he, ite_eq_left rfl]
        have hsumj : (∑ j ∈ univ.erase i,
            (2 : ℝ) ^ ((n : ℤ) - 2) * (x i * x j) * (if i = j then (2 : ℝ) else 1)) =
            (2 : ℝ) ^ ((n : ℤ) - 2) * (x i * (∑ j ∈ univ.erase i, x j)) := by
          have hw : ∀ j ∈ univ.erase i,
              (2 : ℝ) ^ ((n : ℤ) - 2) * (x i * x j) * (if i = j then (2 : ℝ) else 1) =
              (2 : ℝ) ^ ((n : ℤ) - 2) * (x i * x j) := by
            intro j hj
            have hne : i ≠ j := fun hh => (mem_erase.mp hj).1 hh.symm
            rw [ite_eq_right hne]
            ring
          rw [sum_congr rfl hw, ← mul_sum, ← mul_sum]
        rw [hsumj]
        have hsumj2 : ∑ j ∈ univ.erase i, x j = - x i := by
          have h1 := add_sum_erase univ x (mem_univ i)
          rw [hsum] at h1
          linarith [h1]
        rw [hsumj2]
        ring
    _ = (2 : ℝ) ^ ((n : ℤ) - 2) * ∑ i : Fin n, x i ^ 2 := by
        rw [← mul_sum]
    _ = (2 : ℝ) ^ ((n : ℤ) - 2) := by
        rw [hsq, mul_one]

/-- Pairing each subset with its complement: the sum of `S_A ^ 2` over the subsets
with positive sum equals `2 ^ (n - 3)`. -/
lemma sum_pos_subsetSum_sq {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ)
    (hsum : ∑ i, x i = 0) (hsq : ∑ i, x i ^ 2 = 1) :
    ∑ A ∈ univ.powerset.filter (fun A => 0 < ∑ i ∈ A, x i), (∑ i ∈ A, x i) ^ 2 =
      (2 : ℝ) ^ ((n : ℤ) - 3) := by
  have hcompl : ∀ A : Finset (Fin n), ∑ i ∈ Aᶜ, x i = -(∑ i ∈ A, x i) := by
    intro A
    have h := sum_add_sum_compl A x
    rw [hsum] at h
    exact eq_neg_of_add_eq_zero_right h
  set P := univ.powerset.filter (fun A => 0 < ∑ i ∈ A, x i) with hP
  set N := univ.powerset.filter (fun A => ∑ i ∈ A, x i < 0) with hN
  set Z := univ.powerset.filter (fun A => ∑ i ∈ A, x i = 0) with hZ
  have hpart : univ.powerset = P ∪ (N ∪ Z) := by
    rw [hP, hN, hZ]
    ext A
    simp only [mem_powerset, mem_union, mem_filter, subset_univ, true_and]
    constructor
    · intro _
      rcases lt_trichotomy (∑ i ∈ A, x i) 0 with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
      · exact Or.inl h
    · intro _
      trivial
  have hPN : Disjoint P N := by
    rw [disjoint_left]
    intro A hA hA'
    rw [hP, mem_filter] at hA
    rw [hN, mem_filter] at hA'
    exact absurd (lt_trans hA'.2 hA.2) (lt_irrefl _)
  have hPZ : Disjoint P Z := by
    rw [disjoint_left]
    intro A hA hA'
    rw [hP, mem_filter] at hA
    rw [hZ, mem_filter] at hA'
    rw [hA'.2] at hA
    exact absurd hA.2 (lt_irrefl 0)
  have hNZ : Disjoint N Z := by
    rw [disjoint_left]
    intro A hA hA'
    rw [hN, mem_filter] at hA
    rw [hZ, mem_filter] at hA'
    rw [hA'.2] at hA
    exact absurd hA.2 (lt_irrefl 0)
  have hsumZ : ∑ A ∈ Z, (∑ i ∈ A, x i) ^ 2 = 0 := by
    apply sum_eq_zero
    intro A hA
    rw [hZ, mem_filter] at hA
    rw [hA.2]
    ring
  have hNP : ∑ A ∈ N, (∑ i ∈ A, x i) ^ 2 = ∑ A ∈ P, (∑ i ∈ A, x i) ^ 2 := by
    apply sum_nbij' (fun A => Aᶜ) (fun A => Aᶜ)
    · intro A hA
      rw [hN, mem_filter] at hA
      rw [hP, mem_filter]
      refine ⟨mem_powerset.mpr (subset_univ _), ?_⟩
      rw [hcompl A]
      linarith [hA.2]
    · intro A hA
      rw [hP, mem_filter] at hA
      rw [hN, mem_filter]
      refine ⟨mem_powerset.mpr (subset_univ _), ?_⟩
      rw [hcompl A]
      linarith [hA.2]
    · intro A _
      exact compl_compl A
    · intro A _
      exact compl_compl A
    · intro A _
      rw [hcompl A, neg_sq]
  have hmaster := sum_subsetSum_sq hn x hsum hsq
  rw [hpart, sum_union (disjoint_union_right.mpr ⟨hPN, hPZ⟩), sum_union hNZ, hsumZ,
    add_zero, hNP] at hmaster
  have h2 : (2 : ℝ) ^ ((n : ℤ) - 3) = (2 : ℝ) ^ ((n : ℤ) - 2) / 2 := by
    have h := zpow_sub_one₀ (two_ne_zero : (2 : ℝ) ≠ 0) ((n : ℤ) - 2)
    rw [show (n : ℤ) - 2 - 1 = (n : ℤ) - 3 by ring] at h
    rw [h]
    ring
  linarith [hmaster, h2]

/-- Forward direction of the equality case: if equality holds, then every positive
subset sum equals `λ`. -/
lemma subsetSum_eq_of_card_eq {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ)
    (hsum : ∑ i, x i = 0) (hsq : ∑ i, x i ^ 2 = 1)
    (lam : ℝ) (hlam : 0 < lam)
    (heq : ((univ.powerset.filter (fun A => lam ≤ ∑ i ∈ A, x i)).card : ℝ) =
      (2 : ℝ) ^ ((n : ℤ) - 3) / lam ^ 2) :
    ∀ A : Finset (Fin n), 0 < ∑ i ∈ A, x i → ∑ i ∈ A, x i = lam := by
  set T := univ.powerset.filter (fun A => lam ≤ ∑ i ∈ A, x i) with hTdef
  set P := univ.powerset.filter (fun A => 0 < ∑ i ∈ A, x i) with hPdef
  have hsub : T ⊆ P := by
    intro A hA
    rw [hTdef, mem_filter] at hA
    rw [hPdef, mem_filter]
    exact ⟨hA.1, lt_of_lt_of_le hlam hA.2⟩
  have hlam2 : 0 < lam ^ 2 := pow_pos hlam 2
  have hcardmul : (T.card : ℝ) * lam ^ 2 = (2 : ℝ) ^ ((n : ℤ) - 3) := by
    rw [heq, div_mul_cancel₀ _ (ne_of_gt hlam2)]
  have hsumT_lam : ∑ A ∈ T, lam ^ 2 = (2 : ℝ) ^ ((n : ℤ) - 3) := by
    rw [sum_const, nsmul_eq_mul]
    exact hcardmul
  have hsumT : ∑ A ∈ T, (∑ i ∈ A, x i) ^ 2 = (2 : ℝ) ^ ((n : ℤ) - 3) := by
    have h1 : ∑ A ∈ T, lam ^ 2 ≤ ∑ A ∈ T, (∑ i ∈ A, x i) ^ 2 := by
      apply sum_le_sum
      intro A hA
      rw [hTdef, mem_filter] at hA
      exact pow_le_pow_left₀ hlam.le hA.2 2
    have h2 : ∑ A ∈ T, (∑ i ∈ A, x i) ^ 2 ≤ (2 : ℝ) ^ ((n : ℤ) - 3) := by
      calc ∑ A ∈ T, (∑ i ∈ A, x i) ^ 2
          ≤ ∑ A ∈ P, (∑ i ∈ A, x i) ^ 2 :=
            sum_le_sum_of_subset_of_nonneg hsub (fun A _ _ => sq_nonneg _)
        _ = (2 : ℝ) ^ ((n : ℤ) - 3) := by
            rw [hPdef]
            exact sum_pos_subsetSum_sq hn x hsum hsq
    linarith [h1, h2, hsumT_lam]
  have hT_eq : ∀ A ∈ T, (∑ i ∈ A, x i) ^ 2 = lam ^ 2 := by
    have hsumT' : ∑ A ∈ T, ((∑ i ∈ A, x i) ^ 2 - lam ^ 2) = 0 := by
      rw [sum_sub_distrib, hsumT, hsumT_lam, sub_self]
    have hnonneg : ∀ A ∈ T, 0 ≤ (∑ i ∈ A, x i) ^ 2 - lam ^ 2 := by
      intro A hA
      rw [hTdef, mem_filter] at hA
      exact sub_nonneg.mpr (pow_le_pow_left₀ hlam.le hA.2 2)
    rw [sum_eq_zero_iff_of_nonneg hnonneg] at hsumT'
    intro A hA
    exact sub_eq_zero.mp (hsumT' A hA)
  have hPT : ∀ A ∈ P \ T, (∑ i ∈ A, x i) ^ 2 = 0 := by
    have hsumPT : ∑ A ∈ P \ T, (∑ i ∈ A, x i) ^ 2 = 0 := by
      have h := sum_sdiff hsub (f := fun A => (∑ i ∈ A, x i) ^ 2)
      have h5 : ∑ A ∈ P, (∑ i ∈ A, x i) ^ 2 = (2 : ℝ) ^ ((n : ℤ) - 3) := by
        rw [hPdef]
        exact sum_pos_subsetSum_sq hn x hsum hsq
      rw [hsumT, h5] at h
      linarith [h]
    exact (sum_eq_zero_iff_of_nonneg (fun A _ => sq_nonneg _)).mp hsumPT
  intro A hA0
  by_cases hAT : A ∈ T
  · have h1 := hT_eq A hAT
    rw [sq_eq_sq_iff_eq_or_eq_neg] at h1
    rcases h1 with h1 | h1
    · exact h1
    · exfalso
      rw [h1] at hA0
      linarith [hA0, hlam]
  · have hAP : A ∈ P := by
      rw [hPdef, mem_filter]
      exact ⟨mem_powerset.mpr (subset_univ A), hA0⟩
    have h2 := hPT A (mem_sdiff.mpr ⟨hAP, hAT⟩)
    have hS : (∑ i ∈ A, x i) ^ 2 = 0 := h2
    rw [sq_eq_zero_iff] at hS
    exact absurd hS (ne_of_gt hA0)

/-- Forward direction of the equality case: if equality holds, then `x` is a
permutation of `(1 / √2, -1 / √2, 0, ..., 0)` and `λ = 1 / √2`. -/
lemma equality_case_of_card_eq {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ)
    (hsum : ∑ i, x i = 0) (hsq : ∑ i, x i ^ 2 = 1)
    (lam : ℝ) (hlam : 0 < lam)
    (heq : ((univ.powerset.filter (fun A => lam ≤ ∑ i ∈ A, x i)).card : ℝ) =
      (2 : ℝ) ^ ((n : ℤ) - 3) / lam ^ 2) :
    equality_cases x lam := by
  have hkey := subsetSum_eq_of_card_eq hn x hsum hsq lam hlam heq
  have hexists_pos : ∃ i : Fin n, 0 < x i := by
    by_contra h
    push Not at h
    have hall : ∀ i : Fin n, x i = 0 := by
      have hiff := (sum_eq_zero_iff_of_nonpos (s := univ) (f := x)
        (fun i _ => h i)).mp hsum
      exact fun i => hiff i (mem_univ i)
    have h0 : ∑ i : Fin n, x i ^ 2 = 0 := by
      apply sum_eq_zero
      intro i _
      rw [hall i]
      ring
    rw [hsq] at h0
    exact one_ne_zero h0
  obtain ⟨i₀, hi₀⟩ := hexists_pos
  have hi₀lam : x i₀ = lam := by
    have h := hkey {i₀} (by rw [sum_singleton]; exact hi₀)
    rwa [sum_singleton] at h
  have hneg : ∀ j : Fin n, x j < 0 → x j = -lam := by
    intro j hj
    have hsumj : ∑ k ∈ univ.erase j, x k = - x j := by
      have h1 := add_sum_erase univ x (mem_univ j)
      rw [hsum] at h1
      linarith [h1]
    have h := hkey (univ.erase j) (by rw [hsumj]; linarith [hj])
    rw [hsumj] at h
    linarith [h]
  have hclass : ∀ k : Fin n, x k = lam ∨ x k = -lam ∨ x k = 0 := by
    intro k
    rcases lt_trichotomy (x k) 0 with h | h | h
    · exact Or.inr (Or.inl (hneg k h))
    · exact Or.inr (Or.inr h)
    · exact Or.inl (by
        have hh := hkey {k} (by rw [sum_singleton]; exact h)
        rwa [sum_singleton] at hh)
  have huniq_pos : ∀ a b : Fin n, x a = lam → x b = lam → a = b := by
    intro a b ha hb
    by_contra hab
    have hsum2 : ∑ k ∈ ({a, b} : Finset (Fin n)), x k = 2 * lam := by
      rw [sum_pair hab, ha, hb]
      ring
    have h := hkey {a, b} (by rw [hsum2]; linarith [hlam])
    rw [hsum2] at h
    linarith [h, hlam]
  have huniq_neg : ∀ a b : Fin n, x a = -lam → x b = -lam → a = b := by
    intro a b ha hb
    by_contra hab
    have hba : b ∈ univ.erase a := mem_erase.mpr ⟨Ne.symm hab, mem_univ b⟩
    have h1 := add_sum_erase univ x (mem_univ a)
    have h2 := add_sum_erase (univ.erase a) x hba
    rw [hsum] at h1
    have hsum2 : ∑ k ∈ (univ.erase a).erase b, x k = 2 * lam := by
      linarith [h1, h2, ha, hb]
    have h := hkey ((univ.erase a).erase b) (by rw [hsum2]; linarith [hlam])
    rw [hsum2] at h
    linarith [h, hlam]
  have hexists_neg : ∃ j : Fin n, x j = -lam := by
    have hsum_erase : ∑ k ∈ univ.erase i₀, x k = -lam := by
      have h1 := add_sum_erase univ x (mem_univ i₀)
      rw [hsum, hi₀lam] at h1
      linarith [h1]
    by_contra hcon
    push Not at hcon
    have hnonneg : ∀ k ∈ univ.erase i₀, 0 ≤ x k := by
      intro k _
      rcases hclass k with h | h | h
      · rw [h]
        exact hlam.le
      · exact absurd h (hcon k)
      · exact le_of_eq h.symm
    have hle := sum_nonneg hnonneg
    rw [hsum_erase] at hle
    linarith [hle, hlam]
  obtain ⟨j₀, hj₀⟩ := hexists_neg
  have hij₀ : i₀ ≠ j₀ := by
    by_contra! h
    rw [← h] at hj₀
    rw [hi₀lam] at hj₀
    linarith [hj₀, hlam]
  have hrest : ∀ k : Fin n, k ≠ i₀ → k ≠ j₀ → x k = 0 := by
    intro k hki hkj
    rcases hclass k with h | h | h
    · exact absurd (huniq_pos i₀ k hi₀lam h).symm hki
    · exact absurd (huniq_neg j₀ k hj₀ h).symm hkj
    · exact h
  have hlam_val : lam = 1 / Real.sqrt 2 := by
    have hpair : ∑ k ∈ ({i₀, j₀} : Finset (Fin n)), x k ^ 2 = 2 * lam ^ 2 := by
      rw [sum_pair hij₀, hi₀lam, hj₀]
      ring
    have hrest0 : ∑ k ∈ univ \ {i₀, j₀}, x k ^ 2 = 0 := by
      apply sum_eq_zero
      intro k hk
      rw [mem_sdiff] at hk
      have hki : k ≠ i₀ := fun hh => hk.2 (hh.symm ▸ mem_insert_self i₀ ({j₀} : Finset (Fin n)))
      have hkj : k ≠ j₀ := fun hh =>
        hk.2 (hh.symm ▸ mem_insert_of_mem (mem_singleton_self j₀))
      rw [hrest k hki hkj]
      ring
    have hsplit := sum_sdiff (subset_univ ({i₀, j₀} : Finset (Fin n)))
      (f := fun k => x k ^ 2)
    rw [hsq, hpair, hrest0] at hsplit
    have hsqrt : (1 / Real.sqrt 2 : ℝ) ^ 2 = 1 / 2 := by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      ring
    have hlam2 : lam ^ 2 = (1 / Real.sqrt 2 : ℝ) ^ 2 := by
      rw [hsqrt]
      linarith [hsplit]
    rw [sq_eq_sq_iff_eq_or_eq_neg] at hlam2
    rcases hlam2 with h | h
    · exact h
    · exfalso
      have hpos : (0 : ℝ) < 1 / Real.sqrt 2 :=
        one_div_pos.mpr (Real.sqrt_pos.mpr (by norm_num))
      linarith [h, hlam, hpos]
  exact ⟨i₀, j₀, hij₀, by rw [hi₀lam]; exact hlam_val, by rw [hj₀, hlam_val],
    hrest, hlam_val⟩

/-- Backward direction of the equality case: if `x` is a permutation of
`(1 / √2, -1 / √2, 0, ..., 0)` and `λ = 1 / √2`, then equality holds. -/
lemma card_eq_of_equality_case {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ) (lam : ℝ)
    (i j : Fin n) (hij : i ≠ j) (hxi : x i = 1 / Real.sqrt 2)
    (hxj : x j = -(1 / Real.sqrt 2))
    (hrest : ∀ k : Fin n, k ≠ i → k ≠ j → x k = 0) (hlam : lam = 1 / Real.sqrt 2) :
    ((univ.powerset.filter (fun A => lam ≤ ∑ i ∈ A, x i)).card : ℝ) =
      (2 : ℝ) ^ ((n : ℤ) - 3) / lam ^ 2 := by
  set r := (1 : ℝ) / Real.sqrt 2 with hr
  have hr_pos : 0 < r := by
    rw [hr]
    exact one_div_pos.mpr (Real.sqrt_pos.mpr (by norm_num))
  have hr_sq : r ^ 2 = 1 / 2 := by
    rw [hr, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  have hsumA : ∀ A : Finset (Fin n), ∑ k ∈ A, x k =
      (if i ∈ A then r else 0) + (if j ∈ A then -r else 0) := by
    intro A
    have hx : ∀ k : Fin n, x k = (if k = i then r else 0) + (if k = j then -r else 0) := by
      intro k
      by_cases hki : k = i
      · subst hki
        rw [ite_eq_left rfl, ite_eq_right hij, hxi]
        ring
      · by_cases hkj : k = j
        · subst hkj
          rw [ite_eq_right (Ne.symm hij), ite_eq_left rfl, hxj]
          ring
        · rw [hrest k hki hkj, ite_eq_right hki, ite_eq_right hkj]
          ring
    calc ∑ k ∈ A, x k
        = ∑ k ∈ A, ((if k = i then r else 0) + (if k = j then -r else 0)) :=
          sum_congr rfl fun k _ => hx k
      _ = (∑ k ∈ A, if k = i then r else 0) + (∑ k ∈ A, if k = j then -r else 0) :=
          sum_add_distrib
      _ = (if i ∈ A then r else 0) + (if j ∈ A then -r else 0) := by
          rw [sum_ite_eq' A i (fun _ => r), sum_ite_eq' A j (fun _ => -r)]
  have hT : univ.powerset.filter (fun A => lam ≤ ∑ k ∈ A, x k) =
      univ.powerset.filter (fun A => i ∈ A ∧ j ∉ A) := by
    ext A
    simp only [mem_filter, mem_powerset]
    constructor
    · intro h
      refine ⟨h.1, ?_⟩
      have h2 := h.2
      rw [hsumA A, hlam] at h2
      by_cases hiA : i ∈ A <;> by_cases hjA : j ∈ A
      · rw [ite_eq_left hiA, ite_eq_left hjA] at h2
        exfalso
        linarith [h2, hr_pos]
      · exact ⟨hiA, hjA⟩
      · rw [ite_eq_right hiA, ite_eq_left hjA] at h2
        exfalso
        linarith [h2, hr_pos]
      · rw [ite_eq_right hiA, ite_eq_right hjA] at h2
        exfalso
        linarith [h2, hr_pos]
    · intro h
      refine ⟨h.1, ?_⟩
      rw [hsumA A, ite_eq_left h.2.1, ite_eq_right h.2.2, hlam]
      linarith [hr_pos]
  have hcard : (univ.powerset.filter (fun A => i ∈ A ∧ j ∉ A)).card = 2 ^ (n - 2) := by
    have h1 : (univ.powerset.filter (fun A => i ∈ A ∧ j ∉ A)).card =
        ((univ.erase i).erase j).powerset.card := by
      apply card_bij (fun A _ => A.erase i)
      · intro A hA
        rw [mem_filter, mem_powerset] at hA
        rw [mem_powerset, subset_erase]
        exact ⟨erase_subset_erase i hA.1, fun hjmem => hA.2.2 (mem_erase.mp hjmem).2⟩
      · intro A hA B hB hAB
        rw [mem_filter] at hA hB
        have eA := insert_erase hA.2.1
        have eB := insert_erase hB.2.1
        rw [hAB] at eA
        rw [eB] at eA
        exact eA.symm
      · intro B hB
        rw [mem_powerset] at hB
        refine ⟨insert i B, ?_, ?_⟩
        · rw [mem_filter, mem_powerset]
          refine ⟨subset_univ _, mem_insert_self i B, ?_⟩
          rw [mem_insert]
          push Not
          refine ⟨Ne.symm hij, fun hjB => ?_⟩
          have h2 := hB hjB
          exact (mem_erase.mp h2).1 rfl
        · apply erase_insert
          intro hiB
          have h2 := hB hiB
          exact (mem_erase.mp (erase_subset j _ h2)).1 rfl
    have h2 : (n - 1) - 1 = n - 2 := by omega
    rw [h1, card_powerset, card_erase_of_mem (mem_erase.mpr ⟨Ne.symm hij, mem_univ j⟩),
      card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin, h2]
  rw [hT, hcard, two_pow_sub n 2 hn, hlam, hr_sq]
  push_cast
  have h := zpow_add_one₀ (two_ne_zero : (2 : ℝ) ≠ 0) ((n : ℤ) - 3)
  rw [show ((n : ℤ) - 3) + 1 = (n : ℤ) - 2 by ring] at h
  rw [h, eq_div_iff (by norm_num : (1 / 2 : ℝ) ≠ 0)]
  ring

snip end

problem usa2012_p6 {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ)
    (hsum : ∑ i, x i = 0) (hsq : ∑ i, x i ^ 2 = 1)
    (lam : ℝ) (hlam : 0 < lam) :
    ((univ.powerset.filter (fun A => lam ≤ ∑ i ∈ A, x i)).card : ℝ) ≤
      (2 : ℝ) ^ ((n : ℤ) - 3) / lam ^ 2 := by
  set T := univ.powerset.filter (fun A => lam ≤ ∑ i ∈ A, x i) with hTdef
  set P := univ.powerset.filter (fun A => 0 < ∑ i ∈ A, x i) with hPdef
  have hsub : T ⊆ P := by
    intro A hA
    rw [hTdef, mem_filter] at hA
    rw [hPdef, mem_filter]
    exact ⟨hA.1, lt_of_lt_of_le hlam hA.2⟩
  have h1 : (T.card : ℝ) * lam ^ 2 ≤ (2 : ℝ) ^ ((n : ℤ) - 3) := by
    have h2 : (T.card : ℝ) * lam ^ 2 = ∑ A ∈ T, lam ^ 2 := by
      rw [sum_const, nsmul_eq_mul]
    have h3 : ∑ A ∈ T, lam ^ 2 ≤ ∑ A ∈ T, (∑ i ∈ A, x i) ^ 2 := by
      apply sum_le_sum
      intro A hA
      rw [hTdef, mem_filter] at hA
      exact pow_le_pow_left₀ hlam.le hA.2 2
    have h4 : ∑ A ∈ T, (∑ i ∈ A, x i) ^ 2 ≤ ∑ A ∈ P, (∑ i ∈ A, x i) ^ 2 :=
      sum_le_sum_of_subset_of_nonneg hsub (fun A _ _ => sq_nonneg _)
    have h5 : ∑ A ∈ P, (∑ i ∈ A, x i) ^ 2 = (2 : ℝ) ^ ((n : ℤ) - 3) := by
      rw [hPdef]
      exact sum_pos_subsetSum_sq hn x hsum hsq
    linarith [h2, h3, h4, h5]
  rw [le_div_iff₀ (pow_pos hlam 2)]
  exact h1

problem usa2012_p6_equality_cases {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ)
    (hsum : ∑ i, x i = 0) (hsq : ∑ i, x i ^ 2 = 1)
    (lam : ℝ) (hlam : 0 < lam) :
    ((univ.powerset.filter (fun A => lam ≤ ∑ i ∈ A, x i)).card : ℝ) =
        (2 : ℝ) ^ ((n : ℤ) - 3) / lam ^ 2 ↔
      equality_cases x lam := by
  constructor
  · intro heq
    exact equality_case_of_card_eq hn x hsum hsq lam hlam heq
  · rintro ⟨i, j, hij, hxi, hxj, hrest, hlam⟩
    exact card_eq_of_equality_case hn x lam i j hij hxi hxj hrest hlam

end Usa2012P6
