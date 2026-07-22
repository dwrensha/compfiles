/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Fable 5, via Claude Code)
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra, .Inequality] }

/-!
# International Mathematical Olympiad 1999, Problem 2

Let n ≥ 2 be a fixed integer. Find the least constant C such that

  ∑_{i < j} xᵢxⱼ(xᵢ² + xⱼ²) ≤ C (∑ i, xᵢ)⁴

for all non-negative real numbers x₁, ..., xₙ.
-/

namespace Imo1999P2

noncomputable determine C : ℝ := 1 / 8

problem imo1999_p2 (n : ℕ) (hn : 2 ≤ n) :
    IsLeast
      {c : ℝ | ∀ x : Fin n → ℝ, (∀ i, 0 ≤ x i) →
        ∑ i, ∑ j ∈ Finset.Ioi i, x i * x j * ((x i) ^ 2 + (x j) ^ 2) ≤
          c * (∑ i, x i) ^ 4}
      C := by
  constructor
  · -- The inequality holds for C = 1/8.
    intro x hx
    have hA0 : (0:ℝ) ≤ ∑ i, (x i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hP0 : (0:ℝ) ≤ ∑ i, ∑ j ∈ Finset.Ioi i, x i * x j :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_nonneg (hx i) (hx j)
    -- The lower triangle sums to the same value as the upper triangle.
    have transpose :
        ∑ i, ∑ j ∈ Finset.Iio i, x i * x j = ∑ i, ∑ j ∈ Finset.Ioi i, x i * x j := by
      rw [Finset.sum_sigma', Finset.sum_sigma']
      refine Finset.sum_nbij' (fun p => ⟨p.2, p.1⟩) (fun p => ⟨p.2, p.1⟩) ?_ ?_ ?_ ?_ ?_
      · rintro ⟨i, j⟩ hp
        simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_Iio, true_and] at hp
        simpa only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_Ioi, true_and] using hp
      · rintro ⟨i, j⟩ hp
        simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_Ioi, true_and] at hp
        simpa only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_Iio, true_and] using hp
      · rintro ⟨i, j⟩ _; rfl
      · rintro ⟨i, j⟩ _; rfl
      · rintro ⟨i, j⟩ _; exact mul_comm _ _
    -- Expansion: (∑ x)² = ∑ x² + 2·∑_{i<j} xᵢxⱼ.
    have key : (∑ i, x i) ^ 2
        = (∑ i, (x i) ^ 2) + 2 * ∑ i, ∑ j ∈ Finset.Ioi i, x i * x j := by
      have expand : (∑ i, x i) ^ 2 = ∑ i, ∑ j, x i * x j := by
        rw [sq, Finset.sum_mul_sum]
      have split : ∀ i : Fin n, (∑ j, x i * x j)
          = x i * x i + ((∑ j ∈ Finset.Iio i, x i * x j)
            + ∑ j ∈ Finset.Ioi i, x i * x j) := by
        intro i
        have hdisj : Disjoint (Finset.Iio i) (Finset.Ioi i) :=
          Finset.disjoint_left.mpr fun j hj hj' =>
            absurd ((Finset.mem_Iio.mp hj).trans (Finset.mem_Ioi.mp hj')) (lt_irrefl j)
        have hnm : i ∉ Finset.Iio i ∪ Finset.Ioi i := by
          simp only [Finset.mem_union, Finset.mem_Iio, Finset.mem_Ioi, lt_self_iff_false,
            or_self, not_false_eq_true]
        have hu : (Finset.univ : Finset (Fin n)) = insert i (Finset.Iio i ∪ Finset.Ioi i) := by
          ext j
          simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_union, Finset.mem_Iio,
            Finset.mem_Ioi, true_iff]
          rcases lt_trichotomy j i with h | h | h
          · exact Or.inr (Or.inl h)
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
        rw [hu, Finset.sum_insert hnm, Finset.sum_union hdisj]
      calc (∑ i, x i) ^ 2 = ∑ i, ∑ j, x i * x j := expand
        _ = ∑ i, (x i * x i + ((∑ j ∈ Finset.Iio i, x i * x j)
              + ∑ j ∈ Finset.Ioi i, x i * x j)) :=
            Finset.sum_congr rfl fun i _ => split i
        _ = (∑ i, x i * x i) + ((∑ i, ∑ j ∈ Finset.Iio i, x i * x j)
              + ∑ i, ∑ j ∈ Finset.Ioi i, x i * x j) := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        _ = (∑ i, (x i) ^ 2) + 2 * ∑ i, ∑ j ∈ Finset.Ioi i, x i * x j := by
            rw [transpose]
            have hsq : ∑ i, x i * x i = ∑ i, (x i) ^ 2 :=
              Finset.sum_congr rfl fun i _ => (pow_two (x i)).symm
            rw [hsq]; ring
    -- Pointwise bound: each term xᵢxⱼ(xᵢ²+xⱼ²) ≤ xᵢxⱼ·(∑ x²).
    have step1 : ∑ i, ∑ j ∈ Finset.Ioi i, x i * x j * ((x i) ^ 2 + (x j) ^ 2)
        ≤ (∑ i, ∑ j ∈ Finset.Ioi i, x i * x j) * ∑ i, (x i) ^ 2 := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun j hj => ?_
      have hij : i ≠ j := ne_of_lt (Finset.mem_Ioi.mp hj)
      have hsub : (x i) ^ 2 + (x j) ^ 2 ≤ ∑ k, (x k) ^ 2 := by
        rw [← Finset.sum_pair (f := fun k => (x k) ^ 2) hij]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun k _ _ => sq_nonneg _
      exact mul_le_mul_of_nonneg_left hsub (mul_nonneg (hx i) (hx j))
    -- Combine: AM-GM on A and 2P.
    show ∑ i, ∑ j ∈ Finset.Ioi i, x i * x j * ((x i) ^ 2 + (x j) ^ 2) ≤
      1 / 8 * (∑ i, x i) ^ 4
    have hS4 : (∑ i, x i) ^ 4
        = ((∑ i, (x i) ^ 2) + 2 * ∑ i, ∑ j ∈ Finset.Ioi i, x i * x j) ^ 2 := by
      rw [show (4:ℕ) = 2 * 2 from rfl, pow_mul, key]
    rw [hS4]
    nlinarith [step1, hA0, hP0,
      sq_nonneg ((∑ i, (x i) ^ 2) - 2 * ∑ i, ∑ j ∈ Finset.Ioi i, x i * x j)]
  · -- Any constant in the set is at least 1/8: test x = (1,1,0,...,0).
    rintro c hc
    show (1:ℝ) / 8 ≤ c
    have h0n : 0 < n := lt_of_lt_of_le (by norm_num) hn
    have h1n : 1 < n := lt_of_lt_of_le (by norm_num) hn
    have hlt : (⟨0, h0n⟩ : Fin n) < ⟨1, h1n⟩ := by
      simp [Fin.lt_def]
    have hne : (⟨0, h0n⟩ : Fin n) ≠ ⟨1, h1n⟩ := ne_of_lt hlt
    set i0 : Fin n := ⟨0, h0n⟩
    set i1 : Fin n := ⟨1, h1n⟩
    classical
    let y : Fin n → ℝ := fun i => if i = i0 then 1 else if i = i1 then 1 else 0
    have hy0 : ∀ i, 0 ≤ y i := by
      intro i
      simp only [y]
      split_ifs <;> norm_num
    have hyi0 : y i0 = 1 := by simp only [y, if_pos rfl]
    have hyi1 : y i1 = 1 := by
      simp [y]
    have hyother : ∀ i, i ≠ i0 → i ≠ i1 → y i = 0 := by
      intro i h1 h2
      simp only [y]
      rw [if_neg h1, if_neg h2]
    have hsum : ∑ i, y i = 2 := by
      have h1 : ∑ i ∈ ({i0, i1} : Finset (Fin n)), y i = 2 := by
        rw [Finset.sum_pair hne, hyi0, hyi1]; norm_num
      rw [← h1]
      symm
      refine Finset.sum_subset (Finset.subset_univ _) ?_
      intro i _ hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      push Not at hi
      exact hyother i hi.1 hi.2
    have hlhs : ∑ i, ∑ j ∈ Finset.Ioi i, y i * y j * ((y i) ^ 2 + (y j) ^ 2) = 2 := by
      rw [Finset.sum_eq_single_of_mem i0 (Finset.mem_univ _)]
      · have h1mem : i1 ∈ Finset.Ioi i0 := Finset.mem_Ioi.mpr hlt
        rw [Finset.sum_eq_single_of_mem i1 h1mem]
        · rw [hyi0, hyi1]; norm_num
        · intro j hj hji1
          have hji0 : j ≠ i0 := ne_of_gt (Finset.mem_Ioi.mp hj)
          rw [hyother j hji0 hji1]
          ring
      · intro i _ hii0
        refine Finset.sum_eq_zero fun j hj => ?_
        rcases eq_or_ne i i1 with rfl | hii1
        · have hj1 : i1 < j := Finset.mem_Ioi.mp hj
          have hji1 : j ≠ i1 := (ne_of_gt hj1)
          have hji0 : j ≠ i0 := by
            intro h
            rw [h] at hj1
            exact absurd (hlt.trans hj1) (lt_irrefl _)
          rw [hyother j hji0 hji1]
          ring
        · rw [hyother i hii0 hii1]
          ring
    have h2 := hc y hy0
    rw [hsum, hlhs] at h2
    norm_num at h2
    linarith

end Imo1999P2
