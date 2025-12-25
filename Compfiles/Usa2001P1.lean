/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Data.Finset.Card
import Mathlib.Order.Bounds.Basic
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 2001, Problem 1

Each of eight boxes contains six balls.
Each ball has been colored with one of n colors, such that no two balls
in the same box are the same color, and no two colors occur together in
more than one box. Determine, with justification, the smallest integer n
for which this is possible.
-/

namespace Usa2001P1

def possible_num_colors : Set ℕ :=
{ n : ℕ | ∃ f : Fin 8 → Finset (Fin n),
    (∀ i, (f i).card = 6) ∧
    (∀ x y : Fin n, ∀ i j : Fin 8,
      i ≠ j → x ∈ f i → y ∈ f i → x ≠ y →
        (¬ (x ∈ f j ∧ y ∈ f j))) }

determine min_colors : ℕ := 23

lemma l {α} (s : Finset α) (sz : s.card = 6) (gen : α -> ℕ) (gt : ∀ i ∈ s, gen i ≥ 1) (sum : (∑ i ∈ s, gen i) ≤ 13) : (36:ℝ)/(13:ℝ) ≤ (∑ i ∈ s, 1 / (gen i:ℝ)) := by
  let f := λ (i : α) ↦ Real.sqrt (gen i : ℝ)
  let g := λ (i : α) ↦ (1 : ℝ) / Real.sqrt (gen i : ℝ)
  have h := Finset.sum_mul_sq_le_sq_mul_sq s f g
  unfold f g at h
  have : (∑ x ∈ s, √(gen x : ℝ) * (1 / √(gen x : ℝ))) = ∑ x ∈ s, 1 := by
    apply Finset.sum_congr rfl; intro x hx; have := gt x hx; field_simp
  rw [this] at h; simp only [Finset.sum_const, sz, nsmul_eq_mul, Nat.cast_ofNat, mul_one, Nat.cast_nonneg, Real.sq_sqrt,
    one_div, inv_pow] at h;
  have : (∑ x ∈ s, (gen x:ℝ)⁻¹) = (∑ x ∈ s, 1 / (gen x : ℝ)) := by
    apply Finset.sum_congr rfl; intro x hx; have := gt x hx; field_simp
  rw [this] at h;
  set aa := (∑ x ∈ s, (gen x : ℝ)) with haa
  set bb := (∑ x ∈ s, (1 / (gen x : ℝ))) with hbb
  rify at sum; rw [←haa] at sum; norm_num at h; 
  have : aa ≥ 0 := by rw [haa]; apply Finset.sum_nonneg; intro i hi; simp only [Nat.cast_nonneg]
  have : bb ≥ 0 := by rw [hbb]; apply Finset.sum_nonneg; intro i hi; simp only [one_div, inv_nonneg, Nat.cast_nonneg]
  field_simp; trans aa*bb;
  · exact h
  · nlinarith

set_option maxHeartbeats 1234567 in
problem usa2001_p1 : IsLeast possible_num_colors min_colors := by
  -- Informal solution from
  -- https://artofproblemsolving.com/wiki/index.php/2001_USAMO_Problems/Problem_1
  constructor
  · sorry
  -- · rw [possible_num_colors]
  --   let f : Fin 8 → Finset (Fin 23)
  --       | 0 => {1, 2, 3, 4, 5, 6}
  --       | 1 => {1, 7, 8, 9, 10, 11}
  --       | 2 => {1, 12, 13, 14, 15, 16}
  --       | 3 => {2, 7, 12, 17, 18, 19}
  --       | 4 => {3, 8, 13, 17, 20, 21}
  --       | 5 => {4, 9, 14, 17, 22, 23}
  --       | 6 => {5, 10, 15, 18, 20, 22}
  --       | 7 => {6, 11, 16, 19, 21, 23}
  --   use f
  --   constructor
  --   · intro i
  --     fin_cases i <;> simp (config := { decide := true }) only [Fin.isValue, Fin.zero_eta, Finset.mem_insert, not_false_eq_true,
  --   Finset.card_insert_of_notMem, Finset.mem_singleton, Finset.card_singleton, Nat.reduceAdd, f]
  --   · intro x y i j hij hx hy hxy
  --     unfold min_colors at x y
  --     fin_cases i <;> fin_cases j <;> dsimp [f] at hx <;> dsimp [f] at hy <;> dsimp at hij <;> dsimp [f]
  --     all_goals clear f ; try contradiction
  --     all_goals fin_cases hx <;> fin_cases hy
  --     all_goals (first | decide | contradiction)


  · rw [min_colors, mem_lowerBounds]
    by_contra! ⟨n, ⟨f, ⟨h1, h2⟩⟩, ha_lt⟩
    suffices (22 : ℝ) < n by norm_cast at this; omega
    clear ha_lt
    let count color i := if color ∈ f i then 1 else 0
    let count_k : Fin n → ℕ := λ color ↦ ∑ i : Fin 8, count color i
    have : (∑ (k : Fin n), ∑ i : Fin 8, ((count k i):ℝ) / ((count_k k):ℝ)) ≤ n := by
      have nsum : n = ∑ (k : Fin n), 1 := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
      conv => rhs; rw [nsum]
      push_cast
      gcongr with i a; unfold count_k; rw [← Finset.sum_div]; norm_cast
      by_cases h : (∑ x, count i x) = 0
      · rw [h]; simp only [CharP.cast_eq_zero, div_zero, zero_le_one]
      · apply le_of_eq; rw [div_self]; norm_cast
    refine lt_of_lt_of_le ?_ this; clear this
    rw [Finset.sum_comm]
    apply lt_of_lt_of_le (by linarith : (22 < ∑ (i : Fin 8), ((36:ℝ) / (13:ℝ))))
    gcongr with i a
    have : ∑ (x : Fin n), ((count x i):ℝ) / ((count_k x):ℝ) = ∑ (k ∈ f i), ((count k i):ℝ) / ((count_k k):ℝ) := by
      symm; apply Finset.sum_subset;
      · simp
      · intros; simp [count, *]
    rw [this]
    have : ∀ k ∈ f i, (count k i) = 1 := by intro k hk; unfold count; simp [hk]
    rw [Finset.sum_congr (g := λ k ↦ 1 / ((count_k k):ℝ)) rfl (λ k hk ↦ by congr; norm_cast; exact this k hk)]


    apply l _ (h1 i)
    · intro ii hii; unfold count_k; unfold count; simp; use i; simp; exact hii

    rw [Finset.sum_comm]
    rw [← Finset.sum_erase_add (h := a)]
    have : (∑ x ∈ f i, count x i) = 6 := by simp [count, *]
    rw [this]
    simp only [Nat.reduceLeDiff, ge_iff_le]
    have : (∑ x ∈ Finset.univ.erase i, 1) = 7 := by simp
    rw [← this]
    gcongr with j a
    rw [Finset.mem_erase] at a;
    by_contra!
    rw [<-Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one, Finset.one_lt_card] at this
    simp only [Finset.mem_filter] at this
    obtain ⟨ex, ⟨⟨p1, p4⟩, ⟨ey, ⟨⟨p2, p5⟩, p3⟩⟩⟩⟩ := this
    refine h2 ex ey i j a.1.symm p1 p2 p3 ⟨p4,p5⟩
end Usa2001P1
