/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Constantin Seebach
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file

/-!
# International Mathematical Olympiad 1973, Problem 6

Let $a_1, a_2,\cdots, a_n$ be $n$ positive numbers,
and let $q$ be a given real number such that $0 < q < 1$. Find $n$ numbers $b_1, b_2, \cdots, b_n$ for which

(a) $a_k < b_k$ for $k=1,2,\cdots, n$,

(b) $q < \dfrac{b_{k+1}}{b_k}<\dfrac{1}{q}$ for $k=1,2,\cdots,n-1$,

(c) $b_1+b_2+\cdots+b_n < \dfrac{1+q}{1-q}(a_1+a_2+\cdots+a_n)$.

-/

namespace Imo1973P6

variable (n : ℕ) (a : Fin n → ℝ) (q : ℝ)

snip begin

open Matrix


def m (_:ℕ) : ℕ → ℕ := fun i => i

theorem m_zero : m n 0 = 0 := by
  rfl

theorem m_nonzero (i) (hi1 : 0 < i) : 0 < m n i := hi1


def Q : Fin n → Fin n → ℝ := fun i j => q ^ m n (Int.natAbs (i.val - j.val))

theorem Q_diag_one : ∀ i, Q n q i i = 1 := by
  unfold Q
  simp [m_zero]

theorem Q_pos (hq : q ∈ Set.Ioo 0 1) : ∀ i j, 0 < Q n q i j := by
  unfold Q
  intro i j
  apply pow_pos
  grind only [= Set.mem_Ioo]

theorem Q_row_neighbour_quot (k) (_ : k+1<n) (j) (hq : q ∈ Set.Ioo 0 1) : ∃ f ∈ ({q, q⁻¹} : Finset _),
    Q n q ⟨k+1, by lia⟩ j = f * Q n q ⟨k, by lia⟩ j := by
  simp only [Finset.mem_insert, Finset.mem_singleton, exists_eq_or_imp, ↓existsAndEq, true_and]
  unfold Q
  repeat rw [<-mul_inv_eq_iff_eq_mul₀ (by grind [pow_ne_zero])]
  rw [<-zpow_natCast, <-zpow_natCast, <-div_eq_mul_inv]
  rw [<-zpow_sub₀ (by grind only [= Set.mem_Ioo])]
  nth_rw 2 [show q = q^(1 : ℤ) by simp]
  rw [show q⁻¹ = q^(-1 : ℤ) by simp]
  repeat rw [zpow_right_inj₀ (by grind) (by grind)]
  unfold Int.natAbs m
  split <;> split
  all_goals grind


theorem imo1973_p6_of_n_eq_one (hn : n = 1) (hq : q ∈ Set.Ioo 0 1) (apos : ∀ i, 0 < a i)
    : ∃ b : Fin n → ℝ,
      (∀ k, a k < b k)
    ∧ (∀ k, ∀ _ : k < n-1, (b ⟨k+1, by lia⟩) / (b ⟨k, by lia⟩) ∈ Set.Ioo q (1 / q))
    ∧ (∑ k, b k < (1+q) / (1-q) * ∑ k, a k) := by
  subst n
  simp only [Fin.forall_fin_one, Fin.isValue, tsub_self, not_lt_zero, one_div, Set.mem_Ioo,
    IsEmpty.forall_iff, implies_true, Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton,
    true_and]
  rw [Set.mem_Ioo] at hq
  have : 1 < (1 + q) / (1 - q) := by
    refine (one_lt_div ?_).mpr ?_ <;> linarith
  use fun _ => √((1+q) / (1-q)) * a 0
  and_intros
  · rw [lt_mul_iff_one_lt_left (apos 0)]
    refine (Real.lt_sqrt ?_).mpr ?_ <;> linarith
  · rw [mul_lt_mul_iff_left₀ (apos 0)]
    refine (Real.sqrt_lt' ?_).mpr ?_ <;> nlinarith


snip end


problem imo1973_p6 (npos : 0 < n) (hq : q ∈ Set.Ioo 0 1) (apos : ∀ i, 0 < a i)
    : ∃ b : Fin n → ℝ,
      (∀ k, a k < b k)
    ∧ (∀ k, ∀ _ : k < n-1, (b ⟨k+1, by lia⟩) / (b ⟨k, by lia⟩) ∈ Set.Ioo q (1 / q))
    ∧ (∑ k, b k < (1+q) / (1-q) * ∑ k, a k) := by
  by_cases hn : n = 1
  · apply imo1973_p6_of_n_eq_one <;> trivial
  use (Q n q *ᵥ a)
  have : 1 < n := Nat.lt_of_le_of_ne npos (Ne.symm hn)
  have nnz : NeZero n := NeZero.of_gt this
  rw [Set.mem_Ioo] at hq
  have q_lt_inv_q : q < 1 / q := by
    rw [lt_div_iff₀, <-sq, sq_lt_one_iff₀] <;> linarith
  and_intros
  -- (a) --
  · intro k
    rw [mulVec, dotProduct]
    calc
      _ < a k + Q n q k (k+1) * a (k + 1) := by
        simp [apos, Q_pos n q hq]
      _ = Q n q k k * a k + Q n q k (k+1) * a (k + 1) := by
        simp [Q_diag_one]
      _ = ∑ i ∈ {k, k+1}, Q n q k i * a i := by
        rw [Finset.sum_insert, Finset.sum_singleton]
        rw [Finset.mem_singleton]
        rw [left_eq_add, Fin.one_eq_zero_iff]
        lia
      _ ≤ _ := by
        refine Finset.sum_le_univ_sum_of_nonneg ?_
        simp [le_of_lt (apos _), Q_pos n q hq]
  -- (b) --
  · intro k klt
    let Xi : Finset _ := {i | Q n q ⟨k+1, by lia⟩ i = q * Q n q ⟨k, by lia⟩ i}
    let Yi : Finset _ := {i | Q n q ⟨k+1, by lia⟩ i = q⁻¹ * Q n q ⟨k, by lia⟩ i}
    have XY_union : Xi ∪ Yi = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro i
      apply (Q_row_neighbour_quot n q k (by lia) i hq).elim
      intro qq ⟨hqq, e⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hqq
      apply hqq.elim
      · intro _
        subst qq
        apply Finset.mem_union_left
        unfold Xi
        exact (Finset.mem_filter_univ i).mpr e
      · intro _
        subst qq
        apply Finset.mem_union_right
        unfold Yi
        exact (Finset.mem_filter_univ i).mpr e
    have XY_disj : Disjoint Xi Yi := by
      unfold Xi Yi
      rw [Finset.disjoint_iff_ne]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq]
      intro a h1 b h2
      by_contra
      subst a
      rw [h2] at h1
      rw [mul_eq_mul_right_iff] at h1
      have h (_t) := Q_pos n q hq ⟨k, _t⟩ b
      rcases h1 with hq_eq | hb0
      · have := q_lt_inv_q; rw [one_div, hq_eq] at this; exact absurd this (lt_irrefl q)
      · linarith [h (show k < n by omega)]
    let X := ∑ i ∈ Xi, Q n q ⟨k, by lia⟩ i * a i
    let Y := ∑ i ∈ Yi, Q n q ⟨k, by lia⟩ i * a i
    have Xpos : 0 < X := by
      unfold X
      apply Finset.sum_pos
      · intro i _
        have h (_t) := Q_pos n q hq ⟨k, _t⟩ i
        exact mul_pos (by apply Q_pos _ q hq) (apos i)
      · use ⟨k, by lia⟩
        unfold Xi Q m
        simp
    have Ypos : 0 < Y := by
      unfold Y
      apply Finset.sum_pos
      · intro i _
        have h (_t) := Q_pos n q hq ⟨k, _t⟩ i
        exact mul_pos (by apply Q_pos _ q hq) (apos i)
      · use ⟨k+1, by lia⟩
        unfold Yi Q m
        simp only [Nat.cast_add, Nat.cast_one, Finset.mem_filter, Finset.mem_univ, sub_self,
          Int.natAbs_zero, pow_zero, sub_add_cancel_left, Int.reduceNeg, IsUnit.neg_iff, isUnit_one,
          Int.natAbs_of_isUnit, pow_one, true_and]
        rw [inv_mul_cancel₀]
        exact ne_of_gt hq.left
    have hk (_t) : (Q n q *ᵥ a) ⟨k, _t⟩ = X + Y := by
      unfold X Y
      rw [mulVec, dotProduct, <-Finset.sum_union XY_disj, <-XY_union]
    have hk1 (_t) : (Q n q *ᵥ a) ⟨k+1, _t⟩ = q*X + q⁻¹*Y := by
      unfold X Y
      rw [mulVec, dotProduct]
      rw [Finset.mul_sum, Finset.mul_sum]
      rw [<-XY_union, Finset.sum_union XY_disj]
      congr 1 <;> { apply Finset.sum_bij (fun x _ => x) <;> [simp; simp; simp; grind] }
    constructor
    · rw [lt_div_iff₀ (by grind only)]
      rw [hk, hk1, mul_add]
      rw [add_lt_add_iff_left]
      field_simp
      exact q_lt_inv_q
    · rw [div_lt_iff₀ (by grind only)]
      rw [hk, hk1, mul_add, one_div]
      rw [add_lt_add_iff_right]
      field_simp
      exact q_lt_inv_q
  -- (c) --
  · simp_rw [mulVec, <-sum_dotProduct]
    rw [dotProduct, Finset.mul_sum]
    simp_rw [Finset.sum_apply]
    have h (i) : (∑ j, Q n q j i) * a i < (1 + q) / (1 - q) * a i := by
      rw [mul_lt_mul_iff_left₀ (apos i)]
      unfold Q m
      calc
        _ = ∑ j ∈ Finset.range n, q ^ (j - i.val : ℤ).natAbs := by
          apply Finset.sum_bij (fun i _ => i.val)
          · simp
          · intro a _ b _ e
            exact Fin.eq_of_val_eq e
          · intro a h
            use ⟨a, by exact Finset.mem_range.mp h⟩
            simp
          · simp
        _ = ∑ j ≤ i.val, q ^ (j - i.val : ℤ).natAbs + ∑ j ∈ Finset.Ioo i.val n, q ^ (j - i.val : ℤ).natAbs := by
          rw [<-Finset.sum_union]
          · congr
            refine Finset.ext_iff.mpr ?_
            simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Iic, Finset.mem_Ioo]
            lia
          · rw [Finset.disjoint_iff_ne]
            simp only [Finset.mem_Iic, Finset.mem_Ioo, ne_eq, and_imp]
            lia
        _ = ∑ j ≤ i.val, q ^ (i.val - j) + ∑ j ∈ Finset.Ioo i.val n, q ^ (j - i.val) := by
          congr 1 <;> {
            apply Finset.sum_congr rfl
            intro x xh
            congr
            unfold Int.natAbs
            split <;> grind only [= Finset.mem_Iic, = Finset.mem_Ioo, = Lean.Grind.toInt_fin]
          }
        _ = ∑ k ≤ i.val, q ^ k + ∑ k ∈ Finset.Ioo 0 (n-i.val), q ^ k := by
          congr 1
          · apply Finset.sum_bij (fun j h => i.val-j)
            · simp
            · grind only [= Finset.mem_Iic, = Lean.Grind.toInt_fin]
            · intro y yh
              use i.val - y
              simp only [Finset.mem_Iic, tsub_le_iff_right, le_add_iff_nonneg_right, zero_le,
                exists_const]
              apply Nat.sub_sub_self
              exact Finset.mem_Iic.mp yh
            · simp
          · apply Finset.sum_bij (fun j h => j-i.val)
            · simp only [Finset.mem_Ioo, and_imp]
              lia
            · grind only [= Finset.mem_Ioo, = Lean.Grind.toInt_fin]
            · intro y yh
              use y + i.val
              simp only [add_tsub_cancel_right, Finset.mem_Ioo,
                lt_add_iff_pos_left, exists_prop, and_true]
              simp only [Finset.mem_Ioo] at yh
              lia
            · simp
        _ = 1 + ∑ k ∈ Finset.Ioc 0 i.val, q ^ k + ∑ k ∈ Finset.Ioo 0 (n-i.val), q ^ k := by
          rw [add_left_inj, Finset.sum_eq_add_sum_diff_singleton (i:=0)]
          · congr
          · simp
        _ ≤ 1 + 2 * ∑ k ∈ Finset.Ioo 0 n, q ^ k := by
          rw [one_add_one_eq_two.symm, add_mul, one_mul, add_assoc, add_le_add_iff_left]
          apply add_le_add <;> {
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · grind only [= Finset.subset_iff, = Finset.mem_Ioo, = Finset.mem_Ioc]
            · intro _ _ _
              apply pow_nonneg (le_of_lt hq.left)
          }
        _ = 1 + 2 * (q * ∑ k < n - 1, q ^ k) := by
          congr 2
          rw [Finset.mul_sum, Eq.comm]
          apply Finset.sum_bij (fun i _ => i+1)
          · simp
            lia
          · simp
          · intro y yh
            use y-1, ?_
            · simp only [Finset.mem_Ioo] at yh; omega
            · simp only [Finset.mem_Ioo] at yh; simp only [Finset.mem_Iio]; omega
          · simp [pow_succ']
        _ < _ := by
          rw [Nat.Iio_eq_range, geom_sum_eq (ne_of_lt hq.right)]
          apply lt_of_mul_lt_mul_of_nonneg_right (a:=1-q) ?_ (by linarith)
          rw [IsUnit.div_mul_cancel, <-mul_assoc, mul_div_assoc', <-neg_div_neg_eq, neg_sub,
            add_mul, <-neg_mul, IsUnit.div_mul_cancel, one_mul]
          · ring_nf
            simp only [add_lt_add_iff_left, sub_lt_self_iff, Nat.ofNat_pos, mul_pos_iff_of_pos_right]
            rw [mul_pow_sub_one nnz.out]
            apply pow_pos hq.left
          · exact Ne.isUnit (sub_ne_zero_of_ne (ne_of_gt hq.right))
          · exact Ne.isUnit (sub_ne_zero_of_ne (ne_of_gt hq.right))
    apply Finset.sum_lt_sum
    · intro i _
      exact le_of_lt (h i)
    · use 0
      simp [h 0]



end Imo1973P6
