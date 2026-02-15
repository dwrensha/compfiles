/-
Copyright (c) 2025 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
import Mathlib.Tactic
import Mathlib.Algebra.Order.Group.Int.Sum

import ProblemExtraction

problem_file {
  tags := [.Algebra]
  solutionImportedFrom :=
    "https://github.com/leanprover-community/mathlib4/blob/master/Archive/Imo/Imo2015Q6.lean",
}

/-!
# International Mathematical Olympiad 2015, Problem 6
The sequence $a_1, a_2, \dots$ of integers satisfies the conditions
1. $1 ≤ a_j ≤ 2015$ for all $j ≥ 1$,
2. $k + a_k ≠ l + a_l$ for all $1 ≤ k < l$.
Prove that there exist two positive integers $b$ and $N$ for which
$$\left|\sum_{j=m+1}^n (a_j-b)\right| ≤ 1007^2$$
for all integers $m,n$ such that $N ≤ m < n$.
-/

/-- The conditions on `a` in the problem. We reindex `a` to start from 0 rather than 1;
`N` then only has to be nonnegative rather than positive, and the sum in the problem statement
is over `Ico m n` rather than `Ioc m n`. -/
def Condition (a : ℕ → ℤ) : Prop :=
  (∀ i, a i ∈ Finset.Icc 1 2015) ∧ Function.Injective fun i ↦ i + a i

snip begin
/-
# Solution
We follow solution 2 ("juggling") from https://web.evanchen.cc/exams/IMO-2015-notes.pdf.
Consider a collection of balls at different integer heights that starts out empty at time 0
and is modified at each succeeding integer time `t` as follows:
* If there is a ball at height 0 it is removed (caught)
* Then a ball is added at height $a_t$
* Then all balls have their height decreased by 1
Condition 1 ensures that all heights stay in [0, 2014]. Condition 2 ensures that the heights at any
point in time are distinct, so we can model the collection as a finset of heights of monotonically
increasing, bounded cardinality. So there is a time where the cardinality reaches a maximum;
we take `N` to be that time and `b` to be that maximum cardinality. $1 ≤ b ≤ 2015$.
Let $S_t$ be the sum of heights at time $t$. The key observation is that for all $t ≥ N$
$$S_{t+1} = S_t + a_{t+1} - b$$
because 0 must be in the set of heights at time $t$ (otherwise the cardinality will increase);
this height is replaced by $a_{t+1}$ and then all $b$ balls have their height decreased by 1. Thus
$$\left|\sum_{j=m+1}^n (a_j-b)\right| = |S_n - S_m|.$$
Now for all $t ≥ N$,
$$\sum_{i=0}^{b-1} i ≤ S_t ≤ 0 + \sum_{i=0}^{b-2} (2014-i),$$
so the absolute difference is upper-bounded by
$$\sum_{i=0}^{b-2} (2014-i) - (b-1) - \sum_{i=0}^{b-2} (b-2-i) = (b-1)(2015-b) ≤ 1007^2.$$
-/

/-- The collection of ball heights in the solution. -/
def pool (a : ℕ → ℤ) : ℕ → Finset ℤ
  | 0 => ∅
  | t + 1 => (insert (a t) ((pool a t).erase 0)).map (Equiv.subRight (1 : ℤ))

variable {a : ℕ → ℤ} (ha : Condition a) {t : ℕ}

section Pool

lemma exists_add_eq_of_mem_pool {z : ℤ} (hz : z ∈ pool a t) : ∃ u < t, u + a u = t + z := by
  induction t generalizing z with
  | zero => simp only [pool, Finset.notMem_empty] at hz
  | succ t ih =>
    simp_rw [pool, Finset.mem_map, Equiv.coe_toEmbedding, Equiv.subRight_apply] at hz
    obtain ⟨y, my, ey⟩ := hz
    rw [Finset.mem_insert, Finset.mem_erase] at my; rcases my with h | h
    · use t; lia
    · obtain ⟨u, lu, hu⟩ := ih h.2
      use u; lia

include ha

/-- The ball heights are always within `[0, 2014]`. -/
lemma pool_subset_Icc : pool a t ⊆ Finset.Icc 0 2014 := by
  induction t with
  | zero => simp only [pool, Finset.empty_subset]
  | succ t ih =>
    intro x hx
    simp_rw [pool, Finset.mem_map, Equiv.coe_toEmbedding, Equiv.subRight_apply] at hx
    obtain ⟨y, my, ey⟩ := hx
    suffices y ∈ Finset.Icc 1 2015 by rw [Finset.mem_Icc] at this ⊢; lia
    rw [Finset.mem_insert, Finset.mem_erase] at my; rcases my with h | ⟨h₁, h₂⟩
    · exact h ▸ ha.1 t
    · replace h₂ := ih h₂
      rw [Finset.mem_Icc] at h₂ ⊢; lia

lemma not_mem_pool_self : a t ∉ pool a t := by
  by_contra h
  obtain ⟨u, lu, hu⟩ := exists_add_eq_of_mem_pool h
  exact lu.ne (ha.2 hu)

/-- The number of balls stays unchanged if there is a ball with height 0 and increases by 1
otherwise. -/
lemma card_pool : Finset.card (pool a (t + 1)) = Finset.card (pool a t) + if 0 ∈ pool a t then 0 else 1 := by
  have nms : a t ∉ (pool a t).erase 0 := by
    rw [Finset.mem_erase, not_and_or]; exact .inr (not_mem_pool_self ha)
  rw [pool, Finset.card_map, Finset.card_insert_of_notMem nms, Finset.card_erase_eq_ite]
  split_ifs with h
  · have := Finset.card_pos.mpr ⟨0, h⟩; lia
  · rfl

lemma monotone_card_pool : Monotone fun t ↦ Finset.card (pool a t) := by
  refine monotone_nat_of_le_succ fun t ↦ ?_
  have := card_pool (t := t) ha; lia

/-- There exists a point where the number of balls reaches a maximum (which follows from its
monotonicity and boundedness). We take its coordinates for the problem's `b` and `N`. -/
lemma exists_max_card_pool : ∃ b N, ∀ t ≥ N, Finset.card (pool a t) = b :=
  converges_of_monotone_of_bounded (monotone_card_pool ha)
    (fun t ↦ by simpa using Finset.card_le_card (pool_subset_Icc ha))

end Pool

section Sums

variable {b N : ℕ} (hbN : ∀ t ≥ N, Finset.card (pool a t) = b) (ht : t ≥ N)

include ha hbN

lemma b_pos : 0 < b := by
  by_contra! h; rw [nonpos_iff_eq_zero] at h; subst h
  replace hbN : ∀ t, Finset.card (pool a t) = 0 := fun t ↦ by
    obtain h | h := le_or_gt t N
    · have : Finset.card (pool a t) ≤ Finset.card (pool a N) := monotone_card_pool ha h
      rwa [hbN _ le_rfl, nonpos_iff_eq_zero] at this
    · exact hbN _ h.le
  have cp1 : Finset.card (pool a 1) = 1 := by
    simp_rw [card_pool ha, pool, Finset.card_empty, Finset.notMem_empty, ite_false]
  apply absurd (hbN 1); lia

include ht in
lemma zero_mem_pool : 0 ∈ pool a t := by
  have := card_pool (t := t) ha
  have := hbN (t + 1) (by lia)
  simp_all

include ht in
/-- The key observation, one term of the telescoping sum for the problem's expression. -/
lemma sum_sub_sum_eq_sub : ∑ x ∈ pool a (t + 1), x - ∑ x ∈ pool a t, x = a t - b := by
  simp_rw [pool, Finset.sum_map, Equiv.coe_toEmbedding, Equiv.subRight_apply]
  have nms : a t ∉ (pool a t).erase 0 := by
    rw [Finset.mem_erase, not_and_or]; exact .inr (not_mem_pool_self ha)
  rw [Finset.sum_insert nms, Finset.sum_erase_eq_sub (h := zero_mem_pool ha hbN ht), Finset.sum_sub_distrib, Finset.sum_const,
    nsmul_one, hbN _ ht]
  lia

/-- The telescoping sum giving the part of the problem's expression within the modulus signs. -/
lemma sum_telescope {m n : ℕ} (hm : N ≤ m) (hn : m < n) :
    ∑ j ∈ Finset.Ico m n, (a j - b) = ∑ x ∈ pool a n, x - ∑ x ∈ pool a m, x := by
  induction n, hn using Nat.le_induction with
  | base => rw [sum_sub_sum_eq_sub ha hbN hm]; simp
  | succ k lk ih =>
    rw [Finset.sum_Ico_succ_top (by lia), ih, ← sum_sub_sum_eq_sub ha hbN (by lia)]
    apply sub_add_sub_cancel'

include ht in
lemma le_sum_pool : ∑ i ∈ Finset.range b, (i : ℤ) ≤ ∑ x ∈ pool a t, x := by
  convert Finset.sum_range_le_sum fun x mx ↦ (Finset.mem_Icc.mp ((pool_subset_Icc ha) mx)).1
  · rw [hbN _ ht]
  · rw [zero_add]

include ht in
lemma sum_pool_le : ∑ x ∈ pool a t, x ≤ ∑ i ∈ Finset.range (b - 1), (2014 - i : ℤ) := by
  have zmp := zero_mem_pool ha hbN ht
  rw [← Finset.insert_erase zmp, Finset.sum_insert (Finset.notMem_erase _ _), zero_add]
  convert Finset.sum_le_sum_range fun x mx ↦ ?_
  · rw [Finset.card_erase_of_mem zmp, hbN _ ht]
  · exact (Finset.mem_Icc.mp ((pool_subset_Icc ha) (Finset.mem_erase.mp mx).2)).2

end Sums

snip end

namespace Imo2015P6

problem imo2015_p6 (ha : Condition a) :
    ∃ b > 0, ∃ N, ∀ m ≥ N, ∀ n > m, |∑ j ∈ Finset.Ico m n, (a j - b)| ≤ 1007 ^ 2 := by
  obtain ⟨b, N, hbN⟩ := exists_max_card_pool ha
  have bp := b_pos ha hbN
  use b, Int.natCast_pos.mpr bp, N; intro m hm n hn; rw [sum_telescope ha hbN hm hn]
  calc
    _ ≤ ∑ i ∈ Finset.range (b - 1), (2014 - i : ℤ) - ∑ i ∈ Finset.range b, (i : ℤ) :=
      abs_sub_le_of_le_of_le (le_sum_pool ha hbN (hm.trans hn.le))
        (sum_pool_le ha hbN (hm.trans hn.le)) (le_sum_pool ha hbN hm) (sum_pool_le ha hbN hm)
    _ = (b - 1) * (2015 - b) := by
      nth_rw 2 [← Nat.sub_one_add_one_eq_of_pos bp]
      rw [← Finset.sum_flip, Finset.sum_range_succ, tsub_self, Nat.cast_zero, add_zero, ← Finset.sum_sub_distrib]
      have sc : ∀ x ∈ Finset.range (b - 1), (2014 - x - (b - 1 - x : ℕ)) = (2015 - b : ℤ) := fun x mx ↦ by
        rw [Finset.mem_range] at mx; lia
      rw [Finset.sum_congr rfl sc, Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_pred bp]
    _ ≤ _ := by
      rw [← mul_le_mul_iff_right₀ zero_lt_four, ← mul_assoc,
        show 4 * 1007 ^ 2 = ((b - 1 : ℤ) + (2015 - b)) ^ 2 by simp]
      exact four_mul_le_sq_add ..

end Imo2015P6
