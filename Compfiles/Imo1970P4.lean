/-
Copyright (c) 2024 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw, Adam Kurkiewicz
-/

import Mathlib.Tactic

import ProblemExtraction
import Aesop

--import Mathlib.Algebra.BigOperators.Associated

--open BigOperators

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Olympiad 1970, Problem 4

Determine the set of all positive integers n with the property that
the set {n, n + 1, n + 2, n + 3, n + 4, n + 5} can be partitioned
into two sets such that the product of the numbers in one set
equals the product of the nubmers in the other set.
-/

namespace Imo1970P4

determine SolutionSet : Finset ℕ+ := {}

problem imo1970_p4 (n : ℕ+):
  n ∈ SolutionSet ↔
    ∃ s1 s2 : Finset ℕ,
      s1 ∪ s2 = Finset.Icc n.val (n.val + 5) ∧
      s1 ∩ s2 = ∅ ∧
      ∏ m ∈ s1, m = ∏ m ∈ s2, m :=
  sorry

theorem no_partitions : ¬ ∃ (n : ℕ) (s1 s2 : Finset ℕ),
        s1 ∪ s2 = Finset.Icc n (n + 5) ∧
        s1 ∩ s2 = ∅ ∧
        ∏ m ∈ s1, m = ∏ m ∈ s2, m := by
  apply not_exists_of_forall_not
  intro n
  apply not_exists_of_forall_not
  intro s1
  apply not_exists_of_forall_not
  intro s2
  rintro ⟨H1, H2, H3⟩
  sorry

lemma card_split (s1 s2 s3 : Finset ℕ) (H1 : s1 ∪ s2 = s3) (H2 : s1 ∩ s2 = ∅) (p : ℕ → Prop) [DecidablePred p] :
  (s1.filter p).card + (s2.filter p).card = (s3.filter p).card := by
  rw[← H1]
  rw[Finset.card_filter p s1]
  rw[Finset.card_filter p s2]
  rw[Finset.card_filter p (s1 ∪ s2)]
  have s1_s2_disjoint : Disjoint s1 s2 := by
    dsimp[Disjoint]
    rw[← H2]
    intro sx
    intro r1
    intro r2
    apply Finset.subset_inter
    exact r1
    exact r2
  rw [Finset.sum_union s1_s2_disjoint]

lemma card_opposite (s s' s'' : Finset ℕ) (predicate: ℕ → Prop) [DecidablePred predicate] (filter : s' = (s.filter (λ x => predicate x)))
                    (opposite_filter: s'' = (s.filter (λ x => ¬ predicate x))) : s'.card + s''.card = s.card := by
  rw[filter]
  rw[opposite_filter]
  have := @Finset.filter_card_add_filter_neg_card_eq_card ℕ s predicate
  apply this

lemma elements_close_by (n : ℕ) (s : Finset ℕ) (interval : s = Finset.Icc n (n + 5)) (x : ℕ) (y : ℕ) (x_in_s : x ∈ s) (y_in_s : y ∈ s) (x_le_y : x ≤ y): ∃ k, k ≤ 5 ∧ x + k = y := by
  rw [interval] at x_in_s
  rw [interval] at y_in_s
  simp_all
  obtain ⟨left_x, right_x⟩ := x_in_s
  obtain ⟨left_y, right_y⟩ := y_in_s
  use y - x
  constructor
  · omega
  · omega

lemma elements_close_by_parition (n : ℕ) (s1 s2 : Finset ℕ) (partition : s1 ∪ s2 = Finset.Icc n (n + 5)) (x : ℕ) (y : ℕ) (x_in_s1 : x ∈ s1) (y_in_s2 : y ∈ s2) (x_le_y : x ≤ y): ∃ k, k ≤ 5 ∧ x + k = y := by
  have x_in_interval : x ∈ s1 ∪ s2 := by
    simp
    left
    exact x_in_s1
  have y_in_interval : y ∈ s1 ∪ s2 := by
    simp
    right
    exact y_in_s2
  exact elements_close_by n (s1 ∪ s2) partition x y x_in_interval y_in_interval x_le_y

lemma dvd_prod_of_dvd_elem (p : ℕ) (s : Finset ℕ) (x : ℕ) (H : p ∣ x) : (x ∈ s) → p ∣ (∏ m ∈ s, m) := by
  intro element
  obtain ⟨a, ha⟩ := H
  have dvd_prod_of_mem := Finset.dvd_prod_of_mem (λ n : ℕ => n) element
  obtain ⟨b, hb⟩ := dvd_prod_of_mem
  rw[ha] at hb
  rw[hb]
  use a * b
  ring

lemma prime_dvd_elem_of (p : ℕ) (pp : Nat.Prime p) (s : Finset ℕ) : p ∣ (∏ m ∈ s, m) → ∃ x ∈ s, p ∣ x := by
  exact Prime.exists_mem_finset_dvd pp.prime

lemma no_other_p_divisors_nearby (x : ℕ) (y : ℕ) (p : ℕ) (p_gt_5 : p > 5) (x_lt_y : x < y) (close_by: ∃ k, k ≤ 5 ∧ x + k = y) (x_div_p : p ∣ x) : ¬ (p ∣ y) := by
  obtain ⟨k, ⟨bound, sum⟩⟩ := close_by
  intro H
  obtain ⟨a, Ha⟩ := x_div_p
  obtain ⟨b, Hb⟩ := H
  rw[Ha] at sum
  rw[Hb] at sum
  rw[Ha] at x_lt_y
  rw[Hb] at x_lt_y
  have a_lt_b : a < b := by
    exact (mul_lt_mul_left (show 0 < p by omega)).mp x_lt_y
  have a_lt_b_2 : 1 ≤ (b - a) := by
    omega
  have k_eq : p * (b - a) = k := by
    calc p * (b - a) = p * b - p * a := mul_tsub p b a
    _ = p * a + k - p * a := by rw[sum]
    _ = k := by omega
  have : p * (b - a) > 5 := by
    calc p * (b - a) > 5 * (b - a) := by rel[p_gt_5]
         _ ≥ 5 * 1 := by rel[a_lt_b_2]
  have : k > 5 := by
    omega
  omega

-- The next few functions apply the following logic from the Art of Problem Solving Solution 1

-- There are exactly three odd numbers in s
-- p > 5 is not a divisor of any of those three odd numbers
-- p = 5 is a divisor of at most one of those three odd numbers
-- p = 3 is a divisor of exactly one of those three odd numbers
-- because these numbers are odd, p = 2 is not a divisor of any of those odd numbers
-- p = 2, p = 3, p = 5 and p > 5 are all the prime numbers out there.
-- by pigeonhole principle, one odd number must not have any prime divisors
-- this number must be 1.
-- The only two intervals that contain 1 are {1, 2, 3, 4, 5, 6} and {0, 1, 2, 3, 4, 5}

lemma exactly_three_even_numbers (n : ℕ) (s even_s : Finset ℕ) (interval : s = Finset.Icc n (n + 5))
                                (odd_s_eq: even_s = s.filter (λ x => Even x)): even_s.card = 3 := by
  have explicit_finset : s = {n, n + 1, n + 2, n + 3, n + 4, n + 5} := by
    ext a
    rw[interval]
    simp
    omega
  have explicit_sum : (∑ a ∈ {n, n + 1, n + 2, n + 3, n + 4, n + 5}, if Even a then 1 else 0) =
    (if Even n then 1 else 0) +
    (if Even (n + 1) then 1 else 0) +
    (if Even (n + 2) then 1 else 0) +
    (if Even (n + 3) then 1 else 0) +
    (if Even (n + 4) then 1 else 0) +
    (if Even (n + 5) then 1 else 0)
    := by
    repeat (rw [Finset.sum_insert (by simp)])
    rw [Finset.sum_singleton]
    ring
  cases Nat.even_or_odd n
  case inl h =>
    have first_component : (if Even n then 1 else 0) = 1 := by
      split_ifs
      rfl

    have second_component : (if Even (n + 1) then 1 else 0) = 0 := by
      split_ifs with h_2
      have h_3 := Even.add_one h
      exact (Nat.not_even_iff_odd.mpr h_3) h_2
      rfl

    have third_component : (if Even (n + 2) then 1 else 0) = 1 := by
      split_ifs with h_2
      rfl
      exact h_2 (Even.add h (show Even 2 by decide))

    have fourth_component : (if Even (n + 3) then 1 else 0) = 0 := by
      split_ifs with h_2
      have h_3 := (Even.add_odd h (show Odd 3 by decide))
      exact (Nat.not_even_iff_odd.mpr h_3) h_2
      rfl

    have fifth_component : (if Even (n + 4) then 1 else 0) = 1 := by
      split_ifs with h_2
      rfl
      exact h_2 (Even.add h (show Even 4 by decide))

    have sixth_component : (if Even (n + 5) then 1 else 0) = 0 := by
      split_ifs with h_2
      have h_3 := (Even.add_odd h (show Odd 5 by decide))
      exact (Nat.not_even_iff_odd.mpr h_3) h_2
      rfl

    rw[odd_s_eq]
    rw [s.card_filter (λ x => Even x)]
    rw [explicit_finset]
    rw [explicit_sum]
    rw [first_component]
    rw [second_component]
    rw [third_component]
    rw [fourth_component]
    rw [fifth_component]
    rw [sixth_component]

  case inr h =>
    have first_component : (if Even n then 1 else 0) = 0 := by
      split_ifs with h_2
      exact (Nat.not_even_iff_odd.mpr h) h_2
      rfl

    have second_component : (if Even (n + 1) then 1 else 0) = 1 := by
      split_ifs with h_2
      rfl
      apply h_2
      apply Odd.add_odd
      exact h
      simp

    have third_component : (if Even (n + 2) then 1 else 0) = 0 := by
      split_ifs with h_2
      have := (Odd.add_even h (show Even 2  by decide))
      exact (Nat.not_even_iff_odd.mpr this) h_2
      rfl

    have fourth_component : (if Even (n + 3) then 1 else 0) = 1 := by
      split_ifs with h_2
      rfl
      apply h_2
      apply Odd.add_odd
      exact h
      decide

    have fifth_component : (if Even (n + 4) then 1 else 0) = 0 := by
      split_ifs with h_2
      have := (Odd.add_even h (show Even 4  by decide))
      exact (Nat.not_even_iff_odd.mpr this) h_2
      rfl

    have sixth_component : (if Even (n + 5) then 1 else 0) = 1 := by
      split_ifs with h_2
      rfl
      apply h_2
      apply Odd.add_odd
      exact h
      decide

    rw[odd_s_eq]
    rw [s.card_filter (λ x => Even x)]
    rw [explicit_finset]
    rw [explicit_sum]
    rw [first_component]
    rw [second_component]
    rw [third_component]
    rw [fourth_component]
    rw [fifth_component]
    rw [sixth_component]

lemma exactly_three_odd_numbers (n : ℕ) (s odd_s : Finset ℕ) (interval : s = Finset.Icc n (n + 5))
                                (odd_s_eq: odd_s = s.filter (λ x => Odd x)): (odd_s).card = 3 := by
  let even_s := s.filter (λ x => ¬ Odd x)
  have even_s_eq : even_s = s.filter (λ x => Even x) := by
    dsimp[even_s]
    ext x
    simp
  have card_eq := card_opposite s odd_s even_s (λ x => Odd x) odd_s_eq rfl
  have even_s_card := exactly_three_even_numbers n s even_s interval even_s_eq
  have : s.card = 6 := by
    rw[interval]
    simp
    omega
  omega

lemma elems_in_interval_nearby (x y n : ℕ ) (s : Finset ℕ) (interval : s = Finset.Icc n (n + 5))
  (x_in_s : x ∈ s) (y_in_s : y ∈ s) (x_lt_y : x < y) : ∃ k ≤ 5, x + k = y := by
  simp_all
  use y - x
  constructor
  · omega
  · omega

lemma p_gt_five_not_divides (n : ℕ) (s1 s2 : Finset ℕ) (partition : s1 ∪ s2 = Finset.Icc n (n + 5)) (no_dups: s1 ∩ s2 = ∅)
                            (equal_products : ∏ m ∈ s1, m = ∏ m ∈ s2, m) (x : ℕ) (x_in_interval : x ∈ s1 ∪ s2)
                            (p : ℕ) (pp : Nat.Prime p) (p_gt_5 : p > 5) : ¬ (p ∣ x) := by

  intro p_dvd_x


  have x_in_s1_or_x_in_s2 : x ∈ s1 ∨ x ∈ s2 := Finset.mem_union.mp x_in_interval

  cases x_in_s1_or_x_in_s2
  case inl x_in_s1 =>
    have p_dvd_prod_x : p ∣ ∏ m ∈ s1, m := dvd_prod_of_dvd_elem p s1 x p_dvd_x x_in_s1

    have p_dvd_prod_y : p ∣ ∏ m ∈ s2, m := by
      rw[equal_products] at p_dvd_prod_x
      exact p_dvd_prod_x

    have p_not_dvd_prod_y : ¬ p ∣ ∏ m ∈ s2, m := by
      intro h
      obtain ⟨y, ⟨y_in_s2, p_dvd_y⟩⟩ := prime_dvd_elem_of p pp s2 h

      have s1_s2_disjoint : Disjoint s1 s2 := Finset.disjoint_iff_inter_eq_empty.mpr no_dups

      have x_not_y : x ≠ y := (Finset.disjoint_iff_ne.mp s1_s2_disjoint) x x_in_s1 y y_in_s2

      have x_lt_y_or_y_lt_x := Ne.lt_or_lt x_not_y

      have y_in_interval : y ∈ s1 ∪ s2 := by
        simp
        right
        exact y_in_s2

      cases x_lt_y_or_y_lt_x
      case inl x_lt_y =>
        have := elems_in_interval_nearby x y n (s1 ∪ s2) partition x_in_interval y_in_interval x_lt_y
        have nearby : ∃ k ≤ 5, x + k = y := this
        have p_not_dvd_y := no_other_p_divisors_nearby x y p p_gt_5 x_lt_y nearby p_dvd_x
        apply p_not_dvd_y
        exact p_dvd_y
      case inr y_lt_x =>
        have := elems_in_interval_nearby y x n (s1 ∪ s2) partition y_in_interval x_in_interval y_lt_x
        have nearby : ∃ k ≤ 5, y + k = x := this
        have p_not_dvd_x := no_other_p_divisors_nearby y x p p_gt_5 y_lt_x nearby p_dvd_y
        apply p_not_dvd_x
        exact p_dvd_x

    apply p_not_dvd_prod_y
    exact p_dvd_prod_y

  case inr x_in_s2 =>
    have p_dvd_prod_x : p ∣ ∏ m ∈ s2, m := dvd_prod_of_dvd_elem p s2 x p_dvd_x x_in_s2

    have p_dvd_prod_y : p ∣ ∏ m ∈ s1, m := by
      rw[← equal_products] at p_dvd_prod_x
      exact p_dvd_prod_x

    have p_not_dvd_prod_y : ¬ p ∣ ∏ m ∈ s1, m := by
      intro h
      obtain ⟨y, ⟨y_in_s1, p_dvd_y⟩⟩ := prime_dvd_elem_of p pp s1 h

      have : s2 ∩ s1 = ∅ := by
        rw[← no_dups]
        ext x
        simp
        simp_all only [Finset.mem_Icc, gt_iff_lt]
        apply Iff.intro
        · intro a
          simp_all only [and_self]
        · intro a
          simp_all only [and_self]

      have s2_s1_disjoint : Disjoint s2 s1 := Finset.disjoint_iff_inter_eq_empty.mpr this

      have x_not_y : x ≠ y := (Finset.disjoint_iff_ne.mp s2_s1_disjoint) x x_in_s2 y y_in_s1

      have x_lt_y_or_y_lt_x := Ne.lt_or_lt x_not_y

      have y_in_interval : y ∈ s1 ∪ s2 := by
        simp
        left
        exact y_in_s1

      cases x_lt_y_or_y_lt_x
      case inl x_lt_y =>
        have := elems_in_interval_nearby x y n (s1 ∪ s2) partition x_in_interval y_in_interval x_lt_y
        have nearby : ∃ k ≤ 5, x + k = y := this
        have p_not_dvd_y := no_other_p_divisors_nearby x y p p_gt_5 x_lt_y nearby p_dvd_x
        apply p_not_dvd_y
        exact p_dvd_y
      case inr y_lt_x =>
        have := elems_in_interval_nearby y x n (s1 ∪ s2) partition y_in_interval x_in_interval y_lt_x
        have nearby : ∃ k ≤ 5, y + k = x := this
        have p_not_dvd_x := no_other_p_divisors_nearby y x p p_gt_5 y_lt_x nearby p_dvd_y
        apply p_not_dvd_x
        exact p_dvd_x

    apply p_not_dvd_prod_y
    exact p_dvd_prod_y

lemma five_divides_odd_at_most_once (n : ℕ) (s odd_s : Finset ℕ) (partition : s = Finset.Icc n (n + 5))
                                    (odd_s_eq: odd_s = s.filter (λ x => Odd x)) : (odd_s.filter (λ x => 5 ∣ x)).card ≤ 1 := by
  sorry

lemma three_divides_odd_exactly_once (n : ℕ) (s odd_s : Finset ℕ) (partition : s = Finset.Icc n (n + 5))
                                     (odd_s_eq: odd_s = s.filter (λ x => Odd x)) : (odd_s.filter (λ x => 3 ∣ x)).card = 1 := by
  sorry

lemma no_prime_divisors (x : ℕ) (no_prime : ¬ ∃ (p : ℕ), Nat.Prime p ∧ p ∣ x) : x = 1 := by
  sorry

lemma two_three_five_and_more_is_enough (x : ℕ) (two_does_not_divide : ¬ 2 ∣ x) (three_does_not_divide : ¬ 3 ∣ x) (five_does_not_divide : ¬ 5 ∣ x)
  (p_gt_5_not_dvd : ∀ (p : ℕ), Nat.Prime p → p > 5 → ¬p ∣ x):
  ¬ ∃ (p : ℕ), (Nat.Prime p ∧ p ∣ x) := by
  rintro ⟨p, ⟨pp, div⟩⟩
  -- if p < 5, then p = 2 or p = 3 or p = 5
  --
  sorry

lemma subsets_must_overlap_pigeonhole (s s1 s2 : Finset ℕ) (predicate_s1: ℕ → Prop) (predicate_s2 : ℕ → Prop)
                                      [DecidablePred predicate_s1] [DecidablePred predicate_s2]
                                      (s1_filter : s1 = (s.filter (λ x => predicate_s1 x)))
                                      (s2_filter : s2 = (s.filter (λ x => predicate_s2 x)))
                                      (a b c : ℕ) (total_size_exceeds: a + b > c)
                                      (card_s : s.card = c) (card_s1 : s1.card = a) (card_s2 : s2.card = b):
                                      ∃ x ∈ s, predicate_s1 x ∧ predicate_s2 x := by
  have s1_is_subset: s1 ⊆ s := by
    rw[s1_filter]
    apply Finset.filter_subset
  have s2_is_subset: s2 ⊆ s := by
    rw[s2_filter]
    apply Finset.filter_subset
  have lift_x_in_s1 : ∀ x ∈ s, x ∈ s1 ↔ predicate_s1 x := by
    rw[s1_filter]
    intro x _
    subst card_s
    simp_all only [Finset.mem_filter, true_and]
  have lift_x_in_s2 : ∀ x ∈ s, x ∈ s2 ↔ predicate_s2 x := by
    rw[s2_filter]
    intro x _
    subst card_s
    simp_all only [Finset.mem_filter, true_and]
  apply not_forall_not.mp
  intro h
  simp at h
  have step_1 : (∀ x ∈ s, predicate_s1 x → ¬predicate_s2 x) → (∀ x ∈ s, x ∈ s1 → ¬ x ∈ s2) := by
    intro left
    intro x x_in_s
    intro predicate_s1_fulfills
    intro predicate_s2_fulfills
    have part_1 := ((lift_x_in_s1 x x_in_s).mp predicate_s1_fulfills)
    have part_2 := ((lift_x_in_s2 x x_in_s).mp predicate_s2_fulfills)
    exact left x x_in_s part_1 part_2
  have step_2 : (∀ x ∈ s, x ∈ s1 → x ∉ s2) → Disjoint s1 s2 := by
    intro left
    dsimp[Disjoint]
    dsimp[Finset.instHasSubset]
    simp
    intro s3
    intro rel1
    intro rel2
    intro a
    intro a_in_s3
    have a_in_s1 := rel1 a_in_s3
    have a_in_s2 := rel2 a_in_s3
    have a_in_s : a ∈ s := by
      subst card_s card_s1 s1_filter card_s2 s2_filter
      simp_all only [Finset.filter_subset, Finset.mem_filter, true_and, implies_true, and_self]
    exact left a a_in_s a_in_s1 a_in_s2
  have s1_s2_disjoint : Disjoint s1 s2 := by
    apply step_2
    apply step_1
    exact h
  have card_calc := Finset.card_union_of_disjoint s1_s2_disjoint
  rw[card_s1] at card_calc
  rw[card_s2] at card_calc
  rw[← card_calc] at total_size_exceeds
  rw[← card_s] at total_size_exceeds
  have s1_s2_subset : (s1 ∪ s2) ⊆ s := by
    dsimp[Finset.instHasSubset]
    simp
    intro a
    intro s1_or_s2
    cases s1_or_s2
    case inl left =>
      simp_all only [Finset.filter_subset, Finset.mem_filter]
    case inr left =>
      simp_all only [Finset.filter_subset, Finset.mem_filter]
  have : (s1 ∪ s2).card ≤ s.card := by
    apply Finset.card_le_card
    exact s1_s2_subset
  omega

theorem contains_one (n : ℕ) (s1 s2 odd_s : Finset ℕ) (partition : s1 ∪ s2 = Finset.Icc n (n + 5)) (no_dups: s1 ∩ s2 = ∅)
                      (equal_products : ∏ m ∈ s1, m = ∏ m ∈ s2, m) : ∃ x ∈ (s1 ∪ s2), x = 1 := by
  let odd_s := (s1 ∪ s2).filter (λ x => Odd x)
  let odd_div_by_5 := odd_s.filter (λ x => 5 ∣ x)
  let odd_div_by_3 := odd_s.filter (λ x => 3 ∣ x)

  let odd_non_div_by_5 := odd_s.filter (λ x => ¬ 5 ∣ x)
  let odd_non_div_by_3 := odd_s.filter (λ x => ¬ 3 ∣ x)
  have three_odd_numbers := exactly_three_odd_numbers n (s1 ∪ s2) (odd_s) (partition) rfl

  have odd_div_by_3_card := three_divides_odd_exactly_once n (s1 ∪ s2) (odd_s) partition rfl

  have odd_div_by_5_card := five_divides_odd_at_most_once n (s1 ∪ s2) (odd_s) partition rfl

  have odd_div_by_5_exp_card : odd_div_by_5.card ≤ 1 := by
    simp_all only [odd_s, odd_div_by_5]

  have exactly_2_non_divisers_of_3 : odd_non_div_by_3.card = 2 := by
    have := card_opposite odd_s odd_div_by_3 odd_non_div_by_3 (λ x => 3 ∣ x) rfl rfl
    rw[three_odd_numbers] at this
    rw[odd_div_by_3_card] at this
    omega

  have at_least_2_non_divisers_of_5 : odd_non_div_by_5.card ≥ 2 := by
    have := card_opposite odd_s odd_div_by_5 odd_non_div_by_5 (fun x => 5 ∣ x) rfl rfl
    rw[three_odd_numbers] at this
    omega

  let b := odd_non_div_by_5.card

  have size_calculation : 2 + b > 3 := by
    omega

  have exists_x_non_div_by_3_5 : ∃ x ∈ s1 ∪ s2, ¬ 3 ∣ x ∧ ¬ 5 ∣ x := by
    obtain ⟨x, ⟨x_in_odd_s, non_div_3, non_div_5⟩⟩ := subsets_must_overlap_pigeonhole
      odd_s odd_non_div_by_3 odd_non_div_by_5 (λ x => ¬ 3 ∣ x) (λ x => ¬ 5 ∣ x)
      rfl rfl 2 b 3 size_calculation
      three_odd_numbers exactly_2_non_divisers_of_3 rfl
    use x
    constructor
    · simp_all only [Finset.mem_filter, odd_s]
    · constructor
      · exact non_div_3
      · exact non_div_5

  have exists_x_no_prime_divisors : ∃ x ∈ (s1 ∪ s2), ¬ ∃ (p : ℕ), Nat.Prime p ∧ p ∣ x := by
    obtain ⟨x, x_in_s1_s2, non_div_3, non_div_5⟩ := exists_x_non_div_by_3_5
    use x
    constructor
    · exact x_in_s1_s2
    · intro h
      obtain ⟨p, ⟨pp, p_div⟩⟩ := h
      have p_gt_5_not_dvd := p_gt_five_not_divides n s1 s2 partition no_dups equal_products x x_in_s1_s2
      have to_apply := two_three_five_and_more_is_enough x sorry non_div_3 non_div_5 p_gt_5_not_dvd
      apply to_apply
      use p

  obtain ⟨x, ⟨x_in_s1_u_s2, no_prime⟩⟩ := exists_x_no_prime_divisors
  use x
  constructor
  · exact x_in_s1_u_s2
  · exact no_prime_divisors x no_prime

end Imo1970P4
