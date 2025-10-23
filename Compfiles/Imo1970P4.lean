/-
Copyright (c) 2024 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw, Adam Kurkiewicz
-/

import Mathlib.Tactic
import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Olympiad 1970, Problem 4

Determine the set of all positive integers n with the property that
the set {n, n + 1, n + 2, n + 3, n + 4, n + 5} can be partitioned
into two sets such that the product of the numbers in one set
equals the product of the numbers in the other set.
-/

namespace Imo1970P4

snip begin

lemma card_opposite (s s' s'' : Finset ℕ) (predicate: ℕ → Prop)
    [DecidablePred predicate] (filter : s' = (s.filter (λ x => predicate x)))
    (opposite_filter: s'' = (s.filter (λ x => ¬ predicate x))) :
    s'.card + s''.card = s.card := by
  rw [filter]
  rw [opposite_filter]
  exact Finset.filter_card_add_filter_neg_card_eq_card predicate

lemma no_other_p_divisors_nearby (x : ℕ) (y : ℕ) (p : ℕ) (p_gt_5 : p > 5) (x_lt_y : x < y)
    (close_by: ∃ k, k ≤ 5 ∧ x + k = y) (x_div_p : p ∣ x) : ¬ p ∣ y := by
  obtain ⟨k, hk_le, rfl⟩ := close_by
  have h_not_div_k : ¬ p ∣ k :=
    Nat.not_dvd_of_pos_of_lt (Nat.lt_add_right_iff_pos.mp x_lt_y) (Nat.lt_of_le_of_lt hk_le p_gt_5)
  simp_all [Nat.dvd_add_right]

lemma no_other_5_divisors_nearby (x : ℕ) (y : ℕ) (x_lt_y : x < y) (close_by: ∃ k, k ≤ 4 ∧ x + k = y) (x_div_p : 5 ∣ x) : ¬ (5 ∣ y) := by
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

lemma elems_in_interval_nearby (x y n : ℕ ) (s : Finset ℕ) (interval : s = Finset.Icc n (n + 5))
  (x_in_s : x ∈ s) (y_in_s : y ∈ s) (x_lt_y : x < y) : ∃ k ≤ 5, x + k = y := by
  simp_all only [Finset.mem_Icc]
  use y - x
  omega

lemma p_gt_five_not_divides (n : ℕ) (s1 s2 : Finset ℕ) (partition : s1 ∪ s2 = Finset.Icc n (n + 5)) (no_dups: s1 ∩ s2 = ∅)
                            (equal_products : ∏ m ∈ s1, m = ∏ m ∈ s2, m) (x : ℕ) (x_in_interval : x ∈ s1 ∪ s2)
                            (p : ℕ) (pp : Nat.Prime p) (p_gt_5 : p > 5) : ¬ (p ∣ x) := by

  intro p_dvd_x

  have x_in_s1_or_x_in_s2 : x ∈ s1 ∨ x ∈ s2 := Finset.mem_union.mp x_in_interval

  cases x_in_s1_or_x_in_s2
  case inl x_in_s1 =>
    have p_dvd_prod_x : p ∣ ∏ m ∈ s1, m := by
      have := Finset.dvd_prod_of_mem (λ n : ℕ => n) x_in_s1
      exact Dvd.dvd.trans p_dvd_x this

    have p_dvd_prod_y : p ∣ ∏ m ∈ s2, m := by
      rw[equal_products] at p_dvd_prod_x
      exact p_dvd_prod_x

    have p_not_dvd_prod_y : ¬ p ∣ ∏ m ∈ s2, m := by
      intro h
      obtain ⟨y, ⟨y_in_s2, p_dvd_y⟩⟩ := Prime.exists_mem_finset_dvd pp.prime h

      have s1_s2_disjoint : Disjoint s1 s2 := Finset.disjoint_iff_inter_eq_empty.mpr no_dups

      have x_not_y : x ≠ y := (Finset.disjoint_iff_ne.mp s1_s2_disjoint) x x_in_s1 y y_in_s2

      have x_lt_y_or_y_lt_x := Ne.lt_or_gt x_not_y

      have y_in_interval : y ∈ s1 ∪ s2 := Finset.mem_union_right s1 y_in_s2

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
    have := Finset.dvd_prod_of_mem (λ n : ℕ => n) x_in_s2
    simp only at this
    have p_dvd_prod_x : p ∣ ∏ m ∈ s2, m := (Dvd.dvd.trans p_dvd_x this)

    have p_dvd_prod_y : p ∣ ∏ m ∈ s1, m := by
      rw[← equal_products] at p_dvd_prod_x
      exact p_dvd_prod_x

    have p_not_dvd_prod_y : ¬ p ∣ ∏ m ∈ s1, m := by
      intro h
      obtain ⟨y, ⟨y_in_s1, p_dvd_y⟩⟩ := Prime.exists_mem_finset_dvd pp.prime h

      have : s2 ∩ s1 = ∅ := by
        rw [← no_dups]
        exact Finset.inter_comm s2 s1

      have s2_s1_disjoint : Disjoint s2 s1 := Finset.disjoint_iff_inter_eq_empty.mpr this

      have x_not_y : x ≠ y := (Finset.disjoint_iff_ne.mp s2_s1_disjoint) x x_in_s2 y y_in_s1

      have x_lt_y_or_y_lt_x := Ne.lt_or_gt x_not_y

      have y_in_interval : y ∈ s1 ∪ s2 := Finset.mem_union_left s2 y_in_s1

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

lemma odd_props (n : ℕ) (odd_s : Finset ℕ)
    (s_odd_eq : odd_s = (Finset.Icc n (n + 5)).filter (λ x => Odd x)) :
    ∃ (a b c : ℕ), {a, b, c} = odd_s ∧ b = a + 2 ∧ c = b + 2 := by
  by_cases h : Odd n
  · have h2 := Odd.not_two_dvd_nat h
    use n, n + 2, n + 4
    simp_all only [Nat.two_dvd_ne_zero, and_self, and_true]
    ext x
    simp_all only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_filter, Finset.mem_Icc]
    apply Iff.intro <;> grind
  · use n + 1, n + 3, n + 5
    simp_all only [Nat.not_odd_iff_even, and_self, and_true]
    have := Even.two_dvd h
    ext x
    simp_all only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_filter, Finset.mem_Icc]
    grind

lemma exactly_three_odd_numbers (n : ℕ) (odd_s : Finset ℕ)
                                (odd_s_eq: odd_s = (Finset.Icc n (n + 5)).filter (λ x => Odd x)): (odd_s).card = 3 := by
  -- ∃ (a b c : ℕ), {a, b, c} = odd_s ∧ odd_s.card = 3
  obtain ⟨x, y, z, ⟨left, ⟨y_eq, z_eq⟩⟩⟩ := odd_props n odd_s odd_s_eq
  grind

lemma at_most_one (n : ℕ) (x y : ℕ)
  (x_in_interval : x ∈ Finset.Icc n (n + 5)) (y_in_interval : y ∈ Finset.Icc n (n + 5))
  (x_div_5 : 5 ∣ x )
  (x_non_div_2 : ¬ 2 ∣ x)
  (y_div_5 : 5 ∣ y )
  (y_non_div_2 : ¬ 2 ∣ y) :
  x = y := by
  simp_all only [Finset.mem_Icc, Nat.two_dvd_ne_zero]
  omega

lemma card_of_equal (s : Finset ℕ) : (∀ x ∈ s, ∀ y ∈ s,  x = y) → s.card ≤ 1 := by
  exact (@Finset.card_le_one ℕ s).mpr

lemma five_divides_odd_at_most_once (n : ℕ) (s odd_s : Finset ℕ) (partition : s = Finset.Icc n (n + 5))
                                    (odd_s_eq: odd_s = s.filter (λ x => Odd x)) : (odd_s.filter (λ x => 5 ∣ x)).card ≤ 1 := by
  have : (∀ x ∈ (odd_s.filter (λ x => 5 ∣ x)), ∀ y ∈ (odd_s.filter (λ y => 5 ∣ y)), x = y) → (odd_s.filter (λ x => 5 ∣ x)).card ≤ 1 := by
    exact (card_of_equal) (odd_s.filter (λ x => 5 ∣ x))

  apply this

  rw [odd_s_eq]

  intro x x_in y y_in

  simp only [Finset.mem_filter] at x_in
  obtain ⟨⟨X1, X2⟩, X3⟩ := x_in

  simp only [Finset.mem_filter] at y_in
  obtain ⟨⟨Y1, Y2⟩, Y3⟩ := y_in

  apply at_most_one n
  · rw[partition] at X1
    exact X1
  · rw[partition] at Y1
    exact Y1
  · exact X3
  · exact Odd.not_two_dvd_nat X2
  · exact Y3
  · exact Odd.not_two_dvd_nat Y2

lemma unique_divisor (n : ZMod 3) (a b c : ℕ) (n_eq_a : n = a) (s : Finset ℕ) (s_eq : s = ({a, b, c} : Finset ℕ)) (b_eq: b = a + 2) (c_eq : c = b + 2) : ∃! a', a' ∈ s ∧ 3 ∣ a' := by
  fin_cases n
  · use a
    have three_div_a : 3 ∣ a := by
      apply (ZMod.natCast_eq_zero_iff a 3).mp
      simp_all only [Fin.zero_eta]
    grind
  · use b
    have three_div_b : 3 ∣ b := by
      simp_all only [Fin.mk_one]
      apply (ZMod.natCast_eq_zero_iff (a + 2) 3).mp
      simp_all only [Nat.cast_add, Nat.cast_ofNat]
      rw[← n_eq_a]
      reduce_mod_char
    constructor
    · simp_all only [Fin.mk_one, Finset.mem_insert, add_eq_left, OfNat.ofNat_ne_zero, Finset.mem_singleton, left_eq_add, or_false, or_true, and_self]
    · rintro o ⟨o_in_s, three_div_o⟩
      rw[s_eq] at o_in_s
      simp_all only [Fin.mk_one, Finset.mem_insert, Finset.mem_singleton]
      omega
  · use c
    have three_div_c : 3 ∣ c := by
      simp_all only [Nat.dvd_add_self_right]
      apply (ZMod.natCast_eq_zero_iff (a + 1) 3).mp
      simp_all only [Nat.cast_add, Nat.cast_one]
      rw[← n_eq_a]
      simp only [Nat.reduceAdd, Fin.reduceFinMk, Fin.isValue]
      reduce_mod_char
    constructor
    · simp_all only [Nat.dvd_add_self_right, Finset.mem_insert, add_eq_left, OfNat.ofNat_ne_zero, Finset.mem_singleton, or_true, and_self]
    · rintro o ⟨o_in_s, three_div_o⟩
      rw[s_eq] at o_in_s
      simp_all only [Nat.dvd_add_self_right, Finset.mem_insert, Finset.mem_singleton]
      omega

lemma card_1_of_exists_unique (s : Finset ℕ)
  (predicate: ℕ → Prop)
  [DecidablePred predicate]
  (exists_unique : ∃! n ∈ s, predicate n) :
  (Finset.filter (fun x ↦ predicate x) s).card = 1 := by
  have := (@Finset.card_eq_one ℕ (Finset.filter (fun x ↦ predicate x) s)).mpr
  apply this
  obtain ⟨a', H⟩ := exists_unique
  use a'
  grind

lemma three_divides_odd_exactly_once (n : ℕ) (s odd_s : Finset ℕ) (partition : s = Finset.Icc n (n + 5))
                                     (odd_s_eq: odd_s = s.filter (λ x => Odd x)) : (odd_s.filter (λ x => 3 ∣ x)).card = 1 := by
  rw[partition] at odd_s_eq
  obtain ⟨a, b, c, ⟨explicit_finset, b_comp, c_comp⟩⟩ := odd_props n odd_s odd_s_eq
  rw[← partition] at odd_s_eq
  rw[← explicit_finset]
  have : (∃! a' ∈ ({a, b, c} : Finset ℕ), 3 ∣ a') → (Finset.filter (fun x ↦ 3 ∣ x) {a, b, c}).card = 1 := by
    apply card_1_of_exists_unique
  apply this
  exact unique_divisor (↑a) a b c rfl {a, b, c} rfl b_comp c_comp

lemma empty_of_empty_subset (s : Finset ℕ) : s = {x_1 | x_1 ∈ (∅ : Finset ℕ) } → s = ∅ := by
  simp only [Finset.notMem_empty, Set.setOf_false, Finset.coe_eq_empty, imp_self]

lemma enumerate_primes_le_5 (p : ℕ) (pp : p.Prime) (p_le_5 : p ≤ 5) : p ∈ ({2, 3, 5} : Finset ℕ) := by
  by_contra H
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at H
  obtain ⟨a, b, c⟩ := H
  have := Nat.Prime.five_le_of_ne_two_of_ne_three pp
  omega

lemma two_three_five_and_more_is_enough (x : ℕ) (two_does_not_divide : ¬ 2 ∣ x) (three_does_not_divide : ¬ 3 ∣ x) (five_does_not_divide : ¬ 5 ∣ x)
  (p_gt_5_not_dvd : ∀ (p : ℕ), p.Prime → p > 5 → ¬p ∣ x):
  ¬ ∃ (p : ℕ), (p.Prime ∧ p ∣ x) := by
  have p_le_5_not_dvd : ∀ (p : ℕ), p.Prime → p ≤ 5 → ¬ p ∣ x := by
    intro p pp p_le_5 p_div_x
    have p_subset : p ∈ ({2, 3, 5} : Finset ℕ) := enumerate_primes_le_5 p pp p_le_5
    have : p = 2 ∨ p = 3 ∨ p = 5 := by
      simp_all only [Nat.two_dvd_ne_zero, gt_iff_lt, Finset.mem_insert, Finset.mem_singleton]

    cases this
    case inl h =>
      simp_all only [Nat.two_dvd_ne_zero, gt_iff_lt, Finset.mem_insert, Finset.mem_singleton, true_or]
      omega
    case inr h => grind
  grind

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
  simp only [not_and] at h
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
    dsimp [Disjoint]
    dsimp [Finset.instHasSubset]
    simp only [Finset.notMem_empty, imp_false]
    intro s3 rel1 rel2 a a_in_s3
    have a_in_s1 := rel1 a_in_s3
    have a_in_s2 := rel2 a_in_s3
    have a_in_s : a ∈ s := s1_is_subset (rel1 a_in_s3)
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
    simp only [Finset.mem_union]
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

lemma contains_one_or_zero (n : ℕ) (s1 s2 : Finset ℕ) (partition : s1 ∪ s2 = Finset.Icc n (n + 5)) (no_dups: s1 ∩ s2 = ∅)
                      (equal_products : ∏ m ∈ s1, m = ∏ m ∈ s2, m) : ∃ x ∈ (s1 ∪ s2), x = 1 ∨ x = 0 := by
  let odd_s := (s1 ∪ s2).filter (λ x => Odd x)
  let odd_div_by_5 := odd_s.filter (λ x => 5 ∣ x)
  let odd_div_by_3 := odd_s.filter (λ x => 3 ∣ x)

  let odd_non_div_by_5 := odd_s.filter (λ x => ¬ 5 ∣ x)
  let odd_non_div_by_3 := odd_s.filter (λ x => ¬ 3 ∣ x)

  have : odd_s = Finset.filter (fun x ↦ Odd x) (Finset.Icc n (n + 5)) := by
    dsimp[odd_s]
    rw[partition]

  have three_odd_numbers := exactly_three_odd_numbers n odd_s this

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

  have exists_odd_x_non_div_by_3_5 : ∃ x ∈ s1 ∪ s2, ¬ 3 ∣ x ∧ ¬ 5 ∣ x ∧ ¬ 2 ∣ x := by
    obtain ⟨x, ⟨x_in_odd_s, non_div_3, non_div_5⟩⟩ := subsets_must_overlap_pigeonhole
      odd_s odd_non_div_by_3 odd_non_div_by_5 (λ x => ¬ 3 ∣ x) (λ x => ¬ 5 ∣ x)
      rfl rfl 2 b 3 size_calculation
      three_odd_numbers exactly_2_non_divisers_of_3 rfl
    use x
    constructor
    · simp_all only [Finset.mem_filter, odd_s]
    · constructor
      · exact non_div_3
      grind

  have exists_x_no_prime_divisors : ∃ x ∈ (s1 ∪ s2), ¬ ∃ (p : ℕ), Nat.Prime p ∧ p ∣ x := by
    obtain ⟨x, x_in_s1_s2, non_div_3, non_div_5, non_div_2⟩ := exists_odd_x_non_div_by_3_5
    use x
    constructor
    · exact x_in_s1_s2
    · intro h
      obtain ⟨p, ⟨pp, p_div⟩⟩ := h
      have p_gt_5_not_dvd := p_gt_five_not_divides n s1 s2 partition no_dups equal_products x x_in_s1_s2

      have to_apply := two_three_five_and_more_is_enough x non_div_2 non_div_3 non_div_5 p_gt_5_not_dvd
      apply to_apply
      use p

  obtain ⟨x, ⟨x_in_s1_u_s2, no_prime⟩⟩ := exists_x_no_prime_divisors
  use x
  constructor
  · exact x_in_s1_u_s2
  · left
    exact (Not.imp_symm Nat.exists_prime_and_dvd) no_prime

lemma n_eq_1_of_contains_one
  (n : ℕ) (n_not_zero : n ≠ 0) (contains_one : 1 ∈ Finset.Icc n (n + 5)) : n = 1 := by
  simp_all only [ne_eq, Finset.mem_Icc, le_add_iff_nonneg_left, zero_le, and_true]
  omega

lemma diffs_of_disjoint (t s w : Finset ℕ) (t_subst_s : t ⊆ s) (disjoint: Disjoint t w) : t ⊆ s \ w := by
  simp only [Finset.subset_sdiff, and_self, t_subst_s, disjoint]

lemma not_empty_subst_of_nonempty (t : Finset ℕ) (t_nonempty : t.Nonempty) : ¬ t ⊆ ∅ := by
  rw [Finset.subset_empty]
  exact t_nonempty.ne_empty

lemma mem_of_subst (k : ℕ) (t s : Finset ℕ) (k_in_t : k ∈ t) (t_subst_s : t ⊆ s) : k ∈ s := by
  apply t_subst_s
  simp_all only

lemma contradiction_of_finset_icc_1_6 (s1 s2 : Finset ℕ) (partition : s1 ∪ s2 = Finset.Icc 1 6)
  (disjoint : s1 ∩ s2 = ∅) (eq_prod: ∏ m ∈ s1, m = ∏ m ∈ s2, m) : False := by
  have : 5 ∈ s1 ∪ s2 := by
    rw[partition]
    simp only [Finset.mem_Icc, Nat.one_le_ofNat, Nat.reduceLeDiff, and_self]
  simp only [Finset.mem_union] at this
  cases this
  · case inl five_in_s1 =>
    have s2_in_s1_s2: s2 ⊆ s1 ∪ s2 := Finset.subset_union_right
    have explicit_s2 : s2 ⊆ {1, 2, 3, 4, 6} := by
      have five_not_in_s2 : Disjoint s2 {5} := by
        have s1_s2_disjoint : Disjoint s1 s2 := Finset.disjoint_iff_inter_eq_empty.mpr disjoint
        simp_all only [Finset.disjoint_singleton_right]
        intro five_in_s2
        dsimp[Disjoint] at s1_s2_disjoint
        have five_set_in_s1 : {5} ⊆ s1 := by
          simp_all only [Finset.singleton_subset_iff]
        have five_set_in_s2 : {5} ⊆ s2 := by
          simp_all only [Finset.singleton_subset_iff]
        have set_five_in_empty := s1_s2_disjoint five_set_in_s1 five_set_in_s2
        have : ({5} : Finset ℕ).Nonempty := by
          simp_all only [Finset.singleton_subset_iff, Finset.singleton_nonempty]
        apply not_empty_subst_of_nonempty {5} this
        exact set_five_in_empty
      have explicit_interval: Finset.Icc 1 6 = {1, 2, 3, 4, 5, 6} := by
        rfl
      have := diffs_of_disjoint s2 (s1 ∪ s2) {5} s2_in_s1_s2 five_not_in_s2
      rw [partition] at this
      rw[explicit_interval] at this
      simp_all only [Finset.disjoint_singleton_right]
      exact this
    have others : ∀ k ∈ s2, ¬ 5 ∣ k := by
      intro k
      intro k_in_s2
      have k_in_explicit_s2 : k ∈ ({1, 2, 3, 4, 6} : Finset ℕ) := by
        exact mem_of_subst k s2 {1, 2, 3, 4, 6} k_in_s2 explicit_s2
      intro five_div_k
      simp_all only [Finset.mem_insert, Finset.mem_singleton]
      obtain rfl | rfl | rfl | rfl | rfl | rfl := k_in_explicit_s2 <;> contradiction

    have five_div_prod_s1 := Finset.dvd_prod_of_mem (λ n : ℕ => n) five_in_s1

    have five_div_prod_s2 : 5 ∣ ∏ m ∈ s2, m := by
      rw[eq_prod] at five_div_prod_s1
      exact five_div_prod_s1
    obtain ⟨l, ⟨l_in_s2, five_div_l⟩⟩ :=
      Prime.exists_mem_finset_dvd Nat.prime_five.prime five_div_prod_s2
    exact others l l_in_s2 five_div_l
  · case inr five_in_s2 =>
    have s1_in_s2_s1: s1 ⊆ s2 ∪ s1 := Finset.subset_union_right
    have explicit_s1 : s1 ⊆ {1, 2, 3, 4, 6} := by
      have five_not_in_s1 : Disjoint s1 {5} := by
        have : s2 ∩ s1 = ∅ := by
          rw[Finset.inter_comm] at disjoint
          exact disjoint
        have s2_s1_disjoint : Disjoint s2 s1 := Finset.disjoint_iff_inter_eq_empty.mpr this
        simp_all only [Finset.disjoint_singleton_right]
        intro five_in_s
        dsimp[Disjoint] at s2_s1_disjoint
        have five_set_in_s1 : {5} ⊆ s1 := by
          simp_all only [Finset.singleton_subset_iff]
        have five_set_in_s2 : {5} ⊆ s2 := by
          simp_all only [Finset.singleton_subset_iff]
        have set_five_in_empty := s2_s1_disjoint five_set_in_s2 five_set_in_s1
        have : ({5} : Finset ℕ).Nonempty := by
          simp_all only [Finset.singleton_subset_iff, Finset.singleton_nonempty]
        apply not_empty_subst_of_nonempty {5} this
        exact set_five_in_empty
      have explicit_interval: Finset.Icc 1 6 = {1, 2, 3, 4, 5, 6} := by
        rfl
      have := diffs_of_disjoint s1 (s2 ∪ s1) {5} s1_in_s2_s1 five_not_in_s1
      rw[Finset.union_comm] at this
      rw [partition] at this
      rw[explicit_interval] at this
      simp_all only [Finset.disjoint_singleton_right]
      exact this
    have others : ∀ k ∈ s1, ¬ 5 ∣ k := by
      intro k
      intro k_in_s1
      have k_in_explicit_s1 : k ∈ ({1, 2, 3, 4, 6} : Finset ℕ) := by
        exact mem_of_subst k s1 {1, 2, 3, 4, 6} k_in_s1 explicit_s1
      intro five_div_k
      simp_all only [Finset.mem_insert, Finset.mem_singleton]
      omega

    have five_div_prod_s2 := Finset.dvd_prod_of_mem (λ n : ℕ => n) five_in_s2
    have five_div_prod_s1 : 5 ∣ ∏ m ∈ s1, m := by
      rw[← eq_prod] at five_div_prod_s2
      exact five_div_prod_s2
    obtain ⟨l, ⟨l_in_s1, five_div_l⟩⟩ :=
      Prime.exists_mem_finset_dvd Nat.prime_five.prime five_div_prod_s1
    exact others l l_in_s1 five_div_l

lemma no_partitions (n : ℕ) (s1 s2 : Finset ℕ)
        (partition : s1 ∪ s2 = Finset.Icc n (n + 5))
        (no_dups : s1 ∩ s2 = ∅)
        (eq_prod : ∏ m ∈ s1, m = ∏ m ∈ s2, m)
        (n_not_zero : n ≠ 0) : False := by
  obtain ⟨x, ⟨x_in_partition, x_eq_1⟩⟩ := contains_one_or_zero n s1 s2 partition no_dups eq_prod
  rw[partition] at x_in_partition
  cases x_eq_1
  case inl h =>
    rw[h] at x_in_partition
    have n_eq_1 := n_eq_1_of_contains_one n n_not_zero x_in_partition
    rw[n_eq_1] at partition
    exact contradiction_of_finset_icc_1_6 s1 s2 partition no_dups eq_prod
  case inr h =>
    simp_all only [ne_eq, Finset.mem_Icc, nonpos_iff_eq_zero, le_add_iff_nonneg_left, zero_le, and_true]

lemma contradiction_of_in_empty (x : ℕ+) (s : Finset ℕ+) (s_empty: s = ∅) (x_in_s : x ∈ s) : False := by
  subst s_empty
  simp_all only [Finset.notMem_empty]

lemma n_plus_not_zero (n : ℕ+) : ∃(k : ℕ), n = k ∧ k ≠ 0 := by
  simp_all only [ne_eq, exists_eq_left', PNat.ne_zero, not_false_eq_true]

snip end

determine SolutionSet : Finset ℕ+ := {}

problem imo1970_p4 (n : ℕ+):
  n ∈ SolutionSet ↔
    ∃ s1 s2 : Finset ℕ,
      s1 ∪ s2 = Finset.Icc n.val (n.val + 5) ∧
      s1 ∩ s2 = ∅ ∧
      ∏ m ∈ s1, m = ∏ m ∈ s2, m := by
  apply Iff.intro
  · intro n_in_solution_set
    have no_solutions : SolutionSet = ∅ := by
      simp_all only [Finset.notMem_empty]
    exfalso
    exact contradiction_of_in_empty n SolutionSet no_solutions n_in_solution_set
  · intro H
    obtain ⟨s1, s2, ⟨partition, no_dups, eq_prod⟩⟩ := H

    obtain ⟨k, ⟨n_eq_k, k_not_zero⟩⟩ := n_plus_not_zero n
    rw [n_eq_k] at partition

    exfalso
    exact no_partitions k s1 s2 partition no_dups eq_prod k_not_zero

end Imo1970P4
