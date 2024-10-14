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
equals the product of the nubmers in the other set.
-/

namespace Imo1970P4

snip begin

lemma card_opposite (s s' s'' : Finset ℕ) (predicate: ℕ → Prop) [DecidablePred predicate] (filter : s' = (s.filter (λ x => predicate x)))
                    (opposite_filter: s'' = (s.filter (λ x => ¬ predicate x))) : s'.card + s''.card = s.card := by
  rw[filter]
  rw[opposite_filter]
  have := @Finset.filter_card_add_filter_neg_card_eq_card ℕ s predicate
  apply this

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
    have p_dvd_prod_x : p ∣ ∏ m ∈ s1, m := by
      have := Finset.dvd_prod_of_mem (λ n : ℕ => n) x_in_s1
      exact Dvd.dvd.trans p_dvd_x this

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
    have := Finset.dvd_prod_of_mem (λ n : ℕ => n) x_in_s2
    simp at this
    have p_dvd_prod_x : p ∣ ∏ m ∈ s2, m := (Dvd.dvd.trans p_dvd_x this)

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

lemma odd_props (n : ℕ) (odd_s : Finset ℕ) (s_odd_eq : odd_s = (Finset.Icc n (n + 5)).filter (λ x => Odd x)) :
  ∃ (a b c : ℕ), {a, b, c} = odd_s ∧ b = a + 2 ∧ c = b + 2 := by
  cases Decidable.em (Odd n)
  case inl h =>
    have h2 := Odd.not_two_dvd_nat h
    use n
    use n + 2
    use n + 4
    simp_all
    · ext x
      simp_all
      apply Iff.intro
      intro H
      constructor
      · omega
      · cases H
        case inl h3 =>
          simp_all only
        case inr h4 =>
          cases h4
          case inl h5 =>
            simp_all
            dsimp[Odd]
            dsimp[Odd] at h
            obtain ⟨k, h6⟩ := h
            use k + 1
            rw[h6]
            ring_nf
          case inr h6 =>
            simp_all only
            dsimp[Odd]
            dsimp[Odd] at h
            obtain ⟨k, h6⟩ := h
            use k + 2
            rw[h6]
            ring_nf
      intro H
      obtain ⟨a, Hh⟩ := H
      have h3 := Odd.not_two_dvd_nat Hh
      by_contra Hhh
      simp_all only [Nat.two_dvd_ne_zero, not_or]
      omega
  case inr h =>
    use n + 1
    use n + 3
    use n + 5
    simp_all
    have := Even.two_dvd h
    ext x
    simp_all
    apply Iff.intro
    intro H
    constructor
    · omega
    · cases H
      case inl h3 =>
        simp_all only [Even.add_one]
      case inr h4 =>
        cases h4
        case inl h5 =>
          have : Odd 3 := by decide
          have := Even.add_odd h this
          rw[h5]
          exact this
        case inr h6 =>
          have : Odd 5 := by decide
          have := Even.add_odd h this
          rw[h6]
          exact this
    intro H
    obtain ⟨a, Hh⟩ := H
    have h3 := Odd.not_two_dvd_nat Hh
    by_contra Hhh
    simp_all only [Nat.two_dvd_ne_zero, not_or]
    omega

lemma exactly_three_odd_numbers (n : ℕ) (odd_s : Finset ℕ)
                                (odd_s_eq: odd_s = (Finset.Icc n (n + 5)).filter (λ x => Odd x)): (odd_s).card = 3 := by
  -- ∃ (a b c : ℕ), {a, b, c} = odd_s ∧ odd_s.card = 3
  obtain ⟨x, y, z, ⟨left, ⟨y_eq, z_eq⟩⟩⟩ := odd_props n odd_s odd_s_eq
  have := (@Finset.card_eq_three ℕ odd_s).mpr
  apply this
  use x
  use x + 2
  use x + 2 + 2
  constructor
  · omega
  · constructor
    · omega
    · constructor
      · omega
      · simp_all only






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

  rw[odd_s_eq]

  intro x x_in
  intro y y_in

  simp at x_in
  obtain ⟨⟨X1, X2⟩, X3⟩ := x_in

  simp at y_in
  obtain ⟨⟨Y1, Y2⟩, Y3⟩ := y_in

  apply at_most_one n
  rw[partition] at X1
  exact X1
  rw[partition] at Y1
  exact Y1
  exact X3
  exact Odd.not_two_dvd_nat X2
  exact Y3
  exact Odd.not_two_dvd_nat Y2

lemma unique_divisor (n : ZMod 3) (a b c : ℕ) (n_eq_a : n = a) (s : Finset ℕ) (s_eq : s = ({a, b, c} : Finset ℕ)) (b_eq: b = a + 2) (c_eq : c = b + 2) : ∃! a', a' ∈ s ∧ 3 ∣ a' := by
  fin_cases n
  · use a
    have three_div_a : 3 ∣ a := by
      apply (ZMod.natCast_zmod_eq_zero_iff_dvd a 3).mp
      simp_all only [Fin.zero_eta]
    constructor
    · simp
      constructor
      · aesop
      · simp_all only [Fin.zero_eta]
    · intro o
      rintro ⟨o_in_s, three_div_o⟩
      rw[s_eq] at o_in_s
      simp_all only [Fin.zero_eta, Finset.mem_insert, Finset.mem_singleton]
      omega
  · use b
    have three_div_b : 3 ∣ b := by
      simp_all only [Fin.mk_one]
      apply (ZMod.natCast_zmod_eq_zero_iff_dvd (a + 2) 3).mp
      simp_all only [Nat.cast_add, Nat.cast_ofNat]
      rw[← n_eq_a]
      reduce_mod_char
    constructor
    · simp_all only [Fin.mk_one, Finset.mem_insert, add_right_eq_self, OfNat.ofNat_ne_zero, Finset.mem_singleton, self_eq_add_right, or_false, or_true, and_self]
    · intro o
      rintro ⟨o_in_s, three_div_o⟩
      rw[s_eq] at o_in_s
      simp_all
      omega
  · use c
    have three_div_c : 3 ∣ c := by
      simp_all only [Nat.dvd_add_self_right]
      apply (ZMod.natCast_zmod_eq_zero_iff_dvd (a + 1) 3).mp
      simp_all
      rw[← n_eq_a]
      reduce_mod_char
    constructor
    · simp_all only [Nat.dvd_add_self_right, Finset.mem_insert, add_right_eq_self, OfNat.ofNat_ne_zero, Finset.mem_singleton, or_true, and_self]
    · intro o
      rintro ⟨o_in_s, three_div_o⟩
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
  simp_all only [forall_exists_index, Finset.card_singleton, implies_true, and_imp]
  obtain ⟨left, right⟩ := H
  obtain ⟨left, right_1⟩ := left
  ext a : 1
  simp_all only [Finset.mem_filter, Finset.mem_singleton]
  apply Iff.intro
  · intro a_1
    simp_all only
  · intro a_1
    subst a_1
    simp_all only [and_self]

lemma three_divides_odd_exactly_once (n : ℕ) (s odd_s : Finset ℕ) (partition : s = Finset.Icc n (n + 5))
                                     (odd_s_eq: odd_s = s.filter (λ x => Odd x)) : (odd_s.filter (λ x => 3 ∣ x)).card = 1 := by
  rw[partition] at odd_s_eq
  obtain ⟨a, b, c, ⟨explicit_finset, b_comp, c_comp⟩⟩ := odd_props n odd_s odd_s_eq
  rw[← partition] at odd_s_eq
  rw[← explicit_finset]
  have : (∃! a' ∈ ({a, b, c} : Finset ℕ), 3 ∣ a') → (Finset.filter (fun x ↦ 3 ∣ x) {a, b, c}).card = 1 := by
    apply card_1_of_exists_unique
  apply this
  have := unique_divisor a a b c rfl odd_s (by aesop) b_comp c_comp
  rw[← explicit_finset] at this
  exact this

lemma empty_of_empty_subset (s : Finset ℕ) : s = {x_1 | x_1 ∈ (∅ : Finset ℕ) } → s = ∅ := by
  simp

lemma no_prime_divisors (x : ℕ) (x_not_zero : x ≠ 0) (no_prime : ¬ ∃ (p : ℕ), p.Prime ∧ p ∣ x) : x = 1 := by

  have empty_prime_factors: x.primeFactors = ∅ → x = 1 := by
    intro a
    simp_all only [Nat.primeFactors_eq_empty, false_or]

  have mem_primeFactors : x.primeFactors = {p | Nat.Prime p ∧ p ∣ x ∧ x ≠ 0} := by
    ext x
    simp [Nat.mem_primeFactors]

  have lift_subtypes: x.primeFactors = {x_1 | x_1 ∈ (∅ : Finset ℕ) } → x.primeFactors = ∅ := by
    intro H
    exact empty_of_empty_subset x.primeFactors H

  apply empty_prime_factors
  apply lift_subtypes
  rw[mem_primeFactors]

  have no_prime_for_simp : ∀ p : ℕ, ¬ (Nat.Prime p ∧ p ∣ x ∧ x ≠ 0) := by
    intro p
    intro H
    apply no_prime
    use p
    obtain ⟨a, b, _⟩ := H
    constructor
    · exact a
    · exact b

  have goal: { p | Nat.Prime p ∧ p ∣ x ∧ x ≠ 0 } = {x_1 | (x_1 : ℕ) ∈ ({} : Finset ℕ) } := by
    simp_all only [Finset.not_mem_empty]

  exact goal

lemma enumerate_primes_le_5 (p : ℕ) (pp : p.Prime) (p_le_5 : p ≤ 5) : p ∈ ({2, 3, 5} : Finset ℕ) := by
  by_contra H
  simp at H
  obtain ⟨a, b, c⟩ := H
  have := Nat.Prime.five_le_of_ne_two_of_ne_three pp
  omega

lemma two_three_five_and_more_is_enough (x : ℕ) (two_does_not_divide : ¬ 2 ∣ x) (three_does_not_divide : ¬ 3 ∣ x) (five_does_not_divide : ¬ 5 ∣ x)
  (p_gt_5_not_dvd : ∀ (p : ℕ), p.Prime → p > 5 → ¬p ∣ x):
  ¬ ∃ (p : ℕ), (p.Prime ∧ p ∣ x) := by
  have p_le_5_not_dvd : ∀ (p : ℕ), p.Prime → p ≤ 5 → ¬ p ∣ x := by
    intro p
    intro pp
    intro p_le_5
    intro p_div_x

    have p_subset : p ∈ ({2, 3, 5} : Finset ℕ) := enumerate_primes_le_5 p pp p_le_5

    have : p = 2 ∨ p = 3 ∨ p = 5 := by
      simp_all only [Nat.two_dvd_ne_zero, gt_iff_lt, Finset.mem_insert, Finset.mem_singleton]

    cases this
    case inl h =>
      simp_all only [Nat.two_dvd_ne_zero, gt_iff_lt, Finset.mem_insert, Finset.mem_singleton, true_or]
      omega
    case inr h =>
      cases h
      case inl h =>
        simp_all only [Nat.two_dvd_ne_zero, gt_iff_lt]
      case inr h =>
        simp_all only [Nat.two_dvd_ne_zero, gt_iff_lt, Finset.mem_insert, Finset.mem_singleton]
  rintro ⟨p, ⟨pp, div⟩⟩
  have p_gt_5_implies := p_gt_5_not_dvd p pp
  have p_le_5_implies := p_le_5_not_dvd p pp
  omega

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
      constructor
      · exact non_div_5
      · dsimp[odd_s] at x_in_odd_s
        intro two_div_x
        have : ¬ Odd x := by
          intro odd_x
          dsimp[Odd] at odd_x
          omega
        simp_all only [gt_iff_lt, Finset.mem_filter]

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
  · have := Decidable.em (x = 0)
    cases this
    case inl h =>
      right
      exact h
    case inr h =>
      left
      exact no_prime_divisors x h no_prime

lemma n_eq_1_of_contains_one
  (n : ℕ) (n_not_zero : n ≠ 0) (contains_one : 1 ∈ Finset.Icc n (n + 5)) : n = 1 := by
  simp_all only [ne_eq, Finset.mem_Icc, le_add_iff_nonneg_left, zero_le, and_true]
  omega

lemma diffs_of_disjoint (t s w : Finset ℕ) (t_subst_s : t ⊆ s) (disjoint: Disjoint t w) : t ⊆ s \ w := by
  simp [Finset.subset_sdiff, *]

lemma not_empty_subst_of_nonempty (t : Finset ℕ) (t_nonempty : t.Nonempty) : ¬ t ⊆ ∅ := by
  rw [Finset.subset_empty]
  exact t_nonempty.ne_empty

lemma subset_of_union_right (t s : Finset ℕ) : t ⊆ s ∪ t := by
  have := @Finset.subset_union_right ℕ _ s t
  exact this

lemma mem_of_subst (k : ℕ) (t s : Finset ℕ) (k_in_t : k ∈ t) (t_subst_s : t ⊆ s) : k ∈ s := by
  apply t_subst_s
  simp_all only

lemma contradiction_of_finset_icc_1_6 (s1 s2 : Finset ℕ) (partition : s1 ∪ s2 = Finset.Icc 1 6)
  (disjoint : s1 ∩ s2 = ∅) (eq_prod: ∏ m ∈ s1, m = ∏ m ∈ s2, m) : False := by
  have : 5 ∈ s1 ∪ s2 := by
    rw[partition]
    simp
  simp at this
  cases this
  · case inl five_in_s1 =>
    have s2_in_s1_s2: s2 ⊆ s1 ∪ s2 := subset_of_union_right s2 s1
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
        have : Nonempty ({5} : Finset ℕ)  := by
          simp_all only [Finset.singleton_subset_iff, Finset.mem_singleton, nonempty_subtype, exists_eq]
        have : ({5} : Finset ℕ).Nonempty := by
          simp_all only [Finset.singleton_subset_iff, Finset.mem_singleton, nonempty_subtype, exists_eq, Finset.singleton_nonempty]
        apply not_empty_subst_of_nonempty {5} this
        exact set_five_in_empty
      have s2_in_interval : s2 ⊆ Finset.Icc 1 6 := by
        rw[partition] at s2_in_s1_s2
        exact s2_in_s1_s2
      have explicit_interval: Finset.Icc 1 6 = {1, 2, 3, 4, 5, 6} := by
        rfl
      rw [explicit_interval] at s2_in_interval
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
      cases k_in_explicit_s2 with
      | inl h =>
        subst h
        contradiction
      | inr h_1 =>
        cases h_1 with
        | inl h =>
          subst h
          contradiction
        | inr h_2 =>
          cases h_2 with
          | inl h =>
            subst h
            contradiction
          | inr h_1 =>
            cases h_1 with
            | inl h =>
              subst h
              contradiction
            | inr h_2 =>
              subst h_2
              contradiction

    have five_div_prod_s1 := Finset.dvd_prod_of_mem (λ n : ℕ => n) five_in_s1

    have five_div_prod_s2 : 5 ∣ ∏ m ∈ s2, m := by
      rw[eq_prod] at five_div_prod_s1
      exact five_div_prod_s1
    obtain ⟨l, ⟨l_in_s2, five_div_l⟩⟩ := prime_dvd_elem_of 5 (by decide) s2 five_div_prod_s2
    exact others l l_in_s2 five_div_l
  · case inr five_in_s2 =>
    have s1_in_s2_s1: s1 ⊆ s2 ∪ s1 := subset_of_union_right s1 s2
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
        have : Nonempty ({5} : Finset ℕ) := by
          simp_all only [Finset.singleton_subset_iff, Finset.mem_singleton, nonempty_subtype, exists_eq]
        have : ({5} : Finset ℕ).Nonempty := by
          simp_all only [Finset.singleton_subset_iff, Finset.mem_singleton, nonempty_subtype, exists_eq, Finset.singleton_nonempty]
        apply not_empty_subst_of_nonempty {5} this
        exact set_five_in_empty
      have s2_in_interval : s1 ⊆ Finset.Icc 1 6 := by
        rw[Finset.union_comm] at partition
        rw[partition] at s1_in_s2_s1
        exact s1_in_s2_s1
      have explicit_interval: Finset.Icc 1 6 = {1, 2, 3, 4, 5, 6} := by
        rfl
      rw [explicit_interval] at s2_in_interval
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
      cases k_in_explicit_s1 with
      | inl h =>
        subst h
        contradiction
      | inr h_1 =>
        cases h_1 with
        | inl h =>
          subst h
          contradiction
        | inr h_2 =>
          cases h_2 with
          | inl h =>
            subst h
            contradiction
          | inr h_1 =>
            cases h_1 with
            | inl h =>
              subst h
              contradiction
            | inr h_2 =>
              subst h_2
              contradiction
    have five_div_prod_s2 := Finset.dvd_prod_of_mem (λ n : ℕ => n) five_in_s2
    have five_div_prod_s1 : 5 ∣ ∏ m ∈ s1, m := by
      rw[← eq_prod] at five_div_prod_s2
      exact five_div_prod_s2
    obtain ⟨l, ⟨l_in_s1, five_div_l⟩⟩ := prime_dvd_elem_of 5 (by decide) s1 five_div_prod_s1
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
    simp_all only [ne_eq, one_ne_zero, not_false_eq_true, Finset.mem_Icc, le_refl, le_add_iff_nonneg_right,
  zero_le, and_self]
    exact contradiction_of_finset_icc_1_6 s1 s2 partition no_dups eq_prod
  case inr h =>
    simp_all only [ne_eq, Finset.mem_Icc, nonpos_iff_eq_zero, le_add_iff_nonneg_left, zero_le, and_true]

lemma contradiction_of_in_empty (x : ℕ+) (s : Finset ℕ+) (s_empty: s = ∅) (x_in_s : x ∈ s) : False := by
  subst s_empty
  simp_all only [Finset.not_mem_empty]

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
      simp_all only [Finset.not_mem_empty]
    exfalso
    exact contradiction_of_in_empty n SolutionSet no_solutions n_in_solution_set
  · intro H
    obtain ⟨s1, s2, ⟨partition, no_dups, eq_prod⟩⟩ := H

    obtain ⟨k, ⟨n_eq_k, k_not_zero⟩⟩ := n_plus_not_zero n
    rw [n_eq_k] at partition

    exfalso
    exact no_partitions k s1 s2 partition no_dups eq_prod k_not_zero

end Imo1970P4
