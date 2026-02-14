/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InternLM-MATH LEAN Formalizer v0.1, Constantin Seebach
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Olympiad 1971, Problem 3

Prove that we can find an infinite set of positive integers of the form 2^n - 3
(where n is a positive integer) every pair of which are relatively prime.
-/

namespace Imo1971P3

snip begin

/-!
We follow the revised solution from https://artofproblemsolving.com/wiki/index.php/1971_IMO_Problems/Problem_3 by pf02.
-/


def pairwise_coprime_f (s : Set ℕ) : Prop := s.Pairwise fun m n ↦ Nat.Coprime (2 ^ n - 3) (2 ^ m - 3)


def a (n : ℕ) : ℕ := match n with
| 0 => 3
| n+1 => (a n) * ∏ p ∈ (2 ^ (a n) - 3).primeFactors, (p-1)


theorem a_ge_and_A_odd (n : ℕ) : 3 ≤ a n ∧ Odd (2 ^ (a n) - 3) := by
  fun_induction a with
  | case1 =>
    and_intros
    · rfl
    · exact Nat.odd_iff.mpr rfl
  | case2 n ih =>
    have h : 3 ≤ 2 ^ (a n * ∏ p ∈ (2 ^ a n - 3).primeFactors, (p - 1)) := by
      have : 0 < ∏ p ∈ (2 ^ a n - 3).primeFactors, (p - 1) := by
        rw [Nat.lt_iff_add_one_le]
        apply Finset.one_le_prod'
        · simp only [Nat.mem_primeFactors, ne_eq, and_imp]
          intro x xp _ _
          exact Nat.le_sub_one_of_lt xp.two_le
      refine (Nat.clog_le_iff_le_pow one_lt_two).mp ?_
      rw [show Nat.clog 2 3 = 2 by rfl]
      nlinarith
    and_intros
    · apply le_mul_of_le_mul_right _ ih.left
      rw [le_mul_iff_one_le_right (by simp)]
      lia
    · rw [Nat.odd_sub', iff_true_left, Nat.even_pow']
      · simp
      · refine Nat.mul_ne_zero ?_ ?_
        · lia
        · lia
      · exact Nat.odd_iff.mpr rfl
      · exact h


theorem A_ge' (n : ℕ) : 8 ≤ 2 ^ a n := by
  refine (Nat.clog_le_iff_le_pow one_lt_two).mp ?_
  rw [show Nat.clog 2 8 = 3 by rfl]
  exact (a_ge_and_A_odd _).left


theorem a_strictMono : StrictMono a := by
  refine strictMono_nat_of_lt_succ ?_
  intro n
  have := a_ge_and_A_odd n
  nth_rw 2 [a.eq_def]
  refine (Nat.lt_mul_iff_one_lt_right ?_).mpr ?_
  · lia
  · refine (Finset.one_lt_prod_iff_of_one_le ?_).mpr ?_
    · simp only [Nat.mem_primeFactors, ne_eq, and_imp]
      intro x xp _ _
      exact Nat.le_sub_one_of_lt xp.two_le
    · let ⟨p, ph1, ph2, ph3⟩ := (@Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt (2 ^ a n - 3) ?_ ).resolve_left ?_
      · use p
        and_intros
        · simp [ph1, ph2]
          grind only [= Nat.odd_iff]
        · grind only [= Nat.odd_iff, Nat.Prime.two_le (ph1)]
      · have := A_ge' n
        lia
      · grind only [= Nat.odd_iff]


theorem a_prime_lemma (n1 n2 p : ℕ) (h1 : n1 < n2) (h2 : p ∣ 2 ^ (a n1) - 3) (h3 : Nat.Prime p) : p - 1 ∣ a n2 := by
  fun_induction a n2
  · simp at h1
  · expose_names
    by_cases n1=n
    · subst n
      apply Nat.dvd_mul_left_of_dvd
      apply Finset.dvd_prod_of_mem
      simp [h3, h2]
      grind only [= Nat.odd_iff, a_ge_and_A_odd n1]
    · replace ih1 := ih1 (by omega)
      exact Nat.dvd_mul_right_of_dvd ih1 _


theorem a_pairwise_coprime : pairwise_coprime_f (Set.range a) := by
  intro x1 hx1 x2 hx2 ne
  let ⟨i1, hi1⟩ := hx1
  let ⟨i2, hi2⟩ := hx2
  wlog w : i1 < i2
  · have w' : i1 > i2 := by grind only
    have := @this x2 hx2 x1 hx1 ne.symm i2 hi2 i1 hi1 w'
    exact Nat.coprime_comm.mp this
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra!
  obtain ⟨p, php, ph1, ph2⟩ : ∃ p, Nat.Prime p ∧ p ∣ (2 ^ (a i1) - 3) ∧ p ∣ (2 ^ (a i2) - 3) := by
    let ⟨p, h1, h2⟩ := Nat.exists_prime_and_dvd this
    use p
    and_intros
    · exact h1
    · apply dvd_trans h2
      rw [<-hi1]
      exact Nat.gcd_dvd_right _ _
    · apply dvd_trans h2
      rw [<-hi2]
      exact Nat.gcd_dvd_left _ _
  have pOdd : Odd p := by
    apply Odd.of_dvd_nat _ ph1
    apply (a_ge_and_A_odd _).right
  have := a_prime_lemma _ _ p w ph1 php
  rw [dvd_iff_exists_eq_mul_left] at this
  let ⟨b, bh⟩ := this
  let B : ℤ := 2^(a i2) - 1
  have : ↑p ∣ B := by
    unfold B
    rw [bh, pow_mul]
    apply Int.prime_dvd_pow_sub_one php
    refine IsCoprime.pow_left ?_
    rw [<-Nat.cast_ofNat, Nat.isCoprime_iff_coprime]
    apply pOdd.coprime_two_left
  have : ↑p ∣ B - (2 ^ a i2 - 3) := by
    zify at ph2
    rw [Nat.cast_sub, Nat.cast_pow] at ph2
    · apply dvd_sub <;> trivial
    · have := A_ge' i2
      lia
  unfold B at this
  simp only [sub_sub_sub_cancel_left, Int.reduceSub] at this
  norm_cast at this
  rw [Nat.dvd_prime_two_le Nat.prime_two (Nat.Prime.two_le php)] at this
  subst p
  contradiction


snip end

problem imo1971_p3 :
   ∃ s : Set ℕ+,
     s.Infinite ∧
     s.Pairwise fun m n ↦ Nat.Coprime (2 ^ n.val - 3) (2 ^ m.val - 3) := by
  use {⟨a n, Nat.zero_lt_of_lt (a_ge_and_A_odd n).left⟩ | n : ℕ}
  and_intros
  · apply Set.infinite_range_of_injective
    apply StrictMono.injective
    apply a_strictMono
  · intro x hx y hy ne
    apply a_pairwise_coprime <;> aesop

end Imo1971P3
