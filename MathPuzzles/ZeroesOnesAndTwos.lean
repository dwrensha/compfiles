/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Parity
import Mathlib.Data.Nat.Digits
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.BigOperators.Order
import Mathlib.Algebra.BigOperators.Ring

/-!
(From Mathematical Puzzles: A Connoisseur's Collection by Peter Winkler.)

Let n be a natural number. Prove that

  (a) n has a (nonzero) multiple whose representation in base 10 contains
      only zeroes and ones; and
  (b) 2^n has a multiple whose representation contains only ones and twos.
-/

namespace ZerosOnesAndTwos

open BigOperators

def ones (b : ℕ) : ℕ → ℕ
| k => ∑i in Finset.range k, b^i

def map_mod (n : ℕ) (hn: 0 < n) (f : ℕ → ℕ) : ℕ → Fin n
| m => ⟨f m % n, Nat.mod_lt (f m) hn⟩

lemma pigeonhole (n : ℕ) (f : ℕ → Fin n) :
  ∃ a b : ℕ, a < b ∧ f a = f b :=
let ⟨a, b, hne, hfe⟩ := Finite.exists_ne_map_eq_of_infinite f
hne.lt_or_lt.elim (λ h ↦ ⟨a, b, h, hfe⟩) (λ h ↦ ⟨b, a, h, hfe.symm⟩)

def is_zero_or_one : ℕ → Prop
| 0 => True
| 1 => True
| _ => False

def all_zero_or_one (l : List ℕ) : Prop := ∀ e ∈ l, is_zero_or_one e

lemma digits_lemma
    (base : ℕ)
    (h2 : 2 ≤ base)
    (n : ℕ)
    (hn : 0 < n)
    : (Nat.digits base (base * n)) = 0 :: (Nat.digits base n) := by
  have := Nat.digits_add base h2 0 n (Nat.lt_of_succ_lt (Nat.succ_le_iff.mp h2))
                              (Or.inr (ne_of_gt hn))
  rwa [zero_add (base * n)] at this

lemma times_base_still_all_zero_or_one
    (base : ℕ)
    (h2 : 2 ≤ base)
    (n : ℕ)
    (hn : all_zero_or_one (Nat.digits base n))
    : all_zero_or_one (Nat.digits base (base * n)) := by
  cases' (Nat.eq_zero_or_pos n) with hz hp
  · rw [hz]
    simp [mul_zero, Nat.digits_zero, all_zero_or_one]
  · rw [digits_lemma base h2 n hp]
    simpa[is_zero_or_one, all_zero_or_one]

lemma base_pow_still_all_zero_or_one
    (base : ℕ)
    (h2 : 2 ≤ base)
    (k n : ℕ)
    (hn : all_zero_or_one (Nat.digits base n))
    : all_zero_or_one (Nat.digits base ((base ^ k) * n)) := by
  induction' k with pk hpk
  · simpa
  · have := times_base_still_all_zero_or_one base h2 _ hpk
    rwa [←Nat.add_one pk, pow_succ' base pk, mul_comm (base^pk) base, mul_assoc]

lemma times_base_plus_one_still_all_zero_or_one
    (base : ℕ)
    (h2 : 2 ≤ base)
    (n : ℕ)
    (hazoo : all_zero_or_one (Nat.digits base n))
    : all_zero_or_one (Nat.digits base (1 + base * n)) := by
  rw [Nat.digits_add base h2 1 n (Nat.succ_le_iff.mp h2) (Or.inl Nat.one_ne_zero)]
  simpa[all_zero_or_one, is_zero_or_one]

lemma lemma_0 (k b : ℕ) (h2 : 2 ≤ b) :
    all_zero_or_one (b.digits (∑ i in Finset.range k, b^i)) := by
  induction' k with pk hpk
  · simp[all_zero_or_one]
  · have hh := calc
          ∑ i : ℕ in Finset.range pk.succ, b ^ i
        = ∑ i : ℕ in Finset.range pk, b ^ i.succ + b ^ 0 :=
               Finset.sum_range_succ' (λ (i : ℕ) ↦ b ^ i) pk
      _ = b ^ 0 + ∑ i in Finset.range pk, b ^ i.succ := add_comm _ _
      _ = 1 + ∑ i in Finset.range pk, b ^ i.succ := by rw [pow_zero]
      _ = 1 + ∑ i in Finset.range pk, b * b ^ i :=
          by {simp; exact Finset.sum_congr rfl (λx _ ↦ pow_succ _ _)}
      _ =  1 + b * ∑ i in Finset.range pk, b ^ i := by simp [Finset.mul_sum]
    have := times_base_plus_one_still_all_zero_or_one
               b h2
               (∑ i in Finset.range pk, b ^ i) hpk
    rwa [hh]

lemma lemma_1 (k b m: ℕ) (h2 : 2 ≤ b) :
    all_zero_or_one (b.digits (∑i in Finset.range k, b^(i + m))) := by
  have h := calc
          (∑ i in Finset.range k, b ^ (i + m))
        = (∑ i in Finset.range k, b ^ i * b ^ m) :=
             by { refine Finset.sum_congr rfl ?_; intros x _; exact pow_add b x m }
      _ = (∑ i in Finset.range k, b ^ m * b ^ i) :=
             by { refine Finset.sum_congr rfl ?_; intros x _;
                  exact mul_comm (b ^ x) (b ^ m) }
      _ = b^m * (∑ i in Finset.range k, b ^ i) := Finset.mul_sum.symm

  have := base_pow_still_all_zero_or_one b h2 m
                       (∑ i in Finset.range k, b ^ i)
                       (lemma_0 k b h2)
  rwa [h]

lemma lemma_2'''
    (c d : ℕ)
    (f: ℕ → ℕ) :
    (∑ i in Finset.range c, f (i + d)) + (∑ i in Finset.range d, f i)  =
     ∑ i in Finset.range (c+d), f i := by
  induction' c with pc hpc
  · simp
  · have h1 : ∑ i in Finset.range pc.succ, f (i + d) =
              ∑ i in Finset.range pc, f (i + d) + f (pc + d) :=
         Finset.sum_range_succ (λ (x : ℕ) ↦ f (x + d)) pc

    have h2 := calc
          ∑ i in Finset.range (pc.succ + d), f i
        = ∑ i in Finset.range (pc + d).succ, f i        := by rw [Nat.succ_add]
      _ = ∑ i in Finset.range (pc + d), f i + f (pc + d) := Finset.sum_range_succ f _

    linarith

lemma lemma_2'
    (a b : ℕ)
    (hlt : a < b)
    (f : ℕ → ℕ) :
    (∑ i in Finset.range (b - a), f (i + a)) + (∑ i in Finset.range a, f i)  =
       ∑ i in Finset.range b, f i := by
  have := lemma_2''' (b - a) a f
  rwa [Nat.sub_add_cancel (le_of_lt hlt)] at this

lemma lemma_2_aux (n a b c: ℕ) (hc : a + b = c) (hab: a % n = c % n) : b % n = 0 := by
  rw [show a = a + 0 by rfl, ←hc] at hab
  exact (Nat.ModEq.add_left_cancel' _ hab).symm

lemma lemma_2
    (n : ℕ)
    (a b : ℕ)
    (hlt : a < b)
    (hab : (∑ i in Finset.range a, 10^i) % n = (∑ i in Finset.range b, 10^i) % n) :
    (∑ i in Finset.range (b - a), 10^(i + a)) % n = 0 := by
  have h1 := lemma_2' a b hlt (λi ↦ 10^i)
  refine' lemma_2_aux n _ (∑ i in Finset.range (b - a), 10^(i + a)) _ _ hab
  rwa [add_comm]

lemma lemma_3 {a n : ℕ} (ha : 0 < a) (hm : a % n = 0) : (∃ k : ℕ+, a = n * k) := by
  obtain ⟨k', hk'⟩ := exists_eq_mul_right_of_dvd (Nat.dvd_of_mod_eq_zero hm)
  have hkp : 0 < k' := lt_of_mul_lt_mul_left' (hk' ▸ ha)
  exact ⟨⟨k', hkp⟩, hk'⟩

lemma two_le_ten : (2 : ℕ) ≤ 10 := tsub_eq_zero_iff_le.mp rfl

--
-- Prove that n has a positive multiple whose representation contains only zeroes and ones.
--
theorem zeroes_and_ones (n : ℕ) : ∃ k : ℕ+, all_zero_or_one (Nat.digits 10 (n * k)) := by
  obtain (hn0 : n = 0 ) | (hn : n > 0) := Nat.eq_zero_or_pos n
  · use 1; rw [hn0]; simp[all_zero_or_one]
  obtain ⟨a, b, hlt, hab⟩ := pigeonhole n (λm ↦ map_mod n hn (ones 10) m)
  have h' : (∑ i in Finset.range (b - a), 10^(i + a)) % n = 0 :=
    lemma_2 n a b hlt (Fin.mk.inj hab)
  have ha : 0 < ∑ i in Finset.range (b - a), 10^(i + a) := by
    have hm : 0 < b - a := Nat.sub_pos_of_lt hlt
    have hp : 0 < 10 ^ (0 + a) := pow_pos (Nat.succ_pos _) _
    exact Finset.sum_pos' (λ _ _ ↦ Nat.zero_le _) ⟨0, Finset.mem_range.mpr hm, hp⟩

  obtain ⟨k, hk⟩ := lemma_3 ha h'
  use k
  rw [←hk]
  exact lemma_1 (b - a) 10 a two_le_ten

def is_one_or_two : ℕ → Prop
| 1 => True
| 2 => True
| _ => False

def all_one_or_two (l : List ℕ) : Prop := ∀ e ∈ l, is_one_or_two e

def prepend_one (n : ℕ) := 10 ^ (List.length (Nat.digits 10 n)) + n

lemma prepend_one_pos (n: ℕ) : 0 < prepend_one n := by
  cases' n
  · norm_num
  · rw[prepend_one]; norm_num

lemma digits_len' (n : ℕ) (hn : 0 < n) :
      List.length (Nat.digits 10 n) = 1 + List.length (Nat.digits 10 (n / 10)) := by
  rw[Nat.digits_def' two_le_ten hn, List.length]
  exact add_comm _ _

lemma prepend_one_div (n : ℕ) (hn : 0 < n) : prepend_one n / 10 = prepend_one (n / 10) := by
  rw[prepend_one, prepend_one]
  cases' n with n
  · exact (Nat.lt_asymm hn hn).elim
  · rw[digits_len' n.succ (Nat.succ_pos n)]
    rw[pow_add, pow_one, add_comm]
    rw [Nat.add_mul_div_left _ _ (Nat.succ_pos 9)]
    exact add_comm _ _

lemma prepend_one_mod (n : ℕ) (hn : 0 < n) : prepend_one n % 10 = n % 10 := by
  rw[prepend_one]
  rw[Nat.digits_len _ _ two_le_ten (ne_of_gt hn)]
  rw[pow_add, pow_one]
  exact Nat.mul_add_mod _ 10 n

lemma prepend_one_eq_append (n : ℕ) :
    Nat.digits 10 (prepend_one n) = (Nat.digits 10 n) ++ [1] := by
  induction' n using Nat.strong_induction_on with n' ih
  cases' n' with n'
  · simp[prepend_one]
  · rw[Nat.digits_def' two_le_ten (prepend_one_pos _)]
    rw[prepend_one_div _ (Nat.succ_pos n')]
    have hns : n'.succ / 10 < n'.succ := Nat.div_lt_self' n' 8
    rw[ih _ hns]
    rw[←List.cons_append]
    rw[prepend_one_mod _ (Nat.succ_pos _), Nat.digits_def' two_le_ten (Nat.succ_pos n')]

lemma prepend_one_all_one_or_two (n : ℕ) (hn : all_one_or_two (Nat.digits 10 n)) :
    all_one_or_two (Nat.digits 10 (prepend_one n)) := by
 rw[prepend_one_eq_append, all_one_or_two]
 rw[all_one_or_two] at hn
 intros e he
 rw[List.mem_append] at he
 cases' he with he he
 · exact hn e he
 · rw[List.mem_singleton] at he
   simp only [he, is_one_or_two]

def prepend_two (n : ℕ) := 2 * (10 ^ (List.length (Nat.digits 10 n))) + n

lemma prepend_two_pos (n: ℕ) : 0 < prepend_two n := by
  cases n
  · norm_num
  · rw[prepend_two]; norm_num

lemma prepend_two_div (n : ℕ) (hn : 0 < n) : prepend_two n / 10 = prepend_two (n / 10) := by
  rw[prepend_two, prepend_two]
  cases' n with n
  · cases Nat.lt_asymm hn hn
  · rw[digits_len' n.succ (Nat.succ_pos n)]
    rw[pow_add, pow_one, add_comm]
    rw[←mul_left_comm]
    rw [Nat.add_mul_div_left _ _ (Nat.succ_pos 9)]
    exact add_comm _ _

lemma prepend_two_mod (n : ℕ) (hn : 0 < n) : prepend_two n % 10 = n % 10 := by
  rw[prepend_two]
  rw[Nat.digits_len _ _ two_le_ten (ne_of_gt hn)]
  rw[pow_add, pow_one, ←mul_assoc]
  exact Nat.mul_add_mod _ 10 n

lemma prepend_two_eq_append (n : ℕ) :
    Nat.digits 10 (prepend_two n) = (Nat.digits 10 n) ++ [2] := by
  induction' n using Nat.strong_induction_on with n' ih
  cases' n' with n'
  · simp[prepend_two]
  · rw[Nat.digits_def' two_le_ten (prepend_two_pos _)]
    rw[prepend_two_div _ (Nat.succ_pos n')]
    have hns : n'.succ / 10 < n'.succ := Nat.div_lt_self' n' 8
    rw[ih _ hns]
    rw[←List.cons_append]
    rw[prepend_two_mod _ (Nat.succ_pos _), ←Nat.digits_def' two_le_ten (Nat.succ_pos n')]

lemma prepend_two_all_one_or_two (n : ℕ) (hn : all_one_or_two (Nat.digits 10 n)) :
    all_one_or_two (Nat.digits 10 (prepend_two n)) := by
  rw[prepend_two_eq_append, all_one_or_two]
  rw[all_one_or_two] at hn
  intros e he
  rw[List.mem_append] at he
  cases' he with he he
  · exact hn e he
  · rw[List.mem_singleton] at he
    simp only [he, is_one_or_two]

lemma factor_ten_pow (k : ℕ) : 10 ^ k = (2^k) * (5^k) := by
  induction' k with k' ih
  · simp only [pow_zero, mul_one]
  · rw[pow_succ, pow_succ, pow_succ, ih]; ring

lemma even_5_pow_plus_one (n : ℕ) : 2 ∣ 5 ^ n + 1 := by
  apply Nat.dvd_of_mod_eq_zero
  rw[Nat.add_mod, Nat.pow_mod]
  norm_num

lemma ones_and_twos_aux (n : ℕ) :
  ∃ k : ℕ+, (List.length (Nat.digits 10 (2^n.succ * k)) = n.succ) ∧
             all_one_or_two (Nat.digits 10 (2^n.succ * k)) := by
  induction' n with pn hpn
  · use 1
    simp[all_one_or_two]
    constructor
    · norm_cast
    · intros a ha
      norm_cast
  obtain ⟨pk, hpk1, hpk2⟩ := hpn

  /-
    Adding a 1 or a 2 to the front of 2^pn.succ * pk increments it by 2^pn.succ * 5^pn.succ or
    by 2^{pn.succ+1} * 5^pn.succ, in each case preserving divisibility by 2^pn.succ. Since the
    two choices differ by 2^pn.succ * 5^pn.succ, one of them must actually achieve
    divisibility by 2^{pn.succ+1}.
  -/

  obtain ⟨t, ht : ↑pk = t + t⟩ | ⟨t, ht : ↑pk = 2 * t + 1⟩ := (pk : ℕ).even_or_odd
  · -- Even case. Prepend 2.
    rw[← two_mul] at ht
    have hd : 2 ^ pn.succ.succ ∣ prepend_two (2 ^ pn.succ * ↑pk) := by
      rw [prepend_two, factor_ten_pow, hpk1, ht]
      have hr : 2 * (2 ^ pn.succ * 5 ^ pn.succ) + 2 ^ pn.succ * (2 * t) =
                   2 ^ pn.succ.succ * (5 ^ pn.succ + t) := by
        repeat rw[pow_succ]; ring_nf
      rw[hr]
      exact Dvd.intro (5 ^ Nat.succ pn + t) rfl
    obtain ⟨k', hk'⟩ := hd
    have hkp': 0 < k' := by
      cases' k'
      · exfalso
        have hzz := prepend_two_pos (2 ^ pn.succ * ↑pk)
        rw[Nat.mul_zero] at hk'
        linarith
      · exact Nat.succ_pos _
    use ⟨k', hkp'⟩
    rw[PNat.mk_coe, ←hk']
    constructor
    · rw[prepend_two_eq_append]
      rw [List.length_append, List.length_singleton, hpk1]
    · exact prepend_two_all_one_or_two _ hpk2
  · -- Odd case. Prepend 1.
    have hd : 2 ^ pn.succ.succ ∣ prepend_one (2 ^ pn.succ * ↑pk) := by
      rw[prepend_one, hpk1, factor_ten_pow, ht]
      have h5 : 2 ^ pn.succ * 5 ^ pn.succ + 2 ^ pn.succ * (2 * t + 1) =
            2^pn.succ * (2 * (2 * 5 ^ pn + t) + (5^pn + 1)) := by
        repeat rw[pow_succ]; ring_nf
      rw[h5]
      obtain ⟨k5,hk5⟩:= even_5_pow_plus_one pn
      rw[hk5]
      have h5' : 2 ^ pn.succ * (2 * (2 * 5 ^ pn + t) + 2 * k5) =
           2^pn.succ.succ * (2 * 5 ^ pn + t + k5) := by
        repeat rw[pow_succ]; ring_nf
      rw[h5']
      exact Dvd.intro (2 * 5 ^ pn + t + k5) rfl
    obtain ⟨k', hk'⟩ := hd
    have hkp': 0 < k' := by
      cases k'
      · exfalso
        have hzz := prepend_one_pos (2 ^ pn.succ * ↑pk)
        rw[Nat.mul_zero] at hk'
        linarith
      · exact Nat.succ_pos _
    use ⟨k', hkp'⟩
    rw[PNat.mk_coe,←hk']
    constructor
    · rw [prepend_one_eq_append]
      rw [List.length_append, List.length_singleton, hpk1]
    · exact prepend_one_all_one_or_two _ hpk2

--
-- Prove that 2^n has a positive multiple whose representation contains only ones and twos.
--
theorem ones_and_twos (n : ℕ) : ∃ k : ℕ+, all_one_or_two (Nat.digits 10 (2^n * k)) := by
  cases' n with n
  · use 1; simp[all_one_or_two]; norm_cast
  · obtain ⟨k, _, hk2⟩ := ones_and_twos_aux n
    exact ⟨k, hk2⟩
