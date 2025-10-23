/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
(From Mathematical Puzzles: A Connoisseur's Collection by Peter Winkler.)

Let n be a natural number. Prove that

  (a) n has a (nonzero) multiple whose representation in base 10 contains
      only zeroes and ones; and
  (b) 2^n has a multiple whose representation contains only ones and twos.
-/

namespace ZerosOnesAndTwos

snip begin

def ones (b : ℕ) : ℕ → ℕ
| k => Nat.ofDigits b (List.replicate k 1)

lemma ones_add (b m n : ℕ) :
    ones b (m + n) = ones b m + Nat.ofDigits b ((List.replicate m 0) ++ (List.replicate n 1)) := by
  unfold ones; dsimp only
  rw [List.replicate_add, Nat.ofDigits_append, Nat.ofDigits_append]
  rw [List.length_replicate, List.length_replicate, Nat.ofDigits_replicate_zero, zero_add]

def map_mod (n : ℕ) (hn : 0 < n) (f : ℕ → ℕ) : ℕ → Fin n
| m => ⟨f m % n, Nat.mod_lt (f m) hn⟩

lemma pigeonhole (n : ℕ) (f : ℕ → Fin n) :
  ∃ a b : ℕ, a < b ∧ f a = f b :=
let ⟨a, b, hne, hfe⟩ := Finite.exists_ne_map_eq_of_infinite f
hne.lt_or_gt.elim (fun h ↦ ⟨a, b, h, hfe⟩) (fun h ↦ ⟨b, a, h, hfe.symm⟩)

lemma lemma_3 {a n : ℕ} (ha : 0 < a) (hm : a % n = 0) : (∃ k : ℕ+, a = n * k) := by
  obtain ⟨k', hk'⟩ := exists_eq_mul_right_of_dvd (Nat.dvd_of_mod_eq_zero hm)
  have hkp : 0 < k' := lt_of_mul_lt_mul_left' (hk' ▸ ha)
  exact ⟨⟨k', hkp⟩, hk'⟩

lemma two_le_ten : (2 : ℕ) ≤ 10 := tsub_eq_zero_iff_le.mp rfl
lemma one_lt_ten : (2 : ℕ) ≤ 10 := tsub_eq_zero_iff_le.mp rfl
lemma one_le_ten : (1 : ℕ) ≤ 10 := tsub_eq_zero_iff_le.mp rfl

snip end

problem zeroes_and_ones
    (n : ℕ) : ∃ k : ℕ+, ∀ e ∈ Nat.digits 10 (n * k), e = 0 ∨ e = 1 := by
  obtain (hn0 : n = 0 ) | (hn : n > 0) := Nat.eq_zero_or_pos n
  · use 1; rw [hn0]; simp
  obtain ⟨a, b, hlt, hab⟩ := pigeonhole n (fun m ↦ map_mod n hn (ones 10) m)
  dsimp [map_mod] at hab
  replace hab : ones 10 b % n = ones 10 a % n := (Fin.mk_eq_mk.mp hab).symm
  change ones 10 b ≡ ones 10 a [MOD n] at hab

  have hab2 := ones_add 10 a (b-a)
  rw [Nat.add_sub_of_le (Nat.le_of_lt hlt)] at hab2
  rw [hab2] at hab; clear hab2
  have hab' : (Nat.ofDigits 10 ((List.replicate a 0) ++ (List.replicate (b-a) 1))) ≡ 0 [MOD n] :=
    Nat.ModEq.add_left_cancel (Nat.ModEq.symm hab) rfl

  obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le' (Nat.sub_pos_of_lt hlt)
  have h8 : 0 < Nat.ofDigits 10 (List.replicate a 0 ++ List.replicate (b - a) 1) := by
    rw [hc, List.replicate_succ]
    calc 0 < 1 := zero_lt_one
         _ ≤ List.sum (List.replicate a 0 ++ 1 :: List.replicate c 1) := by simp
         _ ≤ Nat.ofDigits 10 (List.replicate a 0 ++ 1 :: List.replicate c 1) :=
                          Nat.sum_le_ofDigits _ one_le_ten

  obtain ⟨k, hk⟩ := lemma_3 h8 hab'
  use k
  rw [←hk]
  have h4 : ∀ (l : ℕ), l ∈ List.replicate a 0 ++ List.replicate (b - a) 1 → l < 10 := by
    intro l hl
    rw [List.mem_append, List.mem_replicate, List.mem_replicate] at hl
    omega
  have h5 : ∀ (h : List.replicate a 0 ++ List.replicate (b - a) 1 ≠ []),
      List.getLast (List.replicate a 0 ++ List.replicate (b - a) 1) h ≠ 0 := by
    rw [hc] at *
    intro h6
    have h7 : List.replicate (c+1) 1 ≠ [] := List.getLast?_isSome.mp rfl
    have := List.getLast_append_of_right_ne_nil (List.replicate a 0) _ h7
    rw [this, List.getLast_replicate_succ]
    exact Nat.one_ne_zero
  rw [Nat.digits_ofDigits _ one_lt_ten _ h4 h5]
  intro e he
  rw [List.mem_append, List.mem_replicate, List.mem_replicate] at he
  omega

snip begin

abbrev all_one_or_two (l : List ℕ) : Prop := ∀ e ∈ l, e = 1 ∨ e = 2

def prepend_one (n : ℕ) := 10 ^ (List.length (Nat.digits 10 n)) + n

lemma prepend_one_pos (n : ℕ) : 0 < prepend_one n := by
  cases n
  · simp [prepend_one]
  · rw [prepend_one]; norm_num

lemma digits_len' (n : ℕ) (hn : 0 < n) :
      List.length (Nat.digits 10 n) = 1 + List.length (Nat.digits 10 (n / 10)) := by
  rw [Nat.digits_def' two_le_ten hn, List.length]
  exact add_comm _ _

lemma prepend_one_div (n : ℕ) (hn : 0 < n) : prepend_one n / 10 = prepend_one (n / 10) := by
  rw [prepend_one, prepend_one]
  cases n with
  | zero => exact (Nat.lt_asymm hn hn).elim
  | succ n =>
    rw [digits_len' n.succ (Nat.succ_pos n)]
    rw [pow_add, pow_one, add_comm]
    rw [Nat.add_mul_div_left _ _ (Nat.succ_pos 9)]
    exact add_comm _ _

lemma prepend_one_mod (n : ℕ) (hn : 0 < n) : prepend_one n % 10 = n % 10 := by
  rw [prepend_one]
  rw [Nat.digits_len _ _ two_le_ten (ne_of_gt hn)]
  omega

lemma prepend_one_eq_append (n : ℕ) :
    Nat.digits 10 (prepend_one n) = (Nat.digits 10 n) ++ [1] := by
  induction n using Nat.strong_induction_on with | h n' ih =>
  cases n' with
  | zero => simp +arith +decide
  | succ n' =>
    rw [Nat.digits_def' two_le_ten (prepend_one_pos _)]
    rw [prepend_one_div _ (Nat.succ_pos n')]
    have hns : n'.succ / 10 < n'.succ := Nat.div_lt_self' n' 8
    rw [ih _ hns]
    rw [←List.cons_append]
    rw [prepend_one_mod _ (Nat.succ_pos _), Nat.digits_def' two_le_ten (Nat.succ_pos n')]

lemma prepend_one_all_one_or_two (n : ℕ) (hn : all_one_or_two (Nat.digits 10 n)) :
    all_one_or_two (Nat.digits 10 (prepend_one n)) := by
 rw [prepend_one_eq_append, all_one_or_two]
 rw [all_one_or_two] at hn
 intro e he
 rw [List.mem_append] at he
 obtain he | he := he
 · exact hn e he
 · rw [List.mem_singleton] at he
   simp only [he, OfNat.one_ne_ofNat, or_false]

def prepend_two (n : ℕ) := 2 * (10 ^ (List.length (Nat.digits 10 n))) + n

lemma prepend_two_pos (n : ℕ) : 0 < prepend_two n := by
  cases n
  · norm_num [prepend_two]
  · rw [prepend_two]; norm_num

lemma prepend_two_div (n : ℕ) (hn : 0 < n) : prepend_two n / 10 = prepend_two (n / 10) := by
  rw [prepend_two, prepend_two]
  cases n with
  | zero => cases Nat.lt_asymm hn hn
  | succ n =>
    rw [digits_len' n.succ (Nat.succ_pos n)]
    cutsat

lemma prepend_two_mod (n : ℕ) (hn : 0 < n) : prepend_two n % 10 = n % 10 := by
  rw [prepend_two]
  rw [Nat.digits_len _ _ two_le_ten (ne_of_gt hn)]
  omega

lemma prepend_two_eq_append (n : ℕ) :
    Nat.digits 10 (prepend_two n) = (Nat.digits 10 n) ++ [2] := by
  induction n using Nat.strong_induction_on with | h n' ih =>
  cases n' with
  | zero => norm_num [prepend_two]
  | succ n' =>
    rw [Nat.digits_def' two_le_ten (prepend_two_pos _)]
    rw [prepend_two_div _ (Nat.succ_pos n')]
    have hns : n'.succ / 10 < n'.succ := Nat.div_lt_self' n' 8
    rw [ih _ hns]
    rw [←List.cons_append]
    rw [prepend_two_mod _ (Nat.succ_pos _), ←Nat.digits_def' two_le_ten (Nat.succ_pos n')]

lemma prepend_two_all_one_or_two (n : ℕ) (hn : all_one_or_two (Nat.digits 10 n)) :
    all_one_or_two (Nat.digits 10 (prepend_two n)) := by
  rw [prepend_two_eq_append, all_one_or_two]
  rw [all_one_or_two] at hn
  intro e he
  rw [List.mem_append] at he
  obtain he | he := he
  · exact hn e he
  · rw [List.mem_singleton] at he
    right; exact he

lemma factor_ten_pow (k : ℕ) : 10 ^ k = (2^k) * (5^k) := by
  induction k with
  | zero => simp only [pow_zero, mul_one]
  | succ k' ih => rw [pow_succ, pow_succ, pow_succ, ih]; ring

lemma even_5_pow_plus_one (n : ℕ) : 2 ∣ 5 ^ n + 1 := by
  apply Nat.dvd_of_mod_eq_zero
  rw [Nat.add_mod, Nat.pow_mod]
  norm_num

lemma ones_and_twos_aux (n : ℕ) :
  ∃ k : ℕ+, (List.length (Nat.digits 10 (2^n.succ * k)) = n.succ) ∧
             all_one_or_two (Nat.digits 10 (2^n.succ * k)) := by
  induction n with
  | zero =>
    use 1
    norm_num [all_one_or_two]
  | succ pn hpn =>
  obtain ⟨pk, hpk1, hpk2⟩ := hpn

  /-
    Adding a 1 or a 2 to the front of 2^pn.succ * pk increments it by 2^pn.succ * 5^pn.succ or
    by 2^{pn.succ+1} * 5^pn.succ, in each case preserving divisibility by 2^pn.succ. Since the
    two choices differ by 2^pn.succ * 5^pn.succ, one of them must actually achieve
    divisibility by 2^{pn.succ+1}.
  -/

  obtain ⟨t, ht : ↑pk = t + t⟩ | ⟨t, ht : ↑pk = 2 * t + 1⟩ := (pk : ℕ).even_or_odd
  · -- Even case. Prepend 2.
    rw [← two_mul] at ht
    have hd : 2 ^ pn.succ.succ ∣ prepend_two (2 ^ pn.succ * ↑pk) := by
      rw [prepend_two, factor_ten_pow, hpk1, ht]
      have hr : 2 * (2 ^ pn.succ * 5 ^ pn.succ) + 2 ^ pn.succ * (2 * t) =
                   2 ^ pn.succ.succ * (5 ^ pn.succ + t) := by
        repeat rw [pow_succ]; ring_nf
      exact Dvd.intro (5 ^ pn.succ + t) hr.symm
    obtain ⟨k', hk'⟩ := hd
    have hkp': 0 < k' := by
      cases k'
      · have hzz := prepend_two_pos (2 ^ pn.succ * ↑pk)
        omega
      · exact Nat.succ_pos _
    use ⟨k', hkp'⟩
    rw [PNat.mk_coe, ←hk']
    constructor
    · rw [prepend_two_eq_append]
      rw [List.length_append, List.length_singleton, hpk1]
    · exact prepend_two_all_one_or_two _ hpk2
  · -- Odd case. Prepend 1.
    have hd : 2 ^ pn.succ.succ ∣ prepend_one (2 ^ pn.succ * ↑pk) := by
      rw [prepend_one, hpk1, factor_ten_pow, ht]
      have h5 : 2 ^ pn.succ * 5 ^ pn.succ + 2 ^ pn.succ * (2 * t + 1) =
            2^pn.succ * (2 * (2 * 5 ^ pn + t) + (5^pn + 1)) := by
        repeat rw[pow_succ]; ring_nf
      rw [h5]
      obtain ⟨k5,hk5⟩:= even_5_pow_plus_one pn
      rw [hk5]
      have h5' : 2 ^ pn.succ * (2 * (2 * 5 ^ pn + t) + 2 * k5) =
           2^pn.succ.succ * (2 * 5 ^ pn + t + k5) := by
        repeat rw[pow_succ]; ring_nf
      rw [h5']
      exact Dvd.intro (2 * 5 ^ pn + t + k5) rfl
    obtain ⟨k', hk'⟩ := hd
    have hkp': 0 < k' := by
      cases k'
      · have hzz := prepend_one_pos (2 ^ pn.succ * ↑pk)
        omega
      · exact Nat.succ_pos _
    use ⟨k', hkp'⟩
    rw [PNat.mk_coe,←hk']
    constructor
    · rw [prepend_one_eq_append]
      rw [List.length_append, List.length_singleton, hpk1]
    · exact prepend_one_all_one_or_two _ hpk2

snip end

problem ones_and_twos
    (n : ℕ) : ∃ k : ℕ+, ∀ e ∈ Nat.digits 10 (2^n * k), e = 1 ∨ e = 2 := by
  cases n with
  | zero => use 1; norm_num
  | succ n =>
    obtain ⟨k, _, hk2⟩ := ones_and_twos_aux n
    exact ⟨k, hk2⟩


end ZerosOnesAndTwos
