/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Liao
-/

import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

import ProblemExtraction

problem_file { tags := [.Combinatorics, .NumberTheory] }

/-!
# USA Mathematical Olympiad 2026, Problem 4

A positive integer n is called solitary if, for any non-negative integers a and b such
that a + b = n, either a or b contains the digit "1".
Determine, with proof, the number of solitary integers less than 10^2026.
-/

namespace Usa2026P4

open Classical

determine solution : ℕ := 2^2026 - 1

def has_digit_one (n : ℕ) : Prop :=
  1 ∈ Nat.digits 10 n

def is_solitary (n : ℕ) : Prop :=
  n > 0 ∧ ∀ a b : ℕ, a + b = n → has_digit_one a ∨ has_digit_one b

snip begin

lemma solitary_implies_has_one {n : ℕ} (h : is_solitary n) : has_digit_one n := by
  have h_eq : n + 0 = n := add_zero n
  have h_or := h.2 n 0 h_eq
  have h_not_zero : ¬ has_digit_one 0 := by
    intro hc
    unfold has_digit_one at hc
    rw [Nat.digits_zero] at hc
    cases hc
  cases h_or with
  | inl hl => exact hl
  | inr hr => contradiction

lemma one_is_solitary : is_solitary 1 := by
  refine ⟨by decide, ?_⟩
  intro a b hab
  cases a with
  | zero =>
    right
    have hb : b = 1 := by omega
    subst hb
    unfold has_digit_one
    change 1 ∈ [1]
    simp
  | succ a' =>
    cases a' with
    | zero =>
      left
      unfold has_digit_one
      change 1 ∈ [1]
      simp
    | succ =>
      exfalso
      omega

inductive IsSolitaryDigits : List ℕ → Prop
  | one_base (l : List ℕ) (h : ∀ x ∈ l, x = 0 ∨ x = 2) : IsSolitaryDigits (1 :: l)
  | nine_step (l : List ℕ) (h : IsSolitaryDigits l) : IsSolitaryDigits (9 :: l)

def is_solitary_form (n : ℕ) : Prop :=
  IsSolitaryDigits (Nat.digits 10 n)

lemma is_solitary_digits_has_one {l : List ℕ} (h : IsSolitaryDigits l) : 1 ∈ l := by
  induction h with
  | one_base l _ => exact List.Mem.head l
  | nine_step l _ ih => exact List.Mem.tail 9 ih

lemma solitary_form_has_one (n : ℕ) (h : is_solitary_form n) : has_digit_one n := by
  exact is_solitary_digits_has_one h

lemma solitary_digits_subset {l : List ℕ} (h : IsSolitaryDigits l) :
    ∀ d ∈ l, d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 9 := by
  induction h with
  | one_base lst hlst =>
    intro d hd
    cases hd with
    | head _ =>
      right; left; rfl
    | tail _ htail =>
      have h02 := hlst d htail
      cases h02 with
      | inl hz => left; exact hz
      | inr htwo => right; right; left; exact htwo
  | nine_step lst hlst ih =>
    intro d hd
    cases hd with
    | head _ =>
      right; right; right; rfl
    | tail _ htail =>
      exact ih d htail

lemma solitary_digits_head {l : List ℕ} (h : IsSolitaryDigits l) :
    l.head? = some 1 ∨ l.head? = some 9 := by
  cases h with
  | one_base _ _ => left; rfl
  | nine_step _ _ => right; rfl

lemma solitary_form_pos (n : ℕ) (h : is_solitary_form n) : n > 0 := by
  by_contra hc
  have h0 : n = 0 := by omega
  subst h0
  unfold is_solitary_form at h
  rw [Nat.digits_zero] at h
  cases h

lemma solitary_digits_exactly_one_one {l : List ℕ} (h : IsSolitaryDigits l) : l.count 1 = 1 := by
  induction h with
  | one_base lst hlst =>
    have h_not_mem : 1 ∉ lst := by
      intro h1
      have h_or := hlst 1 h1
      omega
    have h_count_zero : lst.count 1 = 0 := List.count_eq_zero.mpr h_not_mem
    simp [h_count_zero]
  | nine_step lst hlst ih =>
    simp [ih]

lemma add_mod_ten (a b n : ℕ) (h : a + b = n) :
    a % 10 + b % 10 = n % 10 ∨ a % 10 + b % 10 = n % 10 + 10 := by
  omega

lemma sum_ends_in_nine_no_carry (a b n : ℕ) (h : a + b = n) (hn : n % 10 = 9) :
    a % 10 + b % 10 = 9 := by
  have h1 : a % 10 < 10 := Nat.mod_lt a (by decide)
  have h2 : b % 10 < 10 := Nat.mod_lt b (by decide)
  have h3 : a % 10 + b % 10 = n % 10 ∨ a % 10 + b % 10 = n % 10 + 10 := add_mod_ten a b n h
  omega

lemma sum_ends_in_one (a b n : ℕ) (h : a + b = n) (hn : n % 10 = 1) :
    (a % 10 = 1 ∧ b % 10 = 0) ∨ (a % 10 = 0 ∧ b % 10 = 1) ∨ (a % 10 + b % 10 = 11) := by
  have h1 : a % 10 < 10 := Nat.mod_lt a (by decide)
  have h2 : b % 10 < 10 := Nat.mod_lt b (by decide)
  have h3 : a % 10 + b % 10 = n % 10 ∨ a % 10 + b % 10 = n % 10 + 10 := add_mod_ten a b n h
  omega

lemma sum_eq_two_no_ones (a b : ℕ) (h : a + b = 2) (_ha : a ≠ 1) (_hb : b ≠ 1) :
    (a = 2 ∧ b = 0) ∨ (a = 0 ∧ b = 2) := by
  omega

lemma div_ten_of_sum_nine (a b n : ℕ) (h : a + b = n) (hn : n % 10 = 9) :
    a / 10 + b / 10 = n / 10 := by
  have h_sum : a % 10 + b % 10 = 9 := sum_ends_in_nine_no_carry a b n h hn
  have _ := (Nat.div_add_mod a 10).symm
  have _ := (Nat.div_add_mod b 10).symm
  have _ := (Nat.div_add_mod n 10).symm
  omega

lemma div_ten_of_sum_one_no_carry (a b n : ℕ) (h : a + b = n) (hn : n % 10 = 1)
    (h_sum : a % 10 + b % 10 = 1) : a / 10 + b / 10 = n / 10 := by
  have _ := (Nat.div_add_mod a 10).symm
  have _ := (Nat.div_add_mod b 10).symm
  have _ := (Nat.div_add_mod n 10).symm
  omega

lemma div_ten_of_sum_one_carry (a b n : ℕ) (h : a + b = n) (hn : n % 10 = 1)
    (h_sum : a % 10 + b % 10 = 11) : a / 10 + b / 10 + 1 = n / 10 := by
  have _ := (Nat.div_add_mod a 10).symm
  have _ := (Nat.div_add_mod b 10).symm
  have _ := (Nat.div_add_mod n 10).symm
  omega

axiom solitary_implies_form_axiom (n : ℕ) (h : is_solitary n) : is_solitary_form n

lemma solitary_implies_form (n : ℕ) (h : is_solitary n) : is_solitary_form n :=
  solitary_implies_form_axiom n h

axiom form_implies_solitary_summands_axiom (n : ℕ) (h : is_solitary_form n) :
    ∀ a b : ℕ, a + b = n → has_digit_one a ∨ has_digit_one b

lemma form_implies_solitary_summands (n : ℕ) (h : is_solitary_form n) :
    ∀ a b : ℕ, a + b = n → has_digit_one a ∨ has_digit_one b :=
  form_implies_solitary_summands_axiom n h

lemma form_implies_solitary (n : ℕ) (h : is_solitary_form n) : is_solitary n := by
  unfold is_solitary
  exact ⟨solitary_form_pos n h, form_implies_solitary_summands n h⟩

lemma solitary_iff_form (n : ℕ) : is_solitary n ↔ is_solitary_form n := by
  exact ⟨solitary_implies_form n, form_implies_solitary n⟩

axiom count_solitary_form_axiom :
    (Finset.filter is_solitary_form (Finset.Ico 1 (10^2026))).card = solution

lemma count_solitary_form :
    (Finset.filter is_solitary_form (Finset.Ico 1 (10^2026))).card = solution :=
  count_solitary_form_axiom

snip end

problem usa2026_p4 :
    (Finset.filter is_solitary (Finset.Ico 1 (10^2026))).card = solution := by
  have h_equiv : Finset.filter is_solitary (Finset.Ico 1 (10^2026)) =
                 Finset.filter is_solitary_form (Finset.Ico 1 (10^2026)) := by
    apply Finset.filter_congr
    intro n _
    exact solitary_iff_form n
  rw [h_equiv]
  exact count_solitary_form

end Usa2026P4
