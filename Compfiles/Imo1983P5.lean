/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InternLM-MATH LEAN Formalizer v0.1, Benpigchu
-/

import Mathlib.Data.List.GetD
import Mathlib.Tactic

import ProblemExtraction

set_option backward.isDefEq.respectTransparency false

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Olympiad 1983, Problem 5

Is it possible to choose $1983$ distinct positive integers,
all less than or equal to $10^5$,
no three of which are consecutive terms of an arithmetic progression?
Justify your answer.
-/

namespace Imo1983P5

snip begin

lemma Nat.ofDigits_eq (b : ℕ) (L : List ℕ)
    : Nat.ofDigits b L = ∑ i ∈ Finset.range L.length, (L.getI i) * b ^ i := by
  induction L with
  | nil => simp
  | cons d L' h =>
    simp only [Nat.ofDigits_cons, List.length_cons, Finset.sum_range_succ',
               List.getI_cons_zero, pow_zero, mul_one, List.getI_cons_succ]
    rw [h, add_comm, mul_comm, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl fun i _ ↦ by ring

lemma Nat.getI_digits_lt (n i : ℕ) {b : ℕ} (h : 2 ≤ b) : (b.digits n).getI i < b := by
  simp only [← List.getD_default_eq_getI, Nat.default_eq_zero, Nat.getD_digits n i h]
  exact Nat.mod_lt _ (by lia)

lemma Nat.getI_digits_add (m n : ℕ) {b : ℕ} (hb : 2 ≤ b)
  (h : ∀ i : ℕ, (b.digits m).getI i + (b.digits n).getI i < b)
  : ∀ i : ℕ, (b.digits m).getI i  + (b.digits n).getI i = (b.digits (m + n)).getI i := by
  induction' m using Nat.strong_induction_on with m h' generalizing n
  by_cases! h'' : m = 0 ∨ n = 0
  · rcases h'' with rfl | rfl <;> simp [Nat.digits_zero, List.getI_nil]
  · rw [Nat.ne_zero_iff_zero_lt, Nat.ne_zero_iff_zero_lt] at h''
    rw [Nat.digits_of_two_le_of_pos hb h''.left] at h ⊢
    rw [Nat.digits_of_two_le_of_pos hb h''.right] at h ⊢
    have hmn : 0 < m + n := add_pos h''.left h''.right
    rw [Nat.digits_of_two_le_of_pos hb hmn]
    have h0 := h 0
    rw [List.getI_cons_zero, List.getI_cons_zero] at h0
    intro i
    by_cases! hi : i = 0
    · rw [hi, List.getI_cons_zero, List.getI_cons_zero, List.getI_cons_zero]
      exact (Nat.add_mod_of_add_mod_lt h0).symm
    · rcases Nat.exists_eq_succ_of_ne_zero hi with ⟨i', hi'⟩
      rw [hi', List.getI_cons_succ, List.getI_cons_succ, List.getI_cons_succ]
      have hm' : m / b < m := Nat.div_lt_self h''.left (by lia)
      have h'mn : ∀ (i : ℕ), (b.digits (m / b)).getI i + (b.digits (n / b)).getI i < b := by
        intro i
        rw [← List.getI_cons_succ (m / b)]
        nth_rw 2 [← List.getI_cons_succ (n / b)]
        exact h (i + 1)
      have h'm'n' := h' (m / b) hm' (n / b) h'mn
      rw [h'm'n' i']
      congr
      exact (Nat.add_div_eq_of_add_mod_lt h0).symm

lemma Nat.eq_iff_getI_digits_eq (m n b: ℕ)
  : m = n ↔ (∀ i : ℕ, (b.digits m).getI i  = (b.digits n).getI i) := by
  constructor
  · intro hmn i
    rw [hmn]
  · intro h
    rw [← Nat.ofDigits_digits b m, ← Nat.ofDigits_digits b n]
    rw [Nat.ofDigits_eq, Nat.ofDigits_eq]
    rw [← Finset.sdiff_union_inter (Finset.range (b.digits m).length) (Finset.range (b.digits n).length)]
    nth_rw 3 [← Finset.sdiff_union_inter (Finset.range (b.digits n).length) (Finset.range (b.digits m).length)]
    rw [Finset.sum_union (Finset.disjoint_sdiff_inter _ _)]
    rw [Finset.sum_union (Finset.disjoint_sdiff_inter _ _)]
    have h₁ : ∀ i ∈ Finset.range (b.digits m).length \ Finset.range (b.digits n).length,
      (b.digits m).getI i * b ^ i = 0 := by
      intro i hi
      rw [h i]
      apply mul_eq_zero_of_left
      rw [← Nat.default_eq_zero]
      apply List.getI_eq_default
      rw [Finset.mem_sdiff, Finset.mem_range, Finset.mem_range, not_lt] at hi
      exact hi.right
    have h₂ : ∀ i ∈ Finset.range (b.digits n).length \ Finset.range (b.digits m).length,
      (b.digits n).getI i * b ^ i = 0 := by
      intro i hi
      rw [← h i]
      apply mul_eq_zero_of_left
      rw [← Nat.default_eq_zero]
      apply List.getI_eq_default
      rw [Finset.mem_sdiff, Finset.mem_range, Finset.mem_range, not_lt] at hi
      exact hi.right
    rw [Finset.sum_eq_zero h₁, Finset.sum_eq_zero h₂, zero_add, zero_add]
    apply Finset.sum_congr (Finset.inter_comm _ _)
    intro i hi
    rw [h i]

def base_two_to_base_three (n : ℕ) := Nat.ofDigits 3 (Nat.digits 2 n)

lemma digits_base_two_to_base_three (n : ℕ)
    : Nat.digits 2 n = Nat.digits 3 (base_two_to_base_three n) := by
  symm; rw [base_two_to_base_three]; apply Nat.digits_ofDigits
  · norm_num
  · exact fun l hl => lt_trans (Nat.digits_lt_base (by norm_num) hl) (by norm_num)
  · exact fun h => Nat.getLast_digit_ne_zero 2 (Nat.digits_ne_nil_iff_ne_zero.mp h)

lemma base_two_to_base_three_inj : Function.Injective base_two_to_base_three := fun m n hmn =>
  Nat.digits_inj_iff.mp (by rw [digits_base_two_to_base_three, digits_base_two_to_base_three, hmn])

lemma base_two_to_base_three_zero : base_two_to_base_three 0 = 0 := rfl

lemma base_two_to_base_three_pos {m : ℕ} (hm : 0 < m) : 0 < base_two_to_base_three m :=
  Nat.pos_of_ne_zero (base_two_to_base_three_zero ▸ base_two_to_base_three_inj.ne hm.ne')

def zero_or_one_in_base_three (n : ℕ) :=
  ∀ i : ℕ, (Nat.digits 3 n).getI i = 0 ∨ (Nat.digits 3 n).getI i = 1

lemma zero_or_one_in_base_three_of_eq_base_two_to_base_three
  {m n : ℕ} (hmn : base_two_to_base_three n = m)
  : zero_or_one_in_base_three m := by
  rw [← hmn, zero_or_one_in_base_three]
  intro i
  rw [← Nat.le_one_iff_eq_zero_or_eq_one, ← digits_base_two_to_base_three]
  rw [← Nat.lt_succ_iff]
  apply Nat.getI_digits_lt
  rfl

lemma eq_iff_of_zero_or_one_in_base {m n : ℕ} (hm : zero_or_one_in_base_three m) (hn : zero_or_one_in_base_three n)
  : (∀ i : ℕ, (Nat.digits 3 (m + n)).getI i = 0 ∨ (Nat.digits 3 (m + n)).getI i = 2)
    ↔ m = n := by
    rw [zero_or_one_in_base_three] at hm hn
    rw [Nat.eq_iff_getI_digits_eq m n 3]
    have h : ∀ i : ℕ, (Nat.digits 3 m).getI i + (Nat.digits 3 n).getI i < 3 := fun i ↦ by
      have := hm i; have := hn i; lia
    apply Nat.getI_digits_add _ _ (by norm_num) at h
    constructor <;> intro h' i
    · have := hm i; have := hn i; have := h i; have := h' i; lia
    · have := hn i; have := h i; have := h' i; lia

theorem generalized (n : ℕ+) :
  ∃ S : Finset ℕ+, S.card = 2 ^ n.val - 1 ∧
  (∀ x ∈ S, x.val ≤ (3 ^ n.val - 1) / 2) ∧
  ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x < y ∧ y < z → x + z ≠ 2 * y := by
  set S' := Finset.image base_two_to_base_three (Finset.range (2 ^ n.val) \ Finset.range 1) with hS'
  use Finset.subtype (fun n ↦ 0 < n) S'
  constructorm* _ ∧ _
  · rw [Finset.card_subtype]
    have hS'_filter : ∀ n ∈ S', 0 < n := by
      simp only [hS', Finset.mem_image, Finset.mem_sdiff, Finset.mem_range, Nat.lt_one_iff,
                 forall_exists_index, and_imp]
      intro _ m _ hm0 rfl
      exact base_two_to_base_three_pos (Nat.pos_of_ne_zero hm0)
    rw [Finset.card_filter_eq_iff.mpr hS'_filter, Finset.card_image_of_injective _ base_two_to_base_three_inj]
    rw [Finset.card_sdiff, Finset.range_inter_range, Finset.card_range, Finset.card_range]
    congr 1
    exact min_eq_left (Nat.one_le_pow _ _ (by norm_num))
  · intro x hx
    rw [Finset.mem_subtype, hS', Finset.mem_image] at hx
    rcases hx with ⟨m, hm, hmx⟩
    rw [PNat.val, ← hmx, base_two_to_base_three, Nat.ofDigits_eq]
    have h' : ∀ i ∈ Finset.range (Nat.digits 2 m).length, (Nat.digits 2 m).getI i * 3 ^ i ≤ 3 ^ i := by
      intro i _; nth_rw 2 [← one_mul (3 ^ i)]
      exact Nat.mul_le_mul_right _ (Nat.lt_succ_iff.mp (Nat.getI_digits_lt (b := 2) m i le_rfl))
    apply le_trans (Finset.sum_le_sum h')
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    zify
    nth_rw 2 [(by norm_num : (2 : ℤ) = 3 - 1)]
    rw [geom_sum_mul, Nat.cast_sub (Nat.one_le_pow _ 3 (by norm_num)), Nat.cast_one]
    rw [sub_le_sub_iff_right]
    push_cast
    rw [pow_le_pow_iff_right₀ (by norm_num), Nat.digits_length_le_iff (by norm_num)]
    rw [Finset.mem_sdiff, Finset.mem_range] at hm
    exact hm.left
  · rintro x hx y hy z hz h'
    contrapose! h'
    rw [Finset.mem_subtype, hS', Finset.mem_image] at hx hy hz
    rcases hx with ⟨x', hx', hx'x⟩
    rcases hy with ⟨y', hy', hy'y⟩
    rcases hz with ⟨z', hz', hz'z⟩
    rw [← PNat.coe_inj] at h'
    rw [← PNat.coe_lt_coe, ← PNat.coe_le_coe]
    push_cast at h'
    rw [two_mul] at h'
    rw [PNat.val] at h' ⊢
    apply zero_or_one_in_base_three_of_eq_base_two_to_base_three at hx'x
    apply zero_or_one_in_base_three_of_eq_base_two_to_base_three at hy'y
    apply zero_or_one_in_base_three_of_eq_base_two_to_base_three at hz'z
    have hzx : Subtype.val x = Subtype.val z := by
      rw [← eq_iff_of_zero_or_one_in_base hx'x hz'z, h']
      rw [eq_iff_of_zero_or_one_in_base hy'y hy'y]
    rw [hzx]
    apply le_of_lt

snip end

problem imo1983_p5 :
  ∃ S : Finset ℕ+, S.card = 1983 ∧
  (∀ x ∈ S, x ≤ 10^5) ∧
  ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x < y ∧ y < z → x + z ≠ 2 * y := by
  rcases generalized 11 with ⟨S', hS'₁, hS'₂, hS'₃⟩
  have h : 1983 ≤ S'.card := by rw [hS'₁]; norm_num
  rcases Finset.exists_subset_card_eq h with ⟨S, hS₁, hS₂⟩
  use S
  constructorm* _ ∧ _
  · exact hS₂
  · exact fun x hx ↦ by rw [← PNat.coe_le_coe]; exact le_trans (hS'₂ x (hS₁ hx)) (by norm_num)
  · exact fun x hx y hy z hz ↦ hS'₃ x (hS₁ hx) y (hS₁ hy) z (hS₁ hz)


end Imo1983P5
