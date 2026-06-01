/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InternLM-MATH LEAN Formalizer v0.1, Goedel-Prover-V2
-/

import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.List.Palindrome
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Set.Card

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 1988, Problem 3

A function $f$ defined on the positive integers (and taking positive integers values) is given by:
f(1) = 1
f(3) = 3
f(2 \cdot n) = f(n)
f(4 \cdot n + 1) = 2 \cdot f(2 \cdot n + 1) - f(n)
f(4 \cdot n + 3) = 3 \cdot f(2 \cdot n + 1) - 2 \cdot f(n)
for all positive integers $n.$
Determine with proof the number of positive integers $\leq 1988$ for which $f(n) = n.$
-/

namespace Imo1988P3

determine solution : ℕ := 92

snip begin

/-- Reverse the base-two digits, dropping leading zeroes. -/
def binaryReverse (n : ℕ) : ℕ :=
  Nat.ofDigits 2 (Nat.digits 2 n).reverse

/-- Positive inputs have positive binary reversals. -/
lemma binaryReverse_pos (n : ℕ+) : 0 < binaryReverse (n : ℕ) := by
  unfold binaryReverse
  have hn : (n : ℕ) ≠ 0 := Nat.ne_of_gt n.2
  have hne : Nat.digits 2 (n : ℕ) ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hn
  have hsum : 0 < ((Nat.digits 2 (n : ℕ)).reverse).sum := by
    rw [List.sum_reverse]
    exact List.sum_pos_iff_exists_pos_nat.mpr
      ⟨_, List.getLast_mem hne, Nat.pos_of_ne_zero (Nat.getLast_digit_ne_zero 2 hn)⟩
  exact lt_of_lt_of_le hsum (Nat.sum_le_ofDigits _ (by decide : 1 ≤ 2))

/-- Binary reversal on positive naturals. -/
def pnatBinaryReverse (n : ℕ+) : ℕ+ :=
  ⟨binaryReverse (n : ℕ), binaryReverse_pos n⟩

/-- Binary palindromes. -/
def BinaryPalindrome (n : ℕ) : Prop :=
  (Nat.digits 2 n).Palindrome

instance instDecidablePredBinaryPalindrome : DecidablePred BinaryPalindrome := by
  intro n
  unfold BinaryPalindrome
  infer_instance

lemma binaryReverse_fixed_iff_binaryPalindrome (n : ℕ) :
    binaryReverse n = n ↔ BinaryPalindrome n := by
  unfold BinaryPalindrome
  constructor
  · intro h
    apply List.Palindrome.of_reverse_eq
    apply Nat.ofDigits_inj_of_len_eq (b := 2) (by decide : 1 < 2)
    · simp
    · intro l hl
      exact Nat.digits_lt_base (by decide : 1 < 2) (by simpa using hl)
    · intro l hl
      exact Nat.digits_lt_base (by decide : 1 < 2) hl
    · unfold binaryReverse at h
      rw [h, Nat.ofDigits_digits]
  · intro h
    unfold binaryReverse
    rw [h.reverse_eq]
    exact Nat.ofDigits_digits 2 n

/-- The five recurrence clauses from the problem. -/
structure SatisfiesRecurrence (f : ℕ+ → ℕ+) : Prop where
  one : f 1 = 1
  three : f 3 = 3
  double : ∀ n, f (2 * n) = f n
  four_one : ∀ n, f (4 * n + 1) + f n = 2 * f (2 * n + 1)
  four_three : ∀ n, f (4 * n + 3) + 2 * f n = 3 * f (2 * n + 1)

/-- Append a binary zero. -/
lemma digits_two_mul (n : ℕ) (hn : n ≠ 0) :
    Nat.digits 2 (2 * n) = 0 :: Nat.digits 2 n := by
  simpa using
    (Nat.digits_base_mul (b := 2) (m := n) (by decide) (Nat.pos_of_ne_zero hn))

/-- Append a binary one. -/
lemma digits_two_mul_add_one (n : ℕ) :
    Nat.digits 2 (2 * n + 1) = 1 :: Nat.digits 2 n := by
  simpa [Nat.add_comm] using
    (Nat.digits_add 2 (by decide : 1 < 2) 1 n (by decide : 1 < 2)
      (Or.inl one_ne_zero))

lemma binaryReverse_two_mul (n : ℕ) (hn : n ≠ 0) :
    binaryReverse (2 * n) = binaryReverse n := by
  unfold binaryReverse
  rw [digits_two_mul n hn, Nat.ofDigits_reverse_zero_cons]

lemma digits_four_mul_add_one (n : ℕ) (hn : n ≠ 0) :
    Nat.digits 2 (4 * n + 1) = 1 :: 0 :: Nat.digits 2 n := by
  rw [show 4 * n + 1 = 2 * (2 * n) + 1 by ring,
    digits_two_mul_add_one, digits_two_mul n hn]

lemma digits_four_mul_add_three (n : ℕ) :
    Nat.digits 2 (4 * n + 3) = 1 :: 1 :: Nat.digits 2 n := by
  rw [show 4 * n + 3 = 2 * (2 * n + 1) + 1 by ring,
    digits_two_mul_add_one, digits_two_mul_add_one]

lemma binaryReverse_four_mul_add_one_recurrence (n : ℕ) (hn : n ≠ 0) :
    binaryReverse (4 * n + 1) + binaryReverse n =
      2 * binaryReverse (2 * n + 1) := by
  unfold binaryReverse
  rw [digits_four_mul_add_one n hn, Nat.ofDigits_reverse_cons,
    Nat.ofDigits_reverse_zero_cons]
  rw [digits_two_mul_add_one n, Nat.ofDigits_reverse_cons]
  simp [Nat.pow_succ]
  ring

lemma binaryReverse_four_mul_add_three_recurrence (n : ℕ) :
    binaryReverse (4 * n + 3) + 2 * binaryReverse n =
      3 * binaryReverse (2 * n + 1) := by
  unfold binaryReverse
  rw [digits_four_mul_add_three n, Nat.ofDigits_reverse_cons, Nat.ofDigits_reverse_cons]
  rw [digits_two_mul_add_one n, Nat.ofDigits_reverse_cons]
  simp [Nat.pow_succ, Nat.add_assoc]
  ring

/-- Binary reversal satisfies the recurrence. -/
lemma pnatBinaryReverse_satisfiesRecurrence :
    SatisfiesRecurrence pnatBinaryReverse := by
  refine
    { one := PNat.eq rfl
      three := PNat.eq rfl
      double := ?_
      four_one := ?_
      four_three := ?_ }
  · intro n
    apply PNat.eq
    exact binaryReverse_two_mul (n : ℕ) (Nat.ne_of_gt n.2)
  · intro n
    apply PNat.eq
    simp only [PNat.add_coe, PNat.mul_coe]
    exact binaryReverse_four_mul_add_one_recurrence (n : ℕ) (Nat.ne_of_gt n.2)
  · intro n
    apply PNat.eq
    simp only [PNat.add_coe, PNat.mul_coe]
    exact binaryReverse_four_mul_add_three_recurrence (n : ℕ)

/-- One binary-recursion step of uniqueness. -/
lemma recurrence_step {f g : ℕ+ → ℕ+}
    (hf : SatisfiesRecurrence f) (hg : SatisfiesRecurrence g) (p : ℕ+)
    (hp : f p = g p) (hodd : f (2 * p + 1) = g (2 * p + 1)) :
    f (2 * p) = g (2 * p) ∧
      f (4 * p + 1) = g (4 * p + 1) ∧
      f (4 * p + 3) = g (4 * p + 3) := by
  constructor
  · calc
      f (2 * p) = f p := hf.double p
      _ = g p := hp
      _ = g (2 * p) := (hg.double p).symm
  constructor
  · apply add_right_cancel (b := g p)
    calc
      f (4 * p + 1) + g p = 2 * g (2 * p + 1) := by
        rw [← hp, hf.four_one p, hodd]
      _ = g (4 * p + 1) + g p := (hg.four_one p).symm
  · apply add_right_cancel (b := 2 * g p)
    calc
      f (4 * p + 3) + 2 * g p = 3 * g (2 * p + 1) := by
        rw [← hp, hf.four_three p, hodd]
      _ = g (4 * p + 3) + 2 * g p := (hg.four_three p).symm

/-- The recurrence determines the function uniquely. -/
lemma recurrence_unique {f g : ℕ+ → ℕ+}
    (hf : SatisfiesRecurrence f) (hg : SatisfiesRecurrence g) :
    ∀ n : ℕ+, f n = g n := by
  let Good : ℕ → Prop := fun m => ∀ hm : m ≠ 0,
    let p : ℕ+ := ⟨m, Nat.pos_of_ne_zero hm⟩
    f p = g p ∧ f (2 * p + 1) = g (2 * p + 1)
  have hGood : ∀ m, Good m := by
    intro m
    induction m using Nat.binaryRecFromOne with
    | zero =>
        intro hm
        exact (hm rfl).elim
    | one =>
        intro hm
        constructor
        · simpa using hf.one.trans hg.one.symm
        · exact hf.three.trans hg.three.symm
    | bit b m hm ih =>
        intro hbit
        let p : ℕ+ := ⟨m, Nat.pos_of_ne_zero hm⟩
        have ihp := ih hm
        have hstep := recurrence_step hf hg p ihp.1 ihp.2
        cases b
        · let q : ℕ+ := ⟨Nat.bit false m, Nat.pos_of_ne_zero hbit⟩
          have harg : 2 * q + 1 = 4 * p + 1 := by
            exact PNat.eq (by simp [q, p, Nat.bit_false_apply]; ring)
          constructor
          · exact hstep.1
          · change f (2 * q + 1) = g (2 * q + 1)
            rw [harg]
            exact hstep.2.1
        · let q : ℕ+ := ⟨Nat.bit true m, Nat.pos_of_ne_zero hbit⟩
          have harg : 2 * q + 1 = 4 * p + 3 := by
            exact PNat.eq (by simp [q, p, Nat.bit_true_apply]; ring)
          constructor
          · exact ihp.2
          · change f (2 * q + 1) = g (2 * q + 1)
            rw [harg]
            exact hstep.2.2
  intro n
  exact (hGood (n : ℕ) (Nat.ne_of_gt n.2)).1

/-- The recurrence solution is binary reversal. -/
lemma recurrence_unique_binaryReverse (f : ℕ+ → ℕ+) (hf : SatisfiesRecurrence f) :
    ∀ n : ℕ+, f n = pnatBinaryReverse n :=
  recurrence_unique hf pnatBinaryReverse_satisfiesRecurrence

/-- Fixed points are binary palindromes. -/
lemma pnatBinaryReverse_fixed_iff_palindrome (n : ℕ+) :
    pnatBinaryReverse n = n ↔ BinaryPalindrome (n : ℕ) := by
  rw [← binaryReverse_fixed_iff_binaryPalindrome (n : ℕ)]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

/-- Count binary palindromes up to `1988`. -/
lemma binaryPalindrome_count_le_1988 :
    ((Finset.Icc 1 1988).filter BinaryPalindrome).card = solution := by
  rfl

/-- Convert the finite count back to the problem statement. -/
lemma fixedPoint_count_from_recurrence (f : ℕ+ → ℕ+) (hf : SatisfiesRecurrence f) :
    Set.ncard {n | n ≤ 1988 ∧ f n = n} = solution := by
  rw [← binaryPalindrome_count_le_1988]
  rw [← Set.ncard_coe_finset]
  refine Set.ncard_congr (fun n _ => (n : ℕ)) ?mem ?inj ?surj
  · intro n hn
    change (n : ℕ) ∈ (Finset.Icc 1 1988).filter BinaryPalindrome
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨n.2, hn.1⟩, ?_⟩
    rw [← pnatBinaryReverse_fixed_iff_palindrome n, ← recurrence_unique_binaryReverse f hf n]
    exact hn.2
  · intro a b _ _ h
    exact Subtype.ext h
  · intro b hb
    rcases Finset.mem_filter.mp hb with ⟨hbIcc, hpal⟩
    rcases Finset.mem_Icc.mp hbIcc with ⟨hb1, hb1988⟩
    have hbpos : 0 < b := Nat.lt_of_lt_of_le Nat.zero_lt_one hb1
    refine ⟨⟨b, hbpos⟩, ⟨hb1988, ?_⟩, rfl⟩
    rw [recurrence_unique_binaryReverse f hf, pnatBinaryReverse_fixed_iff_palindrome]
    exact hpal

snip end

problem imo1988_p3 (f : ℕ+ → ℕ+)
    (h₀ : f 1 = 1)
    (h₁ : f 3 = 3)
    (h₂ : ∀ n, f (2 * n) = f n)
    (h₃ : ∀ n, f (4 * n + 1) + f n = 2 * f (2 * n + 1))
    (h₄ : ∀ n, f (4 * n + 3) + 2 * f n = 3 * f (2 * n + 1)) :
    Set.ncard {n | n ≤ 1988 ∧ f n = n} = solution := by
  exact fixedPoint_count_from_recurrence f ⟨h₀, h₁, h₂, h₃, h₄⟩

end Imo1988P3
