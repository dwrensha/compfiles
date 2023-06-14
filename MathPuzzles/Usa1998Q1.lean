/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Int.ModEq

/-!
# USA Mathematical Olympiad 1998, Problem 1

Suppose that the set { 1, 2, ..., 1998 } has been partitioned into disjoint
pairs {aᵢ, bᵢ}, where 1 ≤ i ≤ 999, so that for all i, |aᵢ - bᵢ| = 1 or 6.

Prove that the sum

  |a₁ - b₁| + |a₂ - b₂| + ... + |a₉₉₉ - b₉₉₉|

ends in the digit 9.
-/

namespace Usa1998Q1
open BigOperators

lemma zmod_eq (a b c : ℤ) : a ≡ b [ZMOD c] ↔ a % c = b % c := by rfl

lemma mod2_neg (a : ℤ) : (-a) % 2 = a % 2 := by aesop

-- For integers M,N we have |M-N| ≡ M-N ≡ M+N MOD 2.
lemma mod2_diff (a b : ℤ) : |a - b| % 2 = (a + b) % 2 := by
  obtain ⟨h1, _⟩ | ⟨h1, _⟩ := abs_cases (a - b)
  · rw[h1]
    rw[Int.sub_eq_add_neg, Int.add_emod, mod2_neg, ←Int.add_emod]
  · rw[h1]
    rw[mod2_neg]
    rw[Int.sub_eq_add_neg, Int.add_emod, mod2_neg, ←Int.add_emod]

theorem usa1998_q1
    (a b : ℤ → ℤ)
    (ha : a '' (Set.Icc 1 999) ⊆ Set.Icc 1 1998)
    (hb : b '' (Set.Icc 1 999) ⊆ Set.Icc 1 1998)
    (hab : Disjoint (a '' (Set.Icc 1 999)) (b '' (Set.Icc 1 999)))
    (hai : a.Injective)
    (hbi : b.Injective)
    (habd : ∀ i ∈ Set.Icc 1 999, |a i - b i| = 1 ∨ |a i - b i| = 6)
    : (∑ i in Finset.range 999, |a (i + 1) - b (i + 1)|) % 10 = 9 := by

  -- Informal solution from https://artofproblemsolving.com:
  -- Notice that |aᵢ-bᵢ| ≡ 1 MOD 5,
  have h1 : ∀ i ∈ (Set.Icc 1 999), |a i - b i| ≡ 1 [ZMOD 5] := by
    intros i hi
    replace habd := habd i hi
    cases' habd with habd habd
    · rw[habd]
    · rw[habd]; rfl

  have h1' : ∀ i ∈ Finset.range 999, |a (i+1) - b (i+1)| % 5 = 1 := by
    intros i hi
    have h2 : ((i:ℤ) + 1) ∈ Set.Icc 1 999 := by
      rw[Set.mem_Icc]
      constructor
      · simp only [le_add_iff_nonneg_left, Nat.cast_nonneg]
      · rw[Finset.mem_range] at hi
        norm_cast
    have h3 := h1 (i + 1) h2
    exact h3

  -- so S=|a₁-b₁|+|a₂-b₂|+ ⋯ +|a₉₉₉ - b₉₉₉| ≡ 1+1+ ⋯ + 1 ≡ 999 ≡ 4 MOD 5.
  have h2 : (∑ i in Finset.range 999, |a (i + 1) - b (i + 1)|) ≡ 4 [ZMOD 5] :=
  by rw[zmod_eq, Finset.sum_int_mod, Finset.sum_congr rfl h1']
     simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
                Nat.cast_ofNat, mul_one]

  --
  -- Also, for integers M,N we have |M-N| ≡ M-N ≡ M+N MOD 2.
  -- (see mod2_diff above).
  --
  -- Thus, we also have
  -- S ≡ a₁ + b₁ + a₂ + b₂ + ⋯ + a₉₉₉ + b₉₉₉ ≡ 1 + 2 + ⋯ + 1998 ≡ 999*1999 ≡ 1 MOD 2
  have h3 : ∑ i in Finset.range 999, |a (i + 1) - b (i + 1)| ≡ 1 [ZMOD 2] := by
    rw[zmod_eq, Finset.sum_int_mod]
    have h4 : ∀ i ∈ Finset.range 999,
        |a (i + 1) - b (i + 1)| % 2 = (a (i + 1) + b (i + 1)) % 2 := by
      intros i hi; exact mod2_diff _ _

    rw[Finset.sum_congr rfl h4]
    sorry

  --
  -- Combining these facts gives S ≡ 9 MOD 10.
  have hmn : Nat.coprime (Int.natAbs 2) (Int.natAbs 5) := by sorry
  rw[show (9:ℤ) = 9 % 10 by norm_num,
     ← zmod_eq,
     show (10:ℤ) = 2 * 5 by norm_num]

  -- TODO why do I need to supply this implicit arguments? a direct rw
  -- does not work here.
  have h4 := @Int.modEq_and_modEq_iff_modEq_mul
       ((∑ i in Finset.range 999, |a (i + 1) - b (i + 1)|))
       9 2 5 hmn
  rw[←h4]
  constructor
  · rw[zmod_eq]
    rw[zmod_eq] at h3
    rw[h3]
    norm_num
  · rw[zmod_eq]
    rw[zmod_eq] at h2
    rw[h2]
    norm_num
