/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Finset.Interval

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

-- For integers M,N we have |M-N| ≡ M-N ≡ M+N MOD 2.
lemma mod2_diff (a b : ℤ) : |a - b| % 2 = (a + b) % 2 := by
  obtain ⟨h1, _⟩ | ⟨h1, _⟩ := abs_cases (a - b)
  · rw[h1]
    rw[Int.sub_eq_add_neg, Int.add_emod, Int.neg_emod_two, ←Int.add_emod]
  · rw[h1]
    rw[Int.neg_emod_two]
    rw[Int.sub_eq_add_neg, Int.add_emod, Int.neg_emod_two, ←Int.add_emod]

lemma lemma1
    (a : ℕ → ℕ)
    (s : Finset ℕ)
    (ha : Set.InjOn a s)
    (g : ℕ → ℤ)
    : ∑ i in s, g (a i) =
      ∑ i in Finset.image a s, g i := by
  induction' s using Finset.induction with n s hs ih
  · simp only [Finset.sum_empty, Finset.image_empty]
  · rw[Finset.sum_insert hs]
    rw[Finset.image_insert]
    have h4 : Set.InjOn a s := by
      intros x hx y hy hxy
      have h7 : x ∈ insert n s := Finset.mem_insert_of_mem hx
      have h8 : y ∈ insert n s := Finset.mem_insert_of_mem hy
      exact ha h7 h8 hxy

    have h2 : a n ∉ Finset.image a s := by
      simp only [Finset.mem_image, not_exists, not_and]
      intros x hx
      clear ih
      intro h6
      have h7 : x ∈ insert n s := Finset.mem_insert_of_mem hx
      have h8 : n ∈ insert n s := Finset.mem_insert_self n s
      exact hs ((ha h7 h8 h6) ▸ hx)
    rw[Finset.sum_insert h2]
    have h5 := ih h4
    congr

lemma lemma2
    {a b c : Finset ℕ}
    (hab : Disjoint a b)
    (hc : a.card + b.card = c.card)
    (hac : a ⊆ c)
    (hbc : b ⊆ c)
    : a ∪ b = c := by
  have habc : a ∪ b ⊆ c := Finset.union_subset hac hbc
  have h1 : (a ∪ b).card = a.card + b.card := Finset.card_union_eq hab
  rw[←h1] at hc
  have h2 := le_of_eq hc.symm
  exact Iff.mp (Finset.subset_iff_eq_of_card_le h2) habc

theorem usa1998_q1
    (a b : ℕ → ℕ)
    (ha : Finset.image a (Finset.Icc 1 999) ⊆ Finset.Icc 1 1998)
    (hb : Finset.image b (Finset.Icc 1 999) ⊆ Finset.Icc 1 1998)
    (hab : Disjoint (Finset.image a (Finset.Icc 1 999))
                    (Finset.image b (Finset.Icc 1 999)))
    (hai : Set.InjOn a (Finset.Icc 1 999))
    (hbi : Set.InjOn b (Finset.Icc 1 999))
    (habd : ∀ i ∈ Finset.Icc 1 999, |(a i : ℤ) - b i| = 1 ∨
                                    |(a i : ℤ) - b i| = 6)
    : (∑ i in Finset.Icc 1 999, |(a i : ℤ) - b i|) % 10 = 9 := by

  -- Informal solution from https://artofproblemsolving.com:
  -- Notice that |aᵢ-bᵢ| ≡ 1 MOD 5,
  have h1 : ∀ i ∈ (Finset.Icc 1 999), |a i - b i| ≡ 1 [ZMOD 5] := by
    intros i hi
    replace habd := habd i hi
    cases' habd with habd habd
    · rw[habd]
    · rw[habd]; rfl

  have h1' : ∀ i ∈ Finset.Icc 1 999, |(a i : ℤ) - b i| % 5 = 1 := by
    intros i hi
    exact h1 i hi

  -- so S=|a₁-b₁|+|a₂-b₂|+ ⋯ +|a₉₉₉ - b₉₉₉| ≡ 1+1+ ⋯ + 1 ≡ 999 ≡ 4 MOD 5.
  have h2 : (∑ i in Finset.Icc 1 999, |a i - b i|) ≡ 4 [ZMOD 5] :=
  by rw[zmod_eq, Finset.sum_int_mod, Finset.sum_congr rfl h1']
     simp only [gt_iff_lt, Finset.sum_const, Nat.card_Icc,
                ge_iff_le, add_tsub_cancel_right, nsmul_eq_mul,
                Nat.cast_ofNat, mul_one]

  have h5 : Finset.image a (Finset.Icc 1 999) ∪
            Finset.image b (Finset.Icc 1 999) =
       Finset.Icc 1 1998 := by
    have h20 : (Finset.Icc 1 999).card = 999 := by rw[Nat.card_Icc]
    have h21 : (Finset.image a (Finset.Icc 1 999)).card = 999 :=
       by nth_rewrite 2 [← h20]
          exact Iff.mpr Finset.card_image_iff hai
    have h22 : (Finset.image b (Finset.Icc 1 999)).card = 999 :=
       by nth_rewrite 2 [← h20]
          exact Iff.mpr Finset.card_image_iff hbi

    have h23 : 1998 = (Finset.image a (Finset.Icc 1 999)).card
                     + (Finset.image b (Finset.Icc 1 999)).card := by
       rw[h21, h22]

    have h24 : ((Finset.image a (Finset.Icc 1 999)) ∪
                (Finset.image b (Finset.Icc 1 999))).card = 1998 := by
      rw[h23, Finset.card_union_eq hab]

    -- therefore they hit every value in Finset.Icc 1 1998
    have h25 : (Finset.Icc 1 1998).card = 1998 := by rw[Nat.card_Icc]
    rw[←h25] at h24
    apply lemma2
    · aesop
    · simp[h21, h22]
    · exact ha
    · exact hb
  --
  -- Also, for integers M,N we have |M-N| ≡ M-N ≡ M+N MOD 2.
  -- (see mod2_diff above).
  --
  -- Thus, we also have
  -- S ≡ a₁ + b₁ + a₂ + b₂ + ⋯ + a₉₉₉ + b₉₉₉ [MOD 2]
  --   ≡ 1 + 2 + ⋯ + 1998 [MOD 2]
  --   ≡ 999*1999 ≡ 1 [MOD 2]
  have h3 : ∑ i in Finset.Icc 1 999, |a i - b i| ≡ 1 [ZMOD 2] := by
    rw[zmod_eq, Finset.sum_int_mod]
    have h4 : ∀ i ∈ Finset.Icc 1 999,
        |(a i : ℤ) - b i| % 2 =
          ((a i % 2) + (b i % 2)) % 2 := by
      intros i _
      rw[mod2_diff, Int.add_emod]

    rw[Finset.sum_congr rfl h4]
    rw[←Finset.sum_int_mod]
    rw[Finset.sum_add_distrib]
    have h10 : ∑ i in Finset.Icc 1 999, (a i : ℤ) % 2 =
        ∑ i in Finset.image a (Finset.Icc 1 999), (i : ℤ) % 2 := by
      exact lemma1 a (Finset.Icc 1 999) hai (fun i ↦ ((i:ℤ) % 2))

    have h11 : ∑ i in Finset.Icc 1 999, (b i : ℤ) % 2 =
        ∑ i in Finset.image b (Finset.Icc 1 999), (i : ℤ) % 2 := by
      exact lemma1 b (Finset.Icc 1 999) hbi (fun i ↦ ((i:ℤ) % 2))

    rw[h10, h11, ←Finset.sum_union hab, h5, ←Finset.sum_int_mod]
    norm_cast

  --
  -- Combining these facts gives S ≡ 9 MOD 10.
  have hmn : Nat.coprime (Int.natAbs 2) (Int.natAbs 5) := by norm_cast
  rw[show (9:ℤ) = 9 % 10 by norm_num,
     ← zmod_eq,
     show (10:ℤ) = 2 * 5 by norm_num]

  -- TODO why do I need to supply this implicit arguments? a direct rw
  -- does not work here.
  have h4 := @Int.modEq_and_modEq_iff_modEq_mul
       ((∑ i in Finset.Icc 1 999, |a i - b i|))
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
