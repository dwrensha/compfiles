/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Order
import Mathlib.Data.Int.ModEq
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.LocallyFinite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.LinearCombination

/-!
There are 101 positive integers arranged in a circle.
Suppose that the integers sum to 300.
Prove that there exists a contiguous subarray that sums to 200.

https://mathstodon.xyz/@alexdbolton/110292738044661739
https://math.stackexchange.com/questions/282589/101-positive-integers-placed-on-a-circle
-/

namespace IntegersInACircle
open scoped BigOperators

lemma lemma1 {a : ℤ} (h1 : a % 100 = 0) (h2 : 0 < a) (h3 : a < 300) :
    a = 100 ∨ a = 200 := by
 rw[show (0:ℤ) = 0 % 100 by rfl] at h1
 have h5 : 100 ∣ a := Iff.mp Int.modEq_zero_iff_dvd h1
 obtain ⟨k,hk⟩ := exists_eq_mul_left_of_dvd h5
 rw[hk] at h2 h3 ⊢
 have h6 : k < 3 := by linarith
 have h7 : 0 < k := by linarith
 interval_cases k <;> norm_num

lemma lemma3 {f : ZMod 101 → ℤ} (y : ZMod 101)
    : ∑ z : ZMod 101, f z = ∑ i in Finset.range 101, f (y + i) := by
  let g := λ (i:ℕ) ↦ y + (i:ZMod 101)
  have hg: ∀ (x : ℕ),
      x ∈ Finset.range 101 → ∀ (y : ℕ), y ∈ Finset.range 101 → g x = g y → x = y := by
    intros a ha b hb hgab
    dsimp at hgab
    have h5 : (a : ZMod 101) = (b : ZMod 101) := by linear_combination hgab
    have h8: a % 101 = b % 101 := Iff.mp (ZMod.nat_cast_eq_nat_cast_iff' a b 101) h5
    rw[Finset.mem_range] at ha hb
    have h6: a % 101 = a := Nat.mod_eq_of_lt ha
    have h7: b % 101 = b := Nat.mod_eq_of_lt hb
    rwa[h6, h7] at h8
  have h1 := Finset.sum_image (f := f) (g := g) (s := Finset.range 101) hg
  --have h2 : ∑ z : ZMod 101, f z = ∑ z in Finset.univ, f z := rfl
  rw[← h1]
  have h3 : Finset.image g (Finset.range 101) = Finset.univ := by
     rw[Finset.eq_univ_iff_forall]
     intros a
     rw[Finset.mem_image]
     use (a - y).val
     constructor
     · rw[Finset.mem_range]
       exact ZMod.val_lt (a - y)
     · simp
  rw[h3]

lemma lemma2
    (a : ZMod 101 → ℤ)
    (ha : ∀ i, 1 ≤ a i)
    (ha_sum : ∑ i : ZMod 101, a i = 300)
    (x y : ZMod 101)
    (hxy : x.val < y.val)
    (hfxy : ∑ i in Finset.range x.val, (a ↑i : ZMod 100) =
              ∑ i in Finset.range y.val, (a ↑i : ZMod 100)) :
    ∃ j : ZMod 101, ∃ n : ℕ, ∑ i in Finset.range n, a (j + i) = 200 := by
  have h0 : (Finset.Ico x.val y.val).Nonempty := by aesop
  have h1 : 0 < ∑ i in Finset.Ico x.val y.val, a ↑i := by
    refine' Finset.sum_pos _ h0
    aesop

  have h3 : ((∑ i in Finset.Ico x.val y.val, a ↑i) : ZMod 100) = 0 := by
     have h4 : x.val ≤ y.val := by norm_cast; exact LT.lt.le hxy
     rw[Finset.sum_Ico_eq_sub _ h4]
     aesop

  have h5 : y.val ∉ Finset.Ico x.val y.val := Finset.right_not_mem_Ico

  have h8 : (Finset.Ico x.val y.val).card < 101 := by
     rw[Nat.card_Ico]
     have hy': y.val - x.val ≤ y.val := Nat.sub_le _ _
     exact lt_of_le_of_lt hy' y.prop

  have h7 :
    ((Finset.Ico x.val y.val).image
     (λ (i:ℕ) ↦ (i : ZMod 101))).card < (@Finset.univ (ZMod 101)).card :=
    calc _ ≤ (Finset.Ico x.val y.val).card := Finset.card_image_le
         _ < 101 := h8

  have h4 : ∑ i in Finset.Ico x.val y.val, a ↑i < 300 := by
    have h10 : ∀ a ∈ Finset.Ico x.val y.val,
               ∀ b ∈ Finset.Ico x.val y.val, (a : ZMod 101) = b → a = b := by
      intros a ha b hb hab
      have h13 : a % 101 = b % 101 :=
        Iff.mp (ZMod.nat_cast_eq_nat_cast_iff' a b 101) hab
      rw[Finset.mem_Ico] at ha hb
      have h11 : a < 101 := lt_trans ha.2 y.prop
      have h12 : b < 101 := lt_trans hb.2 y.prop
      rwa[Nat.mod_eq_of_lt h11, Nat.mod_eq_of_lt h12] at h13
    have h6 := @Finset.sum_image _
               (g := λ i:ℕ ↦ (i : ZMod 101)) a _ _ (Finset.Ico x.val y.val)
               h10
    rw[←h6, ←ha_sum]
    have h9 : (Finset.Ico x.val y.val).image (λ i:ℕ ↦ (i : ZMod 101))
       ⊂ Finset.univ := by
      rw[Finset.ssubset_univ_iff]
      intro hn
      rw[hn] at h7
      aesop
    rw[Finset.ssubset_iff] at h9
    obtain ⟨z, hzn, _⟩ := h9
    apply Finset.sum_lt_sum_of_subset (f := a) (i:= z)
    · exact Finset.subset_univ _
    · exact Finset.mem_univ z
    · exact hzn
    · exact ha z
    · intros j _ _
      exact Int.le_of_lt (ha j)

  -- The difference between those sums is either 100 or 200.

  have h10 : ∑ i in Finset.Ico x.val y.val, (a ↑i : ZMod 100) =
        (((∑ i in Finset.Ico x.val y.val, ((a ↑i))): ℤ) : ZMod 100) :=
     by norm_cast
  rw[h10] at h3; clear h10
  rw[show (0:ZMod 100) = ((0 :ℤ): ZMod 100) by rfl] at h3
  rw[ZMod.int_cast_eq_int_cast_iff'] at h3
  norm_num at h3
  have h11 := lemma1 h3 h1 h4

  have h12 : ∀ k, k ∈ Finset.range (y.val - x.val) → a ↑(x.val + k) = a (x + ↑k) := by
      intros k hk
      congr
      have h15: k < 101 := by
         rw[Finset.mem_range] at hk
         calc k < y.val - x.val := hk
              _ ≤ y.val := Nat.sub_le _ _
              _ < 101 := y.prop
      exact (Nat.mod_eq_of_lt h15).symm

  -- If it's 200, then we choose that subsequence.
  -- If it's 100, then we choose its complement.
  obtain h100 | h200 := h11
  · use y.val
    use 101 - (y.val - x.val)
    rw[Finset.sum_Ico_eq_sum_range, Finset.sum_congr rfl h12] at h100
    rw[lemma3 x] at ha_sum
    have h20 : 101 = ((y.val - x.val) + (101 - (y.val - x.val))) := by
      have : y.val - x.val ≤ 101 :=
           calc _ ≤ y.val := Nat.sub_le _ _
                _ ≤ 101 := le_of_lt y.prop
      rw[add_comm]
      exact Iff.mp (Nat.sub_eq_iff_eq_add this) rfl

    have h18 : Finset.range 101 =
        Finset.range ((y.val - x.val) + (101 - (y.val - x.val))) := by congr
    have h19 := Finset.sum_range_add (λi ↦ a (x + i)) (y.val - x.val) (101 - (y.val - x.val))
    rw[h100, ←h18, ha_sum] at h19
    have h21 : ∀ i ∈ Finset.range (101 - (y.val - x.val)),
          a (x + ↑(y.val - x.val + i)) = a (↑(ZMod.val y) + ↑i) := by
      intros i _
      apply congrArg
      have h22 : x + ↑(y.val - x.val + i) = ↑(x.val + (y.val - x.val + i)) :=
        by have : x = (x.val : ZMod 101) := Eq.symm (ZMod.nat_cast_zmod_val x)
           nth_rewrite 1 [this]
           norm_cast
      rw[h22]
      norm_cast
      rw[←Nat.add_assoc, add_comm x.val _, Nat.sub_add_cancel (le_of_lt hxy)]

    rw[Finset.sum_congr rfl h21] at h19
    linarith
  · use x
    use y.val - x.val
    rw[Finset.sum_Ico_eq_sum_range] at h200
    rwa[Finset.sum_congr rfl h12] at h200

theorem integers_in_a_circle
    (a : ZMod 101 → ℤ)
    (ha : ∀ i, 1 ≤ a i)
    (ha_sum : ∑ i : ZMod 101, a i = 300)
    : ∃ j : ZMod 101, ∃ n : ℕ, ∑ i in Finset.range n, a (j + i) = 200 := by
  -- informal solution (from the math.stackexchange link above)
  -- Start at any position and form sums of subsequences of length 0, 1, ... 100
  -- starting at that position.
  -- By the pigeonhole principle, two of these sums are equivalent mod 100.
  let f : ZMod 101 → ZMod 100 :=
    λ x ↦ ∑ i in Finset.range x.val, a i
  obtain ⟨x,y,hxy,hfxy⟩ := Fintype.exists_ne_map_eq_of_card_lt f
            (Nat.lt.base (Fintype.card (ZMod 100)))

  obtain hxy1 | hxy2 | hxy3 := lt_trichotomy x.val y.val
  · exact lemma2 a ha ha_sum x y hxy1 hfxy
  · exact (hxy (Fin.ext hxy2)).elim
  · exact lemma2 a ha ha_sum y x hxy3 hfxy.symm
