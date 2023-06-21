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

/-!
There are 101 positive integers arranged in a circle.
Suppose that the integers sum to 300.
Prove that there exists a contiguous subarray that sums to 200.

https://mathstodon.xyz/@alexdbolton/110292738044661739
https://math.stackexchange.com/questions/282589/101-positive-integers-placed-on-a-circle
-/

namespace IntegersInACircle
open scoped BigOperators

theorem integers_in_a_circle
    (a : ZMod 101 → ℤ)
    (ha : ∀ i, 1 ≤ a i)
    (ha_sum : ∑ i : ZMod 101, a i = 300)
    : ∃ j : ZMod 101, ∃ n : ℕ, ∑ i in Finset.range n, a (j + n) = 200 := by
  -- informal solution (from the math.stackexchange link above)
  -- Start at any position and form sums of subsequences of length 0, 1, ... 100
  -- starting at that position.
  -- By the pigeonhole principle, two of these sums are equivalent mod 100.
  let f : Fin 101 → ZMod 100 :=
    λ x ↦ ∑ i in Finset.range x.val, a i
  obtain ⟨x,y,hxy,hfxy⟩ := Fintype.exists_ne_map_eq_of_card_lt f
            (Nat.lt.base (Fintype.card (ZMod 100)))

  have hlt : x < y := sorry -- wlog tactic, or something

  have h0 : (Finset.Ico x.val y.val).Nonempty := by aesop
  have h1 : 0 < ∑ i in Finset.Ico x.val y.val, a ↑i := by
    refine' Finset.sum_pos _ h0
    aesop

  have h3 : ((∑ i in Finset.Ico x.val y.val, a ↑i) : ZMod 100) = 0 := by
     have h4 : x.val ≤ y.val := by norm_cast; exact LT.lt.le hlt
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
    obtain ⟨z, hzn, hz⟩ := h9
    apply Finset.sum_lt_sum_of_subset (f := a) (i:= z)
    · exact Finset.subset_univ _
    · exact Finset.mem_univ z
    · exact hzn
    · exact ha z
    · intros j hj hj'
      exact Int.le_of_lt (ha j)

  --have : ((∑ i in Finset.Ico x.val y.val, a ↑i) % 100) = 0 := by aesop
  -- The difference between those sums is either 100 or 200.

  -- If it's 200, then we choose that subsequence.
  -- If it's 100, then we choose its complement.
  sorry
