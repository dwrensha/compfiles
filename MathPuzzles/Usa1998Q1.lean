/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Algebra.BigOperators.Basic

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

theorem usa1998_q1
    (a : ℤ → ℤ)
    (b : ℤ → ℤ)
    (ha : a '' (Set.Icc 1 999) ⊆ Set.Icc 1 1998)
    (hb : b '' (Set.Icc 1 999) ⊆ Set.Icc 1 1998)
    (hab : Disjoint (a '' (Set.Icc 1 999)) (b '' (Set.Icc 1 999)))
    (habd : ∀ i ∈ Set.Icc 1 999, |a i - b i| = 1 ∨ |a i - b i| = 6)
    : (∑ i in Finset.range 999, |a (i + 1) - b (i + 1)|) % 10 = 9 := by
  -- Informal solution from Andreescu & Feng.
  -- Let k denote the number of pairs {aᵢ,bᵢ} with |aᵢ - bᵢ| = 6.
  -- Then the sum in question is k⬝6 + (999 - k)⬝1 = 999 + 5k,
  -- which ends in 9 provided that k is even.
  -- Hence it suffices to show that k is even.
  --
  -- Write k = kₒ + kₑ where kₒ (resp. kₑ) is equal to the number of pairs
  -- {aᵢ,bᵢ} with aᵢ,bᵢ both odd (resp. even). Since there are as many
  -- even numbers as odd numbers between 1 and 1998, and since each pair
  -- {aᵢ,bᵢ} with |aᵢ - bᵢ| contains one number of each type, we must have
  -- kₒ = kₑ. Hence k is even, as claimed.


  -- Informal solution from https://artofproblemsolving.com:
  -- Notice that |aᵢ-bᵢ| ≡ 1 MOD 5,
  -- so S=|a₁-b₁|+|a₂-b₂|+ ⋯ +|a₉₉₉ - b₉₉₉| ≡ 1+1+ ⋯ + 1 ≡ 999 ≡ 4 MOD 5.
  --
  -- Also, for integers M,N we have |M-N| ≡ M-N ≡ M+N MOD 2.
  --
  -- Thus, we also have
  -- S ≡ a₁ + b₁ + a₂ + b₂ + ⋯ + a₉₉₉ + b₉₉₉ ≡ 1 + 2 + ⋯ + 1998 ≡ 999*1999 ≡ 1 MOD 2
  -- so by the Chinese Remainder Theorem S ≡ 9 MOD 10.
  -- Thus, $S$ ends in the digit 9, as desired.
  sorry

