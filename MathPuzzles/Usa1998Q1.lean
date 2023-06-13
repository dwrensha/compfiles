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

theorem usa1998_q1
    (a b : ℤ → ℤ)
    (ha : a '' (Set.Icc 1 999) ⊆ Set.Icc 1 1998)
    (hb : b '' (Set.Icc 1 999) ⊆ Set.Icc 1 1998)
    (hab : Disjoint (a '' (Set.Icc 1 999)) (b '' (Set.Icc 1 999)))
    (habd : ∀ i ∈ Set.Icc 1 999, |a i - b i| = 1 ∨ |a i - b i| = 6)
    : (∑ i in Finset.range 999, |a (i + 1) - b (i + 1)|) % 10 = 9 := by

  -- Informal solution from https://artofproblemsolving.com:
  -- Notice that |aᵢ-bᵢ| ≡ 1 MOD 5,
  -- so S=|a₁-b₁|+|a₂-b₂|+ ⋯ +|a₉₉₉ - b₉₉₉| ≡ 1+1+ ⋯ + 1 ≡ 999 ≡ 4 MOD 5.
  --
  -- Also, for integers M,N we have |M-N| ≡ M-N ≡ M+N MOD 2.
  --
  -- Thus, we also have
  -- S ≡ a₁ + b₁ + a₂ + b₂ + ⋯ + a₉₉₉ + b₉₉₉ ≡ 1 + 2 + ⋯ + 1998 ≡ 999*1999 ≡ 1 MOD 2
  --
  -- Combining these facts gives S ≡ 9 MOD 10.
  sorry

-- this looks useful:
#check Int.modEq_and_modEq_iff_modEq_mul
