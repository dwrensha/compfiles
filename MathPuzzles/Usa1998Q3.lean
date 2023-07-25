/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# USA Mathematical Olympiad 1998, Problem 3

Let a₀,a₁,...,aₙ be real numbers from the interval (0,π/2) such that

  tan(a₀ - π/4) + tan(a₁ - π/4) + ... + tan(aₙ - π/4) ≥ n - 1.

Prove that

  tan(a₀)tan(a₁)...tan(aₙ) ≥ nⁿ⁺¹.

-/

namespace Usa1998Q3
open BigOperators

theorem usa1998_q3
    (n : ℕ)
    (a : ℕ → ℝ)
    (ha : ∀ i, i < n + 1 → a n ∈ Set.Ioo 0 (Real.pi / 2))
    (hs : n - 1 ≤ ∑ i in Finset.range (n + 1), Real.tan (a i - (Real.pi / 4)))
    : Real.rpow n (n + 1) ≤ ∏ i in Finset.range (n + 1), Real.tan (a i) := by
  -- informal solution from artofproblemsolving.com
  --
  -- Let yᵢ = tan(aᵢ - π/4), where 0 ≤ i ≤ n.
  -- Then we have
  --  y₀ + y₁ + ... + yₙ ≥ n - 1
  --  1 + yᵢ ≥ ∑_{j ≠ i} (1 - yⱼ)
  --  (1 + yᵢ)/n ≥ (1/n) ∑_{j ≠ i} (1 - yⱼ)
  --
  -- Then, by AM-GM,
  -- (1/n) ∑_{j ≠ i} (1 - yⱼ) ≥ ∏_{j ≠ i} (1 - yⱼ)^{1/n}
  -- (1 + yᵢ)/n ≥ ∏_{j ≠ i} (1 - yⱼ)^{1/n}
  -- ∏ᵢ(1 + yᵢ)/n ≥ ∏ᵢ∏_{j ≠ i} (1 - yⱼ)^{1/n}
  -- ... a bunch more steps...
  sorry
