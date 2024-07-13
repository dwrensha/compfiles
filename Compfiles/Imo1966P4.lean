/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 1966, Problem 4

Prove that for every natural number n and for every real
number x that is not of the form kπ/2ᵗ for t a non-negative
integer and k any integer,

 1 / (sin 2x) + 1 / (sin 4x) + ... + 1 / (sin 2ⁿx) = cot x - cot 2ⁿ x.
-/

namespace Imo1966P4

problem imo1966_p4 (n : ℕ) (x : ℝ)
    (hx : ∀ t : ℕ, ∀ k : ℤ, x ≠ k * Real.pi / 2^t) :
    ∑ i ∈ Finset.range n, 1 / Real.sin (2^(i + 1) * x) =
    1 / Real.tan x - 1 / Real.tan (2^n * x) := by
  sorry


end Imo1966P4
