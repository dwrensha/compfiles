/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: sjfhsjfh
-/
import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# China Pre-CMO (National High School Math League, Second Round) 1983, Problem 2

函数 `f(x)` 在 `[0, 1]` 上有定义, `f(0) = f(1)`, 且对任意不同的 `x₁, x₂ ∈ [0, 1]`,
都有 `|f(x₂) − f(x₁)| < |x₂ − x₁|`.
求证: 对任意 `x₁, x₂ ∈ [0, 1]`, 都有 `|f(x₂) − f(x₁)| < 1/2`.

A function `f` is defined on `[0, 1]` with `f(0) = f(1)`.
For any distinct `x₁, x₂ ∈ [0, 1]`, we have `|f(x₂) − f(x₁)| < |x₂ − x₁|`.
Prove that `|f(x₂) − f(x₁)| < 1/2` for all `x₁, x₂ ∈ [0, 1]`.
-/

namespace ChinaPre1983P2

problem chinaPre1983_p2 (f : ℝ → ℝ) (h0 : f 0 = f 1)
  (h_contract : ∀ x₁ ∈ Set.Icc (0 : ℝ) 1, ∀ x₂ ∈ Set.Icc (0 : ℝ) 1,
    x₁ ≠ x₂ → |f x₂ - f x₁| < |x₂ - x₁|)
  : ∀ x₁ ∈ Set.Icc (0 : ℝ) 1, ∀ x₂ ∈ Set.Icc (0 : ℝ) 1, |f x₂ - f x₁| < 1 / 2 := by
  intro x₁ ⟨hx₁l, hx₁r⟩ x₂ ⟨hx₂l, hx₂r⟩
  sorry

end ChinaPre1983P2
