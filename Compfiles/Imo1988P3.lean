/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InternLM-MATH LEAN Formalizer v0.1. This is auto-formalized by InternLM-MATH LEAN Formalizer v0.1, modified and verified by InternLM-MATH team members.
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 1988, Problem 3

A function $f$ defined on the positive integers (and taking positive integers values) is given by:
$\begin{matrix} f(1) = 1, f(3) = 3 \\ f(2 \cdot n) = f(n) \\ f(4 \cdot n + 1) = 2 \cdot f(2 \cdot n + 1) - f(n) \\ f(4 \cdot n + 3) = 3 \cdot f(2 \cdot n + 1) - 2 \cdot f(n), \end{matrix}$
for all positive integers $n.$ Determine with proof the number of positive integers $\leq 1988$ for which $f(n) = n.$
-/

namespace Imo1988P3

problem imo1988_p3 (f : ℕ → ℕ) (h₀ : f 1 = 1) (h₁ : f 3 = 3) (h₂ : ∀ n, f (2 * n) = f n) (h₃ : ∀ n, f (4 * n + 1) = 2 * f (2 * n + 1) - f n) (h₄ : ∀ n, f (4 * n + 3) = 3 * f (2 * n + 1) - 2 * f n) (A: Finset {n | 0 < n ∧ n ≤ 1988 ∧ f n = n}) : A.card = 92 := by sorry