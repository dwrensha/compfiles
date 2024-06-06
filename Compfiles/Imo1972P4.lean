/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InternLM-MATH LEAN Formalizer v0.1. This is auto-formalized by InternLM-MATH LEAN Formalizer v0.1, modified and verified by InternLM-MATH team members.
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 1972, Problem 4

Find all positive real solutions to:

(x_1^2 - x_3x_5)(x_2^2 - x_3x_5) ≤ 0
(x_2^2 - x_4x_1)(x_3^2 - x_4x_1) ≤ 0
(x_3^2 - x_5x_2)(x_4^2 - x_5x_2) ≤ 0
(x_4^2 - x_1x_3)(x_5^2 - x_1x_3) ≤ 0
(x_5^2 - x_2x_4)(x_1^2 - x_2x_4) ≤ 0
-/

namespace Imo1972P4

problem imo1972_p4 (a b c d e : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ 0 < e) (h₁ : (a^2 - c * e) * (b^2 - c * e) ≤ 0) (h₂ : (b^2 - d * a) * (c^2 - d * a) ≤ 0) (h₃ : (c^2 - e * b) * (d^2 - e * b) ≤ 0) (h₄ : (d^2 - a * c) * (e^2 - a * c) ≤ 0) (h₅ : (e^2 - b * d) * (a^2 - b * d) ≤ 0) : a = b ∧ b = c ∧ c = d ∧ d = e ∧ e = a := by sorry
