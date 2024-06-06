/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InternLM-MATH LEAN Formalizer v0.1. This is auto-formalized by InternLM-MATH LEAN Formalizer v0.1, modified and verified by InternLM-MATH team members.
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 1993, Problem 1

Let $f\left(x\right)=x^n+5x^{n-1}+3$, where $n>1$ is an integer. Prove that $f\left(x\right)$ cannot be expressed as the product of two non-constant polynomials with integer coefficients.
-/

namespace Imo1993P1

problem imo1993_p1 (n : ℕ) (hn : 1 < n) (f : Polynomial ℤ) (hf : f = X ^ n + 5 * X ^ (n - 1) + 3) : ¬ (∃ (g h : Polynomial ℤ), f = g * h ∧ ¬ (∃ g h : Polynomial ℤ, f = g * h ∧ ¬g = 1 ∧ ¬h = 1))  := by sorry