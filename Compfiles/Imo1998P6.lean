/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InternLM-MATH LEAN Formalizer v0.1. This is auto-formalized by InternLM-MATH LEAN Formalizer v0.1, modified and verified by InternLM-MATH team members.
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 1998, Problem 6

Consider all functions f from the set of all positive integers into itself satisfying f(t^2f(s)) = sf(t)^2 for all s and t. Determine the least possible value of f(1998).
-/

namespace Imo1998P6

problem imo1998_p6 (f : ℕ → ℕ) (h : ∀ s t, f (t^2 * f s) = s * (f t)^2) : IsLeast {n:ℕ | n = f 1998} 120 := by sorry
