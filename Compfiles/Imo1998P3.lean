/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InternLM-MATH LEAN Formalizer v0.1. This is auto-formalized by InternLM-MATH LEAN Formalizer v0.1, modified and verified by InternLM-MATH team members.
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Olympiad 1998, Problem 3

For any positive integer $n$, let $d(n)$ denote the number of positive divisors of $n$ (including 1 and $n$ itself). Determine all positive integers $k$ such that $d(n^2)/d(n) = k$ for some $n$.
-/

namespace Imo1998P3

problem imo1998_p3 (k : ℕ) : (∃ n : ℕ, (Finset.card (Nat.divisors (n^2)))/(Finset.card (Nat.divisors n)) = k) ↔ k % 2=1 := by sorry