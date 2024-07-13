/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InternLM-MATH LEAN Formalizer v0.1
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 1975, Problem 2

Let a1 < a2 < a3 < ... be positive integers.
Prove that for every i >= 1,
there are infinitely many a_n that can be written in the form a_n = ra_i + sa_j,
with r, s positive integers and j > i.
-/

namespace Imo1975P2

problem imo1975_p2 (a : ℕ → ℤ)
  (apos : ∀ i : ℕ, 0 < a i)
  (ha : ∀ i : ℕ, a i < a (i + 1)) :
    ( ∀ i n0 : ℕ ,
      ∃ n, n0 ≤ n ∧
      ∃ r s : ℕ,
      ∃ j : ℕ,
        a n = r * a i + s * a j ∧
        i < j ∧
        0 < r ∧
        0 < s ):= by sorry


end Imo1975P2
