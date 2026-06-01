/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karl Mehltretter
-/

import Mathlib.Data.PNat.Basic
import Mathlib.Algebra.Polynomial.Basic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# USA Mathematical Olympiad 1977, Problem 1

Determine all pairs of positive integers (m, n) such that

  1 + x ^ n + x ^ (2 * n) + ... + x ^ (m * n)

is divisible by

  1 + x + x ^ 2 + ... + x ^ m.
-/

namespace Usa1977P1

open Polynomial

noncomputable def geomSumStep (m n : ℕ+) : ℤ[X] :=
  ∑ k ∈ Finset.range (m + 1), X ^ (k * n : ℕ)

noncomputable def geomSum (m : ℕ+) : ℤ[X] :=
  ∑ k ∈ Finset.range (m + 1), X ^ k

determine solution_set : Set (ℕ+ × ℕ+) := sorry

problem usa1977_p1 (m n : ℕ+) :
    (m, n) ∈ solution_set ↔ geomSum m ∣ geomSumStep m n := by
  sorry

end Usa1977P1
