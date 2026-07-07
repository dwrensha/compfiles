/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Combinatorics, .NumberTheory] }

/-!
# International Mathematical Olympiad 1995, Problem 6

Let p be an odd prime number. How many p-element subsets A of
{1, 2, ..., 2p} are there, the sum of whose elements is
divisible by p?
-/

namespace Imo1995P6

determine solution (p : ℕ) : ℕ := sorry

problem imo1995_p6 (p : ℕ) (hp : p.Prime) (hodd : Odd p) :
    (((Finset.Icc 1 (2 * p)).powersetCard p).filter
      (fun A ↦ p ∣ ∑ x ∈ A, x)).card = solution p := by
  sorry

end Imo1995P6
