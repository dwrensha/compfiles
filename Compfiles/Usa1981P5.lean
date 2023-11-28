/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file

/-!
# USA Mathematical Olympiad 1981, Problem 5

Show that for any positive real number x and any nonnegative
integer n,

    ∑ₖ (⌊kx⌋/k) ≤ ⌊nx⌋

where the sum goes from k = 1 to k = n, inclusive.
-/

namespace Usa1981P5
open BigOperators

problem usa1981_p5 (x : ℝ) (n : ℕ) :
    ∑ k in Finset.Icc 1 n, ((⌊k * x⌋:ℝ)/k) ≤ ⌊n * x⌋ := by
  sorry
