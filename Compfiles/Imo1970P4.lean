/-
Copyright (c) 2024 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Olympiad 1970, Problem 4

Determine the set of all positive integers n with the property that
the set {n, n + 1, n + 2, n + 3, n + 4, n + 5} can be partitioned
into two sets such that the product of the numbers in one set
equals the product of the nubmers in the other set.
-/

namespace Imo1970P4

open scoped BigOperators

determine SolutionSet : Finset ℕ+ := sorry

problem imo1970_p4 (n : ℕ+) :
    n ∈ SolutionSet ↔
      ∃ s1 s2 : Finset ℕ,
        s1 ∪ s2 = Finset.Icc n.val (n.val + 5) ∧
        s1 ∩ s2 = ∅ ∧
        ∏ m in s1, m = ∏ m in s2, m := by
  sorry
