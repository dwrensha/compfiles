/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 1988, Problem 4

Show that the set of real numbers $x$ which satisfy the inequality
$$\sum_{k=1}^{70} \frac{k}{x - k} \ge \frac{5}{4}$$
is a union of disjoint intervals, the sum of whose lengths is $1988$.
-/

namespace Imo1988P4

open scoped BigOperators

problem imo1988_p4 :
    ∃ (n : ℕ) (I : Fin n → Set ℝ),
      (∀ i, (I i).OrdConnected) ∧
      (Pairwise fun i j ↦ Disjoint (I i) (I j)) ∧
      (⋃ i, I i) =
        {x : ℝ | (5 : ℝ) / 4 ≤ ∑ k ∈ Finset.Icc (1 : ℕ) 70, (k : ℝ) / (x - k)} ∧
      ∑ i, MeasureTheory.volume (I i) = 1988 := by
  sorry

end Imo1988P4
