/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karl Mehltretter
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# USA Mathematical Olympiad 1984, Problem 5

P(x) is a polynomial of degree 3n such that

  P(0) = P(3) = ... = P(3n) = 2,
  P(1) = P(4) = ... = P(3n - 2) = 1,
  P(2) = P(5) = ... = P(3n - 1) = 0,
  and P(3n + 1) = 730.

Determine n.
-/

namespace Usa1984P5

open Polynomial

determine solution_value : ℕ := sorry

problem usa1984_p5 (n : ℕ) (hn : 0 < n) (P : ℝ[X])
    (hdeg : P.natDegree = 3 * n)
    (h0 : ∀ k ∈ Finset.range (n + 1), P.eval (((3 * k : ℕ) : ℝ)) = 2)
    (h1 : ∀ k ∈ Finset.range n, P.eval (((3 * k + 1 : ℕ) : ℝ)) = 1)
    (h2 : ∀ k ∈ Finset.range n, P.eval (((3 * k + 2 : ℕ) : ℝ)) = 0)
    (h730 : P.eval (((3 * n + 1 : ℕ) : ℝ)) = 730) :
    n = solution_value := by
  sorry

end Usa1984P5
