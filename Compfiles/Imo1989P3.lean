/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Olympiad 1989, Problem 3

Let $n$ and $k$ be positive integers and let $S$ be a set of $n$ points in
the plane such that
  (i) no three points of $S$ are collinear, and
  (ii) for each point $P$ of $S$ there are at least $k$ points of $S$
       equidistant from $P$.
Prove that $k < \frac{1}{2} + \sqrt{2n}$.
-/

namespace Imo1989P3

abbrev Pt := EuclideanSpace ℝ (Fin 2)

problem imo1989_p3 (n k : ℕ) (hn : 0 < n) (hk : 0 < k)
    (S : Finset Pt)
    (hcard : S.card = n)
    -- no three points of `S` are collinear
    (hcol : ∀ p₁ ∈ S, ∀ p₂ ∈ S, ∀ p₃ ∈ S,
              p₁ ≠ p₂ → p₁ ≠ p₃ → p₂ ≠ p₃ → ¬ Collinear ℝ {p₁, p₂, p₃})
    -- for each point `P` of `S` there are at least `k` points of `S` equidistant from `P`
    (hequi : ∀ P ∈ S, ∃ (r : ℝ) (T : Finset Pt),
               T ⊆ S ∧ k ≤ T.card ∧ ∀ Q ∈ T, dist P Q = r) :
    (k : ℝ) < 1 / 2 + Real.sqrt (2 * n) := by
  sorry

end Imo1989P3
