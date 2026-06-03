/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Olympiad 1997, Problem 4

An $n \times n$ matrix whose entries come from the set
$S = \{1, 2, \ldots, 2n - 1\}$ is called a *silver matrix* if, for each
$i = 1, \ldots, n$, the $i$-th row and the $i$-th column together contain
all elements of $S$. Show that:

  (a) there is no silver matrix for $n = 1997$;

  (b) silver matrices exist for infinitely many values of $n$.
-/

namespace Imo1997P4

/-- An `n × n` matrix `M` is a *silver matrix* if its entries come from
`S = {1, …, 2n - 1}` and, for each `i`, the `i`-th row and the `i`-th column
together contain all of `S`. -/
def SilverMatrix (n : ℕ) (M : Fin n → Fin n → ℕ) : Prop :=
  (∀ i j, M i j ∈ Finset.Icc 1 (2 * n - 1)) ∧
  (∀ i, (Finset.univ.image (fun j ↦ M i j) ∪ Finset.univ.image (fun j ↦ M j i))
          = Finset.Icc 1 (2 * n - 1))

problem imo1997_p4 :
    (¬ ∃ M : Fin 1997 → Fin 1997 → ℕ, SilverMatrix 1997 M) ∧
    {n : ℕ | ∃ M : Fin n → Fin n → ℕ, SilverMatrix n M}.Infinite := by
  sorry

end Imo1997P4
