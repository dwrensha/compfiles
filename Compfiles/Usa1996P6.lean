/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karl Mehltretter
-/

import Mathlib.Data.Int.Basic

import ProblemExtraction

problem_file { tags := [.Combinatorics, .NumberTheory] }

/-!
# USA Mathematical Olympiad 1996, Problem 6

Determine, with proof, whether there is a subset X of the integers with
the following property: for any integer n there is exactly one pair (a, b)
of elements of X satisfying a + 2b = n.
-/

namespace Usa1996P6

def UniqueRepresentationSet (X : Set ℤ) : Prop :=
  ∀ n : ℤ, ∃! p : ℤ × ℤ,
    p.1 ∈ X ∧ p.2 ∈ X ∧ p.1 + 2 * p.2 = n

determine does_exist : Bool := true

problem usa1996_p6 :
    does_exist ↔ ∃ X : Set ℤ, UniqueRepresentationSet X := by
  sorry

end Usa1996P6
