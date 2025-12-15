/-
Copyright (c) 2025 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ansar Azharov
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Olympiad 1989, Problem 1

Prove that the set {1, 2, . . . , 1989} can be expressed as the disjoint union of
subsets Aᵢ (i = 1, 2, . . . , 117) such that:

(i) Each Aᵢ contains 17 elements;
(ii) The sum of all the elements in each Aᵢ is the same.
-/

namespace Imo1989P1

abbrev S := Finset.Icc 1 1989

problem imo1989_p1 : ∃ (A : Fin 117 → Set ℕ),
    S = ⨆ i : Fin 117, A i ∧ ∀ i j, i ≠ j →
    Disjoint (A i) (A j) ∧
    Set.ncard (A i) = 17 ∧
    ∑ᶠ a ∈ A i, a = ∑ᶠ a ∈ A j, a := sorry

end Imo1989P1
