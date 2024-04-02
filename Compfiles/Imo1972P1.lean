/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Olympiad 1972, Problem 1

Prove that from a set of ten distinct two-digit numbers (in
decimal), it is possible to select two disjoint subsets whose
members have the same sum.
-/

namespace Imo1972P1

open scoped BigOperators

problem imo1972_p1 (S : Finset ℕ)
    (Scard : S.card = 10)
    (Sdigits : ∀ s ∈ S, (Nat.digits 10 s).length = 2) :
    ∃ S1 S2 : Finset ℕ,S1 ⊆ S ∧ S2 ⊆ S ∧
       Disjoint S1 S2 ∧ ∑ s in S1, s = ∑ s in S2, s :=
  by sorry
