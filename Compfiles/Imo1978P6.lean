/-
Copyright (c) 2025 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InternLM-MATH LEAN Formalizer v0.1
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Olympiad 1978, Problem 6

An international society has its members from six different countries.
The list of members has 1978 names, numbered $1, 2, \ldots, 1978$.
Prove that there is at least one member whose number is
the sum of the numbers of two (not necessarily distinct) members from his own country.
-/

namespace Imo1978P6

problem imo1978_p6 (n : ℕ) (hn : n = 1978) (C : Fin n → Fin 6) :
  ∃ j : Fin n, ∃ i : Fin n, ∃ k : Fin n,
    C i = C j ∧
    C j = C k ∧
    (i:ℕ) + 1 + (k:ℕ) + 1 = (j:ℕ) + 1 := by sorry


end Imo1978P6
