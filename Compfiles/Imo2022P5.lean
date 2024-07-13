/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Olympiad 2022, Problem 5

Determine all possible triples of positive integers a,b,p that satisfy

  aᵖ = b! + p

where p is prime.

-/

namespace Imo2022P5

determine solution_set : Set (ℕ × ℕ × ℕ) := { ⟨2,2,2⟩, ⟨3,4,3⟩ }

problem imo2022_p5 (a b p : ℕ) (ha : 0 < a) (hb : 0 < b) (hp : p.Prime) :
    ⟨a,b,p⟩ ∈ solution_set ↔ a^p = Nat.factorial b + p := by
  constructor
  · intro h
    simp only [Set.mem_singleton_iff, Set.mem_insert_iff] at h
    aesop
  · sorry


end Imo2022P5
