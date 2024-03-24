/-
Copyright (c) 2023 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 2010, Problem 3

Determine all functions g : ℤ>0 → ℤ>0 such that

               (g(m) + n)(g(n) + m)

is always a perfect square.
-/

namespace Imo2010P3

abbrev PosInt : Type := { x : ℤ // 0 < x }

notation "ℤ>0" => PosInt

determine SolutionSet : Set (ℤ>0 → ℤ>0) := { f | f = id ∨ ∃ c, ∀ x, f x = x + c }

problem imo2010_p3 (g : ℤ>0 → ℤ>0) :
    g ∈ SolutionSet ↔ ∀ m n, IsSquare ((g m + n) * (g n + m)) := by
  constructor
  · rintro (rfl | ⟨c, hc⟩) m n
    · use m + n; rw [id, id]; ac_rfl
    · use m + n + c; rw [hc m, hc n]; ac_rfl
  · sorry
