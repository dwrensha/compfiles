/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file

/-!
# International Mathematical Olympiad 2010, Problem 3

Determine all functions g : ℤ>0 → ℤ>0 such that

               (g(m) + n)(g(n) + m)

is always a perfect square.
-/

namespace Imo2010P3

abbrev PosInt : Type := { x : ℤ // 0 < x }

notation "ℤ>0" => PosInt

determine solution_set : Set (ℤ>0 → ℤ>0) := sorry

problem imo2010_p3 (g : ℤ>0 → ℤ>0) :
    g ∈ solution_set ↔ ∀ m n, IsSquare ((g m + n) * (g n + m)) := by
  sorry