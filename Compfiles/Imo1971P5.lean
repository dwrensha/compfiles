/-
Copyright (c) 2024 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Geometry.Euclidean.Basic
import Mathlib.Geometry.Euclidean.Triangle

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Olympiad 1971, Problem 5

Prove that for every natural number m there exists a finite set S of
points in the plane with the following property:
For every point s in S, there are exactly m points which are at a unit
distance from s.
-/

namespace Imo1971P5

open scoped EuclideanGeometry

abbrev Pt := EuclideanSpace ℝ (Fin 2)

problem imo1971_p5 (m : ℕ) :
    ∃ S : Set Pt, S.Nonempty ∧ S.Finite ∧
      ∀ s ∈ S, Nat.card {t | dist s t = 1} = m := by
  -- https://prase.cz/kalva/imo/isoln/isoln715.html
  sorry


end Imo1971P5
