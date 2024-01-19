/-
Copyright (c) 2020 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 1961, Problem 1.

Given constants a and b, solve the system of equations

             x + y + z = a
          x² + y² + z² = b²
                    xy = z²

for x,y,z. Give the conditions that a and b must satisfy so that
the solutions x,y,z are distinct positive numbers.
-/

namespace Imo1961P1

abbrev IsSolution (a b x y z : ℝ) : Prop :=
    x + y + z = a ∧
    x^2 + y^2 + z^2 = b^2 ∧
    x * y = z^2

determine xyz_of_ab (a b : ℝ) : Set (ℝ × ℝ × ℝ) :=
  { p | let ⟨x,y,z⟩ := p
        z = (a^2 - b^2) / (2 * a) ∧
        ∀ m, (m - x) * (m - y) =
              m^2 - (a^2 + b^2) / (2 * a) * m + ((a^2 - b^2) / (2 * a))^2 }

determine ab_that_make_xyz_positive_distinct : Set (ℝ × ℝ) :=
  { q | let ⟨a,b⟩ := q
        b^2 < a^2 ∧ a^2 < 3 * b ^ 2 }

problem imo1961_p1a (a b x y z : ℝ) :
    ⟨x,y,z⟩ ∈ xyz_of_ab a b ↔ IsSolution a b x y z := sorry

problem imo1961_p1b (a b : ℝ) :
    ⟨a,b⟩ ∈ ab_that_make_xyz_positive_distinct ↔
      (∀ x y z, IsSolution a b x y z → 0 < x ∧ 0 < y ∧ 0 < z ∧ [x,y,z].Nodup) := by
  sorry

