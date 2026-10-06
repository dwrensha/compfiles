/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Hirtz, Farzad Jafarrahmani, Abdelmouksit Sagueni
-/

module

public import Mathlib
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 1974, Problem 2

In the triangle `ABC`, prove that there is a point `D` on side `AB` such that
`CD` is the geometric mean of `AD` and `DB` if and only if
`sin A * sin B ≤ sin² (C / 2)`.

Raw formalization was produced by SAGE, we had to adapt variables and notations to comply with compfiles and Mathlib conventions.
Paper: https://arxiv.org/abs/2609.35790
-/

open Affine EuclideanGeometry Module
open scoped Real

namespace Imo1974P2

variable {V Pt : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace Pt]
variable [NormedAddTorsor V Pt]
variable [Fact (finrank ℝ V = 2)]

problem imo1974_p2
    (A B C : Pt)
    (affineIndependent_ABC : AffineIndependent ℝ ![A, B, C]) :
    (∃ D : Pt,
        Wbtw ℝ A D B ∧
          dist C D = Real.sqrt (dist A D * dist D B)) ↔
      Real.sin (∠ B A C) * Real.sin (∠ A B C) ≤
        Real.sin (∠ A C B / 2) ^ 2 := by
  sorry

end Imo1974P2
