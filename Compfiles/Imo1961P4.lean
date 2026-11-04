/-

Copyright (c) 2026 The Compfiles Contributors. All rights reserved.

Released under Apache 2.0 license as described in the file LICENSE.

Authors: Thomas Hirtz, Farzad Jafarrahmani, Abdelmouksit SAGUENI.

-/

module

public import Mathlib
public import ProblemExtraction

@[expose] public section

problem_file {
  tags := [.Geometry, .Inequality]
}

/-!

# International Mathematical Olympiad 1961, Problem 4

In the interior of triangle `P₁P₂P₃` a point `P` is given. Let `Q₁,Q₂,Q₃`
be the intersections of `PP₁, PP₂, PP₃` with the opposing edges of triangle
`P₁P₂P₃`. Prove that among the ratios `PP₁/PQ₁`, `PP₂/PQ₂`, `PP₃/PQ₃`
there exists one not larger than 2 and one not smaller than 2.

Raw formalization was produced by SAGE, we had to adapt variables and notations to comply with compfiles and Mathlib conventions.
Paper: https://arxiv.org/abs/2609.35790

-/

namespace Imo1961P4

open Set Affine EuclideanGeometry Module

variable {V Pt : Type*}
variable [NormedAddCommGroup V]
variable [InnerProductSpace ℝ V]
variable [MetricSpace Pt]
variable [NormedAddTorsor V Pt]
variable [Fact (finrank ℝ V = 2)]

problem imo1961_p4
    (T : Affine.Triangle ℝ Pt)
    (P : Pt)
    (h_interior : P ∈ T.interior) :
    ∃ Q₁ Q₂ Q₃ : Pt,
      Wbtw ℝ (T.points 1) Q₁ (T.points 2) ∧
      Wbtw ℝ (T.points 2) Q₂ (T.points 0) ∧
      Wbtw ℝ (T.points 0) Q₃ (T.points 1) ∧
      Q₁ ∈ affineSpan ℝ ({P, T.points 0} : Set Pt) ∧
      Q₂ ∈ affineSpan ℝ ({P, T.points 1} : Set Pt) ∧
      Q₃ ∈ affineSpan ℝ ({P, T.points 2} : Set Pt) ∧
      P ≠ Q₁ ∧
      P ≠ Q₂ ∧
      P ≠ Q₃ ∧
      (dist P (T.points 0) / dist P Q₁ ≤ 2 ∨
        dist P (T.points 1) / dist P Q₂ ≤ 2 ∨
        dist P (T.points 2) / dist P Q₃ ≤ 2) ∧
      (2 ≤ dist P (T.points 0) / dist P Q₁ ∨
        2 ≤ dist P (T.points 1) / dist P Q₂ ∨
        2 ≤ dist P (T.points 2) / dist P Q₃) := by
  sorry

end Imo1961P4
