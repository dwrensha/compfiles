/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: sjfhsjfh
-/
import Mathlib

import ProblemExtraction

problem_file { tags := [.Geometry] }

/-!
# China Pre-CMO (National High School Math League, Second Round) 1983, Problem 3

在四边形 `ABCD` 中, `△ABD`, `△BCD`, `△ABC` 的面积比是 `3 : 4 : 1`.
点 `M`, `N` 分别在 `AC`, `CD` 上, 满足 `AM : AC = CN : CD`, 并且 `B`, `M`, `N` 三点共线.
求证: `M` 与 `N` 分别是 `AC` 与 `CD` 的中点.

In quadrilateral `ABCD`, the areas of `△ABD`, `△BCD`, `△ABC` are in the ratio `3 : 4 : 1`.
Points `M`, `N` lie on `AC`, `CD` respectively, such that `AM : AC = CN : CD`,
and `B`, `M`, `N` are collinear.
Prove that `M` and `N` are the midpoints of `AC` and `CD` respectively.
-/

open EuclideanGeometry
open FiniteDimensional
open Module

attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

variable {V : Type*} {Pt : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace Pt]
variable [NormedAddTorsor V Pt]

namespace ChinaPre1983P3

/-- Twice the signed area of `△XYZ`, using the 2D cross product `(Y−X) × (Z−X)`. -/
noncomputable def triArea (X Y Z : Pt) : ℝ :=
  1 / 2 * Real.sqrt (‖Y -ᵥ X‖ ^ 2 * ‖Z -ᵥ X‖ ^ 2 - (inner ℝ (Y -ᵥ X) (Z -ᵥ X)) ^ 2)

problem chinaPre1983_p3 [Fact (finrank ℝ V = 2)]
  (A B C D M N : Pt)
  (h_nondeg : triArea A B C > 0)
  (h_areaABD : triArea A B D = 3 * triArea A B C)
  (h_areaBCD : triArea B C D = 4 * triArea A B C)
  (h_ratio : ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 ∧ M -ᵥ A = r • (C -ᵥ A) ∧ N -ᵥ C = r • (D -ᵥ C))
  (h_coll : Collinear ℝ {B, M, N})
  : M = midpoint ℝ A C ∧ N = midpoint ℝ C D := by
  obtain ⟨r, ⟨hrl, hrr, hrM, hrN⟩⟩ := h_ratio
  rewrite [← eq_vadd_iff_vsub_eq] at hrM hrN; subst hrM hrN
  suffices h : r = 1 / 2 by
    simp only [h, one_div, midpoint, AffineMap.lineMap, invOf_eq_inv,
      LinearMap.coe_toAffineMap, LinearMap.coe_smulRight, LinearMap.id_coe,
      AffineMap.vadd_apply, AffineMap.const_apply, and_self, id_eq]
  sorry

end ChinaPre1983P3
