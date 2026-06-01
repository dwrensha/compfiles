/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: sjfhsjfh
-/
import Mathlib

import ProblemExtraction

problem_file { tags := [.Geometry] }

/-!
# China Pre-CMO (National High School Math League, Second Round) 1986, Problem 2

已知锐角三角形 `ABC` 的外接圆半径为 `R`, 点 `D`, `E`, `F` 分别在边 `BC`, `CA`, `AB` 上。
求证: `AD`, `BE`, `CF` 是 `△ABC` 的三条高的充要条件是
`S = (R/2)(EF + FD + DE)`, 其中 `S` 是 `△ABC` 的面积。

In an acute triangle `ABC` with circumradius `R`, points `D`, `E`, `F` lie on sides
`BC`, `CA`, `AB` respectively.
Prove that `AD`, `BE`, `CF` are the three altitudes of `△ABC` if and only if
`S = (R/2)(EF + FD + DE)`, where `S` is the area of `△ABC`.
-/

attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

variable {V : Type*} {Pt : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace Pt]
variable [NormedAddTorsor V Pt]

open FiniteDimensional
open Module
open EuclideanGeometry
open Affine

open scoped EuclideanGeometry Real

namespace ChinaPre1986P2

noncomputable def triArea (X Y Z : Pt) : ℝ :=
  1 / 2 * Real.sqrt (‖Y -ᵥ X‖ ^ 2 * ‖Z -ᵥ X‖ ^ 2 - (inner ℝ (Y -ᵥ X) (Z -ᵥ X)) ^ 2)

problem chinaPre1986_p2 [Fact (finrank ℝ V = 2)]
  (A B C D E F : Pt)
  (R S : ℝ)
  (h_tri : AffineIndependent ℝ ![A, B, C])
  (h_acuteA : ∠ B A C < π / 2)
  (h_acuteB : ∠ C B A < π / 2)
  (h_acuteC : ∠ A C B < π / 2)
  (hD : Wbtw ℝ B D C)
  (hE : Wbtw ℝ C E A)
  (hF : Wbtw ℝ A F B)
  (h_area : triArea A B C = S)
  (h_circumR : dist B C * dist C A * dist A B = 4 * R * S)
  : let t : Triangle ℝ Pt := ⟨_, h_tri⟩
    (line[ℝ, A, D] = t.altitude 0 ∧ line[ℝ, B, E] = t.altitude 1
      ∧ line[ℝ, C, F] = t.altitude 2)
    ↔ S = R / 2 * (dist E F + dist F D + dist D E) := by
  sorry

end ChinaPre1986P2
