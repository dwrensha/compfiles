/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.Midpoint
import Mathlib.Geometry.Euclidean.Basic
import Mathlib.Geometry.Euclidean.Triangle

import MathPuzzles.Meta.Attributes

#[problem_setup]/-!
Bulgarian Mathematical Olympiad 1998, Problem 2

A convex quadrilateral ABCD has AD = CD and ∠DAB = ∠ABC < 90°.
The line through D and the midpoint of BC intersects line AB
in point E. Prove that ∠BEC = ∠DAC. (Note: The problem is valid
without the assumption ∠ABC < 90°.)
-/

#[problem_setup] namespace Bulgaria1998Q2

#[problem_setup] open EuclideanGeometry

problem bulgaria1998_q2
    (A B C D E M: EuclideanSpace ℝ (Fin 2))
    (H1 : dist D A = dist D C)
    (H2 : ∠ D A B = ∠ A B C)
    (H3 : M = midpoint ℝ B C) :
    ∠ B E C = ∠ D A C := by
  let x := ∠ D A C
  have : ∠ D A C = ∠ D C A := EuclideanGeometry.angle_eq_angle_of_dist_eq H1
  let y := ∠ C A B
  have : ∠ A B C = x + y := sorry
  sorry
