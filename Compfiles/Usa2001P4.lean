/-
Copyright (c) 2024 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Geometry.Euclidean.Basic
import Mathlib.Geometry.Euclidean.Sphere.Basic
import Mathlib.Geometry.Euclidean.Triangle

import ProblemExtraction

problem_file { tags := [.Geometry] }

/-!
# Usa Mathematical Olympiad 2001, Problem 4

Let ABC be a triangle and P be any point such that PA, PB, PC
are the sides of an obtuse triangle, with PA the longest side.
Prove that ∠BAC is acute.
-/

namespace Imo2001P4

open scoped EuclideanGeometry

problem imo2001_p4
    (A B C P X Y Z: EuclideanSpace ℝ (Fin 2))
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hXYZ : AffineIndependent ℝ ![X, Y, Z])
    (hPA : dist X Y = dist P A)
    (hPB : dist Y Z = dist P B)
    (hPC : dist Z X = dist P C)
    (hObtuse : Real.pi / 2 < ∠ X Z Y)
    : ∠ B A C < Real.pi / 2 := by
  sorry
