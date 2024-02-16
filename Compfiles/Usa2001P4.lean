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
    (A B C P X Y Z : EuclideanSpace ℝ (Fin 2))
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hXYZ : AffineIndependent ℝ ![X, Y, Z])
    (hPA : dist X Y = dist P A)
    (hPB : dist Y Z = dist P B)
    (hPC : dist Z X = dist P C)
    (hObtuse : Real.pi / 2 < ∠ X Z Y)
    : ∠ B A C < Real.pi / 2 := by
  have h1 : (dist Y Z)^2 + (dist Z X)^2 < (dist X Y)^2 := by
    have h2 := EuclideanGeometry.law_cos X Z Y
    have h3 : Real.cos (∠ X Z Y) < 0 := by
      suffices H : 0 < - Real.cos (∠ X Z Y) from neg_pos.mp H
      rw [←Real.sin_sub_pi_div_two]
      have h4 : 0 < ∠ X Z Y - Real.pi / 2 := sub_pos.mpr hObtuse
      have h9 : ¬ Collinear ℝ {X, Y, Z} := affineIndependent_iff_not_collinear_set.mp hXYZ
      have h10 : ({X, Y, Z} : Set _) = {X, Z, Y} := by aesop
      have h8 : ¬ Collinear ℝ {X, Z, Y} := by rwa [←h10]
      have h7 : ∠ X Z Y < Real.pi := EuclideanGeometry.angle_lt_pi_of_not_collinear h8
      have h5 : ∠ X Z Y - Real.pi / 2 < Real.pi := by linarith only [h4, h7]
      exact Real.sin_pos_of_mem_Ioo ⟨h4, h5⟩
    simp only [←sq] at h2
    have h15 : X ≠ Z := fun H ↦ by
      rw [show X = ![X, Y, Z] 0 by rfl, show Z = ![X, Y, Z] 2 by rfl] at H
      have := AffineIndependent.injective hXYZ H
      have hne : (0 : Fin 3) ≠ (2 : Fin 3) := by decide
      aesop
    have h11 : 0 < dist X Z := dist_pos.mpr h15
    have h16 : Y ≠ Z := fun H ↦ by
      rw [show Y = ![X, Y, Z] 1 by rfl, show Z = ![X, Y, Z] 2 by rfl] at H
      have := AffineIndependent.injective hXYZ H
      have hne : (1 : Fin 3) ≠ (2 : Fin 3) := by decide
      aesop
    have h12 : 0 < dist Y Z := dist_pos.mpr h16
    have h13 : 2 * dist X Z * dist Y Z * Real.cos (∠ X Z Y) < 0 := by
      have h14 : 0 < 2 * dist X Z * dist Y Z := by positivity
      exact mul_neg_iff.mpr (Or.inl ⟨h14, h3⟩)
    rw [dist_comm Z X]
    calc _ < _ := by linarith
         _ = _ := h2.symm
  sorry
