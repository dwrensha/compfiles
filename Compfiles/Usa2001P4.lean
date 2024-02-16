/-
Copyright (c) 2024 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.NormedSpace.PiLp
import Mathlib.Geometry.Euclidean.Basic
import Mathlib.Geometry.Euclidean.Inversion.Basic
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

snip begin

lemma lemma1 (a b c d : ℝ) : a * c + b * d ≤ Real.sqrt ((a^2 + b^2) * (c^2 + d^2)) := by
  let v1 : EuclideanSpace ℝ (Fin 2) := ![a, b]
  let v2 : EuclideanSpace ℝ (Fin 2) := ![c, d]
  have h1 := abs_real_inner_le_norm v1 v2
  simp [EuclideanSpace.norm_eq] at h1
  have hab : 0 ≤ (a ^ 2 + b ^ 2) := by positivity
  rw [←Real.sqrt_mul hab] at h1
  have h2 : a * c + b * d ≤ |a * c + b * d| := le_abs_self _
  exact h2.trans h1

lemma lemma2 {a b c : ℝ} (ha : 0 < a) (hab : a < b) (hc : 0 < c) :
    Real.sqrt (a * c) < Real.sqrt (b * c) := by
  have h1 : 0 < a * c := Real.mul_pos ha hc
  suffices H : a * c < b * c from Real.sqrt_lt_sqrt (le_of_lt h1) H
  nlinarith

snip end

problem imo2001_p4
    (A B C P X Y Z : EuclideanSpace ℝ (Fin 2))
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hXYZ : AffineIndependent ℝ ![X, Y, Z])
    (hPA : dist X Y = dist P A)
    (hPB : dist Y Z = dist P B)
    (hPC : dist Z X = dist P C)
    (hObtuse : Real.pi / 2 < ∠ X Z Y)
    : ∠ B A C < Real.pi / 2 := by
  -- https://web.evanchen.cc/exams/USAMO-2001-notes.pdf
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

  have h17 : X ≠ Y := fun H ↦ by
    rw [show X = ![X, Y, Z] 0 by rfl, show Y = ![X, Y, Z] 1 by rfl] at H
    have := AffineIndependent.injective hXYZ H
    aesop
  have h18 : 0 < dist X Y := dist_pos.mpr h17

  rw [dist_comm Z X] at hPC

  have h1 : (dist Y Z)^2 + (dist X Z)^2 < (dist X Y)^2 := by
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
    have h13 : 2 * dist X Z * dist Y Z * Real.cos (∠ X Z Y) < 0 := by
      have h14 : 0 < 2 * dist X Z * dist Y Z := by positivity
      exact mul_neg_iff.mpr (Or.inl ⟨h14, h3⟩)

    calc _ < _ := by linarith
         _ = _ := h2.symm
  rw [hPA, hPB, hPC] at h1
  rw [hPA] at h18; rw [hPC] at h11; rw [hPB] at h12
  clear! X Y Z
  have ptolemy := EuclideanGeometry.mul_dist_le_mul_dist_add_mul_dist P B A C
  have h2 := lemma1 (dist P B) (dist P C) (dist A C) (dist B A)
  rw [mul_comm (dist P C)] at h2
  have h20 : 0 < dist P B ^ 2 + dist P C ^ 2 := by positivity
  have h42 : 0 < dist B A := by
    have h60 : B ≠ A := fun H ↦ by
      rw [show B = ![A, B, C] 1 by rfl, show A = ![A, B, C] 0 by rfl] at H
      have := AffineIndependent.injective hABC H
      aesop
    exact dist_pos.mpr h60
  have h43 : 0 < dist A C := by
    have h60 : A ≠ C := fun H ↦ by
      rw [show A = ![A, B, C] 0 by rfl, show C = ![A, B, C] 2 by rfl] at H
      have := AffineIndependent.injective hABC H
      have hne : (0 : Fin 3) ≠ (2 : Fin 3) := by decide
      aesop
    exact dist_pos.mpr h60
  have h21 : 0 < dist A C ^ 2 + dist B A ^ 2 := by positivity
  have h22 := lemma2 h20 h1 h21
  have h23 := calc _ ≤ _ := ptolemy
                   _ ≤ _ := h2
                   _ < _ := h22
  have h24 : 0 ≤ dist P A ^ 2 := by positivity
  rw [Real.sqrt_mul h24] at h23
  rw [Real.sqrt_sq dist_nonneg] at h23
  replace h23 : dist B C < Real.sqrt (dist A C ^ 2 + dist B A ^ 2) :=
    (mul_lt_mul_left h18).mp h23
  replace h23 : dist B C ^2 < (Real.sqrt (dist A C ^ 2 + dist B A ^ 2))^2 :=
    pow_lt_pow_left h23 dist_nonneg (by norm_num)
  rw [Real.sq_sqrt (by positivity)] at h23
  have h30 := EuclideanGeometry.law_cos B A C
  simp only [←sq] at h30
  rw [h30] at h23; clear h30
  rw [dist_comm C A] at h23
  have h31 : 0 < 2 * dist B A * dist A C * Real.cos (∠ B A C) := by linarith only [h23]
  have h44 : 0 < 2 * dist B A * dist A C := by positivity
  have h45 : 0 < Real.cos (∠ B A C) := (mul_pos_iff_of_pos_left h44).mp h31
  by_contra! H
  have h48 : ∠ B A C ≤ Real.pi + Real.pi / 2 := by
    have : ∠ B A C ≤ Real.pi := EuclideanGeometry.angle_le_pi B A C
    linarith
  have h49 : Real.cos (∠ B A C) ≤ 0 := Real.cos_nonpos_of_pi_div_two_le_of_le H h48
  exact not_lt.mpr h49 h45
