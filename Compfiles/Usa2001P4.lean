/-
Copyright (c) 2024 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Geometry.Euclidean.Basic
import Mathlib.Geometry.Euclidean.Inversion.Basic
import Mathlib.Geometry.Euclidean.Sphere.Basic
import Mathlib.Geometry.Euclidean.Triangle

import ProblemExtraction

problem_file { tags := [.Geometry] }

/-!
# USA Mathematical Olympiad 2001, Problem 4

Let ABC be a triangle and P be any point such that PA, PB, PC
are the sides of an obtuse triangle, with PA the longest side.
Prove that ∠BAC is acute.
-/

namespace Usa2001P4

open scoped EuclideanGeometry

snip begin

lemma lemma1 (a b c d : ℝ) : a * c + b * d ≤ Real.sqrt (a^2 + b^2) * Real.sqrt (c^2 + d^2) := by
  let v1 : EuclideanSpace ℝ (Fin 2) := !₂[a, b]
  let v2 : EuclideanSpace ℝ (Fin 2) := !₂[c, d]
  have h2 : a * c + b * d ≤ |a * c + b * d| := le_abs_self _
  have h1 := abs_real_inner_le_norm v1 v2
  simp [EuclideanSpace.norm_eq, v1, v2, inner] at h1
  rw [mul_comm c a, mul_comm d b] at h1
  exact h2.trans h1

snip end

problem usa2001_p4
    (A B C P X Y Z : EuclideanSpace ℝ (Fin 2))
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hXYZ : AffineIndependent ℝ ![X, Y, Z])
    (hPA : dist X Y = dist P A)
    (hPB : dist Y Z = dist P B)
    (hPC : dist Z X = dist P C)
    (hObtuse : Real.pi / 2 < ∠ X Z Y)
    : ∠ B A C < Real.pi / 2 := by
  -- https://web.evanchen.cc/exams/USAMO-2001-notes.pdf
  have h9 : ¬Collinear ℝ {X, Y, Z} := affineIndependent_iff_not_collinear_set.mp hXYZ
  have h11 : 0 < dist X Z := dist_pos.mpr (ne₁₃_of_not_collinear h9)
  have h12 : 0 < dist Y Z := dist_pos.mpr (ne₂₃_of_not_collinear h9)
  have h18 : 0 < dist X Y := dist_pos.mpr (ne₁₂_of_not_collinear h9)

  rw [dist_comm Z X] at hPC

  have h1 : (dist Y Z)^2 + (dist X Z)^2 < (dist X Y)^2 := by
    have h2 := EuclideanGeometry.law_cos X Z Y
    have h3 : Real.cos (∠ X Z Y) < 0 := by
      have h4 : 0 < ∠ X Z Y - Real.pi / 2 := sub_pos.mpr hObtuse
      have h10 : ({X, Y, Z} : Set _) = {X, Z, Y} :=
        congrArg (Set.insert _) (Set.pair_comm _ _)
      have h8 : ¬ Collinear ℝ {X, Z, Y} := by rwa [←h10]
      have h7 : ∠ X Z Y < Real.pi := EuclideanGeometry.angle_lt_pi_of_not_collinear h8
      have h5 : ∠ X Z Y < Real.pi + Real.pi / 2 := by linarith only [h4, h7]
      exact Real.cos_neg_of_pi_div_two_lt_of_lt hObtuse h5
    simp only [←sq] at h2
    have h13 : 2 * dist X Z * dist Y Z * Real.cos (∠ X Z Y) < 0 := by
      have h14 : 0 < 2 * dist X Z * dist Y Z := by positivity
      exact mul_neg_iff.mpr (Or.inl ⟨h14, h3⟩)

    calc _ < _ := by linarith only [h13]
         _ = _ := h2.symm
  rw [hPA, hPB, hPC] at h1
  rw [hPA] at h18; rw [hPC] at h11; rw [hPB] at h12
  clear! X Y Z
  have ptolemy := EuclideanGeometry.mul_dist_le_mul_dist_add_mul_dist P B A C
  have h2 := lemma1 (dist P B) (dist P C) (dist A C) (dist B A)
  rw [mul_comm (dist P C)] at h2
  have h50 : ¬Collinear ℝ {A, B, C} := affineIndependent_iff_not_collinear_set.mp hABC
  have h42 : 0 < dist A B := dist_pos.mpr (ne₁₂_of_not_collinear h50)
  rw [dist_comm] at h42
  have h43 : 0 < dist A C := dist_pos.mpr (ne₁₃_of_not_collinear h50)
  have h23 := calc
    _ ≤ _ := ptolemy
    _ ≤ _ := h2
    _ < Real.sqrt (dist P A ^ 2) * _ :=
          (mul_lt_mul_iff_left₀ (by positivity)).mpr
            (Real.sqrt_lt_sqrt (by positivity) h1)
    _ = dist P A * _ := by rw [Real.sqrt_sq dist_nonneg]
  replace h23 : dist B C < Real.sqrt (dist A C ^ 2 + dist B A ^ 2) :=
    (mul_lt_mul_iff_right₀ h18).mp h23
  replace h23 : dist B C ^2 < (Real.sqrt (dist A C ^ 2 + dist B A ^ 2))^2 :=
    pow_lt_pow_left₀ h23 dist_nonneg (by norm_num)
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
    linarith [EuclideanGeometry.angle_le_pi B A C]
  have h49 : Real.cos (∠ B A C) ≤ 0 := Real.cos_nonpos_of_pi_div_two_le_of_le H h48
  exact not_lt.mpr h49 h45


end Usa2001P4
