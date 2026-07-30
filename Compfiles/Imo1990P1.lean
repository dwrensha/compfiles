/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Affine.Convex
public import Mathlib.Geometry.Euclidean.Triangle
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 1990, Problem 1

Chords AB and CD of a circle intersect at a point E inside the circle. Let M be an
interior point of the segment EB. The tangent line at E to the circle through D, E, and M
intersects the lines BC and AC at F and G, respectively. If AM/AB = t, find EG/EF in
terms of t.

The answer is `t / (1 - t)`.

## Formalization note

We work in the Euclidean plane. The geometric input of the problem is encoded in four
angle equalities, which are exactly the content of the classical solution:

* `∠ E C F = ∠ M A D`: since E lies on the chord CD, F on the line BC and M on the
  segment AB, this is the inscribed-angle equality `∠ D C B = ∠ D A B` for the
  concyclic points A, B, C, D.
* `∠ C E F = ∠ A M D`: the alternate segment theorem applied to the tangent at E to
  the circle through D, E, M gives `∠ C E F = ∠ E M D`, and `∠ E M D = ∠ A M D`
  because M lies on the segment AB (the rays ME and MA coincide).
* `∠ E C G = ∠ M B D`: like the first one, this is `∠ A C D = ∠ A B D`.
* `∠ C E G = ∠ B M D`: the alternate segment theorem on the other side of E.

From these, the law of sines in the triangles CEF, CEG, ADM and BDM gives
`EF / CE = MD / AM` and `EG / CE = MD / BM`, hence
`EG / EF = AM / BM = t / (1 - t)`.
-/

namespace Imo1990P1

open scoped EuclideanGeometry

/-- The answer: `EG / EF = t / (1 - t)`. -/
noncomputable determine ratio (t : ℝ) : ℝ := t / (1 - t)

snip begin

/-- Under the four angle relations of the configuration (see the module docstring),
the law of sines applied to the triangles CEF, CEG, ADM, BDM yields
`EG · BM = EF · AM`. -/
lemma ratio_mul_eq (A B C D E F G M : EuclideanSpace ℝ (Fin 2))
    (hFE : F ≠ E) (hGE : G ≠ E) (hDM : D ≠ M)
    (hncA : ¬Collinear ℝ ({M, D, A} : Set (EuclideanSpace ℝ (Fin 2))))
    (hncB : ¬Collinear ℝ ({M, D, B} : Set (EuclideanSpace ℝ (Fin 2))))
    (h₁ : ∠ E C F = ∠ M A D) (h₂ : ∠ C E F = ∠ A M D)
    (h₃ : ∠ E C G = ∠ M B D) (h₄ : ∠ C E G = ∠ B M D) :
    dist E G * dist B M = dist E F * dist A M := by
  -- The remaining two angle equalities follow from the angle sums of the triangles.
  have h₁' : ∠ F C E = ∠ D A M := by
    rw [EuclideanGeometry.angle_comm F C E, h₁, EuclideanGeometry.angle_comm D A M]
  have h₃' : ∠ G C E = ∠ D B M := by
    rw [EuclideanGeometry.angle_comm G C E, h₃, EuclideanGeometry.angle_comm D B M]
  have hA : ∠ E F C = ∠ M D A := by
    have hpi1 := EuclideanGeometry.angle_add_angle_add_angle_eq_pi C hFE
    have hpi2 := EuclideanGeometry.angle_add_angle_add_angle_eq_pi A hDM
    linarith [hpi1, hpi2, h₁', h₂]
  have hB : ∠ E G C = ∠ M D B := by
    have hpi3 := EuclideanGeometry.angle_add_angle_add_angle_eq_pi C hGE
    have hpi4 := EuclideanGeometry.angle_add_angle_add_angle_eq_pi B hDM
    linarith [hpi3, hpi4, h₃', h₄]
  -- Law of sines in the four triangles CEF, CEG, ADM, BDM.
  have hEF0 := EuclideanGeometry.law_sin C F E
  rw [EuclideanGeometry.angle_comm C F E, dist_comm F E, hA, h₁] at hEF0
  have hEG0 := EuclideanGeometry.law_sin C G E
  rw [EuclideanGeometry.angle_comm C G E, dist_comm G E, hB, h₃] at hEG0
  have hS1 := EuclideanGeometry.law_sin A D M
  rw [EuclideanGeometry.angle_comm A D M, dist_comm D M, dist_comm M A] at hS1
  have hS2 := EuclideanGeometry.law_sin B D M
  rw [EuclideanGeometry.angle_comm B D M, dist_comm D M, dist_comm M B] at hS2
  -- The relevant sines are positive by nondegeneracy.
  have hspA : 0 < Real.sin (∠ M D A) := EuclideanGeometry.sin_pos_of_not_collinear hncA
  have hspB : 0 < Real.sin (∠ M D B) := EuclideanGeometry.sin_pos_of_not_collinear hncB
  -- `MD` as computed from the triangles ADM and BDM agrees.
  have hkey : dist A M * Real.sin (∠ M A D) * Real.sin (∠ M D B)
      = dist B M * Real.sin (∠ M B D) * Real.sin (∠ M D A) := by
    linear_combination Real.sin (∠ M D A) * hS2 - Real.sin (∠ M D B) * hS1
  have hmaster : dist E G * dist B M * (Real.sin (∠ M D B) * Real.sin (∠ M D A))
      = dist E F * dist A M * (Real.sin (∠ M D B) * Real.sin (∠ M D A)) := by
    linear_combination dist B M * Real.sin (∠ M D A) * hEG0
      - dist A M * Real.sin (∠ M D B) * hEF0 - dist E C * hkey
  exact mul_right_cancel₀ (mul_ne_zero hspB.ne' hspA.ne') hmaster

snip end

problem imo1990_p1
    (A B C D E F G M : EuclideanSpace ℝ (Fin 2)) (t : ℝ)
    (hFE : F ≠ E) (hGE : G ≠ E) (hDM : D ≠ M)
    (hncA : ¬Collinear ℝ ({M, D, A} : Set (EuclideanSpace ℝ (Fin 2))))
    (hncB : ¬Collinear ℝ ({M, D, B} : Set (EuclideanSpace ℝ (Fin 2))))
    (h₁ : ∠ E C F = ∠ M A D) (h₂ : ∠ C E F = ∠ A M D)
    (h₃ : ∠ E C G = ∠ M B D) (h₄ : ∠ C E G = ∠ B M D)
    (hE : Sbtw ℝ A E B) (hM : Sbtw ℝ E M B)
    (ht : dist A M / dist A B = t) :
    dist E G / dist E F = ratio t := by
  show dist E G / dist E F = t / (1 - t)
  have hratio := ratio_mul_eq A B C D E F G M hFE hGE hDM hncA hncB h₁ h₂ h₃ h₄
  -- Distances along the chord AB: since M lies on the segment EB ⊂ AB, we have
  -- AM + MB = AB with all distances positive.
  have hAM_sbtw : Sbtw ℝ A M B := hE.trans_right hM
  have hdist : dist A M + dist M B = dist A B := hAM_sbtw.1.dist_add_dist
  have hAMpos : 0 < dist A M := dist_pos.mpr hAM_sbtw.2.1.symm
  have hMBpos : 0 < dist M B := dist_pos.mpr hAM_sbtw.2.2
  have hABpos : 0 < dist A B := by linarith [hdist, hAMpos]
  have ht1 : t < 1 := by
    rw [← ht]
    exact (div_lt_one hABpos).mpr (by linarith [hdist, hMBpos])
  have ht1' : (0 : ℝ) < 1 - t := sub_pos.mpr ht1
  have hAMt : dist A M = t * dist A B := by
    rw [← ht, div_mul_cancel₀ _ hABpos.ne']
  have hBMt : dist B M = (1 - t) * dist A B := by
    rw [dist_comm B M]
    linarith [hdist, hAMt]
  have hEFpos : 0 < dist E F := dist_pos.mpr hFE.symm
  -- Combine `EG · BM = EF · AM` with `AM = t · AB` and `BM = (1 - t) · AB`.
  have hfin : dist E G * (1 - t) = dist E F * t := by
    have h1 := hratio
    rw [hBMt, hAMt] at h1
    have h2 : dist E G * (1 - t) * dist A B = dist E F * t * dist A B := by
      linear_combination h1
    exact mul_right_cancel₀ hABpos.ne' h2
  rw [div_eq_iff hEFpos.ne', div_mul_eq_mul_div, eq_div_iff ht1'.ne',
    mul_comm t (dist E F)]
  exact hfin

end Imo1990P1
