/-
Copyright (c) 2026 The Compfiles Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Geometry.Euclidean.Angle.Sphere
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# USA Mathematical Olympiad 1990, Problem 5

ABC is acute-angled. The circle diameter AB meets the altitude from C
at P and Q. The circle diameter AC meets the altitude from B at R and S.
Show that P, Q, R and S lie on a circle.
-/

namespace Usa1990P5

open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {Pt : Type*} [MetricSpace Pt] [NormedAddTorsor V Pt]

snip begin

/-- A point `X` on the circle with diameter `AB` sees the segment `AB`
under a right angle: `⟪X -ᵥ A, X -ᵥ B⟫ = 0` (Thales' theorem). -/
lemma inner_vsub_vsub_eq_zero_of_mem_ofDiameter {A B X : Pt}
    (h : X ∈ EuclideanGeometry.Sphere.ofDiameter A B) :
    ⟪X -ᵥ A, X -ᵥ B⟫ = 0 := by
  rw [← EuclideanGeometry.Sphere.angle_eq_pi_div_two_iff_mem_sphere_ofDiameter] at h
  rw [EuclideanGeometry.angle,
    ← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two] at h
  rw [← neg_vsub_eq_vsub_rev X A, ← neg_vsub_eq_vsub_rev X B,
    inner_neg_left, inner_neg_right, neg_neg] at h
  exact h

/-- The key computation: if `X` lies on the circle with diameter `AB` and on
the altitude from `C` (the line through `C` perpendicular to `AB`), then
`dist A X ^ 2 = ⟪B -ᵥ A, C -ᵥ A⟫`. -/
lemma dist_sq_eq_inner (A B C X : Pt)
    (hX₁ : ⟪X -ᵥ A, X -ᵥ B⟫ = 0) (hX₂ : ⟪X -ᵥ C, B -ᵥ A⟫ = 0) :
    dist A X ^ 2 = ⟪B -ᵥ A, C -ᵥ A⟫ := by
  rw [dist_eq_norm_vsub', ← real_inner_self_eq_norm_sq]
  rw [← vsub_sub_vsub_cancel_right X B A, inner_sub_right, sub_eq_zero] at hX₁
  rw [← vsub_sub_vsub_cancel_right X C A, inner_sub_left, sub_eq_zero] at hX₂
  rw [hX₁, hX₂, real_inner_comm]

snip end

problem usa1990_p5 (A B C P Q R S : Pt)
    (hP₁ : P ∈ EuclideanGeometry.Sphere.ofDiameter A B)
    (hP₂ : ⟪P -ᵥ C, B -ᵥ A⟫ = 0)
    (hQ₁ : Q ∈ EuclideanGeometry.Sphere.ofDiameter A B)
    (hQ₂ : ⟪Q -ᵥ C, B -ᵥ A⟫ = 0)
    (hR₁ : R ∈ EuclideanGeometry.Sphere.ofDiameter A C)
    (hR₂ : ⟪R -ᵥ B, C -ᵥ A⟫ = 0)
    (hS₁ : S ∈ EuclideanGeometry.Sphere.ofDiameter A C)
    (hS₂ : ⟪S -ᵥ B, C -ᵥ A⟫ = 0) :
    EuclideanGeometry.Cospherical {P, Q, R, S} := by
  -- Following https://prase.cz/kalva/usa/usoln/usol905.html, we show that
  -- all four points are at the same distance from `A`.
  have hP := dist_sq_eq_inner A B C P
    (inner_vsub_vsub_eq_zero_of_mem_ofDiameter hP₁) hP₂
  have hQ := dist_sq_eq_inner A B C Q
    (inner_vsub_vsub_eq_zero_of_mem_ofDiameter hQ₁) hQ₂
  have hR := dist_sq_eq_inner A C B R
    (inner_vsub_vsub_eq_zero_of_mem_ofDiameter hR₁) hR₂
  have hS := dist_sq_eq_inner A C B S
    (inner_vsub_vsub_eq_zero_of_mem_ofDiameter hS₁) hS₂
  rw [real_inner_comm (B -ᵥ A) (C -ᵥ A)] at hR hS
  -- hP hQ hR hS : dist A · ^ 2 = ⟪B -ᵥ A, C -ᵥ A⟫
  have heq : ∀ X : Pt, dist A X ^ 2 = ⟪B -ᵥ A, C -ᵥ A⟫ → dist X A = dist A P :=
    fun X hX ↦ dist_comm X A ▸
      (pow_left_inj₀ (n := 2) dist_nonneg dist_nonneg two_ne_zero).mp (hX.trans hP.symm)
  refine ⟨A, dist A P, fun X hX ↦ ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hX
  rcases hX with h | h | h | h
  · rw [h]; exact heq P hP
  · rw [h]; exact heq Q hQ
  · rw [h]; exact heq R hR
  · rw [h]; exact heq S hS

end Usa1990P5
