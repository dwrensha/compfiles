/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Euclidean.Sphere.Basic
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Finset
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# USA Mathematical Olympiad 1993, Problem 2

The diagonals of a convex quadrilateral meet at right angles at X.
Show that the four points obtained by reflecting X in each of the
sides are cyclic.
-/

namespace Usa1993P2

open EuclideanGeometry
open scoped RealInnerProductSpace

/-- The Euclidean plane. -/
abbrev Pt := EuclideanSpace ℝ (Fin 2)

snip begin

/-- The foot of the perpendicular from the origin to the line through
the points `!₂[p, 0]` and `!₂[0, q]` on the coordinate axes. -/
noncomputable def foot (p q : ℝ) : Pt := !₂[p * q^2 / (p^2 + q^2), p^2 * q / (p^2 + q^2)]

/-- Extensionality for points of the plane. -/
theorem Pt.ext {x y : Pt} (h0 : x 0 = y 0) (h1 : x 1 = y 1) : x = y := by
  apply WithLp.ofLp_injective (p := 2)
  funext i
  fin_cases i <;> assumption

/-- The inner product of two points of the plane, in coordinates. -/
theorem inner_pt (x y : Pt) : ⟪x, y⟫ = x 0 * y 0 + x 1 * y 1 := by
  rw [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, RCLike.inner_apply]
  simp only [conj_trivial]
  ring

/-- The foot `foot p q` lies on the line through `!₂[p, 0]` and `!₂[0, q]`. -/
theorem foot_mem (p q : ℝ) (hpq : p^2 + q^2 ≠ 0) :
    foot p q ∈ affineSpan ℝ ({!₂[p, 0], !₂[0, q]} : Set Pt) := by
  have h : foot p q = AffineMap.lineMap !₂[p, 0] !₂[0, q] (p^2 / (p^2 + q^2)) := by
    rw [AffineMap.lineMap_apply]
    apply Pt.ext
    · simp [foot, PiLp.toLp_apply, vadd_eq_add, vsub_eq_sub]
      field_simp
      ring
    · simp [foot, PiLp.toLp_apply, vadd_eq_add, vsub_eq_sub]
      field_simp
  rw [h]
  exact AffineMap.lineMap_mem_affineSpan_pair _ _ _

/-- The line from the origin to `foot p q` is orthogonal to the line
through `!₂[p, 0]` and `!₂[0, q]`. -/
theorem foot_orth (p q : ℝ) (hpq : p^2 + q^2 ≠ 0) :
    ((0 : Pt) -ᵥ foot p q) ∈
      (affineSpan ℝ ({!₂[p, 0], !₂[0, q]} : Set Pt)).directionᗮ := by
  rw [direction_affineSpan, vectorSpan_pair,
    Submodule.mem_orthogonal_singleton_iff_inner_right, inner_pt]
  simp [foot, vsub_eq_sub]
  field_simp
  ring

/-- The reflection of the origin in the line through `!₂[p, 0]` and
`!₂[0, q]` is twice the foot of the perpendicular from the origin. -/
theorem reflection_zero (p q : ℝ) (hpq : p^2 + q^2 ≠ 0) :
    reflection (affineSpan ℝ ({!₂[p, 0], !₂[0, q]} : Set Pt)) (0 : Pt) = 2 • foot p q := by
  have hmem := foot_mem p q hpq
  have horth := foot_orth p q hpq
  have h0 : (0 : Pt) = ((0 : Pt) -ᵥ foot p q) +ᵥ foot p q := by simp
  rw [h0, reflection_orthogonal_vadd hmem horth]
  simp [vsub_eq_sub, vadd_eq_add, two_smul]

/-- The center of the circle through the four reflected points. -/
noncomputable def circumcenter (a b c d : ℝ) : Pt :=
  !₂[b * d * (a - c) / (a * c + b * d), a * c * (b - d) / (a * c + b * d)]

/-- The squared radius of the circle through the four reflected points. -/
noncomputable def circumradiusSq (a b c d : ℝ) : ℝ :=
  (a^2 * b^2 * c^2 + a^2 * b^2 * d^2 + 2 * a^2 * b * c^2 * d +
    a^2 * c^2 * d^2 + 2 * a * b^2 * c * d^2 + b^2 * c^2 * d^2) / (a * c + b * d)^2

/-- Each reflected point `2 • foot p q`, for `(p, q)` one of the four pairs
`(a, b)`, `(-c, b)`, `(-c, -d)`, `(a, -d)`, is at squared distance
`circumradiusSq a b c d` from `circumcenter a b c d`. -/
theorem dist_sq_circumcenter (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    {p q : ℝ} (hp : p = a ∨ p = -c) (hq : q = b ∨ q = -d) :
    dist (2 • foot p q) (circumcenter a b c d) ^ 2 = circumradiusSq a b c d := by
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;>
    (rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity)]
     simp only [Fin.sum_univ_two, Real.dist_eq, sq_abs, foot, circumcenter, circumradiusSq,
       PiLp.toLp_apply, PiLp.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one, nsmul_eq_mul,
       neg_sq]
     field_simp (discharger := positivity)
     ring)

snip end

-- Up to a rigid motion of the plane (which preserves reflections and
-- concyclicity), the configuration of the problem is a quadrilateral with
-- vertices
--   A = (a, 0), B = (0, b), C = (-c, 0), D = (0, -d)   with a, b, c, d > 0,
-- whose diagonals AC and BD meet at right angles at the origin X.
-- Positivity of a, b, c, d encodes convexity: X lies strictly inside both
-- diagonals.  We show that the reflections of X in the four sidelines
-- AB, BC, CD, DA are concyclic.
problem usa1993_p2 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    Concyclic
      ({reflection (affineSpan ℝ ({!₂[a, 0], !₂[0, b]} : Set Pt)) (0 : Pt),
        reflection (affineSpan ℝ ({!₂[-c, 0], !₂[0, b]} : Set Pt)) (0 : Pt),
        reflection (affineSpan ℝ ({!₂[-c, 0], !₂[0, -d]} : Set Pt)) (0 : Pt),
        reflection (affineSpan ℝ ({!₂[a, 0], !₂[0, -d]} : Set Pt)) (0 : Pt)} : Set Pt) := by
  have hab : a^2 + b^2 ≠ 0 := by positivity
  have hcb : (-c)^2 + b^2 ≠ 0 := by positivity
  have hcd : (-c)^2 + (-d)^2 ≠ 0 := by
    rw [neg_sq, neg_sq]
    positivity
  have had : a^2 + (-d)^2 ≠ 0 := by
    rw [neg_sq]
    positivity
  have d1 := dist_sq_circumcenter a b c d ha hb hc hd (Or.inl rfl) (Or.inl rfl)
  have d2 := dist_sq_circumcenter a b c d ha hb hc hd (Or.inr rfl) (Or.inl rfl)
  have d3 := dist_sq_circumcenter a b c d ha hb hc hd (Or.inr rfl) (Or.inr rfl)
  have d4 := dist_sq_circumcenter a b c d ha hb hc hd (Or.inl rfl) (Or.inr rfl)
  rw [reflection_zero a b hab, reflection_zero (-c) b hcb,
    reflection_zero (-c) (-d) hcd, reflection_zero a (-d) had]
  refine ⟨⟨circumcenter a b c d, Real.sqrt (circumradiusSq a b c d), ?_⟩, ?_⟩
  · intro pt hpt
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hpt
    rcases hpt with rfl | rfl | rfl | rfl
    · rw [← d1]
      exact (Real.sqrt_sq dist_nonneg).symm
    · rw [← d2]
      exact (Real.sqrt_sq dist_nonneg).symm
    · rw [← d3]
      exact (Real.sqrt_sq dist_nonneg).symm
    · rw [← d4]
      exact (Real.sqrt_sq dist_nonneg).symm
  · rw [coplanar_iff_finrank_le_two]
    refine le_trans (Submodule.finrank_mono le_top) ?_
    rw [finrank_top, finrank_euclideanSpace_fin]

end Usa1993P2
