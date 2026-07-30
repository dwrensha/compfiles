/-
Copyright (c) 2026 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw, Kimi K3
-/

module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.InnerProductSpace.OfNorm
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.Geometry.Euclidean.Circumcenter
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

set_option maxHeartbeats 32000000
set_option maxRecDepth 8192

/-!
# International Mathematical Olympiad 2013, Problem 3

Let the excircle of triangle ABC opposite the vertex A be tangent to the side
BC at the point A1. Define the points B1 on CA and C1 on AB analogously, using
the excircles opposite B and C, respectively. Suppose that the circumcenter of
triangle A1B1C1 lies on the circumcircle of triangle ABC. Prove that triangle
ABC is right-angled.
-/

namespace Imo2013P3

open scoped EuclideanGeometry RealInnerProductSpace

snip begin

/-!
### Auxiliary lemmas

The proof is a coordinate computation. After applying a rigid motion we may
place `A` at the origin and `B` on the positive x-axis. Writing the side
lengths as `a = y + z`, `b = z + x`, `c = x + y` (the Ravi substitution,
with strictly positive `x`, `y`, `z`), the touch points of the excircles
have explicit rational coordinates. The condition that the circumcenter of
`A1B1C1` lies on the circumcircle of `ABC` then becomes a polynomial equation,
whose only relevant factors are the three dot products that detect the right
angles. The heavy polynomial identities were found by computer algebra and
are checked here by `ring` / `linear_combination`.
-/

/-- Squared distance between two points of the plane, in coordinates. -/
theorem dist_sq_fin2 (U V : EuclideanSpace ℝ (Fin 2)) :
    dist U V ^ 2 = (U 0 - V 0)^2 + (U 1 - V 1)^2 := by
  rw [EuclideanSpace.dist_eq,
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _),
    Fin.sum_univ_two, Real.dist_eq, Real.dist_eq, sq_abs, sq_abs]

/-- Inner product of two plane vectors, in coordinates. -/
theorem inner_fin2 (U V : EuclideanSpace ℝ (Fin 2)) :
    ⟪U, V⟫ = U 0 * V 0 + U 1 * V 1 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, Fin.sum_univ_two]
  ring

/-- Case split on the indices of `Fin 2`, with numeral forms `0` and `1`. -/
theorem fin2_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  fin_cases i
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Case split on the indices of `Fin 3`, with numeral forms. -/
theorem fin3_cases (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  fin_cases i
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

/-- The rigid-motion parametrization used to place `A` at the origin. -/
noncomputable def TOf (A e1 e2 P : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  !₂[⟪P - A, e1⟫, ⟪P - A, e2⟫]

theorem TOf_apply_zero (A e1 e2 P : EuclideanSpace ℝ (Fin 2)) :
    (TOf A e1 e2 P) 0 = ⟪P - A, e1⟫ := rfl

theorem TOf_apply_one (A e1 e2 P : EuclideanSpace ℝ (Fin 2)) :
    (TOf A e1 e2 P) 1 = ⟪P - A, e2⟫ := rfl

/-- The map `TOf` preserves distances when `e1`, `e2` come from an
orthonormal basis of the plane (we only need the concrete rotated basis). -/
theorem TOf_dist {A e1 e2 : EuclideanSpace ℝ (Fin 2)}
    (he2 : e2 = !₂[-(e1 1), e1 0]) (he1sq : e1 0^2 + e1 1^2 = 1)
    (P Q : EuclideanSpace ℝ (Fin 2)) :
    dist (TOf A e1 e2 P) (TOf A e1 e2 Q) = dist P Q := by
  have h2 : dist (TOf A e1 e2 P) (TOf A e1 e2 Q)^2 = dist P Q^2 := by
    rw [dist_sq_fin2, dist_sq_fin2, TOf_apply_zero, TOf_apply_one,
      TOf_apply_zero, TOf_apply_one, ← inner_sub_left, ← inner_sub_left]
    have hsub : P - A - (Q - A) = P - Q := by abel
    rw [hsub, inner_fin2 (P - Q) e1, inner_fin2 (P - Q) e2, he2]
    simp only [PiLp.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination ((P 0 - Q 0)^2 + (P 1 - Q 1)^2) * he1sq
  exact (sq_eq_sq₀ dist_nonneg dist_nonneg).mp h2

/-- The map `TOf` preserves inner products of differences. -/
theorem TOf_inner {A e1 e2 : EuclideanSpace ℝ (Fin 2)}
    (he2 : e2 = !₂[-(e1 1), e1 0]) (he1sq : e1 0^2 + e1 1^2 = 1)
    (P Q R : EuclideanSpace ℝ (Fin 2)) :
    ⟪TOf A e1 e2 P - TOf A e1 e2 Q, TOf A e1 e2 R - TOf A e1 e2 Q⟫
      = ⟪P - Q, R - Q⟫ := by
  rw [inner_fin2]
  simp only [PiLp.sub_apply, TOf_apply_zero, TOf_apply_one]
  rw [← inner_sub_left, ← inner_sub_left, ← inner_sub_left, ← inner_sub_left]
  have hsub1 : P - A - (Q - A) = P - Q := by abel
  have hsub2 : R - A - (Q - A) = R - Q := by abel
  rw [hsub1, hsub2, inner_fin2 (P - Q) e1, inner_fin2 (P - Q) e2,
    inner_fin2 (R - Q) e1, inner_fin2 (R - Q) e2, inner_fin2 (P - Q) (R - Q), he2]
  simp only [PiLp.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination ((P 0 - Q 0) * (R 0 - Q 0) + (P 1 - Q 1) * (R 1 - Q 1)) * he1sq

/-- Every plane vector is the sum of its coordinates in the basis `e1, e2`. -/
theorem onb_repr {e1 e2 : EuclideanSpace ℝ (Fin 2)}
    (he2 : e2 = !₂[-(e1 1), e1 0]) (he1sq : e1 0^2 + e1 1^2 = 1)
    (v : EuclideanSpace ℝ (Fin 2)) :
    v = ⟪v, e1⟫ • e1 + ⟪v, e2⟫ • e2 := by
  ext i
  rcases fin2_cases i with rfl | rfl
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    rw [inner_fin2 v e1, inner_fin2 v e2, he2]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination (-(v 0)) * he1sq
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    rw [inner_fin2 v e1, inner_fin2 v e2, he2]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination (-(v 1)) * he1sq

/-- `TOf` is affine: it commutes with `lineMap`. -/
theorem TOf_lineMap (A e1 e2 P Q : EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    TOf A e1 e2 (AffineMap.lineMap P Q t)
      = AffineMap.lineMap (TOf A e1 e2 P) (TOf A e1 e2 Q) t := by
  rw [AffineMap.lineMap_apply_module', AffineMap.lineMap_apply_module']
  ext i
  rcases fin2_cases i with rfl | rfl
  · simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul,
      TOf_apply_zero]
    rw [add_sub_assoc, inner_add_left, real_inner_smul_left, ← inner_sub_left]
    have hsub : Q - A - (P - A) = Q - P := by abel
    rw [hsub]
  · simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul,
      TOf_apply_one]
    rw [add_sub_assoc, inner_add_left, real_inner_smul_left, ← inner_sub_left]
    have hsub : Q - A - (P - A) = Q - P := by abel
    rw [hsub]

/- The algebraic heart of the proof.  With the Ravi substitution
`a = y+z, b = z+x, c = x+y` and the triangle placed at
`A = (0,0)`, `B = (x+y, 0)`, `C = (p, q)`, the excircle touch points are
`A1 = B + (z/(y+z))(C-B)`, `B1 = C + (x/(z+x))(A-C)`, `C1 = (y, 0)`.
Here `w0, w1` are the coordinates of a point equidistant from `A1, B1, C1`
(the circumcenter of the extouch triangle), `o0, o1` those of the
circumcenter of `ABC`, and the hypotheses say that the former lies on the
circumcircle.  The conclusion is that one of the three dot products
`x(x+y+z)-yz`, `y(x+y+z)-xz`, `z(x+y+z)-xy` vanishes; each of them is
proportional to a dot product at a vertex of the triangle, hence to a
right angle.  All polynomial identities below were produced by a computer
algebra elimination and are merely *verified* here. -/

/-- Coefficients of the equidistance equations, cleared of denominators. -/
def polyA1 (x y z _q : ℝ) : ℝ := - 2 * x^5 * y^2 - 4 * y * z * x^5 - 2 * x^5 * z^2 - 6 * x^4 * y^3 - 12 * z * x^4 * y^2 - 10 * y * x^4 * z^2 - 4 * x^4 * z^3 - 6 * x^3 * y^4 - 16 * z * x^3 * y^3 - 12 * x^3 * y^2 * z^2 - 4 * y * x^3 * z^3 - 2 * x^3 * z^4 - 2 * x^2 * y^5 - 12 * z * x^2 * y^4 - 12 * x^2 * y^3 * z^2 + 2 * y * x^2 * z^4 - 4 * x * z * y^5 - 10 * x * y^4 * z^2 - 4 * x * y^3 * z^3 + 2 * x * y^2 * z^4 - 2 * y^5 * z^2 - 4 * y^4 * z^3 - 2 * y^3 * z^4

/-- Coefficients of the equidistance equations, cleared of denominators. -/
def polyB1 (x y z q : ℝ) : ℝ := - 2 * q * y * z * x^4 - 2 * q * x^4 * z^2 - 2 * q * z * x^3 * y^2 - 4 * q * y * x^3 * z^2 - 2 * q * x^3 * z^3 + 2 * q * z * x^2 * y^3 - 2 * q * y * x^2 * z^3 + 2 * q * x * z * y^4 + 4 * q * x * y^3 * z^2 + 2 * q * x * y^2 * z^3 + 2 * q * y^4 * z^2 + 2 * q * y^3 * z^3

/-- Coefficients of the equidistance equations, cleared of denominators. -/
def polyE1 (x y z q : ℝ) : ℝ := - q^2 * x^4 * z^2 - 2 * y * q^2 * x^3 * z^2 - 2 * q^2 * x^3 * z^3 - 2 * y * q^2 * x^2 * z^3 + 2 * x * q^2 * y^3 * z^2 + 2 * x * q^2 * y^2 * z^3 + q^2 * y^4 * z^2 + 2 * q^2 * y^3 * z^3 - x^6 * y^2 - 2 * y * z * x^6 - x^6 * z^2 - 4 * x^5 * y^3 - 8 * z * x^5 * y^2 - 8 * y * x^5 * z^2 - 4 * x^5 * z^3 - 6 * x^4 * y^4 - 14 * z * x^4 * y^3 - 15 * x^4 * y^2 * z^2 - 8 * y * x^4 * z^3 - 5 * x^4 * z^4 - 4 * x^3 * y^5 - 14 * z * x^3 * y^4 - 12 * x^3 * y^3 * z^2 - 4 * x^3 * y^2 * z^3 + 4 * y * x^3 * z^4 - 2 * x^3 * z^5 - x^2 * y^6 - 8 * z * x^2 * y^5 - 7 * x^2 * y^4 * z^2 + 2 * x^2 * y^2 * z^4 + 6 * y * x^2 * z^5 - 2 * x * z * y^6 - 4 * x * y^5 * z^2 - 4 * x * y^3 * z^4 - 6 * x * y^2 * z^5 - y^6 * z^2 + 3 * y^4 * z^4 + 2 * y^3 * z^5

/-- Coefficients of the equidistance equations, cleared of denominators. -/
def polyA2 (x y z _q : ℝ) : ℝ := 2 * y * x^4 - 2 * z * x^4 + 4 * x^3 * y^2 - 4 * x^3 * z^2 + 2 * x^2 * y^3 + 6 * z * x^2 * y^2 - 2 * y * x^2 * z^2 - 2 * x^2 * z^3 + 4 * x * z * y^3 + 4 * x * y^2 * z^2 + 2 * y^3 * z^2 + 2 * y^2 * z^3

/-- Coefficients of the equidistance equations, cleared of denominators. -/
def polyB2 (x y z q : ℝ) : ℝ := - 2 * q * z * x^3 - 4 * q * y * z * x^2 - 2 * q * x^2 * z^2 - 2 * q * x * z * y^2 - 4 * q * x * y * z^2 - 2 * q * y^2 * z^2

/-- Coefficients of the equidistance equations, cleared of denominators. -/
def polyE2 (x y z q : ℝ) : ℝ := - q^2 * x^2 * z^2 - 2 * x * y * q^2 * z^2 - q^2 * y^2 * z^2 + x^4 * y^2 - x^4 * z^2 + 2 * x^3 * y^3 + 2 * z * x^3 * y^2 - 2 * y * x^3 * z^2 - 2 * x^3 * z^3 + x^2 * y^4 + 4 * z * x^2 * y^3 - x^2 * z^4 + 2 * x * z * y^4 + 2 * x * y^3 * z^2 + 2 * x * y^2 * z^3 + 2 * x * y * z^4 + y^4 * z^2 - y^2 * z^4

/-- Cofactor of the numerator `N₀` of the `w0`-coordinate. -/
def polyM0 (x y z q : ℝ) : ℝ := q^2 * x^3 * z^2 + y * q^2 * x^2 * z^2 - x * q^2 * y^2 * z^2 - q^2 * y^3 * z^2 + x^5 * y^2 + 2 * y * z * x^5 + x^5 * z^2 + 5 * x^4 * y^3 + 8 * z * x^4 * y^2 + 5 * y * x^4 * z^2 + 2 * x^4 * z^3 + 7 * x^3 * y^4 + 12 * z * x^3 * y^3 + 8 * x^3 * y^2 * z^2 + x^3 * z^4 + 3 * x^2 * y^5 + 8 * z * x^2 * y^4 + 4 * x^2 * y^3 * z^2 - 3 * y * x^2 * z^4 + 2 * x * z * y^5 - x * y^4 * z^2 + 3 * x * y^2 * z^4 - y^5 * z^2 - 2 * y^4 * z^3 - y^3 * z^4

/-- Cofactor of the numerator `N₁` of the `w1`-coordinate. -/
def polyM1 (x y z q : ℝ) : ℝ := y * q^2 * x^5 * z^2 - q^2 * x^5 * z^3 + 4 * q^2 * x^4 * y^2 * z^2 + y * q^2 * x^4 * z^3 - q^2 * x^4 * z^4 + 6 * q^2 * x^3 * y^3 * z^2 + 8 * q^2 * x^3 * y^2 * z^3 + 4 * q^2 * x^2 * y^4 * z^2 + 8 * q^2 * x^2 * y^3 * z^3 + 2 * q^2 * x^2 * y^2 * z^4 + x * q^2 * y^5 * z^2 + x * q^2 * y^4 * z^3 - q^2 * y^5 * z^3 - q^2 * y^4 * z^4 + x^7 * y^3 + z * x^7 * y^2 - y * x^7 * z^2 - x^7 * z^3 + 4 * x^6 * y^4 + 3 * z * x^6 * y^3 - x^6 * y^2 * z^2 - 3 * y * x^6 * z^3 - 3 * x^6 * z^4 + 6 * x^5 * y^5 + 4 * z * x^5 * y^4 + x^5 * y^3 * z^2 - x^5 * y^2 * z^3 + y * x^5 * z^4 - 3 * x^5 * z^5 + 4 * x^4 * y^6 + 4 * z * x^4 * y^5 + 2 * x^4 * y^4 * z^2 + 5 * x^4 * y^3 * z^3 + 3 * x^4 * y^2 * z^4 + 7 * y * x^4 * z^5 - x^4 * z^6 + x^3 * y^7 + 3 * z * x^3 * y^6 + x^3 * y^5 * z^2 + 5 * x^3 * y^4 * z^3 - 2 * x^3 * y^3 * z^4 - 4 * x^3 * y^2 * z^5 + 4 * y * x^3 * z^6 + z * x^2 * y^7 - x^2 * y^6 * z^2 - x^2 * y^5 * z^3 + 3 * x^2 * y^4 * z^4 - 4 * x^2 * y^3 * z^5 - 6 * x^2 * y^2 * z^6 - x * y^7 * z^2 - 3 * x * y^6 * z^3 + x * y^5 * z^4 + 7 * x * y^4 * z^5 + 4 * x * y^3 * z^6 - y^7 * z^3 - 3 * y^6 * z^4 - 3 * y^5 * z^5 - y^4 * z^6

/-- Determinant of the equidistance linear system for `w0, w1`. -/
def polyDD (x y z q : ℝ) : ℝ := 8 * q * x * y * z * (x + y)^4 * (x + z)^3 * (y + z)

/-- Numerator of the `w0` coordinate: `polyDD * w0 = polyN0`. -/
def polyN0 (x y z q : ℝ) : ℝ := 2 * q * z * (x + y)^2 * (x + z)^2 * polyM0 x y z q

/-- Numerator of the `w1` coordinate: `polyDD * w1 = polyN1`. -/
def polyN1 (x y z q : ℝ) : ℝ := 2 * (x + y) * (x + z)^2 * polyM1 x y z q

/-- The `q²`-part of `polyM0`; it factors as `z²(x+y)²(x-y)`. -/
def polyM0a (x y z : ℝ) : ℝ := z^2 * (x + y)^2 * (x - y)
/-- The `q⁰`-part of `polyM0`. -/
def polyM0b (x y z : ℝ) : ℝ := x^5 * y^2 + 2 * y * z * x^5 + x^5 * z^2 + 5 * x^4 * y^3 + 8 * z * x^4 * y^2 + 5 * y * x^4 * z^2 + 2 * x^4 * z^3 + 7 * x^3 * y^4 + 12 * z * x^3 * y^3 + 8 * x^3 * y^2 * z^2 + x^3 * z^4 + 3 * x^2 * y^5 + 8 * z * x^2 * y^4 + 4 * x^2 * y^3 * z^2 - 3 * y * x^2 * z^4 + 2 * x * z * y^5 - x * y^4 * z^2 + 3 * x * y^2 * z^4 - y^5 * z^2 - 2 * y^4 * z^3 - y^3 * z^4
/-- The `q²`-part of `polyM1`. -/
def polyM1a (x y z : ℝ) : ℝ := y * x^5 * z^2 - x^5 * z^3 + 4 * x^4 * y^2 * z^2 + y * x^4 * z^3 - x^4 * z^4 + 6 * x^3 * y^3 * z^2 + 8 * x^3 * y^2 * z^3 + 4 * x^2 * y^4 * z^2 + 8 * x^2 * y^3 * z^3 + 2 * x^2 * y^2 * z^4 + x * y^5 * z^2 + x * y^4 * z^3 - y^5 * z^3 - y^4 * z^4
/-- The `q⁰`-part of `polyM1`. -/
def polyM1b (x y z : ℝ) : ℝ := x^7 * y^3 + z * x^7 * y^2 - y * x^7 * z^2 - x^7 * z^3 + 4 * x^6 * y^4 + 3 * z * x^6 * y^3 - x^6 * y^2 * z^2 - 3 * y * x^6 * z^3 - 3 * x^6 * z^4 + 6 * x^5 * y^5 + 4 * z * x^5 * y^4 + x^5 * y^3 * z^2 - x^5 * y^2 * z^3 + y * x^5 * z^4 - 3 * x^5 * z^5 + 4 * x^4 * y^6 + 4 * z * x^4 * y^5 + 2 * x^4 * y^4 * z^2 + 5 * x^4 * y^3 * z^3 + 3 * x^4 * y^2 * z^4 + 7 * y * x^4 * z^5 - x^4 * z^6 + x^3 * y^7 + 3 * z * x^3 * y^6 + x^3 * y^5 * z^2 + 5 * x^3 * y^4 * z^3 - 2 * x^3 * y^3 * z^4 - 4 * x^3 * y^2 * z^5 + 4 * y * x^3 * z^6 + z * x^2 * y^7 - x^2 * y^6 * z^2 - x^2 * y^5 * z^3 + 3 * x^2 * y^4 * z^4 - 4 * x^2 * y^3 * z^5 - 6 * x^2 * y^2 * z^6 - x * y^7 * z^2 - 3 * x * y^6 * z^3 + x * y^5 * z^4 + 7 * x * y^4 * z^5 + 4 * x * y^3 * z^6 - y^7 * z^3 - 3 * y^6 * z^4 - 3 * y^5 * z^5 - y^4 * z^6

/-- Coefficients of the eliminated polynomial `A₀` in `u = q^2` (factored form). -/
def polyC0 (x y z : ℝ) : ℝ := 4 * (x + y)^2 * (x + z)^4 * (polyM1b x y z)^2
    - 16 * x * y * z * (x + y)^5 * (x + z)^5 * (y + z)
      * (z * (x + y + z) - x * y) * polyM1b x y z

/-- Coefficients of the eliminated polynomial `A₀` in `u = q^2` (factored form). -/
def polyC1 (x y z : ℝ) : ℝ := 4 * z^2 * (x + y)^4 * (x + z)^4 * (polyM0b x y z)^2
    - 16 * x * y * z^2 * (x + y)^7 * (x + z)^5 * (y + z) * polyM0b x y z
    + 8 * (x + y)^2 * (x + z)^4 * polyM1a x y z * polyM1b x y z
    - 16 * x * y * z * (x + y)^5 * (x + z)^5 * (y + z)
      * (z * (x + y + z) - x * y) * polyM1a x y z

/-- Coefficients of the eliminated polynomial `A₀` in `u = q^2` (factored form). -/
def polyC2 (x y z : ℝ) : ℝ := 8 * z^2 * (x + y)^4 * (x + z)^4 * polyM0a x y z * polyM0b x y z
    - 16 * x * y * z^2 * (x + y)^7 * (x + z)^5 * (y + z) * polyM0a x y z
    + 4 * (x + y)^2 * (x + z)^4 * (polyM1a x y z)^2

/-- Coefficients of the eliminated polynomial `A₀` in `u = q^2` (factored form). -/
def polyC3 (x y z : ℝ) : ℝ := 4 * z^2 * (x + y)^4 * (x + z)^4 * (polyM0a x y z)^2

/-- The eliminated condition `A₀` with the circumcircle condition
reduced to a polynomial in `x, y, z, q^2`. -/
def polyA0 (x y z q : ℝ) : ℝ :=
  polyC0 x y z + polyC1 x y z * q^2 + polyC2 x y z * (q^2)^2 + polyC3 x y z * (q^2)^3

/- The big elimination identity `T = q * A₀` (lemma `coreC`) is checked by
`ring` calls on *factored* forms of the polynomials, to keep every
normalization small.  We split `polyM0` and `polyM1` by powers of `q` as
`Mᵢ = q²·Mᵢₐ + Mᵢ_b`, and store the four coefficients of `q²` in `A₀`
(`polyC0` … `polyC3`) directly in factored form.  All of these factored
forms were produced by the same computer algebra elimination. -/

/-- Split of `polyM0` by powers of `q`. -/
lemma polyM0_split (x y z q : ℝ) :
    polyM0 x y z q = q^2 * polyM0a x y z + polyM0b x y z := by
  simp only [polyM0, polyM0a, polyM0b]
  ring

/-- Split of `polyM1` by powers of `q`. -/
lemma polyM1_split (x y z q : ℝ) :
    polyM1 x y z q = q^2 * polyM1a x y z + polyM1b x y z := by
  simp only [polyM1, polyM1a, polyM1b]
  ring

/-- First elimination step: Cramer's rule on the equidistance equations. -/
lemma coreA
    (x y z q w0 w1 : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (heq1 : (w0 - (x + y + z) * (x * y + x * z + y^2 - y * z) / ((x + y) * (y + z)))^2
        + (w1 - q * z / (y + z))^2
      = (w0 - z * (x * (x + y + z) - y * z) / ((x + y) * (x + z)))^2
        + (w1 - q * z / (x + z))^2)
    (heq2 : (w0 - z * (x * (x + y + z) - y * z) / ((x + y) * (x + z)))^2
        + (w1 - q * z / (x + z))^2
      = (w0 - y)^2 + w1^2) :
    polyDD x y z q * w0 = polyN0 x y z q
      ∧ polyDD x y z q * w1 = polyN1 x y z q := by
  have hxy : x + y ≠ 0 := ne_of_gt (add_pos hx hy)
  have hyz : y + z ≠ 0 := ne_of_gt (add_pos hy hz)
  have hzx : z + x ≠ 0 := ne_of_gt (add_pos hz hx)
  have heq1' : ((x + y) * (y + z) * (x + z))^2
        * ((w0 - (x + y + z) * (x * y + x * z + y^2 - y * z) / ((x + y) * (y + z)))^2
          + (w1 - q * z / (y + z))^2)
      = ((x + y) * (y + z) * (x + z))^2
        * ((w0 - z * (x * (x + y + z) - y * z) / ((x + y) * (x + z)))^2
          + (w1 - q * z / (x + z))^2) := by
    rw [heq1]
  have heq2' : ((x + y) * (x + z))^2
        * ((w0 - z * (x * (x + y + z) - y * z) / ((x + y) * (x + z)))^2
          + (w1 - q * z / (x + z))^2)
      = ((x + y) * (x + z))^2 * ((w0 - y)^2 + w1^2) := by
    rw [heq2]
  have eq1c : polyA1 x y z q * w0 + polyB1 x y z q * w1 = polyE1 x y z q := by
    simp only [polyA1, polyB1, polyE1]
    field_simp [hxy, hyz, hzx] at heq1'
    linear_combination heq1'
  have eq2c : polyA2 x y z q * w0 + polyB2 x y z q * w1 = polyE2 x y z q := by
    simp only [polyA2, polyB2, polyE2]
    field_simp [hxy, hzx] at heq2'
    linear_combination heq2'
  have hdd_eq : polyDD x y z q
      = polyA1 x y z q * polyB2 x y z q - polyA2 x y z q * polyB1 x y z q := by
    simp only [polyDD, polyA1, polyB1, polyA2, polyB2]
    ring
  have hN0_eq : polyN0 x y z q
      = polyE1 x y z q * polyB2 x y z q - polyE2 x y z q * polyB1 x y z q := by
    simp only [polyN0, polyM0, polyE1, polyB1, polyE2, polyB2]
    ring
  have hN1_eq : polyN1 x y z q
      = polyA1 x y z q * polyE2 x y z q - polyA2 x y z q * polyE1 x y z q := by
    simp only [polyN1, polyM1, polyA1, polyE1, polyA2, polyE2]
    ring
  have hcr0 : (polyA1 x y z q * polyB2 x y z q - polyA2 x y z q * polyB1 x y z q) * w0
      = polyE1 x y z q * polyB2 x y z q - polyE2 x y z q * polyB1 x y z q := by
    linear_combination polyB2 x y z q * eq1c - polyB1 x y z q * eq2c
  have hcr1 : (polyA1 x y z q * polyB2 x y z q - polyA2 x y z q * polyB1 x y z q) * w1
      = polyA1 x y z q * polyE2 x y z q - polyA2 x y z q * polyE1 x y z q := by
    linear_combination (-polyA2 x y z q) * eq1c + polyA1 x y z q * eq2c
  constructor
  · rw [hdd_eq, hN0_eq]
    exact hcr0
  · rw [hdd_eq, hN1_eq]
    exact hcr1

/-- Second elimination step: substitute into the circumcircle condition. -/
lemma coreB
    (x y z q w0 w1 o0 o1 : ℝ)
    (hO0 : 2 * o0 = x + y)
    (hO1 : 2 * q * o1 = z * (x + y + z) - x * y)
    (hcond : w0^2 - 2 * w0 * o0 + w1^2 - 2 * w1 * o1 = 0)
    (hcr : polyDD x y z q * w0 = polyN0 x y z q
      ∧ polyDD x y z q * w1 = polyN1 x y z q) :
    q * (polyN0 x y z q^2 - (x + y) * polyN0 x y z q * polyDD x y z q
        + polyN1 x y z q^2)
      - polyN1 x y z q * polyDD x y z q * (z * (x + y + z) - x * y) = 0 := by
  obtain ⟨cramer0, cramer1⟩ := hcr
  have hT1 : polyN0 x y z q^2 - (x + y) * polyN0 x y z q * polyDD x y z q
      + polyN1 x y z q^2
      = polyDD x y z q^2 * (w0^2 - (x + y) * w0 + w1^2) := by
    linear_combination
      (-(polyDD x y z q * w0 + polyN0 x y z q - (x + y) * polyDD x y z q)) * cramer0
      + (-(polyDD x y z q * w1 + polyN1 x y z q)) * cramer1
  rw [hT1]
  linear_combination (q * polyDD x y z q^2) * hcond
    + (q * polyDD x y z q^2 * w0) * hO0
    + (polyDD x y z q^2 * w1) * hO1
    + (polyDD x y z q * (z * (x + y + z) - x * y)) * cramer1

/-- The `q²`-free factor in the extouch elimination; see `coreC_factor`. -/
def polyT0 (x y z : ℝ) : ℝ := x^2 * y + x^2 * z + 3 * x * y^2 + x * z^2 - y^2 * z - y * z^2

/-- The degree-6 factor in the extouch elimination; see `coreC_factor`. -/
def polyT1 (x y z : ℝ) : ℝ := x^4 * y^2 - x^4 * z^2 + 2 * x^3 * y^3 - 2 * x^3 * y^2 * z
    + 2 * x^3 * y * z^2 - 2 * x^3 * z^3 + x^2 * y^4 - 2 * x^2 * y^3 * z
    + 2 * x^2 * y^2 * z^2 + 4 * x^2 * y * z^3 - x^2 * z^4 + 2 * x * y^3 * z^2
    + 4 * x * y^2 * z^3 + 2 * x * y * z^4 - y^4 * z^2 - 2 * y^3 * z^3 - y^2 * z^4

/-- Factorization of `polyM1b·(x+y)² + polyM1a·K`, with `K = 4xyz(x+y+z)`. -/
lemma coreC_S1 (x y z : ℝ) :
    polyM1b x y z * (x + y)^2 + polyM1a x y z * (4 * x * y * z * (x + y + z))
      = (x + y)^4 * (x + z) * (y + z) * polyT1 x y z := by
  simp only [polyT1, polyM1a, polyM1b]
  ring

/-- Factorization of `polyM0b·(x+y)² + polyM0a·K`, with `K = 4xyz(x+y+z)`. -/
lemma coreC_S0 (x y z : ℝ) :
    polyM0b x y z * (x + y)^2 + polyM0a x y z * (4 * x * y * z * (x + y + z))
      = (x + y)^4 * (x + z) * (y + z) * polyT0 x y z := by
  simp only [polyT0, polyM0a, polyM0b]
  ring

/-- The degree-12 eliminated condition in the factors `polyT0`, `polyT1`. -/
lemma coreC_E2 (x y z : ℝ) :
    (polyT1 x y z)^2 + z^2 * (4 * x * y * z * (x + y + z)) * (polyT0 x y z)^2
      - 4 * x * y * z * (x + y) * (z * (x + y + z) - x * y) * polyT1 x y z
      - 4 * x * y * z^2 * (x + y) * (4 * x * y * z * (x + y + z)) * polyT0 x y z
      = -((x + y) * (x + z) * (y + z)
        * ((x * (x + y + z) - y * z) * (y * (x + y + z) - x * z)
          * (z * (x + y + z) - x * y))
        * ((x + y) * (x * y + z^2) + z * (x - y)^2)) := by
  simp only [polyT0, polyT1]
  ring

/-- The `polyC`-combination, regrouped over the `Sᵢ` expressions. -/
lemma coreC_fin1 (x y z : ℝ) :
    polyC0 x y z * (x + y)^6
      + polyC1 x y z * (4 * x * y * z * (x + y + z)) * (x + y)^4
      + polyC2 x y z * (4 * x * y * z * (x + y + z))^2 * (x + y)^2
      + polyC3 x y z * (4 * x * y * z * (x + y + z))^3
      = 4 * (x + y)^4 * (x + z)^4
        * ((polyM1b x y z * (x + y)^2 + polyM1a x y z * (4 * x * y * z * (x + y + z)))^2
          + z^2 * (4 * x * y * z * (x + y + z))
            * (polyM0b x y z * (x + y)^2 + polyM0a x y z * (4 * x * y * z * (x + y + z)))^2)
        - 16 * x * y * z * (x + y)^9 * (x + z)^5 * (y + z)
          * ((z * (x + y + z) - x * y)
            * (polyM1b x y z * (x + y)^2 + polyM1a x y z * (4 * x * y * z * (x + y + z)))
            + z * (4 * x * y * z * (x + y + z))
              * (polyM0b x y z * (x + y)^2 + polyM0a x y z * (4 * x * y * z * (x + y + z)))) := by
  simp only [polyC0, polyC1, polyC2, polyC3]
  generalize _ha : x + y = a
  ring

/-- Factoring out `4·(x+y)¹²(x+z)⁶(y+z)²` after the `Sᵢ = (x+y)⁴(x+z)(y+z)·Tᵢ`
substitution. -/
lemma coreC_factor (x y z : ℝ) :
    4 * (x + y)^4 * (x + z)^4
      * (((x + y)^4 * (x + z) * (y + z) * polyT1 x y z)^2
        + z^2 * (4 * x * y * z * (x + y + z))
          * ((x + y)^4 * (x + z) * (y + z) * polyT0 x y z)^2)
      - 16 * x * y * z * (x + y)^9 * (x + z)^5 * (y + z)
        * ((z * (x + y + z) - x * y) * ((x + y)^4 * (x + z) * (y + z) * polyT1 x y z)
          + z * (4 * x * y * z * (x + y + z)) * ((x + y)^4 * (x + z) * (y + z) * polyT0 x y z))
    = 4 * (x + y)^12 * (x + z)^6 * (y + z)^2
      * ((polyT1 x y z)^2 + z^2 * (4 * x * y * z * (x + y + z)) * (polyT0 x y z)^2
        - 4 * x * y * z * (x + y) * (z * (x + y + z) - x * y) * polyT1 x y z
        - 4 * x * y * z^2 * (x + y) * (4 * x * y * z * (x + y + z)) * polyT0 x y z) := by
  generalize _ha : x + y = a
  ring

/-- Final elimination step: the result is `q` times a polynomial in `q^2`,
which yields the right-angle factorization. -/
lemma coreC
    (x y z q : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hq : q ≠ 0)
    (hQ : q^2 * (x + y)^2 = 4 * x * y * z * (x + y + z))
    (hT : q * (polyN0 x y z q^2 - (x + y) * polyN0 x y z q * polyDD x y z q
        + polyN1 x y z q^2)
      - polyN1 x y z q * polyDD x y z q * (z * (x + y + z) - x * y) = 0) :
    (x * (x + y + z) - y * z) * (y * (x + y + z) - x * z)
      * (z * (x + y + z) - x * y) = 0 := by
  -- With `N₀ = 2qz(x+y)²(x+z)²·M₀`, `N₁ = 2(x+y)(x+z)²·M₁` and
  -- `D = 8qxyz(x+y)⁴(x+z)³(y+z)`, the left side of `hT` factors as `q` times
  -- a polynomial in `q²`.  This `ring` is small: `polyM0`/`polyM1` stay folded.
  have hT1 : q * (polyN0 x y z q^2 - (x + y) * polyN0 x y z q * polyDD x y z q
        + polyN1 x y z q^2)
      - polyN1 x y z q * polyDD x y z q * (z * (x + y + z) - x * y)
      = q * (4 * z^2 * (x + y)^4 * (x + z)^4 * q^2 * (polyM0 x y z q)^2
        - 16 * x * y * z^2 * (x + y)^7 * (x + z)^5 * (y + z) * q^2 * polyM0 x y z q
        + 4 * (x + y)^2 * (x + z)^4 * (polyM1 x y z q)^2
        - 16 * x * y * z * (x + y)^5 * (x + z)^5 * (y + z) * (z * (x + y + z) - x * y)
          * polyM1 x y z q) := by
    simp only [polyN0, polyN1, polyDD]
    ring
  -- Collecting by powers of `q²` gives `polyA0`: the coefficients are exactly
  -- the factored `polyC0` … `polyC3`.  With the splits
  -- `Mᵢ = q²·Mᵢₐ + Mᵢ_b` this `ring` only handles folded atoms, so it is small.
  have hT2 : 4 * z^2 * (x + y)^4 * (x + z)^4 * q^2 * (polyM0 x y z q)^2
      - 16 * x * y * z^2 * (x + y)^7 * (x + z)^5 * (y + z) * q^2 * polyM0 x y z q
      + 4 * (x + y)^2 * (x + z)^4 * (polyM1 x y z q)^2
      - 16 * x * y * z * (x + y)^5 * (x + z)^5 * (y + z) * (z * (x + y + z) - x * y)
        * polyM1 x y z q
      = polyA0 x y z q := by
    rw [polyM0_split, polyM1_split]
    simp only [polyA0, polyC0, polyC1, polyC2, polyC3]
    ring
  have hTform : q * (polyN0 x y z q^2 - (x + y) * polyN0 x y z q * polyDD x y z q
        + polyN1 x y z q^2)
      - polyN1 x y z q * polyDD x y z q * (z * (x + y + z) - x * y)
      = q * polyA0 x y z q := by
    rw [hT1, hT2]
  have hA0 : polyA0 x y z q = 0 := by
    rw [hTform] at hT
    rcases mul_eq_zero.mp hT with hq0 | hA0
    · exact absurd hq0 hq
    · exact hA0
  have hstep : (x + y)^6 * polyA0 x y z q
      = polyC0 x y z * (x + y)^6 + polyC1 x y z * (q^2 * (x + y)^2) * (x + y)^4
        + polyC2 x y z * (q^2 * (x + y)^2)^2 * (x + y)^2
        + polyC3 x y z * (q^2 * (x + y)^2)^3 := by
    simp only [polyA0]
    ring
  rw [hQ] at hstep
  rw [hA0, mul_zero] at hstep
  -- The eliminated condition: the `polyC`-combination factors as
  -- `4·(x+y)¹²(x+z)⁶(y+z)²` times a degree-12 polynomial in the factors
  -- `polyT0`, `polyT1` (identities found by computer algebra and verified
  -- here).  Keeping everything factored avoids the degree-32 normalization
  -- that a direct `ring` on the expanded polynomials would need.
  rw [coreC_fin1, coreC_S1, coreC_S0, coreC_factor, coreC_E2, mul_neg, eq_comm,
    neg_eq_zero] at hstep
  have hposG : 0 < 4 * (x + y)^12 * (x + z)^6 * (y + z)^2 := by positivity
  have hposF : 0 < (x + y) * (x + z) * (y + z) := by positivity
  have hposS : 0 < (x + y) * (x * y + z^2) + z * (x - y)^2 := by positivity
  rcases mul_eq_zero.mp hstep with hG | hrest
  · exact absurd hG (ne_of_gt hposG)
  · rcases mul_eq_zero.mp hrest with hFPS | hS
    · rcases mul_eq_zero.mp hFPS with hF | hP
      · exact absurd hF (ne_of_gt hposF)
      · exact hP
    · exact absurd hS (ne_of_gt hposS)

theorem core
    (x y z q w0 w1 o0 o1 : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hq : q ≠ 0)
    (hQ : q^2 * (x + y)^2 = 4 * x * y * z * (x + y + z))
    (hO0 : 2 * o0 = x + y)
    (hO1 : 2 * q * o1 = z * (x + y + z) - x * y)
    (hcond : w0^2 - 2 * w0 * o0 + w1^2 - 2 * w1 * o1 = 0)
    (heq1 : (w0 - (x + y + z) * (x * y + x * z + y^2 - y * z) / ((x + y) * (y + z)))^2
        + (w1 - q * z / (y + z))^2
      = (w0 - z * (x * (x + y + z) - y * z) / ((x + y) * (x + z)))^2
        + (w1 - q * z / (x + z))^2)
    (heq2 : (w0 - z * (x * (x + y + z) - y * z) / ((x + y) * (x + z)))^2
        + (w1 - q * z / (x + z))^2
      = (w0 - y)^2 + w1^2) :
    (x * (x + y + z) - y * z) * (y * (x + y + z) - x * z)
      * (z * (x + y + z) - x * y) = 0 := by
  have hcr := coreA x y z q w0 w1 hx hy hz heq1 heq2
  have hT := coreB x y z q w0 w1 o0 o1 hO0 hO1 hcond hcr
  exact coreC x y z q hx hy hz hq hQ hT

snip end

problem imo2013_p3
    (A B C A1 B1 C1 : EuclideanSpace ℝ (Fin 2))
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hA1 : A1 = AffineMap.lineMap B C
      (((dist B C + dist C A + dist A B) / 2 - dist A B) / dist B C))
    (hB1 : B1 = AffineMap.lineMap C A
      (((dist B C + dist C A + dist A B) / 2 - dist B C) / dist C A))
    (hC1 : C1 = AffineMap.lineMap A B
      (((dist B C + dist C A + dist A B) / 2 - dist C A) / dist A B))
    (hW : ∃ W, dist W A1 = dist W B1 ∧ dist W B1 = dist W C1 ∧
      dist W (⟨![A, B, C], hABC⟩ : Affine.Triangle ℝ _).circumcenter
        = (⟨![A, B, C], hABC⟩ : Affine.Triangle ℝ _).circumradius) :
    ∠ C A B = Real.pi / 2 ∨ ∠ A B C = Real.pi / 2 ∨ ∠ B C A = Real.pi / 2 := by
  -- side lengths
  set a := dist B C with ha_def
  set b := dist C A with hb_def
  set c := dist A B with hc_def
  have hAneB : A ≠ B := hABC.injective.ne (by decide : (0 : Fin 3) ≠ 1)
  have hBneC : B ≠ C := hABC.injective.ne (by decide : (1 : Fin 3) ≠ 2)
  have hAneC : A ≠ C := hABC.injective.ne (by decide : (0 : Fin 3) ≠ 2)
  have ha : 0 < a := dist_pos.mpr hBneC
  have hb : 0 < b := dist_pos.mpr hAneC.symm
  have hc : 0 < c := dist_pos.mpr hAneB
  -- Ravi substitution x = s - a, y = s - b, z = s - c
  set x := (b + c - a) / 2 with hx_def
  set y := (a + c - b) / 2 with hy_def
  set z := (a + b - c) / 2 with hz_def
  have hyz_a : y + z = a := by rw [hy_def, hz_def]; ring
  have hzx_b : z + x = b := by rw [hz_def, hx_def]; ring
  have hxy_c : x + y = c := by rw [hx_def, hy_def]; ring
  -- strict triangle inequalities from non-collinearity
  have hncol := affineIndependent_iff_not_collinear.mp hABC
  -- Note: feeding `not_wbtw_of_injective` directly into `dist_lt_dist_add_dist_iff.mpr`
  -- sends unification into a `WithLp.equiv` unfold loop (the `![A, B, C] i =?= B`
  -- defeqs).  Reduce the matrix applications with `simp only` first instead.
  have hinj102 : Function.Injective (![1, 0, 2] : Fin 3 → Fin 3) := by decide
  have hinj210 : Function.Injective (![2, 1, 0] : Fin 3 → Fin 3) := by decide
  have hinj021 : Function.Injective (![0, 2, 1] : Fin 3 → Fin 3) := by decide
  have hnbac := AffineIndependent.not_wbtw_of_injective 1 0 2 hinj102 hABC
  have hncba := AffineIndependent.not_wbtw_of_injective 2 1 0 hinj210 hABC
  have hnacb := AffineIndependent.not_wbtw_of_injective 0 2 1 hinj021 hABC
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
    at hnbac hncba hnacb
  have htr1 : dist B C < dist B A + dist A C := dist_lt_dist_add_dist_iff.mpr hnbac
  have htr2 : dist C A < dist C B + dist B A := dist_lt_dist_add_dist_iff.mpr hncba
  have htr3 : dist A B < dist A C + dist C B := dist_lt_dist_add_dist_iff.mpr hnacb
  rw [dist_comm B A, dist_comm A C] at htr1
  rw [dist_comm C B, dist_comm B A] at htr2
  rw [dist_comm A C, dist_comm C B] at htr3
  have hx : 0 < x := by rw [hx_def]; linarith
  have hy : 0 < y := by rw [hy_def]; linarith
  have hz : 0 < z := by rw [hz_def]; linarith
  have hxy : x + y ≠ 0 := ne_of_gt (add_pos hx hy)
  have hyz : y + z ≠ 0 := ne_of_gt (add_pos hy hz)
  have hzx : z + x ≠ 0 := ne_of_gt (add_pos hz hx)
  -- orthonormal basis along AB
  set e1 : EuclideanSpace ℝ (Fin 2) := c⁻¹ • (B - A) with he1
  set e2 : EuclideanSpace ℝ (Fin 2) := !₂[-(e1 1), e1 0] with he2
  have hnorm_e1 : ⟪e1, e1⟫ = 1 := by
    rw [he1, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq, ← dist_eq_norm, dist_comm B A, ← hc_def]
    field_simp [hc.ne']
  have he1sq : e1 0^2 + e1 1^2 = 1 := by
    have h := hnorm_e1
    rw [inner_fin2] at h
    linear_combination h
  -- coordinates of C
  set p := ⟪C - A, e1⟫ with hp_def
  set q := ⟪C - A, e2⟫ with hq_def
  have hq_ne : q ≠ 0 := by
    intro hq0
    have hrepr := onb_repr he2 he1sq (C - A)
    rw [← hp_def, ← hq_def, hq0, zero_smul, add_zero, he1, smul_smul] at hrepr
    -- C - A = (p * c⁻¹) • (B - A), so A, B, C are collinear
    have hcoll : Collinear ℝ (Set.range ![A, B, C]) := by
      rw [collinear_iff_exists_forall_eq_smul_vadd]
      refine ⟨A, B - A, ?_⟩
      intro P hP
      rcases hP with ⟨i, rfl⟩
      rcases fin3_cases i with rfl | rfl | rfl
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp [vadd_eq_add]⟩
      · exact ⟨p * c⁻¹, by rw [vadd_eq_add, ← hrepr]; simp⟩
    exact hncol hcoll
  have hTA : TOf A e1 e2 A = 0 := by
    ext i
    rcases fin2_cases i with rfl | rfl <;> simp [TOf]
  have hce1 : c • e1 = B - A := by
    rw [he1]
    exact smul_inv_smul₀ hc.ne' _
  have hTB : TOf A e1 e2 B = !₂[c, 0] := by
    ext i
    rcases fin2_cases i with rfl | rfl
    · simp only [TOf_apply_zero, Matrix.cons_val_zero]
      rw [he1, real_inner_smul_right, real_inner_self_eq_norm_sq,
        ← dist_eq_norm, dist_comm B A, ← hc_def]
      field_simp [hc.ne']
    · simp only [TOf_apply_one, Matrix.cons_val_one]
      rw [he2, inner_fin2 (B - A) !₂[-(e1 1), e1 0]]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [he1]
      simp only [PiLp.smul_apply, smul_eq_mul]
      ring
  have hTC : TOf A e1 e2 C = !₂[p, q] := by
    simp only [TOf, ← hp_def, ← hq_def]
  -- squared distance of C from A
  have hC : p^2 + q^2 = (z + x)^2 := by
    have h4 : dist (TOf A e1 e2 C) (TOf A e1 e2 A) = dist C A :=
      TOf_dist he2 he1sq C A
    have h4sq := congrArg (·^2) h4
    rw [dist_sq_fin2, hTC, hTA, ← hb_def] at h4sq
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
      PiLp.zero_apply, sub_zero] at h4sq
    rw [← hzx_b] at h4sq
    exact h4sq
  -- first moments of C along e1
  have hIA : ⟪C - A, B - A⟫ = x * (x + y + z) - y * z := by
    rw [real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two]
    have hsub : C - A - (B - A) = C - B := by abel
    rw [hsub]
    simp only [← dist_eq_norm]
    rw [dist_comm B A, dist_comm C B, ← ha_def, ← hb_def, ← hc_def,
      hx_def, hy_def, hz_def]
    ring
  have hp : (x + y) * p = x * (x + y + z) - y * z := by
    rw [hxy_c, hp_def, ← real_inner_smul_right, hce1, hIA, hxy_c]
  have hQ : q^2 * (x + y)^2 = 4 * x * y * z * (x + y + z) := by
    linear_combination (x + y)^2 * hC
      - ((x + y) * p + (x * (x + y + z) - y * z)) * hp
  -- circumcenter and circumradius of ABC
  set Tabc : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2)) := ⟨![A, B, C], hABC⟩ with hTabc
  set O := Tabc.circumcenter with hO_def
  set R := Tabc.circumradius with hR_def
  have hO_oa : dist O A = R :=
    Affine.Simplex.dist_circumcenter_eq_circumradius' Tabc 0
  have hO_ob : dist O B = R :=
    Affine.Simplex.dist_circumcenter_eq_circumradius' Tabc 1
  have hO_oc : dist O C = R :=
    Affine.Simplex.dist_circumcenter_eq_circumradius' Tabc 2
  obtain ⟨W, hW1, hW2, hW3⟩ := hW
  -- image points and their coordinates
  set w0 := (TOf A e1 e2 W) 0 with hw0
  set w1 := (TOf A e1 e2 W) 1 with hw1
  set o0 := (TOf A e1 e2 O) 0 with ho0
  set o1 := (TOf A e1 e2 O) 1 with ho1
  have h5 : dist (TOf A e1 e2 O) (TOf A e1 e2 A) = dist (TOf A e1 e2 O) (TOf A e1 e2 B) := by
    rw [TOf_dist he2 he1sq, hO_oa, ← hO_ob, ← TOf_dist he2 he1sq]
  have h5sq := congrArg (·^2) h5
  rw [dist_sq_fin2, dist_sq_fin2, hTA, hTB] at h5sq
  simp only [PiLp.zero_apply, sub_zero, Matrix.cons_val_zero,
    Matrix.cons_val_one] at h5sq
  rw [← ho0, ← ho1] at h5sq
  have hO0c : c * (2 * o0) = c * c := by
    linear_combination h5sq
  have hO0 : 2 * o0 = x + y := by
    have h := mul_left_cancel₀ hc.ne' hO0c
    rw [hxy_c]
    exact h
  have h6 : dist (TOf A e1 e2 O) (TOf A e1 e2 A) = dist (TOf A e1 e2 O) (TOf A e1 e2 C) := by
    rw [TOf_dist he2 he1sq, hO_oa, ← hO_oc, ← TOf_dist he2 he1sq]
  have h6sq := congrArg (·^2) h6
  rw [dist_sq_fin2, dist_sq_fin2, hTA, hTC] at h6sq
  simp only [PiLp.zero_apply, sub_zero, Matrix.cons_val_zero,
    Matrix.cons_val_one] at h6sq
  rw [← ho0, ← ho1] at h6sq
  have h62 : 2 * o0 * p + 2 * o1 * q = (z + x)^2 := by
    have h : 2 * o0 * p + 2 * o1 * q = p^2 + q^2 := by
      linear_combination h6sq
    rw [hC] at h
    exact h
  have hO1 : 2 * q * o1 = z * (x + y + z) - x * y := by
    linear_combination h62 - p * hO0 - hp
  have h7 : dist (TOf A e1 e2 W) (TOf A e1 e2 O) = dist (TOf A e1 e2 O) (TOf A e1 e2 A) := by
    rw [TOf_dist he2 he1sq, hW3, ← hO_oa, ← TOf_dist he2 he1sq]
  have h7sq := congrArg (·^2) h7
  rw [dist_sq_fin2, dist_sq_fin2, hTA] at h7sq
  simp only [PiLp.zero_apply, sub_zero] at h7sq
  rw [← ho0, ← ho1, ← hw0, ← hw1] at h7sq
  have hcond : w0^2 - 2 * w0 * o0 + w1^2 - 2 * w1 * o1 = 0 := by
    linear_combination h7sq
  -- touch point coordinates after the rigid motion
  have hzA1 : ((a + b + c) / 2 - c) / a = z / (y + z) := by
    rw [div_eq_div_iff ha.ne' (ne_of_gt (add_pos hy hz)), hy_def, hz_def]
    ring
  have hxB1 : ((a + b + c) / 2 - a) / b = x / (z + x) := by
    rw [div_eq_div_iff hb.ne' (ne_of_gt (add_pos hz hx)), hx_def, hz_def]
    ring
  have hyC1 : ((a + b + c) / 2 - b) / c = y / (x + y) := by
    rw [div_eq_div_iff hc.ne' (ne_of_gt (add_pos hx hy)), hx_def, hy_def]
    ring
  rw [hzA1] at hA1
  rw [hxB1] at hB1
  rw [hyC1] at hC1
  have hA10 : (TOf A e1 e2 A1) 0
      = (x + y + z) * (x * y + x * z + y^2 - y * z) / ((x + y) * (y + z)) := by
    have hv : (TOf A e1 e2 A1) 0 = c + z / (y + z) * (p - c) := by
      rw [hA1, TOf_lineMap, hTB, hTC, AffineMap.lineMap_apply_module']
      simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul,
        Matrix.cons_val_zero]
      ring
    rw [← hxy_c] at hv
    rw [hv]
    field_simp [hxy, hyz]
    linear_combination z * hp
  have hA11 : (TOf A e1 e2 A1) 1 = q * z / (y + z) := by
    have hv : (TOf A e1 e2 A1) 1 = z / (y + z) * q := by
      rw [hA1, TOf_lineMap, hTB, hTC, AffineMap.lineMap_apply_module']
      simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      ring
    rw [hv]
    ring
  have hB10 : (TOf A e1 e2 B1) 0
      = z * (x * (x + y + z) - y * z) / ((x + y) * (x + z)) := by
    have hv : (TOf A e1 e2 B1) 0 = p - x / (z + x) * p := by
      rw [hB1, TOf_lineMap, hTC, hTA, AffineMap.lineMap_apply_module']
      simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul,
        Matrix.cons_val_zero,
        PiLp.zero_apply]
      ring
    rw [hv]
    have h1 : p - x / (z + x) * p = p * z / (z + x) := by
      field_simp [hzx]
      ring
    rw [h1]
    field_simp [hxy, hzx]
    linear_combination (x + z) * hp
  have hB11 : (TOf A e1 e2 B1) 1 = q * z / (x + z) := by
    have hv : (TOf A e1 e2 B1) 1 = q - x / (z + x) * q := by
      rw [hB1, TOf_lineMap, hTC, hTA, AffineMap.lineMap_apply_module']
      simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul,
        Matrix.cons_val_zero, Matrix.cons_val_one,
        PiLp.zero_apply]
      ring
    rw [hv]
    field_simp [hzx]
    ring
  have hC10 : (TOf A e1 e2 C1) 0 = y := by
    have hv : (TOf A e1 e2 C1) 0 = y / (x + y) * c := by
      rw [hC1, TOf_lineMap, hTA, hTB, AffineMap.lineMap_apply_module']
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
        Matrix.cons_val_zero,
        PiLp.zero_apply, sub_zero]
      ring
    rw [hv, ← hxy_c, div_mul_cancel₀ y (ne_of_gt (add_pos hx hy))]
  have hC11 : (TOf A e1 e2 C1) 1 = 0 := by
    have hv : (TOf A e1 e2 C1) 1 = y / (x + y) * (0 : ℝ) := by
      rw [hC1, TOf_lineMap, hTA, hTB, AffineMap.lineMap_apply_module']
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
        Matrix.cons_val_zero, Matrix.cons_val_one,
        PiLp.zero_apply, sub_zero]
      ring
    rw [hv, mul_zero]
  -- the equidistance equations in coordinates
  have h8 : dist (TOf A e1 e2 W) (TOf A e1 e2 A1)
      = dist (TOf A e1 e2 W) (TOf A e1 e2 B1) := by
    rw [TOf_dist he2 he1sq, hW1, ← TOf_dist he2 he1sq]
  have h8sq := congrArg (·^2) h8
  rw [dist_sq_fin2, dist_sq_fin2, hA10, hA11, hB10, hB11, ← hw0, ← hw1] at h8sq
  have h9 : dist (TOf A e1 e2 W) (TOf A e1 e2 B1)
      = dist (TOf A e1 e2 W) (TOf A e1 e2 C1) := by
    rw [TOf_dist he2 he1sq, hW2, ← TOf_dist he2 he1sq]
  have h9sq := congrArg (·^2) h9
  rw [dist_sq_fin2, dist_sq_fin2, hB10, hB11, hC10, hC11, ← hw0, ← hw1] at h9sq
  rw [sub_zero] at h9sq
  -- apply the algebraic core
  have hprod := core x y z q w0 w1 o0 o1 hx hy hz hq_ne hQ hO0 hO1 hcond h8sq h9sq
  -- translate back to angles
  have hIB : ⟪A - B, C - B⟫ = y * (x + y + z) - x * z := by
    rw [real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two]
    have hsub : A - B - (C - B) = A - C := by abel
    rw [hsub]
    simp only [← dist_eq_norm]
    rw [dist_comm C B, dist_comm A C, ← ha_def, ← hb_def, ← hc_def,
      hx_def, hy_def, hz_def]
    ring
  have hIC : ⟪B - C, A - C⟫ = z * (x + y + z) - x * y := by
    rw [real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two]
    have hsub : B - C - (A - C) = B - A := by abel
    rw [hsub]
    simp only [← dist_eq_norm]
    rw [dist_comm B A, dist_comm A C, ← ha_def, ← hb_def, ← hc_def,
      hx_def, hy_def, hz_def]
    ring
  rcases mul_eq_zero.mp hprod with h | h
  · rcases mul_eq_zero.mp h with h1 | h2
    · left
      rw [EuclideanGeometry.angle, vsub_eq_sub, vsub_eq_sub,
        ← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two, hIA]
      exact h1
    · right
      left
      rw [EuclideanGeometry.angle, vsub_eq_sub, vsub_eq_sub,
        ← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two, hIB]
      exact h2
  · right
    right
    rw [EuclideanGeometry.angle, vsub_eq_sub, vsub_eq_sub,
      ← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two, hIC]
    exact h

end Imo2013P3
