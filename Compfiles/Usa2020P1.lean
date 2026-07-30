/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.Convex.Side
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.Geometry.Euclidean.PerpBisector
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# USA Mathematical Olympiad 2020, Problem 1

Let $ABC$ be a fixed acute triangle inscribed in a circle $\omega$ with center $O$.
A variable point $X$ is chosen on minor arc $AB$ of $\omega$, and segments $CX$ and
$AB$ meet at $D$. Denote by $O_1$ and $O_2$ the circumcenters of triangles $ADX$ and
$BDX$, respectively. Determine all points $X$ for which the area of triangle
$OO_1O_2$ is minimized.

The answer: the area is minimized exactly for the point $X$ of the minor arc with
$CX \perp AB$, and the minimum value of the area is $\tfrac14 [ABC]$.
-/

namespace Usa2020P1

open EuclideanGeometry RealInnerProductSpace Affine

/-- The plane in which the problem takes place. -/
abbrev E := EuclideanSpace ℝ (Fin 2)

/-- The two-dimensional cross product: the signed area of the parallelogram
spanned by two vectors. -/
def cross (u v : E) : ℝ := u 0 * v 1 - u 1 * v 0

/-- Rotation of a plane vector by 90 degrees. -/
def rot90 (u : E) : E := WithLp.toLp 2 (![-u 1, u 0] : Fin 2 → ℝ)

/-- The area of a triangle with vertices `P`, `Q`, `R`. -/
noncomputable def area (P Q R : E) : ℝ := |cross (Q -ᵥ P) (R -ᵥ P)| / 2

snip begin

lemma inner_coord (u v : E) : ⟪u, v⟫ = u 0 * v 0 + u 1 * v 1 := by
  simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, RCLike.conj_to_real]
  ring

lemma cross_comm (u v : E) : cross u v = -cross v u := by
  simp [cross]; ring

lemma cross_self (u : E) : cross u u = 0 := by
  simp [cross, mul_comm]

lemma cross_add_left (u v w : E) : cross (u + v) w = cross u w + cross v w := by
  simp [cross]; ring

lemma cross_add_right (u v w : E) : cross u (v + w) = cross u v + cross u w := by
  simp [cross]; ring

lemma cross_sub_left (u v w : E) : cross (u - v) w = cross u w - cross v w := by
  simp [cross]; ring

lemma cross_sub_right (u v w : E) : cross u (v - w) = cross u v - cross u w := by
  simp [cross]; ring

lemma cross_smul_left (c : ℝ) (u v : E) : cross (c • u) v = c * cross u v := by
  simp [cross]; ring

lemma cross_smul_right (c : ℝ) (u v : E) : cross u (c • v) = c * cross u v := by
  simp [cross]; ring

lemma cross_neg_left (u v : E) : cross (-u) v = -cross u v := by
  simp [cross]; ring

lemma cross_neg_right (u v : E) : cross u (-v) = -cross u v := by
  simp [cross]; ring

/-- The two-dimensional Lagrange identity. -/
lemma lagrange (u v : E) : cross u v ^ 2 = ⟪u, u⟫ * ⟪v, v⟫ - ⟪u, v⟫ ^ 2 := by
  simp only [cross, inner_coord]; ring

lemma inner_rot90_left (u v : E) : ⟪rot90 u, v⟫ = cross u v := by
  simp [rot90, inner_coord, cross]; ring

lemma inner_rot90_self (u : E) : ⟪u, rot90 u⟫ = 0 := by
  simp [rot90, inner_coord]; ring

/-- Expansion of a vector in the orthogonal basis `(w, rot90 w)`. -/
lemma basis_decomp (v w : E) :
    ⟪w, w⟫ • v = ⟪v, w⟫ • w + cross w v • rot90 w := by
  ext i
  fin_cases i <;>
    simp only [Fin.mk_zero, Fin.mk_one, rot90, Matrix.cons_val_zero, Matrix.cons_val_one,
      PiLp.smul_apply, PiLp.add_apply, smul_eq_mul, inner_coord, cross] <;> ring

/-- Two vectors orthogonal to a nonzero vector are parallel. -/
lemma cross_eq_zero_of_inner_eq_zero {a b w : E}
    (ha : ⟪a, w⟫ = 0) (hb : ⟪b, w⟫ = 0) (hw : w ≠ 0) : cross a b = 0 := by
  have hw2 : ⟪w, w⟫ ≠ 0 := by
    rw [ne_eq, inner_self_eq_zero]; exact hw
  have e1 := basis_decomp a w
  have e2 := basis_decomp b w
  rw [ha, zero_smul, zero_add] at e1
  rw [hb, zero_smul, zero_add] at e2
  have e3 : ⟪w, w⟫ * (⟪w, w⟫ * cross a b) = 0 := by
    have e4 := congrArg₂ cross e1 e2
    simp only [cross_smul_left, cross_smul_right, cross_self, mul_zero] at e4
    exact e4
  rcases mul_eq_zero.mp e3 with h | h
  · exact absurd h hw2
  · exact (mul_eq_zero.mp h).resolve_left hw2

/-- If `u ⟂ w` and `v ∥ w`, then `u ⟂ v`. -/
lemma inner_eq_zero_of_cross_eq_zero {u v w : E}
    (hu : ⟪u, w⟫ = 0) (hv : cross v w = 0) (hw : w ≠ 0) : ⟪u, v⟫ = 0 := by
  have hw2 : ⟪w, w⟫ ≠ 0 := by
    rw [ne_eq, inner_self_eq_zero]; exact hw
  have e1 := basis_decomp v w
  rw [cross_comm w v, hv, neg_zero, zero_smul, add_zero] at e1
  have e2 := congrArg (fun y ↦ ⟪u, y⟫) e1
  rw [real_inner_smul_right, real_inner_smul_right, hu, mul_zero] at e2
  exact (mul_eq_zero.mp e2).resolve_left hw2

/-- The line through two points of a perpendicular bisector is orthogonal to the segment. -/
lemma inner_vsub_of_mem_perpBisector {P Q R S : E}
    (hP : P ∈ AffineSubspace.perpBisector R S) (hQ : Q ∈ AffineSubspace.perpBisector R S) :
    ⟪S -ᵥ R, Q -ᵥ P⟫ = 0 := by
  have h3 : Q -ᵥ P ∈ (AffineSubspace.perpBisector R S).direction :=
    AffineSubspace.vsub_mem_direction hQ hP
  rw [AffineSubspace.direction_perpBisector] at h3
  have h4 := Submodule.mem_orthogonal_singleton_iff_inner_left.mp h3
  rw [real_inner_comm] at h4
  exact h4

/-- The difference of two midpoints with a common endpoint is half the difference. -/
lemma midpoint_vsub_midpoint (P Q R : E) :
    midpoint ℝ P R -ᵥ midpoint ℝ Q R = (2⁻¹ : ℝ) • (P -ᵥ Q) := by
  simp only [midpoint_eq_smul_add, vsub_eq_sub, invOf_eq_inv]; module

/-- A line meets a circle in at most two points. -/
lemma eq_or_eq_of_mem_line_of_dist {P Q Y O : E} (hPQ : P ≠ Q)
    (hP : dist P O = dist Q O) (hY : dist Y O = dist P O)
    (s : ℝ) (hs : Y -ᵥ P = s • (Q -ᵥ P)) : Y = P ∨ Y = Q := by
  have hQP : ‖Q -ᵥ P‖ ^ 2 ≠ 0 := by
    rw [ne_eq, sq_eq_zero_iff, norm_eq_zero, vsub_eq_zero_iff_eq]
    exact hPQ.symm
  have eY : ‖Y -ᵥ O‖ ^ 2 = ‖P -ᵥ O‖ ^ 2 := by
    rw [dist_eq_norm_vsub, dist_eq_norm_vsub] at hY; rw [hY]
  have eQ : ‖P -ᵥ O‖ ^ 2 = ‖Q -ᵥ O‖ ^ 2 := by
    rw [dist_eq_norm_vsub, dist_eq_norm_vsub] at hP; rw [hP]
  have hdecompY : Y -ᵥ O = s • (Q -ᵥ P) + (P -ᵥ O) := by
    calc Y -ᵥ O = (Y -ᵥ P) + (P -ᵥ O) := by rw [vsub_add_vsub_cancel]
      _ = s • (Q -ᵥ P) + (P -ᵥ O) := by rw [hs]
  have hdecompQ : Q -ᵥ O = (Q -ᵥ P) + (P -ᵥ O) := by rw [vsub_add_vsub_cancel]
  rw [hdecompY, norm_add_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    real_inner_smul_left] at eY
  rw [hdecompQ, norm_add_sq_real] at eQ
  have hfact : s * (s - 1) * ‖Q -ᵥ P‖ ^ 2 = 0 := by
    linear_combination eY + s * eQ
  rcases mul_eq_zero.mp hfact with h | h
  · rcases mul_eq_zero.mp h with h0 | h1
    · left
      rw [h0, zero_smul] at hs
      exact vsub_eq_zero_iff_eq.mp hs
    · right
      have h1' : s = 1 := by linarith
      rw [h1', one_smul] at hs
      have h2 : (Y : E) - P = Q - P := by simpa only [vsub_eq_sub] using hs
      exact sub_left_inj.mp h2
  · exact absurd h hQP

/-- The main identity: twice the signed area of `OO₁O₂` squared equals
`¼ ‖O₁O₂‖² ‖CD‖²`. -/
lemma main_identity
    (C X D O O₁ O₂ : E)
    (hO1X : dist O₁ D = dist O₁ X)
    (hO2X : dist O₂ D = dist O₂ X)
    (hOCX : dist O C = dist O X)
    (r : ℝ) (hr : D -ᵥ C = r • (X -ᵥ C))
    (hXD : X ≠ D) :
    cross (O₁ -ᵥ O) (O₂ -ᵥ O) ^ 2 =
      (1 / 4) * ⟪O₁ -ᵥ O₂, O₁ -ᵥ O₂⟫ * ⟪C -ᵥ D, C -ᵥ D⟫ := by
  have hF1 : ⟪X -ᵥ D, O₂ -ᵥ O₁⟫ = 0 :=
    inner_vsub_of_mem_perpBisector
      (AffineSubspace.mem_perpBisector_iff_dist_eq.mpr hO1X)
      (AffineSubspace.mem_perpBisector_iff_dist_eq.mpr hO2X)
  have hF4 : ⟪X -ᵥ D, midpoint ℝ D X -ᵥ O₂⟫ = 0 :=
    inner_vsub_of_mem_perpBisector
      (AffineSubspace.mem_perpBisector_iff_dist_eq.mpr hO2X)
      (AffineSubspace.midpoint_mem_perpBisector D X)
  have hF2 : ⟪X -ᵥ C, midpoint ℝ C X -ᵥ O⟫ = 0 :=
    inner_vsub_of_mem_perpBisector
      (AffineSubspace.mem_perpBisector_iff_dist_eq.mpr hOCX)
      (AffineSubspace.midpoint_mem_perpBisector C X)
  have hw : X -ᵥ D ≠ 0 := vsub_ne_zero.mpr hXD
  have huw : ⟪O₁ -ᵥ O₂, X -ᵥ D⟫ = 0 := by
    rw [← neg_vsub_eq_vsub_rev O₂ O₁, inner_neg_left,
      real_inner_comm (X -ᵥ D) (O₂ -ᵥ O₁), hF1, neg_zero]
  have hwXC : X -ᵥ D = (1 - r) • (X -ᵥ C) := by
    calc X -ᵥ D = (X -ᵥ C) - (D -ᵥ C) := by rw [vsub_sub_vsub_cancel_right]
      _ = (1 - r) • (X -ᵥ C) := by rw [hr]; simp only [vsub_eq_sub]; module
  have h1r : 1 - r ≠ 0 := by
    intro h
    apply hw
    rw [hwXC, h, zero_smul]
  have hO2N : ⟪O₂ -ᵥ midpoint ℝ D X, X -ᵥ D⟫ = 0 := by
    rw [← neg_vsub_eq_vsub_rev (midpoint ℝ D X) O₂, inner_neg_left,
      real_inner_comm (X -ᵥ D) (midpoint ℝ D X -ᵥ O₂), hF4, neg_zero]
  have hMO : ⟪midpoint ℝ C X -ᵥ O, X -ᵥ D⟫ = 0 := by
    rw [hwXC, real_inner_smul_right,
      show ⟪midpoint ℝ C X -ᵥ O, X -ᵥ C⟫ = 0 from by
        rw [real_inner_comm]; exact hF2, mul_zero]
  have hNM : midpoint ℝ D X -ᵥ midpoint ℝ C X = (2⁻¹ : ℝ) • (D -ᵥ C) :=
    midpoint_vsub_midpoint D C X
  have hS : cross (O₁ -ᵥ O) (O₂ -ᵥ O) =
      cross (O₁ -ᵥ O₂) (midpoint ℝ D X -ᵥ midpoint ℝ C X) := by
    have e1 : O₁ -ᵥ O = (O₁ -ᵥ O₂) + ((O₂ -ᵥ midpoint ℝ D X) +
        (midpoint ℝ D X -ᵥ midpoint ℝ C X) + (midpoint ℝ C X -ᵥ O)) := by
      simp only [vsub_eq_sub]; module
    have e2 : O₂ -ᵥ O = (O₂ -ᵥ midpoint ℝ D X) +
        (midpoint ℝ D X -ᵥ midpoint ℝ C X) + (midpoint ℝ C X -ᵥ O) := by
      simp only [vsub_eq_sub]; module
    rw [e1, e2, cross_add_left, cross_self, add_zero, cross_add_right, cross_add_right,
      cross_eq_zero_of_inner_eq_zero huw hO2N hw,
      cross_eq_zero_of_inner_eq_zero huw hMO hw, add_zero, zero_add]
  have huDC : ⟪O₁ -ᵥ O₂, D -ᵥ C⟫ = 0 := by
    have huXC : ⟪O₁ -ᵥ O₂, X -ᵥ C⟫ = 0 := by
      have e5 : (1 - r) * ⟪O₁ -ᵥ O₂, X -ᵥ C⟫ = 0 := by
        rw [← real_inner_smul_right, ← hwXC]; exact huw
      exact (mul_eq_zero.mp e5).resolve_left h1r
    rw [hr, real_inner_smul_right, huXC, mul_zero]
  have hL := lagrange (O₁ -ᵥ O₂) (D -ᵥ C)
  rw [huDC] at hL
  rw [hS, hNM, cross_smul_right]
  have hCDC : ⟪D -ᵥ C, D -ᵥ C⟫ = ⟪C -ᵥ D, C -ᵥ D⟫ := by
    rw [← neg_vsub_eq_vsub_rev D C, inner_neg_neg]
  rw [hCDC] at hL
  linear_combination (1 / 4) * hL

/-- The projection of `O₁O₂` onto line `AB` has signed length `-AB²/2`. -/
lemma proj_inner
    (A B D O₁ O₂ : E)
    (hO1A : dist O₁ A = dist O₁ D)
    (hO2B : dist O₂ B = dist O₂ D)
    (t : ℝ) (ht : D -ᵥ A = t • (B -ᵥ A)) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    ⟪O₁ -ᵥ O₂, B -ᵥ A⟫ = -⟪B -ᵥ A, B -ᵥ A⟫ / 2 := by
  have hF5 : ⟪D -ᵥ A, midpoint ℝ A D -ᵥ O₁⟫ = 0 :=
    inner_vsub_of_mem_perpBisector
      (AffineSubspace.mem_perpBisector_iff_dist_eq.mpr hO1A)
      (AffineSubspace.midpoint_mem_perpBisector A D)
  have hF6 : ⟪D -ᵥ B, midpoint ℝ B D -ᵥ O₂⟫ = 0 :=
    inner_vsub_of_mem_perpBisector
      (AffineSubspace.mem_perpBisector_iff_dist_eq.mpr hO2B)
      (AffineSubspace.midpoint_mem_perpBisector B D)
  have hP1 : ⟪midpoint ℝ A D -ᵥ O₁, B -ᵥ A⟫ = 0 := by
    have e1 : t * ⟪midpoint ℝ A D -ᵥ O₁, B -ᵥ A⟫ = 0 := by
      rw [← real_inner_smul_right, ← ht, real_inner_comm]; exact hF5
    exact (mul_eq_zero.mp e1).resolve_left ht0
  have hP2 : ⟪midpoint ℝ B D -ᵥ O₂, B -ᵥ A⟫ = 0 := by
    have htB : D -ᵥ B = (t - 1) • (B -ᵥ A) := by
      calc D -ᵥ B = (D -ᵥ A) - (B -ᵥ A) := by rw [vsub_sub_vsub_cancel_right]
        _ = (t - 1) • (B -ᵥ A) := by rw [ht]; simp only [vsub_eq_sub]; module
    have ht10 : t - 1 ≠ 0 := sub_ne_zero.mpr ht1
    have e2 : (t - 1) * ⟪midpoint ℝ B D -ᵥ O₂, B -ᵥ A⟫ = 0 := by
      rw [← real_inner_smul_right, ← htB, real_inner_comm]; exact hF6
    exact (mul_eq_zero.mp e2).resolve_left ht10
  have hP12 : midpoint ℝ A D -ᵥ midpoint ℝ B D = (2⁻¹ : ℝ) • (A -ᵥ B) :=
    midpoint_vsub_midpoint A B D
  have hO1P1 : ⟪O₁ -ᵥ midpoint ℝ A D, B -ᵥ A⟫ = 0 := by
    rw [← neg_vsub_eq_vsub_rev (midpoint ℝ A D) O₁, inner_neg_left, hP1, neg_zero]
  have hdecomp : O₁ -ᵥ O₂ = (O₁ -ᵥ midpoint ℝ A D) +
      (midpoint ℝ A D -ᵥ midpoint ℝ B D) + (midpoint ℝ B D -ᵥ O₂) := by
    simp only [vsub_eq_sub]; module
  have hAB2 : ⟪A -ᵥ B, B -ᵥ A⟫ = -⟪B -ᵥ A, B -ᵥ A⟫ := by
    have e : A -ᵥ B = -(B -ᵥ A) := (neg_vsub_eq_vsub_rev B A).symm
    rw [e, inner_neg_left]
  rw [hdecomp, inner_add_left, inner_add_left, hO1P1, zero_add, hP2, add_zero, hP12,
    real_inner_smul_left, hAB2]
  ring

/-- The height bound: `‖CD‖²·‖AB‖² = ⟪C−D, B−A⟫² + T²`. -/
lemma height_sq (A B C D : E) (t : ℝ) (ht : D -ᵥ A = t • (B -ᵥ A)) :
    ⟪C -ᵥ D, C -ᵥ D⟫ * ⟪B -ᵥ A, B -ᵥ A⟫ =
      ⟪C -ᵥ D, B -ᵥ A⟫ ^ 2 + cross (B -ᵥ A) (C -ᵥ A) ^ 2 := by
  have hL := lagrange (C -ᵥ D) (B -ᵥ A)
  have hcross : cross (C -ᵥ D) (B -ᵥ A) = -cross (B -ᵥ A) (C -ᵥ A) := by
    have e1 : C -ᵥ D = (C -ᵥ A) - t • (B -ᵥ A) := by
      calc C -ᵥ D = (C -ᵥ A) - (D -ᵥ A) := by rw [vsub_sub_vsub_cancel_right]
        _ = (C -ᵥ A) - t • (B -ᵥ A) := by rw [ht]
    rw [e1, cross_sub_left, cross_smul_left, cross_self, mul_zero, sub_zero, cross_comm]
  have hcross2 : cross (C -ᵥ D) (B -ᵥ A) ^ 2 = cross (B -ᵥ A) (C -ᵥ A) ^ 2 := by
    rw [hcross, neg_sq]
  linear_combination hcross2 - hL

/-- The key estimate `16·[OO₁O₂]² ≥ (2[ABC])²` together with the equality
characterization: equality holds iff `CX ⊥ AB`. -/
lemma area_key
    (A B C X D O O₁ O₂ : E)
    (hAB : A ≠ B) (hXC : X ≠ C) (hXD : X ≠ D)
    (hO1A : dist O₁ A = dist O₁ D) (hO1X : dist O₁ D = dist O₁ X)
    (hO2B : dist O₂ B = dist O₂ D) (hO2X : dist O₂ D = dist O₂ X)
    (hOCX : dist O C = dist O X)
    (t : ℝ) (ht : D -ᵥ A = t • (B -ᵥ A)) (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (r : ℝ) (hr : D -ᵥ C = r • (X -ᵥ C)) (hr0 : r ≠ 0) :
    cross (B -ᵥ A) (C -ᵥ A) ^ 2 ≤ 16 * cross (O₁ -ᵥ O) (O₂ -ᵥ O) ^ 2 ∧
    (16 * cross (O₁ -ᵥ O) (O₂ -ᵥ O) ^ 2 = cross (B -ᵥ A) (C -ᵥ A) ^ 2 ↔
      ⟪X -ᵥ C, B -ᵥ A⟫ = 0) := by
  have hb : 0 < ⟪B -ᵥ A, B -ᵥ A⟫ := real_inner_self_pos.mpr (vsub_ne_zero.mpr hAB.symm)
  have eI := main_identity C X D O O₁ O₂ hO1X hO2X hOCX r hr hXD
  have eP := proj_inner A B D O₁ O₂ hO1A hO2B t ht ht0 ht1
  have eH := height_sq A B C D t ht
  have eL := lagrange (O₁ -ᵥ O₂) (B -ᵥ A)
  have key : 16 * cross (O₁ -ᵥ O) (O₂ -ᵥ O) ^ 2 * ⟪B -ᵥ A, B -ᵥ A⟫ ^ 2 =
      4 * (⟪B -ᵥ A, B -ᵥ A⟫ ^ 2 / 4 + cross (O₁ -ᵥ O₂) (B -ᵥ A) ^ 2) *
        (cross (B -ᵥ A) (C -ᵥ A) ^ 2 + ⟪C -ᵥ D, B -ᵥ A⟫ ^ 2) := by
    linear_combination
      (16 * ⟪B -ᵥ A, B -ᵥ A⟫ ^ 2) * eI
        + (4 * ⟪B -ᵥ A, B -ᵥ A⟫ * ⟪O₁ -ᵥ O₂, O₁ -ᵥ O₂⟫) * eH
        - (4 * (cross (B -ᵥ A) (C -ᵥ A) ^ 2 + ⟪C -ᵥ D, B -ᵥ A⟫ ^ 2)) * eL
        + (4 * (cross (B -ᵥ A) (C -ᵥ A) ^ 2 + ⟪C -ᵥ D, B -ᵥ A⟫ ^ 2) *
            (⟪O₁ -ᵥ O₂, B -ᵥ A⟫ - ⟪B -ᵥ A, B -ᵥ A⟫ / 2)) * eP
  have hb2 : (0:ℝ) < ⟪B -ᵥ A, B -ᵥ A⟫ ^ 2 := pow_pos hb 2
  have hge : cross (B -ᵥ A) (C -ᵥ A) ^ 2 * ⟪B -ᵥ A, B -ᵥ A⟫ ^ 2 ≤
      16 * cross (O₁ -ᵥ O) (O₂ -ᵥ O) ^ 2 * ⟪B -ᵥ A, B -ᵥ A⟫ ^ 2 := by
    rw [key]
    have hexp : 4 * (⟪B -ᵥ A, B -ᵥ A⟫ ^ 2 / 4 + cross (O₁ -ᵥ O₂) (B -ᵥ A) ^ 2) *
          (cross (B -ᵥ A) (C -ᵥ A) ^ 2 + ⟪C -ᵥ D, B -ᵥ A⟫ ^ 2) -
        cross (B -ᵥ A) (C -ᵥ A) ^ 2 * ⟪B -ᵥ A, B -ᵥ A⟫ ^ 2 =
      ⟪B -ᵥ A, B -ᵥ A⟫ ^ 2 * ⟪C -ᵥ D, B -ᵥ A⟫ ^ 2 +
        4 * cross (O₁ -ᵥ O₂) (B -ᵥ A) ^ 2 *
          (cross (B -ᵥ A) (C -ᵥ A) ^ 2 + ⟪C -ᵥ D, B -ᵥ A⟫ ^ 2) := by
      ring
    have hnn : 0 ≤ ⟪B -ᵥ A, B -ᵥ A⟫ ^ 2 * ⟪C -ᵥ D, B -ᵥ A⟫ ^ 2 +
        4 * cross (O₁ -ᵥ O₂) (B -ᵥ A) ^ 2 *
          (cross (B -ᵥ A) (C -ᵥ A) ^ 2 + ⟪C -ᵥ D, B -ᵥ A⟫ ^ 2) := by
      apply add_nonneg
      · exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
      · exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
          (add_nonneg (sq_nonneg _) (sq_nonneg _))
    linarith [hexp, hnn]
  have hineq : cross (B -ᵥ A) (C -ᵥ A) ^ 2 ≤ 16 * cross (O₁ -ᵥ O) (O₂ -ᵥ O) ^ 2 :=
    le_of_mul_le_mul_right hge hb2
  -- auxiliary relations needed for the equality characterization
  have huXC : ⟪O₁ -ᵥ O₂, X -ᵥ C⟫ = 0 := by
    have hF1 : ⟪X -ᵥ D, O₂ -ᵥ O₁⟫ = 0 :=
      inner_vsub_of_mem_perpBisector
        (AffineSubspace.mem_perpBisector_iff_dist_eq.mpr hO1X)
        (AffineSubspace.mem_perpBisector_iff_dist_eq.mpr hO2X)
    have huw : ⟪O₁ -ᵥ O₂, X -ᵥ D⟫ = 0 := by
      rw [← neg_vsub_eq_vsub_rev O₂ O₁, inner_neg_left,
        real_inner_comm (X -ᵥ D) (O₂ -ᵥ O₁), hF1, neg_zero]
    have hwXC : X -ᵥ D = (1 - r) • (X -ᵥ C) := by
      calc X -ᵥ D = (X -ᵥ C) - (D -ᵥ C) := by rw [vsub_sub_vsub_cancel_right]
        _ = (1 - r) • (X -ᵥ C) := by rw [hr]; simp only [vsub_eq_sub]; module
    have h1r : 1 - r ≠ 0 := by
      intro h
      have hz : X -ᵥ D = 0 := by rw [hwXC, h, zero_smul]
      exact hXD (vsub_eq_zero_iff_eq.mp hz)
    have e5 : (1 - r) * ⟪O₁ -ᵥ O₂, X -ᵥ C⟫ = 0 := by
      rw [← real_inner_smul_right, ← hwXC]; exact huw
    exact (mul_eq_zero.mp e5).resolve_left h1r
  have hci2 : ⟪C -ᵥ D, B -ᵥ A⟫ = -r * ⟪X -ᵥ C, B -ᵥ A⟫ := by
    have e : C -ᵥ D = -(D -ᵥ C) := (neg_vsub_eq_vsub_rev D C).symm
    rw [e, inner_neg_left, hr, real_inner_smul_left, ← neg_mul]
  refine ⟨hineq, ?_, ?_⟩
  · intro heq
    have hsum : ⟪B -ᵥ A, B -ᵥ A⟫ ^ 2 * ⟪C -ᵥ D, B -ᵥ A⟫ ^ 2 +
        4 * cross (O₁ -ᵥ O₂) (B -ᵥ A) ^ 2 *
          (cross (B -ᵥ A) (C -ᵥ A) ^ 2 + ⟪C -ᵥ D, B -ᵥ A⟫ ^ 2) = 0 := by
      linear_combination ⟪B -ᵥ A, B -ᵥ A⟫ ^ 2 * heq - key
    have hterm1 : ⟪B -ᵥ A, B -ᵥ A⟫ ^ 2 * ⟪C -ᵥ D, B -ᵥ A⟫ ^ 2 = 0 := by
      have g1 : 0 ≤ ⟪B -ᵥ A, B -ᵥ A⟫ ^ 2 * ⟪C -ᵥ D, B -ᵥ A⟫ ^ 2 :=
        mul_nonneg (sq_nonneg _) (sq_nonneg _)
      have g2 : 0 ≤ 4 * cross (O₁ -ᵥ O₂) (B -ᵥ A) ^ 2 *
          (cross (B -ᵥ A) (C -ᵥ A) ^ 2 + ⟪C -ᵥ D, B -ᵥ A⟫ ^ 2) :=
        mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
          (add_nonneg (sq_nonneg _) (sq_nonneg _))
      exact ((add_eq_zero_iff_of_nonneg g1 g2).mp hsum).1
    have hci : ⟪C -ᵥ D, B -ᵥ A⟫ = 0 := by
      have hsq : ⟪C -ᵥ D, B -ᵥ A⟫ ^ 2 = 0 :=
        (mul_eq_zero.mp hterm1).resolve_left (pow_ne_zero 2 hb.ne')
      exact sq_eq_zero_iff.mp hsq
    rw [hci2] at hci
    rcases mul_eq_zero.mp hci with h | h
    · exact absurd (neg_eq_zero.mp h) hr0
    · exact h
  · intro hXCperp
    have hci : ⟪C -ᵥ D, B -ᵥ A⟫ = 0 := by
      rw [hci2, hXCperp, mul_zero]
    have hcu : cross (O₁ -ᵥ O₂) (B -ᵥ A) = 0 :=
      cross_eq_zero_of_inner_eq_zero huXC (by rw [real_inner_comm]; exact hXCperp)
        (vsub_ne_zero.mpr hXC)
    rw [hci, hcu] at key
    have hfin : 16 * cross (O₁ -ᵥ O) (O₂ -ᵥ O) ^ 2 * ⟪B -ᵥ A, B -ᵥ A⟫ ^ 2 =
        cross (B -ᵥ A) (C -ᵥ A) ^ 2 * ⟪B -ᵥ A, B -ᵥ A⟫ ^ 2 := by
      linear_combination key
    exact mul_right_cancel₀ (pow_ne_zero 2 hb.ne') hfin

lemma inner_rot90_right (u v : E) : ⟪u, rot90 v⟫ = -cross u v := by
  simp [rot90, inner_coord, cross]; ring

lemma inner_rot90_rot90 (u v : E) : ⟪rot90 u, rot90 v⟫ = ⟪u, v⟫ := by
  simp [rot90, inner_coord]; ring

/-- An acute angle has positive inner product. -/
lemma inner_pos_of_angle_lt_pi_div_two (p q r : E)
    (hq1 : p ≠ q) (hq2 : r ≠ q) (h : ∠ p q r < Real.pi / 2) :
    0 < ⟪p -ᵥ q, r -ᵥ q⟫ := by
  have hcos : Real.cos (∠ p q r) = ⟪p -ᵥ q, r -ᵥ q⟫ / (‖p -ᵥ q‖ * ‖r -ᵥ q‖) := by
    rw [EuclideanGeometry.angle]; exact InnerProductGeometry.cos_angle _ _
  have hpos : 0 < Real.cos (∠ p q r) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, EuclideanGeometry.angle_nonneg p q r], h⟩
  rw [hcos] at hpos
  have hden : 0 < ‖p -ᵥ q‖ * ‖r -ᵥ q‖ := by
    apply mul_pos <;> rw [norm_pos_iff] <;> [exact vsub_ne_zero.mpr hq1; exact vsub_ne_zero.mpr hq2]
  nlinarith [mul_pos hpos hden, div_mul_cancel₀ (⟪p -ᵥ q, r -ᵥ q⟫) (ne_of_gt hden)]

/-- The inner product of a circumcenter-related difference is half the squared length. -/
lemma inner_vsub_eq_half {O P Q : E} (h : dist O P = dist O Q) :
    ⟪O -ᵥ P, Q -ᵥ P⟫ = ⟪Q -ᵥ P, Q -ᵥ P⟫ / 2 := by
  have h1 : O ∈ AffineSubspace.perpBisector P Q :=
    AffineSubspace.mem_perpBisector_iff_dist_eq.mpr h
  rw [AffineSubspace.mem_perpBisector_iff_inner_eq_zero] at h1
  have h2 : O -ᵥ P = (O -ᵥ midpoint ℝ P Q) + (midpoint ℝ P Q -ᵥ P) := by
    simp only [vsub_eq_sub]; module
  rw [h2, inner_add_left, h1, zero_add, midpoint_vsub_left, invOf_eq_inv, real_inner_smul_left]
  ring

/-- A point with vanishing cross product against `R −ᵥ Q` lies on line `QR`. -/
lemma mem_line_of_cross_eq_zero {P Q R : E} (hQR : Q ≠ R)
    (h : cross (R -ᵥ Q) (P -ᵥ Q) = 0) : P ∈ line[ℝ, Q, R] := by
  apply mem_affineSpan_pair_iff_exists_lineMap_eq.mpr
  have hb_pos : 0 < ⟪R -ᵥ Q, R -ᵥ Q⟫ := real_inner_self_pos.mpr (vsub_ne_zero.mpr hQR.symm)
  have hβ : ⟪R -ᵥ Q, R -ᵥ Q⟫ ≠ 0 := ne_of_gt hb_pos
  have hbd := basis_decomp (P -ᵥ Q) (R -ᵥ Q)
  rw [h, zero_smul, add_zero] at hbd
  refine ⟨⟪P -ᵥ Q, R -ᵥ Q⟫ / ⟪R -ᵥ Q, R -ᵥ Q⟫, ?_⟩
  rw [AffineMap.lineMap_apply]
  have e2 : ⟪R -ᵥ Q, R -ᵥ Q⟫ • (P -ᵥ Q) = ⟪R -ᵥ Q, R -ᵥ Q⟫ •
      ((⟪P -ᵥ Q, R -ᵥ Q⟫ / ⟪R -ᵥ Q, R -ᵥ Q⟫) • (R -ᵥ Q)) := by
    rw [smul_smul, mul_div_cancel₀ _ hβ, hbd]
  have e4 := congrArg (fun y ↦ (⟪R -ᵥ Q, R -ᵥ Q⟫)⁻¹ • y) e2
  rw [inv_smul_smul₀ hβ, inv_smul_smul₀ hβ] at e4
  rw [← e4, vsub_vadd]

snip end

/-- The set of points for which the area of `OO₁O₂` is minimized: exactly the
points `X` with `CX ⊥ AB`. -/
determine minimizers (A B C : E) : Set E := {X | ⟪X -ᵥ C, B -ᵥ A⟫ = 0}

set_option linter.unusedVariables false in
problem usa2020_p1 (A B C X D O O₁ O₂ : E)
    (htri : AffineIndependent ℝ ![A, B, C])
    (hacuteA : ∠ B A C < Real.pi / 2) (hacuteB : ∠ A B C < Real.pi / 2)
    (hacuteC : ∠ B C A < Real.pi / 2)
    (hOA : dist O A = dist O B) (hOB : dist O B = dist O C)
    (hX : dist X O = dist A O)
    (hside : (line[ℝ, A, B]).SOppSide C X)
    (hDAB : D ∈ line[ℝ, A, B]) (hDCX : D ∈ line[ℝ, C, X])
    (hO1A : dist O₁ A = dist O₁ D) (hO1X : dist O₁ D = dist O₁ X)
    (hO2B : dist O₂ B = dist O₂ D) (hO2X : dist O₂ D = dist O₂ X) :
    area A B C / 4 ≤ area O O₁ O₂ ∧
      (area O O₁ O₂ = area A B C / 4 ↔ X ∈ minimizers A B C) := by
  have hAB : A ≠ B := by simpa using htri.injective.ne (show (0 : Fin 3) ≠ 1 by decide)
  have hAC : A ≠ C := by simpa using htri.injective.ne (show (0 : Fin 3) ≠ 2 by decide)
  have hBC : B ≠ C := by simpa using htri.injective.ne (show (1 : Fin 3) ≠ 2 by decide)
  have hCline : C ∉ line[ℝ, A, B] := hside.left_notMem
  have hXline : X ∉ line[ℝ, A, B] := hside.right_notMem
  have hXC : X ≠ C := by
    intro h
    rw [h] at hside
    exact AffineSubspace.not_sOppSide_self _ _ hside
  have hXD : X ≠ D := by
    intro h
    exact hXline (h.symm ▸ hDAB)
  have hDC : D ≠ C := by
    intro h
    rw [h] at hDAB
    exact hCline hDAB
  obtain ⟨t, ht⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hDAB
  rw [AffineMap.lineMap_apply] at ht
  have ht' : D -ᵥ A = t • (B -ᵥ A) := by rw [← ht, vadd_vsub]
  obtain ⟨r, hr⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hDCX
  rw [AffineMap.lineMap_apply] at hr
  have hr' : D -ᵥ C = r • (X -ᵥ C) := by rw [← hr, vadd_vsub]
  have hr0 : r ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hr'
    exact hDC (vsub_eq_zero_iff_eq.mp hr')
  have hOCX : dist O C = dist O X := by
    rw [← hOB, ← hOA, dist_comm O A, ← hX, dist_comm X O]
  have ht0 : t ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at ht'
    have hDA : D = A := vsub_eq_zero_iff_eq.mp ht'
    rw [hDA] at hDCX
    obtain ⟨s₁, hs₁⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hDCX
    rw [AffineMap.lineMap_apply] at hs₁
    have hs₁' : A -ᵥ C = s₁ • (X -ᵥ C) := by rw [← hs₁, vadd_vsub]
    have hs1ne : s₁ ≠ 0 := by
      intro hz
      rw [hz, zero_smul] at hs₁'
      exact hAC (vsub_eq_zero_iff_eq.mp hs₁')
    have hCO : dist C O = dist A O := by
      rw [dist_comm C O, dist_comm A O, hOA, hOB]
    have hcase := eq_or_eq_of_mem_line_of_dist (P := C) (Q := A) (Y := X) (O := O)
      hAC.symm hCO (hX.trans hCO.symm) s₁⁻¹ (by
        have e1 : X -ᵥ C = s₁⁻¹ • (A -ᵥ C) := by
          rw [hs₁', smul_smul, inv_mul_cancel₀ hs1ne, one_smul]
        exact e1)
    rcases hcase with h | h
    · exact hXC h
    · exact hXline (h.symm ▸ left_mem_affineSpan_pair ℝ A B)
  have ht1 : t ≠ 1 := by
    intro h1
    rw [h1, one_smul] at ht'
    have hDB : D = B := by
      have e1 : (D : E) - A = B - A := by simpa only [vsub_eq_sub] using ht'
      exact sub_left_inj.mp e1
    rw [hDB] at hDCX
    obtain ⟨s₂, hs₂⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hDCX
    rw [AffineMap.lineMap_apply] at hs₂
    have hs₂' : B -ᵥ C = s₂ • (X -ᵥ C) := by rw [← hs₂, vadd_vsub]
    have hs2ne : s₂ ≠ 0 := by
      intro hz
      rw [hz, zero_smul] at hs₂'
      exact hBC (vsub_eq_zero_iff_eq.mp hs₂')
    have hCO : dist C O = dist A O := by
      rw [dist_comm C O, dist_comm A O, hOA, hOB]
    have hCOB : dist C O = dist B O := by
      rw [dist_comm C O, dist_comm B O, hOB]
    have hcase := eq_or_eq_of_mem_line_of_dist (P := C) (Q := B) (Y := X) (O := O)
      hBC.symm hCOB (hX.trans hCO.symm) s₂⁻¹ (by
        have e1 : X -ᵥ C = s₂⁻¹ • (B -ᵥ C) := by
          rw [hs₂', smul_smul, inv_mul_cancel₀ hs2ne, one_smul]
        exact e1)
    rcases hcase with h | h
    · exact hXC h
    · exact hXline (h.symm ▸ right_mem_affineSpan_pair ℝ A B)
  obtain ⟨hineq, hiff⟩ := area_key A B C X D O O₁ O₂ hAB hXC hXD hO1A hO1X hO2B hO2X
    hOCX t ht' ht0 ht1 r hr' hr0
  have hT : |cross (B -ᵥ A) (C -ᵥ A)| ≤ 4 * |cross (O₁ -ᵥ O) (O₂ -ᵥ O)| := by
    have h4 : |cross (B -ᵥ A) (C -ᵥ A)| ^ 2 ≤ (4 * |cross (O₁ -ᵥ O) (O₂ -ᵥ O)|) ^ 2 := by
      rw [sq_abs, mul_pow, sq_abs]
      linarith [hineq]
    exact le_of_sq_le_sq h4 (by positivity)
  refine ⟨?_, ?_⟩
  · rw [area, area]
    linarith [hT]
  · rw [area, area, minimizers, Set.mem_setOf_eq]
    constructor
    · intro h
      have h1 : 4 * |cross (O₁ -ᵥ O) (O₂ -ᵥ O)| = |cross (B -ᵥ A) (C -ᵥ A)| := by
        linarith [h]
      have h2 : (4 * |cross (O₁ -ᵥ O) (O₂ -ᵥ O)|) ^ 2 = |cross (B -ᵥ A) (C -ᵥ A)| ^ 2 := by
        rw [h1]
      rw [mul_pow, sq_abs, sq_abs] at h2
      exact hiff.mp (by linarith [h2])
    · intro h
      have h2 := hiff.mpr h
      have h3 : (4 * |cross (O₁ -ᵥ O) (O₂ -ᵥ O)|) ^ 2 = |cross (B -ᵥ A) (C -ᵥ A)| ^ 2 := by
        rw [mul_pow, sq_abs, sq_abs]
        linarith [h2]
      have h4 : 4 * |cross (O₁ -ᵥ O) (O₂ -ᵥ O)| = |cross (B -ᵥ A) (C -ᵥ A)| :=
        (sq_eq_sq₀ (by positivity) (abs_nonneg _)).mp h3
      linarith [h4]

set_option linter.unusedVariables false in
/-- The minimizing point exists: there is a point `X` on the minor arc `AB`
(i.e. on the circle, strictly on the opposite side of line `AB` from `C`)
with `CX ⊥ AB`. -/
problem usa2020_p1_minimizer_exists (A B C O : E)
    (htri : AffineIndependent ℝ ![A, B, C])
    (hacuteA : ∠ B A C < Real.pi / 2) (hacuteB : ∠ A B C < Real.pi / 2)
    (hacuteC : ∠ B C A < Real.pi / 2)
    (hOA : dist O A = dist O B) (hOB : dist O B = dist O C) :
    ∃ X, dist X O = dist A O ∧ (line[ℝ, A, B]).SOppSide C X ∧ X ∈ minimizers A B C := by
  have hAB : A ≠ B := by simpa using htri.injective.ne (show (0 : Fin 3) ≠ 1 by decide)
  have hAC : A ≠ C := by simpa using htri.injective.ne (show (0 : Fin 3) ≠ 2 by decide)
  have hBC : B ≠ C := by simpa using htri.injective.ne (show (1 : Fin 3) ≠ 2 by decide)
  set w := rot90 (B -ᵥ A) with hw_def
  have hb_pos : 0 < ⟪B -ᵥ A, B -ᵥ A⟫ := real_inner_self_pos.mpr (vsub_ne_zero.mpr hAB.symm)
  have hww : ⟪w, w⟫ = ⟪B -ᵥ A, B -ᵥ A⟫ := by
    rw [hw_def]; exact inner_rot90_rot90 _ _
  have hww_pos : 0 < ⟪w, w⟫ := by linarith [hww, hb_pos]
  have hww_ne : ⟪w, w⟫ ≠ 0 := ne_of_gt hww_pos
  have hbw : ⟪B -ᵥ A, w⟫ = 0 := by rw [hw_def]; exact inner_rot90_self _
  have hscal3 : ∀ v : E, ⟪v, w⟫ = cross (B -ᵥ A) v := by
    intro v
    rw [hw_def, inner_rot90_right, cross_comm, neg_neg]
  have hcross_bw : cross (B -ᵥ A) w = ⟪B -ᵥ A, B -ᵥ A⟫ := by
    rw [hw_def, ← inner_rot90_left, inner_rot90_rot90]
  have hT_ne : cross (B -ᵥ A) (C -ᵥ A) ≠ 0 := by
    intro hT0
    have hCmem : C ∈ line[ℝ, A, B] := mem_line_of_cross_eq_zero hAB hT0
    have hcoll : Collinear ℝ ({A, B, C} : Set E) := by
      rw [show ({A, B, C} : Set E) = insert C {A, B} by
        ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]
      exact (collinear_insert_iff_of_mem_affineSpan hCmem).mpr (collinear_pair ℝ A B)
    exact (affineIndependent_iff_not_collinear_set.mp htri) hcoll
  have hCline : C ∉ line[ℝ, A, B] := by
    intro hCl
    obtain ⟨t', ht'⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hCl
    rw [AffineMap.lineMap_apply] at ht'
    have ht2 : C -ᵥ A = t' • (B -ᵥ A) := by rw [← ht', vadd_vsub]
    have hz : ⟪C -ᵥ A, w⟫ = 0 := by
      rw [ht2, real_inner_smul_left, hbw, mul_zero]
    rw [hscal3] at hz
    exact hT_ne hz
  have hα : 0 < ⟪B -ᵥ A, C -ᵥ A⟫ :=
    inner_pos_of_angle_lt_pi_div_two B A C hAB.symm hAC.symm hacuteA
  have hαB : 0 < ⟪A -ᵥ B, C -ᵥ B⟫ :=
    inner_pos_of_angle_lt_pi_div_two A B C hAB hBC.symm hacuteB
  have hαB' : ⟪A -ᵥ B, C -ᵥ B⟫ = ⟪B -ᵥ A, B -ᵥ A⟫ - ⟪B -ᵥ A, C -ᵥ A⟫ := by
    have e1 : A -ᵥ B = -(B -ᵥ A) := (neg_vsub_eq_vsub_rev B A).symm
    have e2 : C -ᵥ B = (C -ᵥ A) - (B -ᵥ A) := by rw [vsub_sub_vsub_cancel_right]
    rw [e1, e2, inner_neg_left, inner_sub_right]
    ring
  have hαβ : 0 < ⟪B -ᵥ A, B -ᵥ A⟫ - ⟪B -ᵥ A, C -ᵥ A⟫ := by linarith [hαB]
  have hOA_half : ⟪O -ᵥ A, B -ᵥ A⟫ = ⟪B -ᵥ A, B -ᵥ A⟫ / 2 := inner_vsub_eq_half hOA
  have hOC : dist O A = dist O C := hOA.trans hOB
  have hOC_half : ⟪O -ᵥ A, C -ᵥ A⟫ = ⟪C -ᵥ A, C -ᵥ A⟫ / 2 := inner_vsub_eq_half hOC
  have hTcross : cross (B -ᵥ A) (C -ᵥ A) * cross (B -ᵥ A) (O -ᵥ A) =
      ⟪B -ᵥ A, B -ᵥ A⟫ * ⟪C -ᵥ A, C -ᵥ A⟫ / 2 - ⟪B -ᵥ A, C -ᵥ A⟫ * ⟪B -ᵥ A, B -ᵥ A⟫ / 2 := by
    have hbd := basis_decomp (C -ᵥ A) (B -ᵥ A)
    rw [← hw_def] at hbd
    have e1 := congrArg (fun y ↦ ⟪O -ᵥ A, y⟫) hbd
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, real_inner_smul_right,
      hOA_half, hOC_half, hscal3, real_inner_comm (B -ᵥ A) (C -ᵥ A)] at e1
    linear_combination -e1
  have hscal1 : ⟪A -ᵥ C, w⟫ = -cross (B -ᵥ A) (C -ᵥ A) := by
    rw [hscal3, show A -ᵥ C = -(C -ᵥ A) from (neg_vsub_eq_vsub_rev C A).symm,
      cross_neg_right]
  have hsign : ⟪A -ᵥ C, w⟫ * (⟪A -ᵥ C, w⟫ + 2 * ⟪C -ᵥ O, w⟫) < 0 := by
    have hscal2 : ⟪C -ᵥ O, w⟫ = cross (B -ᵥ A) (C -ᵥ O) := hscal3 _
    have hCcross : cross (B -ᵥ A) (C -ᵥ O) = cross (B -ᵥ A) (C -ᵥ A) - cross (B -ᵥ A) (O -ᵥ A) := by
      rw [show C -ᵥ O = (C -ᵥ A) - (O -ᵥ A) from by rw [vsub_sub_vsub_cancel_right],
        cross_sub_right]
    have hLag : cross (B -ᵥ A) (C -ᵥ A) ^ 2 =
        ⟪C -ᵥ A, C -ᵥ A⟫ * ⟪B -ᵥ A, B -ᵥ A⟫ - ⟪B -ᵥ A, C -ᵥ A⟫ ^ 2 := by
      have hL := lagrange (C -ᵥ A) (B -ᵥ A)
      rw [cross_comm (C -ᵥ A) (B -ᵥ A), neg_sq, real_inner_comm (B -ᵥ A) (C -ᵥ A)] at hL
      linear_combination hL
    have key : ⟪A -ᵥ C, w⟫ * (⟪A -ᵥ C, w⟫ + 2 * ⟪C -ᵥ O, w⟫) =
        -(⟪B -ᵥ A, C -ᵥ A⟫ * (⟪B -ᵥ A, B -ᵥ A⟫ - ⟪B -ᵥ A, C -ᵥ A⟫)) := by
      rw [hscal1, hscal2, hCcross]
      linear_combination 2 * hTcross - hLag
    rw [key, neg_lt_zero]
    exact mul_pos hα hαβ
  set σ := -2 * ⟪C -ᵥ O, w⟫ / ⟪w, w⟫ with hσ_def
  set X := C +ᵥ σ • w with hX_def
  have hσ : σ * ⟪w, w⟫ = -2 * ⟪C -ᵥ O, w⟫ := by
    rw [hσ_def]; exact div_mul_cancel₀ _ hww_ne
  have hdist : dist X O = dist A O := by
    have e1 : ‖X -ᵥ O‖ ^ 2 = ‖A -ᵥ O‖ ^ 2 := by
      have e2 : X -ᵥ O = (C -ᵥ O) + σ • w := by
        rw [hX_def]; simp only [vadd_eq_add, vsub_eq_sub]; module
      have e3 : ⟪C -ᵥ O, C -ᵥ O⟫ = ⟪A -ᵥ O, A -ᵥ O⟫ := by
        have h : dist C O = dist A O := by rw [dist_comm C O, dist_comm A O, hOA, hOB]
        rw [dist_eq_norm_vsub, dist_eq_norm_vsub] at h
        have h2 := congrArg (· ^ 2) h
        rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq] at h2
        exact h2
      rw [e2, norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
        mul_pow, sq_abs, ← real_inner_self_eq_norm_sq (C -ᵥ O),
        ← real_inner_self_eq_norm_sq w, ← real_inner_self_eq_norm_sq (A -ᵥ O)]
      linear_combination e3 + σ * hσ
    rw [dist_eq_norm_vsub, dist_eq_norm_vsub]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp e1
  have hXw : cross (B -ᵥ A) (X -ᵥ A) ≠ 0 := by
    have e1 : X -ᵥ A = (C -ᵥ A) + σ • w := by
      rw [hX_def]; simp only [vadd_eq_add, vsub_eq_sub]; module
    have e2 : cross (B -ᵥ A) (X -ᵥ A) = cross (B -ᵥ A) (C -ᵥ A) + σ * ⟪B -ᵥ A, B -ᵥ A⟫ := by
      rw [e1, cross_add_right, cross_smul_right, hcross_bw]
    have e3 : cross (B -ᵥ A) (X -ᵥ A) = -(⟪A -ᵥ C, w⟫ + 2 * ⟪C -ᵥ O, w⟫) := by
      rw [e2]
      linear_combination hσ - σ * hww + hscal1
    have hne : ⟪A -ᵥ C, w⟫ + 2 * ⟪C -ᵥ O, w⟫ ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hsign
      exact (lt_irrefl 0) hsign
    rw [e3, ne_eq, neg_eq_zero]
    exact hne
  have hXline : X ∉ line[ℝ, A, B] := by
    intro hXl
    obtain ⟨t', ht'⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hXl
    rw [AffineMap.lineMap_apply] at ht'
    have ht2 : X -ᵥ A = t' • (B -ᵥ A) := by rw [← ht', vadd_vsub]
    have hz : cross (B -ᵥ A) (X -ᵥ A) = 0 := by
      rw [ht2, cross_smul_right, cross_self, mul_zero]
    exact hXw hz
  have hmin : X ∈ minimizers A B C := by
    rw [minimizers, Set.mem_setOf_eq]
    have e1 : X -ᵥ C = σ • w := by
      rw [hX_def]; simp only [vadd_eq_add, vsub_eq_sub]; module
    rw [e1, real_inner_smul_left, real_inner_comm (B -ᵥ A) w, hbw, mul_zero]
  set υ := ⟪A -ᵥ C, w⟫ / ⟪w, w⟫ with hυ_def
  set F := C +ᵥ υ • w with hF_def
  have hυ : υ * ⟪w, w⟫ = ⟪A -ᵥ C, w⟫ := by
    rw [hυ_def]; exact div_mul_cancel₀ _ hww_ne
  have hFcross : cross (B -ᵥ A) (F -ᵥ A) = 0 := by
    have e1 : F -ᵥ A = (C -ᵥ A) + υ • w := by
      rw [hF_def]; simp only [vadd_eq_add, vsub_eq_sub]; module
    rw [e1, cross_add_right, cross_smul_right, hcross_bw]
    linear_combination hυ - υ * hww + hscal1
  have hFline : F ∈ line[ℝ, A, B] := mem_line_of_cross_eq_zero hAB hFcross
  have hυσ : 0 < υ * (σ - υ) := by
    have h2 : υ * (σ - υ) = -(⟪A -ᵥ C, w⟫ * (⟪A -ᵥ C, w⟫ + 2 * ⟪C -ᵥ O, w⟫)) / (⟪w, w⟫ * ⟪w, w⟫) := by
      rw [hσ_def, hυ_def]
      field_simp
      ring
    rw [h2]
    exact div_pos (by linarith [hsign]) (mul_pos hww_pos hww_pos)
  have hυ_ne : υ ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hυσ
    exact (lt_irrefl 0) hυσ
  have hσυ_ne : σ - υ ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hυσ
    exact (lt_irrefl 0) hυσ
  have hray : SameRay ℝ (C -ᵥ F) (F -ᵥ X) := by
    have hv1 : C -ᵥ F = (-υ) • w := by
      rw [hF_def]; simp only [vadd_eq_add, vsub_eq_sub]; module
    have hv2 : F -ᵥ X = (υ - σ) • w := by
      rw [hF_def, hX_def]; simp only [vadd_eq_add, vsub_eq_sub]; module
    rw [hv1, hv2]
    refine Or.inr (Or.inr ⟨|σ - υ|, |υ|, abs_pos.mpr hσυ_ne, abs_pos.mpr hυ_ne, ?_⟩)
    rw [smul_smul, smul_smul]
    congr 1
    have hkey : |σ - υ| * (-υ) = |υ| * (υ - σ) := by
      rcases lt_or_gt_of_ne hυ_ne with hυl | hυg
      · have h2 : σ - υ < 0 := by nlinarith [hυσ, hυl]
        rw [abs_of_neg h2, abs_of_neg hυl]
        ring
      · have h2 : 0 < σ - υ := by nlinarith [hυσ, hυg]
        rw [abs_of_pos h2, abs_of_pos hυg]
        ring
    exact hkey
  exact ⟨X, hdist, ⟨⟨F, hFline, F, hFline, hray⟩, hCline, hXline⟩, hmin⟩

end Usa2020P1
