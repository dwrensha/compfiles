/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.Geometry.Euclidean.Sphere.Basic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# USA Mathematical Olympiad 2008, Problem 2

Let `ABC` be an acute, scalene triangle, and let `M`, `N`, and `P` be the midpoints of
`BC`, `CA`, and `AB`, respectively. Let the perpendicular bisectors of `AB` and `AC`
intersect ray `AM` in points `D` and `E` respectively, and let lines `BD` and `CE`
intersect in point `F`, inside triangle `ABC`. Prove that points `A`, `N`, `F`, and `P`
all lie on one circle.
-/

namespace Usa2008P2

open EuclideanGeometry RealInnerProductSpace Affine FiniteDimensional

snip begin

/-- Inner product of two vectors in the plane in coordinates. -/
lemma inner_coord (u v : EuclideanSpace ℝ (Fin 2)) :
    ⟪u, v⟫ = u 0 * v 0 + u 1 * v 1 := by
  rw [PiLp.inner_apply, Fin.sum_univ_two]
  simp [RCLike.inner_apply]
  ring

/-- Squared distance of two points in the plane in coordinates. -/
lemma dist_sq_coord (x y : EuclideanSpace ℝ (Fin 2)) :
    dist x y ^ 2 = (x 0 - y 0)^2 + (x 1 - y 1)^2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _),
    Fin.sum_univ_two, Real.dist_eq, Real.dist_eq, sq_abs, sq_abs]

/-- Coordinates of a subtraction of points. -/
lemma coord_sub (u v : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) : (u -ᵥ v) i = u i - v i := by
  simp [vsub_eq_sub]

/-- Coordinates of a scalar multiple of a vector. -/
lemma coord_smul (s : ℝ) (v : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) : (s • v) i = s * v i := by
  simp

/-- Coordinates of a sum of vectors. -/
lemma coord_add (u v : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) : (u + v) i = u i + v i := by
  simp

/-- An angle smaller than `π / 2` has positive inner product. -/
lemma angle_lt_pi_div_two_inner_pos (p q r : EuclideanSpace ℝ (Fin 2))
    (hq1 : p ≠ q) (hq2 : r ≠ q) (h : ∠ p q r < Real.pi / 2) :
    0 < ⟪p -ᵥ q, r -ᵥ q⟫ := by
  have hcos : Real.cos (∠ p q r) = ⟪p -ᵥ q, r -ᵥ q⟫ / (‖p -ᵥ q‖ * ‖r -ᵥ q‖) := by
    rw [EuclideanGeometry.angle]; exact InnerProductGeometry.cos_angle _ _
  have hpos : 0 < Real.cos (∠ p q r) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, EuclideanGeometry.angle_nonneg p q r], h⟩
  rw [hcos] at hpos
  have hden : 0 < ‖p -ᵥ q‖ * ‖r -ᵥ q‖ := by
    apply mul_pos <;> rw [norm_pos_iff] <;>
      [exact sub_ne_zero.mpr hq1; exact sub_ne_zero.mpr hq2]
  nlinarith [mul_pos hpos hden, div_mul_cancel₀ (⟪p -ᵥ q, r -ᵥ q⟫) (ne_of_gt hden)]

/-- Core algebraic identity for USAMO 2008 P2. Here `b`, `c` are the coordinates of
`B - A`, `C - A`; `d`, `e`, `f` those of `D - A`, `E - A`, `F - A`; `t1`, `t2` the ray
parameters of `D` and `E` on `AM`. The conclusion is `2 det(b,c) |f|^2 = f · K`, i.e.
`|f|^2 = f · o` where `o` is the circumcenter of `ABC` (with `A` as origin): this says
`F` lies on the circle with diameter `AO`. -/
lemma core (b1 b2 c1 c2 d1 d2 e1 e2 f1 f2 t1 t2 : ℝ)
    (hd1 : d1 * 2 = t1 * (b1 + c1)) (hd2 : d2 * 2 = t1 * (b2 + c2))
    (he1 : e1 * 2 = t2 * (b1 + c1)) (he2 : e2 * 2 = t2 * (b2 + c2))
    (hdb : 2 * (d1 * b1 + d2 * b2) = b1^2 + b2^2)
    (hec : 2 * (e1 * c1 + e2 * c2) = c1^2 + c2^2)
    (hL1 : (f1 - b1) * (d2 - b2) = (f2 - b2) * (d1 - b1))
    (hL2 : (f1 - c1) * (e2 - c2) = (f2 - c2) * (e1 - c1))
    (hbcpos : 0 < b1 * c1 + b2 * c2)
    (_hbbpos : 0 < b1^2 + b2^2)
    (_hccpos : 0 < c1^2 + c2^2)
    (hdet : b1 * c2 - b2 * c1 ≠ 0)
    (hm : (b1 + c1)^2 + (b2 + c2)^2 ≠ 0) :
    2 * (b1 * c2 - b2 * c1) * (f1^2 + f2^2) =
      f1 * ((b1^2 + b2^2) * c2 - (c1^2 + c2^2) * b2) +
      f2 * ((c1^2 + c2^2) * b1 - (b1^2 + b2^2) * c1) := by
  -- The ray relations `t1 * (b · (b + c)) = |b|^2`, `t2 * (c · (b + c)) = |c|^2`.
  have ht1 : t1 * ((b1 + c1) * b1 + (b2 + c2) * b2) = b1^2 + b2^2 := by
    linear_combination hdb - hd1 * b1 - hd2 * b2
  have ht2 : t2 * ((b1 + c1) * c1 + (b2 + c2) * c2) = c1^2 + c2^2 := by
    linear_combination hec - he1 * c1 - he2 * c2
  -- The two line constraints on `F`, with `d` and `e` eliminated via the ray
  -- equations (and denominators cleared).
  have g1 : (t1 * (b2 + c2) - 2 * b2) * f1 - (t1 * (b1 + c1) - 2 * b1) * f2 =
      t1 * (b1 * c2 - b2 * c1) := by
    linear_combination 2 * hL1 - (f1 - b1) * hd2 + (f2 - b2) * hd1
  have g2 : (t2 * (b2 + c2) - 2 * c2) * f1 - (t2 * (b1 + c1) - 2 * c1) * f2 =
      -t2 * (b1 * c2 - b2 * c1) := by
    linear_combination 2 * hL2 - (f1 - c1) * he2 + (f2 - c2) * he1
  -- Cramer's rule: the determinant `DETF` times each coordinate of `f`.
  have hf1 : ((t1 * (b1 + c1) - 2 * b1) * (t2 * (b2 + c2) - 2 * c2) -
        (t1 * (b2 + c2) - 2 * b2) * (t2 * (b1 + c1) - 2 * c1)) * f1 =
      -(b1 * c2 - b2 * c1) * (t1 * (t2 * (b1 + c1) - 2 * c1) + t2 * (t1 * (b1 + c1) - 2 * b1)) := by
    linear_combination (-(t2 * (b1 + c1) - 2 * c1)) * g1 + (t1 * (b1 + c1) - 2 * b1) * g2
  have hf2 : ((t1 * (b1 + c1) - 2 * b1) * (t2 * (b2 + c2) - 2 * c2) -
        (t1 * (b2 + c2) - 2 * b2) * (t2 * (b1 + c1) - 2 * c1)) * f2 =
      -(b1 * c2 - b2 * c1) * (t2 * (t1 * (b2 + c2) - 2 * b2) + t1 * (t2 * (b2 + c2) - 2 * c2)) := by
    linear_combination (-(t2 * (b2 + c2) - 2 * c2)) * g1 + (t1 * (b2 + c2) - 2 * b2) * g2
  -- The determinant is `2 * det(b,c) * (2 - t1 - t2)`.
  have hDETF : (t1 * (b1 + c1) - 2 * b1) * (t2 * (b2 + c2) - 2 * c2) -
      (t1 * (b2 + c2) - 2 * b2) * (t2 * (b1 + c1) - 2 * c1) =
      2 * (b1 * c2 - b2 * c1) * (2 - t1 - t2) := by
    ring
  -- The ray relations give `DEN1 * DEN2 * (2 - t1 - t2) = (b · c) * |b + c|^2`.
  have hDEN : (b1^2 + b2^2 + (b1 * c1 + b2 * c2)) * (c1^2 + c2^2 + (b1 * c1 + b2 * c2)) *
        (2 - t1 - t2) = (b1 * c1 + b2 * c2) * ((b1 + c1)^2 + (b2 + c2)^2) := by
    linear_combination (-(c1^2 + c2^2 + (b1 * c1 + b2 * c2))) * ht1 +
      (-(b1^2 + b2^2 + (b1 * c1 + b2 * c2))) * ht2
  -- Hence the determinant is nonzero.
  have htt : (2 - t1 - t2) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hDEN
    exact (mul_ne_zero (ne_of_gt hbcpos) hm) hDEN.symm
  have hDETFne : (t1 * (b1 + c1) - 2 * b1) * (t2 * (b2 + c2) - 2 * c2) -
        (t1 * (b2 + c2) - 2 * b2) * (t2 * (b1 + c1) - 2 * c1) ≠ 0 := by
    rw [hDETF]
    exact mul_ne_zero (mul_ne_zero two_ne_zero hdet) htt
  -- The key polynomial identity `det * (W1^2 + W2^2) + (2 - t1 - t2) * (W · K) = 0`,
  -- certified modulo the two ray relations.
  have hBIG : (b1 * c2 - b2 * c1) * ((t1 * (t2 * (b1 + c1) - 2 * c1) +
        t2 * (t1 * (b1 + c1) - 2 * b1))^2 + (t2 * (t1 * (b2 + c2) - 2 * b2) +
        t1 * (t2 * (b2 + c2) - 2 * c2))^2) +
      (2 - t1 - t2) * ((t1 * (t2 * (b1 + c1) - 2 * c1) + t2 * (t1 * (b1 + c1) - 2 * b1)) *
        ((b1^2 + b2^2) * c2 - (c1^2 + c2^2) * b2) + (t2 * (t1 * (b2 + c2) - 2 * b2) +
        t1 * (t2 * (b2 + c2) - 2 * c2)) * ((c1^2 + c2^2) * b1 - (b1^2 + b2^2) * c1)) = 0 := by
    linear_combination (2 * t2 * (b1 * c2 - b2 * c1) * (2 * t1 * t2 - t1 - 3 * t2 + 2)) * ht1 +
      (2 * t1 * (b1 * c2 - b2 * c1) * (2 * t1 * t2 - 3 * t1 - t2 + 2)) * ht2
  -- Multiply the goal by `DETF^2`, rewrite `DETF * fi` as `-det * Wi`, and conclude.
  have key : ((t1 * (b1 + c1) - 2 * b1) * (t2 * (b2 + c2) - 2 * c2) -
        (t1 * (b2 + c2) - 2 * b2) * (t2 * (b1 + c1) - 2 * c1))^2 *
      (2 * (b1 * c2 - b2 * c1) * (f1^2 + f2^2) -
        (f1 * ((b1^2 + b2^2) * c2 - (c1^2 + c2^2) * b2) +
          f2 * ((c1^2 + c2^2) * b1 - (b1^2 + b2^2) * c1))) = 0 := by
    linear_combination (2 * (b1 * c2 - b2 * c1) * (((t1 * (b1 + c1) - 2 * b1) *
          (t2 * (b2 + c2) - 2 * c2) - (t1 * (b2 + c2) - 2 * b2) * (t2 * (b1 + c1) - 2 * c1)) * f1 -
        (b1 * c2 - b2 * c1) * (t1 * (t2 * (b1 + c1) - 2 * c1) + t2 * (t1 * (b1 + c1) - 2 * b1))) -
        ((t1 * (b1 + c1) - 2 * b1) * (t2 * (b2 + c2) - 2 * c2) -
          (t1 * (b2 + c2) - 2 * b2) * (t2 * (b1 + c1) - 2 * c1)) *
          ((b1^2 + b2^2) * c2 - (c1^2 + c2^2) * b2)) * hf1 +
      (2 * (b1 * c2 - b2 * c1) * (((t1 * (b1 + c1) - 2 * b1) * (t2 * (b2 + c2) - 2 * c2) -
          (t1 * (b2 + c2) - 2 * b2) * (t2 * (b1 + c1) - 2 * c1)) * f2 -
        (b1 * c2 - b2 * c1) * (t2 * (t1 * (b2 + c2) - 2 * b2) + t1 * (t2 * (b2 + c2) - 2 * c2))) -
        ((t1 * (b1 + c1) - 2 * b1) * (t2 * (b2 + c2) - 2 * c2) -
          (t1 * (b2 + c2) - 2 * b2) * (t2 * (b1 + c1) - 2 * c1)) *
          ((c1^2 + c2^2) * b1 - (b1^2 + b2^2) * c1)) * hf2 +
      (2 * (b1 * c2 - b2 * c1)^2) * hBIG
  have hG : 2 * (b1 * c2 - b2 * c1) * (f1^2 + f2^2) -
      (f1 * ((b1^2 + b2^2) * c2 - (c1^2 + c2^2) * b2) +
        f2 * ((c1^2 + c2^2) * b1 - (b1^2 + b2^2) * c1)) = 0 := by
    rcases mul_eq_zero.mp key with h | h
    · exact absurd h (pow_ne_zero 2 hDETFne)
    · exact h
  linear_combination hG




snip end

problem usa2008_p2
    (A B C M N P D E F : EuclideanSpace ℝ (Fin 2))
    (htri : AffineIndependent ℝ ![A, B, C])
    (hacuteA : ∠ B A C < Real.pi / 2)
    (hacuteB : ∠ A B C < Real.pi / 2)
    (hacuteC : ∠ B C A < Real.pi / 2)
    (hscalAB : dist A B ≠ dist B C)
    (hscalBC : dist B C ≠ dist C A)
    (hscalCA : dist C A ≠ dist A B)
    (hM : M = midpoint ℝ B C)
    (hN : N = midpoint ℝ C A)
    (hP : P = midpoint ℝ A B)
    (hDray : ∃ t : ℝ, 0 ≤ t ∧ D = t • (M -ᵥ A) +ᵥ A)
    (hDbis : dist D A = dist D B)
    (hEray : ∃ t : ℝ, 0 ≤ t ∧ E = t • (M -ᵥ A) +ᵥ A)
    (hEbis : dist E A = dist E C)
    (hFBD : F ∈ affineSpan ℝ ({B, D} : Set (EuclideanSpace ℝ (Fin 2))))
    (hFCE : F ∈ affineSpan ℝ ({C, E} : Set (EuclideanSpace ℝ (Fin 2))))
    (hFinside : F ∈ interior (convexHull ℝ {A, B, C})) :
    Concyclic ({A, N, F, P} : Set (EuclideanSpace ℝ (Fin 2))) := by
  -- Nondegeneracy of the triangle.
  have hAB : A ≠ B := by simpa using htri.injective.ne (show (0 : Fin 3) ≠ 1 by decide)
  have hAC : A ≠ C := by simpa using htri.injective.ne (show (0 : Fin 3) ≠ 2 by decide)
  -- Acuteness at `A` gives `0 < (B - A) · (C - A)`.
  have posA : 0 < ⟪B -ᵥ A, C -ᵥ A⟫ :=
    angle_lt_pi_div_two_inner_pos B A C hAB.symm hAC.symm hacuteA
  have hbcpos : 0 < (B 0 - A 0) * (C 0 - A 0) + (B 1 - A 1) * (C 1 - A 1) := by
    rw [inner_coord, coord_sub B A 0, coord_sub C A 0, coord_sub B A 1, coord_sub C A 1] at posA
    exact posA
  have hbbpos : 0 < (B 0 - A 0)^2 + (B 1 - A 1)^2 := by
    rw [← dist_sq_coord]
    exact sq_pos_of_pos (dist_pos.mpr hAB.symm)
  have hccpos : 0 < (C 0 - A 0)^2 + (C 1 - A 1)^2 := by
    rw [← dist_sq_coord]
    exact sq_pos_of_pos (dist_pos.mpr hAC.symm)
  -- `A`, `B`, `C` not collinear, as a nonzero determinant.
  have hdet : (B 0 - A 0) * (C 1 - A 1) - (B 1 - A 1) * (C 0 - A 0) ≠ 0 := by
    intro hd
    have hncoll : ¬ Collinear ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2))) :=
      affineIndependent_iff_not_collinear_set.1 htri
    apply hncoll
    have hx : (B 0 - A 0) ≠ 0 ∨ (B 1 - A 1) ≠ 0 := by
      by_contra h
      push Not at h
      have hz : dist B A ^ 2 = 0 := by rw [dist_sq_coord, h.1, h.2]; ring
      rw [pow_eq_zero_iff two_ne_zero, dist_eq_zero] at hz
      exact hAB hz.symm
    rcases hx with hx0 | hx1
    · refine collinear_triple_of_mem_affineSpan_pair (left_mem_affineSpan_pair ℝ A B)
        (right_mem_affineSpan_pair ℝ A B) ?_
      refine (mem_affineSpan_pair_iff_exists_lineMap_eq).2 ⟨(C 0 - A 0) / (B 0 - A 0), ?_⟩
      rw [AffineMap.lineMap_apply]
      have hCv : C -ᵥ A = ((C 0 - A 0) / (B 0 - A 0)) • (B -ᵥ A) := by
        apply PiLp.ext_iff.mpr
        exact Fin.forall_fin_two.2 ⟨by
          rw [coord_smul, coord_sub B A 0, coord_sub C A 0, div_mul_eq_mul_div, eq_div_iff hx0], by
          rw [coord_smul, coord_sub B A 1, coord_sub C A 1, div_mul_eq_mul_div, eq_div_iff hx0]
          linear_combination hd⟩
      exact ((eq_vadd_iff_vsub_eq C (((C 0 - A 0) / (B 0 - A 0)) • (B -ᵥ A)) A).2 hCv).symm
    · refine collinear_triple_of_mem_affineSpan_pair (left_mem_affineSpan_pair ℝ A B)
        (right_mem_affineSpan_pair ℝ A B) ?_
      refine (mem_affineSpan_pair_iff_exists_lineMap_eq).2 ⟨(C 1 - A 1) / (B 1 - A 1), ?_⟩
      rw [AffineMap.lineMap_apply]
      have hCv : C -ᵥ A = ((C 1 - A 1) / (B 1 - A 1)) • (B -ᵥ A) := by
        apply PiLp.ext_iff.mpr
        exact Fin.forall_fin_two.2 ⟨by
          rw [coord_smul, coord_sub B A 0, coord_sub C A 0, div_mul_eq_mul_div, eq_div_iff hx1]
          linear_combination -hd, by
          rw [coord_smul, coord_sub B A 1, coord_sub C A 1, div_mul_eq_mul_div, eq_div_iff hx1]⟩
      exact ((eq_vadd_iff_vsub_eq C (((C 1 - A 1) / (B 1 - A 1)) • (B -ᵥ A)) A).2 hCv).symm
  -- `M ≠ A`, i.e. `(B - A) + (C - A) ≠ 0`.
  have hm : ((B 0 - A 0) + (C 0 - A 0))^2 + ((B 1 - A 1) + (C 1 - A 1))^2 ≠ 0 := by
    intro h
    obtain ⟨h0, h1⟩ := (add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _)).1 h
    rw [sq_eq_zero_iff] at h0 h1
    apply hdet
    have e0 : C 0 - A 0 = -(B 0 - A 0) := by linarith
    have e1 : C 1 - A 1 = -(B 1 - A 1) := by linarith
    rw [e0, e1]
    ring
  -- The ray parameters of `D` and `E`.
  obtain ⟨t1, -, hDt⟩ := hDray
  obtain ⟨t2, -, hEt⟩ := hEray
  have hDvec : D -ᵥ A = t1 • (M -ᵥ A) := (eq_vadd_iff_vsub_eq D (t1 • (M -ᵥ A)) A).1 hDt
  have hEvec : E -ᵥ A = t2 • (M -ᵥ A) := (eq_vadd_iff_vsub_eq E (t2 • (M -ᵥ A)) A).1 hEt
  have hMvec : M -ᵥ A = (2 : ℝ)⁻¹ • ((B -ᵥ A) + (C -ᵥ A)) := by
    rw [hM, midpoint_eq_smul_add, invOf_eq_inv]
    simp only [vsub_eq_sub]
    module
  have hd1 : (D 0 - A 0) * 2 = t1 * ((B 0 - A 0) + (C 0 - A 0)) := by
    have h0 : D 0 - A 0 = t1 * (2⁻¹ * ((B 0 - A 0) + (C 0 - A 0))) := by
      rw [← coord_sub D A 0, hDvec, hMvec, coord_smul, coord_smul, coord_add,
        coord_sub B A 0, coord_sub C A 0]
    linear_combination 2 * h0
  have hd2 : (D 1 - A 1) * 2 = t1 * ((B 1 - A 1) + (C 1 - A 1)) := by
    have h0 : D 1 - A 1 = t1 * (2⁻¹ * ((B 1 - A 1) + (C 1 - A 1))) := by
      rw [← coord_sub D A 1, hDvec, hMvec, coord_smul, coord_smul, coord_add,
        coord_sub B A 1, coord_sub C A 1]
    linear_combination 2 * h0
  have he1 : (E 0 - A 0) * 2 = t2 * ((B 0 - A 0) + (C 0 - A 0)) := by
    have h0 : E 0 - A 0 = t2 * (2⁻¹ * ((B 0 - A 0) + (C 0 - A 0))) := by
      rw [← coord_sub E A 0, hEvec, hMvec, coord_smul, coord_smul, coord_add,
        coord_sub B A 0, coord_sub C A 0]
    linear_combination 2 * h0
  have he2 : (E 1 - A 1) * 2 = t2 * ((B 1 - A 1) + (C 1 - A 1)) := by
    have h0 : E 1 - A 1 = t2 * (2⁻¹ * ((B 1 - A 1) + (C 1 - A 1))) := by
      rw [← coord_sub E A 1, hEvec, hMvec, coord_smul, coord_smul, coord_add,
        coord_sub B A 1, coord_sub C A 1]
    linear_combination 2 * h0
  -- `D` on the perpendicular bisector of `AB`.
  have hDbis2 : (D 0 - A 0)^2 + (D 1 - A 1)^2 = (D 0 - B 0)^2 + (D 1 - B 1)^2 := by
    rw [← dist_sq_coord, ← dist_sq_coord, hDbis]
  have hdb : 2 * ((D 0 - A 0) * (B 0 - A 0) + (D 1 - A 1) * (B 1 - A 1)) =
      (B 0 - A 0)^2 + (B 1 - A 1)^2 := by
    linear_combination hDbis2
  -- `E` on the perpendicular bisector of `AC`.
  have hEbis2 : (E 0 - A 0)^2 + (E 1 - A 1)^2 = (E 0 - C 0)^2 + (E 1 - C 1)^2 := by
    rw [← dist_sq_coord, ← dist_sq_coord, hEbis]
  have hec : 2 * ((E 0 - A 0) * (C 0 - A 0) + (E 1 - A 1) * (C 1 - A 1)) =
      (C 0 - A 0)^2 + (C 1 - A 1)^2 := by
    linear_combination hEbis2
  -- `F` on line `BD`: eliminate the line parameter.
  obtain ⟨s, hs⟩ := (mem_affineSpan_pair_iff_exists_lineMap_eq).1 hFBD
  rw [AffineMap.lineMap_apply] at hs
  have hFvec : F -ᵥ B = s • (D -ᵥ B) := (eq_vadd_iff_vsub_eq F (s • (D -ᵥ B)) B).1 hs.symm
  have hs0 : F 0 - B 0 = s * (D 0 - B 0) := by
    rw [← coord_sub F B 0, hFvec, coord_smul, coord_sub D B 0]
  have hs1 : F 1 - B 1 = s * (D 1 - B 1) := by
    rw [← coord_sub F B 1, hFvec, coord_smul, coord_sub D B 1]
  have hL1 : ((F 0 - A 0) - (B 0 - A 0)) * ((D 1 - A 1) - (B 1 - A 1)) =
      ((F 1 - A 1) - (B 1 - A 1)) * ((D 0 - A 0) - (B 0 - A 0)) := by
    linear_combination (D 1 - B 1) * hs0 - (D 0 - B 0) * hs1
  -- `F` on line `CE`: eliminate the line parameter.
  obtain ⟨r, hr⟩ := (mem_affineSpan_pair_iff_exists_lineMap_eq).1 hFCE
  rw [AffineMap.lineMap_apply] at hr
  have hFvec2 : F -ᵥ C = r • (E -ᵥ C) := (eq_vadd_iff_vsub_eq F (r • (E -ᵥ C)) C).1 hr.symm
  have hr0 : F 0 - C 0 = r * (E 0 - C 0) := by
    rw [← coord_sub F C 0, hFvec2, coord_smul, coord_sub E C 0]
  have hr1 : F 1 - C 1 = r * (E 1 - C 1) := by
    rw [← coord_sub F C 1, hFvec2, coord_smul, coord_sub E C 1]
  have hL2 : ((F 0 - A 0) - (C 0 - A 0)) * ((E 1 - A 1) - (C 1 - A 1)) =
      ((F 1 - A 1) - (C 1 - A 1)) * ((E 0 - A 0) - (C 0 - A 0)) := by
    linear_combination (E 1 - C 1) * hr0 - (E 0 - C 0) * hr1
  -- The core algebraic identity: `2 det(B-A, C-A) * |F-A|^2 = (F-A) · K`.
  have hcore := core (B 0 - A 0) (B 1 - A 1) (C 0 - A 0) (C 1 - A 1)
    (D 0 - A 0) (D 1 - A 1) (E 0 - A 0) (E 1 - A 1) (F 0 - A 0) (F 1 - A 1) t1 t2
    hd1 hd2 he1 he2 hdb hec hL1 hL2 hbcpos hbbpos hccpos hdet hm
  -- The circle with diameter `AO`, where `O` is the circumcenter of `ABC`.
  set ov : EuclideanSpace ℝ (Fin 2) := (WithLp.equiv 2 (Fin 2 → ℝ)).symm
    ![(((B 0 - A 0)^2 + (B 1 - A 1)^2) * (C 1 - A 1) - ((C 0 - A 0)^2 + (C 1 - A 1)^2) * (B 1 - A 1)) /
        (2 * ((B 0 - A 0) * (C 1 - A 1) - (B 1 - A 1) * (C 0 - A 0))),
      (((C 0 - A 0)^2 + (C 1 - A 1)^2) * (B 0 - A 0) - ((B 0 - A 0)^2 + (B 1 - A 1)^2) * (C 0 - A 0)) /
        (2 * ((B 0 - A 0) * (C 1 - A 1) - (B 1 - A 1) * (C 0 - A 0)))] with hov
  have hov0 : ov 0 =
      (((B 0 - A 0)^2 + (B 1 - A 1)^2) * (C 1 - A 1) - ((C 0 - A 0)^2 + (C 1 - A 1)^2) * (B 1 - A 1)) /
        (2 * ((B 0 - A 0) * (C 1 - A 1) - (B 1 - A 1) * (C 0 - A 0))) := by
    rw [hov]; simp
  have hov1 : ov 1 =
      (((C 0 - A 0)^2 + (C 1 - A 1)^2) * (B 0 - A 0) - ((B 0 - A 0)^2 + (B 1 - A 1)^2) * (C 0 - A 0)) /
        (2 * ((B 0 - A 0) * (C 1 - A 1) - (B 1 - A 1) * (C 0 - A 0))) := by
    rw [hov]; simp
  set center : EuclideanSpace ℝ (Fin 2) := (2 : ℝ)⁻¹ • ov +ᵥ A with hcenter
  -- `B - A` and `C - A` satisfy the circumcenter relations `b · o = |b|^2 / 2`.
  have hPb : (B 0 - A 0) * (((B 0 - A 0)^2 + (B 1 - A 1)^2) * (C 1 - A 1) -
      ((C 0 - A 0)^2 + (C 1 - A 1)^2) * (B 1 - A 1)) +
      (B 1 - A 1) * (((C 0 - A 0)^2 + (C 1 - A 1)^2) * (B 0 - A 0) -
        ((B 0 - A 0)^2 + (B 1 - A 1)^2) * (C 0 - A 0)) =
      ((B 0 - A 0)^2 + (B 1 - A 1)^2) *
        ((B 0 - A 0) * (C 1 - A 1) - (B 1 - A 1) * (C 0 - A 0)) := by
    ring
  have hPc : (C 0 - A 0) * (((B 0 - A 0)^2 + (B 1 - A 1)^2) * (C 1 - A 1) -
      ((C 0 - A 0)^2 + (C 1 - A 1)^2) * (B 1 - A 1)) +
      (C 1 - A 1) * (((C 0 - A 0)^2 + (C 1 - A 1)^2) * (B 0 - A 0) -
        ((B 0 - A 0)^2 + (B 1 - A 1)^2) * (C 0 - A 0)) =
      ((C 0 - A 0)^2 + (C 1 - A 1)^2) *
        ((B 0 - A 0) * (C 1 - A 1) - (B 1 - A 1) * (C 0 - A 0)) := by
    ring
  have hov_b : ⟪B -ᵥ A, ov⟫ = ⟪B -ᵥ A, B -ᵥ A⟫ / 2 := by
    rw [inner_coord, hov0, hov1, coord_sub B A 0, coord_sub B A 1,
      ← mul_div_assoc, ← mul_div_assoc, ← add_div, hPb,
      mul_div_mul_right _ _ hdet, inner_coord, coord_sub B A 0, coord_sub B A 1]
    ring
  have hov_c : ⟪C -ᵥ A, ov⟫ = ⟪C -ᵥ A, C -ᵥ A⟫ / 2 := by
    rw [inner_coord, hov0, hov1, coord_sub C A 0, coord_sub C A 1,
      ← mul_div_assoc, ← mul_div_assoc, ← add_div, hPc,
      mul_div_mul_right _ _ hdet, inner_coord, coord_sub C A 0, coord_sub C A 1]
    ring
  -- The circle relation: `X` is on the circle with diameter `AO` iff `|X-A|^2 = (X-A) · o`.
  have key : ∀ X : EuclideanSpace ℝ (Fin 2), ⟪X -ᵥ A, X -ᵥ A⟫ = ⟪X -ᵥ A, ov⟫ →
      dist X center ^ 2 = dist A center ^ 2 := by
    intro X hX
    rw [dist_eq_norm_vsub, dist_eq_norm_vsub, ← real_inner_self_eq_norm_sq,
      ← real_inner_self_eq_norm_sq, hcenter, vsub_vadd_eq_vsub_sub X A ((2 : ℝ)⁻¹ • ov),
      vsub_vadd_eq_vsub_sub A A ((2 : ℝ)⁻¹ • ov), vsub_self, zero_sub, inner_neg_neg]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_right, real_inner_smul_left]
    have hX2 : ⟪ov, X -ᵥ A⟫ = ⟪X -ᵥ A, ov⟫ := real_inner_comm (X -ᵥ A) ov
    linarith [hX, hX2]
  -- The four points satisfy the relation.
  have hAin : ⟪A -ᵥ A, A -ᵥ A⟫ = ⟪A -ᵥ A, ov⟫ := by
    rw [vsub_self, inner_zero_left, inner_zero_left]
  have hPvec : P -ᵥ A = (2 : ℝ)⁻¹ • (B -ᵥ A) := by
    rw [hP, midpoint_vsub_left, invOf_eq_inv]
  have hPin : ⟪P -ᵥ A, P -ᵥ A⟫ = ⟪P -ᵥ A, ov⟫ := by
    rw [hPvec]
    simp only [real_inner_smul_left, real_inner_smul_right]
    rw [hov_b]
    ring
  have hNvec : N -ᵥ A = (2 : ℝ)⁻¹ • (C -ᵥ A) := by
    rw [hN, midpoint_vsub_right, invOf_eq_inv]
  have hNin : ⟪N -ᵥ A, N -ᵥ A⟫ = ⟪N -ᵥ A, ov⟫ := by
    rw [hNvec]
    simp only [real_inner_smul_left, real_inner_smul_right]
    rw [hov_c]
    ring
  have hdet2 : 2 * ((B 0 - A 0) * (C 1 - A 1) - (B 1 - A 1) * (C 0 - A 0)) ≠ 0 :=
    mul_ne_zero two_ne_zero hdet
  have hcore' : (F 0 - A 0) * (((B 0 - A 0)^2 + (B 1 - A 1)^2) * (C 1 - A 1) -
      ((C 0 - A 0)^2 + (C 1 - A 1)^2) * (B 1 - A 1)) +
      (F 1 - A 1) * (((C 0 - A 0)^2 + (C 1 - A 1)^2) * (B 0 - A 0) -
        ((B 0 - A 0)^2 + (B 1 - A 1)^2) * (C 0 - A 0)) =
      2 * ((B 0 - A 0) * (C 1 - A 1) - (B 1 - A 1) * (C 0 - A 0)) *
        ((F 0 - A 0)^2 + (F 1 - A 1)^2) := hcore.symm
  have hFin : ⟪F -ᵥ A, F -ᵥ A⟫ = ⟪F -ᵥ A, ov⟫ := by
    rw [inner_coord, inner_coord, hov0, hov1, coord_sub F A 0, coord_sub F A 1,
      ← mul_div_assoc, ← mul_div_assoc, ← add_div, hcore',
      mul_div_cancel_left₀ _ hdet2]
    ring
  -- Conclusion: the four points are on the circle with diameter `AO`.
  refine ⟨⟨center, dist A center, ?_⟩, ?_⟩
  · intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with h | h | h | h
    · rw [h]
    · rw [h]; exact (sq_eq_sq₀ dist_nonneg dist_nonneg).1 (key N hNin)
    · rw [h]; exact (sq_eq_sq₀ dist_nonneg dist_nonneg).1 (key F hFin)
    · rw [h]; exact (sq_eq_sq₀ dist_nonneg dist_nonneg).1 (key P hPin)
  · haveI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) := ⟨by simp⟩
    exact coplanar_of_fact_finrank_eq_two _

end Usa2008P2
