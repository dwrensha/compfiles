/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# USA Mathematical Olympiad 1974, Problem 5

A point inside an equilateral triangle with side 1 is a distance a, b, c from
the vertices. The triangle ABC has BC = a, CA = b, AB = c. The sides subtend
equal angles at a point inside it. Show that sum of the distances of the point
from the vertices is 1.
-/

open scoped EuclideanGeometry RealInnerProductSpace

namespace Usa1974P5

snip begin

/-- Squared distance between two points of the Euclidean plane, in coordinates. -/
lemma dist_sq_fin2 (A B : EuclideanSpace ℝ (Fin 2)) :
    dist A B ^ 2 = (A 0 - B 0) ^ 2 + (A 1 - B 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq, Real.dist_eq,
    sq_abs, sq_abs, Real.sq_sqrt (by positivity)]

/-- Inner product of two vectors of the Euclidean plane, in coordinates. -/
lemma inner_fin2 (x y : EuclideanSpace ℝ (Fin 2)) :
    ⟪x, y⟫ = x 0 * y 0 + x 1 * y 1 := by
  rw [PiLp.inner_apply, Fin.sum_univ_two]
  simp only [RCLike.inner_apply, RCLike.conj_to_real]
  ring

/-- Squared norm of a vector of the Euclidean plane, in coordinates. -/
lemma norm_sq_fin2 (x : EuclideanSpace ℝ (Fin 2)) :
    ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.norm_eq_abs, Real.norm_eq_abs,
    sq_abs, sq_abs, Real.sq_sqrt (by positivity)]

/-- If a 2×2 determinant is nonzero, the corresponding homogeneous linear
system has only the trivial solution. -/
lemma smul_eq_zero_of_det_ne_zero {u0 u1 w0 w1 s t : ℝ}
    (hdet : u0 * w1 - u1 * w0 ≠ 0)
    (h0 : s * u0 + t * w0 = 0) (h1 : s * u1 + t * w1 = 0) :
    s = 0 ∧ t = 0 := by
  have hs : s * (u0 * w1 - u1 * w0) = 0 := by linear_combination w1 * h0 - w0 * h1
  have ht : t * (u0 * w1 - u1 * w0) = 0 := by linear_combination -u1 * h0 + u0 * h1
  exact ⟨by simpa [hdet] using hs, by simpa [hdet] using ht⟩

/-- A triangle whose vertices are affinely independent has nonzero
(coordinate) determinant. -/
lemma det_ne_zero_of_lind (A B C : EuclideanSpace ℝ (Fin 2))
    (hli : LinearIndependent ℝ ![B - A, C - A]) :
    (B 0 - A 0) * (C 1 - A 1) - (B 1 - A 1) * (C 0 - A 0) ≠ 0 := by
  have hne : (![B - A, C - A] : Fin 2 → EuclideanSpace ℝ (Fin 2)) 0 ≠ 0 :=
    LinearIndependent.ne_zero 0 hli
  rw [LinearIndependent.pair_iff] at hli
  intro hdet
  have hc1 : (C 0 - A 0) • (B - A) + (-(B 0 - A 0)) • (C - A) = 0 := by
    ext i
    fin_cases i <;>
      simp only [Fin.mk_zero, Fin.mk_one, PiLp.add_apply, PiLp.smul_apply,
        PiLp.sub_apply, PiLp.zero_apply, smul_eq_mul]
    · ring
    · linear_combination -hdet
  rcases hli _ _ hc1 with ⟨hs1, ht1⟩
  have hB0 : B 0 = A 0 := by linarith
  have hC0 : C 0 = A 0 := by linarith
  have hc2 : (C 1 - A 1) • (B - A) + (-(B 1 - A 1)) • (C - A) = 0 := by
    ext i
    fin_cases i <;>
      simp only [Fin.mk_zero, Fin.mk_one, PiLp.add_apply, PiLp.smul_apply,
        PiLp.sub_apply, PiLp.zero_apply, smul_eq_mul]
    · rw [hB0, hC0]; ring
    · ring
  rcases hli _ _ hc2 with ⟨hs2, ht2⟩
  have hB1 : B 1 = A 1 := by linarith
  apply hne
  simp only [Matrix.cons_val_zero]
  ext i
  fin_cases i <;>
    simp only [Fin.mk_zero, Fin.mk_one, PiLp.sub_apply, PiLp.zero_apply]
  · linarith
  · linarith

/-- The squared distance of a barycentric combination `β • u + γ • w` of two
unit vectors `u`, `w` whose difference is also a unit vector (this is the
local computation for an equilateral triangle of side `1`). -/
lemma equilateral_rel (u0 u1 w0 w1 β γ : ℝ)
    (h1 : u0 ^ 2 + u1 ^ 2 = 1) (h2 : w0 ^ 2 + w1 ^ 2 = 1)
    (h3 : (u0 - w0) ^ 2 + (u1 - w1) ^ 2 = 1) :
    (β * u0 + γ * w0) ^ 2 + (β * u1 + γ * w1) ^ 2 = β ^ 2 + β * γ + γ ^ 2 := by
  linear_combination (β ^ 2 + β * γ) * h1 + (γ ^ 2 + β * γ) * h2 - β * γ * h3

/-- The key polynomial identity. If `a2, b2, c2` are given by the "120° law of
cosines" pattern from three quantities `U, V, W`, then the symmetric
expression `1 - (a2+b2+c2) + (a2²+b2²+c2²) - (a2b2+b2c2+c2a2)` factors. -/
lemma key_id (a2 b2 c2 U V W : ℝ)
    (ha : a2 = V ^ 2 + V * W + W ^ 2) (hb : b2 = W ^ 2 + W * U + U ^ 2)
    (hc : c2 = U ^ 2 + U * V + V ^ 2) :
    1 - (a2 + b2 + c2) + (a2 ^ 2 + b2 ^ 2 + c2 ^ 2) - (a2 * b2 + b2 * c2 + c2 * a2) =
      (1 - (U + V + W) ^ 2) * (1 - (U + V + W) ^ 2 + 3 * (U * V + V * W + W * U)) := by
  subst ha hb hc; ring

snip end

problem usa1974_p5
    (A₀ B₀ C₀ P A B C D : EuclideanSpace ℝ (Fin 2))
    (hA₀B₀ : dist A₀ B₀ = 1) (hB₀C₀ : dist B₀ C₀ = 1) (hC₀A₀ : dist C₀ A₀ = 1)
    (α β γ : ℝ) (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hsum : α + β + γ = 1)
    (hP : P = α • A₀ + β • B₀ + γ • C₀)
    (a b c : ℝ)
    (ha : dist P A₀ = a) (hb : dist P B₀ = b) (hc : dist P C₀ = c)
    (hBC : dist B C = a) (hCA : dist C A = b) (hAB : dist A B = c)
    (hli : LinearIndependent ℝ ![B - A, C - A])
    (α' β' γ' : ℝ) (hα' : 0 < α') (hβ' : 0 < β') (hγ' : 0 < γ')
    (hsum' : α' + β' + γ' = 1)
    (hD : D = α' • A + β' • B + γ' • C)
    (hang : ∠ A D B = ∠ B D C ∧ ∠ B D C = ∠ C D A) :
    dist D A + dist D B + dist D C = 1 := by
  -- Eliminate `α` using `α + β + γ = 1`.
  have hαe : α = 1 - β - γ := by linarith
  subst hαe
  -- Squared side lengths of the equilateral triangle, in coordinates.
  have hs1 : (A₀ 0 - B₀ 0) ^ 2 + (A₀ 1 - B₀ 1) ^ 2 = 1 := by
    rw [← dist_sq_fin2, hA₀B₀]; norm_num
  have hs2 : (B₀ 0 - C₀ 0) ^ 2 + (B₀ 1 - C₀ 1) ^ 2 = 1 := by
    rw [← dist_sq_fin2, hB₀C₀]; norm_num
  have hs3 : (C₀ 0 - A₀ 0) ^ 2 + (C₀ 1 - A₀ 1) ^ 2 = 1 := by
    rw [← dist_sq_fin2, hC₀A₀]; norm_num
  -- Coordinates of `P`.
  have hP0 : P 0 = (1 - β - γ) * A₀ 0 + β * B₀ 0 + γ * C₀ 0 := by
    rw [hP]; simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  have hP1 : P 1 = (1 - β - γ) * A₀ 1 + β * B₀ 1 + γ * C₀ 1 := by
    rw [hP]; simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  -- The distances `a, b, c` in terms of the barycentric coordinates of `P`.
  have ha2 : a ^ 2 = β ^ 2 + β * γ + γ ^ 2 := by
    have e := dist_sq_fin2 P A₀
    rw [ha, hP0, hP1] at e
    rw [e]
    have h := equilateral_rel (B₀ 0 - A₀ 0) (B₀ 1 - A₀ 1) (C₀ 0 - A₀ 0) (C₀ 1 - A₀ 1)
      β γ (by linear_combination hs1) (by linear_combination hs3)
      (by linear_combination hs2)
    linear_combination h
  have hb2 : b ^ 2 = γ ^ 2 + γ * (1 - β - γ) + (1 - β - γ) ^ 2 := by
    have e := dist_sq_fin2 P B₀
    rw [hb, hP0, hP1] at e
    rw [e]
    have h := equilateral_rel (C₀ 0 - B₀ 0) (C₀ 1 - B₀ 1) (A₀ 0 - B₀ 0) (A₀ 1 - B₀ 1)
      γ (1 - β - γ) (by linear_combination hs2) (by linear_combination hs1)
      (by linear_combination hs3)
    linear_combination h
  have hc2 : c ^ 2 = (1 - β - γ) ^ 2 + (1 - β - γ) * β + β ^ 2 := by
    have e := dist_sq_fin2 P C₀
    rw [hc, hP0, hP1] at e
    rw [e]
    have h := equilateral_rel (A₀ 0 - C₀ 0) (A₀ 1 - C₀ 1) (B₀ 0 - C₀ 0) (B₀ 1 - C₀ 1)
      (1 - β - γ) β (by linear_combination hs3) (by linear_combination hs2)
      (by linear_combination hs1)
    linear_combination h
  -- The symmetric relation from the equilateral side vanishes.
  have hR0 := key_id (a ^ 2) (b ^ 2) (c ^ 2) (1 - β - γ) β γ ha2 hb2 hc2
  rw [show (1 - β - γ) + β + γ = (1 : ℝ) by ring] at hR0
  rw [show ((1 : ℝ) - 1 ^ 2) = 0 by norm_num, zero_mul] at hR0
  -- Nondegeneracy determinants of triangle `ABC`.
  have hdet1 : (B 0 - A 0) * (C 1 - A 1) - (B 1 - A 1) * (C 0 - A 0) ≠ 0 :=
    det_ne_zero_of_lind A B C hli
  have hdet2 : (A 0 - B 0) * (C 1 - B 1) - (A 1 - B 1) * (C 0 - B 0) ≠ 0 := by
    intro h; apply hdet1; linear_combination -h
  have hdet3 : (A 0 - C 0) * (B 1 - C 1) - (A 1 - C 1) * (B 0 - C 0) ≠ 0 := by
    intro h; apply hdet1; linear_combination h
  -- Coordinates of `D`.
  have hD0 : D 0 = α' * A 0 + β' * B 0 + γ' * C 0 := by
    rw [hD]; simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  have hD1 : D 1 = α' * A 1 + β' * B 1 + γ' * C 1 := by
    rw [hD]; simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  -- `D` is distinct from the vertices.
  have hu : 0 < ‖A - D‖ := by
    rw [norm_pos_iff]
    intro h0
    have hDA : D = A := (sub_eq_zero.mp h0).symm
    rw [hDA] at hD0 hD1
    have s0 : β' * (B 0 - A 0) + γ' * (C 0 - A 0) = 0 := by
      linear_combination -hD0 - A 0 * hsum'
    have s1 : β' * (B 1 - A 1) + γ' * (C 1 - A 1) = 0 := by
      linear_combination -hD1 - A 1 * hsum'
    rcases smul_eq_zero_of_det_ne_zero hdet1 s0 s1 with ⟨hβ0, -⟩
    linarith
  have hv : 0 < ‖B - D‖ := by
    rw [norm_pos_iff]
    intro h0
    have hDB : D = B := (sub_eq_zero.mp h0).symm
    rw [hDB] at hD0 hD1
    have s0 : α' * (A 0 - B 0) + γ' * (C 0 - B 0) = 0 := by
      linear_combination -hD0 - B 0 * hsum'
    have s1 : α' * (A 1 - B 1) + γ' * (C 1 - B 1) = 0 := by
      linear_combination -hD1 - B 1 * hsum'
    rcases smul_eq_zero_of_det_ne_zero hdet2 s0 s1 with ⟨hα0, -⟩
    linarith
  have hw : 0 < ‖C - D‖ := by
    rw [norm_pos_iff]
    intro h0
    have hDC : D = C := (sub_eq_zero.mp h0).symm
    rw [hDC] at hD0 hD1
    have s0 : α' * (A 0 - C 0) + β' * (B 0 - C 0) = 0 := by
      linear_combination -hD0 - C 0 * hsum'
    have s1 : α' * (A 1 - C 1) + β' * (B 1 - C 1) = 0 := by
      linear_combination -hD1 - C 1 * hsum'
    rcases smul_eq_zero_of_det_ne_zero hdet3 s0 s1 with ⟨hα0, -⟩
    linarith
  -- The common cosine of the three subtended angles.
  have hcosADB : Real.cos (∠ A D B) = ⟪A - D, B - D⟫ / (‖A - D‖ * ‖B - D‖) := by
    show Real.cos (InnerProductGeometry.angle (A -ᵥ D) (B -ᵥ D)) = _
    rw [vsub_eq_sub, vsub_eq_sub, InnerProductGeometry.cos_angle]
  have hcosBDC : Real.cos (∠ B D C) = ⟪B - D, C - D⟫ / (‖B - D‖ * ‖C - D‖) := by
    show Real.cos (InnerProductGeometry.angle (B -ᵥ D) (C -ᵥ D)) = _
    rw [vsub_eq_sub, vsub_eq_sub, InnerProductGeometry.cos_angle]
  have hcosCDA : Real.cos (∠ C D A) = ⟪C - D, A - D⟫ / (‖C - D‖ * ‖A - D‖) := by
    show Real.cos (InnerProductGeometry.angle (C -ᵥ D) (A -ᵥ D)) = _
    rw [vsub_eq_sub, vsub_eq_sub, InnerProductGeometry.cos_angle]
  have h1 := congrArg Real.cos hang.1
  rw [hcosADB, hcosBDC] at h1
  have h2 := congrArg Real.cos hang.2
  rw [hcosBDC, hcosCDA] at h2
  set μ := ⟪A - D, B - D⟫ / (‖A - D‖ * ‖B - D‖) with hμdef
  have e1 : ⟪A - D, B - D⟫ = μ * (‖A - D‖ * ‖B - D‖) := by
    rw [hμdef]
    exact (div_mul_cancel₀ _ (mul_ne_zero (ne_of_gt hu) (ne_of_gt hv))).symm
  have e2 : ⟪B - D, C - D⟫ = μ * (‖B - D‖ * ‖C - D‖) := by
    rw [h1]
    exact (div_mul_cancel₀ _ (mul_ne_zero (ne_of_gt hv) (ne_of_gt hw))).symm
  have e3 : ⟪C - D, A - D⟫ = μ * (‖C - D‖ * ‖A - D‖) := by
    rw [h1, h2]
    exact (div_mul_cancel₀ _ (mul_ne_zero (ne_of_gt hw) (ne_of_gt hu))).symm
  -- The Gram determinant of three vectors in the plane vanishes.
  have hGram : ‖A - D‖ ^ 2 * ‖B - D‖ ^ 2 * ‖C - D‖ ^ 2 +
      2 * ⟪A - D, B - D⟫ * ⟪B - D, C - D⟫ * ⟪C - D, A - D⟫ -
      ‖A - D‖ ^ 2 * ⟪B - D, C - D⟫ ^ 2 - ‖B - D‖ ^ 2 * ⟪C - D, A - D⟫ ^ 2 -
      ‖C - D‖ ^ 2 * ⟪A - D, B - D⟫ ^ 2 = 0 := by
    simp only [inner_fin2, norm_sq_fin2, PiLp.sub_apply]
    ring
  rw [e1, e2, e3] at hGram
  -- Hence the common cosine satisfies `(μ - 1)² * (2μ + 1) = 0`.
  have hμ2 : (μ - 1) ^ 2 * (2 * μ + 1) = 0 := by
    have huvw : ‖A - D‖ ^ 2 * ‖B - D‖ ^ 2 * ‖C - D‖ ^ 2 ≠ 0 :=
      mul_ne_zero (mul_ne_zero (pow_ne_zero 2 (ne_of_gt hu))
        (pow_ne_zero 2 (ne_of_gt hv))) (pow_ne_zero 2 (ne_of_gt hw))
    have h0 : ‖A - D‖ ^ 2 * ‖B - D‖ ^ 2 * ‖C - D‖ ^ 2 * (2 * μ ^ 3 - 3 * μ ^ 2 + 1)
        = 0 := by
      linear_combination hGram
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h huvw
    · linear_combination h
  -- The case `μ = 1` would force `A - D` and `B - D` to be parallel,
  -- contradicting `D` being strictly inside the triangle.
  have hμ : μ = -1 / 2 := by
    rcases mul_eq_zero.mp hμ2 with h | h
    · have hμ1 : μ = 1 := by
        have := sq_eq_zero_iff.mp h
        linarith
      exfalso
      have hp : ⟪A - D, B - D⟫ = ‖A - D‖ * ‖B - D‖ := by rw [e1, hμ1, one_mul]
      have hdet0 : (A 0 - D 0) * (B 1 - D 1) - (A 1 - D 1) * (B 0 - D 0) = 0 := by
        have h2 : ‖A - D‖ ^ 2 * ‖B - D‖ ^ 2 - ⟪A - D, B - D⟫ ^ 2 = 0 := by
          rw [hp]; ring
        have h3 : ((A 0 - D 0) * (B 1 - D 1) - (A 1 - D 1) * (B 0 - D 0)) ^ 2 =
            ‖A - D‖ ^ 2 * ‖B - D‖ ^ 2 - ⟪A - D, B - D⟫ ^ 2 := by
          simp only [inner_fin2, norm_sq_fin2, PiLp.sub_apply]; ring
        rw [h2] at h3
        exact sq_eq_zero_iff.mp h3
      have hdetγ : (A 0 - D 0) * (B 1 - D 1) - (A 1 - D 1) * (B 0 - D 0) =
          γ' * ((B 0 - A 0) * (C 1 - A 1) - (B 1 - A 1) * (C 0 - A 0)) := by
        rw [hD0, hD1]
        linear_combination (A 1 * (B 0 - A 0) - A 0 * (B 1 - A 1)) * hsum'
      rw [hdet0] at hdetγ
      rcases mul_eq_zero.mp hdetγ.symm with hγ0 | hγ0
      · linarith
      · exact det_ne_zero_of_lind A B C hli hγ0
    · linarith
  -- Law of cosines with angle `120°`: the sides of `ABC`.
  have ha2F : a ^ 2 = ‖B - D‖ ^ 2 + ‖B - D‖ * ‖C - D‖ + ‖C - D‖ ^ 2 := by
    have e : dist B C ^ 2 = ‖B - D‖ ^ 2 - 2 * ⟪B - D, C - D⟫ + ‖C - D‖ ^ 2 := by
      rw [dist_eq_norm, show B - C = (B - D) - (C - D) from by abel, norm_sub_sq_real]
    rw [hBC, e2, hμ] at e
    linear_combination e
  have hb2F : b ^ 2 = ‖C - D‖ ^ 2 + ‖C - D‖ * ‖A - D‖ + ‖A - D‖ ^ 2 := by
    have e : dist C A ^ 2 = ‖C - D‖ ^ 2 - 2 * ⟪C - D, A - D⟫ + ‖A - D‖ ^ 2 := by
      rw [dist_eq_norm, show C - A = (C - D) - (A - D) from by abel, norm_sub_sq_real]
    rw [hCA, e3, hμ] at e
    linear_combination e
  have hc2F : c ^ 2 = ‖A - D‖ ^ 2 + ‖A - D‖ * ‖B - D‖ + ‖B - D‖ ^ 2 := by
    have e : dist A B ^ 2 = ‖A - D‖ ^ 2 - 2 * ⟪A - D, B - D⟫ + ‖B - D‖ ^ 2 := by
      rw [dist_eq_norm, show A - B = (A - D) - (B - D) from by abel, norm_sub_sq_real]
    rw [hAB, e1, hμ] at e
    linear_combination e
  -- The same symmetric expression from the Fermat-point side.
  have hR1 := key_id (a ^ 2) (b ^ 2) (c ^ 2) ‖A - D‖ ‖B - D‖ ‖C - D‖ ha2F hb2F hc2F
  rw [hR0] at hR1
  rcases mul_eq_zero.mp hR1.symm with hcase | hcase
  · -- The good case: `‖A-D‖ + ‖B-D‖ + ‖C-D‖ = 1`.
    have hσ1 : ‖A - D‖ + ‖B - D‖ + ‖C - D‖ = 1 := by
      have h2 : (‖A - D‖ + ‖B - D‖ + ‖C - D‖) ^ 2 = 1 := by
        linear_combination -hcase
      rcases sq_eq_one_iff.mp h2 with h | h
      · exact h
      · have hpos : 0 < ‖A - D‖ + ‖B - D‖ + ‖C - D‖ := add_pos (add_pos hu hv) hw
        linarith
    have eA : dist D A = ‖A - D‖ := by rw [dist_eq_norm, norm_sub_rev]
    have eB : dist D B = ‖B - D‖ := by rw [dist_eq_norm, norm_sub_rev]
    have eC : dist D C = ‖C - D‖ := by rw [dist_eq_norm, norm_sub_rev]
    rw [eA, eB, eC]
    exact hσ1
  · -- The extraneous case is excluded since `a, b, c < 1`
    -- (distances from an interior point are smaller than the side).
    exfalso
    have hσ2 : ‖A - D‖ ^ 2 + ‖B - D‖ ^ 2 + ‖C - D‖ ^ 2 -
        (‖A - D‖ * ‖B - D‖ + ‖B - D‖ * ‖C - D‖ + ‖C - D‖ * ‖A - D‖) = 1 := by
      linear_combination -hcase
    have hlt_a : a ^ 2 < 1 := by
      have e : 1 - a ^ 2 =
          (1 - β - γ) ^ 2 + 2 * ((1 - β - γ) * β) + 2 * ((1 - β - γ) * γ) + β * γ := by
        linear_combination -ha2
      linarith [e, sq_pos_of_pos hα, mul_pos hα hβ, mul_pos hα hγ, mul_pos hβ hγ]
    have hlt_b : b ^ 2 < 1 := by
      have e : 1 - b ^ 2 =
          β ^ 2 + 2 * (β * γ) + 2 * (β * (1 - β - γ)) + γ * (1 - β - γ) := by
        linear_combination -hb2
      linarith [e, sq_pos_of_pos hβ, mul_pos hβ hγ, mul_pos hβ hα, mul_pos hγ hα]
    have hlt_c : c ^ 2 < 1 := by
      have e : 1 - c ^ 2 =
          γ ^ 2 + 2 * (β * γ) + 2 * (γ * (1 - β - γ)) + β * (1 - β - γ) := by
        linear_combination -hc2
      linarith [e, sq_pos_of_pos hγ, mul_pos hβ hγ, mul_pos hγ hα, mul_pos hβ hα]
    have g1 : ‖A - D‖ ^ 2 > 2 * (‖B - D‖ * ‖C - D‖) := by
      have e : 1 - a ^ 2 = ‖A - D‖ ^ 2 - ‖A - D‖ * ‖B - D‖ - ‖A - D‖ * ‖C - D‖ -
          2 * (‖B - D‖ * ‖C - D‖) := by
        linear_combination -hσ2 - ha2F
      linarith [e, hlt_a, mul_pos hu hv, mul_pos hu hw]
    have g2 : ‖B - D‖ ^ 2 > 2 * (‖C - D‖ * ‖A - D‖) := by
      have e : 1 - b ^ 2 = ‖B - D‖ ^ 2 - ‖A - D‖ * ‖B - D‖ - ‖B - D‖ * ‖C - D‖ -
          2 * (‖C - D‖ * ‖A - D‖) := by
        linear_combination -hσ2 - hb2F
      linarith [e, hlt_b, mul_pos hu hv, mul_pos hv hw]
    have g3 : ‖C - D‖ ^ 2 > 2 * (‖A - D‖ * ‖B - D‖) := by
      have e : 1 - c ^ 2 = ‖C - D‖ ^ 2 - ‖B - D‖ * ‖C - D‖ - ‖C - D‖ * ‖A - D‖ -
          2 * (‖A - D‖ * ‖B - D‖) := by
        linear_combination -hσ2 - hc2F
      linarith [e, hlt_c, mul_pos hu hw, mul_pos hv hw]
    -- Multiplying the three strict inequalities gives `8 * T < T` with `T > 0`.
    have hpos : 0 < ‖A - D‖ ^ 2 * ‖B - D‖ ^ 2 * ‖C - D‖ ^ 2 :=
      mul_pos (mul_pos (pow_pos hu 2) (pow_pos hv 2)) (pow_pos hw 2)
    have hm1 := mul_lt_mul g1 g2.le (mul_pos (by norm_num) (mul_pos hw hu))
      (le_of_lt (pow_pos hu 2))
    have hm2 := mul_lt_mul hm1 g3.le (mul_pos (by norm_num) (mul_pos hu hv))
      (le_of_lt (mul_pos (pow_pos hu 2) (pow_pos hv 2)))
    linarith [hm2, hpos]

end Usa1974P5
