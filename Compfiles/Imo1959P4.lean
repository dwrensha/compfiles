/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.RightAngle
public import Mathlib.Geometry.Euclidean.Triangle
public import Mathlib.LinearAlgebra.AffineSpace.Midpoint
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 1959, Problem 4

Given the length |AC|, construct a triangle ABC with ∠ABC = 90°,
and the median BM satisfying BM² = AB·BC.
-/

namespace Imo1959P4

open EuclideanGeometry
open scoped Real

/-- The property required of the triangle `ABC`: the segment `AC` is nondegenerate,
the angle at `B` is a right angle, and the square of the median from `B` to the
midpoint of `AC` equals the product of the two legs `AB` and `BC`. -/
def IsConstruction (A B C : EuclideanSpace ℝ (Fin 2)) : Prop :=
  A ≠ C ∧ ∠ A B C = π / 2 ∧ dist B (midpoint ℝ A C) ^ 2 = dist A B * dist B C

snip begin

/-- In a right-angled triangle (right angle at `B`), the square of the median from
`B` to the midpoint of the hypotenuse `AC` equals the square of half the hypotenuse. -/
theorem median_sq_eq_of_right_angle {A B C : EuclideanSpace ℝ (Fin 2)}
    (h : ∠ A B C = π / 2) :
    dist B (midpoint ℝ A C) ^ 2 = (dist A C / 2) ^ 2 := by
  have hpyth := (dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two A B C).2 h
  have hapol := dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq B A C
  rw [dist_comm B A] at hapol
  rw [dist_comm C B] at hpyth
  nlinarith [hpyth, hapol]

/-- Hence the condition on the median determines the product of the legs. -/
theorem legs_mul_eq {A B C : EuclideanSpace ℝ (Fin 2)} (h : IsConstruction A B C) :
    dist A B * dist B C = dist A C ^ 2 / 4 := by
  have hm := median_sq_eq_of_right_angle h.2.1
  rw [h.2.2] at hm
  rw [hm]
  ring

/-- The triangle is nondegenerate at `A` (and `B`). -/
theorem ne_left {A B C : EuclideanSpace ℝ (Fin 2)} (h : IsConstruction A B C) : A ≠ B := by
  intro hAB
  have hm := legs_mul_eq h
  subst hAB
  simp only [dist_self, zero_mul] at hm
  have hd : 0 < dist A C := dist_pos.mpr h.1
  nlinarith [sq_nonneg (dist A C)]

/-- The triangle is nondegenerate at `C` (and `B`). -/
theorem ne_right {A B C : EuclideanSpace ℝ (Fin 2)} (h : IsConstruction A B C) : B ≠ C := by
  intro hBC
  have hm := legs_mul_eq h
  subst hBC
  rw [dist_self, mul_zero] at hm
  have hd : 0 < dist A B := dist_pos.mpr h.1
  nlinarith [sq_nonneg (dist A B)]

/-- Pure-algebra heart of the problem: positive reals `p, q` whose squares sum to
`d ^ 2` and whose product is `d ^ 2 / 4` must be `d·(√6 - √2)/4` and `d·(√6 + √2)/4`,
in some order. -/
theorem legs_algebra {p q d : ℝ} (hp : 0 < p) (hq : 0 < q) (hd : 0 < d)
    (h1 : p ^ 2 + q ^ 2 = d ^ 2) (h2 : p * q = d ^ 2 / 4) :
    (p = d * ((Real.sqrt 6 - Real.sqrt 2) / 4) ∧
     q = d * ((Real.sqrt 6 + Real.sqrt 2) / 4)) ∨
    (p = d * ((Real.sqrt 6 + Real.sqrt 2) / 4) ∧
     q = d * ((Real.sqrt 6 - Real.sqrt 2) / 4)) := by
  have hsq6 : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have hsq3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h12 : Real.sqrt 6 * Real.sqrt 2 = 2 * Real.sqrt 3 := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 6),
      show (6 : ℝ) * 2 = 2 ^ 2 * 3 by norm_num,
      Real.sqrt_mul (sq_nonneg (2 : ℝ)), Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  have hle32 : Real.sqrt 3 ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hle26 : Real.sqrt 2 ≤ Real.sqrt 6 := Real.sqrt_le_sqrt (by norm_num)
  have hsqrt_sub : Real.sqrt ((2 - Real.sqrt 3) / 4) = (Real.sqrt 6 - Real.sqrt 2) / 4 := by
    have hx : (0 : ℝ) ≤ (2 - Real.sqrt 3) / 4 := div_nonneg (by linarith) (by norm_num)
    have hy : (0 : ℝ) ≤ (Real.sqrt 6 - Real.sqrt 2) / 4 :=
      div_nonneg (by linarith) (by norm_num)
    rw [Real.sqrt_eq_iff_eq_sq hx hy]
    have he : ((Real.sqrt 6 - Real.sqrt 2) / 4) ^ 2
        = (Real.sqrt 6 ^ 2 - 2 * (Real.sqrt 6 * Real.sqrt 2) + Real.sqrt 2 ^ 2) / 16 := by
      ring
    rw [he, hsq6, hsq2, h12]
    ring
  have hsqrt_add : Real.sqrt ((2 + Real.sqrt 3) / 4) = (Real.sqrt 6 + Real.sqrt 2) / 4 := by
    have hx : (0 : ℝ) ≤ (2 + Real.sqrt 3) / 4 := by positivity
    have hy : (0 : ℝ) ≤ (Real.sqrt 6 + Real.sqrt 2) / 4 := by positivity
    rw [Real.sqrt_eq_iff_eq_sq hx hy]
    have he : ((Real.sqrt 6 + Real.sqrt 2) / 4) ^ 2
        = (Real.sqrt 6 ^ 2 + 2 * (Real.sqrt 6 * Real.sqrt 2) + Real.sqrt 2 ^ 2) / 16 := by
      ring
    rw [he, hsq6, hsq2, h12]
    ring
  have h3 : (p ^ 2 - q ^ 2) ^ 2 = 3 / 4 * d ^ 4 := by
    have hring : (p ^ 2 - q ^ 2) ^ 2 = (p ^ 2 + q ^ 2) ^ 2 - 4 * (p * q) ^ 2 := by ring
    rw [hring, h1, h2]
    ring
  have habs : |p ^ 2 - q ^ 2| = Real.sqrt 3 / 2 * d ^ 2 := by
    have hnonneg : 0 ≤ Real.sqrt 3 / 2 * d ^ 2 := by positivity
    have hsq : (Real.sqrt 3 / 2 * d ^ 2) ^ 2 = 3 / 4 * d ^ 4 := by
      have hrw : (Real.sqrt 3 / 2 * d ^ 2) ^ 2 = Real.sqrt 3 ^ 2 / 4 * d ^ 4 := by ring
      rw [hrw, hsq3]
    have hsqeq : (p ^ 2 - q ^ 2) ^ 2 = (Real.sqrt 3 / 2 * d ^ 2) ^ 2 := by rw [h3, hsq]
    have h := (sq_eq_sq_iff_abs_eq_abs (p ^ 2 - q ^ 2) (Real.sqrt 3 / 2 * d ^ 2)).1 hsqeq
    rwa [abs_of_nonneg hnonneg] at h
  rcases le_total p q with hpq | hqp
  · have hle : p ^ 2 - q ^ 2 ≤ 0 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hpq) (add_nonneg hp.le hq.le)]
    rw [abs_of_nonpos hle] at habs
    have hq2 : q ^ 2 - p ^ 2 = Real.sqrt 3 / 2 * d ^ 2 := by linarith [habs]
    have hp2 : p ^ 2 = d ^ 2 * ((2 - Real.sqrt 3) / 4) := by linarith [h1, hq2]
    have hq2' : q ^ 2 = d ^ 2 * ((2 + Real.sqrt 3) / 4) := by linarith [h1, hq2]
    have hpeq : p = d * ((Real.sqrt 6 - Real.sqrt 2) / 4) := by
      rw [← Real.sqrt_sq hp.le, hp2, Real.sqrt_mul (sq_nonneg d), Real.sqrt_sq hd.le,
        hsqrt_sub]
    have hqeq : q = d * ((Real.sqrt 6 + Real.sqrt 2) / 4) := by
      rw [← Real.sqrt_sq hq.le, hq2', Real.sqrt_mul (sq_nonneg d), Real.sqrt_sq hd.le,
        hsqrt_add]
    exact Or.inl ⟨hpeq, hqeq⟩
  · have hle : 0 ≤ p ^ 2 - q ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hqp) (add_nonneg hp.le hq.le)]
    rw [abs_of_nonneg hle] at habs
    have hp2' : p ^ 2 - q ^ 2 = Real.sqrt 3 / 2 * d ^ 2 := habs
    have hp2 : p ^ 2 = d ^ 2 * ((2 + Real.sqrt 3) / 4) := by linarith [h1, hp2']
    have hq2 : q ^ 2 = d ^ 2 * ((2 - Real.sqrt 3) / 4) := by linarith [h1, hp2']
    have hpeq : p = d * ((Real.sqrt 6 + Real.sqrt 2) / 4) := by
      rw [← Real.sqrt_sq hp.le, hp2, Real.sqrt_mul (sq_nonneg d), Real.sqrt_sq hd.le,
        hsqrt_add]
    have hqeq : q = d * ((Real.sqrt 6 - Real.sqrt 2) / 4) := by
      rw [← Real.sqrt_sq hq.le, hq2, Real.sqrt_mul (sq_nonneg d), Real.sqrt_sq hd.le,
        hsqrt_sub]
    exact Or.inr ⟨hpeq, hqeq⟩

/-- The legs of any such triangle are determined: they are
`|AC|·(√6 - √2)/4` and `|AC|·(√6 + √2)/4`, in some order. -/
theorem legs_eq {A B C : EuclideanSpace ℝ (Fin 2)} (h : IsConstruction A B C) :
    (dist A B = dist A C * ((Real.sqrt 6 - Real.sqrt 2) / 4) ∧
     dist B C = dist A C * ((Real.sqrt 6 + Real.sqrt 2) / 4)) ∨
    (dist A B = dist A C * ((Real.sqrt 6 + Real.sqrt 2) / 4) ∧
     dist B C = dist A C * ((Real.sqrt 6 - Real.sqrt 2) / 4)) := by
  have hp : 0 < dist A B := dist_pos.mpr (ne_left h)
  have hq : 0 < dist B C := dist_pos.mpr (ne_right h)
  have hd : 0 < dist A C := dist_pos.mpr h.1
  have h2 : dist A B * dist B C = dist A C ^ 2 / 4 := legs_mul_eq h
  have hpyth := (dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two A B C).2 h.2.1
  rw [dist_comm C B] at hpyth
  have h1 : dist A B ^ 2 + dist B C ^ 2 = dist A C ^ 2 := by nlinarith [hpyth]
  exact legs_algebra hp hq hd h1 h2

/-- The construction: take `B` on the circle with diameter `AC` (equivalently,
with `∠ABC = 90°`) at perpendicular distance `|AC|/4` from the line `AC`;
concretely, `B` is the midpoint of `AC` plus `√3/4` of the vector `C -ᵥ A`
plus `1/4` of that vector rotated by a right angle. -/
theorem exists_B (A C : EuclideanSpace ℝ (Fin 2)) (hAC : A ≠ C) :
    ∃ B, IsConstruction A B C := by
  have hs2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hdist_sq : ∀ x y : EuclideanSpace ℝ (Fin 2),
      dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
    intro x y
    simp [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq, sq_abs]
  set B : EuclideanSpace ℝ (Fin 2) :=
    !₂[ (A 0 + C 0) / 2 + Real.sqrt 3 / 4 * (C 0 - A 0) - (C 1 - A 1) / 4,
        (A 1 + C 1) / 2 + Real.sqrt 3 / 4 * (C 1 - A 1) + (C 0 - A 0) / 4 ] with hB
  have hAC2 : dist A C ^ 2 = (A 0 - C 0) ^ 2 + (A 1 - C 1) ^ 2 := hdist_sq A C
  have hAB2 : dist A B ^ 2
      = ((A 0 - C 0) ^ 2 + (A 1 - C 1) ^ 2) * (2 + Real.sqrt 3) / 4 := by
    rw [hdist_sq]
    simp only [hB, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination ((A 0 - C 0) ^ 2 + (A 1 - C 1) ^ 2) / 16 * hs2
  have hBC2 : dist B C ^ 2
      = ((A 0 - C 0) ^ 2 + (A 1 - C 1) ^ 2) * (2 - Real.sqrt 3) / 4 := by
    rw [hdist_sq]
    simp only [hB, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination ((A 0 - C 0) ^ 2 + (A 1 - C 1) ^ 2) / 16 * hs2
  have hpyth : dist A C * dist A C = dist A B * dist A B + dist C B * dist C B := by
    rw [dist_comm C B]
    simp only [← pow_two]
    rw [hAC2, hAB2, hBC2]
    ring
  have hangle : ∠ A B C = π / 2 :=
    (dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two A B C).1 hpyth
  have hmed : dist B (midpoint ℝ A C) ^ 2 = (dist A C / 2) ^ 2 :=
    median_sq_eq_of_right_angle hangle
  have hprod_sq : (dist A B * dist B C) ^ 2
      = (((A 0 - C 0) ^ 2 + (A 1 - C 1) ^ 2) / 4) ^ 2 := by
    rw [mul_pow, hAB2, hBC2]
    linear_combination (-(((A 0 - C 0) ^ 2 + (A 1 - C 1) ^ 2) ^ 2 / 16)) * hs2
  have hprod : dist A B * dist B C = ((A 0 - C 0) ^ 2 + (A 1 - C 1) ^ 2) / 4 := by
    have h := (sq_eq_sq_iff_abs_eq_abs _ _).mp hprod_sq
    rwa [abs_of_nonneg (by positivity : (0 : ℝ) ≤ dist A B * dist B C),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((A 0 - C 0) ^ 2 + (A 1 - C 1) ^ 2) / 4)] at h
  refine ⟨B, hAC, hangle, ?_⟩
  rw [hmed, hprod]
  linear_combination (1 / 4) * hAC2

snip end

/-- The shorter leg of the triangle, as a multiple of `|AC|`. -/
noncomputable determine shortLeg : ℝ := (Real.sqrt 6 - Real.sqrt 2) / 4

/-- The longer leg of the triangle, as a multiple of `|AC|`. -/
noncomputable determine longLeg : ℝ := (Real.sqrt 6 + Real.sqrt 2) / 4

problem imo1959_p4_legs {A B C : EuclideanSpace ℝ (Fin 2)} (h : IsConstruction A B C) :
    (dist A B = dist A C * shortLeg ∧ dist B C = dist A C * longLeg) ∨
    (dist A B = dist A C * longLeg ∧ dist B C = dist A C * shortLeg) := by
  exact legs_eq h

problem imo1959_p4 (A C : EuclideanSpace ℝ (Fin 2)) (hAC : A ≠ C) :
    ∃ B, IsConstruction A B C := by
  exact exists_B A C hAC

end Imo1959P4
