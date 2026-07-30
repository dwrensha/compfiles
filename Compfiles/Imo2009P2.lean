/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Euclidean.Sphere.Basic
public import Mathlib.Tactic.Positivity.Finset
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 2009, Problem 2

Let ABC be a triangle with circumcenter O. The points P and Q are interior
points of the sides CA and AB respectively. Let K, L, M be the midpoints of
BP, CQ, PQ. Suppose that PQ is tangent to the circumcircle of △KLM.
Prove that OP = OQ.
-/

open scoped RealInnerProductSpace

namespace Imo2009P2

snip begin

/-- Squared distance in the Euclidean plane, coordinatewise. -/
lemma dist_sq (x y : EuclideanSpace ℝ (Fin 2)) :
    dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two]
  congr 1 <;> rw [Real.dist_eq, sq_abs]

/-- Inner product in the Euclidean plane, coordinatewise. -/
lemma inner_plane (x y : EuclideanSpace ℝ (Fin 2)) :
    ⟪x, y⟫ = x 0 * y 0 + x 1 * y 1 := by
  rw [PiLp.inner_apply, Fin.sum_univ_two]
  simp only [Real.inner_apply]

snip end

problem imo2009_p2
    (A B C O P Q K L M : EuclideanSpace ℝ (Fin 2))
    (hO : dist O A = dist O B ∧ dist O B = dist O C)
    (hP : Sbtw ℝ C P A) (hQ : Sbtw ℝ A Q B)
    (hK : K = midpoint ℝ B P) (hL : L = midpoint ℝ C Q)
    (hM : M = midpoint ℝ P Q)
    (htan : ∃ s : EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin 2)),
      K ∈ s ∧ L ∈ s ∧ M ∈ s ∧ ⟪s.center - M, P - Q⟫ = 0) :
    dist O P = dist O Q := by
  obtain ⟨hOAB, hOBC⟩ := hO
  -- Write `P = (1 - lam) • C + lam • A` and `Q = (1 - mu) • A + mu • B`.
  obtain ⟨hPw, hPC, -⟩ := hP
  obtain ⟨hQw, -, hQB⟩ := hQ
  have hPmem : P ∈ segment ℝ C A := mem_segment_iff_wbtw.mpr hPw
  have hQmem : Q ∈ segment ℝ A B := mem_segment_iff_wbtw.mpr hQw
  rw [segment_eq_image] at hPmem hQmem
  obtain ⟨lam, hlamI, rfl⟩ := hPmem
  obtain ⟨mu, hmuI, rfl⟩ := hQmem
  -- Interiority gives `lam ≠ 0` (else `P = C`) and `mu ≠ 1` (else `Q = B`).
  have hlam : lam ≠ 0 := by
    rintro rfl; simp at hPC
  have hmu : mu ≠ 1 := by
    rintro rfl; simp at hQB
  -- Unpack the tangency hypothesis.
  obtain ⟨s, hsK, hsL, hsM, hT⟩ := htan
  have dK : dist K s.center = s.radius := EuclideanGeometry.mem_sphere.mp hsK
  have dL : dist L s.center = s.radius := EuclideanGeometry.mem_sphere.mp hsL
  have dM : dist M s.center = s.radius := EuclideanGeometry.mem_sphere.mp hsM
  -- Metric relations, squared.
  have h1 : dist O A ^ 2 = dist O B ^ 2 := congrArg (· ^ 2) hOAB
  have h2 : dist O B ^ 2 = dist O C ^ 2 := congrArg (· ^ 2) hOBC
  have d2 : dist s.center K ^ 2 = dist s.center M ^ 2 := by
    rw [dist_comm s.center K, dK, dist_comm s.center M, dM]
  have d3 : dist s.center L ^ 2 = dist s.center M ^ 2 := by
    rw [dist_comm s.center L, dL, dist_comm s.center M, dM]
  -- Expand everything into coordinates.
  simp only [dist_sq] at h1 h2
  simp only [dist_sq, hK, hL, hM, midpoint_eq_smul_add, PiLp.add_apply,
    PiLp.smul_apply, smul_eq_mul, invOf_eq_inv] at d2 d3
  rw [inner_plane] at hT
  simp only [hM, midpoint_eq_smul_add, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
    smul_eq_mul, invOf_eq_inv] at hT
  -- The key identity, a polynomial consequence of the five relations.
  have key : lam * (1 - mu) * (dist O ((1 - lam) • C + lam • A) ^ 2)
      = lam * (1 - mu) * (dist O ((1 - mu) • A + mu • B) ^ 2) := by
    simp only [dist_sq, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    linear_combination
      lam * (1 - mu) * (lam + mu - 1) * h1 - lam * (1 - lam) * (1 - mu) * h2
        - 4 * lam * (1 - mu) * hT + 4 * lam * mu * d2 - 4 * (1 - lam) * (1 - mu) * d3
  have hsq : dist O ((1 - lam) • C + lam • A) ^ 2
      = dist O ((1 - mu) • A + mu • B) ^ 2 :=
    mul_left_cancel₀ (mul_ne_zero hlam (sub_ne_zero.mpr hmu.symm)) key
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · exact h
  · have hnn1 : (0:ℝ) ≤ dist O ((1 - lam) • C + lam • A) := dist_nonneg
    have hnn2 : (0:ℝ) ≤ dist O ((1 - mu) • A + mu • B) := dist_nonneg
    linarith

end Imo2009P2
