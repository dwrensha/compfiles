/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.Geometry.Euclidean.MongePoint
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry, .Inequality] }

/-!
# International Mathematical Olympiad 1970, Problem 5

In the tetrahedron ABCD, angle BDC = 90° and the foot of the perpendicular
from D to the plane ABC is the intersection of the altitudes of ABC.
Prove that:

  (AB + BC + CA)² ≤ 6(AD² + BD² + CD²).

When do we have equality?
-/

namespace Imo1970P5

open Affine EuclideanGeometry
open scoped EuclideanGeometry Real RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {P : Type*} [MetricSpace P] [NormedAddTorsor V P]

snip begin

/-!
The solution proceeds vectorially from the orthocenter `H` of `ABC`.
Writing `a = A -ᵥ H`, `b = B -ᵥ H`, `c = C -ᵥ H` and `d = D -ᵥ H`, the
hypotheses say: `⟪a, b⟫ = ⟪a, c⟫ = ⟪b, c⟫` (altitudes concur at `H`),
`d` is orthogonal to `a`, `b`, `c` (`DH` is perpendicular to the plane), and
`⟪b - d, c - d⟫ = 0` (the right angle at `D`).  It follows that
`⟪a, b⟫ = -‖d‖²`, whence `‖a - b‖² = ‖a‖² + ‖b‖² + 2‖d‖²` etc., so
`AB² + BC² + CA² = 2(AD² + BD² + CD²)`, and Cauchy–Schwarz finishes the job.
Equality holds iff `AB = BC = CA`, i.e. iff `ABC` is equilateral.
-/

/-- The orthocenter `H` of a triangle satisfies `⟪H -ᵥ Pᵢ, Pⱼ -ᵥ Pₖ⟫ = 0`:
the line through a vertex and `H` (the altitude) is orthogonal to the
opposite side. -/
lemma orthocenter_inner (t : Triangle ℝ P) {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) :
    ⟪Triangle.orthocenter t -ᵥ t.points i, t.points j -ᵥ t.points k⟫ = 0 := by
  have hH : Triangle.orthocenter t ∈ t.altitude i := t.orthocenter_mem_altitude
  have hA : t.points i ∈ t.altitude i := t.mem_altitude i
  have hv : Triangle.orthocenter t -ᵥ t.points i ∈ (t.altitude i).direction :=
    AffineSubspace.vsub_mem_direction hH hA
  rw [Simplex.direction_altitude] at hv
  obtain ⟨hv1, -⟩ := Submodule.mem_inf.mp hv
  have hj : t.points j ∈ t.points '' ({i}ᶜ : Set (Fin 3)) :=
    ⟨j, by simpa using hij.symm, rfl⟩
  have hk : t.points k ∈ t.points '' ({i}ᶜ : Set (Fin 3)) :=
    ⟨k, by simpa using hik.symm, rfl⟩
  have hjk : t.points j -ᵥ t.points k ∈ vectorSpan ℝ (t.points '' ({i}ᶜ : Set (Fin 3))) :=
    vsub_mem_vectorSpan ℝ hj hk
  exact Submodule.inner_left_of_mem_orthogonal hjk hv1

/-- If the orthogonal projection of `D` onto the plane of `t` is the
orthocenter `H`, then `D -ᵥ H` is orthogonal to every `X -ᵥ H` with `X` in
the plane. -/
lemma foot_inner (t : Triangle ℝ P) {D : P}
    (hfoot : (orthogonalProjection (affineSpan ℝ (Set.range t.points)) D : P) =
      Triangle.orthocenter t)
    {X : P} (hX : X ∈ affineSpan ℝ (Set.range t.points)) :
    ⟪D -ᵥ Triangle.orthocenter t, X -ᵥ Triangle.orthocenter t⟫ = 0 := by
  have hd : D -ᵥ Triangle.orthocenter t ∈
      (affineSpan ℝ (Set.range t.points)).directionᗮ := by
    rw [← hfoot]
    exact vsub_orthogonalProjection_mem_direction_orthogonal _ D
  have hX2 : X -ᵥ Triangle.orthocenter t ∈
      (affineSpan ℝ (Set.range t.points)).direction :=
    AffineSubspace.vsub_mem_direction hX t.orthocenter_mem_affineSpan
  exact Submodule.inner_left_of_mem_orthogonal hX2 hd

/-- Cauchy–Schwarz for three real numbers, with the equality condition. -/
lemma cs_three (x y z : ℝ) :
    (x + y + z) ^ 2 ≤ 3 * (x ^ 2 + y ^ 2 + z ^ 2) ∧
    ((x + y + z) ^ 2 = 3 * (x ^ 2 + y ^ 2 + z ^ 2) ↔ x = y ∧ y = z) := by
  have hring : 3 * (x ^ 2 + y ^ 2 + z ^ 2) - (x + y + z) ^ 2 =
      (x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2 := by ring
  constructor
  · nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
  · constructor
    · intro heq
      have h0 : (x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2 = 0 := by linarith
      obtain ⟨h2, -⟩ := (add_eq_zero_iff_of_nonneg
        (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)).mp h0
      obtain ⟨h4, h5⟩ := (add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _)).mp h2
      exact ⟨sub_eq_zero.mp (sq_eq_zero_iff.mp h4), sub_eq_zero.mp (sq_eq_zero_iff.mp h5)⟩
    · rintro ⟨rfl, rfl⟩
      ring

/-- The vector form of the inequality: under the given orthogonality
hypotheses, `(‖a-b‖ + ‖b-c‖ + ‖c-a‖)² ≤ 6 (‖a-d‖² + ‖b-d‖² + ‖c-d‖²)`,
with equality iff `‖a-b‖ = ‖b-c‖ = ‖c-a‖`. -/
lemma main_vector {a b c d : V}
    (hab : ⟪a, b⟫ = ⟪a, c⟫) (hbc : ⟪b, a⟫ = ⟪b, c⟫)
    (hda : ⟪d, a⟫ = 0) (hdb : ⟪d, b⟫ = 0) (hdc : ⟪d, c⟫ = 0)
    (hbdc : ⟪b - d, c - d⟫ = 0) :
    (‖a - b‖ + ‖b - c‖ + ‖c - a‖) ^ 2 ≤
      6 * (‖a - d‖ ^ 2 + ‖b - d‖ ^ 2 + ‖c - d‖ ^ 2) ∧
    ((‖a - b‖ + ‖b - c‖ + ‖c - a‖) ^ 2 =
      6 * (‖a - d‖ ^ 2 + ‖b - d‖ ^ 2 + ‖c - d‖ ^ 2) ↔
      ‖a - b‖ = ‖b - c‖ ∧ ‖b - c‖ = ‖c - a‖) := by
  have hbdc' : ⟪b, c⟫ = ⟪a, b⟫ := by rw [← hbc, real_inner_comm]
  have had : ⟪a, d⟫ = 0 := by rw [real_inner_comm]; exact hda
  have hbd : ⟪b, d⟫ = 0 := by rw [real_inner_comm]; exact hdb
  have hcd : ⟪c, d⟫ = 0 := by rw [real_inner_comm]; exact hdc
  have hexpand : ⟪b - d, c - d⟫ = ⟪b, c⟫ - ⟪b, d⟫ - (⟪d, c⟫ - ⟪d, d⟫) := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right]
  have hd2 : ⟪d, d⟫ = ‖d‖ ^ 2 := real_inner_self_eq_norm_sq d
  -- The key relation: `⟪a, b⟫ = -‖d‖²` (and the same for the other pairs).
  have hab' : ⟪a, b⟫ = -‖d‖ ^ 2 := by linarith [hbdc, hbdc', hbd, hdc, hexpand, hd2]
  have hbc' : ⟪b, c⟫ = -‖d‖ ^ 2 := by linarith [hbdc', hab']
  have hca' : ⟪c, a⟫ = -‖d‖ ^ 2 := by
    have h1 : ⟪a, c⟫ = -‖d‖ ^ 2 := by linarith [hab, hab']
    have h2 : ⟪c, a⟫ = ⟪a, c⟫ := real_inner_comm a c
    linarith
  -- Expand all six squared distances.
  have sq1 : ‖a - b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 + 2 * ‖d‖ ^ 2 := by
    rw [norm_sub_sq_real]; linarith [hab']
  have sq2 : ‖b - c‖ ^ 2 = ‖b‖ ^ 2 + ‖c‖ ^ 2 + 2 * ‖d‖ ^ 2 := by
    rw [norm_sub_sq_real]; linarith [hbc']
  have sq3 : ‖c - a‖ ^ 2 = ‖c‖ ^ 2 + ‖a‖ ^ 2 + 2 * ‖d‖ ^ 2 := by
    rw [norm_sub_sq_real]; linarith [hca']
  have sd1 : ‖a - d‖ ^ 2 = ‖a‖ ^ 2 + ‖d‖ ^ 2 := by
    rw [norm_sub_sq_real]; linarith [had]
  have sd2 : ‖b - d‖ ^ 2 = ‖b‖ ^ 2 + ‖d‖ ^ 2 := by
    rw [norm_sub_sq_real]; linarith [hbd]
  have sd3 : ‖c - d‖ ^ 2 = ‖c‖ ^ 2 + ‖d‖ ^ 2 := by
    rw [norm_sub_sq_real]; linarith [hcd]
  have hsum : ‖a - b‖ ^ 2 + ‖b - c‖ ^ 2 + ‖c - a‖ ^ 2 =
      2 * (‖a - d‖ ^ 2 + ‖b - d‖ ^ 2 + ‖c - d‖ ^ 2) := by linarith
  obtain ⟨hCS, hCSeq⟩ := cs_three ‖a - b‖ ‖b - c‖ ‖c - a‖
  rw [hsum] at hCSeq
  refine ⟨by linarith, ?_⟩
  constructor
  · intro heq
    exact hCSeq.mp (by linarith)
  · intro h
    have h' := hCSeq.mpr h
    linarith

/-- The full conclusion, bundled so that both parts of the problem can share
the geometric work. -/
lemma tetrahedron_inequality {A B C D : P} (hABC : AffineIndependent ℝ ![A, B, C])
    (hBDC : ∠ B D C = π / 2)
    (hfoot : (orthogonalProjection
        (affineSpan ℝ (Set.range (⟨_, hABC⟩ : Triangle ℝ P).points)) D : P) =
      Triangle.orthocenter (⟨_, hABC⟩ : Triangle ℝ P)) :
    (dist A B + dist B C + dist C A) ^ 2 ≤
      6 * (dist A D ^ 2 + dist B D ^ 2 + dist C D ^ 2) ∧
    ((dist A B + dist B C + dist C A) ^ 2 =
      6 * (dist A D ^ 2 + dist B D ^ 2 + dist C D ^ 2) ↔
      dist A B = dist B C ∧ dist B C = dist C A) := by
  set t : Triangle ℝ P := ⟨_, hABC⟩ with ht
  -- The right angle at `D`, expressed with inner products.
  have hbdc0 : ⟪B -ᵥ D, C -ᵥ D⟫ = 0 := by
    rwa [EuclideanGeometry.angle,
      ← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two] at hBDC
  -- Inner product relations coming from the altitudes through `A` and `B`.
  have hA0 : ⟪Triangle.orthocenter t -ᵥ A, B -ᵥ C⟫ = 0 :=
    orthocenter_inner t (i := 0) (j := 1) (k := 2) (by decide) (by decide)
  have hB0 : ⟪Triangle.orthocenter t -ᵥ B, A -ᵥ C⟫ = 0 :=
    orthocenter_inner t (i := 1) (j := 0) (k := 2) (by decide) (by decide)
  -- `D -ᵥ H` is orthogonal to `A -ᵥ H`, `B -ᵥ H`, `C -ᵥ H`.
  have hAmem : A ∈ affineSpan ℝ (Set.range t.points) :=
    mem_affineSpan ℝ (Set.mem_range_self (0 : Fin 3))
  have hBmem : B ∈ affineSpan ℝ (Set.range t.points) :=
    mem_affineSpan ℝ (Set.mem_range_self (1 : Fin 3))
  have hCmem : C ∈ affineSpan ℝ (Set.range t.points) :=
    mem_affineSpan ℝ (Set.mem_range_self (2 : Fin 3))
  have hdA : ⟪D -ᵥ Triangle.orthocenter t, A -ᵥ Triangle.orthocenter t⟫ = 0 :=
    foot_inner t hfoot hAmem
  have hdB : ⟪D -ᵥ Triangle.orthocenter t, B -ᵥ Triangle.orthocenter t⟫ = 0 :=
    foot_inner t hfoot hBmem
  have hdC : ⟪D -ᵥ Triangle.orthocenter t, C -ᵥ Triangle.orthocenter t⟫ = 0 :=
    foot_inner t hfoot hCmem
  -- Rewrite everything with respect to `H`.
  have hab : ⟪A -ᵥ Triangle.orthocenter t, B -ᵥ Triangle.orthocenter t⟫ =
      ⟪A -ᵥ Triangle.orthocenter t, C -ᵥ Triangle.orthocenter t⟫ := by
    have h := hA0
    rw [← neg_vsub_eq_vsub_rev A (Triangle.orthocenter t),
      ← vsub_sub_vsub_cancel_right B C (Triangle.orthocenter t)] at h
    rw [inner_neg_left, inner_sub_right] at h
    linarith [h]
  have hbc : ⟪B -ᵥ Triangle.orthocenter t, A -ᵥ Triangle.orthocenter t⟫ =
      ⟪B -ᵥ Triangle.orthocenter t, C -ᵥ Triangle.orthocenter t⟫ := by
    have h := hB0
    rw [← neg_vsub_eq_vsub_rev B (Triangle.orthocenter t),
      ← vsub_sub_vsub_cancel_right A C (Triangle.orthocenter t)] at h
    rw [inner_neg_left, inner_sub_right] at h
    linarith [h]
  have hbdc : ⟪(B -ᵥ Triangle.orthocenter t) - (D -ᵥ Triangle.orthocenter t),
      (C -ᵥ Triangle.orthocenter t) - (D -ᵥ Triangle.orthocenter t)⟫ = 0 := by
    rw [vsub_sub_vsub_cancel_right B D (Triangle.orthocenter t),
      vsub_sub_vsub_cancel_right C D (Triangle.orthocenter t)]
    exact hbdc0
  obtain ⟨hineq, heq⟩ := main_vector hab hbc hdA hdB hdC hbdc
  -- Convert the vector equalities back to distances.
  have dAB : dist A B =
      ‖(A -ᵥ Triangle.orthocenter t) - (B -ᵥ Triangle.orthocenter t)‖ := by
    rw [dist_eq_norm_vsub V, vsub_sub_vsub_cancel_right]
  have dBC : dist B C =
      ‖(B -ᵥ Triangle.orthocenter t) - (C -ᵥ Triangle.orthocenter t)‖ := by
    rw [dist_eq_norm_vsub V, vsub_sub_vsub_cancel_right]
  have dCA : dist C A =
      ‖(C -ᵥ Triangle.orthocenter t) - (A -ᵥ Triangle.orthocenter t)‖ := by
    rw [dist_eq_norm_vsub V, vsub_sub_vsub_cancel_right]
  have dAD : dist A D =
      ‖(A -ᵥ Triangle.orthocenter t) - (D -ᵥ Triangle.orthocenter t)‖ := by
    rw [dist_eq_norm_vsub V, vsub_sub_vsub_cancel_right]
  have dBD : dist B D =
      ‖(B -ᵥ Triangle.orthocenter t) - (D -ᵥ Triangle.orthocenter t)‖ := by
    rw [dist_eq_norm_vsub V, vsub_sub_vsub_cancel_right]
  have dCD : dist C D =
      ‖(C -ᵥ Triangle.orthocenter t) - (D -ᵥ Triangle.orthocenter t)‖ := by
    rw [dist_eq_norm_vsub V, vsub_sub_vsub_cancel_right]
  rw [dAB, dBC, dCA, dAD, dBD, dCD]
  exact ⟨hineq, heq⟩

snip end

problem imo1970_p5a {A B C D : P} (hABC : AffineIndependent ℝ ![A, B, C])
    (hBDC : ∠ B D C = π / 2)
    (hfoot : (orthogonalProjection
        (affineSpan ℝ (Set.range (⟨_, hABC⟩ : Triangle ℝ P).points)) D : P) =
      Triangle.orthocenter (⟨_, hABC⟩ : Triangle ℝ P)) :
    (dist A B + dist B C + dist C A) ^ 2 ≤
      6 * (dist A D ^ 2 + dist B D ^ 2 + dist C D ^ 2) :=
  (tetrahedron_inequality hABC hBDC hfoot).1

problem imo1970_p5b {A B C D : P} (hABC : AffineIndependent ℝ ![A, B, C])
    (hBDC : ∠ B D C = π / 2)
    (hfoot : (orthogonalProjection
        (affineSpan ℝ (Set.range (⟨_, hABC⟩ : Triangle ℝ P).points)) D : P) =
      Triangle.orthocenter (⟨_, hABC⟩ : Triangle ℝ P)) :
    (dist A B + dist B C + dist C A) ^ 2 =
      6 * (dist A D ^ 2 + dist B D ^ 2 + dist C D ^ 2) ↔
      dist A B = dist B C ∧ dist B C = dist C A :=
  (tetrahedron_inequality hABC hBDC hfoot).2

end Imo1970P5
