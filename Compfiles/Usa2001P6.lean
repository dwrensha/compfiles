/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Euclidean.Incenter
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# USA Mathematical Olympiad 2001, Problem 6

Each point in the plane is assigned a real number. Suppose that for any
nondegenerate triangle, the number at its incenter is the arithmetic mean
of the three numbers at its vertices. Prove that all points in the plane
were assigned the same number.
-/

open Affine
open scoped RealInnerProductSpace

namespace Usa2001P6

snip begin

/-- The Gram determinant of the two edge vectors at a common vertex is symmetric in the
two edges: `‖v - u‖²·‖u‖² - ⟪v - u, u⟫² = ‖v‖²·‖u‖² - ⟪v, u⟫²`. -/
private theorem gram_switch {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (u v : V) :
    ‖v - u‖ ^ 2 * ‖u‖ ^ 2 - ⟪v - u, u⟫ ^ 2 = ‖v‖ ^ 2 * ‖u‖ ^ 2 - ⟪v, u⟫ ^ 2 := by
  have h1 : ⟪v - u, v - u⟫ = ⟪v, v⟫ - 2 * ⟪u, v⟫ + ⟪u, u⟫ := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right, real_inner_comm v u]
    ring
  have h2 : ⟪v - u, u⟫ = ⟪v, u⟫ - ⟪u, u⟫ := by
    rw [inner_sub_left]
  rw [← real_inner_self_eq_norm_sq (v - u), ← real_inner_self_eq_norm_sq u,
    ← real_inner_self_eq_norm_sq v, h1, h2, real_inner_comm u v]
  ring

/-- If `F` lies in the affine span of `{B, C}` and `A -ᵥ F` is orthogonal to its direction
(so `F` is the foot of the perpendicular from `A` to the line through `B` and `C`), then
`(dist A F * dist B C)²` equals the Gram determinant
`dist B C² * dist A B² - ⟪C -ᵥ B, A -ᵥ B⟫²`. -/
private theorem dist_foot_mul_sq {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] (A B C F : P)
    (hF : F ∈ affineSpan ℝ ({B, C} : Set P))
    (horth : A -ᵥ F ∈ (affineSpan ℝ ({B, C} : Set P)).directionᗮ) :
    (dist A F * dist B C) ^ 2 = dist B C ^ 2 * dist A B ^ 2 - ⟪C -ᵥ B, A -ᵥ B⟫ ^ 2 := by
  have hB : B ∈ affineSpan ℝ ({B, C} : Set P) :=
    mem_affineSpan ℝ (Set.mem_insert B {C})
  have hC : C ∈ affineSpan ℝ ({B, C} : Set P) := mem_affineSpan ℝ (by simp)
  have hu_mem : C -ᵥ B ∈ (affineSpan ℝ ({B, C} : Set P)).direction := by
    rw [direction_affineSpan]
    exact vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan hC hB
  have h0 : ⟪C -ᵥ B, A -ᵥ F⟫ = 0 := Submodule.inner_right_of_mem_orthogonal hu_mem horth
  have h0' : ⟪A -ᵥ F, C -ᵥ B⟫ = 0 := Submodule.inner_left_of_mem_orthogonal hu_mem horth
  have hFB : F -ᵥ B ∈ vectorSpan ℝ ({B, C} : Set P) :=
    vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan hF hB
  rw [Set.pair_comm B C] at hFB
  rcases mem_vectorSpan_pair.mp hFB with ⟨t, ht⟩
  have e1 : ⟪C -ᵥ B, A -ᵥ B⟫ = t * ⟪C -ᵥ B, C -ᵥ B⟫ := by
    have hdecomp : A -ᵥ B = (A -ᵥ F) + t • (C -ᵥ B) := by
      rw [ht]
      exact (vsub_add_vsub_cancel A F B).symm
    rw [hdecomp, inner_add_right, h0, zero_add, real_inner_smul_right]
  have hz : ⟪A -ᵥ F, F -ᵥ B⟫ = 0 := by
    rw [← ht, real_inner_smul_right, h0', mul_zero]
  have e2 : ‖A -ᵥ B‖ ^ 2 = ‖A -ᵥ F‖ ^ 2 + ‖F -ᵥ B‖ ^ 2 := by
    have h2 := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (A -ᵥ F) (F -ᵥ B) hz
    rw [vsub_add_vsub_cancel A F B] at h2
    simp only [pow_two]
    exact h2
  have hn : ‖B -ᵥ C‖ = ‖C -ᵥ B‖ := by
    rw [← neg_vsub_eq_vsub_rev B C, norm_neg]
  simp only [dist_eq_norm_vsub]
  rw [hn, e2, ← ht, norm_smul, mul_pow, Real.norm_eq_abs, mul_pow, sq_abs, e1,
    real_inner_self_eq_norm_sq (C -ᵥ B)]
  ring

/-- The altitude foot of a vertex of a triangle is the orthogonal projection of the vertex
onto the affine span of the other two vertices. -/
private theorem altitudeFoot_eq_orthogonalProjection {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    (s : Affine.Simplex ℝ P 2) (i : Fin 3) {B C : P}
    (h : s.points '' {i}ᶜ = ({B, C} : Set P)) :
    s.altitudeFoot i =
      EuclideanGeometry.orthogonalProjection (affineSpan ℝ ({B, C} : Set P)) (s.points i) := by
  rw [Affine.Simplex.altitudeFoot, Affine.Simplex.orthogonalProjectionSpan]
  exact EuclideanGeometry.orthogonalProjection_congr
    (by rw [Affine.Simplex.range_faceOpposite_points, h]) rfl

/-- "Base times height", squared, at vertex `i` of a triangle whose opposite side is `BC`,
expressed as a Gram determinant. -/
private theorem height_mul_base_sq {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] (s : Affine.Simplex ℝ P 2) (i : Fin 3) {B C : P}
    (h : s.points '' {i}ᶜ = ({B, C} : Set P)) :
    (s.height i * dist B C) ^ 2 =
      dist B C ^ 2 * dist (s.points i) B ^ 2 - ⟪C -ᵥ B, s.points i -ᵥ B⟫ ^ 2 := by
  rw [Affine.Simplex.height, altitudeFoot_eq_orthogonalProjection s i h]
  exact dist_foot_mul_sq (s.points i) B C _
    (EuclideanGeometry.orthogonalProjection_mem _)
    (EuclideanGeometry.vsub_orthogonalProjection_mem_direction_orthogonal _ _)

/-- The Gram determinant in point form does not depend on the chosen base vertex
(both sides equal `4` times the squared area of the triangle). -/
private theorem gram_point_symm {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] (A B C : P) :
    dist B C ^ 2 * dist A B ^ 2 - ⟪C -ᵥ B, A -ᵥ B⟫ ^ 2 =
      dist A C ^ 2 * dist B A ^ 2 - ⟪C -ᵥ A, B -ᵥ A⟫ ^ 2 := by
  have hn1 : ‖B -ᵥ C‖ = ‖C -ᵥ B‖ := by
    rw [← neg_vsub_eq_vsub_rev B C, norm_neg]
  have hn2 : ‖A -ᵥ C‖ = ‖C -ᵥ A‖ := by
    rw [← neg_vsub_eq_vsub_rev A C, norm_neg]
  have eCB : C -ᵥ B = (C -ᵥ A) - (B -ᵥ A) := (vsub_sub_vsub_cancel_right C B A).symm
  have eAB : A -ᵥ B = -(B -ᵥ A) := (neg_vsub_eq_vsub_rev B A).symm
  simp only [dist_eq_norm_vsub]
  rw [hn1, hn2, eCB, eAB, norm_neg, inner_neg_right, neg_sq]
  exact gram_switch (B -ᵥ A) (C -ᵥ A)

theorem Simplex.incenter_triangle_eq_affineCombination {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    (p₀ p₁ p₂ : P) (h : AffineIndependent ℝ ![p₀, p₁, p₂]) :
    (⟨![p₀, p₁, p₂], h⟩ : Affine.Triangle ℝ P).incenter =
      Finset.univ.affineCombination ℝ ![p₀, p₁, p₂]
        ![dist p₁ p₂ / (dist p₁ p₂ + dist p₂ p₀ + dist p₀ p₁),
          dist p₂ p₀ / (dist p₁ p₂ + dist p₂ p₀ + dist p₀ p₁),
          dist p₀ p₁ / (dist p₁ p₂ + dist p₂ p₀ + dist p₀ p₁)] := by
  set s : Affine.Triangle ℝ P := ⟨![p₀, p₁, p₂], h⟩ with hs
  rw [Affine.Simplex.incenter_eq_affineCombination]
  -- The three side lengths are positive, as the points are pairwise distinct.
  have hinj := h.injective
  have ha : 0 < dist p₁ p₂ := dist_pos.mpr (hinj.ne (by decide : (1 : Fin 3) ≠ 2))
  have hb : 0 < dist p₂ p₀ := dist_pos.mpr (hinj.ne (by decide : (2 : Fin 3) ≠ 0))
  have hc : 0 < dist p₀ p₁ := dist_pos.mpr (hinj.ne (by decide : (0 : Fin 3) ≠ 1))
  -- The point sets of the faces opposite to each vertex.
  have him0 : s.points '' {0}ᶜ = ({s.points 1, s.points 2} : Set P) := by
    rw [(by grind : ({0}ᶜ : Set (Fin 3)) = {1, 2}), Set.image_insert_eq, Set.image_singleton]
  have him1 : s.points '' {1}ᶜ = ({s.points 0, s.points 2} : Set P) := by
    rw [(by grind : ({1}ᶜ : Set (Fin 3)) = {0, 2}), Set.image_insert_eq, Set.image_singleton]
  have him2 : s.points '' {2}ᶜ = ({s.points 0, s.points 1} : Set P) := by
    rw [(by grind : ({2}ᶜ : Set (Fin 3)) = {0, 1}), Set.image_insert_eq, Set.image_singleton]
  -- "Base times height", squared, at each vertex, as a Gram determinant.
  have hsq0 : (s.height 0 * dist p₁ p₂) ^ 2 =
      dist p₁ p₂ ^ 2 * dist p₀ p₁ ^ 2 - ⟪p₂ -ᵥ p₁, p₀ -ᵥ p₁⟫ ^ 2 :=
    height_mul_base_sq s 0 him0
  have hsq1 : (s.height 1 * dist p₀ p₂) ^ 2 =
      dist p₀ p₂ ^ 2 * dist p₁ p₀ ^ 2 - ⟪p₂ -ᵥ p₀, p₁ -ᵥ p₀⟫ ^ 2 :=
    height_mul_base_sq s 1 him1
  have hsq2 : (s.height 2 * dist p₀ p₁) ^ 2 =
      dist p₀ p₁ ^ 2 * dist p₂ p₀ ^ 2 - ⟪p₁ -ᵥ p₀, p₂ -ᵥ p₀⟫ ^ 2 :=
    height_mul_base_sq s 2 him2
  -- The Gram determinants agree, hence so do the squared "base times height" quantities.
  have g12 : dist p₀ p₂ ^ 2 * dist p₁ p₀ ^ 2 - ⟪p₂ -ᵥ p₀, p₁ -ᵥ p₀⟫ ^ 2 =
      dist p₀ p₁ ^ 2 * dist p₂ p₀ ^ 2 - ⟪p₁ -ᵥ p₀, p₂ -ᵥ p₀⟫ ^ 2 := by
    rw [dist_comm p₁ p₀, dist_comm p₀ p₂, real_inner_comm (p₂ -ᵥ p₀) (p₁ -ᵥ p₀)]
    ring
  have hsql : (s.height 0 * dist p₁ p₂) ^ 2 = (s.height 1 * dist p₂ p₀) ^ 2 := by
    rw [hsq0, gram_point_symm p₀ p₁ p₂, ← hsq1, dist_comm p₂ p₀]
  have hsqr : (s.height 1 * dist p₂ p₀) ^ 2 = (s.height 2 * dist p₀ p₁) ^ 2 := by
    rw [dist_comm p₂ p₀, hsq1, g12, ← hsq2]
  -- Both quantities are nonnegative, so they are already equal.
  have key1 : s.height 0 * dist p₁ p₂ = s.height 1 * dist p₂ p₀ :=
    (sq_eq_sq₀ (by positivity) (by positivity)).mp hsql
  have key2 : s.height 1 * dist p₂ p₀ = s.height 2 * dist p₀ p₁ :=
    (sq_eq_sq₀ (by positivity) (by positivity)).mp hsqr
  -- Express all heights as multiples of `s.height 0`.
  have hh1 : s.height 1 = s.height 0 * dist p₁ p₂ / dist p₂ p₀ := by
    rw [eq_div_iff_mul_eq (ne_of_gt hb)]
    exact key1.symm
  have hh2 : s.height 2 = s.height 0 * dist p₁ p₂ / dist p₀ p₁ := by
    rw [eq_div_iff_mul_eq (ne_of_gt hc)]
    exact (key1.trans key2).symm
  have H0 : s.height 0 ≠ 0 := ne_of_gt (s.height_pos 0)
  have a0 : dist p₁ p₂ ≠ 0 := ne_of_gt ha
  have b0 : dist p₂ p₀ ≠ 0 := ne_of_gt hb
  have c0 : dist p₀ p₁ ≠ 0 := ne_of_gt hc
  have s0 : dist p₁ p₂ + dist p₂ p₀ + dist p₀ p₁ ≠ 0 := ne_of_gt (by positivity)
  -- The incenter weights: normalization of the inverse heights.
  have hsum3 : (∑ x, (s.height x)⁻¹) = (s.height 0)⁻¹ + ((s.height 1)⁻¹ + (s.height 2)⁻¹) := by
    simp only [Fin.sum_univ_succ, Fin.succ_zero_eq_one', Fin.succ_one_eq_two', Fin.sum_univ_zero,
      add_zero]
  have w0 : s.excenterWeights ∅ 0 = dist p₁ p₂ / (dist p₁ p₂ + dist p₂ p₀ + dist p₀ p₁) := by
    simp only [Affine.Simplex.excenterWeights, Pi.smul_apply, smul_eq_mul,
      Affine.Simplex.excenterWeightsUnnorm_empty_apply]
    rw [hsum3, hh1, hh2]
    field_simp
    ring
  have w1 : s.excenterWeights ∅ 1 = dist p₂ p₀ / (dist p₁ p₂ + dist p₂ p₀ + dist p₀ p₁) := by
    simp only [Affine.Simplex.excenterWeights, Pi.smul_apply, smul_eq_mul,
      Affine.Simplex.excenterWeightsUnnorm_empty_apply]
    rw [hsum3, hh1, hh2]
    field_simp
    ring
  have w2 : s.excenterWeights ∅ 2 = dist p₀ p₁ / (dist p₁ p₂ + dist p₂ p₀ + dist p₀ p₁) := by
    simp only [Affine.Simplex.excenterWeights, Pi.smul_apply, smul_eq_mul,
      Affine.Simplex.excenterWeightsUnnorm_empty_apply]
    rw [hsum3, hh1, hh2]
    field_simp
    ring
  -- Comparing the two affine combinations weight by weight.
  apply Finset.affineCombination_congr
  · intro i _
    fin_cases i
    · simpa using w0
    · simpa using w1
    · simpa using w2
  · intro i _
    rfl

/-- Rotation by 60 degrees (counterclockwise), as an explicit matrix. -/
noncomputable def rot : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) where
  toFun v := WithLp.toLp 2 ![ (v 0 - Real.sqrt 3 * v 1) / 2, (Real.sqrt 3 * v 0 + v 1) / 2 ]
  map_add' := by
    intro x y
    ext i
    fin_cases i <;> simp [PiLp.add_apply] <;> ring
  map_smul' := by
    intro r x
    ext i
    fin_cases i <;> simp [PiLp.smul_apply] <;> ring

lemma rot_apply (v : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) :
    rot v i = ![ (v 0 - Real.sqrt 3 * v 1) / 2, (Real.sqrt 3 * v 0 + v 1) / 2 ] i := by
  simp [rot, PiLp.toLp_apply]

lemma rot_rot (v : EuclideanSpace ℝ (Fin 2)) : rot (rot v) = rot v - v := by
  ext i
  fin_cases i <;>
    simp [rot_apply, PiLp.sub_apply, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
    ring_nf <;>
    rw [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)] <;>
    ring

lemma inner_rot (v : EuclideanSpace ℝ (Fin 2)) : ⟪v, rot v⟫ = ‖v‖ ^ 2 / 2 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.real_norm_sq_eq]
  simp [dotProduct, Fin.sum_univ_two, rot_apply, Fin.isValue]
  ring

lemma norm_rot (v : EuclideanSpace ℝ (Fin 2)) : ‖rot v‖ = ‖v‖ := by
  have h : ‖rot v‖ ^ 2 = ‖v‖ ^ 2 := by
    simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, rot_apply, Fin.isValue]
    ring_nf
    rw [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)]
    ring
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

lemma norm_eq_of_inner {x : EuclideanSpace ℝ (Fin 2)} {r : ℝ} (hr : 0 ≤ r)
    (h : ⟪x, x⟫ = r ^ 2) : ‖x‖ = r := by
  have h2 : ‖x‖ ^ 2 = r ^ 2 := by rw [← real_inner_self_eq_norm_sq]; exact h
  exact (pow_left_inj₀ (norm_nonneg _) hr two_ne_zero).mp h2

lemma norm_sub_rot (v : EuclideanSpace ℝ (Fin 2)) : ‖v - rot v‖ = ‖v‖ := by
  apply norm_eq_of_inner (norm_nonneg _)
  rw [inner_sub_left, inner_sub_right, inner_sub_right, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq, norm_rot, real_inner_comm v (rot v), inner_rot]
  ring

lemma norm_add_rot (v : EuclideanSpace ℝ (Fin 2)) : ‖v + rot v‖ = Real.sqrt 3 * ‖v‖ := by
  apply norm_eq_of_inner (by positivity)
  rw [mul_pow, Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)]
  rw [inner_add_left, inner_add_right, inner_add_right, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq, norm_rot, real_inner_comm v (rot v), inner_rot]
  ring

lemma norm_two_rot_sub (v : EuclideanSpace ℝ (Fin 2)) :
    ‖(2:ℝ) • rot v - v‖ = Real.sqrt 3 * ‖v‖ := by
  apply norm_eq_of_inner (by positivity)
  rw [mul_pow, Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)]
  rw [inner_sub_left, inner_sub_right, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, norm_rot,
    real_inner_comm v (rot v), inner_rot]
  ring

lemma rot_eq_zero_iff {v : EuclideanSpace ℝ (Fin 2)} : rot v = 0 ↔ v = 0 := by
  constructor
  · intro h
    rw [← norm_eq_zero, ← norm_rot, h, norm_zero]
  · intro h
    rw [h, map_zero]

lemma rot_ne_smul (v : EuclideanSpace ℝ (Fin 2)) (hv : v ≠ 0) (c : ℝ)
    (h : rot v = c • v) : False := by
  have hnv : (0:ℝ) < ‖v‖ := norm_pos_iff.mpr hv
  have h1 : ⟪v, rot v⟫ = c * ‖v‖ ^ 2 := by
    rw [h, real_inner_smul_right, real_inner_self_eq_norm_sq]
  rw [inner_rot] at h1
  have h2 : ‖rot v‖ = |c| * ‖v‖ := by rw [h, norm_smul, Real.norm_eq_abs]
  rw [norm_rot] at h2
  have hsq : (0:ℝ) < ‖v‖ ^ 2 := pow_pos hnv _
  have hc : c = 1 / 2 := by
    have h3 : (c - 1/2) * ‖v‖ ^ 2 = 0 := by linarith [h1]
    rcases mul_eq_zero.mp h3 with h4 | h4
    · linarith
    · exact absurd h4 (ne_of_gt hsq)
  rw [hc, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)] at h2
  linarith [h2, hnv]

lemma affineCombination_eq_sum_smul {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (p : ι → EuclideanSpace ℝ (Fin 2)) (h : ∑ i ∈ s, w i = 1) :
    s.affineCombination ℝ p w = ∑ i ∈ s, w i • p i := by
  rw [Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one s w p h 0,
    Finset.weightedVSubOfPoint_apply]
  simp [vsub_eq_sub, vadd_eq_add]

/-- The key non-degeneracy fact: a scaled copy of `v` and a non-trivial combination of
`rot v` and `v` are linearly independent. -/
lemma indep_pair (v : EuclideanSpace ℝ (Fin 2)) (hv : v ≠ 0) {a b : ℝ} (ha : a ≠ 0)
    (hb : b ≠ 0) (c : ℝ) :
    LinearIndependent ℝ ![a • v, b • rot v + c • v] := by
  have h1 : a • v ≠ 0 := smul_ne_zero ha hv
  rw [LinearIndependent.pair_iff' h1]
  intro k h
  have e1 : k • a • v - c • v = b • rot v := sub_eq_iff_eq_add'.mpr (h.trans (add_comm _ _))
  have hb' : b • rot v = (k * a - c) • v := by
    rw [← e1]; module
  have hrot : rot v = (b⁻¹ * (k * a - c)) • v := by
    have e : rot v = b⁻¹ • (b • rot v) := by rw [smul_smul, inv_mul_cancel₀ hb, one_smul]
    rw [e, hb', smul_smul]
  exact rot_ne_smul v hv _ hrot

/-- Three points are affinely independent when the two difference vectors from the first
point are linearly independent. -/
lemma aff_indep_of_pair (p₀ p₁ p₂ : EuclideanSpace ℝ (Fin 2))
    (h : LinearIndependent ℝ ![p₁ -ᵥ p₀, p₂ -ᵥ p₀]) :
    AffineIndependent ℝ ![p₀, p₁, p₂] := by
  rw [affineIndependent_iff_linearIndependent_vsub ℝ ![p₀, p₁, p₂] 0,
    ← linearIndependent_equiv (finSuccAboveEquiv (0 : Fin 3))]
  have hcomp : (fun i : {j // j ≠ (0 : Fin 3)} ↦ (![p₀, p₁, p₂] i -ᵥ ![p₀, p₁, p₂] 0 : _)) ∘
      finSuccAboveEquiv 0 = ![p₁ -ᵥ p₀, p₂ -ᵥ p₀] := by
    funext i
    fin_cases i <;>
      simp [Function.comp_apply, finSuccAboveEquiv_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Fin.succ_zero_eq_one,
        Fin.succ_one_eq_two]
  rwa [hcomp]


/-- The key trapezoid relation: if `X`, `Y` are obtained from `W`, `X` by two successive
rotations of the side vector by 60 degrees (so `W X Y Z` are four consecutive vertices of a
regular hexagon), then `f W + f Y = f X + f Z`.  The proof exhibits a point `T` (the
intersection of lines `WX` and `ZY` extended) such that triangles `T W Y` and `T X Z` share
the same incenter, and applies the hypothesis to both. -/
theorem trap (f : EuclideanSpace ℝ (Fin 2) → ℝ)
    (hf : ∀ (A B C : EuclideanSpace ℝ (Fin 2)) (h : AffineIndependent ℝ ![A, B, C]),
      f ((⟨![A, B, C], h⟩ : Affine.Triangle ℝ _).incenter) = (f A + f B + f C) / 3)
    {W X Y Z : EuclideanSpace ℝ (Fin 2)} (hXW : X ≠ W)
    (hY : Y = X + rot (X - W)) (hZ : Z = Y + rot (Y - X)) :
    f W + f Y = f X + f Z := by
  have hv : X - W ≠ 0 := sub_ne_zero.mpr hXW
  set v := X - W with hvdef
  set T := (2:ℝ) • X - W with hTdef
  have hYv : Y = X + rot v := hY
  have hZv : Z = X + (2:ℝ) • rot v - v := by
    rw [hZ, hY]
    have e : X + rot (X - W) - X = rot (X - W) := by module
    rw [e, rot_rot]; module
  -- vector identities
  have hTW : T - W = (2:ℝ) • v := by rw [hTdef, hvdef]; module
  have hTY : T - Y = v - rot v := by rw [hTdef, hYv, hvdef]; module
  have hWY : Y - W = v + rot v := by rw [hYv, hvdef]; module
  have hTX : T - X = v := by rw [hTdef, hvdef]; module
  have hTZ : T - Z = (2:ℝ) • (v - rot v) := by rw [hTdef, hZv, hvdef]; module
  have hXZ : Z - X = (2:ℝ) • rot v - v := by rw [hZv]; module
  -- distances
  have s_pos : (0:ℝ) < ‖v‖ := norm_pos_iff.mpr hv
  have dTW : dist T W = 2 * ‖v‖ := by
    rw [dist_eq_norm, hTW, norm_smul, Real.norm_ofNat]
  have dTY : dist T Y = ‖v‖ := by rw [dist_eq_norm, hTY, norm_sub_rot]
  have dWY : dist W Y = Real.sqrt 3 * ‖v‖ := by
    rw [dist_eq_norm, ← norm_neg, neg_sub, hWY, norm_add_rot]
  have dTX : dist T X = ‖v‖ := by rw [dist_eq_norm, hTX]
  have dTZ : dist T Z = 2 * ‖v‖ := by
    rw [dist_eq_norm, hTZ, norm_smul, norm_sub_rot, Real.norm_ofNat]
  have dXZ : dist X Z = Real.sqrt 3 * ‖v‖ := by
    rw [dist_eq_norm, ← norm_neg, neg_sub, hXZ, norm_two_rot_sub]
  -- non-degeneracy of the two triangles
  have hind1 : AffineIndependent ℝ ![T, W, Y] := by
    apply aff_indep_of_pair
    have h1 : W -ᵥ T = (-2:ℝ) • v := by
      simp only [vsub_eq_sub]; rw [hTdef, hvdef]; module
    have h2 : Y -ᵥ T = (1:ℝ) • rot v + (-1:ℝ) • v := by
      simp only [vsub_eq_sub]; rw [hTdef, hYv, hvdef]; module
    rw [h1, h2]
    exact indep_pair v hv (by norm_num) (by norm_num) (-1:ℝ)
  have hind2 : AffineIndependent ℝ ![T, X, Z] := by
    apply aff_indep_of_pair
    have h1 : X -ᵥ T = (-1:ℝ) • v := by
      simp only [vsub_eq_sub]; rw [hTdef, hvdef]; module
    have h2 : Z -ᵥ T = (2:ℝ) • rot v + (-2:ℝ) • v := by
      simp only [vsub_eq_sub]; rw [hTdef, hZv, hvdef]; module
    rw [h1, h2]
    exact indep_pair v hv (by norm_num) (by norm_num) (-2:ℝ)
  -- the two triangles share the same incenter
  have hinc1 := Simplex.incenter_triangle_eq_affineCombination T W Y hind1
  have hinc2 := Simplex.incenter_triangle_eq_affineCombination T X Z hind2
  have hI : (⟨![T, W, Y], hind1⟩ : Affine.Triangle ℝ _).incenter =
      (⟨![T, X, Z], hind2⟩ : Affine.Triangle ℝ _).incenter := by
    rw [hinc1, hinc2]
    rw [dist_comm Y T, dist_comm Z T, dWY, dTY, dTW, dXZ, dTZ, dTX]
    rw [show Real.sqrt 3 * ‖v‖ + 2 * ‖v‖ + ‖v‖ = Real.sqrt 3 * ‖v‖ + ‖v‖ + 2 * ‖v‖ from by ring]
    have hDne : Real.sqrt 3 * ‖v‖ + ‖v‖ + 2 * ‖v‖ ≠ 0 := by
      have h3 : (0:ℝ) < Real.sqrt 3 := Real.sqrt_pos_of_pos (by norm_num)
      have := s_pos
      positivity
    have hs1 : ∑ i ∈ Finset.univ, (![Real.sqrt 3 * ‖v‖ / (Real.sqrt 3 * ‖v‖ + ‖v‖ + 2 * ‖v‖),
        ‖v‖ / (Real.sqrt 3 * ‖v‖ + ‖v‖ + 2 * ‖v‖),
        2 * ‖v‖ / (Real.sqrt 3 * ‖v‖ + ‖v‖ + 2 * ‖v‖)] : Fin 3 → ℝ) i = 1 := by
      rw [Fin.sum_univ_three]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
        Fin.isValue]
      field_simp [hDne]
    have hs2 : ∑ i ∈ Finset.univ, (![Real.sqrt 3 * ‖v‖ / (Real.sqrt 3 * ‖v‖ + ‖v‖ + 2 * ‖v‖),
        2 * ‖v‖ / (Real.sqrt 3 * ‖v‖ + ‖v‖ + 2 * ‖v‖),
        ‖v‖ / (Real.sqrt 3 * ‖v‖ + ‖v‖ + 2 * ‖v‖)] : Fin 3 → ℝ) i = 1 := by
      rw [Fin.sum_univ_three]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
        Fin.isValue]
      field_simp [hDne]; ring
    rw [affineCombination_eq_sum_smul Finset.univ _ _ hs1,
      affineCombination_eq_sum_smul Finset.univ _ _ hs2]
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Fin.isValue]
    have ef : ∀ (a : ℝ) (p : EuclideanSpace ℝ (Fin 2)),
        (a / (Real.sqrt 3 * ‖v‖ + ‖v‖ + 2 * ‖v‖)) • p =
          (Real.sqrt 3 * ‖v‖ + ‖v‖ + 2 * ‖v‖)⁻¹ • (a • p) := by
      intro a p
      rw [div_eq_mul_inv, mul_comm a _, smul_smul]
    simp only [ef]
    rw [← smul_add, ← smul_add, ← smul_add, ← smul_add]
    have hN : (Real.sqrt 3 * ‖v‖) • T + ‖v‖ • W + (2 * ‖v‖) • Y =
        (Real.sqrt 3 * ‖v‖) • T + (2 * ‖v‖) • X + ‖v‖ • Z := by
      rw [hTdef, hYv, hZv, show W = X - v from by rw [hvdef]; module]
      module
    rw [hN]
  have e1 := hf T W Y hind1
  have e2 := hf T X Z hind2
  rw [hI] at e1
  linarith [e1, e2]


snip end

problem usa2001_p6 (f : EuclideanSpace ℝ (Fin 2) → ℝ)
    (hf : ∀ (A B C : EuclideanSpace ℝ (Fin 2)) (h : AffineIndependent ℝ ![A, B, C]),
      f ((⟨![A, B, C], h⟩ : Affine.Triangle ℝ _).incenter) = (f A + f B + f C) / 3) :
    ∃ c : ℝ, ∀ p : EuclideanSpace ℝ (Fin 2), f p = c := by
  have key : ∀ P Q : EuclideanSpace ℝ (Fin 2), f P = f Q := by
    intro P Q
    by_cases hPQ : P = Q
    · rw [hPQ]
    set A := P with hAdef
    set B := Q with hBdef
    set v := B - A with hvdef
    have hv : v ≠ 0 := sub_ne_zero.mpr (Ne.symm hPQ)
    set C := B + rot v with hCdef
    set D := C + rot (C - B) with hDdef
    set E := D + rot (D - C) with hEdef
    set F := E + rot (E - D) with hFdef
    -- closed forms of the hexagon vertices in terms of A, v, rot v
    have hB : B = A + v := by rw [hvdef]; module
    have hC2 : C = A + v + rot v := by rw [hCdef, hB]
    have hCB : C - B = rot v := by rw [hC2, hB]; module
    have hD2 : D = A + (2:ℝ) • rot v := by rw [hDdef, hCB, rot_rot, hC2]; module
    have hDC : D - C = rot v - v := by rw [hD2, hC2]; module
    have hE2 : E = A + (2:ℝ) • rot v - v := by rw [hEdef, hDC, map_sub, rot_rot, hD2]; module
    have hED : E - D = -v := by rw [hE2, hD2]; module
    have hF2 : F = A + rot v - v := by rw [hFdef, hED, map_neg, hE2]; module
    have hFE : F - E = -rot v := by rw [hF2, hE2]; module
    have hAF : A - F = v - rot v := by rw [hF2]; module
    have hrotFE : rot (F - E) = v - rot v := by rw [hFE, map_neg, rot_rot]; module
    have hrotAF : rot (A - F) = v := by rw [hAF, map_sub, rot_rot]; module
    -- distinctness of consecutive vertices
    have hBA : B ≠ A := Ne.symm hPQ
    have hCB' : C ≠ B := by
      intro h
      have h0 : C - B = 0 := by rw [h, sub_self]
      rw [hCB] at h0
      exact hv (rot_eq_zero_iff.mp h0)
    have hDC' : D ≠ C := by
      intro h
      have h0 : D - C = 0 := by rw [h, sub_self]
      rw [hDC] at h0
      have h1 : rot v = (1:ℝ) • v := by
        have h2 : rot v = v := sub_eq_zero.mp h0
        rw [h2]; module
      exact rot_ne_smul v hv 1 h1
    have hED' : E ≠ D := by
      intro h
      have h0 : E - D = 0 := by rw [h, sub_self]
      rw [hED] at h0
      exact hv (neg_eq_zero.mp h0)
    have hFE' : F ≠ E := by
      intro h
      have h0 : F - E = 0 := by rw [h, sub_self]
      rw [hFE] at h0
      exact hv (rot_eq_zero_iff.mp (neg_eq_zero.mp h0))
    -- the two closure relations
    have hY_A : A = F + rot (F - E) := by rw [hrotFE, hF2]; module
    have hZ_B : B = A + rot (A - F) := by rw [hrotAF, hB]
    -- the six trapezoid relations
    have t1 : f A + f C = f B + f D := trap f hf hBA hCdef hDdef
    have t2 : f B + f D = f C + f E := trap f hf hCB' hDdef hEdef
    have t3 : f C + f E = f D + f F := trap f hf hDC' hEdef hFdef
    have t4 : f D + f F = f E + f A := trap f hf hED' hFdef hY_A
    have t5 : f E + f A = f F + f B := trap f hf hFE' hY_A hZ_B
    linarith [t1, t2, t3, t4, t5]
  exact ⟨f 0, fun p ↦ key p 0⟩


end Usa2001P6
