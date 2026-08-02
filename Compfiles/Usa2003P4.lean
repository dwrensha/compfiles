/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Euclidean.Sphere.Power
public import Mathlib.Tactic.Positivity.Finset
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# USA Mathematical Olympiad 2003, Problem 4

Let ABC be a triangle. A circle passing through A and B intersects segments AC
and BC at D and E, respectively. Lines AB and DE intersect at F, while lines BD
and CF intersect at M. Prove that MF = MC if and only if MB · MD = MC².
-/

namespace Usa2003P4

open scoped EuclideanGeometry
open EuclideanGeometry

snip begin

/-- If the 2-dimensional cross product of `v` and `w` vanishes, then the vectors
are parallel. -/
lemma parallel_of_cross_eq_zero {v0 v1 w0 w1 : ℝ} (h : v0 * w1 = v1 * w0) :
    (v0 = 0 ∧ v1 = 0) ∨ ∃ r : ℝ, w0 = r * v0 ∧ w1 = r * v1 := by
  by_cases hv0 : v0 = 0
  · subst hv0
    simp at h
    rcases h with h | h
    · subst h; exact Or.inl ⟨rfl, rfl⟩
    · by_cases hv1 : v1 = 0
      · subst hv1; exact Or.inl ⟨rfl, rfl⟩
      · refine Or.inr ⟨w1 / v1, by simp [h], ?_⟩
        field_simp
  · refine Or.inr ⟨w0 / v0, by field_simp, ?_⟩
    rw [div_mul_eq_mul_div, eq_div_iff hv0]
    linear_combination h

/-- The cross product `(A - C) × (B - C)` of a non-collinear triple is nonzero. -/
lemma cross_ne_zero_of_not_collinear {A B C : EuclideanSpace ℝ (Fin 2)}
    (h : ¬ Collinear ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2)))) :
    (A 0 - C 0) * (B 1 - C 1) - (A 1 - C 1) * (B 0 - C 0) ≠ 0 := by
  intro hc
  apply h
  have hc' : (A 0 - C 0) * (B 1 - C 1) = (A 1 - C 1) * (B 0 - C 0) := by linarith
  have hcross : (A 0 - C 0) * (B 1 - A 1) = (A 1 - C 1) * (B 0 - A 0) := by
    linear_combination hc'
  rcases parallel_of_cross_eq_zero hcross with ⟨h0, h1⟩ | ⟨r, hr0, hr1⟩
  · rw [collinear_iff_of_mem (show A ∈ ({A, B, C} : Set _) by simp)]
    refine ⟨B -ᵥ A, fun p hp => ?_⟩
    simp at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
    · refine ⟨0, ?_⟩
      ext i; fin_cases i <;> simp at h0 h1 ⊢ <;> linarith
  · have hr : r ≠ 0 := by
      intro hr0'
      subst hr0'
      simp at hr0 hr1
      apply h
      rw [collinear_iff_of_mem (show A ∈ ({A, B, C} : Set _) by simp)]
      refine ⟨C -ᵥ A, fun p hp => ?_⟩
      simp at hp
      rcases hp with rfl | rfl | rfl
      · exact ⟨0, by simp⟩
      · refine ⟨0, ?_⟩
        ext i; fin_cases i <;> simp at hr0 hr1 ⊢ <;> linarith
      · exact ⟨1, by simp⟩
    rw [collinear_iff_of_mem (show A ∈ ({A, B, C} : Set _) by simp)]
    refine ⟨B -ᵥ A, fun p hp => ?_⟩
    simp at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
    · have hvec : A -ᵥ p = r⁻¹ • (B -ᵥ A) := by
        ext i; fin_cases i <;> simp <;> field_simp <;> linarith
      refine ⟨-r⁻¹, ?_⟩
      rw [eq_vadd_iff_vsub_eq, ← neg_vsub_eq_vsub_rev, hvec, neg_smul]

/-- A set containing the endpoints of a segment and a point of the segment is collinear. -/
lemma collinear_of_mem_segment {x y z : EuclideanSpace ℝ (Fin 2)} (h : z ∈ segment ℝ x y) :
    Collinear ℝ ({x, y, z} : Set (EuclideanSpace ℝ (Fin 2))) := by
  obtain ⟨a, b, ha, hb, hab, hz⟩ := h
  rw [collinear_iff_of_mem (show x ∈ ({x, y, z} : Set _) by simp)]
  refine ⟨y -ᵥ x, fun p hp => ?_⟩
  simp at hp
  rcases hp with rfl | rfl | rfl
  · exact ⟨0, by simp⟩
  · exact ⟨1, by simp⟩
  · refine ⟨b, ?_⟩
    rw [← hz]
    ext i; simp
    have : b = 1 - a := by linarith
    rw [this]; ring

/-- Three collinear points in the plane have vanishing cross product. -/
lemma cross_eq_zero_of_collinear {x y z : EuclideanSpace ℝ (Fin 2)}
    (h : Collinear ℝ ({x, y, z} : Set (EuclideanSpace ℝ (Fin 2)))) :
    (x 0 - z 0) * (y 1 - z 1) - (x 1 - z 1) * (y 0 - z 0) = 0 := by
  rw [collinear_iff_of_mem (show z ∈ ({x, y, z} : Set _) by simp)] at h
  obtain ⟨v, hv⟩ := h
  obtain ⟨r1, hr1⟩ := hv x (by simp)
  obtain ⟨r2, hr2⟩ := hv y (by simp)
  have hx0 : x 0 - z 0 = r1 * v 0 := by rw [hr1]; simp
  have hx1 : x 1 - z 1 = r1 * v 1 := by rw [hr1]; simp
  have hy0 : y 0 - z 0 = r2 * v 0 := by rw [hr2]; simp
  have hy1 : y 1 - z 1 = r2 * v 1 := by rw [hr2]; simp
  rw [hx0, hx1, hy0, hy1]; ring

/-- A point of a segment has an explicit parametrization in coordinates. -/
lemma segment_coords {x y z : EuclideanSpace ℝ (Fin 2)} (h : z ∈ segment ℝ x y) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ ∀ i : Fin 2, z i = y i + t * (x i - y i) := by
  obtain ⟨a, b, ha, hb, hab, hz⟩ := h
  refine ⟨a, ha, by linarith, fun i => ?_⟩
  have hDi : z i = a * x i + b * y i := by
    rw [← hz]; simp
  rw [hDi]
  have : b = 1 - a := by linarith
  rw [this]; ring

/-- A point on the line through two distinct points has an explicit parametrization. -/
lemma line_coords {x y z : EuclideanSpace ℝ (Fin 2)}
    (h : Collinear ℝ ({x, y, z} : Set (EuclideanSpace ℝ (Fin 2)))) (hne : x ≠ y) :
    ∃ u : ℝ, ∀ i : Fin 2, z i = x i + u * (y i - x i) := by
  rw [collinear_iff_of_mem (show x ∈ ({x, y, z} : Set _) by simp)] at h
  obtain ⟨v, hv⟩ := h
  obtain ⟨r1, hr1⟩ := hv y (by simp)
  obtain ⟨r2, hr2⟩ := hv z (by simp)
  have hr1ne : r1 ≠ 0 := by
    intro hr0'
    subst hr0'
    simp at hr1
    exact hne hr1.symm
  refine ⟨r2 / r1, fun i => ?_⟩
  have e1 : y i - x i = r1 * v i := by rw [hr1]; simp
  have e2 : z i - x i = r2 * v i := by rw [hr2]; simp
  have e3 : z i - x i = r2 / r1 * (y i - x i) := by
    rw [e2, e1]; field_simp
  linarith [e3]

/-- The squared distance between two points of the plane, in coordinates. -/
lemma dist_sq_coords (x y : EuclideanSpace ℝ (Fin 2)) :
    dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
  rw [dist_eq_norm_vsub, EuclideanSpace.norm_eq]
  rw [Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two, sq_abs]

/-- `P1` vanishes iff `M` is equidistant from `F` and `C` (squared coordinate form). -/
lemma alg_pA (aa ab bb s t w : ℝ) :
    w * (w - 1) * (t ^ 2 * aa - 2 * t * ab + bb) -
      ((w * t) ^ 2 * aa + 2 * w * t * (1 - w) * ab + (1 - w) ^ 2 * bb) =
    bb * (w * (1 - s * t) - 1) - w * t * (t * aa - s * bb) := by ring

lemma alg_pB (s t u w : ℝ) :
    (s - t) * (1 - u * (1 - t)) * (w * (1 - s * t) - 1) =
    (s - t) * (1 - s * t) * (w * t * u - (1 - w) * (1 - u)) - t * s * (s * t - 2 * t + 1) -
      t * (1 - s) * (u * (s - t) - s * (1 - t)) := by ring

lemma alg_pC (t u w : ℝ) :
    w * (w - 1) * (1 - u + u * t) ^ 2 =
    u * t * (u - 1) + (w * t * u - (1 - w) * (1 - u)) *
      ((w * t * u - (1 - w) * (1 - u)) + 1 - u - u * t) := by ring

/-- The master syzygy for the `P1` side. -/
lemma alg_key (aa ab bb s t u w : ℝ)
    (hR0 : t * aa = s * bb) (hR1 : u * (s - t) = s * (1 - t))
    (hR2 : w * t * u = (1 - w) * (1 - u)) :
    t * (s - t) ^ 3 * (1 - u + u * t) *
      ((1 - u) ^ 2 * aa + 2 * u * (1 - u) * ab + u ^ 2 * bb -
        2 * (w * t * (1 - u) * aa + (w * t * u + (1 - w) * (1 - u)) * ab +
          (1 - w) * u * bb)) =
    (ab * (-2 * s ^ 2 * t * u ^ 3 + 6 * s ^ 2 * t * u ^ 2 - 4 * s ^ 2 * t * u + 2 * s ^ 2 * u ^ 3 -
        4 * s ^ 2 * u ^ 2 + 2 * s ^ 2 * u + 6 * s * t ^ 2 * u ^ 3 - 18 * s * t ^ 2 * u ^ 2 +
        12 * s * t ^ 2 * u - 10 * s * t * u ^ 3 + 24 * s * t * u ^ 2 - 14 * s * t * u + 6 * s * u ^ 3 -
        12 * s * u ^ 2 + 6 * s * u + 2 * t ^ 4 * u ^ 2 - 2 * t ^ 4 * u - 4 * t ^ 3 * u ^ 3 +
        4 * t ^ 3 * u ^ 2 + 8 * t ^ 2 * u ^ 3 - 8 * t ^ 2 * u ^ 2 - 6 * t * u ^ 3 + 6 * t * u ^ 2) +
      bb * (s ^ 3 * u ^ 3 - 3 * s ^ 3 * u ^ 2 + 3 * s ^ 3 * u - s ^ 3 - 2 * s ^ 2 * t * u ^ 3 +
        10 * s ^ 2 * t * u ^ 2 - 15 * s ^ 2 * t * u + 6 * s ^ 2 * t + 3 * s ^ 2 * u ^ 3 -
        11 * s ^ 2 * u ^ 2 + 12 * s ^ 2 * u - 4 * s ^ 2 - 6 * s * t ^ 2 * u ^ 2 + 15 * s * t ^ 2 * u -
        6 * s * t ^ 2 - 4 * s * t * u ^ 3 + 26 * s * t * u ^ 2 - 39 * s * t * u + 15 * s * t +
        7 * s * u ^ 3 - 27 * s * u ^ 2 + 30 * s * u - 10 * s - t ^ 4 * u ^ 2 + t ^ 3 * u ^ 3 +
        2 * t ^ 3 * u ^ 2 - t ^ 3 * u + t ^ 2 * u ^ 3 - 10 * t ^ 2 * u ^ 2 + 5 * t ^ 2 * u -
        7 * t * u ^ 3 + 20 * t * u ^ 2 - 10 * t * u)) * (s * t - 2 * t + 1) := by
  linear_combination
    ((s - t) ^ 3 *
      (t * u ^ 3 - 4 * t * u ^ 2 + 5 * t * u - 2 * t - u ^ 3 + 3 * u ^ 2 - 3 * u + 1)) * hR0 +
    (ab * (-2 * s * u ^ 2 + 2 * s * u - 2 * t ^ 4 * u ^ 2 + 2 * t ^ 4 * u + 10 * t ^ 3 * u ^ 2 -
        10 * t ^ 3 * u - 20 * t ^ 2 * u ^ 2 + 20 * t ^ 2 * u + 20 * t * u ^ 2 - 20 * t * u -
        6 * u ^ 2 + 6 * u) +
      bb * (-s ^ 3 * u ^ 2 + 2 * s ^ 3 * u - s ^ 3 - s ^ 2 * u ^ 2 + 2 * s ^ 2 * u - s ^ 2 -
        3 * s * u ^ 2 + 8 * s * u - 4 * s + t ^ 4 * u ^ 2 - 3 * t ^ 3 * u ^ 2 - 4 * t ^ 3 * u +
        2 * t ^ 3 - t ^ 2 * u ^ 2 + 22 * t ^ 2 * u - 11 * t ^ 2 + 15 * t * u ^ 2 - 50 * t * u +
        25 * t - 7 * u ^ 2 + 20 * u - 10)) * hR1 +
    (-2 * t * (s - t) ^ 3 *
      ((t * (1 - u) * aa + 2 * t * u * ab - u * bb) - ab * (1 - u + u * t))) * hR2

/-- The coefficient of the master condition is, modulo the relations, a nonzero multiple
of the "big" positive quantity. -/
lemma alg_cG (aa ab bb s t u : ℝ)
    (hR0 : t * aa = s * bb) (hR1 : u * (s - t) = s * (1 - t)) :
    ab * (-2 * s ^ 2 * t * u ^ 3 + 6 * s ^ 2 * t * u ^ 2 - 4 * s ^ 2 * t * u + 2 * s ^ 2 * u ^ 3 -
        4 * s ^ 2 * u ^ 2 + 2 * s ^ 2 * u + 6 * s * t ^ 2 * u ^ 3 - 18 * s * t ^ 2 * u ^ 2 +
        12 * s * t ^ 2 * u - 10 * s * t * u ^ 3 + 24 * s * t * u ^ 2 - 14 * s * t * u + 6 * s * u ^ 3 -
        12 * s * u ^ 2 + 6 * s * u + 2 * t ^ 4 * u ^ 2 - 2 * t ^ 4 * u - 4 * t ^ 3 * u ^ 3 +
        4 * t ^ 3 * u ^ 2 + 8 * t ^ 2 * u ^ 3 - 8 * t ^ 2 * u ^ 2 - 6 * t * u ^ 3 + 6 * t * u ^ 2) +
      bb * (s ^ 3 * u ^ 3 - 3 * s ^ 3 * u ^ 2 + 3 * s ^ 3 * u - s ^ 3 - 2 * s ^ 2 * t * u ^ 3 +
        10 * s ^ 2 * t * u ^ 2 - 15 * s ^ 2 * t * u + 6 * s ^ 2 * t + 3 * s ^ 2 * u ^ 3 -
        11 * s ^ 2 * u ^ 2 + 12 * s ^ 2 * u - 4 * s ^ 2 - 6 * s * t ^ 2 * u ^ 2 + 15 * s * t ^ 2 * u -
        6 * s * t ^ 2 - 4 * s * t * u ^ 3 + 26 * s * t * u ^ 2 - 39 * s * t * u + 15 * s * t +
        7 * s * u ^ 3 - 27 * s * u ^ 2 + 30 * s * u - 10 * s - t ^ 4 * u ^ 2 + t ^ 3 * u ^ 3 +
        2 * t ^ 3 * u ^ 2 - t ^ 3 * u + t ^ 2 * u ^ 3 - 10 * t ^ 2 * u ^ 2 + 5 * t ^ 2 * u -
        7 * t * u ^ 3 + 20 * t * u ^ 2 - 10 * t * u) =
    -(s * t ^ 2) * (bb * (s * (1 - t) ^ 2 + t * (1 - s) ^ 2) - 2 * ab * t * (1 - t) * (1 - s)) := by
  linear_combination
    (-s ^ 2 * t ^ 3 - s ^ 2 * u ^ 3 + 3 * s ^ 2 * u ^ 2 - 3 * s ^ 2 * u + s ^ 2 - s * t ^ 4 +
      4 * s * t ^ 3 - s * t ^ 2 + 2 * s * t * u ^ 3 - 10 * s * t * u ^ 2 + 15 * s * t * u -
      6 * s * t - 3 * s * u ^ 3 + 11 * s * u ^ 2 - 12 * s * u + 4 * s + t ^ 4 * u - 3 * t ^ 3 * u -
      t ^ 2 * u ^ 3 + 4 * t ^ 2 * u ^ 2 - 2 * t ^ 2 * u + 3 * t * u ^ 3 - 8 * t * u ^ 2 +
      4 * t * u) * hR0 +
    (aa * (s * t ^ 3 - s * t ^ 2 * u + s * t ^ 2 + s * t * u ^ 2 - 2 * s * t * u + s * t + t ^ 4 -
        3 * t ^ 3 - t ^ 2 * u ^ 2 + 4 * t ^ 2 * u - 2 * t ^ 2 + 3 * t * u ^ 2 - 8 * t * u +
        4 * t) +
      ab * (-2 * s * t ^ 3 + 2 * s * t ^ 2 * u - 2 * s * t * u ^ 2 + 2 * s * t * u + 2 * s * u ^ 2 -
        2 * s * u - 2 * t ^ 3 * u + 2 * t ^ 3 + 4 * t ^ 2 * u ^ 2 - 4 * t ^ 2 * u - 8 * t * u ^ 2 +
        8 * t * u + 6 * u ^ 2 - 6 * u) +
      bb * (t ^ 3 * u - t ^ 2 * u ^ 2 - 2 * t ^ 2 * u + t ^ 2 - t * u ^ 2 + 10 * t * u - 5 * t +
        7 * u ^ 2 - 20 * u + 10)) * hR1

/-- In the configuration of the problem, `M` never lies strictly between `B` and `D`;
equivalently `w (w - 1) > 0` for the parameter `w` with `M = B + w (D - B)`. -/
lemma config_lemma (s t u w : ℝ)
    (hR1 : u * (s - t) = s * (1 - t)) (hR2 : w * t * u = (1 - w) * (1 - u))
    (ht0 : 0 < t) (ht1 : t < 1) (hs0 : 0 < s) (hs1 : s < 1) :
    0 < w * (w - 1) := by
  have hst : s ≠ t := by
    intro h
    have h1 : s * (1 - t) = 0 := by linear_combination -hR1 + u * h
    rcases mul_eq_zero.mp h1 with h2 | h2 <;> linarith [hs0, ht1, h2]
  have hst0 : s - t ≠ 0 := sub_ne_zero.mpr hst
  have hK2 : 1 - u * (1 - t) ≠ 0 := by
    intro h
    have hw : w * (1 - u * (1 - t)) = 1 - u := by linear_combination hR2
    rw [h, mul_zero] at hw
    have hu : u = 1 := by linarith [hw]
    rw [hu] at h
    have ht : t = 0 := by linarith [h]
    linarith [ht0, ht]
  have hC : w * (w - 1) * (1 - u + u * t) ^ 2 = u * t * (u - 1) := by
    linear_combination ((w * t * u - (1 - w) * (1 - u)) + 1 - u - u * t) * hR2
  have hupos : 0 < u * t * (u - 1) := by
    rcases lt_or_gt_of_ne hst with h | h
    · have h2 : s - t < 0 := sub_neg.mpr h
      have h1 : 0 < u * (s - t) := by rw [hR1]; exact mul_pos hs0 (sub_pos.mpr ht1)
      have hu : u < 0 := neg_of_mul_pos_left h1 (le_of_lt h2)
      have h3 : u * t < 0 := mul_neg_of_neg_of_pos hu ht0
      have h4 : u - 1 < 0 := by linarith [hu]
      exact mul_pos_of_neg_of_neg h3 h4
    · have h2 : 0 < s - t := sub_pos.mpr h
      have h1 : 0 < u * (s - t) := by rw [hR1]; exact mul_pos hs0 (sub_pos.mpr ht1)
      have hu : 0 < u := pos_of_mul_pos_left h1 (le_of_lt h2)
      have hD : (u - 1) * (s - t) = t * (1 - s) := by linear_combination hR1
      have h4 : 0 < (u - 1) * (s - t) := by rw [hD]; exact mul_pos ht0 (sub_pos.mpr hs1)
      have hu1 : 0 < u - 1 := pos_of_mul_pos_left h4 (le_of_lt h2)
      exact mul_pos (mul_pos hu ht0) hu1
  have hsq : 0 < (1 - u + u * t) ^ 2 := by
    have : (1:ℝ) - u + u * t = 1 - u * (1 - t) := by ring
    rw [this]
    exact sq_pos_of_ne_zero hK2
  have h5 : 0 < w * (w - 1) * (1 - u + u * t) ^ 2 := by rw [hC]; exact hupos
  exact pos_of_mul_pos_left h5 (sq_nonneg _)

/-- The algebraic heart of the problem. With `C` as origin, write `A = C + a`,
`B = C + b`, `D = C + t a`, `E = C + s b`, `F = A + u (B - A)` and
`M = B + w (D - B)`. Under the relations coming from the geometric hypotheses,
`MF = MC` (left-hand equation, squared coordinates) holds if and only if
`MB · MD = MC²` (right-hand equation). -/
lemma algebra_core (ax0 ax1 bx0 bx1 s t u w : ℝ)
    (hcross : ax0 * bx1 - ax1 * bx0 ≠ 0)
    (hR0 : t * (ax0 ^ 2 + ax1 ^ 2) = s * (bx0 ^ 2 + bx1 ^ 2))
    (hR1 : u * (s - t) = s * (1 - t))
    (hR2 : w * t * u = (1 - w) * (1 - u))
    (ht0 : 0 < t) (ht1 : t < 1) (hs0 : 0 < s) (_hs1 : s < 1) :
    ((bx0 + w * (t * ax0 - bx0) - (ax0 + u * (bx0 - ax0))) ^ 2 +
      (bx1 + w * (t * ax1 - bx1) - (ax1 + u * (bx1 - ax1))) ^ 2 =
      (bx0 + w * (t * ax0 - bx0)) ^ 2 + (bx1 + w * (t * ax1 - bx1)) ^ 2)
    ↔ w * (w - 1) * ((t * ax0 - bx0) ^ 2 + (t * ax1 - bx1) ^ 2) =
      (bx0 + w * (t * ax0 - bx0)) ^ 2 + (bx1 + w * (t * ax1 - bx1)) ^ 2 := by
  have hst : s ≠ t := by
    intro h
    have h1 : s * (1 - t) = 0 := by linear_combination -hR1 + u * h
    rcases mul_eq_zero.mp h1 with h2 | h2 <;> linarith [hs0, ht1, h2]
  have hst0 : s - t ≠ 0 := sub_ne_zero.mpr hst
  have hK2 : 1 - u * (1 - t) ≠ 0 := by
    intro h
    have hw : w * (1 - u * (1 - t)) = 1 - u := by linear_combination hR2
    rw [h, mul_zero] at hw
    have hu : u = 1 := by linarith [hw]
    rw [hu] at h
    have ht : t = 0 := by linarith [h]
    linarith [ht0, ht]
  have hbb : 0 < bx0 ^ 2 + bx1 ^ 2 := by
    by_contra h0
    push Not at h0
    have h1 : bx0 ^ 2 + bx1 ^ 2 = 0 := le_antisymm h0 (by positivity)
    rw [add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _)] at h1
    obtain ⟨h1a, h1b⟩ := h1
    have hb0 : bx0 = 0 := eq_zero_of_pow_eq_zero h1a
    have hb1 : bx1 = 0 := eq_zero_of_pow_eq_zero h1b
    rw [hb0, hb1] at hcross
    simp at hcross
  have hSeq : (1 - t) ^ 2 * (ax0 ^ 2 + ax1 ^ 2) -
      2 * (1 - t) * (1 - s) * (ax0 * bx0 + ax1 * bx1) + (1 - s) ^ 2 * (bx0 ^ 2 + bx1 ^ 2) =
      ((1 - t) * ax0 - (1 - s) * bx0) ^ 2 + ((1 - t) * ax1 - (1 - s) * bx1) ^ 2 := by ring
  have hSpos : 0 < (1 - t) ^ 2 * (ax0 ^ 2 + ax1 ^ 2) -
      2 * (1 - t) * (1 - s) * (ax0 * bx0 + ax1 * bx1) + (1 - s) ^ 2 * (bx0 ^ 2 + bx1 ^ 2) := by
    by_contra h0
    push Not at h0
    rw [hSeq] at h0
    have h1 : ((1 - t) * ax0 - (1 - s) * bx0) ^ 2 + ((1 - t) * ax1 - (1 - s) * bx1) ^ 2 = 0 :=
      le_antisymm h0 (by positivity)
    rw [add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _)] at h1
    obtain ⟨h1a, h1b⟩ := h1
    have g1 : (1 - t) * ax0 - (1 - s) * bx0 = 0 := eq_zero_of_pow_eq_zero h1a
    have g2 : (1 - t) * ax1 - (1 - s) * bx1 = 0 := eq_zero_of_pow_eq_zero h1b
    have hcr : (1 - t) * (ax0 * bx1 - ax1 * bx0) = 0 := by
      linear_combination bx1 * g1 - bx0 * g2
    have ht1' : (1:ℝ) - t ≠ 0 := ne_of_gt (sub_pos.mpr ht1)
    rcases mul_eq_zero.mp hcr with h | h
    · exact absurd h ht1'
    · exact hcross h
  have hbig : 0 < (bx0 ^ 2 + bx1 ^ 2) * (s * (1 - t) ^ 2 + t * (1 - s) ^ 2) -
      2 * (ax0 * bx0 + ax1 * bx1) * t * (1 - t) * (1 - s) := by
    have hbig2 : (bx0 ^ 2 + bx1 ^ 2) * (s * (1 - t) ^ 2 + t * (1 - s) ^ 2) -
        2 * (ax0 * bx0 + ax1 * bx1) * t * (1 - t) * (1 - s) =
        t * ((1 - t) ^ 2 * (ax0 ^ 2 + ax1 ^ 2) - 2 * (1 - t) * (1 - s) * (ax0 * bx0 + ax1 * bx1) +
          (1 - s) ^ 2 * (bx0 ^ 2 + bx1 ^ 2)) := by
      linear_combination -((1 - t) ^ 2) * hR0
    rw [hbig2]
    exact mul_pos ht0 hSpos
  have key := alg_key (ax0 ^ 2 + ax1 ^ 2) (ax0 * bx0 + ax1 * bx1) (bx0 ^ 2 + bx1 ^ 2) s t u w
    hR0 hR1 hR2
  have hCG := alg_cG (ax0 ^ 2 + ax1 ^ 2) (ax0 * bx0 + ax1 * bx1) (bx0 ^ 2 + bx1 ^ 2) s t u hR0 hR1
  have hP1eq : ((bx0 + w * (t * ax0 - bx0) - (ax0 + u * (bx0 - ax0))) ^ 2 +
      (bx1 + w * (t * ax1 - bx1) - (ax1 + u * (bx1 - ax1))) ^ 2) -
      ((bx0 + w * (t * ax0 - bx0)) ^ 2 + (bx1 + w * (t * ax1 - bx1)) ^ 2) =
      (1 - u) ^ 2 * (ax0 ^ 2 + ax1 ^ 2) + 2 * u * (1 - u) * (ax0 * bx0 + ax1 * bx1) +
      u ^ 2 * (bx0 ^ 2 + bx1 ^ 2) -
      2 * (w * t * (1 - u) * (ax0 ^ 2 + ax1 ^ 2) +
        (w * t * u + (1 - w) * (1 - u)) * (ax0 * bx0 + ax1 * bx1) +
          (1 - w) * u * (bx0 ^ 2 + bx1 ^ 2)) := by ring
  have hP2eq : w * (w - 1) * ((t * ax0 - bx0) ^ 2 + (t * ax1 - bx1) ^ 2) -
      ((bx0 + w * (t * ax0 - bx0)) ^ 2 + (bx1 + w * (t * ax1 - bx1)) ^ 2) =
      w * (w - 1) * (t ^ 2 * (ax0 ^ 2 + ax1 ^ 2) - 2 * t * (ax0 * bx0 + ax1 * bx1) +
        (bx0 ^ 2 + bx1 ^ 2)) -
      ((w * t) ^ 2 * (ax0 ^ 2 + ax1 ^ 2) + 2 * w * t * (1 - w) * (ax0 * bx0 + ax1 * bx1) +
        (1 - w) ^ 2 * (bx0 ^ 2 + bx1 ^ 2)) := by ring
  have hG1 : (s * t - 2 * t + 1 = 0) ↔
      ((1 - u) ^ 2 * (ax0 ^ 2 + ax1 ^ 2) + 2 * u * (1 - u) * (ax0 * bx0 + ax1 * bx1) +
        u ^ 2 * (bx0 ^ 2 + bx1 ^ 2) -
        2 * (w * t * (1 - u) * (ax0 ^ 2 + ax1 ^ 2) +
          (w * t * u + (1 - w) * (1 - u)) * (ax0 * bx0 + ax1 * bx1) +
            (1 - w) * u * (bx0 ^ 2 + bx1 ^ 2)) = 0) := by
    constructor
    · intro hG
      have h0 : t * (s - t) ^ 3 * (1 - u + u * t) *
          ((1 - u) ^ 2 * (ax0 ^ 2 + ax1 ^ 2) + 2 * u * (1 - u) * (ax0 * bx0 + ax1 * bx1) +
            u ^ 2 * (bx0 ^ 2 + bx1 ^ 2) -
            2 * (w * t * (1 - u) * (ax0 ^ 2 + ax1 ^ 2) +
              (w * t * u + (1 - w) * (1 - u)) * (ax0 * bx0 + ax1 * bx1) +
                (1 - w) * u * (bx0 ^ 2 + bx1 ^ 2))) = 0 := by
        rw [key, hG, mul_zero]
      rcases mul_eq_zero.mp h0 with h | h
      · exact absurd h (mul_ne_zero (mul_ne_zero (ne_of_gt ht0) (pow_ne_zero 3 hst0))
          (by rwa [show (1:ℝ) - u + u * t = 1 - u * (1 - t) by ring]))
      · exact h
    · intro hP
      have h0 : ((ax0 * bx0 + ax1 * bx1) *
            (-2 * s ^ 2 * t * u ^ 3 + 6 * s ^ 2 * t * u ^ 2 - 4 * s ^ 2 * t * u +
              2 * s ^ 2 * u ^ 3 - 4 * s ^ 2 * u ^ 2 + 2 * s ^ 2 * u + 6 * s * t ^ 2 * u ^ 3 -
              18 * s * t ^ 2 * u ^ 2 + 12 * s * t ^ 2 * u - 10 * s * t * u ^ 3 +
              24 * s * t * u ^ 2 - 14 * s * t * u + 6 * s * u ^ 3 - 12 * s * u ^ 2 + 6 * s * u +
              2 * t ^ 4 * u ^ 2 - 2 * t ^ 4 * u - 4 * t ^ 3 * u ^ 3 + 4 * t ^ 3 * u ^ 2 +
              8 * t ^ 2 * u ^ 3 - 8 * t ^ 2 * u ^ 2 - 6 * t * u ^ 3 + 6 * t * u ^ 2) +
          (bx0 ^ 2 + bx1 ^ 2) *
            (s ^ 3 * u ^ 3 - 3 * s ^ 3 * u ^ 2 + 3 * s ^ 3 * u - s ^ 3 - 2 * s ^ 2 * t * u ^ 3 +
              10 * s ^ 2 * t * u ^ 2 - 15 * s ^ 2 * t * u + 6 * s ^ 2 * t + 3 * s ^ 2 * u ^ 3 -
              11 * s ^ 2 * u ^ 2 + 12 * s ^ 2 * u - 4 * s ^ 2 - 6 * s * t ^ 2 * u ^ 2 +
              15 * s * t ^ 2 * u - 6 * s * t ^ 2 - 4 * s * t * u ^ 3 + 26 * s * t * u ^ 2 -
              39 * s * t * u + 15 * s * t + 7 * s * u ^ 3 - 27 * s * u ^ 2 + 30 * s * u - 10 * s -
              t ^ 4 * u ^ 2 + t ^ 3 * u ^ 3 + 2 * t ^ 3 * u ^ 2 - t ^ 3 * u + t ^ 2 * u ^ 3 -
              10 * t ^ 2 * u ^ 2 + 5 * t ^ 2 * u - 7 * t * u ^ 3 + 20 * t * u ^ 2 - 10 * t * u)) *
          (s * t - 2 * t + 1) = 0 := by
        rw [← key, hP, mul_zero]
      rcases mul_eq_zero.mp h0 with h | h
      · rw [hCG] at h
        rcases mul_eq_zero.mp h with h' | h'
        · have hs2 : s * t ^ 2 = 0 := by linarith [h']
          rcases mul_eq_zero.mp hs2 with h'' | h''
          · exact absurd h'' (ne_of_gt hs0)
          · exact absurd h'' (pow_ne_zero 2 (ne_of_gt ht0))
        · exact absurd h' (ne_of_gt hbig)
      · exact h
  have hBX : (s - t) * (1 - u * (1 - t)) * (w * (1 - s * t) - 1) =
      -(t * s) * (s * t - 2 * t + 1) := by
    linear_combination ((s - t) * (1 - s * t)) * hR2 - (t * (1 - s)) * hR1
  have hG2 : (s * t - 2 * t + 1 = 0) ↔ (w * (1 - s * t) - 1 = 0) := by
    constructor
    · intro hG
      have h0 : (s - t) * (1 - u * (1 - t)) * (w * (1 - s * t) - 1) = 0 := by
        rw [hBX, hG, mul_zero]
      rcases mul_eq_zero.mp h0 with h | h
      · rcases mul_eq_zero.mp h with h' | h'
        · exact absurd h' hst0
        · exact absurd h' hK2
      · exact h
    · intro hX
      have h0 : -(t * s) * (s * t - 2 * t + 1) = 0 := by
        rw [← hBX, hX, mul_zero]
      have h2 : t * s * (s * t - 2 * t + 1) = 0 := by linear_combination -h0
      rcases mul_eq_zero.mp h2 with h | h
      · exact absurd h (mul_ne_zero (ne_of_gt ht0) (ne_of_gt hs0))
      · exact h
  have hAX : w * (w - 1) * (t ^ 2 * (ax0 ^ 2 + ax1 ^ 2) - 2 * t * (ax0 * bx0 + ax1 * bx1) +
      (bx0 ^ 2 + bx1 ^ 2)) -
      ((w * t) ^ 2 * (ax0 ^ 2 + ax1 ^ 2) + 2 * w * t * (1 - w) * (ax0 * bx0 + ax1 * bx1) +
        (1 - w) ^ 2 * (bx0 ^ 2 + bx1 ^ 2)) =
      (bx0 ^ 2 + bx1 ^ 2) * (w * (1 - s * t) - 1) := by
    linear_combination -(w * t) * hR0
  have hG3 : (w * (1 - s * t) - 1 = 0) ↔
      (w * (w - 1) * (t ^ 2 * (ax0 ^ 2 + ax1 ^ 2) - 2 * t * (ax0 * bx0 + ax1 * bx1) +
        (bx0 ^ 2 + bx1 ^ 2)) -
        ((w * t) ^ 2 * (ax0 ^ 2 + ax1 ^ 2) + 2 * w * t * (1 - w) * (ax0 * bx0 + ax1 * bx1) +
          (1 - w) ^ 2 * (bx0 ^ 2 + bx1 ^ 2)) = 0) := by
    constructor
    · intro hX
      rw [hAX, hX, mul_zero]
    · intro hP
      have h0 : (bx0 ^ 2 + bx1 ^ 2) * (w * (1 - s * t) - 1) = 0 := by
        rw [← hAX, hP]
      rcases mul_eq_zero.mp h0 with h | h
      · exact absurd h (ne_of_gt hbb)
      · exact h
  have step1 : ((bx0 + w * (t * ax0 - bx0) - (ax0 + u * (bx0 - ax0))) ^ 2 +
      (bx1 + w * (t * ax1 - bx1) - (ax1 + u * (bx1 - ax1))) ^ 2 =
      (bx0 + w * (t * ax0 - bx0)) ^ 2 + (bx1 + w * (t * ax1 - bx1)) ^ 2) ↔
      ((1 - u) ^ 2 * (ax0 ^ 2 + ax1 ^ 2) + 2 * u * (1 - u) * (ax0 * bx0 + ax1 * bx1) +
        u ^ 2 * (bx0 ^ 2 + bx1 ^ 2) -
        2 * (w * t * (1 - u) * (ax0 ^ 2 + ax1 ^ 2) +
          (w * t * u + (1 - w) * (1 - u)) * (ax0 * bx0 + ax1 * bx1) +
            (1 - w) * u * (bx0 ^ 2 + bx1 ^ 2)) = 0) := by
    rw [← hP1eq]
    constructor <;> intro h <;> linarith [h]
  have step3 : (w * (w - 1) * (t ^ 2 * (ax0 ^ 2 + ax1 ^ 2) - 2 * t * (ax0 * bx0 + ax1 * bx1) +
      (bx0 ^ 2 + bx1 ^ 2)) -
      ((w * t) ^ 2 * (ax0 ^ 2 + ax1 ^ 2) + 2 * w * t * (1 - w) * (ax0 * bx0 + ax1 * bx1) +
        (1 - w) ^ 2 * (bx0 ^ 2 + bx1 ^ 2)) = 0) ↔
      (w * (w - 1) * ((t * ax0 - bx0) ^ 2 + (t * ax1 - bx1) ^ 2) =
        (bx0 + w * (t * ax0 - bx0)) ^ 2 + (bx1 + w * (t * ax1 - bx1)) ^ 2) := by
    rw [← hP2eq]
    constructor <;> intro h <;> linarith [h]
  exact step1.trans (hG1.symm.trans (hG2.trans (hG3.trans step3)))

snip end

problem usa2003_p4
    (A B C D E F M : EuclideanSpace ℝ (Fin 2))
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2))))
    (hD : D ∈ segment ℝ A C)
    (hE : E ∈ segment ℝ B C)
    (hcyc : Cospherical ({A, B, D, E} : Set (EuclideanSpace ℝ (Fin 2))))
    (hFAB : Collinear ℝ ({A, B, F} : Set (EuclideanSpace ℝ (Fin 2))))
    (hFDE : Collinear ℝ ({D, E, F} : Set (EuclideanSpace ℝ (Fin 2))))
    (hMBD : Collinear ℝ ({B, D, M} : Set (EuclideanSpace ℝ (Fin 2))))
    (hMCF : Collinear ℝ ({C, F, M} : Set (EuclideanSpace ℝ (Fin 2))))
    (hDA : D ≠ A) (hDC : D ≠ C) (hEB : E ≠ B) (hEC : E ≠ C) :
    dist M F = dist M C ↔ dist M B * dist M D = dist M C ^ 2 := by
  have hAB : A ≠ B := ne₁₂_of_not_collinear hABC
  have hBC : B ≠ C := ne₂₃_of_not_collinear hABC
  have hAC : A ≠ C := ne₁₃_of_not_collinear hABC
  have hBD : B ≠ D := by
    intro hBDeq
    apply hABC
    have h := collinear_of_mem_segment (x := A) (y := C) (z := D) hD
    rw [← hBDeq] at h
    have hset : ({A, C, B} : Set (EuclideanSpace ℝ (Fin 2))) = {A, B, C} := by
      ext p; simp; tauto
    rwa [hset] at h
  have hcross : (A 0 - C 0) * (B 1 - C 1) - (A 1 - C 1) * (B 0 - C 0) ≠ 0 :=
    cross_ne_zero_of_not_collinear hABC
  obtain ⟨t, ht0', ht1', hDt⟩ := segment_coords hD
  have ht0 : 0 < t := by
    refine lt_of_le_of_ne ht0' ?_
    intro h
    apply hDC
    ext i
    have h1 := hDt i
    rw [← h] at h1
    simp at h1
    exact h1
  have ht1 : t < 1 := by
    refine lt_of_le_of_ne ht1' ?_
    intro h
    apply hDA
    ext i
    have h1 := hDt i
    rw [h] at h1
    simp at h1
    exact h1
  obtain ⟨s, hs0', hs1', hEs⟩ := segment_coords hE
  have hs0 : 0 < s := by
    refine lt_of_le_of_ne hs0' ?_
    intro h
    apply hEC
    ext i
    have h1 := hEs i
    rw [← h] at h1
    simp at h1
    exact h1
  have hs1 : s < 1 := by
    refine lt_of_le_of_ne hs1' ?_
    intro h
    apply hEB
    ext i
    have h1 := hEs i
    rw [h] at h1
    simp at h1
    exact h1
  obtain ⟨u, hFu⟩ := line_coords hFAB hAB
  obtain ⟨w, hMw⟩ := line_coords hMBD hBD
  have eMC0 : M 0 - C 0 = (B 0 - C 0) + w * (t * (A 0 - C 0) - (B 0 - C 0)) := by
    rw [hMw 0, hDt 0]; ring
  have eMC1 : M 1 - C 1 = (B 1 - C 1) + w * (t * (A 1 - C 1) - (B 1 - C 1)) := by
    rw [hMw 1, hDt 1]; ring
  have hR1 : u * (s - t) = s * (1 - t) := by
    have hFDE' : Collinear ℝ ({F, E, D} : Set (EuclideanSpace ℝ (Fin 2))) := by
      have hset : ({F, E, D} : Set (EuclideanSpace ℝ (Fin 2))) = {D, E, F} := by
        ext p; simp; tauto
      rw [hset]; exact hFDE
    have hc1 := cross_eq_zero_of_collinear hFDE'
    have eFD0 : F 0 - D 0 = (1 - u - t) * (A 0 - C 0) + u * (B 0 - C 0) := by
      rw [hFu 0, hDt 0]; ring
    have eFD1 : F 1 - D 1 = (1 - u - t) * (A 1 - C 1) + u * (B 1 - C 1) := by
      rw [hFu 1, hDt 1]; ring
    have eED0 : E 0 - D 0 = s * (B 0 - C 0) - t * (A 0 - C 0) := by
      rw [hEs 0, hDt 0]; ring
    have eED1 : E 1 - D 1 = s * (B 1 - C 1) - t * (A 1 - C 1) := by
      rw [hEs 1, hDt 1]; ring
    rw [eFD0, eFD1, eED0, eED1] at hc1
    have h1 : (s * (1 - t) - u * (s - t)) *
        ((A 0 - C 0) * (B 1 - C 1) - (A 1 - C 1) * (B 0 - C 0)) = 0 := by
      linear_combination hc1
    rcases mul_eq_zero.mp h1 with h | h
    · linarith [h]
    · exact absurd h hcross
  have hR2 : w * t * u = (1 - w) * (1 - u) := by
    have hMCF' : Collinear ℝ ({M, F, C} : Set (EuclideanSpace ℝ (Fin 2))) := by
      have hset : ({M, F, C} : Set (EuclideanSpace ℝ (Fin 2))) = {C, F, M} := by
        ext p; simp; tauto
      rw [hset]; exact hMCF
    have hc2 := cross_eq_zero_of_collinear hMCF'
    have eFC0 : F 0 - C 0 = (1 - u) * (A 0 - C 0) + u * (B 0 - C 0) := by
      rw [hFu 0]; ring
    have eFC1 : F 1 - C 1 = (1 - u) * (A 1 - C 1) + u * (B 1 - C 1) := by
      rw [hFu 1]; ring
    rw [eMC0, eMC1, eFC0, eFC1] at hc2
    have h1 : (w * t * u - (1 - w) * (1 - u)) *
        ((A 0 - C 0) * (B 1 - C 1) - (A 1 - C 1) * (B 0 - C 0)) = 0 := by
      linear_combination hc2
    rcases mul_eq_zero.mp h1 with h | h
    · linarith [h]
    · exact absurd h hcross
  have hpow : dist A C * dist D C = dist B C * dist E C := by
    have hCAD : Collinear ℝ ({A, C, D} : Set (EuclideanSpace ℝ (Fin 2))) :=
      collinear_of_mem_segment hD
    have hCBE : Collinear ℝ ({B, C, E} : Set (EuclideanSpace ℝ (Fin 2))) :=
      collinear_of_mem_segment hE
    have hC1 : C ∈ line[ℝ, A, D] :=
      hCAD.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) (Ne.symm hDA)
    have hC2 : C ∈ line[ℝ, B, E] :=
      hCBE.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) (Ne.symm hEB)
    have h := EuclideanGeometry.mul_dist_eq_mul_dist_of_cospherical
      (a := A) (b := D) (c := B) (d := E) (p := C) ?_ hC1 hC2
    · exact h
    · have hset : ({A, D, B, E} : Set (EuclideanSpace ℝ (Fin 2))) = {A, B, D, E} := by
        ext p; simp; tauto
      rw [hset]; exact hcyc
  have hDCt : dist D C = t * dist A C := by
    have h1 : D -ᵥ C = t • (A -ᵥ C) := by
      ext i; have h2 := hDt i; fin_cases i <;> simp at h2 ⊢ <;> linarith
    rw [dist_eq_norm_vsub, h1, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0', dist_eq_norm_vsub]
  have hECs : dist E C = s * dist B C := by
    have h1 : E -ᵥ C = s • (B -ᵥ C) := by
      ext i; have h2 := hEs i; fin_cases i <;> simp at h2 ⊢ <;> linarith
    rw [dist_eq_norm_vsub, h1, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0', dist_eq_norm_vsub]
  have hsqA : dist A C ^ 2 = (A 0 - C 0) ^ 2 + (A 1 - C 1) ^ 2 := dist_sq_coords A C
  have hsqB : dist B C ^ 2 = (B 0 - C 0) ^ 2 + (B 1 - C 1) ^ 2 := dist_sq_coords B C
  have hR0 : t * ((A 0 - C 0) ^ 2 + (A 1 - C 1) ^ 2) = s * ((B 0 - C 0) ^ 2 + (B 1 - C 1) ^ 2) := by
    rw [hDCt, hECs] at hpow
    have h2 : t * dist A C ^ 2 = s * dist B C ^ 2 := by linear_combination hpow
    rw [hsqA, hsqB] at h2
    exact h2
  have hMF2 : dist M F ^ 2 = (M 0 - F 0) ^ 2 + (M 1 - F 1) ^ 2 := dist_sq_coords M F
  have hMC2 : dist M C ^ 2 = (M 0 - C 0) ^ 2 + (M 1 - C 1) ^ 2 := dist_sq_coords M C
  have hDB2 : dist D B ^ 2 = (D 0 - B 0) ^ 2 + (D 1 - B 1) ^ 2 := dist_sq_coords D B
  have hMBw : dist M B = |w| * dist D B := by
    have h1 : M -ᵥ B = w • (D -ᵥ B) := by
      ext i; have h2 := hMw i; fin_cases i <;> simp at h2 ⊢ <;> linarith
    rw [dist_eq_norm_vsub, h1, norm_smul, Real.norm_eq_abs, dist_eq_norm_vsub]
  have hMDw : dist M D = |w - 1| * dist D B := by
    have h1 : M -ᵥ D = (w - 1) • (D -ᵥ B) := by
      ext i; have h2 := hMw i; fin_cases i <;> simp at h2 ⊢ <;> linarith
    rw [dist_eq_norm_vsub, h1, norm_smul, Real.norm_eq_abs, dist_eq_norm_vsub]
  have hww : 0 < w * (w - 1) := config_lemma s t u w hR1 hR2 ht0 ht1 hs0 hs1
  have habsw : |w| * |w - 1| = w * (w - 1) := by
    rw [← abs_mul]; exact abs_of_pos hww
  have hMBMD : dist M B * dist M D = w * (w - 1) * dist D B ^ 2 := by
    rw [hMBw, hMDw,
      show |w| * dist D B * (|w - 1| * dist D B) = (|w| * |w - 1|) * dist D B ^ 2 by ring,
      habsw]
  have eMF0 : M 0 - F 0 = (B 0 - C 0) + w * (t * (A 0 - C 0) - (B 0 - C 0)) -
      ((A 0 - C 0) + u * ((B 0 - C 0) - (A 0 - C 0))) := by
    rw [hMw 0, hFu 0, hDt 0]; ring
  have eMF1 : M 1 - F 1 = (B 1 - C 1) + w * (t * (A 1 - C 1) - (B 1 - C 1)) -
      ((A 1 - C 1) + u * ((B 1 - C 1) - (A 1 - C 1))) := by
    rw [hMw 1, hFu 1, hDt 1]; ring
  have eDB0 : D 0 - B 0 = t * (A 0 - C 0) - (B 0 - C 0) := by rw [hDt 0]; ring
  have eDB1 : D 1 - B 1 = t * (A 1 - C 1) - (B 1 - C 1) := by rw [hDt 1]; ring
  have hcore := algebra_core (A 0 - C 0) (A 1 - C 1) (B 0 - C 0) (B 1 - C 1) s t u w
    hcross hR0 hR1 hR2 ht0 ht1 hs0 hs1
  constructor
  · intro hlr
    have h1 : dist M F ^ 2 = dist M C ^ 2 := by rw [hlr]
    rw [hMF2, hMC2, eMF0, eMF1, eMC0, eMC1] at h1
    have h2 := hcore.mp h1
    rw [hMBMD, hDB2, eDB0, eDB1, hMC2, eMC0, eMC1]
    exact h2
  · intro hlr
    rw [hMBMD, hDB2, eDB0, eDB1, hMC2, eMC0, eMC1] at hlr
    have h2 := hcore.mpr hlr
    have h1 : dist M F ^ 2 = dist M C ^ 2 := by
      rw [hMF2, hMC2, eMF0, eMF1, eMC0, eMC1]
      exact h2
    exact (pow_left_inj₀ dist_nonneg dist_nonneg two_ne_zero).mp h1

end Usa2003P4
