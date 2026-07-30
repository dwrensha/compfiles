/-
Copyright (c) 2026 The Compfiles Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import ProblemExtraction

@[expose] public section

problem_file {
  tags := [.Geometry]
}

/-!
# USA Mathematical Olympiad 1980, Problem 4

The insphere of a tetrahedron touches each face at its centroid.
Show that the tetrahedron is regular.
-/

namespace Usa1980P4

open scoped InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The centroid of the triangle with vertices `x`, `y`, `z`. -/
noncomputable def centroid (x y z : V) : V := (1 / 3 : ℝ) • (x + y + z)

/-- `IsTangentAtCentroid o r x y z` says that the sphere with center `o` and
radius `r` is tangent to the plane of the triangle `x y z` at the centroid of
the triangle: the centroid lies on the sphere, and the radius to the centroid
is perpendicular to the plane of the triangle (hence perpendicular to the
segments joining the centroid to each vertex). -/
def IsTangentAtCentroid (o : V) (r : ℝ) (x y z : V) : Prop :=
  dist o (centroid x y z) = r ∧
    ⟪o - centroid x y z, x - centroid x y z⟫_ℝ = 0 ∧
    ⟪o - centroid x y z, y - centroid x y z⟫_ℝ = 0 ∧
    ⟪o - centroid x y z, z - centroid x y z⟫_ℝ = 0

snip begin

/-- Two non-negative real numbers with equal squares are equal. -/
lemma eq_of_sq_eq_sq_of_nonneg {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : x ^ 2 = y ^ 2) : x = y := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h | h
  · exact h
  · linarith

/-- Tangent segments drawn from a point to a sphere have equal length:
if the sphere with center `o` and radius `r` passes through `g₁` and `g₂`,
and the radii to `g₁` and `g₂` are perpendicular to the segments joining
them to `v`, then `dist v g₁ = dist v g₂`. -/
lemma dist_eq_of_tangent {o g₁ g₂ v : V} {r : ℝ}
    (h₁ : dist o g₁ = r) (h₂ : dist o g₂ = r)
    (hp₁ : ⟪o - g₁, v - g₁⟫_ℝ = 0) (hp₂ : ⟪o - g₂, v - g₂⟫_ℝ = 0) :
    dist v g₁ = dist v g₂ := by
  have e₁ : dist v g₁ ^ 2 = dist v o ^ 2 - dist o g₁ ^ 2 := by
    have hvo : v - o = (v - g₁) - (o - g₁) := by module
    rw [dist_eq_norm, dist_eq_norm, dist_eq_norm, hvo,
      norm_sub_sq_real (v - g₁) (o - g₁), real_inner_comm (o - g₁) (v - g₁), hp₁]
    ring
  have e₂ : dist v g₂ ^ 2 = dist v o ^ 2 - dist o g₂ ^ 2 := by
    have hvo : v - o = (v - g₂) - (o - g₂) := by module
    rw [dist_eq_norm, dist_eq_norm, dist_eq_norm, hvo,
      norm_sub_sq_real (v - g₂) (o - g₂), real_inner_comm (o - g₂) (v - g₂), hp₂]
    ring
  apply eq_of_sq_eq_sq_of_nonneg dist_nonneg dist_nonneg
  rw [e₁, e₂, h₁, h₂]

/-- The geometric heart of the proof (following the official solution):
if the tangent lengths from `a` to the centroids of the faces `a b c` and
`a c d` are equal, and likewise for `c`, then the edges `b c` and `c d`
have equal length. -/
lemma edge_eq_of_tangent_eq {a b c d g₁ g₂ : V}
    (hg₁ : g₁ = (1 / 3 : ℝ) • (a + b + c))
    (hg₂ : g₂ = (1 / 3 : ℝ) • (a + c + d))
    (ha : dist a g₁ = dist a g₂) (hc : dist c g₁ = dist c g₂) :
    dist b c = dist c d := by
  have h2n : ‖(2 : ℝ)‖ = 2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have h12 : ‖(1 / 2 : ℝ)‖ = 1 / 2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  -- Squared versions of the tangent-length hypotheses.
  have ha2 : ‖a - g₁‖ ^ 2 = ‖a - g₂‖ ^ 2 := by
    rw [← dist_eq_norm, ← dist_eq_norm, ha]
  have hc2 : ‖c - g₁‖ ^ 2 = ‖c - g₂‖ ^ 2 := by
    rw [← dist_eq_norm, ← dist_eq_norm, hc]
  -- The shared edge `a c` determines the two relevant inner products.
  have hac₁ : a - c = (a - g₁) - (c - g₁) := by module
  have hac₂ : a - c = (a - g₂) - (c - g₂) := by module
  have hi₁ : 2 * ⟪c - g₁, a - g₁⟫_ℝ = ‖a - g₁‖ ^ 2 + ‖c - g₁‖ ^ 2 - ‖a - c‖ ^ 2 := by
    have h := norm_sub_sq_real (a - g₁) (c - g₁)
    rw [real_inner_comm (c - g₁) (a - g₁), ← hac₁] at h
    linarith
  have hi₂ : 2 * ⟪c - g₂, a - g₂⟫_ℝ = ‖a - g₂‖ ^ 2 + ‖c - g₂‖ ^ 2 - ‖a - c‖ ^ 2 := by
    have h := norm_sub_sq_real (a - g₂) (c - g₂)
    rw [real_inner_comm (c - g₂) (a - g₂), ← hac₂] at h
    linarith
  -- Each of the edges `b c`, `c d` is twice the segment from `c` to its midpoint.
  have hbc : dist b c = 2 * dist c ((1 / 2 : ℝ) • (b + c)) := by
    have e : c - b = (2 : ℝ) • (c - (1 / 2 : ℝ) • (b + c)) := by module
    rw [dist_eq_norm, dist_eq_norm, ← norm_neg (b - c), neg_sub, e, norm_smul, h2n]
  have hcd : dist c d = 2 * dist c ((1 / 2 : ℝ) • (c + d)) := by
    have e : c - d = (2 : ℝ) • (c - (1 / 2 : ℝ) • (c + d)) := by module
    rw [dist_eq_norm, dist_eq_norm, e, norm_smul, h2n]
  rw [hbc, hcd]
  congr 1
  -- The segments from `c` to the midpoints, expressed via the centroids.
  have hm : c - (1 / 2 : ℝ) • (b + c) = (c - g₁) + (1 / 2 : ℝ) • (a - g₁) := by
    rw [hg₁]; module
  have hn : c - (1 / 2 : ℝ) • (c + d) = (c - g₂) + (1 / 2 : ℝ) • (a - g₂) := by
    rw [hg₂]; module
  apply eq_of_sq_eq_sq_of_nonneg dist_nonneg dist_nonneg
  rw [dist_eq_norm, dist_eq_norm, hm, hn,
    norm_add_sq_real (c - g₁) ((1 / 2 : ℝ) • (a - g₁)),
    norm_add_sq_real (c - g₂) ((1 / 2 : ℝ) • (a - g₂)),
    real_inner_smul_right, real_inner_smul_right,
    norm_smul, norm_smul, h12]
  linear_combination (1 / 2) * hi₁ - (1 / 2) * hi₂ + (3 / 2) * hc2 + (3 / 4) * ha2

snip end

problem usa1980_p4
    (a b c d o : EuclideanSpace ℝ (Fin 3)) (r : ℝ) (_hr : 0 < r)
    (hBCD : IsTangentAtCentroid o r b c d)
    (hACD : IsTangentAtCentroid o r a c d)
    (hABD : IsTangentAtCentroid o r a b d)
    (hABC : IsTangentAtCentroid o r a b c) :
    dist a b = dist a c ∧ dist a b = dist a d ∧ dist a b = dist b c ∧
      dist a b = dist b d ∧ dist a b = dist c d := by
  -- Unfold the tangency hypotheses.
  simp only [IsTangentAtCentroid, centroid] at hBCD hACD hABD hABC
  obtain ⟨ho_a, hpa_b, hpa_c, hpa_d⟩ := hBCD
  obtain ⟨ho_b, hpb_a, hpb_c, hpb_d⟩ := hACD
  obtain ⟨ho_c, hpc_a, hpc_b, hpc_d⟩ := hABD
  obtain ⟨ho_d, hpd_a, hpd_b, hpd_c⟩ := hABC
  -- Tangent segments from each vertex to the insphere are equal.
  have ta1 : dist a ((1 / 3 : ℝ) • (a + b + c)) = dist a ((1 / 3 : ℝ) • (a + b + d)) :=
    dist_eq_of_tangent ho_d ho_c hpd_a hpc_a
  have ta2 : dist a ((1 / 3 : ℝ) • (a + b + d)) = dist a ((1 / 3 : ℝ) • (a + c + d)) :=
    dist_eq_of_tangent ho_c ho_b hpc_a hpb_a
  have tb1 : dist b ((1 / 3 : ℝ) • (a + b + c)) = dist b ((1 / 3 : ℝ) • (a + b + d)) :=
    dist_eq_of_tangent ho_d ho_c hpd_b hpc_b
  have tc1 : dist c ((1 / 3 : ℝ) • (a + b + c)) = dist c ((1 / 3 : ℝ) • (a + c + d)) :=
    dist_eq_of_tangent ho_d ho_b hpd_c hpb_c
  have tc2 : dist c ((1 / 3 : ℝ) • (a + c + d)) = dist c ((1 / 3 : ℝ) • (b + c + d)) :=
    dist_eq_of_tangent ho_b ho_a hpb_c hpa_c
  have td1 : dist d ((1 / 3 : ℝ) • (a + b + d)) = dist d ((1 / 3 : ℝ) • (a + c + d)) :=
    dist_eq_of_tangent ho_c ho_b hpc_d hpb_d
  have td2 : dist d ((1 / 3 : ℝ) • (a + c + d)) = dist d ((1 / 3 : ℝ) • (b + c + d)) :=
    dist_eq_of_tangent ho_b ho_a hpb_d hpa_d
  -- Apply the key lemma to five pairs of faces; each application shows that
  -- two edges sharing a vertex are equal.
  have e1 : dist b c = dist c d := edge_eq_of_tangent_eq rfl rfl (ta1.trans ta2) tc1
  have e2 : dist b d = dist d c := edge_eq_of_tangent_eq rfl (by module) ta2 td1
  have e3 : dist c a = dist a d := edge_eq_of_tangent_eq (by module) (by module) tb1 ta1
  have e4 : dist b a = dist a c := edge_eq_of_tangent_eq (by module) (by module) td1 ta2
  have e5 : dist a c = dist c b := edge_eq_of_tangent_eq (by module) (by module) td2 tc2
  rw [dist_comm b a] at e4
  rw [dist_comm c a] at e3
  rw [dist_comm c b] at e5
  rw [dist_comm d c] at e2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith

end Usa1980P4
