/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# USA Mathematical Olympiad 1983, Problem 4

Show that one can construct (with ruler and compasses) a length equal to
the altitude from A of the tetrahedron ABCD, given the lengths of all the
sides.  [So for each pair of vertices, one is given a pair of points in
the plane the appropriate distance apart.]

## Formalization notes

The lengths constructible from given lengths with ruler and compasses are
exactly those obtained from the data by the field operations `+`, `-`,
`*`, `/` together with (repeated) square roots.  Hence it suffices to
express the altitude from `A` by such an expression in the six side
lengths of the tetrahedron.  We prove the stronger statement that the
*square* of the altitude is a rational function, with integer
coefficients, of the six squared side lengths: concretely, the Gram
determinant ratio (equivalently, a Cayley–Menger determinant ratio)
`altitudeSq` below.  One final square root then exhibits the altitude
itself as a ruler-and-compass expression in the given data.

More precisely, for points `A B C D` of a real inner product space whose
base triangle `BCD` is non-degenerate, we exhibit the foot `H` of the
altitude from `A` as an explicit affine combination of `B`, `C`, `D`,
show that `AH` is perpendicular to the plane `BCD`, and identify
`dist A H ^ 2` with `altitudeSq` evaluated at the six side lengths.
-/

open scoped InnerProductSpace

namespace Usa1983P4

/-- The squared altitude from apex `A` of a tetrahedron `ABCD`, as an
explicit rational function of the six side lengths: the Gram determinant
ratio `det G(B - D, C - D, A - D) / det G(B - D, C - D)`, with the inner
products expressed via polarization, e.g.
`⟪B - D, C - D⟫ = (BD ^ 2 + CD ^ 2 - BC ^ 2) / 2`. -/
noncomputable def altitudeSq (AB AC AD BC BD CD : ℝ) : ℝ :=
  (BD ^ 2 * (CD ^ 2 * AD ^ 2 - ((CD ^ 2 + AD ^ 2 - AC ^ 2) / 2) ^ 2)
    - ((BD ^ 2 + CD ^ 2 - BC ^ 2) / 2) *
      (((BD ^ 2 + CD ^ 2 - BC ^ 2) / 2) * AD ^ 2
        - ((CD ^ 2 + AD ^ 2 - AC ^ 2) / 2) * ((BD ^ 2 + AD ^ 2 - AB ^ 2) / 2))
    + ((BD ^ 2 + AD ^ 2 - AB ^ 2) / 2) *
      (((BD ^ 2 + CD ^ 2 - BC ^ 2) / 2) * ((CD ^ 2 + AD ^ 2 - AC ^ 2) / 2)
        - CD ^ 2 * ((BD ^ 2 + AD ^ 2 - AB ^ 2) / 2))) /
    (BD ^ 2 * CD ^ 2 - ((BD ^ 2 + CD ^ 2 - BC ^ 2) / 2) ^ 2)

snip begin

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Squared distance as an inner product. -/
lemma inner_self_eq_dist_sq (x y : V) :
    ⟪x - y, x - y⟫_ℝ = (dist x y) ^ 2 := by
  rw [real_inner_self_eq_norm_sq, dist_eq_norm]

/-- Polarization: the inner product of two edge vectors with common tail
`z` is a rational expression in the three relevant side lengths. -/
lemma inner_sub_sub_eq (x y z : V) :
    ⟪x - z, y - z⟫_ℝ = ((dist x z) ^ 2 + (dist y z) ^ 2 - (dist x y) ^ 2) / 2 := by
  have h := norm_sub_sq_real (x - z) (y - z)
  have hsub : x - z - (y - z) = x - y := by abel
  rw [hsub, ← dist_eq_norm x y, ← dist_eq_norm x z, ← dist_eq_norm y z] at h
  linarith

/-- The perpendicular from the tip of `w` to the plane spanned by `u, v`:
explicit coefficients of the foot, and the squared distance as the Gram
determinant ratio `det G(u, v, w) / det G(u, v)`. -/
lemma gram_det_ratio (u v w : V)
    (hG : ⟪u, u⟫_ℝ * ⟪v, v⟫_ℝ - (⟪u, v⟫_ℝ) ^ 2 ≠ 0) :
    ∃ s t : ℝ,
      ⟪w - s • u - t • v, u⟫_ℝ = 0 ∧
      ⟪w - s • u - t • v, v⟫_ℝ = 0 ∧
      ⟪w - s • u - t • v, w - s • u - t • v⟫_ℝ =
        (⟪u, u⟫_ℝ * (⟪v, v⟫_ℝ * ⟪w, w⟫_ℝ - (⟪v, w⟫_ℝ) ^ 2)
          - ⟪u, v⟫_ℝ * (⟪u, v⟫_ℝ * ⟪w, w⟫_ℝ - ⟪v, w⟫_ℝ * ⟪u, w⟫_ℝ)
          + ⟪u, w⟫_ℝ * (⟪u, v⟫_ℝ * ⟪v, w⟫_ℝ - ⟪v, v⟫_ℝ * ⟪u, w⟫_ℝ)) /
          (⟪u, u⟫_ℝ * ⟪v, v⟫_ℝ - (⟪u, v⟫_ℝ) ^ 2) := by
  have hG' : ⟪v, v⟫_ℝ * ⟪u, u⟫_ℝ - (⟪u, v⟫_ℝ) ^ 2 ≠ 0 := by rwa [mul_comm] at hG
  refine ⟨(⟪w, u⟫_ℝ * ⟪v, v⟫_ℝ - ⟪w, v⟫_ℝ * ⟪u, v⟫_ℝ) /
      (⟪u, u⟫_ℝ * ⟪v, v⟫_ℝ - (⟪u, v⟫_ℝ) ^ 2),
    (⟪w, v⟫_ℝ * ⟪u, u⟫_ℝ - ⟪w, u⟫_ℝ * ⟪u, v⟫_ℝ) /
      (⟪u, u⟫_ℝ * ⟪v, v⟫_ℝ - (⟪u, v⟫_ℝ) ^ 2), ?_, ?_, ?_⟩ <;>
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, real_inner_comm u v, real_inner_comm u w,
      real_inner_comm v w] <;> field_simp [hG, hG'] <;> ring

snip end

problem usa1983_p4 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (A B C D : V)
    (hnondeg : (dist B D) ^ 2 * (dist C D) ^ 2
      - (((dist B D) ^ 2 + (dist C D) ^ 2 - (dist B C) ^ 2) / 2) ^ 2 ≠ 0) :
    ∃ H : V, ∃ s t : ℝ,
      H = D + s • (B - D) + t • (C - D) ∧
      ⟪A - H, B - D⟫_ℝ = 0 ∧
      ⟪A - H, C - D⟫_ℝ = 0 ∧
      (dist A H) ^ 2 =
        altitudeSq (dist A B) (dist A C) (dist A D) (dist B C) (dist B D) (dist C D) := by
  have hG : ⟪B - D, B - D⟫_ℝ * ⟪C - D, C - D⟫_ℝ - (⟪B - D, C - D⟫_ℝ) ^ 2 ≠ 0 := by
    rw [inner_self_eq_dist_sq B D, inner_self_eq_dist_sq C D, inner_sub_sub_eq B C D]
    exact hnondeg
  obtain ⟨s, t, hperpu, hperpv, hratio⟩ := gram_det_ratio (B - D) (C - D) (A - D) hG
  have hAH : A - (D + s • (B - D) + t • (C - D))
      = (A - D) - s • (B - D) - t • (C - D) := by
    module
  have hdist : (dist A (D + s • (B - D) + t • (C - D))) ^ 2
      = ⟪(A - D) - s • (B - D) - t • (C - D),
          (A - D) - s • (B - D) - t • (C - D)⟫_ℝ := by
    rw [dist_eq_norm, ← real_inner_self_eq_norm_sq, hAH]
  refine ⟨D + s • (B - D) + t • (C - D), s, t, rfl, ?_, ?_, ?_⟩
  · rw [hAH]
    exact hperpu
  · rw [hAH]
    exact hperpv
  · rw [hdist, hratio, inner_self_eq_dist_sq B D, inner_self_eq_dist_sq C D,
      inner_self_eq_dist_sq A D, inner_sub_sub_eq B C D, inner_sub_sub_eq B A D,
      inner_sub_sub_eq C A D, dist_comm B A, dist_comm C A]
    unfold altitudeSq
    field_simp [hnondeg]

end Usa1983P4
