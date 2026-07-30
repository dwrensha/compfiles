/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.Convex.BetweenList
public import Mathlib.Analysis.InnerProductSpace.TwoDim
public import Mathlib.Geometry.Euclidean.Incenter
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 2008, Problem 6

Let ABCD be a convex quadrilateral with BA ≠ BC. Denote the incircles of
triangles ABC and ADC by ω1 and ω2 respectively. Suppose that there exists
a circle ω tangent to ray BA beyond A and to the ray BC beyond C, which is
also tangent to the lines AD and CD. Prove that the common external tangents
to ω1 and ω2 intersect on ω.
-/

open Affine EuclideanGeometry FiniteDimensional Module

open scoped Affine RealInnerProductSpace

attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

namespace Imo2008P6

variable {V Pt : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace Pt]
variable [NormedAddTorsor V Pt] [Fact (finrank ℝ V = 2)]

snip begin

/-- A common external tangent line of two circles: a line (one-dimensional
affine subspace) tangent to both circles, with both centers strictly on the
same side of the line (which is what makes the tangent "external" as opposed
to the common internal tangents, for which the centers are on opposite
sides). -/
def CommonExternalTangent (ω₁ ω₂ : Sphere Pt) (ℓ : AffineSubspace ℝ Pt) : Prop :=
  finrank ℝ ℓ.direction = 1 ∧ ω₁.IsTangent ℓ ∧ ω₂.IsTangent ℓ ∧
    ℓ.SSameSide ω₁.center ω₂.center

omit [Fact (finrank ℝ V = 2)] in
lemma CommonExternalTangent.symm {ω₁ ω₂ : Sphere Pt} {ℓ : AffineSubspace ℝ Pt}
    (h : CommonExternalTangent ω₁ ω₂ ℓ) : CommonExternalTangent ω₂ ω₁ ℓ :=
  ⟨h.1, h.2.2.1, h.2.1, h.2.2.2.symm⟩

/-- A fixed but arbitrary orientation of the plane, used to express
convexity and sidedness through determinants (`Orientation.areaForm`).
`ConvexQuadrilateral` below is independent of this choice because it is
symmetric in the two orientations. -/
noncomputable def planeOrientation : Orientation ℝ V (Fin 2) :=
  (Module.finBasisOfFinrankEq ℝ V Fact.out).orientation

/-- `ABCD` is a strictly convex quadrilateral with the vertices in that
cyclic order: the four consecutive edge cross products all have the same
strict sign (positive for counterclockwise, negative for clockwise
orientation). This is a standard analytic characterization, equivalent to
each side's line having the other two vertices strictly on the same side
(and to the two diagonals crossing internally). -/
def ConvexQuadrilateral (A B C D : Pt) : Prop :=
  (0 < planeOrientation.areaForm (B -ᵥ A) (C -ᵥ B) ∧
    0 < planeOrientation.areaForm (C -ᵥ B) (D -ᵥ C) ∧
    0 < planeOrientation.areaForm (D -ᵥ C) (A -ᵥ D) ∧
    0 < planeOrientation.areaForm (A -ᵥ D) (B -ᵥ A)) ∨
  (planeOrientation.areaForm (B -ᵥ A) (C -ᵥ B) < 0 ∧
    planeOrientation.areaForm (C -ᵥ B) (D -ᵥ C) < 0 ∧
    planeOrientation.areaForm (D -ᵥ C) (A -ᵥ D) < 0 ∧
    planeOrientation.areaForm (A -ᵥ D) (B -ᵥ A) < 0)

/-- The rotation by 90° associated with `planeOrientation`. -/
noncomputable def rot90 : V ≃ₗᵢ[ℝ] V := planeOrientation.rightAngleRotation

@[simp] lemma inner_rot90_left (x y : V) :
    ⟪rot90 x, y⟫ = planeOrientation.areaForm x y :=
  planeOrientation.inner_rightAngleRotation_left x y

@[simp] lemma inner_rot90_right (x y : V) :
    ⟪x, rot90 y⟫ = -planeOrientation.areaForm x y :=
  planeOrientation.inner_rightAngleRotation_right x y

@[simp] lemma rot90_rot90 (x : V) : rot90 (rot90 x) = -x :=
  planeOrientation.rightAngleRotation_rightAngleRotation x

@[simp] lemma inner_rot90_rot90 (x y : V) : ⟪rot90 x, rot90 y⟫ = ⟪x, y⟫ :=
  planeOrientation.inner_comp_rightAngleRotation x y

@[simp] lemma norm_rot90 (x : V) : ‖rot90 x‖ = ‖x‖ :=
  LinearIsometryEquiv.norm_map _ x

@[simp] lemma inner_rot90_self (x : V) : ⟪rot90 x, x⟫ = 0 :=
  planeOrientation.inner_rightAngleRotation_self x

@[simp] lemma areaForm_self (x : V) : planeOrientation.areaForm x x = 0 := by
  rw [← inner_rot90_left, inner_rot90_self]

@[simp] lemma areaForm_swap (x y : V) :
    planeOrientation.areaForm x y = -planeOrientation.areaForm y x :=
  planeOrientation.areaForm_swap x y

@[simp] lemma areaForm_neg_left (x y : V) :
    planeOrientation.areaForm (-x) y = -planeOrientation.areaForm x y := by
  rw [show planeOrientation.areaForm (-x) = -(planeOrientation.areaForm x) from
    map_neg _ _, LinearMap.neg_apply]

@[simp] lemma areaForm_neg_right (x y : V) :
    planeOrientation.areaForm x (-y) = -planeOrientation.areaForm x y := by
  rw [areaForm_swap, areaForm_neg_left, neg_neg]
  exact areaForm_swap y x

/-- Any vector decomposes in the orthogonal basis `{u, J u}` (where `J` is
the rotation by 90 degrees of `planeOrientation`). This is the workhorse for
all coefficient computations below: a vector in the plane is determined by
its inner products with `u` and `J u` (via the Lagrange identity
`Orientation.inner_sq_add_areaForm_sq`). -/
lemma eq_smul_add_smul_rightAngleRotation (z u : V) (hu : u ≠ 0) :
    z = (⟪z, u⟫ / ‖u‖ ^ 2) • u + (⟪z, rot90 u⟫ / ‖u‖ ^ 2) • rot90 u := by
  have hu2 : ‖u‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hu)
  set w := z - ((⟪z, u⟫ / ‖u‖ ^ 2) • u + (⟪z, rot90 u⟫ / ‖u‖ ^ 2) • rot90 u) with hw
  have h1 : ⟪w, u⟫ = 0 := by
    rw [hw, inner_sub_left, inner_add_left, real_inner_smul_left,
      real_inner_smul_left, real_inner_self_eq_norm_sq, inner_rot90_self, mul_zero,
      add_zero, div_mul_cancel₀ _ hu2, sub_self]
  have h2 : ⟪w, rot90 u⟫ = 0 := by
    have hJJ : ⟪rot90 u, rot90 u⟫ = ‖u‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, inner_rot90_rot90]
    rw [hw, inner_sub_left, inner_add_left, real_inner_smul_left,
      real_inner_smul_left, inner_rot90_right, inner_rot90_right, areaForm_self,
      neg_zero, mul_zero, zero_add, hJJ, div_mul_cancel₀ _ hu2, sub_self]
  have hω2 : planeOrientation.areaForm w u = 0 := by
    rw [← neg_eq_zero, ← inner_rot90_right, h2]
  have hlag := planeOrientation.inner_sq_add_areaForm_sq w u
  rw [h1, hω2] at hlag
  have h0 : (0:ℝ) = ‖w‖ ^ 2 * ‖u‖ ^ 2 := by
    calc (0:ℝ) = (0:ℝ) ^ 2 + (0:ℝ) ^ 2 := by norm_num
      _ = ‖w‖ ^ 2 * ‖u‖ ^ 2 := hlag
  have hwz : w = 0 := by
    rcases mul_eq_zero.mp h0.symm with h | h
    · rw [sq_eq_zero_iff, norm_eq_zero] at h
      exact h
    · exact absurd h hu2
  rw [hw, sub_eq_zero] at hwz
  exact hwz

/-- If the determinant of `Z -ᵥ B` with `A -ᵥ B` vanishes, then `Z` lies on
the line through `B` and `A`. -/
lemma mem_line_of_areaForm_eq_zero {A B Z : Pt} (hu : A -ᵥ B ≠ 0)
    (h : planeOrientation.areaForm (Z -ᵥ B) (A -ᵥ B) = 0) :
    Z ∈ line[ℝ, B, A] := by
  set u := A -ᵥ B with hu_def
  have hB : B ∈ line[ℝ, B, A] := left_mem_affineSpan_pair ℝ B A
  have hdec := eq_smul_add_smul_rightAngleRotation (Z -ᵥ B) u hu
  have hβ : ⟪Z -ᵥ B, rot90 u⟫ = 0 := by
    have h2 := inner_rot90_right (Z -ᵥ B) u
    rw [h] at h2
    linarith [h2]
  rw [hβ, zero_div, zero_smul, add_zero] at hdec
  rw [show Z = (Z -ᵥ B) +ᵥ B from (vsub_vadd Z B).symm,
    AffineSubspace.vadd_mem_iff_mem_direction _ hB, direction_affineSpan,
    vectorSpan_pair_rev, hdec]
  exact Submodule.mem_span_singleton.mpr ⟨⟪Z -ᵥ B, u⟫ / ‖u‖ ^ 2, rfl⟩

/-- Sidedness over a line in determinant form: two points are strictly on
the same side of the line through `B` and `A` iff their determinants with
the direction `A -ᵥ B` have the same strict sign. This is the bridge
between mathlib's `AffineSubspace.SSameSide` and `areaForm` sign
computations. -/
lemma sSameSide_iff_areaForm_mul_pos {A B X Y : Pt} (hu : A -ᵥ B ≠ 0) :
    line[ℝ, B, A].SSameSide X Y ↔
      0 < planeOrientation.areaForm (X -ᵥ B) (A -ᵥ B) *
        planeOrientation.areaForm (Y -ᵥ B) (A -ᵥ B) := by
  set u := A -ᵥ B with hu_def
  have hB : B ∈ line[ℝ, B, A] := left_mem_affineSpan_pair ℝ B A
  have hspan : ∀ p : Pt, p ∈ line[ℝ, B, A] → ∃ c : ℝ, c • u = p -ᵥ B := by
    intro p hp
    have h1 : p -ᵥ B ∈ line[ℝ, B, A].direction :=
      AffineSubspace.vsub_mem_direction hp hB
    rw [direction_affineSpan, vectorSpan_pair_rev] at h1
    exact Submodule.mem_span_singleton.mp h1
  have hzero : ∀ p : Pt, p ∈ line[ℝ, B, A] →
      planeOrientation.areaForm (p -ᵥ B) u = 0 := by
    intro p hp
    obtain ⟨c, hc⟩ := hspan p hp
    rw [← hc, map_smul, LinearMap.smul_apply, areaForm_self, smul_zero]
  constructor
  · rintro ⟨hW, hXn, hYn⟩
    obtain ⟨p₁, hp₁, p₂, hp₂, hray⟩ := hW
    have hX0 : X -ᵥ p₁ ≠ 0 := by
      intro h
      have hXp : X = p₁ := vsub_eq_zero_iff_eq.mp h
      subst hXp
      exact hXn hp₁
    have hY0 : Y -ᵥ p₂ ≠ 0 := by
      intro h
      have hYp : Y = p₂ := vsub_eq_zero_iff_eq.mp h
      subst hYp
      exact hYn hp₂
    obtain ⟨r₁, r₂, hr₁, hr₂, hrr⟩ := hray.exists_pos hX0 hY0
    have h1 : planeOrientation.areaForm (X -ᵥ p₁) u = planeOrientation.areaForm (X -ᵥ B) u := by
      have e : X -ᵥ p₁ = (X -ᵥ B) - (p₁ -ᵥ B) := (vsub_sub_vsub_cancel_right X p₁ B).symm
      rw [e, map_sub, LinearMap.sub_apply, hzero p₁ hp₁, sub_zero]
    have h2 : planeOrientation.areaForm (Y -ᵥ p₂) u = planeOrientation.areaForm (Y -ᵥ B) u := by
      have e : Y -ᵥ p₂ = (Y -ᵥ B) - (p₂ -ᵥ B) := (vsub_sub_vsub_cancel_right Y p₂ B).symm
      rw [e, map_sub, LinearMap.sub_apply, hzero p₂ hp₂, sub_zero]
    have h3 : r₁ * planeOrientation.areaForm (X -ᵥ B) u =
        r₂ * planeOrientation.areaForm (Y -ᵥ B) u := by
      have h4 := congrArg (fun z : V => planeOrientation.areaForm z u) hrr
      rw [map_smul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul,
        smul_eq_mul, h1, h2] at h4
      exact h4
    have hafX : planeOrientation.areaForm (X -ᵥ B) u ≠ 0 := by
      intro h0
      exact hXn (mem_line_of_areaForm_eq_zero hu h0)
    have hafY : planeOrientation.areaForm (Y -ᵥ B) u ≠ 0 := by
      intro h0
      exact hYn (mem_line_of_areaForm_eq_zero hu h0)
    have h6 : r₂ * (planeOrientation.areaForm (X -ᵥ B) u *
        planeOrientation.areaForm (Y -ᵥ B) u) =
        r₁ * (planeOrientation.areaForm (X -ᵥ B) u) ^ 2 := by
      linear_combination planeOrientation.areaForm (X -ᵥ B) u * h3.symm
    have h7 : 0 < r₁ * (planeOrientation.areaForm (X -ᵥ B) u) ^ 2 :=
      mul_pos hr₁ (pow_two_pos_of_ne_zero hafX)
    rw [← h6] at h7
    exact pos_of_mul_pos_right h7 hr₂.le
  · intro hprod
    have haf1 : planeOrientation.areaForm (X -ᵥ B) u ≠ 0 := by
      intro h
      rw [h, zero_mul] at hprod
      exact lt_irrefl _ hprod
    have haf2 : planeOrientation.areaForm (Y -ᵥ B) u ≠ 0 := by
      intro h
      rw [h, mul_zero] at hprod
      exact lt_irrefl _ hprod
    have hu2 : ‖u‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hu)
    have hdecX := eq_smul_add_smul_rightAngleRotation (X -ᵥ B) u hu
    have hdecY := eq_smul_add_smul_rightAngleRotation (Y -ᵥ B) u hu
    set β₁ : ℝ := ⟪X -ᵥ B, rot90 u⟫ / ‖u‖ ^ 2 with hβ₁def
    set β₂ : ℝ := ⟪Y -ᵥ B, rot90 u⟫ / ‖u‖ ^ 2 with hβ₂def
    have hβ₁ : β₁ = -planeOrientation.areaForm (X -ᵥ B) u / ‖u‖ ^ 2 := by
      rw [hβ₁def, inner_rot90_right, neg_div]
    have hβ₂ : β₂ = -planeOrientation.areaForm (Y -ᵥ B) u / ‖u‖ ^ 2 := by
      rw [hβ₂def, inner_rot90_right, neg_div]
    have hβ1 : β₁ ≠ 0 := by
      rw [hβ₁]
      exact div_ne_zero (neg_ne_zero.mpr haf1) hu2
    have hβ2 : β₂ ≠ 0 := by
      rw [hβ₂]
      exact div_ne_zero (neg_ne_zero.mpr haf2) hu2
    have hββ : 0 < β₁ * β₂ := by
      rw [hβ₁, hβ₂, neg_div, neg_div, neg_mul_neg, div_mul_div_comm]
      exact div_pos hprod (mul_pos (pow_pos (norm_pos_iff.mpr hu) 2)
        (pow_pos (norm_pos_iff.mpr hu) 2))
    have hβpos : 0 < β₂ / β₁ := by
      rcases mul_pos_iff.mp hββ with h | h
      · exact div_pos h.2 h.1
      · exact div_pos_of_neg_of_neg h.2 h.1
    refine ⟨⟨((X -ᵥ B) - β₁ • rot90 u) +ᵥ B, ?_, ((Y -ᵥ B) - β₂ • rot90 u) +ᵥ B, ?_,
      ?_⟩, ?_, ?_⟩
    · have h2 := hdecX
      have h1 : (X -ᵥ B) - β₁ • rot90 u = (⟪X -ᵥ B, u⟫ / ‖u‖ ^ 2) • u := by
        nth_rewrite 1 [h2]
        abel
      rw [AffineSubspace.vadd_mem_iff_mem_direction _ hB, direction_affineSpan,
        vectorSpan_pair_rev, h1]
      exact Submodule.mem_span_singleton.mpr ⟨⟪X -ᵥ B, u⟫ / ‖u‖ ^ 2, rfl⟩
    · have h2 := hdecY
      have h1 : (Y -ᵥ B) - β₂ • rot90 u = (⟪Y -ᵥ B, u⟫ / ‖u‖ ^ 2) • u := by
        nth_rewrite 1 [h2]
        abel
      rw [AffineSubspace.vadd_mem_iff_mem_direction _ hB, direction_affineSpan,
        vectorSpan_pair_rev, h1]
      exact Submodule.mem_span_singleton.mpr ⟨⟪Y -ᵥ B, u⟫ / ‖u‖ ^ 2, rfl⟩
    · have e1 : X -ᵥ (((X -ᵥ B) - β₁ • rot90 u) +ᵥ B) = β₁ • rot90 u := by
        rw [vsub_vadd_eq_vsub_sub]
        abel
      have e2 : Y -ᵥ (((Y -ᵥ B) - β₂ • rot90 u) +ᵥ B) = β₂ • rot90 u := by
        rw [vsub_vadd_eq_vsub_sub]
        abel
      rw [e1, e2, show β₂ • rot90 u = (β₂ / β₁) • (β₁ • rot90 u) from by
        rw [smul_smul, div_mul_cancel₀ _ hβ1]]
      exact SameRay.sameRay_pos_smul_right _ hβpos
    · intro hXl
      exact haf1 (hzero X hXl)
    · intro hYl
      exact haf2 (hzero Y hYl)

/-- A vector in the plane is zero if its determinants with two independent
vectors both vanish (`areaForm` is nondegenerate on a basis). -/
lemma eq_zero_of_areaForm_eq_zero_eq_zero {z u v : V} (hu : u ≠ 0)
    (hω : planeOrientation.areaForm u v ≠ 0)
    (h1 : planeOrientation.areaForm z u = 0) (h2 : planeOrientation.areaForm z v = 0) :
    z = 0 := by
  have h3 : ⟪z, rot90 u⟫ = 0 := by
    have h := inner_rot90_right z u
    rw [h1] at h
    linarith [h]
  have h4 : ⟪z, u⟫ = 0 := by
    have hdec := eq_smul_add_smul_rightAngleRotation (rot90 v) u hu
    have hc1 : ⟪rot90 v, u⟫ = -planeOrientation.areaForm u v := by
      rw [inner_rot90_left, areaForm_swap]
    have hc2 : ⟪rot90 v, rot90 u⟫ = ⟪u, v⟫ := by
      rw [inner_rot90_rot90, real_inner_comm]
    rw [hc1, hc2] at hdec
    have h5 : ⟪z, rot90 v⟫ = 0 := by
      have h := inner_rot90_right z v
      rw [h2] at h
      linarith [h]
    have h6 : ⟪z, rot90 v⟫ = (-planeOrientation.areaForm u v / ‖u‖ ^ 2) * ⟪z, u⟫ +
        (⟪u, v⟫ / ‖u‖ ^ 2) * ⟪z, rot90 u⟫ := by
      conv_lhs => rw [hdec]
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
    have h8 : (-planeOrientation.areaForm u v / ‖u‖ ^ 2) * ⟪z, u⟫ = 0 := by
      rw [h5, h3, mul_zero, add_zero] at h6
      exact h6.symm
    rcases mul_eq_zero.mp h8 with h | h
    · exact absurd h
        (div_ne_zero (neg_ne_zero.mpr hω) (pow_ne_zero 2 (norm_ne_zero_iff.mpr hu)))
    · exact h
  have h9 := eq_smul_add_smul_rightAngleRotation z u hu
  rw [h4, h3, zero_div, zero_smul, zero_smul, add_zero] at h9
  exact h9

/-- Two vectors with componentwise-proportional determinants against a
basis are proportional. -/
lemma smul_of_areaForm_smul_areaForm {x₁ x₂ u v : V} {c : ℝ}
    (hu : u ≠ 0) (hω : planeOrientation.areaForm u v ≠ 0)
    (h1 : planeOrientation.areaForm x₂ u = c * planeOrientation.areaForm x₁ u)
    (h2 : planeOrientation.areaForm x₂ v = c * planeOrientation.areaForm x₁ v) :
    x₂ = c • x₁ := by
  have h3 : planeOrientation.areaForm (x₂ - c • x₁) u = 0 := by
    rw [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, h1,
      sub_self]
  have h4 : planeOrientation.areaForm (x₂ - c • x₁) v = 0 := by
    rw [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, h2,
      sub_self]
  have h5 := eq_zero_of_areaForm_eq_zero_eq_zero hu hω h3 h4
  exact sub_eq_zero.mp h5

/-- The center proportionality pattern: two centers whose signed normal
components against the two side directions match the same sign pattern
(with an overall sign `s = ±1` flipping the ratio) are proportional. The
signed normal component of a center is the signed distance to the side
line times the side length, in determinant form. -/
lemma smul_of_areaForm_pattern {x₁ x₂ u v : V} {ρ₁ ρ₂ s su sv : ℝ}
    (hu : u ≠ 0) (hω : planeOrientation.areaForm u v ≠ 0)
    (hρ₁ : 0 < ρ₁) (_hρ₂ : 0 < ρ₂) (_hs : s = 1 ∨ s = -1)
    (h1₁ : planeOrientation.areaForm x₁ u * planeOrientation.areaForm u v =
      su * (ρ₁ * ‖u‖ * |planeOrientation.areaForm u v|))
    (h2₁ : planeOrientation.areaForm x₁ v * planeOrientation.areaForm u v =
      sv * (ρ₁ * ‖v‖ * |planeOrientation.areaForm u v|))
    (h1₂ : planeOrientation.areaForm x₂ u * planeOrientation.areaForm u v =
      (s * su) * (ρ₂ * ‖u‖ * |planeOrientation.areaForm u v|))
    (h2₂ : planeOrientation.areaForm x₂ v * planeOrientation.areaForm u v =
      (s * sv) * (ρ₂ * ‖v‖ * |planeOrientation.areaForm u v|)) :
    x₂ = (s * (ρ₂ / ρ₁)) • x₁ := by
  have e1 : planeOrientation.areaForm x₂ u = (s * ρ₂ / ρ₁) * planeOrientation.areaForm x₁ u := by
    have h5 : ρ₁ * planeOrientation.areaForm x₂ u = (s * ρ₂) * planeOrientation.areaForm x₁ u := by
      have h6 : (ρ₁ * planeOrientation.areaForm x₂ u - (s * ρ₂) * planeOrientation.areaForm x₁ u) *
          planeOrientation.areaForm u v = 0 := by
        linear_combination ρ₁ * h1₂ - s * ρ₂ * h1₁
      rcases mul_eq_zero.mp h6 with h | h
      · linarith [h]
      · exact absurd h hω
    rw [div_mul_eq_mul_div, eq_div_iff hρ₁.ne']
    linarith [h5]
  have e2 : planeOrientation.areaForm x₂ v = (s * ρ₂ / ρ₁) * planeOrientation.areaForm x₁ v := by
    have h5 : ρ₁ * planeOrientation.areaForm x₂ v = (s * ρ₂) * planeOrientation.areaForm x₁ v := by
      have h6 : (ρ₁ * planeOrientation.areaForm x₂ v - (s * ρ₂) * planeOrientation.areaForm x₁ v) *
          planeOrientation.areaForm u v = 0 := by
        linear_combination ρ₁ * h2₂ - s * ρ₂ * h2₁
      rcases mul_eq_zero.mp h6 with h | h
      · linarith [h]
      · exact absurd h hω
    rw [div_mul_eq_mul_div, eq_div_iff hρ₁.ne']
    linarith [h5]
  have h := smul_of_areaForm_smul_areaForm hu hω e1 e2
  rw [mul_div_assoc] at h
  exact h

/-- The opposite-side version of the bridge (forward direction): points
strictly on opposite sides of the line have determinants of opposite
strict signs. -/
lemma sOppSide_areaForm_mul_neg {A B X Y : Pt} (hu : A -ᵥ B ≠ 0)
    (h : line[ℝ, B, A].SOppSide X Y) :
    planeOrientation.areaForm (X -ᵥ B) (A -ᵥ B) *
      planeOrientation.areaForm (Y -ᵥ B) (A -ᵥ B) < 0 := by
  set u := A -ᵥ B with hu_def
  obtain ⟨hW, hXn, hYn⟩ := h
  obtain ⟨p₁, hp₁, p₂, hp₂, hray⟩ := hW
  have hB : B ∈ line[ℝ, B, A] := left_mem_affineSpan_pair ℝ B A
  have hzero : ∀ p : Pt, p ∈ line[ℝ, B, A] →
      planeOrientation.areaForm (p -ᵥ B) u = 0 := by
    intro p hp
    have h1 : p -ᵥ B ∈ line[ℝ, B, A].direction :=
      AffineSubspace.vsub_mem_direction hp hB
    rw [direction_affineSpan, vectorSpan_pair_rev] at h1
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h1
    rw [← hc, map_smul, LinearMap.smul_apply, areaForm_self, smul_zero]
  have hX0 : X -ᵥ p₁ ≠ 0 := by
    intro h0
    have hXp : X = p₁ := vsub_eq_zero_iff_eq.mp h0
    subst hXp
    exact hXn hp₁
  have hY0 : Y -ᵥ p₂ ≠ 0 := by
    intro h0
    have hYp : Y = p₂ := vsub_eq_zero_iff_eq.mp h0
    subst hYp
    exact hYn hp₂
  obtain ⟨r₁, r₂, hr₁, hr₂, hrr⟩ :=
    hray.exists_pos hX0 (vsub_ne_zero.mpr (vsub_ne_zero.mp hY0).symm)
  have h1 : planeOrientation.areaForm (X -ᵥ p₁) u = planeOrientation.areaForm (X -ᵥ B) u := by
    have e : X -ᵥ p₁ = (X -ᵥ B) - (p₁ -ᵥ B) := (vsub_sub_vsub_cancel_right X p₁ B).symm
    rw [e, map_sub, LinearMap.sub_apply, hzero p₁ hp₁, sub_zero]
  have h2 : planeOrientation.areaForm (p₂ -ᵥ Y) u = -planeOrientation.areaForm (Y -ᵥ B) u := by
    have e : p₂ -ᵥ Y = (p₂ -ᵥ B) - (Y -ᵥ B) := (vsub_sub_vsub_cancel_right p₂ Y B).symm
    rw [e, map_sub, LinearMap.sub_apply, hzero p₂ hp₂, zero_sub]
  have h3 : r₁ * planeOrientation.areaForm (X -ᵥ B) u =
      -(r₂ * planeOrientation.areaForm (Y -ᵥ B) u) := by
    have h4 := congrArg (fun z : V => planeOrientation.areaForm z u) hrr
    rw [map_smul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul,
      smul_eq_mul, h1, h2, mul_neg] at h4
    exact h4
  have hafX : r₁ * planeOrientation.areaForm (X -ᵥ B) u ≠ 0 := by
    intro h8
    rcases mul_eq_zero.mp h8 with h' | h'
    · linarith [h', hr₁]
    · exact hXn (mem_line_of_areaForm_eq_zero hu h')
  have h5 : r₁ * r₂ * (planeOrientation.areaForm (X -ᵥ B) u *
      planeOrientation.areaForm (Y -ᵥ B) u) < 0 := by
    have h6 : r₁ * r₂ * (planeOrientation.areaForm (X -ᵥ B) u *
        planeOrientation.areaForm (Y -ᵥ B) u) =
        (r₁ * planeOrientation.areaForm (X -ᵥ B) u) *
          (r₂ * planeOrientation.areaForm (Y -ᵥ B) u) := by ring
    rw [h6]
    have h8 : (r₁ * planeOrientation.areaForm (X -ᵥ B) u) *
        (r₂ * planeOrientation.areaForm (Y -ᵥ B) u) =
        -(r₁ * planeOrientation.areaForm (X -ᵥ B) u) ^ 2 := by
      have e : r₂ * planeOrientation.areaForm (Y -ᵥ B) u =
          -(r₁ * planeOrientation.areaForm (X -ᵥ B) u) := by linarith [h3]
      rw [e]
      ring
    rw [h8]
    have h10 : 0 < (r₁ * planeOrientation.areaForm (X -ᵥ B) u) ^ 2 :=
      pow_two_pos_of_ne_zero hafX
    linarith [h10]
  rcases mul_neg_iff.mp h5 with h | h
  · exact h.2
  · linarith [h.1, mul_pos hr₁ hr₂]

omit [Fact (finrank ℝ V = 2)] in
/-- If `s • u` is on the same ray as `u` and `u ≠ 0`, then `s ≥ 0`. -/
lemma nonneg_of_sameRay_smul {u : V} {s : ℝ} (hu : u ≠ 0) (h : SameRay ℝ (s • u) u) :
    0 ≤ s := by
  rcases eq_or_ne s 0 with h0 | h0
  · rw [h0]
  · by_contra hneg
    rw [not_le] at hneg
    obtain ⟨r₁, r₂, hr₁, hr₂, hrr⟩ := h.exists_pos (smul_ne_zero h0 hu) hu
    have e : (r₁ * s) • u = r₂ • u := by
      rw [smul_smul] at hrr
      exact hrr
    have h1 : (r₁ * s - r₂) • u = 0 := by
      rw [sub_smul, sub_eq_zero]
      exact e
    rcases smul_eq_zero.mp h1 with h' | h'
    · nlinarith [h', hr₁, hr₂, hneg]
    · exact hu h'

omit [Fact (finrank ℝ V = 2)] in
/-- Two points on the same segment with the same distance to the segment's
end are equal. -/
lemma eq_of_dist_eq_of_wbtw {A C X Y : Pt} (hAC : A ≠ C)
    (hX : Wbtw ℝ A X C) (hY : Wbtw ℝ A Y C)
    (hd : dist C X = dist C Y) : X = Y := by
  have hu : C -ᵥ A ≠ 0 := vsub_ne_zero.mpr hAC.symm
  have hparam : ∀ Z : Pt, Wbtw ℝ A Z C → ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ Z -ᵥ A = s • (C -ᵥ A) := by
    intro Z hZ
    have hsr := hZ.sameRay_vsub
    rcases eq_or_ne (Z -ᵥ A) 0 with h0 | h0
    · exact ⟨0, le_refl 0, by norm_num, by rw [h0, zero_smul]⟩
    · rcases eq_or_ne (C -ᵥ Z) 0 with h0' | h0'
      · have hZC : Z = C := (vsub_eq_zero_iff_eq.mp h0').symm
        exact ⟨1, by norm_num, le_refl 1, by rw [hZC, one_smul]⟩
      · obtain ⟨r₁, r₂, hr₁, hr₂, hrr⟩ := hsr.exists_pos h0 h0'
        have hpos : 0 < r₁ + r₂ := add_pos hr₁ hr₂
        have e : (r₁ + r₂) • (Z -ᵥ A) = r₂ • (C -ᵥ A) := by
          have e1 : C -ᵥ Z = (C -ᵥ A) - (Z -ᵥ A) := (vsub_sub_vsub_cancel_right C Z A).symm
          rw [e1, smul_sub] at hrr
          rw [add_smul, hrr]
          abel
        refine ⟨r₂ / (r₁ + r₂), div_nonneg hr₂.le hpos.le, ?_, ?_⟩
        · rw [div_le_one hpos]
          linarith [hr₁]
        · have e2 : Z -ᵥ A = (r₁ + r₂)⁻¹ • (r₂ • (C -ᵥ A)) := by
            rw [← e, smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]
          rw [e2, smul_smul, div_eq_inv_mul]
  obtain ⟨s₁, hs₁0, hs₁1, hs₁⟩ := hparam X hX
  obtain ⟨s₂, hs₂0, hs₂1, hs₂⟩ := hparam Y hY
  have hCX : dist C X = (1 - s₁) * ‖C -ᵥ A‖ := by
    have e : C -ᵥ X = (1 - s₁) • (C -ᵥ A) := by
      have e1 : C -ᵥ X = (C -ᵥ A) - (X -ᵥ A) := (vsub_sub_vsub_cancel_right C X A).symm
      rw [e1, hs₁, sub_smul, one_smul]
    rw [dist_eq_norm_vsub, e, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [hs₁1])]
  have hCY : dist C Y = (1 - s₂) * ‖C -ᵥ A‖ := by
    have e : C -ᵥ Y = (1 - s₂) • (C -ᵥ A) := by
      have e1 : C -ᵥ Y = (C -ᵥ A) - (Y -ᵥ A) := (vsub_sub_vsub_cancel_right C Y A).symm
      rw [e1, hs₂, sub_smul, one_smul]
    rw [dist_eq_norm_vsub, e, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [hs₂1])]
  have hs12 : s₁ = s₂ := by
    have h0 : (1 - s₁) * ‖C -ᵥ A‖ = (1 - s₂) * ‖C -ᵥ A‖ := by rw [← hCX, ← hCY, hd]
    have hune : ‖C -ᵥ A‖ ≠ 0 := norm_ne_zero_iff.mpr hu
    have h1 : 1 - s₁ = 1 - s₂ := by
      rcases mul_eq_mul_right_iff.mp h0 with h | h
      · exact h
      · exact absurd h hune
    linarith [h1]
  have h2 : X -ᵥ A = Y -ᵥ A := by rw [hs₁, hs₂, hs12]
  exact vsub_eq_zero_iff_eq.mp (by rw [← vsub_sub_vsub_cancel_right X Y A, h2, sub_self])

/-- Decomposition of a vector `z` in the orthogonal basis `{u, J u}` of an
oriented plane, where `J` is the rotation by 90 degrees (version with the
orientation as an explicit argument). -/
lemma eq_smul_add_smul_rightAngleRotation' (o : Orientation ℝ V (Fin 2)) (z u : V)
    (hu : u ≠ 0) :
    z = (⟪z, u⟫ / ‖u‖ ^ 2) • u + (⟪z, o.rightAngleRotation u⟫ / ‖u‖ ^ 2) •
      o.rightAngleRotation u := by
  have hu2 : ‖u‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hu)
  have hJu : ⟪o.rightAngleRotation u, u⟫ = 0 := o.inner_rightAngleRotation_self u
  have huJ : ⟪u, o.rightAngleRotation u⟫ = 0 := by
    rw [o.inner_rightAngleRotation_right, o.areaForm_apply_self, neg_zero]
  have hJJ : ⟪o.rightAngleRotation u, o.rightAngleRotation u⟫ = ‖u‖ ^ 2 := by
    rw [o.inner_comp_rightAngleRotation, real_inner_self_eq_norm_sq]
  set w := z - ((⟪z, u⟫ / ‖u‖ ^ 2) • u + (⟪z, o.rightAngleRotation u⟫ / ‖u‖ ^ 2) •
    o.rightAngleRotation u) with hw
  have e1 : ⟪w, u⟫ = 0 := by
    rw [hw, inner_sub_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq, hJu, mul_zero, add_zero, div_mul_cancel₀ _ hu2, sub_self]
  have e2 : ⟪w, o.rightAngleRotation u⟫ = 0 := by
    rw [hw, inner_sub_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      huJ, hJJ, mul_zero, zero_add, div_mul_cancel₀ _ hu2, sub_self]
  have e3 : o.areaForm w u = 0 := by
    have h := e2
    rw [o.inner_rightAngleRotation_right] at h
    exact neg_eq_zero.mp h
  have lag := o.inner_sq_add_areaForm_sq w u
  rw [e1, e3] at lag
  have hwnorm : ‖w‖ = 0 := by
    have h0 : ‖w‖ ^ 2 * ‖u‖ ^ 2 = 0 := by
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add] at lag
      exact lag.symm
    rcases mul_eq_zero.mp h0 with h | h
    · exact (pow_eq_zero_iff (n := 2) two_ne_zero).mp h
    · exact absurd h hu2
  have hwz : w = 0 := norm_eq_zero.mp hwnorm
  rw [hw] at hwz
  exact sub_eq_zero.mp hwz

/-- In an oriented plane, if a vector `x` has prescribed signed projections
onto the normals of two independent vectors `u`, `v` (with magnitudes `r`
times `‖u‖`, `‖v‖` and the shown signs), then `⟪x, u⟫ < 0`. This is the
computational heart of the "angle wedge" argument at the vertex `D`: the
excircle center lies in the wedge vertically opposite to the one spanned by
the two sides, so its projection onto each side falls beyond the vertex. -/
lemma inner_neg_of_areaForm_mul {o : Orientation ℝ V (Fin 2)} {x u v : V} {r : ℝ}
    (hu : u ≠ 0) (hω : o.areaForm u v ≠ 0) (hr : 0 < r)
    (h1 : o.areaForm x u * o.areaForm u v = r * ‖u‖ * |o.areaForm u v|)
    (h2 : o.areaForm x v * o.areaForm u v = -r * ‖v‖ * |o.areaForm u v|) :
    ⟪x, u⟫ < 0 := by
  have hωxu : o.areaForm x u = -⟪x, o.rightAngleRotation u⟫ := by
    rw [o.inner_rightAngleRotation_right x u, neg_neg]
  rw [hωxu] at h1
  have hdec := eq_smul_add_smul_rightAngleRotation' o (o.rightAngleRotation v) u hu
  have hc1 : ⟪o.rightAngleRotation v, u⟫ = -o.areaForm u v := by
    rw [o.inner_rightAngleRotation_left, o.areaForm_swap]
  have hc2 : ⟪o.rightAngleRotation v, o.rightAngleRotation u⟫ = ⟪u, v⟫ := by
    rw [o.inner_comp_rightAngleRotation, real_inner_comm]
  rw [hc1, hc2] at hdec
  have hωxv : ‖u‖ ^ 2 * o.areaForm x v
      = ⟪x, u⟫ * o.areaForm u v - ⟪x, o.rightAngleRotation u⟫ * ⟪u, v⟫ := by
    have h : ⟪x, o.rightAngleRotation v⟫
        = (-o.areaForm u v / ‖u‖ ^ 2) * ⟪x, u⟫
          + (⟪u, v⟫ / ‖u‖ ^ 2) * ⟪x, o.rightAngleRotation u⟫ := by
      conv_lhs => rw [hdec]
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
    have h2a : o.areaForm x v = -⟪x, o.rightAngleRotation v⟫ := by
      rw [o.inner_rightAngleRotation_right x v, neg_neg]
    have hu2 : ‖u‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hu)
    rw [h2a, h]
    field_simp
    ring
  have hkey : o.areaForm u v ^ 2 * ⟪x, u⟫
      = -r * ‖u‖ * |o.areaForm u v| * (‖u‖ * ‖v‖ + ⟪u, v⟫) := by
    linear_combination -o.areaForm u v * hωxv + ‖u‖ ^ 2 * h2 - ⟪u, v⟫ * h1
  have hu_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hv : v ≠ 0 := by
    intro h'
    apply hω
    rw [h']
    exact map_zero _
  have hv_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hW2 : 0 < o.areaForm u v ^ 2 := pow_two_pos_of_ne_zero hω
  have hLag := o.inner_sq_add_areaForm_sq u v
  have hCS : |⟪u, v⟫| < ‖u‖ * ‖v‖ := by
    have hsq : ⟪u, v⟫ ^ 2 < (‖u‖ * ‖v‖) ^ 2 := by nlinarith [hLag, hW2]
    exact abs_lt_of_sq_lt_sq hsq (mul_nonneg hu_pos.le hv_pos.le)
  have hS : 0 < ‖u‖ * ‖v‖ + ⟪u, v⟫ := by
    have h' := abs_lt.mp hCS
    linarith
  have hRHS : -r * ‖u‖ * |o.areaForm u v| * (‖u‖ * ‖v‖ + ⟪u, v⟫) < 0 := by
    have hp : 0 < r * ‖u‖ * |o.areaForm u v| * (‖u‖ * ‖v‖ + ⟪u, v⟫) :=
      mul_pos (mul_pos (mul_pos hr hu_pos) (abs_pos.mpr hω)) hS
    linarith
  nlinarith [hkey, hRHS, hW2]

omit [Fact (finrank ℝ V = 2)] in
/-- If `A` lies strictly between `B` and `T`, then `T -ᵥ A` is a positive
multiple of `A -ᵥ B`. -/
lemma exists_pos_smul_vsub_of_sbtw {A B T : Pt} (h : Sbtw ℝ B A T) :
    ∃ σ : ℝ, 0 < σ ∧ T -ᵥ A = σ • (A -ᵥ B) := by
  rcases h with ⟨hw, hne1, hne2⟩
  have hsame : SameRay ℝ (A -ᵥ B) (T -ᵥ A) := hw.sameRay_vsub
  obtain ⟨r₁, r₂, hr₁, hr₂, hrr⟩ :=
    hsame.exists_pos (vsub_ne_zero.mpr hne1) (vsub_ne_zero.mpr hne2.symm)
  refine ⟨r₁ / r₂, div_pos hr₁ hr₂, ?_⟩
  have e : T -ᵥ A = r₂⁻¹ • (r₁ • (A -ᵥ B)) := by
    rw [hrr, inv_smul_smul₀ hr₂.ne']
  rw [e, smul_smul, mul_comm r₂⁻¹ r₁, div_eq_mul_inv]

omit [Fact (finrank ℝ V = 2)] in
/-- The radius to a tangent point is perpendicular to the tangent subspace:
for any two points `X, Y` of the tangent subspace,
`⟪ω.center -ᵥ T, X -ᵥ Y⟫ = 0`. -/
lemma IsTangentAt.inner_vsub_center_eq_zero {ω : Sphere Pt} {T X Y : Pt}
    {ℓ : AffineSubspace ℝ Pt} (h : ω.IsTangentAt T ℓ) (hX : X ∈ ℓ) (hY : Y ∈ ℓ) :
    ⟪ω.center -ᵥ T, X -ᵥ Y⟫ = 0 := by
  have h1 := h.inner_left_eq_zero_of_mem hX
  have h2 := h.inner_left_eq_zero_of_mem hY
  have h3 : ⟪X -ᵥ Y, T -ᵥ ω.center⟫ = 0 := by
    have e : (X -ᵥ T) - (Y -ᵥ T) = X -ᵥ Y := vsub_sub_vsub_cancel_right X Y T
    rw [← e, inner_sub_left, h1, h2, sub_zero]
  have h4 : ⟪X -ᵥ Y, ω.center -ᵥ T⟫ = 0 := by
    rw [← neg_vsub_eq_vsub_rev T ω.center, inner_neg_right, h3, neg_zero]
  rw [show ⟪ω.center -ᵥ T, X -ᵥ Y⟫ = ⟪X -ᵥ Y, ω.center -ᵥ T⟫ by rw [real_inner_comm], h4]

/-- The normal component of the center offset has absolute value
`radius * ‖X -ᵥ Y‖`: for `X, Y` on the tangent subspace,
`|⟪ω.center -ᵥ T, rot90 (X -ᵥ Y)⟫| = ω.radius * ‖X -ᵥ Y‖`. This is
"distance from center to tangent line equals radius" in determinant form. -/
lemma IsTangentAt.abs_inner_vsub_center_rot90 {ω : Sphere Pt} {T X Y : Pt}
    {ℓ : AffineSubspace ℝ Pt} (h : ω.IsTangentAt T ℓ) (hX : X ∈ ℓ) (hY : Y ∈ ℓ)
    (hR : 0 < ω.radius) :
    |⟪ω.center -ᵥ T, rot90 (X -ᵥ Y)⟫| = ω.radius * ‖X -ᵥ Y‖ := by
  have hperp := IsTangentAt.inner_vsub_center_eq_zero h hX hY
  have hnormT : ‖ω.center -ᵥ T‖ = ω.radius := by
    have hT : dist T ω.center = ω.radius := h.mem_sphere
    rw [← hT, dist_comm, dist_eq_norm_vsub]
  have haf : planeOrientation.areaForm (ω.center -ᵥ T) (X -ᵥ Y) =
      -⟪ω.center -ᵥ T, rot90 (X -ᵥ Y)⟫ := by rw [inner_rot90_right, neg_neg]
  have hlag := planeOrientation.inner_sq_add_areaForm_sq (ω.center -ᵥ T) (X -ᵥ Y)
  rw [hperp, haf, hnormT] at hlag
  have hsq : ⟪ω.center -ᵥ T, rot90 (X -ᵥ Y)⟫ ^ 2 = (ω.radius * ‖X -ᵥ Y‖) ^ 2 := by
    nlinarith [hlag]
  exact (pow_left_inj₀ (abs_nonneg _) (mul_nonneg hR.le (norm_nonneg _)) two_ne_zero).mp
    (by rwa [sq_abs])

omit [Fact (finrank ℝ V = 2)] in
/-- The square of the length of a tangent segment from a point `q` to a
sphere equals the power of `q` with respect to the sphere. This is the key
computation behind "tangents from a common point are equal" and hence behind
the external version of the Pitot theorem (`BA + AD = CB + CD`) that the
official solution starts with. -/
lemma Sphere.IsTangentAt.dist_sq_eq {ω : Sphere Pt} {T q : Pt}
    {ℓ : AffineSubspace ℝ Pt} (h : ω.IsTangentAt T ℓ) (hq : q ∈ ℓ) :
    dist q T ^ 2 = dist q ω.center ^ 2 - ω.radius ^ 2 := by
  have hperp := h.inner_left_eq_zero_of_mem hq
  have hT : dist T ω.center = ω.radius := h.mem_sphere
  have e : (q -ᵥ T) + (T -ᵥ ω.center) = q -ᵥ ω.center := vsub_add_vsub_cancel q T ω.center
  have h2 : dist q ω.center ^ 2 = dist q T ^ 2 + dist T ω.center ^ 2 := by
    simp only [dist_eq_norm_vsub]
    rw [← e, norm_add_sq_real, hperp, mul_zero, add_zero]
  rw [hT] at h2
  linarith

omit [Fact (finrank ℝ V = 2)] in
/-- Tangents to a sphere from a common point have equal lengths. -/
lemma dist_eq_dist_of_isTangentAt {ω : Sphere Pt} {B T₁ T₂ : Pt}
    {ℓ₁ ℓ₂ : AffineSubspace ℝ Pt}
    (h₁ : ω.IsTangentAt T₁ ℓ₁) (hB₁ : B ∈ ℓ₁)
    (h₂ : ω.IsTangentAt T₂ ℓ₂) (hB₂ : B ∈ ℓ₂) :
    dist B T₁ = dist B T₂ := by
  have hsq : dist B T₁ ^ 2 = dist B T₂ ^ 2 := by
    rw [Sphere.IsTangentAt.dist_sq_eq h₁ hB₁, Sphere.IsTangentAt.dist_sq_eq h₂ hB₂]
  have hfactor : (dist B T₁ - dist B T₂) * (dist B T₁ + dist B T₂) = 0 := by
    linear_combination hsq
  have h1 : 0 ≤ dist B T₁ := dist_nonneg
  have h2 : 0 ≤ dist B T₂ := dist_nonneg
  rcases mul_eq_zero.mp hfactor with hsub | hsum <;> linarith

omit [Fact (finrank ℝ V = 2)] in
/-- Chord-radius identity: if a sphere is tangent to a subspace at `T`, then
for any point `X` of the sphere,
`⟪X -ᵥ T, ω.center -ᵥ T⟫ = ‖X -ᵥ T‖ ^ 2 / 2`. This is the computational
content of "a tangent hyperplane has the whole sphere on one side". -/
lemma IsTangentAt.inner_vsub_center_eq {ω : Sphere Pt} {T X : Pt}
    {ℓ : AffineSubspace ℝ Pt} (h : ω.IsTangentAt T ℓ) (hX : X ∈ (ω : Set Pt)) :
    ⟪X -ᵥ T, ω.center -ᵥ T⟫ = ‖X -ᵥ T‖ ^ 2 / 2 := by
  have hT : dist T ω.center = ω.radius := h.mem_sphere
  have hX' : dist X ω.center = ω.radius := hX
  have e : X -ᵥ T = (X -ᵥ ω.center) + (ω.center -ᵥ T) :=
    (vsub_add_vsub_cancel X ω.center T).symm
  have hnorm : ‖ω.center -ᵥ T‖ = ω.radius := by rw [← hT, dist_comm, dist_eq_norm_vsub]
  have hnormX : ‖X -ᵥ ω.center‖ = ω.radius := by rw [← hX', dist_eq_norm_vsub]
  have h1 : ‖X -ᵥ T‖ ^ 2 =
      ω.radius ^ 2 + 2 * ⟪X -ᵥ ω.center, ω.center -ᵥ T⟫ + ω.radius ^ 2 := by
    rw [e, norm_add_sq_real, hnorm, hnormX]
  have h2 : ⟪X -ᵥ T, ω.center -ᵥ T⟫ = ⟪X -ᵥ ω.center, ω.center -ᵥ T⟫ + ω.radius ^ 2 := by
    rw [e, inner_add_left, real_inner_self_eq_norm_sq, hnorm]
  linarith

omit [Fact (finrank ℝ V = 2)] in
/-- Chord-radius angle is non-obtuse: `⟪X -ᵥ T, ω.center -ᵥ T⟫ ≥ 0`. -/
lemma IsTangentAt.inner_vsub_center_nonneg {ω : Sphere Pt} {T X : Pt}
    {ℓ : AffineSubspace ℝ Pt} (h : ω.IsTangentAt T ℓ) (hX : X ∈ (ω : Set Pt)) :
    0 ≤ ⟪X -ᵥ T, ω.center -ᵥ T⟫ := by
  rw [IsTangentAt.inner_vsub_center_eq h hX]
  positivity

omit [Fact (finrank ℝ V = 2)] in
/-- The chord-radius angle is right only at the tangency point itself:
`⟪X -ᵥ T, ω.center -ᵥ T⟫ > 0` for `X ≠ T`. -/
lemma IsTangentAt.inner_vsub_center_pos {ω : Sphere Pt} {T X : Pt}
    {ℓ : AffineSubspace ℝ Pt} (h : ω.IsTangentAt T ℓ) (hX : X ∈ (ω : Set Pt))
    (hXT : X ≠ T) :
    0 < ⟪X -ᵥ T, ω.center -ᵥ T⟫ := by
  rw [IsTangentAt.inner_vsub_center_eq h hX]
  have hn : 0 < ‖X -ᵥ T‖ :=
    norm_pos_iff.mpr (fun hxz => hXT (vsub_eq_zero_iff_eq.mp hxz))
  have h2 := pow_pos hn 2
  linarith

omit [Fact (finrank ℝ V = 2)] in
/-- Tangent segments from a vertex of a triangle to its incircle have equal
lengths. -/
lemma dist_point_touchpoint_empty_eq {t : Triangle ℝ Pt} {j i₁ i₂ : Fin 3}
    (hj₁ : j ≠ i₁) (hj₂ : j ≠ i₂) :
    dist (t.points j) (t.touchpoint ∅ i₁) = dist (t.points j) (t.touchpoint ∅ i₂) :=
  EuclideanGeometry.Sphere.IsTangentAt.dist_eq_of_mem_of_mem
    (t.isTangentAt_insphere_touchpoint i₁) (t.isTangentAt_insphere_touchpoint i₂)
    ((t.points_mem_affineSpan_faceOpposite).2 hj₁)
    ((t.points_mem_affineSpan_faceOpposite).2 hj₂)

omit [Fact (finrank ℝ V = 2)] in
/-- The distance equations determined by the three touchpoints of the
incircle: equal tangent lengths from each vertex, and each touchpoint
splitting its side. -/
lemma touchpoint_dist_eqs {t : Triangle ℝ Pt} :
    dist (t.points 0) (t.touchpoint ∅ 1) = dist (t.points 0) (t.touchpoint ∅ 2) ∧
      dist (t.points 1) (t.touchpoint ∅ 2) = dist (t.points 1) (t.touchpoint ∅ 0) ∧
      dist (t.points 2) (t.touchpoint ∅ 0) = dist (t.points 2) (t.touchpoint ∅ 1) ∧
      dist (t.points 0) (t.touchpoint ∅ 1) + dist (t.touchpoint ∅ 1) (t.points 2) =
        dist (t.points 0) (t.points 2) ∧
      dist (t.points 1) (t.touchpoint ∅ 0) + dist (t.touchpoint ∅ 0) (t.points 2) =
        dist (t.points 1) (t.points 2) ∧
      dist (t.points 0) (t.touchpoint ∅ 2) + dist (t.touchpoint ∅ 2) (t.points 1) =
        dist (t.points 0) (t.points 1) := by
  refine ⟨dist_point_touchpoint_empty_eq (j := 0) (i₁ := 1) (i₂ := 2) (by decide) (by decide),
    dist_point_touchpoint_empty_eq (j := 1) (i₁ := 2) (i₂ := 0) (by decide) (by decide),
    dist_point_touchpoint_empty_eq (j := 2) (i₁ := 0) (i₂ := 1) (by decide) (by decide),
    ?_, ?_, ?_⟩
  · exact (Affine.Triangle.sbtw_touchpoint_empty t (i₁ := 0) (i₂ := 1) (i₃ := 2)
      (by decide) (by decide) (by decide)).wbtw.dist_add_dist
  · exact (Affine.Triangle.sbtw_touchpoint_empty t (i₁ := 1) (i₂ := 0) (i₃ := 2)
      (by decide) (by decide) (by decide)).wbtw.dist_add_dist
  · exact (Affine.Triangle.sbtw_touchpoint_empty t (i₁ := 0) (i₂ := 2) (i₃ := 1)
      (by decide) (by decide) (by decide)).wbtw.dist_add_dist

omit [Fact (finrank ℝ V = 2)] in
/-- `touchpoint_dist_eqs` specialized to the triangle `⟨![A, B, C], h⟩`, with
the vertices written as `A`, `B`, `C` (definitionally equal to `![A, B, C] 0`
etc.). -/
lemma touchpoint_dist_eqs_mk {A B C : Pt} (h : AffineIndependent ℝ ![A, B, C]) :
    dist A ((⟨![A, B, C], h⟩ : Triangle ℝ Pt).touchpoint ∅ 1) =
      dist A ((⟨![A, B, C], h⟩ : Triangle ℝ Pt).touchpoint ∅ 2) ∧
      dist B ((⟨![A, B, C], h⟩ : Triangle ℝ Pt).touchpoint ∅ 2) =
        dist B ((⟨![A, B, C], h⟩ : Triangle ℝ Pt).touchpoint ∅ 0) ∧
      dist C ((⟨![A, B, C], h⟩ : Triangle ℝ Pt).touchpoint ∅ 0) =
        dist C ((⟨![A, B, C], h⟩ : Triangle ℝ Pt).touchpoint ∅ 1) ∧
      dist A ((⟨![A, B, C], h⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +
        dist C ((⟨![A, B, C], h⟩ : Triangle ℝ Pt).touchpoint ∅ 1) = dist A C ∧
      dist B ((⟨![A, B, C], h⟩ : Triangle ℝ Pt).touchpoint ∅ 0) +
        dist C ((⟨![A, B, C], h⟩ : Triangle ℝ Pt).touchpoint ∅ 0) = dist B C ∧
      dist A ((⟨![A, B, C], h⟩ : Triangle ℝ Pt).touchpoint ∅ 2) +
        dist B ((⟨![A, B, C], h⟩ : Triangle ℝ Pt).touchpoint ∅ 2) = dist A B := by
  obtain ⟨tA, tB, tC, e1, e0, e2⟩ := touchpoint_dist_eqs (t := ⟨![A, B, C], h⟩)
  rw [dist_comm _ (![A, B, C] 2)] at e1 e0
  rw [dist_comm _ (![A, B, C] 1)] at e2
  exact ⟨tA, tB, tC, e1, e0, e2⟩

omit [Fact (finrank ℝ V = 2)] in
/-- The first vertex of the triangle `⟨![A, B, C], h⟩` is `A`. -/
lemma points_mk_zero {A B C : Pt} (h : AffineIndependent ℝ ![A, B, C]) :
    (⟨![A, B, C], h⟩ : Triangle ℝ Pt).points 0 = A := rfl

omit [Fact (finrank ℝ V = 2)] in
/-- The third vertex of the triangle `⟨![A, B, C], h⟩` is `C`. -/
lemma points_mk_two {A B C : Pt} (h : AffineIndependent ℝ ![A, B, C]) :
    (⟨![A, B, C], h⟩ : Triangle ℝ Pt).points 2 = C := rfl

omit [Fact (finrank ℝ V = 2)] in
/-- The touchpoint of the incircle of triangle `ABC` with the side `AC`
(mathlib's `Simplex.touchpoint ∅ 1`, the touchpoint on the face opposite the
vertex `B`) lies weakly between `A` and `C`. -/
lemma wbtw_touchpoint_insphere {A B C : Pt} (h : AffineIndependent ℝ ![A, B, C]) :
    Wbtw ℝ A ((⟨![A, B, C], h⟩ : Triangle ℝ Pt).touchpoint ∅ 1) C := by
  have hs := Affine.Triangle.sbtw_touchpoint_empty (⟨![A, B, C], h⟩ : Triangle ℝ Pt)
    (i₁ := 0) (i₂ := 1) (i₃ := 2) (by decide) (by decide) (by decide)
  rw [points_mk_zero h, points_mk_two h] at hs
  exact hs.wbtw

omit [Fact (finrank ℝ V = 2)] in
/-- The distance from `A` to the touchpoint of the incircle on `AC` equals
the semiperimeter minus the opposite side. -/
lemma dist_touchpoint_insphere_left {A B C : Pt} (h : AffineIndependent ℝ ![A, B, C]) :
    dist A ((⟨![A, B, C], h⟩ : Triangle ℝ Pt).touchpoint ∅ 1) =
      (dist A B + dist A C - dist B C) / 2 := by
  obtain ⟨tA, tB, tC, e1, e0, e2⟩ := touchpoint_dist_eqs_mk h
  linarith

omit [Fact (finrank ℝ V = 2)] in
/-- The distance from `C` to the same touchpoint. -/
lemma dist_touchpoint_insphere_right {A B C : Pt} (h : AffineIndependent ℝ ![A, B, C]) :
    dist C ((⟨![A, B, C], h⟩ : Triangle ℝ Pt).touchpoint ∅ 1) =
      (dist C A + dist C B - dist A B) / 2 := by
  obtain ⟨tA, tB, tC, e1, e0, e2⟩ := touchpoint_dist_eqs_mk h
  rw [dist_comm C A, dist_comm C B]
  linarith

omit [Fact (finrank ℝ V = 2)] in
/-- Tangent segments from a vertex of a triangle to an excircle have equal
lengths. -/
lemma dist_point_touchpoint_singleton_eq {t : Triangle ℝ Pt} {i j i₁ i₂ : Fin 3}
    (hj₁ : j ≠ i₁) (hj₂ : j ≠ i₂) :
    dist (t.points j) (t.touchpoint {i} i₁) = dist (t.points j) (t.touchpoint {i} i₂) :=
  EuclideanGeometry.Sphere.IsTangentAt.dist_eq_of_mem_of_mem
    ((t.excenterExists_singleton i).isTangentAt_touchpoint i₁)
    ((t.excenterExists_singleton i).isTangentAt_touchpoint i₂)
    ((t.points_mem_affineSpan_faceOpposite).2 hj₁)
    ((t.points_mem_affineSpan_faceOpposite).2 hj₂)

omit [Fact (finrank ℝ V = 2)] in
/-- The distance equations determined by the three touchpoints of the
B-excircle (excircle opposite vertex `1` of `![A, B, C]`): equal tangent
lengths from each vertex, the touchpoint on side `AC` splitting it, and the
touchpoints on the extensions beyond `A` and `C`. -/
lemma touchpoint_exsphere_dist_eqs {A B C : Pt} (h : AffineIndependent ℝ ![A, B, C]) :
    dist A ((⟨![A, B, C], h⟩ : Triangle ℝ Pt).touchpoint {1} 1) =
      dist A ((⟨![A, B, C], h⟩ : Triangle ℝ Pt).touchpoint {1} 2) ∧
    dist C ((⟨![A, B, C], h⟩ : Triangle ℝ Pt).touchpoint {1} 1) =
      dist C ((⟨![A, B, C], h⟩ : Triangle ℝ Pt).touchpoint {1} 0) ∧
    dist B ((⟨![A, B, C], h⟩ : Triangle ℝ Pt).touchpoint {1} 0) =
      dist B ((⟨![A, B, C], h⟩ : Triangle ℝ Pt).touchpoint {1} 2) ∧
    dist A ((⟨![A, B, C], h⟩ : Triangle ℝ Pt).touchpoint {1} 1) +
      dist C ((⟨![A, B, C], h⟩ : Triangle ℝ Pt).touchpoint {1} 1) = dist A C ∧
    dist B A + dist A ((⟨![A, B, C], h⟩ : Triangle ℝ Pt).touchpoint {1} 2) =
      dist B ((⟨![A, B, C], h⟩ : Triangle ℝ Pt).touchpoint {1} 2) ∧
    dist B C + dist C ((⟨![A, B, C], h⟩ : Triangle ℝ Pt).touchpoint {1} 0) =
      dist B ((⟨![A, B, C], h⟩ : Triangle ℝ Pt).touchpoint {1} 0) := by
  have p0 : (⟨![A, B, C], h⟩ : Triangle ℝ Pt).points 0 = A := rfl
  have p1 : (⟨![A, B, C], h⟩ : Triangle ℝ Pt).points 1 = B := rfl
  have p2 : (⟨![A, B, C], h⟩ : Triangle ℝ Pt).points 2 = C := rfl
  have tA := dist_point_touchpoint_singleton_eq (t := ⟨![A, B, C], h⟩) (i := 1) (j := 0)
    (i₁ := 1) (i₂ := 2) (by decide) (by decide)
  have tC := dist_point_touchpoint_singleton_eq (t := ⟨![A, B, C], h⟩) (i := 1) (j := 2)
    (i₁ := 1) (i₂ := 0) (by decide) (by decide)
  have tB := dist_point_touchpoint_singleton_eq (t := ⟨![A, B, C], h⟩) (i := 1) (j := 1)
    (i₁ := 0) (i₂ := 2) (by decide) (by decide)
  rw [p0] at tA
  rw [p2] at tC
  rw [p1] at tB
  refine ⟨tA, tC, tB, ?_, ?_, ?_⟩
  · have h4 := (Affine.Triangle.sbtw_touchpoint_singleton (⟨![A, B, C], h⟩ : Triangle ℝ Pt)
      (i₁ := 0) (i₂ := 1) (i₃ := 2) (by decide) (by decide) (by decide)).wbtw.dist_add_dist
    rw [p0, p2, dist_comm ((⟨![A, B, C], h⟩ : Triangle ℝ Pt).touchpoint {1} 1) C] at h4
    exact h4
  · have h5 := (Affine.Triangle.touchpoint_singleton_sbtw (⟨![A, B, C], h⟩ : Triangle ℝ Pt)
      (i₁ := 1) (i₂ := 2) (i₃ := 0) (by decide) (by decide) (by decide)).wbtw.dist_add_dist
    rw [p0, p1, dist_comm A B,
      dist_comm ((⟨![A, B, C], h⟩ : Triangle ℝ Pt).touchpoint {1} 2) A,
      dist_comm ((⟨![A, B, C], h⟩ : Triangle ℝ Pt).touchpoint {1} 2) B] at h5
    linarith
  · have h6 := (Affine.Triangle.touchpoint_singleton_sbtw (⟨![A, B, C], h⟩ : Triangle ℝ Pt)
      (i₁ := 1) (i₂ := 0) (i₃ := 2) (by decide) (by decide) (by decide)).wbtw.dist_add_dist
    rw [p1, p2, dist_comm C B,
      dist_comm ((⟨![A, B, C], h⟩ : Triangle ℝ Pt).touchpoint {1} 0) C,
      dist_comm ((⟨![A, B, C], h⟩ : Triangle ℝ Pt).touchpoint {1} 0) B] at h6
    linarith

omit [Fact (finrank ℝ V = 2)] in
/-- The distance from `A` to the touchpoint of the B-excircle on line `AC`. -/
lemma dist_touchpoint_exsphere_left {A B C : Pt} (h : AffineIndependent ℝ ![A, B, C]) :
    dist A ((⟨![A, B, C], h⟩ : Triangle ℝ Pt).touchpoint {1} 1) =
      (dist B C + dist A C - dist A B) / 2 := by
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := touchpoint_exsphere_dist_eqs h
  rw [dist_comm B A] at e5
  linarith

omit [Fact (finrank ℝ V = 2)] in
/-- The distance from `C` to the same touchpoint. -/
lemma dist_touchpoint_exsphere_right {A B C : Pt} (h : AffineIndependent ℝ ![A, B, C]) :
    dist C ((⟨![A, B, C], h⟩ : Triangle ℝ Pt).touchpoint {1} 1) =
      (dist A C + dist A B - dist B C) / 2 := by
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := touchpoint_exsphere_dist_eqs h
  rw [dist_comm B A] at e5
  linarith

/-- Side-chain, right half: the signed determinant of `ω.center -ᵥ D`
against `v = C -ᵥ D` equals minus the radius times `‖v‖`, signed by the
`ConvexQuadrilateral` cross product `c₃ = areaForm (D -ᵥ C) (A -ᵥ D)`.
This is the mirror of `areaForm_center_left` (with the sign flips
verified numerically). -/
lemma areaForm_center_right {A B C D T₂ W : Pt} {ω : Sphere Pt}
    (hR : 0 < ω.radius)
    (hs : 0 < planeOrientation.areaForm (D -ᵥ C) (A -ᵥ D) *
      planeOrientation.areaForm (C -ᵥ B) (D -ᵥ C))
    (hsbtw : [B, C, T₂].Sbtw ℝ)
    (htan₂ : ω.IsTangentAt T₂ line[ℝ, B, C])
    (htanW : ω.IsTangentAt W line[ℝ, C, D]) :
    planeOrientation.areaForm (ω.center -ᵥ D) (C -ᵥ D) *
        planeOrientation.areaForm (D -ᵥ C) (A -ᵥ D) =
      -ω.radius * ‖C -ᵥ D‖ * |planeOrientation.areaForm (D -ᵥ C) (A -ᵥ D)| := by
  -- `v ≠ 0` (else `c₃ = 0`, contradicting `hs`)
  have hv : C -ᵥ D ≠ 0 := by
    intro h
    have h' : D -ᵥ C = 0 := by rw [← neg_vsub_eq_vsub_rev C D, h, neg_zero]
    rw [h'] at hs
    simp only [map_zero, LinearMap.zero_apply, mul_zero, lt_irrefl] at hs
  have hc2ne : planeOrientation.areaForm (C -ᵥ B) (D -ᵥ C) ≠ 0 := by
    rcases mul_pos_iff.mp hs with h | h <;> linarith [h.1, h.2]
  -- `T₂ ≠ W`: the lines `BC` and `CD` meet only in `C`, and `T₂ ≠ C`.
  have hne : T₂ ≠ W := by
    intro hEq
    have h1 : T₂ -ᵥ C ∈ line[ℝ, B, C].direction :=
      AffineSubspace.vsub_mem_direction htan₂.mem_space (right_mem_affineSpan_pair ℝ B C)
    have h2 : T₂ -ᵥ C ∈ line[ℝ, C, D].direction := by
      rw [hEq]
      exact AffineSubspace.vsub_mem_direction htanW.mem_space (left_mem_affineSpan_pair ℝ C D)
    rw [direction_affineSpan, mem_vectorSpan_pair] at h1 h2
    obtain ⟨c₁, hc₁⟩ := h1
    obtain ⟨c₂, hc₂⟩ := h2
    have hcross : planeOrientation.areaForm (B -ᵥ C) (C -ᵥ D) ≠ 0 := by
      have e1 : B -ᵥ C = -(C -ᵥ B) := (neg_vsub_eq_vsub_rev C B).symm
      have e2 : C -ᵥ D = -(D -ᵥ C) := (neg_vsub_eq_vsub_rev D C).symm
      rw [e1, e2, areaForm_neg_left, areaForm_neg_right, neg_neg]
      exact hc2ne
    have h0 : c₁ * planeOrientation.areaForm (B -ᵥ C) (C -ᵥ D) = 0 := by
      have e : c₁ • (B -ᵥ C) = c₂ • (C -ᵥ D) := by rw [hc₁, hc₂]
      have := congrArg (fun z : V => planeOrientation.areaForm z (C -ᵥ D)) e
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at this
      rw [areaForm_self, mul_zero] at this
      exact this
    have hc₁0 : c₁ = 0 := by
      rcases mul_eq_zero.mp h0 with h | h
      · exact h
      · exact absurd h hcross
    have hT2C : T₂ = C := by
      have : T₂ -ᵥ C = 0 := by rw [← hc₁, hc₁0, zero_smul]
      exact vsub_eq_zero_iff_eq.mp this
    have hSbtw := List.sbtw_triple.mp hsbtw
    exact hSbtw.2.2 hT2C.symm
  -- `areaForm (O -ᵥ D) v = -⟪O -ᵥ W, rot90 v⟫`
  have hspanW : ∃ c : ℝ, c • (C -ᵥ D) = W -ᵥ D := by
    have h1 : W -ᵥ D ∈ line[ℝ, C, D].direction :=
      AffineSubspace.vsub_mem_direction htanW.mem_space (right_mem_affineSpan_pair ℝ C D)
    rwa [direction_affineSpan, mem_vectorSpan_pair] at h1
  obtain ⟨cw, hcw⟩ := hspanW
  have hWv : ⟪W -ᵥ D, rot90 (C -ᵥ D)⟫ = 0 := by
    rw [← hcw, real_inner_smul_left, inner_rot90_right, areaForm_self, neg_zero,
      mul_zero]
  have hWv0 : planeOrientation.areaForm (W -ᵥ D) (C -ᵥ D) = 0 := by
    rw [← hcw, map_smul, LinearMap.smul_apply, areaForm_self, smul_zero]
  have hAf : planeOrientation.areaForm (ω.center -ᵥ D) (C -ᵥ D) =
      -⟪ω.center -ᵥ W, rot90 (C -ᵥ D)⟫ := by
    have e : ω.center -ᵥ D = (ω.center -ᵥ W) + (W -ᵥ D) :=
      (vsub_add_vsub_cancel (ω.center) W D).symm
    rw [e, map_add, LinearMap.add_apply, hWv0, add_zero, inner_rot90_right, neg_neg]
  -- magnitude
  have hMag : |⟪ω.center -ᵥ W, rot90 (C -ᵥ D)⟫| = ω.radius * ‖C -ᵥ D‖ :=
    IsTangentAt.abs_inner_vsub_center_rot90 htanW
      (left_mem_affineSpan_pair ℝ C D) (right_mem_affineSpan_pair ℝ C D) hR
  -- sign chain: `0 < ⟪O -ᵥ W, rot90 v⟫ * c₂`
  obtain ⟨τ, hτpos, hτ⟩ := exists_pos_smul_vsub_of_sbtw (List.sbtw_triple.mp hsbtw)
  have hT2W : ⟪T₂ -ᵥ W, rot90 (C -ᵥ D)⟫ = τ * planeOrientation.areaForm (C -ᵥ B) (D -ᵥ C) := by
    have hspanD : ∃ c : ℝ, c • (C -ᵥ D) = D -ᵥ W := by
      have h1 : D -ᵥ W ∈ line[ℝ, C, D].direction :=
        AffineSubspace.vsub_mem_direction (right_mem_affineSpan_pair ℝ C D) htanW.mem_space
      rwa [direction_affineSpan, mem_vectorSpan_pair] at h1
    obtain ⟨cd, hcd⟩ := hspanD
    have hDv : ⟪D -ᵥ W, rot90 (C -ᵥ D)⟫ = 0 := by
      rw [← hcd, real_inner_smul_left, inner_rot90_right, areaForm_self, neg_zero,
        mul_zero]
    have e1 : T₂ -ᵥ W = (T₂ -ᵥ D) + (D -ᵥ W) := (vsub_add_vsub_cancel T₂ D W).symm
    have e2 : T₂ -ᵥ D = (T₂ -ᵥ C) + (C -ᵥ D) := (vsub_add_vsub_cancel T₂ C D).symm
    have hCB : ⟪C -ᵥ B, rot90 (C -ᵥ D)⟫ = planeOrientation.areaForm (C -ᵥ B) (D -ᵥ C) := by
      have e3 : C -ᵥ D = -(D -ᵥ C) := (neg_vsub_eq_vsub_rev D C).symm
      rw [inner_rot90_right, e3, areaForm_neg_right, neg_neg]
    rw [e1, inner_add_left, hDv, add_zero, e2, hτ, inner_add_left,
      real_inner_smul_left, hCB, inner_rot90_right, areaForm_self, neg_zero, add_zero]
  have hchord : 0 < ⟪T₂ -ᵥ W, ω.center -ᵥ W⟫ :=
    IsTangentAt.inner_vsub_center_pos htanW htan₂.mem_sphere hne
  have hperp : ⟪ω.center -ᵥ W, C -ᵥ D⟫ = 0 :=
    IsTangentAt.inner_vsub_center_eq_zero htanW
      (left_mem_affineSpan_pair ℝ C D) (right_mem_affineSpan_pair ℝ C D)
  have hdecomp : ω.center -ᵥ W =
      (⟪ω.center -ᵥ W, rot90 (C -ᵥ D)⟫ / ‖C -ᵥ D‖ ^ 2) • rot90 (C -ᵥ D) := by
    have h := eq_smul_add_smul_rightAngleRotation (ω.center -ᵥ W) (C -ᵥ D) hv
    rw [hperp, zero_div, zero_smul, zero_add] at h
    exact h
  have hv2 : 0 < ‖C -ᵥ D‖ ^ 2 := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hv)
  have hsign : 0 < ⟪ω.center -ᵥ W, rot90 (C -ᵥ D)⟫ *
      planeOrientation.areaForm (C -ᵥ B) (D -ᵥ C) := by
    rw [hdecomp, real_inner_smul_right, hT2W] at hchord
    have hrw : (⟪ω.center -ᵥ W, rot90 (C -ᵥ D)⟫ / ‖C -ᵥ D‖ ^ 2) *
        (τ * planeOrientation.areaForm (C -ᵥ B) (D -ᵥ C)) =
        ⟪ω.center -ᵥ W, rot90 (C -ᵥ D)⟫ * planeOrientation.areaForm (C -ᵥ B) (D -ᵥ C) *
          τ / ‖C -ᵥ D‖ ^ 2 := by ring
    rw [hrw] at hchord
    have h1 : 0 < ⟪ω.center -ᵥ W, rot90 (C -ᵥ D)⟫ *
        planeOrientation.areaForm (C -ᵥ B) (D -ᵥ C) * τ := by
      have h2 := mul_pos hchord hv2
      rwa [div_mul_cancel₀ _ hv2.ne'] at h2
    exact pos_of_mul_pos_left h1 hτpos.le
  -- `0 < Y * c₃` from `0 < Y * c₂` and `0 < c₃ * c₂`
  have hYc3 : 0 < ⟪ω.center -ᵥ W, rot90 (C -ᵥ D)⟫ *
      planeOrientation.areaForm (D -ᵥ C) (A -ᵥ D) := by
    have h1 := mul_pos hsign hs
    have h2 : ⟪ω.center -ᵥ W, rot90 (C -ᵥ D)⟫ * planeOrientation.areaForm (C -ᵥ B) (D -ᵥ C) *
        (planeOrientation.areaForm (D -ᵥ C) (A -ᵥ D) *
          planeOrientation.areaForm (C -ᵥ B) (D -ᵥ C)) =
        (⟪ω.center -ᵥ W, rot90 (C -ᵥ D)⟫ * planeOrientation.areaForm (D -ᵥ C) (A -ᵥ D)) *
          planeOrientation.areaForm (C -ᵥ B) (D -ᵥ C) ^ 2 := by ring
    rw [h2] at h1
    exact pos_of_mul_pos_left h1 (sq_nonneg _)
  -- assemble
  rw [hAf]
  have hneg : ⟪ω.center -ᵥ W, rot90 (C -ᵥ D)⟫ *
      planeOrientation.areaForm (D -ᵥ C) (A -ᵥ D) = |⟪ω.center -ᵥ W, rot90 (C -ᵥ D)⟫| *
        |planeOrientation.areaForm (D -ᵥ C) (A -ᵥ D)| := by
    rw [← abs_mul, abs_of_pos hYc3]
  calc (-⟪ω.center -ᵥ W, rot90 (C -ᵥ D)⟫) * planeOrientation.areaForm (D -ᵥ C) (A -ᵥ D)
      = -(⟪ω.center -ᵥ W, rot90 (C -ᵥ D)⟫ * planeOrientation.areaForm (D -ᵥ C) (A -ᵥ D)) :=
        neg_mul _ _
    _ = -(|⟪ω.center -ᵥ W, rot90 (C -ᵥ D)⟫| *
          |planeOrientation.areaForm (D -ᵥ C) (A -ᵥ D)|) := by rw [hneg]
    _ = -(ω.radius * ‖C -ᵥ D‖ * |planeOrientation.areaForm (D -ᵥ C) (A -ᵥ D)|) := by
        rw [hMag]
    _ = -ω.radius * ‖C -ᵥ D‖ * |planeOrientation.areaForm (D -ᵥ C) (A -ᵥ D)| := by ring

/-- Side-chain, left half: the signed determinant of `ω.center -ᵥ D` against
`u = A -ᵥ D` equals the radius times `‖u‖`, with the sign of the
`ConvexQuadrilateral` cross product `c₃ = areaForm (D -ᵥ C) (A -ᵥ D)`. -/
lemma areaForm_center_left {A B C D T₁ U : Pt} {ω : Sphere Pt}
    (hR : 0 < ω.radius)
    (hs : 0 < planeOrientation.areaForm (D -ᵥ C) (A -ᵥ D) *
      planeOrientation.areaForm (A -ᵥ D) (B -ᵥ A))
    (hsbtw : [B, A, T₁].Sbtw ℝ)
    (htan₁ : ω.IsTangentAt T₁ line[ℝ, B, A])
    (htanU : ω.IsTangentAt U line[ℝ, A, D]) :
    planeOrientation.areaForm (ω.center -ᵥ D) (A -ᵥ D) *
        planeOrientation.areaForm (D -ᵥ C) (A -ᵥ D) =
      ω.radius * ‖A -ᵥ D‖ * |planeOrientation.areaForm (D -ᵥ C) (A -ᵥ D)| := by
  set u := A -ᵥ D with hu_def
  set c₃ := planeOrientation.areaForm (D -ᵥ C) u
  set c₄ := planeOrientation.areaForm u (B -ᵥ A) with hc₄
  have hu : u ≠ 0 := by
    intro h
    have hc4z : c₄ = 0 := by
      rw [hc₄, h, map_zero, LinearMap.zero_apply]
    rw [hc4z, mul_zero] at hs
    exact lt_irrefl _ hs
  have hTU : T₁ ≠ U := by
    intro hEq
    have hT₁AD : T₁ ∈ line[ℝ, A, D] := by
      rw [hEq]
      exact htanU.mem_space
    have hdir1 : T₁ -ᵥ A ∈ line[ℝ, B, A].direction :=
      AffineSubspace.vsub_mem_direction htan₁.mem_space (right_mem_affineSpan_pair ℝ B A)
    rw [direction_affineSpan] at hdir1
    obtain ⟨c₁, hc₁⟩ := mem_vectorSpan_pair.mp hdir1
    have hdir2 : T₁ -ᵥ A ∈ line[ℝ, A, D].direction :=
      AffineSubspace.vsub_mem_direction hT₁AD (left_mem_affineSpan_pair ℝ A D)
    rw [direction_affineSpan] at hdir2
    obtain ⟨c₂, hc₂⟩ := mem_vectorSpan_pair.mp hdir2
    have hc4ne : c₄ ≠ 0 := by
      intro h
      rw [h, mul_zero] at hs
      exact lt_irrefl _ hs
    have haf1 : planeOrientation.areaForm (T₁ -ᵥ A) u = 0 := by
      rw [← hc₂, ← hu_def, map_smul, LinearMap.smul_apply, areaForm_self, smul_zero]
    have haf2 : planeOrientation.areaForm (T₁ -ᵥ A) u =
        c₁ * planeOrientation.areaForm (B -ᵥ A) u := by
      rw [← hc₁, map_smul, LinearMap.smul_apply, smul_eq_mul]
    have hBAne : planeOrientation.areaForm (B -ᵥ A) u ≠ 0 := by
      rw [areaForm_swap, ← hc₄]
      exact neg_ne_zero.mpr hc4ne
    have hc₁z : c₁ = 0 := by
      have h : c₁ * planeOrientation.areaForm (B -ᵥ A) u = 0 := by
        rw [← haf2]
        exact haf1
      exact (mul_eq_zero.mp h).resolve_right hBAne
    have hT₁A : T₁ = A := by
      have h : T₁ -ᵥ A = 0 := by
        rw [← hc₁, hc₁z, zero_smul]
      exact vsub_eq_zero_iff_eq.mp h
    exact (List.sbtw_triple.mp hsbtw).2.2 hT₁A.symm
  have hUD : ⟪U -ᵥ D, rot90 u⟫ = 0 := by
    have hdir : U -ᵥ D ∈ line[ℝ, A, D].direction :=
      AffineSubspace.vsub_mem_direction htanU.mem_space (right_mem_affineSpan_pair ℝ A D)
    rw [direction_affineSpan] at hdir
    obtain ⟨c, hc⟩ := mem_vectorSpan_pair.mp hdir
    rw [← hc, ← hu_def, real_inner_smul_left, inner_rot90_right, areaForm_self, neg_zero,
      mul_zero]
  have hstep3 : planeOrientation.areaForm (ω.center -ᵥ D) u =
      -⟪ω.center -ᵥ U, rot90 u⟫ := by
    have h1 : ⟪ω.center -ᵥ D, rot90 u⟫ = ⟪ω.center -ᵥ U, rot90 u⟫ := by
      have e : (ω.center -ᵥ D) = (ω.center -ᵥ U) + (U -ᵥ D) :=
        (vsub_add_vsub_cancel ω.center U D).symm
      rw [e, inner_add_left, hUD, add_zero]
    have h2 := inner_rot90_right (ω.center -ᵥ D) u
    rw [h1] at h2
    rw [h2, neg_neg]
  have habs : |⟪ω.center -ᵥ U, rot90 u⟫| = ω.radius * ‖u‖ := by
    have h := IsTangentAt.abs_inner_vsub_center_rot90 htanU
      (left_mem_affineSpan_pair ℝ A D) (right_mem_affineSpan_pair ℝ A D) hR
    rwa [← hu_def] at h
  have hDU : ⟪D -ᵥ U, rot90 u⟫ = 0 := by
    have hdir : D -ᵥ U ∈ line[ℝ, A, D].direction :=
      AffineSubspace.vsub_mem_direction (right_mem_affineSpan_pair ℝ A D) htanU.mem_space
    rw [direction_affineSpan] at hdir
    obtain ⟨c, hc⟩ := mem_vectorSpan_pair.mp hdir
    rw [← hc, ← hu_def, real_inner_smul_left, inner_rot90_right, areaForm_self, neg_zero,
      mul_zero]
  have h5a : ⟪T₁ -ᵥ U, rot90 u⟫ = ⟪T₁ -ᵥ D, rot90 u⟫ := by
    have e : (T₁ -ᵥ U) = (T₁ -ᵥ D) + (D -ᵥ U) := (vsub_add_vsub_cancel T₁ D U).symm
    rw [e, inner_add_left, hDU, add_zero]
  obtain ⟨σ, hσpos, hσ⟩ := exists_pos_smul_vsub_of_sbtw (List.sbtw_triple.mp hsbtw)
  have haf4 : planeOrientation.areaForm (A -ᵥ B) u = c₄ := by
    have e2 : (A -ᵥ B) = -(B -ᵥ A) := (neg_vsub_eq_vsub_rev B A).symm
    rw [areaForm_swap, e2, map_neg, ← hc₄, neg_neg]
  have h5b : ⟪T₁ -ᵥ D, rot90 u⟫ = σ * (-c₄) := by
    have e : (T₁ -ᵥ D) = σ • (A -ᵥ B) + u := by
      rw [hu_def, ← hσ]
      exact (vsub_add_vsub_cancel T₁ A D).symm
    rw [e, inner_add_left, real_inner_smul_left, inner_rot90_right, inner_rot90_right,
      haf4, areaForm_self, neg_zero, add_zero]
  have h5c : 0 < ⟪T₁ -ᵥ U, ω.center -ᵥ U⟫ :=
    IsTangentAt.inner_vsub_center_pos htanU htan₁.mem_sphere hTU
  have h5d : (ω.center -ᵥ U) = (⟪ω.center -ᵥ U, rot90 u⟫ / ‖u‖ ^ 2) • rot90 u := by
    have h0 : ⟪ω.center -ᵥ U, u⟫ = 0 := by
      have h := IsTangentAt.inner_vsub_center_eq_zero htanU
        (left_mem_affineSpan_pair ℝ A D) (right_mem_affineSpan_pair ℝ A D)
      rwa [← hu_def] at h
    have hdecomp := eq_smul_add_smul_rightAngleRotation (ω.center -ᵥ U) u hu
    rw [h0, zero_div, zero_smul, zero_add] at hdecomp
    exact hdecomp
  have h5e : 0 < (⟪ω.center -ᵥ U, rot90 u⟫ / ‖u‖ ^ 2) * (σ * (-c₄)) := by
    rw [h5d] at h5c
    rw [real_inner_smul_right, h5a, h5b] at h5c
    exact h5c
  have hn2 : 0 < ‖u‖ ^ 2 := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hu)
  have h5f : 0 < ⟪ω.center -ᵥ U, rot90 u⟫ * (σ * (-c₄)) := by
    have h := mul_pos h5e hn2
    rwa [div_mul_eq_mul_div, div_mul_cancel₀ _ hn2.ne'] at h
  have hsign : 0 < ⟪ω.center -ᵥ U, rot90 u⟫ * (-c₄) := by
    have heq : ⟪ω.center -ᵥ U, rot90 u⟫ * (σ * (-c₄)) =
        (⟪ω.center -ᵥ U, rot90 u⟫ * (-c₄)) * σ := by ring
    rw [heq] at h5f
    exact pos_of_mul_pos_left h5f hσpos.le
  have hX : 0 < (-⟪ω.center -ᵥ U, rot90 u⟫) * c₃ := by
    have h2 : 0 < ((-⟪ω.center -ᵥ U, rot90 u⟫) * c₄) * (c₃ * c₄) := by
      have e : (-⟪ω.center -ᵥ U, rot90 u⟫) * c₄ =
          ⟪ω.center -ᵥ U, rot90 u⟫ * (-c₄) := by ring
      rw [e]
      exact mul_pos hsign hs
    have heq : ((-⟪ω.center -ᵥ U, rot90 u⟫) * c₄) * (c₃ * c₄) =
        ((-⟪ω.center -ᵥ U, rot90 u⟫) * c₃) * c₄ ^ 2 := by ring
    rw [heq] at h2
    exact pos_of_mul_pos_left h2 (sq_nonneg c₄)
  calc planeOrientation.areaForm (ω.center -ᵥ D) u * c₃
      = (-⟪ω.center -ᵥ U, rot90 u⟫) * c₃ := by rw [hstep3]
    _ = |(-⟪ω.center -ᵥ U, rot90 u⟫) * c₃| := (abs_of_pos hX).symm
    _ = |(-⟪ω.center -ᵥ U, rot90 u⟫)| * |c₃| := abs_mul _ _
    _ = |⟪ω.center -ᵥ U, rot90 u⟫| * |c₃| := by rw [abs_neg]
    _ = ω.radius * ‖u‖ * |c₃| := by rw [habs]

omit [Fact (finrank ℝ V = 2)] in
/-- If `U` is on the line through `A` and `D`, and `O` projects onto the
line beyond `D` from `A` (i.e. `⟪O -ᵥ U, D -ᵥ A⟫ = 0` and
`0 < ⟪O -ᵥ D, D -ᵥ A⟫`), then `D` is weakly between `A` and `U`. -/
lemma wbtw_of_projection_beyond {A D U O : Pt}
    (hU : U ∈ line[ℝ, A, D]) (hAD : A ≠ D)
    (hperp : ⟪O -ᵥ U, D -ᵥ A⟫ = 0)
    (hpos : 0 < ⟪O -ᵥ D, D -ᵥ A⟫) :
    Wbtw ℝ A D U := by
  have hUD : 0 < ⟪U -ᵥ D, D -ᵥ A⟫ := by
    have e : U -ᵥ D = (U -ᵥ O) + (O -ᵥ D) := (vsub_add_vsub_cancel U O D).symm
    have h1 : ⟪U -ᵥ O, D -ᵥ A⟫ = 0 := by
      rw [show U -ᵥ O = -(O -ᵥ U) from (neg_vsub_eq_vsub_rev O U).symm,
        inner_neg_left, hperp, neg_zero]
    rw [e, inner_add_left, h1, zero_add]
    exact hpos
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t • (A -ᵥ D) = U -ᵥ A := by
    have h1 : U -ᵥ A ∈ line[ℝ, A, D].direction :=
      AffineSubspace.vsub_mem_direction hU (left_mem_affineSpan_pair ℝ A D)
    rwa [direction_affineSpan, mem_vectorSpan_pair] at h1
  have hu : A -ᵥ D ≠ 0 := vsub_ne_zero.mpr hAD
  have hcomp : ⟪U -ᵥ D, D -ᵥ A⟫ = -(t + 1) * ‖A -ᵥ D‖ ^ 2 := by
    have e2 : U -ᵥ D = (U -ᵥ A) + (A -ᵥ D) := (vsub_add_vsub_cancel U A D).symm
    have e3 : (U -ᵥ A) + (A -ᵥ D) = (t + 1) • (A -ᵥ D) := by
      rw [← ht, add_smul, one_smul]
    have e4 : D -ᵥ A = -(A -ᵥ D) := (neg_vsub_eq_vsub_rev A D).symm
    rw [e2, e3, e4, real_inner_smul_left, inner_neg_right, real_inner_self_eq_norm_sq]
    ring
  have ht1 : t + 1 < 0 := by
    have hu2pos : 0 < ‖A -ᵥ D‖ ^ 2 := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hu)
    rw [hcomp] at hUD
    nlinarith
  have hsr : SameRay ℝ (D -ᵥ A) (U -ᵥ D) := by
    have e5 : U -ᵥ D = (-(t + 1)) • (D -ᵥ A) := by
      have e2 : U -ᵥ D = (U -ᵥ A) + (A -ᵥ D) := (vsub_add_vsub_cancel U A D).symm
      have e3 : (U -ᵥ A) + (A -ᵥ D) = (t + 1) • (A -ᵥ D) := by
        rw [← ht, add_smul, one_smul]
      have e4 : A -ᵥ D = -(D -ᵥ A) := (neg_vsub_eq_vsub_rev D A).symm
      rw [e2, e3, e4, smul_neg, neg_smul]
    rw [e5]
    exact SameRay.sameRay_pos_smul_right _ (neg_pos.mpr ht1)
  exact wbtw_iff_sameRay_vsub.mpr hsr

/-- The external version of the Pitot theorem: the tangent conditions on ω
force `BA + AD = CB + CD`. This is the first step of the official
solution. -/
lemma external_pitot {A B C D : Pt} {ω : Sphere Pt}
    (hconvex : ConvexQuadrilateral A B C D)
    (hR : 0 < ω.radius)
    (hωBA : ∃ T : Pt, [B, A, T].Sbtw ℝ ∧ ω.IsTangentAt T line[ℝ, B, A])
    (hωBC : ∃ T : Pt, [B, C, T].Sbtw ℝ ∧ ω.IsTangentAt T line[ℝ, B, C])
    (hωAD : ω.IsTangent line[ℝ, A, D])
    (hωCD : ω.IsTangent line[ℝ, C, D]) :
    dist B A + dist A D = dist C B + dist C D := by
  obtain ⟨T₁, hsbtw₁, htan₁⟩ := hωBA
  obtain ⟨T₂, hsbtw₂, htan₂⟩ := hωBC
  obtain ⟨U, htanU⟩ := hωAD
  obtain ⟨W, htanW⟩ := hωCD
  have h34 : 0 < planeOrientation.areaForm (D -ᵥ C) (A -ᵥ D) *
      planeOrientation.areaForm (A -ᵥ D) (B -ᵥ A) := by
    rcases hconvex with h | h
    · exact mul_pos h.2.2.1 h.2.2.2
    · exact mul_pos_of_neg_of_neg h.2.2.1 h.2.2.2
  have h32 : 0 < planeOrientation.areaForm (D -ᵥ C) (A -ᵥ D) *
      planeOrientation.areaForm (C -ᵥ B) (D -ᵥ C) := by
    rcases hconvex with h | h
    · exact mul_pos h.2.2.1 h.2.1
    · exact mul_pos_of_neg_of_neg h.2.2.1 h.2.1
  have hA := areaForm_center_left hR h34 hsbtw₁ htan₁ htanU
  have hB := areaForm_center_right hR h32 hsbtw₂ htan₂ htanW
  have huAD : A -ᵥ D ≠ 0 := by
    intro h
    rw [h, map_zero, map_zero, LinearMap.zero_apply, mul_zero] at h34
    exact lt_irrefl _ h34
  have huCD : C -ᵥ D ≠ 0 := by
    intro h
    have h' : D -ᵥ C = 0 := by rw [← neg_vsub_eq_vsub_rev C D, h, neg_zero]
    rw [h', map_zero, LinearMap.zero_apply, zero_mul] at h32
    exact lt_irrefl _ h32
  have hc3eq : planeOrientation.areaForm (A -ᵥ D) (C -ᵥ D) =
      planeOrientation.areaForm (D -ᵥ C) (A -ᵥ D) := by
    have e1 : D -ᵥ C = -(C -ᵥ D) := (neg_vsub_eq_vsub_rev C D).symm
    rw [e1, areaForm_neg_left, areaForm_swap]
  have hω : planeOrientation.areaForm (A -ᵥ D) (C -ᵥ D) ≠ 0 := by
    rw [hc3eq]
    intro h
    rw [h, zero_mul] at h34
    exact lt_irrefl _ h34
  have hω' : planeOrientation.areaForm (C -ᵥ D) (A -ᵥ D) ≠ 0 := by
    rw [areaForm_swap]
    exact neg_ne_zero.mpr hω
  have h1 : planeOrientation.areaForm (ω.center -ᵥ D) (A -ᵥ D) *
      planeOrientation.areaForm (A -ᵥ D) (C -ᵥ D) =
      ω.radius * ‖A -ᵥ D‖ * |planeOrientation.areaForm (A -ᵥ D) (C -ᵥ D)| := by
    rw [hc3eq]
    exact hA
  have h2 : planeOrientation.areaForm (ω.center -ᵥ D) (C -ᵥ D) *
      planeOrientation.areaForm (A -ᵥ D) (C -ᵥ D) =
      -ω.radius * ‖C -ᵥ D‖ * |planeOrientation.areaForm (A -ᵥ D) (C -ᵥ D)| := by
    rw [hc3eq]
    exact hB
  have hneg1 : ⟪ω.center -ᵥ D, A -ᵥ D⟫ < 0 :=
    inner_neg_of_areaForm_mul huAD hω hR h1 h2
  have hpos1 : 0 < ⟪ω.center -ᵥ D, D -ᵥ A⟫ := by
    have e : D -ᵥ A = -(A -ᵥ D) := (neg_vsub_eq_vsub_rev A D).symm
    rw [e, inner_neg_right]
    linarith [hneg1]
  have hA' : planeOrientation.areaForm (ω.center -ᵥ D) (A -ᵥ D) *
      planeOrientation.areaForm (C -ᵥ D) (A -ᵥ D) =
      -ω.radius * ‖A -ᵥ D‖ * |planeOrientation.areaForm (C -ᵥ D) (A -ᵥ D)| := by
    have e1 : planeOrientation.areaForm (D -ᵥ C) (A -ᵥ D) =
        -planeOrientation.areaForm (C -ᵥ D) (A -ᵥ D) := by
      have e2 : D -ᵥ C = -(C -ᵥ D) := (neg_vsub_eq_vsub_rev C D).symm
      rw [e2, areaForm_neg_left]
    rw [e1, abs_neg, mul_neg] at hA
    linarith [hA]
  have hB' : planeOrientation.areaForm (ω.center -ᵥ D) (C -ᵥ D) *
      planeOrientation.areaForm (C -ᵥ D) (A -ᵥ D) =
      ω.radius * ‖C -ᵥ D‖ * |planeOrientation.areaForm (C -ᵥ D) (A -ᵥ D)| := by
    have e1 : planeOrientation.areaForm (D -ᵥ C) (A -ᵥ D) =
        -planeOrientation.areaForm (C -ᵥ D) (A -ᵥ D) := by
      have e2 : D -ᵥ C = -(C -ᵥ D) := (neg_vsub_eq_vsub_rev C D).symm
      rw [e2, areaForm_neg_left]
    rw [e1, abs_neg, mul_neg] at hB
    linarith [hB]
  have hneg2 : ⟪ω.center -ᵥ D, C -ᵥ D⟫ < 0 :=
    inner_neg_of_areaForm_mul huCD hω' hR hB' hA'
  have hpos2 : 0 < ⟪ω.center -ᵥ D, D -ᵥ C⟫ := by
    have e : D -ᵥ C = -(C -ᵥ D) := (neg_vsub_eq_vsub_rev C D).symm
    rw [e, inner_neg_right]
    linarith [hneg2]
  have hperp1 : ⟪ω.center -ᵥ U, D -ᵥ A⟫ = 0 :=
    IsTangentAt.inner_vsub_center_eq_zero htanU
      (right_mem_affineSpan_pair ℝ A D) (left_mem_affineSpan_pair ℝ A D)
  have hwbtw1 : Wbtw ℝ A D U :=
    wbtw_of_projection_beyond htanU.mem_space (vsub_ne_zero.mp huAD) hperp1 hpos1
  have hperp2 : ⟪ω.center -ᵥ W, D -ᵥ C⟫ = 0 :=
    IsTangentAt.inner_vsub_center_eq_zero htanW
      (right_mem_affineSpan_pair ℝ C D) (left_mem_affineSpan_pair ℝ C D)
  have hwbtw2 : Wbtw ℝ C D W :=
    wbtw_of_projection_beyond htanW.mem_space (vsub_ne_zero.mp huCD) hperp2 hpos2
  have e1 := (List.sbtw_triple.mp hsbtw₁).wbtw.dist_add_dist
  have e2 := (List.sbtw_triple.mp hsbtw₂).wbtw.dist_add_dist
  have e3 := hwbtw1.dist_add_dist
  have e4 := hwbtw2.dist_add_dist
  have e5 : dist B T₁ = dist B T₂ :=
    EuclideanGeometry.Sphere.IsTangentAt.dist_eq_of_mem_of_mem htan₁ htan₂
      (left_mem_affineSpan_pair ℝ B A) (left_mem_affineSpan_pair ℝ B C)
  have e6 : dist A T₁ = dist A U :=
    EuclideanGeometry.Sphere.IsTangentAt.dist_eq_of_mem_of_mem htan₁ htanU
      (right_mem_affineSpan_pair ℝ B A) (left_mem_affineSpan_pair ℝ A D)
  have e7 : dist C T₂ = dist C W :=
    EuclideanGeometry.Sphere.IsTangentAt.dist_eq_of_mem_of_mem htan₂ htanW
      (right_mem_affineSpan_pair ℝ B C) (left_mem_affineSpan_pair ℝ C D)
  have e8 : dist D U = dist D W :=
    EuclideanGeometry.Sphere.IsTangentAt.dist_eq_of_mem_of_mem htanU htanW
      (right_mem_affineSpan_pair ℝ A D) (right_mem_affineSpan_pair ℝ C D)
  linarith [e1, e2, e3, e4, e5, e6, e7, e8, dist_comm B C]

/-- The touchpoints of the two incircles with `AC` are equidistant from `A`
and `C` respectively (`AP = CT`), i.e. they are reflections of each other
about the midpoint of `AC`. This is step 2 of the official solution, an
immediate consequence of the external Pitot theorem. -/
lemma dist_touchpoint_eq {A B C D : Pt} {ω : Sphere Pt}
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hADC : AffineIndependent ℝ ![A, D, C])
    (hconvex : ConvexQuadrilateral A B C D)
    (hR : 0 < ω.radius)
    (hωBA : ∃ T : Pt, [B, A, T].Sbtw ℝ ∧ ω.IsTangentAt T line[ℝ, B, A])
    (hωBC : ∃ T : Pt, [B, C, T].Sbtw ℝ ∧ ω.IsTangentAt T line[ℝ, B, C])
    (hωAD : ω.IsTangent line[ℝ, A, D])
    (hωCD : ω.IsTangent line[ℝ, C, D]) :
    dist A ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) =
      dist C ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) := by
  have hpitot := external_pitot hconvex hR hωBA hωBC hωAD hωCD
  have e1 := dist_touchpoint_insphere_left hABC
  have e2 := dist_touchpoint_insphere_right hADC
  linarith [hpitot, e1, e2, dist_comm A B, dist_comm A C, dist_comm B C]

/-- The B-excircle touchpoint of `ABC` on `AC` coincides with the incircle
touchpoint of `ADC` on `AC` (both are the reflection of the incircle
touchpoint of `ABC` about the midpoint of `AC`). -/
lemma excircle_touchpoint_eq_insphere_touchpoint {A B C D : Pt} {ω : Sphere Pt}
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hADC : AffineIndependent ℝ ![A, D, C])
    (hconvex : ConvexQuadrilateral A B C D)
    (hR : 0 < ω.radius)
    (hωBA : ∃ T : Pt, [B, A, T].Sbtw ℝ ∧ ω.IsTangentAt T line[ℝ, B, A])
    (hωBC : ∃ T : Pt, [B, C, T].Sbtw ℝ ∧ ω.IsTangentAt T line[ℝ, B, C])
    (hωAD : ω.IsTangent line[ℝ, A, D])
    (hωCD : ω.IsTangent line[ℝ, C, D]) :
    (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint {1} 1 =
      (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 := by
  have hd : dist C ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint {1} 1) =
      dist C ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) := by
    have e1 := dist_touchpoint_exsphere_right hABC
    have e2 := dist_touchpoint_eq hABC hADC hconvex hR hωBA hωBC hωAD hωCD
    have e3 := dist_touchpoint_insphere_left hABC
    linarith [e1, e2, e3, dist_comm A C]
  have hAC : A ≠ C := hABC.injective.ne (by decide : (0 : Fin 3) ≠ 2)
  have hwX : Wbtw ℝ A ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint {1} 1) C := by
    have h := (Affine.Triangle.sbtw_touchpoint_singleton (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt)
      (i₁ := 0) (i₂ := 1) (i₃ := 2) (by decide) (by decide) (by decide)).wbtw
    have p0 : (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).points 0 = A := rfl
    have p2 : (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).points 2 = C := rfl
    rw [p0, p2] at h
    exact h
  have hwY : Wbtw ℝ A ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) C :=
    wbtw_touchpoint_insphere hADC
  exact eq_of_dist_eq_of_wbtw hAC hwX hwY hd

/-- The D-excircle touchpoint of `ADC` on `AC` coincides with the incircle
touchpoint of `ABC` on `AC`. -/
lemma excenter_touchpoint_eq_insphere_touchpoint' {A B C D : Pt} {ω : Sphere Pt}
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hADC : AffineIndependent ℝ ![A, D, C])
    (hconvex : ConvexQuadrilateral A B C D)
    (hR : 0 < ω.radius)
    (hωBA : ∃ T : Pt, [B, A, T].Sbtw ℝ ∧ ω.IsTangentAt T line[ℝ, B, A])
    (hωBC : ∃ T : Pt, [B, C, T].Sbtw ℝ ∧ ω.IsTangentAt T line[ℝ, B, C])
    (hωAD : ω.IsTangent line[ℝ, A, D])
    (hωCD : ω.IsTangent line[ℝ, C, D]) :
    (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint {1} 1 =
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 := by
  have hd : dist A ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint {1} 1) =
      dist A ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) := by
    have e1 := dist_touchpoint_exsphere_left hADC
    have e2 := dist_touchpoint_insphere_left hABC
    have e3 := external_pitot hconvex hR hωBA hωBC hωAD hωCD
    linarith [e1, e2, e3, dist_comm A C, dist_comm C D, dist_comm A B, dist_comm B C]
  have hCA : C ≠ A := hABC.injective.ne (by decide : (2 : Fin 3) ≠ 0)
  have hwX : Wbtw ℝ C ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint {1} 1) A := by
    have h := (Affine.Triangle.sbtw_touchpoint_singleton (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt)
      (i₁ := 2) (i₂ := 1) (i₃ := 0) (by decide) (by decide) (by decide)).wbtw
    have p0 : (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).points 0 = A := rfl
    have p2 : (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).points 2 = C := rfl
    rw [p0, p2] at h
    exact h
  have hwY : Wbtw ℝ C ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) A :=
    (wbtw_touchpoint_insphere hABC).symm
  exact eq_of_dist_eq_of_wbtw hCA hwX hwY hd

/-- The product form of the "distance from center to tangent line equals
radius" identity: for a circle `ω` tangent to `line[ℝ, B, P]`, with its
center strictly on the same side of the line as a point `Q`, the product of
the signed determinants of `ω.center -ᵥ B` and `Q -ᵥ B` against the
direction `P -ᵥ B` equals `ω.radius * ‖P -ᵥ B‖` times the absolute
determinant. This packages the magnitude computation
`IsTangentAt.abs_inner_vsub_center_rot90` (moving the foot of the
perpendicular from the touchpoint `T` to `B`, which does not change the
normal component) with the sign bridge `sSameSide_iff_areaForm_mul_pos`. -/
lemma areaForm_center_mul_areaForm_of_isTangentAt {B P Q T : Pt} {ω : Sphere Pt}
    (hP : P -ᵥ B ≠ 0) (hr : 0 < ω.radius) (hT : ω.IsTangentAt T line[ℝ, B, P])
    (hss : line[ℝ, B, P].SSameSide ω.center Q) :
    planeOrientation.areaForm (ω.center -ᵥ B) (P -ᵥ B) *
        planeOrientation.areaForm (Q -ᵥ B) (P -ᵥ B) =
      ω.radius * ‖P -ᵥ B‖ * |planeOrientation.areaForm (Q -ᵥ B) (P -ᵥ B)| := by
  have hmag : |⟪ω.center -ᵥ T, rot90 (P -ᵥ B)⟫| = ω.radius * ‖P -ᵥ B‖ :=
    IsTangentAt.abs_inner_vsub_center_rot90 hT
      (right_mem_affineSpan_pair ℝ B P) (left_mem_affineSpan_pair ℝ B P) hr
  have hdir : T -ᵥ B ∈ line[ℝ, B, P].direction :=
    AffineSubspace.vsub_mem_direction hT.mem_space (left_mem_affineSpan_pair ℝ B P)
  rw [direction_affineSpan, vectorSpan_pair_rev] at hdir
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hdir
  have hshift : ⟪ω.center -ᵥ B, rot90 (P -ᵥ B)⟫ = ⟪ω.center -ᵥ T, rot90 (P -ᵥ B)⟫ := by
    have e : ω.center -ᵥ B = (ω.center -ᵥ T) + (T -ᵥ B) :=
      (vsub_add_vsub_cancel ω.center T B).symm
    rw [e, ← hc, inner_add_left, real_inner_smul_left, inner_rot90_right (P -ᵥ B) (P -ᵥ B),
      areaForm_self, neg_zero, mul_zero, add_zero]
  rw [← hshift] at hmag
  have habs : |planeOrientation.areaForm (ω.center -ᵥ B) (P -ᵥ B)| = ω.radius * ‖P -ᵥ B‖ := by
    have e : planeOrientation.areaForm (ω.center -ᵥ B) (P -ᵥ B) =
        -⟪ω.center -ᵥ B, rot90 (P -ᵥ B)⟫ := by
      rw [inner_rot90_right, neg_neg]
    rw [e, abs_neg]
    exact hmag
  have hsign : 0 < planeOrientation.areaForm (ω.center -ᵥ B) (P -ᵥ B) *
      planeOrientation.areaForm (Q -ᵥ B) (P -ᵥ B) :=
    (sSameSide_iff_areaForm_mul_pos hP).mp hss
  calc planeOrientation.areaForm (ω.center -ᵥ B) (P -ᵥ B) *
          planeOrientation.areaForm (Q -ᵥ B) (P -ᵥ B)
      = |planeOrientation.areaForm (ω.center -ᵥ B) (P -ᵥ B)| *
          |planeOrientation.areaForm (Q -ᵥ B) (P -ᵥ B)| := by
        rw [← abs_mul, abs_of_pos hsign]
    _ = ω.radius * ‖P -ᵥ B‖ * |planeOrientation.areaForm (Q -ᵥ B) (P -ᵥ B)| := by
        rw [habs]

/-- Signed normal component of the incenter at vertex `B` along `BA`. -/
lemma areaForm_incenter_left {A B C : Pt} (h : AffineIndependent ℝ ![A, B, C]) :
    planeOrientation.areaForm ((⟨![A, B, C], h⟩ : Triangle ℝ Pt).incenter -ᵥ B) (A -ᵥ B) *
        planeOrientation.areaForm (A -ᵥ B) (C -ᵥ B) =
      -(⟨![A, B, C], h⟩ : Triangle ℝ Pt).inradius * ‖A -ᵥ B‖ *
        |planeOrientation.areaForm (A -ᵥ B) (C -ᵥ B)| := by
  set t : Triangle ℝ Pt := ⟨![A, B, C], h⟩
  have hp0 : t.points 0 = A := rfl
  have hp1 : t.points 1 = B := rfl
  have hp2 : t.points 2 = C := rfl
  have hu : A -ᵥ B ≠ 0 := vsub_ne_zero.mpr (h.injective.ne (by decide : (0 : Fin 3) ≠ 1))
  have hface : affineSpan ℝ (Set.range (t.faceOpposite 2).points) = line[ℝ, B, A] := by
    rw [Simplex.range_faceOpposite_points]
    have hc : ({2}ᶜ : Set (Fin 3)) = {0, 1} := by grind
    rw [hc, Set.image_insert_eq, Set.image_singleton, hp0, hp1, Set.pair_comm]
  have htan : t.insphere.IsTangentAt (t.touchpoint ∅ 2) line[ℝ, B, A] := by
    rw [← hface]
    exact t.isTangentAt_insphere_touchpoint 2
  have hss : line[ℝ, B, A].SSameSide t.incenter C := by
    have h1 := t.sSameSide_incenter_point 2
    rw [hface, hp2] at h1
    exact h1
  have key : planeOrientation.areaForm (t.incenter -ᵥ B) (A -ᵥ B) *
        planeOrientation.areaForm (C -ᵥ B) (A -ᵥ B) =
      t.inradius * ‖A -ᵥ B‖ * |planeOrientation.areaForm (C -ᵥ B) (A -ᵥ B)| :=
    areaForm_center_mul_areaForm_of_isTangentAt hu t.inradius_pos htan hss
  rw [areaForm_swap (C -ᵥ B) (A -ᵥ B), abs_neg] at key
  linear_combination -key

/-- Signed normal component of the incenter at vertex `B` along `BC`. -/
lemma areaForm_incenter_right {A B C : Pt} (h : AffineIndependent ℝ ![A, B, C]) :
    planeOrientation.areaForm ((⟨![A, B, C], h⟩ : Triangle ℝ Pt).incenter -ᵥ B) (C -ᵥ B) *
        planeOrientation.areaForm (A -ᵥ B) (C -ᵥ B) =
      (⟨![A, B, C], h⟩ : Triangle ℝ Pt).inradius * ‖C -ᵥ B‖ *
        |planeOrientation.areaForm (A -ᵥ B) (C -ᵥ B)| := by
  set t : Triangle ℝ Pt := ⟨![A, B, C], h⟩
  have hp0 : t.points 0 = A := rfl
  have hp1 : t.points 1 = B := rfl
  have hp2 : t.points 2 = C := rfl
  have hv : C -ᵥ B ≠ 0 := vsub_ne_zero.mpr (h.injective.ne (by decide : (2 : Fin 3) ≠ 1))
  have hface : affineSpan ℝ (Set.range (t.faceOpposite 0).points) = line[ℝ, B, C] := by
    rw [Simplex.range_faceOpposite_points]
    have hc : ({0}ᶜ : Set (Fin 3)) = {1, 2} := by grind
    rw [hc, Set.image_insert_eq, Set.image_singleton, hp1, hp2]
  have htan : t.insphere.IsTangentAt (t.touchpoint ∅ 0) line[ℝ, B, C] := by
    rw [← hface]
    exact t.isTangentAt_insphere_touchpoint 0
  have hss : line[ℝ, B, C].SSameSide t.incenter A := by
    have h1 := t.sSameSide_incenter_point 0
    rw [hface, hp0] at h1
    exact h1
  exact areaForm_center_mul_areaForm_of_isTangentAt hv t.inradius_pos htan hss

/-- Signed normal component of the B-excenter at vertex `B` along `BA`. -/
lemma areaForm_excenter_left {A B C : Pt} (h : AffineIndependent ℝ ![A, B, C]) :
    planeOrientation.areaForm ((⟨![A, B, C], h⟩ : Triangle ℝ Pt).excenter {1} -ᵥ B) (A -ᵥ B) *
        planeOrientation.areaForm (A -ᵥ B) (C -ᵥ B) =
      -(⟨![A, B, C], h⟩ : Triangle ℝ Pt).exradius {1} * ‖A -ᵥ B‖ *
        |planeOrientation.areaForm (A -ᵥ B) (C -ᵥ B)| := by
  set t : Triangle ℝ Pt := ⟨![A, B, C], h⟩
  have hp0 : t.points 0 = A := rfl
  have hp1 : t.points 1 = B := rfl
  have hp2 : t.points 2 = C := rfl
  have hu : A -ᵥ B ≠ 0 := vsub_ne_zero.mpr (h.injective.ne (by decide : (0 : Fin 3) ≠ 1))
  have hface : affineSpan ℝ (Set.range (t.faceOpposite 2).points) = line[ℝ, B, A] := by
    rw [Simplex.range_faceOpposite_points]
    have hc : ({2}ᶜ : Set (Fin 3)) = {0, 1} := by grind
    rw [hc, Set.image_insert_eq, Set.image_singleton, hp0, hp1, Set.pair_comm]
  have htan : (t.exsphere {1}).IsTangentAt (t.touchpoint {1} 2) line[ℝ, B, A] := by
    rw [← hface]
    exact (t.excenterExists_singleton 1).isTangentAt_touchpoint 2
  have hss : line[ℝ, B, A].SSameSide (t.excenter {1}) C := by
    have h1 := t.sSameSide_excenter_singleton_point (show (2 : Fin 3) ≠ 1 by decide)
    rw [hface, hp2] at h1
    exact h1
  have key : planeOrientation.areaForm (t.excenter {1} -ᵥ B) (A -ᵥ B) *
        planeOrientation.areaForm (C -ᵥ B) (A -ᵥ B) =
      t.exradius {1} * ‖A -ᵥ B‖ * |planeOrientation.areaForm (C -ᵥ B) (A -ᵥ B)| :=
    areaForm_center_mul_areaForm_of_isTangentAt hu (t.exradius_singleton_pos 1) htan hss
  rw [areaForm_swap (C -ᵥ B) (A -ᵥ B), abs_neg] at key
  linear_combination -key

/-- Signed normal component of the B-excenter at vertex `B` along `BC`. -/
lemma areaForm_excenter_right {A B C : Pt} (h : AffineIndependent ℝ ![A, B, C]) :
    planeOrientation.areaForm ((⟨![A, B, C], h⟩ : Triangle ℝ Pt).excenter {1} -ᵥ B) (C -ᵥ B) *
        planeOrientation.areaForm (A -ᵥ B) (C -ᵥ B) =
      (⟨![A, B, C], h⟩ : Triangle ℝ Pt).exradius {1} * ‖C -ᵥ B‖ *
        |planeOrientation.areaForm (A -ᵥ B) (C -ᵥ B)| := by
  set t : Triangle ℝ Pt := ⟨![A, B, C], h⟩
  have hp0 : t.points 0 = A := rfl
  have hp1 : t.points 1 = B := rfl
  have hp2 : t.points 2 = C := rfl
  have hv : C -ᵥ B ≠ 0 := vsub_ne_zero.mpr (h.injective.ne (by decide : (2 : Fin 3) ≠ 1))
  have hface : affineSpan ℝ (Set.range (t.faceOpposite 0).points) = line[ℝ, B, C] := by
    rw [Simplex.range_faceOpposite_points]
    have hc : ({0}ᶜ : Set (Fin 3)) = {1, 2} := by grind
    rw [hc, Set.image_insert_eq, Set.image_singleton, hp1, hp2]
  have htan : (t.exsphere {1}).IsTangentAt (t.touchpoint {1} 0) line[ℝ, B, C] := by
    rw [← hface]
    exact (t.excenterExists_singleton 1).isTangentAt_touchpoint 0
  have hss : line[ℝ, B, C].SSameSide (t.excenter {1}) A := by
    have h1 := t.sSameSide_excenter_singleton_point (show (0 : Fin 3) ≠ 1 by decide)
    rw [hface, hp0] at h1
    exact h1
  exact areaForm_center_mul_areaForm_of_isTangentAt hv (t.exradius_singleton_pos 1) htan hss

/-- Signed normal component of `ω.center` at vertex `B` along `BA`
(negative pattern). The sign chain is: `⟪O -ᵥ T₁, rot90 u⟫` has the sign
of `T₂`'s side over `BA`, which is `C`'s side by the ray hypothesis. -/
lemma areaForm_center_B_left {A B C T₁ T₂ : Pt} {ω : Sphere Pt}
    (hωf : planeOrientation.areaForm (A -ᵥ B) (C -ᵥ B) ≠ 0)
    (hR : 0 < ω.radius)
    (_hsbtw₁ : [B, A, T₁].Sbtw ℝ)
    (htan₁ : ω.IsTangentAt T₁ line[ℝ, B, A])
    (hsbtw₂ : [B, C, T₂].Sbtw ℝ)
    (htan₂ : ω.IsTangentAt T₂ line[ℝ, B, C]) :
    planeOrientation.areaForm (ω.center -ᵥ B) (A -ᵥ B) *
        planeOrientation.areaForm (A -ᵥ B) (C -ᵥ B) =
      -ω.radius * ‖A -ᵥ B‖ * |planeOrientation.areaForm (A -ᵥ B) (C -ᵥ B)| := by
  set u := A -ᵥ B with hu_def
  set v := C -ᵥ B with hv_def
  have hu : u ≠ 0 := by
    intro h
    apply hωf
    rw [h, map_zero, LinearMap.zero_apply]
  have hv : v ≠ 0 := by
    intro h
    apply hωf
    rw [h, map_zero]
  -- `T₂ ≠ T₁`: the lines `BA` and `BC` meet only in `B`, and `T₂ ≠ B`.
  have hne : T₂ ≠ T₁ := by
    intro hEq
    have h1 : T₂ -ᵥ B ∈ line[ℝ, B, A].direction := by
      rw [hEq]
      exact AffineSubspace.vsub_mem_direction htan₁.mem_space (left_mem_affineSpan_pair ℝ B A)
    have h2 : T₂ -ᵥ B ∈ line[ℝ, B, C].direction :=
      AffineSubspace.vsub_mem_direction htan₂.mem_space (left_mem_affineSpan_pair ℝ B C)
    rw [direction_affineSpan, vectorSpan_pair_rev] at h1 h2
    obtain ⟨c₁, hc₁⟩ := Submodule.mem_span_singleton.mp h1
    obtain ⟨c₂, hc₂⟩ := Submodule.mem_span_singleton.mp h2
    have h0 : c₁ * planeOrientation.areaForm u v = 0 := by
      have e : c₁ • u = c₂ • v := by rw [hc₁, hc₂]
      have h3 := congrArg (fun z : V => planeOrientation.areaForm z v) e
      rw [map_smul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul,
        smul_eq_mul, areaForm_self, mul_zero] at h3
      exact h3
    have hc₁0 : c₁ = 0 := by
      rcases mul_eq_zero.mp h0 with h | h
      · exact h
      · exact absurd h hωf
    have hT2B : T₂ = B := by
      have h : T₂ -ᵥ B = 0 := by rw [← hc₁, hc₁0, zero_smul]
      exact vsub_eq_zero_iff_eq.mp h
    have hSbtw := List.sbtw_triple.mp hsbtw₂
    rw [hT2B] at hSbtw
    have hray := hSbtw.1.sameRay_vsub
    have hCB : C -ᵥ B = 0 := by
      by_contra hne0
      obtain ⟨r₁, r₂, hr₁, hr₂, hrr⟩ :=
        hray.exists_pos hne0 (vsub_ne_zero.mpr (vsub_ne_zero.mp hne0).symm)
      have e : B -ᵥ C = -(C -ᵥ B) := (neg_vsub_eq_vsub_rev C B).symm
      rw [e, smul_neg] at hrr
      have h0 : (r₁ + r₂) • (C -ᵥ B) = 0 := by
        rw [add_smul, hrr, neg_add_cancel]
      rcases smul_eq_zero.mp h0 with h | h
      · linarith [h, hr₁, hr₂]
      · exact hne0 h
    exact hSbtw.2.1 (vsub_eq_zero_iff_eq.mp hCB)
  -- `areaForm (O -ᵥ B) u = -⟪O -ᵥ T₁, rot90 u⟫`
  have hT1B : ∃ c : ℝ, c • u = T₁ -ᵥ B := by
    have h1 : T₁ -ᵥ B ∈ line[ℝ, B, A].direction :=
      AffineSubspace.vsub_mem_direction htan₁.mem_space (left_mem_affineSpan_pair ℝ B A)
    rw [direction_affineSpan, vectorSpan_pair_rev] at h1
    exact Submodule.mem_span_singleton.mp h1
  obtain ⟨c₁, hc₁⟩ := hT1B
  have hT1u : ⟪T₁ -ᵥ B, rot90 u⟫ = 0 := by
    rw [← hc₁, real_inner_smul_left, inner_rot90_right, areaForm_self, neg_zero, mul_zero]
  have hAf : planeOrientation.areaForm (ω.center -ᵥ B) u = -⟪ω.center -ᵥ T₁, rot90 u⟫ := by
    have e : ω.center -ᵥ B = (ω.center -ᵥ T₁) + (T₁ -ᵥ B) :=
      (vsub_add_vsub_cancel (ω.center) T₁ B).symm
    have h0 : planeOrientation.areaForm (T₁ -ᵥ B) u = 0 := by
      rw [← hc₁, map_smul, LinearMap.smul_apply, areaForm_self, smul_zero]
    rw [inner_rot90_right, e, map_add, LinearMap.add_apply, h0, add_zero, neg_neg]
  -- magnitude
  have hMag0 : |⟪ω.center -ᵥ T₁, rot90 (B -ᵥ A)⟫| = ω.radius * ‖B -ᵥ A‖ :=
    IsTangentAt.abs_inner_vsub_center_rot90 htan₁
      (left_mem_affineSpan_pair ℝ B A) (right_mem_affineSpan_pair ℝ B A) hR
  have hMag : |⟪ω.center -ᵥ T₁, rot90 u⟫| = ω.radius * ‖u‖ := by
    have e1 : B -ᵥ A = -u := by rw [hu_def, neg_vsub_eq_vsub_rev]
    rw [e1, map_neg, inner_neg_right, abs_neg, norm_neg] at hMag0
    exact hMag0
  -- sign chain
  obtain ⟨τ, hτpos, hτ⟩ := exists_pos_smul_vsub_of_sbtw (List.sbtw_triple.mp hsbtw₂)
  have hT2T1 : ⟪T₂ -ᵥ T₁, rot90 u⟫ = (τ + 1) * planeOrientation.areaForm u v := by
    have hspan1 : ⟪T₁ -ᵥ B, rot90 u⟫ = 0 := hT1u
    have e1 : T₂ -ᵥ T₁ = (T₂ -ᵥ B) - (T₁ -ᵥ B) := (vsub_sub_vsub_cancel_right T₂ T₁ B).symm
    have e2 : T₂ -ᵥ B = (τ + 1) • v := by
      have e3 : T₂ -ᵥ B = (T₂ -ᵥ C) + (C -ᵥ B) := (vsub_add_vsub_cancel T₂ C B).symm
      rw [e3, hτ, add_smul, one_smul, ← hv_def]
    have h4 : ⟪v, rot90 u⟫ = planeOrientation.areaForm u v := by
      rw [inner_rot90_right, areaForm_swap, neg_neg]
    rw [e1, inner_sub_left, hspan1, sub_zero, e2, real_inner_smul_left, h4]
  have hchord : 0 < ⟪T₂ -ᵥ T₁, ω.center -ᵥ T₁⟫ :=
    IsTangentAt.inner_vsub_center_pos htan₁ htan₂.mem_sphere hne
  have hperp : ⟪ω.center -ᵥ T₁, u⟫ = 0 :=
    IsTangentAt.inner_vsub_center_eq_zero htan₁
      (right_mem_affineSpan_pair ℝ B A) (left_mem_affineSpan_pair ℝ B A)
  have hdecomp : ω.center -ᵥ T₁ =
      (⟪ω.center -ᵥ T₁, rot90 u⟫ / ‖u‖ ^ 2) • rot90 u := by
    have h := eq_smul_add_smul_rightAngleRotation (ω.center -ᵥ T₁) u hu
    rw [hperp, zero_div, zero_smul, zero_add] at h
    exact h
  have hu2 : 0 < ‖u‖ ^ 2 := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hu)
  have hsign : 0 < ⟪ω.center -ᵥ T₁, rot90 u⟫ * planeOrientation.areaForm u v := by
    rw [hdecomp, real_inner_smul_right, hT2T1] at hchord
    have hrw : (⟪ω.center -ᵥ T₁, rot90 u⟫ / ‖u‖ ^ 2) * ((τ + 1) * planeOrientation.areaForm u v) =
        ⟪ω.center -ᵥ T₁, rot90 u⟫ * planeOrientation.areaForm u v * (τ + 1) / ‖u‖ ^ 2 := by
      ring
    rw [hrw] at hchord
    have h1 : 0 < ⟪ω.center -ᵥ T₁, rot90 u⟫ * planeOrientation.areaForm u v * (τ + 1) := by
      have h2 := mul_pos hchord hu2
      rwa [div_mul_cancel₀ _ hu2.ne'] at h2
    have hτ1 : 0 < τ + 1 := by linarith [hτpos]
    exact pos_of_mul_pos_left h1 hτ1.le
  -- assemble
  have hneg : planeOrientation.areaForm (ω.center -ᵥ B) u * planeOrientation.areaForm u v < 0 := by
    rw [hAf, neg_mul, neg_lt_zero]
    exact hsign
  have hfin : planeOrientation.areaForm (ω.center -ᵥ B) u * planeOrientation.areaForm u v =
      -(|⟪ω.center -ᵥ T₁, rot90 u⟫| * |planeOrientation.areaForm u v|) := by
    rw [hAf, ← abs_mul, abs_of_pos hsign, neg_mul]
  rw [hfin, hMag]
  ring

/-- Signed normal component of `ω.center` at vertex `B` along `BC`
(positive pattern). Mirror of `areaForm_center_B_left`. -/
lemma areaForm_center_B_right {A B C T₁ T₂ : Pt} {ω : Sphere Pt}
    (hωf : planeOrientation.areaForm (A -ᵥ B) (C -ᵥ B) ≠ 0)
    (hR : 0 < ω.radius)
    (hsbtw₁ : [B, A, T₁].Sbtw ℝ)
    (htan₁ : ω.IsTangentAt T₁ line[ℝ, B, A])
    (hsbtw₂ : [B, C, T₂].Sbtw ℝ)
    (htan₂ : ω.IsTangentAt T₂ line[ℝ, B, C]) :
    planeOrientation.areaForm (ω.center -ᵥ B) (C -ᵥ B) *
        planeOrientation.areaForm (A -ᵥ B) (C -ᵥ B) =
      ω.radius * ‖C -ᵥ B‖ * |planeOrientation.areaForm (A -ᵥ B) (C -ᵥ B)| := by
  set u := A -ᵥ B with hu_def
  set v := C -ᵥ B with hv_def
  have hu : u ≠ 0 := by
    intro h
    apply hωf
    rw [h, map_zero, LinearMap.zero_apply]
  have hv : v ≠ 0 := by
    intro h
    apply hωf
    rw [h, map_zero]
  have hne : T₂ ≠ T₁ := by
    intro hEq
    have h1 : T₂ -ᵥ B ∈ line[ℝ, B, A].direction := by
      rw [hEq]
      exact AffineSubspace.vsub_mem_direction htan₁.mem_space (left_mem_affineSpan_pair ℝ B A)
    have h2 : T₂ -ᵥ B ∈ line[ℝ, B, C].direction :=
      AffineSubspace.vsub_mem_direction htan₂.mem_space (left_mem_affineSpan_pair ℝ B C)
    rw [direction_affineSpan, vectorSpan_pair_rev] at h1 h2
    obtain ⟨c₁, hc₁⟩ := Submodule.mem_span_singleton.mp h1
    obtain ⟨c₂, hc₂⟩ := Submodule.mem_span_singleton.mp h2
    have h0 : c₁ * planeOrientation.areaForm u v = 0 := by
      have e : c₁ • u = c₂ • v := by rw [hc₁, hc₂]
      have h3 := congrArg (fun z : V => planeOrientation.areaForm z v) e
      rw [map_smul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul,
        smul_eq_mul, areaForm_self, mul_zero] at h3
      exact h3
    have hc₁0 : c₁ = 0 := by
      rcases mul_eq_zero.mp h0 with h | h
      · exact h
      · exact absurd h hωf
    have hT2B : T₂ = B := by
      have h : T₂ -ᵥ B = 0 := by rw [← hc₁, hc₁0, zero_smul]
      exact vsub_eq_zero_iff_eq.mp h
    have hSbtw := List.sbtw_triple.mp hsbtw₂
    rw [hT2B] at hSbtw
    have hray := hSbtw.1.sameRay_vsub
    have hCB : C -ᵥ B = 0 := by
      by_contra hne0
      obtain ⟨r₁, r₂, hr₁, hr₂, hrr⟩ :=
        hray.exists_pos hne0 (vsub_ne_zero.mpr (vsub_ne_zero.mp hne0).symm)
      have e : B -ᵥ C = -(C -ᵥ B) := (neg_vsub_eq_vsub_rev C B).symm
      rw [e, smul_neg] at hrr
      have h0 : (r₁ + r₂) • (C -ᵥ B) = 0 := by
        rw [add_smul, hrr, neg_add_cancel]
      rcases smul_eq_zero.mp h0 with h | h
      · linarith [h, hr₁, hr₂]
      · exact hne0 h
    exact hSbtw.2.1 (vsub_eq_zero_iff_eq.mp hCB)
  have hT2Bspan : ∃ c : ℝ, c • v = T₂ -ᵥ B := by
    have h1 : T₂ -ᵥ B ∈ line[ℝ, B, C].direction :=
      AffineSubspace.vsub_mem_direction htan₂.mem_space (left_mem_affineSpan_pair ℝ B C)
    rw [direction_affineSpan, vectorSpan_pair_rev] at h1
    exact Submodule.mem_span_singleton.mp h1
  obtain ⟨c₂, hc₂⟩ := hT2Bspan
  have hT2v : ⟪T₂ -ᵥ B, rot90 v⟫ = 0 := by
    rw [← hc₂, real_inner_smul_left, inner_rot90_right, areaForm_self, neg_zero, mul_zero]
  have hAf : planeOrientation.areaForm (ω.center -ᵥ B) v = -⟪ω.center -ᵥ T₂, rot90 v⟫ := by
    have e : ω.center -ᵥ B = (ω.center -ᵥ T₂) + (T₂ -ᵥ B) :=
      (vsub_add_vsub_cancel (ω.center) T₂ B).symm
    have h0 : planeOrientation.areaForm (T₂ -ᵥ B) v = 0 := by
      rw [← hc₂, map_smul, LinearMap.smul_apply, areaForm_self, smul_zero]
    rw [inner_rot90_right, e, map_add, LinearMap.add_apply, h0, add_zero, neg_neg]
  have hMag0 : |⟪ω.center -ᵥ T₂, rot90 (B -ᵥ C)⟫| = ω.radius * ‖B -ᵥ C‖ :=
    IsTangentAt.abs_inner_vsub_center_rot90 htan₂
      (left_mem_affineSpan_pair ℝ B C) (right_mem_affineSpan_pair ℝ B C) hR
  have hMag : |⟪ω.center -ᵥ T₂, rot90 v⟫| = ω.radius * ‖v‖ := by
    have e1 : B -ᵥ C = -v := by rw [hv_def, neg_vsub_eq_vsub_rev]
    rw [e1, map_neg, inner_neg_right, abs_neg, norm_neg] at hMag0
    exact hMag0
  obtain ⟨σ, hσpos, hσ⟩ := exists_pos_smul_vsub_of_sbtw (List.sbtw_triple.mp hsbtw₁)
  have hT1T2 : ⟪T₁ -ᵥ T₂, rot90 v⟫ = -(σ + 1) * planeOrientation.areaForm u v := by
    have e1 : T₁ -ᵥ T₂ = (T₁ -ᵥ B) - (T₂ -ᵥ B) := (vsub_sub_vsub_cancel_right T₁ T₂ B).symm
    have e2 : T₁ -ᵥ B = (σ + 1) • u := by
      have e3 : T₁ -ᵥ B = (T₁ -ᵥ A) + (A -ᵥ B) := (vsub_add_vsub_cancel T₁ A B).symm
      rw [e3, hσ, add_smul, one_smul, ← hu_def]
    have h4 : ⟪u, rot90 v⟫ = -planeOrientation.areaForm u v := by
      rw [inner_rot90_right]
    rw [e1, inner_sub_left, hT2v, sub_zero, e2, real_inner_smul_left, h4]
    ring
  have hchord : 0 < ⟪T₁ -ᵥ T₂, ω.center -ᵥ T₂⟫ :=
    IsTangentAt.inner_vsub_center_pos htan₂ htan₁.mem_sphere hne.symm
  have hperp : ⟪ω.center -ᵥ T₂, v⟫ = 0 :=
    IsTangentAt.inner_vsub_center_eq_zero htan₂
      (right_mem_affineSpan_pair ℝ B C) (left_mem_affineSpan_pair ℝ B C)
  have hdecomp : ω.center -ᵥ T₂ =
      (⟪ω.center -ᵥ T₂, rot90 v⟫ / ‖v‖ ^ 2) • rot90 v := by
    have h := eq_smul_add_smul_rightAngleRotation (ω.center -ᵥ T₂) v hv
    rw [hperp, zero_div, zero_smul, zero_add] at h
    exact h
  have hv2 : 0 < ‖v‖ ^ 2 := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hv)
  have hsign : ⟪ω.center -ᵥ T₂, rot90 v⟫ * planeOrientation.areaForm u v < 0 := by
    rw [hdecomp, real_inner_smul_right, hT1T2] at hchord
    have hrw : (⟪ω.center -ᵥ T₂, rot90 v⟫ / ‖v‖ ^ 2) * (-(σ + 1) * planeOrientation.areaForm u v) =
        ⟪ω.center -ᵥ T₂, rot90 v⟫ * planeOrientation.areaForm u v * (-(σ + 1)) / ‖v‖ ^ 2 := by
      ring
    rw [hrw] at hchord
    have h1 : 0 < ⟪ω.center -ᵥ T₂, rot90 v⟫ * planeOrientation.areaForm u v * (-(σ + 1)) := by
      have h2 := mul_pos hchord hv2
      rwa [div_mul_cancel₀ _ hv2.ne'] at h2
    have hσ1 : 0 < σ + 1 := by linarith [hσpos]
    have h4 : 0 < ⟪ω.center -ᵥ T₂, rot90 v⟫ * planeOrientation.areaForm u v * (-(σ + 1)) * (σ + 1) :=
      mul_pos h1 hσ1
    nlinarith [h4, hσ1]
  have hpos : 0 < planeOrientation.areaForm (ω.center -ᵥ B) v * planeOrientation.areaForm u v := by
    rw [hAf, neg_mul, neg_pos]
    exact hsign
  have hfin : planeOrientation.areaForm (ω.center -ᵥ B) v * planeOrientation.areaForm u v =
      |⟪ω.center -ᵥ T₂, rot90 v⟫| * |planeOrientation.areaForm u v| := by
    rw [hAf, ← abs_mul, abs_of_neg hsign, neg_mul]
  rw [hfin, hMag]

/-- Three affinely independent points give a nonzero determinant. -/
lemma areaForm_ne_zero_of_affineIndependent {A B C : Pt}
    (h : AffineIndependent ℝ ![A, B, C]) :
    planeOrientation.areaForm (A -ᵥ B) (C -ᵥ B) ≠ 0 := by
  have hu : A -ᵥ B ≠ 0 := vsub_ne_zero.mpr (h.injective.ne (by decide : (0 : Fin 3) ≠ 1))
  have hC : C ∉ line[ℝ, B, A] := by
    have h1 := h.notMem_affineSpan_sdiff 2 Set.univ
    have himg : (![A, B, C] '' (Set.univ \ {2})) = ({A, B} : Set Pt) := by
      have hs : (Set.univ \ {2}) = ({0, 1} : Set (Fin 3)) := by
        ext i
        fin_cases i <;> simp
      rw [hs, Set.image_insert_eq, Set.image_singleton]
      rfl
    rw [himg] at h1
    have h2 : affineSpan ℝ ({A, B} : Set Pt) = line[ℝ, B, A] := by
      rw [Set.pair_comm]
    rw [h2] at h1
    exact h1
  intro h0
  apply hC
  apply mem_line_of_areaForm_eq_zero hu
  rw [areaForm_swap, h0, neg_zero]

/-- The excircle center of the quadrilateral and the incenter of `ABC` lie
on the same ray from `B`, in the ratio of the radii: `O -ᵥ B = (R/r1) •
(O1 -ᵥ B)`. This is the "positive homothety at `B`" relation. -/
lemma center_vsub_B_eq_smul {A B C T₁ T₂ : Pt} {ω : Sphere Pt}
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hR : 0 < ω.radius)
    (hsbtw₁ : [B, A, T₁].Sbtw ℝ) (htan₁ : ω.IsTangentAt T₁ line[ℝ, B, A])
    (hsbtw₂ : [B, C, T₂].Sbtw ℝ) (htan₂ : ω.IsTangentAt T₂ line[ℝ, B, C]) :
    ω.center -ᵥ B = (ω.radius / (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius) •
      ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ B) := by
  set t : Triangle ℝ Pt := ⟨![A, B, C], hABC⟩
  have hu : A -ᵥ B ≠ 0 := vsub_ne_zero.mpr (hABC.injective.ne (by decide : (0 : Fin 3) ≠ 1))
  have hωf := areaForm_ne_zero_of_affineIndependent hABC
  have hO1u' : planeOrientation.areaForm (t.incenter -ᵥ B) (A -ᵥ B) *
      planeOrientation.areaForm (A -ᵥ B) (C -ᵥ B) =
      (-1 : ℝ) * (t.inradius * ‖A -ᵥ B‖ * |planeOrientation.areaForm (A -ᵥ B) (C -ᵥ B)|) := by
    rw [areaForm_incenter_left hABC]
    ring
  have hO1v' : planeOrientation.areaForm (t.incenter -ᵥ B) (C -ᵥ B) *
      planeOrientation.areaForm (A -ᵥ B) (C -ᵥ B) =
      (1 : ℝ) * (t.inradius * ‖C -ᵥ B‖ * |planeOrientation.areaForm (A -ᵥ B) (C -ᵥ B)|) := by
    rw [areaForm_incenter_right hABC]
    ring
  have hOu' : planeOrientation.areaForm (ω.center -ᵥ B) (A -ᵥ B) *
      planeOrientation.areaForm (A -ᵥ B) (C -ᵥ B) =
      ((1 : ℝ) * (-1 : ℝ)) * (ω.radius * ‖A -ᵥ B‖ *
        |planeOrientation.areaForm (A -ᵥ B) (C -ᵥ B)|) := by
    rw [areaForm_center_B_left hωf hR hsbtw₁ htan₁ hsbtw₂ htan₂]
    ring
  have hOv' : planeOrientation.areaForm (ω.center -ᵥ B) (C -ᵥ B) *
      planeOrientation.areaForm (A -ᵥ B) (C -ᵥ B) =
      ((1 : ℝ) * (1 : ℝ)) * (ω.radius * ‖C -ᵥ B‖ *
        |planeOrientation.areaForm (A -ᵥ B) (C -ᵥ B)|) := by
    rw [areaForm_center_B_right hωf hR hsbtw₁ htan₁ hsbtw₂ htan₂]
    ring
  have h := smul_of_areaForm_pattern hu hωf t.inradius_pos hR (Or.inl rfl)
    hO1u' hO1v' hOu' hOv'
  rwa [one_mul] at h

/-- The B-excircle center of `ABC` and its incenter lie on the same ray
from `B`, in the ratio of the radii: `E_B -ᵥ B = (r_B/r1) • (O1 -ᵥ B)`. -/
lemma excenter_vsub_B_eq_smul {A B C : Pt} (hABC : AffineIndependent ℝ ![A, B, C]) :
    (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).excenter {1} -ᵥ B =
      ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).exradius {1} /
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius) •
        ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ B) := by
  set t : Triangle ℝ Pt := ⟨![A, B, C], hABC⟩
  have hu : A -ᵥ B ≠ 0 := vsub_ne_zero.mpr (hABC.injective.ne (by decide : (0 : Fin 3) ≠ 1))
  have hωf := areaForm_ne_zero_of_affineIndependent hABC
  have hE1u' : planeOrientation.areaForm (t.excenter {1} -ᵥ B) (A -ᵥ B) *
      planeOrientation.areaForm (A -ᵥ B) (C -ᵥ B) =
      ((1 : ℝ) * (-1 : ℝ)) * (t.exradius {1} * ‖A -ᵥ B‖ *
        |planeOrientation.areaForm (A -ᵥ B) (C -ᵥ B)|) := by
    rw [areaForm_excenter_left hABC]
    ring
  have hE1v' : planeOrientation.areaForm (t.excenter {1} -ᵥ B) (C -ᵥ B) *
      planeOrientation.areaForm (A -ᵥ B) (C -ᵥ B) =
      ((1 : ℝ) * (1 : ℝ)) * (t.exradius {1} * ‖C -ᵥ B‖ *
        |planeOrientation.areaForm (A -ᵥ B) (C -ᵥ B)|) := by
    rw [areaForm_excenter_right hABC]
    ring
  have hO1u' : planeOrientation.areaForm (t.incenter -ᵥ B) (A -ᵥ B) *
      planeOrientation.areaForm (A -ᵥ B) (C -ᵥ B) =
      (-1 : ℝ) * (t.inradius * ‖A -ᵥ B‖ * |planeOrientation.areaForm (A -ᵥ B) (C -ᵥ B)|) := by
    rw [areaForm_incenter_left hABC]
    ring
  have hO1v' : planeOrientation.areaForm (t.incenter -ᵥ B) (C -ᵥ B) *
      planeOrientation.areaForm (A -ᵥ B) (C -ᵥ B) =
      (1 : ℝ) * (t.inradius * ‖C -ᵥ B‖ * |planeOrientation.areaForm (A -ᵥ B) (C -ᵥ B)|) := by
    rw [areaForm_incenter_right hABC]
    ring
  have h := smul_of_areaForm_pattern hu hωf t.inradius_pos (t.exradius_singleton_pos 1)
    (Or.inl rfl) hO1u' hO1v' hE1u' hE1v'
  rwa [one_mul] at h

/-- The negative homothety at `D`: `O -ᵥ D = -(R/r2) • (O2 -ᵥ D)`. This is
the mirror of `center_vsub_B_eq_smul`, with the sign flip coming from the
opposite wedges of `O` and `O2` at `D` (Lemmas A/B give `O`'s pattern
`(+,-)`, the incircle lemmas give `O2`'s pattern `(-,+)`). -/
lemma center_vsub_D_eq_neg_smul {A B C D : Pt} {ω : Sphere Pt}
    (_hABC : AffineIndependent ℝ ![A, B, C])
    (hADC : AffineIndependent ℝ ![A, D, C])
    (hconvex : ConvexQuadrilateral A B C D)
    (hR : 0 < ω.radius)
    (hωBA : ∃ T : Pt, [B, A, T].Sbtw ℝ ∧ ω.IsTangentAt T line[ℝ, B, A])
    (hωBC : ∃ T : Pt, [B, C, T].Sbtw ℝ ∧ ω.IsTangentAt T line[ℝ, B, C])
    (hωAD : ω.IsTangent line[ℝ, A, D])
    (hωCD : ω.IsTangent line[ℝ, C, D]) :
    ω.center -ᵥ D = -(ω.radius / (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius) •
      ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ D) := by
  set t₂ : Triangle ℝ Pt := ⟨![A, D, C], hADC⟩
  obtain ⟨T₁, hsbtw₁, htan₁⟩ := hωBA
  obtain ⟨T₂, hsbtw₂, htan₂⟩ := hωBC
  obtain ⟨U, htanU⟩ := hωAD
  obtain ⟨W, htanW⟩ := hωCD
  have h34 : 0 < planeOrientation.areaForm (D -ᵥ C) (A -ᵥ D) *
      planeOrientation.areaForm (A -ᵥ D) (B -ᵥ A) := by
    rcases hconvex with h | h
    · exact mul_pos h.2.2.1 h.2.2.2
    · exact mul_pos_of_neg_of_neg h.2.2.1 h.2.2.2
  have h32 : 0 < planeOrientation.areaForm (D -ᵥ C) (A -ᵥ D) *
      planeOrientation.areaForm (C -ᵥ B) (D -ᵥ C) := by
    rcases hconvex with h | h
    · exact mul_pos h.2.2.1 h.2.1
    · exact mul_pos_of_neg_of_neg h.2.2.1 h.2.1
  have hA := areaForm_center_left hR h34 hsbtw₁ htan₁ htanU
  have hB := areaForm_center_right hR h32 hsbtw₂ htan₂ htanW
  have hc3 : planeOrientation.areaForm (D -ᵥ C) (A -ᵥ D) =
      planeOrientation.areaForm (A -ᵥ D) (C -ᵥ D) := by
    have e1 : D -ᵥ C = -(C -ᵥ D) := (neg_vsub_eq_vsub_rev C D).symm
    rw [e1, areaForm_neg_left, areaForm_swap, neg_neg]
  rw [hc3] at hA hB
  have hu : A -ᵥ D ≠ 0 := vsub_ne_zero.mpr (hADC.injective.ne (by decide : (0 : Fin 3) ≠ 1))
  have hωf := areaForm_ne_zero_of_affineIndependent hADC
  have hO2u' : planeOrientation.areaForm (t₂.incenter -ᵥ D) (A -ᵥ D) *
      planeOrientation.areaForm (A -ᵥ D) (C -ᵥ D) =
      (-1 : ℝ) * (t₂.inradius * ‖A -ᵥ D‖ * |planeOrientation.areaForm (A -ᵥ D) (C -ᵥ D)|) := by
    rw [areaForm_incenter_left hADC]
    ring
  have hO2v' : planeOrientation.areaForm (t₂.incenter -ᵥ D) (C -ᵥ D) *
      planeOrientation.areaForm (A -ᵥ D) (C -ᵥ D) =
      (1 : ℝ) * (t₂.inradius * ‖C -ᵥ D‖ * |planeOrientation.areaForm (A -ᵥ D) (C -ᵥ D)|) := by
    rw [areaForm_incenter_right hADC]
    ring
  have hOu' : planeOrientation.areaForm (ω.center -ᵥ D) (A -ᵥ D) *
      planeOrientation.areaForm (A -ᵥ D) (C -ᵥ D) =
      ((-1 : ℝ) * (-1 : ℝ)) * (ω.radius * ‖A -ᵥ D‖ *
        |planeOrientation.areaForm (A -ᵥ D) (C -ᵥ D)|) := by
    rw [hA]
    ring
  have hOv' : planeOrientation.areaForm (ω.center -ᵥ D) (C -ᵥ D) *
      planeOrientation.areaForm (A -ᵥ D) (C -ᵥ D) =
      ((-1 : ℝ) * (1 : ℝ)) * (ω.radius * ‖C -ᵥ D‖ *
        |planeOrientation.areaForm (A -ᵥ D) (C -ᵥ D)|) := by
    rw [hB]
    ring
  have h := smul_of_areaForm_pattern hu hωf t₂.inradius_pos hR (Or.inr rfl)
    hO2u' hO2v' hOu' hOv'
  rwa [neg_one_mul] at h

/-- The determinant swap identity used to pass between the two
orientations of the `ConvexQuadrilateral` cross product. -/
lemma areaForm_DAC_eq_ADC {A C D : Pt} :
    planeOrientation.areaForm (D -ᵥ C) (A -ᵥ D) =
      planeOrientation.areaForm (A -ᵥ D) (C -ᵥ D) := by
  have e1 : D -ᵥ C = -(C -ᵥ D) := (neg_vsub_eq_vsub_rev C D).symm
  rw [e1, areaForm_neg_left, areaForm_swap, neg_neg]

/-- In a convex quadrilateral `ABCD`, the vertices `B` and `D` lie on
opposite sides of the diagonal line `AC` (determinant form). -/
lemma areaForm_mul_neg_of_convexQuadrilateral {A B C D : Pt}
    (h : ConvexQuadrilateral A B C D) :
    planeOrientation.areaForm (B -ᵥ A) (A -ᵥ C) *
      planeOrientation.areaForm (D -ᵥ A) (A -ᵥ C) < 0 := by
  have e1 : planeOrientation.areaForm (B -ᵥ A) (A -ᵥ C) =
      -planeOrientation.areaForm (B -ᵥ A) (C -ᵥ B) := by
    have e : A -ᵥ C = -((C -ᵥ B) + (B -ᵥ A)) := by
      rw [vsub_add_vsub_cancel C B A]
      exact (neg_vsub_eq_vsub_rev C A).symm
    rw [e, areaForm_neg_right, map_add, areaForm_self, add_zero]
  have e2 : planeOrientation.areaForm (D -ᵥ A) (A -ᵥ C) =
      planeOrientation.areaForm (D -ᵥ C) (A -ᵥ D) := by
    have e : A -ᵥ C = -((C -ᵥ D) + (D -ᵥ A)) := by
      rw [vsub_add_vsub_cancel C D A]
      exact (neg_vsub_eq_vsub_rev C A).symm
    rw [e, areaForm_neg_right, map_add, areaForm_self, add_zero,
      ← neg_vsub_eq_vsub_rev A D, areaForm_neg_left, neg_neg,
      show planeOrientation.areaForm (A -ᵥ D) (C -ᵥ D) =
        planeOrientation.areaForm (D -ᵥ C) (A -ᵥ D) from areaForm_DAC_eq_ADC.symm]
  rw [e1, e2]
  rcases h with h | h
  · exact mul_neg_of_neg_of_pos (by linarith [h.1]) h.2.2.1
  · exact mul_neg_of_pos_of_neg (by linarith [h.1]) (by linarith [h.2.2.1])

omit [Fact (finrank ℝ V = 2)] in
/-- If `a * b < 0` and `|a| = c * |b|` with `c > 0`, then `a = -c * b`. -/
lemma eq_neg_smul_of_mul_neg_abs {a b c : ℝ} (_hc : 0 < c) (habs : |a| = c * |b|)
    (hneg : a * b < 0) : a = -c * b := by
  have hb : b ≠ 0 := by
    intro h
    rw [h, mul_zero] at hneg
    exact lt_irrefl _ hneg
  have h1 : a / b = -|a / b| := by
    have h2 : a / b < 0 := by
      have h3 : (a / b) * (b * b) < 0 := by
        rw [← mul_assoc, div_mul_cancel₀ a hb]
        exact hneg
      rcases mul_neg_iff.mp h3 with h' | h'
      · exact absurd h'.2 (not_lt.mpr (mul_self_nonneg b))
      · exact h'.1
    rw [abs_of_neg h2, neg_neg]
  rw [abs_div, habs] at h1
  have h4 : c * |b| / |b| = c := by
    rw [mul_comm c |b|, mul_div_cancel_left₀ c (abs_pos.mpr hb).ne']
  rw [h4] at h1
  rw [← h1, div_mul_cancel₀ a hb]

/-- Signed normal relation between the two incircle touchpoints:
`T -ᵥ O2 = -(r2/r1) • (P -ᵥ O1)`, i.e. the foot vectors of the two
incenters on `AC` are antiparallel (the incenters lie on opposite sides of
`AC`). This gives the shared unit normal `n̂ = (P -ᵥ O1)/r1` of the whole
configuration. -/
lemma touchpoint_vsub_incenter_neg_smul {A B C D : Pt}
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hADC : AffineIndependent ℝ ![A, D, C])
    (hconvex : ConvexQuadrilateral A B C D) :
    (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 -ᵥ
      (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter =
      -((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius /
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius) •
        ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 -ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) := by
  set t : Triangle ℝ Pt := ⟨![A, B, C], hABC⟩
  set t₂ : Triangle ℝ Pt := ⟨![A, D, C], hADC⟩
  set w := A -ᵥ C
  have hw : w ≠ 0 := vsub_ne_zero.mpr (hABC.injective.ne (by decide : (0 : Fin 3) ≠ 2))
  -- tangencies of both inspheres with line AC
  have hface1 : affineSpan ℝ (Set.range (t.faceOpposite 1).points) = line[ℝ, A, C] := by
    have hp0 : t.points 0 = A := rfl
    have hp2 : t.points 2 = C := rfl
    rw [Simplex.range_faceOpposite_points]
    have hc : ({1}ᶜ : Set (Fin 3)) = {0, 2} := by grind
    rw [hc, Set.image_insert_eq, Set.image_singleton, hp0, hp2]
  have hface2 : affineSpan ℝ (Set.range (t₂.faceOpposite 1).points) = line[ℝ, A, C] := by
    have hp0 : t₂.points 0 = A := rfl
    have hp2 : t₂.points 2 = C := rfl
    rw [Simplex.range_faceOpposite_points]
    have hc : ({1}ᶜ : Set (Fin 3)) = {0, 2} := by grind
    rw [hc, Set.image_insert_eq, Set.image_singleton, hp0, hp2]
  have htan1 : t.insphere.IsTangentAt (t.touchpoint ∅ 1) line[ℝ, A, C] := by
    rw [← hface1]
    exact t.isTangentAt_insphere_touchpoint 1
  have htan2 : t₂.insphere.IsTangentAt (t₂.touchpoint ∅ 1) line[ℝ, A, C] := by
    rw [← hface2]
    exact t₂.isTangentAt_insphere_touchpoint 1
  -- perpendicularity
  have hperp1 : ⟪t.touchpoint ∅ 1 -ᵥ t.incenter, w⟫ = 0 := by
    have h := IsTangentAt.inner_vsub_center_eq_zero htan1
      (left_mem_affineSpan_pair ℝ A C) (right_mem_affineSpan_pair ℝ A C)
    rw [show t.touchpoint ∅ 1 -ᵥ t.incenter = -((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).insphere.center -ᵥ
        (t.touchpoint ∅ 1)) from (neg_vsub_eq_vsub_rev _ _).symm, inner_neg_left, h, neg_zero]
  have hperp2 : ⟪t₂.touchpoint ∅ 1 -ᵥ t₂.incenter, w⟫ = 0 := by
    have h := IsTangentAt.inner_vsub_center_eq_zero htan2
      (left_mem_affineSpan_pair ℝ A C) (right_mem_affineSpan_pair ℝ A C)
    rw [show t₂.touchpoint ∅ 1 -ᵥ t₂.incenter = -((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).insphere.center -ᵥ
        (t₂.touchpoint ∅ 1)) from (neg_vsub_eq_vsub_rev _ _).symm, inner_neg_left, h, neg_zero]
  -- magnitudes
  have hmag1 : |⟪t.touchpoint ∅ 1 -ᵥ t.incenter, rot90 w⟫| = t.inradius * ‖w‖ := by
    have h := IsTangentAt.abs_inner_vsub_center_rot90 htan1
      (left_mem_affineSpan_pair ℝ A C) (right_mem_affineSpan_pair ℝ A C) t.inradius_pos
    rw [show t.touchpoint ∅ 1 -ᵥ t.incenter = -((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).insphere.center -ᵥ
        (t.touchpoint ∅ 1)) from (neg_vsub_eq_vsub_rev _ _).symm, inner_neg_left, abs_neg]
    exact h
  have hmag2 : |⟪t₂.touchpoint ∅ 1 -ᵥ t₂.incenter, rot90 w⟫| = t₂.inradius * ‖w‖ := by
    have h := IsTangentAt.abs_inner_vsub_center_rot90 htan2
      (left_mem_affineSpan_pair ℝ A C) (right_mem_affineSpan_pair ℝ A C) t₂.inradius_pos
    rw [show t₂.touchpoint ∅ 1 -ᵥ t₂.incenter = -((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).insphere.center -ᵥ
        (t₂.touchpoint ∅ 1)) from (neg_vsub_eq_vsub_rev _ _).symm, inner_neg_left, abs_neg]
    exact h
  -- sign chain: the incenters are on opposite sides of AC
  have hss1 : line[ℝ, A, C].SSameSide t.incenter B := by
    have h1 := t.sSameSide_incenter_point 1
    rw [hface1] at h1
    have p1 : t.points 1 = B := rfl
    rw [p1] at h1
    exact h1
  have hss2 : line[ℝ, A, C].SSameSide t₂.incenter D := by
    have h1 := t₂.sSameSide_incenter_point 1
    rw [hface2] at h1
    have p1 : t₂.points 1 = D := rfl
    rw [p1] at h1
    exact h1
  have hw' : C -ᵥ A ≠ 0 := vsub_ne_zero.mpr (hABC.injective.ne (by decide : (2 : Fin 3) ≠ 0))
  have hsign1 : 0 < planeOrientation.areaForm (t.incenter -ᵥ A) w *
      planeOrientation.areaForm (B -ᵥ A) w := by
    have h1 := (sSameSide_iff_areaForm_mul_pos hw').mp hss1
    rw [show w = -(C -ᵥ A) from (neg_vsub_eq_vsub_rev C A).symm, areaForm_neg_right,
      areaForm_neg_right, neg_mul_neg]
    exact h1
  have hsign2 : 0 < planeOrientation.areaForm (t₂.incenter -ᵥ A) w *
      planeOrientation.areaForm (D -ᵥ A) w := by
    have h1 := (sSameSide_iff_areaForm_mul_pos hw').mp hss2
    rw [show w = -(C -ᵥ A) from (neg_vsub_eq_vsub_rev C A).symm, areaForm_neg_right,
      areaForm_neg_right, neg_mul_neg]
    exact h1
  have hsign3 : planeOrientation.areaForm (B -ᵥ A) w *
      planeOrientation.areaForm (D -ᵥ A) w < 0 :=
    areaForm_mul_neg_of_convexQuadrilateral hconvex
  have hsign4 : planeOrientation.areaForm (t₂.incenter -ᵥ A) w *
      planeOrientation.areaForm (t.incenter -ᵥ A) w < 0 := by
    have h1 := mul_pos hsign2 hsign1
    have h2 : (planeOrientation.areaForm (t₂.incenter -ᵥ A) w *
        planeOrientation.areaForm (D -ᵥ A) w) *
        (planeOrientation.areaForm (t.incenter -ᵥ A) w *
          planeOrientation.areaForm (B -ᵥ A) w) =
        (planeOrientation.areaForm (t₂.incenter -ᵥ A) w *
          planeOrientation.areaForm (t.incenter -ᵥ A) w) *
          (planeOrientation.areaForm (D -ᵥ A) w *
            planeOrientation.areaForm (B -ᵥ A) w) := by ring
    rw [h2] at h1
    rcases mul_pos_iff.mp h1 with h' | h'
    · linarith [h'.2, hsign3]
    · exact h'.1
  -- convert to the foot vectors (both negated, so the product stays negative)
  have hsign : ⟪t₂.touchpoint ∅ 1 -ᵥ t₂.incenter, rot90 w⟫ *
      ⟪t.touchpoint ∅ 1 -ᵥ t.incenter, rot90 w⟫ < 0 := by
    have e1 : planeOrientation.areaForm (t₂.touchpoint ∅ 1 -ᵥ t₂.incenter) w =
        -planeOrientation.areaForm (t₂.incenter -ᵥ A) w := by
      have hT : planeOrientation.areaForm (t₂.touchpoint ∅ 1 -ᵥ A) w = 0 := by
        have hmem : t₂.touchpoint ∅ 1 -ᵥ A ∈ line[ℝ, A, C].direction :=
          AffineSubspace.vsub_mem_direction htan2.mem_space (left_mem_affineSpan_pair ℝ A C)
        rw [direction_affineSpan, mem_vectorSpan_pair] at hmem
        obtain ⟨c, hc⟩ := hmem
        rw [← hc, map_smul, LinearMap.smul_apply, areaForm_self, smul_zero]
      have e : t₂.touchpoint ∅ 1 -ᵥ t₂.incenter =
          (t₂.touchpoint ∅ 1 -ᵥ A) + (A -ᵥ t₂.incenter) :=
        (vsub_add_vsub_cancel (t₂.touchpoint ∅ 1) A t₂.incenter).symm
      rw [e, map_add, LinearMap.add_apply, hT, zero_add,
        ← neg_vsub_eq_vsub_rev t₂.incenter A, areaForm_neg_left]
    have e2 : planeOrientation.areaForm (t.touchpoint ∅ 1 -ᵥ t.incenter) w =
        -planeOrientation.areaForm (t.incenter -ᵥ A) w := by
      have hP : planeOrientation.areaForm (t.touchpoint ∅ 1 -ᵥ A) w = 0 := by
        have hmem : t.touchpoint ∅ 1 -ᵥ A ∈ line[ℝ, A, C].direction :=
          AffineSubspace.vsub_mem_direction htan1.mem_space (left_mem_affineSpan_pair ℝ A C)
        rw [direction_affineSpan, mem_vectorSpan_pair] at hmem
        obtain ⟨c, hc⟩ := hmem
        rw [← hc, map_smul, LinearMap.smul_apply, areaForm_self, smul_zero]
      have e : t.touchpoint ∅ 1 -ᵥ t.incenter =
          (t.touchpoint ∅ 1 -ᵥ A) + (A -ᵥ t.incenter) :=
        (vsub_add_vsub_cancel (t.touchpoint ∅ 1) A t.incenter).symm
      rw [e, map_add, LinearMap.add_apply, hP, zero_add,
        ← neg_vsub_eq_vsub_rev t.incenter A, areaForm_neg_left]
    have h4 : ⟪t₂.touchpoint ∅ 1 -ᵥ t₂.incenter, rot90 w⟫ =
        -planeOrientation.areaForm (t₂.touchpoint ∅ 1 -ᵥ t₂.incenter) w := by
      rw [inner_rot90_right]
    have h5 : ⟪t.touchpoint ∅ 1 -ᵥ t.incenter, rot90 w⟫ =
        -planeOrientation.areaForm (t.touchpoint ∅ 1 -ᵥ t.incenter) w := by
      rw [inner_rot90_right]
    rw [h4, h5, e1, e2, neg_mul_neg, neg_mul_neg]
    exact hsign4
  -- the ratio
  have habs : |⟪t₂.touchpoint ∅ 1 -ᵥ t₂.incenter, rot90 w⟫| =
      (t₂.inradius / t.inradius) * |⟪t.touchpoint ∅ 1 -ᵥ t.incenter, rot90 w⟫| := by
    rw [hmag2, hmag1]
    field_simp [t.inradius_pos.ne']
  have key := eq_neg_smul_of_mul_neg_abs (div_pos t₂.inradius_pos t.inradius_pos) habs hsign
  -- back to vectors via the decomposition
  have hdec1 := eq_smul_add_smul_rightAngleRotation (t₂.touchpoint ∅ 1 -ᵥ t₂.incenter) w hw
  have hdec2 := eq_smul_add_smul_rightAngleRotation (t.touchpoint ∅ 1 -ᵥ t.incenter) w hw
  rw [hperp2, zero_div, zero_smul, zero_add] at hdec1
  rw [hperp1, zero_div, zero_smul, zero_add] at hdec2
  rw [hdec1, key]
  conv_rhs => rw [hdec2]
  rw [smul_smul, mul_div_assoc]

/-- The B-excenter offset from its touchpoint `T'` on line `AC` is the
incircle touchpoint offset scaled by the ratio of the radii:
`E_B -ᵥ T' = (r_B/r1) • (P -ᵥ O1)`. Both offsets are perpendicular to
`AC` (radii to the tangent points), their normal components have absolute
values `r_B * ‖AC‖` and `r1 * ‖AC‖` respectively, and they point to the
same side of `AC` because the excenter and the incenter lie on opposite
sides of `AC` while the touchpoint offsets are measured in opposite
directions. -/
lemma excenter_vsub_touchpoint_eq_smul {A B C : Pt}
    (hABC : AffineIndependent ℝ ![A, B, C]) :
    (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).excenter {1} -ᵥ
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint {1} 1 =
      ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).exradius {1} /
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius) •
        ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 -ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) := by
  set t : Triangle ℝ Pt := ⟨![A, B, C], hABC⟩
  have hp0 : t.points 0 = A := rfl
  have hp1 : t.points 1 = B := rfl
  have hp2 : t.points 2 = C := rfl
  have hAC : A ≠ C := hABC.injective.ne (by decide : (0 : Fin 3) ≠ 2)
  have hwne : A -ᵥ C ≠ 0 := vsub_ne_zero.mpr hAC
  have hwpos : 0 < ‖A -ᵥ C‖ := norm_pos_iff.mpr hwne
  have hr1 : 0 < t.inradius := t.inradius_pos
  have hrB : 0 < t.exradius {1} := t.exradius_singleton_pos 1
  have hr1ne : t.inradius ≠ 0 := hr1.ne'
  have hface : affineSpan ℝ (Set.range (t.faceOpposite 1).points) = line[ℝ, C, A] := by
    rw [Simplex.range_faceOpposite_points]
    have hc : ({1}ᶜ : Set (Fin 3)) = {0, 2} := by grind
    rw [hc, Set.image_insert_eq, Set.image_singleton, hp0, hp2, Set.pair_comm]
  have hAmem : A ∈ line[ℝ, C, A] := right_mem_affineSpan_pair ℝ C A
  have hCmem : C ∈ line[ℝ, C, A] := left_mem_affineSpan_pair ℝ C A
  have htanE : (t.exsphere {1}).IsTangentAt (t.touchpoint {1} 1) line[ℝ, C, A] := by
    rw [← hface]
    exact (t.excenterExists_singleton 1).isTangentAt_touchpoint 1
  have htanI : t.insphere.IsTangentAt (t.touchpoint ∅ 1) line[ℝ, C, A] := by
    rw [← hface]
    exact t.isTangentAt_insphere_touchpoint 1
  have hperpE : ⟪t.excenter {1} -ᵥ t.touchpoint {1} 1, A -ᵥ C⟫ = 0 := by
    have h := IsTangentAt.inner_vsub_center_eq_zero htanE hAmem hCmem
    rwa [Simplex.exsphere_center] at h
  have hperpI : ⟪t.touchpoint ∅ 1 -ᵥ t.incenter, A -ᵥ C⟫ = 0 := by
    have h := IsTangentAt.inner_vsub_center_eq_zero htanI hAmem hCmem
    rw [Simplex.insphere_center] at h
    rw [← neg_vsub_eq_vsub_rev, inner_neg_left, h, neg_zero]
  have hmagE : |⟪t.excenter {1} -ᵥ t.touchpoint {1} 1, rot90 (A -ᵥ C)⟫| =
      t.exradius {1} * ‖A -ᵥ C‖ := by
    have h := IsTangentAt.abs_inner_vsub_center_rot90 htanE hAmem hCmem hrB
    rwa [Simplex.exsphere_center, Simplex.exsphere_radius] at h
  have hmagI : |⟪t.touchpoint ∅ 1 -ᵥ t.incenter, rot90 (A -ᵥ C)⟫| =
      t.inradius * ‖A -ᵥ C‖ := by
    have h := IsTangentAt.abs_inner_vsub_center_rot90 htanI hAmem hCmem hr1
    rw [Simplex.insphere_center, Simplex.insphere_radius] at h
    have e : ⟪t.touchpoint ∅ 1 -ᵥ t.incenter, rot90 (A -ᵥ C)⟫ =
        -⟪t.incenter -ᵥ t.touchpoint ∅ 1, rot90 (A -ᵥ C)⟫ := by
      rw [← neg_vsub_eq_vsub_rev, inner_neg_left]
    rw [e, abs_neg]
    exact h
  have hOpp : line[ℝ, C, A].SOppSide (t.excenter {1}) B := by
    have h1 := t.sOppSide_excenter_singleton_point 1
    rwa [hface, hp1] at h1
  have hSame : line[ℝ, C, A].SSameSide t.incenter B := by
    have h1 := t.sSameSide_incenter_point 1
    rwa [hface, hp1] at h1
  have hsignOpp : planeOrientation.areaForm (t.excenter {1} -ᵥ C) (A -ᵥ C) *
      planeOrientation.areaForm (B -ᵥ C) (A -ᵥ C) < 0 :=
    sOppSide_areaForm_mul_neg hwne hOpp
  have hsignSame : 0 < planeOrientation.areaForm (t.incenter -ᵥ C) (A -ᵥ C) *
      planeOrientation.areaForm (B -ᵥ C) (A -ᵥ C) :=
    (sSameSide_iff_areaForm_mul_pos hwne).mp hSame
  have hsign : planeOrientation.areaForm (t.excenter {1} -ᵥ C) (A -ᵥ C) *
      planeOrientation.areaForm (t.incenter -ᵥ C) (A -ᵥ C) < 0 := by
    rcases mul_neg_iff.mp hsignOpp with ⟨he, hb⟩ | ⟨he, hb⟩ <;>
      rcases mul_pos_iff.mp hsignSame with ⟨ho, hb'⟩ | ⟨ho, hb'⟩
    · exact absurd hb' (not_lt.mpr hb.le)
    · exact mul_neg_of_pos_of_neg he ho
    · exact mul_neg_of_neg_of_pos he ho
    · exact absurd hb (not_lt.mpr hb'.le)
  have hT'mem : t.touchpoint {1} 1 ∈ line[ℝ, C, A] := htanE.mem_space
  have hPmem : t.touchpoint ∅ 1 ∈ line[ℝ, C, A] := htanI.mem_space
  have hzeroE : planeOrientation.areaForm (t.touchpoint {1} 1 -ᵥ C) (A -ᵥ C) = 0 := by
    have hmem : t.touchpoint {1} 1 -ᵥ C ∈ line[ℝ, C, A].direction :=
      AffineSubspace.vsub_mem_direction hT'mem hCmem
    rw [direction_affineSpan, vectorSpan_pair_rev] at hmem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    rw [← hc, map_smul, LinearMap.smul_apply, areaForm_self, smul_zero]
  have hzeroI : planeOrientation.areaForm (t.touchpoint ∅ 1 -ᵥ C) (A -ᵥ C) = 0 := by
    have hmem : t.touchpoint ∅ 1 -ᵥ C ∈ line[ℝ, C, A].direction :=
      AffineSubspace.vsub_mem_direction hPmem hCmem
    rw [direction_affineSpan, vectorSpan_pair_rev] at hmem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    rw [← hc, map_smul, LinearMap.smul_apply, areaForm_self, smul_zero]
  have hfootE : planeOrientation.areaForm (t.excenter {1} -ᵥ t.touchpoint {1} 1) (A -ᵥ C) =
      planeOrientation.areaForm (t.excenter {1} -ᵥ C) (A -ᵥ C) := by
    have e : t.excenter {1} -ᵥ t.touchpoint {1} 1 =
        (t.excenter {1} -ᵥ C) - (t.touchpoint {1} 1 -ᵥ C) :=
      (vsub_sub_vsub_cancel_right _ _ _).symm
    rw [e, map_sub, LinearMap.sub_apply, hzeroE, sub_zero]
  have hfootI : planeOrientation.areaForm (t.touchpoint ∅ 1 -ᵥ t.incenter) (A -ᵥ C) =
      -planeOrientation.areaForm (t.incenter -ᵥ C) (A -ᵥ C) := by
    have e : t.touchpoint ∅ 1 -ᵥ t.incenter =
        (t.touchpoint ∅ 1 -ᵥ C) - (t.incenter -ᵥ C) :=
      (vsub_sub_vsub_cancel_right _ _ _).symm
    rw [e, map_sub, LinearMap.sub_apply, hzeroI, zero_sub]
  have hprod : 0 < planeOrientation.areaForm (t.excenter {1} -ᵥ t.touchpoint {1} 1) (A -ᵥ C) *
      planeOrientation.areaForm (t.touchpoint ∅ 1 -ᵥ t.incenter) (A -ᵥ C) := by
    rw [hfootE, hfootI, mul_neg]
    exact neg_pos.mpr hsign
  have hprodI : 0 < ⟪t.excenter {1} -ᵥ t.touchpoint {1} 1, rot90 (A -ᵥ C)⟫ *
      ⟪t.touchpoint ∅ 1 -ᵥ t.incenter, rot90 (A -ᵥ C)⟫ := by
    rw [inner_rot90_right, inner_rot90_right, neg_mul_neg]
    exact hprod
  have hratio : ⟪t.excenter {1} -ᵥ t.touchpoint {1} 1, rot90 (A -ᵥ C)⟫ =
      (t.exradius {1} / t.inradius) * ⟪t.touchpoint ∅ 1 -ᵥ t.incenter, rot90 (A -ᵥ C)⟫ := by
    rcases eq_or_eq_neg_of_abs_eq hmagE with hae | hae <;>
      rcases eq_or_eq_neg_of_abs_eq hmagI with hbe | hbe
    · rw [hae, hbe]
      field_simp
    · exfalso
      rw [hae, hbe, mul_neg] at hprodI
      have h1 : (0 : ℝ) < (t.exradius {1} * ‖A -ᵥ C‖) * (t.inradius * ‖A -ᵥ C‖) :=
        mul_pos (mul_pos hrB hwpos) (mul_pos hr1 hwpos)
      exact absurd (neg_pos.mp hprodI) (not_lt.mpr h1.le)
    · exfalso
      rw [hae, hbe, neg_mul] at hprodI
      have h1 : (0 : ℝ) < (t.exradius {1} * ‖A -ᵥ C‖) * (t.inradius * ‖A -ᵥ C‖) :=
        mul_pos (mul_pos hrB hwpos) (mul_pos hr1 hwpos)
      exact absurd (neg_pos.mp hprodI) (not_lt.mpr h1.le)
    · rw [hae, hbe]
      field_simp
  have hdecE := eq_smul_add_smul_rightAngleRotation
    (t.excenter {1} -ᵥ t.touchpoint {1} 1) (A -ᵥ C) hwne
  rw [hperpE, zero_div, zero_smul, zero_add] at hdecE
  have hdecI := eq_smul_add_smul_rightAngleRotation
    (t.touchpoint ∅ 1 -ᵥ t.incenter) (A -ᵥ C) hwne
  rw [hperpI, zero_div, zero_smul, zero_add] at hdecI
  calc t.excenter {1} -ᵥ t.touchpoint {1} 1
      = (⟪t.excenter {1} -ᵥ t.touchpoint {1} 1, rot90 (A -ᵥ C)⟫ / ‖A -ᵥ C‖ ^ 2) •
          rot90 (A -ᵥ C) := hdecE
    _ = ((t.exradius {1} / t.inradius) *
            ⟪t.touchpoint ∅ 1 -ᵥ t.incenter, rot90 (A -ᵥ C)⟫ / ‖A -ᵥ C‖ ^ 2) •
          rot90 (A -ᵥ C) := by rw [hratio]
    _ = (t.exradius {1} / t.inradius) •
          ((⟪t.touchpoint ∅ 1 -ᵥ t.incenter, rot90 (A -ᵥ C)⟫ / ‖A -ᵥ C‖ ^ 2) •
            rot90 (A -ᵥ C)) := by rw [smul_smul, mul_div_assoc]
    _ = (t.exradius {1} / t.inradius) • (t.touchpoint ∅ 1 -ᵥ t.incenter) := by rw [← hdecI]

/-- Collinearity `B, Q, T`: the line from `B` through the antipode `Q` of
the incircle touchpoint `P` of `ABC` on `AC` passes through `T`, the
incircle touchpoint of `ADC` on `AC`. In vector form, with `O1` the
incenter of `ABC` (so that the antipode `Q` of `P` on the incircle
satisfies `Q -ᵥ B = (O1 -ᵥ P) + (O1 -ᵥ B)`):
`T -ᵥ B = (r_B/r1) • ((O1 -ᵥ P) + (O1 -ᵥ B))`. -/
lemma collinear_B_Q_T {A B C D : Pt} {ω : Sphere Pt}
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hADC : AffineIndependent ℝ ![A, D, C])
    (hconvex : ConvexQuadrilateral A B C D)
    (hR : 0 < ω.radius)
    (hωBA : ∃ T : Pt, [B, A, T].Sbtw ℝ ∧ ω.IsTangentAt T line[ℝ, B, A])
    (hωBC : ∃ T : Pt, [B, C, T].Sbtw ℝ ∧ ω.IsTangentAt T line[ℝ, B, C])
    (hωAD : ω.IsTangent line[ℝ, A, D])
    (hωCD : ω.IsTangent line[ℝ, C, D]) :
    (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 -ᵥ B =
      ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).exradius {1} /
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius) •
        (((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
          ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1)) +
          ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ B)) := by
  have hT'T := excircle_touchpoint_eq_insphere_touchpoint hABC hADC hconvex hR hωBA hωBC hωAD hωCD
  have hR2 := excenter_vsub_touchpoint_eq_smul hABC
  have hEB := excenter_vsub_B_eq_smul hABC
  have key : (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint {1} 1 -ᵥ B =
      ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).exradius {1} /
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius) •
        (((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
          ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1)) +
          ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ B)) := by
    have e1 : (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint {1} 1 -ᵥ B =
        ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).excenter {1} -ᵥ B) -
          ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).excenter {1} -ᵥ
            (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint {1} 1) :=
      (vsub_sub_vsub_cancel_left _ _ _).symm
    have hv : ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ B) -
        ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 -ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) =
        ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
          ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1)) +
          ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ B) := by
      rw [sub_eq_add_neg, neg_vsub_eq_vsub_rev]
      exact add_comm _ _
    rw [e1, hEB, hR2, ← smul_sub, hv]
  rw [← hT'T]
  exact key

/-- Collinearity `D, S, P` (the mirror of `collinear_B_Q_T`): the line
from `D` through the antipode `S` of the incircle touchpoint `T` of `ADC`
on `AC` passes through `P`, the incircle touchpoint of `ABC` on `AC`. In
vector form, with `O2` the incenter of `ADC`:
`P -ᵥ D = (r_D/r2) • ((O2 -ᵥ T) + (O2 -ᵥ D))`. -/
lemma collinear_D_S_P {A B C D : Pt} {ω : Sphere Pt}
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hADC : AffineIndependent ℝ ![A, D, C])
    (hconvex : ConvexQuadrilateral A B C D)
    (hR : 0 < ω.radius)
    (hωBA : ∃ T : Pt, [B, A, T].Sbtw ℝ ∧ ω.IsTangentAt T line[ℝ, B, A])
    (hωBC : ∃ T : Pt, [B, C, T].Sbtw ℝ ∧ ω.IsTangentAt T line[ℝ, B, C])
    (hωAD : ω.IsTangent line[ℝ, A, D])
    (hωCD : ω.IsTangent line[ℝ, C, D]) :
    (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 -ᵥ D =
      ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).exradius {1} /
        (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius) •
        (((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
          ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1)) +
          ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ D)) := by
  have hP'P := excenter_touchpoint_eq_insphere_touchpoint' hABC hADC hconvex hR hωBA hωBC hωAD hωCD
  have hR2 := excenter_vsub_touchpoint_eq_smul hADC
  have hED := excenter_vsub_B_eq_smul hADC
  have key : (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint {1} 1 -ᵥ D =
      ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).exradius {1} /
        (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius) •
        (((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
          ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1)) +
          ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ D)) := by
    have e1 : (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint {1} 1 -ᵥ D =
        ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).excenter {1} -ᵥ D) -
          ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).excenter {1} -ᵥ
            (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint {1} 1) :=
      (vsub_sub_vsub_cancel_left _ _ _).symm
    have hv : ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ D) -
        ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 -ᵥ
          (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter) =
        ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
          ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1)) +
          ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ D) := by
      rw [sub_eq_add_neg, neg_vsub_eq_vsub_rev]
      exact add_comm _ _
    rw [e1, hED, hR2, ← smul_sub, hv]
  rw [← hP'P]
  exact key

/-- The unit normal to `AC` pointing from the `B`-side towards the
`D`-side of the plane, built from the incircle of `ABC`. -/
noncomputable def unitNormal {A B C : Pt} (hABC : AffineIndependent ℝ ![A, B, C]) : V :=
  ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius)⁻¹ •
    ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 -ᵥ
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter)

omit [Fact (finrank ℝ V = 2)] in
lemma unitNormal_norm {A B C : Pt} (hABC : AffineIndependent ℝ ![A, B, C]) :
    ‖unitNormal hABC‖ = 1 := by
  have h1 : dist (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter
      ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) =
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius :=
    Simplex.dist_incenter _ 1
  have h2 : ‖(⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 -ᵥ
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter‖ =
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius := by
    rw [← h1, dist_eq_norm_vsub, ← neg_vsub_eq_vsub_rev, norm_neg]
  rw [unitNormal, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius_pos.le), h2]
  field_simp [(⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius_pos.ne']

/-- The point of `ω` at the `B`-side extreme perpendicular to `AC`: the
tangency point of the unique tangent line of `ω` parallel to `AC` on the
`B` side. -/
noncomputable def Kpoint {A B C : Pt} (hABC : AffineIndependent ℝ ![A, B, C])
    (ω : Sphere Pt) : Pt :=
  (-(ω.radius • unitNormal hABC)) +ᵥ ω.center

omit [Fact (finrank ℝ V = 2)] in
lemma Kpoint_mem_sphere {A B C : Pt} {ω : Sphere Pt} (hABC : AffineIndependent ℝ ![A, B, C])
    (hR : 0 < ω.radius) :
    Kpoint hABC ω ∈ (ω : Set Pt) := by
  show dist (Kpoint hABC ω) ω.center = ω.radius
  rw [Kpoint, dist_eq_norm_vsub, vadd_vsub, norm_neg, norm_smul, Real.norm_eq_abs,
    abs_of_pos hR, unitNormal_norm, mul_one]

/-- The homothety relation at `B` for `K`: `K -ᵥ B = (R/r1) • (Q -ᵥ B)`,
where `Q = O1 +ᵥ (O1 -ᵥ P)` is the antipode of the incircle touchpoint
`P` of `ABC` on `AC`. -/
lemma Kpoint_vsub_B {A B C T₁ T₂ : Pt} {ω : Sphere Pt}
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hR : 0 < ω.radius)
    (hsbtw₁ : [B, A, T₁].Sbtw ℝ) (htan₁ : ω.IsTangentAt T₁ line[ℝ, B, A])
    (hsbtw₂ : [B, C, T₂].Sbtw ℝ) (htan₂ : ω.IsTangentAt T₂ line[ℝ, B, C]) :
    (Kpoint hABC ω) -ᵥ B = (ω.radius / (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius) •
      (((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
        ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1)) +
        ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ B)) := by
  have hO := center_vsub_B_eq_smul hABC hR hsbtw₁ htan₁ hsbtw₂ htan₂
  have e1 : (Kpoint hABC ω) -ᵥ B =
      ((Kpoint hABC ω) -ᵥ ω.center) + (ω.center -ᵥ B) :=
    (vsub_add_vsub_cancel (Kpoint hABC ω) ω.center B).symm
  have e2 : (Kpoint hABC ω) -ᵥ ω.center = -(ω.radius • unitNormal hABC) := by
    rw [Kpoint, vadd_vsub]
  have e3 : ω.radius • unitNormal hABC =
      (ω.radius / (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius) •
        ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 -ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) := by
    rw [unitNormal, smul_smul]
    congr 1
  have hv : ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ B) -
      ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 -ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) =
      ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
        ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1)) +
        ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ B) := by
    rw [sub_eq_add_neg, neg_vsub_eq_vsub_rev]
    exact add_comm _ _
  have h5 : (ω.radius / (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius) •
      ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ B) -
      (ω.radius / (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius) •
        ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 -ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) =
      (ω.radius / (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius) •
        (((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ B) -
          ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 -ᵥ
            (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter)) :=
    (smul_sub _ _ _).symm
  rw [e1,
    show (Kpoint hABC ω -ᵥ ω.center) + (ω.center -ᵥ B) =
      (ω.radius / (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius) •
        ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ B) +
        -((ω.radius / (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius) •
          ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 -ᵥ
            (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter)) from by
      rw [e2, e3, hO]
      exact add_comm _ _, ← sub_eq_add_neg, h5, hv]

/-- The homothety relation at `D` for `K`: `K -ᵥ D = -(R/r2) • (S -ᵥ D)`,
where `S = O2 +ᵥ (O2 -ᵥ T)` is the antipode of the incircle touchpoint
`T` of `ADC` on `AC`. -/
lemma Kpoint_vsub_D {A B C D : Pt} {ω : Sphere Pt}
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hADC : AffineIndependent ℝ ![A, D, C])
    (hconvex : ConvexQuadrilateral A B C D)
    (hR : 0 < ω.radius)
    (hωBA : ∃ T : Pt, [B, A, T].Sbtw ℝ ∧ ω.IsTangentAt T line[ℝ, B, A])
    (hωBC : ∃ T : Pt, [B, C, T].Sbtw ℝ ∧ ω.IsTangentAt T line[ℝ, B, C])
    (hωAD : ω.IsTangent line[ℝ, A, D])
    (hωCD : ω.IsTangent line[ℝ, C, D]) :
    (Kpoint hABC ω) -ᵥ D = -(ω.radius / (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius) •
      (((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
        ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1)) +
        ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ D)) := by
  have hO := center_vsub_D_eq_neg_smul hABC hADC hconvex hR hωBA hωBC hωAD hωCD
  have hTn := touchpoint_vsub_incenter_neg_smul hABC hADC hconvex
  have e1 : (Kpoint hABC ω) -ᵥ D =
      ((Kpoint hABC ω) -ᵥ ω.center) + (ω.center -ᵥ D) :=
    (vsub_add_vsub_cancel (Kpoint hABC ω) ω.center D).symm
  have e2 : (Kpoint hABC ω) -ᵥ ω.center = -(ω.radius • unitNormal hABC) := by
    rw [Kpoint, vadd_vsub]
  have e4 : -(ω.radius / (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius) •
      ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 -ᵥ
        (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter) =
      (ω.radius / (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius) •
        ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 -ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) := by
    rw [hTn, smul_smul]
    have hc : -(ω.radius / (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius) *
        -((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius /
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius) =
        ω.radius / (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius := by
      field_simp [(⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius_pos.ne']
    rw [hc]
  have e3 : ω.radius • unitNormal hABC =
      -(ω.radius / (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius) •
        ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 -ᵥ
          (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter) := by
    rw [unitNormal, smul_smul, e4]
    congr 1
  have hv : ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 -ᵥ
        (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter) -
      ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ D) =
      -(((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
        ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1)) +
        ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ D)) := by
    rw [sub_eq_add_neg, neg_add, neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev]
  rw [e1, e2, e3, neg_smul, neg_neg, hO, neg_smul, ← sub_eq_add_neg, ← smul_sub, hv,
    smul_neg, ← neg_smul]

omit [Fact (finrank ℝ V = 2)] in
/-- If a nonzero vector is a scalar multiple of another vector, the two
singletons span the same submodule (the scalar is automatically nonzero). -/
lemma span_singleton_eq_span_singleton_of_smul {c : ℝ} {x y : V} (h : x = c • y)
    (hx : x ≠ 0) : Submodule.span ℝ {x} = Submodule.span ℝ {y} := by
  have hc : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at h
    exact hx h
  apply le_antisymm
  · rw [Submodule.span_singleton_le_iff_mem, h]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · rw [Submodule.span_singleton_le_iff_mem]
    have hy : y = c⁻¹ • x := by rw [h, smul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [hy]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

/-- The basic package for Step 5: tangencies of the two incircles with the
line `AC`, the inner-product identities for the shared unit normal
`n̂ = unitNormal hABC` (with `P`, `T` the incircle touchpoints and `O1`, `O2`
the incenters of `ABC`, `ADC`), the antipode decompositions
`T -ᵥ Q = (O2 -ᵥ O1) + (r1 - r2) • n̂` and `S -ᵥ P = (O2 -ᵥ O1) - (r1 - r2) • n̂`
(where `Q`, `S` are the antipodes of `P`, `T` on the two incircles), and the
nonvanishing of those two vectors. -/
lemma insphere_tangent_inner_package {A B C D : Pt}
    (hABC : AffineIndependent ℝ ![A, B, C]) (hADC : AffineIndependent ℝ ![A, D, C])
    (hconvex : ConvexQuadrilateral A B C D) :
    (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).insphere.IsTangentAt
        ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) line[ℝ, A, C] ∧
      (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).insphere.IsTangentAt
        ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) line[ℝ, A, C] ∧
      ⟪unitNormal hABC, unitNormal hABC⟫ = 1 ∧
      ⟪A -ᵥ C, unitNormal hABC⟫ = 0 ∧
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 -ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter =
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius • unitNormal hABC ∧
      (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 -ᵥ
          (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter =
        -((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius • unitNormal hABC) ∧
      ⟪(⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter, unitNormal hABC⟫ =
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius +
          (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius ∧
      (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 -ᵥ
          (((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
            (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
            (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) =
        ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) +
        ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius -
          (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius) • unitNormal hABC ∧
      (((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
          (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
          (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter) -ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 =
        ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) -
        ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius -
          (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius) • unitNormal hABC ∧
      (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 -ᵥ
          (((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
            (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
            (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) ≠ 0 ∧
      (((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
          (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
          (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter) -ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 ≠ 0 := by
  have hr1 := (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius_pos
  have hr2 := (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius_pos
  -- tangencies of both inspheres with line AC
  have hface1 : affineSpan ℝ (Set.range ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).faceOpposite 1).points)
      = line[ℝ, A, C] := by
    have hp0 : (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).points 0 = A := rfl
    have hp2 : (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).points 2 = C := rfl
    rw [Simplex.range_faceOpposite_points]
    have hc : ({1}ᶜ : Set (Fin 3)) = {0, 2} := by grind
    rw [hc, Set.image_insert_eq, Set.image_singleton, hp0, hp2]
  have hface2 : affineSpan ℝ (Set.range ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).faceOpposite 1).points)
      = line[ℝ, A, C] := by
    have hp0 : (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).points 0 = A := rfl
    have hp2 : (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).points 2 = C := rfl
    rw [Simplex.range_faceOpposite_points]
    have hc : ({1}ᶜ : Set (Fin 3)) = {0, 2} := by grind
    rw [hc, Set.image_insert_eq, Set.image_singleton, hp0, hp2]
  have htan1 : (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).insphere.IsTangentAt
      ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) line[ℝ, A, C] := by
    rw [← hface1]
    exact (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).isTangentAt_insphere_touchpoint 1
  have htan2 : (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).insphere.IsTangentAt
      ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) line[ℝ, A, C] := by
    rw [← hface2]
    exact (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).isTangentAt_insphere_touchpoint 1
  -- the unit normal
  have hnn : ⟪unitNormal hABC, unitNormal hABC⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, unitNormal_norm, one_pow]
  have hperp1 : ⟪(⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 -ᵥ
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter, A -ᵥ C⟫ = 0 := by
    have h := IsTangentAt.inner_vsub_center_eq_zero htan1
      (left_mem_affineSpan_pair ℝ A C) (right_mem_affineSpan_pair ℝ A C)
    rw [show (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 -ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter =
        -((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).insphere.center -ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) from
      (neg_vsub_eq_vsub_rev _ _).symm, inner_neg_left, h, neg_zero]
  have hperp : ⟪A -ᵥ C, unitNormal hABC⟫ = 0 := by
    rw [unitNormal, real_inner_smul_right, real_inner_comm _ (A -ᵥ C), hperp1, mul_zero]
  have hPO1 : (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 -ᵥ
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter =
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius • unitNormal hABC := by
    rw [unitNormal, smul_smul, mul_inv_cancel₀ hr1.ne', one_smul]
  have hTO2 : (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 -ᵥ
      (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter =
      -((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius • unitNormal hABC) := by
    have hTn := touchpoint_vsub_incenter_neg_smul hABC hADC hconvex
    have hc : -((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius /
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius) *
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius =
        -(⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius := by
      rw [neg_div', div_mul_cancel₀ _ hr1.ne']
    rw [hTn, hPO1, smul_smul, hc, neg_smul]
  have hO2T'v : (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
      (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 =
      (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius • unitNormal hABC := by
    have e : (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
        (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 =
        -((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 -ᵥ
          (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter) :=
      (neg_vsub_eq_vsub_rev _ _).symm
    rw [e, hTO2, neg_neg]
  -- the incenter offset along the normal
  have hsplit : ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
      (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +
      ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 -ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +
      ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 -ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) =
      (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter := by
    rw [vsub_add_vsub_cancel, vsub_add_vsub_cancel]
  have hT'P : ⟪(⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 -ᵥ
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1, unitNormal hABC⟫ = 0 := by
    have hmem : (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 -ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 ∈ line[ℝ, A, C].direction :=
      AffineSubspace.vsub_mem_direction htan2.mem_space htan1.mem_space
    rw [direction_affineSpan, mem_vectorSpan_pair] at hmem
    obtain ⟨c, hc⟩ := hmem
    rw [← hc, real_inner_smul_left, hperp, mul_zero]
  have hO2T'i : ⟪(⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
      (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1, unitNormal hABC⟫ =
      (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius := by
    rw [hO2T'v, real_inner_smul_left, hnn, mul_one]
  have hPO1i : ⟪(⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 -ᵥ
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter, unitNormal hABC⟫ =
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius := by
    rw [hPO1, real_inner_smul_left, hnn, mul_one]
  have hm_inner : ⟪(⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter, unitNormal hABC⟫ =
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius +
        (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius := by
    rw [← hsplit, inner_add_left, inner_add_left, hO2T'i, hT'P, hPO1i, add_zero]
    exact add_comm _ _
  -- antipode bookkeeping
  have hQO1 : (((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) -ᵥ
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter =
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 :=
    vadd_vsub _ _
  have hO1Q : (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
      (((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) =
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 -ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter := by
    rw [vsub_vadd_eq_vsub_sub, vsub_self, zero_sub, neg_vsub_eq_vsub_rev]
  have hSO2 : (((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
      (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
      (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter) -ᵥ
      (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter =
      (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
        (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 :=
    vadd_vsub _ _
  have hO1P : (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 =
      -((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius • unitNormal hABC) := by
    rw [← hPO1]
    exact (neg_vsub_eq_vsub_rev _ _).symm
  have hT'Qsplit : (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 -ᵥ
      (((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) =
      ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 -ᵥ
        (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter) +
      (((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) +
      ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
        (((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter))) := by
    have e1 : (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 -ᵥ
        (((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) =
        ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 -ᵥ
          (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter) +
        ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
          (((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
            (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
            (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter)) :=
      (vsub_add_vsub_cancel _ _ _).symm
    have e2 : (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
        (((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) =
        ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) +
        ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
          (((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
            (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
            (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter)) :=
      (vsub_add_vsub_cancel _ _ _).symm
    rw [e1, e2]
  have hSPsplit : (((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
      (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
      (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter) -ᵥ
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 =
      ((((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
        (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
        (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter) -ᵥ
        (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter) +
      (((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) +
      ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1)) := by
    have e1 : (((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
        (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
        (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter) -ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 =
        ((((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
          (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
          (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter) -ᵥ
          (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter) +
        ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) :=
      (vsub_add_vsub_cancel _ _ _).symm
    have e2 : (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 =
        ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) +
        ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) :=
      (vsub_add_vsub_cancel _ _ _).symm
    rw [e1, e2]
  have hT'Qv : (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 -ᵥ
      (((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) =
      ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) +
      ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius -
        (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius) • unitNormal hABC := by
    rw [hT'Qsplit, hO1Q, hPO1, hTO2]
    module
  have hSPv : (((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
      (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
      (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter) -ᵥ
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 =
      ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) -
      ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius -
        (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius) • unitNormal hABC := by
    rw [hSPsplit, hSO2, hO2T'v, hO1P]
    module
  -- nonvanishing of the two antipode vectors
  have hTO2i : ⟪(⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 -ᵥ
      (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter, unitNormal hABC⟫ =
      -(⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius := by
    rw [hTO2, inner_neg_left, real_inner_smul_left, hnn, mul_one]
  have hO1Qi : ⟪(⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
      (((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter), unitNormal hABC⟫ =
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius := by
    rw [hO1Q, hPO1, real_inner_smul_left, hnn, mul_one]
  have hSO2i : ⟪(((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
      (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
      (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter) -ᵥ
      (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter, unitNormal hABC⟫ =
      (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius := by
    rw [hSO2, hO2T'v, real_inner_smul_left, hnn, mul_one]
  have hO1Pi : ⟪(⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1, unitNormal hABC⟫ =
      -(⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius := by
    rw [hO1P, inner_neg_left, real_inner_smul_left, hnn, mul_one]
  have hT'Qinner : ⟪(⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 -ᵥ
      (((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter), unitNormal hABC⟫ =
      2 * (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius := by
    rw [hT'Qsplit, inner_add_left, inner_add_left, hTO2i, hm_inner, hO1Qi]
    ring
  have hSPinner : ⟪(((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
      (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
      (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter) -ᵥ
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1, unitNormal hABC⟫ =
      2 * (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius := by
    rw [hSPsplit, inner_add_left, inner_add_left, hSO2i, hm_inner, hO1Pi]
    ring
  have hT'Qne : (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 -ᵥ
      (((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) ≠ 0 := by
    intro h
    rw [h, inner_zero_left] at hT'Qinner
    exact (mul_ne_zero two_ne_zero hr1.ne') hT'Qinner.symm
  have hSPne : (((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
      (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
      (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter) -ᵥ
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 ≠ 0 := by
    intro h
    rw [h, inner_zero_left] at hSPinner
    exact (mul_ne_zero two_ne_zero hr2.ne') hSPinner.symm
  exact ⟨htan1, htan2, hnn, hperp, hPO1, hTO2, hm_inner, hT'Qv, hSPv, hT'Qne, hSPne⟩

/-- The antipode `Q` of the incircle touchpoint `P` of `ABC` on `AC` does not
lie on the line `AC` (its normal offset from `P` is `-2 • (P -ᵥ O1)`). -/
lemma antipode_not_mem_line {A B C D : Pt}
    (hABC : AffineIndependent ℝ ![A, B, C]) (hADC : AffineIndependent ℝ ![A, D, C])
    (hconvex : ConvexQuadrilateral A B C D) :
    (((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) ∉ line[ℝ, A, C] := by
  obtain ⟨htan1, htan2, hnn, hperp, hPO1, hTO2, hm_inner, hT'Qv, hSPv, hT'Qne, hSPne⟩ :=
    insphere_tangent_inner_package hABC hADC hconvex
  have hr1 := (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius_pos
  intro hQ
  have hP_AC : (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 ∈ line[ℝ, A, C] :=
    htan1.mem_space
  have hQPmem : (((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) -ᵥ
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 ∈ (line[ℝ, A, C]).direction :=
    AffineSubspace.vsub_mem_direction hQ hP_AC
  rw [direction_affineSpan, vectorSpan_pair] at hQPmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hQPmem
  have hinner0 : ⟪(((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) -ᵥ
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1, unitNormal hABC⟫ = 0 := by
    rw [← hc, real_inner_smul_left, hperp, mul_zero]
  have hQO1 : (((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) -ᵥ
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter =
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 :=
    vadd_vsub _ _
  have hQP : (((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) -ᵥ
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 =
      (2 : ℝ) • ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) := by
    have e1 : (((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) -ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 =
        ((((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) -ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) +
        ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) :=
      (vsub_add_vsub_cancel _ _ _).symm
    rw [e1, hQO1, two_smul]
  have hO1Pv : (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 =
      -((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius • unitNormal hABC) := by
    rw [← hPO1]
    exact (neg_vsub_eq_vsub_rev _ _).symm
  have hinner : ⟪(((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) -ᵥ
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1, unitNormal hABC⟫ =
      -(2 * (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius) := by
    rw [hQP, real_inner_smul_left, hO1Pv, inner_neg_left, real_inner_smul_left, hnn, mul_one]
    ring
  rw [hinner] at hinner0
  exact (neg_ne_zero.mpr (mul_ne_zero two_ne_zero hr1.ne')) hinner0

/-- The two incircle touchpoints on `AC` are distinct: `T ≠ P`. (If they
coincided, `2 • dist A P = dist A C`, forcing `dist A B = dist B C`.) -/
lemma insphere_touchpoint_ne {A B C D : Pt} {ω : Sphere Pt}
    (hABC : AffineIndependent ℝ ![A, B, C]) (hADC : AffineIndependent ℝ ![A, D, C])
    (hconvex : ConvexQuadrilateral A B C D) (hBA_ne_BC : dist B A ≠ dist B C)
    (hR : 0 < ω.radius)
    (hωBA : ∃ T : Pt, [B, A, T].Sbtw ℝ ∧ ω.IsTangentAt T line[ℝ, B, A])
    (hωBC : ∃ T : Pt, [B, C, T].Sbtw ℝ ∧ ω.IsTangentAt T line[ℝ, B, C])
    (hωAD : ω.IsTangent line[ℝ, A, D]) (hωCD : ω.IsTangent line[ℝ, C, D]) :
    (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 ≠
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 := by
  intro hTP
  have hdist := (wbtw_touchpoint_insphere hADC).dist_add_dist
  have hAP_CT := dist_touchpoint_eq hABC hADC hconvex hR hωBA hωBC hωAD hωCD
  have hleft := dist_touchpoint_insphere_left hABC
  rw [hTP] at hdist
  have h1 : dist ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) C =
      dist A ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) := by
    rw [dist_comm ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) C,
      congrArg (dist C) hTP.symm, ← hAP_CT]
  have h2 : dist A B = dist B C := by linarith
  have h3 : dist B A = dist B C := by
    rw [dist_comm B A]
    exact h2
  exact hBA_ne_BC h3

/-- `K` lies on the line through the antipode `Q` of `P` and the touchpoint
`T`: both `K -ᵥ B` and `T -ᵥ B` are scalar multiples of `Q -ᵥ B`. -/
lemma Kpoint_mem_line_antipode_touchpoint {A B C D : Pt} {ω : Sphere Pt}
    (hABC : AffineIndependent ℝ ![A, B, C]) (hADC : AffineIndependent ℝ ![A, D, C])
    (hconvex : ConvexQuadrilateral A B C D) (hR : 0 < ω.radius)
    (hωBA : ∃ T : Pt, [B, A, T].Sbtw ℝ ∧ ω.IsTangentAt T line[ℝ, B, A])
    (hωBC : ∃ T : Pt, [B, C, T].Sbtw ℝ ∧ ω.IsTangentAt T line[ℝ, B, C])
    (hωAD : ω.IsTangent line[ℝ, A, D]) (hωCD : ω.IsTangent line[ℝ, C, D]) :
    Kpoint hABC ω ∈ line[ℝ,
      (((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter),
      (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1] := by
  obtain ⟨htan1, htan2, hnn, hperp, hPO1, hTO2, hm_inner, hT'Qv, hSPv, hT'Qne, hSPne⟩ :=
    insphere_tangent_inner_package hABC hADC hconvex
  have hT'B := collinear_B_Q_T hABC hADC hconvex hR hωBA hωBC hωAD hωCD
  obtain ⟨T₁, hsbtw₁, htan₁⟩ := hωBA
  obtain ⟨T₂, hsbtw₂, htan₂⟩ := hωBC
  have hKB := Kpoint_vsub_B hABC hR hsbtw₁ htan₁ hsbtw₂ htan₂
  have hQB : (((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) -ᵥ B =
      ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +
      ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ B) :=
    vadd_vsub_assoc _ _ _
  rw [← hQB] at hKB hT'B
  have hT'Q : (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 -ᵥ
      (((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) =
      (((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).exradius {1} /
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius) - 1) •
        ((((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) -ᵥ B) := by
    have e1 : (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 -ᵥ
        (((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) =
        ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 -ᵥ B) -
        ((((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) -ᵥ B) :=
      (vsub_sub_vsub_cancel_right _ _ _).symm
    rw [e1, hT'B, sub_smul, one_smul]
  have hspan : Submodule.span ℝ {(⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 -ᵥ
      (((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter)} =
      Submodule.span ℝ {(((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) -ᵥ B} :=
    span_singleton_eq_span_singleton_of_smul hT'Q hT'Qne
  have hKQ : (Kpoint hABC ω) -ᵥ
      (((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) =
      ((ω.radius / (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius) - 1) •
        ((((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) -ᵥ B) := by
    have e1 : (Kpoint hABC ω) -ᵥ
        (((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) =
        ((Kpoint hABC ω) -ᵥ B) -
        ((((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) -ᵥ B) :=
      (vsub_sub_vsub_cancel_right _ _ _).symm
    rw [e1, hKB, sub_smul, one_smul]
  have hKQmem : (Kpoint hABC ω) -ᵥ
      (((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) ∈
      Submodule.span ℝ {(⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 -ᵥ
        (((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter)} := by
    rw [hKQ, hspan]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have hdir : (line[ℝ,
      (((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter),
      (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1]).direction =
      Submodule.span ℝ {(⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 -ᵥ
        (((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter)} := by
    rw [direction_affineSpan, vectorSpan_pair_rev]
  have hKQmem' : (Kpoint hABC ω) -ᵥ
      (((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) ∈
      (line[ℝ,
        (((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter),
        (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1]).direction := by
    rw [hdir]
    exact hKQmem
  rw [show Kpoint hABC ω = ((Kpoint hABC ω) -ᵥ
      (((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter)) +ᵥ
      (((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) from (vsub_vadd _ _).symm]
  exact AffineSubspace.vadd_mem_of_mem_direction hKQmem'
    (left_mem_affineSpan_pair ℝ
      (((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter)
      ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1))

/-- `K` lies on the line through the touchpoint `P` and the antipode `S` of
`T`: both `K -ᵥ D` and `P -ᵥ D` are scalar multiples of `S -ᵥ D`. -/
lemma Kpoint_mem_line_touchpoint_antipode {A B C D : Pt} {ω : Sphere Pt}
    (hABC : AffineIndependent ℝ ![A, B, C]) (hADC : AffineIndependent ℝ ![A, D, C])
    (hconvex : ConvexQuadrilateral A B C D) (hR : 0 < ω.radius)
    (hωBA : ∃ T : Pt, [B, A, T].Sbtw ℝ ∧ ω.IsTangentAt T line[ℝ, B, A])
    (hωBC : ∃ T : Pt, [B, C, T].Sbtw ℝ ∧ ω.IsTangentAt T line[ℝ, B, C])
    (hωAD : ω.IsTangent line[ℝ, A, D]) (hωCD : ω.IsTangent line[ℝ, C, D]) :
    Kpoint hABC ω ∈ line[ℝ,
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1,
      (((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
        (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
        (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter)] := by
  obtain ⟨htan1, htan2, hnn, hperp, hPO1, hTO2, hm_inner, hT'Qv, hSPv, hT'Qne, hSPne⟩ :=
    insphere_tangent_inner_package hABC hADC hconvex
  have hKD := Kpoint_vsub_D hABC hADC hconvex hR hωBA hωBC hωAD hωCD
  have hSD : (((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
      (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
      (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter) -ᵥ D =
      ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
        (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +
      ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ D) :=
    vadd_vsub_assoc _ _ _
  rw [← hSD] at hKD
  have hPD := collinear_D_S_P hABC hADC hconvex hR hωBA hωBC hωAD hωCD
  rw [← hSD] at hPD
  have hSP : (((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
      (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
      (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter) -ᵥ
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 =
      (1 - (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).exradius {1} /
        (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius) •
        ((((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
          (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
          (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter) -ᵥ D) := by
    have e1 : (((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
        (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
        (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter) -ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 =
        ((((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
          (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
          (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter) -ᵥ D) -
        ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 -ᵥ D) :=
      (vsub_sub_vsub_cancel_right _ _ _).symm
    rw [e1, hPD, sub_smul, one_smul]
  have hspan : Submodule.span ℝ {(((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
      (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
      (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter) -ᵥ
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1} =
      Submodule.span ℝ {(((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
        (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
        (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter) -ᵥ D} :=
    span_singleton_eq_span_singleton_of_smul hSP hSPne
  have hKP : (Kpoint hABC ω) -ᵥ (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 =
      (-(ω.radius / (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius) -
        (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).exradius {1} /
          (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius) •
        ((((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
          (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
          (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter) -ᵥ D) := by
    have e1 : (Kpoint hABC ω) -ᵥ (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 =
        ((Kpoint hABC ω) -ᵥ D) -
        ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 -ᵥ D) :=
      (vsub_sub_vsub_cancel_right _ _ _).symm
    rw [e1, hKD, hPD, sub_smul]
  have hKPmem : (Kpoint hABC ω) -ᵥ (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 ∈
      Submodule.span ℝ {(((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
        (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
        (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter) -ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1} := by
    rw [hKP, hspan]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have hdir : (line[ℝ,
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1,
      (((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
        (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
        (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter)]).direction =
      Submodule.span ℝ {(((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
        (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
        (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter) -ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1} := by
    rw [direction_affineSpan, vectorSpan_pair_rev]
  have hKPmem' : (Kpoint hABC ω) -ᵥ (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 ∈
      (line[ℝ,
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1,
        (((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
          (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
          (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter)]).direction := by
    rw [hdir]
    exact hKPmem
  rw [show Kpoint hABC ω = ((Kpoint hABC ω) -ᵥ
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 from (vsub_vadd _ _).symm]
  exact AffineSubspace.vadd_mem_of_mem_direction hKPmem'
    (left_mem_affineSpan_pair ℝ
      ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1)
      (((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
        (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
        (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter))

/-- The two antipode lines are distinct: `line[ℝ, Q, T] ≠ line[ℝ, P, S]`.
(Otherwise `Q` would lie on the line `AC`, since `T ≠ P` forces
`line[ℝ, Q, T] = line[ℝ, T, P] = line[ℝ, A, C]`.) -/
lemma antipode_lines_ne {A B C D : Pt} {ω : Sphere Pt}
    (hABC : AffineIndependent ℝ ![A, B, C]) (hADC : AffineIndependent ℝ ![A, D, C])
    (hconvex : ConvexQuadrilateral A B C D) (hBA_ne_BC : dist B A ≠ dist B C)
    (hR : 0 < ω.radius)
    (hωBA : ∃ T : Pt, [B, A, T].Sbtw ℝ ∧ ω.IsTangentAt T line[ℝ, B, A])
    (hωBC : ∃ T : Pt, [B, C, T].Sbtw ℝ ∧ ω.IsTangentAt T line[ℝ, B, C])
    (hωAD : ω.IsTangent line[ℝ, A, D]) (hωCD : ω.IsTangent line[ℝ, C, D]) :
    line[ℝ,
      (((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter),
      (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1] ≠
    line[ℝ,
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1,
      (((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
        (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
        (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter)] := by
  intro hlines
  obtain ⟨htan1, htan2, hnn, hperp, hPO1, hTO2, hm_inner, hT'Qv, hSPv, hT'Qne, hSPne⟩ :=
    insphere_tangent_inner_package hABC hADC hconvex
  have hT'neP := insphere_touchpoint_ne hABC hADC hconvex hBA_ne_BC hR hωBA hωBC hωAD hωCD
  have hB := antipode_not_mem_line hABC hADC hconvex
  have hP_QT : (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 ∈ line[ℝ,
      (((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter),
      (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1] := by
    rw [hlines]
    exact left_mem_affineSpan_pair ℝ
      ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1)
      (((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
        (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
        (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter)
  have hT'_QT : (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 ∈ line[ℝ,
      (((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter),
      (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1] :=
    right_mem_affineSpan_pair ℝ _ _
  have hP_AC : (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 ∈ line[ℝ, A, C] :=
    htan1.mem_space
  have hT'_AC : (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 ∈ line[ℝ, A, C] :=
    htan2.mem_space
  have hPTne : (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 -ᵥ
      (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 ≠ 0 :=
    vsub_ne_zero.mpr hT'neP.symm
  have hdir1 : (line[ℝ,
      (((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter),
      (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1]).direction =
      Submodule.span ℝ {(⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 -ᵥ
        (((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter)} := by
    rw [direction_affineSpan, vectorSpan_pair_rev]
  have hdir2 : (line[ℝ, A, C]).direction = Submodule.span ℝ {A -ᵥ C} := by
    rw [direction_affineSpan, vectorSpan_pair]
  have hPTmem1 : (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 -ᵥ
      (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 ∈
      Submodule.span ℝ {(⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 -ᵥ
        (((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter)} := by
    rw [← hdir1]
    exact AffineSubspace.vsub_mem_direction hP_QT hT'_QT
  have hPTmem2 : (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 -ᵥ
      (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 ∈
      Submodule.span ℝ {A -ᵥ C} := by
    rw [← hdir2]
    exact AffineSubspace.vsub_mem_direction hP_AC hT'_AC
  obtain ⟨c₁, hc₁⟩ := Submodule.mem_span_singleton.mp hPTmem1
  obtain ⟨c₂, hc₂⟩ := Submodule.mem_span_singleton.mp hPTmem2
  have hspan1 := span_singleton_eq_span_singleton_of_smul hc₁.symm hPTne
  have hspan2 := span_singleton_eq_span_singleton_of_smul hc₂.symm hPTne
  have hdir : (line[ℝ,
      (((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter),
      (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1]).direction =
      (line[ℝ, A, C]).direction := by
    rw [hdir1, hdir2, ← hspan1, ← hspan2]
  have hline : line[ℝ,
      (((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter),
      (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1] = line[ℝ, A, C] :=
    AffineSubspace.ext_of_direction_eq hdir
      ⟨(⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1, hT'_QT, hT'_AC⟩
  have hQ_AC : (((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) ∈ line[ℝ, A, C] := by
    have h := left_mem_affineSpan_pair ℝ
      (((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter)
      ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1)
    rw [hline] at h
    exact h
  exact hB hQ_AC

/-- Step 5: `K` is the exsimilicenter of the two incircles. The two inradii
differ, `K` divides the incenters externally in the ratio of the radii
(`K -ᵥ O2 = (r2 / r1) • (K -ᵥ O1)`), and `K` lies outside the incircle of
`ABC` (`r1 < dist K O1`). -/
lemma Kpoint_exsimilicenter_spec {A B C D : Pt} {ω : Sphere Pt}
    (hABC : AffineIndependent ℝ ![A, B, C]) (hADC : AffineIndependent ℝ ![A, D, C])
    (hconvex : ConvexQuadrilateral A B C D) (hBA_ne_BC : dist B A ≠ dist B C)
    (hR : 0 < ω.radius)
    (hωBA : ∃ T : Pt, [B, A, T].Sbtw ℝ ∧ ω.IsTangentAt T line[ℝ, B, A])
    (hωBC : ∃ T : Pt, [B, C, T].Sbtw ℝ ∧ ω.IsTangentAt T line[ℝ, B, C])
    (hωAD : ω.IsTangent line[ℝ, A, D]) (hωCD : ω.IsTangent line[ℝ, C, D]) :
    (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius ≠
        (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius ∧
      (Kpoint hABC ω) -ᵥ (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter =
        ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius /
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius) •
          ((Kpoint hABC ω) -ᵥ (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) ∧
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius <
        dist (Kpoint hABC ω) (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter := by
  obtain ⟨htan1, htan2, hnn, hperp, hPO1, hTO2, hm_inner, hT'Qv, hSPv, hT'Qne, hSPne⟩ :=
    insphere_tangent_inner_package hABC hADC hconvex
  have hr1 := (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius_pos
  have hr2 := (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius_pos
  have hK_QT := Kpoint_mem_line_antipode_touchpoint hABC hADC hconvex hR hωBA hωBC hωAD hωCD
  have hK_PS := Kpoint_mem_line_touchpoint_antipode hABC hADC hconvex hR hωBA hωBC hωAD hωCD
  have hlines := antipode_lines_ne hABC hADC hconvex hBA_ne_BC hR hωBA hωBC hωAD hωCD
  have hdirQT : (line[ℝ,
      (((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter),
      (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1]).direction =
      Submodule.span ℝ {(⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 -ᵥ
        (((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter)} := by
    rw [direction_affineSpan, vectorSpan_pair_rev]
  have hdirPS : (line[ℝ,
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1,
      (((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
        (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
        (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter)]).direction =
      Submodule.span ℝ {(((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
        (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
        (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter) -ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1} := by
    rw [direction_affineSpan, vectorSpan_pair_rev]
  -- the two inradii differ
  have hr_ne : (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius ≠
      (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius := by
    intro hr
    have hT'Qm : (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 -ᵥ
        (((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) =
        (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter := by
      rw [hT'Qv, hr, sub_self, zero_smul, add_zero]
    have hSPm : (((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
        (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
        (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter) -ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 =
        (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter := by
      rw [hSPv, hr, sub_self, zero_smul, sub_zero]
    have hspanQ : Submodule.span ℝ {(⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 -ᵥ
        (((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter)} =
        Submodule.span ℝ {(⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter} := by
      rw [hT'Qm]
    have hspanP : Submodule.span ℝ {(((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
        (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
        (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter) -ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1} =
        Submodule.span ℝ {(⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter} := by
      rw [hSPm]
    have hdireq : (line[ℝ,
        (((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter),
        (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1]).direction =
        (line[ℝ,
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1,
          (((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
            (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
            (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter)]).direction := by
      rw [hdirQT, hdirPS, hspanQ, hspanP]
    have hlineeq := AffineSubspace.ext_of_direction_eq hdireq
      ⟨Kpoint hABC ω, hK_QT, hK_PS⟩
    exact hlines hlineeq
  have hsub : (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius -
      (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius ≠ 0 := sub_ne_zero.mpr hr_ne
  -- the exsimilicenter lies on both lines
  have hO1Q : (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
      (((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) =
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 -ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter := by
    rw [vsub_vadd_eq_vsub_sub, vsub_self, zero_sub, neg_vsub_eq_vsub_rev]
  have hO1P : (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 =
      -((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius • unitNormal hABC) := by
    rw [← hPO1]
    exact (neg_vsub_eq_vsub_rev _ _).symm
  have hEO1 : ((((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius /
      ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius -
        (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius)) •
      ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter)) +ᵥ
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) -ᵥ
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter =
      ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius /
        ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius -
          (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius)) •
        ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) :=
    vadd_vsub _ _
  have hEQ : ((((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius /
      ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius -
        (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius)) •
      ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter)) +ᵥ
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) -ᵥ
      (((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) =
      ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius /
        ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius -
          (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius)) •
        ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 -ᵥ
          (((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
            (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
            (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter)) := by
    have e1 : ((((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius /
        ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius -
          (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius)) •
        ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter)) +ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) -ᵥ
        (((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) =
        (((((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius /
          ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius -
            (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius)) •
          ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
            (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter)) +ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) -ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) +
        ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
          (((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
            (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
            (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter)) :=
      (vsub_add_vsub_cancel _ _ _).symm
    rw [e1, hEO1, hO1Q, hPO1, hT'Qv, smul_add, smul_smul,
      div_mul_cancel₀ _ hsub]
  have hE_QT : (((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius /
      ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius -
        (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius)) •
      ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter)) +ᵥ
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter ∈ line[ℝ,
      (((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter),
      (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1] := by
    have hmem : ((((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius /
        ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius -
          (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius)) •
        ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter)) +ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) -ᵥ
        (((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) ∈
        (line[ℝ,
          (((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
            (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
            (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter),
          (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1]).direction := by
      rw [hEQ]
      exact Submodule.smul_mem _ _ (AffineSubspace.vsub_mem_direction
        (right_mem_affineSpan_pair ℝ _ _) (left_mem_affineSpan_pair ℝ _ _))
    have hK := AffineSubspace.vadd_mem_of_mem_direction hmem (left_mem_affineSpan_pair ℝ _ _)
    rwa [vsub_vadd] at hK
  have hEP : ((((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius /
      ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius -
        (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius)) •
      ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter)) +ᵥ
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) -ᵥ
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 =
      ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius /
        ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius -
          (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius)) •
        ((((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
          (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
          (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter) -ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) := by
    have e1 : ((((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius /
        ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius -
          (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius)) •
        ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter)) +ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) -ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 =
        (((((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius /
          ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius -
            (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius)) •
          ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
            (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter)) +ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) -ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) +
        ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) :=
      (vsub_add_vsub_cancel _ _ _).symm
    have hRHS : ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius /
        ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius -
          (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius)) •
        ((((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
          (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
          (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter) -ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) =
        ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius /
          ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius -
            (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius)) •
          ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
            (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) +
        -((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius • unitNormal hABC) := by
      rw [hSPv, smul_sub, smul_smul, div_mul_cancel₀ _ hsub]
      exact sub_eq_add_neg _ _
    rw [e1, hEO1, hO1P, hRHS]
  have hE_PS : (((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius /
      ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius -
        (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius)) •
      ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter)) +ᵥ
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter ∈ line[ℝ,
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1,
      (((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
        (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
        (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter)] := by
    have hmem : ((((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius /
        ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius -
          (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius)) •
        ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter)) +ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) -ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1 ∈
        (line[ℝ,
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1,
          (((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
            (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
            (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter)]).direction := by
      rw [hEP]
      exact Submodule.smul_mem _ _ (AffineSubspace.vsub_mem_direction
        (right_mem_affineSpan_pair ℝ _ _) (left_mem_affineSpan_pair ℝ _ _))
    have hK := AffineSubspace.vadd_mem_of_mem_direction hmem (left_mem_affineSpan_pair ℝ _ _)
    rwa [vsub_vadd] at hK
  -- the two lines meet only at `K`, so `K` is the exsimilicenter
  have hKEq : Kpoint hABC ω = (((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius /
      ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius -
        (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius)) •
      ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter)) +ᵥ
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter := by
    by_contra hne
    have hKEne : (Kpoint hABC ω) -ᵥ ((((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius /
        ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius -
          (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius)) •
        ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter)) +ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) ≠ 0 := vsub_ne_zero.mpr hne
    have hKEmem1 : (Kpoint hABC ω) -ᵥ ((((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius /
        ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius -
          (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius)) •
        ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter)) +ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) ∈
        (line[ℝ,
          (((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
            (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
            (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter),
          (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1]).direction :=
      AffineSubspace.vsub_mem_direction hK_QT hE_QT
    have hKEmem2 : (Kpoint hABC ω) -ᵥ ((((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius /
        ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius -
          (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius)) •
        ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter)) +ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) ∈
        (line[ℝ,
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1,
          (((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
            (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
            (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter)]).direction :=
      AffineSubspace.vsub_mem_direction hK_PS hE_PS
    rw [hdirQT] at hKEmem1
    rw [hdirPS] at hKEmem2
    obtain ⟨d₁, hd₁⟩ := Submodule.mem_span_singleton.mp hKEmem1
    obtain ⟨d₂, hd₂⟩ := Submodule.mem_span_singleton.mp hKEmem2
    have hsp1 := span_singleton_eq_span_singleton_of_smul hd₁.symm hKEne
    have hsp2 := span_singleton_eq_span_singleton_of_smul hd₂.symm hKEne
    have hdireq : (line[ℝ,
        (((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter -ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter),
        (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1]).direction =
        (line[ℝ,
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).touchpoint ∅ 1,
          (((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
            (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).touchpoint ∅ 1) +ᵥ
            (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter)]).direction := by
      rw [hdirQT, hdirPS, ← hsp1, ← hsp2]
    have hlineeq := AffineSubspace.ext_of_direction_eq hdireq
      ⟨Kpoint hABC ω, hK_QT, hK_PS⟩
    exact hlines hlineeq
  -- the homothety and distance relations
  have hKO1 : (Kpoint hABC ω) -ᵥ (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter =
      ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius /
        ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius -
          (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius)) •
        ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) := by
    rw [hKEq]
    exact vadd_vsub _ _
  have hKO2 : (Kpoint hABC ω) -ᵥ (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter =
      ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius /
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius) •
        ((Kpoint hABC ω) -ᵥ (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) := by
    have h1 : (Kpoint hABC ω) -ᵥ (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter =
        (((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius /
          ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius -
            (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius)) - 1) •
          ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
            (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) := by
      have e1 : (Kpoint hABC ω) -ᵥ (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter =
          ((Kpoint hABC ω) -ᵥ (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) -
          ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
            (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter) :=
        (vsub_sub_vsub_cancel_right _ _ _).symm
      rw [e1, hKO1, sub_smul, one_smul]
    have hcoef : (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius /
        ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius -
          (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius) - 1 =
        ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius /
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius) *
        ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius /
          ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius -
            (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius)) := by
      have e2 : (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius /
          ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius -
            (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius) - 1 =
          (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius /
            ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius -
              (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius) := by
        rw [sub_eq_iff_eq_add, div_add_one hsub, ← add_sub_assoc, add_sub_cancel_left]
      have e3 : ((⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius /
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius) *
          ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius /
            ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius -
              (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius)) =
          (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius /
            ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius -
              (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius) := by
        rw [div_mul_div_comm, mul_comm (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius _,
          mul_div_mul_left _ _ hr1.ne']
      rw [e2, e3]
    rw [h1, hKO1, smul_smul, ← hcoef]
  have hdist : dist (Kpoint hABC ω) (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter =
      ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius /
        |(⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius -
          (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius|) *
        ‖(⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter‖ := by
    rw [dist_eq_norm_vsub, hKO1, norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos hr1]
  have hnormm : (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius +
      (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius ≤
      ‖(⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter‖ := by
    have h1 : (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius +
        (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius ≤
        |⟪(⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter, unitNormal hABC⟫| := by
      rw [← hm_inner]
      exact le_abs_self _
    have h2 : |⟪(⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter, unitNormal hABC⟫| ≤
        ‖(⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter‖ * ‖unitNormal hABC‖ := by
      rw [← Real.norm_eq_abs]
      exact norm_inner_le_norm _ _
    rw [unitNormal_norm, mul_one] at h2
    exact le_trans h1 h2
  have habsr : |(⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius -
      (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius| <
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius +
        (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius := by
    rw [abs_lt]
    constructor <;> linarith
  have hlt : |(⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius -
      (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius| <
      ‖(⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
        (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter‖ :=
    lt_of_lt_of_le habsr hnormm
  have hr1r2pos : (0 : ℝ) < |(⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius -
      (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius| := abs_pos.mpr hsub
  have h3 : (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius <
      dist (Kpoint hABC ω) (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter := by
    have h5 : ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius /
        |(⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius -
          (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius|) *
        |(⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius -
          (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius| <
        ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius /
          |(⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius -
            (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius|) *
        ‖(⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).incenter -ᵥ
          (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).incenter‖ :=
      mul_lt_mul_of_pos_left hlt (div_pos hr1 hr1r2pos)
    have h4 : (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius =
        ((⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius /
          |(⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius -
            (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius|) *
        |(⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius -
          (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius| :=
      (div_mul_cancel₀ _ hr1r2pos.ne').symm
    rw [hdist]
    exact lt_of_eq_of_lt h4 h5
  exact ⟨hr_ne, hKO2, h3⟩

/-- The construction behind `external_tangents_through_exsimilicenter`: with
`e = E -ᵥ O1` and `d = dist E O1`, the point
`X = O1 +ᵥ ((r1²/d²) • e + c2' • rot90 e)`, where `c2'` is either of the two
values `± r1 * √(d² - r1²) / d²` (captured here by the hypothesis on
`c2' ^ 2`), lies on the first circle and the radius `O1X` is perpendicular to
`XE`; moreover the line through `E` and `X` is also tangent to the second
circle (with tangency point `(r2/r1) • (X -ᵥ E) +ᵥ E`, by the homothety) and
has both centers strictly on the same side. -/
lemma exsimilicenter_tangent_line {O1 O2 E : Pt} {r1 r2 c2' : ℝ}
    (hr1 : 0 < r1) (hr2 : 0 < r2)
    (hE : E -ᵥ O2 = (r2 / r1) • (E -ᵥ O1))
    (hd : r1 < dist E O1)
    (hc2'sq : c2' ^ 2 = r1 ^ 2 * (dist E O1 ^ 2 - r1 ^ 2) / (dist E O1 ^ 2) ^ 2)
    (hc2'0 : c2' ≠ 0) :
    ∃ X : Pt, X -ᵥ O1 = (r1 ^ 2 / dist E O1 ^ 2) • (E -ᵥ O1) +
        c2' • rot90 (E -ᵥ O1) ∧
      finrank ℝ line[ℝ, E, X].direction = 1 ∧
      (⟨O1, r1⟩ : Sphere Pt).IsTangentAt X line[ℝ, E, X] ∧
      (⟨O2, r2⟩ : Sphere Pt).IsTangent line[ℝ, E, X] ∧
      line[ℝ, E, X].SSameSide O1 O2 := by
  set d := dist E O1
  set e := E -ᵥ O1 with he_def
  have hd0 : 0 < d := hr1.trans hd
  have hd2 : d ^ 2 ≠ 0 := pow_ne_zero 2 hd0.ne'
  have he_norm : d = ‖e‖ := dist_eq_norm_vsub V E O1
  have hi1 : ⟪e, e⟫ = d ^ 2 := by rw [real_inner_self_eq_norm_sq, ← he_norm]
  have hi2 : ⟪e, rot90 e⟫ = 0 := by rw [inner_rot90_right, areaForm_self, neg_zero]
  have hi3 : ⟪rot90 e, e⟫ = 0 := inner_rot90_self e
  have hi4 : ⟪rot90 e, rot90 e⟫ = d ^ 2 := by
    rw [inner_rot90_rot90, real_inner_self_eq_norm_sq, ← he_norm]
  -- The tangency point on the first circle.
  set X := ((r1 ^ 2 / d ^ 2) • e + c2' • rot90 e) +ᵥ O1 with hX_def
  have hXv : X -ᵥ O1 = (r1 ^ 2 / d ^ 2) • e + c2' • rot90 e := by
    rw [hX_def, vadd_vsub]
  -- The two components of `X -ᵥ O1` are orthogonal.
  have hcross : ⟪(r1 ^ 2 / d ^ 2) • e, c2' • rot90 e⟫ = 0 := by
    rw [real_inner_smul_left, real_inner_smul_right, hi2, mul_zero, mul_zero]
  -- `X` lies on the first circle: the two orthogonal components have squared
  -- norms adding up to `r1 ^ 2`.
  have hnorm_sq : ‖X -ᵥ O1‖ ^ 2 = r1 ^ 2 := by
    rw [hXv, norm_add_sq_real, hcross, mul_zero, add_zero, norm_smul, norm_smul,
      Real.norm_eq_abs, Real.norm_eq_abs, norm_rot90, ← he_norm, mul_pow, mul_pow, sq_abs,
      sq_abs, hc2'sq]
    field_simp [hd2]
    ring
  have hdistX : dist X O1 = r1 := by
    rw [dist_eq_norm_vsub]
    exact (pow_left_inj₀ (norm_nonneg _) hr1.le two_ne_zero).mp hnorm_sq
  have hXE : X -ᵥ E = (r1 ^ 2 / d ^ 2) • e + c2' • rot90 e - e := by
    rw [← vsub_sub_vsub_cancel_right X E O1, hXv, ← he_def]
  -- The right angle at `X`: `O1X ⊥ XE`. It is enough to compute
  -- `⟪X -ᵥ O1, e⟫ = r1 ^ 2 = ‖X -ᵥ O1‖ ^ 2`.
  have hinner1 : ⟪X -ᵥ O1, e⟫ = r1 ^ 2 := by
    rw [hXv, inner_add_left, real_inner_smul_left, real_inner_smul_left, hi1, hi3,
      mul_zero, add_zero]
    exact div_mul_cancel₀ _ hd2
  have hinner : ⟪X -ᵥ O1, X -ᵥ E⟫ = 0 := by
    have hde : X -ᵥ E = (X -ᵥ O1) - e := by
      rw [← vsub_sub_vsub_cancel_right X E O1, ← he_def]
    rw [hde, inner_sub_right, real_inner_self_eq_norm_sq, hnorm_sq, hinner1, sub_self]
  have htAt1 : (⟨O1, r1⟩ : Sphere Pt).IsTangentAt X line[ℝ, E, X] := by
    refine ⟨?_, right_mem_affineSpan_pair ℝ E X, ?_⟩
    · exact hdistX
    · apply affineSpan_pair_le_of_mem_of_mem
      · rw [Sphere.mem_orthRadius_iff_inner_left]
        show ⟪E -ᵥ X, X -ᵥ O1⟫ = 0
        rw [← neg_vsub_eq_vsub_rev, inner_neg_left, real_inner_comm, hinner, neg_zero]
      · exact Sphere.self_mem_orthRadius _ _
  -- Transport to the second circle via the homothety of ratio `r2 / r1`.
  set k := r2 / r1
  have hk : 0 < k := div_pos hr2 hr1
  set X' := k • (X -ᵥ E) +ᵥ E with hX'_def
  have hX'E : X' -ᵥ E = k • (X -ᵥ E) := by rw [hX'_def, vadd_vsub]
  have hX'O : X' -ᵥ O2 = k • (X -ᵥ O1) := by
    rw [show X' -ᵥ O2 = (X' -ᵥ E) + (E -ᵥ O2) from (vsub_add_vsub_cancel X' E O2).symm,
      hX'E, hE, ← smul_add, show X -ᵥ E + e = X -ᵥ O1 from vsub_add_vsub_cancel X E O1]
  have hnormX : ‖X -ᵥ O1‖ = r1 := by
    rw [← dist_eq_norm_vsub V X O1]
    exact hdistX
  have hdistX' : dist X' O2 = r2 := by
    rw [dist_eq_norm_vsub, hX'O, norm_smul, Real.norm_eq_abs, abs_of_pos hk, hnormX]
    exact div_mul_cancel₀ r2 hr1.ne'
  have hX'mem : X' ∈ line[ℝ, E, X] := by
    have hv : k • (X -ᵥ E) ∈ line[ℝ, E, X].direction :=
      Submodule.smul_mem _ k
        (AffineSubspace.vsub_mem_direction (right_mem_affineSpan_pair ℝ E X)
          (left_mem_affineSpan_pair ℝ E X))
    have h := AffineSubspace.vadd_mem_of_mem_direction hv (left_mem_affineSpan_pair ℝ E X)
    rw [hX'_def]
    exact h
  have hinner' : ⟪X -ᵥ E, X -ᵥ O1⟫ = 0 := by rw [real_inner_comm, hinner]
  have hEorth : E ∈ (⟨O2, r2⟩ : Sphere Pt).orthRadius X' := by
    rw [Sphere.mem_orthRadius_iff_inner_left]
    show ⟪E -ᵥ X', X' -ᵥ O2⟫ = 0
    have hv : E -ᵥ X' = -(k • (X -ᵥ E)) := by
      rw [hX'_def, vsub_vadd_eq_vsub_sub, vsub_self, zero_sub]
    rw [hv, hX'O, inner_neg_left, real_inner_smul_left, real_inner_smul_right, hinner',
      mul_zero, mul_zero, neg_zero]
  have hXorth : X ∈ (⟨O2, r2⟩ : Sphere Pt).orthRadius X' := by
    rw [Sphere.mem_orthRadius_iff_inner_left]
    show ⟪X -ᵥ X', X' -ᵥ O2⟫ = 0
    have hv : X -ᵥ X' = (1 - k) • (X -ᵥ E) := by
      rw [hX'_def, vsub_vadd_eq_vsub_sub, sub_smul, one_smul]
    rw [hv, hX'O, real_inner_smul_left, real_inner_smul_right, hinner', mul_zero, mul_zero]
  have htAt2 : (⟨O2, r2⟩ : Sphere Pt).IsTangentAt X' line[ℝ, E, X] :=
    ⟨hdistX', hX'mem, affineSpan_pair_le_of_mem_of_mem hEorth hXorth⟩
  have ht2 : (⟨O2, r2⟩ : Sphere Pt).IsTangent line[ℝ, E, X] := htAt2.isTangent
  -- The line is genuine (one-dimensional).
  have hXneE : X ≠ E := by
    intro h
    rw [h] at hdistX
    exact absurd hdistX (ne_of_gt hd)
  have hfr : finrank ℝ line[ℝ, E, X].direction = 1 := by
    rw [direction_affineSpan, vectorSpan_pair]
    exact finrank_span_singleton (vsub_ne_zero.mpr hXneE.symm)
  -- Both centers are strictly on the same side (external tangency).
  have harea : planeOrientation.areaForm e (rot90 e) = d ^ 2 := by
    rw [← inner_rot90_left, inner_rot90_rot90, real_inner_self_eq_norm_sq, ← he_norm]
  have haf1 : planeOrientation.areaForm (O1 -ᵥ E) (X -ᵥ E) = -c2' * d ^ 2 := by
    rw [hXE, ← neg_vsub_eq_vsub_rev, ← he_def]
    simp only [areaForm_neg_left, map_sub, map_add, map_smul, smul_eq_mul, areaForm_self,
      harea]
    ring
  have hO2E : O2 -ᵥ E = k • (O1 -ᵥ E) := by
    rw [← neg_vsub_eq_vsub_rev E O2, ← neg_vsub_eq_vsub_rev E O1, ← he_def, hE, smul_neg]
  have hprod : 0 < planeOrientation.areaForm (O1 -ᵥ E) (X -ᵥ E) *
      planeOrientation.areaForm (O2 -ᵥ E) (X -ᵥ E) := by
    rw [hO2E, map_smul, LinearMap.smul_apply, smul_eq_mul, haf1]
    have heq : -c2' * d ^ 2 * (k * (-c2' * d ^ 2)) = k * (-c2' * d ^ 2) ^ 2 := by ring
    rw [heq]
    exact mul_pos hk (pow_two_pos_of_ne_zero (mul_ne_zero (neg_ne_zero.mpr hc2'0) hd2))
  have hSS : line[ℝ, E, X].SSameSide O1 O2 :=
    (sSameSide_iff_areaForm_mul_pos (vsub_ne_zero.mpr hXneE)).mpr hprod
  exact ⟨X, hXv, hfr, htAt1, ht2, hSS⟩

/-- Through the exsimilicenter `E` of two circles (with distinct radii),
there are exactly two common external tangent lines, both passing through
`E`. -/
lemma external_tangents_through_exsimilicenter {O1 O2 E : Pt} {r1 r2 : ℝ}
    (hr1 : 0 < r1) (hr2 : 0 < r2) (hr12 : r1 ≠ r2)
    (hE : E -ᵥ O2 = (r2 / r1) • (E -ᵥ O1))
    (hd : r1 < dist E O1) :
    ∃ ℓ₁ ℓ₂ : AffineSubspace ℝ Pt, ℓ₁ ≠ ℓ₂ ∧
      CommonExternalTangent (⟨O1, r1⟩ : Sphere Pt) (⟨O2, r2⟩ : Sphere Pt) ℓ₁ ∧
      CommonExternalTangent (⟨O1, r1⟩ : Sphere Pt) (⟨O2, r2⟩ : Sphere Pt) ℓ₂ ∧
      E ∈ ℓ₁ ∧ E ∈ ℓ₂ := by
  have _ := hr12
  set d := dist E O1
  set e := E -ᵥ O1 with he_def
  have hd0 : 0 < d := hr1.trans hd
  have hr1d : r1 ^ 2 < d ^ 2 := pow_lt_pow_left₀ hd hr1.le two_ne_zero
  have hsq : 0 < d ^ 2 - r1 ^ 2 := sub_pos.mpr hr1d
  set c2 := r1 * Real.sqrt (d ^ 2 - r1 ^ 2) / d ^ 2 with hc2_def
  have hc2pos : 0 < c2 := by
    rw [hc2_def]
    exact div_pos (mul_pos hr1 (Real.sqrt_pos.mpr hsq)) (pow_pos hd0 2)
  have hc2sq : c2 ^ 2 = r1 ^ 2 * (d ^ 2 - r1 ^ 2) / (d ^ 2) ^ 2 := by
    rw [hc2_def, div_pow, mul_pow, Real.sq_sqrt hsq.le]
  obtain ⟨Xp, hXpv, hfrp, htAtp, ht2p, hSSp⟩ :=
    exsimilicenter_tangent_line hr1 hr2 hE hd hc2sq hc2pos.ne'
  obtain ⟨Xm, hXmv, hfrm, htAtm, ht2m, hSSm⟩ :=
    exsimilicenter_tangent_line hr1 hr2 hE hd (c2' := -c2)
      (by rw [neg_sq]; exact hc2sq) (neg_ne_zero.mpr hc2pos.ne')
  have he_norm : d = ‖e‖ := dist_eq_norm_vsub V E O1
  have harea : planeOrientation.areaForm e (rot90 e) = d ^ 2 := by
    rw [← inner_rot90_left, inner_rot90_rot90, real_inner_self_eq_norm_sq, ← he_norm]
  -- The two lines are distinct: a common tangent line of the first circle
  -- touches it at a single point, but `Xp ≠ Xm` since `c2 ≠ 0`.
  have hne : line[ℝ, E, Xp] ≠ line[ℝ, E, Xm] := by
    intro hline
    rw [← hline] at htAtm
    have hXX : Xp = Xm := Sphere.IsTangentAt.eq_of_isTangentAt htAtp htAtm
    have h2 : Xp -ᵥ O1 = Xm -ᵥ O1 := congrArg (· -ᵥ O1) hXX
    rw [hXpv, hXmv, ← he_def] at h2
    have h3 := congrArg (fun v => planeOrientation.areaForm e v) h2
    simp only [map_add, map_smul, smul_eq_mul, areaForm_self, harea] at h3
    have h4 : 0 < c2 * d ^ 2 := mul_pos hc2pos (pow_pos hd0 2)
    linarith [h3, h4]
  exact ⟨line[ℝ, E, Xp], line[ℝ, E, Xm], hne,
    ⟨hfrp, htAtp.isTangent, ht2p, hSSp⟩, ⟨hfrm, htAtm.isTangent, ht2m, hSSm⟩,
    left_mem_affineSpan_pair ℝ E Xp, left_mem_affineSpan_pair ℝ E Xm⟩

snip end

problem imo2008_p6 {A B C D : Pt} {ω ω₁ ω₂ : Sphere Pt}
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hADC : AffineIndependent ℝ ![A, D, C])
    -- ABCD is a convex quadrilateral (with the vertices in that cyclic
    -- order).
    (hconvex : ConvexQuadrilateral A B C D)
    -- BA ≠ BC.
    (hBA_ne_BC : dist B A ≠ dist B C)
    -- ω1 and ω2 are the incircles of triangles ABC and ADC.
    (hω₁ : ω₁ = (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).insphere)
    (hω₂ : ω₂ = (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).insphere)
    -- ω is a circle tangent to ray BA beyond A and to ray BC beyond C,
    -- and also tangent to the lines AD and CD.
    (hωpos : 0 < ω.radius)
    (hωBA : ∃ T : Pt, [B, A, T].Sbtw ℝ ∧ ω.IsTangentAt T line[ℝ, B, A])
    (hωBC : ∃ T : Pt, [B, C, T].Sbtw ℝ ∧ ω.IsTangentAt T line[ℝ, B, C])
    (hωAD : ω.IsTangent line[ℝ, A, D])
    (hωCD : ω.IsTangent line[ℝ, C, D]) :
    ∃ K : Pt, ∃ ℓ₁ ℓ₂ : AffineSubspace ℝ Pt,
      K ∈ (ω : Set Pt) ∧ ℓ₁ ≠ ℓ₂ ∧ K ∈ ℓ₁ ∧ K ∈ ℓ₂ ∧
      CommonExternalTangent ω₁ ω₂ ℓ₁ ∧ CommonExternalTangent ω₁ ω₂ ℓ₂ := by
  -- Step 5: `K` is the exsimilicenter of the two incircles.
  obtain ⟨hr12, hE, hd⟩ := Kpoint_exsimilicenter_spec hABC hADC hconvex hBA_ne_BC
    hωpos hωBA hωBC hωAD hωCD
  -- Step 6: the two common external tangents of the incircles pass through
  -- the exsimilicenter.
  obtain ⟨ℓ₁, ℓ₂, hne, hcet1, hcet2, hK1, hK2⟩ :=
    external_tangents_through_exsimilicenter
      (⟨![A, B, C], hABC⟩ : Triangle ℝ Pt).inradius_pos
      (⟨![A, D, C], hADC⟩ : Triangle ℝ Pt).inradius_pos hr12 hE hd
  -- Step 7: transport the tangencies to `ω₁ = t.insphere` and
  -- `ω₂ = t₂.insphere` (defeq: `Simplex.insphere_center/radius` are `rfl`).
  rw [hω₁, hω₂]
  exact ⟨Kpoint hABC ω, ℓ₁, ℓ₂, Kpoint_mem_sphere hABC hωpos, hne, hK1, hK2,
    hcet1, hcet2⟩

end Imo2008P6

/-!
## Progress notes (formalization COMPLETE — zero `sorry`)

### Status

Statement fully formalized and believed faithful to the original problem
(the convexity hypothesis was re-packaged as the determinant-based
`ConvexQuadrilateral`, see below). **The main theorem `imo2008_p6` is
proved; the file contains no `sorry`.**

Proved so far (no `sorry`):
- `CommonExternalTangent.symm`.
- `Sphere.IsTangentAt.dist_sq_eq` (tangent length squared = power of the
  point) and `dist_eq_dist_of_isTangentAt` (tangents from a common point
  are equal — NOTE: mathlib already has this as
  `EuclideanGeometry.Sphere.IsTangentAt.dist_eq_of_mem_of_mem`
  (Sphere/Tangent.lean:121); keep or refactor later).
- `IsTangentAt.inner_vsub_center_eq` / `_nonneg` / `_pos`: the
  chord-radius identity `⟪X -ᵥ T, ω.center -ᵥ T⟫ = ‖X -ᵥ T‖ ^ 2 / 2`
  (computational content of "the sphere lies on one side of a tangent
  line") — the primitive for all side-propagation arguments.
- Incircle touchpoint package (proved):
  `dist_point_touchpoint_empty_eq`, `touchpoint_dist_eqs`,
  `touchpoint_dist_eqs_mk`, `points_mk_zero`, `points_mk_two`,
  `wbtw_touchpoint_insphere`, `dist_touchpoint_insphere_left`
  (`AP = (AB + AC - BC)/2`), `dist_touchpoint_insphere_right`
  (`CP = (CA + CB - AB)/2`). Built on mathlib's
  `Affine.Triangle.sbtw_touchpoint_empty` (Incenter.lean:1338, touchpoint
  strictly between vertices) and `isTangentAt_insphere_touchpoint`.
- `rot90` (90° rotation of `planeOrientation`) with simp wrappers
  `inner_rot90_left/right`, `rot90_rot90`, `inner_rot90_rot90`,
  `norm_rot90`, `inner_rot90_self`, `areaForm_self`, `areaForm_swap`.
- `eq_smul_add_smul_rightAngleRotation` (and the `o`-parameterized
  `eq_smul_add_smul_rightAngleRotation'`): decomposition of any vector in
  the orthogonal basis `{u, J u}` — the workhorse for coefficient
  computations (proved via the Lagrange identity
  `Orientation.inner_sq_add_areaForm_sq`).
- `inner_neg_of_areaForm_mul` (proved): the wedge
  computation — if `ωF x u * ωF u v = r‖u‖|ωF u v|` and
  `ωF x v * ωF u v = -r‖v‖|ωF u v|` with `r > 0`, `u ≠ 0`, `ωF u v ≠ 0`,
  then `⟪x, u⟫ < 0`. Applied with `x := ω.center -ᵥ D`, `u := A -ᵥ D`
  (and the mirror instance `u := C -ᵥ D`, `v := A -ᵥ D`) it gives the
  touchpoint positions `⟪O -ᵥ D, D -ᵥ A⟫ > 0`, `⟪O -ᵥ D, D -ᵥ C⟫ > 0`.
- `exists_pos_smul_vsub_of_sbtw`: `[B, A, T].Sbtw`-style hypotheses give
  `T -ᵥ A = σ • (A -ᵥ B)` with `σ > 0` (via `Wbtw.sameRay_vsub` +
  `SameRay.exists_pos`).
- `IsTangentAt.inner_vsub_center_eq_zero`: the radius to a tangent point
  is perpendicular to the tangent subspace.
- `IsTangentAt.abs_inner_vsub_center_rot90`: the determinant-form
  "distance from center to tangent line equals radius":
  `|⟪ω.center -ᵥ T, rot90 (X -ᵥ Y)⟫| = ω.radius * ‖X -ᵥ Y‖` for
  `X, Y` on the tangent subspace (via the Lagrange identity).
- **Step 1 COMPLETE — the external Pitot theorem** (`external_pitot`):
  `dist B A + dist A D = dist C B + dist C D`. Built from:
  `areaForm_center_left` / `areaForm_center_right` (the two side-chain
  lemmas), `inner_neg_of_areaForm_mul`
  instantiated twice (wedge at `D` on both sides),
  `wbtw_of_projection_beyond` (touchpoints `U, W` lie beyond `D`), and
  the length chase with `Wbtw.dist_add_dist` and mathlib's
  `IsTangentAt.dist_eq_of_mem_of_mem`.
- **Step 2 COMPLETE** (`dist_touchpoint_eq`): the two incircle
  touchpoints on `AC` satisfy `AP = CT` (reflection about the midpoint of
  `AC` in distances), from `external_pitot` + `dist_touchpoint_insphere_*`.
- **The sidedness bridge** `sSameSide_iff_areaForm_mul_pos` (+
  `mem_line_of_areaForm_eq_zero`): `line[ℝ, B, A].SSameSide X Y ↔
  0 < areaForm (X -ᵥ B) (A -ᵥ B) * areaForm (Y -ᵥ B) (A -ᵥ B)`.
  This converts mathlib's `SSameSide` facts (incenter/excenter side
  lemmas, e.g. `Simplex.sSameSide_incenter_point`,
  `Simplex.sSameSide_excenter_singleton_point`,
  `sOppSide_excenter_singleton_point`) into `areaForm` sign relations
  and back (needed for `CommonExternalTangent`'s `SSameSide`).
- **Excircle touchpoint package** (proved):
  `dist_point_touchpoint_singleton_eq`, `touchpoint_exsphere_dist_eqs`,
  `dist_touchpoint_exsphere_left`
  (`AT' = (BC + CA - AB)/2` for the B-excircle touchpoint `T'` on `AC`),
  `dist_touchpoint_exsphere_right` (`CT' = (CA + AB - BC)/2`). Built on
  mathlib's `ExcenterExists.isTangentAt_touchpoint`,
  `Affine.Triangle.sbtw_touchpoint_singleton` (touchpoint strictly inside
  the side) and `Affine.Triangle.touchpoint_singleton_sbtw` (touchpoints
  on the extensions beyond the vertices).
- **Proportionality machinery**: `eq_zero_of_areaForm_eq_zero_eq_zero`
  (areaForm nondegenerate on a basis), `smul_of_areaForm_smul_areaForm`,
  `smul_of_areaForm_pattern` (two centers with the same signed-normal
  pattern are proportional, with an overall sign flipping the ratio),
  `areaForm_ne_zero_of_affineIndependent`, and the helper
  `areaForm_center_mul_areaForm_of_isTangentAt` (
  magnitude × sign for a tangent circle with center on a given side).
- **Signed normal components of all relevant centers**:
  `areaForm_center_B_left/right` (for `ω.center` at `B`, sign chain via
  chord-radius positivity — no convexity needed),
  `areaForm_incenter_left/right` and `areaForm_excenter_left/right`
  (incenter/excenter at `B`, signs via mathlib side lemmas + the bridge).
- **Center collinearities (the homothety relations)**:
  `center_vsub_B_eq_smul : O -ᵥ B = (R/r1) • (O1 -ᵥ B)` and
  `excenter_vsub_B_eq_smul : E_B -ᵥ B = (r_B/r1) • (O1 -ᵥ B)`,
  both instances of `smul_of_areaForm_pattern` with pattern `(-1, +1)`.
- **Sidedness extras**: `sOppSide_areaForm_mul_neg` (opposite-side
  bridge), `eq_of_dist_eq_of_wbtw` (points on a segment are determined
  by their distance to an endpoint), `eq_neg_smul_of_mul_neg_abs`
  (sign×magnitude ⟹ ratio), `areaForm_ne_zero_of_affineIndependent`,
  `areaForm_DAC_eq_ADC`, `areaForm_mul_neg_of_convexQuadrilateral`
  (B, D on opposite sides of `AC` from `hconvex`).
- **Touchpoint coincidences**: `excircle_touchpoint_eq_insphere_touchpoint`
  (`T' = T`, B-excircle touchpoint of `ABC` = incircle touchpoint of `ADC`)
  and `excenter_touchpoint_eq_insphere_touchpoint'` (`P'' = P`, the mirror),
  via the excircle formulas + `dist_touchpoint_eq` / `external_pitot` +
  `eq_of_dist_eq_of_wbtw`.
- **The normal relation** `touchpoint_vsub_incenter_neg_smul`:
  `T -ᵥ O2 = -(r2/r1) • (P -ᵥ O1)` (the two incircle touchpoint offsets
  are antiparallel — the incenters lie on opposite sides of `AC`).
- **Collinearities**: `excenter_vsub_touchpoint_eq_smul`
  (`E_B -ᵥ T' = (r_B/r1) • (P -ᵥ O1)`, the classical lemma R2),
  `collinear_B_Q_T : T -ᵥ B = (r_B/r1) • ((O1 -ᵥ P) + (O1 -ᵥ B))` and
  `collinear_D_S_P : P -ᵥ D = (r_D/r2) • ((O2 -ᵥ T) + (O2 -ᵥ D))`.
- **The point K and its homotheties**: `unitNormal` (the shared unit
  normal `n̂ = (P -ᵥ O1)/r1`, with `unitNormal_norm : ‖n̂‖ = 1`),
  `Kpoint hABC ω := (-(R • n̂)) +ᵥ O` (the point of ω at the `B`-side
  extreme perpendicular to `AC`), `Kpoint_mem_sphere : Kpoint ∈ ω`,
  `Kpoint_vsub_B : K -ᵥ B = (R/r1) • ((O1 -ᵥ P) + (O1 -ᵥ B))` and
  `Kpoint_vsub_D : K -ᵥ D = -(R/r2) • ((O2 -ᵥ T) + (O2 -ᵥ D))`
  (built on `center_vsub_B_eq_smul`, `center_vsub_D_eq_neg_smul`, and
  `touchpoint_vsub_incenter_neg_smul`).
- **Step 5 — K is the exsimilicenter**:
  `Kpoint_exsimilicenter_spec : r1 ≠ r2 ∧ K -ᵥ O2 = (r2/r1) • (K -ᵥ O1) ∧
  r1 < dist K O1`. Built from `span_singleton_eq_span_singleton_of_smul`,
  `insphere_tangent_inner_package` (the step-A vector/inner-product
  identities, incl. `⟪O2 -ᵥ O1, n̂⟫ = r1 + r2`), `antipode_not_mem_line`
  (`Q ∉ line AC`), `insphere_touchpoint_ne` (`T' ≠ P`, via the
  `2·AP = AC ⟹ AB = BC` contradiction with `hBA_ne_BC`),
  `Kpoint_mem_line_antipode_touchpoint` (`K ∈ line[ℝ, Q, T']`),
  `Kpoint_mem_line_touchpoint_antipode` (`K ∈ line[ℝ, P, S]`),
  `antipode_lines_ne` (`line QT' ≠ line PS`), and uniqueness of the
  intersection of two distinct lines (`AffineSubspace.ext_of_direction_eq`).
- **Step 6 COMPLETE — external tangents through the exsimilicenter**
  `external_tangents_through_exsimilicenter` (two
  distinct `CommonExternalTangent` lines of `⟨O1, r1⟩`, `⟨O2, r2⟩` through
  `E`, given `E -ᵥ O2 = (r2/r1) • (E -ᵥ O1)` and `r1 < dist E O1`), built
  from `exsimilicenter_tangent_line` (the `X±` construction: tangency at
  `O1 +ᵥ ((r1²/d²)•e ± c2•rot90 e)`, Pythagoras via `norm_add_sq_real`,
  right angle via `⟪X -ᵥ O1, e⟫ = r1²`, transport by the `r2/r1`
  homothety, `SSameSide` via the areaForm bridge, distinctness via
  mathlib's `Sphere.IsTangentAt.eq_of_isTangentAt`).
- **Step 7 COMPLETE — final assembly** (`imo2008_p6`, zero `sorry`):
  `K := Kpoint hABC ω` with `Kpoint_mem_sphere`; the two lines from step 6
  instantiated at the incenters/inradii via step 5's spec; tangencies
  transported to `ω₁ = t.insphere`, `ω₂ = t₂.insphere` by `rw [hω₁, hω₂]`
  (defeq, since mathlib's `Simplex.insphere_center/radius` are `rfl`).

### Route spec that was followed for steps 5–7 (all DONE; kept for
### reference)

5. **K is the exsimilicenter**: let `Q := O1 +ᵥ (O1 -ᵥ P)` (antipode of
   `P` in ω1, so `Q -ᵥ B = (O1 -ᵥ P) + (O1 -ᵥ B)` by `vadd_vsub`, matching
   `Kpoint_vsub_B` and `collinear_B_Q_T`), `S := O2 +ᵥ (O2 -ᵥ T)`
   (matching `Kpoint_vsub_D` and `collinear_D_S_P`).
   - `Q, T` and `P, S` are parallel-radii endpoint pairs:
     `Q -ᵥ O1 = -(P -ᵥ O1) = -r1 • n̂` and `T -ᵥ O2 = -r2 • n̂`
     (`touchpoint_vsub_incenter_neg_smul` rewrites the second to
     `-(r2/r1)•(P -ᵥ O1)`), while `P -ᵥ O1 = +r1 • n̂` and
     `S -ᵥ O2 = O2 -ᵥ T = +r2 • n̂`. Hence the exsimilicenter
     `E := O1 +ᵥ (r1/(r1-r2)) • (O2 -ᵥ O1)` (needs `r1 ≠ r2`, see below)
     satisfies `E -ᵥ Q = (r1/(r1-r2)) • (T -ᵥ Q)` and
     `E -ᵥ P = (r1/(r1-r2)) • (S -ᵥ P)` (pure `smul` algebra with
     `(T -ᵥ Q) = (O2 -ᵥ O1) + (r1-r2)•n̂`, `(S -ᵥ P) = (O2 -ᵥ O1) - (r1-r2)•n̂`),
     i.e. `E ∈ line[ℝ, Q, T]` and `E ∈ line[ℝ, P, S]`. Also
     `E -ᵥ O2 = (r2/r1) • (E -ᵥ O1)` (external division, for step 6).
   - `K ∈ line[ℝ, B, Q]` (from `Kpoint_vsub_B`, `K -ᵥ B ∈ span (Q -ᵥ B)`)
     and `T ∈ line[ℝ, B, Q]` (from `collinear_B_Q_T`); since `Q ∉ line AC`
     (its `areaForm (Q -ᵥ A) (A -ᵥ C) = 2·areaForm (O1 -ᵥ A) (A -ᵥ C) ≠ 0`)
     but `T ∈ line AC`, `Q ≠ T`, so `line[ℝ, Q, T] = line[ℝ, B, Q]` and
     `K ∈ line[ℝ, Q, T]`. Mirror: `K ∈ line[ℝ, P, S]`.
   - `r1 ≠ r2` and `QT ≠ PS`: if `r1 = r2`, then `T - Q = S - P = O2 - O1`,
     so lines `QT ∥ PS` (or equal); `K` on both forces `QT = PS`, hence
     `Q, T, P, S` collinear, hence `Q - P ∥ n̂` gives `O1O2 ∥ n̂`, i.e. the
     two incenters have the same foot on `AC`: `P = T`. Then
     `dist A P = dist A T = dist A C - dist C T = dist A C - dist A P`
     (step 2: `dist C T = dist A P`; `T` on segment: `Wbtw.dist_add_dist`),
     so `2·dist A P = dist A C`, i.e. `dist A B = dist B C` (by
     `dist_touchpoint_insphere_left`), contradicting `hBA_ne_BC`.
   - `K = E`: `K -ᵥ E ∈ direction(QT) ∩ direction(PS) = {0}` (two
     non-parallel lines meet in at most one point; `QT ≠ PS` above).
6. **External tangents through the exsimilicenter**: for two circles with
   `r1 ≠ r2`, the two tangent lines from `E` to ω1 are also tangent to ω2
   (same side), are distinct, and pass through `E = K ∈ ω`.
   - `dist E O1 > r1`: `EO1 = (r1/|r1-r2|)·|O1O2|` and
     `|O1O2| ≥ r1 + r2 > |r1 - r2|` (O1, O2 on opposite sides of `AC`;
     decompose `O2 -ᵥ O1` along/⟂ `AC`: the ⟂-component is `r1 + r2`).
   - Tangent-point construction: with `d := dist E O1`, `e := E -ᵥ O1`,
     `X± := O1 +ᵥ ((r1²/d²)•e ± (r1·√(d²-r1²)/d²)•rot90 e)`: verify
     `‖X± - O1‖ = r1` (Pythagoras) and `⟪X± - O1, X± - E⟫ = 0`
     (expand: cross terms vanish since `⟪e, rot90 e⟫ = 0`), so
     `ℓ± := line[ℝ, E, X±]` is tangent to ω1 at `X±`
     (`IsTangentAt` via `le_orthRadius`: direction `span(X± - E) ⊥ (X± - O1)`;
     `E ≠ X±` from `d > r1 > 0`, so the direction has `finrank 1`).
   - Transport to ω2: `X'± := E +ᵥ (r2/r1)•(X± - E)`: `X'± - O2 =
     (r2/r1)•(X± - O1)` (from `E -ᵥ O2 = (r2/r1)•(E -ᵥ O1)`) so
     `‖X'± - O2‖ = r2`, `X'± ∈ ℓ±` (same line through `E`), and
     `⟪X'± - O2, X± - E⟫ = (r2/r1)·⟪X± - O1, X± - E⟫ = 0`, so `ℓ±` is
     also tangent to ω2 at `X'±`. `CommonExternalTangent` follows:
     `finrank direction = 1`, both tangencies, and centers on the same side
     via the bridge (`areaForm (O2 -ᵥ E) w = (r2/r1)·areaForm (O1 -ᵥ E) w`,
     same sign, `w := X± - E ≠ 0`).
   - Distinctness: `ℓ₊ ≠ ℓ₋` since `areaForm w₊ w₋ = -2c₁c₂‖e‖² ≠ 0`
     (`c₁ = (r1²-d²)/d² < 0`, `c₂ = r1√(d²-r1²)/d² > 0` from `d > r1`;
     equal lines would give `w₋ = c•w₊`, hence `areaForm w₊ w₋ = 0`).
7. **Final assembly**: `K := Kpoint hABC ω` (with `Kpoint_mem_sphere`),
   `ℓ₁, ℓ₂ := ℓ₊, ℓ₋` from step 6, and
   `E = K` from step 5 transports the tangencies to `K`. The `problem`
   statement's conclusion is exactly `∃ K ∈ ω, ∃ ℓ₁ ≠ ℓ₂, both
   `CommonExternalTangent ω₁ ω₂`, both through `K`.

### Pitfalls (accumulated; check the older notes below too)

- `p -ᵥ v` (point − vector) does NOT typecheck in this mathlib: write
  `(-v) +ᵥ p`. `-a • x` parses as `(-a) • x` (scalar negated); whole-smul
  negation needs parens `-(a • x)`. Convert with `neg_smul`
  (`(-r)•x = -(r•x)`) and `smul_neg` (`r•(-x) = -(r•x)`); `neg_one_mul`
  for `(-1)·a = -a`. `vadd_vsub : (v +ᵥ p) -ᵥ p = v`;
  `vsub_vadd : (p₁ -ᵥ p₂) +ᵥ p₂ = p₁`;
  `vsub_sub_vsub_cancel_left (a b c) : (a -ᵥ b) - (a -ᵥ c) = c -ᵥ b`.
- `rw [add_comm]` can hit a stray `2 + 1` inside `Fin`-typed matrix
  literals — use `exact add_comm _ _` against an add_comm-shaped goal, or
  `conv_lhs => rw [add_comm]`.
- `rw` closes goals by defeq only with reducible transparency; `congr 1`
  closes coefficient goals like `R·r1⁻¹ = R/r1` (do not follow it with
  more rewrites). `field_simp [h.ne']` handles ratio coefficients.
- `Simplex.exsphere_center/radius`, `Simplex.insphere_center/radius`
  (simp lemmas projecting `exsphere/excenter` and `insphere/incenter` to
  the sphere's center/radius fields — needed when applying
  `IsTangentAt.*` lemmas stated for `Sphere` to `s.insphere`/`s.exsphere`).
4. **K and the homotheties**: `K := O -ᵥ R • n̂`; from
   `O -ᵥ B = (R/r1)•(O1 -ᵥ B)` (step 3) and `Q = O1 -ᵥ r1•n̂` get
   `K -ᵥ B = (R/r1)•(Q -ᵥ B)` (`K ∈ line BQ = line QT`); at `D`:
   `O -ᵥ D = -(R/r2)•(O2 -ᵥ D)` — needs the `O2` analogues of Lemmas A/B:
   `areaForm (O2 -ᵥ D) u · c₃ = -r2‖u‖|c₃|` and
   `areaForm (O2 -ᵥ D) v · c₃ = +r2‖v‖|c₃|` (signs OPPOSITE to `O`'s:
   `O2` same side as `C` over `AD`, same side as `A` over `CD`, from
   `sSameSide_incenter_point` + bridge; magnitudes from
   `IsTangentAt.abs_inner_vsub_center_rot90` on the insphere's
   touchpoints — the helper `areaForm_center_mul_areaForm_of_isTangentAt`
   does exactly this twice, then `smul_of_areaForm_pattern` with `s = -1`
   against Lemmas A/B's equations).
4. **K and the homotheties**: `K := O -ᵥ R • n̂`; from
   `O -ᵥ B = (R/r1)•(O1 -ᵥ B)` (step 3) and `Q = O1 -ᵥ r1•n̂` get
   `K -ᵥ B = (R/r1)•(Q -ᵥ B)` (`K ∈ line BQ = line QT`); at `D`:
   `O -ᵥ D = -(R/r2)•(O2 -ᵥ D)` — THIS IS ALREADY HALF-DONE:
   `areaForm_center_left/right` + the wedge give
   `⟪O -ᵥ D, u⟫ = -(R‖u‖/|c₃|)(|u||v| + ⟪u,v⟫)` and the same
   computation with `O2` (`sSameSide_incenter_point` for its wedge)
   gives `⟪O2 -ᵥ D, u⟫ = +(r2‖u‖/|c₃|)(|u||v|+⟪u,v⟫)`; the full vector
   equality `O -ᵥ D = -(R/r2)(O2 -ᵥ D)` needs BOTH components
   (`⟪·, u⟫` and `⟪·, rot90 u⟫`/`areaForm (O -ᵥ D) u = ±R‖u‖` signs
   from Lemmas A/B vs. their `O2` analogues), then
   `K -ᵥ D = -(R/r2)•(S -ᵥ D)` with `S = O2 + r2•n̂`.
5. **K is the exsimilicenter**: `O1Q = -r1•n̂ ∥ O2T = -r2•n̂` (same
   direction radii) ⟹ line `QT` through exsimilicenter `E`
   (characterize `E` as the point on line `O1O2` with
   `E -ᵥ O1 = (r1/(r1-r2))•(O2 -ᵥ O1)`-style external division; the
   parallel-radii fact: line through `Q = O1 - r1•n̂` and
   `T = O2 - r2•n̂` passes through `E`); similarly `O1P ∥ O2S` (`+n̂`)
   ⟹ line `PS` through `E`. `K` on both ⟹ `K = E` (lines `QT`, `PS`
   distinct — else `r1 = r2` giving `QT ∥ PS`, contradiction with `K`
   on both; `BA ≠ BC` enters here or earlier).
6. **External tangents through the exsimilicenter**: for two circles
   with `r1 ≠ r2`, the two tangent lines from `E` to ω1 are also tangent
   to ω2 (homothety at `E` with ratio `r2/r1` maps ω1 ↦ ω2 and preserves
   tangency), are distinct, and are common external tangents (centers on
   the same side). Needs: tangents from an exterior point
   (`E` exterior since `EO1 > r1`), tangency transport along homothety
   (prove `AffineMap.homothety` maps spheres to spheres and preserves
   `IsTangentAt`: dist scaling + orthRadius mapping), sides via
   chord-radius positivity.

### The side-chain (next target, fully specified; signs verified
### numerically on the same concrete configuration as before)

Two lemmas, feeding `inner_neg_of_areaForm_mul`. Write
`u := A -ᵥ D`, `v := C -ᵥ D`, `c₃ := areaForm (D -ᵥ C) (A -ᵥ D)`,
`c₂ := areaForm (C -ᵥ B) (D -ᵥ C)`, `c₄ := areaForm (A -ᵥ D) (B -ᵥ A)`
(three of the four `ConvexQuadrilateral` crosses; note
`c₃ = areaForm u v` EXACTLY, by two swaps).

**Lemma A** (`areaForm_center_left`): from `0 < c₃ * c₄` (one branch of
`hconvex`), `0 < ω.radius`, `[B, A, T₁].Sbtw ℝ`,
`ω.IsTangentAt T₁ line[ℝ, B, A]`, `ω.IsTangentAt U line[ℝ, A, D]`:
conclude `areaForm (ω.center -ᵥ D) u * c₃ = ω.radius * ‖u‖ * |c₃|`.
**Lemma B** (`areaForm_center_right`): from `0 < c₃ * c₂`, the ray
hypothesis on `BC` and `ω.IsTangentAt W line[ℝ, C, D]`:
conclude `areaForm (ω.center -ᵥ D) v * c₃ = -ω.radius * ‖v‖ * |c₃|`.

Proof skeleton for Lemma A (Lemma B mirrors it with the sign flips listed
below):
1. `u ≠ 0` (else `c₄ = 0`, contradicting `0 < c₃ * c₄`); `T₁ ≠ U`
   (`T₁ ∈ line BA ∩ line AD = {A}` since `areaForm (A -ᵥ B) (A -ᵥ D) ≠ 0`,
   but `T₁ ≠ A` by the `Sbtw`).
2. `areaForm (O -ᵥ D) u = -⟪O -ᵥ U, rot90 u⟫`: from
   `inner_rot90_right` and `⟪U -ᵥ D, rot90 u⟫ = 0`
   (`U -ᵥ D ∈ span u`: `U, D ∈ line[ℝ, A, D]`,
   `AffineSubspace.vsub_mem_direction` + `direction_line`/vectorSpan_pair, then
   `mem_span_singleton` gives `U -ᵥ D = c • u`, and
   `⟪u, rot90 u⟫ = -areaForm u u = 0`).
3. `|⟪O -ᵥ U, rot90 u⟫| = ω.radius * ‖u‖`:
   `IsTangentAt.abs_inner_vsub_center_rot90` with `X := A`, `Y := D`.
4. Sign: `0 < ⟪O -ᵥ U, rot90 u⟫ * (-c₄)`. Chain:
   `⟪T₁ -ᵥ U, rot90 u⟫ = ⟪T₁ -ᵥ D, rot90 u⟫` (same span argument) and
   `T₁ -ᵥ D = (A -ᵥ D) + σ • (A -ᵥ B)` (from
   `exists_pos_smul_vsub_of_sbtw` on the `Sbtw`, via `List.sbtw_triple`),
   so `⟪T₁ -ᵥ D, rot90 u⟫ = σ * ⟪A -ᵥ B, rot90 u⟫ = σ * (-c₄)`
   (`⟪A -ᵥ B, rot90 u⟫ = -areaForm (A -ᵥ B) u` and
   `areaForm (A -ᵥ B) (A -ᵥ D) = c₄` by two swaps).
   Chord positivity `⟪T₁ -ᵥ U, O -ᵥ U⟫ > 0`
   (`IsTangentAt.inner_vsub_center_pos`, needs `T₁ ≠ U`) together with
   `O -ᵥ U = (⟪O -ᵥ U, rot90 u⟫ / ‖u‖ ^ 2) • rot90 u` (from
   `eq_smul_add_smul_rightAngleRotation` with `⟪O -ᵥ U, u⟫ = 0`, which is
   `IsTangentAt.inner_vsub_center_eq_zero` at `X := A`, `Y := D`)
   gives `0 < ⟪O -ᵥ U, rot90 u⟫ * ⟪T₁ -ᵥ U, rot90 u⟫`
   (the factor `‖u‖ ^ 2 > 0`), hence the claim with the previous step.
5. Assemble: `areaForm (O -ᵥ D) u * c₃ = (-⟪O -ᵥ U, rot90 u⟫) * c₃`;
   from steps 4 (`X := -⟪O -ᵥ U, rot90 u⟫` has `0 < X * c₄`) and
   `0 < c₃ * c₄` derive `0 < X * c₃` (via
   `nlinarith [mul_pos hX4 h34, sq_pos_of_ne_zero c₄]` or manual field
   manipulations); then `X * c₃ = |X * c₃| = |X| * |c₃| = ω.radius * ‖u‖ * |c₃|`
   (step 3, `abs_mul`, `abs_of_pos`).

Lemma B sign flips (verified numerically): with `v = C -ᵥ D`,
`⟪C -ᵥ B, rot90 v⟫ = c₂` (EXACT, by swaps), so
`⟪T₂ -ᵥ D, rot90 v⟫ = τ * c₂` (`τ > 0`), giving
`0 < ⟪O -ᵥ W, rot90 v⟫ * c₂`, hence `⟪O -ᵥ W, rot90 v⟫` has sign
`sign c₃`, and `areaForm (O -ᵥ D) v = -⟪O -ᵥ W, rot90 v⟫` has sign
`-sign c₃`, giving the negative product with `|⟪O -ᵥ W, rot90 v⟫| = ω.radius * ‖v‖`.

After Lemmas A and B: `inner_neg_of_areaForm_mul` with
`x := ω.center -ᵥ D`, `r := ω.radius` gives `⟪O -ᵥ D, u⟫ < 0`, i.e.
`⟪O -ᵥ D, D -ᵥ A⟫ > 0`; the mirror instance (`u := v`, `v := u`,
`h1 := Lemma B with c₃ = areaForm u v` swapped, `h2 := Lemma A`) gives
`⟪O -ᵥ D, v⟫ < 0`. Then `Wbtw A D U` and `Wbtw C D W` follow (see step 1
of the plan below), and the chase
`BA + AD = BT₁ - DW = BT₂ - DW = CB + CD` finishes external Pitot.

### Formalization choices

- Works over an arbitrary 2-dimensional real inner product space, in the
  style of the other geometry problems in this repository
  (e.g. `Imo2025P2.lean`, `Imo2023P2.lean`).
- "ABCD is a convex quadrilateral" (vertices in this cyclic order) is
  expressed by `ConvexQuadrilateral A B C D`: the four consecutive edge
  cross products `areaForm (B -ᵥ A) (C -ᵥ B)`, `areaForm (C -ᵥ B) (D -ᵥ C)`,
  `areaForm (D -ᵥ C) (A -ᵥ D)`, `areaForm (A -ᵥ D) (B -ᵥ A)` all have the
  same strict sign. This is equivalent to each side's line having the
  other two vertices strictly on the same side, and to the diagonals
  crossing internally. It uses an arbitrary but fixed orientation
  (`planeOrientation`); sidedness arguments then become sign computations
  with `Orientation.areaForm` instead of `SSameSide`/`SOppSide` API
  wrangling. (A bridge lemma `ConvexQuadrilateral → SSameSide`-style
  facts can be added later if wanted for faithfulness.)
- The incircles are mathlib's `Affine.Simplex.insphere` of the two
  triangles.
- "ω tangent to ray BA beyond A" is expressed as: the tangency point `T`
  satisfies `[B, A, T].Sbtw ℝ` (i.e. `A` is strictly between `B` and `T`)
  and `ω.IsTangentAt T line[ℝ, B, A]`. Similarly for ray BC beyond C.
  Tangency to lines AD and CD is `Sphere.IsTangent`.
- The conclusion: there is a point `K` on ω lying on two distinct common
  external tangent lines of ω1 and ω2 (i.e. the two external tangents
  intersect at a point of ω). `CommonExternalTangent` requires the
  subspace to be a genuine line (`finrank ℝ ℓ.direction = 1`) so that the
  statement cannot be satisfied by degenerate subspaces.

### The mathematics to formalize (verified numerically on a concrete
### configuration: A=(4,0), B=(0,0), C=(0,6), ω with center (9,9) radius 9,
### D=(36/23, 90/23); all claims below were checked numerically.
### STEPS 1–2 DONE as `external_pitot` and `dist_touchpoint_eq`;
### steps 3–6 done too, see the route spec above.)

Let `P` = touchpoint of ω1 with `AC`, `T` = touchpoint of ω2 with `AC`,
`Q` = antipode of `P` in ω1, `S` = antipode of `T` in ω2, `O` = ω.center,
`R` = ω.radius, and `n̂` = unit normal to `AC` pointing away from `B`
(i.e. from `O1` towards `AC`, computable as `(P -ᵥ O1)/r1`).

1. **External Pitot**: `BA + AD = CB + CD`. Tangent equalities
   (`dist_eq_dist_of_isTangentAt` / mathlib's
   `IsTangentAt.dist_eq_of_mem_of_mem`): `BT₁ = BT₂`, `AT₁ = AU`,
   `CT₂ = CW`, `DU = DW` where `T₁, T₂` are the tangency points on the
   rays and `U, W` those on lines `AD, CD`.
   - **Sign correction vs. earlier note**: `U` lies on ray `AD` *beyond D*
     and `W` on ray `CD` *beyond D* (verified; they are generally NOT on
     the segments `AD`, `CD`). The position is forced by the wedge
     analysis at `D`: `O` is on the opposite side of line `AD` from `C`
     and on the opposite side of line `CD` from `A`, which together with
     `dist(O, line AD) = dist(O, line CD) = R` gives
     `⟪O -ᵥ D, D -ᵥ A⟫ > 0` and `⟪O -ᵥ D, D -ᵥ C⟫ > 0` (the proof is a
     2D linear algebra computation: decompose `O -ᵥ D = α(A -ᵥ D) +
     β(C -ᵥ D)` in the basis `{A -ᵥ D, C -ᵥ D}`; the side conditions give
     `α, β < 0`, the equidistance gives `|α| = R/h_A`, `|β| = R/h_C`
     with `h_A = dist(A, line DC)`, `h_C = dist(C, line DA)`; then
     `⟪O -ᵥ D, D -ᵥ A⟫ = (R·|A-D|/|ω(u,v)|)·(|u||v| + ⟪u,v⟫) > 0` since
     `|⟪u,v⟫| < |u||v|` for independent `u = A -ᵥ D`, `v = C -ᵥ D` —
     strict Cauchy–Schwarz, equivalently `ω(u,v) ≠ 0` via the Lagrange
     identity `ω(u,v)² + ⟪u,v⟫² = |u|²|v|²`, mathlib:
     `Orientation.inner_mul_inner_add_areaForm_mul_areaForm`).
   - The side facts come from chord-radius positivity
     (`IsTangentAt.inner_vsub_center_pos`): `O` and `T₁` are strictly on
     the same side of line `AD` (`T₁ ∈ ω`, `T₁ ≠ U`), and `T₁` (beyond
     `A` on ray `BA`) is on the opposite side of `AD` from `B`, while
     `B, C` are on the same side of `AD` (from `ConvexQuadrilateral`).
   - The chase: `BT₁ = BA + AT₁`, `BT₂ = BC + CT₂` (from the `Sbtw`
     hypotheses via `Sbtw.wbtw` + `Wbtw.dist_add_dist`), `AU = AD + DU`,
     `CW = CD + DW` (from the beyond-`D` positions), so
     `BA + AD = BT₁ - DW = BT₂ - DW = CB + CD`. ∎
2. **Touchpoint reflection**: `AP = CT`, i.e. `P` and `T` are reflections
   about the midpoint of `AC`. Immediate from step 1:
   `AP = (AB + AC - BC)/2` (`dist_touchpoint_insphere_left`) and
   `CT = (CD + CA - AD)/2` (`dist_touchpoint_insphere_right` applied to
   triangle `ADC`), equal iff `BA + AD = CB + CD`. ∎
3. **Classical collinearity**: `B, Q, T` are collinear and `D, S, P` are
   collinear (both verified). Reason: `T` is also the touchpoint of the
   `B`-excircle of `△ABC` with `AC` (its distance from `C` is
   `s - AB = (BC + CA - AB)/2 = CT` by step 2); the homothety at `B`
   mapping the incircle ω1 to the `B`-excircle (mathlib `Simplex.exsphere`
   / `excenter`) sends `Q` to `T` since the tangent of ω1 at `Q` is
   parallel to `AC` and maps to the tangent of the excircle parallel to
   `AC` on the same side from `B`, which is `AC` itself. Formalizing this
   needs: homothety action on spheres (`AffineMap.homothety`), tangency
   preservation, and the B-excircle's touchpoint formula (another tangent
   chase, mirroring `dist_touchpoint_insphere_*` for
   `s.exsphere {i}`; mathlib has `ExcenterExists.isTangentAt_touchpoint`).
4. **K and the two homotheties**: let `K := O -ᵥ R • n̂` (the point of ω
   whose tangent is parallel to `AC`, on the `B`-side extreme). The
   homothety at `B` mapping ω1 ↦ ω (exists: both circles tangent to lines
   `BA`, `BC`, centers on the same bisector ray from `B` — sides from
   chord-radius positivity) has *positive* ratio and sends `Q ↦ K`
   (tangent at `Q` is `∥ AC` with ω1 on the `+n̂` side; positive
   homothety preserves the side, so the image tangent is the `∥ AC`
   tangent of ω with ω on the `+n̂` side, i.e. the one at `K`). Hence
   `B, Q, K` collinear; with step 3, `K ∈ line QT`. Similarly the
   homothety at `D` mapping ω2 ↦ ω has *negative* ratio (centers on the
   same bisector *line* at `D` but opposite rays: the wedge analysis of
   step 1 gives `O -ᵥ D = -(R/r2)(O2 -ᵥ D)` directly from the basis
   computation, since `O2 -ᵥ D` has `α₂, β₂ > 0` by
   `Simplex.sSameSide_incenter_point`) and sends `S ↦ K` (negative ratio
   flips the side). Hence `D, S, K` collinear; with step 3,
   `K ∈ line PS`.
5. **K is the exsimilicenter**: `O1Q = Q -ᵥ O1 = -r1 • n̂` and
   `O2T = T -ᵥ O2 = -r2 • n̂` are parallel same-direction radii, so line
   `QT` passes through the exsimilicenter `E` of ω1, ω2; similarly
   `O1P ∥ O2S` (direction `+n̂`), so line `PS` passes through `E`. The
   two lines `QT` and `PS` are distinct (they meet only at `E`), and `K`
   lies on both (step 4), hence `K = E`. If `r1 = r2` the exsimilicenter
   is at infinity, `QT ∥ PS ∥ O1O2`, contradicting `K` on both — so the
   configuration forces `r1 ≠ r2` (this is where `BA ≠ BC` is expected to
   enter; possibly via `r1 = r2 → BA = BC` given step 1).
6. **External tangents through the exsimilicenter**: generic circle
   theory: for two circles with `r1 ≠ r2`, the two tangent lines from the
   exsimilicenter `E` to ω1 are also tangent to ω2, are distinct common
   external tangents, and pass through `E = K ∈ ω`. Needs: tangent lines
   from an exterior point (`E` exterior to both circles since
   `EO1 > r1`), tangency transport along the homothety at `E` (ratio
   `r2/r1` mapping ω1 ↦ ω2), and the side check that makes the tangents
   external (centers on the same side of each).

### Pitfalls / notes for the next session

- `FiniteDimensional.of_fact_finrank_eq_two` must be a local instance
  (done above) or many `finrank`/orthogonality lemmas won't fire.
- Inner product notation: bare `⟪x, y⟫` needs
  `open scoped RealInnerProductSpace` (done); `⟪x, y⟫_ℝ` would need
  `open scoped InnerProductSpace` instead — don't use both.
- `omit [Fact (finrank ℝ V = 2)] in` must precede docstrings (a docstring
  must be immediately followed by the declaration keyword).
- Name resolution pitfall: lemmas declared in this file as
  `Sphere.IsTangentAt.foo` inside `namespace Imo2008P6` can later be
  MIS-resolved to `EuclideanGeometry.Sphere.IsTangentAt.foo` (via
  `open EuclideanGeometry`) and fail with "unknown constant" — new
  tangent-related lemmas here are named `IsTangentAt.foo` (without the
  `Sphere.` prefix) and called explicitly as `IsTangentAt.foo h ...`
  (dot-notation `h.foo` does not work for them, since `h`'s type lives in
  `EuclideanGeometry.Sphere`). When calling mathlib's own
  `Sphere.IsTangentAt.*` lemmas inside this file, fully qualify them as
  `EuclideanGeometry.Sphere.IsTangentAt.*` (see
  `dist_point_touchpoint_empty_eq`).
- Useful mathlib finds: `Affine.Triangle.sbtw_touchpoint_empty`
  (touchpoints strictly inside sides), `isTangentAt_insphere_touchpoint`,
  `ExcenterExists.isTangentAt_touchpoint` (for excircles, step 3),
  `Simplex.sSameSide_incenter_point` (incenter strictly on the same side
  of each face's span as the opposite vertex — gives `O2`'s wedge at
  `D`), `Simplex.touchpointWeights` + `affineCombination_touchpointWeights`
  (barycentric coordinates of touchpoints), `Wbtw.dist_add_dist`,
  `Orientation.inner_mul_inner_add_areaForm_mul_areaForm` (Lagrange
  identity for strict Cauchy–Schwarz).
- `vsub_add_vsub_cancel a b c : (a -ᵥ b) + (b -ᵥ c) = a -ᵥ c` (mind the
  direction; `.symm` often needed).
-/
