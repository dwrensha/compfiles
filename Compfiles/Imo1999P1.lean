/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 1999, Problem 1

Determine all finite sets S of at least three points in the plane such that
for any two distinct points A and B in S, the perpendicular bisector of the
line segment AB is an axis of symmetry of S.

## Formalization notes

The answer: the vertex sets of the regular `n`-gons (`n ≥ 3`).

We work in `Pl := EuclideanSpace ℝ (Fin 2)`.  `reflect A B` below is the
reflection across the perpendicular bisector of the segment `AB`; the
hypothesis that this bisector is an axis of symmetry of `S` is formalized as
`∀ X ∈ S, reflect A B X ∈ S`.  (For a finite `S` this is equivalent to the
reflection mapping `S` onto itself, since the reflection is an involution.)

A finite set `S` is the vertex set of a regular `n`-gon iff there are a
center `c`, a radius `r > 0` and an initial angle `θ₀` such that
`S = {c + r • (cos (θ₀ + 2πk/n), sin (θ₀ + 2πk/n)) | k ∈ Fin n}`.

Solution outline: the centroid `G` of `S` is fixed by every such reflection
(being an affine invariant of `S`), so `G` lies on every perpendicular
bisector, hence all points of `S` lie on a circle around `G`.  In angular
coordinates around `G`, the reflection across the bisector of the points at
angles `α` and `β` acts by `θ ↦ α + β - θ`.  Applying this to three
consecutive angles `α < θ < β` forces `α + β - θ = θ`, so all gaps between
consecutive points are equal and `S` is a regular polygon.
-/

namespace Imo1999P1

open scoped RealInnerProductSpace

/-- The Euclidean plane. -/
abbrev Pl := EuclideanSpace ℝ (Fin 2)

/-- Reflection across the perpendicular bisector of the segment `AB`
(for `A ≠ B`): the mirror is the hyperplane `{X | ⟪X - (A + B)/2, B - A⟫ = 0}`,
i.e. the set of points equidistant from `A` and `B`. -/
noncomputable def reflect (A B X : Pl) : Pl :=
  X - (2 * inner ℝ (X - (2⁻¹ : ℝ) • (A + B)) (B - A) / inner ℝ (B - A) (B - A)) • (B - A)

/-- The answer to the problem: vertex sets of regular polygons with at least
three vertices. -/
noncomputable determine regularPolygonVertexSets : Set (Finset Pl) :=
  {S | ∃ n : ℕ, 3 ≤ n ∧ ∃ c : Pl, ∃ r : ℝ, 0 < r ∧ ∃ θ₀ : ℝ,
    S = (Finset.univ : Finset (Fin n)).image
      (fun k : Fin n => c + r • !₂[Real.cos (θ₀ + 2 * Real.pi * (k : ℝ) / (n : ℝ)),
                           Real.sin (θ₀ + 2 * Real.pi * (k : ℝ) / (n : ℝ))])}

snip begin

/-- The unit vector at angle `θ`. -/
noncomputable def unitVec (θ : ℝ) : Pl := !₂[Real.cos θ, Real.sin θ]

@[simp] lemma unitVec_zero (θ : ℝ) : unitVec θ 0 = Real.cos θ := rfl

@[simp] lemma unitVec_one (θ : ℝ) : unitVec θ 1 = Real.sin θ := rfl

lemma inner_unitVec_unitVec (θ : ℝ) : inner ℝ (unitVec θ) (unitVec θ) = 1 := by
  have h := Real.cos_sq_add_sin_sq θ
  rw [PiLp.inner_apply, Fin.sum_univ_two, unitVec_zero, unitVec_one]
  simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial]
  linear_combination h

/-- `unitVec` values are equal iff the angles differ by a multiple of `2π`. -/
lemma unitVec_eq {a b : ℝ} (h : unitVec a = unitVec b) :
    ∃ k : ℤ, a = b + 2 * Real.pi * k := by
  have hc : Real.cos a = Real.cos b := by
    have h1 := congrArg (fun v : Pl => v 0) h
    rwa [unitVec_zero, unitVec_zero] at h1
  have hs : Real.sin a = Real.sin b := by
    have h1 := congrArg (fun v : Pl => v 1) h
    rwa [unitVec_one, unitVec_one] at h1
  rcases Real.cos_eq_cos_iff.mp hc with ⟨k, hk | hk⟩
  · exact ⟨-k, by push_cast; linarith⟩
  · have h1 : Real.sin b = - Real.sin a := by
      rw [hk, show 2 * (k : ℝ) * Real.pi - a = -a + k * (2 * Real.pi) by ring,
        Real.sin_add_int_mul_two_pi, Real.sin_neg]
    have hsa : Real.sin a = 0 := by linarith
    rcases Real.sin_eq_zero_iff.mp hsa with ⟨m, hm⟩
    exact ⟨m - k, by push_cast; linarith⟩

lemma unitVec_periodic (φ : ℝ) (q : ℤ) :
    unitVec (φ + 2 * Real.pi * q) = unitVec φ := by
  have h1 : φ + 2 * Real.pi * (q : ℝ) = φ + (q : ℝ) * (2 * Real.pi) := by ring
  rw [h1]
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp [Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]

/-- The algebraic heart of the reflection: on angles, reflection across the
perpendicular bisector of the points at angles `α` and `β` acts by
`θ ↦ α + β - θ`.  After clearing the (nonzero) denominator this is a
polynomial identity modulo `cos² + sin² = 1` for `α` and `β`; the
`linear_combination` certificates were found by factoring the difference as
`(zβ - zα)·(zα·hβ - zβ·hα)` over the complexes. -/
lemma unitVec_reflect_aux (α β θ : ℝ)
    (hD : (Real.cos β - Real.cos α) ^ 2 + (Real.sin β - Real.sin α) ^ 2 ≠ 0) :
    unitVec (α + β - θ) =
      unitVec θ - (2 * (Real.cos θ * (Real.cos β - Real.cos α) +
          Real.sin θ * (Real.sin β - Real.sin α)) /
        ((Real.cos β - Real.cos α) ^ 2 + (Real.sin β - Real.sin α) ^ 2)) •
        (unitVec β - unitVec α) := by
  have hα := Real.cos_sq_add_sin_sq α
  have hβ := Real.cos_sq_add_sin_sq β
  apply PiLp.ext
  intro i
  fin_cases i
  · show Real.cos (α + β - θ) = Real.cos θ - (2 * (Real.cos θ * (Real.cos β - Real.cos α) +
        Real.sin θ * (Real.sin β - Real.sin α)) /
      ((Real.cos β - Real.cos α) ^ 2 + (Real.sin β - Real.sin α) ^ 2)) *
      (Real.cos β - Real.cos α)
    rw [Real.cos_sub, Real.cos_add, Real.sin_add]
    field_simp [hD]
    linear_combination
      (Real.cos θ * ((Real.cos α * Real.cos β - Real.sin α * Real.sin β) - Real.cos β ^ 2 +
          Real.sin β ^ 2) +
        Real.sin θ * ((Real.sin α * Real.cos β + Real.cos α * Real.sin β) -
          2 * Real.sin β * Real.cos β)) * hα +
      (Real.cos θ * ((Real.cos α * Real.cos β - Real.sin α * Real.sin β) - Real.cos α ^ 2 +
          Real.sin α ^ 2) +
        Real.sin θ * ((Real.sin α * Real.cos β + Real.cos α * Real.sin β) -
          2 * Real.sin α * Real.cos α)) * hβ
  · show Real.sin (α + β - θ) = Real.sin θ - (2 * (Real.cos θ * (Real.cos β - Real.cos α) +
        Real.sin θ * (Real.sin β - Real.sin α)) /
      ((Real.cos β - Real.cos α) ^ 2 + (Real.sin β - Real.sin α) ^ 2)) *
      (Real.sin β - Real.sin α)
    rw [Real.sin_sub, Real.sin_add, Real.cos_add]
    field_simp [hD]
    linear_combination
      (Real.cos θ * ((Real.sin α * Real.cos β + Real.cos α * Real.sin β) -
          2 * Real.sin β * Real.cos β) -
        Real.sin θ * ((Real.cos α * Real.cos β - Real.sin α * Real.sin β) - Real.cos β ^ 2 +
          Real.sin β ^ 2)) * hα +
      (Real.cos θ * ((Real.sin α * Real.cos β + Real.cos α * Real.sin β) -
          2 * Real.sin α * Real.cos α) -
        Real.sin θ * ((Real.cos α * Real.cos β - Real.sin α * Real.sin β) - Real.cos α ^ 2 +
          Real.sin α ^ 2)) * hβ

lemma inner_unitVec_sub_unitVec (θ α β : ℝ) :
    inner ℝ (unitVec θ) (unitVec β - unitVec α) =
      Real.cos θ * (Real.cos β - Real.cos α) + Real.sin θ * (Real.sin β - Real.sin α) := by
  rw [inner_sub_right, PiLp.inner_apply, PiLp.inner_apply, Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [unitVec_zero, unitVec_one, RCLike.inner_apply, starRingEnd_apply, star_trivial]
  ring

lemma inner_unitVec_sub_self (α β : ℝ) :
    inner ℝ (unitVec β - unitVec α) (unitVec β - unitVec α) =
      (Real.cos β - Real.cos α) ^ 2 + (Real.sin β - Real.sin α) ^ 2 := by
  rw [PiLp.inner_apply, Fin.sum_univ_two]
  show inner ℝ (Real.cos β - Real.cos α) (Real.cos β - Real.cos α) +
    inner ℝ (Real.sin β - Real.sin α) (Real.sin β - Real.sin α) = _
  simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial]
  ring

/-- Reflection across the perpendicular bisector of two points on the circle
of radius `r` around `G`, expressed in angular coordinates. -/
lemma reflect_eq_of_on_circle {G A B X : Pl} {r : ℝ} (hr : r ≠ 0)
    {α β θ : ℝ} (hA : A = G + r • unitVec α) (hB : B = G + r • unitVec β)
    (hX : X = G + r • unitVec θ)
    (hD : inner ℝ (unitVec β - unitVec α) (unitVec β - unitVec α) ≠ 0) :
    reflect A B X = G + r • unitVec (α + β - θ) := by
  have hv : B - A = r • (unitVec β - unitVec α) := by rw [hB, hA]; module
  have hM : X - (2⁻¹ : ℝ) • (A + B) =
      r • (unitVec θ - (2⁻¹ : ℝ) • (unitVec α + unitVec β)) := by
    rw [hX, hA, hB]; module
  have hz : inner ℝ (unitVec α + unitVec β) (unitVec β - unitVec α) = 0 := by
    rw [inner_add_left, inner_sub_right, inner_sub_right, inner_unitVec_unitVec,
      inner_unitVec_unitVec, real_inner_comm (unitVec α) (unitVec β)]
    ring
  have hsc1 : inner ℝ (X - (2⁻¹ : ℝ) • (A + B)) (B - A) =
      r * r * inner ℝ (unitVec θ) (unitVec β - unitVec α) := by
    rw [hM, hv, inner_smul_left, inner_smul_right]
    simp only [starRingEnd_apply, star_trivial]
    rw [inner_sub_left, inner_smul_left, hz]
    simp only [starRingEnd_apply, star_trivial, mul_zero, sub_zero]
    ring
  have hsc2 : inner ℝ (B - A) (B - A) =
      r * r * inner ℝ (unitVec β - unitVec α) (unitVec β - unitVec α) := by
    rw [hv, inner_smul_left, inner_smul_right]
    simp only [starRingEnd_apply, star_trivial]
    ring
  have hrr : r * r ≠ 0 := mul_ne_zero hr hr
  have hsc3 : 2 * (r * r * inner ℝ (unitVec θ) (unitVec β - unitVec α)) /
      (r * r * inner ℝ (unitVec β - unitVec α) (unitVec β - unitVec α)) =
      2 * inner ℝ (unitVec θ) (unitVec β - unitVec α) /
        inner ℝ (unitVec β - unitVec α) (unitVec β - unitVec α) := by
    field_simp [hrr, hD]
  have hD' : (Real.cos β - Real.cos α) ^ 2 + (Real.sin β - Real.sin α) ^ 2 ≠ 0 := by
    rwa [← inner_unitVec_sub_self]
  have main : reflect A B X = G + r • (unitVec θ -
      (2 * inner ℝ (unitVec θ) (unitVec β - unitVec α) /
        inner ℝ (unitVec β - unitVec α) (unitVec β - unitVec α)) •
        (unitVec β - unitVec α)) := by
    rw [reflect, hsc1, hsc2, hsc3, hv, hX]
    module
  rw [main, inner_unitVec_sub_unitVec, inner_unitVec_sub_self,
    ← unitVec_reflect_aux α β θ hD']

/-- The linear part of `reflect A B`. -/
noncomputable def reflectLin (A B : Pl) (w : Pl) : Pl :=
  w - (2 * inner ℝ w (B - A) / inner ℝ (B - A) (B - A)) • (B - A)

lemma reflectLin_sub (A B X Y : Pl) :
    reflect A B X - reflect A B Y = reflectLin A B (X - Y) := by
  have e : X - (2⁻¹ : ℝ) • (A + B) - (Y - (2⁻¹ : ℝ) • (A + B)) = X - Y := by module
  have sc : 2 * inner ℝ (X - (2⁻¹ : ℝ) • (A + B)) (B - A) / inner ℝ (B - A) (B - A) -
      2 * inner ℝ (Y - (2⁻¹ : ℝ) • (A + B)) (B - A) / inner ℝ (B - A) (B - A) =
      2 * inner ℝ (X - Y) (B - A) / inner ℝ (B - A) (B - A) := by
    have h1 : 2 * inner ℝ (X - (2⁻¹ : ℝ) • (A + B)) (B - A) / inner ℝ (B - A) (B - A) -
        2 * inner ℝ (Y - (2⁻¹ : ℝ) • (A + B)) (B - A) / inner ℝ (B - A) (B - A) =
        2 * (inner ℝ (X - (2⁻¹ : ℝ) • (A + B)) (B - A) -
          inner ℝ (Y - (2⁻¹ : ℝ) • (A + B)) (B - A)) / inner ℝ (B - A) (B - A) := by ring
    rw [h1, ← inner_sub_left, e]
  rw [reflect, reflect, reflectLin, ← sc]
  module

lemma reflectLin_zero (A B : Pl) : reflectLin A B 0 = 0 := by
  simp [reflectLin, inner_zero_left]

lemma reflectLin_add (A B : Pl) (w₁ w₂ : Pl) :
    reflectLin A B (w₁ + w₂) = reflectLin A B w₁ + reflectLin A B w₂ := by
  rw [reflectLin, reflectLin, reflectLin, inner_add_left]
  module

lemma reflectLin_sum (A B : Pl) (S : Finset Pl) (f : Pl → Pl) :
    reflectLin A B (∑ X ∈ S, f X) = ∑ X ∈ S, reflectLin A B (f X) := by
  classical
  induction S using Finset.induction with
  | empty => simp [reflectLin_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, reflectLin_add, ih]

lemma inner_BA_ne_zero {A B : Pl} (hAB : A ≠ B) : inner ℝ (B - A) (B - A) ≠ 0 :=
  inner_self_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm hAB))

lemma reflect_left {A B : Pl} (hAB : A ≠ B) : reflect A B A = B := by
  have hD := inner_BA_ne_zero hAB
  have e1 : A - (2⁻¹ : ℝ) • (A + B) = (-(2⁻¹ : ℝ)) • (B - A) := by module
  have sc : 2 * inner ℝ (A - (2⁻¹ : ℝ) • (A + B)) (B - A) / inner ℝ (B - A) (B - A) = -1 := by
    rw [e1, inner_smul_left]
    simp only [starRingEnd_apply, star_trivial]
    field_simp [hD]
  rw [reflect, sc]
  module

lemma reflect_right {A B : Pl} (hAB : A ≠ B) : reflect A B B = A := by
  have hD := inner_BA_ne_zero hAB
  have e1 : B - (2⁻¹ : ℝ) • (A + B) = (2⁻¹ : ℝ) • (B - A) := by module
  have sc : 2 * inner ℝ (B - (2⁻¹ : ℝ) • (A + B)) (B - A) / inner ℝ (B - A) (B - A) = 1 := by
    rw [e1, inner_smul_left]
    simp only [starRingEnd_apply, star_trivial]
    field_simp [hD]
  rw [reflect, sc]
  module

lemma reflect_involutive {A B : Pl} (hAB : A ≠ B) : Function.Involutive (reflect A B) := by
  intro X
  have hD := inner_BA_ne_zero hAB
  have e2 : inner ℝ (reflect A B X - (2⁻¹ : ℝ) • (A + B)) (B - A) =
      - inner ℝ (X - (2⁻¹ : ℝ) • (A + B)) (B - A) := by
    have e1 : reflect A B X - (2⁻¹ : ℝ) • (A + B) =
        (X - (2⁻¹ : ℝ) • (A + B)) -
          (2 * inner ℝ (X - (2⁻¹ : ℝ) • (A + B)) (B - A) / inner ℝ (B - A) (B - A)) • (B - A) := by
      rw [reflect]; module
    rw [e1, inner_sub_left, inner_smul_left]
    simp only [starRingEnd_apply, star_trivial]
    field_simp [hD]
    ring
  rw [reflect, e2, reflect]
  module

lemma reflectLin_norm {A B : Pl} (hAB : A ≠ B) (w : Pl) :
    ‖reflectLin A B w‖ = ‖w‖ := by
  have hD := inner_BA_ne_zero hAB
  have hsq : ‖reflectLin A B w‖ ^ 2 = ‖w‖ ^ 2 := by
    have hD2 : inner ℝ B B - inner ℝ A B - (inner ℝ A B - inner ℝ A A) ≠ 0 := by
      have e : inner ℝ (B - A) (B - A) =
          inner ℝ B B - inner ℝ A B - (inner ℝ A B - inner ℝ A A) := by
        simp only [inner_sub_left, inner_sub_right, real_inner_comm A B]
      rwa [← e]
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
    simp only [reflectLin, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      starRingEnd_apply, star_trivial]
    rw [real_inner_comm A B, real_inner_comm w A, real_inner_comm w B]
    field_simp [hD2]
    ring
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

lemma reflect_dist {A B : Pl} (hAB : A ≠ B) (X Y : Pl) :
    dist (reflect A B X) (reflect A B Y) = dist X Y := by
  rw [dist_eq_norm, dist_eq_norm, reflectLin_sub, reflectLin_norm hAB]

/-- The centroid of `S` is fixed by every bisector reflection, since the
reflection permutes `S` and is affine. -/
lemma reflect_center {S : Finset Pl}
    (hS : ∀ A ∈ S, ∀ B ∈ S, A ≠ B → ∀ X ∈ S, reflect A B X ∈ S)
    {A B : Pl} (hA : A ∈ S) (hB : B ∈ S) (hAB : A ≠ B) (hn : (S.card : ℝ) ≠ 0) :
    reflect A B ((S.card : ℝ)⁻¹ • ∑ X ∈ S, X) = (S.card : ℝ)⁻¹ • ∑ X ∈ S, X := by
  classical
  have hinj : Function.Injective (reflect A B) := (reflect_involutive hAB).injective
  have hcl : ∀ X ∈ S, reflect A B X ∈ S := hS A hA B hB hAB
  have himg : S.image (reflect A B) = S := by
    apply Finset.eq_of_subset_of_card_le
    · intro Y hY
      rcases Finset.mem_image.mp hY with ⟨X, hX, rfl⟩
      exact hcl X hX
    · rw [Finset.card_image_of_injective S hinj]
  have hsum : ∑ X ∈ S, reflect A B X = ∑ X ∈ S, X := by
    have h1 : ∑ X ∈ S.image (reflect A B), X = ∑ X ∈ S, X := by rw [himg]
    rw [Finset.sum_image hinj.injOn] at h1
    exact h1
  have hG : ∑ X ∈ S, (X - (S.card : ℝ)⁻¹ • ∑ Y ∈ S, Y) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ,
      smul_inv_smul₀ hn, sub_self]
  have key : ∑ X ∈ S, (reflect A B X - reflect A B ((S.card : ℝ)⁻¹ • ∑ Y ∈ S, Y)) = 0 := by
    have e : ∀ X ∈ S, reflect A B X - reflect A B ((S.card : ℝ)⁻¹ • ∑ Y ∈ S, Y) =
        reflectLin A B (X - (S.card : ℝ)⁻¹ • ∑ Y ∈ S, Y) := fun X _ => reflectLin_sub A B X _
    rw [Finset.sum_congr rfl e, ← reflectLin_sum, hG, reflectLin_zero]
  rw [Finset.sum_sub_distrib, hsum, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ,
    sub_eq_zero] at key
  calc reflect A B ((S.card : ℝ)⁻¹ • ∑ X ∈ S, X)
      = (S.card : ℝ)⁻¹ • ((S.card : ℝ) • reflect A B ((S.card : ℝ)⁻¹ • ∑ X ∈ S, X)) :=
        (inv_smul_smul₀ hn _).symm
    _ = (S.card : ℝ)⁻¹ • ∑ X ∈ S, X := by rw [← key]

/-- Hence the centroid is equidistant from all points of `S`. -/
lemma dist_center_eq {S : Finset Pl}
    (hS : ∀ A ∈ S, ∀ B ∈ S, A ≠ B → ∀ X ∈ S, reflect A B X ∈ S)
    {A B : Pl} (hA : A ∈ S) (hB : B ∈ S) (hn : (S.card : ℝ) ≠ 0) :
    dist ((S.card : ℝ)⁻¹ • ∑ Y ∈ S, Y) A = dist ((S.card : ℝ)⁻¹ • ∑ Y ∈ S, Y) B := by
  rcases eq_or_ne A B with rfl | hAB
  · rfl
  · have h1 := reflect_dist hAB ((S.card : ℝ)⁻¹ • ∑ Y ∈ S, Y) A
    rw [reflect_center hS hA hB hAB hn, reflect_left hAB] at h1
    exact h1.symm

/-- Parametrization of the unit circle by angle. -/
lemma exists_angle (v : Pl) (hv : ‖v‖ = 1) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ < 2 * Real.pi ∧ v = unitVec θ := by
  have hvv : v = !₂[v 0, v 1] := by
    apply PiLp.ext
    intro i
    fin_cases i <;> rfl
  have hnorm : v 0 ^ 2 + v 1 ^ 2 = 1 := by
    have h1 : (1 : ℝ) = ‖v‖ ^ 2 := by rw [hv]; norm_num
    rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply, Fin.sum_univ_two] at h1
    have h2 : ∀ a : ℝ, inner ℝ a a = a ^ 2 := fun a => by
      simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial]; ring
    rw [h2, h2] at h1
    rw [← h1]
  have hx0 : -1 ≤ v 0 ∧ v 0 ≤ 1 := by
    constructor <;> nlinarith [sq_nonneg (v 1), hnorm]
  rcases le_or_gt 0 (v 1) with hy | hy
  · refine ⟨Real.arccos (v 0), Real.arccos_nonneg _, ?_, ?_⟩
    · exact lt_of_le_of_lt (Real.arccos_le_pi _) (by linarith [Real.pi_pos])
    · rw [hvv]
      apply PiLp.ext
      intro i
      fin_cases i
      · show v 0 = Real.cos (Real.arccos (v 0))
        exact (Real.cos_arccos hx0.1 hx0.2).symm
      · show v 1 = Real.sin (Real.arccos (v 0))
        rw [Real.sin_arccos]
        have h1 : v 1 = √(v 1 ^ 2) := by rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hy]
        rw [h1]
        congr 1
        linarith [hnorm]
  · have hpos : 0 < Real.arccos (v 0) := by
      rw [Real.arccos_pos]
      by_contra h
      push Not at h
      have hv0 : v 0 = 1 := le_antisymm hx0.2 h
      have hv1 : v 1 = 0 := by
        have h2 : v 1 ^ 2 = 0 := by nlinarith [hnorm]
        exact sq_eq_zero_iff.mp h2
      linarith [hy]
    refine ⟨2 * Real.pi - Real.arccos (v 0), ?_, ?_, ?_⟩
    · have h1 : Real.arccos (v 0) ≤ Real.pi := Real.arccos_le_pi _
      linarith [Real.pi_pos]
    · linarith [Real.pi_pos]
    · rw [hvv]
      apply PiLp.ext
      intro i
      fin_cases i
      · show v 0 = Real.cos (2 * Real.pi - Real.arccos (v 0))
        rw [Real.cos_two_pi_sub]
        exact (Real.cos_arccos hx0.1 hx0.2).symm
      · show v 1 = Real.sin (2 * Real.pi - Real.arccos (v 0))
        rw [Real.sin_two_pi_sub, Real.sin_arccos]
        have h1 : v 1 = -√(v 1 ^ 2) := by rw [Real.sqrt_sq_eq_abs, abs_of_neg hy, neg_neg]
        rw [h1]
        congr 2
        linarith [hnorm]

/-- The index in `Fin n` corresponding to `i : ℤ` in the periodic
enumeration. -/
noncomputable def periodicIdx {n : ℕ} (hn : 0 < n) (i : ℤ) : Fin n :=
  ⟨(i % (n : ℤ)).toNat, (Int.toNat_lt (Int.emod_nonneg i (by exact_mod_cast hn.ne'))).mpr
    (Int.emod_lt_of_pos i (by exact_mod_cast hn))⟩

/-- The bi-infinite enumeration of the values `g : Fin n → ℝ` (thought of as
the sorted angles in `[0, 2π)` of the points), continued `2π`-periodically:
`f (i + n) = f i + 2π`. -/
noncomputable def periodicEnum {n : ℕ} (hn : 0 < n) (g : Fin n → ℝ) (i : ℤ) : ℝ :=
  g (periodicIdx hn i) + 2 * Real.pi * ((i / (n : ℤ) : ℤ) : ℝ)

lemma periodicIdx_congr {n : ℕ} (hn : 0 < n) {i j : ℤ} (h : i % (n : ℤ) = j % (n : ℤ)) :
    periodicIdx hn i = periodicIdx hn j := by
  apply Fin.ext
  show (i % (n : ℤ)).toNat = (j % (n : ℤ)).toNat
  rw [h]

lemma periodicIdx_apply_coe {n : ℕ} (hn : 0 < n) (k : Fin n) :
    periodicIdx hn ((k : ℕ) : ℤ) = k := by
  apply Fin.ext
  show (((k : ℕ) : ℤ) % (n : ℤ)).toNat = (k : ℕ)
  rw [Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast k.2), Int.toNat_natCast]

lemma periodicEnum_add_n {n : ℕ} (hn : 0 < n) (g : Fin n → ℝ) (i : ℤ) :
    periodicEnum hn g (i + (n : ℤ)) = periodicEnum hn g i + 2 * Real.pi := by
  have hnZ : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  have e1 : (i + (n : ℤ)) % (n : ℤ) = i % (n : ℤ) := by
    conv_lhs => rw [show i + (n : ℤ) = i + (n : ℤ) * 1 from by ring]
    exact Int.add_mul_emod_self_left _ _ _
  have e2 : (i + (n : ℤ)) / (n : ℤ) = i / (n : ℤ) + 1 := by
    conv_lhs => rw [show i + (n : ℤ) = i + 1 * (n : ℤ) from by ring]
    exact Int.add_mul_ediv_right _ _ hnZ
  show g (periodicIdx hn (i + (n : ℤ))) + 2 * Real.pi * (((i + (n : ℤ)) / (n : ℤ) : ℤ) : ℝ) =
    g (periodicIdx hn i) + 2 * Real.pi * ((i / (n : ℤ) : ℤ) : ℝ) + 2 * Real.pi
  rw [e2, periodicIdx_congr hn e1]
  push_cast
  ring

lemma periodicEnum_strictMono {n : ℕ} (hn : 0 < n) {g : Fin n → ℝ}
    (hg : StrictMono g) (hb : ∀ k, 0 ≤ g k ∧ g k < 2 * Real.pi) :
    StrictMono (periodicEnum hn g) := by
  intro i j hij
  have hnZpos : (0 : ℤ) < n := by exact_mod_cast hn
  have hdiv : i / (n : ℤ) ≤ j / (n : ℤ) := Int.ediv_le_ediv hnZpos (le_of_lt hij)
  rcases eq_or_lt_of_le hdiv with h | h
  · -- same integer part: compare the remainders
    have hrem : i % (n : ℤ) < j % (n : ℤ) := by
      have hi2 := Int.emod_def i (n : ℤ)
      have hj2 := Int.emod_def j (n : ℤ)
      rw [← h] at hj2
      linarith [hij]
    have hrem' : (i % (n : ℤ)).toNat < (j % (n : ℤ)).toNat := by
      have h1 : (((i % (n : ℤ)).toNat : ℕ) : ℤ) = i % (n : ℤ) :=
        Int.toNat_of_nonneg (Int.emod_nonneg i (by exact_mod_cast hn.ne'))
      have h2 : (((j % (n : ℤ)).toNat : ℕ) : ℤ) = j % (n : ℤ) :=
        Int.toNat_of_nonneg (Int.emod_nonneg j (by exact_mod_cast hn.ne'))
      omega
    have h3 : g (periodicIdx hn i) < g (periodicIdx hn j) := by
      apply hg
      unfold periodicIdx
      exact Fin.mk_lt_mk.mpr hrem'
    have h4 : ((i / (n : ℤ) : ℤ) : ℝ) = ((j / (n : ℤ) : ℤ) : ℝ) := by rw [h]
    show g (periodicIdx hn i) + 2 * Real.pi * ((i / (n : ℤ) : ℤ) : ℝ) <
      g (periodicIdx hn j) + 2 * Real.pi * ((j / (n : ℤ) : ℤ) : ℝ)
    rw [h4]
    linarith [h3]
  · have h1 := hb (periodicIdx hn i)
    have h2 := hb (periodicIdx hn j)
    have h3 : ((i / (n : ℤ) : ℤ) : ℝ) + 1 ≤ ((j / (n : ℤ) : ℤ) : ℝ) := by
      have h4 : (i / (n : ℤ)) + 1 ≤ j / (n : ℤ) := h
      exact_mod_cast h4
    have e1 : periodicEnum hn g i < 2 * Real.pi * (((i / (n : ℤ) : ℤ) : ℝ) + 1) := by
      show g (periodicIdx hn i) + 2 * Real.pi * ((i / (n : ℤ) : ℤ) : ℝ) <
        2 * Real.pi * (((i / (n : ℤ) : ℤ) : ℝ) + 1)
      linarith [h1.2, Real.pi_pos]
    have e2 : 2 * Real.pi * (((i / (n : ℤ) : ℤ) : ℝ) + 1) ≤
        2 * Real.pi * ((j / (n : ℤ) : ℤ) : ℝ) :=
      mul_le_mul_of_nonneg_left h3 (le_of_lt (mul_pos zero_lt_two Real.pi_pos))
    have e3 : 2 * Real.pi * ((j / (n : ℤ) : ℤ) : ℝ) ≤ periodicEnum hn g j := by
      show 2 * Real.pi * ((j / (n : ℤ) : ℤ) : ℝ) ≤
        g (periodicIdx hn j) + 2 * Real.pi * ((j / (n : ℤ) : ℤ) : ℝ)
      linarith [h2.1, Real.pi_pos]
    exact e1.trans_le (e2.trans e3)

/-- The combinatorial core: for a finite set of angles in `[0, 2π)` closed
under all reflections `θ ↦ α + β - θ (mod 2π)` (with `α ≠ β`), consecutive
gaps of the lifted enumeration are all equal. -/
lemma periodicEnum_gap {n : ℕ} (hn : 0 < n) {g : Fin n → ℝ}
    (hg : StrictMono g) (hb : ∀ k, 0 ≤ g k ∧ g k < 2 * Real.pi)
    (hcl : ∀ a b c : Fin n, a ≠ b →
      ∃ d : Fin n, ∃ q : ℤ, g d = g a + g b - g c + 2 * Real.pi * q)
    (hn3 : 3 ≤ n) (i : ℤ) :
    periodicEnum hn g (i + 1) - periodicEnum hn g i =
      periodicEnum hn g i - periodicEnum hn g (i - 1) := by
  have hnZ : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  have hmono := periodicEnum_strictMono hn hg hb
  have hne : (i - 1) % (n : ℤ) ≠ (i + 1) % (n : ℤ) := by
    intro h
    have h2 : ((i - 1) - (i + 1)) % (n : ℤ) = 0 := Int.emod_eq_emod_iff_emod_sub_eq_zero.mp h
    have h3 : (-2 : ℤ) % (n : ℤ) = 0 := by
      have e : (i - 1) - (i + 1) = -2 := by ring
      rwa [e] at h2
    have h4 : (n : ℤ) ∣ 2 := dvd_neg.mp (Int.dvd_of_emod_eq_zero h3)
    have h5 : (n : ℤ) ≤ 2 := Int.le_of_dvd (by norm_num) h4
    have h6 : (3 : ℤ) ≤ n := by exact_mod_cast hn3
    linarith
  have hlift : ∃ p : ℤ, periodicEnum hn g p =
      periodicEnum hn g (i - 1) + periodicEnum hn g (i + 1) - periodicEnum hn g i := by
    have hab : periodicIdx hn (i - 1) ≠ periodicIdx hn (i + 1) := by
      intro h
      apply hne
      have h3 := congrArg Fin.val h
      have h4 : (((i - 1) % (n : ℤ)).toNat : ℤ) = (i - 1) % (n : ℤ) :=
        Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hn.ne'))
      have h5 : (((i + 1) % (n : ℤ)).toNat : ℤ) = (i + 1) % (n : ℤ) :=
        Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hn.ne'))
      have h6 : ((i - 1) % (n : ℤ)).toNat = ((i + 1) % (n : ℤ)).toNat := h3
      omega
    rcases hcl (periodicIdx hn (i - 1)) (periodicIdx hn (i + 1)) (periodicIdx hn i) hab
      with ⟨d, q, hq⟩
    refine ⟨((d : ℕ) : ℤ) + ((i - 1) / (n : ℤ) + (i + 1) / (n : ℤ) - i / (n : ℤ) - q) * (n : ℤ), ?_⟩
    have hp_emod : (((d : ℕ) : ℤ) +
        ((i - 1) / (n : ℤ) + (i + 1) / (n : ℤ) - i / (n : ℤ) - q) * (n : ℤ)) % (n : ℤ) =
        ((d : ℕ) : ℤ) := by
      rw [mul_comm _ (n : ℤ), Int.add_mul_emod_self_left]
      exact Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast d.2)
    have hp_ediv : (((d : ℕ) : ℤ) +
        ((i - 1) / (n : ℤ) + (i + 1) / (n : ℤ) - i / (n : ℤ) - q) * (n : ℤ)) / (n : ℤ) =
        (i - 1) / (n : ℤ) + (i + 1) / (n : ℤ) - i / (n : ℤ) - q := by
      rw [Int.add_mul_ediv_right _ _ hnZ,
        Int.ediv_eq_zero_of_lt (Int.natCast_nonneg _) (by exact_mod_cast d.2)]
      ring
    have hp_idx : periodicIdx hn (((d : ℕ) : ℤ) +
        ((i - 1) / (n : ℤ) + (i + 1) / (n : ℤ) - i / (n : ℤ) - q) * (n : ℤ)) = d := by
      apply Fin.ext
      show ((((d : ℕ) : ℤ) +
          ((i - 1) / (n : ℤ) + (i + 1) / (n : ℤ) - i / (n : ℤ) - q) * (n : ℤ)) % (n : ℤ)).toNat =
          (d : ℕ)
      rw [hp_emod, Int.toNat_natCast]
    show g (periodicIdx hn _) + 2 * Real.pi * ((_ / (n : ℤ) : ℤ) : ℝ) =
      (g (periodicIdx hn (i - 1)) + 2 * Real.pi * (((i - 1) / (n : ℤ) : ℤ) : ℝ)) +
      (g (periodicIdx hn (i + 1)) + 2 * Real.pi * (((i + 1) / (n : ℤ) : ℤ) : ℝ)) -
      (g (periodicIdx hn i) + 2 * Real.pi * ((i / (n : ℤ) : ℤ) : ℝ))
    rw [hp_idx, hp_ediv, hq]
    push_cast
    ring
  rcases hlift with ⟨p, hp⟩
  have hlt1 : periodicEnum hn g (i - 1) < periodicEnum hn g p := by
    rw [hp]
    have h1 : periodicEnum hn g i < periodicEnum hn g (i + 1) := hmono (by linarith)
    linarith
  have hlt2 : periodicEnum hn g p < periodicEnum hn g (i + 1) := by
    rw [hp]
    have h1 : periodicEnum hn g (i - 1) < periodicEnum hn g i := hmono (by linarith)
    linarith
  have hp_eq : p = i := by
    have h1 := hmono.lt_iff_lt.mp hlt1
    have h2 := hmono.lt_iff_lt.mp hlt2
    omega
  rw [hp_eq] at hp
  linarith [hp]

/-- All values of the enumeration are affine in the index. -/
lemma periodicEnum_affine {n : ℕ} (hn : 0 < n) {g : Fin n → ℝ}
    (hg : StrictMono g) (hb : ∀ k, 0 ≤ g k ∧ g k < 2 * Real.pi)
    (hcl : ∀ a b c : Fin n, a ≠ b →
      ∃ d : Fin n, ∃ q : ℤ, g d = g a + g b - g c + 2 * Real.pi * q)
    (hn3 : 3 ≤ n) (i : ℤ) :
    periodicEnum hn g i =
      periodicEnum hn g 0 + (i : ℝ) * (periodicEnum hn g 1 - periodicEnum hn g 0) := by
  have key : ∀ i : ℤ, periodicEnum hn g (i + 1) - periodicEnum hn g i =
      periodicEnum hn g 1 - periodicEnum hn g 0 := by
    have up : ∀ i : ℤ, 0 ≤ i → periodicEnum hn g (i + 1) - periodicEnum hn g i =
        periodicEnum hn g 1 - periodicEnum hn g 0 := by
      intro i hi
      exact Int.leInduction (motive := fun i _ =>
          periodicEnum hn g (i + 1) - periodicEnum hn g i =
            periodicEnum hn g 1 - periodicEnum hn g 0) rfl
        (fun j hj ih => by
          have h := periodicEnum_gap hn hg hb hcl hn3 (j + 1)
          rw [show j + 1 - 1 = j from by ring] at h
          linarith [ih, h]) i hi
    have down : ∀ i : ℤ, i ≤ 0 → periodicEnum hn g (i + 1) - periodicEnum hn g i =
        periodicEnum hn g 1 - periodicEnum hn g 0 := by
      intro i hi
      exact Int.leInductionDown (motive := fun i _ =>
          periodicEnum hn g (i + 1) - periodicEnum hn g i =
            periodicEnum hn g 1 - periodicEnum hn g 0) rfl
        (fun j hj ih => by
          have h := periodicEnum_gap hn hg hb hcl hn3 j
          have e : j - 1 + 1 = j := by ring
          rw [e]
          linarith [ih, h]) i hi
    intro i
    rcases le_or_gt 0 i with h | h
    · exact up i h
    · exact down i (le_of_lt h)
  rcases le_or_gt 0 i with hi | hi
  · exact Int.leInduction (motive := fun i _ =>
        periodicEnum hn g i =
          periodicEnum hn g 0 + (i : ℝ) * (periodicEnum hn g 1 - periodicEnum hn g 0)) (by simp)
      (fun j hj ih => by
        have h := key j
        have e : ((j + 1 : ℤ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
        rw [e]
        linarith [ih, h]) i hi
  · exact Int.leInductionDown (motive := fun i _ =>
        periodicEnum hn g i =
          periodicEnum hn g 0 + (i : ℝ) * (periodicEnum hn g 1 - periodicEnum hn g 0)) (by simp)
      (fun j hj ih => by
        have h := key (j - 1)
        rw [show j - 1 + 1 = j from by ring] at h
        have e : ((j - 1 : ℤ) : ℝ) = (j : ℝ) - 1 := by push_cast; ring
        rw [e]
        linarith [ih, h]) i (le_of_lt hi)

lemma periodicEnum_apply_coe {n : ℕ} (hn : 0 < n) (g : Fin n → ℝ) (k : Fin n) :
    periodicEnum hn g ((k : ℕ) : ℤ) = g k := by
  have e2 : (((k : ℕ) : ℤ) / (n : ℤ)) = 0 :=
    Int.ediv_eq_zero_of_lt (Int.natCast_nonneg _) (by exact_mod_cast k.2)
  show g (periodicIdx hn ((k : ℕ) : ℤ)) + 2 * Real.pi * ((((k : ℕ) : ℤ) / (n : ℤ) : ℤ) : ℝ) = g k
  rw [periodicIdx_apply_coe hn k, e2]
  simp

/-- The forward direction: a set with the bisector-symmetry property is the
vertex set of a regular polygon. -/
theorem forward {S : Finset Pl} (hcard : 3 ≤ S.card)
    (hS : ∀ A ∈ S, ∀ B ∈ S, A ≠ B → ∀ X ∈ S, reflect A B X ∈ S) :
    ∃ n : ℕ, 3 ≤ n ∧ ∃ c : Pl, ∃ r : ℝ, 0 < r ∧ ∃ θ₀ : ℝ,
      S = (Finset.univ : Finset (Fin n)).image
        (fun k : Fin n => c + r • !₂[Real.cos (θ₀ + 2 * Real.pi * (k : ℝ) / (n : ℝ)),
                             Real.sin (θ₀ + 2 * Real.pi * (k : ℝ) / (n : ℝ))]) := by
  classical
  set n := S.card with hn_def
  have hn3 : 3 ≤ n := hcard
  have hnpos : 0 < n := by omega
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hnpos.ne'
  set G : Pl := (n : ℝ)⁻¹ • ∑ X ∈ S, X with hG_def
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  rcases hne with ⟨A₀, hA₀⟩
  set r := dist G A₀ with hr_def
  have hdist : ∀ X ∈ S, dist G X = r := fun X hX => (dist_center_eq hS hA₀ hX hnR).symm
  have hr : 0 < r := by
    rw [hr_def, dist_pos]
    by_contra hGA
    rcases Finset.one_lt_card.mp (by omega : 1 < S.card) with ⟨a, ha, b, hb, hab⟩
    have hz : r = 0 := by rw [hr_def, ← hGA, dist_self]
    have haG : a = G := by
      have h1 : dist G a = 0 := by rw [hdist a ha, hz]
      rw [dist_eq_zero] at h1
      exact h1.symm
    have hbG : b = G := by
      have h1 : dist G b = 0 := by rw [hdist b hb, hz]
      rw [dist_eq_zero] at h1
      exact h1.symm
    exact hab (haG.trans hbG.symm)
  -- assign an angle to each point
  have hθ : ∀ X ∈ S, ∃ t : ℝ, 0 ≤ t ∧ t < 2 * Real.pi ∧ X - G = r • unitVec t := by
    intro X hX
    have hnorm : ‖(r⁻¹ : ℝ) • (X - G)‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, ← dist_eq_norm, dist_comm, hdist X hX,
        abs_of_pos (inv_pos.mpr hr), inv_mul_cancel₀ hr.ne']
    rcases exists_angle _ hnorm with ⟨t, ht0, ht1, ht2⟩
    exact ⟨t, ht0, ht1, by rw [← ht2]; exact (smul_inv_smul₀ hr.ne' (X - G)).symm⟩
  choose t0 ht0 using hθ
  let t : Pl → ℝ := fun X => if hX : X ∈ S then t0 X hX else 0
  have ht : ∀ X ∈ S, 0 ≤ t X ∧ t X < 2 * Real.pi ∧ X - G = r • unitVec (t X) := by
    intro X hX
    have h2 : t X = t0 X hX := dif_pos hX
    rw [h2]
    exact ht0 X hX
  have ht_inj : ∀ X ∈ S, ∀ Y ∈ S, t X = t Y → X = Y := by
    intro X hX Y hY h
    have e1 := (ht X hX).2.2
    have e2 := (ht Y hY).2.2
    rw [h] at e1
    have h1 : X - G = Y - G := by rw [e1, e2]
    exact sub_left_inj.mp h1
  set Θ : Finset ℝ := S.image t with hΘ_def
  have hcardΘ : Θ.card = n := Finset.card_image_of_injOn ht_inj
  have hΘ_mem : ∀ θ' ∈ Θ, 0 ≤ θ' ∧ θ' < 2 * Real.pi := by
    intro θ' hθ'
    rcases Finset.mem_image.mp hθ' with ⟨X, hX, rfl⟩
    exact ⟨(ht X hX).1, (ht X hX).2.1⟩
  -- the reflection property in angular form
  have hrefl : ∀ α ∈ Θ, ∀ β ∈ Θ, ∀ θ' ∈ Θ, α ≠ β →
      ∃ θ'' ∈ Θ, ∃ k : ℤ, θ'' = α + β - θ' + 2 * Real.pi * k := by
    intro α hα β hβ θ' hθ' hαβ
    rcases Finset.mem_image.mp hα with ⟨A, hA, hAe⟩
    rcases Finset.mem_image.mp hβ with ⟨B, hB, hBe⟩
    rcases Finset.mem_image.mp hθ' with ⟨X, hX, hXe⟩
    have hAB : A ≠ B := by
      intro h
      apply hαβ
      rw [← hAe, ← hBe, h]
    have hσX : reflect A B X ∈ S := hS A hA B hB hAB X hX
    have hAeq : A = G + r • unitVec α := by
      have h1 := (ht A hA).2.2
      rw [hAe] at h1
      rw [sub_eq_iff_eq_add, add_comm] at h1
      exact h1
    have hBeq : B = G + r • unitVec β := by
      have h1 := (ht B hB).2.2
      rw [hBe] at h1
      rw [sub_eq_iff_eq_add, add_comm] at h1
      exact h1
    have hXeq : X = G + r • unitVec θ' := by
      have h1 := (ht X hX).2.2
      rw [hXe] at h1
      rw [sub_eq_iff_eq_add, add_comm] at h1
      exact h1
    have huab : unitVec β ≠ unitVec α := by
      intro h
      apply hAB
      rw [hAeq, hBeq, h]
    have hD : inner ℝ (unitVec β - unitVec α) (unitVec β - unitVec α) ≠ 0 :=
      inner_self_ne_zero.mpr (sub_ne_zero.mpr huab)
    have hσ := reflect_eq_of_on_circle hr.ne' hAeq hBeq hXeq hD
    have h2 := (ht (reflect A B X) hσX).2.2
    have h3 : r • unitVec (t (reflect A B X)) = r • unitVec (α + β - θ') := by
      have e : reflect A B X - G = r • unitVec (α + β - θ') := by rw [hσ]; module
      rw [← h2, e]
    have h4 : unitVec (t (reflect A B X)) = unitVec (α + β - θ') := by
      rw [← inv_smul_smul₀ hr.ne' (unitVec (t (reflect A B X))),
        ← inv_smul_smul₀ hr.ne' (unitVec (α + β - θ')), h3]
    exact ⟨t (reflect A B X), Finset.mem_image.mpr ⟨reflect A B X, hσX, rfl⟩, unitVec_eq h4⟩
  -- set up the periodic enumeration of the angles
  set e := Θ.orderIsoOfFin hcardΘ with he_def
  have hn0 : 0 < n := hnpos
  set g : Fin n → ℝ := fun k => ((e k : Θ) : ℝ) with hg_def
  have hg : StrictMono g := fun _ _ h => Subtype.coe_lt_coe.mpr (e.strictMono h)
  have hb : ∀ k : Fin n, 0 ≤ g k ∧ g k < 2 * Real.pi := fun k => hΘ_mem _ (e k).2
  have hcl : ∀ a b c : Fin n, a ≠ b →
      ∃ d : Fin n, ∃ q : ℤ, g d = g a + g b - g c + 2 * Real.pi * q := by
    intro a b c hab
    have hga : g a ∈ Θ := (e a).2
    have hgb : g b ∈ Θ := (e b).2
    have hgc : g c ∈ Θ := (e c).2
    have hab' : g a ≠ g b := fun h => hab (e.toEquiv.injective (Subtype.ext h))
    rcases hrefl (g a) hga (g b) hgb (g c) hgc hab' with ⟨θ'', hθ'', q, hq⟩
    refine ⟨e.symm ⟨θ'', hθ''⟩, q, ?_⟩
    have h1 : g (e.symm ⟨θ'', hθ''⟩) = θ'' :=
      congrArg Subtype.val (e.apply_symm_apply ⟨θ'', hθ''⟩)
    rw [h1]
    exact hq
  -- the gaps are all equal, hence equal to `2π/n`
  have hfd := periodicEnum_affine hn0 hg hb hcl hn3
  have hfn0 : periodicEnum hn0 g (n : ℤ) = periodicEnum hn0 g 0 + 2 * Real.pi := by
    have e1 : (n : ℤ) % (n : ℤ) = (0 : ℤ) % (n : ℤ) := by rw [Int.emod_self, Int.zero_emod]
    have e2 : (n : ℤ) / (n : ℤ) = 1 := Int.ediv_self (by exact_mod_cast hnpos.ne')
    have e3 : (0 : ℤ) / (n : ℤ) = 0 := Int.zero_ediv _
    show g (periodicIdx hn0 (n : ℤ)) + 2 * Real.pi * (((n : ℤ) / (n : ℤ) : ℤ) : ℝ) =
      g (periodicIdx hn0 0) + 2 * Real.pi * (((0 : ℤ) / (n : ℤ) : ℤ) : ℝ) + 2 * Real.pi
    rw [e2, e3, periodicIdx_congr hn0 e1]
    push_cast
    ring
  have hd : periodicEnum hn0 g 1 - periodicEnum hn0 g 0 = 2 * Real.pi / (n : ℝ) := by
    have h1 := hfd (n : ℤ)
    rw [hfn0] at h1
    have h2 : ((n : ℤ) : ℝ) = (n : ℝ) := by push_cast; ring
    rw [h2] at h1
    field_simp [hnR]
    linarith [h1]
  -- every value of the enumeration is of the form `f 0 + 2πk/n`
  have hev_eq : ∀ k : Fin n, g k = periodicEnum hn0 g 0 + 2 * Real.pi * (k : ℝ) / (n : ℝ) := by
    intro k
    have h1 := hfd ((k : ℕ) : ℤ)
    rw [periodicEnum_apply_coe hn0 g k] at h1
    have h2 : (((k : ℕ) : ℤ) : ℝ) = ((k : ℕ) : ℝ) := by push_cast; ring
    rw [h2, hd] at h1
    field_simp [hnR] at h1 ⊢
    linarith [h1]
  -- assemble the final image description
  have hsub : S ⊆ (Finset.univ : Finset (Fin n)).image
      (fun k : Fin n => G + r • !₂[Real.cos (periodicEnum hn0 g 0 + 2 * Real.pi * (k : ℝ) / (n : ℝ)),
                           Real.sin (periodicEnum hn0 g 0 + 2 * Real.pi * (k : ℝ) / (n : ℝ))]) := by
    intro X hX
    have htX : t X ∈ Θ := Finset.mem_image.mpr ⟨X, hX, rfl⟩
    set idx := e.symm ⟨t X, htX⟩ with hidx
    have h2 : g idx = t X := congrArg Subtype.val (e.apply_symm_apply ⟨t X, htX⟩)
    rw [hev_eq idx] at h2
    have h3 := (ht X hX).2.2
    apply Finset.mem_image.mpr
    refine ⟨idx, Finset.mem_univ _, ?_⟩
    show G + r • unitVec (periodicEnum hn0 g 0 + 2 * Real.pi * (idx : ℝ) / (n : ℝ)) = X
    rw [h2, ← h3]
    module
  have hinj2 : Function.Injective
      (fun k : Fin n => G + r • unitVec (periodicEnum hn0 g 0 + 2 * Real.pi * (k : ℝ) / (n : ℝ))) := by
    intro j k hjk
    simp only [] at hjk
    rw [add_left_cancel_iff] at hjk
    have h1 : unitVec (periodicEnum hn0 g 0 + 2 * Real.pi * (j : ℝ) / (n : ℝ)) =
        unitVec (periodicEnum hn0 g 0 + 2 * Real.pi * (k : ℝ) / (n : ℝ)) :=
      smul_right_injective Pl hr.ne' hjk
    rcases unitVec_eq h1 with ⟨m, hm⟩
    have hpi : (2 : ℝ) * Real.pi ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
    have hmn : ((j : ℝ) - (k : ℝ)) = (n : ℝ) * (m : ℝ) := by
      have hm2 : 2 * Real.pi * ((j : ℝ) - (k : ℝ)) = 2 * Real.pi * ((m : ℝ) * (n : ℝ)) := by
        field_simp [hnR] at hm
        linarith [hm]
      have h3 : (j : ℝ) - (k : ℝ) = (m : ℝ) * (n : ℝ) := mul_left_cancel₀ hpi hm2
      rw [mul_comm]
      exact h3
    have h5 : ((j : ℕ) : ℤ) - ((k : ℕ) : ℤ) = (n : ℤ) * m := by
      apply Int.cast_injective (α := ℝ)
      push_cast
      linarith [hmn]
    have h6 : (n : ℤ) ∣ (((j : ℕ) : ℤ) - ((k : ℕ) : ℤ)) := ⟨m, h5⟩
    by_cases hjk2 : ((j : ℕ) : ℤ) = ((k : ℕ) : ℤ)
    · have h7 : (j : ℕ) = (k : ℕ) := by exact_mod_cast hjk2
      exact Fin.ext h7
    · exfalso
      have h7 : (n : ℤ) ≤ |((j : ℕ) : ℤ) - ((k : ℕ) : ℤ)| :=
        Int.le_of_dvd (abs_pos.mpr (sub_ne_zero.mpr hjk2)) ((dvd_abs (n : ℤ) _).mpr h6)
      have h8 : |((j : ℕ) : ℤ) - ((k : ℕ) : ℤ)| < (n : ℤ) := by
        have hj2 : ((j : ℕ) : ℤ) < n := by exact_mod_cast j.2
        have hk2 : ((k : ℕ) : ℤ) < n := by exact_mod_cast k.2
        rcases le_or_gt ((j : ℕ) : ℤ) ((k : ℕ) : ℤ) with h | h
        · rw [abs_of_nonpos (by linarith)]
          have hj0 : (0 : ℤ) ≤ (j : ℕ) := Int.natCast_nonneg _
          linarith
        · rw [abs_of_nonneg (by linarith)]
          have hk0 : (0 : ℤ) ≤ (k : ℕ) := Int.natCast_nonneg _
          linarith
      linarith [h7, h8]
  have hinj2' : Function.Injective
      (fun k : Fin n => G + r • !₂[Real.cos (periodicEnum hn0 g 0 + 2 * Real.pi * (k : ℝ) / (n : ℝ)),
          Real.sin (periodicEnum hn0 g 0 + 2 * Real.pi * (k : ℝ) / (n : ℝ))]) := hinj2
  exact ⟨n, hn3, G, r, hr, periodicEnum hn0 g 0,
    Finset.eq_of_subset_of_card_le hsub (by
      rw [Finset.card_image_of_injective _ hinj2', Finset.card_univ, Fintype.card_fin])⟩

/-- The backward direction: vertices of a regular polygon have the
bisector-symmetry property. -/
theorem backward {S : Finset Pl}
    (h : ∃ n : ℕ, 3 ≤ n ∧ ∃ c : Pl, ∃ r : ℝ, 0 < r ∧ ∃ θ₀ : ℝ,
      S = (Finset.univ : Finset (Fin n)).image
        (fun k : Fin n => c + r • !₂[Real.cos (θ₀ + 2 * Real.pi * (k : ℝ) / (n : ℝ)),
                             Real.sin (θ₀ + 2 * Real.pi * (k : ℝ) / (n : ℝ))])) :
    3 ≤ S.card ∧ ∀ A ∈ S, ∀ B ∈ S, A ≠ B → ∀ X ∈ S, reflect A B X ∈ S := by
  classical
  rcases h with ⟨n, hn3, c, r, hr, θ₀, hS⟩
  have hnpos : 0 < n := by omega
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hnpos.ne'
  have hnZ : (n : ℤ) ≠ 0 := by exact_mod_cast hnpos.ne'
  have hginj : Function.Injective
      (fun k : Fin n => c + r • unitVec (θ₀ + 2 * Real.pi * (k : ℝ) / (n : ℝ))) := by
    intro j k hjk
    simp only [] at hjk
    rw [add_left_cancel_iff] at hjk
    have h1 := smul_right_injective Pl hr.ne' hjk
    rcases unitVec_eq h1 with ⟨m, hm⟩
    have hpi : (2 : ℝ) * Real.pi ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
    have hmn : ((j : ℝ) - (k : ℝ)) = (n : ℝ) * (m : ℝ) := by
      have hm2 : 2 * Real.pi * ((j : ℝ) - (k : ℝ)) = 2 * Real.pi * ((m : ℝ) * (n : ℝ)) := by
        field_simp [hnR] at hm
        linarith [hm]
      have h3 : (j : ℝ) - (k : ℝ) = (m : ℝ) * (n : ℝ) := mul_left_cancel₀ hpi hm2
      rw [mul_comm]
      exact h3
    have h5 : ((j : ℕ) : ℤ) - ((k : ℕ) : ℤ) = (n : ℤ) * m := by
      apply Int.cast_injective (α := ℝ)
      push_cast
      linarith [hmn]
    have h6 : (n : ℤ) ∣ (((j : ℕ) : ℤ) - ((k : ℕ) : ℤ)) := ⟨m, h5⟩
    by_cases hjk2 : ((j : ℕ) : ℤ) = ((k : ℕ) : ℤ)
    · have h7 : (j : ℕ) = (k : ℕ) := by exact_mod_cast hjk2
      exact Fin.ext h7
    · exfalso
      have h7 : (n : ℤ) ≤ |((j : ℕ) : ℤ) - ((k : ℕ) : ℤ)| :=
        Int.le_of_dvd (abs_pos.mpr (sub_ne_zero.mpr hjk2)) ((dvd_abs (n : ℤ) _).mpr h6)
      have h8 : |((j : ℕ) : ℤ) - ((k : ℕ) : ℤ)| < (n : ℤ) := by
        have hj2 : ((j : ℕ) : ℤ) < n := by exact_mod_cast j.2
        have hk2 : ((k : ℕ) : ℤ) < n := by exact_mod_cast k.2
        rcases le_or_gt ((j : ℕ) : ℤ) ((k : ℕ) : ℤ) with h | h
        · rw [abs_of_nonpos (by linarith)]
          have hj0 : (0 : ℤ) ≤ (j : ℕ) := Int.natCast_nonneg _
          linarith
        · rw [abs_of_nonneg (by linarith)]
          have hk0 : (0 : ℤ) ≤ (k : ℕ) := Int.natCast_nonneg _
          linarith
      linarith [h7, h8]
  have hginj' : Function.Injective
      (fun k : Fin n => c + r • !₂[Real.cos (θ₀ + 2 * Real.pi * (k : ℝ) / (n : ℝ)),
          Real.sin (θ₀ + 2 * Real.pi * (k : ℝ) / (n : ℝ))]) := hginj
  constructor
  · rw [hS, Finset.card_image_of_injective _ hginj', Finset.card_univ, Fintype.card_fin]
    exact hn3
  · intro A hA B hB hAB X hX
    rw [hS] at hA hB hX ⊢
    rcases Finset.mem_image.mp hA with ⟨j, -, hAj⟩
    rcases Finset.mem_image.mp hB with ⟨l, -, hBl⟩
    rcases Finset.mem_image.mp hX with ⟨m, -, hXm⟩
    have hAj2 : A = c + r • unitVec (θ₀ + 2 * Real.pi * (j : ℝ) / (n : ℝ)) := hAj.symm
    have hBl2 : B = c + r • unitVec (θ₀ + 2 * Real.pi * (l : ℝ) / (n : ℝ)) := hBl.symm
    have hXm2 : X = c + r • unitVec (θ₀ + 2 * Real.pi * (m : ℝ) / (n : ℝ)) := hXm.symm
    have hjl : j ≠ l := fun h => hAB (by rw [hAj2, hBl2, h])
    have huab : unitVec (θ₀ + 2 * Real.pi * (l : ℝ) / (n : ℝ)) ≠
        unitVec (θ₀ + 2 * Real.pi * (j : ℝ) / (n : ℝ)) := by
      intro hcc
      apply hjl
      apply hginj
      simp only []
      rw [add_left_cancel_iff, hcc]
    have hD : inner ℝ (unitVec (θ₀ + 2 * Real.pi * (l : ℝ) / (n : ℝ)) -
        unitVec (θ₀ + 2 * Real.pi * (j : ℝ) / (n : ℝ)))
        (unitVec (θ₀ + 2 * Real.pi * (l : ℝ) / (n : ℝ)) -
        unitVec (θ₀ + 2 * Real.pi * (j : ℝ) / (n : ℝ))) ≠ 0 :=
      inner_self_ne_zero.mpr (sub_ne_zero.mpr huab)
    have hσ := reflect_eq_of_on_circle hr.ne' hAj2 hBl2 hXm2 hD
    -- find the image index of the reflected point
    set s : ℤ := ((j : ℕ) : ℤ) + ((l : ℕ) : ℤ) - ((m : ℕ) : ℤ) with hs
    set k' : Fin n := ⟨(s % (n : ℤ)).toNat, (Int.toNat_lt (Int.emod_nonneg s hnZ)).mpr
      (Int.emod_lt_of_pos s (by exact_mod_cast hnpos))⟩ with hk'
    have hkk : ((k' : ℕ) : ℤ) = s % (n : ℤ) := by
      have h1 : (k' : ℕ) = (s % (n : ℤ)).toNat := rfl
      rw [h1]
      exact Int.toNat_of_nonneg (Int.emod_nonneg s hnZ)
    have hq : (s : ℝ) = ((k' : ℕ) : ℝ) + ((s / (n : ℤ) : ℤ) : ℝ) * (n : ℝ) := by
      have h1 : (s : ℤ) % (n : ℤ) = s - (n : ℤ) * (s / (n : ℤ)) := Int.emod_def s (n : ℤ)
      have h3 : (((k' : ℕ) : ℤ) : ℝ) = (s : ℝ) - (n : ℝ) * ((s / (n : ℤ) : ℤ) : ℝ) := by
        rw [hkk]
        exact_mod_cast h1
      push_cast at h3
      linarith [h3]
    apply Finset.mem_image.mpr
    refine ⟨k', Finset.mem_univ _, ?_⟩
    have hsum : (θ₀ + 2 * Real.pi * (j : ℝ) / (n : ℝ)) + (θ₀ + 2 * Real.pi * (l : ℝ) / (n : ℝ)) -
        (θ₀ + 2 * Real.pi * (m : ℝ) / (n : ℝ)) =
        θ₀ + 2 * Real.pi * ((s : ℝ) / (n : ℝ)) := by
      rw [hs]
      push_cast
      field_simp [hnR]
      ring
    have hdecomp : θ₀ + 2 * Real.pi * ((s : ℝ) / (n : ℝ)) =
        (θ₀ + 2 * Real.pi * ((k' : ℕ) : ℝ) / (n : ℝ)) + 2 * Real.pi * ((s / (n : ℤ) : ℤ) : ℝ) := by
      rw [hq]
      field_simp [hnR]
      ring
    show c + r • !₂[Real.cos (θ₀ + 2 * Real.pi * (k' : ℝ) / (n : ℝ)),
        Real.sin (θ₀ + 2 * Real.pi * (k' : ℝ) / (n : ℝ))] = reflect A B X
    rw [hσ, hsum, hdecomp, unitVec_periodic]
    rfl

snip end

problem imo1999_p1 :
    {S : Finset Pl | 3 ≤ S.card ∧
      ∀ A ∈ S, ∀ B ∈ S, A ≠ B → ∀ X ∈ S, reflect A B X ∈ S} =
      regularPolygonVertexSets := by
  ext S
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hcard, hS⟩
    exact forward hcard hS
  · rintro h
    exact backward h

end Imo1999P1
