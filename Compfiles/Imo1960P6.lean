/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 1960, Problem 6

Consider a cone of revolution with an inscribed sphere tangent to the base
of the cone. A cylinder is circumscribed about this sphere so that one of its
bases lies in the base of the cone. Let V₁ be the volume of the cone and V₂
the volume of the cylinder.

(a) Prove that V₁ ≠ V₂.

(b) Find the smallest number k for which V₁ = kV₂; for this case construct
the angle subtended by a diameter of the base of the cone at the vertex of
the cone.
-/

namespace Imo1960P6

open Real Set

/-- The volume of a cone of revolution that has an inscribed sphere of radius
`r` tangent to the base of the cone, where `θ` is the half-angle of the cone,
i.e. the angle between the axis of the cone and its sloping surface.

Up to scaling, the configuration is determined by `θ`: the center `O` of the
sphere lies on the axis of the cone at distance `r` above the base plane
(tangency of the sphere to the base) and at distance `r / sin θ` from the
vertex `V` (tangency of the sphere to the sloping surface). Hence the height
of the cone is `h = VX = VO + OX = r * (1 + 1 / sin θ)` (where `X` is the
center of the base) and the radius of its base is `R = h * tan θ`, so its
volume is `(1 / 3) * π * R ^ 2 * h`. -/
noncomputable def coneVolume (r θ : ℝ) : ℝ :=
  (1 / 3) * π * (r * (1 + 1 / sin θ) * tan θ) ^ 2 * (r * (1 + 1 / sin θ))

/-- The volume of a cylinder circumscribed about a sphere of radius `r`:
such a cylinder has radius `r` and height `2 * r`. -/
noncomputable def cylinderVolume (r : ℝ) : ℝ :=
  π * r ^ 2 * (2 * r)

snip begin

lemma cylinderVolume_pos {r : ℝ} (hr : 0 < r) : 0 < cylinderVolume r :=
  mul_pos (mul_pos pi_pos (pow_pos hr 2)) (mul_pos two_pos hr)

/-- The ratio `V₁ / V₂`, cleared of denominators:
`V₁ / V₂ = (1 + sin θ) ^ 3 / (6 * sin θ * (1 - sin θ ^ 2))`. -/
lemma coneVolume_mul {r θ : ℝ} (hr : 0 < r) (hθ : θ ∈ Ioo 0 (π / 2)) :
    coneVolume r θ * (6 * sin θ * (1 - sin θ ^ 2)) =
      cylinderVolume r * (1 + sin θ) ^ 3 := by
  have hs : 0 < sin θ :=
    sin_pos_of_pos_of_lt_pi hθ.1 (hθ.2.trans (half_lt_self pi_pos))
  have hc : 0 < cos θ := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos, hθ.1], hθ.2⟩
  have hsq : 1 - sin θ ^ 2 = cos θ ^ 2 := by
    have h := sin_sq_add_cos_sq θ
    linarith
  simp only [coneVolume, cylinderVolume, tan_eq_sin_div_cos, hsq]
  field_simp [hs.ne', hc.ne']
  ring

/-- The main inequality: `V₁ ≥ (4 / 3) * V₂` for every admissible
configuration. Both parts (a) and (b) of the problem follow from it. -/
lemma coneVolume_ge {r θ : ℝ} (hr : 0 < r) (hθ : θ ∈ Ioo 0 (π / 2)) :
    4 / 3 * cylinderVolume r ≤ coneVolume r θ := by
  have hs : 0 < sin θ :=
    sin_pos_of_pos_of_lt_pi hθ.1 (hθ.2.trans (half_lt_self pi_pos))
  have hs1 : sin θ < 1 := by
    have h := sin_lt_sin_of_lt_of_le_pi_div_two
      (show -(π / 2) ≤ θ by linarith [pi_pos, hθ.1]) le_rfl hθ.2
    rwa [sin_pi_div_two] at h
  have hsq1 : sin θ ^ 2 < 1 := by nlinarith [hs, hs1]
  have h6 : 0 < 6 * sin θ * (1 - sin θ ^ 2) :=
    mul_pos (mul_pos (by norm_num) hs) (by linarith)
  -- The polynomial inequality `(1 + s) ^ 3 ≥ 8 * s * (1 - s ^ 2)` for
  -- `s = sin θ`: the difference factors as `(3 * s - 1) ^ 2 * (s + 1)`.
  have hbound : 8 * sin θ * (1 - sin θ ^ 2) ≤ (1 + sin θ) ^ 3 := by
    have hprod : 0 ≤ (3 * sin θ - 1) ^ 2 * (sin θ + 1) :=
      mul_nonneg (sq_nonneg _) (by linarith)
    have hexpand : (3 * sin θ - 1) ^ 2 * (sin θ + 1) =
        (1 + sin θ) ^ 3 - 8 * sin θ * (1 - sin θ ^ 2) := by ring
    linarith
  have hbound' : (4 / 3 * cylinderVolume r) * (6 * sin θ * (1 - sin θ ^ 2)) ≤
      coneVolume r θ * (6 * sin θ * (1 - sin θ ^ 2)) :=
    calc (4 / 3 * cylinderVolume r) * (6 * sin θ * (1 - sin θ ^ 2))
        = cylinderVolume r * (8 * sin θ * (1 - sin θ ^ 2)) := by ring
      _ ≤ cylinderVolume r * (1 + sin θ) ^ 3 :=
          mul_le_mul_of_nonneg_left hbound (cylinderVolume_pos hr).le
      _ = coneVolume r θ * (6 * sin θ * (1 - sin θ ^ 2)) :=
          (coneVolume_mul hr hθ).symm
  exact le_of_mul_le_mul_right hbound' h6

/-- Equality `V₁ = (4 / 3) * V₂` holds for the configuration with
`sin θ = 1 / 3`. -/
lemma coneVolume_eq {r θ : ℝ} (hr : 0 < r) (hθ : θ ∈ Ioo 0 (π / 2)) (hs : sin θ = 1 / 3) :
    coneVolume r θ = 4 / 3 * cylinderVolume r := by
  have h := coneVolume_mul hr hθ
  rw [hs] at h
  norm_num at h
  linarith

/-- The half-angle `θ = arcsin (1 / 3)` is admissible; it is the half-angle
asked for in part (b) (so the angle subtended by a diameter of the base at
the vertex is `2 * arcsin (1 / 3)`). -/
lemma arcsin_third_mem : arcsin (1 / 3) ∈ Ioo 0 (π / 2) := by
  have h0 : (0 : ℝ) ∈ Icc (-1) 1 := ⟨by norm_num, by norm_num⟩
  have h3 : (1 / 3 : ℝ) ∈ Icc (-1) 1 := ⟨by norm_num, by norm_num⟩
  have h1 : (1 : ℝ) ∈ Icc (-1) 1 := ⟨by norm_num, by norm_num⟩
  constructor
  · have h := strictMonoOn_arcsin h0 h3 (by norm_num : (0 : ℝ) < 1 / 3)
    rwa [arcsin_zero] at h
  · have h := strictMonoOn_arcsin h3 h1 (by norm_num : (1 / 3 : ℝ) < 1)
    rwa [arcsin_one] at h

snip end

/-- The smallest possible value of `V₁ / V₂`. -/
noncomputable determine minVolumeRatio : ℝ := 4 / 3

problem imo1960_p6 :
    (∀ r θ : ℝ, 0 < r → θ ∈ Ioo 0 (π / 2) → coneVolume r θ ≠ cylinderVolume r) ∧
    IsLeast {k : ℝ | ∃ r θ : ℝ, 0 < r ∧ θ ∈ Ioo 0 (π / 2) ∧
      coneVolume r θ = k * cylinderVolume r} minVolumeRatio := by
  refine ⟨fun r θ hr hθ hEq => ?_, ⟨?_, ?_⟩⟩
  · -- Part (a): `V₁ ≠ V₂`, since `V₁ ≥ (4 / 3) * V₂ > V₂`.
    have hge := coneVolume_ge hr hθ
    have hcyl := cylinderVolume_pos hr
    linarith
  · -- Part (b), attainment: the ratio `4 / 3` occurs for `sin θ = 1 / 3`.
    refine ⟨1, arcsin (1 / 3), one_pos, arcsin_third_mem, ?_⟩
    show coneVolume 1 (arcsin (1 / 3)) = (4 / 3) * cylinderVolume 1
    exact coneVolume_eq one_pos arcsin_third_mem (sin_arcsin (by norm_num) (by norm_num))
  · -- Part (b), minimality: no smaller ratio occurs.
    intro k ⟨r, θ, hr, hθ, hEq⟩
    have hge := coneVolume_ge hr hθ
    have hcyl := cylinderVolume_pos hr
    have h : (4 / 3 : ℝ) * cylinderVolume r ≤ k * cylinderVolume r := by linarith
    exact le_of_mul_le_mul_right h hcyl

end Imo1960P6
