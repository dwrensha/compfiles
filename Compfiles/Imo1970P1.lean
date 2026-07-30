/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import Mathlib.Analysis.Convex.StrictConvexBetween
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Geometry.Euclidean.Triangle
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 1970, Problem 1

`M` is any point on the side `AB` of the triangle `ABC`. Let `r`, `r₁`, `r₂`
be the radii of the circles inscribed in `ABC`, `AMC`, `BMC`, and let `q` be
the radius of the circle on the opposite side of `AB` to `C`, touching `AB`
and the extensions of `CA` and `CB`; `q₁` and `q₂` are defined similarly.
Prove that `r₁r₂q = rq₁q₂`.

# Solution

For a triangle with inradius `r`, and with `q` the radius of the excircle
touching the side `c = AB` (on the opposite side of `AB` from the third
vertex), one has `r / q = tan(A/2) · tan(B/2)`: writing `s` for the
semiperimeter, `r / q = (s - c) / s`, and the half-angle formulas together
with the law of cosines give `tan(A/2) · tan(B/2) = (s - c) / s`.

Applying this to the three triangles, with `θ = ∠AMC` and `φ = ∠BMC`,
`r / q = tan(A/2)tan(B/2)`, `r₁ / q₁ = tan(A/2)tan(θ/2)` and
`r₂ / q₂ = tan(B/2)tan(φ/2)`. Since `M` lies on `AB`, `θ + φ = π`, so
`tan(φ/2) = tan(π/2 - θ/2) = 1 / tan(θ/2)` and hence
`r₁r₂q / (rq₁q₂) = tan(θ/2)tan(φ/2) = 1`.
-/

namespace Imo1970P1

open scoped EuclideanGeometry
open EuclideanGeometry

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {P : Type*} [MetricSpace P] [NormedAddTorsor V P]

/-- The inradius of a triangle with side lengths `a`, `b`, `c`, given by
Heron's formula `r = √((s-a)(s-b)(s-c)/s)` with `s` the semiperimeter. -/
noncomputable def inradius (a b c : ℝ) : ℝ :=
  Real.sqrt (((b + c - a) * (c + a - b) * (a + b - c)) / (8 * (a + b + c)))

/-- The radius of the excircle of a triangle with side lengths `a`, `b`, `c`
that touches the side of length `c` and the extensions of the other two sides,
lying on the opposite side of that side from the third vertex:
`q = √(s(s-a)(s-b)/(s-c))` with `s` the semiperimeter. -/
noncomputable def exradius (a b c : ℝ) : ℝ :=
  Real.sqrt (((a + b + c) * (b + c - a) * (c + a - b)) / (8 * (a + b - c)))

snip begin

theorem nc12 {a b c : P} (h : ¬Collinear ℝ ({a, b, c} : Set P)) :
    ¬Collinear ℝ ({b, a, c} : Set P) := by
  rwa [Set.insert_comm b a {c}]

theorem nc23 {a b c : P} (h : ¬Collinear ℝ ({a, b, c} : Set P)) :
    ¬Collinear ℝ ({a, c, b} : Set P) := by
  rwa [Set.pair_comm c b]

/-- The side lengths of a non-degenerate triangle: positivity and the strict
triangle inequalities, in a normal form used repeatedly below. -/
theorem tri_sides {A B C : P} (h : ¬Collinear ℝ ({A, B, C} : Set P)) :
    0 < dist B C ∧ 0 < dist C A ∧ 0 < dist A B ∧
      dist B C < dist C A + dist A B ∧ dist C A < dist A B + dist B C ∧
        dist A B < dist B C + dist C A := by
  have hBAC : ¬Collinear ℝ ({B, A, C} : Set P) := nc12 h
  have hACB : ¬Collinear ℝ ({A, C, B} : Set P) := nc23 h
  have hCBA : ¬Collinear ℝ ({C, B, A} : Set P) := nc12 (nc23 (nc12 h))
  refine ⟨dist_pos.mpr (ne₂₃_of_not_collinear h),
    dist_pos.mpr (ne₂₃_of_not_collinear hBAC).symm,
    dist_pos.mpr (ne₁₂_of_not_collinear h), ?_, ?_, ?_⟩
  · have hr : dist B C < dist B A + dist A C := by
      rw [dist_lt_dist_add_dist_iff]
      exact fun hw => hBAC hw.collinear
    rw [dist_comm B A, dist_comm A C] at hr
    linarith
  · have hr : dist C A < dist C B + dist B A := by
      rw [dist_lt_dist_add_dist_iff]
      exact fun hw => hCBA hw.collinear
    rw [dist_comm C B, dist_comm B A] at hr
    linarith
  · have hr : dist A B < dist A C + dist C B := by
      rw [dist_lt_dist_add_dist_iff]
      exact fun hw => hACB hw.collinear
    rw [dist_comm A C, dist_comm C B] at hr
    linarith

/-- The inradius of a non-degenerate triangle is positive. -/
theorem inradius_pos {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a < b + c) (h2 : b < c + a) (h3 : c < a + b) : 0 < inradius a b c := by
  simp only [inradius]
  apply Real.sqrt_pos.mpr
  exact div_pos (mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)) (by linarith)

/-- The exradius of a non-degenerate triangle is positive. -/
theorem exradius_pos {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a < b + c) (h2 : b < c + a) (h3 : c < a + b) : 0 < exradius a b c := by
  simp only [exradius]
  apply Real.sqrt_pos.mpr
  exact div_pos (mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)) (by linarith)

/-- The ratio of the inradius to the radius of the excircle touching the side
of length `c` equals `(s - c) / s`, where `s` is the semiperimeter. -/
theorem inradius_div_exradius {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a < b + c) (h2 : b < c + a) (h3 : c < a + b) :
    inradius a b c / exradius a b c = (a + b - c) / (a + b + c) := by
  have g1 : (0:ℝ) < b + c - a := by linarith
  have g2 : (0:ℝ) < c + a - b := by linarith
  have g3 : (0:ℝ) < a + b - c := by linarith
  have g4 : (0:ℝ) < a + b + c := by linarith
  have hu : (0:ℝ) ≤ (b + c - a) * (c + a - b) * (a + b - c) / (8 * (a + b + c)) :=
    div_nonneg ((mul_pos (mul_pos g1 g2) g3).le) (by linarith)
  simp only [inradius, exradius]
  rw [← Real.sqrt_div hu]
  have heq : (b + c - a) * (c + a - b) * (a + b - c) / (8 * (a + b + c)) /
      ((a + b + c) * (b + c - a) * (c + a - b) / (8 * (a + b - c))) =
      ((a + b - c) / (a + b + c)) ^ 2 := by
    have n1 : (8:ℝ) * (a + b + c) ≠ 0 := mul_ne_zero (by norm_num) g4.ne'
    have n2 : (8:ℝ) * (a + b - c) ≠ 0 := mul_ne_zero (by norm_num) g3.ne'
    have n3 : (a + b + c) * (b + c - a) * (c + a - b) ≠ 0 :=
      mul_ne_zero (mul_ne_zero g4.ne' g1.ne') g2.ne'
    have n4 : a + b + c ≠ 0 := g4.ne'
    have n5 : a + b - c ≠ 0 := g3.ne'
    field_simp
  rw [heq, Real.sqrt_sq (div_nonneg g3.le g4.le)]

/-- `(x/2) / (y/2) = x / y`, also when `y = 0`. -/
theorem div_half_div_half (x y : ℝ) : x / 2 / (y / 2) = x / y := by
  by_cases hy : y = 0
  · simp [hy]
  · field_simp

/-- For `θ ∈ (0, π)`, the squared tangent of the half angle. -/
theorem tan_sq_half {θ : ℝ} (h0 : 0 < θ) (hπ : θ < Real.pi) :
    Real.tan (θ / 2) ^ 2 = (1 - Real.cos θ) / (1 + Real.cos θ) := by
  have hc2 : Real.cos θ = 2 * Real.cos (θ / 2) ^ 2 - 1 := by
    have h := Real.cos_two_mul (θ / 2)
    rwa [show (2:ℝ) * (θ / 2) = θ from by ring] at h
  have hs2 : Real.sin (θ / 2) ^ 2 = (1 - Real.cos θ) / 2 := by
    have h := Real.sin_sq_add_cos_sq (θ / 2)
    linarith
  have hc2' : Real.cos (θ / 2) ^ 2 = (1 + Real.cos θ) / 2 := by linarith
  have hcpos : Real.cos (θ / 2) ≠ 0 := by
    have h := Real.cos_pos_of_mem_Ioo (show θ / 2 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) from
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩)
    exact h.ne'
  rw [Real.tan_eq_sin_div_cos, div_pow, hs2, hc2', div_half_div_half]

/-- For `θ ∈ (0, π)`, the tangent of the half angle is positive. -/
theorem tan_half_pos {θ : ℝ} (h0 : 0 < θ) (hπ : θ < Real.pi) : 0 < Real.tan (θ / 2) := by
  have hs : 0 < Real.sin (θ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hc : 0 < Real.cos (θ / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  rw [Real.tan_eq_sin_div_cos]
  exact div_pos hs hc

/-- Pure algebra behind `tan(A/2) · tan(B/2) = (s - c) / s`. -/
theorem tan_half_mul_sq_algebra {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a < b + c) (h2 : b < c + a) (h3 : c < a + b) :
    (a - b + c) * (a + b - c) / (2 * b * c) / ((b + c - a) * (a + b + c) / (2 * b * c)) *
      ((b - a + c) * (a + b - c) / (2 * c * a) /
        ((a + c - b) * (a + b + c) / (2 * c * a))) =
      ((a + b - c) / (a + b + c)) ^ 2 := by
  have n1 : (2:ℝ) * b * c ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero hb.ne') hc.ne'
  have n2 : (2:ℝ) * c * a ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero hc.ne') ha.ne'
  have n3 : b + c - a ≠ 0 := (by linarith : (0:ℝ) < b + c - a).ne'
  have n4 : a + b + c ≠ 0 := (by linarith : (0:ℝ) < a + b + c).ne'
  have n5 : a + c - b ≠ 0 := (by linarith : (0:ℝ) < a + c - b).ne'
  have n6 : a + b - c ≠ 0 := (by linarith : (0:ℝ) < a + b - c).ne'
  have n7 : (b + c - a) * (a + b + c) ≠ 0 := mul_ne_zero n3 n4
  have n8 : (a + c - b) * (a + b + c) ≠ 0 := mul_ne_zero n5 n4
  field_simp
  ring

/-- In a non-degenerate triangle `ABC`, the product of the tangents of the
half-angles at `A` and `B` equals `(s - c) / s`, where `c = AB` and `s` is
the semiperimeter. -/
theorem tan_half_angle_mul {A B C : P} (h : ¬Collinear ℝ ({A, B, C} : Set P)) :
    Real.tan (∠ C A B / 2) * Real.tan (∠ A B C / 2) =
      (dist B C + dist C A - dist A B) / (dist B C + dist C A + dist A B) := by
  obtain ⟨ha, hb, hc, htri1, htri2, htri3⟩ := tri_sides h
  have hb' : dist C A ≠ 0 := hb.ne'
  have hc' : dist A B ≠ 0 := hc.ne'
  have ha' : dist B C ≠ 0 := ha.ne'
  have hcosA : Real.cos (∠ C A B) =
      (dist C A ^ 2 + dist A B ^ 2 - dist B C ^ 2) / (2 * dist C A * dist A B) := by
    have hlaw := law_cos C A B
    rw [dist_comm C B, dist_comm B A] at hlaw
    rw [eq_div_iff (mul_ne_zero (mul_ne_zero two_ne_zero hb') hc')]
    linear_combination hlaw
  have hcosB : Real.cos (∠ A B C) =
      (dist A B ^ 2 + dist B C ^ 2 - dist C A ^ 2) / (2 * dist A B * dist B C) := by
    have hlaw := law_cos A B C
    rw [dist_comm A C, dist_comm C B] at hlaw
    rw [eq_div_iff (mul_ne_zero (mul_ne_zero two_ne_zero hc') ha')]
    linear_combination hlaw
  have hA0 : 0 < ∠ C A B := angle_pos_of_not_collinear (nc12 (nc23 h))
  have hAπ : ∠ C A B < Real.pi := angle_lt_pi_of_not_collinear (nc12 (nc23 h))
  have hB0 : 0 < ∠ A B C := angle_pos_of_not_collinear h
  have hBπ : ∠ A B C < Real.pi := angle_lt_pi_of_not_collinear h
  have htanA2 := tan_sq_half hA0 hAπ
  have htanB2 := tan_sq_half hB0 hBπ
  have h1mA : 1 - Real.cos (∠ C A B) =
      (dist B C - dist C A + dist A B) * (dist B C + dist C A - dist A B) /
        (2 * dist C A * dist A B) := by
    rw [hcosA]
    field_simp
    ring
  have h1pA : 1 + Real.cos (∠ C A B) =
      (dist C A + dist A B - dist B C) * (dist B C + dist C A + dist A B) /
        (2 * dist C A * dist A B) := by
    rw [hcosA]
    field_simp
    ring
  have h1mB : 1 - Real.cos (∠ A B C) =
      (dist C A - dist B C + dist A B) * (dist B C + dist C A - dist A B) /
        (2 * dist A B * dist B C) := by
    rw [hcosB]
    field_simp
    ring
  have h1pB : 1 + Real.cos (∠ A B C) =
      (dist B C + dist A B - dist C A) * (dist B C + dist C A + dist A B) /
        (2 * dist A B * dist B C) := by
    rw [hcosB]
    field_simp
    ring
  have hmul : (Real.tan (∠ C A B / 2) * Real.tan (∠ A B C / 2)) ^ 2 =
      ((dist B C + dist C A - dist A B) / (dist B C + dist C A + dist A B)) ^ 2 := by
    rw [mul_pow, htanA2, htanB2, h1mA, h1pA, h1mB, h1pB]
    exact tan_half_mul_sq_algebra ha hb hc htri1 htri2 htri3
  have hposL : 0 ≤ Real.tan (∠ C A B / 2) * Real.tan (∠ A B C / 2) :=
    mul_nonneg (tan_half_pos hA0 hAπ).le (tan_half_pos hB0 hBπ).le
  have hposR : 0 ≤ (dist B C + dist C A - dist A B) / (dist B C + dist C A + dist A B) := by
    apply div_nonneg <;> linarith
  exact (sq_eq_sq₀ hposL hposR).mp hmul

/-- In a non-degenerate triangle `ABC`, the inradius divided by the radius of
the excircle tangent to `AB` equals `tan(A/2) · tan(B/2)`. -/
theorem inradius_div_exradius_eq_tan_mul {A B C : P} (h : ¬Collinear ℝ ({A, B, C} : Set P)) :
    inradius (dist B C) (dist C A) (dist A B) / exradius (dist B C) (dist C A) (dist A B) =
      Real.tan (∠ C A B / 2) * Real.tan (∠ A B C / 2) := by
  obtain ⟨ha, hb, hc, htri1, htri2, htri3⟩ := tri_sides h
  rw [inradius_div_exradius ha hb hc htri1 htri2 htri3, tan_half_angle_mul h]

/-- If `M` lies strictly between `A` and `B` and `C` is not on the line `AB`,
then `A`, `M`, `C` are not collinear. -/
theorem not_collinear_of_sbtw_left {A B C M : P} (h : ¬Collinear ℝ ({A, B, C} : Set P))
    (hM : Sbtw ℝ A M B) : ¬Collinear ℝ ({A, M, C} : Set P) := by
  intro hAMC
  rw [collinear_iff_of_mem (show A ∈ ({A, M, C} : Set P) by simp)] at hAMC
  obtain ⟨v, hv⟩ := hAMC
  obtain ⟨rM, hrM⟩ := hv M (by simp)
  obtain ⟨rC, hrC⟩ := hv C (by simp)
  obtain ⟨hW, hAMne, -⟩ := hM
  have hW' : M ∈ AffineMap.lineMap A B '' Set.Icc (0 : ℝ) 1 := hW
  obtain ⟨t, -, hMt⟩ := hW'
  rw [AffineMap.lineMap_apply] at hMt
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [zero_smul, zero_vadd] at hMt
    exact hAMne hMt.symm
  have hMtA : M -ᵥ A = t • (B -ᵥ A) := by rw [← hMt, vadd_vsub]
  have hrMA : M -ᵥ A = rM • v := by rw [hrM, vadd_vsub]
  have hB : B = (t⁻¹ * rM) • v +ᵥ A := by
    have h1 : B -ᵥ A = (t⁻¹ * rM) • v := by
      have h2 : t • (B -ᵥ A) = rM • v := by rw [← hMtA, ← hrMA]
      calc B -ᵥ A = t⁻¹ • (t • (B -ᵥ A)) := by
            rw [smul_smul, inv_mul_cancel₀ ht0, one_smul]
        _ = t⁻¹ • (rM • v) := by rw [h2]
        _ = (t⁻¹ * rM) • v := smul_smul _ _ _
    rw [← vsub_vadd B A, h1]
  apply h
  rw [collinear_iff_of_mem (show A ∈ ({A, B, C} : Set P) by simp)]
  refine ⟨v, fun p hp => ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl
  · exact ⟨0, by simp⟩
  · exact ⟨t⁻¹ * rM, hB⟩
  · exact ⟨rC, hrC⟩

/-- If `M` lies strictly between `A` and `B` and `C` is not on the line `AB`,
then `B`, `M`, `C` are not collinear. -/
theorem not_collinear_of_sbtw_right {A B C M : P} (h : ¬Collinear ℝ ({A, B, C} : Set P))
    (hM : Sbtw ℝ A M B) : ¬Collinear ℝ ({B, M, C} : Set P) :=
  not_collinear_of_sbtw_left (nc12 h) hM.symm

/-- The angle `∠CAM` equals `∠CAB` when `M` lies strictly between `A` and `B`. -/
theorem angle_left_eq_of_sbtw {A M B C : P} (hM : Sbtw ℝ A M B) : ∠ C A M = ∠ C A B := by
  obtain ⟨hW, hAMne, -⟩ := hM
  have hW' : M ∈ AffineMap.lineMap A B '' Set.Icc (0 : ℝ) 1 := hW
  obtain ⟨t, ht, hMt⟩ := hW'
  rw [AffineMap.lineMap_apply] at hMt
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [zero_smul, zero_vadd] at hMt
    exact hAMne hMt.symm
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  show InnerProductGeometry.angle (C -ᵥ A) (M -ᵥ A) =
    InnerProductGeometry.angle (C -ᵥ A) (B -ᵥ A)
  rw [← hMt, vadd_vsub]
  exact InnerProductGeometry.angle_smul_right_of_pos _ _ htpos

/-- The angles `∠AMC` and `∠BMC` are supplementary when `M` lies strictly
between `A` and `B`. -/
theorem angle_supplementary {A B C M : P} (hM : Sbtw ℝ A M B) :
    ∠ A M C + ∠ B M C = Real.pi := by
  have h := angle_add_angle_eq_pi_of_angle_eq_pi C hM.angle₁₂₃_eq_pi
  rwa [angle_comm C M A, angle_comm C M B] at h

snip end

problem imo1970_p1 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {P : Type*} [MetricSpace P] [NormedAddTorsor V P] (A B C M : P)
    (h : ¬Collinear ℝ ({A, B, C} : Set P)) (hM : Sbtw ℝ A M B) :
    inradius (dist M C) (dist C A) (dist A M) *
        inradius (dist M C) (dist C B) (dist B M) *
        exradius (dist B C) (dist C A) (dist A B) =
      inradius (dist B C) (dist C A) (dist A B) *
        exradius (dist M C) (dist C A) (dist A M) *
        exradius (dist M C) (dist C B) (dist B M) := by
  have hAMC : ¬Collinear ℝ ({A, M, C} : Set P) := not_collinear_of_sbtw_left h hM
  have hBMC : ¬Collinear ℝ ({B, M, C} : Set P) := not_collinear_of_sbtw_right h hM
  have hr := inradius_div_exradius_eq_tan_mul h
  have hr1 := inradius_div_exradius_eq_tan_mul hAMC
  have hr2 := inradius_div_exradius_eq_tan_mul hBMC
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := tri_sides h
  obtain ⟨g1', g2', g3', g4', g5', g6'⟩ := tri_sides hAMC
  obtain ⟨g1'', g2'', g3'', g4'', g5'', g6''⟩ := tri_sides hBMC
  have hrp : 0 < inradius (dist B C) (dist C A) (dist A B) :=
    inradius_pos g1 g2 g3 g4 g5 g6
  have hqp : 0 < exradius (dist B C) (dist C A) (dist A B) :=
    exradius_pos g1 g2 g3 g4 g5 g6
  have hr1p : 0 < inradius (dist M C) (dist C A) (dist A M) :=
    inradius_pos g1' g2' g3' g4' g5' g6'
  have hq1p : 0 < exradius (dist M C) (dist C A) (dist A M) :=
    exradius_pos g1' g2' g3' g4' g5' g6'
  have hr2p : 0 < inradius (dist M C) (dist C B) (dist B M) :=
    inradius_pos g1'' g2'' g3'' g4'' g5'' g6''
  have hq2p : 0 < exradius (dist M C) (dist C B) (dist B M) :=
    exradius_pos g1'' g2'' g3'' g4'' g5'' g6''
  have e_r : inradius (dist B C) (dist C A) (dist A B) =
      (Real.tan (∠ C A B / 2) * Real.tan (∠ A B C / 2)) *
        exradius (dist B C) (dist C A) (dist A B) := by
    rw [div_eq_iff hqp.ne'] at hr
    exact hr
  have e_r1 : inradius (dist M C) (dist C A) (dist A M) =
      (Real.tan (∠ C A M / 2) * Real.tan (∠ A M C / 2)) *
        exradius (dist M C) (dist C A) (dist A M) := by
    rw [div_eq_iff hq1p.ne'] at hr1
    exact hr1
  have e_r2 : inradius (dist M C) (dist C B) (dist B M) =
      (Real.tan (∠ C B M / 2) * Real.tan (∠ B M C / 2)) *
        exradius (dist M C) (dist C B) (dist B M) := by
    rw [div_eq_iff hq2p.ne'] at hr2
    exact hr2
  have hφ : Real.tan (∠ B M C / 2) = (Real.tan (∠ A M C / 2))⁻¹ := by
    have hsupp : ∠ A M C + ∠ B M C = Real.pi := angle_supplementary hM
    have hhalf : ∠ B M C / 2 = Real.pi / 2 - ∠ A M C / 2 := by linarith
    rw [hhalf, Real.tan_pi_div_two_sub]
  have hθ : Real.tan (∠ A M C / 2) ≠ 0 :=
    (tan_half_pos (angle_pos_of_not_collinear hAMC)
      (angle_lt_pi_of_not_collinear hAMC)).ne'
  have hkey : Real.tan (∠ C A M / 2) * Real.tan (∠ A M C / 2) *
      (Real.tan (∠ C B M / 2) * Real.tan (∠ B M C / 2)) =
      Real.tan (∠ C A B / 2) * Real.tan (∠ A B C / 2) := by
    rw [angle_left_eq_of_sbtw hM, angle_left_eq_of_sbtw hM.symm, hφ, angle_comm C B A]
    linear_combination Real.tan (∠ C A B / 2) * Real.tan (∠ A B C / 2) * mul_inv_cancel₀ hθ
  rw [e_r, e_r1, e_r2]
  linear_combination (exradius (dist B C) (dist C A) (dist A B) *
    exradius (dist M C) (dist C A) (dist A M) * exradius (dist M C) (dist C B) (dist B M)) * hkey

end Imo1970P1
