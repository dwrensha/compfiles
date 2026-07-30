/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Geometry.Euclidean.Sphere.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import ProblemExtraction

@[expose] public section

problem_file {
  tags := [.Geometry]
}

/-!
# International Mathematical Olympiad 2019, Problem 6

Let `ABC` be a triangle with incenter `I` and incircle `ω`. Let `D`, `E`, `F` denote the
tangency points of `ω` with `BC`, `CA`, `AB`. The line through `D` perpendicular to `EF`
meets `ω` again at `R` (other than `D`), and line `AR` meets `ω` again at `P` (other than
`R`). Suppose the circumcircles of `△PCE` and `△PBF` meet again at `Q` (other than `P`).
Prove that lines `DI` and `PQ` meet on the external `∠A`-bisector.

## Formulation notes

We work in the complex plane `ℂ`, normalized (by a similarity transformation) so that the
incircle `ω` is the unit circle centered at the origin, hence `I = 0`. The triangle is then
*defined* by its contact triangle: the vertices `A`, `B`, `C` are characterized by the
tangency conditions (side `CA` is tangent to `ω` at `E`, side `AB` is tangent to `ω` at `F`,
etc., so `A` is the intersection of the tangent lines at `E` and at `F`, and similarly for
`B` and `C`). The external `∠A`-bisector is the line through `A` perpendicular to `AI`,
and since `I = 0` the conclusion states that the lines `DI` and `PQ` have a common point
`T` with `⟪T - A, A⟫_ℝ = 0`.

The explicit nonvanishing hypotheses are the nondegeneracy conditions of the configuration
(in the IMO problem these are guaranteed by acuteness of `ABC` together with `AB ≠ AC`;
`D^2 + E * F ≠ 0` corresponds to the excluded case `AB = AC`, in which `DI` would be
parallel to the external bisector).

We follow the complex-number solution of Evan Chen and Yang Liu
(<https://web.evanchen.cc/exams/IMO-2019-notes.pdf>): with `D = x`, `E = y`, `F = z` on the
unit circle one has `A = 2yz/(y+z)`, `R = -yz/x`, `P = yz(2x+y+z)/(2yz+x(y+z))`, and one
verifies directly that the point `T = x²/(x²+yz) · 4yz/(y+z)` on line `DI` satisfies
`PT ⟂ O_B O_C`, where `O_B`, `O_C` are the circumcenters of `△PBF` and `△PCE`, so that
`T` lies on the common chord `PQ` of the two circumcircles.
-/

open Affine EuclideanGeometry ComplexConjugate InnerProductSpace

namespace Imo2019P6

snip begin


/-! ### Basic unit-circle facts -/

lemma ne_zero_of_norm_eq_one {z : ℂ} (h : ‖z‖ = 1) : z ≠ 0 := by
  intro hz
  rw [hz, norm_zero] at h
  norm_num at h

lemma mul_conj_eq_one_of_norm_eq_one {z : ℂ} (h : ‖z‖ = 1) : z * conj z = 1 := by
  have h1 : (Complex.normSq z : ℂ) = 1 := by
    have hsq : Complex.normSq z = 1 := by
      rw [← Complex.norm_mul_self_eq_normSq, h, mul_one]
    exact_mod_cast hsq
  rw [Complex.mul_conj, h1]

lemma conj_eq_inv_of_norm_eq_one {z : ℂ} (h : ‖z‖ = 1) : conj z = z⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact mul_conj_eq_one_of_norm_eq_one h)

lemma conj_eq_zero_iff {z : ℂ} : conj z = 0 ↔ z = 0 := by
  constructor
  · intro h
    have h2 := congrArg conj h
    rwa [Complex.conj_conj, map_zero] at h2
  · rintro rfl
    exact map_zero _

/-- If a complex number has real part `0`, it equals `i` times its imaginary part. -/
lemma eq_im_mul_I_of_re_eq_zero {z : ℂ} (h : z.re = 0) : z = (z.im : ℂ) * Complex.I := by
  have h2 := Complex.re_add_im z
  rw [h, Complex.ofReal_zero, zero_add] at h2
  exact h2.symm

/-- If `z + conj z = 0` then `z.re = 0`. -/
lemma re_eq_zero_of_add_conj_eq_zero {z : ℂ} (h : z + conj z = 0) : z.re = 0 := by
  have h2 := Complex.add_conj z
  rw [h, eq_comm, Complex.ofReal_eq_zero, mul_eq_zero] at h2
  rcases h2 with h2 | h2
  · norm_num at h2
  · exact h2

/-- If `z.re = 0` then `z + conj z = 0`. -/
lemma add_conj_eq_zero_of_re_eq_zero {z : ℂ} (h : z.re = 0) : z + conj z = 0 := by
  have h2 := Complex.add_conj z
  rw [h, mul_zero, Complex.ofReal_zero] at h2
  exact h2

/-- Orthogonality from a complex identity: `⟪u, v⟫_ℝ = 0` if `v * conj u` is purely
imaginary. -/
lemma inner_eq_zero_of {u v : ℂ} (h : v * conj u + conj (v * conj u) = 0) :
    ⟪u, v⟫_ℝ = 0 := by
  rw [Complex.inner]
  exact re_eq_zero_of_add_conj_eq_zero h

/-! ### Geometric helper lemmas -/

/-- The intersection of the tangent lines to the unit circle at two points `E`, `F`. -/
lemma tangent_inter_eq {A E F : ℂ} (hE0 : E ≠ 0) (hF0 : F ≠ 0)
    (hEc : E * conj E = 1) (hFc : F * conj F = 1)
    (hEF : E ≠ F) (hEF2 : E + F ≠ 0)
    (hAE : (E * conj (A - E)).re = 0) (hAF : (F * conj (A - F)).re = 0) :
    A = 2 * E * F / (E + F) ∧ conj A = 2 / (E + F) := by
  have hEi : conj E = E⁻¹ := eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hEc)
  have hFi : conj F = F⁻¹ := eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hFc)
  have eqE : E * conj (A - E) + conj (E * conj (A - E)) = 0 :=
    add_conj_eq_zero_of_re_eq_zero hAE
  simp only [map_mul, map_sub, Complex.conj_conj] at eqE
  have eqE2 : E * conj A + A * conj E = 2 := by linear_combination eqE + 2 * hEc
  rw [hEi] at eqE2
  have eqE3 : A + E ^ 2 * conj A = 2 * E := by
    have h1 : E * E⁻¹ = 1 := mul_inv_cancel₀ hE0
    linear_combination E * eqE2 - A * h1
  have eqF : F * conj (A - F) + conj (F * conj (A - F)) = 0 :=
    add_conj_eq_zero_of_re_eq_zero hAF
  simp only [map_mul, map_sub, Complex.conj_conj] at eqF
  have eqF2 : F * conj A + A * conj F = 2 := by linear_combination eqF + 2 * hFc
  rw [hFi] at eqF2
  have eqF3 : A + F ^ 2 * conj A = 2 * F := by
    have h1 : F * F⁻¹ = 1 := mul_inv_cancel₀ hF0
    linear_combination F * eqF2 - A * h1
  have hsub : (E ^ 2 - F ^ 2) * conj A = 2 * (E - F) := by
    linear_combination eqE3 - eqF3
  have hsq : E ^ 2 - F ^ 2 = (E - F) * (E + F) := by ring
  have hEF0 : E - F ≠ 0 := sub_ne_zero.mpr hEF
  have hstep : (E - F) * ((E + F) * conj A) = (E - F) * 2 := by
    linear_combination hsub - conj A * hsq
  have hmid : (E + F) * conj A = 2 := mul_left_cancel₀ hEF0 hstep
  have hconjA : conj A = 2 / (E + F) :=
    EuclideanDomain.eq_div_of_mul_eq_left hEF2 (by rw [mul_comm]; exact hmid)
  have hA : A = 2 * E * F / (E + F) := by
    have e : A = 2 * E - E ^ 2 * conj A := by linear_combination eqE3
    rw [e, hconjA]
    field_simp [hEF2]
    ring
  exact ⟨hA, hconjA⟩

/-- The second intersection with the unit circle of the line through `D` perpendicular
to `EF`. -/
lemma R_eq {D E F R : ℂ} (hD0 : D ≠ 0) (_hE0 : E ≠ 0) (_hF0 : F ≠ 0)
    (hDc : D * conj D = 1) (hEc : E * conj E = 1) (hFc : F * conj F = 1)
    (hRD : R ≠ D) (hEF : E ≠ F) (hRc : R * conj R = 1)
    (hperp : ((F - E) * conj (R - D)).re = 0) : R = -(E * F) / D := by
  have hFE : F - E ≠ 0 := sub_ne_zero.mpr (Ne.symm hEF)
  have eq1 : (F - E) * conj (R - D) + conj ((F - E) * conj (R - D)) = 0 :=
    add_conj_eq_zero_of_re_eq_zero hperp
  simp only [map_mul, map_sub, Complex.conj_conj] at eq1
  -- multiply out the conjugate of `F - E` using `E * conj E = 1`, `F * conj F = 1`
  have eqA : (F - E) * ((E * F) * (conj R - conj D)) = (F - E) * (R - D) := by
    have h1 : (conj F - conj E) * (E * F) = E - F := by
      linear_combination E * hFc - F * hEc
    linear_combination (E * F) * eq1 - (R - D) * h1
  have eqA' : (E * F) * (conj R - conj D) = R - D := mul_left_cancel₀ hFE eqA
  have eqB : (conj R - conj D) * (R * D) = D - R := by
    linear_combination D * hRc - R * hDc
  have key : (R - D) * (R * D + E * F) = 0 := by
    linear_combination E * F * eqB - R * D * eqA'
  rcases mul_eq_zero.mp key with h | h
  · exact absurd (eq_of_sub_eq_zero h) hRD
  · have h2 : R * D = -(E * F) := by linear_combination h
    have h3 : R = -(E * F) / D := by
      apply EuclideanDomain.eq_div_of_mul_eq_left hD0
      linear_combination h2
    exact h3

/-- `1 - R * conj A ≠ 0` when `R` is on the unit circle and `A ≠ R`. -/
lemma one_sub_mul_conj_ne_zero {A R : ℂ} (hRc : R * conj R = 1) (hAR : A ≠ R) :
    1 - R * conj A ≠ 0 := by
  intro h
  have h1 : R * conj A = 1 := by linear_combination -h
  have h2 : conj A = R⁻¹ := eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact h1)
  have hRi : conj R = R⁻¹ := eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hRc)
  have h3 : conj A = conj R := by rw [h2, hRi]
  have h4 : A = R := by
    have h5 := congrArg conj h3
    rwa [Complex.conj_conj, Complex.conj_conj] at h5
  exact hAR h4

/-- A point on `line[ℝ, A, R]` is a real affine combination of `A` and `R`. -/
lemma exists_real_smul_of_mem_line {A R P : ℂ} (h : P ∈ line[ℝ, A, R]) :
    ∃ s : ℝ, P = A + s • (R - A) := by
  have hs : P -ᵥ A ∈ (line[ℝ, A, R]).direction :=
    AffineSubspace.vsub_mem_direction h (left_mem_affineSpan_pair ℝ A R)
  rw [direction_affineSpan, vectorSpan_pair] at hs
  obtain ⟨s, hs'⟩ := Submodule.mem_span_singleton.mp hs
  refine ⟨-s, ?_⟩
  have e : P -ᵥ A = (-s) • (R -ᵥ A) := by
    rw [← hs']
    rw [← neg_vsub_eq_vsub_rev R A]
    rw [smul_neg, neg_smul]
  have e2 : P = (-s) • (R - A) + A := by
    have e3 : P = (-s) • (R -ᵥ A) +ᵥ A := by
      rw [← e]
      exact (vsub_vadd P A).symm
    rwa [vsub_eq_sub, vadd_eq_add] at e3
  rw [e2, add_comm]

/-- The second intersection with the unit circle of the line `AR`. -/
lemma P_eq {P A R : ℂ} (hP0 : P ≠ 0) (hR0 : R ≠ 0)
    (hPc : P * conj P = 1) (hRc : R * conj R = 1) (hPR : P ≠ R) (hAR : A ≠ R)
    (hcol : ∃ s : ℝ, P = A + s • (R - A)) : P = (A - R) / (1 - R * conj A) := by
  obtain ⟨s, hs⟩ := hcol
  have hPi : conj P = P⁻¹ := eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hPc)
  have hRi : conj R = R⁻¹ := eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hRc)
  have key : (P - R) * conj (A - R) = (A - R) * conj (P - R) := by
    rw [hs]
    have e : A + s • (R - A) - R = (1 - (s : ℂ)) * (A - R) := by
      rw [Complex.real_smul]
      ring
    rw [e]
    simp only [map_mul, map_sub, map_one, Complex.conj_ofReal]
    ring
  have hconjPR : conj (P - R) = (R - P) / (P * R) := by
    rw [map_sub, hPi, hRi]
    field_simp [hP0, hR0]
  rw [hconjPR] at key
  have hPR0 : P - R ≠ 0 := sub_ne_zero.mpr hPR
  have key2 : conj (A - R) = -(A - R) / (P * R) := by
    have e : (A - R) * ((R - P) / (P * R)) = (P - R) * (-(A - R) / (P * R)) := by
      field_simp [hP0, hR0]
      ring
    rw [e] at key
    exact mul_left_cancel₀ hPR0 key
  have key3 : P * (R * conj A - 1) = R - A := by
    have e1 : conj (A - R) = conj A - R⁻¹ := by rw [map_sub, hRi]
    rw [e1] at key2
    have e2 : (conj A - R⁻¹) * (P * R) = P * (R * conj A - 1) := by
      field_simp [hR0]
    have e3 : (conj A - R⁻¹) * (P * R) = R - A := by
      rw [key2]
      field_simp [hP0, hR0]
      ring
    rw [e2] at e3
    exact e3
  have key4 : P * (1 - R * conj A) = A - R := by linear_combination -key3
  have h1R : 1 - R * conj A ≠ 0 := one_sub_mul_conj_ne_zero hRc hAR
  exact EuclideanDomain.eq_div_of_mul_eq_left h1R key4

/-- In two dimensions, a vector orthogonal to two sides of a genuine triangle is zero. -/
lemma eq_zero_of_inner_eq_zero_of_not_collinear {d u v w : ℂ}
    (hnc : ¬Collinear ℝ ({u, v, w} : Set ℂ))
    (h1 : ⟪d, v - u⟫_ℝ = 0) (h2 : ⟪d, w - u⟫_ℝ = 0) : d = 0 := by
  rw [Complex.inner] at h1 h2
  by_contra hd
  have hcd : conj d ≠ 0 := by
    intro h
    exact hd ((conj_eq_zero_iff).mp h)
  set a := ((v - u) * conj d).im with ha_def
  set b := ((w - u) * conj d).im with hb_def
  have ha : (v - u) * conj d = (a : ℂ) * Complex.I := eq_im_mul_I_of_re_eq_zero h1
  have hb : (w - u) * conj d = (b : ℂ) * Complex.I := eq_im_mul_I_of_re_eq_zero h2
  have key : ((b : ℂ) * (v - u) - (a : ℂ) * (w - u)) * conj d = 0 := by
    linear_combination (b : ℂ) * ha - (a : ℂ) * hb
  have hcomb : (b : ℂ) * (v - u) = (a : ℂ) * (w - u) := by
    rcases mul_eq_zero.mp key with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hcd
  by_cases ha0 : a = 0
  · -- `a = 0` forces `v = u`, contradicting non-collinearity
    rw [ha0, Complex.ofReal_zero, zero_mul] at ha
    have hvu : v = u := by
      rcases mul_eq_zero.mp ha with h | h
      · exact eq_of_sub_eq_zero h
      · exact absurd h hcd
    apply hnc
    rw [← hvu]
    have hset : ({v, v, w} : Set ℂ) = {v, w} := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [hset]
    exact collinear_pair ℝ v w
  · -- otherwise `w` lies on line `uv`, contradicting non-collinearity
    apply hnc
    have hmem : w ∈ line[ℝ, u, v] := by
      have h := AffineMap.lineMap_mem_affineSpan_pair (a⁻¹ * b) u v
      rw [AffineMap.lineMap_apply_module'] at h
      have hw : w = (a⁻¹ * b : ℝ) • (v - u) + u := by
        have e1 : w - u = ((b / a : ℝ) : ℂ) * (v - u) := by
          have ha0' : (a : ℂ) ≠ 0 := by
            intro h'
            rw [Complex.ofReal_eq_zero] at h'
            exact ha0 h'
          apply mul_left_cancel₀ ha0'
          have e2 : (a : ℂ) * (w - u) = (b : ℂ) * (v - u) := hcomb.symm
          rw [e2]
          have e3 : ((b / a : ℝ) : ℂ) = (b : ℂ) / (a : ℂ) := by rw [Complex.ofReal_div]
          rw [e3]
          field_simp [ha0']
        have hab : ((a⁻¹ * b : ℝ) : ℂ) = ((b / a : ℝ) : ℂ) := by
          have : (a⁻¹ * b : ℝ) = b / a := by rw [div_eq_mul_inv, mul_comm]
          rw [this]
        rw [Complex.real_smul, hab, ← e1]
        exact (sub_add_cancel w u).symm
      rwa [← hw] at h
    have hc : Collinear ℝ ({u, v, w} : Set ℂ) := by
      have h' := collinear_insert_of_mem_affineSpan_pair hmem
      have hset : ({w, u, v} : Set ℂ) = {u, v, w} := by
        ext x
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        tauto
      rwa [hset] at h'
    exact hc

/-- Two vectors in the plane perpendicular to the same nonzero vector are parallel. -/
lemma exists_real_smul_of_inner_eq_zero {v w₁ w₂ : ℂ} (hv : v ≠ 0)
    (h1 : ⟪w₁, v⟫_ℝ = 0) (h2 : ⟪w₂, v⟫_ℝ = 0) (hw1 : w₁ ≠ 0) :
    ∃ c : ℝ, w₂ = c • w₁ := by
  rw [Complex.inner] at h1 h2
  have ha : v * conj w₁ = (((v * conj w₁).im : ℝ) : ℂ) * Complex.I := eq_im_mul_I_of_re_eq_zero h1
  have hb : v * conj w₂ = (((v * conj w₂).im : ℝ) : ℂ) * Complex.I := eq_im_mul_I_of_re_eq_zero h2
  set a := (v * conj w₁).im with ha_def
  set b := (v * conj w₂).im with hb_def
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, Complex.ofReal_zero, zero_mul] at ha
    have hcw : conj w₁ = 0 := by
      rcases mul_eq_zero.mp ha with h' | h'
      · exact absurd h' hv
      · exact h'
    exact hw1 (conj_eq_zero_iff.mp hcw)
  have key : (b : ℂ) * conj w₁ = (a : ℂ) * conj w₂ := by
    have e : v * ((b : ℂ) * conj w₁ - (a : ℂ) * conj w₂) = 0 := by
      linear_combination (b : ℂ) * ha - (a : ℂ) * hb
    rcases mul_eq_zero.mp e with h' | h'
    · exact absurd h' hv
    · exact sub_eq_zero.mp h'
  refine ⟨b / a, ?_⟩
  have ha0' : (a : ℂ) ≠ 0 := by
    intro h'
    rw [Complex.ofReal_eq_zero] at h'
    exact ha0 h'
  have e1 : conj w₂ = ((b / a : ℝ) : ℂ) * conj w₁ := by
    apply mul_left_cancel₀ ha0'
    have e2 : (a : ℂ) * conj w₂ = (b : ℂ) * conj w₁ := key.symm
    rw [e2]
    have e3 : ((b / a : ℝ) : ℂ) = (b : ℂ) / (a : ℂ) := by rw [Complex.ofReal_div]
    rw [e3]
    field_simp [ha0']
  have e4 : w₂ = ((b / a : ℝ) : ℂ) * w₁ := by
    have h := congrArg conj e1
    rwa [Complex.conj_conj, map_mul, Complex.conj_ofReal, Complex.conj_conj] at h
  rw [e4, Complex.real_smul]

/-- A point equidistant from `u`, `v`, `w` is unique (two dimensions). -/
lemma circumcenter_unique {u v w O₁ O₂ : ℂ} (hnc : ¬Collinear ℝ ({u, v, w} : Set ℂ))
    (h₁u : dist O₁ u = dist O₁ v) (h₁w : dist O₁ u = dist O₁ w)
    (h₂u : dist O₂ u = dist O₂ v) (h₂w : dist O₂ u = dist O₂ w) : O₁ = O₂ := by
  rw [dist_eq_norm, dist_eq_norm] at h₁u h₁w h₂u h₂w
  have s1 : ‖O₁ - u‖ ^ 2 = ‖O₁ - v‖ ^ 2 := by rw [h₁u]
  have s1' : ‖O₁ - u‖ ^ 2 = ‖O₁ - w‖ ^ 2 := by rw [h₁w]
  have s2 : ‖O₂ - u‖ ^ 2 = ‖O₂ - v‖ ^ 2 := by rw [h₂u]
  have s2' : ‖O₂ - u‖ ^ 2 = ‖O₂ - w‖ ^ 2 := by rw [h₂w]
  rw [norm_sub_sq_real, norm_sub_sq_real] at s1 s1' s2 s2'
  have e1 : ⟪O₁ - O₂, v - u⟫_ℝ = 0 := by
    simp only [inner_sub_left, inner_sub_right]
    linarith
  have e2 : ⟪O₁ - O₂, w - u⟫_ℝ = 0 := by
    simp only [inner_sub_left, inner_sub_right]
    linarith
  have hd : O₁ - O₂ = 0 := eq_zero_of_inner_eq_zero_of_not_collinear hnc e1 e2
  exact eq_of_sub_eq_zero hd

/-- The common chord of two intersecting circles is perpendicular to the line of
centers. -/
lemma inner_sub_eq_zero_of_dist_eq {P Q O₁ O₂ : ℂ}
    (h₁ : dist Q O₁ = dist P O₁) (h₂ : dist Q O₂ = dist P O₂) :
    ⟪Q - P, O₁ - O₂⟫_ℝ = 0 := by
  rw [dist_eq_norm, dist_eq_norm] at h₁ h₂
  have s1 : ‖Q - O₁‖ ^ 2 = ‖P - O₁‖ ^ 2 := by rw [h₁]
  have s2 : ‖Q - O₂‖ ^ 2 = ‖P - O₂‖ ^ 2 := by rw [h₂]
  rw [norm_sub_sq_real, norm_sub_sq_real] at s1 s2
  simp only [inner_sub_left, inner_sub_right]
  linarith

/-- Equidistance from a complex polynomial identity. -/
lemma dist_eq_of_conj_mul_eq {O u v : ℂ}
    (h : conj (O - u) * (O - u) = conj (O - v) * (O - v)) : dist O u = dist O v := by
  rw [dist_eq_norm, dist_eq_norm, Complex.norm_def, Complex.norm_def]
  congr 1
  have h2 : ∀ z : ℂ, Complex.normSq z = (conj z * z).re := by
    intro z
    rw [← Complex.normSq_eq_conj_mul_self]
    exact (Complex.ofReal_re _).symm
  rw [h2, h2, h]

snip end

problem imo2019_p6
    {D E F : ℂ} (hDn : ‖D‖ = 1) (hEn : ‖E‖ = 1) (hFn : ‖F‖ = 1)
    (hDE : D ≠ E) (hDF : D ≠ F) (hEF : E ≠ F)
    (hDE2 : D + E ≠ 0) (hDF2 : D + F ≠ 0) (hEF2 : E + F ≠ 0)
    (hD2 : D ^ 2 + E * F ≠ 0)
    {A B C : ℂ}
    (hAtE : ⟪A - E, E⟫_ℝ = 0) (hAtF : ⟪A - F, F⟫_ℝ = 0)
    (hBtD : ⟪B - D, D⟫_ℝ = 0) (hBtF : ⟪B - F, F⟫_ℝ = 0)
    (hCtD : ⟪C - D, D⟫_ℝ = 0) (hCtE : ⟪C - E, E⟫_ℝ = 0)
    {R : ℂ} (hRn : ‖R‖ = 1) (hRD : R ≠ D) (hRperp : ⟪R - D, F - E⟫_ℝ = 0)
    {P : ℂ} (hPn : ‖P‖ = 1) (hPR : P ≠ R) (hAR : A ≠ R) (hPl : P ∈ line[ℝ, A, R])
    {Q : ℂ} (hQP : Q ≠ P)
    (hQCE : Cospherical ({P, C, E, Q} : Set ℂ))
    (hQBF : Cospherical ({P, B, F, Q} : Set ℂ))
    (hPCE : ¬Collinear ℝ ({P, C, E} : Set ℂ))
    (hPBF : ¬Collinear ℝ ({P, B, F} : Set ℂ)) :
    ∃ T : ℂ, T ∈ line[ℝ, D, (0 : ℂ)] ∧ T ∈ line[ℝ, P, Q] ∧ ⟪T - A, A⟫_ℝ = 0 := by
  -- basic nonvanishing facts
  have hD0 : D ≠ 0 := ne_zero_of_norm_eq_one hDn
  have hE0 : E ≠ 0 := ne_zero_of_norm_eq_one hEn
  have hF0 : F ≠ 0 := ne_zero_of_norm_eq_one hFn
  have hP0 : P ≠ 0 := ne_zero_of_norm_eq_one hPn
  have hR0 : R ≠ 0 := ne_zero_of_norm_eq_one hRn
  have hDc : D * conj D = 1 := mul_conj_eq_one_of_norm_eq_one hDn
  have hEc : E * conj E = 1 := mul_conj_eq_one_of_norm_eq_one hEn
  have hFc : F * conj F = 1 := mul_conj_eq_one_of_norm_eq_one hFn
  have hPc : P * conj P = 1 := mul_conj_eq_one_of_norm_eq_one hPn
  have hRc : R * conj R = 1 := mul_conj_eq_one_of_norm_eq_one hRn
  have hDi : conj D = D⁻¹ := conj_eq_inv_of_norm_eq_one hDn
  have hEi : conj E = E⁻¹ := conj_eq_inv_of_norm_eq_one hEn
  have hFi : conj F = F⁻¹ := conj_eq_inv_of_norm_eq_one hFn
  -- the vertices as intersections of tangent lines
  rw [Complex.inner] at hAtE hAtF hBtD hBtF hCtD hCtE hRperp
  obtain ⟨hA, hconjA⟩ := tangent_inter_eq hE0 hF0 hEc hFc hEF hEF2 hAtE hAtF
  obtain ⟨hB, -⟩ := tangent_inter_eq hD0 hF0 hDc hFc hDF hDF2 hBtD hBtF
  obtain ⟨hC, -⟩ := tangent_inter_eq hD0 hE0 hDc hEc hDE hDE2 hCtD hCtE
  -- the point `R`
  have hR : R = -(E * F) / D := R_eq hD0 hE0 hF0 hDc hEc hFc hRD hEF hRc hRperp
  -- the point `P`
  obtain ⟨s, hs⟩ := exists_real_smul_of_mem_line hPl
  have hP1 : P = (A - R) / (1 - R * conj A) := P_eq hP0 hR0 hPc hRc hPR hAR ⟨s, hs⟩
  have h1R : 1 - R * conj A ≠ 0 := one_sub_mul_conj_ne_zero hRc hAR
  have hPden : 2 * E * F + D * (E + F) ≠ 0 := by
    have e : 1 - R * conj A = (2 * E * F + D * (E + F)) / (D * (E + F)) := by
      rw [hR, hconjA]
      field_simp [hD0, hEF2]
      ring
    rw [e] at h1R
    exact (div_ne_zero_iff.mp h1R).1
  have hP : P = E * F * (2 * D + E + F) / (2 * E * F + D * (E + F)) := by
    rw [hP1, hR, hconjA, hA]
    field_simp [hD0, hE0, hF0, hEF2, hPden]
    ring
  have h2DEF : 2 * D + E + F ≠ 0 := by
    intro h
    rw [hP, h] at hPn
    simp at hPn
  have h2D : 2 * D - E - F ≠ 0 := by
    intro h
    have h1 : 2 * D = E + F := by linear_combination h
    have h2 : 2 * D⁻¹ = E⁻¹ + F⁻¹ := by
      have e := congrArg conj h1
      simp only [map_ofNat, map_mul, map_add, hDi, hEi, hFi] at e
      exact e
    have h3 : E * F = D ^ 2 := by
      have h4 : (2 * D⁻¹) * (D * (E * F)) = (E⁻¹ + F⁻¹) * (D * (E * F)) := by rw [h2]
      have h5 : (2 * D⁻¹) * (D * (E * F)) = 2 * (E * F) := by
        have hD1 : D⁻¹ * D = 1 := inv_mul_cancel₀ hD0
        linear_combination 2 * (E * F) * hD1
      have h6 : (E⁻¹ + F⁻¹) * (D * (E * F)) = D * (E + F) := by
        have hE1 : E⁻¹ * E = 1 := inv_mul_cancel₀ hE0
        have hF1 : F⁻¹ * F = 1 := inv_mul_cancel₀ hF0
        linear_combination (D * F) * hE1 + (D * E) * hF1
      rw [h5, h6] at h4
      rw [← h1] at h4
      linear_combination h4 / 2
    have h7 : (E - F) ^ 2 = 0 := by
      have e : (E - F) ^ 2 = (E + F) ^ 2 - 4 * (E * F) := by ring
      rw [← h1, h3] at e
      linear_combination e
    have h8 : E - F = 0 := sq_eq_zero_iff.mp h7
    exact hEF (eq_of_sub_eq_zero h8)
  -- the circumcenters of `△PBF` and `△PCE`, and the meeting point `T`
  set OB : ℂ := (D - F) / (D + F) * (E * F * (2 * D + E + F) / ((E - F) * (D + E))) with hOB
  set OC : ℂ := (D - E) / (D + E) * (E * F * (2 * D + E + F) / ((F - E) * (D + F))) with hOC
  set T : ℂ := D ^ 2 / (D ^ 2 + E * F) * (4 * E * F / (E + F)) with hTdef
  have hEF0 : E - F ≠ 0 := sub_ne_zero.mpr hEF
  have hFE0 : F - E ≠ 0 := sub_ne_zero.mpr (Ne.symm hEF)
  have hDEDF : (D + E) * (D + F) ≠ 0 := mul_ne_zero hDE2 hDF2

  -- conjugates of the polynomial factors appearing as denominators
  have c1 : conj (E + F) = (E + F) / (E * F) := by
    rw [map_add, hEi, hFi]
    field_simp [hE0, hF0]
    ring
  have c2 : conj (2 * D + E + F) = (2 * E * F + D * (E + F)) / (D * E * F) := by
    simp only [map_add, map_mul, map_ofNat, hDi, hEi, hFi]
    field_simp (disch := first
    | assumption
    | (apply mul_ne_zero <;> (first
      | assumption
      | (apply mul_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (apply pow_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring))))
    | (apply pow_ne_zero <;> (first
      | assumption
      | (apply mul_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (apply pow_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring))))
    | (convert hPden using 1; ring)
    | (convert h2DEF using 1; ring)
    | (convert hD2 using 1; ring)
    | (convert hDEDF using 1; ring)
    | (convert hEF2 using 1; ring)
    | (convert hDE2 using 1; ring)
    | (convert hDF2 using 1; ring)
    | (convert hEF0 using 1; ring)
    | (convert hFE0 using 1; ring)
    | (convert h2D using 1; ring)
    | (convert hD0 using 1; ring)
    | (convert hE0 using 1; ring)
    | (convert hF0 using 1; ring)) []
    try ring
  have c3 : conj (2 * E * F + D * (E + F)) = (2 * D + E + F) / (D * E * F) := by
    simp only [map_add, map_mul, map_ofNat, hDi, hEi, hFi]
    field_simp (disch := first
    | assumption
    | (apply mul_ne_zero <;> (first
      | assumption
      | (apply mul_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (apply pow_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring))))
    | (apply pow_ne_zero <;> (first
      | assumption
      | (apply mul_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (apply pow_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring))))
    | (convert hPden using 1; ring)
    | (convert h2DEF using 1; ring)
    | (convert hD2 using 1; ring)
    | (convert hDEDF using 1; ring)
    | (convert hEF2 using 1; ring)
    | (convert hDE2 using 1; ring)
    | (convert hDF2 using 1; ring)
    | (convert hEF0 using 1; ring)
    | (convert hFE0 using 1; ring)
    | (convert h2D using 1; ring)
    | (convert hD0 using 1; ring)
    | (convert hE0 using 1; ring)
    | (convert hF0 using 1; ring)) []
    try ring
  have c4 : conj (D ^ 2 + E * F) = (D ^ 2 + E * F) / (D ^ 2 * E * F) := by
    simp only [map_add, map_pow, map_mul, hDi, hEi, hFi]
    field_simp (disch := first
    | assumption
    | (apply mul_ne_zero <;> (first
      | assumption
      | (apply mul_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (apply pow_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring))))
    | (apply pow_ne_zero <;> (first
      | assumption
      | (apply mul_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (apply pow_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring))))
    | (convert hPden using 1; ring)
    | (convert h2DEF using 1; ring)
    | (convert hD2 using 1; ring)
    | (convert hDEDF using 1; ring)
    | (convert hEF2 using 1; ring)
    | (convert hDE2 using 1; ring)
    | (convert hDF2 using 1; ring)
    | (convert hEF0 using 1; ring)
    | (convert hFE0 using 1; ring)
    | (convert h2D using 1; ring)
    | (convert hD0 using 1; ring)
    | (convert hE0 using 1; ring)
    | (convert hF0 using 1; ring)) []
    try ring
  have c5 : conj (D + E) = (D + E) / (D * E) := by
    rw [map_add, hDi, hEi]
    field_simp [hD0, hE0]
    ring
  have c6 : conj (D + F) = (D + F) / (D * F) := by
    rw [map_add, hDi, hFi]
    field_simp [hD0, hF0]
    ring
  have c7 : conj (E - F) = (F - E) / (E * F) := by
    rw [map_sub, hEi, hFi]
    field_simp [hE0, hF0]
  have c8 : conj (F - E) = (E - F) / (E * F) := by
    rw [map_sub, hFi, hEi]
    field_simp [hE0, hF0]

  -- single-fraction forms of the differences involving the circumcenters
  have hOBP : OB - P = E * F * (2 * D + E + F) *
      (2 * D ^ 2 * F - D * E ^ 2 + D * E * F - E ^ 2 * F - E * F ^ 2) /
      ((D + E) * (D + F) * (E - F) * (2 * E * F + D * (E + F))) := by
    rw [hOB, hP]
    field_simp (disch := first
    | assumption
    | (apply mul_ne_zero <;> (first
      | assumption
      | (apply mul_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (apply pow_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring))))
    | (apply pow_ne_zero <;> (first
      | assumption
      | (apply mul_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (apply pow_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring))))
    | (convert hPden using 1; ring)
    | (convert h2DEF using 1; ring)
    | (convert hD2 using 1; ring)
    | (convert hDEDF using 1; ring)
    | (convert hEF2 using 1; ring)
    | (convert hDE2 using 1; ring)
    | (convert hDF2 using 1; ring)
    | (convert hEF0 using 1; ring)
    | (convert hFE0 using 1; ring)
    | (convert h2D using 1; ring)
    | (convert hD0 using 1; ring)
    | (convert hE0 using 1; ring)
    | (convert hF0 using 1; ring)) []
    try ring
  have hOBB : OB - B = F * (2 * D ^ 2 * F - D * E ^ 2 + D * E * F - E ^ 2 * F - E * F ^ 2) /
      ((D + E) * (D + F) * (E - F)) := by
    rw [hOB, hB]
    field_simp (disch := first
    | assumption
    | (apply mul_ne_zero <;> (first
      | assumption
      | (apply mul_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (apply pow_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring))))
    | (apply pow_ne_zero <;> (first
      | assumption
      | (apply mul_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (apply pow_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring))))
    | (convert hPden using 1; ring)
    | (convert h2DEF using 1; ring)
    | (convert hD2 using 1; ring)
    | (convert hDEDF using 1; ring)
    | (convert hEF2 using 1; ring)
    | (convert hDE2 using 1; ring)
    | (convert hDF2 using 1; ring)
    | (convert hEF0 using 1; ring)
    | (convert hFE0 using 1; ring)
    | (convert h2D using 1; ring)
    | (convert hD0 using 1; ring)
    | (convert hE0 using 1; ring)
    | (convert hF0 using 1; ring)) []
    try ring
  have hOBF : OB - F = F * (D ^ 2 * E + D ^ 2 * F - D * E * F + D * F ^ 2 - 2 * E ^ 2 * F) /
      ((D + E) * (D + F) * (E - F)) := by
    rw [hOB]
    field_simp (disch := first
    | assumption
    | (apply mul_ne_zero <;> (first
      | assumption
      | (apply mul_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (apply pow_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring))))
    | (apply pow_ne_zero <;> (first
      | assumption
      | (apply mul_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (apply pow_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring))))
    | (convert hPden using 1; ring)
    | (convert h2DEF using 1; ring)
    | (convert hD2 using 1; ring)
    | (convert hDEDF using 1; ring)
    | (convert hEF2 using 1; ring)
    | (convert hDE2 using 1; ring)
    | (convert hDF2 using 1; ring)
    | (convert hEF0 using 1; ring)
    | (convert hFE0 using 1; ring)
    | (convert h2D using 1; ring)
    | (convert hD0 using 1; ring)
    | (convert hE0 using 1; ring)
    | (convert hF0 using 1; ring)) []
    try ring
  have hOCP : OC - P = -(E * F) * (2 * D + E + F) *
      (2 * D ^ 2 * E + D * E * F - D * F ^ 2 - E ^ 2 * F - E * F ^ 2) /
      ((D + E) * (D + F) * (E - F) * (2 * E * F + D * (E + F))) := by
    rw [hOC, hP]
    field_simp (disch := first
    | assumption
    | (apply mul_ne_zero <;> (first
      | assumption
      | (apply mul_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (apply pow_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring))))
    | (apply pow_ne_zero <;> (first
      | assumption
      | (apply mul_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (apply pow_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring))))
    | (convert hPden using 1; ring)
    | (convert h2DEF using 1; ring)
    | (convert hD2 using 1; ring)
    | (convert hDEDF using 1; ring)
    | (convert hEF2 using 1; ring)
    | (convert hDE2 using 1; ring)
    | (convert hDF2 using 1; ring)
    | (convert hEF0 using 1; ring)
    | (convert hFE0 using 1; ring)
    | (convert h2D using 1; ring)
    | (convert hD0 using 1; ring)
    | (convert hE0 using 1; ring)
    | (convert hF0 using 1; ring)) []
    try ring
  have hOCC : OC - C = -E * (2 * D ^ 2 * E + D * E * F - D * F ^ 2 - E ^ 2 * F - E * F ^ 2) /
      ((D + E) * (D + F) * (E - F)) := by
    rw [hOC, hC]
    field_simp (disch := first
    | assumption
    | (apply mul_ne_zero <;> (first
      | assumption
      | (apply mul_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (apply pow_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring))))
    | (apply pow_ne_zero <;> (first
      | assumption
      | (apply mul_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (apply pow_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring))))
    | (convert hPden using 1; ring)
    | (convert h2DEF using 1; ring)
    | (convert hD2 using 1; ring)
    | (convert hDEDF using 1; ring)
    | (convert hEF2 using 1; ring)
    | (convert hDE2 using 1; ring)
    | (convert hDF2 using 1; ring)
    | (convert hEF0 using 1; ring)
    | (convert hFE0 using 1; ring)
    | (convert h2D using 1; ring)
    | (convert hD0 using 1; ring)
    | (convert hE0 using 1; ring)
    | (convert hF0 using 1; ring)) []
    try ring
  have hOCE : OC - E = -E * (D ^ 2 * E + D ^ 2 * F + D * E ^ 2 - D * E * F - 2 * E * F ^ 2) /
      ((D + E) * (D + F) * (E - F)) := by
    rw [hOC]
    field_simp (disch := first
    | assumption
    | (apply mul_ne_zero <;> (first
      | assumption
      | (apply mul_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (apply pow_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring))))
    | (apply pow_ne_zero <;> (first
      | assumption
      | (apply mul_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (apply pow_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring))))
    | (convert hPden using 1; ring)
    | (convert h2DEF using 1; ring)
    | (convert hD2 using 1; ring)
    | (convert hDEDF using 1; ring)
    | (convert hEF2 using 1; ring)
    | (convert hDE2 using 1; ring)
    | (convert hDF2 using 1; ring)
    | (convert hEF0 using 1; ring)
    | (convert hFE0 using 1; ring)
    | (convert h2D using 1; ring)
    | (convert hD0 using 1; ring)
    | (convert hE0 using 1; ring)
    | (convert hF0 using 1; ring)) []
    try ring
  -- `OB` is equidistant from `P`, `B`, `F` and `OC` from `P`, `C`, `E`
  have idOB1 : conj (OB - P) * (OB - P) = conj (OB - B) * (OB - B) := by
    rw [hOBP, hOBB]
    simp only [map_mul, map_div₀, map_inv₀, map_pow, map_neg, map_ofNat, map_one,
      Complex.conj_conj]
    simp only [c1, c2, c3, c4, c5, c6, c7, c8]
    simp only [map_add, map_sub, map_mul, map_div₀, map_inv₀, map_pow, map_neg, map_ofNat,
      map_one, Complex.conj_conj, hDi, hEi, hFi, inv_inv]
    field_simp (disch := first
    | assumption
    | (apply mul_ne_zero <;> (first
      | assumption
      | (apply mul_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (apply pow_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring))))
    | (apply pow_ne_zero <;> (first
      | assumption
      | (apply mul_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (apply pow_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring))))
    | (convert hPden using 1; ring)
    | (convert h2DEF using 1; ring)
    | (convert hD2 using 1; ring)
    | (convert hDEDF using 1; ring)
    | (convert hEF2 using 1; ring)
    | (convert hDE2 using 1; ring)
    | (convert hDF2 using 1; ring)
    | (convert hEF0 using 1; ring)
    | (convert hFE0 using 1; ring)
    | (convert h2D using 1; ring)
    | (convert hD0 using 1; ring)
    | (convert hE0 using 1; ring)
    | (convert hF0 using 1; ring)) []
    try ring
  have idOB2 : conj (OB - P) * (OB - P) = conj (OB - F) * (OB - F) := by
    rw [hOBP, hOBF]
    simp only [map_mul, map_div₀, map_inv₀, map_pow, map_neg, map_ofNat, map_one,
      Complex.conj_conj]
    simp only [c1, c2, c3, c4, c5, c6, c7, c8]
    simp only [map_add, map_sub, map_mul, map_div₀, map_inv₀, map_pow, map_neg, map_ofNat,
      map_one, Complex.conj_conj, hDi, hEi, hFi, inv_inv]
    field_simp (disch := first
    | assumption
    | (apply mul_ne_zero <;> (first
      | assumption
      | (apply mul_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (apply pow_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring))))
    | (apply pow_ne_zero <;> (first
      | assumption
      | (apply mul_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (apply pow_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring))))
    | (convert hPden using 1; ring)
    | (convert h2DEF using 1; ring)
    | (convert hD2 using 1; ring)
    | (convert hDEDF using 1; ring)
    | (convert hEF2 using 1; ring)
    | (convert hDE2 using 1; ring)
    | (convert hDF2 using 1; ring)
    | (convert hEF0 using 1; ring)
    | (convert hFE0 using 1; ring)
    | (convert h2D using 1; ring)
    | (convert hD0 using 1; ring)
    | (convert hE0 using 1; ring)
    | (convert hF0 using 1; ring)) []
    try ring
  have idOC1 : conj (OC - P) * (OC - P) = conj (OC - C) * (OC - C) := by
    rw [hOCP, hOCC]
    simp only [map_mul, map_div₀, map_inv₀, map_pow, map_neg, map_ofNat, map_one,
      Complex.conj_conj]
    simp only [c1, c2, c3, c4, c5, c6, c7, c8]
    simp only [map_add, map_sub, map_mul, map_div₀, map_inv₀, map_pow, map_neg, map_ofNat,
      map_one, Complex.conj_conj, hDi, hEi, hFi, inv_inv]
    field_simp (disch := first
    | assumption
    | (apply mul_ne_zero <;> (first
      | assumption
      | (apply mul_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (apply pow_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring))))
    | (apply pow_ne_zero <;> (first
      | assumption
      | (apply mul_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (apply pow_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring))))
    | (convert hPden using 1; ring)
    | (convert h2DEF using 1; ring)
    | (convert hD2 using 1; ring)
    | (convert hDEDF using 1; ring)
    | (convert hEF2 using 1; ring)
    | (convert hDE2 using 1; ring)
    | (convert hDF2 using 1; ring)
    | (convert hEF0 using 1; ring)
    | (convert hFE0 using 1; ring)
    | (convert h2D using 1; ring)
    | (convert hD0 using 1; ring)
    | (convert hE0 using 1; ring)
    | (convert hF0 using 1; ring)) []
    try ring
  have idOC2 : conj (OC - P) * (OC - P) = conj (OC - E) * (OC - E) := by
    rw [hOCP, hOCE]
    simp only [map_mul, map_div₀, map_inv₀, map_pow, map_neg, map_ofNat, map_one,
      Complex.conj_conj]
    simp only [c1, c2, c3, c4, c5, c6, c7, c8]
    simp only [map_add, map_sub, map_mul, map_div₀, map_inv₀, map_pow, map_neg, map_ofNat,
      map_one, Complex.conj_conj, hDi, hEi, hFi, inv_inv]
    field_simp (disch := first
    | assumption
    | (apply mul_ne_zero <;> (first
      | assumption
      | (apply mul_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (apply pow_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring))))
    | (apply pow_ne_zero <;> (first
      | assumption
      | (apply mul_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (apply pow_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring))))
    | (convert hPden using 1; ring)
    | (convert h2DEF using 1; ring)
    | (convert hD2 using 1; ring)
    | (convert hDEDF using 1; ring)
    | (convert hEF2 using 1; ring)
    | (convert hDE2 using 1; ring)
    | (convert hDF2 using 1; ring)
    | (convert hEF0 using 1; ring)
    | (convert hFE0 using 1; ring)
    | (convert h2D using 1; ring)
    | (convert hD0 using 1; ring)
    | (convert hE0 using 1; ring)
    | (convert hF0 using 1; ring)) []
    try ring
  -- single-fraction forms of `P - T` and `OB - OC`
  have hPT : P - T = -(E * F) * (2 * D - E - F) *
      (D ^ 2 * E + D ^ 2 * F + 4 * D * E * F + E ^ 2 * F + E * F ^ 2) /
      ((E + F) * (D ^ 2 + E * F) * (2 * E * F + D * (E + F))) := by
    rw [hP, hTdef]
    field_simp (disch := first
    | assumption
    | (apply mul_ne_zero <;> (first
      | assumption
      | (apply mul_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (apply pow_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring))))
    | (apply pow_ne_zero <;> (first
      | assumption
      | (apply mul_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (apply pow_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring))))
    | (convert hPden using 1; ring)
    | (convert h2DEF using 1; ring)
    | (convert hD2 using 1; ring)
    | (convert hDEDF using 1; ring)
    | (convert hEF2 using 1; ring)
    | (convert hDE2 using 1; ring)
    | (convert hDF2 using 1; ring)
    | (convert hEF0 using 1; ring)
    | (convert hFE0 using 1; ring)
    | (convert h2D using 1; ring)
    | (convert hD0 using 1; ring)
    | (convert hE0 using 1; ring)
    | (convert hF0 using 1; ring)) []
    try ring
  have hOBC : OB - OC = (E * F) * (2 * D - E - F) * (2 * D + E + F) /
      ((D + E) * (D + F) * (E - F)) := by
    rw [hOB, hOC]
    field_simp (disch := first
    | assumption
    | (apply mul_ne_zero <;> (first
      | assumption
      | (apply mul_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (apply pow_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring))))
    | (apply pow_ne_zero <;> (first
      | assumption
      | (apply mul_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (apply pow_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring))))
    | (convert hPden using 1; ring)
    | (convert h2DEF using 1; ring)
    | (convert hD2 using 1; ring)
    | (convert hDEDF using 1; ring)
    | (convert hEF2 using 1; ring)
    | (convert hDE2 using 1; ring)
    | (convert hDF2 using 1; ring)
    | (convert hEF0 using 1; ring)
    | (convert hFE0 using 1; ring)
    | (convert h2D using 1; ring)
    | (convert hD0 using 1; ring)
    | (convert hE0 using 1; ring)
    | (convert hF0 using 1; ring)) []
    try ring
  -- the master identity: `PT ⟂ OB - OC`
  have hmaster : (OB - OC) * conj (P - T) + conj ((OB - OC) * conj (P - T)) = 0 := by
    rw [hPT, hOBC]
    simp only [map_mul, map_div₀, map_inv₀, map_pow, map_neg, map_ofNat, map_one,
      Complex.conj_conj]
    simp only [c1, c2, c3, c4, c5, c6, c7, c8]
    simp only [map_add, map_sub, map_mul, map_div₀, map_inv₀, map_pow, map_neg, map_ofNat,
      map_one, Complex.conj_conj, hDi, hEi, hFi, inv_inv]
    field_simp (disch := first
    | assumption
    | (apply mul_ne_zero <;> (first
      | assumption
      | (apply mul_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (apply pow_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring))))
    | (apply pow_ne_zero <;> (first
      | assumption
      | (apply mul_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (apply pow_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring))))
    | (convert hPden using 1; ring)
    | (convert h2DEF using 1; ring)
    | (convert hD2 using 1; ring)
    | (convert hDEDF using 1; ring)
    | (convert hEF2 using 1; ring)
    | (convert hDE2 using 1; ring)
    | (convert hDF2 using 1; ring)
    | (convert hEF0 using 1; ring)
    | (convert hFE0 using 1; ring)
    | (convert h2D using 1; ring)
    | (convert hD0 using 1; ring)
    | (convert hE0 using 1; ring)
    | (convert hF0 using 1; ring)) []
    try ring
  have hOBC0 : OB - OC ≠ 0 := by
    rw [hOBC]
    apply div_ne_zero_iff.mpr
    exact ⟨mul_ne_zero (mul_ne_zero (mul_ne_zero hE0 hF0) h2D) h2DEF,
      mul_ne_zero (mul_ne_zero hDE2 hDF2) hEF0⟩
  -- `T / D` is real
  have hTD : T * D⁻¹ = conj (T * D⁻¹) := by
    rw [hTdef]
    simp only [map_mul, map_div₀, map_inv₀, map_pow, map_neg, map_ofNat, map_one,
      Complex.conj_conj]
    simp only [c1, c2, c3, c4, c5, c6, c7, c8]
    simp only [map_add, map_sub, map_mul, map_div₀, map_inv₀, map_pow, map_neg, map_ofNat,
      map_one, Complex.conj_conj, hDi, hEi, hFi, inv_inv]
    field_simp (disch := first
    | assumption
    | (apply mul_ne_zero <;> (first
      | assumption
      | (apply mul_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (apply pow_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring))))
    | (apply pow_ne_zero <;> (first
      | assumption
      | (apply mul_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (apply pow_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring))))
    | (convert hPden using 1; ring)
    | (convert h2DEF using 1; ring)
    | (convert hD2 using 1; ring)
    | (convert hDEDF using 1; ring)
    | (convert hEF2 using 1; ring)
    | (convert hDE2 using 1; ring)
    | (convert hDF2 using 1; ring)
    | (convert hEF0 using 1; ring)
    | (convert hFE0 using 1; ring)
    | (convert h2D using 1; ring)
    | (convert hD0 using 1; ring)
    | (convert hE0 using 1; ring)
    | (convert hF0 using 1; ring)) []
    try ring
  -- single-fraction form of `T - A`
  have hTA1 : T - A = 2 * E * F * (D ^ 2 - E * F) / ((D ^ 2 + E * F) * (E + F)) := by
    rw [hTdef, hA]
    field_simp (disch := first
    | assumption
    | (apply mul_ne_zero <;> (first
      | assumption
      | (apply mul_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (apply pow_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring))))
    | (apply pow_ne_zero <;> (first
      | assumption
      | (apply mul_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (apply pow_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring))))
    | (convert hPden using 1; ring)
    | (convert h2DEF using 1; ring)
    | (convert hD2 using 1; ring)
    | (convert hDEDF using 1; ring)
    | (convert hEF2 using 1; ring)
    | (convert hDE2 using 1; ring)
    | (convert hDF2 using 1; ring)
    | (convert hEF0 using 1; ring)
    | (convert hFE0 using 1; ring)
    | (convert h2D using 1; ring)
    | (convert hD0 using 1; ring)
    | (convert hE0 using 1; ring)
    | (convert hF0 using 1; ring)) []
    try ring
  -- `T - A ⟂ A`
  have idTA : A * conj (T - A) + conj (A * conj (T - A)) = 0 := by
    rw [hTA1, hA]
    simp only [map_mul, map_div₀, map_inv₀, map_pow, map_neg, map_ofNat, map_one,
      Complex.conj_conj]
    simp only [c1, c2, c3, c4, c5, c6, c7, c8]
    simp only [map_add, map_sub, map_mul, map_div₀, map_inv₀, map_pow, map_neg, map_ofNat,
      map_one, Complex.conj_conj, hDi, hEi, hFi, inv_inv]
    field_simp (disch := first
    | assumption
    | (apply mul_ne_zero <;> (first
      | assumption
      | (apply mul_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (apply pow_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring))))
    | (apply pow_ne_zero <;> (first
      | assumption
      | (apply mul_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (apply pow_ne_zero <;> (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring)))
      | (first
          | assumption
          | (convert hD0 using 1; ring)
          | (convert hE0 using 1; ring)
          | (convert hF0 using 1; ring))))
    | (convert hPden using 1; ring)
    | (convert h2DEF using 1; ring)
    | (convert hD2 using 1; ring)
    | (convert hDEDF using 1; ring)
    | (convert hEF2 using 1; ring)
    | (convert hDE2 using 1; ring)
    | (convert hDF2 using 1; ring)
    | (convert hEF0 using 1; ring)
    | (convert hFE0 using 1; ring)
    | (convert h2D using 1; ring)
    | (convert hD0 using 1; ring)
    | (convert hE0 using 1; ring)
    | (convert hF0 using 1; ring)) []
    try ring
  -- extract the two circles through `Q`
  obtain ⟨O₁, r₁, hO₁⟩ := hQCE
  obtain ⟨O₂, r₂, hO₂⟩ := hQBF
  have dP1 : dist P O₁ = r₁ := hO₁ P (by simp)
  have dC1 : dist C O₁ = r₁ := hO₁ C (by simp)
  have dE1 : dist E O₁ = r₁ := hO₁ E (by simp)
  have dQ1 : dist Q O₁ = r₁ := hO₁ Q (by simp)
  have dP2 : dist P O₂ = r₂ := hO₂ P (by simp)
  have dB2 : dist B O₂ = r₂ := hO₂ B (by simp)
  have dF2 : dist F O₂ = r₂ := hO₂ F (by simp)
  have dQ2 : dist Q O₂ = r₂ := hO₂ Q (by simp)
  -- identify the centers
  have hO₁eq : O₁ = OC := circumcenter_unique hPCE
    (by rw [dist_comm O₁ P, dP1, dist_comm O₁ C, dC1])
    (by rw [dist_comm O₁ P, dP1, dist_comm O₁ E, dE1])
    (dist_eq_of_conj_mul_eq idOC1) (dist_eq_of_conj_mul_eq idOC2)
  have hO₂eq : O₂ = OB := circumcenter_unique hPBF
    (by rw [dist_comm O₂ P, dP2, dist_comm O₂ B, dB2])
    (by rw [dist_comm O₂ P, dP2, dist_comm O₂ F, dF2])
    (dist_eq_of_conj_mul_eq idOB1) (dist_eq_of_conj_mul_eq idOB2)
  -- `PQ ⟂ O₁O₂` and `PT ⟂ O₁O₂`
  have hchord : ⟪Q - P, O₁ - O₂⟫_ℝ = 0 :=
    inner_sub_eq_zero_of_dist_eq (dQ1.trans dP1.symm) (dQ2.trans dP2.symm)
  have hTperp : ⟪T - P, O₁ - O₂⟫_ℝ = 0 := by
    rw [hO₁eq, hO₂eq]
    have e : ⟪T - P, OC - OB⟫_ℝ = ⟪P - T, OB - OC⟫_ℝ := by
      rw [show T - P = -(P - T) by rw [neg_sub],
        show OC - OB = -(OB - OC) by rw [neg_sub]]
      rw [inner_neg_left, inner_neg_right, neg_neg]
    rw [e]
    exact inner_eq_zero_of hmaster
  have hOO : O₁ - O₂ ≠ 0 := by
    rw [hO₁eq, hO₂eq]
    intro h
    apply hOBC0
    have e : OB - OC = -(OC - OB) := by rw [neg_sub]
    rw [e, h, neg_zero]
  have hQP0 : Q - P ≠ 0 := sub_ne_zero.mpr hQP
  obtain ⟨c, hc⟩ := exists_real_smul_of_inner_eq_zero hOO hchord hTperp hQP0
  -- assemble
  refine ⟨T, ?_, ?_, ?_⟩
  · -- `T ∈ line[ℝ, D, 0]` since `T / D` is real
    have him : (T * D⁻¹).im = 0 := by
      have h := congrArg Complex.im hTD
      rw [Complex.conj_im] at h
      linarith
    set cDI : ℝ := (T * D⁻¹).re with hcDI
    have hT3 : T = (cDI : ℂ) * D := by
      have h2 : T * D⁻¹ = (cDI : ℂ) := by
        have h3 := Complex.re_add_im (T * D⁻¹)
        rw [him, Complex.ofReal_zero, zero_mul, add_zero, ← hcDI] at h3
        exact h3.symm
      calc T = (T * D⁻¹) * D := by rw [inv_mul_cancel_right₀ hD0]
        _ = (cDI : ℂ) * D := by conv_lhs => rw [h2]
    have h4 := AffineMap.lineMap_mem_affineSpan_pair (1 - cDI) D (0 : ℂ)
    rw [AffineMap.lineMap_apply_module'] at h4
    have h5 : (1 - cDI) • ((0 : ℂ) - D) + D = T := by
      rw [hT3, Complex.real_smul]
      push_cast
      ring
    rwa [h5] at h4
  · -- `T ∈ line[ℝ, P, Q]`
    have h := AffineMap.lineMap_mem_affineSpan_pair c P Q
    rw [AffineMap.lineMap_apply_module'] at h
    have hT2 : T = c • (Q - P) + P := sub_eq_iff_eq_add.mp hc
    rwa [hT2]
  · -- `T - A ⟂ A`
    exact inner_eq_zero_of idTA

end Imo2019P6
