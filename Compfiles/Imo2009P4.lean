/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.Geometry.Euclidean.Incenter
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 2009, Problem 4

Let ABC be a triangle with AB = AC. The angle bisectors of ∠CAB and ∠ABC
meet the sides BC and CA at D and E, respectively. Let K be the incenter of
triangle ADC. Suppose that ∠BEK = 45°. Find all possible values of ∠CAB.
-/

namespace Imo2009P4

open scoped EuclideanGeometry RealInnerProductSpace

snip begin

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MetricSpace P] [NormedAddTorsor V P]

/-- In an isosceles triangle `ABC` with `AB = AC`, the foot `D` of the angle bisector
from `A` on the open segment `BC` is the midpoint of `BC` and `AD ⟂ BC`.
Vector form: `B -ᵥ D = -(C -ᵥ D)` and `⟪A -ᵥ D, C -ᵥ D⟫ = 0`. -/
lemma perp_and_midpoint {A B C D : P}
    (hD : Sbtw ℝ B D C) (hACn : A ≠ C) (hADn : A ≠ D)
    (hAB : dist A B = dist A C) (hAD : ∠ B A D = ∠ D A C) :
    ⟪A -ᵥ D, C -ᵥ D⟫ = 0 ∧ B -ᵥ D = -(C -ᵥ D) := by
  obtain ⟨t, ht, hDt⟩ : ∃ t ∈ Set.Ioo (0 : ℝ) 1, D = AffineMap.lineMap B C t := by
    obtain ⟨t, ht, hDt⟩ := hD.mem_image_Ioo
    exact ⟨t, ht, hDt.symm⟩
  rw [Set.mem_Ioo] at ht
  have h1t' : (0 : ℝ) < 1 - t := sub_pos.mpr ht.2
  have h1t : (1 : ℝ) - t ≠ 0 := ne_of_gt h1t'
  have hBCn : B ≠ C := hD.left_ne_right
  -- vector relation from `D ∈ segment BC`
  have htw : (t - 1) • (B -ᵥ D) = t • (C -ᵥ D) := by
    have hDB : D -ᵥ B = t • (C -ᵥ B) := by
      rw [hDt, AffineMap.lineMap_apply, vadd_vsub]
    have hCB : C -ᵥ B = (C -ᵥ D) - (B -ᵥ D) := (vsub_sub_vsub_cancel_right C B D).symm
    rw [hCB, show D -ᵥ B = -(B -ᵥ D) from (neg_vsub_eq_vsub_rev B D).symm, smul_sub] at hDB
    have h2 : t • (B -ᵥ D) + (-(B -ᵥ D)) = t • (C -ᵥ D) := by
      rw [hDB]; abel
    have h3 : (t - 1) • (B -ᵥ D) = t • (B -ᵥ D) + (-(B -ᵥ D)) := by module
    rw [h3, h2]
  -- introduce `μ = t / (1 - t) > 0` so that `B -ᵥ D = -μ • (C -ᵥ D)`
  set μ : ℝ := t / (1 - t) with hμ
  have hμpos : 0 < μ := by rw [hμ]; exact div_pos ht.1 h1t'
  have hw : B -ᵥ D = (-μ) • (C -ᵥ D) := by
    have h4 : (1 - t) • (B -ᵥ D) = (-t) • (C -ᵥ D) := by
      have h5 : (1 - t) • (B -ᵥ D) = (-1) • ((t - 1) • (B -ᵥ D)) := by module
      rw [h5, htw]; module
    have hcoef : (1 - t)⁻¹ * (-t) = -μ := by rw [hμ]; field_simp [h1t]
    calc B -ᵥ D = (1 : ℝ) • (B -ᵥ D) := by rw [one_smul]
      _ = ((1 - t)⁻¹ * (1 - t)) • (B -ᵥ D) := by rw [inv_mul_cancel₀ h1t]
      _ = (1 - t)⁻¹ • ((1 - t) • (B -ᵥ D)) := by rw [smul_smul]
      _ = (1 - t)⁻¹ • ((-t) • (C -ᵥ D)) := by rw [h4]
      _ = (-μ) • (C -ᵥ D) := by rw [smul_smul, hcoef]
  -- norms
  have hDn : ‖D -ᵥ A‖ ≠ 0 := by
    rw [← dist_eq_norm_vsub V D A]
    exact dist_ne_zero.mpr (Ne.symm hADn)
  have hCn : ‖C -ᵥ A‖ ≠ 0 := by
    rw [← dist_eq_norm_vsub V C A]
    exact dist_ne_zero.mpr (Ne.symm hACn)
  have hBA : ‖B -ᵥ A‖ = ‖C -ᵥ A‖ := by
    rw [← dist_eq_norm_vsub V B A, ← dist_eq_norm_vsub V C A, dist_comm B A, dist_comm C A]
    exact hAB
  -- the cosine equation from the bisector hypothesis
  have hcos : ⟪B -ᵥ A, D -ᵥ A⟫ = ⟪D -ᵥ A, C -ᵥ A⟫ := by
    have h := congr_arg Real.cos hAD
    rw [EuclideanGeometry.angle, EuclideanGeometry.angle,
        InnerProductGeometry.cos_angle, InnerProductGeometry.cos_angle, hBA,
        mul_comm ‖D -ᵥ A‖ ‖C -ᵥ A‖] at h
    have hd : ‖C -ᵥ A‖ * ‖D -ᵥ A‖ ≠ 0 := mul_ne_zero hCn hDn
    rw [div_eq_div_iff hd hd] at h
    exact mul_right_cancel₀ hd h
  -- expand the cosines in terms of `A -ᵥ D` and `C -ᵥ D`
  have hBAv : B -ᵥ A = (-μ) • (C -ᵥ D) - (A -ᵥ D) := by
    rw [← hw, vsub_sub_vsub_cancel_right]
  have hDAv : D -ᵥ A = -(A -ᵥ D) := (neg_vsub_eq_vsub_rev A D).symm
  have hCAv : C -ᵥ A = (C -ᵥ D) - (A -ᵥ D) := (vsub_sub_vsub_cancel_right C A D).symm
  rw [hBAv, hDAv, hCAv] at hcos
  have hperp : ⟪A -ᵥ D, C -ᵥ D⟫ = 0 := by
    have hμ1 : μ + 1 ≠ 0 := ne_of_gt (add_pos hμpos one_pos)
    simp only [inner_sub_left, inner_sub_right, inner_smul_left,
      inner_neg_left, inner_neg_right, RCLike.conj_to_real,
      real_inner_comm (A -ᵥ D) (C -ᵥ D)] at hcos
    have h2 : (μ + 1) * ⟪A -ᵥ D, C -ᵥ D⟫ = 0 := by linarith [hcos]
    exact (mul_eq_zero.mp h2).resolve_left hμ1
  refine ⟨hperp, ?_⟩
  -- nonvanishing of `C -ᵥ D`
  have hCv : C -ᵥ D ≠ 0 := by
    rw [Ne, vsub_eq_zero_iff_eq]
    intro hCD
    have h2 : C -ᵥ B = t • (C -ᵥ B) := by
      have h3 := congr_arg (· -ᵥ B) (hCD.trans hDt)
      rw [AffineMap.lineMap_apply, vadd_vsub] at h3
      exact h3
    have h4 : (1 - t) • (C -ᵥ B) = 0 := by
      have h5 : (1 - t) • (C -ᵥ B) = (C -ᵥ B) - t • (C -ᵥ B) := by module
      rw [h5, ← h2, sub_self]
    have h7 : C -ᵥ B = 0 := (smul_eq_zero.mp h4).resolve_left h1t
    rw [vsub_eq_zero_iff_eq] at h7
    exact hBCn h7.symm
  have hWn : ‖C -ᵥ D‖ ≠ 0 := norm_ne_zero_iff.mpr hCv
  have hperp' : ⟪C -ᵥ D, A -ᵥ D⟫ = 0 := by rw [real_inner_comm]; exact hperp
  -- finally `AB = AC` forces `μ = 1`
  have h2 : ‖B -ᵥ A‖ ^ 2 = ‖C -ᵥ A‖ ^ 2 := by rw [hBA]
  rw [hBAv, hCAv] at h2
  simp only [norm_sub_sq_real, norm_smul, norm_neg, real_inner_smul_left,
    hperp', Real.norm_eq_abs, abs_of_pos hμpos] at h2
  have h3 : (μ * ‖C -ᵥ D‖) ^ 2 = ‖C -ᵥ D‖ ^ 2 := by linear_combination h2
  have h4 : μ * μ * (‖C -ᵥ D‖ ^ 2) = ‖C -ᵥ D‖ ^ 2 := by
    calc μ * μ * (‖C -ᵥ D‖ ^ 2) = (μ * ‖C -ᵥ D‖) ^ 2 := by ring
      _ = ‖C -ᵥ D‖ ^ 2 := h3
  have hμ2 : μ * μ = 1 := by
    have h6 : ‖C -ᵥ D‖ ^ 2 ≠ 0 := pow_ne_zero 2 hWn
    have h7 : (μ * μ - 1) * (‖C -ᵥ D‖ ^ 2) = 0 := by linarith [h4]
    rcases mul_eq_zero.mp h7 with h8 | h8
    · linarith [h8]
    · exact absurd h8 h6
  have hμ1 : μ = 1 := by
    have h4' : μ ^ 2 = 1 := by rw [pow_two]; exact hμ2
    rcases sq_eq_one_iff.mp h4' with h5 | h5
    · exact h5
    · linarith [hμpos, h5]
  rw [hμ1] at hw
  rw [hw]
  module


/-- The angle bisector foot: in the normalized configuration (`D` midpoint of `BC`,
`AD ⟂ BC`), the point `E` on the open segment `CA` with `BE` bisecting `∠ABC`
has barycentric coordinates given by the angle bisector theorem,
`E -ᵥ D = (2w/(s+2w)) • (A -ᵥ D) + (s/(s+2w)) • (C -ᵥ D)` with `w = dist D C`,
`s = dist A C`. -/
lemma bisector_foot_coeff {A B C D E : P}
    (hE : Sbtw ℝ C E A) (hBE : ∠ A B E = ∠ E B C)
    (hmid : B -ᵥ D = -(C -ᵥ D)) (hperp : ⟪A -ᵥ D, C -ᵥ D⟫ = 0)
    (hADn : A ≠ D) (hCDn : C ≠ D) (hBEn : B ≠ E) :
    E -ᵥ D = (2 * dist D C / (dist A C + 2 * dist D C)) • (A -ᵥ D) +
      (dist A C / (dist A C + 2 * dist D C)) • (C -ᵥ D) := by
  obtain ⟨τ, hτI, hEt⟩ : ∃ τ ∈ Set.Ioo (0 : ℝ) 1, E = AffineMap.lineMap C A τ := by
    obtain ⟨τ, hτ, hEt⟩ := hE.mem_image_Ioo
    exact ⟨τ, hτ, hEt.symm⟩
  rw [Set.mem_Ioo] at hτI
  set g := ‖A -ᵥ D‖ with hg
  set w := ‖C -ᵥ D‖ with hw'
  set s := ‖A -ᵥ C‖ with hs
  have hACv : A -ᵥ C = (A -ᵥ D) - (C -ᵥ D) := (vsub_sub_vsub_cancel_right A C D).symm
  have hEvec : E -ᵥ D = τ • (A -ᵥ D) + (1 - τ) • (C -ᵥ D) := by
    rw [hEt, AffineMap.lineMap_apply, vadd_vsub_assoc, hACv]
    module
  have hgpos : 0 < g := by
    rw [hg]; exact norm_pos_iff.mpr (by rw [vsub_ne_zero]; exact hADn)
  have hwpos : 0 < w := by
    rw [hw']; exact norm_pos_iff.mpr (by rw [vsub_ne_zero]; exact hCDn)
  have hspos : 0 < s := by
    rw [hs]; exact norm_pos_iff.mpr (by rw [vsub_ne_zero]; exact hE.left_ne_right.symm)
  have huv : ⟪A -ᵥ D, C -ᵥ D⟫ = 0 := hperp
  have hvu : ⟪C -ᵥ D, A -ᵥ D⟫ = 0 := by rw [real_inner_comm]; exact hperp
  -- Pythagoras
  have hpyt : s ^ 2 = g ^ 2 + w ^ 2 := by
    rw [hs, hg, hw', hACv, norm_sub_sq_real, huv]
    ring
  -- vector expressions
  have hBAv : A -ᵥ B = (A -ᵥ D) + (C -ᵥ D) := by
    have h2 : A -ᵥ B = (A -ᵥ D) - (B -ᵥ D) := (vsub_sub_vsub_cancel_right A B D).symm
    rw [h2, hmid]
    module
  have hCBv : C -ᵥ B = (2 : ℝ) • (C -ᵥ D) := by
    have h2 : C -ᵥ B = (C -ᵥ D) - (B -ᵥ D) := (vsub_sub_vsub_cancel_right C B D).symm
    rw [h2, hmid]
    module
  have hEBv : E -ᵥ B = τ • (A -ᵥ D) + (2 - τ) • (C -ᵥ D) := by
    have h2 : E -ᵥ B = (E -ᵥ D) - (B -ᵥ D) := (vsub_sub_vsub_cancel_right E B D).symm
    rw [h2, hEvec, hmid]
    module
  -- norms
  have hnormAB : ‖A -ᵥ B‖ = s := by
    have h1 : ‖(A -ᵥ D) + (C -ᵥ D)‖ ^ 2 = ‖(A -ᵥ D) - (C -ᵥ D)‖ ^ 2 := by
      rw [norm_add_sq_real, norm_sub_sq_real, huv]
      ring
    have h2 : ‖(A -ᵥ D) + (C -ᵥ D)‖ = ‖(A -ᵥ D) - (C -ᵥ D)‖ := by
      have h3 : 0 ≤ ‖(A -ᵥ D) + (C -ᵥ D)‖ := norm_nonneg _
      have h4 : 0 ≤ ‖(A -ᵥ D) - (C -ᵥ D)‖ := norm_nonneg _
      nlinarith [h1, h3, h4]
    rw [hBAv, h2, hs, hACv]
  have hnormCB : ‖C -ᵥ B‖ = 2 * w := by
    rw [hCBv, norm_smul, Real.norm_ofNat, hw']
  -- the cosine equation from the bisector hypothesis
  have hN : ‖E -ᵥ B‖ ≠ 0 := by
    rw [← dist_eq_norm_vsub V E B]
    exact dist_ne_zero.mpr (fun h => hBEn h.symm)
  have hcos := congr_arg Real.cos hBE
  rw [EuclideanGeometry.angle, EuclideanGeometry.angle,
    InnerProductGeometry.cos_angle, InnerProductGeometry.cos_angle,
    hnormAB, hnormCB] at hcos
  have h2w : (2 : ℝ) * w ≠ 0 := by positivity
  have hs' : s ≠ 0 := ne_of_gt hspos
  rw [div_eq_div_iff (mul_ne_zero hs' hN) (mul_ne_zero hN h2w)] at hcos
  have hcos2 : ⟪A -ᵥ B, E -ᵥ B⟫ * (2 * w) = ⟪E -ᵥ B, C -ᵥ B⟫ * s := by
    apply mul_right_cancel₀ hN
    linear_combination hcos
  -- expand the inner products
  have hX : ⟪A -ᵥ B, E -ᵥ B⟫ = τ * g ^ 2 + (2 - τ) * w ^ 2 := by
    rw [hBAv, hEBv]
    simp only [inner_add_left, inner_add_right, real_inner_smul_right,
      huv, hvu, real_inner_self_eq_norm_sq, ← hg, ← hw']
    ring
  have hY : ⟪E -ᵥ B, C -ᵥ B⟫ = 2 * (2 - τ) * w ^ 2 := by
    rw [hEBv, hCBv]
    simp only [inner_add_left, real_inner_smul_left, real_inner_smul_right,
      huv, real_inner_self_eq_norm_sq, ← hw']
    ring
  rw [hX, hY] at hcos2
  -- deduce `τ * (s + 2w) = 2w`
  have hswpos : 0 < s - w := by
    have h1 : w ^ 2 < s ^ 2 := by nlinarith [hpyt, hgpos]
    nlinarith [h1, le_of_lt hwpos, le_of_lt hspos]
  have key1 : τ * g ^ 2 = (2 - τ) * w * (s - w) := by
    apply mul_right_cancel₀ h2w
    linear_combination hcos2
  have key : τ * (s + 2 * w) = 2 * w := by
    apply mul_right_cancel₀ (ne_of_gt hswpos)
    linear_combination key1 + τ * hpyt
  have hτeq : τ = 2 * w / (s + 2 * w) := by
    rw [eq_div_iff (show s + 2 * w ≠ 0 by positivity)]
    exact key
  have h1mτ : 1 - τ = s / (s + 2 * w) := by
    rw [hτeq]
    field_simp [(show s + 2 * w ≠ 0 by positivity)]
    ring
  rw [h1mτ, hτeq] at hEvec
  have hwd : w = dist D C := by
    rw [hw', ← dist_eq_norm_vsub V C D, dist_comm]
  have hsd : s = dist A C := by
    rw [hs, ← dist_eq_norm_vsub V A C]
  rw [hwd, hsd] at hEvec
  exact hEvec


open EuclideanGeometry in
/-- If `F` lies on the line through `p₁, p₂` and `F -ᵥ p₃` is orthogonal to `p₁ -ᵥ p₂`,
then `F` is the orthogonal projection of `p₃` onto that line. -/
lemma orthogonalProjection_affineSpan_pair_eq {F p₁ p₂ p₃ : P}
    (hm : F ∈ (affineSpan ℝ ({p₁, p₂} : Set P) : Set P))
    (h : ⟪p₁ -ᵥ p₂, F -ᵥ p₃⟫ = 0) :
    orthogonalProjection (affineSpan ℝ ({p₁, p₂} : Set P)) p₃ = F := by
  have hdir : (affineSpan ℝ ({p₁, p₂} : Set P)).direction = Submodule.span ℝ {p₁ -ᵥ p₂} := by
    rw [direction_affineSpan, vectorSpan_eq_span_vsub_set_left ℝ (Set.mem_insert p₁ {p₂})]
    simp [Set.image_insert_eq, Set.image_singleton]
  have hF : F ∈ AffineSubspace.mk' p₃ ((affineSpan ℝ ({p₁, p₂} : Set P)).directionᗮ) := by
    rw [AffineSubspace.mem_mk', hdir, Submodule.mem_orthogonal]
    intro u hu
    rw [Submodule.mem_span_singleton] at hu
    obtain ⟨r, rfl⟩ := hu
    rw [real_inner_smul_left, h, mul_zero]
  have hsingle := inter_eq_singleton_orthogonalProjection (s := affineSpan ℝ ({p₁, p₂} : Set P)) p₃
  have hmem : F ∈ (affineSpan ℝ ({p₁, p₂} : Set P) : Set P) ∩
      AffineSubspace.mk' p₃ ((affineSpan ℝ ({p₁, p₂} : Set P)).directionᗮ) := ⟨hm, hF⟩
  rw [hsingle, Set.mem_singleton_iff] at hmem
  exact hmem.symm

/-- The incenter of a right triangle `ADC` with the right angle at `D`
(`⟪A -ᵥ D, C -ᵥ D⟫ = 0`), in barycentric coordinates relative to `D`:
`K -ᵥ D = (w/P) • (A -ᵥ D) + (g/P) • (C -ᵥ D)` where `w = dist D C`, `g = dist A D`,
`s = dist A C` and `P = w + s + g` is the perimeter. -/
lemma incenter_right_coeff {A D C : P} (hADC : AffineIndependent ℝ ![A, D, C])
    (hperp : ⟪A -ᵥ D, C -ᵥ D⟫ = 0) :
    (⟨![A, D, C], hADC⟩ : Affine.Simplex ℝ P 2).incenter -ᵥ D =
      (dist D C / (dist D C + dist A C + dist A D)) • (A -ᵥ D) +
      (dist A D / (dist D C + dist A C + dist A D)) • (C -ᵥ D) := by
  classical
  set T : Affine.Simplex ℝ P 2 := ⟨![A, D, C], hADC⟩ with hT
  set g := dist A D with hg
  set w := dist D C with hw
  set s := dist A C with hs
  have hTpts : T.points = ![A, D, C] := rfl
  have huv : ⟪A -ᵥ D, C -ᵥ D⟫ = 0 := hperp
  have hvu : ⟪C -ᵥ D, A -ᵥ D⟫ = 0 := by rw [real_inner_comm]; exact hperp
  have hgpos : 0 < g := by
    rw [hg]; exact dist_pos.mpr (hADC.injective.ne (by decide : (0 : Fin 3) ≠ 1))
  have hwpos : 0 < w := by
    rw [hw]; exact dist_pos.mpr (hADC.injective.ne (by decide : (1 : Fin 3) ≠ 2))
  have hspos : 0 < s := by
    rw [hs]; exact dist_pos.mpr (hADC.injective.ne (by decide : (0 : Fin 3) ≠ 2))
  have hs' : s ≠ 0 := ne_of_gt hspos
  -- scalar inner-product data
  have hACv : A -ᵥ C = (A -ᵥ D) - (C -ᵥ D) := (vsub_sub_vsub_cancel_right A C D).symm
  have hgg : ⟪A -ᵥ D, A -ᵥ D⟫ = g ^ 2 := by
    rw [real_inner_self_eq_norm_sq, hg, ← dist_eq_norm_vsub V A D]
  have hww : ⟪C -ᵥ D, C -ᵥ D⟫ = w ^ 2 := by
    rw [real_inner_self_eq_norm_sq, hw, ← dist_eq_norm_vsub V C D, dist_comm]
  have hspq : s ^ 2 = g ^ 2 + w ^ 2 := by
    have h1 : ‖A -ᵥ C‖ ^ 2 = ‖A -ᵥ D‖ ^ 2 + ‖C -ᵥ D‖ ^ 2 := by
      rw [hACv, norm_sub_sq_real, huv]
      ring
    rw [hs, hg, hw, dist_comm D C, dist_eq_norm_vsub V A C, dist_eq_norm_vsub V A D,
      dist_eq_norm_vsub V C D, h1]
  -- the altitude feet from `A` and from `C`
  have hset0 : T.points '' ({0}ᶜ : Set (Fin 3)) = {D, C} := by
    rw [show ({0}ᶜ : Set (Fin 3)) = {1, 2} by grind, hTpts]
    ext x
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, hi, rfl⟩
      fin_cases i <;> simp_all
    · intro hx
      rcases hx with rfl | rfl
      · exact ⟨1, by simp, rfl⟩
      · exact ⟨2, by simp, rfl⟩
  have hsub0 : affineSpan ℝ (Set.range (T.faceOpposite 0).points) =
      affineSpan ℝ ({D, C} : Set P) := by
    rw [Affine.Simplex.range_faceOpposite_points, hset0]
  have hfoot0 : T.altitudeFoot 0 = D := by
    rw [Affine.Simplex.altitudeFoot, Affine.Simplex.orthogonalProjectionSpan,
      EuclideanGeometry.orthogonalProjection_congr hsub0 rfl]
    exact orthogonalProjection_affineSpan_pair_eq (left_mem_affineSpan_pair ℝ D C) (by
      show ⟪D -ᵥ C, D -ᵥ A⟫ = 0
      have h1 : D -ᵥ C = -(C -ᵥ D) := (neg_vsub_eq_vsub_rev C D).symm
      have h2 : D -ᵥ A = -(A -ᵥ D) := (neg_vsub_eq_vsub_rev A D).symm
      rw [h1, h2, inner_neg_left, inner_neg_right, neg_neg, hvu])
  have hset2 : T.points '' ({2}ᶜ : Set (Fin 3)) = {A, D} := by
    rw [show ({2}ᶜ : Set (Fin 3)) = {0, 1} by grind, hTpts]
    ext x
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, hi, rfl⟩
      fin_cases i <;> simp_all
    · intro hx
      rcases hx with rfl | rfl
      · exact ⟨0, by simp, rfl⟩
      · exact ⟨1, by simp, rfl⟩
  have hsub2 : affineSpan ℝ (Set.range (T.faceOpposite 2).points) =
      affineSpan ℝ ({A, D} : Set P) := by
    rw [Affine.Simplex.range_faceOpposite_points, hset2]
  have hfoot2 : T.altitudeFoot 2 = D := by
    rw [Affine.Simplex.altitudeFoot, Affine.Simplex.orthogonalProjectionSpan,
      EuclideanGeometry.orthogonalProjection_congr hsub2 rfl]
    exact orthogonalProjection_affineSpan_pair_eq (right_mem_affineSpan_pair ℝ A D) (by
      show ⟪A -ᵥ D, D -ᵥ C⟫ = 0
      have h1 : D -ᵥ C = -(C -ᵥ D) := (neg_vsub_eq_vsub_rev C D).symm
      rw [h1, inner_neg_right, huv, neg_zero])
  -- the foot from `D` onto line `AC`
  set σ : ℝ := g ^ 2 / s ^ 2 with hσ
  set F : P := AffineMap.lineMap A C σ with hF
  have hFvec : F -ᵥ D = σ • ((C -ᵥ D) - (A -ᵥ D)) + (A -ᵥ D) := by
    rw [hF, AffineMap.lineMap_apply, vadd_vsub_assoc]
    congr 2
    exact (vsub_sub_vsub_cancel_right C A D).symm
  have hss : ⟪(A -ᵥ D) - (C -ᵥ D), (A -ᵥ D) - (C -ᵥ D)⟫ = s ^ 2 := by
    rw [real_inner_self_eq_norm_sq, hs, dist_eq_norm_vsub V A C, hACv]
  have hinner1 : ⟪A -ᵥ C, F -ᵥ D⟫ = 0 := by
    have hexpr : ⟪A -ᵥ C, F -ᵥ D⟫ = g ^ 2 - σ * s ^ 2 := by
      rw [hFvec, hACv]
      simp only [inner_sub_left, inner_add_right, real_inner_smul_right, inner_sub_right,
        huv, hvu, hgg, hww]
      rw [hspq]
      ring
    rw [hexpr, hσ]
    field_simp [hs', pow_ne_zero 2 hs']
    ring
  have hset1 : T.points '' ({1}ᶜ : Set (Fin 3)) = {A, C} := by
    rw [show ({1}ᶜ : Set (Fin 3)) = {0, 2} by grind, hTpts]
    ext x
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, hi, rfl⟩
      fin_cases i <;> simp_all
    · intro hx
      rcases hx with rfl | rfl
      · exact ⟨0, by simp, rfl⟩
      · exact ⟨2, by simp, rfl⟩
  have hsub1 : affineSpan ℝ (Set.range (T.faceOpposite 1).points) =
      affineSpan ℝ ({A, C} : Set P) := by
    rw [Affine.Simplex.range_faceOpposite_points, hset1]
  have hfoot1 : T.altitudeFoot 1 = F := by
    rw [Affine.Simplex.altitudeFoot, Affine.Simplex.orthogonalProjectionSpan,
      EuclideanGeometry.orthogonalProjection_congr hsub1 rfl]
    exact orthogonalProjection_affineSpan_pair_eq (AffineMap.lineMap_mem_affineSpan_pair σ A C)
      hinner1
  -- distance from `D` to `F`
  have hdistF : dist D F = g * w / s := by
    have h1 : dist D F ^ 2 = (g * w / s) ^ 2 := by
      rw [div_pow, dist_eq_norm_vsub V D F, ← real_inner_self_eq_norm_sq,
        eq_div_iff (pow_ne_zero 2 hs')]
      have hDFv : D -ᵥ F = -(σ • ((C -ᵥ D) - (A -ᵥ D)) + (A -ᵥ D)) := by
        rw [← hFvec, neg_vsub_eq_vsub_rev]
      have hval : ⟪D -ᵥ F, D -ᵥ F⟫ * s ^ 2 =
          σ ^ 2 * (g ^ 2 + w ^ 2) * s ^ 2 - 2 * σ * g ^ 2 * s ^ 2 + g ^ 2 * s ^ 2 := by
        rw [hDFv]
        simp only [inner_neg_left, inner_neg_right, inner_add_left, inner_add_right,
          inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
          huv, hvu, hww, hgg]
        ring
      have hσi : σ * s ^ 2 = g ^ 2 := by
        rw [hσ]; field_simp [pow_ne_zero 2 hs']
      have hval2 : ⟪D -ᵥ F, D -ᵥ F⟫ * s ^ 2 = g ^ 2 * s ^ 2 - g ^ 4 := by
        linear_combination hval + (σ * s ^ 2 + g ^ 2) * hσi +
          σ ^ 2 * s ^ 2 * hspq.symm - 2 * g ^ 2 * hσi
      linear_combination hval2 + g ^ 2 * hspq
    exact (sq_eq_sq₀ dist_nonneg (by positivity)).mp h1
  -- the three heights
  have hheight0 : T.height 0 = g := by
    rw [Affine.Simplex.height, hfoot0, hg]
    rfl
  have hheight2 : T.height 2 = w := by
    rw [Affine.Simplex.height, hfoot2, hw]
    exact dist_comm C D
  have hheight1 : T.height 1 = g * w / s := by
    rw [Affine.Simplex.height, hfoot1]
    exact hdistF
  -- the incenter as an affine combination
  rw [Affine.Simplex.incenter_eq_affineCombination]
  have hconv := Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one
    Finset.univ (T.excenterWeights ∅) T.points
    (T.excenterExists_empty.sum_excenterWeights_eq_one) D
  rw [hconv, vadd_vsub]
  rw [Finset.weightedVSubOfPoint_apply, Fin.sum_univ_three]
  have hw0 : T.excenterWeights ∅ 0 = w / (w + s + g) := by
    rw [Affine.Simplex.excenterWeights, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three]
    simp only [Affine.Simplex.excenterWeightsUnnorm_empty_apply]
    rw [hheight0, hheight1, hheight2]
    field_simp [ne_of_gt hgpos, ne_of_gt hwpos, hs']
  have hw2 : T.excenterWeights ∅ 2 = g / (w + s + g) := by
    rw [Affine.Simplex.excenterWeights, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three]
    simp only [Affine.Simplex.excenterWeightsUnnorm_empty_apply]
    rw [hheight0, hheight1, hheight2]
    field_simp [ne_of_gt hgpos, ne_of_gt hwpos, hs']
  rw [hw0, hw2, hTpts]
  rw [show (![A, D, C] : Fin 3 → P) 0 = A from rfl,
    show (![A, D, C] : Fin 3 → P) 1 = D from rfl,
    show (![A, D, C] : Fin 3 → P) 2 = C from rfl]
  rw [vsub_self, smul_zero, add_zero]


/-- The `t`-parametrization relations: for `t = w/(g+s)` with `s² = g² + w²`
(half-angle substitution `t = tan(φ/2)` where `tan φ = w/g`). -/
lemma t_rels {g w s : ℝ} (hg : 0 < g) (hw : 0 < w) (hs : 0 < s)
    (hspq : s ^ 2 = g ^ 2 + w ^ 2) {t : ℝ} (ht : t = w / (g + s)) :
    0 < t ∧ t < 1 ∧ s = (1 + t ^ 2) * g / (1 - t ^ 2) ∧ w = 2 * t * g / (1 - t ^ 2) ∧
      w ^ 2 = 4 * t ^ 2 * g ^ 2 / (1 - t ^ 2) ^ 2 := by
  have hgs : (0 : ℝ) < g + s := add_pos hg hs
  have ht0 : 0 < t := by rw [ht]; positivity
  have hwlts : w < s := by
    have h1 : w ^ 2 < s ^ 2 := by nlinarith [hspq, hg]
    nlinarith [h1, le_of_lt hw, le_of_lt hs]
  have ht1 : t < 1 := by
    rw [ht]
    rw [div_lt_one hgs]
    linarith [hwlts, hg]
  have h1t2 : (0 : ℝ) < 1 - t ^ 2 := by nlinarith [ht0, ht1]
  have h1t2' : (1 : ℝ) - t ^ 2 ≠ 0 := ne_of_gt h1t2
  have htgs : t * (g + s) = w := by
    rw [ht]
    field_simp [ne_of_gt hgs]
  have hspq2 : w ^ 2 = s ^ 2 - g ^ 2 := by linear_combination -hspq
  have h1 : t ^ 2 * (g + s) * (g + s) = (s - g) * (g + s) := by
    linear_combination t * (g + s) * htgs + w * htgs + hspq2
  have h2 : t ^ 2 * (g + s) = s - g := mul_right_cancel₀ (ne_of_gt hgs) h1
  have h3 : g * (1 + t ^ 2) = s * (1 - t ^ 2) := by linear_combination h2
  have hsrel : s = (1 + t ^ 2) * g / (1 - t ^ 2) := by
    rw [eq_div_iff h1t2']
    linear_combination -h3
  have hwrel : w = 2 * t * g / (1 - t ^ 2) := by
    rw [eq_div_iff h1t2']
    linear_combination -(1 - t ^ 2) * htgs - t * h3
  have hw2rel : w ^ 2 = 4 * t ^ 2 * g ^ 2 / (1 - t ^ 2) ^ 2 := by
    rw [hwrel, div_pow]
    ring
  exact ⟨ht0, ht1, hsrel, hwrel, hw2rel⟩

/-- The barycentric coefficients of `E` and `K` in terms of `t`. -/
lemma coeff_vals {g w s : ℝ} (hg : 0 < g) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hsrel : s = (1 + t ^ 2) * g / (1 - t ^ 2)) (hwrel : w = 2 * t * g / (1 - t ^ 2))
    {e_a e_c k_a k_c : ℝ}
    (he_a0 : e_a = 2 * w / (s + 2 * w)) (he_c0 : e_c = s / (s + 2 * w))
    (hk_a0 : k_a = w / (w + s + g)) (hk_c0 : k_c = g / (w + s + g)) :
    e_a = 4 * t / (t ^ 2 + 4 * t + 1) ∧ e_c = (1 + t ^ 2) / (t ^ 2 + 4 * t + 1) ∧
    k_a = t / (1 + t) ∧ k_c = (1 - t) / 2 := by
  have h1t2 : (0 : ℝ) < 1 - t ^ 2 := by nlinarith [ht0, ht1]
  have hΔ : (0 : ℝ) < t ^ 2 + 4 * t + 1 := by nlinarith [ht0]
  have ht1' : (1 : ℝ) + t ≠ 0 := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [he_a0, hsrel, hwrel]
    field_simp [ne_of_gt hg, ne_of_gt h1t2, ne_of_gt hΔ]
    ring_nf
  · rw [he_c0, hsrel, hwrel]
    field_simp [ne_of_gt hg, ne_of_gt h1t2, ne_of_gt hΔ]
    ring_nf
  · rw [hk_a0, hsrel, hwrel]
    field_simp [ne_of_gt hg, ne_of_gt h1t2, ht1']
    ring_nf
  · rw [hk_c0, hsrel, hwrel]
    field_simp [ne_of_gt hg, ne_of_gt h1t2]
    ring_nf

/-- The algebraic heart: the angle condition `∠BEK = 45°` is equivalent to
`(t²-4t+1)(t²+2t-1) = 0` for `t = w/(g+s)` in `(0,1)`. The inner product `dot` is
always positive. -/
lemma heart_real {g w s t : ℝ} (hg : 0 < g) (hw : 0 < w) (ht0 : 0 < t) (ht1 : t < 1)
    (_hsrel : s = (1 + t ^ 2) * g / (1 - t ^ 2)) (hwrel : w = 2 * t * g / (1 - t ^ 2))
    (hw2rel : w ^ 2 = 4 * t ^ 2 * g ^ 2 / (1 - t ^ 2) ^ 2)
    {e_a e_c k_a k_c dot crs uu vv : ℝ}
    (he_a : e_a = 4 * t / (t ^ 2 + 4 * t + 1)) (he_c : e_c = (1 + t ^ 2) / (t ^ 2 + 4 * t + 1))
    (hk_a : k_a = t / (1 + t)) (hk_c : k_c = (1 - t) / 2)
    (hdot0 : dot = (-e_a) * (k_a - e_a) * g ^ 2 + (-(1 + e_c)) * (k_c - e_c) * w ^ 2)
    (hcrs0 : crs = ((-e_a) * (k_c - e_c) + (1 + e_c) * (k_a - e_a)) * g * w)
    (huu0 : uu = e_a ^ 2 * g ^ 2 + (1 + e_c) ^ 2 * w ^ 2)
    (hvv0 : vv = (k_a - e_a) ^ 2 * g ^ 2 + (k_c - e_c) ^ 2 * w ^ 2) :
    0 < dot ∧ (2 * dot ^ 2 = uu * vv ↔ (t ^ 2 - 4 * t + 1) * (t ^ 2 + 2 * t - 1) = 0) := by
  have h1t2 : (0 : ℝ) < 1 - t ^ 2 := by nlinarith only [ht0, ht1]
  have hΔ : (0 : ℝ) < t ^ 2 + 4 * t + 1 := by nlinarith only [ht0]
  have ht1' : (1 : ℝ) + t ≠ 0 := by positivity
  -- Lagrange identity
  have hL : uu * vv = dot ^ 2 + crs ^ 2 := by
    rw [huu0, hvv0, hdot0, hcrs0]
    ring
  -- the value of `dot`
  have htm2 : (1 : ℝ) - t * 2 + t ^ 2 ≠ 0 := by nlinarith only [ht0, ht1]
  have h1tm : (1 : ℝ) - t ≠ 0 := by linarith [ht1]
  have hdot : dot = g ^ 2 * (16 * t ^ 2 * (2 * t ^ 3 + t ^ 2 - 2 * t + 1) /
      ((1 - t) ^ 2 * (t + 1) * (t ^ 2 + 4 * t + 1) ^ 2)) := by
    rw [hdot0, he_a, he_c, hk_a, hk_c, hw2rel]
    field_simp [ne_of_gt h1t2, ne_of_gt hΔ, ht1', h1tm]
    ring_nf
  -- the value of `crs`
  have hcrs : crs = g * w * (4 * t * (t - 1) / (t ^ 2 + 4 * t + 1)) := by
    rw [hcrs0, he_a, he_c, hk_a, hk_c]
    field_simp [ne_of_gt hΔ, ht1']
    ring_nf
  -- the value of `dot + crs`
  have hdc : dot + crs = g ^ 2 * (-8 * t ^ 2 * (t ^ 2 - 4 * t + 1) * (t ^ 2 + 2 * t - 1) /
      ((1 - t) ^ 2 * (t + 1) * (t ^ 2 + 4 * t + 1) ^ 2)) := by
    rw [hdot, hcrs, hwrel]
    field_simp [ne_of_gt h1t2, ne_of_gt hΔ, ht1', h1tm]
    ring_nf
  -- signs
  have h4 : (0 : ℝ) < (1 - t) ^ 2 := by nlinarith only [ht1]
  have ht1p : (0 : ℝ) < t + 1 := by linarith [ht0]
  have hden : (0 : ℝ) < (1 - t) ^ 2 * (t + 1) * (t ^ 2 + 4 * t + 1) ^ 2 :=
    mul_pos (mul_pos h4 ht1p) (pow_pos hΔ 2)
  have hdotpos : 0 < dot := by
    rw [hdot]
    have h2 : (0 : ℝ) < 2 * t ^ 3 + t ^ 2 - 2 * t + 1 := by
      have h5 : 2 * t ^ 3 + t ^ 2 - 2 * t + 1 = 2 * t ^ 3 + (t - 1) ^ 2 := by ring
      rw [h5]
      have h6 : (0 : ℝ) < 2 * t ^ 3 := by positivity
      have h7 : (0 : ℝ) < (t - 1) ^ 2 := by nlinarith only [ht1]
      linarith [h6, h7]
    have ht2p : (0 : ℝ) < t ^ 2 := by positivity
    have h1 : (0 : ℝ) < 16 * t ^ 2 * (2 * t ^ 3 + t ^ 2 - 2 * t + 1) :=
      mul_pos (mul_pos (by norm_num) ht2p) h2
    exact mul_pos (pow_pos hg 2) (div_pos h1 hden)
  have hcrsneg : crs < 0 := by
    rw [hcrs]
    have h1 : (0 : ℝ) < g * w := by positivity
    have h2 : 4 * t * (t - 1) / (t ^ 2 + 4 * t + 1) < 0 := by
      rw [div_neg_iff]
      right
      constructor
      · nlinarith only [ht0, ht1]
      · exact hΔ
    exact mul_neg_of_pos_of_neg h1 h2
  have hdotcrs : 0 < dot - crs := by linarith [hdotpos, hcrsneg]
  refine ⟨hdotpos, ?_⟩
  -- the equivalence
  have hF : 2 * dot ^ 2 - uu * vv = (dot - crs) * (dot + crs) := by
    linear_combination -hL
  have hF2 : (2 * dot ^ 2 = uu * vv) ↔ ((dot - crs) * (dot + crs) = 0) := by
    constructor
    · intro h
      linear_combination h - hF
    · intro h
      linear_combination h + hF
  rw [hF2]
  have hne : dot - crs ≠ 0 := ne_of_gt hdotcrs
  rw [mul_eq_zero_iff_left hne]
  rw [hdc]
  constructor
  · intro h
    have h1 : ((1 - t) ^ 2 * (t + 1) * (t ^ 2 + 4 * t + 1) ^ 2) ≠ 0 := ne_of_gt hden
    have h3 : g ^ 2 ≠ 0 := by positivity
    have h5 : -8 * t ^ 2 * (t ^ 2 - 4 * t + 1) * (t ^ 2 + 2 * t - 1) = 0 := by
      rcases mul_eq_zero.mp h with h6 | h6
      · exact absurd h6 h3
      · rw [div_eq_zero_iff] at h6
        rcases h6 with h7 | h7
        · exact h7
        · exact absurd h7 h1
    have h8 : t ^ 2 ≠ 0 := by positivity
    rcases mul_eq_zero.mp h5 with h9 | h9
    · rcases mul_eq_zero.mp h9 with h11 | h11
      · rcases mul_eq_zero.mp h11 with h12 | h12
        · norm_num at h12
        · exact absurd h12 h8
      · rw [h11, zero_mul]
    · rw [h9, mul_zero]
  · intro h
    have h0 : -8 * t ^ 2 * (t ^ 2 - 4 * t + 1) * (t ^ 2 + 2 * t - 1) = 0 := by
      rw [show -8 * t ^ 2 * (t ^ 2 - 4 * t + 1) * (t ^ 2 + 2 * t - 1) =
        -8 * t ^ 2 * ((t ^ 2 - 4 * t + 1) * (t ^ 2 + 2 * t - 1)) by ring, h, mul_zero]
    rw [h0, zero_div, mul_zero]


/-- Bridge: for nonzero vectors `B -ᵥ E`, `K -ᵥ E`, the angle `∠BEK` equals `π/4`
iff `2·dot² = uu·vv` and `dot > 0`, where `dot = ⟪B -ᵥ E, K -ᵥ E⟫` and
`uu = ‖B -ᵥ E‖²`, `vv = ‖K -ᵥ E‖²`. -/
lemma angle_eq_pi_div_four_iff {B E K : P} {dot uu vv : ℝ}
    (hdot : dot = ⟪B -ᵥ E, K -ᵥ E⟫)
    (huu : uu = ‖B -ᵥ E‖ ^ 2)
    (hvv : vv = ‖K -ᵥ E‖ ^ 2)
    (hBEn : B ≠ E) (hEKn : K ≠ E) :
    ∠ B E K = Real.pi / 4 ↔ (2 * dot ^ 2 = uu * vv ∧ 0 < dot) := by
  have hN1 : ‖B -ᵥ E‖ ≠ 0 := by
    rw [← dist_eq_norm_vsub V B E]
    exact dist_ne_zero.mpr hBEn
  have hN2 : ‖K -ᵥ E‖ ≠ 0 := by
    rw [← dist_eq_norm_vsub V K E]
    exact dist_ne_zero.mpr hEKn
  have hN : (0 : ℝ) < ‖B -ᵥ E‖ * ‖K -ᵥ E‖ := by positivity
  have hcos : Real.cos (∠ B E K) = dot / (‖B -ᵥ E‖ * ‖K -ᵥ E‖) := by
    rw [EuclideanGeometry.angle, InnerProductGeometry.cos_angle, hdot]
  have hangle_mem : ∠ B E K ∈ Set.Icc 0 Real.pi := by
    rw [EuclideanGeometry.angle]
    exact ⟨InnerProductGeometry.angle_nonneg _ _, InnerProductGeometry.angle_le_pi _ _⟩
  have hpi4_mem : Real.pi / 4 ∈ Set.Icc 0 Real.pi := by
    constructor
    · positivity
    · linarith only [Real.pi_nonneg]
  have hsqrt : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by
    rw [div_pow, Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]
    norm_num
  constructor
  · intro h
    rw [h, Real.cos_pi_div_four] at hcos
    have h1 : dot = (‖B -ᵥ E‖ * ‖K -ᵥ E‖) * (Real.sqrt 2 / 2) := by
      rw [hcos]
      field_simp [hN1, hN2]
    refine ⟨?_, ?_⟩
    · rw [huu, hvv, h1, mul_pow, div_pow, Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]
      ring
    · rw [h1]
      positivity
  · intro h
    obtain ⟨h2d, hdpos⟩ := h
    have hcos2 : (dot / (‖B -ᵥ E‖ * ‖K -ᵥ E‖)) ^ 2 = 1 / 2 := by
      rw [huu, hvv] at h2d
      field_simp [hN1, hN2]
      linear_combination h2d
    have hcospos : 0 < dot / (‖B -ᵥ E‖ * ‖K -ᵥ E‖) := div_pos hdpos hN
    have hcosv : dot / (‖B -ᵥ E‖ * ‖K -ᵥ E‖) = Real.sqrt 2 / 2 :=
      (sq_eq_sq₀ (le_of_lt hcospos) (by positivity)).mp (by rw [hcos2, hsqrt])
    have h : Real.cos (∠ B E K) = Real.cos (Real.pi / 4) := by
      rw [hcos, hcosv, Real.cos_pi_div_four]
    exact Real.injOn_cos hangle_mem hpi4_mem h


/-- If `W` is on the line `YZ` but `XYZ` is a genuine triangle, then `X ≠ W`. -/
lemma ne_of_not_collinear_of_mem_line {X Y Z W : P}
    (hncol : ¬Collinear ℝ ({X, Y, Z} : Set P)) (hmem : W ∈ line[ℝ, Y, Z]) : X ≠ W := by
  intro h
  apply hncol
  rw [h]
  exact collinear_insert_of_mem_affineSpan_pair hmem

/-- Necessity: any configuration satisfying the problem's conditions has
`∠CAB ∈ {π/3, π/2}`. -/
lemma necessity {A B C D E K : P} (hABC : AffineIndependent ℝ ![A, B, C])
    (hADC : AffineIndependent ℝ ![A, D, C])
    (hAB : dist A B = dist A C)
    (hD : Sbtw ℝ B D C) (hAD : ∠ B A D = ∠ D A C)
    (hE : Sbtw ℝ C E A) (hBE : ∠ A B E = ∠ E B C)
    (hK : K = (⟨![A, D, C], hADC⟩ : Affine.Simplex ℝ P 2).incenter)
    (hBEK : ∠ B E K = Real.pi / 4) :
    ∠ C A B = Real.pi / 3 ∨ ∠ C A B = Real.pi / 2 := by
  -- nondegeneracy
  have hACn : A ≠ C := hABC.injective.ne (by decide : (0 : Fin 3) ≠ 2)
  have hncol : ¬Collinear ℝ ({A, B, C} : Set P) := affineIndependent_iff_not_collinear_set.mp hABC
  have hDmem : D ∈ line[ℝ, B, C] := by
    obtain ⟨t', ht', hDt⟩ := hD.mem_image_Ioo
    rw [← hDt]
    exact AffineMap.lineMap_mem_affineSpan_pair _ _ _
  have hEmem : E ∈ line[ℝ, C, A] := by
    obtain ⟨t', ht', hEt⟩ := hE.mem_image_Ioo
    rw [← hEt]
    exact AffineMap.lineMap_mem_affineSpan_pair _ _ _
  have hADn : A ≠ D := ne_of_not_collinear_of_mem_line hncol hDmem
  have hBEn : B ≠ E := by
    intro h
    apply hncol
    rw [h]
    have h1 : Collinear ℝ ({E, C, A} : Set P) := collinear_insert_of_mem_affineSpan_pair hEmem
    exact h1.subset (by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      tauto)
  have hCDn : C ≠ D := hD.ne_right.symm
  -- the normalization
  obtain ⟨hperp, hmid⟩ := perp_and_midpoint hD hACn hADn hAB hAD
  have huv : ⟪A -ᵥ D, C -ᵥ D⟫ = 0 := hperp
  have hvu : ⟪C -ᵥ D, A -ᵥ D⟫ = 0 := by rw [real_inner_comm]; exact hperp
  -- the coefficients of `E` and `K`
  have hED := bisector_foot_coeff hE hBE hmid hperp hADn hCDn hBEn
  have hKD : K -ᵥ D =
      (dist D C / (dist D C + dist A C + dist A D)) • (A -ᵥ D) +
      (dist A D / (dist D C + dist A C + dist A D)) • (C -ᵥ D) := by
    rw [hK]
    exact incenter_right_coeff hADC hperp
  -- abbreviations
  set g := dist A D with hg
  set w := dist D C with hw
  set s := dist A C with hs
  have hgpos : 0 < g := by rw [hg]; exact dist_pos.mpr hADn
  have hwpos : 0 < w := by rw [hw]; exact dist_pos.mpr hCDn.symm
  have hspos : 0 < s := by rw [hs]; exact dist_pos.mpr hACn
  have hgg : ⟪A -ᵥ D, A -ᵥ D⟫ = g ^ 2 := by
    rw [real_inner_self_eq_norm_sq, hg, ← dist_eq_norm_vsub V A D]
  have hww : ⟪C -ᵥ D, C -ᵥ D⟫ = w ^ 2 := by
    rw [real_inner_self_eq_norm_sq, hw, ← dist_eq_norm_vsub V C D, dist_comm]
  have hspq : s ^ 2 = g ^ 2 + w ^ 2 := by
    have h1 : ‖A -ᵥ C‖ ^ 2 = ‖A -ᵥ D‖ ^ 2 + ‖C -ᵥ D‖ ^ 2 := by
      rw [show A -ᵥ C = (A -ᵥ D) - (C -ᵥ D) from (vsub_sub_vsub_cancel_right A C D).symm,
        norm_sub_sq_real, huv]
      ring
    rw [hs, hg, hw, dist_comm D C, dist_eq_norm_vsub V A C, dist_eq_norm_vsub V A D,
      dist_eq_norm_vsub V C D, h1]
  set e_a := 2 * w / (s + 2 * w) with he_a0
  set e_c := s / (s + 2 * w) with he_c0
  set k_a := w / (w + s + g) with hk_a0
  set k_c := g / (w + s + g) with hk_c0
  -- `E ≠ K` by comparing coefficients
  have hsw2 : (0 : ℝ) < s + 2 * w := by positivity
  have hP : (0 : ℝ) < w + s + g := by positivity
  have hEKn : E ≠ K := by
    intro h
    have h1 : E -ᵥ D = K -ᵥ D := by rw [h]
    rw [hED, hKD] at h1
    have h2 : (e_a - k_a) • (A -ᵥ D) + (e_c - k_c) • (C -ᵥ D) = 0 := by
      have h3 := h1
      calc (e_a - k_a) • (A -ᵥ D) + (e_c - k_c) • (C -ᵥ D)
          = (e_a • (A -ᵥ D) + e_c • (C -ᵥ D)) - (k_a • (A -ᵥ D) + k_c • (C -ᵥ D)) := by
            module
        _ = 0 := by rw [h3, sub_self]
    have h4 : e_a - k_a = 0 := by
      have h5 := congr_arg (fun x => ⟪A -ᵥ D, x⟫) h2
      simp only [inner_add_right, real_inner_smul_right, huv, hgg, inner_zero_right,
        mul_zero, add_zero] at h5
      have h6 : g ^ 2 ≠ 0 := by positivity
      rcases mul_eq_zero.mp h5 with h7 | h7
      · exact h7
      · exact absurd h7 h6
    have h8 : e_a = k_a := sub_eq_zero.mp h4
    rw [he_a0, hk_a0] at h8
    field_simp [ne_of_gt hsw2, ne_of_gt hP] at h8
    nlinarith only [h8, hgpos, hspos, hwpos]
  -- vector expressions for `B -ᵥ E` and `K -ᵥ E`
  have hBEv : B -ᵥ E = (-e_a) • (A -ᵥ D) + (-(1 + e_c)) • (C -ᵥ D) := by
    have h2 : B -ᵥ E = (B -ᵥ D) - (E -ᵥ D) := (vsub_sub_vsub_cancel_right B E D).symm
    rw [h2, hmid, hED]
    module
  have hKEv : K -ᵥ E = (k_a - e_a) • (A -ᵥ D) + (k_c - e_c) • (C -ᵥ D) := by
    have h2 : K -ᵥ E = (K -ᵥ D) - (E -ᵥ D) := (vsub_sub_vsub_cancel_right K E D).symm
    rw [h2, hKD, hED]
    module
  -- the scalar invariants
  set dot := (-e_a) * (k_a - e_a) * g ^ 2 + (-(1 + e_c)) * (k_c - e_c) * w ^ 2 with hdot0
  set uu := e_a ^ 2 * g ^ 2 + (1 + e_c) ^ 2 * w ^ 2 with huu0
  set vv := (k_a - e_a) ^ 2 * g ^ 2 + (k_c - e_c) ^ 2 * w ^ 2 with hvv0
  set crs := ((-e_a) * (k_c - e_c) + (1 + e_c) * (k_a - e_a)) * g * w with hcrs0
  have hdot : dot = ⟪B -ᵥ E, K -ᵥ E⟫ := by
    rw [hdot0, hBEv, hKEv]
    simp only [inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right, huv, hvu, hgg, hww]
    ring
  have huu : uu = ‖B -ᵥ E‖ ^ 2 := by
    rw [huu0, hBEv, ← real_inner_self_eq_norm_sq]
    simp only [inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right, huv, hvu, hgg, hww]
    ring
  have hvv : vv = ‖K -ᵥ E‖ ^ 2 := by
    rw [hvv0, hKEv, ← real_inner_self_eq_norm_sq]
    simp only [inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right, huv, hvu, hgg, hww]
    ring
  -- apply the bridge and the algebraic heart
  obtain ⟨h2d, hdpos⟩ := (angle_eq_pi_div_four_iff hdot huu hvv hBEn hEKn.symm).mp hBEK
  set t := w / (g + s) with ht
  obtain ⟨ht0, ht1, hsrel, hwrel, hw2rel⟩ := t_rels hgpos hwpos hspos hspq ht
  obtain ⟨he_a, he_c, hk_a, hk_c⟩ := coeff_vals hgpos ht0 ht1 hsrel hwrel he_a0 he_c0 hk_a0 hk_c0
  obtain ⟨-, hiff⟩ := heart_real hgpos hwpos ht0 ht1 hsrel hwrel hw2rel he_a he_c hk_a hk_c
    hdot0 hcrs0 huu0 hvv0
  have hPQ : (t ^ 2 - 4 * t + 1) * (t ^ 2 + 2 * t - 1) = 0 := hiff.mp h2d
  have h1t2' : (1 : ℝ) - t ^ 2 ≠ 0 := by nlinarith only [ht0, ht1]
  -- cosine of the answer angle
  have hcosCAB : Real.cos (∠ C A B) = (g ^ 2 - w ^ 2) / (s * s) := by
    rw [EuclideanGeometry.angle, InnerProductGeometry.cos_angle]
    have hCAv : C -ᵥ A = (C -ᵥ D) - (A -ᵥ D) := (vsub_sub_vsub_cancel_right C A D).symm
    have hBAv : B -ᵥ A = -(C -ᵥ D) - (A -ᵥ D) := by
      have h2 : B -ᵥ A = (B -ᵥ D) - (A -ᵥ D) := (vsub_sub_vsub_cancel_right B A D).symm
      rw [h2, hmid]
    have hnAB : ‖B -ᵥ A‖ = s := by
      have h1 : ‖(A -ᵥ D) + (C -ᵥ D)‖ ^ 2 = ‖(A -ᵥ D) - (C -ᵥ D)‖ ^ 2 := by
        rw [norm_add_sq_real, norm_sub_sq_real, huv]
        ring
      have h2 : ‖(A -ᵥ D) + (C -ᵥ D)‖ = ‖(A -ᵥ D) - (C -ᵥ D)‖ := by
        have h3 : 0 ≤ ‖(A -ᵥ D) + (C -ᵥ D)‖ := norm_nonneg _
        have h4 : 0 ≤ ‖(A -ᵥ D) - (C -ᵥ D)‖ := norm_nonneg _
        nlinarith only [h1, h3, h4]
      have h5 : B -ᵥ A = -((A -ᵥ D) + (C -ᵥ D)) := by
        rw [hBAv]
        module
      rw [h5, norm_neg, h2, hs, dist_eq_norm_vsub V A C]
      congr 1
      exact vsub_sub_vsub_cancel_right A C D
    have hnormCA : ‖C -ᵥ A‖ = s := by rw [hs, ← dist_eq_norm_vsub V C A, dist_comm]
    rw [hnormCA, hnAB, hCAv, hBAv]
    have hnum : ⟪(C -ᵥ D) - (A -ᵥ D), -(C -ᵥ D) - (A -ᵥ D)⟫ = g ^ 2 - w ^ 2 := by
      simp only [inner_sub_left, inner_sub_right, inner_neg_right,
        huv, hvu, hgg, hww]
      ring
    rw [hnum]
  have hangle_mem : ∠ C A B ∈ Set.Icc 0 Real.pi := by
    rw [EuclideanGeometry.angle]
    exact ⟨InnerProductGeometry.angle_nonneg _ _, InnerProductGeometry.angle_le_pi _ _⟩
  -- the two cases
  rcases mul_eq_zero.mp hPQ with hP2 | hQ2
  · -- case `t² = 4t - 1`, giving `∠CAB = π/3`
    left
    have ht2v : t ^ 2 = 4 * t - 1 := by linear_combination hP2
    have h12 : (1 - t ^ 2) ^ 2 = 12 * t ^ 2 := by
      have h1t2v : 1 - t ^ 2 = 2 - 4 * t := by linear_combination -ht2v
      rw [h1t2v]
      linear_combination 4 * ht2v
    have ht2ne : 12 * t ^ 2 ≠ 0 := by positivity
    have h3w : 3 * w ^ 2 = g ^ 2 := by
      rw [hw2rel, h12]
      field_simp [ht2ne]
      ring
    have hcos0 : Real.cos (∠ C A B) = 1 / 2 := by
      rw [hcosCAB, show s * s = s ^ 2 from (sq s).symm, hspq,
        show g ^ 2 + w ^ 2 = 4 * w ^ 2 by linear_combination -h3w,
        show g ^ 2 - w ^ 2 = 2 * w ^ 2 by linear_combination -h3w,
        div_eq_iff (show (4:ℝ) * w ^ 2 ≠ 0 by positivity)]
      ring
    have hpi3 : Real.pi / 3 ∈ Set.Icc 0 Real.pi :=
      ⟨by positivity, by linarith only [Real.pi_nonneg]⟩
    have h : Real.cos (∠ C A B) = Real.cos (Real.pi / 3) := by
      rw [hcos0, Real.cos_pi_div_three]
    exact Real.injOn_cos hangle_mem hpi3 h
  · -- case `t² = 1 - 2t`, giving `∠CAB = π/2`
    right
    have h1t2v : 1 - t ^ 2 = 2 * t := by linear_combination -hQ2
    have hwg : w = g := by
      have h1 : w * (1 - t ^ 2) = 2 * t * g := by
        rw [hwrel]
        field_simp [h1t2']
      rw [h1t2v] at h1
      have ht2t : (2 : ℝ) * t ≠ 0 := by positivity
      exact mul_right_cancel₀ ht2t (by linear_combination h1)
    have hcos0 : Real.cos (∠ C A B) = 0 := by
      rw [hcosCAB, hwg, sub_self, zero_div]
    have hpi2 : Real.pi / 2 ∈ Set.Icc 0 Real.pi :=
      ⟨by positivity, by linarith only [Real.pi_nonneg]⟩
    have h : Real.cos (∠ C A B) = Real.cos (Real.pi / 2) := by
      rw [hcos0, Real.cos_pi_div_two]
    exact Real.injOn_cos hangle_mem hpi2 h


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Inner product of two linear combinations of orthogonal vectors. -/
lemma inner_comb {u v : V} (h : ⟪u, v⟫ = 0) (a b c d : ℝ) :
    ⟪a • u + b • v, c • u + d • v⟫ = a * c * ⟪u, u⟫ + b * d * ⟪v, v⟫ := by
  have hv : ⟪v, u⟫ = 0 := by rw [real_inner_comm]; exact h
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    h, hv]
  ring

/-- Squared norm of a linear combination of orthogonal vectors. -/
lemma norm_sq_comb {u v : V} (h : ⟪u, v⟫ = 0) (a b : ℝ) :
    ‖a • u + b • v‖ ^ 2 = a ^ 2 * ⟪u, u⟫ + b ^ 2 * ⟪v, v⟫ := by
  rw [← real_inner_self_eq_norm_sq, inner_comb h a b a b, sq, sq]

/-- If `⟪U, W⟫ = 0`, `⟪U, Z⟫ = 0`, `U ≠ 0` and `⟪W, Z - W⟫ ≠ 0`, then `U, Z, W`
are affinely independent. -/
lemma affineIndependent_of_perp {U W Z : V}
    (hUW : ⟪U, W⟫ = 0) (hUZ : ⟪U, Z⟫ = 0) (hU : U ≠ 0) (hZW : ⟪W, Z - W⟫ ≠ 0) :
    AffineIndependent ℝ ![U, Z, W] := by
  rw [affineIndependent_iff_not_collinear_set]
  intro hcol
  rw [collinear_iff_of_mem (show U ∈ ({U, Z, W} : Set V) by simp)] at hcol
  obtain ⟨v, hv⟩ := hcol
  obtain ⟨r₁, hr₁⟩ := hv Z (by simp)
  obtain ⟨r₂, hr₂⟩ := hv W (by simp)
  have h1 : Z - U = r₁ • v := by rw [hr₁, vadd_eq_add]; abel
  have h2 : W - U = r₂ • v := by rw [hr₂, vadd_eq_add]; abel
  have h3 : ⟪U, Z - U⟫ = r₁ * ⟪U, v⟫ := by rw [h1, real_inner_smul_right]
  have h4 : ⟪U, W - U⟫ = r₂ * ⟪U, v⟫ := by rw [h2, real_inner_smul_right]
  have h5 : ⟪U, Z - U⟫ = -⟪U, U⟫ := by
    simp only [inner_sub_right, hUZ, zero_sub]
  have h6 : ⟪U, W - U⟫ = -⟪U, U⟫ := by
    simp only [inner_sub_right, hUW, zero_sub]
  have h7 : (r₁ - r₂) * ⟪U, v⟫ = 0 := by
    have h10 : r₁ * ⟪U, v⟫ = r₂ * ⟪U, v⟫ := by linarith [h3, h4, h5, h6]
    linear_combination h10
  have h8 : Z - W = (r₁ - r₂) • v := by
    have h9 : Z - W = (Z - U) - (W - U) := by abel
    rw [h9, h1, h2]
    module
  have h9 : ⟪W, Z - W⟫ = (r₁ - r₂) * ⟪W, v⟫ := by rw [h8, real_inner_smul_right]
  have h10 : r₁ - r₂ ≠ 0 := by
    intro h11
    rw [h11, zero_mul] at h9
    exact hZW h9
  have h11 : ⟪U, v⟫ = 0 := by
    rcases mul_eq_zero.mp h7 with h12 | h12
    · exact absurd h12 h10
    · exact h12
  have h12 : ⟪U, U⟫ = 0 := by
    rw [h11, mul_zero] at h3
    linarith [h3, h5]
  rw [inner_self_eq_zero] at h12
  exact hU h12


/-- Sufficiency: for `g, w > 0`, if `t = w/(g+s)` (with `s = √(g²+w²)`) satisfies the
critical polynomial, then the explicit configuration `A = U, B = -W, C = W, D = 0`
(with `⟪U, W⟫ = 0`, `‖U‖ = g`, `‖W‖ = w`) satisfies all the problem's conditions,
and `cos ∠CAB = (g²-w²)/(g²+w²)`. -/
lemma suff_config {U W : V}
    (hUW : ⟪U, W⟫ = 0) {g w : ℝ} (hgU : ‖U‖ = g) (hwW : ‖W‖ = w)
    (hg : 0 < g) (hw : 0 < w)
    {t : ℝ} (ht : t = w / (g + Real.sqrt (g ^ 2 + w ^ 2)))
    (hPQ : (t ^ 2 - 4 * t + 1) * (t ^ 2 + 2 * t - 1) = 0) :
    ∃ (A B C D E K : V) (_hABC : AffineIndependent ℝ ![A, B, C])
      (hADC : AffineIndependent ℝ ![A, D, C]),
      dist A B = dist A C ∧ Sbtw ℝ B D C ∧ ∠ B A D = ∠ D A C ∧
      Sbtw ℝ C E A ∧ ∠ A B E = ∠ E B C ∧
      K = (⟨![A, D, C], hADC⟩ : Affine.Simplex ℝ V 2).incenter ∧
      ∠ B E K = Real.pi / 4 ∧ Real.cos (∠ C A B) = (g ^ 2 - w ^ 2) / (g ^ 2 + w ^ 2) := by
  -- basic data
  have hU : U ≠ 0 := by
    rw [← norm_ne_zero_iff, hgU]
    positivity
  have hW : W ≠ 0 := by
    rw [← norm_ne_zero_iff, hwW]
    positivity
  have hWU : ⟪W, U⟫ = 0 := by rw [real_inner_comm]; exact hUW
  set s : ℝ := Real.sqrt (g ^ 2 + w ^ 2) with hs
  have hs2 : s ^ 2 = g ^ 2 + w ^ 2 := by
    rw [hs]
    exact Real.sq_sqrt (by positivity)
  have hspos : 0 < s := by rw [hs]; positivity
  have hUnorm : ⟪U, U⟫ = g ^ 2 := by rw [real_inner_self_eq_norm_sq, hgU]
  have hWnorm : ⟪W, W⟫ = w ^ 2 := by rw [real_inner_self_eq_norm_sq, hwW]
  -- norm computations
  have hnormUW : ‖U - W‖ = s := by
    have h1 : ‖U - W‖ ^ 2 = s ^ 2 := by
      rw [norm_sub_sq_real, hUW, hs2, hgU, hwW]
      ring
    exact (sq_eq_sq₀ (norm_nonneg _) (le_of_lt hspos)).mp h1
  have hnormUpW : ‖U + W‖ = s := by
    have h1 : ‖U + W‖ ^ 2 = s ^ 2 := by
      rw [norm_add_sq_real, hUW, hs2, hgU, hwW]
      ring
    exact (sq_eq_sq₀ (norm_nonneg _) (le_of_lt hspos)).mp h1
  have hnormWU : ‖W - U‖ = s := by
    rw [show W - U = -(U - W) by abel, norm_neg, hnormUW]
  have hnormmWmU : ‖-W - U‖ = s := by
    rw [show -W - U = -(U + W) by abel, norm_neg, hnormUpW]
  -- distances
  have hdAD : dist U (0 : V) = g := by rw [dist_zero_right, hgU]
  have hdDC : dist (0 : V) W = w := by rw [dist_zero_left, hwW]
  have hdAC : dist U W = s := by rw [dist_eq_norm, hnormUW]
  have hdAB : dist U (-W) = s := by
    rw [dist_eq_norm, show U - (-W) = U + W by abel, hnormUpW]
  -- affine independence
  have hABC : AffineIndependent ℝ ![U, -W, W] :=
    affineIndependent_of_perp hUW (by rw [inner_neg_right, hUW, neg_zero]) hU (by
      have h1 : ⟪W, -W - W⟫ = -2 * ⟪W, W⟫ := by
        simp only [inner_sub_right, inner_neg_right]
        ring
      rw [h1, hWnorm]
      exact mul_ne_zero (by norm_num : (-2 : ℝ) ≠ 0) (pow_ne_zero 2 (ne_of_gt hw)))
  have hADC : AffineIndependent ℝ ![U, (0 : V), W] :=
    affineIndependent_of_perp hUW (by rw [inner_zero_right]) hU (by
      have h1 : ⟪W, (0 : V) - W⟫ = -⟪W, W⟫ := by
        simp only [inner_neg_right, zero_sub]
      rw [h1, hWnorm]
      exact neg_ne_zero.mpr (pow_ne_zero 2 (ne_of_gt hw)))
  -- `D = 0` strictly between `B = -W` and `C = W`
  have hDBC : Sbtw ℝ (-W) (0 : V) W := by
    rw [sbtw_iff_mem_image_Ioo_and_ne]
    constructor
    · use (1 / 2 : ℝ)
      constructor
      · norm_num [Set.mem_Ioo]
      · rw [AffineMap.lineMap_apply, vadd_eq_add, vsub_eq_sub]
        module
    · intro h
      have h1 : W = -W := h.symm
      have h2 : ⟪W, W⟫ = 0 := by
        have h3 := congr_arg (⟪W, ·⟫) h1
        rw [inner_neg_right] at h3
        linarith [h3]
      rw [hWnorm] at h2
      exact pow_ne_zero 2 (ne_of_gt hw) h2
  -- `∠BAD = ∠DAC` via cosines
  have hBAD_DAC : ∠ (-W) U (0 : V) = ∠ (0 : V) U W := by
    have hcos1 : Real.cos (∠ (-W) U (0 : V)) = g / s := by
      rw [EuclideanGeometry.angle, InnerProductGeometry.cos_angle]
      have h1 : (-W) -ᵥ U = -W - U := by rw [vsub_eq_sub]
      have h2 : (0 : V) -ᵥ U = -U := by rw [vsub_eq_sub, zero_sub]
      rw [h1, h2]
      have h3 : ⟪-W - U, -U⟫ = g ^ 2 := by
        simp only [inner_neg_right, inner_sub_left, inner_neg_left, hWU, hUnorm]
        ring
      have h6 : ‖-U‖ = g := by rw [norm_neg, hgU]
      rw [h3, hnormmWmU, h6]
      field_simp [ne_of_gt hg, ne_of_gt hspos]
    have hcos2 : Real.cos (∠ (0 : V) U W) = g / s := by
      rw [EuclideanGeometry.angle, InnerProductGeometry.cos_angle]
      have h1 : (0 : V) -ᵥ U = -U := by rw [vsub_eq_sub, zero_sub]
      have h2 : W -ᵥ U = W - U := by rw [vsub_eq_sub]
      rw [h1, h2]
      have h3 : ⟪-U, W - U⟫ = g ^ 2 := by
        simp only [inner_neg_left, inner_sub_right, hUW, hUnorm]
        ring
      have h4 : ‖-U‖ = g := by rw [norm_neg, hgU]
      rw [h3, h4, hnormWU]
      field_simp [ne_of_gt hg, ne_of_gt hspos]
    have hmem1 : ∠ (-W) U (0 : V) ∈ Set.Icc 0 Real.pi := by
      rw [EuclideanGeometry.angle]
      exact ⟨InnerProductGeometry.angle_nonneg _ _, InnerProductGeometry.angle_le_pi _ _⟩
    have hmem2 : ∠ (0 : V) U W ∈ Set.Icc 0 Real.pi := by
      rw [EuclideanGeometry.angle]
      exact ⟨InnerProductGeometry.angle_nonneg _ _, InnerProductGeometry.angle_le_pi _ _⟩
    exact Real.injOn_cos hmem1 hmem2 (by rw [hcos1, hcos2])
  -- coefficients of `E` and `K`
  have hsw2 : (0 : ℝ) < s + 2 * w := by positivity
  have hP : (0 : ℝ) < w + s + g := by positivity
  set e_a : ℝ := 2 * w / (s + 2 * w) with he_a0
  set e_c : ℝ := s / (s + 2 * w) with he_c0
  set k_a : ℝ := w / (w + s + g) with hk_a0
  set k_c : ℝ := g / (w + s + g) with hk_c0
  set E : V := e_a • U + e_c • W with hE
  set K : V := k_a • U + k_c • W with hK
  have he_a_pos : 0 < e_a := by rw [he_a0]; positivity
  have he_a_lt : e_a < 1 := by
    rw [he_a0, div_lt_one hsw2]
    linarith only [hspos]
  have he_c_eq : e_c = 1 - e_a := by
    rw [he_c0, he_a0]
    field_simp [ne_of_gt hsw2]
    ring
  -- `E` strictly between `C = W` and `A = U`
  have hECA : Sbtw ℝ W E U := by
    rw [sbtw_iff_mem_image_Ioo_and_ne]
    constructor
    · use e_a
      constructor
      · exact ⟨he_a_pos, he_a_lt⟩
      · rw [hE, AffineMap.lineMap_apply, he_c_eq, vadd_eq_add, vsub_eq_sub]
        module
    · intro h
      rw [h] at hUW
      rw [hUnorm] at hUW
      exact (ne_of_gt (by positivity : (0:ℝ) < g ^ 2)) hUW
  -- `K` is the incenter
  have hperp : ⟪U -ᵥ (0 : V), W -ᵥ (0 : V)⟫ = 0 := by
    simp only [vsub_eq_sub, sub_zero]
    exact hUW
  have hKinc : K = (⟨![U, (0 : V), W], hADC⟩ : Affine.Simplex ℝ V 2).incenter := by
    have h1 := incenter_right_coeff hADC hperp
    rw [hdAD, hdDC, hdAC] at h1
    simp only [vsub_eq_sub, sub_zero] at h1
    rw [hK, hk_a0, hk_c0, h1]
  -- `E ≠ B` and `E ≠ K`
  have hBEn : (-W) ≠ E := by
    intro h
    rw [hE] at h
    have h1 : e_a • U + (e_c + 1) • W = 0 := by
      rw [add_smul, one_smul, ← add_assoc, ← h]
      abel
    have h3 := congr_arg (fun x => ⟪U, x⟫) h1
    simp only [inner_add_right, real_inner_smul_right, hUW, hUnorm, inner_zero_right,
      mul_zero, add_zero] at h3
    have h4 : e_a * g ^ 2 = 0 := by linarith [h3]
    have h5 : g ^ 2 ≠ 0 := by positivity
    exact (ne_of_gt he_a_pos) (by
      rcases mul_eq_zero.mp h4 with h6 | h6
      · exact h6
      · exact absurd h6 h5)
  have hEKn : E ≠ K := by
    intro h
    rw [hE, hK] at h
    have h1 : (e_a - k_a) • U + (e_c - k_c) • W = 0 := by
      rw [sub_smul, sub_smul]
      have h3 : e_a • U - k_a • U + (e_c • W - k_c • W) =
          e_a • U + e_c • W - (k_a • U + k_c • W) := by abel
      rw [h3, h, sub_self]
    have h3 := congr_arg (fun x => ⟪U, x⟫) h1
    simp only [inner_add_right, real_inner_smul_right, hUW, hUnorm, inner_zero_right,
      mul_zero, add_zero] at h3
    have h4 : e_a - k_a = 0 := by
      have h6 : g ^ 2 ≠ 0 := by positivity
      rcases mul_eq_zero.mp (show (e_a - k_a) * g ^ 2 = 0 by linarith [h3]) with h7 | h7
      · exact h7
      · exact absurd h7 h6
    have h8 : e_a = k_a := sub_eq_zero.mp h4
    rw [he_a0, hk_a0] at h8
    field_simp [ne_of_gt hsw2, ne_of_gt hP] at h8
    nlinarith only [h8, hg, hspos, hw]
  -- vector forms
  have hBEv : (-W) -ᵥ E = (-e_a) • (U -ᵥ (0 : V)) + (-(1 + e_c)) • (W -ᵥ (0 : V)) := by
    rw [hE]
    simp only [vsub_eq_sub, sub_zero]
    module
  have hKEv : K -ᵥ E = (k_a - e_a) • (U -ᵥ (0 : V)) + (k_c - e_c) • (W -ᵥ (0 : V)) := by
    rw [hE, hK]
    simp only [vsub_eq_sub, sub_zero]
    module
  -- scalar invariants
  set dot : ℝ := (-e_a) * (k_a - e_a) * g ^ 2 + (-(1 + e_c)) * (k_c - e_c) * w ^ 2 with hdot0
  set uu : ℝ := e_a ^ 2 * g ^ 2 + (1 + e_c) ^ 2 * w ^ 2 with huu0
  set vv : ℝ := (k_a - e_a) ^ 2 * g ^ 2 + (k_c - e_c) ^ 2 * w ^ 2 with hvv0
  set crs : ℝ := ((-e_a) * (k_c - e_c) + (1 + e_c) * (k_a - e_a)) * g * w with hcrs0
  have hdot : dot = ⟪(-W) -ᵥ E, K -ᵥ E⟫ := by
    rw [hdot0, hBEv, hKEv]
    simp only [vsub_eq_sub, sub_zero, inner_comb hUW, hUnorm, hWnorm]
  have huu : uu = ‖(-W) -ᵥ E‖ ^ 2 := by
    rw [huu0, hBEv]
    simp only [vsub_eq_sub, sub_zero, norm_sq_comb hUW, hUnorm, hWnorm]
    ring
  have hvv : vv = ‖K -ᵥ E‖ ^ 2 := by
    rw [hvv0, hKEv]
    simp only [vsub_eq_sub, sub_zero, norm_sq_comb hUW, hUnorm, hWnorm]
  -- the t-relations and the heart
  have ht' : t = w / (g + s) := by rw [ht, hs]
  obtain ⟨ht0, ht1, hsrel, hwrel, hw2rel⟩ := t_rels hg hw hspos hs2 ht'
  obtain ⟨he_a, he_c, hk_a, hk_c⟩ := coeff_vals hg ht0 ht1 hsrel hwrel he_a0 he_c0 hk_a0 hk_c0
  obtain ⟨hdotpos, hiff⟩ := heart_real hg hw ht0 ht1 hsrel hwrel hw2rel he_a he_c hk_a hk_c
    hdot0 hcrs0 huu0 hvv0
  have h2d : 2 * dot ^ 2 = uu * vv := hiff.mpr hPQ
  have hBEK : ∠ (-W) E K = Real.pi / 4 :=
    (angle_eq_pi_div_four_iff hdot huu hvv hBEn hEKn.symm).mpr ⟨h2d, hdotpos⟩
  -- `∠ABE = ∠EBC` via cosines, using the bisector relation `e_a * (s + 2w) = 2w`
  have hABE : ∠ U (-W) E = ∠ E (-W) W := by
    have hN : ‖E -ᵥ (-W)‖ ≠ 0 := by
      rw [← dist_eq_norm_vsub V E (-W)]
      exact dist_ne_zero.mpr (fun h => hBEn h.symm)
    have hEBv : E -ᵥ (-W) = e_a • (U -ᵥ (0 : V)) + (2 - e_a) • (W -ᵥ (0 : V)) := by
      rw [hE]
      simp only [vsub_eq_sub, sub_zero]
      rw [sub_neg_eq_add, he_c_eq, sub_smul, sub_smul, one_smul, two_smul]
      abel
    have hBAv : U -ᵥ (-W) = (1 : ℝ) • U + (1 : ℝ) • W := by
      simp only [vsub_eq_sub]
      module
    have hCBv : W -ᵥ (-W) = (2 : ℝ) • (W -ᵥ (0 : V)) := by
      simp only [vsub_eq_sub, sub_zero]
      module
    have hnormAB : ‖U -ᵥ (-W)‖ = s := by
      rw [hBAv]
      simp only [one_smul]
      exact hnormUpW
    have hnormCB : ‖W -ᵥ (-W)‖ = 2 * w := by
      rw [hCBv]
      simp only [vsub_eq_sub, sub_zero, norm_smul, Real.norm_ofNat, hwW]
    have hcos1 : Real.cos (∠ U (-W) E) * (s * ‖E -ᵥ (-W)‖) =
        e_a * g ^ 2 + (2 - e_a) * w ^ 2 := by
      rw [EuclideanGeometry.angle, InnerProductGeometry.cos_angle, hnormAB]
      rw [hBAv, hEBv]
      have hN' : ‖e_a • U + (2 - e_a) • W‖ ≠ 0 := by
        have h1 := hN
        rw [hEBv] at h1
        simpa only [vsub_eq_sub, sub_zero] using h1
      simp only [vsub_eq_sub, sub_zero, inner_comb hUW, hUnorm, hWnorm]
      field_simp [ne_of_gt hspos, hN']
    have hcos2 : Real.cos (∠ E (-W) W) * (‖E -ᵥ (-W)‖ * (2 * w)) =
        2 * (2 - e_a) * w ^ 2 := by
      rw [EuclideanGeometry.angle, InnerProductGeometry.cos_angle, hnormCB]
      rw [hEBv, hCBv]
      have hN' : ‖e_a • U + (2 - e_a) • W‖ ≠ 0 := by
        have h1 := hN
        rw [hEBv] at h1
        simpa only [vsub_eq_sub, sub_zero] using h1
      simp only [vsub_eq_sub, sub_zero]
      have h8 : ⟪e_a • U + (2 - e_a) • W, (2 : ℝ) • W⟫ = 2 * (2 - e_a) * w ^ 2 := by
        simp only [inner_add_left, real_inner_smul_left, real_inner_smul_right, hUW, hWnorm]
        ring
      rw [h8]
      field_simp [hN', ne_of_gt hw]
    have hkey : e_a * (s + 2 * w) = 2 * w := by
      rw [he_a0]
      field_simp [ne_of_gt hsw2]
    have hcos_eq : Real.cos (∠ U (-W) E) = Real.cos (∠ E (-W) W) := by
      have hX2 : (e_a * g ^ 2 + (2 - e_a) * w ^ 2) * (s + 2 * w) =
          (2 - e_a) * w * s * (s + 2 * w) := by
        linear_combination (g ^ 2 - w ^ 2 + w * s) * hkey - 2 * w * hs2
      have hX : e_a * g ^ 2 + (2 - e_a) * w ^ 2 = (2 - e_a) * w * s :=
        mul_right_cancel₀ (ne_of_gt hsw2) hX2
      have h1 : Real.cos (∠ U (-W) E) * (s * ‖E -ᵥ (-W)‖) = (2 - e_a) * w * s := by
        linear_combination hcos1 + hX
      have h2 : Real.cos (∠ E (-W) W) * (‖E -ᵥ (-W)‖ * (2 * w)) =
          (2 - e_a) * w * (2 * w) := by
        linear_combination hcos2
      have h3 : Real.cos (∠ U (-W) E) * (s * ‖E -ᵥ (-W)‖) * (2 * w) =
          Real.cos (∠ E (-W) W) * (‖E -ᵥ (-W)‖ * (2 * w)) * s := by
        linear_combination h1 * (2 * w) - h2 * s
      have h4 : (Real.cos (∠ U (-W) E) - Real.cos (∠ E (-W) W)) *
          (s * ‖E -ᵥ (-W)‖ * (2 * w)) = 0 := by
        linear_combination h3
      have h5 : s * ‖E -ᵥ (-W)‖ * (2 * w) ≠ 0 := by positivity
      rcases mul_eq_zero.mp h4 with h6 | h6
      · linarith [h6]
      · exact absurd h6 h5
    have hmem1 : ∠ U (-W) E ∈ Set.Icc 0 Real.pi := by
      rw [EuclideanGeometry.angle]
      exact ⟨InnerProductGeometry.angle_nonneg _ _, InnerProductGeometry.angle_le_pi _ _⟩
    have hmem2 : ∠ E (-W) W ∈ Set.Icc 0 Real.pi := by
      rw [EuclideanGeometry.angle]
      exact ⟨InnerProductGeometry.angle_nonneg _ _, InnerProductGeometry.angle_le_pi _ _⟩
    exact Real.injOn_cos hmem1 hmem2 hcos_eq
  -- `cos ∠CAB`
  have hcosCAB : Real.cos (∠ W U (-W)) = (g ^ 2 - w ^ 2) / (g ^ 2 + w ^ 2) := by
    rw [EuclideanGeometry.angle, InnerProductGeometry.cos_angle]
    have h1 : W -ᵥ U = W - U := by rw [vsub_eq_sub]
    have h2 : (-W) -ᵥ U = -W - U := by rw [vsub_eq_sub]
    rw [h1, h2]
    have h3 : ⟪W - U, -W - U⟫ = g ^ 2 - w ^ 2 := by
      simp only [inner_sub_left, inner_sub_right, inner_neg_right, hUW, hWU, hUnorm, hWnorm]
      ring
    rw [h3, hnormWU, hnormmWmU, show s * s = s ^ 2 from (sq s).symm, hs2]
  exact ⟨U, -W, W, 0, E, K, hABC, hADC, by rw [hdAB, hdAC], hDBC, hBAD_DAC, hECA,
    hABE, hKinc, hBEK, hcosCAB⟩


/-- The `∠CAB = π/3` example, with `g = √3`, `w = 1`. -/
lemma suff_inst_pi3 : ∃ (A B C D E K : EuclideanSpace ℝ (Fin 2))
    (_hABC : AffineIndependent ℝ ![A, B, C]) (hADC : AffineIndependent ℝ ![A, D, C]),
    dist A B = dist A C ∧ Sbtw ℝ B D C ∧ ∠ B A D = ∠ D A C ∧
    Sbtw ℝ C E A ∧ ∠ A B E = ∠ E B C ∧
    K = (⟨![A, D, C], hADC⟩ : Affine.Triangle ℝ _).incenter ∧
    ∠ B E K = Real.pi / 4 ∧ ∠ C A B = Real.pi / 3 := by
  have hUW : ⟪(!₂[0, Real.sqrt 3] : EuclideanSpace ℝ (Fin 2)), !₂[1, 0]⟫ = 0 := by
    rw [PiLp.inner_apply, Fin.sum_univ_two]
    simp [RCLike.inner_apply]
  have hgU : ‖(!₂[0, Real.sqrt 3] : EuclideanSpace ℝ (Fin 2))‖ = Real.sqrt 3 := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    simp [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 3),
      Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)]
  have hwW : ‖(!₂[1, 0] : EuclideanSpace ℝ (Fin 2))‖ = 1 := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    simp [Real.sqrt_one]
  have hsqrt : Real.sqrt (Real.sqrt 3 ^ 2 + 1 ^ 2) = 2 := by
    rw [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num),
      show ((3:ℝ) + 1 ^ 2 = 2 ^ 2) from by norm_num, Real.sqrt_sq (by norm_num)]
  have ht : (2 - Real.sqrt 3) = 1 / (Real.sqrt 3 + Real.sqrt (Real.sqrt 3 ^ 2 + 1 ^ 2)) := by
    rw [hsqrt]
    field_simp [show (Real.sqrt 3 + 2) ≠ 0 by positivity]
    have h4 : (2 - Real.sqrt 3) * (Real.sqrt 3 + 2) = 4 - (Real.sqrt 3) ^ 2 := by ring
    rw [h4, Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)]
    norm_num
  have hPQ : ((2 - Real.sqrt 3) ^ 2 - 4 * (2 - Real.sqrt 3) + 1) *
      ((2 - Real.sqrt 3) ^ 2 + 2 * (2 - Real.sqrt 3) - 1) = 0 := by
    have h1 : (2 - Real.sqrt 3) ^ 2 - 4 * (2 - Real.sqrt 3) + 1 = 0 := by
      have h4 : (2 - Real.sqrt 3) ^ 2 = 4 - 4 * Real.sqrt 3 + (Real.sqrt 3) ^ 2 := by ring
      rw [h4, Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)]
      ring
    rw [h1, zero_mul]
  obtain ⟨A, B, C, D, E, K, hABC, hADC, h1, h2, h3, h4, h5, hK, h6, hcos⟩ :=
    suff_config hUW hgU hwW (by positivity : (0:ℝ) < Real.sqrt 3) (by norm_num) ht hPQ
  have hangle : ∠ C A B = Real.pi / 3 := by
    have hcos1 : Real.cos (∠ C A B) = 1 / 2 := by
      rw [hcos, Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)]
      norm_num
    have hmem : ∠ C A B ∈ Set.Icc 0 Real.pi := by
      rw [EuclideanGeometry.angle]
      exact ⟨InnerProductGeometry.angle_nonneg _ _, InnerProductGeometry.angle_le_pi _ _⟩
    have hpi3 : Real.pi / 3 ∈ Set.Icc 0 Real.pi :=
      ⟨by positivity, by linarith only [Real.pi_nonneg]⟩
    exact Real.injOn_cos hmem hpi3 (by rw [hcos1, Real.cos_pi_div_three])
  exact ⟨A, B, C, D, E, K, hABC, hADC, h1, h2, h3, h4, h5, hK, h6, hangle⟩

/-- The `∠CAB = π/2` example, with `g = 1`, `w = 1`. -/
lemma suff_inst_pi2 : ∃ (A B C D E K : EuclideanSpace ℝ (Fin 2))
    (_hABC : AffineIndependent ℝ ![A, B, C]) (hADC : AffineIndependent ℝ ![A, D, C]),
    dist A B = dist A C ∧ Sbtw ℝ B D C ∧ ∠ B A D = ∠ D A C ∧
    Sbtw ℝ C E A ∧ ∠ A B E = ∠ E B C ∧
    K = (⟨![A, D, C], hADC⟩ : Affine.Triangle ℝ _).incenter ∧
    ∠ B E K = Real.pi / 4 ∧ ∠ C A B = Real.pi / 2 := by
  have hUW : ⟪(!₂[0, 1] : EuclideanSpace ℝ (Fin 2)), !₂[1, 0]⟫ = 0 := by
    rw [PiLp.inner_apply, Fin.sum_univ_two]
    simp [RCLike.inner_apply]
  have hgU : ‖(!₂[0, 1] : EuclideanSpace ℝ (Fin 2))‖ = 1 := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    simp [Real.sqrt_one]
  have hwW : ‖(!₂[1, 0] : EuclideanSpace ℝ (Fin 2))‖ = 1 := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    simp [Real.sqrt_one]
  have hsqrt : Real.sqrt ((1:ℝ) ^ 2 + (1:ℝ) ^ 2) = Real.sqrt 2 := by norm_num
  have ht : (Real.sqrt 2 - 1) = 1 / (1 + Real.sqrt ((1:ℝ) ^ 2 + (1:ℝ) ^ 2)) := by
    rw [hsqrt]
    field_simp [show (1 + Real.sqrt 2) ≠ 0 by positivity]
    have h4 : (Real.sqrt 2 - 1) * (1 + Real.sqrt 2) = (Real.sqrt 2) ^ 2 - 1 := by ring
    rw [h4, Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]
    norm_num
  have hPQ : ((Real.sqrt 2 - 1) ^ 2 - 4 * (Real.sqrt 2 - 1) + 1) *
      ((Real.sqrt 2 - 1) ^ 2 + 2 * (Real.sqrt 2 - 1) - 1) = 0 := by
    have h1 : (Real.sqrt 2 - 1) ^ 2 + 2 * (Real.sqrt 2 - 1) - 1 = 0 := by
      have h4 : (Real.sqrt 2 - 1) ^ 2 = 1 - 2 * Real.sqrt 2 + (Real.sqrt 2) ^ 2 := by ring
      rw [h4, Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]
      ring
    rw [h1, mul_zero]
  obtain ⟨A, B, C, D, E, K, hABC, hADC, h1, h2, h3, h4, h5, hK, h6, hcos⟩ :=
    suff_config hUW hgU hwW (by norm_num) (by norm_num) ht hPQ
  have hangle : ∠ C A B = Real.pi / 2 := by
    have hcos1 : Real.cos (∠ C A B) = 0 := by
      rw [hcos]
      norm_num
    have hmem : ∠ C A B ∈ Set.Icc 0 Real.pi := by
      rw [EuclideanGeometry.angle]
      exact ⟨InnerProductGeometry.angle_nonneg _ _, InnerProductGeometry.angle_le_pi _ _⟩
    have hpi2 : Real.pi / 2 ∈ Set.Icc 0 Real.pi :=
      ⟨by positivity, by linarith only [Real.pi_nonneg]⟩
    exact Real.injOn_cos hmem hpi2 (by rw [hcos1, Real.cos_pi_div_two])
  exact ⟨A, B, C, D, E, K, hABC, hADC, h1, h2, h3, h4, h5, hK, h6, hangle⟩

snip end

determine solution_set : Set ℝ := {Real.pi / 3, Real.pi / 2}

problem imo2009_p4 :
    {α : ℝ | ∃ (A B C D E K : EuclideanSpace ℝ (Fin 2))
        (_hABC : AffineIndependent ℝ ![A, B, C]) (hADC : AffineIndependent ℝ ![A, D, C]),
        dist A B = dist A C ∧
        Sbtw ℝ B D C ∧ ∠ B A D = ∠ D A C ∧
        Sbtw ℝ C E A ∧ ∠ A B E = ∠ E B C ∧
        K = (⟨![A, D, C], hADC⟩ : Affine.Triangle ℝ _).incenter ∧
        ∠ B E K = Real.pi / 4 ∧ α = ∠ C A B} = solution_set := by
  ext α
  constructor
  · rintro ⟨A, B, C, D, E, K, hABC, hADC, hAB, hD, hAD, hE, hBE, hK, hBEK, rfl⟩
    exact necessity hABC hADC hAB hD hAD hE hBE hK hBEK
  · intro hα
    rcases hα with (rfl | rfl)
    · obtain ⟨A, B, C, D, E, K, hABC, hADC, hAB, hD, hAD, hE, hBE, hK, hBEK, hangle⟩ :=
        suff_inst_pi3
      exact ⟨A, B, C, D, E, K, hABC, hADC, hAB, hD, hAD, hE, hBE, hK, hBEK, hangle.symm⟩
    · obtain ⟨A, B, C, D, E, K, hABC, hADC, hAB, hD, hAD, hE, hBE, hK, hBEK, hangle⟩ :=
        suff_inst_pi2
      exact ⟨A, B, C, D, E, K, hABC, hADC, hAB, hD, hAD, hE, hBE, hK, hBEK, hangle.symm⟩

end Imo2009P4
