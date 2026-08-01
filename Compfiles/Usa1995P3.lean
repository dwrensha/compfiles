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
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import ProblemExtraction

@[expose] public section

problem_file {
  tags := [.Geometry]
}

/-!
# USA Mathematical Olympiad 1995, Problem 3

The circumcenter O of the triangle ABC does not lie on any side or median.
Let the midpoints of BC, CA, AB be L, M, N respectively. Take P, Q, R on the
rays OL, OM, ON respectively so that ∠OPA = ∠OAL, ∠OQB = ∠OBM and
∠ORC = ∠OCN. Show that AP, BQ and CR meet at a point.
-/

open scoped EuclideanGeometry RealInnerProductSpace InnerProductSpace

namespace Usa1995P3

/-- The plane, as both the vector space and the point space we work in. -/
abbrev E2 := EuclideanSpace ℝ (Fin 2)

snip begin

/-- Inner product on `EuclideanSpace ℝ (Fin 2)` in coordinates. -/
lemma inner_coord (x y : E2) : ⟪x, y⟫_ℝ = x 0 * y 0 + x 1 * y 1 := by
  rw [PiLp.inner_apply, Fin.sum_univ_two]
  simp [RCLike.inner_apply, mul_comm]

/-- Squared norm on `EuclideanSpace ℝ (Fin 2)` in coordinates. -/
lemma norm_sq_coord (x : E2) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  simp [Real.norm_eq_abs, sq_abs]

/-- **Step 1.** The angle condition `∠OPA = ∠OAL` for `P = t • L` (`t > 0`) on the
ray `OL`, where `L = (B + C)/2` is the midpoint of `BC`, forces `OP · OL = r²`;
explicitly `P = (r² / (r² + ⟪B, C⟫)) • (B + C)`, the intersection of the tangents
to the circumcircle at `B` and `C`. -/
lemma inversion_of_angle {r : ℝ} (hr : 0 < r) {A B C : E2}
    (hA : ‖A‖ = r) (hB : ‖B‖ = r) (hC : ‖C‖ = r) (hAB : A ≠ B)
    (hL0 : (2 : ℝ)⁻¹ • (B + C) ≠ 0)
    (hdep : ∀ s : ℝ, (2 : ℝ)⁻¹ • (B + C) ≠ s • A)
    {P : E2} {t : ℝ} (ht : 0 < t)
    (hP : P = t • (2 : ℝ)⁻¹ • (B + C))
    (hang : ∠ (0 : E2) P A = ∠ (0 : E2) A ((2 : ℝ)⁻¹ • (B + C))) :
    P = (r ^ 2 / (r ^ 2 + ⟪B, C⟫_ℝ)) • (B + C) := by
  set L : E2 := (2 : ℝ)⁻¹ • (B + C) with hLdef
  have hA0 : A ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hA
    linarith
  have hs : 0 < ‖L‖ ^ 2 := pow_pos (norm_pos_iff.mpr hL0) 2
  set s : ℝ := ‖L‖ ^ 2 with hsdef
  have hLs : Real.sqrt s = ‖L‖ := Real.sqrt_sq (norm_nonneg L)
  set m : ℝ := ⟪A, L⟫_ℝ with hmdef
  have hmL : ⟪L, A⟫_ℝ = m := by
    rw [real_inner_comm A L, hmdef]
  have hLA : L ≠ A := by
    intro h
    exact hdep 1 (by rw [h, one_smul])
  have hAP : A ≠ P := by
    intro h
    have h2 : L = t⁻¹ • A := by
      have h3 : t⁻¹ • A = t⁻¹ • (t • L) := by rw [h, hP]
      rw [smul_smul, inv_mul_cancel₀ ht.ne', one_smul] at h3
      rw [h3]
    exact hdep t⁻¹ h2
  have hnP : ‖P‖ = t * Real.sqrt s := by
    rw [hP, norm_smul, Real.norm_eq_abs, abs_of_pos ht, hLs]
  have hnAP : ‖A - P‖ ^ 2 = r ^ 2 - 2 * t * m + t ^ 2 * s := by
    rw [norm_sub_sq_real, hA, hP, real_inner_smul_right, ← hmdef]
    have e1 : ‖t • L‖ ^ 2 = t ^ 2 * s := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht, mul_pow, ← hsdef]
    rw [e1]
    ring
  have hnLA : ‖L - A‖ ^ 2 = s - 2 * m + r ^ 2 := by
    rw [norm_sub_sq_real, hA, ← hsdef, hmL]
  have hm_lt : m < r ^ 2 := by
    have e : m = (⟪A, B⟫_ℝ + ⟪A, C⟫_ℝ) / 2 := by
      rw [hmdef, hLdef, real_inner_smul_right, inner_add_right]
      ring
    have hABi : ⟪A, B⟫_ℝ < r ^ 2 := by
      have h1 : (0 : ℝ) < ‖A - B‖ ^ 2 := pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hAB)) 2
      rw [norm_sub_sq_real, hA, hB] at h1
      linarith
    have hACi : ⟪A, C⟫_ℝ ≤ r ^ 2 := by
      have h1 : (0 : ℝ) ≤ ‖A - C‖ ^ 2 := sq_nonneg _
      rw [norm_sub_sq_real, hA, hC] at h1
      linarith
    linarith [e, hABi, hACi]
  have hden2 : (0 : ℝ) < r * ‖L - A‖ := mul_pos hr (norm_pos_iff.mpr (sub_ne_zero.mpr hLA))
  -- Take cosine of both sides of the angle equality.
  have hcos := congrArg Real.cos hang
  unfold EuclideanGeometry.angle at hcos
  rw [InnerProductGeometry.cos_angle, InnerProductGeometry.cos_angle] at hcos
  rw [vsub_eq_sub, vsub_eq_sub, vsub_eq_sub, vsub_eq_sub, zero_sub, zero_sub] at hcos
  have hi1 : ⟪-P, A - P⟫_ℝ = t * (t * s - m) := by
    rw [hP]
    simp only [inner_neg_left, inner_sub_right, real_inner_smul_left,
      real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs, abs_of_pos ht, mul_pow, ← hsdef]
    rw [hmL]
    ring
  have hi2 : ⟪-A, L - A⟫_ℝ = r ^ 2 - m := by
    simp only [inner_neg_left, inner_sub_right, real_inner_self_eq_norm_sq, hA]
    rw [← hmdef]
    ring
  rw [hi1, hi2, norm_neg, norm_neg, hnP, hA] at hcos
  -- Cross-multiply and cancel `t`.
  have hd1 : t * Real.sqrt s * ‖A - P‖ ≠ 0 :=
    mul_ne_zero (mul_ne_zero ht.ne' (Real.sqrt_pos.mpr hs).ne')
      (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hAP))
  have hd2 : r * ‖L - A‖ ≠ 0 := mul_ne_zero hr.ne' (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hLA))
  rw [div_eq_div_iff hd1 hd2] at hcos
  have hE : (t * s - m) * (r * ‖L - A‖) = (r ^ 2 - m) * (Real.sqrt s * ‖A - P‖) := by
    apply mul_left_cancel₀ ht.ne'
    linear_combination hcos
  -- The unsquared equation forces a sign.
  have hsign : 0 < t * s - m := by
    have pos1 : (0 : ℝ) < Real.sqrt s * ‖A - P‖ :=
      mul_pos (Real.sqrt_pos.mpr hs) (norm_pos_iff.mpr (sub_ne_zero.mpr hAP))
    have pos2 : (0 : ℝ) < (r ^ 2 - m) * (Real.sqrt s * ‖A - P‖) := mul_pos (by linarith) pos1
    rw [← hE] at pos2
    rcases mul_pos_iff.mp pos2 with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact h1
    · linarith
  -- Square the equation and factor.
  have hsq : (t * s - m) ^ 2 * r ^ 2 * (s - 2 * m + r ^ 2) =
      (r ^ 2 - m) ^ 2 * s * (r ^ 2 - 2 * t * m + t ^ 2 * s) := by
    have h2 := congrArg (· ^ 2) hE
    simp only [mul_pow, hnLA, hnAP, Real.sq_sqrt hs.le] at h2
    linear_combination h2
  have hfact : (r ^ 2 * s - m ^ 2) * ((s * t - r ^ 2) * (s * t + r ^ 2 - 2 * m)) = 0 := by
    linear_combination hsq
  rcases mul_eq_zero.mp hfact with h1 | h2
  · -- `r² * s = m²`: Cauchy–Schwarz equality, so `A ∥ L` — excluded.
    exfalso
    have hm0 : m ≠ 0 := by
      intro h0
      rw [h0] at h1
      have hz : r ^ 2 * s = 0 := by linear_combination h1
      exact (mul_ne_zero (pow_ne_zero 2 hr.ne') hs.ne') hz
    have hz : ‖s • A - m • L‖ ^ 2 = 0 := by
      have e : ‖s • A - m • L‖ ^ 2 = ⟪s • A - m • L, s • A - m • L⟫_ℝ :=
        (real_inner_self_eq_norm_sq _).symm
      rw [e]
      simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
        real_inner_self_eq_norm_sq, hA, norm_smul, Real.norm_eq_abs, abs_of_pos hs, mul_pow,
        sq_abs, ← hsdef]
      rw [hmL, ← hmdef]
      linear_combination s * h1
    have hAL : s • A = m • L := by
      have h1' : ‖s • A - m • L‖ = 0 := (pow_eq_zero_iff two_ne_zero).mp hz
      rwa [norm_eq_zero, sub_eq_zero] at h1'
    have hLr : L = (m⁻¹ * s) • A := by
      have h3 := congrArg (m⁻¹ • ·) hAL
      rw [smul_smul, smul_smul, inv_mul_cancel₀ hm0, one_smul] at h3
      exact h3.symm
    exact hdep _ hLr
  · rcases mul_eq_zero.mp h2 with hst | hst
    · -- `s * t = r²`: the good root.
      have hst' : s * t = r ^ 2 := by linear_combination hst
      have ht_eq : t = r ^ 2 / s := (eq_div_iff hs.ne').mpr (by rw [mul_comm]; exact hst')
      have hsBC : s = (r ^ 2 + ⟪B, C⟫_ℝ) / 2 := by
        rw [hsdef, hLdef, norm_smul, Real.norm_eq_abs,
          abs_of_pos (show (0 : ℝ) < (2 : ℝ)⁻¹ by norm_num), mul_pow, norm_add_sq_real, hB, hC]
        field_simp
        ring
      have hu : r ^ 2 + ⟪B, C⟫_ℝ ≠ 0 := by
        have hBC0 : B + C ≠ 0 := by
          intro h0
          apply hL0
          rw [hLdef, h0, smul_zero]
        have h1 : (0 : ℝ) < ‖B + C‖ ^ 2 := pow_pos (norm_pos_iff.mpr hBC0) 2
        rw [norm_add_sq_real, hB, hC] at h1
        have h2 : (0 : ℝ) < r ^ 2 + ⟪B, C⟫_ℝ := by linarith
        exact h2.ne'
      rw [hP, ht_eq, hLdef, smul_smul, hsBC]
      congr 1
      field_simp [hu]
    · -- The extraneous root contradicts the sign.
      have htsm : t * s - m = m - r ^ 2 := by linear_combination hst
      linarith

/-- The symmedian (Lemoine) point of the triangle `ABC` with circumcenter at the
origin, in vector form: barycentric weights proportional to the squared side
lengths `|B−C|² : |C−A|² : |A−B|² = (r²−⟪B,C⟫) : (r²−⟪C,A⟫) : (r²−⟪A,B⟫)`. -/
noncomputable def symmedianPoint (r : ℝ) (A B C : E2) : E2 :=
  ((r ^ 2 - ⟪B, C⟫_ℝ) + (r ^ 2 - ⟪C, A⟫_ℝ) + (r ^ 2 - ⟪A, B⟫_ℝ))⁻¹ •
    ((r ^ 2 - ⟪B, C⟫_ℝ) • A + (r ^ 2 - ⟪C, A⟫_ℝ) • B + (r ^ 2 - ⟪A, B⟫_ℝ) • C)

/-- The symmedian point is cyclically symmetric. -/
lemma symmedianPoint_perm (r : ℝ) (A B C : E2) :
    symmedianPoint r B C A = symmedianPoint r A B C := by
  show (((r ^ 2 - ⟪C, A⟫_ℝ) + (r ^ 2 - ⟪A, B⟫_ℝ) + (r ^ 2 - ⟪B, C⟫_ℝ))⁻¹ •
      ((r ^ 2 - ⟪C, A⟫_ℝ) • B + (r ^ 2 - ⟪A, B⟫_ℝ) • C + (r ^ 2 - ⟪B, C⟫_ℝ) • A)) =
    ((r ^ 2 - ⟪B, C⟫_ℝ) + (r ^ 2 - ⟪C, A⟫_ℝ) + (r ^ 2 - ⟪A, B⟫_ℝ))⁻¹ •
      ((r ^ 2 - ⟪B, C⟫_ℝ) • A + (r ^ 2 - ⟪C, A⟫_ℝ) • B + (r ^ 2 - ⟪A, B⟫_ℝ) • C)
  congr 1
  · congr 1
    ring
  · ac_rfl

/-- The polynomial identity behind **Step 2**, proved coordinate-wise. It reduces
to Lagrange's identity `(B₀²+B₁²)(C₀²+C₁²) = ⟪B,C⟫² + (B₀C₁−B₁C₀)²` and the
two-dimensional relation `(B₀C₁−B₁C₀)•A + (C₀A₁−C₁A₀)•B + (A₀B₁−A₁B₀)•C = 0`. -/
lemma key_identity (r : ℝ) (A B C : E2)
    (hB2 : B 0 ^ 2 + B 1 ^ 2 = r ^ 2) (hC2 : C 0 ^ 2 + C 1 ^ 2 = r ^ 2) :
    (r ^ 2 + ⟪B, C⟫_ℝ) •
        ((r ^ 2 - ⟪B, C⟫_ℝ) • A + (r ^ 2 - ⟪C, A⟫_ℝ) • B + (r ^ 2 - ⟪A, B⟫_ℝ) • C) =
      ((r ^ 2 + ⟪B, C⟫_ℝ) * (2 * (r ^ 2 - ⟪B, C⟫_ℝ))) • A +
        ((r ^ 2 + ⟪B, C⟫_ℝ - ⟪C, A⟫_ℝ - ⟪A, B⟫_ℝ) * r ^ 2) • (B + C) := by
  simp only [inner_coord]
  ext i
  revert i
  rw [Fin.forall_fin_two]
  constructor
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    linear_combination ((C 0 ^ 2 + C 1 ^ 2) * A 0 - (C 0 * A 0 + C 1 * A 1) * C 0) * hB2 +
      (r ^ 2 * A 0 - (A 0 * B 0 + A 1 * B 1) * B 0) * hC2
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    linear_combination ((C 0 ^ 2 + C 1 ^ 2) * A 1 - (C 0 * A 0 + C 1 * A 1) * C 1) * hB2 +
      (r ^ 2 * A 1 - (A 0 * B 0 + A 1 * B 1) * B 1) * hC2

/-- **Step 2.** The symmedian point lies on the line `AP` (the `A`-symmedian). -/
lemma symmedian_mem {r : ℝ} (hr : 0 < r) {A B C : E2}
    (hA : ‖A‖ = r) (hB : ‖B‖ = r) (hC : ‖C‖ = r)
    (hAB : A ≠ B) (hBC : B ≠ C) (hCA : C ≠ A) (hBCneg : B ≠ -C)
    {P : E2} (hP : P = (r ^ 2 / (r ^ 2 + ⟪B, C⟫_ℝ)) • (B + C)) :
    symmedianPoint r A B C ∈ line[ℝ, A, P] := by
  have hB2 : B 0 ^ 2 + B 1 ^ 2 = r ^ 2 := by
    have h := norm_sq_coord B
    rw [hB] at h
    exact h.symm
  have hC2 : C 0 ^ 2 + C 1 ^ 2 = r ^ 2 := by
    have h := norm_sq_coord C
    rw [hC] at h
    exact h.symm
  have hbc_pos : (0 : ℝ) < r ^ 2 + ⟪B, C⟫_ℝ := by
    have hBC0 : B + C ≠ 0 := by
      intro h0
      exact hBCneg (add_eq_zero_iff_eq_neg.mp h0)
    have h1 : (0 : ℝ) < ‖B + C‖ ^ 2 := pow_pos (norm_pos_iff.mpr hBC0) 2
    rw [norm_add_sq_real, hB, hC] at h1
    linarith
  have hu : r ^ 2 + ⟪B, C⟫_ℝ ≠ 0 := hbc_pos.ne'
  have hbc_lt : ⟪B, C⟫_ℝ < r ^ 2 := by
    have h1 : (0 : ℝ) < ‖B - C‖ ^ 2 := pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hBC)) 2
    rw [norm_sub_sq_real, hB, hC] at h1
    linarith
  have hca_lt : ⟪C, A⟫_ℝ < r ^ 2 := by
    have h1 : (0 : ℝ) < ‖C - A‖ ^ 2 := pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hCA)) 2
    rw [norm_sub_sq_real, hC, hA] at h1
    linarith
  have hab_lt : ⟪A, B⟫_ℝ < r ^ 2 := by
    have h1 : (0 : ℝ) < ‖A - B‖ ^ 2 := pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hAB)) 2
    rw [norm_sub_sq_real, hA, hB] at h1
    linarith
  have hσ : (r ^ 2 - ⟪B, C⟫_ℝ) + (r ^ 2 - ⟪C, A⟫_ℝ) + (r ^ 2 - ⟪A, B⟫_ℝ) ≠ 0 := by
    have hpos : (0 : ℝ) < (r ^ 2 - ⟪B, C⟫_ℝ) + (r ^ 2 - ⟪C, A⟫_ℝ) + (r ^ 2 - ⟪A, B⟫_ℝ) := by
      linarith
    exact hpos.ne'
  have hP2 : (r ^ 2 + ⟪B, C⟫_ℝ) • P = r ^ 2 • (B + C) := by
    rw [hP, smul_smul]
    congr 1
    field_simp [hu]
  have key := key_identity r A B C hB2 hC2
  have hS : (r ^ 2 - ⟪B, C⟫_ℝ) • A + (r ^ 2 - ⟪C, A⟫_ℝ) • B + (r ^ 2 - ⟪A, B⟫_ℝ) • C =
      (2 * (r ^ 2 - ⟪B, C⟫_ℝ)) • A + (r ^ 2 + ⟪B, C⟫_ℝ - ⟪C, A⟫_ℝ - ⟪A, B⟫_ℝ) • P := by
    have e : (r ^ 2 + ⟪B, C⟫_ℝ) •
          ((r ^ 2 - ⟪B, C⟫_ℝ) • A + (r ^ 2 - ⟪C, A⟫_ℝ) • B + (r ^ 2 - ⟪A, B⟫_ℝ) • C) =
        (r ^ 2 + ⟪B, C⟫_ℝ) • ((2 * (r ^ 2 - ⟪B, C⟫_ℝ)) • A +
          (r ^ 2 + ⟪B, C⟫_ℝ - ⟪C, A⟫_ℝ - ⟪A, B⟫_ℝ) • P) := by
      conv_rhs => rw [smul_add, smul_smul, smul_comm (r ^ 2 + ⟪B, C⟫_ℝ)
        (r ^ 2 + ⟪B, C⟫_ℝ - ⟪C, A⟫_ℝ - ⟪A, B⟫_ℝ) P, hP2, smul_smul]
      exact key
    have h := congrArg ((r ^ 2 + ⟪B, C⟫_ℝ)⁻¹ • ·) e
    simp only [smul_smul] at h
    rw [inv_mul_cancel₀ hu, one_smul, one_smul] at h
    exact h
  have hK : symmedianPoint r A B C = AffineMap.lineMap A P
      ((r ^ 2 + ⟪B, C⟫_ℝ - ⟪C, A⟫_ℝ - ⟪A, B⟫_ℝ) /
        ((r ^ 2 - ⟪B, C⟫_ℝ) + (r ^ 2 - ⟪C, A⟫_ℝ) + (r ^ 2 - ⟪A, B⟫_ℝ))) := by
    rw [AffineMap.lineMap_apply_module]
    unfold symmedianPoint
    rw [hS, smul_add, smul_smul, smul_smul]
    congr 1
    · congr 1
      field_simp [hσ]
      ring
    · congr 1
      field_simp [hσ]
  rw [hK]
  exact AffineMap.lineMap_mem_affineSpan_pair _ _ _

/-- If the midpoint of `BC` is not the circumcenter, then `B ≠ -C` conversely. -/
lemma midpoint_ne_zero_of_ne_neg {B C : E2} (h : B ≠ -C) :
    (2 : ℝ)⁻¹ • (B + C) ≠ 0 := by
  intro h0
  rw [smul_eq_zero] at h0
  rcases h0 with h0 | h0
  · norm_num at h0
  · exact h (add_eq_zero_iff_eq_neg.mp h0)

/-- If `O` does not lie on the line `XY` (and `X ≠ Y` is irrelevant), then `X ≠ -Y`. -/
lemma ne_neg_of_not_mem_line {X Y : E2} (h : (0 : E2) ∉ line[ℝ, X, Y]) : X ≠ -Y := by
  intro hXY
  apply h
  have h0 : AffineMap.lineMap X Y (1 / 2 : ℝ) = 0 := by
    rw [AffineMap.lineMap_apply_module, hXY,
      show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, smul_neg, neg_add_cancel]
  rw [← h0]
  exact AffineMap.lineMap_mem_affineSpan_pair _ _ _

/-- If `O` does not lie on the median from `A`, then the midpoint of `BC` is not
collinear with `O` and `A`. -/
lemma not_smul_midpoint_of_not_mem_median {r : ℝ} (hr : 0 < r) {A B C : E2}
    (hA : ‖A‖ = r) (hB : ‖B‖ = r) (hC : ‖C‖ = r) (hAB : A ≠ B)
    (hmed : (0 : E2) ∉ line[ℝ, A, midpoint ℝ B C]) :
    ∀ s : ℝ, (2 : ℝ)⁻¹ • (B + C) ≠ s • A := by
  intro s hs
  have hmp : midpoint ℝ B C = (2 : ℝ)⁻¹ • (B + C) := by
    rw [midpoint_eq_smul_add, invOf_eq_inv]
  have hA0 : A ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hA
    linarith
  by_cases hs1 : s = 1
  · -- The midpoint equals `A`; but then equal norms force `A = B`.
    rw [hs1, one_smul] at hs
    have hsum : B + C = (2 : ℝ) • A := by
      have h2 := congrArg ((2 : ℝ) • ·) hs
      rwa [smul_smul, show (2 : ℝ) * (2 : ℝ)⁻¹ = 1 by norm_num, one_smul] at h2
    have hCeq : C = (2 : ℝ) • A - B := by rw [← hsum]; abel
    have hCs : ‖C‖ ^ 2 = ‖(2 : ℝ) • A - B‖ ^ 2 := by rw [hCeq]
    rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
      abs_of_pos (show (0 : ℝ) < 2 by norm_num), hA, hB, hC, real_inner_smul_left] at hCs
    have hinner : ⟪A, B⟫_ℝ = r ^ 2 := by linarith
    have hABsq : ‖A - B‖ ^ 2 = 0 := by
      rw [norm_sub_sq_real, hA, hB, hinner]
      ring
    have hAB0 : A = B := by
      have h1 : ‖A - B‖ = 0 := (pow_eq_zero_iff two_ne_zero).mp hABsq
      exact sub_eq_zero.mp (norm_eq_zero.mp h1)
    exact hAB hAB0
  · -- `s ≠ 1`: then `O` lies on the median line, contradiction.
    apply hmed
    have hs10 : (1 : ℝ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
    have h0 : AffineMap.lineMap A (midpoint ℝ B C) ((1 - s)⁻¹ : ℝ) = 0 := by
      rw [AffineMap.lineMap_apply_module, hmp, hs, smul_smul, ← add_smul]
      have he : (1 - (1 - s)⁻¹) + (1 - s)⁻¹ * s = 0 := by field_simp [hs10]; ring
      rw [he, zero_smul]
    rw [← h0]
    exact AffineMap.lineMap_mem_affineSpan_pair _ _ _

snip end

/-- **USA Mathematical Olympiad 1995, Problem 3.**

The circumcenter `O` of the triangle `ABC` does not lie on any side or median.
Let the midpoints of `BC`, `CA`, `AB` be `L`, `M`, `N` respectively. Take
`P, Q, R` on the rays `OL`, `OM`, `ON` respectively so that
`∠OPA = ∠OAL`, `∠OQB = ∠OBM` and `∠ORC = ∠OCN`. Then `AP`, `BQ` and `CR`
meet at a point.

We place `O` at the origin; `r` is the circumradius. The hypothesis that `P`
lies on the ray `OL` is encoded as `P = tP • midpoint ℝ B C` with `0 < tP`
(`P = O` would make `∠OPA` meaningless). -/
problem usa1995_p3
    (r : ℝ) (hr : 0 < r)
    (A B C : E2) (hA : ‖A‖ = r) (hB : ‖B‖ = r) (hC : ‖C‖ = r)
    (hAB : A ≠ B) (hBC : B ≠ C) (hCA : C ≠ A)
    (hsideA : (0 : E2) ∉ line[ℝ, B, C])
    (hsideB : (0 : E2) ∉ line[ℝ, C, A])
    (hsideC : (0 : E2) ∉ line[ℝ, A, B])
    (hmedA : (0 : E2) ∉ line[ℝ, A, midpoint ℝ B C])
    (hmedB : (0 : E2) ∉ line[ℝ, B, midpoint ℝ C A])
    (hmedC : (0 : E2) ∉ line[ℝ, C, midpoint ℝ A B])
    (P Q R : E2)
    (tP : ℝ) (htP : 0 < tP) (hPr : P = tP • midpoint ℝ B C)
    (tQ : ℝ) (htQ : 0 < tQ) (hQr : Q = tQ • midpoint ℝ C A)
    (tR : ℝ) (htR : 0 < tR) (hRr : R = tR • midpoint ℝ A B)
    (hPa : ∠ (0 : E2) P A = ∠ (0 : E2) A (midpoint ℝ B C))
    (hQa : ∠ (0 : E2) Q B = ∠ (0 : E2) B (midpoint ℝ C A))
    (hRa : ∠ (0 : E2) R C = ∠ (0 : E2) C (midpoint ℝ A B)) :
    ∃ K : E2, K ∈ line[ℝ, A, P] ∧ K ∈ line[ℝ, B, Q] ∧ K ∈ line[ℝ, C, R] := by
  have hmpBC : midpoint ℝ B C = (2 : ℝ)⁻¹ • (B + C) := by
    rw [midpoint_eq_smul_add, invOf_eq_inv]
  have hmpCA : midpoint ℝ C A = (2 : ℝ)⁻¹ • (C + A) := by
    rw [midpoint_eq_smul_add, invOf_eq_inv]
  have hmpAB : midpoint ℝ A B = (2 : ℝ)⁻¹ • (A + B) := by
    rw [midpoint_eq_smul_add, invOf_eq_inv]
  have hBCneg : B ≠ -C := ne_neg_of_not_mem_line hsideA
  have hCAneg : C ≠ -A := ne_neg_of_not_mem_line hsideB
  have hABneg : A ≠ -B := ne_neg_of_not_mem_line hsideC
  have hL0A : (2 : ℝ)⁻¹ • (B + C) ≠ 0 := midpoint_ne_zero_of_ne_neg hBCneg
  have hL0B : (2 : ℝ)⁻¹ • (C + A) ≠ 0 := midpoint_ne_zero_of_ne_neg hCAneg
  have hL0C : (2 : ℝ)⁻¹ • (A + B) ≠ 0 := midpoint_ne_zero_of_ne_neg hABneg
  have hdepA : ∀ s : ℝ, (2 : ℝ)⁻¹ • (B + C) ≠ s • A :=
    not_smul_midpoint_of_not_mem_median hr hA hB hC hAB hmedA
  have hdepB : ∀ s : ℝ, (2 : ℝ)⁻¹ • (C + A) ≠ s • B :=
    not_smul_midpoint_of_not_mem_median hr hB hC hA hBC hmedB
  have hdepC : ∀ s : ℝ, (2 : ℝ)⁻¹ • (A + B) ≠ s • C :=
    not_smul_midpoint_of_not_mem_median hr hC hA hB hCA hmedC
  have hPr' : P = tP • (2 : ℝ)⁻¹ • (B + C) := by rw [hmpBC] at hPr; exact hPr
  have hQr' : Q = tQ • (2 : ℝ)⁻¹ • (C + A) := by rw [hmpCA] at hQr; exact hQr
  have hRr' : R = tR • (2 : ℝ)⁻¹ • (A + B) := by rw [hmpAB] at hRr; exact hRr
  have hPa' : ∠ (0 : E2) P A = ∠ (0 : E2) A ((2 : ℝ)⁻¹ • (B + C)) := by
    rw [hmpBC] at hPa; exact hPa
  have hQa' : ∠ (0 : E2) Q B = ∠ (0 : E2) B ((2 : ℝ)⁻¹ • (C + A)) := by
    rw [hmpCA] at hQa; exact hQa
  have hRa' : ∠ (0 : E2) R C = ∠ (0 : E2) C ((2 : ℝ)⁻¹ • (A + B)) := by
    rw [hmpAB] at hRa; exact hRa
  have hPf : P = (r ^ 2 / (r ^ 2 + ⟪B, C⟫_ℝ)) • (B + C) :=
    inversion_of_angle hr hA hB hC hAB hL0A hdepA htP hPr' hPa'
  have hQf : Q = (r ^ 2 / (r ^ 2 + ⟪C, A⟫_ℝ)) • (C + A) :=
    inversion_of_angle hr hB hC hA hBC hL0B hdepB htQ hQr' hQa'
  have hRf : R = (r ^ 2 / (r ^ 2 + ⟪A, B⟫_ℝ)) • (A + B) :=
    inversion_of_angle hr hC hA hB hCA hL0C hdepC htR hRr' hRa'
  refine ⟨symmedianPoint r A B C, ?_, ?_, ?_⟩
  · exact symmedian_mem hr hA hB hC hAB hBC hCA hBCneg hPf
  · rw [← symmedianPoint_perm r A B C]
    exact symmedian_mem hr hB hC hA hBC hCA hAB hCAneg hQf
  · rw [symmedianPoint_perm r C A B]
    exact symmedian_mem hr hC hA hB hCA hAB hBC hABneg hRf

end Usa1995P3
