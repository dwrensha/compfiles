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
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality
public import Mathlib.Tactic.Linarith.NNRealPreprocessor
public import Mathlib.Geometry.Euclidean.Triangle
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# USA Mathematical Olympiad 1981, Problem 4

A convex polygon has n sides. Each vertex is joined to a point P not in the
same plane. If A, B, C are adjacent vertices of the polygon take the angle
between the planes PBA and PBC. The sum of the n such angles equals the sum of
the n angles subtended at P by the sides of the polygon (such as the angle
APB). Show that n = 3.
-/

namespace Usa1981P4

open InnerProductGeometry
open Real
open scoped RealInnerProductSpace NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The component of `x` orthogonal to `v` (the projection of `x` onto `vᗮ`). -/
noncomputable def dproj (v x : E) : E := x - (⟪v, x⟫ / ⟪v, v⟫) • v

/-- The angle between the planes `PBA` and `PBC` along their common line `PB`
(for `P` not in the plane `ABC`): the angle between the components of `A - P`
and `C - P` orthogonal to `B - P`. -/
noncomputable def planeAngle (P B A C : E) : ℝ :=
  angle (dproj (B - P) (A - P)) (dproj (B - P) (C - P))

snip begin

lemma dproj_inner (u v w : E) :
    ⟪dproj u v, dproj u w⟫ = ⟪v, w⟫ - ⟪u, v⟫ * ⟪u, w⟫ / ⟪u, u⟫ := by
  simp only [dproj, inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right]
  rw [real_inner_comm v u]
  by_cases hu : ⟪u, u⟫ = 0 <;> field_simp <;> ring

lemma dproj_norm_sq (u v : E) : ‖dproj u v‖ ^ 2 = ‖v‖ ^ 2 - ⟪u, v⟫ ^ 2 / ⟪u, u⟫ := by
  rw [← real_inner_self_eq_norm_sq (dproj u v), dproj_inner, real_inner_self_eq_norm_sq,
    ← sq]

lemma dproj_eq_zero_iff (u v : E) (hu : u ≠ 0) :
    dproj u v = 0 ↔ ∃ r : ℝ, v = r • u := by
  constructor
  · intro h
    refine ⟨⟪u, v⟫ / ⟪u, u⟫, ?_⟩
    have h2 : v = dproj u v + (⟪u, v⟫ / ⟪u, u⟫) • u := by simp [dproj]
    rw [h] at h2
    simpa using h2
  · rintro ⟨r, rfl⟩
    have h3 : (⟪u, r • u⟫ / ⟪u, u⟫) = r := by
      rw [real_inner_smul_right]
      field_simp [inner_self_ne_zero.mpr hu]
    rw [dproj, h3, sub_self]

/-- Cosine of the dihedral angle along `u` between the planes spanned by `{u, v}`
and `{u, w}`, for unit vectors. -/
lemma cos_dihedral {u v w : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    Real.cos (angle (dproj u v) (dproj u w)) =
      (⟪v, w⟫ - ⟪u, v⟫ * ⟪u, w⟫) /
        (Real.sqrt (1 - ⟪u, v⟫ ^ 2) * Real.sqrt (1 - ⟪u, w⟫ ^ 2)) := by
  have huu : ⟪u, u⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  have hnv : ‖dproj u v‖ = Real.sqrt (1 - ⟪u, v⟫ ^ 2) := by
    conv_lhs => rw [← Real.sqrt_sq (norm_nonneg (dproj u v))]
    rw [dproj_norm_sq, hv, huu]; norm_num
  have hnw : ‖dproj u w‖ = Real.sqrt (1 - ⟪u, w⟫ ^ 2) := by
    conv_lhs => rw [← Real.sqrt_sq (norm_nonneg (dproj u w))]
    rw [dproj_norm_sq, hw, huu]; norm_num
  rw [cos_angle, dproj_inner, hnv, hnw, huu]; norm_num

/-- The Gram determinant of three unit vectors, which is strictly positive
iff the vectors are linearly independent. -/
noncomputable def gramDet (u v w : E) : ℝ :=
  1 - ⟪u, v⟫ ^ 2 - ⟪u, w⟫ ^ 2 - ⟪v, w⟫ ^ 2 + 2 * ⟪u, v⟫ * ⟪u, w⟫ * ⟪v, w⟫

/-- The Gram determinant of three unit vectors is nonnegative
(Cauchy–Schwarz in the plane `uᗮ`). -/
lemma gramDet_nonneg {u v w : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    0 ≤ gramDet u v w := by
  have huu : ⟪u, u⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  have hcs : ⟪dproj u v, dproj u w⟫ ^ 2 ≤ (‖dproj u v‖ * ‖dproj u w‖) ^ 2 :=
    sq_le_sq.mpr (by
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖dproj u v‖ * ‖dproj u w‖)]
      exact abs_real_inner_le_norm _ _)
  rw [mul_pow, dproj_inner, dproj_norm_sq, dproj_norm_sq, hv, hw, huu] at hcs
  simp only [gramDet]
  norm_num at hcs ⊢
  linarith

/-- Sine of the dihedral angle along `u`, for unit vectors with `v, w` not
parallel to `u`. -/
lemma sin_dihedral {u v w : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (huv : |⟪u, v⟫| < 1) (huw : |⟪u, w⟫| < 1) :
    Real.sin (angle (dproj u v) (dproj u w)) =
      Real.sqrt (gramDet u v w) /
        (Real.sqrt (1 - ⟪u, v⟫ ^ 2) * Real.sqrt (1 - ⟪u, w⟫ ^ 2)) := by
  have ha : (0 : ℝ) < 1 - ⟪u, v⟫ ^ 2 := by
    rw [sub_pos, sq_lt_one_iff_abs_lt_one]; exact huv
  have hb : (0 : ℝ) < 1 - ⟪u, w⟫ ^ 2 := by
    rw [sub_pos, sq_lt_one_iff_abs_lt_one]; exact huw
  have hsin2 : Real.sin (angle (dproj u v) (dproj u w)) ^ 2 =
      gramDet u v w / ((1 - ⟪u, v⟫ ^ 2) * (1 - ⟪u, w⟫ ^ 2)) := by
    rw [Real.sin_sq, cos_dihedral hu hv hw, div_pow, mul_pow,
      Real.sq_sqrt ha.le, Real.sq_sqrt hb.le]
    simp only [gramDet]
    field_simp [ne_of_gt ha, ne_of_gt hb]
    ring
  have hg : (0 : ℝ) ≤ gramDet u v w := gramDet_nonneg hu hv hw
  rw [← Real.sqrt_sq (sin_angle_nonneg _ _), hsin2, Real.sqrt_div hg,
    Real.sqrt_mul ha.le]

/-- For unit vectors, `|⟪u, v⟫| < 1` iff `u ≠ ±v`. -/
lemma abs_inner_lt_one_of_ne {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (h1 : v ≠ u) (h2 : v ≠ -u) : |⟪u, v⟫| < 1 := by
  have hle : |⟪u, v⟫| ≤ 1 := by
    have h := abs_real_inner_le_norm u v
    rwa [hu, hv, mul_one] at h
  refine lt_of_le_of_ne hle (fun habs ↦ ?_)
  rcases eq_or_eq_neg_of_abs_eq habs with h | h
  · exact h1 ((inner_eq_one_iff_of_norm_eq_one hu hv).mp h).symm
  · exact h2 (by rw [← neg_neg v, ← (inner_eq_neg_one_iff_of_norm_eq_one hu hv).mp h])

/-- The Gram determinant of three linearly independent unit vectors is
strictly positive. -/
lemma gramDet_pos {u v w : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (huv : |⟪u, v⟫| < 1) (hwspan : w ∉ Submodule.span ℝ {u, v}) :
    0 < gramDet u v w := by
  have huu : ⟪u, u⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  have hune : u ≠ 0 := by rw [← norm_ne_zero_iff, hu]; norm_num
  have hdne : dproj u v ≠ 0 := by
    rw [ne_eq, dproj_eq_zero_iff u v hune]
    rintro ⟨r, hr⟩
    have hrv : ‖v‖ = |r| := by rw [hr, norm_smul, hu, mul_one, Real.norm_eq_abs]
    rw [hv] at hrv
    have hrr : ⟪u, v⟫ = r := by rw [hr, real_inner_smul_right, huu]; ring
    rw [hrr, hrv] at huv
    exact absurd huv (by norm_num)
  set e := (‖dproj u v‖)⁻¹ • dproj u v with he
  have hudp : ⟪u, dproj u v⟫ = 0 := by
    rw [dproj, inner_sub_right, real_inner_smul_right, huu, div_one, mul_one, sub_self]
  have hue : ⟪u, e⟫ = 0 := by rw [he, real_inner_smul_right, hudp]; simp
  have he_norm : ‖e‖ = 1 := by
    rw [he, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hdne)]
  have hne : w - ⟪u, w⟫ • u - ⟪e, w⟫ • e ≠ 0 := by
    intro hz
    have hw2 : w = ⟪e, w⟫ • e + ⟪u, w⟫ • u := by
      have h1 : w - ⟪u, w⟫ • u = ⟪e, w⟫ • e := sub_eq_zero.mp hz
      rw [← h1]; abel
    have hdmem : dproj u v ∈ Submodule.span ℝ {u, v} := by
      have h2 : dproj u v = v - (⟪u, v⟫ / ⟪u, u⟫) • u := rfl
      rw [h2]
      exact Submodule.sub_mem _ (Submodule.subset_span (by simp))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    have hemem : e ∈ Submodule.span ℝ {u, v} := Submodule.smul_mem _ _ hdmem
    have hwmem : w ∈ Submodule.span ℝ {u, v} := by
      rw [hw2]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ hemem)
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    exact hwspan hwmem
  have hee : ⟪e, e⟫ = 1 := by rw [real_inner_self_eq_norm_sq, he_norm]; norm_num
  have heu : ⟪e, u⟫ = 0 := by rw [real_inner_comm]; exact hue
  have hww : ⟪w, w⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hw]; norm_num
  have hinner : ⟪w - ⟪u, w⟫ • u - ⟪e, w⟫ • e, w - ⟪u, w⟫ • u - ⟪e, w⟫ • e⟫ =
      1 - ⟪u, w⟫ ^ 2 - ⟪e, w⟫ ^ 2 := by
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right]
    rw [hww, huu, hee, hue, heu, real_inner_comm w u, real_inner_comm w e]
    ring
  have hbval : ⟪e, w⟫ = (⟪v, w⟫ - ⟪u, v⟫ * ⟪u, w⟫) / ‖dproj u v‖ := by
    rw [he, real_inner_smul_left, inv_mul_eq_div, dproj, inner_sub_left,
      real_inner_smul_left, huu]
    ring_nf
  have hdn : ‖dproj u v‖ ^ 2 = 1 - ⟪u, v⟫ ^ 2 := by
    rw [dproj_norm_sq, hv, huu]; norm_num
  have h1s : (0 : ℝ) < 1 - ⟪u, v⟫ ^ 2 := by
    rw [sub_pos, sq_lt_one_iff_abs_lt_one]; exact huv
  have key : (1 - ⟪u, v⟫ ^ 2) *
      ⟪w - ⟪u, w⟫ • u - ⟪e, w⟫ • e, w - ⟪u, w⟫ • u - ⟪e, w⟫ • e⟫ = gramDet u v w := by
    rw [hinner, hbval, div_pow, hdn]
    simp only [gramDet]
    field_simp [ne_of_gt h1s]
    ring
  have hpos : 0 < ⟪w - ⟪u, w⟫ • u - ⟪e, w⟫ • e, w - ⟪u, w⟫ • u - ⟪e, w⟫ • e⟫ :=
    real_inner_self_pos.mpr hne
  rw [← key]
  exact mul_pos h1s hpos

lemma gramDet_comm12 (u v w : E) : gramDet u v w = gramDet v u w := by
  simp only [gramDet, real_inner_comm v u]; ring

/-- **Spherical triangle excess**: the three dihedral angles of a
nondegenerate trihedral angle sum to strictly more than `π`. -/
lemma dihedral_sum_gt_pi {u v w : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (huv : |⟪u, v⟫| < 1) (hwspan : w ∉ Submodule.span ℝ {u, v}) :
    Real.pi < angle (dproj u v) (dproj u w) + angle (dproj v u) (dproj v w) +
      angle (dproj w u) (dproj w v) := by
  have huu : ⟪u, u⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  have hww : ⟪w, w⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hw]; norm_num
  have huw : |⟪u, w⟫| < 1 := by
    apply abs_inner_lt_one_of_ne hu hw
    · intro h; apply hwspan; rw [h]; exact Submodule.subset_span (by simp)
    · intro h; apply hwspan; rw [h]
      exact Submodule.neg_mem _ (Submodule.subset_span (by simp))
  have hvw : |⟪v, w⟫| < 1 := by
    apply abs_inner_lt_one_of_ne hv hw
    · intro h; apply hwspan; rw [h]; exact Submodule.subset_span (by simp)
    · intro h; apply hwspan; rw [h]
      exact Submodule.neg_mem _ (Submodule.subset_span (by simp))
  have hvu : |⟪v, u⟫| < 1 := by rwa [real_inner_comm u v]
  have hD : 0 < gramDet u v w := gramDet_pos hu hv hw huv hwspan
  have hDnn : 0 ≤ gramDet u v w := hD.le
  -- cosines and sines of the three dihedral angles
  have hcu : Real.cos (angle (dproj u v) (dproj u w)) =
      (⟪v, w⟫ - ⟪u, v⟫ * ⟪u, w⟫) /
        (Real.sqrt (1 - ⟪u, v⟫ ^ 2) * Real.sqrt (1 - ⟪u, w⟫ ^ 2)) :=
    cos_dihedral hu hv hw
  have hcv : Real.cos (angle (dproj v u) (dproj v w)) =
      (⟪u, w⟫ - ⟪u, v⟫ * ⟪v, w⟫) /
        (Real.sqrt (1 - ⟪u, v⟫ ^ 2) * Real.sqrt (1 - ⟪v, w⟫ ^ 2)) := by
    rw [cos_dihedral hv hu hw, real_inner_comm v u]
  have hcw : Real.cos (angle (dproj w u) (dproj w v)) =
      (⟪u, v⟫ - ⟪u, w⟫ * ⟪v, w⟫) /
        (Real.sqrt (1 - ⟪u, w⟫ ^ 2) * Real.sqrt (1 - ⟪v, w⟫ ^ 2)) := by
    rw [cos_dihedral hw hu hv, real_inner_comm w u, real_inner_comm w v]
  have hsu : Real.sin (angle (dproj u v) (dproj u w)) =
      Real.sqrt (gramDet u v w) /
        (Real.sqrt (1 - ⟪u, v⟫ ^ 2) * Real.sqrt (1 - ⟪u, w⟫ ^ 2)) :=
    sin_dihedral hu hv hw huv huw
  have hsv : Real.sin (angle (dproj v u) (dproj v w)) =
      Real.sqrt (gramDet u v w) /
        (Real.sqrt (1 - ⟪u, v⟫ ^ 2) * Real.sqrt (1 - ⟪v, w⟫ ^ 2)) := by
    rw [sin_dihedral hv hu hw hvu hvw, ← gramDet_comm12, real_inner_comm v u]
  -- the key inequality: cos(δu + δv) < -cos(δw)
  have hkey : Real.cos (angle (dproj u v) (dproj u w) + angle (dproj v u) (dproj v w)) <
      -Real.cos (angle (dproj w u) (dproj w v)) := by
    rw [Real.cos_add, hcu, hcv, hsu, hsv, hcw]
    set p := ⟪v, w⟫ with hp
    set q := ⟪u, w⟫ with hq
    set r := ⟪u, v⟫ with hr
    have hrlt : r < 1 := (abs_lt.mp huv).2
    have h1p : (0 : ℝ) < 1 - p ^ 2 := by
      rw [sub_pos, sq_lt_one_iff_abs_lt_one]; exact hvw
    have h1q : (0 : ℝ) < 1 - q ^ 2 := by
      rw [sub_pos, sq_lt_one_iff_abs_lt_one]; exact huw
    have h1r : (0 : ℝ) < 1 - r ^ 2 := by
      rw [sub_pos, sq_lt_one_iff_abs_lt_one]; exact huv
    set A := Real.sqrt (1 - p ^ 2) with hA
    set B := Real.sqrt (1 - q ^ 2) with hB
    set C := Real.sqrt (1 - r ^ 2) with hC
    set S := Real.sqrt (gramDet u v w) with hS
    have hA2 : A ^ 2 = 1 - p ^ 2 := Real.sq_sqrt h1p.le
    have hB2 : B ^ 2 = 1 - q ^ 2 := Real.sq_sqrt h1q.le
    have hC2 : C ^ 2 = 1 - r ^ 2 := Real.sq_sqrt h1r.le
    have hS2 : S ^ 2 = gramDet u v w := Real.sq_sqrt hDnn
    have hApos : 0 < A := Real.sqrt_pos.mpr h1p
    have hBpos : 0 < B := Real.sqrt_pos.mpr h1q
    have hden : (0 : ℝ) < (1 - r ^ 2) * (B * A) := mul_pos h1r (mul_pos hBpos hApos)
    have hCB2 : (C * B) * (C * A) = (1 - r ^ 2) * (B * A) := by
      have h1 : (C * B) * (C * A) = C * C * (B * A) := by ring
      rw [h1, ← pow_two, hC2]
    have e1 : (p - r * q) / (C * B) * ((q - r * p) / (C * A)) =
        (p - r * q) * (q - r * p) / ((1 - r ^ 2) * (B * A)) := by
      rw [div_mul_div_comm, hCB2]
    have e2 : S / (C * B) * (S / (C * A)) =
        gramDet u v w / ((1 - r ^ 2) * (B * A)) := by
      rw [div_mul_div_comm, ← pow_two S, hS2, hCB2]
    have e3 : (r - q * p) / (B * A) =
        (r - q * p) * (1 - r ^ 2) / ((1 - r ^ 2) * (B * A)) := by
      rw [← mul_div_mul_right _ _ (ne_of_gt h1r), mul_comm (B * A) (1 - r ^ 2)]
    rw [e1, e2, e3, div_sub_div_same, ← neg_div, div_lt_div_iff_of_pos_right hden]
    have hid : (p - r * q) * (q - r * p) - gramDet u v w + (r - q * p) * (1 - r ^ 2) =
        gramDet u v w * (r - 1) := by simp only [gramDet, hp, hq, hr]; ring
    have hneg : gramDet u v w * (r - 1) < 0 := mul_neg_of_pos_of_neg hD (by linarith)
    linarith [hid, hneg]
  -- conclude by casework on whether δu + δv ≤ π
  rcases le_or_gt (angle (dproj u v) (dproj u w) + angle (dproj v u) (dproj v w))
      Real.pi with hsum | hsum
  · have hmem1 : angle (dproj u v) (dproj u w) + angle (dproj v u) (dproj v w) ∈
        Set.Icc 0 Real.pi :=
      ⟨add_nonneg (angle_nonneg _ _) (angle_nonneg _ _), hsum⟩
    have hmem2 : Real.pi - angle (dproj w u) (dproj w v) ∈ Set.Icc 0 Real.pi :=
      ⟨by linarith [angle_le_pi (dproj w u) (dproj w v)],
       by linarith [angle_nonneg (dproj w u) (dproj w v)]⟩
    have hlt := (StrictAntiOn.lt_iff_gt Real.strictAntiOn_cos hmem1 hmem2).mp (by
      rwa [← Real.cos_pi_sub] at hkey)
    linarith
  · have hδw : angle (dproj w u) (dproj w v) ≠ 0 := by
      intro h0
      obtain ⟨hx, r0, hr0, hrw⟩ := angle_eq_zero_iff.mp h0
      have hvmem : v ∈ Submodule.span ℝ ({u, w} : Set E) := by
        have hv2 : v = r0 • u + (⟪w, v⟫ - r0 * ⟪w, u⟫) • w := by
          have hdv := hrw
          simp only [dproj, hww, div_one] at hdv
          have h1 : v - ⟪w, v⟫ • w + ⟪w, v⟫ • w =
              r0 • u + (⟪w, v⟫ - r0 * ⟪w, u⟫) • w := by
            rw [hdv, smul_sub, smul_smul, sub_smul]; abel
          exact (sub_add_cancel v _).symm.trans h1
        rw [hv2]
        exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      rw [Submodule.mem_span_pair] at hvmem
      obtain ⟨a, b, hab⟩ := hvmem
      by_cases hb0 : b = 0
      · rw [hb0, zero_smul, add_zero] at hab
        have hna : ‖v‖ = |a| := by rw [← hab, norm_smul, hu, mul_one, Real.norm_eq_abs]
        rw [hv] at hna
        have hrr : ⟪u, v⟫ = a := by rw [← hab, real_inner_smul_right, huu]; ring
        rw [hrr, ← hna] at huv
        exact lt_irrefl _ huv
      · apply hwspan
        have hw2 : w = b⁻¹ • (v - a • u) := by
          have h2 : b • w = v - a • u := by rw [← hab]; abel
          calc w = (b⁻¹ * b) • w := by rw [inv_mul_cancel₀ hb0, one_smul]
            _ = b⁻¹ • (b • w) := by rw [smul_smul]
            _ = b⁻¹ • (v - a • u) := by rw [h2]
        rw [hw2]
        exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.subset_span (by simp))
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))
    have hδwpos : 0 < angle (dproj w u) (dproj w v) :=
      lt_of_le_of_ne (angle_nonneg _ _) (Ne.symm hδw)
    linarith


lemma dproj_self (u : E) : dproj u u = 0 := by
  by_cases hu : u = 0
  · simp [dproj, hu]
  · rw [dproj_eq_zero_iff u u hu]; exact ⟨1, (one_smul ℝ u).symm⟩

lemma dproj_add (u v w : E) : dproj u (v + w) = dproj u v + dproj u w := by
  simp only [dproj, inner_add_right]
  rw [add_div, add_smul, sub_add_eq_sub_sub]
  abel

lemma dproj_smul (u v : E) (c : ℝ) : dproj u (c • v) = c • dproj u v := by
  simp only [dproj, real_inner_smul_right]
  rw [mul_div_assoc, mul_smul, smul_sub]

/-- `i + 1 ≠ i` for `i : Fin n`, `2 ≤ n`. -/
lemma fin_add_one_ne_self {n : ℕ} [NeZero n] (hn : 2 ≤ n) (i : Fin n) : i + 1 ≠ i := by
  intro h
  have h2 : (i + 1).val = i.val := congrArg Fin.val h
  rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < n)] at h2
  have h1 := i.isLt
  rcases Nat.lt_trichotomy (i.val + 1) n with hlt | heq | hgt
  · rw [Nat.mod_eq_of_lt hlt] at h2; omega
  · rw [heq, Nat.mod_self] at h2; omega
  · omega

/-- `i - 1 ≠ i` for `i : Fin n`, `2 ≤ n`. -/
lemma fin_sub_one_ne_self {n : ℕ} [NeZero n] (hn : 2 ≤ n) (i : Fin n) : i - 1 ≠ i := by
  intro h
  have hval : (i - 1).val = (n - 1 + i.val) % n := by
    rw [Fin.sub_def, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < n)]
  have h2 : (i - 1).val = i.val := congrArg Fin.val h
  rw [hval] at h2
  have h1 := i.isLt
  rcases Nat.lt_trichotomy (n - 1 + i.val) n with hlt | heq | hgt
  · rw [Nat.mod_eq_of_lt hlt] at h2; omega
  · rw [heq, Nat.mod_self] at h2; omega
  · have hm : (n - 1 + i.val) % n = (n - 1 + i.val) - n := by
      rw [Nat.mod_eq_sub_mod (by omega : n ≤ n - 1 + i.val),
        Nat.mod_eq_of_lt (by omega : n - 1 + i.val - n < n)]
    rw [hm] at h2; omega

/-- `(i + 1).val = i.val + 1` when `i.val + 1 < n`. -/
lemma fin_val_add_one {n : ℕ} [NeZero n] (i : Fin n) (hi : i.val + 1 < n) :
    (i + 1).val = i.val + 1 := by
  rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < n), Nat.mod_eq_of_lt hi]

/-- `(i - 1).val = i.val - 1` when `1 ≤ i.val`. -/
lemma fin_val_sub_one {n : ℕ} [NeZero n] (i : Fin n) (hi : 1 ≤ i.val) :
    (i - 1).val = i.val - 1 := by
  rw [Fin.coe_sub_iff_le.mpr (show (1 : Fin n) ≤ i by
    rwa [Fin.le_iff_val_le_val, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < n)]),
    Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < n)]

/-- `i - 1 ≠ i + 1` for `i : Fin n`, `3 ≤ n`. -/
lemma fin_sub_one_ne_add_one {n : ℕ} [NeZero n] (hn : 3 ≤ n) (i : Fin n) : i - 1 ≠ i + 1 := by
  intro h
  have h2 : i = i + (1 + 1) := by
    rw [← add_assoc]
    calc i = (i - 1) + 1 := (sub_add_cancel i 1).symm
      _ = (i + 1) + 1 := by rw [h]
  have h3 : (1 + 1 : Fin n) = 0 := by
    have hh := add_left_cancel_iff.mp (show i + 0 = i + (1 + 1) from by rw [add_zero]; exact h2)
    exact hh.symm
  have h4 : ((1 + 1 : Fin n)).val = (0 : Fin n).val := congrArg Fin.val h3
  have hz : ((0 : Fin n) : ℕ) = 0 := rfl
  have h1n : 1 % n = 1 := Nat.mod_eq_of_lt (by omega : 1 < n)
  have h2n : (1 + 1) % n = 1 + 1 := Nat.mod_eq_of_lt (by omega : 1 + 1 < n)
  rw [Fin.val_add, Fin.val_one', hz, h1n, h2n] at h4
  omega

/-- `(1 : Fin n) ≠ 0` for `2 ≤ n`. -/
lemma fin_one_ne_zero {n : ℕ} [NeZero n] (hn : 2 ≤ n) : (1 : Fin n) ≠ 0 := by
  intro h
  have h4 := congrArg Fin.val h
  have hz : ((0 : Fin n) : ℕ) = 0 := rfl
  rw [Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < n), hz] at h4
  omega

/-- `(2 : Fin n) ≠ 0` for `3 ≤ n`. -/
lemma fin_two_ne_zero {n : ℕ} [NeZero n] (hn : 3 ≤ n) : (2 : Fin n) ≠ 0 := by
  intro h
  have h4 := congrArg Fin.val h
  have hz : ((0 : Fin n) : ℕ) = 0 := rfl
  rw [show ((2 : Fin n) : ℕ) = 2 % n from rfl, Nat.mod_eq_of_lt (by omega : 2 < n), hz] at h4
  omega

/-- `(2 : Fin n) ≠ 1` for `3 ≤ n`. -/
lemma fin_two_ne_one {n : ℕ} [NeZero n] (hn : 3 ≤ n) : (2 : Fin n) ≠ 1 := by
  intro h
  have h4 := congrArg Fin.val h
  rw [show ((2 : Fin n) : ℕ) = 2 % n from rfl, Fin.val_one',
    Nat.mod_eq_of_lt (by omega : 2 < n), Nat.mod_eq_of_lt (by omega : 1 < n)] at h4
  omega

/-- `(0 : Fin n) + 1 = 1`. -/
lemma fin_zero_add_one {n : ℕ} [NeZero n] : (0 : Fin n) + 1 = 1 := by
  apply Fin.ext
  rw [Fin.val_add, Fin.val_one', show ((0 : Fin n) : ℕ) = 0 from rfl,
    Nat.zero_add, Nat.mod_mod]

/-- **Strict trihedral face inequality**: the angle `∠(x, z)` is strictly less
than the sum `∠(x, y) + ∠(y, z)` when `y` does not lie in the cone of `x, z`
and `x, z` are not antiparallel. -/
lemma angle_lt_angle_add_of_not_coplanar {x y z : E} (hy : y ≠ 0)
    (hπ : angle x z ≠ π) (hcone : y ∉ Submodule.span ℝ≥0 {x, z}) :
    angle x z < angle x y + angle y z := by
  refine lt_of_le_of_ne (angle_le_angle_add_angle x y z) ?_
  intro heq
  rcases (angle_eq_angle_add_angle_iff hy).mp heq with h1 | h2
  · exact hπ h1
  · exact hcone h2

section PolygonFacts

variable {n : ℕ} [hNz : NeZero n] {V : Fin n → E} {P m : E}
  (hinj : Function.Injective V)
  (hcopl : ∀ i, ⟪m, V i⟫ = ⟪m, V 0⟫)
  (hP : ⟪m, P⟫ ≠ ⟪m, V 0⟫)
  (hconv : ∀ i : Fin n, ∃ f : E →ₗ[ℝ] ℝ, f (V (i + 1) - V i) = 0 ∧
    (∀ j, 0 ≤ f (V j - V i)) ∧ ∀ j, j ≠ i → j ≠ i + 1 → 0 < f (V j - V i))
  (hn : 3 ≤ n)
  (hplane : ∀ j, V j - V 0 ∈ Submodule.span ℝ {V 1 - V 0, V 2 - V 0})

include hcopl hP in
lemma vertex_ne_P (i : Fin n) : V i - P ≠ 0 := by
  intro h
  apply hP
  rw [sub_eq_zero] at h
  rw [← h]
  exact hcopl i

include hcopl in
lemma inner_sub_vertex (i j : Fin n) : ⟪m, V j - V i⟫ = 0 := by
  rw [inner_sub_right, hcopl j, hcopl i, sub_self]

include hP hcopl in
lemma vertex_not_mem_cone (i : Fin n) :
    (P - V i) ∉ Submodule.span ℝ≥0 {V (i - 1) - V i, V (i + 1) - V i} := by
  intro hmem
  rw [Submodule.mem_span_pair] at hmem
  obtain ⟨a, b, hab⟩ := hmem
  have h1 : ⟪m, P - V i⟫ ≠ 0 := by
    rw [inner_sub_right, hcopl i, sub_ne_zero]; exact hP
  have h2 : ⟪m, P - V i⟫ = 0 := by
    rw [← hab]
    simp only [NNReal.smul_def, real_inner_smul_right, inner_add_right, inner_sub_right,
      hcopl (i - 1), hcopl (i + 1), hcopl i, sub_self, mul_zero, add_zero]
  exact h1 h2

include hconv hn in
lemma angle_prev_next_ne_pi (i : Fin n) :
    angle (V (i - 1) - V i) (V (i + 1) - V i) ≠ π := by
  intro h
  obtain ⟨f, hf, -, hfpos⟩ := hconv i
  rw [angle_eq_pi_iff] at h
  obtain ⟨hx, r, hr, hrv⟩ := h
  have h1 : 0 < f (V (i - 1) - V i) :=
    hfpos (i - 1) (fin_sub_one_ne_self (by omega) i) (fin_sub_one_ne_add_one hn i)
  have h2 : f (V (i + 1) - V i) = r * f (V (i - 1) - V i) := by
    rw [hrv, map_smul, smul_eq_mul]
  rw [hf] at h2
  nlinarith

include hinj hn in
lemma tri_sum (i : Fin n) :
    angle (V (i + 1) - V i) (P - V i) + angle (V i - P) (V (i + 1) - P) +
      angle (P - V (i + 1)) (V i - V (i + 1)) = π := by
  have hne : V i ≠ V (i + 1) := (hinj.ne (fin_add_one_ne_self (by omega) i)).symm
  have h2 := EuclideanGeometry.angle_add_angle_add_angle_eq_pi (p₁ := V (i + 1))
    (p₂ := V i) (p₃ := P) hne
  simpa [EuclideanGeometry.angle] using h2

include hconv hP hcopl hn in
lemma vertex_ineq (i : Fin n) :
    angle (V (i - 1) - V i) (V (i + 1) - V i) <
      angle (V (i - 1) - V i) (P - V i) + angle (P - V i) (V (i + 1) - V i) := by
  have hPi : P - V i ≠ 0 := by
    rw [← neg_ne_zero, neg_sub]; exact vertex_ne_P hcopl hP i
  apply angle_lt_angle_add_of_not_coplanar hPi
  · exact angle_prev_next_ne_pi hconv hn i
  · exact vertex_not_mem_cone hcopl hP i

include hconv hn in
/-- At a polygon vertex, neither edge direction is a multiple of the other. -/
lemma corner_not_mem_span (i : Fin n) :
    V (i - 1) - V i ∉ Submodule.span ℝ {V (i + 1) - V i} ∧
    V (i + 1) - V i ∉ Submodule.span ℝ {V (i - 1) - V i} := by
  obtain ⟨f, hf, -, hfpos⟩ := hconv i
  obtain ⟨g, hg, -, hgpos⟩ := hconv (i - 1)
  have hg' : g (V i - V (i - 1)) = 0 := by rw [sub_add_cancel] at hg; exact hg
  have hge2 : g (V (i - 1) - V i) = 0 := by
    have h1 : V (i - 1) - V i = -(V i - V (i - 1)) := by abel
    rw [h1, map_neg, neg_eq_zero]; exact hg'
  have hge1 : 0 < g (V (i + 1) - V i) := by
    have h1 := hgpos (i + 1) (Ne.symm (fin_sub_one_ne_add_one hn i))
      (by rw [sub_add_cancel]; exact fin_add_one_ne_self (by omega) i)
    have h2 : V (i + 1) - V (i - 1) = (V (i + 1) - V i) + (V i - V (i - 1)) := by abel
    rw [h2, map_add, hg', add_zero] at h1
    exact h1
  constructor
  · intro hmem
    rw [Submodule.mem_span_singleton] at hmem
    obtain ⟨r, hr⟩ := hmem
    have h1 : 0 < f (V (i - 1) - V i) :=
      hfpos (i - 1) (fin_sub_one_ne_self (by omega) i) (fin_sub_one_ne_add_one hn i)
    have h2 : f (V (i - 1) - V i) = r * f (V (i + 1) - V i) := by
      rw [← hr, map_smul, smul_eq_mul]
    rw [hf] at h2
    nlinarith
  · intro hmem
    rw [Submodule.mem_span_singleton] at hmem
    obtain ⟨r, hr⟩ := hmem
    have h2 : g (V (i + 1) - V i) = r * g (V (i - 1) - V i) := by
      rw [← hr, map_smul, smul_eq_mul]
    rw [hge2] at h2
    nlinarith [hge1]

include hinj hconv hn in
/-- The two edge directions at a polygon vertex are linearly independent. -/
lemma corner_independent (i : Fin n) :
    LinearIndependent ℝ ![V (i - 1) - V i, V (i + 1) - V i] := by
  have hx : V (i - 1) - V i ≠ 0 := by
    rw [sub_ne_zero]; exact hinj.ne (fin_sub_one_ne_self (by omega) i)
  rw [LinearIndependent.pair_iff' hx]
  intro a h
  exact (corner_not_mem_span hconv hn i).2 (Submodule.mem_span_singleton.mpr ⟨a, h⟩)

lemma range_pair {E : Type*} (x y : E) : Set.range ![x, y] = {x, y} := by
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · intro hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩

include hinj hconv hn hplane in
/-- **Corner containment**: at any vertex of the polygon, every other vertex
lies in the cone of the two adjacent edge directions. -/
lemma corner_cone (i j : Fin n) :
    V j - V i ∈ Submodule.span ℝ≥0 {V (i - 1) - V i, V (i + 1) - V i} := by
  set W₀ : Submodule ℝ E := Submodule.span ℝ {V 1 - V 0, V 2 - V 0} with hW₀def
  set S : Submodule ℝ E := Submodule.span ℝ {V (i - 1) - V i, V (i + 1) - V i} with hSdef
  have hin0 : LinearIndependent ℝ ![V 1 - V 0, V 2 - V 0] := by
    have h10 : V 1 - V 0 ≠ 0 := by
      rw [sub_ne_zero]; exact hinj.ne (fin_one_ne_zero (by omega))
    rw [LinearIndependent.pair_iff' h10]
    intro a hmem
    obtain ⟨f, hf, -, hfpos⟩ := hconv 0
    have hf0 : f (V 1 - V 0) = 0 := by rw [fin_zero_add_one] at hf; exact hf
    have h1 : 0 < f (V 2 - V 0) :=
      hfpos 2 (fin_two_ne_zero hn) (by rw [fin_zero_add_one]; exact fin_two_ne_one hn)
    have h2 : f (V 2 - V 0) = a * f (V 1 - V 0) := by rw [← hmem, map_smul, smul_eq_mul]
    rw [hf0] at h2
    nlinarith
  have hrkW : Module.finrank ℝ W₀ = 2 := by
    rw [hW₀def, ← range_pair, finrank_span_eq_card hin0, Fintype.card_fin]
  have hrkS : Module.finrank ℝ S = 2 := by
    rw [hSdef, ← range_pair, finrank_span_eq_card (corner_independent hinj hconv hn i),
      Fintype.card_fin]
  have hle : S ≤ W₀ := by
    rw [hSdef, hW₀def, Submodule.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · have h1 : V (i - 1) - V i = (V (i - 1) - V 0) - (V i - V 0) := by abel
      rw [h1]; exact Submodule.sub_mem _ (hplane (i - 1)) (hplane i)
    · have h1 : V (i + 1) - V i = (V (i + 1) - V 0) - (V i - V 0) := by abel
      rw [h1]; exact Submodule.sub_mem _ (hplane (i + 1)) (hplane i)
  have heq : S = W₀ := by
    haveI : Module.Finite ℝ ↥W₀ := by
      rw [hW₀def]; exact Module.Finite.span_of_finite _ (Set.toFinite _)
    exact Submodule.eq_of_le_of_finrank_eq hle (hrkS.trans hrkW.symm)
  have hmem : V j - V i ∈ S := by
    rw [heq, hW₀def]
    have h1 : V j - V i = (V j - V 0) - (V i - V 0) := by abel
    rw [h1]; exact Submodule.sub_mem _ (hplane j) (hplane i)
  rw [hSdef, Submodule.mem_span_pair] at hmem
  obtain ⟨a, b, hab⟩ := hmem
  obtain ⟨f, hf, hfnonneg, hfpos⟩ := hconv i
  obtain ⟨g, hg, hgnonneg, hgpos⟩ := hconv (i - 1)
  have hg' : g (V i - V (i - 1)) = 0 := by rw [sub_add_cancel] at hg; exact hg
  have hge2 : g (V (i - 1) - V i) = 0 := by
    have h1 : V (i - 1) - V i = -(V i - V (i - 1)) := by abel
    rw [h1, map_neg, neg_eq_zero]; exact hg'
  have hge1 : 0 < g (V (i + 1) - V i) := by
    have h1 := hgpos (i + 1) (Ne.symm (fin_sub_one_ne_add_one hn i))
      (by rw [sub_add_cancel]; exact fin_add_one_ne_self (by omega) i)
    have h2 : V (i + 1) - V (i - 1) = (V (i + 1) - V i) + (V i - V (i - 1)) := by abel
    rw [h2, map_add, hg', add_zero] at h1
    exact h1
  have hfe2 : 0 < f (V (i - 1) - V i) :=
    hfpos (i - 1) (fin_sub_one_ne_self (by omega) i) (fin_sub_one_ne_add_one hn i)
  have ha : 0 ≤ a := by
    have h1 : f (V j - V i) = a * f (V (i - 1) - V i) := by
      rw [← hab, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hf, mul_zero, add_zero]
    have hnn : 0 ≤ a * f (V (i - 1) - V i) := h1 ▸ hfnonneg j
    exact nonneg_of_mul_nonneg_right ((mul_comm a (f (V (i - 1) - V i))) ▸ hnn) hfe2
  have hb : 0 ≤ b := by
    have h1 : g (V j - V (i - 1)) = b * g (V (i + 1) - V i) := by
      have h2 : V j - V (i - 1) = (V j - V i) + (V i - V (i - 1)) := by abel
      rw [h2, map_add, hg', add_zero, ← hab, map_add, map_smul, map_smul, smul_eq_mul,
        smul_eq_mul, hge2, mul_zero, zero_add]
    have hnn : 0 ≤ b * g (V (i + 1) - V i) := h1 ▸ hgnonneg j
    exact nonneg_of_mul_nonneg_right ((mul_comm b (g (V (i + 1) - V i))) ▸ hnn) hge1
  rw [Submodule.mem_span_pair]
  exact ⟨⟨a, ha⟩, ⟨b, hb⟩, by simp only [NNReal.smul_def]; exact hab⟩

include hinj hconv hn hplane in
/-- **Extremality**: at a non-boundary vertex `V i` (`2 ≤ i ≤ n - 2`), the
coefficients of the corner decomposition of `V 0` sum to more than `1`.
Equivalently, `V 0` does not lie in the triangle of three consecutive
vertices around `V i`. -/
lemma corner_coeff_gt_one (i : Fin n) (hi1 : 2 ≤ i.val) (hi2 : i.val ≤ n - 2) {a b : ℝ≥0}
    (h : a • (V (i - 1) - V i) + b • (V (i + 1) - V i) = V 0 - V i) :
    (a : ℝ) + b > 1 := by
  obtain ⟨f, hf, hfnonneg, hfpos⟩ := hconv 0
  have hf0 : f (V 1 - V 0) = 0 := by rw [fin_zero_add_one] at hf; exact hf
  have hval1 : (i + 1 : Fin n).val = i.val + 1 := by
    rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < n),
      Nat.mod_eq_of_lt (by omega : i.val + 1 < n)]
  have hxi : 0 < f (V i - V 0) := by
    apply hfpos i
    · intro hh; have hv := congrArg Fin.val hh
      rw [show ((0 : Fin n) : ℕ) = 0 from rfl] at hv; omega
    · intro hh; rw [fin_zero_add_one] at hh; have hv := congrArg Fin.val hh
      rw [Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < n)] at hv; omega
  have hxi1 : 0 < f (V (i + 1) - V 0) := by
    apply hfpos (i + 1)
    · intro hh; have hv := congrArg Fin.val hh
      rw [hval1, show ((0 : Fin n) : ℕ) = 0 from rfl] at hv; omega
    · intro hh; rw [fin_zero_add_one] at hh; have hv := congrArg Fin.val hh
      rw [hval1, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < n)] at hv; omega
  have happ : f (V 0 - V i) =
      (a : ℝ) * f (V (i - 1) - V i) + (b : ℝ) * f (V (i + 1) - V i) := by
    rw [← h, map_add, NNReal.smul_def, NNReal.smul_def, map_smul, map_smul,
      smul_eq_mul, smul_eq_mul]
  have hleft : f (V 0 - V i) = -f (V i - V 0) := by
    rw [← map_neg]; congr 1; abel
  have hr1 : f (V (i - 1) - V i) = f (V (i - 1) - V 0) - f (V i - V 0) := by
    rw [← map_sub]; congr 1; abel
  have hr2 : f (V (i + 1) - V i) = f (V (i + 1) - V 0) - f (V i - V 0) := by
    rw [← map_sub]; congr 1; abel
  rw [hleft, hr1, hr2] at happ
  -- (a + b - 1) * xᵢ = a * x_{i-1} + b * x_{i+1} ≥ 0
  have hkey : ((a : ℝ) + b - 1) * f (V i - V 0) =
      (a : ℝ) * f (V (i - 1) - V 0) + (b : ℝ) * f (V (i + 1) - V 0) := by
    nlinarith [happ]
  by_contra hle
  push Not at hle
  have hnonneg1 := hfnonneg (i - 1)
  have hnonneg2 := hfnonneg (i + 1)
  have hprod : (a : ℝ) * f (V (i - 1) - V 0) + (b : ℝ) * f (V (i + 1) - V 0) ≤ 0 := by
    have h1 : (a : ℝ) + b - 1 ≤ 0 := by linarith
    nlinarith [hkey, hxi]
  have hb0 : (b : ℝ) = 0 := by
    have h1 : (b : ℝ) * f (V (i + 1) - V 0) = 0 := by
      nlinarith [hprod, hnonneg1, hnonneg2, NNReal.coe_nonneg a, NNReal.coe_nonneg b]
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact h2
    · exact absurd h2 (ne_of_gt hxi1)
  have hab0 : (a : ℝ) * f (V (i - 1) - V 0) = 0 := by
    nlinarith [hprod, hnonneg2, NNReal.coe_nonneg a]
  by_cases haz : (a : ℝ) = 0
  · -- `a = b = 0`, so `V 0 = V i`, contradicting injectivity (`i ≠ 0`).
    have ha0' : a = 0 := NNReal.coe_eq_zero.mp haz
    have hb0' : b = 0 := NNReal.coe_eq_zero.mp hb0
    rw [ha0', hb0', zero_smul, zero_smul, add_zero, eq_comm, sub_eq_zero] at h
    have hi0 : (0 : Fin n) ≠ i := by
      intro hh; have hv := congrArg Fin.val hh; simp at hv; omega
    exact hi0 (hinj h)
  · -- Then `x_{i-1} = 0`, forcing `i = 2`; the corner equation gives `a = 1`,
    -- hence `V 0 = V 1`, again contradicting injectivity.
    have hx1 : f (V (i - 1) - V 0) = 0 := by
      rcases mul_eq_zero.mp hab0 with h2 | h2
      · exact absurd h2 haz
      · exact h2
    have hi2' : i = 2 := by
      by_contra hne
      have h3 : 0 < f (V (i - 1) - V 0) := by
        apply hfpos (i - 1)
        · intro hh
          have hv := congrArg Fin.val hh
          rw [fin_val_sub_one i (by omega), show ((0 : Fin n) : ℕ) = 0 from rfl] at hv
          omega
        · intro hh
          apply hne
          rw [fin_zero_add_one] at hh
          have hv := congrArg Fin.val hh
          rw [fin_val_sub_one i (by omega), Fin.val_one',
            Nat.mod_eq_of_lt (by omega : 1 < n)] at hv
          exact Fin.ext (by rw [show ((2 : Fin n) : ℕ) = 2 % n from rfl,
            Nat.mod_eq_of_lt (by omega : 2 < n)]; omega)
      exact absurd hx1 (ne_of_gt h3)
    have hb0' : b = 0 := NNReal.coe_eq_zero.mp hb0
    rw [hb0', zero_smul, add_zero] at h
    have happ2 : (a : ℝ) * f (V (i - 1) - V i) = f (V 0 - V i) := by
      rw [← h, NNReal.smul_def, map_smul, smul_eq_mul]
    rw [hleft, hr1, hx1, zero_sub] at happ2
    have ha1 : (a : ℝ) = 1 := by
      have h3 : (a : ℝ) * f (V i - V 0) = f (V i - V 0) := by nlinarith [happ2]
      exact (mul_eq_right₀ (ne_of_gt hxi)).mp h3
    have ha1' : a = 1 := NNReal.coe_eq_one.mp ha1
    have h4 : V 0 = V (i - 1) := by
      rw [ha1', one_smul] at h
      have h5 := congrArg (· + V i) h
      rw [sub_add_cancel, sub_add_cancel] at h5
      exact h5.symm
    have h5 : V 0 = V 1 := by
      rw [hi2', show ((2 : Fin n) - 1) = 1 from by
        rw [show (2 : Fin n) = 1 + 1 from by
          apply Fin.ext
          rw [Fin.val_add, Fin.val_one',
            show ((2 : Fin n) : ℕ) = 2 % n from rfl,
            Nat.mod_eq_of_lt (by omega : 1 < n),
            Nat.mod_eq_of_lt (by omega : 2 < n)]]
        exact add_sub_cancel_right 1 1] at h4
      exact h4
    exact Ne.symm (fin_one_ne_zero (by omega)) (hinj h5)

include hinj hconv hn hplane in
/-- **Strict corner containment**: at any vertex, every non-adjacent vertex
lies in the *interior* of the cone of the two adjacent edge directions. -/
lemma corner_cone_strict (i j : Fin n) (hj1 : j ≠ i - 1) (hj2 : j ≠ i) (hj3 : j ≠ i + 1) :
    ∃ a b : ℝ≥0, 0 < a ∧ 0 < b ∧
      a • (V (i - 1) - V i) + b • (V (i + 1) - V i) = V j - V i := by
  have hcc := corner_cone hinj hconv hn hplane i j
  rw [Submodule.mem_span_pair] at hcc
  obtain ⟨a, b, hab⟩ := hcc
  obtain ⟨f, hf, -, hfpos⟩ := hconv i
  obtain ⟨g, hg, -, hgpos⟩ := hconv (i - 1)
  have ha : 0 < a := by
    by_contra ha0
    push Not at ha0
    have ha0' : a = 0 := le_antisymm ha0 (NNReal.coe_nonneg a)
    rw [ha0', zero_smul, zero_add] at hab
    have h1 : 0 < f (V j - V i) := hfpos j hj2 hj3
    have h2 : f (V j - V i) = (b : ℝ) * f (V (i + 1) - V i) := by
      rw [← hab, NNReal.smul_def, map_smul, smul_eq_mul]
    rw [hf] at h2
    linarith [h1, h2, NNReal.coe_nonneg b]
  have hb : 0 < b := by
    by_contra hb0
    push Not at hb0
    have hb0' : b = 0 := le_antisymm hb0 (NNReal.coe_nonneg b)
    rw [hb0', zero_smul, add_zero] at hab
    have hg' : g (V i - V (i - 1)) = 0 := by rw [sub_add_cancel] at hg; exact hg
    have h1 : 0 < g (V j - V (i - 1)) :=
      hgpos j hj1 (by rwa [sub_add_cancel])
    have h3 : g (V (i - 1) - V i) = 0 := by
      have h4 : V (i - 1) - V i = -(V i - V (i - 1)) := by abel
      rw [h4, map_neg, neg_eq_zero]; exact hg'
    have h2 : g (V j - V i) = 0 := by
      rw [← hab, NNReal.smul_def, map_smul, smul_eq_mul, h3, mul_zero]
    have h5 : g (V j - V i) = g (V j - V (i - 1)) := by
      have h6 : V j - V (i - 1) = (V j - V i) + (V i - V (i - 1)) := by abel
      have h7 : g (V j - V (i - 1)) = g (V j - V i) + g (V i - V (i - 1)) := by
        rw [h6, map_add]
      rw [hg', add_zero] at h7
      exact h7.symm
    rw [h5] at h2
    linarith [h1, h2]
  exact ⟨a, b, ha, hb, hab⟩

include hinj hconv hn hplane in
/-- **Fan monotonicity**: viewed from `V 0`, the ray to `V j` lies in the cone
of the rays to `V 1` and `V (j+1)` (for `1 ≤ j ≤ n - 2`). -/
lemma fan_cone (j : Fin n) (hj1 : 1 ≤ j.val) (hj2 : j.val ≤ n - 2) :
    V j - V 0 ∈ Submodule.span ℝ≥0 {V 1 - V 0, V (j + 1) - V 0} := by
  -- We induct on `j.val`. The key step: at vertex `V (k+1)`, the corner
  -- decomposition of `V 0` has coefficients `a, b > 0` with `a + b > 1`
  -- (extremality), so `V (k+1) - V 0 = (a/D)(V k - V 0) + (b/D)(V (k+2) - V 0)`
  -- with `D = a + b - 1 > 0`; substituting the induction hypothesis for `V k`
  -- and eliminating the `(V (k+1) - V 0)`-term via the edge-`(0,1)` functional
  -- yields the claim.
  have H : ∀ k : ℕ, ∀ i : Fin n, i.val = k → 1 ≤ k → k ≤ n - 2 →
      V i - V 0 ∈ Submodule.span ℝ≥0 {V 1 - V 0, V (i + 1) - V 0} := by
    intro k
    induction k with
    | zero => intro i _ h1; omega
    | succ k ihk =>
      intro i hival hk1 hkn
      by_cases hk0 : k = 0
      · -- base: `i = 1`, and `V 1 - V 0 = 1 • (V 1 - V 0) + 0 • (V 2 - V 0)`
        subst hk0
        have hi1 : i = 1 := by
          apply Fin.ext
          rw [hival, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < n)]
        have h12 : (1 : Fin n) + 1 = 2 := by
          apply Fin.ext
          rw [Fin.val_add, Fin.val_one', show ((2 : Fin n) : ℕ) = 2 % n from rfl,
            Nat.mod_eq_of_lt (by omega : 1 < n), Nat.mod_eq_of_lt (by omega : 2 < n)]
        rw [hi1, h12, Submodule.mem_span_pair]
        refine ⟨⟨1, by norm_num⟩, ⟨0, by norm_num⟩, ?_⟩
        rw [NNReal.smul_def, NNReal.smul_def]
        show (1 : ℝ) • (V 1 - V 0) + (0 : ℝ) • (V 2 - V 0) = V 1 - V 0
        rw [one_smul, zero_smul, add_zero]
      · -- inductive step: `i.val = k + 1` with `1 ≤ k`
        have hk1' : 1 ≤ k := by omega
        have hk2' : k ≤ n - 2 := by omega
        -- the induction hypothesis at `i - 1`
        have him1 : (i - 1 : Fin n).val = k := by
          rw [fin_val_sub_one i (by omega), hival]; omega
        have hih := ihk (i - 1) him1 hk1' hk2'
        rw [Submodule.mem_span_pair] at hih
        obtain ⟨a', b', hab'⟩ := hih
        rw [sub_add_cancel] at hab'
        -- corner decomposition at `V i` with target `V 0`, strictly positive
        have h0ne1 : (0 : Fin n) ≠ i - 1 := by
          intro hh
          have hv := congrArg Fin.val hh
          rw [show ((0 : Fin n) : ℕ) = 0 from rfl, fin_val_sub_one i (by omega), hival] at hv
          omega
        have h0ne2 : (0 : Fin n) ≠ i := by
          intro hh
          have hv := congrArg Fin.val hh
          rw [show ((0 : Fin n) : ℕ) = 0 from rfl, hival] at hv
          omega
        have h0ne3 : (0 : Fin n) ≠ i + 1 := by
          intro hh
          have hv := congrArg Fin.val hh
          rw [show ((0 : Fin n) : ℕ) = 0 from rfl, fin_val_add_one i (by omega), hival] at hv
          omega
        obtain ⟨a, b, ha, hb, hab⟩ := corner_cone_strict hinj hconv hn hplane i 0
          h0ne1 h0ne2 h0ne3
        -- extremality: `a + b > 1`
        have hgt : (a : ℝ) + b > 1 :=
          corner_coeff_gt_one hinj hconv hn hplane i (by rw [hival]; omega)
            (by rw [hival]; omega) hab
        -- the "betweenness" relation
        have hD : (a : ℝ) • (V (i - 1) - V 0) + (b : ℝ) • (V (i + 1) - V 0) =
            ((a : ℝ) + b - 1) • (V i - V 0) := by
          have h1 := hab
          simp only [NNReal.smul_def] at h1
          have h2 : (a : ℝ) • (V (i - 1) - V 0) + (b : ℝ) • (V (i + 1) - V 0) =
              ((a : ℝ) • (V (i - 1) - V i) + (b : ℝ) • (V (i + 1) - V i)) +
                ((a : ℝ) + b) • (V i - V 0) := by
            have h3 : (a : ℝ) • (V (i - 1) - V 0) =
                (a : ℝ) • (V (i - 1) - V i) + (a : ℝ) • (V i - V 0) := by
              rw [← smul_add]; congr 1; abel
            have h4 : (b : ℝ) • (V (i + 1) - V 0) =
                (b : ℝ) • (V (i + 1) - V i) + (b : ℝ) • (V i - V 0) := by
              rw [← smul_add]; congr 1; abel
            rw [h3, h4, add_smul]; abel
          rw [h2, h1, show V 0 - V i = -(V i - V 0) from by abel, sub_smul, one_smul]
          abel
        -- substitute the induction hypothesis
        have hE : (((a : ℝ) + b - 1) - (a : ℝ) * b') • (V i - V 0) =
            ((a : ℝ) * a') • (V 1 - V 0) + (b : ℝ) • (V (i + 1) - V 0) := by
          have h1 : (a : ℝ) • (V (i - 1) - V 0) =
              ((a : ℝ) * a') • (V 1 - V 0) + ((a : ℝ) * b') • (V i - V 0) := by
            have h2 := hab'
            simp only [NNReal.smul_def] at h2
            rw [← h2, smul_add, smul_smul, smul_smul]
          rw [h1] at hD
          have h3 : (((a : ℝ) + b - 1) - (a : ℝ) * b') • (V i - V 0) =
              ((a : ℝ) + b - 1) • (V i - V 0) - ((a : ℝ) * b') • (V i - V 0) := by
            rw [sub_smul]
          rw [h3, ← hD]
          abel
        -- show the eliminated coefficient positive, using the edge-`(0,1)` functional
        obtain ⟨f, hf, hfnonneg, hfpos⟩ := hconv 0
        have hf0 : f (V 1 - V 0) = 0 := by rw [fin_zero_add_one] at hf; exact hf
        have hEpos : 0 < ((a : ℝ) + b - 1) - (a : ℝ) * b' := by
          have h4 := congrArg f hE
          simp only [map_smul, smul_eq_mul, map_add] at h4
          rw [hf0, mul_zero, zero_add] at h4
          have h5 : 0 < f (V i - V 0) := by
            apply hfpos i
            · exact h0ne2.symm
            · intro hh
              rw [fin_zero_add_one] at hh
              have hv := congrArg Fin.val hh
              rw [hival, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < n)] at hv; omega
          have h6 : 0 < f (V (i + 1) - V 0) := by
            apply hfpos (i + 1)
            · exact h0ne3.symm
            · intro hh
              rw [fin_zero_add_one] at hh
              have hv := congrArg Fin.val hh
              rw [fin_val_add_one i (by omega), hival, Fin.val_one',
                Nat.mod_eq_of_lt (by omega : 1 < n)] at hv; omega
          nlinarith [h4, h5, h6, hb]
        -- conclude
        set E : ℝ := ((a : ℝ) + b - 1) - (a : ℝ) * b' with hEdef
        have h7 : V i - V 0 =
            (((a : ℝ) * a') / E) • (V 1 - V 0) + ((b : ℝ) / E) • (V (i + 1) - V 0) := by
          have h8 := congrArg (E⁻¹ • ·) hE
          rwa [smul_add, smul_smul, smul_smul, smul_smul, mul_comm E⁻¹ E,
            mul_inv_cancel₀ (ne_of_gt hEpos), one_smul, mul_comm E⁻¹ (↑a * ↑a'),
            mul_comm E⁻¹ (↑b : ℝ), ← div_eq_mul_inv, ← div_eq_mul_inv] at h8
        rw [Submodule.mem_span_pair]
        have hnn1 : (0 : ℝ) ≤ (a : ℝ) * a' / E := by positivity
        have hnn2 : (0 : ℝ) ≤ (b : ℝ) / E := by positivity
        refine ⟨⟨(a * a') / E, hnn1⟩, ⟨(b : ℝ) / E, hnn2⟩, ?_⟩
        rw [NNReal.smul_def, NNReal.smul_def]
        show ((a : ℝ) * a' / E) • (V 1 - V 0) + ((b : ℝ) / E) • (V (i + 1) - V 0) =
          V i - V 0
        exact h7.symm
  exact H j.val j rfl hj1 hj2

/-- The vertices, viewed as a circular (`ℕ`-indexed) family: `Vc k = V ⟨k % n⟩`.
Useful for stating fan triangulations without `Fin n` arithmetic. -/
noncomputable def Vc (V : Fin n → E) (k : ℕ) : E := V ⟨k % n, Nat.mod_lt k (by omega)⟩

lemma Vc_val (k : ℕ) (hk : k < n) : Vc hn V k = V ⟨k, hk⟩ :=
  congrArg V (Fin.ext (Nat.mod_eq_of_lt hk))

lemma Vc_zero : Vc hn V 0 = V 0 := congrArg V (Fin.ext (Nat.zero_mod n))

lemma Vc_add_one (j : Fin n) : Vc hn V (j.val + 1) = V (j + 1) := by
  apply congrArg V
  apply Fin.ext
  rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < n)]

lemma Vc_sub_one (j : Fin n) : Vc hn V (j.val + n - 1) = V (j - 1) := by
  apply congrArg V
  apply Fin.ext
  have h2 : (j - 1 : Fin n).val = (n - 1 + j.val) % n := by
    rw [Fin.sub_def, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < n)]
  have h3 : j.val + n - 1 = n - 1 + j.val := by omega
  rw [h2, h3]

/-- Conversion between the `Fin n`-indexed and the circular `ℕ`-indexed
interior angle at vertex `j`. -/
lemma theta_eq (j : Fin n) :
    angle (Vc hn V (j.val + n - 1) - Vc hn V j.val) (Vc hn V (j.val + 1) - Vc hn V j.val) =
      angle (V (j - 1) - V j) (V (j + 1) - V j) := by
  rw [Vc_sub_one hn j, Vc_add_one hn j, Vc_val hn j.val j.isLt]

/-- **Angle telescope**: if every `u k` (`1 ≤ k ≤ n - 2`) lies in the cone of
`u 1` and `u (k+1)`, then the consecutive angles telescope. Used twice:
for the interior-angle sum (with `u k = Vc k - V 0`) and for the dihedral-angle
sum (with `u k = dproj (V 0 - P) (Vc k - V 0)`). -/
lemma angle_telescope {u : ℕ → E} (hn : 3 ≤ n)
    (h_cone : ∀ k, 1 ≤ k → k ≤ n - 2 → u k ∈ Submodule.span ℝ≥0 {u 1, u (k + 1)})
    (h_ne : ∀ k, 1 ≤ k → k ≤ n - 2 → u k ≠ 0)
    (m : ℕ) (hm : m ≤ n - 2) :
    ∑ k ∈ Finset.range m, angle (u (k + 1)) (u (k + 2)) = angle (u 1) (u (m + 1)) := by
  induction m with
  | zero =>
    rw [Finset.range_zero, Finset.sum_empty, angle_self (h_ne 1 (by omega) (by omega))]
  | succ m ihm =>
    rw [Finset.sum_range_succ, ihm (by omega)]
    by_cases hm0 : m = 0
    · subst hm0
      rw [angle_self (h_ne 1 (by omega) (by omega)), zero_add]
    · exact (angle_eq_angle_add_add_angle_add_of_mem_span
        (h_ne (m + 1) (by omega) (by omega)) (h_cone (m + 1) (by omega) (by omega))).symm

include hinj hconv hn hplane in
/-- The cone hypothesis of `angle_telescope` for the rays from `V 0`. -/
lemma fan_cone_Vc (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ n - 2) :
    Vc hn V k - V 0 ∈ Submodule.span ℝ≥0 {Vc hn V 1 - V 0, Vc hn V (k + 1) - V 0} := by
  have hk : k < n := by omega
  have h1 : Vc hn V 1 = V 1 := by
    rw [Vc_val hn 1 (by omega)]
    congr 1
    apply Fin.ext
    rw [Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < n)]
  have h2 : Vc hn V (k + 1) = V (⟨k, hk⟩ + 1) := by
    have h3 := Vc_add_one (V := V) hn (⟨k, hk⟩ : Fin n)
    rwa [show (⟨k, hk⟩ : Fin n).val = k from rfl] at h3
  rw [Vc_val hn k hk, h1, h2]
  exact fan_cone hinj hconv hn hplane ⟨k, hk⟩ (by omega) (by omega)

include hinj hn in
/-- The rays from `V 0` are nonzero. -/
lemma fan_ne_Vc (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ n - 2) : Vc hn V k - V 0 ≠ 0 := by
  have hk : k < n := by omega
  rw [Vc_val hn k hk, sub_ne_zero]
  apply hinj.ne
  intro hh
  have hv := congrArg Fin.val hh
  rw [show ((⟨k, hk⟩ : Fin n)).val = k from rfl, show ((0 : Fin n) : ℕ) = 0 from rfl] at hv
  omega

include hinj hn in
/-- Angle sum of the fan triangle `(V 0, Vc (k+1), Vc (k+2))`. -/
lemma fan_triangle_sum (k : ℕ) (hk : k ≤ n - 3) :
    angle (Vc hn V (k + 1) - V 0) (Vc hn V (k + 2) - V 0) +
      angle (V 0 - Vc hn V (k + 1)) (Vc hn V (k + 2) - Vc hn V (k + 1)) +
        angle (Vc hn V (k + 1) - Vc hn V (k + 2)) (V 0 - Vc hn V (k + 2)) = π := by
  have hne : Vc hn V (k + 1) ≠ Vc hn V (k + 2) := by
    rw [Vc_val hn (k + 1) (by omega), Vc_val hn (k + 2) (by omega)]
    apply hinj.ne
    intro hh
    have hv := congrArg Fin.val hh
    rw [show ((⟨k + 1, by omega⟩ : Fin n)).val = k + 1 from rfl,
      show ((⟨k + 2, by omega⟩ : Fin n)).val = k + 2 from rfl] at hv
    omega
  have h2 := EuclideanGeometry.angle_add_angle_add_angle_eq_pi (p₁ := Vc hn V (k + 2))
    (p₂ := Vc hn V (k + 1)) (p₃ := V 0) hne
  simp only [EuclideanGeometry.angle, vsub_eq_sub] at h2
  rw [show angle (Vc hn V (k + 2) - Vc hn V (k + 1)) (V 0 - Vc hn V (k + 1)) =
      angle (V 0 - Vc hn V (k + 1)) (Vc hn V (k + 2) - Vc hn V (k + 1)) from angle_comm _ _,
    show angle (V 0 - Vc hn V (k + 2)) (Vc hn V (k + 1) - Vc hn V (k + 2)) =
      angle (Vc hn V (k + 1) - Vc hn V (k + 2)) (V 0 - Vc hn V (k + 2)) from angle_comm _ _] at h2
  linarith

include hinj hconv hn hplane in
/-- **Corner split**: the interior angle at `Vc j` (`2 ≤ j ≤ n - 2`) splits
along the diagonal to `V 0`. -/
lemma corner_split (j : ℕ) (hj1 : 2 ≤ j) (hj2 : j ≤ n - 2) :
    angle (Vc hn V (j + n - 1) - Vc hn V j) (Vc hn V (j + 1) - Vc hn V j) =
      angle (Vc hn V (j - 1) - Vc hn V j) (V 0 - Vc hn V j) +
        angle (V 0 - Vc hn V j) (Vc hn V (j + 1) - Vc hn V j) := by
  set j' : Fin n := ⟨j, by omega⟩ with hj'def
  have hjv : j'.val = j := rfl
  have h1 : angle (Vc hn V (j + n - 1) - Vc hn V j) (Vc hn V (j + 1) - Vc hn V j) =
      angle (V (j' - 1) - V j') (V (j' + 1) - V j') := by
    have h2 := theta_eq (V := V) hn j'
    rwa [hjv] at h2
  have hne : V 0 - V j' ≠ 0 := by
    rw [sub_ne_zero]
    apply hinj.ne
    intro hh
    have hv := congrArg Fin.val hh
    rw [show ((0 : Fin n) : ℕ) = 0 from rfl, hjv] at hv
    omega
  have hsplit : angle (V (j' - 1) - V j') (V (j' + 1) - V j') =
      angle (V (j' - 1) - V j') (V 0 - V j') + angle (V 0 - V j') (V (j' + 1) - V j') :=
    angle_eq_angle_add_add_angle_add_of_mem_span hne
      (corner_cone hinj hconv hn hplane j' 0)
  rw [h1, hsplit]
  congr 1
  · have h3 : Vc hn V (j - 1) = V (j' - 1) := by
      rw [Vc_val hn (j - 1) (by omega)]
      congr 1
      apply Fin.ext
      rw [fin_val_sub_one j' (by omega), hjv]
    rw [h3, Vc_val hn j (by omega)]
  · rw [Vc_val hn j (by omega)]
    have h4 : Vc hn V (j + 1) = V (j' + 1) := by
      have h5 := Vc_add_one (V := V) hn j'
      rwa [hjv] at h5
    rw [h4]

lemma Vc_n : Vc hn V n = V 0 := congrArg V (Fin.ext (Nat.mod_self n))

include hinj hcopl hconv hn hplane in
/-- **Interior angle sum of a convex polygon** (used in Part 1 of the proof).
Proved by fan triangulation from `V 0`: the `n - 2` triangles
`(V 0, V (k+1), V (k+2))` each contribute `π`; the angles at `V 0` telescope
(`angle_telescope` with `fan_cone_Vc`), and the interior angle at every
non-boundary vertex splits along the diagonal (`corner_split`). -/
lemma interior_angle_sum :
    ∑ i : Fin n, angle (V (i - 1) - V i) (V (i + 1) - V i) = ((n : ℝ) - 2) * π := by
  -- conversion of the `Fin n` sum into a range sum of circular angles
  have hrange : ∑ i : Fin n, angle (V (i - 1) - V i) (V (i + 1) - V i) =
      ∑ i ∈ Finset.range n,
        angle (Vc hn V (i + n - 1) - Vc hn V i) (Vc hn V (i + 1) - Vc hn V i) := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    exact (theta_eq hn i).symm
  -- (A) peel off the boundary terms of the range sum
  have hA : ∑ i ∈ Finset.range n,
        angle (Vc hn V (i + n - 1) - Vc hn V i) (Vc hn V (i + 1) - Vc hn V i) =
      angle (Vc hn V (n - 1) - V 0) (Vc hn V 1 - V 0) +
        (angle (V 0 - Vc hn V 1) (Vc hn V 2 - Vc hn V 1) +
          (∑ k ∈ Finset.range (n - 3),
              angle (Vc hn V (k + 2 + n - 1) - Vc hn V (k + 2))
                (Vc hn V (k + 3) - Vc hn V (k + 2)) +
            angle (Vc hn V (n - 2) - Vc hn V (n - 1)) (V 0 - Vc hn V (n - 1)))) := by
    have hA1 := Finset.sum_range_succ'
      (fun i ↦ angle (Vc hn V (i + n - 1) - Vc hn V i) (Vc hn V (i + 1) - Vc hn V i)) (n - 1)
    rw [show (n - 1) + 1 = n from by omega] at hA1
    have hA2 := Finset.sum_range_succ'
      (fun i ↦ angle (Vc hn V (i + 1 + n - 1) - Vc hn V (i + 1))
        (Vc hn V (i + 1 + 1) - Vc hn V (i + 1))) (n - 2)
    rw [show (n - 2) + 1 = n - 1 from by omega] at hA2
    have hA3 := Finset.sum_range_succ
      (fun i ↦ angle (Vc hn V (i + 1 + 1 + n - 1) - Vc hn V (i + 1 + 1))
        (Vc hn V (i + 1 + 1 + 1) - Vc hn V (i + 1 + 1))) (n - 3)
    rw [show (n - 3) + 1 = n - 2 from by omega] at hA3
    rw [hA1, hA2, hA3]
    rw [show (∑ k ∈ Finset.range (n - 3), angle (Vc hn V (k + 1 + 1 + n - 1) - Vc hn V (k + 1 + 1))
          (Vc hn V (k + 1 + 1 + 1) - Vc hn V (k + 1 + 1))) =
        ∑ k ∈ Finset.range (n - 3), angle (Vc hn V (k + 2 + n - 1) - Vc hn V (k + 2))
          (Vc hn V (k + 3) - Vc hn V (k + 2)) from
      Finset.sum_congr rfl (fun k _ ↦ rfl)]
    rw [show angle (Vc hn V (0 + n - 1) - Vc hn V 0) (Vc hn V (0 + 1) - Vc hn V 0) =
        angle (Vc hn V (n - 1) - V 0) (Vc hn V 1 - V 0) from by
      rw [show (0 : ℕ) + n - 1 = n - 1 from by omega, show (0 : ℕ) + 1 = 1 from rfl, Vc_zero]]
    rw [show angle (Vc hn V (0 + 1 + n - 1) - Vc hn V (0 + 1))
          (Vc hn V (0 + 1 + 1) - Vc hn V (0 + 1)) =
        angle (V 0 - Vc hn V 1) (Vc hn V 2 - Vc hn V 1) from by
      rw [show (0 : ℕ) + 1 = 1 from rfl, show (0 : ℕ) + 1 + 1 = 2 from rfl,
        show 1 + n - 1 = n from by omega, Vc_n]]
    rw [show angle (Vc hn V (n - 2 + 1 + n - 1) - Vc hn V (n - 2 + 1))
          (Vc hn V (n - 2 + 1 + 1) - Vc hn V (n - 2 + 1)) =
        angle (Vc hn V (n - 2) - Vc hn V (n - 1)) (V 0 - Vc hn V (n - 1)) from by
      have h2 : n - 2 + 1 + n - 1 = 2 * n - 2 := by omega
      have h3 : (2 * n - 2) % n = (n - 2) % n := by
        rw [show 2 * n - 2 = n + (n - 2) from by omega, add_comm n (n - 2),
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : n - 2 < n)]
      rw [h2, show Vc hn V (2 * n - 2) = Vc hn V (n - 2) from congrArg V (Fin.ext h3),
        show (n - 2) + 1 + 1 = n from by omega, Vc_n,
        show (n - 2) + 1 = n - 1 from by omega]]
    abel
  -- (B) the corner split, summed over the middle vertices
  have hB : ∑ k ∈ Finset.range (n - 3),
        angle (Vc hn V (k + 2 + n - 1) - Vc hn V (k + 2)) (Vc hn V (k + 3) - Vc hn V (k + 2)) =
      (∑ k ∈ Finset.range (n - 3), angle (Vc hn V (k + 1) - Vc hn V (k + 2)) (V 0 - Vc hn V (k + 2))) +
      (∑ k ∈ Finset.range (n - 3), angle (V 0 - Vc hn V (k + 2)) (Vc hn V (k + 3) - Vc hn V (k + 2))) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    exact corner_split hinj hconv hn hplane (k + 2) (by omega) (by omega)
  -- (T) the telescope at `V 0`
  have hT : ∑ k ∈ Finset.range (n - 2), angle (Vc hn V (k + 1) - V 0) (Vc hn V (k + 2) - V 0) =
      angle (Vc hn V (n - 1) - V 0) (Vc hn V 1 - V 0) := by
    have h1 := angle_telescope hn (u := fun k ↦ Vc hn V k - V 0)
      (fun k hk1 hk2 ↦ fan_cone_Vc hinj hconv hn hplane k hk1 hk2)
      (fun k hk1 hk2 ↦ fan_ne_Vc hinj hn k hk1 hk2) (n - 2) (by omega)
    rw [show (n - 2) + 1 = n - 1 from by omega, angle_comm] at h1
    exact h1
  -- (F) the fan sum equals `(n - 2)π`
  have hF : (∑ k ∈ Finset.range (n - 2), angle (Vc hn V (k + 1) - V 0) (Vc hn V (k + 2) - V 0)) +
      (∑ k ∈ Finset.range (n - 2), angle (V 0 - Vc hn V (k + 1)) (Vc hn V (k + 2) - Vc hn V (k + 1))) +
      (∑ k ∈ Finset.range (n - 2), angle (Vc hn V (k + 1) - Vc hn V (k + 2)) (V 0 - Vc hn V (k + 2))) =
      ((n : ℝ) - 2) * π := by
    have h1 : ∀ k ∈ Finset.range (n - 2), angle (Vc hn V (k + 1) - V 0) (Vc hn V (k + 2) - V 0) +
        angle (V 0 - Vc hn V (k + 1)) (Vc hn V (k + 2) - Vc hn V (k + 1)) +
          angle (Vc hn V (k + 1) - Vc hn V (k + 2)) (V 0 - Vc hn V (k + 2)) = π := by
      intro k hk
      rw [Finset.mem_range] at hk
      exact fan_triangle_sum hinj hn k (by omega)
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.sum_congr rfl h1,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_sub (by omega : 2 ≤ n),
      Nat.cast_two]
  -- shifts
  have hS2 : ∑ k ∈ Finset.range (n - 2), angle (V 0 - Vc hn V (k + 1)) (Vc hn V (k + 2) - Vc hn V (k + 1)) =
      angle (V 0 - Vc hn V 1) (Vc hn V 2 - Vc hn V 1) +
        ∑ k ∈ Finset.range (n - 3), angle (V 0 - Vc hn V (k + 2)) (Vc hn V (k + 3) - Vc hn V (k + 2)) := by
    have h1 := Finset.sum_range_succ'
      (fun k ↦ angle (V 0 - Vc hn V (k + 1)) (Vc hn V (k + 2) - Vc hn V (k + 1))) (n - 3)
    rw [show (n - 3) + 1 = n - 2 from by omega] at h1
    rw [h1, add_comm]
  have hS3 : ∑ k ∈ Finset.range (n - 2), angle (Vc hn V (k + 1) - Vc hn V (k + 2)) (V 0 - Vc hn V (k + 2)) =
      (∑ k ∈ Finset.range (n - 3), angle (Vc hn V (k + 1) - Vc hn V (k + 2)) (V 0 - Vc hn V (k + 2))) +
        angle (Vc hn V (n - 2) - Vc hn V (n - 1)) (V 0 - Vc hn V (n - 1)) := by
    have h1 := Finset.sum_range_succ
      (fun k ↦ angle (Vc hn V (k + 1) - Vc hn V (k + 2)) (V 0 - Vc hn V (k + 2))) (n - 3)
    rw [show (n - 3) + 1 = n - 2 from by omega] at h1
    rw [h1]
    have h3 : (n - 3) + 2 = n - 1 := by omega
    rw [h3]
  -- assemble
  rw [hrange, hA, hB]
  linarith [hT, hF, hS2, hS3]

include hinj hconv hP hcopl hn hplane in
/-- **Part 1**: the sum of the angles subtended at `P` by the sides of the
polygon is strictly less than `2π`. -/
lemma sum_subAngle_lt :
    ∑ i : Fin n, angle (V i - P) (V (i + 1) - P) < 2 * π := by
  have h1 : ∀ i : Fin n, angle (V (i - 1) - V i) (V (i + 1) - V i) <
      angle (V (i - 1) - V i) (P - V i) + angle (P - V i) (V (i + 1) - V i) :=
    vertex_ineq hcopl hP hconv hn
  have hsum : ∑ i : Fin n, angle (V (i - 1) - V i) (V (i + 1) - V i) <
      ∑ i : Fin n, (angle (V (i - 1) - V i) (P - V i) +
        angle (P - V i) (V (i + 1) - V i)) :=
    Finset.sum_lt_sum (fun i _ ↦ (h1 i).le) ⟨0, Finset.mem_univ 0, h1 0⟩
  have hre : ∑ i : Fin n, angle (V (i - 1) - V i) (P - V i) =
      ∑ i : Fin n, angle (V i - V (i + 1)) (P - V (i + 1)) := by
    have h := Equiv.sum_comp (Equiv.addRight (1 : Fin n))
      (fun i ↦ angle (V (i - 1) - V i) (P - V i))
    simp only [Equiv.coe_addRight, add_sub_cancel_right] at h
    exact h.symm
  have h2 : ∑ i : Fin n, (angle (V (i - 1) - V i) (P - V i) +
        angle (P - V i) (V (i + 1) - V i)) =
      (n : ℝ) * π - ∑ i : Fin n, angle (V i - P) (V (i + 1) - P) := by
    rw [Finset.sum_add_distrib, hre, ← Finset.sum_add_distrib]
    have h3 : ∀ i ∈ Finset.univ, angle (V i - V (i + 1)) (P - V (i + 1)) +
          angle (P - V i) (V (i + 1) - V i) =
        π - angle (V i - P) (V (i + 1) - P) := fun i _ ↦ by
      have ht := tri_sum (P := P) hinj hn i
      rw [angle_comm (V (i + 1) - V i) (P - V i),
        angle_comm (P - V (i + 1)) (V i - V (i + 1))] at ht
      linarith
    rw [Finset.sum_congr rfl h3, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  rw [interior_angle_sum hinj hcopl hconv hn hplane, h2] at hsum
  linarith

lemma dproj_smul_left (u v : E) (c : ℝ) (hc : c ≠ 0) : dproj (c • u) v = dproj u v := by
  simp only [dproj, real_inner_smul_left, real_inner_smul_right]
  rw [smul_smul]
  have h : (c * ⟪u, v⟫ / (c * (c * ⟪u, u⟫))) * c = ⟪u, v⟫ / ⟪u, u⟫ := by
    by_cases hu : ⟪u, u⟫ = 0
    · rw [hu]; simp
    · field_simp [hc, hu]
  rw [h]

/-- The dihedral angle is invariant under normalization of all three
directions. This bridges `planeAngle` (arbitrary vectors from `P`) and the
unit-vector formulation of `dihedral_sum_gt_pi`. -/
lemma planeAngle_normalize (B A C : E) (hB : B - P ≠ 0) (hA : A - P ≠ 0) (hC : C - P ≠ 0) :
    planeAngle P B A C = angle (dproj (NormedSpace.normalize (B - P)) (NormedSpace.normalize (A - P)))
      (dproj (NormedSpace.normalize (B - P)) (NormedSpace.normalize (C - P))) := by
  have hB' : ‖B - P‖⁻¹ ≠ 0 := inv_ne_zero (norm_ne_zero_iff.mpr hB)
  have hA' : 0 < ‖A - P‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hA)
  have hC' : 0 < ‖C - P‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hC)
  rw [planeAngle]
  simp only [NormedSpace.normalize]
  rw [dproj_smul_left (B - P) _ ‖B - P‖⁻¹ hB', dproj_smul_left (B - P) _ ‖B - P‖⁻¹ hB',
    dproj_smul, dproj_smul, angle_smul_left_of_pos _ _ hA', angle_smul_right_of_pos _ _ hC']

include hcopl hP in
lemma vertex_ne_P' (i : Fin n) : V i - P ≠ 0 := vertex_ne_P hcopl hP i

include hcopl hP hn in
lemma vertex_ne_P_c (j : ℕ) (hj : j < n) : Vc hn V j - P ≠ 0 := by
  rw [Vc_val hn j hj]; exact vertex_ne_P hcopl hP ⟨j, hj⟩

include hinj hcopl hP hn in
/-- The rays from `P` to distinct vertices are not parallel. -/
lemma ray_ne (j : ℕ) (hj : 1 ≤ j) (hj2 : j ≤ n - 1) :
    ¬∃ t : ℝ, Vc hn V j - P = t • (V 0 - P) := by
  rintro ⟨t, ht⟩
  have hc0 : ⟪m, V 0 - P⟫ ≠ 0 := by
    rw [inner_sub_right, sub_ne_zero]; exact hP.symm
  have h2 : ⟪m, Vc hn V j - P⟫ = ⟪m, V 0 - P⟫ := by
    rw [inner_sub_right, inner_sub_right, Vc_val hn j (by omega : j < n), hcopl ⟨j, by omega⟩]
  have h3 : ⟪m, Vc hn V j - P⟫ = t * ⟪m, V 0 - P⟫ := by rw [ht, real_inner_smul_right]
  rw [h2] at h3
  have ht1 : t = 1 :=
    mul_right_cancel₀ hc0 (show t * ⟪m, V 0 - P⟫ = 1 * ⟪m, V 0 - P⟫ from by
      rw [one_mul]; exact h3.symm)
  rw [ht1, one_smul] at ht
  have h4 : Vc hn V j = V 0 := by
    have h5 := congrArg (· + P) ht
    simpa using h5
  rw [Vc_val hn j (by omega : j < n)] at h4
  have h6 : (⟨j, by omega⟩ : Fin n) = 0 := hinj h4
  have hv : j = 0 := congrArg Fin.val h6
  omega

include hinj hcopl hP hn in
/-- The rays from `P` to distinct vertices make an angle in the open interval
`(0, π)`, i.e. `|⟪a, b⟫| < 1` for the normalized rays. -/
lemma ray_inner_abs_lt_one (j : ℕ) (hj : 1 ≤ j) (hj2 : j ≤ n - 1) :
    |⟪NormedSpace.normalize (V 0 - P), NormedSpace.normalize (Vc hn V j - P)⟫| < 1 := by
  have hne0 : V 0 - P ≠ 0 := vertex_ne_P hcopl hP 0
  have hnej : Vc hn V j - P ≠ 0 := vertex_ne_P_c hcopl hP hn j (by omega)
  apply abs_inner_lt_one_of_ne (NormedSpace.norm_normalize_eq_one_iff.mpr hne0)
    (NormedSpace.norm_normalize_eq_one_iff.mpr hnej)
  · intro h
    apply ray_ne hinj hcopl hP hn j hj hj2
    simp only [NormedSpace.normalize] at h
    exact ⟨‖Vc hn V j - P‖ * ‖V 0 - P‖⁻¹, by
      rw [← smul_smul, ← h, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hnej), one_smul]⟩
  · intro h
    apply ray_ne hinj hcopl hP hn j hj hj2
    simp only [NormedSpace.normalize] at h
    have h2' : ‖V 0 - P‖⁻¹ • (V 0 - P) = -(‖Vc hn V j - P‖⁻¹ • (Vc hn V j - P)) := by
      have hs := h.symm
      rw [← neg_neg (‖V 0 - P‖⁻¹ • (V 0 - P)), hs]
    refine ⟨-(‖Vc hn V j - P‖ * ‖V 0 - P‖⁻¹), ?_⟩
    rw [show -(‖Vc hn V j - P‖ * ‖V 0 - P‖⁻¹) • (V 0 - P) =
        (-‖Vc hn V j - P‖) • (‖V 0 - P‖⁻¹ • (V 0 - P)) from by
      rw [show -(‖Vc hn V j - P‖ * ‖V 0 - P‖⁻¹) = (-‖Vc hn V j - P‖) * ‖V 0 - P‖⁻¹ from by ring,
        smul_smul]]
    rw [h2', neg_smul_neg, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hnej), one_smul]

include hinj hcopl hP hconv hn hplane in
/-- The ray to `Vc (k+2)` is not in the plane spanned by the rays to `V 0`
and `Vc (k+1)` (equivalently, `V 0, V (k+1), V (k+2)` are not collinear). -/
lemma ray_not_mem_span (k : ℕ) (hk : k ≤ n - 3) :
    NormedSpace.normalize (Vc hn V (k + 2) - P) ∉
      Submodule.span ℝ {NormedSpace.normalize (V 0 - P), NormedSpace.normalize (Vc hn V (k + 1) - P)} := by
  intro hmem
  have hne0 : V 0 - P ≠ 0 := vertex_ne_P hcopl hP 0
  have hne2 : Vc hn V (k + 2) - P ≠ 0 := vertex_ne_P_c hcopl hP hn (k + 2) (by omega)
  have h1 : Vc hn V (k + 2) - P ∈ Submodule.span ℝ {V 0 - P, Vc hn V (k + 1) - P} := by
    have hle : Submodule.span ℝ {NormedSpace.normalize (V 0 - P), NormedSpace.normalize (Vc hn V (k + 1) - P)} ≤
        Submodule.span ℝ {V 0 - P, Vc hn V (k + 1) - P} := by
      rw [Submodule.span_le, Set.pair_subset_iff]
      constructor
      · simp only [NormedSpace.normalize]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
      · simp only [NormedSpace.normalize]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    have h2 : Vc hn V (k + 2) - P = ‖Vc hn V (k + 2) - P‖ • NormedSpace.normalize (Vc hn V (k + 2) - P) :=
      (NormedSpace.norm_smul_normalize (Vc hn V (k + 2) - P)).symm
    rw [h2]
    exact Submodule.smul_mem _ _ (hle hmem)
  rw [Submodule.mem_span_pair] at h1
  obtain ⟨a, b, hab⟩ := h1
  have hc0 : ⟪m, V 0 - P⟫ ≠ 0 := by
    rw [inner_sub_right, sub_ne_zero]; exact hP.symm
  have h2 : ⟪m, Vc hn V (k + 2) - P⟫ = a * ⟪m, V 0 - P⟫ + b * ⟪m, Vc hn V (k + 1) - P⟫ := by
    rw [← hab, inner_add_right, real_inner_smul_right, real_inner_smul_right]
  have h3 : ⟪m, Vc hn V (k + 2) - P⟫ = ⟪m, V 0 - P⟫ := by
    rw [inner_sub_right, inner_sub_right, Vc_val hn (k + 2) (by omega), hcopl ⟨k + 2, by omega⟩]
  have h4 : ⟪m, Vc hn V (k + 1) - P⟫ = ⟪m, V 0 - P⟫ := by
    rw [inner_sub_right, inner_sub_right, Vc_val hn (k + 1) (by omega), hcopl ⟨k + 1, by omega⟩]
  rw [h3, h4] at h2
  have hab1 : a + b = 1 := by
    have h5 : ⟪m, V 0 - P⟫ * (a + b) = ⟪m, V 0 - P⟫ := by linarith [h2]
    exact (mul_eq_left₀ hc0).mp h5
  have h6 : Vc hn V (k + 2) - V 0 = b • (Vc hn V (k + 1) - V 0) := by
    rw [show Vc hn V (k + 2) - V 0 = (Vc hn V (k + 2) - P) + (P - V 0) from by abel, ← hab]
    have ha : a = 1 - b := by linarith [hab1]
    rw [ha, sub_smul, one_smul]
    rw [show b • (Vc hn V (k + 1) - V 0) = b • (Vc hn V (k + 1) - P) - b • (V 0 - P) from by
      rw [show Vc hn V (k + 1) - V 0 = (Vc hn V (k + 1) - P) - (V 0 - P) from by abel, smul_sub]]
    abel
  have hk1 : k + 1 < n := by omega
  have hk2 : k + 2 < n := by omega
  obtain ⟨f, hf, -, hfpos⟩ := hconv ⟨k + 1, hk1⟩
  have h8 : f (Vc hn V (k + 2) - Vc hn V (k + 1)) = 0 := by
    rw [Vc_val hn (k + 2) hk2, Vc_val hn (k + 1) hk1]
    have h9 : (⟨k + 1, hk1⟩ : Fin n) + 1 = ⟨k + 2, hk2⟩ := by
      apply Fin.ext
      rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < n),
        Nat.mod_eq_of_lt hk2]
    rw [h9] at hf
    exact hf
  have h9 : f (Vc hn V (k + 1) - V 0) ≠ 0 := by
    have h10 : 0 < f (V 0 - Vc hn V (k + 1)) := by
      rw [Vc_val hn (k + 1) hk1]
      apply hfpos 0
      · apply Fin.ne_of_val_ne
        rw [Fin.val_mk hk1, show ((0 : Fin n) : ℕ) = 0 % n from rfl, Nat.zero_mod]
        omega
      · apply Fin.ne_of_val_ne
        rw [fin_val_add_one (⟨k + 1, hk1⟩ : Fin n) (by omega), Fin.val_mk hk1,
          show ((0 : Fin n) : ℕ) = 0 % n from rfl, Nat.zero_mod]
        omega
    rw [show Vc hn V (k + 1) - V 0 = -(V 0 - Vc hn V (k + 1)) from by abel, map_neg]
    exact neg_ne_zero.mpr (ne_of_gt h10)
  have h11 : f (Vc hn V (k + 2) - V 0) = f (Vc hn V (k + 1) - V 0) := by
    rw [show Vc hn V (k + 2) - V 0 = (Vc hn V (k + 2) - Vc hn V (k + 1)) + (Vc hn V (k + 1) - V 0) from by abel,
      map_add, h8, zero_add]
  have h12 : f (Vc hn V (k + 2) - V 0) = b * f (Vc hn V (k + 1) - V 0) := by
    rw [h6, map_smul, smul_eq_mul]
  rw [h11] at h12
  have hb1 : b = 1 := (mul_eq_right₀ h9).mp h12.symm
  rw [hb1, one_smul] at h6
  have h13 : Vc hn V (k + 2) = Vc hn V (k + 1) := by
    have h14 := congrArg (· + V 0) h6
    rwa [sub_add_cancel, sub_add_cancel] at h14
  rw [Vc_val hn (k + 2) hk2, Vc_val hn (k + 1) hk1] at h13
  have h15 := hinj h13
  have hv : k + 2 = k + 1 := congrArg Fin.val h15
  omega

include hinj hcopl hP hconv hn hplane in
/-- **Trihedral excess at each fan triangle**: the three dihedral angles of
the trihedral angle at `P` over `(V 0, V (k+1), V (k+2))` sum to more than `π`. -/
lemma fan_trihedral_gt_pi (k : ℕ) (hk : k ≤ n - 3) :
    π < planeAngle P (V 0) (Vc hn V (k + 1)) (Vc hn V (k + 2)) +
      planeAngle P (Vc hn V (k + 1)) (V 0) (Vc hn V (k + 2)) +
        planeAngle P (Vc hn V (k + 2)) (V 0) (Vc hn V (k + 1)) := by
  have hne0 : V 0 - P ≠ 0 := vertex_ne_P hcopl hP 0
  have hne1 : Vc hn V (k + 1) - P ≠ 0 := vertex_ne_P_c hcopl hP hn (k + 1) (by omega)
  have hne2 : Vc hn V (k + 2) - P ≠ 0 := vertex_ne_P_c hcopl hP hn (k + 2) (by omega)
  rw [planeAngle_normalize (V 0) (Vc hn V (k + 1)) (Vc hn V (k + 2)) hne0 hne1 hne2,
    planeAngle_normalize (Vc hn V (k + 1)) (V 0) (Vc hn V (k + 2)) hne1 hne0 hne2,
    planeAngle_normalize (Vc hn V (k + 2)) (V 0) (Vc hn V (k + 1)) hne2 hne0 hne1]
  exact dihedral_sum_gt_pi (NormedSpace.norm_normalize_eq_one_iff.mpr hne0)
    (NormedSpace.norm_normalize_eq_one_iff.mpr hne1) (NormedSpace.norm_normalize_eq_one_iff.mpr hne2)
    (ray_inner_abs_lt_one hinj hcopl hP hn (k + 1) (by omega) (by omega))
    (ray_not_mem_span hinj hcopl hP hconv hn hplane k hk)

lemma dproj_sub (u v w : E) : dproj u (v - w) = dproj u v - dproj u w := by
  simp only [dproj, inner_sub_right, sub_div, sub_smul]
  abel

lemma planeAngle_comm (P B A C : E) : planeAngle P B A C = planeAngle P B C A :=
  angle_comm _ _

lemma dproj_vertex_P (j : ℕ) :
    dproj (V 0 - P) (Vc hn V j - P) = dproj (V 0 - P) (Vc hn V j - V 0) := by
  rw [show Vc hn V j - P = (Vc hn V j - V 0) + (V 0 - P) from by abel, dproj_add,
    dproj_self, add_zero]

lemma dproj_vertex_P_at (j : ℕ) (x : E) :
    dproj (Vc hn V j - P) (x - P) = dproj (Vc hn V j - P) (x - Vc hn V j) := by
  rw [show x - P = (x - Vc hn V j) + (Vc hn V j - P) from by abel, dproj_add,
    dproj_self, add_zero]

lemma dproj_vertex_P_sub (i : Fin n) (x : E) :
    dproj (V i - P) (x - V i) = dproj (V i - P) (x - P) := by
  rw [show x - V i = (x - P) - (V i - P) from by abel, dproj_sub, dproj_self, sub_zero]

/-- Conversion between the `Fin n`-indexed and the circular `ℕ`-indexed
dihedral angle at edge `PV j`. -/
lemma delta_eq (j : Fin n) :
    planeAngle P (Vc hn V j.val) (Vc hn V (j.val + n - 1)) (Vc hn V (j.val + 1)) =
      planeAngle P (V j) (V (j - 1)) (V (j + 1)) := by
  rw [Vc_sub_one hn j, Vc_add_one hn j, Vc_val hn j.val j.isLt]

include hinj hcopl hP hconv hn hplane in
/-- The cone hypothesis of `angle_telescope` for the projected rays from `PV 0`. -/
lemma fan_cone_dproj (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ n - 2) :
    dproj (V 0 - P) (Vc hn V k - V 0) ∈
      Submodule.span ℝ≥0 {dproj (V 0 - P) (Vc hn V 1 - V 0),
        dproj (V 0 - P) (Vc hn V (k + 1) - V 0)} := by
  have h := fan_cone_Vc hinj hconv hn hplane k hk1 hk2
  rw [Submodule.mem_span_pair] at h
  obtain ⟨a, b, hab⟩ := h
  rw [Submodule.mem_span_pair]
  refine ⟨a, b, ?_⟩
  have h2 := congrArg (dproj (V 0 - P)) hab
  simp only [NNReal.smul_def, dproj_add, dproj_smul] at h2
  exact h2

include hinj hcopl hP hn in
/-- The projected rays from `PV 0` are nonzero. -/
lemma fan_ne_dproj (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ n - 2) :
    dproj (V 0 - P) (Vc hn V k - V 0) ≠ 0 := by
  intro h0
  rw [dproj_eq_zero_iff (V 0 - P) (Vc hn V k - V 0) (vertex_ne_P hcopl hP 0)] at h0
  obtain ⟨r, hr⟩ := h0
  have hc0 : ⟪m, V 0 - P⟫ ≠ 0 := by
    rw [inner_sub_right, sub_ne_zero]; exact hP.symm
  have h1 : ⟪m, Vc hn V k - V 0⟫ = r * ⟪m, V 0 - P⟫ := by rw [hr, real_inner_smul_right]
  have h2 : ⟪m, Vc hn V k - V 0⟫ = 0 := by
    rw [Vc_val hn k (by omega : k < n)]
    exact inner_sub_vertex hcopl 0 ⟨k, by omega⟩
  rw [h2] at h1
  have hr0 : r = 0 := by
    have h3 : r * ⟪m, V 0 - P⟫ = 0 := by rw [h1]
    exact (mul_eq_zero.mp h3).resolve_right hc0
  rw [hr0, zero_smul] at hr
  have h4 : Vc hn V k = V 0 := by
    have h5 := congrArg (· + V 0) hr
    rwa [sub_add_cancel, zero_add] at h5
  rw [Vc_val hn k (by omega : k < n)] at h4
  have h6 : (⟨k, by omega⟩ : Fin n) = 0 := hinj h4
  have hv : k = 0 := congrArg Fin.val h6
  omega

include hinj hconv hP hcopl hn hplane in
/-- **Dihedral split**: the dihedral angle at edge `PV j` (`2 ≤ j ≤ n - 2`)
splits along the plane through the diagonal to `V 0`. -/
lemma delta_split (j : ℕ) (hj1 : 2 ≤ j) (hj2 : j ≤ n - 2) :
    planeAngle P (Vc hn V j) (Vc hn V (j + n - 1)) (Vc hn V (j + 1)) =
      planeAngle P (Vc hn V j) (V 0) (Vc hn V (j - 1)) +
        planeAngle P (Vc hn V j) (V 0) (Vc hn V (j + 1)) := by
  set j' : Fin n := ⟨j, by omega⟩ with hj'def
  have hjv : j'.val = j := rfl
  have h1 : planeAngle P (Vc hn V j) (Vc hn V (j + n - 1)) (Vc hn V (j + 1)) =
      planeAngle P (V j') (V (j' - 1)) (V (j' + 1)) := by
    have h2 := delta_eq (P := P) (V := V) hn j'
    rwa [hjv] at h2
  have hne : dproj (V j' - P) (V 0 - P) ≠ 0 := by
    intro h0
    rw [dproj_eq_zero_iff (V j' - P) (V 0 - P) (vertex_ne_P hcopl hP j')] at h0
    obtain ⟨r, hr⟩ := h0
    have hc0 : ⟪m, V 0 - P⟫ ≠ 0 := by
      rw [inner_sub_right, sub_ne_zero]; exact hP.symm
    have h3 : ⟪m, V 0 - P⟫ = r * ⟪m, V j' - P⟫ := by rw [hr, real_inner_smul_right]
    have h4 : ⟪m, V j' - P⟫ = ⟪m, V 0 - P⟫ := by
      rw [inner_sub_right, inner_sub_right, hcopl j']
    rw [h4] at h3
    have hr1 : r = 1 :=
      mul_right_cancel₀ hc0 (show r * ⟪m, V 0 - P⟫ = 1 * ⟪m, V 0 - P⟫ from by
        rw [one_mul]; exact h3.symm)
    rw [hr1, one_smul] at hr
    have h5 : V 0 = V j' := by
      have h6 := congrArg (· + P) hr
      rwa [sub_add_cancel, sub_add_cancel] at h6
    have h7 : (0 : Fin n) ≠ j' := by
      intro hh
      have hv := congrArg Fin.val hh
      rw [show ((0 : Fin n) : ℕ) = 0 % n from rfl, Nat.zero_mod, hjv] at hv
      omega
    exact h7 (hinj h5)
  have hsplit : angle (dproj (V j' - P) (V (j' - 1) - P)) (dproj (V j' - P) (V (j' + 1) - P)) =
      angle (dproj (V j' - P) (V (j' - 1) - P)) (dproj (V j' - P) (V 0 - P)) +
        angle (dproj (V j' - P) (V 0 - P)) (dproj (V j' - P) (V (j' + 1) - P)) := by
    apply angle_eq_angle_add_add_angle_add_of_mem_span hne
    have h8 := corner_cone hinj hconv hn hplane j' 0
    rw [Submodule.mem_span_pair] at h8
    obtain ⟨a, b, hab⟩ := h8
    rw [Submodule.mem_span_pair]
    refine ⟨a, b, ?_⟩
    have h9 := congrArg (dproj (V j' - P)) hab
    simp only [NNReal.smul_def, dproj_add, dproj_smul, dproj_vertex_P_sub] at h9
    exact h9
  rw [h1]
  have h10 : planeAngle P (Vc hn V j) (V 0) (Vc hn V (j - 1)) =
      angle (dproj (V j' - P) (V 0 - P)) (dproj (V j' - P) (V (j' - 1) - P)) := by
    rw [planeAngle]
    have hA : Vc hn V j = V j' := Vc_val hn j (by omega)
    have hB : Vc hn V (j - 1) = V (j' - 1) := by
      rw [Vc_val hn (j - 1) (by omega)]
      congr 1
      apply Fin.ext
      rw [fin_val_sub_one j' (by omega), hjv]
    rw [hA, hB]
  have h11 : planeAngle P (Vc hn V j) (V 0) (Vc hn V (j + 1)) =
      angle (dproj (V j' - P) (V 0 - P)) (dproj (V j' - P) (V (j' + 1) - P)) := by
    rw [planeAngle]
    have hA : Vc hn V j = V j' := Vc_val hn j (by omega)
    have hB : Vc hn V (j + 1) = V (j' + 1) := by
      have h5 := Vc_add_one (V := V) hn j'
      rwa [hjv] at h5
    rw [hA, hB]
  rw [h10, h11]
  have h12 : planeAngle P (V j') (V (j' - 1)) (V (j' + 1)) =
      angle (dproj (V j' - P) (V (j' - 1) - P)) (dproj (V j' - P) (V (j' + 1) - P)) := by
    rw [planeAngle]
  rw [h12, hsplit, angle_comm (dproj (V j' - P) (V (j' - 1) - P)) (dproj (V j' - P) (V 0 - P))]

include hinj hcopl hP hconv hn hplane in
/-- **Part 2**: the sum of the dihedral angles along the edges `PV i` is
strictly greater than `(n - 2)π`. Proved by the same fan triangulation as
`interior_angle_sum`: each trihedral angle at `P` over a fan triangle has
dihedral sum `> π` (`fan_trihedral_gt_pi`); the dihedrals along `PV 0`
telescope (`angle_telescope` on the projected rays), and the dihedral angle
at every non-boundary edge splits along the diagonal plane (`delta_split`). -/
lemma sum_planeAngle_gt :
    ((n : ℝ) - 2) * π < ∑ i : Fin n, planeAngle P (V i) (V (i - 1)) (V (i + 1)) := by
  -- conversion of the `Fin n` sum into a range sum of circular dihedral angles
  have hrange : ∑ i : Fin n, planeAngle P (V i) (V (i - 1)) (V (i + 1)) =
      ∑ i ∈ Finset.range n, planeAngle P (Vc hn V i) (Vc hn V (i + n - 1)) (Vc hn V (i + 1)) := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    exact (delta_eq (P := P) (V := V) hn i).symm
  -- (A) peel off the boundary terms of the range sum
  have hA : ∑ i ∈ Finset.range n,
        planeAngle P (Vc hn V i) (Vc hn V (i + n - 1)) (Vc hn V (i + 1)) =
      planeAngle P (V 0) (Vc hn V (n - 1)) (Vc hn V 1) +
        (planeAngle P (Vc hn V 1) (V 0) (Vc hn V 2) +
          (∑ k ∈ Finset.range (n - 3),
              planeAngle P (Vc hn V (k + 2)) (Vc hn V (k + 2 + n - 1)) (Vc hn V (k + 3)) +
            planeAngle P (Vc hn V (n - 1)) (Vc hn V (n - 2)) (V 0))) := by
    have hA1 := Finset.sum_range_succ'
      (fun i ↦ planeAngle P (Vc hn V i) (Vc hn V (i + n - 1)) (Vc hn V (i + 1))) (n - 1)
    rw [show (n - 1) + 1 = n from by omega] at hA1
    have hA2 := Finset.sum_range_succ'
      (fun i ↦ planeAngle P (Vc hn V (i + 1)) (Vc hn V (i + 1 + n - 1)) (Vc hn V (i + 1 + 1))) (n - 2)
    rw [show (n - 2) + 1 = n - 1 from by omega] at hA2
    have hA3 := Finset.sum_range_succ
      (fun i ↦ planeAngle P (Vc hn V (i + 1 + 1)) (Vc hn V (i + 1 + 1 + n - 1))
        (Vc hn V (i + 1 + 1 + 1))) (n - 3)
    rw [show (n - 3) + 1 = n - 2 from by omega] at hA3
    rw [hA1, hA2, hA3]
    rw [show (∑ k ∈ Finset.range (n - 3), planeAngle P (Vc hn V (k + 1 + 1))
          (Vc hn V (k + 1 + 1 + n - 1)) (Vc hn V (k + 1 + 1 + 1))) =
        ∑ k ∈ Finset.range (n - 3), planeAngle P (Vc hn V (k + 2))
          (Vc hn V (k + 2 + n - 1)) (Vc hn V (k + 3)) from
      Finset.sum_congr rfl (fun k _ ↦ rfl)]
    rw [show planeAngle P (Vc hn V 0) (Vc hn V (0 + n - 1)) (Vc hn V (0 + 1)) =
        planeAngle P (V 0) (Vc hn V (n - 1)) (Vc hn V 1) from by
      rw [show (0 : ℕ) + n - 1 = n - 1 from by omega, show (0 : ℕ) + 1 = 1 from rfl, Vc_zero]]
    rw [show planeAngle P (Vc hn V (0 + 1)) (Vc hn V (0 + 1 + n - 1)) (Vc hn V (0 + 1 + 1)) =
        planeAngle P (Vc hn V 1) (V 0) (Vc hn V 2) from by
      rw [show (0 : ℕ) + 1 = 1 from rfl, show (0 : ℕ) + 1 + 1 = 2 from rfl,
        show 1 + n - 1 = n from by omega, Vc_n]]
    rw [show planeAngle P (Vc hn V (n - 2 + 1)) (Vc hn V (n - 2 + 1 + n - 1))
          (Vc hn V (n - 2 + 1 + 1)) =
        planeAngle P (Vc hn V (n - 1)) (Vc hn V (n - 2)) (V 0) from by
      have h2 : n - 2 + 1 + n - 1 = 2 * n - 2 := by omega
      have h3 : (2 * n - 2) % n = (n - 2) % n := by
        rw [show 2 * n - 2 = n + (n - 2) from by omega, add_comm n (n - 2),
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : n - 2 < n)]
      rw [h2, show Vc hn V (2 * n - 2) = Vc hn V (n - 2) from congrArg V (Fin.ext h3),
        show (n - 2) + 1 + 1 = n from by omega, Vc_n,
        show (n - 2) + 1 = n - 1 from by omega]]
    abel
  -- (B) the dihedral split, summed over the middle edges
  have hB : ∑ k ∈ Finset.range (n - 3),
        planeAngle P (Vc hn V (k + 2)) (Vc hn V (k + 2 + n - 1)) (Vc hn V (k + 3)) =
      (∑ k ∈ Finset.range (n - 3), planeAngle P (Vc hn V (k + 2)) (V 0) (Vc hn V (k + 1))) +
      (∑ k ∈ Finset.range (n - 3), planeAngle P (Vc hn V (k + 2)) (V 0) (Vc hn V (k + 3))) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    exact delta_split hinj hcopl hP hconv hn hplane (k + 2) (by omega) (by omega)
  -- (T) the telescope at `PV 0`
  have hT : ∑ k ∈ Finset.range (n - 2), planeAngle P (V 0) (Vc hn V (k + 1)) (Vc hn V (k + 2)) =
      planeAngle P (V 0) (Vc hn V (n - 1)) (Vc hn V 1) := by
    have h1 := angle_telescope hn (u := fun k ↦ dproj (V 0 - P) (Vc hn V k - V 0))
      (fun k hk1 hk2 ↦ fan_cone_dproj hinj hcopl hP hconv hn hplane k hk1 hk2)
      (fun k hk1 hk2 ↦ fan_ne_dproj hinj hcopl hP hn k hk1 hk2) (n - 2) (by omega)
    have h2 : ∀ k, planeAngle P (V 0) (Vc hn V (k + 1)) (Vc hn V (k + 2)) =
        angle (dproj (V 0 - P) (Vc hn V (k + 1) - V 0))
          (dproj (V 0 - P) (Vc hn V (k + 2) - V 0)) := by
      intro k
      rw [planeAngle, dproj_vertex_P, dproj_vertex_P]
    rw [show (∑ k ∈ Finset.range (n - 2), planeAngle P (V 0) (Vc hn V (k + 1)) (Vc hn V (k + 2))) =
        ∑ k ∈ Finset.range (n - 2), angle (dproj (V 0 - P) (Vc hn V (k + 1) - V 0))
          (dproj (V 0 - P) (Vc hn V (k + 2) - V 0)) from
      Finset.sum_congr rfl (fun k _ ↦ h2 k)]
    rw [show (n - 2) + 1 = n - 1 from by omega, angle_comm] at h1
    rw [h1]
    rw [show planeAngle P (V 0) (Vc hn V (n - 1)) (Vc hn V 1) =
        angle (dproj (V 0 - P) (Vc hn V (n - 1) - V 0)) (dproj (V 0 - P) (Vc hn V 1 - V 0)) from by
      rw [planeAngle, dproj_vertex_P, dproj_vertex_P]]
  -- (F) the fan sum is strictly greater than `(n - 2)π`
  have hF : ((n : ℝ) - 2) * π <
      (∑ k ∈ Finset.range (n - 2), planeAngle P (V 0) (Vc hn V (k + 1)) (Vc hn V (k + 2))) +
      (∑ k ∈ Finset.range (n - 2), planeAngle P (Vc hn V (k + 1)) (V 0) (Vc hn V (k + 2))) +
      (∑ k ∈ Finset.range (n - 2), planeAngle P (Vc hn V (k + 2)) (V 0) (Vc hn V (k + 1))) := by
    have h1 : ∀ k ∈ Finset.range (n - 2), π <
        planeAngle P (V 0) (Vc hn V (k + 1)) (Vc hn V (k + 2)) +
        planeAngle P (Vc hn V (k + 1)) (V 0) (Vc hn V (k + 2)) +
          planeAngle P (Vc hn V (k + 2)) (V 0) (Vc hn V (k + 1)) := by
      intro k hk
      rw [Finset.mem_range] at hk
      exact fan_trihedral_gt_pi hinj hcopl hP hconv hn hplane k (by omega)
    have h2 : ∑ k ∈ Finset.range (n - 2), (planeAngle P (V 0) (Vc hn V (k + 1)) (Vc hn V (k + 2)) +
        planeAngle P (Vc hn V (k + 1)) (V 0) (Vc hn V (k + 2)) +
          planeAngle P (Vc hn V (k + 2)) (V 0) (Vc hn V (k + 1))) =
      (∑ k ∈ Finset.range (n - 2), planeAngle P (V 0) (Vc hn V (k + 1)) (Vc hn V (k + 2))) +
      (∑ k ∈ Finset.range (n - 2), planeAngle P (Vc hn V (k + 1)) (V 0) (Vc hn V (k + 2))) +
      (∑ k ∈ Finset.range (n - 2), planeAngle P (Vc hn V (k + 2)) (V 0) (Vc hn V (k + 1))) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    rw [← h2]
    have h3 : ((n : ℝ) - 2) * π = ∑ k ∈ Finset.range (n - 2), π := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_sub (by omega : 2 ≤ n),
        Nat.cast_two]
    rw [h3]
    refine Finset.sum_lt_sum (fun k hk ↦ (h1 k hk).le) ⟨0, ?_, h1 0 (Finset.mem_range.mpr (by omega))⟩
    rw [Finset.mem_range]; omega
  -- shifts
  have hS2 : ∑ k ∈ Finset.range (n - 2), planeAngle P (Vc hn V (k + 1)) (V 0) (Vc hn V (k + 2)) =
      planeAngle P (Vc hn V 1) (V 0) (Vc hn V 2) +
        ∑ k ∈ Finset.range (n - 3), planeAngle P (Vc hn V (k + 2)) (V 0) (Vc hn V (k + 3)) := by
    have h1 := Finset.sum_range_succ'
      (fun k ↦ planeAngle P (Vc hn V (k + 1)) (V 0) (Vc hn V (k + 2))) (n - 3)
    rw [show (n - 3) + 1 = n - 2 from by omega] at h1
    rw [h1, add_comm]
  have hS3 : ∑ k ∈ Finset.range (n - 2), planeAngle P (Vc hn V (k + 2)) (V 0) (Vc hn V (k + 1)) =
      (∑ k ∈ Finset.range (n - 3), planeAngle P (Vc hn V (k + 2)) (V 0) (Vc hn V (k + 1))) +
        planeAngle P (Vc hn V (n - 1)) (Vc hn V (n - 2)) (V 0) := by
    have h1 := Finset.sum_range_succ
      (fun k ↦ planeAngle P (Vc hn V (k + 1 + 1)) (V 0) (Vc hn V (k + 1))) (n - 3)
    rw [show (n - 3) + 1 = n - 2 from by omega] at h1
    rw [h1]
    have h3 : (n - 2) + 1 = n - 1 := by omega
    rw [h3]
    rw [show (∑ x ∈ Finset.range (n - 3), planeAngle P (Vc hn V (x + 1 + 1)) (V 0) (Vc hn V (x + 1))) =
        ∑ k ∈ Finset.range (n - 3), planeAngle P (Vc hn V (k + 2)) (V 0) (Vc hn V (k + 1)) from
      Finset.sum_congr rfl (fun k _ ↦ rfl)]
    rw [planeAngle_comm P (Vc hn V (n - 1)) (V 0) (Vc hn V (n - 2))]
  -- assemble
  rw [hrange, hA, hB]
  linarith [hT, hF, hS2, hS3]

end PolygonFacts

/-!
## Proof notes

The proof is complete (no `sorry`). Structure of the argument
(kalva's classical solution, formalized):

* `dproj` API, `cos_dihedral`/`sin_dihedral` (dihedral cos/sin laws),
  `gramDet_nonneg`/`gramDet_pos` (Gram determinant of three unit vectors),
  and `dihedral_sum_gt_pi` — **spherical triangle excess**: the three dihedral
  angles of a nondegenerate trihedral angle sum to more than `π`. Proved by
  pure vector algebra: with `p = ⟪v,w⟫, q = ⟪u,w⟫, r = ⟪u,v⟫` one has
  `cos(δu + δv) + cos δw = D(r-1)/((1-r²)·√(1-p²)·√(1-q²)) < 0` where
  `D = gramDet u v w > 0`; concluded via strict antitonicity of `cos` on `[0,π]`
  (case split on whether `δu + δv ≤ π`).
* `angle_lt_angle_add_of_not_coplanar` — **strict trihedral face inequality**,
  assembled from mathlib's `angle_le_angle_add_angle` +
  `angle_eq_angle_add_angle_iff` (both in
  `Mathlib/Geometry/Euclidean/Angle/Unoriented/TriangleInequality.lean`).
* Convex-polygon infrastructure: `corner_cone` (every vertex lies in the cone
  of the two adjacent edge directions; proved via the two edge functionals and
  `Submodule.eq_of_le_of_finrank_eq` against the 2-dimensional plane `W₀`),
  `corner_cone_strict` (strict version for non-adjacent targets),
  `corner_coeff_gt_one` (**extremality**: the corner coefficients for target
  `V 0` at a non-boundary vertex sum to more than 1 — proved by applying the
  edge-`(0,1)` functional and ruling out `a+b ≤ 1` via `V 0`'s extremeness),
  `fan_cone` (**fan monotonicity**: `V j - V 0` is in the cone of
  `V 1 - V 0` and `V (j+1) - V 0`; proved by induction on `j.val`, using
  `corner_coeff_gt_one` to get `D = a+b-1 > 0` and eliminating the middle term
  via the edge-`(0,1)` functional).
* Circular indexing `Vc : ℕ → E` (`Vc k = V ⟨k % n⟩`) with its cast lemmas,
  used to state the fan triangulation without `Fin n` arithmetic; the generic
  `angle_telescope` used for both the interior-angle sum and the dihedral sum.
* **Part 1** (`sum_subAngle_lt`): `∑ ∠V i P V (i+1) < 2π`. At each polygon
  vertex the strict trihedral face inequality gives
  `θ i < ∠V (i-1) V i P + ∠P V i V (i+1)`; summing and using the fan
  triangulation for the interior angle sum `∑ θ i = (n-2)π`
  (`interior_angle_sum`, proved via `angle_telescope` with `fan_cone` at
  `V 0` and `corner_split` at the other vertices) yields the bound.
* **Part 2** (`sum_planeAngle_gt`): `(n-2)π < ∑ δ i`. The same fan
  triangulation lifted to trihedra at `P`: each trihedral has dihedral sum
  `> π` (`fan_trihedral_gt_pi`, via `dihedral_sum_gt_pi` after normalizing the
  rays with `planeAngle_normalize`; non-degeneracy from `ray_ne`,
  `ray_inner_abs_lt_one`, `ray_not_mem_span`). The dihedrals along `PV 0`
  telescope on the projected rays (`fan_cone_dproj`, `fan_ne_dproj`), and the
  dihedral at every non-boundary edge splits along the diagonal plane
  (`delta_split`, from `corner_cone` transported through `dproj`).
* `usa1981_p4`: from `h`, `(n-2)π < ∑δ = ∑α < 2π`, so `n < 4`, hence `n = 3`.


### Pitfalls encountered (for future maintenance)

* `omega` cannot evaluate `k % n` with variable `n`; use
  `Nat.mod_eq_of_lt`-rewrites first (see the `fin_*` lemmas).
* `rw [Fin.sub_def]` inside a goal whose LHS is `Fin.val (i - 1)` fails with a
  dependent-motive error; prove the value formula separately via
  `Fin.coe_sub_iff_le` / `Fin.sub_def` and rewrite with it afterwards.
* `real_inner_comm x y : ⟪y, x⟫ = ⟪x, y⟫` (note the swapped argument order).
* `LinearIndependent.pair_iff'` reduces to `∀ a, a • x ≠ y`, not to a span
  statement; `Submodule.mem_span_singleton` mediates.
* `rw` rewrites *all* occurrences — take care when the goal's RHS also
  contains the LHS-pattern (use `conv_lhs => rw` or build the equation first).
* `Nat.le_induction`'s motive must not contain `⟨k, by omega⟩` casts (the
  proof term gets abstracted as an extra motive argument); state induction
  predicates with `i : Fin n` and `i.val = k` instead (see `fan_cone`).
-/

snip end

problem usa1981_p4 (n : ℕ) [NeZero n] (hn : 3 ≤ n) (V : Fin n → E) (P : E)
    (hinj : Function.Injective V)
    (m : E)
    (hcopl : ∀ i, ⟪m, V i⟫ = ⟪m, V 0⟫)
    (hP : ⟪m, P⟫ ≠ ⟪m, V 0⟫)
    (hconv : ∀ i : Fin n, ∃ f : E →ₗ[ℝ] ℝ, f (V (i + 1) - V i) = 0 ∧
      (∀ j, 0 ≤ f (V j - V i)) ∧ ∀ j, j ≠ i → j ≠ i + 1 → 0 < f (V j - V i))
    (hplane : ∀ j, V j - V 0 ∈ Submodule.span ℝ {V 1 - V 0, V 2 - V 0})
    (h : (∑ i : Fin n, planeAngle P (V i) (V (i - 1)) (V (i + 1))) =
         ∑ i : Fin n, angle (V i - P) (V (i + 1) - P)) :
    n = 3 := by
  have h1 := sum_subAngle_lt hinj hcopl hP hconv hn hplane
  have h2 := sum_planeAngle_gt hinj hcopl hP hconv hn hplane
  rw [h] at h2
  have hlt : ((n : ℝ) - 2) * π < 2 * π := by linarith
  have hn4 : (n : ℝ) < 4 := by nlinarith [Real.pi_pos]
  have hn5 : n < 4 := by exact_mod_cast hn4
  omega

end Usa1981P4
