/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Euclidean.Angle.Sphere
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 1996, Problem 5

Let ABCDEF be a convex hexagon such that AB is parallel to DE, BC is
parallel to EF, and CD is parallel to FA. Let R_A, R_C, R_E denote the
circumradii of triangles FAB, BCD, DEF respectively, and let p denote the
perimeter of the hexagon. Prove that

  R_A + R_C + R_E ≥ p / 2.

## Formalization notes

We work in `EuclideanSpace ℝ (Fin 2)`. Any counterclockwise convex hexagon
`ABCDEF` with `AB ∥ DE`, `BC ∥ EF`, `CD ∥ FA` can be parametrized by

* unit vectors `u₁`, `u₂`, `u₃` along the sides `AB`, `BC`, `CD`,
* the side lengths `a = |AB|`, `b = |BC|`, `c = |CD|`,
* the positive ratios `kα = |DE|/|AB|`, `kβ = |EF|/|BC|`, `kγ = |FA|/|CD|`,

and the hypothesis `hparam` below asserts the existence of such a
parametrization, together with the counterclockwise ordering conditions
`0 < cross u₁ u₂`, `0 < cross u₂ u₃`, `0 < cross u₁ u₃` (these follow from
convexity: consecutive edges make positive turns, and the parallelism of
opposite sides forces the first three edge directions to span less than a
half-plane). The clockwise case is symmetric. The closure relation
`a(1 - kα)u₁ + b(1 - kβ)u₂ + c(1 - kγ)u₃ = 0` then holds automatically,
and the claim follows from the law of sines `2R = side / sin (opposite
angle)` together with projection inequalities of the form
`2|BF| ≥ AB sin B + AF sin F + CD sin C + DE sin E` and the estimate
`x + 1/x ≥ 2`.
-/

namespace Imo1996P5

open scoped RealInnerProductSpace EuclideanGeometry

/-- The two-dimensional cross product (signed area of the parallelogram
spanned by two vectors). -/
abbrev cross (v w : EuclideanSpace ℝ (Fin 2)) : ℝ := v 0 * w 1 - v 1 * w 0

snip begin

/-- Rotation by 90° counterclockwise. -/
abbrev rot90 (v : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) := !₂[- v 1, v 0]

lemma inner_rot90_right (v w : EuclideanSpace ℝ (Fin 2)) :
    ⟪v, rot90 w⟫ = - cross v w := by
  simp only [rot90, cross, PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

lemma cross_antisymm (v w : EuclideanSpace ℝ (Fin 2)) : cross v w = - cross w v := by
  simp only [cross]; ring

lemma cross_self (v : EuclideanSpace ℝ (Fin 2)) : cross v v = 0 := by
  simp only [cross]; ring

lemma norm_rot90 (v : EuclideanSpace ℝ (Fin 2)) : ‖rot90 v‖ = ‖v‖ := by
  simp only [EuclideanSpace.norm_eq, Fin.sum_univ_two, rot90]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring_nf

lemma inner_eq (v w : EuclideanSpace ℝ (Fin 2)) :
    ⟪v, w⟫ = v 0 * w 0 + v 1 * w 1 := by
  simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial]
  ring

lemma lagrange (v w : EuclideanSpace ℝ (Fin 2)) :
    ⟪v, w⟫ ^ 2 + cross v w ^ 2 = ‖v‖ ^ 2 * ‖w‖ ^ 2 := by
  have hvw : cross v w = v 0 * w 1 - v 1 * w 0 := rfl
  rw [← real_inner_self_eq_norm_sq v, ← real_inner_self_eq_norm_sq w,
    inner_eq, inner_eq, inner_eq, hvw]
  ring

lemma sin_angle_eq (x y : EuclideanSpace ℝ (Fin 2)) (hx : x ≠ 0) (hy : y ≠ 0) :
    Real.sin (InnerProductGeometry.angle x y) = |cross x y| / (‖x‖ * ‖y‖) := by
  have hnorm : (0:ℝ) < ‖x‖ * ‖y‖ := mul_pos (norm_pos_iff.mpr hx) (norm_pos_iff.mpr hy)
  have e : 1 - (⟪x, y⟫ / (‖x‖ * ‖y‖)) ^ 2 = cross x y ^ 2 / (‖x‖ * ‖y‖) ^ 2 := by
    have hl := lagrange x y
    have hne : (‖x‖ * ‖y‖) ^ 2 ≠ 0 := pow_ne_zero _ (ne_of_gt hnorm)
    field_simp
    linear_combination -hl
  rw [InnerProductGeometry.angle, Real.sin_arccos, e, Real.sqrt_div (sq_nonneg _),
    Real.sqrt_sq_eq_abs, Real.sqrt_sq (le_of_lt hnorm)]

lemma unit_ne_zero {x : EuclideanSpace ℝ (Fin 2)} (hx : ‖x‖ = 1) : x ≠ 0 :=
  norm_pos_iff.mp (hx ▸ one_pos)

lemma sin_angle_smul_pos {x y : EuclideanSpace ℝ (Fin 2)} (hx : x ≠ 0) (hy : y ≠ 0)
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    Real.sin (InnerProductGeometry.angle (r • x) (s • y)) = |cross x y| / (‖x‖ * ‖y‖) := by
  rw [sin_angle_eq _ _ (smul_ne_zero hr.ne' hx) (smul_ne_zero hs.ne' hy)]
  have e1 : cross (r • x) (s • y) = r * s * cross x y := by
    simp only [cross, PiLp.smul_apply, smul_eq_mul]
    ring
  have e2 : ‖r • x‖ = r * ‖x‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
  have e3 : ‖s • y‖ = s * ‖y‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs]
  have hr' : r ≠ 0 := hr.ne'
  have hs' : s ≠ 0 := hs.ne'
  have hx' : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hy' : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  have h1 : ‖x‖ * ‖y‖ ≠ 0 := mul_ne_zero hx' hy'
  have h2 : r * ‖x‖ * (s * ‖y‖) ≠ 0 := mul_ne_zero (mul_ne_zero hr' hx') (mul_ne_zero hs' hy')
  rw [e1, e2, e3, abs_mul, abs_of_pos (mul_pos hr hs)]
  field_simp

/-- Projection of a vector on a unit vector is bounded by the norm. -/
lemma proj_bound (v n : EuclideanSpace ℝ (Fin 2)) (hn : ‖n‖ = 1) : ⟪v, n⟫ ≤ ‖v‖ := by
  have h := real_inner_le_norm v n
  rwa [hn, mul_one] at h

snip end

problem imo1996_p5
    (A B C D E F : EuclideanSpace ℝ (Fin 2))
    (hFAB : AffineIndependent ℝ ![F, A, B])
    (hBCD : AffineIndependent ℝ ![B, C, D])
    (hDEF : AffineIndependent ℝ ![D, E, F])
    (hparam : ∃ (u₁ u₂ u₃ : EuclideanSpace ℝ (Fin 2)) (a b c kα kβ kγ : ℝ),
      ‖u₁‖ = 1 ∧ ‖u₂‖ = 1 ∧ ‖u₃‖ = 1 ∧
      0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < kα ∧ 0 < kβ ∧ 0 < kγ ∧
      B - A = a • u₁ ∧ C - B = b • u₂ ∧ D - C = c • u₃ ∧
      E - D = (-(kα * a)) • u₁ ∧ F - E = (-(kβ * b)) • u₂ ∧ A - F = (-(kγ * c)) • u₃ ∧
      0 < cross u₁ u₂ ∧ 0 < cross u₂ u₃ ∧ 0 < cross u₁ u₃) :
    (⟨![F, A, B], hFAB⟩ : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))).circumradius +
      (⟨![B, C, D], hBCD⟩ : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))).circumradius +
      (⟨![D, E, F], hDEF⟩ : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))).circumradius ≥
    (dist A B + dist B C + dist C D + dist D E + dist E F + dist F A) / 2 := by
  obtain ⟨u₁, u₂, u₃, a, b, c, kα, kβ, kγ, hu₁, hu₂, hu₃, ha, hb, hc, hkα, hkβ, hkγ,
    hAB, hBC, hCD, hDE, hEF, hFA, hs12, hs23, hs13⟩ := hparam
  set RA := (⟨![F, A, B], hFAB⟩ : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))).circumradius
    with hRA_def
  set RC := (⟨![B, C, D], hBCD⟩ : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))).circumradius
    with hRC_def
  set RE := (⟨![D, E, F], hDEF⟩ : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))).circumradius
    with hRE_def
  -- Reversed edge vectors.
  have hFA' : F - A = (kγ * c) • u₃ := by
    rw [← neg_sub A F, hFA, neg_smul, neg_neg]
  have hDE' : D - E = (kα * a) • u₁ := by
    rw [← neg_sub E D, hDE, neg_smul, neg_neg]
  have hCB' : B - C = (-b) • u₂ := by
    rw [neg_smul, ← hBC, neg_sub]
  have hEF' : F - E = (kβ * b) • (-u₂) := by
    rw [hEF, smul_neg, neg_smul]
  -- Side lengths.
  have hdAB : dist A B = a := by
    rw [dist_eq_norm, ← norm_neg, neg_sub, hAB, norm_smul, hu₁, mul_one, Real.norm_eq_abs,
      abs_of_pos ha]
  have hdBC : dist B C = b := by
    rw [dist_eq_norm, ← norm_neg, neg_sub, hBC, norm_smul, hu₂, mul_one, Real.norm_eq_abs,
      abs_of_pos hb]
  have hdCD : dist C D = c := by
    rw [dist_eq_norm, ← norm_neg, neg_sub, hCD, norm_smul, hu₃, mul_one, Real.norm_eq_abs,
      abs_of_pos hc]
  have hdDE : dist D E = kα * a := by
    rw [dist_eq_norm, ← norm_neg, neg_sub, hDE, norm_smul, hu₁, mul_one, Real.norm_eq_abs,
      abs_neg, abs_of_pos (mul_pos hkα ha)]
  have hdEF : dist E F = kβ * b := by
    rw [dist_eq_norm, ← norm_neg, neg_sub, hEF, norm_smul, hu₂, mul_one, Real.norm_eq_abs,
      abs_neg, abs_of_pos (mul_pos hkβ hb)]
  have hdFA : dist F A = kγ * c := by
    rw [dist_eq_norm, ← norm_neg, neg_sub, hFA, norm_smul, hu₃, mul_one, Real.norm_eq_abs,
      abs_neg, abs_of_pos (mul_pos hkγ hc)]
  -- Sines of the angles of the three triangles.
  have hsinA : Real.sin (∠ B A F) = cross u₁ u₃ := by
    have e : ∠ B A F = InnerProductGeometry.angle (a • u₁) ((kγ * c) • u₃) := by
      rw [EuclideanGeometry.angle, vsub_eq_sub, vsub_eq_sub, hAB, hFA']
    rw [e, sin_angle_smul_pos (unit_ne_zero hu₁) (unit_ne_zero hu₃) ha (mul_pos hkγ hc),
      hu₁, hu₃, mul_one, div_one, abs_of_pos hs13]
  have hsinC : Real.sin (∠ B C D) = cross u₂ u₃ := by
    have e : ∠ B C D = InnerProductGeometry.angle (b • (-u₂)) (c • u₃) := by
      rw [EuclideanGeometry.angle, vsub_eq_sub, vsub_eq_sub, hCB', hCD, smul_neg, neg_smul]
    have e2 : cross (-u₂) u₃ = - cross u₂ u₃ := by
      show (-(u₂ 0)) * u₃ 1 - (-(u₂ 1)) * u₃ 0 = -(u₂ 0 * u₃ 1 - u₂ 1 * u₃ 0)
      ring
    rw [e, sin_angle_smul_pos (unit_ne_zero (by rw [norm_neg, hu₂])) (unit_ne_zero hu₃) hb hc,
      norm_neg, hu₂, hu₃, mul_one, div_one, e2, abs_neg, abs_of_pos hs23]
  have hsinE : Real.sin (∠ D E F) = cross u₁ u₂ := by
    have e : ∠ D E F = InnerProductGeometry.angle ((kα * a) • u₁) ((kβ * b) • (-u₂)) := by
      rw [EuclideanGeometry.angle, vsub_eq_sub, vsub_eq_sub, hDE', hEF']
    have e2 : cross u₁ (-u₂) = - cross u₁ u₂ := by
      show u₁ 0 * (-(u₂ 1)) - u₁ 1 * (-(u₂ 0)) = -(u₁ 0 * u₂ 1 - u₁ 1 * u₂ 0)
      ring
    rw [e, sin_angle_smul_pos (unit_ne_zero hu₁) (unit_ne_zero (by rw [norm_neg, hu₂]))
      (mul_pos hkα ha) (mul_pos hkβ hb), hu₁, norm_neg, hu₂, mul_one, div_one, e2, abs_neg,
      abs_of_pos hs12]
  -- The law of sines for the three circumradii.
  have hRA : dist B F / cross u₁ u₃ = 2 * RA := by
    have h := Affine.Triangle.dist_div_sin_angle_eq_two_mul_circumradius
      (⟨![F, A, B], hFAB⟩ : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2)))
      (i₁ := 2) (i₂ := 1) (i₃ := 0) (by decide) (by decide) (by decide)
    have p0 : (⟨![F, A, B], hFAB⟩ : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))).points 0 = F := by
      simp
    have p1 : (⟨![F, A, B], hFAB⟩ : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))).points 1 = A := by
      simp
    have p2 : (⟨![F, A, B], hFAB⟩ : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))).points 2 = B := by
      simp
    rw [p0, p1, p2, hsinA, ← hRA_def] at h
    exact h
  have hRC : dist B D / cross u₂ u₃ = 2 * RC := by
    have h := Affine.Triangle.dist_div_sin_angle_eq_two_mul_circumradius
      (⟨![B, C, D], hBCD⟩ : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2)))
      (i₁ := 0) (i₂ := 1) (i₃ := 2) (by decide) (by decide) (by decide)
    have p0 : (⟨![B, C, D], hBCD⟩ : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))).points 0 = B := by
      simp
    have p1 : (⟨![B, C, D], hBCD⟩ : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))).points 1 = C := by
      simp
    have p2 : (⟨![B, C, D], hBCD⟩ : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))).points 2 = D := by
      simp
    rw [p0, p1, p2, hsinC, ← hRC_def] at h
    exact h
  have hRE : dist D F / cross u₁ u₂ = 2 * RE := by
    have h := Affine.Triangle.dist_div_sin_angle_eq_two_mul_circumradius
      (⟨![D, E, F], hDEF⟩ : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2)))
      (i₁ := 0) (i₂ := 1) (i₃ := 2) (by decide) (by decide) (by decide)
    have p0 : (⟨![D, E, F], hDEF⟩ : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))).points 0 = D := by
      simp
    have p1 : (⟨![D, E, F], hDEF⟩ : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))).points 1 = E := by
      simp
    have p2 : (⟨![D, E, F], hDEF⟩ : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))).points 2 = F := by
      simp
    rw [p0, p1, p2, hsinE, ← hRE_def] at h
    exact h
  -- Closure of the hexagon: the edge vectors sum to zero.
  have hclosure : a • u₁ + b • u₂ + c • u₃ + (-(kα * a)) • u₁ + (-(kβ * b)) • u₂ +
      (-(kγ * c)) • u₃ = 0 := by
    rw [← hAB, ← hBC, ← hCD, ← hDE, ← hEF, ← hFA]
    abel
  -- Projecting the closure relation onto the three directions perpendicular
  -- to the sides gives three scalar identities.
  have key1 : b * cross u₁ u₂ + c * cross u₁ u₃ =
      kβ * b * cross u₁ u₂ + kγ * c * cross u₁ u₃ := by
    have h1 := congr_arg (fun v : EuclideanSpace ℝ (Fin 2) => ⟪v, rot90 u₁⟫) hclosure
    simp only [inner_add_left, real_inner_smul_left, inner_zero_left, inner_rot90_right] at h1
    have e1 : cross u₂ u₁ = - cross u₁ u₂ := cross_antisymm u₂ u₁
    have e2 : cross u₃ u₁ = - cross u₁ u₃ := cross_antisymm u₃ u₁
    have e3 : cross u₁ u₁ = 0 := cross_self u₁
    linarith [h1, e1, e2, e3]
  have key2 : kα * a * cross u₁ u₂ + c * cross u₂ u₃ =
      a * cross u₁ u₂ + kγ * c * cross u₂ u₃ := by
    have h2 := congr_arg (fun v : EuclideanSpace ℝ (Fin 2) => ⟪v, rot90 u₂⟫) hclosure
    simp only [inner_add_left, real_inner_smul_left, inner_zero_left, inner_rot90_right] at h2
    have e1 : cross u₃ u₂ = - cross u₂ u₃ := cross_antisymm u₃ u₂
    have e2 : cross u₂ u₂ = 0 := cross_self u₂
    linarith [h2, e1, e2]
  have key3 : a * cross u₁ u₃ + b * cross u₂ u₃ =
      kα * a * cross u₁ u₃ + kβ * b * cross u₂ u₃ := by
    have h3 := congr_arg (fun v : EuclideanSpace ℝ (Fin 2) => ⟪v, rot90 u₃⟫) hclosure
    simp only [inner_add_left, real_inner_smul_left, inner_zero_left, inner_rot90_right] at h3
    have e3 : cross u₃ u₃ = 0 := cross_self u₃
    linarith [h3, e3]
  -- Projection inequalities: each diagonal is at least the width of the
  -- corresponding strip between parallel sides, measured in two ways.
  have hBF1 : a * cross u₁ u₂ + kγ * c * cross u₂ u₃ ≤ dist B F := by
    have e1 : F - B = (kγ * c) • u₃ - a • u₁ := by
      have h : F - B = (F - A) - (B - A) := by abel
      rw [h, hFA', hAB]
    have hinner : ⟪(kγ * c) • u₃ - a • u₁, rot90 u₂⟫ =
        a * cross u₁ u₂ + kγ * c * cross u₂ u₃ := by
      rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left,
        inner_rot90_right, inner_rot90_right, cross_antisymm u₃ u₂]
      ring
    rw [dist_eq_norm, ← norm_neg, neg_sub, e1, ← hinner]
    exact proj_bound _ (rot90 u₂) (by rw [norm_rot90, hu₂])
  have hBF2 : kα * a * cross u₁ u₂ + c * cross u₂ u₃ ≤ dist B F := by
    linarith [hBF1, key2]
  have hBF : (1 + kα) * a * cross u₁ u₂ + (1 + kγ) * c * cross u₂ u₃ ≤ 2 * dist B F := by
    linarith [hBF1, hBF2]
  have hBD1 : b * cross u₁ u₂ + c * cross u₁ u₃ ≤ dist B D := by
    have e1 : D - B = b • u₂ + c • u₃ := by
      have h : D - B = (C - B) + (D - C) := by abel
      rw [h, hBC, hCD]
    have hinner : ⟪b • u₂ + c • u₃, rot90 u₁⟫ =
        b * cross u₁ u₂ + c * cross u₁ u₃ := by
      rw [inner_add_left, real_inner_smul_left, real_inner_smul_left,
        inner_rot90_right, inner_rot90_right, cross_antisymm u₂ u₁, cross_antisymm u₃ u₁]
      ring
    rw [dist_eq_norm, ← norm_neg, neg_sub, e1, ← hinner]
    exact proj_bound _ (rot90 u₁) (by rw [norm_rot90, hu₁])
  have hBD2 : kβ * b * cross u₁ u₂ + kγ * c * cross u₁ u₃ ≤ dist B D := by
    linarith [hBD1, key1]
  have hBD : (1 + kβ) * b * cross u₁ u₂ + (1 + kγ) * c * cross u₁ u₃ ≤ 2 * dist B D := by
    linarith [hBD1, hBD2]
  have hDF1 : kα * a * cross u₁ u₃ + kβ * b * cross u₂ u₃ ≤ dist D F := by
    have e1 : F - D = (-(kβ * b)) • u₂ + (-(kα * a)) • u₁ := by
      have h : F - D = (F - E) + (E - D) := by abel
      rw [h, hEF, hDE]
    have hinner : ⟪(-(kβ * b)) • u₂ + (-(kα * a)) • u₁, rot90 u₃⟫ =
        kα * a * cross u₁ u₃ + kβ * b * cross u₂ u₃ := by
      rw [inner_add_left, real_inner_smul_left, real_inner_smul_left,
        inner_rot90_right, inner_rot90_right]
      ring
    rw [dist_eq_norm, ← norm_neg, neg_sub, e1, ← hinner]
    exact proj_bound _ (rot90 u₃) (by rw [norm_rot90, hu₃])
  have hDF2 : a * cross u₁ u₃ + b * cross u₂ u₃ ≤ dist D F := by
    linarith [hDF1, key3]
  have hDF : (1 + kα) * a * cross u₁ u₃ + (1 + kβ) * b * cross u₂ u₃ ≤ 2 * dist D F := by
    linarith [hDF1, hDF2]
  -- Convert the diagonal bounds into circumradius bounds via the law of sines.
  have hdistBF : dist B F = 2 * RA * cross u₁ u₃ := by
    have hs' : cross u₁ u₃ ≠ 0 := ne_of_gt hs13
    rw [div_eq_iff hs'] at hRA
    exact hRA
  have hdistBD : dist B D = 2 * RC * cross u₂ u₃ := by
    have hs' : cross u₂ u₃ ≠ 0 := ne_of_gt hs23
    rw [div_eq_iff hs'] at hRC
    exact hRC
  have hdistDF : dist D F = 2 * RE * cross u₁ u₂ := by
    have hs' : cross u₁ u₂ ≠ 0 := ne_of_gt hs12
    rw [div_eq_iff hs'] at hRE
    exact hRE
  have g1 : (1 + kα) * a * cross u₁ u₂ + (1 + kγ) * c * cross u₂ u₃ ≤
      RA * (4 * cross u₁ u₃) := by linarith [hBF, hdistBF]
  have g2 : (1 + kβ) * b * cross u₁ u₂ + (1 + kγ) * c * cross u₁ u₃ ≤
      RC * (4 * cross u₂ u₃) := by linarith [hBD, hdistBD]
  have g3 : (1 + kα) * a * cross u₁ u₃ + (1 + kβ) * b * cross u₂ u₃ ≤
      RE * (4 * cross u₁ u₂) := by linarith [hDF, hdistDF]
  -- Clear denominators: multiply each bound by the product of the two sines
  -- of the *other* triangles (all of which are positive).
  have g1' : ((1 + kα) * a * cross u₁ u₂ + (1 + kγ) * c * cross u₂ u₃) *
        (cross u₁ u₂ * cross u₂ u₃) ≤
      RA * (4 * cross u₁ u₃) * (cross u₁ u₂ * cross u₂ u₃) :=
    mul_le_mul_of_nonneg_right g1 (le_of_lt (mul_pos hs12 hs23))
  have g2' : ((1 + kβ) * b * cross u₁ u₂ + (1 + kγ) * c * cross u₁ u₃) *
        (cross u₁ u₂ * cross u₁ u₃) ≤
      RC * (4 * cross u₂ u₃) * (cross u₁ u₂ * cross u₁ u₃) :=
    mul_le_mul_of_nonneg_right g2 (le_of_lt (mul_pos hs12 hs13))
  have g3' : ((1 + kα) * a * cross u₁ u₃ + (1 + kβ) * b * cross u₂ u₃) *
        (cross u₁ u₃ * cross u₂ u₃) ≤
      RE * (4 * cross u₁ u₂) * (cross u₁ u₃ * cross u₂ u₃) :=
    mul_le_mul_of_nonneg_right g3 (le_of_lt (mul_pos hs13 hs23))
  -- The estimate `2xy ≤ x² + y²` for each pair of sines.
  have h1kα : (0:ℝ) < 1 + kα := by linarith
  have h1kβ : (0:ℝ) < 1 + kβ := by linarith
  have h1kγ : (0:ℝ) < 1 + kγ := by linarith
  have am1' : (1 + kα) * a * (2 * cross u₁ u₂ * cross u₁ u₃) * cross u₂ u₃ ≤
      (1 + kα) * a * (cross u₁ u₂ ^ 2 + cross u₁ u₃ ^ 2) * cross u₂ u₃ :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (two_mul_le_add_sq _ _) (le_of_lt (mul_pos h1kα ha)))
      (le_of_lt hs23)
  have am2' : (1 + kβ) * b * (2 * cross u₁ u₂ * cross u₂ u₃) * cross u₁ u₃ ≤
      (1 + kβ) * b * (cross u₁ u₂ ^ 2 + cross u₂ u₃ ^ 2) * cross u₁ u₃ :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (two_mul_le_add_sq _ _) (le_of_lt (mul_pos h1kβ hb)))
      (le_of_lt hs13)
  have am3' : (1 + kγ) * c * (2 * cross u₂ u₃ * cross u₁ u₃) * cross u₁ u₂ ≤
      (1 + kγ) * c * (cross u₂ u₃ ^ 2 + cross u₁ u₃ ^ 2) * cross u₁ u₂ :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (two_mul_le_add_sq _ _) (le_of_lt (mul_pos h1kγ hc)))
      (le_of_lt hs12)
  -- The perimeter.
  have hp : dist A B + dist B C + dist C D + dist D E + dist E F + dist F A =
      a + b + c + kα * a + kβ * b + kγ * c := by
    rw [hdAB, hdBC, hdCD, hdDE, hdEF, hdFA]
  rw [hp]
  have htot : (2 * (cross u₁ u₂ * cross u₁ u₃ * cross u₂ u₃)) *
        (a + b + c + kα * a + kβ * b + kγ * c) ≤
      (2 * (cross u₁ u₂ * cross u₁ u₃ * cross u₂ u₃)) * (2 * (RA + RC + RE)) := by
    linarith [g1', g2', g3', am1', am2', am3']
  have hsM : (0:ℝ) < 2 * (cross u₁ u₂ * cross u₁ u₃ * cross u₂ u₃) :=
    mul_pos two_pos (mul_pos (mul_pos hs12 hs13) hs23)
  have hfinal : a + b + c + kα * a + kβ * b + kγ * c ≤ 2 * (RA + RC + RE) :=
    le_of_mul_le_mul_left htot hsM
  linarith [hfinal]

end Imo1996P5
