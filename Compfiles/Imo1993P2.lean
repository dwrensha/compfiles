/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Real.Sign
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import Mathlib.Geometry.Euclidean.Circumcenter
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 1993, Problem 2

Let D be a point inside the acute-angled triangle ABC such that
∠ADB = ∠ACB + 90°, and AC·BD = AD·BC.

(a) Calculate the ratio AB·CD/(AC·BD).

(b) Prove that the tangents at C to the circumcircles of ACD and BCD
are perpendicular.
-/

namespace Imo1993P2

open scoped EuclideanGeometry RealInnerProductSpace

/-- The Euclidean plane. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

noncomputable section

snip begin

/-- The 2D cross product (signed area) of two plane vectors. -/
def cross (x y : Plane) : ℝ := x 0 * y 1 - x 1 * y 0

lemma inner_pt (x y : Plane) : ⟪x, y⟫ = x 0 * y 0 + x 1 * y 1 := by
  rw [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, RCLike.inner_apply]
  simp only [conj_trivial]
  ring

lemma dist_sq (x y : Plane) : dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.sq_sqrt (by positivity),
    Real.dist_eq, Real.dist_eq, sq_abs, sq_abs]

lemma cos_angle_mul_dist (x y z : Plane) :
    Real.cos (∠ x y z) * (dist x y * dist z y) = ⟪x -ᵥ y, z -ᵥ y⟫ := by
  rw [dist_eq_norm_vsub Plane x y, dist_eq_norm_vsub Plane z y, EuclideanGeometry.angle,
    InnerProductGeometry.cos_angle_mul_norm_mul_norm]

lemma sin_angle_mul_dist (x y z : Plane) :
    Real.sin (∠ x y z) * (dist x y * dist z y) = |cross (x -ᵥ y) (z -ᵥ y)| := by
  rw [dist_eq_norm_vsub Plane x y, dist_eq_norm_vsub Plane z y, EuclideanGeometry.angle,
    InnerProductGeometry.sin_angle_mul_norm_mul_norm, ← Real.sqrt_sq_eq_abs]
  congr 1
  simp only [vsub_eq_sub, inner_pt, cross]
  ring

lemma Plane.ext {x y : Plane} (h0 : x 0 = y 0) (h1 : x 1 = y 1) : x = y := by
  apply WithLp.ofLp_injective (p := 2)
  funext i
  fin_cases i <;> assumption

/-- Barycentric coordinates of a point strictly inside a triangle. -/
lemma insideData {A B C D : Plane} (hABC : AffineIndependent ℝ ![A, B, C])
    (hD : D ∈ interior (convexHull ℝ {A, B, C})) :
    ∃ w₀ w₁ w₂ : ℝ, 0 < w₀ ∧ 0 < w₁ ∧ 0 < w₂ ∧ w₀ + w₁ + w₂ = 1 ∧
      D = w₀ • A + w₁ • B + w₂ • C := by
  have htot' : affineSpan ℝ (Set.range ![A, B, C]) = ⊤ := by
    rw [AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nontrivial]
    apply AffineIndependent.vectorSpan_eq_top_of_card_eq_finrank_add_one hABC
    rw [finrank_euclideanSpace]
    simp only [Nat.succ_eq_add_one, zero_add, Nat.reduceAdd, Fintype.card_fin]
  set basis := AffineBasis.mk _ hABC htot' with h_basis
  have h_range : {A, B, C} = Set.range basis := by
    rw [h_basis, DFunLike.coe, AffineBasis.instFunLike]
    simp
    rw [Set.pair_comm, Set.insert_comm, Set.pair_comm]
  rw [h_range, AffineBasis.interior_convexHull] at hD
  dsimp at hD
  have hA : A = basis 0 := by
    rw [h_basis, DFunLike.coe, AffineBasis.instFunLike]
    simp
  have hB : B = basis 1 := by
    rw [h_basis, DFunLike.coe, AffineBasis.instFunLike]
    simp
  have hC : C = basis 2 := by
    rw [h_basis, DFunLike.coe, AffineBasis.instFunLike]
    simp
  refine ⟨basis.coord 0 D, basis.coord 1 D, basis.coord 2 D, hD 0, hD 1, hD 2, ?_, ?_⟩
  · have hsum' := AffineBasis.sum_coord_apply_eq_one basis D
    rw [Fin.sum_univ_three] at hsum'
    exact hsum'
  · have hlin := AffineBasis.linear_combination_coord_eq_self basis D
    rw [Fin.sum_univ_three, ← hA, ← hB, ← hC] at hlin
    exact hlin.symm

lemma cross_AD_BD {A B C D : Plane} {w₀ w₁ w₂ : ℝ}
    (hsum : w₀ + w₁ + w₂ = 1) (heq : D = w₀ • A + w₁ • B + w₂ • C) :
    cross (A - D) (B - D) = w₂ * cross (A - C) (B - C) := by
  have hD0 : D 0 = w₀ * A 0 + w₁ * B 0 + w₂ * C 0 := by
    rw [heq]
    simp [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  have hD1 : D 1 = w₀ * A 1 + w₁ * B 1 + w₂ * C 1 := by
    rw [heq]
    simp [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  simp only [cross, PiLp.sub_apply, hD0, hD1]
  linear_combination (A 1 * B 0 - A 0 * B 1) * hsum

lemma cross_AC_DC {A B C D : Plane} {w₀ w₁ w₂ : ℝ}
    (hsum : w₀ + w₁ + w₂ = 1) (heq : D = w₀ • A + w₁ • B + w₂ • C) :
    cross (A - C) (D - C) = w₁ * cross (A - C) (B - C) := by
  have hD0 : D 0 = w₀ * A 0 + w₁ * B 0 + w₂ * C 0 := by
    rw [heq]
    simp [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  have hD1 : D 1 = w₀ * A 1 + w₁ * B 1 + w₂ * C 1 := by
    rw [heq]
    simp [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  simp only [cross, PiLp.sub_apply, hD0, hD1]
  linear_combination (A 0 * C 1 - A 1 * C 0) * hsum

lemma cross_BC_DC {A B C D : Plane} {w₀ w₁ w₂ : ℝ}
    (hsum : w₀ + w₁ + w₂ = 1) (heq : D = w₀ • A + w₁ • B + w₂ • C) :
    cross (B - C) (D - C) = -w₀ * cross (A - C) (B - C) := by
  have hD0 : D 0 = w₀ * A 0 + w₁ * B 0 + w₂ * C 0 := by
    rw [heq]
    simp [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  have hD1 : D 1 = w₀ * A 1 + w₁ * B 1 + w₂ * C 1 := by
    rw [heq]
    simp [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  simp only [cross, PiLp.sub_apply, hD0, hD1]
  linear_combination (B 0 * C 1 - B 1 * C 0) * hsum

lemma cross_ne_zero {A B C : Plane} (hABC : AffineIndependent ℝ ![A, B, C]) :
    cross (A - C) (B - C) ≠ 0 := by
  have hAC : A ≠ C := hABC.injective.ne (by decide : ((0 : Fin 3) ≠ 2))
  rw [affineIndependent_iff_not_collinear_set] at hABC
  intro hcross
  apply hABC
  have hBmem : B ∈ line[ℝ, A, C] := by
    rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
    simp only [cross, PiLp.sub_apply] at hcross
    by_cases h1 : A 1 - C 1 = 0
    · have h0 : A 0 - C 0 ≠ 0 := by
        intro h0
        apply hAC
        apply Plane.ext <;> linarith
      have hB1 : A 1 - B 1 = 0 := by
        have hz : (A 0 - C 0) * (B 1 - C 1) = 0 := by
          linear_combination hcross + (B 0 - C 0) * h1
        have hb : B 1 - C 1 = 0 := (mul_eq_zero.mp hz).resolve_left h0
        linarith
      have hr0 : (A 0 - B 0) / (A 0 - C 0) * (A 0 - C 0) = A 0 - B 0 :=
        div_mul_cancel₀ _ h0
      have hvec : ((A 0 - B 0) / (A 0 - C 0)) • (C - A) = B - A := by
        apply Plane.ext
        · simp only [PiLp.smul_apply, smul_eq_mul, PiLp.sub_apply]
          linear_combination -hr0
        · simp only [PiLp.smul_apply, smul_eq_mul, PiLp.sub_apply]
          have h1' : C 1 - A 1 = 0 := by linarith
          rw [h1', mul_zero]
          linarith
      refine ⟨(A 0 - B 0) / (A 0 - C 0), ?_⟩
      rw [AffineMap.lineMap_apply_module]
      have hm : (1 - (A 0 - B 0) / (A 0 - C 0)) • A + ((A 0 - B 0) / (A 0 - C 0)) • C =
          A + ((A 0 - B 0) / (A 0 - C 0)) • (C - A) := by module
      rw [hm, hvec, add_sub_cancel]
    · have hr1 : (A 1 - B 1) / (A 1 - C 1) * (A 1 - C 1) = A 1 - B 1 :=
        div_mul_cancel₀ _ h1
      have hr0 : (A 1 - B 1) / (A 1 - C 1) * (A 0 - C 0) = A 0 - B 0 := by
        rw [div_mul_eq_mul_div, div_eq_iff h1]
        linear_combination -hcross
      have hvec : ((A 1 - B 1) / (A 1 - C 1)) • (C - A) = B - A := by
        apply Plane.ext
        · simp only [PiLp.smul_apply, smul_eq_mul, PiLp.sub_apply]
          linear_combination -hr0
        · simp only [PiLp.smul_apply, smul_eq_mul, PiLp.sub_apply]
          linear_combination -hr1
      refine ⟨(A 1 - B 1) / (A 1 - C 1), ?_⟩
      rw [AffineMap.lineMap_apply_module]
      have hm : (1 - (A 1 - B 1) / (A 1 - C 1)) • A + ((A 1 - B 1) / (A 1 - C 1)) • C =
          A + ((A 1 - B 1) / (A 1 - C 1)) • (C - A) := by module
      rw [hm, hvec, add_sub_cancel]
  rw [Set.insert_comm A B {C}]
  exact collinear_insert_of_mem_affineSpan_pair hBmem

@[simp] lemma cross_self (x : Plane) : cross x x = 0 := by simp only [cross]; ring

/-- The transport equations: the content of the two metric hypotheses of the
problem, packaged in coordinate form using the similarity ratio `r` and the
orientation sign `s` of the triangle. -/
lemma setup {A B C D : Plane}
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hD : D ∈ interior (convexHull ℝ {A, B, C}))
    (hAngle : ∠ A D B = ∠ A C B + Real.pi / 2)
    (hRatio : dist A C * dist B D = dist A D * dist B C) :
    ∃ r s : ℝ, s ^ 2 = 1 ∧
      ((A 0 - D 0) ^ 2 + (A 1 - D 1) ^ 2) =
        r * ((A 0 - C 0) ^ 2 + (A 1 - C 1) ^ 2) ∧
      ((B 0 - D 0) ^ 2 + (B 1 - D 1) ^ 2) =
        r * ((B 0 - C 0) ^ 2 + (B 1 - C 1) ^ 2) ∧
      ((A 0 - D 0) * (B 0 - D 0) + (A 1 - D 1) * (B 1 - D 1)) =
        -(r * s * ((A 0 - C 0) * (B 1 - C 1) - (A 1 - C 1) * (B 0 - C 0))) ∧
      ((A 0 - D 0) * (B 1 - D 1) - (A 1 - D 1) * (B 0 - D 0)) =
        r * s * ((A 0 - C 0) * (B 0 - C 0) + (A 1 - C 1) * (B 1 - C 1)) ∧
      (A 0 - C 0) * (D 1 - C 1) - (A 1 - C 1) * (D 0 - C 0) ≠ 0 ∧
      (B 0 - C 0) * (D 1 - C 1) - (B 1 - C 1) * (D 0 - C 0) ≠ 0 := by
  obtain ⟨w₀, w₁, w₂, hw₀, hw₁, hw₂, hsum, heq⟩ := insideData hABC hD
  have hcpq : cross (A - C) (B - C) ≠ 0 := cross_ne_zero hABC
  have hdet1 : cross (A - C) (D - C) ≠ 0 := by
    rw [cross_AC_DC hsum heq]
    exact mul_ne_zero (ne_of_gt hw₁) hcpq
  have hdet2 : cross (B - C) (D - C) ≠ 0 := by
    rw [cross_BC_DC hsum heq]
    exact mul_ne_zero (neg_ne_zero.mpr (ne_of_gt hw₀)) hcpq
  have hAC' : A ≠ C := hABC.injective.ne (by decide : ((0 : Fin 3) ≠ 2))
  have hBC' : B ≠ C := hABC.injective.ne (by decide : ((1 : Fin 3) ≠ 2))
  have hAD' : A ≠ D := by
    rintro rfl
    simp at hdet1
  have hBD' : B ≠ D := by
    rintro rfl
    exact hdet2 (by simp)
  have hdAC : 0 < dist A C := dist_pos.mpr hAC'
  have hdBC : 0 < dist B C := dist_pos.mpr hBC'
  have hdAD : 0 < dist A D := dist_pos.mpr hAD'
  have hdBD : 0 < dist B D := dist_pos.mpr hBD'
  have hAC0 : dist A C ≠ 0 := ne_of_gt hdAC
  have hwAC0 : dist A C * dist B C ≠ 0 := mul_ne_zero (ne_of_gt hdAC) (ne_of_gt hdBC)
  -- the orientation sign
  set s := Real.sign (cross (A - C) (B - C)) with hs
  have hsgn : s = -1 ∨ s = 1 := Real.sign_apply_eq_of_ne_zero _ hcpq
  have hs2 : s ^ 2 = 1 := by rcases hsgn with h | h <;> rw [h] <;> norm_num
  have hscpq : s * cross (A - C) (B - C) = |cross (A - C) (B - C)| := by
    rw [hs]
    rcases lt_or_gt_of_ne hcpq with hlt | hgt
    · rw [Real.sign_of_neg hlt, neg_mul, one_mul, abs_of_neg hlt]
    · rw [Real.sign_of_pos hgt, one_mul, abs_of_pos hgt]
  have hscuv : s * cross (A - D) (B - D) = |cross (A - D) (B - D)| := by
    rw [cross_AD_BD hsum heq, abs_mul, abs_of_pos hw₂, ← hscpq]
    ring
  -- the similarity ratio
  set r := dist A D ^ 2 / dist A C ^ 2 with hr
  have hg1' : dist A D ^ 2 = r * dist A C ^ 2 := by
    rw [hr, div_mul_cancel₀ _ (pow_ne_zero 2 hAC0)]
  have hg2' : dist B D ^ 2 = r * dist B C ^ 2 := by
    have h2 : dist A C ^ 2 * dist B D ^ 2 = dist A D ^ 2 * dist B C ^ 2 := by
      rw [← mul_pow, ← mul_pow, hRatio]
    have h2' : dist A C ^ 2 * dist B D ^ 2 = dist A C ^ 2 * (r * dist B C ^ 2) := by
      linear_combination h2 + dist B C ^ 2 * hg1'
    exact mul_left_cancel₀ (pow_ne_zero 2 hAC0) h2'
  -- the angle condition in cosine/sine form
  have hcos : Real.cos (∠ A D B) = - Real.sin (∠ A C B) := by
    rw [hAngle, Real.cos_add_pi_div_two]
  have hsin : Real.sin (∠ A D B) = Real.cos (∠ A C B) := by
    rw [hAngle, Real.sin_add_pi_div_two]
  have h1 := cos_angle_mul_dist A D B
  have h2 := sin_angle_mul_dist A C B
  have h3 := sin_angle_mul_dist A D B
  have h4 := cos_angle_mul_dist A C B
  simp only [vsub_eq_sub] at h1 h2 h3 h4
  have hwAD : dist A D * dist B D = r * (dist A C * dist B C) := by
    have hsq : (dist A D * dist B D) ^ 2 = (r * (dist A C * dist B C)) ^ 2 := by
      rw [mul_pow, mul_pow, hg1', hg2', mul_pow]
      ring
    have hpos1 : 0 ≤ dist A D * dist B D := by positivity
    have hpos2 : 0 ≤ r * (dist A C * dist B C) := by
      apply mul_nonneg _ (by positivity)
      rw [hr]
      positivity
    have hx : dist A D * dist B D = Real.sqrt ((dist A D * dist B D) ^ 2) :=
      (Real.sqrt_sq hpos1).symm
    rw [hx, hsq, Real.sqrt_sq hpos2]
  have hg3 : ⟪A - D, B - D⟫ * (dist A C * dist B C) =
      -(dist A D * dist B D) * |cross (A - C) (B - C)| := by
    linear_combination hcos * (dist A D * dist B D) * (dist A C * dist B C) -
      h1 * (dist A C * dist B C) - h2 * (dist A D * dist B D)
  have hg4 : |cross (A - D) (B - D)| * (dist A C * dist B C) =
      (dist A D * dist B D) * ⟪A - C, B - C⟫ := by
    linear_combination hsin * (dist A D * dist B D) * (dist A C * dist B C) -
      h3 * (dist A C * dist B C) + h4 * (dist A D * dist B D)
  have hg3' : ⟪A - D, B - D⟫ = -(r * s * cross (A - C) (B - C)) := by
    rw [hwAD, ← hscpq] at hg3
    have hgg : ⟪A - D, B - D⟫ * (dist A C * dist B C) =
        -(r * s * cross (A - C) (B - C)) * (dist A C * dist B C) := by
      linear_combination hg3
    exact mul_right_cancel₀ hwAC0 hgg
  have hg4' : cross (A - D) (B - D) = r * s * ⟪A - C, B - C⟫ := by
    rw [hwAD, ← hscuv] at hg4
    have hgg : cross (A - D) (B - D) * (dist A C * dist B C) =
        (r * s * ⟪A - C, B - C⟫) * (dist A C * dist B C) := by
      linear_combination s * hg4 - ((dist A C * dist B C) * cross (A - D) (B - D)) * hs2
    exact mul_right_cancel₀ hwAC0 hgg
  refine ⟨r, s, hs2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [dist_sq A D, dist_sq A C] at hg1'
    exact hg1'
  · rw [dist_sq B D, dist_sq B C] at hg2'
    exact hg2'
  · simp only [inner_pt, cross, PiLp.sub_apply] at hg3'
    exact hg3'
  · simp only [cross, inner_pt, PiLp.sub_apply] at hg4'
    exact hg4'
  · simp only [cross, PiLp.sub_apply] at hdet1
    exact hdet1
  · simp only [cross, PiLp.sub_apply] at hdet2
    exact hdet2

lemma master_a {A B C D : Plane} {r s : ℝ}
    (hg1 : ((A 0 - D 0) ^ 2 + (A 1 - D 1) ^ 2) =
      r * ((A 0 - C 0) ^ 2 + (A 1 - C 1) ^ 2))
    (hg2 : ((B 0 - D 0) ^ 2 + (B 1 - D 1) ^ 2) =
      r * ((B 0 - C 0) ^ 2 + (B 1 - C 1) ^ 2))
    (hg3 : ((A 0 - D 0) * (B 0 - D 0) + (A 1 - D 1) * (B 1 - D 1)) =
      -(r * s * ((A 0 - C 0) * (B 1 - C 1) - (A 1 - C 1) * (B 0 - C 0))))
    (hg4 : ((A 0 - D 0) * (B 1 - D 1) - (A 1 - D 1) * (B 0 - D 0)) =
      r * s * ((A 0 - C 0) * (B 0 - C 0) + (A 1 - C 1) * (B 1 - C 1))) :
    ((A 0 - B 0) ^ 2 + (A 1 - B 1) ^ 2) * ((C 0 - D 0) ^ 2 + (C 1 - D 1) ^ 2) =
      2 * (((A 0 - C 0) ^ 2 + (A 1 - C 1) ^ 2) * ((B 0 - D 0) ^ 2 + (B 1 - D 1) ^ 2)) := by
  linear_combination
    ((B 1 - C 1) ^ 2 + (B 0 - C 0) ^ 2) * hg1 -
    ((A 1 - C 1) ^ 2 + (A 0 - C 0) ^ 2) * hg2 -
    2 * ((A 1 - C 1) * (B 1 - C 1) + (A 0 - C 0) * (B 0 - C 0)) * hg3 +
    2 * ((A 1 - C 1) * (B 0 - C 0) - (A 0 - C 0) * (B 1 - C 1)) * hg4

snip end

/-- The answer to part (a). -/
determine answer : ℝ := Real.sqrt 2

problem imo1993_p2_a
    (A B C D : Plane)
    (hABC : AffineIndependent ℝ ![A, B, C])
    (_hAcuteA : ∠ C A B < Real.pi / 2)
    (_hAcuteB : ∠ A B C < Real.pi / 2)
    (_hAcuteC : ∠ B C A < Real.pi / 2)
    (hD : D ∈ interior (convexHull ℝ {A, B, C}))
    (hAngle : ∠ A D B = ∠ A C B + Real.pi / 2)
    (hRatio : dist A C * dist B D = dist A D * dist B C) :
    dist A B * dist C D / (dist A C * dist B D) = answer := by
  obtain ⟨r, s, hs2, hg1, hg2, hg3, hg4, hdet1, hdet2⟩ := setup hABC hD hAngle hRatio
  have hgoal : dist A B ^ 2 * dist C D ^ 2 = 2 * (dist A C ^ 2 * dist B D ^ 2) := by
    rw [dist_sq A B, dist_sq C D, dist_sq A C, dist_sq B D]
    exact master_a hg1 hg2 hg3 hg4
  have hAC' : A ≠ C := hABC.injective.ne (by decide : ((0 : Fin 3) ≠ 2))
  have hBD' : B ≠ D := by
    rintro rfl
    exact hdet2 (by ring)
  have hdAC : 0 < dist A C := dist_pos.mpr hAC'
  have hdBD : 0 < dist B D := dist_pos.mpr hBD'
  have hY : 0 < dist A C * dist B D := mul_pos hdAC hdBD
  have hX0 : 0 ≤ dist A B * dist C D := by positivity
  have hX : dist A B * dist C D = Real.sqrt 2 * (dist A C * dist B D) := by
    have hsq : (dist A B * dist C D) ^ 2 = (Real.sqrt 2 * (dist A C * dist B D)) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num)]
      linear_combination hgoal
    have hpos2 : 0 ≤ Real.sqrt 2 * (dist A C * dist B D) := by positivity
    have hx : dist A B * dist C D = Real.sqrt ((dist A B * dist C D) ^ 2) :=
      (Real.sqrt_sq hX0).symm
    rw [hx, hsq, Real.sqrt_sq hpos2]
  unfold answer
  rw [hX, div_eq_iff (ne_of_gt hY)]

/-- **Part (b).**  The tangent at `C` to the circumcircle of `ACD` is the line
through `C` perpendicular to the radius `O₁C` (with `O₁` the circumcenter of
`ACD`), and similarly for the circumcircle of `BCD`.  Two lines through `C` are
perpendicular iff the corresponding radii are, so the claim is formalized as
perpendicularity of the two circumradii, i.e. vanishing of the inner product.
(The non-degeneracy assumptions `hACD`, `hBCD` follow from `hD`; they are
included as hypotheses so that the circumcenters are well-defined.) -/
problem imo1993_p2_b
    (A B C D : Plane)
    (hABC : AffineIndependent ℝ ![A, B, C])
    (_hAcuteA : ∠ C A B < Real.pi / 2)
    (_hAcuteB : ∠ A B C < Real.pi / 2)
    (_hAcuteC : ∠ B C A < Real.pi / 2)
    (hD : D ∈ interior (convexHull ℝ {A, B, C}))
    (hAngle : ∠ A D B = ∠ A C B + Real.pi / 2)
    (hRatio : dist A C * dist B D = dist A D * dist B C)
    (hACD : AffineIndependent ℝ ![A, C, D])
    (hBCD : AffineIndependent ℝ ![B, C, D]) :
    let T₁ : Affine.Triangle ℝ Plane := ⟨![A, C, D], hACD⟩
    let T₂ : Affine.Triangle ℝ Plane := ⟨![B, C, D], hBCD⟩
    ⟪T₁.circumcenter - C, T₂.circumcenter - C⟫ = 0 := by
  obtain ⟨r, s, hs2, hg1, hg2, hg3, hg4, hdet1, hdet2⟩ := setup hABC hD hAngle hRatio
  set T₁ : Affine.Triangle ℝ Plane := ⟨![A, C, D], hACD⟩ with hT₁
  set T₂ : Affine.Triangle ℝ Plane := ⟨![B, C, D], hBCD⟩ with hT₂
  -- distances from the circumcenters
  have hO₁A : dist A T₁.circumcenter = dist C T₁.circumcenter := by
    have hpts0 : T₁.points 0 = A := rfl
    have hpts1 : T₁.points 1 = C := rfl
    rw [← hpts0, ← hpts1, Affine.Simplex.dist_circumcenter_eq_circumradius,
      Affine.Simplex.dist_circumcenter_eq_circumradius]
  have hO₁D : dist D T₁.circumcenter = dist C T₁.circumcenter := by
    have hpts2 : T₁.points 2 = D := rfl
    have hpts1 : T₁.points 1 = C := rfl
    rw [← hpts2, ← hpts1, Affine.Simplex.dist_circumcenter_eq_circumradius,
      Affine.Simplex.dist_circumcenter_eq_circumradius]
  have hO₂B : dist B T₂.circumcenter = dist C T₂.circumcenter := by
    have hpts0 : T₂.points 0 = B := rfl
    have hpts1 : T₂.points 1 = C := rfl
    rw [← hpts0, ← hpts1, Affine.Simplex.dist_circumcenter_eq_circumradius,
      Affine.Simplex.dist_circumcenter_eq_circumradius]
  have hO₂D : dist D T₂.circumcenter = dist C T₂.circumcenter := by
    have hpts2 : T₂.points 2 = D := rfl
    have hpts1 : T₂.points 1 = C := rfl
    rw [← hpts2, ← hpts1, Affine.Simplex.dist_circumcenter_eq_circumradius,
      Affine.Simplex.dist_circumcenter_eq_circumradius]
  -- the circumcenter equations in coordinate form
  have hc1 : 2 * ((T₁.circumcenter 0 - C 0) * (A 0 - C 0) +
      (T₁.circumcenter 1 - C 1) * (A 1 - C 1)) =
      (A 0 - C 0) ^ 2 + (A 1 - C 1) ^ 2 := by
    have hdist : dist A T₁.circumcenter ^ 2 = dist C T₁.circumcenter ^ 2 := by rw [hO₁A]
    rw [dist_sq, dist_sq] at hdist
    linear_combination -hdist
  have hc2 : 2 * ((T₁.circumcenter 0 - C 0) * (D 0 - C 0) +
      (T₁.circumcenter 1 - C 1) * (D 1 - C 1)) =
      (D 0 - C 0) ^ 2 + (D 1 - C 1) ^ 2 := by
    have hdist : dist D T₁.circumcenter ^ 2 = dist C T₁.circumcenter ^ 2 := by rw [hO₁D]
    rw [dist_sq, dist_sq] at hdist
    linear_combination -hdist
  have hc3 : 2 * ((T₂.circumcenter 0 - C 0) * (B 0 - C 0) +
      (T₂.circumcenter 1 - C 1) * (B 1 - C 1)) =
      (B 0 - C 0) ^ 2 + (B 1 - C 1) ^ 2 := by
    have hdist : dist B T₂.circumcenter ^ 2 = dist C T₂.circumcenter ^ 2 := by rw [hO₂B]
    rw [dist_sq, dist_sq] at hdist
    linear_combination -hdist
  have hc4 : 2 * ((T₂.circumcenter 0 - C 0) * (D 0 - C 0) +
      (T₂.circumcenter 1 - C 1) * (D 1 - C 1)) =
      (D 0 - C 0) ^ 2 + (D 1 - C 1) ^ 2 := by
    have hdist : dist D T₂.circumcenter ^ 2 = dist C T₂.circumcenter ^ 2 := by rw [hO₂D]
    rw [dist_sq, dist_sq] at hdist
    linear_combination -hdist
  -- Cramer formulas for the circumcenter coordinates
  have fo10 : 2 * ((A 0 - C 0) * (D 1 - C 1) - (A 1 - C 1) * (D 0 - C 0)) *
      (T₁.circumcenter 0 - C 0) =
      (D 1 - C 1) * ((A 0 - C 0) ^ 2 + (A 1 - C 1) ^ 2) -
      (A 1 - C 1) * ((D 0 - C 0) ^ 2 + (D 1 - C 1) ^ 2) := by
    linear_combination (D 1 - C 1) * hc1 - (A 1 - C 1) * hc2
  have fo11 : 2 * ((A 0 - C 0) * (D 1 - C 1) - (A 1 - C 1) * (D 0 - C 0)) *
      (T₁.circumcenter 1 - C 1) =
      (A 0 - C 0) * ((D 0 - C 0) ^ 2 + (D 1 - C 1) ^ 2) -
      (D 0 - C 0) * ((A 0 - C 0) ^ 2 + (A 1 - C 1) ^ 2) := by
    linear_combination (A 0 - C 0) * hc2 - (D 0 - C 0) * hc1
  have fo20 : 2 * ((B 0 - C 0) * (D 1 - C 1) - (B 1 - C 1) * (D 0 - C 0)) *
      (T₂.circumcenter 0 - C 0) =
      (D 1 - C 1) * ((B 0 - C 0) ^ 2 + (B 1 - C 1) ^ 2) -
      (B 1 - C 1) * ((D 0 - C 0) ^ 2 + (D 1 - C 1) ^ 2) := by
    linear_combination (D 1 - C 1) * hc3 - (B 1 - C 1) * hc4
  have fo21 : 2 * ((B 0 - C 0) * (D 1 - C 1) - (B 1 - C 1) * (D 0 - C 0)) *
      (T₂.circumcenter 1 - C 1) =
      (B 0 - C 0) * ((D 0 - C 0) ^ 2 + (D 1 - C 1) ^ 2) -
      (D 0 - C 0) * ((B 0 - C 0) ^ 2 + (B 1 - C 1) ^ 2) := by
    linear_combination (B 0 - C 0) * hc4 - (D 0 - C 0) * hc3
  -- the key identity: the inner product times the nonzero determinant factor vanishes
  have hK : ((T₁.circumcenter 0 - C 0) * (T₂.circumcenter 0 - C 0) +
      (T₁.circumcenter 1 - C 1) * (T₂.circumcenter 1 - C 1)) *
      (4 * ((A 0 - C 0) * (D 1 - C 1) - (A 1 - C 1) * (D 0 - C 0)) *
        ((B 0 - C 0) * (D 1 - C 1) - (B 1 - C 1) * (D 0 - C 0))) = 0 := by
    linear_combination
      (2 * ((B 0 - C 0) * (D 1 - C 1) - (B 1 - C 1) * (D 0 - C 0)) *
        (T₂.circumcenter 0 - C 0)) * fo10 +
      (2 * ((B 0 - C 0) * (D 1 - C 1) - (B 1 - C 1) * (D 0 - C 0)) *
        (T₂.circumcenter 1 - C 1)) * fo11 +
      ((D 1 - C 1) * ((A 0 - C 0) ^ 2 + (A 1 - C 1) ^ 2) -
        (A 1 - C 1) * ((D 0 - C 0) ^ 2 + (D 1 - C 1) ^ 2)) * fo20 +
      ((A 0 - C 0) * ((D 0 - C 0) ^ 2 + (D 1 - C 1) ^ 2) -
        (D 0 - C 0) * ((A 0 - C 0) ^ 2 + (A 1 - C 1) ^ 2)) * fo21 +
      (((D 0 - C 0) ^ 2 + (D 1 - C 1) ^ 2) *
        ((A 0 - C 0) * (B 0 - C 0) + (A 1 - C 1) * (B 1 - C 1))) * hg3 +
      (((D 0 - C 0) ^ 2 + (D 1 - C 1) ^ 2) *
        ((A 0 - C 0) * (B 1 - C 1) - (A 1 - C 1) * (B 0 - C 0))) * hg4
  have hdd : 4 * ((A 0 - C 0) * (D 1 - C 1) - (A 1 - C 1) * (D 0 - C 0)) *
      ((B 0 - C 0) * (D 1 - C 1) - (B 1 - C 1) * (D 0 - C 0)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hdet1) hdet2
  have hinner : (T₁.circumcenter 0 - C 0) * (T₂.circumcenter 0 - C 0) +
      (T₁.circumcenter 1 - C 1) * (T₂.circumcenter 1 - C 1) = 0 := by
    rcases mul_eq_zero.mp hK with h | h
    · exact h
    · exact absurd h hdd
  show ⟪T₁.circumcenter - C, T₂.circumcenter - C⟫ = 0
  rw [inner_pt]
  simp only [PiLp.sub_apply]
  exact hinner

end

end Imo1993P2
