/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.Geometry.Euclidean.Sphere.Basic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# USA Mathematical Olympiad 2019, Problem 2

Let `ABCD` be a cyclic quadrilateral satisfying `AD² + BC² = AB²`. The diagonals
of `ABCD` intersect at `E`. Let `P` be a point on side `AB` satisfying
`∠APD = ∠BPC`. Show that line `PE` bisects `CD`.
-/

open scoped EuclideanGeometry

open Affine EuclideanGeometry RealInnerProductSpace

noncomputable section

namespace Usa2019P2

abbrev Pt := EuclideanSpace ℝ (Fin 2)

snip begin

/-- Rotation by a right angle in the plane, used to build coordinates relative to the
line `AB`. -/
def J (v : Pt) : Pt := WithLp.toLp 2 ![-v 1, v 0]

/- The proof is a coordinate computation. We place `P` at the origin and use the unit
vector `u` along `AB` together with its rotation `J u` as an orthonormal frame. In this
frame the angle condition `∠APD = ∠BPC` says that the rays `PC` and `PD` are mirror
images in the perpendicular to `AB` at `P`; writing `C = c•(-X, S)` and `D = d•(X, S)`,
the concyclicity of `ABCD` and the condition `AD² + BC² = AB²` become two polynomial
equations, from which the conclusion (the intersection `E` of the diagonals, `P` and the
midpoint of `CD` are collinear) follows by an explicit polynomial identity. -/

lemma inner_J_left (u v : Pt) : ⟪J u, v⟫ = -⟪u, J v⟫ := by
  simp only [J, PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

lemma inner_self_J (u : Pt) : ⟪u, J u⟫ = 0 := by
  simp only [J, PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

lemma inner_J_J (u : Pt) : ⟪J u, J u⟫ = ⟪u, u⟫ := by
  simp only [J, PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- The two-dimensional Lagrange (Binet–Cauchy) identity. -/
lemma inner_mul_inner_eq (u v w : Pt) :
    ⟪v, w⟫ * ⟪u, u⟫ = ⟪v, u⟫ * ⟪w, u⟫ + ⟪v, J u⟫ * ⟪w, J u⟫ := by
  simp only [J, PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

lemma inner_eq_of_unit (u : Pt) (hu : ⟪u, u⟫ = 1) (v w : Pt) :
    ⟪v, w⟫ = ⟪v, u⟫ * ⟪w, u⟫ + ⟪v, J u⟫ * ⟪w, J u⟫ := by
  have h := inner_mul_inner_eq u v w
  rw [hu, mul_one] at h
  exact h

lemma norm_sq_eq_of_unit (u : Pt) (hu : ⟪u, u⟫ = 1) (v : Pt) :
    ‖v‖ ^ 2 = ⟪v, u⟫ ^ 2 + ⟪v, J u⟫ ^ 2 := by
  have h := inner_mul_inner_eq u v v
  rw [hu, mul_one] at h
  rw [← real_inner_self_eq_norm_sq, h]; ring

lemma dist_sq_eq_of_unit (u : Pt) (hu : ⟪u, u⟫ = 1) (x y : Pt) :
    dist x y ^ 2 = ⟪x -ᵥ y, u⟫ ^ 2 + ⟪x -ᵥ y, J u⟫ ^ 2 := by
  rw [dist_eq_norm_vsub, norm_sq_eq_of_unit u hu]

lemma eq_inner_smul_add_of_unit (u : Pt) (hu : ⟪u, u⟫ = 1) (v : Pt) :
    v = ⟪v, u⟫ • u + ⟪v, J u⟫ • J u := by
  have h1 : ⟪v - (⟪v, u⟫ • u + ⟪v, J u⟫ • J u), u⟫ = 0 := by
    rw [inner_sub_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      inner_J_left, inner_self_J, hu]
    ring
  have h2 : ⟪v - (⟪v, u⟫ • u + ⟪v, J u⟫ • J u), J u⟫ = 0 := by
    rw [inner_sub_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      inner_self_J, inner_J_J, hu]
    ring
  have h3 := inner_mul_inner_eq u (v - (⟪v, u⟫ • u + ⟪v, J u⟫ • J u))
    (v - (⟪v, u⟫ • u + ⟪v, J u⟫ • J u))
  rw [hu, mul_one, h1, h2] at h3
  simp only [mul_zero, add_zero] at h3
  have h4 : v - (⟪v, u⟫ • u + ⟪v, J u⟫ • J u) = 0 := inner_self_eq_zero.mp h3
  rw [sub_eq_zero] at h4
  exact h4

/-- A point whose difference vector is a multiple of `u` lies on the line through `P` in
direction `u`. -/
lemma mem_line_of_vsub_smul (P X u : Pt) (r : ℝ) (h : X -ᵥ P = r • u) :
    X ∈ line[ℝ, P, P +ᵥ u] := by
  have h2 : X = (X -ᵥ P) +ᵥ P := (vsub_vadd X P).symm
  have h3 : X = r • u + P := by rw [h2, h, vadd_eq_add]
  have h4 : (P +ᵥ u) - P = u := by rw [vadd_eq_add]; abel
  have hX : X = AffineMap.lineMap P (P +ᵥ u) r := by
    rw [AffineMap.lineMap_apply_module', h4, h3]
  rw [hX]
  exact AffineMap.lineMap_mem_affineSpan_pair r P (P +ᵥ u)

/-- The algebraic heart of the proof. With `a = PA`, `b = PB`, `c = PC`, `d = PD` and
coordinates `(aC, bC)`, `(aD, bD)`, `(aE, bE)` of `C`, `D`, `E` in the frame, the angle
condition gives `hR1` and `hR2`, the length condition `AD² + BC² = AB²` gives `hLEN`,
concyclicity gives `hCYC`, and `E` lying on both diagonals gives `hdet1` and `hdet2`.
The conclusion is the collinearity determinant of `P`, `E` and the midpoint of `CD`. -/
theorem core {a b c d aC bC aD bD aE bE : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hbC : bC ≠ 0) (hbD : bD ≠ 0)
    (hR1 : c * aD + d * aC = 0)
    (hR2 : d * bC - c * bD = 0)
    (hLEN : d ^ 2 + 2 * a * aD + a ^ 2 + (c ^ 2 - 2 * b * aC + b ^ 2) = (a + b) ^ 2)
    (hCYC : 2 * (a - b) * c * aD = (c - d) * (a * b + c * d))
    (hdet1 : (aE + a) * bC = bE * (aC + a))
    (hdet2 : (aE - b) * bD = bE * (aD - b)) :
    aE * (bC + bD) = bE * (aC + aD) := by
  have hGcd : (c + d) * (a ^ 2 * b * d - a * b ^ 2 * c + b * c * d ^ 2 - a * c ^ 2 * d) = 0 := by
    linear_combination -(a - b) * c * d * hLEN + (a * d + b * c) * hCYC - 2 * b * c * (a - b) * hR1
  have hG : a ^ 2 * b * d - a * b ^ 2 * c + b * c * d ^ 2 - a * c ^ 2 * d = 0 := by
    rcases mul_eq_zero.mp hGcd with h | h
    · exact absurd h (ne_of_gt (add_pos hc hd))
    · exact h
  have hG0 : (a - b) * (a * b * (d ^ 2 - c ^ 2) - 2 * c * aD * (b * d - a * c)) = 0 := by
    linear_combination (d - c) * hG - (b * d - a * c) * hCYC
  have hGOAL : a * b * (d ^ 2 - c ^ 2) = 2 * c * aD * (b * d - a * c) := by
    by_cases hab : a = b
    · rw [hab] at hCYC
      have hcd0 : (c - d) * (b * b + c * d) = 0 := by linear_combination -hCYC
      have hcd : c = d := by
        rcases mul_eq_zero.mp hcd0 with h | h
        · exact sub_eq_zero.mp h
        · have hpos : (0 : ℝ) < b * b + c * d := by positivity
          exact absurd h (ne_of_gt hpos)
      rw [hab, hcd]
      ring
    · rcases mul_eq_zero.mp hG0 with h | h
      · exact absurd (sub_eq_zero.mp h) hab
      · linear_combination h
  have he1 : (a + b) * c * bD = bE * (a * d + b * c - 2 * c * aD) := by
    linear_combination d * hdet1 - c * hdet2 - (aE + a) * hR2 + bE * hR1
  have he2b : bC * (aE * (a * d + b * c - 2 * c * aD) - ((a - b) * c * aD + a * b * (d - c))) = 0 := by
    linear_combination c * (aC + a) * hdet2 - c * (aD - b) * hdet1 + bC * (b - aE) * hR1 + (aE - b) * (aC + a) * hR2
  have he2 : aE * (a * d + b * c - 2 * c * aD) = (a - b) * c * aD + a * b * (d - c) := by
    rcases mul_eq_zero.mp he2b with h | h
    · exact absurd h hbC
    · linear_combination h
  have hDelta : (a * d + b * c - 2 * c * aD) ≠ 0 := by
    intro hD
    rw [hD, mul_zero] at he1
    exact absurd he1 (mul_ne_zero (mul_ne_zero (ne_of_gt (add_pos ha hb)) (ne_of_gt hc)) hbD)
  have hfin : d * (a * d + b * c - 2 * c * aD) * (aE * (bC + bD) - bE * (aC + aD)) = 0 := by
    linear_combination bD * hGOAL - (a + b) * c * bD * hR1 + ((a - b) * c * aD + a * b * (d - c)) * hR2 + d * (aC + aD) * he1 + d * (bC + bD) * he2
  rcases mul_eq_zero.mp hfin with h | h
  · rcases mul_eq_zero.mp h with h1 | h2
    · exact absurd h1 hd.ne'
    · exact absurd h2 hDelta
  · linear_combination h

snip end

problem usa2019_p2 (A B C D E P : Pt)
    (hcyc : Cospherical ({A, B, C, D} : Set Pt))
    (hlen : dist A D ^ 2 + dist B C ^ 2 = dist A B ^ 2)
    (hEAC : Sbtw ℝ A E C) (hEBD : Sbtw ℝ B E D)
    (hPAB : Wbtw ℝ A P B)
    (hang : ∠ A P D = ∠ B P C)
    -- Named side `AB` and quadrilateral vertices.
    (hAB : A ≠ B) (hBC : B ≠ C) (hAD : A ≠ D)
    -- Named angles.
    (hAP : A ≠ P) (hBP : B ≠ P) (hCP : C ≠ P) (hDP : D ≠ P)
    -- Named line in the conclusion.
    (hPE : P ≠ E) :
    midpoint ℝ C D ∈ line[ℝ, P, E] := by
  have hAC : A ≠ C := hEAC.left_ne_right
  have hBD : B ≠ D := hEBD.left_ne_right
  have ha : 0 < dist P A := by rw [dist_comm]; exact dist_pos.mpr hAP
  have hb : 0 < dist P B := by rw [dist_comm]; exact dist_pos.mpr hBP
  have hc : 0 < dist P C := by rw [dist_comm]; exact dist_pos.mpr hCP
  have hd : 0 < dist P D := by rw [dist_comm]; exact dist_pos.mpr hDP
  -- The nondegeneracy hypothesis `P ≠ E` implicit in the named line `PE` is not needed
  -- for the proof; we simply reference it here.
  have hPE' := hPE
  -- The parameter of `P` on segment `AB`.
  have hWbtw := hPAB
  obtain ⟨tP, htP, hPt⟩ := hPAB
  have htP0 : tP ≠ 0 := by
    intro h0
    apply hAP
    rw [← hPt, h0, AffineMap.lineMap_apply_zero]
  have htP1 : tP ≠ 1 := by
    intro h1
    apply hBP
    rw [← hPt, h1, AffineMap.lineMap_apply_one]
  -- The adapted orthonormal frame.
  generalize hu_def : (dist A B)⁻¹ • (B -ᵥ A) = u
  have hnu : ‖u‖ = 1 := by
    have h1 : ‖B -ᵥ A‖ = dist A B := by rw [← dist_eq_norm_vsub, dist_comm]
    rw [← hu_def, norm_smul, Real.norm_eq_abs, abs_inv, h1, abs_of_nonneg dist_nonneg,
      inv_mul_cancel₀ (ne_of_gt (dist_pos.mpr hAB))]
  have hu1 : ⟪u, u⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hnu, one_pow]
  have hBAu : B -ᵥ A = dist A B • u := by
    rw [← hu_def, smul_smul, mul_inv_cancel₀ (ne_of_gt (dist_pos.mpr hAB)), one_smul]
  have hPAv' : P -ᵥ A = tP • (B -ᵥ A) := by
    have h : P = tP • (B -ᵥ A) +ᵥ A := by rw [← hPt, AffineMap.lineMap_apply]
    rw [h, vadd_vsub]
  have hdPA : dist P A = tP * dist A B := by
    rw [dist_eq_norm_vsub, hPAv', norm_smul, Real.norm_eq_abs, abs_of_nonneg htP.1,
      ← dist_eq_norm_vsub, dist_comm B A]
  have hPAv : P -ᵥ A = dist P A • u := by
    rw [hPAv', hBAu, smul_smul, hdPA]
  have hAv : A -ᵥ P = -(dist P A) • u := by
    rw [← neg_vsub_eq_vsub_rev, hPAv, neg_smul]
  have hdPB : dist P B = (1 - tP) * dist A B := by
    have h := Wbtw.dist_add_dist hWbtw
    rw [dist_comm A P, hdPA] at h
    have h2 : dist P B = dist A B - tP * dist A B := by linarith
    rw [h2]; ring
  have hBv : B -ᵥ P = dist P B • u := by
    have h1 : (B -ᵥ A) - (P -ᵥ A) = B -ᵥ P := vsub_sub_vsub_cancel_right B P A
    have h2 : dist A B • u - (tP * dist A B) • u = dist P B • u := by
      rw [← sub_smul, hdPB, sub_mul, one_mul]
    rw [← h1, hPAv', hBAu, smul_smul, h2]
  -- The parameters of `E` on the two diagonals.
  obtain ⟨t, ht, htE⟩ := hEAC.1
  have ht0 : t ≠ 0 := by
    intro h0
    apply hEAC.2.1
    rw [← htE, h0, AffineMap.lineMap_apply_zero]
  have ht1 : t ≠ 1 := by
    intro h1
    apply hEAC.2.2
    rw [← htE, h1, AffineMap.lineMap_apply_one]
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  obtain ⟨s, hs, hsE⟩ := hEBD.1
  have hs0 : s ≠ 0 := by
    intro h0
    apply hEBD.2.1
    rw [← hsE, h0, AffineMap.lineMap_apply_zero]
  have hs1 : s ≠ 1 := by
    intro h1
    apply hEBD.2.2
    rw [← hsE, h1, AffineMap.lineMap_apply_one]
  have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
  have htE' : E -ᵥ A = t • (C -ᵥ A) := by
    have h : E = t • (C -ᵥ A) +ᵥ A := by rw [← htE, AffineMap.lineMap_apply]
    rw [h, vadd_vsub]
  have hsE' : E -ᵥ B = s • (D -ᵥ B) := by
    have h : E = s • (D -ᵥ B) +ᵥ B := by rw [← hsE, AffineMap.lineMap_apply]
    rw [h, vadd_vsub]
  have hE1 : E -ᵥ P = (A -ᵥ P) + t • ((C -ᵥ P) - (A -ᵥ P)) := by
    rw [← vsub_add_vsub_cancel E A P, htE',
      show C -ᵥ A = (C -ᵥ P) - (A -ᵥ P) from (vsub_sub_vsub_cancel_right C A P).symm,
      add_comm]
  have hE2 : E -ᵥ P = (B -ᵥ P) + s • ((D -ᵥ P) - (B -ᵥ P)) := by
    rw [← vsub_add_vsub_cancel E B P, hsE',
      show D -ᵥ B = (D -ᵥ P) - (B -ᵥ P) from (vsub_sub_vsub_cancel_right D B P).symm,
      add_comm]
  -- Coordinates of `A` and `B` in the frame.
  have hiA : ⟪A -ᵥ P, u⟫ = -dist P A := by
    rw [hAv, real_inner_smul_left, hu1]; ring
  have hiAJ : ⟪A -ᵥ P, J u⟫ = 0 := by
    rw [hAv, real_inner_smul_left, inner_self_J]; ring
  have hiB : ⟪B -ᵥ P, u⟫ = dist P B := by
    rw [hBv, real_inner_smul_left, hu1]; ring
  have hiBJ : ⟪B -ᵥ P, J u⟫ = 0 := by
    rw [hBv, real_inner_smul_left, inner_self_J]; ring
  -- The angle condition, in coordinates: the rays `PC` and `PD` are mirror images in
  -- the perpendicular to `AB` at `P`.
  have hcos : Real.cos (∠ A P D) = Real.cos (∠ B P C) := by rw [hang]
  unfold EuclideanGeometry.angle at hcos
  rw [InnerProductGeometry.cos_angle, InnerProductGeometry.cos_angle] at hcos
  have hnA : ‖A -ᵥ P‖ = dist P A := by rw [← dist_eq_norm_vsub, dist_comm]
  have hnB : ‖B -ᵥ P‖ = dist P B := by rw [← dist_eq_norm_vsub, dist_comm]
  have hnC : ‖C -ᵥ P‖ = dist P C := by rw [← dist_eq_norm_vsub, dist_comm]
  have hnD : ‖D -ᵥ P‖ = dist P D := by rw [← dist_eq_norm_vsub, dist_comm]
  rw [hnA, hnB, hnC, hnD] at hcos
  have hinnerAD : ⟪A -ᵥ P, D -ᵥ P⟫ = -dist P A * ⟪D -ᵥ P, u⟫ := by
    rw [inner_eq_of_unit u hu1, hiA, hiAJ]; ring
  have hinnerBC : ⟪B -ᵥ P, C -ᵥ P⟫ = dist P B * ⟪C -ᵥ P, u⟫ := by
    rw [inner_eq_of_unit u hu1, hiB, hiBJ]; ring
  rw [hinnerAD, hinnerBC] at hcos
  rw [div_eq_div_iff (mul_ne_zero ha.ne' hd.ne') (mul_ne_zero hb.ne' hc.ne')] at hcos
  have hR1 : dist P C * ⟪D -ᵥ P, u⟫ + dist P D * ⟪C -ᵥ P, u⟫ = 0 := by
    have h2 : dist P A * dist P B * (dist P C * ⟪D -ᵥ P, u⟫ + dist P D * ⟪C -ᵥ P, u⟫) = 0 := by
      linear_combination -hcos
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h (mul_ne_zero ha.ne' hb.ne')
    · exact h
  -- `C` and `D` are on the same side of `AB`, and off the line `AB`.
  have hbE1 : ⟪E -ᵥ P, J u⟫ = t * ⟪C -ᵥ P, J u⟫ := by
    rw [hE1, inner_add_left, real_inner_smul_left, inner_sub_left, hiAJ]; ring
  have hbE2 : ⟪E -ᵥ P, J u⟫ = s * ⟪D -ᵥ P, J u⟫ := by
    rw [hE2, inner_add_left, real_inner_smul_left, inner_sub_left, hiBJ]; ring
  have hsign : t * ⟪C -ᵥ P, J u⟫ = s * ⟪D -ᵥ P, J u⟫ := by rw [← hbE1, ← hbE2]
  have hNc : dist P C ^ 2 = ⟪C -ᵥ P, u⟫ ^ 2 + ⟪C -ᵥ P, J u⟫ ^ 2 := by
    rw [dist_eq_norm_vsub, ← neg_vsub_eq_vsub_rev, norm_neg, norm_sq_eq_of_unit u hu1]
  have hNd : dist P D ^ 2 = ⟪D -ᵥ P, u⟫ ^ 2 + ⟪D -ᵥ P, J u⟫ ^ 2 := by
    rw [dist_eq_norm_vsub, ← neg_vsub_eq_vsub_rev, norm_neg, norm_sq_eq_of_unit u hu1]
  have hsubABC : ({A, B, C} : Set Pt) ⊆ {A, B, C, D} := by
    rw [Set.insert_subset_iff, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨by simp, by simp, by simp⟩
  have hsubABD : ({A, B, D} : Set Pt) ⊆ {A, B, C, D} := by
    rw [Set.insert_subset_iff, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨by simp, by simp, by simp⟩
  have hAI1 : AffineIndependent ℝ ![A, B, C] :=
    (hcyc.subset hsubABC).affineIndependent_of_ne hAB hAC hBC
  have hAI2 : AffineIndependent ℝ ![A, B, D] :=
    (hcyc.subset hsubABD).affineIndependent_of_ne hAB hAD hBD
  have hbC : ⟪C -ᵥ P, J u⟫ ≠ 0 := by
    intro hz
    have hCv : C -ᵥ P = ⟪C -ᵥ P, u⟫ • u := by
      have h := eq_inner_smul_add_of_unit u hu1 (C -ᵥ P)
      rw [hz, zero_smul, add_zero] at h
      exact h
    exact (affineIndependent_iff_not_collinear_set.1 hAI1)
      (collinear_triple_of_mem_affineSpan_pair
        (mem_line_of_vsub_smul P A u (-(dist P A)) hAv)
        (mem_line_of_vsub_smul P B u (dist P B) hBv)
        (mem_line_of_vsub_smul P C u _ hCv))
  have hbD : ⟪D -ᵥ P, J u⟫ ≠ 0 := by
    intro hz
    have hDv : D -ᵥ P = ⟪D -ᵥ P, u⟫ • u := by
      have h := eq_inner_smul_add_of_unit u hu1 (D -ᵥ P)
      rw [hz, zero_smul, add_zero] at h
      exact h
    exact (affineIndependent_iff_not_collinear_set.1 hAI2)
      (collinear_triple_of_mem_affineSpan_pair
        (mem_line_of_vsub_smul P A u (-(dist P A)) hAv)
        (mem_line_of_vsub_smul P B u (dist P B) hBv)
        (mem_line_of_vsub_smul P D u _ hDv))
  have hR2 : dist P D * ⟪C -ᵥ P, J u⟫ - dist P C * ⟪D -ᵥ P, J u⟫ = 0 := by
    have hsq1 : (dist P C * ⟪D -ᵥ P, u⟫) ^ 2 = (dist P D * ⟪C -ᵥ P, u⟫) ^ 2 := by
      have h1 : dist P C * ⟪D -ᵥ P, u⟫ = -(dist P D * ⟪C -ᵥ P, u⟫) := by
        linear_combination hR1
      rw [h1, neg_sq]
    have hsq : (dist P D * ⟪C -ᵥ P, J u⟫) ^ 2 = (dist P C * ⟪D -ᵥ P, J u⟫) ^ 2 := by
      linear_combination -dist P D ^ 2 * hNc + dist P C ^ 2 * hNd + hsq1
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
    · linear_combination h
    · exfalso
      have hbDeq : ⟪D -ᵥ P, J u⟫ = (t / s) * ⟪C -ᵥ P, J u⟫ := by
        rw [div_mul_eq_mul_div, eq_div_iff hspos.ne', mul_comm ⟪D -ᵥ P, J u⟫ s, ← hsign]
      rw [hbDeq] at h
      have hz : (dist P D + dist P C * (t / s)) * ⟪C -ᵥ P, J u⟫ = 0 := by
        linear_combination h
      rcases mul_eq_zero.mp hz with h3 | h3
      · have hts : 0 < t / s := div_pos htpos hspos
        have hpos : 0 < dist P D + dist P C * (t / s) := add_pos hd (mul_pos hc hts)
        exact absurd h3 (ne_of_gt hpos)
      · exact hbC h3
  -- The length condition `AD² + BC² = AB²`, in coordinates.
  have hdAD : dist A D ^ 2 = dist P D ^ 2 + 2 * dist P A * ⟪D -ᵥ P, u⟫ + dist P A ^ 2 := by
    rw [dist_sq_eq_of_unit u hu1 A D]
    have h1 : ⟪A -ᵥ D, u⟫ = -dist P A - ⟪D -ᵥ P, u⟫ := by
      rw [← vsub_sub_vsub_cancel_right A D P, inner_sub_left, hiA]
    have h2 : ⟪A -ᵥ D, J u⟫ = -⟪D -ᵥ P, J u⟫ := by
      rw [← vsub_sub_vsub_cancel_right A D P, inner_sub_left, hiAJ]; ring
    rw [h1, h2]
    linear_combination -hNd
  have hdBC : dist B C ^ 2 = dist P C ^ 2 - 2 * dist P B * ⟪C -ᵥ P, u⟫ + dist P B ^ 2 := by
    rw [dist_sq_eq_of_unit u hu1 B C]
    have h1 : ⟪B -ᵥ C, u⟫ = dist P B - ⟪C -ᵥ P, u⟫ := by
      rw [← vsub_sub_vsub_cancel_right B C P, inner_sub_left, hiB]
    have h2 : ⟪B -ᵥ C, J u⟫ = -⟪C -ᵥ P, J u⟫ := by
      rw [← vsub_sub_vsub_cancel_right B C P, inner_sub_left, hiBJ]; ring
    rw [h1, h2]
    linear_combination -hNc
  have hdAB : dist A B = dist P A + dist P B := by
    have h := Wbtw.dist_add_dist hWbtw
    rw [dist_comm A P] at h
    linarith
  have hdAB2 : dist A B ^ 2 = (dist P A + dist P B) ^ 2 := by rw [hdAB]
  have hLEN : dist P D ^ 2 + 2 * dist P A * ⟪D -ᵥ P, u⟫ + dist P A ^ 2 +
      (dist P C ^ 2 - 2 * dist P B * ⟪C -ᵥ P, u⟫ + dist P B ^ 2) =
      (dist P A + dist P B) ^ 2 := by
    linear_combination hlen - hdAD - hdBC + hdAB2
  -- Concyclicity, in coordinates.
  obtain ⟨O, r, hO⟩ := hcyc
  have hsA : dist A O ^ 2 = ⟪A -ᵥ O, u⟫ ^ 2 + ⟪A -ᵥ O, J u⟫ ^ 2 := dist_sq_eq_of_unit u hu1 A O
  have hsB : dist B O ^ 2 = ⟪B -ᵥ O, u⟫ ^ 2 + ⟪B -ᵥ O, J u⟫ ^ 2 := dist_sq_eq_of_unit u hu1 B O
  have hsC : dist C O ^ 2 = ⟪C -ᵥ O, u⟫ ^ 2 + ⟪C -ᵥ O, J u⟫ ^ 2 := dist_sq_eq_of_unit u hu1 C O
  have hsD : dist D O ^ 2 = ⟪D -ᵥ O, u⟫ ^ 2 + ⟪D -ᵥ O, J u⟫ ^ 2 := dist_sq_eq_of_unit u hu1 D O
  have hgA1 : ⟪A -ᵥ O, u⟫ = -dist P A - ⟪O -ᵥ P, u⟫ := by
    rw [← vsub_sub_vsub_cancel_right A O P, inner_sub_left, hiA]
  have hgA2 : ⟪A -ᵥ O, J u⟫ = -⟪O -ᵥ P, J u⟫ := by
    rw [← vsub_sub_vsub_cancel_right A O P, inner_sub_left, hiAJ]; ring
  have hgB1 : ⟪B -ᵥ O, u⟫ = dist P B - ⟪O -ᵥ P, u⟫ := by
    rw [← vsub_sub_vsub_cancel_right B O P, inner_sub_left, hiB]
  have hgB2 : ⟪B -ᵥ O, J u⟫ = -⟪O -ᵥ P, J u⟫ := by
    rw [← vsub_sub_vsub_cancel_right B O P, inner_sub_left, hiBJ]; ring
  have hgC1 : ⟪C -ᵥ O, u⟫ = ⟪C -ᵥ P, u⟫ - ⟪O -ᵥ P, u⟫ := by
    rw [← vsub_sub_vsub_cancel_right C O P, inner_sub_left]
  have hgC2 : ⟪C -ᵥ O, J u⟫ = ⟪C -ᵥ P, J u⟫ - ⟪O -ᵥ P, J u⟫ := by
    rw [← vsub_sub_vsub_cancel_right C O P, inner_sub_left]
  have hgD1 : ⟪D -ᵥ O, u⟫ = ⟪D -ᵥ P, u⟫ - ⟪O -ᵥ P, u⟫ := by
    rw [← vsub_sub_vsub_cancel_right D O P, inner_sub_left]
  have hgD2 : ⟪D -ᵥ O, J u⟫ = ⟪D -ᵥ P, J u⟫ - ⟪O -ᵥ P, J u⟫ := by
    rw [← vsub_sub_vsub_cancel_right D O P, inner_sub_left]
  have heq1 : 2 * ⟪O -ᵥ P, u⟫ * (dist P A + dist P B) = dist P B ^ 2 - dist P A ^ 2 := by
    have h1 : dist A O ^ 2 = dist B O ^ 2 := by rw [hO A (by simp), hO B (by simp)]
    rw [hsA, hsB, hgA1, hgA2, hgB1, hgB2] at h1
    linear_combination h1
  have heq2 : 2 * ⟪O -ᵥ P, J u⟫ * ⟪D -ᵥ P, J u⟫ =
      dist P D ^ 2 - dist P A ^ 2 - 2 * ⟪O -ᵥ P, u⟫ * (⟪D -ᵥ P, u⟫ + dist P A) := by
    have h1 : dist D O ^ 2 = dist A O ^ 2 := by rw [hO D (by simp), hO A (by simp)]
    rw [hsD, hsA, hgD1, hgD2, hgA1, hgA2] at h1
    linear_combination -h1 - hNd
  have heq3 : 2 * ⟪O -ᵥ P, J u⟫ * ⟪C -ᵥ P, J u⟫ =
      dist P C ^ 2 - dist P A ^ 2 - 2 * ⟪O -ᵥ P, u⟫ * (⟪C -ᵥ P, u⟫ + dist P A) := by
    have h1 : dist C O ^ 2 = dist A O ^ 2 := by rw [hO C (by simp), hO A (by simp)]
    rw [hsC, hsA, hgC1, hgC2, hgA1, hgA2] at h1
    linear_combination -h1 - hNc
  have hg1 : 2 * ⟪O -ᵥ P, u⟫ = dist P B - dist P A := by
    have h1 : 2 * ⟪O -ᵥ P, u⟫ * (dist P A + dist P B) =
        (dist P B - dist P A) * (dist P A + dist P B) := by linear_combination heq1
    exact mul_right_cancel₀ (ne_of_gt (add_pos ha hb)) h1
  have hUD : 2 * ⟪O -ᵥ P, J u⟫ * ⟪D -ᵥ P, J u⟫ =
      dist P D ^ 2 - dist P A ^ 2 - (dist P B - dist P A) * (⟪D -ᵥ P, u⟫ + dist P A) := by
    linear_combination heq2 - (⟪D -ᵥ P, u⟫ + dist P A) * hg1
  have hUC : 2 * ⟪O -ᵥ P, J u⟫ * ⟪C -ᵥ P, J u⟫ =
      dist P C ^ 2 - dist P A ^ 2 - (dist P B - dist P A) * (⟪C -ᵥ P, u⟫ + dist P A) := by
    linear_combination heq3 - (⟪C -ᵥ P, u⟫ + dist P A) * hg1
  have helim : ⟪C -ᵥ P, J u⟫ * (dist P D ^ 2 - dist P A ^ 2 -
        (dist P B - dist P A) * (⟪D -ᵥ P, u⟫ + dist P A)) =
      ⟪D -ᵥ P, J u⟫ * (dist P C ^ 2 - dist P A ^ 2 -
        (dist P B - dist P A) * (⟪C -ᵥ P, u⟫ + dist P A)) := by
    linear_combination ⟪D -ᵥ P, J u⟫ * hUC - ⟪C -ᵥ P, J u⟫ * hUD
  have hcd : ⟪D -ᵥ P, J u⟫ * (dist P C * (dist P D ^ 2 - dist P A ^ 2 -
        (dist P B - dist P A) * (⟪D -ᵥ P, u⟫ + dist P A)) -
      dist P D * (dist P C ^ 2 - dist P A ^ 2 -
        (dist P B - dist P A) * (⟪C -ᵥ P, u⟫ + dist P A))) = 0 := by
    linear_combination dist P D * helim -
      (dist P D ^ 2 - dist P A ^ 2 - (dist P B - dist P A) * (⟪D -ᵥ P, u⟫ + dist P A)) * hR2
  have hcd' : dist P C * (dist P D ^ 2 - dist P A ^ 2 -
        (dist P B - dist P A) * (⟪D -ᵥ P, u⟫ + dist P A)) =
      dist P D * (dist P C ^ 2 - dist P A ^ 2 -
        (dist P B - dist P A) * (⟪C -ᵥ P, u⟫ + dist P A)) := by
    rcases mul_eq_zero.mp hcd with h | h
    · exact absurd h hbD
    · linear_combination h
  have hCYC : 2 * (dist P A - dist P B) * dist P C * ⟪D -ᵥ P, u⟫ =
      (dist P C - dist P D) * (dist P A * dist P B + dist P C * dist P D) := by
    linear_combination hcd' + (dist P A - dist P B) * hR1
  -- `E` lies on both diagonals, in coordinates.
  have haE1 : ⟪E -ᵥ P, u⟫ = -dist P A + t * (⟪C -ᵥ P, u⟫ + dist P A) := by
    rw [hE1, inner_add_left, real_inner_smul_left, inner_sub_left, hiA]; ring
  have hdet1 : (⟪E -ᵥ P, u⟫ + dist P A) * ⟪C -ᵥ P, J u⟫ =
      ⟪E -ᵥ P, J u⟫ * (⟪C -ᵥ P, u⟫ + dist P A) := by
    rw [haE1, hbE1]; ring
  have haE2 : ⟪E -ᵥ P, u⟫ = dist P B + s * (⟪D -ᵥ P, u⟫ - dist P B) := by
    rw [hE2, inner_add_left, real_inner_smul_left, inner_sub_left, hiB]
  have hdet2 : (⟪E -ᵥ P, u⟫ - dist P B) * ⟪D -ᵥ P, J u⟫ =
      ⟪E -ᵥ P, J u⟫ * (⟪D -ᵥ P, u⟫ - dist P B) := by
    rw [haE2, hbE2]; ring
  -- The polynomial heart of the proof.
  have hdetG : ⟪E -ᵥ P, u⟫ * (⟪C -ᵥ P, J u⟫ + ⟪D -ᵥ P, J u⟫) =
      ⟪E -ᵥ P, J u⟫ * (⟪C -ᵥ P, u⟫ + ⟪D -ᵥ P, u⟫) :=
    core ha hb hc hd hbC hbD hR1 hR2 hLEN hCYC hdet1 hdet2
  -- Conclusion: the midpoint of `CD` lies on line `PE`.
  have hbE : ⟪E -ᵥ P, J u⟫ ≠ 0 := by
    rw [hbE1]; exact mul_ne_zero htpos.ne' hbC
  set r₀ : ℝ := (⟪C -ᵥ P, J u⟫ + ⟪D -ᵥ P, J u⟫) / (2 * ⟪E -ᵥ P, J u⟫) with hr₀
  have h3 : r₀ * ⟪E -ᵥ P, J u⟫ = (⟪C -ᵥ P, J u⟫ + ⟪D -ᵥ P, J u⟫) / 2 := by
    rw [hr₀]; field_simp [hbE]
  have h4 : r₀ * ⟪E -ᵥ P, u⟫ = (⟪C -ᵥ P, u⟫ + ⟪D -ᵥ P, u⟫) / 2 := by
    rw [hr₀]; field_simp [hbE]; linear_combination hdetG
  have hMv : midpoint ℝ C D -ᵥ P = r₀ • (E -ᵥ P) := by
    have hL := eq_inner_smul_add_of_unit u hu1 (midpoint ℝ C D -ᵥ P)
    have hR := eq_inner_smul_add_of_unit u hu1 (r₀ • (E -ᵥ P))
    have h1 : ⟪midpoint ℝ C D -ᵥ P, u⟫ = (⟪C -ᵥ P, u⟫ + ⟪D -ᵥ P, u⟫) / 2 := by
      rw [midpoint_vsub, inner_add_left, real_inner_smul_left, real_inner_smul_left,
        invOf_eq_inv]; ring
    have h2 : ⟪midpoint ℝ C D -ᵥ P, J u⟫ = (⟪C -ᵥ P, J u⟫ + ⟪D -ᵥ P, J u⟫) / 2 := by
      rw [midpoint_vsub, inner_add_left, real_inner_smul_left, real_inner_smul_left,
        invOf_eq_inv]; ring
    rw [h1, h2] at hL
    rw [real_inner_smul_left, real_inner_smul_left, h3, h4] at hR
    rw [hL, hR]
  have hM : midpoint ℝ C D = AffineMap.lineMap P E r₀ := by
    rw [AffineMap.lineMap_apply, ← hMv, vsub_vadd]
  rw [hM]
  exact AffineMap.lineMap_mem_affineSpan_pair r₀ P E

end Usa2019P2

end
