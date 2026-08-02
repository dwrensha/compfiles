/-
Copyright (c) 2026 Kimi Code. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry, .Inequality] }

/-!
# International Mathematical Olympiad 1967, Problem 2

Prove that a tetrahedron with just one edge length greater than 1 has
volume at most 1/8.

# Formalization notes

We take the four vertices of the tetrahedron to be points of 3-dimensional
Euclidean space, and we define the volume by the classical determinant
formula `V = |det| / 6` for the determinant of the three edge vectors
emanating from one vertex (this is one sixth of the volume of the
parallelipiped spanned by the edge vectors).  The hypothesis
"just one edge length greater than 1" is formalized as a disjunction:
one of the six edges may have arbitrary length while the other five
edges have length at most `1`.
-/

namespace Imo1967P2

open scoped InnerProductSpace RealInnerProductSpace Matrix

/-- The edge matrix of a tetrahedron with vertices `A`, `B`, `C`, `D`:
its columns are the three edge vectors from `A` to the other vertices. -/
noncomputable def edgeMat (A B C D : EuclideanSpace ℝ (Fin 3)) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j => ![B - A, C - A, D - A] j i

/-- The volume of a tetrahedron with vertices `A`, `B`, `C`, `D`,
given by the determinant formula `V = |det| / 6`. -/
noncomputable def tetrahedronVolume (A B C D : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  |(edgeMat A B C D).det| / 6

snip begin

/-- Moving the reference vertex of the edge matrix from `A` to `C`
does not change the determinant. -/
lemma det_edgeMat_eq (A B C D : EuclideanSpace ℝ (Fin 3)) :
    (edgeMat A B C D).det =
      (Matrix.of fun i j => ![B - C, D - C, A - C] j i).det := by
  rw [Matrix.det_fin_three, Matrix.det_fin_three]
  simp only [edgeMat, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, PiLp.sub_apply]
  ring

/-- The entries of the Gram matrix of three vectors in `ℝ³` are the
pairwise inner products. -/
lemma gram_entry (v : Fin 3 → EuclideanSpace ℝ (Fin 3)) (i j : Fin 3) :
    ((Matrix.of fun r c => v c r).transpose * Matrix.of fun r c => v c r) i j =
      ⟪v i, v j⟫_ℝ := by
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply, Matrix.of_apply]
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [RCLike.inner_apply]
  simp [mul_comm]

/-- The square of the determinant of the matrix with columns `b'`, `e`, `a'`,
expressed as a polynomial in the pairwise inner products
(the Gram determinant). -/
lemma det_sq_eq_gram_poly (b' e a' : EuclideanSpace ℝ (Fin 3)) :
    ((Matrix.of fun i j => ![b', e, a'] j i).det) ^ 2 =
      ⟪b', b'⟫_ℝ * ⟪e, e⟫_ℝ * ⟪a', a'⟫_ℝ - ⟪b', b'⟫_ℝ * ⟪a', e⟫_ℝ ^ 2 -
        ⟪e, e⟫_ℝ * ⟪b', a'⟫_ℝ ^ 2 - ⟪a', a'⟫_ℝ * ⟪b', e⟫_ℝ ^ 2 +
        2 * ⟪b', e⟫_ℝ * ⟪a', e⟫_ℝ * ⟪b', a'⟫_ℝ := by
  have hdet2 : ((Matrix.of fun i j => ![b', e, a'] j i).det) ^ 2 =
      ((Matrix.of fun i j => ![b', e, a'] j i).transpose *
        Matrix.of fun i j => ![b', e, a'] j i).det := by
    rw [Matrix.det_mul, Matrix.det_transpose, pow_two]
  rw [hdet2, Matrix.det_fin_three]
  simp only [gram_entry, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [real_inner_comm b' e, real_inner_comm b' a', real_inner_comm a' e]
  ring

/-- The key estimate.  Write `e = D - C` for the edge shared by the two faces
`BCD` and `ACD`, and decompose `B - C` and `A - C` into components parallel and
perpendicular to `e`.  If `s = ‖e‖²`, `β = ⟪B - C, e⟫` and `α = ⟪A - C, e⟫`,
the Gram determinant factors as
`s⁻¹ ((‖B - C‖² s - β²)(‖A - C‖² s - α²) - (⟪B - C, A - C⟫ s - αβ)²)`,
which is at most `s (1 - s / 4)²` since each of `‖B - C‖² - β² / s` and
`‖A - C‖² - α² / s` (the squared distances of `B` and `A` from the line `CD`)
is at most `1 - s / 4`. -/
lemma det_sq_le (A B C D : EuclideanSpace ℝ (Fin 3))
    (hAC : dist A C ≤ 1) (hAD : dist A D ≤ 1)
    (hBC : dist B C ≤ 1) (hBD : dist B D ≤ 1) (hCD : dist C D ≤ 1) :
    ((Matrix.of fun i j => ![B - C, D - C, A - C] j i).det) ^ 2 ≤
      (dist C D * (1 - dist C D ^ 2 / 4)) ^ 2 := by
  rw [det_sq_eq_gram_poly]
  set s := ⟪D - C, D - C⟫_ℝ with hs
  set β := ⟪B - C, D - C⟫_ℝ with hβ
  set α := ⟪A - C, D - C⟫_ℝ with hα
  set bb := ⟪B - C, B - C⟫_ℝ with hbb
  set aa := ⟪A - C, A - C⟫_ℝ with haa
  set pp := ⟪B - C, A - C⟫_ℝ with hpp
  have hs_norm : s = ‖D - C‖ ^ 2 := real_inner_self_eq_norm_sq (D - C)
  have hbb_norm : bb = ‖B - C‖ ^ 2 := real_inner_self_eq_norm_sq (B - C)
  have haa_norm : aa = ‖A - C‖ ^ 2 := real_inner_self_eq_norm_sq (A - C)
  have hs_nonneg : 0 ≤ s := real_inner_self_nonneg
  rw [dist_eq_norm] at hBC hBD hAC hAD hCD
  have hCDn : ‖D - C‖ ≤ 1 := by rw [norm_sub_rev]; exact hCD
  have hbb1 : bb ≤ 1 := by rw [hbb_norm]; exact pow_le_one₀ (norm_nonneg _) hBC
  have haa1 : aa ≤ 1 := by rw [haa_norm]; exact pow_le_one₀ (norm_nonneg _) hAC
  have hs1 : s ≤ 1 := by rw [hs_norm]; exact pow_le_one₀ (norm_nonneg _) hCDn
  have hbe : bb - 2 * β + s ≤ 1 := by
    have h : ‖(B - C) - (D - C)‖ ^ 2 ≤ 1 := by
      have hsub : (B - C) - (D - C) = B - D := by abel
      rw [hsub]
      exact pow_le_one₀ (norm_nonneg _) hBD
    rw [norm_sub_sq_real, ← hbb_norm, ← hs_norm, ← hβ] at h
    exact h
  have hae : aa - 2 * α + s ≤ 1 := by
    have h : ‖(A - C) - (D - C)‖ ^ 2 ≤ 1 := by
      have hsub : (A - C) - (D - C) = A - D := by abel
      rw [hsub]
      exact pow_le_one₀ (norm_nonneg _) hAD
    rw [norm_sub_sq_real, ← haa_norm, ← hs_norm, ← hα] at h
    exact h
  have hnn_b : 0 ≤ bb * s - β ^ 2 := by
    have h := real_inner_mul_inner_self_le (B - C) (D - C)
    rw [← hbb, ← hs, ← hβ] at h
    nlinarith [h]
  have hnn_a : 0 ≤ aa * s - α ^ 2 := by
    have h := real_inner_mul_inner_self_le (A - C) (D - C)
    rw [← haa, ← hs, ← hα] at h
    nlinarith [h]
  have hb_key : bb * s - β ^ 2 ≤ s * (1 - s / 4) := by
    have h2 : 0 ≤ 1 - (bb - 2 * β + s) / 2 - bb / 2 := by linarith [hbe, hbb1]
    have h3 : 0 ≤ s * (1 - (bb - 2 * β + s) / 2 - bb / 2) := mul_nonneg hs_nonneg h2
    nlinarith [sq_nonneg (β - s / 2), h3]
  have ha_key : aa * s - α ^ 2 ≤ s * (1 - s / 4) := by
    have h2 : 0 ≤ 1 - (aa - 2 * α + s) / 2 - aa / 2 := by linarith [hae, haa1]
    have h3 : 0 ≤ s * (1 - (aa - 2 * α + s) / 2 - aa / 2) := mul_nonneg hs_nonneg h2
    nlinarith [sq_nonneg (α - s / 2), h3]
  have hs14 : 0 ≤ s * (1 - s / 4) := by
    have h4 : 0 ≤ 1 - s / 4 := by linarith [hs1]
    exact mul_nonneg hs_nonneg h4
  by_cases hs0 : s = 0
  · -- Degenerate case: `C = D`, so the tetrahedron has volume `0`.
    have hDC : D - C = 0 := inner_self_eq_zero.mp hs0
    have hβ0 : β = 0 := by rw [hβ, hDC]; exact inner_zero_right _
    have hα0 : α = 0 := by rw [hα, hDC]; exact inner_zero_right _
    have hd0 : dist C D = 0 := by
      rw [dist_eq_norm, show C - D = -(D - C) by abel, norm_neg, hDC, norm_zero]
    rw [hβ0, hα0, hs0, hd0]
    norm_num
  · have hs_pos : 0 < s := lt_of_le_of_ne hs_nonneg (Ne.symm hs0)
    have hKey : s * (bb * s * aa - bb * α ^ 2 - s * pp ^ 2 - aa * β ^ 2 +
        2 * β * α * pp)
        = (bb * s - β ^ 2) * (aa * s - α ^ 2) - (pp * s - β * α) ^ 2 := by ring
    have h1 : s * (bb * s * aa - bb * α ^ 2 - s * pp ^ 2 - aa * β ^ 2 +
        2 * β * α * pp)
        ≤ (bb * s - β ^ 2) * (aa * s - α ^ 2) := by
      rw [hKey]
      have hY : 0 ≤ (pp * s - β * α) ^ 2 := sq_nonneg _
      linarith [hY]
    have hmul : (bb * s - β ^ 2) * (aa * s - α ^ 2) ≤ (s * (1 - s / 4)) ^ 2 := by
      have h := mul_le_mul hb_key ha_key hnn_a hs14
      rwa [← pow_two (s * (1 - s / 4))] at h
    have h2 : s * (bb * s * aa - bb * α ^ 2 - s * pp ^ 2 - aa * β ^ 2 +
        2 * β * α * pp)
        ≤ s * (s * (1 - s / 4) ^ 2) := by
      have hrw : (s * (1 - s / 4)) ^ 2 = s * (s * (1 - s / 4) ^ 2) := by ring
      rw [hrw] at hmul
      exact le_trans h1 hmul
    have h3 := (mul_le_mul_iff_of_pos_left hs_pos).mp h2
    have hd : dist C D = ‖D - C‖ := by rw [dist_eq_norm, norm_sub_rev]
    have hRHS : (dist C D * (1 - dist C D ^ 2 / 4)) ^ 2 = s * (1 - s / 4) ^ 2 := by
      have e1 : (dist C D * (1 - dist C D ^ 2 / 4)) ^ 2
          = dist C D ^ 2 * (1 - dist C D ^ 2 / 4) ^ 2 := by ring
      rw [e1, hd, ← hs_norm]
    rw [hRHS]
    exact h3

/-- The core inequality: if all edges except possibly `AB` have length at
most `1`, then the volume of the tetrahedron is at most `1/8`. -/
lemma volume_le_one_eighth (A B C D : EuclideanSpace ℝ (Fin 3))
    (hAC : dist A C ≤ 1) (hAD : dist A D ≤ 1)
    (hBC : dist B C ≤ 1) (hBD : dist B D ≤ 1) (hCD : dist C D ≤ 1) :
    tetrahedronVolume A B C D ≤ 1 / 8 := by
  have hd : |(edgeMat A B C D).det| =
      |(Matrix.of fun i j => ![B - C, D - C, A - C] j i).det| := by
    rw [det_edgeMat_eq]
  have h2 := det_sq_le A B C D hAC hAD hBC hBD hCD
  set c := dist C D with hc
  have hc0 : 0 ≤ c := dist_nonneg
  have hc2 : c ^ 2 ≤ 1 := pow_le_one₀ hc0 hCD
  have h14 : 0 ≤ 1 - c ^ 2 / 4 := by nlinarith [hc2]
  have habs : |(Matrix.of fun i j => ![B - C, D - C, A - C] j i).det| ≤
      c * (1 - c ^ 2 / 4) := abs_le_of_sq_le_sq h2 (mul_nonneg hc0 h14)
  have hfin : c * (1 - c ^ 2 / 4) ≤ 3 / 4 := by
    have h1c : 0 ≤ 1 - c := sub_nonneg.mpr hCD
    have h2c : 0 ≤ 3 - c - c ^ 2 := by nlinarith [hc0, hCD]
    nlinarith [mul_nonneg h1c h2c]
  rw [tetrahedronVolume, hd]
  linarith [habs, hfin]

/-- Swapping two vertices of a tetrahedron negates the signed volume,
hence does not change the volume. -/
lemma volume_swap_bc (A B C D : EuclideanSpace ℝ (Fin 3)) :
    tetrahedronVolume A B C D = tetrahedronVolume A C B D := by
  have h : (edgeMat A B C D).det = -(edgeMat A C B D).det := by
    rw [Matrix.det_fin_three, Matrix.det_fin_three]
    simp only [edgeMat, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, PiLp.sub_apply]
    ring
  rw [tetrahedronVolume, tetrahedronVolume, h, abs_neg]

lemma volume_swap_bd (A B C D : EuclideanSpace ℝ (Fin 3)) :
    tetrahedronVolume A B C D = tetrahedronVolume A D C B := by
  have h : (edgeMat A B C D).det = -(edgeMat A D C B).det := by
    rw [Matrix.det_fin_three, Matrix.det_fin_three]
    simp only [edgeMat, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, PiLp.sub_apply]
    ring
  rw [tetrahedronVolume, tetrahedronVolume, h, abs_neg]

lemma volume_swap_ac (A B C D : EuclideanSpace ℝ (Fin 3)) :
    tetrahedronVolume A B C D = tetrahedronVolume C B A D := by
  have h : (edgeMat A B C D).det = -(edgeMat C B A D).det := by
    rw [Matrix.det_fin_three, Matrix.det_fin_three]
    simp only [edgeMat, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, PiLp.sub_apply]
    ring
  rw [tetrahedronVolume, tetrahedronVolume, h, abs_neg]

lemma volume_swap_ad (A B C D : EuclideanSpace ℝ (Fin 3)) :
    tetrahedronVolume A B C D = tetrahedronVolume D B C A := by
  have h : (edgeMat A B C D).det = -(edgeMat D B C A).det := by
    rw [Matrix.det_fin_three, Matrix.det_fin_three]
    simp only [edgeMat, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, PiLp.sub_apply]
    ring
  rw [tetrahedronVolume, tetrahedronVolume, h, abs_neg]

snip end

problem imo1967_p2 (A B C D : EuclideanSpace ℝ (Fin 3))
    (h : (dist A C ≤ 1 ∧ dist A D ≤ 1 ∧ dist B C ≤ 1 ∧ dist B D ≤ 1 ∧ dist C D ≤ 1) ∨
      (dist A B ≤ 1 ∧ dist A D ≤ 1 ∧ dist B C ≤ 1 ∧ dist B D ≤ 1 ∧ dist C D ≤ 1) ∨
      (dist A B ≤ 1 ∧ dist A C ≤ 1 ∧ dist B C ≤ 1 ∧ dist B D ≤ 1 ∧ dist C D ≤ 1) ∨
      (dist A B ≤ 1 ∧ dist A C ≤ 1 ∧ dist A D ≤ 1 ∧ dist B D ≤ 1 ∧ dist C D ≤ 1) ∨
      (dist A B ≤ 1 ∧ dist A C ≤ 1 ∧ dist A D ≤ 1 ∧ dist B C ≤ 1 ∧ dist C D ≤ 1) ∨
      (dist A B ≤ 1 ∧ dist A C ≤ 1 ∧ dist A D ≤ 1 ∧ dist B C ≤ 1 ∧ dist B D ≤ 1)) :
    tetrahedronVolume A B C D ≤ 1 / 8 := by
  rcases h with ⟨hAC, hAD, hBC, hBD, hCD⟩ | ⟨hAB, hAD, hBC, hBD, hCD⟩ |
    ⟨hAB, hAC, hBC, hBD, hCD⟩ | ⟨hAB, hAC, hAD, hBD, hCD⟩ |
    ⟨hAB, hAC, hAD, hBC, hCD⟩ | ⟨hAB, hAC, hAD, hBC, hBD⟩
  · -- The edge `AB` may exceed `1`.
    exact volume_le_one_eighth A B C D hAC hAD hBC hBD hCD
  · -- The edge `AC` may exceed `1`.
    rw [volume_swap_bc]
    exact volume_le_one_eighth A C B D hAB hAD (by rw [dist_comm]; exact hBC) hCD hBD
  · -- The edge `AD` may exceed `1`.
    rw [volume_swap_bd]
    exact volume_le_one_eighth A D C B hAC hAB (by rw [dist_comm]; exact hCD)
      (by rw [dist_comm]; exact hBD) (by rw [dist_comm]; exact hBC)
  · -- The edge `BC` may exceed `1`.
    rw [volume_swap_ac]
    exact volume_le_one_eighth C B A D (by rw [dist_comm]; exact hAC) hCD
      (by rw [dist_comm]; exact hAB) hBD hAD
  · -- The edge `BD` may exceed `1`.
    rw [volume_swap_ad]
    exact volume_le_one_eighth D B C A (by rw [dist_comm]; exact hCD)
      (by rw [dist_comm]; exact hAD) hBC (by rw [dist_comm]; exact hAB)
      (by rw [dist_comm]; exact hAC)
  · -- The edge `CD` may exceed `1`.
    rw [volume_swap_ac, volume_swap_bd]
    exact volume_le_one_eighth C D A B (by rw [dist_comm]; exact hAC)
      (by rw [dist_comm]; exact hBC) (by rw [dist_comm]; exact hAD)
      (by rw [dist_comm]; exact hBD) hAB

end Imo1967P2
