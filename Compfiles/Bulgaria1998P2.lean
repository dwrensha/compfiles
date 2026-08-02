/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw, Kimi K3
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.AffineSpace.Midpoint
public import Mathlib.Geometry.Euclidean.Basic
public import Mathlib.Geometry.Euclidean.Triangle
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

set_option maxHeartbeats 1000000

/-!
# Bulgarian Mathematical Olympiad 1998, Problem 2

A convex quadrilateral ABCD has AD = CD and ∠DAB = ∠ABC < 90°.
The line through D and the midpoint of BC intersects line AB
in point E. Prove that ∠BEC = ∠DAC. (Note: The problem is valid
without the assumption ∠ABC < 90°.)

(Formalization note: the original statement was defective — the point E
was unconstrained, and the theorem was false as stated. Here E is required
to lie on lines AB and DM; moreover C and D are required to lie on the same
side of line AB (a consequence of the convexity of ABCD — without some such
hypothesis the claim is false even with E on both lines); nondegeneracy side
conditions are added as needed.)
-/

namespace Bulgaria1998P2

open EuclideanGeometry

snip begin

/-- Rotation by 90 degrees (counterclockwise) in the Euclidean plane. Used to
express the "same side of line AB" hypothesis. -/
def J (v : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) := !₂[-v 1, v 0]

theorem J_add (v w : EuclideanSpace ℝ (Fin 2)) : J (v + w) = J v + J w := by
  ext i; fin_cases i <;> simp [J, PiLp.add_apply, add_comm]

theorem J_smul (r : ℝ) (v : EuclideanSpace ℝ (Fin 2)) : J (r • v) = r • J v := by
  ext i; fin_cases i <;> simp [J, PiLp.smul_apply, smul_eq_mul]

theorem J_J (v : EuclideanSpace ℝ (Fin 2)) : J (J v) = -v := by
  ext i; fin_cases i <;> simp [J, PiLp.neg_apply]

theorem inner_J_left (v w : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ (J v) w = - inner ℝ v (J w) := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, J]

theorem inner_J_self (v : EuclideanSpace ℝ (Fin 2)) : inner ℝ (J v) v = 0 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, J]
  ring

theorem inner_J_J (v w : EuclideanSpace ℝ (Fin 2)) : inner ℝ (J v) (J w) = inner ℝ v w := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, J]
  ring

/-- Every vector in the plane is the sum of its projections onto a unit vector
`u` and its rotation `J u`. -/
theorem coord_decomp (v u : EuclideanSpace ℝ (Fin 2)) (hu : inner ℝ u u = 1) :
    v = inner ℝ u v • u + inner ℝ (J u) v • J u := by
  have hub : u 0 ^ 2 + u 1 ^ 2 = 1 := by
    simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial] at hu
    rw [sq, sq]
    exact hu
  ext i
  fin_cases i
  · simp [PiLp.inner_apply, Fin.sum_univ_two, J]
    linear_combination (-(v 0)) * hub
  · simp [PiLp.inner_apply, Fin.sum_univ_two, J]
    linear_combination (-(v 1)) * hub

snip end

problem bulgaria1998_p2
    (A B C D E M : EuclideanSpace ℝ (Fin 2))
    (H1 : dist D A = dist D C)
    (H2 : ∠ D A B = ∠ A B C)
    (H3 : M = midpoint ℝ B C)
    (H4 : E ∈ line[ℝ, A, B])
    (H5 : E ∈ line[ℝ, D, M])
    (HAB : A ≠ B)
    (HDA : D ≠ A)
    (HCB : C ≠ B)
    (HAC : A ≠ C)
    (HEB : E ≠ B)
    (HEC : E ≠ C)
    (HSIDE : 0 < inner ℝ (J (B -ᵥ A)) (D -ᵥ A) * inner ℝ (J (B -ᵥ A)) (C -ᵥ B)) :
    ∠ B E C = ∠ D A C := by
  -- nonzero vectors
  have hvBA : B -ᵥ A ≠ 0 := fun h => HAB (vsub_eq_zero_iff_eq.mp h).symm
  have hvDA : D -ᵥ A ≠ 0 := fun h => HDA (vsub_eq_zero_iff_eq.mp h)
  have hvCB : C -ᵥ B ≠ 0 := fun h => HCB (vsub_eq_zero_iff_eq.mp h)
  have hvCA : C -ᵥ A ≠ 0 := fun h => HAC (vsub_eq_zero_iff_eq.mp h).symm
  have hvBE : B -ᵥ E ≠ 0 := fun h => HEB (vsub_eq_zero_iff_eq.mp h).symm
  have hvCE : C -ᵥ E ≠ 0 := fun h => HEC (vsub_eq_zero_iff_eq.mp h).symm
  -- set up the orthonormal frame (û, nu) along AB
  set u : EuclideanSpace ℝ (Fin 2) := B -ᵥ A with hu_def
  set b : ℝ := ‖u‖ with hb_def
  have hb : 0 < b := norm_pos_iff.mpr hvBA
  have hb0 : b ≠ 0 := ne_of_gt hb
  set d : ℝ := ‖D -ᵥ A‖ with hd_def
  have hd : 0 < d := norm_pos_iff.mpr hvDA
  have hd0 : d ≠ 0 := ne_of_gt hd
  set c : ℝ := ‖C -ᵥ B‖ with hc_def
  have hc : 0 < c := norm_pos_iff.mpr hvCB
  have hc0 : c ≠ 0 := ne_of_gt hc
  set û : EuclideanSpace ℝ (Fin 2) := b⁻¹ • u with hu1_def
  set nu : EuclideanSpace ℝ (Fin 2) := J û with hn1_def
  have huu : inner ℝ û û = 1 := by
    rw [hu1_def, real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq, ← hb_def]
    field_simp
  have hun : inner ℝ û nu = 0 := by rw [hn1_def, real_inner_comm]; exact inner_J_self û
  have hnu : inner ℝ nu û = 0 := by rw [hn1_def]; exact inner_J_self û
  have hnn : inner ℝ nu nu = 1 := by rw [hn1_def, inner_J_J, huu]
  -- coordinates of D and C in the frame
  set x : ℝ := inner ℝ û (D -ᵥ A) with hx_def
  set y : ℝ := inner ℝ nu (D -ᵥ A) with hy_def
  set x' : ℝ := inner ℝ û (C -ᵥ B) with hx'_def
  set y' : ℝ := inner ℝ nu (C -ᵥ B) with hy'_def
  have hvB : B -ᵥ A = b • û := by
    rw [hu1_def, smul_inv_smul₀ hb0, hu_def]
  -- norm-name bridges between raw terms and the set variables
  have hb' : ‖B -ᵥ A‖ = b := by rw [hb_def, hu_def]
  have hd' : ‖D -ᵥ A‖ = d := hd_def.symm
  have hc' : ‖C -ᵥ B‖ = c := hc_def.symm
  rw [dist_eq_norm_vsub, dist_eq_norm_vsub] at H1
  have hvD : D -ᵥ A = x • û + y • nu := by
    rw [hx_def, hy_def, hn1_def]
    exact coord_decomp (D -ᵥ A) û huu
  have hvC : C -ᵥ B = x' • û + y' • nu := by
    rw [hx'_def, hy'_def, hn1_def]
    exact coord_decomp (C -ᵥ B) û huu
  have hvCAf : C -ᵥ A = (b + x') • û + y' • nu := by
    have h : C -ᵥ A = (C -ᵥ B) + (B -ᵥ A) := by
      simp only [vsub_eq_sub]
      abel
    rw [h, hvB, hvC]
    module
  -- the angle hypothesis in coordinate form: d*x' + c*x = 0
  have hcos : inner ℝ (D -ᵥ A) (B -ᵥ A) / (‖D -ᵥ A‖ * ‖B -ᵥ A‖) =
      inner ℝ (A -ᵥ B) (C -ᵥ B) / (‖A -ᵥ B‖ * ‖C -ᵥ B‖) := by
    have h := congrArg Real.cos H2
    simp only [EuclideanGeometry.angle, InnerProductGeometry.cos_angle] at h
    exact h
  have hDA_BA : inner ℝ (D -ᵥ A) (B -ᵥ A) = x * b := by
    rw [hvD, hvB]
    simp only [inner_add_left, real_inner_smul_left, real_inner_smul_right, huu, hnu]
    ring
  have hAB : A -ᵥ B = -(B -ᵥ A) := by rw [neg_vsub_eq_vsub_rev]
  have hAB_CB : inner ℝ (A -ᵥ B) (C -ᵥ B) = -(b * x') := by
    rw [hAB, hvB, hvC]
    simp only [inner_neg_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      huu, hun]
    ring
  have hnAB : ‖A -ᵥ B‖ = b := by rw [← neg_vsub_eq_vsub_rev, norm_neg]
  have hx'rel : d * x' + c * x = 0 := by
    rw [hd', hb', hc', hnAB, hDA_BA, hAB_CB] at hcos
    rw [div_eq_div_iff (mul_ne_zero hd0 hb0) (mul_ne_zero hb0 hc0)] at hcos
    have e1 : x * b * (b * c) = x * c * (b * b) := by ring
    have e2 : -(b * x') * (d * b) = -(x' * d) * (b * b) := by ring
    rw [e1, e2] at hcos
    have h2 := mul_right_cancel₀ (mul_ne_zero hb0 hb0) hcos
    linarith [h2]
  -- norms in coordinates
  have hR1 : x ^ 2 + y ^ 2 = d ^ 2 := by
    have h1 : d ^ 2 = inner ℝ (D -ᵥ A) (D -ᵥ A) := by
      rw [hd_def, real_inner_self_eq_norm_sq]
    rw [h1, hvD]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      huu, hun, hnu, hnn]
    ring
  have hc2 : x' ^ 2 + y' ^ 2 = c ^ 2 := by
    have h1 : c ^ 2 = inner ℝ (C -ᵥ B) (C -ᵥ B) := by
      rw [hc_def, real_inner_self_eq_norm_sq]
    rw [h1, hvC]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      huu, hun, hnu, hnn]
    ring
  -- the same-side hypothesis in coordinate form: 0 < y * y'
  have hJ1 : inner ℝ (J (B -ᵥ A)) (D -ᵥ A) = b * y := by
    rw [hvB, J_smul, ← hn1_def, real_inner_smul_left]
  have hJ2 : inner ℝ (J (B -ᵥ A)) (C -ᵥ B) = b * y' := by
    rw [hvB, J_smul, ← hn1_def, real_inner_smul_left]
  have hbyy : 0 < y * y' := by
    rw [hJ1, hJ2] at HSIDE
    have e1 : b * y * (b * y') = b ^ 2 * (y * y') := by ring
    rw [e1] at HSIDE
    exact (mul_pos_iff_of_pos_left (sq_pos_of_ne_zero hb0)).mp HSIDE
  have hy0 : y ≠ 0 := by
    intro h
    rw [h] at hbyy
    simp at hbyy
  -- second coordinate relation: d*y' = c*y
  have hyy : (d * y') ^ 2 = (c * y) ^ 2 := by
    linear_combination d ^ 2 * hc2 - (d * x' - c * x) * hx'rel - c ^ 2 * hR1
  have hy'rel : d * y' = c * y := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hyy with h | h
    · exact h
    · exfalso
      have hneg : y * y' < 0 := by
        have h1 : d * (y * y') = -(c * y ^ 2) := by linear_combination y * h
        have h2 : 0 < c * y ^ 2 := mul_pos hc (sq_pos_of_ne_zero hy0)
        have h3 : d * (y * y') < 0 := by rw [h1]; linarith [h2]
        nlinarith [hd]
      linarith [hbyy, hneg]
  -- the constraint from H1 in coordinate form
  have hDC : ‖D -ᵥ C‖ = d := by rw [← H1]
  have hvDC : D -ᵥ C = (x - b - x') • û + (y - y') • nu := by
    have h : D -ᵥ C = (D -ᵥ A) - (C -ᵥ A) := by
      simp only [vsub_eq_sub]
      abel
    rw [h, hvD, hvCAf]
    module
  have h1 : (x - b - x') ^ 2 + (y - y') ^ 2 = d ^ 2 := by
    have h2 : ‖D -ᵥ C‖ ^ 2 = (x - b - x') ^ 2 + (y - y') ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, hvDC]
      simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
        huu, hun, hnu, hnn]
      ring
    rw [← h2, hDC]
  -- position of E on line AB
  obtain ⟨e₀, he₀⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp H4
  rw [AffineMap.lineMap_apply_module] at he₀
  set e : ℝ := e₀ * b with he_def
  have hvE : E -ᵥ A = e • û := by
    rw [vsub_eq_sub, ← he₀, he_def, hu1_def, smul_smul, mul_assoc, mul_inv_cancel₀ hb0, mul_one,
      hu_def, vsub_eq_sub]
    module
  -- position of E on line DM
  obtain ⟨s, hs⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp H5
  rw [AffineMap.lineMap_apply_module] at hs
  have hvEsM : E -ᵥ A = (1 - s) • (D -ᵥ A) + s • (M -ᵥ A) := by
    rw [vsub_eq_sub, ← hs, vsub_eq_sub, vsub_eq_sub]
    module
  have hM2 : (B -ᵥ A) + (C -ᵥ A) = (2 : ℝ) • (M -ᵥ A) := by
    have h2M : (2 : ℝ) • M = B + C := by
      rw [H3, midpoint_eq_smul_add, smul_smul]
      norm_num [invOf_eq_inv]
    have h1 : (B - A) + (C - A) = (B + C) - (2 : ℝ) • A := by module
    simp only [vsub_eq_sub]
    rw [h1, ← h2M]
    module
  -- scalar coordinate equations for E
  have hnBA : inner ℝ nu (B -ᵥ A) = 0 := by rw [hvB, real_inner_smul_right, hnu, mul_zero]
  have hnCA : inner ℝ nu (C -ᵥ A) = y' := by
    rw [hvCAf]
    simp only [inner_add_right, real_inner_smul_right, hnu, hnn]
    ring
  have hnM : (2 : ℝ) * inner ℝ nu (M -ᵥ A) = y' := by
    have h1 := congrArg (inner ℝ nu) hM2
    simp only [inner_add_right, hnBA, hnCA, real_inner_smul_right] at h1
    linarith [h1]
  have hy'E : inner ℝ nu (E -ᵥ A) = 0 := by rw [hvE, real_inner_smul_right, hnu, mul_zero]
  have hyc : (1 - s) * y + s * (inner ℝ nu (M -ᵥ A)) = 0 := by
    have h1 := hy'E
    simp only [hvEsM, inner_add_right, real_inner_smul_right, ← hy_def] at h1
    linarith [h1]
  have huBA : inner ℝ û (B -ᵥ A) = b := by rw [hvB, real_inner_smul_right, huu, mul_one]
  have huCA : inner ℝ û (C -ᵥ A) = b + x' := by
    rw [hvCAf]
    simp only [inner_add_right, real_inner_smul_right, huu, hun]
    ring
  have huM : (2 : ℝ) * inner ℝ û (M -ᵥ A) = b + (b + x') := by
    have h1 := congrArg (inner ℝ û) hM2
    simp only [inner_add_right, huBA, huCA, real_inner_smul_right] at h1
    linarith [h1]
  have hxc : e = (1 - s) * x + s * (inner ℝ û (M -ᵥ A)) := by
    have h1 : inner ℝ û (E -ᵥ A) = e := by rw [hvE, real_inner_smul_right, huu, mul_one]
    simp only [hvEsM, inner_add_right, real_inner_smul_right, ← hx_def] at h1
    linarith [h1]
  -- the parameter s along DM
  have hyc2 : 2 * (1 - s) * (y * d) + s * (c * y) = 0 := by
    linear_combination 2 * d * hyc - d * s * hnM - s * hy'rel
  have hyc3 : y * (2 * (1 - s) * d + s * c) = 0 := by linear_combination hyc2
  have hyc4 : 2 * (1 - s) * d + s * c = 0 := by
    rcases mul_eq_zero.mp hyc3 with h | h
    · exact absurd h hy0
    · linarith [h]
  have hsd : s * (2 * d - c) = 2 * d := by linarith [hyc4]
  have h2dc : 2 * d - c ≠ 0 := by
    intro h
    rw [h, mul_zero] at hsd
    linarith [hd]
  -- the key parameter p = b*d - c*x and the position of E
  set p : ℝ := b * d - c * x with hp_def
  have he : e * (2 * d - c) = 2 * p := by
    linear_combination (2 * d - c) * hxc + (inner ℝ û (M -ᵥ A) - x) * hsd + d * huM + hx'rel -
      2 * hp_def
  -- constraint from H1 in (p, x, y) form
  have h1' : (d * x - p) ^ 2 + (y * (d - c)) ^ 2 = d ^ 4 := by
    have e1 : d * x - p = d * (x - b - x') := by linear_combination hx'rel - hp_def
    have e2 : y * (d - c) = d * (y - y') := by linear_combination hy'rel
    rw [e1, e2]
    have e3 : (d * (x - b - x')) ^ 2 + (d * (y - y')) ^ 2 =
        d ^ 2 * ((x - b - x') ^ 2 + (y - y') ^ 2) := by ring
    rw [e3, h1]
    ring
  have hCON : p ^ 2 - 2 * p * d * x + c * y ^ 2 * (c - 2 * d) = 0 := by
    linear_combination h1' - d ^ 2 * hR1
  -- the crux polynomial identity
  have hG : (p ^ 2 + c ^ 2 * y ^ 2) * (p ^ 2 + y ^ 2 * (2 * d - c) ^ 2) = 4 * d ^ 4 * p ^ 2 := by
    linear_combination (p ^ 2 + 2 * p * d * x - c * y ^ 2 * (2 * d - c)) * hCON +
      (4 * d ^ 2 * p ^ 2) * hR1
  -- closed forms for the relevant inner products and norms
  have hvBEf : B -ᵥ E = (b - e) • û := by
    have h : B -ᵥ E = (B -ᵥ A) - (E -ᵥ A) := by
      simp only [vsub_eq_sub]
      abel
    rw [h, hvB, hvE]
    module
  have hvCEf : C -ᵥ E = (b + x' - e) • û + y' • nu := by
    have h : C -ᵥ E = (C -ᵥ A) - (E -ᵥ A) := by
      simp only [vsub_eq_sub]
      abel
    rw [h, hvCAf, hvE]
    module
  have hiBECE : inner ℝ (B -ᵥ E) (C -ᵥ E) = (b - e) * (b + x' - e) := by
    rw [hvBEf, hvCEf]
    simp only [inner_add_right, real_inner_smul_left, real_inner_smul_right, huu, hun]
    ring
  have hnBE2 : ‖B -ᵥ E‖ ^ 2 = (b - e) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, hvBEf]
    simp only [real_inner_smul_left, real_inner_smul_right, huu]
    ring
  have hnCE2 : ‖C -ᵥ E‖ ^ 2 = (b + x' - e) ^ 2 + y' ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, hvCEf]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      huu, hun, hnu, hnn]
    ring
  have hnCA2 : ‖C -ᵥ A‖ ^ 2 = (b + x') ^ 2 + y' ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, hvCAf]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      huu, hun, hnu, hnn]
    ring
  have hbe : (b - e) * (2 * d - c) = -(c * (b - 2 * x)) := by
    linear_combination -he - 2 * hp_def
  have hQe : (b + x' - e) * (d * (2 * d - c)) = -(p * c) := by
    linear_combination -d * he + (2 * d - c) * hx'rel - (2 * d - c) * hp_def
  have hT : inner ℝ (B -ᵥ E) (C -ᵥ E) * (d * (2 * d - c) ^ 2) = p * c ^ 2 * (b - 2 * x) := by
    rw [hiBECE]
    have h1 : (b - e) * (b + x' - e) * (d * (2 * d - c) ^ 2) =
        ((b - e) * (2 * d - c)) * ((b + x' - e) * (d * (2 * d - c))) := by ring
    rw [h1, hbe, hQe]
    ring
  have hnBE' : ‖B -ᵥ E‖ ^ 2 * (2 * d - c) ^ 2 = c ^ 2 * (b - 2 * x) ^ 2 := by
    rw [hnBE2]
    have h1 : (b - e) ^ 2 * (2 * d - c) ^ 2 = ((b - e) * (2 * d - c)) ^ 2 := by ring
    rw [h1, hbe]
    ring
  have hnCE' : ‖C -ᵥ E‖ ^ 2 * (d ^ 2 * (2 * d - c) ^ 2) =
      c ^ 2 * (p ^ 2 + y ^ 2 * (2 * d - c) ^ 2) := by
    rw [hnCE2]
    have h1 : ((b + x' - e) ^ 2 + y' ^ 2) * (d ^ 2 * (2 * d - c) ^ 2) =
        ((b + x' - e) * (d * (2 * d - c))) ^ 2 + (y' * (d * (2 * d - c))) ^ 2 := by ring
    rw [h1, hQe]
    have h2 : y' * (d * (2 * d - c)) = c * y * (2 * d - c) := by
      linear_combination (2 * d - c) * hy'rel
    rw [h2]
    ring
  have hnCA' : ‖C -ᵥ A‖ ^ 2 * d ^ 2 = p ^ 2 + c ^ 2 * y ^ 2 := by
    rw [hnCA2]
    have h1 : ((b + x') ^ 2 + y' ^ 2) * d ^ 2 = ((b + x') * d) ^ 2 + (d * y') ^ 2 := by ring
    rw [h1, hy'rel]
    have h2 : (b + x') * d = p := by linear_combination hx'rel - hp_def
    rw [h2]
    ring
  -- the sign fact: cd < bx + 2y²
  have hquad : d ^ 2 * c ^ 2 + 2 * d * c * (x ^ 2 - y ^ 2 - b * x) + d ^ 2 * (b ^ 2 - 2 * b * x) =
      0 := by
    linear_combination hCON - c ^ 2 * hR1
  have hb2x : b - 2 * x ≠ 0 := by
    intro hbx
    have hb2 : b = 2 * x := by linarith [hbx]
    rw [hb2] at hquad
    have hc2d : d ^ 2 * c * (c - 2 * d) = 0 := by
      linear_combination hquad + (2 * d * c) * hR1
    have hne : d ^ 2 * c ≠ 0 := mul_ne_zero (pow_ne_zero 2 hd0) hc0
    have hcd : c - 2 * d = 0 := by
      rcases mul_eq_zero.mp hc2d with h1 | h1
      · exact absurd h1 hne
      · exact h1
    exact h2dc (by linarith [hcd])
  have hid : d ^ 4 - (x ^ 2 - y ^ 2 - b * x) ^ 2 + d ^ 2 * (b ^ 2 - 2 * b * x) =
      y ^ 2 * (b - 2 * x) ^ 2 := by
    linear_combination (b * (2 * x - b) - (x ^ 2 + y ^ 2 + d ^ 2)) * hR1
  have hlt : (d * c + (x ^ 2 - y ^ 2 - b * x)) ^ 2 < d ^ 4 := by
    have hq2 : (d * c + (x ^ 2 - y ^ 2 - b * x)) ^ 2 =
        (x ^ 2 - y ^ 2 - b * x) ^ 2 - d ^ 2 * (b ^ 2 - 2 * b * x) := by
      linear_combination hquad
    have hpos : 0 < y ^ 2 * (b - 2 * x) ^ 2 :=
      mul_pos (sq_pos_of_ne_zero hy0) (sq_pos_of_ne_zero hb2x)
    rw [hq2]
    have h3 : (x ^ 2 - y ^ 2 - b * x) ^ 2 - d ^ 2 * (b ^ 2 - 2 * b * x) =
        d ^ 4 - y ^ 2 * (b - 2 * x) ^ 2 := by
      linear_combination -hid
    rw [h3]
    linarith [hpos]
  have hS1 : c * d < b * x + 2 * y ^ 2 := by
    have h2 : (d * c + (x ^ 2 - y ^ 2 - b * x)) ^ 2 < (d ^ 2) ^ 2 := by
      rw [show (d ^ 2) ^ 2 = d ^ 4 by ring]
      exact hlt
    have h4 := abs_lt_of_sq_lt_sq h2 (sq_nonneg d)
    have h1 : d * c + (x ^ 2 - y ^ 2 - b * x) < d ^ 2 := (abs_lt.mp h4).2
    linarith [h1, hR1]
  -- positivity of the inner product
  have hsign : 0 < p * (b - 2 * x) := by
    have h1 : d * (p * (b - 2 * x)) = d * (c * (b * x + 2 * y ^ 2 - c * d)) := by
      linear_combination hCON - c ^ 2 * hR1
    have h2 : p * (b - 2 * x) = c * (b * x + 2 * y ^ 2 - c * d) := mul_left_cancel₀ hd0 h1
    rw [h2]
    have h3 : 0 < b * x + 2 * y ^ 2 - c * d := by linarith [hS1]
    exact mul_pos hc h3
  have hposT : 0 < inner ℝ (B -ᵥ E) (C -ᵥ E) := by
    have h1 : inner ℝ (B -ᵥ E) (C -ᵥ E) = (p * c ^ 2 * (b - 2 * x)) / (d * (2 * d - c) ^ 2) := by
      have hne : d * (2 * d - c) ^ 2 ≠ 0 := mul_ne_zero hd0 (pow_ne_zero 2 h2dc)
      rw [eq_div_iff hne]
      exact hT
    rw [h1]
    have h2 : 0 < p * c ^ 2 * (b - 2 * x) := by
      rw [show p * c ^ 2 * (b - 2 * x) = c ^ 2 * (p * (b - 2 * x)) by ring]
      exact mul_pos (sq_pos_of_ne_zero hc0) hsign
    exact div_pos h2 (mul_pos hd (sq_pos_of_ne_zero h2dc))
  -- the squared key equality
  have hbig : (4 * d ^ 2 * (inner ℝ (B -ᵥ E) (C -ᵥ E)) ^ 2) * (d ^ 4 * (2 * d - c) ^ 4) =
      (‖C -ᵥ A‖ ^ 2 * ‖B -ᵥ E‖ ^ 2 * ‖C -ᵥ E‖ ^ 2) * (d ^ 4 * (2 * d - c) ^ 4) := by
    have e1 : (4 * d ^ 2 * (inner ℝ (B -ᵥ E) (C -ᵥ E)) ^ 2) * (d ^ 4 * (2 * d - c) ^ 4) =
        4 * d ^ 4 * (inner ℝ (B -ᵥ E) (C -ᵥ E) * (d * (2 * d - c) ^ 2)) ^ 2 := by ring
    rw [e1, hT]
    have e2 : (‖C -ᵥ A‖ ^ 2 * ‖B -ᵥ E‖ ^ 2 * ‖C -ᵥ E‖ ^ 2) * (d ^ 4 * (2 * d - c) ^ 4) =
        (‖C -ᵥ A‖ ^ 2 * d ^ 2) * (‖B -ᵥ E‖ ^ 2 * (2 * d - c) ^ 2) *
          (‖C -ᵥ E‖ ^ 2 * (d ^ 2 * (2 * d - c) ^ 2)) := by ring
    rw [e2, hnCA', hnBE', hnCE']
    linear_combination (-(c ^ 4 * (b - 2 * x) ^ 2)) * hG
  have hsq : 4 * d ^ 2 * (inner ℝ (B -ᵥ E) (C -ᵥ E)) ^ 2 =
      ‖C -ᵥ A‖ ^ 2 * ‖B -ᵥ E‖ ^ 2 * ‖C -ᵥ E‖ ^ 2 :=
    mul_right_cancel₀ (mul_ne_zero (pow_ne_zero 4 hd0) (pow_ne_zero 4 h2dc)) hbig
  -- inner product of the isosceles triangle
  have hiDACA : inner ℝ (D -ᵥ A) (C -ᵥ A) = ‖C -ᵥ A‖ ^ 2 / 2 := by
    have h1 : ‖D -ᵥ C‖ = ‖D -ᵥ A‖ := H1.symm
    have h2 : D -ᵥ C = (D -ᵥ A) - (C -ᵥ A) := by
      simp only [vsub_eq_sub]
      abel
    have h3 : ‖D -ᵥ C‖ ^ 2 = ‖D -ᵥ A‖ ^ 2 - 2 * inner ℝ (D -ᵥ A) (C -ᵥ A) + ‖C -ᵥ A‖ ^ 2 := by
      rw [h2, norm_sub_sq_real]
    have h4 : ‖D -ᵥ C‖ ^ 2 = ‖D -ᵥ A‖ ^ 2 := by rw [h1]
    rw [h3] at h4
    linarith [h4]
  -- unsquaring
  have hU : 0 < ‖B -ᵥ E‖ := norm_pos_iff.mpr hvBE
  have hV : 0 < ‖C -ᵥ E‖ := norm_pos_iff.mpr hvCE
  have hZ : 0 < ‖C -ᵥ A‖ := norm_pos_iff.mpr hvCA
  have hfin : 2 * d * (inner ℝ (B -ᵥ E) (C -ᵥ E)) = ‖C -ᵥ A‖ * ‖B -ᵥ E‖ * ‖C -ᵥ E‖ := by
    have hsq2 : (2 * d * (inner ℝ (B -ᵥ E) (C -ᵥ E))) ^ 2 =
        (‖C -ᵥ A‖ * ‖B -ᵥ E‖ * ‖C -ᵥ E‖) ^ 2 := by
      rw [show (2 * d * (inner ℝ (B -ᵥ E) (C -ᵥ E))) ^ 2 =
          4 * d ^ 2 * (inner ℝ (B -ᵥ E) (C -ᵥ E)) ^ 2 by ring, hsq]
      ring
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq2 with h | h
    · exact h
    · exfalso
      have h1 : 0 < 2 * d * (inner ℝ (B -ᵥ E) (C -ᵥ E)) := mul_pos (mul_pos (by norm_num) hd) hposT
      have h2 : 0 < ‖C -ᵥ A‖ * ‖B -ᵥ E‖ * ‖C -ᵥ E‖ := mul_pos (mul_pos hZ hU) hV
      rw [h] at h1
      linarith [h1, h2]
  -- conclude the angle equality
  have harg : inner ℝ (B -ᵥ E) (C -ᵥ E) / (‖B -ᵥ E‖ * ‖C -ᵥ E‖) =
      inner ℝ (D -ᵥ A) (C -ᵥ A) / (‖D -ᵥ A‖ * ‖C -ᵥ A‖) := by
    rw [hiDACA, hd']
    rw [div_eq_div_iff (ne_of_gt (mul_pos hU hV)) (ne_of_gt (mul_pos hd hZ))]
    linear_combination (‖C -ᵥ A‖ / 2) * hfin
  simp only [EuclideanGeometry.angle, InnerProductGeometry.angle, harg]

end Bulgaria1998P2
