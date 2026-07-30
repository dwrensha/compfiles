/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.AffineSpace.Midpoint
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 1978, Problem 4

In the triangle ABC, AB = AC. A circle is tangent internally to the
circumcircle of the triangle and also to AB, AC at P, Q respectively.
Prove that the midpoint of PQ is the center of the incircle of the triangle.

## Formalization note

We place the isosceles triangle in the plane with `A = (0, a)` on the positive
y-axis and `B = (-b, 0)`, `C = (b, 0)` symmetric about it (`a, b > 0`), which is
without loss of generality by rigid motions.  The circle has center `S` and
radius `r`; tangency to the lines `AB`, `AC` at `P`, `Q` is expressed by
`P ∈ line AB`, `dist S P = r` and `SP ⊥ AB` (and similarly for `Q`), and
internal tangency to the circumcircle (with circumcenter `O` and circumradius
`R`) by `dist S O + r = R`.  The conclusion is that the midpoint of `PQ` is
`(0, a*b/(b + √(a²+b²)))`, which is the incenter of the triangle: it lies on
the axis of symmetry at height equal to the inradius
`area / semiperimeter = a*b / (b + √(a²+b²))`.
-/

namespace Imo1978P4

open scoped RealInnerProductSpace

/-- The Euclidean plane. -/
abbrev Pt := EuclideanSpace ℝ (Fin 2)

snip begin

/-- Extensionality for points of the plane. -/
lemma pt_ext {x y : Pt} (h0 : x 0 = y 0) (h1 : x 1 = y 1) : x = y := by
  apply WithLp.ofLp_injective (p := 2)
  funext i
  fin_cases i <;> assumption

/-- Inner product of plane vectors in coordinates. -/
lemma inner_pt (x y : Pt) : ⟪x, y⟫ = x 0 * y 0 + x 1 * y 1 := by
  rw [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, RCLike.inner_apply]
  simp only [conj_trivial]
  ring

/-- Distance between two explicitly given points of the plane. -/
lemma dist2 (x1 y1 x2 y2 : ℝ) :
    dist (!₂[x1, y1] : Pt) !₂[x2, y2] = Real.sqrt ((x1 - x2)^2 + (y1 - y2)^2) := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Real.dist_eq, sq_abs]

/-- Squared distance in coordinates. -/
lemma dist_sq (X Y : Pt) : dist X Y ^ 2 = (X 0 - Y 0)^2 + (X 1 - Y 1)^2 := by
  have eX : X = !₂[X 0, X 1] := pt_ext rfl rfl
  have eY : Y = !₂[Y 0, Y 1] := pt_ext rfl rfl
  rw [eX, eY, dist2, Real.sq_sqrt (by positivity)]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one]

/-- The circumcenter of the isosceles triangle lies on the axis of symmetry,
with explicit coordinates. -/
lemma O_coords (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (A B C O : Pt) (R : ℝ)
    (hA : A = !₂[0, a]) (hB : B = !₂[-b, 0]) (hC : C = !₂[b, 0])
    (hOA : dist O A = R) (hOB : dist O B = R) (hOC : dist O C = R)
    (hRpos : 0 < R) :
    O 0 = 0 ∧ 2 * a * O 1 = a ^ 2 - b ^ 2 ∧ 2 * a * R = a ^ 2 + b ^ 2 ∧
      R ^ 2 = (O 1 - a) ^ 2 := by
  have eOA : R ^ 2 = (O 0) ^ 2 + (O 1 - a) ^ 2 := by
    have e := dist_sq O A
    rw [hOA, hA] at e
    simpa [Matrix.cons_val_zero, Matrix.cons_val_one] using e
  have eOB : R ^ 2 = (O 0 + b) ^ 2 + (O 1) ^ 2 := by
    have e := dist_sq O B
    rw [hOB, hB] at e
    simpa [Matrix.cons_val_zero, Matrix.cons_val_one] using e
  have eOC : R ^ 2 = (O 0 - b) ^ 2 + (O 1) ^ 2 := by
    have e := dist_sq O C
    rw [hOC, hC] at e
    simpa [Matrix.cons_val_zero, Matrix.cons_val_one] using e
  have hOx : O 0 = 0 := by
    have h4 : 4 * b * O 0 = 0 := by nlinarith only [eOB, eOC]
    rcases mul_eq_zero.mp h4 with h | h
    · exfalso; linarith only [h, hb]
    · exact h
  rw [hOx] at eOA eOB eOC
  norm_num at eOA eOB eOC
  have hoy : 2 * a * O 1 = a ^ 2 - b ^ 2 := by linarith only [eOA, eOB]
  have hR2b : R ^ 2 = b ^ 2 + (O 1) ^ 2 := by linarith only [eOB]
  have hR2a : 2 * a * R = a ^ 2 + b ^ 2 := by
    have h1 : (2 * a * R) ^ 2 = (a ^ 2 + b ^ 2) ^ 2 := by
      have e1 : (2 * a * R) ^ 2 = 4 * a ^ 2 * R ^ 2 := by ring
      rw [e1, hR2b]
      nlinarith only [hoy]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h1 with h | h
    · exact h
    · exfalso; nlinarith only [h, ha, hRpos]
  exact ⟨hOx, hoy, hR2a, eOA⟩

/-- Coordinates of the two tangency points on `AB` and `AC`. -/
lemma PQ_coords (a b : ℝ) (A B C P Q : Pt) (t w : ℝ)
    (hA : A = !₂[0, a]) (hB : B = !₂[-b, 0]) (hC : C = !₂[b, 0])
    (htP : P = (1 - t) • A + t • B) (hwQ : Q = (1 - w) • A + w • C) :
    P = !₂[-t * b, (1 - t) * a] ∧ Q = !₂[w * b, (1 - w) * a] := by
  constructor
  · rw [htP, hA, hB]
    apply pt_ext <;>
      simp [smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
  · rw [hwQ, hA, hC]
    apply pt_ext <;>
      simp [smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- The four polynomial equations expressing the two tangencies. -/
lemma tangency_polys (a b : ℝ)
    (A B C P Q S : Pt) (r t w : ℝ)
    (hA : A = !₂[0, a]) (hB : B = !₂[-b, 0]) (hC : C = !₂[b, 0])
    (hPpt : P = !₂[-t * b, (1 - t) * a]) (hQpt : Q = !₂[w * b, (1 - w) * a])
    (hSP : dist S P = r) (hSQ : dist S Q = r)
    (hSPperp : ⟪S - P, A - B⟫ = 0) (hSQperp : ⟪S - Q, A - C⟫ = 0) :
    (S 0 + t * b) * b + (S 1 - (1 - t) * a) * a = 0 ∧
    (S 0 + t * b) ^ 2 + (S 1 - (1 - t) * a) ^ 2 = r ^ 2 ∧
    (S 0 - w * b) * (-b) + (S 1 - (1 - w) * a) * a = 0 ∧
    (S 0 - w * b) ^ 2 + (S 1 - (1 - w) * a) ^ 2 = r ^ 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [inner_pt, hPpt, hA, hB] at hSPperp
    simp only [WithLp.ofLp_sub, Pi.sub_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one] at hSPperp
    linear_combination hSPperp
  · have e := dist_sq S P
    rw [hSP, hPpt] at e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e
    linear_combination -e
  · rw [inner_pt, hQpt, hA, hC] at hSQperp
    simp only [WithLp.ofLp_sub, Pi.sub_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one] at hSQperp
    linear_combination hSQperp
  · have e := dist_sq S Q
    rw [hSQ, hQpt] at e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e
    linear_combination -e

/-- The center `S` is equidistant from the lines `AB` and `AC`, so it lies on
one of the two angle bisectors at `A` (in squared form). -/
lemma bisector_sq (a b : ℝ) (ha : 0 < a) (S : Pt) (r t w : ℝ)
    (ht1 : (S 0 + t * b) * b + (S 1 - (1 - t) * a) * a = 0)
    (ht2 : (S 0 + t * b) ^ 2 + (S 1 - (1 - t) * a) ^ 2 = r ^ 2)
    (hw1 : (S 0 - w * b) * (-b) + (S 1 - (1 - w) * a) * a = 0)
    (hw2 : (S 0 - w * b) ^ 2 + (S 1 - (1 - w) * a) ^ 2 = r ^ 2) :
    (S 0 + t * b) ^ 2 = (S 0 - w * b) ^ 2 := by
  have hY1 : a * (S 1 - (1 - t) * a) = -((S 0 + t * b) * b) := by
    linear_combination ht1
  have hY2 : a * (S 1 - (1 - w) * a) = (S 0 - w * b) * b := by
    linear_combination hw1
  have hs1 : a ^ 2 * (S 1 - (1 - t) * a) ^ 2 = b ^ 2 * (S 0 + t * b) ^ 2 := by
    have h := congrArg (· ^ 2) hY1
    linear_combination h
  have hs2 : a ^ 2 * (S 1 - (1 - w) * a) ^ 2 = b ^ 2 * (S 0 - w * b) ^ 2 := by
    have h := congrArg (· ^ 2) hY2
    linear_combination h
  have hs3 : (a ^ 2 + b ^ 2) * (S 0 + t * b) ^ 2 = a ^ 2 * r ^ 2 := by
    have h := congrArg (fun z => a ^ 2 * z) ht2
    linear_combination h - hs1
  have hs4 : (a ^ 2 + b ^ 2) * (S 0 - w * b) ^ 2 = a ^ 2 * r ^ 2 := by
    have h := congrArg (fun z => a ^ 2 * z) hw2
    linear_combination h - hs2
  have hpos : (0 : ℝ) < a ^ 2 + b ^ 2 := by positivity
  exact mul_left_cancel₀ (ne_of_gt hpos) (by linear_combination hs3 - hs4)

/-- The external-bisector case (tangency point at the "top" of the circumcircle)
contradicts internal tangency with positive radius. -/
lemma not_external (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (S O : Pt) (r R t w : ℝ)
    (ht1 : (S 0 + t * b) * b + (S 1 - (1 - t) * a) * a = 0)
    (hw1 : (S 0 - w * b) * (-b) + (S 1 - (1 - w) * a) * a = 0)
    (hcase : S 0 + t * b = S 0 - w * b)
    (hOx : O 0 = 0) (eOA : R ^ 2 = (O 1 - a) ^ 2)
    (hSO : dist S O + r = R) (hr : 0 < r) (hRpos : 0 < R) (hDnn : 0 ≤ dist S O) :
    False := by
  have htww : t + w = 0 := by
    have h1 : (t + w) * b = 0 := by linear_combination hcase
    rcases mul_eq_zero.mp h1 with h | h
    · exact h
    · exfalso; exact (ne_of_gt hb) h
  have hS1a : S 1 = a := by
    have h2 : (S 1 - (1 - t) * a + (S 1 - (1 - w) * a)) * a = 0 := by
      linear_combination ht1 + hw1 - b * hcase
    rcases mul_eq_zero.mp h2 with h | h
    · have h3 : 2 * S 1 = (2 - t - w) * a := by linear_combination h
      have h4 : (t + w) * a = 0 := by rw [htww]; ring
      linarith only [h3, h4]
    · exfalso; exact (ne_of_gt ha) h
  have hSO2 : dist S O ^ 2 = (S 0) ^ 2 + R ^ 2 := by
    have e := dist_sq S O
    rw [hS1a, hOx] at e
    linarith only [e, eOA]
  have h1 : dist S O = R - r := by linarith only [hSO]
  rw [h1] at hSO2
  have h2 : (S 0) ^ 2 + 2 * R * r = r ^ 2 := by nlinarith only [hSO2]
  have h3 : 2 * R * r ≤ r * r := by linarith only [h2, sq_nonneg (S 0)]
  have h4 : 2 * R ≤ r := le_of_mul_le_mul_right h3 hr
  have h5 : dist S O ≤ -R := by linarith only [h1, h4]
  linarith only [h5, hDnn, hRpos]

/-- In the internal-bisector case, `t = w` and `S` lies on the axis. -/
lemma internal_axis (a b : ℝ) (ha : 0 < a) (S : Pt) (t w : ℝ)
    (ht1 : (S 0 + t * b) * b + (S 1 - (1 - t) * a) * a = 0)
    (hw1 : (S 0 - w * b) * (-b) + (S 1 - (1 - w) * a) * a = 0)
    (hcase : S 0 + t * b = -(S 0 - w * b)) :
    t = w ∧ S 0 = 0 := by
  have htw : t = w := by
    have h1 : ((S 1 - (1 - t) * a) - (S 1 - (1 - w) * a)) * a = 0 := by
      linear_combination ht1 - hw1 - b * hcase
    rcases mul_eq_zero.mp h1 with h | h
    · have h2 : (t - w) * a = 0 := by linear_combination h
      rcases mul_eq_zero.mp h2 with h3 | h3
      · linarith only [h3]
      · exfalso; exact (ne_of_gt ha) h3
    · exfalso; exact (ne_of_gt ha) h
  refine ⟨htw, ?_⟩
  rw [← htw] at hcase
  linarith only [hcase]

/-- The radius of the circle, in polynomial form. -/
lemma radius_sq (a b u r t : ℝ) (hu2 : u ^ 2 = a ^ 2 + b ^ 2) (S : Pt)
    (ht1 : (t * b) * b + (S 1 - (1 - t) * a) * a = 0)
    (ht2 : (t * b) ^ 2 + (S 1 - (1 - t) * a) ^ 2 = r ^ 2) :
    r ^ 2 * a ^ 2 = t ^ 2 * b ^ 2 * u ^ 2 := by
  have hZ : a * (S 1 - (1 - t) * a) = -(t * b ^ 2) := by linear_combination ht1
  have h1 : (a * (S 1 - (1 - t) * a)) ^ 2 = (t * b ^ 2) ^ 2 := by rw [hZ]; ring
  have h2 := congrArg (fun z => a ^ 2 * z) ht2
  have h3 : r ^ 2 * a ^ 2 = t ^ 2 * b ^ 2 * (a ^ 2 + b ^ 2) := by
    linear_combination h1 - h2
  rwa [← hu2] at h3

/-- The final computation: the height of the midpoint of `PQ`. -/
lemma final_height (a b u r R t : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hu : 0 < u) (hu2 : u ^ 2 = a ^ 2 + b ^ 2) (hr : 0 < r)
    (S O : Pt)
    (hoy : 2 * a * O 1 = a ^ 2 - b ^ 2) (hR2a : 2 * a * R = a ^ 2 + b ^ 2)
    (hZ : a * (S 1 - (1 - t) * a) = -(t * b ^ 2))
    (hr2 : r ^ 2 * a ^ 2 = t ^ 2 * b ^ 2 * u ^ 2)
    (hSpt : S = !₂[0, S 1]) (hOpt : O = !₂[0, O 1])
    (hSO : dist S O + r = R) :
    (1 - t) * a = a * b / (b + u) := by
  have hdist : dist S O = |S 1 - O 1| := by
    rw [hSpt, hOpt, dist2]
    simp [Real.sqrt_sq_eq_abs]
  have habs : |S 1 - O 1| = R - r := by linarith only [hSO, hdist]
  by_cases hle : 0 ≤ S 1 - O 1
  · -- `S` above `O`: impossible.
    have h1 : |S 1 - O 1| = S 1 - O 1 := abs_of_nonneg hle
    have hcaseA0 : S 1 - O 1 = R - r := by linarith only [habs, h1]
    have hcase2a : 2 * a * S 1 - 2 * a * O 1 = 2 * a * R - 2 * a * r := by
      linear_combination 2 * a * hcaseA0
    have hcaseA1 : a * r = t * (a ^ 2 + b ^ 2) := by linarith only [hcase2a, hZ, hoy, hR2a]
    rw [← hu2] at hcaseA1
    have h1' : (a * r) ^ 2 = (t * u ^ 2) ^ 2 := by rw [hcaseA1]
    have h2' : t ^ 2 * u ^ 4 = t ^ 2 * b ^ 2 * u ^ 2 := by nlinarith only [h1', hr2]
    have h3 : t ^ 2 * u ^ 2 * a ^ 2 = 0 := by
      have e : t ^ 2 * u ^ 2 * (u ^ 2 - b ^ 2) = 0 := by nlinarith only [h2']
      have e2 : u ^ 2 - b ^ 2 = a ^ 2 := by linarith only [hu2]
      rwa [e2] at e
    have h4 : t = 0 := by
      have hpos : (0 : ℝ) < u ^ 2 * a ^ 2 := by positivity
      have e : t ^ 2 * (u ^ 2 * a ^ 2) = 0 := by nlinarith only [h3]
      rcases mul_eq_zero.mp e with h | h
      · rcases mul_eq_zero.mp (show t * t = 0 by linarith only [h]) with h' | h' <;> exact h'
      · exfalso; linarith only [h, hpos]
    have h5 : a * r = 0 := by rw [h4] at hcaseA1; linarith only [hcaseA1]
    have h6 : r = 0 := by
      rcases mul_eq_zero.mp h5 with h | h
      · exfalso; exact (ne_of_gt ha) h
      · exact h
    exact absurd h6 (ne_of_gt hr)
  · -- `S` below `O`: the actual configuration.
    have hlt : S 1 - O 1 < 0 := lt_of_not_ge hle
    have h1 : |S 1 - O 1| = -(S 1 - O 1) := abs_of_neg hlt
    have hcaseB0 : O 1 - S 1 = R - r := by linarith only [habs, h1]
    have hcase2a : 2 * a * O 1 - 2 * a * S 1 = 2 * a * R - 2 * a * r := by
      linear_combination 2 * a * hcaseB0
    have hcaseB1 : a * r = (1 - t) * (a ^ 2 + b ^ 2) := by
      linarith only [hcase2a, hZ, hoy, hR2a]
    rw [← hu2] at hcaseB1
    have h2' : ((1 - t) * u ^ 2) ^ 2 = (t * b * u) ^ 2 := by
      have e1 : (a * r) ^ 2 = ((1 - t) * u ^ 2) ^ 2 := by rw [hcaseB1]
      nlinarith only [e1, hr2]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h2' with hB1 | hB2
    · -- `(1 - t) * u^2 = t * b * u`, the good branch.
      have ht : t * (u + b) = u := by
        have hune : u ≠ 0 := ne_of_gt hu
        have e : (1 - t) * u = t * b := by
          have h4 : ((1 - t) * u - t * b) * u = 0 := by nlinarith only [hB1]
          rcases mul_eq_zero.mp h4 with h | h
          · linarith only [h]
          · exfalso; exact hune h
        linarith only [e]
      have hbu : (0 : ℝ) < b + u := by linarith only [hb, hu]
      rw [eq_div_iff (ne_of_gt hbu)]
      have hta : t * a * (u + b) = u * a := by linear_combination a * ht
      linarith only [hta]
    · -- `(1 - t) * u^2 = -(t * b * u)`, contradicting `r > 0`.
      exfalso
      have hub : b < u := by nlinarith only [hu2, ha, hb, hu]
      have htpos : 0 < t := by
        have hune : u ≠ 0 := ne_of_gt hu
        have e : t * (u - b) = u := by
          have h4 : (u - t * u + t * b) * u = 0 := by nlinarith only [hB2]
          rcases mul_eq_zero.mp h4 with h | h
          · linarith only [h]
          · exfalso; exact hune h
        nlinarith only [e, hub, hu]
      have har : a * r = -(t * b * u) := by
        have e : (1 - t) * u ^ 2 = -t * b * u := by nlinarith only [hB2]
        linarith only [hcaseB1, e]
      have hpos1 : (0 : ℝ) < t * b * u := mul_pos (mul_pos htpos hb) hu
      have hpos2 : (0 : ℝ) < a * r := mul_pos ha hr
      linarith only [har, hpos1, hpos2]

snip end

problem imo1978_p4
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (A B C P Q S O : Pt) (r R : ℝ)
    -- The isosceles triangle with `AB = AC`, placed symmetrically about the y-axis.
    (hA : A = !₂[0, a]) (hB : B = !₂[-b, 0]) (hC : C = !₂[b, 0])
    -- The circle has center `S` and positive radius `r`.
    (hr : 0 < r)
    -- It is tangent to `AB` at `P` and to `AC` at `Q`.
    (hP : ∃ t : ℝ, P = (1 - t) • A + t • B)
    (hQ : ∃ w : ℝ, Q = (1 - w) • A + w • C)
    (hSP : dist S P = r) (hSQ : dist S Q = r)
    (hSPperp : ⟪S - P, A - B⟫ = 0) (hSQperp : ⟪S - Q, A - C⟫ = 0)
    -- `O` and `R` are the circumcenter and circumradius of `ABC` ...
    (hOA : dist O A = R) (hOB : dist O B = R) (hOC : dist O C = R)
    -- ... and the circle is tangent internally to the circumcircle.
    (hSO : dist S O + r = R) :
    midpoint ℝ P Q = !₂[0, a * b / (b + Real.sqrt (a ^ 2 + b ^ 2))] := by
  obtain ⟨t, htP⟩ := hP
  obtain ⟨w, hwQ⟩ := hQ
  -- `u` is the common length of `AB` and `AC`.
  set u := Real.sqrt (a ^ 2 + b ^ 2) with hu_def
  have hu2 : u ^ 2 = a ^ 2 + b ^ 2 := Real.sq_sqrt (by positivity)
  have hu : 0 < u := Real.sqrt_pos.2 (by positivity)
  have hDnn : (0 : ℝ) ≤ dist S O := dist_nonneg
  have hRpos : 0 < R := by linarith only [hSO, hr, hDnn]
  obtain ⟨hOx, hoy, hR2a, eOA⟩ := O_coords a b ha hb A B C O R hA hB hC hOA hOB hOC hRpos
  obtain ⟨hPpt, hQpt⟩ := PQ_coords a b A B C P Q t w hA hB hC htP hwQ
  obtain ⟨ht1, ht2, hw1, hw2⟩ :=
    tangency_polys a b A B C P Q S r t w hA hB hC hPpt hQpt hSP hSQ hSPperp hSQperp
  have hs5 := bisector_sq a b ha S r t w ht1 ht2 hw1 hw2
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs5 with hcase | hcase
  · exact False.elim (not_external a b ha hb S O r R t w ht1 hw1 hcase hOx eOA hSO hr hRpos hDnn)
  obtain ⟨htw, hS0⟩ := internal_axis a b ha S t w ht1 hw1 hcase
  rw [hS0] at ht1 ht2
  simp only [zero_add] at ht1 ht2
  have hZ : a * (S 1 - (1 - t) * a) = -(t * b ^ 2) := by linear_combination ht1
  have hr2 := radius_sq a b u r t hu2 S ht1 ht2
  have hSpt : S = !₂[0, S 1] :=
    pt_ext (by simp [hS0, Matrix.cons_val_zero]) (by simp [Matrix.cons_val_one])
  have hOpt : O = !₂[0, O 1] :=
    pt_ext (by simp [hOx, Matrix.cons_val_zero]) (by simp [Matrix.cons_val_one])
  have hfinal :=
    final_height a b u r R t ha hb hu hu2 hr S O hoy hR2a hZ hr2 hSpt hOpt hSO
  rw [← htw] at hQpt
  rw [hPpt, hQpt]
  apply pt_ext
  · rw [midpoint_eq_smul_add]
    simp [smul_eq_mul, Matrix.cons_val_zero]
  · rw [midpoint_eq_smul_add]
    simp only [WithLp.ofLp_smul, WithLp.ofLp_add, Pi.smul_apply, Pi.add_apply,
      smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
    have e2 : (⅟2 : ℝ) = 1 / 2 := by rw [invOf_eq_inv]; norm_num
    rw [e2]
    linear_combination hfinal

end Imo1978P4
