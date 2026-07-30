/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Euclidean.Sphere.Basic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# USA Mathematical Olympiad 1999, Problem 6

Let `ABCD` be an isosceles trapezoid with `AB ∥ CD`. The inscribed circle `ω` of
triangle `BCD` meets `CD` at `E`. Let `F` be a point on the (internal) angle
bisector of `∠DAC` such that `EF ⊥ CD`. Let the circumscribed circle of
triangle `ACF` meet line `CD` at `C` and `G`. Prove that triangle `AFG` is
isosceles.

# Formalization notes

We place the isosceles trapezoid in the coordinate plane in its standard
symmetric position: `A = (−a, h)`, `B = (a, h)`, `C = (d, 0)`, `D = (−d, 0)`
with `0 < a < d` and `0 < h`. Every isosceles trapezoid with `AB ∥ CD` can be
moved to this position by a rigid motion (the axis of symmetry being the
`y`-axis), and the condition `a ≠ d` (here strengthened to `a < d`, which can be
achieved by relabelling) rules out the parallelogram case.

The remaining data are encoded as follows:

* `E`, the point where the incircle of `△BCD` touches `CD`, is characterized by
  the standard equal-tangent-lengths formula `E ∈ segment ℝ C D` together with
  `dist C E = (dist B C + dist C D - dist B D) / 2`.
* `F` lying on the internal bisector of `∠DAC` is expressed by saying that `F`
  is on the ray from `A` in the direction of the sum of the unit vectors along
  `AD` and `AC`.
* `EF ⊥ CD` is `inner ℝ (F - E) (D - C) = 0`.
* `G` lies on line `CD` (`Collinear ℝ {C, D, G}`), `G ≠ C`, and `A, C, F, G`
  are concyclic.

The conclusion "`△AFG` is isosceles" is proved in the form `AF = GF`
(i.e. `dist A F = dist G F`), which is the actual content of the official
problem.

# Solution

Direct coordinate computation. Writing `p = |AD| = |BC|` and `q = |AC| = |BD|`
(so `p² = (d − a)² + h²`, `q² = (d + a)² + h²`), one finds `E = ((q − p)/2, 0)`,
`F = ((q − p)/2, f)` with
`f = (a² − d² + h² − pq + a(q − p) − d(p + q)) / (2h)`
(in fact `F` is the excenter of `△ACD` opposite `A`, with
`f = −2dh / (p + q − 2d)`), and `G = (−d − p, 0)`.
The claim `AF² = GF²` then reduces to algebraic identities that are checked
here by `linear_combination` certificates against the relations
`p² = (d − a)² + h²` and `q² = (d + a)² + h²`.
-/

namespace Usa1999P6

open EuclideanGeometry

snip begin

/-- Distance in the Euclidean plane as a square root of a sum of squares. -/
lemma dist_eq_sqrt_fin2 (x y : EuclideanSpace ℝ (Fin 2)) :
    dist x y = Real.sqrt ((x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2) := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
  simp [Real.dist_eq, sq_abs]

/-- Squared distance in the Euclidean plane as a sum of squares. -/
lemma dist_sq_fin2 (x y : EuclideanSpace ℝ (Fin 2)) :
    dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two]
  simp [Real.dist_eq, sq_abs]

/-- Inner product in the Euclidean plane in coordinates. -/
lemma inner_fin2 (x y : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ x y = x 0 * y 0 + x 1 * y 1 := by
  rw [PiLp.inner_apply, Fin.sum_univ_two]
  simp [RCLike.inner_apply]
  ring

/-- The algebraic identity behind the computation of the second coordinate of
`F` from the angle-bisector condition. -/
lemma key_bisector {a d h p q V : ℝ}
    (hV : V = a ^ 2 - d ^ 2 + h ^ 2 - p * q + a * (q - p) - d * (p + q))
    (hp : p ^ 2 = (d - a) ^ 2 + h ^ 2) (hq : q ^ 2 = (d + a) ^ 2 + h ^ 2) :
    (2 * h ^ 2 - V) * (q * (a - d) + p * (a + d)) =
      2 * h ^ 2 * (p + q) * ((q - p) / 2 + a) := by
  subst hV
  linear_combination
    (a ^ 2 + 2 * a * d + a * q + d ^ 2 + d * q + h ^ 2) * hp +
      (-a ^ 2 + 2 * a * d + a * p - d ^ 2 - d * p - h ^ 2) * hq

/-- The identity identifying `V / (2h)` with the (negated) exradius
`−2dh / (p + q − 2d)`; used to see that `F` lies below the line `CD`. -/
lemma key_exradius {a d h p q V : ℝ}
    (hV : V = a ^ 2 - d ^ 2 + h ^ 2 - p * q + a * (q - p) - d * (p + q))
    (hp : p ^ 2 = (d - a) ^ 2 + h ^ 2) (hq : q ^ 2 = (d + a) ^ 2 + h ^ 2) :
    V * (p + q - 2 * d) = -4 * d * h ^ 2 := by
  subst hV
  linear_combination (-a - d - q) * hp + (a - d - p) * hq

/-- The algebraic identity behind the computation of `G` from the concyclicity
condition. -/
lemma key_circle {a d h p q V f : ℝ}
    (hV : V = a ^ 2 - d ^ 2 + h ^ 2 - p * q + a * (q - p) - d * (p + q))
    (hf : 2 * h * f = V)
    (hp : p ^ 2 = (d - a) ^ 2 + h ^ 2) (hq : q ^ 2 = (d + a) ^ 2 + h ^ 2) :
    4 * h ^ 2 *
        (h * ((q - p) / 2) * (d - (q - p) / 2) -
           h * f ^ 2 +
           f * (a ^ 2 + a * d + h ^ 2) +
           (d + p) * (h * (d - (q - p) / 2) - f * (a + d))) =
      0 := by
  subst hV
  linear_combination
    (a ^ 2 * h + 2 * a * d * h + d ^ 2 * h + h ^ 3 - h * q ^ 2) * hp +
      (-2 * a ^ 2 * h + 4 * a * d * h + 2 * a * h * p - 2 * d ^ 2 * h - 2 * d * h * p -
        2 * h ^ 3) * hq +
      (a ^ 2 * h - a * h * p - a * h * q - d ^ 2 * h - d * h * p + d * h * q -
        2 * f * h ^ 2 + h ^ 3 + h * p * q) * hf

/-- The final identity `AF² = GF²`. -/
lemma key_dist {a d h p q V f : ℝ}
    (hV : V = a ^ 2 - d ^ 2 + h ^ 2 - p * q + a * (q - p) - d * (p + q))
    (hf : 2 * h * f = V) :
    ((q - p) / 2 + a) ^ 2 + (f - h) ^ 2 = ((q - p) / 2 + d + p) ^ 2 + f ^ 2 := by
  subst hV
  linear_combination -hf

snip end

problem usa1999_p6
    (a d h : ℝ) (ha : 0 < a) (had : a < d) (hh : 0 < h)
    (A B C D E F G : EuclideanSpace ℝ (Fin 2))
    (hA : A = !₂[-a, h]) (hB : B = !₂[a, h]) (hC : C = !₂[d, 0]) (hD : D = !₂[-d, 0])
    (hEseg : E ∈ segment ℝ C D)
    (hElen : dist C E = (dist B C + dist C D - dist B D) / 2)
    (hFb : ∃ t : ℝ, 0 < t ∧
      F = A + t • ((‖D - A‖⁻¹ • (D - A)) + (‖C - A‖⁻¹ • (C - A))))
    (hFperp : inner ℝ (F - E) (D - C) = 0)
    (hGcol : Collinear ℝ ({C, D, G} : Set (EuclideanSpace ℝ (Fin 2))))
    (hGne : G ≠ C)
    (hcyc : Concyclic ({A, C, F, G} : Set (EuclideanSpace ℝ (Fin 2)))) :
    dist A F = dist G F := by
  have hd : 0 < d := lt_trans ha had
  have hh2 : 0 < h ^ 2 := pow_pos hh 2
  -- The two diagonal/side lengths `p = |AD| = |BC|`, `q = |AC| = |BD|`.
  generalize hp_def : Real.sqrt ((d - a) ^ 2 + h ^ 2) = p
  generalize hq_def : Real.sqrt ((d + a) ^ 2 + h ^ 2) = q
  have hP : 0 < (d - a) ^ 2 + h ^ 2 := add_pos_of_nonneg_of_pos (sq_nonneg _) hh2
  have hQ : 0 < (d + a) ^ 2 + h ^ 2 := add_pos_of_nonneg_of_pos (sq_nonneg _) hh2
  have hp : 0 < p := by rw [← hp_def]; exact Real.sqrt_pos_of_pos hP
  have hq : 0 < q := by rw [← hq_def]; exact Real.sqrt_pos_of_pos hQ
  have hp2 : p ^ 2 = (d - a) ^ 2 + h ^ 2 := by rw [← hp_def]; exact Real.sq_sqrt (le_of_lt hP)
  have hq2 : q ^ 2 = (d + a) ^ 2 + h ^ 2 := by rw [← hq_def]; exact Real.sq_sqrt (le_of_lt hQ)
  -- `p < q`, hence `E 0 = (q - p)/2 > 0`.
  have hqp : p < q := by
    have h1 : p ^ 2 < q ^ 2 := by
      rw [hp2, hq2]
      have e : 0 < a * d := mul_pos ha hd
      linarith [e]
    exact lt_of_pow_lt_pow_left₀ 2 (le_of_lt hq) h1
  -- Triangle inequality `2d < p + q`.
  have hsp : 2 * d < p + q := by
    have hpq2 : (p * q) ^ 2 = ((d - a) ^ 2 + h ^ 2) * ((d + a) ^ 2 + h ^ 2) := by
      rw [mul_pow, hp2, hq2]
    have h2 : ((d - a) ^ 2 + h ^ 2) * ((d + a) ^ 2 + h ^ 2) - (d ^ 2 - a ^ 2 - h ^ 2) ^ 2 =
        4 * d ^ 2 * h ^ 2 := by ring
    have h1 : (d ^ 2 - a ^ 2 - h ^ 2) ^ 2 < (p * q) ^ 2 := by
      rw [hpq2]
      have e : (0 : ℝ) < 4 * d ^ 2 * h ^ 2 := by positivity
      linarith [h2, e]
    have h3 : d ^ 2 - a ^ 2 - h ^ 2 < p * q :=
      lt_of_pow_lt_pow_left₀ 2 (le_of_lt (mul_pos hp hq)) h1
    have e1 : p ^ 2 + q ^ 2 = 2 * a ^ 2 + 2 * d ^ 2 + 2 * h ^ 2 := by
      linear_combination hp2 + hq2
    have e2 : (p + q) ^ 2 = p ^ 2 + q ^ 2 + 2 * (p * q) := by ring
    have e3 : (2 * d) ^ 2 = 4 * d ^ 2 := by ring
    have h4 : (2 * d) ^ 2 < (p + q) ^ 2 := by linarith [e1, e2, e3, h3]
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity : 0 ≤ p + q) h4
  -- `E 0 = (q - p)/2 < d`.
  have he_lt_d : (q - p) / 2 < d := by
    have h1' : q ^ 2 - p ^ 2 = 4 * a * d := by linear_combination hq2 - hp2
    have e1 : (p + 2 * d) ^ 2 = p ^ 2 + 4 * (d * p) + 4 * d ^ 2 := by ring
    have e2 : 0 < d * p := mul_pos hd hp
    have e3 : 0 < d * (d - a) := mul_pos hd (sub_pos.2 had)
    have e4 : a * d < d ^ 2 + d * p := by linarith [e2, e3]
    have h1 : q ^ 2 < (p + 2 * d) ^ 2 := by linarith [h1', e1, e4]
    have h2 : q < p + 2 * d := lt_of_pow_lt_pow_left₀ 2 (by positivity : 0 ≤ p + 2 * d) h1
    linarith [h2]
  -- The direction `x`-component of the angle bisector is positive.
  have hDelta : 0 < q * (a - d) + p * (a + d) := by
    have h1 : p ^ 2 * (a + d) ^ 2 - q ^ 2 * (a - d) ^ 2 = 4 * a * d * h ^ 2 := by
      linear_combination ((a + d) ^ 2) * hp2 - ((a - d) ^ 2) * hq2
    have h2 : (q * (d - a)) ^ 2 < (p * (a + d)) ^ 2 := by
      have e1 : (q * (d - a)) ^ 2 = q ^ 2 * (a - d) ^ 2 := by ring
      have e2 : (p * (a + d)) ^ 2 = p ^ 2 * (a + d) ^ 2 := by ring
      rw [e1, e2]
      have e3 : (0 : ℝ) < 4 * a * d * h ^ 2 := by positivity
      linarith [h1, e3]
    have h3 : q * (d - a) < p * (a + d) :=
      lt_of_pow_lt_pow_left₀ 2 (le_of_lt (mul_pos hp (by linarith [ha, hd]))) h2
    linarith [h3]
  -- Distances between the vertices.
  have hdBC : dist B C = p := by
    rw [← hp_def, hB, hC, dist_eq_sqrt_fin2]
    congr 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  have hdBD : dist B D = q := by
    rw [← hq_def, hB, hD, dist_eq_sqrt_fin2]
    congr 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  have hdCD : dist C D = 2 * d := by
    rw [hC, hD, dist_eq_sqrt_fin2]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [show (d - -d) ^ 2 + ((0 : ℝ) - 0) ^ 2 = (2 * d) ^ 2 by ring,
      Real.sqrt_sq (by linarith [hd] : 0 ≤ 2 * d)]
  have hdAD : dist A D = p := by
    rw [← hp_def, hA, hD, dist_eq_sqrt_fin2]
    congr 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  have hdAC : dist A C = q := by
    rw [← hq_def, hA, hC, dist_eq_sqrt_fin2]
    congr 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  have hnormDA : ‖D - A‖ = p := by rw [← dist_eq_norm, dist_comm]; exact hdAD
  have hnormCA : ‖C - A‖ = q := by rw [← dist_eq_norm, dist_comm]; exact hdAC
  -- The coordinates of `E`.
  obtain ⟨u, v, hu, hv, huv, hEuv⟩ := hEseg
  have hE1 : E 1 = 0 := by
    have h1 : (u • C + v • D) 1 = E 1 := by rw [hEuv]
    rw [hC, hD] at h1
    simp only [PiLp.add_apply, PiLp.smul_apply, Matrix.cons_val_one,
      Matrix.cons_val_zero, smul_eq_mul] at h1
    linarith [h1]
  have hE0le : E 0 ≤ d := by
    have h0 : (u • C + v • D) 0 = E 0 := by rw [hEuv]
    rw [hC, hD] at h0
    simp only [PiLp.add_apply, PiLp.smul_apply, Matrix.cons_val_zero,
      smul_eq_mul] at h0
    have hu1 : u ≤ 1 := by linarith [huv, hv]
    have hdu : u * d ≤ d := by
      have e := mul_le_mul_of_nonneg_right hu1 (le_of_lt hd)
      linarith [e, hd]
    have hvd : 0 ≤ v * d := mul_nonneg hv (le_of_lt hd)
    linarith [h0, hdu, hvd, hd]
  have hCE : dist C E = d - E 0 := by
    rw [hC, dist_eq_sqrt_fin2]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hE1,
      show (d - E 0) ^ 2 + (0 - (0 : ℝ)) ^ 2 = (d - E 0) ^ 2 by ring,
      Real.sqrt_sq_eq_abs]
    exact abs_of_nonneg (sub_nonneg.2 hE0le)
  have hE0 : E 0 = (q - p) / 2 := by
    rw [hdBC, hdCD, hdBD, hCE] at hElen
    linarith [hElen]
  -- The coordinates of `F`, part 1: `F 0 = E 0` from `EF ⊥ CD`.
  have hF0 : F 0 = (q - p) / 2 := by
    have h1 : inner ℝ (F - E) (D - C) =
        (F 0 - E 0) * (D 0 - C 0) + (F 1 - E 1) * (D 1 - C 1) := by
      rw [inner_fin2]
      simp [PiLp.sub_apply]
    rw [h1, hC, hD] at hFperp
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hFperp
    rw [hE0, hE1] at hFperp
    have h2 : (F 0 - (q - p) / 2) * (-(2 : ℝ) * d) = 0 := by
      ring_nf at hFperp ⊢
      linarith [hFperp]
    rcases mul_eq_zero.1 h2 with h | h
    · linarith [h]
    · exfalso
      linarith [hd, h]
  -- The coordinates of `F`, part 2: use the angle-bisector ray condition.
  obtain ⟨t, ht, hFt⟩ := hFb
  have hF0eq : (A + t • ((‖D - A‖⁻¹ • (D - A)) + (‖C - A‖⁻¹ • (C - A)))) 0 = F 0 := by
    rw [hFt]
  have hF1eq : (A + t • ((‖D - A‖⁻¹ • (D - A)) + (‖C - A‖⁻¹ • (C - A)))) 1 = F 1 := by
    rw [hFt]
  rw [hF0, hnormDA, hnormCA, hA, hC, hD] at hF0eq
  simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply,
    Matrix.cons_val_zero, smul_eq_mul] at hF0eq
  rw [hnormDA, hnormCA, hA, hC, hD] at hF1eq
  simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul] at hF1eq
  -- Eliminating `t` from the coordinate equations.
  have htΔ : t * (q * (a - d) + p * (a + d)) = ((q - p) / 2 + a) * (p * q) := by
    have e := hF0eq
    field_simp [hp.ne', hq.ne'] at e
    linarith [e]
  have hF1eqP : (h - F 1) * (p * q) = t * h * (p + q) := by
    have e := hF1eq
    field_simp [hp.ne', hq.ne'] at e
    linarith [e]
  -- The second coordinate of `F`, via the polynomial `V`.
  generalize hV_def : a ^ 2 - d ^ 2 + h ^ 2 - p * q + a * (q - p) - d * (p + q) = V
  have hI1 : (2 * h ^ 2 - V) * (q * (a - d) + p * (a + d)) =
      2 * h ^ 2 * (p + q) * ((q - p) / 2 + a) := key_bisector hV_def.symm hp2 hq2
  have hf1 : 2 * h * (F 1) = V := by
    have hΔne : q * (a - d) + p * (a + d) ≠ 0 := ne_of_gt hDelta
    have hpqne : p * q ≠ 0 := ne_of_gt (mul_pos hp hq)
    have e1 : (2 * h ^ 2 - V) * (p * q) * (q * (a - d) + p * (a + d)) =
        2 * h * (h - F 1) * (p * q) * (q * (a - d) + p * (a + d)) := by
      linear_combination (p * q) * hI1 - (2 * h ^ 2 * (p + q)) * htΔ -
        (2 * h * (q * (a - d) + p * (a + d))) * hF1eqP
    have e2 : (2 * h ^ 2 - V) * (p * q) = 2 * h * (h - F 1) * (p * q) :=
      mul_right_cancel₀ hΔne e1
    have e3 : 2 * h ^ 2 - V = 2 * h * (h - F 1) := mul_right_cancel₀ hpqne e2
    linarith [e3]
  -- `V < 0`, so `F` lies strictly below the line `CD`.
  have hV_neg : V < 0 := by
    have hI4 : V * (p + q - 2 * d) = -4 * d * h ^ 2 := key_exradius hV_def.symm hp2 hq2
    have h1 : V * (p + q - 2 * d) < 0 := by
      rw [hI4]
      have e : (0 : ℝ) < 4 * d * h ^ 2 := by positivity
      linarith [e]
    by_contra hc
    push Not at hc
    have h2 : 0 ≤ V * (p + q - 2 * d) := mul_nonneg hc (by linarith [hsp])
    linarith [h1, h2]
  -- `G 1 = 0` from collinearity with `C` and `D`.
  have hG1 : G 1 = 0 := by
    rw [collinear_iff_exists_forall_eq_smul_vadd] at hGcol
    obtain ⟨p₀, w, hw⟩ := hGcol
    obtain ⟨r₁, hr₁⟩ := hw C (by simp)
    obtain ⟨r₂, hr₂⟩ := hw D (by simp)
    obtain ⟨r₃, hr₃⟩ := hw G (by simp)
    have h1 : (r₁ • w +ᵥ p₀) 1 = C 1 := by rw [← hr₁]
    have h2 : (r₂ • w +ᵥ p₀) 1 = D 1 := by rw [← hr₂]
    have h3 : (r₃ • w +ᵥ p₀) 1 = G 1 := by rw [← hr₃]
    rw [hC] at h1; rw [hD] at h2
    simp only [vadd_eq_add, PiLp.add_apply, PiLp.smul_apply,
      Matrix.cons_val_one, Matrix.cons_val_zero, smul_eq_mul] at h1 h2 h3
    have h4 : (r₁ - r₂) * w 1 = 0 := by linarith
    rcases mul_eq_zero.1 h4 with hrr | hw1
    · exfalso
      have h5 : r₁ = r₂ := by linarith
      have hCD : C = D := by rw [hr₁, hr₂, h5]
      rw [hC, hD] at hCD
      have h6 : (!₂[d, (0 : ℝ)] : EuclideanSpace ℝ (Fin 2)) 0 =
          (!₂[-d, (0 : ℝ)] : EuclideanSpace ℝ (Fin 2)) 0 := by rw [hCD]
      simp only [Matrix.cons_val_zero] at h6
      linarith [hd, h6]
    · rw [hw1] at h1 h3
      simp only [mul_zero, zero_add] at h1 h3
      linarith [h1, h3]
  -- The circle through `A`, `C`, `F`, `G`.
  obtain ⟨O, ρ, hO⟩ := hcyc.Cospherical
  have hAO : dist A O = ρ := hO A (Set.mem_insert _ _)
  have hCO : dist C O = ρ := hO C (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hFO : dist F O = ρ :=
    hO F (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
  have hGO : dist G O = ρ :=
    hO G (Set.mem_insert_of_mem _
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
  -- From `dist C O = dist G O`: either `G = C` (excluded) or `2·O 0 = d + G 0`.
  have hCG : (d - O 0) ^ 2 = (G 0 - O 0) ^ 2 := by
    have e1 : dist C O ^ 2 = (C 0 - O 0) ^ 2 + (C 1 - O 1) ^ 2 := dist_sq_fin2 C O
    have e2 : dist G O ^ 2 = (G 0 - O 0) ^ 2 + (G 1 - O 1) ^ 2 := dist_sq_fin2 G O
    rw [hCO] at e1; rw [hGO] at e2
    rw [hC] at e1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e1
    rw [hG1] at e2
    linarith [e1, e2]
  have hO0 : 2 * O 0 = d + G 0 := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hCG with h | h
    · exfalso
      apply hGne
      have g0 : G 0 = d := by linarith [h]
      rw [hC]
      ext i
      fin_cases i
      · simpa [Matrix.cons_val_zero] using g0
      · simpa [Matrix.cons_val_one, Matrix.cons_val_zero] using hG1
    · linarith [h]
  -- From `dist A O = dist C O`: an equation for `O 1`.
  have hO1 : 2 * h * O 1 = (a + O 0) ^ 2 + h ^ 2 - (d - O 0) ^ 2 := by
    have e1 : dist A O ^ 2 = (A 0 - O 0) ^ 2 + (A 1 - O 1) ^ 2 := dist_sq_fin2 A O
    have e2 : dist C O ^ 2 = (C 0 - O 0) ^ 2 + (C 1 - O 1) ^ 2 := dist_sq_fin2 C O
    rw [hAO] at e1; rw [hCO] at e2
    rw [hA] at e1; rw [hC] at e2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e1 e2
    linear_combination e1 - e2
  -- From `dist F O = dist C O`: the linear equation determining `G 0`.
  have hFsq : (F 0 - O 0) ^ 2 + (F 1 - O 1) ^ 2 = (d - O 0) ^ 2 + (0 - O 1) ^ 2 := by
    have e1 : dist F O ^ 2 = (F 0 - O 0) ^ 2 + (F 1 - O 1) ^ 2 := dist_sq_fin2 F O
    have e2 : dist C O ^ 2 = (C 0 - O 0) ^ 2 + (C 1 - O 1) ^ 2 := dist_sq_fin2 C O
    rw [hFO] at e1; rw [hCO] at e2
    rw [hC] at e2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e2
    linarith [e1, e2]
  rw [hF0] at hFsq
  have hGeq : G 0 * (h * (d - (q - p) / 2) - (F 1) * (a + d)) =
      h * ((q - p) / 2) * (d - (q - p) / 2) - h * (F 1) ^ 2 +
        (F 1) * (a ^ 2 + a * d + h ^ 2) := by
    linear_combination
      h * hFsq + (-h * (d - (q - p) / 2) + (F 1) * (a + d)) * hO0 + (F 1) * hO1
  -- Hence `(G 0 + d + p) * Φ = 0` with `Φ ≠ 0`.
  have hI2 : 4 * h ^ 2 *
        (h * ((q - p) / 2) * (d - (q - p) / 2) -
           h * (F 1) ^ 2 +
           (F 1) * (a ^ 2 + a * d + h ^ 2) +
           (d + p) * (h * (d - (q - p) / 2) - (F 1) * (a + d))) =
      0 := key_circle hV_def.symm hf1 hp2 hq2
  have hG0dp4 : 4 * h ^ 2 *
      ((G 0 + d + p) * (h * (d - (q - p) / 2) - (F 1) * (a + d))) = 0 := by
    linear_combination (4 * h ^ 2) * hGeq + hI2
  have hG0dp : (G 0 + d + p) * (h * (d - (q - p) / 2) - (F 1) * (a + d)) = 0 := by
    rcases mul_eq_zero.1 hG0dp4 with h | h
    · exfalso
      linarith [hh2, h]
    · exact h
  have hPhi_pos : 0 < h * (d - (q - p) / 2) - (F 1) * (a + d) := by
    have t1 : 0 < h * (d - (q - p) / 2) := mul_pos hh (by linarith [he_lt_d])
    have s1 : F 1 < 0 := by
      by_contra hc
      push Not at hc
      have e : 0 ≤ 2 * h * (F 1) := mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hh)) hc
      rw [hf1] at e
      linarith [e, hV_neg]
    have s2 : 0 < a + d := by linarith [ha, hd]
    have t2 : 0 < -(F 1) * (a + d) := mul_pos (neg_pos.2 s1) s2
    linarith [t1, t2]
  have hG0 : G 0 = -d - p := by
    rcases mul_eq_zero.1 hG0dp with h | h
    · linarith [h]
    · exfalso
      linarith [hPhi_pos, h]
  -- Conclusion: `AF = GF` via the squared-distance identity.
  have hI3 : ((q - p) / 2 + a) ^ 2 + (F 1 - h) ^ 2 =
      ((q - p) / 2 + d + p) ^ 2 + (F 1) ^ 2 := key_dist hV_def.symm hf1
  rw [hA, dist_eq_sqrt_fin2, dist_eq_sqrt_fin2, hF0, hG0, hG1]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  congr 1
  linear_combination hI3

end Usa1999P6
