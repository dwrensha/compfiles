/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry, .Inequality] }

/-!
# USA Mathematical Olympiad 1999, Problem 2

Let ABCD be a convex cyclic quadrilateral. Prove that
|AB - CD| + |AD - BC| ≥ 2|AC - BD|.
-/

namespace Usa1999P2

open Real

snip begin

-- Any convex cyclic quadrilateral can be moved by a rigid motion so that its
-- circumcenter is the origin, and then its vertices are at angles
-- a < b < c < d < a + 2π on the circle of some radius R > 0 (possibly in the
-- opposite orientation, which gives the same inequality). We therefore prove
-- the inequality for points parametrized in this way.
--
-- If p = (b-a)/2, q = (c-b)/2, r = (d-c)/2, then the chord-length formula
-- below gives AB = 2R sin p, BC = 2R sin q, CD = 2R sin r,
-- AD = 2R sin (p+q+r), AC = 2R sin (p+q), BD = 2R sin (q+r),
-- and the claim reduces to `key_ineq` below.  With
-- φ = (p+r)/2, ψ = (p-r)/2, θ = (p+2q+r)/2, the three sine differences
-- become 2 sin ψ cos φ, 2 sin φ cos θ and 2 sin ψ cos θ respectively, and
-- since |sin ψ| ≤ sin φ and |cos θ| ≤ cos φ the inequality follows from
-- A cos φ + B sin φ ≥ 2 A B for 0 ≤ A ≤ sin φ and 0 ≤ B ≤ cos φ.

/--
The square of the length of the chord joining the two points at angles `a` and
`b` on the circle of radius `R` centered at the origin.
-/
lemma chord_sq (R a b : ℝ) :
    (R * cos a - R * cos b) ^ 2 + (R * sin a - R * sin b) ^ 2
      = (2 * R * sin ((b - a) / 2)) ^ 2 := by
  have h1 : R * cos a - R * cos b = -2 * R * sin ((a + b) / 2) * sin ((a - b) / 2) := by
    rw [show R * cos a - R * cos b = R * (cos a - cos b) by ring, cos_sub_cos]
    ring
  have h2 : R * sin a - R * sin b = 2 * R * sin ((a - b) / 2) * cos ((a + b) / 2) := by
    rw [show R * sin a - R * sin b = R * (sin a - sin b) by ring, sin_sub_sin]
    ring
  rw [h1, h2]
  have h3 : (-2 * R * sin ((a + b) / 2) * sin ((a - b) / 2)) ^ 2
      + (2 * R * sin ((a - b) / 2) * cos ((a + b) / 2)) ^ 2
      = 4 * R ^ 2 * sin ((a - b) / 2) ^ 2
        * (sin ((a + b) / 2) ^ 2 + cos ((a + b) / 2) ^ 2) := by
    ring
  rw [h3, sin_sq_add_cos_sq, mul_one]
  have h4 : sin ((a - b) / 2) ^ 2 = sin ((b - a) / 2) ^ 2 := by
    rw [show (a - b) / 2 = -((b - a) / 2) by ring, sin_neg, neg_sq]
  rw [h4]
  ring

/--
The length of the chord joining the two points at angles `a` and `b` (with
`a < b < a + 2π`) on the circle of radius `R` centered at the origin.
-/
lemma chord_length (R a b : ℝ) (hR : 0 < R) (hab : a < b) (hba : b < a + 2 * π) :
    dist (!₂[R * cos a, R * sin a] : EuclideanSpace ℝ (Fin 2)) !₂[R * cos b, R * sin b]
      = 2 * R * sin ((b - a) / 2) := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Real.dist_eq, sq_abs]
  have hsin : 0 ≤ sin ((b - a) / 2) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi <;> linarith
  have hpos : 0 ≤ 2 * R * sin ((b - a) / 2) := by positivity
  rw [chord_sq, Real.sqrt_sq hpos]

/--
The key trigonometric inequality: for `p q r > 0` with `p + q + r < π`,
`|sin p - sin r| + |sin (p+q+r) - sin q| ≥ 2 |sin (p+q) - sin (q+r)|`.
-/
lemma key_ineq (p q r : ℝ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (h : p + q + r < π) :
    |sin p - sin r| + |sin (p + q + r) - sin q| ≥ 2 * |sin (p + q) - sin (q + r)| := by
  have hφ0 : 0 < (p + r) / 2 := by linarith
  have hφπ : (p + r) / 2 < π / 2 := by linarith
  have hsinφ : 0 < sin ((p + r) / 2) :=
    Real.sin_pos_of_pos_of_lt_pi hφ0 (by linarith [Real.pi_pos])
  have hcosφ : 0 < cos ((p + r) / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hφπ⟩
  -- sum-to-product rewrites of the three sine differences
  have e1 : sin p - sin r = 2 * sin ((p - r) / 2) * cos ((p + r) / 2) :=
    Real.sin_sub_sin p r
  have e2 : sin (p + q + r) - sin q = 2 * sin ((p + r) / 2) * cos ((p + 2 * q + r) / 2) := by
    have e := Real.sin_sub_sin (p + q + r) q
    rwa [show (p + q + r - q) / 2 = (p + r) / 2 by ring,
      show (p + q + r + q) / 2 = (p + 2 * q + r) / 2 by ring] at e
  have e3 : sin (p + q) - sin (q + r) = 2 * sin ((p - r) / 2) * cos ((p + 2 * q + r) / 2) := by
    have e := Real.sin_sub_sin (p + q) (q + r)
    rwa [show (p + q - (q + r)) / 2 = (p - r) / 2 by ring,
      show (p + q + (q + r)) / 2 = (p + 2 * q + r) / 2 by ring] at e
  -- the bound |sin ((p - r) / 2)| ≤ sin ((p + r) / 2)
  have hψ : |(p - r) / 2| < (p + r) / 2 := by
    have h1 : |p - r| < p + r := by
      rw [abs_sub_lt_iff]
      exact ⟨by linarith, by linarith⟩
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hA : |sin ((p - r) / 2)| ≤ sin ((p + r) / 2) := by
    have h1 : |sin ((p - r) / 2)| = sin |(p - r) / 2| := by
      apply Real.abs_sin_eq_sin_abs_of_abs_le_pi
      linarith [hψ, hφπ, Real.pi_pos]
    rw [h1]
    apply Real.strictMonoOn_sin.monotoneOn
    · exact ⟨by linarith [abs_nonneg ((p - r) / 2), Real.pi_pos], by linarith⟩
    · exact ⟨by linarith [Real.pi_pos], le_of_lt hφπ⟩
    · exact le_of_lt hψ
  -- the bound |cos ((p + 2q + r) / 2)| ≤ cos ((p + r) / 2)
  have hB : |cos ((p + 2 * q + r) / 2)| ≤ cos ((p + r) / 2) := by
    have hθ0 : 0 < (p + 2 * q + r) / 2 := by linarith
    have hθπ : (p + 2 * q + r) / 2 < π := by linarith
    have h1 : cos ((p + 2 * q + r) / 2) ≤ cos ((p + r) / 2) :=
      Real.cos_le_cos_of_nonneg_of_le_pi hφ0.le hθπ.le (by linarith)
    have h2 : -cos ((p + r) / 2) ≤ cos ((p + 2 * q + r) / 2) := by
      have h3 := Real.cos_le_cos_of_nonneg_of_le_pi hθ0.le
        (show π - (p + r) / 2 ≤ π by linarith)
        (show (p + 2 * q + r) / 2 ≤ π - (p + r) / 2 by linarith)
      rw [Real.cos_pi_sub] at h3
      exact h3
    exact abs_le.mpr ⟨h2, h1⟩
  -- remove the absolute values of the factors with a definite sign
  have a1 : |2 * sin ((p - r) / 2) * cos ((p + r) / 2)|
      = 2 * |sin ((p - r) / 2)| * cos ((p + r) / 2) := by
    rw [abs_mul, abs_mul, abs_of_pos hcosφ, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have a2 : |2 * sin ((p + r) / 2) * cos ((p + 2 * q + r) / 2)|
      = 2 * sin ((p + r) / 2) * |cos ((p + 2 * q + r) / 2)| := by
    rw [abs_mul, abs_mul, abs_of_pos hsinφ, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have a3 : |2 * sin ((p - r) / 2) * cos ((p + 2 * q + r) / 2)|
      = 2 * |sin ((p - r) / 2)| * |cos ((p + 2 * q + r) / 2)| := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [e1, a1, e2, a2, e3, a3]
  -- finish with A cos φ + B sin φ ≥ 2AB
  have h1 := mul_le_mul_of_nonneg_left hB (abs_nonneg (sin ((p - r) / 2)))
  have h2 := mul_le_mul_of_nonneg_right hA (abs_nonneg (cos ((p + 2 * q + r) / 2)))
  linarith [h1, h2]

snip end

problem usa1999_p2 (R : ℝ) (hR : 0 < R) (a b c d : ℝ)
    (hab : a < b) (hbc : b < c) (hcd : c < d) (hd : d < a + 2 * π) :
    let P : ℝ → EuclideanSpace ℝ (Fin 2) := fun θ ↦ !₂[R * cos θ, R * sin θ]
    |dist (P a) (P b) - dist (P c) (P d)| + |dist (P a) (P d) - dist (P b) (P c)| ≥
      2 * |dist (P a) (P c) - dist (P b) (P d)| := by
  intro P
  have hAB : dist (P a) (P b) = 2 * R * sin ((b - a) / 2) :=
    chord_length R a b hR hab (by linarith)
  have hCD : dist (P c) (P d) = 2 * R * sin ((d - c) / 2) :=
    chord_length R c d hR hcd (by linarith)
  have hBC : dist (P b) (P c) = 2 * R * sin ((c - b) / 2) :=
    chord_length R b c hR hbc (by linarith)
  have hAD : dist (P a) (P d) = 2 * R * sin ((d - a) / 2) :=
    chord_length R a d hR (by linarith) hd
  have hAC : dist (P a) (P c) = 2 * R * sin ((c - a) / 2) :=
    chord_length R a c hR (by linarith) (by linarith)
  have hBD : dist (P b) (P d) = 2 * R * sin ((d - b) / 2) :=
    chord_length R b d hR (by linarith) (by linarith)
  rw [hAB, hCD, hBC, hAD, hAC, hBD]
  set p := (b - a) / 2 with hp_def
  set q := (c - b) / 2 with hq_def
  set r := (d - c) / 2 with hr_def
  have hs : (d - a) / 2 = p + q + r := by rw [hp_def, hq_def, hr_def]; ring
  have hcu : (c - a) / 2 = p + q := by rw [hp_def, hq_def]; ring
  have hcv : (d - b) / 2 = q + r := by rw [hq_def, hr_def]; ring
  rw [hs, hcu, hcv]
  have hp0 : 0 < p := by rw [hp_def]; linarith
  have hq0 : 0 < q := by rw [hq_def]; linarith
  have hr0 : 0 < r := by rw [hr_def]; linarith
  have hsum : p + q + r < π := by
    rw [hp_def, hq_def, hr_def,
      show (b - a) / 2 + (c - b) / 2 + (d - c) / 2 = (d - a) / 2 by ring]
    linarith
  have hscale : ∀ x y : ℝ, |2 * R * x - 2 * R * y| = 2 * R * |x - y| := by
    intro x y
    rw [← mul_sub, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * R)]
  simp only [hscale]
  have key := key_ineq p q r hp0 hq0 hr0 hsum
  have hmul := mul_le_mul_of_nonneg_left key (show (0 : ℝ) ≤ 2 * R by positivity)
  linarith [hmul]

end Usa1999P2
