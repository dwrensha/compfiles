/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.Normed.Affine.Convex
public import Mathlib.Geometry.Euclidean.Triangle
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# USA Mathematical Olympiad 2004, Problem 1

Let ABCD be a quadrilateral circumscribed about a circle, whose interior
and exterior angles are at least 60 degrees. Prove that

  (1/3)⬝|AB³ − AD³| ≤ |BC³ − CD³| ≤ 3⬝|AB³ − AD³|.

When does equality hold?

## Formalization notes

The hypothesis that `ABCD` is circumscribed about a circle is expressed by
giving the center `I` of the circle, its radius `r > 0`, and tangency points
`P ∈ AB`, `Q ∈ BC`, `R ∈ CD`, `S ∈ DA` at distance `r` from `I` such that the
radii to the tangency points are perpendicular to the corresponding sides.
The condition that the interior and exterior angles are all at least 60
degrees is expressed as each interior angle lying in the interval
`[π/3, 2π/3]`. Equality holds iff `ABCD` is a kite with `AB = AD` and
`CB = CD`, which is expressed by the `↔` statement at the end.
-/

namespace Usa2004P1

open scoped EuclideanGeometry InnerProductSpace

snip begin

/-- Reversing a subtraction inside a vanishing inner product. -/
lemma inner_eq_zero_vsub_rev {u v w : EuclideanSpace ℝ (Fin 2)} (h : ⟪u, v -ᵥ w⟫_ℝ = 0) :
    ⟪u, w -ᵥ v⟫_ℝ = 0 := by
  rw [← neg_eq_zero, ← inner_neg_right, neg_vsub_eq_vsub_rev w v]
  exact h

/-- The Pythagorean theorem at a tangency point: if `P` lies on segment `XY`
and `IP` is perpendicular to `XY`, then `dist X I ^ 2 = dist X P ^ 2 + dist I P ^ 2`. -/
lemma dist_sq_eq_dist_sq_add_dist_sq_of_tangent {X Y I P : EuclideanSpace ℝ (Fin 2)}
    (hP : P ∈ segment ℝ X Y) (hperp : ⟪I -ᵥ P, X -ᵥ Y⟫_ℝ = 0) :
    dist X I ^ 2 = dist X P ^ 2 + dist I P ^ 2 := by
  rw [segment_eq_image_lineMap] at hP
  obtain ⟨t, -, rfl⟩ := hP
  have h2 : ⟪X -ᵥ Y, AffineMap.lineMap X Y t -ᵥ I⟫_ℝ = 0 := by
    rw [← neg_eq_zero, ← inner_neg_right, neg_vsub_eq_vsub_rev (AffineMap.lineMap X Y t) I,
      real_inner_comm]
    exact hperp
  have hinner : ⟪X -ᵥ AffineMap.lineMap X Y t, AffineMap.lineMap X Y t -ᵥ I⟫_ℝ = 0 := by
    rw [AffineMap.left_vsub_lineMap, real_inner_smul_left, h2, mul_zero]
  have hdecomp : X -ᵥ I = (X -ᵥ AffineMap.lineMap X Y t) + (AffineMap.lineMap X Y t -ᵥ I) := by
    rw [vsub_eq_sub, vsub_eq_sub, vsub_eq_sub, sub_add_sub_cancel]
  have key : ‖X -ᵥ I‖ ^ 2 = ‖X -ᵥ AffineMap.lineMap X Y t‖ ^ 2 +
      ‖AffineMap.lineMap X Y t -ᵥ I‖ ^ 2 := by
    rw [hdecomp, norm_add_sq_real, hinner]
    ring
  rw [dist_eq_norm_vsub (EuclideanSpace ℝ (Fin 2)) X I,
    dist_eq_norm_vsub (EuclideanSpace ℝ (Fin 2)) X (AffineMap.lineMap X Y t),
    dist_eq_norm_vsub' (EuclideanSpace ℝ (Fin 2)) I (AffineMap.lineMap X Y t)]
  exact key

/-- **Equal tangents**: if a circle with center `I` is tangent to segments `XY` and `XZ`
at `P` and `Q` respectively, then the two tangent segments from `X` have equal length. -/
lemma tangent_dist_eq {X Y Z I P Q : EuclideanSpace ℝ (Fin 2)}
    (hP : P ∈ segment ℝ X Y) (hQ : Q ∈ segment ℝ X Z)
    (hperpP : ⟪I -ᵥ P, X -ᵥ Y⟫_ℝ = 0) (hperpQ : ⟪I -ᵥ Q, X -ᵥ Z⟫_ℝ = 0)
    (hIPQ : dist I P = dist I Q) :
    dist X P = dist X Q := by
  have h1 := dist_sq_eq_dist_sq_add_dist_sq_of_tangent hP hperpP
  have h2 := dist_sq_eq_dist_sq_add_dist_sq_of_tangent hQ hperpQ
  rw [← hIPQ] at h2
  have hsq : dist X P ^ 2 = dist X Q ^ 2 := by linarith
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · exact h
  · have e1 := dist_nonneg (x := X) (y := P)
    have e2 := dist_nonneg (x := X) (y := Q)
    linarith

/-- The cube difference factors through the tangent lengths. -/
lemma abs_cube_sub_cube {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |x ^ 3 - y ^ 3| = |x - y| * (x ^ 2 + x * y + y ^ 2) := by
  have h1 : x ^ 3 - y ^ 3 = (x - y) * (x ^ 2 + x * y + y ^ 2) := by ring
  have h2 : 0 ≤ x ^ 2 + x * y + y ^ 2 := by
    linarith [mul_nonneg hx hy, sq_nonneg x, sq_nonneg y]
  rw [h1, abs_mul, abs_of_nonneg h2]

/-- The key estimate for the left inequality: under the law-of-cosines compatibility
`hBD` and the cosine bounds coming from the angle hypotheses,
`(1/3)(a² + ad + d²) ≤ b² + bc + c²`. Strict when `a ≠ d`. -/
lemma quad_left {a b c d ca cc : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hBD : a ^ 2 + d ^ 2 - 2 * a * d * ca = b ^ 2 + c ^ 2 - 2 * b * c * cc)
    (hca : ca ≤ 1 / 2) (hcc : -1 / 2 ≤ cc) :
    (1 / 3) * (a ^ 2 + a * d + d ^ 2) ≤ b ^ 2 + b * c + c ^ 2 := by
  have e1 : a ^ 2 + d ^ 2 - a * d ≤ a ^ 2 + d ^ 2 - 2 * a * d * ca := by
    have h := mul_le_mul_of_nonneg_left hca (mul_nonneg ha hd)
    linarith
  have e2 : b ^ 2 + c ^ 2 - 2 * b * c * cc ≤ b ^ 2 + b * c + c ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hcc (mul_nonneg hb hc)
    linarith
  have e3 : (1 / 3) * (a ^ 2 + a * d + d ^ 2) ≤ a ^ 2 + d ^ 2 - a * d := by
    nlinarith [sq_nonneg (a - d)]
  linarith [hBD]

/-- Strict version of `quad_left`. -/
lemma quad_left_strict {a b c d ca cc : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hBD : a ^ 2 + d ^ 2 - 2 * a * d * ca = b ^ 2 + c ^ 2 - 2 * b * c * cc)
    (hca : ca ≤ 1 / 2) (hcc : -1 / 2 ≤ cc)
    (hne : a ≠ d) :
    (1 / 3) * (a ^ 2 + a * d + d ^ 2) < b ^ 2 + b * c + c ^ 2 := by
  have e1 : a ^ 2 + d ^ 2 - a * d ≤ a ^ 2 + d ^ 2 - 2 * a * d * ca := by
    have h := mul_le_mul_of_nonneg_left hca (mul_nonneg ha hd)
    linarith
  have e2 : b ^ 2 + c ^ 2 - 2 * b * c * cc ≤ b ^ 2 + b * c + c ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hcc (mul_nonneg hb hc)
    linarith
  have e3 : (1 / 3) * (a ^ 2 + a * d + d ^ 2) < a ^ 2 + d ^ 2 - a * d := by
    have h : 0 < (a - d) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
    nlinarith
  linarith [hBD]

/-- The key estimate for the right inequality, by symmetry:
`(1/3)(b² + bc + c²) ≤ a² + ad + d²`. Strict when `b ≠ c`. -/
lemma quad_right {a b c d ca cc : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hBD : a ^ 2 + d ^ 2 - 2 * a * d * ca = b ^ 2 + c ^ 2 - 2 * b * c * cc)
    (hca : -1 / 2 ≤ ca) (hcc : cc ≤ 1 / 2) :
    (1 / 3) * (b ^ 2 + b * c + c ^ 2) ≤ a ^ 2 + a * d + d ^ 2 := by
  have e1 : b ^ 2 + c ^ 2 - b * c ≤ b ^ 2 + c ^ 2 - 2 * b * c * cc := by
    have h := mul_le_mul_of_nonneg_left hcc (mul_nonneg hb hc)
    linarith
  have e2 : a ^ 2 + d ^ 2 - 2 * a * d * ca ≤ a ^ 2 + a * d + d ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hca (mul_nonneg ha hd)
    linarith
  have e3 : (1 / 3) * (b ^ 2 + b * c + c ^ 2) ≤ b ^ 2 + c ^ 2 - b * c := by
    nlinarith [sq_nonneg (b - c)]
  linarith [hBD]

/-- Strict version of `quad_right`. -/
lemma quad_right_strict {a b c d ca cc : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hBD : a ^ 2 + d ^ 2 - 2 * a * d * ca = b ^ 2 + c ^ 2 - 2 * b * c * cc)
    (hca : -1 / 2 ≤ ca) (hcc : cc ≤ 1 / 2)
    (hne : b ≠ c) :
    (1 / 3) * (b ^ 2 + b * c + c ^ 2) < a ^ 2 + a * d + d ^ 2 := by
  have e1 : b ^ 2 + c ^ 2 - b * c ≤ b ^ 2 + c ^ 2 - 2 * b * c * cc := by
    have h := mul_le_mul_of_nonneg_left hcc (mul_nonneg hb hc)
    linarith
  have e2 : a ^ 2 + d ^ 2 - 2 * a * d * ca ≤ a ^ 2 + a * d + d ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hca (mul_nonneg ha hd)
    linarith
  have e3 : (1 / 3) * (b ^ 2 + b * c + c ^ 2) < b ^ 2 + c ^ 2 - b * c := by
    have h : 0 < (b - c) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
    nlinarith
  linarith [hBD]

/-- The purely algebraic core of the problem: given side lengths `a, b, c, d`
of a tangential quadrilateral (`hpitot`, a consequence of equal tangents) and the
law-of-cosines compatibility `hBD` with cosine bounds from the angle hypotheses,
the claimed inequalities hold, with equality exactly when `a = d` and `b = c`. -/
lemma usa2004_p1_algebra {a b c d ca cc : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hpitot : a + c = b + d)
    (hca1 : -1 / 2 ≤ ca) (hca2 : ca ≤ 1 / 2)
    (hcc1 : -1 / 2 ≤ cc) (hcc2 : cc ≤ 1 / 2)
    (hBD : a ^ 2 + d ^ 2 - 2 * a * d * ca = b ^ 2 + c ^ 2 - 2 * b * c * cc) :
    (1 / 3) * |a ^ 3 - d ^ 3| ≤ |b ^ 3 - c ^ 3| ∧
    |b ^ 3 - c ^ 3| ≤ 3 * |a ^ 3 - d ^ 3| ∧
    ((1 / 3) * |a ^ 3 - d ^ 3| = |b ^ 3 - c ^ 3| ∨
      |b ^ 3 - c ^ 3| = 3 * |a ^ 3 - d ^ 3| ↔ a = d ∧ b = c) := by
  have hk : |a - d| = |b - c| := by
    have h : a - d = b - c := by linarith [hpitot]
    rw [h]
  have hL := quad_left ha hb hc hd hBD hca2 hcc1
  have hR := quad_right ha hb hc hd hBD hca1 hcc2
  rw [abs_cube_sub_cube ha hd, abs_cube_sub_cube hb hc, hk]
  set k := |b - c| with hk_def
  set p := a ^ 2 + a * d + d ^ 2 with hp_def
  set q := b ^ 2 + b * c + c ^ 2 with hq_def
  have hk0 : 0 ≤ k := abs_nonneg _
  have hkite : k = 0 → a = d ∧ b = c := by
    intro hkz
    have hbc : b = c := by
      have h : b - c = 0 := by rwa [hk_def, abs_eq_zero] at hkz
      linarith
    have had : a = d := by
      have h : |a - d| = 0 := by rw [hk]; exact hkz
      rw [abs_eq_zero] at h
      linarith
    exact ⟨had, hbc⟩
  refine ⟨?_, ?_, ?_⟩
  · have h := mul_le_mul_of_nonneg_left hL hk0
    linarith
  · have h := mul_le_mul_of_nonneg_left hR hk0
    linarith
  · constructor
    · rintro (h | h)
      · by_cases hkz : k = 0
        · exact hkite hkz
        · have hkpos : 0 < k := lt_of_le_of_ne hk0 (Ne.symm hkz)
          have hne : a ≠ d := by
            intro had
            apply hkz
            rw [← hk, had, sub_self, abs_zero]
          have hstrict := quad_left_strict ha hb hc hd hBD hca2 hcc1 hne
          rw [← hp_def, ← hq_def] at hstrict
          have hmul := mul_lt_mul_of_pos_left hstrict hkpos
          linarith
      · by_cases hkz : k = 0
        · exact hkite hkz
        · have hkpos : 0 < k := lt_of_le_of_ne hk0 (Ne.symm hkz)
          have hne : b ≠ c := by
            intro hbc
            apply hkz
            rw [hk_def, hbc, sub_self, abs_zero]
          have hstrict := quad_right_strict ha hb hc hd hBD hca1 hcc2 hne
          rw [← hp_def, ← hq_def] at hstrict
          have hmul := mul_lt_mul_of_pos_left hstrict hkpos
          linarith
    · rintro ⟨had, hbc⟩
      subst had; subst hbc
      have hkz : k = 0 := by simp [hk_def]
      rw [hkz]
      simp

snip end

problem usa2004_p1
    (A B C D I P Q R S : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
    (_hr : 0 < r)
    (hP : P ∈ segment ℝ A B) (hQ : Q ∈ segment ℝ B C)
    (hR : R ∈ segment ℝ C D) (hS : S ∈ segment ℝ D A)
    (hIP : dist I P = r) (hIQ : dist I Q = r)
    (hIR : dist I R = r) (hIS : dist I S = r)
    (hperpP : ⟪I -ᵥ P, A -ᵥ B⟫_ℝ = 0) (hperpQ : ⟪I -ᵥ Q, B -ᵥ C⟫_ℝ = 0)
    (hperpR : ⟪I -ᵥ R, C -ᵥ D⟫_ℝ = 0) (hperpS : ⟪I -ᵥ S, D -ᵥ A⟫_ℝ = 0)
    (hA1 : Real.pi / 3 ≤ ∠ D A B) (hA2 : ∠ D A B ≤ 2 * Real.pi / 3)
    (_hB1 : Real.pi / 3 ≤ ∠ A B C) (_hB2 : ∠ A B C ≤ 2 * Real.pi / 3)
    (hC1 : Real.pi / 3 ≤ ∠ B C D) (hC2 : ∠ B C D ≤ 2 * Real.pi / 3)
    (_hD1 : Real.pi / 3 ≤ ∠ C D A) (_hD2 : ∠ C D A ≤ 2 * Real.pi / 3) :
    (1 / 3) * |dist A B ^ 3 - dist A D ^ 3| ≤ |dist B C ^ 3 - dist C D ^ 3| ∧
    |dist B C ^ 3 - dist C D ^ 3| ≤ 3 * |dist A B ^ 3 - dist A D ^ 3| ∧
    ((1 / 3) * |dist A B ^ 3 - dist A D ^ 3| = |dist B C ^ 3 - dist C D ^ 3| ∨
      |dist B C ^ 3 - dist C D ^ 3| = 3 * |dist A B ^ 3 - dist A D ^ 3| ↔
      dist A B = dist A D ∧ dist B C = dist C D) := by
  -- Equal tangent segments from each vertex.
  have hperpP' : ⟪I -ᵥ P, B -ᵥ A⟫_ℝ = 0 := inner_eq_zero_vsub_rev hperpP
  have hperpQ' : ⟪I -ᵥ Q, C -ᵥ B⟫_ℝ = 0 := inner_eq_zero_vsub_rev hperpQ
  have hperpR' : ⟪I -ᵥ R, D -ᵥ C⟫_ℝ = 0 := inner_eq_zero_vsub_rev hperpR
  have hperpS' : ⟪I -ᵥ S, A -ᵥ D⟫_ℝ = 0 := inner_eq_zero_vsub_rev hperpS
  have hP' : P ∈ segment ℝ B A := segment_symm ℝ A B ▸ hP
  have hQ' : Q ∈ segment ℝ C B := segment_symm ℝ B C ▸ hQ
  have hR' : R ∈ segment ℝ D C := segment_symm ℝ C D ▸ hR
  have hS' : S ∈ segment ℝ A D := segment_symm ℝ D A ▸ hS
  have hAS : dist A P = dist A S :=
    tangent_dist_eq hP hS' hperpP hperpS' (by rw [hIP, hIS])
  have hBQ : dist B P = dist B Q :=
    tangent_dist_eq hP' hQ hperpP' hperpQ (by rw [hIP, hIQ])
  have hCR : dist C Q = dist C R :=
    tangent_dist_eq hQ' hR hperpQ' hperpR (by rw [hIQ, hIR])
  have hDS : dist D R = dist D S :=
    tangent_dist_eq hR' hS hperpR' hperpS (by rw [hIR, hIS])
  -- Splitting the sides at the tangency points.
  have hsegP : dist A P + dist P B = dist A B := (mem_segment_iff_wbtw.mp hP).dist_add_dist
  have hsegQ : dist B Q + dist Q C = dist B C := (mem_segment_iff_wbtw.mp hQ).dist_add_dist
  have hsegR : dist C R + dist R D = dist C D := (mem_segment_iff_wbtw.mp hR).dist_add_dist
  have hsegS : dist D S + dist S A = dist D A := (mem_segment_iff_wbtw.mp hS).dist_add_dist
  -- Pitot's theorem: the sums of opposite sides are equal.
  have hpitot : dist A B + dist C D = dist B C + dist A D := by
    have c1 : dist P B = dist B P := dist_comm P B
    have c2 : dist Q C = dist C Q := dist_comm Q C
    have c3 : dist R D = dist D R := dist_comm R D
    have c4 : dist S A = dist A S := dist_comm S A
    have c5 : dist D A = dist A D := dist_comm D A
    linarith [hsegP, hsegQ, hsegR, hsegS, hAS, hBQ, hCR, hDS]
  -- The law of cosines applied to the diagonal `BD`, from both sides.
  have hBD1 := EuclideanGeometry.law_cos B A D
  have hBD2 := EuclideanGeometry.law_cos B C D
  rw [EuclideanGeometry.angle_comm B A D] at hBD1
  have hBD : dist A B ^ 2 + dist A D ^ 2 - 2 * dist A B * dist A D * Real.cos (∠ D A B)
      = dist B C ^ 2 + dist C D ^ 2 - 2 * dist B C * dist C D * Real.cos (∠ B C D) := by
    rw [dist_comm B A, dist_comm D A] at hBD1
    rw [dist_comm D C] at hBD2
    linarith [hBD1, hBD2]
  -- Cosine bounds from the angle hypotheses.
  have hA0 : 0 ≤ ∠ D A B := EuclideanGeometry.angle_nonneg _ _ _
  have hAπ : ∠ D A B ≤ Real.pi := EuclideanGeometry.angle_le_pi _ _ _
  have hC0 : 0 ≤ ∠ B C D := EuclideanGeometry.angle_nonneg _ _ _
  have hCπ : ∠ B C D ≤ Real.pi := EuclideanGeometry.angle_le_pi _ _ _
  have h3nonneg : (0 : ℝ) ≤ Real.pi / 3 := by positivity
  have h3lepi : Real.pi / 3 ≤ Real.pi := by linarith [Real.pi_pos]
  have h23nonneg : (0 : ℝ) ≤ 2 * Real.pi / 3 := by positivity
  have h23lepi : 2 * Real.pi / 3 ≤ Real.pi := by linarith [Real.pi_pos]
  have hcos23 : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
    have h : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
    rw [h, Real.cos_pi_sub, Real.cos_pi_div_three]
    ring
  have hca2 : Real.cos (∠ D A B) ≤ 1 / 2 := by
    rw [← Real.cos_pi_div_three]
    exact Real.antitoneOn_cos ⟨h3nonneg, h3lepi⟩ ⟨hA0, hAπ⟩ hA1
  have hca1 : -1 / 2 ≤ Real.cos (∠ D A B) := by
    rw [← hcos23]
    exact Real.antitoneOn_cos ⟨hA0, hAπ⟩ ⟨h23nonneg, h23lepi⟩ hA2
  have hcc2 : Real.cos (∠ B C D) ≤ 1 / 2 := by
    rw [← Real.cos_pi_div_three]
    exact Real.antitoneOn_cos ⟨h3nonneg, h3lepi⟩ ⟨hC0, hCπ⟩ hC1
  have hcc1 : -1 / 2 ≤ Real.cos (∠ B C D) := by
    rw [← hcos23]
    exact Real.antitoneOn_cos ⟨hC0, hCπ⟩ ⟨h23nonneg, h23lepi⟩ hC2
  exact usa2004_p1_algebra (dist_nonneg (x := A) (y := B)) (dist_nonneg (x := B) (y := C))
    (dist_nonneg (x := C) (y := D)) (dist_nonneg (x := A) (y := D))
    hpitot hca1 hca2 hcc1 hcc2 hBD

end Usa2004P1
