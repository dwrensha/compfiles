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
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import Mathlib.Geometry.Euclidean.Sphere.Basic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# USA Mathematical Olympiad 2009, Problem 5

Trapezoid ABCD, with AB ∥ CD, is inscribed in circle ω and point G lies inside
triangle BCD. Rays AG and BG meet ω again at points P and Q, respectively.
Let the line through G parallel to AB intersect BD and BC at points R and S,
respectively. Prove that quadrilateral PQRS is cyclic if and only if BG bisects
∠CBD.
-/

namespace Usa2009P5

open scoped EuclideanGeometry InnerProductSpace

snip begin

abbrev Point := EuclideanSpace ℝ (Fin 2)

/-- A point of the plane given by its coordinates. -/
def pt (x y : ℝ) : Point := !₂[x, y]

/-- The vertices of the trapezoid. A trapezoid inscribed in a circle is necessarily
isosceles, so after a translation, rotation, reflection and scaling we may assume that
the circumcircle is centered at the origin, that `AB` and `CD` are horizontal with
`A = (-u, v)`, `B = (u, v)`, `C = (w, -z)`, `D = (-w, -z)`, with `0 < u`, `0 < w` and
`0 < v + z` (so `AB` lies strictly above `CD`). -/
def A (u v : ℝ) : Point := pt (-u) v

/-- See `A`. -/
def B (u v : ℝ) : Point := pt u v

/-- See `A`. -/
def C (w z : ℝ) : Point := pt w (-z)

/-- See `A`. -/
def D (w z : ℝ) : Point := pt (-w) (-z)

lemma inner_coord (X Y : Point) : ⟪X, Y⟫_ℝ = X 0 * Y 0 + X 1 * Y 1 := by
  rw [PiLp.inner_apply]
  simp [Fin.sum_univ_two]
  ring

lemma coord_of_eq {X Y : Point} (h : X = Y) (i : Fin 2) : X i = Y i :=
  congrFun (congrArg WithLp.ofLp h) i

lemma dist_coord (X Y : Point) :
    dist X Y = Real.sqrt ((X 0 - Y 0) ^ 2 + (X 1 - Y 1) ^ 2) := by
  rw [dist_eq_norm, EuclideanSpace.norm_eq]
  simp [PiLp.sub_apply, Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]

/-- The cosine form of the angle bisector condition: under the sign (i.e. "inside the
angle") hypothesis `hpos`, the equality of the unoriented angles `∠(a,b)` and `∠(b,c)`
is equivalent to the polynomial (squared) condition, which is what the algebraic
computation produces. -/
lemma angle_bisector_iff {a b c : Point} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hpos : 0 < ⟪a, b⟫_ℝ * ‖c‖ + ⟪c, b⟫_ℝ * ‖a‖) :
    InnerProductGeometry.angle a b = InnerProductGeometry.angle b c ↔
      ⟪a, b⟫_ℝ ^ 2 * ⟪c, c⟫_ℝ = ⟪c, b⟫_ℝ ^ 2 * ⟪a, a⟫_ℝ := by
  have hna : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
  have hnb : ‖b‖ ≠ 0 := norm_ne_zero_iff.mpr hb
  have hnc : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  have hmem1 : ⟪a, b⟫_ℝ / (‖a‖ * ‖b‖) ∈ Set.Icc (-1) 1 := by
    rw [Set.mem_Icc, ← abs_le]
    exact abs_real_inner_div_norm_mul_norm_le_one a b
  have hmem2 : ⟪b, c⟫_ℝ / (‖b‖ * ‖c‖) ∈ Set.Icc (-1) 1 := by
    rw [Set.mem_Icc, ← abs_le]
    exact abs_real_inner_div_norm_mul_norm_le_one b c
  have hbc : ⟪b, c⟫_ℝ = ⟪c, b⟫_ℝ := real_inner_comm c b
  unfold InnerProductGeometry.angle
  constructor
  · intro h
    have h2 : ⟪a, b⟫_ℝ / (‖a‖ * ‖b‖) = ⟪b, c⟫_ℝ / (‖b‖ * ‖c‖) :=
      Real.arccos_injOn hmem1 hmem2 h
    rw [hbc] at h2
    have h3 : ⟪a, b⟫_ℝ * ‖c‖ = ⟪c, b⟫_ℝ * ‖a‖ := by
      field_simp [hna, hnb, hnc] at h2
      linear_combination h2
    have h4 : (⟪a, b⟫_ℝ * ‖c‖) ^ 2 = (⟪c, b⟫_ℝ * ‖a‖) ^ 2 := by rw [h3]
    have hca : ⟪a, a⟫_ℝ = ‖a‖ ^ 2 := real_inner_self_eq_norm_sq a
    have hcc : ⟪c, c⟫_ℝ = ‖c‖ ^ 2 := real_inner_self_eq_norm_sq c
    rw [hca, hcc]
    linear_combination h4
  · intro h
    have hca : ⟪a, a⟫_ℝ = ‖a‖ ^ 2 := real_inner_self_eq_norm_sq a
    have hcc : ⟪c, c⟫_ℝ = ‖c‖ ^ 2 := real_inner_self_eq_norm_sq c
    rw [hca, hcc] at h
    have h2 : (⟪a, b⟫_ℝ * ‖c‖) ^ 2 = (⟪c, b⟫_ℝ * ‖a‖) ^ 2 := by linear_combination h
    have h3 : ⟪a, b⟫_ℝ * ‖c‖ = ⟪c, b⟫_ℝ * ‖a‖ := by
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp h2 with h' | h'
      · exact h'
      · exfalso
        nlinarith only [hpos, h']
    have h4 : ⟪a, b⟫_ℝ / (‖a‖ * ‖b‖) = ⟪b, c⟫_ℝ / (‖b‖ * ‖c‖) := by
      rw [hbc]
      field_simp [hna, hnb, hnc]
      linear_combination h3
    rw [h4]

/-- The sign condition needed by `angle_bisector_iff`: a point `b` strictly between
the two sides of a nondegenerate angle (expressed barycentrically as `b = γ • a + δ • c`
with `0 < γ, δ`) lies on the same side, so that the sum of the two projections is
strictly positive. -/
lemma inner_sign_pos {a b c : Point} (γ δ : ℝ) (hγ : 0 < γ) (hδ : 0 < δ)
    (hb : b = γ • a + δ • c) (ha : a ≠ 0) (hc : c ≠ 0)
    (hcross : a 0 * c 1 - a 1 * c 0 ≠ 0) :
    0 < ⟪a, b⟫_ℝ * ‖c‖ + ⟪c, b⟫_ℝ * ‖a‖ := by
  have hna : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hnc : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hab : ⟪a, b⟫_ℝ = γ * ⟪a, a⟫_ℝ + δ * ⟪a, c⟫_ℝ := by
    rw [hb, inner_add_right, real_inner_smul_right, real_inner_smul_right]
  have hcb : ⟪c, b⟫_ℝ = γ * ⟪a, c⟫_ℝ + δ * ⟪c, c⟫_ℝ := by
    rw [hb, inner_add_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_comm c a]
  have hkey : ⟪a, b⟫_ℝ * ‖c‖ + ⟪c, b⟫_ℝ * ‖a‖
      = (γ * ‖a‖ + δ * ‖c‖) * (‖a‖ * ‖c‖ + ⟪a, c⟫_ℝ) := by
    rw [hab, hcb, real_inner_self_eq_norm_sq a, real_inner_self_eq_norm_sq c]
    ring
  rw [hkey]
  apply mul_pos
  · nlinarith only [mul_pos hγ hna, mul_pos hδ hnc]
  · have hcs : (‖a‖ * ‖c‖) ^ 2 = ⟪a, c⟫_ℝ ^ 2 + (a 0 * c 1 - a 1 * c 0) ^ 2 := by
      have e1 : (‖a‖ * ‖c‖) ^ 2 = ‖a‖ ^ 2 * ‖c‖ ^ 2 := by ring
      rw [e1, ← real_inner_self_eq_norm_sq a, ← real_inner_self_eq_norm_sq c,
        inner_coord, inner_coord, inner_coord]
      ring
    have hcross2 : 0 < (a 0 * c 1 - a 1 * c 0) ^ 2 := sq_pos_of_ne_zero hcross
    have habs : |⟪a, c⟫_ℝ| < ‖a‖ * ‖c‖ := by
      have h1 : ⟪a, c⟫_ℝ ^ 2 < (‖a‖ * ‖c‖) ^ 2 := by nlinarith only [hcs, hcross2]
      have h2 : (0 : ℝ) ≤ ‖a‖ * ‖c‖ := mul_nonneg hna.le hnc.le
      rw [sq_lt_sq] at h1
      rwa [abs_of_nonneg h2] at h1
    have h3 : -(‖a‖ * ‖c‖) < ⟪a, c⟫_ℝ := (abs_lt.mp habs).1
    linarith only [h3]

/-!
### The algebraic setup

We write `G = (u + x, v + y)` (so that `x, y` are the coordinates of `G - B`).
All the points `P, Q, R, S` have coordinates that are rational functions of
`u, v, w, z, x, y`; the following definitions are the numerators of those rational
functions, with `denP, denQ` the corresponding denominators.
-/

/-- `= |G - A|²`, the denominator appearing in the formula for `P`. -/
def denP (u x y : ℝ) : ℝ := (x + 2 * u) ^ 2 + y ^ 2

/-- `= |G - B|²`, the denominator appearing in the formula for `Q`. -/
def denQ (x y : ℝ) : ℝ := x ^ 2 + y ^ 2

/-- Numerator of the parameter of `P` on the ray `AG`. -/
def tPn (u v x y : ℝ) : ℝ := 2 * (2 * u ^ 2 + u * x - v * y)

/-- Numerator of the parameter of `Q` on the ray `BG`. -/
def tQn (u v x y : ℝ) : ℝ := -2 * (u * x + v * y)

/-- Numerator of the first coordinate of `P`. -/
def P1n (u v x y : ℝ) : ℝ := -u * denP u x y + tPn u v x y * (x + 2 * u)

/-- Numerator of the second coordinate of `P`. -/
def P2n (u v x y : ℝ) : ℝ := v * denP u x y + tPn u v x y * y

/-- Numerator of the first coordinate of `Q`. -/
def Q1n (u v x y : ℝ) : ℝ := u * (y ^ 2 - x ^ 2) - 2 * v * x * y

/-- Numerator of the second coordinate of `Q`. -/
def Q2n (u v x y : ℝ) : ℝ := v * (x ^ 2 - y ^ 2) - 2 * u * x * y

/-- Numerator of the first coordinate of `R`. -/
def R1n (u v w z y : ℝ) : ℝ := u * (v + z) + y * (u + w)

/-- Numerator of the first coordinate of `S`. -/
def S1n (u v w z y : ℝ) : ℝ := u * (v + z) + y * (u - w)

/-- Numerator of the first coordinate of the midpoint of `RS`. -/
def mn (u v z y : ℝ) : ℝ := u * (v + z + y)

/-- Numerator of `(sq Q - sq R - 2 m (Q₀ - R₀))`. -/
def A1n (u v w z x y : ℝ) : ℝ :=
  (Q1n u v x y ^ 2 + Q2n u v x y ^ 2) * (v + z) ^ 2
    - (R1n u v w z y ^ 2 + (v + y) ^ 2 * (v + z) ^ 2) * (denQ x y) ^ 2
    - 2 * (mn u v z y) * (Q1n u v x y * (v + z) - R1n u v w z y * denQ x y) * (denQ x y)

/-- Numerator of `(sq P - sq R - 2 m (P₀ - R₀))`. -/
def A2n (u v w z x y : ℝ) : ℝ :=
  (P1n u v x y ^ 2 + P2n u v x y ^ 2) * (v + z) ^ 2
    - (R1n u v w z y ^ 2 + (v + y) ^ 2 * (v + z) ^ 2) * (denP u x y) ^ 2
    - 2 * (mn u v z y) * (P1n u v x y * (v + z) - R1n u v w z y * denP u x y) * (denP u x y)

/-- Numerator of `P₁ - G₁`. -/
def P2m (u v x y : ℝ) : ℝ := -y * denP u x y + tPn u v x y * y

/-- Numerator of `Q₁ - G₁`. -/
def Q2m (u v x y : ℝ) : ℝ := -y * denQ x y + tQn u v x y * y

/-- The polynomial whose vanishing is equivalent to `P Q R S` being concyclic. -/
def polyN (u v w z x y : ℝ) : ℝ :=
  A1n u v w z x y * P2m u v x y * denP u x y - A2n u v w z x y * Q2m u v x y * denQ x y

/-- The polynomial whose vanishing is equivalent to `BG` bisecting `∠CBD`. -/
def polyH (u v w z x y : ℝ) : ℝ :=
  ((w - u) * x - (z + v) * y) ^ 2 * ((w + u) ^ 2 + (z + v) ^ 2)
    - (-(w + u) * x - (z + v) * y) ^ 2 * ((w - u) ^ 2 + (z + v) ^ 2)

/-- `= ρ² - |G|²`, positive because `G` lies strictly inside the circumcircle. -/
def gRad (u v x y : ℝ) : ℝ := u ^ 2 + v ^ 2 - (u + x) ^ 2 - (v + y) ^ 2

/-- The master identity, relating the cyclic condition `polyN` and the bisector
condition `polyH`, modulo the circle hypothesis `u² + v² = w² + z²`.  Found and
verified by computer algebra; all the factors of the correction term are nonnegative
or strictly positive under the problem's hypotheses. -/
lemma master (u v w z x y : ℝ) :
    w * (v + z) * polyN u v w z x y
      = u * (-y) * (v + y + z) * gRad u v x y * polyH u v w z x y * denP u x y * denQ x y
        + 4 * u * w * y ^ 2 * (v + z) * denP u x y * denQ x y * gRad u v x y
          * (x * (v + z) - u * y) * (u ^ 2 + v ^ 2 - w ^ 2 - z ^ 2) := by
  simp only [polyN, A1n, A2n, P2m, Q2m, P1n, P2n, Q1n, Q2n, R1n, mn, denP, denQ,
    tPn, tQn, polyH, gRad]
  ring

/-- The cleared concyclicity equation: the determinant condition for `P Q R S` to be
concyclic, multiplied by the (nonzero) denominators, is exactly `polyN`.  The proof is
a staged `linear_combination`, so no denominators appear. -/
lemma e1_cleared (u v w z x y m P0 P1 Q0 Q1 R0 R1 : ℝ)
    (hP0 : P0 * denP u x y = P1n u v x y) (hP1 : P1 * denP u x y = P2n u v x y)
    (hQ0 : Q0 * denQ x y = Q1n u v x y) (hQ1 : Q1 * denQ x y = Q2n u v x y)
    (hR0 : R0 * (v + z) = R1n u v w z y) (hR1 : R1 = v + y)
    (hm : m * (v + z) = mn u v z y) :
    (((Q0 ^ 2 + Q1 ^ 2) - (R0 ^ 2 + R1 ^ 2) - 2 * m * (Q0 - R0)) * (P1 - (v + y))
        - ((P0 ^ 2 + P1 ^ 2) - (R0 ^ 2 + R1 ^ 2) - 2 * m * (P0 - R0)) * (Q1 - (v + y)))
      * ((denP u x y) ^ 2 * (denQ x y) ^ 2 * (v + z) ^ 2)
    = polyN u v w z x y := by
  have s1 : (Q0 ^ 2 + Q1 ^ 2) * (denQ x y) ^ 2 = Q1n u v x y ^ 2 + Q2n u v x y ^ 2 := by
    linear_combination hQ0 * (Q0 * denQ x y + Q1n u v x y)
      + hQ1 * (Q1 * denQ x y + Q2n u v x y)
  have s2 : (R0 ^ 2 + R1 ^ 2) * (v + z) ^ 2 = R1n u v w z y ^ 2 + (v + y) ^ 2 * (v + z) ^ 2 := by
    rw [hR1]
    linear_combination hR0 * (R0 * (v + z) + R1n u v w z y)
  have s3 : 2 * m * (Q0 - R0) * (denQ x y) * (v + z) ^ 2
      = 2 * (mn u v z y) * (Q1n u v x y * (v + z) - R1n u v w z y * denQ x y) := by
    linear_combination (2 * (Q0 - R0) * denQ x y * (v + z)) * hm
      + (2 * (mn u v z y) * (v + z)) * hQ0 - (2 * (mn u v z y) * denQ x y) * hR0
  have s1' : (P0 ^ 2 + P1 ^ 2) * (denP u x y) ^ 2 = P1n u v x y ^ 2 + P2n u v x y ^ 2 := by
    linear_combination hP0 * (P0 * denP u x y + P1n u v x y)
      + hP1 * (P1 * denP u x y + P2n u v x y)
  have s3' : 2 * m * (P0 - R0) * (denP u x y) * (v + z) ^ 2
      = 2 * (mn u v z y) * (P1n u v x y * (v + z) - R1n u v w z y * denP u x y) := by
    linear_combination (2 * (P0 - R0) * denP u x y * (v + z)) * hm
      + (2 * (mn u v z y) * (v + z)) * hP0 - (2 * (mn u v z y) * denP u x y) * hR0
  have eA1 : ((Q0 ^ 2 + Q1 ^ 2) - (R0 ^ 2 + R1 ^ 2) - 2 * m * (Q0 - R0))
      * ((denQ x y) ^ 2 * (v + z) ^ 2) = A1n u v w z x y := by
    simp only [A1n]
    linear_combination s1 * (v + z) ^ 2 - s2 * (denQ x y) ^ 2 - s3 * denQ x y
  have eA2 : ((P0 ^ 2 + P1 ^ 2) - (R0 ^ 2 + R1 ^ 2) - 2 * m * (P0 - R0))
      * ((denP u x y) ^ 2 * (v + z) ^ 2) = A2n u v w z x y := by
    simp only [A2n]
    linear_combination s1' * (v + z) ^ 2 - s2 * (denP u x y) ^ 2 - s3' * denP u x y
  have eP1m : (P1 - (v + y)) * denP u x y = P2m u v x y := by
    simp only [P2m, P2n] at hP1 ⊢
    linear_combination hP1
  have eQ1m : (Q1 - (v + y)) * denQ x y = Q2m u v x y := by
    simp only [Q2m, Q2n, tQn, denQ] at hQ1 ⊢
    linear_combination hQ1
  simp only [polyN]
  linear_combination eA1 * (((P1 - (v + y)) * denP u x y) * denP u x y)
    + eP1m * (A1n u v w z x y * denP u x y)
    - eA2 * (((Q1 - (v + y)) * denQ x y) * denQ x y)
    - eQ1m * (A2n u v w z x y * denQ x y)

snip end

problem usa2009_p5
    (u v w z : ℝ) (hu : 0 < u) (hw : 0 < w) (hvz : 0 < v + z)
    (hcirc : u ^ 2 + v ^ 2 = w ^ 2 + z ^ 2)
    (G P Q R S : Point)
    (hG : ∃ γ δ : ℝ, 0 < γ ∧ 0 < δ ∧ γ + δ < 1 ∧
      G = B u v + γ • (C w z - B u v) + δ • (D w z - B u v))
    (hP : P ≠ A u v ∧ (P 0) ^ 2 + (P 1) ^ 2 = u ^ 2 + v ^ 2 ∧
      ∃ t : ℝ, 0 ≤ t ∧ P = A u v + t • (G - A u v))
    (hQ : Q ≠ B u v ∧ (Q 0) ^ 2 + (Q 1) ^ 2 = u ^ 2 + v ^ 2 ∧
      ∃ t : ℝ, 0 ≤ t ∧ Q = B u v + t • (G - B u v))
    (hR : (∃ s : ℝ, R = B u v + s • (D w z - B u v)) ∧
      (G - R) 0 * (B u v - A u v) 1 = (G - R) 1 * (B u v - A u v) 0)
    (hS : (∃ s : ℝ, S = B u v + s • (C w z - B u v)) ∧
      (G - S) 0 * (B u v - A u v) 1 = (G - S) 1 * (B u v - A u v) 0) :
    EuclideanGeometry.Concyclic {P, Q, R, S} ↔
      InnerProductGeometry.angle (C w z - B u v) (G - B u v) =
        InnerProductGeometry.angle (G - B u v) (D w z - B u v) := by
  -- Unpack the hypotheses.
  obtain ⟨γ, δ, hγ, hδ, hγδ, hGeq⟩ := hG
  obtain ⟨hPA, hPcirc, t, _ht0, hPt⟩ := hP
  obtain ⟨hQB, hQcirc, t', _ht'0, hQt⟩ := hQ
  obtain ⟨⟨sr, hRs⟩, hRpar⟩ := hR
  obtain ⟨⟨ss, hSs⟩, hSpar⟩ := hS
  -- Coordinates of `G`.
  have hG0 : G 0 = u + γ * (w - u) + δ * (-w - u) := by
    have h := coord_of_eq hGeq 0
    simp only [B, C, D, pt, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero] at h
    linarith only [h]
  have hG1 : G 1 = v + (γ + δ) * (-z - v) := by
    have h := coord_of_eq hGeq 1
    simp only [B, C, D, pt, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one] at h
    linarith only [h]
  -- The relative coordinates `x, y` of `G - B`.
  set x := G 0 - u with hx
  set y := G 1 - v with hy
  have hG0x : G 0 = u + x := by linarith only [hx]
  have hG1y : G 1 = v + y := by linarith only [hy]
  have hxv : x = γ * (w - u) - δ * (w + u) := by linarith only [hG0, hx]
  have hyv : y = -(γ + δ) * (z + v) := by linarith only [hG1, hy]
  have hγδ' : 0 < γ + δ := by linarith only [hγ, hδ]
  have hyneg : y < 0 := by linarith only [hyv, mul_pos hγδ' hvz]
  have h1γδ : (0 : ℝ) < 1 - γ - δ := by linarith only [hγδ]
  have hybound : (γ + δ) * (v + z) < v + z := by
    have hlt := mul_lt_mul_of_pos_right hγδ hvz
    linarith only [hlt]
  have hg2z : 0 < v + y + z := by linarith only [hyv, hybound]
  -- Nondegeneracy of the denominators.
  have hdenQ : 0 < denQ x y := by
    simp only [denQ]
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero (ne_of_lt hyneg))
  have hdenP : 0 < denP u x y := by
    simp only [denP]
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero (ne_of_lt hyneg))
  -- `G` lies strictly inside the circumcircle.
  have hGr : 0 < gRad u v x y := by
    have hCB2 : (0 : ℝ) < (w - u) ^ 2 + (z + v) ^ 2 :=
      add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero (by linarith only [hvz]))
    have hDB2 : (0 : ℝ) < (w + u) ^ 2 + (z + v) ^ 2 :=
      add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero (by linarith only [hvz]))
    have e : gRad u v x y = (1 - γ - δ) * γ * ((w - u) ^ 2 + (z + v) ^ 2)
        + (1 - γ - δ) * δ * ((w + u) ^ 2 + (z + v) ^ 2) + 4 * γ * δ * w ^ 2 := by
      simp only [gRad]
      rw [hxv, hyv]
      linear_combination (γ + δ) * hcirc
    rw [e]
    have t1 : (0 : ℝ) < (1 - γ - δ) * γ * ((w - u) ^ 2 + (z + v) ^ 2) :=
      mul_pos (mul_pos h1γδ hγ) hCB2
    have t2 : (0 : ℝ) < (1 - γ - δ) * δ * ((w + u) ^ 2 + (z + v) ^ 2) :=
      mul_pos (mul_pos h1γδ hδ) hDB2
    have t3 : (0 : ℝ) < 4 * γ * δ * w ^ 2 :=
      mul_pos (mul_pos (mul_pos (by norm_num) hγ) hδ) (sq_pos_of_ne_zero (ne_of_gt hw))
    exact add_pos (add_pos t1 t2) t3
  -- The ray parameter and coordinates of `P`.
  have hPt0 : P 0 = -u + t * (x + 2 * u) := by
    have h := coord_of_eq hPt 0
    simp only [A, pt, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, hG0x] at h
    linarith only [h]
  have hPt1 : P 1 = v + t * y := by
    have h := coord_of_eq hPt 1
    simp only [A, pt, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, hG1y] at h
    linarith only [h]
  have htne : t ≠ 0 := by
    intro ht0
    rw [ht0] at hPt
    simp at hPt
    exact hPA hPt
  have hquad : t * (t * denP u x y + (2 * v * y - 2 * u * (x + 2 * u))) = 0 := by
    have hc := hPcirc
    rw [hPt0, hPt1] at hc
    simp only [denP]
    linear_combination hc
  have htP : t * denP u x y = 2 * (2 * u ^ 2 + u * x - v * y) := by
    have h := (mul_eq_zero.mp hquad).resolve_left htne
    simp only [denP] at h ⊢
    linarith only [h]
  have hP0f : P 0 * denP u x y = P1n u v x y := by
    simp only [P1n, tPn]
    rw [hPt0]
    linear_combination htP * (x + 2 * u)
  have hP1f : P 1 * denP u x y = P2n u v x y := by
    simp only [P2n, tPn]
    rw [hPt1]
    linear_combination htP * y
  -- The ray parameter and coordinates of `Q`.
  have hQt0 : Q 0 = u + t' * x := by
    have h := coord_of_eq hQt 0
    simp only [B, pt, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, hG0x] at h
    linarith only [h]
  have hQt1 : Q 1 = v + t' * y := by
    have h := coord_of_eq hQt 1
    simp only [B, pt, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, hG1y] at h
    linarith only [h]
  have ht'ne : t' ≠ 0 := by
    intro ht0
    rw [ht0] at hQt
    simp at hQt
    exact hQB hQt
  have hquad' : t' * (t' * denQ x y + 2 * (u * x + v * y)) = 0 := by
    have hc := hQcirc
    rw [hQt0, hQt1] at hc
    simp only [denQ]
    linear_combination hc
  have htQ : t' * denQ x y = -2 * (u * x + v * y) := by
    have h := (mul_eq_zero.mp hquad').resolve_left ht'ne
    simp only [denQ] at h ⊢
    linarith only [h]
  have hQ0f : Q 0 * denQ x y = Q1n u v x y := by
    simp only [Q1n, denQ] at ⊢
    simp only [denQ] at htQ
    rw [hQt0]
    linear_combination htQ * x
  have hQ1f : Q 1 * denQ x y = Q2n u v x y := by
    simp only [Q2n, denQ] at ⊢
    simp only [denQ] at htQ
    rw [hQt1]
    linear_combination htQ * y
  -- Coordinates of `R`.
  have hR0eq : R 0 = u + sr * (-w - u) := by
    have h := coord_of_eq hRs 0
    simp only [B, D, pt, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero] at h
    linarith only [h]
  have hR1eq : R 1 = v + sr * (-z - v) := by
    have h := coord_of_eq hRs 1
    simp only [B, D, pt, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one] at h
    linarith only [h]
  have hR1 : R 1 = v + y := by
    have h := hRpar
    simp only [A, B, pt, PiLp.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h
    rw [show v - v = (0 : ℝ) by ring, show u - -u = 2 * u by ring, mul_zero] at h
    have h3 : G 1 - R 1 = 0 :=
      (mul_eq_zero.mp h.symm).resolve_right (mul_ne_zero two_ne_zero (ne_of_gt hu))
    linarith only [h3, hG1y]
  have hsr : sr * (v + z) = -y := by linarith only [hR1, hR1eq]
  have hR0f : R 0 * (v + z) = R1n u v w z y := by
    simp only [R1n]
    rw [hR0eq]
    linear_combination hsr * (-(w + u))
  -- Coordinates of `S`.
  have hS0eq : S 0 = u + ss * (w - u) := by
    have h := coord_of_eq hSs 0
    simp only [B, C, pt, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero] at h
    linarith only [h]
  have hS1eq : S 1 = v + ss * (-z - v) := by
    have h := coord_of_eq hSs 1
    simp only [B, C, pt, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one] at h
    linarith only [h]
  have hS1 : S 1 = v + y := by
    have h := hSpar
    simp only [A, B, pt, PiLp.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h
    rw [show v - v = (0 : ℝ) by ring, show u - -u = 2 * u by ring, mul_zero] at h
    have h3 : G 1 - S 1 = 0 :=
      (mul_eq_zero.mp h.symm).resolve_right (mul_ne_zero two_ne_zero (ne_of_gt hu))
    linarith only [h3, hG1y]
  have hss : ss * (v + z) = -y := by linarith only [hS1, hS1eq]
  have hS0f : S 0 * (v + z) = S1n u v w z y := by
    simp only [S1n]
    rw [hS0eq]
    linear_combination hss * (w - u)
  -- The midpoint `m` of `RS`, `R ≢ S`, and `P` lies strictly below the line `RS`.
  set m := u * (v + z + y) / (v + z) with hm_def
  have hm : m * (v + z) = mn u v z y := by
    rw [hm_def]
    simp only [mn]
    exact div_mul_cancel₀ _ (ne_of_gt hvz)
  have h2m : S 0 + R 0 = 2 * m := by
    have h1 : (S 0 + R 0) * (v + z) = (2 * m) * (v + z) := by
      have e1 := hS0f
      have e2 := hR0f
      have e3 := hm
      simp only [S1n, R1n, mn] at e1 e2 e3
      linear_combination e1 + e2 - 2 * e3
    exact mul_right_cancel₀ (ne_of_gt hvz) h1
  have hSR : R 0 < S 0 := by
    have e1 := hS0f
    have e2 := hR0f
    simp only [S1n, R1n] at e1 e2
    have h2yw : (0 : ℝ) < -2 * y * w := by
      have h' := mul_pos (mul_pos two_pos (neg_pos.mpr hyneg)) hw
      linarith only [h']
    have e3 : (S 0 - R 0) * (v + z) = -2 * y * w := by linear_combination e1 - e2
    have h1 : 0 < (S 0 - R 0) * (v + z) := by rw [e3]; exact h2yw
    exact sub_pos.mp ((mul_pos_iff_of_pos_right hvz).mp h1)
  have hP1ne : P 1 - (v + y) ≠ 0 := by
    have e1 : (P 1 - (v + y)) * denP u x y = y * gRad u v x y := by
      have e2 : tPn u v x y - denP u x y = gRad u v x y := by
        simp only [tPn, denP, gRad]
        ring
      simp only [P2n] at hP1f
      linear_combination hP1f + y * e2
    have h2 : (P 1 - (v + y)) * denP u x y < 0 := by
      rw [e1]
      exact mul_neg_of_neg_of_pos hyneg hGr
    have h3 : P 1 - (v + y) < 0 := by nlinarith only [h2, hdenP]
    exact ne_of_lt h3
  -- The equivalence of `polyN = 0` and `polyH = 0`, via the master identity.
  have hNH : polyN u v w z x y = 0 ↔ polyH u v w z x y = 0 := by
    have hmast := master u v w z x y
    have hh : (u ^ 2 + v ^ 2 - w ^ 2 - z ^ 2) = 0 := by linarith only [hcirc]
    rw [hh, mul_zero, add_zero] at hmast
    constructor
    · intro hN
      rw [hN, mul_zero] at hmast
      have hne : u * (-y) * (v + y + z) * gRad u v x y * denP u x y * denQ x y ≠ 0 :=
        mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (ne_of_gt hu)
          (neg_ne_zero.mpr (ne_of_lt hyneg))) (ne_of_gt hg2z)) (ne_of_gt hGr))
          (ne_of_gt hdenP)) (ne_of_gt hdenQ)
      have h0 : (u * (-y) * (v + y + z) * gRad u v x y * denP u x y * denQ x y)
          * polyH u v w z x y = 0 := by
        rw [show (u * (-y) * (v + y + z) * gRad u v x y * denP u x y * denQ x y)
            * polyH u v w z x y
            = u * (-y) * (v + y + z) * gRad u v x y * polyH u v w z x y * denP u x y
              * denQ x y from by ring]
        exact hmast.symm
      exact (mul_eq_zero.mp h0).resolve_left hne
    · intro hH
      rw [hH] at hmast
      have h0 : w * (v + z) * polyN u v w z x y = 0 := by
        rw [hmast]
        ring
      exact (mul_eq_zero.mp h0).resolve_left (mul_ne_zero (ne_of_gt hw) (ne_of_gt hvz))
  -- The angle bisector condition, via the sign lemma and the bridge lemma.
  have hb : G - B u v = γ • (C w z - B u v) + δ • (D w z - B u v) := by
    rw [hGeq]
    abel
  have ha : C w z - B u v ≠ 0 := by
    intro hz
    have h := coord_of_eq hz 1
    simp only [C, B, pt, PiLp.sub_apply, PiLp.zero_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one] at h
    linarith only [hvz, h]
  have hc : D w z - B u v ≠ 0 := by
    intro hz
    have h := coord_of_eq hz 1
    simp only [D, B, pt, PiLp.sub_apply, PiLp.zero_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one] at h
    linarith only [hvz, h]
  have hb' : G - B u v ≠ 0 := by
    intro hz
    have h := coord_of_eq hz 1
    simp only [B, pt, PiLp.sub_apply, PiLp.zero_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one] at h
    linarith only [hyneg, hG1y, h]
  have hcross : (C w z - B u v) 0 * (D w z - B u v) 1 - (C w z - B u v) 1 * (D w z - B u v) 0
      ≠ 0 := by
    have e : (C w z - B u v) 0 * (D w z - B u v) 1 - (C w z - B u v) 1 * (D w z - B u v) 0
        = -(2 * w * (v + z)) := by
      simp only [C, D, B, pt, PiLp.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
      ring
    rw [e]
    exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero two_ne_zero (ne_of_gt hw))
      (ne_of_gt hvz))
  have hsign : 0 < ⟪C w z - B u v, G - B u v⟫_ℝ * ‖D w z - B u v‖
      + ⟪D w z - B u v, G - B u v⟫_ℝ * ‖C w z - B u v‖ :=
    inner_sign_pos γ δ hγ hδ hb ha hc hcross
  have hbr := angle_bisector_iff ha hb' hc hsign
  -- The polynomial form of the bisector condition in coordinates.
  have i1 : ⟪C w z - B u v, G - B u v⟫_ℝ = (w - u) * x - (z + v) * y := by
    rw [inner_coord]
    simp only [C, B, pt, PiLp.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      ← hx, ← hy]
    ring
  have i2 : ⟪D w z - B u v, D w z - B u v⟫_ℝ = (w + u) ^ 2 + (z + v) ^ 2 := by
    rw [inner_coord]
    simp only [D, B, pt, PiLp.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  have i3 : ⟪D w z - B u v, G - B u v⟫_ℝ = -(w + u) * x - (z + v) * y := by
    rw [inner_coord]
    simp only [D, B, pt, PiLp.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      ← hx, ← hy]
    ring
  have i4 : ⟪C w z - B u v, C w z - B u v⟫_ℝ = (w - u) ^ 2 + (z + v) ^ 2 := by
    rw [inner_coord]
    simp only [C, B, pt, PiLp.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  have hH_iff : (⟪C w z - B u v, G - B u v⟫_ℝ ^ 2 * ⟪D w z - B u v, D w z - B u v⟫_ℝ
        = ⟪D w z - B u v, G - B u v⟫_ℝ ^ 2 * ⟪C w z - B u v, C w z - B u v⟫_ℝ)
      ↔ polyH u v w z x y = 0 := by
    rw [i1, i2, i3, i4]
    simp only [polyH]
    constructor <;> intro h <;> linarith only [h]
  -- Now the two directions of the equivalence.
  constructor
  · -- Forward: `P Q R S` concyclic implies `BG` bisects `∠CBD`.
    intro hcyc
    obtain ⟨c, r, hmem⟩ := hcyc.1
    have hPm : dist P c = r := hmem P (by simp)
    have hQm : dist Q c = r := hmem Q (by simp)
    have hRm : dist R c = r := hmem R (by simp)
    have hSm : dist S c = r := hmem S (by simp)
    have ePR : (P 0 - c 0) ^ 2 + (P 1 - c 1) ^ 2 = (R 0 - c 0) ^ 2 + (R 1 - c 1) ^ 2 := by
      have h1 : Real.sqrt ((P 0 - c 0) ^ 2 + (P 1 - c 1) ^ 2)
          = Real.sqrt ((R 0 - c 0) ^ 2 + (R 1 - c 1) ^ 2) := by
        rw [← dist_coord, ← dist_coord, hPm, hRm]
      exact (Real.sqrt_inj (by positivity) (by positivity)).mp h1
    have eQR : (Q 0 - c 0) ^ 2 + (Q 1 - c 1) ^ 2 = (R 0 - c 0) ^ 2 + (R 1 - c 1) ^ 2 := by
      have h1 : Real.sqrt ((Q 0 - c 0) ^ 2 + (Q 1 - c 1) ^ 2)
          = Real.sqrt ((R 0 - c 0) ^ 2 + (R 1 - c 1) ^ 2) := by
        rw [← dist_coord, ← dist_coord, hQm, hRm]
      exact (Real.sqrt_inj (by positivity) (by positivity)).mp h1
    have eSR : (S 0 - c 0) ^ 2 + (S 1 - c 1) ^ 2 = (R 0 - c 0) ^ 2 + (R 1 - c 1) ^ 2 := by
      have h1 : Real.sqrt ((S 0 - c 0) ^ 2 + (S 1 - c 1) ^ 2)
          = Real.sqrt ((R 0 - c 0) ^ 2 + (R 1 - c 1) ^ 2) := by
        rw [← dist_coord, ← dist_coord, hSm, hRm]
      exact (Real.sqrt_inj (by positivity) (by positivity)).mp h1
    have hc0 : c 0 = m := by
      rw [hS1, hR1] at eSR
      have h1 : (S 0 - R 0) * (S 0 + R 0 - 2 * (c 0)) = 0 := by linear_combination eSR
      have h2 : S 0 + R 0 - 2 * (c 0) = 0 :=
        (mul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr (ne_of_lt hSR).symm)
      linarith only [h2, h2m]
    have eq1 : ((P 0) ^ 2 + (P 1) ^ 2) - ((R 0) ^ 2 + (R 1) ^ 2) - 2 * m * (P 0 - R 0)
        = 2 * (c 1) * (P 1 - (v + y)) := by
      rw [hR1] at ePR ⊢
      have ePR' : (P 0) ^ 2 - 2 * (c 0) * (P 0) + ((P 1) ^ 2 - 2 * (c 1) * (P 1))
          = (R 0) ^ 2 - 2 * (c 0) * (R 0) + ((v + y) ^ 2 - 2 * (c 1) * (v + y)) := by
        linear_combination ePR
      rw [hc0] at ePR'
      linear_combination ePR'
    have eq2 : ((Q 0) ^ 2 + (Q 1) ^ 2) - ((R 0) ^ 2 + (R 1) ^ 2) - 2 * m * (Q 0 - R 0)
        = 2 * (c 1) * (Q 1 - (v + y)) := by
      rw [hR1] at eQR ⊢
      have eQR' : (Q 0) ^ 2 - 2 * (c 0) * (Q 0) + ((Q 1) ^ 2 - 2 * (c 1) * (Q 1))
          = (R 0) ^ 2 - 2 * (c 0) * (R 0) + ((v + y) ^ 2 - 2 * (c 1) * (v + y)) := by
        linear_combination eQR
      rw [hc0] at eQR'
      linear_combination eQR'
    have hE1 : (((Q 0) ^ 2 + (Q 1) ^ 2) - ((R 0) ^ 2 + (R 1) ^ 2) - 2 * m * (Q 0 - R 0))
          * (P 1 - (v + y))
        - (((P 0) ^ 2 + (P 1) ^ 2) - ((R 0) ^ 2 + (R 1) ^ 2) - 2 * m * (P 0 - R 0))
          * (Q 1 - (v + y)) = 0 := by
      rw [eq1, eq2]
      ring
    have key := e1_cleared u v w z x y m (P 0) (P 1) (Q 0) (Q 1) (R 0) (R 1)
      hP0f hP1f hQ0f hQ1f hR0f hR1 hm
    rw [hE1, zero_mul] at key
    have hN : polyN u v w z x y = 0 := key.symm
    have hH : polyH u v w z x y = 0 := hNH.mp hN
    exact hbr.mpr ((hH_iff).mpr hH)
  · -- Backward: `BG` bisects `∠CBD` implies `P Q R S` concyclic.
    intro hang
    have hH : polyH u v w z x y = 0 := (hH_iff).mp (hbr.mp hang)
    have hN : polyN u v w z x y = 0 := hNH.mpr hH
    have key := e1_cleared u v w z x y m (P 0) (P 1) (Q 0) (Q 1) (R 0) (R 1)
      hP0f hP1f hQ0f hQ1f hR0f hR1 hm
    rw [hN] at key
    have hdn : (denP u x y) ^ 2 * (denQ x y) ^ 2 * (v + z) ^ 2 ≠ 0 :=
      mul_ne_zero (mul_ne_zero (pow_ne_zero 2 (ne_of_gt hdenP))
        (pow_ne_zero 2 (ne_of_gt hdenQ))) (pow_ne_zero 2 (ne_of_gt hvz))
    have hE1 : (((Q 0) ^ 2 + (Q 1) ^ 2) - ((R 0) ^ 2 + (R 1) ^ 2) - 2 * m * (Q 0 - R 0))
          * (P 1 - (v + y))
        - (((P 0) ^ 2 + (P 1) ^ 2) - ((R 0) ^ 2 + (R 1) ^ 2) - 2 * m * (P 0 - R 0))
          * (Q 1 - (v + y)) = 0 :=
      (mul_eq_zero.mp key).resolve_right hdn
    set k := (((P 0) ^ 2 + (P 1) ^ 2) - ((R 0) ^ 2 + (R 1) ^ 2) - 2 * m * (P 0 - R 0))
      / (2 * (P 1 - (v + y))) with hk_def
    have h2ne : (2 : ℝ) * (P 1 - (v + y)) ≠ 0 := mul_ne_zero two_ne_zero hP1ne
    have eq1 : ((P 0) ^ 2 + (P 1) ^ 2) - ((R 0) ^ 2 + (R 1) ^ 2) - 2 * m * (P 0 - R 0)
        = 2 * k * (P 1 - (v + y)) := by
      have e := div_mul_cancel₀
        (((P 0) ^ 2 + (P 1) ^ 2) - ((R 0) ^ 2 + (R 1) ^ 2) - 2 * m * (P 0 - R 0)) h2ne
      rw [hk_def]
      linear_combination -e
    have eq2 : ((Q 0) ^ 2 + (Q 1) ^ 2) - ((R 0) ^ 2 + (R 1) ^ 2) - 2 * m * (Q 0 - R 0)
        = 2 * k * (Q 1 - (v + y)) := by
      have h1 : (((Q 0) ^ 2 + (Q 1) ^ 2) - ((R 0) ^ 2 + (R 1) ^ 2) - 2 * m * (Q 0 - R 0))
            * (P 1 - (v + y))
          = (2 * k * (Q 1 - (v + y))) * (P 1 - (v + y)) := by
        linear_combination hE1 + eq1 * (Q 1 - (v + y))
      exact mul_right_cancel₀ hP1ne h1
    have eqS : ((S 0) ^ 2 + (S 1) ^ 2) - ((R 0) ^ 2 + (R 1) ^ 2) - 2 * m * (S 0 - R 0)
        = 0 := by
      rw [hS1, hR1]
      linear_combination (S 0 - R 0) * h2m
    refine ⟨?_, coplanar_of_finrank_eq_two _ finrank_euclideanSpace_fin⟩
    refine ⟨pt m k, dist R (pt m k), ?_⟩
    rintro X hX
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hX
    rcases hX with hX | hX | hX | hX
    · rw [hX]
      have hsq : (P 0 - m) ^ 2 + (P 1 - k) ^ 2 = (R 0 - m) ^ 2 + (R 1 - k) ^ 2 := by
        rw [hR1] at eq1 ⊢
        linear_combination eq1
      rw [dist_coord, dist_coord]
      simp only [pt, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [hsq]
    · rw [hX]
      have hsq : (Q 0 - m) ^ 2 + (Q 1 - k) ^ 2 = (R 0 - m) ^ 2 + (R 1 - k) ^ 2 := by
        rw [hR1] at eq2 ⊢
        linear_combination eq2
      rw [dist_coord, dist_coord]
      simp only [pt, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [hsq]
    · rw [hX]
    · rw [hX]
      have hsq : (S 0 - m) ^ 2 + (S 1 - k) ^ 2 = (R 0 - m) ^ 2 + (R 1 - k) ^ 2 := by
        rw [hS1, hR1] at eqS ⊢
        linear_combination eqS
      rw [dist_coord, dist_coord]
      simp only [pt, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [hsq]

end Usa2009P5

