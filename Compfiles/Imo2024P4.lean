/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 2024, Problem 4

Let triangle ABC with incenter I satisfying AB < AC < BC. Let X be a point
on line BC, different from C, such that the line through X and parallel to AC is
tangent to the incircle. Similarly, let Y be a point on line BC, different from B,
such that the line through Y and parallel to AB is tangent to the incircle. Line
AI intersects the circumcircle of triangle ABC again at P. Let K and L be the
midpoints of AC and AB, respectively. Prove that ∠KIL + ∠YPX = 180°.

## Formalization

We prove the result by a coordinate computation. Every triangle is similar to a
triangle whose incircle is the unit circle centered at the origin, with the side
BC lying on the line `y = -1`. Writing `u = tan(B/2)` and `v = tan(C/2)`, the
conditions `0 < u`, `0 < v` and `u * v < 1` parametrize all triangles up to
similarity (note `B/2 + C/2 < π/2`), and every point of the configuration is a
rational function of `u` and `v`:

* `A = ((v-u)/(1-uv), (1+uv)/(1-uv))`, `B = (-1/u, -1)`, `C = (1/v, -1)`;
* the incenter is `I = (0, 0)`;
* `X = (-v, -1)`, `Y = (u, -1)` (the tangents parallel to AC, AB are the
  tangents to the unit circle at the antipodes of the touchpoints);
* `P = ((u-v)/(2uv), -(1+uv)/(2uv))` (the second intersection of line `AI`
  with the circumcircle, computed via the power of the origin);
* `K`, `L` are the midpoints of `AC` and `AB`.

The side condition `AB < AC < BC` becomes `dist A B < dist A C < dist B C`,
taken as hypotheses (they are satisfiable, e.g. `u = 4/7`, `v = 1/2` gives the
13-14-15 triangle). The conclusion `∠KIL + ∠YPX = π` reduces, via
`Real.arccos_neg`, to the statement that the cosines of the two angles are
negatives of each other, which is a pair of polynomial identities in `u` and `v`.
-/

namespace Imo2024P4

open scoped EuclideanGeometry

/-- The plane, as the ambient space for the problem. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Vertex `A`, in the parametrization by `u = tan(B/2)`, `v = tan(C/2)`. -/
noncomputable def ptA (u v : ℝ) : Plane := !₂[(v - u) / (1 - u * v), (1 + u * v) / (1 - u * v)]

/-- Vertex `B`: the tangents from `B` to the unit circle have length `1/u`. -/
noncomputable def ptB (u _v : ℝ) : Plane := !₂[-1 / u, -1]

/-- Vertex `C`: the tangents from `C` to the unit circle have length `1/v`. -/
noncomputable def ptC (_u v : ℝ) : Plane := !₂[1 / v, -1]

/-- The midpoint `K` of `AC`. -/
noncomputable def ptK (u v : ℝ) : Plane :=
  !₂[(1 + v ^ 2 - 2 * u * v) / (2 * v * (1 - u * v)), u * v / (1 - u * v)]

/-- The midpoint `L` of `AB`. -/
noncomputable def ptL (u v : ℝ) : Plane :=
  !₂[-(1 + u ^ 2 - 2 * u * v) / (2 * u * (1 - u * v)), u * v / (1 - u * v)]

/-- The point `X` on line `BC` (i.e. on `y = -1`) such that the line through `X`
parallel to `AC` is tangent to the incircle. -/
noncomputable def ptX (_u v : ℝ) : Plane := !₂[-v, -1]

/-- The point `Y` on line `BC` such that the line through `Y` parallel to `AB`
is tangent to the incircle. -/
noncomputable def ptY (u _v : ℝ) : Plane := !₂[u, -1]

/-- The second intersection of line `AI` with the circumcircle of `ABC`. -/
noncomputable def ptP (u v : ℝ) : Plane := !₂[(u - v) / (2 * u * v), -(1 + u * v) / (2 * u * v)]

snip begin

/-- The common numerator factor of the two dot products
`K · L` and `(Y - P) · (X - P)` (up to signs and denominators). -/
def Phi (u v : ℝ) : ℝ :=
  1 + u ^ 2 + v ^ 2 - 4 * u * v + 5 * u ^ 2 * v ^ 2 - 2 * u ^ 3 * v - 2 * u * v ^ 3
    - 4 * u ^ 3 * v ^ 3

/-- Numerator of `‖Y - P‖²`. -/
def S1 (u v : ℝ) : ℝ := (2 * u ^ 2 * v - u + v) ^ 2 + (1 - u * v) ^ 2

/-- Numerator of `‖X - P‖²`. -/
def S2 (u v : ℝ) : ℝ := (2 * u * v ^ 2 + u - v) ^ 2 + (1 - u * v) ^ 2

/-- Numerator of `‖K‖²`. -/
def T1 (u v : ℝ) : ℝ := (1 + v ^ 2 - 2 * u * v) ^ 2 + 4 * u ^ 2 * v ^ 4

/-- Numerator of `‖L‖²`. -/
def T2 (u v : ℝ) : ℝ := (1 + u ^ 2 - 2 * u * v) ^ 2 + 4 * u ^ 4 * v ^ 2

lemma inner_pt (a b c d : ℝ) :
    inner ℝ (!₂[a, b] : Plane) (!₂[c, d]) = a * c + b * d := by
  simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

lemma inner_sub_pt (a b c d e f g h : ℝ) :
    inner ℝ (!₂[a, b] -ᵥ !₂[c, d] : Plane) (!₂[e, f] -ᵥ !₂[g, h]) =
      (a - c) * (e - g) + (b - d) * (f - h) := by
  simp only [vsub_eq_sub, PiLp.sub_apply, PiLp.inner_apply, Fin.sum_univ_two,
    RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

lemma inner_pt_sub (a b e f g h : ℝ) :
    inner ℝ (!₂[a, b] : Plane) (!₂[e, f] -ᵥ !₂[g, h]) = a * (e - g) + b * (f - h) := by
  simp only [vsub_eq_sub, PiLp.sub_apply, PiLp.inner_apply, Fin.sum_univ_two,
    RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

lemma normSq_pt (a b : ℝ) : ‖(!₂[a, b] : Plane)‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two, sq_abs]

lemma normSq_sub_pt (a b c d : ℝ) :
    ‖(!₂[a, b] -ᵥ !₂[c, d] : Plane)‖ ^ 2 = (a - c) ^ 2 + (b - d) ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two, sq_abs, vsub_eq_sub, PiLp.sub_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]

/-- A point of the plane with a nonzero second coordinate is nonzero. -/
lemma ne_zero_of_coord1 {x : Plane} {c : ℝ} (h : x 1 = c) (hc : c ≠ 0) : x ≠ 0 := by
  rintro rfl
  simp at h
  exact hc h.symm

/-- Clearing a single nonzero factor on the left. -/
lemma eq_div_of_mul_left {F x N : ℝ} (hF : F ≠ 0) (h : F * x = N) : x = N / F := by
  rw [eq_div_iff_mul_eq hF, mul_comm]
  exact h

/-! ### Coordinate computations -/

lemma ptK_coord1 (u v : ℝ) : (ptK u v) 1 = u * v / (1 - u * v) := by
  simp [ptK, Matrix.cons_val_one]

lemma ptL_coord1 (u v : ℝ) : (ptL u v) 1 = u * v / (1 - u * v) := by
  simp [ptL, Matrix.cons_val_one]

lemma sub_YP_coord1 (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    (ptY u v -ᵥ ptP u v) 1 = (1 - u * v) / (2 * u * v) := by
  have hu' : u ≠ 0 := ne_of_gt hu
  have hv' : v ≠ 0 := ne_of_gt hv
  simp only [ptY, ptP, vsub_eq_sub, PiLp.sub_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  field_simp
  ring

lemma sub_XP_coord1 (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    (ptX u v -ᵥ ptP u v) 1 = (1 - u * v) / (2 * u * v) := by
  have hu' : u ≠ 0 := ne_of_gt hu
  have hv' : v ≠ 0 := ne_of_gt hv
  simp only [ptX, ptP, vsub_eq_sub, PiLp.sub_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  field_simp
  ring

lemma ptK_ne_zero (u v : ℝ) (hu : 0 < u) (hv : 0 < v) (huv : u * v < 1) :
    ptK u v ≠ 0 := by
  have h1uv : (0 : ℝ) < 1 - u * v := sub_pos.mpr huv
  have huvpos : (0 : ℝ) < u * v := mul_pos hu hv
  exact ne_zero_of_coord1 (ptK_coord1 u v) (div_ne_zero huvpos.ne' h1uv.ne')

lemma ptL_ne_zero (u v : ℝ) (hu : 0 < u) (hv : 0 < v) (huv : u * v < 1) :
    ptL u v ≠ 0 := by
  have h1uv : (0 : ℝ) < 1 - u * v := sub_pos.mpr huv
  have huvpos : (0 : ℝ) < u * v := mul_pos hu hv
  exact ne_zero_of_coord1 (ptL_coord1 u v) (div_ne_zero huvpos.ne' h1uv.ne')

lemma sub_YP_ne_zero (u v : ℝ) (hu : 0 < u) (hv : 0 < v) (huv : u * v < 1) :
    ptY u v -ᵥ ptP u v ≠ 0 := by
  have h1uv : (0 : ℝ) < 1 - u * v := sub_pos.mpr huv
  have h2uv : (2 : ℝ) * u * v ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hu.ne') hv.ne'
  exact ne_zero_of_coord1 (sub_YP_coord1 u v hu hv) (div_ne_zero h1uv.ne' h2uv)

lemma sub_XP_ne_zero (u v : ℝ) (hu : 0 < u) (hv : 0 < v) (huv : u * v < 1) :
    ptX u v -ᵥ ptP u v ≠ 0 := by
  have h1uv : (0 : ℝ) < 1 - u * v := sub_pos.mpr huv
  have h2uv : (2 : ℝ) * u * v ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hu.ne') hv.ne'
  exact ne_zero_of_coord1 (sub_XP_coord1 u v hu hv) (div_ne_zero h1uv.ne' h2uv)

/-- The dot product `K · L`, cleared of denominators. -/
lemma inner_KL (u v : ℝ) (hu : 0 < u) (hv : 0 < v) (huv : u * v < 1) :
    4 * u * v * (1 - u * v) ^ 2 * inner ℝ (ptK u v) (ptL u v) = -Phi u v := by
  have hu' : u ≠ 0 := ne_of_gt hu
  have hv' : v ≠ 0 := ne_of_gt hv
  have huv' : (1 : ℝ) - v * u ≠ 0 := by
    rw [mul_comm v u]
    exact ne_of_gt (sub_pos.mpr huv)
  have huv'' : (1 : ℝ) - u * v ≠ 0 := ne_of_gt (sub_pos.mpr huv)
  simp only [ptK, ptL]
  rw [inner_pt]
  field_simp
  simp only [Phi]
  ring

/-- The dot product `(Y - P) · (X - P)`, cleared of denominators. -/
lemma inner_YPXP (u v : ℝ) (hu : 0 < u) (hv : 0 < v) (huv : u * v < 1) :
    4 * u ^ 2 * v ^ 2 * inner ℝ (ptY u v -ᵥ ptP u v) (ptX u v -ᵥ ptP u v) = Phi u v := by
  have hu' : u ≠ 0 := ne_of_gt hu
  have hv' : v ≠ 0 := ne_of_gt hv
  have huv' : (1 : ℝ) - v * u ≠ 0 := by
    rw [mul_comm v u]
    exact ne_of_gt (sub_pos.mpr huv)
  have huv'' : (1 : ℝ) - u * v ≠ 0 := ne_of_gt (sub_pos.mpr huv)
  simp only [ptY, ptP, ptX]
  rw [inner_sub_pt]
  field_simp
  simp only [Phi]
  ring

lemma normSq_K (u v : ℝ) (hu : 0 < u) (hv : 0 < v) (huv : u * v < 1) :
    4 * v ^ 2 * (1 - u * v) ^ 2 * ‖ptK u v‖ ^ 2 = T1 u v := by
  have hu' : u ≠ 0 := ne_of_gt hu
  have hv' : v ≠ 0 := ne_of_gt hv
  have huv' : (1 : ℝ) - v * u ≠ 0 := by
    rw [mul_comm v u]
    exact ne_of_gt (sub_pos.mpr huv)
  have huv'' : (1 : ℝ) - u * v ≠ 0 := ne_of_gt (sub_pos.mpr huv)
  simp only [ptK]
  rw [normSq_pt]
  field_simp
  simp only [T1]
  ring

lemma normSq_L (u v : ℝ) (hu : 0 < u) (hv : 0 < v) (huv : u * v < 1) :
    4 * u ^ 2 * (1 - u * v) ^ 2 * ‖ptL u v‖ ^ 2 = T2 u v := by
  have hu' : u ≠ 0 := ne_of_gt hu
  have hv' : v ≠ 0 := ne_of_gt hv
  have huv' : (1 : ℝ) - v * u ≠ 0 := by
    rw [mul_comm v u]
    exact ne_of_gt (sub_pos.mpr huv)
  have huv'' : (1 : ℝ) - u * v ≠ 0 := ne_of_gt (sub_pos.mpr huv)
  simp only [ptL]
  rw [normSq_pt]
  field_simp
  simp only [T2]
  ring

lemma normSq_YP (u v : ℝ) (hu : 0 < u) (hv : 0 < v) (huv : u * v < 1) :
    4 * u ^ 2 * v ^ 2 * ‖ptY u v -ᵥ ptP u v‖ ^ 2 = S1 u v := by
  have hu' : u ≠ 0 := ne_of_gt hu
  have hv' : v ≠ 0 := ne_of_gt hv
  have huv' : (1 : ℝ) - v * u ≠ 0 := by
    rw [mul_comm v u]
    exact ne_of_gt (sub_pos.mpr huv)
  have huv'' : (1 : ℝ) - u * v ≠ 0 := ne_of_gt (sub_pos.mpr huv)
  simp only [ptY, ptP]
  rw [normSq_sub_pt]
  field_simp
  simp only [S1]
  ring

lemma normSq_XP (u v : ℝ) (hu : 0 < u) (hv : 0 < v) (huv : u * v < 1) :
    4 * u ^ 2 * v ^ 2 * ‖ptX u v -ᵥ ptP u v‖ ^ 2 = S2 u v := by
  have hu' : u ≠ 0 := ne_of_gt hu
  have hv' : v ≠ 0 := ne_of_gt hv
  have huv' : (1 : ℝ) - v * u ≠ 0 := by
    rw [mul_comm v u]
    exact ne_of_gt (sub_pos.mpr huv)
  have huv'' : (1 : ℝ) - u * v ≠ 0 := ne_of_gt (sub_pos.mpr huv)
  simp only [ptX, ptP]
  rw [normSq_sub_pt]
  field_simp
  simp only [S2]
  ring

/-- The key polynomial identity: the numerators of `‖Y-P‖² · ‖X-P‖²` and of
`‖K‖² · ‖L‖²` agree. -/
lemma hPoly (u v : ℝ) : S1 u v * S2 u v = T1 u v * T2 u v := by
  simp only [S1, S2, T1, T2]
  ring

/-- A real-analysis warm-up: if `p * q ≤ 0` and `(p * b)² = (q * a)²` with
`a, b > 0`, then `p / a = -(q / b)`. -/
lemma neg_div_of_sq_mul_sq {p q a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hpq : p * q ≤ 0) (hsq : (p * b) ^ 2 = (q * a) ^ 2) :
    p / a = -(q / b) := by
  rw [← neg_div, div_eq_div_iff (ne_of_gt ha) (ne_of_gt hb)]
  rw [sq_eq_sq_iff_eq_or_eq_neg] at hsq
  rcases hsq with h | h
  · -- If `p * b = q * a`, the sign condition forces `p = q = 0`.
    have hle : (p * b) * (q * a) ≤ 0 := by
      have e : (p * b) * (q * a) = (p * q) * (a * b) := by ring
      rw [e]
      exact mul_nonpos_of_nonpos_of_nonneg hpq (le_of_lt (mul_pos ha hb))
    rw [h] at hle
    have hqa : q * a * (q * a) = 0 := le_antisymm hle (mul_self_nonneg _)
    have hq0 : q * a = 0 := by
      rcases mul_eq_zero.mp hqa with h0 | h0 <;> exact h0
    have hq : q = 0 := by
      rcases mul_eq_zero.mp hq0 with hq | ha0
      · exact hq
      · exact absurd ha0 (ne_of_gt ha)
    have hp : p = 0 := by
      have hpb : p * b = 0 := by rw [h, hq, zero_mul]
      rcases mul_eq_zero.mp hpb with hp | hb0
      · exact hp
      · exact absurd hb0 (ne_of_gt hb)
    rw [hp, hq]
    norm_num
  · rw [← neg_mul] at h
    exact h

/-- The master identity: the squared cosines of the two angles agree. -/
lemma master (u v : ℝ) (hu : 0 < u) (hv : 0 < v) (huv : u * v < 1) :
    (inner ℝ (ptK u v) (ptL u v)) ^ 2 * (‖ptY u v -ᵥ ptP u v‖ ^ 2 * ‖ptX u v -ᵥ ptP u v‖ ^ 2)
    = (inner ℝ (ptY u v -ᵥ ptP u v) (ptX u v -ᵥ ptP u v)) ^ 2 * (‖ptK u v‖ ^ 2 * ‖ptL u v‖ ^ 2) := by
  have h1uv : (0 : ℝ) < 1 - u * v := sub_pos.mpr huv
  have hF1ne : (4 : ℝ) * u * v * (1 - u * v) ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hu.ne') hv.ne')
      (pow_ne_zero 2 h1uv.ne')
  have hF2ne : (4 : ℝ) * u ^ 2 * v ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hu.ne')) (pow_ne_zero 2 hv.ne')
  have hF3ne : (4 : ℝ) * v ^ 2 * (1 - u * v) ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hv.ne')) (pow_ne_zero 2 h1uv.ne')
  have hF4ne : (4 : ℝ) * u ^ 2 * (1 - u * v) ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hu.ne')) (pow_ne_zero 2 h1uv.ne')
  have h1 := inner_KL u v hu hv huv
  have h1sq : (4 * u * v * (1 - u * v) ^ 2) ^ 2 * (inner ℝ (ptK u v) (ptL u v)) ^ 2
      = Phi u v ^ 2 := by
    linear_combination (4 * u * v * (1 - u * v) ^ 2 * (inner ℝ (ptK u v) (ptL u v))
      - Phi u v) * h1
  have h2 := inner_YPXP u v hu hv huv
  have h2sq : (4 * u ^ 2 * v ^ 2) ^ 2
      * (inner ℝ (ptY u v -ᵥ ptP u v) (ptX u v -ᵥ ptP u v)) ^ 2 = Phi u v ^ 2 := by
    linear_combination (4 * u ^ 2 * v ^ 2
      * (inner ℝ (ptY u v -ᵥ ptP u v) (ptX u v -ᵥ ptP u v)) + Phi u v) * h2
  have h3 := normSq_K u v hu hv huv
  have h4 := normSq_L u v hu hv huv
  have h5 := normSq_YP u v hu hv huv
  have h6 := normSq_XP u v hu hv huv
  have hF : (4 * u * v * (1 - u * v) ^ 2) ^ 2
      = (4 * v ^ 2 * (1 - u * v) ^ 2) * (4 * u ^ 2 * (1 - u * v) ^ 2) := by ring
  have hPoly2 : S1 u v * S2 u v * ((4 * v ^ 2 * (1 - u * v) ^ 2) * (4 * u ^ 2 * (1 - u * v) ^ 2))
      = T1 u v * T2 u v * (4 * u * v * (1 - u * v) ^ 2) ^ 2 := by
    have hP := hPoly u v
    linear_combination ((4 * v ^ 2 * (1 - u * v) ^ 2) * (4 * u ^ 2 * (1 - u * v) ^ 2)) * hP
      - T1 u v * T2 u v * hF
  have hD : (4 * u * v * (1 - u * v) ^ 2) ^ 2 * ((4 * u ^ 2 * v ^ 2) ^ 2
      * ((4 * v ^ 2 * (1 - u * v) ^ 2) * (4 * u ^ 2 * (1 - u * v) ^ 2))) ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hF1ne)
      (mul_ne_zero (pow_ne_zero 2 hF2ne) (mul_ne_zero hF3ne hF4ne))
  apply mul_left_cancel₀ hD
  linear_combination
    (4 * u ^ 2 * v ^ 2 * ‖ptY u v -ᵥ ptP u v‖ ^ 2) * (4 * u ^ 2 * v ^ 2 * ‖ptX u v -ᵥ ptP u v‖ ^ 2)
      * ((4 * v ^ 2 * (1 - u * v) ^ 2) * (4 * u ^ 2 * (1 - u * v) ^ 2)) * h1sq
    - (4 * v ^ 2 * (1 - u * v) ^ 2 * ‖ptK u v‖ ^ 2) * (4 * u ^ 2 * (1 - u * v) ^ 2 * ‖ptL u v‖ ^ 2)
      * (4 * u * v * (1 - u * v) ^ 2) ^ 2 * h2sq
    + Phi u v ^ 2 * ((4 * u ^ 2 * v ^ 2 * ‖ptX u v -ᵥ ptP u v‖ ^ 2)
      * ((4 * v ^ 2 * (1 - u * v) ^ 2) * (4 * u ^ 2 * (1 - u * v) ^ 2))) * h5
    + Phi u v ^ 2 * (S1 u v
      * ((4 * v ^ 2 * (1 - u * v) ^ 2) * (4 * u ^ 2 * (1 - u * v) ^ 2))) * h6
    - Phi u v ^ 2 * ((4 * u ^ 2 * (1 - u * v) ^ 2 * ‖ptL u v‖ ^ 2)
      * (4 * u * v * (1 - u * v) ^ 2) ^ 2) * h3
    - Phi u v ^ 2 * (T1 u v * (4 * u * v * (1 - u * v) ^ 2) ^ 2) * h4
    + Phi u v ^ 2 * hPoly2

/-! ### Sanity checks on the parametrization

The following lemmas verify that the explicit points really are the ones
described in the problem: `K` and `L` are the midpoints, and `P` lies on the
line `AI` (it is a scalar multiple of `A`). -/

/-- `K` is indeed the midpoint of `AC`. -/
lemma ptK_eq_midpoint (u v : ℝ) (hu : 0 < u) (hv : 0 < v) (huv : u * v < 1) :
    ptK u v = midpoint ℝ (ptA u v) (ptC u v) := by
  have hu' : u ≠ 0 := ne_of_gt hu
  have hv' : v ≠ 0 := ne_of_gt hv
  have huv' : (1 : ℝ) - v * u ≠ 0 := by
    rw [mul_comm v u]
    exact ne_of_gt (sub_pos.mpr huv)
  have huv'' : (1 : ℝ) - u * v ≠ 0 := ne_of_gt (sub_pos.mpr huv)
  rw [midpoint_eq_smul_add]
  ext i
  fin_cases i <;>
    simp [ptK, ptA, ptC, Matrix.cons_val_zero, Matrix.cons_val_one,
      PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] <;>
    field_simp <;> ring

/-- `L` is indeed the midpoint of `AB`. -/
lemma ptL_eq_midpoint (u v : ℝ) (hu : 0 < u) (hv : 0 < v) (huv : u * v < 1) :
    ptL u v = midpoint ℝ (ptA u v) (ptB u v) := by
  have hu' : u ≠ 0 := ne_of_gt hu
  have hv' : v ≠ 0 := ne_of_gt hv
  have huv' : (1 : ℝ) - v * u ≠ 0 := by
    rw [mul_comm v u]
    exact ne_of_gt (sub_pos.mpr huv)
  have huv'' : (1 : ℝ) - u * v ≠ 0 := ne_of_gt (sub_pos.mpr huv)
  rw [midpoint_eq_smul_add]
  ext i
  fin_cases i <;>
    simp [ptL, ptA, ptB, Matrix.cons_val_zero, Matrix.cons_val_one,
      PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] <;>
    field_simp <;> ring

/-- `P` lies on line `AI`: it is a scalar multiple of `A`. -/
lemma ptP_eq_smul (u v : ℝ) (hu : 0 < u) (hv : 0 < v) (huv : u * v < 1) :
    ptP u v = (-(1 - u * v) / (2 * u * v)) • ptA u v := by
  have hu' : u ≠ 0 := ne_of_gt hu
  have hv' : v ≠ 0 := ne_of_gt hv
  have huv' : (1 : ℝ) - v * u ≠ 0 := by
    rw [mul_comm v u]
    exact ne_of_gt (sub_pos.mpr huv)
  have huv'' : (1 : ℝ) - u * v ≠ 0 := ne_of_gt (sub_pos.mpr huv)
  ext i
  fin_cases i <;>
    simp [ptP, ptA, Matrix.cons_val_zero, Matrix.cons_val_one,
      PiLp.smul_apply, smul_eq_mul] <;>
    field_simp <;> ring

/-- The touchpoint of the tangent parallel to `AC` (the antipode of the
touchpoint of `AC` itself). -/
noncomputable def ptTX (_u v : ℝ) : Plane := !₂[-2 * v / (1 + v ^ 2), -(1 - v ^ 2) / (1 + v ^ 2)]

/-- The touchpoint of the tangent parallel to `AB` (the antipode of the
touchpoint of `AB` itself). -/
noncomputable def ptTY (u _v : ℝ) : Plane := !₂[2 * u / (1 + u ^ 2), -(1 - u ^ 2) / (1 + u ^ 2)]

/-- The touchpoint `ptTX` lies on the incircle (the unit circle). -/
lemma ptTX_norm (u v : ℝ) : ‖ptTX u v‖ = 1 := by
  have hv2 : (1 : ℝ) + v ^ 2 ≠ 0 := by positivity
  have h : ‖ptTX u v‖ ^ 2 = 1 := by
    simp only [ptTX]
    rw [normSq_pt]
    field_simp
    ring
  rw [sq_eq_one_iff] at h
  rcases h with h | h
  · exact h
  · have := norm_nonneg (ptTX u v)
    nlinarith

/-- The radius to `ptTX` is perpendicular to the tangent direction `AC`. -/
lemma ptTX_perp (u v : ℝ) (hv : 0 < v) (huv : u * v < 1) :
    inner ℝ (ptTX u v) (ptC u v -ᵥ ptA u v) = 0 := by
  have hv' : v ≠ 0 := ne_of_gt hv
  have huv' : (1 : ℝ) - v * u ≠ 0 := by
    rw [mul_comm v u]
    exact ne_of_gt (sub_pos.mpr huv)
  have huv'' : (1 : ℝ) - u * v ≠ 0 := ne_of_gt (sub_pos.mpr huv)
  have hv2 : (1 : ℝ) + v ^ 2 ≠ 0 := by positivity
  simp only [ptTX, ptC, ptA]
  rw [inner_pt_sub]
  field_simp
  ring

/-- The line through `X` and `ptTX` is parallel to `AC`. -/
lemma ptTX_sub_ptX (u v : ℝ) (hu : 0 < u) (hv : 0 < v) (huv : u * v < 1) :
    ptTX u v -ᵥ ptX u v = (-(v ^ 2 * (1 - u * v)) / (1 + v ^ 2)) • (ptC u v -ᵥ ptA u v) := by
  have hu' : u ≠ 0 := ne_of_gt hu
  have hv' : v ≠ 0 := ne_of_gt hv
  have huv' : (1 : ℝ) - v * u ≠ 0 := by
    rw [mul_comm v u]
    exact ne_of_gt (sub_pos.mpr huv)
  have huv'' : (1 : ℝ) - u * v ≠ 0 := ne_of_gt (sub_pos.mpr huv)
  have hv2 : (1 : ℝ) + v ^ 2 ≠ 0 := by positivity
  ext i
  fin_cases i <;>
    simp [ptTX, ptX, ptC, ptA, Matrix.cons_val_zero, Matrix.cons_val_one,
      vsub_eq_sub, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] <;>
    field_simp <;> ring

/-- The touchpoint `ptTY` lies on the incircle (the unit circle). -/
lemma ptTY_norm (u v : ℝ) : ‖ptTY u v‖ = 1 := by
  have hu2 : (1 : ℝ) + u ^ 2 ≠ 0 := by positivity
  have h : ‖ptTY u v‖ ^ 2 = 1 := by
    simp only [ptTY]
    rw [normSq_pt]
    field_simp
    ring
  rw [sq_eq_one_iff] at h
  rcases h with h | h
  · exact h
  · have := norm_nonneg (ptTY u v)
    nlinarith

/-- The radius to `ptTY` is perpendicular to the tangent direction `AB`. -/
lemma ptTY_perp (u v : ℝ) (hu : 0 < u) (huv : u * v < 1) :
    inner ℝ (ptTY u v) (ptB u v -ᵥ ptA u v) = 0 := by
  have hu' : u ≠ 0 := ne_of_gt hu
  have huv' : (1 : ℝ) - v * u ≠ 0 := by
    rw [mul_comm v u]
    exact ne_of_gt (sub_pos.mpr huv)
  have huv'' : (1 : ℝ) - u * v ≠ 0 := ne_of_gt (sub_pos.mpr huv)
  have hu2 : (1 : ℝ) + u ^ 2 ≠ 0 := by positivity
  simp only [ptTY, ptB, ptA]
  rw [inner_pt_sub]
  field_simp
  ring

/-- The line through `Y` and `ptTY` is parallel to `AB`. -/
lemma ptTY_sub_ptY (u v : ℝ) (hu : 0 < u) (hv : 0 < v) (huv : u * v < 1) :
    ptTY u v -ᵥ ptY u v = (-(u ^ 2 * (1 - u * v)) / (1 + u ^ 2)) • (ptB u v -ᵥ ptA u v) := by
  have hu' : u ≠ 0 := ne_of_gt hu
  have hv' : v ≠ 0 := ne_of_gt hv
  have huv' : (1 : ℝ) - v * u ≠ 0 := by
    rw [mul_comm v u]
    exact ne_of_gt (sub_pos.mpr huv)
  have huv'' : (1 : ℝ) - u * v ≠ 0 := ne_of_gt (sub_pos.mpr huv)
  have hu2 : (1 : ℝ) + u ^ 2 ≠ 0 := by positivity
  ext i
  fin_cases i <;>
    simp [ptTY, ptY, ptB, ptA, Matrix.cons_val_zero, Matrix.cons_val_one,
      vsub_eq_sub, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] <;>
    field_simp <;> ring

snip end

problem imo2024_p4 (u v : ℝ) (hu : 0 < u) (hv : 0 < v) (huv : u * v < 1)
    (_hAB : dist (ptA u v) (ptB u v) < dist (ptA u v) (ptC u v))
    (_hAC : dist (ptA u v) (ptC u v) < dist (ptB u v) (ptC u v)) :
    ∠ (ptK u v) (0 : Plane) (ptL u v) + ∠ (ptY u v) (ptP u v) (ptX u v) = Real.pi := by
  have h1uv : (0 : ℝ) < 1 - u * v := sub_pos.mpr huv
  have huvpos : (0 : ℝ) < u * v := mul_pos hu hv
  have hnK : (0 : ℝ) < ‖ptK u v‖ := norm_pos_iff.mpr (ptK_ne_zero u v hu hv huv)
  have hnL : (0 : ℝ) < ‖ptL u v‖ := norm_pos_iff.mpr (ptL_ne_zero u v hu hv huv)
  have hnY : (0 : ℝ) < ‖ptY u v -ᵥ ptP u v‖ :=
    norm_pos_iff.mpr (sub_YP_ne_zero u v hu hv huv)
  have hnX : (0 : ℝ) < ‖ptX u v -ᵥ ptP u v‖ :=
    norm_pos_iff.mpr (sub_XP_ne_zero u v hu hv huv)
  -- The two dot products have opposite signs: their product is `-Φ²` times a
  -- positive factor.
  have hF1 : (0 : ℝ) < 4 * u * v * (1 - u * v) ^ 2 :=
    mul_pos (mul_pos (mul_pos (by norm_num) hu) hv) (pow_pos h1uv 2)
  have hF2 : (0 : ℝ) < 4 * u ^ 2 * v ^ 2 :=
    mul_pos (mul_pos (by norm_num) (pow_pos hu 2)) (pow_pos hv 2)
  have e : (4 * u * v * (1 - u * v) ^ 2) * (4 * u ^ 2 * v ^ 2) *
      (inner ℝ (ptK u v) (ptL u v) * inner ℝ (ptY u v -ᵥ ptP u v) (ptX u v -ᵥ ptP u v))
      = -(Phi u v) ^ 2 := by
    have hh1 := inner_KL u v hu hv huv
    have hh2 := inner_YPXP u v hu hv huv
    linear_combination (4 * u ^ 2 * v ^ 2)
      * (inner ℝ (ptY u v -ᵥ ptP u v) (ptX u v -ᵥ ptP u v)) * hh1 - Phi u v * hh2
  have hpq : inner ℝ (ptK u v) (ptL u v)
      * inner ℝ (ptY u v -ᵥ ptP u v) (ptX u v -ᵥ ptP u v) ≤ 0 := by
    nlinarith [e, mul_pos hF1 hF2, sq_nonneg (Phi u v)]
  -- The squared cosines agree.
  have hM := master u v hu hv huv
  have hsq : (inner ℝ (ptK u v) (ptL u v) * (‖ptY u v -ᵥ ptP u v‖ * ‖ptX u v -ᵥ ptP u v‖)) ^ 2
      = (inner ℝ (ptY u v -ᵥ ptP u v) (ptX u v -ᵥ ptP u v) * (‖ptK u v‖ * ‖ptL u v‖)) ^ 2 := by
    rw [mul_pow (inner ℝ (ptK u v) (ptL u v)) (‖ptY u v -ᵥ ptP u v‖ * ‖ptX u v -ᵥ ptP u v‖),
      mul_pow ‖ptY u v -ᵥ ptP u v‖ ‖ptX u v -ᵥ ptP u v‖, hM,
      ← mul_pow ‖ptK u v‖ ‖ptL u v‖,
      ← mul_pow (inner ℝ (ptY u v -ᵥ ptP u v) (ptX u v -ᵥ ptP u v)) (‖ptK u v‖ * ‖ptL u v‖)]
  have key := neg_div_of_sq_mul_sq (mul_pos hnK hnL) (mul_pos hnY hnX) hpq hsq
  -- Unfold the angles to `arccos` and conclude.
  have hangle1 : ∠ (ptK u v) (0 : Plane) (ptL u v)
      = Real.arccos (inner ℝ (ptK u v) (ptL u v) / (‖ptK u v‖ * ‖ptL u v‖)) := by
    unfold EuclideanGeometry.angle InnerProductGeometry.angle
    simp
  have hangle2 : ∠ (ptY u v) (ptP u v) (ptX u v)
      = Real.arccos (inner ℝ (ptY u v -ᵥ ptP u v) (ptX u v -ᵥ ptP u v)
        / (‖ptY u v -ᵥ ptP u v‖ * ‖ptX u v -ᵥ ptP u v‖)) := by
    unfold EuclideanGeometry.angle InnerProductGeometry.angle
    rfl
  rw [hangle1, hangle2, key, Real.arccos_neg]
  exact sub_add_cancel _ _

end Imo2024P4
