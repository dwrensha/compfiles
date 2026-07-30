/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import Mathlib.Analysis.Real.Sqrt
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 1976, Problem 1

A plane convex quadrilateral has area 32, and the sum of two opposite sides
and a diagonal is 16. Determine all possible lengths for the other diagonal.

# Answer

The other diagonal must have length `8 * √2`.

# Solution

Let the quadrilateral be `A B C D`; without loss of generality the two
opposite sides are `AB`, `CD` and the given diagonal is `AC` (any other
labeling is symmetric). The area of the quadrilateral is the sum of the
areas of the triangles `ABC` and `ACD`, and each of these areas is at most
half the product of `AC` with the corresponding side (`AB` resp. `CD`),
with equality only if that side is perpendicular to `AC`. Hence, using
AM–GM,

`32 ≤ AC * (AB + CD) / 2 ≤ ((AC + AB + CD) / 2)^2 / 2 = 32`,

so equality holds throughout: `AC = AB + CD = 8` and both `AB` and `CD` are
perpendicular to `AC`. Since the quadrilateral is convex, `B` and `D` lie on
opposite sides of `AC`, so the other diagonal satisfies
`BD² = AC² + (AB + CD)² = 128`, i.e. `BD = 8 * √2`. This value is attained,
for example by `A = (0,0)`, `B = (0,4)`, `C = (8,0)`, `D = (8,-4)`.

(Problem and answer source: https://prase.cz/kalva/imo/isoln/isoln761.html)
-/

namespace Imo1976P1

/-- The Euclidean plane, coordinatized as `ℝ²`. -/
abbrev Point := Fin 2 → ℝ

/-- The scalar cross product of two plane vectors. -/
def cross (u v : Point) : ℝ := u 0 * v 1 - u 1 * v 0

/-- The inner (dot) product of two plane vectors. -/
def ip (u v : Point) : ℝ := u 0 * v 0 + u 1 * v 1

/-- The squared Euclidean norm of a plane vector. -/
def sqNorm (u : Point) : ℝ := u 0 ^ 2 + u 1 ^ 2

/-- The Euclidean distance between two points of the plane. -/
noncomputable def Dist (A B : Point) : ℝ := Real.sqrt (sqNorm (B - A))

/-- `A B C D` is a strictly convex quadrangle with vertices listed in order
(in either orientation): all four consecutive edge turns have the same strict
sign. -/
def ConvexQuad (A B C D : Point) : Prop :=
  (0 < cross (B - A) (C - B) ∧ 0 < cross (C - B) (D - C) ∧
      0 < cross (D - C) (A - D) ∧ 0 < cross (A - D) (B - A)) ∨
    (cross (B - A) (C - B) < 0 ∧ cross (C - B) (D - C) < 0 ∧
      cross (D - C) (A - D) < 0 ∧ cross (A - D) (B - A) < 0)

/-- The area of a convex quadrangle `A B C D`, as the sum of the areas of the
triangles `A B C` and `A C D` obtained by cutting along the diagonal `AC`. -/
noncomputable def QuadArea (A B C D : Point) : ℝ :=
  (|cross (B - A) (C - A)| + |cross (C - A) (D - A)|) / 2

snip begin

lemma sqNorm_nonneg (u : Point) : 0 ≤ sqNorm u := by
  simp only [sqNorm]
  positivity

/-- The two-dimensional Lagrange identity: `cross² + inner² = |u|² · |v|²`. -/
lemma lagrange (u v : Point) :
    cross u v ^ 2 + ip u v ^ 2 = sqNorm u * sqNorm v := by
  simp only [cross, ip, sqNorm]
  ring

lemma ip_comm (u v : Point) : ip u v = ip v u := by
  simp only [ip]
  ring

/-- The magnitude of the cross product of two vectors is at most the product
of their norms (the area of a triangle is at most half the product of two
sides). -/
lemma abs_cross_le (u v : Point) :
    |cross u v| ≤ Real.sqrt (sqNorm u) * Real.sqrt (sqNorm v) := by
  have h1 : cross u v ^ 2 ≤ sqNorm u * sqNorm v := by
    have h := lagrange u v
    have h2 : 0 ≤ ip u v ^ 2 := sq_nonneg _
    linarith only [h, h2]
  have h2 : cross u v ^ 2 ≤ (Real.sqrt (sqNorm u) * Real.sqrt (sqNorm v)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (sqNorm_nonneg u), Real.sq_sqrt (sqNorm_nonneg v)]
    exact h1
  exact abs_le_of_sq_le_sq h2 (by positivity)

/-- If equality holds in `abs_cross_le`, the two vectors are perpendicular. -/
lemma ip_eq_zero_of_abs_cross_eq {u v : Point}
    (h : |cross u v| = Real.sqrt (sqNorm u) * Real.sqrt (sqNorm v)) :
    ip u v = 0 := by
  have hsq : cross u v ^ 2 = sqNorm u * sqNorm v := by
    have h2 : cross u v ^ 2 = (Real.sqrt (sqNorm u) * Real.sqrt (sqNorm v)) ^ 2 := by
      rw [← sq_abs, h]
    rwa [mul_pow, Real.sq_sqrt (sqNorm_nonneg u), Real.sq_sqrt (sqNorm_nonneg v)] at h2
  have hz : ip u v ^ 2 = 0 := by
    have hl := lagrange u v
    linarith only [hl, hsq]
  exact sq_eq_zero_iff.mp hz

/-- The second triangle's cross product can be measured from `C` instead of
`A`. -/
lemma cross_sub_sub (A C D : Point) :
    cross (C - A) (D - A) = cross (C - A) (D - C) := by
  simp only [cross, Pi.sub_apply]
  ring

/-- The turn at `B` detects the side of the diagonal `AC` containing `B`. -/
lemma cross_turn1 (A B C : Point) :
    cross (C - A) (B - A) = -cross (B - A) (C - B) := by
  simp only [cross, Pi.sub_apply]
  ring

/-- The turn at `D` detects the side of the diagonal `AC` containing `D`. -/
lemma cross_turn3 (A _B C D : Point) :
    cross (C - A) (D - C) = cross (D - C) (A - D) := by
  simp only [cross, Pi.sub_apply]
  ring

/-- A two-dimensional identity relating inner and cross products. -/
lemma ip_mul_sqNorm (u p q : Point) :
    ip p q * sqNorm u = ip u p * ip u q + cross u p * cross u q := by
  simp only [ip, sqNorm, cross]
  ring

/-- Two plane vectors perpendicular to the same nonzero vector are parallel:
their cross product vanishes. -/
lemma cross_eq_zero_of_ip_eq_zero {u p q : Point} (hp : ip u p = 0)
    (hq : ip u q = 0) (hu : sqNorm u ≠ 0) : cross p q = 0 := by
  have key : cross p q * sqNorm u =
      (q 1 * u 0 - q 0 * u 1) * ip u p + (p 0 * u 1 - p 1 * u 0) * ip u q := by
    simp only [cross, ip, sqNorm]
    ring
  simp only [hp, hq, mul_zero, add_zero] at key
  exact (mul_eq_zero.mp key).resolve_right hu

/-- Expanding the squared norm of `u - p + q`. -/
lemma sqNorm_sub_add (u p q : Point) :
    sqNorm (u - p + q) =
      sqNorm u + sqNorm p + sqNorm q - 2 * ip u p + 2 * ip u q - 2 * ip p q := by
  simp only [sqNorm, ip, Pi.sub_apply, Pi.add_apply]
  ring

/-- `√128 = 8 * √2`. -/
lemma sqrt_128 : Real.sqrt 128 = 8 * Real.sqrt 2 := by
  have h1 : (0 : ℝ) ≤ 8 ^ 2 := by norm_num
  have h2 : (0 : ℝ) ≤ 8 := by norm_num
  rw [show (128 : ℝ) = 8 ^ 2 * 2 by norm_num, Real.sqrt_mul h1, Real.sqrt_sq h2]

/-- Componentwise computation with explicit points of the plane. -/
macro "coord" : tactic =>
  `(tactic| norm_num [cross, sqNorm, ip, Pi.sub_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons])

snip end

/-- The only possible length of the other diagonal. -/
noncomputable determine other_diagonal : ℝ := 8 * Real.sqrt 2

problem imo1976_p1 :
    {d : ℝ | ∃ A B C D : Point, ConvexQuad A B C D ∧ QuadArea A B C D = 32 ∧
        Dist A B + Dist C D + Dist A C = 16 ∧ d = Dist B D} = {other_diagonal} := by
  ext d
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Every admissible configuration has the other diagonal of length `8 * √2`.
    rintro ⟨A, B, C, D, hconv, harea, hsum, rfl⟩
    show Real.sqrt (sqNorm (D - B)) = 8 * Real.sqrt 2
    simp only [Dist, QuadArea] at harea hsum
    rw [cross_sub_sub A C D] at harea
    set u := C - A with hu
    set p := B - A with hp
    set q := D - C with hq
    have sp0 : 0 ≤ sqNorm p := sqNorm_nonneg p
    have su0 : 0 ≤ sqNorm u := sqNorm_nonneg u
    have sq0 : 0 ≤ sqNorm q := sqNorm_nonneg q
    -- The two triangle-area bounds and the AM–GM bound are both tight.
    have cb1 : |cross p u| ≤ Real.sqrt (sqNorm p) * Real.sqrt (sqNorm u) :=
      abs_cross_le p u
    have cb2 : |cross u q| ≤ Real.sqrt (sqNorm u) * Real.sqrt (sqNorm q) :=
      abs_cross_le u q
    have h64 : |cross p u| + |cross u q| = 64 := by linarith only [harea]
    have hsum' : Real.sqrt (sqNorm u) + (Real.sqrt (sqNorm p) + Real.sqrt (sqNorm q)) = 16 := by
      linarith only [hsum]
    have heq : Real.sqrt (sqNorm u) * (Real.sqrt (sqNorm p) + Real.sqrt (sqNorm q)) =
        Real.sqrt (sqNorm p) * Real.sqrt (sqNorm u) +
          Real.sqrt (sqNorm u) * Real.sqrt (sqNorm q) := by ring
    have key64 : Real.sqrt (sqNorm u) * (Real.sqrt (sqNorm p) + Real.sqrt (sqNorm q)) = 64 := by
      apply le_antisymm
      · have h1 : (Real.sqrt (sqNorm u) + (Real.sqrt (sqNorm p) + Real.sqrt (sqNorm q))) ^ 2
            = 256 := by
          rw [hsum']
          norm_num
        have h2 : 0 ≤ (Real.sqrt (sqNorm u) - (Real.sqrt (sqNorm p) + Real.sqrt (sqNorm q))) ^ 2 :=
          sq_nonneg _
        nlinarith only [h1, h2]
      · linarith only [h64, cb1, cb2, heq]
    have e_cross1 : |cross p u| = Real.sqrt (sqNorm p) * Real.sqrt (sqNorm u) := by
      linarith only [h64, cb1, cb2, key64, heq]
    have e_cross2 : |cross u q| = Real.sqrt (sqNorm u) * Real.sqrt (sqNorm q) := by
      linarith only [h64, cb1, cb2, key64, heq]
    -- Equality in AM–GM forces `AC = AB + CD = 8`.
    have eq_amgm : Real.sqrt (sqNorm u) = Real.sqrt (sqNorm p) + Real.sqrt (sqNorm q) := by
      have h1 : (Real.sqrt (sqNorm u) + (Real.sqrt (sqNorm p) + Real.sqrt (sqNorm q))) ^ 2
          = 256 := by
        rw [hsum']
        norm_num
      have hz : (Real.sqrt (sqNorm u) - (Real.sqrt (sqNorm p) + Real.sqrt (sqNorm q))) ^ 2 = 0 := by
        linear_combination h1 - 4 * key64
      have h0 := sq_eq_zero_iff.mp hz
      linarith only [h0]
    have valu : Real.sqrt (sqNorm u) = 8 := by linarith only [eq_amgm, hsum']
    have vals : Real.sqrt (sqNorm p) + Real.sqrt (sqNorm q) = 8 := by
      linarith only [eq_amgm, hsum']
    have hsu : sqNorm u = 64 := by
      have h : sqNorm u = Real.sqrt (sqNorm u) ^ 2 := (Real.sq_sqrt su0).symm
      rw [valu] at h
      norm_num at h
      exact h
    have hsu_ne : sqNorm u ≠ 0 := by
      rw [hsu]
      norm_num
    -- Equality in the area bounds forces both sides to be perpendicular to `AC`.
    have hip1 : ip p u = 0 := ip_eq_zero_of_abs_cross_eq e_cross1
    have hip2 : ip u q = 0 := ip_eq_zero_of_abs_cross_eq e_cross2
    have hip1' : ip u p = 0 := by
      rw [ip_comm]
      exact hip1
    -- Convexity: `B` and `D` lie on opposite sides of the diagonal `AC`.
    have hsign : cross u p * cross u q < 0 := by
      have t1 : cross u p = -cross (B - A) (C - B) := by
        rw [hu, hp]
        exact cross_turn1 A B C
      have t3 : cross u q = cross (D - C) (A - D) := by
        rw [hu, hq]
        exact cross_turn3 A B C D
      simp only [ConvexQuad] at hconv
      rcases hconv with ⟨g1, _, g3, _⟩ | ⟨g1, _, g3, _⟩
      · exact mul_neg_of_neg_of_pos (by linarith only [t1, g1]) (by linarith only [t3, g3])
      · exact mul_neg_of_pos_of_neg (by linarith only [t1, g1]) (by linarith only [t3, g3])
    -- The two perpendicular sides are anti-parallel: `ip p q = -(AB * CD)`.
    have hcpq : cross p q = 0 := cross_eq_zero_of_ip_eq_zero hip1' hip2 hsu_ne
    have hipq_neg : ip p q < 0 := by
      have hid := ip_mul_sqNorm u p q
      rw [hip1', hip2, hsu] at hid
      simp only [mul_zero, zero_add] at hid
      linarith only [hid, hsign]
    have hipq_abs : |ip p q| = Real.sqrt (sqNorm p) * Real.sqrt (sqNorm q) := by
      have hl := lagrange p q
      rw [hcpq, zero_pow two_ne_zero, zero_add] at hl
      have h2 : ip p q ^ 2 = (Real.sqrt (sqNorm p) * Real.sqrt (sqNorm q)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt sp0, Real.sq_sqrt sq0]
        exact hl
      have h3 := (sq_eq_sq_iff_abs_eq_abs _ _).mp h2
      rwa [abs_of_nonneg (show (0 : ℝ) ≤ Real.sqrt (sqNorm p) * Real.sqrt (sqNorm q) by positivity)]
        at h3
    have hipq : ip p q = -(Real.sqrt (sqNorm p) * Real.sqrt (sqNorm q)) := by
      rw [abs_of_neg hipq_neg] at hipq_abs
      linarith only [hipq_abs]
    -- The other diagonal: `BD² = AC² + (AB + CD)² = 128`.
    have hDB : D - B = u - p + q := by
      funext i
      fin_cases i <;> simp only [hu, hp, hq, Pi.sub_apply, Pi.add_apply] <;> ring
    have hfin : sqNorm (D - B) = 128 := by
      rw [hDB, sqNorm_sub_add, hsu, hip1', hip2, hipq]
      have h2 : (Real.sqrt (sqNorm p) + Real.sqrt (sqNorm q)) ^ 2 =
          sqNorm p + sqNorm q + 2 * (Real.sqrt (sqNorm p) * Real.sqrt (sqNorm q)) := by
        rw [add_sq, Real.sq_sqrt sp0, Real.sq_sqrt sq0]
        ring
      rw [vals] at h2
      norm_num at h2
      linarith only [h2]
    rw [hfin]
    exact sqrt_128
  · -- The value `8 * √2` is attained by an explicit quadrangle.
    intro hd
    subst hd
    refine ⟨![0, 0], ![0, 4], ![8, 0], ![8, -4], ?_, ?_, ?_, ?_⟩
    · simp only [ConvexQuad]
      right
      refine ⟨?_, ?_, ?_, ?_⟩ <;> coord
    · norm_num [QuadArea, cross, Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    · have hAB : Dist (![0, 0] : Point) ![0, 4] = 4 := by
        have e : sqNorm ((![0, 4] : Point) - ![0, 0]) = 16 := by coord
        simp only [Dist]
        rw [e, show (16 : ℝ) = 4 ^ 2 by norm_num,
          Real.sqrt_sq (show (0 : ℝ) ≤ 4 by norm_num)]
      have hCD : Dist (![8, 0] : Point) ![8, -4] = 4 := by
        have e : sqNorm ((![8, -4] : Point) - ![8, 0]) = 16 := by coord
        simp only [Dist]
        rw [e, show (16 : ℝ) = 4 ^ 2 by norm_num,
          Real.sqrt_sq (show (0 : ℝ) ≤ 4 by norm_num)]
      have hAC : Dist (![0, 0] : Point) ![8, 0] = 8 := by
        have e : sqNorm ((![8, 0] : Point) - ![0, 0]) = 64 := by coord
        simp only [Dist]
        rw [e, show (64 : ℝ) = 8 ^ 2 by norm_num,
          Real.sqrt_sq (show (0 : ℝ) ≤ 8 by norm_num)]
      calc Dist (![0, 0] : Point) ![0, 4] + Dist (![8, 0] : Point) ![8, -4] +
              Dist (![0, 0] : Point) ![8, 0]
          = 4 + 4 + 8 := by rw [hAB, hCD, hAC]
        _ = 16 := by norm_num
    · have e : sqNorm ((![8, -4] : Point) - ![0, 4]) = 128 := by coord
      show (8 * Real.sqrt 2 : ℝ) = Real.sqrt (sqNorm ((![8, -4] : Point) - ![0, 4]))
      rw [e]
      exact sqrt_128.symm

end Imo1976P1
