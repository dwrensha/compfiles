/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Real.Sqrt
public import ProblemExtraction

@[expose] public section

problem_file {
  tags := [.Geometry]
}

/-!
# International Mathematical Olympiad 1992, Problem 4

In the plane, let C be a circle, L a line tangent to C, and M a point on L.
Find the locus of all points P such that there exist points Q and R on L,
equidistant from M, with C the incircle of the triangle PQR.

# Answer

Let X be the point where C touches L, let O be the centre of C, let the
diameter through X meet C again at Z, and let Y be the point of L such that
M is the midpoint of XY. The locus is the open ray from Z along the line YZ
on the opposite side of Z from Y, i.e. the set of points Z + t • (Z - Y)
with 0 < t.

We prove this in Cartesian coordinates: by a rigid motion we may assume that
L is the x-axis, that C touches L at the origin X = (0, 0), that the centre
of C is O = (0, r) with 0 < r (so Z = (0, 2r)), and that M = (m, 0); then
Y = (2m, 0) and the locus is { (2m(1 - t), 2rt) | 1 < t }.
Since Q ≠ R are equidistant from M, M is the midpoint of QR.
-/

namespace Imo1992P4

/-- The Euclidean plane. -/
abbrev Pl := EuclideanSpace ℝ (Fin 2)

/-- The 2D determinant (twice a signed area); its sign tells on which side of
the line through `a` (direction `a`) the point lies. -/
noncomputable def det2 (a b : Pl) : ℝ := a 0 * b 1 - a 1 * b 0

/-- The distance from the point `O` to the line through `A` and `B`
(degenerate, i.e. defined by the formula below, when `A = B`). -/
noncomputable def distLine (O A B : Pl) : ℝ := |det2 (B - A) (O - A)| / dist A B

/-- `O` lies strictly inside the triangle `PQR`: it is on the same side of
each side line as the opposite vertex. -/
def InsideTriangle (O P Q R : Pl) : Prop :=
  0 < det2 (P - Q) (O - Q) * det2 (P - Q) (R - Q) ∧
  0 < det2 (Q - R) (O - R) * det2 (Q - R) (P - R) ∧
  0 < det2 (R - P) (O - P) * det2 (R - P) (Q - P)

/-- The circle with centre `O` and radius `r` is the incircle of the triangle
`PQR`: its centre lies inside the triangle and all three side lines are at
distance `r` from it. -/
def IsIncircle (O : Pl) (r : ℝ) (P Q R : Pl) : Prop :=
  InsideTriangle O P Q R ∧
  distLine O P Q = r ∧ distLine O Q R = r ∧ distLine O R P = r

/-- The answer: the open ray from `Z = (0, 2r)` along the line `YZ` on the
opposite side of `Z` from `Y = (2m, 0)`. -/
determine locus (m r : ℝ) : Set Pl :=
  {P | ∃ t : ℝ, 1 < t ∧ P = !₂[2 * m * (1 - t), 2 * r * t]}

snip begin

/-
## Solution

Write `P = (A, B)`, `Q = (q, 0)`, `R = (s, 0)` and `O = (0, r)`.

For the forward direction, squaring the two equations
`distLine O P Q = r` and `distLine O R P = r` and simplifying using `B ≠ 0`
gives `q²(B - 2r) + 2qrA - r²B = 0` and `s²(B - 2r) + 2srA - r²B = 0`.
Subtracting (and using `q ≠ s`, `q + s = 2m`) yields `rA + mB = 2mr`, i.e.
`P` lies on the line `YZ`.  Substituting back gives `(B - 2r)qs = -r²B`.
The interiority conditions give `(B(m - q) - rs)(rq - B(m - s)) > 0`, which
simplifies to `B(2r - B)(qs - m²) > r²qs`; together with
`(B - 2r)qs = -r²B` this forces `2r < B`, so `P = (2m(1 - t), 2rt)` with
`t = B / (2r) > 1`.

For the converse, given `t > 1`, set `c = m² + r²t / (t - 1)`,
`u = √c - m`, `v = √c + m` and `w = (t - 1)(u + v)`.  Then `Q = (-u, 0)` and
`R = (v, 0)` are equidistant from `M = (m, 0)`, and with
`P = (2m(1 - t), 2rt)` all the incircle conditions reduce to the polynomial
identities `v - u = 2m` and `uv(t - 1) = r²t`.
-/

/-- The distance condition `distLine O P Q = r`, squared and simplified to a
polynomial equation (for `Q` on the `x`-axis and `P` above it). -/
lemma eq_of_distLine_left (r A B q : ℝ) (hB : 0 < B)
    (d : distLine (!₂[0, r] : Pl) (!₂[A, B]) (!₂[q, 0]) = r) :
    q ^ 2 * (B - 2 * r) + 2 * q * r * A - r ^ 2 * B = 0 := by
  have hd7 : det2 (!₂[q, 0] - !₂[A, B] : Pl) (!₂[0, r] - !₂[A, B]) = q * r - q * B - A * r := by
    simp only [det2, PiLp.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue]; ring
  have hdistPQ : dist (!₂[A, B] : Pl) (!₂[q, 0]) = √((A - q) ^ 2 + B ^ 2) := by
    rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
    simp [Real.dist_eq, sq_abs]
  unfold distLine at d
  rw [hd7, hdistPQ] at d
  have hX1 : 0 < (A - q) ^ 2 + B ^ 2 := by
    have h1 : 0 ≤ (A - q) ^ 2 := sq_nonneg _
    have h2 : 0 < B ^ 2 := pow_pos hB 2
    linarith
  have habs1 : |q * r - q * B - A * r| = r * √((A - q) ^ 2 + B ^ 2) := by
    have h1 : √((A - q) ^ 2 + B ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hX1).ne'
    rwa [div_eq_iff h1] at d
  have hsq1 : (q * r - q * B - A * r) ^ 2 = r ^ 2 * ((A - q) ^ 2 + B ^ 2) := by
    have h1 : |q * r - q * B - A * r| ^ 2 = (r * √((A - q) ^ 2 + B ^ 2)) ^ 2 := by rw [habs1]
    rwa [sq_abs, mul_pow, Real.sq_sqrt hX1.le] at h1
  have hBne : B ≠ 0 := ne_of_gt hB
  have h1 : B * (q ^ 2 * (B - 2 * r) + 2 * q * r * A - r ^ 2 * B) = 0 := by
    linear_combination hsq1
  rcases mul_eq_zero.mp h1 with h | h
  · exact absurd h hBne
  · exact h

/-- The distance condition `distLine O R P = r`, squared and simplified to a
polynomial equation (for `R` on the `x`-axis and `P` above it). -/
lemma eq_of_distLine_right (r A B s : ℝ) (hB : 0 < B)
    (d : distLine (!₂[0, r] : Pl) (!₂[s, 0]) (!₂[A, B]) = r) :
    s ^ 2 * (B - 2 * r) + 2 * s * r * A - r ^ 2 * B = 0 := by
  have hd9 : det2 (!₂[A, B] - !₂[s, 0] : Pl) (!₂[0, r] - !₂[s, 0]) = A * r - s * r + B * s := by
    simp only [det2, PiLp.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue]; ring
  have hdistRP : dist (!₂[s, 0] : Pl) (!₂[A, B]) = √((s - A) ^ 2 + B ^ 2) := by
    rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
    simp [Real.dist_eq, sq_abs]
  unfold distLine at d
  rw [hd9, hdistRP] at d
  have hX3 : 0 < (s - A) ^ 2 + B ^ 2 := by
    have h1 : 0 ≤ (s - A) ^ 2 := sq_nonneg _
    have h2 : 0 < B ^ 2 := pow_pos hB 2
    linarith
  have habs3 : |A * r - s * r + B * s| = r * √((s - A) ^ 2 + B ^ 2) := by
    have h1 : √((s - A) ^ 2 + B ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hX3).ne'
    rwa [div_eq_iff h1] at d
  have hsq3 : (A * r - s * r + B * s) ^ 2 = r ^ 2 * ((s - A) ^ 2 + B ^ 2) := by
    have h1 : |A * r - s * r + B * s| ^ 2 = (r * √((s - A) ^ 2 + B ^ 2)) ^ 2 := by rw [habs3]
    rwa [sq_abs, mul_pow, Real.sq_sqrt hX3.le] at h1
  have hBne : B ≠ 0 := ne_of_gt hB
  have h1 : B * (s ^ 2 * (B - 2 * r) + 2 * s * r * A - r ^ 2 * B) = 0 := by
    linear_combination hsq3
  rcases mul_eq_zero.mp h1 with h | h
  · exact absurd h hBne
  · exact h

/-- The key relations extracted from the incircle condition: `P` lies above
the `x`-axis and on the line `YZ`, and `(B - 2r)qs = -r²B`. -/
lemma forward_keys (r m A B q s : ℝ) (hr : 0 < r) (hqs : q ≠ s) (hmid : q + s = 2 * m)
    (hinc : IsIncircle (!₂[0, r] : Pl) r (!₂[A, B]) (!₂[q, 0]) (!₂[s, 0])) :
    0 < B ∧ 0 < ((A - q) * r + B * q) * (-B * (s - q)) ∧
      0 < (s * r - s * B - A * r) * (-B * (s - q)) ∧
      r * A + m * B = 2 * m * r ∧ (B - 2 * r) * (q * s) = -r ^ 2 * B := by
  unfold IsIncircle InsideTriangle at hinc
  rcases hinc with ⟨⟨i1, i2, i3⟩, d1, -, d3⟩
  have hd1 : det2 (!₂[A, B] - !₂[q, 0] : Pl) (!₂[0, r] - !₂[q, 0]) = (A - q) * r + B * q := by
    simp only [det2, PiLp.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue]; ring
  have hd2 : det2 (!₂[A, B] - !₂[q, 0] : Pl) (!₂[s, 0] - !₂[q, 0]) = -B * (s - q) := by
    simp only [det2, PiLp.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue]; ring
  have hd3 : det2 (!₂[q, 0] - !₂[s, 0] : Pl) (!₂[0, r] - !₂[s, 0]) = (q - s) * r := by
    simp only [det2, PiLp.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue]; ring
  have hd4 : det2 (!₂[q, 0] - !₂[s, 0] : Pl) (!₂[A, B] - !₂[s, 0]) = (q - s) * B := by
    simp only [det2, PiLp.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue]; ring
  have hd5 : det2 (!₂[s, 0] - !₂[A, B] : Pl) (!₂[0, r] - !₂[A, B]) = s * r - s * B - A * r := by
    simp only [det2, PiLp.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue]; ring
  have hd6 : det2 (!₂[s, 0] - !₂[A, B] : Pl) (!₂[q, 0] - !₂[A, B]) = B * (q - s) := by
    simp only [det2, PiLp.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue]; ring
  rw [hd1, hd2] at i1
  rw [hd3, hd4] at i2
  rw [hd5, hd6] at i3
  -- `P` lies above the `x`-axis.
  have hB : 0 < B := by
    by_contra hBn
    push Not at hBn
    nlinarith [i2, mul_nonneg (sq_nonneg (q - s)) (mul_nonneg hr.le (neg_nonneg.mpr hBn))]
  -- The two distance equations, squared.
  have hE1 : q ^ 2 * (B - 2 * r) + 2 * q * r * A - r ^ 2 * B = 0 :=
    eq_of_distLine_left r A B q hB d1
  have hE2 : s ^ 2 * (B - 2 * r) + 2 * s * r * A - r ^ 2 * B = 0 :=
    eq_of_distLine_right r A B s hB d3
  -- Key relations: `P` is on the line `YZ`, and `(B - 2r)qs = -r²B`.
  have hsub : (q - s) * ((q + s) * (B - 2 * r) + 2 * r * A) = 0 := by
    linear_combination hE1 - hE2
  have hqs2 : q - s ≠ 0 := sub_ne_zero.mpr hqs
  have hkey : (q + s) * (B - 2 * r) + 2 * r * A = 0 := by
    rcases mul_eq_zero.mp hsub with h | h
    · exact absurd h hqs2
    · exact h
  rw [hmid] at hkey
  have key1 : r * A + m * B = 2 * m * r := by linear_combination hkey / 2
  have hrA : r * A = 2 * m * r - m * B := by linear_combination key1
  have hs' : s = 2 * m - q := by linarith [hmid]
  have key2 : (B - 2 * r) * (q * s) = -r ^ 2 * B := by
    rw [hs']
    linear_combination -hE1 + 2 * q * hrA
  have h6' : B * (q - s) = -B * (s - q) := by ring
  rw [h6'] at i3
  exact ⟨hB, i1, i3, key1, key2⟩

/-- The product inequality coming from the interiority conditions. -/
lemma forward_hprod (r m A B q s : ℝ) (hmid : q + s = 2 * m)
    (i1 : 0 < ((A - q) * r + B * q) * (-B * (s - q)))
    (i3 : 0 < (s * r - s * B - A * r) * (-B * (s - q)))
    (key1 : r * A + m * B = 2 * m * r) :
    0 < B * (2 * r - B) * (q * s - m ^ 2) - r ^ 2 * (q * s) := by
  have hrA : r * A = 2 * m * r - m * B := by linear_combination key1
  have hs' : s = 2 * m - q := by linarith [hmid]
  have hpos : 0 < ((A - q) * r + B * q) * (s * r - s * B - A * r) := by
    have h4 : 0 < (((A - q) * r + B * q) * (-B * (s - q))) *
        ((s * r - s * B - A * r) * (-B * (s - q))) := mul_pos i1 i3
    have h5 : (((A - q) * r + B * q) * (-B * (s - q))) * ((s * r - s * B - A * r) * (-B * (s - q)))
        = (((A - q) * r + B * q) * (s * r - s * B - A * r)) * (-B * (s - q)) ^ 2 := by ring
    rw [h5] at h4
    exact pos_of_mul_pos_left h4 (sq_nonneg _)
  have huw : ((A - q) * r + B * q) * ((2 * m - q) * r - (2 * m - q) * B - A * r)
      = B * (2 * r - B) * (q * (2 * m - q) - m ^ 2) - r ^ 2 * (q * (2 * m - q)) := by
    linear_combination (-(r * A + (2 * m * r - m * B)) + ((2 * m - q) * (r - B) + q * r - B * q)) * hrA
  rw [hs'] at hpos
  rw [huw] at hpos
  rw [hs']
  exact hpos

/-- The inequality `2r < B`: the `y`-coordinate of `P` is above `Z`. -/
lemma forward_Bgt (r m B p : ℝ) (hr : 0 < r) (hB : 0 < B)
    (key2 : (B - 2 * r) * p = -r ^ 2 * B)
    (hprod : 0 < B * (2 * r - B) * (p - m ^ 2) - r ^ 2 * p) :
    2 * r < B := by
  by_contra hle
  push Not at hle
  rcases eq_or_lt_of_le hle with heq | hlt
  · rw [heq] at key2
    have h0 : (0 : ℝ) = -r ^ 2 * (2 * r) := by linear_combination key2
    nlinarith [h0, pow_pos hr 3]
  · have hX : 0 < 2 * r - B := by linarith
    have hp_pos : 0 < p := by
      have h1 : 0 < r ^ 2 * B := by positivity
      have h2 : p * (2 * r - B) = r ^ 2 * B := by linear_combination -key2
      rw [← h2] at h1
      exact pos_of_mul_pos_left h1 hX.le
    have hprod' : B * (2 * r - B) * (p - m ^ 2) > r ^ 2 * p := by linarith [hprod]
    have h3 : B ^ 2 * (p - m ^ 2) > p ^ 2 := by
      have h4 : B * (B * (2 * r - B) * (p - m ^ 2)) > B * (r ^ 2 * p) :=
        mul_lt_mul_of_pos_left hprod' hB
      have h5 : B * (r ^ 2 * p) = (2 * r - B) * p ^ 2 := by
        have h6 : r ^ 2 * B = p * (2 * r - B) := by linear_combination key2
        calc B * (r ^ 2 * p) = p * (r ^ 2 * B) := by ring
          _ = p * (p * (2 * r - B)) := by rw [h6]
          _ = (2 * r - B) * p ^ 2 := by ring
      have h7 : B * (B * (2 * r - B) * (p - m ^ 2)) = (2 * r - B) * (B ^ 2 * (p - m ^ 2)) := by
        ring
      rw [h7, h5] at h4
      exact lt_of_mul_lt_mul_left h4 hX.le
    have h9 : B ^ 2 > p := by
      have h10 : B ^ 2 * p > p ^ 2 := by
        have h11 : 0 ≤ B ^ 2 * m ^ 2 := mul_nonneg (sq_nonneg B) (sq_nonneg m)
        linarith [h3, h11]
      nlinarith [h10, hp_pos]
    have h12 : r ^ 2 * B = p * (2 * r - B) := by linear_combination key2
    nlinarith [h9, h12, hX, hB, hr, mul_pos (sub_pos.mpr h9) hX, mul_nonneg hB.le (sq_nonneg (B - r))]

/-- Forward direction: if the circle is the incircle of `PQR`, then `P` lies
on the claimed ray. -/
lemma forward (r m A B q s : ℝ) (hr : 0 < r) (hqs : q ≠ s) (hmid : q + s = 2 * m)
    (hinc : IsIncircle (!₂[0, r] : Pl) r (!₂[A, B]) (!₂[q, 0]) (!₂[s, 0])) :
    ∃ t : ℝ, 1 < t ∧ (!₂[A, B] : Pl) = !₂[2 * m * (1 - t), 2 * r * t] := by
  obtain ⟨hB, i1, i3, key1, key2⟩ := forward_keys r m A B q s hr hqs hmid hinc
  have hprod : 0 < B * (2 * r - B) * (q * s - m ^ 2) - r ^ 2 * (q * s) :=
    forward_hprod r m A B q s hmid i1 i3 key1
  have hB2r : 2 * r < B := forward_Bgt r m B (q * s) hr hB key2 hprod
  refine ⟨B / (2 * r), ?_, ?_⟩
  · rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * r)]
    linarith [hB2r]
  · have hrne : r ≠ 0 := ne_of_gt hr
    have h2rne : (2 : ℝ) * r ≠ 0 := by positivity
    have hA2 : A = (2 * m * r - m * B) / r := by
      rw [eq_div_iff hrne]
      linear_combination key1
    have htA : 2 * m * (1 - B / (2 * r)) = (2 * m * r - m * B) / r := by
      field_simp
    ext i
    fin_cases i
    · show A = 2 * m * (1 - B / (2 * r))
      rw [htA, hA2]
    · show B = 2 * r * (B / (2 * r))
      exact (mul_div_cancel₀ B h2rne).symm

/-- Reverse direction: every point of the ray is obtained. -/
lemma reverse (r m : ℝ) (hr : 0 < r) (t : ℝ) (ht : 1 < t) :
    ∃ Q R : Pl, Q 1 = 0 ∧ R 1 = 0 ∧ Q ≠ R ∧ midpoint ℝ Q R = (!₂[m, 0] : Pl) ∧
      IsIncircle (!₂[0, r] : Pl) r (!₂[2 * m * (1 - t), 2 * r * t]) Q R := by
  have ht0 : 0 < t := by linarith
  have ht1 : (0 : ℝ) < t - 1 := by linarith
  have ht1ne : t - 1 ≠ 0 := ne_of_gt ht1
  have hpos1 : 0 < r ^ 2 * t / (t - 1) := by positivity
  set A := 2 * m * (1 - t) with hA
  set B := 2 * r * t with hB
  have hBpos : 0 < B := by rw [hB]; positivity
  set sq := √(m ^ 2 + r ^ 2 * t / (t - 1)) with hsq
  have hsq2 : sq ^ 2 = m ^ 2 + r ^ 2 * t / (t - 1) := by
    rw [hsq]
    exact Real.sq_sqrt (by positivity)
  have hc' : m ^ 2 < m ^ 2 + r ^ 2 * t / (t - 1) := lt_add_of_pos_right _ hpos1
  have habs : |m| < sq := by
    rw [hsq, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_lt_sqrt (sq_nonneg m) hc'
  set u := sq - m with hu
  set v := sq + m with hv
  have hu0 : 0 < u := by rw [hu]; linarith [le_abs_self m, habs]
  have hv0 : 0 < v := by rw [hv]; linarith [neg_abs_le m, habs]
  have hR1 : v - u = 2 * m := by rw [hv, hu]; ring
  have huvpos : 0 < u + v := add_pos hu0 hv0
  have huvne : u + v ≠ 0 := ne_of_gt huvpos
  have hR2 : u * v * (t - 1) = r ^ 2 * t := by
    have h1 : u * v = sq ^ 2 - m ^ 2 := by rw [hu, hv]; ring
    rw [hsq2] at h1
    have h2 : u * v = r ^ 2 * t / (t - 1) := by rw [h1]; ring
    rw [h2]
    exact div_mul_cancel₀ _ ht1ne
  -- Auxiliary linear identities.
  have hu1 : (A + u) * r - B * u = -r * (u + (t - 1) * (u + v)) := by
    rw [hA, hB]; linear_combination r * (t - 1) * hR1
  have hw1 : det2 (!₂[v, 0] - !₂[A, B] : Pl) (!₂[0, r] - !₂[A, B])
      = -r * (v + (t - 1) * (u + v)) := by
    simp only [det2, PiLp.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue]
    rw [hA, hB]; linear_combination -r * (t - 1) * hR1
  have hwA : (t - 1) * (u + v) - A = 2 * v * (t - 1) := by
    rw [hA]; linear_combination -(t - 1) * hR1
  have h2uwA : 2 * u + (t - 1) * (u + v) + A = 2 * u * t := by
    rw [hA]; linear_combination (t - 1) * hR1
  have hwA3 : (t - 1) * (u + v) + A = 2 * u * (t - 1) := by
    rw [hA]; linear_combination (t - 1) * hR1
  have h2vwA : 2 * v + (t - 1) * (u + v) - A = 2 * v * t := by
    rw [hA]; linear_combination -(t - 1) * hR1
  -- The two "Pythagoras" identities (tangent lengths from `P`).
  have hPyth : (A + u) ^ 2 + B ^ 2 = (u + (t - 1) * (u + v)) ^ 2 := by
    have h1 : (u + (t - 1) * (u + v)) ^ 2 - (A + u) ^ 2
        = ((t - 1) * (u + v) - A) * (2 * u + (t - 1) * (u + v) + A) := by ring
    rw [hwA, h2uwA] at h1
    have h2 : 2 * v * (t - 1) * (2 * u * t) = B ^ 2 := by
      have h3 : 2 * v * (t - 1) * (2 * u * t) = 4 * t * (u * v * (t - 1)) := by ring
      rw [h3, hR2, hB]; ring
    linarith [h1, h2]
  have hPyth3 : (v - A) ^ 2 + B ^ 2 = (v + (t - 1) * (u + v)) ^ 2 := by
    have h1 : (v + (t - 1) * (u + v)) ^ 2 - (v - A) ^ 2
        = ((t - 1) * (u + v) + A) * (2 * v + (t - 1) * (u + v) - A) := by ring
    rw [hwA3, h2vwA] at h1
    have h2 : 2 * u * (t - 1) * (2 * v * t) = B ^ 2 := by
      have h3 : 2 * u * (t - 1) * (2 * v * t) = 4 * t * (u * v * (t - 1)) := by ring
      rw [h3, hR2, hB]; ring
    linarith [h1, h2]
  -- Distances.
  have hdistPQ : dist (!₂[A, B] : Pl) (!₂[-u, 0]) = u + (t - 1) * (u + v) := by
    rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
    simp [Real.dist_eq, sq_abs]
    rw [hPyth]
    exact Real.sqrt_sq (le_of_lt (by positivity))
  have hdistQR : dist (!₂[-u, 0] : Pl) (!₂[v, 0]) = u + v := by
    rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
    simp [Real.dist_eq, sq_abs]
    rw [show (-u - v) ^ 2 = (u + v) ^ 2 by ring]
    exact Real.sqrt_sq (le_of_lt huvpos)
  have hdistRP : dist (!₂[v, 0] : Pl) (!₂[A, B]) = v + (t - 1) * (u + v) := by
    rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
    simp [Real.dist_eq, sq_abs]
    rw [hPyth3]
    exact Real.sqrt_sq (le_of_lt (by positivity))
  -- Determinant computations.
  have hdet1 : det2 (!₂[-u, 0] - !₂[A, B] : Pl) (!₂[0, r] - !₂[A, B])
      = r * (u + (t - 1) * (u + v)) := by
    simp only [det2, PiLp.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue]
    linear_combination -hu1
  have hdet2 : det2 (!₂[v, 0] - !₂[-u, 0] : Pl) (!₂[0, r] - !₂[-u, 0]) = (u + v) * r := by
    simp only [det2, PiLp.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue]; ring
  have hdet3 : det2 (!₂[A, B] - !₂[v, 0] : Pl) (!₂[0, r] - !₂[v, 0])
      = r * (v + (t - 1) * (u + v)) := by
    simp only [det2, PiLp.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue]
    rw [hA, hB]; linear_combination r * (t - 1) * hR1
  have hdet_i1a : det2 (!₂[A, B] - !₂[-u, 0] : Pl) (!₂[0, r] - !₂[-u, 0])
      = -r * (u + (t - 1) * (u + v)) := by
    simp only [det2, PiLp.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue]
    linear_combination hu1
  have hdet_i1b : det2 (!₂[A, B] - !₂[-u, 0] : Pl) (!₂[v, 0] - !₂[-u, 0]) = -B * (u + v) := by
    simp only [det2, PiLp.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue]; ring
  have hdet_i2a : det2 (!₂[-u, 0] - !₂[v, 0] : Pl) (!₂[0, r] - !₂[v, 0]) = (-u - v) * r := by
    simp only [det2, PiLp.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue]; ring
  have hdet_i2b : det2 (!₂[-u, 0] - !₂[v, 0] : Pl) (!₂[A, B] - !₂[v, 0]) = (-u - v) * B := by
    simp only [det2, PiLp.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue]; ring
  have hdet_i3b : det2 (!₂[v, 0] - !₂[A, B] : Pl) (!₂[-u, 0] - !₂[A, B]) = -B * (u + v) := by
    simp only [det2, PiLp.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue]; ring
  -- Assemble everything.
  refine ⟨!₂[-u, 0], !₂[v, 0], by simp, by simp, ?_, ?_, ?_⟩
  · intro h
    have h2 := congrArg (· 0) h
    simp at h2
    linarith [huvpos]
  · rw [midpoint_eq_smul_add]
    ext i
    fin_cases i
    · simp [PiLp.add_apply, PiLp.smul_apply]
      linarith [hR1]
    · simp [PiLp.add_apply, PiLp.smul_apply]
  · unfold IsIncircle InsideTriangle distLine
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · rw [hdet_i1a, hdet_i1b]
      apply mul_pos_of_neg_of_neg
      · have h1 : 0 < r * (u + (t - 1) * (u + v)) := by positivity
        linarith
      · have h2 : 0 < B * (u + v) := by positivity
        linarith
    · rw [hdet_i2a, hdet_i2b]
      apply mul_pos_of_neg_of_neg
      · have h1 : 0 < (u + v) * r := by positivity
        linarith
      · have h2 : 0 < (u + v) * B := by positivity
        linarith
    · rw [hw1, hdet_i3b]
      apply mul_pos_of_neg_of_neg
      · have h1 : 0 < r * (v + (t - 1) * (u + v)) := by positivity
        linarith
      · have h2 : 0 < B * (u + v) := by positivity
        linarith
    · rw [hdet1, hdistPQ, abs_of_pos (by positivity : (0 : ℝ) < r * (u + (t - 1) * (u + v)))]
      rw [mul_comm r _]
      exact mul_div_cancel_left₀ _ (ne_of_gt (by positivity))
    · rw [hdet2, hdistQR, abs_of_pos (by positivity : (0 : ℝ) < (u + v) * r)]
      exact mul_div_cancel_left₀ _ huvne
    · rw [hdet3, hdistRP, abs_of_pos (by positivity : (0 : ℝ) < r * (v + (t - 1) * (u + v)))]
      rw [mul_comm r _]
      exact mul_div_cancel_left₀ _ (ne_of_gt (by positivity))

snip end

problem imo1992_p4 (r m : ℝ) (hr : 0 < r) :
    {P : Pl | ∃ Q R : Pl, Q 1 = 0 ∧ R 1 = 0 ∧ Q ≠ R ∧ midpoint ℝ Q R = (!₂[m, 0] : Pl) ∧
        IsIncircle (!₂[0, r] : Pl) r P Q R} = locus m r := by
  ext P
  simp only [locus, Set.mem_setOf_eq]
  constructor
  · rintro ⟨Q, R, hQ1, hR1, hQR, hmid, hinc⟩
    have hPe : P = !₂[P 0, P 1] := by ext i; fin_cases i <;> simp
    have hQe : Q = !₂[Q 0, 0] := by ext i; fin_cases i <;> simp [hQ1]
    have hRe : R = !₂[R 0, 0] := by ext i; fin_cases i <;> simp [hR1]
    have hqs : Q 0 ≠ R 0 := by
      intro h
      apply hQR
      rw [hQe, hRe, h]
    have hmid2 : Q 0 + R 0 = 2 * m := by
      rw [hQe, hRe, midpoint_eq_smul_add] at hmid
      have h2 := congrArg (· 0) hmid
      simp at h2
      linarith
    rw [hPe, hQe, hRe] at hinc
    obtain ⟨t, ht, hPt⟩ := forward r m (P 0) (P 1) (Q 0) (R 0) hr hqs hmid2 hinc
    rw [← hPe] at hPt
    exact ⟨t, ht, hPt⟩
  · rintro ⟨t, ht, hP⟩
    rw [hP]
    exact reverse r m hr t ht

end Imo1992P4
