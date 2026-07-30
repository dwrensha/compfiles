/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 1995, Problem 1

Let A, B, C, D be four distinct points on a line, in that order. The circles
with diameters AC and BD intersect at X and Y. The line XY meets BC at Z.
Let P be a point on the line XY other than Z. The line CP intersects the
circle with diameter AC at C and M, and the line BP intersects the circle
with diameter BD at B and N. Prove that the lines AM, DN, XY are concurrent.
-/

namespace Imo1995P1

open scoped Affine RealInnerProductSpace

/-- The Euclidean plane. -/
abbrev Pt := EuclideanSpace ℝ (Fin 2)

/- The statement of the problem is invariant under rigid motions of the
plane, so we may place the common line of `A, B, C, D` on the `x`-axis:
`A = (a, 0)`, `B = (b, 0)`, `C = (c, 0)`, `D = (d, 0)` with `a < b < c < d`.
A point `W` lies on the circle with diameter `UV` iff `⟪W -ᵥ U, W -ᵥ V⟫ = 0`
(Thales); subtracting the two circle equations for `X` (and for `Y`) shows
that `X` and `Y` both have first coordinate
`z = (b*d - a*c)/(b + d - a - c)`, so the line `XY` is the vertical line
`x = z`, whence `Z = (z, 0)` and `P = (z, p)` with `p ≠ 0`.  Writing
`M = (m₀, m₁)`, the line and circle conditions reduce to
`p*m₁ = (c - z)*(m₀ - a)`, and similarly `p*n₁ = (d - n₀)*(z - b)` for
`N = (n₀, n₁)`.  One then checks directly that the point
`Q = (z, (z - a)*(c - z)/p)` lies on `AM`, on `DN` — this uses
`(z - a)*(c - z) = (d - z)*(z - b)`, which is exactly the defining equation
of `z` (the equality of the powers of `Z` with respect to the two circles) —
and on `XY`. -/

snip begin

theorem Pt.ext {x y : Pt} (h0 : x 0 = y 0) (h1 : x 1 = y 1) : x = y := by
  apply WithLp.ofLp_injective (p := 2)
  funext i
  fin_cases i <;> assumption

lemma inner_pt (n x : Pt) : ⟪n, x⟫ = n 0 * x 0 + n 1 * x 1 := by
  rw [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, RCLike.inner_apply]
  simp only [conj_trivial]
  ring

/-- Coordinates of a point on the line through `U` and `V`. -/
lemma lineMap_coord (U V : Pt) (s : ℝ) (i : Fin 2) :
    (AffineMap.lineMap U V s) i = s * (V i - U i) + U i := by
  rw [AffineMap.lineMap_apply]
  simp only [vsub_eq_sub, vadd_eq_add, PiLp.add_apply, PiLp.smul_apply,
    PiLp.sub_apply, smul_eq_mul]

/-- Membership in the line through two distinct points of the plane, as a
determinant (cross product) equation. -/
lemma mem_line_iff {U V W : Pt} (hUV : U ≠ V) :
    W ∈ line[ℝ, U, V] ↔
      (W 0 - U 0) * (V 1 - U 1) = (W 1 - U 1) * (V 0 - U 0) := by
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
  constructor
  · rintro ⟨s, rfl⟩
    rw [lineMap_coord, lineMap_coord]
    ring
  · intro h
    by_cases h0 : V 0 - U 0 = 0
    · -- The line is vertical: parametrize by the second coordinate.
      have h1 : V 1 - U 1 ≠ 0 := by
        intro h1'
        exact hUV (Pt.ext (sub_eq_zero.mp h0).symm (sub_eq_zero.mp h1').symm)
      have hW0 : W 0 - U 0 = 0 := by
        rw [h0] at h
        have hh : (W 0 - U 0) * (V 1 - U 1) = 0 := by linear_combination h
        exact (mul_eq_zero.mp hh).resolve_right h1
      refine ⟨(W 1 - U 1) / (V 1 - U 1), Pt.ext ?_ ?_⟩
      · rw [lineMap_coord, h0, sub_eq_zero.mp hW0]
        ring
      · rw [lineMap_coord, div_mul_cancel₀ _ h1]
        ring
    · refine ⟨(W 0 - U 0) / (V 0 - U 0), Pt.ext ?_ ?_⟩
      · rw [lineMap_coord, div_mul_cancel₀ _ h0]
        ring
      · rw [lineMap_coord]
        have h3 : (W 0 - U 0) / (V 0 - U 0) * (V 1 - U 1) = W 1 - U 1 := by
          rw [div_mul_eq_mul_div, div_eq_iff h0]
          exact h
        rw [h3]
        ring

/-- The Thales equation in coordinates: a point `W` lies on the circle with
diameter `UV`, where `U = (u, 0)` and `V = (v, 0)`, iff
`(W 0 - u)*(W 0 - v) + (W 1)^2 = 0`. -/
lemma inner_circle {W U V : Pt} {u v : ℝ} (hU0 : U 0 = u) (hU1 : U 1 = 0)
    (hV0 : V 0 = v) (hV1 : V 1 = 0) (h : ⟪W -ᵥ U, W -ᵥ V⟫ = 0) :
    (W 0 - u) * (W 0 - v) + (W 1) ^ 2 = 0 := by
  rw [inner_pt] at h
  simp only [vsub_eq_sub, PiLp.sub_apply] at h
  rw [hU0, hU1, hV0, hV1] at h
  linear_combination h

snip end

problem imo1995_p1
    (a b c d : ℝ) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (A B C D X Y Z P M N : Pt)
    (hA : A = !₂[a, 0]) (hB : B = !₂[b, 0]) (hC : C = !₂[c, 0])
    (hD : D = !₂[d, 0])
    (hXAC : ⟪X -ᵥ A, X -ᵥ C⟫ = 0) (hXBD : ⟪X -ᵥ B, X -ᵥ D⟫ = 0)
    (hYAC : ⟪Y -ᵥ A, Y -ᵥ C⟫ = 0) (hYBD : ⟪Y -ᵥ B, Y -ᵥ D⟫ = 0)
    (hXY : X ≠ Y)
    (hZXY : Z ∈ line[ℝ, X, Y]) (hZBC : Z ∈ line[ℝ, B, C])
    (hPXY : P ∈ line[ℝ, X, Y]) (hPZ : P ≠ Z)
    (hMCP : M ∈ line[ℝ, C, P]) (hMAC : ⟪M -ᵥ A, M -ᵥ C⟫ = 0) (hMC : M ≠ C)
    (hNBP : N ∈ line[ℝ, B, P]) (hNBD : ⟪N -ᵥ B, N -ᵥ D⟫ = 0) (hNB : N ≠ B) :
    ∃ Q, Q ∈ line[ℝ, A, M] ∧ Q ∈ line[ℝ, D, N] ∧ Q ∈ line[ℝ, X, Y] := by
  -- Coordinate values of the base points.
  have hA0 : A 0 = a := by rw [hA]; simp
  have hA1 : A 1 = 0 := by rw [hA]; simp
  have hB0 : B 0 = b := by rw [hB]; simp
  have hB1 : B 1 = 0 := by rw [hB]; simp
  have hC0 : C 0 = c := by rw [hC]; simp
  have hC1 : C 1 = 0 := by rw [hC]; simp
  have hD0 : D 0 = d := by rw [hD]; simp
  have hD1 : D 1 = 0 := by rw [hD]; simp
  -- The denominator `b + d - a - c = (b - a) + (d - c)` is positive.
  have hden : (0 : ℝ) < b + d - a - c := by linarith
  have hden' : b + d - a - c ≠ 0 := ne_of_gt hden
  -- The first coordinate of the radical axis of the two circles.
  set z := (b * d - a * c) / (b + d - a - c) with hz_def
  have hz : (b + d - a - c) * z = b * d - a * c := by
    rw [hz_def]
    exact mul_div_cancel₀ _ hden'
  -- `X` and `Y` lie on the vertical line `x = z`.
  have hX0 : X 0 = z := by
    have h1 : (X 0 - a) * (X 0 - c) + (X 1) ^ 2 = 0 :=
      inner_circle hA0 hA1 hC0 hC1 hXAC
    have h2 : (X 0 - b) * (X 0 - d) + (X 1) ^ 2 = 0 :=
      inner_circle hB0 hB1 hD0 hD1 hXBD
    have h3 : (b + d - a - c) * X 0 = b * d - a * c := by
      linear_combination h1 - h2
    exact mul_left_cancel₀ hden' (by linear_combination h3 - hz)
  have hY0 : Y 0 = z := by
    have h1 : (Y 0 - a) * (Y 0 - c) + (Y 1) ^ 2 = 0 :=
      inner_circle hA0 hA1 hC0 hC1 hYAC
    have h2 : (Y 0 - b) * (Y 0 - d) + (Y 1) ^ 2 = 0 :=
      inner_circle hB0 hB1 hD0 hD1 hYBD
    have h3 : (b + d - a - c) * Y 0 = b * d - a * c := by
      linear_combination h1 - h2
    exact mul_left_cancel₀ hden' (by linear_combination h3 - hz)
  -- Since `X ≠ Y`, their second coordinates differ.
  have hY1X1 : Y 1 ≠ X 1 := fun h => hXY (Pt.ext (by rw [hX0, hY0]) h.symm)
  -- `z` lies strictly between `b` and `c`.
  have hcz : (0 : ℝ) < c - z := by
    have h1 : (0 : ℝ) < (b + d - a - c) * (c - z) := by
      have he : (b + d - a - c) * (c - z) = (d - c) * (c - b) := by
        linear_combination -hz
      rw [he]
      exact mul_pos (sub_pos.mpr hcd) (sub_pos.mpr hbc)
    exact pos_of_mul_pos_right h1 (le_of_lt hden)
  have hbz : (0 : ℝ) < z - b := by
    have h1 : (0 : ℝ) < (b + d - a - c) * (z - b) := by
      have he : (b + d - a - c) * (z - b) = (b - a) * (c - b) := by
        linear_combination hz
      rw [he]
      exact mul_pos (sub_pos.mpr hab) (sub_pos.mpr hbc)
    exact pos_of_mul_pos_right h1 (le_of_lt hden)
  have hzc : z - c ≠ 0 := sub_ne_zero.mpr (ne_of_lt (show z < c by linarith))
  have hzb : z - b ≠ 0 := sub_ne_zero.mpr (ne_of_gt (sub_pos.mp hbz))
  -- The key identity: the powers of `Z` with respect to the two circles
  -- agree (`AZ*CZ = BZ*DZ` in the classical solution).
  have hkey2 : (d - z) * (z - b) = (z - a) * (c - z) := by
    linear_combination hz
  -- `Z = (z, 0)` and `P = (z, p)` with `p ≠ 0`.
  have hBC : B ≠ C := by
    intro h
    have h2 : B 0 = C 0 := by rw [h]
    rw [hB0, hC0] at h2
    exact (ne_of_lt hbc) h2
  have hZ1 : Z 1 = 0 := by
    have h := (mem_line_iff hBC).mp hZBC
    rw [hB0, hB1, hC0, hC1] at h
    have h1 : Z 1 * (c - b) = 0 := by linear_combination -h
    exact (mul_eq_zero.mp h1).resolve_right
      (sub_ne_zero.mpr (ne_of_gt hbc))
  have hZ0 : Z 0 = z := by
    have h := (mem_line_iff hXY).mp hZXY
    rw [hX0, hY0] at h
    have h1 : (Z 0 - z) * (Y 1 - X 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h1 with h2 | h2
    · linear_combination h2
    · exact absurd h2 (sub_ne_zero.mpr hY1X1)
  have hP0 : P 0 = z := by
    have h := (mem_line_iff hXY).mp hPXY
    rw [hX0, hY0] at h
    have h1 : (P 0 - z) * (Y 1 - X 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h1 with h2 | h2
    · linear_combination h2
    · exact absurd h2 (sub_ne_zero.mpr hY1X1)
  have hp : P 1 ≠ 0 := by
    intro hp1
    exact hPZ (Pt.ext (by rw [hP0, hZ0]) (by rw [hp1, hZ1]))
  -- The line conditions on `M` and `N` in coordinates.
  have hCP : C ≠ P := by
    intro h
    have h2 : C 0 = P 0 := by rw [h]
    rw [hC0, hP0] at h2
    exact (ne_of_gt (sub_pos.mp hcz)) h2
  have hBP : B ≠ P := by
    intro h
    have h2 : B 0 = P 0 := by rw [h]
    rw [hB0, hP0] at h2
    exact (ne_of_lt (show b < z by linarith)) h2
  have hMline : (M 0 - c) * P 1 = M 1 * (z - c) := by
    have h := (mem_line_iff hCP).mp hMCP
    rw [hC0, hC1, hP0] at h
    linear_combination h
  have hNline : (N 0 - b) * P 1 = N 1 * (z - b) := by
    have h := (mem_line_iff hBP).mp hNBP
    rw [hB0, hB1, hP0] at h
    linear_combination h
  have hMcirc : (M 0 - a) * (M 0 - c) + (M 1) ^ 2 = 0 :=
    inner_circle hA0 hA1 hC0 hC1 hMAC
  have hNcirc : (N 0 - b) * (N 0 - d) + (N 1) ^ 2 = 0 :=
    inner_circle hB0 hB1 hD0 hD1 hNBD
  -- `M ≠ C` and `N ≠ B` give `M 0 ≠ c` and `N 0 ≠ b`.
  have hm0 : M 0 ≠ c := by
    intro hm0
    apply hMC
    apply Pt.ext (by rw [hm0, hC0])
    have h1 : M 1 * (z - c) = 0 := by rw [← hMline, hm0]; ring
    rcases mul_eq_zero.mp h1 with h2 | h2
    · rw [hC1]; exact h2
    · exact absurd h2 hzc
  have hn0 : N 0 ≠ b := by
    intro hn0
    apply hNB
    apply Pt.ext (by rw [hn0, hB0])
    have h1 : N 1 * (z - b) = 0 := by rw [← hNline, hn0]; ring
    rcases mul_eq_zero.mp h1 with h2 | h2
    · rw [hB1]; exact h2
    · exact absurd h2 hzb
  -- The directions of `AM` and of `DN`.
  have hkeyM : P 1 * M 1 = (c - z) * (M 0 - a) := by
    have hstep : (M 0 - a) * (z - c) ^ 2 + (M 0 - c) * (P 1) ^ 2 = 0 := by
      have h1 : (M 0 - c) *
          ((M 0 - a) * (z - c) ^ 2 + (M 0 - c) * (P 1) ^ 2) = 0 := by
        linear_combination (z - c) ^ 2 * hMcirc +
          ((M 0 - c) * P 1 + M 1 * (z - c)) * hMline
      exact (mul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr hm0)
    have h2 : P 1 * M 1 * (z - c) = (c - z) * (M 0 - a) * (z - c) := by
      linear_combination -P 1 * hMline + hstep
    exact mul_right_cancel₀ hzc h2
  have hkeyN : P 1 * N 1 = (d - N 0) * (z - b) := by
    have hstep : (N 0 - d) * (z - b) ^ 2 + (N 0 - b) * (P 1) ^ 2 = 0 := by
      have h1 : (N 0 - b) *
          ((N 0 - d) * (z - b) ^ 2 + (N 0 - b) * (P 1) ^ 2) = 0 := by
        linear_combination (z - b) ^ 2 * hNcirc +
          ((N 0 - b) * P 1 + N 1 * (z - b)) * hNline
      exact (mul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr hn0)
    have h2 : P 1 * N 1 * (z - b) = (d - N 0) * (z - b) * (z - b) := by
      linear_combination -P 1 * hNline + hstep
    exact mul_right_cancel₀ hzb h2
  -- `A ≠ M` and `D ≠ N`, so the lines `AM` and `DN` are well defined.
  have hAM : A ≠ M := by
    intro hAM
    have hm0' : M 0 = a := by rw [← hAM, hA0]
    have hm1' : M 1 = 0 := by rw [← hAM, hA1]
    have h := hMline
    rw [hm0', hm1'] at h
    have h1 : (a - c) * P 1 = 0 := by linear_combination h
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact (ne_of_lt (show a < c by linarith)) (by linarith)
    · exact hp h2
  have hDN : D ≠ N := by
    intro hDN
    have hn0' : N 0 = d := by rw [← hDN, hD0]
    have hn1' : N 1 = 0 := by rw [← hDN, hD1]
    have h := hNline
    rw [hn0', hn1'] at h
    have h1 : (d - b) * P 1 = 0 := by linear_combination h
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact (ne_of_gt (show d > b by linarith)) (by linarith)
    · exact hp h2
  -- The common point `Q = (z, (z - a)*(c - z)/p)` of `AM`, `DN` and `XY`.
  refine ⟨!₂[z, (z - a) * (c - z) / P 1], ?_, ?_, ?_⟩
  · -- `Q ∈ AM`.
    rw [mem_line_iff hAM]
    have hQ0 : (!₂[z, (z - a) * (c - z) / P 1] : Pt) 0 = z := by simp
    have hQ1 : (!₂[z, (z - a) * (c - z) / P 1] : Pt) 1 =
        (z - a) * (c - z) / P 1 := by simp
    rw [hQ0, hQ1, hA0, hA1]
    field_simp [hp]
    linear_combination (z - a) * hkeyM
  · -- `Q ∈ DN`.
    rw [mem_line_iff hDN]
    have hQ0 : (!₂[z, (z - a) * (c - z) / P 1] : Pt) 0 = z := by simp
    have hQ1 : (!₂[z, (z - a) * (c - z) / P 1] : Pt) 1 =
        (z - a) * (c - z) / P 1 := by simp
    rw [hQ0, hQ1, hD0, hD1]
    field_simp [hp]
    linear_combination (z - d) * hkeyN + (N 0 - d) * hkey2
  · -- `Q ∈ XY`.
    rw [mem_line_iff hXY]
    have hQ0 : (!₂[z, (z - a) * (c - z) / P 1] : Pt) 0 = z := by simp
    have hQ1 : (!₂[z, (z - a) * (c - z) / P 1] : Pt) 1 =
        (z - a) * (c - z) / P 1 := by simp
    rw [hQ0, hQ1, hX0, hY0]
    ring

end Imo1995P1
