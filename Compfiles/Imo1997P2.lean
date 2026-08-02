/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 1997, Problem 2

The angle at A is the smallest angle in the triangle ABC. The points B and C
divide the circumcircle of the triangle into two arcs. Let U be an interior
point of the arc between B and C which does not contain A. The perpendicular
bisectors of AB and AC meet the line AU at V and W, respectively. The lines
BV and CW meet at T. Show that AU = TB + TC.

## Formalization notes

We work in normalized coordinates: translate `A` to the origin and rotate the
plane so that the ray `AU` becomes the positive x-axis. Write
`U = (u, 0)`, `B = (xb, yb)`, `C = (xc, yc)`. The geometric hypotheses become:
* `0 < u`: `U ≠ A`.
* `0 < xb`, `0 < xc`: the angles `∠BAU` and `∠UAC` are acute, since they are
  smaller than `∠BAC`, the smallest angle of the triangle (so `∠BAC ≤ π/3`).
* `yb < 0`, `0 < yc`: `B` and `C` lie on opposite sides of the line `AU`,
  as `U` is an interior point of the arc `BC` not containing `A`.
* `hcirc`: `A`, `B`, `C`, `U` are concyclic; the equation says that the
  x-axis meets the circumcircle of `ABC` again exactly at the point `(u, 0)`.
* `hv`, `hw`: `V` and `W` lie between `A` and the point where the line `BC`
  crosses the line `AU`. This follows from `∠BAU < ∠ABC` and `∠UAC < ∠BCA`,
  which hold because `∠BAC` is the smallest angle of the triangle.

In these coordinates, the perpendicular bisector of `AB` meets the x-axis at
`V = ((xb² + yb²)/(2xb), 0)`, the perpendicular bisector of `AC` meets it at
`W = ((xc² + yc²)/(2xc), 0)`, and the intersection `T` of the lines `BV` and
`CW` is `B + s • (V - B)` for the explicit scalar `s` below. All distances
involved are rational functions of the coordinates, and the conclusion reduces
to a single polynomial identity modulo the concyclicity equation.
-/

namespace Imo1997P2

snip begin

/-- The algebraic heart of the proof: with the explicit choices of `s` and `t`
below, the concyclicity equation `hcirc` implies `s * v + t * w = u` (this is
the identity `AU = TB + TC` after dividing out the common length factors), and
the point `B + s • (V - B)` lies on the line `CW`, witnessed by the point
`C + t • (W - C)`, as checked one coordinate at a time. -/
theorem key_alg (u xb yb xc yc v w cr m s t : ℝ)
    (h2xb : (2 : ℝ) * xb ≠ 0) (h2xc : (2 : ℝ) * xc ≠ 0)
    (hcrn : cr ≠ 0) (hmn : m ≠ 0)
    (hv : v = (xb ^ 2 + yb ^ 2) / (2 * xb))
    (hw : w = (xc ^ 2 + yc ^ 2) / (2 * xc))
    (hcr : cr = xb * yc - xc * yb)
    (hmd : m = yc * v - yb * w - cr)
    (hs : s = (w * (yc - yb) - cr) / m)
    (ht : t = (v * (yc - yb) - cr) / m)
    (hcirc : u * cr = (xb ^ 2 + yb ^ 2) * yc - (xc ^ 2 + yc ^ 2) * yb) :
    s * v + t * w = u ∧
    xb + s * (v - xb) = xc + t * (w - xc) ∧
    yb + s * (0 - yb) = yc + t * (0 - yc) := by
  have es : s * m = w * (yc - yb) - cr := by rw [hs]; exact div_mul_cancel₀ _ hmn
  have et : t * m = v * (yc - yb) - cr := by rw [ht]; exact div_mul_cancel₀ _ hmn
  have hv' : 2 * xb * v = xb ^ 2 + yb ^ 2 := by
    rw [hv, ← mul_div_assoc]; exact mul_div_cancel_left₀ _ h2xb
  have hw' : 2 * xc * w = xc ^ 2 + yc ^ 2 := by
    rw [hw, ← mul_div_assoc]; exact mul_div_cancel_left₀ _ h2xc
  refine ⟨?_, ?_, ?_⟩
  · -- `s * v + t * w = u`: the identity `AU = TB + TC` modulo concyclicity,
    -- proved by cancelling the common factor `m * cr`.
    have hmcr : m * cr ≠ 0 := mul_ne_zero hmn hcrn
    have master : (s * v + t * w) * (m * cr) = u * (m * cr) := by
      have step : (s * v + t * w) * (m * cr) = (s * m) * v * cr + (t * m) * w * cr := by
        ring
      have step2 : u * (m * cr) = m * (u * cr) := by ring
      rw [step, step2, es, et, hcirc, hmd, hcr]
      refine mul_left_cancel₀ h2xb ?_
      linear_combination
        (-(2 * w * xb * yb * yc - 2 * w * xb * yc ^ 2 - 2 * w * xc * yb ^ 2 +
          2 * w * xc * yb * yc + 2 * xb ^ 2 * yc ^ 2 - 2 * xb * xc * yb * yc +
          xc ^ 2 * yb ^ 2 - xc ^ 2 * yb * yc + yb ^ 2 * yc ^ 2 - yb * yc ^ 3)) * hv'
        + (yb * (xb ^ 2 * yb + xb ^ 2 * yc - 2 * xb * xc * yb + yb ^ 3 - yb ^ 2 * yc)) * hw'
    exact mul_right_cancel₀ hmcr master
  · -- The x-coordinate of `B + s • (V - B) = C + t • (W - C)`.
    have e2 : (xb + s * (v - xb)) * m = (xc + t * (w - xc)) * m := by
      have r1 : (xb + s * (v - xb)) * m = xb * m + (s * m) * (v - xb) := by ring
      have r2 : (xc + t * (w - xc)) * m = xc * m + (t * m) * (w - xc) := by ring
      rw [r1, r2, es, et, hmd, hcr]
      ring
    exact mul_right_cancel₀ hmn e2
  · -- The y-coordinate.
    have e3 : (yb + s * (0 - yb)) * m = (yc + t * (0 - yc)) * m := by
      have r1 : (yb + s * (0 - yb)) * m = yb * m + (s * m) * (0 - yb) := by ring
      have r2 : (yc + t * (0 - yc)) * m = yc * m + (t * m) * (0 - yc) := by ring
      rw [r1, r2, es, et, hmd]
      ring
    exact mul_right_cancel₀ hmn e3

/-- The geometric step: all distances are explicit rational functions of the
coordinates, and the only square roots that show up are of the form `√(x²) = x`
with `x ≥ 0`. -/
theorem result (u xb yb xc yc v w cr m s t : ℝ) (T : EuclideanSpace ℝ (Fin 2))
    (hu : 0 < u) (hxb : 0 < xb) (hxc : 0 < xc) (hyb : yb < 0) (hyc : 0 < yc)
    (hv : v = (xb ^ 2 + yb ^ 2) / (2 * xb))
    (hw : w = (xc ^ 2 + yc ^ 2) / (2 * xc))
    (hcr : cr = xb * yc - xc * yb)
    (hmd : m = yc * v - yb * w - cr)
    (hs : s = (w * (yc - yb) - cr) / m)
    (ht : t = (v * (yc - yb) - cr) / m)
    (hcirc : u * cr = (xb ^ 2 + yb ^ 2) * yc - (xc ^ 2 + yc ^ 2) * yb)
    (hvl : (xb ^ 2 + yb ^ 2) * (yc - yb) < 2 * xb * cr)
    (hwl : (xc ^ 2 + yc ^ 2) * (yc - yb) < 2 * xc * cr)
    (hT : T = !₂[xb, yb] + s • (!₂[v, 0] - !₂[xb, yb])) :
    dist (!₂[(0 : ℝ), 0] : EuclideanSpace ℝ (Fin 2)) !₂[u, 0]
      = dist T !₂[xb, yb] + dist T !₂[xc, yc] := by
  -- Sign facts coming from the configuration.
  have hcb : (0 : ℝ) < yc - yb := by linarith
  have hqb : (0 : ℝ) < xb ^ 2 + yb ^ 2 := by
    nlinarith [sq_pos_of_pos hxb, sq_nonneg yb]
  have hqc : (0 : ℝ) < xc ^ 2 + yc ^ 2 := by
    nlinarith [sq_pos_of_pos hxc, sq_nonneg yc]
  have hcrp : (0 : ℝ) < cr := by
    rw [hcr]
    have h1 := mul_pos hxb hyc
    have h2 := mul_neg_of_pos_of_neg hxc hyb
    linarith
  have hcrn : cr ≠ 0 := ne_of_gt hcrp
  have hvp : (0 : ℝ) < v := by rw [hv]; exact div_pos hqb (by linarith)
  have hwp : (0 : ℝ) < w := by rw [hw]; exact div_pos hqc (by linarith)
  have hvx : v * (yc - yb) < cr := by
    rw [hv, div_mul_eq_mul_div, div_lt_iff₀ (by linarith : (0 : ℝ) < 2 * xb)]
    linarith [hvl]
  have hwy : w * (yc - yb) < cr := by
    rw [hw, div_mul_eq_mul_div, div_lt_iff₀ (by linarith : (0 : ℝ) < 2 * xc)]
    linarith [hwl]
  have hm : m < 0 := by
    rw [hmd]
    have h1 := mul_lt_mul_of_pos_left hvx hyc
    have h2 := mul_lt_mul_of_pos_left hwy (show (0 : ℝ) < -yb by linarith)
    have h3 : (yc - yb) * (yc * v - yb * w) < (yc - yb) * cr := by nlinarith [h1, h2]
    have h4 : (yc - yb) * (yc * v - yb * w - cr) < 0 := by nlinarith [h3]
    exact neg_of_mul_neg_right h4 (le_of_lt hcb)
  have hmn : m ≠ 0 := ne_of_lt hm
  have hsp : (0 : ℝ) < s := by rw [hs]; exact div_pos_of_neg_of_neg (by linarith) hm
  have htp : (0 : ℝ) < t := by rw [ht]; exact div_pos_of_neg_of_neg (by linarith) hm
  have h2xb : (2 : ℝ) * xb ≠ 0 := mul_ne_zero (by norm_num) (ne_of_gt hxb)
  have h2xc : (2 : ℝ) * xc ≠ 0 := mul_ne_zero (by norm_num) (ne_of_gt hxc)
  obtain ⟨key, keyx, keyy⟩ :=
    key_alg u xb yb xc yc v w cr m s t h2xb h2xc hcrn hmn hv hw hcr hmd hs ht hcirc
  -- Coordinate evaluations.
  have cz0 : (!₂[(0 : ℝ), 0] : EuclideanSpace ℝ (Fin 2)) 0 = (0 : ℝ) := by simp
  have cz1 : (!₂[(0 : ℝ), 0] : EuclideanSpace ℝ (Fin 2)) 1 = (0 : ℝ) := by simp
  have cu0 : (!₂[u, 0] : EuclideanSpace ℝ (Fin 2)) 0 = u := by simp
  have cu1 : (!₂[u, 0] : EuclideanSpace ℝ (Fin 2)) 1 = (0 : ℝ) := by simp
  have cv0 : (!₂[v, 0] : EuclideanSpace ℝ (Fin 2)) 0 = v := by simp
  have cv1 : (!₂[v, 0] : EuclideanSpace ℝ (Fin 2)) 1 = (0 : ℝ) := by simp
  have cw0 : (!₂[w, 0] : EuclideanSpace ℝ (Fin 2)) 0 = w := by simp
  have cw1 : (!₂[w, 0] : EuclideanSpace ℝ (Fin 2)) 1 = (0 : ℝ) := by simp
  have cb0 : (!₂[xb, yb] : EuclideanSpace ℝ (Fin 2)) 0 = xb := by simp
  have cb1 : (!₂[xb, yb] : EuclideanSpace ℝ (Fin 2)) 1 = yb := by simp
  have cc0 : (!₂[xc, yc] : EuclideanSpace ℝ (Fin 2)) 0 = xc := by simp
  have cc1 : (!₂[xc, yc] : EuclideanSpace ℝ (Fin 2)) 1 = yc := by simp
  -- The three distances.
  have hAU : dist (!₂[(0 : ℝ), 0] : EuclideanSpace ℝ (Fin 2)) !₂[u, 0] = u := by
    rw [EuclideanSpace.dist_eq, Fin.sum_univ_two, cz0, cu0, cz1, cu1,
      Real.dist_eq, Real.dist_eq]
    simp [abs_of_pos hu, Real.sqrt_sq (le_of_lt hu)]
  have hVB : dist (!₂[v, 0] : EuclideanSpace ℝ (Fin 2)) !₂[xb, yb] = v := by
    rw [EuclideanSpace.dist_eq, Fin.sum_univ_two, cv0, cb0, cv1, cb1,
      Real.dist_eq, Real.dist_eq, sq_abs, sq_abs]
    rw [Real.sqrt_eq_iff_eq_sq (by positivity) (le_of_lt hvp), hv]
    field_simp [h2xb]
    ring
  have hWC : dist (!₂[w, 0] : EuclideanSpace ℝ (Fin 2)) !₂[xc, yc] = w := by
    rw [EuclideanSpace.dist_eq, Fin.sum_univ_two, cw0, cc0, cw1, cc1,
      Real.dist_eq, Real.dist_eq, sq_abs, sq_abs]
    rw [Real.sqrt_eq_iff_eq_sq (by positivity) (le_of_lt hwp), hw]
    field_simp [h2xc]
    ring
  have hTvec : T = !₂[xc, yc] + t • (!₂[w, 0] - !₂[xc, yc]) := by
    rw [hT]
    ext i
    fin_cases i
    · show xb + s * (v - xb) = xc + t * (w - xc)
      exact keyx
    · show yb + s * (0 - yb) = yc + t * (0 - yc)
      exact keyy
  have hTB : dist T !₂[xb, yb] = s * v := by
    rw [hT, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (le_of_lt hsp), ← dist_eq_norm, hVB]
  have hTC : dist T !₂[xc, yc] = t * w := by
    rw [hTvec, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (le_of_lt htp), ← dist_eq_norm, hWC]
  rw [hAU, hTB, hTC]
  exact key.symm

snip end

problem imo1997_p2 (u xb yb xc yc : ℝ)
    (hu : 0 < u) (hxb : 0 < xb) (hxc : 0 < xc) (hyb : yb < 0) (hyc : 0 < yc)
    (hcirc : u * (xb * yc - xc * yb)
        = (xb ^ 2 + yb ^ 2) * yc - (xc ^ 2 + yc ^ 2) * yb)
    (hv : (xb ^ 2 + yb ^ 2) * (yc - yb) < 2 * xb * (xb * yc - xc * yb))
    (hw : (xc ^ 2 + yc ^ 2) * (yc - yb) < 2 * xc * (xb * yc - xc * yb)) :
    let v := (xb ^ 2 + yb ^ 2) / (2 * xb)
    let w := (xc ^ 2 + yc ^ 2) / (2 * xc)
    let m := yc * v - yb * w - (xb * yc - xc * yb)
    let s := (w * (yc - yb) - (xb * yc - xc * yb)) / m
    let T : EuclideanSpace ℝ (Fin 2) := !₂[xb, yb] + s • (!₂[v, 0] - !₂[xb, yb])
    dist (!₂[(0 : ℝ), 0] : EuclideanSpace ℝ (Fin 2)) !₂[u, 0]
      = dist T !₂[xb, yb] + dist T !₂[xc, yc] := by
  intro v w m s T
  exact result u xb yb xc yc v w (xb * yc - xc * yb) m s
    ((v * (yc - yb) - (xb * yc - xc * yb)) / m) T
    hu hxb hxc hyb hyc rfl rfl rfl rfl rfl rfl hcirc hv hw rfl

end Imo1997P2
