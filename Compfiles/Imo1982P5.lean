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
# International Mathematical Olympiad 1982, Problem 5

The diagonals AC and CE of the regular hexagon ABCDEF are divided by
inner points M and N respectively, so that

  AM/AC = CN/CE = r.

Determine r if B, M and N are collinear.
-/

namespace Imo1982P5

/-- The plane, as a Euclidean affine space. -/
abbrev Pt := EuclideanSpace ℝ (Fin 2)

/-- The vertex `A` of a regular hexagon `ABCDEF` with side length `1`.
Since the ratio `r` in the problem is invariant under similarities of the
plane, we may fix coordinates:
`A = (0, √3)`, `B = (1, √3)`, `C = (3/2, √3/2)`,
`D = (1, 0)`, `E = (0, 0)`, `F = (-1/2, √3/2)`. -/
noncomputable def hexA : Pt := !₂[0, Real.sqrt 3]

/-- See `hexA`. -/
noncomputable def hexB : Pt := !₂[1, Real.sqrt 3]

/-- See `hexA`. -/
noncomputable def hexC : Pt := !₂[3 / 2, Real.sqrt 3 / 2]

/-- See `hexA`. -/
noncomputable def hexD : Pt := !₂[1, 0]

/-- See `hexA`. -/
noncomputable def hexE : Pt := !₂[0, 0]

/-- See `hexA`. -/
noncomputable def hexF : Pt := !₂[-1 / 2, Real.sqrt 3 / 2]

snip begin

theorem Pt.ext {x y : Pt} (h0 : x 0 = y 0) (h1 : x 1 = y 1) : x = y := by
  apply WithLp.ofLp_injective (p := 2)
  funext i
  fin_cases i <;> assumption

/-- The point `N = (1 - r) • C + r • E` lies on the line through `B` and
`M = (1 - r) • A + r • C` if and only if `N - B` is a scalar multiple of
`B - M`. -/
lemma mem_line_iff (r : ℝ) :
    ((1 - r) • hexC + r • hexE) ∈ line[ℝ, hexB, (1 - r) • hexA + r • hexC] ↔
      ∃ a : ℝ, a • (hexB - ((1 - r) • hexA + r • hexC)) =
        (1 - r) • hexC + r • hexE - hexB := by
  set M : Pt := (1 - r) • hexA + r • hexC with hM
  set N : Pt := (1 - r) • hexC + r • hexE with hN
  nth_rewrite 1 [← vsub_vadd N hexB]
  rw [AffineSubspace.vadd_mem_iff_mem_direction _
    (mem_affineSpan ℝ (Set.mem_insert hexB {M}))]
  rw [direction_affineSpan, vectorSpan_pair, Submodule.mem_span_singleton]
  simp only [vsub_eq_sub]

/-- Coordinates of `B - M` and `N - B`, where `M = (1 - r) • A + r • C`
and `N = (1 - r) • C + r • E`. -/
lemma coords (r : ℝ) :
    ((hexB - ((1 - r) • hexA + r • hexC)) 0 = 1 - 3 * r / 2) ∧
    ((hexB - ((1 - r) • hexA + r • hexC)) 1 = Real.sqrt 3 * r / 2) ∧
    (((1 - r) • hexC + r • hexE - hexB) 0 = (1 - 3 * r) / 2) ∧
    (((1 - r) • hexC + r • hexE - hexB) 1 = -Real.sqrt 3 * (1 + r) / 2) := by
  simp only [hexA, hexB, hexC, hexE, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

/-- The distance between two points given in coordinates. -/
lemma dist2 (x1 y1 x2 y2 : ℝ) :
    dist (!₂[x1, y1] : Pt) !₂[x2, y2] = Real.sqrt ((x1 - x2) ^ 2 + (y1 - y2) ^ 2) := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Real.dist_eq, sq_abs]

/-- Sanity check: the six points above really are the vertices of a regular
hexagon; every side has length `1`. -/
lemma hexagon_regular :
    dist hexA hexB = 1 ∧ dist hexB hexC = 1 ∧ dist hexC hexD = 1 ∧
      dist hexD hexE = 1 ∧ dist hexE hexF = 1 ∧ dist hexF hexA = 1 := by
  have h3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [hexA, hexB]
    rw [dist2, Real.sqrt_eq_one]
    ring
  · simp only [hexB, hexC]
    rw [dist2, Real.sqrt_eq_one]
    linear_combination (1 / 4) * h3
  · simp only [hexC, hexD]
    rw [dist2, Real.sqrt_eq_one]
    linear_combination (1 / 4) * h3
  · simp only [hexD, hexE]
    rw [dist2, Real.sqrt_eq_one]
    ring
  · simp only [hexE, hexF]
    rw [dist2, Real.sqrt_eq_one]
    linear_combination (1 / 4) * h3
  · simp only [hexF, hexA]
    rw [dist2, Real.sqrt_eq_one]
    linear_combination (1 / 4) * h3

/-- The core computation: with `M` and `N` dividing the diagonals `AC` and `CE`
of the regular hexagon in ratio `r`, the points `B`, `M`, `N` are collinear
if and only if `r² = 1/3`. -/
lemma collinear_iff (r : ℝ) (hr : 0 < r) :
    Collinear ℝ {hexB, (1 - r) • hexA + r • hexC, (1 - r) • hexC + r • hexE} ↔
      r ^ 2 = 1 / 3 := by
  obtain ⟨hBM0, hBM1, hNB0, hNB1⟩ := coords r
  have hsqrt3 : (0 : ℝ) < Real.sqrt 3 := by positivity
  have hBneM : hexB ≠ (1 - r) • hexA + r • hexC := by
    intro h
    have h1 : (hexB - ((1 - r) • hexA + r • hexC)) 1 = 0 := by rw [h, sub_self]; rfl
    rw [hBM1] at h1
    exact (ne_of_gt (div_pos (mul_pos hsqrt3 hr) two_pos)) h1
  have hcoll : Collinear ℝ {hexB, (1 - r) • hexA + r • hexC, (1 - r) • hexC + r • hexE} ↔
      ((1 - r) • hexC + r • hexE) ∈ line[ℝ, hexB, (1 - r) • hexA + r • hexC] := by
    constructor
    · intro hcol
      exact hcol.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hBneM
    · intro hNmem
      have h := collinear_insert_of_mem_affineSpan_pair hNmem
      rwa [show ({hexB, (1 - r) • hexA + r • hexC, (1 - r) • hexC + r • hexE} : Set Pt) =
          {(1 - r) • hexC + r • hexE, hexB, (1 - r) • hexA + r • hexC} by
        ext x
        simp
        tauto]
  rw [hcoll, mem_line_iff r]
  constructor
  · intro hNmem
    obtain ⟨a, ha⟩ := hNmem
    have hax : a * (1 - 3 * r / 2) = (1 - 3 * r) / 2 := by
      have h := congrArg (fun x : Pt => x 0) ha
      rwa [PiLp.smul_apply, smul_eq_mul, hBM0, hNB0] at h
    have hay : a * (Real.sqrt 3 * r / 2) = -Real.sqrt 3 * (1 + r) / 2 := by
      have h := congrArg (fun x : Pt => x 1) ha
      rwa [PiLp.smul_apply, smul_eq_mul, hBM1, hNB1] at h
    have ha_r : a * r = -(1 + r) := by
      have h2 : a * Real.sqrt 3 * r = -Real.sqrt 3 * (1 + r) := by
        linear_combination 2 * hay
      have h3 : Real.sqrt 3 * (a * r) = Real.sqrt 3 * (-(1 + r)) := by
        linear_combination h2
      exact mul_left_cancel₀ (ne_of_gt hsqrt3) h3
    have ha_val : a = -1 - 3 * r := by
      linear_combination hax + (3 / 2) * ha_r
    rw [ha_val] at ha_r
    linear_combination -ha_r / 3
  · intro hr2
    refine ⟨-1 - 3 * r, ?_⟩
    apply Pt.ext
    · rw [PiLp.smul_apply, smul_eq_mul, hBM0, hNB0]
      linear_combination (9 / 2) * hr2
    · rw [PiLp.smul_apply, smul_eq_mul, hBM1, hNB1]
      linear_combination (-3 * Real.sqrt 3 / 2) * hr2

snip end

/-- The answer: `r = 1/√3`. -/
noncomputable determine solution_r : ℝ := 1 / Real.sqrt 3

problem imo1982_p5 (r : ℝ) (M N : Pt)
    (hr : r ∈ Set.Ioo 0 1)
    (hM : M = (1 - r) • hexA + r • hexC)
    (hN : N = (1 - r) • hexC + r • hexE) :
    Collinear ℝ {hexB, M, N} ↔ r = solution_r := by
  rw [hM, hN]
  have hsol : solution_r = 1 / Real.sqrt 3 := rfl
  have hsol2 : solution_r ^ 2 = 1 / 3 := by
    rw [hsol, div_pow, one_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have hsolpos : 0 ≤ solution_r := by rw [hsol]; positivity
  rw [collinear_iff r hr.1]
  constructor
  · intro h2
    exact (sq_eq_sq₀ hr.1.le hsolpos).mp (by rw [h2, hsol2])
  · intro h
    rw [h]
    exact hsol2

end Imo1982P5
