/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Affine.AddTorsor
public import Mathlib.Analysis.Real.Sqrt
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 1973, Problem 4

A soldier needs to sweep a region with the shape of an equilateral triangle for mines.
The detector has an effective radius equal to half the altitude of the triangle.
He starts at a vertex of the triangle. What path should he follow in order to travel
the least distance and still sweep the whole region?

# Formalization notes

We take the side length of the triangle to be `1` and the starting vertex to be
`A = (0, 0)`; the other two vertices are `B = (1/2, √3/2)` and `C = (1, 0)`, so the
detector radius is `√3 / 4`.

Any successful path must come within distance `√3 / 4` of both `B` and `C`. As in the
classical solution, an optimal path may be taken to consist of two straight segments,
going from `A` to a point `X` on the circle of radius `√3 / 4` around one of the other
vertices and from there to a point `Y` on the circle around the remaining vertex. The
theorem below shows that the minimum of `dist A X + dist X Y` over all such broken
paths (in either order) is `(2 * √7 - √3) / 4`, and that this minimum is attained by
the path that goes from `A` to the midpoint of the altitude from `B` and from there
straight towards `C` until reaching distance `√3 / 4` of `C` (and by the mirror-image
path). The last conjunct shows that this path indeed sweeps the whole triangle: the
disks of radius `√3 / 4` around `A`, around the midpoint of the altitude from `B`,
and around the endpoint cover the triangle.

Note on the reduction to broken paths: any path from `A` that sweeps the triangle
must enter the closed disk of radius `√3 / 4` around `B` at some first point `X₀`
and the one around `C` at some first point `Y₀` (in one order or the other), and its
length is then at least `dist A X₀ + dist X₀ Y₀`; since `X₀`, `Y₀` lie on the two
circles, the lower bound proved here applies to arbitrary sweeping paths. As mathlib
lacks a path-length API, this reduction is kept as prose.
-/

namespace Imo1973P4

/-- The plane. -/
abbrev Pt := EuclideanSpace ℝ (Fin 2)

/-- The starting vertex of the equilateral triangle (of side length `1`). -/
noncomputable def A : Pt := !₂[0, 0]

/-- The second vertex of the triangle. -/
noncomputable def B : Pt := !₂[1 / 2, √3 / 2]

/-- The third vertex of the triangle. -/
noncomputable def C : Pt := !₂[1, 0]

/-- The detector radius: half the altitude of the triangle. -/
noncomputable def detectorRadius : ℝ := √3 / 4

/-- The first intermediate point of the optimal path: the midpoint of the altitude
from `B`. -/
noncomputable def optX : Pt := !₂[1 / 2, √3 / 4]

/-- The second (last) point of the optimal path: the point of the segment from `optX`
to `C` at distance `√3 / 4` from `C`. -/
noncomputable def optY : Pt := AffineMap.lineMap C optX (√3 / √7)

/-- The least distance the soldier has to travel (for a triangle of side `1`). -/
noncomputable determine answer : ℝ := (2 * √7 - √3) / 4

snip begin

lemma dist_sq_eq' (x y : Pt) :
    dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq, Real.dist_eq,
    sq_abs, sq_abs]

lemma dist_eq_of_coords (x y : Pt) {c : ℝ} (hc : 0 ≤ c)
    (h : (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 = c ^ 2) : dist x y = c := by
  have h1 : dist x y ^ 2 = c ^ 2 := by
    rw [dist_sq_eq']
    exact h
  have e := Real.sqrt_sq (dist_nonneg : 0 ≤ dist x y)
  rw [h1, Real.sqrt_sq hc] at e
  exact e.symm

lemma dist_le_of_coords (x y z : Pt)
    (h : (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 ≤ (x 0 - z 0) ^ 2 + (x 1 - z 1) ^ 2) :
    dist x y ≤ dist x z := by
  have h1 : dist x y ^ 2 ≤ dist x z ^ 2 := by
    rw [dist_sq_eq', dist_sq_eq']
    exact h
  have e := Real.sqrt_le_sqrt h1
  rwa [Real.sqrt_sq dist_nonneg, Real.sqrt_sq dist_nonneg] at e

lemma dist_le_of_sq_le (x y : Pt) {c : ℝ} (hc : 0 ≤ c) (h : dist x y ^ 2 ≤ c ^ 2) :
    dist x y ≤ c := by
  have e := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_sq dist_nonneg, Real.sqrt_sq hc] at e

lemma sq3 : (√3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
lemma sq7 : (√7 : ℝ) ^ 2 = 7 := Real.sq_sqrt (by norm_num)
lemma sq34 : (√3 / 4 : ℝ) ^ 2 = 3 / 16 := by
  rw [div_pow, sq3]
  norm_num
lemma sq37 : (√3 / √7 : ℝ) ^ 2 = 3 / 7 := by
  rw [div_pow, sq3, sq7]

lemma coordA0 : A 0 = 0 := by simp [A]
lemma coordA1 : A 1 = 0 := by simp [A]
lemma coordB0 : B 0 = 1 / 2 := by simp [B]
lemma coordB1 : B 1 = √3 / 2 := by simp [B]
lemma coordC0 : C 0 = 1 := by simp [C]
lemma coordC1 : C 1 = 0 := by simp [C]
lemma coordOptX0 : optX 0 = 1 / 2 := by simp [optX]
lemma coordOptX1 : optX 1 = √3 / 4 := by simp [optX]

lemma coordOptY0 : optY 0 = 1 - (√3 / √7) / 2 := by
  rw [optY, AffineMap.lineMap_apply_module']
  simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, coordOptX0,
    coordC0]
  ring

lemma coordOptY1 : optY 1 = (√3 / √7) * √3 / 4 := by
  rw [optY, AffineMap.lineMap_apply_module']
  simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, coordOptX1,
    coordC1]
  ring

/-- The reflection of `C` across the line `y = √3 / 4`, which is tangent at `optX`
to the circle of radius `√3 / 4` around `B`. -/
noncomputable def C' : Pt := !₂[1, √3 / 2]

lemma coordC'0 : C' 0 = 1 := by simp [C']
lemma coordC'1 : C' 1 = √3 / 2 := by simp [C']

/-- The reflection of `B` across the tangent line at the midpoint of the altitude
from `C` to the circle of radius `√3 / 4` around `C`. -/
noncomputable def B' : Pt := !₂[5 / 4, √3 / 4]

lemma coordB'0 : B' 0 = 5 / 4 := by simp [B']
lemma coordB'1 : B' 1 = √3 / 4 := by simp [B']

/-- Key optimization step: for `X` on the circle of radius `√3 / 4` around `B`,
the sum `dist A X + dist X C` is at least `dist A C' = √7 / 2`. -/
lemma lower_aux (X : Pt) (hX : dist X B = detectorRadius) :
    √7 / 2 ≤ dist A X + dist X C := by
  have hX' : dist X B = √3 / 4 := hX
  have hXB : (X 0 - 1 / 2) ^ 2 + (X 1 - √3 / 2) ^ 2 = 3 / 16 := by
    have h1 : dist X B ^ 2 = (√3 / 4) ^ 2 := by rw [hX']
    rw [dist_sq_eq', coordB0, coordB1, sq34] at h1
    exact h1
  -- The circle around `B` is tangent to the line `y = √3 / 4`, so `X` lies above it.
  have hy : √3 / 4 ≤ X 1 := by
    have h2 : (X 1 - √3 / 2) ^ 2 ≤ (√3 / 4) ^ 2 := by
      have hs := sq_nonneg (X 0 - 1 / 2)
      linarith [hXB, sq34, hs]
    have h3 := abs_le_of_sq_le_sq h2 (by positivity : (0 : ℝ) ≤ √3 / 4)
    have h4 := (abs_le.mp h3).1
    linarith
  have hAC' : dist A C' = √7 / 2 := by
    apply dist_eq_of_coords _ _ (by positivity)
    rw [coordA0, coordA1, coordC'0, coordC'1]
    linear_combination sq3 / 4 - sq7 / 4
  -- `X` is at least as close to the reflection `C'` as to `C`.
  have hC'C : dist X C' ≤ dist X C := by
    apply dist_le_of_coords
    rw [coordC'0, coordC'1, coordC0, coordC1]
    have hmul : (0 : ℝ) ≤ √3 * (X 1 - √3 / 4) :=
      mul_nonneg (Real.sqrt_nonneg 3) (sub_nonneg.mpr hy)
    nlinarith [sq3]
  have htri : dist A C' ≤ dist A X + dist X C' := dist_triangle A X C'
  linarith [hAC', hC'C, htri]

/-- The mirror-image optimization step: for `X` on the circle of radius `√3 / 4`
around `C`, the sum `dist A X + dist X B` is at least `dist A B' = √7 / 2`. -/
lemma lower_aux' (X : Pt) (hX : dist X C = detectorRadius) :
    √7 / 2 ≤ dist A X + dist X B := by
  have hX' : dist X C = √3 / 4 := hX
  have hXC : (X 0 - 1) ^ 2 + (X 1 - 0) ^ 2 = 3 / 16 := by
    have h1 : dist X C ^ 2 = (√3 / 4) ^ 2 := by rw [hX']
    rw [dist_sq_eq', coordC0, coordC1, sq34] at h1
    exact h1
  -- `X` lies on the far side of the tangent line at `(5/8, √3 / 8)`.
  have hside : 3 / 2 ≤ 3 * X 0 - √3 * X 1 := by
    nlinarith [sq_nonneg (X 0 - 5 / 8), sq_nonneg (X 1 - √3 / 8), sq3, hXC]
  have hAB' : dist A B' = √7 / 2 := by
    apply dist_eq_of_coords _ _ (by positivity)
    rw [coordA0, coordA1, coordB'0, coordB'1]
    linear_combination sq3 / 16 - sq7 / 4
  -- `X` is at least as close to the reflection `B'` as to `B`.
  have hB'B : dist X B' ≤ dist X B := by
    apply dist_le_of_coords
    rw [coordB'0, coordB'1, coordB0, coordB1]
    nlinarith [hside, sq3]
  have htri : dist A B' ≤ dist A X + dist X B' := dist_triangle A X B'
  linarith [hAB', hB'B, htri]

/-- Lower bound for broken paths that visit the circle around `B` first. -/
lemma lower (X Y : Pt) (hX : dist X B = detectorRadius) (hY : dist Y C = detectorRadius) :
    answer ≤ dist A X + dist X Y := by
  have h1 := lower_aux X hX
  have hY' : dist Y C = √3 / 4 := hY
  have h2 : dist X C ≤ dist X Y + dist Y C := dist_triangle X Y C
  have hans : answer = √7 / 2 - √3 / 4 := by
    unfold answer
    ring
  rw [hans]
  linarith [h1, h2, hY']

/-- Lower bound for broken paths that visit the circle around `C` first. -/
lemma lower' (X Y : Pt) (hX : dist X C = detectorRadius) (hY : dist Y B = detectorRadius) :
    answer ≤ dist A X + dist X Y := by
  have h1 := lower_aux' X hX
  have hY' : dist Y B = √3 / 4 := hY
  have h2 : dist X B ≤ dist X Y + dist Y B := dist_triangle X Y B
  have hans : answer = √7 / 2 - √3 / 4 := by
    unfold answer
    ring
  rw [hans]
  linarith [h1, h2, hY']

/-- The midpoint of the altitude from `B` is at distance `√3 / 4` from `B`. -/
lemma dist_optX_B : dist optX B = detectorRadius := by
  show dist optX B = √3 / 4
  apply dist_eq_of_coords _ _ (by positivity)
  rw [coordOptX0, coordOptX1, coordB0, coordB1]
  ring

/-- The distance from `A` to `optX` is `√7 / 4`. -/
lemma dist_A_optX : dist A optX = √7 / 4 := by
  apply dist_eq_of_coords _ _ (by positivity)
  rw [coordA0, coordA1, coordOptX0, coordOptX1]
  linear_combination sq3 / 16 - sq7 / 16

/-- The distance from `optX` to `C` is `√7 / 4`. -/
lemma dist_optX_C : dist optX C = √7 / 4 := by
  apply dist_eq_of_coords _ _ (by positivity)
  rw [coordOptX0, coordOptX1, coordC0, coordC1]
  linear_combination sq3 / 16 - sq7 / 16

/-- The endpoint `optY` of the optimal path is at distance `√3 / 4` from `C`. -/
lemma dist_optY_C : dist optY C = detectorRadius := by
  show dist optY C = √3 / 4
  rw [optY, dist_lineMap_left, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ √3 / √7), dist_comm C optX, dist_optX_C]
  have h7 : (√7 : ℝ) ≠ 0 := ne_of_gt (by positivity)
  field_simp

/-- The distance from `optX` to `optY` is `(√7 - √3) / 4`. -/
lemma dist_optX_optY : dist optX optY = (√7 - √3) / 4 := by
  rw [dist_comm optX optY, optY, dist_lineMap_right, Real.norm_eq_abs]
  have hlt : √3 / √7 ≤ 1 := by
    rw [div_le_one (by positivity : (0 : ℝ) < √7)]
    exact Real.sqrt_le_sqrt (by norm_num)
  rw [abs_of_nonneg (sub_nonneg.mpr hlt), dist_comm C optX, dist_optX_C]
  have h7 : (√7 : ℝ) ≠ 0 := ne_of_gt (by positivity)
  field_simp

/-- The total length of the optimal path is the answer. -/
lemma path_length : dist A optX + dist optX optY = answer := by
  rw [dist_A_optX, dist_optX_optY]
  unfold answer
  ring

/-- Every point of the triangle is within distance `√3 / 4` of `A`, of `optX`, or of
`optY`: the optimal path sweeps the whole triangle. We parametrize the triangle by
`Q(s, t) = (s/2 + t, s·√3/2) = A + s(B - A) + t(C - A)` with `0 ≤ s`, `0 ≤ t`,
`s + t ≤ 1`, and split it into three regions: `s ≥ 1 / 4` (covered by the disk around
`optX`), `s, t ≤ 1 / 4` (covered by the disk around `A`), and the remaining points
with `s ≤ 1 / 4 ≤ t` (covered by the disk around `optY`, unless already covered by
the disk around `A`). -/
lemma cover (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t ≤ 1) :
    dist !₂[s / 2 + t, s * √3 / 2] A ≤ detectorRadius ∨
      dist !₂[s / 2 + t, s * √3 / 2] optX ≤ detectorRadius ∨
        dist !₂[s / 2 + t, s * √3 / 2] optY ≤ detectorRadius := by
  set Q : Pt := !₂[s / 2 + t, s * √3 / 2] with hQ
  have hQ0 : Q 0 = s / 2 + t := by simp [hQ]
  have hQ1 : Q 1 = s * √3 / 2 := by simp [hQ]
  have hdA : dist Q A ^ 2 = s ^ 2 + s * t + t ^ 2 := by
    rw [dist_sq_eq', hQ0, hQ1, coordA0, coordA1]
    linear_combination (s ^ 2 / 4) * sq3
  have hdP : dist Q optX ^ 2 = s ^ 2 + s * t + t ^ 2 - 5 * s / 4 - t + 7 / 16 := by
    rw [dist_sq_eq', hQ0, hQ1, coordOptX0, coordOptX1]
    linear_combination ((s / 2 - 1 / 4) ^ 2) * sq3
  by_cases h1 : 1 / 4 ≤ s
  · -- Region `1 / 4 ≤ s`: covered by the disk around `optX`.
    right; left
    show dist Q optX ≤ √3 / 4
    apply dist_le_of_sq_le _ _ (by positivity)
    have hGP : dist Q optX ^ 2 - 3 / 16 =
        t * (t - 3 / 4) + (s - 1 / 4) * (s + t - 1) := by
      rw [hdP]
      ring
    have hp1 : t * (t - 3 / 4) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht (by linarith)
    have hp2 : (s - 1 / 4) * (s + t - 1) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith : (0 : ℝ) ≤ s - 1 / 4) (by linarith)
    nlinarith [hGP, sq34, hp1, hp2]
  · push Not at h1
    by_cases h2 : t ≤ 1 / 4
    · -- Region `s ≤ 1 / 4`, `t ≤ 1 / 4`: covered by the disk around `A`.
      left
      show dist Q A ≤ √3 / 4
      apply dist_le_of_sq_le _ _ (by positivity)
      have g1 : 0 ≤ s * (1 / 4 - s) := mul_nonneg hs (by linarith)
      have g2 : 0 ≤ t * (1 / 4 - t) := mul_nonneg ht (by linarith)
      have g3 : 0 ≤ s * (1 / 4 - t) := mul_nonneg hs (by linarith)
      nlinarith [hdA, sq34, g1, g2, g3, h1, h2]
    · push Not at h2
      by_cases h3 : dist Q A ^ 2 ≤ 3 / 16
      · -- Already covered by the disk around `A`.
        left
        show dist Q A ≤ √3 / 4
        exact dist_le_of_sq_le _ _ (by positivity) (by rwa [sq34])
      · -- Region `s ≤ 1 / 4 ≤ t` outside the disk around `A`: covered by the
        -- disk around `optY`.
        push Not at h3
        rw [hdA] at h3
        right; right
        show dist Q optY ≤ √3 / 4
        have hdY : dist Q optY ^ 2 =
            s ^ 2 + s * t + t ^ 2 - s * (1 + (√3 / √7) / 4) - t * (2 - √3 / √7) +
              1 - √3 / √7 + 3 / 16 := by
          rw [dist_sq_eq', hQ0, hQ1, coordOptY0, coordOptY1]
          linear_combination ((s / 2 - (√3 / √7) / 4) ^ 2) * sq3 + (7 / 16) * sq37
        have hfact : dist Q optY ^ 2 - 3 / 16 =
            -((1 - s - t) * (3 / 4 * s + t + (√3 / √7 - 1)) +
              s * (-(1 / 4) * s + 3 / 4 * t + (5 * (√3 / √7) / 4 - 3 / 4))) := by
          rw [hdY]
          ring
        -- The first factor `3 / 4 * s + t + (√3 / √7 - 1)` is nonnegative:
        -- `3 / 4 * s + t ≥ √3 / 4` since its square exceeds `(√3 / 4) ^ 2 = 3 / 16`.
        have hp1 : 0 ≤ t / 2 - 7 * s / 16 := by linarith
        have hp2 : (√3 / 4 : ℝ) ^ 2 ≤ (3 / 4 * s + t) ^ 2 := by
          have hid : (3 / 4 * s + t) ^ 2 =
              (s ^ 2 + s * t + t ^ 2) + s * (t / 2 - 7 * s / 16) := by
            ring
          have hs0 : 0 ≤ s * (t / 2 - 7 * s / 16) := mul_nonneg hs hp1
          nlinarith [sq34, h3, hid, hs0]
        have hp3 : √3 / 4 ≤ 3 / 4 * s + t := by
          have hnn : 0 ≤ 3 / 4 * s + t := by linarith
          have h4 := abs_le_of_sq_le_sq hp2 hnn
          rwa [abs_of_nonneg (by positivity : (0 : ℝ) ≤ √3 / 4)] at h4
        -- `√3 / √7 + √3 / 4 ≥ 1`, proved by squaring twice.
        have hk1 : (43 / 24 : ℝ) ≤ √7 := by
          have h5 : ((43 / 24 : ℝ)) ^ 2 ≤ 7 := by norm_num
          have h6 := Real.sqrt_le_sqrt h5
          rwa [Real.sqrt_sq (by norm_num)] at h6
        have hk3 : 4 * √7 ≤ 4 * √3 + √21 := by
          have hside : (0 : ℝ) ≤ 4 * √3 + √21 := by positivity
          have hsq7' : (4 * √7) ^ 2 = 112 := by
            rw [mul_pow, sq7]
            norm_num
          have hsqrt : √3 * √21 = 3 * √7 := by
            have e1 : (√3 : ℝ) * √21 = √(3 * 21) := by
              rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
            have e2 : √(3 * 21 : ℝ) = 3 * √7 := by
              rw [show (3 * 21 : ℝ) = (9 : ℝ) * 7 by norm_num,
                Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 9),
                show √(9 : ℝ) = 3 by
                  rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
            rw [e1, e2]
          have hsq21 : (√21 : ℝ) ^ 2 = 21 := Real.sq_sqrt (by norm_num)
          have hbig : (4 * √3 + √21) ^ 2 = 69 + 24 * √7 := by
            linear_combination 16 * sq3 + 8 * hsqrt + hsq21
          have hle : (4 * √7) ^ 2 ≤ (4 * √3 + √21) ^ 2 := by
            rw [hsq7', hbig]
            have h43 : (43 : ℝ) ≤ 24 * √7 := by linarith
            linarith
          have h7 := abs_le_of_sq_le_sq hle hside
          rwa [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * √7)] at h7
        have hk4 : 1 ≤ √3 / √7 + √3 / 4 := by
          have h4pos : (0 : ℝ) < (4 : ℝ) := by norm_num
          have h7pos : (0 : ℝ) < √7 := by positivity
          have g1 : (4 - √3) * √7 ≤ √3 * 4 := by
            have hsqrt2 : √3 * √7 = √21 := by
              rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
              norm_num
            nlinarith [hk3, hsqrt2]
          have g2 : (4 - √3) / 4 ≤ √3 / √7 := by
            rw [div_le_div_iff₀ h4pos h7pos]
            linarith [g1]
          have g3 : (1 : ℝ) = (4 - √3) / 4 + √3 / 4 := by ring
          linarith [g2, g3]
        have hp : 0 ≤ 3 / 4 * s + t + (√3 / √7 - 1) := by linarith [hp3, hk4]
        -- The second factor is nonnegative since `√3 / √7 ≥ 1 / 2`.
        have hkh : 1 / 2 ≤ √3 / √7 := by
          have g1 : ((1 / 2 : ℝ)) ^ 2 ≤ (√3 / √7) ^ 2 := by
            rw [sq37]
            norm_num
          have g2 := abs_le_of_sq_le_sq g1 (by positivity : (0 : ℝ) ≤ √3 / √7)
          rwa [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)] at g2
        have hq : 0 ≤ -(1 / 4) * s + 3 / 4 * t + (5 * (√3 / √7) / 4 - 3 / 4) := by
          linarith [h1, h2, hkh]
        have hprod1 : 0 ≤ (1 - s - t) * (3 / 4 * s + t + (√3 / √7 - 1)) :=
          mul_nonneg (by linarith) hp
        have hprod2 : 0 ≤ s * (-(1 / 4) * s + 3 / 4 * t + (5 * (√3 / √7) / 4 - 3 / 4)) :=
          mul_nonneg hs hq
        have hfin : dist Q optY ^ 2 ≤ (√3 / 4 : ℝ) ^ 2 := by
          nlinarith [hfact, sq34, hprod1, hprod2]
        exact dist_le_of_sq_le _ _ (by positivity) hfin

snip end

problem imo1973_p4 :
    (∀ X Y : Pt, dist X B = detectorRadius → dist Y C = detectorRadius →
      answer ≤ dist A X + dist X Y) ∧
    (∀ X Y : Pt, dist X C = detectorRadius → dist Y B = detectorRadius →
      answer ≤ dist A X + dist X Y) ∧
    dist optX B = detectorRadius ∧
    dist optY C = detectorRadius ∧
    dist A optX + dist optX optY = answer ∧
    (∀ s t : ℝ, 0 ≤ s → 0 ≤ t → s + t ≤ 1 →
      dist !₂[s / 2 + t, s * √3 / 2] A ≤ detectorRadius ∨
        dist !₂[s / 2 + t, s * √3 / 2] optX ≤ detectorRadius ∨
          dist !₂[s / 2 + t, s * √3 / 2] optY ≤ detectorRadius) :=
  ⟨lower, lower', dist_optX_B, dist_optY_C, path_length, cover⟩

end Imo1973P4
