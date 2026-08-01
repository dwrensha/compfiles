/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.AffineSpace.Midpoint
public import Mathlib.Tactic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 1960, Problem 5

The cube ABCDA'B'C'D' has A above A', B above B' and so on.
X is any point of the face diagonal AC and Y is any point of B'D'.

(a) Find the locus of the midpoint of XY.

(b) Find the locus of the point Z which lies one-third of the way along XY,
    so that ZY = 2·XZ.
-/

namespace Imo1960P5

open AffineMap

/-- Three-dimensional Euclidean space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The cube, taken with side length 1: the face `A'B'C'D'` lies in the plane
`z = 0`, the face `ABCD` in the plane `z = 1`, and `A` is directly above `A'`,
`B` above `B'`, and so on. -/
def A : E3 := !₂[0, 0, 1]

def B : E3 := !₂[1, 0, 1]
def C : E3 := !₂[1, 1, 1]
def D : E3 := !₂[0, 1, 1]
def A' : E3 := !₂[0, 0, 0]
def B' : E3 := !₂[1, 0, 0]
def C' : E3 := !₂[1, 1, 0]
def D' : E3 := !₂[0, 1, 0]

/-- The answer to part (a): the square whose vertices are the centers of the
four vertical faces of the cube, i.e. the midpoints of `AB'`, `CB'`, `CD'`
and `AD'`. -/
determine midpointLocus : Set E3 :=
  convexHull ℝ {midpoint ℝ A B', midpoint ℝ C B', midpoint ℝ C D', midpoint ℝ A D'}

/-- The answer to part (b): the rectangle whose vertices are the points
one-third of the way along `AB'`, `CB'`, `CD'` and `AD'`. -/
determine trisectionLocus : Set E3 :=
  convexHull ℝ {lineMap A B' (1 / 3 : ℝ), lineMap C B' (1 / 3 : ℝ),
    lineMap C D' (1 / 3 : ℝ), lineMap A D' (1 / 3 : ℝ)}

snip begin

/-- The set of points lying a fixed fraction `c` of the way from some point of
the segment `AC` to some point of the segment `B'D'` is the convex hull of the
four extreme positions. -/
theorem locus_eq_convexHull {E : Type*} [AddCommGroup E] [Module ℝ E]
    (A C B' D' : E) (c : ℝ) :
    {P : E | ∃ t ∈ Set.Icc (0 : ℝ) 1, ∃ s ∈ Set.Icc (0 : ℝ) 1,
        P = lineMap (lineMap A C t) (lineMap B' D' s) c}
      = convexHull ℝ {lineMap A B' c, lineMap C B' c, lineMap C D' c, lineMap A D' c} := by
  apply Set.Subset.antisymm
  · -- Every such point is the convex combination of the four extreme points
    -- with weights (1 - t)(1 - s), t(1 - s), ts, (1 - t)s.
    rintro P ⟨t, ht, s, hs, rfl⟩
    rw [Set.mem_Icc] at ht hs
    refine mem_convexHull_of_exists_fintype
      (w := ![(1 - t) * (1 - s), t * (1 - s), t * s, (1 - t) * s])
      (z := ![lineMap A B' c, lineMap C B' c, lineMap C D' c, lineMap A D' c]) ?_ ?_ ?_ ?_
    · intro i
      fin_cases i
      · exact mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hs.2)
      · exact mul_nonneg ht.1 (sub_nonneg.mpr hs.2)
      · exact mul_nonneg ht.1 hs.1
      · exact mul_nonneg (sub_nonneg.mpr ht.2) hs.1
    · rw [Fin.sum_univ_four]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
      ring
    · intro i
      fin_cases i <;> simp
    · rw [Fin.sum_univ_four]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three,
        AffineMap.lineMap_apply_module]
      module
  · -- The locus contains the four extreme points and is convex.
    apply convexHull_min
    · rintro Q (rfl | rfl | rfl | rfl)
      · exact ⟨0, Set.left_mem_Icc.mpr zero_le_one, 0, Set.left_mem_Icc.mpr zero_le_one,
          by simp⟩
      · exact ⟨1, Set.right_mem_Icc.mpr zero_le_one, 0, Set.left_mem_Icc.mpr zero_le_one,
          by simp⟩
      · exact ⟨1, Set.right_mem_Icc.mpr zero_le_one, 1, Set.right_mem_Icc.mpr zero_le_one,
          by simp⟩
      · exact ⟨0, Set.left_mem_Icc.mpr zero_le_one, 1, Set.right_mem_Icc.mpr zero_le_one,
          by simp⟩
    · rintro P₁ ⟨t₁, ht₁, s₁, hs₁, rfl⟩ P₂ ⟨t₂, ht₂, s₂, hs₂, rfl⟩ a b ha hb hab
      rw [Set.mem_Icc] at ht₁ ht₂ hs₁ hs₂
      refine ⟨a * t₁ + b * t₂, ⟨?_, ?_⟩, a * s₁ + b * s₂, ⟨?_, ?_⟩, ?_⟩
      · exact add_nonneg (mul_nonneg ha ht₁.1) (mul_nonneg hb ht₂.1)
      · calc a * t₁ + b * t₂ ≤ a * 1 + b * 1 :=
            add_le_add (mul_le_mul_of_nonneg_left ht₁.2 ha)
              (mul_le_mul_of_nonneg_left ht₂.2 hb)
          _ = 1 := by rw [mul_one, mul_one, hab]
      · exact add_nonneg (mul_nonneg ha hs₁.1) (mul_nonneg hb hs₂.1)
      · calc a * s₁ + b * s₂ ≤ a * 1 + b * 1 :=
            add_le_add (mul_le_mul_of_nonneg_left hs₁.2 ha)
              (mul_le_mul_of_nonneg_left hs₂.2 hb)
          _ = 1 := by rw [mul_one, mul_one, hab]
      · have e1 : (1 : ℝ) - (a * t₁ + b * t₂) = a * (1 - t₁) + b * (1 - t₂) := by
          linear_combination -hab
        have e2 : (1 : ℝ) - (a * s₁ + b * s₂) = a * (1 - s₁) + b * (1 - s₂) := by
          linear_combination -hab
        simp only [AffineMap.lineMap_apply_module]
        rw [e1, e2]
        module

/-- The point one-third of the way along `XY` indeed satisfies `ZY = 2·XZ`. -/
theorem dist_lineMap_one_third (X Y : E3) :
    dist Y (lineMap X Y (1 / 3 : ℝ)) = 2 * dist X (lineMap X Y (1 / 3 : ℝ)) := by
  have h1 : (1 : ℝ) - 1 / 3 = 2 / 3 := by norm_num
  rw [dist_eq_norm_vsub, right_vsub_lineMap, h1, dist_eq_norm_vsub, left_vsub_lineMap,
    norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2 / 3),
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 3), vsub_eq_sub, vsub_eq_sub, norm_sub_rev]
  ring

snip end

problem imo1960_p5a :
    {M : E3 | ∃ X ∈ segment ℝ A C, ∃ Y ∈ segment ℝ B' D', M = midpoint ℝ X Y}
      = midpointLocus := by
  show _ = convexHull ℝ {lineMap A B' (⅟2 : ℝ), lineMap C B' (⅟2 : ℝ),
    lineMap C D' (⅟2 : ℝ), lineMap A D' (⅟2 : ℝ)}
  rw [← locus_eq_convexHull]
  apply Set.Subset.antisymm
  · rintro M ⟨X, hX, Y, hY, rfl⟩
    rw [segment_eq_image_lineMap] at hX hY
    rcases hX with ⟨t, ht, rfl⟩
    rcases hY with ⟨s, hs, rfl⟩
    exact ⟨t, ht, s, hs, rfl⟩
  · rintro M ⟨t, ht, s, hs, rfl⟩
    exact ⟨lineMap A C t, by rw [segment_eq_image_lineMap]; exact ⟨t, ht, rfl⟩,
      lineMap B' D' s, by rw [segment_eq_image_lineMap]; exact ⟨s, hs, rfl⟩, rfl⟩

problem imo1960_p5b :
    {Z : E3 | ∃ X ∈ segment ℝ A C, ∃ Y ∈ segment ℝ B' D', Z = lineMap X Y (1 / 3 : ℝ)}
      = trisectionLocus := by
  show _ = convexHull ℝ {lineMap A B' (1 / 3 : ℝ), lineMap C B' (1 / 3 : ℝ),
    lineMap C D' (1 / 3 : ℝ), lineMap A D' (1 / 3 : ℝ)}
  rw [← locus_eq_convexHull]
  apply Set.Subset.antisymm
  · rintro Z ⟨X, hX, Y, hY, rfl⟩
    rw [segment_eq_image_lineMap] at hX hY
    rcases hX with ⟨t, ht, rfl⟩
    rcases hY with ⟨s, hs, rfl⟩
    exact ⟨t, ht, s, hs, rfl⟩
  · rintro Z ⟨t, ht, s, hs, rfl⟩
    exact ⟨lineMap A C t, by rw [segment_eq_image_lineMap]; exact ⟨t, ht, rfl⟩,
      lineMap B' D' s, by rw [segment_eq_image_lineMap]; exact ⟨s, hs, rfl⟩, rfl⟩

end Imo1960P5
