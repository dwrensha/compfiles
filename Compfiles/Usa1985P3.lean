/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Bound
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# USA Mathematical Olympiad 1985, Problem 3

A tetrahedron has at most one edge longer than 1.
What is the maximum total length of its edges?
-/

namespace Usa1985P3

/-- Vertices of a (possibly degenerate) tetrahedron: points of Euclidean 3-space. -/
abbrev Pt := EuclideanSpace ℝ (Fin 3)

/-- The total length of the six edges determined by four points. -/
noncomputable def totalLength (A B C D : Pt) : ℝ :=
  dist A B + dist A C + dist A D + dist B C + dist B D + dist C D

/-- All edges determined by `A B C D` have length at most `1`,
except possibly the edge `AB`. -/
def AllButOneLe (A B C D : Pt) : Prop :=
  dist A C ≤ 1 ∧ dist A D ≤ 1 ∧ dist B C ≤ 1 ∧ dist B D ≤ 1 ∧ dist C D ≤ 1

/-- At most one of the six edges determined by `A B C D` is longer than `1`. -/
def Valid (A B C D : Pt) : Prop :=
  AllButOneLe A B C D ∨ AllButOneLe A C B D ∨ AllButOneLe A D B C ∨
  AllButOneLe B C A D ∨ AllButOneLe B D A C ∨ AllButOneLe C D A B

noncomputable determine solution : ℝ := 5 + Real.sqrt 3

snip begin

/-- Parallelogram-law bound: a point within distance `1` of both `C` and `D` is
within distance `√(1 - (dist C D / 2)²)` of the midpoint of the segment `CD`.
This is the only geometric input needed; in particular no planarity reduction
is required, and the bound holds in any real inner product space. -/
lemma dist_midpoint_le {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (A C D : V) (hAC : dist A C ≤ 1) (hAD : dist A D ≤ 1) :
    dist A ((2 : ℝ)⁻¹ • (C + D)) ≤ √(1 - (dist C D / 2) ^ 2) := by
  simp only [dist_eq_norm] at hAC hAD ⊢
  set O : V := (2 : ℝ)⁻¹ • (C + D) with hO
  have hAC2 : ‖A - C‖ ^ 2 ≤ 1 := by
    have h := pow_le_pow_left₀ (norm_nonneg _) hAC 2
    rwa [one_pow] at h
  have hAD2 : ‖A - D‖ ^ 2 ≤ 1 := by
    have h := pow_le_pow_left₀ (norm_nonneg _) hAD 2
    rwa [one_pow] at h
  have hpar := parallelogram_law_with_norm ℝ (A - C) (A - D)
  have h1 : A - C + (A - D) = (2 : ℝ) • (A - O) := by
    rw [hO]; module
  have h2 : A - C - (A - D) = D - C := by abel
  rw [h1, h2, norm_smul, Real.norm_two, norm_sub_rev D C] at hpar
  have hexp : (2 * ‖A - O‖) ^ 2 = 4 * ‖A - O‖ ^ 2 := by ring
  have hsq2 : (‖C - D‖ / 2) ^ 2 = ‖C - D‖ ^ 2 / 4 := by ring
  have hsq : ‖A - O‖ ^ 2 ≤ 1 - (‖C - D‖ / 2) ^ 2 := by linarith
  have hnn : (0:ℝ) ≤ 1 - (‖C - D‖ / 2) ^ 2 := le_trans (sq_nonneg _) hsq
  exact (Real.le_sqrt (norm_nonneg _) hnn).mpr hsq

/-- The one-dimensional optimization behind the problem:
for `x ≤ 1/2` we have `2x + 2√(1 - x²) ≤ 1 + √3`
(the function is increasing on `[0, 1/2]` and this is its value at `x = 1/2`). -/
lemma two_mul_add_two_mul_sqrt_le {x : ℝ} (hx1 : x ≤ 1 / 2) :
    2 * x + 2 * √(1 - x ^ 2) ≤ 1 + √3 := by
  have h3lt : (1:ℝ) < √3 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hrhs : (0:ℝ) ≤ 1 + √3 - 2 * x := by linarith [Real.sqrt_nonneg 3]
  have hkey : (1 + √3 - 2 * x) ^ 2 - 4 * (1 - x ^ 2) =
      2 * (2 * x - 1) * (2 * x - √3) := by
    linear_combination Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  have hsq : 4 * (1 - x ^ 2) ≤ (1 + √3 - 2 * x) ^ 2 := by
    have e1 : 2 * x - 1 ≤ 0 := by linarith
    have e2 : 2 * x - √3 ≤ 0 := by linarith
    have hprod : (0:ℝ) ≤ 2 * (2 * x - 1) * (2 * x - √3) := by
      have h := mul_nonneg_of_nonpos_of_nonpos e1 e2
      nlinarith
    linarith
  have hsqrt : 2 * √(1 - x ^ 2) = √(4 * (1 - x ^ 2)) := by
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4), show (4:ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
  have hfin : √(4 * (1 - x ^ 2)) ≤ 1 + √3 - 2 * x := (Real.sqrt_le_left hrhs).mpr hsq
  linarith

/-- If all edges determined by `A B C D` except possibly `AB` have length at most `1`,
then the total length of the six edges is at most `5 + √3`. -/
lemma total_le {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (A B C D : V) (hAC : dist A C ≤ 1) (hAD : dist A D ≤ 1) (hBC : dist B C ≤ 1)
    (hBD : dist B D ≤ 1) (hCD : dist C D ≤ 1) :
    dist A B + dist A C + dist A D + dist B C + dist B D + dist C D ≤ 5 + √3 := by
  have hA := dist_midpoint_le A C D hAC hAD
  have hB := dist_midpoint_le B C D hBC hBD
  have hAB : dist A B ≤ 2 * √(1 - (dist C D / 2) ^ 2) := by
    calc dist A B
        ≤ dist A ((2 : ℝ)⁻¹ • (C + D)) + dist ((2 : ℝ)⁻¹ • (C + D)) B :=
          dist_triangle _ _ _
      _ = dist A ((2 : ℝ)⁻¹ • (C + D)) + dist B ((2 : ℝ)⁻¹ • (C + D)) := by
          rw [dist_comm ((2 : ℝ)⁻¹ • (C + D)) B]
      _ ≤ √(1 - (dist C D / 2) ^ 2) + √(1 - (dist C D / 2) ^ 2) :=
          add_le_add hA hB
      _ = 2 * √(1 - (dist C D / 2) ^ 2) := by ring
  have hx := two_mul_add_two_mul_sqrt_le (x := dist C D / 2) (by linarith)
  linarith

/-- The distance between two explicitly given points of `EuclideanSpace ℝ (Fin 3)`. -/
lemma dist_wit (a₁ a₂ a₃ b₁ b₂ b₃ : ℝ) :
    dist !₂[a₁, a₂, a₃] !₂[b₁, b₂, b₃] =
      √((a₁ - b₁) ^ 2 + (a₂ - b₂) ^ 2 + (a₃ - b₃) ^ 2) := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Real.dist_eq, sq_abs]

lemma sqrt3_div_two_sq : (√3 / 2 : ℝ) ^ 2 = 3 / 4 := by
  rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]; norm_num

lemma neg_sqrt3_div_two_sq : (-√3 / 2 : ℝ) ^ 2 = 3 / 4 := by
  rw [neg_div, neg_sq, div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]; norm_num

snip end

problem usa1985_p3 :
    IsGreatest {s : ℝ | ∃ A B C D : Pt, Valid A B C D ∧ s = totalLength A B C D}
      solution := by
  -- The extremal configuration: `C D` has length `1`, and `A`, `B` are the two
  -- points at distance `1` from both `C` and `D` (a planar rhombus of side `1`
  -- with `AB = √3`).
  constructor
  · have hAB : dist !₂[(0:ℝ), √3 / 2, 0] !₂[(0:ℝ), -√3 / 2, 0] = √3 := by
      rw [dist_wit, show (0 - 0 : ℝ) ^ 2 + (√3 / 2 - -√3 / 2) ^ 2 + (0 - 0) ^ 2 = √3 ^ 2
        by ring]
      exact Real.sqrt_sq (Real.sqrt_nonneg 3)
    have hAC : dist !₂[(0:ℝ), √3 / 2, 0] !₂[(-1/2:ℝ), 0, 0] = 1 := by
      rw [dist_wit, Real.sqrt_eq_one, sub_zero, sub_zero, sqrt3_div_two_sq]
      norm_num
    have hAD : dist !₂[(0:ℝ), √3 / 2, 0] !₂[(1/2:ℝ), 0, 0] = 1 := by
      rw [dist_wit, Real.sqrt_eq_one, sub_zero, sub_zero, sqrt3_div_two_sq]
      norm_num
    have hBC : dist !₂[(0:ℝ), -√3 / 2, 0] !₂[(-1/2:ℝ), 0, 0] = 1 := by
      rw [dist_wit, Real.sqrt_eq_one, sub_zero, sub_zero, neg_sqrt3_div_two_sq]
      norm_num
    have hBD : dist !₂[(0:ℝ), -√3 / 2, 0] !₂[(1/2:ℝ), 0, 0] = 1 := by
      rw [dist_wit, Real.sqrt_eq_one, sub_zero, sub_zero, neg_sqrt3_div_two_sq]
      norm_num
    have hCD : dist !₂[(-1/2:ℝ), 0, 0] !₂[(1/2:ℝ), 0, 0] = 1 := by
      rw [dist_wit, Real.sqrt_eq_one]
      norm_num
    refine ⟨!₂[(0:ℝ), √3 / 2, 0], !₂[(0:ℝ), -√3 / 2, 0], !₂[(-1/2:ℝ), 0, 0],
      !₂[(1/2:ℝ), 0, 0], Or.inl ⟨hAC.le, hAD.le, hBC.le, hBD.le, hCD.le⟩, ?_⟩
    show (5:ℝ) + √3 = dist _ _ + dist _ _ + dist _ _ + dist _ _ + dist _ _ + dist _ _
    rw [hAB, hAC, hAD, hBC, hBD, hCD]
    ring
  · rintro s ⟨A, B, C, D, hvalid, rfl⟩
    unfold Valid at hvalid
    obtain h | h | h | h | h | h := hvalid <;> unfold AllButOneLe at h
    · exact total_le A B C D h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2
    · have h' := total_le A C B D h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2
      rw [dist_comm C B] at h'
      show dist A B + dist A C + dist A D + dist B C + dist B D + dist C D ≤ 5 + √3
      linarith
    · have h' := total_le A D B C h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2
      rw [dist_comm D B, dist_comm D C] at h'
      show dist A B + dist A C + dist A D + dist B C + dist B D + dist C D ≤ 5 + √3
      linarith
    · have h' := total_le B C A D h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2
      rw [dist_comm B A, dist_comm C A] at h'
      show dist A B + dist A C + dist A D + dist B C + dist B D + dist C D ≤ 5 + √3
      linarith
    · have h' := total_le B D A C h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2
      rw [dist_comm B A, dist_comm D A, dist_comm D C] at h'
      show dist A B + dist A C + dist A D + dist B C + dist B D + dist C D ≤ 5 + √3
      linarith
    · have h' := total_le C D A B h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2
      rw [dist_comm C A, dist_comm C B, dist_comm D A, dist_comm D B] at h'
      show dist A B + dist A C + dist A D + dist B C + dist B D + dist C D ≤ 5 + √3
      linarith

end Usa1985P3
