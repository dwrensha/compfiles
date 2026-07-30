/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.LinearAlgebra.AffineSpace.Midpoint
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 1959, Problem 5

An arbitrary point M is taken in the interior of the segment AB.
Squares AMCD and MBEF are constructed on the same side of AB.
The circles circumscribed about these squares, with centers P and Q,
intersect at M and N.

(a) Prove that AF and BC intersect at N.
(b) Prove that the lines MN pass through a fixed point S
    (independent of the choice of M).
(c) Find the locus of the midpoints of the segments PQ as M varies.

## Formalization notes

We work in Cartesian coordinates in the Euclidean plane. Since the
hypotheses and conclusions are invariant under rigid motions of the
plane, we may assume that `A = (0, 0)` and `B = (b, 0)` with `0 < b`;
then `M = (m, 0)` with `0 < m < b`. The squares are constructed on the
positive-`y` side of `AB`, so `C = (m, m)`, `D = (0, m)`,
`E = (b, b - m)` and `F = (m, b - m)`. The circumcenters of the two
squares are `P = (m/2, m/2)` and `Q = ((m+b)/2, (b-m)/2)`.
The second intersection point of the two circumcircles is
`N = (2 b m² / D, 2 m b (b - m) / D)` with `D = 2 b² - 4 b m + 4 m²`,
and the fixed point of part (b) is `S = (b/2, -b/2)`: the midpoint of
the arc `AB` of the circle with diameter `AB` lying on the opposite
side of `AB` from the squares.
-/

namespace Imo1959P5

/-- The Euclidean plane. -/
abbrev Pt := EuclideanSpace ℝ (Fin 2)

/-- We place `A` at the origin. -/
def ptA : Pt := 0

/-- We place `B` at `(b, 0)`, where `b = dist A B > 0`. -/
def ptB (b : ℝ) : Pt := !₂[b, 0]

/-- The point `M = (m, 0)` in the interior of `AB`, so `0 < m < b`. -/
def ptM (m : ℝ) : Pt := !₂[m, 0]

/-- The square `AMCD` on the positive-`y` side of `AB`: `C = (m, m)`. -/
def ptC (m : ℝ) : Pt := !₂[m, m]

/-- The square `AMCD` on the positive-`y` side of `AB`: `D = (0, m)`. -/
def ptD (m : ℝ) : Pt := !₂[0, m]

/-- The square `MBEF` on the positive-`y` side of `AB`: `E = (b, b - m)`. -/
def ptE (b m : ℝ) : Pt := !₂[b, b - m]

/-- The square `MBEF` on the positive-`y` side of `AB`: `F = (m, b - m)`. -/
def ptF (b m : ℝ) : Pt := !₂[m, b - m]

/-- The center `P = (m/2, m/2)` of the square `AMCD`. -/
noncomputable def ptP (m : ℝ) : Pt := !₂[m / 2, m / 2]

/-- The center `Q = ((m + b)/2, (b - m)/2)` of the square `MBEF`. -/
noncomputable def ptQ (b m : ℝ) : Pt := !₂[(m + b) / 2, (b - m) / 2]

/-- The quantity `D = 2 b² - 4 b m + 4 m² = 2 ((b - m)² + m²)`,
which is positive when `0 < m`, appearing in the coordinates of `N`. -/
def discr (b m : ℝ) : ℝ := 2 * b ^ 2 - 4 * b * m + 4 * m ^ 2

/-- The second intersection point of the two circumcircles:
`N = (2 b m² / D, 2 m b (b - m) / D)`. -/
noncomputable def ptN (b m : ℝ) : Pt :=
  !₂[2 * b * m ^ 2 / discr b m, 2 * m * b * (b - m) / discr b m]

/-- The fixed point `S = (b/2, -b/2)` of part (b): the midpoint of the
arc `AB` of the circle with diameter `AB` lying on the opposite side
of `AB` from the squares. It depends only on `b`, not on `m`. -/
noncomputable def ptS (b : ℝ) : Pt := !₂[b / 2, -b / 2]

snip begin

/-- Extensionality for points of the plane, by coordinates. -/
theorem Pt.ext {x y : Pt} (h0 : x 0 = y 0) (h1 : x 1 = y 1) : x = y := by
  apply WithLp.ofLp_injective (p := 2)
  funext i
  fin_cases i <;> assumption

lemma discr_pos {b m : ℝ} (hm : 0 < m) : 0 < discr b m := by
  have h : discr b m = 2 * (b - m) ^ 2 + 2 * m ^ 2 := by unfold discr; ring
  rw [h]
  have h1 : 0 ≤ 2 * (b - m) ^ 2 := by positivity
  have h2 : 0 < m ^ 2 := pow_pos hm 2
  linarith

/-- `M` lies on the circumcircle of the square `AMCD`. -/
lemma dist_M_P (m : ℝ) : dist (ptM m) (ptP m) = dist ptA (ptP m) := by
  rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq]
  congr 1
  simp only [Fin.sum_univ_two, Real.dist_eq, ptM, ptP, ptA, sq_abs, PiLp.zero_apply,
    PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- `C` lies on the circumcircle of the square `AMCD`. -/
lemma dist_C_P (m : ℝ) : dist (ptC m) (ptP m) = dist ptA (ptP m) := by
  rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq]
  congr 1
  simp only [Fin.sum_univ_two, Real.dist_eq, ptC, ptP, ptA, sq_abs, PiLp.zero_apply,
    PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- `N` lies on the circumcircle of the square `AMCD`. -/
lemma dist_N_P (b m : ℝ) (hm : 0 < m) :
    dist (ptN b m) (ptP m) = dist ptA (ptP m) := by
  have hD : discr b m ≠ 0 := (discr_pos hm).ne'
  rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq]
  congr 1
  simp only [Fin.sum_univ_two, Real.dist_eq, ptN, ptP, ptA, sq_abs, PiLp.zero_apply,
    PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp [hD]
  unfold discr
  ring

/-- `N` lies on the circumcircle of the square `MBEF`. -/
lemma dist_N_Q (b m : ℝ) (hm : 0 < m) :
    dist (ptN b m) (ptQ b m) = dist (ptM m) (ptQ b m) := by
  have hD : discr b m ≠ 0 := (discr_pos hm).ne'
  rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq]
  congr 1
  simp only [Fin.sum_univ_two, Real.dist_eq, ptN, ptQ, ptM, sq_abs,
    PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp [hD]
  unfold discr
  ring

/-- The two intersection points of the circumcircles are distinct. -/
lemma ptN_ne_ptM {b m : ℝ} (hb : 0 < b) (hm : 0 < m) (hmb : m < b) :
    ptN b m ≠ ptM m := by
  intro h
  have h1 : (ptN b m) 1 = (ptM m) 1 := by rw [h]
  simp only [ptN, ptM, PiLp.toLp_apply, Matrix.cons_val_one, Matrix.cons_val_zero] at h1
  have hpos : 0 < 2 * m * b * (b - m) / discr b m := by
    have h2 : 0 < b - m := by linarith
    exact div_pos (mul_pos (mul_pos (mul_pos two_pos hm) hb) h2) (discr_pos hm)
  linarith

/-- Part (a): `N` lies on the line `AF`. -/
lemma collinear_AFN (b m : ℝ) : Collinear ℝ {ptA, ptF b m, ptN b m} := by
  rw [collinear_iff_of_mem (Set.mem_insert _ _)]
  refine ⟨ptF b m, fun p hp => ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl
  · exact ⟨0, by simp [ptA]⟩
  · exact ⟨1, by simp [ptA]⟩
  · refine ⟨2 * b * m / discr b m, ?_⟩
    apply Pt.ext <;> simp [ptN, ptF, ptA] <;> ring

/-- Part (a): `N` lies on the line `BC`. -/
lemma collinear_BCN (b m : ℝ) (hm : 0 < m) : Collinear ℝ {ptB b, ptC m, ptN b m} := by
  have hD : discr b m ≠ 0 := (discr_pos hm).ne'
  rw [collinear_iff_of_mem (Set.mem_insert _ _)]
  refine ⟨ptC m -ᵥ ptB b, fun p hp => ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl
  · exact ⟨0, by simp⟩
  · exact ⟨1, by simp⟩
  · refine ⟨2 * b * (b - m) / discr b m, ?_⟩
    apply Pt.ext
    all_goals simp [ptN, ptC, ptB]
    all_goals field_simp [hD]
    all_goals unfold discr
    all_goals ring

/-- Part (b): the line `MN` passes through the fixed point `S`. -/
lemma collinear_MNS (b m : ℝ) (hm : 0 < m) : Collinear ℝ {ptM m, ptN b m, ptS b} := by
  have hD : discr b m ≠ 0 := (discr_pos hm).ne'
  rw [collinear_iff_of_mem (Set.mem_insert _ _)]
  refine ⟨ptS b -ᵥ ptM m, fun p hp => ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl
  · exact ⟨0, by simp⟩
  · refine ⟨-4 * m * (b - m) / discr b m, ?_⟩
    apply Pt.ext <;> simp [ptN, ptS, ptM] <;> field_simp [hD] <;>
      first | (unfold discr; ring) | ring
  · exact ⟨1, by simp⟩

/-- The midpoint of `PQ` in coordinates. -/
lemma midpoint_PQ (b m : ℝ) :
    midpoint ℝ (ptP m) (ptQ b m) = !₂[(2 * m + b) / 4, b / 4] := by
  have h2 : (⅟2 : ℝ) = 1 / 2 := by rw [invOf_eq_inv]; norm_num
  rw [midpoint_eq_smul_add, h2]
  apply Pt.ext <;> simp [ptP, ptQ] <;> ring

snip end

/-- The answer to part (c): the open segment of length `b / 2 = AB / 2`
on the line `y = b / 4`, centered above the midpoint of `AB`. -/
determine locus (b : ℝ) : Set Pt :=
  {R | R 1 = b / 4 ∧ b / 4 < R 0 ∧ R 0 < 3 * b / 4}

/-- Part (a), together with the verification that `N` (as defined above)
is indeed the second common point of the two circumcircles: both `M` and
`N` lie on the circle centered at `P` through `A` (the circumcircle of
the square `AMCD`), `N` lies on the circle centered at `Q` through `M`
(the circumcircle of the square `MBEF`), and `N ≠ M`. -/
problem imo1959_p5_a (b m : ℝ) (hb : 0 < b) (hm : 0 < m) (hmb : m < b) :
    dist (ptM m) (ptP m) = dist ptA (ptP m) ∧
    dist (ptC m) (ptP m) = dist ptA (ptP m) ∧
    dist (ptN b m) (ptP m) = dist ptA (ptP m) ∧
    dist (ptN b m) (ptQ b m) = dist (ptM m) (ptQ b m) ∧
    ptN b m ≠ ptM m ∧
    Collinear ℝ {ptA, ptF b m, ptN b m} ∧
    Collinear ℝ {ptB b, ptC m, ptN b m} :=
  ⟨dist_M_P m, dist_C_P m, dist_N_P b m hm, dist_N_Q b m hm,
    ptN_ne_ptM hb hm hmb, collinear_AFN b m, collinear_BCN b m hm⟩

problem imo1959_p5_b (b m : ℝ) (_hb : 0 < b) (hm : 0 < m) (_hmb : m < b) :
    Collinear ℝ {ptM m, ptN b m, ptS b} :=
  collinear_MNS b m hm

problem imo1959_p5_c (b : ℝ) (_hb : 0 < b) :
    {R : Pt | ∃ m : ℝ, 0 < m ∧ m < b ∧ R = midpoint ℝ (ptP m) (ptQ b m)} = locus b := by
  ext R
  simp only [Set.mem_setOf_eq, locus]
  constructor
  · rintro ⟨m, hm0, hmb, rfl⟩
    rw [midpoint_PQ]
    refine ⟨?_, by simp; linarith, by simp; linarith⟩
    simp
  · rintro ⟨h1, h2, h3⟩
    refine ⟨2 * R 0 - b / 2, by linarith, by linarith, ?_⟩
    rw [midpoint_PQ]
    have e : (2 * (2 * R 0 - b / 2) + b) / 4 = R 0 := by ring
    rw [e, ← h1]
    apply Pt.ext <;> simp

end Imo1959P5
