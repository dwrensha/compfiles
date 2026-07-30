/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import Mathlib.Analysis.Convex.Segment
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 1962, Problem 3

Consider the cube ABCDA'B'C'D' (ABCD and A'B'C'D' are the upper and lower
bases, respectively, and edges AA', BB', CC', DD' are parallel). The point X
moves at constant speed along the perimeter of the square ABCD in the
direction ABCDA, and the point Y moves at the same speed along the perimeter
of the square B'C'CB in the direction B'C'CBB'. Points X and Y begin their
motion at the same instant from the starting points A and B' respectively.
Determine and draw the locus of the midpoints of the segments XY.
-/

namespace Imo1962P3

open scoped Convex

/-- Coordinate 3-space. -/
abbrev E3 : Type := Fin 3 → ℝ

/-- The vertices of the unit cube: `cubeA` = A = (0, 0, 0) and
`cubeC'` = C' = (1, 1, 1), with the face ABCD in the plane z = 0 and the
face A'B'C'D' in the parallel plane z = 1, A directly above A', etc. -/
def cubeA : E3 := ![0, 0, 0]
/-- Vertex B = (1, 0, 0) of the unit cube. -/
def cubeB : E3 := ![1, 0, 0]
/-- Vertex C = (1, 1, 0) of the unit cube. -/
def cubeC : E3 := ![1, 1, 0]
/-- Vertex D = (0, 1, 0) of the unit cube. -/
def cubeD : E3 := ![0, 1, 0]
/-- Vertex A' = (0, 0, 1) of the unit cube. -/
def cubeA' : E3 := ![0, 0, 1]
/-- Vertex B' = (1, 0, 1) of the unit cube. -/
def cubeB' : E3 := ![1, 0, 1]
/-- Vertex C' = (1, 1, 1) of the unit cube. -/
def cubeC' : E3 := ![1, 1, 1]
/-- Vertex D' = (0, 1, 1) of the unit cube. -/
def cubeD' : E3 := ![0, 1, 1]

/-- The center U = (1/2, 1/2, 0) of the face ABCD. -/
noncomputable def centerABCD : E3 := ![1/2, 1/2, 0]
/-- The center V = (1/2, 0, 1/2) of the face ABB'A'. -/
noncomputable def centerABB'A' : E3 := ![1/2, 0, 1/2]
/-- The center W = (1, 1/2, 1/2) of the face BCC'B'. -/
noncomputable def centerBCC'B' : E3 := ![1, 1/2, 1/2]

/-- The point at fraction `t` of the way from `P` to `Q`. -/
def trav (P Q : E3) (t : ℝ) : E3 := (1 - t) • P + t • Q

/-- The midpoint of XY during the first phase of the motion, when X traverses
the edge AB from A to B while Y traverses the edge B'C' from B' to C';
`t ∈ [0, 1]` is the fraction of the edge covered. -/
noncomputable def midAB (t : ℝ) : E3 :=
  (2 : ℝ)⁻¹ • (trav cubeA cubeB t + trav cubeB' cubeC' t)

/-- The midpoint of XY during the second phase of the motion, when X traverses
the edge BC from B to C while Y traverses the edge C'C from C' to C. -/
noncomputable def midBC (t : ℝ) : E3 :=
  (2 : ℝ)⁻¹ • (trav cubeB cubeC t + trav cubeC' cubeC t)

/-- The midpoint of XY during the third phase of the motion, when X traverses
the edge CD from C to D while Y traverses the edge CB from C to B. -/
noncomputable def midCD (t : ℝ) : E3 :=
  (2 : ℝ)⁻¹ • (trav cubeC cubeD t + trav cubeC cubeB t)

/-- The midpoint of XY during the fourth phase of the motion, when X traverses
the edge DA from D to A while Y traverses the edge BB' from B to B'. -/
noncomputable def midDA (t : ℝ) : E3 :=
  (2 : ℝ)⁻¹ • (trav cubeD cubeA t + trav cubeB cubeB' t)

/-- The locus of the midpoints of the segments XY: the boundary of the
rhombus whose vertices are the center V of the face ABB'A', the center W of
the face BCC'B', the vertex C of the cube, and the center U of the face
ABCD. -/
noncomputable determine locus : Set E3 :=
  [centerABB'A' -[ℝ] centerBCC'B'] ∪ [centerBCC'B' -[ℝ] cubeC] ∪
    [cubeC -[ℝ] centerABCD] ∪ [centerABCD -[ℝ] centerABB'A']

snip begin

/-- During the first phase, the midpoint moves linearly from the center V of
ABB'A' to the center W of BCC'B'. -/
lemma midAB_eq : midAB = fun t => (1 - t) • centerABB'A' + t • centerBCC'B' := by
  funext t
  ext j
  fin_cases j <;>
    simp [midAB, trav, cubeA, cubeB, cubeB', cubeC', centerABB'A', centerBCC'B'] <;>
    ring

/-- During the second phase, the midpoint moves linearly from the center W of
BCC'B' to the vertex C. -/
lemma midBC_eq : midBC = fun t => (1 - t) • centerBCC'B' + t • cubeC := by
  funext t
  ext j
  fin_cases j <;>
    simp [midBC, trav, cubeB, cubeC, cubeC', centerBCC'B'] <;>
    ring

/-- During the third phase, the midpoint moves linearly from the vertex C to
the center U of ABCD. -/
lemma midCD_eq : midCD = fun t => (1 - t) • cubeC + t • centerABCD := by
  funext t
  ext j
  fin_cases j <;>
    simp [midCD, trav, cubeB, cubeC, cubeD, centerABCD] <;>
    ring

/-- During the fourth phase, the midpoint moves linearly from the center U of
ABCD to the center V of ABB'A'. -/
lemma midDA_eq : midDA = fun t => (1 - t) • centerABCD + t • centerABB'A' := by
  funext t
  ext j
  fin_cases j <;>
    simp [midDA, trav, cubeA, cubeB, cubeB', cubeD, centerABCD, centerABB'A'] <;>
    ring

/-- The set of midpoints traced during the first phase is the segment VW. -/
lemma midAB_image :
    midAB '' Set.Icc 0 1 = [centerABB'A' -[ℝ] centerBCC'B'] := by
  rw [midAB_eq]
  exact (segment_eq_image ℝ _ _).symm

/-- The set of midpoints traced during the second phase is the segment WC. -/
lemma midBC_image :
    midBC '' Set.Icc 0 1 = [centerBCC'B' -[ℝ] cubeC] := by
  rw [midBC_eq]
  exact (segment_eq_image ℝ _ _).symm

/-- The set of midpoints traced during the third phase is the segment CU. -/
lemma midCD_image :
    midCD '' Set.Icc 0 1 = [cubeC -[ℝ] centerABCD] := by
  rw [midCD_eq]
  exact (segment_eq_image ℝ _ _).symm

/-- The set of midpoints traced during the fourth phase is the segment UV. -/
lemma midDA_image :
    midDA '' Set.Icc 0 1 = [centerABCD -[ℝ] centerABB'A'] := by
  rw [midDA_eq]
  exact (segment_eq_image ℝ _ _).symm

snip end

problem imo1962_p3 :
    (midAB '' Set.Icc 0 1) ∪ (midBC '' Set.Icc 0 1) ∪
      (midCD '' Set.Icc 0 1) ∪ (midDA '' Set.Icc 0 1) = locus := by
  rw [midAB_image, midBC_image, midCD_image, midDA_image]

end Imo1962P3
