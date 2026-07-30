/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 1987, Problem 2

In an acute-angled triangle ABC the interior bisector of angle A meets BC at L
and meets the circumcircle of ABC again at N. From L perpendiculars are drawn to
AB and AC, with feet K and M respectively. Prove that the quadrilateral AKNM and
the triangle ABC have equal areas.

## Solution sketch (after Gerhard Wöginger)

The triangles AKL and AML are congruent, so KM is perpendicular to AN and
area(AKNM) = KM·AN/2. The quadrilateral AKLM is cyclic (two opposite right
angles), and the sine rule gives KM = AL·sin BAC. The triangles ABL and ANC are
similar, so AB·AC = AN·AL. Hence
area(ABC) = AB·AC·sin BAC/2 = AN·AL·sin BAC/2 = AN·KM/2 = area(AKNM).

## Formalization notes

We prove the result by coordinates. Applying a rigid motion (which preserves
angles, circles, perpendicularity and areas), we place A at the origin and the
interior bisector of ∠BAC along the positive x-axis. Writing 2α for ∠BAC,
c = AB and b = AC, the vertices are
  A = (0, 0),  B = (c·cos α, c·sin α),  C = (b·cos α, -b·sin α).
The remaining points are then determined:
* L = AL ∩ BC. By the angle bisector theorem BL : LC = c : b, which gives
  L = (2·b·c·cos α/(b + c), 0).
* K (resp. M) is the orthogonal projection of L onto the line AB (resp. AC):
  K = (2·b·c·cos³α/(b+c), 2·b·c·cos²α·sin α/(b+c)) and M its mirror image.
* The circumcircle of ABC has equation x² + y² + Dx + Ey = 0 with
  D = -(b + c)/(2·cos α), so it meets the x-axis again in
  N = ((b + c)/(2·cos α), 0).
The auxiliary lemmas below verify that the points so defined have the required
geometric properties: L lies on BC with BL : LC = c : b, K lies on AB with
LK ⟂ AB, M lies on AC with LM ⟂ AC, and A, B, C, N are concyclic.
The area statement then becomes a shoelace computation: twice the
signed area of both AKNM and ABC equals -2·b·c·sin α·cos α. Note that the
equality of areas in fact holds for the whole configuration, whether or not the
triangle is acute (acuteness only guarantees that K, M lie on the segments and
that the quadrilateral is convex); we assume α < π/4 so that ∠BAC < 90°.
-/

namespace Imo1987P2

open Real

snip begin

/-- Twice the signed area of the triangle PQR (shoelace formula). -/
def twoAreaTriangle (P Q R : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  (Q 0 - P 0) * (R 1 - P 1) - (R 0 - P 0) * (Q 1 - P 1)

/-- Twice the signed area of the quadrilateral P Q R S (shoelace formula). -/
def twoAreaQuad (P Q R S : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  (P 0 * Q 1 - Q 0 * P 1) + (Q 0 * R 1 - R 0 * Q 1) +
    (R 0 * S 1 - S 0 * R 1) + (S 0 * P 1 - P 0 * S 1)

/-- The area of a triangle given by its vertices. -/
noncomputable def triArea (P Q R : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  |twoAreaTriangle P Q R| / 2

/-- The area of a (simple) quadrilateral given by its vertices in order. -/
noncomputable def quadArea (P Q R S : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  |twoAreaQuad P Q R S| / 2

/-- Vertex A, placed at the origin. -/
noncomputable def ptA : EuclideanSpace ℝ (Fin 2) := !₂[0, 0]

/-- Vertex B, with AB = c making the angle α with the bisector. -/
noncomputable def ptB (c α : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  !₂[c * cos α, c * sin α]

/-- Vertex C, with AC = b making the angle -α with the bisector. -/
noncomputable def ptC (b α : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  !₂[b * cos α, -b * sin α]

/-- The point L where the interior bisector of ∠BAC meets BC
(coordinates from the angle bisector theorem BL : LC = c : b). -/
noncomputable def ptL (b c α : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  !₂[2 * b * c * cos α / (b + c), 0]

/-- The foot K of the perpendicular from L to AB
(coordinates from the orthogonal projection of L onto the line AB). -/
noncomputable def ptK (b c α : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  !₂[2 * b * c * cos α ^ 3 / (b + c), 2 * b * c * cos α ^ 2 * sin α / (b + c)]

/-- The foot M of the perpendicular from L to AC. -/
noncomputable def ptM (b c α : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  !₂[2 * b * c * cos α ^ 3 / (b + c), -(2 * b * c * cos α ^ 2 * sin α / (b + c))]

/-- The second intersection N of the bisector AL with the circumcircle of ABC
(coordinates from the circumcircle equation). -/
noncomputable def ptN (b c α : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  !₂[(b + c) / (2 * cos α), 0]

/-- L lies on the line BC, in the ratio BL : LC = c : b prescribed by the
angle bisector theorem. -/
lemma ptL_on_BC (b c α : ℝ) (hbc : b + c ≠ 0) :
    ptL b c α = (b / (b + c)) • ptB c α + (c / (b + c)) • ptC b α := by
  ext i
  fin_cases i <;>
    simp [ptL, ptB, ptC, Matrix.cons_val_zero, Matrix.cons_val_one, PiLp.toLp_apply] <;>
    field_simp <;>
    ring

/-- K lies on the line AB (it is a scalar multiple of B). -/
lemma ptK_on_AB (b c α : ℝ) (hbc : b + c ≠ 0) :
    ptK b c α = (2 * b * cos α ^ 2 / (b + c)) • ptB c α := by
  ext i
  fin_cases i <;>
    simp [ptK, ptB, Matrix.cons_val_zero, Matrix.cons_val_one, PiLp.toLp_apply] <;>
    field_simp

/-- M lies on the line AC (it is a scalar multiple of C). -/
lemma ptM_on_AC (b c α : ℝ) (hbc : b + c ≠ 0) :
    ptM b c α = (2 * c * cos α ^ 2 / (b + c)) • ptC b α := by
  ext i
  fin_cases i <;>
    simp [ptM, ptC, Matrix.cons_val_zero, Matrix.cons_val_one, PiLp.toLp_apply] <;>
    field_simp

/-- LK is perpendicular to AB: the coordinate dot product
⟪B - A, L - K⟫ = (B-A)₀·(L-K)₀ + (B-A)₁·(L-K)₁ vanishes.
Together with `ptK_on_AB` this shows that K is the foot of the perpendicular
from L to AB. -/
lemma ptLK_perp_ptAB (b c α : ℝ) (hbc : b + c ≠ 0) :
    (ptB c α - ptA) 0 * (ptL b c α - ptK b c α) 0 +
      (ptB c α - ptA) 1 * (ptL b c α - ptK b c α) 1 = 0 := by
  simp [ptA, ptB, ptL, ptK, Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp
  linear_combination (-2 * b * c ^ 2 * cos α ^ 2) * (Real.sin_sq_add_cos_sq α)

/-- LM is perpendicular to AC. Together with `ptM_on_AC` this shows that M is
the foot of the perpendicular from L to AC. -/
lemma ptLM_perp_ptAC (b c α : ℝ) (hbc : b + c ≠ 0) :
    (ptC b α - ptA) 0 * (ptL b c α - ptM b c α) 0 +
      (ptC b α - ptA) 1 * (ptL b c α - ptM b c α) 1 = 0 := by
  simp [ptA, ptC, ptL, ptM, Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp
  linear_combination (-2 * b ^ 2 * c * cos α ^ 2) * (Real.sin_sq_add_cos_sq α)

/-- Point predicate: P lies on the circle x² + y² + D·x + E·y = 0
(a circle through the origin, hence no constant term). -/
def onCircle (P : EuclideanSpace ℝ (Fin 2)) (D E : ℝ) : Prop :=
  P 0 ^ 2 + P 1 ^ 2 + D * P 0 + E * P 1 = 0

/-- The x-coefficient of the circumcircle equation of ABC. -/
noncomputable def circleD (b c α : ℝ) : ℝ := -(b + c) / (2 * cos α)

/-- The y-coefficient of the circumcircle equation of ABC. -/
noncomputable def circleE (b c α : ℝ) : ℝ := (b - c) / (2 * sin α)

/-- The points A, B, C and N all lie on one circle, the circumcircle of ABC;
in particular N is indeed the second intersection of the bisector with the
circumcircle (N ≠ A since (b + c)/(2·cos α) > 0). -/
lemma pts_on_circumcircle (b c α : ℝ) (hcos : cos α ≠ 0) (hsin : sin α ≠ 0) :
    onCircle ptA (circleD b c α) (circleE b c α) ∧
      onCircle (ptB c α) (circleD b c α) (circleE b c α) ∧
        onCircle (ptC b α) (circleD b c α) (circleE b c α) ∧
          onCircle (ptN b c α) (circleD b c α) (circleE b c α) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [onCircle, ptA, Matrix.cons_val_zero, Matrix.cons_val_one]
  · simp [onCircle, circleD, circleE, ptB, Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp
    linear_combination (2 * c ^ 2) * (Real.sin_sq_add_cos_sq α)
  · simp [onCircle, circleD, circleE, ptC, Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp
    linear_combination (2 * b ^ 2) * (Real.sin_sq_add_cos_sq α)
  · simp [onCircle, circleD, circleE, ptN, Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp
    ring

/-- Twice the signed area of the quadrilateral AKNM and of the triangle ABC
coincide: both equal -2·b·c·sin α·cos α. This is the heart of the proof. -/
lemma twoArea_quad_eq_twoArea_triangle (b c α : ℝ) (hbc : b + c ≠ 0)
    (_hcos : cos α ≠ 0) :
    twoAreaQuad ptA (ptK b c α) (ptN b c α) (ptM b c α) =
      twoAreaTriangle ptA (ptB c α) (ptC b α) := by
  simp only [twoAreaQuad, twoAreaTriangle, ptA, ptK, ptN, ptM, ptB, ptC]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp
  ring

/-- Cosine is positive on (0, π/4). -/
lemma cos_pos_of_lt_pi_div_four {α : ℝ} (hα0 : 0 < α) (hα1 : α < π / 4) :
    0 < cos α := by
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> linarith [Real.pi_pos]

snip end

/-- **IMO 1987, Problem 2.** The quadrilateral AKNM and the triangle ABC have
equal areas. -/
problem imo1987_p2 (b c α : ℝ) (hb : 0 < b) (hc : 0 < c)
    (hα0 : 0 < α) (hα1 : α < Real.pi / 4) :
    quadArea ptA (ptK b c α) (ptN b c α) (ptM b c α) =
      triArea ptA (ptB c α) (ptC b α) := by
  have hbc : b + c ≠ 0 := ne_of_gt (add_pos hb hc)
  have hcos : cos α ≠ 0 := ne_of_gt (cos_pos_of_lt_pi_div_four hα0 hα1)
  simp only [quadArea, triArea, twoArea_quad_eq_twoArea_triangle b c α hbc hcos]

end Imo1987P2
