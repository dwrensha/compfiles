/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 1989, Problem 2

In an acute-angled triangle ABC, the internal bisector of angle A meets the
circumcircle again at A₁. Points B₁ and C₁ are defined similarly. Let A₀ be the
point of intersection of the line AA₁ with the external bisectors of angles B
and C. Points B₀ and C₀ are defined similarly. Prove that the area of the
triangle A₀B₀C₀ is twice the area of the hexagon AC₁BA₁CB₁ and at least four
times the area of the triangle ABC.

The proof below is after the solution by Marcin Mazur and Thomas Jäger, via
kalva.
-/

namespace Imo1989P2

open Real

snip begin

/-- Twice the signed area of the triangle PQR (shoelace formula). -/
def twoAreaTriangle (P Q R : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  (Q 0 - P 0) * (R 1 - P 1) - (R 0 - P 0) * (Q 1 - P 1)

/-- Twice the signed area of the hexagon P₁P₂P₃P₄P₅P₆ (shoelace formula). -/
def twoAreaHex (P₁ P₂ P₃ P₄ P₅ P₆ : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  (P₁ 0 * P₂ 1 - P₁ 1 * P₂ 0) + (P₂ 0 * P₃ 1 - P₂ 1 * P₃ 0) +
    (P₃ 0 * P₄ 1 - P₃ 1 * P₄ 0) + (P₄ 0 * P₅ 1 - P₄ 1 * P₅ 0) +
      (P₅ 0 * P₆ 1 - P₅ 1 * P₆ 0) + (P₆ 0 * P₁ 1 - P₆ 1 * P₁ 0)

/-- The area of a triangle given by its vertices. -/
noncomputable def triArea (P Q R : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  |twoAreaTriangle P Q R| / 2

/-- The area of a (simple) hexagon given by its vertices in order. -/
noncomputable def hexArea (P₁ P₂ P₃ P₄ P₅ P₆ : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  |twoAreaHex P₁ P₂ P₃ P₄ P₅ P₆| / 2

/-- The point at angle `θ` on the circle of radius `R` centered at the origin. -/
noncomputable def circ (R θ : ℝ) : EuclideanSpace ℝ (Fin 2) := !₂[R * cos θ, R * sin θ]

/-- Vertex A, at angle `β − γ + π` on the circumcircle. -/
noncomputable def ptA (R β γ : ℝ) : EuclideanSpace ℝ (Fin 2) := circ R (β - γ + π)

/-- Vertex B, at angle `β + γ + π` on the circumcircle. -/
noncomputable def ptB (R β γ : ℝ) : EuclideanSpace ℝ (Fin 2) := circ R (β + γ + π)

/-- Vertex C, at angle `π − β − γ` on the circumcircle. -/
noncomputable def ptC (R β γ : ℝ) : EuclideanSpace ℝ (Fin 2) := circ R (π - β - γ)

/-- The midpoint A₁ of the arc BC not containing A, placed at angle 0. -/
noncomputable def ptA₁ (R : ℝ) : EuclideanSpace ℝ (Fin 2) := circ R 0

/-- The midpoint B₁ of the arc CA not containing B, at angle `π − γ`. -/
noncomputable def ptB₁ (R γ : ℝ) : EuclideanSpace ℝ (Fin 2) := circ R (π - γ)

/-- The midpoint C₁ of the arc AB not containing C, at angle `β + π`. -/
noncomputable def ptC₁ (R β : ℝ) : EuclideanSpace ℝ (Fin 2) := circ R (β + π)

/-- The excenter A₀ opposite A (the meeting point of the line AA₁ with the
external bisectors of angles B and C). -/
noncomputable def ptA₀ (R β γ : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  !₂[R * (1 + cos β + cos γ), R * (sin β - sin γ)]

/-- The excenter B₀ opposite B. -/
noncomputable def ptB₀ (R β γ : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  !₂[R * (cos β - cos γ - 1), R * (sin β + sin γ)]

/-- The excenter C₀ opposite C. -/
noncomputable def ptC₀ (R β γ : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  !₂[R * (cos γ - cos β - 1), -(R * (sin β + sin γ))]

/-- The cross product of two circle points is `R²` times the sine of the
angle difference; this drives the hexagon shoelace computation. -/
lemma circ_cross (R u v : ℝ) :
    circ R u 0 * circ R v 1 - circ R u 1 * circ R v 0 = R ^ 2 * sin (v - u) := by
  simp [circ, Matrix.cons_val_zero, Matrix.cons_val_one, PiLp.toLp_apply]
  rw [sin_sub]
  ring

/-- Twice the signed area of ABC. -/
lemma twoAreaTriangle_abc (R β γ : ℝ) :
    twoAreaTriangle (ptA R β γ) (ptB R β γ) (ptC R β γ) =
      4 * R ^ 2 * sin β * sin γ * sin (β + γ) := by
  have eπ : π - β - γ = π - (β + γ) := by ring
  simp only [twoAreaTriangle, ptA, ptB, ptC, circ, Matrix.cons_val_zero,
    Matrix.cons_val_one, PiLp.toLp_apply]
  rw [eπ]
  simp only [cos_add_pi, sin_add_pi, cos_pi_sub, sin_pi_sub]
  simp only [cos_sub, sin_sub, cos_add, sin_add]
  ring

/-- Twice the signed area of the excentral triangle A₀B₀C₀. -/
lemma twoAreaTriangle_exc (R β γ : ℝ) :
    twoAreaTriangle (ptA₀ R β γ) (ptB₀ R β γ) (ptC₀ R β γ) =
      4 * R ^ 2 * (sin β + sin γ + sin (β + γ)) := by
  simp only [twoAreaTriangle, ptA₀, ptB₀, ptC₀, Matrix.cons_val_zero,
    Matrix.cons_val_one, PiLp.toLp_apply]
  simp only [sin_add]
  ring

/-- Twice the signed area of the hexagon AC₁BA₁CB₁. The vertices lie on the
circumcircle in this (counterclockwise) order, so each shoelace cross term is
`R²` times the sine of an arc, giving `2R²(sin α + sin β + sin γ)`. -/
lemma twoAreaHex_pts (R β γ : ℝ) :
    twoAreaHex (ptA R β γ) (ptC₁ R β) (ptB R β γ) (ptA₁ R) (ptC R β γ)
        (ptB₁ R γ) =
      2 * R ^ 2 * (sin β + sin γ + sin (β + γ)) := by
  simp only [twoAreaHex, ptA, ptC₁, ptB, ptA₁, ptC, ptB₁]
  rw [circ_cross, circ_cross, circ_cross, circ_cross, circ_cross, circ_cross]
  have e1 : β + π - (β - γ + π) = γ := by ring
  have e2 : β + γ + π - (β + π) = γ := by ring
  have e4 : π - β - γ - 0 = π - (β + γ) := by ring
  have e5 : π - γ - (π - β - γ) = β := by ring
  have e6 : β - γ + π - (π - γ) = β := by ring
  rw [e1, e2, e4, e5, e6, zero_sub, sin_neg, sin_add_pi, sin_pi_sub, neg_neg]
  ring

/-- Product of sines of two half-angles in terms of cosines. -/
lemma sin_half_mul_sin_half (β γ : ℝ) :
    sin (β / 2) * sin (γ / 2) = (cos (β / 2 - γ / 2) - cos (β / 2 + γ / 2)) / 2 := by
  rw [cos_sub, cos_add]
  ring

/-- The product of the sines of the half-angles of a triangle is at most 1/8
(equivalently `r ≤ R / 2`, a form of Euler's inequality). -/
lemma half_prod_le (α β γ : ℝ) (h : α + β + γ = π) (hα : 0 < α) (hβ : 0 < β)
    (hγ : 0 < γ) :
    sin (α / 2) * sin (β / 2) * sin (γ / 2) ≤ 1 / 8 := by
  have hαπ : α < π := by linarith
  have hα2 : 0 < sin (α / 2) := Real.sin_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hbc := sin_half_mul_sin_half β γ
  have hsum : β / 2 + γ / 2 = π / 2 - α / 2 := by linarith
  have hcos : cos (β / 2 + γ / 2) = sin (α / 2) := by rw [hsum, cos_pi_div_two_sub]
  have h1 : sin (β / 2) * sin (γ / 2) ≤ (1 - sin (α / 2)) / 2 := by
    rw [hbc, hcos]
    linarith [Real.cos_le_one (β / 2 - γ / 2)]
  calc sin (α / 2) * sin (β / 2) * sin (γ / 2)
      = sin (α / 2) * (sin (β / 2) * sin (γ / 2)) := by ring
    _ ≤ sin (α / 2) * ((1 - sin (α / 2)) / 2) :=
        mul_le_mul_of_nonneg_left h1 (le_of_lt hα2)
    _ ≤ 1 / 8 := by nlinarith [sq_nonneg (sin (α / 2) - 1 / 2)]

/-- The sum of the sines of the angles of a triangle. -/
lemma sum_sin_eq (α β γ : ℝ) (h : α + β + γ = π) :
    sin α + sin β + sin γ = 4 * cos (α / 2) * cos (β / 2) * cos (γ / 2) := by
  have e1 : sin α + sin β = 2 * sin ((α + β) / 2) * cos ((α - β) / 2) :=
    Real.sin_add_sin α β
  have h1 : (α + β) / 2 = π / 2 - γ / 2 := by linarith
  have h2 : sin ((α + β) / 2) = cos (γ / 2) := by rw [h1, sin_pi_div_two_sub]
  have e3 : sin γ = 2 * sin (γ / 2) * cos (γ / 2) := by
    rw [← sin_two_mul]
    congr 1
    ring
  have h4 : sin (γ / 2) = cos ((α + β) / 2) := by
    have h41 : γ / 2 = π / 2 - (α + β) / 2 := by linarith
    rw [h41, sin_pi_div_two_sub]
  have e5 : cos ((α - β) / 2) + cos ((α + β) / 2) = 2 * cos (α / 2) * cos (β / 2) := by
    rw [Real.cos_add_cos]
    have g1 : ((α - β) / 2 + (α + β) / 2) / 2 = α / 2 := by ring
    have g2 : ((α - β) / 2 - (α + β) / 2) / 2 = -(β / 2) := by ring
    rw [g1, g2, cos_neg]
  calc sin α + sin β + sin γ
      = 2 * sin ((α + β) / 2) * cos ((α - β) / 2) + sin γ := by rw [e1]
    _ = 2 * cos (γ / 2) * cos ((α - β) / 2) + 2 * sin (γ / 2) * cos (γ / 2) := by
        rw [h2, e3]
    _ = 2 * cos (γ / 2) * (cos ((α - β) / 2) + cos ((α + β) / 2)) := by rw [h4]; ring
    _ = 2 * cos (γ / 2) * (2 * cos (α / 2) * cos (β / 2)) := by rw [e5]
    _ = 4 * cos (α / 2) * cos (β / 2) * cos (γ / 2) := by ring

/-- The product of the sines of the angles of a triangle, in half-angles. -/
lemma prod_sin_eq (α β γ : ℝ) :
    4 * (sin α * sin β * sin γ) =
      32 * (sin (α / 2) * sin (β / 2) * sin (γ / 2)) *
        (cos (α / 2) * cos (β / 2) * cos (γ / 2)) := by
  have eα : sin α = 2 * sin (α / 2) * cos (α / 2) := by
    rw [← sin_two_mul]
    congr 1
    ring
  have eβ : sin β = 2 * sin (β / 2) * cos (β / 2) := by
    rw [← sin_two_mul]
    congr 1
    ring
  have eγ : sin γ = 2 * sin (γ / 2) * cos (γ / 2) := by
    rw [← sin_two_mul]
    congr 1
    ring
  rw [eα, eβ, eγ]
  ring

/-- The trigonometric form of the second claim: with `α = π − β − γ` this is
`sin α + sin β + sin γ ≥ 4 sin α sin β sin γ`. -/
lemma trig_ineq (β γ : ℝ) (hβ : 0 < β) (hγ : 0 < γ) (hsum : β + γ < π) :
    4 * (sin β * sin γ * sin (β + γ)) ≤ sin β + sin γ + sin (β + γ) := by
  set α := π - β - γ with hαdef
  have h : α + β + γ = π := by rw [hαdef]; ring
  have hα : 0 < α := by rw [hαdef]; linarith
  have hαπ : α < π := by rw [hαdef]; linarith
  have hβπ : β < π := by linarith
  have hγπ : γ < π := by linarith
  have hsinα : sin α = sin (β + γ) := by
    rw [hαdef]
    have e : π - β - γ = π - (β + γ) := by ring
    rw [e, sin_pi_sub]
  have hsum' := sum_sin_eq α β γ h
  have hprod' := prod_sin_eq α β γ
  have hhalf := half_prod_le α β γ h hα hβ hγ
  rw [hsinα] at hsum' hprod'
  have c1 : 0 < cos (α / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have c2 : 0 < cos (β / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have c3 : 0 < cos (γ / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hcospos : 0 < cos (α / 2) * cos (β / 2) * cos (γ / 2) := mul_pos (mul_pos c1 c2) c3
  have hsc := mul_le_mul_of_nonneg_right hhalf (le_of_lt hcospos)
  nlinarith [hsum', hprod', hsc]

snip end

/-- **IMO 1989, Problem 2.** The area of A₀B₀C₀ is twice the area of the
hexagon AC₁BA₁CB₁ and at least four times the area of ABC. -/
problem imo1989_p2 (R β γ : ℝ) (hR : 0 < R) (hβ : 0 < β) (hγ : 0 < γ)
    (hβ' : β < Real.pi / 2) (hγ' : γ < Real.pi / 2)
    (hacute : Real.pi / 2 < β + γ) (hsum : β + γ < Real.pi) :
    triArea (ptA₀ R β γ) (ptB₀ R β γ) (ptC₀ R β γ) =
        2 * hexArea (ptA R β γ) (ptC₁ R β) (ptB R β γ) (ptA₁ R) (ptC R β γ)
          (ptB₁ R γ) ∧
      4 * triArea (ptA R β γ) (ptB R β γ) (ptC R β γ) ≤
        triArea (ptA₀ R β γ) (ptB₀ R β γ) (ptC₀ R β γ) := by
  have hsβ : 0 < sin β := Real.sin_pos_of_mem_Ioo ⟨hβ, by linarith⟩
  have hsγ : 0 < sin γ := Real.sin_pos_of_mem_Ioo ⟨hγ, by linarith⟩
  have hsβγ : 0 < sin (β + γ) :=
    Real.sin_pos_of_mem_Ioo ⟨lt_trans (by positivity) hacute, hsum⟩
  have hS : 0 < sin β + sin γ + sin (β + γ) := by linarith [hsβ, hsγ, hsβγ]
  have e1 := twoAreaTriangle_abc R β γ
  have e2 := twoAreaTriangle_exc R β γ
  have e3 := twoAreaHex_pts R β γ
  have pos1 : 0 < 4 * R ^ 2 * sin β * sin γ * sin (β + γ) := by positivity
  have pos2 : 0 < 4 * R ^ 2 * (sin β + sin γ + sin (β + γ)) := by positivity
  have pos3 : 0 < 2 * R ^ 2 * (sin β + sin γ + sin (β + γ)) := by positivity
  simp only [triArea, hexArea]
  rw [e1, e2, e3, abs_of_pos pos1, abs_of_pos pos2, abs_of_pos pos3]
  refine ⟨by ring, ?_⟩
  have key := trig_ineq β γ hβ hγ hsum
  have hR2 : (0 : ℝ) ≤ R ^ 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_left key hR2
  nlinarith [hmul]

end Imo1989P2
