/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# USA Mathematical Olympiad 2003, Problem 2

A convex polygon P in the plane is dissected into smaller convex polygons
by drawing all of its diagonals. The lengths of all sides and all diagonals
of P are rational numbers. Prove that the lengths of all sides of all
polygons in the dissection are also rational numbers.
-/

local notation "Pt" => EuclideanSpace ℝ (Fin 2)

namespace Usa2003P2

snip begin

/-- Euclidean distance between two points of the plane, in coordinates. -/
lemma dist_eq_sqrt (X Y : Pt) :
    dist X Y = Real.sqrt ((X 0 - Y 0) ^ 2 + (X 1 - Y 1) ^ 2) := by
  simp only [EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq, sq_abs]

/-- If the distance between two points is rational, then so is the sum of
squares of the coordinate differences. -/
lemma sq_dist_eq {X Y : Pt} {q : ℚ} (h : dist X Y = q) :
    (X 0 - Y 0) ^ 2 + (X 1 - Y 1) ^ 2 = (q ^ 2 : ℚ) := by
  have h2 : (Real.sqrt ((X 0 - Y 0) ^ 2 + (X 1 - Y 1) ^ 2)) ^ 2 = (q : ℝ) ^ 2 := by
    rw [← dist_eq_sqrt, h]
  rw [Real.sq_sqrt (by positivity)] at h2
  rw [h2]
  norm_cast

snip end

/-
The full statement about dissections reduces to the following lemma about
four points, which is what we formalize as the main theorem.  Indeed, every
side of a small polygon in the dissection is a piece of a side or of a
diagonal of P, and every vertex of the dissection is either a vertex of P or
the crossing of two diagonals AC and BD, where A, B, C, D are four vertices
of P (in convex position).  If O = AC ∩ BD, the lemma below shows that
AO, OC, BO, OD are all rational.  Along any fixed diagonal of P, all
crossings therefore have rational distances from the endpoints of the
diagonal, hence rational distances from each other (differences of rational
numbers), so every segment of the dissection has rational length.

For the lemma, place the points in the plane and write
O = (1 - θ) • A + θ • C = (1 - φ) • B + φ • D.
Taking wedge products (u × v = u₀v₁ - u₁v₀) of the vector equation
θ • (C - A) - φ • (D - B) = B - A with (D - B) and with (C - A) gives
θ · w = p and φ · w = q₂, where
w = (C - A) × (D - B) ≠ 0 is the hypothesis that the diagonals are not
parallel (true for a genuine convex quadrilateral), p = (B - A) × (D - A)
and q₂ = (C - A) × (A - B).  The six rational distances make all dot
products of the edge vectors rational (law of cosines), and the 2D
Gram/Binet–Cauchy identities
  (x × y)² = (x·x)(y·y) - (x·y)²,
  (a × b)(c × d) = (a·c)(b·d) - (a·d)(b·c)
then show that p·w, q₂·w and w² are rational, hence so are
θ = p·w/w² and φ = q₂·w/w².  Finally
AO = θ·AC, OC = (1 - θ)·AC, BO = φ·BD, OD = (1 - φ)·BD are rational.
(This is a coordinate-free version of the standard official solution, which
uses rational cosines and the formula sin x sin y = cos x cos y - cos(x+y).)
-/

problem usa2003_p2 {A B C D O : Pt}
    (hAB : ∃ q : ℚ, dist A B = q) (hBC : ∃ q : ℚ, dist B C = q)
    (hCD : ∃ q : ℚ, dist C D = q) (hDA : ∃ q : ℚ, dist D A = q)
    (hAC : ∃ q : ℚ, dist A C = q) (hBD : ∃ q : ℚ, dist B D = q)
    (hw : (C 0 - A 0) * (D 1 - B 1) - (C 1 - A 1) * (D 0 - B 0) ≠ 0)
    (hOAC : O ∈ segment ℝ A C) (hOBD : O ∈ segment ℝ B D) :
    (∃ q : ℚ, dist A O = q) ∧ (∃ q : ℚ, dist O C = q) ∧
    (∃ q : ℚ, dist B O = q) ∧ (∃ q : ℚ, dist O D = q) := by
  -- Step 1: parametrize the position of O on the two diagonals.
  rw [segment_eq_image] at hOAC hOBD
  obtain ⟨θ, ⟨hθ0, hθ1⟩, hOθ⟩ := hOAC
  obtain ⟨φ, ⟨hφ0, hφ1⟩, hOφ⟩ := hOBD
  change (1 - θ) • A + θ • C = O at hOθ
  change (1 - φ) • B + φ • D = O at hOφ
  have hvec : (1 - θ) • A + θ • C = (1 - φ) • B + φ • D := hOθ.trans hOφ.symm
  have e0 := congrArg (fun v : Pt ↦ v 0) hvec
  have e1 := congrArg (fun v : Pt ↦ v 1) hvec
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at e0 e1
  -- Step 2: Cramer-style determinant equations for θ and φ.
  have hθw : θ * ((C 0 - A 0) * (D 1 - B 1) - (C 1 - A 1) * (D 0 - B 0))
      = (B 0 - A 0) * (D 1 - A 1) - (B 1 - A 1) * (D 0 - A 0) := by
    linear_combination (D 1 - B 1) * e0 - (D 0 - B 0) * e1
  have hφw : φ * ((C 0 - A 0) * (D 1 - B 1) - (C 1 - A 1) * (D 0 - B 0))
      = (C 0 - A 0) * (A 1 - B 1) - (C 1 - A 1) * (A 0 - B 0) := by
    linear_combination (C 1 - A 1) * e0 - (C 0 - A 0) * e1
  have hθ2 : θ * ((C 0 - A 0) * (D 1 - B 1) - (C 1 - A 1) * (D 0 - B 0)) ^ 2
      = ((B 0 - A 0) * (D 1 - A 1) - (B 1 - A 1) * (D 0 - A 0))
        * ((C 0 - A 0) * (D 1 - B 1) - (C 1 - A 1) * (D 0 - B 0)) := by
    rw [← hθw]; ring
  have hφ2 : φ * ((C 0 - A 0) * (D 1 - B 1) - (C 1 - A 1) * (D 0 - B 0)) ^ 2
      = ((C 0 - A 0) * (A 1 - B 1) - (C 1 - A 1) * (A 0 - B 0))
        * ((C 0 - A 0) * (D 1 - B 1) - (C 1 - A 1) * (D 0 - B 0)) := by
    rw [← hφw]; ring
  -- Step 3: the six squared distances are squares of rationals.
  obtain ⟨qAB, hqAB⟩ := hAB
  obtain ⟨qBC, hqBC⟩ := hBC
  obtain ⟨qCD, hqCD⟩ := hCD
  obtain ⟨qDA, hqDA⟩ := hDA
  obtain ⟨qAC, hqAC⟩ := hAC
  obtain ⟨qBD, hqBD⟩ := hBD
  have hsqAB := sq_dist_eq hqAB
  have hsqBC := sq_dist_eq hqBC
  have hsqCD := sq_dist_eq hqCD
  have hsqDA := sq_dist_eq hqDA
  have hsqAC := sq_dist_eq hqAC
  have hsqBD := sq_dist_eq hqBD
  -- Step 4: dot products of the edge vectors are rational (law of cosines).
  have hbc : (B 0 - A 0) * (C 0 - A 0) + (B 1 - A 1) * (C 1 - A 1)
      = ((qAB ^ 2 + qAC ^ 2 - qBC ^ 2) / 2 : ℚ) := by
    have e : 2 * ((B 0 - A 0) * (C 0 - A 0) + (B 1 - A 1) * (C 1 - A 1))
        = ((A 0 - B 0) ^ 2 + (A 1 - B 1) ^ 2) + ((A 0 - C 0) ^ 2 + (A 1 - C 1) ^ 2)
          - ((B 0 - C 0) ^ 2 + (B 1 - C 1) ^ 2) := by ring
    rw [hsqAB, hsqAC, hsqBC] at e
    push_cast
    push_cast at e
    linarith
  have hbd : (B 0 - A 0) * (D 0 - A 0) + (B 1 - A 1) * (D 1 - A 1)
      = ((qAB ^ 2 + qDA ^ 2 - qBD ^ 2) / 2 : ℚ) := by
    have e : 2 * ((B 0 - A 0) * (D 0 - A 0) + (B 1 - A 1) * (D 1 - A 1))
        = ((A 0 - B 0) ^ 2 + (A 1 - B 1) ^ 2) + ((D 0 - A 0) ^ 2 + (D 1 - A 1) ^ 2)
          - ((B 0 - D 0) ^ 2 + (B 1 - D 1) ^ 2) := by ring
    rw [hsqAB, hsqDA, hsqBD] at e
    push_cast
    push_cast at e
    linarith
  have hcd : (C 0 - A 0) * (D 0 - A 0) + (C 1 - A 1) * (D 1 - A 1)
      = ((qAC ^ 2 + qDA ^ 2 - qCD ^ 2) / 2 : ℚ) := by
    have e : 2 * ((C 0 - A 0) * (D 0 - A 0) + (C 1 - A 1) * (D 1 - A 1))
        = ((A 0 - C 0) ^ 2 + (A 1 - C 1) ^ 2) + ((D 0 - A 0) ^ 2 + (D 1 - A 1) ^ 2)
          - ((C 0 - D 0) ^ 2 + (C 1 - D 1) ^ 2) := by ring
    rw [hsqAC, hsqDA, hsqCD] at e
    push_cast
    push_cast at e
    linarith
  have hbb : (B 0 - A 0) ^ 2 + (B 1 - A 1) ^ 2 = ((qAB ^ 2 : ℚ) : ℝ) := by
    linear_combination hsqAB
  have hcc : (C 0 - A 0) ^ 2 + (C 1 - A 1) ^ 2 = ((qAC ^ 2 : ℚ) : ℝ) := by
    linear_combination hsqAC
  have hdd : (D 0 - A 0) ^ 2 + (D 1 - A 1) ^ 2 = ((qDA ^ 2 : ℚ) : ℝ) := by
    linear_combination hsqDA
  -- Step 5: Gram/Binet–Cauchy identities: the needed wedge products
  -- (times w or squared) are rational.
  have hpw : ((B 0 - A 0) * (D 1 - A 1) - (B 1 - A 1) * (D 0 - A 0))
        * ((C 0 - A 0) * (D 1 - B 1) - (C 1 - A 1) * (D 0 - B 0))
      = ((qAB ^ 2 + qAC ^ 2 - qBC ^ 2) / 2 * qDA ^ 2
        - (qAB ^ 2 + qDA ^ 2 - qBD ^ 2) / 2 * ((qAC ^ 2 + qDA ^ 2 - qCD ^ 2) / 2)
        - ((qAB ^ 2 + qAC ^ 2 - qBC ^ 2) / 2 * ((qAB ^ 2 + qDA ^ 2 - qBD ^ 2) / 2)
          - qAB ^ 2 * ((qAC ^ 2 + qDA ^ 2 - qCD ^ 2) / 2)) : ℚ) := by
    trans (((B 0 - A 0) * (C 0 - A 0) + (B 1 - A 1) * (C 1 - A 1))
        * ((D 0 - A 0) ^ 2 + (D 1 - A 1) ^ 2)
      - ((B 0 - A 0) * (D 0 - A 0) + (B 1 - A 1) * (D 1 - A 1))
        * ((C 0 - A 0) * (D 0 - A 0) + (C 1 - A 1) * (D 1 - A 1))
      - (((B 0 - A 0) * (C 0 - A 0) + (B 1 - A 1) * (C 1 - A 1))
          * ((B 0 - A 0) * (D 0 - A 0) + (B 1 - A 1) * (D 1 - A 1))
        - ((B 0 - A 0) ^ 2 + (B 1 - A 1) ^ 2)
          * ((C 0 - A 0) * (D 0 - A 0) + (C 1 - A 1) * (D 1 - A 1))))
    · ring
    · rw [hbc, hbd, hcd, hbb, hdd]
      push_cast
      ring
  have hw2 : ((C 0 - A 0) * (D 1 - B 1) - (C 1 - A 1) * (D 0 - B 0)) ^ 2
      = (qAC ^ 2 * qDA ^ 2 - ((qAC ^ 2 + qDA ^ 2 - qCD ^ 2) / 2) ^ 2
        - 2 * (qAC ^ 2 * ((qAB ^ 2 + qDA ^ 2 - qBD ^ 2) / 2)
          - (qAB ^ 2 + qAC ^ 2 - qBC ^ 2) / 2 * ((qAC ^ 2 + qDA ^ 2 - qCD ^ 2) / 2))
        + (qAC ^ 2 * qAB ^ 2 - ((qAB ^ 2 + qAC ^ 2 - qBC ^ 2) / 2) ^ 2) : ℚ) := by
    trans ((((C 0 - A 0) ^ 2 + (C 1 - A 1) ^ 2) * ((D 0 - A 0) ^ 2 + (D 1 - A 1) ^ 2)
        - ((C 0 - A 0) * (D 0 - A 0) + (C 1 - A 1) * (D 1 - A 1)) ^ 2)
      - 2 * (((C 0 - A 0) ^ 2 + (C 1 - A 1) ^ 2)
          * ((B 0 - A 0) * (D 0 - A 0) + (B 1 - A 1) * (D 1 - A 1))
        - ((B 0 - A 0) * (C 0 - A 0) + (B 1 - A 1) * (C 1 - A 1))
          * ((C 0 - A 0) * (D 0 - A 0) + (C 1 - A 1) * (D 1 - A 1)))
      + (((C 0 - A 0) ^ 2 + (C 1 - A 1) ^ 2) * ((B 0 - A 0) ^ 2 + (B 1 - A 1) ^ 2)
        - ((B 0 - A 0) * (C 0 - A 0) + (B 1 - A 1) * (C 1 - A 1)) ^ 2))
    · ring
    · rw [hcc, hdd, hcd, hbd, hbc, hbb]
      push_cast
      ring
  have hq2w : ((C 0 - A 0) * (A 1 - B 1) - (C 1 - A 1) * (A 0 - B 0))
        * ((C 0 - A 0) * (D 1 - B 1) - (C 1 - A 1) * (D 0 - B 0))
      = (qAC ^ 2 * qAB ^ 2 - ((qAB ^ 2 + qAC ^ 2 - qBC ^ 2) / 2) ^ 2
        - (qAC ^ 2 * ((qAB ^ 2 + qDA ^ 2 - qBD ^ 2) / 2)
          - (qAB ^ 2 + qAC ^ 2 - qBC ^ 2) / 2 * ((qAC ^ 2 + qDA ^ 2 - qCD ^ 2) / 2)) : ℚ) := by
    trans ((((C 0 - A 0) ^ 2 + (C 1 - A 1) ^ 2) * ((B 0 - A 0) ^ 2 + (B 1 - A 1) ^ 2)
        - ((B 0 - A 0) * (C 0 - A 0) + (B 1 - A 1) * (C 1 - A 1)) ^ 2)
      - (((C 0 - A 0) ^ 2 + (C 1 - A 1) ^ 2)
          * ((B 0 - A 0) * (D 0 - A 0) + (B 1 - A 1) * (D 1 - A 1))
        - ((B 0 - A 0) * (C 0 - A 0) + (B 1 - A 1) * (C 1 - A 1))
          * ((C 0 - A 0) * (D 0 - A 0) + (C 1 - A 1) * (D 1 - A 1))))
    · ring
    · rw [hcc, hbb, hbc, hbd, hcd]
      push_cast
      ring
  -- Step 6: θ and φ are rational.
  have hθq : ∃ t : ℚ, θ = t := by
    refine ⟨((qAB ^ 2 + qAC ^ 2 - qBC ^ 2) / 2 * qDA ^ 2
      - (qAB ^ 2 + qDA ^ 2 - qBD ^ 2) / 2 * ((qAC ^ 2 + qDA ^ 2 - qCD ^ 2) / 2)
      - ((qAB ^ 2 + qAC ^ 2 - qBC ^ 2) / 2 * ((qAB ^ 2 + qDA ^ 2 - qBD ^ 2) / 2)
        - qAB ^ 2 * ((qAC ^ 2 + qDA ^ 2 - qCD ^ 2) / 2)))
      / (qAC ^ 2 * qDA ^ 2 - ((qAC ^ 2 + qDA ^ 2 - qCD ^ 2) / 2) ^ 2
        - 2 * (qAC ^ 2 * ((qAB ^ 2 + qDA ^ 2 - qBD ^ 2) / 2)
          - (qAB ^ 2 + qAC ^ 2 - qBC ^ 2) / 2 * ((qAC ^ 2 + qDA ^ 2 - qCD ^ 2) / 2))
        + (qAC ^ 2 * qAB ^ 2 - ((qAB ^ 2 + qAC ^ 2 - qBC ^ 2) / 2) ^ 2)), ?_⟩
    rw [Rat.cast_div, ← hw2, ← hpw, ← hθ2, mul_div_cancel_right₀ θ (pow_ne_zero 2 hw)]
  have hφq : ∃ t : ℚ, φ = t := by
    refine ⟨(qAC ^ 2 * qAB ^ 2 - ((qAB ^ 2 + qAC ^ 2 - qBC ^ 2) / 2) ^ 2
      - (qAC ^ 2 * ((qAB ^ 2 + qDA ^ 2 - qBD ^ 2) / 2)
        - (qAB ^ 2 + qAC ^ 2 - qBC ^ 2) / 2 * ((qAC ^ 2 + qDA ^ 2 - qCD ^ 2) / 2)))
      / (qAC ^ 2 * qDA ^ 2 - ((qAC ^ 2 + qDA ^ 2 - qCD ^ 2) / 2) ^ 2
        - 2 * (qAC ^ 2 * ((qAB ^ 2 + qDA ^ 2 - qBD ^ 2) / 2)
          - (qAB ^ 2 + qAC ^ 2 - qBC ^ 2) / 2 * ((qAC ^ 2 + qDA ^ 2 - qCD ^ 2) / 2))
        + (qAC ^ 2 * qAB ^ 2 - ((qAB ^ 2 + qAC ^ 2 - qBC ^ 2) / 2) ^ 2)), ?_⟩
    rw [Rat.cast_div, ← hw2, ← hq2w, ← hφ2, mul_div_cancel_right₀ φ (pow_ne_zero 2 hw)]
  obtain ⟨θq, hθq⟩ := hθq
  obtain ⟨φq, hφq⟩ := hφq
  -- Step 7: the four distances scale by θ and φ along the diagonals.
  have hdAO : dist A O = θ * dist A C := by
    rw [← hOθ, dist_eq_norm, dist_eq_norm]
    have e : A - ((1 - θ) • A + θ • C) = θ • (A - C) := by module
    rw [e, norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ0]
  have hdOC : dist O C = (1 - θ) * dist A C := by
    rw [← hOθ, dist_eq_norm, dist_eq_norm]
    have e : (1 - θ) • A + θ • C - C = (1 - θ) • (A - C) := by module
    rw [e, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - θ)]
  have hdBO : dist B O = φ * dist B D := by
    rw [← hOφ, dist_eq_norm, dist_eq_norm]
    have e : B - ((1 - φ) • B + φ • D) = φ • (B - D) := by module
    rw [e, norm_smul, Real.norm_eq_abs, abs_of_nonneg hφ0]
  have hdOD : dist O D = (1 - φ) * dist B D := by
    rw [← hOφ, dist_eq_norm, dist_eq_norm]
    have e : (1 - φ) • B + φ • D - D = (1 - φ) • (B - D) := by module
    rw [e, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - φ)]
  refine ⟨⟨θq * qAC, ?_⟩, ⟨(1 - θq) * qAC, ?_⟩, ⟨φq * qBD, ?_⟩, ⟨(1 - φq) * qBD, ?_⟩⟩
  · rw [hdAO, hθq, hqAC]; push_cast; ring
  · rw [hdOC, hθq, hqAC]; push_cast; ring
  · rw [hdBO, hφq, hqBD]; push_cast; ring
  · rw [hdOD, hφq, hqBD]; push_cast; ring

end Usa2003P2
