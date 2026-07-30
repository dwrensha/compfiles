/-
Copyright (c) 2026 The Compfiles Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.RightAngle
public import Mathlib.Tactic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 1960, Problem 7

In the isosceles trapezoid ABCD (AB parallel to DC, and BC = AD), let AB = a,
CD = c and let the perpendicular distance from A to CD be h. Show how to
construct all points X on the axis of symmetry such that ∠BXC = ∠AXD = 90°.
Find the distance of each such X from AB and from CD. What is the condition
for such points to exist?

# Solution

Place the trapezoid in the plane so that its axis of symmetry is the y-axis
and the line AB is the x-axis:
A = (-a/2, 0), B = (a/2, 0), C = (c/2, h), D = (-c/2, h).
This is no loss of generality: any isosceles trapezoid can be moved to this
position by a rigid motion, and rigid motions preserve angles and distances.
A point X of the axis of symmetry has the form X = (0, t), where t is its
distance from AB and h - t is its distance from CD.

The condition ∠BXC = 90° is (B - X) · (C - X) = 0, i.e.
t² - ht + ac/4 = 0, and by symmetry the same equation expresses ∠AXD = 90°.
Hence t = (h ± √(h² - ac))/2, and such points exist if and only if
ac ≤ h². (Construction: intersect the axis of symmetry with the circle of
diameter BC, equivalently AD.)
-/

namespace Imo1960P7

open scoped EuclideanGeometry RealInnerProductSpace

/-- The Euclidean plane. -/
abbrev Pt := EuclideanSpace ℝ (Fin 2)

/-- Vertex A of the trapezoid. -/
noncomputable def A (a : ℝ) : Pt := !₂[(-a) / 2, 0]

/-- Vertex B of the trapezoid. -/
noncomputable def B (a : ℝ) : Pt := !₂[a / 2, 0]

/-- Vertex C of the trapezoid. -/
noncomputable def C (c h : ℝ) : Pt := !₂[c / 2, h]

/-- Vertex D of the trapezoid. -/
noncomputable def D (c h : ℝ) : Pt := !₂[(-c) / 2, h]

/-- A point X on the axis of symmetry (the y-axis);
`t` is its distance from the line AB. -/
noncomputable def X (t : ℝ) : Pt := !₂[0, t]

/-- The answer: the distances of the points X from the line AB are
`(h + √(h² - ac))/2` and `(h - √(h² - ac))/2`. -/
determine SolutionDistances (a c h : ℝ) : Set ℝ :=
  {t | t = (h + Real.sqrt (h^2 - a * c)) / 2 ∨ t = (h - Real.sqrt (h^2 - a * c)) / 2}

snip begin

theorem Pt.ext {x y : Pt} (h0 : x 0 = y 0) (h1 : x 1 = y 1) : x = y := by
  apply WithLp.ofLp_injective (p := 2)
  funext i
  fin_cases i <;> assumption

/-- Inner product in coordinates. -/
theorem inner_pt (u v : Pt) : ⟪u, v⟫ = u 0 * v 0 + u 1 * v 1 := by
  rw [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, RCLike.inner_apply]
  simp only [conj_trivial]
  ring

/-- The right angle condition ∠BXC = 90° as an equation in `t`. -/
theorem inner_BX_CX (a c h t : ℝ) :
    ⟪B a -ᵥ X t, C c h -ᵥ X t⟫ = t^2 - h * t + a * c / 4 := by
  rw [inner_pt]
  simp [B, C, X]
  ring

/-- The right angle condition ∠AXD = 90° gives the same equation. -/
theorem inner_AX_DX (a c h t : ℝ) :
    ⟪A a -ᵥ X t, D c h -ᵥ X t⟫ = t^2 - h * t + a * c / 4 := by
  rw [inner_pt]
  simp [A, D, X]
  ring

/-- ∠BXC = 90° if and only if `t` satisfies the quadratic equation. -/
theorem angle_BXC_iff (a c h t : ℝ) :
    ∠ (B a) (X t) (C c h) = Real.pi / 2 ↔ t^2 - h * t + a * c / 4 = 0 := by
  rw [EuclideanGeometry.angle, ← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two,
    inner_BX_CX]

/-- ∠AXD = 90° if and only if `t` satisfies the same quadratic equation. -/
theorem angle_AXD_iff (a c h t : ℝ) :
    ∠ (A a) (X t) (D c h) = Real.pi / 2 ↔ t^2 - h * t + a * c / 4 = 0 := by
  rw [EuclideanGeometry.angle, ← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two,
    inner_AX_DX]

/-- The quadratic equation factors using `s = √(h² - ac)`. -/
theorem quad_factor (a c h t s : ℝ) (hs : s^2 = h^2 - a * c) :
    t^2 - h * t + a * c / 4 = (t - (h + s) / 2) * (t - (h - s) / 2) := by
  linear_combination hs / 4

/-- Solving the quadratic equation: there is a real solution iff `ac ≤ h²`,
and then the solutions are `(h ± √(h² - ac))/2`. -/
theorem quad_eq_iff (a c h t : ℝ) :
    t^2 - h * t + a * c / 4 = 0 ↔ a * c ≤ h^2 ∧ t ∈ SolutionDistances a c h := by
  constructor
  · intro ht
    have hle : a * c ≤ h^2 := by nlinarith [sq_nonneg (t - h / 2)]
    refine ⟨hle, ?_⟩
    have hs : (Real.sqrt (h^2 - a * c))^2 = h^2 - a * c := Real.sq_sqrt (by linarith)
    rw [quad_factor a c h t _ hs] at ht
    rcases mul_eq_zero.mp ht with h1 | h2
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  · rintro ⟨hle, htr | htr⟩ <;>
    · have hs : (Real.sqrt (h^2 - a * c))^2 = h^2 - a * c := Real.sq_sqrt (by linarith)
      rw [quad_factor a c h t _ hs, htr]
      ring

/-- The midpoint of AB is the origin. -/
theorem midpoint_AB (a : ℝ) : midpoint ℝ (A a) (B a) = !₂[0, 0] := by
  rw [midpoint_eq_smul_add]
  apply Pt.ext
  · simp [A, B]
    ring
  · simp [A, B]

/-- The midpoint of CD lies on the axis of symmetry at height `h`. -/
theorem midpoint_CD (c h : ℝ) : midpoint ℝ (C c h) (D c h) = !₂[0, h] := by
  rw [midpoint_eq_smul_add]
  apply Pt.ext
  · simp [C, D]
    ring
  · simp [C, D]
    ring

/-- The distance from X to the midpoint of AB (the foot of the perpendicular
from X to the line AB). -/
theorem dist_X_origin (t : ℝ) : dist (X t) (!₂[0, 0] : Pt) = |t| := by
  rw [dist_eq_norm, EuclideanSpace.norm_eq]
  simp [X, Fin.sum_univ_two, Real.sqrt_sq_eq_abs]

/-- The distance from X to the midpoint of CD (the foot of the perpendicular
from X to the line CD). -/
theorem dist_X_axis_h (t h : ℝ) : dist (X t) (!₂[0, h] : Pt) = |t - h| := by
  rw [dist_eq_norm, EuclideanSpace.norm_eq]
  simp [X, Fin.sum_univ_two, Real.sqrt_sq_eq_abs]

/-- The square root in the answer is at most `h`. -/
theorem sqrt_le (a c h : ℝ) (ha : 0 < a) (hc : 0 < c) (hh : 0 < h) :
    Real.sqrt (h^2 - a * c) ≤ h := by
  have h1 : Real.sqrt (h^2 - a * c) ≤ Real.sqrt (h^2) :=
    Real.sqrt_le_sqrt (by nlinarith [mul_pos ha hc])
  rw [Real.sqrt_sq (le_of_lt hh)] at h1
  exact h1

snip end

/-- The construction: X is the intersection of the axis of symmetry with the
circle of diameter BC (equivalently AD); its distance from AB is one of
`(h ± √(h² - ac))/2`, and such a point exists iff `ac ≤ h²`. -/
problem imo1960_p7 (a c h t : ℝ) (_ha : 0 < a) (_hc : 0 < c) (_hh : 0 < h) :
    (∠ (B a) (X t) (C c h) = Real.pi / 2 ∧ ∠ (A a) (X t) (D c h) = Real.pi / 2) ↔
    (a * c ≤ h^2 ∧ t ∈ SolutionDistances a c h) := by
  rw [angle_BXC_iff, angle_AXD_iff, and_self]
  exact quad_eq_iff a c h t

/-- The condition for such points to exist: `ac ≤ h²`. -/
problem imo1960_p7_existence (a c h : ℝ) (ha : 0 < a) (hc : 0 < c) (hh : 0 < h) :
    (∃ t : ℝ, ∠ (B a) (X t) (C c h) = Real.pi / 2 ∧
      ∠ (A a) (X t) (D c h) = Real.pi / 2) ↔ a * c ≤ h^2 := by
  constructor
  · rintro ⟨t, ht⟩
    exact ((imo1960_p7 a c h t ha hc hh).mp ht).1
  · intro hle
    refine ⟨(h + Real.sqrt (h^2 - a * c)) / 2, ?_⟩
    rw [imo1960_p7 a c h _ ha hc hh]
    exact ⟨hle, Or.inl rfl⟩

/-- The distance of each solution point X from AB is `t` and its distance
from CD is `h - t`. -/
problem imo1960_p7_distances (a c h t : ℝ) (ha : 0 < a) (hc : 0 < c) (hh : 0 < h)
    (hX : ∠ (B a) (X t) (C c h) = Real.pi / 2 ∧
      ∠ (A a) (X t) (D c h) = Real.pi / 2) :
    dist (X t) (midpoint ℝ (A a) (B a)) = t ∧
    dist (X t) (midpoint ℝ (C c h) (D c h)) = h - t := by
  obtain ⟨hle, htr⟩ := (imo1960_p7 a c h t ha hc hh).mp hX
  have hs := sqrt_le a c h ha hc hh
  have hs0 : 0 ≤ Real.sqrt (h^2 - a * c) := Real.sqrt_nonneg _
  have ht0 : 0 ≤ t := by rcases htr with h1 | h1 <;> linarith
  have hth : t ≤ h := by rcases htr with h1 | h1 <;> linarith
  rw [midpoint_AB, midpoint_CD, dist_X_origin, dist_X_axis_h,
    abs_of_nonneg ht0, abs_of_nonpos (show t - h ≤ 0 by linarith)]
  exact ⟨rfl, by ring⟩

end Imo1960P7
