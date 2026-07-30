/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Real.Sqrt
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 1960, Problem 3

In a given right triangle ABC, the hypotenuse BC, of length a, is divided
into n equal parts, with n an odd integer. The central part subtends an
angle α at A. If h is the perpendicular distance from A to BC, prove that

  tan α = 4nh / (an² − a).
-/

namespace Imo1960P3

open scoped EuclideanGeometry RealInnerProductSpace

/-- The Euclidean plane, in which the triangle lives. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

snip begin

/-!
We place the triangle in coordinates: without loss of generality the
hypotenuse lies on the x-axis with `B = (0, 0)` and `C = (a, 0)`, and we
write `A = (x, h)` with `h > 0`, so that `h` is indeed the perpendicular
distance from `A` to `BC`. The right angle at `A` is then equivalent to
`x ^ 2 - a * x + h ^ 2 = 0` (the equation `⟪B - A, C - A⟫ = 0`).
Since `n` is odd, the central one of the `n` equal parts is centered at the
midpoint of `BC`, so its endpoints are
`P = (a / 2 - a / (2n), 0)` and `Q = (a / 2 + a / (2n), 0)`, and the angle
subtended at `A` is `α = ∠PAQ`.

The classical solution computes `tan α` from the dot product of the two
legs: with `u = P - A` and `v = Q - A` we have
`tan α = √(⟪u, u⟫ * ⟪v, v⟫ - ⟪u, v⟫ ^ 2) / ⟪u, v⟫`, the numerator being
`h * (a / n)` and the denominator `a ^ 2 / 4 - (a / (2n)) ^ 2`, where the
last step uses the right-angle condition.
-/

/-- Inner product of plane vectors in coordinates. -/
lemma inner_eq (u v : Plane) : ⟪u, v⟫ = u 0 * v 0 + u 1 * v 1 := by
  simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, RCLike.conj_to_real]
  ring

/-- `vsub` on the plane, evaluated at a coordinate. -/
lemma vsub_apply (u v : Plane) (i : Fin 2) : (u -ᵥ v) i = u i - v i := rfl

/-- Auxiliary division simplification. -/
lemma div_div_div {r s t : ℝ} (ht : t ≠ 0) : r / t / (s / t) = r / s := by
  field_simp

/-- The tangent of the angle between two nonzero vectors, in terms of
their inner products. -/
lemma tan_angle_eq {u v : Plane} (hu : u ≠ 0) (hv : v ≠ 0) :
    Real.tan (InnerProductGeometry.angle u v) =
      √(⟪u, u⟫ * ⟪v, v⟫ - ⟪u, v⟫ * ⟪u, v⟫) / ⟪u, v⟫ := by
  have hn0 : ‖u‖ * ‖v‖ ≠ 0 := by positivity
  rw [Real.tan_eq_sin_div_cos, InnerProductGeometry.sin_angle hu hv,
    InnerProductGeometry.cos_angle, div_div_div hn0]

/-- The final algebraic identity: with the computed numerator and
denominator, `tan α` takes the required form. Note that for `n = 1` both
sides of the identity are `0` (the angle is `π / 2`, and in Lean
`Real.tan (π / 2) = 0` while the right-hand side has denominator `0`). -/
lemma final_div {n : ℕ} (hn : 0 < n) {a h : ℝ} (ha : 0 < a) :
    h * (a / (n : ℝ)) / (a ^ 2 / 4 - (a / (2 * (n : ℝ))) ^ 2) =
      4 * (n : ℝ) * h / (a * (n : ℝ) ^ 2 - a) := by
  have hnr : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnr' : (n : ℝ) ≠ 0 := ne_of_gt hnr
  rcases eq_or_ne n 1 with rfl | hn1
  · simp only [Nat.cast_one]
    have e1 : a ^ 2 / 4 - (a / (2 * (1 : ℝ))) ^ 2 = 0 := by ring
    have e2 : a * (1 : ℝ) ^ 2 - a = 0 := by ring
    rw [e1, e2, div_zero, div_zero]
  · have hn2 : 2 ≤ n := by omega
    have hn2r : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    have h4 : (4 : ℝ) ≤ (n : ℝ) ^ 2 := by
      have hmul := mul_le_mul hn2r hn2r (by norm_num) (by linarith)
      nlinarith
    have h1 : (0 : ℝ) < (n : ℝ) ^ 2 - 1 := by linarith
    have hD1 : a ^ 2 / 4 - (a / (2 * (n : ℝ))) ^ 2 =
        a ^ 2 * ((n : ℝ) ^ 2 - 1) / (4 * (n : ℝ) ^ 2) := by
      field_simp
      ring
    have hD2 : a * (n : ℝ) ^ 2 - a = a * ((n : ℝ) ^ 2 - 1) := by ring
    have hd1 : a ^ 2 * ((n : ℝ) ^ 2 - 1) / (4 * (n : ℝ) ^ 2) ≠ 0 :=
      ne_of_gt (by positivity)
    have hd2 : a * ((n : ℝ) ^ 2 - 1) ≠ 0 := ne_of_gt (by positivity)
    have hn42 : (4 : ℝ) * (n : ℝ) ^ 2 ≠ 0 := by positivity
    rw [hD1, hD2, div_eq_div_iff hd1 hd2]
    field_simp [hnr', hn42]

snip end

problem imo1960_p3
    (n : ℕ) (hn : Odd n)
    (a h x : ℝ) (ha : 0 < a) (hh : 0 < h)
    (hr : x ^ 2 - a * x + h ^ 2 = 0) :
    Real.tan (∠ (!₂[a / 2 - a / (2 * (n : ℝ)), 0] : Plane)
                (!₂[x, h] : Plane)
                (!₂[a / 2 + a / (2 * (n : ℝ)), 0] : Plane)) =
      4 * (n : ℝ) * h / (a * (n : ℝ) ^ 2 - a) := by
  have hnpos : 0 < n := hn.pos
  have hnr : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  -- The two legs `P -ᵥ A` and `Q -ᵥ A` are nonzero, since their second
  -- coordinate is `-h ≠ 0`.
  have hP : (!₂[a / 2 - a / (2 * (n : ℝ)), 0] : Plane) -ᵥ !₂[x, h] ≠ 0 := by
    intro hcon
    have h1 : ((!₂[a / 2 - a / (2 * (n : ℝ)), 0] : Plane) -ᵥ !₂[x, h]) 1 = (0 : Plane) 1 := by
      rw [hcon]
    change (0 : ℝ) - h = (0 : ℝ) at h1
    linarith
  have hQ : (!₂[a / 2 + a / (2 * (n : ℝ)), 0] : Plane) -ᵥ !₂[x, h] ≠ 0 := by
    intro hcon
    have h1 : ((!₂[a / 2 + a / (2 * (n : ℝ)), 0] : Plane) -ᵥ !₂[x, h]) 1 = (0 : Plane) 1 := by
      rw [hcon]
    change (0 : ℝ) - h = (0 : ℝ) at h1
    linarith
  -- The inner product of the two legs, using the right-angle condition `hr`.
  have hinner : ⟪(!₂[a / 2 - a / (2 * (n : ℝ)), 0] : Plane) -ᵥ !₂[x, h],
                  (!₂[a / 2 + a / (2 * (n : ℝ)), 0] : Plane) -ᵥ !₂[x, h]⟫ =
      a ^ 2 / 4 - (a / (2 * (n : ℝ))) ^ 2 := by
    simp only [inner_eq, vsub_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination hr
  -- The numerator `√(⟪u, u⟫ * ⟪v, v⟫ - ⟪u, v⟫ ^ 2) = h * (a / n)`.
  have hdisc : √(⟪(!₂[a / 2 - a / (2 * (n : ℝ)), 0] : Plane) -ᵥ !₂[x, h],
                    (!₂[a / 2 - a / (2 * (n : ℝ)), 0] : Plane) -ᵥ !₂[x, h]⟫ *
                  ⟪(!₂[a / 2 + a / (2 * (n : ℝ)), 0] : Plane) -ᵥ !₂[x, h],
                    (!₂[a / 2 + a / (2 * (n : ℝ)), 0] : Plane) -ᵥ !₂[x, h]⟫ -
                ⟪(!₂[a / 2 - a / (2 * (n : ℝ)), 0] : Plane) -ᵥ !₂[x, h],
                    (!₂[a / 2 + a / (2 * (n : ℝ)), 0] : Plane) -ᵥ !₂[x, h]⟫ *
                  ⟪(!₂[a / 2 - a / (2 * (n : ℝ)), 0] : Plane) -ᵥ !₂[x, h],
                    (!₂[a / 2 + a / (2 * (n : ℝ)), 0] : Plane) -ᵥ !₂[x, h]⟫) =
      h * (a / (n : ℝ)) := by
    have e : ⟪(!₂[a / 2 - a / (2 * (n : ℝ)), 0] : Plane) -ᵥ !₂[x, h],
                (!₂[a / 2 - a / (2 * (n : ℝ)), 0] : Plane) -ᵥ !₂[x, h]⟫ *
              ⟪(!₂[a / 2 + a / (2 * (n : ℝ)), 0] : Plane) -ᵥ !₂[x, h],
                (!₂[a / 2 + a / (2 * (n : ℝ)), 0] : Plane) -ᵥ !₂[x, h]⟫ -
            ⟪(!₂[a / 2 - a / (2 * (n : ℝ)), 0] : Plane) -ᵥ !₂[x, h],
                (!₂[a / 2 + a / (2 * (n : ℝ)), 0] : Plane) -ᵥ !₂[x, h]⟫ *
              ⟪(!₂[a / 2 - a / (2 * (n : ℝ)), 0] : Plane) -ᵥ !₂[x, h],
                (!₂[a / 2 + a / (2 * (n : ℝ)), 0] : Plane) -ᵥ !₂[x, h]⟫ =
        (h * (a / (n : ℝ))) ^ 2 := by
      simp only [inner_eq, vsub_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
      ring
    rw [e, Real.sqrt_sq (by positivity)]
  -- Assemble the computation of `tan α`.
  unfold EuclideanGeometry.angle
  rw [tan_angle_eq hP hQ, hdisc, hinner]
  exact final_div hnpos ha

end Imo1960P3
