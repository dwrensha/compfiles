/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import Mathlib.Analysis.Complex.Basic
public import ProblemExtraction

@[expose] public section

problem_file {
  tags := [.Geometry]
}

/-!
# International Mathematical Olympiad 1979, Problem 3

Two circles in a plane intersect. A is one of the points of intersection.
Starting simultaneously from A two points move with constant speed, each
travelling along its own circle in the same sense. The two points return to
A simultaneously after one revolution. Prove that there is a fixed point P
in the plane such that the two points are always equidistant from P.
-/

namespace Imo1979P3

open scoped ComplexConjugate

snip begin

/-- The candidate fixed point: the reflection of `A` across the perpendicular
bisector of the segment `OO'`, expressed using complex conjugation. -/
noncomputable def fixedPoint (O O' A : ℂ) : ℂ :=
  (O + O') / 2 - (O' - O) / (conj O' - conj O) * conj (A - (O + O') / 2)

/-- Key algebraic identity: writing `P = fixedPoint O O' A` for the candidate
fixed point, the difference of the squared distances from `P` to the two
moving points is a multiple of `t * conj t - 1`, and hence vanishes whenever
the rotation factor `t` lies on the unit circle. -/
lemma sq_dist_sub_sq_dist (O O' A t : ℂ) (hO : O ≠ O') :
    (fixedPoint O O' A - (O + t * (A - O))) *
        conj (fixedPoint O O' A - (O + t * (A - O))) -
      (fixedPoint O O' A - (O' + t * (A - O'))) *
        conj (fixedPoint O O' A - (O' + t * (A - O'))) =
    (t * conj t - 1) *
      ((conj (O' - O) * (2 * A - (O + O')) +
        (O' - O) * conj (2 * A - (O + O'))) / 2) := by
  have hd : O' - O ≠ 0 := sub_ne_zero.mpr hO.symm
  have hcd : conj O' - conj O ≠ 0 := by
    intro h
    have h2 := congrArg conj h
    simp only [map_sub, map_zero, Complex.conj_conj] at h2
    exact hO (sub_eq_zero.mp h2).symm
  simp only [fixedPoint, map_sub, map_add, map_mul, map_div₀, map_ofNat,
    Complex.conj_conj]
  field_simp [hd, hcd]
  ring

snip end

problem imo1979_p3
    (O O' A : ℂ) (hO : O ≠ O') (X X' : ℂ → ℂ)
    (hX : ∀ t : ℂ, X t = O + t * (A - O))
    (hX' : ∀ t : ℂ, X' t = O' + t * (A - O')) :
    ∃ P : ℂ, ∀ t : ℂ, ‖t‖ = 1 → dist (X t) P = dist (X' t) P := by
  -- We follow the solution from
  -- https://prase.cz/kalva/imo/isoln/isoln793.html :
  -- take `P` to be the reflection of `A` across the perpendicular bisector
  -- of `OO'`; then the triangles `POX` and `X'O'P` are congruent,
  -- hence `PX = PX'`.
  use fixedPoint O O' A
  intro t ht
  have ht1 : t * conj t = 1 := by
    rw [Complex.mul_conj, ← Complex.sq_norm, ht]
    norm_num
  have key := sq_dist_sub_sq_dist O O' A t hO
  rw [ht1] at key
  simp only [sub_self, zero_mul] at key
  have h3 : (fixedPoint O O' A - X t) * conj (fixedPoint O O' A - X t) =
      (fixedPoint O O' A - X' t) * conj (fixedPoint O O' A - X' t) := by
    rw [hX t, hX' t]
    exact sub_eq_zero.mp key
  rw [Complex.mul_conj, Complex.mul_conj] at h3
  have h2 : Complex.normSq (fixedPoint O O' A - X t) =
      Complex.normSq (fixedPoint O O' A - X' t) := Complex.ofReal_inj.mp h3
  rw [Complex.dist_eq, Complex.dist_eq, norm_sub_rev (X t) (fixedPoint O O' A),
    norm_sub_rev (X' t) (fixedPoint O O' A), Complex.norm_def, Complex.norm_def, h2]

end Imo1979P3
