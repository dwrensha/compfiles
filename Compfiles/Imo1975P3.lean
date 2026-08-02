/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 1975, Problem 3

Given any triangle ABC, construct external triangles ABR, BCP, CAQ on the
sides, so that ∠PBC = 45°, ∠PCB = 30°, ∠QAC = 45°, ∠QCA = 30°,
∠RAB = 15°, ∠RBA = 15°. Prove that ∠QRP = 90° and QR = RP.

# Formalization

We work in the Euclidean plane `Pt := EuclideanSpace ℝ (Fin 2)`. The
constructed points are given explicitly: for a directed segment from `U` to
`V`, the apex `X` of the triangle erected on the right-hand side of `U → V`
with base angles `β` (at `U`) and `γ` (at `V`) is

`X = U + (cot β / (cot β + cot γ)) • (V - U) - (1 / (cot β + cot γ)) • rot90 (V - U)`,

because the foot of the altitude from `X` divides `UV` in the ratio
`cot β : cot γ` and the altitude has length `|V - U| / (cot β + cot γ)`.
With `cot 45° = 1`, `cot 30° = √3` and `cot 15° = 2 + √3` this yields the
hypotheses `hP`, `hQ`, `hR` below; the minus sign erects the triangles
externally when `ABC` is oriented counterclockwise (the clockwise case is
symmetric). The conclusion `∠QRP = 90°` is expressed as
`⟪Q - R, P - R⟫ = 0` and `QR = RP` as `dist Q R = dist P R`.

(Problem and solution source: https://prase.cz/kalva/imo/isoln/isoln753.html)
-/

namespace Imo1975P3

open scoped RealInnerProductSpace

/-- The Euclidean plane. -/
abbrev Pt := EuclideanSpace ℝ (Fin 2)

/-- Rotation by 90 degrees (counterclockwise). -/
def rot90 (v : Pt) : Pt := !₂[-(v 1), v 0]

snip begin

theorem Pt.ext {x y : Pt} (h0 : x 0 = y 0) (h1 : x 1 = y 1) : x = y := by
  apply WithLp.ofLp_injective (p := 2)
  funext i
  fin_cases i <;> assumption

@[simp] theorem rot90_apply0 (v : Pt) : rot90 v 0 = -(v 1) := rfl

@[simp] theorem rot90_apply1 (v : Pt) : rot90 v 1 = v 0 := rfl

theorem inner_pt (n x : Pt) : ⟪n, x⟫ = n 0 * x 0 + n 1 * x 1 := by
  rw [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, RCLike.inner_apply]
  simp only [conj_trivial]
  ring

theorem inner_self_rot90 (v : Pt) : ⟪v, rot90 v⟫ = 0 := by
  rw [inner_pt, rot90_apply0, rot90_apply1]
  ring

theorem inner_rot90_rot90 (v : Pt) : ⟪rot90 v, rot90 v⟫ = ⟪v, v⟫ := by
  rw [inner_pt, inner_pt, rot90_apply0, rot90_apply1]
  ring

theorem norm_rot90 (v : Pt) : ‖rot90 v‖ = ‖v‖ := by
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner, inner_rot90_rot90]

/-- The key identity: `RP` is obtained from `RQ` by a quarter turn. -/
theorem sub_eq_neg_rot90_sub (A B C P Q R : Pt)
    (hR : R = (1 / 2 : ℝ) • (A + B) - ((2 - Real.sqrt 3) / 2) • rot90 (B - A))
    (hP : P = B + ((Real.sqrt 3 - 1) / 2) • (C - B) -
      ((Real.sqrt 3 - 1) / 2) • rot90 (C - B))
    (hQ : Q = C + ((3 - Real.sqrt 3) / 2) • (A - C) -
      ((Real.sqrt 3 - 1) / 2) • rot90 (A - C)) :
    P - R = -rot90 (Q - R) := by
  apply Pt.ext <;>
    simp only [hP, hQ, hR, rot90_apply0, rot90_apply1, PiLp.add_apply,
      PiLp.sub_apply, PiLp.neg_apply, PiLp.smul_apply, smul_eq_mul] <;>
    ring

snip end

problem imo1975_p3 (A B C P Q R : Pt)
    (hR : R = (1 / 2 : ℝ) • (A + B) - ((2 - Real.sqrt 3) / 2) • rot90 (B - A))
    (hP : P = B + ((Real.sqrt 3 - 1) / 2) • (C - B) -
      ((Real.sqrt 3 - 1) / 2) • rot90 (C - B))
    (hQ : Q = C + ((3 - Real.sqrt 3) / 2) • (A - C) -
      ((Real.sqrt 3 - 1) / 2) • rot90 (A - C)) :
    ⟪Q - R, P - R⟫ = 0 ∧ dist Q R = dist P R := by
  have key := sub_eq_neg_rot90_sub A B C P Q R hR hP hQ
  constructor
  · rw [key, inner_neg_right, neg_eq_zero]
    exact inner_self_rot90 (Q - R)
  · rw [dist_eq_norm, dist_eq_norm, key, norm_neg, norm_rot90]

end Imo1975P3
