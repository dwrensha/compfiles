/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.InnerProductSpace.Basic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 1963, Problem 2

Point $A$ and segment $BC$ are given. Determine the locus of points in
space which are vertices of right angles with one side passing through
$A$ and the other side intersecting segment $BC$.
-/

namespace Imo1963P2

open scoped Convex InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

snip begin

/-- Key one-dimensional fact: `0` is a convex combination of two real numbers
`u` and `v` if and only if their product is nonpositive. -/
lemma exists_convex_comb_eq_zero_iff_mul_nonpos {u v : ℝ} :
    (∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ a + b = 1 ∧ a * u + b * v = 0) ↔ u * v ≤ 0 := by
  constructor
  · rintro ⟨a, b, ha, hb, hab, h⟩
    have e1 : b * (u * v) = -a * u ^ 2 := by linear_combination u * h
    have e2 : a * (u * v) = -b * v ^ 2 := by linear_combination v * h
    have h1 : b * (u * v) ≤ 0 := by
      rw [e1, neg_mul]; exact neg_nonpos.mpr (mul_nonneg ha (sq_nonneg u))
    have h2 : a * (u * v) ≤ 0 := by
      rw [e2, neg_mul]; exact neg_nonpos.mpr (mul_nonneg hb (sq_nonneg v))
    have e3 : u * v = a * (u * v) + b * (u * v) := by
      rw [← add_mul, hab, one_mul]
    linarith
  · intro huv
    rcases mul_nonpos_iff.mp huv with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · by_cases h0 : u - v = 0
      · have hu0 : u = 0 := by linarith
        exact ⟨1, 0, zero_le_one, le_refl (0 : ℝ), by norm_num, by rw [hu0]; norm_num⟩
      · have hpos : 0 < u - v := lt_of_le_of_ne' (by linarith) h0
        refine ⟨-v / (u - v), u / (u - v), div_nonneg (neg_nonneg.mpr hv) hpos.le,
          div_nonneg hu hpos.le, ?_, ?_⟩
        · rw [← add_div, show -v + u = u - v by ring, div_self hpos.ne']
        · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div,
            show -v * u + u * v = 0 by ring, zero_div]
    · by_cases h0 : v - u = 0
      · have hu0 : u = 0 := by linarith
        exact ⟨1, 0, zero_le_one, le_refl (0 : ℝ), by norm_num, by rw [hu0]; norm_num⟩
      · have hpos : 0 < v - u := lt_of_le_of_ne' (by linarith) h0
        refine ⟨v / (v - u), -u / (v - u), div_nonneg hv hpos.le,
          div_nonneg (neg_nonneg.mpr hu) hpos.le, ?_, ?_⟩
        · rw [← add_div, show v + -u = v - u by ring, div_self hpos.ne']
        · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div,
            show v * u + -u * v = 0 by ring, zero_div]

/-- The inner product `⟪A - P, X - P⟫_ℝ` is affine in `X`: at the convex
combination `X = a • B + b • C` with `a + b = 1` it equals the corresponding
convex combination of its values at `B` and at `C`. -/
lemma inner_sub_smul_add_smul {A B C P : V} {a b : ℝ} (hab : a + b = 1) :
    ⟪A - P, a • B + b • C - P⟫_ℝ =
      a * ⟪A - P, B - P⟫_ℝ + b * ⟪A - P, C - P⟫_ℝ := by
  have hX : a • B + b • C - P = a • (B - P) + b • (C - P) := by
    have hP : P = (a + b) • P := by rw [hab, one_smul]
    nth_rewrite 1 [hP]
    rw [add_smul, smul_sub, smul_sub]
    abel
  rw [hX, inner_add_right, real_inner_smul_right, real_inner_smul_right]

snip end

/-- The answer: the locus is the set of points `P` such that the two inner
products `⟪A - P, B - P⟫_ℝ` and `⟪A - P, C - P⟫_ℝ` have opposite signs (or one
of them vanishes).

Since `⟪A - P, X - P⟫_ℝ ≤ 0` means that the angle `∠APX` is right or obtuse,
i.e. that `P` belongs to the closed ball with diameter `AX` (with equality on
its boundary sphere), the locus consists of the points lying in exactly one of
the closed balls with diameters `AB` and `AC`, or on the surface of either
ball. -/
determine locus (A B C : V) : Set V :=
  {P | ⟪A - P, B - P⟫_ℝ * ⟪A - P, C - P⟫_ℝ ≤ 0}

problem imo1963_p2 (A B C P : V) :
    P ∈ locus A B C ↔ ∃ X ∈ [B -[ℝ] C], ⟪A - P, X - P⟫_ℝ = 0 := by
  show ⟪A - P, B - P⟫_ℝ * ⟪A - P, C - P⟫_ℝ ≤ 0 ↔
    ∃ X ∈ [B -[ℝ] C], ⟪A - P, X - P⟫_ℝ = 0
  constructor
  · intro h
    obtain ⟨a, b, ha, hb, hab, h0⟩ := exists_convex_comb_eq_zero_iff_mul_nonpos.mpr h
    exact ⟨a • B + b • C, ⟨a, b, ha, hb, hab, rfl⟩,
      by rw [inner_sub_smul_add_smul hab]; exact h0⟩
  · rintro ⟨X, ⟨a, b, ha, hb, hab, hX⟩, hP⟩
    rw [← hX, inner_sub_smul_add_smul hab] at hP
    exact exists_convex_comb_eq_zero_iff_mul_nonpos.mp ⟨a, b, ha, hb, hab, hP⟩

end Imo1963P2
