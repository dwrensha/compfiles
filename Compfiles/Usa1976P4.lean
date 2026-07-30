/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Ring
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry, .Inequality] }

/-!
# USA Mathematical Olympiad 1976, Problem 4

A tetrahedron ABCD has edges of total length 1. The angles at A (∠BAC etc)
are all 90°. Find the maximum volume of the tetrahedron.
-/

namespace Usa1976P4

/-!
Since the three face angles at `A` are all right angles, the three edges
`AB`, `AC`, `AD` are pairwise perpendicular. Writing `x`, `y`, `z` for their
lengths, the remaining three edges are `√(x² + y²)`, `√(y² + z²)` and
`√(z² + x²)` by the Pythagorean theorem, and the volume of the tetrahedron is
`x * y * z / 6` (base area `x * y / 2` times height `z`). The problem therefore
becomes: maximize `x * y * z / 6` over positive reals `x`, `y`, `z` with

  `x + y + z + √(x² + y²) + √(y² + z²) + √(z² + x²) = 1`.
-/

noncomputable determine max_volume : ℝ := (5 * Real.sqrt 2 - 7) / 162

/-- The set of possible volumes, parametrized by the lengths `x`, `y`, `z`
of the three edges of the tetrahedron that meet at the vertex `A`. -/
def VolumeSet : Set ℝ :=
  {v | ∃ x y z : ℝ, 0 < x ∧ 0 < y ∧ 0 < z ∧
    x + y + z + Real.sqrt (x^2 + y^2) + Real.sqrt (y^2 + z^2) + Real.sqrt (z^2 + x^2) = 1 ∧
    v = x * y * z / 6}

snip begin

/-- AM-GM for three nonnegative numbers, in cubed form, proved by an explicit
sum-of-squares identity. -/
lemma cube_sum_ge (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    27 * (a * b * c) ≤ (a + b + c)^3 := by
  have key : (a + b + c)^3 - 27 * a * b * c =
      (a + b + c) * ((a - b)^2 + (b - c)^2 + (c - a)^2) / 2 +
      3 * (a * (b - c)^2 + b * (c - a)^2 + c * (a - b)^2) := by ring
  have h1 : 0 ≤ (a + b + c) * ((a - b)^2 + (b - c)^2 + (c - a)^2) / 2 := by positivity
  have h2 : 0 ≤ 3 * (a * (b - c)^2 + b * (c - a)^2 + c * (a - b)^2) := by positivity
  linarith

lemma sqrt_prod (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    Real.sqrt (x * y) * Real.sqrt (y * z) * Real.sqrt (z * x) = x * y * z := by
  rw [← Real.sqrt_mul (mul_nonneg hx hy) (y * z),
    ← Real.sqrt_mul (mul_nonneg (mul_nonneg hx hy) (mul_nonneg hy hz)) (z * x),
    show x * y * (y * z) * (z * x) = (x * y * z)^2 by ring,
    Real.sqrt_sq (mul_nonneg (mul_nonneg hx hy) hz)]

lemma sqrt_pair_ge (x y : ℝ) :
    Real.sqrt 2 * Real.sqrt (x * y) ≤ Real.sqrt (x^2 + y^2) := by
  have h : 2 * (x * y) ≤ x^2 + y^2 := by linarith [sq_nonneg (x - y)]
  have h2 := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_mul (show (0 : ℝ) ≤ 2 by norm_num) (x * y)] at h2

/-- The common value of `x = y = z` at the maximum. -/
lemma t_pos : 0 < (Real.sqrt 2 - 1) / 3 := by
  have h : (1 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)]; norm_num
  linarith

lemma t_cubed : ((Real.sqrt 2 - 1) / 3)^3 = (5 * Real.sqrt 2 - 7) / 27 := by
  have h2 : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : (Real.sqrt 2)^3 = 2 * Real.sqrt 2 := by
    calc (Real.sqrt 2)^3 = (Real.sqrt 2)^2 * Real.sqrt 2 := by ring
    _ = 2 * Real.sqrt 2 := by rw [h2]
  have h4 : (Real.sqrt 2 - 1)^3 = 5 * Real.sqrt 2 - 7 := by
    linear_combination h3 - 3 * h2
  rw [div_pow, h4]
  norm_num

/-- `t = (√2 - 1)/3` satisfies `3 * t * (1 + √2) = 1`: the total edge length
of the extremal tetrahedron is `1`. -/
lemma t_key : 3 * ((Real.sqrt 2 - 1) / 3) * (1 + Real.sqrt 2) = 1 := by
  have h2 : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  linear_combination h2

lemma t_diag : Real.sqrt (((Real.sqrt 2 - 1) / 3)^2 + ((Real.sqrt 2 - 1) / 3)^2) =
    Real.sqrt 2 * ((Real.sqrt 2 - 1) / 3) := by
  rw [show ((Real.sqrt 2 - 1) / 3)^2 + ((Real.sqrt 2 - 1) / 3)^2 =
      2 * (((Real.sqrt 2 - 1) / 3)^2) by ring,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_sq t_pos.le]

/-- The heart of the estimate: if `27 * p ≤ s³`, `27 * p ≤ q³` and
`s + √2 * q ≤ 1`, then `p ≤ t³` for `t` the positive number with
`3 * t * (1 + √2) = 1`. -/
lemma abstract_bound (s q p t : ℝ) (hs : 0 ≤ s) (hq : 0 ≤ q)
    (hps : 27 * p ≤ s^3) (hpq : 27 * p ≤ q^3) (hsum : s + Real.sqrt 2 * q ≤ 1)
    (htk : 3 * t * (1 + Real.sqrt 2) = 1) : p ≤ t^3 := by
  by_contra hpc
  push Not at hpc
  have h27 : (3 * t)^3 = 27 * t^3 := by ring
  have hsgt : 3 * t < s := by
    by_contra hle
    push Not at hle
    have hc := pow_le_pow_left₀ hs hle 3
    rw [h27] at hc
    linarith
  have hqgt : 3 * t < q := by
    by_contra hle
    push Not at hle
    have hc := pow_le_pow_left₀ hq hle 3
    rw [h27] at hc
    linarith
  have h4 : Real.sqrt 2 * (3 * t) < Real.sqrt 2 * q :=
    mul_lt_mul_of_pos_left hqgt (Real.sqrt_pos.mpr (by norm_num))
  have h6 : 3 * t + Real.sqrt 2 * (3 * t) = 1 := by linear_combination htk
  linarith

lemma volume_le (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x + y + z + Real.sqrt (x^2 + y^2) + Real.sqrt (y^2 + z^2) +
      Real.sqrt (z^2 + x^2) = 1) :
    x * y * z / 6 ≤ max_volume := by
  have hps : 27 * (x * y * z) ≤ (x + y + z)^3 := cube_sum_ge _ _ _ hx.le hy.le hz.le
  have hsp : Real.sqrt (x * y) * Real.sqrt (y * z) * Real.sqrt (z * x) = x * y * z :=
    sqrt_prod _ _ _ hx.le hy.le hz.le
  have hpq : 27 * (x * y * z) ≤
      (Real.sqrt (x * y) + Real.sqrt (y * z) + Real.sqrt (z * x))^3 := by
    have h' := cube_sum_ge (Real.sqrt (x * y)) (Real.sqrt (y * z)) (Real.sqrt (z * x))
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have heq : (27 : ℝ) * (Real.sqrt (x * y) * Real.sqrt (y * z) * Real.sqrt (z * x)) =
        27 * (x * y * z) := by
      rw [hsp]
    rwa [heq] at h'
  have hsqrt : Real.sqrt 2 * (Real.sqrt (x * y) + Real.sqrt (y * z) + Real.sqrt (z * x)) ≤
      Real.sqrt (x^2 + y^2) + Real.sqrt (y^2 + z^2) + Real.sqrt (z^2 + x^2) := by
    have e1 := sqrt_pair_ge x y
    have e2 := sqrt_pair_ge y z
    have e3 := sqrt_pair_ge z x
    linarith
  have hsum : (x + y + z) +
      Real.sqrt 2 * (Real.sqrt (x * y) + Real.sqrt (y * z) + Real.sqrt (z * x)) ≤ 1 := by
    linarith [h, hsqrt]
  have hq_pos : 0 < Real.sqrt (x * y) + Real.sqrt (y * z) + Real.sqrt (z * x) :=
    add_pos (add_pos (Real.sqrt_pos.mpr (mul_pos hx hy))
      (Real.sqrt_pos.mpr (mul_pos hy hz))) (Real.sqrt_pos.mpr (mul_pos hz hx))
  have hbound : x * y * z ≤ ((Real.sqrt 2 - 1) / 3)^3 :=
    abstract_bound _ _ _ _ (add_pos (add_pos hx hy) hz).le hq_pos.le hps hpq hsum t_key
  rw [t_cubed] at hbound
  have hgoal : x * y * z / 6 ≤ (5 * Real.sqrt 2 - 7) / 162 := by linarith
  exact hgoal

snip end

problem usa1976_p4 : IsGreatest VolumeSet max_volume := by
  unfold IsGreatest upperBounds
  constructor
  · -- the bound is attained at x = y = z = (√2 - 1)/3
    refine ⟨(Real.sqrt 2 - 1) / 3, (Real.sqrt 2 - 1) / 3, (Real.sqrt 2 - 1) / 3,
      t_pos, t_pos, t_pos, ?_, ?_⟩
    · simp only [t_diag]
      linear_combination t_key
    · have hvol : (Real.sqrt 2 - 1) / 3 * ((Real.sqrt 2 - 1) / 3) * ((Real.sqrt 2 - 1) / 3) / 6 =
          (5 * Real.sqrt 2 - 7) / 162 := by
        rw [show (Real.sqrt 2 - 1) / 3 * ((Real.sqrt 2 - 1) / 3) * ((Real.sqrt 2 - 1) / 3) =
            ((Real.sqrt 2 - 1) / 3)^3 by ring, t_cubed]
        ring
      exact hvol.symm
  · rintro v ⟨x, y, z, hx, hy, hz, hsum, rfl⟩
    exact volume_le x y z hx hy hz hsum

end Usa1976P4
