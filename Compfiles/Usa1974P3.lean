/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# USA Mathematical Olympiad 1974, Problem 3

Two points in a thin spherical shell are joined by a curve shorter than
the diameter of the shell. Show that the curve lies entirely in one
hemisphere.

## Formalization remarks

We model the shell as a sphere of radius `R` (hence diameter `2 * R`)
centered at the origin of `EuclideanSpace ℝ (Fin 3)`, and a hemisphere
centered at a point `u` of the sphere as the set `{x | 0 ≤ ⟪u, x⟫_ℝ}`.

A curve of length `ℓ` traced on the sphere can be parametrized by arc
length, i.e. as a 1-Lipschitz map from the interval `[0, ℓ]` to the
sphere; conversely, any 1-Lipschitz map on `[0, L]` has length at most
`L`. We therefore encode "a curve on the sphere, shorter than the
diameter `2 * R`" as a 1-Lipschitz map `γ` from `[0, L]` into the sphere
with `L < 2 * R`.

The proof shows the stronger statement that the whole curve lies in the
open cap `{x | R ^ 2 / 2 < ⟪γ (L / 2), x⟫_ℝ}` around the midpoint
`γ (L / 2)` of the curve: by the Lipschitz property the chord from
`γ (L / 2)` to `γ t` has length at most `L / 2 < R`, and expanding the
squared chord length with the polarization identity gives
`0 ≤ ⟪γ (L / 2), γ t⟫_ℝ`.
-/

namespace Usa1974P3

open Set
open scoped InnerProductSpace

snip begin

/-- For `t ∈ [0, L]`, the distance in parameter space from `t` to the
midpoint `L / 2` of the interval is at most `L / 2`. -/
theorem dist_le_midpoint {L : ℝ} (t : ℝ) (ht : t ∈ Icc 0 L) :
    dist t (L / 2) ≤ L / 2 := by
  rw [Real.dist_eq, abs_le]
  exact ⟨by linarith [ht.1], by linarith [ht.2]⟩

/-- The squared length of a chord between two points of the sphere of
radius `R` centered at the origin, in terms of their inner product. -/
theorem norm_sub_sq_of_mem_sphere {x y : EuclideanSpace ℝ (Fin 3)} {R : ℝ}
    (hx : x ∈ Metric.sphere 0 R) (hy : y ∈ Metric.sphere 0 R) :
    ‖x - y‖ ^ 2 = 2 * R ^ 2 - 2 * ⟪x, y⟫_ℝ := by
  rw [Metric.mem_sphere, dist_zero_right] at hx hy
  rw [norm_sub_sq_real, hx, hy]
  ring

snip end

problem usa1974_p3 {R L : ℝ} (hR : 0 < R) (hL : 0 ≤ L) (hLR : L < 2 * R)
    {γ : ℝ → EuclideanSpace ℝ (Fin 3)}
    (hγ : LipschitzOnWith 1 γ (Icc 0 L))
    (hsphere : ∀ t ∈ Icc 0 L, γ t ∈ Metric.sphere 0 R) :
    ∃ u ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) R,
      ∀ t ∈ Icc 0 L, 0 ≤ ⟪u, γ t⟫_ℝ := by
  -- Take as center of the hemisphere the midpoint `M = γ (L / 2)` of the curve.
  have hm : L / 2 ∈ Icc (0 : ℝ) L := ⟨by linarith, by linarith⟩
  refine ⟨γ (L / 2), hsphere _ hm, fun t ht => ?_⟩
  -- Every point `γ t` is at distance at most `L / 2 < R` from `M`:
  -- the chord is no longer than the arc from `t` to `L / 2`.
  have hd : dist (γ t) (γ (L / 2)) ≤ L / 2 := by
    have h := hγ.dist_le_mul t ht (L / 2) hm
    rw [NNReal.coe_one, one_mul] at h
    exact le_trans h (dist_le_midpoint t ht)
  -- Squaring, the chord `γ t - M` has squared length strictly less than `R ^ 2`.
  have hsq : ‖γ t - γ (L / 2)‖ ^ 2 < R ^ 2 := by
    rw [← dist_eq_norm]
    exact lt_of_le_of_lt (pow_le_pow_left₀ dist_nonneg hd 2)
      (pow_lt_pow_left₀ (by linarith) (by linarith) (by norm_num))
  -- The polarization identity then forces `0 < ⟪M, γ t⟫`.
  rw [norm_sub_sq_of_mem_sphere (hsphere t ht) (hsphere _ hm)] at hsq
  rw [real_inner_comm]
  linarith [pow_pos hR 2]

end Usa1974P3
