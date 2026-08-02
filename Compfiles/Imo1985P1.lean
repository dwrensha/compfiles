/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Real.Sqrt
public import ProblemExtraction

@[expose] public section

problem_file {
  tags := [.Geometry]
  }

/-!
# International Mathematical Olympiad 1985, Problem 1

A circle has center on the side AB of the cyclic quadrilateral ABCD.
The other three sides are tangent to the circle. Prove that AD + BC = AB.

## Formalization notes

We coordinatize the plane as `EuclideanSpace ℝ (Fin 2)`. Every configuration
satisfying the hypotheses of the problem is similar to one in which the circle
has center `O = (0, 0)` and radius `r > 0`, the side `AB` lies on the x-axis
with `A` on the negative half-axis and `B` on the positive half-axis, and the
quadrilateral lies above the x-axis.

Write `α` and `β` for the interior angles at `A` and `B`, and let `L`, `M`, `N`
be the points where the sides `AD`, `DC`, `CB` touch the circle. In the right
triangle `OLA` (the angle at `L` is right since `AD` is tangent at `L`) the
angle at `A` equals `α`; hence `α < π / 2`, `OA = r / sin α` and
`AL = r / tan α`. Similarly `β < π / 2`, `OB = r / sin β` and
`BN = r / tan β`. Since `ABCD` is cyclic, the angles at `C` and `D` are
`π - α` and `π - β`, so the radii to the touchpoints make angles
`π / 2 + α` (for `L`), `π / 2 + α - β` (for `M`, since `∠LOM = π - ∠D = β`)
and `π / 2 - β` (for `N`) with the positive x-axis. Conversely, for any
`α, β ∈ (0, π / 2)` this construction produces a cyclic quadrilateral
satisfying the hypotheses of the problem, so the configuration is completely
described by the parameters `(r, α, β)`.

With the half-angle substitutions `u = tan (α / 2) ∈ (0, 1)` and
`v = tan (β / 2) ∈ (0, 1)` (so that `sin α = 2u / (1 + u²)`,
`cos α = (1 - u²) / (1 + u²)`, etc.), the four vertices have rational
coordinates in `r, u, v`:
* `A = (-r (1 + u²) / (2u), 0)` and `B = (r (1 + v²) / (2v), 0)`;
* `D`, the intersection of the tangents at `L` and `M`, is
  `r / (1 + u²) • (v - 2u - u²v, 1 - u² + 2uv)`;
* `C`, the intersection of the tangents at `M` and `N`, is
  `r / (1 + v²) • (2v - u + uv², 1 - v² + 2uv)`.

The theorem below is the statement `AD + BC = AB` for these points.
-/

namespace Imo1985P1

abbrev Pt := EuclideanSpace ℝ (Fin 2)

/-- The vertex `A`, on the negative x-axis: `OA = r / sin α` with `u = tan (α/2)`. -/
noncomputable def vtxA (r u : ℝ) : Pt := !₂[-r * (1 + u^2) / (2 * u), 0]

/-- The vertex `B`, on the positive x-axis: `OB = r / sin β` with `v = tan (β/2)`. -/
noncomputable def vtxB (r v : ℝ) : Pt := !₂[r * (1 + v^2) / (2 * v), 0]

/-- The vertex `C`: the intersection of the tangent lines at `M` and `N`. -/
noncomputable def vtxC (r u v : ℝ) : Pt :=
  !₂[r * (2 * v - u + u * v^2) / (1 + v^2), r * (1 - v^2 + 2 * u * v) / (1 + v^2)]

/-- The vertex `D`: the intersection of the tangent lines at `L` and `M`. -/
noncomputable def vtxD (r u v : ℝ) : Pt :=
  !₂[r * (v - 2 * u - u^2 * v) / (1 + u^2), r * (1 - u^2 + 2 * u * v) / (1 + u^2)]

snip begin

-- Solution formalized from https://prase.cz/kalva/imo/isoln/isoln851.html

lemma dist2 (x1 y1 x2 y2 : ℝ) :
    dist (!₂[x1, y1] : Pt) !₂[x2, y2]
      = Real.sqrt ((x1 - x2)^2 + (y1 - y2)^2) := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Real.dist_eq, sq_abs]

lemma one_sub_sq_pos {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) : 0 < 1 - u^2 := by
  calc (0 : ℝ) < (1 - u) * (1 + u) := mul_pos (sub_pos.mpr hu1) (by linarith)
  _ = 1 - u^2 := by ring

lemma dist_AD (r u v : ℝ) (hr : 0 < r) (hu0 : 0 < u) (hu1 : u < 1) (hv0 : 0 < v) :
    dist (vtxA r u) (vtxD r u v) = r * (1 - u^2 + 2 * u * v) / (2 * u) := by
  have hu : u ≠ 0 := ne_of_gt hu0
  have hu2 : (1 + u^2) ≠ 0 := by positivity
  have h1 : 0 < 1 - u^2 + 2 * u * v := by
    have := one_sub_sq_pos hu0 hu1
    have := mul_pos hu0 hv0
    linarith
  have hpos : 0 ≤ r * (1 - u^2 + 2 * u * v) / (2 * u) := by positivity
  simp only [vtxA, vtxD, dist2]
  rw [show (-r * (1 + u^2) / (2 * u) - r * (v - 2 * u - u^2 * v) / (1 + u^2))^2
        + (0 - r * (1 - u^2 + 2 * u * v) / (1 + u^2))^2
        = (r * (1 - u^2 + 2 * u * v) / (2 * u))^2 by field_simp; ring]
  exact Real.sqrt_sq hpos

lemma dist_BC (r u v : ℝ) (hr : 0 < r) (hv0 : 0 < v) (hv1 : v < 1) (hu0 : 0 < u) :
    dist (vtxB r v) (vtxC r u v) = r * (1 - v^2 + 2 * u * v) / (2 * v) := by
  have hv : v ≠ 0 := ne_of_gt hv0
  have hv2 : (1 + v^2) ≠ 0 := by positivity
  have h1 : 0 < 1 - v^2 + 2 * u * v := by
    have := one_sub_sq_pos hv0 hv1
    have := mul_pos hu0 hv0
    linarith
  have hpos : 0 ≤ r * (1 - v^2 + 2 * u * v) / (2 * v) := by positivity
  simp only [vtxB, vtxC, dist2]
  rw [show (r * (1 + v^2) / (2 * v) - r * (2 * v - u + u * v^2) / (1 + v^2))^2
        + (0 - r * (1 - v^2 + 2 * u * v) / (1 + v^2))^2
        = (r * (1 - v^2 + 2 * u * v) / (2 * v))^2 by field_simp; ring]
  exact Real.sqrt_sq hpos

lemma dist_AB (r u v : ℝ) (hr : 0 < r) (hu0 : 0 < u) (hv0 : 0 < v) :
    dist (vtxA r u) (vtxB r v) = r * (1 + u^2) / (2 * u) + r * (1 + v^2) / (2 * v) := by
  have hu : u ≠ 0 := ne_of_gt hu0
  have hv : v ≠ 0 := ne_of_gt hv0
  have hpos : 0 ≤ r * (1 + u^2) / (2 * u) + r * (1 + v^2) / (2 * v) := by positivity
  simp only [vtxA, vtxB, dist2]
  rw [show (-r * (1 + u^2) / (2 * u) - r * (1 + v^2) / (2 * v))^2 + (0 - 0)^2
        = (r * (1 + u^2) / (2 * u) + r * (1 + v^2) / (2 * v))^2 by field_simp; ring]
  exact Real.sqrt_sq hpos

snip end

problem imo1985_p1 (r u v : ℝ) (hr : 0 < r) (hu0 : 0 < u) (hu1 : u < 1)
    (hv0 : 0 < v) (hv1 : v < 1) :
    dist (vtxA r u) (vtxD r u v) + dist (vtxB r v) (vtxC r u v)
      = dist (vtxA r u) (vtxB r v) := by
  have hu : u ≠ 0 := ne_of_gt hu0
  have hv : v ≠ 0 := ne_of_gt hv0
  rw [dist_AD r u v hr hu0 hu1 hv0, dist_BC r u v hr hv0 hv1 hu0,
    dist_AB r u v hr hu0 hv0]
  field_simp
  ring

end Imo1985P1
