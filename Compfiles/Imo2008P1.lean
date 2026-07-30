/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.Geometry.Euclidean.MongePoint
public import ProblemExtraction

@[expose] public section

problem_file {
  tags := [.Geometry]
}

/-!
# International Mathematical Olympiad 2008, Problem 1

Let H be the orthocenter of an acute-angled triangle ABC. The circle Γ_A centered
at the midpoint of BC and passing through H intersects the sideline BC at points
A₁ and A₂. Similarly, define the points B₁, B₂, C₁, and C₂. Prove that the six
points A₁, A₂, B₁, B₂, C₁, C₂ are concyclic.
-/

open Affine EuclideanGeometry
open scoped Real InnerProductSpace RealInnerProductSpace

namespace Imo2008P1

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MetricSpace P] [NormedAddTorsor V P]

/-- The two points where the circle centered at the midpoint of the side through
`t.points i` and `t.points j` and passing through the orthocenter meets that sideline;
in the problem these are the points called `A₁, A₂` (for the side `BC`), etc. -/
def sideInterPts (t : Triangle ℝ P) (i j : Fin 3) : Set P :=
  {p : P | p ∈ line[ℝ, t.points i, t.points j] ∧
    dist p (midpoint ℝ (t.points i) (t.points j)) =
      dist (midpoint ℝ (t.points i) (t.points j)) t.orthocenter}

/-- The six points `A₁, A₂, B₁, B₂, C₁, C₂` of the problem. -/
def sixPoints (t : Triangle ℝ P) : Set P :=
  sideInterPts t 1 2 ∪ sideInterPts t 2 0 ∪ sideInterPts t 0 1

snip begin

/-!
## Solution

We follow the length chase from https://web.evanchen.cc/exams/IMO-2008-notes.pdf
(the second solution there, by Ritwin Narra): the circumcenter `O` of `ABC` is
equidistant from all six points. Indeed, if `D` is the midpoint of `BC`, then
`OD ⟂ BC`; hence for any of the two intersection points `X` of `Γ_A` with the line
`BC`, Pythagoras gives `OX² = OD² + DX² = OD² + DH²`. This last expression is
symmetric in the three sides: writing `b, c, h` for the vectors from `O` to the
endpoints of the side and to `H`, the parallelogram identity yields
`OD² + DH² = (‖h‖² + ‖h - (b + c)‖²) / 2`, where `h - (b + c)` is the vector from
`O` to the third vertex (by Sylvester's theorem `h` is the sum of the three vertex
vectors), so `OD² + DH² = (OH² + R²) / 2` with `R` the circumradius.
-/

/-- Vector form of the length chase: `b, c` are the vectors from the circumcenter to
the two endpoints of a side, `h` the vector from the circumcenter to the orthocenter
and `R` the circumradius. Any point `x` on the sideline whose distance to the
midpoint `(2 : ℝ)⁻¹ • (b + c)` of the side equals the distance from that midpoint to
`h` has squared norm `(R² + ‖h‖²) / 2`, which is independent of the chosen side. -/
theorem norm_sq_vsub_circumcenter_eq {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {b c h : W} {R : ℝ} (hb : ‖b‖ = R) (hc : ‖c‖ = R) (ha : ‖h - (b + c)‖ = R)
    {x : W} {s : ℝ} (hs : x - b = s • (c - b))
    (hd : ‖x - (2 : ℝ)⁻¹ • (b + c)‖ = ‖(2 : ℝ)⁻¹ • (b + c) - h‖) :
    ‖x‖ ^ 2 = (R ^ 2 + ‖h‖ ^ 2) / 2 := by
  -- The line joining the circumcenter to the midpoint of the side is perpendicular
  -- to the side.
  have hortho : ⟪(2 : ℝ)⁻¹ • (b + c), c - b⟫_ℝ = 0 := by
    simp only [real_inner_smul_left, inner_add_left, inner_sub_right,
      real_inner_self_eq_norm_sq, real_inner_comm c b, hb, hc]
    ring
  have hxd : x - (2 : ℝ)⁻¹ • (b + c) = (s - (2 : ℝ)⁻¹) • (c - b) := by
    have e2 : b - (2 : ℝ)⁻¹ • (b + c) = -(2 : ℝ)⁻¹ • (c - b) := by module
    rw [← sub_add_sub_cancel x b ((2 : ℝ)⁻¹ • (b + c)), hs, e2]
    module
  -- Pythagoras in the triangle formed by the circumcenter, the midpoint and `x`.
  have hpyth : ‖x‖ ^ 2 = ‖(2 : ℝ)⁻¹ • (b + c)‖ ^ 2 + ‖x - (2 : ℝ)⁻¹ • (b + c)‖ ^ 2 := by
    have hx : x = (2 : ℝ)⁻¹ • (b + c) + (x - (2 : ℝ)⁻¹ • (b + c)) := by abel
    nth_rewrite 1 [hx]
    rw [norm_add_sq_real, hxd, real_inner_smul_right, hortho]
    ring
  -- The parallelogram identity gives `‖d‖² + ‖h - d‖² = (‖h‖² + ‖h - (b+c)‖²) / 2`.
  have hpara := parallelogram_law_with_norm ℝ ((2 : ℝ)⁻¹ • (b + c)) (h - (2 : ℝ)⁻¹ • (b + c))
  rw [show (2 : ℝ)⁻¹ • (b + c) + (h - (2 : ℝ)⁻¹ • (b + c)) = h by abel,
    show (2 : ℝ)⁻¹ • (b + c) - (h - (2 : ℝ)⁻¹ • (b + c)) = -(h - (b + c)) by module,
    norm_neg, ha] at hpara
  rw [norm_sub_rev ((2 : ℝ)⁻¹ • (b + c)) h] at hd
  rw [hpyth, hd]
  linarith [hpara]

/-- A point on the sideline through `t.points i` and `t.points j` whose distance to
the midpoint of that side equals the distance from the midpoint to the orthocenter
is at distance `√((R² + OH²) / 2)` from the circumcenter. -/
theorem dist_circumcenter_eq_of_mem (t : Triangle ℝ P) (i j : Fin 3) {p : P}
    (hpl : p ∈ line[ℝ, t.points i, t.points j])
    (hdist : dist p (midpoint ℝ (t.points i) (t.points j)) =
      dist (midpoint ℝ (t.points i) (t.points j)) t.orthocenter)
    (hk : ‖t.orthocenter -ᵥ t.circumcenter -
        (t.points i -ᵥ t.circumcenter + (t.points j -ᵥ t.circumcenter))‖ = t.circumradius) :
    dist p t.circumcenter =
      Real.sqrt ((t.circumradius ^ 2 + ‖t.orthocenter -ᵥ t.circumcenter‖ ^ 2) / 2) := by
  have hR : ∀ l : Fin 3, ‖t.points l -ᵥ t.circumcenter‖ = t.circumradius := fun l => by
    rw [← dist_eq_norm_vsub]; exact t.dist_circumcenter_eq_circumradius l
  have hvsub : p -ᵥ t.points i ∈ vectorSpan ℝ {t.points i, t.points j} := by
    have h := AffineSubspace.vsub_mem_direction hpl (left_mem_affineSpan_pair ℝ _ _)
    rwa [direction_affineSpan] at h
  obtain ⟨s, hs⟩ := mem_vectorSpan_pair.1 hvsub
  have hmid : midpoint ℝ (t.points i) (t.points j) -ᵥ t.circumcenter =
      (2 : ℝ)⁻¹ • (t.points i -ᵥ t.circumcenter + (t.points j -ᵥ t.circumcenter)) := by
    rw [midpoint_vsub, ← smul_add, invOf_eq_inv]
  rw [dist_eq_norm_vsub, dist_eq_norm_vsub,
    ← vsub_sub_vsub_cancel_right p (midpoint ℝ (t.points i) (t.points j)) t.circumcenter,
    ← vsub_sub_vsub_cancel_right (midpoint ℝ (t.points i) (t.points j)) t.orthocenter
      t.circumcenter,
    hmid] at hdist
  have hsx : p -ᵥ t.circumcenter - (t.points i -ᵥ t.circumcenter) =
      -s • (t.points j -ᵥ t.circumcenter - (t.points i -ᵥ t.circumcenter)) := by
    have e1 : t.points i -ᵥ t.points j =
        t.points i -ᵥ t.circumcenter - (t.points j -ᵥ t.circumcenter) :=
      (vsub_sub_vsub_cancel_right (t.points i) (t.points j) t.circumcenter).symm
    rw [vsub_sub_vsub_cancel_right, ← hs, e1]
    module
  have hnorm := norm_sq_vsub_circumcenter_eq (hR i) (hR j) hk hsx hdist
  rw [dist_eq_norm_vsub, ← Real.sqrt_sq (norm_nonneg _), hnorm]

snip end

/-- **International Mathematical Olympiad 2008, Problem 1.**
The six points are concyclic; in fact the proof below shows that the circumcenter of
`ABC` is equidistant from all of them, and the hypothesis that the triangle is acute
is not needed (it is included to match the problem statement). -/
problem imo2008_p1 [Fact (Module.finrank ℝ V = 2)] (t : Triangle ℝ P)
    (_hacute : ∀ i j k : Fin 3, i ≠ j → j ≠ k →
      ∠ (t.points i) (t.points j) (t.points k) < π / 2) :
    Concyclic (sixPoints t) := by
  refine ⟨?_, coplanar_of_fact_finrank_eq_two _⟩
  refine ⟨t.circumcenter,
    Real.sqrt ((t.circumradius ^ 2 + ‖t.orthocenter -ᵥ t.circumcenter‖ ^ 2) / 2), ?_⟩
  intro p hp
  have hR : ∀ l : Fin 3, ‖t.points l -ᵥ t.circumcenter‖ = t.circumradius := fun l => by
    rw [← dist_eq_norm_vsub]; exact t.dist_circumcenter_eq_circumradius l
  -- Sylvester's theorem: the orthocenter vector is the sum of the vertex vectors.
  have hsum : t.orthocenter -ᵥ t.circumcenter =
      t.points 0 -ᵥ t.circumcenter + (t.points 1 -ᵥ t.circumcenter) +
        (t.points 2 -ᵥ t.circumcenter) := by
    rw [t.orthocenter_vsub_circumcenter_eq_sum_vsub, Fin.sum_univ_three]
  have hk : ∀ i j k : Fin 3,
      t.orthocenter -ᵥ t.circumcenter -
          (t.points i -ᵥ t.circumcenter + (t.points j -ᵥ t.circumcenter)) =
        t.points k -ᵥ t.circumcenter →
      ‖t.orthocenter -ᵥ t.circumcenter -
          (t.points i -ᵥ t.circumcenter + (t.points j -ᵥ t.circumcenter))‖ =
        t.circumradius := by
    intro i j k h
    rw [h]; exact hR k
  have e120 : t.orthocenter -ᵥ t.circumcenter -
      (t.points 1 -ᵥ t.circumcenter + (t.points 2 -ᵥ t.circumcenter)) =
      t.points 0 -ᵥ t.circumcenter := by
    rw [hsum]; abel
  have e201 : t.orthocenter -ᵥ t.circumcenter -
      (t.points 2 -ᵥ t.circumcenter + (t.points 0 -ᵥ t.circumcenter)) =
      t.points 1 -ᵥ t.circumcenter := by
    rw [hsum]; abel
  have e012 : t.orthocenter -ᵥ t.circumcenter -
      (t.points 0 -ᵥ t.circumcenter + (t.points 1 -ᵥ t.circumcenter)) =
      t.points 2 -ᵥ t.circumcenter := by
    rw [hsum]; abel
  simp only [sixPoints, sideInterPts, Set.mem_union, Set.mem_setOf_eq] at hp
  rcases hp with ((h | h) | h)
  · obtain ⟨hpl, hdist⟩ := h
    exact dist_circumcenter_eq_of_mem t 1 2 hpl hdist (hk 1 2 0 e120)
  · obtain ⟨hpl, hdist⟩ := h
    exact dist_circumcenter_eq_of_mem t 2 0 hpl hdist (hk 2 0 1 e201)
  · obtain ⟨hpl, hdist⟩ := h
    exact dist_circumcenter_eq_of_mem t 0 1 hpl hdist (hk 0 1 2 e012)

end Imo2008P1
