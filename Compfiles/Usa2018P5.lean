/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.Convex.BetweenList
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.Geometry.Euclidean.Sphere.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import ProblemExtraction

@[expose] public section

problem_file {
  tags := [.Geometry]
}

/-!
# USA Mathematical Olympiad 2018, Problem 5

Let `ABCD` be a convex cyclic quadrilateral with `E = AC ∩ BD`, `F = AB ∩ CD`,
`G = DA ∩ BC`. The circumcircle of `△ABE` intersects line `CB` at `B` and `P`, and the
circumcircle of `△ADE` intersects line `CD` at `D` and `Q`. Assume `C, B, P, G` and
`C, Q, D, F` are collinear in that order. Let `M = FP ∩ GQ`. Prove that `∠MAC = 90°`.
-/

open Affine EuclideanGeometry RealInnerProductSpace Module
open scoped Affine EuclideanGeometry Real InnerProductSpace

namespace Usa2018P5

abbrev Pt := EuclideanSpace ℝ (Fin 2)

snip begin

/-!
## Proof overview

We prove the theorem by coordinates. Everything is invariant under similarities, so we
may place `C` at the origin and `A` on the positive x-axis. More precisely, for
`u = A₀ - C₀`, `v = A₁ - C₁` we use the rotated/translated coordinates
`X' = (u * (X₀ - C₀) + v * (X₁ - C₁), -v * (X₀ - C₀) + u * (X₁ - C₁))`, in which
`C' = (0,0)` and `A' = (w, 0)` with `w = u² + v² ≠ 0`. Cross products, dot products and
squared norms simply scale by the factor `u² + v²` under this map (`xfer_cross_eq`,
`xfer_dot_eq`, `xfer_nsq` below), so all hypotheses transport to polynomial identities
in the new coordinates.

Write `B' = (b₁,b₂)`, `D' = (d₁,d₂)`, `E' = (e,0)`. The key observations are:

* By the power of the point `C` with respect to the circumcircles of `△ABE` and `△ADE`
  (lemma `power_origin`), `B'·P' = A'·E' = w·e = D'·Q'`, hence
  `P' = (w·e/|B'|²)·B'` and `Q' = (w·e/|D'|²)·D'`.
* `F'`, `G'`, `M'` are given by Cramer's rule as rational functions of `b₁,b₂,d₁,d₂,e,w`.
* The condition that `A',B',C',D'` are concyclic gives
  `(|B'|² - w·b₁)·d₂ = (|D'|² - w·d₁)·b₂`, and the condition that `E'` lies on line `BD`
  gives `e·(b₂-d₂) = b₂·d₁ - b₁·d₂`.
* Substituting everything, the statement `m₁ = w` (i.e. `MA ⊥ AC`) reduces to a
  polynomial identity which, after clearing denominators, reads
  `(num - w·den)·J = -(b₂·d₂·(b₁d₂-b₂d₁)·R·w²)` where `R` vanishes by the two
  constraints above (this factorization was found and checked with a computer algebra
  system). The whole computation is carried out in lemma `core`.
-/

/-- Two coordinates determine a point. -/
private theorem pt_ext {X Y : Pt} (h0 : X 0 = Y 0) (h1 : X 1 = Y 1) : X = Y :=
  (WithLp.ext_iff 2).mpr (funext (Fin.forall_fin_two.mpr ⟨h0, h1⟩))

/-- Collinearity in coordinates: a point on a line gives a vanishing cross product. -/
theorem cross_of_mem_line {X Y Z : Pt} (h : X ∈ line[ℝ, Y, Z]) :
    (Z 0 - Y 0) * (X 1 - Y 1) - (Z 1 - Y 1) * (X 0 - Y 0) = 0 := by
  rw [← vsub_vadd X Y] at h
  obtain ⟨r, hr⟩ := vadd_left_mem_affineSpan_pair.mp h
  have h0 : (r • (Z -ᵥ Y)) 0 = (X -ᵥ Y) 0 := by rw [hr]
  have h1 : (r • (Z -ᵥ Y)) 1 = (X -ᵥ Y) 1 := by rw [hr]
  simp only [PiLp.smul_apply, vsub_eq_sub, PiLp.sub_apply, smul_eq_mul] at h0 h1
  linear_combination (Z 1 - Y 1) * h0 - (Z 0 - Y 0) * h1

/-- A vanishing cross product gives collinearity. -/
theorem collinear_of_cross {X Y Z : Pt}
    (h : (Z 0 - Y 0) * (X 1 - Y 1) - (Z 1 - Y 1) * (X 0 - Y 0) = 0) :
    Collinear ℝ ({X, Y, Z} : Set Pt) := by
  by_cases hZY : Z = Y
  · subst hZY
    rw [Set.pair_eq_singleton]
    exact collinear_pair ℝ X Z
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  have hD : (Z 0 - Y 0) ^ 2 + (Z 1 - Y 1) ^ 2 ≠ 0 := by
    intro hD0
    rw [add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _), sq_eq_zero_iff,
      sq_eq_zero_iff] at hD0
    exact hZY (pt_ext (sub_eq_zero.mp hD0.1) (sub_eq_zero.mp hD0.2))
  refine ⟨Y, Z -ᵥ Y, fun p hp => ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with h | h | h <;> subst p
  · set r := ((Z 0 - Y 0) * (X 0 - Y 0) + (Z 1 - Y 1) * (X 1 - Y 1)) /
      ((Z 0 - Y 0) ^ 2 + (Z 1 - Y 1) ^ 2) with hr_eq
    have h0 : X 0 - Y 0 = r * (Z 0 - Y 0) := by
      rw [hr_eq, div_mul_eq_mul_div, eq_div_iff hD]
      linear_combination (-(Z 1 - Y 1)) * h
    have h1 : X 1 - Y 1 = r * (Z 1 - Y 1) := by
      rw [hr_eq, div_mul_eq_mul_div, eq_div_iff hD]
      linear_combination (Z 0 - Y 0) * h
    refine ⟨r, (WithLp.ext_iff 2).mpr (funext ?_)⟩
    rw [Fin.forall_fin_two]
    constructor <;>
      simp only [vadd_eq_add, vsub_eq_sub, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply,
        smul_eq_mul]
    · linear_combination h0
    · linear_combination h1
  · exact ⟨0, by simp⟩
  · exact ⟨1, by simp⟩

/-- Two nondegenerate non-parallel lines have a nonzero cross product of direction
vectors. (The nondegeneracy hypotheses are needed: if `X = Y` then `line[ℝ, Y, X]` is a
single point, which is not `AffineSubspace.Parallel` to any line, while the cross
product vanishes automatically.) -/
theorem cross_ne_zero_of_not_parallel {Y X Z W : Pt} (hYX : Y ≠ X) (hZW : Z ≠ W)
    (h : ¬ line[ℝ, Y, X] ∥ line[ℝ, Z, W]) :
    (X 0 - Y 0) * (W 1 - Z 1) - (X 1 - Y 1) * (W 0 - Z 0) ≠ 0 := by
  intro hc
  apply h
  rw [AffineSubspace.affineSpan_pair_parallel_iff_exists_unit_smul']
  have hD : (X 0 - Y 0) ^ 2 + (X 1 - Y 1) ^ 2 ≠ 0 := by
    intro hD0
    rw [add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _), sq_eq_zero_iff,
      sq_eq_zero_iff] at hD0
    exact hYX (pt_ext (sub_eq_zero.mp hD0.1) (sub_eq_zero.mp hD0.2)).symm
  set r := ((X 0 - Y 0) * (W 0 - Z 0) + (X 1 - Y 1) * (W 1 - Z 1)) /
    ((X 0 - Y 0) ^ 2 + (X 1 - Y 1) ^ 2) with hr_eq
  have h0 : r * (X 0 - Y 0) = W 0 - Z 0 := by
    rw [hr_eq, div_mul_eq_mul_div, div_eq_iff hD]
    linear_combination (X 1 - Y 1) * hc
  have h1 : r * (X 1 - Y 1) = W 1 - Z 1 := by
    rw [hr_eq, div_mul_eq_mul_div, div_eq_iff hD]
    linear_combination (-(X 0 - Y 0)) * hc
  have hr : r ≠ 0 := by
    intro hr0
    have hW0 : W 0 - Z 0 = 0 := by rw [← h0, hr0, zero_mul]
    have hW1 : W 1 - Z 1 = 0 := by rw [← h1, hr0, zero_mul]
    exact hZW (pt_ext (sub_eq_zero.mp hW0) (sub_eq_zero.mp hW1)).symm
  refine ⟨Units.mk0 r hr, (WithLp.ext_iff 2).mpr (funext ?_)⟩
  rw [Fin.forall_fin_two]
  constructor <;>
    simp only [Units.smul_def, Units.val_mk0, PiLp.smul_apply, vsub_eq_sub, PiLp.sub_apply,
      smul_eq_mul]
  · linear_combination h0
  · linear_combination h1

/-- A sphere membership equation in coordinates. -/
theorem dist_sq_eq_of_dist_eq {X O : Pt} {r : ℝ} (h : dist X O = r) :
    (X 0 - O 0) ^ 2 + (X 1 - O 1) ^ 2 = r ^ 2 := by
  rw [← h, dist_eq_norm_vsub, EuclideanSpace.norm_eq,
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _), Fin.sum_univ_two]
  simp only [vsub_eq_sub, PiLp.sub_apply, Real.norm_eq_abs, sq_abs]

/-- The inner product of two vectors in coordinates. -/
theorem inner_vsub_eq (M A C : Pt) :
    ⟪M -ᵥ A, C -ᵥ A⟫_ℝ = (M 0 - A 0) * (C 0 - A 0) + (M 1 - A 1) * (C 1 - A 1) := by
  simp only [PiLp.inner_apply, Fin.sum_univ_two, vsub_eq_sub, PiLp.sub_apply,
    RCLike.inner_apply, conj_trivial]
  ring

/-- The rotated coordinate map is injective (when `u² + v² ≠ 0`). -/
theorem eq_of_rot {u v : ℝ} (huv : u ^ 2 + v ^ 2 ≠ 0) {X Y : Pt}
    (h1 : u * (X 0 - Y 0) + v * (X 1 - Y 1) = 0)
    (h2 : -v * (X 0 - Y 0) + u * (X 1 - Y 1) = 0) : X = Y := by
  have h0 : X 0 = Y 0 := by
    have hmul : (u ^ 2 + v ^ 2) * (X 0 - Y 0) = 0 := by
      linear_combination u * h1 - v * h2
    rcases mul_eq_zero.mp hmul with h | h
    · exact absurd h huv
    · exact sub_eq_zero.mp h
  have h1' : X 1 = Y 1 := by
    have hmul : (u ^ 2 + v ^ 2) * (X 1 - Y 1) = 0 := by
      linear_combination v * h1 + u * h2
    rcases mul_eq_zero.mp hmul with h | h
    · exact absurd h huv
    · exact sub_eq_zero.mp h
  exact pt_ext h0 h1'

/-- If `X ≠ Y` then the squared distance of their coordinates is nonzero. -/
lemma sq_sum_ne_zero_of_ne {X Y : Pt} (h : X ≠ Y) : (X 0 - Y 0)^2 + (X 1 - Y 1)^2 ≠ 0 := by
  intro hz
  have h1 : (X 0 - Y 0)^2 = 0 := by
    have hs : (X 1 - Y 1)^2 ≥ 0 := sq_nonneg _
    nlinarith [sq_nonneg (X 0 - Y 0)]
  have h2 : (X 1 - Y 1)^2 = 0 := by
    have hs : (X 0 - Y 0)^2 ≥ 0 := sq_nonneg _
    nlinarith [sq_nonneg (X 1 - Y 1)]
  have e0 : X 0 = Y 0 := sub_eq_zero.mp (sq_eq_zero_iff.mp h1)
  have e1 : X 1 = Y 1 := sub_eq_zero.mp (sq_eq_zero_iff.mp h2)
  apply h
  rw [WithLp.ext_iff]
  apply funext
  intro i
  fin_cases i
  · exact e0
  · exact e1

/-- The rotated coordinate map preserves cross products up to the factor `u² + v²`. -/
lemma xfer_cross_eq {u v : ℝ} (C Y Z X : Pt) {y1 y2 z1 z2 x1 x2 : ℝ}
    (hy1 : u * (Y 0 - C 0) + v * (Y 1 - C 1) = y1)
    (hy2 : -v * (Y 0 - C 0) + u * (Y 1 - C 1) = y2)
    (hz1 : u * (Z 0 - C 0) + v * (Z 1 - C 1) = z1)
    (hz2 : -v * (Z 0 - C 0) + u * (Z 1 - C 1) = z2)
    (hx1 : u * (X 0 - C 0) + v * (X 1 - C 1) = x1)
    (hx2 : -v * (X 0 - C 0) + u * (X 1 - C 1) = x2) :
    (z1 - y1) * (x2 - y2) - (z2 - y2) * (x1 - y1) =
      (u^2 + v^2) * ((Z 0 - Y 0) * (X 1 - Y 1) - (Z 1 - Y 1) * (X 0 - Y 0)) := by
  rw [← hy1, ← hy2, ← hz1, ← hz2, ← hx1, ← hx2]
  ring

/-- The rotated coordinate map preserves cross products of direction vectors of two
lines, up to the factor `u² + v²`. -/
lemma xfer_cross4_eq {u v : ℝ} (C Y X Z W : Pt) {y1 y2 x1 x2 z1 z2 w1 w2 : ℝ}
    (hy1 : u * (Y 0 - C 0) + v * (Y 1 - C 1) = y1)
    (hy2 : -v * (Y 0 - C 0) + u * (Y 1 - C 1) = y2)
    (hx1 : u * (X 0 - C 0) + v * (X 1 - C 1) = x1)
    (hx2 : -v * (X 0 - C 0) + u * (X 1 - C 1) = x2)
    (hz1 : u * (Z 0 - C 0) + v * (Z 1 - C 1) = z1)
    (hz2 : -v * (Z 0 - C 0) + u * (Z 1 - C 1) = z2)
    (hw1 : u * (W 0 - C 0) + v * (W 1 - C 1) = w1)
    (hw2 : -v * (W 0 - C 0) + u * (W 1 - C 1) = w2) :
    (x1 - y1) * (w2 - z2) - (x2 - y2) * (w1 - z1) =
      (u^2 + v^2) * ((X 0 - Y 0) * (W 1 - Z 1) - (X 1 - Y 1) * (W 0 - Z 0)) := by
  rw [← hy1, ← hy2, ← hx1, ← hx2, ← hz1, ← hz2, ← hw1, ← hw2]
  ring

/-- The rotated coordinate map preserves squared norms up to the factor `u² + v²`. -/
lemma xfer_nsq {u v : ℝ} (C X : Pt) {x1 x2 : ℝ}
    (hx1 : u * (X 0 - C 0) + v * (X 1 - C 1) = x1)
    (hx2 : -v * (X 0 - C 0) + u * (X 1 - C 1) = x2) :
    x1^2 + x2^2 = (u^2 + v^2) * ((X 0 - C 0)^2 + (X 1 - C 1)^2) := by
  rw [← hx1, ← hx2]
  ring

/-- The rotated coordinate map preserves squared distances up to the factor `u² + v²`. -/
lemma xfer_sub_nsq {u v : ℝ} (C X Y : Pt) {x1 x2 y1 y2 : ℝ}
    (hx1 : u * (X 0 - C 0) + v * (X 1 - C 1) = x1)
    (hx2 : -v * (X 0 - C 0) + u * (X 1 - C 1) = x2)
    (hy1 : u * (Y 0 - C 0) + v * (Y 1 - C 1) = y1)
    (hy2 : -v * (Y 0 - C 0) + u * (Y 1 - C 1) = y2) :
    (x1 - y1)^2 + (x2 - y2)^2 = (u^2 + v^2) * ((X 0 - Y 0)^2 + (X 1 - Y 1)^2) := by
  rw [← hx1, ← hx2, ← hy1, ← hy2]
  ring

/-- The rotated coordinate map preserves dot products up to the factor `u² + v²`. -/
lemma xfer_dot_eq {u v : ℝ} (C X Y Z W : Pt) {x1 x2 y1 y2 z1 z2 w1 w2 : ℝ}
    (hx1 : u * (X 0 - C 0) + v * (X 1 - C 1) = x1)
    (hx2 : -v * (X 0 - C 0) + u * (X 1 - C 1) = x2)
    (hy1 : u * (Y 0 - C 0) + v * (Y 1 - C 1) = y1)
    (hy2 : -v * (Y 0 - C 0) + u * (Y 1 - C 1) = y2)
    (hz1 : u * (Z 0 - C 0) + v * (Z 1 - C 1) = z1)
    (hz2 : -v * (Z 0 - C 0) + u * (Z 1 - C 1) = z2)
    (hw1 : u * (W 0 - C 0) + v * (W 1 - C 1) = w1)
    (hw2 : -v * (W 0 - C 0) + u * (W 1 - C 1) = w2) :
    (x1 - y1) * (z1 - w1) + (x2 - y2) * (z2 - w2) =
      (u^2 + v^2) * ((X 0 - Y 0) * (Z 0 - W 0) + (X 1 - Y 1) * (Z 1 - W 1)) := by
  rw [← hx1, ← hx2, ← hy1, ← hy2, ← hz1, ← hz2, ← hw1, ← hw2]
  ring

/-- Membership of a sphere transports to the rotated coordinates (with the radius
scaled by `√(u² + v²)`). -/
lemma xfer_sphere {u v : ℝ} (C X O : Pt) (r : ℝ) {x1 x2 o1 o2 : ℝ}
    (hx1 : u * (X 0 - C 0) + v * (X 1 - C 1) = x1)
    (hx2 : -v * (X 0 - C 0) + u * (X 1 - C 1) = x2)
    (ho1 : u * (O 0 - C 0) + v * (O 1 - C 1) = o1)
    (ho2 : -v * (O 0 - C 0) + u * (O 1 - C 1) = o2)
    (hd : (X 0 - O 0)^2 + (X 1 - O 1)^2 = r^2) :
    (x1 - o1)^2 + (x2 - o2)^2 = (Real.sqrt (u^2 + v^2) * r)^2 := by
  rw [← hx1, ← hx2, ← ho1, ← ho2, mul_pow, Real.sq_sqrt (by positivity), ← hd]
  ring

/-- Power of a point at the origin: if `X = (x1,x2)` and `Y = (y1,y2)` are two distinct
points of a circle with center `(o1,o2)` and radius `r`, and `X, Y` are collinear with
the origin, then `X · Y = |O|² - r²`, the power of the origin with respect to the
circle. -/
lemma power_origin {x1 x2 y1 y2 o1 o2 r : ℝ}
    (hx : (x1 - o1)^2 + (x2 - o2)^2 = r^2)
    (hy : (y1 - o1)^2 + (y2 - o2)^2 = r^2)
    (hcol : x1 * y2 = x2 * y1)
    (hne : (x1 - y1)^2 + (x2 - y2)^2 ≠ 0) :
    x1 * y1 + x2 * y2 = o1^2 + o2^2 - r^2 := by
  have key : (x1 * y1 + x2 * y2 - (o1^2 + o2^2 - r^2)) * ((x1 - y1)^2 + (x2 - y2)^2) = 0 := by
    linear_combination
      (x1 * y1 + x2 * y2 - (y1^2 + y2^2)) * hx +
      (x1 * y1 + x2 * y2 - (x1^2 + x2^2)) * hy +
      (2 * (x1 * y2 - x2 * y1) - 2 * x1 * o2 + 2 * x2 * o1 + 2 * y1 * o2 - 2 * y2 * o1) * hcol
  rcases mul_eq_zero.mp key with h | h
  · linear_combination h
  · exact absurd h hne

set_option maxHeartbeats 800000 in
/-- The coordinate heart of the problem. With `C = (0,0)`, `A = (w,0)`, `B = (b1,b2)`,
`D = (d1,d2)`, `E = (e,0)`, the points `P, Q, F, G, M` constructed as in the problem
satisfy `m1 = w`, i.e. `MA ⊥ AC`. -/
lemma core {b1 b2 d1 d2 e w : ℝ} {f1 f2 g1 g2 p1 p2 q1 q2 m1 m2 : ℝ}
    {o1 o2 r o3 o4 r2 o5 o6 r3 : ℝ}
    (hw : w ≠ 0)
    (hBn : b1^2 + b2^2 ≠ 0) (hDn : d1^2 + d2^2 ≠ 0)
    (hbd : b2 ≠ d2)
    -- Ω through A=(w,0), B, C=(0,0), D
    (hcA : (w - o1)^2 + (0 - o2)^2 = r^2) (hcB : (b1 - o1)^2 + (b2 - o2)^2 = r^2)
    (hcC : (0 - o1)^2 + (0 - o2)^2 = r^2) (hcD : (d1 - o1)^2 + (d2 - o2)^2 = r^2)
    -- E on line BD
    (hE : e * (b2 - d2) = b2 * d1 - b1 * d2)
    -- ω₁ through A, B, E=(e,0), P=(p1,p2)
    (h1A : (w - o3)^2 + (0 - o4)^2 = r2^2) (h1B : (b1 - o3)^2 + (b2 - o4)^2 = r2^2)
    (h1E : (e - o3)^2 + (0 - o4)^2 = r2^2) (h1P : (p1 - o3)^2 + (p2 - o4)^2 = r2^2)
    (hAE : (w - e)^2 ≠ 0)
    (hBP : (b1 - p1)^2 + (b2 - p2)^2 ≠ 0)
    (hcolBP : b1 * p2 = b2 * p1)
    -- ω₂ through A, D, E, Q
    (h2A : (w - o5)^2 + (0 - o6)^2 = r3^2) (h2D : (d1 - o5)^2 + (d2 - o6)^2 = r3^2)
    (h2E : (e - o5)^2 + (0 - o6)^2 = r3^2) (h2Q : (q1 - o5)^2 + (q2 - o6)^2 = r3^2)
    (hDQ : (d1 - q1)^2 + (d2 - q2)^2 ≠ 0)
    (hcolDQ : d1 * q2 = d2 * q1)
    -- F on line AB and line CD
    (eqF1 : (b1 - w) * (f2 - 0) - (b2 - 0) * (f1 - w) = 0)
    (eqF2 : d1 * f2 - d2 * f1 = 0)
    (hdenF : (b1 - w) * d2 - b2 * d1 ≠ 0)
    -- G on line DA and line BC
    (eqG1 : (w - d1) * (g2 - d2) - (0 - d2) * (g1 - d1) = 0)
    (eqG2 : (0 - b1) * (g2 - b2) - (0 - b2) * (g1 - b1) = 0)
    (hdenG : (w - d1) * (0 - b2) - (0 - d2) * (0 - b1) ≠ 0)
    -- M on line FP and line GQ
    (eqM1 : (p1 - f1) * (m2 - f2) - (p2 - f2) * (m1 - f1) = 0)
    (eqM2 : (q1 - g1) * (m2 - g2) - (q2 - g2) * (m1 - g1) = 0)
    (hdetM : (p1 - f1) * (q2 - g2) - (p2 - f2) * (q1 - g1) ≠ 0) :
    m1 = w := by
  -- power relations
  have hAE' : (w - e)^2 + (0 - 0)^2 ≠ 0 := by
    have h : (w - e)^2 + (0 - 0)^2 = (w - e)^2 := by ring
    rw [h]; exact hAE
  have hAEpow : w * e + 0 * 0 = o3^2 + o4^2 - r2^2 :=
    power_origin h1A h1E (by ring) hAE'
  have hBPpow : b1 * p1 + b2 * p2 = o3^2 + o4^2 - r2^2 :=
    power_origin h1B h1P hcolBP hBP
  have hPpow : b1 * p1 + b2 * p2 = w * e := by
    linear_combination hBPpow - hAEpow
  have hAEpow2 : w * e + 0 * 0 = o5^2 + o6^2 - r3^2 :=
    power_origin h2A h2E (by ring) hAE'
  have hDQpow : d1 * q1 + d2 * q2 = o5^2 + o6^2 - r3^2 :=
    power_origin h2D h2Q hcolDQ hDQ
  have hQpow : d1 * q1 + d2 * q2 = w * e := by
    linear_combination hDQpow - hAEpow2
  -- solved values for P, Q
  have hP1d : (b1^2 + b2^2) * p1 = b1 * (w * e) := by
    linear_combination b1 * hPpow - b2 * hcolBP
  have hP2d : (b1^2 + b2^2) * p2 = b2 * (w * e) := by
    linear_combination b2 * hPpow + b1 * hcolBP
  have hQ1d : (d1^2 + d2^2) * q1 = d1 * (w * e) := by
    linear_combination d1 * hQpow - d2 * hcolDQ
  have hQ2d : (d1^2 + d2^2) * q2 = d2 * (w * e) := by
    linear_combination d2 * hQpow + d1 * hcolDQ
  have hp1v : p1 = b1 * (w * e) / (b1^2 + b2^2) := by
    rw [eq_div_iff hBn]; linear_combination hP1d
  have hp2v : p2 = b2 * (w * e) / (b1^2 + b2^2) := by
    rw [eq_div_iff hBn]; linear_combination hP2d
  have hq1v : q1 = d1 * (w * e) / (d1^2 + d2^2) := by
    rw [eq_div_iff hDn]; linear_combination hQ1d
  have hq2v : q2 = d2 * (w * e) / (d1^2 + d2^2) := by
    rw [eq_div_iff hDn]; linear_combination hQ2d
  -- solved values for F, G (Cramer's rule)
  have hf1 : (b1 * d2 - b2 * d1 - d2 * w) * f1 = -(b2 * d1 * w) := by
    linear_combination d1 * eqF1 - (b1 - w) * eqF2
  have hf2 : (b1 * d2 - b2 * d1 - d2 * w) * f2 = -(b2 * d2 * w) := by
    linear_combination d2 * eqF1 - b2 * eqF2
  have hg1 : (b1 * d2 - b2 * d1 + b2 * w) * g1 = b1 * d2 * w := by
    linear_combination b1 * eqG1 + (w - d1) * eqG2
  have hg2 : (b1 * d2 - b2 * d1 + b2 * w) * g2 = b2 * d2 * w := by
    linear_combination b2 * eqG1 - d2 * eqG2
  have hdenF' : (b1 * d2 - b2 * d1 - d2 * w) ≠ 0 := by
    have h : (b1 - w) * d2 - b2 * d1 = (b1 * d2 - b2 * d1 - d2 * w) := by ring
    rwa [h] at hdenF
  have hdenG' : (b1 * d2 - b2 * d1 + b2 * w) ≠ 0 := by
    have h : (w - d1) * (0 - b2) - (0 - d2) * (0 - b1) = -(b1 * d2 - b2 * d1 + b2 * w) := by ring
    rw [h] at hdenG
    exact neg_ne_zero.mp hdenG
  have hf1v : f1 = -(b2 * d1 * w) / (b1 * d2 - b2 * d1 - d2 * w) := by
    rw [eq_div_iff hdenF']; linear_combination hf1
  have hf2v : f2 = -(b2 * d2 * w) / (b1 * d2 - b2 * d1 - d2 * w) := by
    rw [eq_div_iff hdenF']; linear_combination hf2
  have hg1v : g1 = b1 * d2 * w / (b1 * d2 - b2 * d1 + b2 * w) := by
    rw [eq_div_iff hdenG']; linear_combination hg1
  have hg2v : g2 = b2 * d2 * w / (b1 * d2 - b2 * d1 + b2 * w) := by
    rw [eq_div_iff hdenG']; linear_combination hg2
  -- normal forms of the denominator-nonvanishing facts, for `field_simp`
  have hdenF'' : (b1 * d2 - b2 * d1 - w * d2) ≠ 0 := by
    intro h; apply hdenF'; linear_combination h
  have hdenG'' : (b1 * d2 - b2 * d1 + w * b2) ≠ 0 := by
    intro h; apply hdenG'; linear_combination h
  -- M: Cramer's rule eliminates m2
  have hm1 : ((p1 - f1) * (q2 - g2) - (p2 - f2) * (q1 - g1)) * m1 =
      (p1 - f1) * ((q2 - g2) * g1 - (q1 - g1) * g2) -
      (q1 - g1) * ((p2 - f2) * f1 - (p1 - f1) * f2) := by
    linear_combination (q1 - g1) * eqM1 - (p1 - f1) * eqM2
  rw [hp1v, hp2v, hq1v, hq2v, hf1v, hf2v, hg1v, hg2v] at hm1 hdetM
  set DT := (b1 * (w * e) / (b1^2 + b2^2) - -(b2 * d1 * w) / (b1 * d2 - b2 * d1 - d2 * w)) *
      (d2 * (w * e) / (d1^2 + d2^2) - b2 * d2 * w / (b1 * d2 - b2 * d1 + b2 * w)) -
      (b2 * (w * e) / (b1^2 + b2^2) - -(b2 * d2 * w) / (b1 * d2 - b2 * d1 - d2 * w)) *
      (d1 * (w * e) / (d1^2 + d2^2) - b1 * d2 * w / (b1 * d2 - b2 * d1 + b2 * w)) with hDT
  set NM := (b1 * (w * e) / (b1^2 + b2^2) - -(b2 * d1 * w) / (b1 * d2 - b2 * d1 - d2 * w)) *
      ((d2 * (w * e) / (d1^2 + d2^2) - b2 * d2 * w / (b1 * d2 - b2 * d1 + b2 * w)) *
        (b1 * d2 * w / (b1 * d2 - b2 * d1 + b2 * w)) -
        (d1 * (w * e) / (d1^2 + d2^2) - b1 * d2 * w / (b1 * d2 - b2 * d1 + b2 * w)) *
        (b2 * d2 * w / (b1 * d2 - b2 * d1 + b2 * w))) -
      (d1 * (w * e) / (d1^2 + d2^2) - b1 * d2 * w / (b1 * d2 - b2 * d1 + b2 * w)) *
      ((b2 * (w * e) / (b1^2 + b2^2) - -(b2 * d2 * w) / (b1 * d2 - b2 * d1 - d2 * w)) *
        (-(b2 * d1 * w) / (b1 * d2 - b2 * d1 - d2 * w)) -
        (b1 * (w * e) / (b1^2 + b2^2) - -(b2 * d1 * w) / (b1 * d2 - b2 * d1 - d2 * w)) *
        (-(b2 * d2 * w) / (b1 * d2 - b2 * d1 - d2 * w))) with hNM
  -- concyclicity constraint K1
  have h2o1 : 2 * o1 = w := by
    have h : w * (w - 2 * o1) = 0 := by linear_combination hcA - hcC
    rcases mul_eq_zero.mp h with h1 | h2
    · exact absurd h1 hw
    · linear_combination -h2
  have hK1 : (b1^2 + b2^2 - w * b1) * d2 - (d1^2 + d2^2 - w * d1) * b2 = 0 := by
    linear_combination d2 * hcB - b2 * hcD + (b2 - d2) * hcC + (b1 * d2 - b2 * d1) * h2o1
  -- the key polynomial R vanishes
  set R := w^2 * (b1 + d1 - w) * e^2 - w * (d1 * (b1^2 + b2^2) + b1 * (d1^2 + d2^2)) * e +
    w * (b1^2 + b2^2) * (d1^2 + d2^2) with hRdef
  have hstep : (b2 - d2)^2 * R =
      w * (b1 * b2 * d1 - b1 * d1 * d2 + b1 * d2 * w + b2^2 * d2 - b2 * d1 * w - b2 * d2^2) *
        ((b1^2 + b2^2 - w * b1) * d2 - (d1^2 + d2^2 - w * d1) * b2) +
      (e * (b2 - d2) - (b2 * d1 - b1 * d2)) *
        (w^2 * (b1 + d1 - w) * (e * (b2 - d2) + (b2 * d1 - b1 * d2)) -
         w * (d1 * (b1^2 + b2^2) + b1 * (d1^2 + d2^2)) * (b2 - d2)) := by
    ring
  rw [hK1, hE] at hstep
  have hbd2 : (b2 - d2)^2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr hbd)
  have hR : R = 0 := by
    have h : (b2 - d2)^2 * R = 0 := by linear_combination hstep
    rcases mul_eq_zero.mp h with h1 | h2
    · exact absurd h1 hbd2
    · exact h2
  -- master identity
  have master : (NM - w * DT) *
      ((b1^2 + b2^2) * (d1^2 + d2^2) * (b1 * d2 - b2 * d1 - d2 * w) *
        (b1 * d2 - b2 * d1 + b2 * w)) = -(b2 * d2 * (b1 * d2 - b2 * d1) * R * w^2) := by
    rw [hNM, hDT]
    field_simp [hBn, hDn, hdenF'', hdenG'']
    ring
  have hJ : (b1^2 + b2^2) * (d1^2 + d2^2) * (b1 * d2 - b2 * d1 - d2 * w) *
      (b1 * d2 - b2 * d1 + b2 * w) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hBn hDn) hdenF') hdenG'
  rw [hR] at master
  simp only [mul_zero, zero_mul, neg_zero] at master
  rcases mul_eq_zero.mp master with h1 | h2
  swap
  · exact absurd h2 hJ
  have hN : NM = w * DT := by linear_combination h1
  rw [hN] at hm1
  have hfinal : DT * (m1 - w) = 0 := by linear_combination hm1
  rcases mul_eq_zero.mp hfinal with h3 | h4
  · exact absurd h3 hdetM
  · linear_combination h4

/-- Extraction of the usable content of a 4-point strict betweenness hypothesis. -/
lemma sbtw4_extract {C B P G : Pt} (h : [C, B, P, G].Sbtw ℝ) :
    Wbtw ℝ C B P ∧ Wbtw ℝ C B G ∧ Wbtw ℝ C P G ∧ Wbtw ℝ B P G ∧
    C ≠ B ∧ C ≠ P ∧ C ≠ G ∧ B ≠ P ∧ B ≠ G ∧ P ≠ G := by
  obtain ⟨hw, hne⟩ := h
  rw [List.wbtw_cons] at hw
  obtain ⟨hp1, hw2⟩ := hw
  rw [List.wbtw_cons] at hw2
  obtain ⟨hp2, _⟩ := hw2
  have hp1' := List.Pairwise.of_cons hp1
  have hne1 := List.Pairwise.of_cons hne
  have hne2 := List.Pairwise.of_cons hne1
  exact ⟨List.rel_of_pairwise_cons hp1 (by simp),
         List.rel_of_pairwise_cons hp1 (by simp),
         List.rel_of_pairwise_cons hp1' (by simp),
         List.rel_of_pairwise_cons hp2 (by simp),
         List.rel_of_pairwise_cons hne (by simp),
         List.rel_of_pairwise_cons hne (by simp),
         List.rel_of_pairwise_cons hne (by simp),
         List.rel_of_pairwise_cons hne1 (by simp),
         List.rel_of_pairwise_cons hne1 (by simp),
         List.rel_of_pairwise_cons hne2 (by simp)⟩

snip end

problem usa2018_p5
    (A B C D E F G P Q M : Pt)
    (hABCD : Concyclic ({A, B, C, D} : Set Pt))
    (hEAC : Sbtw ℝ A E C) (hEBD : Sbtw ℝ B E D)
    (hPc : Cospherical ({A, B, E, P} : Set Pt))
    (hQc : Cospherical ({A, D, E, Q} : Set Pt))
    (hCBPG : [C, B, P, G].Sbtw ℝ) (hCQDF : [C, Q, D, F].Sbtw ℝ)
    (hFAB : F ∈ line[ℝ, A, B]) (hGDA : G ∈ line[ℝ, D, A])
    (hMFP : M ∈ line[ℝ, F, P]) (hMGQ : M ∈ line[ℝ, G, Q])
    (hAB : A ≠ B) (hAD : A ≠ D) (hMA : M ≠ A) (hFP : F ≠ P) (hGQ : G ≠ Q)
    (hnpF : ¬ line[ℝ, A, B] ∥ line[ℝ, C, D])
    (hnpG : ¬ line[ℝ, D, A] ∥ line[ℝ, B, C])
    (hnpM : ¬ line[ℝ, F, P] ∥ line[ℝ, G, Q]) :
    ∠ M A C = Real.pi / 2 := by
  have _ := hMA -- (hypothesis implicit in the named angle `∠MAC`)
  -- basic distinctness facts
  have hAC : A ≠ C := hEAC.left_ne_right
  have hAEn : A ≠ E := hEAC.left_ne
  obtain ⟨wCBP, wCBG, _wCPG, _wBPG, nCB, _nCP, _nCG, nBP, _nBG, _nPG⟩ := sbtw4_extract hCBPG
  obtain ⟨wCQD, _wCQF, wCDF, _wQDF, _nCQ, nCD, _nCF, nQD, _nQF, _nDF⟩ := sbtw4_extract hCQDF
  -- collinearity facts needed below
  have hEline : E ∈ line[ℝ, A, C] := hEAC.wbtw.mem_affineSpan
  have hElineBD : E ∈ line[ℝ, B, D] := hEBD.wbtw.mem_affineSpan
  have hPline : P ∈ line[ℝ, C, B] :=
    wCBP.collinear.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) nCB
  have hGline : G ∈ line[ℝ, C, B] :=
    wCBG.collinear.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) nCB
  have hQline : Q ∈ line[ℝ, C, D] :=
    wCQD.collinear.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) nCD
  have hFline : F ∈ line[ℝ, C, D] :=
    wCDF.collinear.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) nCD
  -- the three circles
  obtain ⟨sΩ, hΩ⟩ := cospherical_iff_exists_sphere.mp hABCD.1
  obtain ⟨s1, hs1⟩ := cospherical_iff_exists_sphere.mp hPc
  obtain ⟨s2, hs2⟩ := cospherical_iff_exists_sphere.mp hQc
  -- coordinate setup: rotation/scaling sending C to 0 and A to (w, 0)
  obtain ⟨u, hu⟩ : ∃ x : ℝ, A 0 - C 0 = x := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ x : ℝ, A 1 - C 1 = x := ⟨_, rfl⟩
  obtain ⟨w, hwd⟩ : ∃ x : ℝ, u^2 + v^2 = x := ⟨_, rfl⟩
  have hu2v2 : u^2 + v^2 ≠ 0 := by
    rw [← hu, ← hv]
    exact sq_sum_ne_zero_of_ne hAC
  have hw : w ≠ 0 := by
    rw [← hwd]
    exact hu2v2
  -- primed coordinates of all points
  obtain ⟨b1, hb1⟩ : ∃ x : ℝ, u * (B 0 - C 0) + v * (B 1 - C 1) = x := ⟨_, rfl⟩
  obtain ⟨b2, hb2⟩ : ∃ x : ℝ, -v * (B 0 - C 0) + u * (B 1 - C 1) = x := ⟨_, rfl⟩
  obtain ⟨d1, hd1⟩ : ∃ x : ℝ, u * (D 0 - C 0) + v * (D 1 - C 1) = x := ⟨_, rfl⟩
  obtain ⟨d2, hd2⟩ : ∃ x : ℝ, -v * (D 0 - C 0) + u * (D 1 - C 1) = x := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ x : ℝ, u * (E 0 - C 0) + v * (E 1 - C 1) = x := ⟨_, rfl⟩
  obtain ⟨e2, he2⟩ : ∃ x : ℝ, -v * (E 0 - C 0) + u * (E 1 - C 1) = x := ⟨_, rfl⟩
  obtain ⟨f1, hf1s⟩ : ∃ x : ℝ, u * (F 0 - C 0) + v * (F 1 - C 1) = x := ⟨_, rfl⟩
  obtain ⟨f2, hf2s⟩ : ∃ x : ℝ, -v * (F 0 - C 0) + u * (F 1 - C 1) = x := ⟨_, rfl⟩
  obtain ⟨g1, hg1s⟩ : ∃ x : ℝ, u * (G 0 - C 0) + v * (G 1 - C 1) = x := ⟨_, rfl⟩
  obtain ⟨g2, hg2s⟩ : ∃ x : ℝ, -v * (G 0 - C 0) + u * (G 1 - C 1) = x := ⟨_, rfl⟩
  obtain ⟨p1, hp1s⟩ : ∃ x : ℝ, u * (P 0 - C 0) + v * (P 1 - C 1) = x := ⟨_, rfl⟩
  obtain ⟨p2, hp2s⟩ : ∃ x : ℝ, -v * (P 0 - C 0) + u * (P 1 - C 1) = x := ⟨_, rfl⟩
  obtain ⟨q1, hq1s⟩ : ∃ x : ℝ, u * (Q 0 - C 0) + v * (Q 1 - C 1) = x := ⟨_, rfl⟩
  obtain ⟨q2, hq2s⟩ : ∃ x : ℝ, -v * (Q 0 - C 0) + u * (Q 1 - C 1) = x := ⟨_, rfl⟩
  obtain ⟨m1, hm1s⟩ : ∃ x : ℝ, u * (M 0 - C 0) + v * (M 1 - C 1) = x := ⟨_, rfl⟩
  obtain ⟨m2, hm2s⟩ : ∃ x : ℝ, -v * (M 0 - C 0) + u * (M 1 - C 1) = x := ⟨_, rfl⟩
  obtain ⟨o1, ho1⟩ : ∃ x : ℝ, u * (sΩ.center 0 - C 0) + v * (sΩ.center 1 - C 1) = x := ⟨_, rfl⟩
  obtain ⟨o2, ho2⟩ : ∃ x : ℝ, -v * (sΩ.center 0 - C 0) + u * (sΩ.center 1 - C 1) = x := ⟨_, rfl⟩
  obtain ⟨o3, ho3⟩ : ∃ x : ℝ, u * (s1.center 0 - C 0) + v * (s1.center 1 - C 1) = x := ⟨_, rfl⟩
  obtain ⟨o4, ho4⟩ : ∃ x : ℝ, -v * (s1.center 0 - C 0) + u * (s1.center 1 - C 1) = x := ⟨_, rfl⟩
  obtain ⟨o5, ho5⟩ : ∃ x : ℝ, u * (s2.center 0 - C 0) + v * (s2.center 1 - C 1) = x := ⟨_, rfl⟩
  obtain ⟨o6, ho6⟩ : ∃ x : ℝ, -v * (s2.center 0 - C 0) + u * (s2.center 1 - C 1) = x := ⟨_, rfl⟩
  -- coordinates of A and C in the new frame
  have hA1 : u * (A 0 - C 0) + v * (A 1 - C 1) = w := by
    rw [← hwd, hu, hv]; ring
  have hA2 : -v * (A 0 - C 0) + u * (A 1 - C 1) = 0 := by
    rw [hu, hv]; ring
  have hC1 : u * (C 0 - C 0) + v * (C 1 - C 1) = 0 := by ring
  have hC2 : -v * (C 0 - C 0) + u * (C 1 - C 1) = 0 := by ring
  -- E lies on the x-axis in the new frame
  have he2E : e2 = 0 := by
    have h1 := xfer_cross_eq C A C E hA1 hA2 hC1 hC2 he he2
    rw [cross_of_mem_line hEline, mul_zero] at h1
    have h2 : w * e2 = 0 := by linear_combination -h1
    rcases mul_eq_zero.mp h2 with h3 | h4
    · exact absurd h3 hw
    · exact h4
  -- transfer of the circle memberships
  have hdAΩ : (A 0 - sΩ.center 0)^2 + (A 1 - sΩ.center 1)^2 = sΩ.radius^2 :=
    dist_sq_eq_of_dist_eq (by rw [dist_comm]; exact EuclideanGeometry.mem_sphere'.mp (hΩ (by simp)))
  have hdBΩ : (B 0 - sΩ.center 0)^2 + (B 1 - sΩ.center 1)^2 = sΩ.radius^2 :=
    dist_sq_eq_of_dist_eq (by rw [dist_comm]; exact EuclideanGeometry.mem_sphere'.mp (hΩ (by simp)))
  have hdCΩ : (C 0 - sΩ.center 0)^2 + (C 1 - sΩ.center 1)^2 = sΩ.radius^2 :=
    dist_sq_eq_of_dist_eq (by rw [dist_comm]; exact EuclideanGeometry.mem_sphere'.mp (hΩ (by simp)))
  have hdDΩ : (D 0 - sΩ.center 0)^2 + (D 1 - sΩ.center 1)^2 = sΩ.radius^2 :=
    dist_sq_eq_of_dist_eq (by rw [dist_comm]; exact EuclideanGeometry.mem_sphere'.mp (hΩ (by simp)))
  have hcA := xfer_sphere C A sΩ.center sΩ.radius hA1 hA2 ho1 ho2 hdAΩ
  have hcB := xfer_sphere C B sΩ.center sΩ.radius hb1 hb2 ho1 ho2 hdBΩ
  have hcC := xfer_sphere C C sΩ.center sΩ.radius hC1 hC2 ho1 ho2 hdCΩ
  have hcD := xfer_sphere C D sΩ.center sΩ.radius hd1 hd2 ho1 ho2 hdDΩ
  have hdA1 : (A 0 - s1.center 0)^2 + (A 1 - s1.center 1)^2 = s1.radius^2 :=
    dist_sq_eq_of_dist_eq (by rw [dist_comm]; exact EuclideanGeometry.mem_sphere'.mp (hs1 (by simp)))
  have hdB1 : (B 0 - s1.center 0)^2 + (B 1 - s1.center 1)^2 = s1.radius^2 :=
    dist_sq_eq_of_dist_eq (by rw [dist_comm]; exact EuclideanGeometry.mem_sphere'.mp (hs1 (by simp)))
  have hdE1 : (E 0 - s1.center 0)^2 + (E 1 - s1.center 1)^2 = s1.radius^2 :=
    dist_sq_eq_of_dist_eq (by rw [dist_comm]; exact EuclideanGeometry.mem_sphere'.mp (hs1 (by simp)))
  have hdP1 : (P 0 - s1.center 0)^2 + (P 1 - s1.center 1)^2 = s1.radius^2 :=
    dist_sq_eq_of_dist_eq (by rw [dist_comm]; exact EuclideanGeometry.mem_sphere'.mp (hs1 (by simp)))
  have h1A := xfer_sphere C A s1.center s1.radius hA1 hA2 ho3 ho4 hdA1
  have h1B := xfer_sphere C B s1.center s1.radius hb1 hb2 ho3 ho4 hdB1
  have h1E := xfer_sphere C E s1.center s1.radius he he2 ho3 ho4 hdE1
  have h1P := xfer_sphere C P s1.center s1.radius hp1s hp2s ho3 ho4 hdP1
  have hdA2 : (A 0 - s2.center 0)^2 + (A 1 - s2.center 1)^2 = s2.radius^2 :=
    dist_sq_eq_of_dist_eq (by rw [dist_comm]; exact EuclideanGeometry.mem_sphere'.mp (hs2 (by simp)))
  have hdD2 : (D 0 - s2.center 0)^2 + (D 1 - s2.center 1)^2 = s2.radius^2 :=
    dist_sq_eq_of_dist_eq (by rw [dist_comm]; exact EuclideanGeometry.mem_sphere'.mp (hs2 (by simp)))
  have hdE2 : (E 0 - s2.center 0)^2 + (E 1 - s2.center 1)^2 = s2.radius^2 :=
    dist_sq_eq_of_dist_eq (by rw [dist_comm]; exact EuclideanGeometry.mem_sphere'.mp (hs2 (by simp)))
  have hdQ2 : (Q 0 - s2.center 0)^2 + (Q 1 - s2.center 1)^2 = s2.radius^2 :=
    dist_sq_eq_of_dist_eq (by rw [dist_comm]; exact EuclideanGeometry.mem_sphere'.mp (hs2 (by simp)))
  have h2A := xfer_sphere C A s2.center s2.radius hA1 hA2 ho5 ho6 hdA2
  have h2D := xfer_sphere C D s2.center s2.radius hd1 hd2 ho5 ho6 hdD2
  have h2E := xfer_sphere C E s2.center s2.radius he he2 ho5 ho6 hdE2
  have h2Q := xfer_sphere C Q s2.center s2.radius hq1s hq2s ho5 ho6 hdQ2
  rw [he2E] at h1E h2E
  -- transfer of collinearity
  have hExfer := xfer_cross_eq C B D E hb1 hb2 hd1 hd2 he he2
  rw [cross_of_mem_line hElineBD, mul_zero, he2E] at hExfer
  have hE' : e * (b2 - d2) = b2 * d1 - b1 * d2 := by linear_combination hExfer
  have hcolBPxfer := xfer_cross_eq C C B P hC1 hC2 hb1 hb2 hp1s hp2s
  rw [cross_of_mem_line hPline, mul_zero] at hcolBPxfer
  have hcolBP : b1 * p2 = b2 * p1 := by linear_combination hcolBPxfer
  have hcolDQxfer := xfer_cross_eq C C D Q hC1 hC2 hd1 hd2 hq1s hq2s
  rw [cross_of_mem_line hQline, mul_zero] at hcolDQxfer
  have hcolDQ : d1 * q2 = d2 * q1 := by linear_combination hcolDQxfer
  have eqF1 := xfer_cross_eq C A B F hA1 hA2 hb1 hb2 hf1s hf2s
  rw [cross_of_mem_line hFAB, mul_zero] at eqF1
  have eqF2xfer := xfer_cross_eq C C D F hC1 hC2 hd1 hd2 hf1s hf2s
  rw [cross_of_mem_line hFline, mul_zero] at eqF2xfer
  have eqF2 : d1 * f2 - d2 * f1 = 0 := by linear_combination eqF2xfer
  have eqG1 := xfer_cross_eq C D A G hd1 hd2 hA1 hA2 hg1s hg2s
  rw [cross_of_mem_line hGDA, mul_zero] at eqG1
  have eqG2xfer := xfer_cross_eq C C B G hC1 hC2 hb1 hb2 hg1s hg2s
  rw [cross_of_mem_line hGline, mul_zero] at eqG2xfer
  have eqG2 : (0 - b1) * (g2 - b2) - (0 - b2) * (g1 - b1) = 0 := by linear_combination -eqG2xfer
  have eqM1 := xfer_cross_eq C F P M hf1s hf2s hp1s hp2s hm1s hm2s
  rw [cross_of_mem_line hMFP, mul_zero] at eqM1
  have eqM2 := xfer_cross_eq C G Q M hg1s hg2s hq1s hq2s hm1s hm2s
  rw [cross_of_mem_line hMGQ, mul_zero] at eqM2
  -- transfer of nonparallelism
  have hdenFx := xfer_cross4_eq C A B C D hA1 hA2 hb1 hb2 hC1 hC2 hd1 hd2
  have hdenF' : (b1 - w) * (d2 - 0) - (b2 - 0) * (d1 - 0) ≠ 0 := by
    rw [hdenFx]; exact mul_ne_zero hu2v2 (cross_ne_zero_of_not_parallel hAB nCD hnpF)
  have hdenF : (b1 - w) * d2 - b2 * d1 ≠ 0 := by
    intro hcontra; apply hdenF'; linear_combination hcontra
  have hdenGx := xfer_cross4_eq C D A B C hd1 hd2 hA1 hA2 hb1 hb2 hC1 hC2
  have hdenG : (w - d1) * (0 - b2) - (0 - d2) * (0 - b1) ≠ 0 := by
    rw [hdenGx]; exact mul_ne_zero hu2v2 (cross_ne_zero_of_not_parallel hAD.symm nCB.symm hnpG)
  have hdetMx := xfer_cross4_eq C F P G Q hf1s hf2s hp1s hp2s hg1s hg2s hq1s hq2s
  have hdetM : (p1 - f1) * (q2 - g2) - (p2 - f2) * (q1 - g1) ≠ 0 := by
    rw [hdetMx]; exact mul_ne_zero hu2v2 (cross_ne_zero_of_not_parallel hFP hGQ hnpM)
  -- nonvanishing norms
  have hBn : b1^2 + b2^2 ≠ 0 := by
    have h1 := xfer_nsq C B hb1 hb2
    rw [h1]
    exact mul_ne_zero hu2v2 (sq_sum_ne_zero_of_ne nCB.symm)
  have hDn : d1^2 + d2^2 ≠ 0 := by
    have h1 := xfer_nsq C D hd1 hd2
    rw [h1]
    exact mul_ne_zero hu2v2 (sq_sum_ne_zero_of_ne nCD.symm)
  have hBP : (b1 - p1)^2 + (b2 - p2)^2 ≠ 0 := by
    have h1 := xfer_sub_nsq C B P hb1 hb2 hp1s hp2s
    rw [h1]
    exact mul_ne_zero hu2v2 (sq_sum_ne_zero_of_ne nBP)
  have hDQ : (d1 - q1)^2 + (d2 - q2)^2 ≠ 0 := by
    have h1 := xfer_sub_nsq C D Q hd1 hd2 hq1s hq2s
    rw [h1]
    exact mul_ne_zero hu2v2 (sq_sum_ne_zero_of_ne nQD.symm)
  have hAE : (w - e)^2 ≠ 0 := by
    have h1 := xfer_sub_nsq C A E hA1 hA2 he he2
    rw [he2E] at h1
    have h3 : (w - e)^2 = (u^2 + v^2) * ((A 0 - E 0)^2 + (A 1 - E 1)^2) := by
      linear_combination h1
    rw [h3]
    exact mul_ne_zero hu2v2 (sq_sum_ne_zero_of_ne hAEn)
  -- B does not lie on line AC (in the new frame, b2 ≠ 0)
  have hb2n : b2 ≠ 0 := by
    intro hb2z
    have h1 := xfer_cross_eq C C A B hC1 hC2 hA1 hA2 hb1 hb2
    rw [hb2z] at h1
    have hc0 : (C 0 - B 0) * (A 1 - B 1) - (C 1 - B 1) * (A 0 - B 0) = 0 := by
      have h2 : (u^2 + v^2) *
          ((A 0 - C 0) * (B 1 - C 1) - (A 1 - C 1) * (B 0 - C 0)) = 0 := by
        linear_combination -h1
      rcases mul_eq_zero.mp h2 with h3 | h4
      · exact absurd h3 hu2v2
      · linear_combination h4
    have hcol : Collinear ℝ ({A, B, C} : Set Pt) := collinear_of_cross hc0
    have hsph : Cospherical ({A, B, C} : Set Pt) := hABCD.1.subset (by simp [Set.insert_subset_iff])
    have hai : AffineIndependent ℝ ![A, B, C] :=
      Cospherical.affineIndependent_of_ne hsph hAB hAC nCB.symm
    exact (affineIndependent_iff_not_collinear_set.mp hai) hcol
  -- D does not lie on line AC (in the new frame, d2 ≠ 0)
  have hd2n : d2 ≠ 0 := by
    intro hd2z
    have h1 := xfer_cross_eq C C A D hC1 hC2 hA1 hA2 hd1 hd2
    rw [hd2z] at h1
    have hc0 : (C 0 - D 0) * (A 1 - D 1) - (C 1 - D 1) * (A 0 - D 0) = 0 := by
      have h2 : (u^2 + v^2) *
          ((A 0 - C 0) * (D 1 - C 1) - (A 1 - C 1) * (D 0 - C 0)) = 0 := by
        linear_combination -h1
      rcases mul_eq_zero.mp h2 with h3 | h4
      · exact absurd h3 hu2v2
      · linear_combination h4
    have hcol : Collinear ℝ ({A, D, C} : Set Pt) := collinear_of_cross hc0
    have hsph : Cospherical ({A, D, C} : Set Pt) := hABCD.1.subset (by simp [Set.insert_subset_iff])
    have hai : AffineIndependent ℝ ![A, D, C] :=
      Cospherical.affineIndependent_of_ne hsph hAD hAC nCD.symm
    exact (affineIndependent_iff_not_collinear_set.mp hai) hcol
  -- B and D are distinct (in the new frame, b2 ≠ d2)
  have hbd : b2 ≠ d2 := by
    intro hbdz
    have hd1b1 : d1 = b1 := by
      have h1 : d2 * (d1 - b1) = 0 := by linear_combination (e - d1) * hbdz - hE'
      rcases mul_eq_zero.mp h1 with h3 | h4
      · exact absurd h3 hd2n
      · linear_combination h4
    have hBD : B = D := by
      have g1 : u * (B 0 - D 0) + v * (B 1 - D 1) = 0 := by
        have h5 : u * (B 0 - D 0) + v * (B 1 - D 1) = b1 - d1 := by
          linear_combination hb1 - hd1
        rw [h5, hd1b1, sub_self]
      have g2 : -v * (B 0 - D 0) + u * (B 1 - D 1) = 0 := by
        have h5 : -v * (B 0 - D 0) + u * (B 1 - D 1) = b2 - d2 := by
          linear_combination hb2 - hd2
        rw [h5, hbdz, sub_self]
      exact eq_of_rot hu2v2 g1 g2
    rw [hBD] at hEBD
    have hEB : E = D := Iff.mp (wbtw_self_iff ℝ) hEBD.wbtw
    exact hEBD.left_ne.symm hEB
  -- the coordinate heart
  have hcore : m1 = w :=
    core hw hBn hDn hbd hcA hcB hcC hcD hE' h1A h1B h1E h1P hAE hBP hcolBP
      h2A h2D h2E h2Q hDQ hcolDQ eqF1 eqF2 hdenF eqG1 eqG2 hdenG eqM1 eqM2 hdetM
  -- conclude perpendicularity
  have hdotx := xfer_dot_eq C M A C A hm1s hm2s hA1 hA2 hC1 hC2 hA1 hA2
  rw [hcore] at hdotx
  have hdot : (M 0 - A 0) * (C 0 - A 0) + (M 1 - A 1) * (C 1 - A 1) = 0 := by
    have h2 : (u^2 + v^2) * ((M 0 - A 0) * (C 0 - A 0) + (M 1 - A 1) * (C 1 - A 1)) = 0 := by
      linear_combination -hdotx
    rcases mul_eq_zero.mp h2 with h3 | h4
    · exact absurd h3 hu2v2
    · exact h4
  rw [EuclideanGeometry.angle, ← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two,
    inner_vsub_eq]
  exact hdot

end Usa2018P5
