/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.Geometry.Euclidean.Triangle
public import Mathlib.Tactic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 1971, Problem 4

All faces of the tetrahedron ABCD are acute-angled. Take a point X in the
interior of the segment AB, and similarly Y in BC, Z in CD and T in AD.

(a) If ∠DAB + ∠BCD ≠ ∠CDA + ∠ABC, prove that none of the closed paths
XYZTX has minimal length.

(b) If ∠DAB + ∠BCD = ∠CDA + ∠ABC, then there are infinitely many shortest
paths XYZTX, each with length 2·AC·sin k, where 2k = ∠BAC + ∠CAD + ∠DAB.
-/

namespace Imo1971P4

open EuclideanGeometry Topology
open scoped EuclideanGeometry Real RealInnerProductSpace

/-- Euclidean 3-space. -/
abbrev Pt := EuclideanSpace ℝ (Fin 3)

/-- The triangle with vertices `X`, `Y`, `Z` is acute-angled:
all three of its angles are less than `π / 2`. -/
def AcuteTriangle (X Y Z : Pt) : Prop :=
  ∠ X Y Z < π / 2 ∧ ∠ Y Z X < π / 2 ∧ ∠ Z X Y < π / 2

/-- The total length `|XY| + |YZ| + |ZT| + |TX|` of the closed path `XYZTX`. -/
noncomputable def pathLength (X Y Z T : Pt) : ℝ :=
  dist X Y + dist Y Z + dist Z T + dist T X

/-- The closed paths considered in the problem: `X` in the interior of the
segment `AB`, `Y` in the interior of `BC`, `Z` in the interior of `CD` and
`T` in the interior of `DA`. -/
def IsPath (A B C D X Y Z T : Pt) : Prop :=
  X ∈ openSegment ℝ A B ∧ Y ∈ openSegment ℝ B C ∧
    Z ∈ openSegment ℝ C D ∧ T ∈ openSegment ℝ D A

/-- The claimed minimal length in part (b): `2 · AC · sin k` with
`2k = ∠BAC + ∠CAD + ∠DAB`. -/
noncomputable def minLength (A B C D : Pt) : ℝ :=
  2 * dist A C * Real.sin ((∠ B A C + ∠ C A D + ∠ D A B) / 2)

snip begin

/-- The Euclidean plane, in which the surface of the tetrahedron is unfolded. -/
abbrev Pt2 := EuclideanSpace ℝ (Fin 2)

/-- The unit vector in the plane with direction angle `θ`. -/
noncomputable def e (θ : ℝ) : Pt2 := !₂[Real.cos θ, Real.sin θ]

lemma e_zero (θ : ℝ) : e θ 0 = Real.cos θ := rfl
lemma e_one (θ : ℝ) : e θ 1 = Real.sin θ := rfl

lemma add_one (x y : Pt2) : (x + y) 1 = (x) 1 + (y) 1 := by simp [PiLp.add_apply]

lemma sub_one (x y : Pt2) : (x - y) 1 = (x) 1 - (y) 1 := by simp [PiLp.sub_apply]

lemma smul_one (r : ℝ) (x : Pt2) : (r • x) 1 = r * (x) 1 := by
  rw [PiLp.smul_apply, smul_eq_mul]

@[simp]
lemma norm_e (θ : ℝ) : ‖e θ‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, e_zero, e_one]
  simp [Real.norm_eq_abs, sq_abs, Real.cos_sq_add_sin_sq]

lemma e_ne_zero (θ : ℝ) : e θ ≠ 0 := by
  have h := norm_e θ
  intro he
  rw [he, norm_zero] at h
  norm_num at h

/-- The inner product of two unit direction vectors is the cosine of the
difference of their direction angles. -/
lemma inner_e_e (θ φ : ℝ) : ⟪e θ, e φ⟫ = Real.cos (θ - φ) := by
  rw [PiLp.inner_apply, Fin.sum_univ_two, e_zero, e_one, e_zero, e_one,
    RCLike.inner_apply, RCLike.inner_apply, RCLike.conj_to_real, RCLike.conj_to_real,
    Real.cos_sub]
  ring

lemma norm_smul_e (r : ℝ) (θ : ℝ) : ‖r • e θ‖ = |r| := by
  rw [norm_smul, norm_e, mul_one, Real.norm_eq_abs]

/-- The squared distance between two points on rays from the origin. -/
lemma dist_sq_smul_e_smul_e (r₁ r₂ : ℝ) (θ₁ θ₂ : ℝ) :
    (dist (r₁ • e θ₁) (r₂ • e θ₂)) ^ 2 =
      r₁ ^ 2 + r₂ ^ 2 - 2 * r₁ * r₂ * Real.cos (θ₁ - θ₂) := by
  rw [dist_eq_norm, ← real_inner_self_eq_norm_sq, real_inner_sub_sub_self,
    real_inner_smul_left, real_inner_smul_right, real_inner_smul_left,
    real_inner_smul_right, real_inner_smul_left, real_inner_smul_right,
    inner_e_e, inner_e_e, inner_e_e,
    show θ₁ - θ₁ = (0 : ℝ) from sub_self θ₁, show θ₂ - θ₂ = (0 : ℝ) from sub_self θ₂,
    Real.cos_zero]
  ring

/-- A vector whose inner product with the unit vector `e θ` equals its norm
is necessarily `r • e θ`. -/
lemma eq_smul_e_of_inner_eq {v : Pt2} {r : ℝ} {θ : ℝ}
    (h₁ : ⟪v, e θ⟫ = r) (h₂ : ‖v‖ = r) : v = r • e θ := by
  have h3 : ⟪v - r • e θ, v - r • e θ⟫ = 0 := by
    rw [real_inner_sub_sub_self, real_inner_smul_right, real_inner_smul_left,
      real_inner_smul_right, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
      norm_e, one_pow, h₁, h₂]
    ring
  rw [inner_self_eq_zero, sub_eq_zero] at h3
  exact h3

/-- Pairs of vertices of a non-degenerate tetrahedron are distinct. -/
lemma tet_ne {A B C D : Pt} (htet : AffineIndependent ℝ ![A, B, C, D])
    {i j : Fin 4} (hij : i ≠ j) : (![A, B, C, D] : Fin 4 → Pt) i ≠ ![A, B, C, D] j :=
  fun he => hij (htet.injective he)

/-! ### The planar net

The surface of the tetrahedron is unfolded into the plane: face `ABC` is
placed with `C` at the origin and `B` on the positive x-axis; face `BCD` is
unfolded about `BC` to the lower half-plane; face `ACD` is unfolded about the
image of `CD`; face `ABD` is unfolded about the image of `AD`. -/

/-- Vertex `C` of the net, placed at the origin. -/
noncomputable def netC0 : Pt2 := 0

/-- Vertex `B` of the net, placed at `(dist B C, 0)`. -/
noncomputable def netB0 (B C : Pt) : Pt2 := dist B C • e 0

/-- Vertex `A` of the net: the image of `A` from face `ABC` (above the x-axis). -/
noncomputable def netA0 (A B C : Pt) : Pt2 := dist A C • e (∠ B C A)

/-- The image of `D` from face `BCD`, unfolded about `BC` (below the x-axis). -/
noncomputable def netD1 (B C D : Pt) : Pt2 := dist C D • e (-(∠ B C D))

/-- The image of `A` from face `ACD`, unfolded about the image of `CD`. -/
noncomputable def netA2 (A B C D : Pt) : Pt2 := dist A C • e (-(∠ B C D + ∠ D C A))

/-- The image of `B` from face `ABD`, unfolded about the image of `AD`. -/
noncomputable def netB3 (A B C D : Pt) : Pt2 :=
  netA2 A B C D + dist A B • e (∠ C D A - ∠ B C D - ∠ D A B)

lemma dist_netC0_netB0 (B C : Pt) : dist netC0 (netB0 B C) = dist B C := by
  rw [netC0, netB0, dist_eq_norm, zero_sub, norm_neg, norm_smul_e,
    abs_of_nonneg dist_nonneg]

lemma dist_netC0_netA0 (A B C : Pt) : dist netC0 (netA0 A B C) = dist A C := by
  rw [netC0, netA0, dist_eq_norm, zero_sub, norm_neg, norm_smul_e,
    abs_of_nonneg dist_nonneg]

lemma dist_netC0_netD1 (B C D : Pt) : dist netC0 (netD1 B C D) = dist C D := by
  rw [netC0, netD1, dist_eq_norm, zero_sub, norm_neg, norm_smul_e,
    abs_of_nonneg dist_nonneg]

lemma dist_netC0_netA2 (A B C D : Pt) : dist netC0 (netA2 A B C D) = dist A C := by
  rw [netC0, netA2, dist_eq_norm, zero_sub, norm_neg, norm_smul_e,
    abs_of_nonneg dist_nonneg]

/-- Squared-distance equality gives distance equality (both sides nonnegative). -/
lemma dist_eq_of_sq_eq {x y : Pt2} {d : ℝ} (hd : 0 ≤ d)
    (h : dist x y ^ 2 = d ^ 2) : dist x y = d :=
  (pow_left_inj₀ dist_nonneg hd (two_ne_zero)).1 h

lemma dist_netA0_netB0 (A B C : Pt) : dist (netA0 A B C) (netB0 B C) = dist A B := by
  apply dist_eq_of_sq_eq dist_nonneg
  have hlc := law_cos A C B
  rw [angle_comm A C B] at hlc
  rw [netA0, netB0, dist_sq_smul_e_smul_e,
    show (∠ B C A) - 0 = ∠ B C A from sub_zero _, pow_two (dist A B)]
  linear_combination -hlc

lemma dist_netB0_netD1 (B C D : Pt) : dist (netB0 B C) (netD1 B C D) = dist B D := by
  apply dist_eq_of_sq_eq dist_nonneg
  have hlc := law_cos B C D
  rw [dist_comm D C] at hlc
  rw [netB0, netD1, dist_sq_smul_e_smul_e,
    show (0 : ℝ) - -(∠ B C D) = ∠ B C D from by ring, pow_two (dist B D)]
  linear_combination -hlc

lemma dist_netD1_netA2 (A B C D : Pt) : dist (netD1 B C D) (netA2 A B C D) = dist D A := by
  apply dist_eq_of_sq_eq dist_nonneg
  have hlc := law_cos D C A
  rw [dist_comm D C] at hlc
  rw [netD1, netA2, dist_sq_smul_e_smul_e,
    show -(∠ B C D) - -(∠ B C D + ∠ D C A) = ∠ D C A from by ring, pow_two (dist D A)]
  linear_combination -hlc

lemma dist_netA2_netB3 (A B C D : Pt) : dist (netA2 A B C D) (netB3 A B C D) = dist A B := by
  rw [netB3, dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul_e,
    abs_of_nonneg dist_nonneg]

lemma netB3_sub_netA2 (A B C D : Pt) :
    netB3 A B C D - netA2 A B C D = dist A B • e (∠ C D A - ∠ B C D - ∠ D A B) := by
  rw [netB3, add_sub_cancel_left]

lemma netA0_def (A B C : Pt) : netA0 A B C = dist A C • e (∠ B C A) := rfl

lemma netB0_sub_netC0 (B C : Pt) : netB0 B C - netC0 = dist B C • e 0 := by
  rw [netC0, netB0, sub_zero]

lemma netD1_sub_netC0 (B C D : Pt) : netD1 B C D - netC0 = dist C D • e (-(∠ B C D)) := by
  rw [netC0, netD1, sub_zero]

lemma netA2_sub_netC0 (A B C D : Pt) :
    netA2 A B C D - netC0 = dist A C • e (-(∠ B C D + ∠ D C A)) := by
  rw [netC0, netA2, sub_zero]

/-- The direction of the image of edge `DA` in the net (the fourth hinge). -/
lemma netA2_sub_netD1 (A B C D : Pt) (htet : AffineIndependent ℝ ![A, B, C, D]) :
    netA2 A B C D - netD1 B C D = dist A D • e (π - ∠ B C D + ∠ C D A) := by
  have hCD : C ≠ D := by have h := tet_ne htet (show (2 : Fin 4) ≠ 3 by decide); simpa using h
  have hAC : A ≠ C := by have h := tet_ne htet (show (0 : Fin 4) ≠ 2 by decide); simpa using h
  have hAD : A ≠ D := by have h := tet_ne htet (show (0 : Fin 4) ≠ 3 by decide); simpa using h
  have hd1 : (0:ℝ) < dist C D := dist_pos.mpr hCD
  have hb : (0:ℝ) < dist A C := dist_pos.mpr hAC
  have he : (0:ℝ) < dist A D := dist_pos.mpr hAD
  -- The law of cosines in face `ACD`, at `C` and at `D`.
  have hlcC := law_cos D C A
  rw [dist_comm D C, dist_comm D A] at hlcC
  have cC : 2 * dist C D * dist A C * Real.cos (∠ D C A) =
      dist C D ^ 2 + dist A C ^ 2 - dist A D ^ 2 := by
    have h := hlcC
    rw [pow_two, pow_two, pow_two] at *
    linear_combination h
  have hlcD := law_cos A D C
  rw [angle_comm A D C] at hlcD
  have cD : 2 * dist A D * dist C D * Real.cos (∠ C D A) =
      dist A D ^ 2 + dist C D ^ 2 - dist A C ^ 2 := by
    have h := hlcD
    rw [pow_two, pow_two, pow_two] at *
    linear_combination h
  -- The law of sines in face `ACD`: `AC · sin(∠DCA) = AD · sin(∠CDA)`.
  have hls1 := law_sin C A D
  have hls2 := law_sin A D C
  rw [angle_comm A D C, dist_comm D C, dist_comm C A] at hls2
  rw [dist_comm D C] at hls1
  have cs' : dist A C * Real.sin (∠ D C A) * dist C D =
      dist A D * Real.sin (∠ C D A) * dist C D := by
    linear_combination (-dist A C * hls1 - dist A D * hls2)
  have cs : dist A C * Real.sin (∠ D C A) = dist A D * Real.sin (∠ C D A) :=
    mul_right_cancel₀ hd1.ne' cs'
  apply eq_smul_e_of_inner_eq
  · rw [netA2, netD1, inner_sub_left, real_inner_smul_left, real_inner_smul_left,
      inner_e_e, inner_e_e,
      show -(∠ B C D + ∠ D C A) - (π - ∠ B C D + ∠ C D A) = -((∠ D C A + ∠ C D A) + π)
        from by ring,
      show -(∠ B C D) - (π - ∠ B C D + ∠ C D A) = -(∠ C D A + π) from by ring,
      Real.cos_neg, Real.cos_neg, Real.cos_add_pi, Real.cos_add_pi, Real.cos_add]
    have p : Real.cos (∠ C D A) ^ 2 + Real.sin (∠ C D A) ^ 2 = 1 :=
      Real.cos_sq_add_sin_sq _
    apply mul_left_cancel₀ (mul_ne_zero two_ne_zero hd1.ne')
    linear_combination (-Real.cos (∠ C D A)) * cC + (2 * dist C D * Real.sin (∠ C D A)) * cs +
      (-Real.cos (∠ C D A)) * cD + (2 * dist C D * dist A D) * p
  · rw [← dist_eq_norm, dist_comm, dist_netD1_netA2, dist_comm]

/-- The consistency of the last unfolded face: the image of `DB` has the
right length. -/
lemma dist_netD1_netB3 (A B C D : Pt) (htet : AffineIndependent ℝ ![A, B, C, D]) :
    dist (netD1 B C D) (netB3 A B C D) = dist D B := by
  apply dist_eq_of_sq_eq dist_nonneg
  have h4 := netA2_sub_netD1 A B C D htet
  have hde : netB3 A B C D - netD1 B C D =
      dist A D • e (π - ∠ B C D + ∠ C D A) + dist A B • e (∠ C D A - ∠ B C D - ∠ D A B) := by
    rw [netB3, add_sub_right_comm, h4]
  have hlc := law_cos D A B
  rw [dist_comm B A, dist_comm D A] at hlc
  rw [dist_eq_norm, show netD1 B C D - netB3 A B C D = -(netB3 A B C D - netD1 B C D)
      from (neg_sub _ _).symm, norm_neg, ← real_inner_self_eq_norm_sq, hde,
    real_inner_add_add_self,
    real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq,
    norm_e, one_pow, real_inner_smul_left, real_inner_smul_right, inner_e_e,
    real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq, norm_e, one_pow,
    show (π - ∠ B C D + ∠ C D A) - (∠ C D A - ∠ B C D - ∠ D A B) = ∠ D A B + π from by ring,
    Real.cos_add_pi, pow_two (dist D B)]
  linear_combination -hlc

/-- The distance between the two images of `A` in the net. -/
lemma dist_netA0_netA2 (A B C D : Pt)
    (hγ : ∠ B C A < π / 2) (hδ : ∠ B C D < π / 2) (hα : ∠ D C A < π / 2) :
    dist (netA0 A B C) (netA2 A B C D) =
      2 * dist A C * Real.sin ((∠ B C A + ∠ B C D + ∠ D C A) / 2) := by
  have hS0 : 0 ≤ ∠ B C A + ∠ B C D + ∠ D C A := by
    have h1 : 0 ≤ ∠ B C A := angle_nonneg _ _ _
    have h2 : 0 ≤ ∠ B C D := angle_nonneg _ _ _
    have h3 : 0 ≤ ∠ D C A := angle_nonneg _ _ _
    linarith
  have hsin : 0 ≤ Real.sin ((∠ B C A + ∠ B C D + ∠ D C A) / 2) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · linarith [hS0]
    · have hpi := Real.pi_pos
      linarith [hγ, hδ, hα, hpi]
  have hd : 0 ≤ 2 * dist A C * Real.sin ((∠ B C A + ∠ B C D + ∠ D C A) / 2) :=
    mul_nonneg (mul_nonneg two_pos.le dist_nonneg) hsin
  apply dist_eq_of_sq_eq hd
  have h1 : (Real.sin ((∠ B C A + ∠ B C D + ∠ D C A) / 2)) ^ 2 =
      (1 - Real.cos (∠ B C A + ∠ B C D + ∠ D C A)) / 2 := by
    have h2 := Real.sin_sq_eq_half_sub ((∠ B C A + ∠ B C D + ∠ D C A) / 2)
    rw [show 2 * ((∠ B C A + ∠ B C D + ∠ D C A) / 2) = ∠ B C A + ∠ B C D + ∠ D C A
      from by ring] at h2
    linarith [h2]
  have h3 : (2 * dist A C * Real.sin ((∠ B C A + ∠ B C D + ∠ D C A) / 2)) ^ 2 =
      2 * dist A C ^ 2 * (1 - Real.cos (∠ B C A + ∠ B C D + ∠ D C A)) := by
    rw [show (2 * dist A C * Real.sin ((∠ B C A + ∠ B C D + ∠ D C A) / 2)) ^ 2 =
      4 * dist A C ^ 2 * (Real.sin ((∠ B C A + ∠ B C D + ∠ D C A) / 2)) ^ 2 from by ring, h1]
    ring
  rw [netA0, netA2, dist_sq_smul_e_smul_e,
    show (∠ B C A) - -(∠ B C D + ∠ D C A) = ∠ B C A + ∠ B C D + ∠ D C A from by ring, h3]
  ring


/-- The direction of the image of edge `AB` in the net (first face). -/
lemma netB0_sub_netA0 (A B C D : Pt) (htet : AffineIndependent ℝ ![A, B, C, D]) :
    netB0 B C - netA0 A B C = dist A B • e (-(∠ A B C)) := by
  have hAB : A ≠ B := by have h := tet_ne htet (show (0 : Fin 4) ≠ 1 by decide); simpa using h
  have hAC : A ≠ C := by have h := tet_ne htet (show (0 : Fin 4) ≠ 2 by decide); simpa using h
  have hBC : B ≠ C := by have h := tet_ne htet (show (1 : Fin 4) ≠ 2 by decide); simpa using h
  have hc : (0:ℝ) < dist A B := dist_pos.mpr hAB
  have hsum : ∠ A B C + ∠ B C A + ∠ C A B = π := angle_add_angle_add_angle_eq_pi C hAB.symm
  have c1 : 2 * dist A B * dist B C * Real.cos (∠ A B C) =
      dist A B ^ 2 + dist B C ^ 2 - dist A C ^ 2 := by
    have h := law_cos A B C
    rw [dist_comm C B, pow_two, pow_two, pow_two] at *
    linear_combination h
  have c2 : 2 * dist A B * dist A C * Real.cos (∠ C A B) =
      dist A B ^ 2 + dist A C ^ 2 - dist B C ^ 2 := by
    have h := law_cos B A C
    rw [angle_comm B A C, dist_comm B A, dist_comm C A, pow_two, pow_two, pow_two] at *
    linear_combination h
  apply eq_smul_e_of_inner_eq
  · rw [netB0, netA0, inner_sub_left, real_inner_smul_left, real_inner_smul_left,
      inner_e_e, inner_e_e,
      show (0 : ℝ) - -(∠ A B C) = ∠ A B C from by ring,
      show (∠ B C A) - -(∠ A B C) = π - ∠ C A B from by linarith [hsum],
      Real.cos_pi_sub]
    apply mul_left_cancel₀ (mul_ne_zero two_ne_zero hc.ne')
    linear_combination (c1 + c2)
  · rw [← dist_eq_norm, dist_comm, dist_netA0_netB0]

/-- The two images of the edge-vector `B - A` in the net coincide iff the
angle condition of part (b) holds. -/
lemma net_edge_vec_eq_iff (A B C D : Pt) (htet : AffineIndependent ℝ ![A, B, C, D])
    (hα : 0 < ∠ D A B) (hβ : 0 < ∠ A B C) (hγ : 0 < ∠ B C D) (hδ : 0 < ∠ C D A)
    (hα2 : ∠ D A B < π / 2) (hβ2 : ∠ A B C < π / 2) (hγ2 : ∠ B C D < π / 2)
    (hδ2 : ∠ C D A < π / 2) :
    netB3 A B C D - netA2 A B C D = netB0 B C - netA0 A B C ↔
      ∠ D A B + ∠ B C D = ∠ C D A + ∠ A B C := by
  have hAB : A ≠ B := by have h := tet_ne htet (show (0 : Fin 4) ≠ 1 by decide); simpa using h
  have hc : (0:ℝ) < dist A B := dist_pos.mpr hAB
  rw [netB3_sub_netA2, netB0_sub_netA0 A B C D htet]
  constructor
  · intro h
    have heq : e (∠ C D A - ∠ B C D - ∠ D A B) = e (-(∠ A B C)) := by
      have h' := congrArg ((dist A B)⁻¹ • ·) h
      rwa [← mul_smul, ← mul_smul, inv_mul_cancel₀ hc.ne', one_smul, one_smul] at h'
    have hc1 : Real.cos (∠ C D A - ∠ B C D - ∠ D A B) = Real.cos (∠ A B C) := by
      have h2 := congrArg (fun v => v 0) heq
      rwa [e_zero, e_zero, Real.cos_neg] at h2
    have hs1 : Real.sin (∠ C D A - ∠ B C D - ∠ D A B) = -Real.sin (∠ A B C) := by
      have h2 := congrArg (fun v => v 1) heq
      rwa [e_one, e_one, Real.sin_neg] at h2
    have hsum : Real.cos ((∠ C D A - ∠ B C D - ∠ D A B) + ∠ A B C) = 1 := by
      rw [Real.cos_add, hc1, hs1]
      linarith [Real.cos_sq_add_sin_sq (∠ A B C)]
    obtain ⟨k, hk⟩ := (Real.cos_eq_one_iff _).1 hsum
    have hbnd : -π < (∠ C D A - ∠ B C D - ∠ D A B) + ∠ A B C ∧
        (∠ C D A - ∠ B C D - ∠ D A B) + ∠ A B C < π := by
      have hpi := Real.pi_pos
      constructor <;> linarith [hα, hβ, hγ, hδ, hα2, hβ2, hγ2, hδ2, hpi]
    have hk0 : k = 0 := by
      by_contra hkne
      have h1 : (1:ℝ) ≤ |(k : ℝ)| := by
        have h2 : (1:ℤ) ≤ |k| := Int.one_le_abs hkne
        have h3 : ((1:ℤ) : ℝ) ≤ (↑|k| : ℝ) := by exact_mod_cast h2
        rwa [Int.cast_one, Int.cast_abs] at h3
      have h2 : (2 * π) ≤ |(k : ℝ) * (2 * π)| := by
        rw [abs_mul, abs_of_pos (mul_pos two_pos Real.pi_pos)]
        calc (2:ℝ) * π = 1 * (2 * π) := by ring
          _ ≤ |(k : ℝ)| * (2 * π) :=
            mul_le_mul_of_nonneg_right h1 (mul_nonneg two_pos.le Real.pi_pos.le)
      rw [hk] at h2
      have h3 : |(∠ C D A - ∠ B C D - ∠ D A B) + ∠ A B C| < π := abs_lt.mpr hbnd
      linarith [h2, h3, Real.pi_pos]
    rw [hk0] at hk
    simp at hk
    linarith [hk]
  · intro h
    have h2 : ∠ C D A - ∠ B C D - ∠ D A B = -(∠ A B C) := by linarith [h]
    rw [h2]

/-
Proof strategy (classical, after Kalva's notes): unfold the surface of the
tetrahedron into the plane: keep face `ABC` fixed, unfold face `BCD` about
`BC`, then face `ACD` about the image of `CD`, then face `ABD` about the
image of `AD`, producing a planar hexagonal net.  The closed path `XYZTX`
becomes a polygonal path in the plane, from the image of `X` on
one copy of edge `AB` to the image of `X` on the other copy, with the same
total length.  Its length is therefore at least the straight-line distance
between those two images, with equality iff the unfolded path is straight.

The two images of edge `AB` in the net are parallel iff
`∠BCD + ∠DCA + ∠CAD + ∠DAB + ∠BAC + ∠ACB = 360°`, which (using the angle sums
in triangles `ACD` and `ABC`) is equivalent to
`∠DAB + ∠BCD = ∠CDA + ∠ABC`.  If they are not parallel, the infimum of the
path length is attained only in a limiting position where one of `X, Y, Z, T`
leaves the interior of its edge, so no admissible path is minimal.  If they
are parallel, every straight transversal gives a shortest path; the common
length is the distance between the two parallel lines, which computes to
`2 · AC · sin k`, `2k = ∠BAC + ∠CAD + ∠DAB`.  The acuteness of all faces
guarantees that these straight transversals indeed cross all four edges in
their interiors.
-/

/-- Equality of real numbers from equality of their squares (nonneg). -/
lemma eq_of_sq_eq_sq {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x ^ 2 = y ^ 2) : x = y :=
  (pow_left_inj₀ hx hy (two_ne_zero)).1 h

/-- Angles between positively rescaled vectors. -/
lemma angle_smul_smul {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (u v : V) {r₁ r₂ : ℝ} (h1 : 0 < r₁) (h2 : 0 < r₂) :
    InnerProductGeometry.angle (r₁ • u) (r₂ • v) = InnerProductGeometry.angle u v := by
  rw [InnerProductGeometry.angle_smul_right_of_pos _ _ h2,
    InnerProductGeometry.angle_smul_left_of_pos _ _ h1]

/-- The SSS congruence for angles: triangles with equal side lengths have
equal angles. -/
lemma angle_eq_of_three_dist_eq {V₁ V₂ : Type*} [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁]
    [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂]
    {a b c : V₁} {a' b' c' : V₂}
    (hab : dist a b ≠ 0) (hbc : dist b c ≠ 0)
    (h1 : dist a b = dist a' b') (h2 : dist b c = dist b' c') (h3 : dist a c = dist a' c') :
    ∠ a b c = ∠ a' b' c' := by
  have h1' := law_cos a b c
  have h2' := law_cos a' b' c'
  rw [dist_comm c b, h1, h2, h3] at h1'
  rw [dist_comm c' b'] at h2'
  have hb' : dist a' b' ≠ 0 := h1 ▸ hab
  have hbc' : dist b' c' ≠ 0 := h2 ▸ hbc
  have hcos : Real.cos (∠ a b c) = Real.cos (∠ a' b' c') := by
    have key : 2 * dist a' b' * dist b' c' * Real.cos (∠ a b c) =
        2 * dist a' b' * dist b' c' * Real.cos (∠ a' b' c') := by
      linear_combination h1' - h2'
    exact mul_left_cancel₀ (mul_ne_zero (mul_ne_zero two_ne_zero hb') hbc') key
  exact Real.injOn_cos ⟨angle_nonneg _ _ _, angle_le_pi _ _ _⟩
    ⟨angle_nonneg _ _ _, angle_le_pi _ _ _⟩ hcos

/-- Matching two law-of-cosines computations. -/
lemma dist_eq_of_law_cos_match {P M₁ M₂ : Pt} {p m₁ m₂ : Pt2}
    (hang : ∠ M₁ P M₂ = ∠ m₁ p m₂)
    (h1 : dist P M₁ = dist p m₁) (h2 : dist P M₂ = dist p m₂) :
    dist m₁ m₂ = dist M₁ M₂ := by
  have h1' := law_cos M₁ P M₂
  have h2' := law_cos m₁ p m₂
  rw [dist_comm M₁ P, dist_comm M₂ P, hang, h1, h2] at h1'
  rw [dist_comm m₁ p, dist_comm m₂ p] at h2'
  have hsq : dist M₁ M₂ * dist M₁ M₂ = dist m₁ m₂ * dist m₁ m₂ := by
    rw [h1', ← h2']
  exact (eq_of_sq_eq_sq dist_nonneg dist_nonneg (by rw [pow_two, pow_two]; exact hsq)).symm

/-- The distance from an apex to a rescaled point in the net. -/
lemma dist_apex_img (p u : Pt2) (α : ℝ) (hα : 0 < α) :
    dist (p + α • (u - p)) p = α * dist p u := by
  rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hα,
    ← dist_eq_norm, dist_comm]

/-- The distance from an apex to a rescaled point on an edge of the tetrahedron. -/
lemma dist_apex_orig (P U M : Pt) (α : ℝ) (hα : 0 < α) (hM : M - P = α • (U - P)) :
    dist P M = α * dist P U := by
  rw [dist_eq_norm, norm_sub_rev, hM, norm_smul, Real.norm_eq_abs, abs_of_pos hα,
    ← dist_eq_norm, dist_comm]

/-- Generic distance correspondence for points on two edges from a common apex:
the planar net images preserve distances to the apex and to each other. -/
lemma dist_edge_point_img (P U₁ U₂ : Pt) (p u₁ u₂ : Pt2)
    (hd : dist u₁ u₂ = dist U₁ U₂) (hd1 : dist p u₁ = dist P U₁) (hd2 : dist p u₂ = dist P U₂)
    (hp1 : dist P U₁ ≠ 0) (hp2 : dist P U₂ ≠ 0)
    {α₁ α₂ : ℝ} (hα1 : 0 < α₁) (hα2 : 0 < α₂)
    (M₁ M₂ : Pt) (hM1 : M₁ - P = α₁ • (U₁ - P)) (hM2 : M₂ - P = α₂ • (U₂ - P)) :
    dist (p + α₁ • (u₁ - p)) (p + α₂ • (u₂ - p)) = dist M₁ M₂ := by
  have hang3 : InnerProductGeometry.angle (U₁ - P) (U₂ - P) =
      InnerProductGeometry.angle (u₁ - p) (u₂ - p) := by
    have hp1n : dist U₁ P ≠ 0 := by rwa [dist_comm]
    have e1 : dist U₁ P = dist u₁ p := by rw [dist_comm, hd1.symm, dist_comm]
    exact angle_eq_of_three_dist_eq (V₁ := Pt) (V₂ := Pt2) hp1n hp2 e1 hd2.symm hd.symm
  have hang : ∠ M₁ P M₂ = ∠ (p + α₁ • (u₁ - p)) p (p + α₂ • (u₂ - p)) := by
    have e1 : ∠ M₁ P M₂ = InnerProductGeometry.angle (U₁ - P) (U₂ - P) := by
      show InnerProductGeometry.angle (M₁ -ᵥ P) (M₂ -ᵥ P) = _
      rw [vsub_eq_sub, vsub_eq_sub, hM1, hM2, angle_smul_smul _ _ hα1 hα2]
    have e2 : ∠ (p + α₁ • (u₁ - p)) p (p + α₂ • (u₂ - p)) =
        InnerProductGeometry.angle (u₁ - p) (u₂ - p) := by
      show InnerProductGeometry.angle ((p + α₁ • (u₁ - p)) -ᵥ p) ((p + α₂ • (u₂ - p)) -ᵥ p) = _
      rw [vsub_eq_sub, vsub_eq_sub, add_sub_cancel_left, add_sub_cancel_left,
        angle_smul_smul _ _ hα1 hα2]
    rw [e1, e2, hang3]
  apply dist_eq_of_law_cos_match hang
  · rw [dist_apex_orig P U₁ M₁ α₁ hα1 hM1, dist_comm p (p + α₁ • (u₁ - p)),
      dist_apex_img p u₁ α₁ hα1, hd1]
  · rw [dist_apex_orig P U₂ M₂ α₂ hα2 hM2, dist_comm p (p + α₂ • (u₂ - p)),
      dist_apex_img p u₂ α₂ hα2, hd2]

/-- The image in the net of a point `X` on edge `AB` (in face `ABC`). -/
noncomputable def imgX (A B C : Pt) (t : ℝ) : Pt2 := netB0 B C + t • (netA0 A B C - netB0 B C)

/-- The image in the net of a point `Y` on edge `BC`. -/
noncomputable def imgY (B C : Pt) (t : ℝ) : Pt2 := netC0 + t • (netB0 B C - netC0)

/-- The image in the net of a point `Z` on edge `CD`. -/
noncomputable def imgZ (B C D : Pt) (t : ℝ) : Pt2 := netD1 B C D + t • (netC0 - netD1 B C D)

/-- The image in the net of a point `T` on edge `DA`. -/
noncomputable def imgT (A B C D : Pt) (t : ℝ) : Pt2 :=
  netA2 A B C D + t • (netD1 B C D - netA2 A B C D)

/-- The second image of a point `X` on edge `AB` (in unfolded face `ABD`). -/
noncomputable def imgX3 (A B C D : Pt) (t : ℝ) : Pt2 :=
  netA2 A B C D + t • (netB3 A B C D - netA2 A B C D)

/-- `dist X Y` equals the distance of the net images, for `X` on `AB`, `Y` on `BC`. -/
lemma dist_imgX_imgY (A B C D : Pt) (htet : AffineIndependent ℝ ![A, B, C, D])
    {X Y : Pt} {x1 x2 y1 y2 : ℝ}
    (hx1 : 0 < x1) (hx2 : 0 < x2) (hx12 : x1 + x2 = 1) (hXe : x1 • A + x2 • B = X)
    (hy1 : 0 < y1) (hy2 : 0 < y2) (hy12 : y1 + y2 = 1) (hYe : y1 • B + y2 • C = Y) :
    dist (imgX A B C x1) (imgY B C y1) = dist X Y := by
  have hAB : A ≠ B := by have h := tet_ne htet (show (0 : Fin 4) ≠ 1 by decide); simpa using h
  have hBC : B ≠ C := by have h := tet_ne htet (show (1 : Fin 4) ≠ 2 by decide); simpa using h
  have hx2' : x2 = 1 - x1 := by linarith [hx12]
  have hy2' : y2 = 1 - y1 := by linarith [hy12]
  have hM1 : X - B = x1 • (A - B) := by rw [← hXe, hx2']; module
  have hM2 : Y - B = y2 • (C - B) := by rw [← hYe, hy2']; module
  have himg2 : imgY B C y1 = netB0 B C + y2 • (netC0 - netB0 B C) := by
    rw [imgY, hy2']; module
  rw [himg2]
  have hd1 : dist (netB0 B C) (netA0 A B C) = dist B A := by
    rw [dist_comm, dist_netA0_netB0, dist_comm]
  have hd2 : dist (netB0 B C) netC0 = dist B C := by rw [dist_comm, dist_netC0_netB0]
  have hd : dist (netA0 A B C) netC0 = dist A C := by rw [dist_comm, dist_netC0_netA0]
  exact dist_edge_point_img B A C (netB0 B C) (netA0 A B C) netC0 hd hd1 hd2
    (dist_ne_zero.mpr hAB.symm) (dist_ne_zero.mpr hBC) hx1 hy2 X Y hM1 hM2

/-- `dist Y Z` equals the distance of the net images, for `Y` on `BC`, `Z` on `CD`. -/
lemma dist_imgY_imgZ (A B C D : Pt) (htet : AffineIndependent ℝ ![A, B, C, D])
    {Y Z : Pt} {y1 y2 z1 z2 : ℝ}
    (hy1 : 0 < y1) (hy2 : 0 < y2) (hy12 : y1 + y2 = 1) (hYe : y1 • B + y2 • C = Y)
    (hz1 : 0 < z1) (hz2 : 0 < z2) (hz12 : z1 + z2 = 1) (hZe : z1 • C + z2 • D = Z) :
    dist (imgY B C y1) (imgZ B C D z1) = dist Y Z := by
  have hBC : B ≠ C := by have h := tet_ne htet (show (1 : Fin 4) ≠ 2 by decide); simpa using h
  have hCD : C ≠ D := by have h := tet_ne htet (show (2 : Fin 4) ≠ 3 by decide); simpa using h
  have hy2' : y2 = 1 - y1 := by linarith [hy12]
  have hz2' : z2 = 1 - z1 := by linarith [hz12]
  have hM1 : Y - C = y1 • (B - C) := by rw [← hYe, hy2']; module
  have hM2 : Z - C = z2 • (D - C) := by rw [← hZe, hz2']; module
  have himg2 : imgZ B C D z1 = netC0 + z2 • (netD1 B C D - netC0) := by
    rw [imgZ, hz2']; module
  rw [himg2]
  have hd1 : dist netC0 (netB0 B C) = dist C B := by rw [dist_netC0_netB0, dist_comm]
  have hd2 : dist netC0 (netD1 B C D) = dist C D := dist_netC0_netD1 _ _ _
  have hd : dist (netB0 B C) (netD1 B C D) = dist B D := dist_netB0_netD1 _ _ _
  exact dist_edge_point_img C B D netC0 (netB0 B C) (netD1 B C D) hd hd1 hd2
    (dist_ne_zero.mpr hBC.symm) (dist_ne_zero.mpr hCD) hy1 hz2 Y Z hM1 hM2

/-- `dist Z T` equals the distance of the net images, for `Z` on `CD`, `T` on `DA`. -/
lemma dist_imgZ_imgT (A B C D : Pt) (htet : AffineIndependent ℝ ![A, B, C, D])
    {Z T : Pt} {z1 z2 t1 t2 : ℝ}
    (hz1 : 0 < z1) (hz2 : 0 < z2) (hz12 : z1 + z2 = 1) (hZe : z1 • C + z2 • D = Z)
    (ht1 : 0 < t1) (ht2 : 0 < t2) (ht12 : t1 + t2 = 1) (hTe : t1 • D + t2 • A = T) :
    dist (imgZ B C D z1) (imgT A B C D t1) = dist Z T := by
  have hCD : C ≠ D := by have h := tet_ne htet (show (2 : Fin 4) ≠ 3 by decide); simpa using h
  have hAD : A ≠ D := by have h := tet_ne htet (show (0 : Fin 4) ≠ 3 by decide); simpa using h
  have hz2' : z2 = 1 - z1 := by linarith [hz12]
  have ht2' : t2 = 1 - t1 := by linarith [ht12]
  have hM1 : Z - D = z1 • (C - D) := by rw [← hZe, hz2']; module
  have hM2 : T - D = t2 • (A - D) := by rw [← hTe, ht2']; module
  have himg2 : imgT A B C D t1 = netD1 B C D + t2 • (netA2 A B C D - netD1 B C D) := by
    rw [imgT, ht2']; module
  rw [himg2]
  have hd1 : dist (netD1 B C D) netC0 = dist D C := by rw [dist_comm, dist_netC0_netD1, dist_comm]
  have hd2 : dist (netD1 B C D) (netA2 A B C D) = dist D A := dist_netD1_netA2 _ _ _ _
  have hd : dist netC0 (netA2 A B C D) = dist C A := by rw [dist_netC0_netA2, dist_comm]
  exact dist_edge_point_img D C A (netD1 B C D) netC0 (netA2 A B C D) hd hd1 hd2
    (dist_ne_zero.mpr hCD.symm) (dist_ne_zero.mpr hAD.symm) hz1 ht2 Z T hM1 hM2

/-- `dist T X` equals the distance of the net images, for `T` on `DA`, `X` on `AB`. -/
lemma dist_imgT_imgX3 (A B C D : Pt) (htet : AffineIndependent ℝ ![A, B, C, D])
    {T X : Pt} {t1 t2 x1 x2 : ℝ}
    (ht1 : 0 < t1) (ht2 : 0 < t2) (ht12 : t1 + t2 = 1) (hTe : t1 • D + t2 • A = T)
    (hx1 : 0 < x1) (hx2 : 0 < x2) (hx12 : x1 + x2 = 1) (hXe : x1 • A + x2 • B = X) :
    dist (imgT A B C D t1) (imgX3 A B C D x2) = dist T X := by
  have hAD : A ≠ D := by have h := tet_ne htet (show (0 : Fin 4) ≠ 3 by decide); simpa using h
  have hAB : A ≠ B := by have h := tet_ne htet (show (0 : Fin 4) ≠ 1 by decide); simpa using h
  have ht2' : t2 = 1 - t1 := by linarith [ht12]
  have hx2' : x2 = 1 - x1 := by linarith [hx12]
  have hM1 : T - A = t1 • (D - A) := by rw [← hTe, ht2']; module
  have hM2 : X - A = x2 • (B - A) := by rw [← hXe, hx2']; module
  have hd1 : dist (netA2 A B C D) (netD1 B C D) = dist A D := by
    rw [dist_comm, dist_netD1_netA2, dist_comm]
  have hd2 : dist (netA2 A B C D) (netB3 A B C D) = dist A B := dist_netA2_netB3 _ _ _ _
  have hd : dist (netD1 B C D) (netB3 A B C D) = dist D B := dist_netD1_netB3 _ _ _ _ htet
  exact dist_edge_point_img A D B (netA2 A B C D) (netD1 B C D) (netB3 A B C D) hd hd1 hd2
    (dist_ne_zero.mpr hAD) (dist_ne_zero.mpr hAB) ht1 hx2 T X hM1 hM2

/-- The unfolded polygonal chain has the same length as the closed path, and is
therefore at least the distance between the two images of `X`. -/
lemma pathLength_ge_dist_imgX_imgX3 (A B C D : Pt) (htet : AffineIndependent ℝ ![A, B, C, D])
    {X Y Z T : Pt} {x1 x2 y1 y2 z1 z2 t1 t2 : ℝ}
    (hx1 : 0 < x1) (hx2 : 0 < x2) (hx12 : x1 + x2 = 1) (hXe : x1 • A + x2 • B = X)
    (hy1 : 0 < y1) (hy2 : 0 < y2) (hy12 : y1 + y2 = 1) (hYe : y1 • B + y2 • C = Y)
    (hz1 : 0 < z1) (hz2 : 0 < z2) (hz12 : z1 + z2 = 1) (hZe : z1 • C + z2 • D = Z)
    (ht1 : 0 < t1) (ht2 : 0 < t2) (ht12 : t1 + t2 = 1) (hTe : t1 • D + t2 • A = T) :
    dist (imgX A B C x1) (imgX3 A B C D x2) ≤ pathLength X Y Z T := by
  have h1 := dist_imgX_imgY A B C D htet hx1 hx2 hx12 hXe hy1 hy2 hy12 hYe
  have h2 := dist_imgY_imgZ A B C D htet hy1 hy2 hy12 hYe hz1 hz2 hz12 hZe
  have h3 := dist_imgZ_imgT A B C D htet hz1 hz2 hz12 hZe ht1 ht2 ht12 hTe
  have h4 := dist_imgT_imgX3 A B C D htet ht1 ht2 ht12 hTe hx1 hx2 hx12 hXe
  rw [pathLength, ← h1, ← h2, ← h3, ← h4]
  calc dist (imgX A B C x1) (imgX3 A B C D x2)
      ≤ dist (imgX A B C x1) (imgZ B C D z1) + dist (imgZ B C D z1) (imgX3 A B C D x2) :=
        dist_triangle _ _ _
    _ ≤ (dist (imgX A B C x1) (imgY B C y1) + dist (imgY B C y1) (imgZ B C D z1)) +
          dist (imgZ B C D z1) (imgX3 A B C D x2) := by
        gcongr; exact dist_triangle _ _ _
    _ ≤ (dist (imgX A B C x1) (imgY B C y1) + dist (imgY B C y1) (imgZ B C D z1)) +
          (dist (imgZ B C D z1) (imgT A B C D t1) + dist (imgT A B C D t1) (imgX3 A B C D x2)) := by
        gcongr; exact dist_triangle _ _ _
    _ = dist (imgX A B C x1) (imgY B C y1) + dist (imgY B C y1) (imgZ B C D z1) +
          dist (imgZ B C D z1) (imgT A B C D t1) + dist (imgT A B C D t1) (imgX3 A B C D x2) := by
        ring

/-- Three vertices of a non-degenerate tetrahedron are not collinear. -/
lemma tet_not_collinear (A B C D : Pt) (htet : AffineIndependent ℝ ![A, B, C, D])
    (i j k : Fin 4) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ¬ Collinear ℝ ({((![A, B, C, D] : Fin 4 → Pt) i), ((![A, B, C, D] : Fin 4 → Pt) j),
      ((![A, B, C, D] : Fin 4 → Pt) k)} : Set Pt) := by
  have h3 : AffineIndependent ℝ ((![A, B, C, D] : Fin 4 → Pt) ∘ ![i, j, k]) :=
    AffineIndependent.comp_embedding ⟨![i, j, k], by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all⟩ htet
  have hnc := (affineIndependent_iff_not_collinear_of_ne
    (p := (![A, B, C, D] : Fin 4 → Pt) ∘ ![i, j, k])
    (by decide : (0 : Fin 3) ≠ 1) (by decide : (0 : Fin 3) ≠ 2)
    (by decide : (1 : Fin 3) ≠ 2)).mp h3
  have hset : ({((![A, B, C, D] : Fin 4 → Pt) ∘ ![i, j, k]) 0,
      ((![A, B, C, D] : Fin 4 → Pt) ∘ ![i, j, k]) 1,
      ((![A, B, C, D] : Fin 4 → Pt) ∘ ![i, j, k]) 2} : Set Pt) =
      {((![A, B, C, D] : Fin 4 → Pt) i), ((![A, B, C, D] : Fin 4 → Pt) j),
        ((![A, B, C, D] : Fin 4 → Pt) k)} := by
    simp [Function.comp_apply]
  rwa [hset] at hnc

/-- Face angles of a non-degenerate tetrahedron are positive. -/
lemma angle_pos_of_tet (A B C D : Pt) (htet : AffineIndependent ℝ ![A, B, C, D])
    (i j k : Fin 4) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    0 < ∠ ((![A, B, C, D] : Fin 4 → Pt) i) ((![A, B, C, D] : Fin 4 → Pt) j)
      ((![A, B, C, D] : Fin 4 → Pt) k) :=
  angle_pos_of_not_collinear (tet_not_collinear A B C D htet i j k hij hik hjk)

/-- Face angles of a non-degenerate tetrahedron are less than `π`. -/
lemma angle_lt_pi_of_tet (A B C D : Pt) (htet : AffineIndependent ℝ ![A, B, C, D])
    (i j k : Fin 4) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∠ ((![A, B, C, D] : Fin 4 → Pt) i) ((![A, B, C, D] : Fin 4 → Pt) j)
      ((![A, B, C, D] : Fin 4 → Pt) k) < π :=
  angle_lt_pi_of_not_collinear (tet_not_collinear A B C D htet i j k hij hik hjk)

/-- The sine of a face angle of a non-degenerate tetrahedron is positive. -/
lemma sin_pos_of_tet (A B C D : Pt) (htet : AffineIndependent ℝ ![A, B, C, D])
    (i j k : Fin 4) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    0 < Real.sin (∠ ((![A, B, C, D] : Fin 4 → Pt) i) ((![A, B, C, D] : Fin 4 → Pt) j)
      ((![A, B, C, D] : Fin 4 → Pt) k)) :=
  Real.sin_pos_of_pos_of_lt_pi (angle_pos_of_tet A B C D htet i j k hij hik hjk)
    (angle_lt_pi_of_tet A B C D htet i j k hij hik hjk)

/-- The sum of two face angles of a non-degenerate tetrahedron has positive sine. -/
lemma sin_sum_pos_of_tet (A B C D : Pt) (htet : AffineIndependent ℝ ![A, B, C, D])
    (i j k : Fin 4) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (i' j' k' : Fin 4) (hij' : i' ≠ j') (hik' : i' ≠ k') (hjk' : j' ≠ k')
    (hsum : ∠ ((![A, B, C, D] : Fin 4 → Pt) i) ((![A, B, C, D] : Fin 4 → Pt) j)
        ((![A, B, C, D] : Fin 4 → Pt) k) +
      ∠ ((![A, B, C, D] : Fin 4 → Pt) i') ((![A, B, C, D] : Fin 4 → Pt) j')
        ((![A, B, C, D] : Fin 4 → Pt) k') < π) :
    0 < Real.sin (∠ ((![A, B, C, D] : Fin 4 → Pt) i) ((![A, B, C, D] : Fin 4 → Pt) j)
        ((![A, B, C, D] : Fin 4 → Pt) k) +
      ∠ ((![A, B, C, D] : Fin 4 → Pt) i') ((![A, B, C, D] : Fin 4 → Pt) j')
        ((![A, B, C, D] : Fin 4 → Pt) k')) := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · have h1 := by simpa using angle_pos_of_tet A B C D htet i j k hij hik hjk
    have h2 := by simpa using angle_pos_of_tet A B C D htet i' j' k' hij' hik' hjk'
    linarith
  · exact hsum

/-- The angle sums in faces `ABC` and `ACD`. -/
lemma face_angle_sums (A B C D : Pt) (htet : AffineIndependent ℝ ![A, B, C, D]) :
    (∠ A B C + ∠ B C A + ∠ C A B = π) ∧ (∠ A C D + ∠ C D A + ∠ D A C = π) := by
  have hAB : A ≠ B := by have h := tet_ne htet (show (0 : Fin 4) ≠ 1 by decide); simpa using h
  have hAC : A ≠ C := by have h := tet_ne htet (show (0 : Fin 4) ≠ 2 by decide); simpa using h
  exact ⟨angle_add_angle_add_angle_eq_pi C hAB.symm,
    angle_add_angle_add_angle_eq_pi D hAC.symm⟩

/-- Under the angle condition of part (b), the two images of any point `X` on
edge `AB` are at the constant distance `dist netA0 netA2` apart. -/
lemma dist_imgX_imgX3_of_condition (A B C D : Pt) (htet : AffineIndependent ℝ ![A, B, C, D])
    (hcond : ∠ D A B + ∠ B C D = ∠ C D A + ∠ A B C)
    (hα : 0 < ∠ D A B) (hβ : 0 < ∠ A B C) (hγ : 0 < ∠ B C D) (hδ : 0 < ∠ C D A)
    (hα2 : ∠ D A B < π / 2) (hβ2 : ∠ A B C < π / 2) (hγ2 : ∠ B C D < π / 2)
    (hδ2 : ∠ C D A < π / 2)
    {x1 x2 : ℝ} (hx12 : x1 + x2 = 1) :
    dist (imgX A B C x1) (imgX3 A B C D x2) = dist (netA0 A B C) (netA2 A B C D) := by
  have hpar : netB3 A B C D - netA2 A B C D = netB0 B C - netA0 A B C :=
    (net_edge_vec_eq_iff A B C D htet hα hβ hγ hδ hα2 hβ2 hγ2 hδ2).2 hcond
  have hx2' : x2 = 1 - x1 := by linarith [hx12]
  have himg1 : imgX A B C x1 = netA0 A B C + x2 • (netB0 B C - netA0 A B C) := by
    rw [imgX, hx2']; module
  rw [himg1, imgX3, hpar, dist_eq_norm, dist_eq_norm]
  congr 1
  module

/-- Under the angle condition, the claimed minimal length equals the distance
between the two images of `A` in the net. -/
lemma minLength_eq_dist_netA0_netA2 (A B C D : Pt) (htet : AffineIndependent ℝ ![A, B, C, D])
    (hcond : ∠ D A B + ∠ B C D = ∠ C D A + ∠ A B C)
    (hγ : ∠ B C A < π / 2) (hδ : ∠ B C D < π / 2) (hα : ∠ D C A < π / 2) :
    minLength A B C D = dist (netA0 A B C) (netA2 A B C D) := by
  obtain ⟨hs1, hs2⟩ := face_angle_sums A B C D htet
  rw [minLength, dist_netA0_netA2 A B C D hγ hδ hα]
  congr 1
  have h1 : ∠ C A B = ∠ B A C := angle_comm _ _ _
  have h2 : ∠ D A C = ∠ C A D := angle_comm _ _ _
  have h3 : ∠ A C D = ∠ D C A := angle_comm _ _ _
  have hS : (∠ B A C + ∠ C A D + ∠ D A B) + (∠ B C A + ∠ B C D + ∠ D C A) = 2 * π := by
    linarith [hcond, hs1, hs2, h1, h2, h3]
  have h4 : (∠ B A C + ∠ C A D + ∠ D A B) / 2 = π - (∠ B C A + ∠ B C D + ∠ D C A) / 2 := by
    linarith [hS]
  rw [h4, Real.sin_pi_sub]

/-- Part (b), lower bound: under the angle condition, every admissible path
has length at least `2 · AC · sin k`. -/
lemma minLength_le_pathLength_of_condition (A B C D : Pt)
    (htet : AffineIndependent ℝ ![A, B, C, D])
    (hABC : AcuteTriangle A B C) (hBCD : AcuteTriangle B C D)
    (hACD : AcuteTriangle A C D) (hABD : AcuteTriangle A B D)
    (hcond : ∠ D A B + ∠ B C D = ∠ C D A + ∠ A B C)
    {X Y Z T : Pt} (hp : IsPath A B C D X Y Z T) :
    minLength A B C D ≤ pathLength X Y Z T := by
  have hα : 0 < ∠ D A B := by simpa using angle_pos_of_tet A B C D htet 3 0 1 (by decide) (by decide) (by decide)
  have hβ : 0 < ∠ A B C := by simpa using angle_pos_of_tet A B C D htet 0 1 2 (by decide) (by decide) (by decide)
  have hγ : 0 < ∠ B C D := by simpa using angle_pos_of_tet A B C D htet 1 2 3 (by decide) (by decide) (by decide)
  have hδ : 0 < ∠ C D A := by simpa using angle_pos_of_tet A B C D htet 2 3 0 (by decide) (by decide) (by decide)
  have hα2 : ∠ D A B < π / 2 := hABD.2.2
  have hβ2 : ∠ A B C < π / 2 := hABC.1
  have hγ2 : ∠ B C D < π / 2 := hBCD.1
  have hδ2 : ∠ C D A < π / 2 := hACD.2.1
  have hγ2' : ∠ B C A < π / 2 := hABC.2.1
  have hα2' : ∠ D C A < π / 2 := by rw [angle_comm D C A]; exact hACD.1
  obtain ⟨⟨x1, x2⟩, ⟨hx1, hx2, hx12⟩, hXe⟩ :=
    (openSegment_eq_image₂ ℝ A B).symm ▸ hp.1
  obtain ⟨⟨y1, y2⟩, ⟨hy1, hy2, hy12⟩, hYe⟩ :=
    (openSegment_eq_image₂ ℝ B C).symm ▸ hp.2.1
  obtain ⟨⟨z1, z2⟩, ⟨hz1, hz2, hz12⟩, hZe⟩ :=
    (openSegment_eq_image₂ ℝ C D).symm ▸ hp.2.2.1
  obtain ⟨⟨t1, t2⟩, ⟨ht1, ht2, ht12⟩, hTe⟩ :=
    (openSegment_eq_image₂ ℝ D A).symm ▸ hp.2.2.2
  rw [minLength_eq_dist_netA0_netA2 A B C D htet hcond hγ2' hγ2 hα2',
    ← dist_imgX_imgX3_of_condition A B C D htet hcond hα hβ hγ hδ hα2 hβ2 hγ2 hδ2 hx12]
  exact pathLength_ge_dist_imgX_imgX3 A B C D htet hx1 hx2 hx12 hXe hy1 hy2 hy12 hYe
    hz1 hz2 hz12 hZe ht1 ht2 ht12 hTe

/-! ### The signed area (2D cross product) and line crossings -/

/-- The 2D cross product (signed area). -/
noncomputable def crss (x y : Pt2) : ℝ := x 0 * y 1 - x 1 * y 0

lemma crss_e_e (θ₁ θ₂ : ℝ) : crss (e θ₁) (e θ₂) = Real.sin (θ₂ - θ₁) := by
  rw [crss, e_zero, e_one, e_zero, e_one, Real.sin_sub]
  ring

@[simp]
lemma crss_self (x : Pt2) : crss x x = 0 := by rw [crss]; ring

@[simp]
lemma crss_zero_left (y : Pt2) : crss 0 y = 0 := by simp [crss]

@[simp]
lemma crss_zero_right (x : Pt2) : crss x 0 = 0 := by simp [crss]

lemma crss_add_left (x y z : Pt2) : crss (x + y) z = crss x z + crss y z := by
  simp [crss]; ring

lemma crss_add_right (x y z : Pt2) : crss z (x + y) = crss z x + crss z y := by
  simp [crss]; ring

lemma crss_smul_left (r : ℝ) (x y : Pt2) : crss (r • x) y = r * crss x y := by
  simp [crss, smul_eq_mul]; ring

lemma crss_smul_right (r : ℝ) (x y : Pt2) : crss y (r • x) = r * crss y x := by
  simp [crss, smul_eq_mul]; ring

lemma crss_neg_left (x y : Pt2) : crss (-x) y = -crss x y := by simp [crss]; ring

lemma crss_neg_right (x y : Pt2) : crss y (-x) = -crss y x := by simp [crss]; ring

lemma crss_sub_left (x y z : Pt2) : crss (x - y) z = crss x z - crss y z := by
  simp [crss]; ring

lemma crss_sub_right (x y z : Pt2) : crss z (x - y) = crss z x - crss z y := by
  simp [crss]; ring

lemma crss_comm (x y : Pt2) : crss x y = -crss y x := by simp [crss]; ring

/-- If the signed area vanishes and `u ≠ 0`, then `v` is a scalar multiple of `u`. -/
lemma exists_smul_of_crss_eq_zero {u v : Pt2} (hu : u ≠ 0) (h : crss u v = 0) :
    ∃ r : ℝ, v = r • u := by
  have key : u 0 * v 1 = u 1 * v 0 := by rw [crss] at h; linarith [h]
  have hu0 : u 0 ≠ 0 ∨ u 1 ≠ 0 := by
    by_contra! hcon
    refine hu (PiLp.ext (fun i => ?_))
    fin_cases i <;> simp [hcon.1, hcon.2]
  rcases hu0 with h0 | h1
  · have hv1 : v 1 = u 1 * (v 0 / u 0) := by
      field_simp
      linarith [key]
    refine ⟨v 0 / u 0, PiLp.ext (fun i => ?_)⟩
    fin_cases i
    · simp [smul_eq_mul, div_mul_cancel₀ _ h0]
    · simp [smul_eq_mul, hv1]; ring
  · have hv0 : v 0 = u 0 * (v 1 / u 1) := by
      field_simp
      linarith [key]
    refine ⟨v 1 / u 1, PiLp.ext (fun i => ?_)⟩
    fin_cases i
    · simp [smul_eq_mul, hv0]; ring
    · simp [smul_eq_mul, div_mul_cancel₀ _ h1]

/-- A line through `X₀` in direction `u ≠ 0` meets the open segment `Q R` if the
endpoints are strictly on opposite sides of the line. -/
lemma exists_mem_openSegment_and_eq_add_smul_of_crss {u X₀ Q R : Pt2}
    (hQR : crss u (Q - X₀) * crss u (R - X₀) < 0) :
    ∃ Y : Pt2, Y ∈ openSegment ℝ Q R ∧ ∃ r : ℝ, Y = X₀ + r • u := by
  have hu : u ≠ 0 := by
    intro hu0
    rw [hu0] at hQR
    simp [crss] at hQR
  set a := crss u (Q - X₀) with ha_def
  set b := crss u (R - X₀) with hb_def
  have hab : a * b < 0 := hQR
  have ha : a ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hab; exact lt_irrefl _ hab
  have hb : b ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hab; exact lt_irrefl _ hab
  have hpos : 0 < |a| + |b| := add_pos_of_pos_of_nonneg (abs_pos.mpr ha) (abs_nonneg _)
  set lam := |b| / (|a| + |b|) with hlam_def
  have hlam0 : 0 < lam := div_pos (abs_pos.mpr hb) hpos
  have hlam1 : lam < 1 := by
    rw [div_lt_one hpos]
    have := abs_pos.mpr ha
    linarith [abs_nonneg b]
  have hsum : |b| * a + |a| * b = 0 := by
    rcases (mul_neg_iff).1 hab with h | h
    · rw [abs_of_pos h.1, abs_of_neg h.2]; ring
    · rw [abs_of_neg h.1, abs_of_pos h.2]; ring
  refine ⟨lam • Q + (1 - lam) • R, ?_, ?_⟩
  · rw [openSegment_eq_image₂]
    exact ⟨(lam, 1 - lam), ⟨hlam0, by linarith [hlam1], by ring⟩, rfl⟩
  · have hcr : crss u ((lam • Q + (1 - lam) • R) - X₀) = 0 := by
      have hde : (lam • Q + (1 - lam) • R) - X₀ =
          lam • (Q - X₀) + (1 - lam) • (R - X₀) := by module
      rw [hde, crss_add_right, crss_smul_right, crss_smul_right, hlam_def]
      field_simp
      linarith [hsum]
    obtain ⟨r, hr⟩ := exists_smul_of_crss_eq_zero hu hcr
    exact ⟨r, by rw [← hr]; module⟩

/-- The projection formula: a side of a triangle is the sum of the projections
of the other two sides. -/
lemma side_eq_proj (X Y Z : Pt) (h0 : dist Y Z ≠ 0) :
    dist Y Z = dist X Z * Real.cos (∠ X Z Y) + dist X Y * Real.cos (∠ X Y Z) := by
  have h1 := law_cos X Y Z
  have h2 := law_cos X Z Y
  rw [dist_comm Z Y] at h1
  apply mul_left_cancel₀ (mul_ne_zero two_ne_zero h0)
  linear_combination -h1 - h2


namespace Trihedral

open Real Set InnerProductGeometry

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- If `![u, v, w]` is linearly independent, the only vanishing linear combination of
`u, v, w` is the trivial one. -/
lemma combo_eq_zero {u v w : V} (hind : LinearIndependent ℝ ![u, v, w])
    {a b c : ℝ} (h : a • u + b • v + c • w = 0) : a = 0 ∧ b = 0 ∧ c = 0 := by
  have key := (Fintype.linearIndependent_iff.mp hind) ![a, b, c] (by
    simpa [Fin.sum_univ_three] using h)
  exact ⟨by simpa using key 0, by simpa using key 1, by simpa using key 2⟩

/-- In a linearly independent triple, no vector is a scalar multiple of another one.
We record the three cases needed below. -/
lemma not_smul_of_indep {u v w : V} (hind : LinearIndependent ℝ ![u, v, w]) :
    (¬ ∃ r : ℝ, v = r • u) ∧ (¬ ∃ r : ℝ, w = r • u) ∧ (¬ ∃ r : ℝ, v = r • w) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨r, hr⟩
    have h0 : r • u + (-1 : ℝ) • v + (0 : ℝ) • w = 0 := by
      rw [hr]
      module
    obtain ⟨-, h1, -⟩ := combo_eq_zero hind (a := r) (b := -1) (c := 0) h0
    norm_num at h1
  · rintro ⟨r, hr⟩
    have h0 : r • u + (0 : ℝ) • v + (-1 : ℝ) • w = 0 := by
      rw [hr]
      module
    obtain ⟨-, -, h2⟩ := combo_eq_zero hind (a := r) (b := 0) (c := -1) h0
    norm_num at h2
  · rintro ⟨r, hr⟩
    have h0 : (0 : ℝ) • u + (-1 : ℝ) • v + r • w = 0 := by
      rw [hr]
      module
    obtain ⟨-, h1, -⟩ := combo_eq_zero hind (a := 0) (b := -1) (c := r) h0
    norm_num at h1

/-- If `y` is not a scalar multiple of `x`, the InnerProductGeometry.angle between them lies strictly between
`0` and `π`. -/
lemma angle_mem_Ioo {x y : V} (hnp : ¬ ∃ r : ℝ, y = r • x) :
    InnerProductGeometry.angle x y ∈ Ioo 0 π := by
  refine ⟨lt_of_le_of_ne' (angle_nonneg x y) ?_, lt_of_le_of_ne (angle_le_pi x y) ?_⟩
  · intro h0
    obtain ⟨-, r, -, hr⟩ := angle_eq_zero_iff.mp h0
    exact hnp ⟨r, hr⟩
  · intro hpi
    obtain ⟨-, r, -, hr⟩ := angle_eq_pi_iff.mp hpi
    exact hnp ⟨r, hr⟩

/-- Unitizing a nonzero vector gives a norm-one vector. -/
lemma norm_smul_inv_self {x : V} (hx : x ≠ 0) : ‖‖x‖⁻¹ • x‖ = 1 := by
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x)), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]

/-- The inner product of two unitized vectors, times the product of the norms, is the
inner product. -/
lemma inner_smul_inv_norm {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
    ⟪‖x‖⁻¹ • x, ‖y‖⁻¹ • y⟫ * (‖x‖ * ‖y‖) = ⟪x, y⟫ := by
  have hnx : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hny : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  rw [real_inner_smul_left, inner_smul_right,
    show ‖x‖⁻¹ * (‖y‖⁻¹ * ⟪x, y⟫) * (‖x‖ * ‖y‖)
        = (‖x‖⁻¹ * ‖x‖) * ((‖y‖⁻¹ * ‖y‖) * ⟪x, y⟫) by ring,
    inv_mul_cancel₀ hnx, inv_mul_cancel₀ hny, one_mul, one_mul]

/-- The strict spherical triangle (trihedral) inequality: for three linearly
independent vectors, each InnerProductGeometry.angle is strictly less than the sum of the other two. -/
theorem trihedral_angle_lt {u v w : V} (hind : LinearIndependent ℝ ![u, v, w]) :
    InnerProductGeometry.angle u v < InnerProductGeometry.angle u w + InnerProductGeometry.angle w v := by
  -- The vectors are nonzero and no one is a scalar multiple of another.
  have hu0 : u ≠ 0 := by simpa using hind.ne_zero 0
  have hv0 : v ≠ 0 := by simpa using hind.ne_zero 1
  have hw0 : w ≠ 0 := by simpa using hind.ne_zero 2
  have hnu : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu0
  have hnv : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv0
  have hnw : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw0
  obtain ⟨hnp1, hnp2, hnp3⟩ := not_smul_of_indep hind
  have huvI : InnerProductGeometry.angle u v ∈ Ioo 0 π := angle_mem_Ioo hnp1
  have huwI : InnerProductGeometry.angle u w ∈ Ioo 0 π := angle_mem_Ioo hnp2
  have hwvI : InnerProductGeometry.angle w v ∈ Ioo 0 π := angle_mem_Ioo hnp3
  -- Unit vectors.
  set u' := ‖u‖⁻¹ • u with hu'
  set v' := ‖v‖⁻¹ • v with hv'
  set w' := ‖w‖⁻¹ • w with hw'
  have nu' : ‖u'‖ = 1 := by
    rw [hu']
    exact norm_smul_inv_self hu0
  have nv' : ‖v'‖ = 1 := by
    rw [hv']
    exact norm_smul_inv_self hv0
  have nw' : ‖w'‖ = 1 := by
    rw [hw']
    exact norm_smul_inv_self hw0
  have huu : ⟪u', u'⟫ = 1 := by rw [real_inner_self_eq_norm_sq, nu', one_pow]
  have hvv : ⟪v', v'⟫ = 1 := by rw [real_inner_self_eq_norm_sq, nv', one_pow]
  have hww : ⟪w', w'⟫ = 1 := by rw [real_inner_self_eq_norm_sq, nw', one_pow]
  -- The cosines of the three angles.
  set c₁ := ⟪u', w'⟫ with hc₁
  set c₂ := ⟪w', v'⟫ with hc₂
  set c₃ := ⟪u', v'⟫ with hc₃
  have cos_uw : cos (InnerProductGeometry.angle u w) = c₁ := by
    rw [cos_angle, div_eq_iff (mul_ne_zero hnu hnw), hc₁, hu', hw']
    exact (inner_smul_inv_norm hu0 hw0).symm
  have cos_wv : cos (InnerProductGeometry.angle w v) = c₂ := by
    rw [cos_angle, div_eq_iff (mul_ne_zero hnw hnv), hc₂, hw', hv']
    exact (inner_smul_inv_norm hw0 hv0).symm
  have cos_uv : cos (InnerProductGeometry.angle u v) = c₃ := by
    rw [cos_angle, div_eq_iff (mul_ne_zero hnu hnv), hc₃, hu', hv']
    exact (inner_smul_inv_norm hu0 hv0).symm
  -- The components of `u'`, `v'` orthogonal to `w'`.
  set x := u' - c₁ • w' with hx
  set y := v' - c₂ • w' with hy
  -- `x` and `y` are linearly independent.
  have hxy : ∀ a b : ℝ, a • x + b • y = 0 → a = 0 ∧ b = 0 := by
    intro a b hab
    have e : a • x + b • y = (a * ‖u‖⁻¹) • u + (b * ‖v‖⁻¹) • v
        + (-(a * c₁ + b * c₂) * ‖w‖⁻¹) • w := by
      rw [hx, hy, hu', hv', hw']
      module
    rw [e] at hab
    obtain ⟨ha, hb, -⟩ := combo_eq_zero hind hab
    refine ⟨?_, ?_⟩
    · rcases mul_eq_zero.mp ha with h | h
      · exact h
      · exact absurd h (inv_ne_zero hnu)
    · rcases mul_eq_zero.mp hb with h | h
      · exact h
      · exact absurd h (inv_ne_zero hnv)
  -- Strict Cauchy–Schwarz for `x` and `y`.
  have hcs : ⟪x, y⟫ ^ 2 < ⟪x, x⟫ * ⟪y, y⟫ := by
    by_contra hcon
    push Not at hcon
    rw [pow_two] at hcon
    have heq : ⟪x, x⟫ * ⟪y, y⟫ = ⟪x, y⟫ * ⟪x, y⟫ :=
      le_antisymm hcon (real_inner_mul_inner_self_le x y)
    -- The vector `⟪y,y⟫ • x - ⟪x,y⟫ • y` has zero inner product with itself.
    have hzz : ⟪y, y⟫ • x - ⟪x, y⟫ • y = 0 := by
      apply (inner_self_eq_zero (𝕜 := ℝ)).mp
      have e : ⟪⟪y, y⟫ • x - ⟪x, y⟫ • y, ⟪y, y⟫ • x - ⟪x, y⟫ • y⟫
          = ⟪y, y⟫ * (⟪x, x⟫ * ⟪y, y⟫ - ⟪x, y⟫ * ⟪x, y⟫) := by
        simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, inner_smul_right,
          real_inner_comm x y]
        ring
      rw [e, heq, sub_self, mul_zero]
    have hcomb : ⟪y, y⟫ • x + (-⟪x, y⟫) • y = 0 := by
      rw [neg_smul, ← sub_eq_add_neg]
      exact hzz
    obtain ⟨hyy0, -⟩ := hxy ⟪y, y⟫ (-⟪x, y⟫) hcomb
    have hy0 : y = 0 := (inner_self_eq_zero (𝕜 := ℝ)).mp hyy0
    obtain ⟨-, h10⟩ := hxy 0 1 (by rw [zero_smul, one_smul, zero_add]; exact hy0)
    exact one_ne_zero h10
  -- The Gram determinant is positive.
  have hxx : ⟪x, x⟫ = 1 - c₁ ^ 2 := by
    rw [hx]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, inner_smul_right,
      real_inner_comm u' w', ← hc₁, huu, hww]
    ring
  have hyy : ⟪y, y⟫ = 1 - c₂ ^ 2 := by
    rw [hy]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, inner_smul_right,
      real_inner_comm w' v', ← hc₂, hvv, hww]
    ring
  have hxyi : ⟪x, y⟫ = c₃ - c₁ * c₂ := by
    rw [hx, hy]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, inner_smul_right,
      ← hc₁, ← hc₂, ← hc₃, hww]
    ring
  have hD : 0 < 1 - c₁ ^ 2 - c₂ ^ 2 - c₃ ^ 2 + 2 * c₁ * c₂ * c₃ := by
    have key : (1 - c₁ ^ 2) * (1 - c₂ ^ 2) - (c₃ - c₁ * c₂) ^ 2
        = 1 - c₁ ^ 2 - c₂ ^ 2 - c₃ ^ 2 + 2 * c₁ * c₂ * c₃ := by
      ring
    rw [hxx, hyy, hxyi] at hcs
    linarith [hcs, key]
  -- The sines of the two angles on the right.
  have hs1 : sin (InnerProductGeometry.angle u w) = √(1 - c₁ ^ 2) := by
    rw [Real.sin_eq_sqrt_one_sub_cos_sq (angle_nonneg u w) (angle_le_pi u w), cos_uw]
  have hs2 : sin (InnerProductGeometry.angle w v) = √(1 - c₂ ^ 2) := by
    rw [Real.sin_eq_sqrt_one_sub_cos_sq (angle_nonneg w v) (angle_le_pi w v), cos_wv]
  have hC1 : 0 ≤ 1 - c₁ ^ 2 := by
    rw [← hxx]
    exact real_inner_self_nonneg
  have hC2 : 0 ≤ 1 - c₂ ^ 2 := by
    rw [← hyy]
    exact real_inner_self_nonneg
  -- Case split: if the right-hand side is at least `π`, strictness comes from
  -- `InnerProductGeometry.angle u v < π`.
  by_cases hcase : π ≤ InnerProductGeometry.angle u w + InnerProductGeometry.angle w v
  · exact huvI.2.trans_le hcase
  · -- Otherwise both sides lie in `[0, π]` and we compare cosines.
    have hcase : InnerProductGeometry.angle u w + InnerProductGeometry.angle w v < π := lt_of_not_ge hcase
    have hsum_nn : 0 ≤ InnerProductGeometry.angle u w + InnerProductGeometry.angle w v :=
      add_nonneg (angle_nonneg u w) (angle_nonneg w v)
    have hmem1 : InnerProductGeometry.angle u v ∈ Icc (0 : ℝ) π := ⟨angle_nonneg u v, angle_le_pi u v⟩
    have hmem2 : InnerProductGeometry.angle u w + InnerProductGeometry.angle w v ∈ Icc (0 : ℝ) π := ⟨hsum_nn, hcase.le⟩
    have hs1pos : 0 < √(1 - c₁ ^ 2) := hs1 ▸ Real.sin_pos_of_mem_Ioo huwI
    have hs2pos : 0 < √(1 - c₂ ^ 2) := hs2 ▸ Real.sin_pos_of_mem_Ioo hwvI
    have hspos : 0 < √(1 - c₁ ^ 2) * √(1 - c₂ ^ 2) := mul_pos hs1pos hs2pos
    have hcos : cos (InnerProductGeometry.angle u w + InnerProductGeometry.angle w v) < cos (InnerProductGeometry.angle u v) := by
      rw [Real.cos_add, cos_uw, cos_wv, cos_uv, hs1, hs2]
      by_cases hneg : c₁ * c₂ - c₃ ≤ 0
      · linarith [hspos]
      · have hpos : 0 < c₁ * c₂ - c₃ := lt_of_not_ge hneg
        have hsq : (c₁ * c₂ - c₃) ^ 2 < (√(1 - c₁ ^ 2) * √(1 - c₂ ^ 2)) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hC1, Real.sq_sqrt hC2]
          have key : (1 - c₁ ^ 2) * (1 - c₂ ^ 2) - (c₁ * c₂ - c₃) ^ 2
              = 1 - c₁ ^ 2 - c₂ ^ 2 - c₃ ^ 2 + 2 * c₁ * c₂ * c₃ := by
            ring
          linarith [hD, key]
        have habs := sq_lt_sq.mp hsq
        rw [abs_of_pos hpos, abs_of_pos hspos] at habs
        linarith
    -- `cos` is strictly antitone on `[0, π]`, so we are done.
    by_contra hcon
    push Not at hcon
    have hmono := Real.strictAntiOn_cos.antitoneOn hmem2 hmem1 hcon
    linarith

end Trihedral

/-- The vectors from one vertex of a non-degenerate tetrahedron to the other
three are linearly independent. -/
lemma linIndep_of_tet (A B C D : Pt) (htet : AffineIndependent ℝ ![A, B, C, D]) :
    LinearIndependent ℝ ![B - C, A - C, D - C] := by
  have hperm : AffineIndependent ℝ ((![A, B, C, D] : Fin 4 → Pt) ∘ ![(2 : Fin 4), 0, 1, 3]) :=
    AffineIndependent.comp_embedding ⟨![(2 : Fin 4), 0, 1, 3], by decide⟩ htet
  have hli := (affineIndependent_iff_linearIndependent_vsub (k := ℝ)
    ((![A, B, C, D] : Fin 4 → Pt) ∘ ![(2 : Fin 4), 0, 1, 3]) (0 : Fin 4)).mp hperm
  have hcomp := LinearIndependent.comp hli ![⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩] (by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all)
  have hcomp2 := LinearIndependent.comp hcomp ![(1 : Fin 3), 0, 2] (by decide)
  have hEq : (((fun i : {x // x ≠ (0 : Fin 4)} =>
      (((![A, B, C, D] : Fin 4 → Pt) ∘ ![(2 : Fin 4), 0, 1, 3]) i -ᵥ
        ((![A, B, C, D] : Fin 4 → Pt) ∘ ![(2 : Fin 4), 0, 1, 3]) 0)) ∘
      ![⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩]) ∘ ![(1 : Fin 3), 0, 2]) =
      ![B - C, A - C, D - C] := by
    funext i
    fin_cases i <;> simp [Function.comp_apply, vsub_eq_sub]
  rwa [hEq] at hcomp2

lemma linIndep_triple_rev {u v w : Pt} (h : LinearIndependent ℝ ![u, v, w]) :
    LinearIndependent ℝ ![w, v, u] := by
  have h2 := LinearIndependent.comp h ![(2 : Fin 3), 1, 0] (by decide)
  rwa [show (![u, v, w] ∘ ![(2 : Fin 3), 1, 0]) = ![w, v, u] from by
    funext i; fin_cases i <;> simp [Function.comp_apply]] at h2

/-- The trihedral (spherical) inequalities at vertex `C` of the tetrahedron. -/
lemma trihedral_at_C (A B C D : Pt) (htet : AffineIndependent ℝ ![A, B, C, D]) :
    (∠ B C A < ∠ B C D + ∠ D C A) ∧ (∠ D C A < ∠ B C D + ∠ B C A) := by
  have hli := linIndep_of_tet A B C D htet
  have h1 : InnerProductGeometry.angle (B - C) (A - C) <
      InnerProductGeometry.angle (B - C) (D - C) + InnerProductGeometry.angle (D - C) (A - C) :=
    Trihedral.trihedral_angle_lt (u := B - C) (v := A - C) (w := D - C) hli
  have h2 : InnerProductGeometry.angle (D - C) (A - C) <
      InnerProductGeometry.angle (D - C) (B - C) + InnerProductGeometry.angle (B - C) (A - C) :=
    Trihedral.trihedral_angle_lt (u := D - C) (v := A - C) (w := B - C) (linIndep_triple_rev hli)
  refine ⟨h1, ?_⟩
  rwa [show InnerProductGeometry.angle (D - C) (B - C) = ∠ D C B from rfl,
    angle_comm D C B] at h2

/-- The signed area of `netB0` with respect to the transversal direction `u = netA2 - netA0`. -/
lemma crss_u_netB0 (A B C D : Pt) :
    crss (netA2 A B C D - netA0 A B C) (netB0 B C) =
      dist B C * dist A C * (Real.sin (∠ B C D + ∠ D C A) + Real.sin (∠ B C A)) := by
  rw [crss_sub_left, netA2, netA0, netB0, crss_smul_left, crss_smul_right, crss_e_e,
    crss_smul_left, crss_smul_right, crss_e_e,
    show (0:ℝ) - -(∠ B C D + ∠ D C A) = ∠ B C D + ∠ D C A from by ring,
    show (0:ℝ) - ∠ B C A = -(∠ B C A) from by ring, Real.sin_neg]
  ring

lemma crss_u_netB0_pos (A B C D : Pt) (htet : AffineIndependent ℝ ![A, B, C, D])
    (hBCD : AcuteTriangle B C D) (hACD : AcuteTriangle A C D) :
    0 < crss (netA2 A B C D - netA0 A B C) (netB0 B C) := by
  rw [crss_u_netB0]
  have hsin1 : 0 < Real.sin (∠ B C D + ∠ D C A) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · have h1 := by simpa using angle_pos_of_tet A B C D htet 1 2 3 (by decide) (by decide) (by decide)
      have h2 := by simpa using angle_pos_of_tet A B C D htet 3 2 0 (by decide) (by decide) (by decide)
      linarith
    · have h3 : ∠ B C D < π / 2 := hBCD.1
      have h5 : ∠ D C A < π / 2 := by rw [angle_comm D C A]; exact hACD.1
      have hpi := Real.pi_pos
      linarith
  have hsin2 := by simpa using sin_pos_of_tet A B C D htet 1 2 0 (by decide) (by decide) (by decide)
  have hBC : B ≠ C := by have h := tet_ne htet (show (1 : Fin 4) ≠ 2 by decide); simpa using h
  have hAC : A ≠ C := by have h := tet_ne htet (show (0 : Fin 4) ≠ 2 by decide); simpa using h
  exact mul_pos (mul_pos (dist_pos.mpr hBC) (dist_pos.mpr hAC)) (by linarith [hsin1, hsin2])

/-- The signed area of `netA0` with respect to `u`. -/
lemma crss_u_netA0 (A B C D : Pt) :
    crss (netA2 A B C D - netA0 A B C) (netA0 A B C) =
      dist A C ^ 2 * Real.sin (∠ B C A + ∠ B C D + ∠ D C A) := by
  rw [crss_sub_left, crss_self, sub_zero, netA2, netA0, crss_smul_left, crss_smul_right, crss_e_e,
    show (∠ B C A) - -(∠ B C D + ∠ D C A) = ∠ B C A + ∠ B C D + ∠ D C A from by ring]
  ring

/-- The signed area of `netD1` with respect to `u`. -/
lemma crss_u_netD1 (A B C D : Pt) :
    crss (netA2 A B C D - netA0 A B C) (netD1 B C D) =
      dist C D * dist A C * (Real.sin (∠ D C A) + Real.sin (∠ B C D + ∠ B C A)) := by
  rw [crss_sub_left, netA2, netA0, netD1, crss_smul_left, crss_smul_right, crss_e_e,
    crss_smul_left, crss_smul_right, crss_e_e,
    show -(∠ B C D) - -(∠ B C D + ∠ D C A) = ∠ D C A from by ring,
    show -(∠ B C D) - ∠ B C A = -(∠ B C D + ∠ B C A) from by ring, Real.sin_neg]
  ring

lemma crss_u_netD1_pos (A B C D : Pt) (htet : AffineIndependent ℝ ![A, B, C, D])
    (hBCD : AcuteTriangle B C D) (hABC : AcuteTriangle A B C) :
    0 < crss (netA2 A B C D - netA0 A B C) (netD1 B C D) := by
  rw [crss_u_netD1]
  have hsin1 := by simpa using sin_pos_of_tet A B C D htet 3 2 0 (by decide) (by decide) (by decide)
  have hsin2 : 0 < Real.sin (∠ B C D + ∠ B C A) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · have h1 := by simpa using angle_pos_of_tet A B C D htet 1 2 3 (by decide) (by decide) (by decide)
      have h2 := by simpa using angle_pos_of_tet A B C D htet 1 2 0 (by decide) (by decide) (by decide)
      linarith
    · have h3 : ∠ B C D < π / 2 := hBCD.1
      have h4 : ∠ B C A < π / 2 := hABC.2.1
      have hpi := Real.pi_pos
      linarith
  have hCD : C ≠ D := by have h := tet_ne htet (show (2 : Fin 4) ≠ 3 by decide); simpa using h
  have hAC : A ≠ C := by have h := tet_ne htet (show (0 : Fin 4) ≠ 2 by decide); simpa using h
  exact mul_pos (mul_pos (dist_pos.mpr hCD) (dist_pos.mpr hAC)) (by linarith [hsin1, hsin2])

/-- The transversal direction is nonzero. -/
lemma u_ne_zero (A B C D : Pt) (htet : AffineIndependent ℝ ![A, B, C, D])
    (hBCD : AcuteTriangle B C D) (hACD : AcuteTriangle A C D) :
    netA2 A B C D - netA0 A B C ≠ 0 := by
  have h := crss_u_netB0_pos A B C D htet hBCD hACD
  intro hu
  rw [hu, crss_zero_left] at h
  exact lt_irrefl _ h

/-- F1: the trihedral inequality at `C` forces `cA0 < cB0`. -/
lemma crss_u_netA0_lt_crss_u_netB0 (A B C D : Pt) (htet : AffineIndependent ℝ ![A, B, C, D])
    (hABC : AcuteTriangle A B C) (hBCD : AcuteTriangle B C D) (hACD : AcuteTriangle A C D)
    (htri : ∠ B C A < ∠ B C D + ∠ D C A) :
    crss (netA2 A B C D - netA0 A B C) (netA0 A B C) <
      crss (netA2 A B C D - netA0 A B C) (netB0 B C) := by
  have hAB : A ≠ B := by have h := tet_ne htet (show (0 : Fin 4) ≠ 1 by decide); simpa using h
  have hAC : A ≠ C := by have h := tet_ne htet (show (0 : Fin 4) ≠ 2 by decide); simpa using h
  have hBC : B ≠ C := by have h := tet_ne htet (show (1 : Fin 4) ≠ 2 by decide); simpa using h
  have hb : 0 < dist A C := dist_pos.mpr hAC
  rw [crss_u_netA0, crss_u_netB0]
  have hfoot : dist A C * Real.cos (∠ B C A) < dist B C := by
    have hproj := side_eq_proj A C B (dist_ne_zero.mpr hBC.symm)
    rw [angle_comm A C B] at hproj
    have hpos : 0 < ∠ A B C := by
      simpa using angle_pos_of_tet A B C D htet 0 1 2 (by decide) (by decide) (by decide)
    have hcos : 0 < Real.cos (∠ A B C) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hpos, Real.pi_pos], hABC.1⟩
    have hc : 0 < dist A B := dist_pos.mpr hAB
    have hpos2 : 0 < dist A B * Real.cos (∠ A B C) := mul_pos hc hcos
    have hcb : dist B C = dist C B := dist_comm _ _
    linarith [hproj, hpos2, hcb]
  have hcosmono : Real.cos (∠ B C D + ∠ D C A) < Real.cos (∠ B C A) := by
    apply Real.strictAntiOn_cos
    · exact ⟨angle_nonneg _ _ _, angle_le_pi _ _ _⟩
    · have h1 : 0 ≤ ∠ B C D := angle_nonneg _ _ _
      have h2 : 0 ≤ ∠ D C A := angle_nonneg _ _ _
      have h3 : ∠ B C D < π / 2 := hBCD.1
      have h4 : ∠ A C D < π / 2 := hACD.1
      have h5 : ∠ D C A < π / 2 := by rw [angle_comm D C A]; exact hACD.1
      have hpi := Real.pi_pos
      exact ⟨by linarith, by linarith⟩
    · exact htri
  have hsin1 := by simpa using sin_pos_of_tet A B C D htet 1 2 0 (by decide) (by decide) (by decide)
  have hsin2 : 0 < Real.sin (∠ B C D + ∠ D C A) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · have h1 := by simpa using angle_pos_of_tet A B C D htet 1 2 3 (by decide) (by decide) (by decide)
      have h2 := by simpa using angle_pos_of_tet A B C D htet 3 2 0 (by decide) (by decide) (by decide)
      linarith
    · have h3 : ∠ B C D < π / 2 := hBCD.1
      have h5 : ∠ D C A < π / 2 := by rw [angle_comm D C A]; exact hACD.1
      have hpi := Real.pi_pos
      linarith
  have key : dist A C * Real.sin (∠ B C A + ∠ B C D + ∠ D C A) -
      dist B C * (Real.sin (∠ B C D + ∠ D C A) + Real.sin (∠ B C A)) < 0 := by
    rw [show ∠ B C A + ∠ B C D + ∠ D C A = ∠ B C A + (∠ B C D + ∠ D C A) from by ring,
      Real.sin_add]
    have h1 : Real.sin (∠ B C A) * (dist A C * Real.cos (∠ B C D + ∠ D C A) - dist B C) < 0 := by
      apply mul_neg_of_pos_of_neg hsin1
      have h2 : dist A C * Real.cos (∠ B C D + ∠ D C A) < dist A C * Real.cos (∠ B C A) :=
        mul_lt_mul_of_pos_left hcosmono hb
      linarith [h2, hfoot]
    have h2 : Real.sin (∠ B C D + ∠ D C A) * (dist A C * Real.cos (∠ B C A) - dist B C) < 0 := by
      exact mul_neg_of_pos_of_neg hsin2 (by linarith [hfoot])
    linarith [h1, h2]
  have hb2 : dist A C ^ 2 * Real.sin (∠ B C A + ∠ B C D + ∠ D C A) <
      dist B C * dist A C * (Real.sin (∠ B C D + ∠ D C A) + Real.sin (∠ B C A)) := by
    have h3 := mul_lt_mul_of_pos_left key hb
    rw [mul_sub] at h3
    have h4 : dist A C * (dist A C * Real.sin (∠ B C A + ∠ B C D + ∠ D C A)) =
        dist A C ^ 2 * Real.sin (∠ B C A + ∠ B C D + ∠ D C A) := by ring
    rw [h4] at h3
    have h5 : dist A C * (dist B C * (Real.sin (∠ B C D + ∠ D C A) + Real.sin (∠ B C A))) =
        dist B C * dist A C * (Real.sin (∠ B C D + ∠ D C A) + Real.sin (∠ B C A)) := by ring
    linarith [h3, h5]
  exact hb2

/-- F2: the trihedral inequality at `C` forces `cA0 < cD1`. -/
lemma crss_u_netA0_lt_crss_u_netD1 (A B C D : Pt) (htet : AffineIndependent ℝ ![A, B, C, D])
    (hABC : AcuteTriangle A B C) (hBCD : AcuteTriangle B C D) (hACD : AcuteTriangle A C D)
    (htri : ∠ D C A < ∠ B C D + ∠ B C A) :
    crss (netA2 A B C D - netA0 A B C) (netA0 A B C) <
      crss (netA2 A B C D - netA0 A B C) (netD1 B C D) := by
  have hCD : C ≠ D := by have h := tet_ne htet (show (2 : Fin 4) ≠ 3 by decide); simpa using h
  have hAC : A ≠ C := by have h := tet_ne htet (show (0 : Fin 4) ≠ 2 by decide); simpa using h
  have hAD : A ≠ D := by have h := tet_ne htet (show (0 : Fin 4) ≠ 3 by decide); simpa using h
  have hb : 0 < dist A C := dist_pos.mpr hAC
  rw [crss_u_netA0, crss_u_netD1]
  have hfoot : dist A C * Real.cos (∠ D C A) < dist C D := by
    have hproj := side_eq_proj A D C (dist_ne_zero.mpr hCD.symm)
    rw [angle_comm A D C] at hproj
    rw [angle_comm A C D] at hproj
    have hpos : 0 < ∠ C D A := by
      simpa using angle_pos_of_tet A B C D htet 2 3 0 (by decide) (by decide) (by decide)
    have hcos : 0 < Real.cos (∠ C D A) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hpos, Real.pi_pos], hACD.2.1⟩
    have he : 0 < dist A D := dist_pos.mpr hAD
    have hpos2 : 0 < dist A D * Real.cos (∠ C D A) := mul_pos he hcos
    have hcb : dist C D = dist D C := dist_comm _ _
    linarith [hproj, hpos2, hcb]
  have hcosmono : Real.cos (∠ B C D + ∠ B C A) < Real.cos (∠ D C A) := by
    apply Real.strictAntiOn_cos
    · exact ⟨angle_nonneg _ _ _, angle_le_pi _ _ _⟩
    · have h1 : 0 ≤ ∠ B C D := angle_nonneg _ _ _
      have h2 : 0 ≤ ∠ B C A := angle_nonneg _ _ _
      have h3 : ∠ B C D < π / 2 := hBCD.1
      have h4 : ∠ B C A < π / 2 := hABC.2.1
      have hpi := Real.pi_pos
      exact ⟨by linarith, by linarith⟩
    · exact htri
  have hsin1 := by simpa using sin_pos_of_tet A B C D htet 3 2 0 (by decide) (by decide) (by decide)
  have hsin2 : 0 < Real.sin (∠ B C D + ∠ B C A) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · have h1 := by simpa using angle_pos_of_tet A B C D htet 1 2 3 (by decide) (by decide) (by decide)
      have h2 := by simpa using angle_pos_of_tet A B C D htet 1 2 0 (by decide) (by decide) (by decide)
      linarith
    · have h3 : ∠ B C D < π / 2 := hBCD.1
      have h4 : ∠ B C A < π / 2 := hABC.2.1
      have hpi := Real.pi_pos
      linarith
  have key : dist A C * Real.sin (∠ B C A + ∠ B C D + ∠ D C A) -
      dist C D * (Real.sin (∠ D C A) + Real.sin (∠ B C D + ∠ B C A)) < 0 := by
    rw [show ∠ B C A + ∠ B C D + ∠ D C A = ∠ D C A + (∠ B C D + ∠ B C A) from by ring,
      Real.sin_add]
    have h1 : Real.sin (∠ D C A) * (dist A C * Real.cos (∠ B C D + ∠ B C A) - dist C D) < 0 := by
      apply mul_neg_of_pos_of_neg hsin1
      have h2 : dist A C * Real.cos (∠ B C D + ∠ B C A) < dist A C * Real.cos (∠ D C A) :=
        mul_lt_mul_of_pos_left hcosmono hb
      linarith [h2, hfoot]
    have h2 : Real.sin (∠ B C D + ∠ B C A) * (dist A C * Real.cos (∠ D C A) - dist C D) < 0 := by
      exact mul_neg_of_pos_of_neg hsin2 (by linarith [hfoot])
    linarith [h1, h2]
  have hb2 : dist A C ^ 2 * Real.sin (∠ B C A + ∠ B C D + ∠ D C A) <
      dist C D * dist A C * (Real.sin (∠ D C A) + Real.sin (∠ B C D + ∠ B C A)) := by
    have h3 := mul_lt_mul_of_pos_left key hb
    rw [mul_sub] at h3
    have h4 : dist A C * (dist A C * Real.sin (∠ B C A + ∠ B C D + ∠ D C A)) =
        dist A C ^ 2 * Real.sin (∠ B C A + ∠ B C D + ∠ D C A) := by ring
    rw [h4] at h3
    have h5 : dist A C * (dist C D * (Real.sin (∠ D C A) + Real.sin (∠ B C D + ∠ B C A))) =
        dist C D * dist A C * (Real.sin (∠ D C A) + Real.sin (∠ B C D + ∠ B C A)) := by ring
    linarith [h3, h5]
  exact hb2

/-- The auxiliary inequality for the attainability of shortest paths:
the transversal crosses the second hinge within the segment. -/
lemma net_ineq_aux (A B C D : Pt) (htet : AffineIndependent ℝ ![A, B, C, D])
    (hABC : AcuteTriangle A B C) (hBCD : AcuteTriangle B C D)
    (hACD : AcuteTriangle A C D) (hABD : AcuteTriangle A B D)
    (hcond : ∠ D A B + ∠ B C D = ∠ C D A + ∠ A B C) :
    dist A C * Real.sin (∠ D C A) + dist A C * Real.sin (∠ B C A + ∠ B C D) -
      dist B C * Real.sin (∠ B C D) > 0 := by
  have hAB : A ≠ B := by have h := tet_ne htet (show (0 : Fin 4) ≠ 1 by decide); simpa using h
  have hBC : B ≠ C := by have h := tet_ne htet (show (1 : Fin 4) ≠ 2 by decide); simpa using h
  have hAD : A ≠ D := by have h := tet_ne htet (show (0 : Fin 4) ≠ 3 by decide); simpa using h
  have hBD : B ≠ D := by have h := tet_ne htet (show (1 : Fin 4) ≠ 3 by decide); simpa using h
  have hproj1 := side_eq_proj A C B (dist_ne_zero.mpr hBC.symm)
  rw [angle_comm A C B] at hproj1
  have hproj2 := side_eq_proj B D A (dist_ne_zero.mpr hAD.symm)
  rw [angle_comm B A D] at hproj2
  have hsin1 : Real.sin (∠ B C A) * dist A C = Real.sin (∠ A B C) * dist A B := by
    have h := law_sin B C A
    rwa [dist_comm C A] at h
  have hsin2 : Real.sin (∠ D C A) * dist A C = Real.sin (∠ C D A) * dist A D := by
    have h := law_sin D C A
    rw [angle_comm A D C] at h
    rwa [dist_comm C A] at h
  have hid : dist A C * Real.sin (∠ D C A) + dist A C * Real.sin (∠ B C A + ∠ B C D) -
      dist B C * Real.sin (∠ B C D) =
      dist A D * Real.sin (∠ C D A) - dist A B * Real.sin (∠ C D A - ∠ D A B) := by
    have hcond2 : ∠ B C D - ∠ A B C = ∠ C D A - ∠ D A B := by linarith [hcond]
    have hcomm : dist B C = dist C B := dist_comm _ _
    rw [Real.sin_add, ← hcond2, Real.sin_sub]
    linear_combination hsin2 + Real.cos (∠ B C D) * hsin1 - Real.sin (∠ B C D) * hproj1 -
      Real.sin (∠ B C D) * hcomm
  rw [hid, Real.sin_sub]
  have hcos1 : 0 < Real.cos (∠ B D A) := by
    have hpos : 0 < ∠ B D A := by
      rw [angle_comm B D A]
      simpa using angle_pos_of_tet A B C D htet 0 3 1 (by decide) (by decide) (by decide)
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [hpos, Real.pi_pos], hABD.2.1⟩
  have hcos2 : 0 < Real.cos (∠ C D A) := by
    have hpos : 0 < ∠ C D A := by
      simpa using angle_pos_of_tet A B C D htet 2 3 0 (by decide) (by decide) (by decide)
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [hpos, Real.pi_pos], hACD.2.1⟩
  have hsinδd := by simpa using sin_pos_of_tet A B C D htet 2 3 0 (by decide) (by decide) (by decide)
  have hsinαa := by simpa using sin_pos_of_tet A B C D htet 3 0 1 (by decide) (by decide) (by decide)
  have hf : 0 < dist B D := dist_pos.mpr hBD
  have hc : 0 < dist A B := dist_pos.mpr hAB
  have h1 : dist A D - dist A B * Real.cos (∠ D A B) = dist B D * Real.cos (∠ B D A) := by
    have hcomm : dist A D = dist D A := dist_comm _ _
    have hcomm2 : dist A B = dist B A := dist_comm _ _
    rw [hcomm, hcomm2]
    linarith [hproj2]
  have key : 0 < Real.sin (∠ C D A) * (dist A D - dist A B * Real.cos (∠ D A B)) +
      dist A B * Real.cos (∠ C D A) * Real.sin (∠ D A B) := by
    rw [h1]
    have t1 : 0 < Real.sin (∠ C D A) * (dist B D * Real.cos (∠ B D A)) :=
      mul_pos hsinδd (mul_pos hf hcos1)
    have t2 : 0 < dist A B * Real.cos (∠ C D A) * Real.sin (∠ D A B) :=
      mul_pos (mul_pos hc hcos2) hsinαa
    linarith [t1, t2]
  have hfin : dist A D * Real.sin (∠ C D A) -
      dist A B * (Real.sin (∠ C D A) * Real.cos (∠ D A B) -
        Real.cos (∠ C D A) * Real.sin (∠ D A B)) =
      Real.sin (∠ C D A) * (dist A D - dist A B * Real.cos (∠ D A B)) +
        dist A B * Real.cos (∠ C D A) * Real.sin (∠ D A B) := by ring
  rw [hfin]
  exact key

/-! ### The sweep: valid transversals and shortest paths -/

/-- The transversal direction of the net (constant in case (b)). -/
@[reducible]
noncomputable def uT (A B C D : Pt) : Pt2 := netA2 A B C D - netA0 A B C

/-- The transversal base point at parameter `t` (the image of `X` in face `ABC`). -/
@[reducible]
noncomputable def X0T (A B C D : Pt) (t : ℝ) : Pt2 := netA0 A B C + t • (netB0 B C - netA0 A B C)

/-- The second image of `X` (in unfolded face `ABD`) in case (b). -/
@[reducible]
noncomputable def X3T (A B C D : Pt) (t : ℝ) : Pt2 := X0T A B C D t + uT A B C D

/-- The parameter `t` is valid: the straight transversal at `t` crosses all
three hinges in their interiors. -/
def ValidTransversal (A B C D : Pt) (t : ℝ) : Prop :=
  0 < t ∧ t < 1 ∧
    crss (uT A B C D) (netB0 B C - X0T A B C D t) *
      crss (uT A B C D) (netC0 - X0T A B C D t) < 0 ∧
    crss (uT A B C D) (netC0 - X0T A B C D t) *
      crss (uT A B C D) (netD1 B C D - X0T A B C D t) < 0 ∧
    crss (uT A B C D) (netD1 B C D - X0T A B C D t) *
      crss (uT A B C D) (netA2 A B C D - X0T A B C D t) < 0

/-- The signed area along the transversal is affine in `t`. -/
lemma crss_uT_X0T (A B C D : Pt) (t : ℝ) :
    crss (uT A B C D) (X0T A B C D t) =
      crss (uT A B C D) (netA0 A B C) +
        t * (crss (uT A B C D) (netB0 B C) - crss (uT A B C D) (netA0 A B C)) := by
  rw [X0T, crss_add_right, crss_smul_right, crss_sub_right]

/-- There is a nonempty interval of valid parameters. -/
lemma exists_valid_transversal_interval (A B C D : Pt)
    (htet : AffineIndependent ℝ ![A, B, C, D])
    (hABC : AcuteTriangle A B C) (hBCD : AcuteTriangle B C D)
    (hACD : AcuteTriangle A C D) (hABD : AcuteTriangle A B D)
    (hcond : ∠ D A B + ∠ B C D = ∠ C D A + ∠ A B C) :
    ∃ tlo thi : ℝ, 0 ≤ tlo ∧ tlo < thi ∧ thi ≤ 1 ∧
      ∀ t : ℝ, t ∈ Set.Ioo tlo thi → ValidTransversal A B C D t := by
  have h1 := trihedral_at_C A B C D htet
  set cA0 := crss (uT A B C D) (netA0 A B C) with hcA0
  set cB0 := crss (uT A B C D) (netB0 B C) with hcB0
  set cD1 := crss (uT A B C D) (netD1 B C D) with hcD1
  have hF1 : cA0 < cB0 := crss_u_netA0_lt_crss_u_netB0 A B C D htet hABC hBCD hACD h1.1
  have hF2 : cA0 < cD1 := crss_u_netA0_lt_crss_u_netD1 A B C D htet hABC hBCD hACD h1.2
  have hpos1 : 0 < cB0 := crss_u_netB0_pos A B C D htet hBCD hACD
  have hpos2 : 0 < cD1 := crss_u_netD1_pos A B C D htet hBCD hABC
  set m := max 0 cA0
  set M := min cB0 cD1
  have hmM : m < M := by
    simp only [m, M, max_lt_iff, lt_min_iff]
    exact ⟨⟨hpos1, hF1⟩, ⟨hpos2, hF2⟩⟩
  have hslope : 0 < cB0 - cA0 := by linarith [hF1]
  refine ⟨(m - cA0) / (cB0 - cA0), (M - cA0) / (cB0 - cA0), ?_, ?_, ?_, ?_⟩
  · apply div_nonneg _ hslope.le
    have : cA0 ≤ m := le_max_right 0 cA0
    simp only [sub_nonneg]
    exact this
  · apply div_lt_div_of_pos_right (sub_lt_sub_right hmM cA0) hslope
  · rw [div_le_one hslope]
    have : M ≤ cB0 := min_le_left cB0 cD1
    simp only [sub_le_iff_le_add]
    linarith [this]
  · intro t ht
    have hφ : crss (uT A B C D) (X0T A B C D t) = cA0 + t * (cB0 - cA0) := crss_uT_X0T A B C D t
    have htm : m - cA0 < t * (cB0 - cA0) := by
      have h := mul_lt_mul_of_pos_right ht.1 hslope
      rwa [div_mul_cancel₀ _ hslope.ne'] at h
    have htM : t * (cB0 - cA0) < M - cA0 := by
      have h := mul_lt_mul_of_pos_right ht.2 hslope
      rwa [div_mul_cancel₀ _ hslope.ne'] at h
    have hφ0 : 0 < crss (uT A B C D) (X0T A B C D t) := by
      have h2 : 0 ≤ m := le_max_left 0 cA0
      rw [hφ]
      linarith [htm, h2]
    have hφcB0 : crss (uT A B C D) (X0T A B C D t) < cB0 := by
      have h2 : M ≤ cB0 := min_le_left cB0 cD1
      rw [hφ] at *
      linarith [htM, h2]
    have hφcD1 : crss (uT A B C D) (X0T A B C D t) < cD1 := by
      have h2 : M ≤ cD1 := min_le_right cB0 cD1
      rw [hφ] at *
      linarith [htM, h2]
    have hφcA0 : cA0 < crss (uT A B C D) (X0T A B C D t) := by
      have h2 : cA0 ≤ m := le_max_right 0 cA0
      rw [hφ] at *
      linarith [htm, h2]
    have ht0 : 0 < t := by
      have htlo0 : 0 ≤ (m - cA0) / (cB0 - cA0) := by
        apply div_nonneg _ hslope.le
        have h2 : cA0 ≤ m := le_max_right 0 cA0
        simp only [sub_nonneg]
        exact h2
      linarith [ht.1, htlo0]
    have ht1 : t < 1 := by
      have hthi1 : (M - cA0) / (cB0 - cA0) ≤ 1 := by
        rw [div_le_one hslope]
        have h2 : M ≤ cB0 := min_le_left cB0 cD1
        simp only [sub_le_iff_le_add]
        linarith [h2]
      linarith [ht.2, hthi1]
    refine ⟨ht0, ht1, ?_, ?_, ?_⟩
    · have hsub1 : crss (uT A B C D) (netB0 B C - X0T A B C D t) =
          cB0 - crss (uT A B C D) (X0T A B C D t) := by
        rw [crss_sub_right]
      have hsub2 : crss (uT A B C D) (netC0 - X0T A B C D t) =
          -crss (uT A B C D) (X0T A B C D t) := by
        rw [netC0, crss_sub_right, crss_zero_right]; ring
      rw [hsub1, hsub2]
      exact mul_neg_of_pos_of_neg (by linarith [hφcB0]) (by linarith [hφ0])
    · have hsub1 : crss (uT A B C D) (netC0 - X0T A B C D t) =
          -crss (uT A B C D) (X0T A B C D t) := by
        rw [netC0, crss_sub_right, crss_zero_right]; ring
      have hsub2 : crss (uT A B C D) (netD1 B C D - X0T A B C D t) =
          cD1 - crss (uT A B C D) (X0T A B C D t) := by
        rw [crss_sub_right]
      rw [hsub1, hsub2]
      exact mul_neg_of_neg_of_pos (by linarith [hφ0]) (by linarith [hφcD1])
    · have hsub1 : crss (uT A B C D) (netD1 B C D - X0T A B C D t) =
          cD1 - crss (uT A B C D) (X0T A B C D t) := by
        rw [crss_sub_right]
      have hsub2 : crss (uT A B C D) (netA2 A B C D - X0T A B C D t) =
          cA0 - crss (uT A B C D) (X0T A B C D t) := by
        have hA2 : crss (uT A B C D) (netA2 A B C D) = cA0 := by
          rw [show netA2 A B C D = netA0 A B C + uT A B C D from by rw [uT]; module,
            crss_add_right, crss_self, add_zero]
        rw [crss_sub_right, hA2]
      rw [hsub1, hsub2]
      exact mul_neg_of_pos_of_neg (by linarith [hφcD1]) (by linarith [hφcA0])


/-- Distance between two points on the same line in the plane. -/
lemma dist_param {X₀ u : Pt2} (a b : ℝ) :
    dist (X₀ + a • u) (X₀ + b • u) = |b - a| * ‖u‖ := by
  rw [dist_eq_norm]
  have e : X₀ + a • u - (X₀ + b • u) = (a - b) • u := by module
  rw [e, norm_smul, Real.norm_eq_abs, show a - b = -(b - a) from by ring, abs_neg]

/-- Distance from a point to a point further along the same line. -/
lemma dist_param_left {X₀ u : Pt2} (r : ℝ) : dist X₀ (X₀ + r • u) = |r| * ‖u‖ := by
  rw [dist_eq_norm]
  have e : X₀ - (X₀ + r • u) = -(r • u) := by module
  rw [e, norm_neg, norm_smul, Real.norm_eq_abs]

/-- If an affine function is positive at `p`, negative at `q`, and zero at `r`,
then `r` lies between `p` and `q`. -/
lemma lt_of_affine_pos_neg {p q r s₀ k : ℝ} (hpq : p < q)
    (hp : 0 < s₀ + p * k) (hq : s₀ + q * k < 0) (hr : s₀ + r * k = 0) : p < r ∧ r < q := by
  have h2 : (q - p) * k < 0 := by linarith [hp, hq]
  have hk : k < 0 := by
    rcases mul_neg_iff.1 h2 with h | h
    · exact h.2
    · linarith [h.1, hpq]
  have h3 : (p - r) * k > 0 := by linarith [hp, hr]
  have h4 : (q - r) * k < 0 := by linarith [hq, hr]
  constructor
  · rcases mul_pos_iff.1 h3 with h | h
    · linarith [h.2, hk]
    · linarith [h.1]
  · rcases mul_neg_iff.1 h4 with h | h
    · linarith [h.1]
    · linarith [h.2, hk]

/-- If an affine function is negative at `p`, positive at `q`, and zero at `r`,
then `r` lies between `p` and `q`. -/
lemma lt_of_affine_neg_pos {p q r s₀ k : ℝ} (hpq : p < q)
    (hp : s₀ + p * k < 0) (hq : 0 < s₀ + q * k) (hr : s₀ + r * k = 0) : p < r ∧ r < q := by
  have h2 : (q - p) * k > 0 := by linarith [hp, hq]
  have hk : 0 < k := by
    rcases mul_pos_iff.1 h2 with h | h
    · exact h.2
    · linarith [h.1, hpq]
  have h3 : (p - r) * k < 0 := by linarith [hp, hr]
  have h4 : (q - r) * k > 0 := by linarith [hq, hr]
  constructor
  · rcases mul_neg_iff.1 h3 with h | h
    · linarith [h.2, hk]
    · linarith [h.1]
  · rcases mul_pos_iff.1 h4 with h | h
    · linarith [h.1]
    · linarith [h.2, hk]

/-- The y-coordinate of the transversal base point. -/
lemma X0T_one (A B C D : Pt) (t : ℝ) :
    (X0T A B C D t) 1 = (1 - t) * dist A C * Real.sin (∠ B C A) := by
  rw [X0T, add_one, smul_one, sub_one, netA0, netB0, smul_one, smul_one, e_one, e_one,
    Real.sin_zero]
  ring

/-- The y-coordinate of the transversal direction. -/
lemma uT_one (A B C D : Pt) :
    (uT A B C D) 1 = -(dist A C * (Real.sin (∠ B C D + ∠ D C A) + Real.sin (∠ B C A))) := by
  rw [uT, sub_one, netA2, netA0, smul_one, smul_one, e_one, e_one, Real.sin_neg]
  ring

/-- The y-coordinate of the second image. -/
lemma X3T_one (A B C D : Pt) (t : ℝ) :
    (X3T A B C D t) 1 = -(dist A C * Real.sin (∠ B C D + ∠ D C A) +
      t * dist A C * Real.sin (∠ B C A)) := by
  rw [X3T, add_one, X0T_one, uT_one]
  ring

/-- `crss netD1 netB0` in terms of the tetrahedron data. -/
lemma crss_netD1_netB0 (A B C D : Pt) :
    crss (netD1 B C D) (netB0 B C) = dist C D * dist B C * Real.sin (∠ B C D) := by
  rw [netD1, netB0, crss_smul_left, crss_smul_right, crss_e_e,
    show (0:ℝ) - -(∠ B C D) = ∠ B C D from by ring]
  ring

/-- `crss netD1 netA0` in terms of the tetrahedron data. -/
lemma crss_netD1_netA0 (A B C D : Pt) :
    crss (netD1 B C D) (netA0 A B C) = dist C D * dist A C * Real.sin (∠ B C A + ∠ B C D) := by
  rw [netD1, netA0, crss_smul_left, crss_smul_right, crss_e_e,
    show (∠ B C A) - -(∠ B C D) = ∠ B C A + ∠ B C D from by ring]
  ring

/-- `crss netD1 netA2` in terms of the tetrahedron data. -/
lemma crss_netD1_netA2 (A B C D : Pt) :
    crss (netD1 B C D) (netA2 A B C D) = -dist C D * dist A C * Real.sin (∠ D C A) := by
  rw [netD1, netA2, crss_smul_left, crss_smul_right, crss_e_e,
    show -(∠ B C D + ∠ D C A) - -(∠ B C D) = -(∠ D C A) from by ring, Real.sin_neg]
  ring

/-- `crss (netA2 - netD1) netD1` in terms of the tetrahedron data. -/
lemma crss_netA2_sub_netD1_netD1 (A B C D : Pt) :
    crss (netA2 A B C D - netD1 B C D) (netD1 B C D) =
      dist A C * dist C D * Real.sin (∠ D C A) := by
  rw [crss_sub_left, crss_self, sub_zero, netA2, netD1, crss_smul_left, crss_smul_right, crss_e_e,
    show -(∠ B C D) - -(∠ B C D + ∠ D C A) = ∠ D C A from by ring]
  ring

/-- A valid transversal gives rise to an admissible path of minimal length. -/
lemma path_of_valid_transversal (A B C D : Pt) (htet : AffineIndependent ℝ ![A, B, C, D])
    (hABC : AcuteTriangle A B C) (hBCD : AcuteTriangle B C D)
    (hACD : AcuteTriangle A C D) (hABD : AcuteTriangle A B D)
    (hcond : ∠ D A B + ∠ B C D = ∠ C D A + ∠ A B C)
    {t : ℝ} (hv : ValidTransversal A B C D t) :
    ∃ Y Z T : Pt, IsPath A B C D ((1 - t) • A + t • B) Y Z T ∧
      pathLength ((1 - t) • A + t • B) Y Z T = minLength A B C D := by
  obtain ⟨ht0, ht1, hY, hZ, hT⟩ := hv
  set u := uT A B C D with hu_def
  set X₀ := X0T A B C D t with hX0_def
  set X₃ := X0T A B C D t + uT A B C D with hX3_def
  have hu : u ≠ 0 := u_ne_zero A B C D htet hBCD hACD
  have hAC : A ≠ C := by have h := tet_ne htet (show (0 : Fin 4) ≠ 2 by decide); simpa using h
  have hCD : C ≠ D := by have h := tet_ne htet (show (2 : Fin 4) ≠ 3 by decide); simpa using h
  have hBC : B ≠ C := by have h := tet_ne htet (show (1 : Fin 4) ≠ 2 by decide); simpa using h
  have hb : 0 < dist A C := dist_pos.mpr hAC
  have hd1 : 0 < dist C D := dist_pos.mpr hCD
  have ha : 0 < dist B C := dist_pos.mpr hBC
  -- the three crossings
  obtain ⟨Y, hY1, rY, hrY⟩ := exists_mem_openSegment_and_eq_add_smul_of_crss hY
  obtain ⟨Z, hZ1, rZ, hrZ⟩ := exists_mem_openSegment_and_eq_add_smul_of_crss hZ
  obtain ⟨T, hT1, rT, hrT⟩ := exists_mem_openSegment_and_eq_add_smul_of_crss hT
  -- coefficients of the crossings on their hinges
  rw [openSegment_eq_image₂] at hY1 hZ1 hT1
  obtain ⟨⟨y1, y2⟩, ⟨hy1, hy2, hy12⟩, hYe⟩ := hY1
  obtain ⟨⟨z1, z2⟩, ⟨hz1, hz2, hz12⟩, hZe⟩ := hZ1
  obtain ⟨⟨t1, t2⟩, ⟨ht1', ht2', ht12⟩, hTe⟩ := hT1
  have hYe2 : y1 • netB0 B C + y2 • netC0 = Y := hYe
  have hZe2 : z1 • netC0 + z2 • netD1 B C D = Z := hZe
  have hTe2 : t1 • netD1 B C D + t2 • netA2 A B C D = T := hTe
  have hy1' : 0 < y1 := hy1
  have hy2' : 0 < y2 := hy2
  have hy12' : y1 + y2 = 1 := hy12
  have hz1' : 0 < z1 := hz1
  have hz2' : 0 < z2 := hz2
  have hz12' : z1 + z2 = 1 := hz12
  have ht1'' : 0 < t1 := ht1'
  have ht2'' : 0 < t2 := ht2'
  have ht12' : t1 + t2 = 1 := ht12
  -- y-coordinates for the first crossing's parameter
  have hX0y : 0 < (X₀) 1 := by
    rw [hX0_def, X0T_one]
    have hsin := by simpa using sin_pos_of_tet A B C D htet 1 2 0 (by decide) (by decide) (by decide)
    have h2 : 0 < 1 - t := by linarith [ht1]
    positivity
  have hX3y : (X₃) 1 < 0 := by
    rw [hX3_def, X3T_one]
    have hsin1 : 0 < Real.sin (∠ B C D + ∠ D C A) := by
      apply Real.sin_pos_of_pos_of_lt_pi
      · have h1 := by simpa using angle_pos_of_tet A B C D htet 1 2 3 (by decide) (by decide) (by decide)
        have h2 := by simpa using angle_pos_of_tet A B C D htet 3 2 0 (by decide) (by decide) (by decide)
        linarith
      · have h3 : ∠ B C D < π / 2 := hBCD.1
        have h5 : ∠ D C A < π / 2 := by rw [angle_comm D C A]; exact hACD.1
        have hpi := Real.pi_pos
        linarith
    have hsin2 := by simpa using sin_pos_of_tet A B C D htet 1 2 0 (by decide) (by decide) (by decide)
    have t1 : 0 < dist A C * Real.sin (∠ B C D + ∠ D C A) := mul_pos hb hsin1
    have t2 : 0 < t * (dist A C * Real.sin (∠ B C A)) := mul_pos ht0 (mul_pos hb hsin2)
    linarith [t1, t2]
  have hYy : (Y) 1 = 0 := by
    rw [← hYe]
    simp [netB0, netC0, e_one]
  have h1 : (X₀) 1 + rY * (u) 1 = 0 := by
    have h2 : (Y) 1 = (X₀) 1 + rY * (u) 1 := by rw [hrY, add_one, smul_one]
    linarith [hYy, h2]
  have hu1 : (u) 1 < 0 := by
    have h2 : (X₃) 1 = (X₀) 1 + (u) 1 := by rw [hX3_def, add_one]
    linarith [hX3y, hX0y, h2]
  have hrY_eq : rY = (X₀) 1 / (-(u) 1) := by
    have h3 : -(u) 1 ≠ 0 := by linarith [hu1]
    rw [eq_div_iff h3]
    linarith [h1]
  have hrY01 : 0 < rY ∧ rY < 1 := by
    have h3 : 0 < -(u) 1 := by linarith [hu1]
    rw [hrY_eq]
    constructor
    · exact div_pos hX0y h3
    · rw [div_lt_one h3]
      have h4 : (X₃) 1 = (X₀) 1 + (u) 1 := by rw [hX3_def, add_one]
      linarith [hX3y, h4]
  -- the order at the second hinge
  have hs2Y : 0 < crss (netD1 B C D) Y := by
    have hsin := by simpa using sin_pos_of_tet A B C D htet 1 2 3 (by decide) (by decide) (by decide)
    have heq : crss (netD1 B C D) Y = y1 * (dist C D * (dist B C * Real.sin (∠ B C D))) := by
      rw [← hYe2, crss_add_right, crss_smul_right, crss_smul_right, crss_netD1_netB0 A B C D, netC0,
        crss_zero_right]
      ring
    rw [heq]
    exact mul_pos hy1' (mul_pos hd1 (mul_pos ha hsin))
  have hs21 : crss (netD1 B C D) X₃ < 0 := by
    have hstar := net_ineq_aux A B C D htet hABC hBCD hACD hABD hcond
    have hsin1 := by simpa using sin_pos_of_tet A B C D htet 3 2 0 (by decide) (by decide) (by decide)
    have hsin2 : 0 < Real.sin (∠ B C A + ∠ B C D) := by
      apply Real.sin_pos_of_pos_of_lt_pi
      · have h1 := by simpa using angle_pos_of_tet A B C D htet 1 2 0 (by decide) (by decide) (by decide)
        have h2 := by simpa using angle_pos_of_tet A B C D htet 1 2 3 (by decide) (by decide) (by decide)
        linarith
      · have h3 : ∠ B C A < π / 2 := hABC.2.1
        have h4 : ∠ B C D < π / 2 := hBCD.1
        have hpi := Real.pi_pos
        linarith
    have hkey : 0 < dist A C * Real.sin (∠ D C A) +
        t * (dist A C * Real.sin (∠ B C A + ∠ B C D) - dist B C * Real.sin (∠ B C D)) := by
      by_cases hcase : 0 ≤ dist A C * Real.sin (∠ B C A + ∠ B C D) - dist B C * Real.sin (∠ B C D)
      · nlinarith [hb, hsin1]
      · push Not at hcase
        have h2 : t * (dist A C * Real.sin (∠ B C A + ∠ B C D) - dist B C * Real.sin (∠ B C D)) >
            dist A C * Real.sin (∠ B C A + ∠ B C D) - dist B C * Real.sin (∠ B C D) := by
          have h3 : 0 < (t - 1) *
              (dist A C * Real.sin (∠ B C A + ∠ B C D) - dist B C * Real.sin (∠ B C D)) :=
            mul_pos_of_neg_of_neg (by linarith [ht1]) hcase
          linarith [h3]
        linarith [h2, hstar]
    have hX3u : crss (netD1 B C D) X₃ =
        -dist C D * (dist A C * Real.sin (∠ D C A) +
          t * (dist A C * Real.sin (∠ B C A + ∠ B C D) - dist B C * Real.sin (∠ B C D))) := by
      rw [hX3_def, crss_add_right, X0T, uT, crss_add_right, crss_smul_right, crss_sub_right,
        crss_sub_right, crss_netD1_netB0 A B C D, crss_netD1_netA0, crss_netD1_netA2]
      ring
    rw [hX3u]
    exact mul_neg_of_neg_of_pos (by linarith [hd1]) hkey
  have hs2Z : crss (netD1 B C D) Z = 0 := by
    rw [← hZe2, crss_add_right, crss_smul_right, crss_smul_right, netC0, crss_zero_right,
      crss_self]
    simp
  have hs2Y_eq : crss (netD1 B C D) Y = crss (netD1 B C D) X₀ + rY * crss (netD1 B C D) u := by
    rw [hrY, crss_add_right, crss_smul_right]
  have hs21_eq : crss (netD1 B C D) X₃ = crss (netD1 B C D) X₀ + 1 * crss (netD1 B C D) u := by
    rw [hX3_def, crss_add_right]
    ring
  have hs2Z_eq : crss (netD1 B C D) Z = crss (netD1 B C D) X₀ + rZ * crss (netD1 B C D) u := by
    rw [hrZ, crss_add_right, crss_smul_right]
  have hrYZ : rY < rZ ∧ rZ < 1 := by
    rw [hs2Y_eq] at hs2Y
    rw [hs21_eq] at hs21
    rw [hs2Z_eq] at hs2Z
    exact lt_of_affine_pos_neg hrY01.2 hs2Y hs21 hs2Z
  -- the order at the third hinge
  have hs3Z : crss (netA2 A B C D - netD1 B C D) (Z - netD1 B C D) < 0 := by
    have hsin := by simpa using sin_pos_of_tet A B C D htet 3 2 0 (by decide) (by decide) (by decide)
    have hde : Z - netD1 B C D = (z2 - 1) • netD1 B C D := by
      rw [← hZe2, netC0]
      module
    rw [hde, crss_smul_right, crss_netA2_sub_netD1_netD1]
    have h2 : z2 - 1 < 0 := by linarith [hz12, hz1]
    exact mul_neg_of_neg_of_pos h2 (mul_pos (mul_pos hb hd1) hsin)
  have hs3T : 0 < crss (netA2 A B C D - netD1 B C D) (X₃ - netD1 B C D) := by
    have hpar : netB3 A B C D - netA2 A B C D = netB0 B C - netA0 A B C := by
      have hα : 0 < ∠ D A B := by simpa using angle_pos_of_tet A B C D htet 3 0 1 (by decide) (by decide) (by decide)
      have hβ : 0 < ∠ A B C := by simpa using angle_pos_of_tet A B C D htet 0 1 2 (by decide) (by decide) (by decide)
      have hγ : 0 < ∠ B C D := by simpa using angle_pos_of_tet A B C D htet 1 2 3 (by decide) (by decide) (by decide)
      have hδ : 0 < ∠ C D A := by simpa using angle_pos_of_tet A B C D htet 2 3 0 (by decide) (by decide) (by decide)
      exact (net_edge_vec_eq_iff A B C D htet hα hβ hγ hδ hABD.2.2 hABC.1 hBCD.1 hACD.2.1).2 hcond
    have hsin := by simpa using sin_pos_of_tet A B C D htet 3 0 1 (by decide) (by decide) (by decide)
    have hAD : A ≠ D := by have h := tet_ne htet (show (0 : Fin 4) ≠ 3 by decide); simpa using h
    have hAB : A ≠ B := by have h := tet_ne htet (show (0 : Fin 4) ≠ 1 by decide); simpa using h
    have he : 0 < dist A D := dist_pos.mpr hAD
    have hc : 0 < dist A B := dist_pos.mpr hAB
    have hX3e : X₃ - netD1 B C D = netA2 A B C D - netD1 B C D + t • (netB3 A B C D - netA2 A B C D) := by
      rw [hX3_def, X0T, uT, ← hpar]
      module
    rw [hX3e, crss_add_right, crss_self, zero_add, crss_smul_right, netB3_sub_netA2,
      netA2_sub_netD1 A B C D htet, crss_smul_left, crss_smul_right, crss_e_e,
      show (∠ C D A - ∠ B C D - ∠ D A B) - (π - ∠ B C D + ∠ C D A) = -(π + ∠ D A B) from by ring,
      Real.sin_neg, Real.sin_add, Real.sin_pi, Real.cos_pi]
    have t1 : 0 < t * (dist A D * (dist A B * Real.sin (∠ D A B))) :=
      mul_pos ht0 (mul_pos he (mul_pos hc hsin))
    convert t1 using 1
    ring
  have hs3Z_eq : crss (netA2 A B C D - netD1 B C D) (Z - netD1 B C D) =
      crss (netA2 A B C D - netD1 B C D) (X₀ - netD1 B C D) +
        rZ * crss (netA2 A B C D - netD1 B C D) u := by
    rw [hrZ, crss_sub_right, crss_sub_right, crss_add_right, crss_smul_right]
    ring
  have hs3T_eq : crss (netA2 A B C D - netD1 B C D) (X₃ - netD1 B C D) =
      crss (netA2 A B C D - netD1 B C D) (X₀ - netD1 B C D) +
        1 * crss (netA2 A B C D - netD1 B C D) u := by
    rw [hX3_def, crss_sub_right, crss_sub_right, crss_add_right]
    ring
  have hs3T'_eq : crss (netA2 A B C D - netD1 B C D) (T - netD1 B C D) =
      crss (netA2 A B C D - netD1 B C D) (X₀ - netD1 B C D) +
        rT * crss (netA2 A B C D - netD1 B C D) u := by
    rw [hrT, crss_sub_right, crss_sub_right, crss_add_right, crss_smul_right]
    ring
  have hs3T' : crss (netA2 A B C D - netD1 B C D) (T - netD1 B C D) = 0 := by
    have hde : T - netD1 B C D = t2 • (netA2 A B C D - netD1 B C D) := by
      have ht2e : t2 = 1 - t1 := by linarith [ht12']
      rw [← hTe2, ht2e]
      module
    rw [hde, crss_smul_right, crss_self]
    simp
  have hrZT : rZ < rT ∧ rT < 1 := by
    rw [hs3Z_eq] at hs3Z
    rw [hs3T_eq] at hs3T
    rw [hs3T'_eq] at hs3T'
    exact lt_of_affine_neg_pos hrYZ.2 hs3Z hs3T hs3T'
  -- the chain of distances
  have hchain : dist X₀ Y + dist Y Z + dist Z T + dist T X₃ = dist X₀ X₃ := by
    have e1 : dist X₀ Y = rY * ‖u‖ := by
      rw [hrY, dist_param_left, abs_of_pos hrY01.1]
    have e2 : dist Y Z = (rZ - rY) * ‖u‖ := by
      rw [hrY, hrZ, dist_param, abs_of_pos (sub_pos.mpr hrYZ.1)]
    have e3 : dist Z T = (rT - rZ) * ‖u‖ := by
      rw [hrZ, hrT, dist_param, abs_of_pos (sub_pos.mpr hrZT.1)]
    have e4 : dist T X₃ = (1 - rT) * ‖u‖ := by
      have ee : X₃ = X₀ + (1:ℝ) • u := by rw [hX3_def, one_smul]
      rw [hrT, ee, dist_param, abs_of_pos (by linarith [hrZT.2] : (0:ℝ) < 1 - rT)]
    have e5 : dist X₀ X₃ = ‖u‖ := by
      have ee : X₃ = X₀ + (1:ℝ) • u := by rw [hX3_def, one_smul]
      rw [ee, dist_param_left, abs_of_pos one_pos, one_mul]
    rw [e1, e2, e3, e4, e5]
    ring
  -- the admissible path
  have hx2 : 0 < 1 - t := by linarith [ht1]
  refine ⟨y1 • B + y2 • C, z1 • C + z2 • D, t1 • D + t2 • A, ?_, ?_⟩
  · have hpath : IsPath A B C D ((1 - t) • A + t • B) (y1 • B + y2 • C) (z1 • C + z2 • D) (t1 • D + t2 • A) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [openSegment_eq_image₂]
        exact ⟨(1 - t, t), ⟨hx2, ht0, by ring⟩, rfl⟩
      · rw [openSegment_eq_image₂]
        exact ⟨(y1, y2), ⟨hy1, hy2, hy12⟩, rfl⟩
      · rw [openSegment_eq_image₂]
        exact ⟨(z1, z2), ⟨hz1, hz2, hz12⟩, rfl⟩
      · rw [openSegment_eq_image₂]
        exact ⟨(t1, t2), ⟨ht1', ht2', ht12⟩, rfl⟩
    exact hpath
  · -- the image point equalities
    have hpar : netB3 A B C D - netA2 A B C D = netB0 B C - netA0 A B C := by
      have hα : 0 < ∠ D A B := by simpa using angle_pos_of_tet A B C D htet 3 0 1 (by decide) (by decide) (by decide)
      have hβ : 0 < ∠ A B C := by simpa using angle_pos_of_tet A B C D htet 0 1 2 (by decide) (by decide) (by decide)
      have hγ : 0 < ∠ B C D := by simpa using angle_pos_of_tet A B C D htet 1 2 3 (by decide) (by decide) (by decide)
      have hδ : 0 < ∠ C D A := by simpa using angle_pos_of_tet A B C D htet 2 3 0 (by decide) (by decide) (by decide)
      exact (net_edge_vec_eq_iff A B C D htet hα hβ hγ hδ hABD.2.2 hABC.1 hBCD.1 hACD.2.1).2 hcond
    have himgX : imgX A B C (1 - t) = X₀ := by
      rw [imgX, hX0_def, X0T]
      module
    have himgY : imgY B C y1 = Y := by
      rw [imgY, ← hYe2, netC0]
      module
    have himgZ : imgZ B C D z1 = Z := by
      have hz2e : z2 = 1 - z1 := by linarith [hz12']
      rw [imgZ, ← hZe2, hz2e]
      module
    have himgT : imgT A B C D t1 = T := by
      have ht2e : t2 = 1 - t1 := by linarith [ht12']
      rw [imgT, ← hTe2, ht2e]
      module
    have himgX3 : imgX3 A B C D t = X₃ := by
      rw [imgX3, hX3_def, X0T, uT, ← hpar]
      module
    have h1 := dist_imgX_imgY A B C D htet hx2 ht0 (by ring : (1 - t) + t = 1) rfl
      hy1' hy2' hy12' rfl
    have h2 := dist_imgY_imgZ A B C D htet hy1' hy2' hy12' rfl hz1' hz2' hz12' rfl
    have h3 := dist_imgZ_imgT A B C D htet hz1' hz2' hz12' rfl ht1'' ht2'' ht12' rfl
    have h4 := dist_imgT_imgX3 A B C D htet ht1'' ht2'' ht12' rfl hx2 ht0 (by ring : (1 - t) + t = 1) rfl
    rw [pathLength, ← h1, ← h2, ← h3, ← h4, himgX, himgY, himgZ, himgT, himgX3, hchain]
    have h5 := dist_imgX_imgX3_of_condition A B C D htet hcond
      (by simpa using angle_pos_of_tet A B C D htet 3 0 1 (by decide) (by decide) (by decide))
      (by simpa using angle_pos_of_tet A B C D htet 0 1 2 (by decide) (by decide) (by decide))
      (by simpa using angle_pos_of_tet A B C D htet 1 2 3 (by decide) (by decide) (by decide))
      (by simpa using angle_pos_of_tet A B C D htet 2 3 0 (by decide) (by decide) (by decide))
      hABD.2.2 hABC.1 hBCD.1 hACD.2.1 (by ring : (1 - t) + t = 1)
    rw [himgX, himgX3] at h5
    rw [h5]
    exact (minLength_eq_dist_netA0_netA2 A B C D htet hcond hABC.2.1 hBCD.1
      (by rw [angle_comm D C A]; exact hACD.1)).symm

/-- Part (b), attainability: infinitely many shortest paths. -/
lemma shortest_paths_infinite (A B C D : Pt) (htet : AffineIndependent ℝ ![A, B, C, D])
    (hABC : AcuteTriangle A B C) (hBCD : AcuteTriangle B C D)
    (hACD : AcuteTriangle A C D) (hABD : AcuteTriangle A B D)
    (hcond : ∠ D A B + ∠ B C D = ∠ C D A + ∠ A B C) :
    Set.Infinite {p : Pt × Pt × Pt × Pt | IsPath A B C D p.1 p.2.1 p.2.2.1 p.2.2.2 ∧
      pathLength p.1 p.2.1 p.2.2.1 p.2.2.2 = minLength A B C D} := by
  obtain ⟨tlo, thi, htlo, hlt, hthi, hsub⟩ :=
    exists_valid_transversal_interval A B C D htet hABC hBCD hACD hABD hcond
  have hAB : A ≠ B := by have h := tet_ne htet (show (0 : Fin 4) ≠ 1 by decide); simpa using h
  have hinj : Set.InjOn (fun t : ℝ => (1 - t) • A + t • B) (Set.Ioo tlo thi) := by
    intro t₁ ht₁ t₂ ht₂ h
    have h4 : (t₂ - t₁) • (A - B) = 0 := by
      have h3 : (1 - t₁) • A + t₁ • B = (1 - t₂) • A + t₂ • B := h
      have e : (t₂ - t₁) • (A - B) =
          ((1 - t₁) • A + t₁ • B) - ((1 - t₂) • A + t₂ • B) := by module
      rw [e, h3, sub_self]
    have h5 : t₂ - t₁ = 0 := (smul_eq_zero.mp h4).resolve_right (sub_ne_zero.mpr hAB)
    linarith [h5]
  have himg : Set.Infinite ((fun t : ℝ => (1 - t) • A + t • B) '' Set.Ioo tlo thi) :=
    Set.Infinite.image hinj (Set.Ioo_infinite hlt)
  have hsub2 : (fun t : ℝ => (1 - t) • A + t • B) '' Set.Ioo tlo thi ⊆
      Prod.fst '' {p : Pt × Pt × Pt × Pt | IsPath A B C D p.1 p.2.1 p.2.2.1 p.2.2.2 ∧
        pathLength p.1 p.2.1 p.2.2.1 p.2.2.2 = minLength A B C D} := by
    rintro x ⟨t, ht, rfl⟩
    obtain ⟨Y, Z, T, hp, hlen⟩ :=
      path_of_valid_transversal A B C D htet hABC hBCD hACD hABD hcond (hsub t ht)
    exact ⟨((1 - t) • A + t • B, Y, Z, T), ⟨hp, hlen⟩, rfl⟩
  exact Set.Infinite.of_image Prod.fst (Set.Infinite.mono hsub2 himg)

/-! ### Calculus for the variational step (part a) -/

/-- Derivative of `t ↦ √(⟪A - P + t • d, A - P + t • d⟫)`. -/
lemma hasDerivAt_dist_line_aux (P A d : Pt2) (t : ℝ) (hne : A + t • d - P ≠ 0) :
    HasDerivAt (fun t => Real.sqrt (⟪A - P + t • d, A - P + t • d⟫))
      ((⟪A - P + t • d, d⟫ + ⟪d, A - P + t • d⟫) /
        (2 * Real.sqrt (⟪A - P + t • d, A - P + t • d⟫))) t := by
  have h1 : HasDerivAt (fun t => A - P + t • d) d t := by
    simpa using ((hasDerivAt_id t).smul_const d).const_add (A - P)
  have h2 : HasDerivAt (fun t => ⟪A - P + t • d, A - P + t • d⟫)
      (⟪A - P + t • d, d⟫ + ⟪d, A - P + t • d⟫) t :=
    HasDerivAt.inner ℝ h1 h1
  have h3 : A - P + t • d ≠ 0 := by
    have h4 : A + t • d - P = A - P + t • d := by module
    rwa [h4] at hne
  have h4 : (fun t => ⟪A - P + t • d, A - P + t • d⟫) t ≠ 0 := inner_self_ne_zero.mpr h3
  exact h2.sqrt h4

/-- Derivative of `t ↦ dist P (A + t • d)`. -/
lemma hasDerivAt_dist_line (P A d : Pt2) (t : ℝ) (hne : A + t • d - P ≠ 0) :
    HasDerivAt (fun t => dist P (A + t • d))
      (⟪A + t • d - P, d⟫ / dist P (A + t • d)) t := by
  have h := hasDerivAt_dist_line_aux P A d t hne
  have h3 : A + t • d - P = A - P + t • d := by module
  have h4 : Real.sqrt (⟪A - P + t • d, A - P + t • d⟫) = dist P (A + t • d) := by
    rw [← norm_eq_sqrt_real_inner, ← h3, dist_comm, dist_eq_norm]
  rw [← h4]
  convert h using 1
  · funext x
    have e : A + x • d - P = A - P + x • d := by module
    rw [dist_eq_norm, ← norm_eq_sqrt_real_inner,
      show P - (A + x • d) = -(A - P + x • d) from by module, norm_neg]
  · rw [real_inner_comm (A - P + t • d) d]
    have h5 : ⟪A - P + t • d, d⟫ + ⟪A - P + t • d, d⟫ = 2 * ⟪A - P + t • d, d⟫ := by ring
    rw [h5, h4, ← h3]
    have h6 : dist P (A + t • d) ≠ 0 :=
      dist_ne_zero.mpr (Ne.symm (sub_ne_zero.mp hne))
    field_simp [h6]

/-- Derivative of the sum of distances to two fixed points along a line. -/
lemma hasDerivAt_h (P Q A d : Pt2) (t : ℝ) (h1 : A + t • d - P ≠ 0) (h2 : A + t • d - Q ≠ 0) :
    HasDerivAt (fun t => dist P (A + t • d) + dist Q (A + t • d))
      (⟪A + t • d - P, d⟫ / dist P (A + t • d) +
        ⟪A + t • d - Q, d⟫ / dist Q (A + t • d)) t := by
  exact (hasDerivAt_dist_line P A d t h1).add (hasDerivAt_dist_line Q A d t h2)

/-- A function with nonzero derivative at `t₀` takes a strictly smaller value
arbitrarily close to `t₀` (on the appropriate side). -/
lemma exists_smaller_of_hasDerivAt_ne_zero {h : ℝ → ℝ} {t₀ h' : ℝ}
    (hd : HasDerivAt h h' t₀) (hne : h' ≠ 0) (δ : ℝ) (hδ : 0 < δ) :
    ∃ s, |s| < δ ∧ h (t₀ + s) < h t₀ := by
  rw [hasDerivAt_iff_tendsto_slope] at hd
  by_cases hpos : 0 < h'
  · have h1 : ∀ᶠ y in 𝓝 h', h' / 2 < y := IsOpen.mem_nhds isOpen_Ioi (half_lt_self hpos)
    have h2 : ∀ᶠ x in 𝓝[≠] t₀, h' / 2 < slope h t₀ x := hd.eventually h1
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff_ball] at h2
    obtain ⟨δ', hδ', hball⟩ := h2
    have hδm : 0 < min δ δ' := lt_min hδ hδ'
    have hle' : min δ δ' ≤ δ' := min_le_right _ _
    have hle : min δ δ' ≤ δ := min_le_left _ _
    have hne2 : t₀ - min δ δ' / 2 ≠ t₀ := by
      intro he
      exact (ne_of_gt hδm) (by linarith [he])
    have h3 := hball (t₀ - min δ δ' / 2) (by
      rw [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs,
        show t₀ - min δ δ' / 2 - t₀ = -(min δ δ' / 2) from by ring,
        abs_of_neg (by linarith [hδm])]
      linarith [hle', hδm]) (by simpa using hne2)
    rw [slope_def_field, show t₀ - min δ δ' / 2 - t₀ = -(min δ δ' / 2) from by ring] at h3
    have h5 : h (t₀ - min δ δ' / 2) - h t₀ < 0 := by
      have h6 : 0 < (h (t₀ - min δ δ' / 2) - h t₀) / (-(min δ δ' / 2)) := by linarith [h3]
      rw [div_pos_iff] at h6
      rcases h6 with h7 | h7
      · linarith [hδm]
      · exact h7.1
    refine ⟨-(min δ δ' / 2), ?_, ?_⟩
    · rw [abs_neg, abs_of_pos (by linarith [hδm] : (0:ℝ) < min δ δ' / 2)]
      linarith [hle, hδm]
    · rw [show t₀ + -(min δ δ' / 2) = t₀ - min δ δ' / 2 from by ring]
      linarith [h5]
  · have hlt : h' < 0 := by
      rcases lt_or_gt_of_ne hne with h | h
      · exact h
      · exact absurd h hpos
    have h1 : ∀ᶠ y in 𝓝 h', y < h' / 2 :=
      IsOpen.mem_nhds isOpen_Iio (show h' < h' / 2 from by linarith [hlt])
    have h2 : ∀ᶠ x in 𝓝[≠] t₀, slope h t₀ x < h' / 2 := hd.eventually h1
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff_ball] at h2
    obtain ⟨δ', hδ', hball⟩ := h2
    have hδm : 0 < min δ δ' := lt_min hδ hδ'
    have hle' : min δ δ' ≤ δ' := min_le_right _ _
    have hle : min δ δ' ≤ δ := min_le_left _ _
    have hne2 : t₀ + min δ δ' / 2 ≠ t₀ := by
      intro he
      exact (ne_of_gt hδm) (by linarith [he])
    have h3 := hball (t₀ + min δ δ' / 2) (by
      rw [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs,
        show t₀ + min δ δ' / 2 - t₀ = min δ δ' / 2 from by ring,
        abs_of_pos (by linarith [hδm])]
      linarith [hle', hδm]) (by simpa using hne2)
    rw [slope_def_field, show t₀ + min δ δ' / 2 - t₀ = min δ δ' / 2 from by ring] at h3
    have h5 : h (t₀ + min δ δ' / 2) - h t₀ < 0 := by
      have h6 : (h (t₀ + min δ δ' / 2) - h t₀) / (min δ δ' / 2) < 0 := by linarith [h3]
      rw [div_neg_iff] at h6
      rcases h6 with h7 | h7
      · linarith [hδm]
      · exact h7.1
    refine ⟨min δ δ' / 2, ?_, ?_⟩
    · rw [abs_of_pos (by linarith [hδm] : (0:ℝ) < min δ δ' / 2)]
      linarith [hle, hδm]
    · rw [show t₀ + min δ δ' / 2 = t₀ + min δ δ' / 2 from rfl]
      linarith [h5]


/-- Inner product with a vector parallel to the x-axis. -/
lemma inner_e0 (v d : Pt2) (hd1 : d 1 = 0) : ⟪v, d⟫ = (v) 0 * d 0 := by
  rw [PiLp.inner_apply, Fin.sum_univ_two, hd1, RCLike.inner_apply, RCLike.inner_apply,
    RCLike.conj_to_real, RCLike.conj_to_real]
  ring

/-- The squared norm in coordinates. -/
lemma norm_sq_e (v : Pt2) : ‖v‖ ^ 2 = (v) 0 ^ 2 + (v) 1 ^ 2 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.sq_sqrt (by positivity)]
  simp [Real.norm_eq_abs, sq_abs]

/-- If the unit vectors from `P` and `Q` toward `Y` are opposite, `Y` lies
(weakly) between `P` and `Q`. -/
lemma wbtw_of_unit_neg {P Q Y : Pt2} (hPY : P ≠ Y) (hQY : Q ≠ Y)
    (h : (dist P Y)⁻¹ • (Y - P) = -((dist Q Y)⁻¹ • (Y - Q))) : Wbtw ℝ P Y Q := by
  have hP1 : dist P Y ≠ 0 := dist_ne_zero.mpr hPY
  have hQ1 : dist Q Y ≠ 0 := dist_ne_zero.mpr hQY
  have ki : ∀ i : Fin 2, dist Q Y * ((Y) i - (P) i) = -(dist P Y * ((Y) i - (Q) i)) := by
    intro i
    have ei := congrArg (fun w : Pt2 => (w) i) h
    rw [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, PiLp.neg_apply,
      PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul] at ei
    field_simp [hP1, hQ1] at ei
    linarith [ei]
  have hsum : (0:ℝ) < dist Q Y + dist P Y := by
    have e4 : (0:ℝ) < dist Q Y := dist_pos.mpr hQY
    linarith [dist_nonneg (x := P) (y := Y)]
  -- segment membership via the defining convex combination
  refine mem_segment_iff_wbtw.1
    ⟨dist Q Y / (dist Q Y + dist P Y), dist P Y / (dist Q Y + dist P Y),
      div_nonneg dist_nonneg hsum.le, div_nonneg dist_nonneg hsum.le, ?_, ?_⟩
  · rw [← add_div]
    exact div_self hsum.ne'
  · apply PiLp.ext
    intro i
    rw [PiLp.add_apply, PiLp.smul_apply, PiLp.smul_apply, smul_eq_mul, smul_eq_mul]
    have ki2 := ki i
    field_simp [hsum.ne']
    linarith [ki2]

/-- If the derivative of the sum of distances to two fixed points vanishes at a
point of the x-axis, the point lies between the two fixed points. -/
lemma wbtw_of_deriv_eq_zero {P Q Y d : Pt2}
    (hP : (P) 1 < 0) (hQ : 0 < (Q) 1) (hd0 : d 0 ≠ 0) (hd1 : d 1 = 0)
    (hY : (Y) 1 = 0)
    (h : ⟪Y - P, d⟫ / dist P Y + ⟪Y - Q, d⟫ / dist Q Y = 0) :
    Wbtw ℝ P Y Q := by
  have hPY : P ≠ Y := by
    intro he
    rw [he] at hP
    linarith [hP, hY]
  have hQY : Q ≠ Y := by
    intro he
    rw [he] at hQ
    linarith [hQ, hY]
  have hP1 : dist P Y ≠ 0 := dist_ne_zero.mpr hPY
  have hQ1 : dist Q Y ≠ 0 := dist_ne_zero.mpr hQY
  -- cross-multiply the derivative equation
  have h2 : ⟪Y - P, d⟫ * dist Q Y = -(⟪Y - Q, d⟫ * dist P Y) := by
    have h3 : ⟪Y - P, d⟫ / dist P Y = -(⟪Y - Q, d⟫ / dist Q Y) := by linarith [h]
    rw [div_eq_iff hP1] at h3
    field_simp [hQ1] at h3 ⊢
    linarith [h3]
  rw [inner_e0 (Y - P) d hd1, inner_e0 (Y - Q) d hd1, PiLp.sub_apply, PiLp.sub_apply] at h2
  -- the 0-components of the unit vectors are opposite
  have h3 : (Y 0 - P 0) * d 0 * dist Q Y = -((Y 0 - Q 0) * d 0 * dist P Y) := by
    linarith [h2]
  have h4 : (Y 0 - P 0) * dist Q Y = -((Y 0 - Q 0) * dist P Y) := by
    apply mul_left_cancel₀ hd0
    convert h3 using 1 <;> ring
  -- unit vectors
  set u := (dist P Y)⁻¹ • (Y - P) with hu
  set v := (dist Q Y)⁻¹ • (Y - Q) with hv
  have hu0 : (u) 0 = -(v) 0 := by
    rw [hu, hv]
    simp [PiLp.smul_apply, smul_eq_mul]
    field_simp [hP1, hQ1]
    linarith [h4]
  have hnu : ‖u‖ = 1 := by
    rw [hu, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr dist_nonneg),
      ← dist_eq_norm, dist_comm Y P, inv_mul_cancel₀ hP1]
  have hnv : ‖v‖ = 1 := by
    rw [hv, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr dist_nonneg),
      ← dist_eq_norm, dist_comm Y Q, inv_mul_cancel₀ hQ1]
  have hu1 : 0 < (u) 1 := by
    rw [hu, PiLp.smul_apply, smul_eq_mul,
      show (Y - P) 1 = (0:ℝ) - P 1 from by rw [PiLp.sub_apply, hY]]
    exact mul_pos (inv_pos.mpr (dist_pos.mpr hPY)) (by linarith [hP])
  have hv1 : (v) 1 < 0 := by
    rw [hv, PiLp.smul_apply, smul_eq_mul,
      show (Y - Q) 1 = (0:ℝ) - Q 1 from by rw [PiLp.sub_apply, hY]]
    exact mul_neg_of_pos_of_neg (inv_pos.mpr (dist_pos.mpr hQY)) (by linarith [hQ])
  -- the 1-components are opposite too
  have h7 : (u) 1 = -(v) 1 := by
    have h8 : (u) 0 ^ 2 + (u) 1 ^ 2 = (v) 0 ^ 2 + (v) 1 ^ 2 := by
      have e1 := norm_sq_e u
      have e2 := norm_sq_e v
      rw [hnu] at e1
      rw [hnv] at e2
      linarith [e1, e2]
    rw [hu0] at h8
    have h9 : (u) 1 ^ 2 = (v) 1 ^ 2 := by
      have h10 : (-(v) 0) ^ 2 = (v) 0 ^ 2 := by ring
      rw [h10] at h8
      linarith [h8]
    have h11 : |(u) 1| = |(v) 1| := by
      have h12 : |(u) 1| ^ 2 = |(v) 1| ^ 2 := by
        rw [sq_abs, sq_abs]
        linarith [h9]
      exact (pow_left_inj₀ (abs_nonneg _) (abs_nonneg _) (two_ne_zero)).1 h12
    rw [abs_of_pos hu1, abs_of_neg hv1] at h11
    linarith [h11]
  -- u = -v, hence Y lies between P and Q
  have huv : u = -v := by
    apply PiLp.ext
    rw [Fin.forall_fin_two]
    exact ⟨by rw [PiLp.neg_apply]; exact hu0, by rw [PiLp.neg_apply]; exact h7⟩
  rw [hu, hv] at huv
  exact wbtw_of_unit_neg hPY hQY huv

/-- The 2D Lagrange identity: cross-product squared plus inner product squared
equals the product of the squared norms. -/
lemma crss_sq_add_inner_sq (x y : Pt2) :
    crss x y ^ 2 + ⟪x, y⟫ ^ 2 = ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
  rw [crss, norm_sq_e, norm_sq_e, PiLp.inner_apply, Fin.sum_univ_two,
    RCLike.inner_apply, RCLike.inner_apply, RCLike.conj_to_real, RCLike.conj_to_real]
  ring

/-- A vector in the plane whose inner product and cross product with a nonzero
vector both vanish is zero. -/
lemma eq_zero_of_inner_crss_eq_zero {x w : Pt2} (hx : x ≠ 0)
    (h1 : ⟪x, w⟫ = 0) (h2 : crss x w = 0) : w = 0 := by
  have h3 : (x) 0 ^ 2 + (x) 1 ^ 2 ≠ 0 := by
    have h4 : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
    rw [norm_sq_e] at h4
    exact h4
  rw [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, RCLike.inner_apply,
    RCLike.conj_to_real, RCLike.conj_to_real] at h1
  rw [crss] at h2
  have g1 : (x) 0 * (w) 0 = -((x) 1 * (w) 1) := by linarith [h1]
  have g2 : (x) 1 * (w) 0 = (x) 0 * (w) 1 := by linarith [h2]
  have e0 : ((x) 0 ^ 2 + (x) 1 ^ 2) * (w) 0 = 0 := by
    have t1 : (x) 0 * ((x) 0 * (w) 0) + (x) 1 * ((x) 1 * (w) 0) = 0 := by
      rw [g1, g2]
      ring
    have t2 : (x) 0 * ((x) 0 * (w) 0) + (x) 1 * ((x) 1 * (w) 0) =
        ((x) 0 ^ 2 + (x) 1 ^ 2) * (w) 0 := by ring
    rw [t2] at t1
    exact t1
  have e1 : ((x) 0 ^ 2 + (x) 1 ^ 2) * (w) 1 = 0 := by
    have g1' : (x) 1 * (w) 1 = -((x) 0 * (w) 0) := by linarith [h1]
    have t1 : (x) 0 * ((x) 0 * (w) 1) + (x) 1 * ((x) 1 * (w) 1) = 0 := by
      rw [← g2, g1']
      ring
    have t2 : (x) 0 * ((x) 0 * (w) 1) + (x) 1 * ((x) 1 * (w) 1) =
        ((x) 0 ^ 2 + (x) 1 ^ 2) * (w) 1 := by ring
    rw [t2] at t1
    exact t1
  have hw0 : (w) 0 = 0 := (mul_eq_zero.mp e0).resolve_left h3
  have hw1 : (w) 1 = 0 := (mul_eq_zero.mp e1).resolve_left h3
  apply PiLp.ext
  rw [Fin.forall_fin_two]
  exact ⟨hw0, hw1⟩

/-- Two vectors simultaneously "parallel" to a nonzero vector are parallel to
each other. -/
lemma crss_eq_zero_of_crss_eq_zero_and_crss_eq_zero {x y z : Pt2} (hx : x ≠ 0)
    (h1 : crss x y = 0) (h2 : crss x z = 0) : crss y z = 0 := by
  obtain ⟨r1, hr1⟩ := exists_smul_of_crss_eq_zero hx h1
  obtain ⟨r2, hr2⟩ := exists_smul_of_crss_eq_zero hx h2
  rw [hr1, hr2, crss_smul_left, crss_smul_right, crss_self, mul_zero, mul_zero]

/-- General-direction form of `wbtw_of_deriv_eq_zero`: if the derivative of the
sum of distances to two fixed points on opposite sides of a line vanishes at a
point of the line, the point lies between the two fixed points. -/
lemma wbtw_of_deriv_eq_zero_gen {P Q Y d : Pt2} (hd : d ≠ 0)
    (hsides : crss d (P - Y) * crss d (Q - Y) < 0)
    (h : ⟪Y - P, d⟫ / dist P Y + ⟪Y - Q, d⟫ / dist Q Y = 0) :
    Wbtw ℝ P Y Q := by
  have hPY : P ≠ Y := by
    intro he
    rw [he, sub_self, crss_zero_right, zero_mul] at hsides
    exact lt_irrefl _ hsides
  have hQY : Q ≠ Y := by
    intro he
    rw [he, sub_self, crss_zero_right, mul_zero] at hsides
    exact lt_irrefl _ hsides
  have hP1 : dist P Y ≠ 0 := dist_ne_zero.mpr hPY
  have hQ1 : dist Q Y ≠ 0 := dist_ne_zero.mpr hQY
  set u := (dist P Y)⁻¹ • (Y - P) with hu
  set v := (dist Q Y)⁻¹ • (Y - Q) with hv
  have hnu : ‖u‖ = 1 := by
    rw [hu, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr dist_nonneg),
      ← dist_eq_norm, dist_comm Y P, inv_mul_cancel₀ hP1]
  have hnv : ‖v‖ = 1 := by
    rw [hv, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr dist_nonneg),
      ← dist_eq_norm, dist_comm Y Q, inv_mul_cancel₀ hQ1]
  -- the inner products with `d` are opposite
  have hinner : ⟪d, u⟫ = -⟪d, v⟫ := by
    rw [real_inner_comm u d, real_inner_comm v d]
    rw [hu, hv, real_inner_smul_left, real_inner_smul_left,
      show (dist P Y)⁻¹ * ⟪Y - P, d⟫ = ⟪Y - P, d⟫ / dist P Y from by rw [div_eq_inv_mul],
      show (dist Q Y)⁻¹ * ⟪Y - Q, d⟫ = ⟪Y - Q, d⟫ / dist Q Y from by rw [div_eq_inv_mul]]
    linarith [h]
  -- the cross products with `d` have strictly opposite signs
  have hsign : crss d u * crss d v < 0 := by
    have e1 : crss d u = (dist P Y)⁻¹ * (-(crss d (P - Y))) := by
      rw [hu, crss_smul_right, show Y - P = -(P - Y) from by module, crss_neg_right]
    have e2 : crss d v = (dist Q Y)⁻¹ * (-(crss d (Q - Y))) := by
      rw [hv, crss_smul_right, show Y - Q = -(Q - Y) from by module, crss_neg_right]
    rw [e1, e2]
    have e3 : (dist P Y)⁻¹ * -(crss d (P - Y)) * ((dist Q Y)⁻¹ * -(crss d (Q - Y))) =
        ((dist P Y)⁻¹ * (dist Q Y)⁻¹) * (crss d (P - Y) * crss d (Q - Y)) := by ring
    rw [e3]
    exact mul_neg_of_pos_of_neg
      (mul_pos (inv_pos.mpr (dist_pos.mpr hPY)) (inv_pos.mpr (dist_pos.mpr hQY))) hsides
  -- hence the cross products are opposite (their squares agree by Lagrange)
  have hcrss : crss d u = -crss d v := by
    have hsq : crss d u ^ 2 = crss d v ^ 2 := by
      have L1 := crss_sq_add_inner_sq d u
      have L2 := crss_sq_add_inner_sq d v
      rw [hnu, one_pow, mul_one] at L1
      rw [hnv, one_pow, mul_one] at L2
      rw [hinner] at L1
      have hnegsq : (-⟪d, v⟫) ^ 2 = ⟪d, v⟫ ^ 2 := by ring
      rw [hnegsq] at L1
      linarith [L1, L2]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h1 | h1
    · exfalso
      rw [h1] at hsign
      exact lt_irrefl _ (lt_of_lt_of_le hsign (mul_self_nonneg _))
    · exact h1
  -- therefore u = -v
  have huv : u = -v := by
    have h2 : u + v = 0 :=
      eq_zero_of_inner_crss_eq_zero hd
        (by rw [inner_add_right, hinner]; ring)
        (by rw [crss_add_right, hcrss]; ring)
    exact add_eq_zero_iff_eq_neg.1 h2
  rw [hu, hv] at huv
  exact wbtw_of_unit_neg hPY hQY huv

/-- Weak betweenness implies the distance identity (local version of
`Wbtw.dist_add_dist`, whose home module is not imported here). -/
lemma wbtw_dist_add_dist {x y z : Pt2} (h : Wbtw ℝ x y z) :
    dist x y + dist y z = dist x z := by
  obtain ⟨a, ⟨ha0, ha1⟩, rfl⟩ := h
  rw [AffineMap.lineMap_apply_module]
  have e1 : dist x ((1 - a) • x + a • z) = a * dist x z := by
    rw [dist_eq_norm, show x - ((1 - a) • x + a • z) = a • (x - z) from by module, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg ha0, ← dist_eq_norm]
  have e2 : dist ((1 - a) • x + a • z) z = (1 - a) * dist x z := by
    rw [dist_eq_norm, show (1 - a) • x + a • z - z = (1 - a) • (x - z) from by module, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg (by linarith [ha1]), ← dist_eq_norm]
  rw [e1, e2]
  ring


/-- Distinct indices of an affinely independent family give distinct points. -/
lemma AffineIndependent.ne_of_ne_index {ι : Type*} {p : ι → Pt}
    (h : AffineIndependent ℝ p) {i j : ι} (hij : i ≠ j) : p i ≠ p j :=
  fun he => hij (h.injective he)

/-- An interior point of a non-degenerate segment differs from its left endpoint. -/
lemma ne_left_of_mem_openSegment {A B X : Pt} (hX : X ∈ openSegment ℝ A B)
    (hAB : A ≠ B) : X ≠ A := by
  intro he
  rw [he, left_mem_openSegment_iff] at hX
  exact hAB hX

/-- An interior point of a non-degenerate segment differs from its right endpoint. -/
lemma ne_right_of_mem_openSegment {A B X : Pt} (hX : X ∈ openSegment ℝ A B)
    (hAB : A ≠ B) : X ≠ B := by
  intro he
  rw [he, right_mem_openSegment_iff] at hX
  exact hAB hX

/-- The length of a closed path is nonnegative. -/
lemma pathLength_nonneg (X Y Z T : Pt) : 0 ≤ pathLength X Y Z T := by
  unfold pathLength
  positivity

/-- The midpoints of the four edges form an admissible closed path. -/
lemma midpoint_isPath (A B C D : Pt) :
    IsPath A B C D (midpoint ℝ A B) (midpoint ℝ B C) (midpoint ℝ C D)
      (midpoint ℝ D A) :=
  ⟨midpoint_mem_openSegment _ _, midpoint_mem_openSegment _ _,
   midpoint_mem_openSegment _ _, midpoint_mem_openSegment _ _⟩

set_option maxHeartbeats 800000 in
/-- Part (a): if the angle condition fails, every admissible closed path can be
shortened; hence no admissible path has minimal length. -/
theorem no_shortest_path_of_angle_ne {A B C D : Pt}
    (htet : AffineIndependent ℝ ![A, B, C, D])
    (hABC : AcuteTriangle A B C) (hBCD : AcuteTriangle B C D)
    (hACD : AcuteTriangle A C D) (hABD : AcuteTriangle A B D)
    (hang : ∠ D A B + ∠ B C D ≠ ∠ C D A + ∠ A B C)
    {X Y Z T : Pt} (hpath : IsPath A B C D X Y Z T) :
    ∃ X' Y' Z' T' : Pt, IsPath A B C D X' Y' Z' T' ∧
      pathLength X' Y' Z' T' < pathLength X Y Z T := by
  obtain ⟨hX0, hY0, hZ0, hT0⟩ := hpath
  have hXc := hX0
  have hYc := hY0
  have hZc := hZ0
  have hTc := hT0
  rw [openSegment_eq_image₂] at hXc hYc hZc hTc
  obtain ⟨⟨x1, x2⟩, ⟨hx1, hx2, hx12⟩, hXe⟩ := hXc
  obtain ⟨⟨y1, y2⟩, ⟨hy1, hy2, hy12⟩, hYe⟩ := hYc
  obtain ⟨⟨z1, z2⟩, ⟨hz1, hz2, hz12⟩, hZe⟩ := hZc
  obtain ⟨⟨t1, t2⟩, ⟨ht1, ht2, ht12⟩, hTe⟩ := hTc
  -- vertex distinctness and positive edge lengths
  have hAB : A ≠ B := by have h := tet_ne htet (show (0 : Fin 4) ≠ 1 by decide); simpa using h
  have hBC : B ≠ C := by have h := tet_ne htet (show (1 : Fin 4) ≠ 2 by decide); simpa using h
  have hCD : C ≠ D := by have h := tet_ne htet (show (2 : Fin 4) ≠ 3 by decide); simpa using h
  have hAD : A ≠ D := by have h := tet_ne htet (show (0 : Fin 4) ≠ 3 by decide); simpa using h
  have hAC : A ≠ C := by have h := tet_ne htet (show (0 : Fin 4) ≠ 2 by decide); simpa using h
  have ha : 0 < dist B C := dist_pos.mpr hBC
  have hb : 0 < dist A C := dist_pos.mpr hAC
  have hd : 0 < dist C D := dist_pos.mpr hCD
  have he : 0 < dist A D := dist_pos.mpr hAD
  have hx1' : x1 = 1 - x2 := by linarith [hx12]
  have hy2' : y2 = 1 - y1 := by linarith [hy12]
  have hz2' : z2 = 1 - z1 := by linarith [hz12]
  have ht2' : t2 = 1 - t1 := by linarith [ht12]
  -- the net images and their defining forms
  have hX0eq : imgX A B C x1 = netA0 A B C + x2 • (netB0 B C - netA0 A B C) := by
    rw [imgX, hx1']; module
  have hYpeq : imgY B C y1 = y1 • netB0 B C := by
    rw [imgY, netC0]; module
  have hZpeq : imgZ B C D z1 = z2 • netD1 B C D := by
    rw [imgZ, hz2', netC0]; module
  have hTpeq : imgT A B C D t1 = t1 • netD1 B C D + t2 • netA2 A B C D := by
    rw [imgT, ht2']; module
  have hX3eq : imgX3 A B C D x2 = netA2 A B C D + x2 • (netB3 A B C D - netA2 A B C D) := rfl
  -- the length identity
  have hLen : pathLength X Y Z T = dist (imgX A B C x1) (imgY B C y1) +
      dist (imgY B C y1) (imgZ B C D z1) + dist (imgZ B C D z1) (imgT A B C D t1) +
      dist (imgT A B C D t1) (imgX3 A B C D x2) := by
    rw [pathLength, ← dist_imgX_imgY A B C D htet hx1 hx2 hx12 hXe hy1 hy2 hy12 hYe,
      ← dist_imgY_imgZ A B C D htet hy1 hy2 hy12 hYe hz1 hz2 hz12 hZe,
      ← dist_imgZ_imgT A B C D htet hz1 hz2 hz12 hZe ht1 ht2 ht12 hTe,
      ← dist_imgT_imgX3 A B C D htet ht1 ht2 ht12 hTe hx1 hx2 hx12 hXe]
  -- y-coordinates of the images on the first hinge line (the x-axis)
  have hX0one : (imgX A B C x1) 1 = x1 * (dist A C * Real.sin (∠ B C A)) := by
    rw [imgX, add_one, smul_one, sub_one, netA0, netB0, smul_one, smul_one, e_one, e_one,
      Real.sin_zero]
    ring
  have hX0y : 0 < (imgX A B C x1) 1 := by
    rw [hX0one]
    have hsin := by simpa using sin_pos_of_tet A B C D htet 1 2 0 (by decide) (by decide) (by decide)
    exact mul_pos hx1 (mul_pos hb hsin)
  have hYpone : (imgY B C y1) 1 = 0 := by
    rw [hYpeq, smul_one, netB0, smul_one, e_one, Real.sin_zero]
    ring
  have hZpone : (imgZ B C D z1) 1 = -(z2 * dist C D * Real.sin (∠ B C D)) := by
    rw [hZpeq, smul_one, netD1, smul_one, e_one, Real.sin_neg]
    ring
  have hZpy : (imgZ B C D z1) 1 < 0 := by
    rw [hZpone]
    have hsin := by simpa using sin_pos_of_tet A B C D htet 1 2 3 (by decide) (by decide) (by decide)
    have h2 : 0 < z2 * (dist C D * Real.sin (∠ B C D)) := mul_pos hz2 (mul_pos hd hsin)
    linarith [h2]
  -- distinctness facts between images on adjacent hinges
  have hYX : imgX A B C x1 - imgY B C y1 ≠ 0 := by
    intro he
    have e := congrArg (fun w : Pt2 => (w) 1) (sub_eq_zero.mp he)
    rw [hYpone] at e
    linarith [hX0y, e]
  have hYZ : imgY B C y1 - imgZ B C D z1 ≠ 0 := by
    intro he
    have e := congrArg (fun w : Pt2 => (w) 1) (sub_eq_zero.mp he)
    rw [hYpone] at e
    linarith [hZpy, e]
  have hZT : imgZ B C D z1 ≠ imgT A B C D t1 := by
    intro he
    have h1 : crss (netA2 A B C D - netD1 B C D) (imgZ B C D z1 - netD1 B C D) =
        crss (netA2 A B C D - netD1 B C D) (imgT A B C D t1 - netD1 B C D) := by rw [he]
    have hL : imgZ B C D z1 - netD1 B C D = (z2 - 1) • netD1 B C D := by rw [hZpeq]; module
    have hR : imgT A B C D t1 - netD1 B C D = t2 • (netA2 A B C D - netD1 B C D) := by
      rw [hTpeq, ht2']; module
    rw [hL, crss_smul_right, crss_netA2_sub_netD1_netD1] at h1
    rw [hR, crss_smul_right, crss_self, mul_zero] at h1
    have hsin := by simpa using sin_pos_of_tet A B C D htet 3 2 0 (by decide) (by decide) (by decide)
    have h2 : 0 < dist A C * (dist C D * Real.sin (∠ D C A)) := mul_pos hb (mul_pos hd hsin)
    rcases mul_eq_zero.mp h1 with h4 | h4
    · linarith [hz1, h4]
    · linarith [h2, h4]
  have hTX3 : imgT A B C D t1 - imgX3 A B C D x2 ≠ 0 := by
    intro he0
    have heq : imgT A B C D t1 = imgX3 A B C D x2 := sub_eq_zero.mp he0
    have h1 : crss (netB3 A B C D - netA2 A B C D) (imgT A B C D t1 - netA2 A B C D) =
        crss (netB3 A B C D - netA2 A B C D) (imgX3 A B C D x2 - netA2 A B C D) := by rw [heq]
    have hL : imgT A B C D t1 - netA2 A B C D = t1 • (netD1 B C D - netA2 A B C D) := by
      rw [hTpeq, ht2']; module
    have hR : imgX3 A B C D x2 - netA2 A B C D = x2 • (netB3 A B C D - netA2 A B C D) := by
      rw [imgX3]; module
    rw [hL, crss_smul_right] at h1
    rw [hR, crss_smul_right, crss_self, mul_zero] at h1
    -- crss v₂ (netD1 - netA2) = dist A B * dist A D * sin (∠ D A B) > 0
    have h2 : crss (netB3 A B C D - netA2 A B C D) (netD1 B C D - netA2 A B C D) =
        dist A B * dist A D * Real.sin (∠ D A B) := by
      rw [netB3_sub_netA2, show netD1 B C D - netA2 A B C D = -(netA2 A B C D - netD1 B C D)
        from by module, crss_neg_right, netA2_sub_netD1 A B C D htet, crss_smul_left,
        crss_smul_right, crss_e_e,
        show (π - ∠ B C D + ∠ C D A) - (∠ C D A - ∠ B C D - ∠ D A B) = π + ∠ D A B from by ring,
        Real.sin_add, Real.sin_pi, Real.cos_pi]
      ring
    have hsin := by simpa using sin_pos_of_tet A B C D htet 3 0 1 (by decide) (by decide) (by decide)
    have h5 : 0 < dist A B * dist A D * Real.sin (∠ D A B) :=
      mul_pos (mul_pos (dist_pos.mpr hAB) he) hsin
    rcases mul_eq_zero.mp h1 with h4 | h4
    · linarith [ht1, h4]
    · rw [h2] at h4
      linarith [h4, h5]
  -- derivative along the first hinge (edge BC, the x-axis)
  have hne1Y : imgY B C y1 + (0:ℝ) • e 0 - imgX A B C x1 ≠ 0 := by
    rw [zero_smul, add_zero]
    exact sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp hYX))
  have hne2Y : imgY B C y1 + (0:ℝ) • e 0 - imgZ B C D z1 ≠ 0 := by
    rw [zero_smul, add_zero]
    exact hYZ
  have hderY := hasDerivAt_h (imgX A B C x1) (imgZ B C D z1) (imgY B C y1) (e 0) 0 hne1Y hne2Y
  rw [zero_smul, add_zero] at hderY
  by_cases hDY : ⟪imgY B C y1 - imgX A B C x1, e 0⟫ / dist (imgX A B C x1) (imgY B C y1) +
      ⟪imgY B C y1 - imgZ B C D z1, e 0⟫ / dist (imgZ B C D z1) (imgY B C y1) = 0
  · -- hinge Y straight: continue with the remaining hinges
    have hW1 : Wbtw ℝ (imgX A B C x1) (imgY B C y1) (imgZ B C D z1) := by
      have hd0 : (e 0) 0 ≠ 0 := by rw [e_zero, Real.cos_zero]; exact one_ne_zero
      have hd1 : (e 0) 1 = 0 := by rw [e_one, Real.sin_zero]
      exact wbtw_comm.1 (wbtw_of_deriv_eq_zero hZpy hX0y hd0 hd1 hYpone (by linarith [hDY]))
    -- derivative along the second hinge (edge CD)
    have hne1Z : imgZ B C D z1 + (0:ℝ) • e (-(∠ B C D)) - imgY B C y1 ≠ 0 := by
      rw [zero_smul, add_zero]
      exact sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp hYZ))
    have hne2Z : imgZ B C D z1 + (0:ℝ) • e (-(∠ B C D)) - imgT A B C D t1 ≠ 0 := by
      rw [zero_smul, add_zero]
      exact sub_ne_zero.mpr hZT
    have hderZ := hasDerivAt_h (imgY B C y1) (imgT A B C D t1) (imgZ B C D z1)
      (e (-(∠ B C D))) 0 hne1Z hne2Z
    rw [zero_smul, add_zero] at hderZ
    have hcrssYZ : crss (e (-(∠ B C D))) (imgY B C y1 - imgZ B C D z1) =
        y1 * (dist B C * Real.sin (∠ B C D)) := by
      have e1 : imgY B C y1 - imgZ B C D z1 = y1 • netB0 B C - z2 • netD1 B C D := by
        rw [hYpeq, hZpeq]
      rw [e1, crss_sub_right, crss_smul_right, crss_smul_right, netB0, netD1, crss_smul_right,
        crss_smul_right, crss_e_e,
        show (0:ℝ) - -(∠ B C D) = ∠ B C D from by ring, crss_e_e,
        show -(∠ B C D) - -(∠ B C D) = (0:ℝ) from by ring, Real.sin_zero]
      ring
    have hcrssTZ : crss (e (-(∠ B C D))) (imgT A B C D t1 - imgZ B C D z1) =
        -(t2 * (dist A C * Real.sin (∠ D C A))) := by
      have e1 : imgT A B C D t1 - imgZ B C D z1 =
          (t1 - z2) • netD1 B C D + t2 • netA2 A B C D := by
        rw [hTpeq, hZpeq]; module
      rw [e1, crss_add_right, crss_smul_right, crss_smul_right, netD1, netA2, crss_smul_right,
        crss_smul_right, crss_e_e,
        show -(∠ B C D) - -(∠ B C D) = (0:ℝ) from by ring, Real.sin_zero, crss_e_e,
        show -(∠ B C D + ∠ D C A) - -(∠ B C D) = -(∠ D C A) from by ring, Real.sin_neg]
      ring
    have hsidesZ : crss (e (-(∠ B C D))) (imgY B C y1 - imgZ B C D z1) *
        crss (e (-(∠ B C D))) (imgT A B C D t1 - imgZ B C D z1) < 0 := by
      rw [hcrssYZ, hcrssTZ]
      have hsin1 := by simpa using sin_pos_of_tet A B C D htet 1 2 3 (by decide) (by decide) (by decide)
      have hsin2 := by simpa using sin_pos_of_tet A B C D htet 3 2 0 (by decide) (by decide) (by decide)
      have hp1 : 0 < y1 * (dist B C * Real.sin (∠ B C D)) := mul_pos hy1 (mul_pos ha hsin1)
      have hp2 : 0 < t2 * (dist A C * Real.sin (∠ D C A)) := mul_pos ht2 (mul_pos hb hsin2)
      exact mul_neg_of_pos_of_neg hp1 (by linarith [hp2])
    by_cases hDZ : ⟪imgZ B C D z1 - imgY B C y1, e (-(∠ B C D))⟫ /
        dist (imgY B C y1) (imgZ B C D z1) +
        ⟪imgZ B C D z1 - imgT A B C D t1, e (-(∠ B C D))⟫ /
        dist (imgT A B C D t1) (imgZ B C D z1) = 0
    · -- hinge Z straight: continue with the last hinge
      have hW2 : Wbtw ℝ (imgY B C y1) (imgZ B C D z1) (imgT A B C D t1) :=
        wbtw_of_deriv_eq_zero_gen (e_ne_zero _) hsidesZ hDZ
      -- derivative along the third hinge (edge DA)
      have hne1T : imgT A B C D t1 + (0:ℝ) • e (π - ∠ B C D + ∠ C D A) - imgZ B C D z1 ≠ 0 := by
        rw [zero_smul, add_zero]
        exact sub_ne_zero.mpr (Ne.symm hZT)
      have hne2T : imgT A B C D t1 + (0:ℝ) • e (π - ∠ B C D + ∠ C D A) -
          imgX3 A B C D x2 ≠ 0 := by
        rw [zero_smul, add_zero]
        exact hTX3
      have hderT := hasDerivAt_h (imgZ B C D z1) (imgX3 A B C D x2) (imgT A B C D t1)
        (e (π - ∠ B C D + ∠ C D A)) 0 hne1T hne2T
      rw [zero_smul, add_zero] at hderT
      have hcrssZT : crss (e (π - ∠ B C D + ∠ C D A)) (imgZ B C D z1 - imgT A B C D t1) =
          -(z1 * (dist C D * Real.sin (∠ C D A))) := by
        have e1 : imgZ B C D z1 - imgT A B C D t1 =
            (z2 - 1) • netD1 B C D - t2 • (netA2 A B C D - netD1 B C D) := by
          rw [hZpeq, hTpeq, ht2']; module
        rw [e1, show z2 - 1 = -z1 from by linarith [hz12], crss_sub_right, crss_smul_right,
          netA2_sub_netD1 A B C D htet, crss_smul_right, crss_smul_right, crss_self, mul_zero,
          mul_zero, sub_zero, netD1, crss_smul_right, crss_e_e,
          show -(∠ B C D) - (π - ∠ B C D + ∠ C D A) = -(π + ∠ C D A) from by ring,
          Real.sin_neg, Real.sin_add, Real.sin_pi, Real.cos_pi]
        ring
      have hcrssX3T : crss (e (π - ∠ B C D + ∠ C D A)) (imgX3 A B C D x2 - imgT A B C D t1) =
          x2 * (dist A B * Real.sin (∠ D A B)) := by
        have ht : t1 = 1 - t2 := by linarith [ht12]
        have e1 : imgX3 A B C D x2 - imgT A B C D t1 =
            t1 • (netA2 A B C D - netD1 B C D) + x2 • (netB3 A B C D - netA2 A B C D) := by
          rw [hX3eq, hTpeq, ht]; module
        rw [e1, crss_add_right, crss_smul_right, netA2_sub_netD1 A B C D htet, crss_smul_right,
          crss_self, mul_zero, mul_zero, zero_add, netB3_sub_netA2, crss_smul_right,
          crss_smul_right, crss_e_e,
          show (∠ C D A - ∠ B C D - ∠ D A B) - (π - ∠ B C D + ∠ C D A) = -(π + ∠ D A B)
            from by ring, Real.sin_neg, Real.sin_add, Real.sin_pi, Real.cos_pi]
        ring
      have hsidesT : crss (e (π - ∠ B C D + ∠ C D A)) (imgZ B C D z1 - imgT A B C D t1) *
          crss (e (π - ∠ B C D + ∠ C D A)) (imgX3 A B C D x2 - imgT A B C D t1) < 0 := by
        rw [hcrssZT, hcrssX3T]
        have hsin1 := by simpa using sin_pos_of_tet A B C D htet 2 3 0 (by decide) (by decide) (by decide)
        have hsin2 := by simpa using sin_pos_of_tet A B C D htet 3 0 1 (by decide) (by decide) (by decide)
        have hp1 : 0 < z1 * (dist C D * Real.sin (∠ C D A)) := mul_pos hz1 (mul_pos hd hsin1)
        have hp2 : 0 < x2 * (dist A B * Real.sin (∠ D A B)) :=
          mul_pos hx2 (mul_pos (dist_pos.mpr hAB) hsin2)
        exact mul_neg_of_neg_of_pos (by linarith [hp1]) hp2
      by_cases hDT : ⟪imgT A B C D t1 - imgZ B C D z1, e (π - ∠ B C D + ∠ C D A)⟫ /
          dist (imgZ B C D z1) (imgT A B C D t1) +
          ⟪imgT A B C D t1 - imgX3 A B C D x2, e (π - ∠ B C D + ∠ C D A)⟫ /
          dist (imgX3 A B C D x2) (imgT A B C D t1) = 0
      · -- all three hinges straight
        have hW3 : Wbtw ℝ (imgZ B C D z1) (imgT A B C D t1) (imgX3 A B C D x2) :=
          wbtw_of_deriv_eq_zero_gen (e_ne_zero _) hsidesT hDT
        -- the unfolded chain is straight, so the length is `dist X₀ X₃`
        have G1 : Wbtw ℝ (imgX A B C x1) (imgZ B C D z1) (imgT A B C D t1) :=
          Wbtw.trans_expand_right hW1 hW2 (sub_ne_zero.mp hYZ)
        have G2 : Wbtw ℝ (imgX A B C x1) (imgZ B C D z1) (imgX3 A B C D x2) :=
          Wbtw.trans_expand_left G1 hW3 hZT
        have G3 : Wbtw ℝ (imgX A B C x1) (imgY B C y1) (imgX3 A B C D x2) :=
          Wbtw.trans_left G2 hW1
        have G3b : Wbtw ℝ (imgX A B C x1) (imgT A B C D t1) (imgX3 A B C D x2) :=
          Wbtw.trans_expand_right G1 hW3 hZT
        have hLen2 : pathLength X Y Z T = dist (imgX A B C x1) (imgX3 A B C D x2) := by
          have e1 := wbtw_dist_add_dist hW1
          have e3 := wbtw_dist_add_dist hW3
          have e4 := wbtw_dist_add_dist G2
          linarith [hLen, e1, e3, e4]
        -- derivative at the X-hinge (moving both images of X simultaneously)
        have hne1X : netA0 A B C + x2 • (netB0 B C - netA0 A B C) - imgY B C y1 ≠ 0 := by
          rw [← hX0eq]
          exact hYX
        have hne2X : netA2 A B C D + x2 • (netB3 A B C D - netA2 A B C D) -
            imgT A B C D t1 ≠ 0 := by
          rw [← hX3eq]
          exact sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp hTX3))
        have hderX := (hasDerivAt_dist_line (imgY B C y1) (netA0 A B C)
          (netB0 B C - netA0 A B C) x2 hne1X).add (hasDerivAt_dist_line (imgT A B C D t1)
          (netA2 A B C D) (netB3 A B C D - netA2 A B C D) x2 hne2X)
        rw [← hX0eq, ← hX3eq] at hderX
        by_cases hDX : ⟪imgX A B C x1 - imgY B C y1, netB0 B C - netA0 A B C⟫ /
            dist (imgY B C y1) (imgX A B C x1) +
            ⟪imgX3 A B C D x2 - imgT A B C D t1, netB3 A B C D - netA2 A B C D⟫ /
            dist (imgT A B C D t1) (imgX3 A B C D x2) = 0
        · -- the critical case: the side-alternation forces the two images of edge `AB`
          -- to be parallel, i.e. the angle condition — contradiction
          have hXX3 : imgX A B C x1 ≠ imgX3 A B C D x2 := by
            intro he
            have h1 := mem_segment_iff_wbtw.2 G3
            rw [he, segment_same, Set.mem_singleton_iff] at h1
            have e := congrArg (fun w : Pt2 => (w) 1) h1
            rw [← he, hYpone] at e
            linarith [hX0y, e]
          have hlam : imgX3 A B C D x2 - imgX A B C x1 ≠ 0 := sub_ne_zero.mpr hXX3.symm
          obtain ⟨a1, b1, ha1, hb1, hab1, hYseg⟩ := mem_segment_iff_wbtw.2 G3
          obtain ⟨a2, b2, ha2, hb2, hab2, hZseg⟩ := mem_segment_iff_wbtw.2 G2
          obtain ⟨a3, b3, ha3, hb3, hab3, hTseg⟩ := mem_segment_iff_wbtw.2 G3b
          have hσY : crss (imgX3 A B C D x2 - imgX A B C x1) (imgY B C y1 - imgX A B C x1) = 0 := by
            have e1 : imgY B C y1 - imgX A B C x1 =
                b1 • (imgX3 A B C D x2 - imgX A B C x1) := by
              have ha1' : a1 = 1 - b1 := by linarith [hab1]
              rw [← hYseg, ha1']
              module
            rw [e1, crss_smul_right, crss_self, mul_zero]
          have hσZ : crss (imgX3 A B C D x2 - imgX A B C x1) (imgZ B C D z1 - imgX A B C x1) = 0 := by
            have e1 : imgZ B C D z1 - imgX A B C x1 =
                b2 • (imgX3 A B C D x2 - imgX A B C x1) := by
              have ha2' : a2 = 1 - b2 := by linarith [hab2]
              rw [← hZseg, ha2']
              module
            rw [e1, crss_smul_right, crss_self, mul_zero]
          have hσT : crss (imgX3 A B C D x2 - imgX A B C x1) (imgT A B C D t1 - imgX A B C x1) = 0 := by
            have e1 : imgT A B C D t1 - imgX A B C x1 =
                b3 • (imgX3 A B C D x2 - imgX A B C x1) := by
              have ha3' : a3 = 1 - b3 := by linarith [hab3]
              rw [← hTseg, ha3']
              module
            rw [e1, crss_smul_right, crss_self, mul_zero]
          -- the hinge-endpoint side relations along the transversal line
          have hYc : y1 * crss (imgX3 A B C D x2 - imgX A B C x1) (netB0 B C - imgX A B C x1) +
              y2 * crss (imgX3 A B C D x2 - imgX A B C x1) (netC0 - imgX A B C x1) = 0 := by
            have e1 : imgY B C y1 - imgX A B C x1 =
                y1 • (netB0 B C - imgX A B C x1) + y2 • (netC0 - imgX A B C x1) := by
              have hy : y1 = 1 - y2 := by linarith [hy12]
              rw [hYpeq, netC0, hy]
              module
            rw [e1, crss_add_right, crss_smul_right, crss_smul_right] at hσY
            linarith [hσY]
          have hZc : z1 * crss (imgX3 A B C D x2 - imgX A B C x1) (netC0 - imgX A B C x1) +
              z2 * crss (imgX3 A B C D x2 - imgX A B C x1) (netD1 B C D - imgX A B C x1) = 0 := by
            have e1 : imgZ B C D z1 - imgX A B C x1 =
                z1 • (netC0 - imgX A B C x1) + z2 • (netD1 B C D - imgX A B C x1) := by
              rw [hZpeq, netC0, hz2']
              module
            rw [e1, crss_add_right, crss_smul_right, crss_smul_right] at hσZ
            linarith [hσZ]
          have hTc : t1 * crss (imgX3 A B C D x2 - imgX A B C x1) (netD1 B C D - imgX A B C x1) +
              t2 * crss (imgX3 A B C D x2 - imgX A B C x1) (netA2 A B C D - imgX A B C x1) = 0 := by
            have e1 : imgT A B C D t1 - imgX A B C x1 =
                t1 • (netD1 B C D - imgX A B C x1) + t2 • (netA2 A B C D - imgX A B C x1) := by
              rw [hTpeq, ht2']
              module
            rw [e1, crss_add_right, crss_smul_right, crss_smul_right] at hσT
            linarith [hσT]
          -- the side function at B₀ and at A₂ in terms of the two edge images
          have hσB0 : crss (imgX3 A B C D x2 - imgX A B C x1) (netB0 B C - imgX A B C x1) =
              (1 - x2) * crss (imgX3 A B C D x2 - imgX A B C x1) (netB0 B C - netA0 A B C) := by
            have e1 : netB0 B C - imgX A B C x1 = (1 - x2) • (netB0 B C - netA0 A B C) := by
              rw [hX0eq]; module
            rw [e1, crss_smul_right]
          have hσA2 : crss (imgX3 A B C D x2 - imgX A B C x1) (netA2 A B C D - imgX A B C x1) =
              -x2 * crss (imgX3 A B C D x2 - imgX A B C x1) (netB3 A B C D - netA2 A B C D) := by
            have e1 : netA2 A B C D - imgX A B C x1 =
                (imgX3 A B C D x2 - imgX A B C x1) - x2 • (netB3 A B C D - netA2 A B C D) := by
              rw [hX0eq, hX3eq]; module
            rw [e1, crss_sub_right, crss_self, zero_sub, crss_smul_right]
            ring
          -- strict side alternation, bootstrapped from the first hinge
          have hnot : ¬ (crss (imgX3 A B C D x2 - imgX A B C x1) (netB0 B C - imgX A B C x1) = 0 ∧
              crss (imgX3 A B C D x2 - imgX A B C x1) (netC0 - imgX A B C x1) = 0) := by
            rintro ⟨h1, h2⟩
            have hc1 : crss (imgX3 A B C D x2 - imgX A B C x1) (netB0 B C - netA0 A B C) = 0 := by
              have e : (1 - x2) * crss (imgX3 A B C D x2 - imgX A B C x1)
                  (netB0 B C - netA0 A B C) = 0 := by rw [← hσB0]; exact h1
              exact (mul_eq_zero.mp e).resolve_left
                (show (0:ℝ) < 1 - x2 from by linarith [hx1, hx1']).ne'
            have hc2 : crss (imgX3 A B C D x2 - imgX A B C x1) (netA0 A B C) = 0 := by
              have e1 : netC0 - imgX A B C x1 = -(netA0 A B C + x2 • (netB0 B C - netA0 A B C)) := by
                rw [netC0, hX0eq]; module
              rw [e1, crss_neg_right, neg_eq_zero, crss_add_right, crss_smul_right, hc1] at h2
              linarith [h2]
            have hc3 : crss (netA0 A B C) (netB0 B C - netA0 A B C) = 0 :=
              crss_eq_zero_of_crss_eq_zero_and_crss_eq_zero hlam hc2 hc1
            have hc4 : crss (netA0 A B C) (netB0 B C) = 0 := by
              have e : crss (netA0 A B C) (netB0 B C - netA0 A B C) =
                  crss (netA0 A B C) (netB0 B C) := by
                rw [crss_sub_right, crss_self, sub_zero]
              rw [e] at hc3
              exact hc3
            have hc5 : crss (netA0 A B C) (netB0 B C) =
                -(dist A C * (dist B C * Real.sin (∠ B C A))) := by
              rw [netA0, netB0, crss_smul_left, crss_smul_right, crss_e_e,
                show (0:ℝ) - ∠ B C A = -(∠ B C A) from by ring, Real.sin_neg]
              ring
            have hsin := by
              simpa using sin_pos_of_tet A B C D htet 1 2 0 (by decide) (by decide) (by decide)
            have h6 : 0 < dist A C * (dist B C * Real.sin (∠ B C A)) := mul_pos hb (mul_pos ha hsin)
            rw [hc5] at hc4
            linarith [h6, hc4]
          have hprodB : crss (imgX3 A B C D x2 - imgX A B C x1) (netB0 B C - imgX A B C x1) *
              crss (imgX3 A B C D x2 - imgX A B C x1) (netC0 - imgX A B C x1) < 0 := by
            have e1 : y2 * crss (imgX3 A B C D x2 - imgX A B C x1) (netC0 - imgX A B C x1) =
                -(y1 * crss (imgX3 A B C D x2 - imgX A B C x1) (netB0 B C - imgX A B C x1)) := by
              linarith [hYc]
            by_cases hB0 : crss (imgX3 A B C D x2 - imgX A B C x1) (netB0 B C - imgX A B C x1) = 0
            · exfalso
              have hC0 : crss (imgX3 A B C D x2 - imgX A B C x1) (netC0 - imgX A B C x1) = 0 := by
                rw [hB0, mul_zero, neg_zero] at e1
                exact (mul_eq_zero.mp e1).resolve_left hy2.ne'
              exact hnot ⟨hB0, hC0⟩
            · have e2 := congrArg (crss (imgX3 A B C D x2 - imgX A B C x1)
                (netB0 B C - imgX A B C x1) * ·) e1
              have e3 : y2 * (crss (imgX3 A B C D x2 - imgX A B C x1) (netB0 B C - imgX A B C x1) *
                  crss (imgX3 A B C D x2 - imgX A B C x1) (netC0 - imgX A B C x1)) =
                  -(y1 * (crss (imgX3 A B C D x2 - imgX A B C x1)
                    (netB0 B C - imgX A B C x1)) ^ 2) := by
                have t : y2 * (crss (imgX3 A B C D x2 - imgX A B C x1) (netB0 B C - imgX A B C x1) *
                    crss (imgX3 A B C D x2 - imgX A B C x1) (netC0 - imgX A B C x1)) =
                    crss (imgX3 A B C D x2 - imgX A B C x1) (netB0 B C - imgX A B C x1) *
                    (y2 * crss (imgX3 A B C D x2 - imgX A B C x1) (netC0 - imgX A B C x1)) := by ring
                rw [t, e2]
                ring
              have h7 : y2 * (crss (imgX3 A B C D x2 - imgX A B C x1) (netB0 B C - imgX A B C x1) *
                  crss (imgX3 A B C D x2 - imgX A B C x1) (netC0 - imgX A B C x1)) < 0 := by
                rw [e3]
                have h6 : 0 < y1 * (crss (imgX3 A B C D x2 - imgX A B C x1)
                    (netB0 B C - imgX A B C x1)) ^ 2 := mul_pos hy1 (sq_pos_of_ne_zero hB0)
                linarith [h6]
              rcases mul_neg_iff.1 h7 with hcase | hcase
              · exact hcase.2
              · linarith [hcase.1, hy2]
          have hC0ne : crss (imgX3 A B C D x2 - imgX A B C x1) (netC0 - imgX A B C x1) ≠ 0 := by
            intro hcc
            rw [hcc, mul_zero] at hprodB
            exact lt_irrefl _ hprodB
          have hprodC : crss (imgX3 A B C D x2 - imgX A B C x1) (netC0 - imgX A B C x1) *
              crss (imgX3 A B C D x2 - imgX A B C x1) (netD1 B C D - imgX A B C x1) < 0 := by
            have e1 : z2 * crss (imgX3 A B C D x2 - imgX A B C x1) (netD1 B C D - imgX A B C x1) =
                -(z1 * crss (imgX3 A B C D x2 - imgX A B C x1) (netC0 - imgX A B C x1)) := by
              linarith [hZc]
            have e2 := congrArg (crss (imgX3 A B C D x2 - imgX A B C x1)
              (netC0 - imgX A B C x1) * ·) e1
            have e3 : z2 * (crss (imgX3 A B C D x2 - imgX A B C x1) (netC0 - imgX A B C x1) *
                crss (imgX3 A B C D x2 - imgX A B C x1) (netD1 B C D - imgX A B C x1)) =
                -(z1 * (crss (imgX3 A B C D x2 - imgX A B C x1) (netC0 - imgX A B C x1)) ^ 2) := by
              have t : z2 * (crss (imgX3 A B C D x2 - imgX A B C x1) (netC0 - imgX A B C x1) *
                  crss (imgX3 A B C D x2 - imgX A B C x1) (netD1 B C D - imgX A B C x1)) =
                  crss (imgX3 A B C D x2 - imgX A B C x1) (netC0 - imgX A B C x1) *
                  (z2 * crss (imgX3 A B C D x2 - imgX A B C x1) (netD1 B C D - imgX A B C x1)) := by
                ring
              rw [t, e2]
              ring
            have h7 : z2 * (crss (imgX3 A B C D x2 - imgX A B C x1) (netC0 - imgX A B C x1) *
                crss (imgX3 A B C D x2 - imgX A B C x1) (netD1 B C D - imgX A B C x1)) < 0 := by
              rw [e3]
              have h6 : 0 < z1 * (crss (imgX3 A B C D x2 - imgX A B C x1)
                  (netC0 - imgX A B C x1)) ^ 2 := mul_pos hz1 (sq_pos_of_ne_zero hC0ne)
              linarith [h6]
            rcases mul_neg_iff.1 h7 with hcase | hcase
            · exact hcase.2
            · linarith [hcase.1, hz2]
          have hD1ne : crss (imgX3 A B C D x2 - imgX A B C x1) (netD1 B C D - imgX A B C x1) ≠ 0 := by
            intro hcc
            rw [hcc, mul_zero] at hprodC
            exact lt_irrefl _ hprodC
          have hprodD : crss (imgX3 A B C D x2 - imgX A B C x1) (netD1 B C D - imgX A B C x1) *
              crss (imgX3 A B C D x2 - imgX A B C x1) (netA2 A B C D - imgX A B C x1) < 0 := by
            have e1 : t2 * crss (imgX3 A B C D x2 - imgX A B C x1) (netA2 A B C D - imgX A B C x1) =
                -(t1 * crss (imgX3 A B C D x2 - imgX A B C x1) (netD1 B C D - imgX A B C x1)) := by
              linarith [hTc]
            have e2 := congrArg (crss (imgX3 A B C D x2 - imgX A B C x1)
              (netD1 B C D - imgX A B C x1) * ·) e1
            have e3 : t2 * (crss (imgX3 A B C D x2 - imgX A B C x1) (netD1 B C D - imgX A B C x1) *
                crss (imgX3 A B C D x2 - imgX A B C x1) (netA2 A B C D - imgX A B C x1)) =
                -(t1 * (crss (imgX3 A B C D x2 - imgX A B C x1) (netD1 B C D - imgX A B C x1)) ^ 2) := by
              have t : t2 * (crss (imgX3 A B C D x2 - imgX A B C x1) (netD1 B C D - imgX A B C x1) *
                  crss (imgX3 A B C D x2 - imgX A B C x1) (netA2 A B C D - imgX A B C x1)) =
                  crss (imgX3 A B C D x2 - imgX A B C x1) (netD1 B C D - imgX A B C x1) *
                  (t2 * crss (imgX3 A B C D x2 - imgX A B C x1) (netA2 A B C D - imgX A B C x1)) := by
                ring
              rw [t, e2]
              ring
            have h7 : t2 * (crss (imgX3 A B C D x2 - imgX A B C x1) (netD1 B C D - imgX A B C x1) *
                crss (imgX3 A B C D x2 - imgX A B C x1) (netA2 A B C D - imgX A B C x1)) < 0 := by
              rw [e3]
              have h6 : 0 < t1 * (crss (imgX3 A B C D x2 - imgX A B C x1)
                  (netD1 B C D - imgX A B C x1)) ^ 2 := mul_pos ht1 (sq_pos_of_ne_zero hD1ne)
              linarith [h6]
            rcases mul_neg_iff.1 h7 with hcase | hcase
            · exact hcase.2
            · linarith [hcase.1, ht2]
          -- chaining the alternation: B₀ and A₂ are on opposite sides
          have hprodBA2 : crss (imgX3 A B C D x2 - imgX A B C x1) (netB0 B C - imgX A B C x1) *
              crss (imgX3 A B C D x2 - imgX A B C x1) (netA2 A B C D - imgX A B C x1) < 0 := by
            have hp := mul_neg_of_pos_of_neg (mul_pos_of_neg_of_neg hprodB hprodC) hprodD
            have hCD2 : 0 < (crss (imgX3 A B C D x2 - imgX A B C x1) (netC0 - imgX A B C x1) *
                crss (imgX3 A B C D x2 - imgX A B C x1) (netD1 B C D - imgX A B C x1)) ^ 2 :=
              sq_pos_of_ne_zero (fun hq => by
                rw [hq] at hprodC; exact lt_irrefl _ hprodC)
            have heq : ((crss (imgX3 A B C D x2 - imgX A B C x1) (netB0 B C - imgX A B C x1) *
                crss (imgX3 A B C D x2 - imgX A B C x1) (netC0 - imgX A B C x1)) *
                (crss (imgX3 A B C D x2 - imgX A B C x1) (netC0 - imgX A B C x1) *
                crss (imgX3 A B C D x2 - imgX A B C x1) (netD1 B C D - imgX A B C x1))) *
                (crss (imgX3 A B C D x2 - imgX A B C x1) (netD1 B C D - imgX A B C x1) *
                crss (imgX3 A B C D x2 - imgX A B C x1) (netA2 A B C D - imgX A B C x1)) =
                (crss (imgX3 A B C D x2 - imgX A B C x1) (netB0 B C - imgX A B C x1) *
                crss (imgX3 A B C D x2 - imgX A B C x1) (netA2 A B C D - imgX A B C x1)) *
                (crss (imgX3 A B C D x2 - imgX A B C x1) (netC0 - imgX A B C x1) *
                crss (imgX3 A B C D x2 - imgX A B C x1) (netD1 B C D - imgX A B C x1)) ^ 2 := by
              ring
            rw [heq] at hp
            rcases mul_neg_iff.1 hp with hcase | hcase
            · linarith [hcase.2, hCD2]
            · exact hcase.1
          -- hence the two cross products have the same strict sign
          have hsgn : 0 < crss (imgX3 A B C D x2 - imgX A B C x1) (netB0 B C - netA0 A B C) *
              crss (imgX3 A B C D x2 - imgX A B C x1) (netB3 A B C D - netA2 A B C D) := by
            have e : crss (imgX3 A B C D x2 - imgX A B C x1) (netB0 B C - imgX A B C x1) *
                crss (imgX3 A B C D x2 - imgX A B C x1) (netA2 A B C D - imgX A B C x1) =
                ((1 - x2) * (-x2)) * (crss (imgX3 A B C D x2 - imgX A B C x1)
                  (netB0 B C - netA0 A B C) *
                  crss (imgX3 A B C D x2 - imgX A B C x1) (netB3 A B C D - netA2 A B C D)) := by
              rw [hσB0, hσA2]
              ring
            rw [e] at hprodBA2
            have hf : (1 - x2) * (-x2) < 0 :=
              mul_neg_of_pos_of_neg (by linarith [hx1, hx1'] : (0:ℝ) < 1 - x2)
                (by linarith [hx2] : -x2 < 0)
            rcases mul_neg_iff.1 hprodBA2 with hcase | hcase
            · linarith [hcase.1, hf]
            · exact hcase.2
          -- the inner products are equal (criticality of the X-hinge)
          have hpara1 : imgX A B C x1 - imgY B C y1 =
              -(b1 • (imgX3 A B C D x2 - imgX A B C x1)) := by
            have ha1' : a1 = 1 - b1 := by linarith [hab1]
            rw [← hYseg, ha1']
            module
          have hb1pos : 0 < b1 := by
            rcases eq_or_lt_of_le hb1 with h | h
            · exfalso
              have ha1' : a1 = 1 := by linarith [hab1, h]
              have e : imgY B C y1 = imgX A B C x1 := by
                rw [← hYseg, ← h, ha1']
                module
              have e2 := congrArg (fun w : Pt2 => (w) 1) e
              rw [hYpone] at e2
              linarith [hX0y, e2]
            · exact h
          have hdist1 : dist (imgX A B C x1) (imgY B C y1) =
              b1 * dist (imgX A B C x1) (imgX3 A B C D x2) := by
            rw [dist_eq_norm, hpara1, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hb1,
              ← dist_eq_norm, dist_comm (imgX3 A B C D x2) (imgX A B C x1)]
          have hpara2 : imgX3 A B C D x2 - imgT A B C D t1 =
              a3 • (imgX3 A B C D x2 - imgX A B C x1) := by
            have hb3' : b3 = 1 - a3 := by linarith [hab3]
            rw [← hTseg, hb3']
            module
          have ha3pos : 0 < a3 := by
            rcases eq_or_lt_of_le ha3 with h | h
            · exfalso
              have hb3' : b3 = 1 := by linarith [hab3, h]
              have e : imgT A B C D t1 = imgX3 A B C D x2 := by
                rw [← hTseg, ← h, hb3']
                module
              exact hTX3 (sub_eq_zero.2 e)
            · exact h
          have hdist2 : dist (imgT A B C D t1) (imgX3 A B C D x2) =
              a3 * dist (imgX A B C x1) (imgX3 A B C D x2) := by
            rw [dist_eq_norm, show imgT A B C D t1 - imgX3 A B C D x2 =
              -(a3 • (imgX3 A B C D x2 - imgX A B C x1)) from by rw [← hpara2]; module,
              norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha3, ← dist_eq_norm,
              dist_comm (imgX3 A B C D x2) (imgX A B C x1)]
          have hinner : ⟪imgX3 A B C D x2 - imgX A B C x1, netB0 B C - netA0 A B C⟫ =
              ⟪imgX3 A B C D x2 - imgX A B C x1, netB3 A B C D - netA2 A B C D⟫ := by
            rw [hpara1, inner_neg_left, real_inner_smul_left, hpara2, real_inner_smul_left,
              dist_comm (imgY B C y1) (imgX A B C x1), hdist1, hdist2, neg_div,
              mul_div_mul_left _ _ hb1pos.ne', mul_div_mul_left _ _ ha3pos.ne'] at hDX
            have hDXX : dist (imgX A B C x1) (imgX3 A B C D x2) ≠ 0 := dist_ne_zero.mpr hXX3
            field_simp [hDXX] at hDX
            linarith [hDX]
          -- Lagrange: the cross products agree too
          have hnorm1 : ‖netB0 B C - netA0 A B C‖ = dist A B := by
            rw [← dist_eq_norm, dist_comm, dist_netA0_netB0]
          have hnorm2 : ‖netB3 A B C D - netA2 A B C D‖ = dist A B := by
            rw [← dist_eq_norm, dist_comm, dist_netA2_netB3]
          have hcsq : crss (imgX3 A B C D x2 - imgX A B C x1) (netB0 B C - netA0 A B C) ^ 2 =
              crss (imgX3 A B C D x2 - imgX A B C x1) (netB3 A B C D - netA2 A B C D) ^ 2 := by
            have L1 := crss_sq_add_inner_sq (imgX3 A B C D x2 - imgX A B C x1)
              (netB0 B C - netA0 A B C)
            have L2 := crss_sq_add_inner_sq (imgX3 A B C D x2 - imgX A B C x1)
              (netB3 A B C D - netA2 A B C D)
            rw [hnorm1] at L1
            rw [hnorm2] at L2
            rw [hinner] at L1
            linarith [L1, L2]
          have hceq : crss (imgX3 A B C D x2 - imgX A B C x1) (netB0 B C - netA0 A B C) =
              crss (imgX3 A B C D x2 - imgX A B C x1) (netB3 A B C D - netA2 A B C D) := by
            rcases sq_eq_sq_iff_eq_or_eq_neg.1 hcsq with h | h
            · exact h
            · exfalso
              rw [h] at hsgn
              have hnn : (0:ℝ) ≤ crss (imgX3 A B C D x2 - imgX A B C x1)
                  (netB3 A B C D - netA2 A B C D) ^ 2 := sq_nonneg _
              have he2 : (-crss (imgX3 A B C D x2 - imgX A B C x1)
                  (netB3 A B C D - netA2 A B C D)) *
                  crss (imgX3 A B C D x2 - imgX A B C x1) (netB3 A B C D - netA2 A B C D) ≤ 0 := by
                have h3 : (-crss (imgX3 A B C D x2 - imgX A B C x1)
                    (netB3 A B C D - netA2 A B C D)) *
                    crss (imgX3 A B C D x2 - imgX A B C x1) (netB3 A B C D - netA2 A B C D) =
                    -(crss (imgX3 A B C D x2 - imgX A B C x1) (netB3 A B C D - netA2 A B C D) ^ 2) := by
                  ring
                rw [h3]
                linarith [hnn]
              exact absurd hsgn (not_lt.mpr he2)
          have hveq : netB3 A B C D - netA2 A B C D = netB0 B C - netA0 A B C := by
            have h1 : (netB3 A B C D - netA2 A B C D) - (netB0 B C - netA0 A B C) = 0 :=
              eq_zero_of_inner_crss_eq_zero hlam
                (by rw [inner_sub_right, hinner]; ring)
                (by rw [crss_sub_right, hceq]; ring)
            exact sub_eq_zero.1 h1
          have hcond : ∠ D A B + ∠ B C D = ∠ C D A + ∠ A B C := by
            have hα : 0 < ∠ D A B := by
              simpa using angle_pos_of_tet A B C D htet 3 0 1 (by decide) (by decide) (by decide)
            have hβ : 0 < ∠ A B C := by
              simpa using angle_pos_of_tet A B C D htet 0 1 2 (by decide) (by decide) (by decide)
            have hγ : 0 < ∠ B C D := by
              simpa using angle_pos_of_tet A B C D htet 1 2 3 (by decide) (by decide) (by decide)
            have hδ : 0 < ∠ C D A := by
              simpa using angle_pos_of_tet A B C D htet 2 3 0 (by decide) (by decide) (by decide)
            exact (net_edge_vec_eq_iff A B C D htet hα hβ hγ hδ hABD.2.2 hABC.1 hBCD.1
              hACD.2.1).1 hveq
          exact absurd hcond hang
        · -- slide X: perturbing `X` along `AB` shortens the path
          obtain ⟨s, hsabs, hslt⟩ := exists_smaller_of_hasDerivAt_ne_zero hderX hDX
            (min x2 (1 - x2)) (lt_min hx2 (by linarith [hx1, hx1'] : (0:ℝ) < 1 - x2))
          have htn0 : 0 < x2 + s := by
            have hle : min x2 (1 - x2) ≤ x2 := min_le_left _ _
            have h1 := abs_lt.1 hsabs
            linarith [h1.1, hle]
          have htn1 : x2 + s < 1 := by
            have hle : min x2 (1 - x2) ≤ 1 - x2 := min_le_right _ _
            have h1 := abs_lt.1 hsabs
            linarith [h1.2, hle]
          have himgXn : imgX A B C (1 - (x2 + s)) =
              netA0 A B C + (x2 + s) • (netB0 B C - netA0 A B C) := by
            rw [imgX]
            module
          have hX3n : imgX3 A B C D (x2 + s) =
              netA2 A B C D + (x2 + s) • (netB3 A B C D - netA2 A B C D) := rfl
          refine ⟨(1 - (x2 + s)) • A + (x2 + s) • B, Y, Z, T, ⟨?_, hY0, hZ0, hT0⟩, ?_⟩
          · rw [openSegment_eq_image₂]
            exact ⟨(1 - (x2 + s), x2 + s), ⟨by linarith [htn1], htn0, by ring⟩, rfl⟩
          · have hLenN : pathLength ((1 - (x2 + s)) • A + (x2 + s) • B) Y Z T =
                dist (imgX A B C (1 - (x2 + s))) (imgY B C y1) +
                dist (imgY B C y1) (imgZ B C D z1) +
                dist (imgZ B C D z1) (imgT A B C D t1) +
                dist (imgT A B C D t1) (imgX3 A B C D (x2 + s)) := by
              rw [pathLength, ← dist_imgX_imgY A B C D htet
                (by linarith [htn1] : (0:ℝ) < 1 - (x2 + s)) htn0
                (by ring : 1 - (x2 + s) + (x2 + s) = 1) rfl hy1 hy2 hy12 hYe,
                ← dist_imgY_imgZ A B C D htet hy1 hy2 hy12 hYe hz1 hz2 hz12 hZe,
                ← dist_imgZ_imgT A B C D htet hz1 hz2 hz12 hZe ht1 ht2 ht12 hTe,
                ← dist_imgT_imgX3 A B C D htet ht1 ht2 ht12 hTe
                (by linarith [htn1] : (0:ℝ) < 1 - (x2 + s)) htn0 (by ring) rfl]
            change dist (imgY B C y1) (netA0 A B C + (x2 + s) • (netB0 B C - netA0 A B C)) +
                dist (imgT A B C D t1) (netA2 A B C D + (x2 + s) • (netB3 A B C D - netA2 A B C D)) <
              dist (imgY B C y1) (netA0 A B C + x2 • (netB0 B C - netA0 A B C)) +
                dist (imgT A B C D t1) (netA2 A B C D + x2 • (netB3 A B C D - netA2 A B C D)) at hslt
            rw [← hX0eq, ← hX3eq] at hslt
            rw [dist_comm (imgY B C y1) (imgX A B C x1)] at hslt
            rw [hLenN, himgXn, hX3n, dist_comm (netA0 A B C + (x2 + s) • (netB0 B C - netA0 A B C))
              (imgY B C y1), hLen]
            linarith [hslt]
      · -- hinge T bends: perturbing `T` along its edge shortens the path
        obtain ⟨s, hsabs, hslt⟩ := exists_smaller_of_hasDerivAt_ne_zero hderT hDT
          (min (t1 * dist A D) ((1 - t1) * dist A D))
          (lt_min (mul_pos ht1 he) (mul_pos (by linarith [ht1, ht2] : (0:ℝ) < 1 - t1) he))
        have ht1n : 0 < t1 - s / dist A D := by
          have h1 : |s / dist A D| < t1 := by
            rw [abs_div, abs_of_pos he, div_lt_iff₀ he]
            exact lt_of_lt_of_le hsabs (min_le_left _ _)
          have h2 := abs_lt.1 h1
          linarith [h2.2]
        have ht2n : 0 < 1 - (t1 - s / dist A D) := by
          have h1 : |s / dist A D| < 1 - t1 := by
            rw [abs_div, abs_of_pos he, div_lt_iff₀ he]
            exact lt_of_lt_of_le hsabs (min_le_right _ _)
          have h2 := abs_lt.1 h1
          linarith [h2.1]
        have himgTn : imgT A B C D (t1 - s / dist A D) = imgT A B C D t1 +
            s • e (π - ∠ B C D + ∠ C D A) := by
          have ediff : imgT A B C D (t1 - s / dist A D) - imgT A B C D t1 =
              (-(s / dist A D)) • (netD1 B C D - netA2 A B C D) := by
            rw [imgT, imgT]
            module
          have hnd : netD1 B C D - netA2 A B C D = -(dist A D • e (π - ∠ B C D + ∠ C D A)) := by
            rw [← netA2_sub_netD1 A B C D htet]; module
          have es : (-(s / dist A D)) • (netD1 B C D - netA2 A B C D) =
              s • e (π - ∠ B C D + ∠ C D A) := by
            rw [hnd, smul_neg, ← neg_div, smul_smul, div_mul_cancel₀ _ he.ne', neg_smul, neg_neg]
          have e3 := sub_eq_iff_eq_add.1 ediff
          rw [es] at e3
          rw [e3]
          module
        refine ⟨X, Y, Z, (t1 - s / dist A D) • D + (1 - (t1 - s / dist A D)) • A,
          ⟨hX0, hY0, hZ0, ?_⟩, ?_⟩
        · rw [openSegment_eq_image₂]
          exact ⟨(t1 - s / dist A D, 1 - (t1 - s / dist A D)),
            ⟨ht1n, ht2n, by ring⟩, rfl⟩
        · have hLenN : pathLength X Y Z ((t1 - s / dist A D) • D + (1 - (t1 - s / dist A D)) • A) =
              dist (imgX A B C x1) (imgY B C y1) +
              dist (imgY B C y1) (imgZ B C D z1) +
              dist (imgZ B C D z1) (imgT A B C D (t1 - s / dist A D)) +
              dist (imgT A B C D (t1 - s / dist A D)) (imgX3 A B C D x2) := by
            rw [pathLength, ← dist_imgX_imgY A B C D htet hx1 hx2 hx12 hXe hy1 hy2 hy12 hYe,
              ← dist_imgY_imgZ A B C D htet hy1 hy2 hy12 hYe hz1 hz2 hz12 hZe,
              ← dist_imgZ_imgT A B C D htet hz1 hz2 hz12 hZe ht1n ht2n (by ring) rfl,
              ← dist_imgT_imgX3 A B C D htet ht1n ht2n (by ring) rfl hx1 hx2 hx12 hXe]
          simp only [zero_add, zero_smul, add_zero] at hslt
          rw [dist_comm (imgX3 A B C D x2) (imgT A B C D t1 +
              s • e (π - ∠ B C D + ∠ C D A)),
            dist_comm (imgX3 A B C D x2) (imgT A B C D t1)] at hslt
          rw [hLenN, himgTn, hLen]
          linarith [hslt]
    · -- hinge Z bends: perturbing `Z` along its edge shortens the path
      obtain ⟨s, hsabs, hslt⟩ := exists_smaller_of_hasDerivAt_ne_zero hderZ hDZ
        (min (z1 * dist C D) ((1 - z1) * dist C D))
        (lt_min (mul_pos hz1 hd) (mul_pos (by linarith [hz1, hz2] : (0:ℝ) < 1 - z1) hd))
      have hz1n : 0 < z1 - s / dist C D := by
        have h1 : |s / dist C D| < z1 := by
          rw [abs_div, abs_of_pos hd, div_lt_iff₀ hd]
          exact lt_of_lt_of_le hsabs (min_le_left _ _)
        have h2 := abs_lt.1 h1
        linarith [h2.2]
      have hz2n : 0 < 1 - (z1 - s / dist C D) := by
        have h1 : |s / dist C D| < 1 - z1 := by
          rw [abs_div, abs_of_pos hd, div_lt_iff₀ hd]
          exact lt_of_lt_of_le hsabs (min_le_right _ _)
        have h2 := abs_lt.1 h1
        linarith [h2.1]
      have himgZn : imgZ B C D (z1 - s / dist C D) = imgZ B C D z1 + s • e (-(∠ B C D)) := by
        have e1 : imgZ B C D (z1 - s / dist C D) = (z2 + s / dist C D) • netD1 B C D := by
          rw [imgZ, netC0, hz2']
          module
        rw [e1, hZpeq, add_smul, netD1, smul_smul, smul_smul, div_mul_cancel₀ _ hd.ne']
      refine ⟨X, Y, (z1 - s / dist C D) • C + (1 - (z1 - s / dist C D)) • D, T,
        ⟨hX0, hY0, ?_, hT0⟩, ?_⟩
      · rw [openSegment_eq_image₂]
        exact ⟨(z1 - s / dist C D, 1 - (z1 - s / dist C D)),
          ⟨hz1n, hz2n, by ring⟩, rfl⟩
      · have hLenN : pathLength X Y ((z1 - s / dist C D) • C + (1 - (z1 - s / dist C D)) • D) T =
            dist (imgX A B C x1) (imgY B C y1) +
            dist (imgY B C y1) (imgZ B C D (z1 - s / dist C D)) +
            dist (imgZ B C D (z1 - s / dist C D)) (imgT A B C D t1) +
            dist (imgT A B C D t1) (imgX3 A B C D x2) := by
          rw [pathLength, ← dist_imgX_imgY A B C D htet hx1 hx2 hx12 hXe hy1 hy2 hy12 hYe,
            ← dist_imgY_imgZ A B C D htet hy1 hy2 hy12 hYe hz1n hz2n (by ring) rfl,
            ← dist_imgZ_imgT A B C D htet hz1n hz2n (by ring) rfl ht1 ht2 ht12 hTe,
            ← dist_imgT_imgX3 A B C D htet ht1 ht2 ht12 hTe hx1 hx2 hx12 hXe]
        simp only [zero_add, zero_smul, add_zero] at hslt
        rw [dist_comm (imgT A B C D t1) (imgZ B C D z1 + s • e (-(∠ B C D))),
          dist_comm (imgT A B C D t1) (imgZ B C D z1)] at hslt
        rw [hLenN, himgZn, hLen]
        linarith [hslt]
  · -- hinge Y bends: perturbing `Y` along its edge shortens the path
    obtain ⟨s, hsabs, hslt⟩ := exists_smaller_of_hasDerivAt_ne_zero hderY hDY
      (min (y1 * dist B C) ((1 - y1) * dist B C))
      (lt_min (mul_pos hy1 ha) (mul_pos (by linarith [hy1, hy2] : (0:ℝ) < 1 - y1) ha))
    have hy1n : 0 < y1 + s / dist B C := by
      have h1 : |s / dist B C| < y1 := by
        rw [abs_div, abs_of_pos ha, div_lt_iff₀ ha]
        exact lt_of_lt_of_le hsabs (min_le_left _ _)
      have h2 := abs_lt.1 h1
      linarith [h2.1]
    have hy2n : 0 < 1 - (y1 + s / dist B C) := by
      have h1 : |s / dist B C| < 1 - y1 := by
        rw [abs_div, abs_of_pos ha, div_lt_iff₀ ha]
        exact lt_of_lt_of_le hsabs (min_le_right _ _)
      have h2 := abs_lt.1 h1
      linarith [h2.2]
    have himgYn : imgY B C (y1 + s / dist B C) = imgY B C y1 + s • e 0 := by
      rw [imgY, imgY, netC0, netB0]
      rw [show (y1 + s / dist B C) • (dist B C • e 0 - 0) =
          y1 • (dist B C • e 0 - 0) + s • e 0 from by
        rw [add_smul, sub_zero, smul_smul, smul_smul, div_mul_cancel₀ _ ha.ne']]
      module
    refine ⟨X, (y1 + s / dist B C) • B + (1 - (y1 + s / dist B C)) • C, Z, T,
      ⟨hX0, ?_, hZ0, hT0⟩, ?_⟩
    · rw [openSegment_eq_image₂]
      exact ⟨(y1 + s / dist B C, 1 - (y1 + s / dist B C)),
        ⟨hy1n, hy2n, by ring⟩, rfl⟩
    · have hLenN : pathLength X ((y1 + s / dist B C) • B + (1 - (y1 + s / dist B C)) • C) Z T =
          dist (imgX A B C x1) (imgY B C (y1 + s / dist B C)) +
          dist (imgY B C (y1 + s / dist B C)) (imgZ B C D z1) +
          dist (imgZ B C D z1) (imgT A B C D t1) +
          dist (imgT A B C D t1) (imgX3 A B C D x2) := by
        rw [pathLength, ← dist_imgX_imgY A B C D htet hx1 hx2 hx12 hXe hy1n hy2n
          (by ring : y1 + s / dist B C + (1 - (y1 + s / dist B C)) = 1) rfl,
          ← dist_imgY_imgZ A B C D htet hy1n hy2n (by ring) rfl hz1 hz2 hz12 hZe,
          ← dist_imgZ_imgT A B C D htet hz1 hz2 hz12 hZe ht1 ht2 ht12 hTe,
          ← dist_imgT_imgX3 A B C D htet ht1 ht2 ht12 hTe hx1 hx2 hx12 hXe]
      simp only [zero_add, zero_smul, add_zero] at hslt
      rw [dist_comm (imgZ B C D z1) (imgY B C y1 + s • e 0),
        dist_comm (imgZ B C D z1) (imgY B C y1)] at hslt
      rw [hLenN, himgYn, hLen]
      linarith [hslt]


/-- Part (b): if the angle condition holds, there are infinitely many shortest
paths, each of length `2 · AC · sin k` where `2k = ∠BAC + ∠CAD + ∠DAB`. -/
theorem infinite_shortest_paths_of_angle_eq {A B C D : Pt}
    (htet : AffineIndependent ℝ ![A, B, C, D])
    (hABC : AcuteTriangle A B C) (hBCD : AcuteTriangle B C D)
    (hACD : AcuteTriangle A C D) (hABD : AcuteTriangle A B D)
    (hang : ∠ D A B + ∠ B C D = ∠ C D A + ∠ A B C) :
    Set.Infinite {p : Pt × Pt × Pt × Pt |
        IsPath A B C D p.1 p.2.1 p.2.2.1 p.2.2.2 ∧
        pathLength p.1 p.2.1 p.2.2.1 p.2.2.2 = minLength A B C D} ∧
      ∀ X Y Z T : Pt, IsPath A B C D X Y Z T →
        minLength A B C D ≤ pathLength X Y Z T := by
  exact ⟨shortest_paths_infinite A B C D htet hABC hBCD hACD hABD hang,
    fun X Y Z T hp =>
      minLength_le_pathLength_of_condition A B C D htet hABC hBCD hACD hABD hang hp⟩

snip end

problem imo1971_p4 {A B C D : Pt}
    (htet : AffineIndependent ℝ ![A, B, C, D])
    (hABC : AcuteTriangle A B C) (hBCD : AcuteTriangle B C D)
    (hACD : AcuteTriangle A C D) (hABD : AcuteTriangle A B D) :
    (∠ D A B + ∠ B C D ≠ ∠ C D A + ∠ A B C →
      ∀ X Y Z T : Pt, IsPath A B C D X Y Z T →
        ∃ X' Y' Z' T' : Pt, IsPath A B C D X' Y' Z' T' ∧
          pathLength X' Y' Z' T' < pathLength X Y Z T) ∧
    (∠ D A B + ∠ B C D = ∠ C D A + ∠ A B C →
      Set.Infinite {p : Pt × Pt × Pt × Pt |
          IsPath A B C D p.1 p.2.1 p.2.2.1 p.2.2.2 ∧
          pathLength p.1 p.2.1 p.2.2.1 p.2.2.2 = minLength A B C D} ∧
        ∀ X Y Z T : Pt, IsPath A B C D X Y Z T →
          minLength A B C D ≤ pathLength X Y Z T) := by
  exact ⟨fun h X Y Z T hp =>
      no_shortest_path_of_angle_ne htet hABC hBCD hACD hABD h hp,
    fun h => infinite_shortest_paths_of_angle_eq htet hABC hBCD hACD hABD h⟩

end Imo1971P4
