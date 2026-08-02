/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import Mathlib.Analysis.Convex.Between
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Euclidean.Angle.Sphere
public import Mathlib.Geometry.Euclidean.Sphere.SecondInter
public import Mathlib.Geometry.Euclidean.Triangle
public import Mathlib.LinearAlgebra.Dimension.Free
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 1972, Problem 2

Given `n > 4`, prove that every cyclic quadrilateral can be dissected into `n` cyclic
quadrilaterals.

# Formalization notes

We formalize a *dissection* of a quadrilateral as a finite family of cyclic quadrilaterals
whose regions (the convex hulls of their vertices) are contained in the original region,
cover it, and have pairwise disjoint interiors. (Solution after J. Scholes, kalva.)
-/

namespace Imo1972P2

open scoped RealInnerProductSpace

/-- The Euclidean plane, the ambient space of the problem. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

open scoped EuclideanGeometry EuclideanSpace

open EuclideanGeometry

/-- A choice of positive orientation on the plane (needed for the oriented angle `∡`). -/
noncomputable instance : Module.Oriented ℝ Plane (Fin 2) :=
  ⟨Module.Basis.orientation (Module.finBasisOfFinrankEq ℝ Plane finrank_euclideanSpace_fin)⟩

/-- A (nondegenerate, strictly convex) quadrilateral: four points of the plane in convex
position (none of them lies in the convex hull of the other three), listed in boundary
order, as witnessed by the two diagonals `AC` and `BD` meeting strictly inside. -/
structure ConvexQuad (A B C D : Plane) : Prop where
  not_mem₁ : A ∉ convexHull ℝ {B, C, D}
  not_mem₂ : B ∉ convexHull ℝ {C, D, A}
  not_mem₃ : C ∉ convexHull ℝ {D, A, B}
  not_mem₄ : D ∉ convexHull ℝ {A, B, C}
  diagonals : ∃ X : Plane, Sbtw ℝ A X C ∧ Sbtw ℝ B X D

/-- A cyclic quadrilateral: a convex quadrilateral whose four vertices lie on a common
circle. -/
structure CyclicQuad (A B C D : Plane) : Prop where
  convex : ConvexQuad A B C D
  concyclic : ∃ O : Plane, ∃ r : ℝ, dist A O = r ∧ dist B O = r ∧ dist C O = r ∧ dist D O = r

/-- The (closed) quadrilateral region determined by four points: their convex hull. -/
def quadRegion (A B C D : Plane) : Set Plane := convexHull ℝ {A, B, C, D}

/-- A dissection of the quadrilateral `ABCD` into `n` cyclic quadrilaterals: a family of
`n` cyclic quadrilaterals whose regions are contained in the region of `ABCD`, cover it,
and have pairwise disjoint interiors. (Bundled as data; the problem asserts its
`Nonempty`-ness.) -/
structure CyclicDissection (A B C D : Plane) (n : ℕ) where
  pieces : Fin n → Plane × Plane × Plane × Plane
  cyclic : ∀ i, CyclicQuad (pieces i).1 (pieces i).2.1 (pieces i).2.2.1 (pieces i).2.2.2
  subset : ∀ i, quadRegion (pieces i).1 (pieces i).2.1 (pieces i).2.2.1 (pieces i).2.2.2 ⊆
    quadRegion A B C D
  cover : quadRegion A B C D ⊆
    ⋃ i, quadRegion (pieces i).1 (pieces i).2.1 (pieces i).2.2.1 (pieces i).2.2.2
  disjoint : ∀ i j, i ≠ j →
    Disjoint (interior (quadRegion (pieces i).1 (pieces i).2.1 (pieces i).2.2.1
      (pieces i).2.2.2))
      (interior (quadRegion (pieces j).1 (pieces j).2.1 (pieces j).2.2.1 (pieces j).2.2.2))

snip begin

/-- An isosceles trapezoid: a convex quadrilateral with the sides `AB` and `DC` parallel
and the two other sides `BC`, `AD` of equal length. (Any such quadrilateral is cyclic.) -/
structure IsoscelesTrapezoid (A B C D : Plane) : Prop where
  convex : ConvexQuad A B C D
  parallel : ∃ k : ℝ, D - C = k • (B - A)
  legs_eq : dist B C = dist A D

/-- A `lineMap` point with parameter in `(0,1)` is strictly between the endpoints. -/
theorem sbtw_lineMap {x y : Plane} {t : ℝ} (hxy : x ≠ y) (ht0 : 0 < t) (ht1 : t < 1) :
    Sbtw ℝ x (AffineMap.lineMap x y t) y := by
  have hyx : y - x ≠ 0 := sub_ne_zero.mpr hxy.symm
  have hval : AffineMap.lineMap x y t = t • (y - x) + x :=
    AffineMap.lineMap_apply_module' x y t
  refine ⟨⟨t, Set.mem_Icc.mpr ⟨ht0.le, ht1.le⟩, rfl⟩, ?_, ?_⟩
  · intro h
    rw [hval] at h
    have h1 : t • (y - x) = 0 := by
      have h2 := congrArg (· - x) h
      rwa [add_sub_cancel_right, sub_self] at h2
    rcases smul_eq_zero.mp h1 with h3 | h3
    · linarith
    · exact hyx h3
  · intro h
    rw [hval] at h
    have h1 : (t - 1) • (y - x) = 0 := by
      have h2 := congrArg (· - y) h
      rw [show t • (y - x) + x - y = (t - 1) • (y - x) by
        rw [sub_smul, one_smul]; abel] at h2
      rwa [sub_self] at h2
    rcases smul_eq_zero.mp h1 with h3 | h3
    · linarith
    · exact hyx h3

/-- If `x` is a convex combination of `p₁, p₂, p₃` and an inner-product functional strictly
separates `p₁, p₂` from `x` while `p₃` has the same value as `x`, then `x = p₃`. -/
theorem eq_of_mem_convexHull_of_inner {x p₁ p₂ p₃ w : Plane}
    (hmem : x ∈ convexHull ℝ ({p₁, p₂, p₃} : Set Plane)) (hp₁₂ : p₁ ≠ p₂)
    (hd₁ : 0 < ⟪p₁ - x, w⟫) (hd₂ : 0 < ⟪p₂ - x, w⟫) (hd₃ : ⟪p₃ - x, w⟫ = 0) :
    x = p₃ := by
  have hp₁₃ : p₁ ≠ p₃ := fun h ↦ by
    rw [h, hd₃] at hd₁; exact (lt_irrefl _ hd₁)
  have hp₂₃ : p₂ ≠ p₃ := fun h ↦ by
    rw [h, hd₃] at hd₂; exact (lt_irrefl _ hd₂)
  have hset : ({p₁, p₂, p₃} : Set Plane) = (({p₁, p₂, p₃} : Finset Plane) : Set Plane) := by
    simp
  rw [hset] at hmem
  obtain ⟨wt, hwt0, hwt1, hwt2⟩ := Finset.mem_convexHull'.mp hmem
  have hp₁ : p₁ ∉ ({p₂, p₃} : Finset Plane) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hp₁₂, hp₁₃⟩
  have hp₂ : p₂ ∉ ({p₃} : Finset Plane) := by
    simp only [Finset.mem_singleton]; exact hp₂₃
  have hmem₁ : p₁ ∈ ({p₁, p₂, p₃} : Finset Plane) := Finset.mem_insert_self _ _
  have hmem₂ : p₂ ∈ ({p₁, p₂, p₃} : Finset Plane) :=
    Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hmem₃ : p₃ ∈ ({p₁, p₂, p₃} : Finset Plane) :=
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hsub : ∑ y ∈ ({p₁, p₂, p₃} : Finset Plane), wt y • (y - x) = 0 := by
    have hcongr : ∀ y ∈ ({p₁, p₂, p₃} : Finset Plane), wt y • (y - x) = wt y • y - wt y • x :=
      fun y _ ↦ smul_sub (wt y) y x
    rw [Finset.sum_congr rfl hcongr, Finset.sum_sub_distrib, hwt2, ← Finset.sum_smul, hwt1,
      one_smul, sub_self]
  have hsum : ∑ y ∈ ({p₁, p₂, p₃} : Finset Plane), wt y * ⟪y - x, w⟫ = 0 := by
    have hcalc : ∑ y ∈ ({p₁, p₂, p₃} : Finset Plane), wt y * ⟪y - x, w⟫ =
        ⟪∑ y ∈ ({p₁, p₂, p₃} : Finset Plane), wt y • (y - x), w⟫ := by
      rw [sum_inner]
      exact Finset.sum_congr rfl fun y _ ↦ (real_inner_smul_left (y - x) w (wt y)).symm
    rw [hcalc, hsub, inner_zero_left]
  rw [Finset.sum_insert hp₁, Finset.sum_insert hp₂, Finset.sum_singleton, hd₃, mul_zero,
    add_zero] at hsum
  have hw₁ : wt p₁ = 0 := by
    have h1 : 0 ≤ wt p₁ * ⟪p₁ - x, w⟫ := mul_nonneg (hwt0 p₁ hmem₁) hd₁.le
    have h2 : 0 ≤ wt p₂ * ⟪p₂ - x, w⟫ := mul_nonneg (hwt0 p₂ hmem₂) hd₂.le
    by_cases hp : 0 < wt p₁
    · have h3 : 0 < wt p₁ * ⟪p₁ - x, w⟫ := mul_pos hp hd₁
      linarith
    · exact le_antisymm (not_lt.mp hp) (hwt0 p₁ hmem₁)
  rw [hw₁, zero_mul, zero_add] at hsum
  have hw₂ : wt p₂ = 0 := by
    have h2 : 0 ≤ wt p₂ * ⟪p₂ - x, w⟫ := mul_nonneg (hwt0 p₂ hmem₂) hd₂.le
    by_cases hp : 0 < wt p₂
    · have h3 : 0 < wt p₂ * ⟪p₂ - x, w⟫ := mul_pos hp hd₂
      linarith
    · exact le_antisymm (not_lt.mp hp) (hwt0 p₂ hmem₂)
  have hw₃ : wt p₃ = 1 := by
    have h1 := hwt1
    rw [Finset.sum_insert hp₁, Finset.sum_insert hp₂, Finset.sum_singleton, hw₁, hw₂,
      zero_add, zero_add] at h1
    exact h1
  rw [Finset.sum_insert hp₁, Finset.sum_insert hp₂, Finset.sum_singleton, hw₁, hw₂, hw₃,
    zero_smul, zero_smul, one_smul, zero_add, zero_add] at hwt2
  exact hwt2.symm

/-- A trapezoid built from orthogonal data is a strictly convex quadrilateral: if `e ≠ 0`,
`w ≠ 0`, `⟪e, w⟫ = 0`, `0 < h` and `λ < κ`, then `A`, `A + e`, `A + κ • e + h • w`,
`A + λ • e + h • w` are, in this order, the vertices of a strictly convex quadrilateral. -/
theorem convexQuad_of_ortho {A e w : Plane} (he : e ≠ 0) (hw : w ≠ 0)
    (horth : ⟪e, w⟫ = 0) {h μ κ : ℝ} (hh : 0 < h) (hκμ : μ < κ) :
    ConvexQuad A (A + e) (A + κ • e + h • w) (A + μ • e + h • w) := by
  have hww : 0 < ⟪w, w⟫ := real_inner_self_pos.mpr hw
  have hhw : 0 < h * ⟪w, w⟫ := mul_pos hh hww
  have horth' : ⟪w, e⟫ = 0 := by rw [real_inner_comm e w]; exact horth
  -- inner-product values relative to `w`
  have hKw : ⟪κ • e + h • w, w⟫ = h * ⟪w, w⟫ := by
    rw [inner_add_left, real_inner_smul_left, horth, mul_zero, zero_add,
      real_inner_smul_left]
  have hLw : ⟪μ • e + h • w, w⟫ = h * ⟪w, w⟫ := by
    rw [inner_add_left, real_inner_smul_left, horth, mul_zero, zero_add,
      real_inner_smul_left]
  have hKL : A + κ • e + h • w ≠ A + μ • e + h • w := by
    intro h'
    have h1 : (κ - μ) • e = 0 := by
      have h2 := congrArg (· - (A + μ • e + h • w)) h'
      rw [show A + κ • e + h • w - (A + μ • e + h • w) = (κ - μ) • e by
        rw [sub_smul]; abel] at h2
      rwa [sub_self] at h2
    rcases smul_eq_zero.mp h1 with h3 | h3
    · linarith
    · exact he h3
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- A ∉ convexHull {A+e, A+κe+hw, A+μe+hw}
    intro hmem
    have hd₁ : 0 < ⟪(A + κ • e + h • w) - A, w⟫ := by
      rw [show A + κ • e + h • w - A = κ • e + h • w by abel, hKw]; exact hhw
    have hd₂ : 0 < ⟪(A + μ • e + h • w) - A, w⟫ := by
      rw [show A + μ • e + h • w - A = μ • e + h • w by abel, hLw]; exact hhw
    have hd₃ : ⟪(A + e) - A, w⟫ = 0 := by
      rw [show A + e - A = e by abel, horth]
    rw [show ({A + e, A + κ • e + h • w, A + μ • e + h • w} : Set Plane) =
        {A + κ • e + h • w, A + μ • e + h • w, A + e} by
      rw [Set.insert_comm (A + e) (A + κ • e + h • w) {A + μ • e + h • w},
        Set.pair_comm (A + e) (A + μ • e + h • w)]] at hmem
    have hx := eq_of_mem_convexHull_of_inner hmem hKL hd₁ hd₂ hd₃
    have heq : e = 0 := by
      have h2 := congrArg (· - A) hx
      rw [sub_self, add_sub_cancel_left] at h2
      exact h2.symm
    exact he heq
  · -- A+e ∉ convexHull {A+κe+hw, A+μe+hw, A}
    intro hmem
    have hd₁ : 0 < ⟪(A + κ • e + h • w) - (A + e), w⟫ := by
      rw [show (A + κ • e + h • w) - (A + e) = (κ - 1) • e + h • w by
        rw [sub_smul, one_smul]; abel]
      rw [inner_add_left, real_inner_smul_left, horth, mul_zero, zero_add,
        real_inner_smul_left]
      exact hhw
    have hd₂ : 0 < ⟪(A + μ • e + h • w) - (A + e), w⟫ := by
      rw [show (A + μ • e + h • w) - (A + e) = (μ - 1) • e + h • w by
        rw [sub_smul, one_smul]; abel]
      rw [inner_add_left, real_inner_smul_left, horth, mul_zero, zero_add,
        real_inner_smul_left]
      exact hhw
    have hd₃ : ⟪A - (A + e), w⟫ = 0 := by
      rw [show A - (A + e) = -e by abel]
      rw [inner_neg_left, horth, neg_zero]
    have hx := eq_of_mem_convexHull_of_inner hmem hKL hd₁ hd₂ hd₃
    have heq : e = 0 := by
      have h2 := congrArg (· - A) hx
      rwa [add_sub_cancel_left, sub_self] at h2
    exact he heq
  · -- A+κe+hw ∉ convexHull {A+μe+hw, A, A+e}
    intro hmem
    have hd₁ : 0 < ⟪A - (A + κ • e + h • w), -w⟫ := by
      rw [inner_neg_right]
      rw [show A - (A + κ • e + h • w) = -(κ • e + h • w) by abel]
      rw [inner_neg_left, hKw]
      linarith [hhw]
    have hd₂ : 0 < ⟪(A + e) - (A + κ • e + h • w), -w⟫ := by
      rw [show (A + e) - (A + κ • e + h • w) = (1 - κ) • e - h • w by
        rw [sub_smul, one_smul]; abel]
      rw [inner_neg_right, inner_sub_left, real_inner_smul_left, horth, mul_zero,
        real_inner_smul_left, zero_sub]
      linarith [hhw]
    have hd₃ : ⟪(A + μ • e + h • w) - (A + κ • e + h • w), -w⟫ = 0 := by
      rw [show (A + μ • e + h • w) - (A + κ • e + h • w) = (μ - κ) • e by
        rw [sub_smul]; abel]
      rw [inner_neg_right, real_inner_smul_left, horth, mul_zero, neg_zero]
    rw [show ({A + μ • e + h • w, A, A + e} : Set Plane) = {A, A + e, A + μ • e + h • w} by
      rw [Set.insert_comm (A + μ • e + h • w) A {A + e},
        Set.pair_comm (A + μ • e + h • w) (A + e)]] at hmem
    have hx := eq_of_mem_convexHull_of_inner hmem (by
      intro h'
      have h2 := congrArg (· - A) h'
      rw [sub_self, add_sub_cancel_left] at h2
      exact he h2.symm) hd₁ hd₂ hd₃
    exact hKL hx
  · -- A+μe+hw ∉ convexHull {A, A+e, A+κe+hw}
    intro hmem
    have hd₁ : 0 < ⟪A - (A + μ • e + h • w), -w⟫ := by
      rw [show A - (A + μ • e + h • w) = -(μ • e + h • w) by abel]
      rw [inner_neg_right, inner_neg_left, hLw]
      linarith [hhw]
    have hd₂ : 0 < ⟪(A + e) - (A + μ • e + h • w), -w⟫ := by
      rw [show (A + e) - (A + μ • e + h • w) = (1 - μ) • e - h • w by
        rw [sub_smul, one_smul]; abel]
      rw [inner_neg_right, inner_sub_left, real_inner_smul_left, horth, mul_zero,
        real_inner_smul_left, zero_sub]
      linarith [hhw]
    have hd₃ : ⟪(A + κ • e + h • w) - (A + μ • e + h • w), -w⟫ = 0 := by
      rw [show (A + κ • e + h • w) - (A + μ • e + h • w) = (κ - μ) • e by
        rw [sub_smul]; abel]
      rw [inner_neg_right, real_inner_smul_left, horth, mul_zero, neg_zero]
    have hx := eq_of_mem_convexHull_of_inner hmem (by
      intro h'
      have h2 := congrArg (· - A) h'
      rw [sub_self, add_sub_cancel_left] at h2
      exact he h2.symm) hd₁ hd₂ hd₃
    exact hKL hx.symm
  · -- diagonals
    set t : ℝ := (1 + κ - μ)⁻¹ with ht
    have hdpos : 0 < 1 + κ - μ := by linarith
    have ht0 : 0 < t := inv_pos.mpr hdpos
    have ht1 : t < 1 := by
      rw [ht]
      exact inv_lt_one_of_one_lt₀ (by linarith)
    have ht' : t * (1 + κ - μ) = 1 := by
      rw [ht]
      exact inv_mul_cancel₀ hdpos.ne'
    have hK0 : κ • e + h • w ≠ 0 := by
      intro h'
      have : ⟪κ • e + h • w, w⟫ = 0 := by rw [h', inner_zero_left]
      rw [hKw] at this
      linarith [hhw]
    have hBL : A + e ≠ A + μ • e + h • w := by
      intro h'
      have h1 : e = μ • e + h • w := by
        have h2 := congrArg (· - A) h'
        rwa [show A + e - A = e by abel,
          show A + μ • e + h • w - A = μ • e + h • w by abel] at h2
      have h2 : ⟪e, w⟫ = ⟪μ • e + h • w, w⟫ := congrArg (fun x ↦ ⟪x, w⟫) h1
      rw [horth, hLw] at h2
      exact hhw.ne' h2.symm
    refine ⟨A + t • (κ • e + h • w), ?_, ?_⟩
    · have hX1 : A + t • (κ • e + h • w) =
          AffineMap.lineMap A (A + κ • e + h • w) t := by
        rw [AffineMap.lineMap_apply_module',
          show A + κ • e + h • w - A = κ • e + h • w by abel, add_comm]
      rw [hX1]
      exact sbtw_lineMap (x := A) (y := A + κ • e + h • w) (fun h' ↦ by
        have h2 := congrArg (· - A) h'
        rw [sub_self, show A + κ • e + h • w - A = κ • e + h • w by abel] at h2
        exact hK0 h2.symm) ht0 ht1
    · have hX2 : A + t • (κ • e + h • w) =
          AffineMap.lineMap (A + e) (A + μ • e + h • w) t := by
        rw [AffineMap.lineMap_apply_module']
        have he_eq : t * (μ - 1) + 1 = t * κ := by linarith [ht']
        rw [show A + μ • e + h • w - (A + e) = (μ - 1) • e + h • w by
          rw [sub_smul, one_smul]; abel]
        simp only [smul_add, smul_smul]
        have heq2 : (t * (μ - 1)) • e + e = (t * κ) • e := by
          have h3 := congrArg (· • e) he_eq
          rwa [add_smul, one_smul] at h3
        have hvec : (t * (μ - 1)) • e + (t * h) • w + (A + e) =
            A + (t * κ) • e + (t * h) • w := by
          rw [show (t * (μ - 1)) • e + (t * h) • w + (A + e) =
              (((t * (μ - 1)) • e + e) + (t * h) • w) + A by abel, heq2]
          abel
        rw [hvec]
        abel
      rw [hX2]
      exact sbtw_lineMap (x := A + e) (y := A + μ • e + h • w) hBL ht0 ht1

/-- Points in the "band" between the two parallel sides of a trapezoid lie in the
trapezoid: if `0 < h`, `μ < κ`, `0 ≤ s ≤ h` and `(s/h)·μ ≤ ξ ≤ 1 + (s/h)·(κ−1)`, then
`A + ξ•e + s•w ∈ convexHull {A, A+e, A+κe+hw, A+μe+hw}`. -/
theorem mem_convexHull_trapezoid_band {A e w : Plane} {h μ κ ξ s : ℝ} (hh : 0 < h)
    (hμκ : μ < κ) (hs0 : 0 ≤ s) (hsh : s ≤ h) (hξl : s / h * μ ≤ ξ)
    (hξu : ξ ≤ 1 + s / h * (κ - 1)) :
    A + ξ • e + s • w ∈ convexHull ℝ {A, A + e, A + κ • e + h • w, A + μ • e + h • w} := by
  have hA : A ∈ ({A, A + e, A + κ • e + h • w, A + μ • e + h • w} : Set Plane) :=
    Set.mem_insert _ _
  have hB : A + e ∈ ({A, A + e, A + κ • e + h • w, A + μ • e + h • w} : Set Plane) :=
    Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  have hK : A + κ • e + h • w ∈
      ({A, A + e, A + κ • e + h • w, A + μ • e + h • w} : Set Plane) :=
    Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hL : A + μ • e + h • w ∈
      ({A, A + e, A + κ • e + h • w, A + μ • e + h • w} : Set Plane) :=
    Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
      (Set.mem_singleton _)))
  have hh0 : h ≠ 0 := hh.ne'
  by_cases h1 : s = 0
  · subst h1
    rw [zero_smul, add_zero]
    have hξ0 : 0 ≤ ξ := by
      have h2 := hξl
      rw [zero_div, zero_mul] at h2
      exact h2
    have hξ1 : ξ ≤ 1 := by
      have h2 := hξu
      rw [zero_div, zero_mul, add_zero] at h2
      exact h2
    apply Convex.segment_subset (convex_convexHull ℝ _) ((subset_convexHull ℝ _) hA)
      ((subset_convexHull ℝ _) hB)
    exact ⟨1 - ξ, ξ, sub_nonneg.mpr hξ1, hξ0, sub_add_cancel 1 ξ, by module⟩
  · by_cases h2 : s = h
    · rw [h2] at hξl hξu ⊢
      rw [div_self hh0, one_mul] at hξl hξu
      have hκμ : 0 < κ - μ := sub_pos.mpr hμκ
      have hq0 : 0 ≤ (ξ - μ) / (κ - μ) := div_nonneg (sub_nonneg.mpr hξl) hκμ.le
      have hq1 : (ξ - μ) / (κ - μ) ≤ 1 := by
        rw [div_le_one hκμ]
        linarith [hξu]
      have hid : (1 - (ξ - μ) / (κ - μ)) • (A + μ • e + h • w) +
          ((ξ - μ) / (κ - μ)) • (A + κ • e + h • w) = A + ξ • e + h • w := by
        rw [show (1 - (ξ - μ) / (κ - μ)) • (A + μ • e + h • w) +
            ((ξ - μ) / (κ - μ)) • (A + κ • e + h • w) =
            A + ((1 - (ξ - μ) / (κ - μ)) * μ + (ξ - μ) / (κ - μ) * κ) • e +
              ((1 - (ξ - μ) / (κ - μ)) * h + (ξ - μ) / (κ - μ) * h) • w by module]
        rw [show (1 - (ξ - μ) / (κ - μ)) * μ + (ξ - μ) / (κ - μ) * κ = ξ by
          field_simp [hκμ.ne']; ring,
          show (1 - (ξ - μ) / (κ - μ)) * h + (ξ - μ) / (κ - μ) * h = h by
          field_simp [hκμ.ne']; ring]
      apply Convex.segment_subset (convex_convexHull ℝ _) ((subset_convexHull ℝ _) hL)
        ((subset_convexHull ℝ _) hK)
      exact ⟨1 - (ξ - μ) / (κ - μ), (ξ - μ) / (κ - μ), sub_nonneg.mpr hq1, hq0,
        sub_add_cancel 1 _, hid⟩
    · have hs_pos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm h1)
      have hsh' : s < h := lt_of_le_of_ne hsh h2
      have hu0 : 0 < s / h := div_pos hs_pos hh
      have hu1 : s / h < 1 := (div_lt_one hh).mpr hsh'
      have hT1 : ξ - s / h * μ ≤ (1 - s / h) + s / h * (κ - μ) := by
        linarith [hξu]
      by_cases hT : ξ - s / h * μ ≤ 1 - s / h
      · have hu : 0 < 1 - s / h := sub_pos.mpr hu1
        have hy0 : 0 ≤ (ξ - s / h * μ) / (1 - s / h) :=
          div_nonneg (sub_nonneg.mpr hξl) hu.le
        have hy1 : (ξ - s / h * μ) / (1 - s / h) ≤ 1 := (div_le_one hu).mpr hT
        have hY : A + ((ξ - s / h * μ) / (1 - s / h)) • e ∈ convexHull ℝ
            {A, A + e, A + κ • e + h • w, A + μ • e + h • w} := by
          apply Convex.segment_subset (convex_convexHull ℝ _) ((subset_convexHull ℝ _) hA)
            ((subset_convexHull ℝ _) hB)
          exact ⟨1 - (ξ - s / h * μ) / (1 - s / h), (ξ - s / h * μ) / (1 - s / h),
            sub_nonneg.mpr hy1, hy0, sub_add_cancel 1 _, by module⟩
        have hid : (1 - s / h) • (A + ((ξ - s / h * μ) / (1 - s / h)) • e) +
            (s / h) • (A + μ • e + h • w) = A + ξ • e + s • w := by
          rw [show (1 - s / h) • (A + ((ξ - s / h * μ) / (1 - s / h)) • e) +
              (s / h) • (A + μ • e + h • w) =
              A + ((1 - s / h) * ((ξ - s / h * μ) / (1 - s / h)) + (s / h) * μ) • e +
                ((s / h) * h) • w by module]
          rw [show (1 - s / h) * ((ξ - s / h * μ) / (1 - s / h)) + (s / h) * μ = ξ by
            field_simp [hu.ne']; ring,
            show (s / h) * h = s by field_simp [hh0]]
        apply Convex.segment_subset (convex_convexHull ℝ _) hY ((subset_convexHull ℝ _) hL)
        exact ⟨1 - s / h, s / h, sub_nonneg.mpr hu1.le, hu0.le, sub_add_cancel 1 _, hid⟩
      · push_neg at hT
        have hu : 0 < s / h * (κ - μ) := mul_pos hu0 (sub_pos.mpr hμκ)
        have hq0 : 0 ≤ (ξ - s / h * μ - (1 - s / h)) / (s / h * (κ - μ)) :=
          div_nonneg (sub_nonneg.mpr hT.le) hu.le
        have hq1 : (ξ - s / h * μ - (1 - s / h)) / (s / h * (κ - μ)) ≤ 1 := by
          rw [div_le_one hu]
          linarith [hT1]
        set q := (ξ - s / h * μ - (1 - s / h)) / (s / h * (κ - μ)) with hqdef
        have hQ : (1 - q) • (A + μ • e + h • w) + q • (A + κ • e + h • w) ∈
            convexHull ℝ {A, A + e, A + κ • e + h • w, A + μ • e + h • w} := by
          apply Convex.segment_subset (convex_convexHull ℝ _) ((subset_convexHull ℝ _) hL)
            ((subset_convexHull ℝ _) hK)
          exact ⟨1 - q, q, sub_nonneg.mpr hq1, hq0, sub_add_cancel 1 _, by module⟩
        have hid : (1 - s / h) • (A + e) + (s / h) • ((1 - q) • (A + μ • e + h • w) +
            q • (A + κ • e + h • w)) = A + ξ • e + s • w := by
          rw [hqdef]
          rw [show (1 - s / h) • (A + e) +
              (s / h) • ((1 - (ξ - s / h * μ - (1 - s / h)) / (s / h * (κ - μ))) •
                (A + μ • e + h • w) +
              ((ξ - s / h * μ - (1 - s / h)) / (s / h * (κ - μ))) •
                (A + κ • e + h • w)) =
              A + ((1 - s / h) + (s / h) * ((1 - (ξ - s / h * μ - (1 - s / h)) /
                  (s / h * (κ - μ))) * μ +
                ((ξ - s / h * μ - (1 - s / h)) / (s / h * (κ - μ))) * κ)) • e +
                ((s / h) * h) • w by module]
          rw [show (1 - s / h) + (s / h) * ((1 - (ξ - s / h * μ - (1 - s / h)) /
                (s / h * (κ - μ))) * μ +
              ((ξ - s / h * μ - (1 - s / h)) / (s / h * (κ - μ))) * κ) = ξ by
            field_simp [hu0.ne', (sub_pos.mpr hμκ).ne']; ring,
            show (s / h) * h = s by field_simp [hh0]]
        apply Convex.segment_subset (convex_convexHull ℝ _) ((subset_convexHull ℝ _) hB) hQ
        exact ⟨1 - s / h, s / h, sub_nonneg.mpr hu1.le, hu0.le, sub_add_cancel 1 _, hid⟩

/-- In the plane, every vector decomposes along two orthogonal nonzero vectors. -/
theorem eq_smul_add_smul_of_ortho {e w : Plane} (he : e ≠ 0) (hw : w ≠ 0)
    (horth : ⟪e, w⟫ = 0) (v : Plane) :
    v = (⟪v, e⟫ / ⟪e, e⟫) • e + (⟪v, w⟫ / ⟪w, w⟫) • w := by
  have hee : ⟪e, e⟫ ≠ 0 := fun h ↦ he (inner_self_eq_zero.mp h)
  have hww : ⟪w, w⟫ ≠ 0 := fun h ↦ hw (inner_self_eq_zero.mp h)
  have horth' : ⟪w, e⟫ = 0 := by rw [real_inner_comm e w]; exact horth
  have hind : LinearIndependent ℝ ![e, w] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    rw [Fin.sum_univ_two] at hg
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hg
    have h0 : g 0 = 0 := by
      have h1 : ⟪g 0 • e + g 1 • w, e⟫ = 0 := by rw [hg, inner_zero_left]
      rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, horth', mul_zero,
        add_zero] at h1
      exact (mul_eq_zero.mp h1).resolve_right hee
    fin_cases i
    · exact h0
    · rw [h0, zero_smul, zero_add] at hg
      exact (smul_eq_zero.mp hg).resolve_right hw
  have hspan : Submodule.span ℝ (Set.range ![e, w]) = ⊤ :=
    hind.span_eq_top_of_card_eq_finrank' (by simp [finrank_euclideanSpace])
  set ξ := ⟪v, e⟫ / ⟪e, e⟫ with hξ
  set η := ⟪v, w⟫ / ⟪w, w⟫ with hη
  have hv'e : ⟪e, v - ξ • e - η • w⟫ = 0 := by
    rw [inner_sub_right, inner_sub_right, real_inner_smul_right, real_inner_smul_right,
      horth, hξ, real_inner_comm v e]
    field_simp
    ring
  have hv'w : ⟪w, v - ξ • e - η • w⟫ = 0 := by
    rw [inner_sub_right, inner_sub_right, real_inner_smul_right, real_inner_smul_right,
      horth', hη, real_inner_comm v w]
    field_simp
    ring
  have hv'mem : v - ξ • e - η • w ∈ (Submodule.span ℝ (Set.range ![e, w]))ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro u hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
      rcases Set.mem_range.mp hu with ⟨i, rfl⟩
      fin_cases i
      · simpa using hv'e
      · simpa using hv'w
    | zero => exact inner_zero_left _
    | add u₁ u₂ _ _ hu₁ hu₂ => rw [inner_add_left, hu₁, hu₂, add_zero]
    | smul a u₁ _ hu₁ => rw [real_inner_smul_left, hu₁, mul_zero]
  rw [hspan] at hv'mem
  have hself : ⟪v - ξ • e - η • w, v - ξ • e - η • w⟫ = 0 :=
    Submodule.inner_right_of_mem_orthogonal Submodule.mem_top hv'mem
  have hz : v - ξ • e - η • w = 0 := inner_self_eq_zero.mp hself
  rw [sub_sub, sub_eq_zero] at hz
  exact hz

/-- The 2D scalar cross product. -/
def ω (u v : Plane) : ℝ := u 0 * v 1 - u 1 * v 0

theorem ω_self (u : Plane) : ω u u = 0 := by
  simp only [ω]
  ring

theorem ω_add_left (u v w' : Plane) : ω (u + v) w' = ω u w' + ω v w' := by
  simp only [ω, PiLp.add_apply]
  ring

theorem ω_add_right (u v w' : Plane) : ω w' (u + v) = ω w' u + ω w' v := by
  simp only [ω, PiLp.add_apply]
  ring

theorem ω_sub_left (u v w' : Plane) : ω (u - v) w' = ω u w' - ω v w' := by
  simp only [ω, PiLp.sub_apply]
  ring

theorem ω_sub_right (u v w' : Plane) : ω w' (u - v) = ω w' u - ω w' v := by
  simp only [ω, PiLp.sub_apply]
  ring

theorem ω_smul_left (c : ℝ) (u v : Plane) : ω (c • u) v = c * ω u v := by
  simp only [ω, PiLp.smul_apply, smul_eq_mul]
  ring

theorem ω_smul_right (c : ℝ) (u v : Plane) : ω u (c • v) = c * ω u v := by
  simp only [ω, PiLp.smul_apply, smul_eq_mul]
  ring

theorem ω_neg_left (u v : Plane) : ω (-u) v = -ω u v := by
  simp only [ω, PiLp.neg_apply]
  ring

theorem ω_neg_right (u v : Plane) : ω u (-v) = -ω u v := by
  simp only [ω, PiLp.neg_apply]
  ring

theorem ω_comm (u v : Plane) : ω u v = -ω v u := by
  simp only [ω]
  ring

/-- `ω` as a linear map in the left argument. -/
def ωL (v : Plane) : Plane →ₗ[ℝ] ℝ where
  toFun := fun u ↦ ω u v
  map_add' := fun u₁ u₂ ↦ ω_add_left u₁ u₂ v
  map_smul' := fun c u ↦ ω_smul_left c u v

/-- `ω` as a linear map in the right argument. -/
def ωR (u : Plane) : Plane →ₗ[ℝ] ℝ where
  toFun := fun v ↦ ω u v
  map_add' := fun v₁ v₂ ↦ ω_add_right v₁ v₂ u
  map_smul' := fun c v ↦ ω_smul_right c u v

@[simp] theorem ωL_apply (v u : Plane) : ωL v u = ω u v := rfl
@[simp] theorem ωR_apply (u v : Plane) : ωR u v = ω u v := rfl

theorem ω_zero_left (v : Plane) : ω 0 v = 0 := by
  simp only [ω, PiLp.zero_apply, zero_mul, sub_zero]

theorem ω_zero_right (u : Plane) : ω u 0 = 0 := by
  simp only [ω, PiLp.zero_apply, mul_zero, sub_zero]

/-- If `ω a b = 0` with `a ≠ 0`, then `b` is a scalar multiple of `a`. -/
theorem exists_smul_of_ω_eq_zero {a b : Plane} (ha : a ≠ 0) (h : ω a b = 0) :
    ∃ t : ℝ, b = t • a := by
  by_cases hx0 : a 0 ≠ 0
  · refine ⟨b 0 / a 0, ?_⟩
    have h1 : b 1 * a 0 = b 0 * a 1 := by
      have h2 := h
      simp only [ω] at h2
      linarith
    have e0 : b 0 = (b 0 / a 0) * a 0 := by
      field_simp [hx0]
    have e1 : b 1 = (b 0 / a 0) * a 1 := by
      field_simp [hx0]
      linarith [h1]
    ext i
    fin_cases i
    · simpa [Fin.zero_eta, PiLp.smul_apply, smul_eq_mul] using e0
    · simpa [Fin.mk_one, PiLp.smul_apply, smul_eq_mul] using e1
  · have hx00 : a 0 = 0 := of_not_not hx0
    have hx1 : a 1 ≠ 0 := by
      intro h1
      apply ha
      ext i
      fin_cases i
      · simpa [Fin.zero_eta, hx00]
      · simpa [Fin.mk_one, h1]
    refine ⟨b 1 / a 1, ?_⟩
    have h1 : b 0 * a 1 = b 1 * a 0 := by
      have h2 := h
      simp only [ω] at h2
      linarith
    rw [hx00, mul_zero] at h1
    have hy0 : b 0 = 0 := (mul_eq_zero.mp h1).resolve_right hx1
    have e0 : b 0 = (b 1 / a 1) * a 0 := by
      rw [hx00, mul_zero]
      exact hy0
    have e1 : b 1 = (b 1 / a 1) * a 1 := by
      field_simp [hx1]
    ext i
    fin_cases i
    · simpa [Fin.zero_eta, PiLp.smul_apply, smul_eq_mul] using e0
    · simpa [Fin.mk_one, PiLp.smul_apply, smul_eq_mul] using e1

/-- If `ω a b ≠ 0`, then `a b` span the plane, with Cramer's rule coefficients. -/
theorem eq_smul_add_smul_of_ω {a b : Plane} (h : ω a b ≠ 0) (v : Plane) :
    v = (ω v b / ω a b) • a + (ω a v / ω a b) • b := by
  have hb : b ≠ 0 := fun hb ↦ h (by rw [hb, ω_zero_right])
  have hC : ∀ (x y : Plane), x ≠ 0 → ω x y = 0 → ∃ t : ℝ, y = t • x := by
    intro x y hx hxy
    by_cases hx0 : x 0 ≠ 0
    · refine ⟨y 0 / x 0, ?_⟩
      have h1 : y 1 * x 0 = y 0 * x 1 := by
        have h2 := hxy
        simp only [ω] at h2
        linarith
      have e0 : y 0 = (y 0 / x 0) * x 0 := by
        field_simp [hx0]
      have e1 : y 1 = (y 0 / x 0) * x 1 := by
        field_simp [hx0]
        linarith [h1]
      ext i
      fin_cases i
      · simpa [Fin.zero_eta, PiLp.smul_apply, smul_eq_mul] using e0
      · simpa [Fin.mk_one, PiLp.smul_apply, smul_eq_mul] using e1
    · have hx00 : x 0 = 0 := of_not_not hx0
      have hx1 : x 1 ≠ 0 := by
        intro h1
        apply hx
        ext i
        fin_cases i
        · simpa [Fin.zero_eta, hx00]
        · simpa [Fin.mk_one, h1]
      refine ⟨y 1 / x 1, ?_⟩
      have h1 : y 0 * x 1 = y 1 * x 0 := by
        have h2 := hxy
        simp only [ω] at h2
        linarith
      rw [hx00, mul_zero] at h1
      have hy0 : y 0 = 0 := (mul_eq_zero.mp h1).resolve_right hx1
      have e0 : y 0 = (y 1 / x 1) * x 0 := by
        rw [hx00, mul_zero]
        exact hy0
      have e1 : y 1 = (y 1 / x 1) * x 1 := by
        field_simp [hx1]
      ext i
      fin_cases i
      · simpa [Fin.zero_eta, PiLp.smul_apply, smul_eq_mul] using e0
      · simpa [Fin.mk_one, PiLp.smul_apply, smul_eq_mul] using e1
  set c₁ := ω v b / ω a b with hc₁
  set c₂ := ω a v / ω a b with hc₂
  have hRb : ω (v - c₁ • a - c₂ • b) b = 0 := by
    rw [ω_sub_left, ω_sub_left, ω_smul_left, ω_smul_left, ω_self, hc₁]
    field_simp [h]
    ring
  have haR : ω a (v - c₁ • a - c₂ • b) = 0 := by
    rw [ω_sub_right, ω_sub_right, ω_smul_right, ω_smul_right, ω_self, hc₂]
    field_simp [h]
    ring
  have hbR : ω b (v - c₁ • a - c₂ • b) = 0 := by
    have h2 := hRb
    rw [ω_comm] at h2
    exact neg_eq_zero.mp h2
  obtain ⟨t, ht⟩ := hC b (v - c₁ • a - c₂ • b) hb hbR
  have ht0 : t = 0 := by
    have h1 : ω a (v - c₁ • a - c₂ • b) = ω a (t • b) := by rw [ht]
    rw [haR, ω_smul_right] at h1
    have h2 : t * ω a b = 0 := h1.symm
    exact (mul_eq_zero.mp h2).resolve_right h
  have hR : v - c₁ • a - c₂ • b = 0 := by rw [ht, ht0, zero_smul]
  rw [sub_sub, sub_eq_zero] at hR
  exact hR

/-- If an affine functional `c + L·` strictly separates `x` from all points of `s`, then
`x` is not in the convex hull of `s`. -/
theorem not_mem_convexHull_of_forall_lt {x : Plane} {s : Set Plane} {L : Plane →ₗ[ℝ] ℝ}
    {c : ℝ} (h : ∀ y ∈ s, c + L y < c + L x) : x ∉ convexHull ℝ s := by
  have hconv : Convex ℝ {y : Plane | c + L y < c + L x} := by
    intro a ha b hb c₁ d₁ hc₁ hd₁ hcd
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_add, map_smul, map_smul]
    simp only [smul_eq_mul]
    rcases hc₁.eq_or_lt with rfl | hcp
    · rw [zero_add] at hcd
      subst hcd
      simpa using hb
    · have h1 : c₁ * (c + L a) < c₁ * (c + L x) := mul_lt_mul_of_pos_left ha hcp
      have h2 : d₁ * (c + L b) ≤ d₁ * (c + L x) := mul_le_mul_of_nonneg_left hb.le hd₁
      have h3 : c₁ * (c + L x) + d₁ * (c + L x) = c + L x := by
        rw [← add_mul, hcd, one_mul]
      have h4 : c₁ * (c + L a) + d₁ * (c + L b) < c + L x := by
        rw [← h3]
        exact add_lt_add_of_lt_of_le h1 h2
      have h5 : c₁ * (c + L a) + d₁ * (c + L b) = c + (c₁ * L a + d₁ * L b) := by
        rw [mul_add, mul_add]
        have h6 : c₁ * c + c₁ * L a + (d₁ * c + d₁ * L b) =
            (c₁ + d₁) * c + (c₁ * L a + d₁ * L b) := by ring
        rw [h6, hcd, one_mul]
      rw [h5] at h4
      exact h4
  have hsub : convexHull ℝ s ⊆ {y : Plane | c + L y < c + L x} := convexHull_min h hconv
  intro hmem
  have h1 : c + L x < c + L x := hsub hmem
  exact absurd h1 (not_lt.mpr le_rfl)

/-- The `>` version of `not_mem_convexHull_of_forall_lt`. -/
theorem not_mem_convexHull_of_forall_gt {x : Plane} {s : Set Plane} {L : Plane →ₗ[ℝ] ℝ}
    {c : ℝ} (h : ∀ y ∈ s, c + L x < c + L y) : x ∉ convexHull ℝ s := by
  have h' : ∀ y ∈ s, (-c) + (-L : Plane →ₗ[ℝ] ℝ) y < (-c) + (-L : Plane →ₗ[ℝ] ℝ) x := by
    intro y hy
    have := h y hy
    simp only [LinearMap.neg_apply]
    linarith [this]
  exact not_mem_convexHull_of_forall_lt h'

/-- The two barycentric functionals over the triangle `(V, U₁, U₂)`, via `ω`. -/
noncomputable def baryA (V U₁ U₂ : Plane) : Plane → ℝ :=
  fun X ↦ ω (X - V) (U₂ - V) / ω (U₁ - V) (U₂ - V)

noncomputable def baryB (V U₁ U₂ : Plane) : Plane → ℝ :=
  fun X ↦ ω (U₁ - V) (X - V) / ω (U₁ - V) (U₂ - V)

/-- The corner quadrilateral is strictly convex: for a nondegenerate triangle `V U₁ U₂`,
points `K` on `VU₁`, `N` on `VU₂`, and `P` on `U₁U₂` (all strictly inside their segments)
form the vertices of a strictly convex quadrilateral `V K P N` in this order. -/
theorem convexQuad_corner {V U₁ U₂ : Plane} {φ ψ σ : ℝ}
    (hW : ω (U₁ - V) (U₂ - V) ≠ 0)
    (hφ0 : 0 < φ) (hφ1 : φ < 1) (hψ0 : 0 < ψ) (hψ1 : ψ < 1)
    (hσ0 : 0 < σ) (hσ1 : σ < 1)
    {K N P : Plane} (hK : K = V + φ • (U₁ - V)) (hN : N = V + ψ • (U₂ - V))
    (hP : P = (1 - σ) • U₁ + σ • U₂) :
    ConvexQuad V K P N := by
  -- barycentric values
  have hW' : ω (U₂ - V) (U₁ - V) ≠ 0 := by
    rw [ω_comm]
    exact neg_ne_zero.mpr hW
  have hKV : K - V = φ • (U₁ - V) := by rw [hK]; module
  have hNV : N - V = ψ • (U₂ - V) := by rw [hN]; module
  have hPV : P - V = (1 - σ) • (U₁ - V) + σ • (U₂ - V) := by rw [hP]; module
  have hαK : baryA V U₁ U₂ K = φ := by
    rw [baryA, hKV, ω_smul_left]
    field_simp [hW]
  have hαN : baryA V U₁ U₂ N = 0 := by
    rw [baryA, hNV, ω_smul_left, ω_self, mul_zero, zero_div]
  have hαP : baryA V U₁ U₂ P = 1 - σ := by
    rw [baryA, hPV, ω_add_left, ω_smul_left, ω_smul_left, ω_self, mul_zero, add_zero]
    field_simp [hW]
  have hβK : baryB V U₁ U₂ K = 0 := by
    rw [baryB, hKV, ω_smul_right, ω_self, mul_zero, zero_div]
  have hβN : baryB V U₁ U₂ N = ψ := by
    rw [baryB, hNV, ω_smul_right]
    field_simp [hW]
  have hβP : baryB V U₁ U₂ P = σ := by
    rw [baryB, hPV, ω_add_right, ω_smul_right, ω_smul_right, ω_self, mul_zero, zero_add]
    field_simp [hW]
  have hαV : baryA V U₁ U₂ V = 0 := by
    rw [baryA, sub_self, ω_zero_left, zero_div]
  have hβV : baryB V U₁ U₂ V = 0 := by
    rw [baryB, sub_self, ω_zero_right, zero_div]
  -- the two separation functionals, in affine form
  set G : Plane →ₗ[ℝ] ℝ := (ω (U₁ - V) (U₂ - V))⁻¹ • ωL (U₂ - V) with hG
  set H : Plane →ₗ[ℝ] ℝ := (ω (U₁ - V) (U₂ - V))⁻¹ • ωR (U₁ - V) with hH
  have hGA : ∀ X : Plane, G X = ω X (U₂ - V) / ω (U₁ - V) (U₂ - V) := fun X ↦ by
    rw [hG]
    simp only [LinearMap.smul_apply, ωL_apply, smul_eq_mul]
    rw [inv_mul_eq_div]
  have hHB : ∀ X : Plane, H X = ω (U₁ - V) X / ω (U₁ - V) (U₂ - V) := fun X ↦ by
    rw [hH]
    simp only [LinearMap.smul_apply, ωR_apply, smul_eq_mul]
    rw [inv_mul_eq_div]
  have hα : ∀ X : Plane, baryA V U₁ U₂ X = G X - G V := fun X ↦ by
    rw [baryA, hGA, hGA, ω_sub_left]
    ring
  have hβ : ∀ X : Plane, baryB V U₁ U₂ X = H X - H V := fun X ↦ by
    rw [baryB, hHB, hHB, ω_sub_right]
    ring
  -- F₁ = φψ − ψ·α − φ·β with c₁ + L₁ form
  set L₁ : Plane →ₗ[ℝ] ℝ := (-ψ) • G + (-φ) • H with hL₁
  set c₁ : ℝ := φ * ψ + ψ * G V + φ * H V with hc₁
  have hF₁ : ∀ X : Plane, c₁ + L₁ X = φ * ψ - ψ * baryA V U₁ U₂ X -
      φ * baryB V U₁ U₂ X := fun X ↦ by
    rw [hc₁, hL₁, hα, hβ]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    ring
  set L₂ : Plane →ₗ[ℝ] ℝ := σ • G + (-(1 - σ)) • H with hL₂
  set c₂ : ℝ := -σ * G V + (1 - σ) * H V with hc₂
  have hF₂ : ∀ X : Plane, c₂ + L₂ X = σ * baryA V U₁ U₂ X -
      (1 - σ) * baryB V U₁ U₂ X := fun X ↦ by
    rw [hc₂, hL₂, hα, hβ]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    ring
  -- values
  have hF₁V : c₁ + L₁ V = φ * ψ := by rw [hF₁, hαV, hβV]; ring
  have hF₁K : c₁ + L₁ K = 0 := by rw [hF₁, hαK, hβK]; ring
  have hF₁N : c₁ + L₁ N = 0 := by rw [hF₁, hαN, hβN]; ring
  have hF₁P : c₁ + L₁ P = -(ψ * (1 - σ) * (1 - φ) + φ * σ * (1 - ψ)) := by
    rw [hF₁, hαP, hβP]; ring
  have hF₁Pneg : c₁ + L₁ P < 0 := by
    rw [hF₁P]
    have h1 : 0 < ψ * (1 - σ) * (1 - φ) := mul_pos (mul_pos hψ0 (sub_pos.mpr hσ1))
      (sub_pos.mpr hφ1)
    have h2 : 0 < φ * σ * (1 - ψ) := mul_pos (mul_pos hφ0 hσ0) (sub_pos.mpr hψ1)
    linarith
  have hF₂V : c₂ + L₂ V = 0 := by rw [hF₂, hαV, hβV]; ring
  have hF₂K : c₂ + L₂ K = σ * φ := by rw [hF₂, hαK, hβK]; ring
  have hF₂N : c₂ + L₂ N = -((1 - σ) * ψ) := by rw [hF₂, hαN, hβN]; ring
  have hF₂P : c₂ + L₂ P = 0 := by rw [hF₂, hαP, hβP]; ring
  have hF₂Kpos : 0 < c₂ + L₂ K := by rw [hF₂K]; exact mul_pos hσ0 hφ0
  have hF₂Nneg : c₂ + L₂ N < 0 := by
    rw [hF₂N]
    have := mul_pos (sub_pos.mpr hσ1) hψ0
    linarith
  have hF₁Vpos : 0 < c₁ + L₁ V := by rw [hF₁V]; exact mul_pos hφ0 hψ0
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- V ∉ hull {K, P, N}
    apply not_mem_convexHull_of_forall_lt (c := c₁) (L := L₁)
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · rw [hF₁K]; exact hF₁Vpos
    · linarith [hF₁Pneg, hF₁Vpos]
    · rw [hF₁N]; exact hF₁Vpos
  · -- K ∉ hull {P, N, V}
    apply not_mem_convexHull_of_forall_lt (c := c₂) (L := L₂)
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · rw [hF₂P]; exact hF₂Kpos
    · linarith [hF₂Nneg, hF₂Kpos]
    · rw [hF₂V]; exact hF₂Kpos
  · -- P ∉ hull {N, V, K}
    apply not_mem_convexHull_of_forall_gt (c := c₁) (L := L₁)
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · rw [hF₁N]; linarith [hF₁Pneg]
    · rw [hF₁V]; linarith [hF₁Pneg, mul_pos hφ0 hψ0]
    · rw [hF₁K]; linarith [hF₁Pneg]
  · -- N ∉ hull {V, K, P}
    apply not_mem_convexHull_of_forall_gt (c := c₂) (L := L₂)
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · rw [hF₂V]; linarith [hF₂Nneg]
    · rw [hF₂K]; linarith [hF₂Nneg, hF₂Kpos]
    · rw [hF₂P]; linarith [hF₂Nneg]
  · -- diagonals
    set D : ℝ := ψ * (1 - σ) + σ * φ with hD
    have hDpos : 0 < D := by
      rw [hD]
      exact add_pos (mul_pos hψ0 (sub_pos.mpr hσ1)) (mul_pos hσ0 hφ0)
    have hDne : D ≠ 0 := hDpos.ne'
    set s : ℝ := φ * ψ / D with hs
    set t : ℝ := φ * σ / D with ht
    have hs0 : 0 < s := div_pos (mul_pos hφ0 hψ0) hDpos
    have hs1 : s < 1 := by
      rw [hs, div_lt_one hDpos, hD]
      have : φ * ψ < ψ * (1 - σ) + σ * φ := by
        have h1 : φ * ψ < ψ * (1 - σ) * (1 - φ) + σ * φ * (1 - ψ) + φ * ψ := by
          have h2 : 0 < ψ * (1 - σ) * (1 - φ) + σ * φ * (1 - ψ) := by
            exact add_pos (mul_pos (mul_pos hψ0 (sub_pos.mpr hσ1)) (sub_pos.mpr hφ1))
              (mul_pos (mul_pos hσ0 hφ0) (sub_pos.mpr hψ1))
          linarith
        linarith [h1]
      exact this
    have ht0 : 0 < t := div_pos (mul_pos hφ0 hσ0) hDpos
    have ht1 : t < 1 := by
      rw [ht, div_lt_one hDpos, hD]
      have h1 : 0 < ψ * (1 - σ) := mul_pos hψ0 (sub_pos.mpr hσ1)
      linarith
    have hVP : V ≠ P := by
      intro h'
      have h1 : baryA V U₁ U₂ P = baryA V U₁ U₂ V := by rw [← h']
      rw [hαP, hαV] at h1
      linarith [hσ1]
    have hKN : K ≠ N := by
      intro h'
      have h1 : baryB V U₁ U₂ K = baryB V U₁ U₂ N := by rw [h']
      rw [hβK, hβN] at h1
      linarith [hψ0]
    have hsc1 : (1 - t) * φ = s * (1 - σ) := by
      rw [hs, ht, div_mul_eq_mul_div, eq_div_iff_mul_eq hDne, sub_mul, one_mul]
      field_simp [hDne]
      rw [hD]
      ring
    have hsc2 : t * ψ = s * σ := by
      rw [hs, ht]
      field_simp [hDne]
    have hQ : (1 - s) • V + s • P = (1 - t) • K + t • N := by
      rw [show (1 - s) • V + s • P = V + (s * (1 - σ)) • (U₁ - V) + (s * σ) • (U₂ - V) by
        rw [hP]
        module]
      rw [← hsc1, ← hsc2]
      rw [show V + ((1 - t) * φ) • (U₁ - V) + (t * ψ) • (U₂ - V) =
          (1 - t) • (V + φ • (U₁ - V)) + t • (V + ψ • (U₂ - V)) by module]
      rw [hK, hN]
    refine ⟨(1 - s) • V + s • P, ?_, ?_⟩
    · have hQlm : (1 - s) • V + s • P = AffineMap.lineMap V P s := by
        rw [AffineMap.lineMap_apply_module]
      rw [hQlm]
      exact sbtw_lineMap hVP hs0 hs1
    · rw [hQ]
      have hQlm : (1 - t) • K + t • N = AffineMap.lineMap K N t := by
        rw [AffineMap.lineMap_apply_module]
      rw [hQlm]
      exact sbtw_lineMap hKN ht0 ht1

/-- A triangle is split by a cevian: if `P` lies on the segment `V₁V₃`, then
`hull {V₁, V₂, V₃} ⊆ hull {P, V₁, V₂} ∪ hull {P, V₂, V₃}`. -/
theorem triangle_split_of_mem_segment {V₁ V₂ V₃ P : Plane} (hP : P ∈ segment ℝ V₁ V₃)
    (h₁₂ : V₁ ≠ V₂) (h₁₃ : V₁ ≠ V₃) (h₂₃ : V₂ ≠ V₃) {X : Plane}
    (hX : X ∈ convexHull ℝ {V₁, V₂, V₃}) :
    X ∈ convexHull ℝ {P, V₁, V₂} ∪ convexHull ℝ {P, V₂, V₃} := by
  obtain ⟨a, b, ha, hb, hab, hPab⟩ := hP
  set σ := b with hσb
  have ha' : a = 1 - σ := by
    rw [hσb]
    linarith [hab]
  rw [ha'] at hPab
  rw [show ({V₁, V₂, V₃} : Set Plane) = (({V₁, V₂, V₃} : Finset Plane) : Set Plane) by simp]
    at hX
  obtain ⟨w, hw0, hw1, hw2⟩ := Finset.mem_convexHull'.mp hX
  have hV₁ : V₁ ∉ ({V₂, V₃} : Finset Plane) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨h₁₂, h₁₃⟩
  have hV₂ : V₂ ∉ ({V₃} : Finset Plane) := by
    simp only [Finset.mem_singleton]; exact h₂₃
  rw [Finset.sum_insert hV₁, Finset.sum_insert hV₂, Finset.sum_singleton] at hw1
  rw [Finset.sum_insert hV₁, Finset.sum_insert hV₂, Finset.sum_singleton] at hw2
  have hm1 : V₁ ∈ ({V₁, V₂, V₃} : Finset Plane) := Finset.mem_insert_self _ _
  have hm2 : V₂ ∈ ({V₁, V₂, V₃} : Finset Plane) :=
    Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hm3 : V₃ ∈ ({V₁, V₂, V₃} : Finset Plane) :=
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hVin₁ : V₁ ∈ convexHull ℝ {P, V₁, V₂} :=
    subset_convexHull ℝ _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hVin₂ : V₂ ∈ convexHull ℝ {P, V₁, V₂} :=
    subset_convexHull ℝ _ (Set.mem_insert_of_mem _
      (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  have hVin₃ : V₃ ∈ convexHull ℝ {P, V₂, V₃} :=
    subset_convexHull ℝ _ (Set.mem_insert_of_mem _
      (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  have hVin₄ : V₂ ∈ convexHull ℝ {P, V₂, V₃} :=
    subset_convexHull ℝ _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hPin₁ : P ∈ convexHull ℝ {P, V₁, V₂} := subset_convexHull ℝ _ (Set.mem_insert _ _)
  have hPin₂ : P ∈ convexHull ℝ {P, V₂, V₃} := subset_convexHull ℝ _ (Set.mem_insert _ _)
  by_cases h13 : w V₁ + w V₃ = 0
  · have hz1 : w V₁ = 0 := by
      have h1 := hw0 V₁ hm1
      have h3 := hw0 V₃ hm3
      exact le_antisymm (by linarith [h13, h3]) h1
    have hz3 : w V₃ = 0 := by
      have h1 := hw0 V₁ hm1
      have h3 := hw0 V₃ hm3
      exact le_antisymm (by linarith [h13, h1]) h3
    rw [hz1, hz3, zero_smul, zero_smul, zero_add, add_zero] at hw2
    rw [hz1, hz3, zero_add, add_zero] at hw1
    have hw2v : w V₂ = 1 := by linarith [hw1]
    rw [hw2v, one_smul] at hw2
    rw [← hw2]
    exact Set.mem_union_left _ hVin₂
  · have h13p : 0 < w V₁ + w V₃ := by
      have h1 := hw0 V₁ hm1
      have h3 := hw0 V₃ hm3
      exact lt_of_le_of_ne (add_nonneg h1 h3) (Ne.symm h13)
    have h13ne : w V₁ + w V₃ ≠ 0 := h13p.ne'
    set Q : Plane := (w V₁ / (w V₁ + w V₃)) • V₁ + (w V₃ / (w V₁ + w V₃)) • V₃ with hQ
    have hQcombo : (w V₁ + w V₃) • Q = w V₁ • V₁ + w V₃ • V₃ := by
      rw [hQ, smul_add, smul_smul, smul_smul]
      have h2 : (w V₁ + w V₃) * (w V₁ / (w V₁ + w V₃)) = w V₁ := by
        field_simp [h13ne]
      have h3 : (w V₁ + w V₃) * (w V₃ / (w V₁ + w V₃)) = w V₃ := by
        field_simp [h13ne]
      rw [h2, h3]
    have hQX : X = w V₂ • V₂ + (w V₁ + w V₃) • Q := by
      rw [← hw2, hQcombo]
      module
    have hsum : w V₂ + (w V₁ + w V₃) = 1 := by linarith [hw1]
    by_cases hle : w V₃ / (w V₁ + w V₃) ≤ σ
    · -- Q ∈ segment V₁P, so X ∈ hull {P, V₁, V₂}
      have hQin : Q ∈ segment ℝ V₁ P := by
        by_cases hσ0 : σ = 0
        · have h0 : w V₃ / (w V₁ + w V₃) = 0 := by
            have hnn := div_nonneg (hw0 V₃ hm3) h13p.le
            have hle0 : w V₃ / (w V₁ + w V₃) ≤ 0 := by
              rw [hσ0] at hle
              exact hle
            exact le_antisymm hle0 hnn
          have hw3 : w V₃ = 0 := by
            have h1 : w V₃ / (w V₁ + w V₃) = 0 := h0
            rw [div_eq_zero_iff] at h1
            exact h1.resolve_right h13ne
          rw [hw3, add_zero] at h13ne
          have hQv : Q = V₁ := by
            rw [hQ, hw3, zero_div, zero_smul, add_zero, add_zero]
            have h1 : w V₁ / w V₁ = 1 := by
              field_simp [h13ne]
            rw [h1, one_smul]
          have hPv : P = V₁ := by
            rw [← hPab, hσ0, sub_zero, one_smul, zero_smul, add_zero]
          rw [hQv, hPv]
          exact left_mem_segment ℝ V₁ V₁
        · have hσp : 0 < σ := lt_of_le_of_ne hb (Ne.symm hσ0)
          have hu : 0 ≤ (w V₃ / (w V₁ + w V₃)) / σ ∧
              (w V₃ / (w V₁ + w V₃)) / σ ≤ 1 := by
            have h1 : 0 ≤ w V₃ / (w V₁ + w V₃) := div_nonneg (hw0 V₃ hm3) h13p.le
            have h2 : (w V₃ / (w V₁ + w V₃)) / σ = (w V₃ / (w V₁ + w V₃)) * σ⁻¹ := by
              rw [div_eq_mul_inv]
            have h3 : (w V₃ / (w V₁ + w V₃)) * σ⁻¹ ≤ 1 := by
              have h4 : w V₃ / (w V₁ + w V₃) ≤ σ := hle
              have h5 : 0 < σ⁻¹ := inv_pos.mpr hσp
              have h6 : (w V₃ / (w V₁ + w V₃)) * σ⁻¹ ≤ σ * σ⁻¹ := by
                exact mul_le_mul_of_nonneg_right h4 h5.le
              rwa [mul_inv_cancel₀ hσp.ne'] at h6
            exact ⟨by rw [h2]; exact mul_nonneg h1 (inv_pos.mpr hσp).le, by rw [h2]; exact h3⟩
          set u := (w V₃ / (w V₁ + w V₃)) / σ with hub
          have hQv : Q = (1 - u) • V₁ + u • P := by
            rw [← hPab, hub, hQ]
            have h1 : (w V₃ / (w V₁ + w V₃)) / σ * σ = w V₃ / (w V₁ + w V₃) :=
              div_mul_cancel₀ _ hσp.ne'
            have h2 : 1 - w V₃ / (w V₁ + w V₃) = w V₁ / (w V₁ + w V₃) := by
              have h3 : w V₁ / (w V₁ + w V₃) + w V₃ / (w V₁ + w V₃) = 1 := by
                field_simp [h13ne]
              linarith [h3]
            rw [show (1 - (w V₃ / (w V₁ + w V₃)) / σ) • V₁ +
                ((w V₃ / (w V₁ + w V₃)) / σ) • ((1 - σ) • V₁ + σ • V₃) =
                (1 - (w V₃ / (w V₁ + w V₃)) / σ * σ) • V₁ +
                ((w V₃ / (w V₁ + w V₃)) / σ * σ) • V₃ by module]
            rw [h1, h2]
          rw [hQv]
          exact ⟨1 - u, u, sub_nonneg.mpr hu.2, hu.1, sub_add_cancel 1 u, rfl⟩
      have hQin' : Q ∈ convexHull ℝ {P, V₁, V₂} :=
        Convex.segment_subset (convex_convexHull ℝ _) hVin₁ hPin₁ hQin
      have hXin : X ∈ segment ℝ V₂ Q :=
        ⟨w V₂, w V₁ + w V₃, hw0 V₂ hm2, h13p.le, hsum, hQX.symm⟩
      exact Set.mem_union_left _ (Convex.segment_subset (convex_convexHull ℝ _) hVin₂
        hQin' hXin)
    · -- Q ∈ segment PV₃, so X ∈ hull {P, V₂, V₃}
      push_neg at hle
      have hσ1' : σ < 1 := by
        have h1 : σ ≤ 1 := by
          linarith [hab, ha]
        have h2 : w V₃ / (w V₁ + w V₃) ≤ 1 := by
          rw [div_le_one h13p]
          exact le_add_of_nonneg_left (hw0 V₁ hm1)
        by_contra h
        push_neg at h
        have h3 : σ = 1 := le_antisymm h1 h
        rw [h3] at hle
        linarith [hle, h2]
      have hμ : 0 ≤ (w V₃ / (w V₁ + w V₃) - σ) / (1 - σ) ∧
          (w V₃ / (w V₁ + w V₃) - σ) / (1 - σ) ≤ 1 := by
        have h1σ : 0 < 1 - σ := sub_pos.mpr hσ1'
        have h2 : w V₃ / (w V₁ + w V₃) ≤ 1 := by
          rw [div_le_one h13p]
          exact le_add_of_nonneg_left (hw0 V₁ hm1)
        exact ⟨div_nonneg (sub_nonneg.mpr hle.le) h1σ.le, by
          rw [div_le_one h1σ]
          linarith [h2]⟩
      set μ := (w V₃ / (w V₁ + w V₃) - σ) / (1 - σ) with hμb
      have hQin : Q ∈ segment ℝ P V₃ := by
        have hQv : Q = (1 - μ) • P + μ • V₃ := by
          rw [← hPab, hμb, hQ]
          have h1 : (w V₃ / (w V₁ + w V₃) - σ) / (1 - σ) * (1 - σ) =
              w V₃ / (w V₁ + w V₃) - σ := div_mul_cancel₀ _ (sub_pos.mpr hσ1').ne'
          have h2 : w V₁ / (w V₁ + w V₃) = 1 - w V₃ / (w V₁ + w V₃) := by
            have h4 : w V₁ / (w V₁ + w V₃) + w V₃ / (w V₁ + w V₃) = 1 := by
              field_simp [h13ne]
            linarith [h4]
          rw [show (1 - (w V₃ / (w V₁ + w V₃) - σ) / (1 - σ)) • ((1 - σ) • V₁ + σ • V₃) +
              ((w V₃ / (w V₁ + w V₃) - σ) / (1 - σ)) • V₃ =
              (1 - σ - (w V₃ / (w V₁ + w V₃) - σ) / (1 - σ) * (1 - σ)) • V₁ +
              (σ + (w V₃ / (w V₁ + w V₃) - σ) / (1 - σ) * (1 - σ)) • V₃ by module]
          rw [h1, h2]
          module
        rw [hQv]
        exact ⟨1 - μ, μ, sub_nonneg.mpr hμ.2, hμ.1, sub_add_cancel 1 μ, rfl⟩
      have hQin' : Q ∈ convexHull ℝ {P, V₂, V₃} :=
        Convex.segment_subset (convex_convexHull ℝ _) hPin₂ hVin₃ hQin
      have hXin : X ∈ segment ℝ V₂ Q :=
        ⟨w V₂, w V₁ + w V₃, hw0 V₂ hm2, h13p.le, hsum, hQX.symm⟩
      exact Set.mem_union_right _ (Convex.segment_subset (convex_convexHull ℝ _) hVin₄
        hQin' hXin)

/-- If `R` lies on the segment `VW` and has its `f`-value on the same side as `V` (for an
affine `f` vanishing at `X₀ ∈ VW`), then `R` is in the triangle `hull {A, C, V}`, provided
`X₀` also lies on the segment `AC`. -/
theorem mem_convexHull_of_same_side {A C V W R X₀ : Plane} {f : Plane → ℝ} {τ : ℝ}
    (hfV : 0 < f V) (hfW : f W < 0) (hX₀AC : X₀ ∈ segment ℝ A C)
    (hX₀VW : X₀ = (1 - τ) • V + τ • W) (hfX₀ : f X₀ = 0)
    (hR : R ∈ segment ℝ V W) (hfR : 0 ≤ f R)
    (hA : A ∈ convexHull ℝ {A, C, V}) (hC : C ∈ convexHull ℝ {A, C, V})
    (hV : V ∈ convexHull ℝ {A, C, V})
    (hf : ∀ (x y : Plane) (t : ℝ), f ((1 - t) • x + t • y) = (1 - t) * f x + t * f y) :
    R ∈ convexHull ℝ {A, C, V} := by
  obtain ⟨a, b, ha, hb, hab, hRab⟩ := hR
  set t := b with ht
  have ha' : a = 1 - t := by
    rw [ht]
    linarith [hab]
  rw [ha'] at hRab
  have hfVW : 0 < f V - f W := sub_pos.mpr (by linarith [hfV, hfW])
  have hfR' : (1 - t) * f V + t * f W ≥ 0 := by
    have h := hfR
    rw [← hRab, hf] at h
    exact h
  have ht₀pos : 0 < f V / (f V - f W) := div_pos hfV hfVW
  have ht₀1 : f V / (f V - f W) < 1 := by
    rw [div_lt_one hfVW]
    linarith [hfW]
  set t₀ := f V / (f V - f W) with ht₀
  have htτ : τ = t₀ := by
    have h1 : f X₀ = (1 - τ) * f V + τ * f W := by
      rw [hX₀VW, hf]
    rw [hfX₀] at h1
    rw [ht₀]
    field_simp [hfVW.ne']
    linarith [h1]
  have htt₀ : t ≤ t₀ := by
    rw [ht₀]
    refine (le_div_iff₀ hfVW).mpr ?_
    linarith [hfR']
  have ht0 : 0 ≤ t := hb
  have ht0' : 0 < t₀ := ht₀pos
  have hseg : R ∈ segment ℝ V X₀ := by
    have hratio : 0 ≤ t / t₀ ∧ t / t₀ ≤ 1 :=
      ⟨div_nonneg ht0 ht0'.le, (div_le_one ht0').mpr htt₀⟩
    have hR' : R = (1 - t / t₀) • V + (t / t₀) • X₀ := by
      rw [← hRab, hX₀VW, htτ]
      have h3 : (t / t₀) * t₀ = t := div_mul_cancel₀ _ ht0'.ne'
      rw [show (1 - t / t₀) • V + (t / t₀) • ((1 - t₀) • V + t₀ • W) =
          (1 - t / t₀ + (t / t₀) * (1 - t₀)) • V + ((t / t₀) * t₀) • W by module]
      rw [h3]
      have h4 : 1 - t / t₀ + (t / t₀) * (1 - t₀) = 1 - t := by
        field_simp [ht0'.ne']
        ring
      rw [h4]
    rw [hR']
    exact ⟨1 - t / t₀, t / t₀, sub_nonneg.mpr hratio.2, hratio.1, sub_add_cancel 1 _, rfl⟩
  exact Convex.segment_subset (convex_convexHull ℝ _) hV
    (Convex.segment_subset (convex_convexHull ℝ _) hA hC hX₀AC) hseg

/-- A convex quadrilateral is the union of the two triangles cut out by a diagonal:
`hull {A,B,C,D} ⊆ hull {A,B,C} ∪ hull {A,C,D}`. -/
theorem omega_BA_CA_ne_zero {A B C D : Plane} (h : ConvexQuad A B C D) (hCA : C - A ≠ 0) :
    ω (B - A) (C - A) ≠ 0 := by
    intro hB0
    have hB0' : ω (C - A) (B - A) = 0 := by
      have h2 : ω (B - A) (C - A) = 0 := hB0
      rw [ω_comm] at h2
      exact neg_eq_zero.mp h2
    obtain ⟨t, ht⟩ := exists_smul_of_ω_eq_zero hCA hB0'
    -- B = A + t • (C − A), i.e. B − A = t • (C − A)
    have htB : B = (1 - t) • A + t • C := by
      rw [show B = A + (B - A) by module, ht]
      module
    by_cases ht0 : t ≤ 0
    · -- A ∈ segment BC ⊆ hull {B,C,D}, contradicting not_mem₁
      have ht0' : t ≠ 1 := by linarith [ht0]
      have hseg : A ∈ segment ℝ B C := by
        have hs : A = (1 - (-t / (1 - t))) • B + (-t / (1 - t)) • C := by
          rw [htB]
          rw [show (1 - (-t / (1 - t))) • ((1 - t) • A + t • C) + (-t / (1 - t)) • C =
              ((1 - (-t / (1 - t))) * (1 - t)) • A +
              (((1 - (-t / (1 - t))) * t + (-t / (1 - t)))) • C by module]
          rw [show (1 - (-t / (1 - t))) * (1 - t) = 1 by
            field_simp [ht0']; ring,
            show (1 - (-t / (1 - t))) * t + (-t / (1 - t)) = 0 by
            field_simp [ht0']; ring]
          rw [one_smul, zero_smul, add_zero]
        rw [hs]
        have h1 : 0 ≤ -t / (1 - t) := by
          have h2 : 0 < 1 - t := by linarith [ht0]
          exact div_nonneg (by linarith [ht0]) h2.le
        have h2 : -t / (1 - t) ≤ 1 := by
          have h3 : 0 < 1 - t := by linarith [ht0]
          rw [div_le_one h3]
          linarith [ht0]
        exact ⟨1 - (-t / (1 - t)), -t / (1 - t), sub_nonneg.mpr h2, h1,
          sub_add_cancel 1 _, rfl⟩
      exact h.not_mem₁ (Convex.segment_subset (convex_convexHull ℝ _)
        (subset_convexHull ℝ _ (Set.mem_insert _ _))
        (subset_convexHull ℝ _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))) hseg)
    · push_neg at ht0
      by_cases ht1 : t < 1
      · -- B ∈ segment AC ⊆ hull {C,D,A}, contradicting not_mem₂
        have hseg : B ∈ segment ℝ A C := by
          rw [htB]
          exact ⟨1 - t, t, sub_nonneg.mpr ht1.le, ht0.le, sub_add_cancel 1 t, rfl⟩
        exact h.not_mem₂ (Convex.segment_subset (convex_convexHull ℝ _)
          (subset_convexHull ℝ _ (Set.mem_insert_of_mem _
            (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
          (subset_convexHull ℝ _ (Set.mem_insert _ _)) hseg)
      · push_neg at ht1
        have ht1' : 1 ≤ t := ht1
        have htne : t ≠ 0 := by linarith [ht1']
        -- C ∈ segment AB ⊆ hull {D,A,B}, contradicting not_mem₃
        have hseg : C ∈ segment ℝ A B := by
          have hs : C = (1 - 1 / t) • A + (1 / t) • B := by
            rw [htB]
            have h1 : (1 / t) * t = 1 := by
              field_simp [htne]
            have h2 : (1 / t) * (1 - t) = 1 / t - 1 := by
              field_simp [htne]
            rw [show (1 - 1 / t) • A + (1 / t) • ((1 - t) • A + t • C) =
                ((1 - 1 / t) + (1 / t) * (1 - t)) • A + ((1 / t) * t) • C by module]
            rw [h1, h2]
            have h3 : (1 - 1 / t) + (1 / t - 1) = 0 := by ring
            rw [h3, zero_smul, zero_add, one_smul]
          rw [hs]
          have h1 : 0 ≤ 1 / t := div_nonneg zero_le_one ht0.le
          have h2 : 1 / t ≤ 1 := by
            have h3 : 0 < t := ht0
            rw [div_le_one h3]
            exact ht1'
          exact ⟨1 - 1 / t, 1 / t, sub_nonneg.mpr h2, h1, sub_add_cancel 1 _, rfl⟩
        exact h.not_mem₃ (Convex.segment_subset (convex_convexHull ℝ _)
          (subset_convexHull ℝ _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
          (subset_convexHull ℝ _ (Set.mem_insert_of_mem _
            (Set.mem_insert_of_mem _ (Set.mem_singleton _)))) hseg)


theorem omega_DA_CA_ne_zero {A B C D : Plane} (h : ConvexQuad A B C D) (hCA : C - A ≠ 0) :
    ω (D - A) (C - A) ≠ 0 := by
    intro hD0
    have hD0' : ω (C - A) (D - A) = 0 := by
      have h2 : ω (D - A) (C - A) = 0 := hD0
      rw [ω_comm] at h2
      exact neg_eq_zero.mp h2
    obtain ⟨t, ht⟩ := exists_smul_of_ω_eq_zero hCA hD0'
    have htD : D = (1 - t) • A + t • C := by
      rw [show D = A + (D - A) by module, ht]
      module
    by_cases ht0 : t ≤ 0
    · have ht0' : t ≠ 1 := by linarith [ht0]
      have hseg : A ∈ segment ℝ D C := by
        have hs : A = (1 - (-t / (1 - t))) • D + (-t / (1 - t)) • C := by
          rw [htD]
          rw [show (1 - (-t / (1 - t))) • ((1 - t) • A + t • C) + (-t / (1 - t)) • C =
              ((1 - (-t / (1 - t))) * (1 - t)) • A +
              (((1 - (-t / (1 - t))) * t + (-t / (1 - t)))) • C by module]
          rw [show (1 - (-t / (1 - t))) * (1 - t) = 1 by
            field_simp [ht0']; ring,
            show (1 - (-t / (1 - t))) * t + (-t / (1 - t)) = 0 by
            field_simp [ht0']; ring]
          rw [one_smul, zero_smul, add_zero]
        rw [hs]
        have h1 : 0 ≤ -t / (1 - t) := by
          have h2 : 0 < 1 - t := by linarith [ht0]
          exact div_nonneg (by linarith [ht0]) h2.le
        have h2 : -t / (1 - t) ≤ 1 := by
          have h3 : 0 < 1 - t := by linarith [ht0]
          rw [div_le_one h3]
          linarith [ht0]
        exact ⟨1 - (-t / (1 - t)), -t / (1 - t), sub_nonneg.mpr h2, h1,
          sub_add_cancel 1 _, rfl⟩
      exact h.not_mem₁ (Convex.segment_subset (convex_convexHull ℝ _)
        (subset_convexHull ℝ _ (Set.mem_insert_of_mem _
          (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
        (subset_convexHull ℝ _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))) hseg)
    · push_neg at ht0
      by_cases ht1 : t < 1
      · have hseg : D ∈ segment ℝ A C := by
          rw [htD]
          exact ⟨1 - t, t, sub_nonneg.mpr ht1.le, ht0.le, sub_add_cancel 1 t, rfl⟩
        exact h.not_mem₄ (Convex.segment_subset (convex_convexHull ℝ _)
          (subset_convexHull ℝ _ (Set.mem_insert _ _))
          (subset_convexHull ℝ _ (Set.mem_insert_of_mem _
            (Set.mem_insert_of_mem _ (Set.mem_singleton _)))) hseg)
      · push_neg at ht1
        have ht1' : 1 ≤ t := ht1
        have htne : t ≠ 0 := by linarith [ht1']
        have hseg : C ∈ segment ℝ A D := by
          have hs : C = (1 - 1 / t) • A + (1 / t) • D := by
            rw [htD]
            have h1 : (1 / t) * t = 1 := by
              field_simp [htne]
            have h2 : (1 / t) * (1 - t) = 1 / t - 1 := by
              field_simp [htne]
            rw [show (1 - 1 / t) • A + (1 / t) • ((1 - t) • A + t • C) =
                ((1 - 1 / t) + (1 / t) * (1 - t)) • A + ((1 / t) * t) • C by module]
            rw [h1, h2]
            have h3 : (1 - 1 / t) + (1 / t - 1) = 0 := by ring
            rw [h3, zero_smul, zero_add, one_smul]
          rw [hs]
          have h1 : 0 ≤ 1 / t := div_nonneg zero_le_one ht0.le
          have h2 : 1 / t ≤ 1 := by
            have h3 : 0 < t := ht0
            rw [div_le_one h3]
            exact ht1'
          exact ⟨1 - 1 / t, 1 / t, sub_nonneg.mpr h2, h1, sub_add_cancel 1 _, rfl⟩
        exact h.not_mem₃ (Convex.segment_subset (convex_convexHull ℝ _)
          (subset_convexHull ℝ _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
          (subset_convexHull ℝ _ (Set.mem_insert _ _)) hseg)


theorem convexHull_quad_subset_union_triangle {A B C D : Plane} (h : ConvexQuad A B C D)
    {X : Plane} (hX : X ∈ convexHull ℝ {A, B, C, D}) :
    X ∈ convexHull ℝ {A, B, C} ∪ convexHull ℝ {A, C, D} := by
  obtain ⟨X₀, hAC, hBD⟩ := h.diagonals
  obtain ⟨σ₀, hσ₀, hX₀σ⟩ := hAC.1
  obtain ⟨τ₀, hτ₀, hX₀τ⟩ := hBD.1
  rw [AffineMap.lineMap_apply_module] at hX₀σ hX₀τ
  have hσ₀0 : 0 < σ₀ := by
    rcases hσ₀ with ⟨h1, h2⟩
    by_contra h'
    push_neg at h'
    have : σ₀ = 0 := by linarith [h1, h']
    rw [this] at hX₀σ
    simp at hX₀σ
    exact hAC.2.1 hX₀σ.symm
  have hσ₀1 : σ₀ < 1 := by
    rcases hσ₀ with ⟨h1, h2⟩
    by_contra h'
    push_neg at h'
    have : σ₀ = 1 := by linarith [h2, h']
    rw [this] at hX₀σ
    simp at hX₀σ
    exact hAC.2.2 hX₀σ.symm
  have hτ₀0 : 0 < τ₀ := by
    rcases hτ₀ with ⟨h1, h2⟩
    by_contra h'
    push_neg at h'
    have : τ₀ = 0 := by linarith [h1, h']
    rw [this] at hX₀τ
    simp at hX₀τ
    exact hBD.2.1 hX₀τ.symm
  have hτ₀1 : τ₀ < 1 := by
    rcases hτ₀ with ⟨h1, h2⟩
    by_contra h'
    push_neg at h'
    have : τ₀ = 1 := by linarith [h2, h']
    rw [this] at hX₀τ
    simp at hX₀τ
    exact hBD.2.2 hX₀τ.symm
  -- the functional and its basic values
  set f : Plane → ℝ := fun Y ↦ ω (Y - A) (C - A) with hfdef
  have hf : ∀ (x y : Plane) (t : ℝ), f ((1 - t) • x + t • y) = (1 - t) * f x + t * f y := by
    intro x y t
    simp only [hfdef]
    rw [show (1 - t) • x + t • y - A = (1 - t) • (x - A) + t • (y - A) by module]
    rw [ω_add_left, ω_smul_left, ω_smul_left]
  have hfA : f A = 0 := by
    rw [hfdef]
    show ω (A - A) (C - A) = 0
    rw [sub_self, ω_zero_left]
  have hfC : f C = 0 := by
    rw [hfdef]
    show ω (C - A) (C - A) = 0
    rw [ω_self]
  have hCA : C - A ≠ 0 := by
    intro h'
    apply h.not_mem₁
    have hAC' : A = C := (sub_eq_zero.mp h').symm
    rw [hAC']
    exact subset_convexHull ℝ _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hfX₀ : f X₀ = 0 := by
    rw [hfdef, ← hX₀σ]
    show ω (((1 - σ₀) • A + σ₀ • C) - A) (C - A) = 0
    rw [show (1 - σ₀) • A + σ₀ • C - A = σ₀ • (C - A) by module,
      ω_smul_left, ω_self, mul_zero]
  have hfB : f B ≠ 0 := omega_BA_CA_ne_zero h hCA
  have hfD : f D ≠ 0 := omega_DA_CA_ne_zero h hCA
  -- opposite signs of f(B), f(D)
  have hsign : (0 < f B ∧ f D < 0) ∨ (f B < 0 ∧ 0 < f D) := by
    have h1 : (1 - τ₀) * f B + τ₀ * f D = 0 := by
      have h2 : f X₀ = (1 - τ₀) * f B + τ₀ * f D := by
        rw [← hX₀τ, hf]
      rw [hfX₀] at h2
      exact h2.symm
    rcases lt_trichotomy (f B) 0 with hb | hb | hb
    · -- f B < 0
      right
      refine ⟨hb, ?_⟩
      by_contra h'
      push_neg at h'
      have h2 : f D ≤ 0 := h'
      rcases eq_or_lt_of_le h2 with h3 | h3
      · exact hfD h3
      · have h4 : (1 - τ₀) * f B < 0 := mul_neg_of_pos_of_neg (sub_pos.mpr hτ₀1) hb
        have h5 : τ₀ * f D < 0 := mul_neg_of_pos_of_neg hτ₀0 h3
        linarith [h4, h5]
    · exact absurd hb hfB
    · -- 0 < f B
      left
      refine ⟨hb, ?_⟩
      by_contra h'
      push_neg at h'
      have h2 : 0 ≤ f D := h'
      have h3 : 0 < (1 - τ₀) * f B := mul_pos (sub_pos.mpr hτ₀1) hb
      have h4 : 0 ≤ τ₀ * f D := mul_nonneg hτ₀0.le h2
      linarith [h3, h4]
  -- distinctness of the four points
  have hdAB : A ≠ B := fun h' ↦ hfB (by rw [← h', hfA])
  have hdAC : A ≠ C := fun h' ↦ hCA (by rw [h', sub_self])
  have hdAD : A ≠ D := fun h' ↦ hfD (by rw [← h', hfA])
  have hdBC : B ≠ C := fun h' ↦ hfB (by rw [h', hfC])
  have hdBD : B ≠ D := by
    rcases hsign with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact fun h' ↦ by rw [h'] at h1; linarith [h1, h2]
    · exact fun h' ↦ by rw [h'] at h1; linarith [h1, h2]
  have hdCD : C ≠ D := fun h' ↦ hfD (by rw [← h', hfC])
  -- weights
  rw [show ({A, B, C, D} : Set Plane) = (({A, B, C, D} : Finset Plane) : Set Plane) by simp]
    at hX
  obtain ⟨w, hw0, hw1, hw2⟩ := Finset.mem_convexHull'.mp hX
  have hAin : A ∉ ({B, C, D} : Finset Plane) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hdAB, hdAC, hdAD⟩
  have hBin : B ∉ ({C, D} : Finset Plane) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hdBC, hdBD⟩
  have hCin : C ∉ ({D} : Finset Plane) := by
    simp only [Finset.mem_singleton]; exact hdCD
  rw [Finset.sum_insert hAin, Finset.sum_insert hBin, Finset.sum_insert hCin,
    Finset.sum_singleton] at hw1 hw2
  have hmA : A ∈ ({A, B, C, D} : Finset Plane) := Finset.mem_insert_self _ _
  have hmB : B ∈ ({A, B, C, D} : Finset Plane) :=
    Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hmC : C ∈ ({A, B, C, D} : Finset Plane) :=
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have hmD : D ∈ ({A, B, C, D} : Finset Plane) :=
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_singleton_self _)))
  -- the diagonal point as segment memberships
  have hX₀AC : X₀ ∈ segment ℝ A C := affineSegment_eq_segment ℝ A C ▸ hAC.1
  have hX₀τ : X₀ = (1 - τ₀) • B + τ₀ • D := hX₀τ.symm
  have hX₀τ' : X₀ = (1 - (1 - τ₀)) • D + (1 - τ₀) • B := by
    rw [hX₀τ]
    module
  have hsetCB : ({A, C, B} : Set Plane) = {A, B, C} := by
    rw [show ({A, C, B} : Set Plane) = insert A {C, B} from rfl, Set.pair_comm C B]
  by_cases hAC0 : w A + w C = 0
  · -- all of X's weight is on B and D: X = R
    have hzA : w A = 0 := by
      have h1 := hw0 A hmA
      have h3 := hw0 C hmC
      exact le_antisymm (by linarith [hAC0, h3]) h1
    have hzC : w C = 0 := by
      have h1 := hw0 A hmA
      have h3 := hw0 C hmC
      exact le_antisymm (by linarith [hAC0, h1]) h3
    have hBDp : 0 < w B + w D := by
      have h1 := hw0 B hmB
      have h3 := hw0 D hmD
      have h4 : w B + w D ≠ 0 := by
        intro h'
        have h5 : w B + w D = 1 := by linarith [hw1, hzA, hzC]
        rw [h'] at h5
        exact one_ne_zero h5.symm
      exact lt_of_le_of_ne (add_nonneg h1 h3) (Ne.symm h4)
    rw [hzA, hzC, zero_smul, zero_smul, zero_add, zero_add] at hw2
    set R : Plane := (w B / (w B + w D)) • B + (w D / (w B + w D)) • D with hR
    have hRseg : R ∈ segment ℝ B D :=
      ⟨w B / (w B + w D), w D / (w B + w D), div_nonneg (hw0 B hmB) hBDp.le,
        div_nonneg (hw0 D hmD) hBDp.le, by field_simp [hBDp.ne'], hR.symm⟩
    have hXisR : X = R := by
      have h1 : w B + w D = 1 := by linarith [hw1, hzA, hzC]
      rw [hR]
      have h2 : w B / (w B + w D) = w B := by
        rw [h1]
        field_simp
      have h3 : w D / (w B + w D) = w D := by
        rw [h1]
        field_simp
      rw [h2, h3]
      exact hw2.symm
    rw [hXisR]
    -- f R determines the triangle
    have hfRw : f R = (w B / (w B + w D)) * f B + (w D / (w B + w D)) * f D := by
      have h4 : 1 - w D / (w B + w D) = w B / (w B + w D) := by
        rw [sub_eq_iff_eq_add]
        field_simp [hBDp.ne']
      rw [hR, show (w B / (w B + w D)) • B + (w D / (w B + w D)) • D =
          (1 - (w D / (w B + w D))) • B + (w D / (w B + w D)) • D by
        rw [h4]]
      rw [hf, h4]
    rcases hsign with ⟨hsgB, hsgD⟩ | ⟨hsgB, hsgD⟩
    · -- f B > 0, f D < 0
      by_cases hfR : 0 ≤ f R
      · left
        rw [← hsetCB]
        exact mem_convexHull_of_same_side hsgB hsgD hX₀AC hX₀τ hfX₀ hRseg hfR
          (subset_convexHull ℝ _ (Set.mem_insert _ _))
          (subset_convexHull ℝ _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
          (subset_convexHull ℝ _ (Set.mem_insert_of_mem _
            (Set.mem_insert_of_mem _ (Set.mem_singleton _)))) hf
      · push_neg at hfR
        right
        have hfR' : 0 ≤ (-f) R := by
          simp only [Pi.neg_apply]
          linarith [hfR]
        have hsegDB : R ∈ segment ℝ D B := segment_symm ℝ B D ▸ hRseg
        have h := mem_convexHull_of_same_side (f := -f)
          (by simp only [Pi.neg_apply]; linarith [hsgD])
          (by simp only [Pi.neg_apply]; linarith [hsgB])
          hX₀AC hX₀τ' (by simp only [Pi.neg_apply, hfX₀, neg_zero]) hsegDB hfR'
          (subset_convexHull ℝ _ (Set.mem_insert _ _))
          (subset_convexHull ℝ _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
          (subset_convexHull ℝ _ (Set.mem_insert_of_mem _
            (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
          (fun x y t ↦ by simp only [Pi.neg_apply, hf x y t]; ring)
        exact h
    · -- f B < 0, f D > 0
      by_cases hfR : 0 ≤ f R
      · right
        exact mem_convexHull_of_same_side hsgD hsgB hX₀AC hX₀τ' hfX₀
          (segment_symm ℝ B D ▸ hRseg) hfR
          (subset_convexHull ℝ _ (Set.mem_insert _ _))
          (subset_convexHull ℝ _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
          (subset_convexHull ℝ _ (Set.mem_insert_of_mem _
            (Set.mem_insert_of_mem _ (Set.mem_singleton _)))) hf
      · push_neg at hfR
        left
        have hfR' : 0 ≤ (-f) R := by
          simp only [Pi.neg_apply]
          linarith [hfR]
        have h := mem_convexHull_of_same_side (f := -f)
          (by simp only [Pi.neg_apply]; linarith [hsgB])
          (by simp only [Pi.neg_apply]; linarith [hsgD])
          hX₀AC hX₀τ (by simp only [Pi.neg_apply, hfX₀, neg_zero]) hRseg hfR'
          (subset_convexHull ℝ _ (Set.mem_insert _ _))
          (subset_convexHull ℝ _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
          (subset_convexHull ℝ _ (Set.mem_insert_of_mem _
            (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
          (fun x y t ↦ by simp only [Pi.neg_apply, hf x y t]; ring)
        rw [hsetCB] at h
        exact h
  · have hACp : 0 < w A + w C := by
      have h1 := hw0 A hmA
      have h3 := hw0 C hmC
      exact lt_of_le_of_ne (add_nonneg h1 h3) (Ne.symm hAC0)
    by_cases hBD0 : w B + w D = 0
    · have hzB : w B = 0 := by
        have h1 := hw0 B hmB
        have h3 := hw0 D hmD
        exact le_antisymm (by linarith [hBD0, h3]) h1
      have hzD : w D = 0 := by
        have h1 := hw0 B hmB
        have h3 := hw0 D hmD
        exact le_antisymm (by linarith [hBD0, h1]) h3
      rw [hzB, hzD, zero_smul, zero_smul, add_zero, zero_add] at hw2
      left
      set S : Plane := (w A / (w A + w C)) • A + (w C / (w A + w C)) • C with hS
      have hSseg : S ∈ segment ℝ A C :=
        ⟨w A / (w A + w C), w C / (w A + w C), div_nonneg (hw0 A hmA) hACp.le,
          div_nonneg (hw0 C hmC) hACp.le, by field_simp [hACp.ne'], hS.symm⟩
      have hXS : X = S := by
        have h1 : w A + w C = 1 := by
          rw [hzB, hzD, zero_add, add_zero] at hw1
          linarith [hw1]
        rw [hS]
        have h2 : w A / (w A + w C) = w A := by
          rw [h1]
          field_simp
        have h3 : w C / (w A + w C) = w C := by
          rw [h1]
          field_simp
        rw [h2, h3]
        exact hw2.symm
      rw [hXS]
      exact Convex.segment_subset (convex_convexHull ℝ _)
        (subset_convexHull ℝ _ (Set.mem_insert _ _))
        (subset_convexHull ℝ _ (Set.mem_insert_of_mem _
          (Set.mem_insert_of_mem _ (Set.mem_singleton _)))) hSseg
    · have hBDp : 0 < w B + w D := by
        have h1 := hw0 B hmB
        have h3 := hw0 D hmD
        exact lt_of_le_of_ne (add_nonneg h1 h3) (Ne.symm hBD0)
      set S : Plane := (w A / (w A + w C)) • A + (w C / (w A + w C)) • C with hS
      set R : Plane := (w B / (w B + w D)) • B + (w D / (w B + w D)) • D with hR
      have hSseg : S ∈ segment ℝ A C :=
        ⟨w A / (w A + w C), w C / (w A + w C), div_nonneg (hw0 A hmA) hACp.le,
          div_nonneg (hw0 C hmC) hACp.le, by field_simp [hACp.ne'], hS.symm⟩
      have hRseg : R ∈ segment ℝ B D :=
        ⟨w B / (w B + w D), w D / (w B + w D), div_nonneg (hw0 B hmB) hBDp.le,
          div_nonneg (hw0 D hmD) hBDp.le, by field_simp [hBDp.ne'], hR.symm⟩
      have hS' : (w A + w C) • S = w A • A + w C • C := by
        rw [hS, smul_add, smul_smul, smul_smul]
        have h2 : (w A + w C) * (w A / (w A + w C)) = w A := by
          field_simp [hACp.ne']
        have h3 : (w A + w C) * (w C / (w A + w C)) = w C := by
          field_simp [hACp.ne']
        rw [h2, h3]
      have hR' : (w B + w D) • R = w B • B + w D • D := by
        rw [hR, smul_add, smul_smul, smul_smul]
        have h2 : (w B + w D) * (w B / (w B + w D)) = w B := by
          field_simp [hBDp.ne']
        have h3 : (w B + w D) * (w D / (w B + w D)) = w D := by
          field_simp [hBDp.ne']
        rw [h2, h3]
      have hX' : X = (w A + w C) • S + (w B + w D) • R := by
        rw [hS', hR', ← hw2]
        module
      have hsum' : (w A + w C) + (w B + w D) = 1 := by
        linarith [hw1]
      have hSin₁ : S ∈ convexHull ℝ {A, B, C} :=
        Convex.segment_subset (convex_convexHull ℝ _)
          (subset_convexHull ℝ _ (Set.mem_insert _ _))
          (subset_convexHull ℝ _ (Set.mem_insert_of_mem _
            (Set.mem_insert_of_mem _ (Set.mem_singleton _)))) hSseg
      have hSin₂ : S ∈ convexHull ℝ {A, C, D} :=
        Convex.segment_subset (convex_convexHull ℝ _)
          (subset_convexHull ℝ _ (Set.mem_insert _ _))
          (subset_convexHull ℝ _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))) hSseg
      have hmem₁ : A ∈ convexHull ℝ {A, C, B} :=
        subset_convexHull ℝ _ (Set.mem_insert _ _)
      have hmem₂ : C ∈ convexHull ℝ {A, C, B} :=
        subset_convexHull ℝ _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
      have hmem₃ : B ∈ convexHull ℝ {A, C, B} :=
        subset_convexHull ℝ _ (Set.mem_insert_of_mem _
          (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
      have hmem₄ : A ∈ convexHull ℝ {A, C, D} :=
        subset_convexHull ℝ _ (Set.mem_insert _ _)
      have hmem₅ : C ∈ convexHull ℝ {A, C, D} :=
        subset_convexHull ℝ _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
      have hmem₆ : D ∈ convexHull ℝ {A, C, D} :=
        subset_convexHull ℝ _ (Set.mem_insert_of_mem _
          (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
      rcases hsign with ⟨hsgB, hsgD⟩ | ⟨hsgB, hsgD⟩
      · -- f B > 0, f D < 0
        by_cases hfR : 0 ≤ f R
        · left
          have hRin : R ∈ convexHull ℝ {A, B, C} := by
            rw [← hsetCB]
            exact mem_convexHull_of_same_side hsgB hsgD hX₀AC hX₀τ hfX₀ hRseg hfR
              hmem₁ hmem₂ hmem₃ hf
          exact Convex.segment_subset (convex_convexHull ℝ _) hSin₁ hRin
            ⟨w A + w C, w B + w D, hACp.le, hBDp.le, hsum', hX'.symm⟩
        · push_neg at hfR
          right
          have hfR' : 0 ≤ (-f) R := by
            simp only [Pi.neg_apply]
            linarith [hfR]
          have hRin : R ∈ convexHull ℝ {A, C, D} :=
            mem_convexHull_of_same_side (f := -f)
              (by simp only [Pi.neg_apply]; linarith [hsgD])
              (by simp only [Pi.neg_apply]; linarith [hsgB])
              hX₀AC hX₀τ' (by simp only [Pi.neg_apply, hfX₀, neg_zero])
              (segment_symm ℝ B D ▸ hRseg) hfR' hmem₄ hmem₅ hmem₆
              (fun x y t ↦ by simp only [Pi.neg_apply, hf x y t]; ring)
          exact Convex.segment_subset (convex_convexHull ℝ _) hSin₂ hRin
            ⟨w A + w C, w B + w D, hACp.le, hBDp.le, hsum', hX'.symm⟩
      · -- f B < 0, f D > 0
        by_cases hfR : 0 ≤ f R
        · right
          have hRin : R ∈ convexHull ℝ {A, C, D} :=
            mem_convexHull_of_same_side hsgD hsgB hX₀AC hX₀τ' hfX₀
              (segment_symm ℝ B D ▸ hRseg) hfR hmem₄ hmem₅ hmem₆ hf
          exact Convex.segment_subset (convex_convexHull ℝ _) hSin₂ hRin
            ⟨w A + w C, w B + w D, hACp.le, hBDp.le, hsum', hX'.symm⟩
        · push_neg at hfR
          left
          have hfR' : 0 ≤ (-f) R := by
            simp only [Pi.neg_apply]
            linarith [hfR]
          have hRin : R ∈ convexHull ℝ {A, B, C} := by
            rw [← hsetCB]
            exact mem_convexHull_of_same_side (f := -f)
              (by simp only [Pi.neg_apply]; linarith [hsgB])
              (by simp only [Pi.neg_apply]; linarith [hsgD])
              hX₀AC hX₀τ (by simp only [Pi.neg_apply, hfX₀, neg_zero]) hRseg hfR'
              hmem₁ hmem₂ hmem₃
              (fun x y t ↦ by simp only [Pi.neg_apply, hf x y t]; ring)
          exact Convex.segment_subset (convex_convexHull ℝ _) hSin₁ hRin
            ⟨w A + w C, w B + w D, hACp.le, hBDp.le, hsum', hX'.symm⟩

/-- Doubling kills the `π`-shift from rescaling either argument by a nonzero scalar:
the doubled oriented angle between two vectors only depends on the directed lines they span. -/
theorem two_zsmul_oangle_smul_smul_of_ne_zero {u v : Plane} {a b : ℝ}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    (2 : ℤ) • o.oangle (a • u) (b • v) = (2 : ℤ) • o.oangle u v := by
  rw [o.two_zsmul_oangle_smul_left_of_ne_zero _ _ ha,
    o.two_zsmul_oangle_smul_right_of_ne_zero _ _ hb]

/-- **Angles in the same segment** (and opposite angles of a cyclic quadrilateral), for doubled
oriented angles.  Thin wrapper around Mathlib's
`EuclideanGeometry.Cospherical.two_zsmul_oangle_eq`, with the four points reordered so that the
two angles compared are `∡ x w y` at `w` and `∡ x z y` at `z`. -/
theorem Cospherical.two_zsmul_oangle_of_cospherical {w x y z : Plane}
    (h : Cospherical ({w, x, y, z} : Set Plane))
    (hwx : w ≠ x) (hwy : w ≠ y) (hzx : z ≠ x) (hzy : z ≠ y) :
    (2 : ℤ) • ∡ x w y = (2 : ℤ) • ∡ x z y :=
  (h.subset (by simp [Set.insert_subset_iff])).two_zsmul_oangle_eq hwx hwy hzx hzy

/-- **Converse of "angles in the same segment"**: equal doubled oriented angles (plus a
non-collinearity side condition) imply cosphericality.  Thin wrapper around Mathlib's
`EuclideanGeometry.cospherical_of_two_zsmul_oangle_eq_of_not_collinear`. -/
theorem cospherical_of_two_zsmul_oangle_eq {w x y z : Plane}
    (h : (2 : ℤ) • ∡ x w y = (2 : ℤ) • ∡ x z y)
    (hn : ¬ Collinear ℝ ({x, w, y} : Set Plane)) :
    Cospherical ({w, x, y, z} : Set Plane) :=
  (EuclideanGeometry.cospherical_of_two_zsmul_oangle_eq_of_not_collinear h hn).subset
    (by simp [Set.insert_subset_iff])

/-- **Pivot theorem.** Points `K,L,M,N` lie on the lines `AB, BC, CD, DA` respectively
(hypotheses given as vector-parallelism), and `P` is a further point.  If each of
`(B,K,L,P)`, `(C,L,M,P)`, `(D,M,N,P)` is cospherical, then `(A,K,P,N)` is cospherical. -/
theorem pivot_cospherical {A B C D P K L M N : Plane}
    (hK : ∃ c : ℝ, K - B = c • (A - B)) (hL : ∃ c : ℝ, L - C = c • (B - C))
    (hM : ∃ c : ℝ, M - D = c • (C - D)) (hN : ∃ c : ℝ, N - A = c • (D - A))
    (hBKP : Cospherical ({B, K, L, P} : Set Plane))
    (hCLP : Cospherical ({C, L, M, P} : Set Plane))
    (hDMP : Cospherical ({D, M, N, P} : Set Plane))
    -- nondegeneracy: distinctness of points appearing as vertices/endpoints of angles
    (hAB : A ≠ B) (hBC : B ≠ C) (hCD : C ≠ D) (hDA : D ≠ A)
    (hKA : K ≠ A) (hKB : K ≠ B) (hLB : L ≠ B) (hLC : L ≠ C)
    (hMC : M ≠ C) (hMD : M ≠ D) (hNA : N ≠ A) (hND : N ≠ D)
    (hPK : P ≠ K) (hPL : P ≠ L) (hPM : P ≠ M) (hPN : P ≠ N)
    (hnc : ¬ Collinear ℝ ({K, P, N} : Set Plane)) :
    Cospherical ({A, K, P, N} : Set Plane) := by
  obtain ⟨cK, hK⟩ := hK
  obtain ⟨cL, hL⟩ := hL
  obtain ⟨cM, hM⟩ := hM
  obtain ⟨cN, hN⟩ := hN
  -- the four side vectors are nonzero
  have hABe : A - B ≠ 0 := sub_ne_zero.mpr hAB
  have hBCe : B - C ≠ 0 := sub_ne_zero.mpr hBC
  have hCDe : C - D ≠ 0 := sub_ne_zero.mpr hCD
  have hDAe : D - A ≠ 0 := sub_ne_zero.mpr hDA
  -- vector forms of the "point on line" hypotheses, relative to the angle vertices
  have hLv : L - B = (cL - 1) • (B - C) := by
    rw [← sub_add_sub_cancel L C B, hL]; module
  have hMv : M - C = (cM - 1) • (C - D) := by
    rw [← sub_add_sub_cancel M D C, hM]; module
  have hNv : N - D = (cN - 1) • (D - A) := by
    rw [← sub_add_sub_cancel N A D, hN]; module
  have hKv : K - A = (cK - 1) • (A - B) := by
    rw [← sub_add_sub_cancel K B A, hK]; module
  -- the scalars appearing are nonzero (otherwise two supposedly distinct points coincide)
  have hcK : cK ≠ 0 := by
    intro h; apply hKB; rw [← sub_eq_zero, hK, h, zero_smul]
  have hcL : cL ≠ 0 := by
    intro h; apply hLC; rw [← sub_eq_zero, hL, h, zero_smul]
  have hcM : cM ≠ 0 := by
    intro h; apply hMD; rw [← sub_eq_zero, hM, h, zero_smul]
  have hcN : cN ≠ 0 := by
    intro h; apply hNA; rw [← sub_eq_zero, hN, h, zero_smul]
  have hcK1 : cK - 1 ≠ 0 := by
    intro h; apply hKA; rw [← sub_eq_zero, hKv, h, zero_smul]
  have hcL1 : cL - 1 ≠ 0 := by
    intro h; apply hLB; rw [← sub_eq_zero, hLv, h, zero_smul]
  have hcM1 : cM - 1 ≠ 0 := by
    intro h; apply hMC; rw [← sub_eq_zero, hMv, h, zero_smul]
  have hcN1 : cN - 1 ≠ 0 := by
    intro h; apply hND; rw [← sub_eq_zero, hNv, h, zero_smul]
  -- Step 1: equal inscribed doubled angles on the three given circles
  have h1 : (2 : ℤ) • ∡ K P L = (2 : ℤ) • ∡ K B L :=
    (hBKP.subset (by simp [Set.insert_subset_iff])).two_zsmul_oangle_eq hPK hPL hKB.symm hLB.symm
  have h2 : (2 : ℤ) • ∡ L P M = (2 : ℤ) • ∡ L C M :=
    (hCLP.subset (by simp [Set.insert_subset_iff])).two_zsmul_oangle_eq hPL hPM hLC.symm hMC.symm
  have h3 : (2 : ℤ) • ∡ M P N = (2 : ℤ) • ∡ M D N :=
    (hDMP.subset (by simp [Set.insert_subset_iff])).two_zsmul_oangle_eq hPM hPN hMD.symm hND.symm
  -- Step 2: the vertex angles equal the angles between the corresponding side directions
  have eB : (2 : ℤ) • ∡ K B L = (2 : ℤ) • o.oangle (A - B) (B - C) := by
    rw [EuclideanGeometry.oangle, vsub_eq_sub, vsub_eq_sub, hK, hLv,
      o.two_zsmul_oangle_smul_left_of_ne_zero _ _ hcK,
      o.two_zsmul_oangle_smul_right_of_ne_zero _ _ hcL1]
  have eC : (2 : ℤ) • ∡ L C M = (2 : ℤ) • o.oangle (B - C) (C - D) := by
    rw [EuclideanGeometry.oangle, vsub_eq_sub, vsub_eq_sub, hL, hMv,
      o.two_zsmul_oangle_smul_left_of_ne_zero _ _ hcL,
      o.two_zsmul_oangle_smul_right_of_ne_zero _ _ hcM1]
  have eD : (2 : ℤ) • ∡ M D N = (2 : ℤ) • o.oangle (C - D) (D - A) := by
    rw [EuclideanGeometry.oangle, vsub_eq_sub, vsub_eq_sub, hM, hNv,
      o.two_zsmul_oangle_smul_left_of_ne_zero _ _ hcM,
      o.two_zsmul_oangle_smul_right_of_ne_zero _ _ hcN1]
  -- Step 3a: Chasles' relation at `P`
  have hP1 : ∡ K P L + ∡ L P M = ∡ K P M :=
    EuclideanGeometry.oangle_add hPK.symm hPL.symm hPM.symm
  have hP2 : ∡ K P M + ∡ M P N = ∡ K P N :=
    EuclideanGeometry.oangle_add hPK.symm hPM.symm hPN.symm
  -- Step 3b: Chasles' relation for the side directions (telescoping)
  have hV1 : o.oangle (A - B) (B - C) + o.oangle (B - C) (C - D) =
      o.oangle (A - B) (C - D) := o.oangle_add hABe hBCe hCDe
  have hV2 : o.oangle (A - B) (C - D) + o.oangle (C - D) (D - A) =
      o.oangle (A - B) (D - A) := o.oangle_add hABe hCDe hDAe
  -- the angle at `A` between the points on `AB` and `AD`
  have eA : (2 : ℤ) • ∡ K A N = (2 : ℤ) • o.oangle (A - B) (D - A) := by
    rw [EuclideanGeometry.oangle, vsub_eq_sub, vsub_eq_sub, hKv, hN,
      o.two_zsmul_oangle_smul_left_of_ne_zero _ _ hcK1,
      o.two_zsmul_oangle_smul_right_of_ne_zero _ _ hcN]
  -- Step 4: the full chase
  have hfin : (2 : ℤ) • ∡ K P N = (2 : ℤ) • ∡ K A N := by
    rw [← hP2, ← hP1, smul_add, smul_add, h1, h2, h3, eB, eC, eD,
      ← smul_add, ← smul_add, hV1, hV2, ← eA]
  -- Step 5: conclude via the converse inscribed-angle criterion
  have hco : Cospherical ({K, P, A, N} : Set Plane) :=
    EuclideanGeometry.cospherical_of_two_zsmul_oangle_eq_of_not_collinear hfin hnc
  exact hco.subset (by simp [Set.insert_subset_iff])

/-- A dissection into cyclic quadrilaterals, one of which is an isosceles trapezoid; the
trapezoid witness is what allows the induction on the number of pieces to go through. -/
def DissectionWithTrapezoid (A B C D : Plane) (n : ℕ) : Prop :=
  ∃ d : CyclicDissection A B C D n, ∃ i : Fin n,
    IsoscelesTrapezoid (d.pieces i).1 (d.pieces i).2.1 (d.pieces i).2.2.1 (d.pieces i).2.2.2

/-- The pieces of the dissection obtained from `d` by replacing piece `i` by the two pieces
of `e`: index `i` hosts the first new piece, the new last index `n` hosts the second new
piece, and every other index keeps its old piece. -/
def succPieces {n : ℕ} {A B C D P₁ P₂ P₃ P₄ : Plane} (d : CyclicDissection A B C D n)
    (i : Fin n) (e : CyclicDissection P₁ P₂ P₃ P₄ 2) :
    Fin (n + 1) → Plane × Plane × Plane × Plane :=
  fun j ↦
    if j.val = i.val then e.pieces 0
    else if h : j.val < n then d.pieces ⟨j.val, h⟩
    else e.pieces 1

theorem succPieces_of_val_eq {n : ℕ} {A B C D P₁ P₂ P₃ P₄ : Plane}
    (d : CyclicDissection A B C D n) (i : Fin n) (e : CyclicDissection P₁ P₂ P₃ P₄ 2)
    {j : Fin (n + 1)} (h : j.val = i.val) : succPieces d i e j = e.pieces 0 :=
  if_pos h

theorem succPieces_of_val_eq_n {n : ℕ} {A B C D P₁ P₂ P₃ P₄ : Plane}
    (d : CyclicDissection A B C D n) (i : Fin n) (e : CyclicDissection P₁ P₂ P₃ P₄ 2)
    {j : Fin (n + 1)} (h₁ : j.val ≠ i.val) (h₂ : j.val = n) :
    succPieces d i e j = e.pieces 1 :=
  (if_neg h₁).trans (dif_neg (by omega))

theorem succPieces_of_old {n : ℕ} {A B C D P₁ P₂ P₃ P₄ : Plane}
    (d : CyclicDissection A B C D n) (i : Fin n) (e : CyclicDissection P₁ P₂ P₃ P₄ 2)
    {j : Fin (n + 1)} (h₁ : j.val ≠ i.val) (h₂ : j.val < n) :
    succPieces d i e j = d.pieces ⟨j.val, h₂⟩ :=
  (if_neg h₁).trans (dif_pos h₂)

/-- The three cases for the substituted family: the two new pieces at indices `i` and `n`,
and the old pieces everywhere else. -/
theorem succPieces_spec {n : ℕ} {A B C D P₁ P₂ P₃ P₄ : Plane}
    (d : CyclicDissection A B C D n) (i : Fin n) (e : CyclicDissection P₁ P₂ P₃ P₄ 2)
    (j : Fin (n + 1)) :
    (j.val = i.val ∧ succPieces d i e j = e.pieces 0) ∨
      (j.val = n ∧ succPieces d i e j = e.pieces 1) ∨
        ∃ j' : Fin n, j'.val = j.val ∧ j' ≠ i ∧ succPieces d i e j = d.pieces j' := by
  by_cases h₁ : j.val = i.val
  · exact .inl ⟨h₁, succPieces_of_val_eq d i e h₁⟩
  · by_cases h₂ : j.val < n
    · exact .inr (.inr ⟨⟨j.val, h₂⟩, rfl, fun hh ↦ h₁ (Fin.ext_iff.mp hh),
        succPieces_of_old d i e h₁ h₂⟩)
    · have hj := j.isLt
      exact .inr (.inl ⟨by omega, succPieces_of_val_eq_n d i e h₁ (by omega)⟩)

/-- The region of piece `i`, when that piece is the quadruple `(Q₁, Q₂, Q₃, Q₄)`. -/
theorem CyclicDissection.subset_of_pieces_eq {n : ℕ} {A B C D Q₁ Q₂ Q₃ Q₄ : Plane}
    (d : CyclicDissection A B C D n) {i : Fin n} (hi : d.pieces i = (Q₁, Q₂, Q₃, Q₄)) :
    quadRegion Q₁ Q₂ Q₃ Q₄ ⊆ quadRegion A B C D := by
  have h := d.subset i
  rw [hi] at h
  exact h

/-- The interior of piece `i` (when it is the quadruple `(Q₁, Q₂, Q₃, Q₄)`) is disjoint
from the interior of any other piece. -/
theorem CyclicDissection.disjoint_interior_of_pieces_eq {n : ℕ}
    {A B C D Q₁ Q₂ Q₃ Q₄ : Plane} (d : CyclicDissection A B C D n) {i j : Fin n}
    (hne : i ≠ j) (hi : d.pieces i = (Q₁, Q₂, Q₃, Q₄)) :
    Disjoint (interior (quadRegion Q₁ Q₂ Q₃ Q₄))
      (interior (quadRegion (d.pieces j).1 (d.pieces j).2.1 (d.pieces j).2.2.1
        (d.pieces j).2.2.2)) := by
  have hdi := d.disjoint i j hne
  rw [hi] at hdi
  exact hdi

/-- The interior of any piece is disjoint from the interior of piece `j`, when that piece
is the quadruple `(Q₁, Q₂, Q₃, Q₄)`. -/
theorem CyclicDissection.disjoint_interior_of_pieces_eq' {n : ℕ}
    {A B C D Q₁ Q₂ Q₃ Q₄ : Plane} (d : CyclicDissection A B C D n) {i j : Fin n}
    (hne : i ≠ j) (hj : d.pieces j = (Q₁, Q₂, Q₃, Q₄)) :
    Disjoint (interior (quadRegion (d.pieces i).1 (d.pieces i).2.1 (d.pieces i).2.2.1
      (d.pieces i).2.2.2)) (interior (quadRegion Q₁ Q₂ Q₃ Q₄)) := by
  have hdi := d.disjoint i j hne
  rw [hj] at hdi
  exact hdi

/-- Substituting a dissection of piece `i` (into two pieces) for piece `i` itself refines a
dissection into `n` cyclic quadrilaterals to a dissection into `n + 1` cyclic
quadrilaterals. -/
def CyclicDissection.succ {n : ℕ} {A B C D P₁ P₂ P₃ P₄ : Plane}
    (d : CyclicDissection A B C D n) (i : Fin n) (hi : d.pieces i = (P₁, P₂, P₃, P₄))
    (e : CyclicDissection P₁ P₂ P₃ P₄ 2) : CyclicDissection A B C D (n + 1) where
  pieces := succPieces d i e
  cyclic := by
    intro j
    rcases succPieces_spec d i e j with ⟨hs, hw⟩ | ⟨hs, hw⟩ | ⟨j', hj, hne, hw⟩
    · rw [hw]; exact e.cyclic 0
    · rw [hw]; exact e.cyclic 1
    · rw [hw]; exact d.cyclic j'
  subset := by
    intro j
    rcases succPieces_spec d i e j with ⟨hs, hw⟩ | ⟨hs, hw⟩ | ⟨j', hj, hne, hw⟩
    · rw [hw]; exact (e.subset 0).trans (d.subset_of_pieces_eq hi)
    · rw [hw]; exact (e.subset 1).trans (d.subset_of_pieces_eq hi)
    · rw [hw]; exact d.subset j'
  cover := by
    intro x hx
    obtain ⟨i₀, hx₀⟩ := Set.mem_iUnion.mp (d.cover hx)
    by_cases h₀ : i₀ = i
    · rw [h₀] at hx₀
      rw [hi] at hx₀
      obtain ⟨k, hxk⟩ := Set.mem_iUnion.mp (e.cover hx₀)
      fin_cases k
      · refine Set.mem_iUnion.mpr ⟨⟨i.val, Nat.lt_succ_of_lt i.isLt⟩, ?_⟩
        rcases succPieces_spec d i e ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ with
          ⟨hs, hw⟩ | ⟨hs, hw⟩ | ⟨j', hj, hne, hw⟩
        · rw [hw]; exact hxk
        · change i.val = n at hs; have := i.isLt; omega
        · exact absurd (Fin.ext hj) hne
      · refine Set.mem_iUnion.mpr ⟨⟨n, Nat.lt_succ_self n⟩, ?_⟩
        rcases succPieces_spec d i e ⟨n, Nat.lt_succ_self n⟩ with
          ⟨hs, hw⟩ | ⟨hs, hw⟩ | ⟨j', hj, hne, hw⟩
        · change n = i.val at hs; have := i.isLt; omega
        · rw [hw]; exact hxk
        · change j'.val = n at hj; have := j'.isLt; omega
    · refine Set.mem_iUnion.mpr ⟨⟨i₀.val, Nat.lt_succ_of_lt i₀.isLt⟩, ?_⟩
      rcases succPieces_spec d i e ⟨i₀.val, Nat.lt_succ_of_lt i₀.isLt⟩ with
        ⟨hs, hw⟩ | ⟨hs, hw⟩ | ⟨j', hj, hne, hw⟩
      · exact absurd (Fin.ext hs) h₀
      · change i₀.val = n at hs; have := i₀.isLt; omega
      · rw [hw, Fin.ext hj]; exact hx₀
  disjoint := by
    intro j₁ j₂ hne
    rcases succPieces_spec d i e j₁ with ⟨h₁, hw₁⟩ | ⟨h₁, hw₁⟩ | ⟨j₁', hj₁, hne₁, hw₁⟩ <;>
    rcases succPieces_spec d i e j₂ with ⟨h₂, hw₂⟩ | ⟨h₂, hw₂⟩ | ⟨j₂', hj₂, hne₂, hw₂⟩
    · rw [hw₁, hw₂]; exact absurd (Fin.ext (h₁.trans h₂.symm)) hne
    · rw [hw₁, hw₂]; exact e.disjoint 0 1 (by decide)
    · rw [hw₁, hw₂]
      exact Disjoint.mono (interior_mono (e.subset 0)) le_rfl
        (d.disjoint_interior_of_pieces_eq (Ne.symm hne₂) hi)
    · rw [hw₁, hw₂]; exact e.disjoint 1 0 (by decide)
    · rw [hw₁, hw₂]; exact absurd (Fin.ext (h₁.trans h₂.symm)) hne
    · rw [hw₁, hw₂]
      exact Disjoint.mono (interior_mono (e.subset 1)) le_rfl
        (d.disjoint_interior_of_pieces_eq (Ne.symm hne₂) hi)
    · rw [hw₁, hw₂]
      exact Disjoint.mono le_rfl (interior_mono (e.subset 0))
        (d.disjoint_interior_of_pieces_eq' hne₁ hi)
    · rw [hw₁, hw₂]
      exact Disjoint.mono le_rfl (interior_mono (e.subset 1))
        (d.disjoint_interior_of_pieces_eq' hne₁ hi)
    · rw [hw₁, hw₂]
      exact d.disjoint j₁' j₂'
        (fun hh ↦ hne (Fin.ext ((hj₁.symm.trans (congrArg Fin.val hh)).trans hj₂)))

/-! ### Convexity / nondegeneracy facts about `ConvexQuad` -/

/-- Three points of a convex quadrilateral with one vertex "between" the other two in the
boundary order are never collinear: if each of `X, Y, Z` avoids the convex hull of the
remaining triple (with `W` the fourth point), then `ω (X - Y) (Z - Y) ≠ 0`. -/
theorem ω_ne_zero_of_not_mem_hull {X Y Z W : Plane}
    (h₁ : X ∉ convexHull ℝ {Y, Z, W}) (h₂ : Y ∉ convexHull ℝ {Z, W, X})
    (h₃ : Z ∉ convexHull ℝ {W, X, Y}) : ω (X - Y) (Z - Y) ≠ 0 := by
  intro hω
  have hXY : X ≠ Y := by
    intro he
    apply h₁
    rw [he]
    exact subset_convexHull ℝ _ (Set.mem_insert _ _)
  obtain ⟨t, ht⟩ := exists_smul_of_ω_eq_zero (sub_ne_zero.mpr hXY) hω
  have hZ : Z = (1 - t) • Y + t • X := by
    rw [show Z = Y + (Z - Y) by module, ht]
    module
  by_cases ht0 : t ≤ 0
  · -- `Y ∈ segment Z X ⊆ hull {Z, W, X}`, contradicting `h₂`
    apply h₂
    have h1t : (0 : ℝ) < 1 - t := by linarith
    have hseg : Y ∈ segment ℝ Z X := by
      refine ⟨(1 - t)⁻¹, -t * (1 - t)⁻¹, inv_nonneg.mpr h1t.le,
        mul_nonneg (neg_nonneg.mpr ht0) (inv_nonneg.mpr h1t.le), ?_, ?_⟩
      · have hsum : (1 - t)⁻¹ + -t * (1 - t)⁻¹ = (1 - t) * (1 - t)⁻¹ := by ring
        rw [hsum, mul_inv_cancel₀ h1t.ne']
      · rw [hZ, smul_add, smul_smul, smul_smul, inv_mul_cancel₀ h1t.ne', one_smul,
          add_assoc, ← add_smul]
        have hsc : (1 - t)⁻¹ * t + -t * (1 - t)⁻¹ = 0 := by ring
        rw [hsc, zero_smul, add_zero]
    exact Convex.segment_subset (convex_convexHull ℝ _)
      (subset_convexHull ℝ _ (Set.mem_insert _ _))
      (subset_convexHull ℝ _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
        (Set.mem_singleton _)))) hseg
  · push Not at ht0
    rcases lt_or_ge t 1 with ht1 | ht1
    · -- `Z ∈ segment X Y ⊆ hull {W, X, Y}`, contradicting `h₃`
      apply h₃
      have hseg : Z ∈ segment ℝ X Y :=
        ⟨t, 1 - t, ht0.le, sub_nonneg.mpr ht1.le, add_sub_cancel t 1,
          by rw [hZ]; module⟩
      exact Convex.segment_subset (convex_convexHull ℝ _)
        (subset_convexHull ℝ _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
        (subset_convexHull ℝ _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
          (Set.mem_singleton _)))) hseg
    · -- `X ∈ segment Y Z ⊆ hull {Y, Z, W}`, contradicting `h₁`
      apply h₁
      have htpos : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht1
      have htne : t ≠ 0 := htpos.ne'
      have hseg : X ∈ segment ℝ Y Z := by
        refine ⟨1 - t⁻¹, t⁻¹, sub_nonneg.mpr (inv_le_one_of_one_le₀ ht1),
          inv_nonneg.mpr htpos.le, sub_add_cancel 1 t⁻¹, ?_⟩
        rw [hZ, smul_add, smul_smul, smul_smul, inv_mul_cancel₀ htne, one_smul,
          ← add_assoc, ← add_smul]
        have hsc : (1 - t⁻¹) + t⁻¹ * (1 - t) = 0 := by
          rw [mul_sub, mul_one, inv_mul_cancel₀ htne]
          ring
        rw [hsc, zero_smul, zero_add]
      exact Convex.segment_subset (convex_convexHull ℝ _)
        (subset_convexHull ℝ _ (Set.mem_insert _ _))
        (subset_convexHull ℝ _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))) hseg
/-- The triangle `A B D` cut off by a diagonal of a convex quadrilateral is
nondegenerate. -/
theorem ConvexQuad.ω_ABD_ne {A B C D : Plane} (h : ConvexQuad A B C D) :
    ω (A - B) (D - B) ≠ 0 := by
  apply ω_ne_zero_of_not_mem_hull (X := A) (Y := B) (Z := D) (W := C)
  · rw [show ({B, D, C} : Set Plane) = {B, C, D} by
        ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]
    exact h.not_mem₁
  · rw [show ({D, C, A} : Set Plane) = {C, D, A} by
        ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]
    exact h.not_mem₂
  · rw [show ({C, A, B} : Set Plane) = {A, B, C} by
        ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]
    exact h.not_mem₄

/-- The triangle `B C D` cut off by a diagonal of a convex quadrilateral is
nondegenerate. -/
theorem ConvexQuad.ω_BCD_ne {A B C D : Plane} (h : ConvexQuad A B C D) :
    ω (B - C) (D - C) ≠ 0 :=
  ω_ne_zero_of_not_mem_hull (X := B) (Y := C) (Z := D) (W := A)
    h.not_mem₂ h.not_mem₃ h.not_mem₄

theorem ConvexQuad.ne₁₂ {A B C D : Plane} (h : ConvexQuad A B C D) : A ≠ B := by
  intro he
  apply h.not_mem₁
  rw [he]
  exact subset_convexHull ℝ _ (Set.mem_insert _ _)

theorem ConvexQuad.ne₂₃ {A B C D : Plane} (h : ConvexQuad A B C D) : B ≠ C := by
  intro he
  apply h.not_mem₂
  rw [he]
  exact subset_convexHull ℝ _ (Set.mem_insert _ _)

theorem ConvexQuad.ne₃₄ {A B C D : Plane} (h : ConvexQuad A B C D) : C ≠ D := by
  intro he
  apply h.not_mem₃
  rw [he]
  exact subset_convexHull ℝ _ (Set.mem_insert _ _)

theorem ConvexQuad.ne₄₁ {A B C D : Plane} (h : ConvexQuad A B C D) : D ≠ A := by
  intro he
  apply h.not_mem₄
  rw [he]
  exact subset_convexHull ℝ _ (Set.mem_insert _ _)

/-- Collinear triples have vanishing `ω`. -/
theorem ω_eq_zero_of_collinear {x y z : Plane} (h : Collinear ℝ ({x, y, z} : Set Plane)) :
    ω (y - x) (z - x) = 0 := by
  rw [collinear_iff_exists_forall_eq_smul_vadd] at h
  obtain ⟨p₀, v, hv⟩ := h
  obtain ⟨r₁, h₁⟩ := hv x (Set.mem_insert _ _)
  obtain ⟨r₂, h₂⟩ := hv y (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  obtain ⟨r₃, h₃⟩ := hv z (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
    (Set.mem_singleton _)))
  simp only [h₁, h₂, h₃, vadd_eq_add, add_sub_add_right_eq_sub, ← sub_smul,
    ω_smul_left, ω_smul_right, ω_self, mul_zero]

/-! ### The construction layer: cosphericality "by construction" (all proved)

The next three theorems formalize the kalva construction circle-by-circle.  They show
that the three "outer" cosphericality facts of `landing_crux` are *by construction*:
given `s ∈ (0,1)` (and, for the later circles, the previously landed point being
strictly inside its side — the only analytic input), the circumsphere of the previous
triple is nondegenerate and its second intersection with the next side lies on that side
and is cospherical with the triple.  Neither cyclicity nor any landing estimate is used
here; those enter only in `landing_crux`. -/

/-- **Layer 1 of the construction.**  For every `s ∈ (0,1)`, with `K = lineMap A B s`
and `P = lineMap B D (1 - s)`, the circle through `B, K, P` is nondegenerate, and its
second intersection `L` with the line `BC` lies on that line and is cospherical with
`B, K, P`. -/
theorem landing_layer_L {A B C D : Plane} (h : ConvexQuad A B C D) {s : ℝ} (_hs0 : 0 < s) (hs1 : s < 1) :
    ∃ (L : Plane) (t : ℝ), L = AffineMap.lineMap B C t ∧
      Cospherical ({B, AffineMap.lineMap A B s, L,
        AffineMap.lineMap B D (1 - s)} : Set Plane) := by
  set K : Plane := AffineMap.lineMap A B s with hKdef
  set P : Plane := AffineMap.lineMap B D (1 - s) with hPdef
  have h1s : (1 : ℝ) - s ≠ 0 := by linarith
  have hvK : K - B = (1 - s) • (A - B) := by
    rw [hKdef, AffineMap.lineMap_apply_module]; module
  have hvP : P - B = (1 - s) • (D - B) := by
    rw [hPdef, AffineMap.lineMap_apply_module]; module
  -- nondegeneracy: `B, K, P` are not collinear (since `KP ∥ AD` and `A, B, D` are not
  -- collinear)
  have hnc : ¬ Collinear ℝ ({B, K, P} : Set Plane) := by
    intro hcol
    have h0 : ω (K - B) (P - B) = 0 := ω_eq_zero_of_collinear hcol
    rw [hvK, hvP, ω_smul_left, ω_smul_right] at h0
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact h1s h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · exact h1s h2
      · exact h.ω_ABD_ne h2
  set sx : Affine.Simplex ℝ Plane 2 :=
    Affine.Simplex.mk ![B, K, P] (affineIndependent_iff_not_collinear_set.mpr hnc)
    with hsx
  set L : Plane := sx.circumsphere.secondInter B (C -ᵥ B) with hLdef
  have hpts : sx.points = ![B, K, P] := by rw [hsx]
  have hBsp : B ∈ sx.circumsphere := by
    have h0 := sx.mem_circumsphere (0 : Fin 3)
    rwa [show sx.points (0 : Fin 3) = B by rw [hpts]; rfl] at h0
  have hKsp : K ∈ sx.circumsphere := by
    have h1 := sx.mem_circumsphere (1 : Fin 3)
    rwa [show sx.points (1 : Fin 3) = K by rw [hpts]; rfl] at h1
  have hPsp : P ∈ sx.circumsphere := by
    have h2 := sx.mem_circumsphere (2 : Fin 3)
    rwa [show sx.points (2 : Fin 3) = P by rw [hpts]; rfl] at h2
  have hLsp : L ∈ sx.circumsphere := (Sphere.secondInter_mem _).2 hBsp
  have hLline : L ∈ line[ℝ, B, C] := Sphere.secondInter_vsub_mem_affineSpan _ _ _
  -- extract the line parameter of `L` on `BC`
  have hcol : Collinear ℝ ({B, C, L} : Set Plane) := by
    rw [Set.pair_comm, Set.insert_comm]
    exact (collinear_insert_iff_of_mem_affineSpan hLline).2 (collinear_pair ℝ _ _)
  have h0 : ω (C - B) (L - B) = 0 := ω_eq_zero_of_collinear hcol
  obtain ⟨t, ht⟩ := exists_smul_of_ω_eq_zero (sub_ne_zero.mpr h.ne₂₃.symm) h0
  have hLm : L = AffineMap.lineMap B C t := by
    rw [AffineMap.lineMap_apply_module', ← ht]
    module
  refine ⟨L, t, hLm, sx.circumsphere.center, sx.circumsphere.radius, fun q hq ↦ ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact mem_sphere.mp hBsp
  · exact mem_sphere.mp hKsp
  · exact mem_sphere.mp hLsp
  · exact mem_sphere.mp hPsp

/-- **Layer 2 of the construction.**  Given `L = lineMap B C tL` with `tL < 1` (the only
landing input needed at this stage), the circle through `C, L, P` is nondegenerate, and
its second intersection `M` with the line `CD` lies on that line and is cospherical with
`C, L, P`. -/
theorem landing_layer_M {A B C D : Plane} (h : ConvexQuad A B C D) {s : ℝ} (_hs0 : 0 < s) (hs1 : s < 1)
    {L : Plane} {tL : ℝ} (hLt : L = AffineMap.lineMap B C tL) (htL1 : tL < 1) :
    ∃ (M : Plane) (t : ℝ), M = AffineMap.lineMap C D t ∧
      Cospherical ({C, L, M, AffineMap.lineMap B D (1 - s)} : Set Plane) := by
  set P : Plane := AffineMap.lineMap B D (1 - s) with hPdef
  have h1s : (1 : ℝ) - s ≠ 0 := by linarith
  have h1tL : (1 : ℝ) - tL ≠ 0 := by linarith
  have hvLC : L - C = (1 - tL) • (B - C) := by
    rw [hLt, AffineMap.lineMap_apply_module]; module
  have hvPC : P - C = (1 - s) • (D - B) + (B - C) := by
    rw [hPdef, AffineMap.lineMap_apply_module]; module
  -- nondegeneracy: `C, L, P` are not collinear (since `L ≠ C` and `P ∉ line BC`)
  have hnc : ¬ Collinear ℝ ({C, L, P} : Set Plane) := by
    intro hcol
    have h0 : ω (L - C) (P - C) = 0 := ω_eq_zero_of_collinear hcol
    rw [hvLC, hvPC, ω_smul_left, ω_add_right, ω_smul_right, ω_self, add_zero] at h0
    have hω : ω (B - C) (D - B) ≠ 0 := by
      have e : ω (B - C) (D - B) = ω (B - C) (D - C) := by
        simp only [ω, PiLp.sub_apply]; ring
      rw [e]; exact h.ω_BCD_ne
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact h1tL h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · exact h1s h2
      · exact hω h2
  set sx : Affine.Simplex ℝ Plane 2 :=
    Affine.Simplex.mk ![C, L, P] (affineIndependent_iff_not_collinear_set.mpr hnc)
    with hsx
  set M : Plane := sx.circumsphere.secondInter C (D -ᵥ C) with hMdef
  have hpts : sx.points = ![C, L, P] := by rw [hsx]
  have hCsp : C ∈ sx.circumsphere := by
    have h0 := sx.mem_circumsphere (0 : Fin 3)
    rwa [show sx.points (0 : Fin 3) = C by rw [hpts]; rfl] at h0
  have hLsp : L ∈ sx.circumsphere := by
    have h1 := sx.mem_circumsphere (1 : Fin 3)
    rwa [show sx.points (1 : Fin 3) = L by rw [hpts]; rfl] at h1
  have hPsp : P ∈ sx.circumsphere := by
    have h2 := sx.mem_circumsphere (2 : Fin 3)
    rwa [show sx.points (2 : Fin 3) = P by rw [hpts]; rfl] at h2
  have hMsp : M ∈ sx.circumsphere := (Sphere.secondInter_mem _).2 hCsp
  have hMline : M ∈ line[ℝ, C, D] := Sphere.secondInter_vsub_mem_affineSpan _ _ _
  have hcol : Collinear ℝ ({C, D, M} : Set Plane) := by
    rw [Set.pair_comm, Set.insert_comm]
    exact (collinear_insert_iff_of_mem_affineSpan hMline).2 (collinear_pair ℝ _ _)
  have h0 : ω (D - C) (M - C) = 0 := ω_eq_zero_of_collinear hcol
  obtain ⟨t, ht⟩ := exists_smul_of_ω_eq_zero (sub_ne_zero.mpr h.ne₃₄.symm) h0
  have hMm : M = AffineMap.lineMap C D t := by
    rw [AffineMap.lineMap_apply_module', ← ht]
    module
  refine ⟨M, t, hMm, sx.circumsphere.center, sx.circumsphere.radius, fun q hq ↦ ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact mem_sphere.mp hCsp
  · exact mem_sphere.mp hLsp
  · exact mem_sphere.mp hMsp
  · exact mem_sphere.mp hPsp

/-- **Layer 3 of the construction.**  Given `M = lineMap C D tM` with `tM < 1`, the
circle through `D, M, P` is nondegenerate, and its second intersection `N` with the line
`DA` lies on that line and is cospherical with `D, M, P`. -/
theorem landing_layer_N {A B C D : Plane} (h : ConvexQuad A B C D) {s : ℝ} (hs0 : 0 < s) (_hs1 : s < 1)
    {M : Plane} {tM : ℝ} (hMt : M = AffineMap.lineMap C D tM) (htM1 : tM < 1) :
    ∃ (N : Plane) (t : ℝ), N = AffineMap.lineMap D A t ∧
      Cospherical ({D, M, N, AffineMap.lineMap B D (1 - s)} : Set Plane) := by
  set P : Plane := AffineMap.lineMap B D (1 - s) with hPdef
  have h1tM : (1 : ℝ) - tM ≠ 0 := by linarith
  have hvMD : M - D = (1 - tM) • (C - D) := by
    rw [hMt, AffineMap.lineMap_apply_module]; module
  have hvPD : P - D = s • (B - D) := by
    rw [hPdef, AffineMap.lineMap_apply_module]; module
  -- nondegeneracy: `D, M, P` are not collinear (since `M ≠ D` and `P ∉ line CD`)
  have hnc : ¬ Collinear ℝ ({D, M, P} : Set Plane) := by
    intro hcol
    have h0 : ω (M - D) (P - D) = 0 := ω_eq_zero_of_collinear hcol
    rw [hvMD, hvPD, ω_smul_left, ω_smul_right] at h0
    have hω : ω (C - D) (B - D) ≠ 0 := by
      have e : ω (C - D) (B - D) = ω (B - C) (D - C) := by
        simp only [ω, PiLp.sub_apply]; ring
      rw [e]; exact h.ω_BCD_ne
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact h1tM h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · linarith
      · exact hω h2
  set sx : Affine.Simplex ℝ Plane 2 :=
    Affine.Simplex.mk ![D, M, P] (affineIndependent_iff_not_collinear_set.mpr hnc)
    with hsx
  set N : Plane := sx.circumsphere.secondInter D (A -ᵥ D) with hNdef
  have hpts : sx.points = ![D, M, P] := by rw [hsx]
  have hDsp : D ∈ sx.circumsphere := by
    have h0 := sx.mem_circumsphere (0 : Fin 3)
    rwa [show sx.points (0 : Fin 3) = D by rw [hpts]; rfl] at h0
  have hMsp : M ∈ sx.circumsphere := by
    have h1 := sx.mem_circumsphere (1 : Fin 3)
    rwa [show sx.points (1 : Fin 3) = M by rw [hpts]; rfl] at h1
  have hPsp : P ∈ sx.circumsphere := by
    have h2 := sx.mem_circumsphere (2 : Fin 3)
    rwa [show sx.points (2 : Fin 3) = P by rw [hpts]; rfl] at h2
  have hNsp : N ∈ sx.circumsphere := (Sphere.secondInter_mem _).2 hDsp
  have hNline : N ∈ line[ℝ, D, A] := Sphere.secondInter_vsub_mem_affineSpan _ _ _
  have hcol : Collinear ℝ ({D, A, N} : Set Plane) := by
    rw [Set.pair_comm, Set.insert_comm]
    exact (collinear_insert_iff_of_mem_affineSpan hNline).2 (collinear_pair ℝ _ _)
  have h0 : ω (A - D) (N - D) = 0 := ω_eq_zero_of_collinear hcol
  obtain ⟨t, ht⟩ := exists_smul_of_ω_eq_zero (sub_ne_zero.mpr h.ne₄₁.symm) h0
  have hNm : N = AffineMap.lineMap D A t := by
    rw [AffineMap.lineMap_apply_module', ← ht]
    module
  refine ⟨N, t, hNm, sx.circumsphere.center, sx.circumsphere.radius, fun q hq ↦ ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact mem_sphere.mp hDsp
  · exact mem_sphere.mp hMsp
  · exact mem_sphere.mp hNsp
  · exact mem_sphere.mp hPsp

/-! ### Exact algebra for the landing

The landing is cracked by the observation that the whole construction is *exactly
linear* in `s` (no asymptotics needed): `tL = 1 - s` (homothety), and the power-of-point
identities give `tM = 1 - s * (|BD|² - |BC|²) / |CD|²` and `tN = s * (|BD|² - |AB|²) / |AD|²`
exactly.  The last one uses cyclicity, in the polynomial form `cyclicity_identity`
(which is the circle determinant in disguise). -/

/-- Squared distance in coordinates. -/
theorem dist_sq_fin2 (x y : Plane) : dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq,
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  simp only [Real.dist_eq, sq_abs, Fin.sum_univ_two]

/-- Piece 1 of the construction is cyclic *by homothety*: `K, L, P` are the images of
`A, C, D` under the homothety `h(B, 1 - s)`, so `B, K, L, P` lie on the image of the
circumcircle. -/
theorem cospherical_BKLP {A B C D O : Plane} {r s : ℝ} (hs : s < 1)
    (hA : dist A O = r) (hB : dist B O = r) (hC : dist C O = r) (hD : dist D O = r) :
    Cospherical ({B, s • B + (1 - s) • A, s • B + (1 - s) • C,
      s • B + (1 - s) • D} : Set Plane) := by
  have h1s : (0 : ℝ) ≤ 1 - s := sub_nonneg.mpr hs.le
  refine ⟨s • B + (1 - s) • O, (1 - s) * r, fun q hq ↦ ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
  have hmod : ∀ X : Plane, s • B + (1 - s) • X - (s • B + (1 - s) • O) =
      (1 - s) • (X - O) := fun X ↦ by module
  have hmodB : B - (s • B + (1 - s) • O) = (1 - s) • (B - O) := by module
  have hcalc : ∀ X : Plane, dist (s • B + (1 - s) • X) (s • B + (1 - s) • O) =
      (1 - s) * dist X O := fun X ↦ by
    rw [dist_eq_norm, hmod, norm_smul, Real.norm_of_nonneg h1s, ← dist_eq_norm]
  rcases hq with rfl | rfl | rfl | rfl
  · rw [dist_eq_norm, hmodB, norm_smul, Real.norm_of_nonneg h1s, ← dist_eq_norm, hB]
  · rw [hcalc, hA]
  · rw [hcalc, hC]
  · rw [hcalc, hD]

/-- The exact power identity for the second circle: if the homothety images `L, P` and
`C` are equidistant from `o₂` (i.e. lie on a circle of center `o₂`), then the power of
`D` w.r.t. that circle is exactly `s * (|BD|² - |BC|²)`.  Pure algebra (no cyclicity). -/
theorem pow_identity_CD {B C D o₂ : Plane} {s : ℝ} (hs : s ≠ 1)
    (h₁ : dist (s • B + (1 - s) • C) o₂ = dist C o₂)
    (h₂ : dist (s • B + (1 - s) • D) o₂ = dist C o₂) :
    dist D o₂ ^ 2 - dist C o₂ ^ 2 = s * (dist B D ^ 2 - dist B C ^ 2) := by
  have H₁ := congrArg (· ^ 2) h₁
  have H₂ := congrArg (· ^ 2) h₂
  have key : (1 - s) * (dist D o₂ ^ 2 - dist C o₂ ^ 2) =
      (1 - s) * (s * (dist B D ^ 2 - dist B C ^ 2)) := by
    simp only [dist_sq_fin2, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at H₁ H₂ ⊢
    linear_combination H₂ - H₁
  exact mul_left_cancel₀ (sub_ne_zero.mpr hs.symm) key

/-- The cyclicity identity (a polynomial form of cocircularity, in fact the circle
determinant `det[|Pᵢ|², xᵢ, yᵢ, 1]`): the `ω`-combination that governs the third-stage
parameter vanishes for four points on a common circle. -/
theorem cyclicity_identity {A B C D O : Plane} {r : ℝ}
    (hA : dist A O = r) (hB : dist B O = r) (hC : dist C O = r) (hD : dist D O = r) :
    ω (D - C) (A - D) * dist B D ^ 2 -
      ω (A - D) (B - D) * (dist B D ^ 2 - dist B C ^ 2) -
      ω (D - C) (B - D) * (dist B D ^ 2 - dist A B ^ 2) = 0 := by
  have hA2 : (A 0 - O 0) ^ 2 + (A 1 - O 1) ^ 2 = r ^ 2 := by
    rw [← dist_sq_fin2, hA]
  have hB2 : (B 0 - O 0) ^ 2 + (B 1 - O 1) ^ 2 = r ^ 2 := by
    rw [← dist_sq_fin2, hB]
  have hC2 : (C 0 - O 0) ^ 2 + (C 1 - O 1) ^ 2 = r ^ 2 := by
    rw [← dist_sq_fin2, hC]
  have hD2 : (D 0 - O 0) ^ 2 + (D 1 - O 1) ^ 2 = r ^ 2 := by
    rw [← dist_sq_fin2, hD]
  simp only [dist_sq_fin2, ω, PiLp.sub_apply]
  linear_combination
    ((B 0) * (C 1) - (B 0) * (D 1) - (B 1) * (C 0) + (B 1) * (D 0) + (C 0) * (D 1) -
      (C 1) * (D 0)) * hA2 +
    (-(A 0) * (C 1) + (A 0) * (D 1) + (A 1) * (C 0) - (A 1) * (D 0) - (C 0) * (D 1) +
      (C 1) * (D 0)) * hB2 +
    ((A 0) * (B 1) - (A 0) * (D 1) - (A 1) * (B 0) + (A 1) * (D 0) + (B 0) * (D 1) -
      (B 1) * (D 0)) * hC2 +
    (-(A 0) * (B 1) + (A 0) * (C 1) + (A 1) * (B 0) - (A 1) * (C 0) - (B 0) * (C 1) +
      (B 1) * (C 0)) * hD2

/-! ### The crux: kalva's landing analysis (proved, under the anchor condition) -/

/-- **The anchor theorem (kalva's landing, exact form).**  If the diagonal `BD` is
strictly longer than both sides adjacent to `B` (the "anchor at `A`" case), then the
kalva construction with `P = lineMap B D (1 - s)` lands for any small enough `s`
(the two `hbound` hypotheses are exactly `tM > 0` and `tN < 1`).
Everything is exact: `tL = 1 - s`, `tM = 1 - s * (|BD|² - |BC|²) / |CD|²`,
`tN = s * (|BD|² - |AB|²) / |AD|²`. -/
theorem landing_anchor {A B C D : Plane} (h : ConvexQuad A B C D)
    (hcyc : ∃ O : Plane, ∃ r : ℝ, dist A O = r ∧ dist B O = r ∧ dist C O = r ∧
      dist D O = r)
    (hdiag : dist B C < dist B D ∧ dist A B < dist B D)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hboundM : s * (dist B D ^ 2 - dist B C ^ 2) < dist C D ^ 2)
    (hboundN : s * (dist B D ^ 2 - dist A B ^ 2) < dist A D ^ 2) :
    ∃ (P K L M N : Plane),
      K = AffineMap.lineMap A B s ∧ P = AffineMap.lineMap B D (1 - s) ∧
      L = AffineMap.lineMap B C (1 - s) ∧
      M = AffineMap.lineMap C D ((dist C D ^ 2 - s * (dist B D ^ 2 - dist B C ^ 2)) /
        dist C D ^ 2) ∧
      N = AffineMap.lineMap D A (s * (dist B D ^ 2 - dist A B ^ 2) / dist A D ^ 2) ∧
      Sbtw ℝ A K B ∧ Sbtw ℝ B L C ∧ Sbtw ℝ C M D ∧ Sbtw ℝ D N A ∧
      Cospherical ({B, K, L, P} : Set Plane) ∧ Cospherical ({C, L, M, P} : Set Plane) ∧
      Cospherical ({D, M, N, P} : Set Plane) ∧ Cospherical ({A, K, P, N} : Set Plane) ∧
      (∃ c : ℝ, A - N = c • (P - K)) := by
  obtain ⟨O, r, hA, hB, hC, hD⟩ := hcyc
  have hAB : A ≠ B := h.ne₁₂
  have hBC : B ≠ C := h.ne₂₃
  have hCD : C ≠ D := h.ne₃₄
  have hDA : D ≠ A := h.ne₄₁
  have hωABD : ω (A - B) (D - B) ≠ 0 := h.ω_ABD_ne
  have hωBCD : ω (B - C) (D - C) ≠ 0 := h.ω_BCD_ne
  -- the two gaps are positive
  have hμ : 0 < dist B D ^ 2 - dist B C ^ 2 := by
    have hd := hdiag.1
    nlinarith [hd, @dist_nonneg _ _ B C, @dist_nonneg _ _ B D]
  have hκ : 0 < dist B D ^ 2 - dist A B ^ 2 := by
    have hd := hdiag.2
    nlinarith [hd, @dist_nonneg _ _ A B, @dist_nonneg _ _ B D]
  have hCD2 : 0 < dist C D ^ 2 := by
    have hd := dist_pos.mpr hCD
    nlinarith
  have hAD2 : 0 < dist A D ^ 2 := by
    have hd := dist_pos.mpr hDA.symm
    nlinarith
  have hs1' : s ≠ 1 := hs1.ne
  have hs0' : s ≠ 0 := hs0.ne'
  -- the three fixed points of the construction
  set K : Plane := AffineMap.lineMap A B s with hKdef
  set P : Plane := AffineMap.lineMap B D (1 - s) with hPdef
  set L : Plane := AffineMap.lineMap B C (1 - s) with hLdef
  have hvK : K - B = (1 - s) • (A - B) := by
    rw [hKdef, AffineMap.lineMap_apply_module]; module
  have hvP : P - B = (1 - s) • (D - B) := by
    rw [hPdef, AffineMap.lineMap_apply_module]; module
  have hvPK : P - K = (1 - s) • (D - A) := by
    rw [hPdef, hKdef, AffineMap.lineMap_apply_module, AffineMap.lineMap_apply_module]
    module
  have hvLC : L - C = s • (B - C) := by
    rw [hLdef, AffineMap.lineMap_apply_module]; module
  have hKs : K = s • B + (1 - s) • A := by
    rw [hKdef, AffineMap.lineMap_apply_module]; module
  have hPs : P = s • B + (1 - s) • D := by
    rw [hPdef, AffineMap.lineMap_apply_module]; module
  have hLs : L = s • B + (1 - s) • C := by
    rw [hLdef, AffineMap.lineMap_apply_module]; module
  -- piece 1: cyclic by homothety; `K` and `L` land on their sides
  have hBKP : Cospherical ({B, K, L, P} : Set Plane) := by
    rw [hKs, hPs, hLs]
    exact cospherical_BKLP hs1 hA hB hC hD
  have hKb : Sbtw ℝ A K B := sbtw_lineMap hAB hs0 hs1
  have hLb : Sbtw ℝ B L C := sbtw_lineMap hBC (by linarith) (by linarith)
  -- piece 2: the circle through `C, L, P`
  have hnc₂ : ¬ Collinear ℝ ({C, L, P} : Set Plane) := by
    intro hcol
    have h0 : ω (L - C) (P - C) = 0 := ω_eq_zero_of_collinear hcol
    have hvPC : P - C = (1 - s) • (D - B) + (B - C) := by
      rw [hPdef, AffineMap.lineMap_apply_module]; module
    rw [hvLC, hvPC, ω_smul_left, ω_add_right, ω_smul_right, ω_self, add_zero] at h0
    have hω : ω (B - C) (D - B) ≠ 0 := by
      have e : ω (B - C) (D - B) = ω (B - C) (D - C) := by
        simp only [ω, PiLp.sub_apply]; ring
      rw [e]; exact hωBCD
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact hs0' h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · exact hs1' (by linarith)
      · exact hω h2
  set sx₂ : Affine.Simplex ℝ Plane 2 :=
    Affine.Simplex.mk ![C, L, P] (affineIndependent_iff_not_collinear_set.mpr hnc₂)
    with hsx₂
  set M : Plane := sx₂.circumsphere.secondInter C (D -ᵥ C) with hMdef
  have hpts₂ : sx₂.points = ![C, L, P] := by rw [hsx₂]
  have hCsp : C ∈ sx₂.circumsphere := by
    have h0 := sx₂.mem_circumsphere (0 : Fin 3)
    rwa [show sx₂.points (0 : Fin 3) = C by rw [hpts₂]; rfl] at h0
  have hLsp : L ∈ sx₂.circumsphere := by
    have h1 := sx₂.mem_circumsphere (1 : Fin 3)
    rwa [show sx₂.points (1 : Fin 3) = L by rw [hpts₂]; rfl] at h1
  have hPsp : P ∈ sx₂.circumsphere := by
    have h2 := sx₂.mem_circumsphere (2 : Fin 3)
    rwa [show sx₂.points (2 : Fin 3) = P by rw [hpts₂]; rfl] at h2
  have hMsp : M ∈ sx₂.circumsphere := (Sphere.secondInter_mem _).2 hCsp
  have hCLP : Cospherical ({C, L, M, P} : Set Plane) :=
    ⟨sx₂.circumsphere.center, sx₂.circumsphere.radius, fun q hq ↦ by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact mem_sphere.mp hCsp
      · exact mem_sphere.mp hLsp
      · exact mem_sphere.mp hMsp
      · exact mem_sphere.mp hPsp⟩
  have hpow : dist D sx₂.circumsphere.center ^ 2 - dist C sx₂.circumsphere.center ^ 2 =
      s * (dist B D ^ 2 - dist B C ^ 2) := by
    refine pow_identity_CD hs1' ?_ ?_
    · rw [← hLs, mem_sphere.mp hLsp, mem_sphere.mp hCsp]
    · rw [← hPs, mem_sphere.mp hPsp, mem_sphere.mp hCsp]
  set tM : ℝ := (dist C D ^ 2 - s * (dist B D ^ 2 - dist B C ^ 2)) / dist C D ^ 2 with htM
  have hMlm : M = AffineMap.lineMap C D
      (-2 * ⟪D -ᵥ C, C -ᵥ sx₂.circumsphere.center⟫ / ⟪D -ᵥ C, D -ᵥ C⟫) :=
    Sphere.secondInter_eq_lineMap _ _ _
  have htval : -2 * ⟪D -ᵥ C, C -ᵥ sx₂.circumsphere.center⟫ / ⟪D -ᵥ C, D -ᵥ C⟫ = tM := by
    rw [htM]
    have e3 : dist D sx₂.circumsphere.center ^ 2 = dist C D ^ 2 +
        2 * ⟪D - C, C - sx₂.circumsphere.center⟫ + dist C sx₂.circumsphere.center ^ 2 := by
      rw [dist_eq_norm,
        show D - sx₂.circumsphere.center = (D - C) + (C - sx₂.circumsphere.center) by
          module,
        norm_add_sq_real, ← dist_eq_norm, ← dist_eq_norm, dist_comm D C]
    have e2 : -2 * ⟪D - C, C - sx₂.circumsphere.center⟫ =
        dist C D ^ 2 - s * (dist B D ^ 2 - dist B C ^ 2) := by
      linarith [hpow, e3]
    rw [vsub_eq_sub, vsub_eq_sub, e2, real_inner_self_eq_norm_sq,
      ← dist_eq_norm, dist_comm D C]
  have htM0 : 0 < tM := by
    rw [htM]
    exact div_pos (by linarith [hboundM]) hCD2
  have htM1 : tM < 1 := by
    rw [htM, div_lt_one hCD2]
    have h1 : 0 < s * (dist B D ^ 2 - dist B C ^ 2) := mul_pos hs0 hμ
    linarith
  have hMb : Sbtw ℝ C M D := by
    rw [hMlm, htval]
    exact sbtw_lineMap hCD htM0 htM1
  have hvMD : M - D = (1 - tM) • (C - D) := by
    rw [hMlm, htval, AffineMap.lineMap_apply_module]; module
  have hvPD : P - D = s • (B - D) := by
    rw [hPdef, AffineMap.lineMap_apply_module]; module
  -- piece 3: the circle through `D, M, P`
  have hnc₃ : ¬ Collinear ℝ ({D, M, P} : Set Plane) := by
    intro hcol
    have h0 : ω (M - D) (P - D) = 0 := ω_eq_zero_of_collinear hcol
    rw [hvMD, hvPD, ω_smul_left, ω_smul_right] at h0
    have h1tM : (1 : ℝ) - tM ≠ 0 := by linarith [htM1]
    have hω : ω (C - D) (B - D) ≠ 0 := by
      have e : ω (C - D) (B - D) = ω (B - C) (D - C) := by
        simp only [ω, PiLp.sub_apply]; ring
      rw [e]; exact hωBCD
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact h1tM h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · exact hs0' h2
      · exact hω h2
  set sx₃ : Affine.Simplex ℝ Plane 2 :=
    Affine.Simplex.mk ![D, M, P] (affineIndependent_iff_not_collinear_set.mpr hnc₃)
    with hsx₃
  set N : Plane := sx₃.circumsphere.secondInter D (A -ᵥ D) with hNdef
  have hpts₃ : sx₃.points = ![D, M, P] := by rw [hsx₃]
  have hDsp : D ∈ sx₃.circumsphere := by
    have h0 := sx₃.mem_circumsphere (0 : Fin 3)
    rwa [show sx₃.points (0 : Fin 3) = D by rw [hpts₃]; rfl] at h0
  have hMsp₃ : M ∈ sx₃.circumsphere := by
    have h1 := sx₃.mem_circumsphere (1 : Fin 3)
    rwa [show sx₃.points (1 : Fin 3) = M by rw [hpts₃]; rfl] at h1
  have hPsp₃ : P ∈ sx₃.circumsphere := by
    have h2 := sx₃.mem_circumsphere (2 : Fin 3)
    rwa [show sx₃.points (2 : Fin 3) = P by rw [hpts₃]; rfl] at h2
  have hNsp : N ∈ sx₃.circumsphere := (Sphere.secondInter_mem _).2 hDsp
  have hDMP : Cospherical ({D, M, N, P} : Set Plane) :=
    ⟨sx₃.circumsphere.center, sx₃.circumsphere.radius, fun q hq ↦ by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact mem_sphere.mp hDsp
      · exact mem_sphere.mp hMsp₃
      · exact mem_sphere.mp hNsp
      · exact mem_sphere.mp hPsp₃⟩
  -- the two exact inner-product identities for the third circle
  have hEM : 2 * ⟪D - sx₃.circumsphere.center, D - C⟫ = (1 - tM) * dist C D ^ 2 := by
    have hd : dist M sx₃.circumsphere.center = dist D sx₃.circumsphere.center := by
      rw [mem_sphere.mp hMsp₃, mem_sphere.mp hDsp]
    have e1 : M - sx₃.circumsphere.center =
        (D - sx₃.circumsphere.center) + (1 - tM) • (C - D) := by
      rw [← hvMD]; module
    have heq : dist M sx₃.circumsphere.center ^ 2 = dist D sx₃.circumsphere.center ^ 2 :=
      congrArg (· ^ 2) hd
    simp only [dist_eq_norm] at heq
    rw [e1, norm_add_sq_real, inner_smul_right, norm_smul,
      Real.norm_of_nonneg (sub_nonneg.mpr htM1.le)] at heq
    have e2 : 2 * (1 - tM) * ⟪D - sx₃.circumsphere.center, C - D⟫ +
        (1 - tM) ^ 2 * ‖C - D‖ ^ 2 = 0 := by
      linarith [heq]
    have e3 : (1 - tM) * (2 * ⟪D - sx₃.circumsphere.center, D - C⟫) =
        (1 - tM) * ((1 - tM) * dist C D ^ 2) := by
      rw [show C - D = -(D - C) by abel, inner_neg_right, norm_neg, ← dist_eq_norm, dist_comm D C] at e2
      linarith [e2]
    exact mul_left_cancel₀ (sub_ne_zero.mpr htM1.ne') e3
  have hEP : 2 * ⟪D - sx₃.circumsphere.center, B - D⟫ = -s * dist B D ^ 2 := by
    have hd : dist P sx₃.circumsphere.center = dist D sx₃.circumsphere.center := by
      rw [mem_sphere.mp hPsp₃, mem_sphere.mp hDsp]
    have e1 : P - sx₃.circumsphere.center = (D - sx₃.circumsphere.center) + s • (B - D) := by
      rw [← hvPD]; module
    have heq : dist P sx₃.circumsphere.center ^ 2 = dist D sx₃.circumsphere.center ^ 2 :=
      congrArg (· ^ 2) hd
    simp only [dist_eq_norm] at heq
    rw [e1, norm_add_sq_real, inner_smul_right, norm_smul,
      Real.norm_of_nonneg hs0.le] at heq
    have e2 : 2 * s * ⟪D - sx₃.circumsphere.center, B - D⟫ + s ^ 2 * ‖B - D‖ ^ 2 = 0 := by
      linarith [heq]
    have e3 : s * (2 * ⟪D - sx₃.circumsphere.center, B - D⟫) = s * (-s * dist B D ^ 2) := by
      rw [← dist_eq_norm] at e2
      linarith [e2]
    exact mul_left_cancel₀ hs0' e3
  -- the cyclicity identity and the Cramer step, giving the exact parameter of `N`
  have hF : ω (D - C) (A - D) * dist B D ^ 2 -
      ω (A - D) (B - D) * (dist B D ^ 2 - dist B C ^ 2) -
      ω (D - C) (B - D) * (dist B D ^ 2 - dist A B ^ 2) = 0 :=
    cyclicity_identity hA hB hC hD
  have hω₀ : ω (D - C) (B - D) ≠ 0 := by
    have e : ω (D - C) (B - D) = -ω (B - C) (D - C) := by
      simp only [ω, PiLp.sub_apply]; ring
    rw [e]; exact neg_ne_zero.mpr hωBCD
  have hCram : A - D = (ω (A - D) (B - D) / ω (D - C) (B - D)) • (D - C) +
      (ω (D - C) (A - D) / ω (D - C) (B - D)) • (B - D) :=
    eq_smul_add_smul_of_ω hω₀ (A - D)
  have hCDval : (1 - tM) * dist C D ^ 2 = s * (dist B D ^ 2 - dist B C ^ 2) := by
    rw [htM]
    have hCDn : dist C D ≠ 0 := dist_ne_zero.mpr hCD
    field_simp [hCDn]
    ring
  have htwo : 2 * ⟪A - D, D - sx₃.circumsphere.center⟫ =
      -s * (dist B D ^ 2 - dist A B ^ 2) := by
    have key : ω (D - C) (B - D) * (2 * ⟪A - D, D - sx₃.circumsphere.center⟫) =
        ω (D - C) (B - D) * (-s * (dist B D ^ 2 - dist A B ^ 2)) := by
      have e1 : ω (D - C) (B - D) * ⟪A - D, D - sx₃.circumsphere.center⟫ =
          ω (A - D) (B - D) * ⟪D - C, D - sx₃.circumsphere.center⟫ +
            ω (D - C) (A - D) * ⟪B - D, D - sx₃.circumsphere.center⟫ := by
        rw [← real_inner_smul_left]
        conv_lhs => rw [hCram]
        rw [real_inner_smul_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
          mul_add, ← mul_assoc, mul_div_cancel₀ _ hω₀, ← mul_assoc, mul_div_cancel₀ _ hω₀]
      have e2 : ω (D - C) (B - D) * (2 * ⟪A - D, D - sx₃.circumsphere.center⟫) =
          2 * (ω (D - C) (B - D) * ⟪A - D, D - sx₃.circumsphere.center⟫) := by ring
      rw [e2, e1, real_inner_comm (D - sx₃.circumsphere.center) (D - C),
        real_inner_comm (D - sx₃.circumsphere.center) (B - D)]
      have e3 : 2 * (ω (A - D) (B - D) * ⟪D - sx₃.circumsphere.center, D - C⟫ +
          ω (D - C) (A - D) * ⟪D - sx₃.circumsphere.center, B - D⟫) =
          ω (A - D) (B - D) * (2 * ⟪D - sx₃.circumsphere.center, D - C⟫) +
          ω (D - C) (A - D) * (2 * ⟪D - sx₃.circumsphere.center, B - D⟫) := by ring
      rw [e3, hEM, hEP, hCDval]
      linear_combination (-s) * hF
    exact mul_left_cancel₀ hω₀ key
  set tN : ℝ := s * (dist B D ^ 2 - dist A B ^ 2) / dist A D ^ 2 with htN
  have hNlm : N = AffineMap.lineMap D A
      (-2 * ⟪A -ᵥ D, D -ᵥ sx₃.circumsphere.center⟫ / ⟪A -ᵥ D, A -ᵥ D⟫) :=
    Sphere.secondInter_eq_lineMap _ _ _
  have htvalN : -2 * ⟪A -ᵥ D, D -ᵥ sx₃.circumsphere.center⟫ / ⟪A -ᵥ D, A -ᵥ D⟫ = tN := by
    rw [htN]
    have e1 : -2 * ⟪A - D, D - sx₃.circumsphere.center⟫ =
        s * (dist B D ^ 2 - dist A B ^ 2) := by
      linarith [htwo]
    rw [vsub_eq_sub, vsub_eq_sub, e1, real_inner_self_eq_norm_sq,
      ← dist_eq_norm]
  have htN0 : 0 < tN := by
    rw [htN]
    exact div_pos (mul_pos hs0 hκ) hAD2
  have htN1 : tN < 1 := by
    rw [htN, div_lt_one hAD2]
    exact hboundN
  have hNb : Sbtw ℝ D N A := by
    rw [hNlm, htvalN]
    exact sbtw_lineMap hDA htN0 htN1
  have hvN' : N - A = (1 - tN) • (D - A) := by
    rw [hNlm, htvalN, AffineMap.lineMap_apply_module]; module
  have hvN : N - D = tN • (A - D) := by
    rw [hNlm, htvalN, AffineMap.lineMap_apply_module]; module
  have hvNK : N - K = (1 - tN) • (D - A) - s • (B - A) := by
    rw [hNlm, htvalN, hKdef, AffineMap.lineMap_apply_module,
      AffineMap.lineMap_apply_module]; module
  -- distinctness of `P` from the four side points
  have hPK : P ≠ K := by
    intro he
    have h1 : (1 - s) • (D - B) = (1 - s) • (A - B) := by rw [← hvP, ← hvK, he]
    have h2 : (1 - s) • (D - B) - (1 - s) • (A - B) = 0 := sub_eq_zero.mpr h1
    rw [← smul_sub] at h2
    have hDB : D - B - (A - B) = D - A := by abel
    rw [hDB] at h2
    rcases smul_eq_zero.mp h2 with h3 | h3
    · linarith
    · exact hDA (sub_eq_zero.mp h3)
  have hPL : P ≠ L := by
    intro he
    have hvL : L - B = (1 - s) • (C - B) := by
      rw [hLdef, AffineMap.lineMap_apply_module]; module
    have h1 : (1 - s) • (D - B) = (1 - s) • (C - B) := by rw [← hvP, ← hvL, he]
    have h2 := congrArg (fun v : Plane ↦ ω v (C - B)) h1
    simp only [ω_smul_left, ω_self, mul_zero] at h2
    have hω : ω (D - B) (C - B) ≠ 0 := by
      have e : ω (D - B) (C - B) = ω (B - C) (D - C) := by
        simp only [ω, PiLp.sub_apply]; ring
      rw [e]; exact hωBCD
    rcases mul_eq_zero.mp h2 with h3 | h3
    · linarith
    · exact absurd h3 hω
  have hPM : P ≠ M := by
    intro he
    have h1 : s • (B - D) = (1 - tM) • (C - D) := by rw [← hvPD, ← hvMD, he]
    have h2 := congrArg (fun v : Plane ↦ ω v (C - D)) h1
    simp only [ω_smul_left, ω_self, mul_zero] at h2
    have hω : ω (B - D) (C - D) ≠ 0 := by
      have e : ω (B - D) (C - D) = -ω (B - C) (D - C) := by
        simp only [ω, PiLp.sub_apply]; ring
      rw [e]; exact neg_ne_zero.mpr hωBCD
    rcases mul_eq_zero.mp h2 with h3 | h3
    · linarith
    · exact absurd h3 hω
  have hPN : P ≠ N := by
    intro he
    have h1 : s • (B - D) = tN • (A - D) := by rw [← hvPD, ← hvN, he]
    have h2 := congrArg (fun v : Plane ↦ ω v (A - D)) h1
    simp only [ω_smul_left, ω_self, mul_zero] at h2
    have hω : ω (B - D) (A - D) ≠ 0 := by
      have e : ω (B - D) (A - D) = ω (A - B) (D - B) := by
        simp only [ω, PiLp.sub_apply]; ring
      rw [e]; exact hωABD
    rcases mul_eq_zero.mp h2 with h3 | h3
    · linarith
    · exact absurd h3 hω
  -- `K, P, N` are not collinear
  have hnc : ¬ Collinear ℝ ({K, P, N} : Set Plane) := by
    intro hcol
    have hω0 : ω (P - K) (N - K) = 0 := ω_eq_zero_of_collinear hcol
    rw [hvPK, hvNK, ω_smul_left, ω_sub_right, ω_smul_right, ω_smul_right, ω_self,
      mul_zero, zero_sub, mul_neg, neg_eq_zero] at hω0
    have hω : ω (D - A) (B - A) ≠ 0 := by
      have e : ω (D - A) (B - A) = ω (A - B) (D - B) := by
        simp only [ω, PiLp.sub_apply]; ring
      rw [e]; exact hωABD
    rcases mul_eq_zero.mp hω0 with h1 | h1
    · linarith
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · linarith
      · exact absurd h2 hω
  -- the A-piece is cyclic, by the pivot theorem
  have hAPN : Cospherical ({A, K, P, N} : Set Plane) :=
    pivot_cospherical ⟨1 - s, hvK⟩ ⟨s, hvLC⟩ ⟨1 - tM, hvMD⟩ ⟨1 - tN, hvN'⟩
      hBKP hCLP hDMP hAB hBC hCD hDA
      hKb.2.1 hKb.2.2 hLb.2.1 hLb.2.2 hMb.2.1 hMb.2.2 hNb.2.2 hNb.2.1
      hPK hPL hPM hPN hnc
  -- the trapezoid parallelism `KP ∥ AN`
  have h1s : (0 : ℝ) < 1 - s := sub_pos.mpr hs1
  have hpar : A - N = (-(1 - tN) / (1 - s)) • (P - K) := by
    rw [hvPK, smul_smul, div_mul_cancel₀ _ h1s.ne', neg_smul]
    rw [show A - N = -(N - A) by module, hvN']
  exact ⟨P, K, L, M, N, hKdef, hPdef, hLdef,
    hMlm.trans (congrArg (AffineMap.lineMap C D) htval),
    hNlm.trans (congrArg (AffineMap.lineMap D A) htvalN),
    hKb, hLb, hMb, hNb, hBKP, hCLP, hDMP, hAPN,
    ⟨-(1 - tN) / (1 - s), hpar⟩⟩

/-! ### Side-separation facts from the diagonal crossing (for the assembly) -/

/-- Two-term affine combination, recentered at a base point. -/
theorem combo_sub (a b : ℝ) (P Q R : Plane) (h : a + b = 1) :
    a • P + b • Q - R = a • (P - R) + b • (Q - R) := by
  calc a • P + b • Q - R = a • P + b • Q - (a + b) • R := by rw [h]; module
    _ = a • (P - R) + b • (Q - R) := by module

/-- The convex-combination form of strict betweenness. -/
theorem sbtw_combo {x y z : Plane} (h : Sbtw ℝ x y z) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ a + b = 1 ∧ a • x + b • z = y := by
  have hm : y ∈ segment ℝ x z := affineSegment_eq_segment ℝ x z ▸ h.1
  obtain ⟨a, b, ha, hb, hab, hc⟩ := hm
  have ha' : 0 < a := by
    rcases ha.eq_or_lt with h0 | h0
    · exfalso
      simp only [← h0, zero_smul, zero_add] at hc
      have hb1 : b = 1 := by linarith
      rw [hb1, one_smul] at hc
      exact h.2.2 hc.symm
    · exact h0
  have hb' : 0 < b := by
    rcases hb.eq_or_lt with h0 | h0
    · exfalso
      simp only [← h0, zero_smul, add_zero] at hc
      have ha1 : a = 1 := by linarith
      rw [ha1, one_smul] at hc
      exact h.2.1 hc.symm
    · exact h0
  exact ⟨a, b, ha', hb', hab, hc⟩

/-- Cyclic invariance of `ω` over a triangle: the three vertex-functionals agree. -/
theorem ω_triangle (P Q R : Plane) : ω (P - Q) (R - Q) = ω (Q - R) (P - R) := by
  simp only [ω, PiLp.sub_apply]
  ring

/-- `C` is not on line `AB` (else the diagonals could not cross). -/
theorem ConvexQuad.ω_ABC_ne {A B C D : Plane} (h : ConvexQuad A B C D) :
    ω (A - B) (C - B) ≠ 0 := by
  intro h0
  obtain ⟨X, hX₁, hX₂⟩ := h.diagonals
  have hXB : ω (A - B) (X - B) = 0 := by
    have hm : X ∈ segment ℝ A C := affineSegment_eq_segment ℝ A C ▸ hX₁.1
    obtain ⟨a, b, ha, hb, hab, hXc⟩ := hm
    have e : X - B = a • (A - B) + b • (C - B) := by
      rw [← hXc]; exact combo_sub a b A C B hab
    have e2 : ω (A - B) (X - B) = a * ω (A - B) (A - B) + b * ω (A - B) (C - B) := by
      rw [e, ω_add_right, ω_smul_right, ω_smul_right]
    rw [ω_self, h0, mul_zero, mul_zero, add_zero] at e2
    exact e2
  have hm2 : X ∈ segment ℝ B D := affineSegment_eq_segment ℝ B D ▸ hX₂.1
  obtain ⟨c, d, hc, hd, hcd, hXd⟩ := hm2
  have hd0 : d ≠ 0 := by
    intro h0
    rw [h0, zero_smul, add_zero] at hXd
    have hc1 : c = 1 := by linarith
    rw [hc1, one_smul] at hXd
    exact hX₂.2.1 hXd.symm
  have e3 : X - B = d • (D - B) := by
    rw [← hXd, combo_sub c d B D B hcd, sub_self, smul_zero, zero_add]
  have h2 : ω (A - B) (X - B) = d * ω (A - B) (D - B) := by
    rw [e3, ω_smul_right]
  rw [hXB] at h2
  rcases mul_eq_zero.mp h2.symm with h2 | h2
  · exact hd0 h2
  · exact h.ω_ABD_ne h2

/-- `D` is not on line `AC` (else the diagonals could not cross). -/
theorem ConvexQuad.ω_ACD_ne {A B C D : Plane} (h : ConvexQuad A B C D) :
    ω (A - C) (D - C) ≠ 0 := by
  intro h0
  obtain ⟨X, hX₁, hX₂⟩ := h.diagonals
  have hAC : A ≠ C := by
    intro he
    subst he
    have hm : X ∈ segment ℝ A A := affineSegment_eq_segment ℝ A A ▸ hX₁.1
    obtain ⟨a, b, ha, hb, hab, hXc⟩ := hm
    have hXA : X = A := by
      rw [← hXc, ← add_smul, hab, one_smul]
    exact hX₁.2.1 hXA
  obtain ⟨t, ht⟩ := exists_smul_of_ω_eq_zero (sub_ne_zero.mpr hAC) h0
  have hXC : ω (A - C) (X - C) = 0 := by
    have hm : X ∈ segment ℝ A C := affineSegment_eq_segment ℝ A C ▸ hX₁.1
    obtain ⟨a, b, ha, hb, hab, hXc⟩ := hm
    have e : X - C = a • (A - C) := by
      rw [← hXc, combo_sub a b A C C hab, sub_self, smul_zero, add_zero]
    rw [e, ω_smul_right, ω_self, mul_zero]
  have hm2 : X ∈ segment ℝ B D := affineSegment_eq_segment ℝ B D ▸ hX₂.1
  obtain ⟨c, d, hc, hd, hcd, hXd⟩ := hm2
  have hc0 : c ≠ 0 := by
    intro h0'
    rw [h0', zero_smul, zero_add] at hXd
    have hd1 : d = 1 := by linarith
    rw [hd1, one_smul] at hXd
    exact hX₂.2.2 hXd.symm
  have e3 : X - C = c • (B - C) + d • (D - C) := by
    rw [← hXd]; exact combo_sub c d B D C hcd
  have h2 : ω (A - C) (X - C) = c * ω (A - C) (B - C) + d * ω (A - C) (D - C) := by
    rw [e3, ω_add_right, ω_smul_right, ω_smul_right]
  rw [hXC, h0, mul_zero, add_zero] at h2
  rcases mul_eq_zero.mp h2.symm with h2 | h2
  · exact hc0 h2
  · have e4 : ω (B - C) (A - C) = -ω (A - C) (B - C) := by
      simp only [ω, PiLp.sub_apply]; ring
    have h3 : ω (B - C) (D - C) = t * ω (B - C) (A - C) := by rw [ht, ω_smul_right]
    rw [e4, h2, neg_zero, mul_zero] at h3
    exact h.ω_BCD_ne h3

theorem ConvexQuad.opp_side_BD {A B C D : Plane} (h : ConvexQuad A B C D) :
    ω (D - B) (A - B) * ω (D - B) (C - B) < 0 := by
  obtain ⟨X, hX₁, hX₂⟩ := h.diagonals
  obtain ⟨a, b, ha, hb, hab, hXc⟩ := sbtw_combo hX₁
  obtain ⟨c, d, hc, hd, hcd, hXd⟩ := sbtw_combo hX₂
  have eB : X - B = a • (A - B) + b • (C - B) := by
    rw [← hXc]; exact combo_sub a b A C B hab
  have eB' : X - B = d • (D - B) := by
    rw [← hXd, combo_sub c d B D B hcd, sub_self, smul_zero, zero_add]
  have key : a * ω (D - B) (A - B) + b * ω (D - B) (C - B) = 0 := by
    have w1 : ω (D - B) (X - B) = a * ω (D - B) (A - B) + b * ω (D - B) (C - B) := by
      rw [eB, ω_add_right, ω_smul_right, ω_smul_right]
    have w2 : ω (D - B) (X - B) = 0 := by
      rw [eB', ω_smul_right, ω_self, mul_zero]
    rw [w2] at w1
    exact w1.symm
  have hne : ω (D - B) (A - B) ≠ 0 := by
    have e : ω (D - B) (A - B) = -ω (A - B) (D - B) := by
      simp only [ω, PiLp.sub_apply]; ring
    rw [e]
    exact neg_ne_zero.mpr h.ω_ABD_ne
  have h2 : ω (D - B) (C - B) = -(a / b) * ω (D - B) (A - B) := by
    have hb' : b ≠ 0 := hb.ne'
    field_simp [hb']
    linarith [key]
  rw [h2]
  have e3 : ω (D - B) (A - B) * (-(a / b) * ω (D - B) (A - B)) =
      -((a / b) * (ω (D - B) (A - B) * ω (D - B) (A - B))) := by ring
  rw [e3]
  exact neg_neg_of_pos (mul_pos (div_pos ha hb) (mul_self_pos.mpr hne))


theorem dist_eq_of_cospherical_parallel {A K P N : Plane}
    (hcyc : Cospherical ({A, K, P, N} : Set Plane))
    (hpar : ∃ c : ℝ, A - N = c • (P - K)) (hAN : A ≠ N) :
    dist P N = dist K A := by
  obtain ⟨s, hs⟩ := cospherical_iff_exists_sphere.mp hcyc
  obtain ⟨c, hc⟩ := hpar
  have hc0 : c ≠ 0 := by
    intro h0
    apply hAN
    rw [← sub_eq_zero, hc, h0, zero_smul]
  have hKmem : dist s.center K = s.radius := mem_sphere'.mp (Sphere.mem_coe.mp
    (hs (Set.mem_insert_of_mem _ (Set.mem_insert _ _))))
  have hPmem : dist s.center P = s.radius := mem_sphere'.mp (Sphere.mem_coe.mp
    (hs (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))))
  have hAmem : dist s.center A = s.radius := mem_sphere'.mp (Sphere.mem_coe.mp
    (hs (Set.mem_insert _ _)))
  have hNmem : dist s.center N = s.radius := mem_sphere'.mp (Sphere.mem_coe.mp
    (hs (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
      (Set.mem_singleton _))))))
  have hKP : dist s.center K = dist s.center P := by rw [hKmem, hPmem]
  have hANd : dist s.center A = dist s.center N := by rw [hAmem, hNmem]
  set w : Plane := s.center - A with hw
  set u : Plane := K - A with hu
  set v : Plane := P - K with hv
  have hscK : s.center - K = w - u := by rw [hw, hu]; module
  have hNeq : N = A - c • v := by
    rw [show N = A - (A - N) by module, hc]
  have hscP : s.center - P = w - u - v := by rw [hw, hu, hv]; module
  have hscN : s.center - N = w + c • v := by rw [hNeq, hw]; module
  have q2 : ‖w - u‖ ^ 2 = ‖w - u - v‖ ^ 2 := by
    have h2 := congrArg (· ^ 2) hKP
    rwa [dist_eq_norm, dist_eq_norm, hscK, hscP] at h2
  have q3 : ‖w‖ ^ 2 = ‖w + c • v‖ ^ 2 := by
    have h2 := congrArg (· ^ 2) hANd
    rwa [dist_eq_norm, dist_eq_norm, hscN, ← hw] at h2
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq] at q2 q3
  have hPN : P - N = u + (1 + c) • v := by rw [hNeq, hu, hv]; module
  rw [← sq_eq_sq₀ dist_nonneg dist_nonneg, dist_eq_norm, dist_eq_norm, hPN, ← hu,
    ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right] at q2 q3 ⊢
  rw [real_inner_comm w u, real_inner_comm w v, real_inner_comm u v] at q2
  rw [real_inner_comm w v] at q3
  rw [real_inner_comm u v]
  have h5 : c * (2 * ⟪w, v⟫ + c * ⟪v, v⟫) = 0 := by
    linear_combination -q3
  rcases mul_eq_zero.mp h5 with h6 | h6
  · exact absurd h6 hc0
  · have h4 : 2 * ⟪w, v⟫ = -c * ⟪v, v⟫ := by linear_combination h6
    linear_combination (-(1 + c)) * q2 + (1 + c) * h4

/-- `C, D` are strictly on the same side of line `AB`. -/
theorem ConvexQuad.side_sign_AB {A B C D : Plane} (h : ConvexQuad A B C D) :
    0 < ω (B - A) (C - A) * ω (B - A) (D - A) := by
  obtain ⟨X, hX₁, hX₂⟩ := h.diagonals
  obtain ⟨a, b, ha, hb, hab, hXc⟩ := sbtw_combo hX₁
  obtain ⟨c, d, hc, hd, hcd, hXd⟩ := sbtw_combo hX₂
  have eA : X - A = b • (C - A) := by
    rw [← hXc, combo_sub a b A C A hab, sub_self, smul_zero, zero_add]
  have eB : X - B = d • (D - B) := by
    rw [← hXd, combo_sub c d B D B hcd, sub_self, smul_zero, zero_add]
  have key : b * ω (B - A) (C - A) = d * ω (B - A) (D - A) := by
    have w1 : ω (B - A) (X - A) = b * ω (B - A) (C - A) := by
      rw [eA, ω_smul_right]
    have w2 : ω (B - A) (X - A) = d * ω (B - A) (D - A) := by
      have eA' : X - A = d • (D - B) + (B - A) := by
        rw [show X - A = (X - B) + (B - A) by module, eB]
      rw [eA', ω_add_right, ω_smul_right, ω_self, add_zero,
        show D - B = (D - A) + (A - B) by module, ω_add_right,
        show (A - B : Plane) = (-1 : ℝ) • (B - A) by module, ω_smul_right, ω_self,
        mul_zero, add_zero]
    rw [w1] at w2
    exact w2
  have hne : ω (B - A) (D - A) ≠ 0 := by
    have e : ω (B - A) (D - A) = -ω (A - B) (D - B) := by
      simp only [ω, PiLp.sub_apply]; ring
    rw [e]
    exact neg_ne_zero.mpr h.ω_ABD_ne
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have h2 : ω (B - A) (C - A) < 0 := by
      by_contra h0
      push_neg at h0
      have h1 : 0 ≤ b * ω (B - A) (C - A) := mul_nonneg hb.le h0
      rw [key] at h1
      exact not_le.mpr (mul_neg_of_pos_of_neg hd hneg) h1
    exact mul_pos_of_neg_of_neg h2 hneg
  · have h2 : 0 < ω (B - A) (C - A) := by
      by_contra h0
      push_neg at h0
      have h1 : b * ω (B - A) (C - A) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb.le h0
      rw [key] at h1
      exact not_le.mpr (mul_pos hd hpos) h1
    exact mul_pos h2 hpos

/-- `A, D` are strictly on the same side of line `BC`. -/
theorem ConvexQuad.side_sign_BC {A B C D : Plane} (h : ConvexQuad A B C D) :
    0 < ω (C - B) (A - B) * ω (C - B) (D - B) := by
  obtain ⟨X, hX₁, hX₂⟩ := h.diagonals
  obtain ⟨a, b, ha, hb, hab, hXc⟩ := sbtw_combo hX₁
  obtain ⟨c, d, hc, hd, hcd, hXd⟩ := sbtw_combo hX₂
  have eB : X - B = a • (A - B) + b • (C - B) := by
    rw [← hXc]; exact combo_sub a b A C B hab
  have eB' : X - B = d • (D - B) := by
    rw [← hXd, combo_sub c d B D B hcd, sub_self, smul_zero, zero_add]
  have key : a * ω (C - B) (A - B) = d * ω (C - B) (D - B) := by
    have w1 : ω (C - B) (X - B) = a * ω (C - B) (A - B) := by
      rw [eB, ω_add_right, ω_smul_right, ω_smul_right, ω_self, mul_zero, add_zero]
    have w2 : ω (C - B) (X - B) = d * ω (C - B) (D - B) := by
      rw [eB', ω_smul_right]
    rw [w1] at w2
    exact w2
  have hne : ω (C - B) (A - B) ≠ 0 := by
    have e : ω (C - B) (A - B) = -ω (A - B) (C - B) := by
      simp only [ω, PiLp.sub_apply]; ring
    rw [e]
    exact neg_ne_zero.mpr h.ω_ABC_ne
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have h2 : ω (C - B) (D - B) < 0 := by
      by_contra h0
      push_neg at h0
      have h1 : 0 ≤ d * ω (C - B) (D - B) := mul_nonneg hd.le h0
      rw [← key] at h1
      exact not_le.mpr (mul_neg_of_pos_of_neg ha hneg) h1
    exact mul_pos_of_neg_of_neg hneg h2
  · have h2 : 0 < ω (C - B) (D - B) := by
      by_contra h0
      push_neg at h0
      have h1 : d * ω (C - B) (D - B) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hd.le h0
      rw [← key] at h1
      exact not_le.mpr (mul_pos ha hpos) h1
    exact mul_pos hpos h2

/-- `A, B` are strictly on the same side of line `CD`. -/
theorem ConvexQuad.side_sign_CD {A B C D : Plane} (h : ConvexQuad A B C D) :
    0 < ω (D - C) (A - C) * ω (D - C) (B - C) := by
  obtain ⟨X, hX₁, hX₂⟩ := h.diagonals
  obtain ⟨a, b, ha, hb, hab, hXc⟩ := sbtw_combo hX₁
  obtain ⟨c, d, hc, hd, hcd, hXd⟩ := sbtw_combo hX₂
  have eC : X - C = a • (A - C) := by
    rw [← hXc, combo_sub a b A C C hab, sub_self, smul_zero, add_zero]
  have eC' : X - C = d • (D - B) + (B - C) := by
    have e2 : X - B = d • (D - B) := by
      rw [← hXd, combo_sub c d B D B hcd, sub_self, smul_zero, zero_add]
    rw [show X - C = (X - B) + (B - C) by module, e2]
  have key : a * ω (D - C) (A - C) = c * ω (D - C) (B - C) := by
    have w1 : ω (D - C) (X - C) = a * ω (D - C) (A - C) := by
      rw [eC, ω_smul_right]
    have w2 : ω (D - C) (X - C) = c * ω (D - C) (B - C) := by
      rw [eC', ω_add_right, ω_smul_right,
        show D - B = (D - C) + (C - B) by module, ω_add_right, ω_self, zero_add,
        show C - B = (-1 : ℝ) • (B - C) by module, ω_smul_right]
      have hc1 : c = 1 - d := by linarith
      rw [hc1]
      ring
    rw [w1] at w2
    exact w2
  have hne : ω (D - C) (B - C) ≠ 0 := by
    have e : ω (D - C) (B - C) = -ω (B - C) (D - C) := by
      simp only [ω, PiLp.sub_apply]; ring
    rw [e]
    exact neg_ne_zero.mpr h.ω_BCD_ne
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have h2 : ω (D - C) (A - C) < 0 := by
      by_contra h0
      push_neg at h0
      have h1 : 0 ≤ a * ω (D - C) (A - C) := mul_nonneg ha.le h0
      rw [key] at h1
      exact not_le.mpr (mul_neg_of_pos_of_neg hc hneg) h1
    exact mul_pos_of_neg_of_neg h2 hneg
  · have h2 : 0 < ω (D - C) (A - C) := by
      by_contra h0
      push_neg at h0
      have h1 : a * ω (D - C) (A - C) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha.le h0
      rw [key] at h1
      exact not_le.mpr (mul_pos hc hpos) h1
    exact mul_pos h2 hpos

/-- `B, C` are strictly on the same side of line `DA`. -/
theorem ConvexQuad.side_sign_DA {A B C D : Plane} (h : ConvexQuad A B C D) :
    0 < ω (A - D) (B - D) * ω (A - D) (C - D) := by
  obtain ⟨X, hX₁, hX₂⟩ := h.diagonals
  obtain ⟨a, b, ha, hb, hab, hXc⟩ := sbtw_combo hX₁
  obtain ⟨c, d, hc, hd, hcd, hXd⟩ := sbtw_combo hX₂
  have eD : X - D = a • (A - D) + b • (C - D) := by
    rw [← hXc]; exact combo_sub a b A C D hab
  have eD' : X - D = c • (B - D) := by
    rw [← hXd, combo_sub c d B D D hcd, sub_self, smul_zero, add_zero]
  have key : b * ω (A - D) (C - D) = c * ω (A - D) (B - D) := by
    have w1 : ω (A - D) (X - D) = b * ω (A - D) (C - D) := by
      rw [eD, ω_add_right, ω_smul_right, ω_smul_right, ω_self, mul_zero, zero_add]
    have w2 : ω (A - D) (X - D) = c * ω (A - D) (B - D) := by
      rw [eD', ω_smul_right]
    rw [w1] at w2
    exact w2
  have hne : ω (A - D) (B - D) ≠ 0 := by
    have e : ω (A - D) (B - D) = -ω (A - B) (D - B) := by
      simp only [ω, PiLp.sub_apply]; ring
    rw [e]
    exact neg_ne_zero.mpr h.ω_ABD_ne
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have h2 : ω (A - D) (C - D) < 0 := by
      by_contra h0
      push_neg at h0
      have h1 : 0 ≤ b * ω (A - D) (C - D) := mul_nonneg hb.le h0
      rw [key] at h1
      exact not_le.mpr (mul_neg_of_pos_of_neg hc hneg) h1
    exact mul_pos_of_neg_of_neg hneg h2
  · have h2 : 0 < ω (A - D) (C - D) := by
      by_contra h0
      push_neg at h0
      have h1 : b * ω (A - D) (C - D) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb.le h0
      rw [key] at h1
      exact not_le.mpr (mul_pos hc hpos) h1
    exact mul_pos hpos h2

/-! ### Piece convexity via the sphere (four concyclic points are in convex position) -/

/-- If an inner-product functional strictly separates all of `p₁, p₂, p₃` from `x`,
then `x` is not in their convex hull. -/
theorem not_mem_convexHull_of_inner {x p₁ p₂ p₃ w : Plane}
    (hd₁ : 0 < ⟪p₁ - x, w⟫) (hd₂ : 0 < ⟪p₂ - x, w⟫) (hd₃ : 0 < ⟪p₃ - x, w⟫) :
    x ∉ convexHull ℝ ({p₁, p₂, p₃} : Set Plane) := by
  intro hmem
  have hset : ({p₁, p₂, p₃} : Set Plane) = (({p₁, p₂, p₃} : Finset Plane) : Set Plane) := by
    simp
  rw [hset] at hmem
  obtain ⟨wt, hwt0, hwt1, hwt2⟩ := Finset.mem_convexHull'.mp hmem
  have hmem₁ : p₁ ∈ ({p₁, p₂, p₃} : Finset Plane) := Finset.mem_insert_self _ _
  have hmem₂ : p₂ ∈ ({p₁, p₂, p₃} : Finset Plane) :=
    Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hmem₃ : p₃ ∈ ({p₁, p₂, p₃} : Finset Plane) :=
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hsub : ∑ y ∈ ({p₁, p₂, p₃} : Finset Plane), wt y • (y - x) = 0 := by
    have hcongr : ∀ y ∈ ({p₁, p₂, p₃} : Finset Plane), wt y • (y - x) = wt y • y - wt y • x :=
      fun y _ ↦ smul_sub (wt y) y x
    rw [Finset.sum_congr rfl hcongr, Finset.sum_sub_distrib, hwt2, ← Finset.sum_smul, hwt1,
      one_smul, sub_self]
  have hsum : ∑ y ∈ ({p₁, p₂, p₃} : Finset Plane), wt y * ⟪y - x, w⟫ = 0 := by
    have hcalc : ∑ y ∈ ({p₁, p₂, p₃} : Finset Plane), wt y * ⟪y - x, w⟫ =
        ⟪∑ y ∈ ({p₁, p₂, p₃} : Finset Plane), wt y • (y - x), w⟫ := by
      rw [sum_inner]
      exact Finset.sum_congr rfl fun y _ ↦ (real_inner_smul_left (y - x) w (wt y)).symm
    rw [hcalc, hsub, inner_zero_left]
  obtain ⟨j, hjmem, hjw⟩ : ∃ j ∈ ({p₁, p₂, p₃} : Finset Plane), 0 < wt j := by
    by_contra h
    push_neg at h
    have hzero : ∑ y ∈ ({p₁, p₂, p₃} : Finset Plane), wt y = 0 :=
      Finset.sum_eq_zero fun y hy ↦ le_antisymm (h y hy) (hwt0 y hy)
    linarith [hwt1]
  have hdj : 0 < ⟪j - x, w⟫ := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hjmem
    rcases hjmem with rfl | rfl | rfl
    · exact hd₁
    · exact hd₂
    · exact hd₃
  have hpos : 0 < ∑ y ∈ ({p₁, p₂, p₃} : Finset Plane), wt y * ⟪y - x, w⟫ :=
    Finset.sum_pos' (fun y hy ↦ by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl
      · exact mul_nonneg (hwt0 _ hmem₁) hd₁.le
      · exact mul_nonneg (hwt0 _ hmem₂) hd₂.le
      · exact mul_nonneg (hwt0 _ hmem₃) hd₃.le) ⟨j, hjmem, mul_pos hjw hdj⟩
  linarith [hsum, hpos]

/-- `⟪x - c, x - c⟫ = dist x c ^ 2`. -/
theorem inner_self_eq_dist_sq (x c : Plane) : ⟪x - c, x - c⟫ = dist x c ^ 2 := by
  rw [dist_eq_norm_vsub, vsub_eq_sub, real_inner_self_eq_norm_sq]

/-- Polarization: the inner product of two shifted vectors in terms of distances. -/
theorem inner_sub_sub_eq (x y c : Plane) :
    ⟪x - c, y - c⟫ = (dist x c ^ 2 + dist y c ^ 2 - dist x y ^ 2) / 2 := by
  have h1 : dist x y ^ 2 = ⟪x - c, x - c⟫ + ⟪y - c, y - c⟫ - 2 * ⟪x - c, y - c⟫ := by
    rw [dist_eq_norm_vsub, vsub_eq_sub, show x - y = (x - c) - (y - c) by module,
      ← real_inner_self_eq_norm_sq]
    rw [inner_sub_left (x - c) (y - c) ((x - c) - (y - c)),
      inner_sub_right (x - c) (x - c) (y - c),
      inner_sub_right (y - c) (x - c) (y - c),
      real_inner_comm (y - c) (x - c)]
    ring
  linarith [h1, inner_self_eq_dist_sq x c, inner_self_eq_dist_sq y c]

/-- A point of a sphere is not in the convex hull of three other points of the sphere. -/
theorem not_mem_convexHull_of_mem_sphere {s : Sphere Plane} {V T₁ T₂ T₃ : Plane}
    (hV : V ∈ s) (hT₁ : T₁ ∈ s) (hT₂ : T₂ ∈ s) (hT₃ : T₃ ∈ s)
    (h₁ : T₁ ≠ V) (h₂ : T₂ ≠ V) (h₃ : T₃ ≠ V) :
    V ∉ convexHull ℝ ({T₁, T₂, T₃} : Set Plane) := by
  have dV : dist V s.center = s.radius := mem_sphere.mp hV
  have dT₁ : dist T₁ s.center = s.radius := mem_sphere.mp hT₁
  have dT₂ : dist T₂ s.center = s.radius := mem_sphere.mp hT₂
  have dT₃ : dist T₃ s.center = s.radius := mem_sphere.mp hT₃
  have key : ∀ T : Plane, dist T s.center = s.radius → T ≠ V →
      0 < ⟪T - V, s.center - V⟫ := by
    intro T dT hTV
    have h1 : ⟪T - V, s.center - V⟫ =
        ⟪V - s.center, V - s.center⟫ - ⟪T - s.center, V - s.center⟫ := by
      rw [show T - V = (T - s.center) - (V - s.center) by module,
        show s.center - V = -(V - s.center) by module,
        inner_sub_left, inner_neg_right, inner_neg_right]
      ring
    rw [h1, inner_self_eq_dist_sq V s.center, inner_sub_sub_eq T V s.center, dV, dT]
    have h2 : 0 < dist T V ^ 2 := pow_pos (dist_pos.mpr hTV) 2
    nlinarith
  exact not_mem_convexHull_of_inner (key T₁ dT₁ h₁) (key T₂ dT₂ h₂) (key T₃ dT₃ h₃)

/-- The diagonals of four cospherical points cross: if `S₁, S₂` are strictly on opposite
sides of the line `VP` (measured by `ω`), then the segments `S₁S₂` and `VP` meet strictly
inside. -/
theorem sbtw_diag_of_cospherical_sides {s : Sphere Plane} {V P S₁ S₂ : Plane}
    (hV : V ∈ s) (hP : P ∈ s) (hS₁ : S₁ ∈ s) (hS₂ : S₂ ∈ s) (hVP : V ≠ P)
    (hsep : ω (P - V) (S₁ - V) * ω (P - V) (S₂ - V) < 0) :
    ∃ Q : Plane, Sbtw ℝ S₁ Q S₂ ∧ Sbtw ℝ V Q P := by
  have dV : dist V s.center = s.radius := mem_sphere.mp hV
  have dP : dist P s.center = s.radius := mem_sphere.mp hP
  have dS₁ : dist S₁ s.center = s.radius := mem_sphere.mp hS₁
  have dS₂ : dist S₂ s.center = s.radius := mem_sphere.mp hS₂
  set u : ℝ := ω (P - V) (S₁ - V) with hu
  set v : ℝ := ω (P - V) (S₂ - V) with hv
  have hune : u ≠ 0 := fun h0 ↦ by rw [h0, zero_mul] at hsep; exact lt_irrefl 0 hsep
  have hvne : v ≠ 0 := fun h0 ↦ by rw [h0, mul_zero] at hsep; exact lt_irrefl 0 hsep
  have hS₁S₂ : S₁ ≠ S₂ := by
    intro h0
    rw [h0] at hu
    have huv : u = v := hu.trans hv.symm
    rw [huv] at hsep
    exact not_lt.mpr (mul_self_nonneg v) hsep
  have hsign : 0 < u * (u - v) := by
    have e : u * (u - v) = u * u - u * v := by ring
    rw [e]
    have h1 : 0 < u * u := mul_self_pos.mpr hune
    linarith [hsep]
  have huv2 : u - v ≠ 0 := fun h0 ↦ by rw [h0, mul_zero] at hsign; exact lt_irrefl 0 hsign
  set t : ℝ := u / (u - v) with ht
  have ht01 : 0 < t ∧ t < 1 := by
    rcases lt_or_gt_of_ne hune with hn | hp
    · have hvp : 0 < v := by
        by_contra h0
        push_neg at h0
        have h2 : 0 ≤ u * v := mul_nonneg_of_nonpos_of_nonpos hn.le h0
        linarith
      have h1 : u - v < 0 := by
        rcases lt_or_gt_of_ne huv2 with hh | hh
        · exact hh
        · exfalso
          have h2 : u * (u - v) < 0 := mul_neg_of_neg_of_pos hn hh
          linarith
      refine ⟨div_pos_of_neg_of_neg hn h1, ?_⟩
      rw [div_lt_one_of_neg h1]
      linarith [hvp]
    · have hvn : v < 0 := by
        by_contra h0
        push_neg at h0
        have h2 : 0 ≤ u * v := mul_nonneg hp.le h0
        linarith
      have h1 : 0 < u - v := by
        rcases lt_or_gt_of_ne huv2 with hh | hh
        · exfalso
          have h2 : u * (u - v) < 0 := mul_neg_of_pos_of_neg hp hh
          linarith
        · exact hh
      refine ⟨div_pos hp h1, ?_⟩
      rw [div_lt_one h1]
      linarith [hvn]
  set Q : Plane := AffineMap.lineMap S₁ S₂ t with hQ
  have hQline : ω (P - V) (Q - V) = 0 := by
    have e : Q - V = (1 - t) • (S₁ - V) + t • (S₂ - V) := by
      rw [hQ, AffineMap.lineMap_apply_module]
      module
    rw [e, ω_add_right, ω_smul_right, ω_smul_right, ← hu, ← hv, ht]
    field_simp [huv2]
    ring
  -- `Q` is strictly inside the sphere's ball
  have hQball : dist Q s.center ^ 2 < s.radius ^ 2 := by
    have e : Q - s.center = (1 - t) • (S₁ - s.center) + t • (S₂ - s.center) := by
      rw [hQ, AffineMap.lineMap_apply_module]
      module
    have hdist : dist Q s.center ^ 2 = (1 - t) * dist S₁ s.center ^ 2 +
        t * dist S₂ s.center ^ 2 - t * (1 - t) * dist S₁ S₂ ^ 2 := by
      rw [dist_eq_norm_vsub, vsub_eq_sub, e, ← real_inner_self_eq_norm_sq,
        inner_add_left ((1 - t) • (S₁ - s.center)) (t • (S₂ - s.center)),
        real_inner_smul_left, real_inner_smul_left,
        inner_add_right (S₁ - s.center), real_inner_smul_right, real_inner_smul_right,
        inner_add_right (S₂ - s.center), real_inner_smul_right, real_inner_smul_right]
      have hp1 : ⟪S₁ - s.center, S₁ - s.center⟫ = s.radius ^ 2 := by
        rw [inner_self_eq_dist_sq, dS₁]
      have hp2 : ⟪S₂ - s.center, S₂ - s.center⟫ = s.radius ^ 2 := by
        rw [inner_self_eq_dist_sq, dS₂]
      have hp3 : ⟪S₂ - s.center, S₁ - s.center⟫ =
          (dist S₂ s.center ^ 2 + dist S₁ s.center ^ 2 - dist S₂ S₁ ^ 2) / 2 :=
        inner_sub_sub_eq S₂ S₁ s.center
      rw [real_inner_comm (S₂ - s.center) (S₁ - s.center), hp1, hp2, hp3, dS₁, dS₂,
        dist_comm S₂ S₁]
      ring
    rw [hdist, dS₁, dS₂]
    have h1 : 0 < t * (1 - t) * dist S₁ S₂ ^ 2 :=
      mul_pos (mul_pos ht01.1 (sub_pos.mpr ht01.2)) (pow_pos (dist_pos.mpr hS₁S₂) 2)
    nlinarith
  -- hence `Q` is on the open chord `VP`
  have hVPv : P - V ≠ 0 := sub_ne_zero.mpr hVP.symm
  obtain ⟨q, hq⟩ := exists_smul_of_ω_eq_zero hVPv hQline
  have hq01 : 0 < q ∧ q < 1 := by
    have hdistQ : dist Q s.center ^ 2 = s.radius ^ 2 - q * (1 - q) * dist V P ^ 2 := by
      have e : Q - s.center = (V - s.center) + q • (P - V) := by
        rw [show Q - s.center = (Q - V) + (V - s.center) by module, hq, add_comm]
      rw [dist_eq_norm_vsub, vsub_eq_sub, e, ← real_inner_self_eq_norm_sq,
        inner_add_left (V - s.center) (q • (P - V)),
        real_inner_smul_left, inner_add_right (V - s.center), real_inner_smul_right,
        inner_add_right (P - V), real_inner_smul_right]
      have hp1 : ⟪V - s.center, V - s.center⟫ = s.radius ^ 2 := by
        rw [inner_self_eq_dist_sq, dV]
      have hp2 : ⟪P - V, P - V⟫ = dist V P ^ 2 := by
        rw [show P - V = -(V - P) by module, inner_neg_left, inner_neg_right, neg_neg,
          inner_self_eq_dist_sq]
      have hp3 : ⟪V - s.center, P - V⟫ = -dist V P ^ 2 / 2 := by
        have h3 := inner_sub_sub_eq P V s.center
        rw [dP, dV] at h3
        have e3 : (P - V : Plane) = (P - s.center) - (V - s.center) := by module
        rw [e3, inner_sub_right (V - s.center) (P - s.center) (V - s.center),
          inner_self_eq_dist_sq V s.center, dV,
          ← real_inner_comm (V - s.center) (P - s.center), h3, dist_comm P V]
        ring
      rw [real_inner_comm (V - s.center) (P - V), hp1, hp2, hp3]
      ring
    rw [hdistQ] at hQball
    have hdVP : 0 < dist V P ^ 2 := pow_pos (dist_pos.mpr hVP) 2
    have hpos : 0 < q * (1 - q) := by
      by_contra h0
      push_neg at h0
      have h1 : q * (1 - q) * dist V P ^ 2 ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg h0 hdVP.le
      linarith
    refine ⟨?_, ?_⟩
    · by_contra h0
      push_neg at h0
      have h1 : q * (1 - q) ≤ 0 := by
        have h2 : (0:ℝ) ≤ 1 - q := by linarith
        nlinarith [mul_nonpos_of_nonpos_of_nonneg h0 h2]
      linarith
    · by_contra h0
      push_neg at h0
      have h1 : q * (1 - q) ≤ 0 := by
        have h2 : (0:ℝ) ≤ q := by linarith
        have h3 : 1 - q ≤ 0 := by linarith
        nlinarith [mul_nonpos_of_nonneg_of_nonpos h2 h3]
      linarith
  exact ⟨Q, sbtw_lineMap hS₁S₂ ht01.1 ht01.2, by
    have hQV : Q = AffineMap.lineMap V P q := by
      have e : Q = q • (P - V) + V := by rw [← hq]; module
      rw [e, AffineMap.lineMap_apply_module]
      module
    rw [hQV]
    exact sbtw_lineMap hVP hq01.1 hq01.2⟩

/-- Four cospherical points `V, S₁, P, S₂` with `S₁, S₂` strictly on opposite sides of
the line `VP` form a strictly convex quadrilateral in the boundary order `V, S₁, P, S₂`. -/
theorem convexQuad_of_cospherical_sides {V S₁ S₂ P : Plane}
    (hcyc : Cospherical ({V, S₁, P, S₂} : Set Plane))
    (hVP : V ≠ P) (hVS₁ : V ≠ S₁) (hVS₂ : V ≠ S₂)
    (hS₁S₂ : S₁ ≠ S₂) (hS₁P : S₁ ≠ P) (hS₂P : S₂ ≠ P)
    (hsep : ω (P - V) (S₁ - V) * ω (P - V) (S₂ - V) < 0) :
    ConvexQuad V S₁ P S₂ := by
  obtain ⟨s, hs⟩ := cospherical_iff_exists_sphere.mp hcyc
  simp only [Set.insert_subset_iff, Set.singleton_subset_iff, Sphere.mem_coe] at hs
  obtain ⟨hV, hS₁, hP, hS₂⟩ := hs
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact not_mem_convexHull_of_mem_sphere hV hS₁ hP hS₂ hVS₁.symm hVP.symm hVS₂.symm
  · exact not_mem_convexHull_of_mem_sphere hS₁ hP hS₂ hV hS₁P.symm hS₁S₂.symm hVS₁
  · exact not_mem_convexHull_of_mem_sphere hP hS₂ hV hS₁ hS₂P hVP hS₁P
  · exact not_mem_convexHull_of_mem_sphere hS₂ hV hS₁ hP hVS₂ hS₁S₂ hS₂P.symm
  · obtain ⟨Q, hQ1, hQ2⟩ := sbtw_diag_of_cospherical_sides hV hP hS₁ hS₂ hVP hsep
    exact ⟨Q, hQ2, hQ1⟩
/-- The A-piece `A K P N` of the kalva construction is strictly convex. -/
theorem convexQuad_A_piece {A B C D : Plane} (h : ConvexQuad A B C D) {s tN : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) (htN0 : 0 < tN) (htN1 : tN < 1)
    {K P N : Plane}
    (hK : K = AffineMap.lineMap A B s) (hP : P = AffineMap.lineMap B D (1 - s))
    (hN : N = AffineMap.lineMap D A tN)
    (hcyc : Cospherical ({A, K, P, N} : Set Plane)) :
    ConvexQuad A K P N := by
  have hs1' : (0 : ℝ) < 1 - s := sub_pos.mpr hs1
  have htN1' : (0 : ℝ) < 1 - tN := sub_pos.mpr htN1
  -- vector forms
  have vK : K - A = s • (B - A) := by rw [hK, AffineMap.lineMap_apply_module]; module
  have vN : N - A = (1 - tN) • (D - A) := by rw [hN, AffineMap.lineMap_apply_module]; module
  have vP : P - A = s • (B - A) + (1 - s) • (D - A) := by
    rw [hP, AffineMap.lineMap_apply_module]; module
  have hω : ω (D - A) (B - A) ≠ 0 := by
    have e : ω (D - A) (B - A) = ω (A - B) (D - B) := by
      simp only [ω, PiLp.sub_apply]; ring
    rw [e]; exact h.ω_ABD_ne
  have wK : ω (P - A) (K - A) = (s * (1 - s)) * ω (D - A) (B - A) := by
    rw [vP, vK]
    simp only [ω_add_left, ω_smul_left, ω_smul_right, ω_self, mul_zero, zero_add, add_zero]
    ring
  have wN : ω (P - A) (N - A) = -(s * (1 - tN) * ω (D - A) (B - A)) := by
    rw [vP, vN]
    simp only [ω_add_left, ω_smul_left, ω_smul_right, ω_self, mul_zero, zero_add, add_zero]
    have e : ω (B - A) (D - A) = -ω (D - A) (B - A) := by
      simp only [ω, PiLp.sub_apply]; ring
    rw [e]
    ring
  have hwK : ω (P - A) (K - A) ≠ 0 := by
    rw [wK]; exact mul_ne_zero (mul_ne_zero hs0.ne' hs1'.ne') hω
  have hwN : ω (P - A) (N - A) ≠ 0 := by
    rw [wN]; exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero hs0.ne' htN1'.ne') hω)
  refine convexQuad_of_cospherical_sides hcyc ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro he; rw [he, sub_self, ω_zero_left] at hwK; exact hwK rfl
  · intro he; rw [he, sub_self, ω_zero_right] at hwK; exact hwK rfl
  · intro he; rw [he, sub_self, ω_zero_right] at hwN; exact hwN rfl
  · -- `K ≠ N`: their direction vectors from `A` are independent
    intro he
    have h1 : K - A = N - A := by rw [he]
    rw [vK, vN] at h1
    have h2 := congrArg (fun x : Plane ↦ ω x (D - A)) h1
    simp only [ω_smul_left, ω_self, mul_zero] at h2
    have e : ω (B - A) (D - A) = -ω (D - A) (B - A) := by
      simp only [ω, PiLp.sub_apply]; ring
    rw [e, mul_neg, neg_eq_zero] at h2
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact hs0.ne' h3
    · exact hω h3
  · intro he; rw [he] at hwK; exact hwK (ω_self _)
  · intro he; rw [he] at hwN; exact hwN (ω_self _)
  · rw [wK, wN]
    have e : (s * (1 - s)) * ω (D - A) (B - A) * (-(s * (1 - tN) * ω (D - A) (B - A))) =
        -((s * (1 - s)) * (s * (1 - tN)) *
          (ω (D - A) (B - A) * ω (D - A) (B - A))) := by ring
    rw [e]
    exact neg_neg_of_pos (mul_pos (mul_pos (mul_pos hs0 hs1') (mul_pos hs0 htN1'))
      (mul_self_pos.mpr hω))

/-- The B-piece `B K P L` of the kalva construction is strictly convex. -/
theorem convexQuad_B_piece {A B C D : Plane} (h : ConvexQuad A B C D) {s : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) {K P L : Plane}
    (hK : K = AffineMap.lineMap A B s) (hP : P = AffineMap.lineMap B D (1 - s))
    (hL : L = AffineMap.lineMap B C (1 - s))
    (hcyc : Cospherical ({B, K, L, P} : Set Plane)) :
    ConvexQuad B K P L := by
  have hcyc : Cospherical ({B, K, P, L} : Set Plane) := by
    rw [show ({B, K, P, L} : Set Plane) = {B, K, L, P} by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]
    exact hcyc
  have hs1' : (0 : ℝ) < 1 - s := sub_pos.mpr hs1
  -- vector forms
  have vK : K - B = (1 - s) • (A - B) := by rw [hK, AffineMap.lineMap_apply_module]; module
  have vL : L - B = (1 - s) • (C - B) := by rw [hL, AffineMap.lineMap_apply_module]; module
  have vP : P - B = (1 - s) • (D - B) := by rw [hP, AffineMap.lineMap_apply_module]; module
  have hω1 : ω (D - B) (A - B) ≠ 0 := by
    have e : ω (D - B) (A - B) = -ω (A - B) (D - B) := by
      simp only [ω, PiLp.sub_apply]; ring
    rw [e]; exact neg_ne_zero.mpr h.ω_ABD_ne
  have hω2 : ω (D - B) (C - B) ≠ 0 := by
    have e : ω (D - B) (C - B) = ω (B - C) (D - C) := by
      simp only [ω, PiLp.sub_apply]; ring
    rw [e]; exact h.ω_BCD_ne
  have hω3 : ω (A - B) (C - B) ≠ 0 := h.ω_ABC_ne
  have wK : ω (P - B) (K - B) = ((1 - s) * (1 - s)) * ω (D - B) (A - B) := by
    rw [vP, vK, ω_smul_left, ω_smul_right]
    ring
  have wL : ω (P - B) (L - B) = ((1 - s) * (1 - s)) * ω (D - B) (C - B) := by
    rw [vP, vL, ω_smul_left, ω_smul_right]
    ring
  have wKL : ω (K - B) (L - B) = ((1 - s) * (1 - s)) * ω (A - B) (C - B) := by
    rw [vK, vL, ω_smul_left, ω_smul_right]
    ring
  have hwK : ω (P - B) (K - B) ≠ 0 := by
    rw [wK]; exact mul_ne_zero (mul_ne_zero hs1'.ne' hs1'.ne') hω1
  have hwL : ω (P - B) (L - B) ≠ 0 := by
    rw [wL]; exact mul_ne_zero (mul_ne_zero hs1'.ne' hs1'.ne') hω2
  have hwKL : ω (K - B) (L - B) ≠ 0 := by
    rw [wKL]; exact mul_ne_zero (mul_ne_zero hs1'.ne' hs1'.ne') hω3
  refine convexQuad_of_cospherical_sides hcyc ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro he; rw [he, sub_self, ω_zero_left] at hwK; exact hwK rfl
  · intro he; rw [he, sub_self, ω_zero_right] at hwK; exact hwK rfl
  · intro he; rw [he, sub_self, ω_zero_right] at hwL; exact hwL rfl
  · intro he; rw [he] at hwKL; exact hwKL (ω_self _)
  · intro he; rw [he] at hwK; exact hwK (ω_self _)
  · intro he; rw [he] at hwL; exact hwL (ω_self _)
  · rw [wK, wL]
    have e : ((1 - s) * (1 - s)) * ω (D - B) (A - B) * (((1 - s) * (1 - s)) *
        ω (D - B) (C - B)) =
        ((1 - s) * (1 - s)) * ((1 - s) * (1 - s)) *
          (ω (D - B) (A - B) * ω (D - B) (C - B)) := by ring
    rw [e]
    exact mul_neg_of_pos_of_neg (mul_pos (mul_pos hs1' hs1') (mul_pos hs1' hs1'))
      h.opp_side_BD

/-- The C-piece `C L P M` of the kalva construction is strictly convex. -/
theorem convexQuad_C_piece {A B C D : Plane} (h : ConvexQuad A B C D) {s tM : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) (htM0 : 0 < tM) (htM1 : tM < 1)
    {L P M : Plane}
    (hL : L = AffineMap.lineMap B C (1 - s))
    (hP : P = AffineMap.lineMap B D (1 - s))
    (hM : M = AffineMap.lineMap C D tM)
    (hcyc : Cospherical ({C, L, M, P} : Set Plane)) :
    ConvexQuad C L P M := by
  have hcyc : Cospherical ({C, L, P, M} : Set Plane) := by
    rw [show ({C, L, P, M} : Set Plane) = {C, L, M, P} by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]
    exact hcyc
  have hs1' : (0 : ℝ) < 1 - s := sub_pos.mpr hs1
  -- vector forms
  have vL : L - C = s • (B - C) := by rw [hL, AffineMap.lineMap_apply_module]; module
  have vM : M - C = tM • (D - C) := by rw [hM, AffineMap.lineMap_apply_module]; module
  have vP : P - C = s • (B - C) + (1 - s) • (D - C) := by
    rw [hP, AffineMap.lineMap_apply_module]; module
  have hω : ω (D - C) (B - C) ≠ 0 := by
    have e : ω (D - C) (B - C) = -ω (B - C) (D - C) := by
      simp only [ω, PiLp.sub_apply]; ring
    rw [e]; exact neg_ne_zero.mpr h.ω_BCD_ne
  have wL : ω (P - C) (L - C) = (s * (1 - s)) * ω (D - C) (B - C) := by
    rw [vP, vL]
    simp only [ω_add_left, ω_smul_left, ω_smul_right, ω_self, mul_zero, zero_add, add_zero]
    ring
  have wM : ω (P - C) (M - C) = -(s * tM * ω (D - C) (B - C)) := by
    rw [vP, vM]
    simp only [ω_add_left, ω_smul_left, ω_smul_right, ω_self, mul_zero, zero_add, add_zero]
    have e : ω (B - C) (D - C) = -ω (D - C) (B - C) := by
      simp only [ω, PiLp.sub_apply]; ring
    rw [e]
    ring
  have wLM : ω (L - C) (M - C) = (s * tM) * ω (B - C) (D - C) := by
    rw [vL, vM, ω_smul_left, ω_smul_right]
    ring
  have hwL : ω (P - C) (L - C) ≠ 0 := by
    rw [wL]; exact mul_ne_zero (mul_ne_zero hs0.ne' hs1'.ne') hω
  have hwM : ω (P - C) (M - C) ≠ 0 := by
    rw [wM]; exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero hs0.ne' htM0.ne') hω)
  have hwLM : ω (L - C) (M - C) ≠ 0 := by
    rw [wLM]; exact mul_ne_zero (mul_ne_zero hs0.ne' htM0.ne') h.ω_BCD_ne
  refine convexQuad_of_cospherical_sides hcyc ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro he; rw [he, sub_self, ω_zero_left] at hwL; exact hwL rfl
  · intro he; rw [he, sub_self, ω_zero_right] at hwL; exact hwL rfl
  · intro he; rw [he, sub_self, ω_zero_right] at hwM; exact hwM rfl
  · intro he; rw [he] at hwLM; exact hwLM (ω_self _)
  · intro he; rw [he] at hwL; exact hwL (ω_self _)
  · intro he; rw [he] at hwM; exact hwM (ω_self _)
  · rw [wL, wM]
    have e : (s * (1 - s)) * ω (D - C) (B - C) * (-(s * tM * ω (D - C) (B - C))) =
        -((s * (1 - s)) * (s * tM) * (ω (D - C) (B - C) * ω (D - C) (B - C))) := by ring
    rw [e]
    exact neg_neg_of_pos (mul_pos (mul_pos (mul_pos hs0 hs1') (mul_pos hs0 htM0))
      (mul_self_pos.mpr hω))

/-- The D-piece `D N P M` of the kalva construction is strictly convex. -/
theorem convexQuad_D_piece {A B C D : Plane} (h : ConvexQuad A B C D) {s tN tM : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) (htN0 : 0 < tN) (htN1 : tN < 1)
    (htM0 : 0 < tM) (htM1 : tM < 1)
    {N P M : Plane}
    (hN : N = AffineMap.lineMap D A tN)
    (hP : P = AffineMap.lineMap B D (1 - s))
    (hM : M = AffineMap.lineMap C D tM)
    (hcyc : Cospherical ({D, M, N, P} : Set Plane)) :
    ConvexQuad D N P M := by
  have hcyc : Cospherical ({D, N, P, M} : Set Plane) := by
    rw [show ({D, N, P, M} : Set Plane) = {D, M, N, P} by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]
    exact hcyc
  have hs1' : (0 : ℝ) < 1 - s := sub_pos.mpr hs1
  have h1tM : (0 : ℝ) < 1 - tM := sub_pos.mpr htM1
  -- vector forms
  have vN : N - D = tN • (A - D) := by rw [hN, AffineMap.lineMap_apply_module]; module
  have vM : M - D = (1 - tM) • (C - D) := by rw [hM, AffineMap.lineMap_apply_module]; module
  have vP : P - D = s • (B - D) := by rw [hP, AffineMap.lineMap_apply_module]; module
  have hω1 : ω (B - D) (A - D) ≠ 0 := by
    have e : ω (B - D) (A - D) = ω (A - B) (D - B) := by
      simp only [ω, PiLp.sub_apply]; ring
    rw [e]; exact h.ω_ABD_ne
  have hω2 : ω (B - D) (C - D) ≠ 0 := by
    have e : ω (B - D) (C - D) = -ω (B - C) (D - C) := by
      simp only [ω, PiLp.sub_apply]; ring
    rw [e]; exact neg_ne_zero.mpr h.ω_BCD_ne
  have hω3 : ω (A - D) (C - D) ≠ 0 := by
    have e : ω (A - D) (C - D) = -ω (A - C) (D - C) := by
      simp only [ω, PiLp.sub_apply]; ring
    rw [e]; exact neg_ne_zero.mpr h.ω_ACD_ne
  have wN : ω (P - D) (N - D) = (s * tN) * ω (B - D) (A - D) := by
    rw [vP, vN, ω_smul_left, ω_smul_right]
    ring
  have wM : ω (P - D) (M - D) = (s * (1 - tM)) * ω (B - D) (C - D) := by
    rw [vP, vM, ω_smul_left, ω_smul_right]
    ring
  have wNM : ω (N - D) (M - D) = (tN * (1 - tM)) * ω (A - D) (C - D) := by
    rw [vN, vM, ω_smul_left, ω_smul_right]
    ring
  have hwN : ω (P - D) (N - D) ≠ 0 := by
    rw [wN]; exact mul_ne_zero (mul_ne_zero hs0.ne' htN0.ne') hω1
  have hwM : ω (P - D) (M - D) ≠ 0 := by
    rw [wM]; exact mul_ne_zero (mul_ne_zero hs0.ne' h1tM.ne') hω2
  have hwNM : ω (N - D) (M - D) ≠ 0 := by
    rw [wNM]; exact mul_ne_zero (mul_ne_zero htN0.ne' h1tM.ne') hω3
  refine convexQuad_of_cospherical_sides hcyc ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro he; rw [he, sub_self, ω_zero_left] at hwN; exact hwN rfl
  · intro he; rw [he, sub_self, ω_zero_right] at hwN; exact hwN rfl
  · intro he; rw [he, sub_self, ω_zero_right] at hwM; exact hwM rfl
  · intro he; rw [he] at hwNM; exact hwNM (ω_self _)
  · intro he; rw [he] at hwN; exact hwN (ω_self _)
  · intro he; rw [he] at hwM; exact hwM (ω_self _)
  · rw [wN, wM]
    have e1 : ω (B - D) (A - D) = -ω (D - B) (A - B) := by
      simp only [ω, PiLp.sub_apply]; ring
    have e2 : ω (B - D) (C - D) = -ω (D - B) (C - B) := by
      simp only [ω, PiLp.sub_apply]; ring
    rw [e1, e2]
    have e3 : (s * tN) * (-ω (D - B) (A - B)) * ((s * (1 - tM)) * (-ω (D - B) (C - B))) =
        (s * tN) * (s * (1 - tM)) * (ω (D - B) (A - B) * ω (D - B) (C - B)) := by ring
    rw [e3]
    exact mul_neg_of_pos_of_neg (mul_pos (mul_pos hs0 htN0) (mul_pos hs0 h1tM))
      h.opp_side_BD


/-! ### The anchor disjunction -/

/-- The triangle `A B C` formed by three consecutive vertices of a convex quadrilateral
is nondegenerate. -/
theorem ConvexQuad.not_collinear_ABC {A B C D : Plane} (h : ConvexQuad A B C D) :
    ¬Collinear ℝ ({A, B, C} : Set Plane) := by
  intro hcol
  obtain ⟨X, hX₁, hX₂⟩ := h.diagonals
  have h0 : ω (B - A) (C - A) = 0 := ω_eq_zero_of_collinear hcol
  have hseg₁ : X ∈ AffineMap.lineMap A C '' Set.Icc (0 : ℝ) 1 := hX₁.1
  obtain ⟨t, -, htX⟩ := hseg₁
  have hseg₂ : X ∈ AffineMap.lineMap B D '' Set.Icc (0 : ℝ) 1 := hX₂.1
  obtain ⟨u, ⟨hu0, -⟩, huX⟩ := hseg₂
  have hun0 : u ≠ 0 := fun hue ↦ hX₂.2.1 (by
    rw [← huX, hue, AffineMap.lineMap_apply_zero])
  have hu0' : 0 < u := hu0.lt_of_ne hun0.symm
  have hXA : X - A = t • (C - A) := by
    rw [← htX, AffineMap.lineMap_apply_module]; module
  have hXB : X - B = u • (D - B) := by
    rw [← huX, AffineMap.lineMap_apply_module]; module
  have hXB' : X - B = t • (C - A) - (B - A) := by
    rw [show X - B = (X - A) - (B - A) by abel, hXA]
  have e1 : ω (B - A) (X - B) = 0 := by
    rw [hXB', ω_sub_right, ω_smul_right, h0, ω_self]; ring
  have e2 : ω (B - A) (X - B) = u * ω (B - A) (D - B) := by
    rw [hXB, ω_smul_right]
  have e3 : ω (B - A) (D - B) = 0 := by
    have h3 : u * ω (B - A) (D - B) = 0 := by rw [← e2, e1]
    rcases mul_eq_zero.mp h3 with hu | hω
    · exact absurd hu hu0'.ne'
    · exact hω
  have e4 : ω (A - B) (D - B) = 0 := by
    have ee : ω (A - B) (D - B) = -ω (B - A) (D - B) := by
      simp only [ω, PiLp.sub_apply]; ring
    rw [e3, neg_zero] at ee
    exact ee
  exact h.ω_ABD_ne e4

/-- The triangle `A C D` formed by three vertices of a convex quadrilateral is
nondegenerate. -/
theorem ConvexQuad.not_collinear_ACD {A B C D : Plane} (h : ConvexQuad A B C D) :
    ¬Collinear ℝ ({A, C, D} : Set Plane) := by
  intro hcol
  obtain ⟨X, hX₁, hX₂⟩ := h.diagonals
  have h0 : ω (C - A) (D - A) = 0 := ω_eq_zero_of_collinear hcol
  obtain ⟨μ, hμ⟩ := exists_smul_of_ω_eq_zero (sub_ne_zero.mpr hX₁.left_ne_right.symm) h0
  have hseg₁ : X ∈ AffineMap.lineMap A C '' Set.Icc (0 : ℝ) 1 := hX₁.1
  obtain ⟨t, -, htX⟩ := hseg₁
  have hseg₂ : X ∈ AffineMap.lineMap B D '' Set.Icc (0 : ℝ) 1 := hX₂.1
  obtain ⟨u, -, huX⟩ := hseg₂
  have hun1 : u ≠ 1 := fun hue ↦ hX₂.2.2 (by
    rw [← huX, hue, AffineMap.lineMap_apply_one])
  have hXA : X - A = t • (C - A) := by
    rw [← htX, AffineMap.lineMap_apply_module]; module
  have hXB : X - B = u • (D - B) := by
    rw [← huX, AffineMap.lineMap_apply_module]; module
  have hXB' : X - B = t • (C - A) - (B - A) := by
    rw [show X - B = (X - A) - (B - A) by abel, hXA]
  have hDB : D - B = μ • (C - A) - (B - A) := by
    rw [← hμ]; module
  have e2 : ω (X - B) (C - A) = -ω (B - A) (C - A) := by
    rw [hXB', ω_sub_left, ω_smul_left, ω_self, mul_zero, zero_sub]
  have e2' : ω (X - B) (C - A) = -(u * ω (B - A) (C - A)) := by
    rw [hXB, hDB, ω_smul_left, ω_sub_left, ω_smul_left, ω_self, mul_zero, zero_sub,
      mul_neg]
  have e3 : ω (B - A) (C - A) = 0 := by
    have h3 : (1 - u) * ω (B - A) (C - A) = 0 := by
      rw [sub_mul, one_mul, sub_eq_zero]
      linarith [e2, e2']
    rcases mul_eq_zero.mp h3 with hu' | hω
    · exact absurd hu' (sub_ne_zero.mpr hun1.symm)
    · exact hω
  have hDC : D - C = (μ - 1) • (C - A) := by
    rw [show D - C = (D - A) - (C - A) by abel, hμ]; module
  have e4 : ω (B - C) (D - C) = 0 := by
    rw [hDC, ω_smul_right]
    have e5 : ω (B - C) (C - A) = ω (B - A) (C - A) := by
      rw [show B - C = (B - A) - (C - A) by abel, ω_sub_left, ω_self, sub_zero]
    rw [e5, e3, mul_zero]
  exact h.ω_BCD_ne e4

/-- The diagonal endpoints `A, C` of a convex quadrilateral are distinct. -/
theorem ConvexQuad.ne₁₃ {A B C D : Plane} (h : ConvexQuad A B C D) : A ≠ C := by
  obtain ⟨X, hX₁, -⟩ := h.diagonals
  exact hX₁.left_ne_right

/-- The diagonal endpoints `B, D` of a convex quadrilateral are distinct. -/
theorem ConvexQuad.ne₂₄ {A B C D : Plane} (h : ConvexQuad A B C D) : B ≠ D := by
  obtain ⟨X, -, hX₂⟩ := h.diagonals
  exact hX₂.left_ne_right

/-- Shifting an oriented angle by `π` replaces the absolute value of its `toReal` by
its complement to `π`. -/
theorem abs_toReal_add_pi (θ : Real.Angle) :
    |(θ + (Real.pi : Real.Angle)).toReal| = Real.pi - |θ.toReal| := by
  set t := θ.toReal with ht
  have h1 : -Real.pi < t := Real.Angle.neg_pi_lt_toReal θ
  have h2 : t ≤ Real.pi := Real.Angle.toReal_le_pi θ
  have htθ : (↑t : Real.Angle) = θ := by rw [ht, Real.Angle.coe_toReal]
  have e : θ + (Real.pi : Real.Angle) = ↑(t - Real.pi) := by
    rw [← Real.Angle.sub_coe_pi_eq_add_coe_pi, ← htθ, Real.Angle.coe_sub]
  rw [e]
  rcases lt_or_ge 0 t with h | h
  · rw [Real.Angle.toReal_coe_eq_self_iff.2 ⟨by linarith, by linarith⟩,
      abs_of_nonpos (by linarith), abs_of_nonneg h.le]
    ring
  · have e2 : (↑(t - Real.pi) : Real.Angle) = ↑(t + Real.pi) := by
      rw [Real.Angle.angle_eq_iff_two_pi_dvd_sub]
      exact ⟨-1, by ring⟩
    rw [e2, Real.Angle.toReal_coe_eq_self_iff.2 ⟨by linarith, by linarith⟩,
      abs_of_nonneg (by linarith), abs_of_nonpos h]
    ring

/-- **Linear core of the anchor disjunction**: if `w, x, y, z` are positive and sum to
`π`, then one of four pairs of linear inequalities holds.  (The point is that at least
one vertex of a convex cyclic quadrilateral has both its incident angles at the
diagonal small.) -/
theorem anchor_disjunction_linear {w x y z : ℝ} (hw : 0 < w) (hx : 0 < x) (hy : 0 < y)
    (hz : 0 < z) (hsum : w + x + y + z = Real.pi) :
    (x < Real.pi - x - y ∧ w < Real.pi - w - z) ∨
    (y < Real.pi - y - z ∧ x < Real.pi - x - w) ∨
    (z < Real.pi - w - z ∧ y < Real.pi - x - y) ∨
    (w < Real.pi - x - w ∧ z < Real.pi - y - z) := by
  by_contra hneg
  have h1 := not_and_or.mp (fun hd ↦ hneg (Or.inl hd))
  have h2 := not_and_or.mp (fun hd ↦ hneg (Or.inr (Or.inl hd)))
  have h3 := not_and_or.mp (fun hd ↦ hneg (Or.inr (Or.inr (Or.inl hd))))
  have h4 := not_and_or.mp (fun hd ↦ hneg (Or.inr (Or.inr (Or.inr hd))))
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;>
    rcases h4 with h4 | h4 <;> simp only [not_lt] at h1 h2 h3 h4 <;>
    linarith [hsum, hw, hx, hy, hz, Real.pi_pos]

/-- **Anchor disjunction** for IMO 1972 problem 2: in a convex cyclic quadrilateral
`A B C D`, at least one of the four "anchors" holds: the two sides at `B` are shorter
than the diagonal `BD`, or the two sides at `C` are shorter than the diagonal `CA`, or
the two sides at `D` are shorter than the diagonal `DB`, or the two sides at `A` are
shorter than the diagonal `AC`. -/
theorem anchor_disjunction {A B C D : Plane} (h : ConvexQuad A B C D)
    (hcyc : ∃ O : Plane, ∃ r : ℝ, dist A O = r ∧ dist B O = r ∧ dist C O = r ∧
      dist D O = r) :
    (dist B C < dist B D ∧ dist A B < dist B D) ∨
    (dist C D < dist C A ∧ dist B C < dist C A) ∨
    (dist D A < dist D B ∧ dist C D < dist D B) ∨
    (dist A B < dist A C ∧ dist D A < dist A C) := by
  obtain ⟨X, hX₁, hX₂⟩ := h.diagonals
  obtain ⟨O, r, hOA, hOB, hOC, hOD⟩ := hcyc
  have hne₁₃ : A ≠ C := hX₁.left_ne_right
  have hne₂₄ : B ≠ D := hX₂.left_ne_right
  -- noncollinearity of every vertex triple, in every order needed below
  have hcol_BAD : ¬ Collinear ℝ ({B, A, D} : Set Plane) :=
    fun hc ↦ h.ω_ABD_ne (ω_eq_zero_of_collinear hc)
  have hcol_CBD : ¬ Collinear ℝ ({C, B, D} : Set Plane) :=
    fun hc ↦ h.ω_BCD_ne (ω_eq_zero_of_collinear hc)
  have hcol_ABC : ¬ Collinear ℝ ({A, B, C} : Set Plane) := h.not_collinear_ABC
  have hcol_ACD : ¬ Collinear ℝ ({A, C, D} : Set Plane) := h.not_collinear_ACD
  have hcol_BDA : ¬ Collinear ℝ ({B, D, A} : Set Plane) := by
    rw [show ({B, D, A} : Set Plane) = {B, A, D} by rw [Set.pair_comm D A]]
    exact hcol_BAD
  have hcol_BDC : ¬ Collinear ℝ ({B, D, C} : Set Plane) := by
    rw [show ({B, D, C} : Set Plane) = {C, B, D} by
      rw [Set.insert_comm B D, Set.pair_comm B C, Set.insert_comm D C, Set.pair_comm D B]]
    exact hcol_CBD
  have hcol_DBC : ¬ Collinear ℝ ({D, B, C} : Set Plane) := by
    rw [show ({D, B, C} : Set Plane) = {C, B, D} by
      rw [Set.pair_comm B C, Set.insert_comm D C, Set.pair_comm D B]]
    exact hcol_CBD
  have hcol_DBA : ¬ Collinear ℝ ({D, B, A} : Set Plane) := by
    rw [show ({D, B, A} : Set Plane) = {B, A, D} by
      rw [Set.pair_comm B A, Set.insert_comm D A, Set.pair_comm D B, Set.insert_comm A B]]
    exact hcol_BAD
  have hcol_BCD : ¬ Collinear ℝ ({B, C, D} : Set Plane) := by
    rw [show ({B, C, D} : Set Plane) = {C, B, D} by rw [Set.insert_comm B C]]
    exact hcol_CBD
  have hcol_CDA : ¬ Collinear ℝ ({C, D, A} : Set Plane) := by
    rw [show ({C, D, A} : Set Plane) = {A, C, D} by
      rw [Set.pair_comm D A, Set.insert_comm C A]]
    exact hcol_ACD
  have hcol_CBA : ¬ Collinear ℝ ({C, B, A} : Set Plane) := by
    rw [show ({C, B, A} : Set Plane) = {A, B, C} by
      rw [Set.insert_comm C B, Set.pair_comm C A, Set.insert_comm B A]]
    exact hcol_ABC
  have hcol_DAB : ¬ Collinear ℝ ({D, A, B} : Set Plane) := by
    rw [show ({D, A, B} : Set Plane) = {B, A, D} by
      rw [Set.pair_comm A B, Set.insert_comm D B, Set.pair_comm D A]]
    exact hcol_BAD
  have hcol_DCB : ¬ Collinear ℝ ({D, C, B} : Set Plane) := by
    rw [show ({D, C, B} : Set Plane) = {C, B, D} by
      rw [Set.insert_comm D C, Set.pair_comm D B]]
    exact hcol_CBD
  have hcol_ADC : ¬ Collinear ℝ ({A, D, C} : Set Plane) := by
    rw [show ({A, D, C} : Set Plane) = {A, C, D} by rw [Set.pair_comm D C]]
    exact hcol_ACD
  have hcol_BAC : ¬ Collinear ℝ ({B, A, C} : Set Plane) := by
    rw [show ({B, A, C} : Set Plane) = {A, B, C} by rw [Set.insert_comm B A]]
    exact hcol_ABC
  have hcol_CAD : ¬ Collinear ℝ ({C, A, D} : Set Plane) := by
    rw [show ({C, A, D} : Set Plane) = {A, C, D} by rw [Set.insert_comm C A]]
    exact hcol_ACD
  have hcol_ACB : ¬ Collinear ℝ ({A, C, B} : Set Plane) := by
    rw [show ({A, C, B} : Set Plane) = {A, B, C} by rw [Set.pair_comm C B]]
    exact hcol_ABC
  have hcol_ABD : ¬ Collinear ℝ ({A, B, D} : Set Plane) := by
    rw [show ({A, B, D} : Set Plane) = {B, A, D} by rw [Set.insert_comm A B]]
    exact hcol_BAD
  -- cyclicity as a mathlib `Cospherical` fact, in all orders needed below
  have hsph : Cospherical ({A, B, C, D} : Set Plane) := ⟨O, r, fun q hq ↦ by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact hOA
    · exact hOB
    · exact hOC
    · exact hOD⟩
  have hsph1 : Cospherical ({D, A, C, B} : Set Plane) := by
    rw [show ({D, A, C, B} : Set Plane) = {A, B, C, D} by
      rw [Set.insert_comm D A, Set.insert_comm D C, Set.pair_comm D B,
        Set.insert_comm C B]]
    exact hsph
  have hsph2 : Cospherical ({B, A, D, C} : Set Plane) := by
    rw [show ({B, A, D, C} : Set Plane) = {A, B, C, D} by
      rw [Set.insert_comm B A, Set.pair_comm D C]]
    exact hsph
  have hsph3 : Cospherical ({C, A, B, D} : Set Plane) := by
    rw [show ({C, A, B, D} : Set Plane) = {A, B, C, D} by
      rw [Set.insert_comm C A, Set.insert_comm C B]]
    exact hsph
  have hsph4 : Cospherical ({A, C, D, B} : Set Plane) := by
    rw [show ({A, C, D, B} : Set Plane) = {A, B, C, D} by
      rw [Set.insert_comm C D, Set.pair_comm C B, Set.insert_comm D B,
        Set.pair_comm D C]]
    exact hsph
  have hsph5 : Cospherical ({A, C, B, D} : Set Plane) := by
    rw [show ({A, C, B, D} : Set Plane) = {A, B, C, D} by rw [Set.insert_comm C B]]
    exact hsph
  -- the five doubled-oangle relations from the inscribed angle theorem
  have e1 : (2 : ℤ) • ∡ D A B = (2 : ℤ) • ∡ D C B :=
    Cospherical.two_zsmul_oangle_eq hsph1 h.ne₄₁.symm h.ne₁₂ h.ne₃₄ h.ne₂₃.symm
  have e2 : (2 : ℤ) • ∡ B A C = (2 : ℤ) • ∡ B D C :=
    Cospherical.two_zsmul_oangle_eq hsph2 h.ne₁₂ hne₁₃ hne₂₄.symm h.ne₃₄.symm
  have e3 : (2 : ℤ) • ∡ C A D = (2 : ℤ) • ∡ C B D :=
    Cospherical.two_zsmul_oangle_eq hsph3 hne₁₃ h.ne₄₁.symm h.ne₂₃ hne₂₄
  have e4 : (2 : ℤ) • ∡ A C B = (2 : ℤ) • ∡ A D B :=
    Cospherical.two_zsmul_oangle_eq hsph4 hne₁₃.symm h.ne₂₃.symm h.ne₄₁ hne₂₄.symm
  have e5 : (2 : ℤ) • ∡ A C D = (2 : ℤ) • ∡ A B D :=
    Cospherical.two_zsmul_oangle_eq hsph5 hne₁₃.symm h.ne₃₄ h.ne₁₂.symm hne₂₄
  -- the sign relations from the diagonal crossing
  have s2 : (∡ B A C).sign = (∡ B D C).sign :=
    Sbtw.oangle_sign_eq_of_sbtw hX₂ hX₁.symm
  have s3 : (∡ C A D).sign = (∡ C B D).sign :=
    (Sbtw.oangle_sign_eq_of_sbtw hX₁.symm hX₂.symm).symm
  have s4 : (∡ A C B).sign = (∡ A D B).sign :=
    (Sbtw.oangle_sign_eq_of_sbtw hX₁ hX₂).symm
  have s5 : (∡ A C D).sign = (∡ A B D).sign :=
    (Sbtw.oangle_sign_eq_of_sbtw hX₁ hX₂.symm).symm
  have hXmem : X ∈ line[ℝ, B, D] := hX₂.wbtw.mem_affineSpan
  have hAnm : A ∉ line[ℝ, B, D] := by
    intro hA
    have hcol : Collinear ℝ ({A, B, D} : Set Plane) :=
      (collinear_insert_iff_of_mem_affineSpan hA).2 (collinear_pair ℝ _ _)
    exact hcol_ABD hcol
  have hopp : line[ℝ, B, D].SOppSide A C :=
    Sbtw.sOppSide_of_notMem_of_mem hX₁ hAnm hXmem
  have s1 : (∡ D A B).sign = -(∡ D C B).sign := by
    have e := AffineSubspace.SOppSide.oangle_sign_eq_neg
      (left_mem_affineSpan_pair ℝ B D) (right_mem_affineSpan_pair ℝ B D) hopp
    have hr1 : ∡ D A B = -∡ B A D := oangle_rev B A D
    have hr2 : ∡ D C B = -∡ B C D := oangle_rev B C D
    rw [hr1, hr2, Real.Angle.sign_neg (∡ B A D), Real.Angle.sign_neg (∡ B C D), e,
      neg_neg]
  -- the signs are nonzero (nondegeneracy)
  have nz1 : (∡ D C B).sign ≠ 0 :=
    fun hz ↦ hcol_DCB (oangle_sign_eq_zero_iff_collinear.mp hz)
  have nz2 : (∡ B A C).sign ≠ 0 :=
    fun hz ↦ hcol_BAC (oangle_sign_eq_zero_iff_collinear.mp hz)
  have nz3 : (∡ C A D).sign ≠ 0 :=
    fun hz ↦ hcol_CAD (oangle_sign_eq_zero_iff_collinear.mp hz)
  have nz4 : (∡ A C B).sign ≠ 0 :=
    fun hz ↦ hcol_ACB (oangle_sign_eq_zero_iff_collinear.mp hz)
  have nz5 : (∡ A C D).sign ≠ 0 :=
    fun hz ↦ hcol_ACD (oangle_sign_eq_zero_iff_collinear.mp hz)
  -- the five oangle conclusions
  have r1 : ∡ D A B = ∡ D C B + (Real.pi : Real.Angle) :=
    Real.Angle.eq_add_pi_of_two_zsmul_eq_of_sign_eq_neg (∡ D A B) (∡ D C B) e1 s1 nz1
  have r2 : ∡ B A C = ∡ B D C := (Real.Angle.two_zsmul_eq_iff_eq nz2 s2).mp e2
  have r3 : ∡ C A D = ∡ C B D := (Real.Angle.two_zsmul_eq_iff_eq nz3 s3).mp e3
  have r4 : ∡ A C B = ∡ A D B := (Real.Angle.two_zsmul_eq_iff_eq nz4 s4).mp e4
  have r5 : ∡ A C D = ∡ A B D := (Real.Angle.two_zsmul_eq_iff_eq nz5 s5).mp e5
  -- the unoriented angle conclusions
  have hDABpi : ∠ D A B + ∠ B C D = Real.pi := by
    rw [angle_comm B C D, angle_eq_abs_oangle_toReal h.ne₄₁ h.ne₁₂.symm,
      angle_eq_abs_oangle_toReal h.ne₃₄.symm h.ne₂₃, r1, abs_toReal_add_pi]
    ring
  have hBAC : ∠ B A C = ∠ B D C := by
    rw [angle_eq_abs_oangle_toReal h.ne₁₂.symm hne₁₃.symm, r2,
      ← angle_eq_abs_oangle_toReal hne₂₄ h.ne₃₄]
  have hCAD : ∠ C A D = ∠ D B C := by
    rw [← angle_comm C B D, angle_eq_abs_oangle_toReal hne₁₃.symm h.ne₄₁, r3,
      ← angle_eq_abs_oangle_toReal h.ne₂₃.symm hne₂₄.symm]
  have hACB : ∠ A C B = ∠ B D A := by
    rw [← angle_comm A D B, angle_eq_abs_oangle_toReal hne₁₃ h.ne₂₃, r4,
      ← angle_eq_abs_oangle_toReal h.ne₄₁.symm hne₂₄]
  have hACD : ∠ A C D = ∠ D B A := by
    rw [← angle_comm A B D, angle_eq_abs_oangle_toReal hne₁₃ h.ne₃₄.symm, r5,
      ← angle_eq_abs_oangle_toReal h.ne₁₂ hne₂₄.symm]
  -- the four triangle angle sums
  have hsumABD : ∠ D A B + ∠ B D A + ∠ D B A = Real.pi := by
    have hs := angle_add_angle_add_angle_eq_pi B h.ne₄₁.symm
    rw [angle_comm A B D] at hs
    linarith [hs]
  have hsumBCD : ∠ B C D + ∠ B D C + ∠ D B C = Real.pi := by
    have hs := angle_add_angle_add_angle_eq_pi D h.ne₂₃.symm
    rw [angle_comm C D B] at hs
    linarith [hs]
  have hsumABC : ∠ B A C + ∠ A C B + ∠ A B C = Real.pi := by
    have hs := angle_add_angle_add_angle_eq_pi C h.ne₁₂
    rw [angle_comm C B A] at hs
    linarith [hs]
  have hsumACD : ∠ C A D + ∠ A D C + ∠ A C D = Real.pi := by
    have hs := angle_add_angle_add_angle_eq_pi D hne₁₃
    rw [angle_comm D C A] at hs
    linarith [hs]
  -- positivity of the four angles at the diagonal `BD`, and their sum
  have hw : 0 < ∠ B D A := angle_pos_of_not_collinear hcol_BDA
  have hx : 0 < ∠ B D C := angle_pos_of_not_collinear hcol_BDC
  have hy : 0 < ∠ D B C := angle_pos_of_not_collinear hcol_DBC
  have hz : 0 < ∠ D B A := angle_pos_of_not_collinear hcol_DBA
  have hsum : ∠ B D A + ∠ B D C + ∠ D B C + ∠ D B A = Real.pi := by
    linarith [hsumABD, hsumBCD, hDABpi]
  -- the eight side/diagonal comparisons as linear conditions
  have c1 : dist B C < dist B D ↔ ∠ B D C < Real.pi - ∠ B D C - ∠ D B C := by
    have e : ∠ B C D = Real.pi - ∠ B D C - ∠ D B C := by linarith [hsumBCD]
    rw [← e]
    exact (angle_lt_iff_dist_lt hcol_BCD).symm
  have c2 : dist A B < dist B D ↔ ∠ B D A < Real.pi - ∠ B D A - ∠ D B A := by
    have e : ∠ B A D = Real.pi - ∠ B D A - ∠ D B A := by
      rw [angle_comm B A D]; linarith [hsumABD]
    rw [dist_comm A B, ← e]
    exact (angle_lt_iff_dist_lt hcol_BAD).symm
  have c3 : dist C D < dist C A ↔ ∠ D B C < Real.pi - ∠ D B C - ∠ D B A := by
    have e : ∠ C D A = Real.pi - ∠ D B C - ∠ D B A := by
      rw [angle_comm C D A]; linarith [hsumACD, hACD, hCAD]
    rw [← e, ← hCAD]
    exact (angle_lt_iff_dist_lt hcol_CDA).symm
  have c4 : dist B C < dist C A ↔ ∠ B D C < Real.pi - ∠ B D C - ∠ B D A := by
    have e : ∠ C B A = Real.pi - ∠ B D C - ∠ B D A := by
      rw [angle_comm C B A]; linarith [hsumABC, hACB, hBAC]
    rw [dist_comm B C, ← e, ← hBAC, ← angle_comm C A B]
    exact (angle_lt_iff_dist_lt hcol_CBA).symm
  have c5 : dist D A < dist D B ↔ ∠ D B A < Real.pi - ∠ B D A - ∠ D B A := by
    have e : ∠ D A B = Real.pi - ∠ B D A - ∠ D B A := by linarith [hsumABD]
    rw [← e]
    exact (angle_lt_iff_dist_lt hcol_DAB).symm
  have c6 : dist C D < dist D B ↔ ∠ D B C < Real.pi - ∠ B D C - ∠ D B C := by
    have e : ∠ D C B = Real.pi - ∠ B D C - ∠ D B C := by
      rw [angle_comm D C B]; linarith [hsumBCD]
    rw [dist_comm C D, ← e]
    exact (angle_lt_iff_dist_lt hcol_DCB).symm
  have c7 : dist A B < dist A C ↔ ∠ B D A < Real.pi - ∠ B D C - ∠ B D A := by
    have e : ∠ A B C = Real.pi - ∠ B D C - ∠ B D A := by
      linarith [hsumABC, hACB, hBAC]
    rw [← e, ← hACB]
    exact (angle_lt_iff_dist_lt hcol_ABC).symm
  have c8 : dist D A < dist A C ↔ ∠ D B A < Real.pi - ∠ D B C - ∠ D B A := by
    have e : ∠ A D C = Real.pi - ∠ D B C - ∠ D B A := by
      linarith [hsumACD, hACD, hCAD]
    rw [dist_comm D A, ← e, ← hACD]
    exact (angle_lt_iff_dist_lt hcol_ADC).symm
  -- conclusion: a pure linear disjunction in the four angles
  rw [c1, c2, c3, c4, c5, c6, c7, c8]
  exact anchor_disjunction_linear hw hx hy hz hsum

/-- A cyclic quadrilateral stays cyclic under a cyclic rotation of its vertices. -/
theorem CyclicQuad.rotate {A B C D : Plane} (h : CyclicQuad A B C D) : CyclicQuad B C D A :=
  ⟨⟨h.convex.not_mem₂, h.convex.not_mem₃, h.convex.not_mem₄, h.convex.not_mem₁, by
    obtain ⟨X, hX1, hX2⟩ := h.convex.diagonals
    exact ⟨X, hX2, hX1.symm⟩⟩,
   by obtain ⟨O, r, hA, hB, hC, hD⟩ := h.concyclic
      exact ⟨O, r, hB, hC, hD, hA⟩⟩

/-- The region of a quadrilateral does not change under a cyclic rotation of its
vertices. -/
theorem quadRegion_rotate (A B C D : Plane) : quadRegion B C D A = quadRegion A B C D := by
  unfold quadRegion
  congr 1
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

/-- A dissection with trapezoid transports under a cyclic rotation of the vertices. -/
theorem DissectionWithTrapezoid.rotate {A B C D : Plane} {n : ℕ}
    (h : DissectionWithTrapezoid B C D A n) : DissectionWithTrapezoid A B C D n := by
  obtain ⟨d, i, hi⟩ := h
  refine ⟨⟨d.pieces, d.cyclic, ?_, ?_, d.disjoint⟩, i, hi⟩
  · intro j
    simpa only [quadRegion_rotate A B C D] using d.subset j
  · simpa only [quadRegion_rotate A B C D] using d.cover

/-! ### Halfspace and interior lemmas for the anchor base case -/

/-- The closed halfspace `{x | c ≤ ω u (x - V)}` is convex (the functional is affine). -/
theorem convex_ω_ge (u V : Plane) (c : ℝ) : Convex ℝ {x : Plane | c ≤ ω u (x - V)} := by
  intro a ha b hb t₁ t₂ ht₁ ht₂ hsum
  simp only [Set.mem_setOf_eq] at ha hb ⊢
  have e : ω u ((t₁ • a + t₂ • b) - V) = t₁ * ω u (a - V) + t₂ * ω u (b - V) := by
    have e2 : t₁ • a + t₂ • b - V = t₁ • (a - V) + t₂ • (b - V) := by
      conv_lhs => rw [show V = (t₁ + t₂) • V by rw [hsum, one_smul]]
      module
    rw [e2, ω_add_right, ω_smul_right, ω_smul_right]
  rw [e]
  have h1 : t₁ * c + t₂ * c ≤ t₁ * ω u (a - V) + t₂ * ω u (b - V) :=
    add_le_add (mul_le_mul_of_nonneg_left ha ht₁) (mul_le_mul_of_nonneg_left hb ht₂)
  have h2 : t₁ * c + t₂ * c = c := by rw [← add_mul, hsum, one_mul]
  linarith [h1, h2]

/-- The closed halfspace `{x | ω u (x - V) ≤ c}` is convex. -/
theorem convex_ω_le (u V : Plane) (c : ℝ) : Convex ℝ {x : Plane | ω u (x - V) ≤ c} := by
  intro a ha b hb t₁ t₂ ht₁ ht₂ hsum
  simp only [Set.mem_setOf_eq] at ha hb ⊢
  have e : ω u ((t₁ • a + t₂ • b) - V) = t₁ * ω u (a - V) + t₂ * ω u (b - V) := by
    have e2 : t₁ • a + t₂ • b - V = t₁ • (a - V) + t₂ • (b - V) := by
      conv_lhs => rw [show V = (t₁ + t₂) • V by rw [hsum, one_smul]]
      module
    rw [e2, ω_add_right, ω_smul_right, ω_smul_right]
  rw [e]
  have h1 : t₁ * ω u (a - V) + t₂ * ω u (b - V) ≤ t₁ * c + t₂ * c :=
    add_le_add (mul_le_mul_of_nonneg_left ha ht₁) (mul_le_mul_of_nonneg_left hb ht₂)
  have h2 : t₁ * c + t₂ * c = c := by rw [← add_mul, hsum, one_mul]
  linarith [h1, h2]

/-- The `ω`-functional `x ↦ ω u (x - V)` is continuous (it is a linear map plus a
constant on a finite-dimensional space). -/
theorem continuous_ω_sub (u V : Plane) : Continuous fun x : Plane ↦ ω u (x - V) := by
  have heq : (fun x : Plane ↦ ω u (x - V)) = fun x ↦ ωR u x - ωR u V := by
    funext x
    show ω u (x - V) = ωR u x - ωR u V
    rw [show ω u (x - V) = ωR u (x - V) from rfl, map_sub]
  rw [heq]
  exact Continuous.sub (LinearMap.continuous_of_finiteDimensional (ωR u)) continuous_const

/-- The interior of a closed halfspace cut out by the (nonconstant) `ω`-functional is
the corresponding open halfspace. -/
theorem interior_ω_halfspace {u V : Plane} (hu : u ≠ 0) (c : ℝ) :
    interior {x : Plane | c ≤ ω u (x - V)} = {x : Plane | c < ω u (x - V)} := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
    have hxc : c ≤ ω u (x - V) := hball (Metric.mem_ball_self hε)
    simp only [Set.mem_setOf_eq]
    rcases hxc.lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      -- perturb `x` in the direction `W` with `ω u W > 0`
      set W : Plane := PiLp.single 2 0 (-(u 1)) + PiLp.single 2 1 (u 0) with hWdef
      have hW0 : W 0 = -(u 1) := by
        rw [hWdef, PiLp.add_apply, PiLp.single_apply, PiLp.single_apply, if_pos rfl,
          if_neg (show (0 : Fin 2) ≠ 1 from by decide), add_zero]
      have hW1 : W 1 = u 0 := by
        rw [hWdef, PiLp.add_apply, PiLp.single_apply, PiLp.single_apply,
          if_neg (show (1 : Fin 2) ≠ 0 from by decide), if_pos rfl, zero_add]
      have hωW : ω u W = u 0 * u 0 + u 1 * u 1 := by
        show u 0 * W 1 - u 1 * W 0 = u 0 * u 0 + u 1 * u 1
        rw [hW0, hW1]
        ring
      have hωWpos : 0 < ω u W := by
        rw [hωW]
        have hne : u 0 ≠ 0 ∨ u 1 ≠ 0 := by
          by_contra hboth
          push_neg at hboth
          apply hu
          apply PiLp.ext
          intro i
          fin_cases i
          · show u 0 = (0 : Plane) 0
            rw [PiLp.zero_apply]
            exact hboth.1
          · show u 1 = (0 : Plane) 1
            rw [PiLp.zero_apply]
            exact hboth.2
        rcases hne with h0 | h1
        · nlinarith [mul_self_pos.mpr h0, mul_self_nonneg (u 1)]
        · nlinarith [mul_self_nonneg (u 0), mul_self_pos.mpr h1]
      set δ := ε / 2 / (‖W‖ + 1) with hδdef
      have hδ : 0 < δ :=
        div_pos (half_pos hε) (add_pos_of_nonneg_of_pos (norm_nonneg W) zero_lt_one)
      have hzmem : x - δ • W ∈ Metric.ball x ε := by
        rw [Metric.mem_ball, dist_eq_norm]
        have e : x - δ • W - x = -(δ • W) := by module
        rw [e, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hδ]
        have h2 : ‖W‖ / (‖W‖ + 1) < 1 := by
          rw [div_lt_one (add_pos_of_nonneg_of_pos (norm_nonneg W) zero_lt_one)]
          linarith [norm_nonneg W]
        have h3 : δ * ‖W‖ = (ε / 2) * (‖W‖ / (‖W‖ + 1)) := by
          rw [hδdef]
          ring
        rw [h3]
        linarith [mul_lt_mul_of_pos_left h2 (half_pos hε), hε]
      have hz := hball hzmem
      simp only [Set.mem_setOf_eq] at hz
      have e2 : ω u ((x - δ • W) - V) = ω u (x - V) - δ * ω u W := by
        rw [show x - δ • W - V = (x - V) - δ • W by module, ω_sub_right, ω_smul_right]
      rw [e2, ← heq] at hz
      nlinarith [hz, hδ, hωWpos]
  · apply interior_maximal
    · intro x hx
      simp only [Set.mem_setOf_eq] at hx ⊢
      exact le_of_lt hx
    · exact isOpen_lt continuous_const (continuous_ω_sub u V)

/-- The interior of the closed halfspace `{x | ω u (x - V) ≤ c}` is the open one. -/
theorem interior_ω_halfspace_le {u V : Plane} (hu : u ≠ 0) (c : ℝ) :
    interior {x : Plane | ω u (x - V) ≤ c} = {x : Plane | ω u (x - V) < c} := by
  have e1 : {x : Plane | ω u (x - V) ≤ c} = {x : Plane | -c ≤ ω (-u) (x - V)} := by
    ext x
    simp only [Set.mem_setOf_eq, ω_neg_left]
    constructor <;> intro h1 <;> linarith [h1]
  have e2 : {x : Plane | ω u (x - V) < c} = {x : Plane | -c < ω (-u) (x - V)} := by
    ext x
    simp only [Set.mem_setOf_eq, ω_neg_left]
    constructor <;> intro h1 <;> linarith [h1]
  rw [e1, e2]
  exact interior_ω_halfspace (neg_ne_zero.mpr hu) (-c)

/-- A point interior to a set contained in a closed halfspace lies in the open
halfspace. -/
theorem mem_open_halfspace_of_mem_interior {T : Set Plane} {u V : Plane} {c : ℝ}
    (hu : u ≠ 0) (hT : T ⊆ {x : Plane | c ≤ ω u (x - V)}) {x : Plane}
    (hx : x ∈ interior T) : c < ω u (x - V) := by
  have h := interior_mono hT hx
  rw [interior_ω_halfspace hu c] at h
  exact h

/-- A point interior to a set contained in a closed halfspace (`≤` side) lies in the
open halfspace. -/
theorem mem_open_halfspace_le_of_mem_interior {T : Set Plane} {u V : Plane} {c : ℝ}
    (hu : u ≠ 0) (hT : T ⊆ {x : Plane | ω u (x - V) ≤ c}) {x : Plane}
    (hx : x ∈ interior T) : ω u (x - V) < c := by
  have h := interior_mono hT hx
  rw [interior_ω_halfspace_le hu c] at h
  exact h

/-- If the line through `U ≠ V` weakly separates the sets `s` and `t` (with `s` on the
nonnegative side of the `ω`-functional), then the interiors of their convex hulls are
disjoint. -/
theorem disjoint_interior_convexHull_of_ω_sep {s t : Set Plane} {U V : Plane}
    (hUV : U ≠ V) (hs : ∀ x ∈ s, (0:ℝ) ≤ ω (V - U) (x - U))
    (ht : ∀ x ∈ t, ω (V - U) (x - U) ≤ 0) :
    Disjoint (interior (convexHull ℝ s)) (interior (convexHull ℝ t)) := by
  have hu : V - U ≠ 0 := sub_ne_zero.mpr hUV.symm
  have h1 : convexHull ℝ s ⊆ {x : Plane | (0:ℝ) ≤ ω (V - U) (x - U)} :=
    convexHull_min hs (convex_ω_ge (V - U) U 0)
  have h2 : convexHull ℝ t ⊆ {x : Plane | ω (V - U) (x - U) ≤ 0} :=
    convexHull_min ht (convex_ω_le (V - U) U 0)
  apply Set.disjoint_left.mpr
  intro x hxs hxt
  have hx1 : (0:ℝ) < ω (V - U) (x - U) := by
    have h1' := interior_mono h1 hxs
    rw [interior_ω_halfspace hu 0] at h1'
    exact h1'
  have hx2 : ω (V - U) (x - U) < (0:ℝ) := by
    have h2' := interior_mono h2 hxt
    rw [interior_ω_halfspace_le hu 0] at h2'
    exact h2'
  exact absurd hx1 (not_lt.mpr hx2.le)

/-- If the line through `U ≠ V` has all points of `s` on the `σ`-side and all points of
`t` on the opposite side (for a common nonzero sign `σ`), then the interiors of the two
convex hulls are disjoint. -/
theorem disjoint_of_common_sign_line {s t : Set Plane} {U V : Plane} {σ : ℝ}
    (hUV : U ≠ V) (hσ : σ ≠ 0)
    (hs : ∀ x ∈ s, (0:ℝ) ≤ ω (V - U) (x - U) * σ)
    (ht : ∀ x ∈ t, ω (V - U) (x - U) * σ ≤ 0) :
    Disjoint (interior (convexHull ℝ s)) (interior (convexHull ℝ t)) := by
  rcases lt_or_gt_of_ne hσ with hneg | hpos
  · exact (disjoint_interior_convexHull_of_ω_sep hUV
      (fun x hx ↦ nonneg_of_mul_nonpos_left (ht x hx) hneg)
      (fun x hx ↦ nonpos_of_mul_nonneg_left (hs x hx) hneg)).symm
  · exact disjoint_interior_convexHull_of_ω_sep hUV
      (fun x hx ↦ nonneg_of_mul_nonneg_left (hs x hx) hpos)
      (fun x hx ↦ nonpos_of_mul_nonpos_left (ht x hx) hpos)

/-- Near a point where a continuous function is negative, it stays negative. -/
theorem exists_ball_of_neg {f : Plane → ℝ} (hfc : Continuous f) {x : Plane} (hx : f x < 0) :
    ∃ ε > (0:ℝ), ∀ y ∈ Metric.ball x ε, f y < 0 := by
  have hopen : IsOpen {y : Plane | f y < 0} := isOpen_lt hfc continuous_const
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen x hx
  exact ⟨ε, hε, hball⟩

/-- Near a point where a continuous function is positive, it stays positive. -/
theorem exists_ball_of_pos {f : Plane → ℝ} (hfc : Continuous f) {x : Plane} (hx : 0 < f x) :
    ∃ ε > (0:ℝ), ∀ y ∈ Metric.ball x ε, 0 < f y := by
  have hopen : IsOpen {y : Plane | 0 < f y} := isOpen_lt continuous_const hfc
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen x hx
  exact ⟨ε, hε, hball⟩

/-- If a ball around `x` lands in `T₁ ∪ T₂` with `T₂` on the nonnegative side of the
`ω`-level through `V` in direction `P - V`, while `x` itself is strictly negative, then
`x` is interior to `T₁`. -/
theorem mem_interior_of_union_of_neg {P V x : Plane} {T₁ T₂ : Set Plane}
    (hT₂ : T₂ ⊆ {y : Plane | (0:ℝ) ≤ ω (P - V) (y - V)})
    (hx : ∃ ε > (0:ℝ), ∀ y ∈ Metric.ball x ε, y ∈ T₁ ∪ T₂)
    (hneg : ω (P - V) (x - V) < 0) :
    x ∈ interior T₁ := by
  obtain ⟨ε, hε, hball⟩ := hx
  obtain ⟨ε₂, hε₂, hball₂⟩ := exists_ball_of_neg (continuous_ω_sub (P - V) V) hneg
  refine mem_interior_iff_mem_nhds.mpr (Metric.mem_nhds_iff.mpr
    ⟨min ε ε₂, lt_min hε hε₂, fun y hy ↦ ?_⟩)
  have hy2 := hball₂ y (Metric.ball_subset_ball (min_le_right ε ε₂) hy)
  rcases hball y (Metric.ball_subset_ball (min_le_left ε ε₂) hy) with hy1 | hy1
  · exact hy1
  · exact absurd hy2 (not_lt.mpr (hT₂ hy1))

/-- The `>` version of `mem_interior_of_union_of_neg`. -/
theorem mem_interior_of_union_of_pos {P V x : Plane} {T₁ T₂ : Set Plane}
    (hT₂ : T₂ ⊆ {y : Plane | ω (P - V) (y - V) ≤ 0})
    (hx : ∃ ε > (0:ℝ), ∀ y ∈ Metric.ball x ε, y ∈ T₁ ∪ T₂)
    (hpos : 0 < ω (P - V) (x - V)) :
    x ∈ interior T₁ := by
  obtain ⟨ε, hε, hball⟩ := hx
  obtain ⟨ε₂, hε₂, hball₂⟩ := exists_ball_of_pos (continuous_ω_sub (P - V) V) hpos
  refine mem_interior_iff_mem_nhds.mpr (Metric.mem_nhds_iff.mpr
    ⟨min ε ε₂, lt_min hε hε₂, fun y hy ↦ ?_⟩)
  have hy2 := hball₂ y (Metric.ball_subset_ball (min_le_right ε ε₂) hy)
  rcases hball y (Metric.ball_subset_ball (min_le_left ε ε₂) hy) with hy1 | hy1
  · exact hy1
  · exact absurd hy2 (not_lt.mpr (hT₂ hy1))

/-- A point of a triangle `hull {V, S, P}` that lies on the line `VP` (with `S` off the
line, measured by the `ω`-functional) lies on the segment `VP`. -/
theorem mem_segment_of_mem_hull_triangle_ω_eq_zero {V S P x : Plane}
    (hVS : V ≠ S) (hVP : V ≠ P) (hSP : S ≠ P)
    (hS : ω (P - V) (S - V) ≠ 0)
    (hx : x ∈ convexHull ℝ {V, S, P}) (hfx : ω (P - V) (x - V) = 0) :
    x ∈ segment ℝ V P := by
  rw [show ({V, S, P} : Set Plane) = (({V, S, P} : Finset Plane) : Set Plane) by simp] at hx
  obtain ⟨w, hw0, hw1, hw2⟩ := Finset.mem_convexHull'.mp hx
  have hV : V ∉ ({S, P} : Finset Plane) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hVS, hVP⟩
  have hS' : S ∉ ({P} : Finset Plane) := by
    simp only [Finset.mem_singleton]
    exact hSP
  rw [Finset.sum_insert hV, Finset.sum_insert hS', Finset.sum_singleton] at hw1 hw2
  have hm1 : V ∈ ({V, S, P} : Finset Plane) := Finset.mem_insert_self _ _
  have hm2 : S ∈ ({V, S, P} : Finset Plane) :=
    Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hm3 : P ∈ ({V, S, P} : Finset Plane) :=
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hsum : w V + w S + w P = 1 := by linarith [hw1]
  have hxV : x - V = w S • (S - V) + w P • (P - V) := by
    rw [← hw2]
    have h2 : w V • V + (w S • S + w P • P) - V =
        w V • V + (w S • S + w P • P) - (w V + w S + w P) • V := by
      rw [hsum, one_smul]
    rw [h2]
    module
  have hf : ω (P - V) (x - V) = w S * ω (P - V) (S - V) := by
    rw [hxV, ω_add_right, ω_smul_right, ω_smul_right, ω_self, mul_zero, add_zero]
  have hwS : w S = 0 := by
    rw [hf] at hfx
    exact (mul_eq_zero.mp hfx).resolve_right hS
  rw [hwS, zero_smul, zero_add] at hw2
  have hsum2 : w V + w P = 1 := by linarith [hsum, hwS]
  exact ⟨w V, w P, hw0 V hm1, hw0 P hm3, hsum2, hw2⟩

/-- Any point of `convexHull (insert x T)` is a convex combination of `x` with a point
of `convexHull T`. -/
theorem mem_convexHull_insert {x z : Plane} {T : Set Plane}
    (hT : (convexHull ℝ T).Nonempty) (hz : z ∈ convexHull ℝ (insert x T)) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ ∃ Y ∈ convexHull ℝ T, z = (1 - t) • x + t • Y := by
  obtain ⟨Y₀, hY₀⟩ := hT
  set S : Set Plane := {zz | ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ ∃ Y ∈ convexHull ℝ T,
    zz = (1 - t) • x + t • Y} with hSdef
  have hsub : insert x T ⊆ S := by
    intro y hy
    simp only [Set.mem_insert_iff] at hy
    rcases hy with rfl | hyT
    · exact ⟨0, le_refl 0, zero_le_one, Y₀, hY₀, by
        rw [sub_zero, one_smul, zero_smul, add_zero]⟩
    · exact ⟨1, zero_le_one, le_refl 1, y, subset_convexHull ℝ T hyT, by
        rw [sub_self, zero_smul, one_smul, zero_add]⟩
  have hconv : Convex ℝ S := by
    rintro a ⟨s₁, hs₁0, hs₁1, Y₁, hY₁, ha⟩ b ⟨s₂, hs₂0, hs₂1, Y₂, hY₂, hb⟩ t₁ t₂ ht₁ ht₂ hsum
    set t := t₁ * s₁ + t₂ * s₂ with htdef
    have ht0 : 0 ≤ t := add_nonneg (mul_nonneg ht₁ hs₁0) (mul_nonneg ht₂ hs₂0)
    have ht1 : t ≤ 1 := by
      have hle : t ≤ t₁ * 1 + t₂ * 1 :=
        add_le_add (mul_le_mul_of_nonneg_left hs₁1 ht₁) (mul_le_mul_of_nonneg_left hs₂1 ht₂)
      rw [mul_one, mul_one, hsum] at hle
      exact hle
    rcases eq_or_lt_of_le ht0 with htz | htp
    · have h1 : t₁ * s₁ = 0 := by
        have hle : t₁ * s₁ ≤ 0 := by
          have h2 : t₁ * s₁ ≤ t₁ * s₁ + t₂ * s₂ :=
            le_add_of_nonneg_right (mul_nonneg ht₂ hs₂0)
          rw [← htdef, ← htz] at h2
          exact h2
        exact le_antisymm hle (mul_nonneg ht₁ hs₁0)
      have h2 : t₂ * s₂ = 0 := by
        have hle : t₂ * s₂ ≤ 0 := by
          have h3 : t₂ * s₂ ≤ t₁ * s₁ + t₂ * s₂ :=
            le_add_of_nonneg_left (mul_nonneg ht₁ hs₁0)
          rw [← htdef, ← htz] at h3
          exact h3
        exact le_antisymm hle (mul_nonneg ht₂ hs₂0)
      refine ⟨0, le_refl 0, zero_le_one, Y₀, hY₀, ?_⟩
      rw [sub_zero, one_smul, zero_smul, add_zero, ha, hb]
      have e : t₁ • ((1 - s₁) • x + s₁ • Y₁) + t₂ • ((1 - s₂) • x + s₂ • Y₂) =
          (t₁ * (1 - s₁) + t₂ * (1 - s₂)) • x + ((t₁ * s₁) • Y₁ + (t₂ * s₂) • Y₂) := by
        module
      rw [e, h1, h2, zero_smul, zero_smul, add_zero, add_zero]
      have h3 : t₁ * (1 - s₁) + t₂ * (1 - s₂) = 1 := by
        have h4 : t₁ * (1 - s₁) + t₂ * (1 - s₂) = (t₁ + t₂) - (t₁ * s₁ + t₂ * s₂) := by
          ring
        rw [h4, hsum, ← htdef, ← htz, sub_zero]
      rw [h3, one_smul]
    · refine ⟨t, ht0, ht1, (t₁ * s₁ / t) • Y₁ + (t₂ * s₂ / t) • Y₂, ?_, ?_⟩
      · exact (convex_convexHull ℝ T) hY₁ hY₂
          (div_nonneg (mul_nonneg ht₁ hs₁0) htp.le)
          (div_nonneg (mul_nonneg ht₂ hs₂0) htp.le)
          (by rw [← add_div, ← htdef, div_self htp.ne'])
      · rw [ha, hb]
        have e : t₁ • ((1 - s₁) • x + s₁ • Y₁) + t₂ • ((1 - s₂) • x + s₂ • Y₂) =
            (t₁ * (1 - s₁) + t₂ * (1 - s₂)) • x + ((t₁ * s₁) • Y₁ + (t₂ * s₂) • Y₂) := by
          module
        rw [e]
        have h3 : t₁ * (1 - s₁) + t₂ * (1 - s₂) = 1 - t := by
          have h4 : t₁ * (1 - s₁) + t₂ * (1 - s₂) = (t₁ + t₂) - (t₁ * s₁ + t₂ * s₂) := by
            ring
          rw [h4, hsum, ← htdef]
        rw [h3]
        have e2 : (t₁ * s₁) • Y₁ + (t₂ * s₂) • Y₂ =
            t • ((t₁ * s₁ / t) • Y₁ + (t₂ * s₂ / t) • Y₂) := by
          rw [smul_add, smul_smul, smul_smul, mul_div_cancel₀ _ htp.ne',
            mul_div_cancel₀ _ htp.ne']
        rw [e2]
  exact convexHull_min hsub hconv hz

/-- A point not in `convexHull T` is not interior to `convexHull (insert x T)`:
otherwise two antipodal perturbations would write it as a convex combination of points
of `convexHull T`. -/
theorem not_mem_interior_convexHull_insert {x : Plane} {T : Set Plane}
    (hT : (convexHull ℝ T).Nonempty) (hx : x ∉ convexHull ℝ T) :
    x ∉ interior (convexHull ℝ (insert x T)) := by
  intro hmem
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hmem)
  set v : Plane := PiLp.single 2 0 (1:ℝ) with hvdef
  have hv0 : v 0 = 1 := by
    rw [hvdef, PiLp.single_apply, if_pos rfl]
  have hv : v ≠ 0 := by
    intro hzero
    have h1 : v 0 = (0 : Plane) 0 := by rw [hzero]
    rw [hv0, PiLp.zero_apply] at h1
    exact one_ne_zero h1
  set δ := ε / 2 / (‖v‖ + 1) with hδdef
  have hδ : 0 < δ :=
    div_pos (half_pos hε) (add_pos_of_nonneg_of_pos (norm_nonneg v) zero_lt_one)
  have hδnorm : δ * ‖v‖ < ε := by
    have h2 : ‖v‖ / (‖v‖ + 1) < 1 := by
      rw [div_lt_one (add_pos_of_nonneg_of_pos (norm_nonneg v) zero_lt_one)]
      linarith [norm_nonneg v]
    have h3 : δ * ‖v‖ = (ε / 2) * (‖v‖ / (‖v‖ + 1)) := by
      rw [hδdef]
      ring
    rw [h3]
    linarith [mul_lt_mul_of_pos_left h2 (half_pos hε), hε]
  have hmem1 : x + δ • v ∈ Metric.ball x ε := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos hδ]
    exact hδnorm
  have hmem2 : x - δ • v ∈ Metric.ball x ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    have e : x - δ • v - x = -(δ • v) := by module
    rw [e, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hδ]
    exact hδnorm
  obtain ⟨t₁, ht₁0, ht₁1, Y₁, hY₁, hz₁⟩ := mem_convexHull_insert hT (hball hmem1)
  obtain ⟨t₂, ht₂0, ht₂1, Y₂, hY₂, hz₂⟩ := mem_convexHull_insert hT (hball hmem2)
  have e1 : δ • v = t₁ • (Y₁ - x) := by
    have h1 : x + δ • v = x + t₁ • (Y₁ - x) := by
      rw [hz₁]
      module
    exact add_left_cancel h1
  have ht₁pos : 0 < t₁ := by
    rcases ht₁0.eq_or_lt with h0 | hpos
    · exfalso
      rw [← h0, zero_smul] at e1
      rcases smul_eq_zero.mp e1 with hδ0 | hv0'
      · exact absurd hδ0 (ne_of_gt hδ)
      · exact hv hv0'
    · exact hpos
  have e2 : (-δ) • v = t₂ • (Y₂ - x) := by
    have h1 : x + (-δ) • v = x + t₂ • (Y₂ - x) := by
      have h1a : x + (-δ) • v = x - δ • v := by module
      rw [h1a, hz₂]
      module
    exact add_left_cancel h1
  have ht₂pos : 0 < t₂ := by
    rcases ht₂0.eq_or_lt with h0 | hpos
    · exfalso
      rw [← h0, zero_smul] at e2
      rcases smul_eq_zero.mp e2 with hδ0 | hv0'
      · exact absurd hδ0 (neg_ne_zero.mpr (ne_of_gt hδ))
      · exact hv hv0'
    · exact hpos
  have e3 : (t₁ + t₂) • x = t₁ • Y₁ + t₂ • Y₂ := by
    have h1 : t₁ • (Y₁ - x) + t₂ • (Y₂ - x) = 0 := by
      rw [← e1, ← e2]
      module
    have h2 : t₁ • (Y₁ - x) + t₂ • (Y₂ - x) = (t₁ • Y₁ + t₂ • Y₂) - (t₁ + t₂) • x := by
      module
    rw [h2, sub_eq_zero] at h1
    exact h1.symm
  have hts : 0 < t₁ + t₂ := add_pos ht₁pos ht₂pos
  have hxmem : x ∈ convexHull ℝ T := by
    have h1 : x = (t₁ / (t₁ + t₂)) • Y₁ + (t₂ / (t₁ + t₂)) • Y₂ := by
      have h2 : x = (t₁ + t₂)⁻¹ • ((t₁ + t₂) • x) := by
        rw [inv_smul_smul₀ hts.ne']
      rw [h2, e3, smul_add, smul_smul, smul_smul]
      have h3 : (t₁ + t₂)⁻¹ * t₁ = t₁ / (t₁ + t₂) := by
        rw [div_eq_mul_inv, mul_comm]
      have h4 : (t₁ + t₂)⁻¹ * t₂ = t₂ / (t₁ + t₂) := by
        rw [div_eq_mul_inv, mul_comm]
      rw [h3, h4]
    rw [h1]
    exact (convex_convexHull ℝ T) hY₁ hY₂
      (div_nonneg ht₁0 hts.le) (div_nonneg ht₂0 hts.le)
      (by rw [← add_div, div_self hts.ne'])
  exact hx hxmem

/-- In a strictly convex quadrilateral `V S₁ P S₂`, the vertices `S₁, S₂` lie strictly
on opposite sides of the diagonal line `VP`. -/
theorem ConvexQuad.opp_side_diagonal {V S₁ P S₂ : Plane} (h : ConvexQuad V S₁ P S₂) :
    ω (P - V) (S₁ - V) * ω (P - V) (S₂ - V) < 0 := by
  obtain ⟨X, hX₁, hX₂⟩ := h.diagonals
  obtain ⟨a, b, ha, hb, hab, hXc⟩ := sbtw_combo hX₂
  obtain ⟨c, d, hc, hd, hcd, hXd⟩ := sbtw_combo hX₁
  have e1 : X - V = a • (S₁ - V) + b • (S₂ - V) := by
    rw [← hXc]
    exact combo_sub a b S₁ S₂ V hab
  have e2 : X - V = d • (P - V) := by
    rw [← hXd, combo_sub c d V P V hcd, sub_self, smul_zero, zero_add]
  have key : a * ω (P - V) (S₁ - V) + b * ω (P - V) (S₂ - V) = 0 := by
    have w1 : ω (P - V) (X - V) = a * ω (P - V) (S₁ - V) + b * ω (P - V) (S₂ - V) := by
      rw [e1, ω_add_right, ω_smul_right, ω_smul_right]
    have w2 : ω (P - V) (X - V) = 0 := by
      rw [e2, ω_smul_right, ω_self, mul_zero]
    rw [w2] at w1
    exact w1.symm
  have hne : ω (P - V) (S₁ - V) ≠ 0 := by
    rw [ω_triangle]
    exact h.ω_ABC_ne
  have h2 : ω (P - V) (S₂ - V) = -(a / b) * ω (P - V) (S₁ - V) := by
    have hb' : b ≠ 0 := hb.ne'
    field_simp [hb']
    linarith [key]
  rw [h2]
  have e3 : ω (P - V) (S₁ - V) * (-(a / b) * ω (P - V) (S₁ - V)) =
      -((a / b) * (ω (P - V) (S₁ - V) * ω (P - V) (S₁ - V))) := by ring
  rw [e3]
  exact neg_neg_of_pos (mul_pos (div_pos ha hb) (mul_self_pos.mpr hne))

/-- A point interior to a strictly convex quadrilateral `V S₁ P S₂` is interior to one
of the two triangles cut out by the diagonal `VP`, or lies strictly between `V` and `P`
on that diagonal. -/
theorem interior_convexHull_quad_subset_union {V S₁ S₂ P : Plane} (h : ConvexQuad V S₁ P S₂)
    {x : Plane} (hx : x ∈ interior (convexHull ℝ {V, S₁, P, S₂})) :
    x ∈ interior (convexHull ℝ {V, S₁, P}) ∪ interior (convexHull ℝ {V, P, S₂}) ∪
      {X : Plane | Sbtw ℝ V X P} := by
  have hsign : ω (P - V) (S₁ - V) * ω (P - V) (S₂ - V) < 0 := h.opp_side_diagonal
  have hS₁ : ω (P - V) (S₁ - V) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hsign
    exact (lt_irrefl 0) hsign
  have hS₂ : ω (P - V) (S₂ - V) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hsign
    exact (lt_irrefl 0) hsign
  have hxU : x ∈ convexHull ℝ {V, S₁, P} ∪ convexHull ℝ {V, P, S₂} :=
    convexHull_quad_subset_union_triangle h (interior_subset hx)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
  have hballU : ∀ y ∈ Metric.ball x ε,
      y ∈ convexHull ℝ {V, S₁, P} ∪ convexHull ℝ {V, P, S₂} :=
    fun y hy ↦ convexHull_quad_subset_union_triangle h (hball hy)
  rcases lt_trichotomy (ω (P - V) (x - V)) 0 with hneg | hzero | hpos
  · -- `x` strictly on the negative side: interior to the triangle on that side
    have hcase : x ∈ interior (convexHull ℝ {V, S₁, P}) ∨
        x ∈ interior (convexHull ℝ {V, P, S₂}) := by
      rcases lt_or_gt_of_ne hS₁ with hS₁neg | hS₁pos
      · left
        have hS₂pos : 0 < ω (P - V) (S₂ - V) := by
          rcases lt_or_gt_of_ne hS₂ with h1 | h1
          · exact absurd hsign (not_lt.mpr
              (mul_nonneg_of_nonpos_of_nonpos (le_of_lt hS₁neg) (le_of_lt h1)))
          · exact h1
        have hT₂ : convexHull ℝ {V, P, S₂} ⊆ {y : Plane | (0:ℝ) ≤ ω (P - V) (y - V)} := by
          apply convexHull_min _ (convex_ω_ge (P - V) V 0)
          intro y hy
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
          rcases hy with rfl | rfl | rfl
          · simp only [Set.mem_setOf_eq, sub_self, ω_zero_right, le_refl]
          · simp only [Set.mem_setOf_eq, ω_self, le_refl]
          · exact le_of_lt hS₂pos
        exact mem_interior_of_union_of_neg hT₂ ⟨ε, hε, hballU⟩ hneg
      · right
        have hS₂neg : ω (P - V) (S₂ - V) < 0 := by
          rcases lt_or_gt_of_ne hS₂ with h1 | h1
          · exact h1
          · exact absurd hsign (not_lt.mpr (mul_nonneg (le_of_lt hS₁pos) (le_of_lt h1)))
        have hT₁ : convexHull ℝ {V, S₁, P} ⊆ {y : Plane | (0:ℝ) ≤ ω (P - V) (y - V)} := by
          apply convexHull_min _ (convex_ω_ge (P - V) V 0)
          intro y hy
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
          rcases hy with rfl | rfl | rfl
          · simp only [Set.mem_setOf_eq, sub_self, ω_zero_right, le_refl]
          · exact le_of_lt hS₁pos
          · simp only [Set.mem_setOf_eq, ω_self, le_refl]
        exact mem_interior_of_union_of_neg hT₁ ⟨ε, hε, fun y hy ↦ (hballU y hy).symm⟩ hneg
    rcases hcase with h1 | h2
    · exact Set.mem_union_left _ (Set.mem_union_left _ h1)
    · exact Set.mem_union_left _ (Set.mem_union_right _ h2)
  · -- `x` on the diagonal: it lies on the segment `VP`, strictly between the endpoints
    refine Set.mem_union_right _ ?_
    have hseg : x ∈ segment ℝ V P := by
      rcases hxU with hx1 | hx2
      · exact mem_segment_of_mem_hull_triangle_ω_eq_zero h.ne₁₂ h.ne₁₃ h.ne₂₃ hS₁ hx1 hzero
      · have hset : ({V, P, S₂} : Set Plane) = {V, S₂, P} := by
          ext y
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          tauto
        exact mem_segment_of_mem_hull_triangle_ω_eq_zero h.ne₄₁.symm h.ne₁₃ h.ne₃₄.symm hS₂
          (hset ▸ hx2) hzero
    have hxV : x ≠ V := by
      intro h0
      rw [h0] at hx
      exact not_mem_interior_convexHull_insert
        ⟨S₁, subset_convexHull ℝ _ (Set.mem_insert _ _)⟩ h.not_mem₁ hx
    have hxP : x ≠ P := by
      intro h0
      rw [h0] at hx
      have hset : insert P {V, S₁, S₂} = ({V, S₁, P, S₂} : Set Plane) := by
        ext y
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        tauto
      rw [← hset] at hx
      have hnot : P ∉ convexHull ℝ {V, S₁, S₂} := by
        have hset2 : ({S₂, V, S₁} : Set Plane) = {V, S₁, S₂} := by
          ext y
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          tauto
        rw [← hset2]
        exact h.not_mem₃
      exact not_mem_interior_convexHull_insert
        ⟨V, subset_convexHull ℝ _ (Set.mem_insert _ _)⟩ hnot hx
    have hseg' : x ∈ affineSegment ℝ V P := (affineSegment_eq_segment ℝ V P).symm ▸ hseg
    exact ⟨hseg', hxV, hxP⟩
  · -- `x` strictly on the positive side: interior to the triangle on that side
    have hcase : x ∈ interior (convexHull ℝ {V, S₁, P}) ∨
        x ∈ interior (convexHull ℝ {V, P, S₂}) := by
      rcases lt_or_gt_of_ne hS₁ with hS₁neg | hS₁pos
      · right
        have hS₂pos : 0 < ω (P - V) (S₂ - V) := by
          rcases lt_or_gt_of_ne hS₂ with h1 | h1
          · exact absurd hsign (not_lt.mpr
              (mul_nonneg_of_nonpos_of_nonpos (le_of_lt hS₁neg) (le_of_lt h1)))
          · exact h1
        have hT₁ : convexHull ℝ {V, S₁, P} ⊆ {y : Plane | ω (P - V) (y - V) ≤ 0} := by
          apply convexHull_min _ (convex_ω_le (P - V) V 0)
          intro y hy
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
          rcases hy with rfl | rfl | rfl
          · simp only [Set.mem_setOf_eq, sub_self, ω_zero_right, le_refl]
          · exact le_of_lt hS₁neg
          · simp only [Set.mem_setOf_eq, ω_self, le_refl]
        exact mem_interior_of_union_of_pos hT₁ ⟨ε, hε, fun y hy ↦ (hballU y hy).symm⟩ hpos
      · left
        have hS₂neg : ω (P - V) (S₂ - V) < 0 := by
          rcases lt_or_gt_of_ne hS₂ with h1 | h1
          · exact h1
          · exact absurd hsign (not_lt.mpr (mul_nonneg (le_of_lt hS₁pos) (le_of_lt h1)))
        have hT₂ : convexHull ℝ {V, P, S₂} ⊆ {y : Plane | ω (P - V) (y - V) ≤ 0} := by
          apply convexHull_min _ (convex_ω_le (P - V) V 0)
          intro y hy
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
          rcases hy with rfl | rfl | rfl
          · simp only [Set.mem_setOf_eq, sub_self, ω_zero_right, le_refl]
          · simp only [Set.mem_setOf_eq, ω_self, le_refl]
          · exact le_of_lt hS₂neg
        exact mem_interior_of_union_of_pos hT₂ ⟨ε, hε, hballU⟩ hpos
    rcases hcase with h1 | h2
    · exact Set.mem_union_left _ (Set.mem_union_left _ h1)
    · exact Set.mem_union_left _ (Set.mem_union_right _ h2)

/-- Four cospherical points in strictly convex position form a cyclic quadrilateral. -/
theorem cyclicQuad_of_cospherical {W X Y Z : Plane} (hconv : ConvexQuad W X Y Z)
    (hcyc : Cospherical ({W, X, Y, Z} : Set Plane)) : CyclicQuad W X Y Z := by
  obtain ⟨sp, hsp⟩ := cospherical_iff_exists_sphere.mp hcyc
  have hW : dist W sp.center = sp.radius :=
    mem_sphere.mp (Sphere.mem_coe.mp (hsp (Set.mem_insert _ _)))
  have hX : dist X sp.center = sp.radius :=
    mem_sphere.mp (Sphere.mem_coe.mp (hsp (Set.mem_insert_of_mem _ (Set.mem_insert _ _))))
  have hY : dist Y sp.center = sp.radius :=
    mem_sphere.mp (Sphere.mem_coe.mp (hsp (Set.mem_insert_of_mem _
      (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))))
  have hZ : dist Z sp.center = sp.radius :=
    mem_sphere.mp (Sphere.mem_coe.mp (hsp (Set.mem_insert_of_mem _
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))))))
  exact ⟨hconv, sp.center, sp.radius, hW, hX, hY, hZ⟩

set_option maxHeartbeats 2400000 in
theorem disjoint_four_pieces {A B C D K L M N P : Plane}
    (hd01 : Disjoint (interior (quadRegion K P N A)) (interior (quadRegion B K P L)))
    (hd02 : Disjoint (interior (quadRegion K P N A)) (interior (quadRegion C L P M)))
    (hd03 : Disjoint (interior (quadRegion K P N A)) (interior (quadRegion D N P M)))
    (hd12 : Disjoint (interior (quadRegion B K P L)) (interior (quadRegion C L P M)))
    (hd23 : Disjoint (interior (quadRegion C L P M)) (interior (quadRegion D N P M)))
    (hd13 : Disjoint (interior (quadRegion B K P L)) (interior (quadRegion D N P M))) :
    ∀ i j : Fin 4, i ≠ j →
      Disjoint (interior (quadRegion (![(K, P, N, A), (B, K, P, L), (C, L, P, M), (D, N, P, M)] i).1 (![(K, P, N, A), (B, K, P, L), (C, L, P, M), (D, N, P, M)] i).2.1 (![(K, P, N, A), (B, K, P, L), (C, L, P, M), (D, N, P, M)] i).2.2.1 (![(K, P, N, A), (B, K, P, L), (C, L, P, M), (D, N, P, M)] i).2.2.2))
        (interior (quadRegion (![(K, P, N, A), (B, K, P, L), (C, L, P, M), (D, N, P, M)] j).1 (![(K, P, N, A), (B, K, P, L), (C, L, P, M), (D, N, P, M)] j).2.1 (![(K, P, N, A), (B, K, P, L), (C, L, P, M), (D, N, P, M)] j).2.2.1 (![(K, P, N, A), (B, K, P, L), (C, L, P, M), (D, N, P, M)] j).2.2.2)) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact hd01
  · exact hd02
  · exact hd03
  · exact hd01.symm
  · exact absurd rfl hij
  · exact hd12
  · exact hd13
  · exact hd02.symm
  · exact hd12.symm
  · exact absurd rfl hij
  · exact hd23
  · exact hd03.symm
  · exact hd13.symm
  · exact hd23.symm
  · exact absurd rfl hij

set_option maxHeartbeats 2400000 in
theorem cover_four_pieces {A B C D K L M N P : Plane} (h : ConvexQuad A B C D)
    (hPseg : P ∈ segment ℝ B D) (hKseg : K ∈ segment ℝ A B) (hLseg : L ∈ segment ℝ B C)
    (hMseg : M ∈ segment ℝ C D) (hNseg : N ∈ segment ℝ D A) (hKseg' : K ∈ segment ℝ B A)
    (hNseg' : N ∈ segment ℝ A D)
    (hAB : A ≠ B) (hBC : B ≠ C) (hCD : C ≠ D) (hDA : D ≠ A) (hBD : B ≠ D)
    (hPb : Sbtw ℝ B P D) (hPA : P ≠ A) (hPC : P ≠ C)
    (hmonoLBP : convexHull ℝ ({L, B, P} : Set Plane) ⊆ convexHull ℝ ({B, K, P, L} : Set Plane))
    (hmonoLPC : convexHull ℝ ({L, P, C} : Set Plane) ⊆ convexHull ℝ ({C, L, P, M} : Set Plane))
    (hmonoMCP : convexHull ℝ ({M, C, P} : Set Plane) ⊆ convexHull ℝ ({C, L, P, M} : Set Plane))
    (hmonoMPD : convexHull ℝ ({M, P, D} : Set Plane) ⊆ convexHull ℝ ({D, N, P, M} : Set Plane))
    (hmonoKBP : convexHull ℝ ({K, B, P} : Set Plane) ⊆ convexHull ℝ ({B, K, P, L} : Set Plane))
    (hmonoKPA : convexHull ℝ ({K, P, A} : Set Plane) ⊆ convexHull ℝ ({K, P, N, A} : Set Plane))
    (hmonoNAP : convexHull ℝ ({N, A, P} : Set Plane) ⊆ convexHull ℝ ({K, P, N, A} : Set Plane))
    (hmonoNPD : convexHull ℝ ({N, P, D} : Set Plane) ⊆ convexHull ℝ ({D, N, P, M} : Set Plane)) :
    quadRegion A B C D ⊆ ⋃ i, quadRegion (![(K, P, N, A), (B, K, P, L), (C, L, P, M), (D, N, P, M)] i).1
      (![(K, P, N, A), (B, K, P, L), (C, L, P, M), (D, N, P, M)] i).2.1
      (![(K, P, N, A), (B, K, P, L), (C, L, P, M), (D, N, P, M)] i).2.2.1
      (![(K, P, N, A), (B, K, P, L), (C, L, P, M), (D, N, P, M)] i).2.2.2 := by
    intro x hx
    have hx' : x ∈ convexHull ℝ ({A, B, C, D} : Set Plane) := hx
    have hrot : ConvexQuad B C D A :=
      ⟨h.not_mem₂, h.not_mem₃, h.not_mem₄, h.not_mem₁, by
        obtain ⟨X, hX1, hX2⟩ := h.diagonals
        exact ⟨X, hX2, hX1.symm⟩⟩
    have hset1 : ({A, B, C, D} : Set Plane) = {B, C, D, A} := by
      ext y
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [hset1] at hx'
    rcases convexHull_quad_subset_union_triangle hrot hx' with hxT | hxT
    · -- `x ∈ hull {B, C, D}`: split by `P ∈ segment B D`
      rcases triangle_split_of_mem_segment hPseg hBC hBD hCD hxT with hxT | hxT
      · -- `x ∈ hull {P, B, C}`: split by `L ∈ segment B C`
        have hset : ({P, B, C} : Set Plane) = {B, P, C} := by
          ext y
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          tauto
        rw [hset] at hxT
        rcases triangle_split_of_mem_segment hLseg hPb.2.1.symm hBC hPC hxT with hxT | hxT
        · exact Set.mem_iUnion.mpr ⟨1, hmonoLBP hxT⟩
        · exact Set.mem_iUnion.mpr ⟨2, hmonoLPC hxT⟩
      · -- `x ∈ hull {P, C, D}`: split by `M ∈ segment C D`
        have hset : ({P, C, D} : Set Plane) = {C, P, D} := by
          ext y
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          tauto
        rw [hset] at hxT
        rcases triangle_split_of_mem_segment hMseg hPC.symm hCD hPb.2.2 hxT with hxT | hxT
        · exact Set.mem_iUnion.mpr ⟨2, hmonoMCP hxT⟩
        · exact Set.mem_iUnion.mpr ⟨3, hmonoMPD hxT⟩
    · -- `x ∈ hull {B, D, A}`: split by `P ∈ segment B D`
      have hset : ({B, D, A} : Set Plane) = {B, A, D} := by
        ext y
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        tauto
      rw [hset] at hxT
      rcases triangle_split_of_mem_segment hPseg hAB.symm hBD hDA.symm hxT with hxT | hxT
      · -- `x ∈ hull {P, B, A}`: split by `K ∈ segment B A`
        have hset2 : ({P, B, A} : Set Plane) = {B, P, A} := by
          ext y
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          tauto
        rw [hset2] at hxT
        rcases triangle_split_of_mem_segment hKseg' hPb.2.1.symm hAB.symm hPA hxT
          with hxT | hxT
        · exact Set.mem_iUnion.mpr ⟨1, hmonoKBP hxT⟩
        · exact Set.mem_iUnion.mpr ⟨0, hmonoKPA hxT⟩
      · -- `x ∈ hull {P, A, D}`: split by `N ∈ segment A D`
        have hset2 : ({P, A, D} : Set Plane) = {A, P, D} := by
          ext y
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          tauto
        rw [hset2] at hxT
        rcases triangle_split_of_mem_segment hNseg' hPA.symm hDA.symm hPb.2.2 hxT
          with hxT | hxT
        · exact Set.mem_iUnion.mpr ⟨0, hmonoNAP hxT⟩
        · exact Set.mem_iUnion.mpr ⟨3, hmonoNPD hxT⟩

set_option maxHeartbeats 2400000 in
theorem disjoint_KPNA_BKPL {A B K L N P : Plane} {s w1 w1c : ℝ} (hKPne : K ≠ P) (hw1 : w1 ≠ 0)
    (hfB_KP : ω (P - K) (B - K) = ((1 - s) * (1 - s)) * w1)
    (hfL_KP : ω (P - K) (L - K) = ((1 - s) * (1 - s)) * w1c)
    (hfN_KP : ω (P - K) (N - K) = -(s * (1 - s)) * w1)
    (hfA_KP : ω (P - K) (A - K) = -(s * (1 - s)) * w1)
    (hs0 : 0 < s) (hs1' : 0 < 1 - s) (hw1w1c : 0 < w1 * w1c) :
    Disjoint (interior (quadRegion K P N A)) (interior (quadRegion B K P L)) :=
    (disjoint_of_common_sign_line (s := ({B, K, P, L} : Set Plane))
      (t := ({K, P, N, A} : Set Plane)) hKPne hw1
      (fun y hy ↦ by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl | rfl | rfl
        · rw [hfB_KP, mul_assoc]
          exact mul_nonneg (mul_nonneg hs1'.le hs1'.le) (mul_self_nonneg w1)
        · simp only [sub_self, ω_zero_right, zero_mul, le_refl]
        · simp only [ω_self, zero_mul, le_refl]
        · rw [hfL_KP, mul_assoc, mul_comm w1c w1]
          exact mul_nonneg (mul_nonneg hs1'.le hs1'.le) hw1w1c.le)
      (fun y hy ↦ by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl | rfl | rfl
        · simp only [sub_self, ω_zero_right, zero_mul, le_refl]
        · simp only [ω_self, zero_mul, le_refl]
        · rw [hfN_KP, mul_assoc]
          exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (mul_nonneg hs0.le hs1'.le))
            (mul_self_nonneg w1)
        · rw [hfA_KP, mul_assoc]
          exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (mul_nonneg hs0.le hs1'.le))
            (mul_self_nonneg w1))).symm


set_option maxHeartbeats 2400000 in
theorem disjoint_KPNA_CLPM {A B C D K L M N P : Plane} {s tN tM w3 w4 : ℝ} (hBD : B ≠ D) (hw3 : w3 ≠ 0)
    (hfK_BD : ω (D - B) (K - B) = (1 - s) * w3)
    (hfP_BD : ω (D - B) (P - B) = 0)
    (hfN_BD : ω (D - B) (N - B) = tN * w3)
    (hfA_BD : ω (D - B) (A - B) = w3)
    (hfC_BD : ω (D - B) (C - B) = w4)
    (hfL_BD : ω (D - B) (L - B) = (1 - s) * w4)
    (hfM_BD : ω (D - B) (M - B) = (1 - tM) * w4)
    (hs1' : 0 < 1 - s) (htN0 : 0 < tN) (htM1' : 0 < 1 - tM) (hw3w4 : w3 * w4 < 0) :
    Disjoint (interior (quadRegion K P N A)) (interior (quadRegion C L P M)) :=
    disjoint_of_common_sign_line (s := ({K, P, N, A} : Set Plane))
      (t := ({C, L, P, M} : Set Plane)) hBD hw3
      (fun y hy ↦ by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl | rfl | rfl
        · rw [hfK_BD, mul_assoc]
          exact mul_nonneg hs1'.le (mul_self_nonneg w3)
        · simp only [hfP_BD, zero_mul, le_refl]
        · rw [hfN_BD, mul_assoc]
          exact mul_nonneg htN0.le (mul_self_nonneg w3)
        · rw [hfA_BD]
          exact mul_self_nonneg w3)
      (fun y hy ↦ by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl | rfl | rfl
        · rw [hfC_BD, mul_comm]
          exact hw3w4.le
        · rw [hfL_BD, mul_assoc, mul_comm w4 w3]
          exact mul_nonpos_of_nonneg_of_nonpos hs1'.le hw3w4.le
        · simp only [hfP_BD, zero_mul, le_refl]
        · rw [hfM_BD, mul_assoc, mul_comm w4 w3]
          exact mul_nonpos_of_nonneg_of_nonpos htM1'.le hw3w4.le)


set_option maxHeartbeats 2400000 in
theorem disjoint_KPNA_DNPM {A D K M N P : Plane} {s tN w6 : ℝ} (hNPne : N ≠ P) (hw6 : w6 ≠ 0)
    (hfK_PN : ω (P - N) (K - N) = (s * (1 - s)) * w6)
    (hfA_PN : ω (P - N) (A - N) = (s * (1 - tN)) * w6)
    (hfD_PN : ω (P - N) (D - N) = -(s * tN) * w6)
    (hs0 : 0 < s) (hs1' : 0 < 1 - s) (htN0 : 0 < tN) (htN1' : 0 < 1 - tN)
    (hsideD_PN : (0:ℝ) < ω (P - N) (D - N) * ω (P - N) (M - N)) :
    Disjoint (interior (quadRegion K P N A)) (interior (quadRegion D N P M)) :=
    disjoint_of_common_sign_line (s := ({K, P, N, A} : Set Plane))
      (t := ({D, N, P, M} : Set Plane)) hNPne hw6
      (fun y hy ↦ by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl | rfl | rfl
        · rw [hfK_PN, mul_assoc]
          exact mul_nonneg (mul_nonneg hs0.le hs1'.le) (mul_self_nonneg w6)
        · simp only [ω_self, zero_mul, le_refl]
        · simp only [sub_self, ω_zero_right, zero_mul, le_refl]
        · rw [hfA_PN, mul_assoc]
          exact mul_nonneg (mul_pos hs0 htN1').le (mul_self_nonneg w6))
      (fun y hy ↦ by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl | rfl | hy4
        · rw [hfD_PN, mul_assoc]
          exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (mul_pos hs0 htN0).le)
            (mul_self_nonneg w6)
        · simp only [sub_self, ω_zero_right, zero_mul, le_refl]
        · simp only [ω_self, zero_mul, le_refl]
        · -- `M` is on `D`'s side of the line `PN` by the side-sign product
          rw [hy4]
          have h1 : (0:ℝ) < -(s * tN) * w6 * ω (P - N) (M - N) := by
            rw [← hfD_PN]
            exact hsideD_PN
          have h2 : (0:ℝ) < s * tN := mul_pos hs0 htN0
          have h3 : ω (P - N) (M - N) * w6 < 0 := by
            by_contra hcon
            push_neg at hcon
            have h4 : -(s * tN) * (ω (P - N) (M - N) * w6) ≤ 0 :=
              mul_nonpos_of_nonpos_of_nonneg (by linarith only [h2]) hcon
            have h5 : -(s * tN) * w6 * ω (P - N) (M - N) =
                -(s * tN) * (ω (P - N) (M - N) * w6) := by ring
            rw [h5] at h1
            linarith only [h1, h4]
          exact le_of_lt h3)


set_option maxHeartbeats 2400000 in
theorem disjoint_BKPL_CLPM {B C K L M P : Plane} {s w2 w2a : ℝ} (hLPne : L ≠ P) (hw2 : w2 ≠ 0)
    (hfB_PL : ω (P - L) (B - L) = ((1 - s) * (1 - s)) * w2)
    (hfK_PL : ω (P - L) (K - L) = ((1 - s) * (1 - s)) * w2a)
    (hfC_PL : ω (P - L) (C - L) = -(s * (1 - s)) * w2)
    (hfM_PL : ω (P - L) (M - L) = -(s * (1 - s)) * w2)
    (hs0 : 0 < s) (hs1' : 0 < 1 - s) (hw2w2a : 0 < w2a * w2) :
    Disjoint (interior (quadRegion B K P L)) (interior (quadRegion C L P M)) :=
    disjoint_of_common_sign_line (s := ({B, K, P, L} : Set Plane))
      (t := ({C, L, P, M} : Set Plane)) hLPne hw2
      (fun y hy ↦ by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl | rfl | rfl
        · rw [hfB_PL, mul_assoc]
          exact mul_nonneg (mul_nonneg hs1'.le hs1'.le) (mul_self_nonneg w2)
        · rw [hfK_PL, mul_assoc]
          exact mul_nonneg (mul_nonneg hs1'.le hs1'.le) hw2w2a.le
        · simp only [ω_self, zero_mul, le_refl]
        · simp only [sub_self, ω_zero_right, zero_mul, le_refl])
      (fun y hy ↦ by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl | rfl | rfl
        · rw [hfC_PL, mul_assoc]
          exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (mul_nonneg hs0.le hs1'.le))
            (mul_self_nonneg w2)
        · simp only [sub_self, ω_zero_right, zero_mul, le_refl]
        · simp only [ω_self, zero_mul, le_refl]
        · rw [hfM_PL, mul_assoc]
          exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (mul_nonneg hs0.le hs1'.le))
            (mul_self_nonneg w2))


set_option maxHeartbeats 2400000 in
theorem disjoint_CLPM_DNPM {C D L M N P : Plane} {s tM w5 : ℝ} (hMPne : M ≠ P) (hw5 : w5 ≠ 0)
    (hfC_PM : ω (P - M) (C - M) = (s * tM) * w5)
    (hfL_PM : ω (P - M) (L - M) = (s * (1 - s)) * w5)
    (hfD_PM : ω (P - M) (D - M) = -(s * (1 - tM)) * w5)
    (hs0 : 0 < s) (hs1' : 0 < 1 - s) (htM0 : 0 < tM) (htM1' : 0 < 1 - tM)
    (hsideD_PM : (0:ℝ) < ω (P - M) (D - M) * ω (P - M) (N - M)) :
    Disjoint (interior (quadRegion C L P M)) (interior (quadRegion D N P M)) :=
    disjoint_of_common_sign_line (s := ({C, L, P, M} : Set Plane))
      (t := ({D, N, P, M} : Set Plane)) hMPne hw5
      (fun y hy ↦ by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl | rfl | rfl
        · rw [hfC_PM, mul_assoc]
          exact mul_nonneg (mul_nonneg hs0.le htM0.le) (mul_self_nonneg w5)
        · rw [hfL_PM, mul_assoc]
          exact mul_nonneg (mul_nonneg hs0.le hs1'.le) (mul_self_nonneg w5)
        · simp only [ω_self, zero_mul, le_refl]
        · simp only [sub_self, ω_zero_right, zero_mul, le_refl])
      (fun y hy ↦ by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | hy2 | rfl | rfl
        · rw [hfD_PM, mul_assoc]
          exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (mul_pos hs0 htM1').le)
            (mul_self_nonneg w5)
        · -- `N` is on `D`'s side of the line `PM` by the side-sign product
          rw [hy2]
          have h1 : (0:ℝ) < -(s * (1 - tM)) * w5 * ω (P - M) (N - M) := by
            rw [← hfD_PM]
            exact hsideD_PM
          have h2 : (0:ℝ) < s * (1 - tM) := mul_pos hs0 htM1'
          have h3 : ω (P - M) (N - M) * w5 < 0 := by
            by_contra hcon
            push_neg at hcon
            have h4 : -(s * (1 - tM)) * (ω (P - M) (N - M) * w5) ≤ 0 :=
              mul_nonpos_of_nonpos_of_nonneg (by linarith only [h2]) hcon
            have h5 : -(s * (1 - tM)) * w5 * ω (P - M) (N - M) =
                -(s * (1 - tM)) * (ω (P - M) (N - M) * w5) := by ring
            rw [h5] at h1
            linarith only [h1, h4]
          exact le_of_lt h3
        · simp only [ω_self, zero_mul, le_refl]
        · simp only [sub_self, ω_zero_right, zero_mul, le_refl])


set_option maxHeartbeats 2400000 in
theorem disjoint_BKP_DNM {B D P K L M N : Plane} {s tM tN w1 w2 w3 w4 : ℝ}
    (hBD : B ≠ D) (hconvB : ConvexQuad B K P L) (hconvD : ConvexQuad D N P M)
    (hKPne : K ≠ P) (hLPne : L ≠ P)
    (hw1 : w1 ≠ 0) (hw2 : w2 ≠ 0) (hw3 : w3 ≠ 0) (hw4 : w4 ≠ 0)
    (hw3w4 : w3 * w4 < 0)
    (hfB_KP : ω (P - K) (B - K) = ((1 - s) * (1 - s)) * w1)
    (hfD_KP : ω (P - K) (D - K) = -(s * (1 - s)) * w1)
    (hfN_KP : ω (P - K) (N - K) = -(s * (1 - s)) * w1)
    (hfB_PL : ω (P - L) (B - L) = ((1 - s) * (1 - s)) * w2)
    (hfD_PL : ω (P - L) (D - L) = -(s * (1 - s)) * w2)
    (hfM_PL : ω (P - L) (M - L) = -(s * (1 - s)) * w2)
    (hfK_BD : ω (D - B) (K - B) = (1 - s) * w3)
    (hfN_BD : ω (D - B) (N - B) = tN * w3)
    (hfL_BD : ω (D - B) (L - B) = (1 - s) * w4)
    (hfM_BD : ω (D - B) (M - B) = (1 - tM) * w4)
    (hfP_BD : ω (D - B) (P - B) = 0)
    (hvPB : P - B = (1 - s) • (D - B))
    (hs0 : 0 < s) (hs1' : 0 < 1 - s) (htN0 : 0 < tN) (htM1' : 0 < 1 - tM)
    (hPdef : P = AffineMap.lineMap B D (1 - s)) :
    Disjoint (interior (quadRegion B K P L)) (interior (quadRegion D N P M)) := by
    have hBD' : D - B ≠ 0 := sub_ne_zero.mpr hBD.symm
    have hdecB : ∀ {x : Plane}, x ∈ interior (convexHull ℝ ({B, K, P, L} : Set Plane)) →
        x ∈ interior (convexHull ℝ ({B, K, P} : Set Plane)) ∪
          interior (convexHull ℝ ({B, P, L} : Set Plane)) ∪
          {X : Plane | Sbtw ℝ B X P} :=
      fun {x} hx ↦ interior_convexHull_quad_subset_union hconvB hx
    have hdecD : ∀ {x : Plane}, x ∈ interior (convexHull ℝ ({D, N, P, M} : Set Plane)) →
        x ∈ interior (convexHull ℝ ({D, N, P} : Set Plane)) ∪
          interior (convexHull ℝ ({D, P, M} : Set Plane)) ∪
          {X : Plane | Sbtw ℝ D X P} :=
      fun {x} hx ↦ interior_convexHull_quad_subset_union hconvD hx
    have hsub1 : Disjoint (interior (convexHull ℝ ({B, K, P} : Set Plane)))
        (interior (convexHull ℝ ({D, N, P} : Set Plane))) :=
      disjoint_of_common_sign_line (s := ({B, K, P} : Set Plane))
        (t := ({D, N, P} : Set Plane)) hKPne hw1
        (fun y hy ↦ by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
          rcases hy with rfl | rfl | rfl
          · rw [hfB_KP, mul_assoc]
            exact mul_nonneg (mul_nonneg hs1'.le hs1'.le) (mul_self_nonneg w1)
          · simp only [sub_self, ω_zero_right, zero_mul, le_refl]
          · simp only [ω_self, zero_mul, le_refl])
        (fun y hy ↦ by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
          rcases hy with rfl | rfl | rfl
          · rw [hfD_KP, mul_assoc]
            exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (mul_nonneg hs0.le hs1'.le))
              (mul_self_nonneg w1)
          · rw [hfN_KP, mul_assoc]
            exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (mul_nonneg hs0.le hs1'.le))
              (mul_self_nonneg w1)
          · simp only [ω_self, zero_mul, le_refl])
    have hsub2 : Disjoint (interior (convexHull ℝ ({B, P, L} : Set Plane)))
        (interior (convexHull ℝ ({D, P, M} : Set Plane))) :=
      disjoint_of_common_sign_line (s := ({B, P, L} : Set Plane))
        (t := ({D, P, M} : Set Plane)) hLPne hw2
        (fun y hy ↦ by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
          rcases hy with rfl | rfl | rfl
          · rw [hfB_PL, mul_assoc]
            exact mul_nonneg (mul_nonneg hs1'.le hs1'.le) (mul_self_nonneg w2)
          · simp only [ω_self, zero_mul, le_refl]
          · simp only [sub_self, ω_zero_right, zero_mul, le_refl])
        (fun y hy ↦ by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
          rcases hy with rfl | rfl | rfl
          · rw [hfD_PL, mul_assoc]
            exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (mul_nonneg hs0.le hs1'.le))
              (mul_self_nonneg w2)
          · simp only [ω_self, zero_mul, le_refl]
          · rw [hfM_PL, mul_assoc]
            exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (mul_nonneg hs0.le hs1'.le))
              (mul_self_nonneg w2))
    have hTBKP : ∀ y ∈ interior (convexHull ℝ ({B, K, P} : Set Plane)),
        (0:ℝ) < ω (D - B) (y - B) * w3 := by
      intro y hy
      rcases lt_or_gt_of_ne hw3 with hw3neg | hw3pos
      · have hT : convexHull ℝ ({B, K, P} : Set Plane) ⊆
            {z : Plane | ω (D - B) (z - B) ≤ 0} := by
          apply convexHull_min _ (convex_ω_le (D - B) B 0)
          intro z hz
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
          rcases hz with rfl | rfl | rfl
          · simp only [Set.mem_setOf_eq, sub_self, ω_zero_right, le_refl]
          · rw [Set.mem_setOf_eq, hfK_BD]
            exact mul_nonpos_of_nonneg_of_nonpos hs1'.le hw3neg.le
          · exact le_of_eq hfP_BD
        have h1 := mem_open_halfspace_le_of_mem_interior hBD' hT hy
        exact mul_pos_of_neg_of_neg h1 hw3neg
      · have hT : convexHull ℝ ({B, K, P} : Set Plane) ⊆
            {z : Plane | (0:ℝ) ≤ ω (D - B) (z - B)} := by
          apply convexHull_min _ (convex_ω_ge (D - B) B 0)
          intro z hz
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
          rcases hz with rfl | rfl | rfl
          · simp only [Set.mem_setOf_eq, sub_self, ω_zero_right, le_refl]
          · rw [Set.mem_setOf_eq, hfK_BD]
            exact mul_nonneg hs1'.le hw3pos.le
          · exact le_of_eq hfP_BD.symm
        have h1 := mem_open_halfspace_of_mem_interior hBD' hT hy
        exact mul_pos h1 hw3pos
    have hTDNP : ∀ y ∈ interior (convexHull ℝ ({D, N, P} : Set Plane)),
        (0:ℝ) < ω (D - B) (y - B) * w3 := by
      intro y hy
      rcases lt_or_gt_of_ne hw3 with hw3neg | hw3pos
      · have hT : convexHull ℝ ({D, N, P} : Set Plane) ⊆
            {z : Plane | ω (D - B) (z - B) ≤ 0} := by
          apply convexHull_min _ (convex_ω_le (D - B) B 0)
          intro z hz
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
          rcases hz with rfl | rfl | rfl
          · simp only [Set.mem_setOf_eq, ω_self, le_refl]
          · rw [Set.mem_setOf_eq, hfN_BD]
            exact mul_nonpos_of_nonneg_of_nonpos htN0.le hw3neg.le
          · exact le_of_eq hfP_BD
        have h1 := mem_open_halfspace_le_of_mem_interior hBD' hT hy
        exact mul_pos_of_neg_of_neg h1 hw3neg
      · have hT : convexHull ℝ ({D, N, P} : Set Plane) ⊆
            {z : Plane | (0:ℝ) ≤ ω (D - B) (z - B)} := by
          apply convexHull_min _ (convex_ω_ge (D - B) B 0)
          intro z hz
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
          rcases hz with rfl | rfl | rfl
          · simp only [Set.mem_setOf_eq, ω_self, le_refl]
          · rw [Set.mem_setOf_eq, hfN_BD]
            exact mul_nonneg htN0.le hw3pos.le
          · exact le_of_eq hfP_BD.symm
        have h1 := mem_open_halfspace_of_mem_interior hBD' hT hy
        exact mul_pos h1 hw3pos
    have hTBPL : ∀ y ∈ interior (convexHull ℝ ({B, P, L} : Set Plane)),
        (0:ℝ) < ω (D - B) (y - B) * w4 := by
      intro y hy
      rcases lt_or_gt_of_ne hw4 with hw4neg | hw4pos
      · have hT : convexHull ℝ ({B, P, L} : Set Plane) ⊆
            {z : Plane | ω (D - B) (z - B) ≤ 0} := by
          apply convexHull_min _ (convex_ω_le (D - B) B 0)
          intro z hz
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
          rcases hz with rfl | rfl | rfl
          · simp only [Set.mem_setOf_eq, sub_self, ω_zero_right, le_refl]
          · exact le_of_eq hfP_BD
          · rw [Set.mem_setOf_eq, hfL_BD]
            exact mul_nonpos_of_nonneg_of_nonpos hs1'.le hw4neg.le
        have h1 := mem_open_halfspace_le_of_mem_interior hBD' hT hy
        exact mul_pos_of_neg_of_neg h1 hw4neg
      · have hT : convexHull ℝ ({B, P, L} : Set Plane) ⊆
            {z : Plane | (0:ℝ) ≤ ω (D - B) (z - B)} := by
          apply convexHull_min _ (convex_ω_ge (D - B) B 0)
          intro z hz
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
          rcases hz with rfl | rfl | rfl
          · simp only [Set.mem_setOf_eq, sub_self, ω_zero_right, le_refl]
          · exact le_of_eq hfP_BD.symm
          · rw [Set.mem_setOf_eq, hfL_BD]
            exact mul_nonneg hs1'.le hw4pos.le
        have h1 := mem_open_halfspace_of_mem_interior hBD' hT hy
        exact mul_pos h1 hw4pos
    have hTDPM : ∀ y ∈ interior (convexHull ℝ ({D, P, M} : Set Plane)),
        (0:ℝ) < ω (D - B) (y - B) * w4 := by
      intro y hy
      rcases lt_or_gt_of_ne hw4 with hw4neg | hw4pos
      · have hT : convexHull ℝ ({D, P, M} : Set Plane) ⊆
            {z : Plane | ω (D - B) (z - B) ≤ 0} := by
          apply convexHull_min _ (convex_ω_le (D - B) B 0)
          intro z hz
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
          rcases hz with rfl | rfl | rfl
          · simp only [Set.mem_setOf_eq, ω_self, le_refl]
          · exact le_of_eq hfP_BD
          · rw [Set.mem_setOf_eq, hfM_BD]
            exact mul_nonpos_of_nonneg_of_nonpos htM1'.le hw4neg.le
        have h1 := mem_open_halfspace_le_of_mem_interior hBD' hT hy
        exact mul_pos_of_neg_of_neg h1 hw4neg
      · have hT : convexHull ℝ ({D, P, M} : Set Plane) ⊆
            {z : Plane | (0:ℝ) ≤ ω (D - B) (z - B)} := by
          apply convexHull_min _ (convex_ω_ge (D - B) B 0)
          intro z hz
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
          rcases hz with rfl | rfl | rfl
          · simp only [Set.mem_setOf_eq, ω_self, le_refl]
          · exact le_of_eq hfP_BD.symm
          · rw [Set.mem_setOf_eq, hfM_BD]
            exact mul_nonneg htM1'.le hw4pos.le
        have h1 := mem_open_halfspace_of_mem_interior hBD' hT hy
        exact mul_pos h1 hw4pos
    -- the two open diagonal subsegments lie on the line `BD`
    have hsegBP : ∀ y ∈ segment ℝ B P, ω (D - B) (y - B) = 0 := by
      intro y hy
      obtain ⟨a, b, ha, hb, hab, hy⟩ := hy
      rw [← hy]
      rw [show a • B + b • P - B = b • (P - B) by
        have hB : B = (a + b) • B := by rw [hab, one_smul]
        nth_rewrite 2 [hB]
        module]
      simp only [ω_smul_left, hvPB, ω_smul_right, ω_self, mul_zero]
    have hsegDP : ∀ y ∈ segment ℝ D P, ω (D - B) (y - B) = 0 := by
      intro y hy
      obtain ⟨a, b, ha, hb, hab, hy⟩ := hy
      rw [← hy]
      rw [show a • D + b • P - B = a • (D - B) + b • (P - B) by
        have hB : B = (a + b) • B := by rw [hab, one_smul]
        nth_rewrite 1 [hB]
        module]
      simp only [ω_add_right, ω_smul_right, ω_self, hvPB, mul_zero, add_zero]
    -- the two open subsegments `BP` and `DP` are disjoint
    have hsegdis : ∀ {y : Plane}, Sbtw ℝ B y P → Sbtw ℝ D y P → False := by
      intro y hy1 hy2
      obtain ⟨a₁, b₁, ha₁, hb₁, hab₁, hy₁⟩ := sbtw_combo hy1
      obtain ⟨a₂, b₂, ha₂, hb₂, hab₂, hy₂⟩ := sbtw_combo hy2
      have hPs : P = s • B + (1 - s) • D := by
        rw [hPdef, AffineMap.lineMap_apply_module]
        module
      have hb₁' : b₁ < 1 := by linarith only [hab₁, ha₁]
      have hb₂' : b₂ < 1 := by linarith only [hab₂, ha₂]
      have ha₁' : a₁ = 1 - b₁ := by linarith only [hab₁]
      have ha₂' : a₂ = 1 - b₂ := by linarith only [hab₂]
      rw [hPs] at hy₁ hy₂
      rw [ha₁'] at hy₁
      rw [ha₂'] at hy₂
      have e1 : y - B = (b₁ * (1 - s)) • (D - B) := by
        rw [← hy₁]
        module
      have e2 : y - B = (1 - b₂ * s) • (D - B) := by
        rw [← hy₂]
        module
      have huniq : b₁ * (1 - s) = 1 - b₂ * s := by
        have h1 : (b₁ * (1 - s) - (1 - b₂ * s)) • (D - B) = 0 := by
          rw [sub_smul, ← e1, ← e2, sub_self]
        rcases smul_eq_zero.mp h1 with h2 | h2
        · linarith only [h2]
        · exact absurd h2 hBD'
      have hlt1 : b₁ * (1 - s) < 1 - s := by
        have h1 := mul_lt_mul_of_pos_right hb₁' hs1'
        rw [one_mul] at h1
        exact h1
      have hlt2 : 1 - s < 1 - b₂ * s := by
        have h1 : b₂ * s < s := by
          have h2 := mul_lt_mul_of_pos_right hb₂' hs0
          rw [one_mul] at h2
          exact h2
        linarith only [h1]
      linarith only [huniq, hlt1, hlt2]
    -- assemble the nine intersections
    apply Set.disjoint_left.mpr
    intro x hxB hxD
    rcases hdecB hxB with (hxT1 | hxT2) | hxSB
    · rcases hdecD hxD with (hxU1 | hxU2) | hxSD
      · exact (Set.disjoint_left.mp hsub1 hxT1) hxU1
      · have h1 := hTBKP x hxT1
        have h2 := hTDPM x hxU2
        have h5 : ω (D - B) (x - B) * w3 * (ω (D - B) (x - B) * w4) =
            ω (D - B) (x - B) ^ 2 * (w3 * w4) := by ring
        have h6 : (0:ℝ) < ω (D - B) (x - B) ^ 2 * (w3 * w4) := by
          rw [← h5]
          exact mul_pos h1 h2
        exact absurd h6 (not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos
          (sq_nonneg (ω (D - B) (x - B))) hw3w4.le))
      · have h1 := hTBKP x hxT1
        have h2 := hsegDP x (affineSegment_eq_segment ℝ D P ▸ hxSD.1)
        rw [h2, zero_mul] at h1
        exact lt_irrefl 0 h1
    · rcases hdecD hxD with (hxU1 | hxU2) | hxSD
      · have h1 := hTBPL x hxT2
        have h2 := hTDNP x hxU1
        have h5 : ω (D - B) (x - B) * w4 * (ω (D - B) (x - B) * w3) =
            ω (D - B) (x - B) ^ 2 * (w3 * w4) := by ring
        have h6 : (0:ℝ) < ω (D - B) (x - B) ^ 2 * (w3 * w4) := by
          rw [← h5]
          exact mul_pos h1 h2
        exact absurd h6 (not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos
          (sq_nonneg (ω (D - B) (x - B))) hw3w4.le))
      · exact (Set.disjoint_left.mp hsub2 hxT2) hxU2
      · have h1 := hTBPL x hxT2
        have h2 := hsegDP x (affineSegment_eq_segment ℝ D P ▸ hxSD.1)
        rw [h2, zero_mul] at h1
        exact lt_irrefl 0 h1
    · rcases hdecD hxD with (hxU1 | hxU2) | hxSD
      · have h1 := hsegBP x (affineSegment_eq_segment ℝ B P ▸ hxSB.1)
        have h2 := hTDNP x hxU1
        rw [h1, zero_mul] at h2
        exact lt_irrefl 0 h2
      · have h1 := hsegBP x (affineSegment_eq_segment ℝ B P ▸ hxSB.1)
        have h2 := hTDPM x hxU2
        rw [h1, zero_mul] at h2
        exact lt_irrefl 0 h2
      · exact hsegdis hxSB hxSD

set_option maxHeartbeats 2400000 in
/-- **Base case, anchor form.**  If the diagonal `BD` is strictly longer than the two
sides adjacent to `B` (the "anchor at `A`"), the cyclic quadrilateral `ABCD` admits a
dissection into four cyclic quadrilaterals, one of which is an isosceles trapezoid
(the kalva construction at the anchor `A`). -/
theorem dissection_four_of_hdiag {A B C D : Plane} (h : CyclicQuad A B C D)
    (hdiag : dist B C < dist B D ∧ dist A B < dist B D) :
    DissectionWithTrapezoid A B C D 4 := by
  -- basic nondegeneracy and the two diagonal gaps
  have hAB : A ≠ B := h.convex.ne₁₂
  have hBC : B ≠ C := h.convex.ne₂₃
  have hCD : C ≠ D := h.convex.ne₃₄
  have hDA : D ≠ A := h.convex.ne₄₁
  have hBD : B ≠ D := h.convex.ne₂₄
  have hμ : 0 < dist B D ^ 2 - dist B C ^ 2 := by
    nlinarith [hdiag.1, @dist_nonneg _ _ B C, @dist_nonneg _ _ B D]
  have hκ : 0 < dist B D ^ 2 - dist A B ^ 2 := by
    nlinarith [hdiag.2, @dist_nonneg _ _ A B, @dist_nonneg _ _ B D]
  have hCD2 : 0 < dist C D ^ 2 := by
    have hd := dist_pos.mpr hCD
    nlinarith
  have hAD2 : 0 < dist A D ^ 2 := by
    have hd := dist_pos.mpr hDA.symm
    nlinarith
  -- the construction parameter `s`, small enough for both landing conditions
  set u₁ := dist C D ^ 2 / (dist B D ^ 2 - dist B C ^ 2) with hu₁
  set u₂ := dist A D ^ 2 / (dist B D ^ 2 - dist A B ^ 2) with hu₂
  have hu₁pos : 0 < u₁ := div_pos hCD2 hμ
  have hu₂pos : 0 < u₂ := div_pos hAD2 hκ
  set s := min 1 (min u₁ u₂) / 2 with hsdef
  have hs0 : 0 < s := by
    rw [hsdef]
    exact half_pos (lt_min zero_lt_one (lt_min hu₁pos hu₂pos))
  have hs1 : s < 1 := by
    rw [hsdef]
    have h1 : min 1 (min u₁ u₂) ≤ 1 := min_le_left 1 (min u₁ u₂)
    linarith [h1]
  have hsu₁ : s < u₁ := by
    rw [hsdef]
    have h1 : min 1 (min u₁ u₂) ≤ u₁ := le_trans (min_le_right 1 _) (min_le_left u₁ u₂)
    have h2 : 0 < min 1 (min u₁ u₂) := lt_min zero_lt_one (lt_min hu₁pos hu₂pos)
    linarith [h1, h2]
  have hsu₂ : s < u₂ := by
    rw [hsdef]
    have h1 : min 1 (min u₁ u₂) ≤ u₂ := le_trans (min_le_right 1 _) (min_le_right u₁ u₂)
    have h2 : 0 < min 1 (min u₁ u₂) := lt_min zero_lt_one (lt_min hu₁pos hu₂pos)
    linarith [h1, h2]
  have hboundM : s * (dist B D ^ 2 - dist B C ^ 2) < dist C D ^ 2 := by
    rw [hu₁] at hsu₁
    rw [lt_div_iff₀ hμ] at hsu₁
    exact hsu₁
  have hboundN : s * (dist B D ^ 2 - dist A B ^ 2) < dist A D ^ 2 := by
    rw [hu₂] at hsu₂
    rw [lt_div_iff₀ hκ] at hsu₂
    exact hsu₂
  clear_value u₁ u₂ s
  -- the kalva construction anchored at `A`
  obtain ⟨P, K, L, M, N, hKdef, hPdef, hLdef, hMdef, hNdef, hKb, hLb, hMb, hNb,
    hBKP, hCLP, hDMP, hAPN, c, hpar⟩ :=
    landing_anchor h.convex h.concyclic hdiag hs0 hs1 hboundM hboundN
  set tM := (dist C D ^ 2 - s * (dist B D ^ 2 - dist B C ^ 2)) / dist C D ^ 2 with htMdef
  set tN := s * (dist B D ^ 2 - dist A B ^ 2) / dist A D ^ 2 with htNdef
  have htM0 : 0 < tM := by
    rw [htMdef]
    exact div_pos (by nlinarith [hboundM]) hCD2
  have htM1 : tM < 1 := by
    rw [htMdef, div_lt_one hCD2]
    nlinarith [mul_pos hs0 hμ]
  have htN0 : 0 < tN := by
    rw [htNdef]
    exact div_pos (mul_pos hs0 hκ) hAD2
  have htN1 : tN < 1 := by
    rw [htNdef, div_lt_one hAD2]
    nlinarith [hboundN]
  clear_value tM tN
  have hs1' : (0:ℝ) < 1 - s := sub_pos.mpr hs1
  have hs1'' : (1:ℝ) - s ≠ 0 := hs1'.ne'
  have htM1' : (0:ℝ) < 1 - tM := sub_pos.mpr htM1
  have htN1' : (0:ℝ) < 1 - tN := sub_pos.mpr htN1
  -- the four pieces are strictly convex
  have hconvA : ConvexQuad A K P N :=
    convexQuad_A_piece h.convex hs0 hs1 htN0 htN1 hKdef hPdef hNdef hAPN
  have hconvB : ConvexQuad B K P L :=
    convexQuad_B_piece h.convex hs0 hs1 hKdef hPdef hLdef hBKP
  have hconvC : ConvexQuad C L P M :=
    convexQuad_C_piece h.convex hs0 hs1 htM0 htM1 hLdef hPdef hMdef hCLP
  have hconvD : ConvexQuad D N P M :=
    convexQuad_D_piece h.convex hs0 hs1 htN0 htN1 htM0 htM1 hNdef hPdef hMdef hDMP
  -- cyclicity of the four pieces (in the boundary orders used by the dissection)
  have hcy0 : Cospherical ({K, P, N, A} : Set Plane) :=
    Cospherical.subset (by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      tauto) hAPN
  have hcy1 : Cospherical ({B, K, P, L} : Set Plane) :=
    Cospherical.subset (by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      tauto) hBKP
  have hcy2 : Cospherical ({C, L, P, M} : Set Plane) :=
    Cospherical.subset (by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      tauto) hCLP
  have hcy3 : Cospherical ({D, N, P, M} : Set Plane) :=
    Cospherical.subset (by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      tauto) hDMP
  have hconvA' : ConvexQuad K P N A :=
    ⟨hconvA.not_mem₂, hconvA.not_mem₃, hconvA.not_mem₄, hconvA.not_mem₁, by
      obtain ⟨X, hX1, hX2⟩ := hconvA.diagonals
      exact ⟨X, hX2, hX1.symm⟩⟩
  have hcyc0 : CyclicQuad K P N A := cyclicQuad_of_cospherical hconvA' hcy0
  have hcyc1 : CyclicQuad B K P L := cyclicQuad_of_cospherical hconvB hcy1
  have hcyc2 : CyclicQuad C L P M := cyclicQuad_of_cospherical hconvC hcy2
  have hcyc3 : CyclicQuad D N P M := cyclicQuad_of_cospherical hconvD hcy3
  -- the trapezoid witness
  have hAN : A ≠ N := hNb.2.2.symm
  have hlegs : dist P N = dist K A := dist_eq_of_cospherical_parallel hAPN ⟨c, hpar⟩ hAN
  have htrap : IsoscelesTrapezoid K P N A := ⟨hconvA', ⟨c, hpar⟩, hlegs⟩
  -- vector forms of the construction points
  have hvKP : P - K = (1 - s) • (D - A) := by
    rw [hPdef, hKdef, AffineMap.lineMap_apply_module, AffineMap.lineMap_apply_module]
    module
  have hvBK : B - K = (1 - s) • (B - A) := by
    rw [hKdef, AffineMap.lineMap_apply_module]
    module
  have hvAK : A - K = s • (A - B) := by
    rw [hKdef, AffineMap.lineMap_apply_module]
    module
  have hvLK : L - K = (1 - s) • (C - A) := by
    rw [hLdef, hKdef, AffineMap.lineMap_apply_module, AffineMap.lineMap_apply_module]
    module
  have hvNK : N - K = (1 - tN) • (D - A) - s • (B - A) := by
    rw [hNdef, hKdef, AffineMap.lineMap_apply_module, AffineMap.lineMap_apply_module]
    module
  have hvDK : D - K = (D - A) - s • (B - A) := by
    rw [hKdef, AffineMap.lineMap_apply_module]
    module
  have hvPL : P - L = (1 - s) • (D - C) := by
    rw [hPdef, hLdef, AffineMap.lineMap_apply_module, AffineMap.lineMap_apply_module]
    module
  have hvBL : B - L = (1 - s) • (B - C) := by
    rw [hLdef, AffineMap.lineMap_apply_module]
    module
  have hvKL : K - L = (1 - s) • (A - C) := by
    rw [hKdef, hLdef, AffineMap.lineMap_apply_module, AffineMap.lineMap_apply_module]
    module
  have hvCL : C - L = s • (C - B) := by
    rw [hLdef, AffineMap.lineMap_apply_module]
    module
  have hvML : M - L = tM • (D - C) + s • (C - B) := by
    rw [hMdef, hLdef, AffineMap.lineMap_apply_module, AffineMap.lineMap_apply_module]
    module
  have hvDL : D - L = (D - C) + s • (C - B) := by
    rw [hLdef, AffineMap.lineMap_apply_module]
    module
  have hvPM : P - M = s • (B - D) + (1 - tM) • (D - C) := by
    rw [hPdef, hMdef, AffineMap.lineMap_apply_module, AffineMap.lineMap_apply_module]
    module
  have hvCM : C - M = tM • (C - D) := by
    rw [hMdef, AffineMap.lineMap_apply_module]
    module
  have hvLM : L - M = s • (B - C) + tM • (C - D) := by
    rw [hLdef, hMdef, AffineMap.lineMap_apply_module, AffineMap.lineMap_apply_module]
    module
  have hvDM : D - M = (1 - tM) • (D - C) := by
    rw [hMdef, AffineMap.lineMap_apply_module]
    module
  have hvPN : P - N = s • (B - D) - tN • (A - D) := by
    rw [hPdef, hNdef, AffineMap.lineMap_apply_module, AffineMap.lineMap_apply_module]
    module
  have hvDN : D - N = tN • (D - A) := by
    rw [hNdef, AffineMap.lineMap_apply_module]
    module
  have hvAN : A - N = (1 - tN) • (A - D) := by
    rw [hNdef, AffineMap.lineMap_apply_module]
    module
  have hvKN : K - N = s • (B - A) + (1 - tN) • (A - D) := by
    rw [hKdef, hNdef, AffineMap.lineMap_apply_module, AffineMap.lineMap_apply_module]
    module
  have hvKB : K - B = (1 - s) • (A - B) := by
    rw [hKdef, AffineMap.lineMap_apply_module]
    module
  have hvNB : N - B = (1 - tN) • (D - A) + (A - B) := by
    rw [hNdef, AffineMap.lineMap_apply_module]
    module
  have hvLB : L - B = (1 - s) • (C - B) := by
    rw [hLdef, AffineMap.lineMap_apply_module]
    module
  have hvMB : M - B = tM • (D - C) + (C - B) := by
    rw [hMdef, AffineMap.lineMap_apply_module]
    module
  have hvPB : P - B = (1 - s) • (D - B) := by
    rw [hPdef, AffineMap.lineMap_apply_module]
    module
  -- the oriented-area constants and their sign facts
  set w1 := ω (D - A) (B - A) with hw1def
  set w1c := ω (D - A) (C - A) with hw1cdef
  set w2 := ω (D - C) (B - C) with hw2def
  set w2a := ω (D - C) (A - C) with hw2adef
  set w3 := ω (D - B) (A - B) with hw3def
  set w4 := ω (D - B) (C - B) with hw4def
  set w5 := ω (B - D) (C - D) with hw5def
  set w6 := ω (B - D) (A - D) with hw6def
  have hw1 : w1 ≠ 0 := by
    rw [hw1def]
    have e : ω (D - A) (B - A) = ω (A - B) (D - B) := by
      simp only [ω, PiLp.sub_apply]; ring
    rw [e]
    exact h.convex.ω_ABD_ne
  have hw2 : w2 ≠ 0 := by
    rw [hw2def]
    have e : ω (D - C) (B - C) = -ω (B - C) (D - C) := by
      simp only [ω, PiLp.sub_apply]; ring
    rw [e]
    exact neg_ne_zero.mpr h.convex.ω_BCD_ne
  have hw3 : w3 ≠ 0 := by
    rw [hw3def]
    have e : ω (D - B) (A - B) = -ω (A - B) (D - B) := by
      simp only [ω, PiLp.sub_apply]; ring
    rw [e]
    exact neg_ne_zero.mpr h.convex.ω_ABD_ne
  have hw4 : w4 ≠ 0 := by
    rw [hw4def]
    have e : ω (D - B) (C - B) = ω (B - C) (D - C) := by
      simp only [ω, PiLp.sub_apply]; ring
    rw [e]
    exact h.convex.ω_BCD_ne
  have hw5 : w5 ≠ 0 := by
    rw [hw5def]
    have e : ω (B - D) (C - D) = -ω (B - C) (D - C) := by
      simp only [ω, PiLp.sub_apply]; ring
    rw [e]
    exact neg_ne_zero.mpr h.convex.ω_BCD_ne
  have hw6 : w6 ≠ 0 := by
    rw [hw6def]
    have e : ω (B - D) (A - D) = ω (A - B) (D - B) := by
      simp only [ω, PiLp.sub_apply]; ring
    rw [e]
    exact h.convex.ω_ABD_ne
  have hw1w1c : 0 < w1 * w1c := by
    have hss := h.convex.side_sign_DA
    have e1 : ω (A - D) (B - D) = -ω (D - A) (B - A) := by
      simp only [ω, PiLp.sub_apply]; ring
    have e2 : ω (A - D) (C - D) = -ω (D - A) (C - A) := by
      simp only [ω, PiLp.sub_apply]; ring
    rw [e1, e2, ← hw1def, ← hw1cdef, neg_mul_neg] at hss
    exact hss
  have hw2w2a : 0 < w2a * w2 := by
    have hss := h.convex.side_sign_CD
    rw [← hw2adef, ← hw2def] at hss
    exact hss
  have hw3w4 : w3 * w4 < 0 := by
    have hos := h.convex.opp_side_BD
    rw [← hw3def, ← hw4def] at hos
    exact hos
  -- the `ω`-values of the construction points against the separating lines
  have hfB_KP : ω (P - K) (B - K) = ((1 - s) * (1 - s)) * w1 := by
    rw [hvKP, hvBK, ω_smul_left, ω_smul_right, ← hw1def, mul_assoc]
  have hfL_KP : ω (P - K) (L - K) = ((1 - s) * (1 - s)) * w1c := by
    rw [hvKP, hvLK, ω_smul_left, ω_smul_right, ← hw1cdef, mul_assoc]
  have hfA_KP : ω (P - K) (A - K) = -(s * (1 - s)) * w1 := by
    rw [hvKP, hvAK, ω_smul_left, ω_smul_right, show A - B = -(B - A) by abel, ω_neg_right, ← hw1def]
    ring
  have hfN_KP : ω (P - K) (N - K) = -(s * (1 - s)) * w1 := by
    rw [hvKP, hvNK, ω_smul_left, ω_sub_right, ω_smul_right, ω_smul_right, ω_self, ← hw1def]
    ring
  have hfD_KP : ω (P - K) (D - K) = -(s * (1 - s)) * w1 := by
    rw [hvKP, hvDK, ω_smul_left, ω_sub_right, ω_self, ω_smul_right, ← hw1def]
    ring
  have hfB_PL : ω (P - L) (B - L) = ((1 - s) * (1 - s)) * w2 := by
    rw [hvPL, hvBL, ω_smul_left, ω_smul_right, ← hw2def, mul_assoc]
  have hfK_PL : ω (P - L) (K - L) = ((1 - s) * (1 - s)) * w2a := by
    rw [hvPL, hvKL, ω_smul_left, ω_smul_right, ← hw2adef, mul_assoc]
  have hfC_PL : ω (P - L) (C - L) = -(s * (1 - s)) * w2 := by
    rw [hvPL, hvCL, ω_smul_left, ω_smul_right, show C - B = -(B - C) by abel, ω_neg_right, ← hw2def]
    ring
  have hfM_PL : ω (P - L) (M - L) = -(s * (1 - s)) * w2 := by
    rw [hvPL, hvML, ω_smul_left, ω_add_right, ω_smul_right, ω_smul_right, ω_self, show C - B = -(B - C) by abel, ω_neg_right, ← hw2def]
    ring
  have hfD_PL : ω (P - L) (D - L) = -(s * (1 - s)) * w2 := by
    rw [hvPL, hvDL, ω_smul_left, ω_add_right, ω_self, ω_smul_right, show C - B = -(B - C) by abel, ω_neg_right, ← hw2def]
    ring
  have hfC_PM : ω (P - M) (C - M) = (s * tM) * w5 := by
    rw [hw5def, hvPM, hvCM]
    simp only [ω, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  have hfL_PM : ω (P - M) (L - M) = (s * (1 - s)) * w5 := by
    rw [hw5def, hvPM, hvLM]
    simp only [ω, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  have hfD_PM : ω (P - M) (D - M) = -(s * (1 - tM)) * w5 := by
    rw [hvPM, hvDM, ω_add_left, ω_smul_left, ω_smul_left, ω_smul_right, ω_smul_right, ω_self, show D - C = -(C - D) by abel, ω_neg_right, ← hw5def]
    ring
  have hfD_PN : ω (P - N) (D - N) = -(s * tN) * w6 := by
    rw [hw6def, hvPN, hvDN]
    simp only [ω, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  have hfA_PN : ω (P - N) (A - N) = (s * (1 - tN)) * w6 := by
    rw [hw6def, hvPN, hvAN]
    simp only [ω, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  have hfK_PN : ω (P - N) (K - N) = (s * (1 - s)) * w6 := by
    rw [hw6def, hvPN, hvKN]
    simp only [ω, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  have hfK_BD : ω (D - B) (K - B) = (1 - s) * w3 := by
    rw [hvKB, ω_smul_right, ← hw3def]
  have hfN_BD : ω (D - B) (N - B) = tN * w3 := by
    rw [hw3def, hvNB]
    simp only [ω, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  have hfL_BD : ω (D - B) (L - B) = (1 - s) * w4 := by
    rw [hvLB, ω_smul_right, ← hw4def]
  have hfM_BD : ω (D - B) (M - B) = (1 - tM) * w4 := by
    rw [hw4def, hvMB]
    simp only [ω, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  have hfP_BD : ω (D - B) (P - B) = 0 := by
    rw [hvPB, ω_smul_right, ω_self, mul_zero]
  have hfA_BD : ω (D - B) (A - B) = w3 := hw3def.symm
  have hfC_BD : ω (D - B) (C - B) = w4 := hw4def.symm
  clear_value w1 w1c w2 w2a w5 w6
  -- the separating lines are nondegenerate
  have hKPne : K ≠ P := by
    intro heq
    rw [heq, sub_self, ω_zero_left] at hfB_KP
    exact mul_ne_zero (mul_ne_zero hs1'' hs1'') hw1 hfB_KP.symm
  have hLPne : L ≠ P := by
    intro heq
    rw [heq, sub_self, ω_zero_left] at hfB_PL
    exact mul_ne_zero (mul_ne_zero hs1'' hs1'') hw2 hfB_PL.symm
  have hMPne : M ≠ P := by
    intro heq
    rw [heq, sub_self, ω_zero_left] at hfC_PM
    exact mul_ne_zero (mul_ne_zero hs0.ne' htM0.ne') hw5 hfC_PM.symm
  have hNPne : N ≠ P := by
    intro heq
    rw [heq, sub_self, ω_zero_left] at hfD_PN
    exact mul_ne_zero (neg_ne_zero.mpr (mul_ne_zero hs0.ne' htN0.ne')) hw6 hfD_PN.symm
  -- side-sign products transported to the `ω`-functionals of the lines `PM` and `PN`
  have hsideD_PM : (0:ℝ) < ω (P - M) (D - M) * ω (P - M) (N - M) := by
    have hss := hconvD.side_sign_CD
    have e1 : ω (M - P) (D - P) = -ω (P - M) (D - M) := by
      simp only [ω, PiLp.sub_apply]; ring
    have e2 : ω (M - P) (N - P) = -ω (P - M) (N - M) := by
      simp only [ω, PiLp.sub_apply]; ring
    rw [e1, e2, neg_mul_neg] at hss
    exact hss
  have hsideD_PN : (0:ℝ) < ω (P - N) (D - N) * ω (P - N) (M - N) := hconvD.side_sign_BC
  -- the construction points lie on the sides, hence in the quadrilateral region
  have hKseg : K ∈ segment ℝ A B := affineSegment_eq_segment ℝ A B ▸ hKb.1
  have hLseg : L ∈ segment ℝ B C := affineSegment_eq_segment ℝ B C ▸ hLb.1
  have hMseg : M ∈ segment ℝ C D := affineSegment_eq_segment ℝ C D ▸ hMb.1
  have hNseg : N ∈ segment ℝ D A := affineSegment_eq_segment ℝ D A ▸ hNb.1
  have hKseg' : K ∈ segment ℝ B A := affineSegment_eq_segment ℝ B A ▸ hKb.symm.1
  have hNseg' : N ∈ segment ℝ A D := affineSegment_eq_segment ℝ A D ▸ hNb.symm.1
  have hPb : Sbtw ℝ B P D := by
    rw [hPdef]
    exact sbtw_lineMap hBD (sub_pos.mpr hs1) (sub_lt_self 1 hs0)
  have hPseg : P ∈ segment ℝ B D := affineSegment_eq_segment ℝ B D ▸ hPb.1
  have hPA : P ≠ A := by
    intro heq
    have h1 : ω (D - B) (A - B) = 0 := by
      rw [← heq]
      exact hfP_BD
    exact hw3 (by rw [hw3def]; exact h1)
  have hPC : P ≠ C := by
    intro heq
    have h1 : ω (D - B) (C - B) = 0 := by
      rw [← heq]
      exact hfP_BD
    exact hw4 (by rw [hw4def]; exact h1)
  clear_value w3 w4
  have hAmem : A ∈ convexHull ℝ ({A, B, C, D} : Set Plane) :=
    subset_convexHull ℝ _ (Set.mem_insert A {B, C, D})
  have hBmem : B ∈ convexHull ℝ ({A, B, C, D} : Set Plane) :=
    subset_convexHull ℝ _ (Set.mem_insert_of_mem A (Set.mem_insert B {C, D}))
  have hCmem : C ∈ convexHull ℝ ({A, B, C, D} : Set Plane) :=
    subset_convexHull ℝ _ (Set.mem_insert_of_mem A
      (Set.mem_insert_of_mem B (Set.mem_insert C {D})))
  have hDmem : D ∈ convexHull ℝ ({A, B, C, D} : Set Plane) :=
    subset_convexHull ℝ _ (Set.mem_insert_of_mem A (Set.mem_insert_of_mem B
      (Set.mem_insert_of_mem C (Set.mem_singleton D))))
  have hKmem : K ∈ convexHull ℝ ({A, B, C, D} : Set Plane) :=
    Convex.segment_subset (convex_convexHull ℝ _) hAmem hBmem hKseg
  have hLmem : L ∈ convexHull ℝ ({A, B, C, D} : Set Plane) :=
    Convex.segment_subset (convex_convexHull ℝ _) hBmem hCmem hLseg
  have hMmem : M ∈ convexHull ℝ ({A, B, C, D} : Set Plane) :=
    Convex.segment_subset (convex_convexHull ℝ _) hCmem hDmem hMseg
  have hNmem : N ∈ convexHull ℝ ({A, B, C, D} : Set Plane) :=
    Convex.segment_subset (convex_convexHull ℝ _) hDmem hAmem hNseg
  have hPmem : P ∈ convexHull ℝ ({A, B, C, D} : Set Plane) :=
    Convex.segment_subset (convex_convexHull ℝ _) hBmem hDmem hPseg
  -- triangle-to-piece inclusions used by the covering argument
  have hmonoLBP : convexHull ℝ ({L, B, P} : Set Plane) ⊆
      convexHull ℝ ({B, K, P, L} : Set Plane) :=
    convexHull_mono (fun z hz ↦ by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
      tauto)
  have hmonoLPC : convexHull ℝ ({L, P, C} : Set Plane) ⊆
      convexHull ℝ ({C, L, P, M} : Set Plane) :=
    convexHull_mono (fun z hz ↦ by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
      tauto)
  have hmonoMCP : convexHull ℝ ({M, C, P} : Set Plane) ⊆
      convexHull ℝ ({C, L, P, M} : Set Plane) :=
    convexHull_mono (fun z hz ↦ by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
      tauto)
  have hmonoMPD : convexHull ℝ ({M, P, D} : Set Plane) ⊆
      convexHull ℝ ({D, N, P, M} : Set Plane) :=
    convexHull_mono (fun z hz ↦ by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
      tauto)
  have hmonoKBP : convexHull ℝ ({K, B, P} : Set Plane) ⊆
      convexHull ℝ ({B, K, P, L} : Set Plane) :=
    convexHull_mono (fun z hz ↦ by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
      tauto)
  have hmonoKPA : convexHull ℝ ({K, P, A} : Set Plane) ⊆
      convexHull ℝ ({K, P, N, A} : Set Plane) :=
    convexHull_mono (fun z hz ↦ by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
      tauto)
  have hmonoNAP : convexHull ℝ ({N, A, P} : Set Plane) ⊆
      convexHull ℝ ({K, P, N, A} : Set Plane) :=
    convexHull_mono (fun z hz ↦ by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
      tauto)
  have hmonoNPD : convexHull ℝ ({N, P, D} : Set Plane) ⊆
      convexHull ℝ ({D, N, P, M} : Set Plane) :=
    convexHull_mono (fun z hz ↦ by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
      tauto)
  -- pairwise disjointness of the piece interiors: the five line-separated pairs
  have hd01 : Disjoint (interior (quadRegion K P N A)) (interior (quadRegion B K P L)) :=
    disjoint_KPNA_BKPL hKPne hw1 hfB_KP hfL_KP hfN_KP hfA_KP hs0 hs1' hw1w1c
  have hd02 : Disjoint (interior (quadRegion K P N A)) (interior (quadRegion C L P M)) :=
    disjoint_KPNA_CLPM hBD hw3 hfK_BD hfP_BD hfN_BD hfA_BD hfC_BD hfL_BD hfM_BD hs1' htN0 htM1' hw3w4
  have hd03 : Disjoint (interior (quadRegion K P N A)) (interior (quadRegion D N P M)) :=
    disjoint_KPNA_DNPM hNPne hw6 hfK_PN hfA_PN hfD_PN hs0 hs1' htN0 htN1' hsideD_PN
  have hd12 : Disjoint (interior (quadRegion B K P L)) (interior (quadRegion C L P M)) :=
    disjoint_BKPL_CLPM hLPne hw2 hfB_PL hfK_PL hfC_PL hfM_PL hs0 hs1' hw2w2a
  have hd23 : Disjoint (interior (quadRegion C L P M)) (interior (quadRegion D N P M)) :=
    disjoint_CLPM_DNPM hMPne hw5 hfC_PM hfL_PM hfD_PM hs0 hs1' htM0 htM1' hsideD_PM
  -- the remaining pair: the B-piece and the D-piece, split along the diagonal `BD`
  have hd13 : Disjoint (interior (quadRegion B K P L)) (interior (quadRegion D N P M)) :=
    disjoint_BKP_DNM hBD hconvB hconvD hKPne hLPne hw1 hw2 hw3 hw4 hw3w4
      hfB_KP hfD_KP hfN_KP hfB_PL hfD_PL hfM_PL hfK_BD hfN_BD hfL_BD hfM_BD hfP_BD hvPB
      hs0 hs1' htN0 htM1' hPdef
  -- assemble the dissection
  refine ⟨⟨![(K, P, N, A), (B, K, P, L), (C, L, P, M), (D, N, P, M)], ?_, ?_, ?_, ?_⟩,
    0, ?_⟩
  · intro i
    fin_cases i
    · show CyclicQuad K P N A
      exact hcyc0
    · show CyclicQuad B K P L
      exact hcyc1
    · show CyclicQuad C L P M
      exact hcyc2
    · show CyclicQuad D N P M
      exact hcyc3
  · intro i
    fin_cases i
    · show quadRegion K P N A ⊆ quadRegion A B C D
      apply convexHull_min _ (convex_convexHull ℝ _)
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl | rfl
      · exact hKmem
      · exact hPmem
      · exact hNmem
      · exact hAmem
    · show quadRegion B K P L ⊆ quadRegion A B C D
      apply convexHull_min _ (convex_convexHull ℝ _)
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl | rfl
      · exact hBmem
      · exact hKmem
      · exact hPmem
      · exact hLmem
    · show quadRegion C L P M ⊆ quadRegion A B C D
      apply convexHull_min _ (convex_convexHull ℝ _)
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl | rfl
      · exact hCmem
      · exact hLmem
      · exact hPmem
      · exact hMmem
    · show quadRegion D N P M ⊆ quadRegion A B C D
      apply convexHull_min _ (convex_convexHull ℝ _)
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl | rfl
      · exact hDmem
      · exact hNmem
      · exact hPmem
      · exact hMmem
  · exact cover_four_pieces h.convex hPseg hKseg hLseg hMseg hNseg hKseg' hNseg'
      hAB hBC hCD hDA hBD hPb hPA hPC hmonoLBP hmonoLPC hmonoMCP hmonoMPD hmonoKBP hmonoKPA
      hmonoNAP hmonoNPD
  · exact disjoint_four_pieces hd01 hd02 hd03 hd12 hd23 hd13
  · show IsoscelesTrapezoid K P N A
    exact htrap

/-- **Base case.** Every cyclic quadrilateral admits a dissection into four cyclic
quadrilaterals, one of which is an isosceles trapezoid.

Construction (kalva): take a point `P` inside the quadrilateral, the point `K` on `AB`
with `PK ∥ AD`, and then `L` on `BC`, `M` on `CD`, `N` on `DA` such that
`∠KPL = 180° − ∠B`, `∠LPM = 180° − ∠C`, `∠MPN = 180° − ∠D`; then also
`∠NPK = 180° − ∠A`, so each of the quadrilaterals `KPLB`, `LPMC`, `MPND`, `NPKA` has a
pair of supplementary opposite angles, hence is cyclic; and `AKPN` has `KP ∥ AN`, hence is
an (isosceles) trapezoid. Choosing `P` suitably close to a vertex guarantees that the four
constructed points lie on the sides and not on their extensions. -/
theorem dissection_four {A B C D : Plane} (h : CyclicQuad A B C D) :
    DissectionWithTrapezoid A B C D 4 := by
  rcases anchor_disjunction h.convex h.concyclic with hA | hB | hC | hD
  · exact dissection_four_of_hdiag h hA
  · exact (dissection_four_of_hdiag h.rotate hB).rotate
  · exact (dissection_four_of_hdiag h.rotate.rotate hC).rotate.rotate
  · exact (dissection_four_of_hdiag h.rotate.rotate.rotate hD).rotate.rotate.rotate

set_option maxHeartbeats 2400000 in
theorem trapezoid_cyclic₀ {A B K L : Plane} {e w : Plane} {κ μ ee ww : ℝ}
    (hB : B = A + e) (hK : K = A + κ • e + (1 / 2 : ℝ) • w) (hL : L = A + μ • e + (1 / 2 : ℝ) • w)
    (he : e ≠ 0) (hw : w ≠ 0) (horth : ⟪e, w⟫ = 0) (hμκ : μ < κ) (hκμ : κ + μ = 1)
    (hww : 0 < ww)
    (inner_eeww : ∀ a b : ℝ, ⟪a • e + b • w, a • e + b • w⟫ = a ^ 2 * ee + b ^ 2 * ww)
    (sq_norm_eq : ∀ x : Plane, ‖x‖ ^ 2 = ⟪x, x⟫)
    (norm_eq_of_sq : ∀ x y : Plane, ‖x‖ ^ 2 = ‖y‖ ^ 2 → ‖x‖ = ‖y‖) :
    CyclicQuad A B K L := by
    refine ⟨?_, ?_⟩
    · rw [hB, hK, hL]
      exact convexQuad_of_ortho he hw horth (by norm_num) hμκ
    · set t₁ := (μ * μ - μ) * ee / ww + 1 / 4 with ht₁def
      set O₁ := A + (1 / 2 : ℝ) • e + t₁ • w with hO₁def
      clear_value t₁ O₁
      have hA1 : A - O₁ = (-1 / 2 : ℝ) • e + (-t₁) • w := by rw [hO₁def]; module
      have hB1 : B - O₁ = (1 / 2 : ℝ) • e + (-t₁) • w := by rw [hO₁def, hB]; module
      have hK1 : K - O₁ = (κ - 1 / 2) • e + (1 / 2 - t₁) • w := by rw [hO₁def, hK]; module
      have hL1 : L - O₁ = (μ - 1 / 2) • e + (1 / 2 - t₁) • w := by rw [hO₁def, hL]; module
      have hsA : ‖A - O₁‖ ^ 2 = (-1 / 2) ^ 2 * ee + (-t₁) ^ 2 * ww := by
        rw [sq_norm_eq, hA1, inner_eeww]
      have hsB : ‖B - O₁‖ ^ 2 = (1 / 2) ^ 2 * ee + (-t₁) ^ 2 * ww := by
        rw [sq_norm_eq, hB1, inner_eeww]
      have hsK : ‖K - O₁‖ ^ 2 = (κ - 1 / 2) ^ 2 * ee + (1 / 2 - t₁) ^ 2 * ww := by
        rw [sq_norm_eq, hK1, inner_eeww]
      have hsL : ‖L - O₁‖ ^ 2 = (μ - 1 / 2) ^ 2 * ee + (1 / 2 - t₁) ^ 2 * ww := by
        rw [sq_norm_eq, hL1, inner_eeww]
      have hsBeq : ‖B - O₁‖ ^ 2 = ‖A - O₁‖ ^ 2 := by rw [hsB, hsA]; ring
      have hsKeq : ‖K - O₁‖ ^ 2 = ‖A - O₁‖ ^ 2 := by
        rw [hsK, hsA, ht₁def]
        have hκ1 : κ = 1 - μ := by linarith [hκμ]
        rw [hκ1]
        field_simp [hww.ne']
        ring
      have hsLeq : ‖L - O₁‖ ^ 2 = ‖A - O₁‖ ^ 2 := by
        rw [hsL, hsA, ht₁def]
        field_simp [hww.ne']
        ring
      refine ⟨O₁, dist A O₁, rfl, ?_, ?_, ?_⟩
      · rw [dist_eq_norm, dist_eq_norm]
        exact norm_eq_of_sq _ _ hsBeq
      · rw [dist_eq_norm, dist_eq_norm]
        exact norm_eq_of_sq _ _ hsKeq
      · rw [dist_eq_norm, dist_eq_norm]
        exact norm_eq_of_sq _ _ hsLeq


set_option maxHeartbeats 2400000 in
theorem trapezoid_cyclic₁ {A C D K L : Plane} {e w : Plane} {α k κ μ ee ww : ℝ}
    (hK2show : K = L + (K - L)) (hC2 : C = L + ((α - k - μ) / (κ - μ)) • (K - L) + (1 / 2 : ℝ) • w)
    (hD2 : D = L + ((α - μ) / (κ - μ)) • (K - L) + (1 / 2 : ℝ) • w)
    (hK : K = A + κ • e + (1 / 2 : ℝ) • w) (hL : L = A + μ • e + (1 / 2 : ℝ) • w)
    (hC : C = A + (α - k) • e + w) (hD : D = A + α • e + w)
    (he' : K - L ≠ 0) (hw : w ≠ 0) (horth'' : ⟪K - L, w⟫ = 0)
    (hμ₂κ₂ : (α - μ) / (κ - μ) < (α - k - μ) / (κ - μ))
    (hκμ : κ + μ = 1) (hα : α = (k + 1) / 2) (hκeq : κ = (3 - k) / 4) (hμeq : μ = (k + 1) / 4)
    (hww : 0 < ww)
    (inner_eeww : ∀ a b : ℝ, ⟪a • e + b • w, a • e + b • w⟫ = a ^ 2 * ee + b ^ 2 * ww)
    (sq_norm_eq : ∀ x : Plane, ‖x‖ ^ 2 = ⟪x, x⟫)
    (norm_eq_of_sq : ∀ x y : Plane, ‖x‖ ^ 2 = ‖y‖ ^ 2 → ‖x‖ = ‖y‖) :
    CyclicQuad L K C D := by
    refine ⟨?_, ?_⟩
    · rw [hK2show, hC2, hD2]
      exact convexQuad_of_ortho he' hw horth'' (by norm_num) hμ₂κ₂
    · set t₂ := 3 / 4 - ((1 / 2 - μ) ^ 2 - (1 / 2 - α) ^ 2) * ee / ww with ht₂def
      set O₂ := A + (1 / 2 : ℝ) • e + t₂ • w with hO₂def
      clear_value t₂ O₂
      have hL2 : L - O₂ = (μ - 1 / 2) • e + (1 / 2 - t₂) • w := by rw [hO₂def, hL]; module
      have hK2 : K - O₂ = (κ - 1 / 2) • e + (1 / 2 - t₂) • w := by rw [hO₂def, hK]; module
      have hC2v : C - O₂ = (α - k - 1 / 2) • e + (1 - t₂) • w := by
        rw [hO₂def, hC]; module
      have hD2v : D - O₂ = (α - 1 / 2) • e + (1 - t₂) • w := by rw [hO₂def, hD]; module
      have hsL2 : ‖L - O₂‖ ^ 2 = (μ - 1 / 2) ^ 2 * ee + (1 / 2 - t₂) ^ 2 * ww := by
        rw [sq_norm_eq, hL2, inner_eeww]
      have hsK2 : ‖K - O₂‖ ^ 2 = (κ - 1 / 2) ^ 2 * ee + (1 / 2 - t₂) ^ 2 * ww := by
        rw [sq_norm_eq, hK2, inner_eeww]
      have hsC2 : ‖C - O₂‖ ^ 2 = (α - k - 1 / 2) ^ 2 * ee + (1 - t₂) ^ 2 * ww := by
        rw [sq_norm_eq, hC2v, inner_eeww]
      have hsD2 : ‖D - O₂‖ ^ 2 = (α - 1 / 2) ^ 2 * ee + (1 - t₂) ^ 2 * ww := by
        rw [sq_norm_eq, hD2v, inner_eeww]
      have hsKeq2 : ‖K - O₂‖ ^ 2 = ‖L - O₂‖ ^ 2 := by
        rw [hsK2, hsL2]
        have hκ1 : κ = 1 - μ := by linarith [hκμ]
        rw [hκ1]; ring
      have hsCeq2 : ‖C - O₂‖ ^ 2 = ‖L - O₂‖ ^ 2 := by
        rw [hsC2, hsL2, ht₂def, hα]
        field_simp [hww.ne']
        ring
      have hsDeq2 : ‖D - O₂‖ ^ 2 = ‖L - O₂‖ ^ 2 := by
        rw [hsD2, hsL2, ht₂def]
        field_simp [hww.ne']
        ring
      refine ⟨O₂, dist L O₂, rfl, ?_, ?_, ?_⟩
      · rw [dist_eq_norm, dist_eq_norm]
        exact norm_eq_of_sq _ _ hsKeq2
      · rw [dist_eq_norm, dist_eq_norm]
        exact norm_eq_of_sq _ _ hsCeq2
      · rw [dist_eq_norm, dist_eq_norm]
        exact norm_eq_of_sq _ _ hsDeq2


set_option maxHeartbeats 2400000 in
theorem trapezoid_disjoint {A B C D K L : Plane} {e w : Plane} {κ μ ww : ℝ}
    (hBAm_w : ⟪B - A, w⟫ = 0) (hCAm_w : ⟪C - A, w⟫ = ww) (hDAm_w : ⟪D - A, w⟫ = ww)
    (hww : 0 < ww) (hww_def : ww = ⟪w, w⟫) (horth : ⟪e, w⟫ = 0)
    (hK : K = A + κ • e + (1 / 2 : ℝ) • w) (hL : L = A + μ • e + (1 / 2 : ℝ) • w) :
    Disjoint (interior (quadRegion A B K L)) (interior (quadRegion L K C D)) := by
  have hFA : ⟪A - A, w⟫ / ww = 0 := by rw [sub_self, inner_zero_left, zero_div]
  have hFB : ⟪B - A, w⟫ / ww = 0 := by rw [hBAm_w, zero_div]
  have hKAm_w : ⟪K - A, w⟫ = (1 / 2) * ww := by
    rw [show K - A = κ • e + (1 / 2 : ℝ) • w by rw [hK]; module]
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, horth, mul_zero,
      zero_add, ← hww_def]
  have hLAm_w : ⟪L - A, w⟫ = (1 / 2) * ww := by
    rw [show L - A = μ • e + (1 / 2 : ℝ) • w by rw [hL]; module]
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, horth, mul_zero,
      zero_add, ← hww_def]
  have hFK : ⟪K - A, w⟫ / ww = 1 / 2 := by rw [hKAm_w, mul_div_cancel_right₀ _ hww.ne']
  have hFL : ⟪L - A, w⟫ / ww = 1 / 2 := by rw [hLAm_w, mul_div_cancel_right₀ _ hww.ne']
  have hFC : ⟪C - A, w⟫ / ww = 1 := by rw [hCAm_w, div_self hww.ne']
  have hFD : ⟪D - A, w⟫ / ww = 1 := by rw [hDAm_w, div_self hww.ne']
  have hconv₁ : Convex ℝ {X : Plane | ⟪X - A, w⟫ / ww ≤ 1 / 2} := by
    intro x hx y hy a b ha hb hab
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    have hlin : ⟪a • x + b • y - A, w⟫ = a * ⟪x - A, w⟫ + b * ⟪y - A, w⟫ := by
      have h3 : (a + b) * ⟪A, w⟫ = ⟪A, w⟫ := by rw [hab, one_mul]
      rw [inner_sub_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
        inner_sub_left, inner_sub_left]
      linear_combination h3
    rw [show ⟪a • x + b • y - A, w⟫ / ww =
        a * (⟪x - A, w⟫ / ww) + b * (⟪y - A, w⟫ / ww) by rw [hlin]; ring]
    have h1 : a * (⟪x - A, w⟫ / ww) ≤ a * (1 / 2) := mul_le_mul_of_nonneg_left hx ha
    have h2 : b * (⟪y - A, w⟫ / ww) ≤ b * (1 / 2) := mul_le_mul_of_nonneg_left hy hb
    have h3 : a * (1 / 2) + b * (1 / 2) = 1 / 2 := by rw [← add_mul, hab, one_mul]
    rw [← h3]; exact add_le_add h1 h2
  have hconv₂ : Convex ℝ {X : Plane | 1 / 2 ≤ ⟪X - A, w⟫ / ww} := by
    intro x hx y hy a b ha hb hab
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    have hlin : ⟪a • x + b • y - A, w⟫ = a * ⟪x - A, w⟫ + b * ⟪y - A, w⟫ := by
      have h3 : (a + b) * ⟪A, w⟫ = ⟪A, w⟫ := by rw [hab, one_mul]
      rw [inner_sub_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
        inner_sub_left, inner_sub_left]
      linear_combination h3
    rw [show ⟪a • x + b • y - A, w⟫ / ww =
        a * (⟪x - A, w⟫ / ww) + b * (⟪y - A, w⟫ / ww) by rw [hlin]; ring]
    have h1 : a * (1 / 2) ≤ a * (⟪x - A, w⟫ / ww) := mul_le_mul_of_nonneg_left hx ha
    have h2 : b * (1 / 2) ≤ b * (⟪y - A, w⟫ / ww) := mul_le_mul_of_nonneg_left hy hb
    have h3 : a * (1 / 2) + b * (1 / 2) = 1 / 2 := by rw [← add_mul, hab, one_mul]
    rw [← h3]; exact add_le_add h1 h2
  have hsub1hp : quadRegion A B K L ⊆ {X : Plane | ⟪X - A, w⟫ / ww ≤ 1 / 2} := by
    apply convexHull_min _ hconv₁
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    simp only [Set.mem_setOf_eq]
    rcases hx with rfl | rfl | rfl | rfl
    · rw [hFA]; norm_num
    · rw [hFB]; norm_num
    · exact hFK.le
    · exact hFL.le
  have hsub2hp : quadRegion L K C D ⊆ {X : Plane | 1 / 2 ≤ ⟪X - A, w⟫ / ww} := by
    apply convexHull_min _ hconv₂
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    simp only [Set.mem_setOf_eq]
    rcases hx with rfl | rfl | rfl | rfl
    · exact hFL.ge
    · exact hFK.ge
    · rw [hFC]; norm_num
    · rw [hFD]; norm_num
  have hkey₁ : ∀ x : Plane, ⟪x - A, w⟫ / ww = 1 / 2 →
      x ∉ interior {X : Plane | ⟪X - A, w⟫ / ww ≤ 1 / 2} := by
    intro x hx hxint
    rw [mem_interior_iff_mem_nhds] at hxint
    rw [Metric.mem_nhds_iff] at hxint
    obtain ⟨ε, hε, hεsub⟩ := hxint
    set cc := ε / (2 * (‖w‖ + 1)) with hccdef
    have hcc : 0 < cc := by
      rw [hccdef]
      exact div_pos hε (mul_pos zero_lt_two (add_pos_of_nonneg_of_pos (norm_nonneg w)
        zero_lt_one))
    have hy_mem : x + cc • w ∈ Metric.ball x ε := by
      rw [Metric.mem_ball, dist_eq_norm]
      rw [show x + cc • w - x = cc • w by abel]
      rw [norm_smul_of_nonneg hcc.le w, hccdef]
      have hn : 0 ≤ ‖w‖ := norm_nonneg w
      rw [div_mul_eq_mul_div, div_lt_iff₀ (show (0 : ℝ) < 2 * (‖w‖ + 1) from
        mul_pos zero_lt_two (add_pos_of_nonneg_of_pos hn zero_lt_one))]
      have hsmall : ‖w‖ < 2 * (‖w‖ + 1) := by
        have h1 : ‖w‖ < ‖w‖ + 2 := lt_add_of_pos_right ‖w‖ (by norm_num)
        have h2 : ‖w‖ + 2 ≤ 2 * (‖w‖ + 1) := by
          rw [show 2 * (‖w‖ + 1) = (‖w‖ + 2) + ‖w‖ by ring]
          exact le_add_of_nonneg_right hn
        exact lt_of_lt_of_le h1 h2
      exact mul_lt_mul_of_pos_left hsmall hε
    have hmemS := hεsub hy_mem
    simp only [Set.mem_setOf_eq] at hmemS
    have hF : ⟪x + cc • w - A, w⟫ / ww = 1 / 2 + cc := by
      rw [show x + cc • w - A = (x - A) + cc • w by abel]
      rw [inner_add_left, real_inner_smul_left, ← hww_def, add_div, hx,
        mul_div_cancel_right₀ _ hww.ne']
    rw [hF] at hmemS
    exact absurd hmemS (not_le_of_gt (lt_add_of_pos_right _ hcc))
  have hkey₂ : ∀ x : Plane, ⟪x - A, w⟫ / ww = 1 / 2 →
      x ∉ interior {X : Plane | 1 / 2 ≤ ⟪X - A, w⟫ / ww} := by
    intro x hx hxint
    rw [mem_interior_iff_mem_nhds] at hxint
    rw [Metric.mem_nhds_iff] at hxint
    obtain ⟨ε, hε, hεsub⟩ := hxint
    set cc := ε / (2 * (‖w‖ + 1)) with hccdef
    have hcc : 0 < cc := by
      rw [hccdef]
      exact div_pos hε (mul_pos zero_lt_two (add_pos_of_nonneg_of_pos (norm_nonneg w)
        zero_lt_one))
    have hy_mem : x - cc • w ∈ Metric.ball x ε := by
      rw [Metric.mem_ball, dist_eq_norm]
      rw [show x - cc • w - x = -(cc • w) by abel]
      rw [norm_neg, norm_smul_of_nonneg hcc.le w, hccdef]
      have hn : 0 ≤ ‖w‖ := norm_nonneg w
      rw [div_mul_eq_mul_div, div_lt_iff₀ (show (0 : ℝ) < 2 * (‖w‖ + 1) from
        mul_pos zero_lt_two (add_pos_of_nonneg_of_pos hn zero_lt_one))]
      have hsmall : ‖w‖ < 2 * (‖w‖ + 1) := by
        have h1 : ‖w‖ < ‖w‖ + 2 := lt_add_of_pos_right ‖w‖ (by norm_num)
        have h2 : ‖w‖ + 2 ≤ 2 * (‖w‖ + 1) := by
          rw [show 2 * (‖w‖ + 1) = (‖w‖ + 2) + ‖w‖ by ring]
          exact le_add_of_nonneg_right hn
        exact lt_of_lt_of_le h1 h2
      exact mul_lt_mul_of_pos_left hsmall hε
    have hmemS := hεsub hy_mem
    simp only [Set.mem_setOf_eq] at hmemS
    have hF : ⟪x - cc • w - A, w⟫ / ww = 1 / 2 - cc := by
      rw [show x - cc • w - A = (x - A) - cc • w by abel]
      rw [inner_sub_left, real_inner_smul_left, ← hww_def, sub_div, hx,
        mul_div_cancel_right₀ _ hww.ne']
    rw [hF] at hmemS
    exact absurd hmemS (not_le_of_gt ((sub_lt_self_iff (1 / 2 : ℝ)).mpr hcc))
  have hint₁ : interior {X : Plane | ⟪X - A, w⟫ / ww ≤ 1 / 2} ⊆
      {X : Plane | ⟪X - A, w⟫ / ww < 1 / 2} := by
    intro x hx
    have h1 := interior_subset hx
    simp only [Set.mem_setOf_eq] at h1
    simp only [Set.mem_setOf_eq]
    by_contra hcon
    rw [not_lt] at hcon
    exact hkey₁ x (le_antisymm h1 hcon) hx
  have hint₂ : interior {X : Plane | 1 / 2 ≤ ⟪X - A, w⟫ / ww} ⊆
      {X : Plane | 1 / 2 < ⟪X - A, w⟫ / ww} := by
    intro x hx
    have h1 := interior_subset hx
    simp only [Set.mem_setOf_eq] at h1
    simp only [Set.mem_setOf_eq]
    by_contra hcon
    rw [not_lt] at hcon
    exact hkey₂ x (le_antisymm hcon h1) hx
  have hdisj01 : Disjoint (interior (quadRegion A B K L))
      (interior (quadRegion L K C D)) := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    have h1 : ⟪x - A, w⟫ / ww < 1 / 2 := hint₁ (interior_mono hsub1hp hx1)
    have h2 : 1 / 2 < ⟪x - A, w⟫ / ww := hint₂ (interior_mono hsub2hp hx2)
    exact absurd h1 (not_lt_of_gt h2)
  exact hdisj01

/-- **Induction step, geometric part.** A cyclic isosceles trapezoid can be dissected into
two isosceles trapezoids by cutting it with a line parallel to its two parallel sides
(e.g. through the midpoints of the two legs).

(The cyclicity hypothesis is essential: a non-rectangular parallelogram satisfies
`IsoscelesTrapezoid` alone, and its midpoint pieces, being non-rectangular parallelograms,
would not be cyclic. A *cyclic* trapezoid is symmetric about the common perpendicular
bisector of its parallel sides, so the midpoint cut produces two smaller isosceles
trapezoids, each again cyclic — and a rectangle produces two rectangles.) -/
theorem trapezoid_split {A B C D : Plane} (h : IsoscelesTrapezoid A B C D)
    (hcyc : CyclicQuad A B C D) :
    ∃ e : CyclicDissection A B C D 2, ∀ k : Fin 2,
      IsoscelesTrapezoid (e.pieces k).1 (e.pieces k).2.1 (e.pieces k).2.2.1
        (e.pieces k).2.2.2 := by
  -- Setup: `e = B − A` along the parallel sides, `w` the perpendicular part of `D − A`.
  set e := B - A with he_def
  have he : e ≠ 0 := by
    intro hzero
    rw [he_def] at hzero
    have hBA : B = A := sub_eq_zero.mp hzero
    exact h.convex.not_mem₁ (by
      rw [← hBA]
      exact subset_convexHull ℝ _ (Set.mem_insert B {C, D}))
  obtain ⟨k, hk⟩ := h.parallel
  rw [← he_def] at hk
  set ee := ⟪e, e⟫ with hee_def
  have hee : 0 < ee := real_inner_self_pos.mpr he
  set α := ⟪D - A, e⟫ / ee with hα_def
  set w := (D - A) - α • e with hw_def
  have horth : ⟪e, w⟫ = 0 := by
    rw [hw_def, inner_sub_right, real_inner_smul_right, ← hee_def, hα_def,
      real_inner_comm e (D - A), div_mul_cancel₀ _ hee.ne', sub_self]
  have hw : w ≠ 0 := by
    intro hzero
    have h3 : (D - A) - α • e = 0 := by rw [← hw_def, hzero]
    have hDA : D - A = α • e := sub_eq_zero.mp h3
    have hD0 : D = A + α • e := by rw [← hDA]; abel
    have hB0 : B = A + e := by rw [he_def]; abel
    rcases lt_or_ge α 0 with hαneg | hα0
    · -- α < 0: A ∈ segment B D ⊆ hull {B,C,D}, contradicting `not_mem₁`.
      have h1α : (0 : ℝ) < 1 - α := by linarith
      have hb1α : (1 - α)⁻¹ * (1 - α) = 1 := inv_mul_cancel₀ h1α.ne'
      have hAseg : (1 - (1 - α)⁻¹) • B + (1 - α)⁻¹ • D = A := by
        rw [hD0, hB0]
        rw [show (1 - (1 - α)⁻¹) • (A + e) + (1 - α)⁻¹ • (A + α • e) =
            A + ((1 - (1 - α)⁻¹) + (1 - α)⁻¹ * α) • e by module]
        rw [show (1 - (1 - α)⁻¹) + (1 - α)⁻¹ * α = 0 by linarith [hb1α],
          zero_smul, add_zero]
      exact h.convex.not_mem₁ (Convex.segment_subset (convex_convexHull ℝ _)
        (subset_convexHull ℝ _ (Set.mem_insert B {C, D}))
        (subset_convexHull ℝ _ (Set.mem_insert_of_mem B (Set.mem_insert_of_mem C
          (Set.mem_singleton D))))
        ⟨1 - (1 - α)⁻¹, (1 - α)⁻¹,
          sub_nonneg.mpr (inv_lt_one_of_one_lt₀ (by linarith : (1 : ℝ) < 1 - α)).le,
          (inv_pos.mpr h1α).le, sub_add_cancel 1 (1 - α)⁻¹, hAseg⟩)
    · rcases lt_or_ge 1 α with hα1 | hα1
      · -- α > 1: B ∈ segment A D ⊆ hull {C,D,A}, contradicting `not_mem₂`.
        have hαpos : 0 < α := lt_trans zero_lt_one hα1
        have hAinv : (1 - α⁻¹) • A + α⁻¹ • D = B := by
          rw [hD0, hB0]
          rw [show (1 - α⁻¹) • A + α⁻¹ • (A + α • e) = A + (α⁻¹ * α) • e by module]
          rw [inv_mul_cancel₀ hαpos.ne', one_smul]
        exact h.convex.not_mem₂ (Convex.segment_subset (convex_convexHull ℝ _)
          (subset_convexHull ℝ _ (Set.mem_insert_of_mem C (Set.mem_insert_of_mem D
            (Set.mem_singleton A))))
          (subset_convexHull ℝ _ (Set.mem_insert_of_mem C (Set.mem_insert D {A})))
          ⟨1 - α⁻¹, α⁻¹, sub_nonneg.mpr (inv_lt_one_of_one_lt₀ hα1).le,
            (inv_pos.mpr hαpos).le, sub_add_cancel 1 α⁻¹, hAinv⟩)
      · -- 0 ≤ α ≤ 1: D ∈ segment A B ⊆ hull {A,B,C}, contradicting `not_mem₄`.
        exact h.convex.not_mem₄ (Convex.segment_subset (convex_convexHull ℝ _)
          (subset_convexHull ℝ _ (Set.mem_insert A {B, C}))
          (subset_convexHull ℝ _ (Set.mem_insert_of_mem A (Set.mem_insert B {C})))
          ⟨1 - α, α, sub_nonneg.mpr hα1, hα0, sub_add_cancel 1 α, by rw [hD0, hB0]; module⟩)
  have hB : B = A + e := by rw [he_def]; abel
  have hD : D = A + α • e + w := by rw [hw_def]; module
  have hC : C = A + (α - k) • e + w := by
    have h1 : C = D - k • e := by rw [← hk]; abel
    rw [h1, hD]; module
  have hCA : C - A = (α - k) • e + w := by rw [hC]; module
  have hDA : D - A = α • e + w := by rw [hD]; module
  have hCB : C - B = (α - k - 1) • e + w := by rw [hC, hB]; module
  set ww := ⟪w, w⟫ with hww_def
  have hww : 0 < ww := real_inner_self_pos.mpr hw
  have horth' : ⟪w, e⟫ = 0 := by rw [real_inner_comm e w]; exact horth
  have sq_norm_eq : ∀ x : Plane, ‖x‖ ^ 2 = ⟪x, x⟫ :=
    fun x ↦ (real_inner_self_eq_norm_sq x).symm
  have inner_eeww : ∀ a b : ℝ, ⟪a • e + b • w, a • e + b • w⟫ = a ^ 2 * ee + b ^ 2 * ww := by
    intro a b
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      horth, horth', ← hee_def, ← hww_def]
    ring
  have inner_ew1 : ∀ a : ℝ, ⟪a • e + w, a • e + w⟫ = a ^ 2 * ee + ww := by
    intro a
    have h1 := inner_eeww a 1
    rwa [one_smul, one_pow, one_mul] at h1
  have norm_eq_of_sq : ∀ x y : Plane, ‖x‖ ^ 2 = ‖y‖ ^ 2 → ‖x‖ = ‖y‖ := by
    intro x y hh
    rcases eq_or_eq_neg_of_sq_eq_sq _ _ hh with h1 | h1
    · exact h1
    · have hn1 := norm_nonneg x
      have hn2 := norm_nonneg y
      linarith
  have hnormCB : ‖C - B‖ ^ 2 = (α - k - 1) ^ 2 * ee + ww := by
    rw [sq_norm_eq, hCB, inner_ew1]
  have hnormDA : ‖D - A‖ ^ 2 = α ^ 2 * ee + ww := by
    rw [sq_norm_eq, hDA, inner_ew1]
  have hquad : (α - k - 1) ^ 2 = α ^ 2 := by
    have h1 := h.legs_eq
    rw [dist_eq_norm, dist_eq_norm] at h1
    have h2 : ‖B - C‖ ^ 2 = ‖A - D‖ ^ 2 := congrArg (· ^ 2) h1
    rw [show B - C = -(C - B) by abel, show A - D = -(D - A) by abel, norm_neg, norm_neg,
      hnormCB, hnormDA] at h2
    have h3 : (α - k - 1) ^ 2 * ee = α ^ 2 * ee := by linarith [h2]
    exact mul_right_cancel₀ hee.ne' h3
  have hlegs : (k + 1) * (2 * α - k - 1) = 0 := by
    have h5 : (k + 1) * (2 * α - k - 1) = α ^ 2 - (α - k - 1) ^ 2 := by ring
    rw [h5, hquad, sub_self]
  -- In a cyclic trapezoid the parallel sides are centered: `α = (k+1)/2`.
  have hα : α = (k + 1) / 2 := by
    rcases mul_eq_zero.mp hlegs with hk1 | hk1
    · have hkval : k = -1 := by linarith
      obtain ⟨O, r, hAO, hBO, hCO, hDO⟩ := hcyc.concyclic
      set o := O - A with ho_def
      have hsqX : ∀ X : Plane,
          ‖X - O‖ ^ 2 = ⟪X - A, X - A⟫ - 2 * ⟪X - A, o⟫ + ⟪o, o⟫ := by
        intro X
        rw [sq_norm_eq, show X - O = (X - A) - o by rw [ho_def]; abel]
        have hexp : ∀ u v : Plane, ⟪u - v, u - v⟫ = ⟪u, u⟫ - 2 * ⟪u, v⟫ + ⟪v, v⟫ := by
          intro u v
          rw [inner_sub_left, inner_sub_right, inner_sub_right, real_inner_comm u v]
          ring
        exact hexp (X - A) o
      have hdist : ∀ X Y : Plane, dist X O = r → dist Y O = r →
          ‖X - O‖ ^ 2 = ‖Y - O‖ ^ 2 := by
        intro X Y hX hY
        have h1 : dist X O = dist Y O := by rw [hX, hY]
        rw [dist_eq_norm, dist_eq_norm] at h1
        exact congrArg (· ^ 2) h1
      have hn1 : ‖A - O‖ ^ 2 = ‖B - O‖ ^ 2 := hdist A B hAO hBO
      have hn2 : ‖A - O‖ ^ 2 = ‖D - O‖ ^ 2 := hdist A D hAO hDO
      have hn3 : ‖A - O‖ ^ 2 = ‖C - O‖ ^ 2 := hdist A C hAO hCO
      have he1 : 2 * ⟪e, o⟫ = ee := by
        rw [hsqX A, hsqX B, sub_self, inner_zero_left, inner_zero_left, ← he_def,
          ← hee_def] at hn1
        linarith [hn1]
      have he2 : 2 * ⟪D - A, o⟫ = ⟪D - A, D - A⟫ := by
        rw [hsqX A, hsqX D, sub_self, inner_zero_left, inner_zero_left] at hn2
        linarith [hn2]
      have he3 : 2 * ⟪C - A, o⟫ = ⟪C - A, C - A⟫ := by
        rw [hsqX A, hsqX C, sub_self, inner_zero_left, inner_zero_left] at hn3
        linarith [hn3]
      have hCA1 : C - A = e + (D - A) := by
        rw [hC, hD, hkval]; module
      have hexp : ⟪C - A, C - A⟫ = ee + 2 * ⟪e, D - A⟫ + ⟪D - A, D - A⟫ := by
        rw [hCA1]
        simp only [inner_add_left, inner_add_right]
        rw [← hee_def, real_inner_comm e (D - A)]
        ring
      have halpha0 : ⟪e, D - A⟫ = 0 := by
        have h2 : 2 * ⟪C - A, o⟫ = 2 * ⟪e, o⟫ + 2 * ⟪D - A, o⟫ := by
          rw [hCA1, inner_add_left]; ring
        rw [he1, he2, he3, hexp] at h2
        linarith [h2]
      rw [hα_def, real_inner_comm e (D - A), halpha0, zero_div]
      linarith [hkval]
    · linarith
  -- The diagonals cross strictly inside, forcing `k < 0`.
  have hkneg : k < 0 := by
    obtain ⟨X, hXAC, hXBD⟩ := h.convex.diagonals
    obtain ⟨hXAC1, hXA, hXC⟩ := hXAC
    obtain ⟨hXBD1, hXB, hXD⟩ := hXBD
    obtain ⟨s, hs, hXs⟩ := hXAC1
    obtain ⟨t, ht, hXt⟩ := hXBD1
    rw [Set.mem_Icc] at hs ht
    obtain ⟨hs0, hs1⟩ := hs
    obtain ⟨ht0, ht1⟩ := ht
    have hXs' : X = A + s • (C - A) := by
      rw [← hXs, AffineMap.lineMap_apply_module']; abel
    have hXt' : X = B + t • (D - B) := by
      rw [← hXt, AffineMap.lineMap_apply_module']; abel
    have hs0' : 0 < s := by
      rcases eq_or_lt_of_le hs0 with hseq | hslt
      · exfalso
        exact hXA (by rw [hXs', ← hseq, zero_smul, add_zero])
      · exact hslt
    have hs1' : s < 1 := by
      rcases eq_or_lt_of_le hs1 with hseq | hslt
      · exfalso
        exact hXC (by rw [hXs', hseq, one_smul]; abel)
      · exact hslt
    have ht0' : 0 < t := by
      rcases eq_or_lt_of_le ht0 with hseq | hslt
      · exfalso
        exact hXB (by rw [hXt', ← hseq, zero_smul, add_zero])
      · exact hslt
    have ht1' : t < 1 := by
      rcases eq_or_lt_of_le ht1 with hseq | hslt
      · exfalso
        exact hXD (by rw [hXt', hseq, one_smul]; abel)
      · exact hslt
    have hDB : D - B = (α - 1) • e + w := by rw [hD, hB]; module
    have hXv1 : X - A = (s * (α - k)) • e + s • w := by
      rw [show X - A = s • (C - A) by rw [hXs']; module, hCA]; module
    have hXv2 : X - A = (1 + t * (α - 1)) • e + t • w := by
      rw [show X - A = e + t • (D - B) by rw [hXt', hB]; module, hDB]; module
    have heq_w : s = t := by
      have h1 : ⟪X - A, w⟫ = s * ww := by
        rw [hXv1]
        simp only [inner_add_left, real_inner_smul_left, horth, mul_zero, zero_add,
          ← hww_def]
      have h2 : ⟪X - A, w⟫ = t * ww := by
        rw [hXv2]
        simp only [inner_add_left, real_inner_smul_left, horth, mul_zero, zero_add,
          ← hww_def]
      have h3 : s * ww = t * ww := by rw [← h1, ← h2]
      exact mul_right_cancel₀ hww.ne' h3
    have heq_e : s * (1 - k) = 1 := by
      have h1 : ⟪X - A, e⟫ = (s * (α - k)) * ee := by
        rw [hXv1]
        simp only [inner_add_left, real_inner_smul_left, horth', mul_zero, add_zero,
          ← hee_def]
      have h2 : ⟪X - A, e⟫ = (1 + t * (α - 1)) * ee := by
        rw [hXv2]
        simp only [inner_add_left, real_inner_smul_left, horth', mul_zero, add_zero,
          ← hee_def]
      have h3 : s * (α - k) = 1 + t * (α - 1) :=
        mul_right_cancel₀ hee.ne' (by rw [← h1, ← h2])
      rw [← heq_w] at h3
      linarith [h3]
    have hs1k : 1 - k = 1 / s := by
      rw [eq_div_iff_mul_eq hs0'.ne']
      linarith [heq_e]
    have h1s : 1 < 1 / s := one_lt_one_div hs0' hs1'
    linarith [hs1k, h1s]
  -- The midpoints of the two legs; the cut `KL` is parallel to `AB` and `DC`.
  -- (Make the coordinate variables opaque to keep normalization fast.)
  clear_value α w ee ww e
  set K := midpoint ℝ B C with hKdef
  set L := midpoint ℝ A D with hLdef
  set κ := (3 - k) / 4 with hκeq
  set μ := (k + 1) / 4 with hμeq
  have hKhalf : K = (1 / 2 : ℝ) • B + (1 / 2 : ℝ) • C := by
    rw [hKdef, midpoint_eq_smul_add, invOf_eq_inv, ← one_div, smul_add]
  have hLhalf : L = (1 / 2 : ℝ) • A + (1 / 2 : ℝ) • D := by
    rw [hLdef, midpoint_eq_smul_add, invOf_eq_inv, ← one_div, smul_add]
  clear_value K L κ μ
  have hK : K = A + κ • e + (1 / 2 : ℝ) • w := by
    rw [hKhalf, hB, hC, hα, hκeq]; module
  have hL : L = A + μ • e + (1 / 2 : ℝ) • w := by
    rw [hLhalf, hD, hα, hμeq]; module
  have hκμ : κ + μ = 1 := by rw [hκeq, hμeq]; ring
  have hμκ : μ < κ := by rw [hκeq, hμeq]; linarith
  have hκμ' : 0 < κ - μ := sub_pos.mpr hμκ
  have hκμne : κ - μ ≠ 0 := hκμ'.ne'
  have hKLdiff : K - L = (κ - μ) • e := by rw [hK, hL]; module
  have hK2show : K = L + (K - L) := by abel
  have hC2 : C = L + ((α - k - μ) / (κ - μ)) • (K - L) + (1 / 2 : ℝ) • w := by
    rw [hKLdiff]
    rw [show ((α - k - μ) / (κ - μ)) • ((κ - μ) • e) = (α - k - μ) • e by
      rw [smul_smul, div_mul_cancel₀ _ hκμne]]
    rw [hC, hL]; module
  have hD2 : D = L + ((α - μ) / (κ - μ)) • (K - L) + (1 / 2 : ℝ) • w := by
    rw [hKLdiff]
    rw [show ((α - μ) / (κ - μ)) • ((κ - μ) • e) = (α - μ) • e by
      rw [smul_smul, div_mul_cancel₀ _ hκμne]]
    rw [hD, hL]; module
  have he' : K - L ≠ 0 := by
    rw [hKLdiff]
    intro hzero
    rcases smul_eq_zero.mp hzero with h1 | h1
    · exact hκμne h1
    · exact he h1
  have horth'' : ⟪K - L, w⟫ = 0 := by
    rw [hKLdiff, real_inner_smul_left, horth, mul_zero]
  have hμ₂κ₂ : (α - μ) / (κ - μ) < (α - k - μ) / (κ - μ) := by
    rw [div_lt_iff₀ hκμ', div_mul_cancel₀ _ hκμne]
    linarith [hkneg]
  -- Piece 1 `(A, B, K, L)` is a cyclic quadrilateral.
  have hcyc0 : CyclicQuad A B K L :=
    trapezoid_cyclic₀ hB hK hL he hw horth hμκ hκμ hww inner_eeww sq_norm_eq norm_eq_of_sq
  -- Piece 2 `(L, K, C, D)` is a cyclic quadrilateral.
  have hcyc1 : CyclicQuad L K C D :=
    trapezoid_cyclic₁ hK2show hC2 hD2 hK hL hC hD he' hw horth'' hμ₂κ₂ hκμ hα hκeq hμeq hww
      inner_eeww sq_norm_eq norm_eq_of_sq
  -- Inner products of the vertices' displacement vectors (used repeatedly below).
  have hBAm_w : ⟪B - A, w⟫ = 0 := by rw [← he_def]; exact horth
  have hCAm_w : ⟪C - A, w⟫ = ww := by
    rw [hCA, inner_add_left, real_inner_smul_left, horth, mul_zero, zero_add, ← hww_def]
  have hDAm_w : ⟪D - A, w⟫ = ww := by
    rw [hDA, inner_add_left, real_inner_smul_left, horth, mul_zero, zero_add, ← hww_def]
  have hBAm_e : ⟪B - A, e⟫ = ee := by rw [← he_def, ← hee_def]
  have hCAm_e : ⟪C - A, e⟫ = (α - k) * ee := by
    rw [hCA, inner_add_left, real_inner_smul_left, horth', add_zero, ← hee_def]
  have hDAm_e : ⟪D - A, e⟫ = α * ee := by
    rw [hDA, inner_add_left, real_inner_smul_left, horth', add_zero, ← hee_def]
  -- Membership of all six points in the original region, giving the `subset` field.
  have hAmem : A ∈ convexHull ℝ ({A, B, C, D} : Set Plane) :=
    subset_convexHull ℝ _ (Set.mem_insert A {B, C, D})
  have hBmem : B ∈ convexHull ℝ ({A, B, C, D} : Set Plane) :=
    subset_convexHull ℝ _ (Set.mem_insert_of_mem A (Set.mem_insert B {C, D}))
  have hCmem : C ∈ convexHull ℝ ({A, B, C, D} : Set Plane) :=
    subset_convexHull ℝ _ (Set.mem_insert_of_mem A (Set.mem_insert_of_mem B
      (Set.mem_insert C {D})))
  have hDmem : D ∈ convexHull ℝ ({A, B, C, D} : Set Plane) :=
    subset_convexHull ℝ _ (Set.mem_insert_of_mem A (Set.mem_insert_of_mem B
      (Set.mem_insert_of_mem C (Set.mem_singleton D))))
  have hKmem : K ∈ convexHull ℝ ({A, B, C, D} : Set Plane) :=
    Convex.segment_subset (convex_convexHull ℝ _) hBmem hCmem
      ⟨(1 / 2 : ℝ), (1 / 2 : ℝ), by norm_num, by norm_num, by norm_num, by rw [hKhalf]⟩
  have hLmem : L ∈ convexHull ℝ ({A, B, C, D} : Set Plane) :=
    Convex.segment_subset (convex_convexHull ℝ _) hAmem hDmem
      ⟨(1 / 2 : ℝ), (1 / 2 : ℝ), by norm_num, by norm_num, by norm_num, by rw [hLhalf]⟩
  have hsubset0 : quadRegion A B K L ⊆ quadRegion A B C D := by
    apply convexHull_min _ (convex_convexHull ℝ _)
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact hAmem
    · exact hBmem
    · exact hKmem
    · exact hLmem
  have hsubset1 : quadRegion L K C D ⊆ quadRegion A B C D := by
    apply convexHull_min _ (convex_convexHull ℝ _)
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact hLmem
    · exact hKmem
    · exact hCmem
    · exact hDmem
  -- The `cover` field: every point of the region lies in one of the two pieces.
  have hcover : ∀ X ∈ quadRegion A B C D,
      X ∈ quadRegion A B K L ∨ X ∈ quadRegion L K C D := by
    intro X hX
    have hAB : A ≠ B := fun hEq ↦ he (by rw [he_def, hEq, sub_self])
    have hAC : A ≠ C := fun hEq ↦ h.convex.not_mem₁ (by
      rw [hEq]
      exact subset_convexHull ℝ _ (Set.mem_insert_of_mem B (Set.mem_insert C {D})))
    have hAD : A ≠ D := fun hEq ↦ h.convex.not_mem₁ (by
      rw [hEq]
      exact subset_convexHull ℝ _ (Set.mem_insert_of_mem B (Set.mem_insert_of_mem C
        (Set.mem_singleton D))))
    have hBC : B ≠ C := fun hEq ↦ h.convex.not_mem₂ (by
      rw [hEq]
      exact subset_convexHull ℝ _ (Set.mem_insert C {D, A}))
    have hBD : B ≠ D := fun hEq ↦ h.convex.not_mem₂ (by
      rw [hEq]
      exact subset_convexHull ℝ _ (Set.mem_insert_of_mem C (Set.mem_insert D {A})))
    have hCD : C ≠ D := fun hEq ↦ h.convex.not_mem₃ (by
      rw [hEq]
      exact subset_convexHull ℝ _ (Set.mem_insert D {A, B}))
    have hset : ({A, B, C, D} : Set Plane) = (({A, B, C, D} : Finset Plane) : Set Plane) :=
      by simp
    change X ∈ convexHull ℝ ({A, B, C, D} : Set Plane) at hX
    rw [hset] at hX
    obtain ⟨c, hc0, hc1, hcX⟩ := Finset.mem_convexHull'.mp hX
    have hA_not : A ∉ ({B, C, D} : Finset Plane) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hAB, hAC, hAD⟩
    have hB_not : B ∉ ({C, D} : Finset Plane) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hBC, hBD⟩
    have hC_not : C ∉ ({D} : Finset Plane) := by
      simp only [Finset.mem_singleton]; exact hCD
    have hXAm : X - A = c B • (B - A) + (c C • (C - A) + c D • (D - A)) := by
      have hcongr : ∀ y ∈ ({A, B, C, D} : Finset Plane), c y • (y - A) = c y • y - c y • A :=
        fun y _ ↦ smul_sub (c y) y A
      have hsub : ∑ y ∈ ({A, B, C, D} : Finset Plane), c y • (y - A) = X - A := by
        rw [Finset.sum_congr rfl hcongr, Finset.sum_sub_distrib, hcX, ← Finset.sum_smul,
          hc1, one_smul]
      rw [Finset.sum_insert hA_not, Finset.sum_insert hB_not, Finset.sum_insert hC_not,
        Finset.sum_singleton, sub_self, smul_zero, zero_add] at hsub
      exact hsub.symm
    rw [Finset.sum_insert hA_not, Finset.sum_insert hB_not, Finset.sum_insert hC_not,
      Finset.sum_singleton] at hc1
    have hcA : 0 ≤ c A := hc0 A (Finset.mem_insert_self A {B, C, D})
    have hcB : 0 ≤ c B := hc0 B (Finset.mem_insert_of_mem (Finset.mem_insert_self B {C, D}))
    have hcC : 0 ≤ c C := hc0 C (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_insert_self C {D})))
    have hcD : 0 ≤ c D := hc0 D (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self D))))
    set s := ⟪X - A, w⟫ / ww with hs_def
    set ξ := ⟪X - A, e⟫ / ee with hξ_def
    clear_value s ξ
    have hsw : ⟪X - A, w⟫ = (c C + c D) * ww := by
      rw [hXAm, inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
        real_inner_smul_left, hBAm_w, hCAm_w, hDAm_w]
      ring
    have hse : ⟪X - A, e⟫ = (c B + c C * (α - k) + c D * α) * ee := by
      rw [hXAm, inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
        real_inner_smul_left, hBAm_e, hCAm_e, hDAm_e]
      ring
    have hs_val : s = c C + c D := by
      rw [hs_def, hsw]
      exact mul_div_cancel_right₀ _ hww.ne'
    have hξ_val : ξ = c B + c C * (α - k) + c D * α := by
      rw [hξ_def, hse]
      exact mul_div_cancel_right₀ _ hee.ne'
    have hs0 : 0 ≤ s := by rw [hs_val]; exact add_nonneg hcC hcD
    have hs1 : s ≤ 1 := by
      rw [hs_val, ← hc1, show c A + (c B + (c C + c D)) = (c A + c B) + (c C + c D) by ring]
      exact le_add_of_nonneg_left (add_nonneg hcA hcB)
    have hξl : s * α ≤ ξ := by
      rw [hξ_val, hs_val]
      have h1 : 0 ≤ c C * (-k) := mul_nonneg hcC (neg_nonneg.mpr hkneg.le)
      have h2 : (c C + c D) * α + (c B + c C * (-k)) = c B + c C * (α - k) + c D * α := by
        ring
      rw [← h2]
      exact le_add_of_nonneg_right (add_nonneg hcB h1)
    have hξu : ξ ≤ 1 + s * (α - k - 1) := by
      rw [hξ_val, hs_val]
      have h1 : 0 ≤ c D * (-k) := mul_nonneg hcD (neg_nonneg.mpr hkneg.le)
      have h2 : (1 : ℝ) + (c C + c D) * (α - k - 1) =
          (c B + c C * (α - k) + c D * α) + (c A + c D * (-k)) := by
        linear_combination -hc1
      rw [h2]
      exact le_add_of_nonneg_right (add_nonneg hcA h1)
    have hXeq : X = A + ξ • e + s • w := by
      have h1 := eq_smul_add_smul_of_ortho he hw horth (X - A)
      rw [← hee_def, ← hww_def, ← hξ_def, ← hs_def] at h1
      rw [show A + ξ • e + s • w = A + (ξ • e + s • w) by abel, ← h1]
      abel
    have hXeq2 : X = L + ((ξ - μ) / (κ - μ)) • (K - L) + (s - 1 / 2) • w := by
      rw [hKLdiff]
      rw [show ((ξ - μ) / (κ - μ)) • ((κ - μ) • e) = (ξ - μ) • e by
        rw [smul_smul, div_mul_cancel₀ _ hκμne]]
      rw [hXeq, hL]; module
    have hb1 : s / (1 / 2 : ℝ) * μ = s * α := by
      rw [hμeq, hα, div_mul_eq_mul_div, div_eq_iff (by norm_num : (1 / 2 : ℝ) ≠ 0)]
      ring
    have hb2 : 1 + s / (1 / 2 : ℝ) * (κ - 1) = 1 + s * (α - k - 1) := by
      rw [add_left_cancel_iff, hκeq, hα, div_mul_eq_mul_div,
        div_eq_iff (by norm_num : (1 / 2 : ℝ) ≠ 0)]
      ring
    rcases lt_or_ge s (1 / 2) with hshalf | hshalf
    · left
      show X ∈ convexHull ℝ {A, B, K, L}
      rw [hB, hK, hL, hXeq]
      refine mem_convexHull_trapezoid_band (by norm_num) hμκ hs0 hshalf.le ?_ ?_
      · rw [hb1]; exact hξl
      · rw [hb2]; exact hξu
    · right
      show X ∈ convexHull ℝ {L, K, C, D}
      rw [hK2show, hC2, hD2, hXeq2]
      refine mem_convexHull_trapezoid_band (by norm_num) hμ₂κ₂ (sub_nonneg.mpr hshalf)
        (by rw [sub_le_iff_le_add, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num]; exact hs1) ?_ ?_
      · have hs2 : (s - 1 / 2 : ℝ) / (1 / 2) = 2 * s - 1 := by
          rw [div_eq_iff (by norm_num : (1 / 2 : ℝ) ≠ 0)]; ring
        have hbound1 : (2 * s - 1) * (α - μ) = s * α - μ := by
          rw [hμeq, hα]; ring
        rw [hs2, ← mul_div_assoc, div_le_iff₀ hκμ', div_mul_cancel₀ _ hκμne, hbound1]
        exact sub_le_sub_right hξl μ
      · have hs2 : (s - 1 / 2 : ℝ) / (1 / 2) = 2 * s - 1 := by
          rw [div_eq_iff (by norm_num : (1 / 2 : ℝ) ≠ 0)]; ring
        have hκ₂1 : (α - k - μ) / (κ - μ) - 1 = (α - k - κ) / (κ - μ) := by
          rw [eq_div_iff_mul_eq hκμne, sub_mul, div_mul_cancel₀ _ hκμne]; ring
        have hcomb : (1 : ℝ) + (2 * s - 1) * (α - k - κ) / (κ - μ) =
            ((κ - μ) + (2 * s - 1) * (α - k - κ)) / (κ - μ) := by
          rw [eq_div_iff_mul_eq hκμne, add_mul, div_mul_cancel₀ _ hκμne, one_mul]
        have hbound2 : (κ - μ) + (2 * s - 1) * (α - k - κ) = (1 + s * (α - k - 1)) - μ := by
          rw [hκeq, hμeq, hα]; ring
        rw [hs2, hκ₂1, ← mul_div_assoc, hcomb, div_le_iff₀ hκμ', div_mul_cancel₀ _ hκμne,
          hbound2]
        exact sub_le_sub_right hξu μ
  have hdisj01 : Disjoint (interior (quadRegion A B K L))
      (interior (quadRegion L K C D)) :=
    trapezoid_disjoint hBAm_w hCAm_w hDAm_w hww hww_def horth hK hL
  -- Both pieces are isosceles trapezoids.
  clear he hee hee_def hα_def hw_def horth hw hCA hDA hCB hww hww_def horth' inner_ew1
    hnormCB hnormDA hquad hlegs hkneg hKdef hLdef hKhalf hLhalf hκμ hμκ hκμ' hK2show
    hC2 hD2 he' horth'' hμ₂κ₂ hBAm_w hCAm_w hDAm_w hBAm_e hCAm_e hDAm_e hAmem hBmem
    hCmem hDmem hKmem hLmem
  have hpar0 : ∃ k' : ℝ, L - K = k' • (B - A) :=
    ⟨μ - κ, by rw [hL, hK, ← he_def]; module⟩
  have hlegs0 : dist B K = dist A L := by
    rw [dist_eq_norm, dist_eq_norm]
    apply norm_eq_of_sq
    rw [sq_norm_eq, sq_norm_eq]
    rw [show B - K = (1 - κ) • e + (-1 / 2 : ℝ) • w by rw [hB, hK]; module]
    rw [show A - L = (-μ) • e + (-1 / 2 : ℝ) • w by rw [hL]; module]
    rw [inner_eeww, inner_eeww]
    have hsq : (1 - κ) ^ 2 = μ ^ 2 := by rw [hκeq, hμeq]; ring
    rw [hsq]; ring
  have hpar1 : ∃ k' : ℝ, D - C = k' • (K - L) := by
    refine ⟨k / (κ - μ), ?_⟩
    rw [hKLdiff, hk, smul_smul, div_mul_cancel₀ _ hκμne]
  have hlegs1 : dist K C = dist L D := by
    rw [dist_eq_norm, dist_eq_norm]
    apply norm_eq_of_sq
    rw [sq_norm_eq, sq_norm_eq]
    rw [show K - C = (κ - (α - k)) • e + (-1 / 2 : ℝ) • w by rw [hK, hC]; module]
    rw [show L - D = (μ - α) • e + (-1 / 2 : ℝ) • w by rw [hL, hD]; module]
    rw [inner_eeww, inner_eeww]
    have hsq : (κ - (α - k)) ^ 2 = (μ - α) ^ 2 := by rw [hκeq, hμeq, hα]; ring
    rw [hsq]
  -- Assemble the dissection.
  refine ⟨⟨![(A, B, K, L), (L, K, C, D)], ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro i
    fin_cases i
    · show CyclicQuad A B K L
      exact hcyc0
    · show CyclicQuad L K C D
      exact hcyc1
  · intro i
    fin_cases i
    · show quadRegion A B K L ⊆ quadRegion A B C D
      exact hsubset0
    · show quadRegion L K C D ⊆ quadRegion A B C D
      exact hsubset1
  · intro X hX
    rcases hcover X hX with h1 | h1
    · exact Set.mem_iUnion.mpr ⟨0, h1⟩
    · exact Set.mem_iUnion.mpr ⟨1, h1⟩
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact hdisj01
    · exact hdisj01.symm
    · exact absurd rfl hij
  · intro k
    fin_cases k
    · show IsoscelesTrapezoid A B K L
      exact ⟨hcyc0.convex, hpar0, hlegs0⟩
    · show IsoscelesTrapezoid L K C D
      exact ⟨hcyc1.convex, hpar1, hlegs1⟩

/-- Every cyclic quadrilateral admits, for every `n ≥ 4`, a dissection into `n` cyclic
quadrilaterals one of which is an isosceles trapezoid: induction on `n`, subdividing a
trapezoid piece at each step. -/
theorem dissection_with_trapezoid {n : ℕ} (hn : 4 ≤ n) {A B C D : Plane}
    (h : CyclicQuad A B C D) : DissectionWithTrapezoid A B C D n := by
  induction n, hn using Nat.le_induction with
  | base => exact dissection_four h
  | succ m hm ih =>
    obtain ⟨d, i, htrap⟩ := ih
    obtain ⟨e, he⟩ := trapezoid_split htrap (d.cyclic i)
    refine ⟨d.succ i rfl e, ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩, ?_⟩
    have hp : (d.succ i rfl e).pieces = succPieces d i e := rfl
    rw [hp]
    rcases succPieces_spec d i e ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ with
      ⟨hs, hw⟩ | ⟨hs, hw⟩ | ⟨j', hj, hne, hw⟩
    · rw [hw]; exact he 0
    · change i.val = m at hs; have := i.isLt; omega
    · exact absurd (Fin.ext hj) hne

/-- Every cyclic quadrilateral admits a dissection into `n` cyclic quadrilaterals for every
`n ≥ 4`. -/
theorem exists_cyclicDissection {n : ℕ} (hn : 4 ≤ n) {A B C D : Plane}
    (h : CyclicQuad A B C D) : Nonempty (CyclicDissection A B C D n) := by
  obtain ⟨d, -, -⟩ := dissection_with_trapezoid hn h
  exact ⟨d⟩

snip end

problem imo1972_p2 {n : ℕ} (hn : 4 < n) (A B C D : Plane) (h : CyclicQuad A B C D) :
    Nonempty (CyclicDissection A B C D n) :=
  exists_cyclicDissection (Nat.le_of_lt hn) h

end Imo1972P2
