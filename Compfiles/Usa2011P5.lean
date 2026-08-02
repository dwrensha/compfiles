/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
public import Mathlib.Geometry.Euclidean.Triangle
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# USA Mathematical Olympiad 2011, Problem 5

Let P be a point inside convex quadrilateral ABCD. Points Q₁ and Q₂ are located
within ABCD such that
∠Q₁BC = ∠ABP,
∠Q₁CB = ∠DCP,
∠Q₂AD = ∠BAP,
∠Q₂DA = ∠CDP.
Prove that Q₁Q₂ ∥ AB if and only if Q₁Q₂ ∥ CD.
-/

namespace Usa2011P5

open scoped EuclideanGeometry Real
open EuclideanGeometry Affine

local instance planeFiniteDim :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) :=
  ⟨finrank_euclideanSpace_fin⟩

noncomputable local instance someOrientation :
    Module.Oriented ℝ (EuclideanSpace ℝ (Fin 2)) (Fin 2) :=
  ⟨Module.Basis.orientation (Module.finBasisOfFinrankEq _ _ planeFiniteDim.out)⟩

abbrev Pt := EuclideanSpace ℝ (Fin 2)

/-- `ConvexQuad A B C D` says that the four points `A`, `B`, `C`, `D` are the vertices
of a (strictly) convex quadrilateral, listed in cyclic order: for the line through each
side, the other two vertices lie strictly on the same side. -/
def ConvexQuad (A B C D : Pt) : Prop :=
  line[ℝ, A, B].SSameSide C D ∧ line[ℝ, B, C].SSameSide D A ∧
    line[ℝ, C, D].SSameSide A B ∧ line[ℝ, D, A].SSameSide B C

/-- `InsideQuad A B C D M` says that `M` lies strictly inside the convex quadrilateral
`ABCD`: for the line through each side, `M` lies strictly on the same side as the
interior of the quadrilateral. -/
def InsideQuad (A B C D M : Pt) : Prop :=
  line[ℝ, A, B].SSameSide M C ∧ line[ℝ, B, C].SSameSide M A ∧
    line[ℝ, C, D].SSameSide M B ∧ line[ℝ, D, A].SSameSide M C

snip begin

/-! ### Affine-line infrastructure -/

lemma eq_max_of_max_ne_top
    {A B : Submodule ℝ Pt}
    (hA : Module.finrank ℝ A = 1)
    (h : A ⊔ B ≠ ⊤) : A = A ⊔ B := by
  apply Submodule.eq_of_le_of_finrank_eq le_sup_left
  rw [hA]
  have hAB := Submodule.finrank_le (A ⊔ B)
  rw [planeFiniteDim.out] at hAB
  have hAB' : 1 ≤ Module.finrank ℝ ↥(A ⊔ B) := by
    simp_rw [← hA]
    exact Submodule.finrank_mono le_sup_left
  have hAB'' : Module.finrank ℝ ↥(A ⊔ B) ≠ 2 := by
    contrapose! h
    apply Submodule.eq_top_of_finrank_eq
    rw [planeFiniteDim.out, h]
  interval_cases Module.finrank ℝ ↥(A ⊔ B) <;> lia

lemma affineSpan_pair_finrank {A B : Pt}
    (hAB : A ≠ B) : Module.finrank ℝ (affineSpan ℝ {A, B}).direction = 1 := by
  rw [direction_affineSpan]
  have h := affineIndependent_of_ne ℝ hAB
  have h' : Set.range ![A, B] = {A, B} := by
    simp
    rw [Set.pair_comm]
  rw [← h']
  apply AffineIndependent.finrank_vectorSpan h
  simp

lemma inter_nonempty_of_not_parallel
    {A₁ A₂ B₁ B₂ : Pt}
    (hA : A₁ ≠ A₂) (hB : B₁ ≠ B₂)
    (h : ¬line[ℝ, A₁, A₂] ∥ line[ℝ, B₁, B₂]) :
    Set.Nonempty ((line[ℝ, A₁, A₂] : Set Pt) ∩ (line[ℝ, B₁, B₂] : Set Pt)) := by
  have hA' : (line[ℝ, A₁, A₂] : Set Pt).Nonempty := by
    use A₁
    apply mem_affineSpan
    simp
  have hB' : (line[ℝ, B₁, B₂] : Set Pt).Nonempty := by
    use B₁
    apply mem_affineSpan
    simp
  apply AffineSubspace.inter_nonempty_of_nonempty_of_sup_direction_eq_top hA' hB'
  contrapose! h
  rw [AffineSubspace.parallel_iff_direction_eq_and_eq_bot_iff_eq_bot]
  constructor
  · set A := (affineSpan ℝ {A₁, A₂}).direction
    set B := (affineSpan ℝ {B₁, B₂}).direction
    trans A ⊔ B
    · exact eq_max_of_max_ne_top (affineSpan_pair_finrank hA) h
    · symm
      rw [sup_comm] at *
      exact eq_max_of_max_ne_top (affineSpan_pair_finrank hB) h
  · rw [affineSpan_eq_bot, affineSpan_eq_bot]
    constructor <;> intro h' <;> contrapose! h' <;> simp

lemma mem_affineSpan_pair_of_collinear {A B C : Pt}
    (hBC : B ≠ C) (h : Collinear ℝ {A, B, C}) :
    A ∈ affineSpan ℝ {B, C} := by
  apply Collinear.mem_affineSpan_of_mem_of_ne h (by simp) (by simp) (by simp) hBC

/-- Rotating a triple of points preserves collinearity. -/
lemma collinear_rot {a b c : Pt} (h : Collinear ℝ ({a, b, c} : Set Pt)) :
    Collinear ℝ ({c, a, b} : Set Pt) := by
  rwa [Set.insert_comm c a, Set.pair_comm c b]

/-- Swapping the first two points of a triple preserves collinearity. -/
lemma collinear_swap {a b c : Pt} (h : Collinear ℝ ({a, b, c} : Set Pt)) :
    Collinear ℝ ({b, a, c} : Set Pt) := by
  rwa [Set.insert_comm b a]

/-- Swapping the last two points of a triple preserves collinearity. -/
lemma collinear_swap₂₃ {a b c : Pt} (h : Collinear ℝ ({a, b, c} : Set Pt)) :
    Collinear ℝ ({a, c, b} : Set Pt) := by
  rwa [Set.pair_comm c b]

/-- Rotating a triple of points preserves non-collinearity. -/
lemma not_collinear_rot {a b c : Pt} (h : ¬Collinear ℝ ({a, b, c} : Set Pt)) :
    ¬Collinear ℝ ({c, a, b} : Set Pt) := fun hc => h (collinear_rot (collinear_rot hc))

/-- Swapping the first two points of a triple preserves non-collinearity. -/
lemma not_collinear_swap {a b c : Pt} (h : ¬Collinear ℝ ({a, b, c} : Set Pt)) :
    ¬Collinear ℝ ({b, a, c} : Set Pt) := fun hc => h (collinear_swap hc)

/-- Three points with the third not on the line through the first two are not
collinear. -/
lemma not_collinear_of_not_mem {U V W : Pt} (hUV : U ≠ V) (h : W ∉ line[ℝ, U, V]) :
    ¬Collinear ℝ ({U, V, W} : Set Pt) :=
  fun hc => h (mem_affineSpan_pair_of_collinear hUV (collinear_rot hc))

/-- If three points are not collinear, the third is not on the line through the first
two. -/
lemma not_mem_of_not_collinear {U V W : Pt} (h : ¬Collinear ℝ ({U, V, W} : Set Pt)) :
    W ∉ line[ℝ, U, V] :=
  fun hW =>
    h (collinear_rot (collinear_rot
      ((collinear_insert_iff_of_mem_affineSpan hW).2 (collinear_pair ℝ U V))))

lemma collinear_of_mem {U V W : Pt} (h : W ∈ line[ℝ, U, V]) :
    Collinear ℝ ({U, V, W} : Set Pt) :=
  collinear_rot (collinear_rot ((collinear_insert_iff_of_mem_affineSpan h).2
    (collinear_pair ℝ U V)))

/-! ### Sines of unoriented angles via oriented angles -/

/-- The sine of an unoriented angle is the absolute value of the sine of the oriented
angle. -/
lemma sin_angle_eq_abs_sin_oangle {p₁ p₂ p₃ : Pt} (h₁ : p₁ ≠ p₂) (h₃ : p₃ ≠ p₂) :
    Real.sin (∠ p₁ p₂ p₃) = |Real.Angle.sin (∡ p₁ p₂ p₃)| := by
  have hle : |(∡ p₁ p₂ p₃).toReal| ≤ π :=
    abs_le.2 ⟨(Real.Angle.toReal_mem_Ioc _).1.le, Real.Angle.toReal_le_pi _⟩
  rw [angle_eq_abs_oangle_toReal h₁ h₃, ← Real.abs_sin_eq_sin_abs_of_abs_le_pi hle,
    Real.Angle.sin_toReal]

/-- If `B` is strictly between `X` and `A`, the angles `∠XBM` and `∠MBA` are
supplementary, so they have the same sine. -/
lemma sin_angle_eq_sin_angle_of_sbtw {X B A M : Pt} (h : Sbtw ℝ X B A) (hM : M ≠ B) :
    Real.sin (∠ X B M) = Real.sin (∠ M B A) := by
  rw [sin_angle_eq_abs_sin_oangle h.left_ne hM, sin_angle_eq_abs_sin_oangle hM h.right_ne,
    ← oangle_add h.left_ne h.right_ne hM, h.oangle₁₂₃_eq_pi, add_comm (π : Real.Angle) _,
    Real.Angle.sin_add_pi, abs_neg, oangle_rev A B M, Real.Angle.sin_neg, abs_neg]

/-! ### Signs of oriented angles from same-side hypotheses -/

/-- If `M` and `W` are strictly on the same side of the line through `U` and `V`, then
the oriented angles `∡UVM` and `∡UVW` have the same sign. -/
lemma oangle_sign_left_of_sSameSide {U V M W : Pt} (_hUV : U ≠ V)
    (h : line[ℝ, U, V].SSameSide M W) :
    (∡ U V M).sign = (∡ U V W).sign := by
  rw [← oangle_rotate_sign U V M, ← oangle_rotate_sign U V W]
  exact AffineSubspace.SSameSide.oangle_sign_eq
    (right_mem_affineSpan_pair ℝ U V) (left_mem_affineSpan_pair ℝ U V) h.symm

/-- If `M` and `U` are strictly on the same side of the line through `V` and `W`, then
the oriented angles `∡MVW` and `∡UVW` have the same sign. -/
lemma oangle_sign_right_of_sSameSide {U V M W : Pt} (_hVW : V ≠ W)
    (h : line[ℝ, V, W].SSameSide M U) :
    (∡ M V W).sign = (∡ U V W).sign := by
  have h' : line[ℝ, W, V].SSameSide M U := by rwa [AffineSubspace.affineSpan_pair_comm]
  have h1 : (∡ W V M).sign = (∡ W V U).sign := oangle_sign_left_of_sSameSide _hVW.symm h'
  rw [oangle_rev W V M, Real.Angle.sign_neg, h1, oangle_rev U V W, Real.Angle.sign_neg,
    neg_neg]

/-- If the two pieces of the angle `∠UVW` cut by the ray `VM` make oriented angles of
the same nonzero sign as `∡UVW`, then `∠UVM + ∠MVW = ∠UVW`. -/
lemma angle_add_of_sign_eq {U V M W : Pt} (hU : U ≠ V) (hM : M ≠ V) (hW : W ≠ V)
    (h0 : (∡ U V W).sign ≠ 0)
    (h₁ : (∡ U V M).sign = (∡ U V W).sign)
    (h₂ : (∡ M V W).sign = (∡ U V W).sign) :
    ∠ U V M + ∠ M V W = ∠ U V W := by
  have hadd : ∡ U V M + ∡ M V W = ∡ U V W := oangle_add hU hM hW
  have hnπ₁ : ∡ U V M ≠ π := by
    intro hpi
    have hs : (∡ U V M).sign = 0 := Real.Angle.sign_eq_zero_iff.2 (Or.inr hpi)
    exact h0 (h₁.symm.trans hs)
  have hnπ₂ : ∡ M V W ≠ π := by
    intro hpi
    have hs : (∡ M V W).sign = 0 := Real.Angle.sign_eq_zero_iff.2 (Or.inr hpi)
    exact h0 (h₂.symm.trans hs)
  have htr : (∡ U V M + ∡ M V W).toReal = (∡ U V M).toReal + (∡ M V W).toReal :=
    Real.Angle.toReal_add_eq_toReal_add_toReal hnπ₁ hnπ₂ (Or.inr (by rw [hadd, ← h₁]))
  obtain (hs | hs | hs) := (∡ U V W).sign.trichotomy
  · have s1 : (∡ U V M).sign = -1 := h₁.trans hs
    have s2 : (∡ M V W).sign = -1 := h₂.trans hs
    have t1 := Real.Angle.toReal_neg_iff_sign_neg.2 s1
    have t2 := Real.Angle.toReal_neg_iff_sign_neg.2 s2
    have t3 := Real.Angle.toReal_neg_iff_sign_neg.2 hs
    rw [angle_eq_abs_oangle_toReal hU hM, angle_eq_abs_oangle_toReal hM hW,
      angle_eq_abs_oangle_toReal hU hW, abs_of_neg t1, abs_of_neg t2, abs_of_neg t3,
      ← hadd, htr]
    ring
  · exact absurd hs h0
  · have s1 : (∡ U V M).sign = 1 := h₁.trans hs
    have s2 : (∡ M V W).sign = 1 := h₂.trans hs
    have t1 := Real.Angle.toReal_mem_Ioo_iff_sign_pos.2 s1
    have t2 := Real.Angle.toReal_mem_Ioo_iff_sign_pos.2 s2
    have t3 := Real.Angle.toReal_mem_Ioo_iff_sign_pos.2 hs
    rw [angle_eq_abs_oangle_toReal hU hM, angle_eq_abs_oangle_toReal hM hW,
      angle_eq_abs_oangle_toReal hU hW, abs_of_pos t1.1, abs_of_pos t2.1, abs_of_pos t3.1,
      ← hadd, htr]

/-! ### The trigonometric core -/

/-- The pure trigonometric chase behind both isogonal computations: three applications
of the law of sines in the triangles `XBM`, `XCM`, `BCM`. -/
lemma sine_chase {X B C M : Pt} (hbm : B ≠ M) (hcm : C ≠ M) (hxm : X ≠ M) :
    Real.sin (∠ M X C) * Real.sin (∠ X B M) * Real.sin (∠ B C M) =
      Real.sin (∠ B X M) * Real.sin (∠ M B C) * Real.sin (∠ X C M) := by
  have h1 : Real.sin (∠ X B M) * dist B M = Real.sin (∠ M X B) * dist M X := law_sin X B M
  have h2 : Real.sin (∠ X C M) * dist C M = Real.sin (∠ M X C) * dist M X := law_sin X C M
  have h3 : Real.sin (∠ B C M) * dist C M = Real.sin (∠ M B C) * dist M B := law_sin B C M
  rw [angle_comm M X B] at h1
  rw [dist_comm M B] at h3
  have dpos : dist B M * dist C M * dist M X ≠ 0 := by
    simp [dist_ne_zero.mpr hbm, dist_ne_zero.mpr hcm, dist_ne_zero.mpr hxm.symm]
  have e1 : Real.sin (∠ M X C) * Real.sin (∠ X B M) * Real.sin (∠ B C M) *
        (dist B M * dist C M * dist M X) =
      Real.sin (∠ B X M) * Real.sin (∠ M B C) * Real.sin (∠ X C M) *
        (dist B M * dist C M * dist M X) := by
    linear_combination
      (Real.sin (∠ M X C) * Real.sin (∠ B C M) * dist C M * dist M X) * h1 +
        (- Real.sin (∠ B X M) * Real.sin (∠ M B C) * dist B M * dist M X) * h2 +
        (Real.sin (∠ M X C) * Real.sin (∠ B X M) * dist M X * dist M X) * h3
  exact mul_right_cancel₀ dpos e1

/-- From `sin (θ - φ) * sin (θ - ψ) = sin φ * sin ψ` with `φ, ψ ∈ (0, θ)` and
`θ ∈ (0, π)`, deduce `ψ = θ - φ`: the direction from the vertex is determined by the
sine ratio. -/
lemma eq_of_sin_mul_sin {θ φ ψ : ℝ} (hθ0 : 0 < θ) (hθπ : θ < π)
    (hφ0 : 0 < φ) (hφθ : φ < θ) (hψ0 : 0 < ψ) (hψθ : ψ < θ)
    (h : Real.sin (θ - φ) * Real.sin (θ - ψ) = Real.sin φ * Real.sin ψ) : ψ = θ - φ := by
  have e1 := Real.cos_sub (θ - φ) (θ - ψ)
  have e2 := Real.cos_add (θ - φ) (θ - ψ)
  have e3 := Real.cos_sub φ ψ
  have e4 := Real.cos_add φ ψ
  rw [show (θ - φ) - (θ - ψ) = ψ - φ by ring, show ψ - φ = -(φ - ψ) by ring,
    Real.cos_neg] at e1
  rw [show (θ - φ) + (θ - ψ) = 2 * θ - (φ + ψ) by ring] at e2
  have hcos : Real.cos (2 * θ - (φ + ψ)) = Real.cos (φ + ψ) := by
    linarith [e1, e2, e3, e4, h]
  rw [Real.cos_eq_cos_iff] at hcos
  obtain ⟨k, hk | hk⟩ := hcos
  · -- `φ + ψ = 2kπ + (2θ - (φ + ψ))`, so `φ + ψ - θ = kπ` and hence `k = 0`
    have h1 : φ + ψ - θ = k * π := by linarith [hk]
    rcases eq_or_ne k 0 with rfl | hkne
    · simp at h1
      linarith [h1]
    · exfalso
      have h3 : |φ + ψ - θ| < π := by
        rw [abs_lt]
        constructor <;> linarith [Real.pi_pos]
      rw [h1, abs_mul, abs_of_pos Real.pi_pos] at h3
      have h4 : (1 : ℝ) ≤ |(k : ℝ)| := by
        have hkk := Int.one_le_abs hkne
        rw [← Int.cast_abs]
        exact_mod_cast hkk
      have h5 : (0 : ℝ) ≤ (|(k : ℝ)| - 1) * π := mul_nonneg (by linarith [h4]) Real.pi_pos.le
      linarith [h3, h5]
  · -- `φ + ψ = 2kπ - (2θ - (φ + ψ))`, so `θ = kπ`, which is impossible
    have h1 : θ = k * π := by linarith [hk]
    rcases eq_or_ne k 0 with rfl | hkne
    · simp at h1
      linarith [Real.pi_pos, hθ0]
    · have h4 : (1 : ℝ) ≤ |(k : ℝ)| := by
        have hkk := Int.one_le_abs hkne
        rw [← Int.cast_abs]
        exact_mod_cast hkk
      have h3 : π ≤ |k * π| := by
        rw [abs_mul, abs_of_pos Real.pi_pos]
        have h5 : (0 : ℝ) ≤ (|(k : ℝ)| - 1) * π := mul_nonneg (by linarith [h4]) Real.pi_pos.le
        linarith [h5]
      rw [← h1, abs_of_pos hθ0] at h3
      linarith [h3, hθπ]


/-! ### The intersection point of lines `AB` and `CD` -/

/-- If lines `AB` and `CD` are not parallel, they meet at a point `X` outside both
segments; convexity forces `X` to lie either beyond both of `B, C` or beyond both of
`A, D`. -/
lemma exists_sbtw_inter_of_convexQuad {A B C D : Pt} (hconv : ConvexQuad A B C D)
    (hA : A ≠ B) (hC : C ≠ D) (hpar : ¬line[ℝ, A, B] ∥ line[ℝ, C, D]) :
    ∃ X, X ∈ line[ℝ, A, B] ∧ X ∈ line[ℝ, C, D] ∧
      ((Sbtw ℝ A B X ∧ Sbtw ℝ X C D) ∨ (Sbtw ℝ X A B ∧ Sbtw ℝ C D X)) := by
  obtain ⟨hAB, hBC, hCD, hDA⟩ := hconv
  obtain ⟨X, hXAB, hXCD⟩ := inter_nonempty_of_not_parallel hA hC hpar
  have hXnsegAB : ¬Wbtw ℝ A X B := fun hw =>
    AffineSubspace.SSameSide.not_wOppSide hCD (hw.wOppSide₁₃ hXCD)
  have hXnsegCD : ¬Wbtw ℝ C X D := fun hw =>
    AffineSubspace.SSameSide.not_wOppSide hAB (hw.wOppSide₁₃ hXAB)
  have hXneA : X ≠ A := by
    intro h
    rw [h] at hXnsegAB
    exact hXnsegAB (mem_segment_iff_wbtw.1 (left_mem_segment ℝ A B))
  have hXneB : X ≠ B := by
    intro h
    rw [h] at hXnsegAB
    exact hXnsegAB (mem_segment_iff_wbtw.1 (right_mem_segment ℝ A B))
  have hXneC : X ≠ C := by
    intro h
    rw [h] at hXnsegCD
    exact hXnsegCD (mem_segment_iff_wbtw.1 (left_mem_segment ℝ C D))
  have hXneD : X ≠ D := by
    intro h
    rw [h] at hXnsegCD
    exact hXnsegCD (mem_segment_iff_wbtw.1 (right_mem_segment ℝ C D))
  have hXnBC : X ∉ line[ℝ, B, C] := by
    intro hXBC
    have h1 : line[ℝ, X, B] = line[ℝ, A, B] := affineSpan_pair_eq_of_left_mem_of_ne hXAB hXneB
    have hXBC' : X ∈ line[ℝ, C, B] := by rwa [AffineSubspace.affineSpan_pair_comm]
    have h2 : line[ℝ, X, B] = line[ℝ, C, B] := affineSpan_pair_eq_of_left_mem_of_ne hXBC' hXneB
    have h3 : line[ℝ, A, B] = line[ℝ, C, B] := h1.symm.trans h2
    have hAmem : A ∈ line[ℝ, C, B] := h3 ▸ left_mem_affineSpan_pair ℝ A B
    rw [AffineSubspace.affineSpan_pair_comm] at hAmem
    exact hBC.right_notMem hAmem
  have hcollAB : Collinear ℝ ({X, A, B} : Set Pt) := collinear_rot (collinear_of_mem hXAB)
  have hcollCD : Collinear ℝ ({X, C, D} : Set Pt) := collinear_rot (collinear_of_mem hXCD)
  obtain h1 | h1 | h1 := hcollAB.wbtw_or_wbtw_or_wbtw
  · -- `X` beyond `A`
    obtain h2 | h2 | h2 := hcollCD.wbtw_or_wbtw_or_wbtw
    · -- `X` beyond `C`: mixed, impossible
      exfalso
      have hsbtw1 : Sbtw ℝ X A B := ⟨h1, hXneA.symm, hA⟩
      have hsbtw2 : Sbtw ℝ X C D := ⟨h2, hXneC.symm, hC⟩
      have hss : line[ℝ, B, C].SSameSide X A :=
        ⟨hsbtw1.wbtw.wSameSide₁₂ (left_mem_affineSpan_pair ℝ B C), hXnBC, hBC.right_notMem⟩
      have hso : line[ℝ, B, C].SOppSide X D :=
        hsbtw2.sOppSide_of_notMem_of_mem hXnBC (right_mem_affineSpan_pair ℝ B C)
      exact AffineSubspace.SSameSide.not_sOppSide hBC.symm
        (AffineSubspace.SSameSide.trans_sOppSide hss.symm hso)
    · -- `X` beyond `D`: valid second case
      exact ⟨X, hXAB, hXCD, Or.inr ⟨⟨h1, hXneA.symm, hA⟩, ⟨h2, hC.symm, hXneD.symm⟩⟩⟩
    · -- `X` inside segment `CD`: impossible
      exact (hXnsegCD (Wbtw.symm h2)).elim
  · -- `X` beyond `B`
    obtain h2 | h2 | h2 := hcollCD.wbtw_or_wbtw_or_wbtw
    · -- `X` beyond `C`: valid first case
      exact ⟨X, hXAB, hXCD, Or.inl ⟨⟨h1, hA.symm, hXneB.symm⟩, ⟨h2, hXneC.symm, hC⟩⟩⟩
    · -- `X` beyond `D`: mixed, impossible
      exfalso
      have hsbtw1 : Sbtw ℝ A B X := ⟨h1, hA.symm, hXneB.symm⟩
      have hsbtw2 : Sbtw ℝ C D X := ⟨h2, hC.symm, hXneD.symm⟩
      have hso : line[ℝ, B, C].SOppSide A X :=
        hsbtw1.sOppSide_of_notMem_of_mem hBC.right_notMem (left_mem_affineSpan_pair ℝ B C)
      have hss : line[ℝ, B, C].SSameSide X D :=
        ⟨hsbtw2.symm.wbtw.wSameSide₁₂ (right_mem_affineSpan_pair ℝ B C), hXnBC, hBC.left_notMem⟩
      exact AffineSubspace.SSameSide.not_sOppSide hBC
        (AffineSubspace.SSameSide.trans_sOppSide hss.symm (AffineSubspace.sOppSide_comm.1 hso))
    · -- `X` inside segment `CD`: impossible
      exact (hXnsegCD (Wbtw.symm h2)).elim
  · -- `X` inside segment `AB`: impossible
    exact (hXnsegAB (Wbtw.symm h1)).elim


/-! ### The geometric core: `X`, `Q₁`, `Q₂` are collinear -/

/-- The geometric core of the problem. Assume `ABCD` is a convex quadrilateral, `P`,
`Q₁`, `Q₂` are inside it, the four angle conditions hold, and lines `AB` and `CD`
meet at `X` beyond `B` and `C` respectively (i.e. `B ∈ (A, X)` and `C ∈ (X, D)`).
Then `X`, `Q₁`, `Q₂` are collinear: the line `Q₁Q₂` is the isogonal of `XP` in the
angle `∠CXB`. The proof is a sine chase in the triangles `XBC`, `XAD`. -/
lemma core_collinear {A B C D P Q₁ Q₂ X : Pt} (hconv : ConvexQuad A B C D)
    (hP : InsideQuad A B C D P) (hQ1 : InsideQuad A B C D Q₁) (hQ2 : InsideQuad A B C D Q₂)
    (hQ1B : ∠ Q₁ B C = ∠ A B P) (hQ1C : ∠ Q₁ C B = ∠ D C P)
    (hQ2A : ∠ Q₂ A D = ∠ B A P) (hQ2D : ∠ Q₂ D A = ∠ C D P)
    (hXAB : Sbtw ℝ A B X) (hXCD : Sbtw ℝ X C D) :
    Collinear ℝ ({X, Q₁, Q₂} : Set Pt) := by
  obtain ⟨hAB, hBC, hCD, hDA⟩ := hconv
  obtain ⟨pAB, pBC, pCD, pDA⟩ := hP
  obtain ⟨q1AB, q1BC, q1CD, q1DA⟩ := hQ1
  obtain ⟨q2AB, q2BC, q2CD, q2DA⟩ := hQ2
  -- non-membership facts
  have CnAB : C ∉ line[ℝ, A, B] := hAB.left_notMem
  have DnAB : D ∉ line[ℝ, A, B] := hAB.right_notMem
  have DnBC : D ∉ line[ℝ, B, C] := hBC.left_notMem
  have AnBC : A ∉ line[ℝ, B, C] := hBC.right_notMem
  have AnCD : A ∉ line[ℝ, C, D] := hCD.left_notMem
  have BnCD : B ∉ line[ℝ, C, D] := hCD.right_notMem
  have BnDA : B ∉ line[ℝ, D, A] := hDA.left_notMem
  have CnDA : C ∉ line[ℝ, D, A] := hDA.right_notMem
  -- distinctness of vertices
  have hneAB : A ≠ B := by
    intro h
    rw [h] at hBC
    exact hBC.right_notMem (left_mem_affineSpan_pair ℝ B C)
  have hneBC : B ≠ C := by
    intro h
    rw [h] at hCD
    exact hCD.right_notMem (left_mem_affineSpan_pair ℝ C D)
  have hneCD : C ≠ D := by
    intro h
    rw [h] at hDA
    exact hDA.right_notMem (left_mem_affineSpan_pair ℝ D A)
  have hneDA : D ≠ A := by
    intro h
    rw [h] at hAB
    exact hAB.right_notMem (left_mem_affineSpan_pair ℝ A B)
  have hneAC : A ≠ C := fun h => AnBC (h.symm ▸ right_mem_affineSpan_pair ℝ B C)
  have hneBD : B ≠ D := fun h => BnCD (h.symm ▸ right_mem_affineSpan_pair ℝ C D)
  have hneAD : A ≠ D := fun h => AnCD (h.symm ▸ right_mem_affineSpan_pair ℝ C D)
  -- extra same-side facts from transitivity
  have pABD : line[ℝ, A, B].SSameSide P D := pAB.trans hAB
  have pBCD : line[ℝ, B, C].SSameSide P D := pBC.trans hBC.symm
  have pCDA : line[ℝ, C, D].SSameSide P A := pCD.trans hCD.symm
  have pDAB : line[ℝ, D, A].SSameSide P B := pDA.trans hDA.symm
  have q1ABD : line[ℝ, A, B].SSameSide Q₁ D := q1AB.trans hAB
  have q1BCD : line[ℝ, B, C].SSameSide Q₁ D := q1BC.trans hBC.symm
  have q1CDA : line[ℝ, C, D].SSameSide Q₁ A := q1CD.trans hCD.symm
  have q1DAB : line[ℝ, D, A].SSameSide Q₁ B := q1DA.trans hDA.symm
  have q2ABD : line[ℝ, A, B].SSameSide Q₂ D := q2AB.trans hAB
  have q2BCD : line[ℝ, B, C].SSameSide Q₂ D := q2BC.trans hBC.symm
  have q2CDA : line[ℝ, C, D].SSameSide Q₂ A := q2CD.trans hCD.symm
  have q2DAB : line[ℝ, D, A].SSameSide Q₂ B := q2DA.trans hDA.symm
  -- facts about `X`
  have hXneA : X ≠ A := hXAB.left_ne_right.symm
  have hXneB : X ≠ B := hXAB.right_ne
  have hXneC : X ≠ C := hXCD.left_ne
  have hXneD : X ≠ D := hXCD.left_ne_right
  have hXinAB : X ∈ line[ℝ, A, B] :=
    mem_affineSpan_pair_of_collinear hneAB (collinear_rot hXAB.wbtw.collinear)
  have hXinCD : X ∈ line[ℝ, C, D] :=
    mem_affineSpan_pair_of_collinear hneCD hXCD.wbtw.collinear
  have hXBeq : line[ℝ, X, B] = line[ℝ, A, B] :=
    affineSpan_pair_eq_of_left_mem_of_ne hXinAB hXneB
  have hXCeq : line[ℝ, X, C] = line[ℝ, C, D] := by
    rw [affineSpan_pair_eq_of_left_mem_of_ne
      (by rwa [AffineSubspace.affineSpan_pair_comm] : X ∈ line[ℝ, D, C]) hXneC,
      AffineSubspace.affineSpan_pair_comm]
  have hXAeq : line[ℝ, X, A] = line[ℝ, A, B] := by
    rw [affineSpan_pair_eq_of_left_mem_of_ne
      (by rwa [AffineSubspace.affineSpan_pair_comm] : X ∈ line[ℝ, B, A]) hXneA,
      AffineSubspace.affineSpan_pair_comm]
  have hXDeq : line[ℝ, X, D] = line[ℝ, C, D] :=
    affineSpan_pair_eq_of_left_mem_of_ne hXinCD hXneD
  have hXnBC : X ∉ line[ℝ, B, C] := by
    intro hXBC
    have h1 : line[ℝ, X, B] = line[ℝ, A, B] := affineSpan_pair_eq_of_left_mem_of_ne hXinAB hXneB
    have hXBC' : X ∈ line[ℝ, C, B] := by rwa [AffineSubspace.affineSpan_pair_comm]
    have h2 : line[ℝ, X, B] = line[ℝ, C, B] := affineSpan_pair_eq_of_left_mem_of_ne hXBC' hXneB
    have h3 : line[ℝ, A, B] = line[ℝ, C, B] := h1.symm.trans h2
    have hAmem : A ∈ line[ℝ, C, B] := h3 ▸ left_mem_affineSpan_pair ℝ A B
    rw [AffineSubspace.affineSpan_pair_comm] at hAmem
    exact AnBC hAmem
  -- distinctness of interior points
  have hPneB : P ≠ B := fun h => pAB.left_notMem (h.symm ▸ right_mem_affineSpan_pair ℝ A B)
  have hPneC : P ≠ C := fun h => pBC.left_notMem (h.symm ▸ right_mem_affineSpan_pair ℝ B C)
  have hPneA : P ≠ A := fun h => pAB.left_notMem (h.symm ▸ left_mem_affineSpan_pair ℝ A B)
  have hPneD : P ≠ D := fun h => pCD.left_notMem (h.symm ▸ right_mem_affineSpan_pair ℝ C D)
  have hPneX : P ≠ X := fun h => pAB.left_notMem (h.symm ▸ hXinAB)
  have hQ1neB : Q₁ ≠ B := fun h => q1AB.left_notMem (h.symm ▸ right_mem_affineSpan_pair ℝ A B)
  have hQ1neC : Q₁ ≠ C := fun h => q1BC.left_notMem (h.symm ▸ right_mem_affineSpan_pair ℝ B C)
  have hQ1neA : Q₁ ≠ A := fun h => q1AB.left_notMem (h.symm ▸ left_mem_affineSpan_pair ℝ A B)
  have hQ1neD : Q₁ ≠ D := fun h => q1CD.left_notMem (h.symm ▸ right_mem_affineSpan_pair ℝ C D)
  have hQ1neX : Q₁ ≠ X := fun h => q1AB.left_notMem (h.symm ▸ hXinAB)
  have hQ2neB : Q₂ ≠ B := fun h => q2AB.left_notMem (h.symm ▸ right_mem_affineSpan_pair ℝ A B)
  have hQ2neC : Q₂ ≠ C := fun h => q2BC.left_notMem (h.symm ▸ right_mem_affineSpan_pair ℝ B C)
  have hQ2neA : Q₂ ≠ A := fun h => q2AB.left_notMem (h.symm ▸ left_mem_affineSpan_pair ℝ A B)
  have hQ2neD : Q₂ ≠ D := fun h => q2CD.left_notMem (h.symm ▸ right_mem_affineSpan_pair ℝ C D)
  have hQ2neX : Q₂ ≠ X := fun h => q2AB.left_notMem (h.symm ▸ hXinAB)
  -- non-collinearity of reference angles
  have h0ABC : (∡ A B C).sign ≠ 0 := fun hs =>
    not_collinear_of_not_mem hneAB CnAB (oangle_sign_eq_zero_iff_collinear.1 hs)
  have h0BCD : (∡ B C D).sign ≠ 0 := fun hs =>
    not_collinear_of_not_mem hneBC DnBC (oangle_sign_eq_zero_iff_collinear.1 hs)
  have h0BAD : (∡ B A D).sign ≠ 0 := fun hs =>
    not_collinear_of_not_mem hneAB.symm
      (by rwa [AffineSubspace.affineSpan_pair_comm] : D ∉ line[ℝ, B, A])
      (oangle_sign_eq_zero_iff_collinear.1 hs)
  have h0CDA : (∡ C D A).sign ≠ 0 := fun hs =>
    not_collinear_of_not_mem hneCD AnCD (oangle_sign_eq_zero_iff_collinear.1 hs)
  have h0BXC : (∡ B X C).sign ≠ 0 := fun hs =>
    not_collinear_of_not_mem hXneB.symm
      (by rw [AffineSubspace.affineSpan_pair_comm, hXBeq]; exact CnAB)
      (oangle_sign_eq_zero_iff_collinear.1 hs)
  have h0AXD : (∡ A X D).sign ≠ 0 := fun hs =>
    not_collinear_of_not_mem hXneA.symm
      (by rw [AffineSubspace.affineSpan_pair_comm, hXAeq]; exact DnAB)
      (oangle_sign_eq_zero_iff_collinear.1 hs)
  -- the twelve angle additions from "inside the angle" sign computations
  have addPB : ∠ A B P + ∠ P B C = ∠ A B C :=
    angle_add_of_sign_eq hneAB hPneB hneBC.symm h0ABC
      (oangle_sign_left_of_sSameSide hneAB pAB)
      (oangle_sign_right_of_sSameSide hneBC pBC)
  have addQ1B : ∠ A B Q₁ + ∠ Q₁ B C = ∠ A B C :=
    angle_add_of_sign_eq hneAB hQ1neB hneBC.symm h0ABC
      (oangle_sign_left_of_sSameSide hneAB q1AB)
      (oangle_sign_right_of_sSameSide hneBC q1BC)
  have addPC : ∠ B C P + ∠ P C D = ∠ B C D :=
    angle_add_of_sign_eq hneBC hPneC hneCD.symm h0BCD
      (oangle_sign_left_of_sSameSide hneBC pBCD)
      (oangle_sign_right_of_sSameSide hneCD pCD)
  have addQ1C : ∠ B C Q₁ + ∠ Q₁ C D = ∠ B C D :=
    angle_add_of_sign_eq hneBC hQ1neC hneCD.symm h0BCD
      (oangle_sign_left_of_sSameSide hneBC q1BCD)
      (oangle_sign_right_of_sSameSide hneCD q1CD)
  have addPA : ∠ B A P + ∠ P A D = ∠ B A D :=
    angle_add_of_sign_eq hneAB.symm hPneA hneDA h0BAD
      (oangle_sign_left_of_sSameSide hneAB.symm
        (by rwa [AffineSubspace.affineSpan_pair_comm] : line[ℝ, B, A].SSameSide P D))
      (oangle_sign_right_of_sSameSide hneAD
        (by rwa [AffineSubspace.affineSpan_pair_comm] : line[ℝ, A, D].SSameSide P B))
  have addQ2A : ∠ B A Q₂ + ∠ Q₂ A D = ∠ B A D :=
    angle_add_of_sign_eq hneAB.symm hQ2neA hneDA h0BAD
      (oangle_sign_left_of_sSameSide hneAB.symm
        (by rwa [AffineSubspace.affineSpan_pair_comm] : line[ℝ, B, A].SSameSide Q₂ D))
      (oangle_sign_right_of_sSameSide hneAD
        (by rwa [AffineSubspace.affineSpan_pair_comm] : line[ℝ, A, D].SSameSide Q₂ B))
  have addPD : ∠ C D P + ∠ P D A = ∠ C D A :=
    angle_add_of_sign_eq hneCD hPneD hneDA.symm h0CDA
      (oangle_sign_left_of_sSameSide hneCD pCDA)
      (oangle_sign_right_of_sSameSide hneDA pDA)
  have addQ2D : ∠ C D Q₂ + ∠ Q₂ D A = ∠ C D A :=
    angle_add_of_sign_eq hneCD hQ2neD hneDA.symm h0CDA
      (oangle_sign_left_of_sSameSide hneCD q2CDA)
      (oangle_sign_right_of_sSameSide hneDA q2DA)
  have addPX : ∠ B X P + ∠ P X C = ∠ B X C :=
    angle_add_of_sign_eq hXneB.symm hPneX hXneC.symm h0BXC
      (oangle_sign_left_of_sSameSide hXneB.symm
        (by rw [AffineSubspace.affineSpan_pair_comm, hXBeq]; exact pAB))
      (oangle_sign_right_of_sSameSide hXneC (by rw [hXCeq]; exact pCD))
  have addQ1X : ∠ B X Q₁ + ∠ Q₁ X C = ∠ B X C :=
    angle_add_of_sign_eq hXneB.symm hQ1neX hXneC.symm h0BXC
      (oangle_sign_left_of_sSameSide hXneB.symm
        (by rw [AffineSubspace.affineSpan_pair_comm, hXBeq]; exact q1AB))
      (oangle_sign_right_of_sSameSide hXneC (by rw [hXCeq]; exact q1CD))
  have addPX2 : ∠ A X P + ∠ P X D = ∠ A X D :=
    angle_add_of_sign_eq hXneA.symm hPneX hXneD.symm h0AXD
      (oangle_sign_left_of_sSameSide hXneA.symm
        (by rw [AffineSubspace.affineSpan_pair_comm, hXAeq]; exact pABD))
      (oangle_sign_right_of_sSameSide hXneD (by rw [hXDeq]; exact pCDA))
  have addQ2X : ∠ A X Q₂ + ∠ Q₂ X D = ∠ A X D :=
    angle_add_of_sign_eq hXneA.symm hQ2neX hXneD.symm h0AXD
      (oangle_sign_left_of_sSameSide hXneA.symm
        (by rw [AffineSubspace.affineSpan_pair_comm, hXAeq]; exact q2ABD))
      (oangle_sign_right_of_sSameSide hXneD (by rw [hXDeq]; exact q2CDA))
  -- same-ray angle rewrites
  have hWBA : Wbtw ℝ X B A := hXAB.symm.wbtw
  have hWCD : Wbtw ℝ X C D := hXCD.wbtw
  have eDX : ∠ D X B = ∠ D X A := hWBA.angle_eq_right D hXneB.symm
  have eBX : ∠ B X C = ∠ B X D := hWCD.angle_eq_right B hXneC.symm
  have θeq : ∠ A X D = ∠ B X C := by
    rw [angle_comm A X D, ← eDX, angle_comm D X B, ← eBX]
  have φeq : ∠ A X P = ∠ B X P := by
    rw [angle_comm A X P, ← hWBA.angle_eq_right P hXneB.symm, angle_comm P X B]
  have ψ2eq : ∠ A X Q₂ = ∠ B X Q₂ := by
    rw [angle_comm A X Q₂, ← hWBA.angle_eq_right Q₂ hXneB.symm, angle_comm Q₂ X B]
  have hApeq : ∠ X A P = ∠ B A P := by
    rw [angle_comm X A P, ← hXAB.wbtw.angle_eq_right P hneAB.symm, angle_comm P A B]
  have hAq2eq : ∠ X A Q₂ = ∠ B A Q₂ := by
    rw [angle_comm X A Q₂, ← hXAB.wbtw.angle_eq_right Q₂ hneAB.symm, angle_comm Q₂ A B]
  have hDpeq : ∠ X D P = ∠ C D P := by
    rw [angle_comm X D P, ← hXCD.symm.wbtw.angle_eq_right P hneCD, angle_comm P D C]
  have hDq2eq : ∠ X D Q₂ = ∠ C D Q₂ := by
    rw [angle_comm X D Q₂, ← hXCD.symm.wbtw.angle_eq_right Q₂ hneCD, angle_comm Q₂ D C]
  -- supplementary sines
  have sinXBP : Real.sin (∠ X B P) = Real.sin (∠ A B P) := by
    rw [sin_angle_eq_sin_angle_of_sbtw hXAB.symm hPneB, angle_comm P B A]
  have sinXBQ1 : Real.sin (∠ X B Q₁) = Real.sin (∠ A B Q₁) := by
    rw [sin_angle_eq_sin_angle_of_sbtw hXAB.symm hQ1neB, angle_comm Q₁ B A]
  have sinXCP : Real.sin (∠ X C P) = Real.sin (∠ D C P) := by
    rw [sin_angle_eq_sin_angle_of_sbtw hXCD hPneC, angle_comm P C D]
  have sinXCQ1 : Real.sin (∠ X C Q₁) = Real.sin (∠ Q₁ C D) := by
    rw [sin_angle_eq_sin_angle_of_sbtw hXCD hQ1neC, angle_comm Q₁ C D]
  -- angle identifications
  have βB_eq : ∠ A B Q₁ = ∠ P B C := by linarith [addPB, addQ1B, hQ1B]
  have βC_eq : ∠ Q₁ C D = ∠ B C P := by
    linarith [addPC, addQ1C, hQ1C, angle_comm B C Q₁, angle_comm D C P]
  have δA_eq : ∠ B A Q₂ = ∠ P A D := by linarith [addPA, addQ2A, hQ2A]
  have δD_eq : ∠ C D Q₂ = ∠ P D A := by linarith [addPD, addQ2D, hQ2D]
  have θmφ : ∠ P X C = ∠ B X C - ∠ B X P := by linarith [addPX]
  have θmψ1 : ∠ Q₁ X C = ∠ B X C - ∠ B X Q₁ := by linarith [addQ1X]
  have θmφ2 : ∠ P X D = ∠ B X C - ∠ B X P := by linarith [addPX2, θeq, φeq]
  have θmψ2 : ∠ Q₂ X D = ∠ B X C - ∠ B X Q₂ := by linarith [addQ2X, θeq, ψ2eq]
  -- the four sine-chase equations
  have E1 := sine_chase hPneB.symm hPneC.symm hPneX.symm
  rw [θmφ, sinXBP, sinXCP] at E1
  have E2 := sine_chase hQ1neB.symm hQ1neC.symm hQ1neX.symm
  rw [θmψ1, sinXBQ1, βB_eq, angle_comm B C Q₁, hQ1C, hQ1B, sinXCQ1, βC_eq] at E2
  have E3 := sine_chase hPneA.symm hPneD.symm hPneX.symm
  rw [θmφ2, hApeq, angle_comm A D P, φeq, hDpeq] at E3
  have E4 := sine_chase hQ2neA.symm hQ2neD.symm hQ2neX.symm
  rw [θmψ2, hAq2eq, δA_eq, angle_comm A D Q₂, hQ2D, ψ2eq, hQ2A, hDq2eq, δD_eq] at E4
  -- positivity of the sines to be cancelled
  have posαB : 0 < Real.sin (∠ A B P) :=
    sin_pos_of_not_collinear (not_collinear_of_not_mem hneAB pAB.left_notMem)
  have posβC : 0 < Real.sin (∠ B C P) :=
    sin_pos_of_not_collinear (not_collinear_of_not_mem hneBC pBC.left_notMem)
  have posβB : 0 < Real.sin (∠ P B C) := sin_pos_of_not_collinear
    (not_collinear_rot (not_collinear_of_not_mem hneBC pBC.left_notMem))
  have posαC : 0 < Real.sin (∠ D C P) := sin_pos_of_not_collinear (not_collinear_of_not_mem
    hneCD.symm (by rw [AffineSubspace.affineSpan_pair_comm]; exact pCD.left_notMem))
  have posγA : 0 < Real.sin (∠ B A P) :=
    sin_pos_of_not_collinear (not_collinear_swap (not_collinear_of_not_mem hneAB pAB.left_notMem))
  have posδD : 0 < Real.sin (∠ P D A) := sin_pos_of_not_collinear
    (not_collinear_rot (not_collinear_of_not_mem hneDA pDA.left_notMem))
  have posδA : 0 < Real.sin (∠ P A D) := sin_pos_of_not_collinear (not_collinear_rot
    (not_collinear_of_not_mem hneDA.symm
      (by rw [AffineSubspace.affineSpan_pair_comm]; exact pDA.left_notMem)))
  have posγD : 0 < Real.sin (∠ C D P) :=
    sin_pos_of_not_collinear (not_collinear_of_not_mem hneCD pCD.left_notMem)
  -- the key relations
  have key1 : Real.sin (∠ B X C - ∠ B X P) * Real.sin (∠ B X C - ∠ B X Q₁) =
      Real.sin (∠ B X P) * Real.sin (∠ B X Q₁) := by
    have hF : Real.sin (∠ A B P) * Real.sin (∠ B C P) * Real.sin (∠ P B C) *
        Real.sin (∠ D C P) ≠ 0 :=
      (mul_pos (mul_pos (mul_pos posαB posβC) posβB) posαC).ne'
    have key1F : (Real.sin (∠ B X C - ∠ B X P) * Real.sin (∠ B X C - ∠ B X Q₁)) *
        (Real.sin (∠ A B P) * Real.sin (∠ B C P) * Real.sin (∠ P B C) * Real.sin (∠ D C P)) =
        (Real.sin (∠ B X P) * Real.sin (∠ B X Q₁)) *
        (Real.sin (∠ A B P) * Real.sin (∠ B C P) * Real.sin (∠ P B C) * Real.sin (∠ D C P)) := by
      linear_combination
        (Real.sin (∠ B X C - ∠ B X Q₁) * Real.sin (∠ P B C) * Real.sin (∠ D C P)) * E1 +
          (Real.sin (∠ B X P) * Real.sin (∠ P B C) * Real.sin (∠ D C P)) * E2
    exact mul_right_cancel₀ hF key1F
  have key2 : Real.sin (∠ B X C - ∠ B X P) * Real.sin (∠ B X C - ∠ B X Q₂) =
      Real.sin (∠ B X P) * Real.sin (∠ B X Q₂) := by
    have hF : Real.sin (∠ B A P) * Real.sin (∠ P D A) * Real.sin (∠ P A D) *
        Real.sin (∠ C D P) ≠ 0 :=
      (mul_pos (mul_pos (mul_pos posγA posδD) posδA) posγD).ne'
    have key2F : (Real.sin (∠ B X C - ∠ B X P) * Real.sin (∠ B X C - ∠ B X Q₂)) *
        (Real.sin (∠ B A P) * Real.sin (∠ P D A) * Real.sin (∠ P A D) * Real.sin (∠ C D P)) =
        (Real.sin (∠ B X P) * Real.sin (∠ B X Q₂)) *
        (Real.sin (∠ B A P) * Real.sin (∠ P D A) * Real.sin (∠ P A D) * Real.sin (∠ C D P)) := by
      linear_combination
        (Real.sin (∠ B X C - ∠ B X Q₂) * Real.sin (∠ P A D) * Real.sin (∠ C D P)) * E3 +
          (Real.sin (∠ B X P) * Real.sin (∠ P A D) * Real.sin (∠ C D P)) * E4
    exact mul_right_cancel₀ hF key2F
  -- non-collinearity for the ranges
  have ncBXC : ¬Collinear ℝ ({B, X, C} : Set Pt) := not_collinear_of_not_mem hXneB.symm
    (by rw [AffineSubspace.affineSpan_pair_comm, hXBeq]; exact CnAB)
  have ncBXP : ¬Collinear ℝ ({B, X, P} : Set Pt) := not_collinear_of_not_mem hXneB.symm
    (by rw [AffineSubspace.affineSpan_pair_comm, hXBeq]; exact pAB.left_notMem)
  have ncPXC : ¬Collinear ℝ ({P, X, C} : Set Pt) := not_collinear_rot
    (not_collinear_of_not_mem hXneC (by rw [hXCeq]; exact pCD.left_notMem))
  have ncBXQ1 : ¬Collinear ℝ ({B, X, Q₁} : Set Pt) := not_collinear_of_not_mem hXneB.symm
    (by rw [AffineSubspace.affineSpan_pair_comm, hXBeq]; exact q1AB.left_notMem)
  have ncQ1XC : ¬Collinear ℝ ({Q₁, X, C} : Set Pt) := not_collinear_rot
    (not_collinear_of_not_mem hXneC (by rw [hXCeq]; exact q1CD.left_notMem))
  have ncBXQ2 : ¬Collinear ℝ ({B, X, Q₂} : Set Pt) := not_collinear_of_not_mem hXneB.symm
    (by rw [AffineSubspace.affineSpan_pair_comm, hXBeq]; exact q2AB.left_notMem)
  have ncQ2XD : ¬Collinear ℝ ({Q₂, X, D} : Set Pt) := not_collinear_rot
    (not_collinear_of_not_mem hXneD (by rw [hXDeq]; exact q2CD.left_notMem))
  -- apply the uniqueness lemma
  have hθ0 : 0 < ∠ B X C := angle_pos_of_not_collinear ncBXC
  have hθπ : ∠ B X C < π := angle_lt_pi_of_not_collinear ncBXC
  have hφ0 : 0 < ∠ B X P := angle_pos_of_not_collinear ncBXP
  have hφθ : ∠ B X P < ∠ B X C := by
    have h1 : 0 < ∠ P X C := angle_pos_of_not_collinear ncPXC
    linarith [addPX, h1]
  have ψ₁eq : ∠ B X Q₁ = ∠ B X C - ∠ B X P :=
    eq_of_sin_mul_sin hθ0 hθπ hφ0 hφθ (angle_pos_of_not_collinear ncBXQ1)
      (by
        have h1 : 0 < ∠ Q₁ X C := angle_pos_of_not_collinear ncQ1XC
        linarith [addQ1X, h1])
      key1
  have ψ₂eq : ∠ B X Q₂ = ∠ B X C - ∠ B X P :=
    eq_of_sin_mul_sin hθ0 hθπ hφ0 hφθ (angle_pos_of_not_collinear ncBXQ2)
      (by
        have h1 : 0 < ∠ Q₂ X D := angle_pos_of_not_collinear ncQ2XD
        linarith [addQ2X, θeq, ψ2eq, h1])
      key2
  -- conclude collinearity
  have ψeq : ∠ B X Q₁ = ∠ B X Q₂ := by rw [ψ₁eq, ψ₂eq]
  have s1 : (∡ B X Q₁).sign = (∡ B X C).sign :=
    oangle_sign_left_of_sSameSide hXneB.symm
      (by rw [AffineSubspace.affineSpan_pair_comm, hXBeq]; exact q1AB)
  have s2 : (∡ B X Q₂).sign = (∡ B X C).sign :=
    oangle_sign_left_of_sSameSide hXneB.symm
      (by rw [AffineSubspace.affineSpan_pair_comm, hXBeq]; exact q2AB)
  have oeq : ∡ B X Q₁ = ∡ B X Q₂ := oangle_eq_of_angle_eq_of_sign_eq ψeq (s1.trans s2.symm)
  have hQ12 : ∡ Q₁ X Q₂ = 0 := by
    rw [← oangle_add hQ1neX hXneB.symm hQ2neX, oangle_rev B X Q₁, oeq, neg_add_cancel]
  exact collinear_swap (oangle_eq_zero_or_eq_pi_iff_collinear.1 (Or.inl hQ12))

snip end

problem usa2011_p5
    {A B C D P Q₁ Q₂ : Pt}
    (hconv : ConvexQuad A B C D)
    (hP : InsideQuad A B C D P)
    (hQ1 : InsideQuad A B C D Q₁)
    (hQ2 : InsideQuad A B C D Q₂)
    (hQ1B : ∠ Q₁ B C = ∠ A B P)
    (hQ1C : ∠ Q₁ C B = ∠ D C P)
    (hQ2A : ∠ Q₂ A D = ∠ B A P)
    (hQ2D : ∠ Q₂ D A = ∠ C D P) :
    line[ℝ, Q₁, Q₂] ∥ line[ℝ, A, B] ↔ line[ℝ, Q₁, Q₂] ∥ line[ℝ, C, D] := by
  have hAB := hconv.1
  have hBC := hconv.2.1
  have hCD := hconv.2.2.1
  have hDA := hconv.2.2.2
  have hneAB : A ≠ B := by
    intro h
    rw [h] at hBC
    exact hBC.right_notMem (left_mem_affineSpan_pair ℝ B C)
  have hneCD : C ≠ D := by
    intro h
    rw [h] at hDA
    exact hDA.right_notMem (left_mem_affineSpan_pair ℝ D A)
  by_cases hpar : line[ℝ, A, B] ∥ line[ℝ, C, D]
  · -- if `AB ∥ CD`, parallelism is transitive
    constructor
    · intro h
      exact h.trans hpar
    · intro h
      exact h.trans hpar.symm
  · obtain ⟨X, hXAB', hXCD', hpos⟩ := exists_sbtw_inter_of_convexQuad hconv hneAB hneCD hpar
    by_cases hQQ : Q₁ = Q₂
    · -- the degenerate case `Q₁ = Q₂`: both sides are false, since the directions
      -- of the (zero-dimensional) span differ from those of the lines
      subst hQQ
      have h0 : Module.finrank ℝ (line[ℝ, Q₁, Q₁]).direction = 0 := by
        rw [show ({Q₁, Q₁} : Set Pt) = {Q₁} by simp, direction_affineSpan,
          vectorSpan_singleton, finrank_bot]
      have hnpar1 : ¬line[ℝ, Q₁, Q₁] ∥ line[ℝ, A, B] := by
        intro h
        have hd := h.direction_eq
        have f1 := affineSpan_pair_finrank hneAB
        rw [hd, f1] at h0
        exact one_ne_zero h0
      have hnpar2 : ¬line[ℝ, Q₁, Q₁] ∥ line[ℝ, C, D] := by
        intro h
        have hd := h.direction_eq
        have f1 := affineSpan_pair_finrank hneCD
        have h0' : Module.finrank ℝ (line[ℝ, Q₁, Q₁]).direction = 0 := by
          rw [show ({Q₁, Q₁} : Set Pt) = {Q₁} by simp, direction_affineSpan,
            vectorSpan_singleton, finrank_bot]
        rw [hd, f1] at h0'
        exact one_ne_zero h0'
      exact iff_of_false hnpar1 hnpar2
    · -- the generic case: `X, Q₁, Q₂` are collinear, so `X ∈ line Q₁Q₂`, and a line
      -- through `X` parallel to `AB` or `CD` would have to equal them, forcing `Q₁`
      -- onto a side line of the quadrilateral
      have hcoll : Collinear ℝ ({X, Q₁, Q₂} : Set Pt) := by
        rcases hpos with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact core_collinear hconv hP hQ1 hQ2 hQ1B hQ1C hQ2A hQ2D h1 h2
        · have hconv' : ConvexQuad B A D C := by
            refine ⟨?_, ?_, ?_, ?_⟩
            · rw [AffineSubspace.affineSpan_pair_comm]; exact hAB.symm
            · rw [AffineSubspace.affineSpan_pair_comm]; exact hDA.symm
            · rw [AffineSubspace.affineSpan_pair_comm]; exact hCD.symm
            · rw [AffineSubspace.affineSpan_pair_comm]; exact hBC.symm
          have hP' : InsideQuad B A D C P := by
            refine ⟨?_, ?_, ?_, ?_⟩
            · rw [AffineSubspace.affineSpan_pair_comm]; exact hP.1.trans hAB
            · rw [AffineSubspace.affineSpan_pair_comm]; exact hP.2.2.2.trans hDA.symm
            · rw [AffineSubspace.affineSpan_pair_comm]; exact hP.2.2.1.trans hCD.symm
            · rw [AffineSubspace.affineSpan_pair_comm]; exact hP.2.1.trans hBC.symm
          have hQ1' : InsideQuad B A D C Q₂ := by
            refine ⟨?_, ?_, ?_, ?_⟩
            · rw [AffineSubspace.affineSpan_pair_comm]; exact hQ2.1.trans hAB
            · rw [AffineSubspace.affineSpan_pair_comm]; exact hQ2.2.2.2.trans hDA.symm
            · rw [AffineSubspace.affineSpan_pair_comm]; exact hQ2.2.2.1.trans hCD.symm
            · rw [AffineSubspace.affineSpan_pair_comm]; exact hQ2.2.1.trans hBC.symm
          have hQ2' : InsideQuad B A D C Q₁ := by
            refine ⟨?_, ?_, ?_, ?_⟩
            · rw [AffineSubspace.affineSpan_pair_comm]; exact hQ1.1.trans hAB
            · rw [AffineSubspace.affineSpan_pair_comm]; exact hQ1.2.2.2.trans hDA.symm
            · rw [AffineSubspace.affineSpan_pair_comm]; exact hQ1.2.2.1.trans hCD.symm
            · rw [AffineSubspace.affineSpan_pair_comm]; exact hQ1.2.1.trans hBC.symm
          have hcoll' : Collinear ℝ ({X, Q₂, Q₁} : Set Pt) :=
            core_collinear hconv' hP' hQ1' hQ2' hQ2A hQ2D hQ1B hQ1C h1.symm h2.symm
          exact collinear_swap₂₃ hcoll'
      have hXin : X ∈ line[ℝ, Q₁, Q₂] := mem_affineSpan_pair_of_collinear hQQ hcoll
      have hQ1nAB : Q₁ ∉ line[ℝ, A, B] := hQ1.1.left_notMem
      have hQ1nCD : Q₁ ∉ line[ℝ, C, D] := hQ1.2.2.1.left_notMem
      have hnpar1 : ¬line[ℝ, Q₁, Q₂] ∥ line[ℝ, A, B] := by
        intro h
        have heq : line[ℝ, Q₁, Q₂] = line[ℝ, A, B] :=
          (AffineSubspace.eq_iff_direction_eq_of_mem hXin hXAB').2 h.direction_eq
        exact hQ1nAB (heq ▸ left_mem_affineSpan_pair ℝ Q₁ Q₂)
      have hnpar2 : ¬line[ℝ, Q₁, Q₂] ∥ line[ℝ, C, D] := by
        intro h
        have heq : line[ℝ, Q₁, Q₂] = line[ℝ, C, D] :=
          (AffineSubspace.eq_iff_direction_eq_of_mem hXin hXCD').2 h.direction_eq
        exact hQ1nCD (heq ▸ left_mem_affineSpan_pair ℝ Q₁ Q₂)
      exact iff_of_false hnpar1 hnpar2

end Usa2011P5
