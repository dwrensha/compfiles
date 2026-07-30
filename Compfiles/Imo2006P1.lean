/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.InnerProductSpace.OfNorm
public import Mathlib.Geometry.Euclidean.Angle.Incenter
public import Mathlib.Geometry.Euclidean.Angle.Sphere
public import Mathlib.Geometry.Euclidean.Triangle
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 2006, Problem 1

Let $ABC$ be a triangle with incenter $I$. A point $P$ in the interior of the
triangle satisfies
$$ ∠PBA + ∠PCA = ∠PBC + ∠PCB. $$
Show that $AP \ge AI$, and that equality holds if and only if $P = I$.
-/

namespace Imo2006P1

open scoped EuclideanGeometry

snip begin

open EuclideanGeometry Affine.Simplex Affine.Triangle

-- We need some instances in order to talk about oriented angles.

local instance planeFiniteDim :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) :=
  ⟨finrank_euclideanSpace_fin⟩

noncomputable local instance someOrientation :
    Module.Oriented ℝ (EuclideanSpace ℝ (Fin 2)) (Fin 2) :=
  ⟨Module.Basis.orientation (Module.finBasisOfFinrankEq _ _ planeFiniteDim.out)⟩

/-- A nonzero sign is `1` or `-1`. -/
lemma sign_eq_one_or_neg_one {σ : SignType} (h : σ ≠ 0) : σ = 1 ∨ σ = -1 := by
  rcases σ with _ | _ | _ <;> simp_all

/-- Auxiliary computation for `abs_toReal_add_of_sign_eq`, in the case of positive signs. -/
private lemma abs_toReal_add_of_sign_eq_one {θ ψ : Real.Angle} (hθ : θ.sign = 1)
    (hs : θ.sign = ψ.sign) (hsum : θ.sign = (θ + ψ).sign) :
    |(θ + ψ).toReal| = |θ.toReal| + |ψ.toReal| := by
  have ha : θ.toReal ∈ Set.Ioo 0 Real.pi := Real.Angle.toReal_mem_Ioo_iff_sign_pos.2 hθ
  have hb : ψ.toReal ∈ Set.Ioo 0 Real.pi := Real.Angle.toReal_mem_Ioo_iff_sign_pos.2 (hs ▸ hθ)
  have hab : (θ + ψ).toReal ∈ Set.Ioo 0 Real.pi :=
    Real.Angle.toReal_mem_Ioo_iff_sign_pos.2 (hsum ▸ hθ)
  have hco : ((θ + ψ).toReal : Real.Angle) = ((θ.toReal + ψ.toReal : ℝ) : Real.Angle) := by
    rw [Real.Angle.coe_add, Real.Angle.coe_toReal, Real.Angle.coe_toReal, Real.Angle.coe_toReal]
  obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.1 hco
  have hlt : |(θ + ψ).toReal - (θ.toReal + ψ.toReal)| < 2 * Real.pi := by
    rw [abs_lt]
    constructor <;> linarith [ha.1, ha.2, hb.1, hb.2, hab.1, hab.2, Real.pi_pos]
  have hk0 : k = 0 := by
    by_contra hk0
    have h1k : (1 : ℝ) ≤ |(k : ℝ)| := by
      rw [← Int.cast_one, ← Int.cast_abs, Int.cast_le]
      exact Int.one_le_abs hk0
    rw [hk, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at hlt
    nlinarith [h1k, Real.pi_pos]
  rw [hk0, Int.cast_zero, mul_zero, sub_eq_zero] at hk
  rw [hk, abs_of_pos (by linarith [ha.1, hb.1] : (0 : ℝ) < θ.toReal + ψ.toReal),
    abs_of_pos ha.1, abs_of_pos hb.1]

/-- If two oriented angles with nonzero equal signs add up to an angle that again has the same
sign, then the absolute values of their real representatives add up. This is the computational
content of "an interior ray splits an angle into two angles". -/
lemma abs_toReal_add_of_sign_eq {θ ψ : Real.Angle} (hθ : θ.sign ≠ 0) (hs : θ.sign = ψ.sign)
    (hsum : θ.sign = (θ + ψ).sign) :
    |(θ + ψ).toReal| = |θ.toReal| + |ψ.toReal| := by
  rcases sign_eq_one_or_neg_one hθ with h1 | h1
  · exact abs_toReal_add_of_sign_eq_one h1 hs hsum
  · -- Case `θ.sign = -1`: apply the positive case to the negated angles.
    have g1 : (-θ).sign = 1 := by simp only [Real.Angle.sign_neg, h1, neg_neg]
    have g2 : (-θ).sign = (-ψ).sign := by simp only [Real.Angle.sign_neg, h1, ← hs]
    have g3 : (-θ).sign = (-θ + -ψ).sign := by
      simp only [← neg_add, Real.Angle.sign_neg, ← hsum, h1]
    have key := abs_toReal_add_of_sign_eq_one g1 g2 g3
    rwa [← neg_add, Real.Angle.abs_toReal_neg, Real.Angle.abs_toReal_neg,
      Real.Angle.abs_toReal_neg] at key

/-- An oriented angle with nonzero sign `σ` whose real representative has absolute value `x`
(with `0 < x < π`) is equal to `x` twisted by the sign. -/
lemma oangle_eq_sign_zsmul_coe {θ : Real.Angle} {x : ℝ} (hx0 : 0 < x) (hxπ : x < Real.pi)
    (habs : |θ.toReal| = x) {σ : SignType} (hσ : σ ≠ 0) (hs : θ.sign = σ) :
    θ = (σ : ℤ) • (x : Real.Angle) := by
  have hto : ((x : ℝ) : Real.Angle).toReal = x :=
    Real.Angle.toReal_coe_eq_self_iff.2 ⟨by linarith [Real.pi_pos], hxπ.le⟩
  have hsign1 : ((x : ℝ) : Real.Angle).sign = 1 :=
    Real.Angle.toReal_mem_Ioo_iff_sign_pos.1 (hto.symm ▸ ⟨hx0, hxπ⟩)
  rcases sign_eq_one_or_neg_one hσ with rfl | rfl
  · rw [show ((1 : SignType) : ℤ) = 1 from rfl, one_zsmul]
    refine (Real.Angle.eq_iff_abs_toReal_eq_of_sign_eq ?_).2 ?_
    · rw [hs, hsign1]
    · rw [habs, hto, abs_of_nonneg hx0.le]
  · rw [show ((-1 : SignType) : ℤ) = -1 from rfl, neg_one_zsmul]
    refine (Real.Angle.eq_iff_abs_toReal_eq_of_sign_eq ?_).2 ?_
    · rw [hs, Real.Angle.sign_neg, hsign1]
    · rw [habs, Real.Angle.abs_toReal_neg, hto, abs_of_nonneg hx0.le]

/-- The real representative of `σ • x` (with `0 ≤ x ≤ π` and nonzero `σ`) has absolute
value `x`. -/
lemma abs_toReal_sign_zsmul_coe {x : ℝ} (hx0 : 0 ≤ x) (hxπ : x ≤ Real.pi) {σ : SignType}
    (hσ : σ ≠ 0) : |((σ : ℤ) • (x : Real.Angle)).toReal| = x := by
  rcases sign_eq_one_or_neg_one hσ with rfl | rfl
  · rw [show ((1 : SignType) : ℤ) = 1 from rfl, one_zsmul,
      Real.Angle.abs_toReal_coe_eq_self_iff.2 ⟨hx0, hxπ⟩]
  · rw [show ((-1 : SignType) : ℤ) = -1 from rfl, neg_one_zsmul, Real.Angle.abs_toReal_neg,
      Real.Angle.abs_toReal_coe_eq_self_iff.2 ⟨hx0, hxπ⟩]

/-- The configuration of the problem: a triangle `ABC` in the plane together with a point `P`
in its interior satisfying the angle condition. -/
structure Imo2006P1Cfg where
  (A B C P : EuclideanSpace ℝ (Fin 2))
  (hABC : AffineIndependent ℝ ![A, B, C])
  (hP : P ∈ (⟨![A, B, C], hABC⟩ : Affine.Triangle ℝ _).interior)
  (hcond : ∠ P B A + ∠ P C A = ∠ P B C + ∠ P C B)

namespace Imo2006P1Cfg

variable (cfg : Imo2006P1Cfg)

/-- The triangle of the configuration. -/
def ABC : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2)) :=
  ⟨![cfg.A, cfg.B, cfg.C], cfg.hABC⟩

/-- The incenter of the triangle. -/
noncomputable def I : EuclideanSpace ℝ (Fin 2) := cfg.ABC.incenter

/-- The sign of the oriented angle `∡ A B C`; all oriented angles in the configuration are
governed by this sign. -/
noncomputable def s : SignType := (∡ cfg.A cfg.B cfg.C).sign

lemma A_ne_B : cfg.A ≠ cfg.B := cfg.hABC.injective.ne (by decide : (0 : Fin 3) ≠ 1)

lemma A_ne_C : cfg.A ≠ cfg.C := cfg.hABC.injective.ne (by decide : (0 : Fin 3) ≠ 2)

lemma B_ne_C : cfg.B ≠ cfg.C := cfg.hABC.injective.ne (by decide : (1 : Fin 3) ≠ 2)

lemma s_ne_zero : cfg.s ≠ 0 := by
  rw [s, Real.Angle.sign_ne_zero_iff]
  exact oangle_ne_zero_and_ne_pi_iff_affineIndependent.2 cfg.hABC

/-- The incenter lies in the interior of the triangle. -/
lemma I_mem_interior : cfg.I ∈ cfg.ABC.interior := incenter_mem_interior cfg.ABC

/-- Points of the interior differ from the vertices. -/
lemma ne_vertex_of_mem_interior {Q : EuclideanSpace ℝ (Fin 2)} (hQ : Q ∈ cfg.ABC.interior)
    (i : Fin 3) : Q ≠ cfg.ABC.points i := by
  intro h
  rw [h] at hQ
  exact cfg.ABC.point_notMem_interior i hQ

lemma P_ne_A : cfg.P ≠ cfg.A := cfg.ne_vertex_of_mem_interior cfg.hP 0

lemma P_ne_B : cfg.P ≠ cfg.B := cfg.ne_vertex_of_mem_interior cfg.hP 1

lemma P_ne_C : cfg.P ≠ cfg.C := cfg.ne_vertex_of_mem_interior cfg.hP 2

lemma I_ne_A : cfg.I ≠ cfg.A := cfg.ne_vertex_of_mem_interior cfg.I_mem_interior 0

lemma I_ne_B : cfg.I ≠ cfg.B := cfg.ne_vertex_of_mem_interior cfg.I_mem_interior 1

lemma I_ne_C : cfg.I ≠ cfg.C := cfg.ne_vertex_of_mem_interior cfg.I_mem_interior 2

/-- An interior point and the opposite vertex lie on the same side of the span of a face. -/
lemma ssameSide_faceOpposite_of_mem_interior {Q : EuclideanSpace ℝ (Fin 2)}
    (hQ : Q ∈ cfg.ABC.interior) (i : Fin 3) :
    (affineSpan ℝ (Set.range (cfg.ABC.faceOpposite i).points)).SSameSide Q
      (cfg.ABC.points i) := by
  obtain ⟨w, hws, hwI, hwQ⟩ := hQ
  rw [← hwQ]
  exact (cfg.ABC.sSameSide_affineSpan_faceOpposite_point_right_iff hws).2 (hwI i).1

lemma B_mem_span_faceOpposite_two :
    cfg.B ∈ affineSpan ℝ (Set.range (cfg.ABC.faceOpposite 2).points) := by
  rw [range_faceOpposite_points]
  apply mem_affineSpan ℝ
  have h1 : cfg.ABC.points 1 = cfg.B := rfl
  rw [← h1]
  exact Set.mem_image_of_mem _ (by simp)

lemma A_mem_span_faceOpposite_two :
    cfg.A ∈ affineSpan ℝ (Set.range (cfg.ABC.faceOpposite 2).points) := by
  rw [range_faceOpposite_points]
  apply mem_affineSpan ℝ
  have h0 : cfg.ABC.points 0 = cfg.A := rfl
  rw [← h0]
  exact Set.mem_image_of_mem _ (by simp)

lemma C_mem_span_faceOpposite_one :
    cfg.C ∈ affineSpan ℝ (Set.range (cfg.ABC.faceOpposite 1).points) := by
  rw [range_faceOpposite_points]
  apply mem_affineSpan ℝ
  have h2 : cfg.ABC.points 2 = cfg.C := rfl
  rw [← h2]
  exact Set.mem_image_of_mem _ (by simp)

lemma A_mem_span_faceOpposite_one :
    cfg.A ∈ affineSpan ℝ (Set.range (cfg.ABC.faceOpposite 1).points) := by
  rw [range_faceOpposite_points]
  apply mem_affineSpan ℝ
  have h0 : cfg.ABC.points 0 = cfg.A := rfl
  rw [← h0]
  exact Set.mem_image_of_mem _ (by simp)

lemma B_mem_span_faceOpposite_zero :
    cfg.B ∈ affineSpan ℝ (Set.range (cfg.ABC.faceOpposite 0).points) := by
  rw [range_faceOpposite_points]
  apply mem_affineSpan ℝ
  have h1 : cfg.ABC.points 1 = cfg.B := rfl
  rw [← h1]
  exact Set.mem_image_of_mem _ (by simp)

lemma C_mem_span_faceOpposite_zero :
    cfg.C ∈ affineSpan ℝ (Set.range (cfg.ABC.faceOpposite 0).points) := by
  rw [range_faceOpposite_points]
  apply mem_affineSpan ℝ
  have h2 : cfg.ABC.points 2 = cfg.C := rfl
  rw [← h2]
  exact Set.mem_image_of_mem _ (by simp)

/-- The key sign computation: an interior point sees the sides of the triangle under oriented
angles whose signs agree with the orientation of the triangle. -/
lemma signs_of_mem_interior {Q : EuclideanSpace ℝ (Fin 2)} (hQ : Q ∈ cfg.ABC.interior) :
    (∡ cfg.A cfg.B Q).sign = cfg.s ∧ (∡ cfg.B cfg.C Q).sign = cfg.s ∧
      (∡ cfg.C cfg.A Q).sign = cfg.s := by
  have hss2 := cfg.ssameSide_faceOpposite_of_mem_interior hQ 2
  have hss1 := cfg.ssameSide_faceOpposite_of_mem_interior hQ 1
  have hss0 := cfg.ssameSide_faceOpposite_of_mem_interior hQ 0
  have h2 : cfg.ABC.points 2 = cfg.C := rfl
  have h1 : cfg.ABC.points 1 = cfg.B := rfl
  have h0 : cfg.ABC.points 0 = cfg.A := rfl
  rw [h2] at hss2
  rw [h1] at hss1
  rw [h0] at hss0
  refine ⟨?_, ?_, ?_⟩
  · -- `(∡ A B Q).sign = s`
    calc (∡ cfg.A cfg.B Q).sign = (∡ cfg.B Q cfg.A).sign := (oangle_rotate_sign _ _ _).symm
    _ = (∡ cfg.B cfg.C cfg.A).sign :=
        (hss2.oangle_sign_eq cfg.B_mem_span_faceOpposite_two cfg.A_mem_span_faceOpposite_two).symm
    _ = (∡ cfg.C cfg.A cfg.B).sign := (oangle_rotate_sign _ _ _).symm
    _ = (∡ cfg.A cfg.B cfg.C).sign := (oangle_rotate_sign _ _ _).symm
  · -- `(∡ B C Q).sign = s`
    calc (∡ cfg.B cfg.C Q).sign = (∡ cfg.C Q cfg.B).sign := (oangle_rotate_sign _ _ _).symm
    _ = (∡ cfg.C cfg.A cfg.B).sign :=
        (hss0.oangle_sign_eq cfg.C_mem_span_faceOpposite_zero cfg.B_mem_span_faceOpposite_zero).symm
    _ = (∡ cfg.A cfg.B cfg.C).sign := (oangle_rotate_sign _ _ _).symm
  · -- `(∡ C A Q).sign = s`
    calc (∡ cfg.C cfg.A Q).sign = (∡ cfg.A Q cfg.C).sign := (oangle_rotate_sign _ _ _).symm
    _ = (∡ cfg.A cfg.B cfg.C).sign :=
        (hss1.oangle_sign_eq cfg.A_mem_span_faceOpposite_one cfg.C_mem_span_faceOpposite_one).symm

/-- The signs of the angles of the triangle, in all six orderings. -/
lemma sign_BCA : (∡ cfg.B cfg.C cfg.A).sign = cfg.s := oangle_rotate_sign cfg.A cfg.B cfg.C

lemma sign_CAB : (∡ cfg.C cfg.A cfg.B).sign = cfg.s :=
  (oangle_rotate_sign cfg.B cfg.C cfg.A).trans cfg.sign_BCA

lemma sign_ACB : (∡ cfg.A cfg.C cfg.B).sign = -cfg.s := by
  rw [oangle_rev cfg.B cfg.C cfg.A, Real.Angle.sign_neg, cfg.sign_BCA]

lemma sign_CBA : (∡ cfg.C cfg.B cfg.A).sign = -cfg.s := by
  have h : (∡ cfg.C cfg.B cfg.A).sign = -(∡ cfg.A cfg.B cfg.C).sign := by
    rw [oangle_rev cfg.A cfg.B cfg.C, Real.Angle.sign_neg]
  exact h

lemma sign_BAC : (∡ cfg.B cfg.A cfg.C).sign = -cfg.s := by
  have h : (∡ cfg.B cfg.A cfg.C).sign = -(∡ cfg.C cfg.A cfg.B).sign := by
    rw [oangle_rev cfg.C cfg.A cfg.B, Real.Angle.sign_neg]
  rw [h, cfg.sign_CAB]

/-- The oriented angle `∡ B I C` has sign `-s`, since `I` and `A` lie on the same side of `BC`. -/
lemma sign_BIC : (∡ cfg.B cfg.I cfg.C).sign = -cfg.s := by
  have h0 : cfg.ABC.points 0 = cfg.A := rfl
  have hss := cfg.ssameSide_faceOpposite_of_mem_interior cfg.I_mem_interior 0
  rw [h0] at hss
  have e := hss.oangle_sign_eq cfg.B_mem_span_faceOpposite_zero cfg.C_mem_span_faceOpposite_zero
  rw [← e, cfg.sign_BAC]

lemma ne_zero_neg_s : (-cfg.s) ≠ 0 := by
  rcases sign_eq_one_or_neg_one cfg.s_ne_zero with h1 | h1 <;> rw [h1] <;> decide


/-- An interior point splits the angle at `B` into two angles with the same orientation. -/
lemma split_B {Q : EuclideanSpace ℝ (Fin 2)} (hQ : Q ∈ cfg.ABC.interior) :
    ∠ cfg.A cfg.B Q + ∠ Q cfg.B cfg.C = ∠ cfg.A cfg.B cfg.C := by
  have hsigns := cfg.signs_of_mem_interior hQ
  have hQne : Q ≠ cfg.B := cfg.ne_vertex_of_mem_interior hQ 1
  have hadd : ∡ cfg.A cfg.B Q + ∡ Q cfg.B cfg.C = ∡ cfg.A cfg.B cfg.C :=
    oangle_add cfg.A_ne_B hQne cfg.B_ne_C.symm
  have hs2 : (∡ Q cfg.B cfg.C).sign = cfg.s := (oangle_rotate_sign _ _ _).symm.trans hsigns.2.1
  have key := abs_toReal_add_of_sign_eq (θ := ∡ cfg.A cfg.B Q) (ψ := ∡ Q cfg.B cfg.C)
    (by rw [hsigns.1]; exact cfg.s_ne_zero) (by rw [hsigns.1, hs2]) (by rw [hadd]; exact hsigns.1)
  rw [angle_eq_abs_oangle_toReal cfg.A_ne_B cfg.B_ne_C.symm,
    angle_eq_abs_oangle_toReal cfg.A_ne_B hQne,
    angle_eq_abs_oangle_toReal hQne cfg.B_ne_C.symm, ← hadd]
  exact key.symm

/-- An interior point splits the angle at `C` into two angles with the same orientation. -/
lemma split_C {Q : EuclideanSpace ℝ (Fin 2)} (hQ : Q ∈ cfg.ABC.interior) :
    ∠ cfg.A cfg.C Q + ∠ Q cfg.C cfg.B = ∠ cfg.A cfg.C cfg.B := by
  have hsigns := cfg.signs_of_mem_interior hQ
  have hQne : Q ≠ cfg.C := cfg.ne_vertex_of_mem_interior hQ 2
  have hadd : ∡ cfg.A cfg.C Q + ∡ Q cfg.C cfg.B = ∡ cfg.A cfg.C cfg.B :=
    oangle_add cfg.A_ne_C hQne cfg.B_ne_C
  have hs1 : (∡ cfg.A cfg.C Q).sign = -cfg.s := by
    rw [oangle_rev Q cfg.C cfg.A, Real.Angle.sign_neg, ← oangle_rotate_sign Q cfg.C cfg.A,
      hsigns.2.2]
  have hs2 : (∡ Q cfg.C cfg.B).sign = -cfg.s := by
    rw [oangle_rev cfg.B cfg.C Q, Real.Angle.sign_neg, hsigns.2.1]
  have key := abs_toReal_add_of_sign_eq (θ := ∡ cfg.A cfg.C Q) (ψ := ∡ Q cfg.C cfg.B)
    (by rw [hs1]; exact cfg.ne_zero_neg_s) (by rw [hs1, hs2])
    (by rw [hadd, hs1, cfg.sign_ACB])
  rw [angle_eq_abs_oangle_toReal cfg.A_ne_C cfg.B_ne_C,
    angle_eq_abs_oangle_toReal cfg.A_ne_C hQne,
    angle_eq_abs_oangle_toReal hQne cfg.B_ne_C, ← hadd]
  exact key.symm

/-- An interior point splits the angle at `A` into two angles with the same orientation. -/
lemma split_A {Q : EuclideanSpace ℝ (Fin 2)} (hQ : Q ∈ cfg.ABC.interior) :
    ∠ cfg.B cfg.A Q + ∠ Q cfg.A cfg.C = ∠ cfg.B cfg.A cfg.C := by
  have hsigns := cfg.signs_of_mem_interior hQ
  have hQne : Q ≠ cfg.A := cfg.ne_vertex_of_mem_interior hQ 0
  have hadd : ∡ cfg.B cfg.A Q + ∡ Q cfg.A cfg.C = ∡ cfg.B cfg.A cfg.C :=
    oangle_add cfg.A_ne_B.symm hQne cfg.A_ne_C.symm
  have hs1 : (∡ cfg.B cfg.A Q).sign = -cfg.s := by
    rw [oangle_rev Q cfg.A cfg.B, Real.Angle.sign_neg, ← oangle_rotate_sign Q cfg.A cfg.B,
      hsigns.1]
  have hs2 : (∡ Q cfg.A cfg.C).sign = -cfg.s := by
    rw [oangle_rev cfg.C cfg.A Q, Real.Angle.sign_neg, hsigns.2.2]
  have key := abs_toReal_add_of_sign_eq (θ := ∡ cfg.B cfg.A Q) (ψ := ∡ Q cfg.A cfg.C)
    (by rw [hs1]; exact cfg.ne_zero_neg_s) (by rw [hs1, hs2])
    (by rw [hadd, hs1, cfg.sign_BAC])
  rw [angle_eq_abs_oangle_toReal cfg.A_ne_B.symm cfg.A_ne_C.symm,
    angle_eq_abs_oangle_toReal cfg.A_ne_B.symm hQne,
    angle_eq_abs_oangle_toReal hQne cfg.A_ne_C.symm, ← hadd]
  exact key.symm

/-- The incenter bisects the angle at `B`. -/
lemma half_B : ∠ cfg.I cfg.B cfg.C = ∠ cfg.A cfg.B cfg.C / 2 := by
  have hbis : ∡ cfg.A cfg.B cfg.I = ∡ cfg.I cfg.B cfg.C :=
    cfg.ABC.oangle_incenter_eq (i₁ := 1) (i₂ := 0) (i₃ := 2) (by decide) (by decide) (by decide)
  have hund : ∠ cfg.A cfg.B cfg.I = ∠ cfg.I cfg.B cfg.C := by
    rw [angle_eq_abs_oangle_toReal cfg.A_ne_B cfg.I_ne_B,
      angle_eq_abs_oangle_toReal cfg.I_ne_B cfg.B_ne_C.symm, hbis]
  have hsplit := cfg.split_B cfg.I_mem_interior
  linarith

/-- The incenter bisects the angle at `C`. -/
lemma half_C : ∠ cfg.I cfg.C cfg.B = ∠ cfg.A cfg.C cfg.B / 2 := by
  have hbis : ∡ cfg.A cfg.C cfg.I = ∡ cfg.I cfg.C cfg.B :=
    cfg.ABC.oangle_incenter_eq (i₁ := 2) (i₂ := 0) (i₃ := 1) (by decide) (by decide) (by decide)
  have hund : ∠ cfg.A cfg.C cfg.I = ∠ cfg.I cfg.C cfg.B := by
    rw [angle_eq_abs_oangle_toReal cfg.A_ne_C cfg.I_ne_C,
      angle_eq_abs_oangle_toReal cfg.I_ne_C (by exact cfg.B_ne_C), hbis]
  have hsplit := cfg.split_C cfg.I_mem_interior
  linarith

/-- The incenter bisects the angle at `A`. -/
lemma half_A : ∠ cfg.B cfg.A cfg.I = ∠ cfg.B cfg.A cfg.C / 2 := by
  have hbis : ∡ cfg.B cfg.A cfg.I = ∡ cfg.I cfg.A cfg.C :=
    cfg.ABC.oangle_incenter_eq (i₁ := 0) (i₂ := 1) (i₃ := 2) (by decide) (by decide) (by decide)
  have hund : ∠ cfg.B cfg.A cfg.I = ∠ cfg.I cfg.A cfg.C := by
    rw [angle_eq_abs_oangle_toReal cfg.A_ne_B.symm cfg.I_ne_A,
      angle_eq_abs_oangle_toReal cfg.I_ne_A cfg.A_ne_C.symm, hbis]
  have hsplit := cfg.split_A cfg.I_mem_interior
  linarith

lemma angle_sum_ABC :
    ∠ cfg.B cfg.A cfg.C + ∠ cfg.A cfg.C cfg.B + ∠ cfg.C cfg.B cfg.A = Real.pi :=
  angle_add_angle_add_angle_eq_pi cfg.C cfg.A_ne_B

lemma notCollinear_ABC : ¬Collinear ℝ {cfg.A, cfg.B, cfg.C} := by
  rw [← oangle_sign_eq_zero_iff_collinear]
  exact cfg.s_ne_zero

lemma notCollinear_BAC : ¬Collinear ℝ {cfg.B, cfg.A, cfg.C} := by
  rw [← oangle_sign_eq_zero_iff_collinear, cfg.sign_BAC]
  exact cfg.ne_zero_neg_s

lemma notCollinear_ACB : ¬Collinear ℝ {cfg.A, cfg.C, cfg.B} := by
  rw [← oangle_sign_eq_zero_iff_collinear, cfg.sign_ACB]
  exact cfg.ne_zero_neg_s

/-- The angle condition together with the splitting of the angles at `B` and `C` gives
`∠PBC + ∠PCB = (∠B + ∠C)/2`, and hence `∠BPC = ∠BIC`. -/
lemma angle_BPC_eq : ∠ cfg.B cfg.P cfg.C = ∠ cfg.B cfg.I cfg.C := by
  have hsplitP_B := cfg.split_B cfg.hP
  have hsplitP_C := cfg.split_C cfg.hP
  have hcond := cfg.hcond
  rw [angle_comm cfg.P cfg.B cfg.A, angle_comm cfg.P cfg.C cfg.A] at hcond
  have h1 : ∠ cfg.P cfg.B cfg.C + ∠ cfg.P cfg.C cfg.B =
      (∠ cfg.A cfg.B cfg.C + ∠ cfg.A cfg.C cfg.B) / 2 := by linarith
  have h2 : ∠ cfg.I cfg.B cfg.C + ∠ cfg.I cfg.C cfg.B =
      (∠ cfg.A cfg.B cfg.C + ∠ cfg.A cfg.C cfg.B) / 2 := by
    linarith [cfg.half_B, cfg.half_C]
  have hsumP := angle_add_angle_add_angle_eq_pi cfg.C cfg.P_ne_B
  have hsumI := angle_add_angle_add_angle_eq_pi cfg.C cfg.I_ne_B
  rw [angle_comm cfg.C cfg.B cfg.P] at hsumP
  rw [angle_comm cfg.C cfg.B cfg.I] at hsumI
  linarith

/-- The oriented version of `angle_BPC_eq`: `P` and `I` see the segment `BC` under the same
oriented angle. -/
lemma oangle_BPC : ∡ cfg.B cfg.P cfg.C = ∡ cfg.B cfg.I cfg.C := by
  apply oangle_eq_of_angle_eq_of_sign_eq cfg.angle_BPC_eq
  have h0 : cfg.ABC.points 0 = cfg.A := rfl
  have eP : (∡ cfg.B cfg.P cfg.C).sign = (∡ cfg.B cfg.A cfg.C).sign := by
    have hss := cfg.ssameSide_faceOpposite_of_mem_interior cfg.hP 0
    rw [h0] at hss
    exact (hss.oangle_sign_eq cfg.B_mem_span_faceOpposite_zero
      cfg.C_mem_span_faceOpposite_zero).symm
  have eI : (∡ cfg.B cfg.I cfg.C).sign = (∡ cfg.B cfg.A cfg.C).sign := by
    have hss := cfg.ssameSide_faceOpposite_of_mem_interior cfg.I_mem_interior 0
    rw [h0] at hss
    exact (hss.oangle_sign_eq cfg.B_mem_span_faceOpposite_zero
      cfg.C_mem_span_faceOpposite_zero).symm
  rw [eP, eI]

/-- `B`, `I`, `C` are not collinear. -/
lemma notCollinear_BIC : ¬Collinear ℝ {cfg.B, cfg.I, cfg.C} := by
  rw [← oangle_sign_eq_zero_iff_collinear, cfg.sign_BIC]
  exact cfg.ne_zero_neg_s

/-- `B`, `I`, `C` form a genuine triangle. -/
lemma hBIC : AffineIndependent ℝ ![cfg.B, cfg.I, cfg.C] := by
  rw [← oangle_ne_zero_and_ne_pi_iff_affineIndependent]
  exact Real.Angle.sign_ne_zero_iff.1 (by rw [cfg.sign_BIC]; exact cfg.ne_zero_neg_s)

/-- The triangle `BIC`. -/
noncomputable def tBIC : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2)) :=
  ⟨![cfg.B, cfg.I, cfg.C], cfg.hBIC⟩

/-- The circumcenter of `BIC`; it will turn out to be the midpoint of the arc `BC` of the
circumcircle of `ABC`, and `A`, `I`, `M` are collinear. -/
noncomputable def M : EuclideanSpace ℝ (Fin 2) := cfg.tBIC.circumcenter

/-- The circumradius of `BIC`. -/
noncomputable def r : ℝ := cfg.tBIC.circumradius

lemma dist_MB : dist cfg.M cfg.B = cfg.r := dist_circumcenter_eq_circumradius' cfg.tBIC 0

lemma dist_MI : dist cfg.M cfg.I = cfg.r := dist_circumcenter_eq_circumradius' cfg.tBIC 1

lemma dist_MC : dist cfg.M cfg.C = cfg.r := dist_circumcenter_eq_circumradius' cfg.tBIC 2

/-- Since `P` sees `BC` under the same angle as `I`, it lies on the circumcircle of `BIC`. -/
lemma dist_PM : dist cfg.P cfg.M = cfg.r := by
  have h2 : (2 : ℤ) • ∡ (cfg.tBIC.points 0) cfg.P (cfg.tBIC.points 2) =
      (2 : ℤ) • ∡ (cfg.tBIC.points 0) (cfg.tBIC.points 1) (cfg.tBIC.points 2) := by
    show (2 : ℤ) • ∡ cfg.B cfg.P cfg.C = (2 : ℤ) • ∡ cfg.B cfg.I cfg.C
    rw [cfg.oangle_BPC]
  have hmem := Affine.Triangle.mem_circumsphere_of_two_zsmul_oangle_eq
    (t := cfg.tBIC) (p := cfg.P) (i₁ := 0) (i₂ := 1) (i₃ := 2)
    (by decide) (by decide) (by decide) h2
  rwa [mem_sphere, Affine.Simplex.circumsphere_center,
    Affine.Simplex.circumsphere_radius] at hmem

/-- The undirected angle `∠ B I C` equals `(π + ∠A)/2`. -/
lemma angle_BIC : ∠ cfg.B cfg.I cfg.C = (Real.pi + ∠ cfg.B cfg.A cfg.C) / 2 := by
  have hsumI := angle_add_angle_add_angle_eq_pi cfg.C cfg.I_ne_B
  rw [angle_comm cfg.C cfg.B cfg.I] at hsumI
  have hsum := cfg.angle_sum_ABC
  rw [angle_comm cfg.C cfg.B cfg.A] at hsum
  have hβ := cfg.half_B
  have hγ := cfg.half_C
  linarith

/-- The oriented angle `∡ B I C`, made explicit. -/
lemma oangle_BIC : ∡ cfg.B cfg.I cfg.C =
    ((-cfg.s : SignType) : ℤ) • (((Real.pi + ∠ cfg.B cfg.A cfg.C) / 2 : ℝ) : Real.Angle) := by
  have hα0 : 0 < ∠ cfg.B cfg.A cfg.C := angle_pos_of_not_collinear cfg.notCollinear_BAC
  have hαπ : ∠ cfg.B cfg.A cfg.C < Real.pi := angle_lt_pi_of_not_collinear cfg.notCollinear_BAC
  apply oangle_eq_sign_zsmul_coe (x := (Real.pi + ∠ cfg.B cfg.A cfg.C) / 2)
  · linarith [Real.pi_pos]
  · linarith
  · rw [← angle_eq_abs_oangle_toReal cfg.I_ne_B.symm cfg.I_ne_C.symm, cfg.angle_BIC]
  · exact cfg.ne_zero_neg_s
  · exact cfg.sign_BIC

/-- The oriented angle `∡ B M C`, made explicit: it is twice `∡ B I C` since `M` is the
circumcenter of `BIC`. -/
lemma oangle_BMC : ∡ cfg.B cfg.M cfg.C =
    (cfg.s : ℤ) • (((Real.pi - ∠ cfg.B cfg.A cfg.C) : ℝ) : Real.Angle) := by
  have hcentral : ∡ cfg.B cfg.M cfg.C = (2 : ℤ) • ∡ cfg.B cfg.I cfg.C := by
    have h := Sphere.oangle_center_eq_two_zsmul_oangle (s := cfg.tBIC.circumsphere)
      (cfg.tBIC.mem_circumsphere 0) (cfg.tBIC.mem_circumsphere 1) (cfg.tBIC.mem_circumsphere 2)
      cfg.I_ne_B cfg.I_ne_C
    rwa [Affine.Simplex.circumsphere_center] at h
  rw [hcentral, cfg.oangle_BIC]
  rcases sign_eq_one_or_neg_one cfg.s_ne_zero with h1 | h1
  · rw [h1]
    show (2 : ℤ) • ((-1 : ℤ) • (((Real.pi + ∠ cfg.B cfg.A cfg.C) / 2 : ℝ) : Real.Angle)) =
      (1 : ℤ) • (((Real.pi - ∠ cfg.B cfg.A cfg.C) : ℝ) : Real.Angle)
    rw [neg_one_zsmul, one_zsmul, smul_neg, ← Real.Angle.coe_zsmul,
      show (2 : ℤ) • ((Real.pi + ∠ cfg.B cfg.A cfg.C) / 2) = Real.pi + ∠ cfg.B cfg.A cfg.C from by
        rw [zsmul_eq_mul]; ring, ← Real.Angle.coe_neg]
    exact Real.Angle.angle_eq_iff_two_pi_dvd_sub.2 ⟨-1, by push_cast; ring⟩
  · rw [h1]
    show (2 : ℤ) • ((1 : ℤ) • (((Real.pi + ∠ cfg.B cfg.A cfg.C) / 2 : ℝ) : Real.Angle)) =
      (-1 : ℤ) • (((Real.pi - ∠ cfg.B cfg.A cfg.C) : ℝ) : Real.Angle)
    rw [one_zsmul, neg_one_zsmul, ← Real.Angle.coe_zsmul,
      show (2 : ℤ) • ((Real.pi + ∠ cfg.B cfg.A cfg.C) / 2) = Real.pi + ∠ cfg.B cfg.A cfg.C from by
        rw [zsmul_eq_mul]; ring, ← Real.Angle.coe_neg]
    exact Real.Angle.angle_eq_iff_two_pi_dvd_sub.2 ⟨1, by push_cast; ring⟩

lemma sign_BMC : (∡ cfg.B cfg.M cfg.C).sign = cfg.s := by
  rw [cfg.oangle_BMC]
  have hα0 : 0 < ∠ cfg.B cfg.A cfg.C := angle_pos_of_not_collinear cfg.notCollinear_BAC
  have hαπ : ∠ cfg.B cfg.A cfg.C < Real.pi := angle_lt_pi_of_not_collinear cfg.notCollinear_BAC
  have hto : ((Real.pi - ∠ cfg.B cfg.A cfg.C : ℝ) : Real.Angle).toReal =
      Real.pi - ∠ cfg.B cfg.A cfg.C :=
    Real.Angle.toReal_coe_eq_self_iff.2 ⟨by linarith [Real.pi_pos], by linarith⟩
  have hs1 : ((Real.pi - ∠ cfg.B cfg.A cfg.C : ℝ) : Real.Angle).sign = 1 :=
    Real.Angle.toReal_mem_Ioo_iff_sign_pos.1 (hto.symm ▸ ⟨by linarith, by linarith⟩)
  rcases sign_eq_one_or_neg_one cfg.s_ne_zero with h1 | h1
  · rw [h1, show ((1 : SignType) : ℤ) = 1 from rfl, one_zsmul, hs1]
  · rw [h1, show ((-1 : SignType) : ℤ) = -1 from rfl, neg_one_zsmul, Real.Angle.sign_neg, hs1]

lemma B_ne_M : cfg.B ≠ cfg.M := by
  apply left_ne_of_oangle_sign_ne_zero
  rw [cfg.sign_BMC]
  exact cfg.s_ne_zero

lemma C_ne_M : cfg.C ≠ cfg.M := by
  apply right_ne_of_oangle_sign_ne_zero
  rw [cfg.sign_BMC]
  exact cfg.s_ne_zero

/-- `M` differs from `I`: they see `BC` under oriented angles of opposite signs. -/
lemma M_ne_I : cfg.M ≠ cfg.I := by
  intro h
  have h1 := cfg.sign_BMC
  rw [h] at h1
  have h2 : cfg.s = -cfg.s := h1.symm.trans cfg.sign_BIC
  rcases sign_eq_one_or_neg_one cfg.s_ne_zero with h3 | h3
  · rw [h3] at h2
    exact absurd h2 (by decide)
  · rw [h3] at h2
    exact absurd h2 (by decide)

/-- The undirected angle `∠ B M C` equals `π - ∠A`. -/
lemma angle_BMC : ∠ cfg.B cfg.M cfg.C = Real.pi - ∠ cfg.B cfg.A cfg.C := by
  rw [angle_eq_abs_oangle_toReal cfg.B_ne_M cfg.C_ne_M, cfg.oangle_BMC]
  exact abs_toReal_sign_zsmul_coe
    (by linarith [angle_le_pi cfg.B cfg.A cfg.C])
    (by linarith [angle_pos_of_not_collinear cfg.notCollinear_BAC]) cfg.s_ne_zero

/-- The triangle `MBC` is isosceles with apex angle `π - ∠A`, hence base angles `∠A/2`. -/
lemma angle_CBM : ∠ cfg.C cfg.B cfg.M = ∠ cfg.B cfg.A cfg.C / 2 := by
  have hisos : ∠ cfg.M cfg.B cfg.C = ∠ cfg.M cfg.C cfg.B :=
    angle_eq_angle_of_dist_eq (by rw [cfg.dist_MB, cfg.dist_MC])
  rw [angle_comm cfg.M cfg.B cfg.C] at hisos
  have hsum := angle_add_angle_add_angle_eq_pi cfg.M cfg.B_ne_C
  linarith [cfg.angle_BMC]

/-- The oriented angle `∡ C B M`, made explicit. -/
lemma oangle_CBM : ∡ cfg.C cfg.B cfg.M =
    (cfg.s : ℤ) • ((∠ cfg.B cfg.A cfg.C / 2 : ℝ) : Real.Angle) := by
  apply oangle_eq_sign_zsmul_coe (x := ∠ cfg.B cfg.A cfg.C / 2)
  · linarith [angle_pos_of_not_collinear cfg.notCollinear_BAC]
  · linarith [Real.pi_pos, angle_lt_pi_of_not_collinear cfg.notCollinear_BAC]
  · rw [← angle_eq_abs_oangle_toReal cfg.B_ne_C.symm cfg.B_ne_M.symm, cfg.angle_CBM]
  · exact cfg.s_ne_zero
  · exact (oangle_rotate_sign cfg.C cfg.B cfg.M).symm.trans cfg.sign_BMC

/-- The oriented angle `∡ M B C`, made explicit. -/
lemma oangle_MBC : ∡ cfg.M cfg.B cfg.C =
    ((-cfg.s : SignType) : ℤ) • ((∠ cfg.B cfg.A cfg.C / 2 : ℝ) : Real.Angle) := by
  rw [oangle_rev cfg.C cfg.B cfg.M, cfg.oangle_CBM]
  rcases sign_eq_one_or_neg_one cfg.s_ne_zero with h1 | h1
  · rw [h1, show ((1 : SignType) : ℤ) = 1 from rfl, one_zsmul,
      show ((-(1 : SignType) : SignType) : ℤ) = -1 from rfl, neg_one_zsmul]
  · rw [h1, show ((-1 : SignType) : ℤ) = -1 from rfl, neg_one_zsmul,
      show ((-(-1 : SignType) : SignType) : ℤ) = 1 from rfl, one_zsmul, neg_neg]

/-- The oriented angle `∡ C B I`, made explicit. -/
lemma oangle_CBI : ∡ cfg.C cfg.B cfg.I =
    ((-cfg.s : SignType) : ℤ) • ((∠ cfg.A cfg.B cfg.C / 2 : ℝ) : Real.Angle) := by
  apply oangle_eq_sign_zsmul_coe (x := ∠ cfg.A cfg.B cfg.C / 2)
  · linarith [angle_pos_of_not_collinear cfg.notCollinear_ABC]
  · linarith [Real.pi_pos, angle_lt_pi_of_not_collinear cfg.notCollinear_ABC]
  · rw [← angle_eq_abs_oangle_toReal cfg.B_ne_C.symm cfg.I_ne_B,
      angle_comm cfg.C cfg.B cfg.I, cfg.half_B]
  · exact cfg.ne_zero_neg_s
  · exact (oangle_rotate_sign cfg.C cfg.B cfg.I).symm.trans cfg.sign_BIC

/-- The undirected angle `∠ A I B`. -/
lemma angle_AIB :
    ∠ cfg.A cfg.I cfg.B = Real.pi - ∠ cfg.B cfg.A cfg.C / 2 - ∠ cfg.A cfg.B cfg.C / 2 := by
  have hsum := angle_add_angle_add_angle_eq_pi cfg.B cfg.I_ne_A
  rw [angle_comm cfg.I cfg.B cfg.A] at hsum
  have hα := cfg.half_A
  have hβ := cfg.half_B
  have hbiso : ∡ cfg.A cfg.B cfg.I = ∡ cfg.I cfg.B cfg.C :=
    cfg.ABC.oangle_incenter_eq (i₁ := 1) (i₂ := 0) (i₃ := 2) (by decide) (by decide) (by decide)
  have hbis : ∠ cfg.A cfg.B cfg.I = ∠ cfg.I cfg.B cfg.C := by
    rw [angle_eq_abs_oangle_toReal cfg.A_ne_B cfg.I_ne_B,
      angle_eq_abs_oangle_toReal cfg.I_ne_B cfg.B_ne_C.symm, hbiso]
  linarith

/-- The oriented angle `∡ A I B` has sign `-s`, since `I` and `C` lie on the same side of `AB`. -/
lemma sign_AIB : (∡ cfg.A cfg.I cfg.B).sign = -cfg.s := by
  have hss := cfg.ssameSide_faceOpposite_of_mem_interior cfg.I_mem_interior 2
  have h2 : cfg.ABC.points 2 = cfg.C := rfl
  rw [h2] at hss
  have e := hss.oangle_sign_eq cfg.A_mem_span_faceOpposite_two cfg.B_mem_span_faceOpposite_two
  rw [← e, cfg.sign_ACB]

/-- The oriented angle `∡ A I B`, made explicit. -/
lemma oangle_AIB : ∡ cfg.A cfg.I cfg.B =
    ((-cfg.s : SignType) : ℤ) •
      (((Real.pi - ∠ cfg.B cfg.A cfg.C / 2 - ∠ cfg.A cfg.B cfg.C / 2 : ℝ)) : Real.Angle) := by
  apply oangle_eq_sign_zsmul_coe
  · have hsum := cfg.angle_sum_ABC
    rw [angle_comm cfg.C cfg.B cfg.A] at hsum
    have hγ0 : 0 < ∠ cfg.A cfg.C cfg.B := angle_pos_of_not_collinear cfg.notCollinear_ACB
    linarith [Real.pi_pos]
  · have hα0 : 0 < ∠ cfg.B cfg.A cfg.C := angle_pos_of_not_collinear cfg.notCollinear_BAC
    have hβ0 : 0 < ∠ cfg.A cfg.B cfg.C := angle_pos_of_not_collinear cfg.notCollinear_ABC
    linarith
  · rw [← angle_eq_abs_oangle_toReal cfg.I_ne_A.symm cfg.I_ne_B.symm, cfg.angle_AIB]
  · exact cfg.ne_zero_neg_s
  · exact cfg.sign_AIB

/-- The oriented angle `∡ M B I`, made explicit by splitting along `BC`. -/
lemma oangle_MBI : ∡ cfg.M cfg.B cfg.I =
    ((-cfg.s : SignType) : ℤ) •
      ((((∠ cfg.B cfg.A cfg.C + ∠ cfg.A cfg.B cfg.C) / 2 : ℝ)) : Real.Angle) := by
  have hadd : ∡ cfg.M cfg.B cfg.C + ∡ cfg.C cfg.B cfg.I = ∡ cfg.M cfg.B cfg.I :=
    oangle_add cfg.B_ne_M.symm cfg.B_ne_C.symm cfg.I_ne_B
  rw [← hadd, cfg.oangle_MBC, cfg.oangle_CBI, ← smul_add, ← Real.Angle.coe_add]
  congr 2
  ring

/-- The triangle `MBI` is isosceles with `MB = MI`, so its base angles agree. -/
lemma oangle_BIM : ∡ cfg.B cfg.I cfg.M = ∡ cfg.M cfg.B cfg.I := by
  apply oangle_eq_of_angle_eq_of_sign_eq
  · have hdist : dist cfg.M cfg.B = dist cfg.M cfg.I := by rw [cfg.dist_MB, cfg.dist_MI]
    have h := angle_eq_angle_of_dist_eq hdist
    rw [angle_comm cfg.M cfg.I cfg.B] at h
    exact h.symm
  · calc (∡ cfg.B cfg.I cfg.M).sign = (∡ cfg.I cfg.M cfg.B).sign := (oangle_rotate_sign _ _ _).symm
    _ = (∡ cfg.M cfg.B cfg.I).sign := (oangle_rotate_sign _ _ _).symm

/-- The key collinearity: `A`, `I`, `M` see each other under the angle `π` at `I`. -/
lemma oangle_AIM : ∡ cfg.A cfg.I cfg.M = Real.pi := by
  have hadd : ∡ cfg.A cfg.I cfg.B + ∡ cfg.B cfg.I cfg.M = ∡ cfg.A cfg.I cfg.M :=
    oangle_add cfg.I_ne_A.symm cfg.I_ne_B.symm cfg.M_ne_I
  rw [← hadd, cfg.oangle_AIB, cfg.oangle_BIM, cfg.oangle_MBI, ← smul_add, ← Real.Angle.coe_add]
  have he : Real.pi - ∠ cfg.B cfg.A cfg.C / 2 - ∠ cfg.A cfg.B cfg.C / 2 +
      (∠ cfg.B cfg.A cfg.C + ∠ cfg.A cfg.B cfg.C) / 2 = Real.pi := by ring
  rw [he]
  rcases sign_eq_one_or_neg_one cfg.s_ne_zero with h1 | h1
  · rw [h1, show ((-(1 : SignType) : SignType) : ℤ) = -1 from rfl, neg_one_zsmul,
      Real.Angle.neg_coe_pi]
  · rw [h1, show ((-(-1 : SignType) : SignType) : ℤ) = 1 from rfl, one_zsmul]

/-- `I` lies strictly between `A` and `M`. -/
lemma sbtw_AIM : Sbtw ℝ cfg.A cfg.I cfg.M := by
  rw [← angle_eq_pi_iff_sbtw, ← oangle_eq_pi_iff_angle_eq_pi]
  exact cfg.oangle_AIM

lemma A_ne_M : cfg.A ≠ cfg.M := cfg.sbtw_AIM.left_ne_right

/-- The distance from `P` to `M` equals the distance from `I` to `M`. -/
lemma dist_PM_eq_dist_IM : dist cfg.P cfg.M = dist cfg.I cfg.M := by
  rw [cfg.dist_PM, dist_comm cfg.I cfg.M, cfg.dist_MI]

/-- The main inequality `AI ≤ AP`: the triangle inequality `AM ≤ AP + PM` together with
`AM = AI + IM` and `PM = IM`. -/
lemma AI_le_AP : dist cfg.A cfg.I ≤ dist cfg.A cfg.P := by
  have hAM : dist cfg.A cfg.I + dist cfg.I cfg.M = dist cfg.A cfg.M :=
    cfg.sbtw_AIM.wbtw.dist_add_dist
  have htri : dist cfg.A cfg.M ≤ dist cfg.A cfg.P + dist cfg.P cfg.M := dist_triangle _ _ _
  linarith [cfg.dist_PM_eq_dist_IM]

/-- The equality case: `AP = AI` forces the triangle inequality `AM ≤ AP + PM` to be an
equality, so `P` lies on the segment `AM`; but that segment meets the circle through
`B`, `I`, `C` centered at `M` only at `I`. -/
lemma eq_of_dist_eq (h : dist cfg.A cfg.P = dist cfg.A cfg.I) : cfg.P = cfg.I := by
  have hAM : dist cfg.A cfg.I + dist cfg.I cfg.M = dist cfg.A cfg.M :=
    cfg.sbtw_AIM.wbtw.dist_add_dist
  have hw : Wbtw ℝ cfg.A cfg.P cfg.M := by
    rw [← dist_add_dist_eq_iff]
    linarith [cfg.dist_PM_eq_dist_IM]
  obtain ⟨t₁, ht₁, hP⟩ := by
    have hmem := mem_segment_iff_wbtw.2 hw
    rw [segment_eq_image_lineMap] at hmem
    exact hmem
  obtain ⟨t₂, ht₂, hI⟩ := by
    have hmem := mem_segment_iff_wbtw.2 cfg.sbtw_AIM.wbtw
    rw [segment_eq_image_lineMap] at hmem
    exact hmem
  have hd : dist cfg.A cfg.M ≠ 0 := (dist_pos.mpr cfg.A_ne_M).ne'
  have eP : dist cfg.P cfg.M = (1 - t₁) * dist cfg.A cfg.M := by
    rw [← hP, dist_lineMap_right, Real.norm_eq_abs,
      abs_of_nonneg (by linarith [ht₁.2] : (0 : ℝ) ≤ 1 - t₁)]
  have eI : dist cfg.I cfg.M = (1 - t₂) * dist cfg.A cfg.M := by
    rw [← hI, dist_lineMap_right, Real.norm_eq_abs,
      abs_of_nonneg (by linarith [ht₂.2] : (0 : ℝ) ≤ 1 - t₂)]
  have htt : t₁ = t₂ := by
    have : (1 - t₁) * dist cfg.A cfg.M = (1 - t₂) * dist cfg.A cfg.M := by
      rw [← eP, ← eI]
      exact cfg.dist_PM_eq_dist_IM
    have := mul_right_cancel₀ hd this
    linarith
  rw [← hP, ← hI, htt]

/-- The full conclusion of the problem. -/
theorem result :
    dist cfg.A cfg.I ≤ dist cfg.A cfg.P ∧ (dist cfg.A cfg.P = dist cfg.A cfg.I ↔ cfg.P = cfg.I) :=
  ⟨cfg.AI_le_AP, ⟨cfg.eq_of_dist_eq, fun h => by rw [h]⟩⟩

end Imo2006P1Cfg
snip end

problem imo2006_p1
    (A B C P : EuclideanSpace ℝ (Fin 2))
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hP : P ∈ (⟨![A, B, C], hABC⟩ : Affine.Triangle ℝ _).interior)
    (hcond : ∠ P B A + ∠ P C A = ∠ P B C + ∠ P C B) :
    let t : Affine.Triangle ℝ _ := ⟨![A, B, C], hABC⟩
    dist A t.incenter ≤ dist A P ∧ (dist A P = dist A t.incenter ↔ P = t.incenter) := by
  set cfg : Imo2006P1Cfg := ⟨A, B, C, P, hABC, hP, hcond⟩
  exact cfg.result

end Imo2006P1
