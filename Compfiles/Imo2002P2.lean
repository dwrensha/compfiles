/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
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
# International Mathematical Olympiad 2002, Problem 2

BC is a diameter of a circle center O. A is any point on the circle with
angle AOC > 60°. EF is the chord which is the perpendicular bisector of AO.
D is the midpoint of the minor arc AB. The line through O parallel to AD
meets AC at J. Show that J is the incenter of triangle CEF.
-/

open Affine Affine.Simplex EuclideanGeometry FiniteDimensional Module

open scoped Affine EuclideanGeometry Real RealInnerProductSpace

attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

variable (V : Type*) (Pt : Type*)

variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace Pt]

variable [NormedAddTorsor V Pt]

namespace Imo2002P2

snip begin

/-- A default choice of orientation, for lemmas that need to pick one. -/
@[implicit_reducible]
noncomputable def someOrientation [hd2 : Fact (finrank ℝ V = 2)] : Module.Oriented ℝ V (Fin 2) :=
  ⟨Basis.orientation (finBasisOfFinrankEq _ _ hd2.out)⟩

/- ### Helper lemmas -/

variable {V Pt}

/-- An oriented angle is determined by its unoriented measure (in `(0, π)`) and its sign. -/
theorem Orientation.oangle_eq_coe_sign_mul {o : Orientation ℝ V (Fin 2)} {x y : V}
    [Fact (finrank ℝ V = 2)]
    {t : ℝ} {s : SignType} (hx : x ≠ 0) (hy : y ≠ 0) (ht0 : 0 < t) (htπ : t < π)
    (hang : InnerProductGeometry.angle x y = t) (hsign : (o.oangle x y).sign = s) :
    o.oangle x y = ((s : ℝ) * t : ℝ) := by
  have hs0 : s ≠ 0 := by
    rw [← hsign]
    apply Real.Angle.sign_ne_zero_iff.2
    constructor
    · intro h
      rw [o.angle_eq_abs_oangle_toReal hx hy, h, Real.Angle.toReal_zero, abs_zero] at hang
      linarith
    · intro h
      rw [o.angle_eq_abs_oangle_toReal hx hy, h, Real.Angle.toReal_pi,
        abs_of_nonneg Real.pi_pos.le] at hang
      linarith
  have hs1 : s = 1 ∨ s = -1 := by
    rcases s with _ | _ | _
    · exact (hs0 rfl).elim
    · exact Or.inr rfl
    · exact Or.inl rfl
  have hst : (((s : ℝ) * t : ℝ) : Real.Angle).sign = s := by
    rcases hs1 with rfl | rfl
    · rw [Real.Angle.sign, Real.Angle.sin_coe, SignType.coe_one, one_mul]
      exact sign_pos (Real.sin_pos_of_mem_Ioo ⟨ht0, htπ⟩)
    · rw [Real.Angle.sign, Real.Angle.sin_coe, SignType.coe_neg, SignType.coe_one, neg_mul,
        one_mul, Real.sin_neg]
      exact sign_neg (neg_lt_zero.2 (Real.sin_pos_of_mem_Ioo ⟨ht0, htπ⟩))
  rw [Real.Angle.eq_iff_abs_toReal_eq_of_sign_eq (by rw [hst, hsign])]
  have htr : (((s : ℝ) * t : ℝ) : Real.Angle).toReal = (s : ℝ) * t := by
    rw [Real.Angle.toReal_coe_eq_self_iff]
    rcases hs1 with rfl | rfl <;>
      simp only [SignType.coe_one, one_mul, SignType.coe_neg, SignType.coe_one, neg_mul] <;>
      constructor <;> linarith [ht0, htπ, Real.pi_pos]
  rw [← o.angle_eq_abs_oangle_toReal hx hy, hang, htr]
  rcases hs1 with rfl | rfl <;> simp [abs_of_pos ht0]

/-- Two oriented angles with equal doubles and equal signs are equal. -/
theorem Real.Angle.eq_of_two_zsmul_eq_of_sign_eq {θ ψ : Real.Angle}
    (h2 : (2 : ℤ) • θ = (2 : ℤ) • ψ) (hs : θ.sign = ψ.sign) (h0 : ψ ≠ 0) (hπ : ψ ≠ π) :
    θ = ψ := by
  rcases Real.Angle.two_zsmul_eq_iff.1 h2 with h | h
  · exact h
  exfalso
  rw [h, Real.Angle.sign_add_pi] at hs
  have hs0 : ψ.sign ≠ 0 := Real.Angle.sign_ne_zero_iff.2 ⟨h0, hπ⟩
  have hcon : (ψ.sign : ℝ) = 0 := by
    have h' := congrArg (fun x : SignType => (x : ℝ)) hs
    simp only [SignType.coe_neg] at h'
    linarith
  have hz : ∀ s : SignType, (s : ℝ) = 0 → s = 0 := by
    intro s; fin_cases s <;> simp
  exact hs0 (hz _ hcon)

/-- In an isosceles triangle `POQ` with `OP = OQ` (non-degenerate), the base oriented angles are
the sign of the apex oriented angle times half the complement of the apex angle. -/
theorem oangle_base_eq_sign_mul_of_dist_eq [Module.Oriented ℝ V (Fin 2)]
    [Fact (finrank ℝ V = 2)] {O P Q : Pt}
    (hdist : dist O P = dist O Q) (hnc : ¬Collinear ℝ ({P, O, Q} : Set Pt)) :
    ∡ O Q P = (((∡ P O Q).sign : ℝ) * ((π - ∠ P O Q) / 2) : ℝ) ∧
    ∡ O P Q = -((((∡ P O Q).sign : ℝ) * ((π - ∠ P O Q) / 2) : ℝ)) := by
  have hai : AffineIndependent ℝ ![P, O, Q] := affineIndependent_iff_not_collinear_set.2 hnc
  have haiQP : AffineIndependent ℝ ![O, Q, P] := by
    apply affineIndependent_iff_not_collinear_set.2
    rw [show ({O, Q, P} : Set Pt) = {P, O, Q} from by ext x; simp; tauto]
    exact hnc
  have haiPQ : AffineIndependent ℝ ![O, P, Q] := by
    apply affineIndependent_iff_not_collinear_set.2
    rw [show ({O, P, Q} : Set Pt) = {P, O, Q} from by ext x; simp; tauto]
    exact hnc
  have hφ : ∡ P O Q ≠ 0 ∧ ∡ P O Q ≠ π := oangle_ne_zero_and_ne_pi_iff_affineIndependent.2 hai
  have hu_ne : ∡ O Q P ≠ 0 ∧ ∡ O Q P ≠ π := oangle_ne_zero_and_ne_pi_iff_affineIndependent.2 haiQP
  have hv_ne : ∡ O P Q ≠ 0 ∧ ∡ O P Q ≠ π := oangle_ne_zero_and_ne_pi_iff_affineIndependent.2 haiPQ
  have hPO : P ≠ O := hai.injective.ne (by decide : (0 : Fin 3) ≠ 1)
  have hQO : Q ≠ O := hai.injective.ne (by decide : (2 : Fin 3) ≠ 1)
  have hPQ : P ≠ Q := hai.injective.ne (by decide : (0 : Fin 3) ≠ 2)
  have hap0 : 0 < ∠ P O Q := by
    have hne : ∠ P O Q ≠ 0 := mt (oangle_eq_zero_iff_angle_eq_zero hPO hQO).2 hφ.1
    exact lt_of_le_of_ne' (angle_nonneg _ _ _) hne
  have hapπ : ∠ P O Q < π := by
    refine lt_of_le_of_ne (angle_le_pi _ _ _) (fun h => hφ.2 ?_)
    exact oangle_eq_pi_iff_angle_eq_pi.2 h
  have hβ0 : 0 < (π - ∠ P O Q) / 2 := by linarith
  have hβπ : (π - ∠ P O Q) / 2 < π := by linarith
  have hbase : ∠ O Q P = ∠ O P Q := angle_eq_angle_of_dist_eq hdist.symm
  have hsum : ∠ P O Q + ∠ O Q P + ∠ Q P O = π := angle_add_angle_add_angle_eq_pi Q hPO.symm
  rw [angle_comm Q P O] at hsum
  have hβu : ∠ O Q P = (π - ∠ P O Q) / 2 := by linarith [hbase]
  have hβv : ∠ O P Q = (π - ∠ P O Q) / 2 := by linarith [hbase]
  have hu : ∡ O Q P = (((∡ O Q P).sign : ℝ) * ((π - ∠ P O Q) / 2) : ℝ) :=
    Orientation.oangle_eq_coe_sign_mul (o := positiveOrientation)
      (vsub_ne_zero.2 hQO.symm) (vsub_ne_zero.2 hPQ) hβ0 hβπ hβu rfl
  have hv : ∡ O P Q = (((∡ O P Q).sign : ℝ) * ((π - ∠ P O Q) / 2) : ℝ) :=
    Orientation.oangle_eq_coe_sign_mul (o := positiveOrientation)
      (vsub_ne_zero.2 hPO.symm) (vsub_ne_zero.2 hPQ.symm) hβ0 hβπ hβv rfl
  have hosum : ∡ P O Q + ∡ O Q P + ∡ Q P O = π :=
    oangle_add_oangle_add_oangle_eq_pi hPO.symm hQO hPQ
  rw [oangle_rev O P Q] at hosum
  have hsu0 : (∡ O Q P).sign ≠ 0 := Real.Angle.sign_ne_zero_iff.2 hu_ne
  have hsv0 : (∡ O P Q).sign ≠ 0 := Real.Angle.sign_ne_zero_iff.2 hv_ne
  have hcase : ∀ s : SignType, s ≠ 0 → s = 1 ∨ s = -1 := by
    intro s hs
    rcases s with _ | _ | _
    · exact (hs rfl).elim
    · exact Or.inr rfl
    · exact Or.inl rfl
  rcases hcase _ hsu0 with hsu | hsu <;> rcases hcase _ hsv0 with hsv | hsv
  · exfalso
    apply hφ.2
    have h := hosum
    rw [hu, hsu, hv, hsv] at h
    simp only [SignType.coe_one, one_mul] at h
    have h2 := eq_sub_iff_add_eq.2
      (show ∡ P O Q + (↑((π - ∠ P O Q) / 2) + -↑((π - ∠ P O Q) / 2)) = π from by
        rw [← add_assoc]; exact h)
    simpa using h2
  · have hφ' : ∡ P O Q = ((π - 2 * ((π - ∠ P O Q) / 2) : ℝ) : Real.Angle) := by
      have h := hosum
      rw [hu, hsu, hv, hsv] at h
      simp only [SignType.coe_one, one_mul, SignType.coe_neg, neg_mul, Real.Angle.coe_neg,
        neg_neg] at h
      have h2 := eq_sub_iff_add_eq.2
        (show ∡ P O Q + (↑((π - ∠ P O Q) / 2) + ↑((π - ∠ P O Q) / 2)) = π from by
          rw [← add_assoc]; exact h)
      rw [h2, ← Real.Angle.coe_add, ← Real.Angle.coe_sub]
      congr 1
      ring
    have hsφ : (∡ P O Q).sign = 1 := by
      rw [hφ', Real.Angle.sign, Real.Angle.sin_coe,
        show π - 2 * ((π - ∠ P O Q) / 2) = ∠ P O Q by ring]
      exact sign_pos (Real.sin_pos_of_mem_Ioo ⟨hap0, hapπ⟩)
    constructor
    · rw [hu, hsu, hsφ]
    · rw [hv, hsv, hsφ]
      simp [Real.Angle.coe_neg]
  · have hφ' : ∡ P O Q = ((π + 2 * ((π - ∠ P O Q) / 2) : ℝ) : Real.Angle) := by
      have h := hosum
      rw [hu, hsu, hv, hsv] at h
      simp only [SignType.coe_one, one_mul, SignType.coe_neg, neg_mul, Real.Angle.coe_neg] at h
      have h2 := eq_sub_iff_add_eq.2
        (show ∡ P O Q + (-↑((π - ∠ P O Q) / 2) + -↑((π - ∠ P O Q) / 2)) = π from by
          rw [← add_assoc]; exact h)
      rw [h2, ← Real.Angle.coe_neg, ← Real.Angle.coe_add, ← Real.Angle.coe_sub]
      congr 1
      ring
    have hsφ : (∡ P O Q).sign = -1 := by
      rw [hφ', Real.Angle.sign, Real.Angle.sin_coe,
        show π + 2 * ((π - ∠ P O Q) / 2) = 2 * ((π - ∠ P O Q) / 2) + π by ring,
        Real.sin_add_pi]
      exact sign_neg (neg_lt_zero.2 (Real.sin_pos_of_mem_Ioo ⟨by linarith, by linarith⟩))
    constructor
    · rw [hu, hsu, hsφ]
    · rw [hv, hsv, hsφ]
      simp [Real.Angle.coe_neg]
  · exfalso
    apply hφ.2
    have h := hosum
    rw [hu, hsu, hv, hsv] at h
    simp only [SignType.coe_one, one_mul, SignType.coe_neg, neg_mul] at h
    have h2 := eq_sub_iff_add_eq.2
      (show ∡ P O Q + (↑(-((π - ∠ P O Q) / 2)) + -↑(-((π - ∠ P O Q) / 2))) = π from by
        rw [← add_assoc]; exact h)
    simpa using h2

/-- Two points, one the center `K` of a circle through `X` and `Y` (with `K` not the midpoint of
`XY`), the other `Q` with `⟪Q - M, K - M⟫ > 0` for `M` the midpoint of `XY`, are strictly on the
same side of line `XY`. -/
theorem sSameSide_center_of_inner_pos [Fact (finrank ℝ V = 2)] {X Y K Q : Pt}
    (hdist : dist K X = dist K Y) (hXY : X ≠ Y) (hKne : K ≠ midpoint ℝ X Y)
    (hQ : 0 < ⟪Q -ᵥ midpoint ℝ X Y, K -ᵥ midpoint ℝ X Y⟫) :
    line[ℝ, X, Y].SSameSide K Q := by
  have hMd : dist (midpoint ℝ X Y) X = dist (midpoint ℝ X Y) Y := by
    rw [dist_midpoint_left, dist_midpoint_right]
  have hKX : dist X K = dist Y K := by rw [dist_comm X K, dist_comm Y K, hdist]
  have hKM : dist X (midpoint ℝ X Y) = dist Y (midpoint ℝ X Y) := by
    rw [dist_comm X, dist_comm Y, hMd]
  have hperp0 : ⟪midpoint ℝ X Y -ᵥ K, Y -ᵥ X⟫ = 0 :=
    inner_vsub_vsub_of_dist_eq_of_dist_eq hKX hKM
  have hperp : ⟪Y -ᵥ X, K -ᵥ midpoint ℝ X Y⟫ = 0 := by
    rw [inner_eq_zero_symm] at hperp0
    rw [← neg_vsub_eq_vsub_rev (midpoint ℝ X Y) K, inner_neg_right, hperp0, neg_zero]
  have hM_mem : midpoint ℝ X Y ∈ line[ℝ, X, Y] := (wbtw_midpoint ℝ X Y).mem_affineSpan
  have hspan : (ℝ ∙ (K -ᵥ midpoint ℝ X Y))ᗮ = ℝ ∙ (Y -ᵥ X) := by
    symm
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_singleton_le_iff_mem]
      exact (Submodule.mem_orthogonal_singleton_iff_inner_left).2 hperp
    · rw [finrank_span_singleton (vsub_ne_zero.2 hXY.symm),
        Submodule.finrank_orthogonal_span_singleton (n := 1) (vsub_ne_zero.2 hKne)]
  have hdir : (line[ℝ, X, Y]).direction = ℝ ∙ (Y -ᵥ X) := by
    have hle : ℝ ∙ (Y -ᵥ X) ≤ (line[ℝ, X, Y]).direction := by
      rw [Submodule.span_singleton_le_iff_mem]
      exact AffineSubspace.vsub_mem_direction (right_mem_affineSpan_pair ℝ X Y)
        (left_mem_affineSpan_pair ℝ X Y)
    symm
    apply Submodule.eq_of_le_of_finrank_eq hle
    rw [finrank_span_singleton (vsub_ne_zero.2 hXY.symm), direction_affineSpan,
      vectorSpan_pair, finrank_span_singleton (vsub_ne_zero.2 hXY)]
  set s := ⟪Q -ᵥ midpoint ℝ X Y, K -ᵥ midpoint ℝ X Y⟫ /
    ⟪K -ᵥ midpoint ℝ X Y, K -ᵥ midpoint ℝ X Y⟫ with hsdef
  have hs : 0 < s := div_pos hQ (real_inner_self_pos.2 (vsub_ne_zero.2 hKne))
  set p₂ := (-(s • (K -ᵥ midpoint ℝ X Y))) +ᵥ Q with hp₂def
  have hp₂ : p₂ ∈ line[ℝ, X, Y] := by
    have hmem : p₂ -ᵥ midpoint ℝ X Y ∈ (line[ℝ, X, Y]).direction := by
      rw [hdir, ← hspan]
      have he : p₂ -ᵥ midpoint ℝ X Y = (Q -ᵥ midpoint ℝ X Y) - s • (K -ᵥ midpoint ℝ X Y) := by
        rw [hp₂def, vadd_vsub_assoc]
        abel
      rw [he]
      apply (Submodule.mem_orthogonal_singleton_iff_inner_left).2
      rw [inner_sub_left, real_inner_smul_left]
      have hnn : ⟪K -ᵥ midpoint ℝ X Y, K -ᵥ midpoint ℝ X Y⟫ ≠ 0 :=
        fun h => (vsub_ne_zero.2 hKne) (inner_self_eq_zero.1 h)
      rw [hsdef, div_mul_cancel₀ _ hnn]
      ring
    have hmem2 := AffineSubspace.vadd_mem_of_mem_direction hmem hM_mem
    rw [vsub_vadd] at hmem2
    exact hmem2
  have hray : SameRay ℝ (K -ᵥ midpoint ℝ X Y) (Q -ᵥ p₂) := by
    have e2 : Q -ᵥ p₂ = s • (K -ᵥ midpoint ℝ X Y) := by
      have h : p₂ -ᵥ Q = -(s • (K -ᵥ midpoint ℝ X Y)) := by
        rw [hp₂def, vadd_vsub_assoc, vsub_self, add_zero]
      have h2 : -(Q -ᵥ p₂) = -(s • (K -ᵥ midpoint ℝ X Y)) := by
        rw [neg_vsub_eq_vsub_rev Q p₂]; exact h
      exact neg_injective h2
    rw [e2]
    exact SameRay.rfl.pos_smul_right hs
  refine ⟨⟨midpoint ℝ X Y, hM_mem, p₂, hp₂, hray⟩, ?_, ?_⟩
  · intro hK
    have hv : K -ᵥ midpoint ℝ X Y ∈ (line[ℝ, X, Y]).direction :=
      AffineSubspace.vsub_mem_direction hK hM_mem
    rw [hdir, ← hspan] at hv
    have h0 := (Submodule.mem_orthogonal_singleton_iff_inner_left).1 hv
    exact (vsub_ne_zero.2 hKne) (inner_self_eq_zero.1 h0)
  · intro hQm
    have hv : Q -ᵥ midpoint ℝ X Y ∈ (line[ℝ, X, Y]).direction :=
      AffineSubspace.vsub_mem_direction hQm hM_mem
    rw [hdir, ← hspan] at hv
    have h0 := (Submodule.mem_orthogonal_singleton_iff_inner_left).1 hv
    exact (ne_of_gt hQ) h0

/-- For `P` on a circle centered at `O` through `X` and `Y`, twice the inner product
`⟪P - M, O - M⟫` (with `M` the midpoint of `XY`) equals `⟪X - P, Y - P⟫`. -/
theorem inner_vsub_midpoint_vsub_center {O X Y P : Pt}
    (hX : dist O X = dist O Y) (hP : dist O P = dist O X) :
    2 * ⟪P -ᵥ midpoint ℝ X Y, O -ᵥ midpoint ℝ X Y⟫ = ⟪X -ᵥ P, Y -ᵥ P⟫ := by
  have hm : midpoint ℝ X Y -ᵥ O = (2⁻¹ : ℝ) • ((X -ᵥ O) + (Y -ᵥ O)) := by
    rw [midpoint_vsub, smul_add]
    rw [show (⅟ 2 : ℝ) = (2 : ℝ)⁻¹ from rfl]
  have h1 : P -ᵥ midpoint ℝ X Y = (P -ᵥ O) - (2⁻¹ : ℝ) • ((X -ᵥ O) + (Y -ᵥ O)) := by
    rw [← hm, vsub_sub_vsub_cancel_right]
  have h2 : O -ᵥ midpoint ℝ X Y = -((2⁻¹ : ℝ) • ((X -ᵥ O) + (Y -ᵥ O))) := by
    rw [← hm, neg_vsub_eq_vsub_rev]
  have h3 : X -ᵥ P = (X -ᵥ O) - (P -ᵥ O) := (vsub_sub_vsub_cancel_right _ _ _).symm
  have h4 : Y -ᵥ P = (Y -ᵥ O) - (P -ᵥ O) := (vsub_sub_vsub_cancel_right _ _ _).symm
  rw [h1, h2, h3, h4]
  simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, inner_neg_right,
    real_inner_comm (Y -ᵥ O) (X -ᵥ O), real_inner_comm (P -ᵥ O) (X -ᵥ O)]
  simp only [real_inner_self_eq_norm_sq]
  have hx : ‖X -ᵥ O‖ = ‖Y -ᵥ O‖ := by
    have e1 : ‖X -ᵥ O‖ = dist O X := by rw [dist_comm, dist_eq_norm_vsub]
    have e2 : ‖Y -ᵥ O‖ = dist O Y := by rw [dist_comm, dist_eq_norm_vsub]
    rw [e1, e2, hX]
  have hp : ‖P -ᵥ O‖ = ‖Y -ᵥ O‖ := by
    have e1 : ‖P -ᵥ O‖ = dist O P := by rw [dist_comm, dist_eq_norm_vsub]
    have e2 : ‖Y -ᵥ O‖ = dist O Y := by rw [dist_comm, dist_eq_norm_vsub]
    rw [e1, e2, hP, hX]
  rw [hx, hp]
  ring

/-- In an equilateral configuration (all pairwise distances equal and nonzero), each angle is
`π / 3`. -/
theorem angle_eq_pi_div_three_of_dist_eq {p₁ p₂ p₃ : Pt} {r : ℝ} (hr : r ≠ 0)
    (h₁ : dist p₁ p₂ = r) (h₂ : dist p₃ p₂ = r) (h₃ : dist p₁ p₃ = r) :
    ∠ p₁ p₂ p₃ = π / 3 := by
  have hx : ‖p₁ -ᵥ p₂‖ = r := by rw [← dist_eq_norm_vsub]; exact h₁
  have hy : ‖p₃ -ᵥ p₂‖ = r := by rw [← dist_eq_norm_vsub]; exact h₂
  have hnorm : ‖(p₁ -ᵥ p₂) - (p₃ -ᵥ p₂)‖ = r := by
    rw [vsub_sub_vsub_cancel_right, ← dist_eq_norm_vsub]; exact h₃
  have hinner : ⟪p₁ -ᵥ p₂, p₃ -ᵥ p₂⟫ = r ^ 2 / 2 := by
    have h2 := norm_sub_sq_real (p₁ -ᵥ p₂) (p₃ -ᵥ p₂)
    rw [hnorm, hx, hy] at h2
    linarith [h2]
  have hcos : Real.cos (∠ p₁ p₂ p₃) = 1 / 2 := by
    have h := InnerProductGeometry.cos_angle_mul_norm_mul_norm (p₁ -ᵥ p₂) (p₃ -ᵥ p₂)
    rw [hx, hy, hinner] at h
    have hr2 : r * r ≠ 0 := mul_ne_zero hr hr
    have e : Real.cos (InnerProductGeometry.angle (p₁ -ᵥ p₂) (p₃ -ᵥ p₂)) * (r * r) =
        (1 / 2) * (r * r) := by
      have h2 : (1 / 2) * (r * r) = r ^ 2 / 2 := by ring
      rw [h2]; exact h
    exact mul_right_cancel₀ hr2 e
  have h3 : ∠ p₁ p₂ p₃ = Real.arccos (1 / 2) := by
    rw [← hcos]
    exact (Real.arccos_cos (angle_nonneg _ _ _) (angle_le_pi _ _ _)).symm
  rw [h3, ← Real.cos_pi_div_three]
  exact Real.arccos_cos (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

/- ### The configuration -/

variable (V) (Pt)

/-- A configuration satisfying the conditions of the problem. We bundle the points and
hypotheses in a structure to avoid passing many hypotheses around. -/
structure Imo2002q2Cfg where
  (B C O A E F D J : Pt)
  hO_midpoint : O = midpoint ℝ B C
  hB_ne_C : B ≠ C
  hA_circle : dist O A = dist O B
  hE_circle : dist O E = dist O B
  hF_circle : dist O F = dist O B
  hD_circle : dist O D = dist O B
  hE_perp : E ∈ AffineSubspace.perpBisector A O
  hF_perp : F ∈ AffineSubspace.perpBisector A O
  hE_ne_F : E ≠ F
  hA_ne_O : A ≠ O
  hC_ne_O : C ≠ O
  hA_ne_B : A ≠ B
  hangle : Real.pi / 3 < ∠ A O C
  hD_arc : ∠ A O D = ∠ D O B
  hD_minor : ∠ A O D + ∠ D O B = ∠ A O B
  hD_ne_A : D ≠ A
  hD_ne_B : D ≠ B
  hJ_mem : J ∈ line[ℝ, A, C]
  hJ_par : line[ℝ, O, J] ∥ line[ℝ, A, D]
  hO_ne_J : O ≠ J
  hA_ne_D : A ≠ D

variable {V Pt}

namespace Imo2002q2Cfg

/-- The configuration has a symmetry swapping `E` and `F`. -/
def symm (cfg : Imo2002q2Cfg V Pt) : Imo2002q2Cfg V Pt where
  B := cfg.B
  C := cfg.C
  O := cfg.O
  A := cfg.A
  E := cfg.F
  F := cfg.E
  D := cfg.D
  J := cfg.J
  hO_midpoint := cfg.hO_midpoint
  hB_ne_C := cfg.hB_ne_C
  hA_circle := cfg.hA_circle
  hE_circle := cfg.hF_circle
  hF_circle := cfg.hE_circle
  hD_circle := cfg.hD_circle
  hE_perp := cfg.hF_perp
  hF_perp := cfg.hE_perp
  hE_ne_F := cfg.hE_ne_F.symm
  hA_ne_O := cfg.hA_ne_O
  hC_ne_O := cfg.hC_ne_O
  hA_ne_B := cfg.hA_ne_B
  hangle := cfg.hangle
  hD_arc := cfg.hD_arc
  hD_minor := cfg.hD_minor
  hD_ne_A := cfg.hD_ne_A
  hD_ne_B := cfg.hD_ne_B
  hJ_mem := cfg.hJ_mem
  hJ_par := cfg.hJ_par
  hO_ne_J := cfg.hO_ne_J
  hA_ne_D := cfg.hA_ne_D

variable (cfg : Imo2002q2Cfg V Pt)

theorem O_ne_B : cfg.O ≠ cfg.B := by
  intro h
  apply cfg.hB_ne_C
  have h2 : midpoint ℝ cfg.B cfg.C = cfg.B := h ▸ cfg.hO_midpoint.symm
  exact (midpoint_eq_left_iff ℝ).1 h2

theorem O_ne_C : cfg.O ≠ cfg.C := by
  intro h
  apply cfg.hB_ne_C
  have h2 : midpoint ℝ cfg.B cfg.C = cfg.C := h ▸ cfg.hO_midpoint.symm
  exact (midpoint_eq_right_iff ℝ).1 h2

theorem B_ne_O : cfg.B ≠ cfg.O := cfg.O_ne_B.symm

theorem r_pos : 0 < dist cfg.O cfg.B := dist_pos.2 cfg.O_ne_B

theorem dist_OC : dist cfg.O cfg.C = dist cfg.O cfg.B := by
  rw [cfg.hO_midpoint, dist_midpoint_right, dist_midpoint_left]

theorem A_ne_C : cfg.A ≠ cfg.C := by
  intro h
  have ha := cfg.hangle
  rw [h, angle_self_of_ne cfg.hC_ne_O] at ha
  linarith [Real.pi_pos, ha]

theorem angle_AOC_ne_zero : ∠ cfg.A cfg.O cfg.C ≠ 0 :=
  ne_of_gt (lt_trans (by linarith [Real.pi_pos]) cfg.hangle)

theorem B_vsub_O : cfg.B -ᵥ cfg.O = -(cfg.C -ᵥ cfg.O) := by
  rw [cfg.hO_midpoint, left_vsub_midpoint, right_vsub_midpoint,
    ← neg_vsub_eq_vsub_rev cfg.B cfg.C, smul_neg, neg_neg]

theorem A_eq_B_of_angle_eq_pi (h : ∠ cfg.A cfg.O cfg.C = π) : cfg.A = cfg.B := by
  rw [angle_eq_pi_iff_sbtw] at h
  obtain ⟨r, hrpos, hrv⟩ := h.wbtw.sameRay_vsub.exists_pos_left
    (vsub_ne_zero.2 cfg.hA_ne_O.symm) (vsub_ne_zero.2 cfg.hC_ne_O)
  have hnorm : ‖r • (cfg.O -ᵥ cfg.A)‖ = ‖cfg.C -ᵥ cfg.O‖ := congrArg norm hrv
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hrpos] at hnorm
  have hAn : ‖cfg.O -ᵥ cfg.A‖ = dist cfg.O cfg.B := by
    rw [← dist_eq_norm_vsub]; exact cfg.hA_circle
  have hCn : ‖cfg.C -ᵥ cfg.O‖ = dist cfg.O cfg.B := by
    rw [← dist_eq_norm_vsub, dist_comm cfg.C cfg.O]; exact cfg.dist_OC
  rw [hAn, hCn] at hnorm
  have hr1 : r = 1 :=
    mul_right_cancel₀ (ne_of_gt cfg.r_pos) (by rw [hnorm]; ring)
  rw [hr1, one_smul] at hrv
  -- `O -ᵥ A = C -ᵥ O`, so `A -ᵥ O = B -ᵥ O`.
  have h2 : cfg.A -ᵥ cfg.O = cfg.B -ᵥ cfg.O := by
    rw [cfg.B_vsub_O, ← neg_vsub_eq_vsub_rev cfg.O cfg.A, hrv]
  have h3 := congrArg (· +ᵥ cfg.O) h2
  rwa [vsub_vadd, vsub_vadd] at h3

theorem angle_AOC_ne_pi : ∠ cfg.A cfg.O cfg.C ≠ π :=
  fun h => cfg.hA_ne_B (A_eq_B_of_angle_eq_pi cfg h)

theorem angle_AOC_lt_pi : ∠ cfg.A cfg.O cfg.C < π :=
  lt_of_le_of_ne (angle_le_pi _ _ _) cfg.angle_AOC_ne_pi

theorem angle_AOC_pos : 0 < ∠ cfg.A cfg.O cfg.C :=
  lt_trans (by linarith [Real.pi_pos]) cfg.hangle

theorem not_collinear_AOC : ¬Collinear ℝ ({cfg.A, cfg.O, cfg.C} : Set Pt) := by
  intro hc
  rw [collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi] at hc
  rcases hc with h | h | h | h
  · exact cfg.hA_ne_O h
  · exact cfg.hC_ne_O h
  · exact angle_AOC_ne_zero cfg h
  · exact angle_AOC_ne_pi cfg h

theorem affineIndependent_AOC : AffineIndependent ℝ ![cfg.A, cfg.O, cfg.C] :=
  affineIndependent_iff_not_collinear_set.2 cfg.not_collinear_AOC

theorem O_ne_A : cfg.O ≠ cfg.A := cfg.hA_ne_O.symm

theorem O_ne_E : cfg.O ≠ cfg.E := by
  intro h
  have hc := cfg.hE_circle
  exact (ne_of_gt cfg.r_pos) (by rw [← hc, h, dist_self])

theorem O_ne_F : cfg.O ≠ cfg.F := by
  intro h
  have hc := cfg.hF_circle
  exact (ne_of_gt cfg.r_pos) (by rw [← hc, h, dist_self])

theorem O_ne_D : cfg.O ≠ cfg.D := by
  intro h
  have hc := cfg.hD_circle
  exact (ne_of_gt cfg.r_pos) (by rw [← hc, h, dist_self])

theorem E_ne_O : cfg.E ≠ cfg.O := cfg.O_ne_E.symm

theorem F_ne_O : cfg.F ≠ cfg.O := cfg.O_ne_F.symm

theorem D_ne_O : cfg.D ≠ cfg.O := cfg.O_ne_D.symm

/-- The circle of the problem. -/
def circle : Sphere Pt := ⟨cfg.O, dist cfg.O cfg.B⟩

theorem A_mem_circle : cfg.A ∈ cfg.circle :=
  mem_sphere.2 (by rw [dist_comm]; exact cfg.hA_circle)

theorem B_mem_circle : cfg.B ∈ cfg.circle :=
  mem_sphere.2 (dist_comm _ _)

theorem C_mem_circle : cfg.C ∈ cfg.circle :=
  mem_sphere.2 (by rw [dist_comm]; exact cfg.dist_OC)

theorem E_mem_circle : cfg.E ∈ cfg.circle :=
  mem_sphere.2 (by rw [dist_comm]; exact cfg.hE_circle)

theorem F_mem_circle : cfg.F ∈ cfg.circle :=
  mem_sphere.2 (by rw [dist_comm]; exact cfg.hF_circle)

theorem D_mem_circle : cfg.D ∈ cfg.circle :=
  mem_sphere.2 (by rw [dist_comm]; exact cfg.hD_circle)

theorem dist_EA : dist cfg.E cfg.A = dist cfg.O cfg.B := by
  have h := (AffineSubspace.mem_perpBisector_iff_dist_eq).1 cfg.hE_perp
  rw [h, dist_comm cfg.E cfg.O]; exact cfg.hE_circle

theorem dist_FA : dist cfg.F cfg.A = dist cfg.O cfg.B := by
  have h := (AffineSubspace.mem_perpBisector_iff_dist_eq).1 cfg.hF_perp
  rw [h, dist_comm cfg.F cfg.O]; exact cfg.hF_circle

theorem angle_AOE : ∠ cfg.A cfg.O cfg.E = π / 3 :=
  angle_eq_pi_div_three_of_dist_eq (ne_of_gt cfg.r_pos)
    (by rw [dist_comm]; exact cfg.hA_circle) (by rw [dist_comm]; exact cfg.hE_circle)
    (by rw [dist_comm]; exact cfg.dist_EA)

theorem angle_AOF : ∠ cfg.A cfg.O cfg.F = π / 3 :=
  angle_eq_pi_div_three_of_dist_eq (ne_of_gt cfg.r_pos)
    (by rw [dist_comm]; exact cfg.hA_circle) (by rw [dist_comm]; exact cfg.hF_circle)
    (by rw [dist_comm]; exact cfg.dist_FA)

theorem angle_EOA : ∠ cfg.E cfg.O cfg.A = π / 3 := by
  rw [angle_comm]; exact cfg.angle_AOE

theorem angle_FOA : ∠ cfg.F cfg.O cfg.A = π / 3 := by
  rw [angle_comm]; exact cfg.angle_AOF

/- ### Oriented angles: the sign `σ` and the equilateral triangles `AEO`, `AFO` -/

section Oriented

variable [Module.Oriented ℝ V (Fin 2)] [Fact (finrank ℝ V = 2)]

/-- The sign of the configuration: `σ = 1` if `A` is counterclockwise from `C` around `O`. -/
noncomputable def σ : SignType := (∡ cfg.C cfg.O cfg.A).sign

theorem oangle_COA_ne : ∡ cfg.C cfg.O cfg.A ≠ 0 ∧ ∡ cfg.C cfg.O cfg.A ≠ π := by
  apply oangle_ne_zero_and_ne_pi_iff_affineIndependent.2
  apply affineIndependent_iff_not_collinear_set.2
  rw [show ({cfg.C, cfg.O, cfg.A} : Set Pt) = {cfg.A, cfg.O, cfg.C} from by
    ext x; simp; tauto]
  exact cfg.not_collinear_AOC

theorem σ_ne_zero : cfg.σ ≠ 0 := Real.Angle.sign_ne_zero_iff.2 cfg.oangle_COA_ne

theorem σ_eq : cfg.σ = 1 ∨ cfg.σ = -1 := by
  have h0 := cfg.σ_ne_zero
  have h : ∀ s : SignType, s ≠ 0 → s = 1 ∨ s = -1 := by
    intro s hs
    rcases s with _ | _ | _
    · exact (hs rfl).elim
    · exact Or.inr rfl
    · exact Or.inl rfl
  exact h _ h0

theorem σ_sq : (cfg.σ : ℝ) ^ 2 = 1 := by
  rcases cfg.σ_eq with h | h <;> simp [h]

theorem σ_cast_ne_zero : (cfg.σ : ℝ) ≠ 0 := by
  rcases cfg.σ_eq with h | h <;> simp [h]

theorem oangle_COA : ∡ cfg.C cfg.O cfg.A = ((cfg.σ : ℝ) * ∠ cfg.A cfg.O cfg.C : ℝ) :=
  Orientation.oangle_eq_coe_sign_mul (o := positiveOrientation)
    (vsub_ne_zero.2 cfg.hC_ne_O) (vsub_ne_zero.2 cfg.hA_ne_O)
    cfg.angle_AOC_pos cfg.angle_AOC_lt_pi (InnerProductGeometry.angle_comm _ _) rfl

theorem oangle_AOC : ∡ cfg.A cfg.O cfg.C = (-((cfg.σ : ℝ) * ∠ cfg.A cfg.O cfg.C) : ℝ) := by
  rw [oangle_rev cfg.C cfg.O cfg.A, cfg.oangle_COA, ← Real.Angle.coe_neg]

theorem oangle_AOE_ne : ∡ cfg.A cfg.O cfg.E ≠ 0 ∧ ∡ cfg.A cfg.O cfg.E ≠ π := by
  constructor
  · intro h
    rw [oangle_eq_zero_iff_angle_eq_zero cfg.hA_ne_O cfg.E_ne_O] at h
    have ha := angle_AOE cfg
    rw [h] at ha
    linarith [Real.pi_pos, ha]
  · intro h
    rw [oangle_eq_pi_iff_angle_eq_pi] at h
    have ha := angle_AOE cfg
    rw [h] at ha
    linarith [Real.pi_pos, ha]

theorem oangle_AOF_ne : ∡ cfg.A cfg.O cfg.F ≠ 0 ∧ ∡ cfg.A cfg.O cfg.F ≠ π := by
  constructor
  · intro h
    rw [oangle_eq_zero_iff_angle_eq_zero cfg.hA_ne_O cfg.F_ne_O] at h
    have ha := angle_AOF cfg
    rw [h] at ha
    linarith [Real.pi_pos, ha]
  · intro h
    rw [oangle_eq_pi_iff_angle_eq_pi] at h
    have ha := angle_AOF cfg
    rw [h] at ha
    linarith [Real.pi_pos, ha]

theorem sign_AOE_eq_neg_sign_AOF :
    (∡ cfg.A cfg.O cfg.E).sign = -(∡ cfg.A cfg.O cfg.F).sign := by
  have hne : (∡ cfg.A cfg.O cfg.E).sign ≠ (∡ cfg.A cfg.O cfg.F).sign := by
    intro h
    have heq : ∡ cfg.A cfg.O cfg.E = ∡ cfg.A cfg.O cfg.F :=
      oangle_eq_of_angle_eq_of_sign_eq (by rw [cfg.angle_AOE, cfg.angle_AOF]) h
    have h0 : ∡ cfg.E cfg.O cfg.F = 0 := by
      have hadd := oangle_add cfg.E_ne_O cfg.hA_ne_O cfg.F_ne_O
      rw [oangle_rev cfg.A cfg.O cfg.E, heq, neg_add_cancel] at hadd
      exact hadd.symm
    have hsr : SameRay ℝ (cfg.E -ᵥ cfg.O) (cfg.F -ᵥ cfg.O) :=
      (Orientation.oangle_eq_zero_iff_sameRay (o := positiveOrientation)).1 h0
    obtain ⟨r, hrpos, hrv⟩ := hsr.exists_pos_left (vsub_ne_zero.2 cfg.E_ne_O)
      (vsub_ne_zero.2 cfg.F_ne_O)
    have hnorm : ‖r • (cfg.E -ᵥ cfg.O)‖ = ‖cfg.F -ᵥ cfg.O‖ := congrArg norm hrv
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hrpos] at hnorm
    have hEn : ‖cfg.E -ᵥ cfg.O‖ = dist cfg.O cfg.B := by
      rw [← dist_eq_norm_vsub, dist_comm cfg.E cfg.O]; exact cfg.hE_circle
    have hFn : ‖cfg.F -ᵥ cfg.O‖ = dist cfg.O cfg.B := by
      rw [← dist_eq_norm_vsub, dist_comm cfg.F cfg.O]; exact cfg.hF_circle
    rw [hEn, hFn] at hnorm
    have hr1 : r = 1 :=
      mul_right_cancel₀ (ne_of_gt cfg.r_pos) (by rw [hnorm]; ring)
    rw [hr1, one_smul] at hrv
    exact cfg.hE_ne_F (by
      have h3 := congrArg (· +ᵥ cfg.O) hrv
      rwa [vsub_vadd, vsub_vadd] at h3)
  have hs0E : (∡ cfg.A cfg.O cfg.E).sign ≠ 0 :=
    Real.Angle.sign_ne_zero_iff.2 cfg.oangle_AOE_ne
  have hs0F : (∡ cfg.A cfg.O cfg.F).sign ≠ 0 :=
    Real.Angle.sign_ne_zero_iff.2 cfg.oangle_AOF_ne
  have h : ∀ s₁ s₂ : SignType, s₁ ≠ 0 → s₂ ≠ 0 → s₁ ≠ s₂ → s₁ = -s₂ := by
    intro s₁ s₂ h1 h2 h12
    rcases s₁ with _ | _ | _ <;> rcases s₂ with _ | _ | _ <;> simp_all
  exact h _ _ hs0E hs0F hne

theorem σ_abs : |(cfg.σ : ℝ)| = 1 := by
  rcases cfg.σ_eq with hσ | hσ <;> simp [hσ]

theorem σ_mul_mem_Ioc {x : ℝ} (hx0 : 0 < x) (hxπ : x < π) :
    -π < (cfg.σ : ℝ) * x ∧ (cfg.σ : ℝ) * x ≤ π := by
  rcases cfg.σ_eq with hσ | hσ
  · rw [hσ, SignType.coe_one, one_mul]
    exact ⟨by linarith, by linarith⟩
  · rw [hσ, SignType.coe_neg, SignType.coe_one, neg_mul, one_mul]
    exact ⟨by linarith, by linarith⟩

theorem σ_mul_toReal {x : ℝ} (hx0 : 0 < x) (hxπ : x < π) :
    (((cfg.σ : ℝ) * x : ℝ) : Real.Angle).toReal = (cfg.σ : ℝ) * x :=
  Real.Angle.toReal_coe_eq_self_iff.2 (cfg.σ_mul_mem_Ioc hx0 hxπ)

theorem sign_coe_σ_mul {x : ℝ} (hx0 : 0 < x) (hxπ : x < π) :
    (((cfg.σ : ℝ) * x : ℝ) : Real.Angle).sign = cfg.σ := by
  rw [Real.Angle.sign, Real.Angle.sin_coe]
  have hs : Real.sin ((cfg.σ : ℝ) * x) = (cfg.σ : ℝ) * Real.sin x := by
    rcases cfg.σ_eq with hσ | hσ <;> simp [hσ]
  rw [hs]
  rcases cfg.σ_eq with hσ | hσ
  · rw [hσ, SignType.coe_one, one_mul]
    exact sign_pos (Real.sin_pos_of_mem_Ioo ⟨hx0, hxπ⟩)
  · rw [hσ, SignType.coe_neg, SignType.coe_one, neg_mul, one_mul]
    exact sign_neg (neg_lt_zero.2 (Real.sin_pos_of_mem_Ioo ⟨hx0, hxπ⟩))

theorem two_zsmul_coe_σ_mul (x : ℝ) :
    (2 : ℤ) • (((cfg.σ : ℝ) * x : ℝ) : Real.Angle) = ((cfg.σ : ℝ) * (2 * x) : ℝ) := by
  rw [two_zsmul, ← Real.Angle.coe_add]
  congr 1
  ring

/-- If twice an oriented angle is `σ • γ` and its sign is `σ`, the angle is `σ • γ / 2`. -/
theorem oangle_eq_half_of_two_zsmul_eq {θ : Real.Angle} {γ : ℝ}
    (h2 : (2 : ℤ) • θ = ((cfg.σ : ℝ) * γ : ℝ)) (hs : θ.sign = cfg.σ)
    (hγ0 : 0 < γ) (hγπ : γ < 2 * π) :
    θ = ((cfg.σ : ℝ) * (γ / 2) : ℝ) := by
  have hγ20 : 0 < γ / 2 := by linarith
  have hγ2π : γ / 2 < π := by linarith
  have hsol : (((cfg.σ : ℝ) * (γ / 2) : ℝ) : Real.Angle).sign = cfg.σ :=
    cfg.sign_coe_σ_mul hγ20 hγ2π
  have hne0 : (((cfg.σ : ℝ) * (γ / 2) : ℝ) : Real.Angle) ≠ 0 := by
    intro h
    have htr := cfg.σ_mul_toReal hγ20 hγ2π
    rw [h, Real.Angle.toReal_zero] at htr
    have hγ : (cfg.σ : ℝ) * (γ / 2) = 0 := htr.symm
    have hγ2 : γ / 2 = 0 := by
      rcases (mul_eq_zero.1 hγ) with h1 | h1
      · exact absurd h1 cfg.σ_cast_ne_zero
      · exact h1
    linarith
  have hneπ : (((cfg.σ : ℝ) * (γ / 2) : ℝ) : Real.Angle) ≠ π := by
    intro h
    have htr := cfg.σ_mul_toReal hγ20 hγ2π
    rw [h, Real.Angle.toReal_pi] at htr
    have habs : |(cfg.σ : ℝ) * (γ / 2)| = γ / 2 := by
      rw [abs_mul, cfg.σ_abs, one_mul, abs_of_pos hγ20]
    have h4 : |(cfg.σ : ℝ) * (γ / 2)| = |π| := by rw [← htr]
    rw [habs, abs_of_nonneg Real.pi_pos.le] at h4
    linarith [h4, hγ2π]
  apply Real.Angle.eq_of_two_zsmul_eq_of_sign_eq _ (by rw [hsol, hs]) hne0 hneπ
  rw [cfg.two_zsmul_coe_σ_mul (γ / 2),
    show (cfg.σ : ℝ) * (2 * (γ / 2)) = (cfg.σ : ℝ) * γ from by ring]
  exact h2

/- ### The point `D` and the direction of `OD` -/

omit [Module.Oriented ℝ V (Fin 2)] [Fact (finrank ℝ V = 2)] in
theorem angle_AOB : ∠ cfg.A cfg.O cfg.B = π - ∠ cfg.A cfg.O cfg.C := by
  have hnA : ‖cfg.A -ᵥ cfg.O‖ = dist cfg.O cfg.B := by
    rw [← dist_eq_norm_vsub, dist_comm cfg.A cfg.O]; exact cfg.hA_circle
  have hnC : ‖cfg.C -ᵥ cfg.O‖ = dist cfg.O cfg.B := by
    rw [← dist_eq_norm_vsub, dist_comm cfg.C cfg.O]; exact cfg.dist_OC
  have hinner : ⟪cfg.A -ᵥ cfg.O, cfg.B -ᵥ cfg.O⟫ =
      (-Real.cos (∠ cfg.A cfg.O cfg.C)) * (dist cfg.O cfg.B * dist cfg.O cfg.B) := by
    rw [cfg.B_vsub_O, ← neg_one_smul ℝ, real_inner_smul_right]
    have hcosAC : ⟪cfg.A -ᵥ cfg.O, cfg.C -ᵥ cfg.O⟫ =
        Real.cos (∠ cfg.A cfg.O cfg.C) * (dist cfg.O cfg.B * dist cfg.O cfg.B) := by
      have h2 := InnerProductGeometry.cos_angle_mul_norm_mul_norm (cfg.A -ᵥ cfg.O) (cfg.C -ᵥ cfg.O)
      rw [hnA, hnC] at h2
      exact h2.symm
    rw [hcosAC]
    ring
  have hcos : Real.cos (∠ cfg.A cfg.O cfg.B) = Real.cos (π - ∠ cfg.A cfg.O cfg.C) := by
    rw [Real.cos_pi_sub]
    have h := InnerProductGeometry.cos_angle_mul_norm_mul_norm (cfg.A -ᵥ cfg.O) (cfg.B -ᵥ cfg.O)
    have hnB : ‖cfg.B -ᵥ cfg.O‖ = dist cfg.O cfg.B := by
      rw [← dist_eq_norm_vsub, dist_comm cfg.B cfg.O]
    rw [hnA, hnB, hinner] at h
    have hr2 : dist cfg.O cfg.B * dist cfg.O cfg.B ≠ 0 :=
      mul_ne_zero (ne_of_gt cfg.r_pos) (ne_of_gt cfg.r_pos)
    exact mul_right_cancel₀ hr2 h
  exact Real.strictAntiOn_cos.injOn ⟨angle_nonneg _ _ _, angle_le_pi _ _ _⟩
    ⟨by linarith [cfg.angle_AOC_pos, cfg.angle_AOC_lt_pi, Real.pi_pos],
     by linarith [cfg.angle_AOC_pos, cfg.angle_AOC_lt_pi, Real.pi_pos]⟩ hcos

theorem oangle_COB : ∡ cfg.C cfg.O cfg.B = π := by
  have h : (positiveOrientation.oangle (cfg.C -ᵥ cfg.O) (cfg.B -ᵥ cfg.O)) = π := by
    rw [cfg.B_vsub_O,
      Orientation.oangle_neg_right (o := positiveOrientation)
        (vsub_ne_zero.2 cfg.hC_ne_O) (vsub_ne_zero.2 cfg.hC_ne_O),
      Orientation.oangle_self (o := positiveOrientation), zero_add]
  exact h

theorem oangle_AOB : ∡ cfg.A cfg.O cfg.B = ((cfg.σ : ℝ) * (π - ∠ cfg.A cfg.O cfg.C) : ℝ) := by
  have hsign : (∡ cfg.A cfg.O cfg.B).sign = cfg.σ := by
    have h := oangle_add cfg.hA_ne_O cfg.hC_ne_O cfg.B_ne_O
    rw [← h, cfg.oangle_COB, Real.Angle.sign_add_pi, oangle_rev cfg.C cfg.O cfg.A,
      Real.Angle.sign_neg, neg_neg, Imo2002q2Cfg.σ]
  exact Orientation.oangle_eq_coe_sign_mul (o := positiveOrientation)
    (vsub_ne_zero.2 cfg.hA_ne_O) (vsub_ne_zero.2 cfg.B_ne_O)
    (by linarith [cfg.angle_AOC_lt_pi])
    (by linarith [cfg.angle_AOC_pos])
    (angle_AOB cfg) hsign

omit [Module.Oriented ℝ V (Fin 2)] [Fact (finrank ℝ V = 2)] in
theorem angle_AOD : ∠ cfg.A cfg.O cfg.D = (π - ∠ cfg.A cfg.O cfg.C) / 2 := by
  have h1 := cfg.hD_arc
  have h2 := cfg.hD_minor
  have h3 := angle_AOB cfg
  linarith [h1, h2, h3]

omit [Module.Oriented ℝ V (Fin 2)] [Fact (finrank ℝ V = 2)] in
theorem angle_DOB : ∠ cfg.D cfg.O cfg.B = (π - ∠ cfg.A cfg.O cfg.C) / 2 := by
  have h1 := cfg.hD_arc
  have h2 := cfg.hD_minor
  have h3 := angle_AOB cfg
  linarith [h1, h2, h3]

theorem oangle_AOD : ∡ cfg.A cfg.O cfg.D = ((cfg.σ : ℝ) * ((π - ∠ cfg.A cfg.O cfg.C) / 2) : ℝ) := by
  have hsign : (∡ cfg.A cfg.O cfg.D).sign = cfg.σ := by
    by_contra hcon
    have hne : (∡ cfg.A cfg.O cfg.D).sign ≠ 0 := by
      apply Real.Angle.sign_ne_zero_iff.2
      constructor
      · intro h
        rw [oangle_eq_zero_iff_angle_eq_zero cfg.hA_ne_O cfg.D_ne_O] at h
        have ha := angle_AOD cfg
        rw [h] at ha
        have hθ : ∠ cfg.A cfg.O cfg.C = π := by linarith [ha, Real.pi_pos]
        exact cfg.angle_AOC_ne_pi hθ
      · intro h
        rw [oangle_eq_pi_iff_angle_eq_pi] at h
        have ha := angle_AOD cfg
        rw [h] at ha
        have hθ0 := cfg.angle_AOC_pos
        linarith [ha, Real.pi_pos]
    have hsign2 : (∡ cfg.A cfg.O cfg.D).sign = -cfg.σ := by
      have h : ∀ s t : SignType, s ≠ 0 → t ≠ 0 → s ≠ t → s = -t := by
        intro s t h1 h2 h12
        rcases s with _ | _ | _ <;> rcases t with _ | _ | _ <;> simp_all
      exact h _ _ hne cfg.σ_ne_zero hcon
    have hval : ∡ cfg.A cfg.O cfg.D = (-((cfg.σ : ℝ) * ((π - ∠ cfg.A cfg.O cfg.C) / 2)) : ℝ) := by
      have h2 := Orientation.oangle_eq_coe_sign_mul (o := positiveOrientation)
        (vsub_ne_zero.2 cfg.hA_ne_O) (vsub_ne_zero.2 cfg.D_ne_O)
        (by have hθπ := cfg.angle_AOC_lt_pi; linarith [Real.pi_pos])
        (by have hθ0 := cfg.angle_AOC_pos; linarith [Real.pi_pos])
        (angle_AOD cfg) hsign2
      rw [SignType.coe_neg, neg_mul] at h2
      exact h2
    have hDOB : ∡ cfg.D cfg.O cfg.B =
        ((cfg.σ : ℝ) * (3 * (π - ∠ cfg.A cfg.O cfg.C) / 2) : ℝ) := by
      have h := oangle_add cfg.D_ne_O cfg.hA_ne_O cfg.B_ne_O
      rw [oangle_rev cfg.A cfg.O cfg.D, hval, cfg.oangle_AOB] at h
      rw [← h, ← Real.Angle.coe_neg, ← Real.Angle.coe_add]
      congr 1
      ring
    have hmag : ∠ cfg.D cfg.O cfg.B = 3 * (π - ∠ cfg.A cfg.O cfg.C) / 2 := by
      have h1 : ∠ cfg.D cfg.O cfg.B = |(∡ cfg.D cfg.O cfg.B).toReal| :=
        Orientation.angle_eq_abs_oangle_toReal (o := positiveOrientation)
          (vsub_ne_zero.2 cfg.D_ne_O) (vsub_ne_zero.2 cfg.B_ne_O)
      have h3π : 3 * (π - ∠ cfg.A cfg.O cfg.C) / 2 < π := by
        have hθ0 := cfg.angle_AOC_pos
        have hθπ := cfg.angle_AOC_lt_pi
        linarith [Real.pi_pos, cfg.hangle]
      have h3 : (0:ℝ) < 3 * (π - ∠ cfg.A cfg.O cfg.C) / 2 := by
        have hθπ := cfg.angle_AOC_lt_pi
        linarith [Real.pi_pos]
      rw [h1, hDOB, cfg.σ_mul_toReal h3 h3π, abs_mul, cfg.σ_abs, one_mul,
        abs_of_pos h3]
    have hbad := angle_DOB cfg
    rw [hmag] at hbad
    have hθ : ∠ cfg.A cfg.O cfg.C = π := by linarith [hbad]
    exact cfg.angle_AOC_ne_pi hθ
  exact Orientation.oangle_eq_coe_sign_mul (o := positiveOrientation)
    (vsub_ne_zero.2 cfg.hA_ne_O) (vsub_ne_zero.2 cfg.D_ne_O)
    (by have hθπ := cfg.angle_AOC_lt_pi; linarith [Real.pi_pos])
    (by have hθ0 := cfg.angle_AOC_pos; linarith [Real.pi_pos])
    (angle_AOD cfg) hsign

theorem oangle_DOB : ∡ cfg.D cfg.O cfg.B = ((cfg.σ : ℝ) * ((π - ∠ cfg.A cfg.O cfg.C) / 2) : ℝ) := by
  have h := oangle_add cfg.D_ne_O cfg.hA_ne_O cfg.B_ne_O
  rw [oangle_rev cfg.A cfg.O cfg.D, cfg.oangle_AOD, cfg.oangle_AOB] at h
  rw [← h, ← Real.Angle.coe_neg, ← Real.Angle.coe_add]
  congr 1
  ring

/- ### The inscribed angle `∡ A C B` and the direction of `OD` -/

theorem two_zsmul_oangle_ACB : (2 : ℤ) • ∡ cfg.A cfg.C cfg.B = ∡ cfg.A cfg.O cfg.B := by
  have h := Sphere.oangle_center_eq_two_zsmul_oangle cfg.A_mem_circle cfg.C_mem_circle
    cfg.B_mem_circle cfg.A_ne_C.symm cfg.hB_ne_C.symm
  exact h.symm

omit [Module.Oriented ℝ V (Fin 2)] in
theorem sSameSide_O_C_AB : line[ℝ, cfg.A, cfg.B].SSameSide cfg.O cfg.C := by
  refine sSameSide_center_of_inner_pos cfg.hA_circle cfg.hA_ne_B ?_ ?_
  · intro h
    have hsb : Sbtw ℝ cfg.A cfg.O cfg.B := h ▸ sbtw_midpoint_of_ne ℝ cfg.hA_ne_B
    have hpi : ∠ cfg.A cfg.O cfg.B = π := hsb.angle₁₂₃_eq_pi
    have hval := angle_AOB cfg
    rw [hpi] at hval
    have hθ : ∠ cfg.A cfg.O cfg.C = 0 := by linarith [hval]
    exact cfg.angle_AOC_ne_zero hθ
  · have hid := inner_vsub_midpoint_vsub_center (O := cfg.O) (X := cfg.A) (Y := cfg.B) (P := cfg.C)
      cfg.hA_circle (by rw [cfg.dist_OC]; exact cfg.hA_circle.symm)
    have hinner : ⟪cfg.A -ᵥ cfg.C, cfg.B -ᵥ cfg.C⟫ =
        2 * dist cfg.O cfg.B ^ 2 * (1 - Real.cos (∠ cfg.A cfg.O cfg.C)) := by
      have e1 : cfg.A -ᵥ cfg.C = (cfg.A -ᵥ cfg.O) - (cfg.C -ᵥ cfg.O) :=
        (vsub_sub_vsub_cancel_right _ _ _).symm
      have e2 : cfg.B -ᵥ cfg.C = -(2 : ℝ) • (cfg.C -ᵥ cfg.O) := by
        have h1 : cfg.B -ᵥ cfg.C = (cfg.B -ᵥ cfg.O) - (cfg.C -ᵥ cfg.O) :=
          (vsub_sub_vsub_cancel_right _ _ _).symm
        rw [h1, cfg.B_vsub_O]
        module
      have hcos : ⟪cfg.A -ᵥ cfg.O, cfg.C -ᵥ cfg.O⟫ =
          Real.cos (∠ cfg.A cfg.O cfg.C) * (dist cfg.O cfg.B * dist cfg.O cfg.B) := by
        have h := InnerProductGeometry.cos_angle_mul_norm_mul_norm (cfg.A -ᵥ cfg.O) (cfg.C -ᵥ cfg.O)
        have hnA : ‖cfg.A -ᵥ cfg.O‖ = dist cfg.O cfg.B := by
          rw [← dist_eq_norm_vsub, dist_comm cfg.A cfg.O]; exact cfg.hA_circle
        have hnC : ‖cfg.C -ᵥ cfg.O‖ = dist cfg.O cfg.B := by
          rw [← dist_eq_norm_vsub, dist_comm cfg.C cfg.O]; exact cfg.dist_OC
        rw [hnA, hnC] at h
        exact h.symm
      rw [e1, e2, inner_sub_left, real_inner_smul_right, hcos, real_inner_smul_right,
        real_inner_self_eq_norm_sq]
      have hnC : ‖cfg.C -ᵥ cfg.O‖ = dist cfg.O cfg.B := by
        rw [← dist_eq_norm_vsub, dist_comm cfg.C cfg.O]; exact cfg.dist_OC
      rw [hnC]
      ring
    have hpos : 0 < ⟪cfg.A -ᵥ cfg.C, cfg.B -ᵥ cfg.C⟫ := by
      rw [hinner]
      have hcos1 : Real.cos (∠ cfg.A cfg.O cfg.C) < 1 := by
        have hle := Real.cos_le_one (∠ cfg.A cfg.O cfg.C)
        rcases hle.lt_or_eq with h | h
        · exact h
        · exfalso
          have h0 : ∠ cfg.A cfg.O cfg.C = 0 :=
            Real.strictAntiOn_cos.injOn ⟨angle_nonneg _ _ _, angle_le_pi _ _ _⟩
              ⟨le_refl 0, Real.pi_pos.le⟩ (by rw [h, Real.cos_zero])
          exact cfg.angle_AOC_ne_zero h0
      nlinarith [cfg.r_pos, hcos1, sq_pos_of_ne_zero (ne_of_gt cfg.r_pos)]
    rw [← hid] at hpos
    linarith [hpos]

theorem sign_ACB : (∡ cfg.A cfg.C cfg.B).sign = cfg.σ := by
  have hsign := cfg.sSameSide_O_C_AB.oangle_sign_eq (left_mem_affineSpan_pair ℝ cfg.A cfg.B)
    (right_mem_affineSpan_pair ℝ cfg.A cfg.B)
  rw [hsign, cfg.oangle_AOB]
  exact cfg.sign_coe_σ_mul (by linarith [cfg.angle_AOC_lt_pi])
    (by linarith [cfg.angle_AOC_pos, Real.pi_pos])

theorem oangle_ACB : ∡ cfg.A cfg.C cfg.B = ((cfg.σ : ℝ) * ((π - ∠ cfg.A cfg.O cfg.C) / 2) : ℝ) := by
  apply cfg.oangle_eq_half_of_two_zsmul_eq _ cfg.sign_ACB
    (by linarith [cfg.angle_AOC_lt_pi]) (by linarith [cfg.angle_AOC_pos, Real.pi_pos])
  rw [cfg.two_zsmul_oangle_ACB, cfg.oangle_AOB]

/- ### `OD` and `CA` are parallel with the same direction -/

theorem oangle_OD_CA : (positiveOrientation.oangle (cfg.O -ᵥ cfg.D) (cfg.C -ᵥ cfg.A)) = 0 := by
  have h1 : (positiveOrientation.oangle (cfg.O -ᵥ cfg.D) (cfg.O -ᵥ cfg.B)) =
      ((cfg.σ : ℝ) * ((π - ∠ cfg.A cfg.O cfg.C) / 2) : ℝ) := by
    have e : (positiveOrientation.oangle (cfg.O -ᵥ cfg.D) (cfg.O -ᵥ cfg.B)) = ∡ cfg.D cfg.O cfg.B := by
      have hπ : (π : Real.Angle) + π = 0 := by
        rw [← Real.Angle.coe_add, show (π : ℝ) + π = 2 * π from by ring, Real.Angle.coe_two_pi]
      rw [show cfg.O -ᵥ cfg.D = -(cfg.D -ᵥ cfg.O) from (neg_vsub_eq_vsub_rev _ _).symm,
        show cfg.O -ᵥ cfg.B = -(cfg.B -ᵥ cfg.O) from (neg_vsub_eq_vsub_rev _ _).symm,
        Orientation.oangle_neg_left (o := positiveOrientation)
          (vsub_ne_zero.2 cfg.D_ne_O) (neg_ne_zero.2 (vsub_ne_zero.2 cfg.B_ne_O)),
        Orientation.oangle_neg_right (o := positiveOrientation)
          (vsub_ne_zero.2 cfg.D_ne_O) (vsub_ne_zero.2 cfg.B_ne_O),
        add_assoc, hπ, add_zero]
      rfl
    rw [e]
    exact cfg.oangle_DOB
  have h2 : (positiveOrientation.oangle (cfg.O -ᵥ cfg.B) (cfg.C -ᵥ cfg.B)) = 0 := by
    have e : cfg.O -ᵥ cfg.B = (⅟ 2 : ℝ) • (cfg.C -ᵥ cfg.B) := by
      have h1 : cfg.O -ᵥ cfg.B = cfg.C -ᵥ cfg.O := by
        rw [← neg_vsub_eq_vsub_rev, cfg.B_vsub_O, neg_neg]
      rw [h1, cfg.hO_midpoint, right_vsub_midpoint]
    rw [e]
    exact (Orientation.oangle_eq_zero_iff_sameRay (o := positiveOrientation)).2
      (SameRay.rfl.pos_smul_left (by rw [invOf_eq_inv]; norm_num))
  have h3 : (positiveOrientation.oangle (cfg.C -ᵥ cfg.B) (cfg.C -ᵥ cfg.A)) =
      (-((cfg.σ : ℝ) * ((π - ∠ cfg.A cfg.O cfg.C) / 2)) : ℝ) := by
    have hπ : (π : Real.Angle) + π = 0 := by
      rw [← Real.Angle.coe_add, show (π : ℝ) + π = 2 * π from by ring, Real.Angle.coe_two_pi]
    have e : (positiveOrientation.oangle (cfg.C -ᵥ cfg.B) (cfg.C -ᵥ cfg.A)) = ∡ cfg.B cfg.C cfg.A := by
      rw [show cfg.C -ᵥ cfg.B = -(cfg.B -ᵥ cfg.C) from (neg_vsub_eq_vsub_rev _ _).symm,
        show cfg.C -ᵥ cfg.A = -(cfg.A -ᵥ cfg.C) from (neg_vsub_eq_vsub_rev _ _).symm,
        Orientation.oangle_neg_left (o := positiveOrientation)
          (vsub_ne_zero.2 cfg.hB_ne_C) (neg_ne_zero.2 (vsub_ne_zero.2 cfg.A_ne_C)),
        Orientation.oangle_neg_right (o := positiveOrientation)
          (vsub_ne_zero.2 cfg.hB_ne_C) (vsub_ne_zero.2 cfg.A_ne_C),
        add_assoc, hπ, add_zero]
      rfl
    rw [e, oangle_rev cfg.A cfg.C cfg.B, cfg.oangle_ACB, ← Real.Angle.coe_neg]
  have hadd1 := Orientation.oangle_add (o := positiveOrientation)
    (vsub_ne_zero.2 cfg.O_ne_D) (vsub_ne_zero.2 cfg.O_ne_B) (vsub_ne_zero.2 cfg.A_ne_C.symm)
  have hadd2 := Orientation.oangle_add (o := positiveOrientation)
    (vsub_ne_zero.2 cfg.O_ne_B) (vsub_ne_zero.2 cfg.hB_ne_C.symm) (vsub_ne_zero.2 cfg.A_ne_C.symm)
  have h : (positiveOrientation.oangle (cfg.O -ᵥ cfg.D) (cfg.C -ᵥ cfg.A)) =
      ((cfg.σ : ℝ) * ((π - ∠ cfg.A cfg.O cfg.C) / 2) : ℝ) +
      (0 + (-((cfg.σ : ℝ) * ((π - ∠ cfg.A cfg.O cfg.C) / 2)) : ℝ)) := by
    rw [← hadd1, ← hadd2, h1, h2, h3]
  rw [h, zero_add, ← Real.Angle.coe_add,
    show (cfg.σ : ℝ) * ((π - ∠ cfg.A cfg.O cfg.C) / 2) +
      -((cfg.σ : ℝ) * ((π - ∠ cfg.A cfg.O cfg.C) / 2)) = 0 from by ring,
    Real.Angle.coe_zero]

theorem sameRay_OD_CA : SameRay ℝ (cfg.O -ᵥ cfg.D) (cfg.C -ᵥ cfg.A) :=
  (Orientation.oangle_eq_zero_iff_sameRay (o := positiveOrientation)).1 cfg.oangle_OD_CA

theorem exists_lambda : ∃ l : ℝ, 0 < l ∧ cfg.O -ᵥ cfg.D = l • (cfg.C -ᵥ cfg.A) := by
  obtain ⟨l, hlpos, hl⟩ := cfg.sameRay_OD_CA.symm.exists_pos_left
    (vsub_ne_zero.2 cfg.A_ne_C.symm) (vsub_ne_zero.2 cfg.O_ne_D)
  exact ⟨l, hlpos, hl.symm⟩

/- ### The chord `AC` and the parameter `λ` -/

omit [Module.Oriented ℝ V (Fin 2)] [Fact (finrank ℝ V = 2)] in
theorem dist_AC_sq :
    dist cfg.A cfg.C ^ 2 = 2 * dist cfg.O cfg.B ^ 2 * (1 - Real.cos (∠ cfg.A cfg.O cfg.C)) := by
  have e : cfg.C -ᵥ cfg.A = (cfg.C -ᵥ cfg.O) - (cfg.A -ᵥ cfg.O) :=
    (vsub_sub_vsub_cancel_right _ _ _).symm
  have h1 : dist cfg.A cfg.C = ‖cfg.C -ᵥ cfg.A‖ := by rw [dist_comm, dist_eq_norm_vsub]
  have hcos : ⟪cfg.C -ᵥ cfg.O, cfg.A -ᵥ cfg.O⟫ =
      Real.cos (∠ cfg.A cfg.O cfg.C) * (dist cfg.O cfg.B * dist cfg.O cfg.B) := by
    have h := InnerProductGeometry.cos_angle_mul_norm_mul_norm (cfg.C -ᵥ cfg.O) (cfg.A -ᵥ cfg.O)
    have hnC : ‖cfg.C -ᵥ cfg.O‖ = dist cfg.O cfg.B := by
      rw [← dist_eq_norm_vsub, dist_comm cfg.C cfg.O]; exact cfg.dist_OC
    have hnA : ‖cfg.A -ᵥ cfg.O‖ = dist cfg.O cfg.B := by
      rw [← dist_eq_norm_vsub, dist_comm cfg.A cfg.O]; exact cfg.hA_circle
    rw [hnC, hnA, InnerProductGeometry.angle_comm] at h
    exact h.symm
  rw [h1, e, norm_sub_sq_real, hcos]
  have hnC : ‖cfg.C -ᵥ cfg.O‖ = dist cfg.O cfg.B := by
    rw [← dist_eq_norm_vsub, dist_comm cfg.C cfg.O]; exact cfg.dist_OC
  have hnA : ‖cfg.A -ᵥ cfg.O‖ = dist cfg.O cfg.B := by
    rw [← dist_eq_norm_vsub, dist_comm cfg.A cfg.O]; exact cfg.hA_circle
  rw [hnC, hnA]
  ring

omit [Module.Oriented ℝ V (Fin 2)] [Fact (finrank ℝ V = 2)] in
theorem cos_AOC_lt_half : Real.cos (∠ cfg.A cfg.O cfg.C) < 1 / 2 := by
  have h := Real.strictAntiOn_cos
    (Set.mem_Icc.2 ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩)
    (Set.mem_Icc.2 ⟨cfg.angle_AOC_pos.le, cfg.angle_AOC_lt_pi.le⟩) cfg.hangle
  rw [Real.cos_pi_div_three] at h
  exact h

omit [Module.Oriented ℝ V (Fin 2)] [Fact (finrank ℝ V = 2)] in
theorem dist_AC_gt_r : dist cfg.O cfg.B < dist cfg.A cfg.C := by
  have hsq : dist cfg.O cfg.B ^ 2 < dist cfg.A cfg.C ^ 2 := by
    rw [cfg.dist_AC_sq]
    have h1 : 1 / 2 < 1 - Real.cos (∠ cfg.A cfg.O cfg.C) := by linarith [cfg.cos_AOC_lt_half]
    nlinarith [cfg.r_pos, h1, sq_pos_of_ne_zero (ne_of_gt cfg.r_pos)]
  have h2 : |dist cfg.O cfg.B| < |dist cfg.A cfg.C| := sq_lt_sq.1 hsq
  rwa [abs_of_nonneg dist_nonneg, abs_of_nonneg dist_nonneg] at h2

/-- The ratio `λ = OD / AC` in which `J` divides `AC`. -/
noncomputable def lam : ℝ := dist cfg.O cfg.B / dist cfg.A cfg.C

omit [Module.Oriented ℝ V (Fin 2)] [Fact (finrank ℝ V = 2)] in
theorem lam_pos : 0 < cfg.lam := div_pos cfg.r_pos (dist_pos.2 cfg.A_ne_C)

omit [Module.Oriented ℝ V (Fin 2)] [Fact (finrank ℝ V = 2)] in
theorem lam_lt_one : cfg.lam < 1 :=
  (div_lt_one (dist_pos.2 cfg.A_ne_C)).2 cfg.dist_AC_gt_r

theorem OD_eq_lam_smul : cfg.O -ᵥ cfg.D = cfg.lam • (cfg.C -ᵥ cfg.A) := by
  obtain ⟨l, hlpos, hl⟩ := cfg.exists_lambda
  have hnorm : ‖cfg.O -ᵥ cfg.D‖ = ‖l • (cfg.C -ᵥ cfg.A)‖ := congrArg norm hl
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hlpos] at hnorm
  have hOD : ‖cfg.O -ᵥ cfg.D‖ = dist cfg.O cfg.B := by
    rw [← dist_eq_norm_vsub]; exact cfg.hD_circle
  have hCA : ‖cfg.C -ᵥ cfg.A‖ = dist cfg.A cfg.C := by rw [dist_comm, dist_eq_norm_vsub]
  rw [hOD, hCA] at hnorm
  have hleq : l = cfg.lam := by
    rw [lam]
    exact (eq_div_iff (ne_of_gt (dist_pos.2 cfg.A_ne_C))).2 hnorm.symm
  rw [hleq] at hl
  exact hl

/- ### `J` lies strictly between `A` and `C` with `AJ = lam • AC` -/

theorem J_vsub : cfg.J -ᵥ cfg.A = cfg.lam • (cfg.C -ᵥ cfg.A) := by
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t • (cfg.C -ᵥ cfg.A) = cfg.J -ᵥ cfg.A := by
    have hJd : cfg.J -ᵥ cfg.A ∈ (line[ℝ, cfg.A, cfg.C]).direction :=
      AffineSubspace.vsub_mem_direction cfg.hJ_mem (left_mem_affineSpan_pair ℝ cfg.A cfg.C)
    rw [direction_affineSpan, vectorSpan_pair_rev] at hJd
    obtain ⟨t, ht⟩ := (Submodule.mem_span_singleton).1 hJd
    exact ⟨t, ht⟩
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u • (cfg.D -ᵥ cfg.A) = cfg.J -ᵥ cfg.O := by
    have hJd : cfg.J -ᵥ cfg.O ∈ (line[ℝ, cfg.O, cfg.J]).direction :=
      AffineSubspace.vsub_mem_direction (right_mem_affineSpan_pair ℝ cfg.O cfg.J)
        (left_mem_affineSpan_pair ℝ cfg.O cfg.J)
    have hdir := cfg.hJ_par.direction_eq
    rw [hdir, direction_affineSpan, vectorSpan_pair_rev] at hJd
    obtain ⟨u, hu⟩ := (Submodule.mem_span_singleton).1 hJd
    exact ⟨u, hu⟩
  have hli : LinearIndependent ℝ ![cfg.C -ᵥ cfg.A, cfg.A -ᵥ cfg.O] := by
    rw [LinearIndependent.pair_iff' (vsub_ne_zero.2 cfg.A_ne_C.symm)]
    intro a ha
    apply cfg.not_collinear_AOC
    have ha0 : a ≠ 0 := by
      intro h0
      rw [h0, zero_smul] at ha
      exact cfg.hA_ne_O (vsub_eq_zero_iff_eq.1 ha.symm)
    have hCm : cfg.C ∈ line[ℝ, cfg.A, cfg.O] := by
      have hd : cfg.C -ᵥ cfg.A ∈ (line[ℝ, cfg.A, cfg.O]).direction := by
        rw [direction_affineSpan, vectorSpan_pair_rev]
        have h4 : cfg.C -ᵥ cfg.A = a⁻¹ • (cfg.A -ᵥ cfg.O) := by
          rw [← ha, inv_smul_smul₀ ha0]
        rw [h4]
        have h5 : cfg.A -ᵥ cfg.O ∈ ℝ ∙ (cfg.O -ᵥ cfg.A) := by
          have h6 : -(cfg.O -ᵥ cfg.A) ∈ ℝ ∙ (cfg.O -ᵥ cfg.A) :=
            Submodule.neg_mem _ (Submodule.mem_span_singleton_self _)
          rwa [neg_vsub_eq_vsub_rev] at h6
        exact Submodule.smul_mem _ _ h5
      have h3 := AffineSubspace.vadd_mem_of_mem_direction hd (left_mem_affineSpan_pair ℝ cfg.A cfg.O)
      rw [vsub_vadd] at h3
      exact h3
    exact collinear_triple_of_mem_affineSpan_pair
      (left_mem_affineSpan_pair ℝ cfg.A cfg.O) (right_mem_affineSpan_pair ℝ cfg.A cfg.O) hCm
  have hkey : cfg.J -ᵥ cfg.O = cfg.J -ᵥ cfg.A + (cfg.A -ᵥ cfg.O) := by
    rw [← vsub_add_vsub_cancel]
  have hDA : cfg.D -ᵥ cfg.A = -(cfg.lam • (cfg.C -ᵥ cfg.A)) + -(cfg.A -ᵥ cfg.O) := by
    have h1 : cfg.D -ᵥ cfg.A = (cfg.D -ᵥ cfg.O) + (cfg.O -ᵥ cfg.A) := (vsub_add_vsub_cancel _ _ _).symm
    rw [h1, ← neg_vsub_eq_vsub_rev cfg.O cfg.D, cfg.OD_eq_lam_smul,
      ← neg_vsub_eq_vsub_rev cfg.A cfg.O]
  have hab : (t + u * cfg.lam) • (cfg.C -ᵥ cfg.A) + (1 + u) • (cfg.A -ᵥ cfg.O) = 0 := by
    have hmain : u • (cfg.D -ᵥ cfg.A) = t • (cfg.C -ᵥ cfg.A) + (cfg.A -ᵥ cfg.O) := by
      rw [hkey, ← ht] at hu
      exact hu
    rw [hDA] at hmain
    have hrw : (t + u * cfg.lam) • (cfg.C -ᵥ cfg.A) + (1 + u) • (cfg.A -ᵥ cfg.O) =
        (t • (cfg.C -ᵥ cfg.A) + (cfg.A -ᵥ cfg.O)) -
        u • (-(cfg.lam • (cfg.C -ᵥ cfg.A)) + -(cfg.A -ᵥ cfg.O)) := by
      module
    rw [hrw, ← hmain, sub_self]
  have hcoeff := (Fintype.linearIndependent_iffₛ.1 hli) ![t + u * cfg.lam, 1 + u] 0 (by
    simp [Fin.sum_univ_two]
    exact hab)
  have h1 : t + u * cfg.lam = 0 := by
    have h := hcoeff 0
    simpa using h
  have h2 : 1 + u = 0 := by
    have h := hcoeff 1
    simpa using h
  have hu1 : u = -1 := by linarith [h2]
  have htl : t = cfg.lam := by
    rw [hu1] at h1
    linarith [h1, cfg.lam_pos]
  rw [← ht, htl]

theorem sbtw_AJC : Sbtw ℝ cfg.A cfg.J cfg.C := by
  have hJ : cfg.J = AffineMap.lineMap cfg.A cfg.C cfg.lam := by
    have h1 : cfg.J -ᵥ cfg.A = cfg.lam • (cfg.C -ᵥ cfg.A) := cfg.J_vsub
    have h2 : AffineMap.lineMap cfg.A cfg.C cfg.lam -ᵥ cfg.A = cfg.lam • (cfg.C -ᵥ cfg.A) :=
      AffineMap.lineMap_vsub_left _ _ _
    rw [← h2] at h1
    have h3 := congrArg (· +ᵥ cfg.A) h1
    rwa [vsub_vadd, vsub_vadd] at h3
  rw [hJ, sbtw_lineMap_iff]
  exact ⟨cfg.A_ne_C, Set.mem_Ioo.2 ⟨cfg.lam_pos, cfg.lam_lt_one⟩⟩

theorem sbtw_CJA : Sbtw ℝ cfg.C cfg.J cfg.A := cfg.sbtw_AJC.symm

theorem dist_AJ : dist cfg.A cfg.J = dist cfg.O cfg.B := by
  have h1 : dist cfg.A cfg.J = ‖cfg.J -ᵥ cfg.A‖ := by
    rw [dist_eq_norm_vsub, ← neg_vsub_eq_vsub_rev, norm_neg]
  rw [h1, cfg.J_vsub, norm_smul, Real.norm_eq_abs, abs_of_pos cfg.lam_pos, lam]
  have hCA : ‖cfg.C -ᵥ cfg.A‖ = dist cfg.A cfg.C := by rw [dist_comm, dist_eq_norm_vsub]
  rw [hCA]
  field_simp [ne_of_gt (dist_pos.2 cfg.A_ne_C)]

omit [Module.Oriented ℝ V (Fin 2)] [Fact (finrank ℝ V = 2)] in
theorem lam_half : 1 / 2 < cfg.lam * (1 - Real.cos (∠ cfg.A cfg.O cfg.C)) := by
  have hAC : 0 < dist cfg.A cfg.C := dist_pos.2 cfg.A_ne_C
  have hc0 : 0 < 1 - Real.cos (∠ cfg.A cfg.O cfg.C) := by linarith [cfg.cos_AOC_lt_half]
  have h1 : dist cfg.A cfg.C < 2 * dist cfg.O cfg.B * (1 - Real.cos (∠ cfg.A cfg.O cfg.C)) := by
    have hsq : dist cfg.A cfg.C ^ 2 <
        (2 * dist cfg.O cfg.B * (1 - Real.cos (∠ cfg.A cfg.O cfg.C))) ^ 2 := by
      rw [cfg.dist_AC_sq]
      have hc : 1 - Real.cos (∠ cfg.A cfg.O cfg.C) > 1 / 2 := by linarith [cfg.cos_AOC_lt_half]
      nlinarith [cfg.r_pos, hc, hc0, sq_pos_of_ne_zero (ne_of_gt cfg.r_pos),
        mul_pos hc0 (show (0:ℝ) < 1 - 2 * Real.cos (∠ cfg.A cfg.O cfg.C) by
          linarith [cfg.cos_AOC_lt_half])]
    have h2 : |dist cfg.A cfg.C| < |2 * dist cfg.O cfg.B * (1 - Real.cos (∠ cfg.A cfg.O cfg.C))| :=
      sq_lt_sq.1 hsq
    rw [abs_of_nonneg dist_nonneg,
      abs_of_nonneg (mul_nonneg (mul_nonneg (by norm_num) cfg.r_pos.le) hc0.le)] at h2
    exact h2
  have h2 : (1 / 2) * dist cfg.A cfg.C < dist cfg.O cfg.B * (1 - Real.cos (∠ cfg.A cfg.O cfg.C)) := by
    linarith [h1]
  rw [lam, div_mul_eq_mul_div, lt_div_iff₀ hAC]
  linarith [h2]

theorem J_notMem_perpBisector : cfg.J ∉ AffineSubspace.perpBisector cfg.A cfg.O := by
  intro hJ
  rw [AffineSubspace.mem_perpBisector_iff_inner_eq_zero'] at hJ
  have hJM : cfg.J -ᵥ midpoint ℝ cfg.A cfg.O =
      cfg.lam • (cfg.C -ᵥ cfg.A) + (⅟ 2 : ℝ) • (cfg.A -ᵥ cfg.O) := by
    have e1 : cfg.J -ᵥ midpoint ℝ cfg.A cfg.O =
        (cfg.J -ᵥ cfg.A) + (cfg.A -ᵥ midpoint ℝ cfg.A cfg.O) :=
      (vsub_add_vsub_cancel _ _ _).symm
    rw [e1, cfg.J_vsub, left_vsub_midpoint]
  have hinner : ⟪cfg.A -ᵥ cfg.O, cfg.C -ᵥ cfg.A⟫ =
      dist cfg.O cfg.B ^ 2 * (Real.cos (∠ cfg.A cfg.O cfg.C) - 1) := by
    have e : cfg.C -ᵥ cfg.A = (cfg.C -ᵥ cfg.O) - (cfg.A -ᵥ cfg.O) :=
      (vsub_sub_vsub_cancel_right _ _ _).symm
    have hcos : ⟪cfg.A -ᵥ cfg.O, cfg.C -ᵥ cfg.O⟫ =
        Real.cos (∠ cfg.A cfg.O cfg.C) * (dist cfg.O cfg.B * dist cfg.O cfg.B) := by
      have h := InnerProductGeometry.cos_angle_mul_norm_mul_norm (cfg.A -ᵥ cfg.O) (cfg.C -ᵥ cfg.O)
      have hnA : ‖cfg.A -ᵥ cfg.O‖ = dist cfg.O cfg.B := by
        rw [← dist_eq_norm_vsub, dist_comm cfg.A cfg.O]; exact cfg.hA_circle
      have hnC : ‖cfg.C -ᵥ cfg.O‖ = dist cfg.O cfg.B := by
        rw [← dist_eq_norm_vsub, dist_comm cfg.C cfg.O]; exact cfg.dist_OC
      rw [hnA, hnC] at h
      exact h.symm
    rw [e, inner_sub_right, hcos, real_inner_self_eq_norm_sq]
    have hnA : ‖cfg.A -ᵥ cfg.O‖ = dist cfg.O cfg.B := by
      rw [← dist_eq_norm_vsub, dist_comm cfg.A cfg.O]; exact cfg.hA_circle
    rw [hnA]
    ring
  have hinner' : ⟪cfg.O -ᵥ cfg.A, cfg.C -ᵥ cfg.A⟫ =
      dist cfg.O cfg.B ^ 2 * (1 - Real.cos (∠ cfg.A cfg.O cfg.C)) := by
    rw [← neg_vsub_eq_vsub_rev, ← neg_one_smul ℝ, real_inner_smul_left, hinner]
    ring
  rw [hJM, inner_add_right, real_inner_smul_right, real_inner_smul_right, hinner'] at hJ
  have hAA : ⟪cfg.O -ᵥ cfg.A, cfg.A -ᵥ cfg.O⟫ = -(dist cfg.O cfg.B ^ 2) := by
    rw [← neg_vsub_eq_vsub_rev, ← neg_one_smul ℝ, real_inner_smul_left,
      real_inner_self_eq_norm_sq]
    have hnA : ‖cfg.A -ᵥ cfg.O‖ = dist cfg.O cfg.B := by
      rw [← dist_eq_norm_vsub, dist_comm cfg.A cfg.O]; exact cfg.hA_circle
    rw [hnA]
    ring
  rw [hAA] at hJ
  have hr2 : (0:ℝ) < dist cfg.O cfg.B ^ 2 := sq_pos_of_ne_zero (ne_of_gt cfg.r_pos)
  have h3 : (cfg.lam * (1 - Real.cos (∠ cfg.A cfg.O cfg.C))) * dist cfg.O cfg.B ^ 2 =
      (1 / 2) * dist cfg.O cfg.B ^ 2 := by
    have h4 : cfg.lam * (dist cfg.O cfg.B ^ 2 * (1 - Real.cos (∠ cfg.A cfg.O cfg.C))) =
        (⅟ 2 : ℝ) * dist cfg.O cfg.B ^ 2 := by linarith [hJ]
    rw [show (⅟ 2 : ℝ) = 1 / 2 by rw [invOf_eq_inv, one_div]] at h4
    rw [show cfg.lam * (dist cfg.O cfg.B ^ 2 * (1 - Real.cos (∠ cfg.A cfg.O cfg.C))) =
      (cfg.lam * (1 - Real.cos (∠ cfg.A cfg.O cfg.C))) * dist cfg.O cfg.B ^ 2 from by ring] at h4
    exact h4
  have h2 : cfg.lam * (1 - Real.cos (∠ cfg.A cfg.O cfg.C)) = 1 / 2 :=
    mul_right_cancel₀ (ne_of_gt hr2) h3
  exact (ne_of_gt cfg.lam_half) h2

theorem J_ne_E : cfg.J ≠ cfg.E := fun h => cfg.J_notMem_perpBisector (h ▸ cfg.hE_perp)

theorem J_ne_F : cfg.J ≠ cfg.F := fun h => cfg.J_notMem_perpBisector (h ▸ cfg.hF_perp)

/- ### Sign of `σ • x` for negative `x` -/

theorem sign_coe_σ_mul_neg {x : ℝ} (hx0 : x < 0) (hxπ : -π < x) :
    (((cfg.σ : ℝ) * x : ℝ) : Real.Angle).sign = -cfg.σ := by
  rw [Real.Angle.sign, Real.Angle.sin_coe]
  have hs : Real.sin ((cfg.σ : ℝ) * x) = (cfg.σ : ℝ) * Real.sin x := by
    rcases cfg.σ_eq with hσ | hσ <;> simp [hσ]
  rw [hs]
  have hsin : Real.sin x < 0 := Real.sin_neg_of_neg_of_neg_pi_lt hx0 hxπ
  rcases cfg.σ_eq with hσ | hσ
  · rw [hσ, SignType.coe_one, one_mul]
    exact sign_neg hsin
  · rw [hσ, SignType.coe_neg, SignType.coe_one, neg_mul, one_mul]
    exact sign_pos (neg_pos.2 hsin)

theorem sign_coe_neg_σ_mul {x : ℝ} (hx0 : 0 < x) (hxπ : x < π) :
    ((↑(-((cfg.σ : ℝ) * x)) : Real.Angle).sign) = -cfg.σ := by
  rw [Real.Angle.sign, Real.Angle.sin_coe, Real.sin_neg]
  have hs : Real.sin ((cfg.σ : ℝ) * x) = (cfg.σ : ℝ) * Real.sin x := by
    rcases cfg.σ_eq with hσ | hσ <;> simp [hσ]
  rw [hs]
  rcases cfg.σ_eq with hσ | hσ
  · rw [hσ, SignType.coe_one, one_mul]
    exact sign_neg (neg_lt_zero.2 (Real.sin_pos_of_mem_Ioo ⟨hx0, hxπ⟩))
  · rw [hσ, SignType.coe_neg, SignType.coe_one, neg_mul, one_mul, neg_neg]
    exact sign_pos (Real.sin_pos_of_mem_Ioo ⟨hx0, hxπ⟩)

/- ### Non-collinearity from an angle strictly between `0` and `π` -/

omit [Module.Oriented ℝ V (Fin 2)] [Fact (finrank ℝ V = 2)] in
theorem not_collinear_of_angle_pos_lt {X Y : Pt} (h0 : 0 < ∠ X cfg.O Y) (hπ : ∠ X cfg.O Y < π)
    (hX : X ≠ cfg.O) (hY : Y ≠ cfg.O) : ¬Collinear ℝ ({X, cfg.O, Y} : Set Pt) := by
  intro hc
  rw [collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi] at hc
  rcases hc with h | h | h | h
  · exact hX h
  · exact hY h
  · exact (ne_of_gt h0) h
  · exact (ne_of_lt hπ) h

/- ### The `hFside` case: `F` is the point of `{E, F}` adjacent to `C` -/

theorem oangle_AOF (hFside : (∡ cfg.A cfg.O cfg.F).sign = -cfg.σ) :
    ∡ cfg.A cfg.O cfg.F = (-((cfg.σ : ℝ) * (π / 3)) : ℝ) := by
  have h2 := Orientation.oangle_eq_coe_sign_mul (o := positiveOrientation)
    (vsub_ne_zero.2 cfg.hA_ne_O) (vsub_ne_zero.2 cfg.F_ne_O)
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) (angle_AOF cfg) hFside
  rw [SignType.coe_neg, neg_mul] at h2
  exact h2

theorem oangle_AOE (hFside : (∡ cfg.A cfg.O cfg.F).sign = -cfg.σ) :
    ∡ cfg.A cfg.O cfg.E = ((cfg.σ : ℝ) * (π / 3) : ℝ) := by
  have hsign : (∡ cfg.A cfg.O cfg.E).sign = cfg.σ := by
    rw [cfg.sign_AOE_eq_neg_sign_AOF, hFside, neg_neg, Imo2002q2Cfg.σ]
  exact Orientation.oangle_eq_coe_sign_mul (o := positiveOrientation)
    (vsub_ne_zero.2 cfg.hA_ne_O) (vsub_ne_zero.2 cfg.E_ne_O)
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) (angle_AOE cfg) hsign

theorem oangle_FOA (hFside : (∡ cfg.A cfg.O cfg.F).sign = -cfg.σ) :
    ∡ cfg.F cfg.O cfg.A = ((cfg.σ : ℝ) * (π / 3) : ℝ) := by
  rw [oangle_rev cfg.A cfg.O cfg.F, oangle_AOF cfg hFside, ← Real.Angle.coe_neg, neg_neg]

theorem oangle_EOA (hFside : (∡ cfg.A cfg.O cfg.F).sign = -cfg.σ) :
    ∡ cfg.E cfg.O cfg.A = (-((cfg.σ : ℝ) * (π / 3)) : ℝ) := by
  rw [oangle_rev cfg.A cfg.O cfg.E, oangle_AOE cfg hFside, ← Real.Angle.coe_neg]

/- ### The second circle (center `A` through `E`, `F`, `O`, `J`) -/

/-- The circle centered at `A` through `E`, `F`, `O`, `J`. -/
noncomputable def circleA : Sphere Pt := ⟨cfg.A, dist cfg.O cfg.B⟩

omit [Module.Oriented ℝ V (Fin 2)] [Fact (finrank ℝ V = 2)] in
theorem E_mem_circleA : cfg.E ∈ cfg.circleA := mem_sphere.2 cfg.dist_EA

omit [Module.Oriented ℝ V (Fin 2)] [Fact (finrank ℝ V = 2)] in
theorem F_mem_circleA : cfg.F ∈ cfg.circleA := mem_sphere.2 cfg.dist_FA

omit [Module.Oriented ℝ V (Fin 2)] [Fact (finrank ℝ V = 2)] in
theorem O_mem_circleA : cfg.O ∈ cfg.circleA :=
  mem_sphere.2 (by show dist cfg.O cfg.A = dist cfg.O cfg.B; exact cfg.hA_circle)

theorem J_mem_circleA : cfg.J ∈ cfg.circleA :=
  mem_sphere.2 (by show dist cfg.J cfg.A = dist cfg.O cfg.B; rw [dist_comm]; exact dist_AJ cfg)

/- ### The isosceles triangle `FOE` and the angles at `A` -/

theorem oangle_FOE (hFside : (∡ cfg.A cfg.O cfg.F).sign = -cfg.σ) :
    ∡ cfg.F cfg.O cfg.E = ((cfg.σ : ℝ) * (2 * π / 3) : ℝ) := by
  have h := oangle_add cfg.F_ne_O cfg.hA_ne_O cfg.E_ne_O
  rw [oangle_FOA cfg hFside, oangle_AOE cfg hFside, ← Real.Angle.coe_add] at h
  rw [← h]
  congr 1
  ring

theorem angle_FOE (hFside : (∡ cfg.A cfg.O cfg.F).sign = -cfg.σ) :
    ∠ cfg.F cfg.O cfg.E = 2 * π / 3 := by
  have h1 : ∠ cfg.F cfg.O cfg.E = |(∡ cfg.F cfg.O cfg.E).toReal| :=
    Orientation.angle_eq_abs_oangle_toReal (o := positiveOrientation)
      (vsub_ne_zero.2 cfg.F_ne_O) (vsub_ne_zero.2 cfg.E_ne_O)
  rw [h1, oangle_FOE cfg hFside,
    cfg.σ_mul_toReal (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]), abs_mul,
    cfg.σ_abs, one_mul, abs_of_pos (by linarith [Real.pi_pos] : (0:ℝ) < 2 * π / 3)]

theorem oangle_OFE (hFside : (∡ cfg.A cfg.O cfg.F).sign = -cfg.σ) :
    ∡ cfg.O cfg.F cfg.E = (-((cfg.σ : ℝ) * (π / 6)) : ℝ) := by
  have hsign : (∡ cfg.F cfg.O cfg.E).sign = cfg.σ := by
    rw [oangle_FOE cfg hFside]
    exact cfg.sign_coe_σ_mul (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have hnc : ¬Collinear ℝ ({cfg.F, cfg.O, cfg.E} : Set Pt) :=
    cfg.not_collinear_of_angle_pos_lt (by rw [angle_FOE cfg hFside]; linarith [Real.pi_pos])
      (by rw [angle_FOE cfg hFside]; linarith [Real.pi_pos]) cfg.F_ne_O cfg.E_ne_O
  have h := oangle_base_eq_sign_mul_of_dist_eq (O := cfg.O) (P := cfg.F) (Q := cfg.E)
    (by rw [cfg.hF_circle, cfg.hE_circle]) hnc
  rw [hsign, angle_FOE cfg hFside, show ((π - 2 * π / 3) / 2 : ℝ) = π / 6 from by ring] at h
  have h2 := h.2
  rw [← Real.Angle.coe_neg] at h2
  exact h2

theorem oangle_OEF (hFside : (∡ cfg.A cfg.O cfg.F).sign = -cfg.σ) :
    ∡ cfg.O cfg.E cfg.F = ((cfg.σ : ℝ) * (π / 6) : ℝ) := by
  have hsign : (∡ cfg.F cfg.O cfg.E).sign = cfg.σ := by
    rw [oangle_FOE cfg hFside]
    exact cfg.sign_coe_σ_mul (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have hnc : ¬Collinear ℝ ({cfg.F, cfg.O, cfg.E} : Set Pt) :=
    cfg.not_collinear_of_angle_pos_lt (by rw [angle_FOE cfg hFside]; linarith [Real.pi_pos])
      (by rw [angle_FOE cfg hFside]; linarith [Real.pi_pos]) cfg.F_ne_O cfg.E_ne_O
  have h := oangle_base_eq_sign_mul_of_dist_eq (O := cfg.O) (P := cfg.F) (Q := cfg.E)
    (by rw [cfg.hF_circle, cfg.hE_circle]) hnc
  rw [hsign, angle_FOE cfg hFside, show ((π - 2 * π / 3) / 2 : ℝ) = π / 6 from by ring] at h
  exact h.1

theorem oangle_EAO (hFside : (∡ cfg.A cfg.O cfg.F).sign = -cfg.σ) :
    ∡ cfg.E cfg.A cfg.O = ((cfg.σ : ℝ) * (π / 3) : ℝ) := by
  have h := Sphere.oangle_center_eq_two_zsmul_oangle (E_mem_circleA cfg)
    (F_mem_circleA cfg) (O_mem_circleA cfg) cfg.hE_ne_F.symm cfg.F_ne_O
  have h2 : ∡ cfg.E cfg.F cfg.O = ((cfg.σ : ℝ) * (π / 6) : ℝ) := by
    rw [oangle_rev cfg.O cfg.F cfg.E, oangle_OFE cfg hFside, ← Real.Angle.coe_neg, neg_neg]
  have h3 : ∡ cfg.E cfg.A cfg.O = (2 : ℤ) • ∡ cfg.E cfg.F cfg.O := h
  rw [h2] at h3
  rw [h3, cfg.two_zsmul_coe_σ_mul (π / 6)]
  congr 1
  ring

theorem oangle_FAO (hFside : (∡ cfg.A cfg.O cfg.F).sign = -cfg.σ) :
    ∡ cfg.F cfg.A cfg.O = (-((cfg.σ : ℝ) * (π / 3)) : ℝ) := by
  have h := Sphere.oangle_center_eq_two_zsmul_oangle (F_mem_circleA cfg)
    (E_mem_circleA cfg) (O_mem_circleA cfg) cfg.hE_ne_F cfg.E_ne_O
  have h2 : ∡ cfg.F cfg.E cfg.O = (-((cfg.σ : ℝ) * (π / 6)) : ℝ) := by
    rw [oangle_rev cfg.O cfg.E cfg.F, oangle_OEF cfg hFside, ← Real.Angle.coe_neg]
  have h3 : ∡ cfg.F cfg.A cfg.O = (2 : ℤ) • ∡ cfg.F cfg.E cfg.O := h
  rw [h2] at h3
  rw [h3, two_zsmul, ← Real.Angle.coe_add]
  congr 1
  ring

theorem oangle_OAF (hFside : (∡ cfg.A cfg.O cfg.F).sign = -cfg.σ) :
    ∡ cfg.O cfg.A cfg.F = ((cfg.σ : ℝ) * (π / 3) : ℝ) := by
  rw [oangle_rev cfg.F cfg.A cfg.O, oangle_FAO cfg hFside, ← Real.Angle.coe_neg, neg_neg]

omit [Module.Oriented ℝ V (Fin 2)] [Fact (finrank ℝ V = 2)] in
theorem E_ne_A : cfg.E ≠ cfg.A := by
  intro h
  have h2 := dist_EA cfg
  rw [h, dist_self] at h2
  exact (ne_of_gt cfg.r_pos) h2.symm

omit [Module.Oriented ℝ V (Fin 2)] [Fact (finrank ℝ V = 2)] in
theorem F_ne_A : cfg.F ≠ cfg.A := by
  intro h
  have h2 := dist_FA cfg
  rw [h, dist_self] at h2
  exact (ne_of_gt cfg.r_pos) h2.symm

theorem oangle_EAF (hFside : (∡ cfg.A cfg.O cfg.F).sign = -cfg.σ) :
    ∡ cfg.E cfg.A cfg.F = ((cfg.σ : ℝ) * (2 * π / 3) : ℝ) := by
  have h := oangle_add (E_ne_A cfg) cfg.O_ne_A (F_ne_A cfg)
  rw [oangle_EAO cfg hFside, oangle_OAF cfg hFside, ← Real.Angle.coe_add] at h
  rw [← h]
  congr 1
  ring

/- ### Cosine of a pinned oriented angle -/

theorem cos_coe_σ_mul (x : ℝ) : Real.Angle.cos (↑((cfg.σ : ℝ) * x : ℝ)) = Real.cos x := by
  rw [Real.Angle.cos_coe]
  rcases cfg.σ_eq with hσ | hσ <;> simp [hσ, Real.cos_neg]

theorem cos_coe_neg_σ_mul (x : ℝ) :
    Real.Angle.cos (↑(-((cfg.σ : ℝ) * x)) : Real.Angle) = Real.cos x := by
  rw [Real.Angle.cos_coe, Real.cos_neg]
  rcases cfg.σ_eq with hσ | hσ <;> simp [hσ, Real.cos_neg]

theorem cos_angle_of_oangle {X Y : Pt} {x : ℝ} (hX : X ≠ cfg.O) (hY : Y ≠ cfg.O)
    (h : ∡ X cfg.O Y = ((cfg.σ : ℝ) * x : ℝ)) :
    Real.cos (∠ X cfg.O Y) = Real.cos x := by
  have h1 : ∠ X cfg.O Y = |(∡ X cfg.O Y).toReal| :=
    Orientation.angle_eq_abs_oangle_toReal (o := positiveOrientation)
      (vsub_ne_zero.2 hX) (vsub_ne_zero.2 hY)
  rw [h1, h, Real.cos_abs, Real.Angle.cos_toReal]
  exact cfg.cos_coe_σ_mul x

/- ### The isosceles triangle `AOC` and the angle `∡ O A C` -/

theorem oangle_OAC : ∡ cfg.O cfg.A cfg.C = ((cfg.σ : ℝ) * ((π - ∠ cfg.A cfg.O cfg.C) / 2) : ℝ) := by
  have hsign : (∡ cfg.A cfg.O cfg.C).sign = -cfg.σ := by
    rw [oangle_AOC cfg]
    exact cfg.sign_coe_neg_σ_mul cfg.angle_AOC_pos cfg.angle_AOC_lt_pi
  have h := oangle_base_eq_sign_mul_of_dist_eq (O := cfg.O) (P := cfg.A) (Q := cfg.C)
    (by rw [cfg.hA_circle, cfg.dist_OC]) cfg.not_collinear_AOC
  rw [hsign, SignType.coe_neg, ← Real.Angle.coe_neg] at h
  have h2 := h.2
  simp only [neg_mul, neg_neg] at h2
  exact h2

/- ### Angles at `F`: `∡ O F A`, `∡ E F A`, `∡ O F C`, `∡ A F C`, `∡ E F C` -/

theorem oangle_OFA (hFside : (∡ cfg.A cfg.O cfg.F).sign = -cfg.σ) :
    ∡ cfg.O cfg.F cfg.A = (-((cfg.σ : ℝ) * (π / 3)) : ℝ) := by
  have hnc : ¬Collinear ℝ ({cfg.A, cfg.O, cfg.F} : Set Pt) :=
    cfg.not_collinear_of_angle_pos_lt (by rw [angle_AOF cfg]; linarith [Real.pi_pos])
      (by rw [angle_AOF cfg]; linarith [Real.pi_pos]) cfg.hA_ne_O cfg.F_ne_O
  have h := oangle_base_eq_sign_mul_of_dist_eq (O := cfg.O) (P := cfg.A) (Q := cfg.F)
    (by rw [cfg.hA_circle, cfg.hF_circle]) hnc
  rw [hFside, angle_AOF cfg, SignType.coe_neg,
    show ((π - π / 3) / 2 : ℝ) = π / 3 from by ring, neg_mul] at h
  exact h.1

theorem oangle_EFA (hFside : (∡ cfg.A cfg.O cfg.F).sign = -cfg.σ) :
    ∡ cfg.E cfg.F cfg.A = (-((cfg.σ : ℝ) * (π / 6)) : ℝ) := by
  have h := oangle_add cfg.hE_ne_F cfg.O_ne_F (F_ne_A cfg).symm
  have h2 : ∡ cfg.E cfg.F cfg.O = ((cfg.σ : ℝ) * (π / 6) : ℝ) := by
    rw [oangle_rev cfg.O cfg.F cfg.E, oangle_OFE cfg hFside, ← Real.Angle.coe_neg, neg_neg]
  rw [h2, oangle_OFA cfg hFside] at h
  rw [← h, ← Real.Angle.coe_add]
  congr 1
  ring

theorem oangle_FOC (hFside : (∡ cfg.A cfg.O cfg.F).sign = -cfg.σ) :
    ∡ cfg.F cfg.O cfg.C = ((cfg.σ : ℝ) * (π / 3 - ∠ cfg.A cfg.O cfg.C) : ℝ) := by
  have h := oangle_add cfg.F_ne_O cfg.hA_ne_O cfg.hC_ne_O
  rw [oangle_FOA cfg hFside, oangle_AOC cfg, ← Real.Angle.coe_add] at h
  rw [← h]
  congr 1
  ring

theorem angle_FOC (hFside : (∡ cfg.A cfg.O cfg.F).sign = -cfg.σ) :
    ∠ cfg.F cfg.O cfg.C = ∠ cfg.A cfg.O cfg.C - π / 3 := by
  have h1 : ∠ cfg.F cfg.O cfg.C = |(∡ cfg.F cfg.O cfg.C).toReal| :=
    Orientation.angle_eq_abs_oangle_toReal (o := positiveOrientation)
      (vsub_ne_zero.2 cfg.F_ne_O) (vsub_ne_zero.2 cfg.hC_ne_O)
  have h2 : (((cfg.σ : ℝ) * (π / 3 - ∠ cfg.A cfg.O cfg.C) : ℝ) : Real.Angle).toReal =
      (cfg.σ : ℝ) * (π / 3 - ∠ cfg.A cfg.O cfg.C) := by
    rw [Real.Angle.toReal_coe_eq_self_iff]
    have hθ3 := cfg.hangle
    have hθπ := cfg.angle_AOC_lt_pi
    rcases cfg.σ_eq with hσ | hσ
    · rw [hσ]
      simp only [SignType.coe_one, one_mul]
      constructor <;> linarith [Real.pi_pos]
    · rw [hσ]
      simp only [SignType.coe_neg, SignType.coe_one, neg_mul, one_mul]
      constructor <;> linarith [Real.pi_pos]
  rw [h1, oangle_FOC cfg hFside, h2, abs_mul, cfg.σ_abs, one_mul,
    abs_of_neg (by have hθ3 := cfg.hangle; linarith [Real.pi_pos] :
      π / 3 - ∠ cfg.A cfg.O cfg.C < 0)]
  ring

theorem C_ne_E (hFside : (∡ cfg.A cfg.O cfg.F).sign = -cfg.σ) : cfg.C ≠ cfg.E := by
  intro h
  have h1 := oangle_AOE cfg hFside
  rw [← h] at h1
  have h2 := oangle_AOC cfg
  have hcos : Real.Angle.cos (∡ cfg.A cfg.O cfg.C) = 1 / 2 := by
    rw [h1, cfg.cos_coe_σ_mul (π / 3), Real.cos_pi_div_three]
  have hcos2 : Real.Angle.cos (∡ cfg.A cfg.O cfg.C) = Real.cos (∠ cfg.A cfg.O cfg.C) := by
    rw [h2, cfg.cos_coe_neg_σ_mul (∠ cfg.A cfg.O cfg.C)]
  rw [hcos2] at hcos
  exact (ne_of_gt cfg.cos_AOC_lt_half) hcos.symm

theorem C_ne_F (hFside : (∡ cfg.A cfg.O cfg.F).sign = -cfg.σ) : cfg.C ≠ cfg.F := by
  intro h
  have h1 := oangle_AOF cfg hFside
  rw [← h] at h1
  have h2 := oangle_AOC cfg
  have hcos : Real.Angle.cos (∡ cfg.A cfg.O cfg.C) = 1 / 2 := by
    rw [h1, cfg.cos_coe_neg_σ_mul (π / 3), Real.cos_pi_div_three]
  have hcos2 : Real.Angle.cos (∡ cfg.A cfg.O cfg.C) = Real.cos (∠ cfg.A cfg.O cfg.C) := by
    rw [h2, cfg.cos_coe_neg_σ_mul (∠ cfg.A cfg.O cfg.C)]
  rw [hcos2] at hcos
  exact (ne_of_gt cfg.cos_AOC_lt_half) hcos.symm

theorem oangle_OFC (hFside : (∡ cfg.A cfg.O cfg.F).sign = -cfg.σ) :
    ∡ cfg.O cfg.F cfg.C = ((cfg.σ : ℝ) * (2 * π / 3 - ∠ cfg.A cfg.O cfg.C / 2) : ℝ) := by
  have hsign : (∡ cfg.F cfg.O cfg.C).sign = -cfg.σ := by
    rw [oangle_FOC cfg hFside]
    apply cfg.sign_coe_σ_mul_neg
    · have hθ3 := cfg.hangle
      linarith [Real.pi_pos]
    · have hθπ := cfg.angle_AOC_lt_pi
      linarith [Real.pi_pos]
  have hnc : ¬Collinear ℝ ({cfg.F, cfg.O, cfg.C} : Set Pt) :=
    cfg.not_collinear_of_angle_pos_lt
      (by rw [angle_FOC cfg hFside]; have hθ3 := cfg.hangle; linarith [Real.pi_pos])
      (by rw [angle_FOC cfg hFside]; have hθπ := cfg.angle_AOC_lt_pi; linarith [Real.pi_pos])
      cfg.F_ne_O cfg.hC_ne_O
  have h := oangle_base_eq_sign_mul_of_dist_eq (O := cfg.O) (P := cfg.F) (Q := cfg.C)
    (by rw [cfg.hF_circle, cfg.dist_OC]) hnc
  rw [hsign, angle_FOC cfg hFside, SignType.coe_neg,
    show ((π - (∠ cfg.A cfg.O cfg.C - π / 3)) / 2 : ℝ) =
      2 * π / 3 - ∠ cfg.A cfg.O cfg.C / 2 from by ring, ← Real.Angle.coe_neg] at h
  have h2 := h.2
  simp only [neg_mul, neg_neg] at h2
  exact h2

theorem oangle_AFC (hFside : (∡ cfg.A cfg.O cfg.F).sign = -cfg.σ) :
    ∡ cfg.A cfg.F cfg.C = ((cfg.σ : ℝ) * (π - ∠ cfg.A cfg.O cfg.C / 2) : ℝ) := by
  have h := oangle_add (F_ne_A cfg).symm cfg.O_ne_F (C_ne_F cfg hFside)
  have h2 : ∡ cfg.A cfg.F cfg.O = ((cfg.σ : ℝ) * (π / 3) : ℝ) := by
    rw [oangle_rev cfg.O cfg.F cfg.A, oangle_OFA cfg hFside, ← Real.Angle.coe_neg, neg_neg]
  rw [h2, oangle_OFC cfg hFside] at h
  rw [← h, ← Real.Angle.coe_add]
  congr 1
  ring

theorem oangle_EFC (hFside : (∡ cfg.A cfg.O cfg.F).sign = -cfg.σ) :
    ∡ cfg.E cfg.F cfg.C = ((cfg.σ : ℝ) * (5 * π / 6 - ∠ cfg.A cfg.O cfg.C / 2) : ℝ) := by
  have h := oangle_add cfg.hE_ne_F (F_ne_A cfg).symm (C_ne_F cfg hFside)
  rw [oangle_EFA cfg hFside, oangle_AFC cfg hFside, ← Real.Angle.coe_add] at h
  rw [← h]
  congr 1
  ring

/- ### `C ≠ E` and `C ≠ F` -/

/- ### The bisector at `C` (goal 1) -/

theorem two_zsmul_oangle_FCA (hFside : (∡ cfg.A cfg.O cfg.F).sign = -cfg.σ) :
    (2 : ℤ) • ∡ cfg.F cfg.C cfg.A = ∡ cfg.F cfg.O cfg.A := by
  have h := Sphere.oangle_center_eq_two_zsmul_oangle cfg.F_mem_circle cfg.C_mem_circle
    cfg.A_mem_circle (C_ne_F cfg hFside) cfg.A_ne_C.symm
  exact h.symm

theorem two_zsmul_oangle_ACE (hFside : (∡ cfg.A cfg.O cfg.F).sign = -cfg.σ) :
    (2 : ℤ) • ∡ cfg.A cfg.C cfg.E = ∡ cfg.A cfg.O cfg.E := by
  have h := Sphere.oangle_center_eq_two_zsmul_oangle cfg.A_mem_circle cfg.C_mem_circle
    cfg.E_mem_circle cfg.A_ne_C.symm (C_ne_E cfg hFside)
  exact h.symm

theorem sSameSide_O_C_FA (_hFside : (∡ cfg.A cfg.O cfg.F).sign = -cfg.σ) :
    line[ℝ, cfg.F, cfg.A].SSameSide cfg.O cfg.C := by
  refine sSameSide_center_of_inner_pos (by rw [cfg.hF_circle, cfg.hA_circle]) (F_ne_A cfg) ?_ ?_
  · intro h
    have hsb : Sbtw ℝ cfg.F cfg.O cfg.A := h ▸ sbtw_midpoint_of_ne ℝ (F_ne_A cfg)
    have hpi : ∠ cfg.F cfg.O cfg.A = π := hsb.angle₁₂₃_eq_pi
    have hval := angle_FOA cfg
    rw [hpi] at hval
    linarith [Real.pi_pos, hval]
  · have hid := inner_vsub_midpoint_vsub_center (O := cfg.O) (X := cfg.F) (Y := cfg.A) (P := cfg.C)
      (by rw [cfg.hF_circle, cfg.hA_circle]) (by rw [cfg.dist_OC, cfg.hF_circle])
    have hnC : ‖cfg.C -ᵥ cfg.O‖ = dist cfg.O cfg.B := by
      rw [← dist_eq_norm_vsub, dist_comm cfg.C cfg.O]; exact cfg.dist_OC
    have hnA : ‖cfg.A -ᵥ cfg.O‖ = dist cfg.O cfg.B := by
      rw [← dist_eq_norm_vsub, dist_comm cfg.A cfg.O]; exact cfg.hA_circle
    have hnF : ‖cfg.F -ᵥ cfg.O‖ = dist cfg.O cfg.B := by
      rw [← dist_eq_norm_vsub, dist_comm cfg.F cfg.O]; exact cfg.hF_circle
    have hfa : ⟪cfg.F -ᵥ cfg.O, cfg.A -ᵥ cfg.O⟫ = dist cfg.O cfg.B ^ 2 / 2 := by
      have h := InnerProductGeometry.cos_angle_mul_norm_mul_norm (cfg.F -ᵥ cfg.O) (cfg.A -ᵥ cfg.O)
      rw [hnF, hnA] at h
      have hcos : Real.cos (InnerProductGeometry.angle (cfg.F -ᵥ cfg.O) (cfg.A -ᵥ cfg.O)) = 1 / 2 := by
        have h1 : InnerProductGeometry.angle (cfg.F -ᵥ cfg.O) (cfg.A -ᵥ cfg.O) = π / 3 :=
          angle_FOA cfg
        rw [h1, Real.cos_pi_div_three]
      rw [hcos] at h
      rw [h.symm]
      ring
    have hfc : ⟪cfg.F -ᵥ cfg.O, cfg.C -ᵥ cfg.O⟫ =
        dist cfg.O cfg.B ^ 2 * Real.cos (∠ cfg.F cfg.O cfg.C) := by
      have h := InnerProductGeometry.cos_angle_mul_norm_mul_norm (cfg.F -ᵥ cfg.O) (cfg.C -ᵥ cfg.O)
      rw [hnF, hnC] at h
      rw [h.symm, show InnerProductGeometry.angle (cfg.F -ᵥ cfg.O) (cfg.C -ᵥ cfg.O) =
        ∠ cfg.F cfg.O cfg.C from rfl]
      ring
    have hca : ⟪cfg.C -ᵥ cfg.O, cfg.A -ᵥ cfg.O⟫ =
        dist cfg.O cfg.B ^ 2 * Real.cos (∠ cfg.A cfg.O cfg.C) := by
      have h := InnerProductGeometry.cos_angle_mul_norm_mul_norm (cfg.C -ᵥ cfg.O) (cfg.A -ᵥ cfg.O)
      rw [hnC, hnA, InnerProductGeometry.angle_comm] at h
      rw [h.symm, show InnerProductGeometry.angle (cfg.A -ᵥ cfg.O) (cfg.C -ᵥ cfg.O) =
        ∠ cfg.A cfg.O cfg.C from rfl]
      ring
    have hinner : ⟪cfg.F -ᵥ cfg.C, cfg.A -ᵥ cfg.C⟫ =
        dist cfg.O cfg.B ^ 2 * (3 / 2 - Real.cos (∠ cfg.A cfg.O cfg.C) -
          Real.cos (∠ cfg.F cfg.O cfg.C)) := by
      have e1 : cfg.F -ᵥ cfg.C = (cfg.F -ᵥ cfg.O) - (cfg.C -ᵥ cfg.O) :=
        (vsub_sub_vsub_cancel_right _ _ _).symm
      have e2 : cfg.A -ᵥ cfg.C = (cfg.A -ᵥ cfg.O) - (cfg.C -ᵥ cfg.O) :=
        (vsub_sub_vsub_cancel_right _ _ _).symm
      rw [e1, e2]
      simp only [inner_sub_left, inner_sub_right]
      rw [hfa, hfc, hca, real_inner_self_eq_norm_sq, hnC]
      ring
    have hpos : 0 < ⟪cfg.F -ᵥ cfg.C, cfg.A -ᵥ cfg.C⟫ := by
      rw [hinner]
      have hle : Real.cos (∠ cfg.F cfg.O cfg.C) ≤ 1 := Real.cos_le_one _
      nlinarith [cfg.cos_AOC_lt_half, sq_pos_of_ne_zero (ne_of_gt cfg.r_pos)]
    rw [← hid] at hpos
    linarith [hpos]

theorem sSameSide_O_C_AE (_hFside : (∡ cfg.A cfg.O cfg.F).sign = -cfg.σ) :
    line[ℝ, cfg.A, cfg.E].SSameSide cfg.O cfg.C := by
  refine sSameSide_center_of_inner_pos (by rw [cfg.hA_circle, cfg.hE_circle]) (E_ne_A cfg).symm ?_ ?_
  · intro h
    have hsb : Sbtw ℝ cfg.A cfg.O cfg.E := h ▸ sbtw_midpoint_of_ne ℝ (E_ne_A cfg).symm
    have hpi : ∠ cfg.A cfg.O cfg.E = π := hsb.angle₁₂₃_eq_pi
    have hval := angle_AOE cfg
    rw [hpi] at hval
    linarith [Real.pi_pos, hval]
  · have hid := inner_vsub_midpoint_vsub_center (O := cfg.O) (X := cfg.A) (Y := cfg.E) (P := cfg.C)
      (by rw [cfg.hA_circle, cfg.hE_circle]) (by rw [cfg.dist_OC, cfg.hA_circle])
    have hnC : ‖cfg.C -ᵥ cfg.O‖ = dist cfg.O cfg.B := by
      rw [← dist_eq_norm_vsub, dist_comm cfg.C cfg.O]; exact cfg.dist_OC
    have hnA : ‖cfg.A -ᵥ cfg.O‖ = dist cfg.O cfg.B := by
      rw [← dist_eq_norm_vsub, dist_comm cfg.A cfg.O]; exact cfg.hA_circle
    have hnE : ‖cfg.E -ᵥ cfg.O‖ = dist cfg.O cfg.B := by
      rw [← dist_eq_norm_vsub, dist_comm cfg.E cfg.O]; exact cfg.hE_circle
    have hae : ⟪cfg.A -ᵥ cfg.O, cfg.E -ᵥ cfg.O⟫ = dist cfg.O cfg.B ^ 2 / 2 := by
      have h := InnerProductGeometry.cos_angle_mul_norm_mul_norm (cfg.A -ᵥ cfg.O) (cfg.E -ᵥ cfg.O)
      rw [hnA, hnE] at h
      have hcos : Real.cos (InnerProductGeometry.angle (cfg.A -ᵥ cfg.O) (cfg.E -ᵥ cfg.O)) = 1 / 2 := by
        have h1 : InnerProductGeometry.angle (cfg.A -ᵥ cfg.O) (cfg.E -ᵥ cfg.O) = π / 3 :=
          angle_AOE cfg
        rw [h1, Real.cos_pi_div_three]
      rw [hcos] at h
      rw [h.symm]
      ring
    have hce : ⟪cfg.C -ᵥ cfg.O, cfg.E -ᵥ cfg.O⟫ =
        dist cfg.O cfg.B ^ 2 * Real.cos (∠ cfg.E cfg.O cfg.C) := by
      have h := InnerProductGeometry.cos_angle_mul_norm_mul_norm (cfg.C -ᵥ cfg.O) (cfg.E -ᵥ cfg.O)
      rw [hnC, hnE, InnerProductGeometry.angle_comm] at h
      rw [h.symm, show InnerProductGeometry.angle (cfg.E -ᵥ cfg.O) (cfg.C -ᵥ cfg.O) =
        ∠ cfg.E cfg.O cfg.C from rfl]
      ring
    have hac : ⟪cfg.A -ᵥ cfg.O, cfg.C -ᵥ cfg.O⟫ =
        dist cfg.O cfg.B ^ 2 * Real.cos (∠ cfg.A cfg.O cfg.C) := by
      have h := InnerProductGeometry.cos_angle_mul_norm_mul_norm (cfg.A -ᵥ cfg.O) (cfg.C -ᵥ cfg.O)
      rw [hnA, hnC] at h
      rw [h.symm, show InnerProductGeometry.angle (cfg.A -ᵥ cfg.O) (cfg.C -ᵥ cfg.O) =
        ∠ cfg.A cfg.O cfg.C from rfl]
      ring
    have hinner : ⟪cfg.A -ᵥ cfg.C, cfg.E -ᵥ cfg.C⟫ =
        dist cfg.O cfg.B ^ 2 * (3 / 2 - Real.cos (∠ cfg.A cfg.O cfg.C) -
          Real.cos (∠ cfg.E cfg.O cfg.C)) := by
      have e1 : cfg.A -ᵥ cfg.C = (cfg.A -ᵥ cfg.O) - (cfg.C -ᵥ cfg.O) :=
        (vsub_sub_vsub_cancel_right _ _ _).symm
      have e2 : cfg.E -ᵥ cfg.C = (cfg.E -ᵥ cfg.O) - (cfg.C -ᵥ cfg.O) :=
        (vsub_sub_vsub_cancel_right _ _ _).symm
      rw [e1, e2]
      simp only [inner_sub_left, inner_sub_right]
      rw [hae, hce, hac, real_inner_self_eq_norm_sq, hnC]
      ring
    have hpos : 0 < ⟪cfg.A -ᵥ cfg.C, cfg.E -ᵥ cfg.C⟫ := by
      rw [hinner]
      have hle : Real.cos (∠ cfg.E cfg.O cfg.C) ≤ 1 := Real.cos_le_one _
      nlinarith [cfg.cos_AOC_lt_half, sq_pos_of_ne_zero (ne_of_gt cfg.r_pos)]
    rw [← hid] at hpos
    linarith [hpos]

theorem sign_FCA (hFside : (∡ cfg.A cfg.O cfg.F).sign = -cfg.σ) :
    (∡ cfg.F cfg.C cfg.A).sign = cfg.σ := by
  have hsign := (sSameSide_O_C_FA cfg hFside).oangle_sign_eq
    (left_mem_affineSpan_pair ℝ cfg.F cfg.A) (right_mem_affineSpan_pair ℝ cfg.F cfg.A)
  rw [hsign, oangle_FOA cfg hFside]
  exact cfg.sign_coe_σ_mul (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

theorem oangle_FCA (hFside : (∡ cfg.A cfg.O cfg.F).sign = -cfg.σ) :
    ∡ cfg.F cfg.C cfg.A = ((cfg.σ : ℝ) * (π / 6) : ℝ) := by
  have h := cfg.oangle_eq_half_of_two_zsmul_eq (θ := ∡ cfg.F cfg.C cfg.A) (γ := π / 3)
    (by rw [two_zsmul_oangle_FCA cfg hFside, oangle_FOA cfg hFside])
    (sign_FCA cfg hFside) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  rw [show (π / 3 : ℝ) / 2 = π / 6 from by ring] at h
  exact h

theorem sign_ACE (hFside : (∡ cfg.A cfg.O cfg.F).sign = -cfg.σ) :
    (∡ cfg.A cfg.C cfg.E).sign = cfg.σ := by
  have hsign := (sSameSide_O_C_AE cfg hFside).oangle_sign_eq
    (left_mem_affineSpan_pair ℝ cfg.A cfg.E) (right_mem_affineSpan_pair ℝ cfg.A cfg.E)
  rw [hsign, oangle_AOE cfg hFside]
  exact cfg.sign_coe_σ_mul (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

theorem oangle_ACE (hFside : (∡ cfg.A cfg.O cfg.F).sign = -cfg.σ) :
    ∡ cfg.A cfg.C cfg.E = ((cfg.σ : ℝ) * (π / 6) : ℝ) := by
  have h := cfg.oangle_eq_half_of_two_zsmul_eq (θ := ∡ cfg.A cfg.C cfg.E) (γ := π / 3)
    (by rw [two_zsmul_oangle_ACE cfg hFside, oangle_AOE cfg hFside])
    (sign_ACE cfg hFside) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  rw [show (π / 3 : ℝ) / 2 = π / 6 from by ring] at h
  exact h

theorem oangle_FCJ : ∡ cfg.F cfg.C cfg.J = ∡ cfg.F cfg.C cfg.A :=
  (sbtw_CJA cfg).oangle_eq_right

theorem oangle_JCE : ∡ cfg.J cfg.C cfg.E = ∡ cfg.A cfg.C cfg.E :=
  (sbtw_CJA cfg).oangle_eq_left

/-- The first bisector: `CJ` bisects `∡ F C E`. -/
theorem bisector_C (hFside : (∡ cfg.A cfg.O cfg.F).sign = -cfg.σ) :
    ∡ cfg.F cfg.C cfg.J = ∡ cfg.J cfg.C cfg.E := by
  rw [oangle_FCJ cfg, oangle_JCE cfg, oangle_FCA cfg hFside, oangle_ACE cfg hFside]

/- ### `∡ E A C` and `∡ E A J` -/

theorem oangle_EAC (hFside : (∡ cfg.A cfg.O cfg.F).sign = -cfg.σ) :
    ∡ cfg.E cfg.A cfg.C = ((cfg.σ : ℝ) * (5 * π / 6 - ∠ cfg.A cfg.O cfg.C / 2) : ℝ) := by
  have h := oangle_add (E_ne_A cfg) cfg.O_ne_A cfg.A_ne_C.symm
  rw [oangle_EAO cfg hFside, oangle_OAC cfg, ← Real.Angle.coe_add] at h
  rw [← h]
  congr 1
  ring

theorem oangle_EAJ : ∡ cfg.E cfg.A cfg.J = ∡ cfg.E cfg.A cfg.C :=
  (sbtw_AJC cfg).oangle_eq_right

theorem angle_EAJ (hFside : (∡ cfg.A cfg.O cfg.F).sign = -cfg.σ) :
    ∠ cfg.E cfg.A cfg.J = 5 * π / 6 - ∠ cfg.A cfg.O cfg.C / 2 := by
  have h1 : ∠ cfg.E cfg.A cfg.J = |(∡ cfg.E cfg.A cfg.J).toReal| :=
    Orientation.angle_eq_abs_oangle_toReal (o := positiveOrientation)
      (vsub_ne_zero.2 (E_ne_A cfg)) (vsub_ne_zero.2 (sbtw_AJC cfg).left_ne.symm)
  have h2 : (((cfg.σ : ℝ) * (5 * π / 6 - ∠ cfg.A cfg.O cfg.C / 2) : ℝ) : Real.Angle).toReal =
      (cfg.σ : ℝ) * (5 * π / 6 - ∠ cfg.A cfg.O cfg.C / 2) := by
    apply cfg.σ_mul_toReal
    · have hθπ := cfg.angle_AOC_lt_pi
      linarith [Real.pi_pos]
    · have hθ3 := cfg.hangle
      linarith [Real.pi_pos]
  rw [h1, oangle_EAJ cfg, oangle_EAC cfg hFside, h2, abs_mul, cfg.σ_abs, one_mul,
    abs_of_pos (by have hθπ := cfg.angle_AOC_lt_pi; linarith [Real.pi_pos] :
      (0:ℝ) < 5 * π / 6 - ∠ cfg.A cfg.O cfg.C / 2)]

theorem two_zsmul_oangle_EFJ (_hFside : (∡ cfg.A cfg.O cfg.F).sign = -cfg.σ) :
    (2 : ℤ) • ∡ cfg.E cfg.F cfg.J = ∡ cfg.E cfg.A cfg.J := by
  have h := Sphere.oangle_center_eq_two_zsmul_oangle (E_mem_circleA cfg) (F_mem_circleA cfg)
    (J_mem_circleA cfg) cfg.hE_ne_F.symm (J_ne_F cfg).symm
  exact h.symm

/- ### The inner product `⟪E - F, J - F⟫` is positive (side fact (g)) -/

omit [Module.Oriented ℝ V (Fin 2)] [Fact (finrank ℝ V = 2)] in
theorem lam_sqrt3_sin_lt : cfg.lam * Real.sqrt 3 * Real.sin (∠ cfg.A cfg.O cfg.C) < 3 / 2 := by
  have hAC : 0 < dist cfg.A cfg.C := dist_pos.2 cfg.A_ne_C
  have hsin0 : 0 < Real.sin (∠ cfg.A cfg.O cfg.C) :=
    Real.sin_pos_of_mem_Ioo ⟨cfg.angle_AOC_pos, cfg.angle_AOC_lt_pi⟩
  have hsq2 : (Real.sqrt 3 * dist cfg.O cfg.B * Real.sin (∠ cfg.A cfg.O cfg.C)) ^ 2 <
      (9 / 4) * (dist cfg.A cfg.C ^ 2) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), Real.sin_sq, cfg.dist_AC_sq]
    have hc0 : 0 < 1 - Real.cos (∠ cfg.A cfg.O cfg.C) := by linarith [cfg.cos_AOC_lt_half]
    have hc2 : 0 < 1 - 2 * Real.cos (∠ cfg.A cfg.O cfg.C) := by linarith [cfg.cos_AOC_lt_half]
    nlinarith [cfg.r_pos, hc0, hc2, sq_pos_of_ne_zero (ne_of_gt cfg.r_pos),
      mul_pos (sq_pos_of_ne_zero (ne_of_gt cfg.r_pos)) (mul_pos hc0 hc2)]
  have hsq : (Real.sqrt 3 * dist cfg.O cfg.B * Real.sin (∠ cfg.A cfg.O cfg.C)) ^ 2 <
      (3 / 2 * dist cfg.A cfg.C) ^ 2 := by
    have h1 : (3 / 2 * dist cfg.A cfg.C) ^ 2 = (9 / 4) * (dist cfg.A cfg.C ^ 2) := by ring
    rw [h1]
    exact hsq2
  have hlt : Real.sqrt 3 * dist cfg.O cfg.B * Real.sin (∠ cfg.A cfg.O cfg.C) <
      3 / 2 * dist cfg.A cfg.C := by
    have h1 : |Real.sqrt 3 * dist cfg.O cfg.B * Real.sin (∠ cfg.A cfg.O cfg.C)| <
        |3 / 2 * dist cfg.A cfg.C| := sq_lt_sq.1 hsq
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) cfg.r_pos.le) hsin0.le),
      abs_of_nonneg (mul_nonneg (by norm_num) hAC.le)] at h1
    exact h1
  have h3 : dist cfg.O cfg.B * Real.sqrt 3 * Real.sin (∠ cfg.A cfg.O cfg.C) / dist cfg.A cfg.C <
      3 / 2 := by
    rw [div_lt_iff₀ hAC]
    have h4 : dist cfg.O cfg.B * Real.sqrt 3 * Real.sin (∠ cfg.A cfg.O cfg.C) =
        Real.sqrt 3 * dist cfg.O cfg.B * Real.sin (∠ cfg.A cfg.O cfg.C) := by ring
    rw [h4]
    exact hlt
  rw [lam]
  have h5 : dist cfg.O cfg.B / dist cfg.A cfg.C * Real.sqrt 3 * Real.sin (∠ cfg.A cfg.O cfg.C) =
      dist cfg.O cfg.B * Real.sqrt 3 * Real.sin (∠ cfg.A cfg.O cfg.C) / dist cfg.A cfg.C := by ring
  rw [h5]
  exact h3

theorem cos_angle_of_oangle_neg {X Y : Pt} {x : ℝ} (hX : X ≠ cfg.O) (hY : Y ≠ cfg.O)
    (h : ∡ X cfg.O Y = (-((cfg.σ : ℝ) * x) : ℝ)) :
    Real.cos (∠ X cfg.O Y) = Real.cos x := by
  have h1 : ∠ X cfg.O Y = |(∡ X cfg.O Y).toReal| :=
    Orientation.angle_eq_abs_oangle_toReal (o := positiveOrientation)
      (vsub_ne_zero.2 hX) (vsub_ne_zero.2 hY)
  rw [h1, h, Real.cos_abs, Real.Angle.cos_toReal]
  exact cfg.cos_coe_neg_σ_mul x

theorem inner_EF_JF (hFside : (∡ cfg.A cfg.O cfg.F).sign = -cfg.σ) :
    0 < ⟪cfg.E -ᵥ cfg.F, cfg.J -ᵥ cfg.F⟫ := by
  have hnF : ‖cfg.F -ᵥ cfg.O‖ = dist cfg.O cfg.B := by
    rw [← dist_eq_norm_vsub, dist_comm cfg.F cfg.O]; exact cfg.hF_circle
  have hnA : ‖cfg.A -ᵥ cfg.O‖ = dist cfg.O cfg.B := by
    rw [← dist_eq_norm_vsub, dist_comm cfg.A cfg.O]; exact cfg.hA_circle
  have hnE : ‖cfg.E -ᵥ cfg.O‖ = dist cfg.O cfg.B := by
    rw [← dist_eq_norm_vsub, dist_comm cfg.E cfg.O]; exact cfg.hE_circle
  have hnC : ‖cfg.C -ᵥ cfg.O‖ = dist cfg.O cfg.B := by
    rw [← dist_eq_norm_vsub, dist_comm cfg.C cfg.O]; exact cfg.dist_OC
  have hea : ⟪cfg.E -ᵥ cfg.O, cfg.A -ᵥ cfg.O⟫ = dist cfg.O cfg.B ^ 2 / 2 := by
    have h := InnerProductGeometry.cos_angle_mul_norm_mul_norm (cfg.E -ᵥ cfg.O) (cfg.A -ᵥ cfg.O)
    rw [hnE, hnA] at h
    have hcos : Real.cos (InnerProductGeometry.angle (cfg.E -ᵥ cfg.O) (cfg.A -ᵥ cfg.O)) = 1 / 2 := by
      have h1 : InnerProductGeometry.angle (cfg.E -ᵥ cfg.O) (cfg.A -ᵥ cfg.O) = π / 3 :=
        angle_EOA cfg
      rw [h1, Real.cos_pi_div_three]
    rw [hcos] at h
    rw [h.symm]
    ring
  have hef : ⟪cfg.E -ᵥ cfg.O, cfg.F -ᵥ cfg.O⟫ = -(dist cfg.O cfg.B ^ 2 / 2) := by
    have h := InnerProductGeometry.cos_angle_mul_norm_mul_norm (cfg.E -ᵥ cfg.O) (cfg.F -ᵥ cfg.O)
    rw [hnE, hnF] at h
    have hcos : Real.cos (InnerProductGeometry.angle (cfg.E -ᵥ cfg.O) (cfg.F -ᵥ cfg.O)) =
        -(1 / 2) := by
      have h1 : InnerProductGeometry.angle (cfg.E -ᵥ cfg.O) (cfg.F -ᵥ cfg.O) = 2 * π / 3 := by
        rw [InnerProductGeometry.angle_comm]
        exact angle_FOE cfg hFside
      rw [h1, show (2 * π / 3 : ℝ) = π - π / 3 from by ring, Real.cos_pi_sub,
        Real.cos_pi_div_three]
    rw [hcos] at h
    rw [h.symm]
    ring
  have hfa : ⟪cfg.F -ᵥ cfg.O, cfg.A -ᵥ cfg.O⟫ = dist cfg.O cfg.B ^ 2 / 2 := by
    have h := InnerProductGeometry.cos_angle_mul_norm_mul_norm (cfg.F -ᵥ cfg.O) (cfg.A -ᵥ cfg.O)
    rw [hnF, hnA] at h
    have hcos : Real.cos (InnerProductGeometry.angle (cfg.F -ᵥ cfg.O) (cfg.A -ᵥ cfg.O)) = 1 / 2 := by
      have h1 : InnerProductGeometry.angle (cfg.F -ᵥ cfg.O) (cfg.A -ᵥ cfg.O) = π / 3 :=
        angle_FOA cfg
      rw [h1, Real.cos_pi_div_three]
    rw [hcos] at h
    rw [h.symm]
    ring
  have hec : ⟪cfg.E -ᵥ cfg.O, cfg.C -ᵥ cfg.O⟫ =
      dist cfg.O cfg.B ^ 2 * Real.cos (∠ cfg.A cfg.O cfg.C + π / 3) := by
    have h := InnerProductGeometry.cos_angle_mul_norm_mul_norm (cfg.E -ᵥ cfg.O) (cfg.C -ᵥ cfg.O)
    rw [hnE, hnC] at h
    have hcos : Real.cos (InnerProductGeometry.angle (cfg.E -ᵥ cfg.O) (cfg.C -ᵥ cfg.O)) =
        Real.cos (∠ cfg.A cfg.O cfg.C + π / 3) := by
      have h1 : ∡ cfg.E cfg.O cfg.C = (-((cfg.σ : ℝ) * (∠ cfg.A cfg.O cfg.C + π / 3)) : ℝ) := by
        have h2 := oangle_add cfg.E_ne_O cfg.hA_ne_O cfg.hC_ne_O
        rw [oangle_EOA cfg hFside, oangle_AOC cfg, ← Real.Angle.coe_add] at h2
        rw [← h2]
        congr 1
        ring
      have h3 := cfg.cos_angle_of_oangle_neg cfg.E_ne_O cfg.hC_ne_O h1
      rw [show InnerProductGeometry.angle (cfg.E -ᵥ cfg.O) (cfg.C -ᵥ cfg.O) = ∠ cfg.E cfg.O cfg.C from rfl]
      exact h3
    rw [hcos] at h
    rw [h.symm]
    ring
  have hfc : ⟪cfg.F -ᵥ cfg.O, cfg.C -ᵥ cfg.O⟫ =
      dist cfg.O cfg.B ^ 2 * Real.cos (∠ cfg.A cfg.O cfg.C - π / 3) := by
    have h := InnerProductGeometry.cos_angle_mul_norm_mul_norm (cfg.F -ᵥ cfg.O) (cfg.C -ᵥ cfg.O)
    rw [hnF, hnC] at h
    have hcos : Real.cos (InnerProductGeometry.angle (cfg.F -ᵥ cfg.O) (cfg.C -ᵥ cfg.O)) =
        Real.cos (∠ cfg.A cfg.O cfg.C - π / 3) := by
      have h3 := cfg.cos_angle_of_oangle cfg.F_ne_O cfg.hC_ne_O (oangle_FOC cfg hFside)
      rw [show InnerProductGeometry.angle (cfg.F -ᵥ cfg.O) (cfg.C -ᵥ cfg.O) = ∠ cfg.F cfg.O cfg.C from rfl,
        h3, show (π / 3 - ∠ cfg.A cfg.O cfg.C) = -(∠ cfg.A cfg.O cfg.C - π / 3) from by ring,
        Real.cos_neg]
    rw [hcos] at h
    rw [h.symm]
    ring
  have hJ : cfg.J -ᵥ cfg.O = (cfg.A -ᵥ cfg.O) + cfg.lam • ((cfg.C -ᵥ cfg.O) - (cfg.A -ᵥ cfg.O)) := by
    have h1 : cfg.J -ᵥ cfg.O = (cfg.J -ᵥ cfg.A) + (cfg.A -ᵥ cfg.O) := (vsub_add_vsub_cancel _ _ _).symm
    rw [h1, cfg.J_vsub]
    have h2 : cfg.C -ᵥ cfg.A = (cfg.C -ᵥ cfg.O) - (cfg.A -ᵥ cfg.O) := (vsub_sub_vsub_cancel_right _ _ _).symm
    rw [h2]
    module
  have e1 : cfg.E -ᵥ cfg.F = (cfg.E -ᵥ cfg.O) - (cfg.F -ᵥ cfg.O) := (vsub_sub_vsub_cancel_right _ _ _).symm
  have e2 : cfg.J -ᵥ cfg.F =
      ((cfg.A -ᵥ cfg.O) + cfg.lam • ((cfg.C -ᵥ cfg.O) - (cfg.A -ᵥ cfg.O))) - (cfg.F -ᵥ cfg.O) := by
    rw [← hJ, vsub_sub_vsub_cancel_right]
  rw [e1, e2]
  simp only [inner_sub_left, inner_sub_right, inner_add_right, real_inner_smul_right]
  rw [hea, hef, hfa, hec, hfc, real_inner_self_eq_norm_sq, hnF, Real.cos_add, Real.cos_sub,
    Real.cos_pi_div_three, Real.sin_pi_div_three]
  have hlt := lam_sqrt3_sin_lt cfg
  have hr2 : (0:ℝ) < dist cfg.O cfg.B ^ 2 := sq_pos_of_ne_zero (ne_of_gt cfg.r_pos)
  have hsin0 : 0 < Real.sin (∠ cfg.A cfg.O cfg.C) :=
    Real.sin_pos_of_mem_Ioo ⟨cfg.angle_AOC_pos, cfg.angle_AOC_lt_pi⟩
  nlinarith [hlt, hr2, hsin0, Real.sqrt_pos.2 (by norm_num : (0:ℝ) < 3),
    mul_pos hr2 (show (0:ℝ) < 3 / 2 - cfg.lam * Real.sqrt 3 * Real.sin (∠ cfg.A cfg.O cfg.C) from by
      linarith [hlt])]

theorem sSameSide_A_F_EJ (hFside : (∡ cfg.A cfg.O cfg.F).sign = -cfg.σ) :
    line[ℝ, cfg.E, cfg.J].SSameSide cfg.A cfg.F := by
  refine sSameSide_center_of_inner_pos ?_ ?_ ?_ ?_
  · rw [dist_comm cfg.A cfg.E, dist_EA cfg, dist_AJ cfg]
  · exact (J_ne_E cfg).symm
  · intro h
    have hsb : Sbtw ℝ cfg.E cfg.A cfg.J := h ▸ sbtw_midpoint_of_ne ℝ (J_ne_E cfg).symm
    have hpi : ∠ cfg.E cfg.A cfg.J = π := hsb.angle₁₂₃_eq_pi
    have hval := angle_EAJ cfg hFside
    rw [hpi] at hval
    have hθ0 := cfg.angle_AOC_pos
    have hθπ := cfg.angle_AOC_lt_pi
    linarith [Real.pi_pos]
  · have hid := inner_vsub_midpoint_vsub_center (O := cfg.A) (X := cfg.E) (Y := cfg.J) (P := cfg.F)
      (by rw [dist_comm cfg.A cfg.E, dist_EA cfg, dist_AJ cfg])
      (by rw [dist_comm cfg.A cfg.F, dist_FA cfg, dist_comm cfg.A cfg.E, dist_EA cfg])
    have hpos := inner_EF_JF cfg hFside
    rw [← hid] at hpos
    linarith [hpos]

theorem sign_EFJ (hFside : (∡ cfg.A cfg.O cfg.F).sign = -cfg.σ) :
    (∡ cfg.E cfg.F cfg.J).sign = cfg.σ := by
  have hsign := (sSameSide_A_F_EJ cfg hFside).oangle_sign_eq
    (left_mem_affineSpan_pair ℝ cfg.E cfg.J) (right_mem_affineSpan_pair ℝ cfg.E cfg.J)
  rw [hsign, oangle_EAJ cfg, oangle_EAC cfg hFside]
  apply cfg.sign_coe_σ_mul
  · have hθπ := cfg.angle_AOC_lt_pi
    linarith [Real.pi_pos]
  · have hθ3 := cfg.hangle
    linarith [Real.pi_pos]

theorem oangle_EFJ (hFside : (∡ cfg.A cfg.O cfg.F).sign = -cfg.σ) :
    ∡ cfg.E cfg.F cfg.J = ((cfg.σ : ℝ) * (5 * π / 12 - ∠ cfg.A cfg.O cfg.C / 4) : ℝ) := by
  have h := cfg.oangle_eq_half_of_two_zsmul_eq (θ := ∡ cfg.E cfg.F cfg.J)
    (γ := 5 * π / 6 - ∠ cfg.A cfg.O cfg.C / 2)
    (by rw [two_zsmul_oangle_EFJ cfg hFside, oangle_EAJ cfg, oangle_EAC cfg hFside])
    (sign_EFJ cfg hFside)
    (by have hθπ := cfg.angle_AOC_lt_pi; linarith [Real.pi_pos])
    (by have hθ3 := cfg.hangle; linarith [Real.pi_pos])
  rw [show (5 * π / 6 - ∠ cfg.A cfg.O cfg.C / 2 : ℝ) / 2 = 5 * π / 12 - ∠ cfg.A cfg.O cfg.C / 4 from by ring] at h
  exact h

theorem oangle_JFC (hFside : (∡ cfg.A cfg.O cfg.F).sign = -cfg.σ) :
    ∡ cfg.J cfg.F cfg.C = ((cfg.σ : ℝ) * (5 * π / 12 - ∠ cfg.A cfg.O cfg.C / 4) : ℝ) := by
  have h := oangle_add (J_ne_F cfg) cfg.hE_ne_F (C_ne_F cfg hFside)
  rw [oangle_rev cfg.E cfg.F cfg.J, oangle_EFJ cfg hFside, oangle_EFC cfg hFside,
    ← Real.Angle.coe_neg, ← Real.Angle.coe_add] at h
  rw [← h]
  congr 1
  ring

/-- The second bisector: `FJ` bisects `∡ E F C`. -/
theorem bisector_F (hFside : (∡ cfg.A cfg.O cfg.F).sign = -cfg.σ) :
    ∡ cfg.E cfg.F cfg.J = ∡ cfg.J cfg.F cfg.C := by
  rw [oangle_EFJ cfg hFside, oangle_JFC cfg hFside]

/- ### Conclusion: `J` is the incenter -/

theorem affineIndependent_CEF (hFside : (∡ cfg.A cfg.O cfg.F).sign = -cfg.σ) :
    AffineIndependent ℝ ![cfg.C, cfg.E, cfg.F] := by
  have hcosp : Cospherical ({cfg.C, cfg.E, cfg.F} : Set Pt) := by
    refine cospherical_iff_exists_sphere.2 ⟨cfg.circle, ?_⟩
    simp [Set.insert_subset_iff, Set.singleton_subset_iff, cfg.C_mem_circle, cfg.E_mem_circle,
      cfg.F_mem_circle]
  exact hcosp.affineIndependent_of_ne (C_ne_E cfg hFside) (C_ne_F cfg hFside) cfg.hE_ne_F

/-- The main result in the `hFside` case: `J` is the incenter of `CEF`. -/
theorem result (hFside : (∡ cfg.A cfg.O cfg.F).sign = -cfg.σ) :
    cfg.J = (⟨![cfg.C, cfg.E, cfg.F], affineIndependent_CEF cfg hFside⟩ : Triangle ℝ Pt).incenter := by
  apply Affine.Triangle.eq_incenter_of_oangle_eq (t := (⟨![cfg.C, cfg.E, cfg.F],
    affineIndependent_CEF cfg hFside⟩ : Triangle ℝ Pt)) (i₁ := 0) (i₂ := 2) (i₃ := 1)
    (by decide) (by decide) (by decide)
  · show ∡ cfg.F cfg.C cfg.J = ∡ cfg.J cfg.C cfg.E
    exact bisector_C cfg hFside
  · show ∡ cfg.E cfg.F cfg.J = ∡ cfg.J cfg.F cfg.C
    exact bisector_F cfg hFside

end Oriented

end Imo2002q2Cfg

snip end

problem imo2002_p2 [Fact (finrank ℝ V = 2)] (B C O A E F D J : Pt)
    (hO_midpoint : O = midpoint ℝ B C) (hB_ne_C : B ≠ C)
    (hA_circle : dist O A = dist O B) (hE_circle : dist O E = dist O B)
    (hF_circle : dist O F = dist O B) (hD_circle : dist O D = dist O B)
    (hE_perp : E ∈ AffineSubspace.perpBisector A O)
    (hF_perp : F ∈ AffineSubspace.perpBisector A O)
    (hE_ne_F : E ≠ F) (hA_ne_O : A ≠ O) (hC_ne_O : C ≠ O) (hA_ne_B : A ≠ B)
    (hangle : Real.pi / 3 < ∠ A O C)
    (hD_arc : ∠ A O D = ∠ D O B) (hD_minor : ∠ A O D + ∠ D O B = ∠ A O B)
    (hD_ne_A : D ≠ A) (hD_ne_B : D ≠ B)
    (hJ_mem : J ∈ line[ℝ, A, C]) (hJ_par : line[ℝ, O, J] ∥ line[ℝ, A, D])
    (hO_ne_J : O ≠ J) (hA_ne_D : A ≠ D) :
    ∃ h : AffineIndependent ℝ ![C, E, F],
      J = (⟨![C, E, F], h⟩ : Triangle ℝ Pt).incenter := by
  let cfg : Imo2002q2Cfg V Pt :=
    ⟨B, C, O, A, E, F, D, J, hO_midpoint, hB_ne_C, hA_circle, hE_circle, hF_circle, hD_circle,
      hE_perp, hF_perp, hE_ne_F, hA_ne_O, hC_ne_O, hA_ne_B, hangle, hD_arc, hD_minor, hD_ne_A,
      hD_ne_B, hJ_mem, hJ_par, hO_ne_J, hA_ne_D⟩
  haveI : Module.Oriented ℝ V (Fin 2) := Imo2002P2.someOrientation (V := V)
  by_cases hFside : (∡ cfg.A cfg.O cfg.F).sign = -cfg.σ
  · exact ⟨Imo2002q2Cfg.affineIndependent_CEF cfg hFside, Imo2002q2Cfg.result cfg hFside⟩
  · -- Swap the roles of `E` and `F`.
    have hF' : (∡ cfg.A cfg.O cfg.F).sign = cfg.σ := by
      have h0 : (∡ cfg.A cfg.O cfg.F).sign ≠ 0 :=
        Real.Angle.sign_ne_zero_iff.2 (Imo2002q2Cfg.oangle_AOF_ne cfg)
      have h1 : ∀ s t : SignType, s ≠ 0 → t ≠ 0 → s ≠ -t → s = t := by
        intro s t h1 h2 h3
        rcases s with _ | _ | _ <;> rcases t with _ | _ | _ <;> simp_all
      exact h1 _ _ h0 cfg.σ_ne_zero hFside
    have hFs : (∡ cfg.symm.A cfg.symm.O cfg.symm.F).sign = -(cfg.symm.σ) := by
      show (∡ cfg.A cfg.O cfg.E).sign = -(∡ cfg.C cfg.O cfg.A).sign
      rw [cfg.sign_AOE_eq_neg_sign_AOF, hF', Imo2002q2Cfg.σ]
    have haiS := Imo2002q2Cfg.affineIndependent_CEF cfg.symm hFs
    have hb1 := Imo2002q2Cfg.bisector_C cfg.symm hFs
    have hb2 := Imo2002q2Cfg.bisector_F cfg.symm hFs
    have hai : AffineIndependent ℝ ![cfg.C, cfg.E, cfg.F] := by
      have hai2 : AffineIndependent ℝ ![cfg.C, cfg.F, cfg.E] := haiS
      rw [← affineIndependent_equiv (Equiv.swap (1 : Fin 3) 2)]
      convert hai2 using 1
      ext i
      fin_cases i <;>
        simp [Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Equiv.swap_apply_left, Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne]
    refine ⟨hai, ?_⟩
    show cfg.symm.J = (⟨![cfg.C, cfg.E, cfg.F], hai⟩ : Triangle ℝ Pt).incenter
    apply Affine.Triangle.eq_incenter_of_oangle_eq (t := (⟨![cfg.C, cfg.E, cfg.F],
      hai⟩ : Triangle ℝ Pt)) (i₁ := 0) (i₂ := 1) (i₃ := 2) (by decide) (by decide) (by decide)
    · show ∡ cfg.symm.F cfg.symm.C cfg.symm.J = ∡ cfg.symm.J cfg.symm.C cfg.symm.E
      exact hb1
    · show ∡ cfg.symm.E cfg.symm.F cfg.symm.J = ∡ cfg.symm.J cfg.symm.F cfg.C
      exact hb2

end Imo2002P2
