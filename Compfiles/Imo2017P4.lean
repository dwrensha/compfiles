/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Geometry.Euclidean.Angle.Sphere
public import Mathlib.Geometry.Euclidean.Similarity
public import Mathlib.Geometry.Euclidean.Sphere.Power
public import Mathlib.Geometry.Euclidean.Sphere.SecondInter
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.MetricSpace.Similarity
public import ProblemExtraction

@[expose] public section

problem_file {
  tags := [.Geometry]
}

/-!
# International Mathematical Olympiad 2017, Problem 4

Let `R` and `S` be different points on a circle `Ω` such that `RS` is not a diameter.
Let `ℓ` be the tangent line to `Ω` at `R`. Point `T` is such that `S` is the midpoint
of `RT`. Point `J` is chosen on the minor arc `RS` of `Ω` so that the circumcircle `Γ`
of triangle `JST` intersects `ℓ` at two distinct points. Let `A` be the common point of
`Γ` and `ℓ` closer to `R`. Line `AJ` meets `Ω` again at `K`. Prove that line `KT` is
tangent to `Γ`.
-/

open Affine Affine.Simplex EuclideanGeometry FiniteDimensional Module

open scoped Affine EuclideanGeometry Real Similar

attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

variable (V : Type*) (Pt : Type*)

variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace Pt]
variable [NormedAddTorsor V Pt]

namespace Imo2017P4

snip begin

/-
We follow the standard elementary solution (also Solution 1 in Evan Chen's notes).
First, an angle chase gives
  ∡RKA = ∡RKJ = ∡RSJ = ∡TSJ = ∡TAJ = ∡TAK  (mod π),
so `RK ∥ AT`; with the correct configuration signs this holds as an equality of oriented
angles mod `2π`, which says that the vectors `R -ᵥ K` and `A -ᵥ T` are on the same ray.
Second, the alternate segment theorem in `Ω` gives `∠SKR = ∠TRA`, and the parallel lines
give `∠KRS = ∠RTA`, so triangles `SKR` and `ART` are similar, yielding
`KR · TA = RS · RT`.  Finally, writing `T -ᵥ R = 2 • (S -ᵥ R)` (midpoint) and
`A -ᵥ T = c • (R -ᵥ K)` with `c > 0` (same ray), an inner product computation shows
`KT² = KA² - AR²`.  Together with the tangent-secant theorem `AR² = AJ · AK` in `Ω`
and the strict betweenness `A`-`J`-`K`, this gives `KT² = KA · KJ = Γ.power K`,
so `KT` is tangent to `Γ` at `T` by `Sphere.isTangentAt_of_dist_sq_eq_power`.

As usual in these formalizations, the bulk of the work is in nondegeneracy conditions
and in the sign analysis of oriented angles.  The positional facts that are "obvious
from the diagram" (the strict betweenness `Sbtw ℝ A J K`, and the various side
conditions on chords) are taken as hypotheses of the configuration, following the
conventions described in `Imo2019P2.lean`.
-/

noncomputable section

/-- A configuration satisfying the conditions of the problem.  We collect the points,
the two circles and the hypotheses (including the positional ones implicit in the
diagram) in a structure to avoid passing many hypotheses around. -/
structure Imo2017P4Cfg (V : Type*) (Pt : Type*) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace Pt] [NormedAddTorsor V Pt] where
  (Ω Γ : Sphere Pt)
  (R S J T A K : Pt)
  /-- `S` lies on `Ω`. -/
  hSΩ : S ∈ Ω
  /-- `R ≠ S`. -/
  hRS : R ≠ S
  /-- `RS` is not a diameter of `Ω`. -/
  hdiam : ∠ R Ω.center S ≠ π
  /-- `S` is the midpoint of `RT`. -/
  hT : S = midpoint ℝ R T
  /-- `J` lies on `Ω`. -/
  hJΩ : J ∈ Ω
  /-- Implicit in "minor arc": `J ≠ R`. -/
  hJR : J ≠ R
  /-- Implicit in "minor arc": `J ≠ S`. -/
  hJS : J ≠ S
  /-- `J` is on the minor arc `RS`, i.e. on the side of chord `RS` opposite to the
  center of `Ω`. -/
  hJside : line[ℝ, R, S].SOppSide J Ω.center
  /-- `Γ` is the circumcircle of `JST`: `J ∈ Γ`. -/
  hJΓ : J ∈ Γ
  /-- `Γ` is the circumcircle of `JST`: `S ∈ Γ`. -/
  hSΓ : S ∈ Γ
  /-- `Γ` is the circumcircle of `JST`: `T ∈ Γ`. -/
  hTΓ : T ∈ Γ
  /-- `A` is a common point of `Γ` and `ℓ`. -/
  hAΓ : A ∈ Γ
  /-- `ℓ`, the line through `R` and `A`, is tangent to `Ω` at `R`. -/
  hAℓ : Ω.IsTangentAt R line[ℝ, R, A]
  /-- `A ≠ R` (implicit in "`A` is the common point of `Γ` and `ℓ` closer to `R`"). -/
  hAR : A ≠ R
  /-- `Γ` intersects `ℓ` at two distinct points: the second intersection of the line
  through `A` and `R` with `Γ` is different from `A`. -/
  hB : Γ.secondInter A (R -ᵥ A) ≠ A
  /-- `A` is the common point of `Γ` and `ℓ` closer to `R`. -/
  hcloser : dist A R < dist (Γ.secondInter A (R -ᵥ A)) R
  /-- `K` is on `Ω` again (i.e. on `Ω` and different from `J`): `K ∈ Ω`. -/
  hKΩ : K ∈ Ω
  /-- `K ≠ J`. -/
  hKJ : K ≠ J
  /-- `K` is on line `AJ`. -/
  hcol : Collinear ℝ ({A, J, K} : Set Pt)
  /-- The order on line `AJ` is `A`, `J`, `K` (implicit in the diagram). -/
  hPa : Sbtw ℝ A J K
  /-- `A` and `J` are on the same side of chord `RS` (implicit in the diagram). -/
  hPb : line[ℝ, R, S].SSameSide A J
  /-- `K` and `J` are on opposite sides of chord `RS` (implicit in the diagram). -/
  hPc : line[ℝ, R, S].SOppSide K J
  /-- `K` and `S` are on the same side of chord `RJ` (implicit in the diagram). -/
  hPe : line[ℝ, R, J].SSameSide K S
  /-- `S` and `A` are on opposite sides of chord `TJ` (implicit in the diagram). -/
  hPf : line[ℝ, T, J].SOppSide S A

variable {V Pt}

/-- A default choice of orientation, for lemmas that need to pick one. -/
@[implicit_reducible]
def someOrientation (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [hd2 : Fact (finrank ℝ V = 2)] : Module.Oriented ℝ V (Fin 2) :=
  ⟨Basis.orientation (finBasisOfFinrankEq _ _ hd2.out)⟩

namespace Imo2017P4Cfg

variable (cfg : Imo2017P4Cfg V Pt)

/-! ### Basic nondegeneracy properties of the configuration -/

theorem R_mem_Ω : cfg.R ∈ cfg.Ω := cfg.hAℓ.mem_sphere

theorem S_ne_T : cfg.S ≠ cfg.T := by
  intro h
  have hT := cfg.hT
  rw [h] at hT
  have h2 : cfg.R = cfg.T := Iff.mp (midpoint_eq_right_iff ℝ) hT.symm
  exact cfg.hRS (h2.trans h.symm)

theorem R_ne_T : cfg.R ≠ cfg.T := by
  intro h
  have hT := cfg.hT
  rw [h, midpoint_self] at hT
  exact cfg.hRS (h.trans hT.symm)

theorem wbtw_RST : Wbtw ℝ cfg.R cfg.S cfg.T := cfg.hT ▸ wbtw_midpoint ℝ cfg.R cfg.T

theorem sbtw_RST : Sbtw ℝ cfg.R cfg.S cfg.T := ⟨cfg.wbtw_RST, cfg.hRS.symm, cfg.S_ne_T⟩

theorem collinear_RST : Collinear ℝ ({cfg.R, cfg.S, cfg.T} : Set Pt) :=
  cfg.sbtw_RST.wbtw.collinear

theorem T_mem_lineRS : cfg.T ∈ line[ℝ, cfg.R, cfg.S] :=
  cfg.collinear_RST.mem_affineSpan_of_mem_of_ne (Set.mem_insert _ _)
    (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))) cfg.hRS

theorem J_not_mem_lineRS : cfg.J ∉ line[ℝ, cfg.R, cfg.S] := cfg.hJside.left_notMem

theorem K_not_mem_lineRS : cfg.K ∉ line[ℝ, cfg.R, cfg.S] := cfg.hPc.left_notMem

theorem A_not_mem_lineRS : cfg.A ∉ line[ℝ, cfg.R, cfg.S] := cfg.hPb.left_notMem

theorem A_ne_S : cfg.A ≠ cfg.S := by
  intro h
  have h1 := cfg.A_not_mem_lineRS
  rw [h] at h1
  exact h1 (right_mem_affineSpan_pair ℝ _ _)

theorem A_ne_T : cfg.A ≠ cfg.T := by
  intro h
  have h1 := cfg.A_not_mem_lineRS
  rw [h] at h1
  exact h1 cfg.T_mem_lineRS

theorem A_ne_J : cfg.A ≠ cfg.J := by
  intro h
  have hJmem : cfg.J ∈ line[ℝ, cfg.R, cfg.A] := by
    rw [← h]; exact right_mem_affineSpan_pair ℝ _ _
  have h1 : cfg.J = cfg.R := cfg.hAℓ.mem_and_mem_iff_eq.1 ⟨cfg.hJΩ, hJmem⟩
  exact cfg.hJR h1

theorem K_ne_R : cfg.K ≠ cfg.R := by
  intro h
  have hcol := cfg.hcol
  rw [h] at hcol
  have hJmem : cfg.J ∈ line[ℝ, cfg.R, cfg.A] := by
    have h2 := hcol.mem_affineSpan_of_mem_of_ne
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
      (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) cfg.hAR.symm
    exact (Set.pair_comm cfg.A cfg.R) ▸ h2
  have h1 : cfg.J = cfg.R := cfg.hAℓ.mem_and_mem_iff_eq.1 ⟨cfg.hJΩ, hJmem⟩
  exact cfg.hJR h1

theorem K_ne_S : cfg.K ≠ cfg.S := by
  intro h
  have h1 := cfg.K_not_mem_lineRS
  rw [h] at h1
  exact h1 (right_mem_affineSpan_pair ℝ _ _)

theorem K_ne_T : cfg.K ≠ cfg.T := by
  intro h
  have hTΩ : cfg.T ∈ cfg.Ω := h ▸ cfg.hKΩ
  have hpow : cfg.Ω.power cfg.T = 0 :=
    (Sphere.power_eq_zero_iff_mem_sphere (Sphere.radius_nonneg_of_mem cfg.R_mem_Ω)).2 hTΩ
  have hmul := Sphere.mul_dist_eq_abs_power cfg.T_mem_lineRS cfg.R_mem_Ω cfg.hSΩ
  rw [hpow, abs_zero] at hmul
  rcases mul_eq_zero.1 hmul with h1 | h1
  · exact cfg.R_ne_T (dist_eq_zero.1 h1).symm
  · exact cfg.S_ne_T (dist_eq_zero.1 h1).symm

theorem J_ne_T : cfg.J ≠ cfg.T := by
  intro h
  have h1 := cfg.J_not_mem_lineRS
  rw [h] at h1
  exact h1 cfg.T_mem_lineRS

theorem A_ne_K : cfg.A ≠ cfg.K := by
  intro h
  have hKmem : cfg.K ∈ line[ℝ, cfg.R, cfg.A] := by
    rw [← h]; exact right_mem_affineSpan_pair ℝ _ _
  have h1 : cfg.K = cfg.R := cfg.hAℓ.mem_and_mem_iff_eq.1 ⟨cfg.hKΩ, hKmem⟩
  exact cfg.hAR (h.trans h1)

theorem O_ne_R : cfg.Ω.center ≠ cfg.R := by
  intro h
  have h1 : dist cfg.R cfg.Ω.center = cfg.Ω.radius :=
    EuclideanGeometry.mem_sphere.1 cfg.R_mem_Ω
  have h2 : dist cfg.S cfg.Ω.center = cfg.Ω.radius :=
    EuclideanGeometry.mem_sphere.1 cfg.hSΩ
  rw [← h, dist_self] at h1
  rw [← h1, dist_eq_zero] at h2
  exact cfg.hRS (h ▸ h2).symm

theorem not_collinear_SKR : ¬Collinear ℝ ({cfg.S, cfg.K, cfg.R} : Set Pt) := by
  intro h
  have h2 : cfg.K ∈ line[ℝ, cfg.S, cfg.R] :=
    h.mem_affineSpan_of_mem_of_ne (Set.mem_insert _ _)
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
      (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) cfg.hRS.symm
  rw [Set.pair_comm] at h2
  exact cfg.K_not_mem_lineRS h2

theorem not_collinear_KRS : ¬Collinear ℝ ({cfg.K, cfg.R, cfg.S} : Set Pt) := by
  intro h
  have h2 : cfg.K ∈ line[ℝ, cfg.R, cfg.S] :=
    h.mem_affineSpan_of_mem_of_ne (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
      (Set.mem_insert _ _) cfg.hRS
  exact cfg.K_not_mem_lineRS h2

theorem not_collinear_RKA : ¬Collinear ℝ ({cfg.R, cfg.K, cfg.A} : Set Pt) := by
  intro h
  have h2 : cfg.K ∈ line[ℝ, cfg.R, cfg.A] :=
    h.mem_affineSpan_of_mem_of_ne (Set.mem_insert _ _)
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
      (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) cfg.hAR.symm
  have h1 : cfg.K = cfg.R := cfg.hAℓ.mem_and_mem_iff_eq.1 ⟨cfg.hKΩ, h2⟩
  exact cfg.K_ne_R h1

theorem sOppSide_KA : line[ℝ, cfg.R, cfg.S].SOppSide cfg.K cfg.A :=
  (cfg.hPb.trans_sOppSide cfg.hPc.symm).symm

end Imo2017P4Cfg

/-! ### General helper lemmas on oriented angles -/

section Oriented

variable [Module.Oriented ℝ V (Fin 2)] [Fact (finrank ℝ V = 2)]

/-- If twice two oriented angles are equal and their signs are equal and nonzero,
then the oriented angles are equal. -/
theorem oangle_eq_of_two_zsmul_oangle_eq_of_sign_eq {p₁ p₂ p₃ p₄ p₅ p₆ : Pt}
    (h2 : (2 : ℤ) • ∡ p₁ p₂ p₃ = (2 : ℤ) • ∡ p₄ p₅ p₆)
    (hs : (∡ p₁ p₂ p₃).sign = (∡ p₄ p₅ p₆).sign)
    (hn : (∡ p₁ p₂ p₃).sign ≠ 0) :
    ∡ p₁ p₂ p₃ = ∡ p₄ p₅ p₆ := by
  rcases Real.Angle.two_zsmul_eq_iff.1 h2 with h | h
  · exact h
  · exfalso
    have h4 : (∡ p₁ p₂ p₃).sign = 0 := by
      have h5 : (∡ p₁ p₂ p₃).sign = -(∡ p₁ p₂ p₃).sign := by
        calc (∡ p₁ p₂ p₃).sign = (∡ p₄ p₅ p₆ + π).sign := by rw [h]
          _ = -(∡ p₄ p₅ p₆).sign := Real.Angle.sign_add_pi _
          _ = -(∡ p₁ p₂ p₃).sign := by rw [← hs]
      simpa using h5
    exact hn h4

/-- If the unoriented angle `∠ p₁ p₂ p₃` equals `π / 2`, then twice the oriented angle
equals `π`. -/
theorem two_zsmul_oangle_eq_pi_of_angle_eq_pi_div_two {p₁ p₂ p₃ : Pt}
    (hp₁ : p₁ ≠ p₂) (hp₃ : p₃ ≠ p₂) (h : ∠ p₁ p₂ p₃ = π / 2) :
    (2 : ℤ) • ∡ p₁ p₂ p₃ = π := by
  rw [angle_eq_abs_oangle_toReal hp₁ hp₃] at h
  rcases eq_or_eq_neg_of_abs_eq h with h1 | h1
  · have h2 : ∡ p₁ p₂ p₃ = ((π / 2 : ℝ) : Real.Angle) := by
      rw [← Real.Angle.coe_toReal (∡ p₁ p₂ p₃), h1]
    rw [h2, Real.Angle.two_zsmul_coe_div_two]
  · have h2 : ∡ p₁ p₂ p₃ = ((-(π / 2) : ℝ) : Real.Angle) := by
      rw [← Real.Angle.coe_toReal (∡ p₁ p₂ p₃), h1]
    have h3 : (-(π / 2) : ℝ) = (-π) / 2 := by ring
    rw [h2, h3, Real.Angle.two_zsmul_coe_div_two, Real.Angle.coe_neg, Real.Angle.neg_coe_pi]

namespace Imo2017P4Cfg

variable (cfg : Imo2017P4Cfg V Pt)

/-! ### Nondegeneracy of the oriented angles -/

theorem sign_RKA_ne : (∡ cfg.R cfg.K cfg.A).sign ≠ 0 := by
  intro h
  rw [oangle_sign_eq_zero_iff_collinear] at h
  exact cfg.not_collinear_RKA h

theorem sign_SKR_ne : (∡ cfg.S cfg.K cfg.R).sign ≠ 0 := by
  intro h
  rw [oangle_sign_eq_zero_iff_collinear] at h
  exact cfg.not_collinear_SKR h

theorem sign_KRS_ne : (∡ cfg.K cfg.R cfg.S).sign ≠ 0 := by
  intro h
  rw [oangle_sign_eq_zero_iff_collinear] at h
  exact cfg.not_collinear_KRS h

/-! ### The alternate segment theorem for `Ω` at `R` -/

theorem two_zsmul_oangle_ARS :
    (2 : ℤ) • ∡ cfg.A cfg.R cfg.S = (2 : ℤ) • ∡ cfg.R cfg.J cfg.S := by
  have h2 := Sphere.two_zsmul_oangle_center_add_two_zsmul_oangle_eq_pi
    cfg.R_mem_Ω cfg.hJΩ cfg.hSΩ cfg.hJR cfg.hJS cfg.hRS
  have h3 : (2 : ℤ) • ∡ cfg.A cfg.R cfg.Ω.center = π :=
    two_zsmul_oangle_eq_pi_of_angle_eq_pi_div_two cfg.hAR cfg.O_ne_R
      (cfg.hAℓ.angle_eq_pi_div_two (right_mem_affineSpan_pair ℝ _ _))
  calc (2 : ℤ) • ∡ cfg.A cfg.R cfg.S
      = (2 : ℤ) • (∡ cfg.A cfg.R cfg.Ω.center + ∡ cfg.Ω.center cfg.R cfg.S) := by
        rw [oangle_add cfg.hAR cfg.O_ne_R cfg.hRS.symm]
    _ = (2 : ℤ) • ∡ cfg.A cfg.R cfg.Ω.center + (2 : ℤ) • ∡ cfg.Ω.center cfg.R cfg.S := by
        rw [smul_add]
    _ = π - (2 : ℤ) • ∡ cfg.S cfg.R cfg.Ω.center := by
        rw [h3, oangle_rev, smul_neg, sub_eq_add_neg]
    _ = (2 : ℤ) • ∡ cfg.R cfg.J cfg.S := by
        rw [eq_sub_of_add_eq h2, sub_sub_self]

theorem two_zsmul_oangle_SRA :
    (2 : ℤ) • ∡ cfg.S cfg.R cfg.A = (2 : ℤ) • ∡ cfg.S cfg.J cfg.R := by
  rw [oangle_rev, smul_neg, cfg.two_zsmul_oangle_ARS, ← smul_neg, ← oangle_rev]

/-! ### The first angle chase: twice `∡RKA` equals twice `∡TAK` -/

theorem two_zsmul_oangle_RKA :
    (2 : ℤ) • ∡ cfg.R cfg.K cfg.A = (2 : ℤ) • ∡ cfg.T cfg.A cfg.K := by
  have h1 : ∡ cfg.R cfg.K cfg.A = ∡ cfg.R cfg.K cfg.J :=
    (Wbtw.oangle_eq_right cfg.hPa.symm.wbtw cfg.hKJ.symm).symm
  have h2 : (2 : ℤ) • ∡ cfg.R cfg.K cfg.J = (2 : ℤ) • ∡ cfg.R cfg.S cfg.J :=
    Sphere.two_zsmul_oangle_eq cfg.R_mem_Ω cfg.hKΩ cfg.hSΩ cfg.hJΩ
      cfg.K_ne_R cfg.hKJ cfg.hRS.symm cfg.hJS.symm
  have h3 : (2 : ℤ) • ∡ cfg.R cfg.S cfg.J = (2 : ℤ) • ∡ cfg.T cfg.S cfg.J :=
    Collinear.two_zsmul_oangle_eq_left cfg.collinear_RST cfg.hRS cfg.S_ne_T.symm
  have h4 : (2 : ℤ) • ∡ cfg.T cfg.S cfg.J = (2 : ℤ) • ∡ cfg.T cfg.A cfg.J :=
    Sphere.two_zsmul_oangle_eq cfg.hTΓ cfg.hSΓ cfg.hAΓ cfg.hJΓ
      cfg.S_ne_T cfg.hJS.symm cfg.A_ne_T cfg.A_ne_J
  have h5 : ∡ cfg.T cfg.A cfg.J = ∡ cfg.T cfg.A cfg.K :=
    Wbtw.oangle_eq_right cfg.hPa.wbtw cfg.A_ne_J.symm
  rw [h1, h2, h3, h4, h5]

/-! ### The sign of `∡RKA` equals the sign of `∡TAK` -/

theorem sign_RKA : (∡ cfg.R cfg.K cfg.A).sign = (∡ cfg.T cfg.A cfg.K).sign := by
  have e1 : ∡ cfg.R cfg.K cfg.A = ∡ cfg.R cfg.K cfg.J :=
    (Wbtw.oangle_eq_right cfg.hPa.symm.wbtw cfg.hKJ.symm).symm
  have s1 : (∡ cfg.R cfg.K cfg.J).sign = (∡ cfg.R cfg.S cfg.J).sign :=
    (AffineSubspace.SSameSide.oangle_sign_eq (left_mem_affineSpan_pair ℝ _ _)
      (right_mem_affineSpan_pair ℝ _ _) cfg.hPe).symm
  have e2 : ∡ cfg.R cfg.S cfg.J = ∡ cfg.T cfg.S cfg.J + π :=
    Sbtw.oangle_eq_add_pi_left cfg.sbtw_RST cfg.hJS
  have s2 : (∡ cfg.T cfg.S cfg.J).sign = -(∡ cfg.T cfg.A cfg.J).sign :=
    AffineSubspace.SOppSide.oangle_sign_eq_neg (left_mem_affineSpan_pair ℝ _ _)
      (right_mem_affineSpan_pair ℝ _ _) cfg.hPf.symm
  have e3 : ∡ cfg.T cfg.A cfg.J = ∡ cfg.T cfg.A cfg.K :=
    Wbtw.oangle_eq_right cfg.hPa.wbtw cfg.A_ne_J.symm
  rw [e1, s1, e2, Real.Angle.sign_add_pi, s2, neg_neg, e3]

/-! ### `RK` is parallel to `TA` -/

theorem parallel_KR_TA : line[ℝ, cfg.K, cfg.R] ∥ line[ℝ, cfg.T, cfg.A] := by
  have hRK : cfg.R -ᵥ cfg.K ≠ 0 := vsub_ne_zero.2 cfg.K_ne_R.symm
  have hAK : cfg.A -ᵥ cfg.K ≠ 0 := vsub_ne_zero.2 cfg.A_ne_K
  have hAT : cfg.A -ᵥ cfg.T ≠ 0 := vsub_ne_zero.2 cfg.A_ne_T
  have h1 : (2 : ℤ) • Module.Oriented.positiveOrientation.oangle (cfg.R -ᵥ cfg.K) (cfg.A -ᵥ cfg.K) =
      (2 : ℤ) • Module.Oriented.positiveOrientation.oangle (cfg.A -ᵥ cfg.T) (cfg.A -ᵥ cfg.K) := by
    have h11 := cfg.two_zsmul_oangle_RKA
    have e2 : ∡ cfg.T cfg.A cfg.K =
        Module.Oriented.positiveOrientation.oangle (cfg.A -ᵥ cfg.T) (cfg.A -ᵥ cfg.K) := by
      show Module.Oriented.positiveOrientation.oangle (cfg.T -ᵥ cfg.A) (cfg.K -ᵥ cfg.A) = _
      rw [← neg_vsub_eq_vsub_rev cfg.T cfg.A, ← neg_vsub_eq_vsub_rev cfg.K cfg.A,
        Module.Oriented.positiveOrientation.oangle_neg_left_eq_neg_right, neg_neg]
    rw [e2] at h11
    exact h11
  have h3 : Module.Oriented.positiveOrientation.oangle (cfg.R -ᵥ cfg.K) (cfg.A -ᵥ cfg.T) = 0 ∨
      Module.Oriented.positiveOrientation.oangle (cfg.R -ᵥ cfg.K) (cfg.A -ᵥ cfg.T) = π := by
    rw [← Real.Angle.two_zsmul_eq_zero_iff]
    have h12 : Module.Oriented.positiveOrientation.oangle (cfg.R -ᵥ cfg.K) (cfg.A -ᵥ cfg.T) =
        Module.Oriented.positiveOrientation.oangle (cfg.R -ᵥ cfg.K) (cfg.A -ᵥ cfg.K) -
        Module.Oriented.positiveOrientation.oangle (cfg.A -ᵥ cfg.T) (cfg.A -ᵥ cfg.K) := by
      rw [Module.Oriented.positiveOrientation.oangle_sub_right hRK hAT hAK]
    rw [h12, smul_sub, h1, sub_self]
  have h4 : (Submodule.span ℝ {cfg.R -ᵥ cfg.K}) = Submodule.span ℝ {cfg.A -ᵥ cfg.T} := by
    rcases h3 with h3 | h3
    · rcases Module.Oriented.positiveOrientation.oangle_eq_zero_iff_sameRay.1 h3 with
        h0 | h0 | ⟨r₁, r₂, hr₁, hr₂, hrr⟩
      · exact absurd h0 hRK
      · exact absurd h0 hAT
      · have e1 : (Submodule.span ℝ {cfg.R -ᵥ cfg.K}) = Submodule.span ℝ {r₁ • (cfg.R -ᵥ cfg.K)} :=
          (Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.2 hr₁.ne') _).symm
        have e2 : (Submodule.span ℝ {cfg.A -ᵥ cfg.T}) = Submodule.span ℝ {r₂ • (cfg.A -ᵥ cfg.T)} :=
          (Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.2 hr₂.ne') _).symm
        rw [e1, e2, hrr]
    · obtain ⟨hx0, hy0, hsr⟩ :=
        Module.Oriented.positiveOrientation.oangle_eq_pi_iff_sameRay_neg.1 h3
      rcases hsr with h0 | h0 | ⟨r₁, r₂, hr₁, hr₂, hrr⟩
      · exact absurd h0 hx0
      · exact absurd h0 (neg_ne_zero.2 hy0)
      · have e1 : (Submodule.span ℝ {cfg.R -ᵥ cfg.K}) = Submodule.span ℝ {r₁ • (cfg.R -ᵥ cfg.K)} :=
          (Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.2 hr₁.ne') _).symm
        have e2 : (Submodule.span ℝ {cfg.A -ᵥ cfg.T}) =
            Submodule.span ℝ {r₂ • (-(cfg.A -ᵥ cfg.T))} := by
          rw [Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.2 hr₂.ne') _,
            ← neg_one_smul ℝ (cfg.A -ᵥ cfg.T),
            Submodule.span_singleton_smul_eq isUnit_one.neg _]
        rw [e1, e2, hrr]
  rw [AffineSubspace.affineSpan_pair_parallel_iff_vectorSpan_eq, vectorSpan_pair, vectorSpan_pair]
  have h5 : (Submodule.span ℝ {cfg.K -ᵥ cfg.R}) = Submodule.span ℝ {cfg.T -ᵥ cfg.A} := by
    have span_neg : ∀ x : V, (Submodule.span ℝ {-x}) = Submodule.span ℝ {x} := fun x => by
      rw [← neg_one_smul ℝ x, Submodule.span_singleton_smul_eq isUnit_one.neg _]
    rw [← neg_vsub_eq_vsub_rev cfg.R cfg.K, span_neg, ← neg_vsub_eq_vsub_rev cfg.A cfg.T, span_neg]
    exact h4
  exact h5

/-! ### The second angle chase: twice `∡SKR` equals twice `∡TRA` -/

theorem two_zsmul_oangle_SKR :
    (2 : ℤ) • ∡ cfg.S cfg.K cfg.R = (2 : ℤ) • ∡ cfg.T cfg.R cfg.A := by
  calc (2 : ℤ) • ∡ cfg.S cfg.K cfg.R = (2 : ℤ) • ∡ cfg.S cfg.J cfg.R :=
      Sphere.two_zsmul_oangle_eq cfg.hSΩ cfg.hKΩ cfg.hJΩ cfg.R_mem_Ω
        cfg.K_ne_S cfg.K_ne_R cfg.hJS cfg.hJR
    _ = (2 : ℤ) • ∡ cfg.S cfg.R cfg.A := cfg.two_zsmul_oangle_SRA.symm
    _ = (2 : ℤ) • ∡ cfg.T cfg.R cfg.A := by
        rw [Wbtw.oangle_eq_left cfg.wbtw_RST cfg.hRS.symm]

/-! ### The sign of `∡SKR` equals the sign of `∡TRA` -/

theorem sign_SKR : (∡ cfg.S cfg.K cfg.R).sign = (∡ cfg.T cfg.R cfg.A).sign := by
  have s1 : (∡ cfg.S cfg.K cfg.R).sign = -(∡ cfg.S cfg.J cfg.R).sign :=
    AffineSubspace.SOppSide.oangle_sign_eq_neg
      (left_mem_affineSpan_pair ℝ cfg.S cfg.R) (right_mem_affineSpan_pair ℝ cfg.S cfg.R)
      ((Set.pair_comm cfg.R cfg.S ▸ cfg.hPc).symm)
  have s2 : (∡ cfg.S cfg.J cfg.R).sign = -(∡ cfg.S cfg.R cfg.A).sign := by
    have h1 : (∡ cfg.S cfg.J cfg.R).sign = (∡ cfg.J cfg.R cfg.S).sign :=
      (oangle_rotate_sign cfg.S cfg.J cfg.R).symm
    have h2 : (∡ cfg.J cfg.R cfg.S).sign = -(∡ cfg.S cfg.R cfg.J).sign := by
      rw [oangle_rev, Real.Angle.sign_neg]
    have h3 : (∡ cfg.S cfg.R cfg.J).sign = (∡ cfg.R cfg.J cfg.S).sign :=
      (oangle_rotate_sign cfg.S cfg.R cfg.J).symm
    have h4 : (∡ cfg.R cfg.J cfg.S).sign = (∡ cfg.R cfg.A cfg.S).sign :=
      AffineSubspace.SSameSide.oangle_sign_eq (left_mem_affineSpan_pair ℝ _ _)
        (right_mem_affineSpan_pair ℝ _ _) cfg.hPb
    have h5 : (∡ cfg.R cfg.A cfg.S).sign = (∡ cfg.S cfg.R cfg.A).sign :=
      ((oangle_rotate_sign cfg.A cfg.S cfg.R).trans (oangle_rotate_sign cfg.R cfg.A cfg.S)).symm
    rw [h1, h2, h3, h4, h5]
  have e1 : ∡ cfg.S cfg.R cfg.A = ∡ cfg.T cfg.R cfg.A :=
    Wbtw.oangle_eq_left cfg.wbtw_RST cfg.hRS.symm
  rw [s1, s2, neg_neg, e1]

/-! ### Twice `∡KRS` equals twice `∡ATR`, and the signs agree -/

theorem two_zsmul_oangle_KRS :
    (2 : ℤ) • ∡ cfg.K cfg.R cfg.S = (2 : ℤ) • ∡ cfg.A cfg.T cfg.R := by
  have e1 : (2 : ℤ) • ∡ cfg.K cfg.R cfg.S = (2 : ℤ) • ∡ cfg.K cfg.R cfg.T := by
    rw [Wbtw.oangle_eq_right cfg.wbtw_RST cfg.hRS.symm]
  have e2 : (2 : ℤ) • ∡ cfg.K cfg.R cfg.T = (2 : ℤ) • ∡ cfg.A cfg.T cfg.R := by
    apply two_zsmul_oangle_of_parallel (Set.pair_comm cfg.T cfg.A ▸ cfg.parallel_KR_TA)
    have e : line[ℝ, cfg.T, cfg.R] = line[ℝ, cfg.R, cfg.T] := by rw [Set.pair_comm]
    rw [e]
  rw [e1, e2]

theorem sign_KRS : (∡ cfg.K cfg.R cfg.S).sign = (∡ cfg.A cfg.T cfg.R).sign := by
  have e1 : ∡ cfg.K cfg.R cfg.S = ∡ cfg.K cfg.R cfg.T :=
    Wbtw.oangle_eq_right cfg.wbtw_RST cfg.hRS.symm
  have s1 : (∡ cfg.K cfg.R cfg.T).sign = (∡ cfg.T cfg.K cfg.R).sign :=
    ((oangle_rotate_sign cfg.R cfg.T cfg.K).trans (oangle_rotate_sign cfg.K cfg.R cfg.T)).symm
  have s2 : (∡ cfg.T cfg.K cfg.R).sign = -(∡ cfg.R cfg.K cfg.T).sign := by
    rw [oangle_rev, Real.Angle.sign_neg]
  have s3 : (∡ cfg.R cfg.K cfg.T).sign = -(∡ cfg.R cfg.A cfg.T).sign :=
    AffineSubspace.SOppSide.oangle_sign_eq_neg
      (left_mem_affineSpan_pair ℝ cfg.R cfg.S) cfg.T_mem_lineRS cfg.sOppSide_KA.symm
  have s4 : (∡ cfg.R cfg.A cfg.T).sign = (∡ cfg.A cfg.T cfg.R).sign :=
    (oangle_rotate_sign cfg.R cfg.A cfg.T).symm
  rw [e1, s1, s2, s3, neg_neg, s4]

/-! ### The mod-`2π` versions of the three angle equalities -/

theorem oangle_RKA : ∡ cfg.R cfg.K cfg.A = ∡ cfg.T cfg.A cfg.K :=
  oangle_eq_of_two_zsmul_oangle_eq_of_sign_eq cfg.two_zsmul_oangle_RKA
    cfg.sign_RKA cfg.sign_RKA_ne

theorem oangle_SKR : ∡ cfg.S cfg.K cfg.R = ∡ cfg.T cfg.R cfg.A :=
  oangle_eq_of_two_zsmul_oangle_eq_of_sign_eq cfg.two_zsmul_oangle_SKR
    cfg.sign_SKR cfg.sign_SKR_ne

theorem oangle_KRS : ∡ cfg.K cfg.R cfg.S = ∡ cfg.A cfg.T cfg.R :=
  oangle_eq_of_two_zsmul_oangle_eq_of_sign_eq cfg.two_zsmul_oangle_KRS
    cfg.sign_KRS cfg.sign_KRS_ne

/-! ### `R -ᵥ K` and `A -ᵥ T` are on the same ray -/

theorem sameRay : SameRay ℝ (cfg.R -ᵥ cfg.K) (cfg.A -ᵥ cfg.T) := by
  have hRK : cfg.R -ᵥ cfg.K ≠ 0 := vsub_ne_zero.2 cfg.K_ne_R.symm
  have hAK : cfg.A -ᵥ cfg.K ≠ 0 := vsub_ne_zero.2 cfg.A_ne_K
  have hAT : cfg.A -ᵥ cfg.T ≠ 0 := vsub_ne_zero.2 cfg.A_ne_T
  have h11 : Module.Oriented.positiveOrientation.oangle (cfg.R -ᵥ cfg.K) (cfg.A -ᵥ cfg.K) =
      Module.Oriented.positiveOrientation.oangle (cfg.A -ᵥ cfg.T) (cfg.A -ᵥ cfg.K) := by
    have h12 := cfg.oangle_RKA
    have e2 : ∡ cfg.T cfg.A cfg.K =
        Module.Oriented.positiveOrientation.oangle (cfg.A -ᵥ cfg.T) (cfg.A -ᵥ cfg.K) := by
      show Module.Oriented.positiveOrientation.oangle (cfg.T -ᵥ cfg.A) (cfg.K -ᵥ cfg.A) = _
      rw [← neg_vsub_eq_vsub_rev cfg.T cfg.A, ← neg_vsub_eq_vsub_rev cfg.K cfg.A,
        Module.Oriented.positiveOrientation.oangle_neg_left_eq_neg_right, neg_neg]
    rw [e2] at h12
    exact h12
  have h1 : Module.Oriented.positiveOrientation.oangle (cfg.R -ᵥ cfg.K) (cfg.A -ᵥ cfg.T) = 0 := by
    have h13 : Module.Oriented.positiveOrientation.oangle (cfg.R -ᵥ cfg.K) (cfg.A -ᵥ cfg.T) =
        Module.Oriented.positiveOrientation.oangle (cfg.R -ᵥ cfg.K) (cfg.A -ᵥ cfg.K) -
        Module.Oriented.positiveOrientation.oangle (cfg.A -ᵥ cfg.T) (cfg.A -ᵥ cfg.K) := by
      rw [Module.Oriented.positiveOrientation.oangle_sub_right hRK hAT hAK]
    rw [h13, h11, sub_self]
  exact Module.Oriented.positiveOrientation.oangle_eq_zero_iff_sameRay.1 h1

/-! ### The similarity of triangles `SKR` and `ART` -/

theorem angle_SKR : ∠ cfg.S cfg.K cfg.R = ∠ cfg.A cfg.R cfg.T := by
  rw [angle_eq_abs_oangle_toReal cfg.K_ne_S.symm cfg.K_ne_R.symm, cfg.oangle_SKR,
    ← angle_eq_abs_oangle_toReal cfg.R_ne_T.symm cfg.hAR, angle_comm]

theorem angle_KRS : ∠ cfg.K cfg.R cfg.S = ∠ cfg.R cfg.T cfg.A := by
  rw [angle_eq_abs_oangle_toReal cfg.K_ne_R cfg.hRS.symm, cfg.oangle_KRS,
    ← angle_eq_abs_oangle_toReal cfg.A_ne_T cfg.R_ne_T, angle_comm]

theorem similar_SKR_ART : ![cfg.S, cfg.K, cfg.R] ∼ ![cfg.A, cfg.R, cfg.T] :=
  similar_of_angle_angle cfg.not_collinear_SKR cfg.angle_SKR cfg.angle_KRS

theorem ratio_KR_TA :
    dist cfg.K cfg.R * dist cfg.A cfg.T = dist cfg.S cfg.R * dist cfg.R cfg.T := by
  obtain ⟨r, _hr0, hr⟩ := cfg.similar_SKR_ART
  have d1 : dist cfg.K cfg.R = (r : ℝ) * dist cfg.R cfg.T := by
    have e := hr 1 2
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons, edist_dist] at e
    have e2 := congrArg ENNReal.toReal e
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal dist_nonneg, ENNReal.toReal_ofReal dist_nonneg,
      ENNReal.coe_toReal] at e2
  have d2 : dist cfg.S cfg.R = (r : ℝ) * dist cfg.A cfg.T := by
    have e := hr 0 2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons, edist_dist] at e
    have e2 := congrArg ENNReal.toReal e
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal dist_nonneg, ENNReal.toReal_ofReal dist_nonneg,
      ENNReal.coe_toReal] at e2
  rw [d1, d2]
  ring

/-! ### The key metric identity `KT² = KA² - AR²` -/

theorem dist_KT_sq : dist cfg.K cfg.T ^ 2 = dist cfg.K cfg.A ^ 2 - dist cfg.A cfg.R ^ 2 := by
  obtain ⟨c, hc0, hcv⟩ : ∃ c : ℝ, 0 < c ∧ cfg.A -ᵥ cfg.T = c • (cfg.R -ᵥ cfg.K) := by
    rcases cfg.sameRay with h0 | h0 | ⟨r₁, r₂, hr₁, hr₂, hrr⟩
    · exact absurd h0 (vsub_ne_zero.2 cfg.K_ne_R.symm)
    · exact absurd h0 (vsub_ne_zero.2 cfg.A_ne_T)
    · refine ⟨r₁ / r₂, div_pos hr₁ hr₂, ?_⟩
      have h2 : cfg.A -ᵥ cfg.T = r₂⁻¹ • (r₁ • (cfg.R -ᵥ cfg.K)) := by
        rw [hrr, inv_smul_smul₀ hr₂.ne']
      rw [h2, smul_smul, mul_comm r₂⁻¹ r₁, ← div_eq_mul_inv]
  have hdAT : dist cfg.A cfg.T = c * dist cfg.R cfg.K := by
    rw [dist_eq_norm_vsub V, hcv, norm_smul, Real.norm_eq_abs, abs_of_pos hc0,
      ← dist_eq_norm_vsub V]
  have hdRT : dist cfg.R cfg.T = 2 * dist cfg.R cfg.S := by
    have h1 : dist cfg.S cfg.R = dist cfg.S cfg.T := by
      rw [cfg.hT, dist_midpoint_left, dist_midpoint_right]
    have h2 := cfg.wbtw_RST.dist_add_dist
    have h3 : dist cfg.R cfg.S = dist cfg.S cfg.R := dist_comm _ _
    linarith
  have hck : c * (dist cfg.R cfg.K) ^ 2 = 2 * (dist cfg.R cfg.S) ^ 2 := by
    calc c * (dist cfg.R cfg.K) ^ 2 = (c * dist cfg.R cfg.K) * dist cfg.R cfg.K := by ring
      _ = dist cfg.A cfg.T * dist cfg.R cfg.K := by rw [hdAT]
      _ = dist cfg.K cfg.R * dist cfg.A cfg.T := by
        rw [dist_comm cfg.A cfg.T, dist_comm cfg.K cfg.R]
        exact mul_comm _ _
      _ = dist cfg.S cfg.R * dist cfg.R cfg.T := cfg.ratio_KR_TA
      _ = 2 * (dist cfg.R cfg.S) ^ 2 := by rw [hdRT, dist_comm cfg.S cfg.R]; ring
  have hT2 : cfg.T -ᵥ cfg.R = (2 : ℝ) • (cfg.S -ᵥ cfg.R) := by
    rw [cfg.hT, midpoint_vsub_left, ← mul_smul, show (2 : ℝ) * ⅟2 = 1 by norm_num, one_smul]
  have hv1 : cfg.K -ᵥ cfg.T = (cfg.K -ᵥ cfg.R) - (2 : ℝ) • (cfg.S -ᵥ cfg.R) := by
    rw [← hT2]
    exact (vsub_sub_vsub_cancel_right cfg.K cfg.T cfg.R).symm
  have hv2 : cfg.A -ᵥ cfg.R = (2 : ℝ) • (cfg.S -ᵥ cfg.R) - c • (cfg.K -ᵥ cfg.R) := by
    rw [← vsub_add_vsub_cancel cfg.A cfg.T cfg.R, hcv, hT2, ← neg_vsub_eq_vsub_rev cfg.R cfg.K,
      smul_neg]
    abel
  have hv3 : cfg.K -ᵥ cfg.A = (1 + c) • (cfg.K -ᵥ cfg.R) - (2 : ℝ) • (cfg.S -ᵥ cfg.R) := by
    rw [← vsub_sub_vsub_cancel_right cfg.K cfg.A cfg.R, hv2, add_smul, one_smul]
    abel
  have hckn : c * ‖cfg.K -ᵥ cfg.R‖ ^ 2 = 2 * ‖cfg.S -ᵥ cfg.R‖ ^ 2 := by
    have e1 : ‖cfg.R -ᵥ cfg.K‖ = ‖cfg.K -ᵥ cfg.R‖ := by
      rw [← neg_vsub_eq_vsub_rev cfg.R cfg.K, norm_neg]
    have e2 : dist cfg.R cfg.K = ‖cfg.K -ᵥ cfg.R‖ := by rw [dist_eq_norm_vsub V, e1]
    have e3 : dist cfg.R cfg.S = ‖cfg.S -ᵥ cfg.R‖ := by
      rw [dist_eq_norm_vsub V, ← neg_vsub_eq_vsub_rev cfg.R cfg.S, norm_neg]
    rw [e2, e3] at hck
    exact hck
  rw [dist_eq_norm_vsub V, dist_eq_norm_vsub V, dist_eq_norm_vsub V, hv1, hv3, hv2]
  have hc1 : (0 : ℝ) < 1 + c := by linarith
  simp only [norm_sub_sq_real, real_inner_smul_left, real_inner_smul_right, norm_smul,
    Real.norm_eq_abs, abs_of_pos hc1, abs_of_pos hc0, abs_of_pos (show (0:ℝ) < 2 by norm_num),
    real_inner_comm]
  linear_combination (-2 : ℝ) * hckn

/-! ### The final result -/

theorem result_oriented : cfg.Γ.IsTangentAt cfg.T line[ℝ, cfg.K, cfg.T] := by
  have hAline : cfg.A ∈ line[ℝ, cfg.J, cfg.K] :=
    cfg.hcol.mem_affineSpan_of_mem_of_ne (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
      (Set.mem_insert _ _) cfg.hKJ.symm
  have hKline : cfg.K ∈ line[ℝ, cfg.A, cfg.J] :=
    cfg.hcol.mem_affineSpan_of_mem_of_ne (Set.mem_insert _ _)
      (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))) cfg.A_ne_J
  have hts : dist cfg.A cfg.R ^ 2 = dist cfg.A cfg.J * dist cfg.A cfg.K := by
    apply Sphere.dist_sq_eq_mul_dist_of_tangent_and_secant cfg.hJΩ cfg.hKΩ hAline
    rw [Set.pair_comm]
    exact cfg.hAℓ
  have hA2 : cfg.A = cfg.Γ.secondInter cfg.J (cfg.K -ᵥ cfg.J) := by
    rcases (Sphere.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair cfg.hJΓ hAline).2
      cfg.hAΓ with h | h
    · exact absurd h cfg.A_ne_J
    · exact h
  have hKout : cfg.Γ.radius ≤ dist cfg.K cfg.Γ.center := by
    by_contra! hc
    have hw := Sphere.wbtw_secondInter cfg.hJΓ hc.le
    rw [← hA2] at hw
    have d1 := hw.dist_add_dist
    have d2 := cfg.hPa.wbtw.dist_add_dist
    rw [dist_comm cfg.K cfg.A, dist_comm cfg.J cfg.A] at d1
    have hJK : 0 < dist cfg.J cfg.K := dist_pos.2 cfg.hKJ.symm
    linarith
  have hpow : cfg.Γ.power cfg.K = dist cfg.K cfg.A * dist cfg.K cfg.J :=
    (Sphere.mul_dist_eq_power_of_radius_le_dist_center (Sphere.radius_nonneg_of_mem cfg.hAΓ)
      hKline cfg.hAΓ cfg.hJΓ hKout).symm
  have hKJdist : dist cfg.K cfg.J = dist cfg.A cfg.K - dist cfg.A cfg.J := by
    have d2 := cfg.hPa.wbtw.dist_add_dist
    rw [dist_comm cfg.K cfg.J]
    linarith
  have hfinal : dist cfg.K cfg.T ^ 2 = cfg.Γ.power cfg.K := by
    rw [hpow, hKJdist, dist_comm cfg.K cfg.A]
    have h1 := cfg.dist_KT_sq
    rw [dist_comm cfg.K cfg.A] at h1
    rw [h1, hts]
    ring
  exact Sphere.isTangentAt_of_dist_sq_eq_power cfg.hTΓ hfinal

end Imo2017P4Cfg

end Oriented

namespace Imo2017P4Cfg

variable (cfg : Imo2017P4Cfg V Pt)

theorem result [Fact (finrank ℝ V = 2)] : cfg.Γ.IsTangentAt cfg.T line[ℝ, cfg.K, cfg.T] := by
  have := someOrientation V
  exact cfg.result_oriented

end Imo2017P4Cfg

end

snip end

problem imo2017_p4 [Fact (finrank ℝ V = 2)] (Ω Γ : Sphere Pt) (R S J T A K : Pt)
    (hSΩ : S ∈ Ω) (hRS : R ≠ S) (hdiam : ∠ R Ω.center S ≠ π)
    (hT : S = midpoint ℝ R T) (hJΩ : J ∈ Ω) (hJR : J ≠ R) (hJS : J ≠ S)
    (hJside : line[ℝ, R, S].SOppSide J Ω.center)
    (hJΓ : J ∈ Γ) (hSΓ : S ∈ Γ) (hTΓ : T ∈ Γ) (hAΓ : A ∈ Γ)
    (hAℓ : Ω.IsTangentAt R line[ℝ, R, A]) (hAR : A ≠ R)
    (hB : Γ.secondInter A (R -ᵥ A) ≠ A)
    (hcloser : dist A R < dist (Γ.secondInter A (R -ᵥ A)) R)
    (hKΩ : K ∈ Ω) (hKJ : K ≠ J) (hcol : Collinear ℝ ({A, J, K} : Set Pt))
    (hPa : Sbtw ℝ A J K)
    (hPb : line[ℝ, R, S].SSameSide A J)
    (hPc : line[ℝ, R, S].SOppSide K J)
    (hPe : line[ℝ, R, J].SSameSide K S)
    (hPf : line[ℝ, T, J].SOppSide S A) :
    Γ.IsTangentAt T line[ℝ, K, T] :=
  (⟨Ω, Γ, R, S, J, T, A, K, hSΩ, hRS, hdiam, hT, hJΩ, hJR, hJS, hJside, hJΓ, hSΓ, hTΓ,
    hAΓ, hAℓ, hAR, hB, hcloser, hKΩ, hKJ, hcol, hPa, hPb, hPc, hPe, hPf⟩ :
      Imo2017P4Cfg V Pt).result

end Imo2017P4
