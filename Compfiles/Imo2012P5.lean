/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tenthmascot
-/
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.Geometry.Euclidean.Angle.Sphere
import Mathlib.Geometry.Euclidean.Sphere.Power
import Mathlib.Geometry.Euclidean.Sphere.SecondInter

import ProblemExtraction

problem_file {
  tags := [.Geometry]
}

/-!
# International Mathematical Olympiad 2012, Problem 5

Let `ABC` be a triangle with `∠BCA = 90°`, and let `D` be the foot of the altitude from `C`.
Let `X` be a point in the interior of the segment `CD`. Let `K` be the point on the segment `AX`
such that `BK = BC`. Similarly, let `L` be the point on the segment `BX` such that `AL = AC`.
Let `M` be the point of intersection of `AL` and `BK`.
Show that `MK = ML`.
-/

open Affine EuclideanGeometry Module

open scoped EuclideanGeometry Real

variable (V P : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MetricSpace P] [NormedAddTorsor V P]

snip begin

/-
This section includes lemmas which might be more useful in a general context.
Since such theorems would likely not want `V` and `P` to be explicit,
we put them in this section so they can have implicit `V` and `P`.
-/

section

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MetricSpace P] [NormedAddTorsor V P]

/-- The converse of the **Intersecting Chords Theorem**, stated with `Sbtw`. -/
theorem cospherical_or_collinear_of_mul_dist_eq_mul_dist_of_sbtw
  {a b c d p : P} (h : dist a p * dist b p = dist c p * dist d p)
  (hapb : Sbtw ℝ a p b) (hcpd : Sbtw ℝ c p d) :
    Cospherical {a, b, c, d} ∨ Collinear ℝ {a, b, c, d} := by
  refine em (AffineIndependent ℝ ![d, c, b]) |>.imp
    (fun hΔ => ?_) (fun hΔ => ?_)
  · let Δ : Simplex _ _ _ := ⟨_, hΔ⟩
    let a' := Δ.circumsphere.secondInter b (p -ᵥ b)
    have ha'pb : Sbtw ℝ a' p b := by
      rw [sbtw_comm]
      refine Sphere.sbtw_secondInter (Δ.mem_circumsphere 2) ?_
      have : _ < max (dist (Δ.points 1) _) (dist (Δ.points 0) _) :=
        hcpd.dist_lt_max_dist Δ.circumcenter
      simpa using this
    have h' : Cospherical {a', b, c, d} := by
      refine ⟨Δ.circumcenter, Δ.circumradius, ?_⟩
      change ∀ p ∈ {Δ.circumsphere.secondInter (Δ.points 2) _,
        Δ.points 2, Δ.points 1, Δ.points 0}, p ∈ Δ.circumsphere
      simp [Δ.mem_circumsphere]
    suffices a' = a by exact this ▸ h'
    have := mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_pi h'
      ha'pb.angle₁₂₃_eq_pi hcpd.angle₁₂₃_eq_pi
    rw [← this] at h
    apply mul_right_cancel₀ (dist_ne_zero.mpr hapb.right_ne) at h
    have h_pb_ap := hapb.symm.wbtw.sameRay_vsub
    have h_a'p_pb := ha'pb.symm.wbtw.sameRay_vsub.symm
    have h_a'p_ap := h_a'p_pb.trans h_pb_ap (by simp [hapb.ne_right])
    obtain ⟨r, r', hr, hr', h0⟩ := h_a'p_ap.exists_pos
      (by simp [ha'pb.left_ne]) (by simp [hapb.left_ne])
    have h1 : ‖r • (a' -ᵥ p)‖ = ‖r' • (a -ᵥ p)‖ := congrArg (‖·‖) h0
    replace h1 : r = r' := by
      simpa [norm_smul, ← dist_eq_norm_vsub, ← h,
        hapb.left_ne, abs_of_pos hr, abs_of_pos hr'] using h1
    simpa [h1, smul_right_inj hr'.ne'] using h0
  · rw [← collinear_iff_not_affineIndependent,
      (by grind [Matrix.range_cons, Matrix.range_empty] : Set.range ![d, c, b] = {b, c, d})] at hΔ
    refine collinear_insert_iff_of_mem_affineSpan ?_ |>.mpr hΔ
    have hp : p ∈ affineSpan ℝ {b, c, d} :=
      mem_of_le_of_mem (affineSpan_mono _ (by grind)) hcpd.wbtw.mem_affineSpan
    rw [← affineSpan_insert_eq_affineSpan _ hp]
    exact mem_of_le_of_mem (affineSpan_mono _ (by grind)) hapb.left_mem_affineSpan

end

snip end

namespace Imo2012P5

snip begin

/-
We follow the standard solution.
Let `ωA` be the circle with center `A` passing through `C` and `L`, and define `ωB` similarly.
Suppose that lines `AX` and `BX` intersect `ωB` and `ωA` again at `K'` and `L'`.
Then we show that `K`, `K'`, `L`, `L'` are concyclic,
and that lines `MK` and `ML` are tangent to this circle, yielding `MK = ML`.
-/

/-
We formalize `D` being the foot of the `C`-altitude literally
with `Simplex.altitudeFoot`, even though informally we might express this
as `D` being the projection from `C` to line `AB`, which would be easier to work with.
This equivalence is proved early on as `Imo2012P5Cfg.D_eq_orthogonalProjection`.
-/

section

/-- A configuration satisfying the conditions of the problem. -/
structure Imo2012P5Cfg where
  {A B C D X K L M : P}
  affineIndependent_ABC : AffineIndependent ℝ ![A, B, C]
  angle_BCA : ∠ B C A = π / 2
  D_eq_altitudeFoot : D = Simplex.altitudeFoot ⟨_, affineIndependent_ABC⟩ 2
  sbtw_CXD : Sbtw ℝ C X D
  wbtw_AKX : Wbtw ℝ A K X
  BK_eq_BC : dist B K = dist B C
  wbtw_BLX : Wbtw ℝ B L X
  AL_eq_AC : dist A L = dist A C
  M_mem_inf_AL_BK : M ∈ line[ℝ, A, L] ⊓ line[ℝ, B, K]

end

namespace Imo2012P5Cfg

/-
We make `V` and `P` implicit here to reduce unnecessary named arguments
in definitions such as `K'`.
-/
variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MetricSpace P] [NormedAddTorsor V P]
variable (cfg : Imo2012P5Cfg V P)

/-- The symmetry of the configuration. -/
def symm : Imo2012P5Cfg V P where
  affineIndependent_ABC := cfg.affineIndependent_ABC.comm_left
  angle_BCA := angle_comm cfg.B cfg.C cfg.A ▸ cfg.angle_BCA
  D_eq_altitudeFoot := by
    rw [cfg.D_eq_altitudeFoot]
    have := Simplex.altitudeFoot_reindex ⟨_, cfg.affineIndependent_ABC.comm_left⟩
      ⟨![1, 0, 2], ![1, 0, 2], by decide, by decide⟩
    replace := congrFun this 2
    dsimp at this
    convert this
    ext i
    fin_cases i <;> simp
  sbtw_CXD := cfg.sbtw_CXD
  wbtw_AKX := cfg.wbtw_BLX
  BK_eq_BC := cfg.AL_eq_AC
  wbtw_BLX := cfg.wbtw_AKX
  AL_eq_AC := cfg.BK_eq_BC
  M := cfg.M
  M_mem_inf_AL_BK :=
    inf_comm line[ℝ, cfg.A, cfg.L] line[ℝ, cfg.B, cfg.K] ▸ cfg.M_mem_inf_AL_BK

theorem A_ne_K : cfg.A ≠ cfg.K := by
  intro h
  have BA_eq_BC := h.symm ▸ cfg.BK_eq_BC
  have := dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two _ _ _
    |>.mpr cfg.angle_BCA
  have A_eq_C : cfg.A = cfg.C := by simpa [BA_eq_BC] using this
  exact cfg.affineIndependent_ABC.injective.ne (by decide : (0 : Fin 3) ≠ 2) A_eq_C

theorem B_ne_L : cfg.B ≠ cfg.L :=
  cfg.symm.A_ne_K

theorem D_eq_orthogonalProjection :
    cfg.D = orthogonalProjection line[ℝ, cfg.A, cfg.B] cfg.C := by
  simp_rw [D_eq_altitudeFoot, Simplex.altitudeFoot, Simplex.faceOpposite,
    Simplex.orthogonalProjectionSpan]
  refine orthogonalProjection_congr ?_ rfl
  · simp [(by grind : ({2}ᶜ : Set (Fin 3)) = {0, 1}), Set.image_insert_eq]

/-- The reflection of `C` in line `AB`. -/
noncomputable def C' : P :=
  reflection (line[ℝ, cfg.A, cfg.B]) cfg.C

theorem C'_def : cfg.C' = reflection line[ℝ, cfg.A, cfg.B] cfg.C :=
  rfl

theorem symm_C' : cfg.symm.C' = cfg.C' := by
  change reflection line[ℝ, cfg.B, cfg.A] cfg.C
    = reflection line[ℝ, cfg.A, cfg.B] cfg.C
  simp only [AffineSubspace.affineSpan_pair_comm]

theorem D_eq_midpoint_CC' : cfg.D = midpoint ℝ cfg.C cfg.C' := by
  rw [← midpoint_self ℝ cfg.D, midpoint_eq_midpoint_iff_vsub_eq_vsub,
    D_eq_orthogonalProjection, C'_def, reflection_apply', vadd_vsub]

theorem sbtw_CXC' : Sbtw ℝ cfg.C cfg.X cfg.C' :=
  (cfg.D_eq_midpoint_CC' ▸ wbtw_midpoint ℝ cfg.C cfg.C').trans_sbtw_left cfg.sbtw_CXD

def ωA : Sphere P := ⟨cfg.A, dist cfg.C cfg.A⟩

def ωB : Sphere P := ⟨cfg.B, dist cfg.C cfg.B⟩

theorem C_mem_ωA : cfg.C ∈ cfg.ωA := rfl

theorem C_mem_ωB : cfg.C ∈ cfg.ωB := rfl

theorem C'_mem_ωA : cfg.C' ∈ cfg.ωA := by
  simpa only [dist_comm cfg.A] using
    (dist_reflection_eq_of_mem line[ℝ, cfg.A, cfg.B]
    (left_mem_affineSpan_pair _ _ _) cfg.C)

theorem C'_mem_ωB : cfg.C' ∈ cfg.ωB :=
  cfg.symm_C' ▸ cfg.symm.C'_mem_ωA

theorem XA_lt_radius_ωA : dist cfg.X cfg.A < cfg.ωA.radius := by
  have : dist cfg.C' cfg.A = dist cfg.C cfg.A := cfg.C'_mem_ωA
  simpa [this] using cfg.sbtw_CXC'.dist_lt_max_dist cfg.A

theorem XB_lt_radius_ωB : dist cfg.X cfg.B < cfg.ωB.radius :=
  cfg.symm.XA_lt_radius_ωA

theorem K_mem_ωB : cfg.K ∈ cfg.ωB := by
  change dist cfg.K cfg.B = dist cfg.C cfg.B
  simpa only [dist_comm] using cfg.BK_eq_BC

theorem L_mem_ωA : cfg.L ∈ cfg.ωA :=
  cfg.symm.K_mem_ωB

/-- The second point on line `AX` with `BC = BK'`. -/
noncomputable def K' := cfg.ωB.secondInter cfg.K (cfg.X -ᵥ cfg.K)

/-- The second point on line `BX` with `AC = AL'`. -/
noncomputable def L' := cfg.ωA.secondInter cfg.L (cfg.X -ᵥ cfg.L)

theorem K'_mem_ωB : cfg.K' ∈ cfg.ωB :=
  (Sphere.secondInter_mem _).mpr cfg.K_mem_ωB

theorem L'_mem_ωA : cfg.L' ∈ cfg.ωA :=
  cfg.symm.K'_mem_ωB

theorem sbtw_KXK' : Sbtw ℝ cfg.K cfg.X cfg.K' :=
  Sphere.sbtw_secondInter cfg.K_mem_ωB cfg.XB_lt_radius_ωB

theorem sbtw_LXL' : Sbtw ℝ cfg.L cfg.X cfg.L' :=
  cfg.symm.sbtw_KXK'

theorem sbtw_AKX : Sbtw ℝ cfg.A cfg.K cfg.X :=
  ⟨cfg.wbtw_AKX, cfg.A_ne_K.symm, cfg.sbtw_KXK'.ne_left.symm⟩

theorem sbtw_BLX : Sbtw ℝ cfg.B cfg.L cfg.X :=
  cfg.symm.sbtw_AKX

theorem KX_mul_K'X_eq_CX_mul_C'X :
    dist cfg.K cfg.X * dist cfg.K' cfg.X = dist cfg.C cfg.X * dist cfg.C' cfg.X := by
  refine mul_dist_eq_mul_dist_of_cospherical ⟨cfg.ωB.center, cfg.ωB.radius, ?_⟩
    cfg.sbtw_KXK'.wbtw.mem_affineSpan cfg.sbtw_CXC'.wbtw.mem_affineSpan
  simp [cfg.K_mem_ωB, cfg.K'_mem_ωB, cfg.C_mem_ωB, cfg.C'_mem_ωB]

theorem LX_mul_L'X_eq_CX_mul_C'X :
    dist cfg.L cfg.X * dist cfg.L' cfg.X = dist cfg.C cfg.X * dist cfg.C' cfg.X :=
  cfg.symm_C' ▸ cfg.symm.KX_mul_K'X_eq_CX_mul_C'X

theorem KX_mul_K'X_eq_LX_mul_L'X :
    dist cfg.K cfg.X * dist cfg.K' cfg.X = dist cfg.L cfg.X * dist cfg.L' cfg.X :=
  cfg.KX_mul_K'X_eq_CX_mul_C'X.trans cfg.LX_mul_L'X_eq_CX_mul_C'X.symm

theorem ωA_IsTangentAt_CB : cfg.ωA.IsTangentAt cfg.C line[ℝ, cfg.C, cfg.B] :=
  Sphere.IsTangentAt_of_angle_eq_pi_div_two cfg.angle_BCA cfg.C_mem_ωA

theorem ωB_IsTangentAt_CA : cfg.ωB.IsTangentAt cfg.C line[ℝ, cfg.C, cfg.A] :=
  cfg.symm.ωA_IsTangentAt_CB

theorem sbtw_AKK' : Sbtw ℝ cfg.A cfg.K cfg.K' :=
  cfg.sbtw_AKX.trans_expand_left cfg.sbtw_KXK'

theorem sbtw_BLL' : Sbtw ℝ cfg.B cfg.L cfg.L' :=
  cfg.symm.sbtw_AKK'

theorem A_mem_line_KK' : cfg.A ∈ line[ℝ, cfg.K, cfg.K'] := by
  rw [AffineSubspace.affineSpan_pair_comm]
  exact cfg.sbtw_AKK'.left_mem_affineSpan

theorem B_mem_line_LL' : cfg.B ∈ line[ℝ, cfg.L, cfg.L'] :=
  cfg.symm.A_mem_line_KK'

theorem AC_sq_eq_AK_mul_AK' : dist cfg.A cfg.C ^ 2 = dist cfg.A cfg.K * dist cfg.A cfg.K' := by
  refine Sphere.dist_sq_eq_mul_dist_of_tangent_and_secant
    cfg.K_mem_ωB cfg.K'_mem_ωB cfg.A_mem_line_KK' ?_
  rw [AffineSubspace.affineSpan_pair_comm]
  exact cfg.ωB_IsTangentAt_CA

theorem BC_sq_eq_BL_mul_BL' : dist cfg.B cfg.C ^ 2 = dist cfg.B cfg.L * dist cfg.B cfg.L' :=
  cfg.symm.AC_sq_eq_AK_mul_AK'

theorem AL_sq_eq_AK_mul_AK' : dist cfg.A cfg.L ^ 2 = dist cfg.A cfg.K * dist cfg.A cfg.K' :=
  cfg.AL_eq_AC.symm ▸ cfg.AC_sq_eq_AK_mul_AK'

theorem BK_sq_eq_BL_mul_BL' : dist cfg.B cfg.K ^ 2 = dist cfg.B cfg.L * dist cfg.B cfg.L' :=
  cfg.symm.AL_sq_eq_AK_mul_AK'

theorem not_collinear_ABX : ¬Collinear ℝ {cfg.A, cfg.B, cfg.X} := by
  intro h
  rw [← collinear_insert_iff_of_mem_affineSpan (p := cfg.D),
    ← collinear_insert_iff_of_mem_affineSpan (p := cfg.C)] at h
  · have := h.subset (by grind : {cfg.C, cfg.B, cfg.A} ⊆ _)
    rw [(by simp : {cfg.C, cfg.B, cfg.A} = Set.range ![cfg.A, cfg.B, cfg.C]),
      collinear_iff_not_affineIndependent] at this
    exact this cfg.affineIndependent_ABC
  · exact mem_of_le_of_mem (affineSpan_mono _ (by grind)) cfg.sbtw_CXD.left_mem_affineSpan
  · have : cfg.D ∈ line[ℝ, cfg.A, cfg.B] := by
      rw [cfg.D_eq_orthogonalProjection]
      exact orthogonalProjection_mem _
    exact mem_of_le_of_mem (affineSpan_mono _ (by grind)) this

theorem cospherical_KK'LL' : Cospherical {cfg.K, cfg.K', cfg.L, cfg.L'} := by
  refine cospherical_or_collinear_of_mul_dist_eq_mul_dist_of_sbtw
    cfg.KX_mul_K'X_eq_LX_mul_L'X cfg.sbtw_KXK' cfg.sbtw_LXL'
    |>.elim id (fun h => False.elim ?_)
  rw [← collinear_insert_iff_of_mem_affineSpan (p := cfg.A),
    ← collinear_insert_iff_of_mem_affineSpan (p := cfg.B),
    ← collinear_insert_iff_of_mem_affineSpan (p := cfg.X)] at h
  · exact cfg.not_collinear_ABX <| h.subset (by grind)
  · exact mem_of_le_of_mem (affineSpan_mono _ (by grind)) cfg.sbtw_KXK'.wbtw.mem_affineSpan
  · exact mem_of_le_of_mem (affineSpan_mono _ (by grind)) cfg.sbtw_BLL'.left_mem_affineSpan
  · exact mem_of_le_of_mem (affineSpan_mono _ (by grind)) cfg.sbtw_AKK'.left_mem_affineSpan

theorem exists_sphere_supset_KK'LL' : ∃ (s : Sphere P),
    {cfg.K, cfg.K', cfg.L, cfg.L'} ⊆ Metric.sphere s.center s.radius :=
  cospherical_iff_exists_sphere.mp cfg.cospherical_KK'LL'

/-
Here, we would like to extract a sphere `s` containing `K`, `K'`, `L`, `L'`,
and complete the rest of the solution using this sphere.
However, trying to do that directly means that `s` would not be dual to itself,
so we wouldn't be able to get dual results for free.

While we could simply copy the dual proofs over manually,
we instead pass in the sphere as a hypothesis, and only eliminate it at the end.
We create `SphereWithKK'LL'` to contain this data.
-/

/-- A sphere containing `K`, `K'`, `L`, `L'`. -/
structure SphereWithKK'LL' (s : Sphere P) where
  K_mem : cfg.K ∈ s
  K'_mem : cfg.K' ∈ s
  L_mem : cfg.L ∈ s
  L'_mem : cfg.L' ∈ s

theorem exists_sphereWithKK'LL' : ∃ s, cfg.SphereWithKK'LL' s := by
  obtain ⟨s, hs⟩ := cfg.exists_sphere_supset_KK'LL'
  change ∀ x ∈ _, x ∈ s at hs
  refine ⟨s, ?_, ?_, ?_, ?_⟩
  <;> grind

namespace SphereWithKK'LL'

variable {s} (hs : cfg.SphereWithKK'LL' s)
include hs

theorem symm : cfg.symm.SphereWithKK'LL' s where
  K_mem := hs.L_mem
  K'_mem := hs.L'_mem
  L_mem := hs.K_mem
  L'_mem := hs.K'_mem

theorem isTangentAt_AL : s.IsTangentAt cfg.L line[ℝ, cfg.A, cfg.L] := by
  refine Sphere.isTangentAt_of_dist_sq_eq_power hs.L_mem ?_
  rw [cfg.AL_sq_eq_AK_mul_AK']
  refine Sphere.mul_dist_eq_power_of_radius_le_dist_center
    (s.radius_nonneg_of_mem hs.K_mem) cfg.A_mem_line_KK' hs.K_mem hs.K'_mem ?_
  by_contra! h
  have : Collinear ℝ {cfg.K, cfg.A, cfg.K'} := by
    convert cfg.sbtw_AKK'.wbtw.collinear using 1
    grind
  replace : Sbtw ℝ cfg.K cfg.A cfg.K' :=
    this.sbtw_of_dist_eq_of_dist_lt hs.K_mem h hs.K'_mem cfg.sbtw_KXK'.left_ne_right
  replace : Sbtw ℝ cfg.X cfg.K cfg.K' :=
    cfg.sbtw_AKX.symm.trans_expand_left this
  exact this.not_swap_left cfg.sbtw_KXK'.wbtw

theorem isTangentAt_BK : s.IsTangentAt cfg.K line[ℝ, cfg.B, cfg.K] :=
  hs.symm.isTangentAt_AL

theorem isTangentAt_ML : s.IsTangentAt cfg.L line[ℝ, cfg.M, cfg.L] := by
  have : line[ℝ, cfg.M, cfg.L] ≤ line[ℝ, cfg.A, cfg.L] := by
    rw [← affineSpan_insert_eq_affineSpan _ cfg.M_mem_inf_AL_BK.left]
    exact affineSpan_mono _ (by grind)
  obtain ⟨mem_sphere, _, le_orthradius⟩ := hs.isTangentAt_AL
  exact ⟨mem_sphere, right_mem_affineSpan_pair _ _ _, this.trans le_orthradius⟩

theorem isTangentAt_MK : s.IsTangentAt cfg.K line[ℝ, cfg.M, cfg.K] :=
  hs.symm.isTangentAt_ML

theorem power_M_eq_ML_sq : s.power cfg.M = dist cfg.M cfg.L ^ 2 :=
  hs.isTangentAt_ML.power_eq_dist_sq

theorem power_M_eq_MK_sq : s.power cfg.M = dist cfg.M cfg.K ^ 2 :=
  hs.symm.power_M_eq_ML_sq

theorem MK_eq_ML : dist cfg.M cfg.K = dist cfg.M cfg.L :=
  (sq_eq_sq₀ dist_nonneg dist_nonneg).mp <|
    hs.power_M_eq_MK_sq.symm.trans hs.power_M_eq_ML_sq

end SphereWithKK'LL'

theorem MK_eq_ML : dist cfg.M cfg.K = dist cfg.M cfg.L :=
  cfg.exists_sphereWithKK'LL'.elim (fun _ hs => hs.MK_eq_ML)

end Imo2012P5Cfg

snip end

problem imo2012_p5 [Fact (finrank ℝ V = 2)] {A B C D X K L M : P}
    (affineIndependent_ABC : AffineIndependent ℝ ![A, B, C])
    (angle_BCA : ∠ B C A = π / 2)
    (D_eq_altitudeFoot : D = Simplex.altitudeFoot ⟨_, affineIndependent_ABC⟩ 2)
    (sbtw_CXD : Sbtw ℝ C X D)
    (wbtw_AKX : Wbtw ℝ A K X) (BK_eq_BC : dist B K = dist B C)
    (wbtw_BLX : Wbtw ℝ B L X) (AL_eq_AC : dist A L = dist A C)
    (M_mem_inf_AL_BK : M ∈ line[ℝ, A, L] ⊓ line[ℝ, B, K]) :
    dist M K = dist M L :=
  Imo2012P5Cfg.mk affineIndependent_ABC angle_BCA D_eq_altitudeFoot
    sbtw_CXD wbtw_AKX BK_eq_BC wbtw_BLX AL_eq_AC M_mem_inf_AL_BK |>.MK_eq_ML
