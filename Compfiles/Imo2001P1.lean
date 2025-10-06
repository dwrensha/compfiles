/-
Copyright (c) 2024 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw, Benpigchu
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Basic
import Mathlib.Geometry.Euclidean.Circumcenter
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Geometry.Euclidean.Angle.Sphere
import Mathlib.Geometry.Euclidean.Altitude

import ProblemExtraction

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 2001, Problem 1

Let ABC be an acute-angled triangle with O as its circumcenter. Let P
on line BC be the foot of the altitude from A. Assume that
∠BCA ≥ ∠ABC + 30°. Prove that ∠CAB + ∠COP < 90°.
-/

namespace Imo2001P1

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

lemma aux₀ {x y : ℝ} (h : ∃ k : ℤ, x = y * k)
  (hx : |x| < y)
  : x = 0 := by
    rcases h with ⟨k, hk⟩
    rw [hk]
    apply mul_eq_zero_of_right
    simp
    contrapose! hx
    rw [hk, abs_mul]
    have h₁ : (1 : ℝ) ≤ |↑k| := by
      rw [← Int.cast_one, ← Int.cast_abs, Int.cast_le]
      exact Int.one_le_abs hx
    calc y
        ≤ |y| := by exact le_abs_self y
      _ = |y| * 1 := by exact (mul_one |y|).symm
      _ ≤ |y| * |↑k| := by exact mul_le_mul_of_nonneg_left h₁ (abs_nonneg y)

lemma aux₁ {x y z : ℝ}
  (hx' : 0 ≤ x) (hy' : y ≤ 0)
  (hx : |x| < z) (hy : |y| < z)
  : |x + y| < z := by
    rw [abs_lt]
    constructor
    · calc -z
          _ < y := by exact (abs_lt.mp hy).left
          _ = 0 + y := by exact (zero_add y).symm
          _ ≤ x + y := by exact add_le_add_right hx' y
    · calc x + y
        _ ≤ x + 0 := by exact add_le_add_left hy' x
        _ = x := by exact add_zero x
        _ < z := by exact (abs_lt.mp hx).right

lemma aux₂ {x y z : ℝ} (h : |x + y| = z)
  (hx : |x| < z) (hy : |y| < z)
  : |x| + |y| = z := by
    symm
    rw [← h, abs_add_eq_add_abs_iff]
    contrapose! h
    apply ne_of_lt
    by_cases hx' : 0 ≤ x
    · have hy' := h.left hx'
      exact aux₁ hx' (le_of_lt hy') hx hy
    · push_neg at hx'
      have hy' := h.right (le_of_lt hx')
      rw [add_comm]
      exact aux₁ (le_of_lt hy') (le_of_lt hx') hy hx

lemma aux₃ {a b : Real.Angle} (h : 2 • a + 2 • b = Real.pi)
  (ha : |a.toReal| < Real.pi / 2) (hb : |b.toReal| < Real.pi / 2)
  : |a.toReal| + |b.toReal| = Real.pi / 2 := by
    rw [← Real.Angle.coe_toReal a, ← Real.Angle.coe_toReal b] at h
    set a' := a.toReal
    set b' := b.toReal
    rw [← smul_add] at h
    rw [Real.Angle.two_nsmul_eq_pi_iff, ← Real.Angle.coe_add] at h
    repeat rw [Real.Angle.angle_eq_iff_two_pi_dvd_sub] at h
    have h₁ : |a' + b'| < Real.pi := by
      calc |a' + b'|
          ≤ |a'| + |b'| := by exact abs_add_le a' b'
        _ < Real.pi / 2 + Real.pi / 2 := by exact add_lt_add ha hb
        _ = Real.pi := by ring
    have h₂ : 0 ≤ Real.pi / 2 := by
      apply div_nonneg Real.pi_nonneg
      norm_num
    have h₃ : |a' + b'| + |Real.pi / 2| < 2 * Real.pi := by
      calc |a' + b'| + |Real.pi / 2|
            < Real.pi + |Real.pi / 2| := by exact add_lt_add_right h₁ _
          _ = Real.pi + Real.pi / 2 := by exact (add_right_inj _).mpr (abs_eq_self.mpr h₂)
          _ ≤ Real.pi + Real.pi / 2 + Real.pi / 2 := by exact (le_add_iff_nonneg_right _).mpr h₂
          _ = 2 * Real.pi := by ring
    have h₄ : |a' + b'| = Real.pi / 2 := by
      rw [abs_eq h₂]
      rcases h with pos|neg
      · left
        apply eq_of_sub_eq_zero
        apply aux₀ pos
        calc |a' + b' - Real.pi / 2|
            ≤ |a' + b'| + |Real.pi / 2| := by exact abs_sub _ _
          _ < 2 * Real.pi := by exact h₃
      · right
        apply eq_of_sub_eq_zero
        rw [← neg_div]
        apply aux₀ neg
        rw [neg_div, sub_neg_eq_add]
        calc |a' + b' + Real.pi / 2|
            ≤ |a' + b'| + |Real.pi / 2| := by exact abs_add_le _ _
          _ < 2 * Real.pi := by exact h₃
    exact aux₂ h₄ ha hb

lemma aux₄ {a : Real.Angle} (h : 2 • 2 • a = 0) (ha : |a.toReal| < Real.pi / 2)
  : |a.toReal| = 0 := by
    rw [smul_smul] at h
    have h₁ : 2 * 2 = 4 := by norm_num
    rw [h₁] at h
    rw [← Real.Angle.coe_toReal a] at h
    set a' := a.toReal
    rw [← Real.Angle.coe_nsmul] at h
    rw [Real.Angle.coe_eq_zero_iff] at h
    rcases h with ⟨k, hk⟩
    have h₂ : a' = Real.pi / 2 * k:= by
      calc a'
          = (4 • a') / 4 := by ring
        _ = k • (2 * Real.pi) / 4 := by rw [hk]
        _ = Real.pi / 2 * k := by ring
    rw [abs_eq_zero]
    exact aux₀ ⟨k, h₂⟩ ha

lemma aux₅ {x y z: ℝ} (h : ∃ k : ℤ, x - y = z * k)
  (hz : 0 < z) (hy : |y| ≤ z / 2)
  : |y| ≤ |x| := by
  rcases h with ⟨k, hk⟩
  by_cases h': k = 0
  · rw [h', Int.cast_zero, mul_zero, sub_eq_zero] at hk
    rw [hk]
  · push_neg at h'
    apply le_trans hy
    have h₁ : (1 : ℝ) ≤ |↑k| := by
      rw [← Int.cast_one, ← Int.cast_abs, Int.cast_le]
      exact Int.one_le_abs h'
    rw [sub_eq_iff_eq_add] at hk
    rw [hk]
    rw [le_abs] at *
    rw [abs_le] at *
    rcases h₁ with pos|neg
    · left
      calc z / 2
          = z * 1 + -(z / 2) := by ring
        _ ≤ z * ↑k + y := by
          apply add_le_add
          · rw [mul_le_mul_iff_right₀ hz]
            exact pos
          · exact hy.left
    · right
      calc z / 2
          = z * 1 + -(z / 2) := by ring
        _ ≤ z * (-↑k) + -y := by
            apply add_le_add
            · rw [mul_le_mul_iff_right₀ hz]
              exact neg
            · apply neg_le_neg
              exact hy.right
        _ = -(z * ↑k + y) := by ring

lemma aux₆ {a b c : Real.Angle} (h : a + b = c)
  : |c.toReal| ≤ |a.toReal| + |b.toReal| := by
    rw [← Real.Angle.coe_toReal a] at h
    rw [← Real.Angle.coe_toReal b] at h
    rw [← Real.Angle.coe_toReal c] at h
    set a' := a.toReal
    set b' := b.toReal
    set c' := c.toReal
    rw [← Real.Angle.coe_add] at h
    rw [Real.Angle.angle_eq_iff_two_pi_dvd_sub] at h
    calc |c'|
        ≤ |a' + b'| := by
          apply aux₅ h
          · apply mul_pos
            · norm_num
            · exact Real.pi_pos
          · rw [mul_div_cancel_left₀ Real.pi (by norm_num:(2 : ℝ) ≠ 0)]
            exact Real.Angle.abs_toReal_le_pi c
      _ ≤ |a'| + |b'| := by apply abs_add_le

lemma aux₇ {a : Real.Angle} : Real.sin |a.toReal| = |a.sin| := by
  nth_rw 2 [← Real.Angle.coe_toReal a]
  rw [Real.Angle.sin_coe]
  have ha' := Real.Angle.abs_toReal_le_pi a
  set a' := a.toReal
  rw [abs_le] at ha'
  by_cases ha'': 0 ≤ a'
  · rw [abs_eq_self.mpr ha'']
    symm
    rw [abs_eq_self]
    apply Real.sin_nonneg_of_mem_Icc
    simp
    exact ⟨ha'',ha'.right⟩
  · push_neg at ha''
    rw [abs_eq_neg_self.mpr (le_of_lt ha'')]
    rw [Real.sin_neg]
    symm
    rw [abs_eq_neg_self]
    apply Real.sin_nonpos_of_nonpos_of_neg_pi_le (le_of_lt ha'') ha'.left

structure Imo2001q1Cfg where
  (A B C : EuclideanSpace ℝ (Fin 2))
  (hABC : AffineIndependent ℝ ![A, B, C])
  (hAcuteA : ∠ C A B < Real.pi / 2)
  (hAcuteB : ∠ A B C < Real.pi / 2)
  (hAcuteC : ∠ B C A < Real.pi / 2)
  (hAB : ∠ A B C + Real.pi / 6 ≤ ∠ B C A)

namespace Imo2001q1Cfg

variable (cfg : Imo2001q1Cfg)

def ABC : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2)) :=
  ⟨![cfg.A, cfg.B, cfg.C], cfg.hABC⟩

noncomputable def P : EuclideanSpace ℝ (Fin 2) :=
  cfg.ABC.altitudeFoot 0

noncomputable def O :EuclideanSpace ℝ (Fin 2) :=
  cfg.ABC.circumcenter

lemma A_ne_B : cfg.A ≠ cfg.B := by
    exact cfg.hABC.injective.ne (by decide : (0 : Fin 3) ≠ 1)

lemma A_ne_C : cfg.A ≠ cfg.C := by
    exact cfg.hABC.injective.ne (by decide : (0 : Fin 3) ≠ 2)

lemma C_ne_B : cfg.C ≠ cfg.B := by
  exact cfg.hABC.injective.ne (by decide : (2 : Fin 3) ≠ 1)

lemma CO_circumradius : dist cfg.O cfg.C = cfg.ABC.circumradius := by
  exact dist_circumcenter_eq_circumradius' cfg.ABC 2

lemma C_ne_O : cfg.O ≠ cfg.C := by
  rw [← dist_pos, CO_circumradius]
  exact circumradius_pos cfg.ABC

lemma A_opposite_BC : {cfg.B, cfg.C} = Set.range (cfg.ABC.faceOpposite 0).points := by
  apply Set.eq_of_subset_of_card_le
  · intro x x_in
    simp at *
    rcases x_in with h'|h'
    · use 1
      rw [h']
      simp
      rfl
    · use 2
      rw [h']
      simp
      rfl
  · simp
    calc (Finset.image cfg.ABC.points {0}ᶜ).card
        ≤ ({0}ᶜ : Finset (Fin (2 + 1))).card := by exact Finset.card_image_le
      _ = 2 := by
        rw [Finset.card_compl]
        simp
      _ = ({cfg.B, cfg.C} : Finset _).card := by
        rw [Finset.card_insert_of_notMem, Finset.card_singleton]
        simp
        exact (C_ne_B cfg).symm

lemma PBC_collinear : Collinear ℝ {cfg.P, cfg.B, cfg.C} := by
  apply collinear_insert_of_mem_affineSpan_pair
  rw [A_opposite_BC]
  apply altitudeFoot_mem_affineSpan_faceOpposite

lemma APx_eq : ∀ x ∈ ({cfg.B, cfg.C} : Set _), ∠ cfg.A cfg.P x = Real.pi / 2 := by
  intro x hx
  rw [EuclideanGeometry.angle, ← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two]
  rw [real_inner_comm]
  apply Submodule.IsOrtho.inner_eq (vectorSpan_isOrtho_altitude_direction cfg.ABC 0)
  · have h₁ := A_opposite_BC cfg
    simp at h₁
    apply vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan
    · rw [← h₁]
      exact mem_affineSpan _ hx
    · rw [← h₁]
      exact Collinear.mem_affineSpan_of_mem_of_ne (PBC_collinear cfg) (by simp:_) (by simp:_) (by simp:_) (C_ne_B cfg).symm
  · apply vsub_mem_vectorSpan _ (mem_altitude cfg.ABC 0) (altitudeFoot_mem_altitude cfg.ABC 0)

lemma APC_eq : ∠ cfg.A cfg.P cfg.C = Real.pi / 2 := by
  apply APx_eq
  simp

lemma APB_eq : ∠ cfg.A cfg.P cfg.B = Real.pi / 2 := by
  apply APx_eq
  simp

lemma PC_eq : dist cfg.P cfg.C = dist cfg.C cfg.A * Real.cos (∠ cfg.A cfg.C cfg.P) := by
  symm
  rw [mul_comm, angle_comm, dist_comm cfg.C cfg.A, dist_comm cfg.P cfg.C]
  exact cos_angle_mul_dist_of_angle_eq_pi_div_two (APC_eq cfg)

lemma non_sbtw_BCP : ¬Sbtw ℝ cfg.B cfg.C cfg.P := by
  intro h
  have h₁ := h.angle₁₂₃_eq_pi
  contrapose! h₁
  apply ne_of_lt
  have h₂ := oangle_add (C_ne_B cfg).symm (A_ne_C cfg) h.ne_right.symm
  have h₃ := angle_le_pi_div_two_of_angle_eq_pi_div_two (APC_eq cfg)
  calc ∠ cfg.B cfg.C cfg.P
      ≤ ∠ cfg.B cfg.C cfg.A + ∠ cfg.P cfg.C cfg.A := by
        rw [angle_comm cfg.P cfg.C cfg.A]
        rw [angle_eq_abs_oangle_toReal (C_ne_B cfg).symm h.ne_right.symm]
        rw [angle_eq_abs_oangle_toReal (A_ne_C cfg) h.ne_right.symm]
        rw [angle_eq_abs_oangle_toReal (C_ne_B cfg).symm (A_ne_C cfg)]
        exact aux₆ h₂
    _ < Real.pi / 2 + Real.pi / 2 := by
      apply add_lt_add_of_lt_of_le cfg.hAcuteC h₃
    _ = Real.pi := by ring

lemma wbtw_BPC : Wbtw ℝ cfg.P cfg.B cfg.C ∨ Wbtw ℝ cfg.C cfg.P cfg.B := by
  have h₁ := non_sbtw_BCP cfg
  have h₂ := (PBC_collinear cfg).wbtw_or_wbtw_or_wbtw
  contrapose! h₁
  constructor
  · tauto
  · rcases h₁ with ⟨h_PBC, h_CPB⟩
    constructor
    · contrapose! h_PBC
      rw [h_PBC]
      apply wbtw_self_right
    · contrapose! h_CPB
      rw [h_CPB]
      apply wbtw_self_left

lemma P_ne_C : cfg.P ≠ cfg.C := by
  intro h
  have h₁ := cfg.hAcuteC
  contrapose! h₁
  apply le_of_eq
  rw [← h, angle_comm, APB_eq]

lemma oriented_BCO_CAB : 2 • ∡ cfg.B cfg.C cfg.O + 2 • ∡ cfg.C cfg.A cfg.B = Real.pi := by
  apply Sphere.two_zsmul_oangle_center_add_two_zsmul_oangle_eq_pi
  · apply mem_circumsphere cfg.ABC 2
  · apply mem_circumsphere cfg.ABC 0
  · apply mem_circumsphere cfg.ABC 1
  · exact A_ne_C cfg
  · exact A_ne_B cfg
  · exact C_ne_B cfg

lemma acute_BCO : ∠ cfg.B cfg.C cfg.O < Real.pi / 2 := by
  rw [angle_eq_abs_oangle_toReal (C_ne_B cfg).symm (C_ne_O cfg)]
  apply Sphere.abs_oangle_center_right_toReal_lt_pi_div_two
  · apply mem_circumsphere cfg.ABC 2
  · apply mem_circumsphere cfg.ABC 1

lemma BCO_CAB : ∠ cfg.B cfg.C cfg.O + ∠ cfg.C cfg.A cfg.B = Real.pi / 2 := by
  have h₁ := oriented_BCO_CAB cfg
  have h₂ := acute_BCO cfg
  have h₃ := cfg.hAcuteA
  rw [angle_eq_abs_oangle_toReal (C_ne_B cfg).symm (C_ne_O cfg)] at *
  rw [angle_eq_abs_oangle_toReal (A_ne_C cfg).symm (A_ne_B cfg).symm] at *
  exact aux₃ h₁ h₂ h₃

lemma xCP_eq_xCB : ∀ x, x ≠ cfg.C → ∠ x cfg.C cfg.P = ∠ x cfg.C cfg.B := by
  intro x hx
  have h₁ : ∡ x cfg.C cfg.P = ∡ x cfg.C cfg.B := by
    apply eq_of_sub_eq_zero
    rw [oangle_sub_left hx (C_ne_B cfg).symm (P_ne_C cfg)]
    rw [oangle_eq_zero_iff_wbtw, wbtw_comm]
    exact wbtw_BPC cfg
  rw [angle_eq_abs_oangle_toReal hx (C_ne_B cfg).symm]
  rw [angle_eq_abs_oangle_toReal hx (P_ne_C cfg)]
  rw [h₁]

lemma OCP_eq_OCB : ∠ cfg.O cfg.C cfg.P = ∠ cfg.O cfg.C cfg.B := by
  exact xCP_eq_xCB cfg cfg.O (C_ne_O cfg)

lemma CAB_OCP : ∠ cfg.C cfg.A cfg.B = Real.pi / 2 - ∠ cfg.O cfg.C cfg.P := by
  rw [← BCO_CAB, OCP_eq_OCB, angle_comm cfg.B cfg.C cfg.O]
  ring

lemma oriented_BOC_BAC : ∡ cfg.B cfg.O cfg.C = 2 • ∡ cfg.B cfg.A cfg.C:= by
  apply Sphere.oangle_center_eq_two_zsmul_oangle
  · apply mem_circumsphere cfg.ABC 1
  · apply mem_circumsphere cfg.ABC 0
  · apply mem_circumsphere cfg.ABC 2
  · exact A_ne_B cfg
  · exact A_ne_C cfg

lemma angle_in_ABC_pos (i j k : Fin 3) (h : Function.Injective ![i, j, k])
  : ∠ (cfg.ABC.points i) (cfg.ABC.points j) (cfg.ABC.points k) ≠ 0 := by
  intro h'
  rw [angle_eq_zero_iff_ne_and_wbtw] at h'
  have h₁ : Function.Injective ![j, i, k] := by
    have h' : ![j, i, k] = Function.comp ![i, j, k] ![1, 0, 2]  := by
      ext x
      fin_cases x <;> simp
    rw [h']
    exact Function.Injective.comp h (by decide)
  have h₂ : Function.Injective ![j, k, i] := by
    have h' : ![j, k, i] = Function.comp ![i, j, k] ![1, 2, 0]  := by
      ext x
      fin_cases x <;> simp
    rw [h']
    exact Function.Injective.comp h (by decide)
  have h₃ := AffineIndependent.not_wbtw_of_injective j i k h₁ cfg.ABC.independent
  have h₄ := AffineIndependent.not_wbtw_of_injective j k i h₂ cfg.ABC.independent
  tauto

lemma BOC_non_collinear : ¬Collinear ℝ {cfg.B, cfg.O, cfg.C} := by
  intro h
  rw [← oangle_eq_zero_or_eq_pi_iff_collinear] at h
  rw [oriented_BOC_BAC] at h
  apply Real.Angle.two_zsmul_eq_zero_iff.mpr at h
  have h₁ := cfg.hAcuteA
  rw [angle_comm] at h₁
  rw [angle_eq_abs_oangle_toReal (A_ne_B cfg).symm (A_ne_C cfg).symm] at h₁
  have h₂ := aux₄ h h₁
  rw [←angle_eq_abs_oangle_toReal (A_ne_B cfg).symm (A_ne_C cfg).symm] at h₂
  apply angle_in_ABC_pos cfg (1 : Fin 3) 0 2 (by decide)
  exact h₂

lemma OCP_non_collinear : ¬Collinear ℝ {cfg.P, cfg.C, cfg.O} := by
  intro h
  apply BOC_non_collinear cfg
  have h₁ : cfg.O ∈ affineSpan ℝ {cfg.P, cfg.C} := by
    exact Collinear.mem_affineSpan_of_mem_of_ne h (by simp:_) (by simp:_) (by simp:_) (P_ne_C cfg)
  have h₂ : cfg.B ∈ affineSpan ℝ {cfg.P, cfg.C} := by
    exact Collinear.mem_affineSpan_of_mem_of_ne (PBC_collinear cfg) (by simp:_) (by simp:_) (by simp:_) (P_ne_C cfg)
  have h₃ := collinear_insert_insert_of_mem_affineSpan_pair h₁ h₂
  exact Collinear.subset (by grind:_) (h₃)

lemma ACP_eq_ACB : ∠ cfg.A cfg.C cfg.P = ∠ cfg.A cfg.C cfg.B := by
  exact xCP_eq_xCB cfg cfg.A (A_ne_C cfg)

lemma CA_eq : dist cfg.C cfg.A = 2 * cfg.ABC.circumradius * Real.sin (∠ cfg.A cfg.B cfg.C) := by
  rw [angle_eq_abs_oangle_toReal (A_ne_B cfg) (C_ne_B cfg)]
  rw [aux₇]
  have h₁ : |(∡ cfg.A cfg.B cfg.C).sin| ≠ 0 := by
    rw [abs_ne_zero, Real.Angle.sin_ne_zero_iff]
    constructor
    · intro h'
      rw [oangle_eq_zero_iff_angle_eq_zero (A_ne_B cfg) (C_ne_B cfg)] at h'
      apply angle_in_ABC_pos cfg (0 : Fin 3) 1 2 (by decide)
      exact h'
    · apply oangle_eq_pi_iff_angle_eq_pi.not.mpr
      exact ne_of_lt (lt_trans cfg.hAcuteB (div_two_lt_of_pos Real.pi_pos))
  have h₂ : dist cfg.C cfg.A / |(∡ cfg.A cfg.B cfg.C).sin| = 2 * cfg.ABC.circumradius := by
    rw [circumradius, dist_comm]
    apply Sphere.dist_div_sin_oangle_eq_two_mul_radius
    · apply mem_circumsphere cfg.ABC 0
    · apply mem_circumsphere cfg.ABC 1
    · apply mem_circumsphere cfg.ABC 2
    · exact A_ne_B cfg
    · exact A_ne_C cfg
    · exact (C_ne_B cfg).symm
  calc dist cfg.C cfg.A
      = dist cfg.C cfg.A / |(∡ cfg.A cfg.B cfg.C).sin| * |(∡ cfg.A cfg.B cfg.C).sin| := by
        rw [div_mul_cancel₀]
        exact h₁
    _ = 2 * cfg.ABC.circumradius * |(∡ cfg.A cfg.B cfg.C).sin| := by
      rw [h₂]

lemma four_sin_B_cos_A_le_one : 4 * Real.sin (∠ cfg.A cfg.B cfg.C) * Real.cos (∠ cfg.A cfg.C cfg.B) ≤ 1 := by
  have h₁ : Real.cos (∠ cfg.A cfg.C cfg.B) ≤ Real.cos (∠ cfg.A cfg.B cfg.C + Real.pi / 6) := by
    apply Real.cos_le_cos_of_nonneg_of_le_pi
    · apply add_nonneg (angle_nonneg _ _ _)
      apply div_nonneg Real.pi_nonneg
      norm_num
    · apply angle_le_pi
    · nth_rw 2 [angle_comm]
      exact cfg.hAB
  have h₂ : 0 < Real.sin (∠ cfg.A cfg.B cfg.C) := by
    apply Real.sin_pos_of_mem_Ioo
    simp
    constructor
    · apply lt_of_le_of_ne (angle_nonneg _ _ _)
      symm
      exact angle_in_ABC_pos cfg (0 : Fin 3) 1 2 (by decide)
    · exact lt_trans cfg.hAcuteB (div_two_lt_of_pos Real.pi_pos)
  calc 4 * Real.sin (∠ cfg.A cfg.B cfg.C) * Real.cos (∠ cfg.A cfg.C cfg.B)
      ≤ 4 * Real.sin (∠ cfg.A cfg.B cfg.C) * Real.cos (∠ cfg.A cfg.B cfg.C + Real.pi / 6) := by
        rw [mul_le_mul_iff_right₀]
        · exact h₁
        · apply mul_pos
          · norm_num
          · exact h₂
    _ = 2 * (2 * Real.sin (∠ cfg.A cfg.B cfg.C) * Real.cos (∠ cfg.A cfg.B cfg.C + Real.pi / 6)) := by ring
    _ = 2 * (Real.sin (∠ cfg.A cfg.B cfg.C - (∠ cfg.A cfg.B cfg.C + Real.pi / 6)) + Real.sin (∠ cfg.A cfg.B cfg.C + (∠ cfg.A cfg.B cfg.C + Real.pi / 6))) := by
        rw [Real.two_mul_sin_mul_cos]
    _ = 2 * (Real.sin (- Real.pi / 6) + Real.sin (2 * ∠ cfg.A cfg.B cfg.C + Real.pi / 6)) := by ring_nf
    _ = 2 * (- 1 / 2 + Real.sin (2 * ∠ cfg.A cfg.B cfg.C + Real.pi / 6)) := by
        rw [neg_div, Real.sin_neg, Real.sin_pi_div_six, neg_div]
    _ ≤ 2 * (- 1 / 2 + 1) := by
        rw [mul_le_mul_iff_right₀]
        · rw [add_le_add_iff_left]
          apply Real.sin_le_one
        · norm_num
    _ = 1 := by norm_num

lemma two_mul_PC_le_circumradius : 2 * dist cfg.P cfg.C ≤ cfg.ABC.circumradius := by
  rw [PC_eq, ACP_eq_ACB, CA_eq]
  calc 2 * (2 * circumradius cfg.ABC * Real.sin (∠ cfg.A cfg.B cfg.C) * Real.cos (∠ cfg.A cfg.C cfg.B))
      = circumradius cfg.ABC * (4 * Real.sin (∠ cfg.A cfg.B cfg.C) * Real.cos (∠ cfg.A cfg.C cfg.B)) := by ring
    _ ≤ circumradius cfg.ABC * 1 := by
      rw [mul_le_mul_iff_right₀ (circumradius_pos cfg.ABC)]
      exact four_sin_B_cos_A_le_one cfg
    _ = circumradius cfg.ABC := by ring

lemma PC_lt_PO : dist cfg.P cfg.C < dist cfg.P cfg.O := by
  have h₁ : dist cfg.O cfg.C < dist cfg.O cfg.P + dist cfg.P cfg.C := by
    rw [dist_lt_dist_add_dist_iff]
    intro h'
    apply OCP_non_collinear cfg
    exact Collinear.subset (by grind:_) (h'.collinear)
  calc dist cfg.P cfg.C
      = 2 * dist cfg.P cfg.C - dist cfg.P cfg.C:= by ring
    _ ≤ cfg.ABC.circumradius - dist cfg.P cfg.C := by exact sub_le_sub_right (two_mul_PC_le_circumradius cfg) _
    _ = dist cfg.O cfg.C - dist cfg.P cfg.C := by rw [CO_circumradius]
    _ < dist cfg.O cfg.P + dist cfg.P cfg.C - dist cfg.P cfg.C := by exact sub_lt_sub_right h₁ _
    _ = dist cfg.O cfg.P := by ring
    _ = dist cfg.P cfg.O := by apply dist_comm

lemma COP_le_OCP : ∠ cfg.C cfg.O cfg.P < ∠ cfg.O cfg.C cfg.P := by
  rw [angle_comm cfg.C cfg.O cfg.P, angle_comm cfg.O cfg.C cfg.P]
  rw [angle_lt_iff_dist_lt (OCP_non_collinear cfg)]
  exact PC_lt_PO cfg

theorem result : ∠ cfg.C cfg.A cfg.B + ∠ cfg.C cfg.ABC.circumcenter cfg.P < Real.pi / 2 := by
  rw [CAB_OCP]
  calc Real.pi / 2 - ∠ cfg.O cfg.C cfg.P + ∠ cfg.C cfg.O cfg.P
      < Real.pi / 2 - ∠ cfg.O cfg.C cfg.P + ∠ cfg.O cfg.C cfg.P := by exact add_lt_add_left (COP_le_OCP cfg) _
    _ = Real.pi / 2 := by ring

end Imo2001q1Cfg

snip end

problem imo2001_p1
    (A B C : EuclideanSpace ℝ (Fin 2))
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hAcuteA : ∠ C A B < Real.pi / 2)
    (hAcuteB : ∠ A B C < Real.pi / 2)
    (hAcuteC : ∠ B C A < Real.pi / 2)
    (hAB : ∠ A B C + Real.pi / 6 ≤ ∠ B C A)
    : let ABC : Affine.Triangle _ _ := ⟨![A, B, C], hABC⟩
      let P := ABC.altitudeFoot 0
      ∠ C A B + ∠ C ABC.circumcenter P < Real.pi / 2 := by
  set cfg : Imo2001q1Cfg := ⟨A, B, C, hABC, hAcuteA, hAcuteB, hAcuteC, hAB⟩
  exact cfg.result

end Imo2001P1
