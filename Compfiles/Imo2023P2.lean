/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Benpigchu
-/
import Mathlib

import ProblemExtraction

set_option backward.isDefEq.respectTransparency false

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 2023, Problem 2

Let ABC be an acute-angled triangle with AB < AC.
Let Ω be the circumcircle of ABC.
Let S be the midpoint of the arc CB of Ω containing A.
The perpendicular from A to BC meets BS at D and meets Ω again at E ≠ A.
The line through D parallel to BC meets line BE at L.
Denote the circumcircle of triangle BDL by ω.
Let ω meet Ω again at P ≠ B.
Prove that the line tangent to ω at P meets line BS on the internal angle bisector of ∠BAC.
-/

open Affine Affine.Simplex EuclideanGeometry FiniteDimensional Module

open scoped Affine EuclideanGeometry Real InnerProductSpace

attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

variable (V : Type*) (Pt : Type*)

variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace Pt]

variable [NormedAddTorsor V Pt] [hd2 : Fact (finrank ℝ V = 2)]

variable [Module.Oriented ℝ V (Fin 2)]

namespace Imo2023P2

snip begin

-- alternate version of Real.Angle.abs_toReal_add_abs_toReal_eq_pi_of_two_nsmul_add_eq_zero_of_sign_eq
lemma aux₁ {a b : Real.Angle} (h₁ : a.sign = b.sign) (h₂ : a.sign ≠ 0)
  (h : 2 • (a + b) = 0) : a + b = Real.pi := by
  rw [Real.Angle.two_nsmul_eq_zero_iff] at h
  rcases h with (h|h)
  · contrapose! h₂
    rw [add_comm, add_eq_zero_iff_eq_neg] at h
    rw [h, Real.Angle.sign_neg, SignType.self_eq_neg_iff] at h₁
    exact h₁
  · exact h

-- alternate version of Real.Angle.sign_pi_sub
lemma aux₂ {a b : Real.Angle} (h : a + b = Real.pi) : a.sign = b.sign := by
  rw [← eq_sub_iff_add_eq] at h
  rw [h]
  apply Real.Angle.sign_pi_sub

lemma aux₃ {a b : Real.Angle} (h : a + b = Real.pi) (h' : a.sign ≠ 0)
  : |a.toReal| + |b.toReal| = Real.pi := by
  have h₁ : 2 • (a + b) = 0 := by
    rw [h]
    exact Real.Angle.two_nsmul_coe_pi
  have h₂ := aux₂ h
  exact Real.Angle.abs_toReal_add_abs_toReal_eq_pi_of_two_zsmul_add_eq_zero_of_sign_eq
    h₁ h₂ h'

lemma aux₄ {a b c : Real.Angle}
  (ha : a.sign ≠ 0)
  (hc : c.sign ≠ 0)
  (h : a + b = c)
  (h' : |a.toReal| + |b.toReal| = |c.toReal|)
  : a.sign = c.sign := by
  wlog hc' : c.sign = -1
  · have h_neg_a : (-a).sign ≠ 0 := by
      rw [Real.Angle.sign_neg, SignType.neg_eq_zero_iff.ne]
      exact ha
    have h_neg_c : (-c).sign ≠ 0 := by
      rw [Real.Angle.sign_neg, SignType.neg_eq_zero_iff.ne]
      exact hc
    have h₁ : (-a) + (-b) = (-c) := by
      rw [← h]
      abel
    have h₂ : |(-a).toReal| + |(-b).toReal| = |(-c).toReal| := by simp [h']
    have h'' := SignType.trichotomy c.sign
    have h₃ : (-c).sign = -1 := by
      rw [Real.Angle.sign_neg, neg_eq_iff_eq_neg]
      tauto
    have h''' := this h_neg_a h_neg_c h₁ h₂ h₃
    rw [Real.Angle.sign_neg, Real.Angle.sign_neg, neg_inj] at h'''
    exact h'''
  rw [hc']
  rw [← Real.Angle.coe_toReal a] at h
  rw [← Real.Angle.coe_toReal b] at h
  rw [← Real.Angle.coe_toReal c] at h
  rw [← sub_eq_zero, ← Real.Angle.coe_add, ← Real.Angle.coe_sub, Real.Angle.coe_eq_zero_iff] at h
  rw [← Real.Angle.toReal_neg_iff_sign_neg] at hc' ⊢
  set a' := a.toReal with haa'
  set b' := b.toReal with hbb'
  set c' := c.toReal with hcc'
  rcases h with ⟨n, hn⟩
  by_contra! ha'
  rw [abs_of_neg hc', abs_of_nonneg ha'] at h'
  rw [le_iff_eq_or_lt] at ha'
  rcases ha' with (ha'|ha')
  · rw [haa'] at ha'
    symm at ha'
    rw [Real.Angle.toReal_eq_zero_iff] at ha'
    contrapose! ha
    rw [ha', Real.Angle.sign_zero]
  · rw [sub_eq_add_neg] at hn
    rw [← Left.neg_pos_iff] at hc'
    set c'' := -c' with hc'c''
    contrapose! hn
    by_cases! hn' : 0 < n
    · apply ne_of_gt
      calc a' + b' + c''
        ≤  a' + |b'| + c'' := by
            apply add_le_add_left
            apply add_le_add_right
            apply le_abs_self
      _ = (2 * c'') := by
          rw [h']
          ring
      _ < (2 * π) := by
          rw [mul_lt_mul_iff_of_pos_left (by norm_num)]
          rw [hc'c'', hcc']
          apply neg_lt_of_neg_lt
          apply Real.Angle.neg_pi_lt_toReal
      _ ≤ n • (2 * π) := by
            rw [← Int.add_one_le_iff, zero_add] at hn'
            rw [le_smul_iff_one_le_left (by positivity)]
            exact hn'
    · apply ne_of_lt
      calc n • (2 * π)
        ≤ 0 := by
            apply smul_nonpos_of_nonpos_of_nonneg hn'
            positivity
      _ < 2 * a' + (b' + |b'|) := by
            apply add_pos_of_pos_of_nonneg (by positivity)
            apply add_abs_nonneg
      _ = a' + b' + c'' := by
            rw [← h']
            ring

lemma aux₅ {a b c : Real.Angle}
  (h : a + b = c)
  (hac : a.sign = c.sign)
  (h' : |a.toReal| < |c.toReal|)
  : a.sign = b.sign := by
  by_cases! ha : a.sign = 0
  · rw [ha] at hac ⊢
    symm at h hac ⊢
    rw [Real.Angle.sign_eq_zero_iff] at hac ha ⊢
    rw [← sub_eq_iff_eq_add'] at h
    rcases hac with hc|hc <;> rcases ha with ha|ha
      <;> rw [ha, hc] at h <;> rw [← h] <;> simp
  · wlog ha' : a.sign = -1
    · have h₁ : (-a) + (-b) = (-c) := by
        rw [← h]
        abel
      have h_neg_ac : (-a).sign = (-c).sign := by
        rw [Real.Angle.sign_neg, Real.Angle.sign_neg, neg_inj]
        exact hac
      have h_neg_a : (-a).sign ≠ 0 := by
        rw [Real.Angle.sign_neg, SignType.neg_eq_zero_iff.ne]
        exact ha
      have h₂ : |(-a).toReal| < |(-c).toReal| := by simp [h']
      have h'' := SignType.trichotomy a.sign
      have h₃ : (-a).sign = -1 := by
        rw [Real.Angle.sign_neg, neg_eq_iff_eq_neg]
        tauto
      have h''' := this h₁ h_neg_ac h₂ h_neg_a h₃
      rw [Real.Angle.sign_neg, Real.Angle.sign_neg, neg_inj] at h'''
      exact h'''
    rw [ha'] at hac ⊢
    symm at h hac ⊢
    rw [← Real.Angle.coe_toReal a] at h
    rw [← Real.Angle.coe_toReal b] at h
    rw [← Real.Angle.coe_toReal c] at h
    rw [← sub_eq_zero, ← Real.Angle.coe_add, ← Real.Angle.coe_sub, Real.Angle.coe_eq_zero_iff] at h
    rw [← Real.Angle.toReal_neg_iff_sign_neg] at hac ha' ⊢
    set a' := a.toReal with haa'
    set b' := b.toReal with hbb'
    set c' := c.toReal with hcc'
    rw [abs_of_neg ha', abs_of_neg hac, neg_lt_neg_iff] at h'
    rcases h with ⟨n, hn⟩
    contrapose! hn
    by_cases! hn' : 0 ≤ n
    · apply ne_of_gt
      calc c' - (a' + b')
        = (c' - a') + -b' := by abel
      _ < 0 := by
            apply add_neg_of_neg_of_nonpos (sub_neg_of_lt h')
            apply neg_nonpos_of_nonneg hn
      _ ≤ n • (2 * π) := by positivity
    · apply ne_of_lt
      calc n • (2 * π)
        ≤ (- 1) • (2 * π) := by
            rw [← Int.le_sub_one_iff, zero_sub] at hn'
            rw [smul_le_smul_iff_of_pos_right (by positivity)]
            exact hn'
      _ = (- π) + 0 + (- π) := by
            ring
      _ < c' + (-a') + (-b') := by
            apply add_lt_add_of_lt_of_le
            · apply add_lt_add
              · exact Real.Angle.neg_pi_lt_toReal c
              · apply neg_pos_of_neg ha'
            · apply neg_le_neg
              apply Real.Angle.toReal_le_pi
      _ = c' - (a' + b') := by abel

lemma aux₆ {a b : Real.Angle} (h₁ : a.sign = b.sign) (h₂ : a.sign ≠ 0)
  (h : 2 • a = 2 • b) : a = b := by
  rw [Real.Angle.two_nsmul_eq_iff] at h
  rcases h with (h|h)
  · exact h
  · contrapose! h₂
    rw [← sub_eq_iff_eq_add] at h
    rw [← h, Real.Angle.sign_sub_pi, SignType.self_eq_neg_iff] at h₁
    exact h₁

lemma aux₇ {x y : ℝ} (h : ∃ k : ℤ, x = y * k)
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

lemma aux₈ {x y z : ℝ}
  (hx' : 0 ≤ x) (hy' : y ≤ 0)
  (hx : |x| < z) (hy : |y| < z)
  : |x + y| < z := by
    rw [abs_lt]
    constructor
    · calc -z
          _ < y := by exact (abs_lt.mp hy).left
          _ = 0 + y := by exact (zero_add y).symm
          _ ≤ x + y := by exact add_le_add_left hx' y
    · calc x + y
        _ ≤ x + 0 := by exact add_le_add_right hy' x
        _ = x := by exact add_zero x
        _ < z := by exact (abs_lt.mp hx).right

lemma aux₉ {x y z : ℝ} (h : |x + y| = z)
  (hx : |x| < z) (hy : |y| < z)
  : |x| + |y| = z := by
    symm
    rw [← h, abs_add_eq_add_abs_iff]
    contrapose! h
    apply ne_of_lt
    by_cases hx' : 0 ≤ x
    · have hy' := h.left hx'
      exact aux₈ hx' (le_of_lt hy') hx hy
    · push_neg at hx'
      have hy' := h.right (le_of_lt hx')
      rw [add_comm]
      exact aux₈ (le_of_lt hy') (le_of_lt hx') hy hx

lemma aux₁₀ {a b : Real.Angle} (h : 2 • a + 2 • b = Real.pi)
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
            < Real.pi + |Real.pi / 2| := by exact add_lt_add_left h₁ _
          _ = Real.pi + Real.pi / 2 := by exact (add_right_inj _).mpr (abs_eq_self.mpr h₂)
          _ ≤ Real.pi + Real.pi / 2 + Real.pi / 2 := by exact (le_add_iff_nonneg_right _).mpr h₂
          _ = 2 * Real.pi := by ring
    have h₄ : |a' + b'| = Real.pi / 2 := by
      rw [abs_eq h₂]
      rcases h with pos|neg
      · left
        apply eq_of_sub_eq_zero
        apply aux₇ pos
        calc |a' + b' - Real.pi / 2|
            ≤ |a' + b'| + |Real.pi / 2| := by exact abs_sub _ _
          _ < 2 * Real.pi := by exact h₃
      · right
        apply eq_of_sub_eq_zero
        rw [← neg_div]
        apply aux₇ neg
        rw [neg_div, sub_neg_eq_add]
        calc |a' + b' + Real.pi / 2|
            ≤ |a' + b'| + |Real.pi / 2| := by exact abs_add_le _ _
          _ < 2 * Real.pi := by exact h₃
    exact aux₉ h₄ ha hb

lemma angle_eq_of_oangle_eq {A₁ A₂ A₃ B₁ B₂ B₃ : Pt}
  (h : ∡ A₁ A₂ A₃ = ∡ B₁ B₂ B₃)
  (hA₁ : A₁ ≠ A₂) (hA₂ : A₃ ≠ A₂) (hB₁ : B₁ ≠ B₂) (hB₂ : B₃ ≠ B₂)
  : ∠ A₁ A₂ A₃ = ∠ B₁ B₂ B₃ := by
  rw [angle_eq_abs_oangle_toReal hA₁ hA₂, angle_eq_abs_oangle_toReal hB₁ hB₂, h]

omit hd2 [Oriented ℝ V (Fin 2)] in
lemma angle_eq_of_cos_angle_eq {A₁ A₂ A₃ B₁ B₂ B₃ : Pt}
  (h : Real.cos (∠ A₁ A₂ A₃) = Real.cos (∠ B₁ B₂ B₃)) : ∠ A₁ A₂ A₃ = ∠ B₁ B₂ B₃ := by
  unfold EuclideanGeometry.angle at *
  rw [InnerProductGeometry.cos_angle, InnerProductGeometry.cos_angle] at h
  unfold InnerProductGeometry.angle at *
  rw [h]

omit hd2 [Oriented ℝ V (Fin 2)] in
lemma eq_of_mem_sphere_of_collinear {A B C : Pt} {Ω : Sphere Pt}
  (hA : A ∈ Ω) (hB : B ∈ Ω) (hC : C ∈ Ω) (h : Collinear ℝ {A, B, C})
  : A = B ∨ B = C ∨ C = A := by
  by_cases! hAB : A = B
  · left
    exact hAB
  · right
    have hA' : A ∈ ({A, B, C} : Set Pt) := by simp
    have hB' : B ∈ ({A, B, C} : Set Pt) := by simp
    have hC' : C ∈ ({A, B, C} : Set Pt) := by simp
    have hC'' := Collinear.mem_affineSpan_of_mem_of_ne h hA' hB' hC' hAB
    rw [← Sphere.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair hA hC''] at hC
    rcases hC with hC|hC
    · right
      exact hC
    · have hB'' := right_mem_affineSpan_pair ℝ A B
      rw [← Sphere.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair hA hB''] at hB
      rcases hB with hB|hB
      · contrapose! hAB
        exact hB.symm
      · rw [← hC] at hB
        left
        exact hB

omit [Oriented ℝ V (Fin 2)] in
lemma eq_max_of_max_ne_top
  {A B : Submodule ℝ V}
  (hA : Module.finrank ℝ A = 1)
  (h : A ⊔ B ≠ ⊤) : A = A ⊔ B := by
  apply Submodule.eq_of_le_of_finrank_eq le_sup_left
  rw [hA]
  have hAB := Submodule.finrank_le (A ⊔ B)
  rw [hd2.out] at hAB
  have hAB' : 1 ≤ Module.finrank ℝ ↥(A ⊔ B) := by
    rw [← hA]
    exact Submodule.finrank_mono le_sup_left
  have hAB'' : Module.finrank ℝ ↥(A ⊔ B) ≠ 2 := by
    contrapose! h
    apply Submodule.eq_top_of_finrank_eq
    rw [hd2.out, h]
  lia

omit [Oriented ℝ V (Fin 2)] hd2 in
lemma affineSpan_pair_finrank {A B : Pt}
  (hAB : A ≠ B): Module.finrank ℝ (affineSpan ℝ {A, B}).direction = 1 := by
  rw [direction_affineSpan]
  have h := affineIndependent_of_ne ℝ hAB
  rw [← Matrix.range_cons_cons_empty]
  apply AffineIndependent.finrank_vectorSpan h
  simp

omit [Oriented ℝ V (Fin 2)] in
lemma inter_nonempty_of_not_parallel
  {A₁ A₂ B₁ B₂ : Pt}
  (hA : A₁ ≠ A₂) (hB : B₁ ≠ B₂)
  (h : ¬line[ℝ, A₁, A₂] ∥ line[ℝ, B₁, B₂]) :
  Set.Nonempty ((line[ℝ, A₁, A₂] : Set _) ∩ (line[ℝ, B₁, B₂] : Set Pt)) := by
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
    · exact eq_max_of_max_ne_top V (affineSpan_pair_finrank V Pt hA) h
    · symm
      rw [sup_comm] at *
      exact eq_max_of_max_ne_top V (affineSpan_pair_finrank V Pt hB) h
  · rw [affineSpan_eq_bot, affineSpan_eq_bot]
    constructor <;> intro h' <;> contrapose! h' <;> simp

lemma oangle_eq_zero_of_collinear {P₁ P₂ P₃ : Pt} (h : Collinear ℝ {P₁, P₂, P₃})
  : ∡ P₂ P₁ P₃ = 0 ∨ ∡ P₂ P₃ P₁ = 0 := by
  have h' := h.wbtw_or_wbtw_or_wbtw
  casesm* _ ∨ _
  · left
    exact h'.oangle₂₁₃_eq_zero
  · left
    exact h'.oangle₁₃₂_eq_zero
  · right
    exact h'.oangle₃₁₂_eq_zero

lemma Sphere.IsTangentAt_of_two_zsmul_oangle_eq {s : Sphere Pt} {P P₁ P₂ Q : Pt}
  (hP : P ∈ s) (hP₁ : P₁ ∈ s) (hP₂ : P₂ ∈ s)
  (hPP₁ : P ≠ P₁) (hPP₂ : P ≠ P₂) (hP₁P₂ : P₁ ≠ P₂) (hPQ : P ≠ Q)
  (h : (2 : ℤ) • ∡ Q P P₁ = (2 : ℤ) • ∡ P P₂ P₁ )
  : s.IsTangentAt P (line[ℝ, P, Q]):= by
  apply EuclideanGeometry.Sphere.IsTangentAt_of_angle_eq_pi_div_two _ hP
  have h' := EuclideanGeometry.Sphere.two_zsmul_oangle_center_add_two_zsmul_oangle_eq_pi
    hP hP₂ hP₁ hPP₂.symm hP₁P₂.symm hPP₁
  have h_OP : s.center ≠ P := by
    contrapose! hPP₁ with h''
    rw [← h'']
    rw [← dist_eq_zero] at h'' ⊢
    rw [EuclideanGeometry.mem_sphere'.mp hP₁]
    rw [EuclideanGeometry.mem_sphere'.mp hP] at h''
    exact h''
  rw [← h, ← smul_add, add_comm, oangle_add hPQ.symm hPP₁.symm h_OP] at h'
  rw [EuclideanGeometry.angle_eq_abs_oangle_toReal hPQ.symm h_OP]
  rw [Real.Angle.abs_toReal_eq_pi_div_two_iff]
  rw [← Real.Angle.two_nsmul_eq_pi_iff]
  exact h'

-- reverse of EuclideanGeometry.sbtw_of_collinear_of_dist_center_lt_radius
omit hd2 [Oriented ℝ V (Fin 2)] in
lemma Sphere.dist_le_radius_of_sbtw {P₁ P₂ P₃ : Pt} {s : Sphere Pt}
  (h : Sbtw ℝ P₁ P₂ P₃)
  (hP₁ : P₁ ∈ s) (hP₃ : P₃ ∈ s)
  : dist P₂ s.center < s.radius := by
  have h := h.dist_lt_max_dist s.center
  rw [EuclideanGeometry.mem_sphere] at hP₁ hP₃
  rw [hP₁, hP₃, max_self] at h
  exact h

-- stronger version of Collinear.wbtw_or_wbtw_or_wbtw
omit hd2 [Oriented ℝ V (Fin 2)] in
lemma Collinear.sbtw_or_wbtw_or_wbtw {P₁ P₂ P₃ : Pt}
  (h : Collinear ℝ {P₁, P₂, P₃})
  : Sbtw ℝ P₁ P₂ P₃ ∨ Wbtw ℝ P₂ P₃ P₁ ∨ Wbtw ℝ P₃ P₁ P₂ := by
  rcases h.wbtw_or_wbtw_or_wbtw with (h'|h')
  · by_cases! h'' : Sbtw ℝ P₁ P₂ P₃
    · left
      exact h''
    · rw [Sbtw, not_and, not_and_or, not_ne_iff, not_ne_iff] at h''
      right
      rcases h'' h' with hX'|hX' <;> rw [hX']
      · right
        apply wbtw_self_right
      · left
        apply wbtw_self_left
  · right
    exact h'

-- eveb stronger version of Collinear.wbtw_or_wbtw_or_wbtw when P₂ ≠ P₃
omit hd2 [Oriented ℝ V (Fin 2)] in
lemma Collinear.sbtw_or_sbtw_or_wbtw_of_ne {P₁ P₂ P₃ : Pt}
  (h : Collinear ℝ {P₁, P₂, P₃}) (h₂₃ : P₂ ≠ P₃)
  : Sbtw ℝ P₁ P₂ P₃ ∨ Sbtw ℝ P₂ P₃ P₁ ∨ Wbtw ℝ P₃ P₁ P₂ := by
  have h' := h.wbtw_or_wbtw_or_wbtw
  by_contra! h''
  rw [Sbtw, not_and_or, not_and_or, not_ne_iff, not_ne_iff] at h''
  rw [Sbtw, not_and_or, not_and_or, not_ne_iff, not_ne_iff] at h''
  have h₁ : P₂ = P₁ → Wbtw ℝ P₃ P₁ P₂ := by
    intro h_eq
    rw [h_eq]
    apply wbtw_self_right
  have h₂ : P₃ = P₁ → Wbtw ℝ P₃ P₁ P₂ := by
    intro h_eq
    rw [h_eq]
    apply wbtw_self_left
  have h₂₃' := h₂₃.symm
  tauto

-- reverse of EuclideanGeometry.two_zsmul_oangle_of_parallel
lemma parallel_of_two_zsmul_oangle_eq {P₁ P₂ P₃ P₄ : Pt}
  (h₁₂ : P₁ ≠ P₂) (h₂₃ : P₂ ≠ P₃) (h₃₄ : P₃ ≠ P₄)
  (h : (2 : ℤ) • ∡ P₁ P₂ P₃ = (2 : ℤ) • ∡ P₄ P₃ P₂)
  : line[ℝ, P₁, P₂] ∥ line[ℝ, P₃, P₄] := by
  symm at h₂₃
  rw [← vsub_eq_zero_iff_eq.ne] at h₁₂ h₂₃ h₃₄
  rw [AffineSubspace.affineSpan_parallel_iff_vectorSpan_eq_and_eq_empty_iff_eq_empty]
  constructor
  · rw [oangle, oangle] at h
    rw [← neg_vsub_eq_vsub_rev P₃ P₂] at h
    rw [← Orientation.oangle_neg_left_eq_neg_right] at h
    rw [neg_vsub_eq_vsub_rev] at h
    rw [Orientation.oangle_rev, smul_neg, neg_eq_iff_add_eq_zero] at h
    rw [add_comm, ← smul_add, o.oangle_add h₃₄ h₂₃ h₁₂] at h
    rw [Real.Angle.two_zsmul_eq_zero_iff] at h
    rw [o.oangle_eq_zero_or_eq_pi_iff_right_eq_smul] at h
    rw [vectorSpan_pair, vectorSpan_pair]
    symm
    rw [Submodule.span_singleton_eq_span_singleton]
    rcases h with (h|h)
    · contrapose! h
      exact h₃₄
    · rcases h with ⟨x, hx⟩
      by_cases! hx' : x = 0
      · contrapose! hx
        rw [hx', zero_smul]
        exact h₁₂
      · use (Units.mk0 _ hx')
        rw [Units.smul_mk0]
        symm
        exact hx
  · constructor <;> intro h <;> contrapose! h <;> simp

structure SphereOrder (P₁ P₂ P₃ P₄ : Pt) where
  (cospherical : Cospherical {P₁, P₂, P₃, P₄})
  (sign_oangle₁₂₃_ne_zero : (∡ P₁ P₂ P₃).sign ≠ 0)
  (sign_oangle₁₂₃_eq_sign_oangle₃₄₁ : (∡ P₁ P₂ P₃).sign = (∡ P₃ P₄ P₁).sign)

def diag_inter_set (P₁ P₂ P₃ P₄ : Pt) := (line[ℝ, P₁, P₃] : Set Pt) ∩ line[ℝ, P₂, P₄]

omit hd2 [Oriented ℝ V (Fin 2)] in
lemma mem_diag_inter_set_comm  {X P₁ P₂ P₃ P₄ : Pt}
  (h : X ∈ diag_inter_set V Pt P₁ P₂ P₃ P₄) : X ∈ diag_inter_set V Pt P₁ P₄ P₃ P₂ := by
  rw [diag_inter_set] at h
  constructor
  · exact h.left
  · rw [Set.pair_comm]
    exact h.right

omit hd2 [Oriented ℝ V (Fin 2)] in
lemma diag_inter_set_comm (P₁ P₂ P₃ P₄ : Pt)
  : diag_inter_set V Pt P₁ P₂ P₃ P₄ = diag_inter_set V Pt P₁ P₄ P₃ P₂ := by
  ext X
  constructor <;> intro h <;> exact mem_diag_inter_set_comm V Pt h

omit hd2 [Oriented ℝ V (Fin 2)] in
lemma mem_diag_inter_set_rotate  {X P₁ P₂ P₃ P₄ : Pt}
  (h : X ∈ diag_inter_set V Pt P₁ P₂ P₃ P₄) : X ∈ diag_inter_set V Pt P₂ P₃ P₄ P₁ := by
  rw [diag_inter_set] at h
  constructor
  · exact h.right
  · rw [Set.pair_comm]
    exact h.left

omit hd2 [Oriented ℝ V (Fin 2)] in
lemma diag_inter_set_rotate (P₁ P₂ P₃ P₄ : Pt)
  : diag_inter_set V Pt P₁ P₂ P₃ P₄ = diag_inter_set V Pt P₂ P₃ P₄ P₁ := by
  ext X
  constructor <;> intro h
  · exact mem_diag_inter_set_rotate V Pt h
  · apply mem_diag_inter_set_rotate
    apply mem_diag_inter_set_rotate
    apply mem_diag_inter_set_rotate
    exact h

namespace SphereOrder

variable {P₁ P₂ P₃ P₄ : Pt}

lemma comm (h : SphereOrder V Pt P₁ P₂ P₃ P₄) : SphereOrder V Pt P₁ P₄ P₃ P₂ := by
  constructor
  · rw [Set.pair_comm]
    nth_rw 2 [Set.insert_comm]
    rw [Set.pair_comm]
    exact h.cospherical
  · rw [EuclideanGeometry.oangle_rev, Real.Angle.sign_neg]
    rw [SignType.neg_eq_zero_iff.ne, ← h.sign_oangle₁₂₃_eq_sign_oangle₃₄₁]
    exact h.sign_oangle₁₂₃_ne_zero
  · rw [EuclideanGeometry.oangle_rev, Real.Angle.sign_neg]
    rw [← h.sign_oangle₁₂₃_eq_sign_oangle₃₄₁]
    exact oangle_swap₁₃_sign P₁ P₂ P₃

lemma P₁_ne_P₂ (h : SphereOrder V Pt P₁ P₂ P₃ P₄) : P₁ ≠ P₂ := by
  exact EuclideanGeometry.left_ne_of_oangle_sign_ne_zero h.sign_oangle₁₂₃_ne_zero

lemma P₁_ne_P₃ (h : SphereOrder V Pt P₁ P₂ P₃ P₄) : P₁ ≠ P₃ := by
  exact EuclideanGeometry.left_ne_right_of_oangle_sign_ne_zero h.sign_oangle₁₂₃_ne_zero

lemma P₂_ne_P₃ (h : SphereOrder V Pt P₁ P₂ P₃ P₄) : P₂ ≠ P₃ := by
  exact (EuclideanGeometry.right_ne_of_oangle_sign_ne_zero h.sign_oangle₁₂₃_ne_zero).symm

lemma sign_oangle₃₄₁_ne_zero (h : SphereOrder V Pt P₁ P₂ P₃ P₄) : (∡ P₃ P₄ P₁).sign ≠ 0 := by
  rw [← h.sign_oangle₁₂₃_eq_sign_oangle₃₄₁]
  exact h.sign_oangle₁₂₃_ne_zero

lemma P₁_ne_P₄ (h : SphereOrder V Pt P₁ P₂ P₃ P₄) : P₁ ≠ P₄ := by
  exact EuclideanGeometry.right_ne_of_oangle_sign_ne_zero h.sign_oangle₃₄₁_ne_zero

lemma P₃_ne_P₄ (h : SphereOrder V Pt P₁ P₂ P₃ P₄) : P₃ ≠ P₄ := by
  exact EuclideanGeometry.left_ne_of_oangle_sign_ne_zero h.sign_oangle₃₄₁_ne_zero

lemma P₂_ne_P₄ (h : SphereOrder V Pt P₁ P₂ P₃ P₄) : P₂ ≠ P₄ := by
  have h' := h.sign_oangle₁₂₃_ne_zero
  contrapose! h'
  have h'' := h.sign_oangle₁₂₃_eq_sign_oangle₃₄₁
  rw [← h', EuclideanGeometry.oangle_rev P₁ P₂ P₃, Real.Angle.sign_neg, SignType.self_eq_neg_iff] at h''
  exact h''

lemma oangle₁₂₃_add_oangle₃₄₁_eq_pi (h : SphereOrder V Pt P₁ P₂ P₃ P₄) : ∡ P₁ P₂ P₃ + ∡ P₃ P₄ P₁ = Real.pi := by
  have h' := h.cospherical
  rw [Set.pair_comm] at h'
  have h'' := EuclideanGeometry.Cospherical.two_zsmul_oangle_eq h'
    h.P₁_ne_P₂.symm h.P₂_ne_P₃ h.P₁_ne_P₄.symm h.P₃_ne_P₄.symm
  rw [← sub_eq_zero, ← smul_sub, sub_eq_add_neg, ← EuclideanGeometry.oangle_rev] at h''
  exact aux₁ h.sign_oangle₁₂₃_eq_sign_oangle₃₄₁ h.sign_oangle₁₂₃_ne_zero h''

lemma oangle₂₃₄_add_oangle₄₁₂_eq_pi (h : SphereOrder V Pt P₁ P₂ P₃ P₄) : ∡ P₂ P₃ P₄ + ∡ P₄ P₁ P₂ = Real.pi := by
  have h' := (EuclideanGeometry.oangle_add_oangle_add_oangle_eq_pi
    h.P₂_ne_P₃.symm h.P₁_ne_P₃ h.P₁_ne_P₂.symm).symm
  have h'' := (EuclideanGeometry.oangle_add_oangle_add_oangle_eq_pi
    h.P₁_ne_P₄ h.P₁_ne_P₃.symm h.P₃_ne_P₄.symm).symm
  rw [← sub_eq_iff_eq_add'] at h' h''
  have h''' := h.oangle₁₂₃_add_oangle₃₄₁_eq_pi
  rw [← h', ← h''] at h'''
  rw [← sub_eq_zero] at h''' ⊢
  rw [← neg_eq_zero, ← h''']
  rw [← EuclideanGeometry.oangle_add h.P₂_ne_P₃ h.P₁_ne_P₃ h.P₃_ne_P₄.symm]
  rw [← EuclideanGeometry.oangle_add h.P₁_ne_P₄.symm h.P₁_ne_P₃.symm h.P₁_ne_P₂.symm]
  abel

lemma rotate (h : SphereOrder V Pt P₁ P₂ P₃ P₄) : SphereOrder V Pt P₂ P₃ P₄ P₁ := by
  constructor
  · rw [Set.pair_comm]
    nth_rw 2 [Set.insert_comm]
    nth_rw 1 [Set.insert_comm]
    exact h.cospherical
  · intro h'
    rw [EuclideanGeometry.oangle_sign_eq_zero_iff_collinear] at h'
    have h'' := h.cospherical
    rw [EuclideanGeometry.cospherical_iff_exists_sphere] at h''
    rcases h'' with ⟨Ω, hΩ⟩
    have hP₂ : P₂ ∈ Ω := by
      apply hΩ
      apply Set.mem_insert_of_mem
      apply Set.mem_insert
    have hP₃ : P₃ ∈ Ω := by
      apply hΩ
      apply Set.mem_insert_of_mem
      apply Set.mem_insert_of_mem
      apply Set.mem_insert
    have hP₄ : P₄ ∈ Ω := by
      apply hΩ
      apply Set.mem_insert_of_mem
      apply Set.mem_insert_of_mem
      apply Set.mem_insert_of_mem
      apply Set.mem_singleton
    have h'' := eq_of_mem_sphere_of_collinear V Pt hP₂ hP₃ hP₄ h'
    contrapose! h''
    constructorm* _ ∧ _
    · exact h.P₂_ne_P₃
    · exact h.P₃_ne_P₄
    · exact h.P₂_ne_P₄.symm
  · exact aux₂ h.oangle₂₃₄_add_oangle₄₁₂_eq_pi

lemma symm (h : SphereOrder V Pt P₁ P₂ P₃ P₄) : SphereOrder V Pt P₃ P₄ P₁ P₂ := by
  exact h.rotate.rotate

lemma rotate' (h : SphereOrder V Pt P₁ P₂ P₃ P₄) : SphereOrder V Pt P₄ P₁ P₂ P₃ := by
  exact h.rotate.rotate.rotate

lemma sign_oangle₂₃₄_ne_zero (h : SphereOrder V Pt P₁ P₂ P₃ P₄) : (∡ P₂ P₃ P₄).sign ≠ 0 := by
  exact h.rotate.sign_oangle₁₂₃_ne_zero

lemma angle₁₂₄_add_angle₄₂₃_eq_angle₁₂₃ (h : SphereOrder V Pt P₁ P₂ P₃ P₄) : ∠ P₁ P₂ P₄ + ∠ P₄ P₂ P₃ = ∠ P₁ P₂ P₃ := by
  have h₁ := aux₃ h.oangle₁₂₃_add_oangle₃₄₁_eq_pi h.sign_oangle₁₂₃_ne_zero
  have h₂ := aux₃ h.oangle₂₃₄_add_oangle₄₁₂_eq_pi h.sign_oangle₂₃₄_ne_zero
  rw [← EuclideanGeometry.angle_eq_abs_oangle_toReal h.P₁_ne_P₂ h.P₂_ne_P₃.symm] at h₁
  rw [← EuclideanGeometry.angle_eq_abs_oangle_toReal h.P₃_ne_P₄ h.P₁_ne_P₄] at h₁
  rw [← EuclideanGeometry.angle_eq_abs_oangle_toReal h.P₂_ne_P₃ h.P₃_ne_P₄.symm] at h₂
  rw [← EuclideanGeometry.angle_eq_abs_oangle_toReal h.P₁_ne_P₄.symm h.P₁_ne_P₂.symm] at h₂
  have h₃ := (EuclideanGeometry.angle_add_angle_add_angle_eq_pi P₂ h.P₃_ne_P₄.symm).symm
  have h₄ := (EuclideanGeometry.angle_add_angle_add_angle_eq_pi P₄ h.P₁_ne_P₂.symm).symm
  rw [← sub_eq_iff_eq_add'] at h₃ h₄
  rw [← h₃, ← h₄, ← neg_inj, ← sub_eq_zero] at h₂
  ring_nf at h₂
  repeat rw [add_assoc] at h₂
  rw [neg_add_eq_zero] at h₂
  rw [h₂] at h₁
  nth_rw 1 [add_left_comm] at h₁
  nth_rw 2 [add_left_comm] at h₁
  rw [← add_assoc] at h₁
  have h₅ := EuclideanGeometry.angle_le_angle_add_angle P₂ P₃ P₄ P₁
  have h₆ := EuclideanGeometry.angle_le_angle_add_angle P₄ P₃ P₂ P₁
  rw [EuclideanGeometry.angle_comm P₃ P₂ P₁] at h₅
  rw [EuclideanGeometry.angle_comm P₃ P₂ P₄] at h₅
  rw [EuclideanGeometry.angle_comm P₄ P₂ P₁] at h₅
  rw [add_eq_add_iff_eq_and_eq h₅ h₆] at h₁
  symm
  rw [add_comm]
  exact h₁.left

lemma sign_oangle₁₂₃_eq_sign_oangle₂₃₄ (h : SphereOrder V Pt P₁ P₂ P₃ P₄) : (∡ P₁ P₂ P₃).sign = (∡ P₂ P₃ P₄).sign := by
  have h₁ := EuclideanGeometry.oangle_add h.P₁_ne_P₂ h.P₂_ne_P₄.symm h.P₂_ne_P₃.symm
  have h₂ := h.angle₁₂₄_add_angle₄₂₃_eq_angle₁₂₃
  rw [EuclideanGeometry.angle_eq_abs_oangle_toReal h.P₁_ne_P₂ h.P₂_ne_P₄.symm] at h₂
  rw [EuclideanGeometry.angle_eq_abs_oangle_toReal h.P₂_ne_P₄.symm h.P₂_ne_P₃.symm] at h₂
  rw [EuclideanGeometry.angle_eq_abs_oangle_toReal h.P₁_ne_P₂ h.P₂_ne_P₃.symm] at h₂
  rw [add_comm] at h₁ h₂
  have h'' : (∡ P₄ P₂ P₃).sign ≠ 0 := by
    rw [← EuclideanGeometry.oangle_rotate_sign]
    exact h.sign_oangle₂₃₄_ne_zero
  have h' := aux₄ h'' h.sign_oangle₁₂₃_ne_zero h₁ h₂
  rw [← h', ← EuclideanGeometry.oangle_rotate_sign]

lemma trans {P₅ : Pt} (h : SphereOrder V Pt P₁ P₂ P₃ P₄)
  (h' : SphereOrder V Pt P₃ P₄ P₅ P₁) : SphereOrder V Pt P₅ P₁ P₂ P₃ := by
  apply rotate
  constructor
  · rw [Set.pair_comm]
    apply EuclideanGeometry.cospherical_of_two_zsmul_oangle_eq_of_not_collinear
    · rw [← EuclideanGeometry.Cospherical.two_zsmul_oangle_eq h'.cospherical
        h'.P₁_ne_P₂.symm h'.P₂_ne_P₄ h'.P₁_ne_P₃.symm h'.P₃_ne_P₄]
      have h'' := h.cospherical
      nth_rw 2 [Set.insert_comm] at h''
      nth_rw 1 [Set.insert_comm] at h''
      nth_rw 2 [Set.insert_comm] at h''
      rw [Set.pair_comm] at h''
      rw [← EuclideanGeometry.Cospherical.two_zsmul_oangle_eq h''
        h.P₂_ne_P₃ h.P₁_ne_P₂.symm h.P₃_ne_P₄.symm h.P₁_ne_P₄.symm]
    · have h'' := h'.cospherical
      rw [cospherical_iff_exists_sphere] at h''
      rcases h'' with ⟨s, hs⟩
      have h₃ : P₃ ∈ s := by
        apply hs
        simp
      have h₅ : P₅ ∈ s := by
        apply hs
        simp
      have h₁ : P₁ ∈ s := by
        apply hs
        simp
      intro h'''
      have h_eq := eq_of_mem_sphere_of_collinear V Pt h₃ h₅ h₁ h'''
      contrapose! h_eq
      constructorm* _ ∧ _
      · exact h'.P₁_ne_P₃
      · exact h'.P₃_ne_P₄
      · exact h'.P₁_ne_P₄.symm
  · rw [← EuclideanGeometry.oangle_rotate_sign]
    exact sign_oangle₃₄₁_ne_zero V Pt h'
  · rw [← EuclideanGeometry.oangle_rotate_sign]
    rw [h'.symm.sign_oangle₁₂₃_eq_sign_oangle₂₃₄]
    rw [← EuclideanGeometry.oangle_rotate_sign]
    rw [h.sign_oangle₁₂₃_eq_sign_oangle₃₄₁]

lemma trans' {P₅ : Pt} (h : SphereOrder V Pt P₁ P₂ P₃ P₄)
  (h' : SphereOrder V Pt P₃ P₄ P₅ P₁) : SphereOrder V Pt P₂ P₃ P₄ P₅ := by
  have h'' := h.trans V Pt h'
  exact h'.trans V Pt h''

lemma trans'' {P₅ : Pt} (h : SphereOrder V Pt P₁ P₂ P₃ P₄)
  (h' : SphereOrder V Pt P₃ P₄ P₅ P₁) : SphereOrder V Pt P₄ P₅ P₁ P₂ := by
  have h'' := h.trans V Pt h'
  have h''' := h.trans' V Pt h'
  exact h''.trans V Pt h'''

lemma exists_diag_inter (h : SphereOrder V Pt P₁ P₂ P₃ P₄)
  : ∃ X : Pt, X ∈ diag_inter_set V Pt P₁ P₂ P₃ P₄ := by
  apply inter_nonempty_of_not_parallel V Pt h.P₁_ne_P₃ h.P₂_ne_P₄
  intro h'
  have h'' := AffineSubspace.Parallel.refl (affineSpan ℝ {P₁, P₂})
  nth_rw 1 [Set.pair_comm] at h''
  nth_rw 1 [Set.pair_comm] at h'
  nth_rw 2 [Set.pair_comm] at h'
  have h_312_124 := EuclideanGeometry.two_zsmul_oangle_of_parallel h'' h'
  rw [EuclideanGeometry.oangle_rev, smul_neg, neg_eq_iff_add_eq_zero, ← smul_add] at h_312_124
  have h_312_124' : (∡ P₃ P₁ P₂).sign = (∡ P₁ P₂ P₄).sign := by
    rw [← EuclideanGeometry.oangle_rotate_sign]
    rw [← h.rotate'.sign_oangle₁₂₃_eq_sign_oangle₂₃₄]
    rw [← EuclideanGeometry.oangle_rotate_sign]
  have h_312 : (∡ P₃ P₁ P₂).sign ≠ 0 := by
    rw [← EuclideanGeometry.oangle_rotate_sign]
    exact h.sign_oangle₁₂₃_ne_zero
  have h_312_124'' := Real.Angle.abs_toReal_add_abs_toReal_eq_pi_of_two_nsmul_add_eq_zero_of_sign_eq
    h_312_124 h_312_124' h_312
  rw [← EuclideanGeometry.angle_eq_abs_oangle_toReal h.P₁_ne_P₃.symm h.P₁_ne_P₂.symm] at h_312_124''
  rw [← EuclideanGeometry.angle_eq_abs_oangle_toReal h.P₁_ne_P₂ h.P₂_ne_P₄.symm] at h_312_124''
  contrapose! h_312_124''
  have h_124 := (h.angle₁₂₄_add_angle₄₂₃_eq_angle₁₂₃).symm
  rw [← sub_eq_iff_eq_add] at h_124
  rw [← h_124, add_sub]
  have h''' := (EuclideanGeometry.angle_add_angle_add_angle_eq_pi P₂ h.P₁_ne_P₃).symm
  rw [← sub_eq_iff_eq_add] at h'''
  rw [← h''', sub_sub]
  apply ne_of_lt
  rw [sub_lt_self_iff]
  apply add_pos_of_nonneg_of_pos (EuclideanGeometry.angle_nonneg _ _ _)
  apply lt_of_le_of_ne (EuclideanGeometry.angle_nonneg _ _ _)
  symm
  rw [← (EuclideanGeometry.oangle_eq_zero_iff_angle_eq_zero h.P₂_ne_P₄.symm h.P₂_ne_P₃.symm).ne]
  intro h_423
  have h_423' : (∡ P₄ P₂ P₃).sign = 0 := by
    rw [h_423, Real.Angle.sign_zero]
  contrapose! h_423'
  rw [← EuclideanGeometry.oangle_rotate_sign]
  exact h.sign_oangle₂₃₄_ne_zero

lemma diag_inter_ne_P₁ (h : SphereOrder V Pt P₁ P₂ P₃ P₄)
  {X : Pt} (hX : X ∈ diag_inter_set V Pt P₁ P₂ P₃ P₄)
  : X ≠ P₁ := by
  intro h'
  have hX' := Set.mem_of_mem_inter_right hX
  rw [h'] at hX'
  have h'' := collinear_insert_of_mem_affineSpan_pair hX'
  have h''' := h.cospherical
  rw [EuclideanGeometry.cospherical_iff_exists_sphere] at h'''
  rcases h''' with ⟨s, hs⟩
  have h₁ : P₁ ∈ s := by
    apply hs
    apply Set.mem_insert
  have h₂ : P₂ ∈ s := by
    apply hs
    apply Set.mem_insert_of_mem
    apply Set.mem_insert
  have h₄ : P₄ ∈ s := by
    apply hs
    apply Set.mem_insert_of_mem
    apply Set.mem_insert_of_mem
    apply Set.mem_insert_of_mem
    apply Set.mem_singleton
  have h'''' := eq_of_mem_sphere_of_collinear V Pt h₁ h₂ h₄ h''
  contrapose! h''''
  constructorm* _ ∧ _
  · exact h.P₁_ne_P₂
  · exact h.P₂_ne_P₄
  · exact h.P₁_ne_P₄.symm

lemma diag_inter_sbtw (h : SphereOrder V Pt P₁ P₂ P₃ P₄)
  {X : Pt} (hX : X ∈ diag_inter_set V Pt P₁ P₂ P₃ P₄)
  : Sbtw ℝ P₁ X P₃ := by
  by_contra! h'
  have h_collinear : Collinear ℝ {P₁, X, P₃} := by
    rw [diag_inter_set, Set.mem_inter_iff] at hX
    rw [Set.insert_comm]
    apply collinear_insert_of_mem_affineSpan_pair
    exact hX.left
  have h'' := Collinear.sbtw_or_wbtw_or_wbtw V Pt h_collinear
  have h''' : Wbtw ℝ X P₃ P₁ ∨ Wbtw ℝ P₃ P₁ X := by
    tauto
  wlog h_wbtw : Wbtw ℝ X P₃ P₁ generalizing P₁ P₂ P₃ P₄
  · have h_wbtw' : Wbtw ℝ X P₁ P₃ := by
      rw [wbtw_comm]
      tauto
    rw [diag_inter_set_rotate, diag_inter_set_rotate] at hX
    rw [sbtw_comm] at h'
    rw [Set.pair_comm, Set.insert_comm, Set.pair_comm] at h_collinear
    nth_rw 1 [wbtw_comm] at h''
    nth_rw 2 [wbtw_comm] at h''
    rw [sbtw_comm] at h''
    nth_rw 2 [or_comm] at h''
    nth_rw 1 [wbtw_comm] at h'''
    nth_rw 2 [wbtw_comm] at h'''
    rw [or_comm] at h'''
    exact this h.symm hX h' h_collinear h'' h''' h_wbtw'
  have h_collinear' : Collinear ℝ {P₂, X, P₄} := by
    rw [diag_inter_set, Set.mem_inter_iff] at hX
    rw [Set.insert_comm]
    apply collinear_insert_of_mem_affineSpan_pair
    exact hX.right
  have h'''' := oangle_eq_zero_of_collinear V Pt h_collinear'
  wlog h_oangle : ∡ X P₂ P₄ = 0 generalizing P₁ P₂ P₃ P₄
  · have h_oangle' : ∡ X P₄ P₂ = 0 := by tauto
    rw [diag_inter_set_comm] at hX
    rw [Set.pair_comm, Set.insert_comm, Set.pair_comm] at h_collinear'
    rw [or_comm] at h''''
    exact this h.comm hX h' h_collinear h'' h''' h_wbtw h_collinear' h'''' h_oangle'
  have h_X_P₃ : X ≠ P₃ := by
    rw [diag_inter_set_rotate, diag_inter_set_rotate] at hX
    exact h.symm.diag_inter_ne_P₁ V Pt hX
  have h_sign := h_wbtw.oangle_sign_eq_of_ne_left P₂ h_X_P₃
  have h_X_P₂ : X ≠ P₂ := by
    rw [diag_inter_set_rotate] at hX
    exact h.rotate.diag_inter_ne_P₁ V Pt hX
  rw [← EuclideanGeometry.oangle_add h_X_P₂ h.P₂_ne_P₄.symm h.P₂_ne_P₃.symm] at h_sign
  rw [← EuclideanGeometry.oangle_add h_X_P₂ h.P₂_ne_P₄.symm h.P₁_ne_P₂] at h_sign
  rw [h_oangle, zero_add, zero_add] at h_sign
  rw [← EuclideanGeometry.oangle_rotate_sign P₄ P₂ P₃] at h_sign
  rw [← EuclideanGeometry.oangle_rotate_sign P₄ P₂ P₁] at h_sign
  rw [← EuclideanGeometry.oangle_swap₁₃_sign P₄ P₁ P₂] at h_sign
  rw [← h.rotate.sign_oangle₁₂₃_eq_sign_oangle₃₄₁, SignType.self_eq_neg_iff] at h_sign
  contrapose! h_sign
  exact h.sign_oangle₂₃₄_ne_zero

lemma diag_inter_sbtw' (h : SphereOrder V Pt P₁ P₂ P₃ P₄)
  {X : Pt} (hX : X ∈ diag_inter_set V Pt P₁ P₂ P₃ P₄)
  : Sbtw ℝ P₂ X P₄ := by
  rw [diag_inter_set_rotate] at hX
  exact h.rotate.diag_inter_sbtw V Pt hX

end SphereOrder

lemma sphereOrder_of_sbtw_diag_inter
  {P₁ P₂ P₃ P₄ X : Pt}
  (h : Cospherical {P₁, P₂, P₃, P₄}) (h₁₂ : P₁ ≠ P₂) (h₂₃ : P₂ ≠ P₃)
  (h₁₃ : Sbtw ℝ P₁ X P₃) (h₂₄ : Sbtw ℝ P₂ X P₄)
  : SphereOrder V Pt P₁ P₂ P₃ P₄ := by
  constructor
  · exact h
  · intro h'
    rw [EuclideanGeometry.oangle_sign_eq_zero_iff_collinear] at h'
    rw [cospherical_iff_exists_sphere] at h
    rcases h with ⟨s, hs⟩
    have hP₁ : P₁ ∈ s := by
      apply hs
      apply Set.mem_insert
    have hP₂ : P₂ ∈ s := by
      apply hs
      apply Set.mem_insert_of_mem
      apply Set.mem_insert
    have hP₃ : P₃ ∈ s := by
      apply hs
      apply Set.mem_insert_of_mem
      apply Set.mem_insert_of_mem
      apply Set.mem_insert
    have h'' := eq_of_mem_sphere_of_collinear V Pt hP₁ hP₂ hP₃ h'
    contrapose! h''
    constructorm* _ ∧ _
    · exact h₁₂
    · exact h₂₃
    · exact h₁₃.left_ne_right.symm
  · rw [EuclideanGeometry.oangle_rotate_sign]
    rw [← h₁₃.oangle_eq_left, EuclideanGeometry.oangle_rev, Real.Angle.sign_neg]
    rw [h₂₄.oangle_sign_eq, h₁₃.oangle_eq_left, EuclideanGeometry.oangle_swap₂₃_sign]

noncomputable def Sphere.antipode
  (s : Sphere Pt) (p : Pt) : Pt :=
  s.secondInter p (s.center -ᵥ p)

omit hd2 [Oriented ℝ V (Fin 2)] in
lemma Sphere.antipode_mem_sphere {s : Sphere Pt} {p : Pt} (h : p ∈ s)
  : Sphere.antipode V Pt s p ∈ s := by
  rw [Sphere.antipode, EuclideanGeometry.Sphere.secondInter_mem]
  exact h

omit hd2 [Oriented ℝ V (Fin 2)] in
lemma Sphere.antipode_isDiameter {s : Sphere Pt} {p : Pt} (h : p ∈ s)
  : Sphere.IsDiameter s p (Sphere.antipode V Pt s p) := by
  rw [Sphere.antipode, EuclideanGeometry.Sphere.isDiameter_iff_mem_and_mem_and_wbtw]
  constructorm* _ ∧ _
  · exact h
  · rw [EuclideanGeometry.Sphere.secondInter_mem]
    exact h
  · apply EuclideanGeometry.Sphere.wbtw_secondInter h
    rw [dist_self]
    apply Sphere.radius_nonneg_of_mem h

structure Imo2023q2Cfg where
  (A B C D E L S P : Pt)
  (Ω ω : Sphere Pt)
  (perp_A_BC prll_D_BC tang_P_ω : AffineSubspace ℝ Pt)
  (h_ABC : AffineIndependent ℝ ![A, B, C])
  (h_acute_ABC : (⟨![A, B, C], h_ABC⟩ : Affine.Triangle _ _).AcuteAngled)
  (h_AB_lt_BC : dist A B < dist A C )
  (h_Ω : {A, B, C} ⊆ (Ω : Set Pt) )
  (h_S_Ω : dist S C = dist S B ∧ S ∈ (Ω : Set Pt))
  (h_S_A : (∡ C B S).sign = (∡ C B A).sign)
  (h_perp_A_BC : perp_A_BC.direction ⟂ line[ℝ, B, C].direction ∧ A ∈ perp_A_BC)
  (h_D : D ∈ (perp_A_BC : Set Pt) ∩ line[ℝ, B, S])
  (h_E : E ∈ (perp_A_BC : Set Pt) ∩ Ω )
  (h_E_ne_A : E ≠ A )
  (h_prll_D_BC : D ∈ prll_D_BC ∧ prll_D_BC ∥ line[ℝ, B, C])
  (h_L : L ∈ (prll_D_BC : Set Pt) ∩ line[ℝ, B, E])
  (h_ω : {B, D, L} ⊆ (ω : Set Pt))
  (h_P : P ∈ (ω : Set Pt) ∩ Ω)
  (h_P_ne_B : P ≠ B)
  (h_rank_tang_P_ω : Module.finrank ℝ tang_P_ω.direction = 1)
  (h_tang_P_ω : Sphere.IsTangentAt ω P tang_P_ω)

namespace Imo2023q2Cfg

variable (cfg : Imo2023q2Cfg V Pt)

def ABC : Affine.Triangle ℝ Pt :=
  ⟨![cfg.A, cfg.B, cfg.C], cfg.h_ABC⟩

lemma B_ne_A : cfg.B ≠ cfg.A := by
  exact cfg.h_ABC.injective.ne (by decide : (1 : Fin 3) ≠ 0)

lemma C_ne_A : cfg.C ≠ cfg.A := by
  exact cfg.h_ABC.injective.ne (by decide : (2 : Fin 3) ≠ 0)

lemma B_ne_C : cfg.B ≠ cfg.C := by
  exact cfg.h_ABC.injective.ne (by decide : (1 : Fin 3) ≠ 2)

lemma S_ne_B : cfg.S ≠ cfg.B := by
  have h := cfg.B_ne_C
  contrapose! h
  rw [← h]
  rw [← dist_eq_zero] at h ⊢
  rw [cfg.h_S_Ω.left]
  exact h

lemma S_ne_C : cfg.S ≠ cfg.C := by
  have h := cfg.B_ne_C
  contrapose! h
  rw [← h]
  rw [← dist_eq_zero] at h ⊢
  rw [cfg.h_S_Ω.left, dist_comm] at h
  exact h

lemma S_ne_A : cfg.S ≠ cfg.A := by
  have h' := cfg.h_S_Ω.left
  have h := cfg.h_AB_lt_BC
  contrapose! h
  apply le_of_eq
  rw [← h]
  exact h'

lemma A_in_Ω : cfg.A ∈ cfg.Ω := by
  have h := cfg.h_Ω
  rw [Set.insert_subset_iff] at h
  exact h.left

lemma B_in_Ω : cfg.B ∈ cfg.Ω := by
  have h := cfg.h_Ω
  rw [Set.insert_subset_iff, Set.insert_subset_iff] at h
  exact h.right.left

lemma C_in_Ω : cfg.C ∈ cfg.Ω := by
  have h := cfg.h_Ω
  rw [Set.insert_subset_iff, Set.insert_subset_iff, Set.singleton_subset_iff] at h
  exact h.right.right

lemma A_opposite_BC : {cfg.B, cfg.C} = Set.range (cfg.ABC.faceOpposite 0).points := by
  ext X
  rw [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range]
  constructor
  · rintro (h|h)
    · use 0
      rw [Affine.Simplex.faceOpposite_point_eq_point_succAbove, h]
      norm_num
      simp [ABC]
    · use 1
      rw [Affine.Simplex.faceOpposite_point_eq_point_succAbove, h]
      norm_num
      simp [ABC]
  · rintro ⟨y, hy⟩
    rw [Affine.Simplex.faceOpposite_point_eq_point_succAbove] at hy
    fin_cases y <;> norm_num at hy <;> simp [ABC] at hy <;> rw [← hy]
    · left
      rfl
    · right
      rfl

lemma angle_BAC_acute : ∠ cfg.B cfg.A cfg.C < π / 2 := by
  have h := cfg.h_acute_ABC
  rw [Affine.Triangle.acuteAngled_iff_angle_lt] at h
  simp at h
  rw [angle_comm]
  exact h.right.right

lemma angle_ACB_acute : ∠ cfg.A cfg.C cfg.B < π / 2 := by
  have h := cfg.h_acute_ABC
  rw [Affine.Triangle.acuteAngled_iff_angle_lt] at h
  simp at h
  rw [angle_comm]
  exact h.right.left

lemma angle_CBA_acute : ∠ cfg.C cfg.B cfg.A < π / 2 := by
  have h := cfg.h_acute_ABC
  rw [Affine.Triangle.acuteAngled_iff_angle_lt] at h
  simp at h
  rw [angle_comm]
  exact h.left

lemma angle_ACB_lt_angle_CBA : ∠ cfg.A cfg.C cfg.B < ∠ cfg.C cfg.B cfg.A := by
  have h := cfg.h_ABC
  rw [affineIndependent_iff_not_collinear_set] at h
  rw [EuclideanGeometry.angle_comm cfg.C cfg.B cfg.A]
  rw [EuclideanGeometry.angle_lt_iff_dist_lt h]
  exact cfg.h_AB_lt_BC

lemma angle_CBS_eq_angle_SBC : ∠ cfg.C cfg.B cfg.S = ∠ cfg.S cfg.C cfg.B := by
  have h := EuclideanGeometry.angle_eq_angle_of_dist_eq cfg.h_S_Ω.left.symm
  rw [EuclideanGeometry.angle_comm]
  exact h

lemma oangle_BSC_eq_oangle_BAC :  ∡ cfg.B cfg.S cfg.C = ∡ cfg.B cfg.A cfg.C := by
  symm
  have h := EuclideanGeometry.Sphere.two_zsmul_oangle_eq cfg.B_in_Ω cfg.A_in_Ω cfg.h_S_Ω.right cfg.C_in_Ω
    cfg.B_ne_A.symm cfg.C_ne_A.symm cfg.S_ne_B cfg.S_ne_C
  have h' := cfg.h_ABC
  rw [affineIndependent_iff_not_collinear_set] at h'
  rw [Set.insert_comm] at h'
  rw [← EuclideanGeometry.oangle_sign_eq_zero_iff_collinear, ← ne_eq] at h'
  apply aux₆ _ h' h
  rw [EuclideanGeometry.oangle_rotate_sign cfg.C cfg.B cfg.A]
  rw [EuclideanGeometry.oangle_rotate_sign cfg.C cfg.B cfg.S]
  exact cfg.h_S_A.symm

lemma angle_BSC_eq_angle_BAC :  ∠ cfg.B cfg.S cfg.C = ∠ cfg.B cfg.A cfg.C := by
  apply angle_eq_of_oangle_eq V Pt _ cfg.S_ne_B.symm cfg.S_ne_C.symm cfg.B_ne_A cfg.C_ne_A
  exact cfg.oangle_BSC_eq_oangle_BAC

lemma angle_CBS_eq : ∠ cfg.C cfg.B cfg.S = (∠ cfg.C cfg.B cfg.A + ∠ cfg.A cfg.C cfg.B) / 2 := by
  rw [eq_div_iff_mul_eq (by norm_num), mul_two]
  nth_rw 2 [angle_CBS_eq_angle_SBC]
  have h₁ := EuclideanGeometry.angle_add_angle_add_angle_eq_pi cfg.B cfg.S_ne_C.symm
  have h₂ := EuclideanGeometry.angle_add_angle_add_angle_eq_pi cfg.B cfg.C_ne_A
  nth_rw 2 [add_comm] at h₁ h₂
  rw [← eq_sub_iff_add_eq] at h₁ h₂
  rw [h₁, h₂, sub_right_inj]
  exact cfg.angle_BSC_eq_angle_BAC

lemma angle_CBS_lt_angle_CBA : ∠ cfg.C cfg.B cfg.S < ∠ cfg.C cfg.B cfg.A := by
  rw [cfg.angle_CBS_eq, div_lt_iff₀ (by norm_num), mul_two, add_lt_add_iff_left]
  exact cfg.angle_ACB_lt_angle_CBA

lemma sign_oangle_SBA_eq_sign_oangle_CBS
  : (∡ cfg.S cfg.B cfg.A).sign = (∡ cfg.C cfg.B cfg.S).sign := by
  have h := EuclideanGeometry.oangle_add cfg.B_ne_C.symm cfg.S_ne_B cfg.B_ne_A.symm
  have h' := cfg.angle_CBS_lt_angle_CBA
  rw [EuclideanGeometry.angle_eq_abs_oangle_toReal cfg.B_ne_C.symm cfg.S_ne_B] at h'
  rw [EuclideanGeometry.angle_eq_abs_oangle_toReal cfg.B_ne_C.symm cfg.B_ne_A.symm] at h'
  have h'' := cfg.h_S_A
  symm
  exact aux₅ h h'' h'

lemma sphereOrder_BASC : SphereOrder V Pt cfg.B cfg.A cfg.S cfg.C := by
  constructor
  · rw [EuclideanGeometry.cospherical_iff_exists_sphere]
    use cfg.Ω
    repeat rw [Set.insert_subset_iff]
    rw [Set.singleton_subset_iff]
    constructorm* _ ∧ _
    · exact cfg.B_in_Ω
    · exact cfg.A_in_Ω
    · exact cfg.h_S_Ω.right
    · exact cfg.C_in_Ω
  · intro h'
    rw [EuclideanGeometry.oangle_sign_eq_zero_iff_collinear] at h'
    have h'' := eq_of_mem_sphere_of_collinear V Pt cfg.B_in_Ω cfg.A_in_Ω cfg.h_S_Ω.right h'
    contrapose! h''
    constructorm* _ ∧ _
    · exact cfg.B_ne_A
    · exact cfg.S_ne_A.symm
    · exact cfg.S_ne_B
  · rw [EuclideanGeometry.oangle_rotate_sign]
    rw [cfg.sign_oangle_SBA_eq_sign_oangle_CBS]
    rw [EuclideanGeometry.oangle_rotate_sign]

noncomputable def M := Sphere.antipode V Pt cfg.Ω cfg.S

lemma M_in_Ω : cfg.M ∈ cfg.Ω := by
  apply Sphere.antipode_mem_sphere
  exact cfg.h_S_Ω.right

lemma isDiameter_SM : cfg.Ω.IsDiameter cfg.S cfg.M := by
  apply Sphere.antipode_isDiameter
  exact cfg.h_S_Ω.right

lemma Ω_radius_ne_zero : cfg.Ω.radius ≠ 0 := by
  have h := cfg.B_ne_A
  contrapose! h
  have h₁ := cfg.B_in_Ω
  have h₂ := cfg.A_in_Ω
  rw [EuclideanGeometry.mem_sphere, h, dist_eq_zero] at h₁ h₂
  rw [h₁, h₂]

lemma sbtw_SOM : Sbtw ℝ cfg.S cfg.Ω.center cfg.M := by
  exact cfg.isDiameter_SM.sbtw cfg.Ω_radius_ne_zero

lemma O_ne_A : cfg.Ω.center ≠ cfg.A := by
  have h := cfg.Ω_radius_ne_zero
  contrapose! h
  rw [← dist_eq_zero, dist_comm, EuclideanGeometry.mem_sphere.mp cfg.A_in_Ω] at h
  exact h

lemma S_ne_M : cfg.S ≠ cfg.M := by
  rw [EuclideanGeometry.Sphere.IsDiameter.left_ne_right_iff_radius_ne_zero cfg.isDiameter_SM]
  exact cfg.Ω_radius_ne_zero

lemma angle_SBM_eq : ∠ cfg.S cfg.B cfg.M = Real.pi / 2 := by
  rw [EuclideanGeometry.Sphere.thales_theorem cfg.isDiameter_SM]
  exact cfg.B_in_Ω

lemma angle_SCM_eq : ∠ cfg.S cfg.C cfg.M = Real.pi / 2 := by
  rw [EuclideanGeometry.Sphere.thales_theorem cfg.isDiameter_SM]
  exact cfg.C_in_Ω

lemma BM_eq_CM : dist cfg.B cfg.M = dist cfg.C cfg.M := by
  nth_rw 1 [dist_comm]
  nth_rw 2 [dist_comm]
  rw [← mul_self_inj (by positivity) (by positivity)]
  have h₁ := cfg.angle_SBM_eq
  have h₂ := cfg.angle_SCM_eq
  rw [← EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two] at h₁ h₂
  rw [← sub_eq_iff_eq_add'] at h₁ h₂
  rw [← h₁, ← h₂, cfg.h_S_Ω.left]

lemma M_ne_B : cfg.M ≠ cfg.B := by
  have h := cfg.B_ne_C
  contrapose! h
  rw [← h]
  rw [← dist_eq_zero] at h ⊢
  rw [dist_comm, cfg.BM_eq_CM, dist_comm] at h
  exact h

lemma M_ne_C : cfg.M ≠ cfg.C := by
  have h := cfg.B_ne_C
  contrapose! h
  rw [← h]
  rw [← dist_eq_zero] at h ⊢
  rw [dist_comm, ← cfg.BM_eq_CM] at h
  exact h

lemma angle_CMS_lt : ∠ cfg.C cfg.M cfg.S < Real.pi / 2 := by
  apply EuclideanGeometry.angle_lt_pi_div_two_of_angle_eq_pi_div_two cfg.angle_SCM_eq
  exact cfg.M_ne_C

lemma angle_SMB_lt : ∠ cfg.S cfg.M cfg.B < Real.pi / 2 := by
  rw [angle_comm]
  apply EuclideanGeometry.angle_lt_pi_div_two_of_angle_eq_pi_div_two cfg.angle_SBM_eq
  exact cfg.M_ne_B

lemma oangle_CMS_eq_oangle_SMB :
    ∡ cfg.C cfg.M cfg.S = ∡ cfg.S cfg.M cfg.B := by
  have h₁ := EuclideanGeometry.Sphere.two_zsmul_oangle_eq cfg.C_in_Ω cfg.M_in_Ω cfg.B_in_Ω cfg.h_S_Ω.right
    cfg.M_ne_C cfg.S_ne_M.symm cfg.B_ne_C cfg.S_ne_B.symm
  have h₂ := EuclideanGeometry.Sphere.two_zsmul_oangle_eq cfg.h_S_Ω.right cfg.M_in_Ω cfg.C_in_Ω cfg.B_in_Ω
    cfg.S_ne_M.symm cfg.M_ne_B cfg.S_ne_C.symm cfg.B_ne_C.symm
  have h₃ := EuclideanGeometry.oangle_eq_oangle_of_dist_eq cfg.h_S_Ω.left
  have h : (2 : ℤ) • ∡ cfg.C cfg.M cfg.S = (2 : ℤ) • ∡ cfg.S cfg.M cfg.B := by
    rw [h₁, h₂, h₃]
  have h' := cfg.angle_CMS_lt
  have h'' := cfg.angle_SMB_lt
  rw [EuclideanGeometry.angle_eq_abs_oangle_toReal cfg.M_ne_C.symm cfg.S_ne_M] at h'
  rw [EuclideanGeometry.angle_eq_abs_oangle_toReal cfg.S_ne_M cfg.M_ne_B.symm] at h''
  rw [Real.Angle.two_zsmul_eq_iff_eq_of_abs_toReal_lt_pi_div_two h' h''] at h
  exact h

lemma sphereOrder_BSCM : SphereOrder V Pt cfg.B cfg.S cfg.C cfg.M := by
  apply SphereOrder.rotate'
  constructor
  · rw [EuclideanGeometry.cospherical_iff_exists_sphere]
    use cfg.Ω
    repeat rw [Set.insert_subset_iff]
    rw [Set.singleton_subset_iff]
    constructorm* _ ∧ _
    · exact cfg.h_S_Ω.right
    · exact cfg.C_in_Ω
    · exact cfg.M_in_Ω
    · exact cfg.B_in_Ω
  · intro h
    rw [EuclideanGeometry.oangle_sign_eq_zero_iff_collinear] at h
    apply eq_of_mem_sphere_of_collinear V Pt cfg.h_S_Ω.right cfg.C_in_Ω cfg.M_in_Ω at h
    contrapose! h
    constructorm* _ ∧ _
    · exact cfg.S_ne_C
    · exact cfg.M_ne_C.symm
    · exact cfg.S_ne_M.symm
  · rw [← EuclideanGeometry.oangle_rotate_sign cfg.S cfg.C cfg.M]
    rw [EuclideanGeometry.oangle_rotate_sign cfg.S cfg.M cfg.B]
    rw [cfg.oangle_CMS_eq_oangle_SMB]

lemma sphereOrder_BASM : SphereOrder V Pt cfg.B cfg.A cfg.S cfg.M := by
  exact (cfg.sphereOrder_BASC.trans V Pt cfg.sphereOrder_BSCM.rotate).rotate

lemma sphereOrder_BACM : SphereOrder V Pt cfg.B cfg.A cfg.C cfg.M := by
  exact (cfg.sphereOrder_BASC.trans'' V Pt cfg.sphereOrder_BSCM.rotate).symm

lemma M_ne_A : cfg.M ≠ cfg.A := by
  exact cfg.sphereOrder_BASM.P₂_ne_P₄.symm

def X_set := diag_inter_set V Pt cfg.B cfg.A cfg.S cfg.M

lemma exists_X : ∃ X : Pt, X ∈ cfg.X_set := by
  exact cfg.sphereOrder_BASM.exists_diag_inter

lemma X_ne_A
    {X : Pt} (hX : X ∈ cfg.X_set) :
    X ≠ cfg.A := by
  rw [X_set, diag_inter_set_rotate] at hX
  exact cfg.sphereOrder_BASM.rotate.diag_inter_ne_P₁ V Pt hX

lemma X_ne_S
    {X : Pt} (hX : X ∈ cfg.X_set) :
    X ≠ cfg.S := by
  rw [X_set, diag_inter_set_rotate, diag_inter_set_rotate] at hX
  exact cfg.sphereOrder_BASM.symm.diag_inter_ne_P₁ V Pt hX

lemma X_ne_M
    {X : Pt} (hX : X ∈ cfg.X_set) :
    X ≠ cfg.M := by
  rw [X_set, ← diag_inter_set_rotate] at hX
  exact cfg.sphereOrder_BASM.rotate'.diag_inter_ne_P₁ V Pt hX

lemma sbtw_AXM
    {X : Pt} (hX : X ∈ cfg.X_set) : Sbtw ℝ cfg.A X cfg.M := by
  exact cfg.sphereOrder_BASM.diag_inter_sbtw' V Pt hX

lemma sbtw_BXS
    {X : Pt} (hX : X ∈ cfg.X_set) : Sbtw ℝ cfg.B X cfg.S := by
  exact cfg.sphereOrder_BASM.diag_inter_sbtw V Pt hX

lemma X_ne_O
    {X : Pt} (hX : X ∈ cfg.X_set) :
    X ≠ cfg.Ω.center := by
  have h := cfg.sphereOrder_BASM.sign_oangle₂₃₄_ne_zero
  rw [← oangle_rotate_sign] at h
  rw [← (cfg.sbtw_AXM V Pt hX).symm.oangle_eq_right] at h
  rw [← cfg.sbtw_SOM.symm.oangle_eq_left] at h
  contrapose! h
  rw [h, oangle_self_left_right, Real.Angle.sign_zero]

lemma oangle_BAM_eq_oangle_MAC :
    ∡ cfg.B cfg.A cfg.M = ∡ cfg.M cfg.A cfg.C := by
  have h₁ := EuclideanGeometry.Sphere.two_zsmul_oangle_eq cfg.B_in_Ω cfg.A_in_Ω cfg.C_in_Ω cfg.M_in_Ω
    cfg.B_ne_A.symm cfg.M_ne_A.symm cfg.B_ne_C.symm cfg.M_ne_C.symm
  have h₂ := EuclideanGeometry.Sphere.two_zsmul_oangle_eq cfg.M_in_Ω cfg.A_in_Ω cfg.B_in_Ω cfg.C_in_Ω
    cfg.M_ne_A.symm cfg.C_ne_A.symm cfg.M_ne_B.symm cfg.B_ne_C
  have h_BM_CM := cfg.BM_eq_CM
  rw [dist_comm cfg.B cfg.M, dist_comm cfg.C cfg.M] at h_BM_CM
  have h₃ := EuclideanGeometry.oangle_eq_oangle_of_dist_eq h_BM_CM
  have h : (2 : ℤ) • ∡ cfg.B cfg.A cfg.M = (2 : ℤ) • ∡ cfg.M cfg.A cfg.C := by
    rw [h₁, h₂, h₃]
  have h' : (∡ cfg.B cfg.A (M V Pt cfg)).sign = (∡ (M V Pt cfg) cfg.A cfg.C).sign := by
    rw [EuclideanGeometry.oangle_rotate_sign cfg.M cfg.B cfg.A]
    rw [← EuclideanGeometry.oangle_rotate_sign cfg.M cfg.A cfg.C]
    exact cfg.sphereOrder_BACM.rotate'.sign_oangle₁₂₃_eq_sign_oangle₃₄₁
  have h'' : (∡ cfg.B cfg.A (M V Pt cfg)).sign ≠ 0 := by
    rw [EuclideanGeometry.oangle_rotate_sign cfg.M cfg.B cfg.A]
    exact cfg.sphereOrder_BACM.rotate'.sign_oangle₁₂₃_ne_zero
  apply aux₆ h' h'' h

lemma angle_BAM_eq_angle_MAC :
  ∠ cfg.B cfg.A cfg.M = ∠ cfg.M cfg.A cfg.C := by
  exact angle_eq_of_oangle_eq V Pt cfg.oangle_BAM_eq_oangle_MAC
    cfg.B_ne_A cfg.M_ne_A cfg.M_ne_A cfg.C_ne_A

lemma oangle_BAX_eq_oangle_XAC
    {X : Pt} (hX : X ∈ cfg.X_set) :
    ∡ cfg.B cfg.A X = ∡ X cfg.A cfg.C := by
  rw [← EuclideanGeometry.oangle_add cfg.B_ne_A cfg.M_ne_A (cfg.X_ne_A V Pt hX)]
  rw [← EuclideanGeometry.oangle_add (cfg.X_ne_A V Pt hX) cfg.M_ne_A cfg.C_ne_A]
  rw [cfg.oangle_BAM_eq_oangle_MAC, add_comm, add_right_cancel_iff]
  rw [EuclideanGeometry.oangle_rev]
  rw [Wbtw.oangle₂₁₃_eq_zero (cfg.sbtw_AXM V Pt hX).wbtw]
  norm_num

lemma angle_BAX_eq_angle_XAC
    {X : Pt} (hX : X ∈ cfg.X_set) :
    ∠ cfg.B cfg.A X = ∠ X cfg.A cfg.C := by
  exact angle_eq_of_oangle_eq V Pt (cfg.oangle_BAX_eq_oangle_XAC V Pt hX)
    cfg.B_ne_A (cfg.X_ne_A V Pt hX) (cfg.X_ne_A V Pt hX) cfg.C_ne_A

lemma angle_BAM_acute : ∠ cfg.B cfg.A cfg.M < π / 2 := by
  have h := cfg.angle_BAC_acute
  apply lt_of_lt_of_le' h
  have h' := cfg.sphereOrder_BACM.angle₁₂₄_add_angle₄₂₃_eq_angle₁₂₃
  rw [← h', le_add_iff_nonneg_right]
  apply angle_nonneg

lemma angle_BAM_eq_angle_BAX
  {X : Pt} (hX : X ∈ cfg.X_set) :
  ∠ cfg.B cfg.A cfg.M = ∠ cfg.B cfg.A X := by
  rw [angle_comm, EuclideanGeometry.angle_eq_iff_oangle_eq_or_wbtw cfg.M_ne_A (cfg.X_ne_A V Pt hX)]
  right
  right
  exact (cfg.sbtw_AXM V Pt hX).wbtw

lemma angle_BAM_eq : ∠ cfg.B cfg.A cfg.M = (π - ∠ cfg.C cfg.B cfg.A - ∠ cfg.A cfg.C cfg.B) / 2 := by
  have h := cfg.sphereOrder_BACM.angle₁₂₄_add_angle₄₂₃_eq_angle₁₂₃
  rw [← cfg.angle_BAM_eq_angle_MAC, ← mul_two, ← eq_div_iff_mul_eq (by norm_num)] at h
  rw [h]
  have h' := EuclideanGeometry.angle_add_angle_add_angle_eq_pi cfg.B cfg.C_ne_A
  rw [← eq_sub_iff_add_eq'] at h'
  rw [h']
  ring

lemma XO_lt_Ω_radius {X : Pt} (hX : X ∈ cfg.X_set)
  : dist X cfg.Ω.center < cfg.Ω.radius := by
  apply Sphere.dist_le_radius_of_sbtw V Pt (cfg.sbtw_AXM V Pt hX) cfg.A_in_Ω cfg.M_in_Ω

lemma P_in_Ω : cfg.P ∈ cfg.Ω := by
  have h := cfg.h_P
  rw [Set.mem_inter_iff] at h
  exact h.right

lemma B_in_ω : cfg.B ∈ cfg.ω := by
  have h := cfg.h_ω
  rw [Set.insert_subset_iff] at h
  exact h.left

lemma D_in_ω : cfg.D ∈ cfg.ω := by
  have h := cfg.h_ω
  rw [Set.insert_subset_iff, Set.insert_subset_iff] at h
  exact h.right.left

lemma L_in_ω : cfg.L ∈ cfg.ω := by
  have h := cfg.h_ω
  rw [Set.insert_subset_iff, Set.insert_subset_iff, Set.singleton_subset_iff] at h
  exact h.right.right

lemma P_in_ω : cfg.P ∈ cfg.ω := by
  have h := cfg.h_P
  rw [Set.mem_inter_iff] at h
  exact h.left

lemma ω_radius_ne_zero : cfg.ω.radius ≠ 0 := by
  have h := cfg.h_P_ne_B
  contrapose! h
  have h₁ := cfg.B_in_ω
  have h₂ := cfg.P_in_ω
  rw [EuclideanGeometry.mem_sphere, h, dist_eq_zero] at h₁ h₂
  rw [h₁, h₂]

lemma P_ne_X {X : Pt} (hX : X ∈ cfg.X_set)
  : cfg.P ≠ X := by
  have h := cfg.XO_lt_Ω_radius V Pt hX
  contrapose! h
  apply le_of_eq
  have h' := cfg.P_in_Ω
  rw [EuclideanGeometry.mem_sphere] at h'
  rw [← h, h']

lemma perp_A_BC_eq_AE : cfg.perp_A_BC = line[ℝ, cfg.A, cfg.E] := by
  symm
  have h_E := cfg.h_E
  have h : line[ℝ, cfg.A, cfg.E] ≤ cfg.perp_A_BC := by
    apply affineSpan_le_of_subset_coe
    rw [Set.pair_subset_iff]
    constructor
    · exact cfg.h_perp_A_BC.right
    · rw [Set.mem_inter_iff] at h_E
      exact h_E.left
  apply AffineSubspace.eq_of_direction_eq_of_nonempty_of_le
  · apply Submodule.eq_of_le_of_finrank_eq (AffineSubspace.direction_le h)
    apply eq_of_le_of_ge (Submodule.finrank_mono (AffineSubspace.direction_le h))
    rw [affineSpan_pair_finrank V Pt cfg.h_E_ne_A.symm]
    have h' := cfg.h_perp_A_BC.left
    rw [Submodule.IsOrtho] at h'
    apply Submodule.finrank_mono at h'
    have h'' : finrank ℝ (affineSpan ℝ {cfg.B, cfg.C}).directionᗮ = 1 := by
      apply Submodule.finrank_add_finrank_orthogonal'
      rw [hd2.out, affineSpan_pair_finrank V Pt cfg.B_ne_C]
    rw [← h'']
    exact h'
  · rw [affineSpan_nonempty]
    apply Set.insert_nonempty
  · exact h

lemma E_in_Ω : cfg.E ∈ cfg.Ω := by
  have h := cfg.h_E
  rw [Set.mem_inter_iff] at h
  exact h.right

noncomputable def H : Pt := cfg.ABC.altitudeFoot 0

lemma collinear_HBC : Collinear ℝ {cfg.H, cfg.B, cfg.C} := by
  apply collinear_insert_of_mem_affineSpan_pair
  rw [cfg.A_opposite_BC]
  apply altitudeFoot_mem_affineSpan_faceOpposite

lemma angle_AHx_eq : ∀ x ∈ ({cfg.B, cfg.C} : Set _), ∠ cfg.A cfg.H x = Real.pi / 2 := by
  intro x hx
  rw [EuclideanGeometry.angle, ← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two]
  rw [real_inner_comm]
  apply Submodule.IsOrtho.inner_eq (vectorSpan_isOrtho_altitude_direction cfg.ABC 0)
  · have h₁ := cfg.A_opposite_BC
    simp at h₁
    apply vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan
    · rw [← h₁]
      exact mem_affineSpan _ hx
    · rw [← h₁]
      exact Collinear.mem_affineSpan_of_mem_of_ne cfg.collinear_HBC (by simp:_) (by simp:_) (by simp:_) cfg.B_ne_C
  · apply vsub_mem_vectorSpan _ (mem_altitude cfg.ABC 0) (altitudeFoot_mem_altitude cfg.ABC 0)

lemma angle_AHC_eq : ∠ cfg.A cfg.H cfg.C = Real.pi / 2 := by
  apply angle_AHx_eq
  simp

lemma angle_AHB_eq : ∠ cfg.A cfg.H cfg.B = Real.pi / 2 := by
  apply angle_AHx_eq
  simp

lemma not_sbtw_BCH : ¬Sbtw ℝ cfg.B cfg.C cfg.H := by
  intro h
  have h₁ := h.angle₁₂₃_eq_pi
  contrapose! h₁
  apply ne_of_lt
  have h₂ := oangle_add cfg.B_ne_C cfg.C_ne_A.symm h.ne_right.symm
  have h₃ := angle_le_pi_div_two_of_angle_eq_pi_div_two cfg.angle_AHC_eq
  calc ∠ cfg.B cfg.C cfg.H
      ≤ ∠ cfg.B cfg.C cfg.A + ∠ cfg.H cfg.C cfg.A := by
        rw [angle_comm cfg.H cfg.C cfg.A]
        apply angle_le_angle_add_angle
    _ < Real.pi / 2 + Real.pi / 2 := by
      rw [angle_comm cfg.B cfg.C cfg.A]
      apply add_lt_add_of_lt_of_le cfg.angle_ACB_acute h₃
    _ = Real.pi := by ring

lemma not_sbtw_CBH : ¬Sbtw ℝ cfg.C cfg.B cfg.H := by
  intro h
  have h₁ := h.angle₁₂₃_eq_pi
  contrapose! h₁
  apply ne_of_lt
  have h₂ := oangle_add cfg.B_ne_C.symm cfg.B_ne_A.symm h.ne_right.symm
  have h₃ := angle_le_pi_div_two_of_angle_eq_pi_div_two cfg.angle_AHB_eq
  calc ∠ cfg.C cfg.B cfg.H
      ≤ ∠ cfg.C cfg.B cfg.A + ∠ cfg.H cfg.B cfg.A := by
        rw [angle_comm cfg.H cfg.B cfg.A]
        apply angle_le_angle_add_angle
    _ < Real.pi / 2 + Real.pi / 2 := by
      apply add_lt_add_of_lt_of_le cfg.angle_CBA_acute h₃
    _ = Real.pi := by ring

lemma wbtw_BHC : Wbtw ℝ cfg.B cfg.H cfg.C := by
  have h₁ := cfg.not_sbtw_BCH
  have h₂ := cfg.not_sbtw_CBH
  rw [sbtw_comm] at h₂
  have h := Collinear.sbtw_or_sbtw_or_wbtw_of_ne V Pt cfg.collinear_HBC cfg.B_ne_C
  rw [wbtw_comm]
  tauto

lemma H_ne_B : cfg.H ≠ cfg.B := by
  have h := cfg.angle_CBA_acute
  contrapose! h
  apply le_of_eq
  rw [← h, angle_comm, cfg.angle_AHC_eq]

lemma H_ne_C : cfg.H ≠ cfg.C := by
  have h := cfg.angle_ACB_acute
  contrapose! h
  apply le_of_eq
  rw [← h, cfg.angle_AHB_eq]

lemma sbtw_BHC : Sbtw ℝ cfg.B cfg.H cfg.C := by
  rw [Sbtw]
  constructorm* _ ∧ _
  · exact cfg.wbtw_BHC
  · exact cfg.H_ne_B
  · exact cfg.H_ne_C

lemma AE_eq_altitude : line[ℝ, cfg.A, cfg.E] = cfg.ABC.altitude 0 := by
  apply AffineSubspace.ext_of_direction_eq
  · rw [Affine.Simplex.direction_altitude]
    rw [← Affine.Simplex.range_faceOpposite_points, ← cfg.A_opposite_BC]
    have h₁ : vectorSpan ℝ (Set.range (ABC V Pt cfg).points) = ⊤ := by
      apply AffineIndependent.vectorSpan_eq_top_of_card_eq_finrank_add_one cfg.ABC.independent
      rw [hd2.out, Fintype.card_fin]
    rw [h₁, inf_top_eq]
    have h₂ := cfg.h_perp_A_BC.left
    rw [cfg.perp_A_BC_eq_AE, Submodule.isOrtho_iff_le] at h₂
    rw [← direction_affineSpan]
    apply Submodule.eq_of_le_of_finrank_eq h₂
    apply eq_of_le_of_ge (Submodule.finrank_mono h₂)
    have h₃ := Submodule.finrank_add_finrank_orthogonal (affineSpan ℝ {cfg.B, cfg.C}).direction
    rw [affineSpan_pair_finrank V Pt cfg.h_E_ne_A.symm]
    rw [affineSpan_pair_finrank V Pt cfg.B_ne_C, hd2.out, Nat.one_add, Nat.succ_inj] at h₃
    rw [h₃]
  · use cfg.A
    apply Set.mem_inter
    · apply mem_affineSpan
      apply Set.mem_insert
    · have h := Affine.Simplex.mem_altitude cfg.ABC 0
      nth_rw 2 [ABC] at h
      simp at h
      exact h

lemma collinear_AHE : Collinear ℝ {cfg.A, cfg.H, cfg.E} := by
  rw [Set.insert_comm]
  apply collinear_insert_of_mem_affineSpan_pair
  rw [AE_eq_altitude]
  apply Affine.Simplex.altitudeFoot_mem_altitude

lemma HO_lt_Ω_radius
  : dist cfg.H cfg.Ω.center < cfg.Ω.radius := by
  apply Sphere.dist_le_radius_of_sbtw V Pt cfg.sbtw_BHC cfg.B_in_Ω cfg.C_in_Ω

lemma sbtw_AHE : Sbtw ℝ cfg.A cfg.H cfg.E := by
  apply EuclideanGeometry.sbtw_of_collinear_of_dist_center_lt_radius
    cfg.collinear_AHE cfg.A_in_Ω cfg.HO_lt_Ω_radius cfg.E_in_Ω cfg.h_E_ne_A.symm

lemma H_ne_A : cfg.H ≠ cfg.A := by
  exact cfg.sbtw_AHE.ne_left

lemma sphereOrder_BACE : SphereOrder V Pt cfg.B cfg.A cfg.C cfg.E := by
  apply sphereOrder_of_sbtw_diag_inter V Pt _ cfg.B_ne_A cfg.C_ne_A.symm
    cfg.sbtw_BHC cfg.sbtw_AHE
  rw [EuclideanGeometry.cospherical_iff_exists_sphere]
  use cfg.Ω
  repeat rw [Set.insert_subset_iff]
  rw [Set.singleton_subset_iff]
  constructorm* _ ∧ _
  · exact cfg.B_in_Ω
  · exact cfg.A_in_Ω
  · exact cfg.C_in_Ω
  · exact cfg.E_in_Ω

lemma sign_oangle_BAE_eq_sign_oangle_BAM
  : (∡ cfg.B cfg.A cfg.E).sign = (∡ cfg.B cfg.A cfg.M).sign := by
  rw [EuclideanGeometry.oangle_rotate_sign]
  rw [cfg.sphereOrder_BACE.rotate'.sign_oangle₁₂₃_eq_sign_oangle₂₃₄]
  rw [← cfg.sphereOrder_BACM.rotate'.sign_oangle₁₂₃_eq_sign_oangle₂₃₄]
  rw [← EuclideanGeometry.oangle_rotate_sign]

lemma angle_BAE_eq_BAH :
  ∠ cfg.B cfg.A cfg.E = ∠ cfg.B cfg.A cfg.H := by
  rw [angle_comm, EuclideanGeometry.angle_eq_iff_oangle_eq_or_wbtw cfg.h_E_ne_A cfg.sbtw_AHE.ne_left]
  right
  right
  exact (cfg.sbtw_AHE).wbtw

lemma angle_HBA_eq_CBA :
  ∠ cfg.H cfg.B cfg.A = ∠ cfg.C cfg.B cfg.A := by
  rw [angle_comm]
  symm
  rw [EuclideanGeometry.angle_eq_iff_oangle_eq_or_wbtw cfg.B_ne_C.symm cfg.sbtw_BHC.ne_left]
  right
  right
  exact (cfg.sbtw_BHC).wbtw

lemma angle_BAE_eq : ∠ cfg.B cfg.A cfg.E = π / 2 - ∠ cfg.C cfg.B cfg.A := by
  rw [angle_BAE_eq_BAH, ← angle_HBA_eq_CBA, eq_sub_iff_add_eq, add_comm]
  have h := EuclideanGeometry.angle_add_angle_add_angle_eq_pi cfg.A cfg.sbtw_BHC.ne_left.symm
  rw [← eq_sub_iff_add_eq] at h
  rw [h, cfg.angle_AHB_eq]
  ring

lemma angle_BAE_lt_angle_BAM : ∠ cfg.B cfg.A cfg.E < ∠ cfg.B cfg.A cfg.M := by
  rw [cfg.angle_BAM_eq, cfg.angle_BAE_eq, ← sub_pos]
  ring_nf
  rw [neg_div, mul_neg, ← sub_eq_add_neg, sub_pos, mul_lt_mul_iff_left₀ (by norm_num)]
  exact cfg.angle_ACB_lt_angle_CBA

lemma sign_oangle_EAM_eq_sign_oangle_BAE
  : (∡ cfg.E cfg.A cfg.M).sign = (∡ cfg.B cfg.A cfg.E).sign := by
  have h := EuclideanGeometry.oangle_add cfg.B_ne_A cfg.h_E_ne_A cfg.M_ne_A
  have h' := cfg.angle_BAE_lt_angle_BAM
  rw [EuclideanGeometry.angle_eq_abs_oangle_toReal cfg.B_ne_A cfg.h_E_ne_A] at h'
  rw [EuclideanGeometry.angle_eq_abs_oangle_toReal cfg.B_ne_A cfg.M_ne_A] at h'
  have h'' := cfg.sign_oangle_BAE_eq_sign_oangle_BAM
  symm
  exact aux₅ h h'' h'

lemma sphereOrder_BAME : SphereOrder V Pt cfg.B cfg.A cfg.M cfg.E := by
  apply SphereOrder.rotate
  constructor
  · rw [EuclideanGeometry.cospherical_iff_exists_sphere]
    use cfg.Ω
    repeat rw [Set.insert_subset_iff]
    rw [Set.singleton_subset_iff]
    constructorm* _ ∧ _
    · exact cfg.E_in_Ω
    · exact cfg.B_in_Ω
    · exact cfg.A_in_Ω
    · exact cfg.M_in_Ω
  · exact cfg.sphereOrder_BACE.rotate'.sign_oangle₁₂₃_ne_zero
  · rw [← EuclideanGeometry.oangle_rotate_sign]
    rw [← sign_oangle_EAM_eq_sign_oangle_BAE]
    rw [← EuclideanGeometry.oangle_rotate_sign]

lemma sphereOrder_BASE : SphereOrder V Pt cfg.B cfg.A cfg.S cfg.E := by
  exact (cfg.sphereOrder_BACE.symm.trans' V Pt cfg.sphereOrder_BASC).rotate

lemma sphereOrder_ASME : SphereOrder V Pt cfg.A cfg.S cfg.M cfg.E := by
  exact cfg.sphereOrder_BAME.symm.trans'' V Pt cfg.sphereOrder_BASM

lemma E_ne_S : cfg.E ≠ cfg.S := by
  exact cfg.sphereOrder_BASE.P₃_ne_P₄.symm

lemma E_ne_B : cfg.E ≠ cfg.B := by
  exact cfg.sphereOrder_BASE.P₁_ne_P₄.symm

lemma E_ne_C : cfg.E ≠ cfg.C := by
  exact cfg.sphereOrder_BACE.P₃_ne_P₄.symm

lemma E_ne_H : cfg.E ≠ cfg.H := by
  exact cfg.sbtw_AHE.ne_right.symm

lemma D_in_diag_inter_BASE : cfg.D ∈ diag_inter_set V Pt cfg.B cfg.A cfg.S cfg.E:= by
  have h := cfg.h_D
  constructor
  · exact h.right
  · rw [← cfg.perp_A_BC_eq_AE]
    exact h.left

lemma D_ne_B : cfg.D ≠ cfg.B := by
  exact cfg.sphereOrder_BASE.diag_inter_ne_P₁ V Pt cfg.D_in_diag_inter_BASE

lemma sbtw_BDS : Sbtw ℝ cfg.B cfg.D cfg.S := by
  exact cfg.sphereOrder_BASE.diag_inter_sbtw V Pt cfg.D_in_diag_inter_BASE

lemma sbtw_ADE : Sbtw ℝ cfg.A cfg.D cfg.E := by
  exact cfg.sphereOrder_BASE.diag_inter_sbtw' V Pt cfg.D_in_diag_inter_BASE

lemma D_ne_A : cfg.D ≠ cfg.A := by
  exact cfg.sbtw_ADE.ne_left

lemma D_ne_S : cfg.D ≠ cfg.S := by
  exact cfg.sbtw_BDS.ne_right

lemma E_ne_D : cfg.E ≠ cfg.D := by
  exact cfg.sbtw_ADE.ne_right.symm

lemma DO_lt_Ω_radius
  : dist cfg.D cfg.Ω.center < cfg.Ω.radius := by
  apply Sphere.dist_le_radius_of_sbtw V Pt cfg.sbtw_BDS cfg.B_in_Ω cfg.h_S_Ω.right

lemma P_ne_D : cfg.P ≠ cfg.D := by
  have h := cfg.DO_lt_Ω_radius
  contrapose! h
  apply le_of_eq
  have h' := cfg.P_in_Ω
  rw [EuclideanGeometry.mem_sphere] at h'
  rw [← h, h']

lemma L_ne_D : cfg.L ≠ cfg.D := by
  intro h
  have h_DBE := cfg.h_L
  rw [Set.mem_inter_iff] at h_DBE
  apply And.right at h_DBE
  rw [h] at h_DBE
  have h_DBS := cfg.h_D
  rw [Set.mem_inter_iff] at h_DBS
  apply And.right at h_DBS
  apply collinear_insert_of_mem_affineSpan_pair at h_DBE
  apply collinear_insert_of_mem_affineSpan_pair at h_DBS
  have hE := Collinear.mem_affineSpan_of_mem_of_ne h_DBE (by simp) (by simp)
    (by simp : cfg.E ∈ _) cfg.D_ne_B
  have hS := Collinear.mem_affineSpan_of_mem_of_ne h_DBS (by simp) (by simp)
    (by simp : cfg.S ∈ _) cfg.D_ne_B
  have h' := collinear_insert_insert_of_mem_affineSpan_pair hE hS
  have h_ESB : Collinear ℝ {cfg.E, cfg.S, cfg.B} := by
    apply h'.subset
    rw [Set.insert_subset_iff, Set.insert_subset_iff, Set.singleton_subset_iff]
    simp
  have h'' := eq_of_mem_sphere_of_collinear V Pt cfg.E_in_Ω cfg.h_S_Ω.right cfg.B_in_Ω h_ESB
  contrapose! h''
  constructorm* _ ∧ _
  · exact cfg.E_ne_S
  · exact cfg.S_ne_B
  · exact cfg.E_ne_B.symm

lemma prll_D_BC_eq_LD : cfg.prll_D_BC = line[ℝ, cfg.L, cfg.D] := by
  have h_L := cfg.h_L
  symm
  have h : line[ℝ, cfg.L, cfg.D] ≤ cfg.prll_D_BC := by
    apply affineSpan_le_of_subset_coe
    rw [Set.pair_subset_iff]
    constructor
    · rw [Set.mem_inter_iff] at h_L
      exact h_L.left
    · exact cfg.h_prll_D_BC.left
  apply AffineSubspace.eq_of_direction_eq_of_nonempty_of_le
  · apply Submodule.eq_of_le_of_finrank_eq (AffineSubspace.direction_le h)
    apply eq_of_le_of_ge (Submodule.finrank_mono (AffineSubspace.direction_le h))
    rw [affineSpan_pair_finrank V Pt cfg.L_ne_D]
    have h' := AffineSubspace.Parallel.direction_eq cfg.h_prll_D_BC.right
    rw [h']
    rw [affineSpan_pair_finrank V Pt cfg.B_ne_C]
  · rw [affineSpan_nonempty]
    apply Set.insert_nonempty
  · exact h

lemma P_ne_S : cfg.P ≠ cfg.S := by
  intro h
  have h' := cfg.sbtw_BDS.wbtw.collinear
  rw [← h] at h'
  have h'' := eq_of_mem_sphere_of_collinear V Pt cfg.B_in_ω cfg.D_in_ω cfg.P_in_ω h'
  contrapose! h''
  constructorm* _ ∧ _
  · exact cfg.D_ne_B.symm
  · exact cfg.P_ne_D.symm
  · exact cfg.h_P_ne_B

lemma collinear_BLE : Collinear ℝ {cfg.B, cfg.L, cfg.E} := by
  have h_L := cfg.h_L
  rw [Set.mem_inter_iff] at h_L
  apply And.right at h_L
  apply collinear_insert_of_mem_affineSpan_pair at h_L
  rw [Set.insert_comm] at h_L
  exact h_L

lemma L_ne_E : cfg.L ≠ cfg.E := by
  have h₁ := cfg.h_perp_A_BC.left
  have h₂ := cfg.h_prll_D_BC.right
  rw [cfg.perp_A_BC_eq_AE] at h₁
  rw [cfg.prll_D_BC_eq_LD] at h₂
  have hD := Collinear.mem_affineSpan_of_mem_of_ne cfg.sbtw_ADE.wbtw.collinear
    (by simp) (by simp) (by simp : cfg.D ∈ _) cfg.h_E_ne_A.symm
  rw [← affineSpan_pair_eq_of_left_mem_of_ne hD cfg.E_ne_D.symm] at h₁
  by_contra! h
  rw [h, Set.pair_comm] at h₂
  apply AffineSubspace.Parallel.direction_eq at h₂
  rw [h₂, Submodule.isOrtho_self, ← Submodule.finrank_eq_zero] at h₁
  contrapose! h₁
  rw [affineSpan_pair_finrank V Pt cfg.B_ne_C]
  norm_num

lemma H_ne_D : cfg.H ≠ cfg.D := by
  have h := cfg.sphereOrder_BASC.sign_oangle₃₄₁_ne_zero
  contrapose! h
  rw [← oangle_rotate_sign]
  rw [← Sbtw.oangle_eq_left cfg.sbtw_BHC, ← Sbtw.oangle_eq_right cfg.sbtw_BDS]
  rw [h, oangle_self_left_right, Real.Angle.sign_zero]

lemma collinear_EHD :Collinear ℝ {cfg.E, cfg.H, cfg.D} := by
  have hH := Collinear.mem_affineSpan_of_mem_of_ne cfg.sbtw_AHE.wbtw.collinear
    (by simp) (by simp) (by simp : cfg.H ∈ _) cfg.h_E_ne_A
  have hD := Collinear.mem_affineSpan_of_mem_of_ne cfg.sbtw_ADE.wbtw.collinear
    (by simp) (by simp) (by simp : cfg.D ∈ _) cfg.h_E_ne_A
  have hE := mem_affineSpan ℝ (by simp : cfg.E ∈ {cfg.E, cfg.A})
  exact collinear_triple_of_mem_affineSpan_pair hE hH hD

lemma sbtw_EHD : Sbtw ℝ cfg.E cfg.H cfg.D := by
  rcases Collinear.sbtw_or_wbtw_or_wbtw V Pt cfg.collinear_EHD with (h'|(h'|h'))
  · exact h'
  · exfalso
    have h'' := Wbtw.oangle_sign_eq_of_ne_left cfg.B h' cfg.H_ne_D
    contrapose! h''
    rw [Sbtw.oangle_eq_left cfg.sbtw_BHC]
    rw [Sbtw.oangle_eq_left cfg.sbtw_BHC, Sbtw.oangle_eq_right cfg.sbtw_BDS]
    rw [oangle_rotate_sign]
    rw [cfg.sphereOrder_BASC.symm.sign_oangle₁₂₃_eq_sign_oangle₂₃₄]
    symm
    rw [← oangle_rotate_sign]
    rw [cfg.sphereOrder_BACE.comm.sign_oangle₁₂₃_eq_sign_oangle₃₄₁]
    rw [← oangle_rotate_sign, ← oangle_swap₁₃_sign]
    rw [SignType.neg_eq_self_iff.ne]
    exact cfg.sphereOrder_BASC.rotate'.sign_oangle₁₂₃_ne_zero
  · exfalso
    have h'' := Wbtw.oangle_sign_eq_of_ne_left cfg.B h' cfg.E_ne_D.symm
    rw [← Wbtw.oangle_sign_eq_of_ne_right cfg.B h' cfg.E_ne_H] at h''
    contrapose! h''
    rw [Sbtw.oangle_eq_left cfg.sbtw_BDS, Sbtw.oangle_eq_right cfg.sbtw_BHC]
    rw [← oangle_rotate_sign]
    rw [cfg.sphereOrder_BASE.comm.sign_oangle₁₂₃_eq_sign_oangle₃₄₁]
    rw [cfg.sphereOrder_BASC.comm.symm.sign_oangle₁₂₃_eq_sign_oangle₂₃₄]
    symm
    rw [oangle_rotate_sign]
    rw [← cfg.sphereOrder_BACE.sign_oangle₁₂₃_eq_sign_oangle₃₄₁]
    rw [oangle_rotate_sign, ← oangle_swap₁₃_sign]
    rw [SignType.neg_eq_self_iff.ne]
    exact cfg.sphereOrder_BASC.comm.rotate'.sign_oangle₁₂₃_ne_zero

lemma not_collinear_EBH : ¬Collinear ℝ {cfg.E, cfg.B, cfg.H} := by
    have hEHA := cfg.sbtw_BHC.wbtw.collinear
    rw [Set.pair_comm, Set.insert_comm] at hEHA
    rw [← EuclideanGeometry.oangle_sign_eq_zero_iff_collinear] at hEHA
    rw [Real.Angle.sign_eq_zero_iff, ← Real.Angle.two_nsmul_eq_zero_iff] at hEHA
    rw [← EuclideanGeometry.oangle_sign_eq_zero_iff_collinear]
    rw [Real.Angle.sign_eq_zero_iff, ← Real.Angle.two_nsmul_eq_zero_iff]
    rw [← oangle_add cfg.E_ne_B cfg.B_ne_C.symm cfg.H_ne_B]
    rw [smul_add, hEHA, add_zero]
    rw [Real.Angle.two_nsmul_eq_zero_iff, ← Real.Angle.sign_eq_zero_iff]
    rw [oangle_rotate_sign]
    exact cfg.sphereOrder_BACE.sign_oangle₃₄₁_ne_zero

lemma oangle_LDE_eq_oangle_BHE : ∡ cfg.L cfg.D cfg.E = ∡ cfg.B cfg.H cfg.E := by
  symm
  apply EuclideanGeometry.oangle_eq_of_parallel
  · intro h
    apply collinear_insert_of_mem_affineSpan_pair at h
    rw [Set.pair_comm, Set.insert_comm, Set.pair_comm] at h
    contrapose! h
    exact cfg.not_collinear_EBH
  · exact Collinear.mem_affineSpan_of_mem_of_ne cfg.collinear_BLE
      (by simp) (by simp) (by simp : cfg.L ∈ _) cfg.E_ne_B.symm
  · apply mem_affineSpan
    simp
  · rw [← cfg.prll_D_BC_eq_LD, AffineSubspace.parallel_comm]
    have h := Collinear.mem_affineSpan_of_mem_of_ne cfg.sbtw_BHC.wbtw.collinear
      (by simp) (by simp) (by simp : cfg.H ∈ _) cfg.B_ne_C
    rw [affineSpan_pair_eq_of_right_mem_of_ne h cfg.H_ne_B]
    exact cfg.h_prll_D_BC.right
  · have h := Collinear.mem_affineSpan_of_mem_of_ne cfg.collinear_EHD
      (by simp) (by simp) (by simp : cfg.H ∈ _) cfg.E_ne_D
    rw [affineSpan_pair_eq_of_right_mem_of_ne h cfg.E_ne_H.symm]

lemma oangle_ELD_eq_oangle_EBH : ∡ cfg.E cfg.L cfg.D = ∡ cfg.E cfg.B cfg.H := by
  symm
  apply EuclideanGeometry.oangle_eq_of_parallel
  · intro h
    apply collinear_insert_of_mem_affineSpan_pair at h
    rw [Set.insert_comm] at h
    contrapose! h
    exact cfg.not_collinear_EBH
  · apply mem_affineSpan
    simp
  · exact Collinear.mem_affineSpan_of_mem_of_ne cfg.collinear_EHD
      (by simp) (by simp) (by simp : cfg.D ∈ _) cfg.E_ne_H
  · have h := Collinear.mem_affineSpan_of_mem_of_ne cfg.collinear_BLE
      (by simp) (by simp) (by simp : cfg.B ∈ _) cfg.L_ne_E.symm
    rw [affineSpan_pair_eq_of_right_mem_of_ne h cfg.E_ne_B.symm]
  · rw [Set.pair_comm cfg.D cfg.L]
    rw [← cfg.prll_D_BC_eq_LD, AffineSubspace.parallel_comm, Set.pair_comm]
    have h := Collinear.mem_affineSpan_of_mem_of_ne cfg.sbtw_BHC.wbtw.collinear
      (by simp) (by simp) (by simp : cfg.H ∈ _) cfg.B_ne_C
    rw [affineSpan_pair_eq_of_right_mem_of_ne h cfg.H_ne_B]
    exact cfg.h_prll_D_BC.right

lemma BE_lt_LE : dist cfg.B cfg.E < dist cfg.L cfg.E := by
  have hBHE := cfg.not_collinear_EBH
  have hLDE : ¬Collinear ℝ {cfg.E, cfg.L, cfg.D} := by
    rw [← EuclideanGeometry.oangle_sign_eq_zero_iff_collinear, cfg.oangle_ELD_eq_oangle_EBH]
    rw [EuclideanGeometry.oangle_sign_eq_zero_iff_collinear]
    exact hBHE
  have h₁ := EuclideanGeometry.dist_eq_dist_mul_sin_angle_div_sin_angle hBHE
  have h₂ := EuclideanGeometry.dist_eq_dist_mul_sin_angle_div_sin_angle hLDE
  rw [EuclideanGeometry.angle_eq_abs_oangle_toReal cfg.H_ne_B.symm cfg.E_ne_H] at h₁
  rw [EuclideanGeometry.angle_eq_abs_oangle_toReal cfg.E_ne_B cfg.H_ne_B] at h₁
  rw [EuclideanGeometry.angle_eq_abs_oangle_toReal cfg.L_ne_D cfg.E_ne_D] at h₂
  rw [EuclideanGeometry.angle_eq_abs_oangle_toReal cfg.L_ne_E.symm cfg.L_ne_D.symm] at h₂
  rw [dist_comm] at h₁ h₂
  rw [h₁, h₂]
  rw [cfg.oangle_LDE_eq_oangle_BHE, cfg.oangle_ELD_eq_oangle_EBH]
  rw [← EuclideanGeometry.angle_eq_abs_oangle_toReal cfg.H_ne_B.symm cfg.E_ne_H]
  rw [← EuclideanGeometry.angle_eq_abs_oangle_toReal cfg.E_ne_B cfg.H_ne_B]
  apply div_lt_div_of_pos_right _ (EuclideanGeometry.sin_pos_of_not_collinear hBHE)
  rw [Set.insert_comm, Set.pair_comm] at hBHE
  have hBHE' := EuclideanGeometry.sin_pos_of_not_collinear hBHE
  apply mul_lt_mul_of_pos_right _ hBHE'
  rw [dist_comm cfg.D cfg.E,← cfg.sbtw_EHD.wbtw.dist_add_dist,dist_comm]
  apply lt_add_of_pos_right
  rw [dist_pos]
  exact cfg.H_ne_D

lemma not_wbtw_BLE : ¬ Wbtw ℝ cfg.B cfg.L cfg.E := by
  rw [← dist_lt_dist_add_dist_iff]
  apply lt_add_of_nonneg_of_lt (by positivity) cfg.BE_lt_LE

lemma LO_gt_Ω_radius
  : cfg.Ω.radius < dist cfg.L cfg.Ω.center := by
  have h := cfg.not_wbtw_BLE
  contrapose! h
  apply EuclideanGeometry.wbtw_of_collinear_of_dist_center_le_radius
    cfg.collinear_BLE cfg.B_in_Ω h cfg.E_in_Ω cfg.E_ne_B.symm

lemma L_ne_P : cfg.L ≠ cfg.P := by
  have h := cfg.LO_gt_Ω_radius
  contrapose! h
  apply le_of_eq
  have h' := cfg.P_in_Ω
  rw [EuclideanGeometry.mem_sphere] at h'
  rw [h, h']

lemma L_ne_B : cfg.L ≠ cfg.B := by
  have h := cfg.LO_gt_Ω_radius
  contrapose! h
  apply le_of_eq
  have h' := cfg.B_in_Ω
  rw [EuclideanGeometry.mem_sphere] at h'
  rw [h, h']

lemma collinear_LPS : Collinear ℝ {cfg.L, cfg.P, cfg.S} := by
  rw [← EuclideanGeometry.oangle_sign_eq_zero_iff_collinear]
  rw [Real.Angle.sign_eq_zero_iff, ← Real.Angle.two_zsmul_eq_zero_iff]
  rw [← EuclideanGeometry.oangle_add cfg.L_ne_P cfg.h_P_ne_B.symm cfg.P_ne_S.symm]
  rw [smul_add]
  rw [EuclideanGeometry.Sphere.two_zsmul_oangle_eq cfg.B_in_Ω cfg.P_in_Ω cfg.C_in_Ω cfg.h_S_Ω.right
    cfg.h_P_ne_B cfg.P_ne_S cfg.B_ne_C.symm cfg.S_ne_C.symm]
  rw [EuclideanGeometry.Sphere.two_zsmul_oangle_eq cfg.L_in_ω cfg.P_in_ω cfg.D_in_ω cfg.B_in_ω
    cfg.L_ne_P.symm cfg.h_P_ne_B cfg.L_ne_D.symm cfg.D_ne_B]
  rw [EuclideanGeometry.oangle_rev cfg.S cfg.C cfg.B, smul_neg, ← sub_eq_add_neg, sub_eq_zero]
  rw [EuclideanGeometry.oangle_eq_oangle_of_dist_eq cfg.h_S_Ω.left]
  apply EuclideanGeometry.two_zsmul_oangle_of_parallel
  · rw [← cfg.prll_D_BC_eq_LD, Set.pair_comm]
    exact cfg.h_prll_D_BC.right
  · have h : line[ℝ, cfg.B, cfg.D] = line[ℝ, cfg.S, cfg.B] := by
      rw [Set.pair_comm]
      apply affineSpan_pair_eq_of_left_mem_of_ne _ cfg.D_ne_B
      apply Collinear.mem_affineSpan_of_mem_of_ne cfg.sbtw_BDS.wbtw.collinear (by simp) (by simp) (by simp)
      exact cfg.S_ne_B
    rw [h]

noncomputable def F := Sphere.antipode V Pt cfg.Ω cfg.A

lemma F_in_Ω : cfg.F ∈ cfg.Ω := by
  apply Sphere.antipode_mem_sphere
  exact cfg.A_in_Ω

lemma isDiameter_AF : cfg.Ω.IsDiameter cfg.A cfg.F := by
  apply Sphere.antipode_isDiameter
  exact cfg.A_in_Ω

lemma sbtw_AOF : Sbtw ℝ cfg.A cfg.Ω.center cfg.F := by
  exact cfg.isDiameter_AF.sbtw cfg.Ω_radius_ne_zero

lemma F_ne_A : cfg.F ≠ cfg.A := by
  exact cfg.sbtw_AOF.left_ne_right.symm

lemma F_ne_O : cfg.F ≠ cfg.Ω.center := by
  exact cfg.sbtw_AOF.ne_right.symm

lemma F_ne_B : cfg.F ≠ cfg.B := by
  have h := cfg.angle_ACB_acute
  contrapose! h
  apply ge_of_eq
  have h' := cfg.isDiameter_AF
  rw [h] at h'
  rw [EuclideanGeometry.Sphere.angle_eq_pi_div_two_iff_mem_sphere_of_isDiameter h']
  exact cfg.C_in_Ω

lemma F_ne_C : cfg.F ≠ cfg.C := by
  have h := cfg.angle_CBA_acute
  contrapose! h
  apply ge_of_eq
  have h' := cfg.isDiameter_AF
  rw [h, Sphere.isDiameter_comm] at h'
  rw [EuclideanGeometry.Sphere.angle_eq_pi_div_two_iff_mem_sphere_of_isDiameter h']
  exact cfg.B_in_Ω

lemma angle_ASF_eq : ∠ cfg.A cfg.S cfg.F = Real.pi / 2 := by
  rw [EuclideanGeometry.Sphere.thales_theorem cfg.isDiameter_AF]
  exact cfg.h_S_Ω.right

lemma oangle_CAO_add_oangle_ABC : 2 • ∡ cfg.C cfg.A cfg.Ω.center + 2 • ∡ cfg.A cfg.B cfg.C = Real.pi := by
  apply Sphere.two_zsmul_oangle_center_add_two_zsmul_oangle_eq_pi
  · exact cfg.A_in_Ω
  · exact cfg.B_in_Ω
  · exact cfg.C_in_Ω
  · exact cfg.B_ne_A
  · exact cfg.B_ne_C
  · exact cfg.C_ne_A.symm

lemma acute_angle_CAO : ∠ cfg.C cfg.A cfg.Ω.center < Real.pi / 2 := by
  rw [angle_eq_abs_oangle_toReal cfg.C_ne_A cfg.O_ne_A]
  apply Sphere.abs_oangle_center_right_toReal_lt_pi_div_two
  · exact cfg.A_in_Ω
  · exact cfg.C_in_Ω

lemma angle_CAO_add_angle_ABC : ∠ cfg.C cfg.A cfg.Ω.center + ∠ cfg.A cfg.B cfg.C = Real.pi / 2 := by
  have h₁ := cfg.oangle_CAO_add_oangle_ABC
  have h₂ := cfg.acute_angle_CAO
  have h₃ := cfg.angle_CBA_acute
  rw [angle_comm] at h₃
  rw [angle_eq_abs_oangle_toReal cfg.C_ne_A cfg.O_ne_A] at *
  rw [angle_eq_abs_oangle_toReal cfg.B_ne_A.symm cfg.B_ne_C.symm] at *
  exact aux₁₀ h₁ h₂ h₃

lemma oangle_BAO_add_oangle_ACB : 2 • ∡ cfg.B cfg.A cfg.Ω.center + 2 • ∡ cfg.A cfg.C cfg.B = Real.pi := by
  apply Sphere.two_zsmul_oangle_center_add_two_zsmul_oangle_eq_pi
  · exact cfg.A_in_Ω
  · exact cfg.C_in_Ω
  · exact cfg.B_in_Ω
  · exact cfg.C_ne_A
  · exact cfg.B_ne_C.symm
  · exact cfg.B_ne_A.symm

lemma acute_angle_BAO : ∠ cfg.B cfg.A cfg.Ω.center < Real.pi / 2 := by
  rw [angle_eq_abs_oangle_toReal cfg.B_ne_A cfg.O_ne_A]
  apply Sphere.abs_oangle_center_right_toReal_lt_pi_div_two
  · exact cfg.A_in_Ω
  · exact cfg.B_in_Ω

lemma angle_BAO_add_angle_ACB : ∠ cfg.B cfg.A cfg.Ω.center + ∠ cfg.A cfg.C cfg.B = Real.pi / 2 := by
  have h₁ := cfg.oangle_BAO_add_oangle_ACB
  have h₂ := cfg.acute_angle_BAO
  have h₃ := cfg.angle_ACB_acute
  rw [angle_eq_abs_oangle_toReal cfg.B_ne_A cfg.O_ne_A] at *
  rw [angle_eq_abs_oangle_toReal cfg.C_ne_A.symm cfg.B_ne_C] at *
  exact aux₁₀ h₁ h₂ h₃

lemma angle_BAO_add_angle_OAC_eq_angle_BAC :
  ∠ cfg.B cfg.A cfg.Ω.center + ∠ cfg.Ω.center cfg.A cfg.C = ∠ cfg.B cfg.A cfg.C := by
  have h₁ := cfg.angle_CAO_add_angle_ABC
  have h₂ := cfg.angle_BAO_add_angle_ACB
  rw [← eq_sub_iff_add_eq] at h₁ h₂
  rw [angle_comm cfg.C cfg.A cfg.Ω.center, angle_comm cfg.A cfg.B cfg.C] at h₁
  rw [h₁, h₂]
  ring_nf
  rw [sub_eq_add_neg, ← neg_add, ← sub_eq_add_neg, sub_eq_iff_eq_add, ← add_assoc]
  symm
  apply angle_add_angle_add_angle_eq_pi
  exact cfg.B_ne_A.symm

lemma sign_oangle_BAO_ne_zero : (∡ cfg.B cfg.A cfg.Ω.center).sign ≠ 0 := by
  rw [cfg.sbtw_AOF.oangle_eq_right]
  intro h
  rw [oangle_sign_eq_zero_iff_collinear] at h
  have h' := eq_of_mem_sphere_of_collinear V Pt cfg.B_in_Ω cfg.A_in_Ω cfg.F_in_Ω h
  contrapose! h'
  constructorm* _ ∧ _
  · exact cfg.B_ne_A
  · exact cfg.F_ne_A.symm
  · exact cfg.F_ne_B

lemma sign_oangle_OAC_ne_zero : (∡ cfg.Ω.center cfg.A cfg.C).sign ≠ 0 := by
  rw [cfg.sbtw_AOF.oangle_eq_left]
  intro h
  rw [oangle_sign_eq_zero_iff_collinear] at h
  have h' := eq_of_mem_sphere_of_collinear V Pt cfg.F_in_Ω cfg.A_in_Ω cfg.C_in_Ω h
  contrapose! h'
  constructorm* _ ∧ _
  · exact cfg.F_ne_A
  · exact cfg.C_ne_A.symm
  · exact cfg.F_ne_C.symm

lemma sign_oangle_BAF_eq_sign_oangle_FAC
  : (∡ cfg.B cfg.A cfg.F).sign = (∡ cfg.F cfg.A cfg.C).sign := by
  rw [← cfg.sbtw_AOF.oangle_eq_right, ← cfg.sbtw_AOF.oangle_eq_left]
  have h₁ := oangle_add cfg.B_ne_A  cfg.O_ne_A cfg.C_ne_A
  have h₂ := cfg.angle_BAO_add_angle_OAC_eq_angle_BAC
  rw [angle_eq_abs_oangle_toReal cfg.B_ne_A cfg.O_ne_A] at h₂
  rw [angle_eq_abs_oangle_toReal cfg.O_ne_A cfg.C_ne_A] at h₂
  rw [angle_eq_abs_oangle_toReal cfg.B_ne_A cfg.C_ne_A] at h₂
  have h_BAC := cfg.sphereOrder_BACE.sign_oangle₁₂₃_ne_zero
  rw [aux₄ cfg.sign_oangle_BAO_ne_zero h_BAC h₁ h₂]
  rw [add_comm] at h₁ h₂
  rw [aux₄ cfg.sign_oangle_OAC_ne_zero h_BAC h₁ h₂]

lemma sphereOrder_BACF : SphereOrder V Pt cfg.B cfg.A cfg.C cfg.F := by
  apply SphereOrder.rotate
  constructor
  · rw [EuclideanGeometry.cospherical_iff_exists_sphere]
    use cfg.Ω
    repeat rw [Set.insert_subset_iff]
    rw [Set.singleton_subset_iff]
    constructorm* _ ∧ _
    · exact cfg.F_in_Ω
    · exact cfg.B_in_Ω
    · exact cfg.A_in_Ω
    · exact cfg.C_in_Ω
  · rw [← oangle_rotate_sign, ← cfg.sbtw_AOF.oangle_eq_right]
    exact cfg.sign_oangle_BAO_ne_zero
  · rw [← oangle_rotate_sign, cfg.sign_oangle_BAF_eq_sign_oangle_FAC]
    rw [← oangle_rotate_sign]

lemma sphereOrder_ASCF : SphereOrder V Pt cfg.A cfg.S cfg.C cfg.F := by
  exact cfg.sphereOrder_BACF.symm.trans'' V Pt cfg.sphereOrder_BASC

lemma F_ne_S : cfg.F ≠ cfg.S := by
  exact cfg.sphereOrder_ASCF.P₂_ne_P₄.symm

lemma sphereOrder_ASFM : SphereOrder V Pt cfg.A cfg.S cfg.F cfg.M := by
  apply sphereOrder_of_sbtw_diag_inter V Pt _ cfg.S_ne_A.symm cfg.F_ne_S.symm cfg.sbtw_AOF cfg.sbtw_SOM
  rw [EuclideanGeometry.cospherical_iff_exists_sphere]
  use cfg.Ω
  repeat rw [Set.insert_subset_iff]
  rw [Set.singleton_subset_iff]
  constructorm* _ ∧ _
  · exact cfg.A_in_Ω
  · exact cfg.h_S_Ω.right
  · exact cfg.F_in_Ω
  · exact cfg.M_in_Ω

lemma sphereOrder_AFME : SphereOrder V Pt cfg.A cfg.F cfg.M cfg.E := by
  exact (cfg.sphereOrder_ASME.symm.trans V Pt cfg.sphereOrder_ASFM).rotate'

lemma F_ne_E : cfg.F ≠ cfg.E := by
  exact cfg.sphereOrder_AFME.P₂_ne_P₄

lemma oangle_BAE_eq_oangle_FAC : ∡ cfg.B cfg.A cfg.E = ∡ cfg.F cfg.A cfg.C := by
  rw [← cfg.sbtw_AOF.oangle_eq_left]
  apply oangle_eq_of_angle_eq_of_sign_eq
  · rw [cfg.angle_BAE_eq, sub_eq_iff_eq_add]
    rw [angle_comm cfg.Ω.center cfg.A cfg.C, angle_comm cfg.C cfg.B cfg.A]
    rw [cfg.angle_CAO_add_angle_ABC]
  · rw [cfg.sbtw_AOF.oangle_eq_left]
    rw [oangle_rotate_sign]
    rw [cfg.sphereOrder_BACE.rotate'.sign_oangle₁₂₃_eq_sign_oangle₂₃₄]
    rw [cfg.sphereOrder_BACF.sign_oangle₁₂₃_eq_sign_oangle₂₃₄]
    rw [oangle_rotate_sign]

lemma oangle_SEF_eq_oangle_EFS : (2 : ℤ) • ∡ cfg.S cfg.E (F V Pt cfg) = (2 : ℤ) • ∡ cfg.E (F V Pt cfg) cfg.S := by
  rw [EuclideanGeometry.Sphere.two_zsmul_oangle_eq cfg.h_S_Ω.right cfg.E_in_Ω cfg.B_in_Ω cfg.F_in_Ω
    cfg.E_ne_S cfg.F_ne_E.symm cfg.S_ne_B.symm cfg.F_ne_B.symm]
  rw [EuclideanGeometry.Sphere.two_zsmul_oangle_eq cfg.E_in_Ω cfg.F_in_Ω cfg.C_in_Ω cfg.h_S_Ω.right
    cfg.F_ne_E cfg.F_ne_S cfg.E_ne_C.symm cfg.S_ne_C.symm]
  rw [← oangle_add cfg.S_ne_B cfg.B_ne_C.symm cfg.F_ne_B]
  rw [← oangle_add cfg.E_ne_C cfg.B_ne_C cfg.S_ne_C]
  rw [smul_add, smul_add]
  rw [EuclideanGeometry.Sphere.two_zsmul_oangle_eq cfg.C_in_Ω cfg.B_in_Ω cfg.A_in_Ω cfg.F_in_Ω
    cfg.B_ne_C cfg.F_ne_B.symm cfg.C_ne_A.symm cfg.F_ne_A.symm]
  rw [EuclideanGeometry.Sphere.two_zsmul_oangle_eq cfg.E_in_Ω cfg.C_in_Ω cfg.A_in_Ω cfg.B_in_Ω
    cfg.E_ne_C.symm cfg.B_ne_C.symm cfg.h_E_ne_A.symm cfg.B_ne_A.symm]
  rw [oangle_rev cfg.F cfg.A cfg.C, oangle_rev cfg.B cfg.A cfg.E]
  rw [oangle_BAE_eq_oangle_FAC]
  rw [EuclideanGeometry.oangle_eq_oangle_of_dist_eq cfg.h_S_Ω.left.symm]
  abel

def K'_set := (cfg.prll_D_BC : Set Pt) ∩ (line[ℝ, cfg.S, cfg.F] : Set Pt)
def K_set := diag_inter_set V Pt cfg.A cfg.S cfg.C cfg.F

lemma K'_ne_D {K' : Pt} (hK' : K' ∈ cfg.K'_set)
  : K' ≠ cfg.D := by
  intro h
  rw [K'_set, Set.mem_inter_iff] at hK'
  have hSF := collinear_insert_of_mem_affineSpan_pair hK'.right
  rw [h] at hSF
  have hSB := cfg.sbtw_BDS.wbtw.collinear
  have hF : cfg.F ∈ affineSpan ℝ {cfg.S, cfg.D} :=
    Collinear.mem_affineSpan_of_mem_of_ne hSF (by simp) (by simp) (by simp) cfg.D_ne_S.symm
  have hB : cfg.B ∈ affineSpan ℝ {cfg.S, cfg.D} :=
    Collinear.mem_affineSpan_of_mem_of_ne hSB (by simp) (by simp) (by simp) cfg.D_ne_S.symm
  have hS : cfg.S ∈ affineSpan ℝ {cfg.S, cfg.D} := by
    apply mem_affineSpan
    simp
  have h' := collinear_triple_of_mem_affineSpan_pair hF hB hS
  have h'' := eq_of_mem_sphere_of_collinear V Pt cfg.F_in_Ω cfg.B_in_Ω cfg.h_S_Ω.right h'
  contrapose! h''
  constructorm* _ ∧ _
  · exact cfg.F_ne_B
  · exact cfg.S_ne_B.symm
  · exact cfg.F_ne_S.symm

lemma two_zsmul_oangle_ADK' {K' : Pt} (hK' : K' ∈ cfg.K'_set)
  : (2 : ℤ) • ∡ cfg.A cfg.D K' = Real.pi := by
  have h_K'LD := hK'.left
  rw [cfg.prll_D_BC_eq_LD] at h_K'LD
  have h_DAE : cfg.D ∈ affineSpan ℝ {cfg.A, cfg.E} :=
    cfg.sbtw_ADE.wbtw.collinear.mem_affineSpan_of_mem_of_ne
    (by simp) (by simp) (by simp) cfg.h_E_ne_A.symm
  have h_HAE : cfg.H ∈ affineSpan ℝ {cfg.A, cfg.E} :=
    cfg.sbtw_AHE.wbtw.collinear.mem_affineSpan_of_mem_of_ne
    (by simp) (by simp) (by simp) cfg.h_E_ne_A.symm
  have h_HBC : cfg.H ∈ affineSpan ℝ {cfg.B, cfg.C} :=
    cfg.sbtw_BHC.wbtw.collinear.mem_affineSpan_of_mem_of_ne
    (by simp) (by simp) (by simp) cfg.B_ne_C
  have h_ADK'_AHC : (2 : ℤ) • ∡ cfg.A cfg.D K' = (2 : ℤ) • ∡ cfg.A cfg.H cfg.C := by
    apply EuclideanGeometry.two_zsmul_oangle_of_parallel
    · rw [affineSpan_pair_eq_of_right_mem_of_ne h_DAE cfg.D_ne_A]
      rw [affineSpan_pair_eq_of_right_mem_of_ne h_HAE cfg.H_ne_A]
    · rw [affineSpan_pair_eq_of_left_mem_of_ne h_K'LD (cfg.K'_ne_D V Pt hK')]
      rw [← cfg.prll_D_BC_eq_LD, Set.pair_comm]
      rw [affineSpan_pair_eq_of_left_mem_of_ne h_HBC cfg.H_ne_C]
      exact cfg.h_prll_D_BC.right
  rw [h_ADK'_AHC, Real.Angle.two_zsmul_eq_pi_iff, ← Real.Angle.abs_toReal_eq_pi_div_two_iff]
  rw [← EuclideanGeometry.angle_eq_abs_oangle_toReal cfg.H_ne_A.symm cfg.H_ne_C.symm]
  exact cfg.angle_AHC_eq

lemma K'_ne_A {K' : Pt} (hK' : K' ∈ cfg.K'_set)
  : K' ≠ cfg.A := by
  have h := cfg.two_zsmul_oangle_ADK' V Pt hK'
  contrapose! h
  rw [h, oangle_self_left_right, smul_zero]
  exact Real.Angle.pi_ne_zero.symm

lemma K'_ne_S {K' : Pt} (hK' : K' ∈ cfg.K'_set)
  : K' ≠ cfg.S := by
  intro h
  have h_K'LD := hK'.left
  rw [cfg.prll_D_BC_eq_LD, h] at h_K'LD
  have h_SLD := collinear_insert_of_mem_affineSpan_pair h_K'LD
  have hL : cfg.L ∈ affineSpan ℝ {cfg.S, cfg.D} :=
    Collinear.mem_affineSpan_of_mem_of_ne h_SLD (by simp) (by simp) (by simp) cfg.D_ne_S.symm
  have hSB := cfg.sbtw_BDS.wbtw.collinear
  have hB : cfg.B ∈ affineSpan ℝ {cfg.S, cfg.D} :=
    Collinear.mem_affineSpan_of_mem_of_ne hSB (by simp) (by simp) (by simp) cfg.D_ne_S.symm
  have hD : cfg.D ∈ affineSpan ℝ {cfg.S, cfg.D} := by
    apply mem_affineSpan
    simp
  have h' := collinear_triple_of_mem_affineSpan_pair hL hB hD
  have h'' := eq_of_mem_sphere_of_collinear V Pt cfg.L_in_ω cfg.B_in_ω cfg.D_in_ω h'
  contrapose! h''
  constructorm* _ ∧ _
  · exact cfg.L_ne_B
  · exact cfg.D_ne_B.symm
  · exact cfg.L_ne_D.symm

lemma cospherical_DASK' {K' : Pt} (hK' : K' ∈ cfg.K'_set)
  : Cospherical {cfg.A, cfg.D, cfg.S, K'} := by
  rw [K'_set, Set.mem_inter_iff] at hK'
  apply EuclideanGeometry.cospherical_of_two_zsmul_oangle_eq_of_not_collinear
  · rw [cfg.two_zsmul_oangle_ADK' V Pt hK']
    rw [← oangle_add cfg.S_ne_A.symm cfg.F_ne_S (cfg.K'_ne_S V Pt hK')]
    rw [smul_add]
    have h_S := cfg.angle_ASF_eq
    rw [angle_eq_abs_oangle_toReal cfg.S_ne_A.symm cfg.F_ne_S] at h_S
    rw [Real.Angle.abs_toReal_eq_pi_div_two_iff, ← Real.Angle.two_zsmul_eq_pi_iff] at h_S
    rw [h_S, ← sub_eq_iff_eq_add', sub_self]
    symm
    rw [Real.Angle.two_zsmul_eq_zero_iff, oangle_eq_zero_or_eq_pi_iff_collinear]
    rw [Set.pair_comm, Set.insert_comm, Set.pair_comm]
    apply collinear_insert_of_mem_affineSpan_pair
    exact hK'.right
  · rw [← oangle_sign_eq_zero_iff_collinear, Real.Angle.sign_eq_zero_iff, ← Real.Angle.two_zsmul_eq_zero_iff]
    rw [cfg.two_zsmul_oangle_ADK' V Pt hK']
    apply Real.Angle.pi_ne_zero

lemma K'_in_K_set {K' : Pt} (hK' : K' ∈ cfg.K'_set)
  : K' ∈ cfg.K_set := by
  rw [K_set, diag_inter_set, Set.mem_inter_iff]
  rw [K'_set, Set.mem_inter_iff] at hK'
  constructor
  · have h₁ := cfg.cospherical_DASK' V Pt hK'
    rw [Set.pair_comm] at h₁
    nth_rw 2 [Set.insert_comm] at h₁
    nth_rw 1 [Set.insert_comm] at h₁
    have h₂ := cfg.sphereOrder_BASC.cospherical
    nth_rw 2 [Set.insert_comm] at h₂
    nth_rw 1 [Set.insert_comm] at h₂
    have h_DSB : cfg.D ∈ affineSpan ℝ {cfg.S, cfg.B} :=
      cfg.sbtw_BDS.wbtw.collinear.mem_affineSpan_of_mem_of_ne
      (by simp) (by simp) (by simp) cfg.S_ne_B
    have h_K'LD := hK'.left
    rw [cfg.prll_D_BC_eq_LD] at h_K'LD
    have h_K'AC : Collinear ℝ {K', cfg.A, cfg.C} := by
      rw [← EuclideanGeometry.oangle_sign_eq_zero_iff_collinear]
      rw [Real.Angle.sign_eq_zero_iff, ← Real.Angle.two_zsmul_eq_zero_iff]
      rw [← EuclideanGeometry.oangle_add (cfg.K'_ne_A V Pt hK') cfg.S_ne_A cfg.C_ne_A]
      rw [smul_add]
      rw [EuclideanGeometry.Cospherical.two_zsmul_oangle_eq h₁
        (cfg.K'_ne_A V Pt hK').symm cfg.S_ne_A.symm (cfg.K'_ne_D V Pt hK').symm cfg.D_ne_S]
      rw [← EuclideanGeometry.Cospherical.two_zsmul_oangle_eq h₂
        cfg.S_ne_B.symm cfg.B_ne_C cfg.S_ne_A.symm cfg.C_ne_A.symm]
      rw [← sub_neg_eq_add, ← smul_neg, ← oangle_rev, sub_eq_zero]
      apply EuclideanGeometry.two_zsmul_oangle_of_parallel
      · rw [affineSpan_pair_eq_of_left_mem_of_ne h_K'LD (cfg.K'_ne_D V Pt hK')]
        rw [← cfg.prll_D_BC_eq_LD, Set.pair_comm]
        exact cfg.h_prll_D_BC.right
      · rw [affineSpan_pair_eq_of_right_mem_of_ne h_DSB cfg.D_ne_S]
    apply h_K'AC.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) cfg.C_ne_A.symm
  · exact hK'.right

lemma sbtw_AKC
    {K : Pt} (hK : K ∈ cfg.K_set) : Sbtw ℝ cfg.A K cfg.C := by
  exact cfg.sphereOrder_ASCF.diag_inter_sbtw V Pt hK

lemma KO_lt_Ω_radius {K : Pt} (hK : K ∈ cfg.K_set)
  : dist K cfg.Ω.center < cfg.Ω.radius := by
  apply Sphere.dist_le_radius_of_sbtw V Pt (cfg.sbtw_AKC V Pt hK) cfg.A_in_Ω cfg.C_in_Ω

lemma P_ne_F : cfg.P ≠ cfg.F := by
  have h := cfg.LO_gt_Ω_radius
  contrapose! h
  apply le_of_lt
  have hL : cfg.L ∈ cfg.K'_set := by
    rw [K'_set, Set.mem_inter_iff]
    constructor
    · rw [cfg.prll_D_BC_eq_LD]
      apply mem_affineSpan
      simp
    · rw [← h]
      exact cfg.collinear_LPS.mem_affineSpan_of_mem_of_ne
        (by simp) (by simp) (by simp) cfg.P_ne_S.symm
  apply cfg.K'_in_K_set at hL
  exact cfg.KO_lt_Ω_radius V Pt hL

lemma collinear_PDF : Collinear ℝ {cfg.P, cfg.D, cfg.F} := by
  rw [Set.insert_comm]
  have h_LPS := cfg.collinear_LPS
  have h_BLE := cfg.collinear_BLE
  rw [Set.pair_comm, Set.insert_comm] at h_BLE
  rw [← oangle_sign_eq_zero_iff_collinear] at h_LPS h_BLE ⊢
  rw [Real.Angle.sign_eq_zero_iff, ← Real.Angle.two_zsmul_eq_zero_iff] at h_LPS h_BLE ⊢
  rw [← oangle_add cfg.P_ne_D.symm cfg.L_ne_P cfg.P_ne_F.symm]
  rw [← oangle_add cfg.L_ne_P cfg.P_ne_S.symm cfg.P_ne_F.symm]
  rw [smul_add, smul_add, h_LPS, zero_add]
  rw [EuclideanGeometry.Sphere.two_zsmul_oangle_eq cfg.D_in_ω cfg.P_in_ω cfg.B_in_ω cfg.L_in_ω
    cfg.P_ne_D cfg.L_ne_P.symm cfg.D_ne_B.symm cfg.L_ne_B.symm]
  rw [← oangle_add cfg.D_ne_B cfg.E_ne_B cfg.L_ne_B]
  rw [smul_add, h_BLE, add_zero]
  rw [cfg.sbtw_BDS.oangle_eq_left]
  rw [EuclideanGeometry.Sphere.two_zsmul_oangle_eq cfg.h_S_Ω.right cfg.B_in_Ω cfg.F_in_Ω cfg.E_in_Ω
    cfg.S_ne_B.symm cfg.E_ne_B.symm cfg.F_ne_S cfg.F_ne_E]
  rw [EuclideanGeometry.Sphere.two_zsmul_oangle_eq cfg.h_S_Ω.right cfg.P_in_Ω cfg.E_in_Ω cfg.F_in_Ω
    cfg.P_ne_S cfg.P_ne_F cfg.E_ne_S cfg.F_ne_E.symm]
  rw [oangle_rev, smul_neg, neg_add_eq_sub, sub_eq_zero]
  exact cfg.oangle_SEF_eq_oangle_EFS

lemma sbtw_PDF : Sbtw ℝ cfg.P cfg.D cfg.F := by
  apply EuclideanGeometry.sbtw_of_collinear_of_dist_center_lt_radius
    cfg.collinear_PDF cfg.P_in_Ω cfg.DO_lt_Ω_radius cfg.F_in_Ω cfg.P_ne_F

lemma F_ne_D : cfg.F ≠ cfg.D := by
  exact cfg.sbtw_PDF.ne_right.symm

lemma sphereOrder_PAFE : SphereOrder V Pt cfg.P cfg.A cfg.F cfg.E := by
  apply SphereOrder.rotate'
  apply sphereOrder_of_sbtw_diag_inter V Pt _ cfg.F_ne_A.symm cfg.F_ne_E cfg.sbtw_ADE cfg.sbtw_PDF.symm
  rw [EuclideanGeometry.cospherical_iff_exists_sphere]
  use cfg.Ω
  repeat rw [Set.insert_subset_iff]
  rw [Set.singleton_subset_iff]
  constructorm* _ ∧ _
  · exact cfg.A_in_Ω
  · exact cfg.F_in_Ω
  · exact cfg.E_in_Ω
  · exact cfg.P_in_Ω

lemma P_ne_A : cfg.P ≠ cfg.A := by
  exact cfg.sphereOrder_PAFE.P₁_ne_P₂

lemma sphereOrder_PAFM : SphereOrder V Pt cfg.P cfg.A cfg.F cfg.M := by
  exact cfg.sphereOrder_PAFE.rotate'.trans' V Pt cfg.sphereOrder_AFME

lemma P_ne_M : cfg.P ≠ cfg.M := by
  exact cfg.sphereOrder_PAFM.P₁_ne_P₄

lemma sphereOrder_PSFM : SphereOrder V Pt cfg.P cfg.S cfg.F cfg.M := by
  exact (cfg.sphereOrder_ASFM.trans' V Pt cfg.sphereOrder_PAFM.symm).rotate'

def Z_set := diag_inter_set V Pt cfg.P cfg.S cfg.F cfg.M

lemma exists_Z : ∃ Z : Pt, Z ∈ cfg.Z_set := by
  exact cfg.sphereOrder_PSFM.exists_diag_inter

lemma sbtw_PZF {Z : Pt} (hZ : Z ∈ cfg.Z_set)
  : Sbtw ℝ cfg.P Z cfg.F := by
  exact cfg.sphereOrder_PSFM.diag_inter_sbtw V Pt hZ

lemma Z_ne_F {Z : Pt} (hZ : Z ∈ cfg.Z_set)
  : Z ≠ cfg.F := by
  exact (cfg.sbtw_PZF V Pt hZ).ne_right

lemma sbtw_SZM {Z : Pt} (hZ : Z ∈ cfg.Z_set)
  : Sbtw ℝ cfg.S Z cfg.M := by
  exact cfg.sphereOrder_PSFM.diag_inter_sbtw' V Pt hZ

lemma Z_ne_S {Z : Pt} (hZ : Z ∈ cfg.Z_set)
  : Z ≠ cfg.S := by
  exact (cfg.sbtw_SZM V Pt hZ).ne_left

lemma Z_ne_D {Z : Pt} (hZ : Z ∈ cfg.Z_set)
  : Z ≠ cfg.D := by
  have h := cfg.sphereOrder_BASM.symm.sign_oangle₁₂₃_ne_zero
  rw [oangle_rotate_sign] at h
  rw [← cfg.sbtw_BDS.symm.oangle_eq_left] at h
  rw [← (cfg.sbtw_SZM V Pt hZ).oangle_eq_right] at h
  exact (left_ne_right_of_oangle_sign_ne_zero h).symm

lemma Z_ne_O {Z : Pt} (hZ : Z ∈ cfg.Z_set)
  : Z ≠ cfg.Ω.center := by
  have h := cfg.sphereOrder_PAFM.symm.sign_oangle₃₄₁_ne_zero
  rw [← oangle_rotate_sign] at h
  rw [← cfg.sbtw_AOF.symm.oangle_eq_left] at h
  rw [← (cfg.sbtw_PZF V Pt hZ).symm.oangle_eq_right] at h
  exact (left_ne_right_of_oangle_sign_ne_zero h).symm

lemma X_ne_D
    {X : Pt} (hX : X ∈ cfg.X_set) :
    X ≠ cfg.D := by
  have h := cfg.sphereOrder_BAME.sign_oangle₂₃₄_ne_zero
  rw [oangle_rotate_sign] at h
  rw [← cfg.sbtw_ADE.oangle_eq_left] at h
  rw [← (cfg.sbtw_AXM V Pt hX).oangle_eq_right] at h
  exact (left_ne_right_of_oangle_sign_ne_zero h).symm

lemma collinear_SXD {X : Pt} (hX : X ∈ cfg.X_set)
  : Collinear ℝ {cfg.S, X, cfg.D} := by
  have hS := mem_affineSpan ℝ (by simp : cfg.S ∈ {cfg.S, cfg.B})
  have hX := Collinear.mem_affineSpan_of_mem_of_ne (cfg.sbtw_BXS V Pt hX).wbtw.collinear
    (by simp) (by simp) (by simp : X ∈ _) cfg.S_ne_B
  have hD := Collinear.mem_affineSpan_of_mem_of_ne cfg.sbtw_BDS.wbtw.collinear
    (by simp) (by simp) (by simp : cfg.D ∈ _) cfg.S_ne_B
  exact collinear_triple_of_mem_affineSpan_pair hS hX hD

lemma sbtw_SXD {X : Pt} (hX : X ∈ cfg.X_set)
  : Sbtw ℝ cfg.S X cfg.D := by
  rcases Collinear.sbtw_or_wbtw_or_wbtw V Pt (cfg.collinear_SXD V Pt hX) with (h'|(h'|h'))
  · exact h'
  · exfalso
    have h'' := Wbtw.oangle_sign_eq_of_ne_left cfg.A h' (cfg.X_ne_D V Pt hX)
    rw [cfg.sbtw_ADE.oangle_eq_right] at h''
    rw [(cfg.sbtw_AXM V Pt hX).oangle_eq_left] at h''
    rw [(cfg.sbtw_AXM V Pt hX).oangle_eq_left] at h''
    rw [← oangle_rotate_sign, ← oangle_swap₁₃_sign] at h''
    rw [← cfg.sphereOrder_AFME.sign_oangle₁₂₃_eq_sign_oangle₃₄₁] at h''
    rw [← oangle_rotate_sign] at h''
    rw [cfg.sphereOrder_ASFM.symm.sign_oangle₁₂₃_eq_sign_oangle₂₃₄] at h''
    rw [SignType.neg_eq_self_iff] at h''
    contrapose! h''
    exact cfg.sphereOrder_ASFM.rotate'.sign_oangle₁₂₃_ne_zero
  · exfalso
    have h'' := Wbtw.oangle_sign_eq_of_ne_left cfg.A h' cfg.D_ne_S
    rw [← Wbtw.oangle_sign_eq_of_ne_right cfg.A h' (cfg.X_ne_S V Pt hX).symm] at h''
    rw [cfg.sbtw_ADE.oangle_eq_left] at h''
    rw [(cfg.sbtw_AXM V Pt hX).oangle_eq_right] at h''
    rw [cfg.sphereOrder_ASME.rotate'.sign_oangle₁₂₃_eq_sign_oangle₂₃₄] at h''
    rw [oangle_rotate_sign, ← oangle_swap₁₃_sign cfg.M cfg.A cfg.S] at h''
    rw [SignType.self_eq_neg_iff] at h''
    contrapose! h''
    exact cfg.sphereOrder_ASFM.rotate.sign_oangle₃₄₁_ne_zero

lemma S_ne_O : cfg.S ≠ cfg.Ω.center := by
  exact cfg.sbtw_SOM.ne_left.symm

lemma collinear_SOZ {Z : Pt} (hZ : Z ∈ cfg.Z_set)
  : Collinear ℝ {cfg.S, cfg.Ω.center, Z} := by
  have hS := mem_affineSpan ℝ (by simp : cfg.S ∈ {cfg.S, cfg.M})
  have hO := Collinear.mem_affineSpan_of_mem_of_ne cfg.sbtw_SOM.wbtw.collinear
    (by simp) (by simp) (by simp : cfg.Ω.center ∈ _) cfg.S_ne_M
  have hZ := Collinear.mem_affineSpan_of_mem_of_ne (cfg.sbtw_SZM V Pt hZ).wbtw.collinear
    (by simp) (by simp) (by simp : Z ∈ _) cfg.S_ne_M
  exact collinear_triple_of_mem_affineSpan_pair hS hO hZ

lemma sbtw_SOZ {Z : Pt} (hZ : Z ∈ cfg.Z_set)
  : Sbtw ℝ cfg.S cfg.Ω.center Z := by
  rcases Collinear.sbtw_or_wbtw_or_wbtw V Pt (cfg.collinear_SOZ V Pt hZ) with (h'|(h'|h'))
  · exact h'
  · have h'' := Wbtw.oangle_sign_eq_of_ne_left cfg.F h' (cfg.Z_ne_O V Pt hZ).symm
    rw [cfg.sbtw_AOF.symm.oangle_eq_left] at h''
    rw [cfg.sbtw_AOF.symm.oangle_eq_left] at h''
    rw [(cfg.sbtw_PZF V Pt hZ).symm.oangle_eq_right] at h''
    rw [oangle_rotate_sign] at h''
    rw [cfg.sphereOrder_PAFM.sign_oangle₁₂₃_eq_sign_oangle₂₃₄] at h''
    rw [← oangle_rotate_sign] at h''
    rw [cfg.sphereOrder_ASFM.symm.sign_oangle₁₂₃_eq_sign_oangle₃₄₁] at h''
    rw [← oangle_swap₁₃_sign cfg.S cfg.F cfg.A, oangle_rotate_sign cfg.A cfg.S cfg.F] at h''
    rw [SignType.self_eq_neg_iff] at h''
    contrapose! h''
    exact cfg.sphereOrder_ASFM.sign_oangle₁₂₃_ne_zero
  · have h'' := Wbtw.oangle_sign_eq_of_ne_left cfg.F h' (cfg.Z_ne_S V Pt hZ)
    rw [← Wbtw.oangle_sign_eq_of_ne_right cfg.F h' cfg.S_ne_O] at h''
    rw [cfg.sbtw_AOF.symm.oangle_eq_right] at h''
    rw [(cfg.sbtw_PZF V Pt hZ).symm.oangle_eq_left] at h''
    rw [← oangle_rotate_sign, ← oangle_swap₁₃_sign] at h''
    rw [cfg.sphereOrder_PSFM.sign_oangle₁₂₃_eq_sign_oangle₂₃₄] at h''
    rw [← cfg.sphereOrder_ASFM.sign_oangle₁₂₃_eq_sign_oangle₂₃₄] at h''
    rw [oangle_rotate_sign cfg.A cfg.S (F V Pt cfg)] at h''
    rw [SignType.neg_eq_self_iff] at h''
    contrapose! h''
    exact cfg.sphereOrder_ASFM.sign_oangle₁₂₃_ne_zero

lemma oangle_MAE_eq_oangle_AMS
  : ∡ cfg.M cfg.A cfg.E = ∡ cfg.A cfg.M cfg.S := by
  apply aux₆
  · rw [← oangle_rotate_sign, ← oangle_swap₁₃_sign]
    rw [← cfg.sphereOrder_ASME.sign_oangle₁₂₃_eq_sign_oangle₃₄₁]
    rw [← oangle_rotate_sign, oangle_swap₁₃_sign]
  · rw [← oangle_rotate_sign, ← oangle_swap₁₃_sign]
    rw [SignType.neg_eq_zero_iff.ne]
    exact cfg.sphereOrder_ASME.sign_oangle₃₄₁_ne_zero
  · rw [← cfg.sbtw_SOM.symm.oangle_eq_right]
    have h : dist cfg.Ω.center cfg.A = dist cfg.Ω.center cfg.M := by
      rw [mem_sphere'.mp cfg.A_in_Ω]
      rw [mem_sphere'.mp cfg.M_in_Ω]
    rw [← EuclideanGeometry.oangle_eq_oangle_of_dist_eq h]
    rw [cfg.sbtw_AOF.oangle_eq_left]
    rw [← oangle_add cfg.M_ne_A cfg.B_ne_A cfg.h_E_ne_A]
    rw [← oangle_add cfg.F_ne_A cfg.C_ne_A cfg.M_ne_A]
    rw [cfg.oangle_BAE_eq_oangle_FAC]
    rw [oangle_rev cfg.M cfg.A cfg.C]
    rw [oangle_rev cfg.B cfg.A cfg.M]
    rw [cfg.oangle_BAM_eq_oangle_MAC]
    abel

lemma DX_to_XS_eq_DA_to_MS {X : Pt} (hX : X ∈ cfg.X_set)
  : dist cfg.D X / dist X cfg.S = dist cfg.D cfg.A / dist cfg.M cfg.S := by
  have hXS : dist X cfg.S ≠ 0 := by
    rw [dist_ne_zero]
    exact (cfg.X_ne_S V Pt hX)
  have hOS : dist cfg.M cfg.S ≠ 0 := by
    rw [dist_ne_zero]
    exact cfg.S_ne_M.symm
  field_simp
  rw [dist_comm X cfg.S, dist_comm cfg.D cfg.A]
  have h₁ : ¬Collinear ℝ {cfg.D, X, cfg.A} := by
    rw [← EuclideanGeometry.oangle_sign_eq_zero_iff_collinear]
    rw [← oangle_rotate_sign]
    rw [cfg.sbtw_ADE.oangle_eq_right]
    rw [(cfg.sbtw_AXM V Pt hX).oangle_eq_left]
    rw [← oangle_rotate_sign]
    rw [← oangle_swap₁₃_sign, SignType.neg_eq_zero_iff]
    exact cfg.sphereOrder_ASME.sign_oangle₃₄₁_ne_zero
  have h₂ : ¬Collinear ℝ {cfg.S, X, cfg.M} := by
    rw [← EuclideanGeometry.oangle_sign_eq_zero_iff_collinear]
    rw [← oangle_rotate_sign]
    rw [(cfg.sbtw_AXM V Pt hX).symm.oangle_eq_left]
    rw [oangle_rotate_sign]
    rw [← oangle_swap₁₃_sign, SignType.neg_eq_zero_iff]
    exact cfg.sphereOrder_ASFM.rotate.sign_oangle₃₄₁_ne_zero
  rw [EuclideanGeometry.dist_eq_dist_mul_sin_angle_div_sin_angle h₁]
  rw [EuclideanGeometry.dist_eq_dist_mul_sin_angle_div_sin_angle h₂]
  rw [EuclideanGeometry.angle_eq_abs_oangle_toReal (cfg.X_ne_A V Pt hX) cfg.D_ne_A]
  rw [EuclideanGeometry.angle_eq_abs_oangle_toReal (cfg.X_ne_D V Pt hX).symm (cfg.X_ne_A V Pt hX).symm]
  rw [EuclideanGeometry.angle_eq_abs_oangle_toReal (cfg.X_ne_M V Pt hX) cfg.S_ne_M]
  rw [EuclideanGeometry.angle_eq_abs_oangle_toReal (cfg.X_ne_S V Pt hX).symm (cfg.X_ne_M V Pt hX).symm]
  rw [Sbtw.oangle_eq_left_right (cfg.sbtw_SXD V Pt hX).symm (cfg.sbtw_AXM V Pt hX)]
  rw [cfg.sbtw_ADE.oangle_eq_right]
  rw [(cfg.sbtw_AXM V Pt hX).oangle_eq_left]
  rw [(cfg.sbtw_AXM V Pt hX).symm.oangle_eq_left]
  rw [cfg.oangle_MAE_eq_oangle_AMS]
  ring

lemma AE_paralell_SM : line[ℝ, cfg.A, cfg.E] ∥ line[ℝ, cfg.S, cfg.M] := by
  rw [Set.pair_comm cfg.A cfg.E, Set.pair_comm cfg.S cfg.M]
  apply parallel_of_two_zsmul_oangle_eq V Pt cfg.h_E_ne_A cfg.M_ne_A.symm cfg.S_ne_M.symm
  rw [oangle_rev, oangle_MAE_eq_oangle_AMS, ← oangle_rev]

lemma oangle_OZF_eq_oangle_ADF {Z : Pt} (hZ : Z ∈ cfg.Z_set)
  : ∡ cfg.Ω.center Z cfg.F = ∡ cfg.A cfg.D cfg.F := by
  apply oangle_eq_of_parallel
  · intro h
    apply collinear_insert_of_mem_affineSpan_pair at h
    rw [← EuclideanGeometry.oangle_sign_eq_zero_iff_collinear] at h
    rw [← oangle_rotate_sign] at h
    rw [cfg.sbtw_AOF.symm.oangle_eq_left] at h
    rw [(cfg.sbtw_PZF V Pt hZ).symm.oangle_eq_right] at h
    rw [oangle_rotate_sign] at h
    contrapose! h
    exact cfg.sphereOrder_PAFM.sign_oangle₁₂₃_ne_zero
  · exact Collinear.mem_affineSpan_of_mem_of_ne cfg.sbtw_AOF.wbtw.collinear
      (by simp) (by simp) (by simp : cfg.A ∈ _) cfg.F_ne_O.symm
  · exact right_mem_affineSpan_pair ℝ cfg.Ω.center (F V Pt cfg)
  · have h₁ := Collinear.mem_affineSpan_of_mem_of_ne cfg.sbtw_ADE.wbtw.collinear
      (by simp) (by simp) (by simp : cfg.D ∈ _) cfg.h_E_ne_A.symm
    have h₂ := Collinear.mem_affineSpan_of_mem_of_ne cfg.sbtw_SOM.wbtw.collinear
      (by simp) (by simp) (by simp : cfg.Ω.center ∈ _) cfg.S_ne_M
    have h₃ := Collinear.mem_affineSpan_of_mem_of_ne (cfg.sbtw_SZM V Pt hZ).wbtw.collinear
      (by simp) (by simp) (by simp : Z ∈ _) cfg.S_ne_M
    rw [affineSpan_pair_eq_of_right_mem_of_ne h₁ cfg.D_ne_A]
    rw [affineSpan_pair_eq_of_mem_of_mem_of_ne h₂ h₃ (cfg.Z_ne_O V Pt hZ).symm]
    exact cfg.AE_paralell_SM.symm
  · have h₁ := Collinear.mem_affineSpan_of_mem_of_ne cfg.sbtw_PDF.wbtw.collinear
      (by simp) (by simp) (by simp : cfg.D ∈ _) cfg.P_ne_F.symm
    rw [affineSpan_pair_eq_of_right_mem_of_ne h₁ cfg.F_ne_D.symm]
    have h₂ := Collinear.mem_affineSpan_of_mem_of_ne (cfg.sbtw_PZF V Pt hZ).wbtw.collinear
      (by simp) (by simp) (by simp : Z ∈ _) cfg.P_ne_F.symm
    rw [affineSpan_pair_eq_of_right_mem_of_ne h₂ (cfg.Z_ne_F V Pt hZ)]

lemma ZO_to_OS_eq_DA_to_MS {Z : Pt} (hZ : Z ∈ cfg.Z_set)
  : dist Z cfg.Ω.center / dist cfg.Ω.center cfg.S = dist cfg.D cfg.A / dist cfg.M cfg.S := by
  have hOS : dist cfg.Ω.center cfg.S ≠ 0 := by
    rw [dist_ne_zero]
    exact cfg.S_ne_O.symm
  have hOS : dist cfg.M cfg.S ≠ 0 := by
    rw [dist_ne_zero]
    exact cfg.S_ne_M.symm
  field_simp
  rw [dist_comm Z cfg.Ω.center, dist_comm cfg.D cfg.A]
  have h₁ : ¬Collinear ℝ {cfg.A, cfg.D, cfg.F} := by
    rw [← EuclideanGeometry.oangle_sign_eq_zero_iff_collinear]
    rw [oangle_rotate_sign]
    rw [cfg.sbtw_ADE.oangle_eq_right]
    rw [← oangle_swap₁₃_sign, SignType.neg_eq_zero_iff]
    exact cfg.sphereOrder_AFME.rotate'.sign_oangle₁₂₃_ne_zero
  have h₂ : ¬Collinear ℝ {cfg.Ω.center, Z, cfg.F} := by
    rw [← EuclideanGeometry.oangle_sign_eq_zero_iff_collinear]
    rw [cfg.oangle_OZF_eq_oangle_ADF V Pt hZ]
    rw [EuclideanGeometry.oangle_sign_eq_zero_iff_collinear]
    exact h₁
  rw [EuclideanGeometry.dist_eq_dist_mul_sin_angle_div_sin_angle h₁]
  rw [EuclideanGeometry.dist_eq_dist_mul_sin_angle_div_sin_angle h₂]
  rw [EuclideanGeometry.angle_eq_abs_oangle_toReal (cfg.Z_ne_F V Pt hZ) cfg.F_ne_O.symm]
  rw [EuclideanGeometry.angle_eq_abs_oangle_toReal (cfg.Z_ne_O V Pt hZ).symm (cfg.Z_ne_F V Pt hZ).symm]
  rw [EuclideanGeometry.angle_eq_abs_oangle_toReal cfg.F_ne_D.symm cfg.F_ne_A.symm]
  rw [EuclideanGeometry.angle_eq_abs_oangle_toReal cfg.D_ne_A.symm cfg.F_ne_D]
  rw [cfg.sbtw_PDF.symm.oangle_eq_left]
  rw [(cfg.sbtw_PZF V Pt hZ).symm.oangle_eq_left]
  rw [cfg.sbtw_AOF.symm.oangle_eq_right]
  rw [cfg.oangle_OZF_eq_oangle_ADF V Pt hZ]
  rw [EuclideanGeometry.mem_sphere.mp cfg.F_in_Ω]
  rw [EuclideanGeometry.mem_sphere'.mp cfg.h_S_Ω.right]
  rw [cfg.isDiameter_AF.symm.dist_left_right]
  rw [cfg.isDiameter_SM.symm.dist_left_right]
  ring

lemma DX_to_XS_eq_ZO_to_OS {X : Pt} (hX : X ∈ cfg.X_set)
  {Z : Pt} (hZ : Z ∈ cfg.Z_set)
  : dist cfg.D X / dist X cfg.S = dist Z cfg.Ω.center / dist cfg.Ω.center cfg.S := by
  rw [cfg.DX_to_XS_eq_DA_to_MS V Pt hX, cfg.ZO_to_OS_eq_DA_to_MS V Pt hZ]

lemma DS_to_XS_eq_ZS_to_OS {X : Pt} (hX : X ∈ cfg.X_set)
  {Z : Pt} (hZ : Z ∈ cfg.Z_set)
  : dist cfg.D cfg.S / dist X cfg.S = dist Z cfg.S / dist cfg.Ω.center cfg.S := by
  rw [← (cfg.sbtw_SXD V Pt hX).symm.wbtw.dist_add_dist]
  rw [← (cfg.sbtw_SOZ V Pt hZ).symm.wbtw.dist_add_dist]
  have hOS : dist cfg.Ω.center cfg.S ≠ 0 := by
    rw [dist_ne_zero]
    exact cfg.S_ne_O.symm
  have hXS : dist X cfg.S ≠ 0 := by
    rw [dist_ne_zero]
    exact (cfg.X_ne_S V Pt hX)
  rw [add_div, add_div, div_self hOS, div_self hXS]
  rw [cfg.DX_to_XS_eq_ZO_to_OS V Pt hX hZ]

lemma DZ_to_XO_eq_ZS_to_OS {X : Pt} (hX : X ∈ cfg.X_set)
  {Z : Pt} (hZ : Z ∈ cfg.Z_set)
  : dist cfg.D Z / dist X cfg.Ω.center = dist Z cfg.S / dist cfg.Ω.center cfg.S := by
  rw [← mul_self_inj_of_nonneg (by positivity) (by positivity)]
  have hOS : dist cfg.Ω.center cfg.S ≠ 0 := by
    rw [dist_ne_zero]
    exact cfg.S_ne_O.symm
  have hXO : dist X cfg.Ω.center ≠ 0 := by
    rw [dist_ne_zero]
    exact (cfg.X_ne_O V Pt hX)
  have hXS : dist X cfg.S ≠ 0 := by
    rw [dist_ne_zero]
    exact (cfg.X_ne_S V Pt hX)
  have h := cfg.DS_to_XS_eq_ZS_to_OS V Pt hX hZ
  field_simp at h ⊢
  rw [pow_two, pow_two, pow_two, pow_two]
  rw [EuclideanGeometry.law_cos cfg.D cfg.S Z]
  rw [EuclideanGeometry.law_cos X cfg.S cfg.Ω.center]
  ring_nf
  rw [pow_two, pow_two, pow_two, pow_two]
  rw [angle_eq_abs_oangle_toReal cfg.D_ne_S (cfg.Z_ne_S V Pt hZ)]
  rw [angle_eq_abs_oangle_toReal (cfg.X_ne_S V Pt hX) cfg.S_ne_O.symm]
  rw [(cfg.sbtw_SOZ V Pt hZ).oangle_eq_right]
  rw [(cfg.sbtw_SXD V Pt hX).oangle_eq_left]
  rw [(by ring: dist cfg.Ω.center cfg.S * dist cfg.Ω.center cfg.S * dist cfg.D cfg.S
    = (dist cfg.D cfg.S * dist cfg.Ω.center cfg.S) * dist cfg.Ω.center cfg.S)]
  rw [(by ring: dist cfg.Ω.center cfg.S * dist cfg.Ω.center cfg.S * (dist cfg.D cfg.S * dist cfg.D cfg.S)
    = (dist cfg.D cfg.S * dist cfg.Ω.center cfg.S) * (dist cfg.D cfg.S * dist cfg.Ω.center cfg.S))]
  rw [h]
  ring

lemma angle_OXS_eq_angle_ZDS {X : Pt} (hX : X ∈ cfg.X_set)
  {Z : Pt} (hZ : Z ∈ cfg.Z_set)
  : ∠ cfg.Ω.center X cfg.S = ∠ Z cfg.D cfg.S := by
  apply angle_eq_of_cos_angle_eq
  have h₁ := EuclideanGeometry.law_cos cfg.Ω.center X cfg.S
  have h₂ := EuclideanGeometry.law_cos Z cfg.D cfg.S
  rw [eq_sub_iff_add_eq, ← eq_sub_iff_add_eq'] at h₁ h₂
  have hOX : dist cfg.Ω.center X ≠ 0 := by
    rw [dist_ne_zero]
    exact (cfg.X_ne_O V Pt hX).symm
  have hSX : dist cfg.S X ≠ 0 := by
    rw [dist_ne_zero]
    exact (cfg.X_ne_S V Pt hX).symm
  rw [mul_comm, ← eq_div_iff (by positivity)] at h₁
  have hSD : dist cfg.S cfg.D ≠ 0 := by
    rw [dist_ne_zero]
    exact cfg.D_ne_S.symm
  have hZD : dist Z cfg.D ≠ 0 := by
    rw [dist_ne_zero]
    exact (cfg.Z_ne_D V Pt hZ)
  rw [mul_comm, ← eq_div_iff (by positivity)] at h₂
  rw [h₁, h₂]
  have h₁ := cfg.DS_to_XS_eq_ZS_to_OS V Pt hX hZ
  rw [← cfg.DZ_to_XO_eq_ZS_to_OS V Pt hX hZ] at h₁
  rw [dist_comm cfg.D cfg.S, dist_comm X cfg.S] at h₁
  rw [dist_comm cfg.D Z, dist_comm X cfg.Ω.center] at h₁
  have hOS : dist cfg.Ω.center cfg.S ≠ 0 := by
    rw [dist_ne_zero]
    exact cfg.S_ne_O.symm
  have h₂ := cfg.DZ_to_XO_eq_ZS_to_OS V Pt hX hZ
  rw [dist_comm cfg.D Z, dist_comm X cfg.Ω.center] at h₂
  have h₃ := cfg.DS_to_XS_eq_ZS_to_OS V Pt hX hZ
  rw [dist_comm cfg.D cfg.S, dist_comm X cfg.S] at h₃
  field_simp at ⊢ h₁ h₂ h₃
  ring_nf
  rw [(by ring : dist cfg.S cfg.D * dist Z cfg.D * dist cfg.Ω.center X ^ 2
    = (dist cfg.S cfg.D * dist cfg.Ω.center X) * dist Z cfg.D * dist cfg.Ω.center X)]
  rw [(by ring :  dist cfg.S cfg.D ^ 2 * dist cfg.Ω.center X * dist cfg.S X
    = (dist cfg.S cfg.D * dist cfg.Ω.center X) * dist cfg.S cfg.D * dist cfg.S X)]
  rw [(by ring : dist cfg.S cfg.D * dist Z cfg.D * dist cfg.Ω.center cfg.S ^ 2
    = dist cfg.S cfg.D * dist cfg.Ω.center cfg.S * (dist Z cfg.D * dist cfg.Ω.center cfg.S))]
  rw [h₁, h₂, h₃]
  ring

lemma oangle_OXS_eq_oangle_ZDS {X : Pt} (hX : X ∈ cfg.X_set)
  {Z : Pt} (hZ : Z ∈ cfg.Z_set)
  : ∡ cfg.Ω.center X cfg.S = ∡ Z cfg.D cfg.S := by
  apply oangle_eq_of_angle_eq_of_sign_eq
  · exact cfg.angle_OXS_eq_angle_ZDS V Pt hX hZ
  · rw [← oangle_rotate_sign cfg.Ω.center X cfg.S, ← oangle_rotate_sign Z cfg.D cfg.S]
    rw [(cfg.sbtw_SXD V Pt hX).oangle_eq_left]
    rw [(cfg.sbtw_SOZ V Pt hZ).oangle_eq_right]

lemma XO_paralell_FP {X : Pt} (hX : X ∈ cfg.X_set)
  : line[ℝ, X, cfg.Ω.center] ∥ line[ℝ, cfg.P, cfg.F] := by
  rcases cfg.exists_Z with ⟨Z, hZ⟩
  have hD := Collinear.mem_affineSpan_of_mem_of_ne cfg.sbtw_PDF.wbtw.collinear
    (by simp) (by simp) (by simp : cfg.D ∈ _) cfg.P_ne_F
  have hZ' := Collinear.mem_affineSpan_of_mem_of_ne (cfg.sbtw_PZF V Pt hZ).wbtw.collinear
    (by simp) (by simp) (by simp : Z ∈ _) cfg.P_ne_F
  rw [← affineSpan_pair_eq_of_mem_of_mem_of_ne hD hZ' (cfg.Z_ne_D V Pt hZ).symm]
  rw [Set.pair_comm]
  apply parallel_of_two_zsmul_oangle_eq V Pt (cfg.X_ne_O V Pt hX).symm (cfg.X_ne_D V Pt hX) (cfg.Z_ne_D V Pt hZ).symm
  rw [← oangle_add (cfg.X_ne_O V Pt hX).symm (cfg.X_ne_S V Pt hX).symm (cfg.X_ne_D V Pt hX).symm]
  rw [← oangle_add (cfg.Z_ne_D V Pt hZ) cfg.D_ne_S.symm (cfg.X_ne_D V Pt hX)]
  rw [smul_add, smul_add]
  have h₁ := (cfg.sbtw_SXD V Pt hX).wbtw.collinear
  have h₂ := (cfg.sbtw_SXD V Pt hX).wbtw.collinear
  rw [Set.pair_comm] at h₂
  rw [← EuclideanGeometry.oangle_sign_eq_zero_iff_collinear] at h₁ h₂
  rw [Real.Angle.sign_eq_zero_iff] at h₁ h₂
  rw [← Real.Angle.two_zsmul_eq_zero_iff] at h₁ h₂
  rw [h₁, h₂]
  rw [add_zero, add_zero]
  rw [cfg.oangle_OXS_eq_oangle_ZDS V Pt hX hZ]

def Y_set := diag_inter_set V Pt cfg.P cfg.A cfg.F cfg.M

lemma exists_Y : ∃ Y : Pt, Y ∈ cfg.Y_set := by
  exact cfg.sphereOrder_PAFM.exists_diag_inter

lemma Y_ne_P {Y : Pt} (hY : Y ∈ cfg.Y_set) : Y ≠ cfg.P := by
  exact cfg.sphereOrder_PAFM.diag_inter_ne_P₁ V Pt hY

lemma Y_ne_A {Y : Pt} (hY : Y ∈ cfg.Y_set) : Y ≠ cfg.A := by
  rw [Y_set, diag_inter_set_rotate] at hY
  exact cfg.sphereOrder_PAFM.rotate.diag_inter_ne_P₁ V Pt hY

lemma Y_ne_F {Y : Pt} (hY : Y ∈ cfg.Y_set) : Y ≠ cfg.F := by
  rw [Y_set, diag_inter_set_rotate, diag_inter_set_rotate] at hY
  exact cfg.sphereOrder_PAFM.symm.diag_inter_ne_P₁ V Pt hY

lemma sbtw_PYF {Y : Pt} (hY : Y ∈ cfg.Y_set)
  : Sbtw ℝ cfg.P Y cfg.F := by
  exact cfg.sphereOrder_PAFM.diag_inter_sbtw V Pt hY

lemma sbtw_AYM {Y : Pt} (hY : Y ∈ cfg.Y_set)
  : Sbtw ℝ cfg.A Y cfg.M := by
  exact cfg.sphereOrder_PAFM.diag_inter_sbtw' V Pt hY

lemma angle_APY_eq {Y : Pt} (hY : Y ∈ cfg.Y_set)
  : ∠ cfg.A cfg.P Y = Real.pi / 2 := by
  rw [angle_eq_abs_oangle_toReal cfg.P_ne_A.symm (cfg.Y_ne_P V Pt hY)]
  rw [Real.Angle.abs_toReal_eq_pi_div_two_iff, ← Real.Angle.two_zsmul_eq_pi_iff]
  rw [(cfg.sbtw_PYF V Pt hY).oangle_eq_right]
  rw [Real.Angle.two_zsmul_eq_pi_iff, ← Real.Angle.abs_toReal_eq_pi_div_two_iff]
  rw [← angle_eq_abs_oangle_toReal cfg.P_ne_A.symm cfg.P_ne_F.symm]
  rw [EuclideanGeometry.Sphere.angle_eq_pi_div_two_iff_mem_sphere_of_isDiameter cfg.isDiameter_AF]
  exact cfg.P_in_Ω

lemma collinear_AXY {X : Pt} (hX : X ∈ cfg.X_set)
  {Y : Pt} (hY : Y ∈ cfg.Y_set)
  :  Collinear ℝ {cfg.A, X, Y} := by
  have h₁ := (cfg.sbtw_AXM V Pt hX).wbtw.collinear
  have h₂ := (cfg.sbtw_AYM V Pt hY).wbtw.collinear
  have hX : X ∈ affineSpan ℝ {cfg.A, cfg.M} :=
    Collinear.mem_affineSpan_of_mem_of_ne h₁ (by simp) (by simp) (by simp) cfg.M_ne_A.symm
  have hY : Y ∈ affineSpan ℝ {cfg.A, cfg.M} :=
    Collinear.mem_affineSpan_of_mem_of_ne h₂ (by simp) (by simp) (by simp) cfg.M_ne_A.symm
  have hA : cfg.A ∈ affineSpan ℝ {cfg.A, cfg.M} := by
    apply mem_affineSpan
    simp
  exact collinear_triple_of_mem_affineSpan_pair hA hX hY

lemma not_collinear_AXO {X : Pt} (hX : X ∈ cfg.X_set)
  : ¬Collinear ℝ {cfg.A, X, cfg.Ω.center} := by
  rw [Set.insert_comm]
  rw [← EuclideanGeometry.oangle_sign_eq_zero_iff_collinear]
  rw [(cfg.sbtw_AXM V Pt hX).oangle_eq_left]
  rw [cfg.sbtw_AOF.oangle_eq_right]
  rw [oangle_rotate_sign]
  exact cfg.sphereOrder_ASFM.sign_oangle₃₄₁_ne_zero

lemma oangle_AXO_eq_oangle_AYF {X : Pt} (hX : X ∈ cfg.X_set)
  {Y : Pt} (hY : Y ∈ cfg.Y_set)
  : ∡ cfg.A X cfg.Ω.center = ∡ cfg.A Y cfg.F := by
  apply EuclideanGeometry.oangle_eq_of_parallel
  · have h := cfg.not_collinear_AXO V Pt hX
    contrapose! h
    rw [Set.insert_comm]
    exact collinear_insert_of_mem_affineSpan_pair h
  · exact left_mem_affineSpan_pair ℝ cfg.A cfg.Ω.center
  · exact Collinear.mem_affineSpan_of_mem_of_ne cfg.sbtw_AOF.wbtw.collinear
      (by simp) (by simp) (by simp : cfg.F ∈ _) cfg.O_ne_A.symm
  · have h₁ := Collinear.mem_affineSpan_of_mem_of_ne (cfg.sbtw_AXM V Pt hX).wbtw.collinear
      (by simp) (by simp) (by simp : X ∈ _) cfg.M_ne_A.symm
    rw [affineSpan_pair_eq_of_right_mem_of_ne h₁ (cfg.X_ne_A V Pt hX)]
    have h₂ := Collinear.mem_affineSpan_of_mem_of_ne (cfg.sbtw_AYM V Pt hY).wbtw.collinear
      (by simp) (by simp) (by simp : Y ∈ _) cfg.M_ne_A.symm
    rw [affineSpan_pair_eq_of_right_mem_of_ne h₂ (cfg.Y_ne_A V Pt hY)]
  · have h := Collinear.mem_affineSpan_of_mem_of_ne (cfg.sbtw_PYF V Pt hY).wbtw.collinear
      (by simp) (by simp) (by simp : Y ∈ _) cfg.P_ne_F.symm
    rw [affineSpan_pair_eq_of_right_mem_of_ne h (cfg.Y_ne_F V Pt hY)]
    rw [Set.pair_comm cfg.Ω.center X, Set.pair_comm cfg.F cfg.P]
    exact cfg.XO_paralell_FP V Pt hX

lemma oangle_XOA_eq_oangle_YFA {X : Pt} (hX : X ∈ cfg.X_set)
  {Y : Pt} (hY : Y ∈ cfg.Y_set)
  : ∡ X cfg.Ω.center cfg.A = ∡ Y cfg.F cfg.A := by
  apply EuclideanGeometry.oangle_eq_of_parallel
  · have h := cfg.not_collinear_AXO V Pt hX
    contrapose! h
    rw [Set.pair_comm, Set.insert_comm, Set.pair_comm]
    exact collinear_insert_of_mem_affineSpan_pair h
  · exact Collinear.mem_affineSpan_of_mem_of_ne (cfg.collinear_AXY V Pt hX hY)
      (by simp) (by simp) (by simp : Y ∈ _) (cfg.X_ne_A V Pt hX)
  · exact right_mem_affineSpan_pair ℝ X cfg.A
  · have h := Collinear.mem_affineSpan_of_mem_of_ne (cfg.sbtw_PYF V Pt hY).wbtw.collinear
      (by simp) (by simp) (by simp : Y ∈ _) cfg.P_ne_F
    rw [affineSpan_pair_eq_of_left_mem_of_ne h (cfg.Y_ne_F V Pt hY)]
    exact cfg.XO_paralell_FP V Pt hX
  · have h := Collinear.mem_affineSpan_of_mem_of_ne cfg.sbtw_AOF.wbtw.collinear
      (by simp) (by simp) (by simp : cfg.Ω.center ∈ _) cfg.F_ne_A.symm
    rw [affineSpan_pair_eq_of_right_mem_of_ne h cfg.O_ne_A]

lemma AX_eq_AY_div_two {X : Pt} (hX : X ∈ cfg.X_set)
  {Y : Pt} (hY : Y ∈ cfg.Y_set)
  : dist cfg.A X = dist cfg.A Y / 2 := by
  have h_AXO := cfg.not_collinear_AXO V Pt hX
  have h_AYF : ¬Collinear ℝ {cfg.A, Y, cfg.F} := by
    rw [← EuclideanGeometry.oangle_sign_eq_zero_iff_collinear, ← cfg.oangle_AXO_eq_oangle_AYF V Pt hX hY]
    rw [EuclideanGeometry.oangle_sign_eq_zero_iff_collinear]
    exact h_AXO
  have h₁ := EuclideanGeometry.dist_eq_dist_mul_sin_angle_div_sin_angle h_AXO
  have h₂ := EuclideanGeometry.dist_eq_dist_mul_sin_angle_div_sin_angle h_AYF
  rw [h₁, h₂, div_right_comm]
  nth_rw 2 [mul_div_right_comm]
  rw [EuclideanGeometry.angle_eq_abs_oangle_toReal (cfg.X_ne_O V Pt hX) cfg.O_ne_A.symm]
  rw [EuclideanGeometry.angle_eq_abs_oangle_toReal (cfg.X_ne_A V Pt hX).symm (cfg.X_ne_O V Pt hX).symm]
  rw [EuclideanGeometry.angle_eq_abs_oangle_toReal (cfg.Y_ne_F V Pt hY) cfg.F_ne_A.symm]
  rw [EuclideanGeometry.angle_eq_abs_oangle_toReal (cfg.Y_ne_A V Pt hY).symm (cfg.Y_ne_F V Pt hY).symm]
  rw [← cfg.oangle_AXO_eq_oangle_AYF V Pt hX hY]
  rw [← cfg.oangle_XOA_eq_oangle_YFA V Pt hX hY]
  have h : dist cfg.Ω.center cfg.A = dist cfg.F cfg.A / 2 := by
    rw [EuclideanGeometry.Sphere.IsDiameter.dist_left_right cfg.isDiameter_AF.symm]
    rw [mul_div_cancel_left₀ _ (by norm_num)]
    rw [← EuclideanGeometry.mem_sphere']
    exact cfg.A_in_Ω
  rw [h]

lemma sbtw_AXY {X : Pt} (hX : X ∈ cfg.X_set)
  {Y : Pt} (hY : Y ∈ cfg.Y_set)
  : Sbtw ℝ cfg.A X Y := by
  rcases Collinear.sbtw_or_wbtw_or_wbtw V Pt (cfg.collinear_AXY V Pt hX hY) with (h'|(h'|h'))
  · exact h'
  · exfalso
    have h := h'.dist_add_dist
    rw [dist_comm X cfg.A, dist_comm Y cfg.A, cfg.AX_eq_AY_div_two V Pt hX hY] at h
    rw [← sub_eq_zero] at h
    field_simp at h
    ring_nf at h
    symm at h
    rw [← add_zero (0 : ℝ), add_eq_add_iff_eq_and_eq (by positivity) (by positivity)] at h
    contrapose h
    rw [not_and_or]
    right
    rw [zero_eq_dist]
    exact (cfg.Y_ne_A V Pt hY).symm
  · exfalso
    have h'' := Wbtw.oangle_sign_eq_of_ne_left cfg.E h' (cfg.Y_ne_A V Pt hY)
    rw [← Wbtw.oangle_sign_eq_of_ne_right cfg.E h' (cfg.X_ne_A V Pt hX).symm] at h''
    contrapose! h''
    rw [← oangle_rotate_sign Y cfg.E cfg.A, oangle_rotate_sign X cfg.A cfg.E]
    rw [(cfg.sbtw_AXM V Pt hX).oangle_eq_left, (cfg.sbtw_AYM V Pt hY).oangle_eq_right]
    rw [oangle_rev cfg.E cfg.A (M V Pt cfg), Real.Angle.sign_neg, SignType.self_eq_neg_iff.ne]
    rw [oangle_rotate_sign]
    exact cfg.sphereOrder_AFME.sign_oangle₃₄₁_ne_zero

lemma X_eq_midpoint_AY {X : Pt} (hX : X ∈ cfg.X_set)
  {Y : Pt} (hY : Y ∈ cfg.Y_set)
  : X = midpoint ℝ cfg.A Y := by
  have h := cfg.AX_eq_AY_div_two V Pt hX hY
  apply eq_midpoint_of_dist_eq_half
  · exact h
  · have h' := (cfg.sbtw_AXY V Pt hX hY).wbtw.dist_add_dist
    rw [h, ← eq_sub_iff_add_eq'] at h'
    rw [h']
    ring

lemma XP_eq_XA  {X : Pt} (hX : X ∈ cfg.X_set)
  : dist X cfg.P = dist X cfg.A := by
  rcases cfg.exists_Y with ⟨Y, hY⟩
  have h := cfg.angle_APY_eq V Pt hY
  rw [EuclideanGeometry.Sphere.angle_eq_pi_div_two_iff_mem_sphere_ofDiameter] at h
  rw [EuclideanGeometry.mem_sphere'] at h
  have h' : X = (Sphere.ofDiameter cfg.A Y).center := by
    rw [Sphere.ofDiameter]
    dsimp
    exact cfg.X_eq_midpoint_AY V Pt hX hY
  rw [h', h]
  symm
  rw [← EuclideanGeometry.mem_sphere']
  exact (EuclideanGeometry.Sphere.isDiameter_ofDiameter cfg.A Y).left_mem

lemma oangle_XPA_eq_oangle_PAX {X : Pt} (hX : X ∈ cfg.X_set)
  : ∡ X cfg.P cfg.A  = ∡ cfg.P cfg.A X := by
  apply EuclideanGeometry.oangle_eq_oangle_of_dist_eq (cfg.XP_eq_XA V Pt hX)

lemma two_zsmul_angle_SPM_eq : (2 : ℤ) • ∡ cfg.S cfg.P cfg.M = Real.pi := by
  rw [Real.Angle.two_zsmul_eq_pi_iff]
  rw [← Real.Angle.abs_toReal_eq_pi_div_two_iff]
  rw [← EuclideanGeometry.angle_eq_abs_oangle_toReal cfg.P_ne_S.symm cfg.P_ne_M.symm]
  rw [EuclideanGeometry.Sphere.thales_theorem cfg.isDiameter_SM]
  exact cfg.P_in_Ω

lemma two_zsmul_angle_APF_eq : (2 : ℤ) • ∡ cfg.A cfg.P cfg.F = Real.pi := by
  rw [Real.Angle.two_zsmul_eq_pi_iff]
  rw [← Real.Angle.abs_toReal_eq_pi_div_two_iff]
  rw [← EuclideanGeometry.angle_eq_abs_oangle_toReal cfg.P_ne_A.symm cfg.P_ne_F.symm]
  rw [EuclideanGeometry.Sphere.thales_theorem cfg.isDiameter_AF]
  exact cfg.P_in_Ω

lemma oangle_XPD_eq_oangle_PBD {X : Pt} (hX : X ∈ cfg.X_set)
  : (2 : ℤ) • ∡ X cfg.P cfg.D  = (2 : ℤ) • ∡ cfg.P cfg.B cfg.D := by
  rw [← oangle_add (cfg.P_ne_X V Pt hX).symm cfg.P_ne_A.symm cfg.P_ne_D.symm]
  rw [smul_add, cfg.oangle_XPA_eq_oangle_PAX V Pt hX]
  rw [(cfg.sbtw_AXM V Pt hX).oangle_eq_right]
  rw [cfg.sbtw_BDS.oangle_eq_right]
  rw [← eq_sub_iff_add_eq']
  rw [EuclideanGeometry.Sphere.two_zsmul_oangle_eq cfg.P_in_Ω cfg.A_in_Ω cfg.h_S_Ω.right cfg.M_in_Ω
    cfg.P_ne_A.symm cfg.M_ne_A.symm cfg.P_ne_S.symm cfg.S_ne_M]
  rw [EuclideanGeometry.Sphere.two_zsmul_oangle_eq cfg.P_in_Ω cfg.B_in_Ω cfg.M_in_Ω cfg.h_S_Ω.right
    cfg.h_P_ne_B.symm cfg.S_ne_B.symm cfg.P_ne_M.symm cfg.S_ne_M.symm]
  rw [sub_eq_add_neg, ← smul_neg, ← oangle_rev, ← smul_add]
  have h := EuclideanGeometry.oangle_add_oangle_add_oangle_eq_pi
    cfg.P_ne_M.symm cfg.S_ne_M cfg.P_ne_S
  rw [← eq_sub_iff_add_eq] at h
  rw [h, smul_sub, two_zsmul_angle_SPM_eq]
  rw [cfg.sbtw_PDF.oangle_eq_right, two_zsmul_angle_APF_eq]
  abel

lemma PX_isTangentAt_ω {X : Pt} (hX : X ∈ cfg.X_set)
  : Sphere.IsTangentAt cfg.ω cfg.P line[ℝ, cfg.P, X] := by
  apply Sphere.IsTangentAt_of_two_zsmul_oangle_eq V Pt cfg.P_in_ω cfg.D_in_ω cfg.B_in_ω
    cfg.P_ne_D cfg.h_P_ne_B cfg.D_ne_B (cfg.P_ne_X V Pt hX) (cfg.oangle_XPD_eq_oangle_PBD V Pt hX)

lemma X_in_tang_P_ω {X : Pt} (hX : X ∈ cfg.X_set)
  : X ∈ cfg.tang_P_ω := by
  have h' : finrank ℝ cfg.tang_P_ω.direction + 1 = finrank ℝ V := by
    rw [cfg.h_rank_tang_P_ω, hd2.out]
  have h₁ := EuclideanGeometry.Sphere.IsTangentAt.eq_orthRadius_of_finrank_add_one_eq
    cfg.h_tang_P_ω cfg.ω_radius_ne_zero h'
  have h'' : finrank ℝ line[ℝ, cfg.P, X].direction + 1 = finrank ℝ V := by
    rw [hd2.out, Nat.add_one, Nat.succ_inj, affineSpan_pair_finrank V Pt (cfg.P_ne_X V Pt hX)]
  have h₂ := EuclideanGeometry.Sphere.IsTangentAt.eq_orthRadius_of_finrank_add_one_eq
    (cfg.PX_isTangentAt_ω V Pt hX) cfg.ω_radius_ne_zero h''
  rw [h₁, ← h₂]
  exact right_mem_affineSpan_pair ℝ cfg.P X

theorem result : ∃ X : Pt,
    X ∈ (cfg.tang_P_ω : Set Pt) ∩ line[ℝ, cfg.B, cfg.S]
    ∧ ∠ cfg.B cfg.A X = ∠ X cfg.A cfg.C
    ∧ ∠ cfg.B cfg.A X < π / 2 := by
  rcases cfg.exists_X with ⟨X, hX⟩
  use X
  constructor
  · constructor
    · exact cfg.X_in_tang_P_ω V Pt hX
    · exact Set.mem_of_mem_inter_left hX
  · constructor
    · exact cfg.angle_BAX_eq_angle_XAC V Pt hX
    · rw [← cfg.angle_BAM_eq_angle_BAX V Pt hX]
      exact cfg.angle_BAM_acute

end Imo2023q2Cfg

snip end

problem imo2023_p1
  -- Points
  (A B C D E L S P : Pt)
  -- Circles
  (Ω ω : Sphere Pt)
  -- Lines
  (perp_A_BC prll_D_BC tang_P_ω : AffineSubspace ℝ Pt)
  -- Let ABC be an acute-angled triangle
  (h_ABC : AffineIndependent ℝ ![A, B, C])
  (h_acute_ABC : (⟨![A, B, C], h_ABC⟩ :Affine.Triangle _ _).AcuteAngled)
  -- with AB < AC.
  (h_AB_lt_BC : dist A B < dist A C)
  -- Let Ω be the circumcircle of ABC.
  (h_Ω : {A, B, C} ⊆ (Ω : Set Pt))
  -- Let S be the midpoint of the arc CB of Ω
  (h_S_Ω : dist S C = dist S B ∧ S ∈ (Ω : Set Pt))
  -- ... containing A.
  (h_S_A : (∡ C B S).sign = (∡ C B A).sign)
  -- The perpendicular from A to BC ...
  (h_perp_A_BC : perp_A_BC.direction ⟂ line[ℝ, B, C].direction ∧ A ∈ perp_A_BC)
  -- ... meets BS at D
  (h_D : D ∈ (perp_A_BC : Set Pt) ∩ line[ℝ, B, S])
  -- ... and meets Ω again at E ...
  (h_E : E ∈ (perp_A_BC : Set Pt) ∩ Ω)
  -- ... E ≠ A.
  (h_E_ne_A : E ≠ A)
  -- The line through D parallel to BC ...
  (h_prll_D_BC : D ∈ prll_D_BC ∧ prll_D_BC ∥ line[ℝ, B, C])
  --- ... meets line BE at L.
  (h_L : L ∈ (prll_D_BC : Set Pt) ∩ line[ℝ, B, E])
  -- Denote the circumcircle of triangle BDL by ω.
  (h_ω : {B, D, L} ⊆ (ω : Set Pt))
  -- Let ω meet Ω again at P ...
  (h_P : P ∈ (ω : Set Pt) ∩ Ω)
  -- P ≠ B.
  (h_P_ne_B : P ≠ B)
  -- Prove that the line tangent to ω at P ...
  (h_rank_tang_P_ω : Module.finrank ℝ tang_P_ω.direction = 1)
  (h_tang_P_ω : Sphere.IsTangentAt ω P tang_P_ω) :
  -- meets line BS on the internal angle bisector of ∠BAC.
  ∃ X : Pt,
    X ∈ (tang_P_ω : Set Pt) ∩ line[ℝ, B, S]
    ∧ ∠ B A X = ∠ X A C
    ∧ ∠ B A X < π / 2 := by
  set cfg : Imo2023q2Cfg V Pt := ⟨
    A, B, C, D, E, L, S, P,
    Ω, ω,
    perp_A_BC, prll_D_BC, tang_P_ω,
    h_ABC,
    h_acute_ABC,
    h_AB_lt_BC,
    h_Ω,
    h_S_Ω,
    h_S_A,
    h_perp_A_BC,
    h_D,
    h_E,
    h_E_ne_A,
    h_prll_D_BC,
    h_L,
    h_ω,
    h_P,
    h_P_ne_B,
    h_rank_tang_P_ω,
    h_tang_P_ω,
  ⟩
  exact cfg.result


end Imo2023P2
