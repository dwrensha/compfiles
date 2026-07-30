/-
Copyright (c) 2026 The Compfiles Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.Convex.StrictConvexBetween
public import Mathlib.Analysis.InnerProductSpace.OfNorm
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import ProblemExtraction

@[expose] public section

problem_file {
  tags := [.Geometry]
}

/-!
# International Mathematical Olympiad 1998, Problem 5

Let I be the incenter of the triangle ABC. Let the incircle of ABC touch the sides
BC, CA, AB at K, L, M respectively. The line through B parallel to MK meets the lines
LM and LK at R and S respectively. Prove that the angle RIS is acute.
-/

namespace Imo1998P5

open scoped InnerProductSpace RealInnerProductSpace Real

noncomputable section

/-- The ambient Euclidean plane. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The semiperimeter of the triangle `ABC`. -/
def sp (A B C : Plane) : ℝ := (dist B C + dist C A + dist A B) / 2

/-- The incenter `I` of the triangle, in barycentric coordinates (weighted by the
lengths of the opposite sides). -/
def incenterPt (A B C : Plane) : Plane :=
  (dist B C + dist C A + dist A B)⁻¹ • (dist B C • A + dist C A • B + dist A B • C)

/-- The touch point `K` where the incircle touches `BC`: it lies on line `BC` with
`BK = sp - CA`. -/
def touchK (A B C : Plane) : Plane := B + ((sp A B C - dist C A) / dist B C) • (C - B)

/-- The touch point `L` where the incircle touches `CA`: it lies on line `CA` with
`CL = sp - AB`. -/
def touchL (A B C : Plane) : Plane := C + ((sp A B C - dist A B) / dist C A) • (A - C)

/-- The touch point `M` where the incircle touches `AB`: it lies on line `AB` with
`AM = sp - BC`. -/
def touchM (A B C : Plane) : Plane := A + ((sp A B C - dist B C) / dist A B) • (B - A)

/-- A direction vector of the line `MK`. -/
def dirKM (A B C : Plane) : Plane := (dist B C)⁻¹ • (C - B) - (dist A B)⁻¹ • (A - B)

/-- The intersection `R` of the line through `B` parallel to `MK` with the line `LM`,
given explicitly. -/
def ptR (A B C : Plane) : Plane :=
  B + (-(dist B C * (sp A B C - dist C A)) / (2 * (sp A B C - dist A B))) • dirKM A B C

/-- The intersection `S` of the line through `B` parallel to `MK` with the line `LK`,
given explicitly. -/
def ptS (A B C : Plane) : Plane :=
  B + ((dist A B * (sp A B C - dist C A)) / (2 * (sp A B C - dist B C))) • dirKM A B C

variable {A B C : Plane}

snip begin

lemma neAB (h : ¬ Collinear ℝ ({A, B, C} : Set Plane)) : A ≠ B := by
  intro he; apply h; rw [he]
  have hset : ({B, B, C} : Set Plane) = {B, C} := by
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  rw [hset]; exact collinear_pair ℝ B C

lemma neBC (h : ¬ Collinear ℝ ({A, B, C} : Set Plane)) : B ≠ C := by
  intro he; apply h; rw [he]
  have hset : ({A, C, C} : Set Plane) = {A, C} := by
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  rw [hset]; exact collinear_pair ℝ A C

lemma neCA (h : ¬ Collinear ℝ ({A, B, C} : Set Plane)) : C ≠ A := by
  intro he; apply h; rw [he]
  have hset : ({A, B, A} : Set Plane) = {A, B} := by
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  rw [hset]; exact collinear_pair ℝ A B

/-- The strict triangle inequality, `BC < AB + CA`. -/
lemma tri_BC (h : ¬ Collinear ℝ ({A, B, C} : Set Plane)) : dist B C < dist A B + dist C A := by
  have h1 : dist B C < dist B A + dist A C := by
    rw [dist_lt_dist_add_dist_iff]
    intro hw
    exact h ((Set.insert_comm B A {C}) ▸ hw.collinear)
  rw [dist_comm B A, dist_comm A C] at h1
  exact h1

/-- The strict triangle inequality, `CA < BC + AB`. -/
lemma tri_CA (h : ¬ Collinear ℝ ({A, B, C} : Set Plane)) : dist C A < dist B C + dist A B := by
  have h1 : dist C A < dist C B + dist B A := by
    rw [dist_lt_dist_add_dist_iff]
    intro hw
    apply h
    have hset : ({C, B, A} : Set Plane) = {A, B, C} := by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    exact hset ▸ hw.collinear
  rw [dist_comm C B, dist_comm B A] at h1
  exact h1

/-- The strict triangle inequality, `AB < CA + BC`. -/
lemma tri_AB (h : ¬ Collinear ℝ ({A, B, C} : Set Plane)) : dist A B < dist C A + dist B C := by
  have h1 : dist A B < dist A C + dist C B := by
    rw [dist_lt_dist_add_dist_iff]
    intro hw
    apply h
    have hset : ({A, C, B} : Set Plane) = {A, B, C} := by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    exact hset ▸ hw.collinear
  rw [dist_comm A C, dist_comm C B] at h1
  exact h1

lemma pos_BC (h : ¬ Collinear ℝ ({A, B, C} : Set Plane)) : 0 < dist B C :=
  dist_pos.mpr (neBC h)

lemma pos_CA (h : ¬ Collinear ℝ ({A, B, C} : Set Plane)) : 0 < dist C A :=
  dist_pos.mpr (neCA h)

lemma pos_AB (h : ¬ Collinear ℝ ({A, B, C} : Set Plane)) : 0 < dist A B :=
  dist_pos.mpr (neAB h)

lemma pos_sp (h : ¬ Collinear ℝ ({A, B, C} : Set Plane)) : 0 < sp A B C := by
  show 0 < (dist B C + dist C A + dist A B) / 2
  linarith [pos_BC h, pos_CA h, pos_AB h]

lemma pos_sp_sub_BC (h : ¬ Collinear ℝ ({A, B, C} : Set Plane)) :
    0 < sp A B C - dist B C := by
  have h1 := tri_BC h
  show 0 < (dist B C + dist C A + dist A B) / 2 - dist B C
  linarith

lemma pos_sp_sub_CA (h : ¬ Collinear ℝ ({A, B, C} : Set Plane)) :
    0 < sp A B C - dist C A := by
  have h1 := tri_CA h
  show 0 < (dist B C + dist C A + dist A B) / 2 - dist C A
  linarith

lemma pos_sp_sub_AB (h : ¬ Collinear ℝ ({A, B, C} : Set Plane)) :
    0 < sp A B C - dist A B := by
  have h1 := tri_AB h
  show 0 < (dist B C + dist C A + dist A B) / 2 - dist A B
  linarith

lemma dsum_ne (h : ¬ Collinear ℝ ({A, B, C} : Set Plane)) :
    dist B C + dist C A + dist A B ≠ 0 :=
  (add_pos (add_pos (pos_BC h) (pos_CA h)) (pos_AB h)).ne'

lemma hdsum_ne (h : ¬ Collinear ℝ ({A, B, C} : Set Plane)) :
    (dist B C + dist C A + dist A B) / 2 ≠ 0 := (pos_sp h).ne'

lemma psub_BC_ne (h : ¬ Collinear ℝ ({A, B, C} : Set Plane)) :
    (dist B C + dist C A + dist A B) / 2 - dist B C ≠ 0 := (pos_sp_sub_BC h).ne'

lemma psub_CA_ne (h : ¬ Collinear ℝ ({A, B, C} : Set Plane)) :
    (dist B C + dist C A + dist A B) / 2 - dist C A ≠ 0 := (pos_sp_sub_CA h).ne'

lemma psub_AB_ne (h : ¬ Collinear ℝ ({A, B, C} : Set Plane)) :
    (dist B C + dist C A + dist A B) / 2 - dist A B ≠ 0 := (pos_sp_sub_AB h).ne'

/-- `2 * (sp - BC) ≠ 0`, in the expanded form that `field_simp` produces. -/
lemma hne_sa (h : ¬ Collinear ℝ ({A, B, C} : Set Plane)) :
    (dist B C + dist C A + dist A B - 2 * dist B C) ≠ 0 := by
  have h1 := pos_sp_sub_BC h
  simp only [sp] at h1
  have h2 : (0 : ℝ) < dist B C + dist C A + dist A B - 2 * dist B C := by linarith
  exact h2.ne'

/-- `2 * (sp - CA) ≠ 0`, in the expanded form that `field_simp` produces. -/
lemma hne_sb (h : ¬ Collinear ℝ ({A, B, C} : Set Plane)) :
    (dist B C + dist C A + dist A B - 2 * dist C A) ≠ 0 := by
  have h1 := pos_sp_sub_CA h
  simp only [sp] at h1
  have h2 : (0 : ℝ) < dist B C + dist C A + dist A B - 2 * dist C A := by linarith
  exact h2.ne'

/-- `2 * (sp - AB) ≠ 0`, in the expanded form that `field_simp` produces. -/
lemma hne_sc (h : ¬ Collinear ℝ ({A, B, C} : Set Plane)) :
    (dist B C + dist C A + dist A B - 2 * dist A B) ≠ 0 := by
  have h1 := pos_sp_sub_AB h
  simp only [sp] at h1
  have h2 : (0 : ℝ) < dist B C + dist C A + dist A B - 2 * dist A B := by linarith
  exact h2.ne'

/-- `K - M` is a positive multiple of the reference direction `dirKM`. -/
lemma touchK_sub_touchM (h : ¬ Collinear ℝ ({A, B, C} : Set Plane)) :
    touchK A B C - touchM A B C = (sp A B C - dist C A) • dirKM A B C := by
  ext i
  fin_cases i <;>
    simp only [touchK, touchM, dirKM, sp, PiLp.add_apply, PiLp.sub_apply,
      PiLp.smul_apply, smul_eq_mul] <;>
    field_simp [hne_sa h, hne_sb h, hne_sc h, (pos_BC h).ne', (pos_CA h).ne',
      (pos_AB h).ne'] <;>
    ring

/-- The point `R` lies on the line through `B` parallel to `MK`. -/
lemma parallel_R (h : ¬ Collinear ℝ ({A, B, C} : Set Plane)) :
    ∃ ζ : ℝ, ptR A B C - B = ζ • (touchK A B C - touchM A B C) := by
  use -(dist B C) / (2 * (sp A B C - dist A B))
  have hRB : ptR A B C - B =
      (-(dist B C * (sp A B C - dist C A)) / (2 * (sp A B C - dist A B))) • dirKM A B C := by
    simp only [ptR, add_sub_cancel_left]
  rw [touchK_sub_touchM h, smul_smul, hRB]
  congr 1
  ring

/-- The point `S` lies on the line through `B` parallel to `MK`. -/
lemma parallel_S (h : ¬ Collinear ℝ ({A, B, C} : Set Plane)) :
    ∃ η : ℝ, ptS A B C - B = η • (touchK A B C - touchM A B C) := by
  use (dist A B) / (2 * (sp A B C - dist B C))
  have hSB : ptS A B C - B =
      ((dist A B * (sp A B C - dist C A)) / (2 * (sp A B C - dist B C))) • dirKM A B C := by
    simp only [ptS, add_sub_cancel_left]
  rw [touchK_sub_touchM h, smul_smul, hSB]
  congr 1
  ring

/-- The point `R` lies on the line `LM`: the incidence, scaled to avoid denominators. -/
lemma online_R_scaled (h : ¬ Collinear ℝ ({A, B, C} : Set Plane)) :
    (2 * (sp A B C - dist B C) * (sp A B C - dist A B)) • (ptR A B C - touchM A B C)
      = (-(dist C A * (sp A B C - dist C A))) • (touchL A B C - touchM A B C) := by
  ext i
  fin_cases i <;>
    simp only [ptR, touchM, touchL, dirKM, sp, PiLp.add_apply, PiLp.sub_apply,
      PiLp.smul_apply, smul_eq_mul] <;>
    field_simp [hne_sa h, hne_sb h, hne_sc h, dsum_ne h, hdsum_ne h,
      psub_BC_ne h, psub_CA_ne h, psub_AB_ne h,
      (pos_BC h).ne', (pos_CA h).ne', (pos_AB h).ne'] <;>
    ring

/-- The point `R` lies on the line `LM`. -/
lemma online_R (h : ¬ Collinear ℝ ({A, B, C} : Set Plane)) :
    ∃ τ : ℝ, ptR A B C = touchM A B C + τ • (touchL A B C - touchM A B C) := by
  have hD : (2 * (sp A B C - dist B C) * (sp A B C - dist A B)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (pos_sp_sub_BC h).ne') (pos_sp_sub_AB h).ne'
  refine ⟨(-(dist C A * (sp A B C - dist C A))) /
    (2 * (sp A B C - dist B C) * (sp A B C - dist A B)), ?_⟩
  have key : ptR A B C - touchM A B C =
      ((-(dist C A * (sp A B C - dist C A))) /
        (2 * (sp A B C - dist B C) * (sp A B C - dist A B))) • (touchL A B C - touchM A B C) := by
    rw [div_eq_mul_inv, mul_comm (-(dist C A * (sp A B C - dist C A))) _⁻¹, ← smul_smul,
      ← online_R_scaled h, smul_smul, inv_mul_cancel₀ hD, one_smul]
  rw [add_comm]
  exact sub_eq_iff_eq_add.mp key

/-- The point `S` lies on the line `LK`: the incidence, scaled to avoid denominators. -/
lemma online_S_scaled (h : ¬ Collinear ℝ ({A, B, C} : Set Plane)) :
    (2 * (sp A B C - dist B C) * (sp A B C - dist A B)) • (ptS A B C - touchK A B C)
      = (-(dist C A * (sp A B C - dist C A))) • (touchL A B C - touchK A B C) := by
  ext i
  fin_cases i <;>
    simp only [ptS, touchK, touchL, dirKM, sp, PiLp.add_apply, PiLp.sub_apply,
      PiLp.smul_apply, smul_eq_mul] <;>
    field_simp [hne_sa h, hne_sb h, hne_sc h, dsum_ne h, hdsum_ne h,
      psub_BC_ne h, psub_CA_ne h, psub_AB_ne h,
      (pos_BC h).ne', (pos_CA h).ne', (pos_AB h).ne'] <;>
    ring

/-- The point `S` lies on the line `LK`. -/
lemma online_S (h : ¬ Collinear ℝ ({A, B, C} : Set Plane)) :
    ∃ υ : ℝ, ptS A B C = touchK A B C + υ • (touchL A B C - touchK A B C) := by
  have hD : (2 * (sp A B C - dist B C) * (sp A B C - dist A B)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (pos_sp_sub_BC h).ne') (pos_sp_sub_AB h).ne'
  refine ⟨(-(dist C A * (sp A B C - dist C A))) /
    (2 * (sp A B C - dist B C) * (sp A B C - dist A B)), ?_⟩
  have key : ptS A B C - touchK A B C =
      ((-(dist C A * (sp A B C - dist C A))) /
        (2 * (sp A B C - dist B C) * (sp A B C - dist A B))) • (touchL A B C - touchK A B C) := by
    rw [div_eq_mul_inv, mul_comm (-(dist C A * (sp A B C - dist C A))) _⁻¹, ← smul_smul,
      ← online_S_scaled h, smul_smul, inv_mul_cancel₀ hD, one_smul]
  rw [add_comm]
  exact sub_eq_iff_eq_add.mp key

/-- The incenter relative to `B`, expressed in the directions `A - B` and `C - B`. -/
lemma incenter_sub (hD : dist B C + dist C A + dist A B ≠ 0) :
    incenterPt A B C - B =
      (dist B C + dist C A + dist A B)⁻¹ • (dist B C • (A - B) + dist A B • (C - B)) := by
  have e : dist B C • (A - B) + dist A B • (C - B)
      = dist B C • A + dist C A • B + dist A B • C
        - (dist B C + dist C A + dist A B) • B := by
    module
  rw [incenterPt, e, smul_sub, smul_smul, inv_mul_cancel₀ hD, one_smul]

/-- The key identity: the inner product of `R - I` and `S - I` equals the square of the
inradius, `(sp - a)(sp - b)(sp - c)/sp`. -/
lemma inner_RS (h : ¬ Collinear ℝ ({A, B, C} : Set Plane)) :
    ⟪ptR A B C - incenterPt A B C, ptS A B C - incenterPt A B C⟫_ℝ
      = ((sp A B C - dist B C) * (sp A B C - dist C A) * (sp A B C - dist A B)) /
        sp A B C := by
  have hRB : ptR A B C - B =
      (-(dist B C * (sp A B C - dist C A)) / (2 * (sp A B C - dist A B))) • dirKM A B C := by
    simp only [ptR, add_sub_cancel_left]
  have hSB : ptS A B C - B =
      ((dist A B * (sp A B C - dist C A)) / (2 * (sp A B C - dist B C))) • dirKM A B C := by
    simp only [ptS, add_sub_cancel_left]
  have hIB := incenter_sub (dsum_ne h)
  have huu : ⟪A - B, A - B⟫_ℝ = (dist A B) ^ 2 := by
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm]
  have hww : ⟪C - B, C - B⟫_ℝ = (dist B C) ^ 2 := by
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, dist_comm C B]
  have huw : ⟪A - B, C - B⟫_ℝ = ((dist B C) ^ 2 + (dist A B) ^ 2 - (dist C A) ^ 2) / 2 := by
    have h3 := norm_sub_sq_real (A - B) (C - B)
    rw [show (A - B) - (C - B) = A - C by abel] at h3
    simp only [← dist_eq_norm] at h3
    rw [dist_comm A C, dist_comm C B] at h3
    linarith
  rw [← sub_sub_sub_cancel_right (ptR A B C) (incenterPt A B C) B,
    ← sub_sub_sub_cancel_right (ptS A B C) (incenterPt A B C) B, hRB, hSB, hIB]
  simp only [dirKM]
  set u := A - B with hu
  set w := C - B with hw
  simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm u w, huu, hww, huw]
  field_simp [(pos_sp_sub_AB h).ne', (pos_sp_sub_BC h).ne', (pos_sp h).ne', dsum_ne h,
    (pos_BC h).ne', (pos_CA h).ne', (pos_AB h).ne']
  rw [show sp A B C = (dist B C + dist C A + dist A B) / 2 from rfl]
  ring

/-- The angle ∠RIS is acute. -/
lemma acute_angle (h : ¬ Collinear ℝ ({A, B, C} : Set Plane)) :
    InnerProductGeometry.angle (ptR A B C - incenterPt A B C)
      (ptS A B C - incenterPt A B C) < π / 2 := by
  have hpos : 0 < ((sp A B C - dist B C) * (sp A B C - dist C A) * (sp A B C - dist A B)) /
      sp A B C :=
    div_pos (mul_pos (mul_pos (pos_sp_sub_BC h) (pos_sp_sub_CA h)) (pos_sp_sub_AB h))
      (pos_sp h)
  have hR : ptR A B C - incenterPt A B C ≠ 0 := by
    intro hz
    have h1 := inner_RS h
    rw [hz, inner_zero_left] at h1
    linarith
  have hS : ptS A B C - incenterPt A B C ≠ 0 := by
    intro hz
    have h1 := inner_RS h
    rw [hz, inner_zero_right] at h1
    linarith
  simp only [InnerProductGeometry.angle]
  rw [Real.arccos_lt_pi_div_two, inner_RS h]
  exact div_pos hpos (mul_pos (norm_pos_iff.mpr hR) (norm_pos_iff.mpr hS))

snip end

problem imo1998_p5 (A B C : Plane) (h : ¬ Collinear ℝ ({A, B, C} : Set Plane)) :
    (∃ ζ : ℝ, ptR A B C - B = ζ • (touchK A B C - touchM A B C)) ∧
    (∃ η : ℝ, ptS A B C - B = η • (touchK A B C - touchM A B C)) ∧
    (∃ τ : ℝ, ptR A B C = touchM A B C + τ • (touchL A B C - touchM A B C)) ∧
    (∃ υ : ℝ, ptS A B C = touchK A B C + υ • (touchL A B C - touchK A B C)) ∧
    InnerProductGeometry.angle (ptR A B C - incenterPt A B C)
      (ptS A B C - incenterPt A B C) < π / 2 :=
  ⟨parallel_R h, parallel_S h, online_R h, online_S h, acute_angle h⟩

end

end Imo1998P5
