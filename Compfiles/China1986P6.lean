/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: sjfhsjfh
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Basic
import Mathlib.Geometry.Euclidean.Sphere.Basic

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# China Mathematical Olympiad 1986, Problem 6

用任意的方式，给平面上的每一个点染上黑色或白色。
求证：一定存在一个边长为 1 或 √3 的正三角形，它的三个顶点是同色的。

Suppose that each point on the plane is colored either white or black.
Show that there exists an equilateral triangle with side length equal to 1 or √3
whose three vertices are in the same color.
-/

namespace China1986P6

abbrev Pt := EuclideanSpace ℝ (Fin 2)

/-- Three points form an equilateral triangle of side length `d`. -/
def Equilateral (A B C : Pt) (d : ℝ) : Prop :=
  dist A B = d ∧ dist B C = d ∧ dist C A = d

snip begin

noncomputable def rot90 (v : Pt) : Pt := !₂[-v 1, v 0]

lemma rot90_smul {v : Pt} {r : ℝ} : rot90 (r • v) = r • rot90 v := by
  simp [rot90, ← WithLp.toLp_smul]

@[simp]
lemma rot90_inner {v : Pt} : inner ℝ v (rot90 v) = 0 := by
  simp [inner, rot90]; rewrite [add_comm, ← sub_eq_add_neg, sub_eq_zero]
  exact mul_comm _ _

@[simp]
lemma rot90_inner' {v : Pt} : inner ℝ (rot90 v) v = 0 := by
  rewrite [real_inner_comm]; exact rot90_inner

@[simp]
lemma norm_rot90 {v : Pt} : ‖rot90 v‖ = ‖v‖ := by
  simp only [norm_eq_sqrt_real_inner]; congr 1
  simp only [inner]; simp [rot90]
  exact add_comm _ _

lemma rot90_dist {v : Pt} {r1 r2 : ℝ}
  : dist (r1 • v) (r2 • rot90 v) = √(r1 ^ 2 + r2 ^ 2) * ‖v‖ := by
  rewrite [dist_eq_norm, norm_eq_sqrt_real_inner]
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right]
  simp [← mul_assoc, ← sq]; rewrite [← add_mul, mul_comm, Real.sqrt_mul (sq_nonneg _)]
  rewrite [Real.sqrt_sq <| norm_nonneg v, mul_comm]; rfl

lemma existsEquidistant (A B : Pt) (d : ℝ) (hd : d > 0)
  (hle : dist A B ≤ 2 * d) (hne : A ≠ B)
  : ∃ C : Pt, dist A C = d ∧ dist B C = d := by
  let (eq := hv) v := A -ᵥ B
  let v' := ‖v‖⁻¹ • v
  let O := midpoint ℝ A B
  have hAO : A = O + ((1 : ℝ) / 2) • (A -ᵥ B) := by
    simp [O, midpoint, AffineMap.lineMap]
    rewrite [add_comm, ← add_assoc, ← smul_add, sub_add_sub_cancel,
      sub_self, smul_zero, zero_add]; rfl
  have hBO : B = O - ((1 : ℝ) / 2) • (A -ᵥ B) := by
    simp [O, midpoint, AffineMap.lineMap]
    rewrite [add_comm, sub_eq_add_neg, ← smul_neg, neg_sub, add_assoc, ← add_smul,
      show (2 : ℝ)⁻¹ + 2⁻¹ = 1 by norm_num, one_smul, add_sub_cancel]; rfl
  by_cases! hv₀ : v = 0
  · rewrite [hv₀] at hv
    have := vsub_eq_zero_iff_eq.mp hv.symm; subst this
    absurd hne; rfl
  use O +ᵥ √(d ^ 2 - (dist A B / 2) ^ 2) • rot90 v'; simp only [vadd_eq_add]
  nth_rewrite 1 [hAO]; rewrite [dist_add_left, ← hv]; nth_rewrite 2 [hBO]
  rewrite [sub_eq_add_neg O, dist_add_left, ← hv, ← neg_smul]
  simp only [v', rot90_smul, smul_smul, rot90_dist]; simp
  rewrite [dist_eq_norm_vsub, show A -ᵥ B = v by rfl] at ⊢ hle
  have h_dsvs : d ^ 2 - (‖v‖ / 2) ^ 2 ≥ 0 := by
    have : ‖v‖ / 2 ≥ 0 := div_nonneg (norm_nonneg v) zero_le_two
    refine sub_nonneg_of_le <| (sq_le_sq₀ (this) hd.le).mpr ?_
    refine (div_le_iff₀ zero_lt_two).mpr ?_; rewrite [mul_comm]
    exact hle
  rewrite [
    mul_pow, Real.sq_sqrt h_dsvs, sub_mul, ← mul_pow (_ / _), ← div_eq_mul_inv,
    div_div_cancel_left' <| norm_eq_zero.not.mpr hv₀, sq, mul_inv, ← sq,
    add_sub_cancel, Real.sqrt_mul <| sq_nonneg d, Real.sqrt_sq hd.le,
    sq, ← mul_inv, Real.sqrt_inv, ← sq, Real.sqrt_sq <| norm_nonneg v,
    mul_assoc, inv_mul_cancel₀ <| norm_eq_zero.not.mpr hv₀, mul_one,
  ]; rfl

lemma exists2Equidistant {A B : Pt} {d : ℝ} (h : dist A B = d)
  : let O := midpoint ℝ A B
  ∃ C D : Pt, (Equilateral A C O <| 1 / 2 * d)
    ∧ (Equilateral A D O <| 1 / 2 * d) ∧ (Equilateral B C D <| √3 / 2 * d)
  := by
  by_cases! hAB : A = B
  · subst hAB; use A, A; simp [Equilateral]; rewrite [← h]; exact dist_self A
  have hd : d > 0 := by rewrite [← h]; exact dist_pos.mpr hAB
  let v := B - A; let v' := ‖v‖⁻¹ • v; let v'' := (√3 / 4) • rot90 v;
  have hv : ‖v‖ = d := by rewrite [← h, dist_comm, dist_eq_norm]; rfl
  rewrite [show B = A + v by exact (add_sub_cancel A B).symm]
  intro O; have hO : O = A + ((1 : ℝ) / 2) • v := by
    simp [O, midpoint, AffineMap.lineMap]; exact add_comm _ A
  use O - ((1 : ℝ) / 4) • v + v'', O - ((1 : ℝ) / 4) • v - v''
  simp [Equilateral, hO, add_assoc, ← add_sub, ← sub_smul, v'']
  norm_num; simp only [norm_eq_sqrt_real_inner, dist_eq_norm]
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right]
  simp only [inner_smul_left, inner_smul_right, rot90_inner, rot90_inner']
  simp only [mul_zero, zero_add, add_zero, sub_zero]; simp [hv, ← mul_assoc, ← sq]
  rewrite [show (√3 / 4) ^ 2 = 3 / 16 by
    rw [sq, div_mul_div_comm, ← sq, Real.sq_sqrt zero_le_three]; norm_num]
  simp only [← add_mul, ← sub_eq_add_neg, ← sub_mul, ← sub_one_mul, ← one_sub_mul]
  have h4sqrt : √4 = 2 := by
    rewrite [show (4 : ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq zero_le_two
  norm_num; rewrite [Real.sqrt_sq hd.le, h4sqrt]; simp

variable (color : Pt → Fin 2)

lemma allSameofDistSame (d : ℝ) (hd : d > 0)
  : (∀ (A B : Pt), dist A B = d → color A = color B)
    → (∀ (A B : Pt), color A = color B) := by
  intro hdist A B
  have h : ∀ (A B : Pt), dist A B ≤ 2 * d → color A = color B := by
    intro A B hle
    by_cases! hAB : A = B
    · exact congrArg color hAB
    obtain ⟨C, ⟨hAC, hBC⟩⟩ := existsEquidistant A B d hd hle hAB
    rewrite [hdist A C hAC, hdist B C hBC]; rfl
  suffices h : ∀ (n : ℕ), ∀ (A B : Pt),
    n = Nat.floor (dist A B / d) → color A = color B by
    exact h ⌊dist A B / d⌋₊ A B rfl
  intro n
  induction n with
  | succ n ih =>
    intro A B hn
    suffices h : ∃ P : Pt, n = ⌊dist P B / d⌋₊ ∧ dist A P = d by
      obtain ⟨P, ⟨hPn, hPd⟩⟩ := h
      exact hdist A P hPd |>.trans <| ih P B hPn
    let (eq := hv) v := B - A; use A + (d / ‖v‖) • v
    have hvne₀ : v ≠ 0 := by
      by_contra! h; rewrite [h, eq_sub_iff_add_eq, zero_add] at hv
      subst hv; simp at hn
    have hnonneg : dist A B / d - 1 ≥ 0 := by
      refine sub_nonneg_of_le ?_
      by_contra! h;
      absurd Nat.floor_lt_one (div_nonneg dist_nonneg hd.le) |>.mpr h
      simp [← hn]
    simp [dist_eq_norm, norm_smul];
    rewrite [add_comm, add_sub_assoc, ← neg_sub, ← sub_eq_add_neg, ← hv,
      div_mul_cancel₀ |d| <| norm_eq_zero.not.mpr hvne₀, abs_of_pos hd,
      ← one_smul ℝ v, smul_smul, ← sub_smul, norm_smul]
    simp only [one_smul, mul_one, Real.norm_eq_abs, and_true]
    rewrite [
      ← neg_sub, abs_neg, ← abs_of_nonneg <| norm_nonneg v, ← abs_mul, sub_mul,
      abs_of_nonneg <| norm_nonneg v, one_mul, ← abs_of_pos hd, ← abs_div,
      div_mul_cancel₀ |d| <| norm_eq_zero.not.mpr hvne₀, abs_of_pos hd, sub_div,
      div_self hd.ne', Nat.eq_sub_of_add_eq hn, ← Nat.floor_sub_one,
      hv, ← dist_eq_norm', abs_of_nonneg hnonneg,
    ]; rfl
  | zero =>
    intro A B hn; refine h A B <| le_of_lt <| lt_trans ?_ <| lt_two_mul_self hd
    exact div_lt_one hd |>.mp <| Nat.floor_eq_zero.mp hn.symm

lemma fin2ne {a b c : Fin 2} (hab : a ≠ b) (hbc : b ≠ c) : a = c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp_all

lemma choose2mid (A B : Pt) (hdist : dist A B = 2)
  (hcolor : color A ≠ color B)
  : ∃ A O B : Pt, O = midpoint ℝ A B ∧ dist A B = 2 ∧ color A ≠ color B
    ∧ color O = color A := by
  set O := midpoint ℝ A B
  by_cases! hOA : color O = color A
  · use A, O, B
  · use B, O, A
    rewrite [midpoint_comm, dist_comm, hdist]; simp only [true_and, O]
    exact ⟨hcolor.symm, fin2ne hOA hcolor⟩

snip end

problem china1986_p6 (color : Pt → Fin 2)
  : ∃ (A B C : Pt),
    (Equilateral A B C 1 ∨ Equilateral A B C √3)
    ∧ color A = color B ∧ color B = color C := by
  by_cases! h_monochrome : ∀ (A B : Pt), color A = color B
  · let A : Pt := !₂[-1 / 2, 0]
    let B : Pt := !₂[0, √3 / 2]
    let C : Pt := !₂[1 / 2, 0]
    use A, B, C; simp only [h_monochrome A B, h_monochrome B C, and_true]
    refine Or.inl ?_; simp [Equilateral, A, B, C, dist, sq]; field_simp
    simp only [Nat.ofNat_nonneg, Real.sq_sqrt]; refine ⟨?_, ?_, ?_⟩ <;> ring
  have hex2 : ¬ (∀ (A B : Pt), dist A B = 2 → color A = color B) := by
    intro h; obtain ⟨A, B, hAB⟩ := h_monochrome
    exact hAB <| allSameofDistSame color 2 (by norm_num) h A B
  push Not at hex2; obtain ⟨A, B, hdist, hcolor⟩ := hex2
  by_cases! hO : color (midpoint ℝ A B) = color A
  · obtain ⟨C, D, ⟨hACO, hADO, hBCD⟩⟩ := exists2Equidistant hdist
    simp at hACO hADO hBCD; set O := midpoint ℝ A B
    by_cases! hC : color C = color A
    · use A, C, O; simp [hACO, hC, hO]
    by_cases! hD : color D = color A
    · use A, D, O; simp [hADO, hD, hO]
    use B, C, D; simp [hBCD, fin2ne hD hC.symm, fin2ne hC hcolor]
  · rewrite [dist_comm] at hdist; rewrite [midpoint_comm] at hO
    obtain ⟨C, D, ⟨hBCO, hBDO, hACD⟩⟩ := exists2Equidistant hdist
    simp at hBCO hBDO hACD; set O := midpoint ℝ B A
    by_cases! hC : color C = color B
    · use B, C, O; simp [hBCO, hC, fin2ne hO hcolor]
    by_cases! hD : color D = color B
    · use B, D, O; simp [hBDO, hD, fin2ne hO hcolor]
    use A, C, D; simp [hACD, fin2ne hD hC.symm]; exact fin2ne hcolor hC.symm

end China1986P6
