/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Real.Sqrt
public import ProblemExtraction

@[expose] public section

problem_file {
  tags := [.Geometry]
  solutionImportedFrom := "https://prase.cz/kalva/imo/isoln/isoln726.html"
}

/-!
# International Mathematical Olympiad 1972, Problem 6

Given four distinct parallel planes, prove that there exists a regular
tetrahedron with a vertex on each plane.

# Solution

We model the four planes as the level sets `{x | ⟪n, x⟫ = c i}` of a common
nonzero normal vector `n : ℝ³` at four distinct offsets `c i`. Normalizing,
we may assume that `ν = n/‖n‖` is a unit vector; write `k i` for the rescaled
offsets, `km` for their mean and `d i = k i - km`, so that `∑ i, d i = 0`.

Start from the standard regular tetrahedron with vertices
`v₀ = (1,1,1)`, `v₁ = (1,-1,-1)`, `v₂ = (-1,1,-1)`, `v₃ = (-1,-1,1)`.
The only linear relation among these four vectors is that their sum is zero,
so the system `⟪w, vᵢ⟫ = d i` has the solution
`w = ((d₀+d₁)/2, (d₀+d₂)/2, (d₀+d₃)/2)`. Put `s = ‖w‖` and `u = w/s`, and let
`H` be a linear isometry with `H ν = u` (the identity if `ν = u`, otherwise
the reflection across the hyperplane perpendicular to `ν - u`). Then the
points `P i = s • H vᵢ + km • ν` satisfy `⟪ν, P i⟫ = k i` and are pairwise at
distance `s√8`, so they form a regular tetrahedron with one vertex on each
(rescaled) plane; rescaling back gives the result for the original planes.
-/

namespace Imo1972P6

open scoped RealInnerProductSpace

/-- Three-dimensional Euclidean space. -/
abbrev Pt := EuclideanSpace ℝ (Fin 3)

snip begin

/-- The vertices of the regular tetrahedron inscribed in the cube `{-1,1}³`,
used as the starting configuration of the construction. -/
def tet : Fin 4 → Pt := ![!₂[1, 1, 1], !₂[1, -1, -1], !₂[-1, 1, -1], !₂[-1, -1, 1]]

@[simp] lemma tet_zero : tet 0 = !₂[1, 1, 1] := rfl
@[simp] lemma tet_one : tet 1 = !₂[1, -1, -1] := rfl
@[simp] lemma tet_two : tet 2 = !₂[-1, 1, -1] := rfl
@[simp] lemma tet_three : tet 3 = !₂[-1, -1, 1] := rfl

@[simp] lemma euc_apply_zero (a b c : ℝ) : (!₂[a, b, c] : Pt) 0 = a := by simp

@[simp] lemma euc_apply_one (a b c : ℝ) : (!₂[a, b, c] : Pt) 1 = b := by simp

@[simp] lemma euc_apply_two (a b c : ℝ) : (!₂[a, b, c] : Pt) 2 = c := by simp

/-- The inner product on `ℝ³` in coordinates. -/
@[simp] lemma inner_pt (a b : Pt) : ⟪a, b⟫ = a 0 * b 0 + a 1 * b 1 + a 2 * b 2 := by
  rw [PiLp.inner_apply, Fin.sum_univ_three]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

lemma inner_tet_diag (i : Fin 4) : ⟪tet i, tet i⟫ = 3 := by
  fin_cases i <;> simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three] <;> norm_num

lemma inner_tet_off {i j : Fin 4} (h : i ≠ j) : ⟪tet i, tet j⟫ = -1 := by
  fin_cases i <;> fin_cases j <;> simp at h ⊢

/-- All edges of the standard tetrahedron `tet` have length `√8`. -/
lemma dist_tet {i j : Fin 4} (h : i ≠ j) : dist (tet i) (tet j) = Real.sqrt 8 := by
  have hsq : dist (tet i) (tet j) ^ 2 = 8 := by
    rw [dist_eq_norm, norm_sub_sq_real, ← real_inner_self_eq_norm_sq (tet i),
      ← real_inner_self_eq_norm_sq (tet j), inner_tet_diag, inner_tet_diag, inner_tet_off h]
    norm_num
  rw [← Real.sqrt_sq dist_nonneg, hsq]

/-- For any `d` with `∑ i, d i = 0` there is a vector `w` whose inner products
with the vertices of `tet` are the `d i`: the only linear relation among the
four vertices is that their sum vanishes. -/
lemma exists_inner_tet (d : Fin 4 → ℝ) (hd : ∑ i, d i = 0) :
    ∃ w : Pt, ∀ i : Fin 4, ⟪w, tet i⟫ = d i := by
  refine ⟨!₂[(d 0 + d 1) / 2, (d 0 + d 2) / 2, (d 0 + d 3) / 2], fun i => ?_⟩
  rw [Fin.sum_univ_four] at hd
  fin_cases i <;> simp <;> linarith

/-- Reflection across the hyperplane perpendicular to `m`. -/
noncomputable def refl (m x : Pt) : Pt := x - (2 * ⟪x, m⟫) • m

lemma inner_self_of_norm_one {m : Pt} (hm : ‖m‖ = 1) : ⟪m, m⟫ = 1 := by
  rw [real_inner_self_eq_norm_sq, hm, one_pow]

lemma refl_sub (m x y : Pt) : refl m x - refl m y = refl m (x - y) := by
  simp only [refl, inner_sub_left, mul_sub, sub_smul]
  abel

lemma refl_symm (m x y : Pt) : ⟪refl m x, y⟫ = ⟪x, refl m y⟫ := by
  simp only [refl, inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm y m]
  ring

lemma refl_inner {m : Pt} (hm : ‖m‖ = 1) (x y : Pt) : ⟪refl m x, refl m y⟫ = ⟪x, y⟫ := by
  simp only [refl, inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm y m, inner_self_of_norm_one hm]
  ring

lemma refl_norm {m : Pt} (hm : ‖m‖ = 1) (x : Pt) : ‖refl m x‖ = ‖x‖ := by
  rw [norm_eq_sqrt_real_inner, refl_inner hm, ← norm_eq_sqrt_real_inner]

lemma refl_invol {m : Pt} (hm : ‖m‖ = 1) (x : Pt) : refl m (refl m x) = x := by
  have h1 : ⟪refl m x, m⟫ = -⟪x, m⟫ := by
    show ⟪x - (2 * ⟪x, m⟫) • m, m⟫ = -⟪x, m⟫
    rw [inner_sub_left, real_inner_smul_left, inner_self_of_norm_one hm]
    ring
  show refl m x - (2 * ⟪refl m x, m⟫) • m = x
  rw [h1]
  show x - (2 * ⟪x, m⟫) • m - (2 * -⟪x, m⟫) • m = x
  rw [mul_neg, neg_smul, sub_neg_eq_add, sub_add_cancel]

/-- The reflection across the hyperplane perpendicular to `ν - u` swaps the two
distinct unit vectors `u` and `ν`. -/
lemma refl_apply_of_unit {u ν : Pt} (hu : ‖u‖ = 1) (hν : ‖ν‖ = 1) (h : u ≠ ν) :
    refl ((‖ν - u‖)⁻¹ • (ν - u)) u = ν := by
  have hsub : ν - u ≠ 0 := sub_ne_zero_of_ne (Ne.symm h)
  have hn0 : ‖ν - u‖ ≠ 0 := norm_ne_zero_iff.mpr hsub
  have hnsq : ‖ν - u‖ ^ 2 = 2 - 2 * ⟪u, ν⟫ := by
    rw [norm_sub_sq_real, hν, hu, one_pow, real_inner_comm u ν]
    ring
  have hval : (2 * ⟪u, (‖ν - u‖)⁻¹ • (ν - u)⟫) • ((‖ν - u‖)⁻¹ • (ν - u)) = u - ν := by
    have him : ⟪u, (‖ν - u‖)⁻¹ • (ν - u)⟫ = ‖ν - u‖⁻¹ * (⟪u, ν⟫ - 1) := by
      rw [real_inner_smul_right, inner_sub_right, real_inner_self_eq_norm_sq, hu, one_pow]
    rw [him, smul_smul]
    have hden : (2 : ℝ) - 2 * ⟪u, ν⟫ ≠ 0 := by
      rw [← hnsq]
      exact pow_ne_zero 2 hn0
    have e : ‖ν - u‖⁻¹ * ‖ν - u‖⁻¹ = (2 - 2 * ⟪u, ν⟫)⁻¹ := by
      rw [← hnsq, pow_two, mul_inv_rev]
    have hcoef : 2 * (‖ν - u‖⁻¹ * (⟪u, ν⟫ - 1)) * ‖ν - u‖⁻¹ = -1 := by
      calc 2 * (‖ν - u‖⁻¹ * (⟪u, ν⟫ - 1)) * ‖ν - u‖⁻¹
          = 2 * (⟪u, ν⟫ - 1) * (‖ν - u‖⁻¹ * ‖ν - u‖⁻¹) := by ring
        _ = 2 * (⟪u, ν⟫ - 1) * (2 - 2 * ⟪u, ν⟫)⁻¹ := by rw [e]
        _ = -1 := by
          rw [← div_eq_mul_inv, div_eq_iff hden]
          ring
    rw [hcoef, neg_one_smul, neg_sub]
  show u - (2 * ⟪u, (‖ν - u‖)⁻¹ • (ν - u)⟫) • ((‖ν - u‖)⁻¹ • (ν - u)) = ν
  rw [hval]
  abel

/-- Any two unit vectors of `ℝ³` are swapped by a self-adjoint linear
isometry: the identity if they are equal, and a hyperplane reflection
otherwise. -/
lemma exists_isometry (u ν : Pt) (hu : ‖u‖ = 1) (hν : ‖ν‖ = 1) :
    ∃ H : Pt → Pt,
      (∀ x y : Pt, ⟪H x, H y⟫ = ⟪x, y⟫) ∧
      (∀ x y : Pt, H x - H y = H (x - y)) ∧
      (∀ x y : Pt, ⟪H x, y⟫ = ⟪x, H y⟫) ∧
      (∀ x : Pt, ‖H x‖ = ‖x‖) ∧
      H ν = u := by
  by_cases h : u = ν
  · exact ⟨id, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl, h.symm⟩
  · have hn0 : ‖ν - u‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero_of_ne (Ne.symm h))
    have hm : ‖(‖ν - u‖)⁻¹ • (ν - u)‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
        inv_mul_cancel₀ hn0]
    refine ⟨refl ((‖ν - u‖)⁻¹ • (ν - u)), refl_inner hm, refl_sub _, refl_symm _,
      refl_norm hm, ?_⟩
    have h2 := refl_apply_of_unit hu hν h
    have h3 := refl_invol hm u
    rw [h2] at h3
    exact h3

/-- The unit-normal form of the problem: for a unit vector `ν` and four
distinct offsets `k i`, there is a regular tetrahedron whose `i`-th vertex
lies on the plane `{x | ⟪ν, x⟫ = k i}`. -/
lemma exists_tet_unit (ν : Pt) (hν : ‖ν‖ = 1) (k : Fin 4 → ℝ) (hk : k.Injective) :
    ∃ p : Fin 4 → Pt,
      (∀ i j : Fin 4, i ≠ j → dist (p i) (p j) = dist (p 0) (p 1)) ∧
      p 0 ≠ p 1 ∧ ∀ i : Fin 4, ⟪ν, p i⟫ = k i := by
  set km := (∑ i, k i) / 4 with hkm
  have hd_sum : ∑ i, (k i - km) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, hkm]
    ring
  obtain ⟨w, hw⟩ := exists_inner_tet (fun i => k i - km) hd_sum
  have hw' : ∀ i : Fin 4, ⟪w, tet i⟫ = k i - km := hw
  have hwne : w ≠ 0 := by
    intro hw0
    have e0 : ⟪w, tet 0⟫ = 0 := by rw [hw0]; exact inner_zero_left _
    have e1 : ⟪w, tet 1⟫ = 0 := by rw [hw0]; exact inner_zero_left _
    rw [hw'] at e0 e1
    have h01 : k 0 ≠ k 1 := hk.ne (by decide)
    exact h01 (by linarith)
  have hws : 0 < ‖w‖ := norm_pos_iff.mpr hwne
  have hu : ‖(‖w‖)⁻¹ • w‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hws.le),
      inv_mul_cancel₀ hws.ne']
  obtain ⟨H, hHinner, hHsub, hHsymm, hHnorm, hHν⟩ := exists_isometry ((‖w‖)⁻¹ • w) ν hu hν
  have hinner : ∀ i : Fin 4, ⟪ν, ‖w‖ • H (tet i) + km • ν⟫ = k i := by
    intro i
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right,
      ← hHsymm ν (tet i), hHν, real_inner_smul_left, hw' i, inner_self_of_norm_one hν,
      ← mul_assoc, mul_inv_cancel₀ hws.ne', one_mul]
    ring
  have key : ∀ a b : Fin 4, a ≠ b →
      dist (‖w‖ • H (tet a) + km • ν) (‖w‖ • H (tet b) + km • ν) = ‖w‖ * Real.sqrt 8 := by
    intro a b hab
    have e1 : ‖w‖ • H (tet a) + km • ν - (‖w‖ • H (tet b) + km • ν) =
        ‖w‖ • H (tet a - tet b) := by
      rw [← hHsub (tet a) (tet b)]
      module
    rw [dist_eq_norm, e1, norm_smul, Real.norm_eq_abs, abs_of_pos hws, hHnorm,
      ← dist_eq_norm, dist_tet hab]
  refine ⟨fun i => ‖w‖ • H (tet i) + km • ν, fun i j hij => ?_, ?_, fun i => ?_⟩
  · dsimp only
    rw [key i j hij, key 0 1 (by decide)]
  · dsimp only
    intro hp
    have h01 : k 0 ≠ k 1 := hk.ne (by decide)
    have e0 := hinner 0
    have e1 := hinner 1
    rw [hp] at e0
    exact h01 (e0.symm.trans e1)
  · dsimp only
    exact hinner i

snip end

problem imo1972_p6 (n : Pt) (hn : n ≠ 0) (c : Fin 4 → ℝ) (hc : c.Injective) :
    ∃ p : Fin 4 → Pt,
      (∀ i j : Fin 4, i ≠ j → dist (p i) (p j) = dist (p 0) (p 1)) ∧
      p 0 ≠ p 1 ∧ ∀ i : Fin 4, ⟪n, p i⟫ = c i := by
  have hnn : 0 < ‖n‖ := norm_pos_iff.mpr hn
  have hν : ‖(‖n‖)⁻¹ • n‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hnn.le),
      inv_mul_cancel₀ hnn.ne']
  have hk : Function.Injective (fun i => (‖n‖)⁻¹ * c i) :=
    fun _ _ hij => hc (mul_left_cancel₀ (inv_ne_zero hnn.ne') hij)
  obtain ⟨p, hdist, hne, hinner⟩ := exists_tet_unit ((‖n‖)⁻¹ • n) hν _ hk
  refine ⟨p, hdist, hne, fun i => ?_⟩
  have e := hinner i
  rw [real_inner_smul_left] at e
  exact mul_left_cancel₀ (inv_ne_zero hnn.ne') e

end Imo1972P6
