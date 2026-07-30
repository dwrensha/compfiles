/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 2013, Problem 4

Let ABC be an acute triangle with orthocenter H, and let W be a point on
the side BC, between B and C. The points M and N are the feet of the
altitudes drawn from B and C, respectively. Suppose ω₁ is the circumcircle
of triangle BWN and X is a point such that WX is a diameter of ω₁.
Similarly, ω₂ is the circumcircle of triangle CWM and Y is a point such
that WY is a diameter of ω₂. Show that the points X, Y, and H are collinear.
-/

namespace Imo2013P4

abbrev Pt := EuclideanSpace ℝ (Fin 2)

open scoped RealInnerProductSpace

snip begin

theorem Pt.ext {x y : Pt} (h0 : x 0 = y 0) (h1 : x 1 = y 1) : x = y := by
  apply WithLp.ofLp_injective (p := 2)
  funext i
  fin_cases i <;> assumption

theorem inner_pt (n x : Pt) : ⟪n, x⟫ = n 0 * x 0 + n 1 * x 1 := by
  rw [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, RCLike.inner_apply]
  simp only [conj_trivial]
  ring

/-- If the 2D cross product of `u` and `v` vanishes and `v ≠ 0`,
then `u` is a scalar multiple of `v`. -/
theorem eq_smul_of_cross_eq_zero {u v : Pt} (hv : v ≠ 0)
    (h : u 0 * v 1 - u 1 * v 0 = 0) : ∃ t : ℝ, u = t • v := by
  have hv' : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hv (Pt.ext (by simpa using hc.1) (by simpa using hc.2))
  rcases hv' with h0 | h1
  · refine ⟨u 0 / v 0, Pt.ext ?_ ?_⟩
    · rw [PiLp.smul_apply, smul_eq_mul]
      field_simp
    · rw [PiLp.smul_apply, smul_eq_mul]
      field_simp
      linarith
  · refine ⟨u 1 / v 1, Pt.ext ?_ ?_⟩
    · rw [PiLp.smul_apply, smul_eq_mul]
      field_simp
      linarith
    · rw [PiLp.smul_apply, smul_eq_mul]
      field_simp

theorem collinear_triple_of_sub_eq_smul {z w x : Pt} (t : ℝ)
    (h : x - z = t • (w - z)) : Collinear ℝ {z, w, x} := by
  rw [collinear_iff_of_mem (Set.mem_insert z {w, x})]
  refine ⟨w - z, fun p hp => ?_⟩
  rcases hp with rfl | rfl | rfl
  · exact ⟨0, by simp⟩
  · exact ⟨1, by simp⟩
  · exact ⟨t, by rw [← h]; simp⟩

theorem collinear_of_cross_eq_zero {z w x : Pt} (hwz : w ≠ z)
    (h : (x - z) 0 * (w - z) 1 - (x - z) 1 * (w - z) 0 = 0) :
    Collinear ℝ {z, w, x} := by
  obtain ⟨t, ht⟩ := eq_smul_of_cross_eq_zero (sub_ne_zero.mpr hwz) h
  exact collinear_triple_of_sub_eq_smul t ht

/-- The coordinate heart of the problem.  Working in the plane with `B` at
the origin, write `p = A - B`, `e = C - B`, and let `W = w • e`,
`N = ν • p`, `M = (1 - μ) • p + μ • e`.  The hypotheses are the foot-of-altitude
and diameter (Thales) conditions, expanded in coordinates; the conclusion is
the vanishing of the cross product of `h - x` and `y - x`, where
`h = H - B`, `x = X - B`, `y = Y - B`. -/
theorem aux {p e h x y : Pt} {ν μ w : ℝ}
    (hw0 : w ≠ 0) (hw1 : w ≠ 1) (hν : ν ≠ 0) (hμ : μ ≠ 1)
    (hΔ : e 0 * p 1 - e 1 * p 0 ≠ 0)
    (hN : ν * (p 0 ^ 2 + p 1 ^ 2) = p 0 * e 0 + p 1 * e 1)
    (hM : (1 - μ) * (p 0 * (e 0 - p 0) + p 1 * (e 1 - p 1)) +
        μ * (e 0 * (e 0 - p 0) + e 1 * (e 1 - p 1)) = 0)
    (hH1 : (p 0 - h 0) * e 0 + (p 1 - h 1) * e 1 = 0)
    (hH2 : h 0 * (p 0 - e 0) + h 1 * (p 1 - e 1) = 0)
    (hX1 : w * (e 0 * x 0 + e 1 * x 1) = 0)
    (hX2 : (w * e 0 - ν * p 0) * (x 0 - ν * p 0) +
        (w * e 1 - ν * p 1) * (x 1 - ν * p 1) = 0)
    (hY1 : (w - 1) * (e 0 * (y 0 - e 0) + e 1 * (y 1 - e 1)) = 0)
    (hY2 : ((w - μ) * e 0 - (1 - μ) * p 0) * (y 0 - (1 - μ) * p 0 - μ * e 0) +
        ((w - μ) * e 1 - (1 - μ) * p 1) * (y 1 - (1 - μ) * p 1 - μ * e 1) = 0) :
    (h 0 - x 0) * (y 1 - x 1) - (h 1 - x 1) * (y 0 - x 0) = 0 := by
  -- Solve the two linear equations determining `h`.
  have hHe : e 0 * h 0 + e 1 * h 1 = p 0 * e 0 + p 1 * e 1 := by
    linear_combination -hH1
  have hHp : p 0 * h 0 + p 1 * h 1 = p 0 * e 0 + p 1 * e 1 := by
    linear_combination hH2 - hH1
  have key_h1 : h 0 * (e 0 * p 1 - e 1 * p 0)
      = (p 0 * e 0 + p 1 * e 1) * (p 1 - e 1) := by
    linear_combination p 1 * hHe - e 1 * hHp
  have key_h2 : h 1 * (e 0 * p 1 - e 1 * p 0)
      = (p 0 * e 0 + p 1 * e 1) * (e 0 - p 0) := by
    linear_combination e 0 * hHp - p 0 * hHe
  -- Solve the two linear equations determining `x`.
  have hXe : e 0 * x 0 + e 1 * x 1 = 0 := by
    rcases mul_eq_zero.mp hX1 with hz | hz
    · exact absurd hz hw0
    · exact hz
  have hXpν : ν * (p 0 * x 0 + p 1 * x 1)
      = ν * ((p 0 * e 0 + p 1 * e 1) * (1 - w)) := by
    linear_combination -hX2 + w * hXe + ν * hN
  have hXp : p 0 * x 0 + p 1 * x 1 = (p 0 * e 0 + p 1 * e 1) * (1 - w) :=
    mul_left_cancel₀ hν hXpν
  have key_x1 : x 0 * (e 0 * p 1 - e 1 * p 0)
      = -(p 0 * e 0 + p 1 * e 1) * (1 - w) * e 1 := by
    linear_combination p 1 * hXe - e 1 * hXp
  have key_x2 : x 1 * (e 0 * p 1 - e 1 * p 0)
      = (p 0 * e 0 + p 1 * e 1) * (1 - w) * e 0 := by
    linear_combination e 0 * hXp - p 0 * hXe
  -- Solve the two linear equations determining `y`.
  have hYe : e 0 * y 0 + e 1 * y 1 = e 0 ^ 2 + e 1 ^ 2 := by
    rcases mul_eq_zero.mp hY1 with hz | hz
    · exact absurd (eq_of_sub_eq_zero hz) hw1
    · linear_combination hz
  have hYpμ : (1 - μ) * (p 0 * y 0 + p 1 * y 1)
      = (1 - μ) * ((p 0 * e 0 + p 1 * e 1) +
          w * ((e 0 ^ 2 + e 1 ^ 2) - (p 0 * e 0 + p 1 * e 1))) := by
    linear_combination -hY2 + (w - μ) * hYe - (1 - μ) * hM
  have hYp : p 0 * y 0 + p 1 * y 1
      = (p 0 * e 0 + p 1 * e 1) +
          w * ((e 0 ^ 2 + e 1 ^ 2) - (p 0 * e 0 + p 1 * e 1)) :=
    mul_left_cancel₀ (sub_ne_zero_of_ne hμ.symm) hYpμ
  have key_y1 : y 0 * (e 0 * p 1 - e 1 * p 0)
      = (e 0 ^ 2 + e 1 ^ 2) * p 1 - ((p 0 * e 0 + p 1 * e 1) +
          w * ((e 0 ^ 2 + e 1 ^ 2) - (p 0 * e 0 + p 1 * e 1))) * e 1 := by
    linear_combination p 1 * hYe - e 1 * hYp
  have key_y2 : y 1 * (e 0 * p 1 - e 1 * p 0)
      = e 0 * ((p 0 * e 0 + p 1 * e 1) +
          w * ((e 0 ^ 2 + e 1 ^ 2) - (p 0 * e 0 + p 1 * e 1))) -
        p 0 * (e 0 ^ 2 + e 1 ^ 2) := by
    linear_combination e 0 * hYp - p 0 * hYe
  -- Clear denominators: the conclusion multiplied by `Δ²` is a polynomial identity.
  have hfinal : (h 0 * (e 0 * p 1 - e 1 * p 0) - x 0 * (e 0 * p 1 - e 1 * p 0)) *
        (y 1 * (e 0 * p 1 - e 1 * p 0) - x 1 * (e 0 * p 1 - e 1 * p 0)) -
      (h 1 * (e 0 * p 1 - e 1 * p 0) - x 1 * (e 0 * p 1 - e 1 * p 0)) *
        (y 0 * (e 0 * p 1 - e 1 * p 0) - x 0 * (e 0 * p 1 - e 1 * p 0)) = 0 := by
    rw [key_h1, key_x1, key_h2, key_x2, key_y1, key_y2]
    ring
  have hscale : (e 0 * p 1 - e 1 * p 0) ^ 2 *
      ((h 0 - x 0) * (y 1 - x 1) - (h 1 - x 1) * (y 0 - x 0)) = 0 := by
    linear_combination hfinal
  rcases mul_eq_zero.mp hscale with hz | hz
  · exact absurd ((pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hz) hΔ
  · exact hz

snip end

problem imo2013_p4
    (A B C W H M N X Y : Pt)
    -- The triangle `ABC` is acute (each angle has positive cosine).
    (hA : 0 < ⟪B - A, C - A⟫)
    (hB : 0 < ⟪A - B, C - B⟫)
    (hC : 0 < ⟪B - C, A - C⟫)
    -- `H` is the orthocenter: it lies on the altitudes through `A` and `B`.
    (hH₁ : ⟪A - H, B - C⟫ = 0)
    (hH₂ : ⟪B - H, A - C⟫ = 0)
    -- `W` lies strictly between `B` and `C` on side `BC`.
    (hW : W ∈ openSegment ℝ B C)
    -- `M` is the foot of the altitude from `B`: on line `AC` with `BM ⊥ AC`.
    (hM : ∃ μ : ℝ, M = A + μ • (C - A) ∧ ⟪B - M, C - A⟫ = 0)
    -- `N` is the foot of the altitude from `C`: on line `AB` with `CN ⊥ AB`.
    (hN : ∃ ν : ℝ, N = B + ν • (A - B) ∧ ⟪C - N, B - A⟫ = 0)
    -- `WX` is a diameter of the circumcircle of `BWN`
    -- (Thales: the angles at `B` and at `N` are right angles).
    (hX₁ : ⟪W - B, X - B⟫ = 0)
    (hX₂ : ⟪W - N, X - N⟫ = 0)
    -- `WY` is a diameter of the circumcircle of `CWM`.
    (hY₁ : ⟪W - C, Y - C⟫ = 0)
    (hY₂ : ⟪W - M, Y - M⟫ = 0) :
    Collinear ℝ {X, Y, H} := by
  obtain ⟨μ, hMdef, hMin⟩ := hM
  obtain ⟨ν, hNdef, hNin⟩ := hN
  obtain ⟨a, b, ha, hb, hab, hWeq⟩ := hW
  -- Reparametrize the points constructed from `W`, `M`, `N` relative to `B`.
  have hWB : W - B = b • (C - B) := by
    have ha' : a = 1 - b := by linarith
    rw [← hWeq, ha']
    module
  have hNB : N - B = ν • (A - B) := by rw [hNdef]; module
  have hMB : M - B = (A - B) + μ • ((C - B) - (A - B)) := by rw [hMdef]; module
  have hw0 : b ≠ 0 := ne_of_gt hb
  have hw1 : b ≠ 1 := by linarith
  -- Rewrite all inner product conditions in terms of vectors based at `B`.
  have hC' : 0 < -⟪C - B, (A - B) - (C - B)⟫ := by
    have h := hC
    rwa [show B - C = -(C - B) by module, show A - C = (A - B) - (C - B) by module,
      inner_neg_left] at h
  have hA' : 0 < -⟪A - B, (C - B) - (A - B)⟫ := by
    have h := hA
    rwa [show B - A = -(A - B) by module, show C - A = (C - B) - (A - B) by module,
      inner_neg_left] at h
  have hH1c : ⟪(A - B) - (H - B), C - B⟫ = 0 := by
    have h := hH₁
    rwa [show A - H = (A - B) - (H - B) by module, show B - C = -(C - B) by module,
      inner_neg_right, neg_eq_zero] at h
  have hH2c : ⟪H - B, (A - B) - (C - B)⟫ = 0 := by
    have h := hH₂
    rwa [show B - H = -(H - B) by module, show A - C = (A - B) - (C - B) by module,
      inner_neg_left, neg_eq_zero] at h
  have hN1c : ⟪(C - B) - ν • (A - B), A - B⟫ = 0 := by
    have h := hNin
    rwa [show C - N = (C - B) - (N - B) by module, hNB,
      show B - A = -(A - B) by module, inner_neg_right, neg_eq_zero] at h
  have hM1c : ⟪(A - B) + μ • ((C - B) - (A - B)), (C - B) - (A - B)⟫ = 0 := by
    have h := hMin
    rwa [show B - M = -(M - B) by module, hMB,
      show C - A = (C - B) - (A - B) by module, inner_neg_left, neg_eq_zero] at h
  have hX1c : ⟪b • (C - B), X - B⟫ = 0 := by rwa [hWB] at hX₁
  have hX2c : ⟪b • (C - B) - ν • (A - B), (X - B) - ν • (A - B)⟫ = 0 := by
    have h := hX₂
    rwa [show W - N = (W - B) - (N - B) by module, hWB, hNB,
      show X - N = (X - B) - (N - B) by module, hNB] at h
  have hY1c : ⟪(b - 1) • (C - B), (Y - B) - (C - B)⟫ = 0 := by
    have h := hY₁
    rwa [show W - C = (b - 1) • (C - B) by
        rw [show W - C = (W - B) - (C - B) by module, hWB]; module,
      show Y - C = (Y - B) - (C - B) by module] at h
  have hY2c : ⟪b • (C - B) - ((A - B) + μ • ((C - B) - (A - B))),
      (Y - B) - ((A - B) + μ • ((C - B) - (A - B)))⟫ = 0 := by
    have h := hY₂
    rwa [show W - M = (W - B) - (M - B) by module, hWB, hMB,
      show Y - M = (Y - B) - (M - B) by module, hMB] at h
  -- Abbreviations for the relevant vectors based at `B`.
  set p : Pt := A - B with hp
  set e : Pt := C - B with he
  set h' : Pt := H - B with hh
  set x' : Pt := X - B with hx
  set y' : Pt := Y - B with hy
  clear_value p e h' x' y'
  -- Expand the inner products into coordinate equations.
  rw [inner_pt] at hB hA' hC'
  simp only [PiLp.sub_apply] at hA' hC'
  have hN_aux : ν * (p 0 ^ 2 + p 1 ^ 2) = p 0 * e 0 + p 1 * e 1 := by
    rw [inner_pt] at hN1c
    simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at hN1c
    linear_combination -hN1c
  have hM_aux : (1 - μ) * (p 0 * (e 0 - p 0) + p 1 * (e 1 - p 1)) +
      μ * (e 0 * (e 0 - p 0) + e 1 * (e 1 - p 1)) = 0 := by
    rw [inner_pt] at hM1c
    simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at hM1c
    linear_combination hM1c
  have hH1_aux : (p 0 - h' 0) * e 0 + (p 1 - h' 1) * e 1 = 0 := by
    rw [inner_pt] at hH1c
    simp only [PiLp.sub_apply] at hH1c
    linear_combination hH1c
  have hH2_aux : h' 0 * (p 0 - e 0) + h' 1 * (p 1 - e 1) = 0 := by
    rw [inner_pt] at hH2c
    simp only [PiLp.sub_apply] at hH2c
    linear_combination hH2c
  have hX1_aux : b * (e 0 * x' 0 + e 1 * x' 1) = 0 := by
    rw [inner_pt] at hX1c
    simp only [PiLp.smul_apply, smul_eq_mul] at hX1c
    linear_combination hX1c
  have hX2_aux : (b * e 0 - ν * p 0) * (x' 0 - ν * p 0) +
      (b * e 1 - ν * p 1) * (x' 1 - ν * p 1) = 0 := by
    rw [inner_pt] at hX2c
    simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at hX2c
    linear_combination hX2c
  have hY1_aux : (b - 1) * (e 0 * (y' 0 - e 0) + e 1 * (y' 1 - e 1)) = 0 := by
    rw [inner_pt] at hY1c
    simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at hY1c
    linear_combination hY1c
  have hY2_aux : ((b - μ) * e 0 - (1 - μ) * p 0) * (y' 0 - (1 - μ) * p 0 - μ * e 0) +
      ((b - μ) * e 1 - (1 - μ) * p 1) * (y' 1 - (1 - μ) * p 1 - μ * e 1) = 0 := by
    rw [inner_pt] at hY2c
    simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at hY2c
    linear_combination hY2c
  -- Nondegeneracy conditions, from acuteness and from `0 < b < 1`.
  have hν : ν ≠ 0 := by
    intro hν0
    rw [hν0, zero_mul] at hN_aux
    linarith
  have hμ : μ ≠ 1 := by
    intro hμ1
    rw [hμ1] at hM_aux
    simp only [sub_self, zero_mul, zero_add, one_mul] at hM_aux
    linarith [hC']
  have hΔ : e 0 * p 1 - e 1 * p 0 ≠ 0 := by
    intro hΔ0
    have h2 : (e 0 * p 1 - e 1 * p 0) ^ 2 = 0 := by rw [hΔ0]; norm_num
    have hLag : (p 0 * e 0 + p 1 * e 1) ^ 2
        = (p 0 ^ 2 + p 1 ^ 2) * (e 0 ^ 2 + e 1 ^ 2) := by
      linear_combination -h2
    have hP : 0 < p 0 ^ 2 + p 1 ^ 2 := by linarith [hB, hA']
    have hES : 0 < (e 0 ^ 2 + e 1 ^ 2) - (p 0 * e 0 + p 1 * e 1) := by
      linarith [hC']
    have hPS : 0 < (p 0 ^ 2 + p 1 ^ 2) - (p 0 * e 0 + p 1 * e 1) := by
      linarith [hA']
    have key1 := mul_pos hP hES
    have key2 := mul_pos hB hPS
    linarith [hLag, key1, key2]
  -- Apply the coordinate computation.
  have hcross : (h' 0 - x' 0) * (y' 1 - x' 1) - (h' 1 - x' 1) * (y' 0 - x' 0) = 0 :=
    aux hw0 hw1 hν hμ hΔ hN_aux hM_aux hH1_aux hH2_aux hX1_aux hX2_aux hY1_aux hY2_aux
  have eYX : Y - X = y' - x' := by rw [hy, hx]; module
  have eHX : H - X = h' - x' := by rw [hh, hx]; module
  have hcross2 : (H - X) 0 * (Y - X) 1 - (H - X) 1 * (Y - X) 0 = 0 := by
    rw [eHX, eYX]
    simp only [PiLp.sub_apply]
    linear_combination hcross
  by_cases hXY : Y = X
  · have hset : ({X, X, H} : Set Pt) = {X, H} := by
      ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [hXY, hset]
    exact collinear_pair ℝ X H
  · exact collinear_of_cross_eq_zero hXY hcross2

end Imo2013P4
