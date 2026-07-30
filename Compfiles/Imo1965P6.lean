/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics, .Geometry] }

/-!
# International Mathematical Olympiad 1965, Problem 6

In a plane a set of n points (n ≥ 3) is given. Each pair of points is
connected by a segment. Let d be the length of the longest of these
segments. We define a diameter of the set to be any connecting segment
of length d. Prove that the number of diameters of the given set is at
most n.
-/

namespace Imo1965P6

/-- The plane. -/
abbrev P2 := EuclideanSpace ℝ (Fin 2)

snip begin

/-- The dot product on the plane, written out in coordinates. -/
def dotp (u v : P2) : ℝ := u 0 * v 0 + u 1 * v 1

/-- The 2-dimensional cross product (signed area), written out in coordinates. -/
def crsp (u v : P2) : ℝ := u 0 * v 1 - u 1 * v 0

lemma sq_le_sq_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  nlinarith

lemma sq_lt_sq_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) : a ^ 2 < b ^ 2 := by
  nlinarith

lemma dotp_comm (u v : P2) : dotp u v = dotp v u := by
  simp only [dotp]
  ring

lemma dotp_add_left (u v w : P2) : dotp (u + v) w = dotp u w + dotp v w := by
  simp only [dotp, PiLp.add_apply]
  ring

lemma dotp_sub_left (u v w : P2) : dotp (u - v) w = dotp u w - dotp v w := by
  simp only [dotp, PiLp.sub_apply]
  ring

lemma dotp_smul_left (c : ℝ) (u v : P2) : dotp (c • u) v = c * dotp u v := by
  simp only [dotp, PiLp.smul_apply, smul_eq_mul]
  ring

lemma dotp_add_right (u v w : P2) : dotp u (v + w) = dotp u v + dotp u w := by
  simp only [dotp, PiLp.add_apply]
  ring

lemma dotp_sub_right (u v w : P2) : dotp u (v - w) = dotp u v - dotp u w := by
  simp only [dotp, PiLp.sub_apply]
  ring

lemma dotp_smul_right (c : ℝ) (u v : P2) : dotp u (c • v) = c * dotp u v := by
  simp only [dotp, PiLp.smul_apply, smul_eq_mul]
  ring

lemma dotp_zero_left (v : P2) : dotp 0 v = 0 := by
  simp only [dotp, PiLp.zero_apply]
  ring

lemma dotp_self_nonneg (u : P2) : 0 ≤ dotp u u := by
  simp only [dotp]
  exact add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

lemma dotp_self_eq_zero {u : P2} (h : dotp u u = 0) : u = 0 := by
  have h' : u 0 ^ 2 + u 1 ^ 2 = 0 := by
    have h2 := h
    simp only [dotp, ← pow_two] at h2 ⊢
    exact h2
  have h0 : u 0 ^ 2 ≤ 0 := by nlinarith [sq_nonneg (u 1)]
  have h1 : u 1 ^ 2 ≤ 0 := by nlinarith [sq_nonneg (u 0)]
  have g0 : u 0 = 0 := sq_eq_zero_iff.mp (le_antisymm h0 (sq_nonneg _))
  have g1 : u 1 = 0 := sq_eq_zero_iff.mp (le_antisymm h1 (sq_nonneg _))
  apply PiLp.ext
  rw [Fin.forall_fin_two]
  refine ⟨?_, ?_⟩ <;> simp only [PiLp.zero_apply] <;> assumption

lemma dotp_self_pos {u : P2} (hu : u ≠ 0) : 0 < dotp u u :=
  lt_of_le_of_ne (dotp_self_nonneg u) (fun h => hu (dotp_self_eq_zero h.symm))

lemma dotp_sub_sub (u v : P2) : dotp (u - v) (u - v) = dotp u u - 2 * dotp u v + dotp v v := by
  simp only [dotp, PiLp.sub_apply]
  ring

lemma dotp_add_add (u v : P2) : dotp (u + v) (u + v) = dotp u u + 2 * dotp u v + dotp v v := by
  simp only [dotp, PiLp.add_apply]
  ring

lemma dotp_smul2 (a b : ℝ) (u v : P2) :
    dotp (a • u + b • v) (a • u + b • v) =
      a ^ 2 * dotp u u + 2 * a * b * dotp u v + b ^ 2 * dotp v v := by
  simp only [dotp, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

lemma dotp_self_sub (x y : P2) : dotp (x - y) (x - y) = dotp (y - x) (y - x) := by
  simp only [dotp, PiLp.sub_apply]
  ring

lemma crsp_self (u : P2) : crsp u u = 0 := by
  simp only [crsp]
  ring

lemma crsp_skew (u v : P2) : crsp u v = -crsp v u := by
  simp only [crsp]
  ring

lemma crsp_add_left (u v w : P2) : crsp (u + v) w = crsp u w + crsp v w := by
  simp only [crsp, PiLp.add_apply]
  ring

lemma crsp_sub_left (u v w : P2) : crsp (u - v) w = crsp u w - crsp v w := by
  simp only [crsp, PiLp.sub_apply]
  ring

lemma crsp_smul_left (c : ℝ) (u v : P2) : crsp (c • u) v = c * crsp u v := by
  simp only [crsp, PiLp.smul_apply, smul_eq_mul]
  ring

lemma crsp_add_right (u v w : P2) : crsp u (v + w) = crsp u v + crsp u w := by
  simp only [crsp, PiLp.add_apply]
  ring

lemma crsp_sub_right (u v w : P2) : crsp u (v - w) = crsp u v - crsp u w := by
  simp only [crsp, PiLp.sub_apply]
  ring

lemma crsp_smul_right (c : ℝ) (u v : P2) : crsp u (c • v) = c * crsp u v := by
  simp only [crsp, PiLp.smul_apply, smul_eq_mul]
  ring

/-- The 2D Lagrange identity. -/
lemma lagrange (u v : P2) : dotp u u * dotp v v = dotp u v ^ 2 + crsp u v ^ 2 := by
  simp only [dotp, crsp]
  ring

/-- The 2D Lagrange identity for a product of two cross products. -/
lemma lagrange2 (u v w t : P2) :
    crsp u v * crsp w t = dotp u w * dotp v t - dotp u t * dotp v w := by
  simp only [dotp, crsp]
  ring

/-- Cramer's rule in 2D. -/
lemma cramer (u v w : P2) : crsp u v • w = crsp w v • u - crsp w u • v := by
  apply PiLp.ext
  rw [Fin.forall_fin_two]
  refine ⟨?_, ?_⟩ <;>
    simp only [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, crsp] <;> ring

lemma dist_sq (x y : P2) : dist x y ^ 2 = dotp (x - y) (x - y) := by
  rw [dist_eq_norm, EuclideanSpace.norm_eq,
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  simp only [dotp, Fin.sum_univ_two, PiLp.sub_apply, Real.norm_eq_abs, sq_abs]
  ring

lemma dist_le_sq {x y : P2} {e : ℝ} (h : dist x y ≤ e) : dist x y ^ 2 ≤ e ^ 2 :=
  sq_le_sq_of_nonneg dist_nonneg h

lemma crsp_neg_left (u v : P2) : crsp (-u) v = -crsp u v := by
  simp only [crsp, PiLp.neg_apply]
  ring

lemma crsp_neg_right (u v : P2) : crsp u (-v) = -crsp u v := by
  simp only [crsp, PiLp.neg_apply]
  ring

lemma dotp_add_smul (b : ℝ) (u v : P2) :
    dotp (u + b • v) (u + b • v) = dotp u u + 2 * b * dotp u v + b ^ 2 * dotp v v := by
  simp only [dotp, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

lemma exists_smul_of_crsp_eq_zero {u v : P2} (h : crsp u v = 0) (hu : u ≠ 0) :
    ∃ μ : ℝ, v = μ • u := by
  have hu2 : 0 < dotp u u := dotp_self_pos hu
  refine ⟨dotp u v / dotp u u, ?_⟩
  have h1 : dotp u (v - (dotp u v / dotp u u) • u) = 0 := by
    rw [dotp_sub_right, dotp_smul_right, div_mul_cancel₀ _ hu2.ne', sub_self]
  have h2 : crsp u (v - (dotp u v / dotp u u) • u) = 0 := by
    rw [crsp_sub_right, crsp_smul_right, h, crsp_self, mul_zero, sub_zero]
  have h3 := lagrange u (v - (dotp u v / dotp u u) • u)
  rw [h1, h2] at h3
  have h4 : dotp (v - (dotp u v / dotp u u) • u) (v - (dotp u v / dotp u u) • u) = 0 := by
    nlinarith [hu2]
  have h5 := dotp_self_eq_zero h4
  rwa [sub_eq_zero] at h5

/-- If `PX = PY = d` (with `d` maximal) and `XY ≤ d` with `X ≠ Y`, then
`X - P` and `Y - P` are not parallel. -/
lemma crsp_ne_zero_of_dist {P X Y : P2} {d : ℝ} (hd : 0 < d)
    (hPX : dist P X = d) (hPY : dist P Y = d) (hdXY : dist X Y ≤ d) (hXY : X ≠ Y) :
    crsp (X - P) (Y - P) ≠ 0 := by
  intro hcon
  have hd2 : 0 < d ^ 2 := pow_pos hd 2
  have hx : dotp (X - P) (X - P) = d ^ 2 := by rw [dotp_self_sub, ← dist_sq, hPX]
  have hy : dotp (Y - P) (Y - P) = d ^ 2 := by rw [dotp_self_sub, ← dist_sq, hPY]
  have hu : X - P ≠ 0 := by
    intro h2
    rw [h2, dotp_zero_left] at hx
    linarith [hd2]
  obtain ⟨μ, hμ⟩ := exists_smul_of_crsp_eq_zero hcon hu
  have hμ2 : μ ^ 2 = 1 := by
    have h1 : dotp (Y - P) (Y - P) = μ ^ 2 * dotp (X - P) (X - P) := by
      rw [hμ, dotp_smul_left, dotp_smul_right]
      ring
    rw [hy, hx] at h1
    have h2 : (μ ^ 2 - 1) * d ^ 2 = 0 := by linear_combination h1.symm
    rcases mul_eq_zero.mp h2 with h3 | h3
    · linear_combination h3
    · exact absurd h3 hd2.ne'
  rcases sq_eq_one_iff.mp hμ2 with hμ1 | hμ1
  · rw [hμ1, one_smul] at hμ
    apply hXY
    have h3 : Y - P + P = X - P + P := congrArg (· + P) hμ
    rw [sub_add_cancel, sub_add_cancel] at h3
    exact h3.symm
  · rw [hμ1, neg_smul, one_smul] at hμ
    have e : X - Y = (X - P) + (X - P) := by
      have eXY : X - Y = (X - P) - (Y - P) := by abel
      rw [eXY, hμ]
      abel
    have h1 : dist X Y ^ 2 = 4 * d ^ 2 := by
      rw [dist_sq, e, dotp_add_add, hx]
      ring
    have h2 := dist_le_sq hdXY
    nlinarith [h1, h2, hd2]

/-- Auxiliary for Lemma A: if the two supporting lines meet beyond the segment
`AB` but on the segment `CD`, then some cross-distance exceeds `d`. -/
lemma lemmaA_beyond {A B C D : P2} {d : ℝ} (hd : 0 < d)
    (hAB : dist A B = d) (hCD : dist C D = d)
    (hAC : dist A C ≤ d) (hAD : dist A D ≤ d) (hBC : dist B C ≤ d) (hBD : dist B D ≤ d)
    {s₀ t₀ : ℝ} (hY : A + s₀ • (B - A) = C + t₀ • (D - C))
    (hs : 1 < s₀) (ht0 : 0 ≤ t₀) (ht1 : t₀ ≤ 1) : False := by
  have hs0 : 0 < s₀ := lt_trans zero_lt_one hs
  have hAY : dist A (A + s₀ • (B - A)) = s₀ * d := by
    have e1 : A - (A + s₀ • (B - A)) = -(s₀ • (B - A)) := by abel
    have hb : ‖B - A‖ = d := by rw [← dist_eq_norm, dist_comm B A, hAB]
    rw [dist_eq_norm, e1, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0.le, hb]
  have hle : dist A (C + t₀ • (D - C)) ^ 2 ≤ d ^ 2 := by
    have e1 : dist A (C + t₀ • (D - C)) ^ 2 =
        dotp (C - A) (C - A) + 2 * t₀ * dotp (C - A) (D - C) +
          t₀ ^ 2 * dotp (D - C) (D - C) := by
      have e2 : (C + t₀ • (D - C)) - A = (C - A) + t₀ • (D - C) := by abel
      rw [dist_sq, dotp_self_sub A (C + t₀ • (D - C)), e2, dotp_add_smul]
    have key : dist A (C + t₀ • (D - C)) ^ 2 ≤
        (1 - t₀) * dist A C ^ 2 + t₀ * dist A D ^ 2 := by
      have eAC : dist A C ^ 2 = dotp (C - A) (C - A) := by rw [dist_sq, dotp_self_sub]
      have eAD : dist A D ^ 2 = dotp (C - A) (C - A) + 2 * dotp (C - A) (D - C) +
          dotp (D - C) (D - C) := by
        have e3 : D - A = (C - A) + (D - C) := by abel
        rw [dist_sq, dotp_self_sub A D, e3, dotp_add_add]
      have hnn : 0 ≤ dotp (D - C) (D - C) := dotp_self_nonneg _
      rw [e1, eAC, eAD]
      nlinarith [mul_nonneg hnn (by nlinarith : 0 ≤ t₀ * (1 - t₀))]
    have hAC2 : dist A C ^ 2 ≤ d ^ 2 := dist_le_sq hAC
    have hAD2 : dist A D ^ 2 ≤ d ^ 2 := dist_le_sq hAD
    nlinarith [key, hAC2, hAD2, ht0, ht1]
  have hlt : d ^ 2 < (s₀ * d) ^ 2 :=
    sq_lt_sq_of_nonneg hd.le (by nlinarith [mul_lt_mul_of_pos_right hs hd])
  rw [← hAY] at hlt
  rw [← hY] at hle
  linarith [hlt, hle]

/-- Auxiliary for Lemma A: if the two supporting lines meet beyond both
segments, then some cross-distance exceeds `d`. -/
lemma lemmaA_far {A B C D : P2} {d : ℝ} (hd : 0 < d)
    (hAB : dist A B = d) (hCD : dist C D = d)
    (hAC : dist A C ≤ d) (hAD : dist A D ≤ d) (hBC : dist B C ≤ d) (hBD : dist B D ≤ d)
    {s₀ t₀ : ℝ} (hY : A + s₀ • (B - A) = C + t₀ • (D - C))
    (hc : crsp (B - A) (D - C) ≠ 0)
    (hs : 1 < s₀) (ht : 1 < t₀) : False := by
  have hd2 : 0 < d ^ 2 := pow_pos hd 2
  have hy : 0 < s₀ - 1 := sub_pos.mpr hs
  have ha : dotp (B - A) (B - A) = d ^ 2 := by rw [dotp_self_sub, ← dist_sq, hAB]
  have hb : dotp (D - C) (D - C) = d ^ 2 := by rw [dotp_self_sub, ← dist_sq, hCD]
  have hp2 : dotp (B - A) (D - C) ^ 2 < (d ^ 2) ^ 2 := by
    have h1 := lagrange (B - A) (D - C)
    rw [ha, hb] at h1
    have h2 : 0 < crsp (B - A) (D - C) ^ 2 := sq_pos_of_ne_zero hc
    nlinarith [h1, h2]
  have hplt : dotp (B - A) (D - C) < d ^ 2 := by
    by_contra hcon
    push_neg at hcon
    have h3 : (d ^ 2) ^ 2 ≤ dotp (B - A) (D - C) ^ 2 := sq_le_sq_of_nonneg hd2.le hcon
    linarith [hp2, h3]
  have hw : C - A = s₀ • (B - A) - t₀ • (D - C) := by
    have e : C = A + s₀ • (B - A) - t₀ • (D - C) := by
      have e2 : C = (C + t₀ • (D - C)) - t₀ • (D - C) := by abel
      rwa [← hY] at e2
    conv_lhs => rw [e]
    abel
  have eBC : B - C = (1 - s₀) • (B - A) + t₀ • (D - C) := by
    have e : B - C = (B - A) - (C - A) := by abel
    rw [e, hw, sub_smul, one_smul]
    abel
  have eBD : B - D = (1 - s₀) • (B - A) + (t₀ - 1) • (D - C) := by
    have e : B - D = (B - A) - (C - A) - (D - C) := by abel
    rw [e, hw, sub_smul, one_smul, sub_smul, one_smul]
    abel
  have eAC : A - C = (-s₀) • (B - A) + t₀ • (D - C) := by
    have e : A - C = -(C - A) := by abel
    rw [e, hw, neg_sub, neg_smul]
    abel
  have eAD : A - D = (-s₀) • (B - A) + (t₀ - 1) • (D - C) := by
    have e : A - D = -(C - A) - (D - C) := by abel
    rw [e, hw, neg_sub, neg_smul, sub_smul, one_smul]
    abel
  have h1 : (s₀ - 1) ^ 2 * d ^ 2 + t₀ ^ 2 * d ^ 2 -
      2 * (s₀ - 1) * t₀ * dotp (B - A) (D - C) ≤ d ^ 2 := by
    have h := dist_le_sq hBC
    rw [dist_sq, eBC, dotp_smul2, ha, hb] at h
    convert h using 1 <;> ring
  have h2 : (s₀ - 1) ^ 2 * d ^ 2 + (t₀ - 1) ^ 2 * d ^ 2 -
      2 * (s₀ - 1) * (t₀ - 1) * dotp (B - A) (D - C) ≤ d ^ 2 := by
    have h := dist_le_sq hBD
    rw [dist_sq, eBD, dotp_smul2, ha, hb] at h
    convert h using 1 <;> ring
  have h3 : s₀ ^ 2 * d ^ 2 + t₀ ^ 2 * d ^ 2 -
      2 * s₀ * t₀ * dotp (B - A) (D - C) ≤ d ^ 2 := by
    have h := dist_le_sq hAC
    rw [dist_sq, eAC, dotp_smul2, ha, hb] at h
    convert h using 1 <;> ring
  have h4 : s₀ ^ 2 * d ^ 2 + (t₀ - 1) ^ 2 * d ^ 2 -
      2 * s₀ * (t₀ - 1) * dotp (B - A) (D - C) ≤ d ^ 2 := by
    have h := dist_le_sq hAD
    rw [dist_sq, eAD, dotp_smul2, ha, hb] at h
    convert h using 1 <;> ring
  have hyt : 0 < (s₀ - 1) * t₀ := mul_pos hy (lt_trans zero_lt_one ht)
  have hyt2 : 0 < s₀ * (t₀ - 1) := mul_pos (lt_trans zero_lt_one hs) (sub_pos.mpr ht)
  have key1 : (s₀ - 1 - t₀) ^ 2 < 1 := by
    have k1 : d ^ 2 * ((s₀ - 1 - t₀) ^ 2 - 1) < 0 := by
      nlinarith [h1, mul_pos hyt (sub_pos.mpr hplt), hd2]
    by_contra hcon
    push_neg at hcon
    have k2 : 0 ≤ d ^ 2 * ((s₀ - 1 - t₀) ^ 2 - 1) :=
      mul_nonneg hd2.le (sub_nonneg.mpr hcon)
    linarith [k1, k2]
  have key2 : (s₀ - t₀ + 1) ^ 2 < 1 := by
    have k1 : d ^ 2 * ((s₀ - t₀ + 1) ^ 2 - 1) < 0 := by
      nlinarith [h4, mul_pos hyt2 (sub_pos.mpr hplt), hd2]
    by_contra hcon
    push_neg at hcon
    have k2 : 0 ≤ d ^ 2 * ((s₀ - t₀ + 1) ^ 2 - 1) :=
      mul_nonneg hd2.le (sub_nonneg.mpr hcon)
    linarith [k1, k2]
  nlinarith [sq_nonneg (s₀ - t₀), key1, key2]

/-- **Lemma A (parallel case)**. -/
lemma lemmaA_parallel {A B C D : P2} {d : ℝ} (hd : 0 < d)
    (hAB : dist A B = d) (hCD : dist C D = d)
    (hAC : dist A C ≤ d) (hAD : dist A D ≤ d)
    (hBC : dist B C ≤ d) (hBD : dist B D ≤ d)
    (hAC' : A ≠ C) (hAD' : A ≠ D) (hBC' : B ≠ C) (hBD' : B ≠ D)
    (hpar : crsp (B - A) (D - C) = 0) :
    ∃ S : P2, S ∈ segment ℝ A B ∧ S ∈ segment ℝ C D := by
  have hd2 : 0 < d ^ 2 := pow_pos hd 2
  have ha : dotp (B - A) (B - A) = d ^ 2 := by rw [dotp_self_sub, ← dist_sq, hAB]
  have hu : B - A ≠ 0 := by
    intro hcon
    rw [hcon, dotp_zero_left] at ha
    linarith [hd2]
  · -- The parallel case.
    obtain ⟨μ, hμ⟩ := exists_smul_of_crsp_eq_zero hpar hu
    have hb : dotp (D - C) (D - C) = d ^ 2 := by rw [dotp_self_sub, ← dist_sq, hCD]
    rw [hμ, dotp_smul_left, dotp_smul_right, ha] at hb
    have hμ2 : μ ^ 2 = 1 := by
      have h1 : (μ ^ 2 - 1) * d ^ 2 = 0 := by linear_combination hb
      rcases mul_eq_zero.mp h1 with h2 | h2
      · linear_combination h2
      · exact absurd h2 hd2.ne'
    rcases sq_eq_one_iff.mp hμ2 with hμ1 | hμ1
    · -- `D - C = B - A`: then `C = A`, contradiction.
      have hv : D - C = B - A := by rw [hμ, hμ1, one_smul]
      have hAC2 : dotp (C - A) (C - A) ≤ d ^ 2 := by
        have h := dist_le_sq hAC
        rwa [dist_sq, dotp_self_sub] at h
      have hBC2 : dotp (B - A) (B - A) - 2 * dotp (B - A) (C - A) +
          dotp (C - A) (C - A) ≤ d ^ 2 := by
        have h := dist_le_sq hBC
        have e : B - C = (B - A) - (C - A) := by abel
        rwa [dist_sq, e, dotp_sub_sub] at h
      have hAD2 : dotp (C - A) (C - A) + 2 * dotp (B - A) (C - A) +
          dotp (B - A) (B - A) ≤ d ^ 2 := by
        have h := dist_le_sq hAD
        have e : D - A = (C - A) + (B - A) := by rw [← hv]; abel
        rwa [dist_sq, dotp_self_sub A D, e, dotp_add_add, dotp_comm (C - A) (B - A)] at h
      have hq : dotp (C - A) (C - A) ≤ 0 := by nlinarith [hBC2, hAD2, ha]
      have hC0 : C - A = 0 := dotp_self_eq_zero (le_antisymm hq (dotp_self_nonneg _))
      rw [sub_eq_zero] at hC0
      exact (hAC' hC0.symm).elim
    · -- `D - C = -(B - A)`: then `C = B`, contradiction.
      have hv : D - C = -(B - A) := by rw [hμ, hμ1, neg_smul, one_smul]
      have hAC2 : dotp (C - A) (C - A) ≤ d ^ 2 := by
        have h := dist_le_sq hAC
        rwa [dist_sq, dotp_self_sub] at h
      have hBD2 : dotp (B - D) (B - D) ≤ d ^ 2 := by
        have h := dist_le_sq hBD
        rwa [dist_sq] at h
      have e3 : B - D = (B - A) + (B - A) - (C - A) := by
        have e : D - A = (C - A) - (B - A) := by
          rw [show D - A = (C - A) + (D - C) by abel, hv]
          abel
        rw [show B - D = (B - A) - (D - A) by abel, e]
        abel
      rw [e3, dotp_sub_sub] at hBD2
      have e4 : dotp ((B - A) + (B - A)) ((B - A) + (B - A)) = 4 * d ^ 2 := by
        rw [dotp_add_add, ha]
        ring
      rw [e4] at hBD2
      have e5 : dotp ((B - A) + (B - A)) (C - A) = 2 * dotp (B - A) (C - A) := by
        rw [dotp_add_left]
        ring
      rw [e5] at hBD2
      have hcs : dotp (B - A) (C - A) ^ 2 ≤ d ^ 2 * dotp (C - A) (C - A) := by
        have h1 := lagrange (B - A) (C - A)
        rw [ha] at h1
        nlinarith [sq_nonneg (crsp (B - A) (C - A))]
      have hqge : d ^ 2 ≤ dotp (C - A) (C - A) := by
        have g1 : dotp (C - A) (C - A) + 3 * d ^ 2 ≤ 4 * dotp (B - A) (C - A) := by
          nlinarith [hBD2]
        have g2 : 0 ≤ dotp (C - A) (C - A) + 3 * d ^ 2 := by
          nlinarith [dotp_self_nonneg (C - A), hd2]
        have g3 : (dotp (C - A) (C - A) + 3 * d ^ 2) ^ 2 ≤ (4 * dotp (B - A) (C - A)) ^ 2 :=
          sq_le_sq_of_nonneg g2 g1
        by_contra hcon
        push_neg at hcon
        have g4 : dotp (C - A) (C - A) ^ 2 + 6 * dotp (C - A) (C - A) * d ^ 2 +
            9 * (d ^ 2) ^ 2 ≤ 16 * dotp (B - A) (C - A) ^ 2 := by nlinarith [g3]
        have g5 : 16 * dotp (B - A) (C - A) ^ 2 ≤
            16 * d ^ 2 * dotp (C - A) (C - A) := by nlinarith [hcs]
        have g6 : 0 < (d ^ 2 - dotp (C - A) (C - A)) *
            (9 * d ^ 2 - dotp (C - A) (C - A)) := by
          apply mul_pos (sub_pos.mpr hcon)
          nlinarith [hcon, hd2]
        nlinarith [g4, g5, g6]
      have hq : dotp (C - A) (C - A) = d ^ 2 := le_antisymm hAC2 hqge
      have hp'ge : d ^ 2 ≤ dotp (B - A) (C - A) := by nlinarith [hBD2, hq]
      have hp'le : dotp (B - A) (C - A) ≤ d ^ 2 := by
        by_contra hcon
        push_neg at hcon
        have h1 : (d ^ 2) ^ 2 < dotp (B - A) (C - A) ^ 2 := sq_lt_sq_of_nonneg hd2.le hcon
        nlinarith [hcs, hq, h1]
      have hp' : dotp (B - A) (C - A) = d ^ 2 := le_antisymm hp'le hp'ge
      have hCB : C - B = 0 := by
        have h1 : dotp (C - B) (C - B) = 0 := by
          have e : C - B = (C - A) - (B - A) := by abel
          rw [e, dotp_sub_sub, dotp_comm (C - A) (B - A), hq, hp', ha]
          ring
        exact dotp_self_eq_zero h1
      rw [sub_eq_zero] at hCB
      exact (hBC' hCB.symm).elim
/-- **Lemma A (generic case)**: the two supporting lines meet at a unique point. -/
lemma lemmaA_nonparallel {A B C D : P2} {d : ℝ} (hd : 0 < d)
    (hAB : dist A B = d) (hCD : dist C D = d)
    (hAC : dist A C ≤ d) (hAD : dist A D ≤ d)
    (hBC : dist B C ≤ d) (hBD : dist B D ≤ d)
    (hAC' : A ≠ C) (hAD' : A ≠ D) (hBC' : B ≠ C) (hBD' : B ≠ D)
    (hpar : crsp (B - A) (D - C) ≠ 0) :
    ∃ S : P2, S ∈ segment ℝ A B ∧ S ∈ segment ℝ C D := by
  · -- The generic case: the two supporting lines meet at a unique point.
    obtain ⟨cu, hcu⟩ := show ∃ x, x = crsp (B - A) (D - C) from ⟨_, rfl⟩
    obtain ⟨s₀, hs₀⟩ := show ∃ x, x = crsp (C - A) (D - C) / cu from ⟨_, rfl⟩
    obtain ⟨t₀, hs₁⟩ := show ∃ x, x = crsp (C - A) (B - A) / cu from ⟨_, rfl⟩
    have hpar' : cu ≠ 0 := hcu ▸ hpar
    have hw : C - A = s₀ • (B - A) - t₀ • (D - C) := by
      have h := cramer (B - A) (D - C) (C - A)
      rw [← hcu] at h
      have e : cu • (C - A) = cu • (s₀ • (B - A) - t₀ • (D - C)) := by
        rw [h]
        conv_rhs => rw [smul_sub, smul_smul, smul_smul, mul_comm cu s₀, mul_comm cu t₀,
          hs₀, div_mul_cancel₀ _ hpar', hs₁, div_mul_cancel₀ _ hpar']
      have h2 := congrArg (fun V => cu⁻¹ • V) e
      simp only [smul_smul, inv_mul_cancel₀ hpar', one_smul] at h2
      exact h2
    have hY : A + s₀ • (B - A) = C + t₀ • (D - C) := by
      have e1 : s₀ • (B - A) = (C - A) + t₀ • (D - C) := by rw [hw]; abel
      calc A + s₀ • (B - A) = A + ((C - A) + t₀ • (D - C)) := by rw [e1]
        _ = C + t₀ • (D - C) := by rw [← add_assoc, add_sub_cancel]
    rcases le_or_gt 0 s₀ with hs0 | hs0
    · rcases le_or_gt s₀ 1 with hs1 | hs1
      · rcases le_or_gt 0 t₀ with ht0 | ht0
        · rcases le_or_gt t₀ 1 with ht1 | ht1
          · -- The lines meet inside both segments: the intersection point.
            refine ⟨A + s₀ • (B - A), ?_, ?_⟩
            · rw [segment_eq_image']
              exact ⟨s₀, ⟨hs0, hs1⟩, rfl⟩
            · rw [segment_eq_image']
              exact ⟨t₀, ⟨ht0, ht1⟩, hY.symm⟩
          · -- `t₀ > 1`: swap the two segments.
            exact (lemmaA_beyond (s₀ := t₀) (t₀ := s₀) hd hCD hAB
              (by rwa [dist_comm] : dist C A ≤ d) (by rwa [dist_comm] : dist C B ≤ d)
              (by rwa [dist_comm] : dist D A ≤ d) (by rwa [dist_comm] : dist D B ≤ d)
              hY.symm ht1 hs0 hs1).elim
        · -- `t₀ < 0`: swap both segments and swap `C`, `D`.
          have hY' : D + (1 - t₀) • (C - D) = A + s₀ • (B - A) := by
            rw [hY, sub_smul, one_smul, show C - D = -(D - C) by abel, smul_neg]
            abel
          exact (lemmaA_beyond (s₀ := 1 - t₀) (t₀ := s₀) hd
            (by rwa [dist_comm] : dist D C = d) hAB
            (by rwa [dist_comm] : dist D A ≤ d) (by rwa [dist_comm] : dist D B ≤ d)
            (by rwa [dist_comm] : dist C A ≤ d) (by rwa [dist_comm] : dist C B ≤ d)
            hY' (by linarith only [ht0]) hs0 hs1).elim
      · rcases le_or_gt 0 t₀ with ht0 | ht0
        · rcases le_or_gt t₀ 1 with ht1 | ht1
          · exact (lemmaA_beyond (s₀ := s₀) (t₀ := t₀) hd hAB hCD hAC hAD hBC hBD hY hs1
              ht0 ht1).elim
          · exact (lemmaA_far (s₀ := s₀) (t₀ := t₀) hd hAB hCD hAC hAD hBC hBD hY hpar hs1
              ht1).elim
        · have hY' : A + s₀ • (B - A) = D + (1 - t₀) • (C - D) := by
            rw [hY, sub_smul, one_smul, show C - D = -(D - C) by abel, smul_neg]
            abel
          exact (lemmaA_far (s₀ := s₀) (t₀ := 1 - t₀) hd hAB
            (by rwa [dist_comm] : dist D C = d) hAD hAC hBD hBC hY'
            (by rw [show C - D = -(D - C) by abel, crsp_neg_right];
                exact neg_ne_zero.mpr hpar) hs1 (by linarith only [ht0])).elim
    · -- `s₀ < 0`: swap `A`, `B`.
      have hY' : B + (1 - s₀) • (A - B) = C + t₀ • (D - C) := by
        rw [← hY, sub_smul, one_smul, show A - B = -(B - A) by abel, smul_neg]
        abel
      have hc' : crsp (A - B) (D - C) ≠ 0 := by
        rw [show A - B = -(B - A) by abel, crsp_neg_left]
        exact neg_ne_zero.mpr hpar
      rcases le_or_gt 0 t₀ with ht0 | ht0
      · rcases le_or_gt t₀ 1 with ht1 | ht1
        · exact (lemmaA_beyond (s₀ := 1 - s₀) (t₀ := t₀) hd
            (by rwa [dist_comm] : dist B A = d) hCD hBC hBD hAC hAD
            hY' (by linarith only [hs0]) ht0 ht1).elim
        · exact (lemmaA_far (s₀ := 1 - s₀) (t₀ := t₀) hd
            (by rwa [dist_comm] : dist B A = d) hCD hBC hBD hAC hAD
            hY' hc' (by linarith only [hs0]) ht1).elim
      · have hY'' : B + (1 - s₀) • (A - B) = D + (1 - t₀) • (C - D) := by
          rw [hY', sub_smul, one_smul, show C - D = -(D - C) by abel, smul_neg]
          abel
        exact (lemmaA_far (s₀ := 1 - s₀) (t₀ := 1 - t₀) hd
          (by rwa [dist_comm] : dist B A = d)
          (by rwa [dist_comm] : dist D C = d) hBD hBC hAD hAC hY''
          (by rw [show A - B = -(B - A) by abel,
              show C - D = -(D - C) by abel, crsp_neg_left, crsp_neg_right, neg_neg];
              exact hpar) (by linarith only [hs0]) (by linarith only [ht0])).elim

/-- **Lemma A**: two diameters (segments of maximal length `d`) with no common
endpoint must intersect. -/
lemma lemmaA {A B C D : P2} {d : ℝ} (hd : 0 < d)
    (hAB : dist A B = d) (hCD : dist C D = d)
    (hAC : dist A C ≤ d) (hAD : dist A D ≤ d)
    (hBC : dist B C ≤ d) (hBD : dist B D ≤ d)
    (hAC' : A ≠ C) (hAD' : A ≠ D) (hBC' : B ≠ C) (hBD' : B ≠ D) :
    ∃ S : P2, S ∈ segment ℝ A B ∧ S ∈ segment ℝ C D := by
  by_cases hpar : crsp (B - A) (D - C) = 0
  · exact lemmaA_parallel hd hAB hCD hAC hAD hBC hBD hAC' hAD' hBC' hBD' hpar
  · exact lemmaA_nonparallel hd hAB hCD hAC hAD hBC hBD hAC' hAD' hBC' hBD' hpar

/-- **Lemma B (middle configuration)**: if `Y` is the angular middle of three
diameter-neighbors of `P`, then `Y - P` is a positive combination of the other
two, and the two chords at `Y` are strictly shorter than `d`. -/
lemma lemmaB_middle {P X Y Z : P2} {d : ℝ} (hd : 0 < d)
    (hXY : X ≠ Y) (hYZ : Y ≠ Z) (hXZ : X ≠ Z)
    (hPX : dist P X = d) (hPY : dist P Y = d) (hPZ : dist P Z = d)
    (hdXY : dist X Y ≤ d) (hdYZ : dist Y Z ≤ d) (hdXZ : dist X Z ≤ d)
    (hmid : crsp (Y - P) (X - P) * crsp (Y - P) (Z - P) < 0) :
    ∃ α β : ℝ, 0 < α ∧ 0 < β ∧ Y - P = α • (X - P) + β • (Z - P) ∧
      dist Y X < d ∧ dist Y Z < d := by
  have hd2 : 0 < d ^ 2 := pow_pos hd 2
  have hx : dotp (X - P) (X - P) = d ^ 2 := by rw [dotp_self_sub, ← dist_sq, hPX]
  have hy : dotp (Y - P) (Y - P) = d ^ 2 := by rw [dotp_self_sub, ← dist_sq, hPY]
  have hz : dotp (Z - P) (Z - P) = d ^ 2 := by rw [dotp_self_sub, ← dist_sq, hPZ]
  have hp : d ^ 2 / 2 ≤ dotp (X - P) (Y - P) := by
    have h := dist_le_sq hdXY
    have e : X - Y = (X - P) - (Y - P) := by abel
    rw [dist_sq, e, dotp_sub_sub, hx, hy] at h
    nlinarith only [h]
  have hq : d ^ 2 / 2 ≤ dotp (Y - P) (Z - P) := by
    have h := dist_le_sq hdYZ
    have e : Y - Z = (Y - P) - (Z - P) := by abel
    rw [dist_sq, e, dotp_sub_sub, hy, hz] at h
    nlinarith only [h]
  have hr : d ^ 2 / 2 ≤ dotp (X - P) (Z - P) := by
    have h := dist_le_sq hdXZ
    have e : X - Z = (X - P) - (Z - P) := by abel
    rw [dist_sq, e, dotp_sub_sub, hx, hz] at h
    nlinarith only [h]
  have hcxy : crsp (X - P) (Y - P) ≠ 0 := crsp_ne_zero_of_dist hd hPX hPY hdXY hXY
  have hcyz : crsp (Y - P) (Z - P) ≠ 0 := crsp_ne_zero_of_dist hd hPY hPZ hdYZ hYZ
  have hcxz : crsp (X - P) (Z - P) ≠ 0 := crsp_ne_zero_of_dist hd hPX hPZ hdXZ hXZ
  have hplt : dotp (X - P) (Y - P) < d ^ 2 := by
    have h1 := lagrange (X - P) (Y - P)
    rw [hx, hy] at h1
    have h2 : 0 < crsp (X - P) (Y - P) ^ 2 := sq_pos_of_ne_zero hcxy
    have h3 : dotp (X - P) (Y - P) ^ 2 < (d ^ 2) ^ 2 := by nlinarith only [h1, h2]
    by_contra hcon
    push_neg at hcon
    have h4 : (d ^ 2) ^ 2 ≤ dotp (X - P) (Y - P) ^ 2 := sq_le_sq_of_nonneg hd2.le hcon
    linarith only [h3, h4]
  have hqlt : dotp (Y - P) (Z - P) < d ^ 2 := by
    have h1 := lagrange (Y - P) (Z - P)
    rw [hy, hz] at h1
    have h2 : 0 < crsp (Y - P) (Z - P) ^ 2 := sq_pos_of_ne_zero hcyz
    have h3 : dotp (Y - P) (Z - P) ^ 2 < (d ^ 2) ^ 2 := by nlinarith only [h1, h2]
    by_contra hcon
    push_neg at hcon
    have h4 : (d ^ 2) ^ 2 ≤ dotp (Y - P) (Z - P) ^ 2 := sq_le_sq_of_nonneg hd2.le hcon
    linarith only [h3, h4]
  have hmid' : d ^ 2 * dotp (X - P) (Z - P) <
      dotp (X - P) (Y - P) * dotp (Y - P) (Z - P) := by
    have h1 := lagrange2 (Y - P) (X - P) (Y - P) (Z - P)
    rw [hy] at h1
    nlinarith only [hmid, h1]
  have hsign1 : 0 < crsp (Y - P) (Z - P) * crsp (X - P) (Z - P) := by
    have h1 := lagrange2 (Y - P) (Z - P) (X - P) (Z - P)
    rw [hz, dotp_comm (Z - P) (X - P), dotp_comm (Y - P) (X - P)] at h1
    rw [h1]
    have g1 : 0 < dotp (Y - P) (Z - P) *
        (dotp (X - P) (Y - P) * dotp (Y - P) (Z - P) - d ^ 2 * dotp (X - P) (Z - P)) :=
      mul_pos (by nlinarith only [hq, hd2]) (sub_pos.mpr hmid')
    have g2 : 0 < dotp (X - P) (Y - P) * ((d ^ 2) ^ 2 - dotp (Y - P) (Z - P) ^ 2) := by
      apply mul_pos (by nlinarith only [hp, hd2])
      have h2 := lagrange (Y - P) (Z - P)
      rw [hy, hz] at h2
      have h3 : 0 < crsp (Y - P) (Z - P) ^ 2 := sq_pos_of_ne_zero hcyz
      nlinarith only [h2, h3]
    have g3 : 0 < d ^ 2 * (dotp (X - P) (Y - P) * d ^ 2 -
        dotp (Y - P) (Z - P) * dotp (X - P) (Z - P)) := by nlinarith only [g1, g2]
    by_contra hcon
    push_neg at hcon
    have h4 : d ^ 2 * (dotp (X - P) (Y - P) * d ^ 2 -
        dotp (Y - P) (Z - P) * dotp (X - P) (Z - P)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hd2.le hcon
    linarith only [g3, h4]
  have hsign2 : 0 < crsp (X - P) (Y - P) * crsp (X - P) (Z - P) := by
    have h1 := lagrange2 (X - P) (Y - P) (X - P) (Z - P)
    rw [hx, dotp_comm (Y - P) (X - P)] at h1
    rw [h1]
    have g1 : 0 < dotp (X - P) (Y - P) *
        (dotp (X - P) (Y - P) * dotp (Y - P) (Z - P) - d ^ 2 * dotp (X - P) (Z - P)) :=
      mul_pos (by nlinarith only [hp, hd2]) (sub_pos.mpr hmid')
    have g2 : 0 < dotp (Y - P) (Z - P) * ((d ^ 2) ^ 2 - dotp (X - P) (Y - P) ^ 2) := by
      apply mul_pos (by nlinarith only [hq, hd2])
      have h2 := lagrange (X - P) (Y - P)
      rw [hx, hy] at h2
      have h3 : 0 < crsp (X - P) (Y - P) ^ 2 := sq_pos_of_ne_zero hcxy
      nlinarith only [h2, h3]
    have g3 : 0 < d ^ 2 * (d ^ 2 * dotp (Y - P) (Z - P) -
        dotp (X - P) (Z - P) * dotp (X - P) (Y - P)) := by nlinarith only [g1, g2]
    by_contra hcon
    push_neg at hcon
    have h4 : d ^ 2 * (d ^ 2 * dotp (Y - P) (Z - P) -
        dotp (X - P) (Z - P) * dotp (X - P) (Y - P)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hd2.le hcon
    linarith only [g3, h4]
  obtain ⟨α, hαdef⟩ := show ∃ x, x = crsp (Y - P) (Z - P) / crsp (X - P) (Z - P) from ⟨_, rfl⟩
  obtain ⟨β, hβdef⟩ := show ∃ x, x = crsp (X - P) (Y - P) / crsp (X - P) (Z - P) from ⟨_, rfl⟩
  have hαpos : 0 < α := by
    rw [hαdef]
    rcases mul_pos_iff.mp hsign1 with h | h
    · exact div_pos h.1 h.2
    · exact div_pos_of_neg_of_neg h.1 h.2
  have hβpos : 0 < β := by
    rw [hβdef]
    rcases mul_pos_iff.mp hsign2 with h | h
    · exact div_pos h.1 h.2
    · exact div_pos_of_neg_of_neg h.1 h.2
  have hyeq : Y - P = α • (X - P) + β • (Z - P) := by
    have h := cramer (X - P) (Z - P) (Y - P)
    have e : crsp (X - P) (Z - P) • (Y - P) =
        crsp (X - P) (Z - P) • (α • (X - P) + β • (Z - P)) := by
      rw [h]
      conv_rhs => rw [smul_add, smul_smul, smul_smul, hαdef, hβdef,
        mul_comm (crsp (X - P) (Z - P)) _, div_mul_cancel₀ _ hcxz,
        mul_comm (crsp (X - P) (Z - P)) _, div_mul_cancel₀ _ hcxz,
        crsp_skew (X - P) (Y - P), neg_smul, ← sub_eq_add_neg]
    have h2 := congrArg (fun V => (crsp (X - P) (Z - P))⁻¹ • V) e
    simp only [smul_smul, inv_mul_cancel₀ hcxz, one_smul] at h2
    exact h2
  have hpgt : d ^ 2 / 2 < dotp (X - P) (Y - P) := by
    rcases eq_or_lt_of_le hp with hcon | hcon
    · exfalso
      have hqle : dotp (Y - P) (Z - P) ≤ d ^ 2 := le_of_lt hqlt
      nlinarith only [hmid', hcon, hqle, hr, hd2]
    · exact hcon
  have hqgt : d ^ 2 / 2 < dotp (Y - P) (Z - P) := by
    rcases eq_or_lt_of_le hq with hcon | hcon
    · exfalso
      have hple : dotp (X - P) (Y - P) ≤ d ^ 2 := le_of_lt hplt
      nlinarith only [hmid', hcon, hple, hr, hd2]
    · exact hcon
  have hYXlt : dist Y X < d := by
    have h1 : dist Y X ^ 2 < d ^ 2 := by
      rw [dist_sq, dotp_self_sub Y X, show X - Y = (X - P) - (Y - P) by abel,
        dotp_sub_sub, hx, hy]
      nlinarith only [hpgt, hd2]
    by_contra hcon
    push_neg at hcon
    have h2 : d ^ 2 ≤ dist Y X ^ 2 := sq_le_sq_of_nonneg hd.le hcon
    linarith only [h1, h2]
  have hYZlt : dist Y Z < d := by
    have h1 : dist Y Z ^ 2 < d ^ 2 := by
      rw [dist_sq, show Y - Z = (Y - P) - (Z - P) by abel, dotp_sub_sub, hy, hz]
      nlinarith only [hqgt, hd2]
    by_contra hcon
    push_neg at hcon
    have h2 : d ^ 2 ≤ dist Y Z ^ 2 := sq_le_sq_of_nonneg hd.le hcon
    linarith only [h1, h2]
  exact ⟨α, β, hαpos, hβpos, hyeq, hYXlt, hYZlt⟩

/-- **Lemma B (core)**: in the middle configuration, a second diameter-neighbor
`T` of `Y` leads to a contradiction. -/
lemma lemmaB_core {P X Y Z : P2} {d : ℝ} (hd : 0 < d)
    (hXY : X ≠ Y) (hYZ : Y ≠ Z) (hXZ : X ≠ Z)
    (hPX : dist P X = d) (hPY : dist P Y = d) (hPZ : dist P Z = d)
    (hdXY : dist X Y ≤ d) (hdYZ : dist Y Z ≤ d) (hdXZ : dist X Z ≤ d)
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hyeq : Y - P = α • (X - P) + β • (Z - P))
    (hYXlt : dist Y X < d) (hYZlt : dist Y Z < d)
    {T : P2} (hT : T ≠ P) (hTP : dist T P ≤ d) (hTX : dist T X ≤ d)
    (hTY : dist T Y ≤ d) (hTZ : dist T Z ≤ d)
    (hTYeq : dist Y T = d) : False := by
  have hd2 : 0 < d ^ 2 := pow_pos hd 2
  have hx : dotp (X - P) (X - P) = d ^ 2 := by rw [dotp_self_sub, ← dist_sq, hPX]
  have hy : dotp (Y - P) (Y - P) = d ^ 2 := by rw [dotp_self_sub, ← dist_sq, hPY]
  have hz : dotp (Z - P) (Z - P) = d ^ 2 := by rw [dotp_self_sub, ← dist_sq, hPZ]
  have hcxz : crsp (X - P) (Z - P) ≠ 0 := crsp_ne_zero_of_dist hd hPX hPZ hdXZ hXZ
  have hr : d ^ 2 / 2 ≤ dotp (X - P) (Z - P) := by
    have h := dist_le_sq hdXZ
    have e : X - Z = (X - P) - (Z - P) := by abel
    rw [dist_sq, e, dotp_sub_sub, hx, hz] at h
    nlinarith only [h]
  have hrpos : 0 < dotp (X - P) (Z - P) := by nlinarith only [hr, hd2]
  have hTX' : T ≠ X := by
    intro hcon
    rw [hcon] at hTYeq
    linarith only [hYXlt, hTYeq]
  have hTZ' : T ≠ Z := by
    intro hcon
    rw [hcon] at hTYeq
    linarith only [hYZlt, hTYeq]
  obtain ⟨S₁, hS₁ab, hS₁cd⟩ := lemmaA hd hTYeq hPX
    (le_of_eq (by rw [dist_comm, hPY])) (le_of_lt hYXlt) hTP hTX
    (by intro hcon; rw [hcon, dist_self] at hPY; linarith only [hd, hPY]) hXY.symm hT hTX'
  obtain ⟨S₂, hS₂ab, hS₂cd⟩ := lemmaA hd hTYeq hPZ
    (le_of_eq (by rw [dist_comm, hPY])) (le_of_lt hYZlt) hTP hTZ
    (by intro hcon; rw [hcon, dist_self] at hPY; linarith only [hd, hPY]) hYZ hT hTZ'
  obtain ⟨w, hw⟩ := show ∃ x, x = T - Y from ⟨_, rfl⟩
  rw [segment_eq_image'] at hS₁ab hS₁cd hS₂ab hS₂cd
  obtain ⟨u₁, hu₁, hS₁ab⟩ := hS₁ab
  obtain ⟨s₁, hs₁, hS₁cd⟩ := hS₁cd
  obtain ⟨u₂, hu₂, hS₂ab⟩ := hS₂ab
  obtain ⟨s₂, hs₂, hS₂cd⟩ := hS₂cd
  rw [← hw] at hS₁ab hS₂ab
  obtain ⟨γ, hγ⟩ := show ∃ x, x = crsp w (Z - P) / crsp (X - P) (Z - P) from ⟨_, rfl⟩
  obtain ⟨δ, hδ⟩ := show ∃ x, x = crsp (X - P) w / crsp (X - P) (Z - P) from ⟨_, rfl⟩
  have hweq : w = γ • (X - P) + δ • (Z - P) := by
    have h := cramer (X - P) (Z - P) w
    have e : crsp (X - P) (Z - P) • w =
        crsp (X - P) (Z - P) • (γ • (X - P) + δ • (Z - P)) := by
      rw [h]
      conv_rhs => rw [smul_add, smul_smul, smul_smul, hγ, hδ,
        mul_comm (crsp (X - P) (Z - P)) _, div_mul_cancel₀ _ hcxz,
        mul_comm (crsp (X - P) (Z - P)) _, div_mul_cancel₀ _ hcxz,
        crsp_skew (X - P) w, neg_smul, ← sub_eq_add_neg]
    have h2 := congrArg (fun V => (crsp (X - P) (Z - P))⁻¹ • V) e
    simp only [smul_smul, inv_mul_cancel₀ hcxz, one_smul] at h2
    exact h2
  have hS₁ : s₁ • (X - P) = (Y - P) + u₁ • w := by
    have e : P + s₁ • (X - P) = Y + u₁ • w := hS₁cd.trans hS₁ab.symm
    have e2 : Y + u₁ • w = P + ((Y - P) + u₁ • w) := by abel
    rw [e2] at e
    exact add_left_cancel e
  have hS₂ : s₂ • (Z - P) = (Y - P) + u₂ • w := by
    have e : P + s₂ • (Z - P) = Y + u₂ • w := hS₂cd.trans hS₂ab.symm
    have e2 : Y + u₂ • w = P + ((Y - P) + u₂ • w) := by abel
    rw [e2] at e
    exact add_left_cancel e
  have hS₁' : s₁ • (X - P) = (α + u₁ * γ) • (X - P) + (β + u₁ * δ) • (Z - P) := by
    have e : (α • (X - P) + β • (Z - P)) + u₁ • (γ • (X - P) + δ • (Z - P)) =
        (α + u₁ * γ) • (X - P) + (β + u₁ * δ) • (Z - P) := by
      rw [add_smul, add_smul, smul_add, smul_smul, smul_smul]
      abel
    rw [hyeq, hweq] at hS₁
    rw [e] at hS₁
    exact hS₁
  have hS₂' : s₂ • (Z - P) = (α + u₂ * γ) • (X - P) + (β + u₂ * δ) • (Z - P) := by
    have e : (α • (X - P) + β • (Z - P)) + u₂ • (γ • (X - P) + δ • (Z - P)) =
        (α + u₂ * γ) • (X - P) + (β + u₂ * δ) • (Z - P) := by
      rw [add_smul, add_smul, smul_add, smul_smul, smul_smul]
      abel
    rw [hyeq, hweq] at hS₂
    rw [e] at hS₂
    exact hS₂
  have e1 : s₁ * crsp (X - P) (Z - P) = (α + u₁ * γ) * crsp (X - P) (Z - P) := by
    have h := congrArg (fun V => crsp V (Z - P)) hS₁'
    simp only [crsp_add_left, crsp_smul_left, crsp_self, mul_zero, add_zero] at h
    exact h
  have e2 : (β + u₁ * δ) * crsp (X - P) (Z - P) = 0 := by
    have h := congrArg (fun V => crsp (X - P) V) hS₁'
    simp only [crsp_add_right, crsp_smul_right, crsp_self, mul_zero, add_zero, zero_add] at h
    exact h.symm
  have e3 : (α + u₂ * γ) * crsp (X - P) (Z - P) = 0 := by
    have h := congrArg (fun V => crsp V (Z - P)) hS₂'
    simp only [crsp_add_left, crsp_smul_left, crsp_self, mul_zero, add_zero, zero_add] at h
    exact h.symm
  have e4 : s₂ * crsp (X - P) (Z - P) = (β + u₂ * δ) * crsp (X - P) (Z - P) := by
    have h := congrArg (fun V => crsp (X - P) V) hS₂'
    simp only [crsp_add_right, crsp_smul_right, crsp_self, mul_zero, zero_add] at h
    exact h
  have hβu₁ : β + u₁ * δ = 0 := by
    rcases mul_eq_zero.mp e2 with h | h
    · exact h
    · exact absurd h hcxz
  have hαu₂ : α + u₂ * γ = 0 := by
    rcases mul_eq_zero.mp e3 with h | h
    · exact h
    · exact absurd h hcxz
  have hu₁pos : 0 < u₁ := by
    rcases eq_or_lt_of_le hu₁.1 with hcon | hcon
    · exfalso
      rw [← hcon] at hβu₁
      simp only [zero_mul, add_zero] at hβu₁
      linarith only [hβ, hβu₁]
    · exact hcon
  have hu₂pos : 0 < u₂ := by
    rcases eq_or_lt_of_le hu₂.1 with hcon | hcon
    · exfalso
      rw [← hcon] at hαu₂
      simp only [zero_mul, add_zero] at hαu₂
      linarith only [hα, hαu₂]
    · exact hcon
  have hδneg : δ < 0 := by
    by_contra hcon
    push_neg at hcon
    have h1 : 0 ≤ u₁ * δ := mul_nonneg hu₁pos.le hcon
    nlinarith only [hβu₁, hβ, h1]
  have hγneg : γ < 0 := by
    by_contra hcon
    push_neg at hcon
    have h1 : 0 ≤ u₂ * γ := mul_nonneg hu₂pos.le hcon
    nlinarith only [hαu₂, hα, h1]
  have hδle : δ ≤ -β := by
    have h1 : u₁ * δ = -β := by linarith only [hβu₁]
    rw [← h1]
    nlinarith only [mul_nonneg_of_nonpos_of_nonpos (by linarith only [hu₁.2] : u₁ - 1 ≤ 0) hδneg.le]
  have hγle : γ ≤ -α := by
    have h1 : u₂ * γ = -α := by linarith only [hαu₂]
    rw [← h1]
    nlinarith only [mul_nonneg_of_nonpos_of_nonpos (by linarith only [hu₂.2] : u₂ - 1 ≤ 0) hγneg.le]
  have hnorm : dotp w w = d ^ 2 := by
    rw [hw, dotp_self_sub, ← dist_sq, hTYeq]
  have hynorm : α ^ 2 * dotp (X - P) (X - P) + 2 * α * β * dotp (X - P) (Z - P) +
      β ^ 2 * dotp (Z - P) (Z - P) = d ^ 2 := by
    have h := hy
    rw [hyeq, dotp_smul2] at h
    exact h
  rw [hweq, dotp_smul2, hx, hz] at hnorm
  rw [hx, hz] at hynorm
  have hγ2 : α ^ 2 ≤ γ ^ 2 := by
    have h1 : γ + α ≤ 0 := by nlinarith only [hγle, hα]
    have h2 : γ - α ≤ 0 := by nlinarith only [hγle, hα]
    nlinarith only [mul_nonneg_of_nonpos_of_nonpos h1 h2]
  have hδ2 : β ^ 2 ≤ δ ^ 2 := by
    have h1 : δ + β ≤ 0 := by nlinarith only [hδle, hβ]
    have h2 : δ - β ≤ 0 := by nlinarith only [hδle, hβ]
    nlinarith only [mul_nonneg_of_nonpos_of_nonpos h1 h2]
  have hγδ : α * β ≤ γ * δ := by
    have h1 : (-α) * δ ≤ γ * δ := mul_le_mul_of_nonpos_right hγle hδneg.le
    have h2 : (-α) * (-β) ≤ (-α) * δ := mul_le_mul_of_nonpos_left hδle (by linarith only [hα])
    nlinarith only [h1, h2]
  have hsum : (γ ^ 2 - α ^ 2) * d ^ 2 + (δ ^ 2 - β ^ 2) * d ^ 2 +
      2 * (γ * δ - α * β) * dotp (X - P) (Z - P) = 0 := by
    linear_combination hnorm - hynorm
  have ht1 : 0 ≤ (γ ^ 2 - α ^ 2) * d ^ 2 := mul_nonneg (by nlinarith only [hγ2]) hd2.le
  have ht2 : 0 ≤ (δ ^ 2 - β ^ 2) * d ^ 2 := mul_nonneg (by nlinarith only [hδ2]) hd2.le
  have ht3 : 0 ≤ 2 * (γ * δ - α * β) * dotp (X - P) (Z - P) := by
    have h1 : 0 ≤ (γ * δ - α * β) * dotp (X - P) (Z - P) :=
      mul_nonneg (sub_nonneg.mpr hγδ) hrpos.le
    nlinarith only [h1]
  have hγ2eq : (γ ^ 2 - α ^ 2) * d ^ 2 = 0 := by nlinarith only [hsum, ht1, ht2, ht3]
  have hδ2eq : (δ ^ 2 - β ^ 2) * d ^ 2 = 0 := by nlinarith only [hsum, ht1, ht2, ht3]
  have hγeq : γ = -α := by
    have h1 : γ ^ 2 = α ^ 2 := by
      have h2 : γ ^ 2 - α ^ 2 = 0 := by
        rcases mul_eq_zero.mp hγ2eq with h | h
        · exact h
        · exact absurd h hd2.ne'
      linear_combination h2
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h1 with h | h
    · exfalso
      nlinarith only [hγle, hα, h]
    · exact h
  have hδeq : δ = -β := by
    have h1 : δ ^ 2 = β ^ 2 := by
      have h2 : δ ^ 2 - β ^ 2 = 0 := by
        rcases mul_eq_zero.mp hδ2eq with h | h
        · exact h
        · exact absurd h hd2.ne'
      linear_combination h2
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h1 with h | h
    · exfalso
      nlinarith only [hδle, hβ, h]
    · exact h
  have hwfinal : w = -(Y - P) := by
    rw [hweq, hγeq, hδeq, neg_smul, neg_smul, ← neg_add, ← hyeq]
  have hTP' : T = P := by
    have h1 : T = Y + w := by rw [hw]; abel
    rw [h1, hwfinal]
    abel
  exact hT hTP'

/-- **Lemma B**: among any three distinct diameter-neighbors of a point `P`,
one of them has `P` as its only diameter-neighbor. -/
lemma lemmaB {P X Y Z : P2} {d : ℝ} (hd : 0 < d)
    (hXY : X ≠ Y) (hYZ : Y ≠ Z) (hXZ : X ≠ Z)
    (hPX : dist P X = d) (hPY : dist P Y = d) (hPZ : dist P Z = d)
    (hdXY : dist X Y ≤ d) (hdYZ : dist Y Z ≤ d) (hdXZ : dist X Z ≤ d) :
    ∃ M : P2, (M = X ∨ M = Y ∨ M = Z) ∧ ∀ T : P2, T ≠ P → dist T P ≤ d →
      dist T X ≤ d → dist T Y ≤ d → dist T Z ≤ d → dist M T < d := by
  have hcxy : crsp (X - P) (Y - P) ≠ 0 := crsp_ne_zero_of_dist hd hPX hPY hdXY hXY
  have hcyz : crsp (Y - P) (Z - P) ≠ 0 := crsp_ne_zero_of_dist hd hPY hPZ hdYZ hYZ
  have hczx : crsp (Z - P) (X - P) ≠ 0 := crsp_ne_zero_of_dist hd hPZ hPX
    (by rwa [dist_comm]) hXZ.symm
  have key : (0 < crsp (X - P) (Y - P) * crsp (Y - P) (Z - P)) ∨
      (0 < crsp (Y - P) (Z - P) * crsp (Z - P) (X - P)) ∨
      (0 < crsp (Z - P) (X - P) * crsp (X - P) (Y - P)) := by
    rcases lt_or_gt_of_ne hcxy with h1 | h1
    · rcases lt_or_gt_of_ne hcyz with h2 | h2
      · rcases lt_or_gt_of_ne hczx with h3 | h3
        · exact Or.inl (mul_pos_of_neg_of_neg h1 h2)
        · exact Or.inl (mul_pos_of_neg_of_neg h1 h2)
      · rcases lt_or_gt_of_ne hczx with h3 | h3
        · exact Or.inr (Or.inr (mul_pos_of_neg_of_neg h3 h1))
        · exact Or.inr (Or.inl (mul_pos h2 h3))
    · rcases lt_or_gt_of_ne hcyz with h2 | h2
      · rcases lt_or_gt_of_ne hczx with h3 | h3
        · exact Or.inr (Or.inl (mul_pos_of_neg_of_neg h2 h3))
        · exact Or.inr (Or.inr (mul_pos h3 h1))
      · rcases lt_or_gt_of_ne hczx with h3 | h3
        · exact Or.inl (mul_pos h1 h2)
        · exact Or.inl (mul_pos h1 h2)
  rcases key with hkey | hkey | hkey
  · -- The middle ray is `Y`.
    refine ⟨Y, Or.inr (Or.inl rfl), fun T hT hTP hTX hTY hTZ => ?_⟩
    have hmid : crsp (Y - P) (X - P) * crsp (Y - P) (Z - P) < 0 := by
      rw [crsp_skew (Y - P) (X - P)]
      nlinarith only [hkey]
    by_contra hcon
    push_neg at hcon
    have hTYeq : dist Y T = d := le_antisymm (by rwa [dist_comm]) hcon
    obtain ⟨α, β, hα, hβ, hyeq, hYXlt, hYZlt⟩ :=
      lemmaB_middle hd hXY hYZ hXZ hPX hPY hPZ hdXY hdYZ hdXZ hmid
    exact lemmaB_core hd hXY hYZ hXZ hPX hPY hPZ hdXY hdYZ hdXZ hα hβ hyeq hYXlt hYZlt
      hT hTP hTX hTY hTZ hTYeq
  · -- The middle ray is `Z`.
    refine ⟨Z, Or.inr (Or.inr rfl), fun T hT hTP hTX hTY hTZ => ?_⟩
    have hmid : crsp (Z - P) (Y - P) * crsp (Z - P) (X - P) < 0 := by
      rw [crsp_skew (Z - P) (Y - P)]
      nlinarith only [hkey]
    by_contra hcon
    push_neg at hcon
    have hTYeq : dist Z T = d := le_antisymm (by rwa [dist_comm]) hcon
    obtain ⟨α, β, hα, hβ, hyeq, hYXlt, hYZlt⟩ :=
      lemmaB_middle hd hYZ hXZ.symm hXY.symm hPY hPZ hPX hdYZ (by rwa [dist_comm])
        (by rwa [dist_comm]) hmid
    exact lemmaB_core hd hYZ hXZ.symm hXY.symm hPY hPZ hPX hdYZ (by rwa [dist_comm])
      (by rwa [dist_comm]) hα hβ hyeq hYXlt hYZlt hT hTP hTY hTZ hTX hTYeq
  · -- The middle ray is `X`.
    refine ⟨X, Or.inl rfl, fun T hT hTP hTX hTY hTZ => ?_⟩
    have hmid : crsp (X - P) (Z - P) * crsp (X - P) (Y - P) < 0 := by
      rw [crsp_skew (X - P) (Z - P)]
      nlinarith only [hkey]
    by_contra hcon
    push_neg at hcon
    have hTYeq : dist X T = d := le_antisymm (by rwa [dist_comm]) hcon
    obtain ⟨α, β, hα, hβ, hyeq, hYXlt, hYZlt⟩ :=
      lemmaB_middle hd hXZ.symm hXY hYZ.symm hPZ hPX hPY (by rwa [dist_comm]) hdXY
        (by rwa [dist_comm]) hmid
    exact lemmaB_core hd hXZ.symm hXY hYZ.symm hPZ hPX hPY (by rwa [dist_comm]) hdXY
      (by rwa [dist_comm]) hα hβ hyeq hYXlt hYZlt hT hTP hTZ hTX hTY hTYeq

/-- The fiber of ordered diameters with first endpoint `P` is in bijection with
the diameter-neighbors of `P`. -/
lemma diam_fiber_fst_card {S : Finset P2} {d : ℝ} {P : P2} (hP : P ∈ S) :
    ((S.offDiag.filter fun p => dist p.1 p.2 = d).filter fun p => p.1 = P).card =
      (S.filter fun y => P ≠ y ∧ dist P y = d).card := by
  apply Finset.card_nbij' Prod.snd fun y => (P, y)
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_offDiag] at hp ⊢
    obtain ⟨⟨⟨-, hp2S, hpne⟩, hpd⟩, hp1P⟩ := hp
    exact ⟨hp2S, hp1P ▸ hpne, hp1P ▸ hpd⟩
  · intro y hy
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_offDiag] at hy ⊢
    obtain ⟨hyS, hPne, hPd⟩ := hy
    exact ⟨⟨⟨hP, hyS, hPne⟩, hPd⟩, trivial⟩
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter] at hp
    exact Prod.ext_iff.mpr ⟨hp.2.symm, rfl⟩
  · intro y _
    rfl

/-- The fiber of ordered diameters with second endpoint `P` is in bijection with
the diameter-neighbors of `P`. -/
lemma diam_fiber_snd_card {S : Finset P2} {d : ℝ} {P : P2} (hP : P ∈ S) :
    ((S.offDiag.filter fun p => dist p.1 p.2 = d).filter fun p => p.2 = P).card =
      (S.filter fun y => P ≠ y ∧ dist P y = d).card := by
  apply Finset.card_nbij' Prod.fst fun y => (y, P)
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_offDiag] at hp ⊢
    obtain ⟨⟨⟨hp1S, -, hpne⟩, hpd⟩, hp2P⟩ := hp
    refine ⟨hp1S, (hp2P ▸ hpne).symm, ?_⟩
    have hpd' : dist p.1 P = d := hp2P ▸ hpd
    rw [dist_comm] at hpd'
    exact hpd'
  · intro y hy
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_offDiag] at hy ⊢
    obtain ⟨hyS, hPne, hPd⟩ := hy
    refine ⟨⟨⟨hyS, hP, hPne.symm⟩, ?_⟩, trivial⟩
    rw [dist_comm]
    exact hPd
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter] at hp
    exact Prod.ext_iff.mpr ⟨rfl, hp.2.symm⟩
  · intro y _
    rfl

/-- Counting bound: the number of (ordered) diameters is at most `2 * |S|`. -/
lemma diam_count_le : ∀ (n : ℕ) (S : Finset P2) (d : ℝ), S.card ≤ n →
    (∀ p ∈ S.offDiag, dist p.1 p.2 ≤ d) →
    (S.offDiag.filter fun p => dist p.1 p.2 = d).card ≤ 2 * S.card := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S d hcard hd
  by_cases hcase : ∃ P ∈ S, 3 ≤ (S.filter fun y => P ≠ y ∧ dist P y = d).card
  · -- Case 1: some point `P` has at least three diameter-neighbors `X`, `Y`, `Z`.
    obtain ⟨P, hPS, hdeg⟩ := hcase
    have hN2 : 2 < (S.filter fun y => P ≠ y ∧ dist P y = d).card := hdeg
    rw [Finset.two_lt_card] at hN2
    obtain ⟨X, hX, Y, hY, Z, hZ, hXY, hXZ, hYZ⟩ := hN2
    rw [Finset.mem_filter] at hX hY hZ
    obtain ⟨hXS, hPXne, hPXeq⟩ := hX
    obtain ⟨hYS, hPYne, hPYeq⟩ := hY
    obtain ⟨hZS, hPZne, hPZeq⟩ := hZ
    have hdpos : 0 < d := by
      have h := dist_pos.mpr hPXne
      rwa [hPXeq] at h
    have hdXY : dist X Y ≤ d := hd (X, Y) (Finset.mem_offDiag.mpr ⟨hXS, hYS, hXY⟩)
    have hdXZ : dist X Z ≤ d := hd (X, Z) (Finset.mem_offDiag.mpr ⟨hXS, hZS, hXZ⟩)
    have hdYZ : dist Y Z ≤ d := hd (Y, Z) (Finset.mem_offDiag.mpr ⟨hYS, hZS, hYZ⟩)
    -- One of `X`, `Y`, `Z` — call it `M` — has `P` as its only diameter-neighbor.
    obtain ⟨M, hM, hMT⟩ := lemmaB hdpos hXY hYZ hXZ hPXeq hPYeq hPZeq hdXY hdYZ hdXZ
    have hMS : M ∈ S := by
      rcases hM with rfl | rfl | rfl
      · exact hXS
      · exact hYS
      · exact hZS
    have hMneP : M ≠ P := by
      rcases hM with rfl | rfl | rfl
      · exact fun h => hPXne h.symm
      · exact fun h => hPYne h.symm
      · exact fun h => hPZne h.symm
    have hMP : dist M P = d := by
      rcases hM with rfl | rfl | rfl
      · rw [dist_comm]; exact hPXeq
      · rw [dist_comm]; exact hPYeq
      · rw [dist_comm]; exact hPZeq
    have hMfilter : S.filter (fun y => M ≠ y ∧ dist M y = d) = {P} := by
      ext T
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hTS, hMneT, hMTeq⟩
        by_contra hTneP
        have hTP : dist T P ≤ d := hd (T, P) (Finset.mem_offDiag.mpr ⟨hTS, hPS, hTneP⟩)
        have hTX : dist T X ≤ d := by
          by_cases h : T = X
          · rw [h, dist_self]; exact hdpos.le
          · exact hd (T, X) (Finset.mem_offDiag.mpr ⟨hTS, hXS, h⟩)
        have hTY : dist T Y ≤ d := by
          by_cases h : T = Y
          · rw [h, dist_self]; exact hdpos.le
          · exact hd (T, Y) (Finset.mem_offDiag.mpr ⟨hTS, hYS, h⟩)
        have hTZ : dist T Z ≤ d := by
          by_cases h : T = Z
          · rw [h, dist_self]; exact hdpos.le
          · exact hd (T, Z) (Finset.mem_offDiag.mpr ⟨hTS, hZS, h⟩)
        have hlt := hMT T hTneP hTP hTX hTY hTZ
        rw [hMTeq] at hlt
        exact lt_irrefl d hlt
      · rintro rfl
        exact ⟨hPS, hMneP, hMP⟩
    -- Split the ordered diameters into those avoiding `M` and those through `M`.
    have hsplit : (S.offDiag.filter fun p => dist p.1 p.2 = d).card =
        ((S.offDiag.filter fun p => dist p.1 p.2 = d).filter fun p => p.1 ≠ M ∧ p.2 ≠ M).card +
          ((S.offDiag.filter fun p => dist p.1 p.2 = d).filter
            fun p => ¬(p.1 ≠ M ∧ p.2 ≠ M)).card := by
      rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter_filter_not _ _ _),
        Finset.filter_union_filter_not_eq]
    have hE1 : (S.offDiag.filter fun p => dist p.1 p.2 = d).filter
          (fun p => p.1 ≠ M ∧ p.2 ≠ M) =
        (S.erase M).offDiag.filter fun p => dist p.1 p.2 = d := by
      ext ⟨a, b⟩
      simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_erase]
      tauto
    have hE1card : ((S.offDiag.filter fun p => dist p.1 p.2 = d).filter
        fun p => p.1 ≠ M ∧ p.2 ≠ M).card ≤ 2 * (S.erase M).card := by
      rw [hE1]
      exact ih _ (by
        have h1 : (S.erase M).card = S.card - 1 := Finset.card_erase_of_mem hMS
        have h2 : 0 < S.card := Finset.card_pos.mpr ⟨M, hMS⟩
        omega) _ _ (Nat.le_refl _) fun p hp =>
        hd p (Finset.offDiag_mono (Finset.erase_subset M S) hp)
    have hE2 : (S.offDiag.filter fun p => dist p.1 p.2 = d).filter
          (fun p => ¬(p.1 ≠ M ∧ p.2 ≠ M)) =
        ((S.offDiag.filter fun p => dist p.1 p.2 = d).filter fun p => p.1 = M) ∪
          ((S.offDiag.filter fun p => dist p.1 p.2 = d).filter fun p => p.2 = M) := by
      rw [← Finset.filter_or]
      exact Finset.filter_congr fun x _ => by simp only [not_and_or, not_ne_iff]
    have hE2card : ((S.offDiag.filter fun p => dist p.1 p.2 = d).filter
        fun p => ¬(p.1 ≠ M ∧ p.2 ≠ M)).card = 2 := by
      have hdisj : Disjoint ((S.offDiag.filter fun p => dist p.1 p.2 = d).filter fun p => p.1 = M)
          ((S.offDiag.filter fun p => dist p.1 p.2 = d).filter fun p => p.2 = M) := by
        rw [Finset.disjoint_filter]
        rintro ⟨a, b⟩ hp haM hbM
        rw [Finset.mem_filter, Finset.mem_offDiag] at hp
        exact hp.1.2.2 (haM.trans hbM.symm)
      rw [hE2, Finset.card_union_of_disjoint hdisj, diam_fiber_fst_card hMS,
        diam_fiber_snd_card hMS, hMfilter, Finset.card_singleton]
    have hScard' : (S.erase M).card = S.card - 1 := Finset.card_erase_of_mem hMS
    have hSpos : 0 < S.card := Finset.card_pos.mpr ⟨M, hMS⟩
    omega
  · -- Case 2: every point has at most two diameter-neighbors; count by fibers.
    have hle2 : ∀ P ∈ S, (S.filter fun y => P ≠ y ∧ dist P y = d).card ≤ 2 := by
      intro P hP
      by_contra h
      exact hcase ⟨P, hP, not_le.mp h⟩
    have hsum : (S.offDiag.filter fun p => dist p.1 p.2 = d).card =
        ∑ P ∈ S, ((S.offDiag.filter fun p => dist p.1 p.2 = d).filter
          fun p => p.1 = P).card := by
      apply Finset.card_eq_sum_card_fiberwise
      intro p hp
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_offDiag] at hp
      exact Finset.mem_coe.mpr hp.1.1
    calc (S.offDiag.filter fun p => dist p.1 p.2 = d).card
        = ∑ P ∈ S, ((S.offDiag.filter fun p => dist p.1 p.2 = d).filter
            fun p => p.1 = P).card := hsum
      _ = ∑ P ∈ S, (S.filter fun y => P ≠ y ∧ dist P y = d).card :=
          Finset.sum_congr rfl fun P hP => diam_fiber_fst_card hP
      _ ≤ ∑ _P ∈ S, 2 := Finset.sum_le_sum fun P hP => hle2 P hP
      _ = 2 * S.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

snip end

/-- The maximal distance between two of the points. -/
noncomputable def maxPairDist {n : ℕ} (hn : 2 ≤ n) (pts : Fin n → P2) : ℝ :=
  (Finset.univ.filter fun q : Fin n × Fin n => q.1 < q.2).sup'
    ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by simp⟩
    fun q => dist (pts q.1) (pts q.2)

problem imo1965_p6 (n : ℕ) (hn : 3 ≤ n) (pts : Fin n → P2) (hinj : Function.Injective pts) :
    ((Finset.univ.filter fun p : Fin n × Fin n =>
        p.1 < p.2 ∧ dist (pts p.1) (pts p.2) = maxPairDist (by omega) pts).card) ≤ n := by
  generalize hd : maxPairDist (by omega) pts = d
  set S := Finset.image pts Finset.univ with hSdef
  have hScard : S.card = n := by
    rw [hSdef, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  -- Every distance between two distinct points of `S` is at most `d`.
  have hd_le : ∀ p ∈ S.offDiag, dist p.1 p.2 ≤ d := by
    intro p hp
    rw [← hd]
    rw [Finset.mem_offDiag] at hp
    obtain ⟨ha, hb, hab⟩ := hp
    rw [hSdef] at ha hb
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp ha
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hb
    rw [← hi, ← hj] at hab ⊢
    have hij : i ≠ j := fun h => hab (by rw [h])
    have key : ∀ i j : Fin n, i < j → dist (pts i) (pts j) ≤ maxPairDist (by omega) pts := by
      intro i j h
      have h1 : dist (pts i) (pts j) =
          (fun q : Fin n × Fin n => dist (pts q.1) (pts q.2)) (i, j) := rfl
      have h2 : (fun q : Fin n × Fin n => dist (pts q.1) (pts q.2)) (i, j) ≤
          maxPairDist (by omega) pts :=
        Finset.le_sup' (fun q : Fin n × Fin n => dist (pts q.1) (pts q.2))
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      rwa [h1]
    rcases lt_trichotomy i j with h | h | h
    · exact key i j h
    · exact absurd h hij
    · rw [dist_comm]; exact key j i h
  have hcount : (S.offDiag.filter fun p => dist p.1 p.2 = d).card ≤ 2 * n := by
    have h := diam_count_le n S d (le_of_eq hScard) hd_le
    rwa [hScard] at h
  -- The ordered index pairs at distance `d` map bijectively onto the ordered
  -- diameter pairs of `S`.
  have himg : (Finset.univ.filter fun p : Fin n × Fin n =>
        p.1 ≠ p.2 ∧ dist (pts p.1) (pts p.2) = d).image (fun p => (pts p.1, pts p.2)) =
      S.offDiag.filter fun p => dist p.1 p.2 = d := by
    ext ⟨a, b⟩
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_offDiag, Prod.mk.injEq, hSdef]
    constructor
    · rintro ⟨⟨i, j⟩, ⟨hij, hdij⟩, rfl, rfl⟩
      exact ⟨⟨⟨i, rfl⟩, ⟨j, rfl⟩, fun h => hij (hinj h)⟩, hdij⟩
    · rintro ⟨⟨⟨i, rfl⟩, ⟨j, rfl⟩, hab⟩, hdab⟩
      exact ⟨⟨i, j⟩, ⟨fun h => hab (congrArg pts h), hdab⟩, rfl, rfl⟩
  have hE'card : (Finset.univ.filter fun p : Fin n × Fin n =>
      p.1 ≠ p.2 ∧ dist (pts p.1) (pts p.2) = d).card =
      (S.offDiag.filter fun p => dist p.1 p.2 = d).card := by
    rw [← himg]
    exact (Finset.card_image_of_injective _ (hinj.prodMap hinj)).symm
  -- Each unordered diameter corresponds to two ordered ones.
  have hsplit : (Finset.univ.filter fun p : Fin n × Fin n =>
      p.1 ≠ p.2 ∧ dist (pts p.1) (pts p.2) = d).card =
      2 * (Finset.univ.filter fun p : Fin n × Fin n =>
        p.1 < p.2 ∧ dist (pts p.1) (pts p.2) = d).card := by
    have hU : (Finset.univ.filter fun p : Fin n × Fin n =>
        p.1 ≠ p.2 ∧ dist (pts p.1) (pts p.2) = d) =
        (Finset.univ.filter fun p : Fin n × Fin n =>
          p.1 < p.2 ∧ dist (pts p.1) (pts p.2) = d) ∪
          (Finset.univ.filter fun p : Fin n × Fin n =>
            p.2 < p.1 ∧ dist (pts p.1) (pts p.2) = d) := by
      ext ⟨i, j⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      constructor
      · rintro ⟨hij, hdij⟩
        rcases lt_or_gt_of_ne hij with h | h
        · exact Or.inl ⟨h, hdij⟩
        · exact Or.inr ⟨h, hdij⟩
      · rintro (⟨h, hdij⟩ | ⟨h, hdij⟩)
        · exact ⟨ne_of_lt h, hdij⟩
        · exact ⟨ne_of_gt h, hdij⟩
    have hdisj : Disjoint
        (Finset.univ.filter fun p : Fin n × Fin n =>
          p.1 < p.2 ∧ dist (pts p.1) (pts p.2) = d)
        (Finset.univ.filter fun p : Fin n × Fin n =>
          p.2 < p.1 ∧ dist (pts p.1) (pts p.2) = d) := by
      rw [Finset.disjoint_filter]
      rintro ⟨i, j⟩ - ⟨h1, -⟩ ⟨h2, -⟩
      exact lt_irrefl i (h1.trans h2)
    have hswap : (Finset.univ.filter fun p : Fin n × Fin n =>
        p.2 < p.1 ∧ dist (pts p.1) (pts p.2) = d).card =
        (Finset.univ.filter fun p : Fin n × Fin n =>
          p.1 < p.2 ∧ dist (pts p.1) (pts p.2) = d).card := by
      apply Finset.card_nbij' Prod.swap Prod.swap
      · rintro ⟨i, j⟩ hp
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
          Prod.fst_swap, Prod.snd_swap] at hp ⊢
        exact ⟨hp.1, by rw [dist_comm]; exact hp.2⟩
      · rintro ⟨i, j⟩ hp
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
          Prod.fst_swap, Prod.snd_swap] at hp ⊢
        exact ⟨hp.1, by rw [dist_comm]; exact hp.2⟩
      · intro p _
        exact Prod.swap_swap p
      · intro p _
        exact Prod.swap_swap p
    rw [hU, Finset.card_union_of_disjoint hdisj, hswap, two_mul]
  have h2 : 2 * (Finset.univ.filter fun p : Fin n × Fin n =>
      p.1 < p.2 ∧ dist (pts p.1) (pts p.2) = d).card ≤ 2 * n := by
    calc 2 * (Finset.univ.filter fun p : Fin n × Fin n =>
            p.1 < p.2 ∧ dist (pts p.1) (pts p.2) = d).card
        = (Finset.univ.filter fun p : Fin n × Fin n =>
            p.1 ≠ p.2 ∧ dist (pts p.1) (pts p.2) = d).card := hsplit.symm
      _ = (S.offDiag.filter fun p => dist p.1 p.2 = d).card := hE'card
      _ ≤ 2 * n := hcount
  exact Nat.le_of_mul_le_mul_left h2 Nat.two_pos

end Imo1965P6
