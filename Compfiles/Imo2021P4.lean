/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Affine.Convex
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 2021, Problem 4

Let Γ be a circle with center I, and ABCD a convex quadrilateral such that each of
the segments AB, BC, CD and DA is tangent to Γ. Let Ω be the circumcircle of the
triangle AIC. The extension of BA beyond A meets Ω at X, and the extension of BC
beyond C meets Ω at Z. The extensions of AD and CD beyond D meet Ω at Y and T,
respectively. Prove that

  AD + DT + TX + XA = CD + DY + YZ + ZC.

## Formalization notes

We work in the complex plane, identifying points with complex numbers, so that the
distance between two points `z w : ℂ` is `dist z w = ‖z - w‖`. By translating the
center I of Γ to the origin and scaling (the claim is homogeneous of degree 1), we
may and do assume that Γ is the unit circle centered at I = 0. We denote the
contact points of Γ with the segments AB, BC, CD, DA by p, q, r, s; the hypothesis
that e.g. the segment AB is tangent to Γ at p is encoded by: p lies on the segment
AB (`Wbtw ℝ A p B`), `‖p‖ = 1`, and the radius Ip is perpendicular to AB, i.e.
`((A - p) * conj p).re = 0` and `((B - p) * conj p).re = 0`. The circle Ω is given
through its center O together with the equidistance conditions on A, I, C (which
characterize the circumcircle of the nondegenerate triangle AIC) and on X, Y, Z, T
(which say that these points lie on Ω); the `Wbtw` hypotheses on X, Y, Z, T encode
"the extension of BA beyond A" etc., and `X ≠ A` etc. say that they are the second
intersection points of the respective lines with Ω. The nondegeneracy hypotheses
(`p ≠ s`, `p + s ≠ 0`, etc., and distinctness of adjacent vertices) follow from the
convexity of ABCD in the original problem.
-/

open Complex ComplexConjugate

namespace Imo2021P4

snip begin

lemma normSq_eq_one_of_norm_eq_one {u : ℂ} (hu : ‖u‖ = 1) : normSq u = 1 := by
  rw [← norm_mul_self_eq_normSq, hu, mul_one]

lemma unit_ne_zero {u : ℂ} (hu : ‖u‖ = 1) : u ≠ 0 := by
  intro h
  rw [h, norm_zero] at hu
  norm_num at hu

lemma conj_unit_mul {u : ℂ} (hu : ‖u‖ = 1) : conj u * u = 1 := by
  rw [mul_comm, Complex.mul_conj, normSq_eq_one_of_norm_eq_one hu]
  norm_num

lemma conj_eq_inv_of_unit {u : ℂ} (hu : ‖u‖ = 1) : conj u = u⁻¹ := by
  exact eq_inv_of_mul_eq_one_left (conj_unit_mul hu)

/-- For a unit complex number, `u * conj u` has real part 1. -/
lemma re_mul_conj_self_of_unit {u : ℂ} (hu : ‖u‖ = 1) : (u * conj u).re = 1 := by
  rw [Complex.mul_conj, normSq_eq_one_of_norm_eq_one hu]
  norm_num

/-- A point `z` on the line perpendicular to the unit vector `u` at `u` satisfies
`(z * conj u).re = 1`. -/
lemma re_mul_conj_eq_one_of_perp {z u : ℂ} (hu : ‖u‖ = 1)
    (h : ((z - u) * conj u).re = 0) : (z * conj u).re = 1 := by
  have h1 : ((z - u) * conj u).re = (z * conj u).re - (u * conj u).re := by
    rw [sub_mul, Complex.sub_re]
  rw [h1, re_mul_conj_self_of_unit hu] at h
  linarith

/-- A complex number perpendicular to two unit complex numbers that are not equal
or opposite is zero. -/
lemma eq_zero_of_re_mul_conj_eq_zero {w p s : ℂ} (hp : ‖p‖ = 1) (hs : ‖s‖ = 1)
    (hps : p ≠ s) (hps0 : p + s ≠ 0)
    (hwp : (w * conj p).re = 0) (hws : (w * conj s).re = 0) : w = 0 := by
  have hpp : conj p * p = 1 := conj_unit_mul hp
  have hss : conj s * s = 1 := conj_unit_mul hs
  -- `w * conj p` and `w * conj s` are purely imaginary
  set β : ℝ := (w * conj p).im with hβ
  set γ : ℝ := (w * conj s).im with hγ
  have hwβ : w * conj p = β * I := by
    rw [Complex.ext_iff]
    constructor
    · rw [hwp]
      simp
    · simp [hβ]
  have hwγ : w * conj s = γ * I := by
    rw [Complex.ext_iff]
    constructor
    · rw [hws]
      simp
    · simp [hγ]
  have hwp' : w = β * I * p := by
    have h := congrArg (· * p) hwβ
    rw [mul_assoc, hpp, mul_one] at h
    rw [h]
  have hws' : w = γ * I * s := by
    have h := congrArg (· * s) hwγ
    rw [mul_assoc, hss, mul_one] at h
    rw [h]
  have hβγ : (β : ℂ) * p = γ * s := by
    have h : β * I * p = γ * I * s := by rw [← hwp', ← hws']
    have hI : (I : ℂ) ≠ 0 := Complex.I_ne_zero
    have e1 : β * I * p = I * (β * p) := by ring
    have e2 : γ * I * s = I * (γ * s) := by ring
    rw [e1, e2] at h
    exact mul_left_cancel₀ hI h
  have hnorm : β ^ 2 = γ ^ 2 := by
    have h := congrArg normSq hβγ
    rw [normSq_mul, normSq_mul, normSq_eq_one_of_norm_eq_one hp,
      normSq_eq_one_of_norm_eq_one hs, normSq_ofReal, normSq_ofReal] at h
    rw [sq, sq]
    linarith [h]
  have hβγ2 : β = γ ∨ β = -γ := sq_eq_sq_iff_eq_or_eq_neg.mp hnorm
  rcases hβγ2 with h | h
  · have hc : (β : ℂ) = γ := by exact_mod_cast h
    rw [hc] at hβγ
    have h0 : (β : ℂ) * (p - s) = 0 := by
      rw [hc]
      linear_combination hβγ
    have hβ0 : β = 0 := by
      rcases mul_eq_zero.mp h0 with h1 | h1
      · exact_mod_cast h1
      · exact absurd (sub_eq_zero.mp h1) hps
    rw [hwp', hβ0]
    simp
  · have hc : (β : ℂ) = -γ := by exact_mod_cast h
    rw [hc] at hβγ
    have h0 : (β : ℂ) * (p + s) = 0 := by
      rw [hc]
      linear_combination hβγ
    have hβ0 : β = 0 := by
      rcases mul_eq_zero.mp h0 with h1 | h1
      · exact_mod_cast h1
      · exact absurd h1 hps0
    rw [hwp', hβ0]
    simp

/-- The point `2 p s / (p + s)` lies on both tangent lines at `p` and `s`. -/
lemma re_tangent_inter {p s : ℂ} (hp : ‖p‖ = 1) (hs : ‖s‖ = 1) (hps0 : p + s ≠ 0) :
    ((2 * p * s / (p + s)) * conj p).re = 1 ∧
    ((2 * p * s / (p + s)) * conj s).re = 1 := by
  have hcp : conj p = p⁻¹ := conj_eq_inv_of_unit hp
  have hcs : conj s = s⁻¹ := conj_eq_inv_of_unit hs
  have hpn : p ≠ 0 := unit_ne_zero hp
  have hsn : s ≠ 0 := unit_ne_zero hs
  have hp' : p * conj p = 1 := by
    rw [Complex.mul_conj, normSq_eq_one_of_norm_eq_one hp]
    norm_num
  have hs' : s * conj s = 1 := by
    rw [Complex.mul_conj, normSq_eq_one_of_norm_eq_one hs]
    norm_num
  have e1 : (2 * p * s / (p + s)) * conj p = 2 * s / (p + s) := by
    calc (2 * p * s / (p + s)) * conj p
        = 2 * s * (p * conj p) / (p + s) := by
          field_simp
      _ = 2 * s / (p + s) := by rw [hp', mul_one]
  have e2 : (2 * p * s / (p + s)) * conj s = 2 * p / (p + s) := by
    calc (2 * p * s / (p + s)) * conj s
        = 2 * p * (s * conj s) / (p + s) := by
          field_simp
      _ = 2 * p / (p + s) := by rw [hs', mul_one]
  have ec : conj ((s - p) / (p + s)) = -((s - p) / (p + s)) := by
    have e : conj ((s - p) / (p + s)) = (s⁻¹ - p⁻¹) / (p⁻¹ + s⁻¹) := by
      rw [map_div₀, map_sub, map_add, hcp, hcs]
    have hpsinv : p⁻¹ + s⁻¹ ≠ 0 := by
      have e2 : p⁻¹ + s⁻¹ = (p + s) / (p * s) := by
        field_simp
        ring
      rw [e2]
      exact div_ne_zero hps0 (mul_ne_zero hpn hsn)
    rw [e, ← neg_div, div_eq_div_iff hpsinv hps0]
    field_simp
    ring
  have hre : ((s - p) / (p + s)).re = 0 := by
    have h := Complex.add_conj ((s - p) / (p + s))
    rw [ec, add_neg_cancel] at h
    have h2 : (0 : ℝ) = 2 * ((s - p) / (p + s)).re := by exact_mod_cast h
    linarith
  have key : (2 * s / (p + s)).re = 1 := by
    have ew : 2 * s / (p + s) = 1 + (s - p) / (p + s) := by
      field_simp
      ring
    rw [ew, Complex.add_re, hre]
    simp
  have key2 : (2 * p / (p + s)).re = 1 := by
    have ew : 2 * p / (p + s) = 1 - (s - p) / (p + s) := by
      field_simp
      ring
    rw [ew, Complex.sub_re, hre]
    simp
  rw [e1]
  exact ⟨key, by rw [e2]; exact key2⟩

/-- The intersection point of the tangent lines at `p` and `s`. -/
lemma tangent_inter {z p s : ℂ} (hp : ‖p‖ = 1) (hs : ‖s‖ = 1)
    (hps : p ≠ s) (hps0 : p + s ≠ 0)
    (hzp : (z * conj p).re = 1) (hzs : (z * conj s).re = 1) :
    z = 2 * p * s / (p + s) := by
  obtain ⟨h1, h2⟩ := re_tangent_inter hp hs hps0
  have hwp : ((z - 2 * p * s / (p + s)) * conj p).re = 0 := by
    rw [sub_mul, Complex.sub_re, hzp, h1]
    norm_num
  have hws : ((z - 2 * p * s / (p + s)) * conj s).re = 0 := by
    rw [sub_mul, Complex.sub_re, hzs, h2]
    norm_num
  have h := eq_zero_of_re_mul_conj_eq_zero hp hs hps hps0 hwp hws
  exact sub_eq_zero.mp h

/-- Perpendicularity transfers along a weakly-between point. -/
lemma perp_of_wbtw {u a b x : ℂ} (ha : ((a - u) * conj u).re = 0)
    (hb : ((b - u) * conj u).re = 0) (h : Wbtw ℝ b a x) (hne : a ≠ b) :
    ((x - u) * conj u).re = 0 := by
  rcases h with ⟨t, ht, hdef⟩
  rw [AffineMap.lineMap_apply_module] at hdef
  -- hdef : (1 - t) • b + t • x = a
  have htne : t ≠ 0 := by
    intro ht0
    rw [ht0] at hdef
    simp at hdef
    exact hne hdef.symm
  have key : ((a - u) * conj u).re =
      (1 - t) * ((b - u) * conj u).re + t * ((x - u) * conj u).re := by
    have e : a - u = (1 - t) • (b - u) + t • (x - u) := by
      rw [← hdef]
      module
    rw [e, add_mul, smul_mul_assoc, smul_mul_assoc, Complex.add_re, Complex.smul_re,
      Complex.smul_re, smul_eq_mul, smul_eq_mul]
  rw [ha, hb] at key
  rw [mul_zero, zero_add] at key
  -- key : 0 = t * ((x - u) * conj u).re
  rcases mul_eq_zero.mp key.symm with h1 | h1
  · exact absurd h1 htne
  · exact h1

/-- A point on the circle centered at `o` passing through `0`. -/
lemma normSq_eq_two_re_of_dist {z o : ℂ} (h : ‖o - z‖ = ‖o‖) :
    normSq z = 2 * (z * conj o).re := by
  have h2 : ‖o - z‖ * ‖o - z‖ = ‖o‖ * ‖o‖ := by rw [h]
  rw [norm_mul_self_eq_normSq, norm_mul_self_eq_normSq, normSq_sub] at h2
  have h3 : (o * conj z).re = (z * conj o).re := by
    have e : conj (o * conj z) = z * conj o := by
      rw [map_mul, Complex.conj_conj, mul_comm]
    rw [← Complex.conj_re (o * conj z), e]
  linarith

/-- A point on the tangent line at the unit `p` and on the circle through `0`
centered at `o` satisfies a quadratic equation. -/
lemma quad_of_mem_line_circle {z p o : ℂ} (hp : ‖p‖ = 1)
    (hline : (z * conj p).re = 1) (hcirc : normSq z = 2 * (z * conj o).re) :
    z ^ 2 = (2 * p + o - conj o * p ^ 2) * z - 2 * p * o := by
  have hpp : conj p * p = 1 := conj_unit_mul hp
  have hl : z * conj p + conj z * p = 2 := by
    have h := Complex.add_conj (z * conj p)
    rw [hline, map_mul, Complex.conj_conj] at h
    exact_mod_cast h
  have hl2 : conj z * p ^ 2 = 2 * p - z := by
    linear_combination hl * p - z * hpp
  have hc : z * conj z = z * conj o + conj z * o := by
    have h1 : z * conj z = (normSq z : ℂ) := Complex.mul_conj z
    have h := Complex.add_conj (z * conj o)
    rw [map_mul, Complex.conj_conj, ← hcirc] at h
    exact h1.trans h.symm
  linear_combination z * hl2 - o * hl2 - hc * p ^ 2

/-- Vieta: the product of the two intersection points of a line and a circle. -/
lemma mul_eq_of_quad {z1 z2 S P : ℂ} (h1 : z1 ^ 2 = S * z1 - P)
    (h2 : z2 ^ 2 = S * z2 - P) (hne : z1 ≠ z2) : z1 * z2 = P := by
  have key : (z1 - z2) * (z1 * z2 - P) = 0 := by
    linear_combination h1 * z2 - h2 * z1
  rcases mul_eq_zero.mp key with h | h
  · exact absurd (sub_eq_zero.mp h) hne
  · exact sub_eq_zero.mp h

/-- Pythagoras at the contact point. -/
lemma normSq_sub_eq_of_unit {z u : ℂ} (hu : ‖u‖ = 1) (h : (z * conj u).re = 1) :
    normSq (z - u) = normSq z - 1 := by
  rw [normSq_sub, normSq_eq_one_of_norm_eq_one hu, h]
  ring

/-- Two equal hypotenuses give equal legs. -/
lemma dist_eq_of_normSq_sub_eq {z1 z2 u1 u2 : ℂ} (h1 : normSq (z1 - u1) = normSq z1 - 1)
    (h2 : normSq (z2 - u2) = normSq z2 - 1) (h : ‖z1‖ = ‖z2‖) :
    dist z1 u1 = dist z2 u2 := by
  have hsq : ‖z1 - u1‖ ^ 2 = ‖z2 - u2‖ ^ 2 := by
    have e1 : ‖z1 - u1‖ ^ 2 = normSq (z1 - u1) := by
      rw [sq, norm_mul_self_eq_normSq]
    have e2 : ‖z2 - u2‖ ^ 2 = normSq (z2 - u2) := by
      rw [sq, norm_mul_self_eq_normSq]
    have e3 : ‖z1‖ ^ 2 = normSq z1 := by
      rw [sq, norm_mul_self_eq_normSq]
    have e4 : ‖z2‖ ^ 2 = normSq z2 := by
      rw [sq, norm_mul_self_eq_normSq]
    rw [e1, e2, h1, h2, ← e3, ← e4, h]
  rw [dist_eq_norm, dist_eq_norm]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

snip end

problem imo2021_p4
    (A B C D X Y Z T O p q r s : ℂ)
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hr : ‖r‖ = 1) (hs : ‖s‖ = 1)
    (hps : p ≠ s) (hqr : q ≠ r) (hps0 : p + s ≠ 0) (hqr0 : q + r ≠ 0)
    (hAB : A ≠ B) (hBC : B ≠ C) (hDA : D ≠ A) (hDC : D ≠ C)
    (hAp : ((A - p) * conj p).re = 0) (hBp : ((B - p) * conj p).re = 0)
    (hBq : ((B - q) * conj q).re = 0) (hCq : ((C - q) * conj q).re = 0)
    (hCr : ((C - r) * conj r).re = 0) (hDr : ((D - r) * conj r).re = 0)
    (hDs : ((D - s) * conj s).re = 0) (hAs : ((A - s) * conj s).re = 0)
    (hpAB : Wbtw ℝ A p B) (hqBC : Wbtw ℝ B q C) (hrCD : Wbtw ℝ C r D)
    (hsDA : Wbtw ℝ D s A)
    (hBAX : Wbtw ℝ B A X) (hBCZ : Wbtw ℝ B C Z) (hADY : Wbtw ℝ A D Y)
    (hCDT : Wbtw ℝ C D T)
    (hXA : X ≠ A) (hYA : Y ≠ A) (hZC : Z ≠ C) (hTC : T ≠ C)
    (hOA : ‖O - A‖ = ‖O‖) (hOC : ‖O - C‖ = ‖O‖) (hOX : ‖O - X‖ = ‖O‖)
    (hOY : ‖O - Y‖ = ‖O‖) (hOZ : ‖O - Z‖ = ‖O‖) (hOT : ‖O - T‖ = ‖O‖) :
    dist A D + dist D T + dist T X + dist X A =
      dist C D + dist D Y + dist Y Z + dist Z C := by
  -- On the four tangent lines, every relevant point `z` satisfies
  -- `(z * conj u).re = 1` for the corresponding contact unit `u`.
  have hAp1 : (A * conj p).re = 1 := re_mul_conj_eq_one_of_perp hp hAp
  have hAs1 : (A * conj s).re = 1 := re_mul_conj_eq_one_of_perp hs hAs
  have hCq1 : (C * conj q).re = 1 := re_mul_conj_eq_one_of_perp hq hCq
  have hCr1 : (C * conj r).re = 1 := re_mul_conj_eq_one_of_perp hr hCr
  have hDr1 : (D * conj r).re = 1 := re_mul_conj_eq_one_of_perp hr hDr
  have hDs1 : (D * conj s).re = 1 := re_mul_conj_eq_one_of_perp hs hDs
  have hXp1 : (X * conj p).re = 1 :=
    re_mul_conj_eq_one_of_perp hp (perp_of_wbtw hAp hBp hBAX hAB)
  have hZq1 : (Z * conj q).re = 1 :=
    re_mul_conj_eq_one_of_perp hq (perp_of_wbtw hCq hBq hBCZ (Ne.symm hBC))
  have hYs1 : (Y * conj s).re = 1 :=
    re_mul_conj_eq_one_of_perp hs (perp_of_wbtw hDs hAs hADY hDA)
  have hTr1 : (T * conj r).re = 1 :=
    re_mul_conj_eq_one_of_perp hr (perp_of_wbtw hDr hCr hCDT hDC)
  -- The vertices A and C are intersections of two tangent lines.
  have hA : A = 2 * p * s / (p + s) := tangent_inter hp hs hps hps0 hAp1 hAs1
  have hC : C = 2 * q * r / (q + r) := tangent_inter hq hr hqr hqr0 hCq1 hCr1
  have hAn : A ≠ 0 := by
    rw [hA]
    exact div_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero (unit_ne_zero hp))
      (unit_ne_zero hs)) hps0
  have hCn : C ≠ 0 := by
    rw [hC]
    exact div_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero (unit_ne_zero hq))
      (unit_ne_zero hr)) hqr0
  -- Circle conditions in `normSq` form.
  have cA : normSq A = 2 * (A * conj O).re := normSq_eq_two_re_of_dist hOA
  have cC : normSq C = 2 * (C * conj O).re := normSq_eq_two_re_of_dist hOC
  have cX : normSq X = 2 * (X * conj O).re := normSq_eq_two_re_of_dist hOX
  have cY : normSq Y = 2 * (Y * conj O).re := normSq_eq_two_re_of_dist hOY
  have cZ : normSq Z = 2 * (Z * conj O).re := normSq_eq_two_re_of_dist hOZ
  have cT : normSq T = 2 * (T * conj O).re := normSq_eq_two_re_of_dist hOT
  -- Vieta products: A·X = 2pO etc.
  have vAX : A * X = 2 * p * O :=
    mul_eq_of_quad (quad_of_mem_line_circle hp hAp1 cA)
      (quad_of_mem_line_circle hp hXp1 cX) (Ne.symm hXA)
  have vAY : A * Y = 2 * s * O :=
    mul_eq_of_quad (quad_of_mem_line_circle hs hAs1 cA)
      (quad_of_mem_line_circle hs hYs1 cY) (Ne.symm hYA)
  have vCZ : C * Z = 2 * q * O :=
    mul_eq_of_quad (quad_of_mem_line_circle hq hCq1 cC)
      (quad_of_mem_line_circle hq hZq1 cZ) (Ne.symm hZC)
  have vCT : C * T = 2 * r * O :=
    mul_eq_of_quad (quad_of_mem_line_circle hr hCr1 cC)
      (quad_of_mem_line_circle hr hTr1 cT) (Ne.symm hTC)
  -- Explicit formulas for X, Y, Z, T.
  have hX : X = 2 * p * O / A := by
    rw [eq_div_iff_mul_eq hAn, mul_comm X A]
    exact vAX
  have hY : Y = 2 * s * O / A := by
    rw [eq_div_iff_mul_eq hAn, mul_comm Y A]
    exact vAY
  have hZ : Z = 2 * q * O / C := by
    rw [eq_div_iff_mul_eq hCn, mul_comm Z C]
    exact vCZ
  have hT : T = 2 * r * O / C := by
    rw [eq_div_iff_mul_eq hCn, mul_comm T C]
    exact vCT
  -- Chord equalities from I: XI = YI and TI = ZI.
  have hXI : ‖X‖ = 2 * ‖O‖ / ‖A‖ := by
    rw [hX, norm_div, norm_mul, norm_mul, hp]
    simp
  have hYI : ‖Y‖ = 2 * ‖O‖ / ‖A‖ := by
    rw [hY, norm_div, norm_mul, norm_mul, hs]
    simp
  have hZI : ‖Z‖ = 2 * ‖O‖ / ‖C‖ := by
    rw [hZ, norm_div, norm_mul, norm_mul, hq]
    simp
  have hTI : ‖T‖ = 2 * ‖O‖ / ‖C‖ := by
    rw [hT, norm_div, norm_mul, norm_mul, hr]
    simp
  have hXY : ‖X‖ = ‖Y‖ := by rw [hXI, hYI]
  have hTZ : ‖T‖ = ‖Z‖ := by rw [hTI, hZI]
  -- Pythagorean right triangles at the contact points.
  have eXP_SY : dist X p = dist Y s :=
    dist_eq_of_normSq_sub_eq (normSq_sub_eq_of_unit hp hXp1)
      (normSq_sub_eq_of_unit hs hYs1) hXY
  have eRT_ZQ : dist T r = dist Z q :=
    dist_eq_of_normSq_sub_eq (normSq_sub_eq_of_unit hr hTr1)
      (normSq_sub_eq_of_unit hq hZq1) hTZ
  have eAP_AS : dist A p = dist A s :=
    dist_eq_of_normSq_sub_eq (normSq_sub_eq_of_unit hp hAp1)
      (normSq_sub_eq_of_unit hs hAs1) rfl
  have eCQ_CR : dist C q = dist C r :=
    dist_eq_of_normSq_sub_eq (normSq_sub_eq_of_unit hq hCq1)
      (normSq_sub_eq_of_unit hr hCr1) rfl
  have eDR_DS : dist D r = dist D s :=
    dist_eq_of_normSq_sub_eq (normSq_sub_eq_of_unit hr hDr1)
      (normSq_sub_eq_of_unit hs hDs1) rfl
  -- The chord equality TX = YZ.
  have eTX_YZ : dist T X = dist Y Z := by
    rw [dist_eq_norm, dist_eq_norm, hT, hX, hY, hZ]
    have e1 : 2 * r * O / C - 2 * p * O / A = 2 * O * (r * A - p * C) / (C * A) := by
      field_simp
    have e2 : 2 * s * O / A - 2 * q * O / C = 2 * O * (s * C - q * A) / (A * C) := by
      field_simp
    rw [e1, e2, norm_div, norm_div]
    have eAC : ‖C * A‖ = ‖A * C‖ := by rw [mul_comm]
    rw [eAC]
    have e3 : r * A - p * C = 2 * p * r * (s * r - p * q) / ((p + s) * (q + r)) := by
      rw [hA, hC]
      field_simp
      ring
    have e4 : s * C - q * A = 2 * q * s * (r * s - p * q) / ((p + s) * (q + r)) := by
      rw [hA, hC]
      field_simp
      ring
    rw [e3, e4]
    simp [hp, hq, hr, hs, mul_comm r s]
  -- Bookkeeping along the sides.
  have eAD : dist A D = dist A s + dist s D := by
    have h := hsDA.dist_add_dist
    rw [dist_comm A D, dist_comm A s, dist_comm s D]
    linarith [h]
  have eCD : dist C D = dist C r + dist r D := hrCD.dist_add_dist.symm
  have eXP : dist X p = dist X A + dist A p :=
    (Wbtw.trans_right_left hBAX.symm hpAB).dist_add_dist.symm
  have eRT : dist r T = dist r D + dist D T :=
    (Wbtw.trans_left_right hCDT hrCD).dist_add_dist.symm
  have eSY : dist s Y = dist s D + dist D Y :=
    (Wbtw.trans_left_right hADY hsDA.symm).dist_add_dist.symm
  have eQZ : dist q Z = dist q C + dist C Z :=
    (Wbtw.trans_left_right hBCZ hqBC).dist_add_dist.symm
  -- Final combination.
  have h1 : dist Y s = dist s Y := dist_comm Y s
  have h2 : dist Z q = dist q Z := dist_comm Z q
  have h3 : dist Z C = dist C Z := dist_comm Z C
  have h4 : dist D s = dist s D := dist_comm D s
  have h5 : dist D r = dist r D := dist_comm D r
  have h6 : dist T r = dist r T := dist_comm T r
  have h7 : dist q C = dist C q := dist_comm q C
  linarith [eAD, eCD, eXP, eRT, eSY, eQZ, eAP_AS, eCQ_CR, eDR_DS, eXP_SY, eRT_ZQ,
    eTX_YZ, h1, h2, h3, h4, h5, h6, h7]

end Imo2021P4
