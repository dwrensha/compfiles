/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Convex.StrictConvexBetween
public import Mathlib.Analysis.InnerProductSpace.OfNorm
public import Mathlib.Analysis.Normed.Affine.Convex
public import Mathlib.Data.Real.Sign
public import Mathlib.FieldTheory.Perfect
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# USA Mathematical Olympiad 2016, Problem 5

An equilateral pentagon AMNPQ is inscribed in triangle ABC such that M ∈ AB,
Q ∈ AC, and N, P ∈ BC. Let S be the intersection of MN and PQ. Denote by ℓ
the angle bisector of ∠MSQ.

Prove that OI is parallel to ℓ, where O is the circumcenter of triangle ABC,
and I is the incenter of triangle ABC.
-/

namespace Usa2016P5

snip begin

/-!
## The scalar cross product in the complex plane

We work with points in `ℂ`, the complex plane, which is a two-dimensional
real inner product space.  The scalar cross product `cr u v` is twice the
signed area of the parallelogram spanned by `u` and `v`.
-/

/-- The scalar cross product of two complex numbers:
twice the signed area of the parallelogram they span. -/
def cr (u v : ℂ) : ℝ := (star u * v).im

lemma star_re (z : ℂ) : (star z).re = z.re := rfl
lemma star_im (z : ℂ) : (star z).im = -z.im := rfl

lemma mul_star_self (z : ℂ) : z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.ext_iff]
  constructor
  · simp only [Complex.mul_re, star_re, star_im, Complex.ofReal_re]
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  · simp only [Complex.mul_im, star_re, star_im, Complex.ofReal_im]
    ring

lemma cr_compute (u v : ℂ) : cr u v = u.re * v.im - u.im * v.re := by
  simp [cr, Complex.mul_im]; ring

lemma cr_zero_left (v : ℂ) : cr 0 v = 0 := by rw [cr_compute]; simp
lemma cr_zero_right (u : ℂ) : cr u 0 = 0 := by rw [cr_compute]; simp
lemma cr_self (u : ℂ) : cr u u = 0 := by rw [cr_compute]; ring
lemma cr_antisymm (u v : ℂ) : cr u v = -cr v u := by rw [cr_compute, cr_compute]; ring
lemma cr_neg_left (u v : ℂ) : cr (-u) v = -cr u v := by
  rw [cr_compute, cr_compute]; simp; ring
lemma cr_neg_right (u v : ℂ) : cr u (-v) = -cr u v := by
  rw [cr_compute, cr_compute]; simp; ring
lemma cr_add_left (u₁ u₂ v : ℂ) : cr (u₁ + u₂) v = cr u₁ v + cr u₂ v := by
  rw [cr_compute, cr_compute, cr_compute]; simp; ring
lemma cr_add_right (u v₁ v₂ : ℂ) : cr u (v₁ + v₂) = cr u v₁ + cr u v₂ := by
  rw [cr_compute, cr_compute, cr_compute]; simp; ring
lemma cr_sub_left (u₁ u₂ v : ℂ) : cr (u₁ - u₂) v = cr u₁ v - cr u₂ v := by
  rw [cr_compute, cr_compute, cr_compute]; simp; ring
lemma cr_sub_right (u v₁ v₂ : ℂ) : cr u (v₁ - v₂) = cr u v₁ - cr u v₂ := by
  rw [cr_compute, cr_compute, cr_compute]; simp; ring
lemma cr_smul_left (r : ℝ) (u v : ℂ) : cr (r • u) v = r * cr u v := by
  rw [cr_compute, cr_compute]; simp [Complex.real_smul]; ring
lemma cr_smul_right (r : ℝ) (u v : ℂ) : cr u (r • v) = r * cr u v := by
  rw [cr_compute, cr_compute]; simp [Complex.real_smul]; ring
lemma cr_I_right (u v : ℂ) : cr u (Complex.I * v) = (star u * v).re := by
  rw [cr_compute]; simp [Complex.mul_re, Complex.mul_im]

/-- In the plane, vanishing cross product means parallel. -/
lemma exists_smul_of_cr_eq_zero {p q : ℂ} (hp : p ≠ 0) (h : cr p q = 0) :
    ∃ t : ℝ, q = t • p := by
  refine ⟨(star p * q).re / ‖p‖ ^ 2, ?_⟩
  have h' : (star p * q).im = 0 := h
  have h1 : star p * q = (((star p * q).re : ℝ) : ℂ) := by
    rw [Complex.ext_iff]
    exact ⟨by simp, by simpa using h'⟩
  have h2 : ((‖p‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.mpr hp)
  have h3 : q * ((‖p‖ ^ 2 : ℝ) : ℂ) = ((star p * q).re : ℂ) * p := by
    calc q * ((‖p‖ ^ 2 : ℝ) : ℂ) = q * (p * star p) := by rw [mul_star_self]
      _ = p * (star p * q) := by ring
      _ = p * ((star p * q).re : ℂ) := by rw [← h1]
      _ = ((star p * q).re : ℂ) * p := by ring
  rw [Complex.real_smul]
  rw [show (((star p * q).re / ‖p‖ ^ 2 : ℝ) : ℂ) * p =
      ((star p * q).re : ℂ) * p / ((‖p‖ ^ 2 : ℝ) : ℂ) by push_cast; ring]
  rw [eq_div_iff h2]
  exact h3

/-!
## Betweenness and collinearity infrastructure
-/

/-- Weak betweenness on a line in the complex plane, in terms of a parameter. -/
lemma wbtw_iff_exists {x y z : ℂ} :
    Wbtw ℝ x y z ↔ ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ y = x + t • (z - x) := by
  rw [Wbtw, affineSegment]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht.1, ht.2, by rw [AffineMap.lineMap_apply_module']; ring⟩
  · rintro ⟨t, ht0, ht1, rfl⟩
    exact ⟨t, ⟨ht0, ht1⟩, by rw [AffineMap.lineMap_apply_module']; ring⟩

lemma wbtw_sub_const {x y z : ℂ} (h : Wbtw ℝ x y z) (c : ℂ) :
    Wbtw ℝ (x - c) (y - c) (z - c) := by
  rw [wbtw_iff_exists] at h ⊢
  obtain ⟨t, ht0, ht1, rfl⟩ := h
  exact ⟨t, ht0, ht1, by simp [Complex.real_smul]; ring⟩

lemma exists_eq_add_smul_of_mem_affineSpan_pair {m n s : ℂ}
    (h : s ∈ affineSpan ℝ ({m, n} : Set ℂ)) : ∃ t : ℝ, s = m + t • (n - m) := by
  have hmem : s -ᵥ m ∈ vectorSpan ℝ ({m, n} : Set ℂ) := by
    rw [← direction_affineSpan]
    exact AffineSubspace.vsub_mem_direction h (left_mem_affineSpan_pair ℝ m n)
  rw [vectorSpan_pair] at hmem
  obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hmem
  simp only [vsub_eq_sub] at hk
  refine ⟨-k, ?_⟩
  calc s = m + (s - m) := by ring
    _ = m + -k • (n - m) := by rw [← hk]; module

lemma mem_affineSpan_pair_sub_const {m n s : ℂ}
    (h : s ∈ affineSpan ℝ ({m, n} : Set ℂ)) (c : ℂ) :
    s - c ∈ affineSpan ℝ ({m - c, n - c} : Set ℂ) := by
  obtain ⟨t, rfl⟩ := exists_eq_add_smul_of_mem_affineSpan_pair h
  have hmem := AffineMap.lineMap_mem_affineSpan_pair (r := t) (p₁ := m - c) (p₂ := n - c)
  rw [AffineMap.lineMap_apply_module'] at hmem
  have e : m + t • (n - m) - c = t • ((n - c) - (m - c)) + (m - c) := by
    simp [Complex.real_smul]; ring
  rwa [e]

lemma dist_sub_const (x y c : ℂ) : dist (x - c) (y - c) = dist x y := by
  rw [dist_eq_norm, dist_eq_norm]
  congr 1
  ring

lemma cr_ofReal_mul_left (r : ℝ) (u v : ℂ) : cr ((r : ℂ) * u) v = r * cr u v := by
  rw [← Complex.real_smul]; exact cr_smul_left r u v

lemma cr_ofReal_mul_right (r : ℝ) (u v : ℂ) : cr u ((r : ℂ) * v) = r * cr u v := by
  rw [← Complex.real_smul]; exact cr_smul_right r u v

/-- If `A` lies on the segment `BC`, the signed area of the triangle is zero. -/
lemma cr_eq_zero_of_wbtw {A B C : ℂ} (h : Wbtw ℝ B A C) : cr (C - A) (B - A) = 0 := by
  rw [wbtw_iff_exists] at h
  obtain ⟨t, ht0, ht1, rfl⟩ := h
  have e1 : C - (B + t • (C - B)) = (1 - t) • (C - B) := by module
  have e2 : B - (B + t • (C - B)) = (-t) • (C - B) := by module
  rw [e1, e2, cr_smul_left, cr_smul_right, cr_self, mul_zero, mul_zero]

/-- Extract the parameters of two points on a segment with their relative order. -/
lemma wbtw_chain_params {B C N P : ℂ} (hBC : B ≠ C)
    (hN : Wbtw ℝ B N C) (hP : Wbtw ℝ B P C) (hNP : Wbtw ℝ B N P) :
    ∃ tN tP : ℝ, 0 ≤ tN ∧ tN ≤ tP ∧ tP ≤ 1 ∧ N = B + tN • (C - B) ∧
      P = B + tP • (C - B) := by
  obtain ⟨tN, htN0, htN1, htNeq⟩ := wbtw_iff_exists.mp hN
  obtain ⟨tP, htP0, htP1, htPeq⟩ := wbtw_iff_exists.mp hP
  obtain ⟨τ, hτ0, hτ1, hτeq⟩ := wbtw_iff_exists.mp hNP
  refine ⟨tN, tP, htN0, ?_, htP1, htNeq, htPeq⟩
  have hCB : C - B ≠ 0 := sub_ne_zero.mpr hBC.symm
  have ht : tN = τ * tP := by
    have e1 : N - B = tN • (C - B) := by rw [htNeq]; module
    have e2 : P - B = tP • (C - B) := by rw [htPeq]; module
    have e3 : N - B = τ • (P - B) := by rw [hτeq]; module
    have e4 : tN • (C - B) = (τ * tP) • (C - B) := by
      rw [← e1, e3, e2]
      module
    have e5 : (tN - τ * tP) • (C - B) = 0 := by
      linear_combination (norm := module) e4
    rcases smul_eq_zero.mp e5 with h1 | h2
    · linarith
    · exact absurd h2 hCB
  nlinarith [hτ0, hτ1, htP0]

/-- The configuration of the problem cannot degenerate to the case where the
lines `MN` and `PQ` are parallel (and hence, meeting at `S`, coincide). -/
lemma coll {A B C M N P Q S : ℂ}
    (hK : cr (C - A) (B - A) ≠ 0)
    (hM : Wbtw ℝ A M B) (hQ : Wbtw ℝ A Q C)
    (hN : Wbtw ℝ B N C) (hP : Wbtw ℝ B P C) (hNP : Wbtw ℝ B N P)
    (hAM : dist A M = dist M N) (hMN : dist M N = dist N P)
    (hNPQ : dist N P = dist P Q) (hPQA : dist P Q = dist Q A)
    (hS1 : S ∈ affineSpan ℝ ({M, N} : Set ℂ)) (hS2 : S ∈ affineSpan ℝ ({P, Q} : Set ℂ))
    (hpar : cr (N - M) (P - Q) = 0) : False := by
  have hBC : B ≠ C := by
    intro h
    rw [h] at hK
    exact hK (cr_self _)
  have hCA : C ≠ A := by
    intro h
    rw [h] at hK
    exact hK (by rw [sub_self, cr_zero_left])
  have hAB : A ≠ B := by
    intro h
    rw [h] at hK
    exact hK (by rw [sub_self, cr_zero_right])
  obtain ⟨μ, hμ0, hμ1, hμeq⟩ := wbtw_iff_exists.mp hM
  obtain ⟨ν, hν0, hν1, hνeq⟩ := wbtw_iff_exists.mp hQ
  obtain ⟨tN, tP, htN0, htNP, htP1, htNeq, htPeq⟩ := wbtw_chain_params hBC hN hP hNP
  have hs : 0 < dist A M := by
    rcases eq_or_lt_of_le (dist_nonneg : 0 ≤ dist A M) with hs0 | hs0
    · exfalso
      have hMA : M = A := (dist_eq_zero.mp hs0.symm).symm
      have hNA : N = A := by
        have hMN0 : dist M N = 0 := by rw [← hAM]; exact hs0.symm
        have hMN' : M = N := dist_eq_zero.mp hMN0
        rw [hMA] at hMN'
        exact hMN'.symm
      have h0 : cr (C - A) (B - A) = 0 := cr_eq_zero_of_wbtw (by rwa [hNA] at hN)
      exact hK h0
    · exact hs0
  have hNM : N ≠ M := by
    intro h
    rw [h, dist_self] at hAM
    linarith [hs, hAM]
  have hNeqP : N ≠ P := by
    intro h
    rw [h] at hAM hMN
    rw [dist_self] at hMN
    linarith [hs, hAM, hMN]
  obtain ⟨ρ, hρ⟩ := exists_smul_of_cr_eq_zero (sub_ne_zero.mpr hNM) hpar
  obtain ⟨t₁, ht₁⟩ := exists_eq_add_smul_of_mem_affineSpan_pair hS1
  obtain ⟨t₂', ht₂'⟩ := exists_eq_add_smul_of_mem_affineSpan_pair hS2
  set t₂ := 1 - t₂' with ht₂def
  have ht₂ : S = Q + t₂ • (P - Q) := by
    rw [ht₂def]
    linear_combination (norm := module) ht₂'
  have hSeq : M + t₁ • (N - M) = Q + t₂ • (P - Q) := ht₁.symm.trans ht₂
  rw [hρ] at hSeq
  have hQlin : Q = M + (t₁ - t₂ * ρ) • (N - M) := by
    linear_combination (norm := module) hSeq.symm
  have hPQ : P = Q + ρ • (N - M) := by linear_combination (norm := module) hρ
  have hPlin : P = M + (t₁ - t₂ * ρ + ρ) • (N - M) := by
    linear_combination (norm := module) hPQ + hQlin
  have htPtN : tP - tN ≠ 0 := by
    intro h0
    apply hNeqP
    rw [htNeq, htPeq, show tP = tN by linarith]
  have hPN1 : P - N = (tP - tN) • (C - B) := by rw [htNeq, htPeq]; module
  have hPN2 : P - N = (t₁ - t₂ * ρ + ρ - 1) • (N - M) := by
    linear_combination (norm := module) hPlin
  have hcrNM : cr (C - B) (N - M) = 0 := by
    have e : (tP - tN) * cr (C - B) (N - M) = 0 := by
      have h0 : cr (P - N) (N - M) = 0 := by rw [hPN2, cr_smul_left, cr_self, mul_zero]
      rwa [hPN1, cr_smul_left] at h0
    rcases mul_eq_zero.mp e with h1 | h2
    · exact absurd h1 htPtN
    · exact h2
  have hMbc : cr (C - B) (M - B) = 0 := by
    have g1 : cr (C - B) (M - N) = 0 := by
      rw [show M - N = -(N - M) by ring, cr_neg_right, hcrNM, neg_zero]
    have g2 : cr (C - B) (N - B) = 0 := by
      rw [htNeq, show B + tN • (C - B) - B = tN • (C - B) by ring, cr_smul_right,
        cr_self, mul_zero]
    have e : M - B = (M - N) + (N - B) := by ring
    rw [e, cr_add_right, g1, g2, add_zero]
  have hQbc : cr (C - B) (Q - B) = 0 := by
    have g1 : cr (C - B) (Q - M) = 0 := by
      have hQM : Q - M = (t₁ - t₂ * ρ) • (N - M) := by
        linear_combination (norm := module) hQlin
      rw [hQM, cr_smul_right, hcrNM, mul_zero]
    have e : Q - B = (Q - M) + (M - B) := by ring
    rw [e, cr_add_right, g1, hMbc, add_zero]
  have hMB : M = B := by
    have h1 : (1 - μ) * cr (C - B) (A - B) = 0 := by
      rw [hμeq] at hMbc
      rwa [show A + μ • (B - A) - B = (1 - μ) • (A - B) by module, cr_smul_right] at hMbc
    have hne : cr (C - B) (A - B) ≠ 0 := by
      have e : cr (C - B) (A - B) = -cr (C - A) (B - A) := by
        simp only [cr_compute, Complex.sub_re, Complex.sub_im]
        ring
      rw [e]
      exact neg_ne_zero.mpr hK
    rcases mul_eq_zero.mp h1 with h1' | h2
    · have hμ1' : μ = 1 := by linarith
      rw [hμeq, hμ1', one_smul]
      ring
    · exact absurd h2 hne
  have hQC : Q = C := by
    rw [hνeq] at hQbc
    rw [show A + ν • (C - A) - B = (A - B) + ν • (C - A) by module, cr_add_right,
      cr_smul_right] at hQbc
    have e1 : cr (C - B) (A - B) = -cr (C - A) (B - A) := by
      simp only [cr_compute, Complex.sub_re, Complex.sub_im]
      ring
    have e2 : cr (C - B) (C - A) = cr (C - A) (B - A) := by
      simp only [cr_compute, Complex.sub_re, Complex.sub_im]
      ring
    rw [e1, e2] at hQbc
    have hν1' : ν = 1 := by
      have hz : (ν - 1) * cr (C - A) (B - A) = 0 := by
        rw [sub_mul, one_mul]
        linarith [hQbc]
      rcases mul_eq_zero.mp hz with h1 | h2
      · linarith
      · exact absurd h2 hK
    rw [hνeq, hν1', one_smul]
    ring
  have hα3 : dist B C = 3 * dist A M := by
    have h1 : dist B N + dist N P = dist B P := Wbtw.dist_add_dist hNP
    have h2 : dist B P + dist P C = dist B C := Wbtw.dist_add_dist hP
    have h3 : dist B N = dist M N := by rw [← hMB]
    have h4 : dist P C = dist P Q := by rw [← hQC]
    linarith [h1, h2, h3, hAM, hMN, hNPQ]
  have htri : dist B C < dist B A + dist A C := by
    rcases lt_or_eq_of_le (dist_triangle B A C) with h | h
    · exact h
    · exfalso
      exact hK (cr_eq_zero_of_wbtw (dist_add_dist_eq_iff.mp h.symm))
  have h2s : dist B A + dist A C = 2 * dist A M := by
    have g1 : dist B A = dist A M := by rw [← hMB, dist_comm]
    have g2 : dist A C = dist A M := by
      rw [← hQC, dist_comm A Q, ← hPQA, ← hNPQ, ← hMN, ← hAM]
    linarith [g1, g2]
  rw [hα3] at htri
  linarith [htri, h2s, hs]

/-!
## The crux: an algebraic identity for the incenter direction
-/

/-- Auxiliary "arc midpoint" direction associated to the side from `p` to `q`
of a triangle inscribed in a circle centered at the origin. -/
noncomputable def arcMid (p q : ℂ) : ℂ := Complex.I * (p - q) / dist p q

/-- `star` fixes real scalars. -/
private lemma star_ofReal' (r : ℝ) : star (r : ℂ) = (r : ℂ) := by
  rw [Complex.ext_iff]
  exact ⟨rfl, neg_zero⟩

/-- Multiplication by a real scalar cancels division by the same real. -/
private lemma ofReal_mul_div_real (w : ℂ) {r : ℝ} (hr : r ≠ 0) : (r : ℂ) * (w / r) = w := by
  rw [Complex.div_ofReal, Complex.ext_iff]
  constructor
  · rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    show r * (w.re / r) - 0 * (w.im / r) = w.re
    field_simp
    ring
  · rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    show r * (w.im / r) + 0 * (w.re / r) = w.im
    field_simp
    ring

/-- The crux of the problem (an algebraic form of the fact that the incenter
of a triangle inscribed in a circle centered at the origin is the sum of the
midpoints of the arcs): the sum of the three arc-midpoint directions is
parallel to the incenter direction. -/
lemma crux {a b c : ℂ} (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a)
    (hRB : ‖a‖ = ‖b‖) (hRC : ‖b‖ = ‖c‖) :
    cr (arcMid b c + arcMid c a + arcMid a b)
      (dist b c • a + dist c a • b + dist a b • c) = 0 := by
  -- R := ‖a‖ is positive (otherwise a = b = c = 0).
  have hRne : ‖a‖ ≠ 0 := by
    intro h
    have ha0 : a = 0 := norm_eq_zero.mp h
    have hb0 : b = 0 := norm_eq_zero.mp (hRB ▸ h)
    exact hab (ha0.trans hb0.symm)
  have hRneC : (‖a‖ : ℂ) ≠ 0 := by exact_mod_cast hRne
  have haC : a ≠ 0 := by
    intro ha
    exact hRne (by rw [ha]; exact norm_zero)
  have hbC : b ≠ 0 := by
    intro hb
    exact hRne (by rw [hRB, hb]; exact norm_zero)
  have hcC : c ≠ 0 := by
    intro hc
    exact hRne (by rw [hRB.trans hRC, hc]; exact norm_zero)
  have hαne : dist b c ≠ 0 := dist_ne_zero.mpr hbc
  have hβne : dist c a ≠ 0 := dist_ne_zero.mpr hca
  have hγne : dist a b ≠ 0 := dist_ne_zero.mpr hab
  have hαpos : 0 < dist b c := dist_pos.mpr hbc
  have hβpos : 0 < dist c a := dist_pos.mpr hca
  have hγpos : 0 < dist a b := dist_pos.mpr hab
  have hαneC : ((dist b c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hαne
  have hβneC : ((dist c a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hβne
  have hγneC : ((dist a b : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hγne
  -- `star a = R² / a` etc.
  have haa : a * star a = (‖a‖ : ℂ) ^ 2 := by
    have h := mul_star_self a
    rwa [Complex.ofReal_pow] at h
  have hbb : b * star b = (‖a‖ : ℂ) ^ 2 := by
    have h := mul_star_self b
    rwa [← hRB, Complex.ofReal_pow] at h
  have hcc : c * star c = (‖a‖ : ℂ) ^ 2 := by
    have h := mul_star_self c
    have h1 : ‖c‖ = ‖a‖ := hRC.symm.trans hRB.symm
    rwa [h1, Complex.ofReal_pow] at h
  have hstara : star a = (‖a‖ : ℂ) ^ 2 / a := by
    rw [eq_div_iff haC, mul_comm]; exact haa
  have hstarb : star b = (‖a‖ : ℂ) ^ 2 / b := by
    rw [eq_div_iff hbC, mul_comm]; exact hbb
  have hstarc : star c = (‖a‖ : ℂ) ^ 2 / c := by
    rw [eq_div_iff hcC, mul_comm]; exact hcc
  -- Abbreviations for the three arc-midpoint directions.
  set x := arcMid b c with hx_def
  set y := arcMid c a with hy_def
  set z := arcMid a b with hz_def
  -- Unit-modulus facts and `star x = x⁻¹` etc.
  have hαx : ((dist b c : ℝ) : ℂ) * x = Complex.I * (b - c) := by
    rw [hx_def]; unfold arcMid; exact ofReal_mul_div_real _ hαne
  have hβx : ((dist c a : ℝ) : ℂ) * y = Complex.I * (c - a) := by
    rw [hy_def]; unfold arcMid; exact ofReal_mul_div_real _ hβne
  have hγx : ((dist a b : ℝ) : ℂ) * z = Complex.I * (a - b) := by
    rw [hz_def]; unfold arcMid; exact ofReal_mul_div_real _ hγne
  have hxC : x = Complex.I * (b - c) / ((dist b c : ℝ) : ℂ) := by
    rw [← hαx]; exact (mul_div_cancel_left₀ _ hαneC).symm
  have hyC : y = Complex.I * (c - a) / ((dist c a : ℝ) : ℂ) := by
    rw [← hβx]; exact (mul_div_cancel_left₀ _ hβneC).symm
  have hzC : z = Complex.I * (a - b) / ((dist a b : ℝ) : ℂ) := by
    rw [← hγx]; exact (mul_div_cancel_left₀ _ hγneC).symm
  have hx2 : x ^ 2 = -(b - c) ^ 2 / ((dist b c : ℝ) : ℂ) ^ 2 := by
    rw [hxC, div_pow, mul_pow, Complex.I_sq]; ring
  have hy2 : y ^ 2 = -(c - a) ^ 2 / ((dist c a : ℝ) : ℂ) ^ 2 := by
    rw [hyC, div_pow, mul_pow, Complex.I_sq]; ring
  have hz2 : z ^ 2 = -(a - b) ^ 2 / ((dist a b : ℝ) : ℂ) ^ 2 := by
    rw [hzC, div_pow, mul_pow, Complex.I_sq]; ring
  have hx_norm : ‖x‖ = 1 := by
    have h1 : ‖((dist b c : ℝ) : ℂ) * x‖ = ‖Complex.I * (b - c)‖ := by rw [hαx]
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, ← dist_eq_norm, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hαpos] at h1
    have h2 : dist b c * ‖x‖ = dist b c * 1 := by rw [h1, mul_one]
    exact mul_left_cancel₀ hαne h2
  have hy_norm : ‖y‖ = 1 := by
    have h1 : ‖((dist c a : ℝ) : ℂ) * y‖ = ‖Complex.I * (c - a)‖ := by rw [hβx]
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, ← dist_eq_norm, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hβpos] at h1
    have h2 : dist c a * ‖y‖ = dist c a * 1 := by rw [h1, mul_one]
    exact mul_left_cancel₀ hβne h2
  have hz_norm : ‖z‖ = 1 := by
    have h1 : ‖((dist a b : ℝ) : ℂ) * z‖ = ‖Complex.I * (a - b)‖ := by rw [hγx]
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, ← dist_eq_norm, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hγpos] at h1
    have h2 : dist a b * ‖z‖ = dist a b * 1 := by rw [h1, mul_one]
    exact mul_left_cancel₀ hγne h2
  have hx_unit : x * star x = 1 := by
    have h := mul_star_self x
    rwa [hx_norm, one_pow, Complex.ofReal_one] at h
  have hy_unit : y * star y = 1 := by
    have h := mul_star_self y
    rwa [hy_norm, one_pow, Complex.ofReal_one] at h
  have hz_unit : z * star z = 1 := by
    have h := mul_star_self z
    rwa [hz_norm, one_pow, Complex.ofReal_one] at h
  have hx_ne : x ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hx_unit; exact zero_ne_one hx_unit
  have hy_ne : y ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hy_unit; exact zero_ne_one hy_unit
  have hz_ne : z ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hz_unit; exact zero_ne_one hz_unit
  have hstarx : star x = x⁻¹ := eq_inv_of_mul_eq_one_right hx_unit
  have hstary : star y = y⁻¹ := eq_inv_of_mul_eq_one_right hy_unit
  have hstarz : star z = z⁻¹ := eq_inv_of_mul_eq_one_right hz_unit
  -- The squared-distance identities: `(dist p q)² = -R² (p - q)² / (p q)`.
  have hα2 : ((dist b c : ℝ) : ℂ) ^ 2 = -(‖a‖ : ℂ) ^ 2 * (b - c) ^ 2 / (b * c) := by
    have e : ((dist b c : ℝ) : ℂ) ^ 2 = (b - c) * star (b - c) := by
      rw [mul_star_self (b - c), ← dist_eq_norm, Complex.ofReal_pow]
    rw [e, star_sub, hstarb, hstarc]
    field_simp [hbC, hcC]
    ring
  have hβ2 : ((dist c a : ℝ) : ℂ) ^ 2 = -(‖a‖ : ℂ) ^ 2 * (c - a) ^ 2 / (c * a) := by
    have e : ((dist c a : ℝ) : ℂ) ^ 2 = (c - a) * star (c - a) := by
      rw [mul_star_self (c - a), ← dist_eq_norm, Complex.ofReal_pow]
    rw [e, star_sub, hstarc, hstara]
    field_simp [hcC, haC]
    ring
  have hγ2 : ((dist a b : ℝ) : ℂ) ^ 2 = -(‖a‖ : ℂ) ^ 2 * (a - b) ^ 2 / (a * b) := by
    have e : ((dist a b : ℝ) : ℂ) ^ 2 = (a - b) * star (a - b) := by
      rw [mul_star_self (a - b), ← dist_eq_norm, Complex.ofReal_pow]
    rw [e, star_sub, hstara, hstarb]
    field_simp [haC, hbC]
    ring
  -- `R² x² = b c` etc.
  have t1 : x ^ 2 * ((dist b c : ℝ) : ℂ) ^ 2 = -(b - c) ^ 2 := by
    rw [hx2]; exact div_mul_cancel₀ _ (pow_ne_zero 2 hαneC)
  have t2 : ((dist b c : ℝ) : ℂ) ^ 2 * (b * c) = -(‖a‖ : ℂ) ^ 2 * (b - c) ^ 2 := by
    rw [hα2]; exact div_mul_cancel₀ _ (mul_ne_zero hbC hcC)
  have e1 : (‖a‖ : ℂ) ^ 2 * x ^ 2 = b * c := by
    have hne : ((dist b c : ℝ) : ℂ) ^ 2 * (b * c) ≠ 0 :=
      mul_ne_zero (pow_ne_zero 2 hαneC) (mul_ne_zero hbC hcC)
    have h : ((dist b c : ℝ) : ℂ) ^ 2 * (b * c) * ((‖a‖ : ℂ) ^ 2 * x ^ 2)
        = ((dist b c : ℝ) : ℂ) ^ 2 * (b * c) * (b * c) := by
      calc ((dist b c : ℝ) : ℂ) ^ 2 * (b * c) * ((‖a‖ : ℂ) ^ 2 * x ^ 2)
          = (‖a‖ : ℂ) ^ 2 * (x ^ 2 * ((dist b c : ℝ) : ℂ) ^ 2) * (b * c) := by ring
        _ = (‖a‖ : ℂ) ^ 2 * (-(b - c) ^ 2) * (b * c) := by rw [t1]
        _ = (-(‖a‖ : ℂ) ^ 2 * (b - c) ^ 2) * (b * c) := by ring
        _ = ((dist b c : ℝ) : ℂ) ^ 2 * (b * c) * (b * c) := by rw [t2]
    exact mul_left_cancel₀ hne h
  have t1y : y ^ 2 * ((dist c a : ℝ) : ℂ) ^ 2 = -(c - a) ^ 2 := by
    rw [hy2]; exact div_mul_cancel₀ _ (pow_ne_zero 2 hβneC)
  have t2y : ((dist c a : ℝ) : ℂ) ^ 2 * (c * a) = -(‖a‖ : ℂ) ^ 2 * (c - a) ^ 2 := by
    rw [hβ2]; exact div_mul_cancel₀ _ (mul_ne_zero hcC haC)
  have e2 : (‖a‖ : ℂ) ^ 2 * y ^ 2 = c * a := by
    have hne : ((dist c a : ℝ) : ℂ) ^ 2 * (c * a) ≠ 0 :=
      mul_ne_zero (pow_ne_zero 2 hβneC) (mul_ne_zero hcC haC)
    have h : ((dist c a : ℝ) : ℂ) ^ 2 * (c * a) * ((‖a‖ : ℂ) ^ 2 * y ^ 2)
        = ((dist c a : ℝ) : ℂ) ^ 2 * (c * a) * (c * a) := by
      calc ((dist c a : ℝ) : ℂ) ^ 2 * (c * a) * ((‖a‖ : ℂ) ^ 2 * y ^ 2)
          = (‖a‖ : ℂ) ^ 2 * (y ^ 2 * ((dist c a : ℝ) : ℂ) ^ 2) * (c * a) := by ring
        _ = (‖a‖ : ℂ) ^ 2 * (-(c - a) ^ 2) * (c * a) := by rw [t1y]
        _ = (-(‖a‖ : ℂ) ^ 2 * (c - a) ^ 2) * (c * a) := by ring
        _ = ((dist c a : ℝ) : ℂ) ^ 2 * (c * a) * (c * a) := by rw [t2y]
    exact mul_left_cancel₀ hne h
  have t1z : z ^ 2 * ((dist a b : ℝ) : ℂ) ^ 2 = -(a - b) ^ 2 := by
    rw [hz2]; exact div_mul_cancel₀ _ (pow_ne_zero 2 hγneC)
  have t2z : ((dist a b : ℝ) : ℂ) ^ 2 * (a * b) = -(‖a‖ : ℂ) ^ 2 * (a - b) ^ 2 := by
    rw [hγ2]; exact div_mul_cancel₀ _ (mul_ne_zero haC hbC)
  have e3 : (‖a‖ : ℂ) ^ 2 * z ^ 2 = a * b := by
    have hne : ((dist a b : ℝ) : ℂ) ^ 2 * (a * b) ≠ 0 :=
      mul_ne_zero (pow_ne_zero 2 hγneC) (mul_ne_zero haC hbC)
    have h : ((dist a b : ℝ) : ℂ) ^ 2 * (a * b) * ((‖a‖ : ℂ) ^ 2 * z ^ 2)
        = ((dist a b : ℝ) : ℂ) ^ 2 * (a * b) * (a * b) := by
      calc ((dist a b : ℝ) : ℂ) ^ 2 * (a * b) * ((‖a‖ : ℂ) ^ 2 * z ^ 2)
          = (‖a‖ : ℂ) ^ 2 * (z ^ 2 * ((dist a b : ℝ) : ℂ) ^ 2) * (a * b) := by ring
        _ = (‖a‖ : ℂ) ^ 2 * (-(a - b) ^ 2) * (a * b) := by rw [t1z]
        _ = (-(‖a‖ : ℂ) ^ 2 * (a - b) ^ 2) * (a * b) := by ring
        _ = ((dist a b : ℝ) : ℂ) ^ 2 * (a * b) * (a * b) := by rw [t2z]
    exact mul_left_cancel₀ hne h
  -- The sign relations: there is `ε = ±1` with `R y z = ε a x`, etc.
  have s1 : ((‖a‖ : ℂ) * (y * z)) ^ 2 = (a * x) ^ 2 := by
    have h : (‖a‖ : ℂ) ^ 2 * ((‖a‖ : ℂ) * (y * z)) ^ 2 = (‖a‖ : ℂ) ^ 2 * (a * x) ^ 2 := by
      calc (‖a‖ : ℂ) ^ 2 * ((‖a‖ : ℂ) * (y * z)) ^ 2
          = ((‖a‖ : ℂ) ^ 2 * y ^ 2) * ((‖a‖ : ℂ) ^ 2 * z ^ 2) := by ring
        _ = (c * a) * (a * b) := by rw [e2, e3]
        _ = a ^ 2 * (b * c) := by ring
        _ = a ^ 2 * ((‖a‖ : ℂ) ^ 2 * x ^ 2) := by rw [e1]
        _ = (‖a‖ : ℂ) ^ 2 * (a * x) ^ 2 := by ring
    exact mul_left_cancel₀ (pow_ne_zero 2 hRneC) h
  have h4or : (‖a‖ : ℂ) * (y * z) = a * x ∨ (‖a‖ : ℂ) * (y * z) = -(a * x) :=
    sq_eq_sq_iff_eq_or_eq_neg.mp s1
  have s2 : ((‖a‖ : ℂ) * (z * x)) ^ 2 = (b * y) ^ 2 := by
    have h : (‖a‖ : ℂ) ^ 2 * ((‖a‖ : ℂ) * (z * x)) ^ 2 = (‖a‖ : ℂ) ^ 2 * (b * y) ^ 2 := by
      calc (‖a‖ : ℂ) ^ 2 * ((‖a‖ : ℂ) * (z * x)) ^ 2
          = ((‖a‖ : ℂ) ^ 2 * z ^ 2) * ((‖a‖ : ℂ) ^ 2 * x ^ 2) := by ring
        _ = (a * b) * (b * c) := by rw [e3, e1]
        _ = b ^ 2 * (c * a) := by ring
        _ = b ^ 2 * ((‖a‖ : ℂ) ^ 2 * y ^ 2) := by rw [e2]
        _ = (‖a‖ : ℂ) ^ 2 * (b * y) ^ 2 := by ring
    exact mul_left_cancel₀ (pow_ne_zero 2 hRneC) h
  have h5or : (‖a‖ : ℂ) * (z * x) = b * y ∨ (‖a‖ : ℂ) * (z * x) = -(b * y) :=
    sq_eq_sq_iff_eq_or_eq_neg.mp s2
  have s3 : ((‖a‖ : ℂ) * (x * y)) ^ 2 = (c * z) ^ 2 := by
    have h : (‖a‖ : ℂ) ^ 2 * ((‖a‖ : ℂ) * (x * y)) ^ 2 = (‖a‖ : ℂ) ^ 2 * (c * z) ^ 2 := by
      calc (‖a‖ : ℂ) ^ 2 * ((‖a‖ : ℂ) * (x * y)) ^ 2
          = ((‖a‖ : ℂ) ^ 2 * x ^ 2) * ((‖a‖ : ℂ) ^ 2 * y ^ 2) := by ring
        _ = (b * c) * (c * a) := by rw [e1, e2]
        _ = c ^ 2 * (a * b) := by ring
        _ = c ^ 2 * ((‖a‖ : ℂ) ^ 2 * z ^ 2) := by rw [e3]
        _ = (‖a‖ : ℂ) ^ 2 * (c * z) ^ 2 := by ring
    exact mul_left_cancel₀ (pow_ne_zero 2 hRneC) h
  have h6or : (‖a‖ : ℂ) * (x * y) = c * z ∨ (‖a‖ : ℂ) * (x * y) = -(c * z) :=
    sq_eq_sq_iff_eq_or_eq_neg.mp s3
  have hprod : (‖a‖ : ℂ) * (y * z) * ((‖a‖ : ℂ) * (z * x)) = a * b * (x * y) := by
    calc (‖a‖ : ℂ) * (y * z) * ((‖a‖ : ℂ) * (z * x))
        = ((‖a‖ : ℂ) ^ 2 * z ^ 2) * (x * y) := by ring
      _ = (a * b) * (x * y) := by rw [e3]
  have hprod2 : (‖a‖ : ℂ) * (x * y) * ((‖a‖ : ℂ) * (z * x)) = b * c * (y * z) := by
    calc (‖a‖ : ℂ) * (x * y) * ((‖a‖ : ℂ) * (z * x))
        = ((‖a‖ : ℂ) ^ 2 * x ^ 2) * (y * z) := by ring
      _ = (b * c) * (y * z) := by rw [e1]
  have habxy : a * b * (x * y) ≠ 0 :=
    mul_ne_zero (mul_ne_zero haC hbC) (mul_ne_zero hx_ne hy_ne)
  have hbcyz : b * c * (y * z) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hbC hcC) (mul_ne_zero hy_ne hz_ne)
  obtain ⟨ε, hε, h4, h5, h6⟩ :
      ∃ ε : ℝ, ε ^ 2 = 1 ∧ (‖a‖ : ℂ) * (y * z) = (ε : ℂ) * (a * x)
        ∧ (‖a‖ : ℂ) * (z * x) = (ε : ℂ) * (b * y) ∧ (‖a‖ : ℂ) * (x * y) = (ε : ℂ) * (c * z) := by
    rcases h4or with h4 | h4 <;> rcases h5or with h5 | h5
    · rcases h6or with h6 | h6
      · exact ⟨1, by norm_num, by rw [h4]; push_cast; ring, by rw [h5]; push_cast; ring,
          by rw [h6]; push_cast; ring⟩
      · rw [h6, h5] at hprod2
        have hX : b * c * (y * z) = 0 := by linear_combination (-1 / 2 : ℂ) * hprod2
        exact absurd hX hbcyz
    · rw [h4, h5] at hprod
      have hX : a * b * (x * y) = 0 := by linear_combination (-1 / 2 : ℂ) * hprod
      exact absurd hX habxy
    · rw [h4, h5] at hprod
      have hX : a * b * (x * y) = 0 := by linear_combination (-1 / 2 : ℂ) * hprod
      exact absurd hX habxy
    · rcases h6or with h6 | h6
      · rw [h6, h5] at hprod2
        have hX : b * c * (y * z) = 0 := by linear_combination (-1 / 2 : ℂ) * hprod2
        exact absurd hX hbcyz
      · exact ⟨-1, by norm_num, by rw [h4]; push_cast; ring, by rw [h5]; push_cast; ring,
          by rw [h6]; push_cast; ring⟩
  have h7 : (ε : ℂ) ^ 2 = 1 := by exact_mod_cast hε
  -- The polynomial identity `abc S M = R² xyz (x+y+z) N`, proved via three
  -- `linear_combination` steps and cancellation of `R⁴`.
  have hL : (‖a‖ : ℂ) ^ 2 * (a * b * c * (y * z + x * z + x * y)
        * (a * (b - c) * y * z + b * (c - a) * x * z + c * (a - b) * x * y))
      = a * b * c * (a * x + b * y + c * z)
        * (a ^ 2 * (b - c) * x + b ^ 2 * (c - a) * y + c ^ 2 * (a - b) * z) := by
    linear_combination
      (a * b * c * ((‖a‖ : ℂ) * (y * z + x * z + x * y)) * (a * (b - c))
        + a * b * c * (ε : ℂ)
          * (a ^ 2 * (b - c) * x + b ^ 2 * (c - a) * y + c ^ 2 * (a - b) * z)) * h4
      + (a * b * c * ((‖a‖ : ℂ) * (y * z + x * z + x * y)) * (b * (c - a))
        + a * b * c * (ε : ℂ)
          * (a ^ 2 * (b - c) * x + b ^ 2 * (c - a) * y + c ^ 2 * (a - b) * z)) * h5
      + (a * b * c * ((‖a‖ : ℂ) * (y * z + x * z + x * y)) * (c * (a - b))
        + a * b * c * (ε : ℂ)
          * (a ^ 2 * (b - c) * x + b ^ 2 * (c - a) * y + c ^ 2 * (a - b) * z)) * h6
      + (a * b * c * (a * x + b * y + c * z)
          * (a ^ 2 * (b - c) * x + b ^ 2 * (c - a) * y + c ^ 2 * (a - b) * z)) * h7
  have hM : (‖a‖ : ℂ) ^ 2 * (a * b * c * (a * x + b * y + c * z)
        * (a ^ 2 * (b - c) * x + b ^ 2 * (c - a) * y + c ^ 2 * (a - b) * z))
      = (‖a‖ : ℂ) ^ 2 * (a ^ 2 * b ^ 2 * c ^ 2 * (x + y + z)
        * (x * (b - c) + y * (c - a) + z * (a - b))) := by
    linear_combination (a * b * c * (a * (b - c) * (a ^ 2 - b * c))) * e1
      + (a * b * c * (b * (c - a) * (b ^ 2 - c * a))) * e2
      + (a * b * c * (c * (a - b) * (c ^ 2 - a * b))) * e3
  have hR : (‖a‖ : ℂ) ^ 2 * ((‖a‖ : ℂ) ^ 2 * x * y * z * (x + y + z)
        * (b * c * (b - c) * y * z + c * a * (c - a) * x * z + a * b * (a - b) * x * y))
      = a ^ 2 * b ^ 2 * c ^ 2 * (x + y + z)
        * (x * (b - c) + y * (c - a) + z * (a - b)) := by
    linear_combination
      ((‖a‖ : ℂ) ^ 4 * x * y * z * (x + y + z) * (-((b - c) * y * z))
        + (x + y + z) * (x * (b - c) + y * (c - a) + z * (a - b))
          * ((‖a‖ : ℂ) ^ 4 * y ^ 2 * z ^ 2)) * e1
      + ((‖a‖ : ℂ) ^ 4 * x * y * z * (x + y + z) * (-((c - a) * x * z))
        + (x + y + z) * (x * (b - c) + y * (c - a) + z * (a - b))
          * (b * c * (‖a‖ : ℂ) ^ 2 * z ^ 2)) * e2
      + ((‖a‖ : ℂ) ^ 4 * x * y * z * (x + y + z) * (-((a - b) * x * y))
        + (x + y + z) * (x * (b - c) + y * (c - a) + z * (a - b))
          * (b * c * c * a)) * e3
  have key4 : (‖a‖ : ℂ) ^ 4 * (a * b * c * (y * z + x * z + x * y)
        * (a * (b - c) * y * z + b * (c - a) * x * z + c * (a - b) * x * y))
      = (‖a‖ : ℂ) ^ 4 * ((‖a‖ : ℂ) ^ 2 * x * y * z * (x + y + z)
        * (b * c * (b - c) * y * z + c * a * (c - a) * x * z + a * b * (a - b) * x * y)) := by
    calc (‖a‖ : ℂ) ^ 4 * (a * b * c * (y * z + x * z + x * y)
          * (a * (b - c) * y * z + b * (c - a) * x * z + c * (a - b) * x * y))
        = (‖a‖ : ℂ) ^ 2 * ((‖a‖ : ℂ) ^ 2 * (a * b * c * (y * z + x * z + x * y)
          * (a * (b - c) * y * z + b * (c - a) * x * z + c * (a - b) * x * y))) := by ring
      _ = (‖a‖ : ℂ) ^ 2 * (a * b * c * (a * x + b * y + c * z)
          * (a ^ 2 * (b - c) * x + b ^ 2 * (c - a) * y + c ^ 2 * (a - b) * z)) := by rw [hL]
      _ = (‖a‖ : ℂ) ^ 2 * (a ^ 2 * b ^ 2 * c ^ 2 * (x + y + z)
          * (x * (b - c) + y * (c - a) + z * (a - b))) := hM
      _ = (‖a‖ : ℂ) ^ 2 * ((‖a‖ : ℂ) ^ 2 * ((‖a‖ : ℂ) ^ 2 * x * y * z * (x + y + z)
          * (b * c * (b - c) * y * z + c * a * (c - a) * x * z + a * b * (a - b) * x * y))) := by
        rw [hR]
      _ = (‖a‖ : ℂ) ^ 4 * ((‖a‖ : ℂ) ^ 2 * x * y * z * (x + y + z)
          * (b * c * (b - c) * y * z + c * a * (c - a) * x * z + a * b * (a - b) * x * y)) := by
        ring
  have key : a * b * c * (y * z + x * z + x * y)
        * (a * (b - c) * y * z + b * (c - a) * x * z + c * (a - b) * x * y)
      = (‖a‖ : ℂ) ^ 2 * x * y * z * (x + y + z)
        * (b * c * (b - c) * y * z + c * a * (c - a) * x * z + a * b * (a - b) * x * y) :=
    mul_left_cancel₀ (pow_ne_zero 4 hRneC) key4
  -- Convert the polynomial identity back into the conjugation identity.
  have hα' : ((dist b c : ℝ) : ℂ) = Complex.I * (b - c) / x := by
    rw [← hαx]; exact (mul_div_cancel_right₀ _ hx_ne).symm
  have hβ' : ((dist c a : ℝ) : ℂ) = Complex.I * (c - a) / y := by
    rw [← hβx]; exact (mul_div_cancel_right₀ _ hy_ne).symm
  have hγ' : ((dist a b : ℝ) : ℂ) = Complex.I * (a - b) / z := by
    rw [← hγx]; exact (mul_div_cancel_right₀ _ hz_ne).symm
  have g1 : (star x + star y + star z) * (((dist b c : ℝ) : ℂ) * a
        + ((dist c a : ℝ) : ℂ) * b + ((dist a b : ℝ) : ℂ) * c)
      = Complex.I * (y * z + x * z + x * y)
        * (a * (b - c) * y * z + b * (c - a) * x * z + c * (a - b) * x * y) / (x * y * z) ^ 2 := by
    rw [hstarx, hstary, hstarz, hα', hβ', hγ']
    field_simp [hx_ne, hy_ne, hz_ne]
  have g2 : (x + y + z) * (((dist b c : ℝ) : ℂ) * star a
        + ((dist c a : ℝ) : ℂ) * star b + ((dist a b : ℝ) : ℂ) * star c)
      = Complex.I * (‖a‖ : ℂ) ^ 2 * (x + y + z)
        * (b * c * (b - c) * y * z + c * a * (c - a) * x * z + a * b * (a - b) * x * y)
        / (a * b * c * x * y * z) := by
    rw [hstara, hstarb, hstarc, hα', hβ', hγ']
    field_simp [hx_ne, hy_ne, hz_ne, haC, hbC, hcC]
  have hSig : dist b c • a + dist c a • b + dist a b • c
      = ((dist b c : ℝ) : ℂ) * a + ((dist c a : ℝ) : ℂ) * b + ((dist a b : ℝ) : ℂ) * c := by
    simp only [Complex.real_smul]
  have hstarSig : star (((dist b c : ℝ) : ℂ) * a + ((dist c a : ℝ) : ℂ) * b
        + ((dist a b : ℝ) : ℂ) * c)
      = ((dist b c : ℝ) : ℂ) * star a + ((dist c a : ℝ) : ℂ) * star b
        + ((dist a b : ℝ) : ℂ) * star c := by
    rw [star_add, star_add, star_mul, star_mul, star_mul, star_ofReal', star_ofReal', star_ofReal']
    ring
  have key_div : star (x + y + z) * (dist b c • a + dist c a • b + dist a b • c)
      = (x + y + z) * star (dist b c • a + dist c a • b + dist a b • c) := by
    rw [star_add, star_add, hSig, hstarSig, g1, g2]
    have dne1 : (x * y * z) ^ 2 ≠ 0 :=
      pow_ne_zero 2 (mul_ne_zero (mul_ne_zero hx_ne hy_ne) hz_ne)
    have dne2 : a * b * c * x * y * z ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero haC hbC) hcC) hx_ne)
        hy_ne) hz_ne
    rw [div_eq_div_iff dne1 dne2]
    linear_combination (Complex.I * x * y * z) * key
  -- The conjugation identity says `star w * Sig` is self-conjugate, hence real.
  have hξ : star (star (x + y + z) * (dist b c • a + dist c a • b + dist a b • c))
      = star (x + y + z) * (dist b c • a + dist c a • b + dist a b • c) := by
    rw [star_mul, star_star]
    linear_combination key_div.symm
  have him : (star (x + y + z) * (dist b c • a + dist c a • b + dist a b • c)).im = 0 := by
    have h2 := congrArg Complex.im hξ
    have h3 : (star (star (x + y + z) * (dist b c • a + dist c a • b + dist a b • c))).im
        = -(star (x + y + z) * (dist b c • a + dist c a • b + dist a b • c)).im := rfl
    rw [h3] at h2
    linarith
  show (star (x + y + z) * (dist b c • a + dist c a • b + dist a b • c)).im = 0
  exact him

lemma core {A B C M N P Q S I : ℂ}
    (hRB : ‖A‖ = ‖B‖) (hRC : ‖B‖ = ‖C‖)
    (hK : cr (C - A) (B - A) ≠ 0)
    (hM : Wbtw ℝ A M B) (hQ : Wbtw ℝ A Q C)
    (hN : Wbtw ℝ B N C) (hP : Wbtw ℝ B P C) (hNP : Wbtw ℝ B N P)
    (hAM : dist A M = dist M N) (hMN : dist M N = dist N P)
    (hNPQ : dist N P = dist P Q) (hPQA : dist P Q = dist Q A)
    (hS1 : S ∈ affineSpan ℝ ({M, N} : Set ℂ)) (hS2 : S ∈ affineSpan ℝ ({P, Q} : Set ℂ))
    (hSM : S ≠ M) (hSQ : S ≠ Q)
    (hI : I = (dist B C + dist C A + dist A B)⁻¹ •
      (dist B C • A + dist C A • B + dist A B • C)) :
    ∃ r : ℝ, I = r • ((dist M S)⁻¹ • (M - S) + (dist Q S)⁻¹ • (Q - S)) := by
  have hBC : B ≠ C := by
    intro h
    rw [h] at hK
    exact hK (cr_self _)
  have hCA : C ≠ A := by
    intro h
    rw [h] at hK
    exact hK (by rw [sub_self, cr_zero_left])
  have hAB : A ≠ B := by
    intro h
    rw [h] at hK
    exact hK (by rw [sub_self, cr_zero_right])
  have hα : 0 < dist B C := dist_pos.mpr hBC
  have hβ : 0 < dist C A := dist_pos.mpr hCA
  have hγ : 0 < dist A B := dist_pos.mpr hAB
  have hSig_ne : dist B C + dist C A + dist A B ≠ 0 := ne_of_gt (by positivity)
  obtain ⟨μ, hμ0, hμ1, hμeq⟩ := wbtw_iff_exists.mp hM
  obtain ⟨ν, hν0, hν1, hνeq⟩ := wbtw_iff_exists.mp hQ
  obtain ⟨tN, tP, htN0, htNP, htP1, htNeq, htPeq⟩ := wbtw_chain_params hBC hN hP hNP
  have htP0 : 0 ≤ tP := by linarith [htN0, htNP]
  have htN1 : tN ≤ 1 := by linarith [htNP, htP1]
  have hs : 0 < dist A M := by
    rcases eq_or_lt_of_le (dist_nonneg : 0 ≤ dist A M) with hs0 | hs0
    · exfalso
      have hMA : M = A := (dist_eq_zero.mp hs0.symm).symm
      have hNA : N = A := by
        have hMN0 : dist M N = 0 := by rw [← hAM]; exact hs0.symm
        have hMN' : M = N := dist_eq_zero.mp hMN0
        rw [hMA] at hMN'
        exact hMN'.symm
      have h0 : cr (C - A) (B - A) = 0 := cr_eq_zero_of_wbtw (by rwa [hNA] at hN)
      exact hK h0
    · exact hs0
  have hNM : N ≠ M := by
    intro h
    rw [h, dist_self] at hAM
    linarith [hs, hAM]
  have hNeqP : N ≠ P := by
    intro h
    rw [h] at hAM hMN
    rw [dist_self] at hMN
    linarith [hs, hAM, hMN]
  have hμs : μ = dist A M / dist A B := by
    have e : dist A M = μ * dist A B := by
      rw [dist_eq_norm, hμeq, show A - (A + μ • (B - A)) = μ • (A - B) by module,
        norm_smul, Real.norm_eq_abs, abs_of_nonneg hμ0, dist_eq_norm]
    have hγ0 : dist A B ≠ 0 := ne_of_gt hγ
    rw [e]
    exact (mul_div_cancel_right₀ μ hγ0).symm
  have hνs : ν = dist A M / dist C A := by
    have hAQ : dist A Q = dist A M := by
      rw [dist_comm A Q, ← hPQA, ← hNPQ, ← hMN, ← hAM]
    have e : dist A Q = ν * dist C A := by
      rw [dist_eq_norm, hνeq, show A - (A + ν • (C - A)) = ν • (A - C) by module,
        norm_smul, Real.norm_eq_abs, abs_of_nonneg hν0, dist_eq_norm,
        show A - C = -(C - A) by ring, norm_neg]
    rw [hAQ] at e
    have hβ0 : dist C A ≠ 0 := ne_of_gt hβ
    rw [e]
    exact (mul_div_cancel_right₀ ν hβ0).symm
  have htPs : tP = tN + dist A M / dist B C := by
    have e : dist N P = (tP - tN) * dist B C := by
      rw [dist_eq_norm, htNeq, htPeq,
        show (B + tN • (C - B)) - (B + tP • (C - B)) = (tN - tP) • (C - B) by module,
        norm_smul, Real.norm_eq_abs, abs_of_nonpos (by linarith [htNP]),
        show -(tN - tP) = tP - tN by ring, dist_eq_norm,
        show C - B = -(B - C) by ring, norm_neg]
    have hNPs : dist N P = dist A M := by rw [← hMN, ← hAM]
    rw [hNPs] at e
    have hα0 : dist B C ≠ 0 := ne_of_gt hα
    have h1 : tP - tN = dist A M / dist B C := by
      rw [e]
      exact (mul_div_cancel_right₀ (tP - tN) hα0).symm
    linarith [h1]
  set u := M - N with hudef
  set v := Q - P with hvdef
  set w := arcMid B C + arcMid C A + arcMid A B with hwdef
  set Sig := dist B C • A + dist C A • B + dist A B • C with hSigdef
  have hcrux : cr w Sig = 0 := crux hAB hBC hCA hRB hRC
  have eM : M - A = ((dist A M / dist A B : ℝ) : ℂ) * (B - A) := by
    have h1 : M - A = μ • (B - A) := by rw [hμeq]; module
    rw [h1, hμs, Complex.real_smul]
  have eQ : A - Q = ((dist A M / dist C A : ℝ) : ℂ) * (A - C) := by
    have h1 : A - Q = -ν • (C - A) := by rw [hνeq]; module
    rw [h1, hνs, Complex.real_smul]
    push_cast
    ring
  have eP : P - N = ((dist A M / dist B C : ℝ) : ℂ) * (C - B) := by
    have h1 : P - N = (tP - tN) • (C - B) := by rw [htNeq, htPeq]; module
    have h2 : tP - tN = dist A M / dist B C := by linarith [htPs]
    rw [h1, h2, Complex.real_smul]
  have huv' : u - v = (dist A M : ℝ) • (Complex.I * w) := by
    rw [hudef, hvdef, hwdef]
    rw [show (M - N) - (Q - P) = (M - A) + (A - Q) + (P - N) by ring, eM, eQ, eP]
    simp only [arcMid, Complex.real_smul]
    have hα0c : ((dist B C : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hα)
    have hβ0c : ((dist C A : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hβ)
    have hγ0c : ((dist A B : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hγ)
    push_cast
    field_simp [hα0c, hβ0c, hγ0c]
    ring_nf
    simp only [Complex.I_sq]
    ring_nf
  have hu_norm : ‖u‖ = dist A M := by
    rw [hudef, ← dist_eq_norm, ← hAM]
  have hv_norm : ‖v‖ = dist A M := by
    rw [hvdef, ← dist_eq_norm, dist_comm Q P, ← hNPQ, ← hMN, ← hAM]
  obtain ⟨t₁, ht₁⟩ := exists_eq_add_smul_of_mem_affineSpan_pair hS1
  obtain ⟨t₂', ht₂'⟩ := exists_eq_add_smul_of_mem_affineSpan_pair hS2
  set t₂ := 1 - t₂' with ht₂def
  have ht₂ : S = Q + t₂ • (P - Q) := by
    rw [ht₂def]
    linear_combination (norm := module) ht₂'
  have ht₁0 : t₁ ≠ 0 := by
    intro h0
    apply hSM
    rw [ht₁, h0, zero_smul, add_zero]
  have ht₂0 : t₂ ≠ 0 := by
    intro h0
    apply hSQ
    rw [ht₂, h0, zero_smul, add_zero]
  by_cases hpar : cr (N - M) (P - Q) = 0
  · exact (coll hK hM hQ hN hP hNP hAM hMN hNPQ hPQA hS1 hS2 hpar).elim
  have hSeq : M + t₁ • (N - M) = Q + t₂ • (P - Q) := ht₁.symm.trans ht₂
  have eMP : cr (M - Q) (P - M) =
      -cr (C - A) (B - A) * ((1 - tP) * ν * (1 - μ) + tP * μ * (1 - ν)) := by
    rw [hμeq, hνeq, htPeq,
      show (A + μ • (B - A)) - (A + ν • (C - A)) = μ • (B - A) - ν • (C - A) by module,
      show (B + tP • (C - B)) - (A + μ • (B - A)) =
        (1 - μ) • (B - A) + tP • (C - B) by module]
    simp only [cr_sub_left, cr_add_right, cr_sub_right, cr_smul_left,
      cr_smul_right, cr_self, sub_zero]
    rw [show cr B A = -cr A B by exact cr_antisymm _ _,
      show cr A C = -cr C A by exact cr_antisymm _ _,
      show cr C B = -cr B C by exact cr_antisymm _ _]
    ring
  have eMN : cr (M - Q) (N - M) =
      -cr (C - A) (B - A) * ((1 - tN) * ν * (1 - μ) + tN * μ * (1 - ν)) := by
    rw [hμeq, hνeq, htNeq,
      show (A + μ • (B - A)) - (A + ν • (C - A)) = μ • (B - A) - ν • (C - A) by module,
      show (B + tN • (C - B)) - (A + μ • (B - A)) =
        (1 - μ) • (B - A) + tN • (C - B) by module]
    simp only [cr_sub_left, cr_add_right, cr_sub_right, cr_smul_left,
      cr_smul_right, cr_self, sub_zero]
    rw [show cr B A = -cr A B by exact cr_antisymm _ _,
      show cr A C = -cr C A by exact cr_antisymm _ _,
      show cr C B = -cr B C by exact cr_antisymm _ _]
    ring
  have ePQ : cr (M - Q) (P - Q) = cr (M - Q) (P - M) := by
    rw [show P - Q = (P - M) + (M - Q) by ring, cr_add_right, cr_self, add_zero]
  have e1 : t₁ * cr (N - M) (P - Q) =
      cr (C - A) (B - A) * ((1 - tP) * ν * (1 - μ) + tP * μ * (1 - ν)) := by
    have h0 : cr ((M + t₁ • (N - M)) - Q) (P - Q) = 0 := by
      rw [hSeq, show Q + t₂ • (P - Q) - Q = t₂ • (P - Q) by ring, cr_smul_left,
        cr_self, mul_zero]
    rw [show (M + t₁ • (N - M)) - Q = (M - Q) + t₁ • (N - M) by ring, cr_add_left,
      cr_smul_left, ePQ, eMP] at h0
    linarith
  have e2 : t₂ * cr (P - Q) (N - M) =
      -cr (C - A) (B - A) * ((1 - tN) * ν * (1 - μ) + tN * μ * (1 - ν)) := by
    have h0 : cr ((Q + t₂ • (P - Q)) - M) (N - M) = 0 := by
      rw [← hSeq, show (M + t₁ • (N - M)) - M = t₁ • (N - M) by ring, cr_smul_left,
        cr_self, mul_zero]
    rw [show (Q + t₂ • (P - Q)) - M = (Q - M) + t₂ • (P - Q) by ring, cr_add_left,
      cr_smul_left, show cr (Q - M) (N - M) = -cr (M - Q) (N - M) by
        rw [show Q - M = -(M - Q) by ring, cr_neg_left], eMN] at h0
    linarith
  have hcoeffP : 0 < (1 - tP) * ν * (1 - μ) + tP * μ * (1 - ν) := by
    have hnn : 0 ≤ (1 - tP) * ν * (1 - μ) + tP * μ * (1 - ν) := by
      have g1 : 0 ≤ (1 - tP) * ν * (1 - μ) :=
        mul_nonneg (mul_nonneg (by linarith [htP1]) hν0) (by linarith [hμ1])
      have g2 : 0 ≤ tP * μ * (1 - ν) :=
        mul_nonneg (mul_nonneg htP0 hμ0) (by linarith [hν1])
      linarith [g1, g2]
    by_contra hz
    have hz2 : (1 - tP) * ν * (1 - μ) + tP * μ * (1 - ν) = 0 := by linarith [hnn, hz]
    have h0 : t₁ * cr (N - M) (P - Q) = 0 := by rw [e1, hz2]; ring
    rcases mul_eq_zero.mp h0 with h1 | h2
    · exact ht₁0 h1
    · exact hpar h2
  have hcoeffN : 0 < (1 - tN) * ν * (1 - μ) + tN * μ * (1 - ν) := by
    have hnn : 0 ≤ (1 - tN) * ν * (1 - μ) + tN * μ * (1 - ν) := by
      have g1 : 0 ≤ (1 - tN) * ν * (1 - μ) :=
        mul_nonneg (mul_nonneg (by linarith [htN1]) hν0) (by linarith [hμ1])
      have g2 : 0 ≤ tN * μ * (1 - ν) :=
        mul_nonneg (mul_nonneg htN0 hμ0) (by linarith [hν1])
      linarith [g1, g2]
    by_contra hz
    have hz2 : (1 - tN) * ν * (1 - μ) + tN * μ * (1 - ν) = 0 := by linarith [hnn, hz]
    have h0 : t₂ * cr (P - Q) (N - M) = 0 := by rw [e2, hz2]; ring
    rcases mul_eq_zero.mp h0 with h1 | h2
    · exact ht₂0 h1
    · exact hpar (by rw [cr_antisymm, h2, neg_zero])
  have ht1t2 : 0 < t₁ * t₂ := by
    have m12 : (t₁ * cr (N - M) (P - Q)) * (t₂ * cr (P - Q) (N - M)) =
        (cr (C - A) (B - A) * ((1 - tP) * ν * (1 - μ) + tP * μ * (1 - ν))) *
        (-cr (C - A) (B - A) * ((1 - tN) * ν * (1 - μ) + tN * μ * (1 - ν))) := by
      rw [e1, e2]
    have hswap : cr (P - Q) (N - M) = -cr (N - M) (P - Q) := cr_antisymm _ _
    rw [hswap] at m12
    have e3 : (t₁ * t₂) * (cr (N - M) (P - Q) * cr (N - M) (P - Q)) =
        (cr (C - A) (B - A) * cr (C - A) (B - A)) *
        (((1 - tP) * ν * (1 - μ) + tP * μ * (1 - ν)) *
        ((1 - tN) * ν * (1 - μ) + tN * μ * (1 - ν))) := by
      linear_combination -m12
    have hpos : 0 < (cr (C - A) (B - A) * cr (C - A) (B - A)) *
        (((1 - tP) * ν * (1 - μ) + tP * μ * (1 - ν)) *
        ((1 - tN) * ν * (1 - μ) + tN * μ * (1 - ν))) := by
      have hK2 : 0 < cr (C - A) (B - A) * cr (C - A) (B - A) := mul_self_pos.mpr hK
      exact mul_pos hK2 (mul_pos hcoeffP hcoeffN)
    rw [← e3] at hpos
    have h2 : 0 ≤ cr (N - M) (P - Q) * cr (N - M) (P - Q) := mul_self_nonneg _
    exact pos_of_mul_pos_left hpos h2
  have hσ : Real.sign t₁ = Real.sign t₂ := by
    rcases mul_pos_iff.mp ht1t2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [Real.sign_of_pos h1, Real.sign_of_pos h2]
    · rw [Real.sign_of_neg h1, Real.sign_of_neg h2]
  have ht₁pos_or_neg : t₁ ≠ 0 := ht₁0
  have hMS : dist M S = |t₁| * dist A M := by
    rw [dist_eq_norm, show M - S = t₁ • (M - N) by rw [ht₁]; module, norm_smul,
      Real.norm_eq_abs, ← dist_eq_norm, hAM]
  have hQS : dist Q S = |t₂| * dist A M := by
    rw [dist_eq_norm, show Q - S = t₂ • (Q - P) by rw [ht₂]; module, norm_smul,
      Real.norm_eq_abs, ← dist_eq_norm, dist_comm Q P, ← hNPQ, ← hMN, ← hAM]
  have ht₁abs : t₁ / |t₁| = Real.sign t₁ := by
    rcases le_or_gt 0 t₁ with h1 | h1
    · have h1' : 0 < t₁ := by
        rcases eq_or_lt_of_le h1 with he | he
        · exact absurd he.symm ht₁0
        · exact he
      rw [Real.sign_of_pos h1', abs_of_pos h1']
      exact div_self ht₁0
    · rw [Real.sign_of_neg h1, abs_of_neg h1, div_neg, div_self ht₁0]
  have ht₂abs : t₂ / |t₂| = Real.sign t₂ := by
    rcases le_or_gt 0 t₂ with h1 | h1
    · have h1' : 0 < t₂ := by
        rcases eq_or_lt_of_le h1 with he | he
        · exact absurd he.symm ht₂0
        · exact he
      rw [Real.sign_of_pos h1', abs_of_pos h1']
      exact div_self ht₂0
    · rw [Real.sign_of_neg h1, abs_of_neg h1, div_neg, div_self ht₂0]
  have hd1 : (dist M S)⁻¹ • (M - S) = (Real.sign t₁ / dist A M : ℝ) • u := by
    rw [hMS, show M - S = t₁ • u by rw [ht₁]; module, smul_smul]
    congr 1
    have h2 : |t₁| ≠ 0 := abs_ne_zero.mpr ht₁0
    have h3 : dist A M ≠ 0 := ne_of_gt hs
    rw [← ht₁abs]
    field_simp [h2, h3]
  have hd2 : (dist Q S)⁻¹ • (Q - S) = (Real.sign t₂ / dist A M : ℝ) • v := by
    rw [hQS, show Q - S = t₂ • v by rw [ht₂]; module, smul_smul]
    congr 1
    have h2 : |t₂| ≠ 0 := abs_ne_zero.mpr ht₂0
    have h3 : dist A M ≠ 0 := ne_of_gt hs
    rw [← ht₂abs]
    field_simp [h2, h3]
  have hd : (dist M S)⁻¹ • (M - S) + (dist Q S)⁻¹ • (Q - S) =
      (Real.sign t₁ / dist A M : ℝ) • (u + v) := by
    rw [hd1, hd2, ← hσ, ← smul_add]
  have hcr_uv : cr (u + v) (Complex.I * (u - v)) = 0 := by
    rw [cr_I_right]
    have e : star (u + v) * (u - v) =
        (u * star u - v * star v) + (star v * u - star u * v) := by
      rw [star_add, star_sub]
      ring
    have e2 : (star v * u - star u * v).re = 0 := by
      have h1 : (star v * u).re = (star u * v).re := by
        have e3 : star v * u = star (star u * v) := by rw [star_mul, star_star]
        rw [e3, star_re]
      rw [Complex.sub_re, h1, sub_self]
    rw [e, Complex.add_re, Complex.sub_re, e2, mul_star_self, mul_star_self]
    simp only [Complex.ofReal_re, add_zero]
    rw [hu_norm, hv_norm]
    ring
  have hw0 : w ≠ 0 := by
    intro hw
    have huv0 : u - v = 0 := by
      rw [huv', hw]
      simp
    have huv'' : u = v := sub_eq_zero.mp huv0
    have h0 : cr (N - M) (P - Q) = 0 := by
      have e1 : N - M = -u := by rw [hudef]; ring
      have e2 : P - Q = -v := by rw [hvdef]; ring
      rw [e1, e2, cr_neg_left, cr_neg_right, neg_neg, huv'', cr_self]
    exact hpar h0
  have hIw : Complex.I * (u - v) = (-dist A M : ℝ) • w := by
    rw [huv']
    simp only [Complex.real_smul]
    rw [show (Complex.I : ℂ) * (((dist A M : ℝ) : ℂ) * (Complex.I * w)) =
      ((dist A M : ℝ) : ℂ) * (Complex.I * Complex.I) * w by ring]
    rw [Complex.I_mul_I]
    push_cast
    ring
  have hIU : Complex.I * (u - v) ≠ 0 := by
    rw [hIw]
    exact smul_ne_zero (neg_ne_zero.mpr (ne_of_gt hs)) hw0
  obtain ⟨κ, hκ⟩ := exists_smul_of_cr_eq_zero hIU (by
    rw [cr_antisymm, hcr_uv, neg_zero])
  have hκ0 : κ ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hκ
    have huv'' : u = -v := by linear_combination hκ
    have h0' : cr (N - M) (P - Q) = 0 := by
      have e1 : N - M = -u := by rw [hudef]; ring
      have e2 : P - Q = -v := by rw [hvdef]; ring
      rw [e1, e2, cr_neg_left, cr_neg_right, neg_neg, huv'', cr_neg_left, cr_self,
        neg_zero]
    exact hpar h0'
  by_cases hSig : Sig = 0
  · refine ⟨0, ?_⟩
    rw [hI, hSig]
    simp
  · obtain ⟨t, ht⟩ := exists_smul_of_cr_eq_zero hSig (by
      rw [cr_antisymm, hcrux, neg_zero])
    have ht0 : t ≠ 0 := by
      intro h0
      rw [h0, zero_smul] at ht
      exact hw0 ht
    have huκw : u + v = (-(κ * (dist A M) * t) : ℝ) • Sig := by
      rw [hκ, huv', ht]
      simp only [Complex.real_smul]
      rw [show (Complex.I : ℂ) * (((dist A M : ℝ) : ℂ) * (Complex.I * ((t : ℂ) * Sig))) =
        ((dist A M : ℝ) : ℂ) * (t : ℂ) * (Complex.I * Complex.I) * Sig by ring]
      rw [Complex.I_mul_I]
      push_cast
      ring
    refine ⟨-1 / (Real.sign t₁ * κ * t * (dist B C + dist C A + dist A B)), ?_⟩
    rw [hI, hd, huκw, smul_smul, smul_smul]
    congr 1
    have h1 : Real.sign t₁ ≠ 0 := by
      rcases le_or_gt 0 t₁ with h1' | h1'
      · have h2 : 0 < t₁ := by
          rcases eq_or_lt_of_le h1' with he | he
          · exact absurd he.symm ht₁0
          · exact he
        rw [Real.sign_of_pos h2]
        norm_num
      · rw [Real.sign_of_neg h1']
        norm_num
    field_simp [hSig_ne, h1, hκ0, ht0, hs.ne']

snip end

problem usa2016_p5
    (A B C M N P Q S O I : ℂ)
    (htri : AffineIndependent ℝ ![A, B, C])
    (hM : Wbtw ℝ A M B) (hQ : Wbtw ℝ A Q C)
    (hN : Wbtw ℝ B N C) (hP : Wbtw ℝ B P C)
    (hNP : Wbtw ℝ B N P)
    (hAM : dist A M = dist M N) (hMN : dist M N = dist N P)
    (hNPQ : dist N P = dist P Q) (hPQA : dist P Q = dist Q A)
    (hS1 : S ∈ affineSpan ℝ ({M, N} : Set ℂ)) (hS2 : S ∈ affineSpan ℝ ({P, Q} : Set ℂ))
    (hSM : S ≠ M) (hSQ : S ≠ Q)
    (hO : dist O A = dist O B ∧ dist O B = dist O C)
    (hI : I = (dist B C + dist C A + dist A B)⁻¹ •
      (dist B C • A + dist C A • B + dist A B • C)) :
    ∃ r : ℝ, I - O = r • ((dist M S)⁻¹ • (M - S) + (dist Q S)⁻¹ • (Q - S)) := by
  have hAB : A ≠ B := by
    have h := htri.injective.ne (show (0 : Fin 3) ≠ 1 by decide)
    simpa using h
  have hBC : B ≠ C := by
    have h := htri.injective.ne (show (1 : Fin 3) ≠ 2 by decide)
    simpa using h
  have hAC : A ≠ C := by
    have h := htri.injective.ne (show (0 : Fin 3) ≠ 2 by decide)
    simpa using h
  have hα : 0 < dist B C := dist_pos.mpr hBC
  have hβ : 0 < dist C A := dist_pos.mpr hAC.symm
  have hγ : 0 < dist A B := dist_pos.mpr hAB
  have hSig_ne : dist B C + dist C A + dist A B ≠ 0 := ne_of_gt (by positivity)
  have hK : cr (C - A) (B - A) ≠ 0 := by
    intro h0
    have hCA0 : C - A ≠ 0 := sub_ne_zero.mpr hAC.symm
    obtain ⟨t, ht⟩ := exists_smul_of_cr_eq_zero hCA0 h0
    have hB : B ∈ affineSpan ℝ ({A, C} : Set ℂ) := by
      have e : B = AffineMap.lineMap A C t := by
        rw [AffineMap.lineMap_apply_module']
        linear_combination (norm := module) ht
      rw [e]
      exact AffineMap.lineMap_mem_affineSpan_pair (r := t) (p₁ := A) (p₂ := C)
    have hcoll : Collinear ℝ ({A, B, C} : Set ℂ) := by
      have hAC2 : Collinear ℝ ({A, C} : Set ℂ) := collinear_pair ℝ A C
      have hset : ({A, B, C} : Set ℂ) = insert B {A, C} := by
        ext x
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        tauto
      rw [hset]
      exact (collinear_insert_iff_of_mem_affineSpan hB).mpr hAC2
    exact (affineIndependent_iff_not_collinear_set.mp htri) hcoll
  have hRB : ‖A - O‖ = ‖B - O‖ := by
    have e1 : ‖A - O‖ = dist O A := by
      rw [dist_eq_norm, show A - O = -(O - A) by ring, norm_neg]
    have e2 : ‖B - O‖ = dist O B := by
      rw [dist_eq_norm, show B - O = -(O - B) by ring, norm_neg]
    rw [e1, e2, hO.1]
  have hRC : ‖B - O‖ = ‖C - O‖ := by
    have e2 : ‖B - O‖ = dist O B := by
      rw [dist_eq_norm, show B - O = -(O - B) by ring, norm_neg]
    have e3 : ‖C - O‖ = dist O C := by
      rw [dist_eq_norm, show C - O = -(O - C) by ring, norm_neg]
    rw [e2, e3, hO.2]
  have hK' : cr ((C - O) - (A - O)) ((B - O) - (A - O)) ≠ 0 := by
    have e1 : (C - O) - (A - O) = C - A := by ring
    have e2 : (B - O) - (A - O) = B - A := by ring
    rw [e1, e2]
    exact hK
  have hI' : I - O = (dist (B - O) (C - O) + dist (C - O) (A - O) +
      dist (A - O) (B - O))⁻¹ • (dist (B - O) (C - O) • (A - O) +
      dist (C - O) (A - O) • (B - O) + dist (A - O) (B - O) • (C - O)) := by
    rw [dist_sub_const B C O, dist_sub_const C A O, dist_sub_const A B O, hI]
    have e : dist B C • (A - O) + dist C A • (B - O) + dist A B • (C - O) =
        (dist B C • A + dist C A • B + dist A B • C) -
          (dist B C + dist C A + dist A B) • O := by module
    rw [e, smul_sub, smul_smul, inv_mul_cancel₀ hSig_ne, one_smul]
  obtain ⟨r, hr⟩ := core hRB hRC hK' (wbtw_sub_const hM O) (wbtw_sub_const hQ O)
    (wbtw_sub_const hN O) (wbtw_sub_const hP O) (wbtw_sub_const hNP O)
    (by rw [dist_sub_const, dist_sub_const]; exact hAM)
    (by rw [dist_sub_const, dist_sub_const]; exact hMN)
    (by rw [dist_sub_const, dist_sub_const]; exact hNPQ)
    (by rw [dist_sub_const, dist_sub_const]; exact hPQA)
    (mem_affineSpan_pair_sub_const hS1 O) (mem_affineSpan_pair_sub_const hS2 O)
    (by intro h; exact hSM (by linear_combination h))
    (by intro h; exact hSQ (by linear_combination h))
    hI'
  have e1 : (M - O) - (S - O) = M - S := by ring
  have e2 : (Q - O) - (S - O) = Q - S := by ring
  rw [dist_sub_const M S O, dist_sub_const Q S O, e1, e2] at hr
  exact ⟨r, hr⟩

end Usa2016P5
