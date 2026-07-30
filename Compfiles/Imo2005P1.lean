/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.RingTheory.SimpleRing.Principal
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 2005, Problem 1

Six points are chosen on the sides of an equilateral triangle ABC: A1, A2 on BC,
B1, B2 on CA and C1, C2 on AB, such that they are the vertices of a convex hexagon
A1A2B1B2C1C2 with equal side lengths. Prove that the lines A1B2, B1C2 and C1A2
are concurrent.

## Formalization notes

We identify the Euclidean plane with the complex numbers `ℂ`. The hypothesis that
`ABC` is equilateral is used in the form `C - B = ω * (B - A)` for a primitive
cube root of unity `ω` (rotation by 120°); both orientations of the triangle are
covered since `ω` may be either primitive cube root. The convexity of the hexagon
is encoded by the order of the points on the sides: `A₁ ∈ [B -[ℝ] C]`,
`A₂ ∈ [A₁ -[ℝ] C]`, etc. Concurrency of the three lines is stated as the
existence of a point lying in the real affine span of each pair of points.
-/

namespace Imo2005P1

open scoped Convex
open ComplexConjugate

snip begin

/-- The squared complex norm equals `Complex.normSq`. -/
lemma norm_sq_complex (z : ℂ) : ‖z‖ ^ 2 = Complex.normSq z := by
  rw [Complex.norm_def, Real.sq_sqrt (Complex.normSq_nonneg z)]

/-- Basic facts about a primitive cube root of unity. -/
lemma omega_facts {ω : ℂ} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) :
    ω ^ 2 + ω + 1 = 0 ∧ ω ≠ 0 ∧ Complex.normSq ω = 1 ∧ ‖ω‖ = 1 ∧
    ω.re = -1 / 2 ∧ ω.im ≠ 0 := by
  have hω2 : ω ^ 2 + ω + 1 = 0 := by
    have h : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination hω3
    rcases mul_eq_zero.mp h with h | h
    · exact absurd (sub_eq_zero.mp h) hω1
    · exact h
  have hω0 : ω ≠ 0 := by
    intro h0
    rw [h0] at hω3
    simp at hω3
  have hns : Complex.normSq ω = 1 := by
    have h3 : Complex.normSq (ω ^ 3) = (Complex.normSq ω) ^ 3 := by
      rw [show ω ^ 3 = ω ^ 2 * ω from by ring, Complex.normSq_mul]
      rw [show ω ^ 2 = ω * ω from by ring, Complex.normSq_mul]
      ring
    rw [hω3] at h3
    simp at h3
    have hnn := Complex.normSq_nonneg ω
    have hf : (Complex.normSq ω - 1) * ((Complex.normSq ω) ^ 2 + Complex.normSq ω + 1) = 0 := by
      linear_combination -h3
    rcases mul_eq_zero.mp hf with h | h
    · linarith
    · have hp : (0 : ℝ) < (Complex.normSq ω) ^ 2 + Complex.normSq ω + 1 := by
        nlinarith [sq_nonneg (Complex.normSq ω + 1 / 2)]
      exact absurd h (ne_of_gt hp)
  have hn : ‖ω‖ = 1 := by rw [Complex.norm_def, hns, Real.sqrt_one]
  have hconj : conj ω = ω ^ 2 := by
    have e1 : ω * conj ω = 1 := by rw [Complex.mul_conj, hns]; simp
    have e2 : ω * ω ^ 2 = 1 := by
      have e : ω * ω ^ 2 = ω ^ 3 := by ring
      rw [e, hω3]
    exact mul_left_cancel₀ hω0 (by rw [e1, e2])
  have hre : ω.re = -1 / 2 := by
    have e : ω + conj ω = -1 := by
      rw [hconj]
      linear_combination hω2
    have e2 := Complex.add_conj ω
    rw [e] at e2
    have e4 : (2 : ℝ) * ω.re = -1 := by
      have h : ((2 * ω.re : ℝ) : ℂ) = (-1 : ℂ) := e2.symm
      have h2 : ((-1 : ℝ) : ℂ) = (-1 : ℂ) := by push_cast; ring
      rw [← h2] at h
      exact Complex.ofReal_inj.mp h
    linarith
  have him : ω.im ≠ 0 := by
    intro him0
    have hw : ω = (ω.re : ℂ) := by
      conv_lhs => rw [← Complex.re_add_im ω]
      rw [him0]
      simp
    have h3 : ω.re ^ 3 = (1 : ℝ) := by
      have e : ((ω.re : ℂ)) ^ 3 = 1 := by rw [hw] at hω3; exact hω3
      rw [← Complex.ofReal_pow, ← Complex.ofReal_one] at e
      exact Complex.ofReal_inj.mp e
    have hf : (ω.re - 1) * (ω.re ^ 2 + ω.re + 1) = 0 := by linear_combination h3
    rcases mul_eq_zero.mp hf with h | h
    · have hr1 : ω.re = 1 := by linarith
      rw [hr1] at hre
      norm_num at hre
    · have hp : (0 : ℝ) < ω.re ^ 2 + ω.re + 1 := by
        nlinarith [sq_nonneg (ω.re + 1 / 2)]
      exact absurd h (ne_of_gt hp)
  exact ⟨hω2, hω0, hns, hn, hre, him⟩

/-- Real scalars are determined by their image in the line spanned by `ω`:
if `α + β * ω = 0` with `α β : ℝ`, then `α = β = 0`. -/
lemma coeff_eq_zero {ω : ℂ} (hωim : ω.im ≠ 0) {α β : ℝ}
    (h : (α : ℂ) + (β : ℂ) * ω = 0) : α = 0 ∧ β = 0 := by
  rw [Complex.ext_iff] at h
  obtain ⟨hre, him⟩ := h
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.add_im, Complex.mul_im, Complex.zero_re, Complex.zero_im, zero_mul,
    sub_zero, add_zero, zero_add] at hre him
  have hb : β = 0 := by
    rcases mul_eq_zero.mp him with h | h
    · exact h
    · exact absurd h hωim
  refine ⟨?_, hb⟩
  rw [hb] at hre
  simp at hre
  exact hre

/-- The squared norm of `α + β * ω` for real `α β`. -/
lemma normSq_add_mul_omega {ω : ℂ} (hre : ω.re = -1 / 2) (hns : Complex.normSq ω = 1)
    (α β : ℝ) :
    Complex.normSq ((α : ℂ) + (β : ℂ) * ω) = α ^ 2 - α * β + β ^ 2 := by
  have him : ω.im ^ 2 = 3 / 4 := by
    have h := hns
    rw [Complex.normSq_apply, hre] at h
    nlinarith [h]
  rw [Complex.normSq_apply]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.add_im, Complex.mul_im]
  rw [hre]
  nlinarith [him]

/-- An equilateral triangle `ABC` (either orientation) is described by a primitive
cube root of unity: `C - B = ω * (B - A)`. -/
lemma omega_of_equilateral {A B C : ℂ} (hAB : dist A B = dist B C)
    (hBC : dist B C = dist C A) (hne : A ≠ B) :
    ∃ ω : ℂ, ω ^ 3 = 1 ∧ ω ≠ 1 ∧ C - B = ω * (B - A) := by
  have hu : B - A ≠ 0 := by
    rw [Ne, sub_eq_zero]
    exact Ne.symm hne
  -- side equalities as `normSq` equalities
  have hs1 : Complex.normSq (B - A) = Complex.normSq (C - B) := by
    have h : ‖A - B‖ ^ 2 = ‖B - C‖ ^ 2 := by
      rw [dist_eq_norm, dist_eq_norm] at hAB
      rw [hAB]
    rwa [norm_sq_complex, norm_sq_complex, ← neg_sub B A, ← neg_sub C B,
      Complex.normSq_neg, Complex.normSq_neg] at h
  have hs2 : Complex.normSq (C - A) = Complex.normSq (B - A) := by
    have h : ‖B - C‖ ^ 2 = ‖C - A‖ ^ 2 := by
      rw [dist_eq_norm, dist_eq_norm] at hBC
      rw [hBC]
    rw [norm_sq_complex, norm_sq_complex, ← neg_sub C B, Complex.normSq_neg] at h
    exact h.symm.trans hs1.symm
  -- the key inner product computation
  have hin : ((B - A) * conj (C - B)).re = -Complex.normSq (B - A) / 2 := by
    have n := Complex.normSq_add (B - A) (C - B)
    have e : (B - A) + (C - B) = C - A := by ring
    rw [e, hs2, hs1] at n
    linarith
  have hS0 : Complex.normSq (B - A) ≠ 0 := by
    rw [Ne, Complex.normSq_eq_zero]
    exact hu
  have hS0' : ((Complex.normSq (B - A) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hS0
  -- properties of `ω := (C - B) / (B - A)`
  have hn1 : ‖(C - B) / (B - A)‖ = 1 := by
    rw [Complex.norm_div]
    have h : ‖C - B‖ = ‖B - A‖ := by
      have h2 : ‖C - B‖ ^ 2 = ‖B - A‖ ^ 2 := by
        rw [norm_sq_complex, norm_sq_complex, hs1]
      rwa [sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)] at h2
    rw [h, div_self]
    rwa [Ne, norm_eq_zero]
  have hre1 : ((C - B) / (B - A)).re = -1 / 2 := by
    have e1 : (C - B) / (B - A) =
        ((C - B) * conj (B - A)) / ((Complex.normSq (B - A) : ℝ) : ℂ) := by
      rw [div_eq_div_iff hu hS0']
      rw [← Complex.mul_conj (B - A)]
      ring
    rw [e1]
    have e2 : (((C - B) * conj (B - A)) /
        ((Complex.normSq (B - A) : ℝ) : ℂ)).re =
        ((C - B) * conj (B - A)).re / Complex.normSq (B - A) := by
      rw [div_eq_mul_inv, ← Complex.ofReal_inv, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero, div_eq_mul_inv]
    rw [e2]
    have e3 : ((C - B) * conj (B - A)).re = -Complex.normSq (B - A) / 2 := by
      have hswap : ((C - B) * conj (B - A)).re = ((B - A) * conj (C - B)).re := by
        simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
        ring
      rw [hswap, hin]
    rw [e3]
    field_simp [hS0]
  -- from `‖ω‖ = 1` and `ω.re = -1/2` we get `ω ^ 2 + ω + 1 = 0`
  have hns1 : Complex.normSq ((C - B) / (B - A)) = 1 := by
    have h : ‖(C - B) / (B - A)‖ ^ 2 = 1 := by rw [hn1]; norm_num
    rwa [norm_sq_complex] at h
  have hsum : (C - B) / (B - A) + conj ((C - B) / (B - A)) = -1 := by
    rw [Complex.add_conj, hre1]
    push_cast
    ring
  have hprod : (C - B) / (B - A) * conj ((C - B) / (B - A)) = 1 := by
    rw [Complex.mul_conj, hns1]
    simp
  have hω2 : ((C - B) / (B - A)) ^ 2 + (C - B) / (B - A) + 1 = 0 := by
    have e : (C - B) / (B - A) * ((C - B) / (B - A) + conj ((C - B) / (B - A))) =
        (C - B) / (B - A) * (-1) := by rw [hsum]
    rw [mul_add, hprod] at e
    linear_combination e
  refine ⟨(C - B) / (B - A), ?_, ?_, ?_⟩
  · have e : (((C - B) / (B - A)) - 1) *
        (((C - B) / (B - A)) ^ 2 + (C - B) / (B - A) + 1) = 0 := by rw [hω2]; ring
    have e2 : ((C - B) / (B - A)) ^ 3 - 1 = 0 := by linear_combination e
    linear_combination e2
  · intro h1
    rw [h1] at hre1
    rw [Complex.one_re] at hre1
    norm_num at hre1
  · exact (div_mul_cancel₀ (C - B) hu).symm

/-- Two nested segment memberships give ordered parameters. -/
lemma segment_chain {B C A₁ A₂ : ℂ} (h1 : A₁ ∈ [B -[ℝ] C]) (h2 : A₂ ∈ [A₁ -[ℝ] C]) :
    ∃ t1 t2 : ℝ, 0 ≤ t1 ∧ t1 ≤ t2 ∧ t2 ≤ 1 ∧
      A₁ = B + (t1 : ℂ) * (C - B) ∧ A₂ = B + (t2 : ℂ) * (C - B) := by
  rw [segment_eq_image' ℝ B C] at h1
  rw [segment_eq_image' ℝ A₁ C] at h2
  obtain ⟨t1, ⟨ht10, ht11⟩, hA1⟩ := h1
  obtain ⟨σ, ⟨hσ0, hσ1⟩, hA2⟩ := h2
  simp only [] at hA1 hA2
  have hA1' : A₁ = B + (t1 : ℂ) * (C - B) := by
    rw [← hA1, Complex.real_smul]
  have hA2' : A₂ = B + ((t1 + σ * (1 - t1) : ℝ) : ℂ) * (C - B) := by
    rw [← hA2, hA1', Complex.real_smul]
    push_cast
    ring
  refine ⟨t1, t1 + σ * (1 - t1), ht10, ?_, ?_, hA1', hA2'⟩
  · exact le_add_of_nonneg_right (mul_nonneg hσ0 (sub_nonneg.mpr ht11))
  · have e : σ * (1 - t1) ≤ 1 - t1 := by
      have h := mul_le_mul_of_nonneg_right hσ1 (sub_nonneg.mpr ht11)
      rwa [one_mul] at h
    linarith

/-- Crux: three equal-length vectors with vanishing sum differ by 120° rotations.
We phrase this as: `y = ω * x` or `y = ω ^ 2 * x` for a primitive cube root `ω`. -/
lemma crux {ω x y z : ℂ} (hω2 : ω ^ 2 + ω + 1 = 0) (hω3 : ω ^ 3 = 1)
    (hsum : x + y + z = 0) (hx : x ≠ 0)
    (hxy : Complex.normSq x = Complex.normSq y) (hxz : Complex.normSq x = Complex.normSq z) :
    y = ω * x ∨ y = ω ^ 2 * x := by
  have hz2 : z = -(x + y) := by linear_combination hsum
  have h1 : Complex.normSq z = Complex.normSq x + Complex.normSq y +
      2 * (x * conj y).re := by
    rw [hz2, Complex.normSq_neg, Complex.normSq_add]
  have h2 : (x * conj y).re = -Complex.normSq x / 2 := by
    linarith [h1, hxy, hxz]
  set ζ := conj x * y with hζ
  have hreζ : ζ.re = (x * conj y).re := by
    rw [hζ]
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  have hζ1 : ζ + conj ζ = -(Complex.normSq x : ℂ) := by
    rw [Complex.add_conj, hreζ, h2]
    have e : (2 : ℝ) * (-Complex.normSq x / 2) = -Complex.normSq x := by ring
    rw [e]
    push_cast
    ring
  have hζ2 : ζ * conj ζ = ((Complex.normSq x : ℝ) : ℂ) ^ 2 := by
    rw [Complex.mul_conj, hζ, Complex.normSq_mul, Complex.normSq_conj, hxy]
    push_cast
    ring
  have hc : conj ζ = -(Complex.normSq x : ℂ) - ζ := by linear_combination hζ1
  rw [hc] at hζ2
  have hζ3 : ζ ^ 2 + (Complex.normSq x : ℂ) * ζ + (Complex.normSq x : ℂ) ^ 2 = 0 := by
    linear_combination -hζ2
  have hcc : conj x * x = (Complex.normSq x : ℂ) := by
    rw [mul_comm, Complex.mul_conj]
  have e1 : (conj x) ^ 2 * (x ^ 2 + x * y + y ^ 2) =
      ((Complex.normSq x : ℝ) : ℂ) ^ 2 + (Complex.normSq x : ℂ) * ζ + ζ ^ 2 := by
    rw [hζ]
    linear_combination
      (conj x * x + (Complex.normSq x : ℂ) + conj x * y) * hcc
  have e2 : (conj x) ^ 2 * (x ^ 2 + x * y + y ^ 2) = 0 := by
    rw [e1]
    linear_combination hζ3
  have hcx : conj x ≠ 0 := by
    intro h
    apply hx
    rw [Complex.ext_iff]
    have h1 := congrArg Complex.re h
    have h2 := congrArg Complex.im h
    simp [Complex.conj_re, Complex.conj_im, Complex.zero_re, Complex.zero_im] at h1 h2
    exact ⟨h1, h2⟩
  have e3 : x ^ 2 + x * y + y ^ 2 = 0 := by
    have hne : (conj x) ^ 2 ≠ 0 := pow_ne_zero 2 hcx
    exact (mul_eq_zero.mp e2).resolve_left hne
  have e4 : (y - ω * x) * (y - ω ^ 2 * x) = 0 := by
    linear_combination e3 - x * y * hω2 + x ^ 2 * hω3
  rcases mul_eq_zero.mp e4 with h | h
  · left
    exact eq_of_sub_eq_zero h
  · right
    exact eq_of_sub_eq_zero h

/-- The key collinearity computation: under the hypotheses of the problem, the
centroid `(A₁ + B₁ + C₁) / 3` of the equilateral triangle `A₁B₁C₁` lies on the
line through the two points differing by the vectors `μ • u` and `x`. -/
lemma key2 {ω : ℂ} (hω2 : ω ^ 2 + ω + 1 = 0) {u : ℂ}
    {a b μ : ℝ} (_ha : 0 ≤ a) (hb : 0 ≤ b) (hμ : 0 < μ)
    (hn : a ^ 2 - a * b + b ^ 2 = μ ^ 2) (x : ℂ)
    (hx : x = ((a : ℂ) + (b : ℂ) * ω) * u) :
    ∃ t : ℝ, (2 + ω) * (((μ : ℂ) * u) + x) / 3 = (t : ℂ) * ((1 + ω) * ((μ : ℂ) * u) + x) := by
  have h1 : (0 : ℝ) < μ + b := by linarith
  refine ⟨(μ + a + b) / (3 * (μ + b)), ?_⟩
  have hnC : ((a : ℂ)) ^ 2 - (a : ℂ) * (b : ℂ) + ((b : ℂ)) ^ 2 = ((μ : ℂ)) ^ 2 := by
    exact_mod_cast hn
  have hden : ((3 * (μ + b) : ℝ) : ℂ) ≠ 0 := by
    have hpos : (0 : ℝ) < 3 * (μ + b) := by linarith
    exact_mod_cast (ne_of_gt hpos)
  have key_mul : ((μ : ℂ) + (b : ℂ)) * (2 + ω) * (((μ : ℂ) * u) + x) =
      ((μ : ℂ) + (a : ℂ) + (b : ℂ)) * ((1 + ω) * ((μ : ℂ) * u) + x) := by
    rw [hx]
    linear_combination (-u) * hnC + ((b : ℂ) * ((μ : ℂ) + (b : ℂ)) * u) * hω2
  have hne3 : (3 * (μ + b)) ≠ 0 := ne_of_gt (by linarith : (0 : ℝ) < 3 * (μ + b))
  have htr : (3 * (μ + b)) * ((μ + a + b) / (3 * (μ + b))) = μ + a + b := by
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ hne3]
  have key_mul2 : ((3 * (μ + b) : ℝ) : ℂ) * ((2 + ω) * (((μ : ℂ) * u) + x) / 3) =
      ((3 * (μ + b) : ℝ) : ℂ) *
        (↑((μ + a + b) / (3 * (μ + b))) * ((1 + ω) * ((μ : ℂ) * u) + x)) := by
    have e1 : ((3 * (μ + b) : ℝ) : ℂ) * ((2 + ω) * (((μ : ℂ) * u) + x) / 3) =
        ((μ : ℂ) + (b : ℂ)) * (2 + ω) * (((μ : ℂ) * u) + x) := by
      push_cast
      ring
    have e2 : ((3 * (μ + b) : ℝ) : ℂ) *
        (↑((μ + a + b) / (3 * (μ + b))) * ((1 + ω) * ((μ : ℂ) * u) + x)) =
        ((μ : ℂ) + (a : ℂ) + (b : ℂ)) * ((1 + ω) * ((μ : ℂ) * u) + x) := by
      rw [← mul_assoc, ← Complex.ofReal_mul, htr]
      push_cast
      ring
    rw [e1, e2]
    exact key_mul
  exact mul_left_cancel₀ hden key_mul2

snip end

problem imo2005_p1 (A B C A₁ A₂ B₁ B₂ C₁ C₂ : ℂ)
    (hABC : dist A B = dist B C ∧ dist B C = dist C A ∧ A ≠ B)
    (hA₁ : A₁ ∈ [B -[ℝ] C]) (hA₂ : A₂ ∈ [A₁ -[ℝ] C])
    (hB₁ : B₁ ∈ [C -[ℝ] A]) (hB₂ : B₂ ∈ [B₁ -[ℝ] A])
    (hC₁ : C₁ ∈ [A -[ℝ] B]) (hC₂ : C₂ ∈ [C₁ -[ℝ] B])
    (hside : dist A₁ A₂ = dist A₂ B₁ ∧ dist A₂ B₁ = dist B₁ B₂ ∧
      dist B₁ B₂ = dist B₂ C₁ ∧ dist B₂ C₁ = dist C₁ C₂ ∧ dist C₁ C₂ = dist C₂ A₁)
    (hpos : 0 < dist A₁ A₂) :
    ∃ P : ℂ, P ∈ affineSpan ℝ {A₁, B₂} ∧ P ∈ affineSpan ℝ {B₁, C₂} ∧
      P ∈ affineSpan ℝ {C₁, A₂} := by
  obtain ⟨hAB, hBC, hne⟩ := hABC
  obtain ⟨ω, hω3, hω1, hrot⟩ := omega_of_equilateral hAB hBC hne
  obtain ⟨hω2, _, hnsω, hnω, hreω, himω⟩ := omega_facts hω3 hω1
  obtain ⟨t1, t2, ht10, ht12, ht21, hA1e, hA2e⟩ := segment_chain hA₁ hA₂
  obtain ⟨u1, u2, hu10, hu12, hu21, hB1e, hB2e⟩ := segment_chain hB₁ hB₂
  obtain ⟨v1, v2, hv10, hv12, hv21, hC1e, hC2e⟩ := segment_chain hC₁ hC₂
  set u := C - B with hu_def
  have hu : u ≠ 0 := by
    rw [hu_def, Ne, sub_eq_zero]
    intro hCB
    rw [hCB, dist_self] at hAB
    exact hne (dist_eq_zero.mp hAB)
  -- rotation relations between the sides of the triangle
  have hBA : B - A = ω ^ 2 * u := by
    have e : ω ^ 2 * u = ω ^ 3 * (B - A) := by rw [hrot]; ring
    rw [e, hω3, one_mul]
  have hAC : A - C = ω * u := by
    have e : A - C = -(B - A) - u := by rw [hu_def]; ring
    rw [e, hBA]
    linear_combination (-u) * hω2
  -- the six side vectors of the hexagon, in terms of `u`, `ω` and the parameters
  have hp : A₂ - A₁ = ((t2 - t1 : ℝ) : ℂ) * u := by
    rw [hA2e, hA1e]
    push_cast
    ring
  have hx : B₁ - A₂ = (((1 - t2 : ℝ) : ℂ) + ((u1 : ℝ) : ℂ) * ω) * u := by
    rw [hB1e, hA2e, hAC]
    rw [show C = B + u from by rw [hu_def]; ring]
    push_cast
    ring
  have hq : B₂ - B₁ = ((u2 - u1 : ℝ) : ℂ) * ω * u := by
    rw [hB2e, hB1e, hAC]
    push_cast
    ring
  have hy : C₁ - B₂ = (((1 - u2 : ℝ) : ℂ) * ω + ((v1 : ℝ) : ℂ) * ω ^ 2) * u := by
    rw [hC1e, hB2e, hBA, hAC]
    rw [show A = C + ω * u from by linear_combination hAC]
    push_cast
    ring
  have hr : C₂ - C₁ = ((v2 - v1 : ℝ) : ℂ) * ω ^ 2 * u := by
    rw [hC2e, hC1e, hBA]
    push_cast
    ring
  have hz : A₁ - C₂ = (((1 - v2 : ℝ) : ℂ) * ω ^ 2 + ((t1 : ℝ) : ℂ)) * u := by
    rw [hA1e, hC2e, hBA]
    rw [show B = A + ω ^ 2 * u from by linear_combination hBA]
    push_cast
    ring
  -- side length equalities, as equalities of norms
  obtain ⟨hd1, hd2, hd3, hd4, hd5⟩ := hside
  simp only [dist_eq_norm] at hd1 hd2 hd3 hd4 hd5 hpos
  have hu_pos : (0 : ℝ) < ‖u‖ := norm_pos_iff.mpr hu
  have hnp : ‖A₂ - A₁‖ = (t2 - t1) * ‖u‖ := by
    rw [hp, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr ht12)]
  have hnq : ‖B₂ - B₁‖ = (u2 - u1) * ‖u‖ := by
    rw [hq, Complex.norm_mul, Complex.norm_mul, hnω, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hu12)]
  have hnr : ‖C₂ - C₁‖ = (v2 - v1) * ‖u‖ := by
    rw [hr, Complex.norm_mul, Complex.norm_mul, Complex.norm_pow, hnω, one_pow, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hv12)]
  -- the three on-triangle sides have the same length: the parameters differ by `μ`
  have hμ2 : u2 - u1 = t2 - t1 := by
    have e : ‖A₂ - A₁‖ = ‖B₂ - B₁‖ := by
      rw [norm_sub_rev A₂ A₁, hd1, hd2, norm_sub_rev B₁ B₂]
    rw [hnp, hnq] at e
    exact (mul_right_cancel₀ (ne_of_gt hu_pos) e).symm
  have hμ3 : v2 - v1 = t2 - t1 := by
    have e : ‖A₂ - A₁‖ = ‖C₂ - C₁‖ := by
      rw [norm_sub_rev A₂ A₁, hd1, hd2, hd3, hd4, norm_sub_rev C₁ C₂]
    rw [hnp, hnr] at e
    exact (mul_right_cancel₀ (ne_of_gt hu_pos) e).symm
  have hμ : 0 < t2 - t1 := by
    have e : 0 < ‖u‖ * (t2 - t1) := by
      rw [mul_comm, ← hnp, norm_sub_rev A₂ A₁]
      exact hpos
    exact pos_of_mul_pos_right e hu_pos.le
  -- the three on-triangle side vectors sum to zero, hence so do the crossing ones
  have hpqr : (A₂ - A₁) + (B₂ - B₁) + (C₂ - C₁) = 0 := by
    rw [hp, hq, hr, hμ2, hμ3]
    have e : ((t2 - t1 : ℝ) : ℂ) * u + ((t2 - t1 : ℝ) : ℂ) * ω * u +
        ((t2 - t1 : ℝ) : ℂ) * ω ^ 2 * u = ((t2 - t1 : ℝ) : ℂ) * u * (1 + ω + ω ^ 2) := by ring
    rw [e]
    have hω2' : 1 + ω + ω ^ 2 = 0 := by linear_combination hω2
    rw [hω2', mul_zero]
  have hxyz : (B₁ - A₂) + (C₁ - B₂) + (A₁ - C₂) = 0 := by
    have tel : (A₂ - A₁) + (B₁ - A₂) + (B₂ - B₁) + (C₁ - B₂) + (C₂ - C₁) +
        (A₁ - C₂) = 0 := by ring
    linear_combination tel - hpqr
  -- equal lengths in `normSq` form
  have hns1 : Complex.normSq (B₁ - A₂) = Complex.normSq (A₂ - A₁) := by
    have h : ‖B₁ - A₂‖ = ‖A₂ - A₁‖ := by
      rw [norm_sub_rev B₁ A₂, ← hd1, norm_sub_rev A₁ A₂]
    have h2 : ‖B₁ - A₂‖ ^ 2 = ‖A₂ - A₁‖ ^ 2 := by rw [h]
    rwa [norm_sq_complex, norm_sq_complex] at h2
  have hns2 : Complex.normSq (C₁ - B₂) = Complex.normSq (A₂ - A₁) := by
    have h : ‖C₁ - B₂‖ = ‖A₂ - A₁‖ := by
      rw [norm_sub_rev C₁ B₂, ← hd3, ← hd2, ← hd1, norm_sub_rev A₁ A₂]
    have h2 : ‖C₁ - B₂‖ ^ 2 = ‖A₂ - A₁‖ ^ 2 := by rw [h]
    rwa [norm_sq_complex, norm_sq_complex] at h2
  have hns3 : Complex.normSq (A₁ - C₂) = Complex.normSq (A₂ - A₁) := by
    have h : ‖A₁ - C₂‖ = ‖A₂ - A₁‖ := by
      rw [norm_sub_rev A₁ C₂, ← hd5, ← hd4, ← hd3, ← hd2, ← hd1, norm_sub_rev A₁ A₂]
    have h2 : ‖A₁ - C₂‖ ^ 2 = ‖A₂ - A₁‖ ^ 2 := by rw [h]
    rwa [norm_sq_complex, norm_sq_complex] at h2
  have hx0 : B₁ - A₂ ≠ 0 := by
    have h : ‖B₁ - A₂‖ ≠ 0 := by
      rw [norm_sub_rev B₁ A₂, ← hd1]
      exact ne_of_gt hpos
    rwa [Ne, norm_eq_zero] at h
  -- the crux: the crossing vectors differ by 120° rotations
  rcases crux hω2 hω3 hxyz hx0 (hns1.trans hns2.symm) (hns1.trans hns3.symm) with hy1 | hy2
  · -- the correct orientation: `y = ω * x`
    have hz1 : A₁ - C₂ = ω ^ 2 * (B₁ - A₂) := by
      have e : A₁ - C₂ = -((B₁ - A₂) + (C₁ - B₂)) := by linear_combination hxyz
      rw [e, hy1]
      linear_combination (-(B₁ - A₂)) * hω2
    -- convenient vector relations
    have hq' : B₂ - B₁ = ω * (A₂ - A₁) := by rw [hq, hμ2, hp]; ring
    have hr' : C₂ - C₁ = ω ^ 2 * (A₂ - A₁) := by rw [hr, hμ3, hp]; ring
    have hS1 : B₁ - A₁ = (A₂ - A₁) + (B₁ - A₂) := by ring
    have hS2 : C₁ - B₁ = ω * ((A₂ - A₁) + (B₁ - A₂)) := by
      have e : C₁ - B₁ = (B₂ - B₁) + (C₁ - B₂) := by ring
      rw [e, hq', hy1]; ring
    have hS3 : C₁ - A₁ = (1 + ω) * ((A₂ - A₁) + (B₁ - A₂)) := by
      have e : C₁ - A₁ = (C₁ - B₁) + (B₁ - A₁) := by ring
      rw [e, hS2, hS1]; ring
    have hnsω2 : Complex.normSq (ω ^ 2) = 1 := by
      rw [pow_two, Complex.normSq_mul, hnsω]; ring
    have hqnorm : Complex.normSq (B₂ - B₁) = Complex.normSq (A₂ - A₁) := by
      rw [hq, hμ2, hp]
      simp only [Complex.normSq_mul, hnsω, mul_one]
    have hrnorm : Complex.normSq (C₂ - C₁) = Complex.normSq (A₂ - A₁) := by
      rw [hr, hμ3, hp]
      simp only [Complex.normSq_mul, hnsω2, mul_one]
    -- the norm conditions for the three applications of `key2`
    have hnf1 : (1 - t2) ^ 2 - (1 - t2) * u1 + u1 ^ 2 = (t2 - t1) ^ 2 := by
      have h := hns1
      rw [hx, hp] at h
      simp only [Complex.normSq_mul] at h
      rw [normSq_add_mul_omega hreω hnsω, Complex.normSq_ofReal, ← pow_two] at h
      have hu0 : Complex.normSq u ≠ 0 := by rwa [Ne, Complex.normSq_eq_zero]
      exact mul_right_cancel₀ hu0 h
    have hnf2 : (1 - u2) ^ 2 - (1 - u2) * v1 + v1 ^ 2 = (t2 - t1) ^ 2 := by
      have h : Complex.normSq (C₁ - B₂) = Complex.normSq (B₂ - B₁) := hns2.trans hqnorm.symm
      rw [hy] at h
      rw [show (↑(1 - u2) * ω + ↑v1 * ω ^ 2 : ℂ) = ω * (↑(1 - u2) + ↑v1 * ω) from by ring] at h
      rw [hq, hμ2] at h
      simp only [Complex.normSq_mul, hnsω, one_mul, mul_one] at h
      rw [normSq_add_mul_omega hreω hnsω, Complex.normSq_ofReal, ← pow_two] at h
      have hu0 : Complex.normSq u ≠ 0 := by rwa [Ne, Complex.normSq_eq_zero]
      exact mul_right_cancel₀ hu0 h
    have hnf3 : (1 - v2) ^ 2 - (1 - v2) * t1 + t1 ^ 2 = (t2 - t1) ^ 2 := by
      have h : Complex.normSq (A₁ - C₂) = Complex.normSq (C₂ - C₁) := hns3.trans hrnorm.symm
      rw [hz] at h
      rw [show (↑(1 - v2) * ω ^ 2 + ↑t1 : ℂ) = ω ^ 2 * (↑(1 - v2) + ↑t1 * ω) from by
        rw [show ω ^ 2 * (↑(1 - v2) + ↑t1 * ω) = ↑(1 - v2) * ω ^ 2 + ↑t1 * ω ^ 3 from by ring,
          hω3]
        ring] at h
      rw [hr, hμ3] at h
      simp only [Complex.normSq_mul, hnsω2, one_mul, mul_one] at h
      rw [normSq_add_mul_omega hreω hnsω, Complex.normSq_ofReal, ← pow_two] at h
      have hu0 : Complex.normSq u ≠ 0 := by rwa [Ne, Complex.normSq_eq_zero]
      exact mul_right_cancel₀ hu0 h
    -- the three collinearity facts from `key2`
    obtain ⟨s1, hs1⟩ := key2 hω2 (sub_nonneg.mpr ht21) hu10 hμ hnf1 (B₁ - A₂) hx
    rw [← hp] at hs1
    have hy2'' : C₁ - B₂ = (((1 - u2 : ℝ) : ℂ) + ((v1 : ℝ) : ℂ) * ω) * (ω * u) := by
      rw [hy]; ring
    obtain ⟨s2, hs2⟩ := key2 hω2 (sub_nonneg.mpr hu21) hv10 hμ hnf2 (C₁ - B₂) hy2''
    have hq2 : B₂ - B₁ = ((t2 - t1 : ℝ) : ℂ) * (ω * u) := by rw [hq, hμ2]; ring
    rw [← hq2] at hs2
    have hz2'' : A₁ - C₂ = (((1 - v2 : ℝ) : ℂ) + ((t1 : ℝ) : ℂ) * ω) * (ω ^ 2 * u) := by
      rw [hz]
      have e : (↑(1 - v2) + ↑t1 * ω) * (ω ^ 2 * u) =
          (↑(1 - v2) * ω ^ 2 + ↑t1 * ω ^ 3) * u := by ring
      rw [e, hω3]
      push_cast
      ring
    obtain ⟨s3, hs3⟩ := key2 hω2 (sub_nonneg.mpr hv21) ht10 hμ hnf3 (A₁ - C₂) hz2''
    have hr2 : C₂ - C₁ = ((t2 - t1 : ℝ) : ℂ) * (ω ^ 2 * u) := by rw [hr, hμ3]; ring
    rw [← hr2] at hs3
    -- the concurrency point: the centroid of the equilateral triangle `A₁B₁C₁`
    let P : ℂ := (A₁ + B₁ + C₁) / 3
    have hP : P = (A₁ + B₁ + C₁) / 3 := rfl
    have hPA1 : P - A₁ = (2 + ω) * ((A₂ - A₁) + (B₁ - A₂)) / 3 := by
      have e : P - A₁ = ((B₁ - A₁) + (C₁ - A₁)) / 3 := by rw [hP]; ring
      rw [e, hS1, hS3]; ring
    have hB2A1 : B₂ - A₁ = (1 + ω) * (A₂ - A₁) + (B₁ - A₂) := by
      have e : B₂ - A₁ = (B₂ - B₁) + (B₁ - A₁) := by ring
      rw [e, hq', hS1]; ring
    have hPB1 : P - B₁ = (2 + ω) * ((B₂ - B₁) + (C₁ - B₂)) / 3 := by
      have e : P - B₁ = ((A₁ - B₁) + (C₁ - B₁)) / 3 := by rw [hP]; ring
      have e2 : A₁ - B₁ = -((A₂ - A₁) + (B₁ - A₂)) := by linear_combination -hS1
      have hqy : (B₂ - B₁) + (C₁ - B₂) = ω * ((A₂ - A₁) + (B₁ - A₂)) := by
        have ee : (B₂ - B₁) + (C₁ - B₂) = C₁ - B₁ := by ring
        rw [ee, hS2]
      rw [e, e2, hS2, hqy]
      have hw1 : (2 + ω) * ω = ω - 1 := by linear_combination hω2
      linear_combination (-((A₂ - A₁) + (B₁ - A₂)) / 3) * hw1
    have hC2B1 : C₂ - B₁ = (1 + ω) * (B₂ - B₁) + (C₁ - B₂) := by
      have e : C₂ - B₁ = (C₂ - C₁) + (C₁ - B₂) + (B₂ - B₁) := by ring
      have hrq : C₂ - C₁ = ω * (B₂ - B₁) := by rw [hr', hq']; ring
      rw [e, hrq]; ring
    have hPC1 : P - C₁ = (2 + ω) * ((C₂ - C₁) + (A₁ - C₂)) / 3 := by
      have e : P - C₁ = ((A₁ - C₁) + (B₁ - C₁)) / 3 := by rw [hP]; ring
      have e3 : A₁ - C₁ = -(1 + ω) * ((A₂ - A₁) + (B₁ - A₂)) := by linear_combination -hS3
      have e4 : B₁ - C₁ = -ω * ((A₂ - A₁) + (B₁ - A₂)) := by linear_combination -hS2
      have e5 : (C₂ - C₁) + (A₁ - C₂) = -(1 + ω) * ((A₂ - A₁) + (B₁ - A₂)) := by
        have ee : (C₂ - C₁) + (A₁ - C₂) = A₁ - C₁ := by ring
        rw [ee]; exact e3
      rw [e, e3, e4, e5]
      have hw2 : (2 + ω) * (1 + ω) = 1 + 2 * ω := by linear_combination hω2
      linear_combination (((A₂ - A₁) + (B₁ - A₂)) / 3) * hw2
    have hA2C1 : A₂ - C₁ = (1 + ω) * (C₂ - C₁) + (A₁ - C₂) := by
      have e : A₂ - C₁ = (A₂ - A₁) + (A₁ - C₂) + (C₂ - C₁) := by ring
      have hpr : A₂ - A₁ = ω * (C₂ - C₁) := by
        rw [hp, hr, hμ3]
        have e : ω * (((t2 - t1 : ℝ) : ℂ) * ω ^ 2 * u) = ((t2 - t1 : ℝ) : ℂ) * ω ^ 3 * u := by
          ring
        rw [e, hω3]; ring
      rw [e, hpr]; ring
    -- conclude: `P` lies on all three lines
    have hcol1 : P - A₁ = (s1 : ℝ) • (B₂ - A₁) := by
      rw [← hB2A1] at hs1
      rw [Complex.real_smul, hPA1]
      exact hs1
    have hcol2 : P - B₁ = (s2 : ℝ) • (C₂ - B₁) := by
      rw [← hC2B1] at hs2
      rw [Complex.real_smul, hPB1]
      exact hs2
    have hcol3 : P - C₁ = (s3 : ℝ) • (A₂ - C₁) := by
      rw [← hA2C1] at hs3
      rw [Complex.real_smul, hPC1]
      exact hs3
    have mem_of_col {X Y P₀ : ℂ} {s : ℝ} (h : P₀ - X = s • (Y - X)) :
        P₀ ∈ affineSpan ℝ {X, Y} := by
      have e : P₀ = AffineMap.lineMap X Y s := by
        rw [AffineMap.lineMap_apply_module]
        simp only [Complex.real_smul] at h ⊢
        push_cast at h ⊢
        linear_combination h
      rw [e]
      exact AffineMap.lineMap_mem_affineSpan_pair s X Y
    exact ⟨P, mem_of_col hcol1, mem_of_col hcol2, mem_of_col hcol3⟩
  · -- the mirror orientation is impossible: it forces `B₁ - A₂ = 0`
    exfalso
    have hzb : A₁ - C₂ = ω * (B₁ - A₂) := by
      have e : A₁ - C₂ = -((B₁ - A₂) + (C₁ - B₂)) := by linear_combination hxyz
      rw [e, hy2]
      linear_combination (-(B₁ - A₂)) * hω2
    have e1 : ((1 - u2 : ℝ) : ℂ) * ω + ((v1 : ℝ) : ℂ) * ω ^ 2 =
        ((1 - t2 : ℝ) : ℂ) * ω ^ 2 + ((u1 : ℝ) : ℂ) := by
      apply mul_right_cancel₀ hu
      rw [← hy, hy2, hx]
      have h : ω ^ 2 * ((↑(1 - t2) + ↑u1 * ω) * u) =
          (↑(1 - t2) * ω ^ 2 + ↑u1 * ω ^ 3) * u := by ring
      rw [h, hω3]
      push_cast
      ring
    have e2 : ((1 - v2 : ℝ) : ℂ) * ω ^ 2 + ((t1 : ℝ) : ℂ) =
        ((1 - t2 : ℝ) : ℂ) * ω + ((u1 : ℝ) : ℂ) * ω ^ 2 := by
      apply mul_right_cancel₀ hu
      rw [← hz, hzb, hx]
      ring
    have e1' : (((1 - t2) - u1 - v1 : ℝ) : ℂ) + ((((1 - t2) + (1 - u2) - v1 : ℝ)) : ℂ) * ω = 0 := by
      push_cast at e1 ⊢
      linear_combination e1 + ((1 - ((t2 : ℝ) : ℂ)) - ((v1 : ℝ) : ℂ)) * hω2
    have e2' : ((t1 + u1 - (1 - v2) : ℝ) : ℂ) +
        (((u1 - (1 - v2) - (1 - t2)) : ℝ) : ℂ) * ω = 0 := by
      push_cast at e2 ⊢
      linear_combination e2 + (((u1 : ℝ) : ℂ) - (1 - ((v2 : ℝ) : ℂ))) * hω2
    obtain ⟨hα1, hβ1⟩ := coeff_eq_zero himω e1'
    obtain ⟨hα2, hβ2⟩ := coeff_eq_zero himω e2'
    have ht2' : (0 : ℝ) ≤ 1 - t2 := sub_nonneg.mpr ht21
    have hu2' : (0 : ℝ) ≤ 1 - u2 := sub_nonneg.mpr hu21
    have hv2' : (0 : ℝ) ≤ 1 - v2 := sub_nonneg.mpr hv21
    have hb0 : u1 = 0 := by linarith
    have ha0 : 1 - t2 = 0 := by linarith
    rw [ha0, hb0] at hx
    simp at hx
    exact hx0 hx

end Imo2005P1
