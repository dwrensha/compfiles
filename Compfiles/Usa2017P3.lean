/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# USA Mathematical Olympiad 2017, Problem 3

Let $ABC$ be a scalene triangle with circumcircle $\Omega$ and incenter $I$.
Ray $AI$ meets $BC$ at $D$ and $\Omega$ again at $M$; the circle with diameter
$DM$ cuts $\Omega$ again at $K$. Lines $MK$ and $BC$ meet at $S$, and $N$ is the
midpoint of $IS$. The circumcircles of $\triangle KID$ and $\triangle MAN$
intersect at points $L_1$ and $L_2$. Prove that $\Omega$ passes through the
midpoint of either $IL_1$ or $IL_2$.
-/

namespace Usa2017P3

open Complex ComplexConjugate

snip begin

/-- `OnCirc u v z` says that `z` lies on the circle (in `ℂ`) with equation
`z * conj z + u * z + conj u * conj z + v = 0`; for a genuine circle one has
`v = conj v` and `u * conj u - v > 0`, with center `-conj u` and squared radius
`u * conj u - v`, but we do not need this. -/
noncomputable def OnCirc (u v z : ℂ) : Prop :=
  z * conj z + u * z + conj u * conj z + v = 0

/-- The incenter `I = -(ab + bc + ca)` for the unit-circle parametrization. -/
noncomputable def ptI (a b c : ℂ) : ℂ := -(a*b + b*c + c*a)

/-- The midpoint of arc `BC` not containing `A` (where ray `AI` meets `Ω`
again): `M = -bc`. -/
noncomputable def ptM (b c : ℂ) : ℂ := -(b*c)

/-- The point of `Ω` opposite `M`: `X = bc`. -/
noncomputable def ptX (b c : ℂ) : ℂ := b*c

/-- `D = AI ∩ BC`. -/
noncomputable def ptD (a b c : ℂ) : ℂ := (a^2*b^2 + a^2*c^2 + a^2*b*c - b^2*c^2)/(a^2 + b*c)

/-- The second intersection of the circle with diameter `DM` with `Ω`. -/
noncomputable def ptK (a b c : ℂ) : ℂ := (a^2*b^2 + a^2*c^2 - 2*b^2*c^2)/(2*a^2 - b^2 - c^2)

/-- `S = MK ∩ BC`. -/
noncomputable def ptS (a b c : ℂ) : ℂ := (a^2*b^2 - a^2*b*c + a^2*c^2 - b^2*c^2)/(a^2 - b*c)

/-- The midpoint of `IS`. -/
noncomputable def ptN (a b c : ℂ) : ℂ :=
  a*(a*b^2 + a*c^2 + b^2*c + b*c^2 - a^2*b - a^2*c - 2*a*b*c)/(2*(a^2 - b*c))

/-- The special common point of the two circumcircles (see the file header). -/
noncomputable def ptL (a b c : ℂ) : ℂ := (a*b^2 + a*c^2 + b^2*c + b*c^2)/(2*a + b + c)

/-- The `u`-coefficient of the circumcircle of `KID`. -/
noncomputable def circU₁ (a b c : ℂ) : ℂ :=
  (2*a^2 - b^2 - c^2)*(a^2 + a*b + a*c - b*c)/(2*b*c*(a^2 - b*c)*(a^2 + b*c))

/-- The `v`-coefficient of the circumcircle of `KID`. -/
noncomputable def circV₁ (a b c : ℂ) : ℂ :=
  -((b^2+c^2)*(a^2 + b*c) + a*(b+c)^3)/(2*b*c*(a^2 + b*c))

/-- The `u`-coefficient of the circumcircle of `MAN`. -/
noncomputable def circU₂ (a b c : ℂ) : ℂ := (b-c)^2/(4*b*c*(a^2 - b*c))

/-- The `v`-coefficient of the circumcircle of `MAN`. -/
noncomputable def circV₂ (b c : ℂ) : ℂ := -(b+c)^2/(4*b*c)

section UnitCircle

variable {a b c : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
  (hab : a^2 ≠ b^2) (hbc : b^2 ≠ c^2) (hac : a^2 ≠ c^2)
  (hp : a^2 + b*c ≠ 0) (hm : a^2 - b*c ≠ 0)

include ha in
lemma anz : a ≠ 0 := by
  intro h; rw [h] at ha; simp at ha

include hb in
lemma bnz : b ≠ 0 := by
  intro h; rw [h] at hb; simp at hb

include hc in
lemma cnz : c ≠ 0 := by
  intro h; rw [h] at hc; simp at hc

include ha in
lemma unit_a : a * conj a = 1 := by
  have h := Complex.mul_conj a
  rw [Complex.normSq_eq_norm_sq, ha, one_pow] at h
  exact_mod_cast h

include hb in
lemma unit_b : b * conj b = 1 := by
  have h := Complex.mul_conj b
  rw [Complex.normSq_eq_norm_sq, hb, one_pow] at h
  exact_mod_cast h

include hc in
lemma unit_c : c * conj c = 1 := by
  have h := Complex.mul_conj c
  rw [Complex.normSq_eq_norm_sq, hc, one_pow] at h
  exact_mod_cast h

include ha in
lemma conj_a : conj a = a⁻¹ := eq_inv_of_mul_eq_one_right (unit_a ha)

include hb in
lemma conj_b : conj b = b⁻¹ := eq_inv_of_mul_eq_one_right (unit_b hb)

include hc in
lemma conj_c : conj c = c⁻¹ := eq_inv_of_mul_eq_one_right (unit_c hc)

/-- A unit-modulus `w` with `w + conj w = 2` equals 1. -/
lemma eq_one_of_unit_add_conj {w : ℂ} (h1 : w * conj w = 1) (h2 : w + conj w = 2) :
    w = 1 := by
  have hw : w ≠ 0 := by
    intro h0; rw [h0, zero_mul] at h1; exact zero_ne_one h1
  have hcj : conj w = w⁻¹ := eq_inv_of_mul_eq_one_right h1
  rw [hcj] at h2
  have h3 : w ^ 2 + 1 = 2 * w := by
    have h4 := congrArg (fun t => t * w) h2
    simp only [add_mul, inv_mul_cancel₀ hw] at h4
    linear_combination h4
  have h5 : (w - 1) ^ 2 = 0 := by linear_combination h3
  have h6 : w - 1 = 0 := by rwa [pow_two, mul_self_eq_zero] at h5
  linear_combination h6

/-- Two unit-modulus points at distance 2 from each other... coincide:
from `(x + y) * conj (x + y) = 4` and unit moduli one gets `x = y`. -/
lemma unit_add_unit {x y : ℂ} (hx : x * conj x = 1) (hy : y * conj y = 1)
    (h : (x + y) * conj (x + y) = 4) : x = y := by
  have e1 : x * conj y + y * conj x = 2 := by
    have hexp : (x + y) * conj (x + y)
        = x * conj x + y * conj y + (x * conj y + y * conj x) := by
      simp only [map_add]; ring
    linear_combination h - hexp - hx - hy
  have hw1 : (x * conj y) * conj (x * conj y) = 1 := by
    simp only [map_mul, Complex.conj_conj]
    have e2 : (x * conj y) * (conj x * y) = (x * conj x) * (y * conj y) := by ring
    rw [e2, hx, hy, mul_one]
  have hw2 : (x * conj y) + conj (x * conj y) = 2 := by
    simp only [map_mul, Complex.conj_conj]
    linear_combination e1
  have h1 := eq_one_of_unit_add_conj hw1 hw2
  have hyne : y ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hy; exact zero_ne_one hy
  have hcy : conj y = y⁻¹ := eq_inv_of_mul_eq_one_right hy
  rw [hcy, mul_inv_eq_one₀ hyne] at h1
  exact h1

lemma unit_pow {x : ℂ} (hx : x * conj x = 1) (n : ℕ) : x ^ n * conj (x ^ n) = 1 := by
  simp only [map_pow, ← mul_pow, hx, one_pow]

/-- Transport a nonvanishing fact to a ring-equal form (used to match the
normal forms produced by `field_simp`'s internal normalization). -/
lemma ne_of_ne {x y : ℂ} (h : x ≠ 0) (he : y = x) : y ≠ 0 := by
  rw [he]; exact h

include ha hb hc hbc in
/-- Nondegeneracy: `2a + b + c ≠ 0`. -/
lemma h2abc_ne : 2*a + b + c ≠ 0 := by
  intro h
  have h1 : b + c = -2 * a := by linear_combination h
  have h2 : (b + c) * conj (b + c) = 4 := by
    rw [h1]
    simp only [map_neg, map_mul, map_ofNat, conj_a ha]
    field_simp [anz ha]
    ring
  have h3 := unit_add_unit (unit_b hb) (unit_c hc) h2
  exact hbc (by rw [h3])

include ha hb hc hbc in
/-- Nondegeneracy: `ab + ac + 2bc ≠ 0`. -/
lemma hab2c_ne : a*b + a*c + 2*b*c ≠ 0 := by
  intro h
  have han := anz ha
  have h1 : a * (b + c) = -2 * (b * c) := by linear_combination h
  have h1' : b + c = -2 * (b * c) * a⁻¹ := by
    have h2 := congrArg (fun t => a⁻¹ * t) h1
    rw [← mul_assoc, inv_mul_cancel₀ han, one_mul] at h2
    linear_combination h2
  have h2 : (b + c) * conj (b + c) = 4 := by
    rw [h1']
    simp only [map_neg, map_mul, map_ofNat, conj_a ha, conj_b hb, conj_c hc, map_inv₀]
    field_simp [han, bnz hb, cnz hc]
    ring
  have h3 := unit_add_unit (unit_b hb) (unit_c hc) h2
  exact hbc (by rw [h3])

include ha hb hc hbc in
/-- Nondegeneracy: `2a² - b² - c² ≠ 0`. -/
lemma h2a2_ne : 2*a^2 - b^2 - c^2 ≠ 0 := by
  intro h
  have han := anz ha
  have h1 : 2 * a^2 = b^2 + c^2 := by linear_combination h
  have h2 : (b^2 + c^2) * conj (b^2 + c^2) = 4 := by
    rw [← h1]
    simp only [map_mul, map_ofNat, map_pow, conj_a ha]
    field_simp [han]
    ring
  have h3 := unit_add_unit (unit_pow (unit_b hb) 2) (unit_pow (unit_c hc) 2) h2
  exact hbc h3

include ha hb hc hbc in
/-- Nondegeneracy: `a²b² + a²c² - 2b²c² ≠ 0`. -/
lemma hnK_ne : a^2*b^2 + a^2*c^2 - 2*b^2*c^2 ≠ 0 := by
  intro h
  have han := anz ha
  have h1 : a^2 * (b^2 + c^2) = 2 * (b^2 * c^2) := by linear_combination h
  have h1' : b^2 + c^2 = 2 * (b^2 * c^2) * (a^2)⁻¹ := by
    have h2 := congrArg (fun t => (a^2)⁻¹ * t) h1
    rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 han), one_mul] at h2
    linear_combination h2
  have h2 : (b^2 + c^2) * conj (b^2 + c^2) = 4 := by
    rw [h1']
    simp only [map_mul, map_ofNat, map_pow, conj_a ha, conj_b hb, conj_c hc, map_inv₀]
    field_simp [han, bnz hb, cnz hc]
    ring
  have h3 := unit_add_unit (unit_pow (unit_b hb) 2) (unit_pow (unit_c hc) 2) h2
  exact hbc h3

include hbc in
lemma hbc_add : b + c ≠ 0 := by
  intro h
  apply hbc
  have h1 : b = -c := by linear_combination h
  rw [h1, neg_sq]

include hbc in
lemma hbc_sub : b - c ≠ 0 := by
  intro h
  apply hbc
  have h1 : b = c := by linear_combination h
  rw [h1]

/-! ### Conjugation formulas -/

include ha hb hc in
lemma cj_a2pbc : conj (a^2 + b*c) = (a^2 + b*c)/(a^2*b*c) := by
  have han := anz ha; have hbn := bnz hb; have hcn := cnz hc
  simp only [map_add, map_mul, map_pow, conj_a ha, conj_b hb, conj_c hc]
  field_simp [han, hbn, hcn]
  ring

include ha hb hc in
lemma cj_a2mbc : conj (a^2 - b*c) = -(a^2 - b*c)/(a^2*b*c) := by
  have han := anz ha; have hbn := bnz hb; have hcn := cnz hc
  simp only [map_sub, map_mul, map_pow, conj_a ha, conj_b hb, conj_c hc]
  field_simp [han, hbn, hcn]
  ring

include ha hb hc in
lemma cj_dK : conj (2*a^2 - b^2 - c^2)
    = -(a^2*b^2 + a^2*c^2 - 2*b^2*c^2)/(a^2*b^2*c^2) := by
  have han := anz ha; have hbn := bnz hb; have hcn := cnz hc
  simp only [map_sub, map_mul, map_pow, map_ofNat, conj_a ha, conj_b hb, conj_c hc]
  field_simp [han, hbn, hcn]
  ring

include ha hb hc in
lemma cj_nK : conj (a^2*b^2 + a^2*c^2 - 2*b^2*c^2)
    = -(2*a^2 - b^2 - c^2)/(a^2*b^2*c^2) := by
  have han := anz ha; have hbn := bnz hb; have hcn := cnz hc
  simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, conj_a ha, conj_b hb, conj_c hc]
  field_simp [han, hbn, hcn]
  ring

include ha hb hc in
lemma cj_2abc : conj (2*a + b + c) = (a*b + a*c + 2*b*c)/(a*b*c) := by
  have han := anz ha; have hbn := bnz hb; have hcn := cnz hc
  simp only [map_add, map_mul, map_ofNat, conj_a ha, conj_b hb, conj_c hc]
  field_simp [han, hbn, hcn]
  ring

include ha hb hc in
lemma cj_ab2c : conj (a*b + a*c + 2*b*c) = (2*a + b + c)/(a*b*c) := by
  have han := anz ha; have hbn := bnz hb; have hcn := cnz hc
  simp only [map_add, map_mul, map_ofNat, conj_a ha, conj_b hb, conj_c hc]
  field_simp [han, hbn, hcn]
  ring

include ha hb hc in
lemma cjI : conj (ptI a b c) = -(a + b + c)/(a*b*c) := by
  have han := anz ha; have hbn := bnz hb; have hcn := cnz hc
  simp only [ptI, map_neg, map_add, map_mul, conj_a ha, conj_b hb, conj_c hc]
  field_simp [han, hbn, hcn]
  ring

include ha hb hc hp in
lemma cjD : conj (ptD a b c) = (b^2 + b*c + c^2 - a^2)/(b*c*(a^2 + b*c)) := by
  have han := anz ha; have hbn := bnz hb; have hcn := cnz hc
  simp only [ptD, map_div₀, cj_a2pbc ha hb hc, map_sub, map_add, map_mul, map_pow,
    conj_a ha, conj_b hb, conj_c hc]
  field_simp [han, hbn, hcn, hp]
  ring

include ha hb hc hbc in
/-- `conj K = 1/K` in fraction form. -/
lemma cjK' : conj (ptK a b c)
    = (2*a^2 - b^2 - c^2)/(a^2*b^2 + a^2*c^2 - 2*b^2*c^2) := by
  have han := anz ha; have hbn := bnz hb; have hcn := cnz hc
  have h4 := h2a2_ne ha hb hc hbc
  have h7 := hnK_ne ha hb hc hbc
  simp only [ptK, map_div₀, cj_dK ha hb hc, cj_nK ha hb hc]
  field_simp [han, hbn, hcn, h4, h7]

include ha hb hc hbc in
lemma hKunit : ptK a b c * conj (ptK a b c) = 1 := by
  have h4 := h2a2_ne ha hb hc hbc
  have h7 := hnK_ne ha hb hc hbc
  rw [cjK' ha hb hc hbc, ptK, div_mul_div_comm,
    mul_comm (a^2*b^2 + a^2*c^2 - 2*b^2*c^2) (2*a^2 - b^2 - c^2)]
  exact div_self (mul_ne_zero h4 h7)

include ha hb hc hbc in
lemma cjK : conj (ptK a b c) = (ptK a b c)⁻¹ :=
  eq_inv_of_mul_eq_one_right (hKunit ha hb hc hbc)

include ha hb hc hbc in
lemma hKne : ptK a b c ≠ 0 := by
  intro h0
  have h1 := hKunit ha hb hc hbc
  rw [h0, zero_mul] at h1; exact zero_ne_one h1

include ha hb hc hm in
lemma cjS : conj (ptS a b c) = (a^2 - b^2 + b*c - c^2)/(b*c*(a^2 - b*c)) := by
  have han := anz ha; have hbn := bnz hb; have hcn := cnz hc
  simp only [ptS, map_div₀, cj_a2mbc ha hb hc, map_sub, map_add, map_mul, map_pow,
    conj_a ha, conj_b hb, conj_c hc, map_ofNat]
  field_simp [han, hbn, hcn, hm]
  ring

include ha hb hc hm in
lemma cjN : conj (ptN a b c)
    = -(a^2*b + a^2*c + a*b^2 - 2*a*b*c + a*c^2 - b^2*c - b*c^2)/(2*a*b*c*(a^2 - b*c)) := by
  have han := anz ha; have hbn := bnz hb; have hcn := cnz hc
  simp only [ptN, map_div₀, map_mul, cj_a2mbc ha hb hc, map_sub, map_add, map_pow,
    conj_a ha, conj_b hb, conj_c hc, map_ofNat]
  field_simp [han, hbn, hcn, hm]
  ring

include ha hb hc hbc in
lemma cjL : conj (ptL a b c) = (a*b + a*c + b^2 + c^2)/(b*c*(a*b + a*c + 2*b*c)) := by
  have han := anz ha; have hbn := bnz hb; have hcn := cnz hc
  have h6 := hab2c_ne ha hb hc hbc
  simp only [ptL, map_div₀, cj_2abc ha hb hc, map_add, map_mul, map_pow,
    conj_a ha, conj_b hb, conj_c hc, map_ofNat]
  field_simp [han, hbn, hcn, h6]
  ring

include ha hb hc hp hm in
lemma cju1 : conj (circU₁ a b c)
    = -(a^2*b^2 + a^2*c^2 - 2*b^2*c^2)*(a^2 - a*b - a*c - b*c)
      /(2*(a^2 - b*c)*(a^2 + b*c)) := by
  have han := anz ha; have hbn := bnz hb; have hcn := cnz hc
  simp only [circU₁, map_div₀, map_mul, cj_a2mbc ha hb hc, cj_a2pbc ha hb hc,
    cj_dK ha hb hc, map_sub, map_add, map_pow, conj_a ha, conj_b hb, conj_c hc, map_ofNat]
  field_simp [han, hbn, hcn, hp, hm]
  ring

include ha hb hc hm in
lemma cju2 : conj (circU₂ a b c) = -a^2*(b - c)^2/(4*(a^2 - b*c)) := by
  have han := anz ha; have hbn := bnz hb; have hcn := cnz hc
  simp only [circU₂, map_div₀, map_mul, cj_a2mbc ha hb hc, map_sub, map_pow,
    conj_b hb, conj_c hc, map_ofNat]
  field_simp [han, hbn, hcn, hm]
  ring

/-! ### Membership of the defining points on the two circumcircles -/

include ha hb hc hbc hp hm in
lemma mem_K₁ : OnCirc (circU₁ a b c) (circV₁ a b c) (ptK a b c) := by
  have han := anz ha; have hbn := bnz hb; have hcn := cnz hc
  have hbc0 : b*c ≠ 0 := mul_ne_zero hbn hcn
  have h4 := h2a2_ne ha hb hc hbc; have h7 := hnK_ne ha hb hc hbc
  have hKn := hKne ha hb hc hbc
  have h4v : (a ^ 2 * 2 - b ^ 2 - c ^ 2) ≠ 0 := ne_of_ne h4 (by ring)
  have h7v1 : (a ^ 2 * (b ^ 2 + c ^ 2) - b ^ 2 * c ^ 2 * 2) ≠ 0 := ne_of_ne h7 (by ring)
  have h7v2 : (a ^ 2 * (b ^ 2 + c ^ 2) - 2 * b ^ 2 * c ^ 2) ≠ 0 := ne_of_ne h7 (by ring)
  have h7v3 : (a ^ 2 * b ^ 2 + a ^ 2 * c ^ 2 - b ^ 2 * c ^ 2 * 2) ≠ 0 := ne_of_ne h7 (by ring)
  have h7v4 : (-(b ^ 2 * c ^ 2 * 2) + b ^ 2 * a ^ 2 + c ^ 2 * a ^ 2) ≠ 0 :=
    ne_of_ne h7 (by ring)
  simp only [OnCirc]
  rw [hKunit ha hb hc hbc]
  simp only [cjK' ha hb hc hbc, cju1 ha hb hc hp hm]
  simp only [ptK, circU₁, circV₁]
  field_simp [han, hbn, hcn, hbc0, hp, hm, h4, h7, hKn, h4v, h7v1, h7v2, h7v3, h7v4]
  ring

include ha hb hc hp hm in
lemma mem_I₁ : OnCirc (circU₁ a b c) (circV₁ a b c) (ptI a b c) := by
  have han := anz ha; have hbn := bnz hb; have hcn := cnz hc
  have hbc0 : b*c ≠ 0 := mul_ne_zero hbn hcn
  simp only [OnCirc]
  simp only [cjI ha hb hc, cju1 ha hb hc hp hm]
  simp only [ptI, circU₁, circV₁]
  field_simp [han, hbn, hcn, hbc0, hp, hm]
  ring

include ha hb hc hp hm in
lemma mem_D₁ : OnCirc (circU₁ a b c) (circV₁ a b c) (ptD a b c) := by
  have han := anz ha; have hbn := bnz hb; have hcn := cnz hc
  have hbc0 : b*c ≠ 0 := mul_ne_zero hbn hcn
  simp only [OnCirc]
  simp only [cjD ha hb hc hp, cju1 ha hb hc hp hm]
  simp only [ptD, circU₁, circV₁]
  field_simp [han, hbn, hcn, hbc0, hp, hm]
  ring

include ha hb hc hbc hp hm in
lemma mem_L₁ : OnCirc (circU₁ a b c) (circV₁ a b c) (ptL a b c) := by
  have han := anz ha; have hbn := bnz hb; have hcn := cnz hc
  have hbc0 : b*c ≠ 0 := mul_ne_zero hbn hcn
  have h5 := h2abc_ne ha hb hc hbc; have h6 := hab2c_ne ha hb hc hbc
  have h5v1 : (a * 2 + b + c) ≠ 0 := ne_of_ne h5 (by ring)
  have h5v2 : (b + a * 2 + c) ≠ 0 := ne_of_ne h5 (by ring)
  have h6v1 : (a * (b + c) + b * c * 2) ≠ 0 := ne_of_ne h6 (by ring)
  have h6v2 : (a * b + a * c + b * c * 2) ≠ 0 := ne_of_ne h6 (by ring)
  have h6v3 : (b * a + b * c * 2 + a * c) ≠ 0 := ne_of_ne h6 (by ring)
  simp only [OnCirc]
  simp only [cjL ha hb hc hbc, cju1 ha hb hc hp hm]
  simp only [ptL, circU₁, circV₁]
  field_simp [han, hbn, hcn, hbc0, hp, hm, h5, h6, h5v1, h5v2, h6v1, h6v2, h6v3]
  ring

include ha hb hc hm in
lemma mem_M₂ : OnCirc (circU₂ a b c) (circV₂ b c) (ptM b c) := by
  have han := anz ha; have hbn := bnz hb; have hcn := cnz hc
  have hbc0 : b*c ≠ 0 := mul_ne_zero hbn hcn
  simp only [OnCirc]
  simp only [cju2 ha hb hc hm]
  simp only [circU₂, circV₂, ptM, map_neg, map_mul, conj_b hb, conj_c hc]
  field_simp [han, hbn, hcn, hbc0, hm]
  ring

include ha hb hc hm in
lemma mem_A₂ : OnCirc (circU₂ a b c) (circV₂ b c) (a^2) := by
  have han := anz ha; have hbn := bnz hb; have hcn := cnz hc
  have hbc0 : b*c ≠ 0 := mul_ne_zero hbn hcn
  simp only [OnCirc]
  simp only [cju2 ha hb hc hm]
  simp only [circU₂, circV₂, map_pow, conj_a ha]
  field_simp [han, hbn, hcn, hbc0, hm]
  ring

include ha hb hc hm in
lemma mem_N₂ : OnCirc (circU₂ a b c) (circV₂ b c) (ptN a b c) := by
  have han := anz ha; have hbn := bnz hb; have hcn := cnz hc
  have hbc0 : b*c ≠ 0 := mul_ne_zero hbn hcn
  simp only [OnCirc]
  simp only [cjN ha hb hc hm, cju2 ha hb hc hm]
  simp only [circU₂, circV₂, ptN]
  field_simp [han, hbn, hcn, hbc0, hm]
  ring

include ha hb hc hbc hm in
lemma mem_L₂ : OnCirc (circU₂ a b c) (circV₂ b c) (ptL a b c) := by
  have han := anz ha; have hbn := bnz hb; have hcn := cnz hc
  have hbc0 : b*c ≠ 0 := mul_ne_zero hbn hcn
  have h5 := h2abc_ne ha hb hc hbc; have h6 := hab2c_ne ha hb hc hbc
  have h5v1 : (a * 2 + b + c) ≠ 0 := ne_of_ne h5 (by ring)
  have h5v2 : (b + a * 2 + c) ≠ 0 := ne_of_ne h5 (by ring)
  have h6v1 : (a * (b + c) + b * c * 2) ≠ 0 := ne_of_ne h6 (by ring)
  have h6v2 : (a * b + a * c + b * c * 2) ≠ 0 := ne_of_ne h6 (by ring)
  have h6v3 : (b * a + b * c * 2 + a * c) ≠ 0 := ne_of_ne h6 (by ring)
  simp only [OnCirc]
  simp only [cjL ha hb hc hbc, cju2 ha hb hc hm]
  simp only [circU₂, circV₂, ptL]
  field_simp [han, hbn, hcn, hbc0, hm, h5, h6, h5v1, h5v2, h6v1, h6v2, h6v3]
  ring

/-! ### The midpoint of `I` and `L` lies on `Ω` -/

include ha hb hc hbc in
lemma hTL : (ptI a b c + ptL a b c) * conj (ptI a b c + ptL a b c) = 4 := by
  have han := anz ha; have hbn := bnz hb; have hcn := cnz hc
  have hbc0 : b*c ≠ 0 := mul_ne_zero hbn hcn
  have h5 := h2abc_ne ha hb hc hbc; have h6 := hab2c_ne ha hb hc hbc
  have h5v1 : (a * 2 + b + c) ≠ 0 := ne_of_ne h5 (by ring)
  have h5v2 : (b + a * 2 + c) ≠ 0 := ne_of_ne h5 (by ring)
  have h6v1 : (a * (b + c) + b * c * 2) ≠ 0 := ne_of_ne h6 (by ring)
  have h6v2 : (a * b + a * c + b * c * 2) ≠ 0 := ne_of_ne h6 (by ring)
  have h6v3 : (b * a + b * c * 2 + a * c) ≠ 0 := ne_of_ne h6 (by ring)

  simp only [map_add, cjI ha hb hc, cjL ha hb hc hbc]
  simp only [ptI, ptL]
  field_simp [han, hbn, hcn, hbc0, h5, h6, h5v1, h5v2, h6v1, h6v2, h6v3]
  ring

include ha hb hc hbc in
/-- The point `T = (I + L)/2` is the second intersection of line `XI` with `Ω`. -/
lemma hT_eq : (ptI a b c + ptL a b c)/2 = -a*(a*b + 2*b*c + c*a)/(2*a + b + c) := by
  have h5 := h2abc_ne ha hb hc hbc
  have h5v1 : (a * 2 + b + c) ≠ 0 := ne_of_ne h5 (by ring)
  have h5v2 : (b + a * 2 + c) ≠ 0 := ne_of_ne h5 (by ring)
  simp only [ptI, ptL]
  field_simp [h5, h5v1, h5v2]
  ring

include ha hb hc hbc in
lemma hmid : ‖(ptI a b c + ptL a b c)/2‖ = 1 := by
  have hTL' := hTL ha hb hc hbc
  have hn : ‖ptI a b c + ptL a b c‖ = 2 := by
    have h1 := Complex.mul_conj (ptI a b c + ptL a b c)
    rw [hTL'] at h1
    have h2 : normSq (ptI a b c + ptL a b c) = (4 : ℝ) := by
      exact_mod_cast h1.symm
    rw [Complex.normSq_eq_norm_sq] at h2
    have h3 : (‖ptI a b c + ptL a b c‖ - 2) * (‖ptI a b c + ptL a b c‖ + 2) = 0 := by
      linear_combination h2
    cases mul_eq_zero.mp h3 with
    | inl h5 => linarith
    | inr h5 =>
      have hnn := norm_nonneg (ptI a b c + ptL a b c)
      linarith
  rw [norm_div, hn]
  norm_num

/-! ### Faithfulness: the formal points match the geometric construction -/

include ha hb hc hp in
/-- `D` lies on line `BC`: for points on the unit circle, the line through
`b^2, c^2` has equation `z + b^2 c^2 * conj z = b^2 + c^2`. -/
lemma ptD_on_BC : ptD a b c + b^2*c^2 * conj (ptD a b c) = b^2 + c^2 := by
  have han := anz ha; have hbn := bnz hb; have hcn := cnz hc
  have hbc0 : b*c ≠ 0 := mul_ne_zero hbn hcn
  simp only [cjD ha hb hc hp]
  simp only [ptD]
  field_simp [han, hbn, hcn, hbc0, hp]
  ring

include ha hb hc hp in
/-- `D` lies on line `AI`: `(D - A) / (I - A)` is real. -/
lemma ptD_on_AI : (ptD a b c - a^2) * conj (ptI a b c - a^2)
    = conj (ptD a b c - a^2) * (ptI a b c - a^2) := by
  have han := anz ha; have hbn := bnz hb; have hcn := cnz hc
  have hbc0 : b*c ≠ 0 := mul_ne_zero hbn hcn
  simp only [map_sub, cjI ha hb hc, cjD ha hb hc hp, map_pow, conj_a ha]
  simp only [ptD, ptI]
  field_simp [han, hbn, hcn, hbc0, hp]
  ring

include ha hb hc in
/-- `M` lies on line `AI` (so `M` is indeed the second meet of ray `AI` with
the unit circle; combined with `unit_M` below). -/
lemma ptM_on_AI : (ptM b c - a^2) * conj (ptI a b c - a^2)
    = conj (ptM b c - a^2) * (ptI a b c - a^2) := by
  have han := anz ha; have hbn := bnz hb; have hcn := cnz hc
  have hbc0 : b*c ≠ 0 := mul_ne_zero hbn hcn
  simp only [map_sub, cjI ha hb hc, map_pow, conj_a ha]
  simp only [ptM, ptI, map_neg, map_mul, conj_b hb, conj_c hc]
  field_simp [han, hbn, hcn, hbc0]
  ring

include hb hc in
/-- `M` lies on the unit circle. -/
lemma unit_M : ptM b c * conj (ptM b c) = 1 := by
  have hbn := bnz hb; have hcn := cnz hc
  simp only [ptM, map_neg, map_mul, conj_b hb, conj_c hc]
  field_simp [hbn, hcn]

include ha hb hc hm in
/-- `S` lies on line `BC`. -/
lemma ptS_on_BC : ptS a b c + b^2*c^2 * conj (ptS a b c) = b^2 + c^2 := by
  have han := anz ha; have hbn := bnz hb; have hcn := cnz hc
  have hbc0 : b*c ≠ 0 := mul_ne_zero hbn hcn
  simp only [cjS ha hb hc hm]
  simp only [ptS]
  field_simp [han, hbn, hcn, hbc0, hm]
  ring

include ha hb hc hbc hm in
/-- `S` lies on line `MK` (both on the unit circle). -/
lemma ptS_on_MK : ptS a b c + ptM b c * ptK a b c * conj (ptS a b c)
    = ptM b c + ptK a b c := by
  have han := anz ha; have hbn := bnz hb; have hcn := cnz hc
  have hbc0 : b*c ≠ 0 := mul_ne_zero hbn hcn
  have h4 := h2a2_ne ha hb hc hbc
  have h4v : (a ^ 2 * 2 - b ^ 2 - c ^ 2) ≠ 0 := ne_of_ne h4 (by ring)
  simp only [cjS ha hb hc hm]
  simp only [ptS, ptM, ptK]
  field_simp [han, hbn, hcn, hbc0, hm, h4, h4v]
  ring

include ha hb hc hbc hp in
/-- The angle `∠DKM` is a right angle: `(K - D)/(K - M)` is purely imaginary.
Together with `hKunit` (`K` on the unit circle), `ptS_on_MK`, and collinearity
of `K, D, X` (`ptK_on_DX`), this confirms that `K` is the second intersection
of the circle with diameter `DM` with `Ω`. -/
lemma ptK_right_angle : (ptK a b c - ptD a b c) * conj (ptK a b c - ptM b c)
    + conj (ptK a b c - ptD a b c) * (ptK a b c - ptM b c) = 0 := by
  have han := anz ha; have hbn := bnz hb; have hcn := cnz hc
  have hbc0 : b*c ≠ 0 := mul_ne_zero hbn hcn
  have h4 := h2a2_ne ha hb hc hbc; have h7 := hnK_ne ha hb hc hbc
  have hKn := hKne ha hb hc hbc
  have h4v : (a ^ 2 * 2 - b ^ 2 - c ^ 2) ≠ 0 := ne_of_ne h4 (by ring)
  have h7v1 : (a ^ 2 * (b ^ 2 + c ^ 2) - b ^ 2 * c ^ 2 * 2) ≠ 0 := ne_of_ne h7 (by ring)
  have h7v2 : (a ^ 2 * (b ^ 2 + c ^ 2) - 2 * b ^ 2 * c ^ 2) ≠ 0 := ne_of_ne h7 (by ring)
  have h7v3 : (a ^ 2 * b ^ 2 + a ^ 2 * c ^ 2 - b ^ 2 * c ^ 2 * 2) ≠ 0 := ne_of_ne h7 (by ring)
  have h7v4 : (-(b ^ 2 * c ^ 2 * 2) + b ^ 2 * a ^ 2 + c ^ 2 * a ^ 2) ≠ 0 :=
    ne_of_ne h7 (by ring)

  simp only [map_sub, cjK ha hb hc hbc, cjD ha hb hc hp]
  simp only [ptM, ptK, ptD, map_neg, map_mul, conj_b hb, conj_c hc]
  field_simp [han, hbn, hcn, hbc0, hp, h4, h7, hKn, h4v, h7v1, h7v2, h7v3, h7v4]
  ring

include ha hb hc hbc hp in
/-- `K, D, X` are collinear: `(K - X)/(D - X)` is real. -/
lemma ptK_on_DX : (ptK a b c - ptX b c) * conj (ptD a b c - ptX b c)
    = conj (ptK a b c - ptX b c) * (ptD a b c - ptX b c) := by
  have han := anz ha; have hbn := bnz hb; have hcn := cnz hc
  have hbc0 : b*c ≠ 0 := mul_ne_zero hbn hcn
  have h4 := h2a2_ne ha hb hc hbc; have h7 := hnK_ne ha hb hc hbc
  have hKn := hKne ha hb hc hbc
  have h4v : (a ^ 2 * 2 - b ^ 2 - c ^ 2) ≠ 0 := ne_of_ne h4 (by ring)
  have h7v1 : (a ^ 2 * (b ^ 2 + c ^ 2) - b ^ 2 * c ^ 2 * 2) ≠ 0 := ne_of_ne h7 (by ring)
  have h7v2 : (a ^ 2 * (b ^ 2 + c ^ 2) - 2 * b ^ 2 * c ^ 2) ≠ 0 := ne_of_ne h7 (by ring)
  have h7v3 : (a ^ 2 * b ^ 2 + a ^ 2 * c ^ 2 - b ^ 2 * c ^ 2 * 2) ≠ 0 := ne_of_ne h7 (by ring)
  have h7v4 : (-(b ^ 2 * c ^ 2 * 2) + b ^ 2 * a ^ 2 + c ^ 2 * a ^ 2) ≠ 0 :=
    ne_of_ne h7 (by ring)

  simp only [map_sub, cjK ha hb hc hbc, cjD ha hb hc hp]
  simp only [ptX, ptK, ptD, map_mul, conj_b hb, conj_c hc]
  field_simp [han, hbn, hcn, hbc0, hp, h4, h7, hKn, h4v, h7v1, h7v2, h7v3, h7v4]
  ring

include ha hb hc hbc hm in
/-- `K ≠ M`: the circle with diameter `DM` meets `Ω` *again* at `K`. -/
lemma ptK_ne_M : ptK a b c ≠ ptM b c := by
  have han := anz ha; have hbn := bnz hb; have hcn := cnz hc
  have hbc0 : b*c ≠ 0 := mul_ne_zero hbn hcn
  have h4 := h2a2_ne ha hb hc hbc; have h7 := hnK_ne ha hb hc hbc
  have h7v1 : (a ^ 2 * (b ^ 2 + c ^ 2) - b ^ 2 * c ^ 2 * 2) ≠ 0 := ne_of_ne h7 (by ring)
  have h7v2 : (a ^ 2 * (b ^ 2 + c ^ 2) - 2 * b ^ 2 * c ^ 2) ≠ 0 := ne_of_ne h7 (by ring)
  have h7v3 : (a ^ 2 * b ^ 2 + a ^ 2 * c ^ 2 - b ^ 2 * c ^ 2 * 2) ≠ 0 := ne_of_ne h7 (by ring)
  have h7v4 : (-(b ^ 2 * c ^ 2 * 2) + b ^ 2 * a ^ 2 + c ^ 2 * a ^ 2) ≠ 0 :=
    ne_of_ne h7 (by ring)
  have h4v : (a ^ 2 * 2 - b ^ 2 - c ^ 2) ≠ 0 := ne_of_ne h4 (by ring)
  have hbc_add' := hbc_add hbc
  intro h
  have hconj : conj (ptK a b c - ptM b c) = 0 := by rw [h, sub_self, map_zero]
  have hKM : conj (ptK a b c - ptM b c)
      = ((a^2 - b*c)*(b+c)^2)/((a^2*b^2 + a^2*c^2 - 2*b^2*c^2)*(b*c)) := by
    simp only [map_sub, cjK ha hb hc hbc]
    simp only [ptM, ptK, map_neg, map_mul, conj_b hb, conj_c hc]
    field_simp [han, hbn, hcn, hbc0, h4, h7, h4v, h7v1, h7v2, h7v3, h7v4]
    ring
  rw [hKM] at hconj
  have hnum : (a^2 - b*c)*(b+c)^2 ≠ 0 :=
    mul_ne_zero hm (pow_ne_zero 2 hbc_add')
  have hden : (a^2*b^2 + a^2*c^2 - 2*b^2*c^2)*(b*c) ≠ 0 := mul_ne_zero h7 hbc0
  rw [div_eq_zero_iff] at hconj
  rcases hconj with hconj | hconj
  · exact hnum hconj
  · exact hden hconj

/-! ### The two circumcircles are distinct -/

include ha hb hc hbc hp hm in
/-- The point `M` does not lie on the circumcircle of `KID`. -/
lemma ptM_not_on₁ : ¬ OnCirc (circU₁ a b c) (circV₁ a b c) (ptM b c) := by
  have han := anz ha; have hbn := bnz hb; have hcn := cnz hc
  have hbc0 : b*c ≠ 0 := mul_ne_zero hbn hcn
  have hbc_add' := hbc_add hbc
  have key : ptM b c * conj (ptM b c) + circU₁ a b c * ptM b c
      + conj (circU₁ a b c) * conj (ptM b c) + circV₁ a b c
      = -2*a*(a^2 - b*c)*(b+c)^3/(2*b*c*(a^2 - b*c)*(a^2 + b*c)) := by
    simp only [cju1 ha hb hc hp hm]
    simp only [circU₁, circV₁, ptM, map_neg, map_mul, conj_b hb, conj_c hc]
    field_simp [han, hbn, hcn, hbc0, hp, hm]
    ring
  rw [OnCirc]
  rw [key]
  have hnum : -2*a*(a^2 - b*c)*(b+c)^3 ≠ 0 := by
    have h1 : (-2 : ℂ) ≠ 0 := by norm_num
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero h1 han) hm) (pow_ne_zero 3 hbc_add')
  have hden : 2*b*c*(a^2 - b*c)*(a^2 + b*c) ≠ 0 := by
    have h1 : (2 : ℂ) ≠ 0 := by norm_num
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h1 hbn) hcn) hm) hp
  intro h0
  rw [div_eq_zero_iff] at h0
  rcases h0 with h0 | h0
  · exact hnum h0
  · exact hden h0

include ha hb hc hbc hp hm in
/-- The two circumcircles are distinct (so they have at most two common points). -/
lemma hcircles_distinct :
    (circU₁ a b c, circV₁ a b c) ≠ (circU₂ a b c, circV₂ b c) := by
  intro h
  have hM2 := mem_M₂ ha hb hc hm
  have hM1 := ptM_not_on₁ ha hb hc hbc hp hm
  obtain ⟨hu, hv⟩ := Prod.mk_inj.mp h
  rw [hu, hv] at hM1
  exact hM1 hM2

/-! ### Two distinct circles meet in at most two points -/

/-- If `(u₁, v₁) ≠ (u₂, v₂)`, the solution sets of the two circle equations
share at most two points: any three common points contain two equal ones. -/
lemma eq_of_three_common {u₁ v₁ u₂ v₂ : ℂ} (hne : (u₁, v₁) ≠ (u₂, v₂))
    {z₁ z₂ z₃ : ℂ}
    (h₁₁ : OnCirc u₁ v₁ z₁) (h₂₁ : OnCirc u₂ v₂ z₁)
    (h₁₂ : OnCirc u₁ v₁ z₂) (h₂₂ : OnCirc u₂ v₂ z₂)
    (h₁₃ : OnCirc u₁ v₁ z₃) (h₂₃ : OnCirc u₂ v₂ z₃) :
    z₁ = z₂ ∨ z₂ = z₃ ∨ z₁ = z₃ := by
  have hE : ∀ z, OnCirc u₁ v₁ z → OnCirc u₂ v₂ z
      → (u₁ - u₂) * z + conj (u₁ - u₂) * conj z + (v₁ - v₂) = 0 := by
    intro z h1 h2
    have hconj : conj (u₁ - u₂) = conj u₁ - conj u₂ := map_sub _ _ _
    rw [OnCirc] at h1 h2
    rw [hconj]
    linear_combination h1 - h2
  by_cases hu : u₁ = u₂
  · have hv : v₁ ≠ v₂ := by
      intro h; exact hne (Prod.ext hu h)
    exfalso
    have h := hE z₁ h₁₁ h₂₁
    simp only [hu, sub_self, zero_mul, map_zero, zero_add, sub_eq_zero] at h
    exact hv h
  · have hw : u₁ - u₂ ≠ 0 := sub_ne_zero.mpr hu
    have hα : (-(u₁ - u₂)) ≠ 0 := neg_ne_zero.mpr hw
    have quad : ∀ z, OnCirc u₁ v₁ z → OnCirc u₂ v₂ z
        → (-(u₁ - u₂))*z^2 + (u₁*conj (u₁ - u₂) - (v₁ - v₂) - conj u₁*(u₁ - u₂))*z
          + (v₁*conj (u₁ - u₂) - conj u₁*(v₁ - v₂)) = 0 := by
      intro z h1 h2
      have hEz := hE z h1 h2
      rw [OnCirc] at h1
      linear_combination conj (u₁ - u₂) * h1 - (z + conj u₁) * hEz
    have q1 := quad z₁ h₁₁ h₂₁
    have q2 := quad z₂ h₁₂ h₂₂
    have q3 := quad z₃ h₁₃ h₂₃
    by_cases h12 : z₁ = z₂
    · exact Or.inl h12
    · by_cases h23 : z₂ = z₃
      · exact Or.inr (Or.inl h23)
      · have s12 : (-(u₁ - u₂))*(z₁+z₂)
            + (u₁*conj (u₁ - u₂) - (v₁ - v₂) - conj u₁*(u₁ - u₂)) = 0 := by
          have hsub : (z₁ - z₂) * ((-(u₁ - u₂))*(z₁+z₂)
              + (u₁*conj (u₁ - u₂) - (v₁ - v₂) - conj u₁*(u₁ - u₂))) = 0 := by
            linear_combination q1 - q2
          exact (mul_eq_zero.mp hsub).resolve_left (sub_ne_zero.mpr h12)
        have s23 : (-(u₁ - u₂))*(z₂+z₃)
            + (u₁*conj (u₁ - u₂) - (v₁ - v₂) - conj u₁*(u₁ - u₂)) = 0 := by
          have hsub : (z₂ - z₃) * ((-(u₁ - u₂))*(z₂+z₃)
              + (u₁*conj (u₁ - u₂) - (v₁ - v₂) - conj u₁*(u₁ - u₂))) = 0 := by
            linear_combination q2 - q3
          exact (mul_eq_zero.mp hsub).resolve_left (sub_ne_zero.mpr h23)
        have hfinal : (-(u₁ - u₂))*(z₁ - z₃) = 0 := by
          linear_combination s12 - s23
        have hz := (mul_eq_zero.mp hfinal).resolve_left hα
        exact Or.inr (Or.inr (eq_of_sub_eq_zero hz))

end UnitCircle

snip end

problem usa2017_p3 (a b c : ℂ) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (hab : a^2 ≠ b^2) (hbc : b^2 ≠ c^2) (hac : a^2 ≠ c^2)
    (hp : a^2 + b*c ≠ 0) (hm : a^2 - b*c ≠ 0)
    (L₁ L₂ : ℂ) (hL : L₁ ≠ L₂)
    (h₁₁ : OnCirc (circU₁ a b c) (circV₁ a b c) L₁)
    (h₂₁ : OnCirc (circU₂ a b c) (circV₂ b c) L₁)
    (h₁₂ : OnCirc (circU₁ a b c) (circV₁ a b c) L₂)
    (h₂₂ : OnCirc (circU₂ a b c) (circV₂ b c) L₂) :
    ‖(ptI a b c + L₁)/2‖ = 1 ∨ ‖(ptI a b c + L₂)/2‖ = 1 := by
  have hmid' := hmid ha hb hc hbc
  have hL1 := mem_L₁ ha hb hc hbc hp hm
  have hL2 := mem_L₂ ha hb hc hbc hm
  have hne := hcircles_distinct ha hb hc hbc hp hm
  have h := eq_of_three_common hne h₁₁ h₂₁ h₁₂ h₂₂ hL1 hL2
  rcases h with h | h | h
  · exact absurd h hL
  · right
    rw [h]
    exact hmid'
  · left
    rw [h]
    exact hmid'

end Usa2017P3
