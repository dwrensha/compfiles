/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Inequality, .Geometry] }

/-!
# USA Mathematical Olympiad 1981, Problem 3

Show that for any triangle, 3(√3)/2 ≥ sin 3A + sin 3B + sin 3C ≥ -2.
When does equality hold?
-/

namespace Usa1981P3

snip begin

/-- For `x y ∈ [0, π]`, `sin x + sin y ≤ 2 sin ((x + y) / 2)`:
follows from the sum-to-product formula and `cos ≤ 1`. -/
lemma sin_pair_le {x y : ℝ} (hx : x ∈ Set.Icc 0 Real.pi) (hy : y ∈ Set.Icc 0 Real.pi) :
    Real.sin x + Real.sin y ≤ 2 * Real.sin ((x + y) / 2) := by
  rw [Real.sin_add_sin]
  have hs : 0 ≤ Real.sin ((x + y) / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hx.1, hy.1]) (by linarith [hx.2, hy.2])
  have hc : Real.cos ((x - y) / 2) ≤ 1 := Real.cos_le_one _
  calc 2 * Real.sin ((x + y) / 2) * Real.cos ((x - y) / 2)
      ≤ 2 * Real.sin ((x + y) / 2) * 1 :=
        mul_le_mul_of_nonneg_left hc (mul_nonneg (by norm_num) hs)
    _ = 2 * Real.sin ((x + y) / 2) := by ring

/-- Equality in `sin_pair_le` forces `x = y`. -/
lemma sin_pair_eq {x y : ℝ} (hx : x ∈ Set.Icc 0 Real.pi) (hy : y ∈ Set.Icc 0 Real.pi)
    (h : Real.sin x + Real.sin y = 2 * Real.sin ((x + y) / 2)) : x = y := by
  obtain ⟨hx0, hxp⟩ := hx
  obtain ⟨hy0, hyp⟩ := hy
  rw [Real.sin_add_sin] at h
  have hfact : 2 * Real.sin ((x + y) / 2) * (1 - Real.cos ((x - y) / 2)) = 0 := by
    linarith [h]
  rcases mul_eq_zero.mp hfact with hs | hc
  · have hs0 : Real.sin ((x + y) / 2) = 0 := by
      rcases mul_eq_zero.mp hs with h2 | h2
      · norm_num at h2
      · exact h2
    have hsp : (x + y) / 2 = 0 ∨ (x + y) / 2 = Real.pi := by
      by_cases h0 : (x + y) / 2 = 0
      · exact Or.inl h0
      · have hpos : 0 < (x + y) / 2 := lt_of_le_of_ne' (by linarith) h0
        by_cases hp : (x + y) / 2 = Real.pi
        · exact Or.inr hp
        · have hlt : (x + y) / 2 < Real.pi := lt_of_le_of_ne (by linarith) hp
          have hsin := Real.sin_pos_of_pos_of_lt_pi hpos hlt
          exact absurd hs0 (by linarith [hsin])
    rcases hsp with hsp | hsp
    · linarith
    · linarith
  · have hc1 : Real.cos ((x - y) / 2) = 1 := by linarith [hc]
    have hd0 : (x - y) / 2 = 0 := by
      have hpi := Real.pi_pos
      exact (Real.cos_eq_one_iff_of_lt_of_lt (by linarith) (by linarith)).mp hc1
    linarith [hd0]

/-- Three-term Jensen inequality for `sin` on `[0, π]`. -/
lemma sin_jensen_three {x y z : ℝ} (hx : x ∈ Set.Icc 0 Real.pi) (hy : y ∈ Set.Icc 0 Real.pi)
    (hz : z ∈ Set.Icc 0 Real.pi) :
    Real.sin x + Real.sin y + Real.sin z ≤ 3 * Real.sin ((x + y + z) / 3) := by
  obtain ⟨hx0, hxp⟩ := hx
  obtain ⟨hy0, hyp⟩ := hy
  obtain ⟨hz0, hzp⟩ := hz
  set m := (x + y + z) / 3 with hm
  have hmem : m ∈ Set.Icc 0 Real.pi := ⟨by linarith, by linarith⟩
  have hmem2 : (x + y) / 2 ∈ Set.Icc 0 Real.pi := ⟨by linarith, by linarith⟩
  have hmem3 : (z + m) / 2 ∈ Set.Icc 0 Real.pi := ⟨by linarith, by linarith⟩
  have step1 := sin_pair_le ⟨hx0, hxp⟩ ⟨hy0, hyp⟩
  have step2 := sin_pair_le ⟨hz0, hzp⟩ hmem
  have step3 := sin_pair_le hmem2 hmem3
  have key : ((x + y) / 2 + (z + m) / 2) / 2 = m := by rw [hm]; ring
  rw [key] at step3
  linarith [step1, step2, step3]

/-- Equality case of `sin_jensen_three`: the three points coincide. -/
lemma sin_jensen_three_eq {x y z : ℝ} (hx : x ∈ Set.Icc 0 Real.pi)
    (hy : y ∈ Set.Icc 0 Real.pi) (hz : z ∈ Set.Icc 0 Real.pi)
    (heq : Real.sin x + Real.sin y + Real.sin z = 3 * Real.sin ((x + y + z) / 3)) :
    x = y ∧ y = z := by
  obtain ⟨hx0, hxp⟩ := hx
  obtain ⟨hy0, hyp⟩ := hy
  obtain ⟨hz0, hzp⟩ := hz
  set m := (x + y + z) / 3 with hm
  have hmem : m ∈ Set.Icc 0 Real.pi := ⟨by linarith, by linarith⟩
  have hmem2 : (x + y) / 2 ∈ Set.Icc 0 Real.pi := ⟨by linarith, by linarith⟩
  have hmem3 : (z + m) / 2 ∈ Set.Icc 0 Real.pi := ⟨by linarith, by linarith⟩
  have step1 := sin_pair_le ⟨hx0, hxp⟩ ⟨hy0, hyp⟩
  have step2 := sin_pair_le ⟨hz0, hzp⟩ hmem
  have step3 := sin_pair_le hmem2 hmem3
  have key : ((x + y) / 2 + (z + m) / 2) / 2 = m := by rw [hm]; ring
  rw [key] at step3
  have e1 : Real.sin x + Real.sin y = 2 * Real.sin ((x + y) / 2) := by
    linarith [heq, step1, step2, step3]
  have e2 : Real.sin z + Real.sin m = 2 * Real.sin ((z + m) / 2) := by
    linarith [heq, step1, step2, step3]
  have e3 : Real.sin ((x + y) / 2) + Real.sin ((z + m) / 2) = 2 * Real.sin m := by
    linarith [heq, step1, step2, step3]
  have hxy : x = y := sin_pair_eq ⟨hx0, hxp⟩ ⟨hy0, hyp⟩ e1
  have hzm : z = m := sin_pair_eq ⟨hz0, hzp⟩ hmem e2
  have h4 : (x + y) / 2 = (z + m) / 2 := by
    apply sin_pair_eq hmem2 hmem3
    rw [key]
    exact e3
  exact ⟨hxy, by linarith⟩

/-- For `0 < x ≤ π/3`, `sin 3x ≥ 0`. -/
lemma sin_three_nonneg_of_le {x : ℝ} (h0 : 0 < x) (h : x ≤ Real.pi / 3) :
    0 ≤ Real.sin (3 * x) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)

/-- For `2π/3 ≤ x < π`, `sin 3x ≥ 0`. -/
lemma sin_three_nonneg_of_ge {x : ℝ} (h : 2 * Real.pi / 3 ≤ x) (hp : x < Real.pi) :
    0 ≤ Real.sin (3 * x) := by
  rw [← Real.sin_sub_two_pi]
  exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)

/-- For `π/3 ≤ x ≤ 2π/3`, `sin 3x ≤ 0`. -/
lemma sin_three_nonpos_of_mem {x : ℝ} (h1 : Real.pi / 3 ≤ x) (h2 : x ≤ 2 * Real.pi / 3) :
    Real.sin (3 * x) ≤ 0 := by
  have h := Real.sin_sub_pi (3 * x)
  have hpos : 0 ≤ Real.sin (3 * x - Real.pi) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  linarith

/-- Among the three angles of a triangle, at least one has nonnegative `sin 3x`. -/
lemma exists_sin_three_nonneg {A B C : ℝ} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hsum : A + B + C = Real.pi) :
    0 ≤ Real.sin (3 * A) ∨ 0 ≤ Real.sin (3 * B) ∨ 0 ≤ Real.sin (3 * C) := by
  by_contra h
  push Not at h
  obtain ⟨h1, h2, h3⟩ := h
  have key : ∀ x : ℝ, 0 < x → x < Real.pi → Real.sin (3 * x) < 0 →
      Real.pi / 3 < x ∧ x < 2 * Real.pi / 3 := by
    intro x hx0 hxp hs
    constructor
    · by_contra hc
      push Not at hc
      linarith [sin_three_nonneg_of_le hx0 hc, hs]
    · by_contra hc
      push Not at hc
      linarith [sin_three_nonneg_of_ge hc hxp, hs]
  obtain ⟨lA, -⟩ := key A hA (by linarith) h1
  obtain ⟨lB, -⟩ := key B hB (by linarith) h2
  obtain ⟨lC, -⟩ := key C hC (by linarith) h3
  linarith

/-- If `0 < x < π` and `sin 3x = -1`, then `x = π/2`. -/
lemma eq_pi_div_two_of_sin_three_eq_neg_one {x : ℝ} (h0 : 0 < x) (hp : x < Real.pi)
    (h : Real.sin (3 * x) = -1) : x = Real.pi / 2 := by
  have hcsq := Real.cos_sq_add_sin_sq (3 * x)
  rw [h] at hcsq
  have hsq : Real.cos (3 * x) ^ 2 = 0 := by linarith [hcsq]
  have hcos : Real.cos (3 * x) = 0 := sq_eq_zero_iff.mp hsq
  obtain ⟨k, hk⟩ := Real.cos_eq_zero_iff.mp hcos
  have hk0 : (0:ℝ) < 2 * k + 1 := by
    have h1 : (0:ℝ) < 3 * x := by linarith
    rw [hk] at h1
    nlinarith [h1, Real.pi_pos]
  have hk6 : (2:ℝ) * k + 1 < 6 := by
    have h1 : 3 * x < 3 * Real.pi := by linarith
    rw [hk] at h1
    nlinarith [h1, Real.pi_pos]
  have hk0' : 0 < 2 * k + 1 := by exact_mod_cast hk0
  have hk6' : 2 * k + 1 < 6 := by exact_mod_cast hk6
  have hklo : 0 ≤ k := by omega
  have hkhi : k ≤ 2 := by omega
  interval_cases k
  · have e : 3 * x = Real.pi / 2 := by
      norm_num at hk
      linarith [hk]
    rw [e, Real.sin_pi_div_two] at h
    norm_num at h
  · have e : 3 * x = 3 * Real.pi / 2 := by
      norm_num at hk
      linarith [hk]
    linarith [e]
  · have e : 3 * x = 5 * Real.pi / 2 := by
      norm_num at hk
      linarith [hk]
    have hs : Real.sin (5 * Real.pi / 2) = 1 := by
      have e2 : 5 * Real.pi / 2 = Real.pi / 2 + 2 * Real.pi := by ring
      rw [e2, Real.sin_add_two_pi, Real.sin_pi_div_two]
    rw [e, hs] at h
    norm_num at h

/-- Lower bound: if `sin 3x ≥ 0` for one angle of a triangle, then the sum of
the three sines is strictly greater than `-2`. -/
lemma lower_aux {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hsum : x + y + z = Real.pi) (h0 : 0 ≤ Real.sin (3 * x)) :
    -2 < Real.sin (3 * x) + Real.sin (3 * y) + Real.sin (3 * z) := by
  by_contra hle
  push Not at hle
  have h1 : Real.sin (3 * y) = -1 := by
    have i1 := Real.neg_one_le_sin (3 * y)
    have i2 := Real.neg_one_le_sin (3 * z)
    linarith
  have h2 : Real.sin (3 * z) = -1 := by
    have i1 := Real.neg_one_le_sin (3 * z)
    have i2 := Real.neg_one_le_sin (3 * y)
    linarith
  have hy2 := eq_pi_div_two_of_sin_three_eq_neg_one hy (by linarith) h1
  have hz2 := eq_pi_div_two_of_sin_three_eq_neg_one hz (by linarith) h2
  linarith

/-- Upper bound on the shifted variables: if `x y z'` are positive with sum `π/3`,
then `sin 3x + sin 3y + sin 3z' ≤ 3√3/2`, with equality iff all equal `π/9`. -/
lemma upper_aux {x y z' : ℝ} (hx : 0 < x) (hy : 0 < y) (hz' : 0 < z')
    (hsum : x + y + z' = Real.pi / 3) :
    Real.sin (3 * x) + Real.sin (3 * y) + Real.sin (3 * z') ≤ 3 * Real.sqrt 3 / 2 ∧
    (Real.sin (3 * x) + Real.sin (3 * y) + Real.sin (3 * z') = 3 * Real.sqrt 3 / 2 →
      x = Real.pi / 9 ∧ y = Real.pi / 9 ∧ z' = Real.pi / 9) := by
  have mx : 3 * x ∈ Set.Icc 0 Real.pi := ⟨by linarith, by linarith⟩
  have my : 3 * y ∈ Set.Icc 0 Real.pi := ⟨by linarith, by linarith⟩
  have mz : 3 * z' ∈ Set.Icc 0 Real.pi := ⟨by linarith, by linarith⟩
  have hm : (3 * x + 3 * y + 3 * z') / 3 = Real.pi / 3 := by linarith
  have hJ := sin_jensen_three mx my mz
  rw [hm, Real.sin_pi_div_three] at hJ
  refine ⟨by linarith [hJ], fun heq => ?_⟩
  have hJe : Real.sin (3 * x) + Real.sin (3 * y) + Real.sin (3 * z') =
      3 * Real.sin ((3 * x + 3 * y + 3 * z') / 3) := by
    rw [hm, Real.sin_pi_div_three]
    linarith [heq]
  obtain ⟨e1, e2⟩ := sin_jensen_three_eq mx my mz hJe
  exact ⟨by linarith, by linarith, by linarith⟩

/-- At `(π/9, π/9, 7π/9)` the sum of sines equals `3√3/2`. -/
lemma sum_sin_eq {A B C : ℝ} (hA : A = Real.pi / 9) (hB : B = Real.pi / 9)
    (hC : C = 7 * Real.pi / 9) :
    Real.sin (3 * A) + Real.sin (3 * B) + Real.sin (3 * C) = 3 * Real.sqrt 3 / 2 := by
  rw [hA, hB, hC]
  have e1 : 3 * (Real.pi / 9) = Real.pi / 3 := by ring
  have e2 : 3 * (7 * Real.pi / 9) = Real.pi / 3 + 2 * Real.pi := by ring
  rw [e1, e2, Real.sin_add_two_pi, Real.sin_pi_div_three]
  ring

snip end

problem usa1981_p3 (A B C : ℝ) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hsum : A + B + C = Real.pi) :
    -2 < Real.sin (3 * A) + Real.sin (3 * B) + Real.sin (3 * C) ∧
    Real.sin (3 * A) + Real.sin (3 * B) + Real.sin (3 * C) ≤ 3 * Real.sqrt 3 / 2 ∧
    (Real.sin (3 * A) + Real.sin (3 * B) + Real.sin (3 * C) = 3 * Real.sqrt 3 / 2 ↔
      (A = Real.pi / 9 ∧ B = Real.pi / 9 ∧ C = 7 * Real.pi / 9) ∨
      (B = Real.pi / 9 ∧ C = Real.pi / 9 ∧ A = 7 * Real.pi / 9) ∨
      (C = Real.pi / 9 ∧ A = Real.pi / 9 ∧ B = 7 * Real.pi / 9)) := by
  have h23 : (2:ℝ) < 3 * Real.sqrt 3 / 2 := by
    have h1 : (4:ℝ) / 3 < Real.sqrt 3 := by
      rw [Real.lt_sqrt (show (0:ℝ) ≤ (4:ℝ) / 3 by norm_num)]
      norm_num
    linarith
  have hback : ((A = Real.pi / 9 ∧ B = Real.pi / 9 ∧ C = 7 * Real.pi / 9) ∨
      (B = Real.pi / 9 ∧ C = Real.pi / 9 ∧ A = 7 * Real.pi / 9) ∨
      (C = Real.pi / 9 ∧ A = Real.pi / 9 ∧ B = 7 * Real.pi / 9)) →
      Real.sin (3 * A) + Real.sin (3 * B) + Real.sin (3 * C) = 3 * Real.sqrt 3 / 2 := by
    rintro (⟨ha, hb, hc⟩ | ⟨hb, hc, ha⟩ | ⟨hc, ha, hb⟩)
    · exact sum_sin_eq ha hb hc
    · linarith [sum_sin_eq hb hc ha]
    · linarith [sum_sin_eq hc ha hb]
  have hlower : -2 < Real.sin (3 * A) + Real.sin (3 * B) + Real.sin (3 * C) := by
    rcases exists_sin_three_nonneg hA hB hC hsum with h0 | h0 | h0
    · exact lower_aux hA hB hC hsum h0
    · linarith [lower_aux hB hC hA (by linarith) h0]
    · linarith [lower_aux hC hA hB (by linarith) h0]
  have hupper : Real.sin (3 * A) + Real.sin (3 * B) + Real.sin (3 * C) ≤
      3 * Real.sqrt 3 / 2 ∧
      (Real.sin (3 * A) + Real.sin (3 * B) + Real.sin (3 * C) = 3 * Real.sqrt 3 / 2 →
        (A = Real.pi / 9 ∧ B = Real.pi / 9 ∧ C = 7 * Real.pi / 9) ∨
        (B = Real.pi / 9 ∧ C = Real.pi / 9 ∧ A = 7 * Real.pi / 9) ∨
        (C = Real.pi / 9 ∧ A = Real.pi / 9 ∧ B = 7 * Real.pi / 9)) := by
    by_cases hpos : (0 < Real.sin (3 * A)) ∧ (0 < Real.sin (3 * B)) ∧
        (0 < Real.sin (3 * C))
    · obtain ⟨sA, sB, sC⟩ := hpos
      have hbig : 2 * Real.pi / 3 < A ∨ 2 * Real.pi / 3 < B ∨ 2 * Real.pi / 3 < C := by
        by_contra hc
        push Not at hc
        obtain ⟨cA, cB, cC⟩ := hc
        have hA3 : A < Real.pi / 3 := by
          by_contra hcc
          push Not at hcc
          linarith [sin_three_nonpos_of_mem hcc cA, sA]
        have hB3 : B < Real.pi / 3 := by
          by_contra hcc
          push Not at hcc
          linarith [sin_three_nonpos_of_mem hcc cB, sB]
        have hC3 : C < Real.pi / 3 := by
          by_contra hcc
          push Not at hcc
          linarith [sin_three_nonpos_of_mem hcc cC, sC]
        linarith
      rcases hbig with hbig | hbig | hbig
      · have hA' : 0 < A - 2 * Real.pi / 3 := by linarith
        have hsum' : B + C + (A - 2 * Real.pi / 3) = Real.pi / 3 := by linarith
        obtain ⟨hu, he⟩ := upper_aux hB hC hA' hsum'
        have hsA : Real.sin (3 * A) = Real.sin (3 * (A - 2 * Real.pi / 3)) := by
          have e : 3 * A = 3 * (A - 2 * Real.pi / 3) + 2 * Real.pi := by ring
          rw [e, Real.sin_add_two_pi]
        refine ⟨by linarith, fun heq => ?_⟩
        obtain ⟨hB9, hC9, hA9⟩ := he (by linarith)
        exact Or.inr (Or.inl ⟨hB9, hC9, by linarith⟩)
      · have hB' : 0 < B - 2 * Real.pi / 3 := by linarith
        have hsum' : C + A + (B - 2 * Real.pi / 3) = Real.pi / 3 := by linarith
        obtain ⟨hu, he⟩ := upper_aux hC hA hB' hsum'
        have hsB : Real.sin (3 * B) = Real.sin (3 * (B - 2 * Real.pi / 3)) := by
          have e : 3 * B = 3 * (B - 2 * Real.pi / 3) + 2 * Real.pi := by ring
          rw [e, Real.sin_add_two_pi]
        refine ⟨by linarith, fun heq => ?_⟩
        obtain ⟨hC9, hA9, hB9⟩ := he (by linarith)
        exact Or.inr (Or.inr ⟨hC9, hA9, by linarith⟩)
      · have hC' : 0 < C - 2 * Real.pi / 3 := by linarith
        have hsum' : A + B + (C - 2 * Real.pi / 3) = Real.pi / 3 := by linarith
        obtain ⟨hu, he⟩ := upper_aux hA hB hC' hsum'
        have hsC : Real.sin (3 * C) = Real.sin (3 * (C - 2 * Real.pi / 3)) := by
          have e : 3 * C = 3 * (C - 2 * Real.pi / 3) + 2 * Real.pi := by ring
          rw [e, Real.sin_add_two_pi]
        refine ⟨by linarith, fun heq => ?_⟩
        obtain ⟨hA9, hB9, hC9⟩ := he (by linarith)
        exact Or.inl ⟨hA9, hB9, by linarith⟩
    · have hS2 : Real.sin (3 * A) + Real.sin (3 * B) + Real.sin (3 * C) ≤ 2 := by
        by_contra hS
        push Not at hS
        apply hpos
        exact ⟨by linarith [Real.sin_le_one (3 * B), Real.sin_le_one (3 * C)],
               by linarith [Real.sin_le_one (3 * A), Real.sin_le_one (3 * C)],
               by linarith [Real.sin_le_one (3 * A), Real.sin_le_one (3 * B)]⟩
      exact ⟨by linarith, fun heq => absurd heq (by linarith)⟩
  exact ⟨hlower, hupper.1, ⟨hupper.2, hback⟩⟩

end Usa1981P3
