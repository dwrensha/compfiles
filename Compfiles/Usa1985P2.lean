/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Algebra] }

/-!
# USA Mathematical Olympiad 1985, Problem 2

Find all real roots of the quartic x⁴ - (2N + 1)x² - x + N² + N - 1 = 0
correct to 4 decimal places, where N = 10¹⁰.
-/

namespace Usa1985P2

snip begin

/-- The quartic of the problem rewrites as `(x² - N - 1/2)² - x - 5/4`;
this is the key observation of the solution
(see https://prase.cz/kalva/usa/usoln/usol852.html). -/
lemma quartic_eq (N x : ℝ) :
    x ^ 4 - (2 * N + 1) * x ^ 2 - x + N ^ 2 + N - 1 =
      (x ^ 2 - N - 1 / 2) ^ 2 - x - 5 / 4 := by
  ring

/-- The function whose zeros are the real roots of the quartic. -/
noncomputable def f (N : ℝ) (x : ℝ) : ℝ := (x ^ 2 - N - 1 / 2) ^ 2 - x - 5 / 4

lemma f_def (N : ℝ) (x : ℝ) : f N x = (x ^ 2 - N - 1 / 2) ^ 2 - x - 5 / 4 := rfl

lemma f_continuous (N : ℝ) : Continuous (f N) := by
  unfold f
  continuity

/-- A sign change of `f N` on an interval locates a root in its interior. -/
lemma exists_root_of_sign_change {N : ℝ} {a b : ℝ} (hab : a ≤ b)
    (h : f N a * f N b < 0) : ∃ x ∈ Set.Ioo a b, f N x = 0 := by
  have hc : ContinuousOn (f N) (Set.Icc a b) := (f_continuous N).continuousOn
  rcases mul_neg_iff.mp h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · obtain ⟨x, hx, hfx⟩ :=
      intermediate_value_Ioo' hab hc (show (0:ℝ) ∈ Set.Ioo (f N b) (f N a) from ⟨hb, ha⟩)
    exact ⟨x, hx, hfx⟩
  · obtain ⟨x, hx, hfx⟩ :=
      intermediate_value_Ioo hab hc (show (0:ℝ) ∈ Set.Ioo (f N a) (f N b) from ⟨ha, hb⟩)
    exact ⟨x, hx, hfx⟩

/-- The quartic has no nonpositive real roots when `N = 10^10`:
for `x ≤ -5/4` the right side `x + 5/4` of `(x² - N - 1/2)² = x + 5/4` is too small,
and for `-5/4 < x ≤ 0` the left side is huge while the right side stays below `5/4`. -/
lemma f_pos_of_nonpos {N : ℝ} (hN : N = 10 ^ 10) {x : ℝ} (hx : x ≤ 0) :
    0 < f N x := by
  subst hN
  rw [f_def]
  rcases le_or_gt x (-5 / 4) with h | h
  · rcases lt_or_eq_of_le h with hlt | heq
    · nlinarith [sq_nonneg (x ^ 2 - (10:ℝ) ^ 10 - 1 / 2)]
    · rw [heq]; norm_num
  · have hx2 : x ^ 2 < 25 / 16 := by
      nlinarith [mul_neg_of_neg_of_pos
        (show x - 5 / 4 < (0:ℝ) by linarith)
        (show (0:ℝ) < x + 5 / 4 by linarith)]
    have hA : (10:ℝ) ^ 10 - 2 < (10:ℝ) ^ 10 + 1 / 2 - x ^ 2 := by linarith
    have hsq : ((10:ℝ) ^ 10 - 2) ^ 2 < ((10:ℝ) ^ 10 + 1 / 2 - x ^ 2) ^ 2 := by
      nlinarith [mul_pos (sub_pos.mpr hA)
        (show (0:ℝ) < ((10:ℝ) ^ 10 - 2) + ((10:ℝ) ^ 10 + 1 / 2 - x ^ 2) by linarith)]
    have hflip : (x ^ 2 - (10:ℝ) ^ 10 - 1 / 2) ^ 2 =
        ((10:ℝ) ^ 10 + 1 / 2 - x ^ 2) ^ 2 := by ring
    rw [hflip]
    nlinarith [hsq, hx]

/-- `f N` is strictly antitone on `{x ≥ 0 | x² ≤ N + 1/2}`. -/
lemma f_lt_f_of_lt {N : ℝ} {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y)
    (hy : y ^ 2 ≤ N + 1 / 2) : f N y < f N x := by
  have h1 : (0:ℝ) < y - x := sub_pos.mpr hxy
  have h2 : (0:ℝ) < y + x := by linarith
  have h3 : (0:ℝ) < y ^ 2 - x ^ 2 := by nlinarith [mul_pos h1 h2]
  have h4 : (0:ℝ) < 2 * N + 1 - x ^ 2 - y ^ 2 := by linarith
  have key : f N x - f N y =
      (y ^ 2 - x ^ 2) * (2 * N + 1 - x ^ 2 - y ^ 2) + (y - x) := by
    rw [f_def, f_def]; ring
  have h5 : (0:ℝ) < (y ^ 2 - x ^ 2) * (2 * N + 1 - x ^ 2 - y ^ 2) := mul_pos h3 h4
  linarith

/-- Hence there is at most one root in `{x ≥ 0 | x² ≤ N + 1/2}`. -/
lemma eq_of_region1 {N : ℝ} {x y : ℝ}
    (hx0 : 0 ≤ x) (hx2 : x ^ 2 ≤ N + 1 / 2) (hfx : f N x = 0)
    (hy0 : 0 ≤ y) (hy2 : y ^ 2 ≤ N + 1 / 2) (hfy : f N y = 0) : x = y := by
  rcases lt_trichotomy x y with h | h | h
  · exact absurd (f_lt_f_of_lt hx0 h hy2) (by linarith)
  · exact h
  · exact absurd (f_lt_f_of_lt hy0 h hx2) (by linarith)

/-- Two roots `x < y` lying in `{x² ≥ C}` would force
`(y + x) * ((y² - C) + (x² - C)) = 1`. -/
lemma region2_key {x y : ℝ} (hxy : x < y) (C : ℝ)
    (e1 : (x ^ 2 - C) ^ 2 = x + 5 / 4) (e2 : (y ^ 2 - C) ^ 2 = y + 5 / 4) :
    (y + x) * ((y ^ 2 - C) + (x ^ 2 - C)) = 1 := by
  have hyx : (0:ℝ) < y - x := sub_pos.mpr hxy
  have e3 := calc
    (y - x) * ((y + x) * ((y ^ 2 - C) + (x ^ 2 - C)))
    _ = ((y - x) * (y + x)) * ((y ^ 2 - C) + (x ^ 2 - C)) := by rw [mul_assoc]
    _ = (y ^ 2 - C) ^ 2 - (x ^ 2 - C) ^ 2 := by rw [sq_sub_sq, sub_sub_sub_cancel_right, sq_sub_sq, mul_comm, mul_comm (y + x)]
    _ = (y - x) * 1 := by rw [e2, e1]; ring
  exact mul_left_cancel₀ (ne_of_gt hyx) e3

/-- But for `N = 10^10` two roots in `{x² ≥ N + 1/2}` are impossible:
the left side of the identity above exceeds `2 * 10^5 * 316`. -/
lemma region2_aux {N : ℝ} (hN : N = 10 ^ 10) {x y : ℝ}
    (hx0 : 0 ≤ x) (hx2 : N + 1 / 2 ≤ x ^ 2) (hfx : f N x = 0)
    (hxy : x < y) (hy2 : N + 1 / 2 ≤ y ^ 2) (hfy : f N y = 0) : False := by
  subst hN
  rw [f_def] at hfx hfy
  have e1 : (x ^ 2 - ((10:ℝ) ^ 10 + 1 / 2)) ^ 2 = x + 5 / 4 := by
    have h1 : x ^ 2 - ((10:ℝ) ^ 10 + 1 / 2) = x ^ 2 - (10:ℝ) ^ 10 - 1 / 2 := by ring
    rw [h1]; linarith [hfx]
  have e2 : (y ^ 2 - ((10:ℝ) ^ 10 + 1 / 2)) ^ 2 = y + 5 / 4 := by
    have h1 : y ^ 2 - ((10:ℝ) ^ 10 + 1 / 2) = y ^ 2 - (10:ℝ) ^ 10 - 1 / 2 := by ring
    rw [h1]; linarith [hfy]
  have e6 := region2_key hxy ((10:ℝ) ^ 10 + 1 / 2) e1 e2
  have hx5 : (10:ℝ) ^ 5 ≤ x := by
    by_contra hlt
    push Not at hlt
    nlinarith [mul_nonneg hx0 (show (0:ℝ) ≤ (10:ℝ) ^ 5 - x by linarith)]
  have hA0 : (0:ℝ) ≤ x ^ 2 - ((10:ℝ) ^ 10 + 1 / 2) := by linarith
  have hB0 : (0:ℝ) ≤ y ^ 2 - ((10:ℝ) ^ 10 + 1 / 2) := by linarith
  have hA316 : (316:ℝ) < x ^ 2 - ((10:ℝ) ^ 10 + 1 / 2) := by
    by_contra hle
    push Not at hle
    have hsq : (x ^ 2 - ((10:ℝ) ^ 10 + 1 / 2)) ^ 2 ≤ (316:ℝ) ^ 2 := by
      nlinarith [mul_nonneg hA0
        (show (0:ℝ) ≤ 316 - (x ^ 2 - ((10:ℝ) ^ 10 + 1 / 2)) by linarith)]
    nlinarith [hsq, e1, hx5]
  have hle1 : (y + x) * (x ^ 2 - ((10:ℝ) ^ 10 + 1 / 2)) ≤ 1 := by
    have hsum : x ^ 2 - ((10:ℝ) ^ 10 + 1 / 2) ≤
        (y ^ 2 - ((10:ℝ) ^ 10 + 1 / 2)) + (x ^ 2 - ((10:ℝ) ^ 10 + 1 / 2)) := by linarith
    have h := mul_le_mul_of_nonneg_left hsum (show (0:ℝ) ≤ y + x by linarith)
    rw [e6] at h
    exact h
  have hle2 : (2:ℝ) * 10 ^ 5 * (x ^ 2 - ((10:ℝ) ^ 10 + 1 / 2)) ≤
      (y + x) * (x ^ 2 - ((10:ℝ) ^ 10 + 1 / 2)) :=
    mul_le_mul_of_nonneg_right (show (2:ℝ) * 10 ^ 5 ≤ y + x by linarith) hA0
  have hle3 : (2:ℝ) * 10 ^ 5 * 316 ≤
      (2:ℝ) * 10 ^ 5 * (x ^ 2 - ((10:ℝ) ^ 10 + 1 / 2)) :=
    mul_le_mul_of_nonneg_left (le_of_lt hA316) (by norm_num)
  nlinarith [hle1, hle2, hle3]

/-- At most one root in `{x ≥ 0 | x² ≥ N + 1/2}`. -/
lemma eq_of_region2 {N : ℝ} (hN : N = 10 ^ 10) {x y : ℝ}
    (hx0 : 0 ≤ x) (hx2 : N + 1 / 2 ≤ x ^ 2) (hfx : f N x = 0)
    (hy0 : 0 ≤ y) (hy2 : N + 1 / 2 ≤ y ^ 2) (hfy : f N y = 0) : x = y := by
  rcases lt_trichotomy x y with h | h | h
  · exact (region2_aux hN hx0 hx2 hfx h hy2 hfy).elim
  · exact h
  · exact (region2_aux hN hy0 hy2 hfy h hx2 hfx).elim

snip end

/-- The two real roots, correct to 4 decimal places. -/
determine answer : ℝ × ℝ := (99999.9984, 100000.0016)

problem usa1985_p2 (N : ℝ) (hN : N = 10 ^ 10) :
    ∃ x₁ x₂ : ℝ, x₁ < x₂ ∧
      (∀ x : ℝ, x ^ 4 - (2 * N + 1) * x ^ 2 - x + N ^ 2 + N - 1 = 0 ↔
        x = x₁ ∨ x = x₂) ∧
      |x₁ - answer.1| < 0.00005 ∧ |x₂ - answer.2| < 0.00005 := by
  subst hN
  -- Sign evaluations (exact rational arithmetic) locate the two roots.
  have s1 : (0:ℝ) < f (10 ^ 10) 99999.99835 := by rw [f_def]; norm_num
  have s2 : f (10 ^ 10) 99999.99845 < 0 := by rw [f_def]; norm_num
  have s3 : f (10 ^ 10) 100000.00155 < 0 := by rw [f_def]; norm_num
  have s4 : (0:ℝ) < f (10 ^ 10) 100000.00165 := by rw [f_def]; norm_num
  obtain ⟨x₁, hx₁I, hfx₁⟩ := exists_root_of_sign_change
    (show (99999.99835:ℝ) ≤ 99999.99845 by norm_num) (mul_neg_of_pos_of_neg s1 s2)
  obtain ⟨x₂, hx₂I, hfx₂⟩ := exists_root_of_sign_change
    (show (100000.00155:ℝ) ≤ 100000.00165 by norm_num) (mul_neg_of_neg_of_pos s3 s4)
  have hx₁0 : (0:ℝ) ≤ x₁ := by linarith [hx₁I.1]
  have hx₁2 : x₁ ^ 2 ≤ (10:ℝ) ^ 10 + 1 / 2 := by
    have h1 : x₁ ^ 2 ≤ (99999.99845:ℝ) ^ 2 := by
      nlinarith [mul_nonneg hx₁0 (show (0:ℝ) ≤ 99999.99845 - x₁ by linarith [hx₁I.2])]
    have h2 : (99999.99845:ℝ) ^ 2 < (10:ℝ) ^ 10 + 1 / 2 := by norm_num
    linarith
  have hx₂0 : (0:ℝ) ≤ x₂ := by linarith [hx₂I.1]
  have hx₂2 : (10:ℝ) ^ 10 + 1 / 2 ≤ x₂ ^ 2 := by
    have h1 : (100000.00155:ℝ) ^ 2 < x₂ ^ 2 := by
      nlinarith [mul_pos (show (0:ℝ) < x₂ - 100000.00155 by linarith [hx₂I.1])
        (show (0:ℝ) < x₂ + 100000.00155 by linarith [hx₂I.1])]
    have h2 : (10:ℝ) ^ 10 + 1 / 2 < (100000.00155:ℝ) ^ 2 := by norm_num
    linarith
  have hx1x2 : x₁ < x₂ := by linarith [hx₁I.2, hx₂I.1]
  have htol1 : |x₁ - answer.1| < 0.00005 := by
    show |x₁ - 99999.9984| < (0.00005:ℝ)
    rw [abs_lt]
    exact ⟨by linarith [hx₁I.1], by linarith [hx₁I.2]⟩
  have htol2 : |x₂ - answer.2| < 0.00005 := by
    show |x₂ - 100000.0016| < (0.00005:ℝ)
    rw [abs_lt]
    exact ⟨by linarith [hx₂I.1], by linarith [hx₂I.2]⟩
  refine ⟨x₁, x₂, hx1x2, fun x ↦ ?_, htol1, htol2⟩
  constructor
  · intro hx
    rw [quartic_eq, ← f_def] at hx
    rcases le_or_gt x 0 with hx0 | hx0
    · exact absurd hx (ne_of_gt (f_pos_of_nonpos rfl hx0))
    · rcases le_or_gt (x ^ 2) ((10:ℝ) ^ 10 + 1 / 2) with hx2 | hx2
      · exact Or.inl (eq_of_region1 (le_of_lt hx0) hx2 hx hx₁0 hx₁2 hfx₁)
      · exact Or.inr (eq_of_region2 rfl (le_of_lt hx0) (le_of_lt hx2) hx hx₂0 hx₂2 hfx₂)
  · rintro (rfl | rfl)
    · rw [quartic_eq, ← f_def]; exact hfx₁
    · rw [quartic_eq, ← f_def]; exact hfx₂

end Usa1985P2
