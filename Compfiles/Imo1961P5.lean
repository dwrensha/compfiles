/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 1961, Problem 5

Construct triangle $ABC$ if $AC = b$, $AB = c$ and $\angle AMB = \omega$,
where $M$ is the midpoint of segment $BC$ and $\omega < 90°$.
Prove that a solution exists if and only if
$$ b \tan\frac{\omega}{2} \le c < b. $$
In what case does the equality hold?
-/

namespace Imo1961P5

/-- The configuration of the problem, in coordinates (see the module
docstring): $M=(0,0)$, $B=(s,0)$, $C=(-s,0)$, $A=(r\cos\omega,r\sin\omega)$
with $r = AM$, $s = BM$; the two equations are $|AB|^2 = c^2$ and
$|AC|^2 = b^2$. `Configuration b c ω` asserts that a (genuine) triangle
with the required data exists. -/
def Configuration (b c ω : ℝ) : Prop :=
  ∃ r s : ℝ, 0 < r ∧ 0 < s ∧
    c^2 = r^2 + s^2 - 2 * r * s * Real.cos ω ∧
    b^2 = r^2 + s^2 + 2 * r * s * Real.cos ω

snip begin

/-- The half-angle identity
$\tan^2(\omega/2) = \dfrac{1-\cos\omega}{1+\cos\omega}$. -/
lemma tan_half_sq (ω : ℝ) (h : Real.cos (ω / 2) ≠ 0) :
    Real.tan (ω / 2) ^ 2 = (1 - Real.cos ω) / (1 + Real.cos ω) := by
  have hcos : Real.cos ω = 2 * Real.cos (ω / 2) ^ 2 - 1 := by
    have hc := Real.cos_two_mul (ω / 2)
    rwa [show 2 * (ω / 2) = ω by ring] at hc
  have hc2 : Real.cos (ω / 2) ^ 2 ≠ 0 := pow_ne_zero 2 h
  have hd2 : (1:ℝ) + (2 * Real.cos (ω / 2) ^ 2 - 1) ≠ 0 := by
    have hpos : (0:ℝ) < Real.cos (ω / 2) ^ 2 := sq_pos_of_ne_zero h
    nlinarith [hpos]
  rw [Real.tan_eq_sin_div_cos, div_pow, Real.sin_sq, hcos]
  field_simp [hc2, hd2]
  ring

lemma cos_pos_of_acute {ω : ℝ} (hω : 0 < ω) (hω2 : ω < Real.pi / 2) :
    0 < Real.cos ω :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hω2⟩

lemma cos_half_ne_zero_of_acute {ω : ℝ} (hω : 0 < ω) (hω2 : ω < Real.pi / 2) :
    Real.cos (ω / 2) ≠ 0 :=
  ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩)

lemma tan_half_pos_of_acute {ω : ℝ} (hω : 0 < ω) (hω2 : ω < Real.pi / 2) :
    0 < Real.tan (ω / 2) :=
  Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith) (by linarith)

/-- From the configuration, $c < b$ (because $b^2 - c^2 = 4rs\cos\omega > 0$). -/
lemma c_lt_b_of_config {b c ω : ℝ} (hb : 0 < b) (hc : 0 < c)
    (hcos : 0 < Real.cos ω) (h : Configuration b c ω) : c < b := by
  obtain ⟨r, s, hr, hs, hce, hbe⟩ := h
  have hpos : (0:ℝ) < 2 * r * s * Real.cos ω :=
    mul_pos (mul_pos (mul_pos two_pos hr) hs) hcos
  have hbc2 : c ^ 2 < b ^ 2 := by linarith [hbe, hce, hpos]
  rw [sq_lt_sq, abs_of_pos hc, abs_of_pos hb] at hbc2
  exact hbc2

/-- From the configuration, $b\tan(\omega/2) \le c$; the difference of the two
sides squared is measured by $-2(r-s)^2\cos\omega \le 0$. -/
lemma bt_le_c_of_config {b c ω : ℝ} (hb : 0 < b) (hc : 0 < c)
    (hcos : 0 < Real.cos ω) (ht : 0 < Real.tan (ω / 2))
    (ht2 : Real.tan (ω / 2) ^ 2 = (1 - Real.cos ω) / (1 + Real.cos ω))
    (h : Configuration b c ω) : b * Real.tan (ω / 2) ≤ c := by
  obtain ⟨r, s, _, _, hce, hbe⟩ := h
  have h1c : (0:ℝ) < 1 + Real.cos ω := by linarith
  have hkey : b^2 * (1 - Real.cos ω) - c^2 * (1 + Real.cos ω) =
      -2 * Real.cos ω * (r - s)^2 := by
    rw [hbe, hce]; ring
  have hle : b^2 * (1 - Real.cos ω) ≤ c^2 * (1 + Real.cos ω) := by
    have h2 : (0:ℝ) ≤ 2 * Real.cos ω * (r - s)^2 :=
      mul_nonneg (mul_nonneg (le_of_lt two_pos) (le_of_lt hcos)) (sq_nonneg _)
    linarith [hkey, h2]
  have hsq : (b * Real.tan (ω / 2)) ^ 2 ≤ c ^ 2 := by
    rw [mul_pow, ht2, ← mul_div_assoc, div_le_iff₀ h1c]
    exact hle
  rw [sq_le_sq, abs_of_nonneg (le_of_lt (mul_pos hb ht)), abs_of_pos hc] at hsq
  exact hsq

/-- The converse construction: from $b\tan(\omega/2) \le c < b$ one builds
$r, s > 0$ satisfying the two law-of-cosines equations. -/
lemma config_of_cond {b c ω : ℝ} (hb : 0 < b) (hc : 0 < c)
    (hcos : 0 < Real.cos ω) (ht : 0 < Real.tan (ω / 2))
    (ht2 : Real.tan (ω / 2) ^ 2 = (1 - Real.cos ω) / (1 + Real.cos ω))
    (hbt : b * Real.tan (ω / 2) ≤ c) (hcb : c < b) : Configuration b c ω := by
  have h1c : (0:ℝ) < 1 + Real.cos ω := by linarith
  have hcos0 : Real.cos ω ≠ 0 := ne_of_gt hcos
  have hbc2 : c ^ 2 < b ^ 2 := by
    rw [sq_lt_sq, abs_of_pos hc, abs_of_pos hb]; exact hcb
  have hsq0 : (b * Real.tan (ω / 2)) ^ 2 ≤ c ^ 2 := by
    rw [sq_le_sq, abs_of_nonneg (le_of_lt (mul_pos hb ht)), abs_of_pos hc]
    exact hbt
  have hle : b^2 * (1 - Real.cos ω) ≤ c^2 * (1 + Real.cos ω) := by
    rw [mul_pow, ht2, ← mul_div_assoc, div_le_iff₀ h1c] at hsq0
    exact hsq0
  -- $u = \frac{b^2+c^2}{2}$ and $v = \frac{b^2-c^2}{2\cos\omega}$
  set u := (b^2 + c^2) / 2 with hu
  have hu0 : 0 < u := by
    rw [hu]; linarith [pow_pos hb 2, sq_nonneg c]
  set v := (b^2 - c^2) / (2 * Real.cos ω) with hv
  have hv0 : 0 < v := by
    rw [hv]; exact div_pos (by linarith) (by linarith)
  have hvu : v ≤ u := by
    rw [hv, hu, div_le_iff₀ (by linarith : (0:ℝ) < 2 * Real.cos ω)]
    linarith [hle]
  have huv2 : v ^ 2 ≤ u ^ 2 := by
    rw [sq_le_sq, abs_of_pos hv0, abs_of_pos hu0]; exact hvu
  -- $w = \sqrt{u^2 - v^2}$, $r = \sqrt{(u+w)/2}$, $s = \sqrt{(u-w)/2}$
  set w := Real.sqrt (u^2 - v^2) with hw
  have hw2 : w ^ 2 = u ^ 2 - v ^ 2 := by
    rw [hw]; exact Real.sq_sqrt (by linarith)
  have hw0 : (0:ℝ) ≤ w := by rw [hw]; exact Real.sqrt_nonneg _
  have hwu : w < u := by
    have hwsq : w ^ 2 < u ^ 2 := by rw [hw2]; linarith [pow_pos hv0 2]
    rw [sq_lt_sq, abs_of_nonneg hw0, abs_of_pos hu0] at hwsq
    exact hwsq
  set r := Real.sqrt ((u + w) / 2) with hrw
  have hr0 : 0 < r := by rw [hrw]; exact Real.sqrt_pos.mpr (by linarith)
  have hr2 : r ^ 2 = (u + w) / 2 := by
    rw [hrw]; exact Real.sq_sqrt (by linarith)
  set s := Real.sqrt ((u - w) / 2) with hsw
  have hs0 : 0 < s := by rw [hsw]; exact Real.sqrt_pos.mpr (by linarith)
  have hs2 : s ^ 2 = (u - w) / 2 := by
    rw [hsw]; exact Real.sq_sqrt (by linarith)
  -- then $r^2 + s^2 = u$ and $2rs = v$
  have hsum : r ^ 2 + s ^ 2 = u := by rw [hr2, hs2]; ring
  have hrs : 2 * r * s = v := by
    have hsq : (2 * r * s) ^ 2 = v ^ 2 := by
      have e1 : (2 * r * s) ^ 2 = 4 * (r ^ 2) * (s ^ 2) := by ring
      have e2 : 4 * (r ^ 2) * (s ^ 2) = 4 * ((u + w) / 2) * ((u - w) / 2) := by
        rw [hr2, hs2]
      have e3 : (4:ℝ) * ((u + w) / 2) * ((u - w) / 2) = u ^ 2 - w ^ 2 := by ring
      rw [e1, e2, e3, hw2]; ring
    have h2rs : (0:ℝ) ≤ 2 * r * s :=
      mul_nonneg (mul_nonneg (le_of_lt two_pos) (le_of_lt hr0)) (le_of_lt hs0)
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
    · exact h
    · exfalso; linarith [h, h2rs, hv0]
  have hprod : 2 * r * s * Real.cos ω = (b^2 - c^2) / 2 := by
    rw [hrs, hv, div_mul_eq_mul_div, mul_div_mul_right _ _ hcos0]
  refine ⟨r, s, hr0, hs0, ?_, ?_⟩
  · rw [hsum, hprod, hu]; ring
  · rw [hsum, hprod, hu]; ring

snip end

/-- The range of `c` for which such a triangle exists. -/
determine answer (b ω : ℝ) : Set ℝ := {c : ℝ | b * Real.tan (ω / 2) ≤ c ∧ c < b}

/-- **IMO 1961 P5.** A triangle $ABC$ with $AC = b$, $AB = c$ and
$\angle AMB = \omega$ (where $M$ is the midpoint of $BC$, $\omega < 90°$)
exists if and only if $b\tan(\omega/2) \le c < b$. -/
problem imo1961_p5 (b c ω : ℝ) (hb : 0 < b) (hc : 0 < c)
    (hω : 0 < ω) (hω2 : ω < Real.pi / 2) :
    Configuration b c ω ↔ c ∈ answer b ω := by
  change Configuration b c ω ↔ b * Real.tan (ω / 2) ≤ c ∧ c < b
  have hcos := cos_pos_of_acute hω hω2
  have ht := tan_half_pos_of_acute hω hω2
  have ht2 := tan_half_sq ω (cos_half_ne_zero_of_acute hω hω2)
  exact ⟨fun h => ⟨bt_le_c_of_config hb hc hcos ht ht2 h,
                   c_lt_b_of_config hb hc hcos h⟩,
         fun ⟨hbt, hcb⟩ => config_of_cond hb hc hcos ht ht2 hbt hcb⟩

/-- **IMO 1961 P5, equality case.** Equality $b\tan(\omega/2) = c$ holds
if and only if $\angle BAC = 90^\circ$, expressed here via the Pythagorean
relation $AB^2 + AC^2 = BC^2$ (recall $BC = 2s$). -/
problem imo1961_p5_equality (b c ω r s : ℝ) (hb : 0 < b) (hc : 0 < c)
    (hω : 0 < ω) (hω2 : ω < Real.pi / 2) (hr : 0 < r) (hs : 0 < s)
    (hce : c^2 = r^2 + s^2 - 2 * r * s * Real.cos ω)
    (hbe : b^2 = r^2 + s^2 + 2 * r * s * Real.cos ω) :
    b * Real.tan (ω / 2) = c ↔ b^2 + c^2 = (2 * s)^2 := by
  have hcos := cos_pos_of_acute hω hω2
  have ht := tan_half_pos_of_acute hω hω2
  have ht2 := tan_half_sq ω (cos_half_ne_zero_of_acute hω hω2)
  have h1c : (0:ℝ) < 1 + Real.cos ω := by linarith
  have hkey : b^2 * (1 - Real.cos ω) - c^2 * (1 + Real.cos ω) =
      -2 * Real.cos ω * (r - s)^2 := by
    rw [hbe, hce]; ring
  have hsum : b^2 + c^2 = 2 * (r^2 + s^2) := by rw [hbe, hce]; ring
  constructor
  · -- If $b\tan(\omega/2) = c$ then $(r-s)^2 = 0$, hence $r = s$ and
    -- $b^2+c^2 = 2(r^2+s^2) = 4s^2$.
    intro h
    have hsq : (b * Real.tan (ω / 2)) ^ 2 = c ^ 2 := by rw [h]
    rw [mul_pow, ht2, ← mul_div_assoc, div_eq_iff h1c.ne'] at hsq
    have hrs0 : (r - s) ^ 2 = 0 := by
      have h0 : -2 * Real.cos ω * (r - s) ^ 2 = 0 := by
        have hdiff : b^2 * (1 - Real.cos ω) - c^2 * (1 + Real.cos ω) = 0 :=
          sub_eq_zero.mpr hsq
        linarith [hkey, hdiff]
      rcases mul_eq_zero.mp h0 with h1 | h1
      · exfalso; linarith [h1, hcos]
      · exact h1
    have hrs : r = s := by
      have h0 : r - s = 0 := sq_eq_zero_iff.mp hrs0
      linarith [h0]
    rw [hsum, hrs]; ring
  · -- If $b^2+c^2 = (2s)^2$ then $r = s$, hence the squared equality and
    -- by positivity $b\tan(\omega/2) = c$.
    intro h
    have hr2 : r ^ 2 = s ^ 2 := by linarith [h, hsum]
    have hrs : r = s := by
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hr2 with h1 | h1
      · exact h1
      · exfalso; linarith [h1, hr, hs]
    have hdiff0 : b^2 * (1 - Real.cos ω) = c^2 * (1 + Real.cos ω) := by
      have h0 : (r - s) ^ 2 = 0 := by rw [hrs]; ring
      have hzero : b^2 * (1 - Real.cos ω) - c^2 * (1 + Real.cos ω) = 0 := by
        rw [hkey, h0]; ring
      exact sub_eq_zero.mp hzero
    have hsq : (b * Real.tan (ω / 2)) ^ 2 = c ^ 2 := by
      rw [mul_pow, ht2, ← mul_div_assoc, div_eq_iff h1c.ne']
      exact hdiff0
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h1 | h1
    · exact h1
    · exfalso; linarith [h1, mul_pos hb ht, hc]

end Imo1961P5
