/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw, Kimi K3
-/

module

public import Mathlib.Tactic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Euclidean.Basic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 1979, Problem 4

Given a plane k, a point P in the plane and a point Q not in the plane,
find all points R in k such that the ratio (QP + PR)/QR is a maximum.
-/

namespace Imo1979P4

open scoped RealInnerProductSpace InnerProductSpace

/-- Three-dimensional Euclidean space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The answer. Let `X` be the foot of the perpendicular from `Q` to the plane `k`.
If `X = P`, the maximizers form the circle in `k` centered at `P` with radius `QP`;
otherwise the unique maximizer is the point on the ray from `P` through `X`
whose distance from `P` equals `QP`. -/
determine maximizerSet (k : AffineSubspace ℝ E3) (P Q X : E3) : Set E3 :=
  {R | R ∈ k ∧ dist P R = dist Q P ∧
    (X = P ∨ R = (dist Q P / dist X P) • (X - P) + P)}

snip begin

/-- Pythagoras: since `QX` is perpendicular to the plane, for `R ∈ k` we have
`QR² = QX² + XR²`. -/
lemma dist_sq_eq_of_perp {k : AffineSubspace ℝ E3} {Q X : E3}
    (hX : ∀ R ∈ k, ⟪Q - X, R - X⟫_ℝ = 0) {R : E3} (hR : R ∈ k) :
    dist Q R ^ 2 = dist Q X ^ 2 + dist X R ^ 2 := by
  have h0 : ⟪Q - X, -(R - X)⟫_ℝ = 0 := by
    rw [inner_neg_right, hX R hR, neg_zero]
  have h1 := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (Q - X) (-(R - X)) h0
  have h2 : (Q - X) + -(R - X) = Q - R := by abel
  rw [h2, norm_neg] at h1
  simp only [← dist_eq_norm, ← pow_two] at h1
  rw [dist_comm R X] at h1
  exact h1

/-- The key one-variable estimate, in polynomial form: for `a² = h² + d²` with
`a > 0` and `d ≥ 0`, we have `(a + r)²(h² + (d - a)²) ≤ 4a²(h² + (d - r)²)`,
and equality forces `r = a`.  (The difference is `2a(a + d)(a - r)²`.) -/
lemma key_poly {h d a r : ℝ} (hd : 0 ≤ d) (ha : 0 < a) (ha2 : a ^ 2 = h ^ 2 + d ^ 2) :
    (a + r) ^ 2 * (h ^ 2 + (d - a) ^ 2) ≤ 4 * a ^ 2 * (h ^ 2 + (d - r) ^ 2) ∧
    (4 * a ^ 2 * (h ^ 2 + (d - r) ^ 2) ≤ (a + r) ^ 2 * (h ^ 2 + (d - a) ^ 2) → r = a) := by
  have h2' : h ^ 2 = a ^ 2 - d ^ 2 := by linarith
  have key : 4 * a ^ 2 * (h ^ 2 + (d - r) ^ 2)
      = (a + r) ^ 2 * (h ^ 2 + (d - a) ^ 2) + 2 * a * (a + d) * (a - r) ^ 2 := by
    linear_combination (4 * a ^ 2 - (a + r) ^ 2) * h2'
  have had : 0 < 2 * a * (a + d) := by positivity
  have hnn : 0 ≤ 2 * a * (a + d) * (a - r) ^ 2 := by positivity
  refine ⟨by linarith, fun hge => ?_⟩
  have hP : 2 * a * (a + d) * (a - r) ^ 2 = 0 := by linarith
  rcases mul_eq_zero.mp hP with hP | hP
  · linarith
  · have h1 : a - r = 0 := by rwa [sq_eq_zero_iff] at hP
    linarith

/-- Analysis of the ratio: writing `a = QP`, `h = QX`, `d = XP`, `r = PR`, `xR = XR`
and `qR = QR` with `QR² = QX² + XR²`, the ratio `(QP + PR)/QR` is at most
`2a / √(h² + (d - a)²)`, and equality forces `PR = QP` and `XR = |XP - QP|`. -/
lemma ratio_analysis {a h d r xR qR : ℝ} (hh : 0 < h) (hd : 0 ≤ d) (ha : 0 < a)
    (ha2 : a ^ 2 = h ^ 2 + d ^ 2) (hr : 0 ≤ r) (hxR : 0 ≤ xR) (hxRl : |d - r| ≤ xR)
    (hqR : 0 < qR) (hqR2 : qR ^ 2 = h ^ 2 + xR ^ 2) :
    (a + r) / qR ≤ 2 * a / Real.sqrt (h ^ 2 + (d - a) ^ 2) ∧
      ((a + r) / qR = 2 * a / Real.sqrt (h ^ 2 + (d - a) ^ 2) → r = a ∧ xR = |d - a|) := by
  have hD : 0 < h ^ 2 + (d - a) ^ 2 := by positivity
  have hxR2 : (d - r) ^ 2 ≤ xR ^ 2 := by
    have h1 := pow_le_pow_left₀ (abs_nonneg (d - r)) hxRl 2
    rwa [sq_abs] at h1
  have hqR2l : h ^ 2 + (d - r) ^ 2 ≤ qR ^ 2 := by linarith
  obtain ⟨kpoly, kpolyeq⟩ := key_poly hd ha ha2 (r := r)
  have hM2 : (2 * a / Real.sqrt (h ^ 2 + (d - a) ^ 2)) ^ 2
      = 4 * a ^ 2 / (h ^ 2 + (d - a) ^ 2) := by
    rw [div_pow, Real.sq_sqrt hD.le]
    congr 1
    ring
  have hf2 : ((a + r) / qR) ^ 2 = (a + r) ^ 2 / qR ^ 2 := div_pow _ _ _
  have hbound2 : (a + r) ^ 2 / qR ^ 2 ≤ 4 * a ^ 2 / (h ^ 2 + (d - a) ^ 2) := by
    have hq2 : 0 < qR ^ 2 := by positivity
    rw [div_le_iff₀ hq2, div_mul_eq_mul_div, le_div_iff₀ hD]
    have h4 : 4 * a ^ 2 * (h ^ 2 + (d - r) ^ 2) ≤ 4 * a ^ 2 * qR ^ 2 :=
      mul_le_mul_of_nonneg_left hqR2l (by positivity)
    linarith
  have hbound : (a + r) / qR ≤ 2 * a / Real.sqrt (h ^ 2 + (d - a) ^ 2) := by
    have h1 : ((a + r) / qR) ^ 2 ≤ (2 * a / Real.sqrt (h ^ 2 + (d - a) ^ 2)) ^ 2 := by
      rw [hf2, hM2]
      exact hbound2
    have hMnn : 0 ≤ 2 * a / Real.sqrt (h ^ 2 + (d - a) ^ 2) := by positivity
    have hfnn : 0 ≤ (a + r) / qR := by positivity
    have h2 := abs_le_of_sq_le_sq h1 hMnn
    rwa [abs_of_nonneg hfnn] at h2
  refine ⟨hbound, fun heq => ?_⟩
  have h1 : ((a + r) / qR) ^ 2 = (2 * a / Real.sqrt (h ^ 2 + (d - a) ^ 2)) ^ 2 := by
    rw [heq]
  rw [hf2, hM2] at h1
  rw [div_eq_div_iff (by positivity : qR ^ 2 ≠ 0) hD.ne'] at h1
  have h4 : 4 * a ^ 2 * (h ^ 2 + (d - r) ^ 2) ≤ 4 * a ^ 2 * qR ^ 2 :=
    mul_le_mul_of_nonneg_left hqR2l (by positivity)
  have heq1 : 4 * a ^ 2 * (h ^ 2 + (d - r) ^ 2) = (a + r) ^ 2 * (h ^ 2 + (d - a) ^ 2) := by
    linarith
  have hra : r = a := kpolyeq (le_of_eq heq1)
  have h5 : 4 * a ^ 2 * qR ^ 2 = 4 * a ^ 2 * (h ^ 2 + (d - r) ^ 2) := by linarith
  have h6 : qR ^ 2 = h ^ 2 + (d - r) ^ 2 :=
    mul_left_cancel₀ (by positivity : (4 : ℝ) * a ^ 2 ≠ 0) h5
  have hx2 : xR ^ 2 = (d - r) ^ 2 := by linarith
  have h7 : |xR| = |d - r| := (sq_eq_sq_iff_abs_eq_abs _ _).mp hx2
  rw [abs_of_nonneg hxR] at h7
  exact ⟨hra, by rw [h7, hra]⟩

/-- Geometric wrapper: for `R ∈ k`, the ratio `(QP + PR)/QR` is at most
`2·QP / √(QX² + (XP - QP)²)`, and equality forces `PR = QP` and `XR = |XP - QP|`. -/
lemma ratio_le_and_eq {k : AffineSubspace ℝ E3} {P Q X : E3}
    (hPk : P ∈ k) (hQk : Q ∉ k) (hXk : X ∈ k)
    (hX : ∀ R ∈ k, ⟪Q - X, R - X⟫_ℝ = 0)
    {R : E3} (hRk : R ∈ k) :
    (dist Q P + dist P R) / dist Q R ≤
        2 * dist Q P / Real.sqrt (dist Q X ^ 2 + (dist X P - dist Q P) ^ 2) ∧
      ((dist Q P + dist P R) / dist Q R =
          2 * dist Q P / Real.sqrt (dist Q X ^ 2 + (dist X P - dist Q P) ^ 2) →
        dist P R = dist Q P ∧ dist X R = |dist X P - dist Q P|) := by
  have ha : 0 < dist Q P := by
    rw [dist_pos]
    intro h
    exact hQk (h ▸ hPk)
  have hh : 0 < dist Q X := by
    rw [dist_pos]
    intro h
    exact hQk (h ▸ hXk)
  have ha2 : dist Q P ^ 2 = dist Q X ^ 2 + dist X P ^ 2 := dist_sq_eq_of_perp hX hPk
  have hqR : 0 < dist Q R := by
    rw [dist_pos]
    intro h
    exact hQk (h ▸ hRk)
  have hqR2 : dist Q R ^ 2 = dist Q X ^ 2 + dist X R ^ 2 := dist_sq_eq_of_perp hX hRk
  have hxRl : |dist X P - dist P R| ≤ dist X R := by
    have h1 := abs_dist_sub_le X R P
    rwa [dist_comm R P] at h1
  exact ratio_analysis (a := dist Q P) (h := dist Q X) (d := dist X P) (r := dist P R)
    (xR := dist X R) (qR := dist Q R) hh dist_nonneg ha ha2 dist_nonneg dist_nonneg
    hxRl hqR hqR2

/-- If `PR = QP` and `XR = |XP - QP|`, then the ratio attains the maximum value. -/
lemma ratio_eq_of {k : AffineSubspace ℝ E3} {P Q X : E3}
    (hX : ∀ R ∈ k, ⟪Q - X, R - X⟫_ℝ = 0)
    {R : E3} (hRk : R ∈ k)
    (hPR : dist P R = dist Q P) (hXR : dist X R = |dist X P - dist Q P|) :
    (dist Q P + dist P R) / dist Q R =
      2 * dist Q P / Real.sqrt (dist Q X ^ 2 + (dist X P - dist Q P) ^ 2) := by
  have hQR2 : dist Q R ^ 2 = dist Q X ^ 2 + (dist X P - dist Q P) ^ 2 := by
    have h1 := dist_sq_eq_of_perp hX hRk
    rw [hXR, sq_abs] at h1
    exact h1
  have hQR : dist Q R = Real.sqrt (dist Q X ^ 2 + (dist X P - dist Q P) ^ 2) := by
    rw [← hQR2]
    exact (Real.sqrt_sq dist_nonneg).symm
  rw [hQR, hPR, two_mul]

/-- Distances from `P` and from `X` to the point on the ray from `P` through `X`
at distance `a` from `P`. -/
lemma dist_ray_point {P X : E3} {a : ℝ} (ha : 0 < a) (hd : 0 < dist X P) :
    dist P ((a / dist X P) • (X - P) + P) = a ∧
      dist X ((a / dist X P) • (X - P) + P) = |dist X P - a| := by
  have hd' : dist X P ≠ 0 := hd.ne'
  refine ⟨?_, ?_⟩
  · rw [dist_comm P _, dist_eq_norm]
    have h1 : (a / dist X P) • (X - P) + P - P = (a / dist X P) • (X - P) := by abel
    rw [h1, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), ← dist_eq_norm]
    exact div_mul_cancel₀ _ hd'
  · have h1 : X - ((a / dist X P) • (X - P) + P) = (1 - a / dist X P) • (X - P) := by
      rw [sub_smul, one_smul]
      abel
    rw [dist_eq_norm, h1, norm_smul, Real.norm_eq_abs, ← dist_eq_norm]
    have h3 : (1 : ℝ) - a / dist X P = (dist X P - a) / dist X P := by
      field_simp
    rw [h3, abs_div, abs_of_pos hd]
    exact div_mul_cancel₀ _ hd'

/-- Equality case of the reverse triangle inequality: if `X ≠ P` and
`XR = |XP - PR|`, then `R` lies on the ray from `P` through `X`. -/
lemma eq_smul_of_dist_eq {P X R : E3} (hXP : X ≠ P)
    (h : dist X R = |dist X P - dist P R|) :
    R = (dist P R / dist X P) • (X - P) + P := by
  set v := X - P with hv
  set w := R - P with hw
  have hvv : ‖v‖ = dist X P := by rw [hv, dist_eq_norm]
  have hww : ‖w‖ = dist P R := by rw [hw, ← dist_eq_norm, dist_comm R P]
  have hv0 : ‖v‖ ≠ 0 := by
    rw [hvv]
    exact (dist_pos.mpr hXP).ne'
  have hvw : v - w = X - R := by
    rw [hv, hw]
    abel
  have h1 : ‖v - w‖ = |‖v‖ - ‖w‖| := by rw [hvw, ← dist_eq_norm, h, hvv, hww]
  have h2 := norm_sub_sq_real v w
  rw [h1, sq_abs] at h2
  have hin : ⟪v, w⟫_ℝ = ‖v‖ * ‖w‖ := by linear_combination h2 / 2
  have h3 : ‖w - (‖w‖ / ‖v‖) • v‖ ^ 2 = 0 := by
    rw [norm_sub_sq_real, real_inner_smul_right, real_inner_comm v w, hin, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    field_simp
    ring
  have h4 : w = (‖w‖ / ‖v‖) • v := by
    have h5 : w - (‖w‖ / ‖v‖) • v = 0 := by
      have h6 : ‖w - (‖w‖ / ‖v‖) • v‖ = 0 := by rwa [sq_eq_zero_iff] at h3
      rwa [norm_eq_zero] at h6
    exact sub_eq_zero.mp h5
  rw [hww, hvv, hv, hw] at h4
  exact sub_eq_iff_eq_add.mp h4

/-- In a 2-dimensional plane there is a point at any prescribed positive distance
from `P`. -/
lemma exists_mem_dist_eq {k : AffineSubspace ℝ E3} {P : E3} (hPk : P ∈ k)
    (hk : Module.finrank ℝ k.direction = 2) {a : ℝ} (ha : 0 < a) :
    ∃ R ∈ k, dist P R = a := by
  have hne : k.direction ≠ ⊥ := by
    intro hbot
    rw [hbot] at hk
    simp at hk
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨(a / ‖v‖) • v + P, ?_, ?_⟩
  · have h1 : (a / ‖v‖) • v ∈ k.direction := Submodule.smul_mem _ _ hv
    exact AffineSubspace.vadd_mem_of_mem_direction h1 hPk
  · rw [dist_comm P _, dist_eq_norm]
    have h2 : (a / ‖v‖) • v + P - P = (a / ‖v‖) • v := by abel
    rw [h2, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hvn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv0
    field_simp

snip end

problem imo1979_p4 (k : AffineSubspace ℝ E3) (hk : Module.finrank ℝ k.direction = 2)
    (P Q X : E3) (hPk : P ∈ k) (hQk : Q ∉ k) (hXk : X ∈ k)
    (hX : ∀ R ∈ k, ⟪Q - X, R - X⟫_ℝ = 0) :
    {R | R ∈ k ∧ ∀ R' ∈ k, (dist Q P + dist P R) / dist Q R ≥
        (dist Q P + dist P R') / dist Q R'} =
      maximizerSet k P Q X := by
  have ha : 0 < dist Q P := by
    rw [dist_pos]
    intro h
    exact hQk (h ▸ hPk)
  ext R
  constructor
  · rintro ⟨hRk, hRmax⟩
    obtain ⟨hle, heq⟩ := ratio_le_and_eq hPk hQk hXk hX hRk
    by_cases hXP : X = P
    · obtain ⟨R₀, hR₀k, hR₀⟩ := exists_mem_dist_eq hPk hk ha
      have hval := ratio_eq_of hX hR₀k hR₀ (by
        rw [hXP, dist_self, hR₀, abs_of_neg (by linarith : (0 : ℝ) - dist Q P < 0)]
        ring)
      have hge := hRmax R₀ hR₀k
      rw [hval] at hge
      have hFM := le_antisymm hle hge
      obtain ⟨h1, -⟩ := heq hFM
      exact ⟨hRk, h1, Or.inl hXP⟩
    · have hd : 0 < dist X P := by
        rw [dist_pos]
        exact hXP
      obtain ⟨hd1, hd2⟩ := dist_ray_point ha hd
      have hR₀k : (dist Q P / dist X P) • (X - P) + P ∈ k := by
        have h0 : X - P ∈ k.direction := AffineSubspace.vsub_mem_direction hXk hPk
        exact AffineSubspace.vadd_mem_of_mem_direction (Submodule.smul_mem _ _ h0) hPk
      have hval := ratio_eq_of hX hR₀k hd1 hd2
      have hge := hRmax _ hR₀k
      rw [hval] at hge
      have hFM := le_antisymm hle hge
      obtain ⟨h1, h2⟩ := heq hFM
      have hray : R = (dist Q P / dist X P) • (X - P) + P := by
        rw [← h1] at h2
        have h3 := eq_smul_of_dist_eq hXP h2
        rwa [h1] at h3
      exact ⟨hRk, h1, Or.inr hray⟩
  · rintro ⟨hRk, hPR, hor⟩
    refine ⟨hRk, fun R' hR'k => ?_⟩
    obtain ⟨hle', -⟩ := ratio_le_and_eq hPk hQk hXk hX hR'k
    have hval : (dist Q P + dist P R) / dist Q R =
        2 * dist Q P / Real.sqrt (dist Q X ^ 2 + (dist X P - dist Q P) ^ 2) := by
      by_cases hXP : X = P
      · refine ratio_eq_of hX hRk hPR ?_
        rw [hXP, dist_self, hPR, abs_of_neg (by linarith : (0 : ℝ) - dist Q P < 0)]
        ring
      · rcases hor with h | h
        · exact absurd h hXP
        · refine ratio_eq_of hX hRk hPR ?_
          rw [h]
          exact (dist_ray_point ha (by rw [dist_pos]; exact hXP)).2
    rw [hval]
    exact hle'

end Imo1979P4
