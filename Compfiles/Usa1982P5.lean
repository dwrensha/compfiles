/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Euclidean.Sphere.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# USA Mathematical Olympiad 1982, Problem 5

O is the center of a sphere S. Points A, B, C are inside S, OA is
perpendicular to AB and AC, and there are two spheres through A, B,
and C which touch S. Show that the sum of their radii equals the
radius of S.
-/

open scoped RealInnerProductSpace

namespace Usa1982P5

snip begin

/-- Squaring out the square roots: if `√(ρ² + (t + a)²) + √(ρ² + t²) = R`,
then `t` is a root of the quadratic
`4(a² - R²)t² + 4a(a² - R²)t + ((a² - R²)² - 4R²ρ²) = 0`. -/
lemma quad_eq_of_sqrt_sum_eq {a R ρ t : ℝ}
    (h : Real.sqrt (ρ ^ 2 + (t + a) ^ 2) + Real.sqrt (ρ ^ 2 + t ^ 2) = R) :
    4 * (a ^ 2 - R ^ 2) * t ^ 2 + 4 * a * (a ^ 2 - R ^ 2) * t +
      ((a ^ 2 - R ^ 2) ^ 2 - 4 * R ^ 2 * ρ ^ 2) = 0 := by
  have hs1 : 0 ≤ ρ ^ 2 + t ^ 2 := by positivity
  have hs2 : 0 ≤ ρ ^ 2 + (t + a) ^ 2 := by positivity
  have hA : Real.sqrt (ρ ^ 2 + (t + a) ^ 2) = R - Real.sqrt (ρ ^ 2 + t ^ 2) := by linarith
  have hB : ρ ^ 2 + t ^ 2 + 2 * a * t + a ^ 2 = (R - Real.sqrt (ρ ^ 2 + t ^ 2)) ^ 2 := by
    have hb : ρ ^ 2 + (t + a) ^ 2 = (R - Real.sqrt (ρ ^ 2 + t ^ 2)) ^ 2 := by
      rw [← hA, Real.sq_sqrt hs2]
    linear_combination hb
  have hC : (R - Real.sqrt (ρ ^ 2 + t ^ 2)) ^ 2 =
      R ^ 2 - 2 * R * Real.sqrt (ρ ^ 2 + t ^ 2) + (ρ ^ 2 + t ^ 2) := by
    rw [sub_sq, Real.sq_sqrt hs1]
  have hD : 2 * a * t + a ^ 2 - R ^ 2 = -2 * R * Real.sqrt (ρ ^ 2 + t ^ 2) := by
    linear_combination hB + hC
  have hE : (2 * a * t + a ^ 2 - R ^ 2) ^ 2 = (2 * R) ^ 2 * (ρ ^ 2 + t ^ 2) := by
    rw [hD, show (-2 * R * Real.sqrt (ρ ^ 2 + t ^ 2)) ^ 2 =
        (2 * R) ^ 2 * (Real.sqrt (ρ ^ 2 + t ^ 2)) ^ 2 by ring, Real.sq_sqrt hs1]
  linear_combination hE

/-- The one-dimensional core of the problem. The set of points `X` in the plane
with `OX + XA = R` is an ellipse with foci `O, A` (where `0 < a = OA < R`).
A line parallel to `OA` meets it in at most two points; if `t₁ ≠ t₂` are the
parameters (signed distances along the line, measured from `A`'s perpendicular)
of two intersection points, then the sum of the two corresponding radii
`√(ρ² + tᵢ²)` equals `R`. This is because the quadratic equation for `t` has
the two roots `t₁, t₂`, so `t₁ + t₂ = -a` by Vieta, hence
`√(ρ² + t₂²) = √(ρ² + (t₁ + a)²)`. -/
lemma sqrt_add_sqrt_eq_of_ne {a R ρ t₁ t₂ : ℝ} (ha : 0 < a) (haR : a < R) (ht : t₁ ≠ t₂)
    (h₁ : Real.sqrt (ρ ^ 2 + (t₁ + a) ^ 2) + Real.sqrt (ρ ^ 2 + t₁ ^ 2) = R)
    (h₂ : Real.sqrt (ρ ^ 2 + (t₂ + a) ^ 2) + Real.sqrt (ρ ^ 2 + t₂ ^ 2) = R) :
    Real.sqrt (ρ ^ 2 + t₁ ^ 2) + Real.sqrt (ρ ^ 2 + t₂ ^ 2) = R := by
  have hp₁ := quad_eq_of_sqrt_sum_eq h₁
  have hp₂ := quad_eq_of_sqrt_sum_eq h₂
  have hsub : (t₁ - t₂) * (4 * (a ^ 2 - R ^ 2) * (t₁ + t₂) + 4 * a * (a ^ 2 - R ^ 2)) = 0 := by
    linear_combination hp₁ - hp₂
  have haR2 : a ^ 2 < R ^ 2 := by
    have h := mul_pos (sub_pos.mpr haR) (show 0 < R + a by linarith)
    nlinarith
  have hK : 4 * (a ^ 2 - R ^ 2) ≠ 0 :=
    mul_ne_zero (by norm_num) (sub_ne_zero.mpr (ne_of_lt haR2))
  have h0 : 4 * (a ^ 2 - R ^ 2) * (t₁ + t₂) + 4 * a * (a ^ 2 - R ^ 2) = 0 := by
    rcases mul_eq_zero.mp hsub with h | h
    · exact absurd h (sub_ne_zero.mpr ht)
    · exact h
  have h0' : 4 * (a ^ 2 - R ^ 2) * (t₁ + t₂) = 4 * (a ^ 2 - R ^ 2) * (-a) := by
    linear_combination h0
  have hsum : t₁ + t₂ = -a := mul_left_cancel₀ hK h0'
  have hsq : t₂ ^ 2 = (t₁ + a) ^ 2 := by
    have ht2 : t₂ = -a - t₁ := by linarith
    rw [ht2]; ring
  rw [hsq, add_comm]
  exact h₁

/-- A point `X` equidistant from `Y` and `Z` satisfies
`⟪X, Z - Y⟫ = (‖Z‖² - ‖Y‖²)/2`. -/
lemma inner_eq_of_dist_eq {X Y Z : EuclideanSpace ℝ (Fin 3)} (h : dist X Y = dist X Z) :
    ⟪X, Z - Y⟫ = (‖Z‖ ^ 2 - ‖Y‖ ^ 2) / 2 := by
  have h2 : ‖X - Y‖ ^ 2 = ‖X - Z‖ ^ 2 := by
    rw [← dist_eq_norm, ← dist_eq_norm, h]
  rw [norm_sub_sq_real, norm_sub_sq_real] at h2
  rw [inner_sub_right]
  linarith

/-- If `z` is orthogonal to `v₁` and `v₂`, it lies in the orthogonal complement
of the span of `![v₁, v₂]`. -/
lemma mem_orthogonal_span_range_pair {z v₁ v₂ : EuclideanSpace ℝ (Fin 3)}
    (h₁ : ⟪z, v₁⟫ = 0) (h₂ : ⟪z, v₂⟫ = 0) :
    z ∈ (Submodule.span ℝ (Set.range ![v₁, v₂]))ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro v hv
  rw [Submodule.mem_span_range_iff_exists_fun] at hv
  obtain ⟨c, rfl⟩ := hv
  have h₁' : ⟪v₁, z⟫ = 0 := by rw [real_inner_comm]; exact h₁
  have h₂' : ⟪v₂, z⟫ = 0 := by rw [real_inner_comm]; exact h₂
  rw [Fin.sum_univ_two, inner_add_left, real_inner_smul_left, real_inner_smul_left]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [h₁', h₂', mul_zero, mul_zero, add_zero]

/-- Pythagoras: if `û` is a unit vector, `w` is orthogonal to it and
`v = w + s • û`, then `‖v‖ = √(‖w‖² + s²)`. -/
lemma norm_eq_sqrt_add_sq {w û v : EuclideanSpace ℝ (Fin 3)} {s : ℝ}
    (hû : ‖û‖ = 1) (horth : ⟪w, û⟫ = 0) (hv : v = w + s • û) :
    ‖v‖ = Real.sqrt (‖w‖ ^ 2 + s ^ 2) := by
  have horth' : ⟪w, s • û⟫ = 0 := by rw [real_inner_smul_right, horth, mul_zero]
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_real horth'
  rw [← hv] at h
  have hs : ‖s • û‖ * ‖s • û‖ = s ^ 2 := by
    rw [norm_smul, hû, mul_one, Real.norm_eq_abs, ← pow_two, sq_abs]
  rw [hs] at h
  have h2 : ‖v‖ ^ 2 = ‖w‖ ^ 2 + s ^ 2 := by linear_combination h
  rw [← h2]
  exact (Real.sqrt_sq (norm_nonneg _)).symm

/-- The distance from a point `X` to `A`, decomposed orthogonally along a unit
vector `û`: `dist X A = √(‖w‖² + t²)` where `t = ⟪X - A, û⟫` is the component
of `X - A` along `û` and `w` is the perpendicular component. -/
lemma dist_eq_sqrt_left {X A û : EuclideanSpace ℝ (Fin 3)} (hû : ‖û‖ = 1) :
    dist X A = Real.sqrt (‖(X - A) - ⟪X - A, û⟫ • û‖ ^ 2 + ⟪X - A, û⟫ ^ 2) := by
  have horth : ⟪(X - A) - ⟪X - A, û⟫ • û, û⟫ = 0 := by
    rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hû]
    ring
  have hdecomp : X - A = ((X - A) - ⟪X - A, û⟫ • û) + ⟪X - A, û⟫ • û :=
    (sub_add_cancel _ _).symm
  rw [dist_eq_norm]
  exact norm_eq_sqrt_add_sq hû horth hdecomp

/-- The distance from `O` to `X`, where `û` is the unit vector along `A - O`
and `a = ‖A - O‖`: `dist O X = √(‖w‖² + (t + a)²)` with `w, t` as in
`dist_eq_sqrt_left`. -/
lemma dist_eq_sqrt_right {O X A û : EuclideanSpace ℝ (Fin 3)}
    (hû : ‖û‖ = 1) (hu : A - O = ‖A - O‖ • û) :
    dist O X = Real.sqrt (‖(X - A) - ⟪X - A, û⟫ • û‖ ^ 2 + (⟪X - A, û⟫ + ‖A - O‖) ^ 2) := by
  have horth : ⟪(X - A) - ⟪X - A, û⟫ • û, û⟫ = 0 := by
    rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hû]
    ring
  have hdecomp : X - O = ((X - A) - ⟪X - A, û⟫ • û) + (⟪X - A, û⟫ + ‖A - O‖) • û := by
    rw [add_smul, ← hu]
    abel
  rw [dist_eq_norm, show O - X = -(X - O) by abel, norm_neg]
  exact norm_eq_sqrt_add_sq hû horth hdecomp

snip end

problem usa1982_p5
    (O A B C : EuclideanSpace ℝ (Fin 3)) (R : ℝ)
    (s₁ s₂ : EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin 3)))
    (hR : 0 < R)
    (hA : dist A O < R) (hB : dist B O < R) (hC : dist C O < R)
    (hAO : A ≠ O)
    (hAB : ⟪A - O, B - A⟫ = 0) (hAC : ⟪A - O, C - A⟫ = 0)
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hA₁ : A ∈ s₁) (hB₁ : B ∈ s₁) (hC₁ : C ∈ s₁)
    (hA₂ : A ∈ s₂) (hB₂ : B ∈ s₂) (hC₂ : C ∈ s₂)
    -- The spheres touch `S` internally: the distance from `O` to the center
    -- plus the radius equals `R`. (External tangency is impossible since the
    -- spheres pass through `A`, which lies strictly inside `S`.)
    (ht₁ : dist O s₁.center + s₁.radius = R)
    (ht₂ : dist O s₂.center + s₂.radius = R)
    (hne : s₁ ≠ s₂) :
    s₁.radius + s₂.radius = R := by
  rw [EuclideanGeometry.mem_sphere] at hA₁ hB₁ hC₁ hA₂ hB₂ hC₂
  set P := s₁.center with hP
  set Q := s₂.center with hQ
  -- The two centers are distinct (equal centers would give equal spheres).
  have centers_ne : P ≠ Q := by
    intro h
    apply hne
    rw [EuclideanGeometry.Sphere.ext_iff]
    refine ⟨h, ?_⟩
    rw [← hA₁, ← hA₂, h]
  -- Both centers are equidistant from `A`, `B` and `C`.
  have hdP_AB : dist P A = dist P B := by rw [dist_comm P A, dist_comm P B, hA₁, hB₁]
  have hdP_AC : dist P A = dist P C := by rw [dist_comm P A, dist_comm P C, hA₁, hC₁]
  have hdQ_AB : dist Q A = dist Q B := by rw [dist_comm Q A, dist_comm Q B, hA₂, hB₂]
  have hdQ_AC : dist Q A = dist Q C := by rw [dist_comm Q A, dist_comm Q C, hA₂, hC₂]
  have hPiB := inner_eq_of_dist_eq hdP_AB
  have hPiC := inner_eq_of_dist_eq hdP_AC
  have hQiB := inner_eq_of_dist_eq hdQ_AB
  have hQiC := inner_eq_of_dist_eq hdQ_AC
  have hPQB : ⟪P - Q, B - A⟫ = 0 := by rw [inner_sub_left]; linarith [hPiB, hQiB]
  have hPQC : ⟪P - Q, C - A⟫ = 0 := by rw [inner_sub_left]; linarith [hPiC, hQiC]
  -- Non-collinearity of `A, B, C` gives linear independence of `B - A`, `C - A`.
  have hli : LinearIndependent ℝ ![B - A, C - A] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    rw [Fin.sum_univ_two] at hg
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hg
    have hw := (affineIndependent_iff_of_fintype (k := ℝ) ![A, B, C]).mp hABC
    set w : Fin 3 → ℝ := ![-(g 0 + g 1), g 0, g 1] with hwdef
    have hsum : ∑ i, w i = 0 := by
      rw [hwdef, Fin.sum_univ_three]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      ring
    have hcomb : Finset.univ.weightedVSub ![A, B, C] w = 0 := by
      rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero Finset.univ w ![A, B, C]
          hsum A,
        Finset.weightedVSubOfPoint_apply Finset.univ w ![A, B, C] A, Fin.sum_univ_three]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, vsub_eq_sub]
      rw [hwdef]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      rw [sub_self, smul_zero, zero_add]
      exact hg
    have h0 := hw w hsum hcomb 1
    have h1 := hw w hsum hcomb 2
    rw [hwdef] at h0 h1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h0 h1
    fin_cases i
    · simpa using h0
    · simpa using h1
  -- The locus of points equidistant from `A, B, C` is the line through the
  -- circumcenter perpendicular to the plane `ABC`; it is parallel to `OA`.
  set W := Submodule.span ℝ (Set.range ![B - A, C - A]) with hWdef
  have hW2 : Module.finrank ℝ W = 2 := by
    rw [hWdef, finrank_span_eq_card hli, Fintype.card_fin]
  have hWo : Module.finrank ℝ Wᗮ = 1 := by
    have h := Submodule.finrank_add_finrank_orthogonal W
    rw [hW2, finrank_euclideanSpace_fin] at h
    omega
  have huW : A - O ∈ Wᗮ := mem_orthogonal_span_range_pair hAB hAC
  have hu0 : A - O ≠ 0 := sub_ne_zero.mpr hAO
  have hle : ℝ ∙ (A - O) ≤ Wᗮ := by
    rw [Submodule.span_singleton_le_iff_mem]
    exact huW
  have hspan : Wᗮ = ℝ ∙ (A - O) :=
    (Submodule.eq_of_le_of_finrank_eq hle (by rw [finrank_span_singleton hu0, hWo])).symm
  have hPQW : P - Q ∈ Wᗮ := mem_orthogonal_span_range_pair hPQB hPQC
  rw [hspan, Submodule.mem_span_singleton] at hPQW
  obtain ⟨μ, hμ⟩ := hPQW
  -- Introduce the unit vector `û` along `OA` and the coordinates along it.
  set û := ‖A - O‖⁻¹ • (A - O) with hûdef
  have ha0 : 0 < ‖A - O‖ := norm_pos_iff.mpr hu0
  have hû : ‖û‖ = 1 := by
    rw [hûdef, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ha0,
      inv_mul_cancel₀ (ne_of_gt ha0)]
  have hu_eq : A - O = ‖A - O‖ • û := by
    rw [hûdef, smul_smul, mul_inv_cancel₀ (ne_of_gt ha0), one_smul]
  have huu : ⟪A - O, û⟫ = ‖A - O‖ := by
    rw [hûdef, real_inner_smul_right, real_inner_self_eq_norm_sq, inv_mul_eq_div, pow_two,
      mul_div_assoc, div_self (ne_of_gt ha0), mul_one]
  set tP := ⟪P - A, û⟫ with htP
  set tQ := ⟪Q - A, û⟫ with htQ
  set wP := (P - A) - tP • û with hwP
  set wQ := (Q - A) - tQ • û with hwQ
  set ρ := ‖wP‖ with hρ
  -- The perpendicular components of `P - A` and `Q - A` coincide, and `tP ≠ tQ`.
  have h1 : tP - tQ = μ * ‖A - O‖ := by
    have hsub : tP - tQ = ⟪P - Q, û⟫ := by
      rw [htP, htQ, ← inner_sub_left, sub_sub_sub_cancel_right]
    rw [hsub, ← hμ, real_inner_smul_left, huu]
  have hw : wP = wQ := by
    have h2 : wP - wQ = (P - Q) - (tP - tQ) • û := by
      rw [hwP, hwQ, sub_smul]
      abel
    have h3 : wP - wQ = 0 := by
      rw [h2, h1, mul_smul, ← hu_eq, hμ, sub_self]
    exact sub_eq_zero.mp h3
  have htne : tP ≠ tQ := by
    intro h
    have hμ0 : μ = 0 := by
      have h0 : μ * ‖A - O‖ = 0 := by rw [← h1, h, sub_self]
      exact (mul_eq_zero.mp h0).resolve_right (ne_of_gt ha0)
    have hPQ : P = Q := by
      rw [← sub_eq_zero, ← hμ, hμ0, zero_smul]
    exact centers_ne hPQ
  have hρQ : ‖wQ‖ = ρ := by rw [hρ, hw]
  -- Express all relevant distances in terms of `ρ`, `tP`, `tQ` and `a = ‖A - O‖`.
  have hPA : dist P A = Real.sqrt (ρ ^ 2 + tP ^ 2) := by
    have h := dist_eq_sqrt_left hû (X := P) (A := A)
    rw [← htP, ← hwP, ← hρ] at h
    exact h
  have hQA : dist Q A = Real.sqrt (ρ ^ 2 + tQ ^ 2) := by
    have h := dist_eq_sqrt_left hû (X := Q) (A := A)
    rw [← htQ, ← hwQ, hρQ] at h
    exact h
  have hPO : dist O P = Real.sqrt (ρ ^ 2 + (tP + ‖A - O‖) ^ 2) := by
    have h := dist_eq_sqrt_right hû hu_eq (X := P) (A := A) (O := O)
    rw [← htP, ← hwP, ← hρ] at h
    exact h
  have hQO : dist O Q = Real.sqrt (ρ ^ 2 + (tQ + ‖A - O‖) ^ 2) := by
    have h := dist_eq_sqrt_right hû hu_eq (X := Q) (A := A) (O := O)
    rw [← htQ, ← hwQ, hρQ] at h
    exact h
  -- Tangency gives the two ellipse equations `OX + XA = R`.
  have hr1 : s₁.radius = dist P A := by rw [← hA₁, dist_comm]
  have hr2 : s₂.radius = dist Q A := by rw [← hA₂, dist_comm]
  have hfP : Real.sqrt (ρ ^ 2 + (tP + ‖A - O‖) ^ 2) + Real.sqrt (ρ ^ 2 + tP ^ 2) = R := by
    rw [← hPO, ← hPA, ← hr1]
    exact ht₁
  have hfQ : Real.sqrt (ρ ^ 2 + (tQ + ‖A - O‖) ^ 2) + Real.sqrt (ρ ^ 2 + tQ ^ 2) = R := by
    rw [← hQO, ← hQA, ← hr2]
    exact ht₂
  -- Apply the one-dimensional core lemma.
  have haR : ‖A - O‖ < R := by rw [← dist_eq_norm]; exact hA
  have hfinal := sqrt_add_sqrt_eq_of_ne ha0 haR htne hfP hfQ
  rw [← hPA, ← hQA] at hfinal
  rw [← hr1, ← hr2] at hfinal
  exact hfinal

end Usa1982P5
