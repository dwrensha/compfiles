/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# USA Mathematical Olympiad 1998, Problem 2

Two circles are concentric. A chord AC of the outer circle touches
the inner circle at Q. P is the midpoint of AQ. A line through A
intersects the inner circle at R and S. The perpendicular bisectors
of PR and CS meet at T on the line AC. What is the ratio AT/TC?
-/

open scoped RealInnerProductSpace InnerProductSpace

namespace Usa1998P2

snip begin

/--
The tangency condition `⟪Q, C - A⟫ = 0` (the radius OQ is perpendicular to
the chord AC, with the common center O translated to the origin) together
with `‖A‖ = ‖C‖ = r₁`, `‖Q‖ = r₂` implies that `⟪A, Q⟫ = r₂²` and that Q is
the midpoint of the chord AC, i.e. `C = A + 2 • (Q - A)`.
-/
lemma chord_facts {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {r₁ r₂ : ℝ} {A C Q : V}
    (hA : ‖A‖ = r₁) (hC : ‖C‖ = r₁) (hQ : ‖Q‖ = r₂)
    (hrr : r₂ < r₁) (_hAC : A ≠ C)
    (htan : ⟪Q, C - A⟫_ℝ = 0) (hQAC : ∃ t : ℝ, Q - A = t • (C - A)) :
    ⟪A, Q⟫_ℝ = r₂^2 ∧ C = A + 2 • (Q - A) := by
  obtain ⟨t₀, ht₀⟩ := hQAC
  have hr₂nn : 0 ≤ r₂ := by rw [← hQ]; exact norm_nonneg Q
  have hpos : (0:ℝ) < r₁ + r₂ := by linarith [hrr, hr₂nn]
  have hpos2 : (0:ℝ) < r₁ - r₂ := by linarith [hrr]
  have hr1sq : (0:ℝ) < r₁^2 - r₂^2 := by nlinarith [mul_pos hpos2 hpos]
  have hQA : Q ≠ A := by
    intro h
    rw [h, hA] at hQ
    linarith [hrr]
  have ht₀ne : t₀ ≠ 0 := by
    intro h
    rw [h, zero_smul] at ht₀
    exact hQA (sub_eq_zero.mp ht₀)
  have hCA : C - A = t₀⁻¹ • (Q - A) := by
    rw [ht₀, smul_smul, inv_mul_cancel₀ ht₀ne, one_smul]
  -- The tangency condition, expressed in terms of the vector `Q - A`.
  have htan2 : ⟪Q, Q - A⟫_ℝ = 0 := by
    rw [hCA, inner_smul_right] at htan
    rcases mul_eq_zero.mp htan with h | h
    · exact absurd (inv_eq_zero.mp h) ht₀ne
    · exact h
  have hAQ : ⟪A, Q⟫_ℝ = r₂^2 := by
    have hQ2 : ⟪Q, Q⟫_ℝ = r₂^2 := by rw [real_inner_self_eq_norm_sq, hQ]
    rw [inner_sub_right] at htan2
    rw [real_inner_comm A Q] at htan2
    linarith [htan2, hQ2]
  refine ⟨hAQ, ?_⟩
  have hA2 : ⟪A, A⟫_ℝ = r₁^2 := by rw [real_inner_self_eq_norm_sq, hA]
  have hQ2 : ⟪Q, Q⟫_ℝ = r₂^2 := by rw [real_inner_self_eq_norm_sq, hQ]
  have hC2 : ⟪C, C⟫_ℝ = r₁^2 := by rw [real_inner_self_eq_norm_sq, hC]
  -- Expand `⟪C, C⟫` using `C = A + t₀⁻¹ • (Q - A)`.
  have hexp : ⟪C, C⟫_ℝ = ⟪A, A⟫_ℝ + 2 * t₀⁻¹ * (⟪A, Q⟫_ℝ - ⟪A, A⟫_ℝ) +
      t₀⁻¹ ^ 2 * (⟪Q, Q⟫_ℝ - 2 * ⟪A, Q⟫_ℝ + ⟪A, A⟫_ℝ) := by
    conv_lhs => rw [← sub_add_cancel C A, hCA]
    simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
      real_inner_smul_left, inner_smul_right, real_inner_comm A Q]
    ring
  rw [hC2, hA2, hQ2, hAQ] at hexp
  have key : (r₁^2 - r₂^2) * (t₀⁻¹ * (t₀⁻¹ - 2)) = 0 := by
    linear_combination -hexp
  rcases mul_eq_zero.mp key with h | h
  · exact absurd h (ne_of_gt hr1sq)
  · rcases mul_eq_zero.mp h with hc | hc
    · exact absurd (inv_eq_zero.mp hc) ht₀ne
    · have hc2 : t₀⁻¹ = 2 := by linarith [hc]
      rw [← sub_add_cancel C A, hCA, hc2]; module

/--
The power of the point A with respect to the inner circle: if R and S are the
two intersections of a line through A with the circle of radius r₂ centered at
the origin, and `S - A = s • (R - A)`, then `s • ‖R - A‖² = r₁² - r₂²`
(i.e. `AR · AS = AQ²`). We also record the expansion
`2 * ⟪A, R - A⟫ = -(r₁² - r₂²) - ‖R - A‖²` coming from `‖R‖ = r₂`.
-/
lemma power_of_point {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {r₁ r₂ : ℝ} {A R S : V}
    (hA : ‖A‖ = r₁) (hR : ‖R‖ = r₂) (hS : ‖S‖ = r₂) (hrr : r₂ < r₁)
    (hRS : R ≠ S) (hSAR : ∃ t : ℝ, S - A = t • (R - A)) :
    ∃ s : ℝ, s ≠ 0 ∧ s ≠ 1 ∧ S - A = s • (R - A) ∧
      2 * ⟪A, R - A⟫_ℝ = -(r₁^2 - r₂^2) - ⟪R - A, R - A⟫_ℝ ∧
      ⟪R - A, R - A⟫_ℝ * s = r₁^2 - r₂^2 := by
  obtain ⟨s, hs⟩ := hSAR
  have hA2 : ⟪A, A⟫_ℝ = r₁^2 := by rw [real_inner_self_eq_norm_sq, hA]
  have hR2 : ⟪R, R⟫_ℝ = r₂^2 := by rw [real_inner_self_eq_norm_sq, hR]
  have hS2 : ⟪S, S⟫_ℝ = r₂^2 := by rw [real_inner_self_eq_norm_sq, hS]
  have hexpR : ⟪R, R⟫_ℝ = ⟪A, A⟫_ℝ + 2 * ⟪A, R - A⟫_ℝ + ⟪R - A, R - A⟫_ℝ := by
    conv_lhs => rw [← sub_add_cancel R A]
    simp only [inner_add_left, inner_add_right, real_inner_comm A (R - A)]
    ring
  rw [hA2, hR2] at hexpR
  have hR1 : 2 * ⟪A, R - A⟫_ℝ = -(r₁^2 - r₂^2) - ⟪R - A, R - A⟫_ℝ := by
    linarith [hexpR]
  have hexpS : ⟪S, S⟫_ℝ = ⟪A, A⟫_ℝ + 2 * s * ⟪A, R - A⟫_ℝ +
      s^2 * ⟪R - A, R - A⟫_ℝ := by
    conv_lhs => rw [← sub_add_cancel S A, hs]
    simp only [inner_add_left, inner_add_right,
      real_inner_smul_left, inner_smul_right, real_inner_comm A (R - A)]
    ring
  rw [hA2, hS2] at hexpS
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hs
    have hSA : S = A := sub_eq_zero.mp hs
    rw [hSA, hA] at hS
    linarith [hrr]
  have hs1 : s ≠ 1 := by
    intro h1
    rw [h1, one_smul, sub_left_inj] at hs
    exact hRS hs.symm
  have hpow : ⟪R - A, R - A⟫_ℝ * s = r₁^2 - r₂^2 := by
    have key : (s - 1) * (s * ⟪R - A, R - A⟫_ℝ - (r₁^2 - r₂^2)) = 0 := by
      linear_combination (s : ℝ) * hexpR - hexpS
    rcases mul_eq_zero.mp key with h | h
    · exfalso; exact hs1 (by linarith [h])
    · rw [mul_comm]; linarith [h]
  exact ⟨s, hs0, hs1, hs, hR1, hpow⟩

/--
The heart of the problem, with the common center translated to the origin.
Set `u = Q - A` (the direction of the chord) and `w = R - A` (the direction of
the second line), and write `T = A + m • u`, `S = A + s • w`. The conditions
`TP = TR` and `TC = TS` become two quadratic equations in the inner products
`U = ⟪u, u⟫`, `W = ⟪w, w⟫`, `G = ⟪u, w⟫`, which combine into
`(s - 4) * (m - 5/4) = 0`. The case `s = 4` is the degenerate case where the
two perpendicular bisectors coincide and both pass through A; it is excluded
by the hypothesis `T ≠ A`. Hence `m = 5/4` and `AT/TC = (5/4)/(3/4) = 5/3`.
-/
lemma ratio_core {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {r₁ r₂ : ℝ} (hrr : r₂ < r₁)
    {A C Q P R S T : V}
    (hA : ‖A‖ = r₁) (hC : ‖C‖ = r₁) (hQ : ‖Q‖ = r₂)
    (hR : ‖R‖ = r₂) (hS : ‖S‖ = r₂)
    (hAC : A ≠ C) (htan : ⟪Q, C - A⟫_ℝ = 0)
    (hQAC : ∃ t : ℝ, Q - A = t • (C - A))
    (hP : P = midpoint ℝ A Q)
    (hRS : R ≠ S) (hSAR : ∃ t : ℝ, S - A = t • (R - A))
    (hTP : ‖T - P‖ = ‖T - R‖) (hTC : ‖T - C‖ = ‖T - S‖)
    (hTAC : ∃ t : ℝ, T - A = t • (C - A)) (hTA : T ≠ A) :
    ‖A - T‖ / ‖T - C‖ = 5 / 3 := by
  obtain ⟨hAQ, hCeq⟩ := chord_facts hA hC hQ hrr hAC htan hQAC
  obtain ⟨s, _hs0, _hs1, hSeq, hR1, hpow⟩ := power_of_point hA hR hS hrr hRS hSAR
  set u := Q - A with hu
  set w := R - A with hw
  set U := ⟪u, u⟫_ℝ with hU
  set W := ⟪w, w⟫_ℝ with hW
  set G := ⟪u, w⟫_ℝ with hG
  have hr₂nn : 0 ≤ r₂ := by rw [← hQ]; exact norm_nonneg Q
  have hpos : (0:ℝ) < r₁ + r₂ := by linarith [hrr, hr₂nn]
  have hpos2 : (0:ℝ) < r₁ - r₂ := by linarith [hrr]
  have hr1sq : (0:ℝ) < r₁^2 - r₂^2 := by nlinarith [mul_pos hpos2 hpos]
  have hA2 : ⟪A, A⟫_ℝ = r₁^2 := by rw [real_inner_self_eq_norm_sq, hA]
  have hQ2 : ⟪Q, Q⟫_ℝ = r₂^2 := by rw [real_inner_self_eq_norm_sq, hQ]
  have hQA : Q ≠ A := by
    intro h
    rw [h, hA] at hQ
    linarith [hrr]
  have hRA : R ≠ A := by
    intro h
    rw [h, hA] at hR
    linarith [hrr]
  have hu0 : u ≠ 0 := by rw [hu]; exact sub_ne_zero.mpr hQA
  have hw0 : w ≠ 0 := by rw [hw]; exact sub_ne_zero.mpr hRA
  have hUval : U = r₁^2 - r₂^2 := by
    have hexp : ⟪u, u⟫_ℝ = ⟪Q, Q⟫_ℝ - 2 * ⟪A, Q⟫_ℝ + ⟪A, A⟫_ℝ := by
      rw [hu]
      simp only [inner_sub_left, inner_sub_right, real_inner_comm A Q]
      ring
    rw [hU, hexp, hAQ, hA2, hQ2]; ring
  have hUne : U ≠ 0 := by rw [hUval]; exact ne_of_gt hr1sq
  have hpowU : s * W = U := by rw [mul_comm, hpow, hUval]
  have hAw : 2 * ⟪A, w⟫_ℝ = -U - W := by rw [← hUval] at hR1; exact hR1
  have hAu : ⟪A, u⟫_ℝ = -U := by
    have hexp : ⟪A, u⟫_ℝ = ⟪A, Q⟫_ℝ - ⟪A, A⟫_ℝ := by
      rw [hu]; simp only [inner_sub_right]
    rw [hexp, hAQ, hA2, hUval]; ring
  obtain ⟨t₁, ht₁⟩ := hTAC
  set m := t₁ * 2 with hm
  have hTm : T - A = m • u := by rw [ht₁, hCeq, hm]; module
  have hm0 : m ≠ 0 := by
    intro h0
    apply hTA
    have h1 : T - A = 0 := by rw [hTm, h0, zero_smul]
    exact sub_eq_zero.mp h1
  have hPeq : P - A = (1/2 : ℝ) • u := by
    have h2 : (⅟2 : ℝ) = 1/2 := by rw [invOf_eq_inv, one_div]
    rw [hP, midpoint_eq_smul_add, h2, hu]; module
  have hTPvec : T - P = (m - 1/2) • u := by
    have h1 : T - P = (T - A) - (P - A) := by module
    rw [h1, hTm, hPeq]; module
  have hTRvec : T - R = m • u - w := by
    have h1 : T - R = (T - A) - (R - A) := by module
    rw [h1, hTm, ← hw]
  have hTCvec : T - C = (m - 2) • u := by
    have h1 : T - C = (T - A) - (C - A) := by module
    have h2 : C - A = 2 • u := by rw [hCeq]; module
    rw [h1, hTm, h2]; module
  have hTSvec : T - S = m • u - s • w := by
    have h1 : T - S = (T - A) - (S - A) := by module
    rw [h1, hTm, hSeq]
  -- `TP = TR`, expanded.
  have e1 : 2 * m * G = W + m * U - U / 4 := by
    have hTP2 : ‖T - P‖^2 = ‖T - R‖^2 := by rw [hTP]
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
      hTPvec, hTRvec] at hTP2
    simp only [inner_sub_left, inner_sub_right,
      real_inner_smul_left, inner_smul_right] at hTP2
    rw [← real_inner_comm w u, ← hU, ← hW, ← hG] at hTP2
    linear_combination hTP2
  -- `TC = TS`, expanded.
  have e2 : 2 * m * s * G = s^2 * W + 4 * m * U - 4 * U := by
    have hTC2 : ‖T - C‖^2 = ‖T - S‖^2 := by rw [hTC]
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
      hTCvec, hTSvec] at hTC2
    simp only [inner_sub_left, inner_sub_right,
      real_inner_smul_left, inner_smul_right] at hTC2
    rw [← real_inner_comm w u, ← hU, ← hW, ← hG] at hTC2
    linear_combination hTC2
  -- Combining the two equations gives `(s - 4) * (m - 5/4) = 0`.
  have hkey : U * ((s - 4) * (m - 5 / 4)) = 0 := by
    linear_combination e2 - s * e1 + (s - 1) * hpowU
  have hkey2 : (s - 4) * (m - 5 / 4) = 0 := by
    rcases mul_eq_zero.mp hkey with h | h
    · exact absurd h hUne
    · exact h
  rcases mul_eq_zero.mp hkey2 with hs4 | hm54
  · -- The degenerate case `s = 4`: it forces `T = A`, contradiction.
    exfalso
    have hs4' : s = 4 := by linarith [hs4]
    have hU4 : U = 4 * W := by rw [← hpowU, hs4']
    have hG2 : G = 2 * W := by
      have h1 : m * (G - 2 * W) = 0 := by
        rw [hU4] at e1
        linear_combination (1 / 2 : ℝ) * e1
      rcases mul_eq_zero.mp h1 with h2 | h2
      · exact absurd h2 hm0
      · linarith [h2]
    -- `4W - 4G + U = 0` implies `2 • w = u`.
    have hcong : ⟪(2:ℝ) • w - u, (2:ℝ) • w - u⟫_ℝ = 0 := by
      have hexp : ⟪(2:ℝ) • w - u, (2:ℝ) • w - u⟫_ℝ = 4 * W - 4 * G + U := by
        simp only [inner_sub_left, inner_sub_right,
          real_inner_smul_left, inner_smul_right]
        rw [← real_inner_comm w u, ← hU, ← hW, ← hG]; ring
      rw [hexp, hG2, hU4]; ring
    have hwu : (2:ℝ) • w = u := by
      have h := inner_self_eq_zero.mp hcong
      rwa [sub_eq_zero] at h
    have hAu2 : ⟪A, u⟫_ℝ = 2 * ⟪A, w⟫_ℝ := by
      rw [← hwu, inner_smul_right]
    have hW0 : W = 0 := by linarith [hAu, hAw, hAu2]
    rw [hW] at hW0
    exact hw0 (inner_self_eq_zero.mp hW0)
  · -- The generic case `m = 5/4`.
    have hm' : m = 5 / 4 := by linarith [hm54]
    have hATn : ‖A - T‖ = 5 / 4 * ‖u‖ := by
      have h1 : A - T = -(m • u) := by rw [← hTm, neg_sub]
      rw [h1, norm_neg, norm_smul, Real.norm_eq_abs, hm',
        abs_of_pos (show (0:ℝ) < 5 / 4 by norm_num)]
    have hTCn : ‖T - C‖ = 3 / 4 * ‖u‖ := by
      rw [hTCvec, norm_smul, Real.norm_eq_abs, hm',
        abs_of_neg (show (5/4 - 2 : ℝ) < 0 by norm_num)]
      ring
    have hu_pos : (0:ℝ) < ‖u‖ := norm_pos_iff.mpr hu0
    rw [hATn, hTCn,
      div_eq_iff (ne_of_gt (by positivity : (0:ℝ) < 3 / 4 * ‖u‖))]
    ring

snip end

noncomputable determine answer : ℝ := 5 / 3

/--
The problem asks for the ratio `AT/TC`. We translate the common center to the
origin and apply `ratio_core`. Note: the hypothesis `T ≠ A` excludes the
degenerate configuration where `PR` and `CS` are parallel, in which case the
two perpendicular bisectors coincide and both pass through `A` (this is the
caveat mentioned in Kalva's solution). In the intended configuration the two
perpendicular bisectors meet in a single point, which forces the
non-degenerate case.
-/
problem usa1998_p2
    {r₁ r₂ : ℝ} (_hr₂ : 0 < r₂) (hrr : r₂ < r₁)
    {O A C Q P R S T : EuclideanSpace ℝ (Fin 2)}
    (hA : dist A O = r₁) (hC : dist C O = r₁)
    (hQ : dist Q O = r₂) (hR : dist R O = r₂) (hS : dist S O = r₂)
    (hAC : A ≠ C) (htan : ⟪Q - O, C - A⟫_ℝ = 0)
    (hQAC : ∃ t : ℝ, Q - A = t • (C - A))
    (hP : P = midpoint ℝ A Q)
    (hRS : R ≠ S) (hSAR : ∃ t : ℝ, S - A = t • (R - A))
    (hTP : dist T P = dist T R) (hTC : dist T C = dist T S)
    (hTAC : ∃ t : ℝ, T - A = t • (C - A)) (hTA : T ≠ A) :
    dist A T / dist T C = answer := by
  have ss : ∀ x y : EuclideanSpace ℝ (Fin 2), (x - O) - (y - O) = x - y :=
    fun x y => by module
  have hA' : ‖A - O‖ = r₁ := by rw [← dist_eq_norm]; exact hA
  have hC' : ‖C - O‖ = r₁ := by rw [← dist_eq_norm]; exact hC
  have hQ' : ‖Q - O‖ = r₂ := by rw [← dist_eq_norm]; exact hQ
  have hR' : ‖R - O‖ = r₂ := by rw [← dist_eq_norm]; exact hR
  have hS' : ‖S - O‖ = r₂ := by rw [← dist_eq_norm]; exact hS
  have hAC' : A - O ≠ C - O := fun h => hAC (sub_left_inj.mp h)
  have htan' : ⟪Q - O, (C - O) - (A - O)⟫_ℝ = 0 := by rw [ss]; exact htan
  obtain ⟨tq, htq⟩ := hQAC
  have hQAC' : ∃ t : ℝ, (Q - O) - (A - O) = t • ((C - O) - (A - O)) :=
    ⟨tq, by rw [ss, ss]; exact htq⟩
  have hP' : P - O = midpoint ℝ (A - O) (Q - O) := by
    have h2 : (⅟2 : ℝ) = 1/2 := by rw [invOf_eq_inv, one_div]
    rw [hP, midpoint_eq_smul_add, midpoint_eq_smul_add, h2]; module
  have hRS' : R - O ≠ S - O := fun h => hRS (sub_left_inj.mp h)
  obtain ⟨ts, hts⟩ := hSAR
  have hSAR' : ∃ t : ℝ, (S - O) - (A - O) = t • ((R - O) - (A - O)) :=
    ⟨ts, by rw [ss, ss]; exact hts⟩
  have hTP' : ‖(T - O) - (P - O)‖ = ‖(T - O) - (R - O)‖ := by
    rw [ss, ss, ← dist_eq_norm, ← dist_eq_norm]; exact hTP
  have hTC' : ‖(T - O) - (C - O)‖ = ‖(T - O) - (S - O)‖ := by
    rw [ss, ss, ← dist_eq_norm, ← dist_eq_norm]; exact hTC
  obtain ⟨tt, htt⟩ := hTAC
  have hTAC' : ∃ t : ℝ, (T - O) - (A - O) = t • ((C - O) - (A - O)) :=
    ⟨tt, by rw [ss, ss]; exact htt⟩
  have hTA' : T - O ≠ A - O := fun h => hTA (sub_left_inj.mp h)
  have hcore := ratio_core hrr hA' hC' hQ' hR' hS' hAC' htan' hQAC' hP' hRS' hSAR'
    hTP' hTC' hTAC' hTA'
  rw [dist_eq_norm A T, dist_eq_norm T C, ← ss A T, ← ss T C]
  exact hcore

end Usa1998P2
