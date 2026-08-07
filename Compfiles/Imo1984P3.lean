/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Data.Fintype.Pigeonhole
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Olympiad 1984, Problem 3

In the plane two different points O and A are given. For each point X of the plane,
other than O, denote by a(X) the measure of the angle between OA and OX in radians,
counterclockwise from OA (0 ≤ a(X) < 2π). Let C(X) be the circle with center O and
radius of length OX + a(X)/OX. Each point of the plane is colored by one of a finite
number of colors. Prove that there exists a point Y for which a(Y) > 0 such that its
color appears on the circumference of the circle C(Y).
-/

namespace Imo1984P3

/-- The angle `a(X)` from the problem statement: the measure in radians, counterclockwise
from `OA`, of the angle between `OA` and `OX`, taking values in `[0, 2 * π)`.
(The problem only uses this for `X ≠ O`; we define it for all `X`.) -/
noncomputable def aang (O A X : ℂ) : ℝ :=
  if 0 ≤ Complex.arg ((X - O) / (A - O)) then Complex.arg ((X - O) / (A - O))
    else Complex.arg ((X - O) / (A - O)) + 2 * Real.pi

problem imo1984_p3 {ι : Type*} [Fintype ι] (O A : ℂ) (hOA : O ≠ A) (color : ℂ → ι) :
    ∃ Y : ℂ, Y ≠ O ∧ 0 < aang O A Y ∧
      ∃ Z : ℂ, ‖Z - O‖ = ‖Y - O‖ + aang O A Y / ‖Y - O‖ ∧ color Z = color Y := by
  classical
  by_contra hcon
  push Not at hcon
  have hAO : A - O ≠ 0 := sub_ne_zero_of_ne hOA.symm
  have hAOpos : 0 < ‖A - O‖ := norm_pos_iff.mpr hAO
  have hAO0 : ‖A - O‖ ≠ 0 := hAOpos.ne'
  -- `S r` is the set of colors that appear on the circle of radius `r` centered at `O`.
  set S : ℝ → Finset ι := fun r =>
    Finset.univ.filter fun c => ∃ Z : ℂ, ‖Z - O‖ = r ∧ color Z = c with hS
  have mem_S {c : ι} {r : ℝ} : c ∈ S r ↔ ∃ Z : ℂ, ‖Z - O‖ = r ∧ color Z = c := by
    simp [hS]
  -- The key "spiral" lemma: if `0 < ρ < r` with `ρ * (r - ρ) < 1`, then some color
  -- appears on the circle of radius `ρ` but not on the circle of radius `r`.
  -- (The point on the circle of radius `ρ` at angle `ρ * (r - ρ)` has its circle
  -- `C(·)` equal to the circle of radius `r`, so its color cannot appear there.)
  have key : ∀ ρ r : ℝ, 0 < ρ → ρ < r → ρ * (r - ρ) < 1 →
      ∃ c : ι, c ∈ S ρ ∧ c ∉ S r := by
    intro ρ r hρ hρr hbound
    set θ₀ : ℝ := ρ * (r - ρ) with hθ₀
    have hθpos : 0 < θ₀ := by rw [hθ₀]; exact mul_pos hρ (sub_pos.mpr hρr)
    have hθmem : θ₀ ∈ Set.Ioc (-Real.pi) Real.pi :=
      ⟨by have hπ := Real.pi_pos; linarith, by have hπ := Real.pi_gt_three; linarith⟩
    set w : ℂ := (ρ / ‖A - O‖ : ℝ) * (Complex.cos θ₀ + Complex.sin θ₀ * Complex.I) with hw
    set Y : ℂ := O + (A - O) * w with hYdef
    have hYO : Y - O = (A - O) * w := by rw [hYdef]; ring
    have hdiv : (Y - O) / (A - O) = w := by
      rw [hYO]; exact mul_div_cancel_left₀ w hAO
    have harg : Complex.arg ((Y - O) / (A - O)) = θ₀ := by
      rw [hdiv, hw]
      exact Complex.arg_mul_cos_add_sin_mul_I (div_pos hρ hAOpos) hθmem
    have haang : aang O A Y = θ₀ := by
      unfold aang; rw [harg, if_pos hθpos.le]
    have hnormw : ‖w‖ = ρ / ‖A - O‖ := by
      rw [hw, norm_mul, Complex.norm_cos_add_sin_mul_I, mul_one, Complex.norm_real,
        Real.norm_of_nonneg (div_pos hρ hAOpos).le]
    have hnormY : ‖Y - O‖ = ρ := by
      rw [hYO, norm_mul, hnormw, mul_comm ‖A - O‖ (ρ / ‖A - O‖), div_mul_cancel₀ ρ hAO0]
    have hYne : Y ≠ O := by
      intro h
      rw [h, sub_self, norm_zero] at hnormY
      exact hρ.ne' hnormY.symm
    have hradius : ‖Y - O‖ + aang O A Y / ‖Y - O‖ = r := by
      rw [hnormY, haang, hθ₀, mul_div_cancel_left₀ (r - ρ) hρ.ne']
      ring
    have hcolρ : color Y ∈ S ρ := mem_S.mpr ⟨Y, hnormY, rfl⟩
    have hcolr : color Y ∉ S r := by
      intro hmem
      obtain ⟨Z, hZnorm, hZcol⟩ := mem_S.mp hmem
      exact hcon Y hYne (by rw [haang]; exact hθpos) Z (by rw [hZnorm, hradius]) hZcol
    exact ⟨color Y, hcolρ, hcolr⟩
  -- Only finitely many sets of colors exist, so two distinct circles among those of
  -- radius `1 / (k + 2)` carry exactly the same colors, contradicting the spiral lemma.
  obtain ⟨k, l, hne, heq⟩ :=
    Finite.exists_ne_map_eq_of_infinite fun k : ℕ => S (((k : ℝ) + 2)⁻¹)
  have heq' : S (((k : ℝ) + 2)⁻¹) = S (((l : ℝ) + 2)⁻¹) := heq
  have hkpos : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  have hlpos : (0 : ℝ) < (l : ℝ) + 2 := by positivity
  have hkρ : (0 : ℝ) < ((k : ℝ) + 2)⁻¹ := by positivity
  have hlρ : (0 : ℝ) < ((l : ℝ) + 2)⁻¹ := by positivity
  have hk1 : ((k : ℝ) + 2)⁻¹ < 1 :=
    inv_lt_one_of_one_lt₀ (by have h0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k; linarith)
  have hl1 : ((l : ℝ) + 2)⁻¹ < 1 :=
    inv_lt_one_of_one_lt₀ (by have h0 : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg l; linarith)
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hrlr : ((l : ℝ) + 2)⁻¹ < ((k : ℝ) + 2)⁻¹ := by
      have hcast : (k : ℝ) + 2 < (l : ℝ) + 2 := by
        have h1 : (k : ℝ) < (l : ℝ) := by exact_mod_cast hlt
        linarith
      exact (inv_lt_inv₀ hlpos hkpos).mpr hcast
    have hq : (0 : ℝ) < ((k : ℝ) + 2)⁻¹ - ((l : ℝ) + 2)⁻¹ := sub_pos.mpr hrlr
    have hlt1 : ((l : ℝ) + 2)⁻¹ * (((k : ℝ) + 2)⁻¹ - ((l : ℝ) + 2)⁻¹) <
        1 * (((k : ℝ) + 2)⁻¹ - ((l : ℝ) + 2)⁻¹) :=
      mul_lt_mul_of_pos_right hl1 hq
    have hdiff : ((k : ℝ) + 2)⁻¹ - ((l : ℝ) + 2)⁻¹ < 1 := by linarith [hk1, hlρ]
    have hbound : ((l : ℝ) + 2)⁻¹ * (((k : ℝ) + 2)⁻¹ - ((l : ℝ) + 2)⁻¹) < 1 := by
      linarith
    obtain ⟨c, hc1, hc2⟩ := key _ _ (by positivity) hrlr hbound
    rw [heq'] at hc2
    exact hc2 hc1
  · have hrlr : ((k : ℝ) + 2)⁻¹ < ((l : ℝ) + 2)⁻¹ := by
      have hcast : (l : ℝ) + 2 < (k : ℝ) + 2 := by
        have h1 : (l : ℝ) < (k : ℝ) := by exact_mod_cast hlt
        linarith
      exact (inv_lt_inv₀ hkpos hlpos).mpr hcast
    have hq : (0 : ℝ) < ((l : ℝ) + 2)⁻¹ - ((k : ℝ) + 2)⁻¹ := sub_pos.mpr hrlr
    have hlt1 : ((k : ℝ) + 2)⁻¹ * (((l : ℝ) + 2)⁻¹ - ((k : ℝ) + 2)⁻¹) <
        1 * (((l : ℝ) + 2)⁻¹ - ((k : ℝ) + 2)⁻¹) :=
      mul_lt_mul_of_pos_right hk1 hq
    have hdiff : ((l : ℝ) + 2)⁻¹ - ((k : ℝ) + 2)⁻¹ < 1 := by linarith [hl1, hkρ]
    have hbound : ((k : ℝ) + 2)⁻¹ * (((l : ℝ) + 2)⁻¹ - ((k : ℝ) + 2)⁻¹) < 1 := by
      linarith
    obtain ⟨c, hc1, hc2⟩ := key _ _ (by positivity) hrlr hbound
    rw [← heq'] at hc2
    exact hc2 hc1

end Imo1984P3
