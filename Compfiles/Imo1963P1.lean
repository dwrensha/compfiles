/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongyu Ouyang
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

import ProblemExtraction

problem_file { tags := [.Algebra, .Inequality] }

/-!
# International Mathematical Olympiad 1963, Problem 1

Find all real roots of the equation

  √(x²-p) + 2√(x²-1) = x

where *p* is a real parameter.
-/

namespace Imo1963P1

snip begin

lemma iff_comm {a b c : Prop} : (a → c) → (b → c) → (c → (a ↔ b)) → (a ↔ b) := by
  tauto

snip end

determine f (p : ℝ) : Set ℝ :=
  if h : p ≥ 0 ∧ p ≤ (4 : ℝ) / 3
  then { (4 - p) / (2 * Real.sqrt (4 - 2 * p)) }
  else ∅

problem imo1963_p1 : ∀ (p x : ℝ), (x ^ 2 - p) ≥ 0 → (x ^ 2 - 1) ≥ 0 →
  (Real.sqrt (x ^ 2 - p) + 2 * Real.sqrt (x ^ 2 - 1) = x ↔ (x ∈ f p)) := by
  intro p x h1 h2
  unfold f
  rw [apply_dite (Membership.mem x)]
  simp only [Set.mem_singleton_iff, ge_iff_le]
  apply @iff_comm (c := x ≥ 0)
  · intro h; rw [←h]; positivity
  · split_ifs with h;
    · intro hx; rw [hx]; apply le_of_lt; apply div_pos_iff.mpr
      left
      constructor
      linarith
      simp only [Nat.ofNat_pos, mul_pos_iff_of_pos_left, Real.sqrt_pos]
      linarith
    · simp only [Set.mem_empty_iff_false, ge_iff_le, IsEmpty.forall_iff]
  intro xge0
  trans (Real.sqrt (x ^ 2 - p) + 2 * Real.sqrt (x ^ 2 - 1)) ^ 2 = x ^ 2
  · refine Iff.symm (sq_eq_sq ?ha ?hb) <;> positivity
  rw [add_sq]
  rw [Real.sq_sqrt h1]
  rw [mul_pow]
  rw [Real.sq_sqrt h2]
  trans Real.sqrt (x ^ 2 - p) * Real.sqrt (x ^ 2 - 1) = (p + 4 - 4 * x ^ 2) / (4 : ℝ)
  · constructor
    · intro h; linear_combination (norm := (field_simp; ring_nf)) (1 / (4 : ℝ)) * h
    · intro h; linear_combination (norm := (field_simp; ring_nf)) (4 : ℝ) * h
  apply @iff_comm (c := p + 4 - 4 * x ^ 2 ≥ 0)
  · intro h; rw [ge_iff_le]; apply (div_le_div_right (by norm_num : (0 : ℝ) < (4 : ℝ))).mp
    norm_num; rw [←h]; positivity
  · split_ifs with h;
    · have tmp : 0 < (4 - 2 * p) := by linarith
      intro h; rw [h]; rw [div_pow, mul_pow, Real.sq_sqrt (le_of_lt tmp)]; norm_num
      rw [←(mul_le_mul_right tmp), mul_assoc, div_mul]
      field_simp
      ring_nf
      norm_num
      nlinarith
    · simp
  intro xp
  trans (Real.sqrt (x ^ 2 - p) * Real.sqrt (x ^ 2 - (1 : ℝ))) ^ 2 = ((p + (4 : ℝ) - (4 : ℝ) * x ^ 2) / (4 : ℝ)) ^ 2
  · symm; apply sq_eq_sq <;> positivity
  rw [mul_pow, Real.sq_sqrt h1, Real.sq_sqrt h2]
  rw [div_pow]
  norm_num
  conv => lhs; rw [←mul_right_cancel_iff_of_pos (by norm_num : (0 : ℝ) < (16 : ℝ))]; norm_num
          rw [sub_sq, mul_pow, ←pow_mul];
          simp only [mul_add, add_mul, mul_sub_left_distrib, mul_sub_right_distrib]; norm_num
          rw [←pow_add]; norm_num
  trans x ^ 2 * 4 * (4 - 2 * p) = (p - 4) ^ 2
  · constructor
    · intro h; linear_combination (norm := (field_simp; ring_nf)) 1 * h
    · intro h; linear_combination (norm := (field_simp; ring_nf)) 1 * h
  apply @iff_comm (c := p < 2)
  · intro; linarith
  · intro ⟨⟨_, _⟩, _⟩; linarith
  intro hp
  have tmp : (4 - 2 * p) > 0 := by linarith
  trans x ^ 2 = (p - 4) ^ 2 / (4 * (4 - 2 * p))
  · constructor
    · intro h; rw [←h]; field_simp [mul_assoc]
    · intro h; rw [h]; field_simp [mul_assoc]
  rw [(by nlinarith : (p - (4 : ℝ)) ^ (2 : ℕ) = ((4 : ℝ) - p) ^ (2 : ℕ))]
  have tmp2 :
    ((4 : ℝ) - p) ^ (2 : ℕ) / ((4 : ℝ) * ((4 : ℝ) - (2 : ℝ) * p)) =
    (((4 : ℝ) - p) / ((2 : ℝ) * Real.sqrt ((4 : ℝ) - (2 : ℝ) * p))) ^ 2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt]; norm_num; exact le_of_lt tmp
  rw [tmp2, sq_eq_sq xge0 (le_of_lt (by apply div_pos; linarith; simp only [gt_iff_lt, Nat.ofNat_pos, mul_pos_iff_of_pos_left, Real.sqrt_pos, sub_pos]; linarith))]
  constructor
  · intro hx
    refine' ⟨_, hx⟩
    rw [hx, ←tmp2] at xp
    simp only [ge_iff_le, sub_nonneg] at xp
    rw [←(mul_le_mul_right (by linarith : (0 < ((4 : ℝ) * ((4 : ℝ) - (2 : ℝ) * p)))))] at xp
    field_simp at xp
    revert xp; ring_nf; intro xp
    rw [pow_two] at xp
    clear tmp tmp2
    by_cases hp1 : 0 ≤ p
    · refine ⟨hp1, ?_⟩
      by_cases hp2 : p ≤ (4 / 3 : ℝ)
      · exact hp2
      · nlinarith
    · nlinarith
  · intro ⟨_, hx⟩; exact hx
