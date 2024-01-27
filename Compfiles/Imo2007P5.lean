/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Sanjaya
-/

import Mathlib.Init.Data.Int.CompLemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic

import ProblemExtraction

problem_file {
  tags := [.NumberTheory]
  importedFrom := .some {
    text := "mortarsanjaya/imo-A-and-N",
    url  := "https://github.com/mortarsanjaya/imo-A-and-N/blob/main/src/IMO2007/N6/N6.lean" },
}

/-!
# International Mathematical Olympiad 2007, Problem 5

Let a and b be positive integers. Show that if 4ab - 1 divides (4a² - 1)²
then a = b.
-/

namespace Imo2007P5

snip begin

lemma bad_symm {n : ℤ} {a b : ℕ} (h : n * a * b - 1 ∣ (n * a ^ 2 - 1) ^ 2) :
  n * b * a - 1 ∣ (n * b ^ 2 - 1) ^ 2 := by
  rw [mul_right_comm, sub_sq', add_comm, mul_right_comm _ _ (1 : ℤ), ← sub_sq']
  replace h := dvd_mul_of_dvd_left h ((n * b ^ 2) ^ 2)
  rw [← mul_pow, sub_one_mul, mul_mul_mul_comm, ← sq, ← mul_pow, ← mul_pow, ← mul_assoc] at h
  rw [← Int.modEq_zero_iff_dvd] at h ⊢
  revert h
  refine' ((Int.ModEq.sub_right _ _).pow _).trans
  nth_rewrite 1 [← one_pow 2]
  exact ((n * a * b).modEq_sub 1).symm.pow 2

lemma bad_exists_descent {n : ℤ} (hn : 1 < n) {a : ℕ}
  (h : 0 < a ∧ ∃ b : ℕ, a < b ∧ n * a * b - 1 ∣ (n * a ^ 2 - 1) ^ 2) :
  ∃ c : ℕ, 0 < c ∧ c < a ∧ n * c * a - 1 ∣ (n * c ^ 2 - 1) ^ 2 := by
  rcases h with ⟨h, b, h0, k, h1⟩
  rw [sq (a : ℤ), ← mul_assoc] at h1
  generalize ht : n * a = t at h1
  obtain ⟨c, rfl⟩ : ∃ c : ℤ, k = t * c - 1 := by
    replace h1 : (t * a - 1) ^ 2 ≡ (t * b - 1) * k [ZMOD t] := by rw [h1]
    have X : ∀ m : ℤ, t * m - 1 ≡ -1 [ZMOD t] := fun m ↦ by
      symm; rw [Int.modEq_iff_dvd, sub_neg_eq_add, sub_add_cancel]; exact ⟨m, rfl⟩
    replace h1 := ((X a).pow 2).symm.trans (h1.trans ((X b).mul_right _))
    rw [Int.modEq_iff_dvd, sq, ← mul_sub, sub_neg_eq_add, neg_one_mul, dvd_neg] at h1
    cases' h1 with c h1
    exact ⟨c, eq_sub_of_add_eq h1⟩

  ---- It suffices to show that `0 < c` and `c < (a : ℤ)`
  suffices h2 : c < a ∧ 0 < c from by
    lift c to ℕ using le_of_lt h2.2
    rw [Int.coe_nat_pos, Int.ofNat_lt] at h2
    refine ⟨c, h2.2, h2.1, bad_symm ⟨t * b - 1, ?_⟩⟩
    rw [sq (a : ℤ), ← mul_assoc, ht, h1, mul_comm]

  ---- We do not need `n`; we just use `t` instead.
  replace ht : 1 < t := by
    rw [← Int.coe_nat_pos] at h
    have h2 := le_trans Int.one_nonneg (le_of_lt hn)
    rw [Int.lt_iff_add_one_le] at hn h ⊢
    rw [← ht]
    refine le_of_eq_of_le ?_ (mul_le_mul hn h zero_le_one h2)
    rw [zero_add, mul_one]

  clear hn n

  ---- Some ordering results
  have h2 := lt_trans one_pos ht
  have h3 : ∀ x y : ℤ, x < y ↔ t * x - 1 < t * y - 1 :=
    λ x y ↦ by rw [sub_lt_sub_iff_right, ← mul_lt_mul_left h2]
  replace h2 : ∀ x : ℤ, 0 < x ↔ 0 < t * x - 1 := by
    intro x
    rw [h3, mul_zero, Int.lt_iff_add_one_le, sub_add_cancel, le_iff_eq_or_lt]
    refine or_iff_right (λ h4 ↦ ne_of_gt ht ?_)
    rw [eq_comm, sub_eq_zero] at h4
    exact Int.eq_one_of_mul_eq_one_right (le_of_lt h2) h4

  ---- Rearranging and final step
  rw [← Int.coe_nat_pos, h2] at h
  rw [← Int.ofNat_lt, h3] at h0
  rw [h2, h3 c]
  constructor
  · rwa [← mul_lt_mul_left (lt_trans h h0), ← h1, sq, mul_lt_mul_right h]
  · rw [← mul_lt_mul_left (lt_trans h h0), mul_zero, ← h1]
    exact pow_pos h 2

lemma nat_pred_descent {P : ℕ → Prop} [DecidablePred P]
  (h : ∀ k : ℕ, P k → ∃ m : ℕ, m < k ∧ P m) : ∀ k : ℕ, ¬P k :=
  forall_not_of_not_exists $ λ h0 ↦ Exists.elim (h (Nat.find h0) (Nat.find_spec h0)) $
    λ _ h1 ↦ Nat.find_min h0 h1.1 h1.2

theorem generalized_imo2007_p5 {n : ℤ} (hn : 1 < n) :
    ∀ a b : ℕ, 0 < a → 0 < b → n * a * b - 1 ∣ (n * a ^ 2 - 1) ^ 2 → a = b := by
  let P : ℕ → Prop := λ k ↦ (0 < k ∧ ∃ m : ℕ, k < m ∧ n * k * m - 1 ∣ (n * k ^ 2 - 1) ^ 2)
  have h : ∀ k : ℕ, P k → ∃ m : ℕ, m < k ∧ P m :=
    λ k h ↦ Exists.elim (bad_exists_descent hn h)
      (λ c h0 ↦ ⟨c, h0.2.1, h0.1, k, h0.2.1, h0.2.2⟩)
  classical
  replace h := nat_pred_descent h
  intro a b ha hb h0
  by_contra! h1
  exact (lt_or_gt_of_ne h1).elim (λ h1 ↦ h a ⟨ha, b, h1, h0⟩)
    (λ h1 ↦ h b ⟨hb, a, h1, bad_symm h0⟩)

snip end

problem imo2007_p5 (a b : ℤ) (ha : 0 < a) (hb : 0 < b)
    (hab : 4 * a * b - 1 ∣ (4 * a^2 - 1)^2) : a = b := by
  lift a to ℕ using le_of_lt ha
  lift b to ℕ using le_of_lt hb
  have ha' : 0 < a := Int.ofNat_pos.mp ha
  have hb' : 0 < b := Int.ofNat_pos.mp hb
  have hg := generalized_imo2007_p5 (n := 4) (by norm_num) a b ha' hb' hab
  exact congrArg Nat.cast hg
