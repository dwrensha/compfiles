/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InternLM-MATH LEAN Formalizer v0.1, Benpigchu
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 1995, Problem 4

The positive real numbers $x_0, x_1, x_2,.....x_{1994}, x_{1995}$ satisfy the relations
$x_0=x_{1995}$ and $x_{i-1}+\frac{2}{x_{i-1}}=2{x_i}+\frac{1}{x_i}$
for $i=1,2,3,....1995$
Find the maximum value that $x_0$ can have.
-/

namespace Imo1995P4

snip begin

lemma aux₁ {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    a + 2 / a = 2 * b + 1 / b ↔ b = 1 / a ∨ b = a / 2 := by
  grind

lemma aux₂ {x : ℕ → ℝ} {n : ℕ} (hn : 1 ≤ n) (hx₁ : ∀ (i : ℕ), 0 < x i)
  (hx₂ : ∀ (i : ℕ), 0 < i ∧ i ≤ n → x (i - 1) + 2 / x (i - 1) = 2 * x i + 1 / x i)
  : (∃ k : ℤ, 2 ∣ n - k ∧ - n ≤ k ∧ k ≤ n - 2 ∧ x n = 2 ^ k * x 0)
  ∨ (∃ k : ℤ, 2 ∣ n - k + 1 ∧ 1 - n ≤ k ∧ k ≤ n - 1 ∧ x n = 2 ^ k / x 0) := by
  induction' n, hn using Nat.le_induction with n' hn'₁ hn'₂
  · have h' := hx₂ 1 (by norm_num:_)
    simp [-one_div] at h'
    rw [aux₁ (hx₁ 0) (hx₁ 1)] at h'
    rcases h' with (h'|h')
    · right
      use 0
      rw [h']
      norm_num
    · left
      use -1
      rw [h']
      norm_num
      field
  · have h'' : (∀ (i : ℕ), 0 < i ∧ i ≤ n' → x (i - 1) + 2 / x (i - 1) = 2 * x i + 1 / x i) := by
      intro i hi
      exact hx₂ i (by cutsat:_)
    have h' := hn'₂ h''
    have h'n' := hx₂ (n' + 1) (by cutsat:_)
    simp [-one_div] at h'n'
    rw [aux₁ (hx₁ n') (hx₁ (n' + 1))] at h'n'
    rcases h' with (⟨k, ⟨hk₁, hk₂, hk₃, hk₄⟩⟩|⟨k, ⟨hk₁, hk₂, hk₃, hk₄⟩⟩)
    · rcases  h'n' with (h'n'|h'n')
      · right
        use -k
        constructorm* _ ∧ _
        · cutsat
        · cutsat
        · cutsat
        · rw [h'n', hk₄, zpow_neg]
          field
      · left
        use k - 1
        constructorm* _ ∧ _
        · cutsat
        · cutsat
        · cutsat
        · rw [h'n', hk₄, zpow_sub₀ (by norm_num:_)]
          field
    · rcases  h'n' with (h'n'|h'n')
      · left
        use -k
        constructorm* _ ∧ _
        · cutsat
        · cutsat
        · cutsat
        · rw [h'n', hk₄, zpow_neg]
          field
      · right
        use k - 1
        constructorm* _ ∧ _
        · cutsat
        · cutsat
        · cutsat
        · rw [h'n', hk₄, zpow_sub₀ (by norm_num:_)]
          field

theorem generalized (n : ℕ) (hn : 0 < n) (hn' : ¬2 ∣ n) : IsGreatest { x₀ | ∃ x : ℕ → ℝ, x 0 = x₀ ∧ (∀ i : ℕ, 0 < x i) ∧ x 0 = x n
    ∧ (∀ i : ℕ, 0 < i ∧ i ≤ n → x (i - 1) + (2 / x (i - 1)) = 2 * x i + (1 / x i))
  } (2 ^ ((n - (1 : ℝ)) / 2)) := by
  constructor
  · use fun i ↦ (2 ^ ((n - (1 : ℝ)) / 2 - (if i < n then i else 0)))
    simp [-one_div]
    constructor
    · intro i
      apply Real.rpow_pos_of_pos
      norm_num
    · intro i hi₁ hi₂
      rw [aux₁ (Real.rpow_pos_of_pos (by norm_num:_) _) (Real.rpow_pos_of_pos (by norm_num:_) _)]
      by_cases hi' : i < n
      · right
        have hi'' : i - 1 < n := by cutsat
        rw [if_pos hi', if_pos hi'']
        rw [Nat.cast_sub (by cutsat:_), Nat.cast_one, ← sub_add, Real.rpow_add_one (by norm_num:_)]
        field
      · left
        have hi'' : i - 1 < n := by cutsat
        have hi''' : i = n := by cutsat
        rw [if_neg hi', if_pos hi'', hi''']
        rw [Nat.cast_sub (by cutsat:_), Nat.cast_one, one_div, ← Real.rpow_neg (by norm_num:_)]
        congr
        ring
  · intro x₀ hx₀
    rcases hx₀ with ⟨x, ⟨hx₁, hx₂, hx₃, hx₄⟩⟩
    rcases aux₂ (by cutsat:_) hx₂ hx₄ with (⟨k, ⟨hk₁, hk₂, hk₃, hk₄⟩⟩|⟨k, ⟨hk₁, hk₂, hk₃, hk₄⟩⟩)
    · rw [← hx₃] at hk₄
      symm at hk₄
      rw [mul_left_eq_self₀] at hk₄
      rcases hk₄ with (h'|h')
      · rw [zpow_eq_one_iff_right₀ (by norm_num:_) (by norm_num:_)] at h'
        contrapose! h'
        cutsat
      · contrapose! h'
        exact ne_of_gt (hx₂ 0)
    · rw [← hx₃] at hk₄
      symm at hk₄
      rw [div_eq_iff (ne_of_gt (hx₂ 0)), ← pow_two] at hk₄
      rw [← Real.sqrt_eq_iff_eq_sq (zpow_nonneg (by norm_num:_) k) (le_of_lt (hx₂ 0))] at hk₄
      rw [Real.sqrt_eq_rpow, ← Real.rpow_intCast_mul (by norm_num:_), hx₁] at hk₄
      rw [← hk₄, Real.rpow_le_rpow_left_iff (by norm_num:_)]
      rw [mul_div, mul_one, div_le_div_iff_of_pos_right (by norm_num:_)]
      rw [← Int.cast_one, ← Int.cast_natCast, ← Int.cast_sub, Int.cast_le]
      exact hk₃

snip end

determine solution : ℝ := 2^997

problem imo1995_p4 :
  IsGreatest { x₀ | ∃ x : ℕ → ℝ, x 0 = x₀ ∧ (∀ i : ℕ, 0 < x i) ∧ x 0 = x 1995
    ∧ (∀ i : ℕ, 0 < i ∧ i ≤ 1995 → x (i - 1) + (2 / x (i - 1)) = 2 * x i + (1 / x i))
  } solution := by
  have h : solution = (2 ^ ((1995 - (1 : ℝ)) / 2)) := by norm_num
  rw [h]
  exact generalized 1995 (by norm_num:_) (by norm_num:_)


end Imo1995P4
