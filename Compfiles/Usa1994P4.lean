/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Order.Star.Real
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Inequality] }

/-!
# USA Mathematical Olympiad 1994, Problem 4

xᵢ is an infinite sequence of positive reals such that for all n,
x₁ + x₂ + ... + xₙ ≥ √n. Show that
x₁² + x₂² + ... + xₙ² > (1 + 1/2 + 1/3 + ... + 1/n) / 4 for all n.
-/

namespace Usa1994P4

snip begin

/-!
The proof follows <https://prase.cz/kalva/usa/usoln/usol944.html>.

Let `y i = √(i+1) - √i`, so that `∑ i ∈ Finset.range n, y i = √n`; the sequence `y`
is strictly decreasing. Summation by parts (Abel's lemma) then shows
`∑ i, (y i)^2 ≤ ∑ i, x i * y i`, and Cauchy–Schwarz upgrades this to
`∑ i, (y i)^2 ≤ ∑ i, (x i)^2`. Finally `y i = 1 / (√(i+1) + √i) > 1 / (2 √(i+1))`,
so `∑ i, (y i)^2 > ∑ i, 1 / (4 (i+1))`.
-/

/-- The telescoping comparison sequence `y i = √(i+1) - √i`. -/
noncomputable def y (i : ℕ) : ℝ := Real.sqrt (i + 1) - Real.sqrt i

lemma hden_pos (i : ℕ) : 0 < Real.sqrt ((i : ℝ) + 1) + Real.sqrt (i : ℝ) := by
  positivity

lemma hy_pos (i : ℕ) : 0 < y i := by
  have h : Real.sqrt (i : ℝ) < Real.sqrt ((i : ℝ) + 1) :=
    Real.sqrt_lt_sqrt (Nat.cast_nonneg _) (lt_add_one _)
  exact sub_pos.mpr h

lemma hy_mul (i : ℕ) : y i * (Real.sqrt ((i : ℝ) + 1) + Real.sqrt (i : ℝ)) = 1 := by
  have h1 : (Real.sqrt ((i : ℝ) + 1)) ^ 2 = (i : ℝ) + 1 := Real.sq_sqrt (by positivity)
  have h2 : (Real.sqrt (i : ℝ)) ^ 2 = (i : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  show (Real.sqrt ((i : ℝ) + 1) - Real.sqrt (i : ℝ)) * _ = 1
  nlinarith [h1, h2]

lemma hy_inv (i : ℕ) : y i = 1 / (Real.sqrt ((i : ℝ) + 1) + Real.sqrt (i : ℝ)) :=
  (eq_div_iff_mul_eq (hden_pos i).ne').mpr (hy_mul i)

lemma hy_succ_le (i : ℕ) : y (i + 1) ≤ y i := by
  rw [hy_inv (i + 1), hy_inv i]
  have hcast : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by push_cast; ring
  rw [hcast]
  have hmono : Real.sqrt ((i : ℝ) + 1) + Real.sqrt (i : ℝ)
      ≤ Real.sqrt ((i : ℝ) + 1 + 1) + Real.sqrt ((i : ℝ) + 1) := by
    have h1 : Real.sqrt (i : ℝ) ≤ Real.sqrt ((i : ℝ) + 1 + 1) :=
      Real.sqrt_le_sqrt (by linarith)
    linarith
  exact one_div_le_one_div_of_le (hden_pos i) hmono

lemma sum_y (n : ℕ) : ∑ i ∈ Finset.range n, y i = Real.sqrt (n : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [y]
    have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    ring

lemma one_div_four_lt (i : ℕ) : (1 : ℝ) / (i + 1) / 4 < (y i) ^ 2 := by
  have hlt : Real.sqrt ((i : ℝ) + 1) + Real.sqrt (i : ℝ)
      < 2 * Real.sqrt ((i : ℝ) + 1) := by
    have h : Real.sqrt (i : ℝ) < Real.sqrt ((i : ℝ) + 1) :=
      Real.sqrt_lt_sqrt (Nat.cast_nonneg _) (lt_add_one _)
    linarith
  have h3 : (1 : ℝ) / (2 * Real.sqrt ((i : ℝ) + 1)) < y i := by
    rw [hy_inv i]
    exact one_div_lt_one_div_of_lt (hden_pos i) hlt
  have h4 : ((1 : ℝ) / (2 * Real.sqrt ((i : ℝ) + 1))) ^ 2 < (y i) ^ 2 :=
    pow_lt_pow_left₀ h3 (by positivity) (by norm_num)
  have h5 : ((1 : ℝ) / (2 * Real.sqrt ((i : ℝ) + 1))) ^ 2 = (1 : ℝ) / (i + 1) / 4 := by
    rw [div_pow, one_pow, mul_pow,
      Real.sq_sqrt (show (0 : ℝ) ≤ (i : ℝ) + 1 by positivity), div_div]
    congr 1
    ring
  rw [← h5]
  exact h4

/-- Abel-summation comparison: the partial sums of `x` dominate those of `y` and `y`
is decreasing, so `∑ i, (y i)^2 ≤ ∑ i, x i * y i`. -/
lemma sum_sq_y_le (x : ℕ → ℝ) (h : ∀ n : ℕ, Real.sqrt (n : ℝ) ≤ ∑ i ∈ Finset.range n, x i)
    (n : ℕ) :
    ∑ i ∈ Finset.range n, (y i) ^ 2 ≤ ∑ i ∈ Finset.range n, x i * y i := by
  rcases n with _ | n
  · simp
  · have hb1 := Finset.sum_range_by_parts y x (n + 1)
    have hb2 := Finset.sum_range_by_parts y y (n + 1)
    simp only [smul_eq_mul, Nat.add_sub_cancel] at hb1 hb2
    rw [sum_y] at hb2
    simp only [sum_y] at hb2
    push_cast at hb2
    have h1 : y n * Real.sqrt ((n : ℝ) + 1) ≤ y n * ∑ i ∈ Finset.range (n + 1), x i := by
      have hh := h (n + 1)
      push_cast at hh
      exact mul_le_mul_of_nonneg_left hh (hy_pos n).le
    have h2 : ∑ i ∈ Finset.range n, (y (i + 1) - y i) * ∑ j ∈ Finset.range (i + 1), x j
        ≤ ∑ i ∈ Finset.range n, (y (i + 1) - y i) * Real.sqrt ((i : ℝ) + 1) := by
      apply Finset.sum_le_sum
      intro i _
      have hh := h (i + 1)
      push_cast at hh
      exact mul_le_mul_of_nonpos_left hh (sub_nonpos.mpr (hy_succ_le i))
    have e1 : ∑ i ∈ Finset.range (n + 1), (y i) ^ 2
        = ∑ i ∈ Finset.range (n + 1), y i * y i :=
      Finset.sum_congr rfl (fun i _ => pow_two (y i))
    have e2 : ∑ i ∈ Finset.range (n + 1), x i * y i
        = ∑ i ∈ Finset.range (n + 1), y i * x i :=
      Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    rw [e1, e2]
    linarith [hb1, hb2, h1, h2]

snip end

problem usa1994_p4 (x : ℕ → ℝ) (_hx : ∀ i, 0 < x i)
    (h : ∀ n : ℕ, Real.sqrt (n : ℝ) ≤ ∑ i ∈ Finset.range n, x i)
    (n : ℕ) (hn : 1 ≤ n) :
    (∑ i ∈ Finset.range n, (1 : ℝ) / (i + 1)) / 4 < ∑ i ∈ Finset.range n, (x i) ^ 2 := by
  rw [Finset.sum_div]
  have hn0 : n ≠ 0 := by omega
  have hA : ∑ i ∈ Finset.range n, (1 : ℝ) / (i + 1) / 4 < ∑ i ∈ Finset.range n, (y i) ^ 2 :=
    Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.mpr hn0)
      (fun i _ => one_div_four_lt i)
  have hB : 0 < ∑ i ∈ Finset.range n, (y i) ^ 2 :=
    Finset.sum_pos (fun i _ => pow_pos (hy_pos i) 2) (Finset.nonempty_range_iff.mpr hn0)
  have hCB : ∑ i ∈ Finset.range n, (y i) ^ 2 ≤ ∑ i ∈ Finset.range n, x i * y i :=
    sum_sq_y_le x h n
  have hCS : (∑ i ∈ Finset.range n, x i * y i) ^ 2
      ≤ (∑ i ∈ Finset.range n, (x i) ^ 2) * ∑ i ∈ Finset.range n, (y i) ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hsq : (∑ i ∈ Finset.range n, (y i) ^ 2) ^ 2
      ≤ (∑ i ∈ Finset.range n, x i * y i) ^ 2 :=
    pow_le_pow_left₀ hB.le hCB 2
  have hBA : ∑ i ∈ Finset.range n, (y i) ^ 2 ≤ ∑ i ∈ Finset.range n, (x i) ^ 2 := by
    have h2 : (∑ i ∈ Finset.range n, (y i) ^ 2) * (∑ i ∈ Finset.range n, (y i) ^ 2)
        ≤ (∑ i ∈ Finset.range n, (x i) ^ 2) * (∑ i ∈ Finset.range n, (y i) ^ 2) := by
      rw [← pow_two]
      exact le_trans hsq hCS
    exact le_of_mul_le_mul_right h2 hB
  exact lt_of_lt_of_le hA hBA

end Usa1994P4
