/-
Copyright (c) 2026 pacmanboss256. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pacmanboss256, hillosanation
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file {
  tags := [.Algebra]
}

/-!
# USA Mathematical Olympiad 1991, Problem 4
let $ a = \frac{m^{m+1} + n^{n+1}}{m^m + n^n} $ where $m$ and $n$ are positive integers. Prove that $a^m + a^n \geq m^m + n^n$.
-/

snip begin
-- Solution adapted from Art of Problem Solving. Note that the solution there has a sign error in the first equation.
open Finset
snip end

namespace Usa1991P4

problem usa1991_p4 (m n : ℕ) (a: ℝ) (hm: 0 < m) (hn: 0 < n)
  (ha : a = (m^(m+1)+ n^(n+1))/(m^m + n^n)) : m^m + n^n ≤ a^m + a^n := by
  have h₀ : 0 ≤ a := by
    rw [ha]
    field_simp
    norm_cast
    simp
  have h_sum {m : ℕ} (h: 0 < m) : ∑ i ∈ range m, a^i * m^(m-1-i)
    = 1 / m * (∑ i ∈ range m, (a/m) ^ i) * m ^ m := by
    rw [mul_sum, sum_mul, sum_congr rfl]
    intro i hi
    rw [div_pow, mul_div_left_comm, mul_assoc, mul_eq_mul_left_iff]
    rw [div_div, ← pow_succ', one_div_mul_eq_div]
    rw [← zpow_natCast_sub_natCast₀ (by exact_mod_cast h.ne.symm)]
    rw [← Int.ofNat_sub (by simpa using hi)]
    rw [tsub_add_eq_tsub_tsub_swap]
    left
    rfl
  wlog! h : n ≤ m generalizing n m
  · simpa [add_comm] using this _ _ hn hm (by simpa [add_comm] using ha) h.le
  · have h₁ := calc
      m - a = m*(m^m+n^n)/(m^m+n^n) - (m^(m+1)+n^(n+1))/(m^m+n^n) := by
        simp [ha, ← Nat.cast_pow, ← Nat.cast_add]
      _ = n^n * (m - n) / (m^m + n^n) := by field_simp; ring
    have h₂ : a / m ≤ 1 := by
      rw [div_le_one (by norm_cast), ← sub_nonneg, h₁]
      refine div_nonneg (mul_nonneg ?_ ?_) ?_ <;> (norm_cast; simp)
    have h₃ := calc
      a - n
      _ = (m^(m+1)+n^(n+1))/(m^m + n^n) - n*(m^m+n^n)/(m^m+n^n) := by
        simp [ha, ← Nat.cast_pow, ← Nat.cast_add]
      _ = m^m*(m-n)/(m^m+n^n) := by field_simp; ring
    have h₄ : 1 ≤ a / n := by
      rw [one_le_div (by norm_cast), ← sub_nonneg, h₃]
      refine div_nonneg (mul_nonneg ?_ ?_) ?_ <;> (norm_cast; simp)
    have h₅ : n * ∑ i ∈ range m, (a/m)^i ≤ m * ∑ i ∈ range n, (a/n)^i := calc
      n * ∑ i ∈ range m, (a/m)^i
      _ ≤ n * ∑ i ∈ range m, 1 :=
        mul_le_mul_iff_right₀ (by norm_cast) |>.mpr
          <| sum_le_sum fun _ _ => pow_le_one₀ (div_nonneg h₀ <| by exact_mod_cast hm.le) h₂
      _ = m * ∑ i ∈ range n, 1 := by simp; field_simp
      _ ≤ m * ∑ i ∈ range n, (a/n)^i :=
        mul_le_mul_iff_right₀ (by norm_cast) |>.mpr
          <| sum_le_sum fun _ _ => one_le_pow₀ h₄
    have := calc
      m^m - a^m
      _ = n^n * (m - n) / (m^m + n^n) * ∑ i ∈ range m, a^(i: ℕ) * m^(m - 1 - i) := by
        simp_rw [← h₁, mul_sum, mul_sub_right_distrib]
        have := sum_range_sub' (fun i => a^i * m^(m-i)) m
        simp only [pow_zero, tsub_zero, one_mul, tsub_self, mul_one] at this
        rw [← this]
        apply sum_equiv (by rfl) (by simp) fun i imem => ?_
        replace h₅: (m: ℝ) * ↑m ^ (m - 1 - i) = m ^ (m - i) := by
          rw [mem_range] at imem
          norm_cast
          rw [← Nat.pow_add_one', ← Nat.sub_add_comm, Nat.sub_add_cancel (by lia)]
          lia
        simp; ring_nf; simp only [Nat.sub_add_eq, mul_assoc, h₅]
      _ ≤ (a - n) * ∑ i ∈ range n, a^(i: ℕ) * n^(n - 1 - i) := by
        rw [h₃]
        wlog! h: (n: ℝ) ≠ m
        · rw [h]; simp
        · have : (m: ℝ) - n > 0 := by norm_cast at h ⊢; lia
          let : ℝ ≃o ℝ := by
            refine ⟨⟨(· / (m-n) * (m^m+n^n)), (· * (m-n) / (m^m+n^n)), ?_, ?_⟩, ?_⟩
            any_goals intro _; dsimp; field_simp
            simp
          apply_fun this
          simp_rw [h_sum hm, h_sum hn]
          simp [this]
          field_simp
          exact h₅
      _ = a^n - n^n := by
        simp_rw [mul_sum, mul_sub_right_distrib]
        have := sum_range_sub (fun i => a^i * n^(n-i)) n
        simp only [tsub_self, pow_zero, mul_one, tsub_zero, one_mul] at this
        rw [← this]
        apply sum_equiv (by rfl) (by simp) fun i imem => ?_
        replace h₅: (n: ℝ) * ↑n ^ (n - 1 - i) = n ^ (n - i) := by
          norm_cast
          rw [mem_range] at imem
          rw [← Nat.pow_add_one', ← Nat.sub_add_comm, Nat.sub_add_cancel (by lia)]
          lia
        simp; ring_nf; simp only [Nat.sub_add_eq, mul_assoc, h₅]
    linarith

end Usa1991P4
