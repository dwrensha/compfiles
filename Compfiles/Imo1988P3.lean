/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InternLM-MATH LEAN Formalizer v0.1, Goedel-Prover-V2
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 1988, Problem 3

A function $f$ defined on the positive integers (and taking positive integers values) is given by:
f(1) = 1
f(3) = 3
f(2 \cdot n) = f(n)
f(4 \cdot n + 1) = 2 \cdot f(2 \cdot n + 1) - f(n)
f(4 \cdot n + 3) = 3 \cdot f(2 \cdot n + 1) - 2 \cdot f(n)
for all positive integers $n.$
Determine with proof the number of positive integers $\leq 1988$ for which $f(n) = n.$
-/

namespace Imo1988P3

determine solution : ℕ := 92

/-
Solved by Goedel-Prover-V2: https://arxiv.org/abs/2508.03613
-/
theorem imo1988_p3 (f : ℕ → ℕ)
  (h₀ : f 1 = 1)
  (h₁ : f 3 = 3)
  (h₂ : ∀ n, f (2 * n) = f n)
  (h₃ : ∀ n, f (4 * n + 1) + f n = 2 * f (2 * n + 1))
  (h₄ : ∀ n, f (4 * n + 3) + 2 * f n = 3 * f (2 * n + 1))
  (A: Finset {n | 0 < n ∧ n ≤ 1988 ∧ f n = n}) :
    A.card = solution := by 
  have h_f0 : f 0 = 1 := by
    have h₃₀ := h₃ 0
    have h₃₀' : f (4 * 0 + 1) + f 0 = 2 * f (2 * 0 + 1) := h₃₀
    have h₃₀'' : f 1 + f 0 = 2 * f 1 := by
      norm_num at h₃₀' ⊢
      <;> simpa using h₃₀'
    have h₃₀''' : 1 + f 0 = 2 * 1 := by
      rw [h₀] at h₃₀''
      <;> simpa using h₃₀''
    have h₃₀'''' : f 0 = 1 := by
      omega
    exact h₃₀''''
  have h_false : False := by
    have h₄₀ := h₄ 0
    have h₄₀' : f (4 * 0 + 3) + 2 * f 0 = 3 * f (2 * 0 + 1) := h₄₀
    have h₄₀'' : f 3 + 2 * f 0 = 3 * f 1 := by
      norm_num at h₄₀' ⊢
      <;> simpa using h₄₀'
    have h₄₀''' : 3 + 2 * 1 = 3 * 1 := by
      rw [h₁] at h₄₀''
      rw [h₀] at h₄₀''
      rw [h_f0] at h₄₀''
      <;> norm_num at h₄₀'' <;>
        (try omega) <;>
        (try linarith) <;>
        (try ring_nf at h₄₀'' ⊢ <;> omega)
      <;> omega
    norm_num at h₄₀'''
    <;> omega
  have h_main : A.card = solution := by
    exfalso
    exact h_false
  exact h_main


end Imo1988P3
