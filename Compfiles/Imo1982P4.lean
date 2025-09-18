/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InternLM-MATH LEAN Formalizer v0.1, Goedel-Prover-V2
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Olympiad 1982, Problem 4

Prove that if n is a positive integer such that the equation

x3 - 3xy^2 + y^3 = n

has a solution in integers x, y, then it has at least three such solutions.
Show that the equation has no solutions in integers for n = 2891.
-/

namespace Imo1982P4

set_option maxHeartbeats 300000

problem imo1982_p4 (n : ℕ)
  (hn : 0 < n)
  (hxy : ∃ x y : ℤ, x^3 - 3 * x * y^2 + y^3 = n) :
    (n ≠ 2891) ∧
    ∃ x1 x2 x3 y1 y2 y3 : ℤ, (x1^3 - 3 * x1 * y1^2 + y1^3 = n ∧
      x2^3 - 3 * x2 * y2^2 + y2^3 = n ∧
      x3^3 - 3 * x3 * y3^2 + y3^3 = n ∧
      (x1 ≠ x2 ∨ y1 ≠ y2) ∧
      (x1 ≠ x3 ∨ y1 ≠ y3) ∧
      (x2 ≠ x3 ∨ y2 ≠ y3)) := by
  have h_part1 : n ≠ 2891 := by
    rintro rfl
    rcases hxy with ⟨x, y, hxy⟩
    have h₁ : (x : ℤ) ^ 3 - 3 * x * y ^ 2 + y ^ 3 = 2891 := by simpa using hxy
    have h₂ : (x : ℤ) % 7 = 0 := by
      have h₃ := h₁
      have h₄ : (x : ℤ) ^ 3 - 3 * x * y ^ 2 + y ^ 3 ≡ 0 [ZMOD 7] := by
        norm_num [Int.ModEq] at h₃ ⊢
        omega
      have h₅ : (x : ℤ) % 7 = 0 := by
        mod_cases h : x % 7 <;> change _ = _ at h <;>
        mod_cases h' : y % 7 <;> change _ = _ at h' <;>
        simp [h, h', pow_three, pow_two, Int.ModEq, Int.mul_emod, Int.add_emod, Int.sub_emod] at h₄ ⊢
      exact h₅
    have h₃ : (y : ℤ) % 7 = 0 := by
      have h₄ := h₁
      have h₅ : (x : ℤ) ^ 3 - 3 * x * y ^ 2 + y ^ 3 ≡ 0 [ZMOD 7] := by
        norm_num [Int.ModEq] at h₄ ⊢
        (try omega)
      have h₆ : (y : ℤ) % 7 = 0 := by
        mod_cases h : x % 7 <;> change _ = _ at h <;>
        mod_cases h' : y % 7 <;> change _ = _ at h' <;>
        simp [h, h', pow_three, pow_two, Int.ModEq, Int.mul_emod, Int.add_emod, Int.sub_emod] at h₅ ⊢
      exact h₆
    have h₄ : (x : ℤ) % 7 = 0 := h₂
    have h₅ : (y : ℤ) % 7 = 0 := h₃
    have h₆ : ∃ (a : ℤ), x = 7 * a := by
      use x / 7
      have h₇ : (x : ℤ) % 7 = 0 := h₄
      omega
    have h₇ : ∃ (b : ℤ), y = 7 * b := by
      use y / 7
      have h₈ : (y : ℤ) % 7 = 0 := h₅
      omega
    obtain ⟨a, ha⟩ := h₆
    obtain ⟨b, hb⟩ := h₇
    rw [ha, hb] at h₁
    ring_nf at h₁
    have h₉ : (7 : ℤ) ∣ 59 := by
      use (a ^ 3 + b ^ 3 - 3 * a * b ^ 2)
      omega
    norm_num at h₉
  have h_part2 : ∃ x1 x2 x3 y1 y2 y3 : ℤ, (x1^3 - 3 * x1 * y1^2 + y1^3 = n ∧ x2^3 - 3 * x2 * y2^2 + y2^3 = n ∧ x3^3 - 3 * x3 * y3^2 + y3^3 = n ∧ (x1 ≠ x2 ∨ y1 ≠ y2) ∧ (x1 ≠ x3 ∨ y1 ≠ y3) ∧ (x2 ≠ x3 ∨ y2 ≠ y3)) := by
    obtain ⟨x, y, hxy⟩ := hxy
    have h1 : (y - x)^3 - 3 * (y - x) * (-x)^2 + (-x)^3 = (x : ℤ)^3 - 3 * x * (y : ℤ)^2 + (y : ℤ)^3 := by
      ring_nf
    have h2 : (-y)^3 - 3 * (-y) * (x - y)^2 + (x - y)^3 = (x : ℤ)^3 - 3 * x * (y : ℤ)^2 + (y : ℤ)^3 := by
      ring_nf
    refine' ⟨x, y - x, -y, y, -x, x - y, _, _, _, _, _, _⟩ <;>
    (try simp_all [pow_three]) <;>
    (try ring_nf at * ; simp_all) <;>
    (try {
      by_contra! h
      have h₃ : x = 0 := by grind
      have h₄ : y = 0 := by grind
      simp [h₃, h₄] at hxy
      norm_cast at hxy
      omega
    })
  exact ⟨h_part1, h_part2⟩


end Imo1982P4
