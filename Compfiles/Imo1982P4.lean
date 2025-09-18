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

snip begin

lemma lemma1 {x' y' : ZMod 7}
    (hxy : x' ^ 3 - 3 * x' * y' ^ 2 + y' ^ 3 = 0) : x' = 0 ∧ y' = 0 := by
  fin_cases x' <;> fin_cases y' <;> simp +decide at hxy ⊢

snip end

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
    replace hxy : (x : ℤ) ^ 3 - 3 * x * y ^ 2 + y ^ 3 = 2891 := by simpa using hxy
    have ⟨h₂, h₃⟩ : (x : ℤ) % 7 = 0 ∧ (y : ℤ) % 7 = 0 := by
      replace hxy : (x : ℤ) ^ 3 - 3 * x * y ^ 2 + y ^ 3 ≡ 0 [ZMOD (7:ℕ)] := by
        norm_num [Int.ModEq] at hxy ⊢
        omega
      replace hxy : (x : ZMod 7) ^ 3 - 3 * (x : ZMod 7) * (y : ZMod 7) ^ 2 +
                      (y : ZMod 7) ^ 3 = 0 := by
        rw [←ZMod.intCast_eq_intCast_iff] at hxy
        norm_cast
      have ⟨h1, h2⟩ := lemma1 hxy
      constructor
      · rw [ZMod.intCast_zmod_eq_zero_iff_dvd, ←Int.modEq_zero_iff_dvd] at h1
        exact h1
      · rw [ZMod.intCast_zmod_eq_zero_iff_dvd, ←Int.modEq_zero_iff_dvd] at h2
        exact h2
    have h₄ : (x : ℤ) % 7 = 0 := h₂
    have h₅ : (y : ℤ) % 7 = 0 := h₃
    have h₆ : ∃ (a : ℤ), x = 7 * a := by
      use x / 7
      exact (Int.mul_ediv_cancel_of_emod_eq_zero h₂).symm
    have h₇ : ∃ (b : ℤ), y = 7 * b := by
      use y / 7
      exact (Int.mul_ediv_cancel_of_emod_eq_zero h₃).symm
    obtain ⟨a, ha⟩ := h₆
    obtain ⟨b, hb⟩ := h₇
    rw [ha, hb] at hxy
    ring_nf at hxy
    have h₉ : (7 : ℤ) ∣ 59 := by
      use (a ^ 3 + b ^ 3 - 3 * a * b ^ 2)
      omega
    norm_num at h₉
  have h_part2 : ∃ x1 x2 x3 y1 y2 y3 : ℤ,
      (x1^3 - 3 * x1 * y1^2 + y1^3 = n ∧ x2^3 - 3 * x2 * y2^2 + y2^3 = n ∧
       x3^3 - 3 * x3 * y3^2 + y3^3 = n ∧ (x1 ≠ x2 ∨ y1 ≠ y2) ∧
       (x1 ≠ x3 ∨ y1 ≠ y3) ∧ (x2 ≠ x3 ∨ y2 ≠ y3)) := by
    obtain ⟨x, y, hxy⟩ := hxy
    have h1 : (y - x)^3 - 3 * (y - x) * (-x)^2 + (-x)^3 =
              (x : ℤ)^3 - 3 * x * (y : ℤ)^2 + (y : ℤ)^3 := by
      ring_nf
    have h2 : (-y)^3 - 3 * (-y) * (x - y)^2 + (x - y)^3 =
              (x : ℤ)^3 - 3 * x * (y : ℤ)^2 + (y : ℤ)^3 := by
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
