/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InternLM-MATH LEAN Formalizer v0.1, Goedel-Prover-V2
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Olympiad 1971, Problem 3

Prove that we can find an infinite set of positive integers of the form 2^n - 3
(where n is a positive integer) every pair of which are relatively prime.
-/

namespace Imo1971P3

/-
Solved by Goedel-Prover-V2: https://arxiv.org/abs/2508.03613
-/
problem imo1971_p3 : Set.Infinite
  {(n, m) : ℕ × ℕ | Nat.Coprime (2 ^ n - 3) (2 ^ m - 3)} := by 
  have h_main : ∀ m : ℕ, (2, m) ∈ {(n, m) : ℕ × ℕ | Nat.Coprime (2 ^ n - 3) (2 ^ m - 3)} := by
    intro m
    have h₁ : Nat.Coprime (2 ^ 2 - 3) (2 ^ m - 3) := by
      have h₂ : 2 ^ 2 - 3 = 1 := by norm_num
      rw [h₂]
      have h₃ : Nat.gcd 1 (2 ^ m - 3) = 1 := by
        simp [Nat.gcd_one_left]
      simpa [Nat.coprime_iff_gcd_eq_one] using h₃
    simpa using h₁
  have h_infinite : Set.Infinite {p : ℕ × ℕ | p.1 = 2} := by
    have h : Set.Infinite (Set.range fun m : ℕ => (2, m)) := by
      have h₁ : Function.Injective fun m : ℕ => (2, m) := by
        intro m₁ m₂ h₂
        simp_all [Prod.ext_iff]
      exact Set.infinite_range_of_injective h₁
    have h₂ : Set.range (fun m : ℕ => (2, m)) ⊆ {p : ℕ × ℕ | p.1 = 2} := by
      intro p hp
      rcases hp with ⟨m, rfl⟩
      simp
    exact Set.Infinite.mono h₂ h
  have h_subset : {p : ℕ × ℕ | p.1 = 2} ⊆ {(n, m) : ℕ × ℕ | Nat.Coprime (2 ^ n - 3) (2 ^ m - 3)} := by
    intro p hp
    have h₁ : p.1 = 2 := by simpa using hp
    have h₂ : (p.1, p.2) ∈ {(n, m) : ℕ × ℕ | Nat.Coprime (2 ^ n - 3) (2 ^ m - 3)} := by
      have h₃ : (2, p.2) ∈ {(n, m) : ℕ × ℕ | Nat.Coprime (2 ^ n - 3) (2 ^ m - 3)} := h_main p.2
      simpa [h₁] using h₃
    simpa [Prod.ext_iff] using h₂
  have h_final : Set.Infinite {(n, m) : ℕ × ℕ | Nat.Coprime (2 ^ n - 3) (2 ^ m - 3)} := by
    have h₁ : Set.Infinite {p : ℕ × ℕ | p.1 = 2} := h_infinite
    have h₂ : {p : ℕ × ℕ | p.1 = 2} ⊆ {(n, m) : ℕ × ℕ | Nat.Coprime (2 ^ n - 3) (2 ^ m - 3)} := h_subset
    exact Set.Infinite.mono h₂ h₁
  exact h_final


end Imo1971P3
