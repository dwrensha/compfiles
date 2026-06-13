/-
Copyright (c) 2025 Roozbeh Yousefzadeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Roozbeh Yousefzadeh
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file {
  tags := [.NumberTheory]
  solutionImportedFrom := "https://github.com/roozbeh-yz/IMO-Steps/blob/main/Lean_v20/imo_proofs/imo_1977_p5.lean"
}

/-!
# International Mathematical Olympiad 1977, Problem 5

Let $a,b$ be two natural numbers. When we divide $a^2+b^2$ by $a+b$,
we get the remainder $r$ and the quotient $q$. Determine all pairs $(a, b)$
for which $q^2 + r = 1977$.

-/

namespace Imo1977P5

determine solution_set : Set (ℕ×ℕ) := {(7,50), (37, 50), (50, 7), (50, 37)}


snip begin

/-- 1009 is prime and `≡ 1 (mod 4)`, so its representation as a sum of two
squares is unique: `1009 = 15² + 28²`. -/
lemma sq_add_sq_eq : ∀ m < 32, ∀ n < 32, m ^ 2 + n ^ 2 = 1009 →
    (m = 15 ∧ n = 28) ∨ (m = 28 ∧ n = 15) := by decide

lemma aux_1
  (a b : ℕ)
  (hp : 0 < a ∧ 0 < b)
  (h₁ : ((a : ℤ) - 22) ^ 2 + ((b : ℤ) - 22) ^ 2 = 1009) :
  (a, b) ∈ solution_set := by
  obtain ⟨ha, hb⟩ := hp
  -- Pass to absolute values, which are natural numbers below 32.
  have hmn : ((a : ℤ) - 22).natAbs ^ 2 + ((b : ℤ) - 22).natAbs ^ 2 = 1009 := by
    have h : ((((a : ℤ) - 22).natAbs ^ 2 + ((b : ℤ) - 22).natAbs ^ 2 : ℕ) : ℤ)
        = 1009 := by push_cast [Int.natCast_natAbs, sq_abs]; linarith
    exact_mod_cast h
  have hbound : ∀ m k : ℕ, m ^ 2 + k = 1009 → m < 32 := by
    intro m k hmk
    by_contra h
    push Not at h
    have : (1024 : ℕ) ≤ m ^ 2 := by
      calc (1024 : ℕ) = 32 ^ 2 := by norm_num
        _ ≤ m ^ 2 := Nat.pow_le_pow_left h 2
    lia
  have hu : ((a : ℤ) - 22).natAbs < 32 := hbound _ _ hmn
  have hv : ((b : ℤ) - 22).natAbs < 32 :=
    hbound _ _ (by rw [add_comm]; exact hmn)
  have key := sq_add_sq_eq _ hu _ hv hmn
  -- `|a - 22|, |b - 22| ∈ {15, 28}` pins down the four solutions.
  simp only [solution_set, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
  lia

lemma aux_2
  (a b q r : ℕ)
  (hp : 0 < a ∧ 0 < b)
  (h₀ : r = (a ^ 2 + b ^ 2) % (a + b))
  (h₁ : q = (a ^ 2 + b ^ 2) / (a + b)) :
  q ^ 2 + r = 1977 → (a, b) ∈ solution_set := by
  intro h₂
  have hr₀: r = 1977 - q ^ 2 := by exact Nat.eq_sub_of_add_eq' h₂
  have h₅₁: 0 < a + b := by linarith
  have h₅₂: a ^ 2 + b ^ 2 = q * (a + b) + r := by
    rw [h₀, h₁,]
    exact Eq.symm (Nat.div_add_mod' (a ^ 2 + b ^ 2) (a + b))
  have h₅₃: q ≤ 44 := by
    by_contra hc₀
    push Not at hc₀
    apply Nat.succ_le_iff.mpr at hc₀
    have hc₁: 45 ^ 2 ≤ q ^ 2 := by exact Nat.pow_le_pow_left hc₀ 2
    linarith
  have h₅₄: 43 < q := by
    have g₀: (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by exact add_sq_le
    have g₁: 2 * (a ^ 2 + b ^ 2) < 2 * (45 * (a + b)) := by
      refine (Nat.mul_lt_mul_left zero_lt_two).mpr ?_
      have g₁₀: 45 = 44 + 1 := by linarith
      rw [h₅₂, g₁₀, add_mul, one_mul]
      refine add_lt_add_of_le_of_lt ?_ ?_
      · exact Nat.mul_le_mul_right (a + b) h₅₃
      · rw [h₀]
        exact Nat.mod_lt (a ^ 2 + b ^ 2) h₅₁
    have g₂: a + b < 90 := by
      apply lt_of_le_of_lt g₀ at g₁
      rw [pow_two] at g₁
      rw [← mul_assoc] at g₁
      simp at g₁
      exact (Nat.mul_lt_mul_right h₅₁).mp g₁
    have g₃: r < 90 := by
      rw [h₀]
      refine lt_trans ?_ g₂
      exact Nat.mod_lt (a ^ 2 + b ^ 2) h₅₁
    by_contra hc₀
    push Not at hc₀
    have hc₁: q ^ 2 ≤ 43 ^ 2 := by exact Nat.pow_le_pow_left hc₀ 2
    lia
  have hq₀: q = 44 := by lia
  rw [hq₀] at hr₀
  norm_num at hr₀
  rw [hq₀, hr₀] at h₅₂
  have hcast : (a : ℤ) ^ 2 + (b : ℤ) ^ 2 = 44 * ((a : ℤ) + (b : ℤ)) + 41 := by
    exact_mod_cast h₅₂
  have h₆ : ((a : ℤ) - 22) ^ 2 + ((b : ℤ) - 22) ^ 2 = 1009 := by
    linear_combination hcast
  exact aux_1 a b hp h₆

snip end

problem imo1977_p5
    (a b q r : ℕ)
    (hp: 0 < a ∧ 0 < b)
    (h₀ : r = (a ^ 2 + b ^ 2) % (a + b))
    (h₁ : q = (a ^ 2 + b ^ 2) / (a + b)) :
    q ^ 2 + r = 1977 ↔ (a, b) ∈ solution_set := by
  constructor
  · exact fun (a_1 : q ^ 2 + r = 1977) ↦ aux_2 a b q r hp h₀ h₁ a_1
  · simp
    intro h₂
    bound

end Imo1977P5
