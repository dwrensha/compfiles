/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Bradley (Problem statement + scaffolding)
-/

import Mathlib.Tactic
import Mathlib.Data.ENat.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.NumberTheory.Divisors

import ProblemExtraction

problem_file {
  tags := [.NumberTheory]
}

/-!
# International Mathematical Olympiad 2025, Problem 4
A proper divisor of a positive integer N is a positive divisor of N other than N itself.

The infinite sequence a₁, a₂, ... consists of positive integers, each of which has at least three proper
divisors. For each n ≥ 1, the integer aₙ + 1 is the sum of the three largest proper divisors of aₙ.
Determine all possible values of a₁.
-/
open Finset

/-- The type of sequences `aₙ` that satisfy the problem constraints -/
structure IsAllowed (a : ℕ → ℕ+) : Prop where
  atLeastThree : ∀ n, #(Nat.properDivisors (a n)) ≥ 3
  isSumOfPrevMaxThree : ∀ n,
    let prevDivisors := Nat.properDivisors (a n)
    let maxThree := @prevDivisors.orderEmbOfCardLe
      _ (.swap _ inferInstance) -- decreasing
      _ (atLeastThree n)
    a (n + 1) = maxThree 0 + maxThree 1 + maxThree 2

/-- The set of all possible values of `a₀` that give allowed sequences -/
def A₀ := { a₀ | ∃ a, a 0 = a₀ ∧ IsAllowed a }

variable {x : ℕ+}

lemma two_dvd_a₀ : x ∈ A₀ → 2 ∣ x :=
  sorry

lemma three_dvd_a₀ : x ∈ A₀ → 3 ∣ x :=
  sorry

/-- A constant sequence from a number divisible by six is allowed -/
lemma isAllowed_of_constant : IsAllowed (fun _ => 6 * x) where
  atLeastThree _ := by
    have : (6 : ℕ) ≤ 6 * x :=
      Nat.le_mul_of_pos_right 6 x.pos

    simp [le_card_iff_exists_subset_card]
    refine ⟨{1, 2, 3}, ?_, rfl⟩
    simp only [insert_subset_iff, singleton_subset_iff]
    split_ands
    · rw [Nat.one_mem_properDivisors_iff_one_lt]
      omega
    all_goals
      rw [Nat.mem_properDivisors]
      exact ⟨Nat.dvd_mul_right_of_dvd (by decide) _, by omega⟩

  isSumOfPrevMaxThree _ := sorry

determine answer : Set ℕ+ :=
  { x | ∃ (k : ℕ) (m : ℕ+), x = 6 * 12^k * m ∧ ¬2 ∣ m ∧ ¬5 ∣ m }

problem imo2025_p4 : A₀ = answer := by
  ext x
  constructor
  case mpr => -- the easy direction
    intro ⟨k, m, hx, not_two_dvd_m, not_five_dvd_m⟩
    rw [hx]
    induction k generalizing x with
    | zero =>
      -- Use the constant sequence 6 * m, 6 * m, ...
      exact ⟨_, rfl, isAllowed_of_constant⟩
    | succ k' ih =>
      sorry
  case mp => -- the hard direction
    intro ⟨a, ha, hx⟩
    sorry
