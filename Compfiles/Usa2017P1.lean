/-
Copyright (c) 2025 Elan Roth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elan Roth
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Ring

import ProblemExtraction

set_option backward.isDefEq.respectTransparency false

problem_file { tags := [.NumberTheory]}

/-!
# USA Mathematical Olympiad 2017, Problem 1

Prove that there are infinitely many distinct pairs $(a,b)$ of
relatively prime positive integers $a>1$ and $b>1$ such that
$a^b+b^a$ is divisible by $a+b$.
-/

namespace Usa2017P1

def condition (a b : ℕ) : Prop :=
  Nat.gcd a b = 1 ∧ a > 1 ∧ b > 1 ∧ (a + b) ∣ (a ^ b + b ^ a)

snip begin

def solution_set : Set (ℕ × ℕ) := { x | condition x.1 x.2 }

lemma divisibility_helper {n k} : k = 3 ∨ k = 5 → (2 * n + k) ^ 2 ≡ 1 [MOD 4 * n + 8] := by
  intro H
  cases H
  case inl h3 =>
    rw [h3]
    ring_nf
    have factorized : 9 + n * 12 + n ^ 2 * 4 = (8 + n * 4) * (1 + n) + 1 := by ring_nf
    rw [factorized]
    apply Nat.ModEq.modulus_mul_add
  case inr h5 =>
    rw [h5]
    ring_nf
    have factorized : 25 + n * 20 + n ^ 2 * 4 = (8 + n * 4) * (3 + n) + 1 := by ring_nf
    rw [factorized]
    apply Nat.ModEq.modulus_mul_add

lemma build_condition_divisibility {n} : (2 * n + 3) + (2 * n + 5) ∣
                                         (2 * n + 3) ^ (2 * n + 5) + (2 * n + 5) ^ (2 * n + 3) := by
  set m : ℕ := 4 * n + 8
  apply @Nat.modEq_zero_iff_dvd.mp
  have h0 : (2 * n + 3) + (2 * n + 5) = 4 * n + 8 := by ring_nf
  rw [h0, pow_add, pow_add, pow_mul, pow_mul]
  have add_3_eq_1 : (2 * n + 3) ^ 2 ≡ 1 [MOD m] := by
    apply divisibility_helper; trivial
  have add_5_eq_1 : (2 * n + 5) ^ 2 ≡ 1 [MOD m] := by
    apply divisibility_helper; trivial


  have h3n : ((2 * n + 3) ^ 2) ^ n ≡ 1 [MOD m] := by
    simpa [m, one_pow] using add_3_eq_1.pow n
  have h5n : ((2 * n + 5) ^ 2) ^ n ≡ 1 [MOD m] := by
    simpa [m, one_pow] using add_5_eq_1.pow n

  have h_reduce :
      ((2 * n + 3)^2) ^ n * (2 * n + 3) ^ 5
    + ((2 * n + 5)^2) ^ n * (2 * n + 5) ^ 3
      ≡ (2 * n + 3) ^ 5 + (2 * n + 5) ^ 3 [MOD m] := by
    simpa [Nat.one_mul] using Nat.ModEq.add (h3n.mul_right ((2 * n + 3) ^ 5))
                                            (h5n.mul_right ((2 * n + 5) ^ 3))


  have h3_5 : (2 * n + 3) ^ 5 ≡ (2 * n + 3) [MOD m] := by
    have h4 : (2 * n + 3) ^ 4 ≡ 1 [MOD m] := by
      rw [pow_mul (2 * n + 3) 2 2, Nat.ModEq, add_3_eq_1.pow 2]
      simp

    simpa [pow_succ] using h4.mul_right (2 * n + 3)

  have h5_3 : (2 * n + 5) ^ 3 ≡ (2 * n + 5) [MOD m] := by
    simpa [pow_two, pow_succ] using add_5_eq_1.mul_right (2 * n + 5)

  have h_sum_ab :
      (2 * n + 3) ^ 5 + (2 * n + 5) ^ 3
        ≡ (2 * n + 3) + (2 * n + 5) [MOD m] :=
    Nat.ModEq.add h3_5 h5_3

  have h_m0 : (4 * n + 8) ≡ 0 [MOD m] := by
    have : (4 * n + 8) = (4 * n + 8) * 1 := by rw [mul_one]
    rw [this]
    apply @Nat.ModEq.modulus_mul_add (4 * n + 8) 1 0
  have h_ab0 : (2 * n + 3) + (2 * n + 5) ≡ 0 [MOD m] := by
    have hm : (2 * n + 3) + (2 * n + 5) = 4 * n + 8 := by ring
    simp [m, hm]

  exact h_reduce.trans (h_sum_ab.trans h_ab0)

lemma build_condition (n : ℕ) : condition (2 * n + 3) (2 * n + 5) := by
  have h0 : 2 * n + 5 = 2 * n + 3 + 2 := rfl
  have h1 : Nat.gcd (2 * n + 3) (2 * n + 5) = 1 := by
    apply Nat.coprime_iff_gcd_eq_one.mp
    rw [h0]
    rw [add_comm (2 * n + 3) 2]
    apply (@Nat.coprime_add_self_right (2 * n + 3)).mpr
    apply (@Nat.coprime_two_right (2 * n + 3)).mpr
    use n + 1
    aesop
  have h2 : 2 * n + 3 > 1 := by aesop
  have h3 : 2 * n + 5 > 1 := by aesop
  have h4 : (2 * n + 3) + (2 * n + 5) ∣ (2 * n + 3) ^ (2 * n + 5) + (2 * n + 5) ^ (2 * n + 3) := by
    exact build_condition_divisibility
  exact ⟨ h1, h2, h3, h4 ⟩

def build : ℕ → solution_set :=
  fun n => ⟨ (2 * n + 3, 2 * n + 5) , build_condition n ⟩

snip end

problem infinite_solution_set :
    Infinite { (x, y) : ℕ × ℕ | condition x y } := by
  refine Infinite.of_injective build (fun _ => ?_)
  simp [build]

end Usa2017P1
