/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 2012, Problem 4

Determine all functions f : ℤ → ℤ such that for all integers a,b,c with a + b + c = 0,
the following equality holds:
  f(a)² + f(b)² + f(c)² = 2f(a)f(b) + 2f(b)f(c) + 2f(c)f(a).
-/

namespace Imo2012P4

def odd_const : Set (ℤ → ℤ) := fun f =>
  ∃ c : ℤ, ∀ x : ℤ,
    (Odd x → f x = c) ∧ (Even x → f x = 0)

determine solution_set : Set (ℤ → ℤ) := odd_const

problem imo2012_p4 (f : ℤ → ℤ) :
    f ∈ solution_set ↔
    ∀ a b c : ℤ, a + b + c = 0 →
      (f a)^2 + (f b)^2 + (f c)^2 =
        2 * f a * f b + 2 * f b * f c + 2 * f c * f a := by

  constructor

  case mpr =>
    intro constraint

    have zero : f 0 = 0 := by
      have := constraint 0 0 0
      simp at this
      nlinarith

    -- `f` is an even function
    have even (t : ℤ) : f (- t) = f t := by
      have := constraint t (-t) 0
      rw [zero] at this
      simp at this
      replace : (f t - f (- t)) ^ 2 = 0 := by nlinarith
      replace : f t - f (- t) = 0 := by exact sq_eq_zero_iff.mp this
      linarith

    have P (a b : ℤ) : (f a) ^ 2 + (f b) ^ 2 + f (a + b) ^ 2 = 2 * f a * f b + 2 * f (a + b) * (f a + f b) := by
      have := constraint a b (- a - b)
      simp at this

      have lem := even (a + b)
      rw [show - (a + b) = -a - b from by ring] at lem
      rw [lem] at this
      rw [this]
      ring

    have lem : f 2 = 0 ∨ f 2 = 4 * f 1 := by
      have := P 1 1
      simp at this
      rw [show f 1 ^ 2 + f 1 ^ 2 = 2 * f 1 * f 1 from by ring] at this
      simp at this
      replace : f 2 * (f 2 - 4 * f 1) = 0 := by linarith
      rw [@Int.mul_eq_zero] at this

      rcases this with this | this
      · left
        assumption
      · right
        linarith

    rcases lem with lem | lem

    -- when `f 2 = 0`
    case inl =>

      have even_nat_zero (n : ℕ) : f (2 * n) = 0 := by
        induction' n with n ih
        · simpa

        simp
        have := P 2 (2 * n)
        simp [ih, lem] at this
        rw [← this]
        congr 1
        ring

      have even_zero (x : ℤ) : f (2 * x) = 0 := by
        -- without loss of generality, we can assume x ≥ 0.
        wlog pos : x ≥ 0 with H

        case inr =>
          simp at pos
          have := even (- (2 * x)); simp at this
          rw [this]; clear this
          set y := -x with yh
          rw [show - (2 * x) = 2 * y from by ring]
          have ynng : y ≥ 0 := by linarith
          apply H <;> assumption

        -- when `x ≥ 0`
        have := even_nat_zero x.toNat
        rw [← this]
        congr 1
        suffices x = ↑(Int.toNat x) from by
          nth_rw 1 [this]
        exact (Int.toNat_of_nonneg pos).symm

      have add_two_id (a : ℤ) : f (- 1 + 2 * a) = f (1 + 2 * a) := by
        have := P (-1 + 2 * a) 2
        simp [lem, zero] at this
        ring_nf at this
        replace : (f (-1 + a * 2) - f (1 + a * 2)) ^ 2 = 0 := by nlinarith
        simp at this
        rw [show 2 * a = a * 2 from by ring]
        linarith

      have h_odd_const (x : ℤ) : Odd x → f x = f 1 := by
        intro odd
        wlog pos : x ≥ 0 with H

        case inr =>
          simp at pos
          have := even (- x); simp at this
          set y := -x with yh
          rw [this]; clear this
          have ynng : y ≥ 0 := by linarith
          have y_odd : Odd y := by
            have ⟨ k, hk ⟩ := odd
            use - k - 1
            linarith

          apply H <;> assumption

        -- when `x ≥ 0`
        cases x
        case negSucc k => simp_all
        case ofNat x =>
          induction x using Nat.strong_induction_on
          rename_i x ih
          cases x
          contradiction
          rename_i x
          cases x
          rfl
          rename_i x
          rw [show .succ (.succ x) = x + 2 from by rfl] at *
          have ⟨k, hk⟩ := odd
          have x_eq : x = -1 + 2 * k := by
            rw [show Int.ofNat (x + 2) = (x : Int) + 2 from by rfl] at hk
            linarith
          have : f x = f (Int.ofNat (x + 2)) := by
            have add_two := add_two_id k
            rw [add_comm _ 1] at hk
            rw [← x_eq] at add_two
            rw [add_two, hk]
          have odd_x : Odd (Int.ofNat x) := by
            use k - 1
            omega
          rw [← this]
          exact ih x (by simp) odd_x (by simp)


      have f_in_odd_const : f ∈ odd_const := by
        use f 1
        intro x
        constructor

        case left =>
          intro odd
          exact h_odd_const x odd

        case right =>
          intro even
          have ⟨ k, hk ⟩ := even
          rw [hk]
          rw [show k + k = 2 * k from by ring]
          exact even_zero k
      simpa [solution_set]
      done
    -- when `f 2 = 4 * f 1`
    
    sorry
  sorry

end Imo2012P4
