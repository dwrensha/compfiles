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

theorem sub_sq'' {x y : Int} : x ^ 2 + y ^ 2 = (2 * x * y) ↔ x = y := by
  rw [← sub_eq_zero, ← sub_sq', sq_eq_zero_iff, sub_eq_zero]

problem imo2012_p4 (f : ℤ → ℤ) :
    f ∈ solution_set ↔
    ∀ a b c : ℤ, a + b + c = 0 →
      (f a)^2 + (f b)^2 + (f c)^2 =
        2 * f a * f b + 2 * f b * f c + 2 * f c * f a := by

  constructor

  case mpr =>
    intro constraint

    have «f0=0» : f 0 = 0 := by
      have := constraint 0 0 0
      simp at this
      nlinarith; save

    -- `f` is an even function
    have even (t : ℤ) : f (- t) = f t := by
      have := constraint t (-t) 0
      simp [«f0=0»] at this
      rw [sub_sq''] at this
      symm; exact this

    have P (a b : ℤ) : (f a) ^ 2 + (f b) ^ 2 + f (a + b) ^ 2 = 2 * f a * f b + 2 * f (a + b) * (f a + f b) := by
      have := constraint a b (- (a + b)) (by omega)
      rw [even (a + b)] at this
      rw [this]
      ring

    have «P(a,a)» (a : ℤ) : f (2 * a) = 0 ∨ f (2 * a) = 4 * f a := by
      conv => rhs; rw [← sub_eq_zero]
      rw [← Int.mul_eq_zero]
      have := P a a; simp at this
      rw [← sub_eq_zero] at this; rw [← this]
      ring_nf

    have ext_eq_zero {{a : ℤ}} (h : f a = 0) : ∀ x, f (a * x) = 0 := by
      rintro (x | x)
      rotate_left; rw [← even, Int.neg_mul_eq_mul_neg, Int.neg_negSucc]
      all_goals
        induction' x with x ih
        . simpa

      have := P a (a * (Nat.succ x))
      rotate_left; have := P a (a * x)

      all_goals
        simp at ih; simp [ih, h] at this
        rw [← this]
        congr 1
        simp; ring
      done

    cases «P(a,a)» 1

    case inl «f2=0» =>
      simp at «f2=0»

      have even_zero : ∀ x, f (2 * x) = 0 := ext_eq_zero «f2=0»

      have sub_even {x : ℤ} (a : ℤ) : f x = f (x - 2 * a) := by
        have := P (x - (2 * a)) (2 * a)
        simp [«f2=0», «f0=0», even_zero] at this
        rwa [add_comm, sub_sq''] at this

      have h_odd_const (x : ℤ) : Odd x → f x = f 1 := by
        intro odd
        have ⟨k, hk⟩ := odd
        rw [sub_even k, hk]
        simp

      have f_in_odd_const : f ∈ odd_const := by
        use f 1
        intro x
        constructor

        case left =>
          apply h_odd_const

        case right =>
          rintro ⟨k, hk⟩
          convert even_zero k using 2
          omega
      simpa [solution_set]
      done

    case inr «f2=4*f1» =>
      simp at «f2=4*f1»
      sorry

  -- for all `f` in solution set, `f` satisfies the constraint
  case mp =>
    sorry

end Imo2012P4
