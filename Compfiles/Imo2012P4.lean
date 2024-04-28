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

def mod4 (x : Int) : Fin 4 := by
  refine ⟨(x % 4).natAbs, ?_⟩
  have pos : 0 ≤ x % 4 := by omega
  have lt : x % 4 < 4 := by omega
  revert pos lt; cases (x % 4) <;> intro pos lt
  . simp [Int.natAbs] at lt ⊢; assumption
  . simp at pos

theorem mod4_eq (x : Int) : (mod4 x : Int) = x % 4 := by
  simp [mod4]; apply Int.emod_nonneg; simp

theorem mod4_add_eq (x : Int) : mod4 (x + 4) = mod4 x := by simp [mod4]

theorem Int.lt_of_ns_lt_ns {x x' : ℕ} (h : Int.negSucc x < Int.negSucc x') : x' < x := by
  have := Int.neg_lt_neg h
  rw [Int.neg_negSucc, Int.neg_negSucc, Int.ofNat_lt] at this
  apply Nat.lt_of_succ_lt_succ this

def myInduction.{u}
  {motive : ℤ -> Sort u}
  (P0 : motive 0) (P1 : motive 1) (P2 : motive 2) (P3 : motive 3)
  (add4 : ∀ x, motive (x + 4) = motive x)
  : ∀ x, motive x := by
    rintro (x | x)
    case ofNat =>
      match x with
      | 0 => exact P0
      | 1 => exact P1
      | 2 => exact P2
      | 3 => exact P3
      | x' + 4 =>
        rw [show Int.ofNat (x' + 4) = (Int.ofNat x') + 4 by rfl, add4]
        have : sizeOf (x' : Int) < sizeOf ((x' + 4 : Nat) : Int) := by
          rw [← Int.ofNat_eq_coe, ← Int.ofNat_eq_coe]
          simp [sizeOf, Int._sizeOf_1]
        apply myInduction <;> assumption
      done
    case negSucc =>
      rw [← add4]
      cases h : Int.negSucc x + 4
      case ofNat x' =>
        match x' with
        | 0 => exact P0
        | 1 => exact P1
        | 2 => exact P2
        | 3 => exact P3
        | x' + 4 => simp at h; done
      case negSucc x' =>
        have : x' < x := by
          have := Int.sub_lt_self (Int.negSucc x + 4) (b := 4) (h := by simp)
          conv at this => rhs; rw [h]
          simp at this
          apply Int.lt_of_ns_lt_ns this
        apply myInduction <;> assumption
        done
      done
    done


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

      have when_f4_is_0 («f4=0» : f 4 = 0) : ∀ x, f x = [0, f 1, 4 * f 1, f 1][mod4 x] := by
        have «f(x+4)=fx» (x : ℤ) : f (x + 4) = f x := by
          have «P(4,x)» := P 4 x
          simp [«f4=0»] at «P(4,x)»
          rw [show 2 * f (4 + x) * f x = 2 * f x * f (4 + x) by ac_rfl, sub_sq''] at «P(4,x)»
          rw [«P(4,x)»]; ac_rfl

        intro x; induction x using myInduction
        case P0 => simp [«f0=0», mod4]
        case P1 => simp [mod4]
        case P2 => simp [«f2=4*f1», mod4]
        case P3 => rw [show 3 = -1 + 4 by rfl, «f(x+4)=fx», even]; simp [mod4]
        case add4 x => rw [«f(x+4)=fx», mod4_add_eq]

      have «P(1,2)» : f 3 = 9 * f 1 ∨ f 3 = f 1 := by
        have := P 1 2
        rw [«f2=4*f1», ← sub_eq_zero] at this
        rw [← sub_eq_zero, ← sub_eq_zero (a := f 3), ← Int.mul_eq_zero, ← this]
        ring_nf

      have «P(2,2)» : f 4 = 0 ∨ f 4 = 16 * f 1 := by convert «P(a,a)» 2 using 2; omega

      cases «P(1,2)»

      case inr «f3=f1» =>

        have «f4=0» : f 4 = 0 := by
          cases «P(2,2)»; case inl «f4=0» => assumption
          case inr «f4=4*f2» =>
            have «P(1,3)» := P 1 3
            simp [«f3=f1», «f4=4*f2», «f2=4*f1»] at «P(1,3)» ⊢
            rw [← sub_eq_zero] at «P(1,3)»; ring_nf at «P(1,3)»
            simp [mul_eq_zero, pow_eq_zero_iff'] at «P(1,3)»
            assumption

        have := when_f4_is_0 «f4=0»
        sorry

      case inl «f3=9*f1» =>

        cases «P(2,2)»

        case inl «f4=0» =>
          have := when_f4_is_0 «f4=0»
          sorry

        case inr «f4=16*f1» =>
          sorry
  -- for all `f` in solution set, `f` satisfies the constraint
  case mp =>
    sorry

end Imo2012P4
