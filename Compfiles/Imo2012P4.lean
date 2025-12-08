/-
Copyright (c) 2023 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: spinylobster, ondanaoto, Seasawher
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

snip begin

def odd_const : Set (ℤ → ℤ) := fun f =>
  ∃ c : ℤ, ∀ x : ℤ,
    (Odd x → f x = c) ∧ (Even x → f x = 0)

def mod4_cycle : Set (ℤ → ℤ) := fun f =>
  ∃ c : ℤ, ∀ x : ℤ, f x =
  match x % 4 with
    | 0 => 0
    | 2 => 4 * c
    | _ => c

def square_set : Set (ℤ → ℤ) := fun f =>
  ∃ c : ℤ, ∀ x : ℤ, f x = x ^ 2 * c

theorem sub_sq'' {x y : Int} : x ^ 2 + y ^ 2 = (2 * x * y) ↔ x = y := by
  rw [← sub_eq_zero, ← sub_sq', sq_eq_zero_iff, sub_eq_zero]

theorem Int.lt_of_ns_lt_ns {x x' : ℕ} (h : Int.negSucc x < Int.negSucc x') : x' < x := by
  grind

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
          rw [← Int.ofNat_eq_natCast, ← Int.ofNat_eq_natCast]
          simp [sizeOf, Int._sizeOf_1]
        apply myInduction <;> assumption
    case negSucc =>
      rw [← add4]
      cases h : Int.negSucc x + 4
      case ofNat x' =>
        match x' with
        | 0 => exact P0
        | 1 => exact P1
        | 2 => exact P2
        | 3 => exact P3
        | x' + 4 => simp at h
      case negSucc x' =>
        have : x' < x := by
          have := Int.sub_lt_self (Int.negSucc x + 4) (b := 4) (h := by simp)
          conv at this => rhs; rw [h]
          simp at this
          apply Int.lt_of_ns_lt_ns this
        apply myInduction <;> assumption

snip end

determine solution_set : Set (ℤ → ℤ) := odd_const ∪ mod4_cycle ∪ square_set

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
      nlinarith

    -- `f` is an even function
    have even (t : ℤ) : f (- t) = f t := by
      have := constraint t (-t) 0
      simp [«f0=0»] at this
      rw [sub_sq''] at this
      symm; exact this

    have P (a b : ℤ) : (f a) ^ 2 + (f b) ^ 2 + f (a + b) ^ 2 =
                       2 * f a * f b + 2 * f (a + b) * (f a + f b) := by
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
      intro x
      induction' x using Int.induction_on with x ih i
      · simp [«f0=0»]
      · specialize P (a * x) a; simp_all
        simpa only [mul_add, mul_one] using P
      · have := P (a * ( -↑i - 1 )) a
        ring_nf at *
        aesop

    cases «P(a,a)» 1

    case inl «f2=0» =>
      simp at «f2=0»

      have even_zero : ∀ x, f (2 * x) = 0 := ext_eq_zero «f2=0»

      have sub_even {x : ℤ} (a : ℤ) : f x = f (x - 2 * a) := by
        have := P (x - (2 * a)) (2 * a)
        simp [even_zero] at this
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
      left
      left
      assumption

    case inr «f2=4*f1» =>
      simp at «f2=4*f1»

      have when_f4_is_0 («f4=0» : f 4 = 0) : mod4_cycle f := by
        exists f 1
        have «f(x+4)=fx» (x : ℤ) : f (x + 4) = f x := by
          have «P(4,x)» := P 4 x
          simp [«f4=0»] at «P(4,x)»
          rw [show 2 * f (4 + x) * f x = 2 * f x * f (4 + x) by ac_rfl, sub_sq''] at «P(4,x)»
          rw [«P(4,x)»]; ac_rfl

        intro x; induction x using myInduction
        case P0 => simp [«f0=0»]
        case P1 => simp
        case P2 => simp [«f2=4*f1»]
        case P3 => rw [show 3 = -1 + 4 by rfl, «f(x+4)=fx», even]; simp
        case add4 x => simp; rw [«f(x+4)=fx»]

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
            simp [«f3=f1», «f4=4*f2»] at «P(1,3)» ⊢
            rw [← sub_eq_zero] at «P(1,3)»; ring_nf at «P(1,3)»
            simp [mul_eq_zero] at «P(1,3)»
            assumption

        have := when_f4_is_0 «f4=0»
        left
        right
        assumption

      case inl «f3=9*f1» =>

        cases «P(2,2)»

        case inl «f4=0» =>
          have := when_f4_is_0 «f4=0»
          left
          right
          assumption

        case inr «f4=16*f1» =>
          have «fx=x²f1» (x : ℤ) : f x = x ^ 2 * f 1 := by
            wlog pos : x ≥ 0 with H

            case inr =>
              rcases x with x | x; case ofNat => simp at pos
              rw [Int.negSucc_eq, even, neg_pow_two]
              apply H <;> try assumption
              · omega

            rcases x with x | x; case negSucc => simp at pos
            induction x using Nat.strongRecOn with
            | ind x ih =>
              rcases x with _ | x; case zero => simp [«f0=0»]

              have «fx=x²f1» : f x = x ^ 2 * f 1 := by apply ih <;> simp
              have := P x 1
              rw [«fx=x²f1», ← sub_eq_zero] at this
              replace this : (f (x + 1) - (x - 1) ^ 2 * f 1) *
                             (f (x + 1) - (x + 1) ^ 2 * f 1) = 0 := by
                rw [← this]; ring
              rw [mul_eq_zero, sub_eq_zero, sub_eq_zero] at this

              rcases this with «f(x+1)=(x-1)²*f1» | goal; case inr => exact goal

              have := P (x + 1) (-2)
              rw [show (x : ℤ) + 1 + (-2) = x - 1 by omega, even] at this
              have «f(x-1)=(x-1)²*f1» : f ((x : ℤ) - 1) = ((x : ℤ) - 1) ^ 2 * f 1 := by
                by_cases h : (x : ℤ) - 1 ≥ 0
                · rcases x with _ | x
                  case pos.zero => simp [even]
                  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
                  apply ih
                  · lia
                  · simp

                simp at h; simp [h, even]

              rw [«f2=4*f1», «f(x-1)=(x-1)²*f1», ← sub_eq_zero] at this
              replace this : (f (x + 1) - (x + 1) ^ 2 * f 1) *
                             (f (x + 1) - ((x : ℤ) - 3) ^ 2 * f 1) = 0 := by
                rw [← this]; ring_nf
              rw [mul_eq_zero, sub_eq_zero, sub_eq_zero] at this

              rcases this with goal | «f(x+1)=(x-3)²*f1»; case inl => exact goal
              have := «f(x+1)=(x-3)²*f1»
              rw [«f(x+1)=(x-1)²*f1», mul_eq_mul_right_iff, pow_eq_pow_iff_cases] at this
              lia

          right
          use f 1

  -- for all `f` in solution set, `f` satisfies the constraint
  case mp =>
    rintro ((sol | sol) | sol)
    all_goals
      intro a b c H
      have c_eq : c = - (a + b) := by omega
      rcases sol with ⟨d, h⟩

    · have ⟨hal, har⟩ := h a
      have ⟨hbl, hbr⟩ := h b
      have ⟨hcl, hcr⟩ := h c
      rcases Int.even_or_odd a with evena | odda <;>
      rcases Int.even_or_odd b with evenb | oddb
      · have hc : Even c := by
          rw [← even_neg, c_eq, neg_neg]
          exact Even.add evena evenb
        simp_all
      · have hc : Odd c := by
          rw [← odd_neg, c_eq, neg_neg]
          exact Even.add_odd evena oddb
        simp_all
        ring
      · have hc : Odd c := by
          rw [← odd_neg, c_eq, neg_neg]
          exact Even.odd_add evenb odda
        simp_all
        ring
      · have hc : Even c := by
          rw [← even_neg, c_eq, neg_neg]
          exact Odd.add_odd odda oddb
        simp_all
        ring

    · grind
    · rw [c_eq, h, h, h]
      ring_nf

end Imo2012P4
