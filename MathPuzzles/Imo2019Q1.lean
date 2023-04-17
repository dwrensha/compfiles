/-
Copyright (c) 2023 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/
import Mathlib.Data.Int.Basic
import Mathlib.Tactic

/-!
# IMO 2019 Q1
Let ℤ be the set of integers. Determine all functions f : ℤ → ℤ such that,
for all integers a and b,￼

   f(2 * a) + 2 * f(b) = f(f(a + b)).

# Solution

Find that g(x) = f(x) - f(0) is linear and then deduce the rest.
-/

lemma mul_from_linear (f : ℤ → ℤ) (h: ∀ (x y : ℤ), f (x + y) = f x + f y):
   ∃ c, ∀ a, f a = c * a := by
  use f 1
  intro a
  induction' a with a a
  · induction' a with a ha
    · simp
      have := h 1 0
      simp at this
      exact this
    · have := h (Int.ofNat a) 1
      rw [ha] at this
      simp only [Int.ofNat_eq_coe] at this
      simp only [Int.ofNat_eq_coe, Nat.cast_succ]
      rw [this]
      ring
  have h₀: Int.negSucc 0 = -1 := by simp
  have h₁ : f (-1) = - f 1 := by
    have := h (Int.negSucc Nat.zero) 1
    simp [h₀] at this
    refine' add_right_cancel _
    exact f 1
    rw [← this]
    have := h 1 0
    simp at this
    ring_nf
    exact this
  · induction' a with a ha
    . simp at h₁
      rw [h₀, h₁]
      ring
    · have : Int.negSucc a + -1  = Int.negSucc (Nat.succ a) := by
        rw [← Int.negSucc_sub_one, Int.add_neg_one]
      rw [← this, h, ha]
      ring_nf
      rw [add_comm, h₁]


theorem imo2019_q1 (f : ℤ → ℤ) (hf : ∀ a b, f (2 * a) + 2 * (f b) = f (f (a + b))) :
  (∀ z,  f z = 0) ∨ (∃ c, ∀ z, f z = 2 * z + c) := by
  let g : ℤ → ℤ := fun z => f z - f 0
  have hg : ∀z, g z = f z - f 0 := by
    intro z
    rfl
  have : ∀ x y, g (x + y) = g x + g y := by
    intro x y
    simp only [hg]
    have hx := hf 0 (x + y)
    have hxy := hf x y
    have hx0 := hf x 0
    have h0x := hf 0 x
    simp at hx hx0 h0x
    linarith
  have : ∃ d, ∀ z, g z = d * z := mul_from_linear g this
  cases' this with d h
  have hz : ∀ z, f z = d * z + f 0 := by
    intro z
    rw [← h z, hg, sub_add_cancel]
  cases' em (d = 0) with hd hd
  · left
    have : f 0 = 0 := by
      have := hf 0 0
      simp at this
      rw [hz (f 0), hz 0, hd] at this
      simp at this
      exact this
    intro z
    convert hz z
    rw [hd, this, zero_mul, add_zero]
  · right
    use f 0
    cases' em (f 0 = 0) with hf₀ hf₀
    · have := hf 1 0
      simp at this
      rw [hz (f 1), hz 2, hz 1, hf₀] at this
      simp [hd] at this
      convert hz
    · have := hf 0 0
      simp at this
      rw [hz (f 0), add_comm, add_right_cancel_iff] at this
      rw [← ne_eq] at hf₀
      have := Int.eq_of_mul_eq_mul_right hf₀ this
      convert hz
