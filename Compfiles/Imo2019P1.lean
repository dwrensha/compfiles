/-
Copyright (c) 2023 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 2019, Problem 1
Let ℤ be the set of integers. Determine all functions f : ℤ → ℤ such that,
for all integers a and b,￼

   f(2 * a) + 2 * f(b) = f(f(a + b)).
-/

namespace Imo2019P1

snip begin

-- proof of the following lemma suggested on Zulip by Riccardo Brasca
lemma additive_to_int_linear (f : ℤ → ℤ) (h: ∀ (x y : ℤ), f (x + y) = f x + f y):
   ∃ c, ∀ a, f a = c * a := by
  let g := AddMonoidHom.toIntLinearMap <| AddMonoidHom.mk' f h
  refine ⟨f 1, fun a => ?_⟩
  change g a = g 1 * a
  exact (Dual.apply_one_mul_eq g a).symm

snip end

determine solution_set : Set (ℤ → ℤ) :=
  { f | (∀ z, f z = 0) ∨ ∃ c, ∀ z, f z = 2 * z + c }

problem imo2019_p1 (f : ℤ → ℤ) :
    (∀ a b, f (2 * a) + 2 * (f b) = f (f (a + b))) ↔ f ∈ solution_set := by
  -- Find that g(x) = f(x) - f(0) is linear and then deduce the rest.

  constructor; swap
  · intro hf a b
    obtain hf1 | hf2 := hf
    · simp [hf1]
    · obtain ⟨c, hc⟩ := hf2
      simp [hc]; ring
  intro hf
  let g : ℤ → ℤ := fun z => f z - f 0
  have hg : ∀z, g z = f z - f 0 := fun z => by rfl
  have : ∀ x y, g (x + y) = g x + g y := by
    intro x y
    simp only [hg]
    have hx := hf 0 (x + y)
    have hxy := hf x y
    have hx0 := hf x 0
    have h0x := hf 0 x
    simp at hx hx0 h0x
    lia
  have ⟨d, h⟩ : ∃ d, ∀ z, g z = d * z := additive_to_int_linear g this
  have hz : ∀ z, f z = d * z + f 0 := by
    intro z
    rw [← h z, hg, sub_add_cancel]
  by_cases hd : d = 0
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
    by_cases hf₀ : f 0 = 0
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


end Imo2019P1
