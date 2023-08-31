/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finite.Basic

import Mathlib.Tactic.IntervalCases

/-!
# USA Mathematical Olympiad 2002, Problem 1

Let S be a set with 2002 elements, and let N be an integer with

  0 ≤ N ≤ 2^2002.

Prove that it is possible to color every subset of S either blue or
red so that the following conditions hold:

 a) the union of any two red subsets is red;
 b) the union of any two blue subsets is blue;
 c) there are exactly N red subsets.
-/

namespace Usa2002Q1

inductive Color : Type where
| red : Color
| blue : Color
deriving DecidableEq

lemma usa2002q1_generalized
    {α : Type} [DecidableEq α] [Fintype α] (n : ℕ) (hs : Fintype.card α = n)
    (N : ℕ) (hN : N ≤ 2 ^ n) :
    ∃ f : Finset α → Color,
      ((∀ s1 s2 : Finset α, f s1 = f s2 → f (s1 ∪ s2) = f s1) ∧
       (Fintype.card { a : Finset α // f a = Color.red } = N)) := by
  -- Informal solution from https://artofproblemsolving.com.
  -- Let a set colored in such a manner be called *properly colored*.
  -- We prove that any set with n elements can be properly colored for any
  -- 0 ≤ N ≤ 2ⁿ. We proceed by induction.

  revert N α
  induction' n
  · -- The base case, n = 0, is trivial.
    intros α hde hft hs N hN
    rw[Nat.pow_zero] at hN
    interval_cases N
    · use λ s ↦ Color.blue
      simp only [forall_true_left, forall_const, true_and]
      have h1 : ∀ a : Finset α, ¬ Color.blue = Color.red := λ s ↦ by
         intro; injections
      have h2 := Subtype.isEmpty_of_false h1
      exact Fintype.card_eq_zero
    · use λ s ↦ Color.red
      simp only [forall_true_left, forall_const, true_and]
      let p := λ a : Finset α ↦ Color.red = Color.red
      have h1 : ∀ a : Finset α, p a := λ s ↦ rfl
      have h3 : Fintype.card (Finset α) = 1 := by simp[hs]
      convert_to Fintype.card Set.univ = 1
      simp only [Fintype.card_ofFinset, Finset.mem_univ, forall_true_left, forall_const,
                 Finset.filter_true_of_mem]
      exact h3
  · -- Suppose that our claim holds for n = k. Let s ∈ S, |S| = k + 1, and let
    -- S' denote the set of all elements of S other than s.

    sorry
    -- If N ≤ 2ᵏ, then we may color blue all subsets of S which contain s,
    -- and we may properly color S'. This is a proper coloring because the union
    -- of any two red sets must be a subset of S', which is properly colored, and
    -- any the union of any two blue sets either must be in S', which is properly
    -- colored, or must contain s and therefore be blue.

    -- If N > 2ᵏ, then we color all subsets containing s red, and we color
    -- N - 2ᵏ elements of S' red in such a way that S' is colored properly.
    -- Then S is properly colored, using similar reasoning as before.
    -- Thus the induction is complete.

theorem usa2002q1
    {α : Type} [DecidableEq α] [Fintype α] (hs : Fintype.card α = 2002)
    (N : ℕ) (hN : N ≤ 2 ^ 2002) :
    ∃ f : Finset α → Color,
      ((∀ s1 s2 : Finset α, f s1 = f s2 → f (s1 ∪ s2) = f s1) ∧
       (@Fintype.card
           { a : Finset α // f a = Color.red } (Fintype.ofFinite _) = N)) := by
  exact usa2002q1_generalized 2002 hs N hN
