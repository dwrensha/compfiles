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

import MathPuzzles.Meta.Attributes

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

@[problem_setup]
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
  induction' n with k ih
  · -- The base case, n = 0, is trivial.
    intros α hde hft hs N hN
    rw[Nat.pow_zero] at hN
    interval_cases N
    · use λ s ↦ Color.blue
      simp only [forall_true_left, forall_const, true_and, Fintype.card_eq_zero]
    · use λ s ↦ Color.red
      simp [Fintype.card_subtype, Finset.card_univ, hs]
  · -- Suppose that our claim holds for n = k. Let s ∈ S, |S| = k + 1, and let
    -- S' denote the set of all elements of S other than s.
    intros S hde hft hs N hN
    have s : S := Nonempty.some (Fintype.card_pos_iff.mp (by rw[hs]; exact Nat.succ_pos k))
    let S' := {a : S // a ≠ s}

    obtain hl | hg := le_or_gt N (2 ^ k)
    · -- If N ≤ 2ᵏ, then we may color blue all subsets of S which contain s,
      -- and we may properly color S'. This is a proper coloring because the union
      -- of any two red sets must be a subset of S', which is properly colored, and
      -- any the union of any two blue sets either must be in S', which is properly
      -- colored, or must contain s and therefore be blue.
      have hs' : Fintype.card S' = k := by simp[Fintype.card_subtype_compl, hs]
      obtain ⟨f', hf1', hf2'⟩ := ih hs' N hl
      let f (x: Finset S) : Color :=
        if h: s ∈ x
        then Color.blue
        else f' (Finset.subtype _ x)
      use f
      have h2 : ∀ a : Finset S, (f a = Color.red ↔ s ∉ a ∧ f' (Finset.subtype _ a) = Color.red) := by
        intros a
        constructor
        · intro ha
          have haa : s ∉ a := by
            intro hns
            simp [hns] at ha
          constructor
          · exact haa
          · simp [haa] at ha
            exact ha
        · intro hsa
          simp[hsa]
      constructor
      · intros s1 s2 hs12
        have h3 := h2 s1
        obtain ⟨h4, h5⟩ := h3
        sorry


      · sorry
    . -- If N > 2ᵏ, then we color all subsets containing s red, and we color
      -- N - 2ᵏ elements of S' red in such a way that S' is colored properly.
      -- Then S is properly colored, using similar reasoning as before.
      -- Thus the induction is complete.
      sorry

@[problem_statement]
theorem usa2002q1
    {α : Type} [DecidableEq α] [Fintype α] (hs : Fintype.card α = 2002)
    (N : ℕ) (hN : N ≤ 2 ^ 2002) :
    ∃ f : Finset α → Color,
      ((∀ s1 s2 : Finset α, f s1 = f s2 → f (s1 ∪ s2) = f s1) ∧
       (Fintype.card
           { a : Finset α // f a = Color.red } = N)) := by
  exact usa2002q1_generalized 2002 hs N hN
