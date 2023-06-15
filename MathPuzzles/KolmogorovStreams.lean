/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Data.Stream.Defs
import Mathlib.Data.Stream.Init

/-

Puzzle referenced from this tweet: https://twitter.com/sigfpe/status/1474173467016589323

From the book _Out of their Minds: The Lives and Discoveries of 15 Great Computer Scientists_
by Dennis Shasha and Cathy Lazere.


Problem: Suppose each (finite) word is either "decent" or "indecent". Given an infinite
sequence of characters, can you always break it into finite words so that all of them
except perhaps the first one belong to the same class?

Answer: yes.

-/


namespace KolmogorovStreams

variable {α : Type}

def break_into_words :
   (Stream' ℕ) → -- word lengths
   (Stream' α) → -- original sequence
   (Stream' (List α)) -- sequence of words
 := Function.curry
     (Stream'.corec
       (λ ⟨lengths, a'⟩ ↦ a'.take lengths.head)
       (λ ⟨lengths, a'⟩ ↦ ⟨lengths.tail, a'.drop lengths.head⟩))

--#eval ((break_into_words id id).take 10 )

def all_same_class
    (is_decent : List α → Prop)
    (b : Stream' (List α))
    : Prop :=
  b.All is_decent ∨ b.All (λ w ↦ ¬is_decent w)

theorem kolmogorov_streams
    (is_decent : List α → Prop)
    (a : Stream' α)
    : (∃ (lengths : Stream' ℕ),
       (lengths.All (0 < ·)  ∧
        all_same_class is_decent (break_into_words lengths a).tail)) := by
  sorry
