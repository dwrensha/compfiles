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

def all_prefixes (p : List α → Prop) (a : Stream' α) : Prop := a.inits.All p

lemma take_prefix
    (is_decent : List α → Prop)
    (a : Stream' α)
    (ha : all_prefixes is_decent a)
    (n : ℕ)
    (hn : 0 < n) : is_decent (a.take n) := by
  cases' n with n
  · exfalso; exact Nat.lt_asymm hn hn
  · have ht := ha n
    rwa [Stream'.nth_inits] at ht

structure decent_word (a : Stream' α) (is_decent: List α → Prop) : Type :=
  (start : ℕ)
  (length : ℕ)
  (nonempty : 0 < length)
  (h : is_decent ((a.drop start).take length))

structure decent_accumulator (a: Stream' α) (is_decent : List α → Prop) : Type :=
  (start : ℕ)
  (prefix_decent : all_prefixes is_decent (a.drop start))

noncomputable def choose_decent_words
    (is_decent : List α → Prop)
    (a : Stream' α)
    (hinit: all_prefixes is_decent a)
    (hnot: ∀ (n : ℕ), ∃ (k : ℕ), 0 < k ∧
            all_prefixes is_decent (a.drop (n + k)))
     : Stream' (decent_word a is_decent) :=
Stream'.corec (λ (acc: decent_accumulator a is_decent) ↦
                  let new_word_length := Classical.choose (hnot acc.start)
                  let new_word_nonempty := (Classical.choose_spec (hnot acc.start)).1
                  ⟨acc.start, new_word_length, new_word_nonempty,
                   take_prefix
                    is_decent _ acc.prefix_decent new_word_length new_word_nonempty⟩)
             (λ acc ↦ ⟨acc.start + Classical.choose (hnot acc.start),
                      (Classical.choose_spec (hnot acc.start)).2⟩)
             ⟨0, hinit⟩

theorem kolmogorov_streams
    (is_decent : List α → Prop)
    (a : Stream' α)
    : (∃ (lengths : Stream' ℕ),
       (lengths.All (0 < ·)  ∧
        all_same_class is_decent (break_into_words lengths a).tail)) := by
  let p : Prop :=
     (∃ (n : ℕ), ∀ (k : ℕ), 0 < k → ¬all_prefixes is_decent (a.drop (n + k)))

  obtain h | hnot := Classical.em p
  · obtain ⟨n, hn⟩ := h
    let a' := a.drop (n + 1)
    have hn' : ∀ (k : ℕ), ¬all_prefixes is_decent (a'.drop k) := by
      intro k
      have hnk := hn (k + 1) (Nat.succ_pos _)
      rwa [Stream'.drop_drop, Nat.add_left_comm]
    sorry
  · push_neg at hnot
    --obtain ⟨k, hkp, hinit⟩ := hnot 0
    --have hdka : a.drop (0 + k) = a.drop k := by { rw [←Stream'.drop_drop]; rfl }
    sorry
