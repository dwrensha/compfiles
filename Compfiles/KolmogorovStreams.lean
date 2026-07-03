/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Data.Stream.Defs
import Mathlib.Data.Stream.Init
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!

Puzzle referenced from this tweet: https://twitter.com/sigfpe/status/1474173467016589323

From the book _Out of their Minds: The Lives and Discoveries of 15 Great Computer Scientists_
by Dennis Shasha and Cathy Lazere.


Problem: Suppose each (finite) word is either "decent" or "indecent". Given an infinite
sequence of characters, can you always break it into finite words so that all of them
except perhaps the first one belong to the same class?

-/

namespace KolmogorovStreams
open scoped Stream'

variable {α : Type}

def break_into_words :
   (Stream' ℕ) → -- word lengths
   (Stream' α) → -- original sequence
   (Stream' (List α)) -- sequence of words
 := Function.curry
     (Stream'.corec
       (fun ⟨lengths, a'⟩ ↦ a'.take lengths.head)
       (fun ⟨lengths, a'⟩ ↦ ⟨lengths.tail, a'.drop lengths.head⟩))

snip begin

/--
Dropping the first word is equivalent to dropping `first_length` symbols of the original stream.
-/
lemma break_into_words_cons
    (lengths : Stream' ℕ)
    (first_length : ℕ)
    (a : Stream' α) :
    (break_into_words (first_length::lengths) a).tail =
           break_into_words lengths (a.drop first_length) := by
  simp [break_into_words, Stream'.corec, Stream'.tail_map, Stream'.tail_iterate]

lemma break_into_words_closed_form
    (lengths : Stream' ℕ)
    (a : Stream' α)
   : break_into_words lengths a =
      (fun i ↦ Stream'.take (lengths i) (Stream'.drop (∑ j ∈ Finset.range i, lengths j) a)) := by
  funext n
  induction n generalizing lengths a with
  | zero => rfl
  | succ n ih =>
    have h1 : (break_into_words lengths a).tail =
        break_into_words lengths.tail (a.drop lengths.head) := by
      conv_lhs => rw [← Stream'.eta lengths]
      exact break_into_words_cons _ _ _
    calc break_into_words lengths a (n + 1)
        = break_into_words lengths.tail (a.drop lengths.head) n := congrFun h1 n
      _ = _ := by
            rw [ih]
            simp [Stream'.drop_drop, Finset.sum_range_succ', Nat.add_comm]
            rfl

def all_prefixes (p : List α → Prop) (a : Stream' α) : Prop := a.inits.All p

lemma take_prefix
    (is_decent : List α → Prop)
    (a : Stream' α)
    (ha : all_prefixes is_decent a)
    (n : ℕ)
    (hn : 0 < n) : is_decent (a.take n) := by
  cases n with
  | zero => exact absurd hn (lt_irrefl 0)
  | succ n => simpa [Stream'.get_inits] using ha n

lemma not_all_prefixes
    (is_decent : List α → Prop)
    (a : Stream' α)
    (h : ¬ all_prefixes is_decent a) :
    ∃ n, ¬ is_decent (a.take (Nat.succ n)) := by
  simpa [all_prefixes, Stream'.all_def, Stream'.get_inits] using h

/--
If from every "good" position of the stream we can carve off a nonempty word
satisfying `q`, landing at another good position, then the stream can be broken
into words that all satisfy `q`.
-/
lemma exists_break_into_words
    (q : List α → Prop)
    (good : ℕ → Prop)
    (a : Stream' α)
    (h0 : good 0)
    (h : ∀ n, good n → ∃ k, 0 < k ∧ good (n + k) ∧ q ((a.drop n).take k)) :
    ∃ lengths : Stream' ℕ,
      lengths.All (0 < ·) ∧ (break_into_words lengths a).All q := by
  choose k hpos hgood hq using h
  -- iterate the choice, starting at position 0
  let s : ℕ → {n // good n} :=
    fun i ↦ i.rec ⟨0, h0⟩ fun _ p ↦ ⟨p.1 + k p.1 p.2, hgood p.1 p.2⟩
  let lengths : Stream' ℕ := fun i ↦ k (s i).1 (s i).2
  have hs : ∀ i, (s i).1 = ∑ j ∈ Finset.range i, lengths j := by
    intro i
    induction i with
    | zero => rfl
    | succ n ih => rw [Finset.sum_range_succ, ← ih]
  have hall : (break_into_words lengths a).All q := by
    rw [break_into_words_closed_form]
    intro i
    show q (Stream'.take (lengths i) (Stream'.drop (∑ j ∈ Finset.range i, lengths j) a))
    rw [← hs i]
    exact hq _ _
  exact ⟨lengths, fun i ↦ hpos _ _, hall⟩

snip end

def all_same_class
    (is_decent : List α → Prop)
    (b : Stream' (List α))
    : Prop :=
  b.All is_decent ∨ b.All (fun w ↦ ¬is_decent w)

problem kolmogorov_streams
    (is_decent : List α → Prop)
    (a : Stream' α)
    : (∃ (lengths : Stream' ℕ),
       (lengths.All (0 < ·) ∧
        all_same_class is_decent (break_into_words lengths a).tail)) := by
  obtain ⟨n, hn⟩ | hnot :=
    Classical.em (∃ n : ℕ, ∀ k : ℕ, 0 < k → ¬all_prefixes is_decent (a.drop (n + k)))
  · -- Beyond position n, no tail has all prefixes decent,
    -- so from any position we can carve off an indecent word.
    have hstep : ∀ m, True → ∃ k, 0 < k ∧ True ∧
        ¬is_decent (((a.drop (n + 1)).drop m).take k) := by
      intro m _
      have hm : ¬ all_prefixes is_decent ((a.drop (n + 1)).drop m) := by
        rw [Stream'.drop_drop, show n + 1 + m = n + (m + 1) by lia]
        exact hn (m + 1) m.succ_pos
      obtain ⟨j, hj⟩ := not_all_prefixes is_decent _ hm
      exact ⟨j + 1, j.succ_pos, trivial, hj⟩
    obtain ⟨lengths, hpos, hq⟩ :=
      exists_break_into_words (¬is_decent ·) (fun _ ↦ True) (a.drop (n + 1)) trivial hstep
    refine ⟨(n + 1)::lengths, ?_, ?_⟩
    · intro i
      cases i with
      | zero => exact n.succ_pos
      | succ i => exact hpos i
    · right
      rwa [break_into_words_cons]
  · -- Every position is followed by one from which all prefixes are decent.
    -- Start at such a position and repeatedly carve off decent prefixes.
    push Not at hnot
    obtain ⟨k₀, hk₀, hinit⟩ := hnot 0
    rw [Nat.zero_add] at hinit
    have hstep : ∀ m, all_prefixes is_decent ((a.drop k₀).drop m) →
        ∃ j, 0 < j ∧ all_prefixes is_decent ((a.drop k₀).drop (m + j)) ∧
          is_decent (((a.drop k₀).drop m).take j) := by
      intro m hm
      obtain ⟨j, hj0, hj⟩ := hnot (k₀ + m)
      refine ⟨j, hj0, ?_, take_prefix is_decent _ hm j hj0⟩
      rwa [Stream'.drop_drop, show k₀ + (m + j) = k₀ + m + j by lia]
    obtain ⟨lengths, hpos, hq⟩ :=
      exists_break_into_words is_decent
        (fun m ↦ all_prefixes is_decent ((a.drop k₀).drop m)) (a.drop k₀)
        (by simpa using hinit) hstep
    refine ⟨k₀::lengths, ?_, ?_⟩
    · intro i
      cases i with
      | zero => exact hk₀
      | succ i => exact hpos i
    · left
      rwa [break_into_words_cons]


end KolmogorovStreams
