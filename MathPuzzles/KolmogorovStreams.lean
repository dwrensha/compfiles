/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Stream.Defs
import Mathlib.Data.Stream.Init
import Mathlib.Tactic.Ring

import MathPuzzles.Meta.ProblemExtraction

#[problem_setup]/-!

Puzzle referenced from this tweet: https://twitter.com/sigfpe/status/1474173467016589323

From the book _Out of their Minds: The Lives and Discoveries of 15 Great Computer Scientists_
by Dennis Shasha and Cathy Lazere.


Problem: Suppose each (finite) word is either "decent" or "indecent". Given an infinite
sequence of characters, can you always break it into finite words so that all of them
except perhaps the first one belong to the same class?

-/

/-

Answer: yes.

-/


#[problem_setup] namespace KolmogorovStreams
#[problem_setup] open Stream' BigOperators

#[problem_setup] variable {α : Type}

#[problem_setup]
def break_into_words :
   (Stream' ℕ) → -- word lengths
   (Stream' α) → -- original sequence
   (Stream' (List α)) -- sequence of words
 := Function.curry
     (Stream'.corec
       (λ ⟨lengths, a'⟩ ↦ a'.take lengths.head)
       (λ ⟨lengths, a'⟩ ↦ ⟨lengths.tail, a'.drop lengths.head⟩))

--#eval ((break_into_words id id).take 10 )

/--
  Dropping the first word is equivalent to dropping `first_length` symbols of the original stream.
-/
lemma break_into_words_cons
    (lengths : Stream' ℕ)
    (first_length : ℕ)
    (a : Stream' α) :
    (break_into_words (first_length::lengths) a).tail =
           break_into_words lengths (a.drop first_length) := by
  simp [break_into_words, corec, tail_map, tail_iterate]

lemma break_into_words_closed_form
    (lengths : Stream' ℕ)
    (a : Stream' α)
   : break_into_words lengths a =
      (λ i ↦ Stream'.take (lengths i) (Stream'.drop (∑ j in Finset.range i, lengths j) a)) := by
  funext n
  convert_to ((Stream'.corec (λ x ↦ Stream'.take (x.fst.head) x.snd)
                 (λ x ↦ ⟨x.fst.tail, Stream'.drop (x.fst.head) x.snd⟩)) :
                  Stream' ℕ × Stream' α → Stream' (List α)) ⟨lengths, a⟩ n =
             Stream'.take (lengths n) (Stream'.drop (∑ j in Finset.range n, lengths j) a)
  rw [Stream'.corec_def,Stream'.map]
  congr
  · revert a lengths
    induction' n with pn hpn
    · intro a b; rfl
    · intro a b
      rw [Stream'.nth_succ, Stream'.iterate_eq, Stream'.tail_cons, hpn]
      rfl
  · revert a lengths
    induction' n with pn hpn
    · intro a b; rfl
    · intro a b
      rw [Stream'.nth_succ, Stream'.iterate_eq, Stream'.tail_cons, hpn,
          drop_drop, Finset.sum_range_succ']
      congr

#[problem_setup]
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

lemma chosen_decent_closed_form
    (is_decent : List α → Prop)
    (a : Stream' α)
    (hinit: all_prefixes is_decent a)
    (hnot: ∀ (n : ℕ), ∃ (k : ℕ), 0 < k ∧
            all_prefixes is_decent (a.drop (n + k)))
    : ∀ n : ℕ, (((choose_decent_words is_decent a hinit hnot).nth n).start =
              ∑ j in Finset.range n, ((choose_decent_words is_decent a hinit hnot).nth j).length)
            := by
  intro n
  induction' n with n pn
  · rfl
  · rw [Finset.sum_range_succ, ← pn]; rfl

lemma check_decent_words
    (is_decent : List α → Prop)
    (a : Stream' α)
    (hinit: all_prefixes is_decent a)
    (hnot: ∀ (n : ℕ), ∃ (k : ℕ), 0 < k ∧
            all_prefixes is_decent (a.drop (n + k)))
    : Stream'.All
      is_decent
      (break_into_words
          (λ i ↦ ((choose_decent_words is_decent a hinit hnot).nth i).length) a) := by
  rw [break_into_words_closed_form]
  simp_rw [←chosen_decent_closed_form]
  intro j
  exact ((choose_decent_words is_decent a hinit hnot).nth j).h

structure indecent_word (a : Stream' α) (is_decent : List α → Prop) : Type :=
  (start : ℕ)
  (length : ℕ)
  (nonempty : 0 < length)
  (h : ¬is_decent ((a.drop start).take length))

lemma not_all_prefixes
    (is_decent : List α → Prop)
    (a : Stream' α)
    (h : ¬ all_prefixes is_decent a) :
    ∃ n, ¬ is_decent (a.take (Nat.succ n)) := by
  simp[all_prefixes, Stream'.all_def] at h
  exact h

/-
 accumulator is: n, the number of symbols consumed so far
-/
noncomputable def choose_indecent_words
    (is_decent : List α → Prop)
    (a : Stream' α)
    (h: ∀ (k : ℕ), ¬all_prefixes is_decent (a.drop k))
     : Stream' (indecent_word a is_decent) :=
Stream'.corec (λ n ↦ let hd := not_all_prefixes is_decent (a.drop n) (h n)
                     let new_word_length := Nat.succ (Classical.choose hd)
                     let hh := (Classical.choose_spec hd)
                     ⟨n, new_word_length, Nat.succ_pos _, hh⟩
              )
              (λ n ↦ let hd := not_all_prefixes is_decent (a.drop n) (h n)
                     let new_word_length := Nat.succ (Classical.choose hd)
                     n + new_word_length)
              0

lemma chosen_indecent_closed_form
    (is_decent : List α → Prop)
    (a : Stream' α)
    (h: ∀ (k : ℕ), ¬all_prefixes is_decent (a.drop k))
    : ∀ n : ℕ, (((choose_indecent_words is_decent a h).nth n).start =
                ∑ j in Finset.range n, ((choose_indecent_words is_decent a h).nth j).length)
             := by
  intro n
  induction' n with n pn
  · rfl
  · rw [Finset.sum_range_succ, ← pn]
    rfl

lemma check_indecent_words
    (is_decent : List α → Prop)
    (a : Stream' α)
    (h: ∀ (k : ℕ), ¬all_prefixes is_decent (a.drop k))
    : Stream'.All
      (λ x ↦ ¬ is_decent x)
      (break_into_words
          (λ i ↦ ((choose_indecent_words is_decent a h).nth i).length)
          a) := by
  rw [break_into_words_closed_form]
  simp_rw [←chosen_indecent_closed_form]
  intro j
  exact ((choose_indecent_words is_decent a h).nth j).h

problem kolmogorov_streams
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
    let d := choose_indecent_words is_decent a' hn'
    use n.succ::(λ i ↦ (d.nth i).length)
    constructor
    · intro i
      cases' i with i
      · exact Nat.succ_pos n
      · exact (d.nth i).nonempty
    · right
      rw [break_into_words_cons]
      exact check_indecent_words is_decent a' hn'

  · push_neg at hnot; push_neg at hnot -- Bug in push_neg?
    obtain ⟨k, hkp, hinit⟩ := hnot 0
    have hdka : a.drop (0 + k) = a.drop k := by { rw [←Stream'.drop_drop]; rfl }
    rw [hdka] at hinit
    let a' := a.drop k
    have hnot' : ∀ (n : ℕ), ∃ (k : ℕ), 0 < k ∧ all_prefixes is_decent (a'.drop (n + k)) := by
      intro n'
      obtain ⟨k', hk0', hk'⟩ := hnot (k + n')
      use k'
      constructor
      · exact hk0'
      · have hd: (a.drop (k + n' + k')) = (a'.drop (n' + k')) := by
          rw [Stream'.drop_drop]
          ring_nf
        rwa [←hd]
    let d := choose_decent_words is_decent a' hinit hnot'
    use k::(λ i ↦ (d.nth i).length)
    constructor
    · intro i
      cases' i with i
      · exact hkp
      · exact (d.nth i).nonempty
    · left
      rw [break_into_words_cons]
      exact check_decent_words is_decent a' hinit hnot'
