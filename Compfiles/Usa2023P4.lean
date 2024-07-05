/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# USA Mathematical Olympiad 2023, Problem 4

Positive integers a and N are fixed, and N positive integers are written on
a blackboard. Alice and Bob play the following game. On Alice's turn, she must
replace some integer n on the board with n + a, and on Bob's turn he must
replace some even integer n on the board with n/2. Alice goes first and they
alternate turns. If Bob has no valid moves on his turn the game ends.

After analyzing the N integers on the board, Bob realizes that, regardless of
what moves Alices makes, he will be able to force the game to end eventually.
Show that, in fact, no matter what either player does, for these values of a and N
and these particular N integers, the game is guaranteed to end, regardless of
either player's moves.
-/

namespace Usa2023P4

inductive Player where
| Alice : Player
| Bob : Player

abbrev Blackboard (n : ℕ) := Fin n → ℕ+

structure State (n : ℕ) where
  board : Blackboard n
  turn : Player

theorem halve_even (x : ℕ+) (he : Even x.val) : 0 < x.val / 2 := by
   obtain ⟨x, hx⟩ := x
   obtain ⟨t, ht⟩ := he
   dsimp at *; omega

def valid_moves (a : ℕ+) (n : ℕ) : State n → Set (State n)
| ⟨b, .Alice⟩ =>
      {s | ∃ i : Fin n, s = ⟨Function.update b i (b i + a), .Bob⟩}
| ⟨b, .Bob⟩ =>
      {s | ∃ i : Fin n,
           ∃ he : Even (b i).val,
           s = ⟨Function.update b i ⟨b i / 2, halve_even _ he⟩,
                .Alice⟩}

inductive BobCanForceEnd (a : ℕ+) (n : ℕ) : State n → Prop where
| BaseCase (b : Blackboard n) :
    valid_moves a n ⟨b, .Bob⟩ = ∅ → BobCanForceEnd a n ⟨b, .Bob⟩
| BobTurn (b : Blackboard n) (m : State n) :
          (m ∈ valid_moves a n ⟨b, .Bob⟩) → BobCanForceEnd a n m →
          BobCanForceEnd a n ⟨b, .Bob⟩
| AliceTurn (b : Blackboard n) :
            (∀ m ∈ valid_moves a n ⟨b, .Alice⟩, BobCanForceEnd a n m) →
            BobCanForceEnd a n ⟨b, .Alice⟩

inductive EndIsInevitable (a : ℕ+) (n : ℕ) : State n → Prop where
| BaseCase (s : State n) : valid_moves a n s = ∅ → EndIsInevitable a n s
| Step (s : State n)
       (h : ∀ m ∈ valid_moves a n s, EndIsInevitable a n m) :
       EndIsInevitable a n s

problem usa2023_p4 (a : ℕ+) (N : ℕ) (hN : 0 < N) (b0 : Blackboard N)
    (he : BobCanForceEnd a N ⟨b0, .Alice⟩) :
    EndIsInevitable a N ⟨b0, .Alice⟩ := by
  sorry
