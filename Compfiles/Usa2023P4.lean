/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Positive.Field
import Mathlib.Tactic

import ProblemExtraction

problem_file

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

abbrev Blackboard (n : ℕ) : Type := Fin n → ℕ+

structure AliceMoveResult {n : ℕ} (a : ℕ+) (b0 : Blackboard n) where
  b : Blackboard n
  i : Fin n
  h1 : b0 i + a = b i
  h2 : ∀ j, j ≠ i → b0 j = b j

abbrev AliceStrategy (n : ℕ) (a : ℕ+) := (b0 : Blackboard n) → AliceMoveResult a b0

abbrev NoValidMoves {n : ℕ} (b : Blackboard n) : Prop := ∀ i, Odd (b i).val

inductive BobMoveResult {n : ℕ} (b0 : Blackboard n) where
| halve :
  (b : Blackboard n) → (i : Fin n) → (b0 i = b i * 2) → (∀ j, j ≠ i → b0 j = b j) →
     BobMoveResult b0
| no_moves : NoValidMoves b0 → BobMoveResult b0

abbrev BobStrategy (n : ℕ) := (b0 : Blackboard n) → BobMoveResult b0

inductive Gamestate' (n : ℕ) where
| active : Blackboard n → Gamestate' n
| done : Gamestate' n

/-- Alice and Bob each make a single move, in sequence. -/
def takeTurn {n : ℕ} (a : ℕ+) (as : AliceStrategy n a) (bs : BobStrategy n)
    : Gamestate' n → Gamestate' n
| .done => .done
| .active b =>
  match bs (as b).b with
  | .halve b .. => .active b
  | .no_moves _ => .done

def is_done {n : ℕ} : Gamestate' n → Prop
| .done => True
| _ => False

problem usa2023_p4 (a : ℕ+) (N : ℕ) (hN : 0 < N) (b0 : Blackboard N)
    (h1 : ∃ bs : BobStrategy N,
           ∀ as : AliceStrategy N a,
             ∃ k, is_done ((takeTurn a as bs)^[k] (.active b0)))
    : ∀ bs : BobStrategy N,
        ∀ as : AliceStrategy N a,
         ∃ k, is_done ((takeTurn a as bs)^[k] (.active b0)) := by
  sorry
