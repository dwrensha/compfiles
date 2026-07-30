/-
Copyright (c) 2026 lean-tom. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-tom, Kimi K3
-/

module

public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 1974, Problem 4

A, B, C play a series of games. Each game is between two players.
The next game is between the winner and the person who was not playing.
The series continues until one player has won two games. He wins the series.
A is the weakest player, C the strongest. Each player has a fixed probability
of winning against a given opponent. A chooses who plays the first game.
Show that he should choose to play himself against B.
-/

namespace Usa1974P4

/-- The three players of the series. -/
inductive Player | A | B | C
  deriving DecidableEq

/-- The player who sits out a game between `x` and `y`.
Only meaningful for `x ≠ y`; returns `A` on the diagonal. -/
def third : Player → Player → Player
  | .A, .B => .C
  | .B, .A => .C
  | .A, .C => .B
  | .C, .A => .B
  | .B, .C => .A
  | .C, .B => .A
  | _, _ => .A

/-- The probability that player `A` wins the series, where

* `win x y` is the probability that `x` beats `y` in a single game,
* the next game is played between `w` (the winner of the previous game)
  and `i` (the player who sat out the previous game); the loser of a game
  sits out the next one,
* `hist` is the list of winners of the games played so far, and
* `n` is a fuel bounding the number of games still to be played.

The series ends as soon as some player has won two games in total, so it
lasts at most four games: if no one has won twice after three games then the
three winners so far are three distinct players, and the fourth game is played
between two of them, so its winner reaches two wins. -/
def probWinA (win : Player → Player → ℝ) :
    ℕ → Player → Player → List Player → ℝ
  | 0, _, _, _ => 0
  | n + 1, w, i, hist =>
      win w i * (if w ∈ hist then (if w = .A then 1 else 0)
                 else probWinA win n w (third w i) (w :: hist)) +
      win i w * (if i ∈ hist then (if i = .A then 1 else 0)
                 else probWinA win n i (third w i) (i :: hist))

/-- The probability that A wins the series when the first game is A against B. -/
def probFirstAB (win : Player → Player → ℝ) : ℝ := probWinA win 4 .A .B []

/-- The probability that A wins the series when the first game is A against C. -/
def probFirstAC (win : Player → Player → ℝ) : ℝ := probWinA win 4 .A .C []

/-- The probability that A wins the series when the first game is B against C. -/
def probFirstBC (win : Player → Player → ℝ) : ℝ := probWinA win 4 .B .C []

snip begin

/-- Expanding the game tree when the first game is A against B: writing XbY for
"X beats Y", A wins the series exactly via the outcome sequences
AbB · AbC, AbB · CbA · BbC · AbB, and BbA · CbB · AbC · AbB. -/
lemma probFirstAB_eq (win : Player → Player → ℝ)
    (hBA : win .B .A = 1 - win .A .B) (hCA : win .C .A = 1 - win .A .C)
    (hCB : win .C .B = 1 - win .B .C) :
    probFirstAB win =
      win .A .B * win .A .C + win .A .B * (1 - win .A .C) * win .B .C * win .A .B +
        (1 - win .A .B) * (1 - win .B .C) * win .A .C * win .A .B := by
  simp [probFirstAB, probWinA, third, hBA, hCA, hCB]
  ring

/-- Expanding the game tree when the first game is A against C: A wins the series
exactly via the outcome sequences AbC · AbB, AbC · BbA · CbB · AbC, and
CbA · BbC · AbB · AbC. -/
lemma probFirstAC_eq (win : Player → Player → ℝ)
    (hBA : win .B .A = 1 - win .A .B) (hCA : win .C .A = 1 - win .A .C)
    (hCB : win .C .B = 1 - win .B .C) :
    probFirstAC win =
      win .A .C * win .A .B + win .A .C * (1 - win .A .B) * (1 - win .B .C) * win .A .C +
        (1 - win .A .C) * win .B .C * win .A .B * win .A .C := by
  simp [probFirstAC, probWinA, third, hBA, hCA, hCB]
  ring

/-- Expanding the game tree when the first game is B against C: A wins the series
exactly via the outcome sequences BbC · AbB · AbC and CbB · AbC · AbB. -/
lemma probFirstBC_eq (win : Player → Player → ℝ)
    (hBA : win .B .A = 1 - win .A .B) (hCA : win .C .A = 1 - win .A .C)
    (hCB : win .C .B = 1 - win .B .C) :
    probFirstBC win =
      win .B .C * win .A .B * win .A .C + (1 - win .B .C) * win .A .C * win .A .B := by
  simp [probFirstBC, probWinA, third, hBA, hCA, hCB]
  ring

snip end

problem usa1974_p4
    (win : Player → Player → ℝ)
    (hwin : ∀ x y : Player, x ≠ y → 0 < win x y ∧ win x y + win y x = 1)
    -- "A is the weakest player, C the strongest"; the proof only uses that A is
    -- more likely to beat B than to beat C.
    (hweak : win Player.A Player.C < win Player.A Player.B) :
    probFirstBC win < probFirstAB win ∧ probFirstAC win < probFirstAB win := by
  have hBA : win .B .A = 1 - win .A .B := by
    have h := (hwin .A .B (by decide)).2; linarith
  have hCA : win .C .A = 1 - win .A .C := by
    have h := (hwin .A .C (by decide)).2; linarith
  have hCB : win .C .B = 1 - win .B .C := by
    have h := (hwin .B .C (by decide)).2; linarith
  rw [probFirstAB_eq win hBA hCA hCB, probFirstAC_eq win hBA hCA hCB,
    probFirstBC_eq win hBA hCA hCB]
  have ha0 : 0 < win .A .B := (hwin .A .B (by decide)).1
  have hb0 : 0 < win .A .C := (hwin .A .C (by decide)).1
  have hc0 : 0 < win .B .C := (hwin .B .C (by decide)).1
  have ha1 : win .A .B < 1 := by
    have h1 := (hwin .A .B (by decide)).2; have h2 := (hwin .B .A (by decide)).1; linarith
  have hb1 : win .A .C < 1 := by
    have h1 := (hwin .A .C (by decide)).2; have h2 := (hwin .C .A (by decide)).1; linarith
  have hc1 : win .B .C < 1 := by
    have h1 := (hwin .B .C (by decide)).2; have h2 := (hwin .C .B (by decide)).1; linarith
  have ha1' : (0:ℝ) < 1 - win .A .B := sub_pos.mpr ha1
  have hb1' : (0:ℝ) < 1 - win .A .C := sub_pos.mpr hb1
  have hab' : (0:ℝ) < win .A .B - win .A .C := sub_pos.mpr hweak
  -- Abbreviate a = win A B, b = win A C, c = win B C. Then
  -- P(AB first) − P(BC first) = a²c(1−b) + ab(1−a)(1−c) > 0 and
  -- P(AB first) − P(AC first) = ac(1−b)(a−b) + b(1−a)(1−c)(a−b) > 0.
  have g1 : 0 < win .A .B * (1 - win .A .C) * win .B .C * win .A .B :=
    mul_pos (mul_pos (mul_pos ha0 hb1') hc0) ha0
  have g2 : 0 < (1 - win .A .B) * (1 - win .B .C) * win .A .C * win .A .B :=
    mul_pos (mul_pos (mul_pos ha1' (sub_pos.mpr hc1)) hb0) ha0
  have u1 : 0 < (1 - win .A .C) * win .B .C * win .A .B * (win .A .B - win .A .C) :=
    mul_pos (mul_pos (mul_pos hb1' hc0) ha0) hab'
  have u2 : 0 < (1 - win .A .B) * (1 - win .B .C) * win .A .C * (win .A .B - win .A .C) :=
    mul_pos (mul_pos (mul_pos ha1' (sub_pos.mpr hc1)) hb0) hab'
  constructor
  · nlinarith [g1, g2]
  · nlinarith [u1, u2]

end Usa1974P4
