/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib

import ProblemExtraction

problem_file {
  problemImportedFrom :=
    "https://github.com/jsm28/IMOLean/blob/main/IMO/IMO2021P5.lean"
}

/-!
# International Mathematical Olympiad 2021, Problem 5

Two squirrels, Bushy and Jumpy, have collected 2001 walnuts for winter.
Jumpy numbers the walnuts from 1 to 2021, and digs 2021 little holes
in a circular pattern around their favorite tree. The next morning,
Jumpy notices that Bushy had placed one walnut into each hole, but
had paid no attention to the numbering. Unhappy, Jumpy decides to
reorder the walnuts by performing a sequence of 2021 moves. In the kth
move, Jump swaps the positions of the two walnuts adjacent to walnut k.

Prove that there exists a value of k such that, on the kth move, Jumpy
swaps some walnuts a and b such that a < k < b.
-/

namespace Imo2021P5

/-- The arrangement of walnuts, as an equiv from holes to walnuts (0-based). -/
abbrev Position : Type := Fin 2021 ≃ Fin 2021

/-- The numbers of the walnuts swapped in move `k` (0-based), given the position. -/
def Position.swapped (p : Position) (k : Fin 2021) : Fin 2021 × Fin 2021 :=
  (p ((p.symm k) - 1), p ((p.symm k) + 1))

/-- A single move, on a pair of position and move number. -/
def move (p : Position × Fin 2021) : Position × Fin 2021 :=
  (p.1.trans (Equiv.swap (p.1.swapped p.2).1 (p.1.swapped p.2).2), p.2 + 1)

/-- The position after `n` moves. -/
def Position.nth (p : Position) (n : Fin 2021) : Position := (move^[n] (p, 0)).1

problem imo2021_p5 (p : Position) :
    ∃ k, (((p.nth k).swapped k).1 < k ∧ k < ((p.nth k).swapped k).2) ∨
      (((p.nth k).swapped k).2 < k ∧ k < ((p.nth k).swapped k).1) := by
  sorry

end Imo2021P5
