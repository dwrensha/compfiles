/-
Copyright (c) 2024 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Data.Set.Card
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Olympiad 2001, Problem 3

Twenty-one girls and twenty-one boys took part in a mathematical competition.
It turned out that each contestant solved at most six problems, and for each
pair of a girl and a boy, there was at most one problem solved by both the
girl and the boy. Show that there was a problem solved by at least three
girls and at least three boys.
-/

namespace Imo2001P3

problem imo2001_p3 {Girl Boy Problem : Type}
    [Finite Girl] [Finite Boy] [Finite Problem]
    (girl_card : Nat.card Girl = 21)
    (boy_card : Nat.card Boy = 21)
    (girl_solved : Girl → Problem → Prop)
    (boy_solved : Boy → Problem → Prop)
    (hG : ∀ g : Girl, Set.ncard {p | girl_solved g p} ≤ 6)
    (hB : ∀ b : Boy, Set.ncard {p | boy_solved b p} ≤ 6)
    (hp : ∀ g : Girl, ∀ b : Boy, Set.ncard {p | girl_solved g p ∧ boy_solved b p} ≤ 1)
    : ∃ p : Problem, 3 ≤ Set.ncard {g | girl_solved g p} ∧
                     3 ≤ Set.ncard {g | boy_solved g p} := by
  sorry
