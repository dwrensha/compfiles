/-
Copyright (c) 2026 lean-tom. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-tom (with assistance from Gemini)
-/

import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

import ProblemExtraction

problem_file

/-!
# International Mathematical Olympiad 1986, Problem 3

To each vertex of a regular pentagon, an integer is assigned,
in such a way that the sum of all five numbers is positive.
If three consecutive vertices are assigned the numbers $x, y, z$ respectively and $y < 0$,
then the following operation is allowed: $x, y, z$ are replaced by $x+y, -y, z+y$ respectively.
Such an operation is performed repeatedly as long as at least one of the five numbers is negative.
Determine whether this procedure necessarily comes to an end after a finite number of steps.
-/

namespace Imo1986P3

open BigOperators

/-- State of the pentagon: an integer assigned to each vertex. -/
def State := Fin 5 → ℤ

/-- The sum of all integers on the pentagon. -/
def State.sum (s : State) : ℤ := ∑ i : Fin 5, s i

/-- The operation performed at vertex `i` when `s i < 0`. -/
def move (s : State) (i : Fin 5) : State :=
  fun j =>
    if j == i - 1 then s (i - 1) + s i
    else if j == i     then -s i
    else if j == i + 1 then s (i + 1) + s i
    else s j

/--
The transition relation `Step next current` asserts that `next` is obtained
from `current` by applying the move operation at some vertex `i` where `s i < 0`.
The order of arguments `(next current)` is chosen to match the convention of `Acc`.
-/
def Step (next current : State) : Prop :=
  ∃ i : Fin 5, current i < 0 ∧ next = move current i

snip begin

/-!
## Solution

We define a potential function $V(s) = \sum (s_i - s_{i+2})^2$.
We show that:
1. The sum of all integers is invariant under the operation.
2. If the sum is positive, the potential strictly decreases.
3. Since the potential is a sum of squares, it is bounded below by 0.
4. Since the potential takes integer values and strictly decreases, the process must terminate.
-/

/-- The potential function $V(s) = \sum (s_i - s_{i+2})^2$. -/
def potential (s : State) : ℤ :=
  ∑ i : Fin 5, (s i - s (i + 2))^2

/-- Helper lemma to expand sums over `Fin 5`. -/
lemma sum_fin5 (f : Fin 5 → ℤ) :
    (∑ i : Fin 5, f i) = f 0 + f 1 + f 2 + f 3 + f 4 := by
  simp [Finset.sum]; abel

/-- The sum of the integers is invariant under the move operation. -/
lemma sum_invariant (s : State) (i : Fin 5) : (move s i).sum = s.sum := by
  simp only [State.sum, sum_fin5]
  fin_cases i
  all_goals (
    simp (config := { decide := true }) [move]
    try simp only [show (-1 : Fin 5) = 4 by decide]
    abel
  )

/-- The change in potential after a move operation.
    $V(s') - V(s) = 2 \cdot s_i \cdot S$ where $S$ is the total sum. -/
lemma potential_diff (s : State) (i : Fin 5) :
    potential (move s i) - potential s = 2 * (s i) * s.sum := by
  simp only [potential, State.sum, sum_fin5]
  fin_cases i
  all_goals (
    simp (config := { decide := true }) [move]
    try simp only [show (-1 : Fin 5) = 4 by decide]
    ring
  )

/-- If $s_i < 0$ and the total sum is positive, the potential strictly decreases. -/
lemma potential_decreasing (s : State) (i : Fin 5) (h_neg : s i < 0) (h_sum_pos : 0 < s.sum) :
    potential (move s i) < potential s := by
  have h_diff := potential_diff s i
  have h_rhs_neg : 2 * (s i) * s.sum < 0 := by
    nlinarith [h_neg, h_sum_pos]
  linarith [h_diff, h_rhs_neg]

/-- The potential is always non-negative. -/
lemma potential_nonneg (s : State) : 0 ≤ potential s := by
  rw [potential]
  exact Finset.sum_nonneg (fun i _ => sq_nonneg (s i - s (i + 2)))

/-- Since the potential is non-negative and decreasing,
    its value as a natural number also decreases. -/
lemma potential_measure_decreases (s : State) (i : Fin 5)
    (h_neg : s i < 0) (h_sum : 0 < s.sum) :
    (potential (move s i)).toNat < (potential s).toNat := by
  have h_pos_s : 0 < potential s := by
    linarith [potential_decreasing s i h_neg h_sum, potential_nonneg (move s i)]
  rw [Int.toNat_lt_toNat h_pos_s]
  exact potential_decreasing s i h_neg h_sum

snip end

/--
Main Theorem: IMO 1986 Problem 3.
Starting from any state with a positive sum, the process terminates.
-/
problem imo1986_p3 (s₀ : State) (h_sum : 0 < s₀.sum) :
    Acc Step s₀ := by
  apply measure_termination s₀ h_sum
where
  measure_termination (current : State) (h_current_sum : 0 < current.sum) : Acc Step current := by
    generalize h_n : (potential current).toNat = n
    revert current h_current_sum h_n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro current h_current_sum h_n_eq
      subst h_n_eq
      apply Acc.intro
      intro next_state h_step
      rcases h_step with ⟨i, h_neg, rfl⟩
      have h_next_sum : 0 < (move current i).sum := by
        rw [sum_invariant]
        exact h_current_sum
      apply ih ((potential (move current i)).toNat)
      · apply potential_measure_decreases current i h_neg h_current_sum
      · exact h_next_sum
      · rfl

end Imo1986P3
