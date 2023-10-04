/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic
import Mathlib

import MathPuzzles.Meta.ProblemExtraction

#[problem_setup]/-!
# USA Mathematical Olympiad 2023, Problem 5

Let n be an integer greater than 2. We will be arranging the numbers
1, 2, ... n² into an n × n grid. Such an arrangement is called *row-valid*
if the numbers in each row can be permuted to make an arithmetic progression.
Similarly, such an arrangement is called *column-valid* if the numbers
in each column can be permuted to make an arithmetic progression.

Determine the values of n for which it possible to transform
any row-valid arrangement into a column-valid arrangment by permuting
the numbers in each row?

-/

#[problem_setup] namespace Usa2023P5

#[problem_setup]
def PermutedArithSeq {n : ℕ} (hn : 0 < n) (f : Fin n ↪ Fin (n^2)) : Prop :=
    ∃ p : Fin n → Fin n, p.Bijective ∧
      ∃ k : ℕ, ∀ m : Fin n, (f (p m)).val = f (p ⟨0, hn⟩) + m.val * k

#[problem_setup]
def row_valid {n : ℕ} (hn : 0 < n) (f : Fin n → Fin n → Fin (n^2)) (hf : f.Injective2) : Prop :=
    ∀ m : Fin n, PermutedArithSeq hn ⟨(f · m), Function.Injective2.left hf m⟩

#[problem_setup]
def col_valid {n : ℕ} (hn : 0 < n) (f : Fin n → Fin n → Fin (n^2)) (hf : f.Injective2) : Prop :=
    ∀ m : Fin n, PermutedArithSeq hn ⟨(f m ·), Function.Injective2.right hf m⟩

#[problem_setup]
theorem injective_of_permuted_rows {α β γ : Type}
    {f : α → β → γ} (hf : f.Injective2) {p : α → α} (hp : p.Injective) :
    Function.Injective2 (fun x ↦ f (p x)) := by
  intro a1 a2 b1 b2 hab
  obtain ⟨hp1, hb1⟩ := hf hab
  exact ⟨hp hp1, hb1⟩

determine solution_set : Set ℕ := { n | n.Prime }

problem usa2023_p5 (n : ℕ) (hn : 2 < n) :
    n ∈ solution_set ↔
    (∀ f : (Fin n → Fin n → Fin (n^2)),
      (hf : f.Injective2) → row_valid (Nat.zero_lt_of_lt hn) f hf →
        ∃ p : Fin n → Fin n, ∃ hp : p.Bijective,
            col_valid (Nat.zero_lt_of_lt hn) (fun x ↦ f (p x))
              (injective_of_permuted_rows hf hp.1)) := by
  constructor
  · sorry
  · sorry
