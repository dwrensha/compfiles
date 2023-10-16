/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic
import Mathlib

import Compfiles.Meta.ProblemExtraction

#[problem_setup]/-!
# USA Mathematical Olympiad 2023, Problem 5

Let n be an integer greater than 2. We will be arranging the numbers
1, 2, ... n² into an n × n grid. Such an arrangement is called *row-valid*
if the numbers in each row can be permuted to make an arithmetic progression.
Similarly, such an arrangement is called *column-valid* if the numbers
in each column can be permuted to make an arithmetic progression.

Determine the values of n for which it possible to transform
any row-valid arrangement into a column-valid arrangement by permuting
the numbers in each row.

-/

#[problem_setup] namespace Usa2023P5

#[problem_setup]
def PermutedArithSeq {n : ℕ} (hn : 0 < n) (a : Fin n ↪ Fin (n^2)) : Prop :=
    ∃ p : Fin n → Fin n, p.Bijective ∧
      ∃ k : ℕ, ∀ m : Fin n, (a (p m)).val = a (p ⟨0, hn⟩) + m.val * k

#[problem_setup]
def row_valid {n : ℕ} (hn : 0 < n) (a : Fin n → Fin n → Fin (n^2)) (ha : a.Injective2) : Prop :=
    ∀ r : Fin n, PermutedArithSeq hn ⟨(a r ·), Function.Injective2.right ha r⟩

#[problem_setup]
def col_valid {n : ℕ} (hn : 0 < n) (a : Fin n → Fin n → Fin (n^2)) (ha : a.Injective2) : Prop :=
    ∀ c : Fin n, PermutedArithSeq hn ⟨(a · c), Function.Injective2.left ha c⟩

#[problem_setup]
theorem injective_of_permuted_rows {α β γ : Type}
    {f : α → β → γ} (hf : f.Injective2) {p : α → β → β} (hp : ∀ a, (p a).Injective) :
    Function.Injective2 (fun r c ↦ f r (p r c)) := by
  intro a1 a2 b1 b2 hab
  obtain ⟨ha1, hp1⟩ := hf hab
  rw [ha1] at *
  rw [hp a2 hp1]
  simp only [and_self]

determine solution_set : Set ℕ := { n | n.Prime }

problem usa2023_p5 (n : ℕ) (hn : 2 < n) :
    n ∈ solution_set ↔
    (∀ a : (Fin n → Fin n → Fin (n^2)),
      (ha : a.Injective2) → row_valid (Nat.zero_lt_of_lt hn) a ha →
        ∃ p : Fin n → Fin n → Fin n, ∃ hp : (∀ r, (p r).Injective),
            col_valid (Nat.zero_lt_of_lt hn) (fun r c ↦ a r (p r c))
              (injective_of_permuted_rows ha hp)) := by
  constructor
  · sorry
  · sorry
