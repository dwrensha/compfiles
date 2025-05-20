/-
Copyright (c) 2023 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 2018, Problem 2

Determine all integers n ≥ 3 such that there exist real numbers
a₁, a₂, ..., aₙ satisfying

  aᵢaᵢ₊₁ + 1 = aᵢ₊₂,

where the indices are taken mod n.
-/

namespace Imo2018P2

determine solution_set : Set ℕ := { n | 3 ≤ n ∧ 3 ∣ n }

abbrev P {n : ℕ} (a : ZMod n → ℝ) :=
  ∀ (i : ZMod n), a i * a (i + 1) + 1 = a (i + 2)

snip begin

theorem mod_dvd_not_dvd_add' {n d : ℕ} {a : ZMod n} (hn : n ≠ 0)
    (hd : d ∣ n) (ha : ¬d ∣ a.val) :
    ∀ i : ZMod n, d ∣ i.val → ¬d ∣ (i + a).val := by
  have : NeZero n := ⟨hn⟩
  have d_ne_0 : d ≠ 0 :=
    ne_zero_of_dvd_ne_zero hn hd

  intro i hi
  by_contra h
  obtain ⟨x, y⟩ := h
  let y := congrArg (· % d) y
  dsimp at y
  rw [ZMod.val_add, Nat.mod_mod_of_dvd _ hd,
      Nat.mul_mod_right, Nat.add_mod,
      Nat.mod_eq_zero_of_dvd hi, Nat.zero_add,
      Nat.mod_mod] at y
  apply ha
  exact Nat.dvd_of_mod_eq_zero y

theorem mod_dvd_not_dvd_add {n d a : ℕ} (hn : n ≠ 0)
    (hd : d ∣ n) (ha : 0 < a ∧ a < d) :
    ∀ i : ZMod n, d ∣ i.val → ¬ (d ∣ (i + a).val) := by
  have : NeZero n := ⟨hn⟩
  have d_le_n : d ≤ n :=
    Nat.le_of_dvd (Nat.zero_lt_of_ne_zero hn) hd

  intro i hi
  by_contra h
  obtain ⟨x, y⟩ := h
  let y := congrArg (· % d) y
  dsimp at y
  rw [ZMod.val_add, Nat.mod_mod_of_dvd _ hd,
      Nat.mul_mod_right, Nat.add_mod,
      Nat.mod_eq_zero_of_dvd hi, Nat.zero_add,
      Nat.mod_mod, ZMod.val_natCast,
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le ha.2 d_le_n),
      Nat.mod_eq_of_lt ha.2] at y
  exact ha.1.ne.symm y

lemma mod_3_satisfies {n : ℕ} (hn : 1 < n) (h : 3 ∣ n) :
    ∃ a : ZMod n → ℝ, P a := by
  have n_ne_0 : n ≠ 0 := Nat.ne_zero_of_lt hn
  have : Fact (1 < n) := ⟨hn⟩
  let fn : ZMod n → ℝ := fun i => if 3 ∣ i.val then 2 else -1
  exists fn
  intro i

  have : (3 ∣ i.val ∧ ¬3 ∣ (i + 1).val ∧ ¬3 ∣ (i + 2).val) ∨
         (¬3 ∣ i.val ∧ 3 ∣ (i + 1).val ∧ ¬3 ∣ (i + 2).val) ∨
         (¬3 ∣ i.val ∧ ¬3 ∣ (i + 1).val ∧ 3 ∣ (i + 2).val) :=
    if hi : 3 ∣ i.val then
      have : ¬3 ∣ (i + 1).val := by
        refine mod_dvd_not_dvd_add' n_ne_0 h ?_ i hi
        rw [ZMod.val_one]
        norm_num
      have : ¬3 ∣ (i + 2).val := by
        refine mod_dvd_not_dvd_add' n_ne_0 h ?_ i hi
        have : ZMod.val (2 : ZMod n) = 2 := by
          rw [ZMod.val_natCast]
          sorry
        rw [ZMod.val_one]
        norm_num
      sorry
    else
      sorry

  refine this.by_cases ?_ (Or.by_cases · ?_ ?_)
  <;> intro ⟨h1, h2, h3⟩
  <;> dsimp [fn]
  <;> simp [h1, h2, h3]
  <;> linarith

lemma satisfies_is_mod_3 {n : ℕ} (h : ∃ a : ZMod n → ℝ, P a) :
    3 ∣ n := sorry

snip end

problem imo2018_p2 (n : ℕ) :
    n ∈ solution_set ↔ 3 ≤ n ∧ ∃ a : ZMod n → ℝ, P a := by
  constructor
  · rintro ⟨hn1, hn2⟩
    have : 1 < n := Nat.lt_of_add_left_lt hn1
    exact ⟨hn1, mod_3_satisfies this hn2⟩
  · rintro ⟨hn1, hn2⟩
    exact ⟨hn1, satisfies_is_mod_3 hn2⟩

end Imo2018P2
