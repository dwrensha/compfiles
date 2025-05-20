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

theorem mod_dvd_not_dvd_add {n d : ℕ} {a : ZMod n} (hn : n ≠ 0)
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

theorem oneof_3_dvd_3 {n : ℕ} (i : ZMod n) (hn : 3 ≤ n) (h : 3 ∣ n) :
    (3 ∣ i.val ∧ ¬3 ∣ (i + 1).val ∧ ¬3 ∣ (i + 2).val) ∨
    (¬3 ∣ i.val ∧ 3 ∣ (i + 1).val ∧ ¬3 ∣ (i + 2).val) ∨
    (¬3 ∣ i.val ∧ ¬3 ∣ (i + 1).val ∧ 3 ∣ (i + 2).val) := by
  have n_ne_0 : n ≠ 0 := Nat.ne_zero_of_lt hn
  have : Fact (1 < n) := ⟨Nat.lt_of_add_left_lt hn⟩

  if h₁ : 3 ∣ i.val then
    refine Or.inl ⟨h₁, ?_, ?_⟩
    . refine mod_dvd_not_dvd_add n_ne_0 h ?_ i h₁
      rw [ZMod.val_one]
      norm_num
    . refine mod_dvd_not_dvd_add n_ne_0 h ?_ i h₁
      rw [ZMod.val_ofNat_of_lt hn]
      norm_num
  else if h₂ : 3 ∣ (i + 1).val then
    refine Or.inr (Or.inl ⟨h₁, h₂, ?_⟩)
    have : (2 : ZMod n) = 1 + 1 := by norm_num
    rw [this, ← add_assoc]
    refine mod_dvd_not_dvd_add n_ne_0 h ?_ (i + 1) h₂
    rw [ZMod.val_one]
    norm_num
  else if h₃ : 3 ∣ (i + 2).val then
    exact Or.inr (Or.inr ⟨h₁, h₂, h₃⟩)
  else
    by_contra
    let ne_0 := mt Nat.dvd_iff_mod_eq_zero.mpr h₁
    let x₂ := mt Nat.dvd_iff_mod_eq_zero.mpr h₂
    let x₃ := mt Nat.dvd_iff_mod_eq_zero.mpr h₃
    rw [ZMod.val_add, Nat.mod_mod_of_dvd _ h, Nat.add_mod] at x₂ x₃
    have : (1 : ZMod n).val = 1 := ZMod.val_one n
    rw [this] at x₂
    have : (2 : ZMod n).val = 2 := ZMod.val_ofNat_of_lt hn
    rw [this] at x₃

    have : i.val % 3 ≤ 2 :=
      Nat.le_of_lt_succ (Nat.mod_lt _ (Nat.zero_lt_succ 2))
    have ne_2 : i.val % 3 ≠ 2 := by
      by_contra h
      apply x₂
      rw [h]

    let eq_0_or_1 :=
      Nat.le_one_iff_eq_zero_or_eq_one.mp
        (Nat.le_of_lt_succ (Nat.lt_of_le_of_ne this ne_2))
    refine eq_0_or_1.elim ne_0 ?_

    by_contra h
    apply x₃
    rw [h]

lemma mod_3_satisfies {n : ℕ} (hn : 3 ≤ n) (h : 3 ∣ n) :
    ∃ a : ZMod n → ℝ, P a := by
  let fn : ZMod n → ℝ := fun i => if 3 ∣ i.val then 2 else -1
  exists fn
  intro i

  refine (oneof_3_dvd_3 i hn h).by_cases ?_ (Or.by_cases · ?_ ?_)
  all_goals {
    intro ⟨h1, h2, h3⟩
    dsimp [fn]
    simp [h1, h2, h3]
    linarith
  }

lemma satisfies_is_mod_3 {n : ℕ} (h : ∃ a : ZMod n → ℝ, P a) :
    3 ∣ n := sorry

snip end

problem imo2018_p2 (n : ℕ) :
    n ∈ solution_set ↔ 3 ≤ n ∧ ∃ a : ZMod n → ℝ, P a := by
  constructor
  · rintro ⟨hn1, hn2⟩
    exact ⟨hn1, mod_3_satisfies hn1 hn2⟩
  · rintro ⟨hn1, hn2⟩
    exact ⟨hn1, satisfies_is_mod_3 hn2⟩

end Imo2018P2
