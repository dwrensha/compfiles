/-
Copyright (c) 2023 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib.Algebra.ModEq
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

lemma three_periodic {n : ℕ} (i c : ZMod n) (a : ZMod n → ℝ)
    [NeZero n] (test : ∀ i : ZMod n, a i = a (i + 3)) :
    a i = a (i + 3 * c) := by
  let k := c.val
  have h_cast : c = ↑k := Eq.symm (ZMod.natCast_zmod_val c)
  rw [h_cast] -- , ← Nat.cast_mul]
  induction k with
  | zero =>
      simp
  | succ d ih =>
      rw [Nat.cast_add, mul_add, Nat.cast_one, ← add_assoc, mul_one]
      rw [← test _]
      exact ih

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

lemma mod_3_satisfies {n : ℕ} (hn : 3 ≤ n) (hd : 3 ∣ n) :
    ∃ a : ZMod n → ℝ, P a := by
  have : Fact (1 < n) := ⟨Nat.lt_of_add_left_lt hn⟩

  let fn : ZMod n → ℝ := fun i => if 3 ∣ i.val then 2 else -1
  exists fn
  intro i

  have :
      (3 ∣ i.val ∧ ¬3 ∣ (i + 1).val ∧ ¬3 ∣ (i + 2).val) ∨
      (¬3 ∣ i.val ∧ 3 ∣ (i + 1).val ∧ ¬3 ∣ (i + 2).val) ∨
      (¬3 ∣ i.val ∧ ¬3 ∣ (i + 1).val ∧ 3 ∣ (i + 2).val) := by
    mod_cases h : i.val % 3
    all_goals {
      repeat rw [Nat.dvd_iff_mod_eq_zero]
      repeat rw [ZMod.val_add, Nat.mod_mod_of_dvd _ hd,
                 Nat.add_mod i.val]
      rw [h, ZMod.val_one, ZMod.val_ofNat_of_lt hn]
      norm_num
    }

  refine this.by_cases ?_ (Or.by_cases · ?_ ?_)
  all_goals {
    intro h
    simp [fn, h]
    linarith
  }

lemma not_dvd_prime_exists_mod_inverse {n p : ℕ}
    (pp : p.Prime) (hn : 1 < n) (h : ¬p ∣ n) :
    ∃ c, p * c ≡ 1 [MOD n] := by
  change ∃ c, _ % n = _ % n
  rw [Nat.mod_eq_of_lt hn]
  refine Nat.exists_mul_emod_eq_one_of_coprime ?_ hn
  exact (pp.coprime_iff_not_dvd).mpr h

lemma not_dvd_prime_exists_mod_inverse' {n p : ℕ}
    (pp : p.Prime) (hn : 1 < n) (h : ¬p ∣ n) :
    ∃ c : ZMod n, ↑p * c = 1 := by
  let ⟨c, hc⟩ := not_dvd_prime_exists_mod_inverse pp hn h
  exists c
  rw [← Nat.cast_mul, ← Nat.cast_one]
  exact (ZMod.natCast_eq_natCast_iff (p * c) 1 n).mpr hc

lemma satisfies_is_mod_3 {n : ℕ} (hn : 3 ≤ n) (h : ∃ a : ZMod n → ℝ, P a) :
    3 ∣ n := by
  have n_gt_1 : 1 < n := Nat.lt_of_add_left_lt hn
  have : Fact (1 < n) := ⟨n_gt_1⟩

  obtain ⟨a, ha⟩ := h
  have {i : ZMod n} : a i = a (i + (Nat.cast 3)) := by sorry
  have three_periodic {i c : ZMod n} : a i = a ((Nat.cast 3) * c + i) := by
    let k := c.val
    have h_cast : c = ↑k := Eq.symm (ZMod.natCast_zmod_val c)
    rw [h_cast]
    induction k with
    | zero =>
        simp
    | succ d ih =>
        rw [Nat.cast_add, mul_add, Nat.cast_one, add_right_comm, mul_one]
        rw [← this]
        exact ih

  by_contra h
  let x := ha 0
  rw [← one_add_one_eq_two, ← add_assoc] at x

  have {i : ZMod n} : a i = a (i + 1) := by
    mod_cases h_dvd : n % 3
    . absurd h
      exact Nat.dvd_of_mod_eq_zero h_dvd
    all_goals {
      let ⟨x, y⟩ := not_dvd_prime_exists_mod_inverse' Nat.prime_three n_gt_1 h
      rw [← y, add_comm, ← three_periodic]
    }
  repeat rw [← this] at x
  apply_fun (· - a 0) at x
  rw [add_sub_right_comm] at x
  field_simp at x

  have : ¬ ∃ x : ℝ, x * x - x + 1 = 0 := by
    intro ⟨x, hx⟩
    suffices x * x - x + 1 ≠ 0 from this hx
    have : x * x - x + 1 = (x - 1/2)^2 + 3/4 := by ring_nf
    have : (x - 1/2)^2 ≥ 0 := sq_nonneg _
    linarith
  apply this
  exists a 0

snip end

problem imo2018_p2 (n : ℕ) :
    n ∈ solution_set ↔ 3 ≤ n ∧ ∃ a : ZMod n → ℝ, P a := by
  constructor
  · rintro ⟨hn1, hn2⟩
    exact ⟨hn1, mod_3_satisfies hn1 hn2⟩
  · rintro ⟨hn1, hn2⟩
    exact ⟨hn1, satisfies_is_mod_3 hn1 hn2⟩

end Imo2018P2
