/-
Copyright (c) 2023 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clayton Knittel
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

abbrev P {n : ℕ} (a : ZMod n → ℝ) :=
  ∀ (i : ZMod n), a i * a (i + 1) + 1 = a (i + 2)

snip begin

lemma not_dvd_prime_exists_mod_inverse {n p : ℕ} [NeZero n]
    (pp : p.Prime) (hn : 1 < n) (h : ¬p ∣ n) :
    ∃ c : ZMod n, p * c = 1 := by
  let ⟨c, hc⟩ := Nat.exists_mul_emod_eq_one_of_coprime
    ((pp.coprime_iff_not_dvd).mpr h) hn
  exists c
  rw [← Nat.cast_one, ← Nat.cast_mul, ZMod.natCast_eq_natCast_iff]
  change _ % n = _ % n
  rw [Nat.mod_eq_of_lt hn]
  exact hc

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
    norm_num
  }

lemma three_periodic {n : ℕ} [NeZero n] {i : ZMod n} {a : ZMod n → ℝ} (ha : P a)
    : a i = a (i + 3) := by
  have (i : ZMod n) : a (i + 2) ^ 2 - a (i + 2) = a i * a (i + 3) - a i := by
    calc
      _ = a i * a (i + 1) * a (i + 2) := by rw [← ha i]; ring_nf
      _ = a i * (a (i + 1 + 2) - 1) := by rw [← ha (i + 1)]; ring_nf
      _ = a i * a (i + 3) - a i := by ring_nf

  have : ∑ i, a i ^ 2 = ∑ i, a i * a (i + 3) := by
    have h : ∑ i : ZMod n, (a (i + 2) ^ 2 - a (i + 2)) =
             ∑ i : ZMod n, (a i * a (i + 3) - a i) :=
      Finset.sum_congr rfl (fun i _ => this i)
    repeat rw [Finset.sum_sub_distrib] at h

    have := Equiv.sum_comp (Equiv.addRight 2) a
    dsimp at this
    rw [this] at h

    have : ∑ i, a (i + 2) ^ 2 = ∑ i, a i ^ 2:=
      Equiv.sum_comp (Equiv.addRight 2) ((a ·) ^ 2)
    rw [this] at h

    apply_fun (· + ∑ i, a i) at h
    simp at h
    exact h

  have : 2 * (∑ i, a i ^ 2 - ∑ i, a i * a (i + 3)) = 0 := by
    rw [sub_eq_zero.mpr this]
    norm_num

  have : 0 = ∑ i, (a i - a (i + 3)) ^ 2 := by
    calc
      0 = 2 * (∑ i, a i ^ 2 - ∑ i, a i * a (i + 3)) := this.symm
      _ = ∑ i, a i ^ 2 + ∑ i, a i ^ 2 - 2 * ∑ i, a i * a (i + 3) := by ring_nf
      _ = ∑ i, a i ^ 2 + ∑ i, a (i + 3) ^ 2 - 2 * ∑ i, a i * a (i + 3) := by
        have := Equiv.sum_comp (Equiv.addRight 3) ((a ·) ^ 2)
        dsimp at this
        rw [this]
      _ = ∑ i, (a i ^ 2 + a (i + 3) ^ 2 - 2 * a i * a (i + 3)) := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
        simp only [mul_assoc]
      _ = ∑ i, (a i - a (i + 3)) ^ 2 := by ring_nf

  have {i : ZMod n} : (a i - a (i + 3)) ^ 2 = 0 := by
    refine (Finset.sum_eq_zero_iff_of_nonneg ?_).mp this.symm i ?_
    · exact fun _ _ => sq_nonneg _
    · exact Finset.mem_univ _

  apply_fun (· - a (i + 3)) using add_left_injective _
  dsimp
  rw [pow_eq_zero this]
  norm_num

lemma satisfies_is_mod_3 {n : ℕ} (hn : 3 ≤ n) (h : ∃ a : ZMod n → ℝ, P a) :
    3 ∣ n := by
  have n_gt_1 : 1 < n := Nat.lt_of_add_left_lt hn
  have : Fact (1 < n) := ⟨n_gt_1⟩
  obtain ⟨a, ha⟩ := h

  have three_periodic' {i c : ZMod n} : a i = a (3 * c + i) := by
    rw [← ZMod.natCast_zmod_val c]
    induction c.val with
    | zero => simp
    | succ d ih =>
      rw [Nat.cast_add, mul_add, Nat.cast_one, mul_one,
          add_right_comm, ← three_periodic ha]
      exact ih

  by_contra h
  let ha_0 := ha 0
  rw [← one_add_one_eq_two, ← add_assoc] at ha_0

  have {i : ZMod n} : a i = a (i + 1) := by
    mod_cases h_dvd : n % 3
    · absurd h
      exact Nat.dvd_of_mod_eq_zero h_dvd
    all_goals {
      let ⟨x, y⟩ := not_dvd_prime_exists_mod_inverse Nat.prime_three n_gt_1 h
      dsimp at y
      rw [← y, add_comm, ← three_periodic']
    }
  repeat rw [← this] at ha_0
  apply_fun (· - a 0) at ha_0
  rw [add_sub_right_comm] at ha_0
  field_simp at ha_0

  have : ¬∃ x : ℝ, x * x - x + 1 = 0 := by
    intro ⟨x, hx⟩
    suffices x * x - x + 1 ≠ 0 from this hx
    have : x * x - x + 1 = (x - 1/2)^2 + 3/4 := by ring_nf
    have : (x - 1/2)^2 ≥ 0 := sq_nonneg _
    linarith
  apply this
  exists a 0
  linarith

snip end

determine solution_set : Set ℕ := { n | 3 ≤ n ∧ 3 ∣ n }

problem imo2018_p2 (n : ℕ) :
    n ∈ solution_set ↔ 3 ≤ n ∧ ∃ a : ZMod n → ℝ, P a := by
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₁, mod_3_satisfies h₁ h₂⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₁, satisfies_is_mod_3 h₁ h₂⟩

end Imo2018P2
