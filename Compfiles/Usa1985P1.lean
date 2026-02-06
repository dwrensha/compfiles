/-
Copyright (c) 2024 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# USA Mathematical Olympiad 1985, Problem 1

Determine whether or not there are any positive integral solutions of
the simultaneous equations

          x₁² + x₂² + ⋯ + x₁₉₈₅² = y³
          x₁³ + x₂³ + ⋯ + x₁₉₈₅³ = z²

with distinct integers x₁, x₂, ⋯, x₁₉₈₅.
-/

namespace Usa1985P1

snip begin

lemma nicomachus (n : ℕ) :
    ∑ i ∈ Finset.range n, i^3 = (∑ i ∈ Finset.range n, i)^2 := by
  induction' n with n ih
  · simp
  rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
  have h1 : ((∑ x ∈ Finset.range n, x) + n) ^ 2 =
      ((∑ x ∈ Finset.range n, x))^2 +
         (2 * (∑ x ∈ Finset.range n, x) * n +
           n ^ 2) := by ring
  rw [h1]
  have h2 : n ^ 3 = 2 * (∑ x ∈ Finset.range n, x) * n + n ^ 2 := by
    have h5 : 2 * ∑ x ∈ Finset.range n, x =
               (∑ x ∈ Finset.range n, x) * 2 := mul_comm _ _
    rw [h5, Finset.sum_range_id_mul_two]
    cases n with
    | zero => simp
    | succ n =>
      simp only [Nat.succ_sub_succ_eq_sub, tsub_zero]
      ring
  lia

lemma nicomachus' (n : ℕ) :
    ∑ i ∈ Finset.range n, ((i:ℤ) + 1)^3 =
    (∑ i ∈ Finset.range n, ((i:ℤ) + 1))^2 := by
  norm_cast
  have h1 := nicomachus (n + 1)
  simp only [Finset.sum_range_succ', add_zero] at h1
  exact h1

snip end

determine does_exist : Bool := true

abbrev is_valid (x : ℕ → ℤ) (y z : ℤ) : Prop :=
    (∀ i ∈ Finset.range 1985, 0 < x i) ∧
    0 < y ∧ 0 < z ∧
    ∑ i ∈ Finset.range 1985, x i ^ 2 = y ^ 3 ∧
    ∑ i ∈ Finset.range 1985, x i ^ 3 = z ^ 2 ∧
    ∀ i ∈ Finset.range 1985, ∀ j ∈ Finset.range 1985, i ≠ j → x i ≠ x j

problem usa1985_p1 :
    if does_exist
    then ∃ x y z, is_valid x y z
    else ¬ ∃ x y z, is_valid x y z := by
  -- solution from
  -- https://artofproblemsolving.com/wiki/index.php/1985_USAMO_Problems/Problem_1
  simp only [ite_true]
  let j : ℤ := ∑ ii ∈ Finset.range 1985, (ii + 1)
  let k : ℤ := ∑ ii ∈ Finset.range 1985, (ii + 1)^2
  let x := fun (ii : ℕ) ↦ ((ii + 1):ℤ) * k ^ 4

  have h0 : ∀ ii ∈ Finset.range 1985, 0 < (ii:ℤ) + 1 := by
    intro ii _
    exact Int.pos_of_sign_eq_one rfl

  have h4 : ∀ ii ∈ Finset.range 1985, 0 < ((ii:ℤ) + 1)^2 := by
    intro ii _
    exact Int.pos_of_sign_eq_one rfl

  have hne : (Finset.range 1985).Nonempty := by aesop
  have h3 : 0 < (∑ ii ∈ Finset.range 1985, ((ii:ℤ) + 1) ^ 2) := by
    exact Finset.sum_pos h4 hne

  use x, k^3, k^6 * j
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ii hii
    dsimp [x]
    have h1 : 0 < (ii : ℤ) + 1 := h0 ii hii
    have h2 : 0 < (∑ ii ∈ Finset.range 1985, ((ii:ℤ) + 1) ^ 2) ^ 4 := by
      exact pow_pos h3 4
    exact Int.mul_pos h1 h2
  · exact pow_pos h3 3
  · have h20 : 0 < k^6 := pow_pos h3 6
    have h21 : 0 < j := Finset.sum_pos h0 hne
    exact Int.mul_pos h20 h21
  · have h5 : ∑ i ∈ Finset.range 1985, x i ^ 2 =
              ∑ i ∈ Finset.range 1985, (((i : ℤ) + 1) ^ 2 * k ^ 8) := by
      rw [Finset.sum_congr rfl]
      intro l _
      unfold x
      have h10 : ∀ a b : ℤ, (a * b^4)^2 = a^2 * b ^8 := by intro a b; ring
      exact h10 _ _

    have h9 : ∀ k : ℤ, k * k^8 = (k^3) ^ 3 := fun k ↦ by ring
    calc
      _ = ∑ i ∈ Finset.range 1985, (((i : ℤ)+1) ^ 2 * k ^ 8) := h5
      _ = (∑ i ∈ Finset.range 1985, (((i : ℤ)+1) ^ 2)) * k ^ 8 := by rw [Finset.sum_mul]
      _ = k * k^8 := by rfl
      _ = _ := h9 k

  · have h5 : ∑ i ∈ Finset.range 1985, x i ^ 3 =
              ∑ i ∈ Finset.range 1985, (((i:ℤ) + 1) ^ 3 * k^12) := by
      rw [Finset.sum_congr rfl]
      intro l _
      unfold x
      have h10 : ∀ a b : ℤ, (a * b^4)^3 = a^3 * b^12 := by intro a b; ring
      exact h10 _ _

    have h9 : ∀ j k : ℤ, j^2 * k^12 = (k^6 * j) ^ 2 := fun j k ↦ by ring
    calc
      _ = _ := h5
      _ = (∑ i ∈ Finset.range 1985, (((i:ℤ) + 1) ^ 3)) * k^12 := by rw [Finset.sum_mul]
      _ = j^2 * k^12 := by rw [nicomachus']
      _ = _ := h9 _ _

  · intro ii _ jj _ hij
    have hsm : StrictMono x := by
      intro a b hab
      dsimp only [x]
      have h5 : (a:ℤ) + 1 < (b:ℤ) + 1 := by linarith
      have h6 : 0 < (∑ ii ∈ Finset.range 1985, ((ii:ℤ) + 1) ^ 2) ^ 4 := by
        exact pow_pos h3 4
      exact Int.mul_lt_mul_of_pos_right h5 h6
    obtain h10 | h11 : ii < jj ∨ jj < ii := Nat.lt_or_gt.mp hij
    · exact ne_of_lt (hsm h10)
    · exact (ne_of_lt (hsm h11)).symm


end Usa1985P1
