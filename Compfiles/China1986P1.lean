/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: sjfhsjfh
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Real.Basic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# China Mathematical Olympiad 1986, Problem 1

a₁, a₂, …, aₙ 为实数，如果它们中任意两数之和非负，那么对于满足
x₁ + x₂ + … + xₙ = 1 的任意非负实数 x₁, x₂, …, xₙ，
有不等式 a₁x₁ + a₂x₂ + … + aₙxₙ ≥ a₁x₁² + a₂x₂² + … + aₙxₙ² 成立。
请证明上述命题及其逆命题。

We are given n real numbers a₁, a₂, …, aₙ such that the sum of any two of them
is non‑negative. Prove that the following statement and its converse are both true:
if n non‑negative reals x₁, x₂, …, xₙ satisfy x₁ + x₂ + … + xₙ = 1,
then the inequality a₁x₁ + a₂x₂ + … + aₙxₙ ≥ a₁x₁² + a₂x₂² + … + aₙxₙ² holds.
-/

namespace China1986P1

open Finset

problem china1986_p1 (n : ℕ) (a : Fin n → ℝ)
  : (∀ i j : Fin n, i ≠ j → a i + a j ≥ 0)
    ↔ ∀ x : Fin n → ℝ, (∀ i, x i ≥ 0) → ∑ i, x i = 1
      → ∑ i, a i * x i ≥ ∑ i, a i * x i ^ 2 := by
  match n with
  | 0 => simp
  | 1 => simp; intro x _ hx; simp only [Fin.isValue, hx, one_pow, mul_one, le_refl]
  | n + 2 =>
  refine ⟨?mp, ?mpr⟩
  case mpr =>
    intro hx i j hij
    let f := fun k ↦ if k = i ∨ k = j then (1 : ℝ) / 2 else 0
    have h_f_nonneg (i : Fin (n + 2)) : f i ≥ 0 := by
      simp [f]; split_ifs <;> norm_num
    have h_f_sum : ∀ g : Fin (n + 2) → ℝ, ∑ k, g k =
      g i + g j + ∑ k ∈ (Finset.univ.erase i).erase j, g k := by
      intro g
      have h1 := sum_erase_add (.univ : Finset (Fin (n + 2))) g <| mem_univ i
      have h2 := sum_erase_add (univ.erase i) g <| mem_erase.mpr ⟨hij.symm, mem_univ j⟩
      rewrite [← h1, ← h2, add_comm _ (g i), add_comm _ (g j), add_assoc]; rfl
    have h_f_sumeqone : ∑ i, f i = 1 := by
      have hrest : ∑ k ∈ (Finset.univ.erase i).erase j, f k = 0 := by
        apply sum_eq_zero; intro k hk; simp at hk; simp [f, hk]
      rewrite [h_f_sum f, hrest]; simp [f, ← mul_two]
    have := hx f h_f_nonneg h_f_sumeqone
    have h_l : ∑ i, a i * f i = 1 / 2 * (a i + a j) := by
      have hrest : ∑ k ∈ (Finset.univ.erase i).erase j, a k * f k = 0 := by
        apply sum_eq_zero; intro k hk; simp at hk; simp [f, hk]
      rewrite [h_f_sum (fun k ↦ a k * f k), hrest]; simp [f]
      rewrite [← add_mul, mul_comm]; rfl
    rewrite [h_l] at this
    have h_r : ∑ i, a i * f i ^ 2 = 1 / 2 * (a i + a j) * 1 / 2 := by
      have hrest : ∑ k ∈ (Finset.univ.erase i).erase j, a k * f k ^ 2 = 0 := by
        apply sum_eq_zero; intro k hk; simp at hk; simp [f, hk]
      rewrite [h_f_sum (fun k ↦ a k * f k ^ 2), hrest]; simp [f]
      rw [← add_mul, div_eq_mul_inv, sq, mul_inv, mul_comm 2⁻¹ (_ + _), mul_assoc]
    rewrite [h_r] at this
    simpa using this
  case mp =>
    induction n with
    | zero =>
      simp; intro h _ x hx1 hx2 hx;
      refine sub_nonneg.mp ?_
      rewrite [add_sub_add_comm]; simp only [sq, ← mul_assoc, ← mul_one_sub]
      rewrite [show 1 - x 0 = x 1 by rw [← hx, add_sub_cancel_left],
        show 1 - x 1 = x 0 by rw [← hx, add_sub_cancel_right],
        mul_assoc, mul_assoc, mul_comm (x 1) (x 0), ← add_mul]
      exact mul_nonneg h <| mul_nonneg hx1 hx2
    | succ m ih =>
    intro ha x hxnonneg hxone
    have h_f_sum {m : ℕ} : ∀ f : Fin m.succ → ℝ, ∑ k, f k = f ⟨m, Nat.lt_add_one m⟩
      + ∑ k ∈ Finset.univ.erase ⟨m, Nat.lt_add_one m⟩, f k := by
      intro f
      have h1 := sum_erase_add (.univ : Finset (Fin m.succ)) f
        <| mem_univ ⟨m, Nat.lt_add_one m⟩
      rewrite [← h1, add_comm _ (f ⟨m, Nat.lt_add_one m⟩)]; rfl
    rewrite [h_f_sum x] at hxone
    set xlast := x ⟨m + 2, Nat.lt_add_one (m + 2)⟩
    by_cases! hlast1 : xlast = 1
    · sorry
    have : xlast < 1 := sorry
    let x' : Fin (m + 3) → ℝ := fun k ↦ if k = m + 2 then xlast else x k / (1 - xlast)
    let x'' : Fin (m + 2) → ℝ := fun ⟨k, hk⟩ ↦ x ⟨k, Nat.lt_succ_of_lt hk⟩ / (1 - xlast)
    have hx''nonneg : ∀ k, x'' k ≥ 0 := fun ⟨k, hk⟩ ↦ by
      simp [x'']
      refine div_nonneg (hxnonneg ⟨k, Nat.lt_succ_of_lt hk⟩) ?_
      exact sub_nonneg_of_le this.le
    have hx''one : ∑ k, x'' k = 1 := sorry
    have := ih (fun ⟨k, hk⟩ ↦ a ⟨k, Nat.lt_succ_of_lt hk⟩) sorry x'' hx''nonneg hx''one
    simp [x'', div_pow, mul_div] at this
    sorry

end China1986P1
