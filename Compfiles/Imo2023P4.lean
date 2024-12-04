/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 2023, Problem 4

Let x₁, x₂, ... x₂₀₂₃ be distinct positive real numbers.
Define

   aₙ := √((x₁ + x₂ + ... + xₙ)(1/x₁ + 1/x₂ + ... + 1/xₙ)).

Suppose that aₙ is an integer for all n ∈ {1,...,2023}.
Prove that 3034 ≤ a₂₀₂₃.
-/

namespace Imo2023P4

noncomputable def a (x : Finset.Icc 1 2023 → ℝ) (n : Finset.Icc 1 2023) : ℝ :=
  √((∑ i ∈ Finset.univ.filter (· ≤ n), x i) *
    (∑ i ∈ Finset.univ.filter (· ≤ n), (1 / x i)))

snip begin

noncomputable def aa (m : ℕ)
    (x : Finset.Icc 1 (2 * m + 1) → ℝ) (n : Finset.Icc 1 (2 * m + 1)) : ℝ :=
  √((∑ i ∈ Finset.univ.filter (· ≤ n), x i) *
    (∑ i ∈ Finset.univ.filter (· ≤ n), (1 / x i)))

theorem imo2023_p4_generalized
    (m : ℕ)
    (x : Finset.Icc 1 (2 * m + 1) → ℝ)
    (hxp : ∀ i, 0 < x i)
    (hxi : x.Injective)
    (hxa : ∀ i : Finset.Icc 1 (2 * m + 1), ∃ k : ℤ, aa m x i = k)
    : 3 * m + 1 ≤ aa m x ⟨2 * m + 1, by simp⟩ := by
  -- We follow the "induct-by-two" solution from
  -- https://web.evanchen.cc/exams/IMO-2023-notes.pdf
  induction m with
  | zero =>
    simp only [CharP.cast_eq_zero, mul_zero, zero_add, aa, Nat.mul_zero, Nat.reduceAdd,
               one_div, Real.one_le_sqrt]
    have h1 : Finset.filter (fun x ↦ x ≤ ⟨1, by simp⟩)
                            (Finset.univ (α := {x //x ∈ Finset.Icc 1 1}))
           = Finset.univ (α := {x // x ∈ Finset.Icc 1 1}) := by
      refine Finset.filter_true_of_mem ?h
      intro x hx
      obtain ⟨x, hx1⟩ := x
      rw [Finset.mem_Icc] at hx1
      obtain ⟨hx2, hx3⟩ := hx1
      simp only [Nat.mul_zero, Nat.reduceAdd, Subtype.mk_le_mk]
      exact hx3
    rw [h1]
    have h2 : Finset.univ (α := { x // x ∈ Finset.Icc 1 1 }) = { ⟨1, by simp⟩ } := by decide
    simp only [h2, Finset.sum_singleton, ge_iff_le]
    simp only [Nat.mul_zero, Nat.reduceAdd, Subtype.forall, Finset.Icc_self,
               Finset.mem_singleton] at hxp
    specialize hxp 1 (by simp)
    field_simp
  | succ m ih =>
    sorry

snip end

problem imo2023_p4
    (x : Finset.Icc 1 2023 → ℝ)
    (hxp : ∀ i, 0 < x i)
    (hxi : x.Injective)
    (hxa : ∀ i : Finset.Icc 1 2023, ∃ k : ℤ, a x i = k)
    : 3034 ≤ a x ⟨2023, by simp⟩ := by
  have := imo2023_p4_generalized 1011 x hxp hxi hxa
  convert this
  norm_num

end Imo2023P4
