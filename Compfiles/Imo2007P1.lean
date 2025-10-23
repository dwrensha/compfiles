/-
Copyright (c) 2023 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benpigchu
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 2007, Problem 1

Real numbers a₁, a₂, ..., aₙ are fixed. For each 1 ≤ i ≤ n,
we let dᵢ = max {aⱼ : 1 ≤ j ≤ i} - min {aⱼ : i ≤ j ≤ n},
and let d = max {dᵢ : 1 ≤ i ≤ n}.

(a) Prove that for any real numbers x₁ ≤ ... ≤ xₙ, we have
   max { |xᵢ - aᵢ| : 1 ≤ i ≤ n } ≥ d / 2.

(b) Show that there exists some choice of x₁ ≤ ... ≤ xₙ which achieves equality.
-/

namespace Imo2007P1

noncomputable abbrev d {n : ℕ} (a : Fin n → ℝ) (i : Fin n) :=
  (⨆ j : {j // j ≤ i}, a j) - (⨅ j : {j // i ≤ j}, a j)

problem imo2007_p1a {n : ℕ} (hn : 0 < n) (a x : Fin n → ℝ) (h : Monotone x) :
    (⨆ i, d a i) / 2 ≤ ⨆ i, |x i - a i| := by
  have h₁ : ∃ i : Fin n, d a i = ⨆ i, d a i:= by
    haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
    apply exists_eq_ciSup_of_finite
  rcases h₁ with ⟨i, hi⟩
  rw [←hi, d]
  have h₂ : ∃ j : {j // j ≤ i}, a j = ⨆ j : {j // j ≤ i}, a j:= by
    haveI : Nonempty {j // j ≤ i} := by
      rw [nonempty_subtype]
      use i
    apply exists_eq_ciSup_of_finite
  have h₃ : ∃ k : {k // i ≤ k}, a k = ⨅ k : {k // i ≤ k}, a k := by
    apply exists_eq_ciInf_of_finite
  rcases h₂ with ⟨j, hj⟩
  rcases h₃ with ⟨k, hk⟩
  rw [← hj, ← hk]
  apply le_of_not_gt
  intro h'
  have h₄ : ∀ i : Fin n, |x i - a i| < (a ↑j - a ↑k) / 2 := by
    intro i
    calc |x i - a i|
        ≤ ⨆ i, |x i - a i| := Finite.le_ciSup (fun i ↦ |x i - a i|) i
      _ < (a ↑j - a ↑k) / 2 := h'
  have h₅ : a ↑j - a ↑k < a ↑j - a ↑k := by
    calc a ↑j - a ↑k
      ≤ (a ↑j - a ↑k) + (x ↑k - x ↑j) := by
          apply le_add_of_nonneg_right
          apply sub_nonneg_of_le
          apply h
          exact le_trans j.prop k.prop
      _ = (a ↑j - x ↑j) + (x ↑k - a ↑k):= by module
      _ ≤ |a ↑j - x ↑j| + |x ↑k - a ↑k| := add_le_add (le_abs_self _) (le_abs_self _)
      _ = |x ↑j - a ↑j| + |x ↑k - a ↑k| := by rw [abs_sub_comm]
      _ < (a ↑j - a ↑k) / 2 + (a ↑j - a ↑k) / 2 := add_lt_add (h₄ j) (h₄ k)
      _ = a ↑j - a ↑k := add_halves _
  exact (lt_self_iff_false _).mp h₅

problem imo2007_p1b {n : ℕ} (hn : 0 < n) {a : Fin n → ℝ} :
    ∃ x : Fin n → ℝ, Monotone x ∧
      (⨆ i, d a i) / 2 = ⨆ i, |x i - a i| := by
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  set d' := (⨆ i, d a i) / 2
  set x := fun (i: Fin n) ↦ (⨆ j : {j // j ≤ i}, a j) - d'
  use x
  have h : Monotone x := by
    intro i j i_le_j
    apply sub_le_sub_right
    haveI : Nonempty {j // j ≤ i} := by
      rw [nonempty_subtype]
      use i
    rw [ciSup_le_iff (Finite.bddAbove_range fun (j : { j // j ≤ i }) ↦ a j)]
    intro i'
    exact Finite.le_ciSup (fun (j' : { j' // j' ≤ j }) ↦ a j') ⟨i', le_trans i'.prop i_le_j⟩
  constructor
  · exact h
  · apply le_antisymm
    · exact imo2007_p1a hn a x h
    · rw [ciSup_le_iff (Finite.bddAbove_range fun i ↦ |x i - a i|)]
      intro i
      rw [abs_le']
      constructor
      · have h': x i - a i = ((⨆ j : {j // j ≤ i}, a j) - a i) - d' := by module
        rw [h', sub_le_iff_le_add, ← mul_two]
        calc (⨆ j : {j // j ≤ i}, a j) - a i
            ≤ (⨆ j : {j // j ≤ i}, a j) - (⨅ j : {j // i ≤ j}, a j) := by
              apply sub_le_sub_left
              exact Finite.ciInf_le (fun (j : { j // i ≤ j }) ↦ a j) ⟨i, le_rfl⟩
          _ ≤ ⨆ i, d a i := Finite.le_ciSup (fun i ↦ d a i) i
          _ = d' * 2 := (div_mul_cancel_of_invertible _ _).symm
      · calc -(x i - a i)
            = d' + (a i - (⨆ j : {j // j ≤ i}, a j)) := by module
          _ ≤ d' := by
              apply add_le_of_nonpos_right
              apply sub_nonpos_of_le
              haveI : Nonempty {j // j ≤ i} := by
                rw [nonempty_subtype]
                use i
              exact Finite.le_ciSup (fun (j : { j // j ≤ i }) ↦ a j) ⟨i, le_rfl⟩


end Imo2007P1
