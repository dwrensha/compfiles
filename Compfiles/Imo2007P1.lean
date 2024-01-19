/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
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

theorem pos_fin_nonempty {n : ℕ} (hn : 0 < n) : (@Finset.univ (Fin n) _).Nonempty := by
  rwa [Finset.univ_nonempty_iff, ←Fin.pos_iff_nonempty]

problem imo2007_p1a {n : ℕ} (hn : 0 < n) {a x : Fin n → ℝ} (h : Monotone x) :
    ∀ {k m : Fin n}, k ≤ m → m ≤ n →
      (a k - a m) / 2 ≤ (@Finset.univ (Fin n) _).sup' (pos_fin_nonempty hn)
                           (fun i ↦ |x i - a i|) := by
  sorry

problem imo2007_p1b {n : ℕ} (hn : 0 < n) {a : Fin n → ℝ} :
    ∃ x : Fin n → ℝ, Monotone x ∧ ∃ k m : Fin n, k ≤ m ∧ m ≤ n ∧
            (a k - a m) / 2 = (@Finset.univ (Fin n) _).sup' (pos_fin_nonempty hn)
                           (fun i ↦ |x i - a i|) := by
  sorry
