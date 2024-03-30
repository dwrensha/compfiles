/-
Copyright (c) 2023 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
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
  (⨆ j : {j // j ≤ i}, a j - ⨅ j : {j // i ≤ j}, a j)

problem imo2007_p1a {n : ℕ} (hn : 0 < n) {a x : Fin n → ℝ} (h : Monotone x) :
    (⨆ i, d a i) / 2 ≤ ⨆ i, |x i - a i| := by
  sorry

problem imo2007_p1b {n : ℕ} (hn : 0 < n) {a : Fin n → ℝ} :
    ∃ x : Fin n → ℝ, Monotone x ∧
      (⨆ i, d a i) / 2 = ⨆ i, |x i - a i| := by
  sorry
