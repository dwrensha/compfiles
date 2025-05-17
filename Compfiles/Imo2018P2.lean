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

lemma mod_3_satisfies {n : ℕ} (hn : 3 ∣ n) :
    ∃ a : ZMod n → ℝ, P a := sorry

lemma satisfies_is_mod_3 {n : ℕ} (h : ∃ a : ZMod n → ℝ, P a) :
    3 ∣ n := sorry

snip end

problem imo2018_p2 (n : ℕ) :
    n ∈ solution_set ↔ 3 ≤ n ∧ ∃ a : ZMod n → ℝ, P a := by
  constructor
  · rintro ⟨hn1, hn2⟩
    exact ⟨hn1, mod_3_satisfies hn2⟩
  · rintro ⟨hn1, hn2⟩
    exact ⟨hn1, satisfies_is_mod_3 hn2⟩

end Imo2018P2
