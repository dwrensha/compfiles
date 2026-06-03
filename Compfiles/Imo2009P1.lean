/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Olympiad 2009, Problem 1

Let $n$ be a positive integer and let $a_1, a_2, \ldots, a_k$ ($k \ge 2$) be
distinct integers in the set $\{1, 2, \ldots, n\}$ such that $n$ divides
$a_i(a_{i+1} - 1)$ for $i = 1, 2, \ldots, k - 1$. Prove that $n$ does not
divide $a_k(a_1 - 1)$.
-/

namespace Imo2009P1

problem imo2009_p1 (n k : ℕ) (hn : 0 < n) (hk : 2 ≤ k)
    (a : Fin k → ℤ)
    (hmem : ∀ i, a i ∈ Finset.Icc 1 (n : ℤ))
    (hdistinct : Function.Injective a)
    (hdvd : ∀ i : Fin k, (hi : (i : ℕ) + 1 < k) →
              (n : ℤ) ∣ a i * (a ⟨(i : ℕ) + 1, hi⟩ - 1)) :
    ¬ (n : ℤ) ∣ a ⟨k - 1, by lia⟩ * (a ⟨0, by lia⟩ - 1) := by
  sorry

end Imo2009P1
