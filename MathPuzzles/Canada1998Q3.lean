import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Real.Basic

/-
Canadian Mathematical Olympiad 1998, Problem 3

Let n be a natural number such that n ≥ 2. Show that

  (1/(n + 1))(1 + 1/3 + ... + 1/(2n - 1)) > (1/n)(1/2 + 1/4 + ... + 1/2n).
-/

open BigOperators

theorem canada1998_q3 (n : ℕ) (hn : 2 ≤ n) :
    (1/((n:ℝ) + 1)) * ∑ i in Finset.range n, (1/(2 * (i:ℝ) + 1)) >
    (1/(n:ℝ)) * ∑ i in Finset.range n, (1/(2 * (i:ℝ) + 2)) := by
  sorry
