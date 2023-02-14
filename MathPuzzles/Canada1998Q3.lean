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
  -- We prove
  -- n(1 + 1/3 + ... + 1/(2n - 1)) > (n + 1)(1/2 + 1/4 + ... + 1/2n)
  -- by induction.
  -- Base case: when n = 2, we have 8/3 > 9/4.
  -- Inductive case: suppose claim is true for k ≥ 2. Then we have
  -- k (1 + 1/3 + ... 1/(2k - 1)) > (k + 1)(1/2 + 1/4 + ... + 1/2k).
  -- Now let n = k + 1.
  -- Note that
  --  (1 + 1/3 + ... + 1/(2k-1)) + (k+1)/(2k+1)
  --    = (1/2 + 1/3 + ... + 1/(2k-1)) + 1/2 + (k+1)/(2k+1)
  --    > (1/2 + 1/4 + ... + 1/2k) + 1/2 + (k+1)/(2k+1)
  --    > (1/2 + 1/4 + ... + 1/2k) + (k + 1)/(2k + 2) + 1/(2k+1)
  --    > (1/2 + 1/4 + ... + 1/2k) + (k + 2)/(2k + 2).
  --
  -- Then we are done because
  -- (k + 1)(1 + 1/3 + ... + 1/(2k - 1) + 1/(2k + 1))
  --  = k (1 + 1/3 + ... + 1/(2k - 1))
  --     + (1 + 1/3 + ... + 1/(2k - 1)) + (k + 1)/(2k + 1)
  --  > k(1 + 1/3 + ... + 1/(2k - 1))
  --     + (1 + 1/2 + ... + 1/2k)) + (k + 2)/(2k + 1)
  --  > (k + 2)(1/2 + 1/4 + ... + 1/(2k + 2)).

  sorry
