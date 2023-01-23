import Mathlib.Data.Nat.Basic

/-!
# International Mathematical Olympiad 1964, Problem 1

 (a) Find all positive integers n for which 2ⁿ - 1 is divisible by 7.
 (b) Prove that there is no positive integer n for which 2ⁿ + 1 is
     divisible by 7.
-/

theorem imo_1964_q1b
    (n : ℕ) :
    ¬ 7 ∣ (2^n + 1) := by
  sorry

