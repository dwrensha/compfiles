import Aesop
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Ring

/-!
# International Mathematical Olympiad 1989, Problem 5

Prove that for each positive integer n there exist n consecutive positive
integers, none of which is an integral power of a prime number.
-/

namespace Imo1989Q5

theorem imo1989_q5 (n : ℕ) :
    ∃ m : ℕ, m > 0 ∧ ∀ j, j < n → ¬ ∃ p k, p.Prime ∧ m + j = p ^ k := by
  sorry
