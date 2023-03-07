import Aesop
import Mathlib.Data.Nat.Prime
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
  -- (informal solution from https://artofproblemsolving.com)
  -- Let p₁,p₂,...pₙ,q₁,q₂,...,qₙ be distinct primes.
  -- By Chinese Remainder theorem, there exists x such that
  --   x ≡ -1 mod p₁q₁
  --   x ≡ -2 mod p₂q₂
  --   ...
  --   x ≡ -n mod pₙqₙ
  -- The n consecutive numbers x+1, x+2, ..., x+n each have at least
  -- two prime factors, so none of them can be expressed as an integral
  -- power of a prime.
  sorry
