import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.LibrarySearch

/-!
# International Mathematical Olympiad 1987, Problem 4

Prove that there is no function f : ℕ → ℕ such that f(f(n)) = n + 1987
for every n.
-/

theorem imo1987_q4 : (¬∃ f : ℕ → ℕ, ∀ n, f (f n) = n + 1987) := by
  -- Informal solution by Sawa Pavlov, listed at
  -- https://artofproblemsolving.com/wiki/index.php/1987_IMO_Problems/Problem_4

  -- Note that f is injective, because if f(n) = f(m),
  -- then f(f(n)) = f(f(m)), so m = n.

  -- Let A := ℕ - f(ℕ) and B := f(A).

  -- We claim that B = f(ℕ) - f(f(ℕ)).
  -- Obviously B is a subset of f(ℕ) and if k belongs to B, then it does not
  -- belong to f(f(ℕ)) since f is injective. Similarly, a member of f(f(ℕ))
  -- cannot belong to B.

  -- A and B are disjoint and have union ℕ - f(f(ℕ)), which is
  -- {0, 1, 2, ... , 1986}. But since f is injective they have the
  -- same number of elements, which is impossible since {0, 1, ... , 1986}
  -- has an odd number of elements.

  sorry
