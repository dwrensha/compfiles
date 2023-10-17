/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import Compfiles.Meta.ProblemExtraction

problem_file

/-!
# USA Mathematical Olympiad 2022, Problem 4

Determine all pairs of primes (p, q) where p - q and pq - q are both perfect squares.
-/

namespace Usa2022P4

determine solution_set : Set (ℕ × ℕ) := sorry

problem usa2022_p4 (p q : ℕ) :
    (p, q) ∈ solution_set ↔
    p.Prime ∧ q.Prime ∧
    ∃ a, a^2 + q = p ∧ ∃ b, b^2 + q = p * q := by
  -- Informal proof outline taken from https://web.evanchen.cc/exams/USAMO-2022-notes.pdf

  -- Note that 0 < p and 0 < q because they are prime.

  -- Note that we then have 0 < a < p, and 0 < b < p (because q ≤ p).

  -- Subtracting our equations gives (b - a)(b + a) = b² - a² = p(q - 1),

  -- Since b - a < p and p is prime, we have that p divides b + a.
  -- Since and b + a < 2p, we have that a + b must in fact equal p.

  -- Hence q - 1 = b - a.

  -- Note that b - a and b + a have the same parity.
  -- Therefore p and q - 1 have the same parity.
  -- If they are both even, then q > p, contradiction.
  -- Therefore, they are both odd, and q = 2.

  -- Moreover, p ≡ 0 mod 3, so (3,2) is the only possibility.
  sorry
