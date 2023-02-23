import Mathlib.Data.Int.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.LibrarySearch

/-!
# USA Mathematical Olympiad 1998, Problem 5

Prove that for each n ≥ 2, there is a set S of n integers such that
(a-b)² divides ab for every distinct a,b ∈ S.
-/

namespace Usa1998Q5

theorem usa1998_q5 (n : ℕ) (hn : 2 ≤ n) :
    ∃ S: Set ℤ, ∀ a b : ℤ, a ∈ S → b ∈ S → a ≠ b → (a - b)^2 ∣ a * b := by
  sorry
