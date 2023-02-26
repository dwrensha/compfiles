import Mathlib.Data.Int.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.LibrarySearch

/-!
# USA Mathematical Olympiad 1998, Problem 5

Prove that for each n ≥ 2, there is a set S of n integers such that
(a-b)² divides ab for every distinct a,b ∈ S.
-/

namespace Usa1998Q5

theorem usa1998_q5 (n : ℕ) (hn : 2 ≤ n) :
    ∃ S : Finset ℤ,
       S.card = n ∧
       ∀ a ∈ S, ∀ b ∈ S, a ≠ b → (a - b)^2 ∣ a * b := by
  -- (Informal proof from Andreescu & Feng.)
  -- We will prove by induction on n that we can find such a set Sₙ all
  -- of whose elements are nonnegative.
  -- For n = 2, we may take S₂ = {0,1}
  -- Now suppose that for some n ≥ 2, the desired set Sₙ of n nonegative
  -- integers exists. Let L be the least common multiple of those numbers
  -- (a-b)² and ab that are nonzero, with (a,b) ranging over pairs of
  -- distinct elements from Sₙ. Define
  --   Sₙ₊₁ = { L + a : a ∈ Sₙ } ∪ { 0 }.
  -- Then Sₙ₊₁ consists of n + 1 nonnegative integers, since L > 0.
  -- If α,β ∈ Sₙ₊₁ and either α or β is zero, then (α - β)² divides α\B.
  -- If L + a, L + b ∈ Sₙ₊₁, with a,b distinct elements of Sₙ, then
  --   (L + a)(L + b) ≡ ab ≡ 0 (mod (a - b)²),
  -- so [(L + a) - (L + b)]² divides (L + a)(L + b), completing the inductive
  -- step.
  sorry
