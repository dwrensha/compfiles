/-
Copyright (c) 2024 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic
import Mathlib.Data.Set.Card

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Olympiad 2008, Problem 5

Let n and k be positive integers with k ≥ n and k - n an even number.
There are 2n lamps labelled 1, 2, ..., 2n each of which can be
either on or off. Initially all the lamps are off. We consider
sequences of steps: at each step one of the lamps is switched (from
on to off or from off to on). Let N be the number of such sequences
consisting of k steps and resulting in the state where lamps 1 through
n are all on, and lamps n + 1 through 2n are all off. Let M be the
number of such sequences consisting of k steps, resulting in the state
where lamps 1 through n are all on, and lamps n + 1 through 2n are all off,
but where none of the lamps n + 1 through 2n is ever switched on.

Determine N/M.
-/

namespace Imo2008P5

abbrev Sequence (n k : ℕ) := Fin k → Fin (2 * n)

abbrev NSequence (n k : ℕ) (f : Sequence n k) : Prop :=
  (∀ i < n, Odd (Nat.card { j | f j = i })) ∧
  (∀ i, n ≤ i → i < 2 * n → Even (Nat.card { j | f j = i }))

abbrev MSequence (n k : ℕ) (f : Sequence n k) : Prop :=
  NSequence n k f ∧
  (∀ i : Fin (2 * n), n ≤ i → ∀ j : Fin k, f j ≠ i)

snip begin

-- We follow the informal solution from
-- https://web.evanchen.cc/exams/IMO-2008-notes.pdf

def ψ (n k : ℕ) : { f // NSequence n k f } → { f // MSequence n k f } :=
  fun ⟨f, hf1, hf2⟩ ↦
    let f' := fun ii : Fin k ↦
         if hfi : f ii < n then f ii else ⟨f ii - n, by omega⟩
    have mf' : MSequence n k f' := by
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro i hi
        have := hf1 i hi
        unfold_let f'
        sorry
      · sorry
      · sorry
    ⟨f', mf'⟩

lemma ψ_surjective (n k : ℕ) (hnk : n ≤ k) (he : Even (n - k))
    : (ψ n k).Surjective := by
  sorry

lemma claim (n k : ℕ) (hnk : n ≤ k) (he : Even (n - k))
    (f : {b : Sequence n k // MSequence n k b }) :
    Set.ncard {g | ψ n k g = f} = 2^(k - n) := by
  sorry

lemma lemma1 (α : Type) (A B : Set α) (hA : A.Finite) (hB : B.Finite)
    (f : {x // A x} → {x // B x})
    (hs : f.Surjective) (n : Nat) (h1 : ∀ b, Set.ncard { a | f a = b } = n)
    : B.ncard * n = A.ncard := by
  haveI hfa : Fintype ↑A := Set.Finite.fintype hA
  haveI hfb : Fintype ↑B := Set.Finite.fintype hB
  rw [Set.ncard_eq_toFinset_card' A, Set.ncard_eq_toFinset_card' B]
  have hbf : ∀ b,  Fintype { a // f a = b } := by
    intro b
    have : Fintype { x // A x } := hfa
    classical
    exact setFintype fun x ↦ f x = b
  have h2 : ∀ b, Set.ncard { a | f a = b } = Fintype.card { a // f a = b} := by
    intro b
    rw [Set.setOf_set, Fintype.card_eq_nat_card, ←Set.Nat.card_coe_set_eq]
    rfl
  have h3 : ∀ b, Fintype.card { a // f a = b} = n := by
    intro b
    exact (h2 b).symm.trans (h1 b)

  rw [Set.toFinset_card, Set.toFinset_card]
  sorry

snip end

determine solution (n k : ℕ) : ℚ := 2 ^ (k - n)

problem imo2008_p5 (n k : ℕ)
    (hn : 0 < n) (hk : 0 < k)
    (hnk : n ≤ k) (he : Even (n - k))
    : solution n k =
      (Set.ncard (NSequence n k) : ℚ) / Set.ncard (MSequence n k) := by
  have hA : Set.Finite { f | NSequence n k f } := Set.toFinite _
  have hB : Set.Finite { f | MSequence n k f } := Set.toFinite _
  have h1 := lemma1 (Sequence n k) (NSequence n k) (MSequence n k) hA hB (ψ n k)
              (ψ_surjective n k hnk he)
              (2 ^ (k - n))
              (claim n k hnk he)
  rw [←h1]
  have h2 : ((Set.ncard (MSequence n k)) : ℚ) ≠ 0 := by
    norm_cast
    sorry
  push_cast
  exact (mul_div_cancel_left (2 ^ (k - n)) h2).symm
