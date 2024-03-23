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
        have h6 := hf1 i hi
        have h7 : {j | ↑(f' j) = i} = {j | ↑(f j) = i} ∪ {j | ↑(f j) = n + i} := by
           ext a
           constructor
           · intro ha
             dsimp [f'] at ha
             split_ifs at ha with h20
             · left
               exact ha
             · dsimp at ha
               right
               dsimp
               omega
           · intro ha
             dsimp [f']
             obtain ha' | ha' := ha
             · rw [Set.mem_setOf] at ha'
               rw [←ha'] at hi
               simpa [hi]
             · rw [Set.mem_setOf] at ha'
               have h8 : ¬ ↑(f a) < n := by omega
               simp [h8]
               omega
        have h8 : Disjoint {j | ↑(f j) = i} {j | ↑(f j) = n + i} := by
          rw [Set.disjoint_left]
          intro a ha ha'
          rw [Set.mem_setOf] at ha ha'
          omega
        have h9 : Set.ncard {j | ↑(f' j) = i} =
                  Set.ncard {j | ↑(f j) = i} + Set.ncard {j | ↑(f j) = n + i} := by
           rw [h7]
           exact Set.ncard_union_eq h8
        rw [Set.Nat.card_coe_set_eq, h9]
        rw [Set.Nat.card_coe_set_eq] at h6
        have h10 := hf2 (n + i) (by omega) (by omega)
        rw [Set.Nat.card_coe_set_eq] at h10
        exact Odd.add_even h6 h10
      · intro i hi1 _
        have h6 : ∀ j, ↑(f' j) ≠ i := by
          intro j
          dsimp [f']
          split_ifs with h10
          · omega
          · dsimp; omega
        use 0
        dsimp
        rw [Nat.card_eq_fintype_card, Fintype.card_eq_zero_iff, isEmpty_subtype]
        exact h6
      · intro i hi j
        unfold_let f'
        dsimp
        split_ifs with h3
        · omega
        · intro h4
          apply_fun (·.val) at h4
          dsimp only at h4
          omega
    ⟨f', mf'⟩

lemma claim (n k : ℕ) (hnk : n ≤ k) (he : Even (k - n))
    (f : {b : Sequence n k // MSequence n k b }) :
    Set.ncard {g | ψ n k g = f} = 2^(k - n) := by
  sorry

lemma lemma1 (α : Type) (A B : Set α) (hA : A.Finite) (hB : B.Finite)
    (f : {x // A x} → {x // B x})
    (n : Nat) (h1 : ∀ b, Set.ncard { a | f a = b } = n)
    : B.ncard * n = A.ncard := by
  classical
  haveI hfa : Fintype ↑A := Set.Finite.fintype hA
  haveI hfb : Fintype ↑B := Set.Finite.fintype hB
  have hbf : ∀ b,  Fintype { a // f a = b } := by
    intro b
    have : Fintype { x // A x } := hfa
    exact setFintype fun x ↦ f x = b
  have h2 : ∀ b, Set.ncard { a | f a = b } = Fintype.card { a // f a = b} := by
    intro b
    rw [Set.setOf_set, Fintype.card_eq_nat_card, ←Set.Nat.card_coe_set_eq]
    rfl

  have h3' : ∀ b ∈ Finset.univ (α := ↑B), (Finset.filter {a | f a = b } (Finset.univ (α := ↑A))).card = n := by
    intro b _
    rw [← @Fintype.card_subtype]
    rw [← h1
        b, h2,
        Set.setOf_set, Fintype.card_eq_nat_card,
        Mathlib.Tactic.Zify.nat_cast_eq, Fintype.card_eq_nat_card]

  clear h1 h2
  let A' := Finset.biUnion
             (Finset.univ (α := ↑B))
             (fun b ↦ Finset.filter { a | f a = b } (Finset.univ (α := ↑A)))
  have h4 :
    ∀ b1 ∈ (Finset.univ (α := ↑B)),
      ∀ b2 ∈ (Finset.univ (α := ↑B)),
        b1 ≠ b2 →
          Disjoint
            (Finset.filter { a | f a = b1 } (Finset.univ (α := ↑A)))
            (Finset.filter { a | f a = b2 } (Finset.univ (α := ↑A))) := by
    intro b1 _ b2 _ hb12
    rw [Finset.disjoint_filter]
    intro x _ hx2 hx3
    rw [Set.setOf_app_iff] at hx2 hx3
    rw [hx2] at hx3
    exact hb12 hx3
  have h5 : A'.card = Set.ncard B * n := by
    rw [Finset.card_biUnion h4]
    rw [Finset.sum_congr rfl h3']
    simp only [Finset.sum_const, smul_eq_mul]
    have : (Finset.univ (α := ↑B)).card = Set.ncard B := by
      rw [Finset.card_univ, Fintype.card_eq_nat_card, Set.Nat.card_coe_set_eq]
    exact congrFun (congrArg HMul.hMul this) n
  rw [←h5]
  have h6 : A' = Finset.univ (α := ↑A) := by
    ext a
    constructor
    · intro _
      exact @Finset.mem_univ _ hfa a
    · intro _
      rw [Finset.mem_biUnion]
      use f a
      refine ⟨Finset.mem_univ _, ?_⟩
      · simp; rfl
  rw[h6]
  rw [@Finset.card_univ, ←Set.Nat.card_coe_set_eq, Fintype.card_eq_nat_card]
  rfl

snip end

determine solution (n k : ℕ) : ℚ := 2 ^ (k - n)

problem imo2008_p5 (n k : ℕ)
    (hn : 0 < n) (hk : 0 < k)
    (hnk : n ≤ k) (he : Even (k - n))
    : Set.ncard (MSequence n k) * solution n k = Set.ncard (NSequence n k) := by
  clear hn hk -- don't need these
  have hA : Set.Finite { f | NSequence n k f } := Set.toFinite _
  have hB : Set.Finite { f | MSequence n k f } := Set.toFinite _
  have h1 := lemma1 (Sequence n k) (NSequence n k) (MSequence n k) hA hB (ψ n k)
              (2 ^ (k - n))
              (claim n k hnk he)
  rw [←h1]
  push_cast
  rfl
