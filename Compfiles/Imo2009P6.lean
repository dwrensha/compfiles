/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Olympiad 2009, Problem 6

Let a₁, a₂, ..., aₙ be distinct positive integers and let M
be a set of n - 1 positive integers not containing
s = a₁ + a₂ + ... + aₙ. A grasshopper is to jump along the
real axis, starting at the point 0 and making n jumps to
the right with lengths a₁, a₂, ..., aₙ in some order. Prove
that the order can be chosen in such a way that the
grasshopper never lands on any point in M.
-/

namespace Imo2009P6

open scoped BigOperators

snip begin

lemma lemma1 (n : ℕ) (a : Fin n → ℤ) :
    ∃ p : Fin n → Fin n,
        p.Bijective ∧ ∀ i j, i ≤ j → a (p i) ≤ a (p j) := by
  sorry

lemma lemma2 (n : ℕ) (a : Fin n → ℤ)
    (ainj : a.Injective) :
    ∃ p : Fin n → Fin n,
        p.Bijective ∧ ∀ i j, i < j → (a ∘ p) i < (a ∘ p) j := by
  obtain ⟨p, hp1, hp2⟩ := lemma1 n a
  refine ⟨p, hp1, ?_⟩
  intro i j hij
  have h0 := ne_of_lt hij
  have h2 := hp2 i j (le_of_lt hij)
  have h3 : p i ≠ p j := fun hx ↦ h0 (hp1.1 hx)
  exact lt_of_le_of_ne h2 fun a ↦ h3 (ainj a)

-- The problem with an additional assumption that a is sorted.
theorem imo2009_p6' (n : ℕ) (hn : 0 < n)
    (a : Fin n → ℤ)
    (ainj : a.Injective)
    (apos : ∀ i, 0 < a i)
    (asorted : ∀ i j, i < j → a i < a j)
    (M : Finset ℤ)
    (Mpos : ∀ m ∈ M, 0 < m)
    (Mcard : M.card = n - 1)
    (hM : ∑ i, a i ∉ M)
    : ∃ p : Fin n → Fin n,
        p.Bijective ∧
        ∀ i : Fin n, ∑ j : Fin (i + 1), a (p ⟨j, by omega⟩) ∉ M := by
  induction' n using Nat.strongInductionOn with n ih
  let x := ∑ i : Fin (n - 1), a ⟨i, by omega⟩
  -- four cases: split on whether x ∈ M and whether
  -- there is any y > x such that y ∈ M.
  have h1 := Classical.em (x ∈ M)
  have h2 := Classical.em (∃ y, x < y ∧ y ∈ M)
  cases' h1 with h1 h1 <;> cases' h2 with h2 h2
  · sorry
  · sorry
  · -- x has no mine, and there is a mine past x.
    -- Then there are at most n − 2 mines in [0, x] and
    -- so we use induction to reach x, then leap from x to s and win
    obtain ⟨y, hy1, hy2⟩ := h2
    let M' := M.filter (fun z ↦ z ≤ x)
    have hyM' : y ∉ M' := by
      intro hy
      rw [Finset.mem_filter] at hy
      omega
    have h3 : M'.card ≤ n - 2 := by
      let M'' := Finset.cons y M' hyM'
      have h4 : M'' ⊆ M := by
        intro a ha
        rw [Finset.mem_cons] at ha
        obtain rfl | ha := ha
        · exact hy2
        · rw [Finset.mem_filter] at ha
          exact ha.1
      have h4' : M''.card ≤ M.card := Finset.card_le_card h4
      have h5 : M''.card = M'.card + 1 := Finset.card_cons hyM'
      have h6 : M'.card + 1 ≤ M.card := by omega
      omega
    obtain h7 | h7 := Nat.eq_zero_or_pos M'.card
    · refine ⟨id, Function.bijective_id, ?_⟩
      intro i
      obtain hi1 | hi2 := Classical.em (i.val < n-1)
      · let z := ∑ j : Fin (↑i + 1), a (id { val := ↑j, isLt := by omega })
        have h9 : z ≤ x := by sorry
        intro h10
        change z ∈ M at h10
        have h11 : z ∈ M' := by
          rw [Finset.mem_filter]
          exact ⟨h10, h9⟩
        rw [Finset.card_eq_zero] at h7
        have h12 := Finset.not_mem_empty z
        rw [h7] at h11
        exact h12 h11
      · have h9 : i.val + 1 = n := by omega
        have h10 : ∑ j : Fin (↑i + 1), a (id { val := ↑j, isLt := by omega })
                = ∑ i : Fin n, a i
             := (Fin.sum_congr' a h9)
        rw [h10]
        exact hM
    have := ih M'.card (by omega) h7
    sorry
  · sorry

snip end

problem imo2009_p6 (n : ℕ) (hn : 0 < n)
    (a : Fin n → ℤ)
    (ainj : a.Injective)
    (apos : ∀ i, 0 < a i)
    (M : Finset ℤ)
    (Mpos : ∀ m ∈ M, 0 < m)
    (Mcard : M.card = n - 1)
    (hM : ∑ i, a i ∉ M)
    : ∃ p : Fin n → Fin n,
        p.Bijective ∧
        ∀ i : Fin n, ∑ j : Fin (i + 1), a (p ⟨j, by omega⟩) ∉ M := by
  obtain ⟨ps, hps1, hps2⟩ := lemma2 n a ainj
  have ainj' : (a ∘ ps).Injective :=
    (Function.Injective.of_comp_iff' a hps1).mpr ainj
  have apos' : ∀ (i : Fin n), 0 < (a ∘ ps) i := by
    intro i
    exact apos (ps i)
  have hM' : ∑ i : Fin n, (a ∘ ps) i ∉ M := by
    have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
    let ps' := Fintype.bijInv hps1
    have h0 : ps'.Bijective := Fintype.bijective_bijInv hps1
    have h3 : ∀ x, ps (ps' x) = x := by
      have h5 := Fintype.rightInverse_bijInv hps1
      intro x
      exact ainj (congrArg a (ainj (congrArg a (h5 x))))
    have h3' : ∀ x, a (ps (ps' x)) = a x := by
      intro x
      exact congrArg a (ainj (congrArg a (h3 x)))
    have h1 : Finset.map ⟨ps', h0.1⟩ Finset.univ = Finset.univ := by simp
    rw [←h1]
    rw [Finset.sum_map, Function.Embedding.coeFn_mk]
    simp_rw [Function.comp_apply]
    rw [Fintype.sum_congr _ _ h3']
    exact hM
  obtain ⟨p', hp1, hp2⟩ :=
    imo2009_p6' n hn (a ∘ ps) ainj' apos' hps2 M Mpos Mcard hM'
  exact ⟨ps ∘ p', Function.Bijective.comp hps1 hp1, hp2⟩
