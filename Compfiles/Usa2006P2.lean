/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Data.Int.Star
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Zify
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 2006, Problem 2

For a given positive integer k find, in terms of k, the minimum value
of N for which there is a set of 2k + 1 distinct positive integers
that has sum greater than N but every subset of size k has sum at
most N / 2.
-/

namespace Usa2006P2

determine solution : ℕ → ℕ := fun k ↦ 2 * k ^ 3 + 3 * k ^ 2 + 3 * k

snip begin

-- Following https://web.evanchen.cc/exams/USAMO-2006-notes.pdf

/-- Lower bound for the sum of a finset of natural numbers bounded below:
if every element of `J` is at least `a`, then the sum of `J` is at least the
sum of the `J.card` smallest allowed values `a, a+1, ...`.
Equivalently `2 * ∑ j ∈ J, j ≥ J.card * (2 * a + (J.card - 1))`; we use this
formulation to avoid truncated subtraction. -/
lemma two_mul_sum_ge (J : Finset ℕ) (a : ℕ) (hJ : ∀ j ∈ J, a ≤ j) :
    J.card * (2 * a) + J.card ^ 2 ≤ 2 * ∑ j ∈ J, j + J.card := by
  induction J using Finset.strongInductionOn with
  | _ J ih =>
    by_cases hne : J.Nonempty
    · set M := J.max' hne with hMdef
      have hMmem : M ∈ J := J.max'_mem hne
      have ih' := ih (J.erase M) (Finset.erase_ssubset hMmem)
        (fun j hj ↦ hJ j (Finset.mem_of_mem_erase hj))
      have hcard : (J.erase M).card + 1 = J.card := J.card_erase_add_one hMmem
      have hsum : M + ∑ j ∈ J.erase M, j = ∑ j ∈ J, j :=
        J.add_sum_erase (fun x => x) hMmem
      have hcardle : (J.erase M).card ≤ (Finset.Ico a M).card := by
        apply Finset.card_le_card
        intro j hj
        rw [Finset.mem_erase] at hj
        have hj3 : j ≤ M := J.le_max' j hj.2
        rw [Finset.mem_Ico]
        exact ⟨hJ j hj.2, by omega⟩
      rw [Nat.card_Ico] at hcardle
      have haM : a ≤ M := hJ M hMmem
      have h2M : 2 * (J.erase M).card + 2 * a ≤ 2 * M := by omega
      rw [← hcard, ← hsum]
      linarith [ih', h2M]
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
      simp

/-- Upper bound for the sum of a finset of natural numbers bounded above:
if every element of `J` is at most `b`, then the sum of `J` is at most the
sum of the `J.card` largest allowed values `b, b-1, ...`.
Equivalently `2 * ∑ j ∈ J, j ≤ J.card * (2 * b + 1 - J.card)`; we use this
formulation to avoid truncated subtraction. -/
lemma two_mul_sum_le (J : Finset ℕ) (b : ℕ) (hJ : ∀ j ∈ J, j ≤ b) :
    2 * ∑ j ∈ J, j + J.card ^ 2 ≤ 2 * (J.card * b) + J.card := by
  induction J using Finset.strongInductionOn with
  | _ J ih =>
    by_cases hne : J.Nonempty
    · set m₀ := J.min' hne with hm₀def
      have hm₀mem : m₀ ∈ J := J.min'_mem hne
      have ih' := ih (J.erase m₀) (Finset.erase_ssubset hm₀mem)
        (fun j hj ↦ hJ j (Finset.mem_of_mem_erase hj))
      have hcard : (J.erase m₀).card + 1 = J.card := J.card_erase_add_one hm₀mem
      have hsum : m₀ + ∑ j ∈ J.erase m₀, j = ∑ j ∈ J, j :=
        J.add_sum_erase (fun x => x) hm₀mem
      have hcardle : (J.erase m₀).card ≤ (Finset.Ioc m₀ b).card := by
        apply Finset.card_le_card
        intro j hj
        rw [Finset.mem_erase] at hj
        have hj3 : m₀ ≤ j := J.min'_le j hj.2
        rw [Finset.mem_Ioc]
        exact ⟨by omega, hJ j hj.2⟩
      rw [Nat.card_Ioc] at hcardle
      have hm₀b : m₀ ≤ b := hJ m₀ hm₀mem
      have h2m : 2 * m₀ + 2 * (J.erase m₀).card ≤ 2 * b := by omega
      rw [← hcard, ← hsum]
      linarith [ih', h2m]
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
      simp

/-- Twice the sum `1 + 2 + ... + n`. -/
lemma two_mul_sum_Icc_one (n : ℕ) :
    2 * ∑ i ∈ Finset.Icc 1 n, i = n * (n + 1) := by
  induction n with
  | zero =>
    rw [Finset.Icc_eq_empty (by omega : ¬ (1 : ℕ) ≤ 0), Finset.sum_empty]
    rfl
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega : (1 : ℕ) ≤ n + 1)]
    linear_combination ih

snip end

-- We formalise "every subset of size k has sum at most N / 2" as
-- `2 * ∑ x ∈ t, x ≤ N`, which is equivalent for natural numbers.
problem usa2006_p2 (k : ℕ) (hk : 0 < k) :
    IsLeast {N : ℕ | ∃ s : Finset ℕ, s.card = 2 * k + 1 ∧ (∀ x ∈ s, 0 < x) ∧
        N < ∑ x ∈ s, x ∧ ∀ t ⊆ s, t.card = k → 2 * ∑ x ∈ t, x ≤ N}
      (solution k) := by
  show IsLeast _ (2 * k ^ 3 + 3 * k ^ 2 + 3 * k)
  refine ⟨?_, fun N hN ↦ ?_⟩
  · -- The construction: the set {k² + 1, k² + 2, ..., k² + 2k + 1}.
    refine ⟨(Finset.Icc 1 (2 * k + 1)).image (· + k ^ 2), ?_, ?_, ?_, ?_⟩
    · -- it has `2 * k + 1` elements
      rw [Finset.card_image_of_injOn, Nat.card_Icc]
      · omega
      · intro x _ y _ h
        dsimp only at h
        omega
    · -- its elements are positive
      intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      rw [Finset.mem_Icc] at hi
      omega
    · -- its sum `(2 * k + 1) * (k ^ 2 + k + 1) = 2 * k ^ 3 + 3 * k ^ 2 + 3 * k + 1`
      -- is greater than `N`
      have hsum : ∑ x ∈ (Finset.Icc 1 (2 * k + 1)).image (· + k ^ 2), x
          = ∑ i ∈ Finset.Icc 1 (2 * k + 1), (i + k ^ 2) :=
        Finset.sum_image fun x _ y _ h ↦ by omega
      have h2 : 2 * ∑ x ∈ (Finset.Icc 1 (2 * k + 1)).image (· + k ^ 2), x
          = 2 * (2 * k ^ 3 + 3 * k ^ 2 + 3 * k + 1) := by
        rw [hsum, Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, smul_eq_mul,
          show 2 * k + 1 + 1 - 1 = 2 * k + 1 by omega]
        linear_combination two_mul_sum_Icc_one (2 * k + 1)
      omega
    · -- every subset of size `k` has sum at most `N / 2`
      intro t hts htcard
      have hlb : ∀ x ∈ t, k ^ 2 ≤ x := by
        intro x hx
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hts hx)
        rw [Finset.mem_Icc] at hi
        omega
      have hinj : Set.InjOn (· - k ^ 2) t := fun x hx y hy h ↦ by
        have h1 := hlb x hx
        have h2 := hlb y hy
        dsimp only at h
        omega
      have hcardJ : (t.image (· - k ^ 2)).card = k := by
        rw [Finset.card_image_of_injOn hinj, htcard]
      have hJb : ∀ j ∈ t.image (· - k ^ 2), j ≤ 2 * k + 1 := by
        intro j hj
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hj
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hts hx)
        rw [Finset.mem_Icc] at hi
        omega
      have h2 := two_mul_sum_le (t.image (· - k ^ 2)) (2 * k + 1) hJb
      rw [hcardJ] at h2
      have hsumJ : ∑ j ∈ t.image (· - k ^ 2), j = ∑ x ∈ t, (x - k ^ 2) :=
        Finset.sum_image hinj
      have hsumt : ∑ x ∈ t, x = ∑ x ∈ t, (x - k ^ 2) + t.card * k ^ 2 := by
        rw [← smul_eq_mul, ← Finset.sum_const, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun x hx ↦ (Nat.sub_add_cancel (hlb x hx)).symm
      rw [htcard] at hsumt
      linarith [h2, hsumJ, hsumt]
  · -- Optimality: any admissible `N` satisfies `2 * k ^ 3 + 3 * k ^ 2 + 3 * k ≤ N`.
    obtain ⟨s, hcard, _hpos, hsumgt, hsub⟩ := hN
    obtain ⟨t₀, ht₀sub, ht₀card⟩ :=
      Finset.le_card_iff_exists_subset_card.mp (show k ≤ s.card by omega)
    have hPne : (s.powersetCard k).Nonempty :=
      ⟨t₀, Finset.mem_powersetCard.mpr ⟨ht₀sub, ht₀card⟩⟩
    obtain ⟨T, hTmem, hmax⟩ :=
      Finset.exists_max_image (s.powersetCard k) (fun t ↦ ∑ x ∈ t, x) hPne
    rw [Finset.mem_powersetCard] at hTmem
    obtain ⟨hTsub, hTcard⟩ := hTmem
    have hN1 : 2 * ∑ x ∈ T, x ≤ N := hsub T hTsub hTcard
    have hTs : T ∩ s = T := by
      rw [Finset.inter_comm]
      exact Finset.inter_eq_right.mpr hTsub
    have hcardu : (s \ T).card = k + 1 := by
      rw [Finset.card_sdiff, hTs, hcard, hTcard]
      omega
    have hu₀ne : (s \ T).Nonempty := Finset.card_pos.mp (by omega)
    -- Every element of `s \ T` is at most every element of `T`:
    -- otherwise swapping increases the sum, contradicting maximality.
    have hswap : ∀ x ∈ s \ T, ∀ y ∈ T, x ≤ y := by
      intro x hx y hy
      by_contra hlt
      have hxs : x ∈ s := (Finset.mem_sdiff.mp hx).1
      have hxnT : x ∉ T := (Finset.mem_sdiff.mp hx).2
      have hxne : x ∉ T.erase y := fun h ↦ hxnT (Finset.mem_of_mem_erase h)
      have hcard₁ : (insert x (T.erase y)).card = k := by
        rw [Finset.card_insert_of_notMem hxne, Finset.card_erase_of_mem hy, hTcard]
        omega
      have hsub₁ : insert x (T.erase y) ⊆ s :=
        Finset.insert_subset hxs ((Finset.erase_subset _ _).trans hTsub)
      have hle := hmax (insert x (T.erase y)) (Finset.mem_powersetCard.mpr ⟨hsub₁, hcard₁⟩)
      rw [Finset.sum_insert hxne] at hle
      have h2 : y + ∑ z ∈ T.erase y, z = ∑ z ∈ T, z := T.add_sum_erase (fun z => z) hy
      omega
    -- The median `min' (s \ T)` is at least `k ^ 2 + 1`.
    have hMumem : (s \ T).max' hu₀ne ∈ s \ T := (s \ T).max'_mem hu₀ne
    have hTlb : ∀ y ∈ T, (s \ T).max' hu₀ne + 1 ≤ y := by
      intro y hy
      have h1 := hswap _ hMumem y hy
      have h2 : (s \ T).max' hu₀ne ∉ T := (Finset.mem_sdiff.mp hMumem).2
      have h3 : (s \ T).max' hu₀ne ≠ y := fun h ↦ h2 (h ▸ hy)
      omega
    have hL1 := two_mul_sum_ge T ((s \ T).max' hu₀ne + 1) hTlb
    rw [hTcard] at hL1
    have hminmem : (s \ T).min' hu₀ne ∈ s \ T := (s \ T).min'_mem hu₀ne
    have hcardJ : ((s \ T).erase ((s \ T).min' hu₀ne)).card = k := by
      rw [Finset.card_erase_of_mem hminmem, hcardu]
      omega
    have hJb : ∀ j ∈ (s \ T).erase ((s \ T).min' hu₀ne), j ≤ (s \ T).max' hu₀ne :=
      fun j hj ↦ (s \ T).le_max' j (Finset.mem_of_mem_erase hj)
    have hL2 := two_mul_sum_le ((s \ T).erase ((s \ T).min' hu₀ne)) ((s \ T).max' hu₀ne) hJb
    rw [hcardJ] at hL2
    have h3 : (s \ T).min' hu₀ne + ∑ j ∈ (s \ T).erase ((s \ T).min' hu₀ne), j
        = ∑ x ∈ s \ T, x := (s \ T).add_sum_erase (fun x => x) hminmem
    have h4 : ∑ x ∈ s \ T, x + ∑ x ∈ T, x = ∑ x ∈ s, x := Finset.sum_sdiff hTsub
    have e1 : ∑ x ∈ T, x + 1
        ≤ (s \ T).min' hu₀ne + ∑ j ∈ (s \ T).erase ((s \ T).min' hu₀ne), j := by
      omega
    have ha₀ : k * k + 1 ≤ (s \ T).min' hu₀ne := by
      linarith [hL1, hL2, e1]
    -- Moreover the largest element of `s \ T` is at least `min' (s \ T) + k`.
    have hsubIcc : s \ T ⊆ Finset.Icc ((s \ T).min' hu₀ne) ((s \ T).max' hu₀ne) := by
      intro j hj
      rw [Finset.mem_Icc]
      exact ⟨(s \ T).min'_le j hj, (s \ T).le_max' j hj⟩
    have hMu : (s \ T).min' hu₀ne + k ≤ (s \ T).max' hu₀ne := by
      have h5 := Finset.card_le_card hsubIcc
      rw [Nat.card_Icc, hcardu] at h5
      omega
    have g1 : k * ((s \ T).min' hu₀ne + k) ≤ k * (s \ T).max' hu₀ne :=
      mul_le_mul_of_nonneg_left hMu (Nat.zero_le k)
    have g2 : k * (k * k + 1) ≤ k * (s \ T).min' hu₀ne :=
      mul_le_mul_of_nonneg_left ha₀ (Nat.zero_le k)
    linarith [hN1, hL1, g1, g2]

end Usa2006P2
