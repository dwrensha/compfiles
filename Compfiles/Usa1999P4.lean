/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Ring.Star
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Inequality] }

/-!
# USA Mathematical Olympiad 1999, Problem 4

Let a₁, a₂, ..., aₙ be a sequence of n > 3 real numbers such that

  a₁ + a₂ + ⋯ + aₙ ≥ n

and

  a₁² + a₂² + ⋯ + aₙ² ≥ n².

Prove that max(a₁, a₂, ..., aₙ) ≥ 2.
-/

namespace Usa1999P4

snip begin

/-!
We follow the proof from Evan Chen's
[USAMO 1999 Solution Notes](https://web.evanchen.cc/exams/USAMO-1999-notes.pdf),
reformulated so that no iterative "smoothing" is needed.

Assume `aᵢ < 2` for all `i`. If every `aᵢ` is nonnegative, then
`∑ aᵢ² < 4n ≤ n²`, a contradiction. Otherwise, writing `S` for the sum of the
nonnegative entries and `-M` for the sum of the negative entries, one checks
`∑ aᵢ² ≤ 2S + M²` and `M ≤ S - n`, hence `n² ≤ 2S + (S - n)²`, which forces
`S ≥ 2n - 2`. But `S < 2·#P ≤ 2(n - 1)`, contradiction.
-/

/-- If every value of `f` on `s` is nonpositive, then the sum of the squares is
at most the square of the sum: the cross terms are nonnegative. -/
theorem sum_sq_le_sq_sum_of_nonpos {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, f i ≤ 0) :
    ∑ i ∈ s, f i ^ 2 ≤ (∑ i ∈ s, f i) ^ 2 := by
  have h1 : ∑ i ∈ s, f i ^ 2 = ∑ i ∈ s, (-f i) ^ 2 :=
    Finset.sum_congr rfl fun i _ ↦ by rw [neg_sq]
  have h2 : (∑ i ∈ s, f i) ^ 2 = (∑ i ∈ s, -f i) ^ 2 := by
    rw [Finset.sum_neg_distrib, neg_sq]
  rw [h1, h2]
  exact Finset.sum_sq_le_sq_sum_of_nonneg fun i hi ↦ neg_nonneg.mpr (hf i hi)

snip end

problem usa1999_p4 (n : ℕ) (hn : 3 < n) (a : Fin n → ℝ)
    (hsum : (n : ℝ) ≤ ∑ i, a i) (hsq : (n : ℝ) ^ 2 ≤ ∑ i, (a i) ^ 2) :
    ∃ i, 2 ≤ a i := by
  by_contra! hlt2
  -- `P` = indices of the nonnegative entries, `N` = indices of the negative ones.
  set P := Finset.univ.filter fun i ↦ 0 ≤ a i with hP
  set N := Finset.univ.filter fun i ↦ ¬ 0 ≤ a i with hN
  have hpart : ∀ f : Fin n → ℝ, ∑ i, f i = ∑ i ∈ P, f i + ∑ i ∈ N, f i :=
    fun f ↦ (Finset.sum_filter_add_sum_filter_not Finset.univ _ f).symm
  by_cases hNe : N = ∅
  · -- Every entry is nonnegative, so `aᵢ² < 4` for all `i` and `∑ aᵢ² < 4n ≤ n²`.
    have hnonneg : ∀ i, 0 ≤ a i := by
      intro i
      by_contra hi
      have him : i ∈ N := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
      rw [hNe] at him
      exact Finset.notMem_empty i him
    have hsum4 : ∑ i, (a i) ^ 2 < 4 * n := by
      have hlt : ∑ i, (a i) ^ 2 < ∑ _i : Fin n, (4 : ℝ) := by
        apply Finset.sum_lt_sum_of_nonempty
        · have : Nonempty (Fin n) := ⟨⟨0, by lia⟩⟩
          exact Finset.univ_nonempty
        · intro i _
          have h1 := hnonneg i
          have h2 := hlt2 i
          nlinarith [mul_nonneg h1 (sub_nonneg_of_le h2.le : (0 : ℝ) ≤ 2 - a i)]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hlt
      linarith [hlt]
    have hn4 : (4 : ℝ) * n ≤ (n : ℝ) ^ 2 := by
      have h1 : (4 : ℝ) ≤ n := by exact_mod_cast hn
      have h2 : (0 : ℝ) ≤ n := by positivity
      calc (4 : ℝ) * n ≤ n * n := mul_le_mul_of_nonneg_right h1 h2
        _ = (n : ℝ) ^ 2 := by ring
    linarith
  · -- Some entry is negative.
    have hNne : N.Nonempty := Finset.nonempty_iff_ne_empty.mpr hNe
    set S := ∑ i ∈ P, a i with hSdef
    set M := -∑ i ∈ N, a i with hMdef
    have hMpos : 0 < M := by
      have hneg : ∑ i ∈ N, a i < 0 := by
        have hlt : ∑ i ∈ N, a i < ∑ _i ∈ N, (0 : ℝ) :=
          Finset.sum_lt_sum_of_nonempty hNne fun i hi ↦
            not_le.mp (Finset.mem_filter.mp hi).2
        rwa [Finset.sum_const_zero] at hlt
      rw [hMdef]
      exact neg_pos.mpr hneg
    have hSM : (n : ℝ) ≤ S - M := by
      have hp := hpart a
      rw [hSdef, hMdef]
      linarith [hsum, hp]
    have hSpos : 0 < S := by
      have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by lia)
      linarith [hSM, hMpos, hnpos]
    -- Bound the two parts of `∑ aᵢ²`: on `P` use `aᵢ² ≤ 2aᵢ`, on `N` the
    -- cross terms of `M²` are nonnegative.
    have hPsq : ∑ i ∈ P, (a i) ^ 2 ≤ 2 * S := by
      rw [hSdef, Finset.mul_sum]
      refine Finset.sum_le_sum fun i hi ↦ ?_
      have h1 : 0 ≤ a i := (Finset.mem_filter.mp hi).2
      have h2 : a i < 2 := hlt2 i
      nlinarith [mul_nonneg h1 (sub_nonneg_of_le h2.le : (0 : ℝ) ≤ 2 - a i)]
    have hNsq : ∑ i ∈ N, (a i) ^ 2 ≤ M ^ 2 := by
      rw [hMdef, neg_sq]
      exact sum_sq_le_sq_sum_of_nonpos N a fun i hi ↦
        le_of_lt (not_le.mp (Finset.mem_filter.mp hi).2)
    -- Combine: `n² ≤ 2S + (S - n)²`, hence `S ≥ 2n - 2`.
    have hMle : M ≤ S - n := by linarith [hSM]
    have hMsq : M ^ 2 ≤ (S - n) ^ 2 := pow_le_pow_left₀ hMpos.le hMle 2
    have hcomb : (n : ℝ) ^ 2 ≤ 2 * S + (S - n) ^ 2 :=
      calc (n : ℝ) ^ 2 ≤ ∑ i, (a i) ^ 2 := hsq
        _ = ∑ i ∈ P, (a i) ^ 2 + ∑ i ∈ N, (a i) ^ 2 := hpart _
        _ ≤ 2 * S + M ^ 2 := add_le_add hPsq hNsq
        _ ≤ 2 * S + (S - n) ^ 2 := by linarith [hMsq]
    have hSge : 2 * n - 2 ≤ S := by
      have hstep : 0 ≤ S * (S + 2 - 2 * n) := by
        have h2 : S * (S + 2 - 2 * n) = 2 * S + (S - n) ^ 2 - n ^ 2 := by ring
        rw [h2]
        linarith [hcomb]
      have hX : 0 ≤ S + 2 - 2 * n := nonneg_of_mul_nonneg_right hstep hSpos
      linarith
    -- But `S < 2·#P ≤ 2(n - 1)`, contradiction.
    have hPne : P.Nonempty := by
      by_contra hcon
      rw [Finset.not_nonempty_iff_eq_empty] at hcon
      have hS0 : S = 0 := by rw [hSdef, hcon, Finset.sum_empty]
      linarith [hSpos, hS0]
    have hSlt : S < 2 * P.card := by
      obtain ⟨j, hj⟩ := hPne
      have hlt : ∑ i ∈ P, a i < ∑ _i ∈ P, (2 : ℝ) :=
        Finset.sum_lt_sum (fun i _ ↦ le_of_lt (hlt2 i)) ⟨j, hj, hlt2 j⟩
      rw [Finset.sum_const, nsmul_eq_mul] at hlt
      rw [hSdef]
      linarith [hlt]
    have hcard : (P.card : ℝ) + 1 ≤ n := by
      have h1 : P.card + N.card = n := by
        have h2 := Finset.card_filter_add_card_filter_not (s := Finset.univ)
          (p := fun i ↦ 0 ≤ a i)
        rwa [Finset.card_univ, Fintype.card_fin] at h2
      have h2 : 1 ≤ N.card := Finset.card_pos.mpr hNne
      have h3 : P.card + 1 ≤ n := by lia
      exact_mod_cast h3
    have hfin : 2 * (P.card : ℝ) ≤ 2 * n - 2 := by linarith [hcard]
    linarith [hSge, hSlt, hfin]

end Usa1999P4
