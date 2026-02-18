/-
Copyright (c) 2025 The Compfiles Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Rydh
-/

import Mathlib.Tactic

import ProblemExtraction

set_option backward.isDefEq.respectTransparency false


problem_file {
  tags := [.Algebra]
}

/-!
# International Mathematical Olympiad 1967, Problem 5

Consider the sequence {cₙ}, where

   c₁ = a₁  + a₂  + ... + a₈
   c₂ = a₁² + a₂² + ... + a₈²
   ...
   cₙ = a₁ⁿ + a₂ⁿ + ... + a₈ⁿ

in which a₁, a₂, ..., a₈ are real numbers not all
equal to zero. Suppose that an infinite number of terms
of the sequence {cₙ} are equal to zero. Find all natural
numbers n such that cₙ = 0.
-/

namespace Imo1967P5

determine solution : (Fin 8 → ℝ) → Set ℕ := fun _ => { n | Odd n }

snip begin

lemma odd_if_sum_eq_zero {α : Type*} {n : ℕ}
    (I : Finset α)
    (f : α → ℝ)
    (h : ∃ α ∈ I, f α ≠ 0)
    : ∑ i ∈ I, f i^n = 0 → Odd n := by
  intro h2
  obtain ⟨m, hm, hm2⟩ := h
  by_contra! h_not_odd
  have h_even := Nat.not_odd_iff_even.mp h_not_odd
  have h_pos : 0 < ∑ i ∈ I, f i^n := by calc
    0 < f m^n := Even.pow_pos h_even hm2
    _ ≤ ∑ i ∈ I, f i^n := Finset.single_le_sum (fun i a ↦ Even.pow_nonneg h_even (f i)) hm
  simp [h2] at h_pos

lemma aux_recursive (I : Finset (Fin 8)) (a : Fin 8 → ℝ)
    (h₁ : Set.Infinite {n | ∑ i ∈ I, a i ^ n = 0})
    (h₂ : ∃ i ∈ I, a i ≠ 0) :
    ∀ n, Odd n → ∑ i ∈ I, a i ^ n = 0 := by
  by_cases! h_empty_I : I = ∅
  · subst h_empty_I
    intro _ _
    rfl
  · obtain ⟨imax⟩ := Finset.exists_max_image I (fun i ↦ |a i|) h_empty_I
    let amax := |a imax|
    have h_pos_amax : 0 < amax := by grind
    -- Split the index set into those having the max absolute value (J) and those that do not (K)
    let J := I.filter (fun i ↦ amax ≤ |a i|)
    let K := I.filter (fun i ↦ |a i| < amax)

    -- Sum over I can be split over K and J
    have h_sum_union_eq_sum_disj : ∀ n, ∑ i ∈ I, a i^n = (∑ k ∈ K, a k^ n) + (∑ j ∈ J, a j ^ n) := by
      intro n
      have h_disj : Disjoint K J := by
        apply Finset.disjoint_left.mpr
        intro x hk hj
        grind only [= Finset.mem_filter]
      have : K ∪ J = I := by grind only [= Finset.mem_union, = Finset.mem_filter]
      rw [← this]
      exact Finset.sum_union h_disj

    -- This is the core of the actual IMO problem
    -- We prove that for large N, the sum over J is large compared to the sum over K
    -- From that we deduce that the sum over J must be zero for odd n, otherwise
    -- the sum over I cannot be zero. We then use this to reduce the problem to K
    -- and apply the lemma recursively.
    have h_sum_J_eq_zero_of_odd : ∀ n, Odd n → ∑ j ∈ J, a j ^ n = 0 := by
      -- Prepare bound q for the terms in K
      have hq : ∃ q : ℝ, 0 ≤ q ∧ q < amax ∧ ∀ k ∈ K, |a k| ≤ q := by
        by_cases! h_empty_K : K = ∅
        · use 0
          grind
        obtain ⟨kmax, h_kmax, _⟩ := Finset.exists_max_image K (fun k ↦ |a k|) h_empty_K
        use |a kmax|
        constructor
        · exact abs_nonneg (a kmax)
        constructor
        · exact (Finset.mem_filter.mp h_kmax).2
        trivial
      obtain ⟨q, h_pos_q, h_q_lt_amax, h_ak_le_q⟩ := hq
      -- Show that for large n, the bound for sum over K is small compared to amax^n
      have h_eventually_dominated : ∀ᶠ n in Filter.atTop, 8 * q^n < amax^n := by
        rw [Filter.eventually_atTop]
        by_cases! h_case : q = 0
        · use 1
          intro N h_pos_N
          simp [h_case, zero_pow (Nat.ne_zero_of_lt h_pos_N), pow_pos h_pos_amax N]
        · have h_pos_q : 0 < q := Std.lt_of_le_of_ne h_pos_q (Ne.symm h_case)
          have h_ratio_pos : 1 < amax / q := (one_lt_div₀ h_pos_q).mpr h_q_lt_amax
          have := (tendsto_pow_atTop_atTop_of_one_lt h_ratio_pos).eventually_gt_atTop 8
          obtain ⟨N, hlt⟩ := this.exists
          use N
          intro M h_M_ge_N
          calc
            8 * q^M < (amax / q)^N * q^M := by
              apply mul_lt_mul_of_pos_right hlt
              exact pow_pos h_pos_q M
            _ ≤ (amax / q)^M * q^M := by
              have : (amax / q)^N ≤ (amax / q)^M := (pow_le_pow_iff_right₀ h_ratio_pos).mpr h_M_ge_N
              aesop
            _ = amax^M := by
              rw [← mul_pow]
              congr
              field_simp
      -- Finally we are ready to obtain N where the sum over I is zero and the sum over K is small
      have h_freq := Nat.frequently_atTop_iff_infinite.mpr h₁
      obtain ⟨N, h_sum_I_pow_N_zero, h_bounds⟩ := (Filter.Frequently.and_eventually h_freq h_eventually_dominated).exists
      -- N is odd since the sum over I is zero
      have h_odd_N : Odd N := odd_if_sum_eq_zero I a h₂ h_sum_I_pow_N_zero

      let p := fun i ↦ SignType.sign (a i)

      -- The sum over J must be a multiple of amax^n (all terms have the same absolute value)
      have h_sum_I_mult_amax : ∃ m : ℤ, ∀ n, Odd n → ∑ j ∈ J, a j^n = m * amax^n := by
        have h_eq : ∀ j ∈ J, a j = (p j) * amax := by
          intro j hj
          have : |a j| = amax := by grind
          rw [← this]
          exact Eq.symm (sign_mul_abs (a j))

        use ∑ j ∈ J, p j
        intro n h_odd
        have h_eq_pow_n : ∀ j ∈ J, a j^n = (p j) * amax^n := by
          intro i hi
          have hp_pow_odd_n : ∀ i n, Odd n → p i = p i^n := by
            intro i n h_odd
            rcases SignType.trichotomy (p i) with hneg | hzero | hpos
            · simp [hneg, Odd.neg_one_pow h_odd]
            · exact Eq.symm (SignType.pow_odd (p i) h_odd)
            · simp [hpos]
          calc
            a i^n = ((p i) * amax)^n := by simp [h_eq i hi]
            _ = p i^n * amax^n := mul_pow ↑(p i) amax n
            _ = p i * amax^n := by
              field_simp
              norm_cast
              rw [← hp_pow_odd_n i n h_odd]

        rw [Int.cast_sum, Finset.sum_mul, Finset.sum_congr rfl]
        simp only [SignType.intCast_cast]
        intro i hi
        exact h_eq_pow_n i hi
      obtain ⟨m, hm⟩ := h_sum_I_mult_amax

      -- First part of proving that m must be zero.
      -- This corresponds to half of the a j = amax and half a j = -amax.
      have hmIneq : |m| * amax^N < amax^N := by
        have h_pow_ak_le_q : ∀ i ∈ K, |a i|^N ≤ q^N := by
          intro i hI
          have hq : |a i| ≤ q := by exact RCLike.ofReal_le_ofReal.mp (h_ak_le_q i hI)
          have haipos : 0 ≤ |a i| := by exact abs_nonneg (a i)
          exact pow_le_pow_left₀ haipos hq N

        calc
          |m| * amax^N = |m * amax^N| := by simp [abs_mul, abs_of_pos (pow_pos h_pos_amax N)]
          _ = |∑ k ∈ J, a k^N| := Eq.symm (congr_arg abs (hm N h_odd_N))
          _ = |∑ k ∈ I, a k^N - ∑ k ∈ K, a k^N| := by simp [h_sum_union_eq_sum_disj N, add_comm]
          _ = |∑ k ∈ K, a k^N| := by simp [h_sum_I_pow_N_zero]
          _ ≤ ∑ k ∈ K, |a k^N| := Finset.abs_sum_le_sum_abs (fun i ↦ a i ^ N) K
          _ = ∑ k ∈ K, |a k|^N := by simp
          _ ≤ ∑ k ∈ K, q^N := by exact Finset.sum_le_sum h_pow_ak_le_q
          _ = K.card * q^N := by simp
          _ ≤ 8 * q^N := by
            gcongr
            simp only [Nat.cast_le_ofNat]
            exact card_finset_fin_le K
          _ < amax^N := RCLike.ofReal_lt_ofReal.mp h_bounds

      -- Conclude that m = 0
      have hmZero : m = 0 := by
        field_simp [h_pos_amax] at hmIneq
        norm_cast at hmIneq
        exact Int.abs_lt_one_iff.mp hmIneq

      -- Finally conclude that the sum over J is zero for all odd n
      intro n h_odd
      simp [hm n h_odd, hmZero]

    -- Now proceed to prove that the sum over I is zero for all odd n
    -- We split into two cases, since if all a k are zero, the infinite sum condition
    -- does not imply that there are infinite number of odd n for which it holds.
    by_cases! hai : ∀ k ∈ K, a k = 0
    -- Simple case, all terms in sum over K are zero
    · intro N h_odd_N
      rw [h_sum_union_eq_sum_disj N]
      have h_sum_K_zero : ∑ k ∈ K, a k^N = 0 := by
        have h_terms_K_zero : ∀ k ∈ K, a k^N = 0 := by
          intro k h_k
          rw [hai k h_k]
          have h_pos_N : 0 < N := Odd.pos h_odd_N
          simp only [pow_eq_zero_iff', ne_eq, true_and]
          exact Nat.ne_zero_of_lt h_pos_N
        exact Finset.sum_eq_zero h_terms_K_zero
      rw [h_sum_J_eq_zero_of_odd N h_odd_N, h_sum_K_zero, zero_add]

    -- Interesting case, not all remaining a k are zero
    · have h_inf_sum_K_zero : Set.Infinite {n | ∑ k ∈ K, a k^n = 0} := by
        have hSame : {n | ∑ i ∈ I, a i^n = 0} = {n | ∑ k ∈ K, a k^n = 0} := by
          ext N
          simp only [Set.mem_setOf_eq]
          constructor <;> intro hS
          · have hOdd : Odd N := odd_if_sum_eq_zero I a h₂ hS
            rw [h_sum_union_eq_sum_disj, h_sum_J_eq_zero_of_odd N hOdd, add_zero] at hS
            exact hS
          · have hOdd : Odd N := odd_if_sum_eq_zero K a hai hS
            simp [h_sum_union_eq_sum_disj, h_sum_J_eq_zero_of_odd N hOdd, add_zero, hS]
        simp [← hSame, h₁]
      have h_rec := aux_recursive K a h_inf_sum_K_zero
      have h_sum : ∀ n, Odd n → (∑ k ∈ K, a k ^ n) + (∑ k ∈ J, a k ^ n) = 0 := by
        intro N h_odd
        simp_all only [add_zero, J, K]
      intro N h_odd
      rw [h_sum_union_eq_sum_disj, h_sum N h_odd]
  termination_by I.card
  decreasing_by
    have hTSubset : K ⊂ I := by grind
    exact Finset.card_lt_card hTSubset

snip end

problem imo1967_p5 (a : Fin 8 → ℝ)
    (h₁ : Set.Infinite {n | ∑ i, a i ^ n = 0})
    (h₂ : ¬∀ i, a i = 0) :
    solution a = {n | ∑ i, a i ^ n = 0} := by
  rw [solution]
  ext N
  let I : Finset (Fin 8) := Finset.univ
  have h₃ : ∃ i ∈ I, a i ≠ 0 := by aesop
  constructor
  -- If N is odd, use the aux_recursive lemma to prove that the sum is zero
  · intro h_odd
    exact aux_recursive Finset.univ a h₁ h₃ N h_odd
  -- If sum is zero, prove that N cannot be even (all terms would be non-negative, not all zero)
  · intro h_zero_sum
    exact odd_if_sum_eq_zero Finset.univ a h₃ h_zero_sum

end Imo1967P5
