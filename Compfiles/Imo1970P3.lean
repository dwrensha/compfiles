/-
Copyright (c) 2025 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Ortega
-/

import Mathlib.Tactic
import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Olympiad 1970, Problem 3

 The real numbers a₀, a₁, a₂, ... satisfy 1 = a₀ ≤ a₁ ≤ a₂ ≤ ... . b₁, b₂, b₃, ... are defined by bₙ = ∑_{k=1}^{n} (1 - a_{k-1}/a_k)/√a_k.

(a)  Prove that 0 ≤ bₙ < 2.

(b)  Given c satisfying 0 ≤ c < 2, prove that we can find an so that bₙ > c for all sufficiently large n.
-/

namespace Imo1970P3


open scoped Real

/-- A sequence of real numbers satisfying the given conditions -/
structure IncreasingSequenceFromOne where
  a : ℕ → ℝ
  a_zero : a 0 = 1
  a_mono : Monotone a

/-- The b_n sequence defined in terms of the a sequence -/
noncomputable def b_seq (seq : IncreasingSequenceFromOne) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, (1 - seq.a k / seq.a (k + 1)) / √ (seq.a (k + 1))

def ValidBounds : Set ℝ :=
  { b | 0 ≤ b ∧ b < 2 }

snip begin

/-- Helper: c_k = √(a_k) -/
noncomputable def c_seq (seq : IncreasingSequenceFromOne) (k : ℕ) : ℝ := Real.sqrt (seq.a k)

/-- All elements of the sequence are positive -/
lemma seq_pos (seq: IncreasingSequenceFromOne) : ∀ n, 0 < seq.a n := by
  intro n
  induction n with
  | zero =>
    rw [seq.a_zero]
    exact zero_lt_one
  | succ n ih =>
    have h1 : seq.a n ≤ seq.a (n + 1) := seq.a_mono (Nat.le_succ n)
    exact lt_of_lt_of_le ih h1

/-- Key lemma: each term is bounded by 2(1/c_{k-1} - 1/c_k) -/
lemma term_bound (seq : IncreasingSequenceFromOne) (k : ℕ) :
  (1 - seq.a (k - 1) / seq.a k) / Real.sqrt (seq.a k) ≤
  2 * (1 / c_seq seq (k - 1) - 1 / c_seq seq k) := by
  -- Let c_k = √(a_k)
  have ck_pos : ∀ j, 0 < c_seq seq j := fun j => Real.sqrt_pos.mpr (seq_pos seq j)
  have ck_is_ak_squared: ∀ j, seq.a j = (c_seq seq j)^2 := by
    intro j
    simp [c_seq, Real.sq_sqrt (le_of_lt (seq_pos seq j))]

  have hcseq : c_seq seq (k - 1) ≤ c_seq seq k := Real.sqrt_le_sqrt (seq.a_mono (Nat.sub_le k 1))

  -- The term equals c_{k-1}²/c_k · (1/a_{k-1} - 1/a_k)
  have h1 : (1 - seq.a (k - 1) / seq.a k) / Real.sqrt (seq.a k) = (c_seq seq (k - 1))^2 / c_seq seq k * (1 / seq.a (k - 1) - 1 / seq.a k) := by
    simp [c_seq, Real.sq_sqrt (le_of_lt (seq_pos seq _))]
    have haUnit : IsUnit (seq.a (k - 1)) := by
      rw [isUnit_iff_ne_zero]
      let j := k - 1
      have hj : j = k-1 := rfl
      rw [←hj]
      have := seq_pos seq j
      linarith
    ring_nf
    simp [field]
    rw [IsUnit.div_mul_left haUnit]
    exact inv_eq_one_div √(seq.a k)

  -- Factor 1/a_{k-1} - 1/a_k using difference of squares
  have h2 : 1 / seq.a (k - 1) - 1 / seq.a k =
    (1 / c_seq seq (k - 1) + 1 / c_seq seq k) * (1 / c_seq seq (k - 1) - 1 / c_seq seq k) := by
    rw [ck_is_ak_squared (k-1), ck_is_ak_squared k]
    ring

  -- Show c_{k-1}²/c_k · (1/c_{k-1} + 1/c_k) ≤ 2
  have h3 : (c_seq seq (k - 1))^2 / c_seq seq k * (1 / c_seq seq (k - 1) + 1 / c_seq seq k) ≤ 2 := by
    calc
      _ = c_seq seq (k - 1) / c_seq seq k + (c_seq seq (k - 1) / c_seq seq k)^2 := by
        have := ck_pos k
        have := ck_pos (k - 1)
        field_simp
      _ ≤ 1 + 1 := by
        apply add_le_add
        · exact (div_le_one (ck_pos k)).mpr hcseq
        · rw [sq_le_one_iff_abs_le_one, abs_div, abs_of_pos (ck_pos (k-1)), abs_of_pos (ck_pos k)]
          exact (div_le_one (ck_pos k)).mpr hcseq
      _ = 2 := one_add_one_eq_two

  rw [h1, h2, ←mul_assoc]
  apply mul_le_mul_of_nonneg_right h3
  rw [sub_nonneg]
  exact one_div_le_one_div_of_le (ck_pos (k - 1)) hcseq

snip end

problem imo1970_p3 :
    (∀ seq : IncreasingSequenceFromOne, ∀ n : ℕ, b_seq seq n ∈ ValidBounds) ∧
    (∀ c ∈ ValidBounds, ∃ seq : IncreasingSequenceFromOne, ∃ N : ℕ,
      ∀ n ≥ N, b_seq seq n > c) := by
  constructor
  /-
  Part (a): All b_n are in [0, 2)
  Each term of the sum is non-negative, so b_n is non-negative. Let c_k = √a_k. Then the kth term = (1 - a_{k-1}/a_k)/√a_k = c_{k-1}²/c_k (1/a_{k-1} - 1/a_k) = c_{k-1}²/c_k (1/c_{k-1} + 1/c_k)(1/c_{k-1} - 1/c_k). But c_{k-1}²/c_k (1/c_{k-1} + 1/c_k) ≤ 2, so the kth term ≤ 2(1/c_{k-1} - 1/c_k). Hence b_n ≤ 2 - 2/c_n < 2.
  -/
  · intro seq n
    constructor
    · -- 0 ≤ b_n
      apply Finset.sum_nonneg
      intro k hk
      have h1 : seq.a k ≤ seq.a (k + 1) := seq.a_mono (Nat.le_succ k)
      have h2 : 0 < seq.a (k + 1) := seq_pos seq (k + 1)
      have h3 : seq.a k / seq.a (k + 1) ≤ 1 := (div_le_one h2).mpr h1
      exact div_nonneg (sub_nonneg.mpr h3) (Real.sqrt_nonneg _)

    · -- b_n < 2
      cases n with
      | zero => simp only [b_seq, Finset.range_zero, Finset.sum_empty, zero_lt_two]
      | succ n =>
        -- Use telescoping sum
        -- Change of index: the k-th term for k ≥ 1 is bounded by 2(1/√a_{k-1} - 1/√a_k)
        have bound : b_seq seq (n + 1) ≤ 2 * (1 - 1 / c_seq seq (n + 1)) := by
          -- Split the sum to handle k = 0 separately
          have split_sum : b_seq seq (n + 1) =
            (1 - seq.a 0 / seq.a 1) / Real.sqrt (seq.a 1) +
            ∑ k ∈ Finset.range n, (1 - seq.a (k + 1) / seq.a (k + 2)) / Real.sqrt (seq.a (k + 2)) := by
            rw [b_seq, Finset.sum_range_succ', add_comm]

          -- Apply term_bound to each term k ≥ 1
          have sum_bound : ∑ k ∈ Finset.range n, (1 - seq.a (k + 1) / seq.a (k + 2)) / Real.sqrt (seq.a (k + 2)) ≤
            2 * ∑ k ∈ Finset.range n, (1 / c_seq seq (k + 1) - 1 / c_seq seq (k + 2)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_le_sum
            intro k hk
            exact term_bound seq (k + 2)

          -- The sum telescopes
          have telescoping : ∑ k ∈ Finset.range n, (1 / c_seq seq (k + 1) - 1 / c_seq seq (k + 2)) =
              1 / c_seq seq 1 - 1 / c_seq seq (n + 1) :=
            Finset.sum_range_sub' (fun i ↦ 1 / c_seq seq (i + 1)) n

          -- Handle the k = 0 term
          have first_term_bound : (1 - seq.a 0 / seq.a 1) / Real.sqrt (seq.a 1) ≤ 2 * (1 / c_seq seq 0 - 1 / c_seq seq 1) := by
            convert term_bound seq 1 using 1

          -- Combine everything
          calc b_seq seq (n + 1)
            = _ := split_sum
            _ ≤ 2 * (1 / c_seq seq 0 - 1 / c_seq seq 1) + 2 * ∑ k ∈ Finset.range n, (1 / c_seq seq (k + 1) - 1 / c_seq seq (k + 2)) := add_le_add first_term_bound sum_bound
            _ = 2 * (1 / c_seq seq 0 - 1 / c_seq seq 1) + 2 * (1 / c_seq seq 1 - 1 / c_seq seq (n + 1)) := by
              rw [telescoping]
            _ = 2 * (1 / c_seq seq 0 - 1 / c_seq seq (n + 1)) := by ring
            _ = 2 * (1 - 1 / c_seq seq (n + 1)) := by
              rw [c_seq, seq.a_zero, Real.sqrt_one]
              simp only [ne_eq, one_ne_zero, not_false_eq_true, div_self, one_div]

        -- Since c_seq seq (n + 1) > 0, we have 1 / c_seq seq (n + 1) > 0
        have pos : 0 < 1 / c_seq seq (n + 1) := by
          apply div_pos one_pos
          exact Real.sqrt_pos.mpr (seq_pos seq (n + 1))

        exact lt_of_le_of_lt bound (by linarith)

  /-
  Part (b): For each c ∈ [0, 2), there exists a sequence with b_n > c for large n
  Note that we can use d = √(c/2) for the solution, unless c = 0, in which case we can use d = 1/2.
  Let 1/√aₖ = d^k, where 0 < d < 1 is a constant, which we will choose later. Then the kth term is (1 - d²)d^k, so bₙ = d(1+d)(1 - d^n). Now take d such that d(1+d) > c, which we can do, since since d(1+d) tends to 2 when d tends to 1, and then take n sufficiently large so that bₙ > c.
  -/

  · intro c hc
    obtain ⟨hc_nonneg, hc_lt_two⟩ := hc

    have existsD : ∃ d : ℝ, 0 < d ∧ d < 1 ∧ d*(1 + d) > c := by
      by_cases h : c = 0
      · use 1 / 2
        constructor
        · exact one_half_pos
        · constructor
          · exact one_half_lt_one
          · linarith
      -- If c > 0, we can find a d such that d(1 + d) > c
      · use √ (c / 2)
        have hc : 0 < c := lt_of_le_of_ne hc_nonneg fun a ↦ h a.symm
        have hc' : 0 < c / 2 := half_pos hc
        have : c / 2 < 1 := by linarith
        have hd : 0 < √ (c / 2) := Real.sqrt_pos.mpr hc'
        constructor
        · exact hd
        · constructor
          · -- square both sides
            rwa [Real.sqrt_lt (le_of_lt hc') zero_le_one, one_pow]
          · rw [mul_add, mul_one, Real.mul_self_sqrt (le_of_lt hc')]
            suffices c / 2 < √(c / 2) by linarith
            nth_rw 1 [show c / 2 = √(c / 2) ^ 2 by rw [Real.sq_sqrt (le_of_lt hc')]]
            apply pow_lt_self_of_lt_one₀ hd _ one_lt_two
            rwa [Real.sqrt_lt' zero_lt_one, one_pow]

    obtain ⟨d, dpos, d_lt_one, d_bound⟩ := existsD
    have d_nonneg : 0 ≤ d := le_of_lt dpos
    have d_leq_one : d ≤ 1 := le_of_lt d_lt_one
    have d_neq_one : d ≠ 1 := Ne.symm (ne_of_gt d_lt_one)
    have one_minus_d_neq_zero : 1 - d ≠ 0 := sub_ne_zero_of_ne (id (Ne.symm d_neq_one))
    have daux : d * (1 + d) > 0 := mul_pos dpos (add_pos one_pos dpos)


    -- Define the geometric sequence aₙ = d^(-k/2)
    let a_seq : IncreasingSequenceFromOne := {
      a := fun k => d^(-(k:ℝ) * 2)
      a_zero := by simp
      a_mono := by
        intro i j hij
        aesop
    }

    use a_seq

    let N := Nat.ceil (1 + Real.log (1 - c / (d * (1 + d))) / Real.log d)

    use N
    intro n hn

    dsimp [b_seq, a_seq]
    simp only [neg_mul, Nat.cast_add, Nat.cast_one, neg_add_rev, gt_iff_lt]
    calc
      c < d * (1 + d) * (1 - d ^ N) := by
        -- divide both sides by d * (1 + d)
        rw [←inv_mul_lt_iff₀ daux]
        suffices d ^ N < 1 - (d * (1 + d))⁻¹ * c by linarith
        rw [←Real.log_lt_log_iff]
        · rw [Real.log_pow d N]
          suffices Real.log (1 - (d * (1 + d))⁻¹ * c) / Real.log d < ↑N by
            rwa [←div_lt_iff_of_neg (Real.log_neg dpos d_lt_one)]
          calc
            _ < 1 + Real.log (1 - (d * (1 + d))⁻¹ * c) / Real.log d := lt_one_add _
            _ = 1 + Real.log (1 - c / (d * (1 + d))) / Real.log d := by field_simp
            _ ≤ _ := by apply Nat.le_ceil
        · exact pow_pos dpos N
        · suffices (d * (1 + d))⁻¹ * c < 1 by linarith
          rwa [inv_mul_lt_one₀ daux]
      _ ≤ d * (1 + d) * (1 - d ^ (n:ℝ)) := by
        norm_cast
        apply mul_le_mul_of_nonneg_left _ (le_of_lt daux)
        apply tsub_le_tsub (le_refl 1)
        exact pow_le_pow_of_le_one d_nonneg d_leq_one hn
      _ = ∑ x ∈ Finset.range n, (1 - d^2) * d^(x + 1) := by
        rw [←Finset.mul_sum]
        have : ∑ i ∈ Finset.range n, d ^ (i + 1) = d * ∑ i ∈ Finset.range n, d ^ i := by
          rw [Finset.mul_sum]
          congr
          ring_nf
        rw [this, geom_sum_eq d_neq_one n]
        norm_cast
        calc
          _ = (1 - d ^ 2) * (d * ((1 - d ^ n) * (1 - d)⁻¹)) := by
            field_simp
            ring_nf
          _ = (1 - d ^ 2) * (d * (-(1 - d ^ n) / -(1 - d))) := by rw [←div_eq_mul_inv, neg_div_neg_eq]
          _ = _ := by ring_nf
      _ = _ := by
        congr
        ext x
        have : √(d ^ ((-1 + -(x:ℝ)) * 2)) = d ^ ((-1 + -(x:ℝ))) := by
          rw [Real.sqrt_eq_rpow, ←Real.rpow_mul d_nonneg]
          ring_nf
        rw [this]
        field_simp
        calc
          _ = (1 - d ^ 2) * (d ^ (x + 1) * d ^ (-(1 + (x:ℝ)))) * d ^ (-(1 + (x:ℝ)) * 2) := by ring_nf
          _ = (1 - d ^ 2) * (d ^ ((-1 + -(x:ℝ)) * 2)) := by
            suffices d ^ (x + 1) * d ^ (-(1 + (x:ℝ))) = 1 by
              rw [this, mul_one, neg_add_rev, add_comm]
            rw [Real.rpow_neg d_nonneg, add_comm]
            norm_cast
            field_simp
          _ = _ := by
            ring_nf
            rw [add_comm]
            suffices d ^ 2 * d ^ (-2 - (x:ℝ) * 2) = d ^ (-((x:ℝ ) * 2)) by
              rw [this]
              rfl
            calc
              _ = d ^ (2 + (-2 - (x:ℝ) * 2)) := by
                rw [Real.rpow_add dpos, Real.rpow_ofNat]
              _ = _ := by ring_nf

end Imo1970P3
