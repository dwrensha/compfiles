/-
Copyright (c) 2025 The Compfiles Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Rydh
-/

import Mathlib.Tactic

import ProblemExtraction


problem_file {
  tags := [.NumberTheory]
}

/-!
# International Mathematical Olympiad 1996, Problem 6

Let p, q, n be three positive integers with p + q < n. Let (x₀, x₁, . . . , xₙ)
be an (n + 1)-tuple of integers satisfying the following conditions:
(a) x₀ = xₙ = 0.
(b) For each i with 1 ≤ i ≤ n, either xᵢ − xᵢ₋₁ = p or xᵢ − xᵢ₋₁ = −q.
Show that there exist indices i < j with (i, j) ≠ (0, n), such that xᵢ = xⱼ.

-/

namespace Imo1996P6

snip begin

lemma one_lt_gcd_of_not_coprime {p q : ℕ} (h₁ : 0 < p) (h₂ : ¬Nat.Coprime p q) : 1 < p.gcd q := by
  simp at h₂
  have h_ne_zero : p.gcd q ≠ 0 := gcd_ne_zero_of_left (ne_zero_of_lt h₁)
  exact Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨h_ne_zero, h₂⟩

lemma dist_gt_one_of_ne_sign {p q : ℤ} (h₁ : p.sign ≠ q.sign) (h₂ : p ≠ 0) (h₃ : q ≠ 0) : 1 < |p - q| := by grind

lemma diff_ne_one_of_dist_gt_one {p q : ℤ} (h : 1 < |p - q|) : p - q ≠ 1 ∧ p - q ≠ -1 := by grind

lemma ne_zero_of_mul {p q r : ℤ} (h₁ : p ≠ 0) (h₂ : p = q * r) : q ≠ 0 ∧ r ≠ 0 := by grind

lemma sum_bivalued {p q : ℤ} (s : Finset (ℕ)) (f : ℕ → ℤ) (h : ∀ i ∈ s, f i = p ∨ f i = q) :
  ∃ r : ℕ, ∑ i ∈ s, f i = r * p + (s.card - r) * q ∧ r ≤ s.card := by
  let s₂ := s.filter (fun i ↦ f i = p)
  let r := s₂.card
  use r
  have h_sum_split : ∑ i ∈ s, f i = ∑ i ∈ s₂, f i + ∑ i ∈ (s \ s₂), f i := by
    rw [← Finset.sum_disjUnion (Finset.disjoint_sdiff)]
    have : s₂.disjUnion (s \ s₂) (Finset.disjoint_sdiff) = s := by grind
    rw [this]
  have h_s₂ : ∀ i ∈ s₂, f i = p := by grind
  have h_s_s₂ : ∀ i ∈ (s \ s₂), f i = q := by grind
  rw [Finset.sum_congr rfl h_s₂, Finset.sum_congr rfl h_s_s₂, Finset.sum_const, Finset.sum_const] at h_sum_split
  grind

snip end

problem imo1996_p6 {p q n : ℕ} (x : ℕ → ℤ)
    (h₁ : 0 < p) (h₂ : 0 < q) (h₃ : 0 < n) (h₄ : p + q < n)
    (h₅ : x 0 = 0) (h₆ : x n = 0)
    (h₇ : ∀ i < n, x (i + 1) - x i = p ∨ x (i + 1) - x i = -q) :
    ∃ i j : ℕ, 0 ≤ i ∧ i < j ∧ j ≤ n ∧ (i, j) ≠ (0, n) ∧ x i = x j := by
  -- Based on solution from https://prase.cz/kalva/imo/isoln/isoln966.html
  have h_tsum_i := Finset.sum_range_sub x
  simp only [h₅, sub_zero] at h_tsum_i

  -- If p and q is not coprime, then we can divide p, q and x i by their gcd and use induction
  by_cases h_coprime : ¬ Nat.Coprime p q
  · let w := p.gcd q
    have h_one_lt_w : 1 < w := one_lt_gcd_of_not_coprime h₁ h_coprime
    have h_w_pos : 0 < ↑w := Nat.gcd_pos_of_pos_left q h₁
    have h_w_dvd_xi : ∀ i ≤ n, ↑w ∣ (x i) := by
      intro i hi
      by_cases h_zero : i = 0
      · rw [h_zero, h₅] ; exact Int.dvd_zero ↑w
      · rw [← h_tsum_i]
        have : ∀ j < n, ↑w ∣ x (j + 1) - x j := by
          intro j hj
          have h_or := h₇ j hj
          cases' h_or with hp hq
          · rw [hp]
            exact Rat.normalize.dvd_num rfl
          · rw [hq, dvd_neg]
            exact Int.gcd_dvd_right p q
        have h_mem : ∀ k ∈ Finset.range i, k < n := by
          intro k hk
          rw [Finset.mem_range] at hk
          exact Nat.lt_of_lt_of_le hk hi
        exact Finset.dvd_sum fun k hk ↦ this k (h_mem k hk)

    -- Setup new p', q' and x' and prove all hypothesis needed for the recursion
    obtain ⟨p', hp'⟩ := exists_eq_mul_left_of_dvd (Nat.gcd_dvd_left p q)
    obtain ⟨q', hq'⟩ := exists_eq_mul_left_of_dvd (Nat.gcd_dvd_right p q)
    have : ∃ x' : ℕ → ℤ, ∀ i ≤ n, x i = x' i * w := by
      use (fun i ↦ (x i) / w)
      intro i hi
      simp
      exact Eq.symm (Int.ediv_mul_cancel (h_w_dvd_xi i hi))

    obtain ⟨x', hx'⟩ := this
    have h₁' : 0 < p' := by rw [hp'] at h₁ ; exact Nat.pos_of_mul_pos_right h₁
    have h₂' : 0 < q' := by rw [hq'] at h₂ ; exact Nat.pos_of_mul_pos_right h₂
    have h₄' : p' + q' < n := by
      have h_lt_p : p' < p := by rw [hp'] ; exact (Nat.lt_mul_iff_one_lt_right h₁').mpr h_one_lt_w
      have h_lt_q : q' < q := by rw [hq'] ; exact (Nat.lt_mul_iff_one_lt_right h₂').mpr h_one_lt_w
      exact Nat.lt_trans (Nat.add_lt_add h_lt_p h_lt_q) h₄
    have h₅' : x' 0 = 0 := by
      have := hx' 0
      rw [h₅] at this
      exact eq_zero_of_ne_zero_of_mul_right_eq_zero (Int.ofNat_ne_zero.mpr (Nat.ne_zero_of_lt h_one_lt_w)) (this (Nat.zero_le n)).symm
    have h₆' : x' n = 0 := by
      have := hx' n
      rw [h₆] at this
      exact eq_zero_of_ne_zero_of_mul_right_eq_zero (Int.ofNat_ne_zero.mpr (Nat.ne_zero_of_lt h_one_lt_w)) (this (Nat.le_refl n)).symm
    have h₇' : ∀ i < n, x' (i + 1) - x' i = p' ∨ x' (i + 1) - x' i = -q' := by
      intro i hi
      cases' h₇ i hi with hp hq
      · left
        rwa [hx' i (Nat.le_of_succ_le hi), hx' (i + 1) (Order.add_one_le_iff.mpr hi), hp', ←sub_mul, Nat.cast_mul,
            mul_right_cancel_iff_of_pos (Int.natCast_pos.mpr h_w_pos)] at hp
      · right
        rwa [hx' i (Nat.le_of_succ_le hi), hx' (i + 1) (Order.add_one_le_iff.mpr hi), hq', ←sub_mul, Nat.cast_mul,
            ←neg_mul, mul_right_cancel_iff_of_pos (Int.natCast_pos.mpr h_w_pos)] at hq

    -- Now use recursion to prove it for the reduced problem
    have h_ind := imo1996_p6 x' h₁' h₂' h₃ h₄' h₅' h₆' h₇'
    obtain ⟨i, j, h_i_pos, h_i_lt_j, h_j_lt_n, h_not_first_last, h_x'i_eq_x'j⟩ := h_ind
    -- Finally, use that result to get our solution from the reduced problem
    have h_xi_eq_xj : x i = x j := by
      rwa [hx' i (lt_of_lt_of_le h_i_lt_j h_j_lt_n).le, hx' j h_j_lt_n, mul_right_cancel_iff_of_pos (Int.natCast_pos.mpr h_w_pos)]
    exact ⟨i, j, h_i_pos, h_i_lt_j, h_j_lt_n, h_not_first_last, h_xi_eq_xj⟩


  -- Here we know that p and q are coprime
  simp at h_coprime
  let g := fun i ↦ x (i + 1) - x i
  let I := Finset.range n

  have {i : ℕ} : i ∈ I → i < n := by grind
  obtain ⟨s, hs, h_s_le_n⟩ := sum_bivalued I g (fun i a ↦ Or.symm (h₇ i (this a)))
  let r := n - s
  have h_eq_add : n = r + s := by grind
  have h_rp_eq_sq : r * p = s * q := by grind

  obtain ⟨k, hk⟩ := Nat.Coprime.dvd_of_dvd_mul_right h_coprime (Dvd.intro_left r h_rp_eq_sq)

  have h_s_pos : 0 < s := by
    by_contra
    simp at this
    have h_rp_zero : r * p = 0 := by
      rw [this, zero_mul] at h_rp_eq_sq
      exact h_rp_eq_sq
    have h_r_zero : r = 0 := by
      apply eq_zero_or_eq_zero_of_mul_eq_zero at h_rp_zero
      exact h_rp_zero.resolve_right (Nat.ne_zero_of_lt h₁)
    have h_n_zero : n = 0 := by
      rw [h_eq_add, h_r_zero, this, zero_add]
    exact Nat.ne_zero_of_lt h₃ h_n_zero

  have h_r_pos : 0 < r := by
    have h_sq_pos : 0 < s * q := mul_pos h_s_pos h₂
    have h_rp_pos : 0 < r * p := Nat.lt_of_lt_of_eq h_sq_pos (Eq.symm h_rp_eq_sq)
    exact Nat.pos_of_mul_pos_right h_rp_pos
  have h_k_pos : 0 < k := by grind only
  have h_k_gt_one : 1 < k := by
    by_contra
    have h_one : k = 1 := by linarith
    have h1: s = p := by simp [hk, h_one]
    have h2: r = q := by
      simp [h1, mul_comm] at h_rp_eq_sq
      exact h_rp_eq_sq.resolve_right (Nat.ne_zero_of_lt h₁)
    have h3: p + q = n := by linarith
    linarith

  have h_p_add_q_mul_k_eq_n : (p + q) * k = n := by
    rw [hk, mul_comm, mul_assoc] at h_rp_eq_sq
    have : r = k * q := Nat.eq_of_mul_eq_mul_left h₁ h_rp_eq_sq
    rw [mul_comm] at this
    simp [h_eq_add, hk, this, ←add_mul, add_comm]

  have h_k_dvd_n : k ∣ n := Dvd.intro_left (p + q) h_p_add_q_mul_k_eq_n
  obtain ⟨h, hh⟩ := h_k_dvd_n
  have h_pos : 0 < h := by grind only
  have h_lt_n : h < n := by rw [hh] ; exact lt_mul_left h_pos h_k_gt_one

  have h_h_eq_p_add_q : h = p + q := by
    rw [hh, mul_comm] at h_p_add_q_mul_k_eq_n
    apply mul_left_cancel₀ (Nat.ne_zero_of_lt h_k_pos) at h_p_add_q_mul_k_eq_n
    exact h_p_add_q_mul_k_eq_n.symm

  let d := fun i ↦ x (i + h) - x i
  have h_h_dvd_di : ∀ i ≤ n - h, ↑h ∣ d i := by
    intro i hi
    unfold d
    have : x (i + h) - x i = ∑ j ∈ Finset.Ico i (i + h), (x (j + 1) - x j) := by
      have hlt : i ≤ i + h := by omega
      rw [←h_tsum_i (i + h), ←h_tsum_i, sub_eq_iff_eq_add]
      conv_rhs =>
        rw [add_comm]
      rw [Finset.sum_range_add_sum_Ico (fun j ↦ x (j + 1) - x j) hlt]
    have : ∃t : ℕ, ∑ j ∈ Finset.Ico i (i + h), (x (j + 1) - x j) = t * p + (h - t) * (-q) := by
      have : ∀ j ∈ Finset.Ico i (i + h), x (j + 1) - x j = p ∨ x (j + 1) - x j = -q := by
        intro j hj
        have h_j_lt_n : j < n := by
          rw [Finset.mem_Ico] at hj
          omega
        exact h₇ j h_j_lt_n
      obtain ⟨t, ht⟩ := sum_bivalued (Finset.Ico i (i + h)) (fun j ↦ x (j + 1) - x j) this
      use t
      simp [ht]
    obtain ⟨t, ht⟩ := this
    rw [this, ht]
    have : (↑t : ℤ) * ↑p + (↑h - ↑t) * -↑q = (↑t - ↑q) * ↑h := by
      calc
        (↑t : ℤ) * ↑p + (↑h - ↑t) * -↑q = ↑t * (↑p + ↑q) - ↑h * ↑q := by grind
        _ = (↑t - ↑q) * ↑h := by rw [h_h_eq_p_add_q] ; grind
    rw [this]
    exact Int.dvd_mul_left (↑t - ↑q) ↑h

  have h_di_delta : ∀ i < n - h, d (i + 1) - d i ∈ { z : ℤ | z = 0 ∨ z = h ∨ z = -h } := by
    intro i hi
    unfold d
    have : d (i + 1) - d i = g (i + h) - g i := by
      unfold d
      grind only
    rw [this]
    have h₈ : ∀ i < n, g i = p ∨ g i = -q := h₇
    have h_gih := h₈ (i + h) (by omega)
    have h_gi := h₈ i (by omega)
    cases' h_gih with h_gihp h_gihq
    · cases' h_gi with h_gip h_giq
      · rw [h_gihp, h_gip]
        simp
      · rw [h_gihp, h_giq]
        simp [h_h_eq_p_add_q]
    · cases' h_gi with h_gip h_giq
      · rw [h_gihq, h_gip, ←neg_sub]
        simp [h_h_eq_p_add_q]
      · rw [h_gihq, h_giq]
        simp


  -- First, if there is any d i = 0, then this trivially gives the proof
  by_cases! h_di_zero : ∃i ≤ n - h, d i = 0
  · obtain ⟨i, hi, hdi⟩ := h_di_zero
    use i, i+h
    constructor
    · exact Nat.zero_le i
    constructor
    · exact (lt_add_iff_pos_right i).mpr h_pos
    constructor
    · omega
    constructor
    · grind only
    exact Eq.symm (Int.eq_of_sub_eq_zero hdi)


  -- Here we have ∀ i, d i ≠ 0. We complete the proof by contradiction
  by_contra
  -- Either all are positive or all negative. Otherwise we must have an i such that
  -- d i and d (i+1) have different signs and are multiples of h so that their absolute difference
  -- is at least 2h, which is a contradiction since the difference is in {0, h, -h} (due to h_di_delta)
  let I₂ := Finset.range (n - h + 1)
  have h_di_pos_or_neg : (∀ i ∈ I₂, 0 < d i) ∨ (∀ i ∈ I₂, d i < 0) := by
    by_contra h_pos_and_neg
    simp at h_pos_and_neg
    let s0 := (d 0).sign
    let I₃ := I₂.filter (fun j ↦ (d j).sign ≠ s0)
    have h_I3_nonempty : I₃.Nonempty := by
      obtain ⟨i, hi, h_di_sign⟩ := h_pos_and_neg.1
      obtain ⟨j, hj, h_dj_sign⟩ := h_pos_and_neg.2
      by_cases h_di_sign_eq_s0 : (d i).sign = s0
      · have : (d j).sign ≠ (d i).sign := by grind
        replace : (d j).sign ≠ s0 := by rw [h_di_sign_eq_s0] at this ; exact this
        replace : j ∈ I₃ := by
          exact Finset.mem_filter.mpr ⟨hj, this⟩
        exact I₃.nonempty_def.mpr (Exists.intro j this)
      · have : (d i).sign ≠ s0 := h_di_sign_eq_s0
        replace : i ∈ I₃ := by
          exact Finset.mem_filter.mpr ⟨hi, this⟩
        exact I₃.nonempty_def.mpr (Exists.intro i this)
    let t := I₃.min' h_I3_nonempty
    have h_t_pos : 0 < t := by
      by_contra h_t_zero
      have h_t_zero : t = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_not_gt h_t_zero)
      have h_t_in_I₃ : t ∈ I₃ := Finset.min'_mem I₃ h_I3_nonempty
      have : (d t).sign ≠ s0 := by
        simp at t
        exact (Finset.mem_filter.mp h_t_in_I₃).2
      rw [h_t_zero] at this
      exact Ne.elim this (by rfl)

    have h_diff_sgn : (d (t - 1)).sign ≠ (d t).sign := by
      have h_t_pred_not_in_I₃ : t - 1 ∉ I₃ := by
        by_contra h_in
        have h_t_min : t ≤ t - 1 := I₃.min'_le (t - 1) h_in
        exact Nat.not_le_of_lt (Nat.sub_one_lt_of_lt h_t_pos) h_t_min
      have h_t_pred_in_I₂ : t - 1 ∈ I₂ := by
        have : t ∈ I₃ := Finset.min'_mem I₃ h_I3_nonempty
        replace : t ∈ I₂ := Finset.mem_of_mem_filter t this
        replace : t < n - h + 1 := Finset.mem_range.mp this
        replace : t - 1 < n - h + 1:= Nat.sub_lt_of_lt this
        exact Finset.mem_range.mpr this
      have h_t_pred_sign : (d (t - 1)).sign = s0 := by
        simp at h_t_pred_not_in_I₃
        exact Classical.by_contradiction (fun h_contra ↦ h_t_pred_not_in_I₃ (Finset.mem_filter.mpr ⟨h_t_pred_in_I₂, h_contra⟩))
      have h_t_sign : (d t).sign ≠ s0 := by
        have h_t_in_I₃ : t ∈ I₃ := Finset.min'_mem I₃ h_I3_nonempty
        simp at h_t_in_I₃
        exact (Finset.mem_filter.mp h_t_in_I₃).2
      rw [← h_t_pred_sign] at h_t_sign
      exact h_t_sign.symm
    have h_t_in_I₃ : t ∈ I₃ := Finset.min'_mem I₃ h_I3_nonempty
    have h_t_lt_nh : t < n - h + 1 := Finset.mem_range.mp (Finset.mem_of_mem_filter t h_t_in_I₃)
    obtain ⟨v, hv⟩ := exists_eq_mul_left_of_dvd (h_h_dvd_di t (Nat.le_of_lt_succ h_t_lt_nh))
    obtain ⟨w, hw⟩ := exists_eq_mul_left_of_dvd (h_h_dvd_di (t-1) (by omega))
    have h_v_ne_zero : v ≠ 0 := (ne_zero_of_mul (h_di_zero t (Nat.le_of_lt_succ h_t_lt_nh)) hv).1
    have h_w_ne_zero : w ≠ 0 := (ne_zero_of_mul (h_di_zero (t-1) (by omega)) hw).1
    replace h_diff_sgn : v.sign ≠ w.sign := by
      have : (↑h : ℤ).sign = 1 := Int.sign_eq_one_of_pos (Int.natCast_pos.mpr h_pos)
      rw [hv, hw, Int.sign_mul, Int.sign_mul, this, mul_one, mul_one] at h_diff_sgn
      exact h_diff_sgn.symm
    have h_di_delta_t_minus_1 := h_di_delta (t - 1) (Nat.sub_lt_right_of_lt_add h_t_pos h_t_lt_nh)
    simp [Nat.sub_add_cancel h_t_pos] at h_di_delta_t_minus_1
    have : d t - d (t - 1) = (v - w) * ↑h := by
      rw [hv, hw, ←sub_mul]
    repeat rw [this] at h_di_delta_t_minus_1
    rcases h_di_delta_t_minus_1 with h_zero | h_eq_pos | h_eq_neg
    · have : v = w := by
        rw [mul_eq_zero] at h_zero
        cases' h_zero with h_1 h_zero
        · exact Int.eq_of_sub_eq_zero h_1
        · by_contra ; linarith
      exact Ne.elim h_diff_sgn (congrArg Int.sign this)
    · have : v - w = 1 := by
        nth_rw 2 [← Int.one_mul ↑h] at h_eq_pos
        exact mul_right_cancel₀ (Int.natCast_ne_zero_iff_pos.mpr h_pos) h_eq_pos
      exact Ne.elim (diff_ne_one_of_dist_gt_one (dist_gt_one_of_ne_sign h_diff_sgn h_v_ne_zero h_w_ne_zero)).1 this
    · have : w - v = 1 := by
        nth_rw 2 [← Int.one_mul ↑h] at h_eq_neg
        rw [← neg_eq_iff_eq_neg, ←neg_mul, neg_sub] at h_eq_neg
        exact mul_right_cancel₀ (Int.natCast_ne_zero_iff_pos.mpr h_pos) h_eq_neg
      exact Ne.elim (diff_ne_one_of_dist_gt_one (dist_gt_one_of_ne_sign h_diff_sgn.symm h_w_ne_zero h_v_ne_zero)).1 this

  let Ik := I₂.filter (fun i ↦ i ≤ n - h ∧ h ∣ i)
  have h_Ik_nonempty : Ik.Nonempty := by
    have h_dvd_0 : h ∣ 0 := by simp
    have h_zero_in_I : 0 ∈ I₂ := Finset.mem_range.mpr (Nat.zero_lt_succ (n - h))
    have h_mem_Ik : 0 ∈ Ik := by
      exact Finset.mem_filter.mpr ⟨h_zero_in_I, Nat.zero_le (n - h), h_dvd_0⟩
    use 0
  have h_di_pos_or_neg : (∀ i ∈ Ik, 0 < d i) ∨ (∀ i ∈ Ik, d i < 0) := by
    cases' h_di_pos_or_neg with h_pos h_neg
    · left ; intro i hi ; exact h_pos i (Finset.mem_of_mem_filter i hi)
    · right ; intro i hi ; exact h_neg i (Finset.mem_of_mem_filter i hi)
  have h_di_sum_eq_zero : ∑ i ∈ Ik, d i = 0 := by
    have hs₁: ∑ i ∈ Ik, d i = ∑ i ∈ Finset.range k, d (i * h) := by
      have : Ik = Finset.image (fun i ↦ i * h) (Finset.range k) := by
        ext j
        constructor
        · intro hj
          rw [Finset.mem_filter] at hj
          obtain ⟨m, hm⟩ := exists_eq_mul_left_of_dvd hj.2.2
          have : j < n := by grind only [= Finset.mem_range]
          have h_m_in_range : m < k := by
            rw [hh, hm] at this
            exact (Nat.mul_lt_mul_right h_pos).mp this
          exact Finset.mem_image.mpr ⟨m, Finset.mem_range.mpr h_m_in_range, hm.symm⟩
        · intro hj
          rw [Finset.mem_image] at hj
          obtain ⟨m, hm_range, hm_eq⟩ := hj
          rw [Finset.mem_filter]
          have : j ≤ n - h := by
            have : m < k := List.mem_range.mp hm_range
            have : m ≤ k - 1 := (Nat.le_sub_one_iff_lt h_k_pos).mpr this
            calc
              j = m * h := hm_eq.symm
              _ ≤ (k - 1) * h := (Nat.mul_le_mul_right_iff h_pos).mpr this
              _ = n - h := by rw [hh] ; exact Nat.sub_one_mul k h
          constructor
          · exact Finset.mem_range.mpr (by omega)
          · exact ⟨this, Dvd.intro_left m hm_eq⟩
      rw [this]
      exact Finset.sum_image (fun i hi j hj h_eq ↦ Nat.eq_of_mul_eq_mul_right h_pos h_eq)
    have hs₂: ∑ i ∈ Finset.range k, d (i * h) = x n - x 0 := by
      let f := fun i ↦ x (i * h)
      simp [d]
      have hf₁: ∀ i, x (i * h + h) = f (i + 1) := by
        intro i
        unfold f
        congr
        exact Eq.symm (Nat.succ_mul i h)
      have hf₂: ∀ i, x (i * h) = f i := by intro i ; rfl
      conv_lhs => arg 1 ; arg 2 ; intro j ; rw [hf₁ j]
      conv_lhs => arg 2 ; arg 2 ; intro j ; rw [hf₂ j]
      rw [← Finset.sum_sub_distrib (fun i ↦ f (i + 1)) f, Finset.sum_range_sub f]
      unfold f
      simp [hh]
    rw [hs₁, hs₂, h₅, h₆, sub_zero]

  rcases h_di_pos_or_neg with h_pos | h_neg
  · have := Finset.sum_pos h_pos h_Ik_nonempty
    exact this.ne h_di_sum_eq_zero.symm
  · have := Finset.sum_neg h_neg h_Ik_nonempty
    exact this.ne h_di_sum_eq_zero
termination_by p
decreasing_by
  rw [hp']
  exact (Nat.lt_mul_iff_one_lt_right (Nat.zero_lt_of_lt h₁')).mpr h_one_lt_w

end Imo1996P6
