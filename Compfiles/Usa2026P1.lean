/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Liao
-/

import Mathlib.Tactic
import Compfiles.Usa1981P5

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# USA Mathematical Olympiad 2026, Problem 1

Fix an integer n ≥ 2. For which real numbers x is
  ⌊nx⌋ - ∑_{k=1}^n ⌊kx⌋/k
maximal, and what is the maximal value that this expression can take?
-/

namespace Usa2026P1

open Real
open Finset

noncomputable def f (n : ℕ) (x : ℝ) : ℝ :=
  (⌊(n : ℝ) * x⌋ : ℝ) - ∑ k ∈ Icc 1 n, (⌊(k : ℝ) * x⌋ : ℝ) / (k : ℝ)

noncomputable determine solution_value : ℕ → ℝ := fun n ↦
  ∑ k ∈ Icc 2 n, (1 : ℝ) / (k : ℝ)

snip begin

/-
Mathematical solution sketch by Evan Chen: https://web.evanchen.cc/twitch/Ep177-USAMO-2026-1-Solution.pdf
-/

lemma f_periodic (n : ℕ) (x : ℝ) : f n (x + 1) = f n x := by
  unfold f
  simp_rw [mul_add, mul_one]

  have h_floor : ∀ m : ℕ, ⌊(m : ℝ) * x + (m : ℝ)⌋ = ⌊(m : ℝ) * x⌋ + (m : ℤ) := by
    intro m
    exact Int.floor_add_natCast (↑m * x) m

  have h2 : ∀ k ∈ Icc 1 n, (⌊(k : ℝ) * x + (k : ℝ)⌋ : ℝ) / (k : ℝ) = ((⌊(k : ℝ) * x⌋ : ℝ) / (k : ℝ)) + 1 := by
    intro k hk
    rw [h_floor k]
    push_cast
    have hk_pos : (k : ℝ) ≠ 0 := by
      have : 1 ≤ k := (mem_Icc.mp hk).1
      positivity
    rw [add_div, div_self hk_pos]

  rw [h_floor n]
  have h3 : ∑ k ∈ Icc 1 n, (⌊(k : ℝ) * x + (k : ℝ)⌋ : ℝ) / (k : ℝ) =
            (∑ k ∈ Icc 1 n, (⌊(k : ℝ) * x⌋ : ℝ) / (k : ℝ)) + (n : ℝ) := by
    rw [sum_congr rfl h2, sum_add_distrib]
    simp

  rw [h3]
  push_cast
  ring

noncomputable def T (n : ℕ) (y : ℝ) : ℝ :=
  ((⌈(n : ℝ) * y⌉ : ℤ) - 1 : ℝ) - ∑ k ∈ Icc 1 n, (((⌈(k : ℝ) * y⌉ : ℤ) - 1 : ℤ) : ℝ) / (k : ℝ)

lemma f_rewrite (n : ℕ) (hn : 1 ≤ n) (y : ℝ) : f n (1 - y) = solution_value n - T n y := by
  unfold f solution_value T
  simp_rw [mul_sub, mul_one]

  have h_floor : ∀ m : ℕ, ⌊(m : ℝ) - (m : ℝ) * y⌋ = (m : ℤ) - ⌈(m : ℝ) * y⌉ := by
    intro m
    have h_eq : (m : ℝ) - (m : ℝ) * y = -((m : ℝ) * y) + ((m : ℤ) : ℝ) := by
      push_cast
      ring
    rw [h_eq, Int.floor_add_intCast, Int.floor_neg]
    ring

  have h_f_terms : ∀ k ∈ Icc 1 n, (⌊(k : ℝ) - (k : ℝ) * y⌋ : ℝ) / (k : ℝ) =
                                  1 - (⌈(k : ℝ) * y⌉ : ℝ) / (k : ℝ) := by
    intro k hk
    rw [h_floor k]
    push_cast
    have hk_pos : (k : ℝ) ≠ 0 := by
      have : 1 ≤ k := (mem_Icc.mp hk).1
      positivity
    rw [sub_div, div_self hk_pos]

  have h_T_terms : ∀ k ∈ Icc 1 n, (((⌈(k : ℝ) * y⌉ : ℤ) - 1 : ℤ) : ℝ) / (k : ℝ) =
                                  ((⌈(k : ℝ) * y⌉ : ℝ) / (k : ℝ)) - 1 / (k : ℝ) := by
    intro k _
    push_cast
    rw [sub_div]

  rw [h_floor n]
  rw [sum_congr rfl h_f_terms]
  rw [sum_congr rfl h_T_terms]
  rw [sum_sub_distrib, sum_sub_distrib]

  have h_sum_ones : ∑ k ∈ Icc 1 n, (1 : ℝ) = (n : ℝ) := by
    simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one]
  rw [h_sum_ones]

  have h_harmonic : ∑ k ∈ Icc 1 n, (1 : ℝ) / (k : ℝ) = 1 + ∑ k ∈ Icc 2 n, (1 : ℝ) / (k : ℝ) := by
    have h_Icc : Icc 1 n = insert 1 (Icc 2 n) := by
      ext x
      simp only [mem_Icc, mem_insert]
      omega
    rw [h_Icc, sum_insert (by simp [mem_Icc])]
    norm_num

  rw [h_harmonic]
  push_cast
  ring

lemma T_eq_zero_of_small_y (n : ℕ) (y : ℝ) (hn : 2 ≤ n) (hy1 : 0 < y) (hy2 : y ≤ 1 / (n : ℝ)) :
  T n y = 0 := by
  unfold T
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have h_ceil : ∀ k ∈ Icc 1 n, ⌈(k : ℝ) * y⌉ = 1 := by
    intro k hk
    have hk1 : 1 ≤ k := (mem_Icc.mp hk).1
    have hkn : k ≤ n := (mem_Icc.mp hk).2
    have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (by omega)
    have hk_le_n : (k : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hkn
    have h1 : 0 < (k : ℝ) * y := mul_pos hk_pos hy1
    have h2 : (k : ℝ) * y ≤ 1 := by
      calc (k : ℝ) * y ≤ (k : ℝ) * (1 / (n : ℝ)) := mul_le_mul_of_nonneg_left hy2 (le_of_lt hk_pos)
        _ = (k : ℝ) / (n : ℝ) := mul_one_div _ _
        _ ≤ 1 := (div_le_one hn_pos).mpr hk_le_n
    apply Int.ceil_eq_iff.mpr
    constructor
    · push_cast
      linarith
    · push_cast
      exact h2

  have hn_in : n ∈ Icc 1 n := mem_Icc.mpr ⟨by omega, le_rfl⟩
  rw [h_ceil n hn_in]
  have h_sum_zero : ∑ k ∈ Icc 1 n, (((⌈(k : ℝ) * y⌉ : ℤ) - 1 : ℤ) : ℝ) / (k : ℝ) = 0 := by
    apply sum_eq_zero
    intro k hk
    rw [h_ceil k hk]
    norm_num

  rw [h_sum_zero]
  norm_num

lemma core_sum_bound (n p : ℕ) (hp1 : 1 ≤ p) (hpn : p < n) :
  ∑ k ∈ Icc 1 n, (((⌈(k : ℝ) * ((p + 1 : ℝ) / (n : ℝ))⌉ : ℤ) - 1 : ℤ) : ℝ) / (k : ℝ) ≤ (p : ℝ) := by

  let x : ℝ := ((p + 1 : ℝ) / (n : ℝ)) - (1 : ℝ) / (2 * (n : ℝ)^2)
  have h_1981 := Usa1981P5.usa1981_p5 x n

  have h_right : (⌊(n : ℝ) * x⌋ : ℝ) = (p : ℝ) := by
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
    have hn_ne_zero : (n : ℝ) ≠ 0 := ne_of_gt hn_pos

    have h_inside : (n : ℝ) * x = (p : ℝ) + 1 - 1 / (2 * (n : ℝ)) := by
      dsimp [x]
      calc (n : ℝ) * (((p + 1 : ℝ) / (n : ℝ)) - 1 / (2 * (n : ℝ)^2))
        _ = (n : ℝ) * ((p + 1 : ℝ) / (n : ℝ)) - (n : ℝ) * (1 / (2 * (n : ℝ)^2)) := mul_sub _ _ _
        _ = (p + 1 : ℝ) - (n : ℝ) / (2 * (n : ℝ)^2) := by
          congr 1
          · exact mul_div_cancel₀ _ hn_ne_zero
          · exact mul_one_div (n : ℝ) _
        _ = (p : ℝ) + 1 - 1 / (2 * (n : ℝ)) := by
          congr 1
          have h_den : 2 * (n : ℝ)^2 = (n : ℝ) * (2 * (n : ℝ)) := by ring
          rw [h_den, div_mul_eq_div_div, div_self hn_ne_zero, one_div]

    have h_lower : (p : ℝ) ≤ (n : ℝ) * x := by
      rw [h_inside]
      have h_n_ge_2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 2 ≤ n)
      have h_pos : 0 < 2 * (n : ℝ) := by linarith
      have h_bound : 1 / (2 * (n : ℝ)) ≤ 1 := by
        rw [div_le_iff₀ h_pos]
        linarith
      linarith

    have h_upper : (n : ℝ) * x < (p : ℝ) + 1 := by
      rw [h_inside]
      have h_pos : 0 < 1 / (2 * (n : ℝ)) := by positivity
      linarith

    have h_floor : ⌊(n : ℝ) * x⌋ = (p : ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor
      · exact_mod_cast h_lower
      · exact_mod_cast h_upper

    rw [h_floor]
    push_cast
    rfl

  have h_pointwise : ∀ k ∈ Icc 1 n,
    (((⌈(k : ℝ) * ((p + 1 : ℝ) / (n : ℝ))⌉ : ℤ) - 1 : ℤ) : ℝ) ≤ (⌊(k : ℝ) * x⌋ : ℝ) := by
    intro k hk
    have hn_pos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
    have hk_pos : 0 < (k : ℝ) := by
      have : 1 ≤ k := (mem_Icc.mp hk).1
      positivity
    have hkn : (k : ℝ) ≤ (n : ℝ) := by
      have : k ≤ n := (mem_Icc.mp hk).2
      exact_mod_cast this

    let y : ℝ := (k : ℝ) * ((p + 1 : ℝ) / (n : ℝ))
    let δ : ℝ := (k : ℝ) / (2 * (n : ℝ)^2)

    have h_kx : (k : ℝ) * x = y - δ := by
      dsimp [x, y, δ]
      rw [mul_sub]
      congr 1
      exact mul_one_div (k : ℝ) (2 * (n : ℝ)^2)

    rw [h_kx]

    have h_floor_equiv : (((⌈y⌉ : ℤ) - 1 : ℤ) : ℝ) ≤ (⌊y - δ⌋ : ℝ) ↔
                         (((⌈y⌉ : ℤ) - 1 : ℤ) : ℝ) ≤ y - δ := by
      exact Iff.trans Int.cast_le Int.le_floor

    apply h_floor_equiv.mpr

    have h_ineq : (((⌈y⌉ : ℤ) - 1 : ℤ) : ℝ) ≤ y - δ := by
      have hδ_le : δ ≤ 1 / (n : ℝ) := by
        have h_nonneg : 0 ≤ 2 * (n : ℝ) ^ 2 := by positivity
        have h_le : (k : ℝ) ≤ (n : ℝ) := hkn
        have h_div_le : (k : ℝ) / (2 * (n : ℝ) ^ 2) ≤ (n : ℝ) / (2 * (n : ℝ) ^ 2) :=
          div_le_div_of_nonneg_right h_le h_nonneg
        calc
          δ = (k : ℝ) / (2 * (n : ℝ) ^ 2) := rfl
          _ ≤ (n : ℝ) / (2 * (n : ℝ) ^ 2) := h_div_le
          _ = 1 / (2 * (n : ℝ)) := by
            field_simp [hn_ne]
          _ ≤ 1 / (n : ℝ) := by
            apply one_div_le_one_div_of_le hn_pos
            linarith

      by_cases hy_int : y = (⌊y⌋ : ℝ)
      · have h_ceil : ⌈y⌉ = ⌊y⌋ := by
          nth_rw 1 [hy_int]
          exact Int.ceil_intCast ⌊y⌋
        have hδ_one : δ ≤ 1 := by
          calc δ ≤ 1 / (n : ℝ) := hδ_le
            _ ≤ 1 := by
              rw [div_le_one hn_pos]
              exact_mod_cast (by omega : 1 ≤ n)
        have : (((⌈y⌉ : ℤ) - 1 : ℤ) : ℝ) = y - 1 := by
          rw [h_ceil]; push_cast; linarith [hy_int]
        linarith
      · have h_fract_pos : 0 < Int.fract y := by
          rw [Int.fract_pos]
          intro hfr
          exact hy_int hfr
        have h_frac_bound : 1 / (n : ℝ) ≤ Int.fract y := by
          have h_nfr_pos : 0 < (n : ℝ) * Int.fract y := mul_pos hn_pos h_fract_pos
          have h_ny_eq : (n : ℝ) * y = ((k * (p + 1) : ℕ) : ℝ) := by
            dsimp [y]
            rw [mul_left_comm]
            rw [mul_div_cancel₀ _ hn_ne]
            push_cast; ring
          have h_z_eq : ((((k * (p + 1) : ℕ) : ℤ) - (n : ℤ) * ⌊y⌋) : ℝ) = (n : ℝ) * Int.fract y := by
            have : Int.fract y = y - ↑⌊y⌋ := rfl
            push_cast
            rw [this, mul_sub, h_ny_eq]
            push_cast; ring
          have h_int_ge_one : (1 : ℤ) ≤ (((k * (p + 1) : ℕ) : ℤ) - (n : ℤ) * ⌊y⌋) := by
            have : (0 : ℝ) < ((((k * (p + 1) : ℕ) : ℤ) - (n : ℤ) * ⌊y⌋) : ℝ) :=
              h_z_eq.symm ▸ h_nfr_pos
            exact_mod_cast this
          rw [div_le_iff₀ hn_pos]
          have : (1 : ℝ) ≤ (n : ℝ) * Int.fract y := by
            calc (1 : ℝ) ≤ ((((k * (p + 1) : ℕ) : ℤ) - (n : ℤ) * ⌊y⌋) : ℝ) := by
                    exact_mod_cast h_int_ge_one
              _ = (n : ℝ) * Int.fract y := h_z_eq
          linarith [mul_comm (Int.fract y) (n : ℝ)]
        have h_ceil : ⌈y⌉ = ⌊y⌋ + 1 := by
          rw [Int.ceil_eq_floor_add_one_iff_notMem]
          intro hy_mem
          rcases hy_mem with ⟨z, hz⟩
          have : y = (⌊y⌋ : ℝ) := by
            rw [← hz, Int.floor_intCast]
          exact hy_int this
        have h_eq : (((⌈y⌉ : ℤ) - 1 : ℤ) : ℝ) = y - Int.fract y := by
          rw [h_ceil]
          have : Int.fract y = y - ⌊y⌋ := rfl
          rw [this]
          push_cast
          ring
        rw [h_eq]
        linarith [h_frac_bound, hδ_le]
    exact h_ineq

  have h_frac_le : ∀ k ∈ Icc 1 n,
    (((⌈(k : ℝ) * ((p + 1 : ℝ) / (n : ℝ))⌉ : ℤ) - 1 : ℤ) : ℝ) / (k : ℝ) ≤ (⌊(k : ℝ) * x⌋ : ℝ) / (k : ℝ) := by
    intro k hk
    apply div_le_div_of_nonneg_right (h_pointwise k hk)
    have : 1 ≤ k := (mem_Icc.mp hk).1
    positivity

  calc
    ∑ k ∈ Icc 1 n, (((⌈(k : ℝ) * ((p + 1 : ℝ) / (n : ℝ))⌉ : ℤ) - 1 : ℤ) : ℝ) / (k : ℝ)
      ≤ ∑ k ∈ Icc 1 n, (⌊(k : ℝ) * x⌋ : ℝ) / (k : ℝ) := sum_le_sum h_frac_le
    _ ≤ (⌊(n : ℝ) * x⌋ : ℝ) := h_1981
    _ = (p : ℝ) := h_right

lemma T_nonneg (n : ℕ) (y : ℝ) (hn : 2 ≤ n) (hy1 : 0 < y) (hy2 : y ≤ 1) :
  0 ≤ T n y := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  set p_int := ⌈(n : ℝ) * y⌉ - 1
  have hp_ge_zero : 0 ≤ p_int := by
    have : (0 : ℝ) < (n : ℝ) * y := mul_pos hn_pos hy1
    have h_ceil : 1 ≤ ⌈(n : ℝ) * y⌉ := Int.ceil_pos.mpr this
    exact sub_nonneg.mpr h_ceil
  by_cases h_p_zero : p_int = 0
  · have h_ceil_one : ⌈(n : ℝ) * y⌉ = 1 := by linarith
    have h_ny_le_1 : (n : ℝ) * y ≤ 1 := by
      have h_ceil_le_1 : ⌈(n : ℝ) * y⌉ ≤ (1 : ℤ) := by omega
      exact_mod_cast Int.ceil_le.mp h_ceil_le_1
    have hy_le_1_n : y ≤ 1 / (n : ℝ) := by
      rw [le_div_iff₀ hn_pos]
      linarith
    rw [T_eq_zero_of_small_y n y hn hy1 hy_le_1_n]
  · have ⟨p, hp_eq⟩ : ∃ p : ℕ, (p : ℤ) = p_int := by
      have h1 : 0 ≤ p_int := hp_ge_zero
      exact ⟨p_int.toNat, Int.toNat_of_nonneg h1⟩

    have hp_real : (p : ℝ) = (((⌈(n : ℝ) * y⌉ : ℤ) - 1 : ℤ) : ℝ) := by
      have : (p : ℤ) = ((⌈(n : ℝ) * y⌉ : ℤ) - 1 : ℤ) := hp_eq
      exact_mod_cast this

    have h_ny_le_p1 : (n : ℝ) * y ≤ (p + 1 : ℝ) := by
      have : ⌈(n : ℝ) * y⌉ = (p : ℤ) + 1 := by linarith
      have h2 : (n : ℝ) * y ≤ (⌈(n : ℝ) * y⌉ : ℝ) := Int.le_ceil ((n : ℝ) * y)
      rw [this] at h2
      exact_mod_cast h2

    have hy_le_frac : y ≤ (p + 1 : ℝ) / (n : ℝ) := by
      rw [le_div_iff₀ hn_pos]
      linarith

    have hpn : p < n := by
      have h_ceil_le : ⌈(n : ℝ) * y⌉ ≤ (n : ℤ) := by
        apply Int.ceil_le.mpr
        have : (n : ℝ) * y ≤ (n : ℝ) * 1 := mul_le_mul_of_nonneg_left hy2 (le_of_lt hn_pos)
        rw [mul_one] at this
        exact_mod_cast this
      have : p_int ≤ (n : ℤ) - 1 := sub_le_sub_right h_ceil_le 1
      have h2 : (p : ℤ) < (n : ℤ) := by linarith
      exact_mod_cast h2

    have hp1 : 1 ≤ p := by
      have h1 : 0 ≤ p_int := hp_ge_zero
      have h2 : p_int ≠ 0 := h_p_zero
      have h3 : 0 < p_int := lt_of_le_of_ne h1 h2.symm
      have h4 : 1 ≤ (p : ℤ) := by omega
      exact_mod_cast h4

    have h_T_eq : T n y = (p : ℝ) - ∑ k ∈ Icc 1 n, (((⌈(k : ℝ) * y⌉ : ℤ) - 1 : ℤ) : ℝ) / (k : ℝ) := by
      unfold T
      have h_cast : ((⌈(n : ℝ) * y⌉ : ℤ) - 1 : ℝ) = (((⌈(n : ℝ) * y⌉ : ℤ) - 1 : ℤ) : ℝ) := by push_cast; rfl
      rw [h_cast, ← hp_real]

    have h_sum_le : ∑ k ∈ Icc 1 n, (((⌈(k : ℝ) * y⌉ : ℤ) - 1 : ℤ) : ℝ) / (k : ℝ) ≤ (p : ℝ) := by
      have h_term_le : ∀ k ∈ Icc 1 n, (((⌈(k : ℝ) * y⌉ : ℤ) - 1 : ℤ) : ℝ) / (k : ℝ) ≤ (((⌈(k : ℝ) * ((p + 1 : ℝ) / (n : ℝ))⌉ : ℤ) - 1 : ℤ) : ℝ) / (k : ℝ) := by
        intro k hk
        have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (by have := (mem_Icc.mp hk).1; omega)
        apply div_le_div_of_nonneg_right _ (le_of_lt hk_pos)
        apply Int.cast_le.mpr
        apply sub_le_sub_right
        apply Int.ceil_mono
        exact mul_le_mul_of_nonneg_left hy_le_frac (le_of_lt hk_pos)
      calc
        ∑ k ∈ Icc 1 n, (((⌈(k : ℝ) * y⌉ : ℤ) - 1 : ℤ) : ℝ) / (k : ℝ)
          ≤ ∑ k ∈ Icc 1 n, (((⌈(k : ℝ) * ((p + 1 : ℝ) / (n : ℝ))⌉ : ℤ) - 1 : ℤ) : ℝ) / (k : ℝ) := sum_le_sum h_term_le
        _ ≤ (p : ℝ) := core_sum_bound n p hp1 hpn

    rw [h_T_eq]
    exact sub_nonneg.mpr h_sum_le

snip end

problem usa2026_p1 (n : ℕ) (hn : 2 ≤ n) :
  (∀ x : ℝ, f n x ≤ solution_value n) ∧
  (∃ x : ℝ, f n x = solution_value n) := by
  constructor
  · intro x
    let y := 1 - Int.fract x
    have hy1 : 0 < y := sub_pos.mpr (Int.fract_lt_one x)
    have hy2 : y ≤ 1 := sub_le_self 1 (Int.fract_nonneg x)

    have h_fx_eq : f n x = f n (1 - y) := by
      have h_sub : 1 - y = Int.fract x := by ring
      rw [h_sub]
      unfold f

      have h_floor : ∀ m : ℕ, ⌊(m : ℝ) * x⌋ = ⌊(m : ℝ) * Int.fract x⌋ + (m : ℤ) * ⌊x⌋ := by
        intro m
        have h_eq : (m : ℝ) * x = (m : ℝ) * Int.fract x + ((m : ℤ) * ⌊x⌋ : ℝ) := by
          have h_fract_def : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
          rw [h_fract_def]
          push_cast
          ring
        rw [h_eq]
        rw [← Int.cast_mul]
        rw [Int.floor_add_intCast]

      have h_sum : ∑ k ∈ Icc 1 n, (⌊(k : ℝ) * x⌋ : ℝ) / (k : ℝ) =
                   ∑ k ∈ Icc 1 n, ((⌊(k : ℝ) * Int.fract x⌋ : ℝ) / (k : ℝ) + (⌊x⌋ : ℝ)) := by
        apply sum_congr rfl
        intro k hk
        rw [h_floor k]
        push_cast
        have hk_pos : (k : ℝ) ≠ 0 := by
          have : 1 ≤ k := (mem_Icc.mp hk).1
          positivity
        rw [add_div, mul_div_cancel_left₀ _ hk_pos]

      rw [h_floor n, h_sum, sum_add_distrib]
      have h_sum_const : ∑ k ∈ Icc 1 n, (⌊x⌋ : ℝ) = (n : ℝ) * (⌊x⌋ : ℝ) := by
        simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      rw [h_sum_const]
      push_cast
      ring

    have hn_ge_1 : 1 ≤ n := by omega
    rw [h_fx_eq, f_rewrite n hn_ge_1 y]
    have h_T_nonneg : 0 ≤ T n y := T_nonneg n y hn hy1 hy2
    linarith

  · use 1 - 1 / (n : ℝ)
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
    have hn_ge_1 : 1 ≤ n := by omega
    have hy1 : 0 < 1 / (n : ℝ) := one_div_pos.mpr hn_pos
    have hy2 : 1 / (n : ℝ) ≤ 1 / (n : ℝ) := le_rfl

    rw [f_rewrite n hn_ge_1 (1 / (n : ℝ))]
    have hT_zero : T n (1 / (n : ℝ)) = 0 := T_eq_zero_of_small_y n (1 / (n : ℝ)) hn hy1 hy2
    rw [hT_zero, sub_zero]

end Usa2026P1
