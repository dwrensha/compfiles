/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.MeanInequalities

/-!
# USA Mathematical Olympiad 1998, Problem 3

Let a₀,a₁,...,aₙ be real numbers from the interval (0,π/2) such that

  tan(a₀ - π/4) + tan(a₁ - π/4) + ... + tan(aₙ - π/4) ≥ n - 1.

Prove that

  tan(a₀)tan(a₁)...tan(aₙ) ≥ nⁿ⁺¹.

-/

namespace Usa1998Q3
open BigOperators

theorem usa1998_q3
    (n : ℕ)
    (a : ℕ → ℝ)
    (ha : ∀ i, i < n + 1 → a i ∈ Set.Ioo 0 (Real.pi / 2))
    (hs : n - 1 ≤ ∑ i in Finset.range (n + 1), Real.tan (a i - (Real.pi / 4)))
    : Real.rpow n (n + 1) ≤ ∏ i in Finset.range (n + 1), Real.tan (a i) := by

  obtain h0 | h0 := eq_or_ne n 0
  · simp_all[h0]
    exact Real.tan_nonneg_of_nonneg_of_le_pi_div_two
            (le_of_lt ha.1)
            (le_of_lt ha.2)

  -- informal solution from artofproblemsolving.com
  --
  -- Let yᵢ = tan(aᵢ - π/4), where 0 ≤ i ≤ n.
  let y : ℕ → ℝ := λ i ↦ Real.tan (a i - Real.pi / 4)
  -- Then we have
  --  y₀ + y₁ + ... + yₙ ≥ n - 1
  have h1 : n - 1 ≤ ∑ i in Finset.range (n + 1), y i := hs

  --  1 + yᵢ ≥ ∑_{j ≠ i} (1 - yⱼ)
  have h2 : ∀ i, i < n + 1 →
      ∑ j in (Finset.range (n + 1)).erase i, (1 - y j) ≤ 1 + y i := by
    intros i hi
    have hi' : i ∈ Finset.range (n + 1) := Finset.mem_range.mpr hi
    rw[Finset.sum_erase_eq_sub hi']
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
               nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    linarith

  --  (1 + yᵢ)/n ≥ (1/n) ∑_{j ≠ i} (1 - yⱼ)
  have h3 : ∀ i, i < n + 1 →
      (1/(n:ℝ)) * ∑ j in (Finset.range (n + 1)).erase i, (1 - y j)
          ≤ (1 + y i)/n := by
    intros i hi
    have h2' := h2 i hi
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    rw[div_mul_eq_mul_div, one_mul]
    exact div_le_div_of_le hn (h2 i hi)

  --
  -- Then, by AM-GM,
  -- (1/n) ∑_{j ≠ i} (1 - yⱼ) ≥ ∏_{j ≠ i} (1 - yⱼ)^{1/n}
  have h4 : ∀ i, i < n + 1 →
     ∏ j in (Finset.range (n + 1)).erase i, (1 - y i)^(1 / (n : ℝ)) ≤
     (1/(n:ℝ)) * ∑ j in (Finset.range (n + 1)).erase i, (1 - y j) := by
    intros i hi
    have hi' : i ∈ Finset.range (n + 1) := Finset.mem_range.mpr hi
    let w : ℕ → ℝ := fun i ↦ 1 / (n:ℝ)
    have hn : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h0
    have hw' : ∑ j in (Finset.range (n + 1)).erase i, w i = 1 := by
       simp[Finset.card_erase_of_mem hi']; field_simp
    have hw : ∀ j ∈ (Finset.range (n + 1)).erase i, 0 ≤ w j := by
      intros j hj
      simp only [one_div, inv_nonneg, Nat.cast_nonneg]
    have hz : ∀ j ∈ (Finset.range (n + 1)).erase i, 0 ≤ 1 - y j := by
      intros j hj
      rw[Finset.mem_erase, Finset.mem_range] at hj
      have haj := ha j hj.2
      rw[Set.mem_Ioo] at haj
      rw[← Real.tan_pi_div_four]

      let y' x := Real.tan (x - Real.pi / 4)
      have h4 : Real.tan (Real.pi / 4) = y' (Real.pi / 2) := by
         dsimp
         have h5 : Real.pi / 2 - Real.pi / 4 = Real.pi / 4 := by field_simp; ring
         rw[h5]
      have h4' : y j = y' (a j) := rfl
      rw[h4, h4']
      let y1 x := x - Real.pi / 4
      have h5 : StrictMonoOn y1 (Set.Icc 0 (Real.pi / 2)) := by
        intros a ha b hb hab
        exact sub_lt_sub_right hab _

      have h10 : Set.Icc (-Real.pi / 4) (Real.pi / 4) ⊆
               Set.Ioo (-(Real.pi / 2)) (Real.pi/2) := by
        intros a ha; exact ⟨by linarith[ha.1], by linarith[ha.2]⟩

      have h6 : StrictMonoOn y' (Set.Icc 0 (Real.pi / 2)) := by
        apply StrictMonoOn.comp (g := Real.tan) (f := y1)
                (t := (Set.Icc (-Real.pi / 4) (Real.pi / 4)))
                (StrictMonoOn.mono Real.strictMonoOn_tan h10)
                h5
        · intro a ha
          obtain ⟨ha1, ha2⟩ := ha
          constructor
          · dsimp; linarith
          · dsimp; linarith
      have h11 : Real.pi / 2 ∈ Set.Icc 0 (Real.pi / 2) := by
        constructor
        · exact le_of_lt Real.pi_div_two_pos
        · exact Eq.le rfl
      have h8 : y' (a j) ≤ y' (Real.pi / 2) := by
        apply le_of_lt
        have h9 : a j ∈ Set.Icc 0 (Real.pi / 2) := by
          constructor
          · exact le_of_lt haj.1
          · exact le_of_lt haj.2
        exact h6 h9 h11 haj.2
      exact Iff.mpr sub_nonneg h8
    have := Real.geom_mean_le_arith_mean_weighted
              ((Finset.range (n + 1)).erase i)
              w (λ j ↦ 1 - y j)
              hw hw' hz
    sorry

  -- (1 + yᵢ)/n ≥ ∏_{j ≠ i} (1 - yⱼ)^{1/n}
  -- ∏ᵢ(1 + yᵢ)/n ≥ ∏ᵢ∏_{j ≠ i} (1 - yⱼ)^{1/n}
  -- ... a bunch more steps...
  sorry

#check Finset.card_erase_of_mem
#check Real.geom_mean_le_arith_mean_weighted
