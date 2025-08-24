/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# USA Mathematical Olympiad 1993, Problem 3

Consider functions f : [0,1] → ℝ which satisfy

  (i)   f(x) ≥ 0 for all x ∈ [0,1]
  (ii)  f(1) = 1
  (iii) f(x) + f(y) ≤ f (x + y) whenever x, y and x + y are all in [0,1].

Determine the smallest constant c such that

       f(x) ≤ cx

for every function satisfying (i) - (iii) and every x ∈ [0,1].
-/

namespace Usa1993P3

snip begin

-- This lemma was proved automatically by Kimina-Prover 72B
theorem lemma1 (c1 : ℝ) :
  let f := fun x : (Set.Icc (0:ℝ) 1) ↦ if (x:ℝ) ≤ 1 / 2 then 0 else 1;
  (∀ (a : ℝ) (ha : 0 ≤ a ∧ a ≤ 1), f ⟨a, ha⟩ ≤ c1 * a) →
    (∀ (x : ↑(Set.Icc 0 1)), 0 ≤ f x) →
      f 1 = 1 → (∀ (x y : ↑(Set.Icc 0 1)) (h : (x:ℝ) + (y:ℝ) ∈ Set.Icc 0 1), f x + f y ≤ f ⟨↑x + ↑y, h⟩) → 2 ≤ c1 := by
  intro f h1 h2 h3 h4
  by_contra h
  push_neg at h
  have hc1 : c1 ≥ 0 := by
    have h1' := h1 (1 / 2 : ℝ) (by norm_num)
    have h5 : f ⟨(1 / 2 : ℝ), by norm_num⟩ = (0 : ℝ) := by
      simp [f]
    have h6 : (0 : ℝ) ≤ c1 * (1 / 2 : ℝ) := by
      have h7 : f ⟨(1 / 2 : ℝ), by norm_num⟩ ≤ c1 * (1 / 2 : ℝ) := by
        simpa using h1'
      rw [h5] at h7
      exact h7
    linarith
  have h9 : ∃ a : ℝ, a > (1 / 2 : ℝ) ∧ a ≤ (1 : ℝ) ∧ 1 > c1 * a := by
    use (1 + (2 - c1) / 4) / 2
    constructor
    · -- Show a > 1/2
      linarith
    constructor
    · -- Show a ≤ 1
      linarith
    · -- Show 1 > c1 * a
      linarith [sq_nonneg (c1 - 1), sq_nonneg ((1 + (2 - c1) / 4) / 2 - 1 / 2), hc1]
  rcases h9 with ⟨a, ha1, ha2, h10⟩
  have h1' := h1 a ⟨by linarith, ha2⟩
  have h5 : f ⟨a, ⟨by linarith, ha2⟩⟩ = 1 := by
    simp only [one_div, ite_eq_right_iff, zero_ne_one, imp_false, not_le, f]
    linarith
  order

private lemma dyadicBracket
    (x : ℝ) (hx0 : 0 < x) (hxhalf : x ≤ (1 : ℝ)/2) :
    ∃ m : ℕ, (1 : ℝ) / (2 : ℝ)^(m+1) < x ∧ x ≤ 1 / (2 : ℝ)^m := by
  obtain ⟨m, hm1, hm2⟩ :=
    exists_nat_pow_near_of_lt_one hx0 (by grind) (show 0 < (1:ℝ)/2 by norm_num) (by norm_num)
  use m
  refine ⟨?_, ?_⟩
  · field_simp at hm1
    exact hm1
  · field_simp at hm2
    exact hm2

/-
This lemma was proved by GPT5, with some help from dwrensha to fix
up some errors.
-/
theorem lemma2 (f : ↑(Set.Icc 0 1) → ℝ) (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 1)
    (h1 : ∀ (x : ↑(Set.Icc 0 1)), 0 ≤ f x) (h2 : f 1 = 1)
    (h3 : ∀ (x y : ↑(Set.Icc 0 1)) (h : x.val + y.val ∈ Set.Icc 0 1),
               f x + f y ≤ f ⟨x.val + y.val, h⟩)
    (h4 : ∀ (x : ↑(Set.Icc (0:ℝ) 1)), 1 - x.val ∈ Set.Icc 0 1)
    (h5 : ∀ (x : ↑(Set.Icc (0:ℝ) 1)), f x + f ⟨1 - x.val, h4 x⟩ ≤ 1)
    (h6 : ∀ (x : ↑(Set.Icc (0:ℝ) 1)), f x ≤ 1)
    (h8 : ∀ n : ℕ, ∀ x : Set.Icc (0:ℝ) (1/2^n), 2^n * (x : ℝ) ∈ Set.Icc (0:ℝ) 1)
    : f ⟨x, hx⟩ ≤ 2 * x := by
  classical
  -- f(0) = 0
  have f0 : f ⟨0, by simp [Set.mem_Icc]⟩ = 0 := by
    have := h5 (1 : ↑(Set.Icc (0 : ℝ) 1))
    have : 1 + f ⟨0, by simp [Set.mem_Icc]⟩ ≤ 1 := by simpa [h2, sub_self] using this
    have h0le : f ⟨0, by simp [Set.mem_Icc]⟩ ≤ 0 := by linarith
    have h0ge : 0 ≤ f ⟨0, by simp [Set.mem_Icc]⟩ := h1 ⟨0, by simp [Set.mem_Icc]⟩
    exact le_antisymm h0le (by simpa using h0ge)

  by_cases hx0 : x = 0
  · subst hx0; simp [mul_zero]; exact le_of_eq f0

  have hxpos : 0 < x := lt_of_le_of_ne' hx.1 hx0

  -- Large x: x ≥ 1/2 ⇒ f(x) ≤ 1 ≤ 2x
  by_cases hxhalf : x ≤ (1 : ℝ)/2
  · -- Small x: use dyadic doubling throughout (this is the part simplified by h8).
    -- Pick m with 2^{-(m+1)} < x ≤ 2^{-m}.
    obtain ⟨m, hx_lower, hx_upper⟩ := dyadicBracket x hxpos hxhalf

    -- For k ≤ m we have x ≤ 1 / 2^k.
    have hx_le_k : ∀ {k}, k ≤ m → x ≤ 1 / (2 : ℝ)^k := by
      intro k hk
      -- since k ≤ m, 2^k ≤ 2^m and thus 1/2^m ≤ 1/2^k
      have : (1 : ℝ) / (2 : ℝ)^m ≤ 1 / (2 : ℝ)^k := by
        -- monotone of (n ↦ (2^n)) with base ≥ 1
        have hk' : (2 : ℝ)^k ≤ (2 : ℝ)^m := by
          have : (1 : ℝ) ≤ (2 : ℝ) := by norm_num
          exact pow_le_pow_right₀ this hk
        have hpos : 0 < (2 : ℝ)^k := by simp
        exact one_div_le_one_div_of_le hpos hk'
      exact hx_upper.trans this

    -- Every 2^k x is in [0,1], by h8.
    have mem_pow (k : ℕ) (hk : k ≤ m) :
        (2 : ℝ)^k * x ∈ Set.Icc (0 : ℝ) 1 := by
      have : x ∈ Set.Icc (0 : ℝ) (1 / (2 : ℝ)^k) := ⟨hx.1, hx_le_k hk⟩
      simpa using h8 k ⟨x, this⟩

    -- Key dyadic superadditivity:  (2^k) f(x) ≤ f(2^k x)  for k ≤ m.
    have super_pow :
        ∀ k, (hk : k ≤ m) → (2 : ℝ)^k * f ⟨x, hx⟩ ≤ f ⟨(2 : ℝ)^k * x, mem_pow k hk⟩ := by
      intro k hk
      induction' k with k ih
      · simp
      · have hk' : k ≤ m := Nat.le_of_succ_le hk
        have memk  := mem_pow k hk'
        have memkp := mem_pow (k+1) hk
        -- multiply IH by 2, then apply h3 at the same point (self + self)
        have step1 :
          (2 : ℝ) * ((2 : ℝ)^k * f ⟨x, hx⟩) ≤
          (2 : ℝ) * f ⟨(2 : ℝ)^k * x, memk⟩ :=
          by
            have : 0 ≤ (2 : ℝ) := by norm_num
            exact mul_le_mul_of_nonneg_left (ih hk') this
        have step2 :
          (2 : ℝ) * f ⟨(2 : ℝ)^k * x, memk⟩ ≤
          f ⟨(2 : ℝ)^(k+1) * x, memkp⟩ := by
          -- h3 applied to the same point adds values
          grind

        -- rewrite 2^(k+1) and combine
        simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using step1.trans step2

    -- At k = m we get (2^m) f(x) ≤ f(2^m x) ≤ 1.
    have two_pow_f_le_one :
        (2 : ℝ)^m * f ⟨x, hx⟩ ≤ 1 := by
      have := super_pow m le_rfl
      exact this.trans (h6 ⟨(2 : ℝ)^m * x, mem_pow m le_rfl⟩)

    -- Divide by 2^m > 0:
    have fx_le : f ⟨x, hx⟩ ≤ 1 / (2 : ℝ)^m := by
      have hpos : 0 < (2 : ℝ)^m := by simp
      exact (le_div_iff₀' hpos).mpr two_pow_f_le_one

    -- And 1 / 2^m ≤ 2x because 1 / 2^(m+1) < x  ⇒  (1 / 2^m) = 2 * (1 / 2^(m+1)) < 2x.
    have one_over_le_twox : 1 / (2 : ℝ)^m ≤ 2 * x := by
      have : 1 / (2 : ℝ)^m < 2 * x := by
        have : (2 : ℝ) * (1 / (2 : ℝ)^(m+1)) < (2 : ℝ) * x :=
          mul_lt_mul_of_pos_left hx_lower (by norm_num)
        simpa [pow_succ, one_div, mul_comm, mul_left_comm, mul_assoc] using this
      exact this.le

    exact fx_le.trans one_over_le_twox

  · -- large x
    have : (1 : ℝ) ≤ 2 * x := by
      have : (1 : ℝ)/2 < x := lt_of_le_of_ne (le_of_not_ge hxhalf) (by grind)
      nlinarith
    exact (h6 ⟨x, hx⟩).trans this

snip end

def valid (f : Set.Icc (0 : ℝ) 1 → ℝ) : Prop :=
  (∀ x, 0 ≤ f x) ∧
  f 1 = 1 ∧
  ∀ x y, (h : x.val + y.val ∈ Set.Icc 0 1) → f x + f y ≤ f ⟨x.val + y.val, h⟩

determine min_c : ℝ := 2

problem usa1993_p5 :
    IsLeast {c | ∀ f, valid f → ∀ x, f x ≤ c * x } min_c := by
  simp only [Subtype.forall, Set.mem_Icc]
  constructor
  · simp only [Set.mem_setOf_eq]
    intro f hf x hx
    obtain ⟨h1, h2, h3⟩ := hf
    unfold min_c
    have h4 : ∀ x : Set.Icc (0:ℝ) 1, (1 - (x:ℝ)) ∈ Set.Icc (0:ℝ) 1 := by
       rintro ⟨x, hx⟩; exact Set.Icc.mem_iff_one_sub_mem.mp hx
    have h5 : ∀ x, f x + f ⟨1 - x, h4 x⟩ ≤ 1 := by
      intro x
      specialize h3 x ⟨1 - x, h4 x⟩
      simp only [add_sub_cancel, Set.mem_Icc, zero_le_one, le_refl, and_self, Set.Icc.mk_one,
        forall_const] at h3
      grw [h3, h2]
    have h6 : ∀ x, f x ≤ 1 := fun x ↦ by
      specialize h5 x
      specialize h1 ⟨1 - x, h4 x⟩
      linarith
    have h8 : ∀ n : ℕ, ∀ x : Set.Icc (0:ℝ) (1/2^n), 2^n * (x : ℝ) ∈ Set.Icc (0:ℝ) 1 := by
      rintro n ⟨x, hx1, hx2⟩; clear h3; simp at hx ⊢
      refine ⟨hx1, ?_⟩
      grw [hx2]; simp
    exact lemma2 f x hx h1 h2 h3 h4 h5 h6 h8
  · rw [mem_lowerBounds]
    intro c1 hc1
    simp only [Set.mem_setOf_eq] at hc1
    let f : Set.Icc (0 : ℝ) 1 → ℝ := fun x ↦ if x.val ≤ 1/2 then 0 else 1
    have hf : valid f := by
      refine ⟨?_, ?_, ?_⟩
      · intro x
        positivity
      · unfold f; norm_num
      · intro x y hx
        obtain ⟨x, hxx⟩ := x
        obtain ⟨y, hyy⟩ := y
        simp only [Set.mem_Icc] at hx hxx hyy
        obtain ⟨hx1, hx2⟩ := hx
        unfold f
        split_ifs with h1 h2 h3 h4 h5 h6 <;> linarith
    specialize hc1 f hf
    obtain ⟨h1, h2, h3⟩ := hf
    exact lemma1 c1 hc1 h1 h2 h3


end Usa1993P3
