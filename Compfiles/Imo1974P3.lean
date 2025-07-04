/-
Copyright (c) 2025 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Roozbeh Yousefzadeh
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file {
  tags := [.NumberTheory]
  importedFrom :=
    "https://github.com/roozbeh-yz/IMO-Steps/blob/main/imo_proofs/imo_1974_p3.lean"
}

/-!
# International Mathematical Olympiad 1974, Problem 3

Prove that the sum from k = 0 to n inclusive of
   Choose[2n + 1, 2k + 1] * 2³ᵏ
is not divisible by 5 for any integer n ≥ 0.
-/

namespace Imo1974P3

snip begin

lemma aux_1 (a : ℕ) :
    ¬ a ^ 2 ≡ 2 [MOD 5] := by
  intro ha
  change _ = _ at ha
  rw [Nat.pow_mod] at ha
  mod_cases H : a % 5 <;>
    change _ % _ = _ % 5 at H <;> rw [H] at ha <;> norm_num at ha

lemma aux_2
  (a : ℕ) :
  ¬ a ^ 2 ≡ 3 [MOD 5] := by
  intro ha
  change _ = _ at ha
  rw [Nat.pow_mod] at ha
  mod_cases H : a % 5 <;>
    change _ % _ = _ % 5 at H <;> rw [H] at ha <;> norm_num at ha

lemma aux_3
  (n : ℕ) :
  7 ^ (2 * n + 1) ≡ 2 [MOD 5] ∨ 7 ^ (2 * n + 1) ≡ 3 [MOD 5] := by
  induction' n with d hd
  . left; decide
  . let b:ℕ := (7 ^ (2 * d + 1)) % 5
    have hb: b = (7 ^ (2 * d + 1)) % 5 := by rfl
    have hb₀: b < 5 := by
      rw [hb]
      omega
    have hb₁: (7 ^ (2 * d + 1)) ≡ b [MOD 5] := by
      exact Nat.ModEq.symm (Nat.mod_modEq (7 ^ (2 * d + 1)) 5)
    ring_nf at *
    have hb₂: 7 ^ (d * 2) * 7 * 49 ≡ b * 49 [MOD 5] := by
      exact Nat.ModEq.mul hb₁ rfl
    have hb₃: 7 ^ (d * 2) * 7 * 49 ≡ 2 * 49 [MOD 5] ∨ 7 ^ (d * 2) * 7 * 49 ≡ 3 * 49 [MOD 5] := by
      cases' hd with hd₀ hd₁
      . left
        exact Nat.ModEq.mul hd₀ rfl
      . right
        exact Nat.ModEq.mul hd₁ rfl
    ring_nf at hb₂
    ring_nf at *
    cases' hb₃ with hb₄ hb₅
    . interval_cases b
      . ring_nf at hb₂
        have g₀: 0 ≡ 98 [MOD 5] := by
          refine Nat.ModEq.trans hb₂.symm hb₄
        have g₁: ¬ 0 ≡ 98 [MOD 5] := by decide
        exact (g₁ g₀).elim
      . ring_nf at hb₂
        have g₀: 49 ≡ 98 [MOD 5] := by
          refine Nat.ModEq.trans hb₂.symm hb₄
        have g₁: ¬ 49 ≡ 98 [MOD 5] := by decide
        exact (g₁ g₀).elim
      . ring_nf at hb₂
        have g₀: 98 ≡ 3 [MOD 5] := by decide
        right
        refine Nat.ModEq.trans hb₂ g₀
      . ring_nf at hb₂
        have g₀: 147 ≡ 98 [MOD 5] := by
          refine Nat.ModEq.trans hb₂.symm hb₄
        have g₁: ¬ 147 ≡ 98 [MOD 5] := by decide
        exact (g₁ g₀).elim
      . ring_nf at hb₂
        have g₀: 196 ≡ 98 [MOD 5] := by
          refine Nat.ModEq.trans hb₂.symm hb₄
        have g₁: ¬ 196 ≡ 98 [MOD 5] := by decide
        exact (g₁ g₀).elim
    . interval_cases b
      . ring_nf at hb₂
        have g₀: 0 ≡ 147 [MOD 5] := by
          refine Nat.ModEq.trans hb₂.symm hb₅
        have g₁: ¬ 0 ≡ 147 [MOD 5] := by decide
        exact (g₁ g₀).elim
      . ring_nf at hb₂
        have g₀: 49 ≡ 147 [MOD 5] := by
          refine Nat.ModEq.trans hb₂.symm hb₅
        have g₁: ¬ 49 ≡ 147 [MOD 5] := by decide
        exact (g₁ g₀).elim
      . ring_nf at hb₂
        have g₀: 98 ≡ 147 [MOD 5] := by
          refine Nat.ModEq.trans hb₂.symm hb₅
        have g₁: ¬ 98 ≡ 147 [MOD 5] := by decide
        exact (g₁ g₀).elim
      . ring_nf at hb₂
        exact Or.intro_left (7 ^ (d * 2) * 343 ≡ 3 [MOD 5]) hb₅
      . ring_nf at hb₂
        have g₀: 196 ≡ 147 [MOD 5] := by
          refine Nat.ModEq.trans hb₂.symm hb₅
        have g₁: ¬ 196 ≡ 147 [MOD 5] := by decide
        exact (g₁ g₀).elim


lemma aux_4
  (n b a : ℕ)
  (k : ℝ)
  (hb₁ : ↑b = 1 / k * ∑ x ∈ Finset.range (n + 1), ↑((2 * n + 1).choose (2 * x + 1)) * k ^ (2 * x + 1))
  (ha₁ : ↑a = ∑ x ∈ Finset.range (n + 1), ↑((2 * n + 1).choose (2 * x)) * k ^ (2 * x))
  (hk₀ : k * k⁻¹ = 1) :
  (1 + k) ^ (2 * n + 1) = ↑a + ↑b * k := by
  rw [mul_comm _ k, hb₁, ← mul_assoc]
  rw [← inv_eq_one_div, hk₀, one_mul, ha₁]
  rw [add_comm, add_pow k 1 (2 * n + 1)]
  simp
  clear hb₁ ha₁ b a hk₀
  let f : ℕ → ℝ := fun i => ↑((2 * n + 1).choose (i)) * k ^ i
  let fs₂ := Finset.range (2 * n + 2)
  -- let fs₀ : Finset ℕ := Finset.filter (fun x => Odd x) (Finset.range (2 * n + 2))
  let fs₀ : Finset ℕ := fs₂.filter (fun x => Odd x)
  let fs₁ : Finset ℕ := fs₂.filter (fun x => Even x)
  let fs₃ : Finset ℕ := Finset.range (n + 1)
  have h₀: ∑ x ∈ Finset.range (n + 1), ↑((2 * n + 1).choose (2 * x + 1)) * k ^ (2 * x + 1) =
    ∑ x ∈ fs₀, ↑((2 * n + 1).choose (x)) * k ^ (x) := by
    have h₀₁: ∑ x ∈ fs₃, f (2 * x + 1) = ∑ x ∈ (fs₀), f x := by
      refine Finset.sum_bij ?i ?_ ?i_inj ?i_surj ?h
      . intros a _
        exact (2 * a + 1)
      . intros a ha₀
        have ha₁: a ≤ n := Finset.mem_range_succ_iff.mp ha₀
        have ha₂: 2 * a + 1 ≤ 2 * n + 1 := by omega
        have ha₃: (2 * a + 1) ∈ fs₂ := Finset.mem_range_succ_iff.mpr ha₂
        have ha₄: Odd (2 * a + 1) := odd_two_mul_add_one a
        refine Finset.mem_filter.mpr ?_
        exact And.symm ⟨ha₄, ha₃⟩
      . intros a _ b _ h₃
        omega
      . intros b hb₀
        use ((b - 1) / 2)
        refine exists_prop.mpr ?_
        have hb₁: b ∈ fs₂ ∧ Odd b := Finset.mem_filter.mp hb₀
        have hb₂: 1 ≤ b := by
          by_contra! hc₀
          interval_cases b
          have hc₁: ¬ Odd 0 := by decide
          apply hc₁ hb₁.2
        have hb₃: Even (b - 1) := by
          refine (Nat.even_sub hb₂).mpr ?_
          simp only [Nat.not_even_one, iff_false, Nat.not_even_iff_odd]
          exact hb₁.2
        constructor
        . have hb₄: b < 2 * n + 2 := by exact List.mem_range.mp hb₁.1
          have hb₅: (b - 1) / 2 < n + 1 := by omega
          exact Finset.mem_range.mpr hb₅
        . have hb₆: 2 * ((b - 1) / 2) = b - 1 := Nat.two_mul_div_two_of_even hb₃
          rw [hb₆]
          exact Nat.sub_add_cancel hb₂
      . exact fun a _ => rfl
    exact h₀₁
  have h₁: ∑ x ∈ Finset.range (n + 1), ↑((2 * n + 1).choose (2 * x)) * k ^ (2 * x) =
    ∑ x ∈ fs₁, ↑((2 * n + 1).choose (x)) * k ^ (x) := by
    have h₁₁: ∑ x ∈ fs₃, f (2 * x) = ∑ x ∈ (fs₁), f x := by
      refine Finset.sum_bij ?_ ?_ ?_ ?_ ?_
      . intros a _
        exact (2 * a)
      . intros a ha₀
        have ha₁: a < n + 1 := List.mem_range.mp ha₀
        have ha₂: 2 * a < 2 * n + 2 := by omega
        refine Finset.mem_filter.mpr ?_
        constructor
        . exact Finset.mem_range.mpr ha₂
        . exact even_two_mul a
      . intros a _ b _ h₃
        exact Nat.eq_of_mul_eq_mul_left (by norm_num) h₃
      . intros b hb₀
        use (b/2)
        refine exists_prop.mpr ?_
        have hb₁: b ∈ fs₂ ∧ Even b := Finset.mem_filter.mp hb₀
        constructor
        . have hb₂: b < 2 * n + 2 := by exact List.mem_range.mp hb₁.1
          have hb₃: (b / 2) < n + 1 := by exact Nat.div_lt_of_lt_mul hb₂
          exact Finset.mem_range.mpr hb₃
        . exact Nat.two_mul_div_two_of_even hb₁.2
      . exact fun a _ => rfl
    exact h₁₁
  have h₂: ∑ x ∈ Finset.range (2 * n + 1 + 1), k ^ x * ↑((2 * n + 1).choose x) =
    ∑ x ∈ fs₂, ↑((2 * n + 1).choose x) * k ^ x := by
    refine Finset.sum_congr (rfl) ?_
    intros x _
    rw [mul_comm]
  rw [h₀, h₁, h₂]
  have h₃: fs₂ = fs₀ ∪ fs₁ := by
    refine Finset.ext_iff.mpr ?_
    intro a
    constructor
    . intro ha₀
      refine Finset.mem_union.mpr ?mp.a
      have ha₁: Odd a ∨ Even a := Or.symm (Nat.even_or_odd a)
      cases' ha₁ with ha₂ ha₃
      . left
        refine Finset.mem_filter.mpr ?mp.a.inl.h.a
        exact And.symm ⟨ha₂, ha₀⟩
      . right
        refine Finset.mem_filter.mpr ?mp.a.inl.h.b
        exact And.symm ⟨ha₃, ha₀⟩
    . intro ha₀
      apply Finset.mem_union.mp at ha₀
      cases' ha₀ with ha₁ ha₂
      . exact Finset.mem_of_mem_filter a ha₁
      . exact Finset.mem_of_mem_filter a ha₂
  have h₄: Disjoint fs₀ fs₁ := by
    refine Finset.disjoint_filter.mpr ?_
    intros x _ hx₁
    exact Nat.not_even_iff_odd.mpr hx₁
  nth_rw 2 [add_comm]
  rw [h₃, Finset.sum_union h₄]


lemma aux_5
  (n b a : ℕ)
  (k : ℝ)
  (hb₁ : ↑b = 1 / k * ∑ x ∈ Finset.range (n + 1), ↑((2 * n + 1).choose (2 * x + 1)) * k ^ (2 * x + 1))
  (ha₁ : ↑a = ∑ x ∈ Finset.range (n + 1), ↑((2 * n + 1).choose (2 * x)) * k ^ (2 * x))
  (hk₀ : k * k⁻¹ = 1) :
  (1 - k) ^ (2 * n + 1) = ↑a - ↑b * k := by
  rw [mul_comm _ k, hb₁, ← mul_assoc]
  rw [← inv_eq_one_div, hk₀, one_mul, ha₁, sub_eq_add_neg]
  rw [add_comm 1 _, add_pow (-k) 1 (2 * n + 1)]
  simp
  clear hb₁ ha₁ b a hk₀
  let f₀ : ℕ → ℝ := fun i => ↑((2 * n + 1).choose (i)) * k ^ i
  let f₁ : ℕ → ℝ := fun i => ↑((2 * n + 1).choose (i)) * (-k) ^ i
  let fs₂ := Finset.range (2 * n + 2)
  let fs₀ : Finset ℕ := fs₂.filter (fun x => Odd x)
  let fs₁ : Finset ℕ := fs₂.filter (fun x => Even x)
  let fs₃ : Finset ℕ := Finset.range (n + 1)
  have h₀: ∑ x ∈ Finset.range (n + 1), ↑((2 * n + 1).choose (2 * x + 1)) * k ^ (2 * x + 1) =
    - ∑ x ∈ fs₀, ↑((2 * n + 1).choose (x)) * (-k) ^ (x) := by
    rw [neg_eq_neg_one_mul, Finset.mul_sum]
    have h₀₁: ∑ x ∈ fs₃, f₀ (2 * x + 1) = ∑ x ∈ (fs₀), -1 * f₁ x := by
      refine Finset.sum_bij ?i ?_ ?i_inj ?i_surj ?h
      . intros a _
        exact (2 * a + 1)
      . intros a ha₀
        have ha₁: a ≤ n := Finset.mem_range_succ_iff.mp ha₀
        have ha₂: 2 * a + 1 ≤ 2 * n + 1 := by omega
        have ha₃: (2 * a + 1) ∈ fs₂ := Finset.mem_range_succ_iff.mpr ha₂
        have ha₄: Odd (2 * a + 1) := odd_two_mul_add_one a
        refine Finset.mem_filter.mpr ?_
        exact And.symm ⟨ha₄, ha₃⟩
      . intros a _ b _ h₃
        omega
      . intros b hb₀
        use ((b - 1) / 2)
        refine exists_prop.mpr ?_
        have hb₁: b ∈ fs₂ ∧ Odd b := Finset.mem_filter.mp hb₀
        have hb₂: 1 ≤ b := by
          by_contra! hc₀
          interval_cases b
          have hc₁: ¬ Odd 0 := by decide
          apply hc₁ hb₁.2
        have hb₃: Even (b - 1) := by
          refine (Nat.even_sub hb₂).mpr ?_
          simp only [Nat.not_even_one, iff_false, Nat.not_even_iff_odd]
          exact hb₁.2
        constructor
        . have hb₄: b < 2 * n + 2 := by exact List.mem_range.mp hb₁.1
          have hb₅: (b - 1) / 2 < n + 1 := by omega
          exact Finset.mem_range.mpr hb₅
        . have hb₆: 2 * ((b - 1) / 2) = b - 1 := Nat.two_mul_div_two_of_even hb₃
          rw [hb₆]
          exact Nat.sub_add_cancel hb₂
      . intros b hb₀
        have hb₁: (-1:ℝ) ^ (b * 2) = 1 := by
          refine (neg_one_pow_eq_one_iff_even (by norm_num)).mpr ?_
          rw [mul_comm]
          exact even_two_mul b
        simp only [f₀, f₁]
        ring_nf
        rw [hb₁, mul_one]
    exact h₀₁
  have h₁: ∑ x ∈ Finset.range (n + 1), ↑((2 * n + 1).choose (2 * x)) * k ^ (2 * x) =
    ∑ x ∈ fs₁, ↑((2 * n + 1).choose (x)) * (-k) ^ (x) := by
    have h₁₁: ∑ x ∈ fs₃, f₀ (2 * x) = ∑ x ∈ (fs₁), f₁ x := by
      refine Finset.sum_bij ?_ ?_ ?_ ?_ ?_
      . intros a _
        exact (2 * a)
      . intros a ha₀
        have ha₁: a < n + 1 := List.mem_range.mp ha₀
        have ha₂: 2 * a < 2 * n + 2 := by omega
        refine Finset.mem_filter.mpr ?_
        constructor
        . exact Finset.mem_range.mpr ha₂
        . exact even_two_mul a
      . intros a _ b _ h₃
        exact Nat.eq_of_mul_eq_mul_left (by norm_num) h₃
      . intros b hb₀
        use (b/2)
        refine exists_prop.mpr ?_
        have hb₁: b ∈ fs₂ ∧ Even b := Finset.mem_filter.mp hb₀
        constructor
        . have hb₂: b < 2 * n + 2 := by exact List.mem_range.mp hb₁.1
          have hb₃: b / 2 < n + 1 := by exact Nat.div_lt_of_lt_mul hb₂
          exact Finset.mem_range.mpr hb₃
        . exact Nat.two_mul_div_two_of_even hb₁.2
      . intros b hb₀
        have hb₁: (-1:ℝ) ^ (b * 2) = 1 := by
          refine (neg_one_pow_eq_one_iff_even (by norm_num)).mpr ?_
          rw [mul_comm]
          exact even_two_mul b
        simp only [f₀, f₁]
        ring_nf
        rw [hb₁, mul_one]
    exact h₁₁
  have h₂: ∑ x ∈ Finset.range (2 * n + 1 + 1), (-k) ^ x * ↑((2 * n + 1).choose x) =
    ∑ x ∈ fs₂, ↑((2 * n + 1).choose x) * (-k) ^ x := by
    refine Finset.sum_congr (rfl) ?_
    intros x _
    rw [mul_comm]
  rw [h₀, h₁, h₂, sub_neg_eq_add]
  have h₃: fs₂ = fs₀ ∪ fs₁ := by
    refine Finset.ext_iff.mpr ?_
    intro a
    constructor
    . intro ha₀
      refine Finset.mem_union.mpr ?mp.a
      have ha₁: Odd a ∨ Even a := by exact Or.symm (Nat.even_or_odd a)
      cases' ha₁ with ha₂ ha₃
      . left
        refine Finset.mem_filter.mpr ?mp.a.inl.h.a
        exact And.symm ⟨ha₂, ha₀⟩
      . right
        refine Finset.mem_filter.mpr ?mp.a.inl.h.b
        exact And.symm ⟨ha₃, ha₀⟩
    . intro ha₀
      apply Finset.mem_union.mp at ha₀
      cases' ha₀ with ha₁ ha₂
      . exact Finset.mem_of_mem_filter a ha₁
      . exact Finset.mem_of_mem_filter a ha₂
  have h₄: Disjoint fs₀ fs₁ := by
    refine Finset.disjoint_filter.mpr ?_
    intros x _ hx₁
    exact Nat.not_even_iff_odd.mpr hx₁
  nth_rw 2 [add_comm]
  rw [h₃, Finset.sum_union h₄]

snip end

problem imo1974_p3
    (n : ℕ) :
    ¬ 5 ∣ ∑ k ∈ Finset.range (n + 1),
            (Nat.choose (2 * n + 1) (2 * k + 1)) * (2^(3 * k)) := by
  let k:ℝ := Real.sqrt (8:ℝ)
  have hk: k = Real.sqrt (8:ℝ) := by rfl
  let b:ℕ := ∑ k ∈ Finset.range (n + 1), (Nat.choose (2 * n + 1) (2 * k + 1)) * (2^(3 * k))
  have hb: b = ∑ k ∈ Finset.range (n + 1), (Nat.choose (2 * n + 1) (2 * k + 1)) * (2^(3 * k)) := by rfl
  rw [← hb]
  let a:ℕ := ∑ k ∈ Finset.range (n + 1), (Nat.choose (2 * n + 1) (2 * k) * (2 ^ (3 * k)))
  have ha: a = ∑ k ∈ Finset.range (n + 1), (Nat.choose (2 * n + 1) (2 * k) * (2 ^ (3 * k))) := by rfl
  have hb₁: b = (1 / k) *
    ∑ x ∈ Finset.range (n + 1), (Nat.choose (2 * n + 1) (2 * x + 1)) * (k ^ (2 * x + 1)) := by
    rw [hb, hk]
    simp
    rw [Finset.mul_sum]
    refine Finset.sum_congr (rfl) ?_
    intros x _
    rw [mul_comm ((√8)⁻¹), mul_assoc]
    refine mul_eq_mul_left_iff.mpr ?_
    left
    rw [pow_succ, pow_mul, pow_mul, Real.sq_sqrt (by norm_num)]
    norm_num
  have ha₁: a = ∑ x ∈ Finset.range (n + 1), (Nat.choose (2 * n + 1) (2 * x) * (k ^ (2 * x))) := by
    rw [ha, hk]
    simp
    refine Finset.sum_congr (rfl) ?_
    intros x _
    refine mul_eq_mul_left_iff.mpr ?_
    left
    rw [pow_mul, pow_mul, Real.sq_sqrt (by norm_num)]
    norm_num
  have hk₀: k * k⁻¹ = 1 := by
    refine (mul_inv_eq_one₀ ?_).mpr (rfl)
    rw [hk]
    norm_num
  have h₀: (1 + k) ^ (2 * n + 1) = a + b * k := by
    exact aux_4 n b a k hb₁ ha₁ hk₀
  have h₁: (1 - k) ^ (2 * n + 1) = a - b * k := by
    exact aux_5 n b a k hb₁ ha₁ hk₀
  have h₂: ((1 + k) * (1 - k)) ^ (2 * n + 1) = (a + b * k) * (a - b * k) := by
    rw [mul_pow, h₀, h₁]
  rw [← sq_sub_sq 1 k] at h₂
  rw [← sq_sub_sq (↑a) ((↑b:ℝ) * k)] at h₂
  rw [mul_pow, hk] at h₂
  norm_num at h₂
  have h₃: (7:ℕ) ^ (2 * n + 1) = b ^ 2 * 8 - a ^ 2 := by
    have h₃₀: Odd (2 * n + 1) := by exact odd_two_mul_add_one n
    have h₃₁: (-7:ℝ) = (-1:ℝ) * (7:ℕ) := by norm_num
    have h₃₂: (-1:ℝ) ^ (2 * n + 1) = -1 := by exact Odd.neg_one_pow h₃₀
    have h₃₃: ↑a ^ 2 - ↑b ^ 2 * 8 = (-1:ℝ) * (↑b ^ 2 * 8 - ↑a ^ 2) := by
      linarith
    rw [h₃₁, mul_pow, h₃₂, h₃₃] at h₂
    simp at h₂
    have h₃₄: (7:ℝ) ^ (2 * n + 1) = ↑b ^ 2 * 8 - ↑a ^ 2 := by
      linarith
    norm_cast at h₃₄
    rw [Int.subNatNat_eq_coe] at h₃₄
    rw [← Int.toNat_sub, ← h₃₄]
    exact rfl
  have h₄: 7 ^ (2 * n + 1) ≡ 2 [MOD 5] ∨ 7 ^ (2 * n + 1) ≡ 3 [MOD 5] := by
    refine aux_3 n
  by_contra! hc₀
  have hc₁: b^2 * 8 ≡ 0^2 * 8 [MOD 5] := by
    refine Nat.ModEq.mul ?_ rfl
    refine Nat.ModEq.pow 2 ?_
    exact Nat.modEq_zero_iff_dvd.mpr hc₀
  simp at hc₁
  have h₅: a ^ 2 < b ^ 2 * 8 := by
    have h₅₀: 0 < 7 ^ (2 * n + 1) := by
      exact Nat.pow_pos (by norm_num)
    rw [h₃] at h₅₀
    exact Nat.lt_of_sub_pos h₅₀
  cases' h₄ with h₄₀ h₄₁
  . rw [h₃] at h₄₀
    have hc₂: b ^ 2 * 8 - a ^ 2 + a ^ 2 ≡ 2 + a ^ 2 [MOD 5] := by
      exact Nat.ModEq.add_right (a ^ 2) h₄₀
    rw [Nat.sub_add_cancel (le_of_lt h₅)] at hc₂
    have hc₃: 3 + (2 + a ^ 2) ≡ 3 [MOD 5] := by
      apply Nat.ModEq.trans hc₂.symm at hc₁
      exact Nat.ModEq.add_left 3 hc₁
    have hc₄: a ^ 2 ≡ 3 [MOD 5] := by
      rw [← add_assoc, ← zero_add 3] at hc₃
      norm_num at hc₃
      have hc₄: 5 ≡ 0 [MOD 5] := by decide
      exact Nat.ModEq.add_left_cancel hc₄ hc₃
    have hc₅: ¬ a ^ 2 ≡ 3 [MOD 5] := by exact aux_2 a
    exact hc₅ hc₄
  . rw [h₃] at h₄₁
    have hc₂: b ^ 2 * 8 - a ^ 2 + a ^ 2 ≡ 3 + a ^ 2 [MOD 5] := by
      exact Nat.ModEq.add_right (a ^ 2) h₄₁
    rw [Nat.sub_add_cancel (le_of_lt h₅)] at hc₂
    apply Nat.ModEq.trans hc₂.symm at hc₁
    have hc₃: a ^ 2 ≡ 2 [MOD 5] := Nat.ModEq.add_left_cancel' 3 hc₁
    exact aux_1 a hc₃

end Imo1974P3
