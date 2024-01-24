/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Olympiad 1979, Problem 1

Suppose that p and q are positive integers such that

  p / q = 1 - 1/2 + 1/3 - 1/4 + ... - 1/1318 + 1/1319.

Prove that p is divisible by 1979.
-/

namespace Imo1979P1

open scoped BigOperators

snip begin

lemma lemma1 (n : ℕ) : ¬ Even (2 * n + 1) := by
  rintro ⟨r, H⟩
  rw [←Nat.two_mul] at H
  apply_fun (· % 2) at H
  rw [Nat.add_mod, Nat.mul_mod] at H
  norm_num at H

lemma lemma2 (x y : ℚ) : x + y - 2 * y = x - y := by ring

lemma lemma3 : ∑ i in Finset.range 1319, (-(1:ℚ))^i / (i + 1) =
      ∑ i in Finset.range 1319, (1:ℚ) / (i + 1) -
         2 * ∑ i in Finset.range 659, (1:ℚ) / (2 * (i + 1)) := by
  have h2 := Finset.sum_filter_add_sum_filter_not
           (Finset.range 1319) (Even ·) (λ i ↦ (1:ℚ) / (i + 1))
  rw [←h2]
  let g : ℕ ↪ ℕ :=
    ⟨fun x ↦ 2 * x + 1,
     by intro a b hab; dsimp at hab; linarith⟩

  have h4 : (Finset.range 659).map g =
        (Finset.range 1319).filter (fun x ↦ ¬Even x) := by
    ext a
    unfold_let g
    rw [Finset.mem_map, Function.Embedding.coeFn_mk,
        Finset.mem_filter, Finset.mem_range]
    constructor
    · intro ha
      obtain ⟨b, hb1, hb2⟩ := ha
      rw [Finset.mem_range] at hb1
      rw [←hb2]
      constructor
      · linarith
      · exact lemma1 b
    · rintro ⟨ha1, ha2⟩
      have h5 : Odd a := Nat.odd_iff_not_even.mpr ha2
      obtain ⟨r, hr⟩ := h5
      use r
      constructor
      · rw [Finset.mem_range]; linarith
      · exact hr.symm
  have h5 : ∑ i in Finset.range 659, 1 / (2 * ((i:ℚ) + 1))
       = ∑ i in Finset.range 659, (1 / (((g i):ℚ) + 1)) := by
    apply Finset.sum_congr rfl
    intro x _
    field_simp; ring
  have h6 := Finset.sum_map (Finset.range 659) g (fun j ↦ 1 / ((j:ℚ) + 1))

  have h3 :
    ∑ x in Finset.filter (fun x ↦ ¬Even x) (Finset.range 1319),
     1 / ((x:ℚ) + 1) =
      ∑ i in Finset.range 659, 1 / (2 * ((i:ℚ) + 1)) := by
    rw [h5]
    rw [←h6, h4]
  rw [h3, lemma2]
  rw [←h3, ←h4, h6, ←h5, ←h3]
  have h7 :
   ∑ i in Finset.filter (fun x ↦ Even x) (Finset.range 1319), 1 / ((i:ℚ) + 1) =
    ∑ i in Finset.filter (fun x ↦ Even x) (Finset.range 1319),
      (-(1:ℚ))^i / ((i:ℚ) + 1) := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mem_filter] at hx
    have h9: (-(1:ℚ))^x = 1 := by aesop
    rw [h9]
  rw [h7]; clear h7
  rw [Rat.sub_eq_add_neg, ←Finset.sum_neg_distrib]
  have h10 : ∑ x in Finset.filter (fun x ↦ ¬Even x) (Finset.range 1319),
               -(1 / ((x:ℚ) + 1)) =
              ∑ x in Finset.filter (fun x ↦ ¬Even x) (Finset.range 1319),
               (-(1:ℚ))^x / ((x:ℚ) + 1) := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mem_filter] at hx
    have h9: (-(1:ℚ))^x = -1 := by aesop
    rw [h9]
    field_simp
  rw [h10, Finset.sum_filter_add_sum_filter_not]

lemma lemma4 (n m : ℕ) (f : ℕ → ℚ) :
    ∑ i in Finset.Ico n (n + 2 * m), f i =
    ∑ i in Finset.range m, (f (n + i) + f (n + (2 * m - 1 - i))) := by
  have h1 : ∑ i in Finset.Ico n (n + 2 * m), f i =
            (∑ i in Finset.Ico n (n + m), f i) +
            (∑ i in Finset.Ico (n + m) (n + 2 * m), f i) := by
    have hmn : n ≤ n + m := Nat.le_add_right n m
    have hnk : n + m ≤ n + 2 * m := by omega
    exact (Finset.sum_Ico_consecutive (fun i ↦ f i) hmn hnk).symm
  rw [h1]; clear h1
  simp only [Finset.sum_Ico_eq_sum_range, add_tsub_cancel_left]
  rw [Finset.sum_add_distrib, add_right_inj]
  rw [show n + 2 * m - (n + m) = m by omega]

  have h2 : ∀ i ∈ Finset.range m, f (n + (2 * m - 1 - i)) = f (n + m + (m - 1 - i)) := by
    intro i hi
    rw [Finset.mem_range] at hi
    apply congr_arg
    omega
  rw [Finset.sum_congr rfl h2]
  let g i := f (n + m + i)
  rw [Finset.sum_range_reflect g]

snip end

problem imo1979_p1 (p q : ℤ) (hp : 0 < p) (hq : 0 < q)
    (h : (p : ℚ) / q = ∑ i in Finset.range 1319, (-(1:ℚ))^i / (i + 1)) :
    1979 ∣ p := by
  -- we follow the solution from
  -- https://artofproblemsolving.com/wiki/index.php/1979_IMO_Problems/Problem_1

  rw [lemma3] at h
  have h1 : 2 * ∑ i in Finset.range 659, 1 / (2 * ((i:ℚ) + 1)) =
              ∑ i in Finset.range 659, 1 / ((i:ℚ) + 1) := by
    rw [Finset.mul_sum, Finset.sum_congr rfl]
    intro x hx
    field_simp
  rw [h1] at h; clear h1
  have h2 : Disjoint (Finset.range 659) (Finset.Ico 659 1319) := by
    rw [Finset.disjoint_left]
    intro a ha ha1
    rw [Finset.mem_range] at ha
    rw [Finset.mem_Ico] at ha1
    omega
  have h3 : Finset.range 1319 =
      Finset.disjUnion (Finset.range 659) (Finset.Ico 659 1319) h2 := by
    ext a
    rw [Finset.mem_range, Finset.disjUnion_eq_union, Finset.mem_union,
        Finset.mem_range, Finset.mem_Ico]
    omega
  rw [h3] at h; clear h3
  rw [Finset.sum_disjUnion, add_sub_cancel'] at h; clear h2
  rw [lemma4 659 330] at h
  sorry
