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

lemma lemma3 : ∑ i in Finset.range 1319, (-(1:ℚ))^i / (i + 1) =
      ∑ i in Finset.range 1319, (1:ℚ) / (i + 1) -
         2 * ∑ i in Finset.range 659, (1:ℚ) / (2 * (i + 1)) := by
  have h2 := Finset.sum_filter_add_sum_filter_not
           (Finset.range 1319) (Even ·) (λ i ↦ (1:ℚ) / (i + 1))
  rw [←h2]
  let g : ℕ ↪ ℕ :=
    ⟨fun x ↦ 2 * x + 1,
     by intro a b hab; dsimp at hab; omega⟩

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
      · omega
      · exact Nat.odd_iff_not_even.mp ⟨b, rfl⟩
    · rintro ⟨ha1, ha2⟩
      have h5 : Odd a := Nat.odd_iff_not_even.mpr ha2
      obtain ⟨r, hr⟩ := h5
      use r
      constructor
      · rw [Finset.mem_range]; omega
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
  rw [h3, two_mul, add_sub_add_right_eq_sub]
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

theorem not_dvd_finset_prod {α M : Type*} [CommMonoidWithZero M]
    {S : Finset α} {p : M} (pp : Prime p)
    {g : α → M} (hS : ∀ i ∈ S, ¬ p ∣ g i) : ¬ p ∣ ∏ i in S, g i := by
  exact mt (Prime.dvd_finset_prod_iff pp _).1 <| not_exists.2 fun a => not_and.2 (hS a)

lemma lemma8 (q : ℕ) (h : 0 < (q:ℤ)) : (q:ℚ) ≠ 0 := by
  norm_cast at h ⊢
  exact Nat.pos_iff_ne_zero.mp h

lemma lemma9' (i : ℕ) (hi : i ∈ Finset.range 330) :
     (((∏ j in Finset.range 330,
         (660 + j) * (1319 - j)):ℕ):ℚ) / ((660 + (i:ℚ)) * (1319 - (i:ℚ)))
       =
     ∏ j in (Finset.range 330).erase i, (660 + j) * (1319 - j) := by
  rw [←Finset.prod_erase_mul _ _ hi]
  rw [Finset.mem_range] at hi
  push_cast
  have h1 : (((1319 - i):ℕ):ℚ) = 1319 - (i:ℚ) := by
    have : i ≤ 1319 := by omega
    simp_all only [Nat.cast_sub, Nat.cast_ofNat]
  rw [h1, mul_div_assoc]
  have h2 : ((660 + (i:ℚ)) * (1319 - (i:ℚ))) /
              ((660 + (i:ℚ)) * (1319 - (i:ℚ))) = 1 := by
    have h3 : (660 + (i:ℚ)) * (1319 - (i:ℚ)) ≠ 0 := by
      have h4 : 0 ≤ (i: ℚ) := by positivity
      have h5 : (i: ℚ) < 330 := by norm_cast
      nlinarith
    exact div_self h3
  rw [h2, mul_one]

lemma lemma9 :
    (∑ i in Finset.range 330, 1 / ((660 + (i:ℚ)) * (1319 - (i:ℚ)))) *
      (((∏ j in Finset.range 330, (660 + j) * (1319 - j)):ℕ):ℚ) =
    (∑ i in Finset.range 330, ∏ j in (Finset.range 330).erase i,
         (660 + j) * (1319 - j)) := by
  simp_rw [Finset.sum_mul, div_mul_eq_mul_div, one_mul]
  rw [Finset.sum_congr rfl lemma9']
  push_cast
  rfl

snip end

problem imo1979_p1 (p q : ℤ) (hp : 0 < p) (hq : 0 < q)
    (h : (p : ℚ) / q = ∑ i in Finset.range 1319, (-1 : ℚ)^i / (i + 1)) :
    1979 ∣ p := by
  -- we follow the solution from
  -- https://artofproblemsolving.com/wiki/index.php/1979_IMO_Problems/Problem_1

  rw [lemma3] at h
  have h1 : 2 * ∑ i in Finset.range 659, 1 / (2 * ((i:ℚ) + 1)) =
              ∑ i in Finset.range 659, 1 / ((i:ℚ) + 1) := by
    rw [Finset.mul_sum, Finset.sum_congr rfl]
    intro x _
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
  have h4 :
    ∀ i ∈ Finset.range 330,
      1 / ((((659 + i):ℕ):ℚ) + 1) + 1 / ((((659 + (2 * 330 - 1 - i)):ℕ):ℚ) + 1) =
      1979 / ((660 + (i:ℚ)) * (1319 - (i:ℚ))) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have h5 : (((659 + i) : ℕ) : ℚ) + 1 = 660 + (i : ℚ) := by
      push_cast; linarith
    have h6 : (((659 + (2 * 330 - 1 - i)):ℕ):ℚ) + 1 = 1319 - (i:ℚ) := by
      rw [show 2 * 330 - 1 - i = 659 - i by omega]
      rw [show 659 + (659 - i) = 1318 - i by omega]
      have h10 : (((1318 - i):ℕ):ℚ) = 1318 - ↑i := by
        have : i ≤ 1318 := by omega
        rw [Nat.cast_sub this]
        rfl
      rw [h10]
      ring
    rw [h5, h6]; clear h5 h6
    have : (1319 : ℚ) - i ≠ 0 := by
      have h8 : 1319 ≠ i := by omega
      intro H
      have h9 : 1319 = (i : ℚ) := by linarith
      norm_cast at h9
    field_simp; norm_num1

  rw [Finset.sum_congr rfl h4] at h; clear h4
  rw [show (1979 : ℚ) = 1979 * 1 by rfl] at h
  simp_rw [mul_div_assoc] at h
  rw [←Finset.mul_sum] at h
  let s : ℕ := ∏ i in Finset.range 330, (660 + i) * (1319 - i)
  let sq := (s : ℚ)
  have hpp : Nat.Prime 1979 := by norm_num1

  have hsqp : ¬ 1979 ∣ s := by
    have h30 : ∀ i ∈ Finset.range 330, ¬ 1979 ∣ (660 + i) * (1319 - i) := fun i hi ↦ by
      rw [Finset.mem_range] at hi
      intro H
      obtain ⟨v, hv⟩ | ⟨u, hu⟩ := (Nat.Prime.dvd_mul hpp).mp H
      · omega
      · clear H; omega -- see https://github.com/leanprover/std4/issues/562
    exact not_dvd_finset_prod (Nat.prime_iff.mp hpp) h30
  obtain ⟨p', rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_lt hp)
  obtain ⟨q', rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_lt hq)
  simp only [Int.cast_ofNat] at h
  suffices H : 1979 ∣ p' from Int.ofNat_dvd.mpr H
  have hqq0 : (q':ℚ) ≠ 0 := lemma8 _ hq
  rw [div_eq_iff hqq0] at h
  apply_fun (· * sq) at h
  have h41 :
     (1979 * ∑ i in Finset.range 330, 1 / ((660 + (i:ℚ)) * (1319 - (i:ℚ)))) * (q':ℚ) * sq
     = 1979 * (q':ℚ) *
        ((∑ i in Finset.range 330, 1 / ((660 + (i:ℚ)) * (1319 - (i:ℚ)))) * sq) := by
   ac_rfl
  rw [h41] at h; clear h41
  rw [lemma9] at h
  rw [← Nat.cast_mul, show (1979:ℚ) = ((1979:ℕ):ℚ) by rfl,
      ← Nat.cast_mul, ← Nat.cast_mul] at h
  replace h := Nat.cast_inj.mp h
  rw [Nat.mul_assoc] at h
  have h20 : 1979 ∣ p' * s :=
    ⟨(q' * ∑ i in Finset.range 330,
       ∏ j in Finset.erase (Finset.range 330) i, (660 + j) * (1319 - j)),
     h⟩
  have : Nat.Coprime 1979 s := (Nat.Prime.coprime_iff_not_dvd hpp).mpr hsqp
  exact (Nat.Coprime.dvd_mul_right this).mp h20
