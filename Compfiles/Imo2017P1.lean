/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Roozbeh Yousefzadeh, David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file {
  tags := [.NumberTheory]
  importedFrom :=
    "https://github.com/roozbeh-yz/IMO-Steps/tree/main/Lean_v20/imo_proofs/imo_2017_p1.lean",
}

/-!
# International Mathematical Olympiad 2017, Problem 1

For any integer a₀ > 1, define the sequence

  aₙ₊₁ =   √aₙ, if aₙ is a perfect square
        or aₙ + 3 otherwise.

Find all values of a₀ for which there exists A such that aₙ = A for
infinitely many values of n.
-/

namespace Imo2017P1


determine solution_set : Set ℕ := {x | 0 < x ∧ 3 ∣ x}


snip begin

lemma aux_1 : ∀ y, y ≡ 2 [MOD 3] → ¬ IsSquare y := by
  rintro y hy₀ ⟨y, rfl⟩
  change _ = _ at hy₀
  rw [Nat.mul_mod] at hy₀
  mod_cases H : y % 3 <;>
    change _ % _ = _ % 3 at H <;> rw [H] at hy₀ <;> norm_num at hy₀

lemma aux_2_1
    (a : ℕ → ℕ → ℕ)
    (ha₁ : ∀ (x i : ℕ),
      (1 : ℕ) < x → if IsSquare (a x i)
                    then a x (i + (1 : ℕ)) = (a x i).sqrt
                    else a x (i + (1 : ℕ)) = a x i + (3 : ℕ))
    (x i j l : ℕ)
    (hx₀ : (1 : ℕ) < x)
    (hl₀ : ∀ m < l, i ≤ m → m < i + j → ¬IsSquare (a x m))
    (hl₁ : i ≤ l)
    (hl₂ : l < i + j) :
    a x l = a x i + (l - i) * (3 : ℕ) := by
  induction hl₁ with
  | refl => simp
  | step ih => grind

lemma aux_2_2
    (a : ℕ → ℕ → ℕ)
    (ha₁ : ∀ (x i : ℕ),
      (1 : ℕ) < x → if IsSquare (a x i)
                    then a x (i + (1 : ℕ)) = (a x i).sqrt
                    else a x (i + (1 : ℕ)) = a x i + (3 : ℕ))
    (x c i j t : ℕ)
    (hj₀ : j = (t - c) / (3 : ℕ))
    (hx₀ : (1 : ℕ) < x)
    (hi₀ : a x i = c)
    (hh₃ : c < t)
    (hh₄ : ∀ (y : ℕ), c ≤ y → y < t → ¬IsSquare y)
    (hc₂ : (3 : ℕ) ∣ t - c) :
    a x (i + j) = t := by
  have hj₁: ∀ k ≥ i, k < i + j → ¬ IsSquare (a x k) := by
    intro k
    refine Nat.strong_induction_on k ?_
    intro l hl₀ hl₁ hl₂
    by_cases hlp: i < l
    · have hl₃: a x l = a x i + (l - i) * 3 := by
        exact aux_2_1 a ha₁ x i j l hx₀ hl₀ hl₁ hl₂
      have hj₁: (t - c) = j * 3 :=
        Nat.eq_mul_of_div_eq_left hc₂ hj₀.symm
      refine hh₄ (a x l) ?_ ?_
      · rw [hl₃]
        linarith
      · rw [hl₃, hi₀]
        refine Nat.add_lt_of_lt_sub' ?_
        rw [hj₁]
        simp
        exact Nat.sub_lt_left_of_lt_add hl₁ hl₂
    · push_neg at hlp
      have hl₃: l = i := by exact Nat.le_antisymm hlp hl₁
      bound
  have hj₂: a x (i + j) = t := by
    have hj₂: a x (i + j) = a x i + j * 3 := by
      revert hj₁
      clear hj₀
      induction' j with d hd₀ hd₁
      · simp
      · intro hj₁
        rw [← add_assoc]
        have hd₁: ¬IsSquare (a x (i + d)) := by
          refine hj₁ (i + d) ?_ ?_
          · exact Nat.le_add_right i d
          · simp
        have hd₂ := ha₁ x (i + d) hx₀
        have hd₃: a x (i + d + (1 : ℕ)) = a x (i + d) + 3 := by simp_all only [↓reduceIte]
        have hd₄: a x (i + d) = a x i + d * (3 : ℕ) := by
          refine hd₀ ?_
          intro k hk₀ hk₁
          refine hj₁ k hk₀ ?_
          refine lt_trans hk₁ ?_
          exact Nat.lt_add_one (i + d)
        rw [hd₃, hd₄, add_mul, add_assoc]
    rw [hj₂, hi₀, hj₀]
    omega
  rw [← hj₂]

lemma aux_2_3
  (a : ℕ → ℕ → ℕ)
  (ha₁ : ∀ (x i : ℕ),
    (1 : ℕ) < x → if IsSquare (a x i)
                  then a x (i + (1 : ℕ)) = (a x i).sqrt
                  else a x (i + (1 : ℕ)) = a x i + (3 : ℕ))
  (x c i j t : ℕ)
  (hx₀ : (1 : ℕ) < x)
  (hi₀ : a x i = c)
  (hh₃ : c < t)
  (hh₄ : ∀ (k : ℕ), i ≤ k → k < i + j → ¬IsSquare (a x k))
  (hh₅ : 3 ∣ t - c)
  (hj₀ : j = (t - c) / (3 : ℕ)) :
  a x (i + j) = t := by
  have h₀: ∀ (k : ℕ), i ≤ k → k ≤ i + j → a x k = c + (k - i) * 3 := by
    intro k
    revert hh₄
    clear hj₀
    refine Nat.strong_induction_on k ?_
    intro d hd₀ hd₁ hd₂ hd₃
    by_cases hd₄: i < d
    · have hd₅: d - 1 + 1 = d := by omega
      have hd₆ := ha₁ x (d - 1) hx₀
      rw [hd₅] at hd₆
      have hd₇: ¬ IsSquare (a x (d - 1)) := by
        refine hd₁ (d - 1) ?_ ?_
        · exact Nat.le_sub_one_of_lt hd₄
        · linarith
      have hd₈: a x d = a x (d - 1) + 3 := by simp_all only [↓reduceIte]
      have hd₉: a x (d - 1) = c + (d - 1 - i) * (3 : ℕ) := by
        refine hd₀ (d - 1) ?_ ?_ ?_ ?_
        · exact Nat.sub_one_lt_of_lt hd₄
        · intro m hm₀ hm₁
          exact hd₁ m hm₀ hm₁
        · linarith
        · cutsat
      rw [hd₈, hd₉]
      omega
    · push_neg at hd₄
      have hd₅: d = i := by exact Nat.le_antisymm hd₄ hd₂
      rw [hd₅]
      bound
  have h₁: a x (i + j) = c + (j) * 3 := by
    have h₁₀: i ≤ i + j := by omega
    have h₁₁: i + j ≤ i + j := by exact Nat.le_refl (i + j)
    rw [h₀ (i + j) h₁₀ h₁₁]
    omega
  rw [h₁, hj₀]
  omega

lemma aux_2_4
  (a : ℕ → ℕ → ℕ)
  (ha₁ : ∀ (x i : ℕ),
    (1 : ℕ) < x → if IsSquare (a x i)
                  then a x (i + (1 : ℕ)) = (a x i).sqrt
                  else a x (i + (1 : ℕ)) = a x i + (3 : ℕ))
  (x c i j : ℕ)
  (hj₀ : j = ((c.sqrt + (2 : ℕ)) ^ (2 : ℕ) - c) / (3 : ℕ))
  (hx₀ : (1 : ℕ) < x)
  (hi₀ : a x i = c)
  (hh₃ : c < (c.sqrt + (1 : ℕ)) ^ (2 : ℕ))
  (hh₄ : ∀ (y : ℕ), c ≤ y → y < (c.sqrt + (1 : ℕ)) ^ (2 : ℕ) → ¬IsSquare y)
  (hh₁ : c % (3 : ℕ) ≠ ((c.sqrt + (1 : ℕ)) ^ (2 : ℕ)) % 3) :
  ∀ (k : ℕ), i ≤ k → k < i + j → ¬IsSquare (a x k) := by
  intro k
  have h₀: ∀ y, (c.sqrt + (1 : ℕ)) ^ (2 : ℕ) < y →
                        y < (c.sqrt + (2 : ℕ)) ^ (2 : ℕ) → ¬ IsSquare y := by
    intro y hy₀ hy₁
    contrapose! hy₀
    obtain ⟨r, hr₀⟩ := hy₀
    rw [hr₀, ← pow_two] at hy₁
    have hr₁: r < c.sqrt + 2 := by exact lt_of_pow_lt_pow_left' (2 : ℕ) hy₁
    rw [hr₀, ← pow_two]
    refine Nat.pow_le_pow_left ?_ 2
    exact Nat.le_of_lt_succ hr₁
  refine Nat.strong_induction_on k ?_
  intro l hl₀ hl₁ hl₂
  by_cases hlp: i < l
  · have hl₃: a x l = a x i + (l - i) * 3 := by
      exact aux_2_1 a ha₁ x i j l hx₀ hl₀ hl₁ hl₂
    by_cases hl₄: a x l ≤ (c.sqrt + (1 : ℕ)) ^ (2 : ℕ)
    · obtain hl₅ | hl₅ := lt_or_eq_of_le hl₄
      · refine hh₄ (a x l) ?_ hl₅
        rw [hl₃, hi₀]
        simp
      · cutsat
    · push_neg at hl₄
      have h₃: a x l < (c.sqrt + (2 : ℕ)) ^ (2 : ℕ) := by
        rw [hl₃]
        have h₃₁: a x i + (l - i) * (3 : ℕ) < a x i + (i + j - i) * 3 := by omega
        refine lt_of_lt_of_le h₃₁ ?_
        rw [Nat.add_sub_cancel_left, hj₀, hi₀]
        omega
      exact h₀ (a x l) hl₄ h₃
  · push_neg at hlp
    have hl₃: l = i := Nat.le_antisymm hlp hl₁
    rw [hl₃, hi₀]
    refine hh₄ c ?_ hh₃
    exact Nat.le_refl c

lemma aux_2_5
  (a : ℕ → ℕ → ℕ)
  (ha₁ : ∀ (x i : ℕ),
    (1 : ℕ) < x → if IsSquare (a x i)
                  then a x (i + (1 : ℕ)) = (a x i).sqrt
                  else a x (i + (1 : ℕ)) = a x i + (3 : ℕ))
  (x c i j : ℕ)
  (hx₀ : (1 : ℕ) < x)
  (hi₀ : a x i = c)
  (hh₃ : c < (c.sqrt + (1 : ℕ)) ^ (2 : ℕ))
  (hh₄ : ∀ (y : ℕ), c ≤ y → y < (c.sqrt + (1 : ℕ)) ^ (2 : ℕ) → ¬IsSquare y)
  (hh₁ : c % (3 : ℕ) = (0 : ℕ))
  (hh₂ : c.sqrt % (3 : ℕ) = (0 : ℕ))
  (hj₀ : j = ((c.sqrt + (3 : ℕ)) ^ (2 : ℕ) - c) / (3 : ℕ)) :
  ∀ (k : ℕ), i ≤ k → k < i + ((c.sqrt + (3 : ℕ)) ^ (2 : ℕ) - c) / (3 : ℕ) → ¬IsSquare (a x k) := by
  intro k
  have h₀: ∀ y t, (c.sqrt + (t : ℕ)) ^ (2 : ℕ) < y →
                    y < (c.sqrt + t + (1 : ℕ)) ^ (2 : ℕ) → ¬ IsSquare y := by
    intro y t hy₀ hy₁
    contrapose! hy₀
    obtain ⟨r, hr₀⟩ := hy₀
    rw [hr₀, ← pow_two] at hy₁
    have hr₁: r < c.sqrt + t + 1 := by exact lt_of_pow_lt_pow_left' (2 : ℕ) hy₁
    rw [hr₀, ← pow_two]
    refine Nat.pow_le_pow_left ?_ 2
    exact Nat.le_of_lt_succ hr₁
  refine Nat.strong_induction_on k ?_
  intro l hl₀ hl₁ hl₂
  by_cases hlp: i < l
  · have hl₃: a x l = a x i + (l - i) * 3 := by
      exact aux_2_1 a ha₁ x i (((c.sqrt + (3 : ℕ)) ^ (2 : ℕ) - c) / (3 : ℕ)) l hx₀ hl₀ hl₁ hl₂
    by_cases hl₄: a x l ≤ (c.sqrt + (1 : ℕ)) ^ (2 : ℕ)
    · obtain hl₅ | hl₅ := lt_or_eq_of_le hl₄
      · refine hh₄ (a x l) ?_ hl₅
        rw [hl₃, hi₀]
        simp
      · exfalso
        have hl₆: (a x l) % 3 = 1 := by
          rw [hl₅, Nat.pow_mod]
          have hl₇: (c.sqrt + (1 : ℕ)) % (3 : ℕ) = 1 := by omega
          rw [hl₇, one_pow]
          group
        have hl₇: a x l % 3 = 0 := by omega
        rw [hl₆] at hl₇
        norm_num at hl₇
    · push_neg at hl₄
      by_cases hl₅: a x l ≤ (c.sqrt + (2 : ℕ)) ^ (2 : ℕ)
      · obtain hl₆ | hl₆ := lt_or_eq_of_le hl₅
        · exact h₀ (a x l) 1 hl₄ hl₆
        · exfalso
          have hl₇: (a x l) % 3 = 1 := by
            rw [hl₆, Nat.pow_mod]
            have hl₇: (c.sqrt + (2 : ℕ)) % (3 : ℕ) = 2 := by omega
            rw [hl₇]
          have hl₈: a x l % 3 = 0 := by omega
          rw [hl₇] at hl₈
          norm_num at hl₈
      · push_neg at hl₅
        have h₃: a x l < (c.sqrt + (3 : ℕ)) ^ (2 : ℕ) := by
          rw [hl₃]
          have h₃₁: a x i + (l - i) * (3 : ℕ) < a x i + (i + j - i) * 3 := by omega
          refine lt_of_lt_of_le h₃₁ ?_
          rw [Nat.add_sub_cancel_left, hj₀, hi₀]
          omega
        exact h₀ (a x l) 2 hl₅ h₃
  · push_neg at hlp
    have hl₃: l = i := by exact Nat.le_antisymm hlp hl₁
    rw [hl₃, hi₀]
    refine hh₄ c ?_ hh₃
    exact Nat.le_refl c

lemma aux_3
    (a : ℕ → ℕ → ℕ)
    (ha₁ : ∀ (x i : ℕ),
      (1 : ℕ) < x → if IsSquare (a x i)
                    then a x (i + (1 : ℕ)) = (a x i).sqrt
                    else a x (i + (1 : ℕ)) = a x i + (3 : ℕ))
    (x c i : ℕ)
    (hx₀ : x > (1 : ℕ))
    (S : Set ℕ)
    (hS₁ : S = Set.range (a x))
    (hi₀ : a x i = c)
    (hc₂ : ¬IsSquare c)
    (hhc : ¬c % (3 : ℕ) = (2 : ℕ)) :
    (c.sqrt + (1 : ℕ)) ^ (2 : ℕ) ∈ S ∨
    (c.sqrt + (2 : ℕ)) ^ (2 : ℕ) ∈ S ∨
    (c.sqrt + (3 : ℕ)) ^ (2 : ℕ) ∈ S := by
  have hh₁: c % 3 = 0 ∨ c % 3 = 1 := by omega
  have hh₂: c.sqrt % 3 = 0 ∨ c.sqrt % 3 = 1 ∨ c.sqrt % 3 = 2 := by omega
  have hh₃: c < (c.sqrt + (1 : ℕ)) ^ (2 : ℕ) := by exact Nat.lt_succ_sqrt' c
  have hh₅: c < (c.sqrt + (2 : ℕ)) ^ (2 : ℕ) := by
    refine lt_trans hh₃ ?_
    refine (Nat.pow_lt_pow_iff_left ?_).mpr ?_
    · exact Ne.symm (Nat.zero_ne_add_one (1 : ℕ))
    · exact Nat.lt_add_one (c.sqrt + (1 : ℕ))
  have hh₆: c < (c.sqrt + (3 : ℕ)) ^ (2 : ℕ) := by
    refine lt_trans hh₃ ?_
    refine (Nat.pow_lt_pow_iff_left ?_).mpr ?_
    · exact Ne.symm (Nat.zero_ne_add_one (1 : ℕ))
    · simp
  have hh₄: ∀ y ≥ c, y < (c.sqrt + (1 : ℕ)) ^ (2 : ℕ) → ¬ IsSquare y := by
    intro y hy₀ hy₁
    have hy₂: (c.sqrt) ^ (2 : ℕ) < y := by
      refine lt_of_lt_of_le ?_ hy₀
      contrapose! hc₂
      have hc₃: c.sqrt ^ (2 : ℕ) ≤ c := by exact Nat.sqrt_le' c
      have hc₄: c = c.sqrt ^ 2 := by exact Nat.le_antisymm hc₂ hc₃
      rw [hc₄]
      exact IsSquare.sq c.sqrt
    contrapose! hy₂
    obtain ⟨r, hr₀⟩ := hy₂
    rw [hr₀, ← pow_two] at hy₁
    have hr₁: r < c.sqrt + 1 := by exact lt_of_pow_lt_pow_left' (2 : ℕ) hy₁
    rw [hr₀, ← pow_two]
    refine Nat.pow_le_pow_left ?_ 2
    exact Nat.le_of_lt_succ hr₁
  rw [hS₁]
  obtain hh₁ | hh₁ := hh₁
  · let j : ℕ := ((c.sqrt + (3 : ℕ) - c.sqrt % 3) ^ (2 : ℕ) - c) / (3 : ℕ)
    obtain hh₂ | hh₂ := hh₂
    · right; right
      have hj₀: j = ((c.sqrt + (3 : ℕ) - c.sqrt % (3 : ℕ)) ^ (2 : ℕ) - c) / (3 : ℕ) := by rfl
      rw [hh₂] at hj₀
      simp at hj₀
      simp_all
      use (i + j)
      refine aux_2_3 a ha₁ x c i j ((c.sqrt + (3 : ℕ)) ^ (2 : ℕ)) hx₀ hi₀ hh₆ ?_ ?_ hj₀
      · simp_all
        exact aux_2_5 a ha₁ x c i j hx₀ hi₀ hh₃ hh₄ hh₁ hh₂ hj₀
      · refine Nat.dvd_of_mod_eq_zero ?_
        refine Nat.sub_mod_eq_zero_of_mod_eq ?_
        rw [hh₁]
        rw [Nat.pow_mod]
        have h₀: (c.sqrt + (3 : ℕ)) % (3 : ℕ) = 0 := by omega
        rw [h₀]
    obtain hh₂ | hh₂ := hh₂
    · right; left
      have hj₀: j = ((c.sqrt + (3 : ℕ) - c.sqrt % (3 : ℕ)) ^ (2 : ℕ) - c) / (3 : ℕ) := by rfl
      rw [hh₂] at hj₀
      simp at hj₀
      simp_all
      use (i + j)
      refine aux_2_3 a ha₁ x c i j ((c.sqrt + (2 : ℕ)) ^ (2 : ℕ)) hx₀ hi₀ hh₅ ?_ ?_ hj₀
      · intro k hk₀ hk₁
        refine aux_2_4 a ha₁ x c i j hj₀ hx₀ hi₀ hh₃ hh₄ ?_ k hk₀ hk₁
        have hc₂: (c.sqrt + (1 : ℕ)) % (3 : ℕ) = 2 := by omega
        rw [hh₁, Nat.pow_mod, hc₂]
        finiteness
      · refine Nat.dvd_of_mod_eq_zero ?_
        refine Nat.sub_mod_eq_zero_of_mod_eq ?_
        rw [hh₁]
        rw [Nat.pow_mod]
        have h₀: (c.sqrt + (2 : ℕ)) % (3 : ℕ) = 0 := by omega
        rw [h₀]
    · left
      have hj₀: j = ((c.sqrt + (3 : ℕ) - c.sqrt % (3 : ℕ)) ^ (2 : ℕ) - c) / (3 : ℕ) := by rfl
      rw [hh₂] at hj₀
      simp at hj₀
      simp_all
      use (i + j)
      refine aux_2_2 a ha₁ x c i j ((c.sqrt + (1 : ℕ)) ^ (2 : ℕ)) hj₀ hx₀ hi₀ hh₃ hh₄ ?_
      refine Nat.dvd_of_mod_eq_zero ?_
      refine Nat.sub_mod_eq_zero_of_mod_eq ?_
      rw [hh₁]
      rw [Nat.pow_mod]
      have h₀: (c.sqrt + (1 : ℕ)) % (3 : ℕ) = 0 := by omega
      rw [h₀]
  · obtain hh₂ | hh₂ := hh₂
    · let j : ℕ := ((c.sqrt + (1 : ℕ)) ^ (2 : ℕ) - c) / (3 : ℕ)
      have hj₀: a x (i + j) = (c.sqrt + (1 : ℕ)) ^ (2 : ℕ) := by
        simp_all
        have hc₂: (3 : ℕ) ∣ (c.sqrt + (1 : ℕ)) ^ (2 : ℕ) - c := by
          refine Nat.dvd_of_mod_eq_zero ?_
          refine Nat.sub_mod_eq_zero_of_mod_eq ?_
          rw [hh₁]
          rw [Nat.pow_mod]
          have h₀: (c.sqrt + (1 : ℕ)) % (3 : ℕ) = 1 := by omega
          rw [h₀]
        exact aux_2_2 a ha₁ x c i j ((c.sqrt + (1 : ℕ)) ^ (2 : ℕ)) rfl hx₀ hi₀ hh₃ hh₄ hc₂
      left
      rw [← hj₀]
      exact Set.mem_range_self (i + j)
    obtain hh₂ | hh₂ := hh₂
    · let j : ℕ := ((c.sqrt + (1 : ℕ)) ^ (2 : ℕ) - c) / (3 : ℕ)
      have hj₀: a x (i + j) = (c.sqrt + (1 : ℕ)) ^ (2 : ℕ) := by
        have hc₃: (3 : ℕ) ∣ (c.sqrt + (1 : ℕ)) ^ (2 : ℕ) - c := by
          refine Nat.dvd_of_mod_eq_zero ?_
          refine Nat.sub_mod_eq_zero_of_mod_eq ?_
          rw [hh₁]
          rw [Nat.pow_mod]
          have h₀: (c.sqrt + (1 : ℕ)) % (3 : ℕ) = 2 := by omega
          rw [h₀]
        exact aux_2_2 a ha₁ x c i j ((c.sqrt + (1 : ℕ)) ^ (2 : ℕ)) rfl hx₀ hi₀ hh₃ hh₄ hc₃
      left
      rw [← hj₀]
      exact Set.mem_range_self (i + j)
    · let j : ℕ := ((c.sqrt + (2 : ℕ)) ^ (2 : ℕ) - c) / (3 : ℕ)
      have hj₀: a x (i + j) = (c.sqrt + (2 : ℕ)) ^ (2 : ℕ) := by
        refine aux_2_3 a ha₁ x c i j ((c.sqrt + (2 : ℕ)) ^ (2 : ℕ)) hx₀ hi₀ hh₅ ?_ ?_ rfl
        · simp_all
          intro k hk₀ hk₁
          refine aux_2_4 a ha₁ x c i j rfl hx₀ hi₀ hh₃ hh₄ ?_ k hk₀ hk₁
          have hc₂: (c.sqrt + (1 : ℕ)) % (3 : ℕ) = 0 := by omega
          rw [hh₁, Nat.pow_mod, hc₂]
          finiteness
        · refine Nat.dvd_of_mod_eq_zero ?_
          refine Nat.sub_mod_eq_zero_of_mod_eq ?_
          rw [hh₁]
          rw [Nat.pow_mod]
          have h₀: (c.sqrt + (2 : ℕ)) % (3 : ℕ) = 1 := by omega
          rw [h₀]
      right; left
      rw [← hj₀]
      exact Set.mem_range_self (i + j)

theorem aux_4
  (a : ℕ → ℕ → ℕ)
  (ha₁ : ∀ x i, 1 < x → if IsSquare (a x i)
                        then a x (i + 1) = Nat.sqrt (a x i)
                        else a x (i + 1) = a x i + 3) :
  ∀ x > 1, (∃ j, a x j ≡ 2 [MOD 3]) → (∀ A, {n | a x n = A}.Finite) := by
  intro x hx₀ hx₁ A
  obtain ⟨i, hi₀⟩ := hx₁
  rw [Set.finite_iff_bddBelow_bddAbove]
  constructor
  · simp
  · let c : ℕ := a x i
    have h₁: StrictMonoOn (a x) (Set.Ici i) := by
      intro j hj₀ k hk₀ hj₁
      have hc₈: c ≡ 2 [MOD 3] := by exact hi₀
      have h₂: ∀ l ≥ i, a x l = c + (l - i) * 3 := by
        intro l
        refine Nat.strong_induction_on l ?_
        intro d hd₀ hd₁
        by_cases hd₃: i < d
        · have hd₄: a x (d - 1) = c + (d - 1 - i) * (3 : ℕ) := by
            refine hd₀ (d - 1) ?_ ?_
            · exact Nat.sub_one_lt_of_lt hd₃
            · exact Nat.le_sub_one_of_lt hd₃
          have hd₅: ¬IsSquare (a x (d - 1)) := by
            have hh₀: ∀ m ≥ i, a x m ≡ 2 [MOD 3] := by
              intro m hm₀
              refine Nat.le_induction hc₈ ?_ m hm₀
              intro t _ ht₁
              have ht₂: ¬ IsSquare (a x t) := by exact aux_1 (a x t) ht₁
              have ht₃ := ha₁ x t hx₀
              have ht₄: a x (t + (1 : ℕ)) = a x t + (3 : ℕ) := by simp_all only [↓reduceIte]
              rw [ht₄]
              have ht₅: a x t + 3 ≡ 2 + 3 [MOD (3 : ℕ)] := by exact Nat.ModEq.add_right (3 : ℕ) ht₁
              exact ht₅
            refine aux_1 (a x (d - 1)) ?_
            refine hh₀ (d - 1) ?_
            exact Nat.le_sub_one_of_lt hd₃
          have hd₆ := ha₁ x (d - 1) hx₀
          cutsat
        · cutsat
      rw [h₂ j hj₀, h₂ k hk₀]
      simp
      exact Nat.sub_lt_sub_right hj₀ hj₁
    rw [bddAbove_iff_subset_Iic]
    have h₂: {n : ℕ | a x n = A} = {n : ℕ | a x n = A ∧ i ≤ n} ∪ {n : ℕ | a x n = A ∧ n < i} := by
      ext j
      simp
      omega
    by_cases h₃: ∃ j, a x j = A ∧ i ≤ j
    · obtain ⟨j, hj₀⟩ := h₃
      use j
      intro k hk₀
      simp_all
      obtain hk₀ | hk₀ := hk₀
      · contrapose! hk₀
        intro hk₁
        exfalso
        have hk₂: k ∈ Set.Ici i := by
          refine Set.mem_Ici.mpr ?_
          refine le_trans hj₀.2 ?_
          exact Nat.le_of_succ_le hk₀
        have hj₁: j ∈ Set.Ici i := by exact Set.mem_Ici.mpr hj₀.2
        have hk₄: a x j ≠ a x k := by
          refine (Set.InjOn.ne_iff ?_ hj₁ hk₂).mpr (Nat.ne_of_lt hk₀)
          exact StrictMonoOn.injOn h₁
        bound
      · refine le_trans ?_ hj₀.2
        exact le_of_lt hk₀.2
    · push_neg at h₃
      have h₄: {n : ℕ | a x n = A ∧ i ≤ n} = ∅ := by
        refine Set.sep_eq_empty_iff_mem_false.mpr ?_
        simp
        intro j hj₀
        exact h₃ j hj₀
      rw [h₂, h₄, Set.empty_union]
      use i
      intro j hj₀
      simp_all
      exact le_of_lt hj₀.2

theorem aux_5
    (a : ℕ → ℕ → ℕ)
    (ha₀ : ∀ x, a x 0 = x)
    (ha₁ : ∀ x i, 1 < x → if IsSquare (a x i)
                          then a x (i + 1) = Nat.sqrt (a x i)
                          else a x (i + 1) = a x i + 3) :
    ∀ x > 1, 3 ∣ x → ∀ i, 3 ∣ a x i := by
  intro x hx₀ hx₁ i
  refine Nat.strong_induction_on i ?_
  intro d hd₀
  by_cases hd₁: 0 < d
  · have hd₃: (3 : ℕ) ∣ a x (d - 1) := by
      refine hd₀ (d - 1) ?_
      exact Nat.sub_one_lt_of_lt hd₁
    have hd₅₀ := ha₁ x (d - 1) hx₀
    by_cases hd₄: IsSquare (a x (d - 1))
    · have hd₅: a x d = (a x (d - 1)).sqrt := by cutsat
      obtain ⟨t, ht₀⟩ := hd₄
      have ht₁: (t ^ (2 : ℕ)).sqrt = t := by exact Nat.sqrt_eq' t
      rw [hd₅, ht₀, ← pow_two, ht₁]
      rw [ht₀, ← pow_two] at hd₃
      exact Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd₃
    · have hd₅: a x d = a x (d - 1) + 3 := by
        have hd₅₁: d - 1 + 1 = d := by exact Nat.sub_add_cancel hd₁
        simp_all only [↓reduceIte]
      rw [hd₅]
      exact Nat.dvd_add_self_right.mpr hd₃
  · push_neg at hd₁
    interval_cases d
    rw [ha₀]
    exact hx₁


snip end

problem imo2017_p1
    (a : ℕ → ℕ → ℕ)
    (ha₀: ∀ x, a x 0 = x)
    (ha₁: ∀ x i, 1 < x → if IsSquare (a x i)
                         then a x (i + 1) = Nat.sqrt (a x i)
                         else a x (i + 1) = a x i + 3) :
    ∀ x > 1, (∃ A, {n | a x n = A}.Infinite) ↔ x ∈ solution_set := by
  intro x hx₀
  simp
  let S : Set ℕ := Set.range (a x)
  have hS₀: BddBelow S := by exact OrderBot.bddBelow S
  have hS₁: ∃ c, IsLeast S c := by
    refine BddBelow.exists_isLeast_of_nonempty hS₀ ?_
    exact Set.range_nonempty (a x)
  obtain ⟨c, hc₀⟩ := hS₁
  have hc₁: c ∈ S := by exact Set.mem_of_mem_inter_left hc₀
  obtain ⟨i, hi₀⟩ := hc₁
  have hc₁ : 1 < c := by
    have h₀: ∀ j, 1 < a x j := by
      intro j
      refine Nat.strong_induction_on j ?_
      intro d hd₀
      by_cases hd₁: 0 < d
      · have hd₂ := ha₁ x (d - 1) hx₀
        have hd₃: d - 1 + 1 = d := by exact Nat.sub_add_cancel hd₁
        rw [hd₃] at hd₂
        have hd₄: 1 < a x (d - 1) := by
          refine hd₀ (d - 1) ?_
          exact Nat.sub_one_lt_of_lt hd₁
        by_cases hd₅: IsSquare (a x (d - (1 : ℕ)))
        · have hd₆: a x d = (a x (d - (1 : ℕ))).sqrt := by bound
          rw [hd₆]
          have hd₇: 2 ^ 2 ≤ (a x (d - (1 : ℕ))) := by
            contrapose! hd₅
            interval_cases (a x (d - (1 : ℕ)))
            · exact fun x ↦ match x with | ⟨_ + 3, hn⟩ => nomatch hn
            · exact fun x ↦ match x with | ⟨_ + 4, hn⟩ => nomatch hn
          have hd₈: 2 ≤ (a x (d - (1 : ℕ))).sqrt := by exact Nat.le_sqrt'.mpr hd₇
          exact hd₈
        · have hd₆: a x d = a x (d - (1 : ℕ)) + 3 := by simp_all only [↓reduceIte]
          omega
      · have hd₂: d = 0 := Nat.eq_zero_of_not_pos hd₁
        rw [hd₂, ha₀]
        exact hx₀
    rw [← hi₀]
    exact h₀ i
  have hc₂: ¬ IsSquare c := by
    by_contra! hh₀
    have hh₁ := ha₁ x i hx₀
    have hh₂: a x (i + 1) = c.sqrt := by bound
    have hh₃: c.sqrt < c := by exact Nat.sqrt_lt_self hc₁
    have hh₄: c.sqrt ∈ S := by
      rw [← hh₂]
      exact Set.mem_range_self (i + (1 : ℕ))
    have hh₅: c ≤ c.sqrt := by
      have hh₆: c ∈ lowerBounds S := by exact Set.mem_of_mem_inter_right hc₀
      exact hh₆ hh₄
    omega
  by_cases hhc: c % 3 = 2
  · constructor
    · intro h₀
      exfalso
      have h₁: (∀ A, {n | a x n = A}.Finite) := by
        refine aux_4 a ha₁ x hx₀ ?_
        bound
      bound
    · intro ⟨h₀, h₁⟩
      exfalso
      have h₂: ∀ j, 3 ∣ a x j := by exact fun (j : ℕ) ↦ aux_5 a ha₀ ha₁ x hx₀ h₁ j
      have h₃: 3 ∣ c := by
        rw [← hi₀]
        exact h₂ i
      omega
  · have hc₃: c ≤ Nat.sqrt c + 3 := by
      have hh₀: (Nat.sqrt c + 1) ^ 2 ∈ S ∨ (Nat.sqrt c + 2) ^ 2 ∈ S ∨ (Nat.sqrt c + 3) ^ 2 ∈ S := by
        exact aux_3 a ha₁ x c i hx₀ S rfl hi₀ hc₂ hhc
      obtain hh₀ | hh₀ | hh₀ := hh₀
      · obtain ⟨j, hj₀⟩ := hh₀
        have hj₁: IsSquare (a x j) := by rw [hj₀]; exact IsSquare.sq (c.sqrt + (1 : ℕ))
        have hj₂ := ha₁ x j hx₀
        have hj₃: a x (j + 1) = (c.sqrt + (1 : ℕ)) := by
          rw [hj₀] at hj₂
          simp_all only [↓reduceIte]
          exact Nat.sqrt_eq' (c.sqrt + (1 : ℕ))
        have hj₄: a x (j + 1) ∈ S := by exact Set.mem_range_self (j + (1 : ℕ))
        have hj₅: c ≤ c.sqrt + (1 : ℕ) := by
          have hj₆: c ∈ lowerBounds S := by exact Set.mem_of_mem_inter_right hc₀
          rw [hj₃] at hj₄
          exact hj₆ hj₄
        refine le_trans hj₅ ?_
        simp
      · obtain ⟨j, hj₀⟩ := hh₀
        have hj₁: IsSquare (a x j) := by rw [hj₀]; exact IsSquare.sq (c.sqrt + (2 : ℕ))
        have hj₂ := ha₁ x j hx₀
        have hj₃: a x (j + 1) = (c.sqrt + (2 : ℕ)) := by
          rw [hj₀] at hj₂
          simp_all only [↓reduceIte]
          exact Nat.sqrt_eq' (c.sqrt + (2 : ℕ))
        have hj₄: a x (j + 1) ∈ S := by exact Set.mem_range_self (j + (1 : ℕ))
        have hj₅: c ≤ c.sqrt + (2 : ℕ) := by
          have hj₆: c ∈ lowerBounds S := by exact Set.mem_of_mem_inter_right hc₀
          rw [hj₃] at hj₄
          exact hj₆ hj₄
        exact Nat.le_succ_of_le hj₅
      · obtain ⟨j, hj₀⟩ := hh₀
        have hj₁: IsSquare (a x j) := by rw [hj₀]; exact IsSquare.sq (c.sqrt + (3 : ℕ))
        have hj₂ := ha₁ x j hx₀
        have hj₃: a x (j + 1) = (c.sqrt + (3 : ℕ)) := by
          rw [hj₀] at hj₂
          simp_all only [↓reduceIte]
          exact Nat.sqrt_eq' (c.sqrt + (3 : ℕ))
        have hj₄: a x (j + 1) ∈ S := by exact Set.mem_range_self (j + (1 : ℕ))
        have hj₆: c ∈ lowerBounds S := by exact Set.mem_of_mem_inter_right hc₀
        rw [hj₃] at hj₄
        exact hj₆ hj₄
    have hc₄: c ≤ 5 := by
      contrapose! hc₃
      refine Nat.add_lt_of_lt_sub ?_
      have hi₁: 2 ≠ 0 := by exact Ne.symm (Nat.zero_ne_add_one (1 : ℕ))
      refine (Nat.pow_lt_pow_iff_left hi₁).mp ?_
      have hc₄: c.sqrt ^ (2 : ℕ) ≤ c := by exact Nat.sqrt_le' c
      refine lt_of_le_of_lt hc₄ ?_
      rw [pow_two, Nat.mul_sub, Nat.sub_mul, Nat.sub_mul]
      ring_nf
      refine Nat.le_induction ?_ ?_ c hc₃
      · norm_num
      · intro d hd₀ hd₁
        simp_all
        refine Nat.add_lt_of_lt_sub ?_
        refine lt_trans hd₁ ?_
        ring_nf
        omega
    have hc₅: c ≠ 4 := by
      contrapose! hc₂
      rw [hc₂]
      use 2
    constructor
    · intro hx₁
      obtain ⟨A, hA₀⟩ := hx₁
      constructor
      · exact Nat.zero_lt_of_lt hx₀
      · contrapose! hA₀
        have hx₂: x ≡ 1 [MOD 3] ∨ x ≡ 2 [MOD 3] := by
          have hx₁₂: x % 3 = 1 ∨ x % 3 = 2 := by omega
          exact hx₁₂
        rw [Set.not_infinite]
        obtain hx₂ | hx₂ := hx₂
        · exfalso
          have hc₆: ¬(3 : ℕ) ∣ c := by
            have hh₀: ∀ j, ¬ 3 ∣ a x j := by
              intro j
              refine Nat.strong_induction_on j ?_
              intro d hd₀
              by_cases hd₁: 0 < d
              · have hd₂: d - 1 + 1 = d := Nat.sub_add_cancel hd₁
                have hd₃ := ha₁ x (d - 1) hx₀
                rw [hd₂] at hd₃
                have hd₄: ¬ 3 ∣ a x (d - 1) := by
                  refine hd₀ (d - 1) ?_
                  exact Nat.sub_one_lt_of_lt hd₁
                by_cases hd₅: IsSquare (a x (d - 1))
                · have hd₆: a x d = (a x (d - (1 : ℕ))).sqrt := by simp_all only [↓reduceIte]
                  rw [hd₆]
                  contrapose! hd₄
                  obtain ⟨r, hr₀⟩ := hd₅
                  rw [hr₀, ← pow_two]
                  refine dvd_pow ?_ (by norm_num)
                  have hr₁: (a x (d - (1 : ℕ))).sqrt = r := by
                    rw [hr₀]
                    exact Nat.sqrt_eq r
                  rw [← hr₁]
                  exact hd₄
                · have hd₆: a x d = a x (d - (1 : ℕ)) + (3 : ℕ) := by simp_all only [↓reduceIte]
                  rw [hd₆]
                  contrapose! hd₄
                  exact Nat.dvd_add_self_right.mp hd₄
              · have hd₂: d = 0 := Nat.eq_zero_of_not_pos hd₁
                rw [hd₂, ha₀]
                exact hA₀
            rw [← hi₀]
            exact hh₀ i
          have hc₇: c = 2 ∨ c = 5 := by omega
          have hc₈: c ≡ 2 [MOD 3] := by
            obtain rfl | rfl := hc₇ <;> rfl
          exact False.elim (hhc hc₈)
        · refine aux_4 a ha₁ x hx₀ ?_ A
          use 0
          rw [ha₀]
          exact hx₂
    · intro ⟨h₀, h₂⟩
      use 3
      have h₃: ∃ i, a x i = 3 := by
        have h₃₀: ∀ i, 3 ∣ a x i := by
          exact fun (i : ℕ) ↦ aux_5 a ha₀ ha₁ x hx₀ h₂ i
        have hc₅: c = 3 := by
          have hc₆: 3 ∣ c := by
            exact (Nat.ModEq.dvd_iff (congrFun (congrArg HMod.hMod hi₀) x) h₂).mp (h₃₀ i)
          interval_cases c
          all_goals try omega
        use i
        rw [hi₀, hc₅]
      obtain ⟨i, h₃⟩ := h₃
      have h₄: ∀ j, a x (i + j * 3) = 3 := by
        intro j
        induction' j with d hd₀
        · exact h₃
        · rw [add_mul, one_mul, ← add_assoc]
          have hd₁: a x (i + d * (3 : ℕ) + 1) = 6 := by
            have hh₀ := ha₁ x (i + d * (3 : ℕ)) hx₀
            have hh₁: ¬ IsSquare (3 : ℕ) := fun x ↦ match x with | ⟨_ + 4, hn⟩ => nomatch hn
            have hh₂: a x (i + d * (3 : ℕ) + (1 : ℕ)) = a x (i + d * (3 : ℕ)) + (3 : ℕ) := by
              rw [hd₀] at hh₀
              simp [hh₁] at hh₀
              rw [hd₀]
              exact hh₀
            rw [hh₂, hd₀]
          have hd₂: a x (i + d * (3 : ℕ) + 2) = 9 := by
            have hh₀ := ha₁ x (i + d * (3 : ℕ) + 1) hx₀
            have hh₁: ¬ IsSquare (6 : ℕ) := fun x ↦ match x with | ⟨_ + 7, hn⟩ => nomatch hn
            have hh₂: a x (i + d * (3 : ℕ) + (2 : ℕ)) = a x (i + d * (3 : ℕ) + 1) + (3 : ℕ) := by
              rw [hd₁] at hh₀
              simp [hh₁] at hh₀
              rw [hd₁]
              exact hh₀
            rw [hh₂, hd₁]
          have hd₃ := ha₁ x (i + d * (3 : ℕ) + (2 : ℕ)) hx₀
          rw [hd₂] at hd₃
          have hh₁: IsSquare (9 : ℕ) := ⟨3, rfl⟩
          norm_num [hh₁] at hd₃
          exact hd₃
      refine Set.infinite_iff_exists_gt.mpr ?_
      simp
      intro j
      use i + (j + 1) * 3
      constructor
      · exact h₄ (j + 1)
      · omega


end Imo2017P1
