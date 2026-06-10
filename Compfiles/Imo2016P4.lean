/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benpigchu
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Olympiad 2016, Problem 4

A set of positive integers is called *fragrant* if it contains
at least two elements and each of its elements has a prime
factor in common with at least one of the other elements.
Let P(n) = n² + n + 1. What is the least possible value of
positive integer b such that there exists a non-negative integer
a for which the set

  { P(a + 1), P(a + 2), ..., P(a + b) }

is fragrant?
-/

namespace Imo2016P4

abbrev Fragrant (s : Set ℕ+) : Prop :=
  2 ≤ s.ncard ∧ ∀ m ∈ s, ∃ n ∈ s, n ≠ m ∧ ¬Nat.Coprime m n

abbrev P (n : ℕ) : ℕ := n^2 + n + 1

snip begin

def fragrantMap : ℕ → ℕ
  | 0 => 0
  | 1 => 5
  | 2 => 4
  | 3 => 6
  | 4 => 2
  | 5 => 1
  | 6 => 3
  | _ => 0

lemma P_inj : Function.Injective P := by
  apply StrictMono.injective
  intro i j hij
  rw [add_lt_add_iff_right]
  apply add_lt_add _ hij
  rw [pow_two, pow_two]
  exact Nat.mul_self_lt_mul_self hij

lemma ncard_set {a : ℕ} {b : ℕ+} : {p : ℕ+ | ∃ i : ℕ+, i ≤ b ∧ p = P (a + i)}.ncard = b := by
  have h : {p : ℕ+ | ∃ i : ℕ+, i ≤ b ∧ p = P (a + i)} =
      (fun i : ℕ+ ↦ (⟨P (a + i), by positivity⟩ : ℕ+)) '' Set.Icc 1 b := by
    ext p
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨i, hib, hp⟩
      exact ⟨i, ⟨one_le, hib⟩, PNat.coe_injective hp.symm⟩
    · rintro ⟨i, ⟨-, hib⟩, rfl⟩
      exact ⟨i, hib, rfl⟩
  have hinj : Function.Injective (fun i : ℕ+ ↦ (⟨P (a + i), by positivity⟩ : ℕ+)) := by
    intro i j hij
    have h2 := P_inj (Subtype.mk_eq_mk.mp hij)
    exact PNat.coe_injective (by lia)
  calc {p : ℕ+ | ∃ i : ℕ+, i ≤ b ∧ p = P (a + i)}.ncard
      = ((fun i : ℕ+ ↦ (⟨P (a + i), by positivity⟩ : ℕ+)) '' Set.Icc 1 b).ncard :=
        congrArg Set.ncard h
    _ = (Set.Icc 1 b).ncard := Set.ncard_image_of_injective _ hinj
    _ = (Finset.Icc 1 b).card := by rw [← Finset.coe_Icc, Set.ncard_coe_finset]
    _ = b := by rw [PNat.card_Icc]; simp

lemma two_not_dvd_P (n : ℕ) : ¬ 2 ∣ P n := by
  have h : 2 ∣ n * (n + 1) := Even.two_dvd (Nat.even_mul_succ_self n)
  have hP : P n = n * (n + 1) + 1 := by simp only [P]; ring
  lia

lemma nine_not_dvd_P (n : ℕ) : ¬ 9 ∣ P n := by
  intro h
  obtain ⟨m, hm⟩ : ∃ m, n = 3 * m ∨ n = 3 * m + 1 ∨ n = 3 * m + 2 := ⟨n / 3, by lia⟩
  rcases hm with rfl | rfl | rfl
  · rw [show P (3 * m) = 9 * m ^ 2 + 3 * m + 1 from by simp only [P]; ring] at h
    lia
  · rw [show P (3 * m + 1) = 9 * (m ^ 2 + m) + 3 from by simp only [P]; ring] at h
    lia
  · rw [show P (3 * m + 2) = 9 * m ^ 2 + 15 * m + 7 from by simp only [P]; ring] at h
    lia

lemma dvd_of_dvd_two_mul {g x : ℕ} (hg : ¬ 2 ∣ g) (h : g ∣ 2 * x) : g ∣ x :=
  ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hg).symm.dvd_of_dvd_mul_left h

/-- Adjacent values of `P` are coprime: a common divisor `g` is odd (values of `P` are odd)
and divides `P (b+1) - P b = 2*(b+1)`, hence divides `b+1`, hence divides `P b - b*(b+1) = 1`. -/
lemma coprime_P_succ (b : ℕ) : Nat.Coprime (P (b + 1)) (P b) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  set g := (P (b + 1)).gcd (P b) with hg
  have hg1 : g ∣ P (b + 1) := Nat.gcd_dvd_left _ _
  have hg2 : g ∣ P b := Nat.gcd_dvd_right _ _
  have hodd : ¬ 2 ∣ g := fun h ↦ two_not_dvd_P b (h.trans hg2)
  have h1 : g ∣ b + 1 := by
    refine dvd_of_dvd_two_mul hodd ((Nat.dvd_add_right hg2).mp ?_)
    rwa [show P b + 2 * (b + 1) = P (b + 1) from by simp only [P]; ring]
  refine Nat.dvd_one.mp ((Nat.dvd_add_right (h1.mul_left b)).mp ?_)
  rwa [show b * (b + 1) + 1 = P b from by simp only [P]; ring]

/-- The gcd of values of `P` at distance two divides 7. -/
lemma gcd_P_add_two_dvd (b : ℕ) : (P (b + 2)).gcd (P b) ∣ 7 := by
  set g := (P (b + 2)).gcd (P b) with hg
  have hg1 : g ∣ P (b + 2) := Nat.gcd_dvd_left _ _
  have hg2 : g ∣ P b := Nat.gcd_dvd_right _ _
  have hodd : ¬ 2 ∣ g := fun h ↦ two_not_dvd_P b (h.trans hg2)
  have h1 : g ∣ 2 * b + 3 := by
    refine dvd_of_dvd_two_mul hodd ((Nat.dvd_add_right hg2).mp ?_)
    rwa [show P b + 2 * (2 * b + 3) = P (b + 2) from by simp only [P]; ring]
  have h2 : g ∣ 8 * b + 5 := by
    have h := h1.mul_left (2 * b + 3)
    rw [show (2 * b + 3) * (2 * b + 3) = 4 * P b + (8 * b + 5) from by simp only [P]; ring] at h
    exact (Nat.dvd_add_right (hg2.mul_left 4)).mp h
  have h3 := h1.mul_left 4
  rw [show 4 * (2 * b + 3) = (8 * b + 5) + 7 from by ring] at h3
  exact (Nat.dvd_add_right h2).mp h3

/-- The gcd of values of `P` at distance three divides 3. -/
lemma gcd_P_add_three_dvd (b : ℕ) : (P (b + 3)).gcd (P b) ∣ 3 := by
  set g := (P (b + 3)).gcd (P b) with hg
  have hg1 : g ∣ P (b + 3) := Nat.gcd_dvd_left _ _
  have hg2 : g ∣ P b := Nat.gcd_dvd_right _ _
  have hodd : ¬ 2 ∣ g := fun h ↦ two_not_dvd_P b (h.trans hg2)
  have h1 : g ∣ 3 * b + 6 := by
    refine dvd_of_dvd_two_mul hodd ((Nat.dvd_add_right hg2).mp ?_)
    rwa [show P b + 2 * (3 * b + 6) = P (b + 3) from by simp only [P]; ring]
  have h2 : g ∣ 27 * b + 27 := by
    have h := h1.mul_left (3 * b + 6)
    rw [show (3 * b + 6) * (3 * b + 6) = 9 * P b + (27 * b + 27) from by simp only [P]; ring] at h
    exact (Nat.dvd_add_right (hg2.mul_left 9)).mp h
  have h27 : g ∣ 27 := by
    have h := h1.mul_left 9
    rw [show 9 * (3 * b + 6) = (27 * b + 27) + 27 from by ring] at h
    exact (Nat.dvd_add_right h2).mp h
  -- since 9 never divides a value of P, the gcd must divide 3
  have h9 : ¬ 9 ∣ g := fun h ↦ nine_not_dvd_P b (h.trans hg2)
  obtain ⟨i, hi, hgi⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 3)).mp
    (show g ∣ 3 ^ 3 by norm_num; exact h27)
  rw [hgi] at h9 ⊢
  interval_cases i
  · norm_num
  · norm_num
  · exact absurd (by norm_num) h9
  · exact absurd (by norm_num) h9

/-- If values of `P` at distance two have a common factor, that factor is 7. -/
lemma seven_dvd_P_of_not_coprime {b : ℕ} (h : ¬Nat.Coprime (P (b + 2)) (P b)) :
    7 ∣ P (b + 2) ∧ 7 ∣ P b := by
  rw [Nat.coprime_iff_gcd_eq_one] at h
  have h7 : (P (b + 2)).gcd (P b) = 7 :=
    ((Nat.dvd_prime (by norm_num)).mp (gcd_P_add_two_dvd b)).resolve_left h
  exact ⟨h7 ▸ Nat.gcd_dvd_left _ _, h7 ▸ Nat.gcd_dvd_right _ _⟩

/-- If values of `P` at distance three have a common factor, that factor is 3. -/
lemma three_dvd_P_of_not_coprime {b : ℕ} (h : ¬Nat.Coprime (P (b + 3)) (P b)) :
    3 ∣ P (b + 3) ∧ 3 ∣ P b := by
  rw [Nat.coprime_iff_gcd_eq_one] at h
  have h3 : (P (b + 3)).gcd (P b) = 3 :=
    ((Nat.dvd_prime (by norm_num)).mp (gcd_P_add_three_dvd b)).resolve_left h
  have hl := Nat.gcd_dvd_left (P (b + 3)) (P b)
  have hr := Nat.gcd_dvd_right (P (b + 3)) (P b)
  rw [h3] at hl hr
  exact ⟨hl, hr⟩

snip end

determine Solution : ℕ+ := 6

problem imo2016_p4 :
    IsLeast
      {b : ℕ+ | ∃ a : ℕ, Fragrant {p | ∃ i : ℕ+, i ≤ b ∧ p = P (a + i)}}
      Solution := by
  rw [Solution]
  constructor
  · set a := 196
    use a
    constructor
    · rw [ncard_set]
      norm_num
    · intro m hm
      simp at *
      rcases hm with ⟨i, hi, hmi⟩
      rw [← PNat.coe_le_coe, PNat.val_ofNat] at hi
      set result := fragrantMap i.val
      set val := P (a + result)
      have hval : 0 < val := by
        simp [val, result, fragrantMap]
      use ⟨val, hval⟩
      have hi' := PNat.pos i
      constructorm* _ ∧ _
      · have hresult : 0 < result := by
          simp [result, fragrantMap]
          interval_cases i.val <;> simp
        use ⟨result, hresult⟩
        constructor
        · rw [← PNat.coe_le_coe, PNat.val_ofNat, PNat.mk_coe]
          simp [result, fragrantMap]
          interval_cases i.val <;> simp
        · simp [val]
      · rw [← PNat.coe_inj]
        simp [hmi, val, a, result, fragrantMap]
        interval_cases i.val <;> simp
      · rw [← PNat.coprime_coe, PNat.mk_coe]
        simp [hmi, val, a, result, fragrantMap, P]
        interval_cases i.val <;> simp
  · rw [lowerBounds]
    intro b hb
    rcases hb with ⟨a, hcard, ha⟩
    set S := {p : ℕ+| ∃ i : ℕ+, i ≤ b ∧ p = P (a + i)} with hS
    by_contra! hb'
    rw [ncard_set] at hcard
    rw [← PNat.coe_lt_coe, PNat.val_ofNat] at hb'
    -- For each index k, fragrance provides a partner index j sharing a prime factor.
    have partner : ∀ k : ℕ, 0 < k → k ≤ (b : ℕ) → ∃ j : ℕ, 0 < j ∧ j ≤ (b : ℕ) ∧ j ≠ k ∧
        ¬Nat.Coprime (P (a + k)) (P (a + j)) := by
      intro k hk hkb
      have hmem : (⟨P (a + k), by positivity⟩ : ℕ+) ∈ S := by
        refine ⟨⟨k, hk⟩, ?_, rfl⟩
        rw [← PNat.coe_le_coe]
        exact hkb
      obtain ⟨n, ⟨j, hjb, hj⟩, hne, hncop⟩ := ha _ hmem
      refine ⟨j, j.pos, by exact_mod_cast hjb, ?_, ?_⟩
      · intro hjk
        exact hne (PNat.coe_injective (by rw [hj, hjk]; rfl))
      · rw [hj] at hncop
        exact hncop
    interval_cases hb : b.val
    · -- b = 2: the partner of index 1 must be index 2, but adjacent values are coprime.
      obtain ⟨j, hj0, hjb, hjne, hp⟩ := partner 1 one_pos (by lia)
      interval_cases j
      · exact hjne rfl
      · rw [Nat.coprime_comm] at hp
        exact hp (coprime_P_succ (a + 1))
    · -- b = 3: the partner of index 2 must be adjacent to it.
      obtain ⟨j, hj0, hjb, hjne, hp⟩ := partner 2 two_pos (by lia)
      interval_cases j
      · exact hp (coprime_P_succ (a + 1))
      · exact hjne rfl
      · rw [Nat.coprime_comm] at hp
        exact hp (coprime_P_succ (a + 2))
    · -- b = 4: 7 divides both P (a+2) and P (a+3), which are coprime.
      have h3 : 7 ∣ P (a + 3) := by
        obtain ⟨j, hj0, hjb, hjne, hp⟩ := partner 3 (by norm_num) (by lia)
        interval_cases j
        · exact (seven_dvd_P_of_not_coprime hp).1
        · exact absurd (coprime_P_succ (a + 2)) hp
        · exact absurd rfl hjne
        · rw [Nat.coprime_comm] at hp
          exact absurd (coprime_P_succ (a + 3)) hp
      have h2 : 7 ∣ P (a + 2) := by
        obtain ⟨j, hj0, hjb, hjne, hp⟩ := partner 2 two_pos (by lia)
        interval_cases j
        · exact absurd (coprime_P_succ (a + 1)) hp
        · exact absurd rfl hjne
        · rw [Nat.coprime_comm] at hp
          exact absurd (coprime_P_succ (a + 2)) hp
        · rw [Nat.coprime_comm] at hp
          exact (seven_dvd_P_of_not_coprime hp).2
      exact absurd (coprime_P_succ (a + 2))
        (Nat.not_coprime_of_dvd_of_dvd (by norm_num) h3 h2)
    · -- b = 5: 7 ∣ P (a+3), and P (a+2), P (a+4) are each divisible by 7 or 3.
      have h3 : 7 ∣ P (a + 3) := by
        obtain ⟨j, hj0, hjb, hjne, hp⟩ := partner 3 (by norm_num) (by lia)
        interval_cases j
        · exact (seven_dvd_P_of_not_coprime hp).1
        · exact absurd (coprime_P_succ (a + 2)) hp
        · exact absurd rfl hjne
        · rw [Nat.coprime_comm] at hp
          exact absurd (coprime_P_succ (a + 3)) hp
        · rw [Nat.coprime_comm] at hp
          exact (seven_dvd_P_of_not_coprime hp).2
      have h2 : 7 ∣ P (a + 2) ∨ 3 ∣ P (a + 2) := by
        obtain ⟨j, hj0, hjb, hjne, hp⟩ := partner 2 two_pos (by lia)
        interval_cases j
        · exact absurd (coprime_P_succ (a + 1)) hp
        · exact absurd rfl hjne
        · rw [Nat.coprime_comm] at hp
          exact absurd (coprime_P_succ (a + 2)) hp
        · rw [Nat.coprime_comm] at hp
          exact .inl (seven_dvd_P_of_not_coprime hp).2
        · rw [Nat.coprime_comm] at hp
          exact .inr (three_dvd_P_of_not_coprime hp).2
      have h4 : 7 ∣ P (a + 4) ∨ 3 ∣ P (a + 4) := by
        obtain ⟨j, hj0, hjb, hjne, hp⟩ := partner 4 (by norm_num) (by lia)
        interval_cases j
        · exact .inr (three_dvd_P_of_not_coprime hp).1
        · exact .inl (seven_dvd_P_of_not_coprime hp).1
        · exact absurd (coprime_P_succ (a + 3)) hp
        · exact absurd rfl hjne
        · rw [Nat.coprime_comm] at hp
          exact absurd (coprime_P_succ (a + 4)) hp
      -- If 7 divides P (a+2) or P (a+4), it divides two adjacent values, contradiction.
      -- Otherwise 3 divides both P (a+2) and P (a+4), whose gcd divides 7, contradiction.
      rcases h2 with h2 | h2
      · exact absurd (coprime_P_succ (a + 2))
          (Nat.not_coprime_of_dvd_of_dvd (by norm_num) h3 h2)
      rcases h4 with h4 | h4
      · exact absurd (coprime_P_succ (a + 3))
          (Nat.not_coprime_of_dvd_of_dvd (by norm_num) h4 h3)
      · have h := (Nat.dvd_gcd h4 h2).trans (gcd_P_add_two_dvd (a + 2))
        norm_num at h

end Imo2016P4
