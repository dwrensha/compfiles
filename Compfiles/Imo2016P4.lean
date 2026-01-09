/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benpigchu
-/

import Mathlib.Data.Set.Card
import Mathlib.Tactic

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
  set f : Fin b → ℕ+ := fun i : Fin b ↦ ⟨(P (a + i + 1)), (by simp : _)⟩
  have hset : Set.range f = {p : ℕ+ | ∃ i : ℕ+, i ≤ b ∧ p = P (a + i)} := by
    rw [Set.range_eq_iff]
    constructor
    · intro i
      simp [f]
      use ⟨i.val + 1, (by simp : _)⟩
      constructor
      · rw [← PNat.coe_le_coe, PNat.mk_coe]
        apply Nat.add_one_le_of_lt
        exact Fin.is_lt i
      · rw [PNat.mk_coe]
        ring
    · intro p hp
      rcases hp with ⟨i, hi, hi'⟩
      rw [← PNat.coe_le_coe] at hi
      have hival : i.val - 1 < b := by
        apply lt_of_lt_of_le _ hi
        apply Nat.sub_one_lt
        apply ne_of_gt
        exact PNat.pos i
      use ⟨i.val - 1, hival⟩
      apply PNat.eq
      rw [PNat.mk_coe, hi']
      simp [P]
      have hi'' : (1 : ℕ) ≤ ↑i := by
        apply PNat.one_le
      rw [add_assoc]
      rw [Nat.sub_add_cancel hi'']
  have hf : Function.Injective f := by
    intro i j hij
    simp [f] at hij
    rw [← PNat.coe_inj, PNat.mk_coe, PNat.mk_coe] at hij
    apply P_inj at hij
    apply Nat.add_right_cancel at hij
    apply Nat.add_left_cancel at hij
    exact Fin.eq_of_val_eq hij
  rw [← hset, Set.ncard_range_of_injective hf, Nat.card_fin]

lemma two_dvd_pow_two_add_self (x : ℤ) : ∃ k : ℤ, 2 * k + 1 = x ^ 2 + x + 1 := by
  mod_cases hx : x % 2
    <;> rw [Int.modEq_comm, Int.modEq_iff_dvd, dvd_iff_exists_eq_mul_right] at hx
    <;> rcases hx with ⟨k, hk⟩
    <;> rw [sub_eq_iff_eq_add] at hk
  · use k * (2 * k + 1)
    rw [hk]
    ring
  · use (2 * k + 1) * (k + 1)
    rw [hk]
    ring

lemma there_dvd_pow_two_add_self (x : ℤ) : ∃ k : ℤ, 3 * k + 1 = x ^ 2 + x + 1 ∨ 9 * k + 3 = x ^ 2 + x + 1 := by
  mod_cases hx : x % 3
    <;> rw [Int.modEq_comm, Int.modEq_iff_dvd, dvd_iff_exists_eq_mul_right] at hx
    <;> rcases hx with ⟨k, hk⟩
    <;> rw [sub_eq_iff_eq_add] at hk
  · use k * (3 * k + 1)
    left
    rw [hk]
    ring
  · use k * (k + 1)
    right
    rw [hk]
    ring
  · use (3 * k + 2) * (k + 1)
    left
    rw [hk]
    ring

lemma gcd_p_of_diff_one {a b : ℕ} (hab : a = b + 1) (hab' : ¬Nat.Coprime (P a) (P b)) : False := by
  have hpa := Nat.gcd_dvd_left (P a) (P b)
  have hpb := Nat.gcd_dvd_right (P a) (P b)
  rw [Nat.coprime_iff_gcd_eq_one] at hab'
  set p := (P a).gcd (P b) with hp
  simp [P] at hpa hpb
  rw [← Int.ofNat_dvd, Nat.cast_add, Nat.cast_add, Nat.cast_pow, Nat.cast_one] at hpa hpb
  rw [← Int.ofNat_inj, Nat.cast_add, Nat.cast_one] at hab
  rw [hab] at hpa
  ring_nf at hpa
  have h₁ := Int.dvd_sub hpa hpb
  ring_nf at h₁
  have h₂ := Int.dvd_sub (dvd_mul_of_dvd_left hpb 3) hpa
  ring_nf at h₂
  have h₃ := Int.dvd_sub (dvd_mul_of_dvd_left h₁ ↑b) h₂
  ring_nf at h₃
  have h₄ := Int.dvd_sub h₁ h₃
  ring_nf at h₄
  rcases two_dvd_pow_two_add_self (b : ℤ) with ⟨k, hk⟩
  have h₅ := hpb
  rw [← hk] at h₅
  have h₆ := Int.dvd_sub h₅ (dvd_mul_of_dvd_left h₄ k)
  ring_nf at h₆
  rw [Int.natCast_dvd, Int.natAbs_one, Nat.dvd_one] at h₆
  contrapose! hab'
  exact h₆

lemma gcd_p_of_diff_two {a b : ℕ} (hab : a = b + 2) (hab' : ¬Nat.Coprime (P a) (P b)) : Nat.gcd (P a) (P b) = 7 := by
  have hpa := Nat.gcd_dvd_left (P a) (P b)
  have hpb := Nat.gcd_dvd_right (P a) (P b)
  rw [Nat.coprime_iff_gcd_eq_one] at hab'
  set p := (P a).gcd (P b)
  simp [P] at hpa hpb
  rw [← Int.ofNat_dvd, Nat.cast_add, Nat.cast_add, Nat.cast_pow, Nat.cast_one] at hpa hpb
  rw [← Int.ofNat_inj, Nat.cast_add, Nat.cast_ofNat] at hab
  rw [hab] at hpa
  ring_nf at hpa
  have h₁ := Int.dvd_sub hpa hpb
  ring_nf at h₁
  have h₂ := Int.dvd_sub (dvd_mul_of_dvd_left hpb 5) hpa
  ring_nf at h₂
  have h₃ := Int.dvd_sub (dvd_mul_of_dvd_left h₁ ↑b) h₂
  ring_nf at h₃
  have h₄ := Int.dvd_sub (dvd_mul_of_dvd_left h₁ 3) (dvd_mul_of_dvd_left h₃ 2)
  ring_nf at h₄
  rcases two_dvd_pow_two_add_self (b : ℤ) with ⟨k, hk⟩
  have h₅ := hpb
  rw [← hk] at h₅
  have h₆ := Int.dvd_sub (dvd_mul_of_dvd_left h₅ 7) (dvd_mul_of_dvd_left h₄ k)
  ring_nf at h₆
  rw [Int.natCast_dvd] at h₆
  norm_num at h₆
  rw [Nat.dvd_prime (by norm_num : _)] at h₆
  rcases h₆ with h₆|h₆
  · contrapose! hab'
    exact h₆
  · exact h₆

lemma gcd_p_of_diff_three {a b : ℕ} (hab : a = b + 3) (hab' : ¬Nat.Coprime (P a) (P b)) : Nat.gcd (P a) (P b) = 3 := by
  have hpa := Nat.gcd_dvd_left (P a) (P b)
  have hpb := Nat.gcd_dvd_right (P a) (P b)
  rw [Nat.coprime_iff_gcd_eq_one] at hab'
  set p := (P a).gcd (P b)
  simp [P] at hpa hpb
  rw [← Int.ofNat_dvd, Nat.cast_add, Nat.cast_add, Nat.cast_pow, Nat.cast_one] at hpa hpb
  rw [← Int.ofNat_inj, Nat.cast_add, Nat.cast_ofNat] at hab
  rw [hab] at hpa
  ring_nf at hpa
  have h₁ := Int.dvd_sub hpa hpb
  ring_nf at h₁
  have h₂ := Int.dvd_sub (dvd_mul_of_dvd_left hpb 7) hpa
  ring_nf at h₂
  have h₃ := Int.dvd_sub (dvd_mul_of_dvd_left h₁ ↑b) h₂
  ring_nf at h₃
  have h₄ := Int.dvd_sub (dvd_mul_of_dvd_left h₁ 2) h₃
  ring_nf at h₄
  rcases two_dvd_pow_two_add_self (b : ℤ) with ⟨k, hk⟩
  have h₅ := hpb
  rw [← hk] at h₅
  have h₆ := Int.dvd_sub (dvd_mul_of_dvd_left h₅ 9) (dvd_mul_of_dvd_left h₄ k)
  ring_nf at h₆
  rcases there_dvd_pow_two_add_self (b : ℤ) with ⟨l, hl|hl⟩
  · have h₇ := hpb
    rw [← hl] at h₇
    have h₈ := Int.dvd_sub (dvd_mul_of_dvd_left h₇ 3) (dvd_mul_of_dvd_left h₆ l)
    ring_nf at h₈
    have h₉ := Int.dvd_sub h₇ (dvd_mul_of_dvd_left h₈ l)
    ring_nf at h₉
    rw [Int.natCast_dvd, Int.natAbs_one, Nat.dvd_one] at h₉
    contrapose! hab'
    exact h₉
  · have h₇ := hpb
    rw [← hl] at h₇
    have h₈ := Int.dvd_sub h₇ (dvd_mul_of_dvd_left h₆ l)
    ring_nf at h₈
    rw [Int.natCast_dvd] at h₈
    norm_num at h₈
    rw [Nat.dvd_prime (by norm_num : _)] at h₈
    rcases h₈ with h₈|h₈
    · contrapose! hab'
      exact h₈
    · exact h₈

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
    interval_cases hb : b.val
    · set pa1 : ℕ+ := ⟨(P (a + 1)), (by simp : _)⟩ with hpa1
      have hpa1S : pa1 ∈ S := by
        simp [S, hpa1]
        use ⟨1, (by norm_num : _)⟩
        simp
      rcases ha pa1 hpa1S with ⟨pi1, ⟨i1, hi1₁, hi1₂⟩, hpi1₁, hpi1₂⟩
      rw [← PNat.coe_le_coe, hb] at hi1₁
      rw [← PNat.coe_inj.ne, hi1₂, hpa1, PNat.mk_coe] at hpi1₁
      rw [hi1₂, hpa1, PNat.mk_coe] at hpi1₂
      have hi1 := i1.pos
      interval_cases i1.val
      · rw [ne_self_iff_false] at hpi1₁
        exact hpi1₁
      · rw [Nat.coprime_comm] at hpi1₂
        exact gcd_p_of_diff_one (by ring: (a + 2) = (a + 1) + 1) hpi1₂
    · set pa2 : ℕ+ := ⟨(P (a + 2)), (by simp : _)⟩ with hpa2
      have hpa2S : pa2 ∈ S := by
        simp [S, hpa2]
        use ⟨2, (by norm_num : _)⟩
        simp
        rw [← PNat.coe_le_coe, PNat.val_ofNat, hb]
        norm_num
      rcases ha pa2 hpa2S with ⟨pi2, ⟨i2, hi2₁, hi2₂⟩, hpi2₁, hpi2₂⟩
      rw [← PNat.coe_le_coe, hb] at hi2₁
      rw [← PNat.coe_inj.ne, hi2₂, hpa2, PNat.mk_coe] at hpi2₁
      rw [hi2₂, hpa2, PNat.mk_coe] at hpi2₂
      have hi2 := i2.pos
      interval_cases i2.val
      · exact gcd_p_of_diff_one (by ring: (a + 2) = (a + 1) + 1) hpi2₂
      · rw [ne_self_iff_false] at hpi2₁
        exact hpi2₁
      · rw [Nat.coprime_comm] at hpi2₂
        exact gcd_p_of_diff_one (by ring: (a + 3) = (a + 2) + 1) hpi2₂
    · set pa2 : ℕ+ := ⟨(P (a + 2)), (by simp : _)⟩ with hpa2
      have hpa2S : pa2 ∈ S := by
        simp [S, hpa2]
        use ⟨2, (by norm_num : _)⟩
        simp
        rw [← PNat.coe_le_coe, PNat.val_ofNat, hb]
        norm_num
      have hpa2' : 7 ∣ P (a + 2) := by
        rcases ha pa2 hpa2S with ⟨pi2, ⟨i2, hi2₁, hi2₂⟩, hpi2₁, hpi2₂⟩
        rw [← PNat.coe_le_coe, hb] at hi2₁
        rw [← PNat.coe_inj.ne, hi2₂, hpa2, PNat.mk_coe] at hpi2₁
        rw [hi2₂, hpa2, PNat.mk_coe] at hpi2₂
        have hi2 := i2.pos
        interval_cases i2.val
        · exfalso
          exact gcd_p_of_diff_one (by ring: (a + 2) = (a + 1) + 1) hpi2₂
        · exfalso
          rw [ne_self_iff_false] at hpi2₁
          exact hpi2₁
        · exfalso
          rw [Nat.coprime_comm] at hpi2₂
          exact gcd_p_of_diff_one (by ring: (a + 3) = (a + 2) + 1) hpi2₂
        · rw [Nat.coprime_comm] at hpi2₂
          have h := gcd_p_of_diff_two (by ring: (a + 4) = (a + 2) + 2) hpi2₂
          rw [← h]
          apply Nat.gcd_dvd_right
      set pa3 : ℕ+ := ⟨(P (a + 3)), (by simp : _)⟩ with hpa3
      have hpa3S : pa3 ∈ S := by
        simp [S, hpa3]
        use ⟨3, (by norm_num : _)⟩
        simp
        rw [← PNat.coe_le_coe, PNat.val_ofNat, hb]
        norm_num
      have hpa3' : 7 ∣ P (a + 3) := by
        rcases ha pa3 hpa3S with ⟨pi3, ⟨i3, hi3₁, hi3₂⟩, hpi3₁, hpi3₂⟩
        rw [← PNat.coe_le_coe, hb] at hi3₁
        rw [← PNat.coe_inj.ne, hi3₂, hpa3, PNat.mk_coe] at hpi3₁
        rw [hi3₂, hpa3, PNat.mk_coe] at hpi3₂
        have hi3 := i3.pos
        interval_cases i3.val
        · have h := gcd_p_of_diff_two (by ring: (a + 3) = (a + 1) + 2) hpi3₂
          rw [← h]
          apply Nat.gcd_dvd_left
        · exfalso
          exact gcd_p_of_diff_one (by ring: (a + 3) = (a + 2) + 1) hpi3₂
        · exfalso
          rw [ne_self_iff_false] at hpi3₁
          exact hpi3₁
        · exfalso
          rw [Nat.coprime_comm] at hpi3₂
          exact gcd_p_of_diff_one (by ring: (a + 4) = (a + 3) + 1) hpi3₂
      have h := Nat.not_coprime_of_dvd_of_dvd (by norm_num : 1 < 7) hpa3' hpa2'
      exact gcd_p_of_diff_one (by ring: (a + 3) = (a + 2) + 1) h
    · set pa3 : ℕ+ := ⟨(P (a + 3)), (by simp : _)⟩ with hpa3
      have hpa3S : pa3 ∈ S := by
        simp [S, hpa3]
        use ⟨3, (by norm_num : _)⟩
        simp
        rw [← PNat.coe_le_coe, PNat.val_ofNat, hb]
        norm_num
      have hpa3' : 7 ∣ P (a + 3) := by
        rcases ha pa3 hpa3S with ⟨pi3, ⟨i3, hi3₁, hi3₂⟩, hpi3₁, hpi3₂⟩
        rw [← PNat.coe_le_coe, hb] at hi3₁
        rw [← PNat.coe_inj.ne, hi3₂, hpa3, PNat.mk_coe] at hpi3₁
        rw [hi3₂, hpa3, PNat.mk_coe] at hpi3₂
        have hi3 := i3.pos
        interval_cases i3.val
        · have h := gcd_p_of_diff_two (by ring: (a + 3) = (a + 1) + 2) hpi3₂
          rw [← h]
          apply Nat.gcd_dvd_left
        · exfalso
          exact gcd_p_of_diff_one (by ring: (a + 3) = (a + 2) + 1) hpi3₂
        · exfalso
          rw [ne_self_iff_false] at hpi3₁
          exact hpi3₁
        · exfalso
          rw [Nat.coprime_comm] at hpi3₂
          exact gcd_p_of_diff_one (by ring: (a + 4) = (a + 3) + 1) hpi3₂
        · rw [Nat.coprime_comm] at hpi3₂
          have h := gcd_p_of_diff_two (by ring: (a + 5) = (a + 3) + 2) hpi3₂
          rw [← h]
          apply Nat.gcd_dvd_right
      set pa2 : ℕ+ := ⟨(P (a + 2)), (by simp : _)⟩ with hpa2
      have hpa2S : pa2 ∈ S := by
        simp [S, hpa2]
        use ⟨2, (by norm_num : _)⟩
        simp
        rw [← PNat.coe_le_coe, PNat.val_ofNat, hb]
        norm_num
      have hpa2' : 7 ∣ P (a + 2) ∨ 3 ∣ P (a + 2) := by
        rcases ha pa2 hpa2S with ⟨pi2, ⟨i2, hi2₁, hi2₂⟩, hpi2₁, hpi2₂⟩
        rw [← PNat.coe_le_coe, hb] at hi2₁
        rw [← PNat.coe_inj.ne, hi2₂, hpa2, PNat.mk_coe] at hpi2₁
        rw [hi2₂, hpa2, PNat.mk_coe] at hpi2₂
        have hi2 := i2.pos
        interval_cases i2.val
        · exfalso
          exact gcd_p_of_diff_one (by ring: (a + 2) = (a + 1) + 1) hpi2₂
        · exfalso
          rw [ne_self_iff_false] at hpi2₁
          exact hpi2₁
        · exfalso
          rw [Nat.coprime_comm] at hpi2₂
          exact gcd_p_of_diff_one (by ring: (a + 3) = (a + 2) + 1) hpi2₂
        · left
          rw [Nat.coprime_comm] at hpi2₂
          have h := gcd_p_of_diff_two (by ring: (a + 4) = (a + 2) + 2) hpi2₂
          rw [← h]
          apply Nat.gcd_dvd_right
        · right
          rw [Nat.coprime_comm] at hpi2₂
          have h := gcd_p_of_diff_three (by ring: (a + 5) = (a + 2) + 3) hpi2₂
          rw [← h]
          apply Nat.gcd_dvd_right
      set pa4 : ℕ+ := ⟨(P (a + 4)), (by simp : _)⟩ with hpa4
      have hpa4S : pa4 ∈ S := by
        simp [S, hpa4]
        use ⟨4, (by norm_num : _)⟩
        simp
        rw [← PNat.coe_le_coe, PNat.val_ofNat, hb]
        norm_num
      have hpa4' : 7 ∣ P (a + 4) ∨ 3 ∣ P (a + 4) := by
        rcases ha pa4 hpa4S with ⟨pi4, ⟨i4, hi4₁, hi4₂⟩, hpi4₁, hpi4₂⟩
        rw [← PNat.coe_le_coe, hb] at hi4₁
        rw [← PNat.coe_inj.ne, hi4₂, hpa4, PNat.mk_coe] at hpi4₁
        rw [hi4₂, hpa4, PNat.mk_coe] at hpi4₂
        have hi4 := i4.pos
        interval_cases i4.val
        · right
          have h := gcd_p_of_diff_three (by ring: (a + 4) = (a + 1) + 3) hpi4₂
          rw [← h]
          apply Nat.gcd_dvd_left
        · left
          have h := gcd_p_of_diff_two (by ring: (a + 4) = (a + 2) + 2) hpi4₂
          rw [← h]
          apply Nat.gcd_dvd_left
        · exfalso
          exact gcd_p_of_diff_one (by ring: (a + 4) = (a + 3) + 1) hpi4₂
        · exfalso
          exact false_of_ne hpi4₁
        · exfalso
          rw [Nat.coprime_comm] at hpi4₂
          exact gcd_p_of_diff_one (by ring: (a + 5) = (a + 4) + 1) hpi4₂
      by_cases hpa2pa4 : 3 ∣ P (a + 2) ∧ 3 ∣ P (a + 4)
      · have hpa2pa4' := Nat.dvd_gcd hpa2pa4.right hpa2pa4.left
        have hpa2pa4'' : ¬Nat.Coprime (P (a + 4)) (P (a + 2)) := by
          rw [Nat.coprime_iff_gcd_eq_one]
          contrapose! hpa2pa4'
          rw [hpa2pa4']
          norm_num
        have h := gcd_p_of_diff_two (by ring: (a + 4) = (a + 2) + 2) hpa2pa4''
        rw [h] at hpa2pa4'
        norm_num at hpa2pa4'
      · have hpa2pa4' : 7 ∣ P (a + 2) ∨ 7 ∣ P (a + 4) := by tauto
        rcases hpa2pa4' with (hpa2''|hpa4'')
        · have h := Nat.not_coprime_of_dvd_of_dvd (by norm_num : 1 < 7) hpa3' hpa2''
          exact gcd_p_of_diff_one (by ring: (a + 3) = (a + 2) + 1) h
        · have h := Nat.not_coprime_of_dvd_of_dvd (by norm_num : 1 < 7) hpa4'' hpa3'
          exact gcd_p_of_diff_one (by ring: (a + 4) = (a + 3) + 1) h

end Imo2016P4
