/-
Copyright (c) 2023 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Rydh, Codex
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 2012, Problem 6

Find all positive integers n for which there exist non-negative
integers a₁, a₂, ..., aₙ such that
1/2^a₁ + 1/2^a₂ + ··· + 1/2^aₙ = 1/3^a₁ + 2/3^a₂ + ··· + n/3^aₙ = 1
-/

namespace Imo2012P6


determine solution_set : Set ℕ := { n : ℕ | n % 4 = 1 ∨ n % 4 = 2 }

def IsSolution (n : ℕ) : Prop := ∃ a : ℕ → ℕ, 0 < n ∧
  (∑ i ∈ Finset.Icc 1 n, (1 : ℚ) / (2 ^ a i)) = 1 ∧
  (∑ i ∈ Finset.Icc 1 n, (i : ℚ) / (3 ^ a i)) = 1

snip begin

lemma sum_id {n : ℕ} : ∑ i ∈ Finset.Icc 1 n, i = n * (n + 1) / 2 := by
  have hIcc : Finset.Icc 1 n = (Finset.range (n + 1)).erase 0 := by
    ext i
    simp [Finset.mem_Icc, Nat.succ_le_iff, Nat.pos_iff_ne_zero]
  rw [hIcc, Finset.sum_erase] <;> simp [Finset.sum_range_id, Nat.mul_comm]

lemma solution_5 : IsSolution 5 := by
  use fun i ↦ if i ∈ Finset.Ico 1 4 then 2 else if i ∈ Finset.Icc 4 5 then 3 else 0
  constructor
  · decide
  · constructor <;> rw [show Finset.Icc 1 5 = {1, 2, 3, 4, 5} by decide] <;> norm_num

lemma solution_9 : IsSolution 9 := by
  use fun i ↦ if i ∈ Finset.Ico 1 2 then 2 else if i ∈ Finset.Ico 2 6 then 3 else if i ∈ Finset.Icc 6 9 then 4 else 0
  constructor
  · decide
  · constructor <;> rw [show Finset.Icc 1 9 = {1, 2, 3, 4, 5, 6, 7, 8, 9} by decide] <;> norm_num

-- If n=4k+1 is a solution then n=4k+2 is also a solution.
lemma ind_4k1_to_4k2 : ∀ k, IsSolution (4 * k + 1) → IsSolution (4 * k + 2) := by
  intro k hk
  obtain ⟨a, hpos, ha₁, ha₂⟩ := hk
  let R : Finset ℕ := Finset.Icc 1 (4 * k + 1)
  let j : ℕ := 2 * k + 1
  let b : ℕ → ℕ := fun i ↦ if i = j then a j + 1 else if i = 4 * k + 2 then a j + 1 else a i
  have hjmem : j ∈ R := by grind
  refine ⟨b, by lia, ?_, ?_⟩
  · rw [Finset.sum_Icc_succ_top (by lia) (fun i ↦ (1 : ℚ) / 2 ^ b i)]
    have : ∑ x ∈ R.erase j, (1 : ℚ) / 2 ^ b x = ∑ x ∈ R.erase j, (1 : ℚ) / 2 ^ a x := by
      apply Finset.sum_congr rfl
      grind
    grind only [Finset.add_sum_erase]
  · rw [Finset.sum_Icc_succ_top (by lia) (fun i ↦ (i : ℚ) / 3 ^ b i)]
    have : ∑ x ∈ R.erase j, (x : ℚ) / 3 ^ b x = ∑ x ∈ R.erase j, (x : ℚ) / 3 ^ a x := by
      apply Finset.sum_congr rfl
      grind
    grind only [Finset.add_sum_erase]

-- If n=4k+1 is a solution then n=4k+13 is also a solution.
lemma ind_4k1_to_4k13 : ∀ k, IsSolution (4 * k + 1) → IsSolution (4 * k + 13) := by
  intro k hk
  obtain ⟨a, hpos, ha₁, ha₂⟩ := hk
  let j : ℕ := k + 1
  let b : ℕ → ℕ := fun i ↦
    if i = j then a j + 2 else
    if i ≤ 4 * k + 1 then a i else
    if i ≤ 4 * k + 2 then a j + 2 else
    if i ≤ 4 * k + 4 then a j + 3 else
    if i ≤ 4 * k + 7 then a j + 6 else
    if i ≤ 4 * k + 8 then a j + 5 else
    if i ≤ 4 * k + 11 then a j + 6 else
    if i ≤ 4 * k + 13 then a j + 4 else
    a i
  let R : Finset ℕ := Finset.Icc 1 (4 * k + 1)
  have htmem : k + 1 ∈ R := by grind

  refine ⟨b, by grind, ?_, ?_⟩
  · iterate 12
      rw [Finset.sum_Icc_succ_top (by grind) (fun i ↦ (1 : ℚ) / 2 ^ b i)]
    have : ∑ i ∈ R.erase (k + 1), (1 : ℚ) / 2 ^ b i = ∑ i ∈ R.erase (k + 1), (1 : ℚ) / 2 ^ a i := by
      apply Finset.sum_congr rfl
      grind
    grind only [Finset.add_sum_erase]
  · iterate 12
      rw [Finset.sum_Icc_succ_top (by grind) (fun i ↦ (i : ℚ) / 3 ^ b i)]
    have : ∑ i ∈ R.erase (k + 1), (i : ℚ) / 3 ^ b i = ∑ i ∈ R.erase (k + 1), (i : ℚ) / 3 ^ a i := by
      apply Finset.sum_congr rfl
      grind
    grind only [Finset.add_sum_erase]

snip end

problem imo2012_p6 : { n | IsSolution n } = solution_set := by
  -- based on https://artofproblemsolving.com/community/c6h488512p2737435
  ext n
  constructor
  · intro hn
    obtain ⟨a, hpos, _, ha⟩ := hn
    set R := Finset.Icc 1 n
    -- Multiply ha by 3^m where m is the maximum of the a i's
    set m := Finset.sup R a
    have hmul : (3 : ℚ)^m = ∑ i ∈ R, (i : ℚ) * (3 : ℚ)^(m - a i) := by
      calc
        (3 : ℚ)^m = (3 : ℚ)^m * 1 := by ring
        _ = (3 : ℚ)^m * ∑ i ∈ R, (i : ℚ) / (3 : ℚ)^a i := by rw [ha]
        _ = ∑ i ∈ R, (3 : ℚ)^m * ((i : ℚ) / (3 : ℚ)^a i) := by rw [Finset.mul_sum]
        _ = ∑ i ∈ R, (i : ℚ) * (3 : ℚ)^(m - a i) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hpow : (3 : ℚ) ^ (m - a i) = (3 : ℚ) ^ m * ((3 : ℚ) ^ a i)⁻¹ := by
            have hne : (3 : ℚ) ^ a i ≠ 0 := by positivity
            field_simp [hne]
            have hm_ge : ∀ i ∈ R, a i ≤ m := fun i hi ↦ Finset.le_sup hi
            rw [← pow_add, Nat.sub_add_cancel (hm_ge i hi)]
          rw [hpow]
          ring
    replace hmul : 3^m = ∑ i ∈ R, i * 3^(m - a i) := by exact_mod_cast hmul

    -- Reduce mod 2 to get a condition on n mod 4
    apply congr_arg (fun x ↦ x % 2) at hmul
    have h_mod_pow {k : ℕ} : (3^k) % 2 = 1 := by
      induction k with
      | zero => simp
      | succ k ih => grind

    rw [h_mod_pow, Finset.sum_nat_mod] at hmul
    conv_rhs at hmul =>
      arg 1
      arg 2
      ext i
      rw [Nat.mul_mod, h_mod_pow]
      simp
    rw [← Finset.sum_nat_mod, sum_id] at hmul

    -- Complete proof by checking cases on n mod 4
    have hlt : n % 4 < 4 := Nat.mod_lt n (by decide)
    have {k : ℕ} : ((4 * k * (4 * k + 1)) / 2) % 2 = 0 := by grind
    have {k : ℕ} : (((4 * k + 3) * (4 * k + 4)) / 2) % 2 = 0 := by grind
    interval_cases hcase : n % 4 <;> try grind
    · grind [show n = 4 * (n / 4) by grind]
    · grind [show n = 4 * (n / 4) + 3 by grind]

  · -- Proof by induction on n, using base cases n=1,5,9 and the
    -- inductive steps to show that all n in the solution set are solutions
    intro hn
    have aux₁ : ∀ k l, l < 3 → IsSolution (12 * k + 4 * l + 1) := by
      intro k l hl
      induction k with
      | zero =>
        interval_cases l
        · use fun _ ↦ 0
          simp
        · exact solution_5
        · exact solution_9
      | succ k ih =>
        convert ind_4k1_to_4k13 (3 * k + l) (by grind : IsSolution (4 * (3 * k + l) + 1)) using 1
        grind

    have aux₂ : ∀ k l, l < 3 → IsSolution (12 * k + 4 * l + 2) := by
      intro k l hl
      convert ind_4k1_to_4k2 (3 * k + l) (by grind : IsSolution (4 * (3 * k + l) + 1)) using 1
      grind

    have hk (r : ℕ) (hr : n % 4 = r) : ∃ l m, m < 3 ∧ n = 12 * l + 4 * m + r := by
      refine ⟨(n / 4) / 3, (n / 4) % 3, ?_, ?_⟩ <;> lia
    cases' hn with h1 h2
    · rcases hk 1 h1 with ⟨l, m, hm, rfl⟩
      exact aux₁ l m hm
    · rcases hk 2 h2 with ⟨l, m, hm, rfl⟩
      exact aux₂ l m hm

end Imo2012P6
