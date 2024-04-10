/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongyu Ouyang
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# USA Mathematical Olympiad 2015, Problem 1

Solve in integers the equation x² + xy + y² = ((x + y) / 3 + 1)³.
-/

namespace Usa2015P1

snip begin

lemma iff_comm {a b c : Prop} : (a → c) → (b → c) → (c → (a ↔ b)) → (a ↔ b) := by
  tauto

lemma abc { a b c : ℤ } (hb : b ≠ 0) : a ^ 2 = b ^ 2 * c → ∃ d, c = d ^ 2 := by
  intro h
  have h1 : b ^ 2 ∣ a ^ 2 := by simp_all only [ne_eq, dvd_mul_right]
  have h2 : b ∣ a := by apply (Int.pow_dvd_pow_iff (by positivity)).mp h1
  obtain ⟨d, rfl⟩ := h2
  rw [mul_pow, mul_right_inj' (by positivity)] at h
  use d
  exact h.symm

snip end

determine SolutionSet : Set (ℤ × ℤ) :=
  {⟨x, y⟩ | ∃ n, x = n ^ 3 + 3 * n ^ 2 - 1 ∧ y = -n ^ 3 + 3 * n + 1} ∪
  {⟨x, y⟩ | ∃ n, y = n ^ 3 + 3 * n ^ 2 - 1 ∧ x = -n ^ 3 + 3 * n + 1}

problem usa2015_p1 (x y : ℤ) :
    ⟨x, y⟩ ∈ SolutionSet ↔
    x^2 + x * y + y^2 = ((x + y) / (3 : ℚ) + 1)^3 := by
  unfold SolutionSet
  apply iff_comm (c := ∃ t, x + y = 3 * t)
  · simp; intro h; cases' h with h h;
    all_goals obtain ⟨h, hx, hy⟩ := h; rw [hx, hy]; ring_nf; use (h + h ^ 2); ring_nf
  · intro h; apply_fun (· * 3 ^ 3) at h; rw [←mul_pow, (add_mul _ 1)] at h; simp at h
    norm_num at h; norm_cast at h
    suffices : (x + y) % 3 = 0; rw [←dvd_def]; exact Int.dvd_of_emod_eq_zero this
    have h1 : (x ^ (2 : ℕ) + x * y + y ^ (2 : ℕ)) * (27 : ℤ) % 3 = (x + y + (3 : ℤ)) ^ (3 : ℕ) % 3 := by rw [h]
    clear h
    have h2 : (x ^ (2 : ℕ) + x * y + y ^ (2 : ℕ)) * (27 : ℤ) % 3 = 0 := by omega
    rw [h2] at h1
    clear h2
    have h3 : (x + y + (3 : ℤ)) ^ (3 : ℕ) = (x + y) ^ 3 + 3 * (x + y) * 3 * 3 + 3 * (x + y)^2 * 3 + 3 * 3 * 3 := by ring
    rw [h3] at h1
    clear h3
    simp only [Int.add_mul_emod_self_left, Int.add_mul_emod_self] at h1
    exact Int.emod_eq_zero_of_dvd <|
      Prime.dvd_of_dvd_pow Int.prime_three (Int.dvd_of_emod_eq_zero h1.symm)
  intro ht
  obtain ⟨t, ht⟩ := ht
  have ht2 : t = (x + y) / 3 := by rw [ht]; simp
  rw [← Rat.intCast_add, ht]
  rw [(by cancel_denoms : ((3 * t) : ℤ) / (3 : ℚ) = t)]
  norm_cast
  rw [(by rw [←ht]; linarith only : (x ^ 2 + x * y + y ^ 2) = (3 * t) ^ 2 + x * (x - 3 * t))]
  trans (2 * x - 3 * t) ^ 2 = (t - 2) ^ 2 * (4 * t + 1)
  swap; constructor <;> intro h <;> linarith only [h]
  constructor
  · intro h
    simp at h
    cases' h with h h
    all_goals obtain ⟨n, h1, h2⟩ := h
    all_goals have ht : t = n ^ 2 + n := by rw [ht2, h1, h2]; ring_nf; field_simp [←add_mul]
    all_goals rw [ht]; (first | rw [h1] | rw [h2]); ring_nf
  · intro ht3
    by_cases ht4 : (t = 2)
    · rw [ht4] at ht3; norm_num at ht3
      have : x = 3 := by linarith only [ht3]
      rw [this, ht4] at ht
      have : y = 3 := by linarith only [ht]
      simp [*]; use 1; simp
    · have : t - 2 ≠ 0 := by intro; apply ht4; linarith
      have hn := abc (by positivity) ht3
      obtain ⟨d, hd⟩ := hn
      have Odd_dd : Odd (d ^ 2) := by rw [←hd]; apply Even.add_one; apply Even.mul_right; exact Int.even_iff.mpr rfl
      have Odd_d  : Odd d := (Int.odd_pow' (by positivity)).mp Odd_dd
      set n := d / 2 with hn
      have nd : d = 2 * n + 1 := by rw [hn]; symm; exact Int.two_mul_ediv_two_add_one_of_odd Odd_d
      have ht5 := nd ▸ hd
      rw [add_sq, mul_pow] at ht5
      have ht6 : 4 * t = 4 * (n * (n + 1)) := by linear_combination 1 * ht5
      clear ht5
      have htn : t = n * (n + 1) := (Int.mul_eq_mul_left_iff (by positivity)).mp ht6
      rw [htn] at ht3
      have ht7 : (2 * x - 3 * n * n - 3 * n) ^ 2 = ((n * n + n - 2) * (2 * n + 1)) ^ 2 := by
        linear_combination 1 * ht3
      clear ht3
      rw [sq_eq_sq_iff_eq_or_eq_neg] at ht7
      simp only [Set.mem_union, Set.mem_setOf_eq]
      cases' ht7 with h h
      · left; use n; refine ⟨?x1, let hx := ?x1; ?_⟩
        · rw [←Int.mul_eq_mul_left_iff (by positivity : ((2 : ℤ) ≠ 0))]
          linear_combination 1 * h
        · rw [hx, htn] at ht; linear_combination 1 * ht
      · right; use n; rw [And.comm]; refine ⟨?x2, let hx := ?x2; ?_⟩
        · rw [←Int.mul_eq_mul_left_iff (by positivity : ((2 : ℤ) ≠ 0))]
          linear_combination 1 * h
        · rw [hx, htn] at ht; linear_combination 1 * ht
