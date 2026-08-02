/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Prime
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.NumberTheory] }

/-!
# USA Mathematical Olympiad 1986, Problem 1

(a) Do there exist 14 consecutive positive integers, each of which is
divisible by a prime less than 13?

(b) Do there exist 21 consecutive positive integers, each of which is
divisible by a prime less than 17?
-/

namespace Usa1986P1

snip begin

/-- A prime less than `13` that is not `2` is one of `3, 5, 7, 11`. -/
lemma prime_lt_thirteen_ne_two {p : ℕ} (hp : p.Prime) (h13 : p < 13) (h2 : p ≠ 2) :
    p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 := by
  have h2le : 2 ≤ p := hp.two_le
  interval_cases p <;> norm_num at hp <;> norm_num at h2 <;> norm_num

/--
If the same prime `p ∈ {7, 11}` divides both `a + 2 * j₁` and `a + 2 * j₂`
with `j₁, j₂ < 7`, then `j₁ = j₂`: `p` divides `2 * (j₂ - j₁)`, which has
absolute value less than `14`, so it must be zero.
-/
lemma eq_of_dvd (j₁ j₂ : ℕ) (a : ℕ) (h₁ : j₁ < 7) (h₂ : j₂ < 7)
    (h : (7 ∣ a + 2 * j₁ ∧ 7 ∣ a + 2 * j₂) ∨
         (11 ∣ a + 2 * j₁ ∧ 11 ∣ a + 2 * j₂)) :
    j₁ = j₂ := by
  rcases h with ⟨⟨k₁, hk₁⟩, ⟨k₂, hk₂⟩⟩ | ⟨⟨k₁, hk₁⟩, ⟨k₂, hk₂⟩⟩ <;> omega

/--
Pigeonhole principle: among three pairwise distinct indices `t₁, t₂, t₃ < 7`,
it cannot happen that each of `a + 2 * t₁`, `a + 2 * t₂`, `a + 2 * t₃` is
divisible by `7` or by `11` (two of them would share a prime, contradicting
`eq_of_dvd`).  Hence, if none of them is divisible by `3` or `5`, one of them
is divisible by none of `3, 5, 7, 11`.
-/
lemma not_all_divisible_of_three (t₁ t₂ t₃ : ℕ) (a : ℕ)
    (h₁₂ : t₁ ≠ t₂) (h₁₃ : t₁ ≠ t₃) (h₂₃ : t₂ ≠ t₃)
    (b₁ : t₁ < 7) (b₂ : t₂ < 7) (b₃ : t₃ < 7)
    (s₁ : ¬ 3 ∣ a + 2 * t₁ ∧ ¬ 5 ∣ a + 2 * t₁)
    (s₂ : ¬ 3 ∣ a + 2 * t₂ ∧ ¬ 5 ∣ a + 2 * t₂)
    (s₃ : ¬ 3 ∣ a + 2 * t₃ ∧ ¬ 5 ∣ a + 2 * t₃) :
    ∃ j < 7, ¬ 3 ∣ a + 2 * j ∧ ¬ 5 ∣ a + 2 * j ∧
             ¬ 7 ∣ a + 2 * j ∧ ¬ 11 ∣ a + 2 * j := by
  by_cases g1 : 7 ∣ a + 2 * t₁ ∨ 11 ∣ a + 2 * t₁
  · by_cases g2 : 7 ∣ a + 2 * t₂ ∨ 11 ∣ a + 2 * t₂
    · by_cases g3 : 7 ∣ a + 2 * t₃ ∨ 11 ∣ a + 2 * t₃
      · rcases g1 with g1 | g1 <;> rcases g2 with g2 | g2 <;> rcases g3 with g3 | g3 <;>
          first
          | exact absurd (eq_of_dvd t₁ t₂ a b₁ b₂ (Or.inl ⟨g1, g2⟩)) h₁₂
          | exact absurd (eq_of_dvd t₁ t₃ a b₁ b₃ (Or.inl ⟨g1, g3⟩)) h₁₃
          | exact absurd (eq_of_dvd t₂ t₃ a b₂ b₃ (Or.inl ⟨g2, g3⟩)) h₂₃
          | exact absurd (eq_of_dvd t₁ t₂ a b₁ b₂ (Or.inr ⟨g1, g2⟩)) h₁₂
          | exact absurd (eq_of_dvd t₁ t₃ a b₁ b₃ (Or.inr ⟨g1, g3⟩)) h₁₃
          | exact absurd (eq_of_dvd t₂ t₃ a b₂ b₃ (Or.inr ⟨g2, g3⟩)) h₂₃
      · exact ⟨t₃, b₃, s₃.1, s₃.2, (not_or.mp g3).1, (not_or.mp g3).2⟩
    · exact ⟨t₂, b₂, s₂.1, s₂.2, (not_or.mp g2).1, (not_or.mp g2).2⟩
  · exact ⟨t₁, b₁, s₁.1, s₁.2, (not_or.mp g1).1, (not_or.mp g1).2⟩

/--
Among any seven consecutive odd numbers `a, a + 2, …, a + 12`, at least one is
divisible by none of the primes `3, 5, 7, 11`.

The proof follows the classical USAMO solution.  At most three of the seven
numbers are divisible by `3` (and if there are three, the two endpoints are
among them), at most two by `5` (and then an endpoint is among them), at most
one by `7` and at most one by `11`, so at most six of the seven numbers can be
divisible by one of `3, 5, 7, 11`.  We check the finitely many cases for
`a % 3` and `a % 5`: in each case three explicit indices avoid `3` and `5`,
and `not_all_divisible_of_three` finishes.
-/
lemma not_all_divisible (a : ℕ) :
    ∃ j < 7, ¬ 3 ∣ a + 2 * j ∧ ¬ 5 ∣ a + 2 * j ∧
             ¬ 7 ∣ a + 2 * j ∧ ¬ 11 ∣ a + 2 * j := by
  have h3 : a % 3 < 3 := Nat.mod_lt a (by norm_num)
  have h5 : a % 5 < 5 := Nat.mod_lt a (by norm_num)
  interval_cases hc3 : a % 3 <;> interval_cases hc5 : a % 5
  · exact not_all_divisible_of_three 1 2 4 a (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  · exact not_all_divisible_of_three 1 4 5 a (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  · exact not_all_divisible_of_three 1 2 5 a (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  · exact not_all_divisible_of_three 2 4 5 a (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  · exact not_all_divisible_of_three 1 2 4 a (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  · exact not_all_divisible_of_three 2 3 6 a (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  · exact not_all_divisible_of_three 0 3 5 a (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  · exact not_all_divisible_of_three 0 3 5 a (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  · exact not_all_divisible_of_three 0 3 5 a (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  · exact not_all_divisible_of_three 0 2 5 a (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  · exact not_all_divisible_of_three 1 3 4 a (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  · exact not_all_divisible_of_three 0 1 3 a (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  · exact not_all_divisible_of_three 0 1 3 a (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  · exact not_all_divisible_of_three 0 3 4 a (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  · exact not_all_divisible_of_three 0 1 4 a (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩

snip end

determine does_exist_14 : Bool := false

determine does_exist_21 : Bool := true

problem usa1986_p1a :
    if does_exist_14 then
      ∃ n : ℕ, 0 < n ∧
        ∀ i ∈ Finset.range 14, ∃ p : ℕ, p.Prime ∧ p < 13 ∧ p ∣ n + i
    else
      ¬ ∃ n : ℕ, 0 < n ∧
        ∀ i ∈ Finset.range 14, ∃ p : ℕ, p.Prime ∧ p < 13 ∧ p ∣ n + i := by
  change ¬ ∃ n : ℕ, 0 < n ∧
        ∀ i ∈ Finset.range 14, ∃ p : ℕ, p.Prime ∧ p < 13 ∧ p ∣ n + i
  rintro ⟨n, -, h⟩
  -- Among `n, …, n + 13` there are seven odd numbers; writing the smallest of
  -- them as `a = n + 1 - n % 2`, they are `a + 2 * j` for `j < 7`.
  obtain ⟨j, hj, h3, h5, h7, h11⟩ := not_all_divisible (n + 1 - n % 2)
  have hi : 1 - n % 2 + 2 * j < 14 := by omega
  obtain ⟨p, hp, h13, hdiv⟩ := h (1 - n % 2 + 2 * j) (Finset.mem_range.mpr hi)
  rw [show n + (1 - n % 2 + 2 * j) = n + 1 - n % 2 + 2 * j by omega] at hdiv
  have hodd : ¬ 2 ∣ n + 1 - n % 2 + 2 * j := by omega
  have hp2 : p ≠ 2 := fun h2 ↦ hodd (h2 ▸ hdiv)
  rcases prime_lt_thirteen_ne_two hp h13 hp2 with rfl | rfl | rfl | rfl
  · exact h3 hdiv
  · exact h5 hdiv
  · exact h7 hdiv
  · exact h11 hdiv

problem usa1986_p1b :
    if does_exist_21 then
      ∃ n : ℕ, 0 < n ∧
        ∀ i ∈ Finset.range 21, ∃ p : ℕ, p.Prime ∧ p < 17 ∧ p ∣ n + i
    else
      ¬ ∃ n : ℕ, 0 < n ∧
        ∀ i ∈ Finset.range 21, ∃ p : ℕ, p.Prime ∧ p < 17 ∧ p ∣ n + i := by
  change ∃ n : ℕ, 0 < n ∧
        ∀ i ∈ Finset.range 21, ∃ p : ℕ, p.Prime ∧ p < 17 ∧ p ∣ n + i
  -- The odd numbers among 9440, …, 9460 are divisible by
  -- 3, 7, 5, 3, 11, 13, 3, 5, 7, 3 respectively.
  refine ⟨9440, by norm_num, fun i hi ↦ ?_⟩
  rw [Finset.mem_range] at hi
  interval_cases i
  · exact ⟨2, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨7, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨11, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨13, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨7, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2, by norm_num, by norm_num, by norm_num⟩

end Usa1986P1
