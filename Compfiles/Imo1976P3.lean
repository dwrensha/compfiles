/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Olympiad 1976, Problem 3

A rectangular box can be completely filled with unit cubes. If one places
as many cubes as possible, each with volume 2, in the box, with their edges
parallel to the edges of the box, one can fill exactly 40% of the box.
Determine the possible dimensions of the box.

# Formalization

The box has integer dimensions `a ≤ b ≤ c`. A cube of volume `2` has side
length `k = ∛2` (the real cube root of two), and along an edge of integer
length `n` exactly `⌊n / k⌋₊` such cubes fit, so the "exactly 40%" condition
reads `a * b * c = 5 * (⌊a / k⌋₊ * ⌊b / k⌋₊ * ⌊c / k⌋₊)`. We prove that the
sorted dimensions are exactly `2 × 3 × 5` or `2 × 5 × 6`.

# Solution

We follow https://prase.cz/kalva/imo/isoln/isoln763.html . Writing
`n' = ⌊n / k⌋₊`, the defining property of the floor becomes the pair of
integer inequalities `2 * n'^3 ≤ n^3 < 2 * (n' + 1)^3`, and everything is
done in `ℕ` from then on. One shows `n^3 < 5 * n'^3` for all `n ≥ 3`, which
forces the smallest dimension to be `2`; then `7 * n < 10 * n'` for `n ≥ 11`
bounds the middle dimension by `10`, and a finite case analysis on
`b ∈ {2, …, 10}` (using `2 * b * c = 5 * b' * c'` and the divisibility it
implies) leaves only `c = 5` (when `b = 3`) and `c = 6` (when `b = 5`).
-/

namespace Imo1976P3

/-- The side length of a cube of volume 2: the real cube root of 2. -/
noncomputable def k : ℝ := (2 : ℝ) ^ (3 : ℝ)⁻¹

snip begin

theorem k_pos : 0 < k :=
  Real.rpow_pos_of_pos (by norm_num) _

theorem k_cube : k ^ 3 = 2 :=
  Real.rpow_inv_natCast_pow (by norm_num) (by norm_num)

theorem one_lt_k : 1 < k := by
  by_contra h
  push Not at h
  have g : k ^ 3 ≤ (1 : ℝ) ^ 3 := pow_le_pow_left₀ k_pos.le h 3
  rw [k_cube] at g
  norm_num at g

theorem k_lt_two : k < 2 := by
  by_contra h
  push Not at h
  have g : (2 : ℝ) ^ 3 ≤ k ^ 3 := pow_le_pow_left₀ (by norm_num) h 3
  rw [k_cube] at g
  norm_num at g

/-- The defining property of `⌊n / k⌋₊`, expressed with integers only:
`2 * n'^3 ≤ n^3 < 2 * (n' + 1)^3`, obtained by cubing `n' * k ≤ n < (n' + 1) * k`. -/
theorem floor_spec (n : ℕ) :
    2 * ⌊(n : ℝ) / k⌋₊ ^ 3 ≤ n ^ 3 ∧ n ^ 3 < 2 * (⌊(n : ℝ) / k⌋₊ + 1) ^ 3 := by
  have h1 : (⌊(n : ℝ) / k⌋₊ : ℝ) ≤ (n : ℝ) / k :=
    Nat.floor_le (div_nonneg (Nat.cast_nonneg _) k_pos.le)
  have h2 : (n : ℝ) / k < (⌊(n : ℝ) / k⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have h3 : (⌊(n : ℝ) / k⌋₊ : ℝ) * k ≤ (n : ℝ) := (le_div_iff₀ k_pos).mp h1
  have h4 : (n : ℝ) < ((⌊(n : ℝ) / k⌋₊ : ℝ) + 1) * k := (div_lt_iff₀ k_pos).mp h2
  have h5 : ((⌊(n : ℝ) / k⌋₊ : ℝ) * k) ^ 3 ≤ (n : ℝ) ^ 3 :=
    pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) k_pos.le) h3 3
  have h6 : (n : ℝ) ^ 3 < (((⌊(n : ℝ) / k⌋₊ : ℝ) + 1) * k) ^ 3 :=
    pow_lt_pow_left₀ h4 (Nat.cast_nonneg _) three_ne_zero
  rw [mul_pow, k_cube] at h5 h6
  constructor
  · have h5' : (2 : ℝ) * (⌊(n : ℝ) / k⌋₊ : ℝ) ^ 3 ≤ (n : ℝ) ^ 3 := by linarith [h5]
    exact_mod_cast h5'
  · have h6' : (n : ℝ) ^ 3 < (2 : ℝ) * ((⌊(n : ℝ) / k⌋₊ : ℝ) + 1) ^ 3 := by linarith [h6]
    have h7 : (n : ℝ) ^ 3 < (2 : ℝ) * ((⌊(n : ℝ) / k⌋₊ + 1 : ℕ) : ℝ) ^ 3 := by
      rw [Nat.cast_add, Nat.cast_one]
      exact h6'
    exact_mod_cast h7

/-- Comparing `x * k` with an integer by comparing cubes. -/
theorem le_of_cube_le {x : ℝ} (n : ℕ) (h : (x * k) ^ 3 ≤ (n : ℝ) ^ 3) : x * k ≤ (n : ℝ) := by
  by_contra h'
  push Not at h'
  have g : (n : ℝ) ^ 3 < (x * k) ^ 3 := pow_lt_pow_left₀ h' (Nat.cast_nonneg _) three_ne_zero
  linarith

/-- Comparing an integer with `x * k` by comparing cubes. -/
theorem lt_of_cube_lt {x : ℝ} (hx : 0 ≤ x) (n : ℕ) (h : (n : ℝ) ^ 3 < (x * k) ^ 3) :
    (n : ℝ) < x * k := by
  by_contra h'
  push Not at h'
  have g : (x * k) ^ 3 ≤ (n : ℝ) ^ 3 := pow_le_pow_left₀ (mul_nonneg hx k_pos.le) h' 3
  linarith

/-- Evaluating `⌊n / k⌋₊` from the two inequalities `c * k ≤ n < (c + 1) * k`. -/
theorem floor_val (n c : ℕ) (h1 : (c : ℝ) * k ≤ (n : ℝ)) (h2 : (n : ℝ) < ((c : ℝ) + 1) * k) :
    ⌊(n : ℝ) / k⌋₊ = c :=
  (Nat.floor_eq_iff (div_nonneg (Nat.cast_nonneg _) k_pos.le)).mpr
    ⟨(le_div_iff₀ k_pos).mpr h1, (div_lt_iff₀ k_pos).mpr h2⟩

theorem floor_two : ⌊(2 : ℝ) / k⌋₊ = 1 := by
  refine floor_val 2 1 ?_ ?_
  · rw [Nat.cast_one, one_mul]
    exact k_lt_two.le
  · push_cast
    linarith [one_lt_k]

theorem floor_three : ⌊(3 : ℝ) / k⌋₊ = 2 := by
  refine floor_val 3 2 ?_ ?_
  · apply le_of_cube_le
    rw [mul_pow, k_cube]
    norm_num
  · push_cast
    linarith [one_lt_k]

theorem floor_five : ⌊(5 : ℝ) / k⌋₊ = 3 := by
  refine floor_val 5 3 ?_ ?_
  · apply le_of_cube_le
    rw [mul_pow, k_cube]
    norm_num
  · push_cast
    refine lt_of_cube_lt ?_ 5 ?_
    · norm_num
    · rw [mul_pow, k_cube]
      norm_num

theorem floor_six : ⌊(6 : ℝ) / k⌋₊ = 4 := by
  refine floor_val 6 4 ?_ ?_
  · apply le_of_cube_le
    rw [mul_pow, k_cube]
    norm_num
  · push_cast
    refine lt_of_cube_lt ?_ 6 ?_
    · norm_num
    · rw [mul_pow, k_cube]
      norm_num

/-- From here on everything is integer arithmetic. `det_of` pins down `n'`
once `n` is known concretely. -/
theorem det_of {n x c : ℕ} (hc1 : 2 * c ^ 3 ≤ n ^ 3) (hc2 : n ^ 3 < 2 * (c + 1) ^ 3)
    (h1 : 2 * x ^ 3 ≤ n ^ 3) (h2 : n ^ 3 < 2 * (x + 1) ^ 3) : x = c := by
  have hx1 : x ≤ c := by
    by_contra h'
    push Not at h'
    have g : (c + 1) ^ 3 ≤ x ^ 3 := Nat.pow_le_pow_left h' 3
    nlinarith [h1, hc2, g]
  have hx2 : c ≤ x := by
    by_contra h'
    push Not at h'
    have g : (x + 1) ^ 3 ≤ c ^ 3 := Nat.pow_le_pow_left (by omega : x + 1 ≤ c) 3
    nlinarith [hc1, h2, g]
  omega

/-- If `1 ≤ n'` and `2 * n'^3 ≤ n^3` then `2 ≤ n`. -/
theorem two_le_of {n n' : ℕ} (hn' : 1 ≤ n') (h1 : 2 * n' ^ 3 ≤ n ^ 3) : 2 ≤ n := by
  have g2 : 2 ≤ n ^ 3 := by
    calc 2 = 2 * 1 ^ 3 := by norm_num
    _ ≤ 2 * n' ^ 3 := mul_le_mul_right (Nat.pow_le_pow_left hn' 3) 2
    _ ≤ n ^ 3 := h1
  by_contra h'
  push Not at h'
  interval_cases n <;> norm_num at g2

/-- The key ratio bound: for `n ≥ 3`, `n^3 < 5 * n'^3`. -/
theorem five_cubed {n n' : ℕ} (hn : 3 ≤ n) (h1 : 2 * n' ^ 3 ≤ n ^ 3)
    (h2 : n ^ 3 < 2 * (n' + 1) ^ 3) : n ^ 3 < 5 * n' ^ 3 := by
  rcases Nat.lt_or_ge n 8 with h8 | h8
  · interval_cases n
    · have hnv : n' = 2 := det_of (by norm_num) (by norm_num) h1 h2
      subst hnv
      norm_num
    · have hnv : n' = 3 := det_of (by norm_num) (by norm_num) h1 h2
      subst hnv
      norm_num
    · have hnv : n' = 3 := det_of (by norm_num) (by norm_num) h1 h2
      subst hnv
      norm_num
    · have hnv : n' = 4 := det_of (by norm_num) (by norm_num) h1 h2
      subst hnv
      norm_num
    · have hnv : n' = 5 := det_of (by norm_num) (by norm_num) h1 h2
      subst hnv
      norm_num
  · have hn' : 6 ≤ n' := by
      by_contra h'
      push Not at h'
      have g1 : (n' + 1) ^ 3 ≤ 6 ^ 3 := Nat.pow_le_pow_left (by omega : n' + 1 ≤ 6) 3
      have g2 : 8 ^ 3 ≤ n ^ 3 := Nat.pow_le_pow_left h8 3
      nlinarith [h2, g1, g2]
    by_contra hc
    push Not at hc
    have g3 : 6 * n' ^ 2 ≤ n' ^ 3 := by
      calc 6 * n' ^ 2 ≤ n' * n' ^ 2 := mul_le_mul_left hn' _
      _ = n' ^ 3 := by ring
    have g4 : n' ≤ n' ^ 2 := by
      calc n' = n' * 1 := by ring
      _ ≤ n' * n' := mul_le_mul_right (by omega : 1 ≤ n') n'
      _ = n' ^ 2 := by ring
    nlinarith [hc, h2, g3, g4, hn']

/-- Auxiliary estimate: `343 * (m + 1)^3 ≤ 500 * m^3` for `m ≥ 8`. -/
theorem key500 {m : ℕ} (hm : 8 ≤ m) : 343 * (m + 1) ^ 3 ≤ 500 * m ^ 3 := by
  obtain ⟨t, rfl⟩ : ∃ t, m = 8 + t := ⟨m - 8, by omega⟩
  nlinarith [Nat.zero_le t, Nat.zero_le (t ^ 2), Nat.zero_le (t ^ 3)]

/-- The second ratio bound: for `n ≥ 11`, `7 * n < 10 * n'`. -/
theorem seven_lt_ten {n n' : ℕ} (hn : 11 ≤ n) (_h1 : 2 * n' ^ 3 ≤ n ^ 3)
    (h2 : n ^ 3 < 2 * (n' + 1) ^ 3) : 7 * n < 10 * n' := by
  have hn' : 8 ≤ n' := by
    by_contra h'
    push Not at h'
    have g1 : (n' + 1) ^ 3 ≤ 8 ^ 3 := Nat.pow_le_pow_left (by omega : n' + 1 ≤ 8) 3
    have g2 : 11 ^ 3 ≤ n ^ 3 := Nat.pow_le_pow_left hn 3
    nlinarith [h2, g1, g2]
  have key := key500 hn'
  by_contra hcontra
  push Not at hcontra
  have g3 : (10 * n') ^ 3 ≤ (7 * n) ^ 3 := Nat.pow_le_pow_left hcontra 3
  nlinarith [h2, key, g3]

/-- The integer core of the problem: the only sorted triples satisfying the
volume equation are `(2, 3, 5)` and `(2, 5, 6)`. -/
theorem main_nat {a b c a' b' c' : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a ≤ b) (hbc : b ≤ c)
    (ha1 : 2 * a' ^ 3 ≤ a ^ 3) (ha2 : a ^ 3 < 2 * (a' + 1) ^ 3)
    (hb1 : 2 * b' ^ 3 ≤ b ^ 3) (hb2 : b ^ 3 < 2 * (b' + 1) ^ 3)
    (hc1 : 2 * c' ^ 3 ≤ c ^ 3) (hc2 : c ^ 3 < 2 * (c' + 1) ^ 3)
    (h : a * b * c = 5 * (a' * b' * c')) :
    (a = 2 ∧ b = 3 ∧ c = 5) ∨ (a = 2 ∧ b = 5 ∧ c = 6) := by
  have hpos : 0 < a' * b' * c' := by
    have habc : 0 < a * b * c := by positivity
    omega
  have ha' : 1 ≤ a' := by
    by_contra h'
    push Not at h'
    interval_cases a'
    simp at hpos
  have hb' : 1 ≤ b' := by
    by_contra h'
    push Not at h'
    interval_cases b'
    simp at hpos
  have hc' : 1 ≤ c' := by
    by_contra h'
    push Not at h'
    interval_cases c'
    simp at hpos
  have ha2' : 2 ≤ a := two_le_of ha' ha1
  have hb2' : 2 ≤ b := two_le_of hb' hb1
  have hc2' : 2 ≤ c := two_le_of hc' hc1
  -- The smallest dimension must be 2.
  have hav : a = 2 := by
    by_contra h'
    have ha3 : 3 ≤ a := by omega
    have e1 := five_cubed ha3 ha1 ha2
    have e2 := five_cubed (le_trans ha3 hab) hb1 hb2
    have e3 := five_cubed (le_trans ha3 (le_trans hab hbc)) hc1 hc2
    have g1 : a ^ 3 * b ^ 3 < (5 * a' ^ 3) * (5 * b' ^ 3) := Nat.mul_lt_mul_of_lt_of_lt e1 e2
    have g2 : a ^ 3 * b ^ 3 * c ^ 3 < (5 * a' ^ 3) * (5 * b' ^ 3) * (5 * c' ^ 3) :=
      Nat.mul_lt_mul_of_lt_of_lt g1 e3
    have g3 : a ^ 3 * b ^ 3 * c ^ 3 = 125 * (a' ^ 3 * b' ^ 3 * c' ^ 3) := by
      calc a ^ 3 * b ^ 3 * c ^ 3 = (a * b * c) ^ 3 := by ring
      _ = (5 * (a' * b' * c')) ^ 3 := by rw [h]
      _ = 125 * (a' ^ 3 * b' ^ 3 * c' ^ 3) := by ring
    nlinarith [g2, g3]
  subst hav
  have ha'v : a' = 1 := det_of (by norm_num) (by norm_num) ha1 ha2
  subst ha'v
  simp only [one_mul] at h
  -- The middle dimension is at most 10.
  have hb10 : b ≤ 10 := by
    by_contra h'
    push Not at h'
    have g1 : 7 * b < 10 * b' := seven_lt_ten h' hb1 hb2
    have g2 : 7 * c < 10 * c' := seven_lt_ten (le_trans h' hbc) hc1 hc2
    have g3 : (7 * b) * (7 * c) < (10 * b') * (10 * c') := Nat.mul_lt_mul_of_lt_of_lt g1 g2
    have g6 : 100 * (b' * c') = 40 * (b * c) := by linarith [h]
    have g7 : 1 ≤ b * c := Nat.mul_pos hb hc
    nlinarith [g3, g6, g7]
  interval_cases b
  · -- b = 2, b' = 1: `4 * c = 5 * c'`, impossible since `128 * m^3 ≤ 125 * m^3`.
    have hb'v : b' = 1 := det_of (by norm_num) (by norm_num) hb1 hb2
    subst hb'v
    obtain ⟨m, rfl⟩ : 5 ∣ c := by omega
    have hc'v : c' = 4 * m := by omega
    rw [hc'v] at hc1
    have hm1 : 1 ≤ m := by omega
    have e3 : 1 ≤ m ^ 3 := Nat.one_le_pow _ _ (by omega : 0 < m)
    exfalso
    nlinarith [hc1, e3]
  · -- b = 3, b' = 2: `3 * c = 5 * c'` gives `c = 5`, the first solution.
    have hb'v : b' = 2 := det_of (by norm_num) (by norm_num) hb1 hb2
    subst hb'v
    obtain ⟨m, rfl⟩ : 5 ∣ c := by omega
    have hc'v : c' = 3 * m := by omega
    rw [hc'v] at hc2
    have hm1 : 1 ≤ m := by omega
    have hmv : m = 1 := by
      rcases Nat.lt_or_ge m 2 with h1 | h1
      · omega
      · exfalso
        have g1 : 2 * m ^ 2 ≤ m ^ 3 := by
          calc 2 * m ^ 2 ≤ m * m ^ 2 := mul_le_mul_left h1 _
          _ = m ^ 3 := by ring
        have e2 : m ≤ m ^ 2 := Nat.le_self_pow two_ne_zero m
        nlinarith [hc2, g1, e2, h1]
    subst hmv
    left
    exact ⟨rfl, rfl, rfl⟩
  · -- b = 4, b' = 3: `8 * c = 15 * c'`, no solution.
    have hb'v : b' = 3 := det_of (by norm_num) (by norm_num) hb1 hb2
    subst hb'v
    obtain ⟨m, rfl⟩ : 15 ∣ c := by omega
    have hc'v : c' = 8 * m := by omega
    rw [hc'v] at hc2
    have hm1 : 1 ≤ m := by omega
    have e1 : m ≤ m ^ 3 := Nat.le_self_pow three_ne_zero m
    have e2 : m ^ 2 ≤ m ^ 3 := Nat.pow_le_pow_right (by omega : 0 < m) (by norm_num)
    have e3 : 1 ≤ m ^ 3 := Nat.one_le_pow _ _ (by omega : 0 < m)
    exfalso
    nlinarith [hc2, e1, e2, e3]
  · -- b = 5, b' = 3: `2 * c = 3 * c'` gives `c ∈ {3, 6}`; only `c = 6 ≥ 5`.
    have hb'v : b' = 3 := det_of (by norm_num) (by norm_num) hb1 hb2
    subst hb'v
    obtain ⟨m, rfl⟩ : 3 ∣ c := by omega
    have hc'v : c' = 2 * m := by omega
    rw [hc'v] at hc1 hc2
    have hm1 : 1 ≤ m := by omega
    have hm2 : m ≤ 2 := by
      by_contra h'
      push Not at h'
      have g1 : 3 * m ^ 2 ≤ m ^ 3 := by
        calc 3 * m ^ 2 ≤ m * m ^ 2 := mul_le_mul_left h' _
        _ = m ^ 3 := by ring
      have g2 : 3 * m ≤ m ^ 2 := by
        calc 3 * m ≤ m * m := mul_le_mul_left h' _
        _ = m ^ 2 := by ring
      nlinarith [hc2, g1, g2]
    interval_cases m
    · exfalso
      omega
    · right
      exact ⟨rfl, rfl, rfl⟩
  · -- b = 6, b' = 4: `3 * c = 5 * c'` forces `c = 5 < 6`.
    have hb'v : b' = 4 := det_of (by norm_num) (by norm_num) hb1 hb2
    subst hb'v
    obtain ⟨m, rfl⟩ : 5 ∣ c := by omega
    have hc'v : c' = 3 * m := by omega
    rw [hc'v] at hc2
    have hm1 : 1 ≤ m := by omega
    have hmv : m = 1 := by
      rcases Nat.lt_or_ge m 2 with h1 | h1
      · omega
      · exfalso
        have g1 : 2 * m ^ 2 ≤ m ^ 3 := by
          calc 2 * m ^ 2 ≤ m * m ^ 2 := mul_le_mul_left h1 _
          _ = m ^ 3 := by ring
        have e2 : m ≤ m ^ 2 := Nat.le_self_pow two_ne_zero m
        nlinarith [hc2, g1, e2, h1]
    exfalso
    omega
  · -- b = 7, b' = 5: `14 * c = 25 * c'`, no solution.
    have hb'v : b' = 5 := det_of (by norm_num) (by norm_num) hb1 hb2
    subst hb'v
    obtain ⟨m, rfl⟩ : 25 ∣ c := by omega
    have hc'v : c' = 14 * m := by omega
    rw [hc'v] at hc2
    have hm1 : 1 ≤ m := by omega
    have e1 : m ≤ m ^ 3 := Nat.le_self_pow three_ne_zero m
    have e2 : m ^ 2 ≤ m ^ 3 := Nat.pow_le_pow_right (by omega : 0 < m) (by norm_num)
    have e3 : 1 ≤ m ^ 3 := Nat.one_le_pow _ _ (by omega : 0 < m)
    exfalso
    nlinarith [hc2, e1, e2, e3]
  · -- b = 8, b' = 6: `8 * c = 15 * c'`, no solution.
    have hb'v : b' = 6 := det_of (by norm_num) (by norm_num) hb1 hb2
    subst hb'v
    obtain ⟨m, rfl⟩ : 15 ∣ c := by omega
    have hc'v : c' = 8 * m := by omega
    rw [hc'v] at hc2
    have hm1 : 1 ≤ m := by omega
    have e1 : m ≤ m ^ 3 := Nat.le_self_pow three_ne_zero m
    have e2 : m ^ 2 ≤ m ^ 3 := Nat.pow_le_pow_right (by omega : 0 < m) (by norm_num)
    have e3 : 1 ≤ m ^ 3 := Nat.one_le_pow _ _ (by omega : 0 < m)
    exfalso
    nlinarith [hc2, e1, e2, e3]
  · -- b = 9, b' = 7: `18 * c = 35 * c'`, no solution.
    have hb'v : b' = 7 := det_of (by norm_num) (by norm_num) hb1 hb2
    subst hb'v
    obtain ⟨m, rfl⟩ : 35 ∣ c := by omega
    have hc'v : c' = 18 * m := by omega
    rw [hc'v] at hc2
    have hm1 : 1 ≤ m := by omega
    have e1 : m ≤ m ^ 3 := Nat.le_self_pow three_ne_zero m
    have e2 : m ^ 2 ≤ m ^ 3 := Nat.pow_le_pow_right (by omega : 0 < m) (by norm_num)
    have e3 : 1 ≤ m ^ 3 := Nat.one_le_pow _ _ (by omega : 0 < m)
    exfalso
    nlinarith [hc2, e1, e2, e3]
  · -- b = 10, b' = 7: `4 * c = 7 * c'`, no solution.
    have hb'v : b' = 7 := det_of (by norm_num) (by norm_num) hb1 hb2
    subst hb'v
    obtain ⟨m, rfl⟩ : 7 ∣ c := by omega
    have hc'v : c' = 4 * m := by omega
    rw [hc'v] at hc2
    have hm1 : 1 ≤ m := by omega
    have e1 : m ≤ m ^ 3 := Nat.le_self_pow three_ne_zero m
    have e2 : m ^ 2 ≤ m ^ 3 := Nat.pow_le_pow_right (by omega : 0 < m) (by norm_num)
    have e3 : 1 ≤ m ^ 3 := Nat.one_le_pow _ _ (by omega : 0 < m)
    exfalso
    nlinarith [hc2, e1, e2, e3]

snip end

determine solution_set : Set (ℕ × ℕ × ℕ) := {⟨2, 3, 5⟩, ⟨2, 5, 6⟩}

problem imo1976_p3 (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a ≤ b) (hbc : b ≤ c) :
    ⟨a, b, c⟩ ∈ solution_set ↔
      a * b * c = 5 * (⌊(a : ℝ) / k⌋₊ * ⌊(b : ℝ) / k⌋₊ * ⌊(c : ℝ) / k⌋₊) := by
  constructor
  · intro h
    simp only [solution_set, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · norm_num [Nat.cast_ofNat, floor_two, floor_three, floor_five]
    · norm_num [Nat.cast_ofNat, floor_two, floor_five, floor_six]
  · intro h
    obtain ⟨ha1, ha2⟩ := floor_spec a
    obtain ⟨hb1, hb2⟩ := floor_spec b
    obtain ⟨hc1, hc2⟩ := floor_spec c
    rcases main_nat ha hb hc hab hbc ha1 ha2 hb1 hb2 hc1 hc2 h with
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp [solution_set]
    · simp [solution_set]

end Imo1976P3
