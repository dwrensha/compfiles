/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Data.Int.Star
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Algebra] }

/-!
# USA Mathematical Olympiad 1972, Problem 4

Let k be the real cube root of 2. Find integers A, B, C, a, b, c such that

  |(Ax² + Bx + C)/(ax² + bx + c) − k| < |x − k|

for all non-negative rational numbers x.
-/

namespace Usa1972P4

/-- The property that the integers `A, B, C, a, b, c` solve the problem for the
real cube root `k` of `2`: the rational function `(Ax² + Bx + C)/(ax² + bx + c)`
approximates `k` strictly better than `x` does, for every non-negative
rational number `x`. -/
abbrev IsSolution (A B C a b c : ℤ) (k : ℝ) : Prop :=
  ∀ x : ℚ, 0 ≤ x →
    |((A : ℝ) * (x : ℝ) ^ 2 + (B : ℝ) * (x : ℝ) + (C : ℝ)) /
        ((a : ℝ) * (x : ℝ) ^ 2 + (b : ℝ) * (x : ℝ) + (c : ℝ)) - k| <
      |(x : ℝ) - k|

snip begin

/-
We follow the solution from
https://prase.cz/kalva/usa/usoln/usol724.html

Take `(A, B, C, a, b, c) = (2, 2, 2, 1, 2, 2)`. Since `k³ = 2`, the numerator
of `(2x² + 2x + 2)/(x² + 2x + 2) − k` factors as
`(2x² + 2x + 2) − (x² + 2x + 2)k = (x − k)((2 − k)x + 2 − k²)`.
For `x ≥ 0`, both `(2 − k)x + 2 − k²` and `x² + 2x + 2` are positive, and the
latter minus the former equals `x² + kx + k² > 0`, so their ratio lies
strictly between `0` and `1`. Multiplying by `|x − k| > 0` (note that `x ≠ k`
because `∛2` is irrational) yields the claim.
-/

/-- There is no rational number whose cube equals `2`. -/
lemma rat_cube_ne_two (q : ℚ) : q ^ 3 ≠ 2 := by
  intro hq
  have hdq : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
  rw [← Rat.num_div_den q, div_pow, div_eq_iff (pow_ne_zero 3 hdq)] at hq
  -- `hq` states `q.num ^ 3 = 2 * q.den ^ 3`, over `ℚ`.
  have h2 : q.num ^ 3 = 2 * (q.den : ℤ) ^ 3 := by exact_mod_cast hq
  -- Hence the numerator is even.
  have hEvenNum : Even q.num := by
    rcases Int.even_or_odd q.num with hE | hO
    · exact hE
    · exfalso
      have hO3 : Odd (q.num ^ 3) := hO.pow
      rw [h2] at hO3
      obtain ⟨r, hr⟩ := hO3
      obtain ⟨s, hs⟩ := (⟨(q.den : ℤ) ^ 3, by ring⟩ : Even (2 * (q.den : ℤ) ^ 3))
      lia
  have h2dvdnum : (2 : ℤ) ∣ q.num := even_iff_two_dvd.mp hEvenNum
  obtain ⟨m, hm⟩ := hEvenNum
  -- Hence the denominator is even as well.
  have hEvenDenZ : Even (q.den : ℤ) := by
    rcases Int.even_or_odd (q.den : ℤ) with hE | hO
    · exact hE
    · exfalso
      have h8 : (q.den : ℤ) ^ 3 = 4 * m ^ 3 := by
        have hh : (m + m) ^ 3 = 2 * (q.den : ℤ) ^ 3 := by rwa [← hm]
        have h8m : (m + m) ^ 3 = 8 * m ^ 3 := by ring
        rw [h8m] at hh
        linarith
      have hO3 : Odd ((q.den : ℤ) ^ 3) := hO.pow
      rw [h8] at hO3
      obtain ⟨r, hr⟩ := hO3
      obtain ⟨s, hs⟩ := (⟨2 * m ^ 3, by ring⟩ : Even (4 * m ^ 3))
      lia
  have hEvenDen : Even q.den := by exact_mod_cast hEvenDenZ
  -- But the numerator and denominator of a rational number are coprime.
  have hdvd : (2 : ℕ) ∣ Nat.gcd q.num.natAbs q.den := by
    refine Nat.dvd_gcd ?_ (even_iff_two_dvd.mp hEvenDen)
    have h' : (2 : ℤ) ∣ (q.num.natAbs : ℤ) := Int.dvd_natAbs.mpr h2dvdnum
    exact_mod_cast h'
  rw [q.reduced.gcd_eq_one] at hdvd
  norm_num at hdvd

/-- A rational number is never equal to the real cube root of `2`. -/
lemma ratCast_ne_of_cube_eq_two {k : ℝ} (hk : k ^ 3 = 2) (q : ℚ) : (q : ℝ) ≠ k := by
  rintro rfl
  have h1 : ((q ^ 3 : ℚ) : ℝ) = 2 := by
    push_cast
    exact hk
  exact rat_cube_ne_two q (by exact_mod_cast h1)

/-- The key factorization, using `k³ = 2`:
`(2x² + 2x + 2) − (x² + 2x + 2)k = (x − k)((2 − k)x + 2 − k²)`. -/
lemma cube_eq_two_factor {k x : ℝ} (hk : k ^ 3 = 2) :
    2 * x ^ 2 + 2 * x + 2 - (x ^ 2 + 2 * x + 2) * k =
      (x - k) * ((2 - k) * x + 2 - k ^ 2) := by
  linear_combination -hk

lemma one_lt_of_cube_eq_two {k : ℝ} (hk : k ^ 3 = 2) : 1 < k := by
  have h3 : Odd 3 := ⟨1, rfl⟩
  rw [← h3.pow_lt_pow, one_pow, hk]
  norm_num

lemma lt_two_of_cube_eq_two {k : ℝ} (hk : k ^ 3 = 2) : k < 2 := by
  have h3 : Odd 3 := ⟨1, rfl⟩
  rw [← h3.pow_lt_pow, hk]
  norm_num

lemma sq_lt_two_of_cube_eq_two {k : ℝ} (hk : k ^ 3 = 2) : k ^ 2 < 2 := by
  have hk1 : 1 < k := one_lt_of_cube_eq_two hk
  have hkpos : 0 < k := zero_lt_one.trans hk1
  have h3 : k ^ 3 = k ^ 2 * k := by ring
  have hk2eq : k ^ 2 = 2 / k := by
    rw [eq_div_iff hkpos.ne', ← h3]
    exact hk
  rw [hk2eq]
  exact div_lt_self (by norm_num) hk1

/-- With `(A, B, C, a, b, c) = (2, 2, 2, 1, 2, 2)`, the required inequality
holds for every non-negative rational number `x`. -/
lemma main_inequality {k : ℝ} (hk : k ^ 3 = 2) (x : ℚ) (hx : 0 ≤ x) :
    |(2 * (x : ℝ) ^ 2 + 2 * (x : ℝ) + 2) / ((x : ℝ) ^ 2 + 2 * (x : ℝ) + 2) - k| <
      |(x : ℝ) - k| := by
  have hkpos : 0 < k := zero_lt_one.trans (one_lt_of_cube_eq_two hk)
  have hk2 : k < 2 := lt_two_of_cube_eq_two hk
  have hk2sq : k ^ 2 < 2 := sq_lt_two_of_cube_eq_two hk
  have hxr : (0 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  -- The denominator is positive.
  have hD : 0 < (x : ℝ) ^ 2 + 2 * (x : ℝ) + 2 := by
    have hsq := sq_nonneg (x : ℝ)
    linarith
  -- The second factor of the factored numerator is positive.
  have hN : 0 < (2 - k) * (x : ℝ) + 2 - k ^ 2 := by
    have h1 : 0 ≤ (2 - k) * (x : ℝ) := mul_nonneg (by linarith) hxr
    linarith
  -- ... and smaller than the denominator, since their difference is
  -- `x² + kx + k² > 0`.
  have hNltD : (2 - k) * (x : ℝ) + 2 - k ^ 2 < (x : ℝ) ^ 2 + 2 * (x : ℝ) + 2 := by
    have hkx : 0 ≤ k * (x : ℝ) := mul_nonneg hkpos.le hxr
    have hsq := sq_nonneg (x : ℝ)
    have hk2pos : 0 < k ^ 2 := pow_pos hkpos 2
    linarith
  have habs : 0 < |(x : ℝ) - k| :=
    abs_pos.mpr (sub_ne_zero.mpr (ratCast_ne_of_cube_eq_two hk x))
  have hDne : (x : ℝ) ^ 2 + 2 * (x : ℝ) + 2 ≠ 0 := hD.ne'
  rw [div_sub' hDne, cube_eq_two_factor hk, abs_div, abs_mul, abs_of_pos hN,
    abs_of_pos hD, mul_div_assoc]
  have h1 : ((2 - k) * (x : ℝ) + 2 - k ^ 2) / ((x : ℝ) ^ 2 + 2 * (x : ℝ) + 2) < 1 :=
    (div_lt_one hD).mpr hNltD
  exact (mul_lt_mul_of_pos_left h1 habs).trans_eq (mul_one _)

snip end

determine solution : ℤ × ℤ × ℤ × ℤ × ℤ × ℤ := (2, 2, 2, 1, 2, 2)

problem usa1972_p4 (k : ℝ) (hk : k ^ 3 = 2) :
    match solution with
    | (A, B, C, a, b, c) => IsSolution A B C a b c k := by
  intro x hx
  simp only [Int.cast_ofNat, Int.cast_one, one_mul]
  exact main_inequality hk x hx

end Usa1972P4
