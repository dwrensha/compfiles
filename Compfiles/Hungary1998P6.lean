/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Nat.Prime
import Mathlib.Algebra.Associated
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Ring

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# Hungarian Mathematical Olympiad 1998, Problem 6

Let x, y, z be integers with z > 1. Show that

 (x + 1)² + (x + 2)² + ... + (x + 99)² ≠ yᶻ.
-/

namespace Hungary1998P6
open BigOperators

snip begin

lemma sum_range_square_mul_six (n : ℕ) :
    (∑i in Finset.range n, (i + 1)^2) * 6 = n * (n + 1) * (2 * n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Finset.sum_range_succ, add_mul, ih, Nat.succ_eq_add_one]
    ring

lemma sum_range_square (n : ℕ) :
    ∑i in Finset.range n, (i + 1)^2 = n * (n + 1) * (2 * n + 1)/6 :=
  by rw [← sum_range_square_mul_six n, Nat.mul_div_cancel]
     norm_num

lemma cast_sum_square (n : ℕ) :
  ∑i in Finset.range n, ((i:ℤ)+1)^2 =
   (((∑i in Finset.range n, (i+1)^2) : ℕ) : ℤ) := by norm_cast

snip end

problem hungary1998_p6 (x y : ℤ) (z : ℕ) (hz : 1 < z) :
    ∑ i in Finset.range 99, (x + i + 1)^2 ≠ y^z := by
  -- Follows the proof in _Mathematical Olympiads 1998-1999_
  -- by Titu Andreescu and Zuming Feng.

  -- Suppose (x + 1)² + (x + 2)² + ... + (x + 99)² = yᶻ.

  intro he

  -- We notice that
  -- y^z = (x + 1)² + (x + 2)² + ... + (x + 99)²
  --     = 99x² + 2(1 + 2 + ... + 99)x + (1² + 2² + ... + 99²)
  --     = 99x² + 2[(99 ⬝ 100)/2]x + (99 ⬝ 100 ⬝ 199)/6
  --     = 33(3x² + 300x + 50 ⬝ 199).

  have h2 : ∑ i in Finset.range 99, (x^2) = 99 * x^2 := by norm_num

  have h4 : ∑ i in Finset.range 99, ((i:ℤ) + 1) =
          ∑ i in Finset.range 100, (i:ℤ) := by
    rw [Finset.sum_range_succ']; rfl

  have h5 : ∑ i in Finset.range 100, (i:ℤ) = 99 * 100 / 2 := by
    rw [←Nat.cast_sum, Finset.sum_range_id]; decide

  have h6 : ∑ i in Finset.range 99, ((i:ℤ) + 1)^2 = (99 * 100 * 199)/6 := by
    rw [cast_sum_square, sum_range_square]; decide

  have hnn1 : (99:ℤ) * 100 / 2 = 99 * 50 := by decide
  have hnn2 : ((99:ℤ) * 100 * 199)/6 = 33 * 50 * 199 := by decide

  have h7 := calc y^z
      = ∑ i in Finset.range 99, ((x + i) + 1)^2 := he.symm
    _ = ∑ i in Finset.range 99,
          (x^2 + 2 * x * ((i:ℤ) + 1) + ((i:ℤ) + 1)^2) :=
               by with_reducible congr; funext; ring
    _ = ∑ i in Finset.range 99, (x^2 + 2 * x * ((i:ℤ) + 1)) +
         ∑ i in Finset.range 99, (((i:ℤ) + 1)^2) := Finset.sum_add_distrib
    _ = ∑ i in Finset.range 99, x^2 +
          ∑ i in Finset.range 99, (2 * x * ((i:ℤ) + 1)) +
         ∑ i in Finset.range 99, (((i:ℤ) + 1)^2) := by rw [Finset.sum_add_distrib]
    _ = 99 * x^2 + 2 * x * (99 * 100 / 2) +  (99 * 100 * 199)/6
        := by rw [h2, ←Finset.mul_sum, h4, h5, h6]
    _ = 3 * (11 * (3 * x^2 + 300 * x + 50 * 199)) := by rw [hnn1,hnn2]; ring

  -- which implies that 3∣y.
  have h8 : 3 ∣ y^z := Dvd.intro _ (Eq.symm h7)
  have h9 : 3 ∣ y := Prime.dvd_of_dvd_pow Int.prime_three h8

  obtain ⟨k,hk⟩ := h9
  rw [hk] at h7

  cases z with | zero => exact Nat.not_lt_zero 1 hz | succ z =>
  cases z with | zero => exact Nat.lt_asymm hz hz | succ z =>
  rw [pow_succ, pow_succ] at h7

  -- Since z ≥ 2, 3²∣yᶻ, but 3² does not divide
  -- 33(3x² + 300x + 50 ⬝ 199), contradiction.

  have h10 : 3 * k * (3 * k * (3 * k) ^ z) = 3 * (k * (3 * k * (3 * k) ^ z))
       := by ring
  rw [h10] at h7
  have h11 : (3:ℤ) ≠ 0 := by norm_num
  have h12 : k * (3 * k * (3 * k) ^ z) = (11 * (3 * x ^ 2 + 300 * x + 50 * 199)) :=
    (mul_right_inj' h11).mp h7
  have h14 : (k * (3 * k * (3 * k) ^ z)) = (3 * (k * k * (3 * k) ^ z)) :=
    by ring
  have h16 : 11 * (3 * x ^ 2 + 300 * x + 50 * 199) =
    3 * (11 * (x ^ 2 + 100 * x + 3316) + 7) + 1 := by ring
  rw [h14,h16] at h12

  apply_fun (· % 3) at h12

  have h19 : (3 * (11 * (x ^ 2 + 100 * x + 3316) + 7) + 1) % 3 =
     (((3 * (11 * (x ^ 2 + 100 * x + 3316) + 7))% 3) + (1%3)) % 3 :=
   Int.add_emod _ _ _

  rw [h19] at h12
  norm_num at h12
