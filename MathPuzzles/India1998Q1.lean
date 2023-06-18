import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.ZMod.Basic

import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum.Prime


/-
Indian Mathematical Olympiad 1998, problem 1

(a) Show that the product of two numbers of the form a² + 3b² is again of that form.
(b) If an integer n is such that 7n is of the form a² + 3b², prove that n is also of that form.
-/

namespace India1998Q1

theorem india1998_q1a (a₁ a₂ b₁ b₂ : ℤ) :
    (∃ a₃ b₃, (a₁^2 + 3 * b₁^2) * (a₂^2 + 3 * b₂^2) = (a₃^2 + 3 * b₃^2)) :=
  ⟨a₁ * a₂ + 3 * b₁ * b₂, ⟨a₁ * b₂ - b₁ * a₂, by ring⟩⟩

theorem india1998_q1b (n a b: ℤ) (hn : a^2 + 3 * b^2 = 7 * n) :
    (∃ a b : ℤ, a^2 + 3 * b^2 = n) := by
  let az : ZMod 7 := a
  let bz : ZMod 7 := b

  have h1 := calc az ^ 2 + 3 * bz ^ 2
        = (((a^2 + 3 * b^2) : ℤ) : ZMod 7) := by norm_cast
      _ = (((7 * n) : ℤ) : ZMod 7) := congrArg Int.cast hn
      _ = 0 := by {rw [Int.cast_mul]; exact zero_mul _}

  have h2 := show (3 : ZMod 7) = -4 by norm_num
  rw [h2] at h1
  have h9 : az^2 = (2 * bz)^2 := by linear_combination h1
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain (hep : az = 2 * bz) | (hen : az = - (2 * bz)) := eq_or_eq_neg_of_sq_eq_sq _ _ h9
  · have h11 : 2 * az + 3 * bz = 0 := by rw[h2]; linear_combination 2 * hep
    have h13 : 7 ∣ (2 * a + 3 * b) := by
      have h50 : (((2 * a + 3 * b):ℤ) : ZMod 7) = 0 := by dsimp at h11; norm_cast at h11
      exact (ZMod.int_cast_zmod_eq_zero_iff_dvd _ 7).mp h50

    obtain ⟨m1, hm1⟩ := exists_eq_mul_right_of_dvd h13
    have h15 : (az + (- 2) * bz) = 0 := by rw [hep]; ring_nf
    have h16: 7 ∣ (a + (-2) * b) := by
      have h50 : (((a + (-2) * b):ℤ) : ZMod 7) = 0 := by dsimp at h15; norm_cast at h15
      exact (ZMod.int_cast_zmod_eq_zero_iff_dvd _ 7).mp h50
    obtain ⟨m2, hm2⟩ := exists_eq_mul_right_of_dvd h16
    use m1; use m2
    have h20 : (7 * m1) ^ 2 + 3 * (7 * m2) ^ 2 = 7 * 7 * n := by
      rw [←hm1, ←hm2]; linear_combination 7 * hn

    have h21 : (7 * m1) ^ 2 + 3 * (7 * m2) ^ 2 = 7 * 7 * (m1 ^ 2 + 3 * m2 ^ 2) := by ring
    rw[h21] at h20
    have h22 : (7:ℤ) * 7 ≠ 0 := by norm_num
    exact (mul_right_inj' h22).mp h20

  · have h11 : 2 * az + (-3) * bz = 0 := by rw[h2]; linear_combination 2 * hen
    have h13: 7 ∣ (2 * a + (-3) * b) := by
      have h50 : (((2 * a + (-3) * b):ℤ) : ZMod 7) = 0 := by
        dsimp at h11; norm_cast at h11
      exact (ZMod.int_cast_zmod_eq_zero_iff_dvd _ 7).mp h50

    obtain ⟨m1, hm1⟩ := exists_eq_mul_right_of_dvd h13
    have h15 : az + 2 * bz = 0 := by rw [hen]; ring_nf
    have h16 : 7 ∣ (a + 2 * b) := by
      have h50 : (((a + 2 * b):ℤ) : ZMod 7) = 0 := by dsimp at h15; norm_cast at h15
      exact (ZMod.int_cast_zmod_eq_zero_iff_dvd _ 7).mp h50

    obtain ⟨m2, hm2⟩ := exists_eq_mul_right_of_dvd h16
    use m1; use m2

    have h20 : (7 * m1) ^ 2 + 3 * (7 * m2) ^ 2 = 7 * 7 * n := by
      rw [←hm1, ←hm2]; linear_combination 7 * hn

    have h21 : (7 * m1) ^ 2 + 3 * (7 * m2) ^ 2 = 7 * 7 * (m1 ^ 2 + 3 * m2 ^ 2) := by ring
    rw[h21] at h20
    have h22 : (7:ℤ) * 7 ≠ 0 := by norm_num
    exact (mul_right_inj' h22).mp h20
