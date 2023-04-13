import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.ModEq
--import data.nat.prime_norm_num
import Mathlib.Data.ZMod.Basic

import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-
Indian Mathematical Olympiad 1998, problem 1

(a) Show that the product of two numbers of the form a² + 3b² is again of that form.
(b) If an integer n is such that 7n is of the form a² + 3b², prove that n is also of that form.
-/

namespace India1998Q1

theorem india1998_q1a (a₁ a₂ b₁ b₂ : ℤ) :
    (∃ a₃ b₃, (a₁^2 + 3 * b₁^2) * (a₂^2 + 3 * b₂^2) = (a₃^2 + 3 * b₃^2)) :=
  ⟨a₁ * a₂ + 3 * b₁ * b₂, ⟨a₁ * b₂ - b₁ * a₂, by ring⟩⟩

lemma make_nonneg (a b: ℤ) (hb : 0 < b) : 0 ≤ a + b * ((b - a) / b) := by
  linarith[Int.emod_lt_of_pos (b-a) hb, (b - a).emod_add_ediv b]

lemma lemma1' (a : ℤ) (b : ℕ) (hb : 0 < b) : ((a : ZMod b).val : ℤ) = a % (b : ℤ) := by
  have h1: (a : ZMod b) = ((( a + b * ((b - a )/ b)) : ℤ): ZMod b) := by simp
  rw [←Int.add_mul_emod_self_left a b ((b - a)/ b), h1]
  have h2 : 0 ≤ (( a + b * ((b - a )/ b)) : ℤ) := make_nonneg a ↑b (Int.coe_nat_pos.mpr hb)
  obtain ⟨A, hA⟩ := Int.eq_ofNat_of_zero_le h2
  simp [hA, ZMod.val_nat_cast A]

lemma lemma1 (a: ℤ) : ((a : ZMod 7).val : ℤ) = a % 7 := lemma1' a 7 (by norm_num)

lemma seven_is_prime : Nat.Prime 7 := by
  have h1 : 7 ≠ 1 := by norm_num
  have h : Nat.minFac 7 = 7 := by rfl
  exact h ▸ Nat.minFac_prime h1

theorem india1998_q1b (n a b: ℤ) (hn : a^2 + 3 * b^2 = 7 * n) :
    (∃ a b : ℤ, a^2 + 3 * b^2 = n) := by
  let az : ZMod 7 := a
  let bz : ZMod 7 := b

  have h1 := calc az ^ 2 + (-4) * bz ^ 2
        = az^2 + ((3:ℤ): ZMod 7) * bz^2 := by rw [show -4 = ((3:ℤ):ZMod 7) by rfl]
      _ = ((a^2 : ℤ) : ZMod 7) + ((3:ℤ): ZMod 7) * (((b^2) : ℤ) : ZMod 7)
                                   := by rw [Int.cast_pow a 2, Int.cast_pow b 2]
      _ = ((a^2 : ℤ) : ZMod 7) + (((3 * b^2) : ℤ) : ZMod 7) := by rw [Int.cast_mul 3 (b^2)]
      _ = (((a^2 + 3 * b^2) : ℤ) : ZMod 7) := (Int.cast_add _ _).symm
      _ = (((7 * n) : ℤ) : ZMod 7) := congrArg Int.cast hn
      _ = 0 := by {rw [Int.cast_mul]; exact zero_mul _}

  have h9: az ^ 2 + (-4) * bz ^ 2 + 4 * bz^2 = 0 + 4 * bz^2 := congrFun (congrArg HAdd.hAdd h1) _
  rw [neg_mul, neg_add_cancel_right, Fin.zero_add] at h9
  have h10 : 4 * bz^2 = (2 * bz) ^ 2 := by ring
  rw [h10] at h9
  haveI : Fact (Nat.Prime 7) := ⟨seven_is_prime⟩
  obtain (hep : az = 2 * bz) | (hen : az = - (2 * bz)) := eq_or_eq_neg_of_sq_eq_sq _ _ h9
  · have h11: (2 * az + 3 * bz) = 0 := by
      rw [hep]; ring_nf;
      rw [show (7 : ZMod 7) = 0 by rfl, mul_zero]
    have h13: 7 ∣ (2 * a + 3 * b) := by
      have h50 : (2 * az + 3 * bz).val = (0 : ZMod 7).val := congr_arg ZMod.val h11
      rw [ZMod.val_add, ZMod.val_mul, ZMod.val_mul,
          Nat.add_mod_mod, Nat.mod_add_mod, ZMod.val_zero] at h50
      have h52 : ((2 * (az.val:ℤ) + 3 * (bz.val:ℤ))) % 7 = 0 := by norm_cast
      rw [lemma1 a, lemma1 b] at h52
      rw [←Int.emod_add_ediv a 7, ←Int.emod_add_ediv b 7]
      have h53 : 2 * (a % 7 + 7 * (a / 7)) + 3 * (b % 7 + 7 * (b / 7)) =
              2 * (a % 7) + 3 * (b % 7) + 7 * (2 * (a / 7) + 3 * (b / 7)) := by ring
      rw [h53]
      have h54 : 7 ∣ 7 * (2 * (a / 7) + 3 * (b / 7)) := Dvd.intro _ rfl
      exact dvd_add (Int.dvd_of_emod_eq_zero h52) h54
    obtain ⟨m1, hm1⟩ := exists_eq_mul_right_of_dvd h13
    have h15 : (az + (- 2) * bz) = 0 := by{ rw [hep]; ring_nf }
    have h16: 7 ∣ (a + (-2) * b) := by
      have h50 : (az + (-2) * bz).val = (0 : ZMod 7).val := congr_arg ZMod.val h15
      rw [ZMod.val_add, ZMod.val_mul, Nat.add_mod_mod, ZMod.val_zero] at h50
      have h52 : (((az.val:ℤ) + 5 * (bz.val:ℤ))) % 7 = 0 :=  by { norm_cast }
      rw [lemma1 a, lemma1 b] at h52
      have h52' : 7 ∣ a % 7 + 5 * (b % 7) := Int.dvd_of_emod_eq_zero h52
      rw [←Int.emod_add_ediv a 7, ←Int.emod_add_ediv b 7]
      have h53 : a % 7 + 7 * (a / 7) + (-2) * (b % 7 + 7 * (b / 7)) =
              a % 7 + 5 * (b % 7) + 7 * (a / 7 - 2 * (b / 7) - (b % 7)) := by ring
      rw [h53]
      have h54 : 7 ∣ 7 * (a / 7 - 2 * (b / 7) - (b % 7)) := Dvd.intro _ rfl
      exact dvd_add h52' h54
    obtain ⟨m2, hm2⟩ := exists_eq_mul_right_of_dvd h16
    use m1; use m2
    have h20 : (7 * m1) ^ 2 + 3 * (7 * m2) ^ 2 = 7 * 7 * n := by
      rw [←hm1, ←hm2]
      ring_nf
      have h18: 7 * (a ^ 2 + 3 * b ^ 2) = 7 * (7 * n) := congrArg (HMul.hMul 7) hn
      ring_nf at h18
      rw [h18]
    have h21 : (7 * m1) ^ 2 + 3 * (7 * m2) ^ 2 = 7 * 7 * (m1 ^ 2 + 3 * m2 ^ 2) := by ring
    rw[h21] at h20
    have h22 : (7:ℤ) * 7 ≠ 0 := by norm_num
    exact (mul_right_inj' h22).mp h20

  · have h11: (2 * az + (-3) * bz) = 0 := by
      rw [hen]
      ring_nf
      simp[show (7 : ZMod 7) = 0 by rfl]

    have h13: 7 ∣ (2 * a + (-3) * b) := by
      have h50 : (2 * az + (-3) * bz).val = (0 : ZMod 7).val := congr_arg ZMod.val h11
      rw[ZMod.val_add, ZMod.val_mul, ZMod.val_mul,
         Nat.add_mod_mod, Nat.mod_add_mod, ZMod.val_zero] at h50
      have h51 : (2 * az.val + 4 * bz.val) % 7 = 0 := h50
      have h52 : ((2 * (az.val:ℤ) + 4 * (bz.val:ℤ))) % 7 = 0 := by norm_cast
      rw [lemma1 a, lemma1 b] at h52
      rw [←Int.emod_add_ediv a 7, ←Int.emod_add_ediv b 7]
      have h53 : 2 * (a % 7 + 7 * (a / 7)) + (-3) * (b % 7 + 7 * (b / 7)) =
               2 * (a % 7) + 4 * (b % 7) + 7 * (2 * (a / 7) + (-3) * (b / 7) - (b % 7) ) := by ring
      rw [h53]
      have h54 : 7 ∣ 7 * (2 * (a / 7) + (-3) * (b / 7) - b % 7) := Dvd.intro _ rfl
      exact dvd_add (Int.dvd_of_emod_eq_zero h52) h54

    have h14 : (∃ m1, 2 * a + (-3) * b = 7 * m1) := exists_eq_mul_right_of_dvd h13
    obtain ⟨m1, hm1⟩ := h14

    have h15: (az + 2 * bz) = 0 := by { rw [hen]; ring_nf }

    have h16: 7 ∣ (a + 2 * b) := by
      have h50 : (az + 2 * bz).val = (0 : ZMod 7).val := congr_arg ZMod.val h15
      rw [ZMod.val_add, ZMod.val_mul, Nat.add_mod_mod, ZMod.val_zero] at h50
      have h51 : (az.val + 2 * bz.val) % 7 = 0 := h50
      have h52 : (((az.val:ℤ) + 2 * (bz.val:ℤ))) % 7 = 0 := by norm_cast
      rw [lemma1 a, lemma1 b] at h52
      have h52' : 7 ∣ a % 7 + 2 * (b % 7) := Int.dvd_of_emod_eq_zero h52
      rw [←Int.emod_add_ediv a 7, ←Int.emod_add_ediv b 7]
      have h53 : a % 7 + 7 * (a / 7) + 2 * (b % 7 + 7 * (b / 7)) =
              a % 7 + 2 * (b % 7) + 7 * (a / 7 + 2 * (b / 7)) := by ring
      rw [h53]
      have h54 : 7 ∣ 7 * (a / 7 + 2 * (b / 7)) := Dvd.intro _ rfl
      exact dvd_add h52' h54

    have h17 : (∃ m2, a + 2 * b = 7 * m2) := exists_eq_mul_right_of_dvd h16
    obtain ⟨m2, hm2⟩ := h17

    use m1; use m2

    have h20 : (7 * m1) ^ 2 + 3 * (7 * m2) ^ 2 = 7 * 7 * n := by
      rw [←hm1, ←hm2]
      ring_nf
      have h18: 7 * (a ^ 2 + 3 * b ^ 2) = 7 * (7 * n) := congrArg (HMul.hMul 7) hn
      ring_nf at h18
      rw [h18]

    have h21 : (7 * m1) ^ 2 + 3 * (7 * m2) ^ 2 = 7 * 7 * (m1 ^ 2 + 3 * m2 ^ 2) := by ring

    rw[h21] at h20
    have h22 : (7:ℤ) * 7 ≠ 0 := by norm_num
    exact (mul_right_inj' h22).mp h20
