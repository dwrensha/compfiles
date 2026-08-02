/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.NumberTheory] }

/-!
# USA Mathematical Olympiad 1993, Problem 4

The sequence aₙ of odd positive integers is defined as follows:
a₁ = r, a₂ = s, and aₙ is the greatest odd divisor of aₙ₋₁ + aₙ₋₂.
Show that, for sufficiently large n, aₙ is constant and find this
constant (in terms of r and s).
-/

namespace Usa1993P4

/-- The constant value that the sequence eventually takes. -/
determine constant_value (r s : ℕ) : ℕ := Nat.gcd r s

snip begin

/-- Dividing out all factors of two from `2 * m` yields `m` when `m` is odd. -/
theorem ordCompl_two_mul {m : ℕ} (hm : Odd m) : ordCompl[2] (2 * m) = m := by
  have h2m : m ≠ 0 := by obtain ⟨k, hk⟩ := hm; omega
  have hfac2 : (2 : ℕ).factorization 2 = 1 := Nat.Prime.factorization_self Nat.prime_two
  have hnot2 : ¬ (2 : ℕ) ∣ m :=
    fun hd ↦ ((Nat.not_even_iff_odd).mpr hm) ((even_iff_two_dvd).mpr hd)
  have hfacm : m.factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd hnot2
  have hfac : (2 * m).factorization 2 = 1 := by
    rw [Nat.factorization_mul (by norm_num) h2m, Finsupp.add_apply, hfac2, hfacm]
  show 2 * m / 2 ^ (2 * m).factorization 2 = m
  rw [hfac, pow_one]
  omega

variable {r s : ℕ} (hr : Odd r) (hs : Odd s) {a : ℕ → ℕ}
    (ha0 : a 0 = r) (ha1 : a 1 = s)
    (han : ∀ n, a (n + 2) = ordCompl[2] (a (n + 1) + a n))

include hr hs ha0 ha1 han

/-- Every term of the sequence is odd and positive. -/
theorem odd_and_pos (n : ℕ) : Odd (a n) ∧ 0 < a n := by
  induction n using Nat.twoStepInduction with
  | zero =>
    rw [ha0]
    exact ⟨hr, by obtain ⟨k, hk⟩ := hr; omega⟩
  | one =>
    rw [ha1]
    exact ⟨hs, by obtain ⟨k, hk⟩ := hs; omega⟩
  | more n ih1 ih2 =>
    have hsum : a (n + 1) + a n ≠ 0 := by omega
    have h2 : ¬ (2 : ℕ) ∣ ordCompl[2] (a (n + 1) + a n) :=
      Nat.not_dvd_ordCompl Nat.prime_two hsum
    have hodd : Odd (ordCompl[2] (a (n + 1) + a n)) :=
      (Nat.not_even_iff_odd).mp (fun he ↦ h2 ((even_iff_two_dvd).mp he))
    rw [han n]
    exact ⟨hodd, Nat.ordCompl_pos 2 hsum⟩

/-- Each term is at most half the sum of the two previous terms. -/
theorem le_half (n : ℕ) : a (n + 2) ≤ (a (n + 1) + a n) / 2 := by
  obtain ⟨hoddn, hposn⟩ := odd_and_pos hr hs ha0 ha1 han n
  obtain ⟨hoddn1, hposn1⟩ := odd_and_pos hr hs ha0 ha1 han (n + 1)
  have hsum : a (n + 1) + a n ≠ 0 := by omega
  have h2dvd : 2 ∣ a (n + 1) + a n := (hoddn1.add_odd hoddn).two_dvd
  have hfact : 0 < (a (n + 1) + a n).factorization 2 :=
    Nat.Prime.factorization_pos_of_dvd Nat.prime_two hsum h2dvd
  have hproj : (2 : ℕ) ^ 1 ≤ ordProj[2] (a (n + 1) + a n) :=
    pow_le_pow_right₀ (by norm_num) hfact
  rw [pow_one] at hproj
  have hle : 2 * ordCompl[2] (a (n + 1) + a n) ≤ a (n + 1) + a n :=
    calc 2 * ordCompl[2] (a (n + 1) + a n)
        ≤ ordProj[2] (a (n + 1) + a n) * ordCompl[2] (a (n + 1) + a n) :=
          Nat.mul_le_mul hproj le_rfl
      _ = a (n + 1) + a n := Nat.ordProj_mul_ordCompl_eq_self _ _
  rw [han n]
  omega

/-- If two consecutive terms differ, the maximum of the pair strictly
decreases two steps later. -/
theorem descent (n : ℕ) (hne : a n ≠ a (n + 1)) :
    max (a (n + 2)) (a (n + 3)) < max (a n) (a (n + 1)) := by
  have h2 := le_half hr hs ha0 ha1 han n
  have h3 : a (n + 3) ≤ (a (n + 2) + a (n + 1)) / 2 := le_half hr hs ha0 ha1 han (n + 1)
  omega

/-- Some two consecutive terms are eventually equal. -/
theorem eventual_eq : ∃ n, a n = a (n + 1) := by
  by_contra hcon
  push Not at hcon
  have hstep : ∀ k, max (a (2 * k)) (a (2 * k + 1)) + k ≤ max (a 0) (a 1) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hd : max (a (2 * k + 2)) (a (2 * k + 2 + 1)) < max (a (2 * k)) (a (2 * k + 1)) :=
        descent hr hs ha0 ha1 han (2 * k) (hcon (2 * k))
      show max (a (2 * k + 2)) (a (2 * k + 2 + 1)) + (k + 1) ≤ max (a 0) (a 1)
      omega
  have hM := hstep (max (a 0) (a 1))
  obtain ⟨-, hpos⟩ := odd_and_pos hr hs ha0 ha1 han (2 * max (a 0) (a 1) + 1)
  have hle := Nat.le_max_right (a (2 * max (a 0) (a 1))) (a (2 * max (a 0) (a 1) + 1))
  omega

/-- Once two consecutive terms agree, the sequence is constant from then on. -/
theorem stable (n : ℕ) (h : a n = a (n + 1)) (k : ℕ) : a (n + k) = a n := by
  induction k using Nat.twoStepInduction with
  | zero => simp
  | one => exact h.symm
  | more k ih1 ih2 =>
    have hodd : Odd (a n) := (odd_and_pos hr hs ha0 ha1 han n).1
    have e1 : n + (k + 2) = n + k + 2 := rfl
    have e2 : n + (k + 1) = n + k + 1 := rfl
    rw [e1]
    rw [e2] at ih2
    rw [han (n + k), ih1, ih2, ← two_mul]
    exact ordCompl_two_mul hodd

/-- The gcd of two consecutive terms is preserved by the recurrence. -/
theorem gcd_invariant (n : ℕ) :
    Nat.gcd (a (n + 1)) (a (n + 2)) = Nat.gcd (a n) (a (n + 1)) := by
  obtain ⟨hodd1, hpos1⟩ := odd_and_pos hr hs ha0 ha1 han (n + 1)
  obtain ⟨-, hposn⟩ := odd_and_pos hr hs ha0 ha1 han n
  have hsum : a (n + 1) + a n ≠ 0 := by omega
  have hdecomp := Nat.ordProj_mul_ordCompl_eq_self (a (n + 1) + a n) 2
  have hcop : Nat.Coprime (ordProj[2] (a (n + 1) + a n)) (a (n + 1)) :=
    Nat.Coprime.pow_left _ ((Nat.coprime_two_left).mpr hodd1)
  have h1 : Nat.gcd (a (n + 1)) (ordProj[2] (a (n + 1) + a n) * ordCompl[2] (a (n + 1) + a n))
      = Nat.gcd (a (n + 1)) (ordCompl[2] (a (n + 1) + a n)) := by
    rw [Nat.gcd_comm (a (n + 1)) _, Nat.Coprime.gcd_mul_left_cancel _ hcop, Nat.gcd_comm]
  rw [han n, ← h1, hdecomp, Nat.gcd_self_add_right, Nat.gcd_comm]

/-- The gcd of any two consecutive terms equals `gcd r s`. -/
theorem gcd_eq (n : ℕ) : Nat.gcd (a n) (a (n + 1)) = Nat.gcd r s := by
  induction n with
  | zero =>
    show Nat.gcd (a 0) (a 1) = Nat.gcd r s
    rw [ha0, ha1]
  | succ n ih =>
    rw [← ih]
    exact gcd_invariant hr hs ha0 ha1 han n

omit hr hs ha0 ha1 han

snip end

problem usa1993_p4 (r s : ℕ) (hr : Odd r) (hs : Odd s) (a : ℕ → ℕ)
    (ha0 : a 0 = r) (ha1 : a 1 = s)
    (han : ∀ n, a (n + 2) = ordCompl[2] (a (n + 1) + a n)) :
    ∃ N, ∀ n, N ≤ n → a n = constant_value r s := by
  obtain ⟨N, hN⟩ := eventual_eq hr hs ha0 ha1 han
  have hgcd : Nat.gcd (a N) (a (N + 1)) = Nat.gcd r s := gcd_eq hr hs ha0 ha1 han N
  rw [← hN, Nat.gcd_self] at hgcd
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [stable hr hs ha0 ha1 han N hN k, hgcd]

end Usa1993P4
