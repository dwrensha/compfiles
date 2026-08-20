/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.Prime.Int
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.LinearCombination.Lemmas
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.NumberTheory] }

/-!
# USA Mathematical Olympiad 2019, Problem 5

Let m and n be relatively prime positive integers. The numbers m/n and n/m are
written on a blackboard. At any point, Evan may pick two of the numbers x and y
written on the board and write either their arithmetic mean (x+y)/2 or their
harmonic mean 2xy/(x+y). For which (m, n) can Evan write 1 on the board in
finitely many steps?
-/

namespace Usa2019P5

snip begin

/-- The rational numbers that Evan can write on the board,
starting from `m / n` and `n / m`. -/
inductive Writable (m n : ℕ) : ℚ → Prop
  | base₁ : Writable m n ((m : ℚ) / n)
  | base₂ : Writable m n ((n : ℚ) / m)
  | am {x y : ℚ} : Writable m n x → Writable m n y → Writable m n ((x + y) / 2)
  | hm {x y : ℚ} : Writable m n x → Writable m n y → Writable m n (2 * x * y / (x + y))

/-- If `p ∣ a + b` and `p ∣ c + d`, then `a * d + b * c ≡ -2 * b * d (mod p)`. -/
theorem sum_dvd_cong {p a b c d : ℤ} (hpab : p ∣ a + b) (hpcd : p ∣ c + d) :
    a * d + b * c ≡ -2 * b * d [ZMOD p] := by
  have hab : a ≡ -b [ZMOD p] := by
    rw [Int.modEq_iff_dvd]
    have e : -b - a = -(a + b) := by ring
    rw [e]
    exact dvd_neg.mpr hpab
  have hcd : c ≡ -d [ZMOD p] := by
    rw [Int.modEq_iff_dvd]
    have e : -d - c = -(c + d) := by ring
    rw [e]
    exact dvd_neg.mpr hpcd
  have h := (hab.mul_right d).add (hcd.mul_left b)
  ring_nf at h ⊢
  exact h

/-- If `p ∣ a * d + b * c` and `a * d + b * c ≡ -2 * b * d (mod p)`,
then `p ∣ 2 * b * d`. -/
theorem dvd_two_mul_mul_of_dvd {p a b c d : ℤ}
    (h : p ∣ a * d + b * c) (hcong : a * d + b * c ≡ -2 * b * d [ZMOD p]) :
    p ∣ 2 * b * d := by
  rw [Int.modEq_iff_dvd] at hcong
  have h3 := dvd_add h hcong
  rw [add_sub_cancel, neg_mul, neg_mul] at h3
  exact dvd_neg.mp h3

/-- An odd prime dividing neither `b` nor `d` does not divide `2 * b * d`. -/
theorem not_dvd_two_mul_mul {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {b d : ℤ}
    (hpb : ¬(p : ℤ) ∣ b) (hpd : ¬(p : ℤ) ∣ d) : ¬(p : ℤ) ∣ 2 * b * d := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hp2Z : ¬(p : ℤ) ∣ 2 := by
    intro h
    have h2 : p ∣ 2 := by exact_mod_cast h
    exact hp2 (le_antisymm (Nat.le_of_dvd two_pos h2) hp.two_le)
  intro h
  rcases hpZ.dvd_mul.mp h with h | h
  · rcases hpZ.dvd_mul.mp h with h | h
    · exact hp2Z h
    · exact hpb h
  · exact hpd h

/-- The key invariant: if an odd prime `p` divides `m + n`, then every number that
Evan can write has a representation `a / b` with `p ∣ a + b` and `p ∤ b`.
(Equivalently, in lowest terms the value is `≡ -1 (mod p)`.) -/
theorem Writable.exists_rep {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m.Coprime n)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpd : p ∣ m + n)
    {x : ℚ} (hx : Writable m n x) :
    ∃ a b : ℤ, b ≠ 0 ∧ x = (a : ℚ) / b ∧ (p : ℤ) ∣ a + b ∧ ¬(p : ℤ) ∣ b := by
  induction hx with
  | base₁ =>
    have hgcd : m.gcd n = 1 := hmn
    refine ⟨(m : ℤ), (n : ℤ), by exact_mod_cast hn.ne',
      by simp, by exact_mod_cast hpd, ?_⟩
    intro h
    rw [Int.natCast_dvd_natCast] at h
    have h1 : p ∣ m := (Nat.dvd_add_left h).mp hpd
    have h2 := Nat.dvd_gcd h1 h
    rw [hgcd, Nat.dvd_one] at h2
    exact hp.ne_one h2
  | base₂ =>
    have hgcd : m.gcd n = 1 := hmn
    refine ⟨(n : ℤ), (m : ℤ), by exact_mod_cast hm.ne',
      by simp, by rw [add_comm]; exact_mod_cast hpd, ?_⟩
    intro h
    rw [Int.natCast_dvd_natCast] at h
    have h1 : p ∣ n := (Nat.dvd_add_right h).mp hpd
    have h2 := Nat.dvd_gcd h h1
    rw [hgcd, Nat.dvd_one] at h2
    exact hp.ne_one h2
  | am hx hy ihx ihy =>
    obtain ⟨a, b, hb, rfl, hpab, hpb⟩ := ihx
    obtain ⟨c, d, hd, rfl, hpcd, hpd'⟩ := ihy
    have h2bd := not_dvd_two_mul_mul hp hp2 hpb hpd'
    refine ⟨a * d + b * c, 2 * b * d,
      mul_ne_zero (mul_ne_zero two_ne_zero hb) hd, ?_, ?_, h2bd⟩
    · have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast hb
      have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd
      push_cast
      field_simp
    · obtain ⟨s, hs⟩ := hpab
      obtain ⟨t, ht⟩ := hpcd
      exact ⟨s * d + b * t, by linear_combination d * hs + b * ht⟩
  | hm hx hy ihx ihy =>
    obtain ⟨a, b, hb, rfl, hpab, hpb⟩ := ihx
    obtain ⟨c, d, hd, rfl, hpcd, hpd'⟩ := ihy
    have hcong := sum_dvd_cong hpab hpcd
    have h2bd := not_dvd_two_mul_mul hp hp2 hpb hpd'
    have hne1 : ¬(p : ℤ) ∣ a * d + b * c :=
      fun h ↦ h2bd (dvd_two_mul_mul_of_dvd h hcong)
    have hne : a * d + b * c ≠ 0 := by
      intro h0
      rw [h0] at hne1
      exact hne1 (dvd_zero _)
    refine ⟨2 * a * c, a * d + b * c, hne, ?_, ?_, hne1⟩
    · have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast hb
      have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd
      have hbd' : ((b * d : ℤ) : ℚ) ≠ 0 := by exact_mod_cast mul_ne_zero hb hd
      have hne' : ((a * d + b * c : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hne
      have hsum : (a : ℚ) / (b : ℚ) + (c : ℚ) / (d : ℚ) =
          ((a * d + b * c : ℤ) : ℚ) / (b * d) := by
        push_cast
        field_simp
      have hprod : (2 : ℚ) * ((a : ℚ) / (b : ℚ)) * ((c : ℚ) / (d : ℚ)) =
          ((2 * a * c : ℤ) : ℚ) / (b * d) := by
        push_cast
        field_simp
      rw [hsum, hprod]
      field_simp
    · obtain ⟨s, hs⟩ := hpab
      obtain ⟨t, ht⟩ := hpcd
      exact ⟨a * t + c * s, by linear_combination a * ht + c * hs⟩

/-- Any natural number `≥ 2` that is not a power of two has an odd prime factor. -/
theorem exists_odd_prime_dvd {N : ℕ} (hN : 2 ≤ N) (h : ∀ k : ℕ, N ≠ 2 ^ k) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ p ∣ N := by
  obtain ⟨e, t, ht, hNeq⟩ := Nat.exists_eq_two_pow_mul_odd (n := N) (by lia)
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [mul_one] at hNeq
    exact h e hNeq
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hNeq
    lia
  obtain ⟨p, hp, hpt⟩ := Nat.exists_prime_and_dvd ht1
  have hp2 : p ≠ 2 := by
    rintro rfl
    rw [Nat.dvd_iff_mod_eq_zero] at hpt
    rw [Nat.odd_iff] at ht
    lia
  exact ⟨p, hp, hp.odd_of_ne_two hp2, hNeq ▸ dvd_mul_of_dvd_right hpt (2 ^ e)⟩

/-- Any dyadic weighted average of two writable numbers is writable
(using arithmetic means alone). -/
theorem writable_combo {m n : ℕ} (k : ℕ) :
    ∀ {a b : ℕ} {x y : ℚ}, a + b = 2 ^ k → Writable m n x → Writable m n y →
      Writable m n (((a : ℚ) * x + (b : ℚ) * y) / ((2 ^ k : ℕ) : ℚ)) := by
  induction k with
  | zero =>
    intro a b x y hab hx hy
    rw [pow_zero] at hab
    have h : (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by lia
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simpa using hy
    · simpa using hx
  | succ k ih =>
    intro a b x y hab hx hy
    have h2k : ((2 : ℚ) ^ k) ≠ 0 := pow_ne_zero _ two_ne_zero
    have h2k1 : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
    rw [h2k1] at hab
    rcases le_total a (2 ^ k) with hle | hle
    · have hu := ih (a := a) (b := 2 ^ k - a) (by lia) hx hy
      have e : ((a : ℚ) * x + (b : ℚ) * y) / ((2 ^ (k + 1) : ℕ) : ℚ) =
          (((a : ℚ) * x + ((2 ^ k - a : ℕ) : ℚ) * y) / ((2 ^ k : ℕ) : ℚ) + y) / 2 := by
        have hbeq : b = (2 ^ k - a) + 2 ^ k := by lia
        rw [hbeq, h2k1]
        push_cast [Nat.cast_sub hle]
        have h2k1' : (2 : ℚ) * (2 : ℚ) ^ k ≠ 0 := mul_ne_zero two_ne_zero h2k
        field_simp
        ring
      rw [e]
      exact Writable.am hu hy
    · have hleb : b ≤ 2 ^ k := by lia
      have hu := ih (a := 2 ^ k - b) (b := b) (by lia) hx hy
      have e : ((a : ℚ) * x + (b : ℚ) * y) / ((2 ^ (k + 1) : ℕ) : ℚ) =
          ((((2 ^ k - b : ℕ) : ℚ) * x + (b : ℚ) * y) / ((2 ^ k : ℕ) : ℚ) + x) / 2 := by
        have haeq : a = (2 ^ k - b) + 2 ^ k := by lia
        rw [haeq, h2k1]
        push_cast [Nat.cast_sub hleb]
        have h2k1' : (2 : ℚ) * (2 : ℚ) ^ k ≠ 0 := mul_ne_zero two_ne_zero h2k
        field_simp
        ring
      rw [e]
      exact Writable.am hu hx

snip end

determine solution_set : Set (ℕ × ℕ) := { (m, n) | ∃ k : ℕ, m + n = 2 ^ k }

problem usa2019_p5 (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : m.Coprime n) :
    (m, n) ∈ solution_set ↔ Writable m n 1 := by
  -- Informal proof outline from
  -- https://web.evanchen.cc/exams/USAMO-2019-notes.pdf (solution to 2019/5).
  constructor
  · -- If `m + n = 2 ^ k`, then `1 = (n * (m / n) + m * (n / m)) / 2 ^ k` is writable.
    intro h
    change ∃ k : ℕ, m + n = 2 ^ k at h
    obtain ⟨k, hk⟩ := h
    have hw := writable_combo k (a := n) (b := m) (x := (m : ℚ) / (n : ℚ))
      (y := (n : ℚ) / (m : ℚ)) (by lia) Writable.base₁ Writable.base₂
    have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
    have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
    have hmn0 : (m : ℚ) + (n : ℚ) ≠ 0 := by
      have h1 : (0 : ℚ) < (m : ℚ) + (n : ℚ) := by exact_mod_cast (by lia)
      exact ne_of_gt h1
    have e3 : ((n : ℚ) * ((m : ℚ) / (n : ℚ)) + (m : ℚ) * ((n : ℚ) / (m : ℚ))) /
        ((2 ^ k : ℕ) : ℚ) = 1 := by
      have hkc : ((2 ^ k : ℕ) : ℚ) = (m : ℚ) + (n : ℚ) := by
        rw [← Nat.cast_add, ← hk]
      rw [hkc]
      field_simp
    rwa [e3] at hw
  · -- If some odd prime divides `m + n`, the invariant shows `1` is not writable.
    intro hw
    by_contra h
    change ¬∃ k : ℕ, m + n = 2 ^ k at h
    rw [not_exists] at h
    obtain ⟨p, hp, hodd, hpd⟩ := exists_odd_prime_dvd (by lia) h
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact (by decide : ¬ Odd 2) hodd
    obtain ⟨a, b, hb0, h1, hpab, hpb⟩ := hw.exists_rep hm hn hmn hp hp2 hpd
    have hb0' : (b : ℚ) ≠ 0 := by exact_mod_cast hb0
    have hab : a = b := by
      have h2 := (div_eq_one_iff_eq hb0').mp h1.symm
      exact_mod_cast h2
    rw [hab] at hpab
    rw [← two_mul] at hpab
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    rcases hpZ.dvd_mul.mp hpab with h | h
    · have h2 : p ∣ 2 := by exact_mod_cast h
      exact hp2 (le_antisymm (Nat.le_of_dvd two_pos h2) hp.two_le)
    · exact hpb h

end Usa2019P5
