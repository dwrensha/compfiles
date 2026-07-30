/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Data.Int.Star
public import Mathlib.FieldTheory.Finite.Basic
public import ProblemExtraction

@[expose] public section

problem_file {
  tags := [.NumberTheory]
}

/-!
# USA Mathematical Olympiad 1991, Problem 3

Define the function $f$ on the natural numbers by $f(1) = 2$, $f(n) = 2^{f(n-1)}$.
Show that $f(n)$ has the same residue mod $m$ for all sufficiently large $n$.
-/

namespace Usa1991P3

/-- The tower-of-exponents function of the problem, with the index shifted by one:
`f 0 = 2` and `f (n + 1) = 2 ^ f n`, so that the problem's `f n` is our `f (n - 1)`. -/
def f : ℕ → ℕ
  | 0 => 2
  | n + 1 => 2 ^ f n

snip begin

/- The trick of the problem is to use strong induction on the modulus `m`
(not on `n`). The case `m = 1` is trivial. If `m` is even, write `m = 2 ^ a * b`
with `b` odd: by the induction hypothesis `f n` is eventually constant mod `b`,
while `f n` is eventually `0` mod `2 ^ a`, so the Chinese remainder theorem gives
that `f n` is eventually constant mod `m`. If `m` is odd, then `2 ^ φ m ≡ 1 [MOD m]`
by Euler's theorem and `φ m < m`, so by the induction hypothesis `f n` is eventually
constant mod `φ m`, and hence `f (n + 1) = 2 ^ f n` is eventually constant mod `m`. -/

lemma f_succ (n : ℕ) : f (n + 1) = 2 ^ f n := rfl

/-- The tower grows at least linearly. -/
lemma le_f (n : ℕ) : n + 2 ≤ f n := by
  induction n with
  | zero => exact Nat.le.refl
  | succ k ih =>
    have h1 : 2 ^ (k + 2) ≤ 2 ^ f k := Nat.pow_le_pow_right (by norm_num) ih
    have h2 : k + 3 ≤ 2 ^ (k + 2) := by
      have h : k + 2 < 2 ^ (k + 2) := Nat.lt_two_pow_self
      omega
    calc k + 1 + 2 = k + 3 := rfl
    _ ≤ 2 ^ (k + 2) := h2
    _ ≤ 2 ^ f k := h1
    _ = f (k + 1) := rfl

lemma f_monotone : Monotone f := by
  apply monotone_nat_of_le_succ
  intro n
  have h : f n < 2 ^ f n := Nat.lt_two_pow_self
  calc f n ≤ 2 ^ f n := h.le
  _ = f (n + 1) := rfl

/-- Eventually `f n` is divisible by any prescribed power of two. -/
lemma two_pow_dvd_f (a n : ℕ) (ha : 1 ≤ a) (hn : a ≤ n) : 2 ^ a ∣ f n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have h : a ≤ f k := by have := le_f k; omega
  exact Nat.pow_dvd_pow 2 h

/-- Main step: strong induction on the modulus. -/
lemma eventually_constant_mod (m : ℕ) (hm : 1 ≤ m) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → f n ≡ f N [MOD m] := by
  induction m using Nat.strong_induction_on with
  | _ m IH =>
    rcases eq_or_lt_of_le hm with h1 | h2
    · -- modulus `1`: trivial
      subst h1
      exact ⟨0, fun n _ => by simp only [Nat.ModEq, Nat.mod_one]⟩
    · by_cases hev : Even m
      · -- even modulus: split `m = 2 ^ a * b` with `b` odd
        obtain ⟨a, b, hb_odd, rfl⟩ := Nat.exists_eq_two_pow_mul_odd (n := m) (by omega)
        have ha : 1 ≤ a := by
          rcases Nat.eq_zero_or_pos a with h | h
          · subst h
            rw [pow_zero, one_mul] at hev
            exact absurd hev (Nat.not_even_iff_odd.mpr hb_odd)
          · exact h
        have hb1 : 1 ≤ b := by obtain ⟨k, hk⟩ := hb_odd; omega
        have h2a : 2 ≤ 2 ^ a := by
          calc 2 = 2 ^ 1 := rfl
          _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
        have hbm : b < 2 ^ a * b := by nlinarith [hb1, h2a]
        obtain ⟨N₁, hN₁⟩ := IH b hbm hb1
        have hcop : Nat.Coprime (2 ^ a) b := (Nat.coprime_two_left.mpr hb_odd).pow_left a
        refine ⟨max N₁ a, fun n hn => ?_⟩
        rw [← Nat.modEq_and_modEq_iff_modEq_mul hcop]
        refine ⟨?_, ?_⟩
        · -- mod `2 ^ a`: both sides are congruent to `0`
          have e1 : f n ≡ 0 [MOD 2 ^ a] :=
            Nat.modEq_zero_iff_dvd.mpr (two_pow_dvd_f a n ha (le_trans (le_max_right N₁ a) hn))
          have e2 : f (max N₁ a) ≡ 0 [MOD 2 ^ a] :=
            Nat.modEq_zero_iff_dvd.mpr (two_pow_dvd_f a _ ha (le_max_right N₁ a))
          exact e1.trans e2.symm
        · -- mod `b`: both sides agree with `f N₁`
          exact (hN₁ n (le_trans (le_max_left N₁ a) hn)).trans
            (hN₁ (max N₁ a) (le_max_left N₁ a)).symm
      · -- odd modulus: Euler's theorem
        have hodd : Odd m := Nat.not_even_iff_odd.mp hev
        obtain ⟨N₁, hN₁⟩ := IH (Nat.totient m) (Nat.totient_lt m h2)
          (Nat.totient_pos.mpr (by omega : 0 < m))
        have heuler : 2 ^ Nat.totient m ≡ 1 [MOD m] :=
          Nat.ModEq.pow_totient (Nat.coprime_two_left.mpr hodd)
        refine ⟨N₁ + 1, fun n hn => ?_⟩
        obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
        have hk : N₁ ≤ k := by omega
        have hle : f N₁ ≤ f k := f_monotone hk
        obtain ⟨t, ht⟩ := (Nat.modEq_iff_dvd' hle).mp (hN₁ k hk).symm
        have hfk : f k = f N₁ + Nat.totient m * t := by omega
        have hfn : f (k + 1) = 2 ^ f N₁ * (2 ^ Nat.totient m) ^ t := by
          rw [f_succ, hfk, pow_add, pow_mul]
        have h : 2 ^ f N₁ * (2 ^ Nat.totient m) ^ t ≡ 2 ^ f N₁ [MOD m] := by
          have h2' := (heuler.pow t).mul_left (2 ^ f N₁)
          rwa [one_pow, mul_one] at h2'
        rw [hfn, f_succ N₁]
        exact h

snip end

problem usa1991_p3 (m : ℕ) (hm : 1 ≤ m) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → f n ≡ f N [MOD m] :=
  eventually_constant_mod m hm

end Usa1991P3
