/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benpigchu
-/

import Mathlib
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Olympiad 1999, Problem 4

Determine all pairs of positive integers (n,p) such that p is
a prime, n not exceeded 2p, and (p-1)ⁿ + 1 is divisible by of nᵖ⁻¹.
-/

namespace Imo1999P4

snip begin

lemma exists_least_prime_factor {n : ℕ} (hn : n ≠ 1) :
    ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ ∀ q : ℕ, q.Prime → q ∣ n → p ≤ q := by
  use Nat.minFac n, Nat.minFac_prime hn, Nat.minFac_dvd n
  intro q hq hqn
  exact Nat.minFac_le_of_dvd hq.two_le hqn

lemma padicValNat_le_padicValNat_of_dvd {p a b : ℕ} (hb: b ≠ 0) (hp: p.Prime) (hab: a ∣ b):
  padicValNat p a ≤ padicValNat p b := by
  haveI: Fact (Nat.Prime p) := { out := hp }
  rw [← padicValNat_dvd_iff_le hb]
  apply dvd_trans _ hab
  exact pow_padicValNat_dvd

lemma aux₁ {a p n: ℕ} (hp : p.Prime) (hp' : 2 < p) (hn : 0 < n)
    (hnp : (p - 1).Coprime n) (hpa: p ∣ a ^ n + 1) :
    p ∣ a + 1 := by
  have := Fact.mk hp
  -- Since $p \nmid a$, we have $a^n \equiv -1 \pmod{p}$, which implies that the order of
  -- $a$ modulo $p$ divides $2n$ but not $n$.
  have h_order : orderOf (a : ZMod p) ∣ 2 * n ∧ ¬(orderOf (a : ZMod p) ∣ n) := by
    simp only [orderOf_dvd_iff_pow_eq_one]
    simp_all only [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow,
      Nat.cast_one, pow_mul', sq_eq_one_iff]
    constructor
    · right; exact eq_neg_of_add_eq_zero_left hpa
    · intro h₁
      rw [h₁] at hpa
      rcases p with ( _ | _ | _ | p ) <;> cases hpa <;> contradiction
  -- Since the order of $a$ modulo $p$ divides $2n$ but not $n$, it must divide $2$.
  have h_order_div_2 : orderOf (a : ZMod p) ∣ 2 := by
    -- Since the order of $a$ modulo $p$ divides $2n$ and $\gcd(p-1, n) = 1$, it must divide $2$.
    have h_order_div_2 : orderOf (a : ZMod p) ∣ p - 1 := by
      simp_all only [orderOf_dvd_iff_pow_eq_one]
      rw [ZMod.pow_card_sub_one_eq_one]
      cases n <;> aesop
    refine Nat.Coprime.dvd_of_dvd_mul_right ?_ h_order.1
    exact Nat.Coprime.coprime_dvd_left h_order_div_2 hnp
  rw [← ZMod.natCast_eq_zero_iff]
  simp_all only [orderOf_dvd_iff_pow_eq_one, sq_eq_one_iff]
  aesop

lemma aux₂ {p n: ℕ} (hp : p.Prime) (hpn : ∀ q : ℕ, q.Prime → q ∣ n → p ≤ q) :
  (p - 1).Coprime n := by
  apply Nat.coprime_of_dvd'
  intro p' hp'₁ hp'₂ hp'₃
  exfalso
  have hp'p := hpn p' hp'₁ hp'₃
  have hp' := hp.two_le
  apply Nat.le_of_dvd (by lia:_) at hp'₂
  lia

snip end

determine SolutionSet : Set (ℕ × ℕ) := {(2,2), (3,3)} ∪ {(n,p) | n = 1 ∧ p.Prime}

problem imo1999_p4 (n p : ℕ) :
    (n,p) ∈ SolutionSet ↔
    0 < n ∧ n ≤ 2 * p ∧ p.Prime ∧ n^(p - 1) ∣ (p - 1)^n + 1 := by
  constructor
  · simp
    intro h
    casesm* _ ∨ _ <;> rcases h with ⟨hn, hp⟩
    · rw [hn, hp]
      norm_num
    · rw [hn, hp]
      norm_num
    · rw [hn]
      norm_num
      constructor
      · rw [Nat.one_le_iff_ne_zero, mul_ne_zero_iff]
        norm_num
        exact hp.ne_zero
      · exact hp
  · rintro ⟨hn, _, hp, h⟩
    simp
    by_cases hn1 : n = 1
    · right
      exact ⟨hn1, hp⟩
    · left
      by_cases hp2 : p = 2
      · left
        rw [hp2] at h
        norm_num at h
        have hn' := Nat.le_of_dvd (by norm_num:_) h
        interval_cases n <;> norm_num at *
        exact hp2
      · right
        rcases exists_least_prime_factor hn1 with ⟨q, ⟨hq₁, hq₂, hq₃⟩⟩
        haveI: Fact (Nat.Prime p) := { out := hp }
        haveI: Fact (Nat.Prime q) := { out := hq₁ }
        have hp' := hp.two_le
        have hq' := hq₁.two_le
        have h' : n ∣ (p - 1) ^ n + 1 := dvd_trans (dvd_pow_self n (by lia:_)) h
        have hq'' : q ∣ (p - 1) ^ n + 1 := dvd_trans hq₂ h'
        have hp_odd : Odd p := Nat.Prime.odd_of_ne_two hp hp2
        have hn_odd : Odd n := by
          rw [← Nat.not_even_iff_odd]
          intro hn'
          apply Dvd.dvd.even h' at hn'
          rw [Nat.even_add'] at hn'
          norm_num at hn'
          rw [Nat.odd_pow_iff (by lia:_), Nat.odd_sub' (by lia:_)] at hn'
          norm_num at hn'
          contrapose! hp_odd
          exact Nat.not_odd_iff_even.mpr hn'
        have hq2 : ¬q = 2 := by
          push_neg
          exact Odd.ne_two_of_dvd_nat hn_odd hq₂
        have hqp := aux₁ hq₁ (by lia:_) (by lia:_) (aux₂ hq₁ hq₃) hq''
        rw [Nat.sub_add_cancel (by lia:_), Nat.prime_dvd_prime_iff_eq hq₁ hp] at hqp
        rw [hqp] at hq₂
        have hp_padic_le := padicValNat_le_padicValNat_of_dvd (by positivity:_) hp h
        rw [padicValNat.pow (p - 1) (by lia:_)] at hp_padic_le
        nth_rw 3 [← one_pow n] at hp_padic_le
        have hlte₁ : p ∣ (p - 1) + 1 := by
          rw [Nat.sub_add_cancel (by lia:_)]
        have hlte₂ : ¬p ∣ (p - 1) := by
          intro h'p
          apply Nat.le_of_dvd (by lia:_) at h'p
          lia
        rw [padicValNat.pow_add_pow hp_odd hlte₁ hlte₂ hn_odd] at hp_padic_le
        rw [Nat.sub_add_cancel (by lia:_), padicValNat_self] at hp_padic_le
        have hpadic_pn := one_le_padicValNat_of_dvd (by lia:_) hq₂
        have hp3' : p ≤ 3 := by
          contrapose! hp_padic_le
          calc 1 + padicValNat p n
              ≤ padicValNat p n + padicValNat p n := add_le_add_left hpadic_pn _
            _ = 2 * padicValNat p n := by ring
            _ < (p - 1) * padicValNat p n := (mul_lt_mul_iff_left₀ (by lia:_)).mpr (by lia:_)
        have hp3 : p = 3 := by lia
        rw [hp3] at h hp_padic_le hq₂
        norm_num at h hp_padic_le
        -- The rest is just IMO1990P3.
        -- If we added `import Compfiles.Imo1990P3` at beginning of the file,
        -- We can get `n = 3` simply by `have hn3 := Imo1990P3.imo_1990_p3_forward n (by lia:_) h`.
        -- We will use another approach here, since we can use the aux lemma again
        -- (and we don't want to depend on other problem files)
        rcases exists_eq_mul_left_of_dvd hq₂ with ⟨m, hm⟩
        rw [hm, mul_pow, pow_mul, pow_right_comm] at h
        norm_num at h
        by_cases hm1 : m = 1
        · rw [hp3, hm, hm1]
          norm_num
        · have hmn : m ∣ n := Dvd.intro 3 (id (Eq.symm hm))
          rw [hm, padicValNat.mul (by lia:_) (by norm_num:_), padicValNat_self] at hp_padic_le
          rcases exists_least_prime_factor hm1 with ⟨qq, ⟨hqq₁, hqq₂, hqq₃⟩⟩
          have hqq'' : qq ∣ 8 ^ m + 1 := dvd_trans (dvd_mul_of_dvd_left (dvd_pow hqq₂ (by lia:_)) 9) h
          have hq1' := hqq₁.two_le
          have hqq2 : ¬qq = 2 := by
            push_neg
            exact Odd.ne_two_of_dvd_nat hn_odd (dvd_trans hqq₂ hmn)
          have hq'p := aux₁ hqq₁ (by lia:_) (by lia:_) (aux₂ hqq₁ hqq₃) hqq''
          norm_num at hq'p
          have hqq_le := Nat.le_of_dvd (by norm_num:_) hq'p
          have hqq3 : qq = 3 := by
            interval_cases qq <;> norm_num at hq'p <;> norm_num at hqq₁ ; norm_num
          rw [hqq3] at hqq₂
          have hpadic_3m := one_le_padicValNat_of_dvd (by lia:_) hqq₂
          rw [Nat.one_le_iff_ne_zero, Nat.ne_zero_iff_zero_lt] at hpadic_3m
          contrapose! hp_padic_le
          ring_nf
          calc 2 + padicValNat 3 m
            _ < 2 + padicValNat 3 m + padicValNat 3 m := (lt_add_iff_pos_right _).mpr hpadic_3m
            _ = 2 + padicValNat 3 m * 2 := by ring

end Imo1999P4
