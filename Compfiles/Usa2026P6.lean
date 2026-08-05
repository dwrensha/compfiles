/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Data.Nat.Factorization.PrimePow
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.NumberTheory] }

/-!
# USA Mathematical Olympiad 2026, Problem 6

Let a and b be positive integers such that φ(ab + 1) divides a² + b² + 1.
Prove that a and b are Fibonacci numbers.
-/

namespace Usa2026P6

snip begin

/-
Mathematical solution sketch by Evan Chen:
https://web.evanchen.cc/exams/USAMO-2026-notes.pdf

* A parity argument shows `ab + 1` must be a prime power `p^e`.
* If `e = 1`, then `ab ∣ a² + b² + 1` and a Vieta jumping argument shows that
  `{a, b} = {F_{2k-1}, F_{2k+1}}`.
* If `e ≥ 2`, write `ab = p^e - 1`; reducing `a² + b² + 1 ≡ 0` mod `p^(e-1)`
  gives `p^(e-1) ∣ (a² + a + 1)(a² - a + 1)`, and the two factors are coprime.
  Since `x² ± x + 1` has a root mod `p` only when `p = 3` or `p ≡ 1 (mod 3)`,
  and `p ≡ 1 (mod 3)` contradicts `3 ∣ a² + b² + 1` (which forces `3 ∤ ab`),
  we must have `p = 3`. Since `9 ∤ x² ± x + 1`, we get `e = 2`, so `ab = 8`,
  and only `(a, b) = (1, 8)` works.
-/

/-- The classification of solutions of `a^2 + b^2 + 1 = 3 * a * b`:
either `a = b = 1`, or `{a, b} = {F_{2k-1}, F_{2k+1}}` for some `k ≥ 1`. -/
def FibPair (a b : ℕ) : Prop :=
  (a = 1 ∧ b = 1) ∨
    ∃ k : ℕ, 1 ≤ k ∧
      ((a = Nat.fib (2 * k - 1) ∧ b = Nat.fib (2 * k + 1)) ∨
        (a = Nat.fib (2 * k + 1) ∧ b = Nat.fib (2 * k - 1)))

/-- Vieta jumping step: if `a * b ∣ a^2 + b^2 + 1` with `0 < a ≤ b`, then the quotient
equals `3`. Strong induction on the sum (the induction hypothesis is passed explicitly). -/
lemma quotient_eq_three_aux {s : ℕ}
    (IH : ∀ t : ℕ, t < s → ∀ a b : ℕ, a + b = t → 0 < a → 0 < b →
      a * b ∣ a ^ 2 + b ^ 2 + 1 → (a ^ 2 + b ^ 2 + 1) / (a * b) = 3)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hsum : a + b = s) (hle : a ≤ b)
    (hdvd : a * b ∣ a ^ 2 + b ^ 2 + 1) : (a ^ 2 + b ^ 2 + 1) / (a * b) = 3 := by
  obtain ⟨k, hk⟩ := hdvd
  have hkq : (a ^ 2 + b ^ 2 + 1) / (a * b) = k := by
    rw [hk, Nat.mul_div_right _ (mul_pos ha hb)]
  rw [hkq]
  -- the other Vieta root `b' = k * a - b`
  have hbk : b ≤ k * a := by
    have h1 : b * b ≤ a * b * k := by
      have h2 : b * b ≤ a ^ 2 + b ^ 2 + 1 := by nlinarith [sq_nonneg a]
      rwa [hk] at h2
    have h3 : b * b ≤ b * (k * a) := by
      convert h1 using 1
      ring
    exact le_of_mul_le_mul_left h3 hb
  have hbb' : b * (k * a - b) = a ^ 2 + 1 := by
    rw [Nat.mul_sub_left_distrib]
    have h2 : b * (k * a) = a * b * k := by ring
    rw [h2, ← hk, pow_two b]
    omega
  have hb'pos : 0 < k * a - b := by
    rcases Nat.eq_zero_or_pos (k * a - b) with h0 | hpos
    · rw [h0, mul_zero] at hbb'
      omega
    · exact hpos
  -- the descended pair `(a, b')` satisfies the same equation with the same `k`
  have hveq : a ^ 2 + (k * a - b) ^ 2 + 1 = a * (k * a - b) * k := by
    have hbb : k * a - b + b = k * a := Nat.sub_add_cancel hbk
    have h1 : a ^ 2 + (k * a - b) ^ 2 + 1 =
        b * (k * a - b) + (k * a - b) * (k * a - b) := by
      rw [pow_two (k * a - b)]
      omega
    rw [h1]
    calc b * (k * a - b) + (k * a - b) * (k * a - b)
        = (k * a - b) * (b + (k * a - b)) := by ring
      _ = (k * a - b) * (k * a) := by rw [add_comm b (k * a - b), hbb]
      _ = a * (k * a - b) * k := by ring
  rcases le_or_gt b (k * a - b) with hcase | hcase
  · -- `b ≤ b'` forces `a = b = 1` and `k = 3`
    have h1 : b * b ≤ a ^ 2 + 1 := by
      have h2 : b * b ≤ b * (k * a - b) := Nat.mul_le_mul_left b hcase
      rwa [hbb'] at h2
    have hab_eq : a = b := by
      by_contra hne
      have hlt : a < b := lt_of_le_of_ne hle hne
      have h3 : (a + 1) * (a + 1) ≤ b * b := Nat.mul_le_mul hlt hlt
      nlinarith [h1, h3, ha]
    subst hab_eq
    have hdv1 : a * a ∣ 1 := by
      have haa : a * a ∣ 2 * (a * a) + 1 := by
        refine ⟨k, ?_⟩
        rw [pow_two a] at hk
        omega
      have hd2 : a * a ∣ 2 * (a * a) := dvd_mul_left (a * a) 2
      exact (Nat.dvd_add_iff_right hd2).mpr haa
    have ha1 : a = 1 := Nat.eq_one_of_mul_eq_one_right (Nat.dvd_one.mp hdv1)
    subst ha1
    omega
  · -- `b' < b`: descend and use the induction hypothesis
    have hsum' : a + (k * a - b) < s := by rw [← hsum]; omega
    have hIH := IH (a + (k * a - b)) hsum' a (k * a - b) rfl ha hb'pos ⟨k, hveq⟩
    have hkq2 : (a ^ 2 + (k * a - b) ^ 2 + 1) / (a * (k * a - b)) = k := by
      rw [hveq, Nat.mul_div_right _ (mul_pos ha hb'pos)]
    omega

/-- If `a * b ∣ a^2 + b^2 + 1` for positive naturals `a, b`, then the quotient is `3`. -/
lemma quotient_eq_three {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hdvd : a * b ∣ a ^ 2 + b ^ 2 + 1) : (a ^ 2 + b ^ 2 + 1) / (a * b) = 3 := by
  have key : ∀ s : ℕ, ∀ a b : ℕ, a + b = s → 0 < a → 0 < b →
      a * b ∣ a ^ 2 + b ^ 2 + 1 → (a ^ 2 + b ^ 2 + 1) / (a * b) = 3 := by
    intro s
    induction s using Nat.strong_induction_on with
    | _ s IH =>
      intro a b hsum ha hb hdvd
      rcases le_or_gt a b with hle | hlt
      · exact quotient_eq_three_aux IH ha hb hsum hle hdvd
      · have hdvd' : b * a ∣ b ^ 2 + a ^ 2 + 1 := by
          rw [mul_comm b a, add_comm (b ^ 2) (a ^ 2)]
          exact hdvd
        have h := quotient_eq_three_aux IH hb ha (by omega) (le_of_lt hlt) hdvd'
        rwa [mul_comm b a, add_comm (b ^ 2) (a ^ 2)] at h
  exact key (a + b) a b rfl ha hb hdvd

/-- The Fibonacci recurrence over four steps: `F_{n+4} + F_n = 3 * F_{n+2}`. -/
lemma fib_add_four (n : ℕ) : Nat.fib (n + 4) + Nat.fib n = 3 * Nat.fib (n + 2) := by
  have h1 : Nat.fib (n + 4) = Nat.fib (n + 2) + Nat.fib (n + 3) := by
    have h := @Nat.fib_add_two (n + 2)
    rwa [show n + 2 + 2 = n + 4 by omega, show n + 2 + 1 = n + 3 by omega] at h
  have h2 : Nat.fib (n + 3) = Nat.fib (n + 1) + Nat.fib (n + 2) := by
    have h := @Nat.fib_add_two (n + 1)
    rwa [show n + 1 + 2 = n + 3 by omega, show n + 1 + 1 = n + 2 by omega] at h
  have h3 : Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) := Nat.fib_add_two
  omega

/-- Vieta jumping for the equation `a^2 + b^2 + 1 = 3 * a * b` with `0 < a ≤ b`:
the pair is a `FibPair`. -/
lemma fib_pair_aux {s : ℕ}
    (IH : ∀ t : ℕ, t < s → ∀ a b : ℕ, a + b = t → 0 < a → 0 < b →
      a ^ 2 + b ^ 2 + 1 = 3 * a * b → FibPair a b)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hsum : a + b = s) (hle : a ≤ b)
    (h : a ^ 2 + b ^ 2 + 1 = 3 * a * b) : FibPair a b := by
  rcases eq_or_lt_of_le hle with heq | hlt
  · -- `a = b` gives `a = b = 1`
    subst heq
    left
    have h1 : a * a = 1 := by
      have h2 : a * a + a * a + 1 = 3 * (a * a) := by
        rw [← mul_assoc 3 a a, ← h, pow_two a]
      omega
    have ha1 : a = 1 := Nat.eq_one_of_mul_eq_one_right h1
    exact ⟨ha1, ha1⟩
  · -- `a < b`: jump down to `(b', a)` with `b' = 3a - b ≤ a`
    have hbk : b ≤ 3 * a := by
      have h1 : b * b ≤ b * (3 * a) := by
        have h2 : b * b ≤ 3 * a * b := by
          have h3 : b * b ≤ a ^ 2 + b ^ 2 + 1 := by nlinarith [sq_nonneg a]
          rwa [h] at h3
        convert h2 using 1
        ring
      exact le_of_mul_le_mul_left h1 hb
    have hbb' : b * (3 * a - b) = a ^ 2 + 1 := by
      rw [Nat.mul_sub_left_distrib]
      have h2 : b * (3 * a) = 3 * a * b := by ring
      rw [h2, ← h, pow_two b]
      omega
    have hb'pos : 0 < 3 * a - b := by
      rcases Nat.eq_zero_or_pos (3 * a - b) with h0 | hpos
      · rw [h0, mul_zero] at hbb'
        omega
      · exact hpos
    have hb'le : 3 * a - b ≤ a := by
      by_contra hcon
      push Not at hcon
      have h1 : (a + 1) * (a + 1) ≤ b * (3 * a - b) := Nat.mul_le_mul hlt hcon
      rw [hbb'] at h1
      nlinarith [h1, ha]
    have hbb : 3 * a - b + b = 3 * a := Nat.sub_add_cancel hbk
    have hveq : a ^ 2 + (3 * a - b) ^ 2 + 1 = 3 * a * (3 * a - b) := by
      have h1 : a ^ 2 + (3 * a - b) ^ 2 + 1 =
          b * (3 * a - b) + (3 * a - b) * (3 * a - b) := by
        rw [pow_two (3 * a - b)]
        omega
      rw [h1]
      calc b * (3 * a - b) + (3 * a - b) * (3 * a - b)
          = (3 * a - b) * (b + (3 * a - b)) := by ring
        _ = (3 * a - b) * (3 * a) := by rw [add_comm b (3 * a - b), hbb]
        _ = 3 * a * (3 * a - b) := by ring
    have hsum' : (3 * a - b) + a < s := by rw [← hsum]; omega
    have hIH := IH ((3 * a - b) + a) hsum' (3 * a - b) a rfl hb'pos ha (by
      rw [add_comm ((3 * a - b) ^ 2) (a ^ 2), hveq]; ring)
    rcases hIH with h11 | ⟨k, hk1, hcase⟩
    · -- `b' = 1`, `a = 1`, so `b = 2 = F_3`
      obtain ⟨hb'1, ha1⟩ := h11
      have hb2 : b = 2 := by omega
      right
      refine ⟨1, le_rfl, Or.inl ⟨ha1, ?_⟩⟩
      show b = Nat.fib (2 * 1 + 1)
      rw [hb2]
      decide
    · rcases hcase with ⟨hb'e, hae⟩ | ⟨hb'e, hae⟩
      · -- `b' = F_{2k-1}`, `a = F_{2k+1}`: then `b = 3a - b' = F_{2k+3}`
        have hfb := fib_add_four (2 * k - 1)
        rw [show 2 * k - 1 + 4 = 2 * k + 3 by omega,
          show 2 * k - 1 + 2 = 2 * k + 1 by omega] at hfb
        have hb_eq : b = Nat.fib (2 * k + 3) := by omega
        right
        refine ⟨k + 1, by omega, Or.inl ⟨?_, ?_⟩⟩
        · rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega]
          exact hae
        · rw [show 2 * (k + 1) + 1 = 2 * k + 3 by omega]
          exact hb_eq
      · -- `b' = F_{2k+1}`, `a = F_{2k-1}` contradicts `b' ≤ a`
        exfalso
        have h1 : Nat.fib (2 * k + 1) = Nat.fib (2 * k - 1) + Nat.fib (2 * k) := by
          have h2 := @Nat.fib_add_two (2 * k - 1)
          rwa [show 2 * k - 1 + 2 = 2 * k + 1 by omega,
            show 2 * k - 1 + 1 = 2 * k by omega] at h2
        have hpos : 0 < Nat.fib (2 * k) := Nat.fib_pos.mpr (by omega)
        omega

/-- The solutions of `a^2 + b^2 + 1 = 3 * a * b` in positive integers are exactly
the pairs `{F_{2k-1}, F_{2k+1}}` (and `(1, 1)`). -/
lemma fib_pair {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (h : a ^ 2 + b ^ 2 + 1 = 3 * a * b) : FibPair a b := by
  have key : ∀ s : ℕ, ∀ a b : ℕ, a + b = s → 0 < a → 0 < b →
      a ^ 2 + b ^ 2 + 1 = 3 * a * b → FibPair a b := by
    intro s
    induction s using Nat.strong_induction_on with
    | _ s IH =>
      intro a b hsum ha hb h
      rcases le_or_gt a b with hle | hlt
      · exact fib_pair_aux IH ha hb hsum hle h
      · have h' : b ^ 2 + a ^ 2 + 1 = 3 * b * a := by
          rw [add_comm (b ^ 2) (a ^ 2), h]
          ring
        have h2 := fib_pair_aux IH hb ha (by omega) (le_of_lt hlt) h'
        rcases h2 with h11 | ⟨k, hk1, hcase⟩
        · exact Or.inl ⟨h11.2, h11.1⟩
        · right
          refine ⟨k, hk1, ?_⟩
          rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inr ⟨h2, h1⟩
          · exact Or.inl ⟨h2, h1⟩
  exact key (a + b) a b rfl ha hb h

/-- Every entry of a `FibPair` is a Fibonacci number. -/
lemma fibPair_fib {a b : ℕ} (h : FibPair a b) :
    (∃ m, a = Nat.fib m) ∧ (∃ n, b = Nat.fib n) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨k, _, hcase⟩
  · exact ⟨⟨1, Nat.fib_one.symm⟩, ⟨1, Nat.fib_one.symm⟩⟩
  · rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨⟨2 * k - 1, h1⟩, ⟨2 * k + 1, h2⟩⟩
    · exact ⟨⟨2 * k + 1, h1⟩, ⟨2 * k - 1, h2⟩⟩

/-- Parity helper: a square has the same parity as its root. -/
lemma sq_mod_two (x : ℕ) : x ^ 2 % 2 = x % 2 := by
  rw [pow_two, Nat.mul_mod]
  have hx : x % 2 < 2 := Nat.mod_lt x two_pos
  interval_cases h : x % 2 <;> rfl

/-- Odd squares are `1 mod 4`. -/
lemma sq_mod_four_of_odd {x : ℕ} (hx : x % 2 = 1) : x ^ 2 % 4 = 1 := by
  have hx4 : x % 4 % 2 = 1 := by
    rw [Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 4)]
    exact hx
  have hlt : x % 4 < 4 := Nat.mod_lt x (by decide)
  rw [pow_two, Nat.mul_mod]
  interval_cases h : x % 4
  · simp at hx4
  · rfl
  · simp at hx4
  · rfl

/-- Even squares are `0 mod 4`. -/
lemma sq_mod_four_of_even {x : ℕ} (hx : x % 2 = 0) : x ^ 2 % 4 = 0 := by
  have hx4 : x % 4 % 2 = 0 := by
    rw [Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 4)]
    exact hx
  have hlt : x % 4 < 4 := Nat.mod_lt x (by decide)
  rw [pow_two, Nat.mul_mod]
  interval_cases h : x % 4
  · rfl
  · simp at hx4
  · rfl
  · simp at hx4

snip end

problem usa2026_p6 {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (h : Nat.totient (a * b + 1) ∣ a ^ 2 + b ^ 2 + 1) :
    (∃ m, a = Nat.fib m) ∧ (∃ n, b = Nat.fib n) := by
  by_cases h11 : a = 1 ∧ b = 1
  · obtain ⟨rfl, rfl⟩ := h11
    exact ⟨⟨1, Nat.fib_one.symm⟩, ⟨1, Nat.fib_one.symm⟩⟩
  · -- from now on: `a * b ≥ 2`, so `n := a * b + 1 ≥ 3`
    have hab2 : 2 ≤ a * b := by
      by_contra hcon
      push Not at hcon
      have h1 : 1 * 1 ≤ a * b := Nat.mul_le_mul ha hb
      simp only [mul_one] at h1
      have h2 : a * b = 1 := le_antisymm (Nat.le_of_lt_succ hcon) h1
      exact h11 ⟨Nat.eq_one_of_mul_eq_one_right h2, Nat.eq_one_of_mul_eq_one_left h2⟩
    set n := a * b + 1 with hn
    have hn3 : 3 ≤ n := by omega
    -- `φ(n)` is even, so `a^2 + b^2 + 1` is even, so exactly one of `a, b` is odd
    have hneven : 2 ∣ Nat.totient n := (Nat.totient_even (by omega)).two_dvd
    have hS2 : 2 ∣ a ^ 2 + b ^ 2 + 1 := hneven.trans h
    have hpar : (a % 2 = 1 ∧ b % 2 = 0) ∨ (a % 2 = 0 ∧ b % 2 = 1) := by
      have ha2 := sq_mod_two a
      have hb2 := sq_mod_two b
      have halt : a % 2 < 2 := Nat.mod_lt a two_pos
      have hblt : b % 2 < 2 := Nat.mod_lt b two_pos
      obtain ⟨t, ht⟩ := hS2
      omega
    -- hence `a * b` is even and `n` is odd
    have hnodd : n % 2 = 1 := by
      rcases hpar with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have h3 : (a * b) % 2 = 0 := by rw [Nat.mul_mod, h2]; simp
        omega
      · have h3 : (a * b) % 2 = 0 := by rw [Nat.mul_mod, h1]; simp
        omega
    -- `a^2 + b^2 + 1 ≡ 2 (mod 4)`, so `4 ∤ φ(n)`
    have hS4 : ¬ 4 ∣ a ^ 2 + b ^ 2 + 1 := by
      intro h4
      obtain ⟨t, ht⟩ := h4
      rcases hpar with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have ha4 := sq_mod_four_of_odd h1
        have hb4 := sq_mod_four_of_even h2
        omega
      · have ha4 := sq_mod_four_of_even h1
        have hb4 := sq_mod_four_of_odd h2
        omega
    have hφ4 : ¬ 4 ∣ Nat.totient n := fun h4 => hS4 (h4.trans h)
    -- `n` has at most one prime factor: two distinct (odd) prime factors
    -- would force `4 ∣ φ(n)`
    have hone : ∀ p q : ℕ, p.Prime → q.Prime → p ∣ n → q ∣ n → p = q := by
      intro p q hp hq hpn hqn
      by_contra hne
      have hnp : p ≠ 2 := by
        intro h2
        subst h2
        have hmod : n % 2 = 0 := Nat.mod_eq_zero_of_dvd hpn
        omega
      have hnq : q ≠ 2 := by
        intro h2
        subst h2
        have hmod : n % 2 = 0 := Nat.mod_eq_zero_of_dvd hqn
        omega
      have hpo : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hnp)
      have hqo : q % 2 = 1 := Nat.odd_iff.mp (hq.odd_of_ne_two hnq)
      have hn0 : n ≠ 0 := by omega
      have hfp : 0 < n.factorization p := hp.factorization_pos_of_dvd hn0 hpn
      have hfq : 0 < n.factorization q := hq.factorization_pos_of_dvd hn0 hqn
      have hpf : p ^ n.factorization p ∣ n := Nat.ordProj_dvd n p
      have hqf : q ^ n.factorization q ∣ n := Nat.ordProj_dvd n q
      have hcop : (p ^ n.factorization p).Coprime (q ^ n.factorization q) :=
        ((Nat.coprime_primes hp hq).mpr hne).pow _ _
      have hpq : p ^ n.factorization p * q ^ n.factorization q ∣ n :=
        hcop.mul_dvd_of_dvd_of_dvd hpf hqf
      have hφ := Nat.totient_dvd_of_dvd hpq
      rw [Nat.totient_mul hcop, Nat.totient_prime_pow hp hfp,
        Nat.totient_prime_pow hq hfq] at hφ
      have h2p : 2 ∣ p - 1 := by
        have hmod : (p - 1) % 2 = 0 := by omega
        exact Nat.dvd_of_mod_eq_zero hmod
      have h2q : 2 ∣ q - 1 := by
        have hmod : (q - 1) % 2 = 0 := by omega
        exact Nat.dvd_of_mod_eq_zero hmod
      obtain ⟨u, hu⟩ := h2p
      obtain ⟨v, hv⟩ := h2q
      have h4 : 4 ∣ p ^ (n.factorization p - 1) * (p - 1) *
          (q ^ (n.factorization q - 1) * (q - 1)) :=
        ⟨p ^ (n.factorization p - 1) * u * (q ^ (n.factorization q - 1) * v), by
          rw [hu, hv]; ring⟩
      exact hφ4 (h4.trans hφ)
    -- hence `n` is a prime power
    have hpp : IsPrimePow n := by
      rw [isPrimePow_iff_card_primeFactors_eq_one]
      by_contra hcard
      have hnonempty : n.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr (by omega)
      obtain ⟨p, hpm⟩ := hnonempty
      have hex : ∃ q ∈ n.primeFactors, q ≠ p := by
        by_contra hall
        push Not at hall
        have hsing : n.primeFactors = {p} :=
          Finset.eq_singleton_iff_unique_mem.mpr ⟨hpm, hall⟩
        rw [hsing, Finset.card_singleton] at hcard
        exact hcard rfl
      obtain ⟨q, hqm, hqp⟩ := hex
      have hp' := Nat.mem_primeFactors.mp hpm
      have hq' := Nat.mem_primeFactors.mp hqm
      exact hqp (hone q p hq'.1 hp'.1 hq'.2.1 hp'.2.1)
    obtain ⟨p, e, hp', he, hpe⟩ := (isPrimePow_def n).mp hpp
    have hp : p.Prime := Nat.prime_iff.mpr hp'
    rcases lt_or_ge e 2 with he2 | he2
    · -- the case `e = 1`: then `φ(n) = p - 1 = a * b ∣ a^2 + b^2 + 1`
      have he1 : e = 1 := by omega
      subst he1
      rw [pow_one] at hpe
      have hφ : Nat.totient n = a * b := by
        rw [← hpe, Nat.totient_prime hp]
        omega
      rw [hφ] at h
      have hq3 := quotient_eq_three ha hb h
      have h3 : a ^ 2 + b ^ 2 + 1 = 3 * a * b := by
        have h4 := Nat.div_mul_cancel h
        rw [hq3] at h4
        rw [← h4, mul_assoc]
      exact fibPair_fib (fib_pair ha hb h3)
    · -- the case `e ≥ 2`
      set m := p ^ (e - 1) with hm
      have hφ : m * (p - 1) ∣ a ^ 2 + b ^ 2 + 1 := by
        have h1 : Nat.totient n = m * (p - 1) := by
          rw [← hpe, Nat.totient_prime_pow hp he, hm]
        rwa [h1] at h
      have hmdvd : m ∣ a ^ 2 + b ^ 2 + 1 := (dvd_mul_right m (p - 1)).trans hφ
      have hab : a * b = p ^ e - 1 := by omega
      -- reduce the divisibility modulo `m = p^(e-1)`:
      -- `a^2 + b^2 + 1 ≡ 0` and `a * b ≡ -1`
      have hS_z : (a : ZMod m) ^ 2 + (b : ZMod m) ^ 2 + 1 = 0 := by
        have h1 : ((a ^ 2 + b ^ 2 + 1 : ℕ) : ZMod m) = 0 :=
          (ZMod.natCast_eq_zero_iff _ m).mpr hmdvd
        rw [Nat.cast_add, Nat.cast_add, Nat.cast_pow, Nat.cast_pow, Nat.cast_one] at h1
        exact h1
      have hpe_z : (p : ZMod m) ^ e = 0 := by
        have h1 : p ^ e = m * p := by
          conv_lhs => rw [show e = e - 1 + 1 by omega, pow_succ, ← hm]
        have h2 : ((p ^ e : ℕ) : ZMod m) = 0 := by
          rw [h1, Nat.cast_mul, ZMod.natCast_self, zero_mul]
        rw [← Nat.cast_pow]
        exact h2
      have hab_z : (a : ZMod m) * (b : ZMod m) = -1 := by
        have h1 : ((a * b : ℕ) : ZMod m) = ((p ^ e - 1 : ℕ) : ZMod m) := by rw [hab]
        rw [Nat.cast_mul] at h1
        rw [h1, Nat.cast_sub (Nat.one_le_pow e p hp.pos), Nat.cast_pow, hpe_z, Nat.cast_one,
          zero_sub]
      -- so `a^4 + a^2 + 1 ≡ 0`, i.e. `m ∣ (a^2 + a + 1)(a^2 - a + 1)`
      have h4_z : (a : ZMod m) ^ 4 + (a : ZMod m) ^ 2 + 1 = 0 := by
        linear_combination
          (a : ZMod m) ^ 2 * hS_z - ((a : ZMod m) * (b : ZMod m) - 1) * hab_z
      have hfac_z : ((a : ZMod m) ^ 2 + a + 1) * ((a : ZMod m) ^ 2 - a + 1) = 0 := by
        have h1 : ((a : ZMod m) ^ 2 + a + 1) * ((a : ZMod m) ^ 2 - a + 1) =
            (a : ZMod m) ^ 4 + (a : ZMod m) ^ 2 + 1 := by ring
        rw [h1, h4_z]
      set u := a ^ 2 + a + 1 with hu
      set v := a ^ 2 + 1 - a with hv
      have hle_a : a ≤ a ^ 2 + 1 := by
        have h1 : a ≤ a * a := Nat.le_mul_of_pos_right a ha
        rw [pow_two a]
        omega
      have huv_z : ((u * v : ℕ) : ZMod m) = 0 := by
        have hu_z : ((u : ℕ) : ZMod m) = (a : ZMod m) ^ 2 + a + 1 := by
          rw [hu, Nat.cast_add, Nat.cast_add, Nat.cast_pow, Nat.cast_one]
        have hv_z : ((v : ℕ) : ZMod m) = (a : ZMod m) ^ 2 - a + 1 := by
          rw [hv, Nat.cast_sub hle_a, Nat.cast_add, Nat.cast_pow, Nat.cast_one]
          ring
        rw [Nat.cast_mul, hu_z, hv_z]
        exact hfac_z
      have hmuv : m ∣ u * v := (ZMod.natCast_eq_zero_iff _ m).mp huv_z
      -- the two factors `u, v` are coprime
      have hcop : u.Coprime v := by
        apply Nat.coprime_of_dvd
        intro r hr hru hrv
        have hruv : r ∣ u - v := Nat.dvd_sub hru hrv
        have huv2 : u - v = 2 * a := by
          rw [hu, hv]
          omega
        rw [huv2] at hruv
        rcases hr.dvd_mul.mp hruv with h2 | hra
        · rcases (Nat.dvd_prime Nat.prime_two).mp h2 with hr1 | hr2
          · exact hr.ne_one hr1
          · subst hr2
            have hodd : u % 2 = 1 := by
              rw [hu]
              have hev : 2 ∣ a * (a + 1) := (Nat.even_mul_succ_self a).two_dvd
              have h1 : a ^ 2 + a = a * (a + 1) := by rw [pow_two a]; ring
              omega
            have h0 : u % 2 = 0 := Nat.mod_eq_zero_of_dvd hru
            omega
        · have hra' : r ∣ a * (a + 1) := dvd_mul_of_dvd_left hra (a + 1)
          have hr1 : r ∣ u - a * (a + 1) := Nat.dvd_sub hru hra'
          have h1 : u - a * (a + 1) = 1 := by
            rw [hu, pow_two a]
            have h2 : a * (a + 1) = a * a + a := by ring
            omega
          rw [h1] at hr1
          exact hr.not_dvd_one hr1
      -- a prime power dividing a product of coprime factors divides one of them
      have hm_uv : m ∣ u ∨ m ∣ v := by
        by_cases hpu : p ∣ u
        · left
          have hpv : ¬ p ∣ v := fun hpv =>
            hp.not_dvd_one (by
              have h1 : p ∣ u.gcd v := Nat.dvd_gcd hpu hpv
              rwa [hcop.gcd_eq_one] at h1)
          have hmv : m.Coprime v := by
            rw [hm, Nat.coprime_pow_left_iff (by omega : 0 < e - 1)]
            exact hp.coprime_iff_not_dvd.mpr hpv
          exact hmv.dvd_of_dvd_mul_right hmuv
        · right
          have hmu : m.Coprime u := by
            rw [hm, Nat.coprime_pow_left_iff (by omega : 0 < e - 1)]
            exact hp.coprime_iff_not_dvd.mpr hpu
          exact hmu.dvd_of_dvd_mul_left hmuv
      have hpm : p ∣ m := hm ▸ dvd_pow_self p (show e - 1 ≠ 0 by omega)
      have hp_uv : p ∣ u ∨ p ∣ v :=
        hm_uv.imp (fun hmid => hpm.trans hmid) (fun hmid => hpm.trans hmid)
      -- a root of `x^2 + x + 1` mod `p` forces `p = 3` or `p ≡ 1 (mod 3)`
      have hp3 : p = 3 ∨ 3 ∣ p - 1 := by
        have : Fact p.Prime := ⟨hp⟩
        have core : ∀ x : ZMod p, x ^ 2 + x + 1 = 0 → p = 3 ∨ 3 ∣ p - 1 := by
          intro x hx
          by_cases hx1 : x = 1
          · left
            subst hx1
            have h3 : (3 : ZMod p) = 0 := by linear_combination hx
            have h4 : ((3 : ℕ) : ZMod p) = 0 := by rw [Nat.cast_ofNat]; exact h3
            have h5 : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp h4
            rcases (Nat.dvd_prime Nat.prime_three).mp h5 with h6 | h6
            · exact absurd h6 hp.one_lt.ne'
            · exact h6
          · right
            have hx0 : x ≠ 0 := by
              intro h0
              rw [h0] at hx
              simp at hx
            have hx3 : x ^ 3 = 1 := by linear_combination (x - 1) * hx
            have hxu3 : (Units.mk0 x hx0 : (ZMod p)ˣ) ^ 3 = 1 := by
              apply Units.ext
              rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
              exact hx3
            have hxu1 : (Units.mk0 x hx0 : (ZMod p)ˣ) ≠ 1 := by
              intro h1
              apply hx1
              have h2 := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) h1
              rw [Units.val_mk0, Units.val_one] at h2
              exact h2
            have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
            have hord : orderOf (Units.mk0 x hx0 : (ZMod p)ˣ) = 3 :=
              orderOf_eq_prime hxu3 hxu1
            have hdvd3 : 3 ∣ Fintype.card (ZMod p)ˣ := hord ▸ orderOf_dvd_card
            rwa [ZMod.card_units p] at hdvd3
        rcases hp_uv with hpu | hpv
        · apply core (a : ZMod p)
          have h1 : ((u : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ p).mpr hpu
          rw [hu, Nat.cast_add, Nat.cast_add, Nat.cast_pow, Nat.cast_one] at h1
          exact h1
        · apply core (-(a : ZMod p))
          have h1 : ((v : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ p).mpr hpv
          rw [hv, Nat.cast_sub hle_a, Nat.cast_add, Nat.cast_pow, Nat.cast_one] at h1
          linear_combination h1
      rcases hp3 with hp3 | hp3
      · -- `p = 3`: since `9 ∤ x^2 ± x + 1`, we get `e = 2` and `a * b = 8`
        subst hp3
        have h9u : ¬ (9 : ℕ) ∣ u := by
          intro h9d
          have h0 : ((u : ℕ) : ZMod 9) = 0 := (ZMod.natCast_eq_zero_iff _ 9).mpr h9d
          rw [hu, Nat.cast_add, Nat.cast_add, Nat.cast_pow, Nat.cast_one] at h0
          exact (by decide : ∀ x : ZMod 9, x ^ 2 + x + 1 ≠ 0) _ h0
        have h9v : ¬ (9 : ℕ) ∣ v := by
          intro h9d
          have h0 : ((v : ℕ) : ZMod 9) = 0 := (ZMod.natCast_eq_zero_iff _ 9).mpr h9d
          rw [hv, Nat.cast_sub hle_a, Nat.cast_add, Nat.cast_pow, Nat.cast_one] at h0
          have h1 : (a : ZMod 9) ^ 2 - a + 1 = 0 := by linear_combination h0
          exact (by decide : ∀ x : ZMod 9, x ^ 2 - x + 1 ≠ 0) _ h1
        have he2' : e ≤ 2 := by
          by_contra hcon
          push Not at hcon
          have h9m : (9 : ℕ) ∣ m := by
            have h1 : (3 : ℕ) ^ 2 ∣ m := by
              rw [hm]
              exact pow_dvd_pow 3 (by omega)
            norm_num at h1
            exact h1
          rcases hm_uv with hmu | hmv
          · exact h9u (h9m.trans hmu)
          · exact h9v (h9m.trans hmv)
        have he2'' : e = 2 := by omega
        have hab8 : a * b = 8 := by
          rw [he2''] at hpe
          norm_num at hpe
          omega
        have ha8 : a ≤ 8 := by
          have h1 : a ≤ a * b := Nat.le_mul_of_pos_right a hb
          omega
        interval_cases a
        · -- `(a, b) = (1, 8)`
          have hb8 : b = 8 := by omega
          subst hb8
          exact ⟨⟨1, Nat.fib_one.symm⟩, ⟨6, by decide⟩⟩
        · -- `(a, b) = (2, 4)`: `φ(9) = 6 ∤ 21`
          have hb4 : b = 4 := by omega
          subst hb4
          rw [hn] at h
          exact absurd h (by decide)
        · omega
        · -- `(a, b) = (4, 2)`: `φ(9) = 6 ∤ 21`
          have hb2 : b = 2 := by omega
          subst hb2
          rw [hn] at h
          exact absurd h (by decide)
        · omega
        · omega
        · omega
        · -- `(a, b) = (8, 1)`
          have hb1 : b = 1 := by omega
          subst hb1
          exact ⟨⟨6, by decide⟩, ⟨1, Nat.fib_one.symm⟩⟩
      · -- `3 ∣ p - 1`: then `3 ∣ φ(n) ∣ a^2 + b^2 + 1`, so `3 ∤ a` and `3 ∤ b`,
        -- but `3 ∣ p^e - 1 = a * b`, contradiction
        have h3S : 3 ∣ a ^ 2 + b ^ 2 + 1 := by
          have h1 : 3 ∣ m * (p - 1) := dvd_mul_of_dvd_right hp3 m
          exact h1.trans hφ
        have hS3 : ((a ^ 2 + b ^ 2 + 1 : ℕ) : ZMod 3) = 0 :=
          (ZMod.natCast_eq_zero_iff _ 3).mpr h3S
        rw [Nat.cast_add, Nat.cast_add, Nat.cast_pow, Nat.cast_pow, Nat.cast_one] at hS3
        have hsq : (a : ZMod 3) ≠ 0 ∧ (b : ZMod 3) ≠ 0 := by
          have h2 : ∀ x y : ZMod 3, x ^ 2 + y ^ 2 + 1 = 0 → x ≠ 0 ∧ y ≠ 0 := by decide
          exact h2 _ _ hS3
        have h3a : ¬ 3 ∣ a := by
          intro h3d
          exact hsq.1 ((ZMod.natCast_eq_zero_iff _ 3).mpr h3d)
        have h3b : ¬ 3 ∣ b := by
          intro h3d
          exact hsq.2 ((ZMod.natCast_eq_zero_iff _ 3).mpr h3d)
        have h3ab : 3 ∣ a * b := by
          have hp1 : ((p - 1 : ℕ) : ZMod 3) = 0 := (ZMod.natCast_eq_zero_iff _ 3).mpr hp3
          rw [Nat.cast_sub hp.one_le, Nat.cast_one] at hp1
          have hpz : (p : ZMod 3) = 1 := by linear_combination hp1
          have h1 : ((p ^ e - 1 : ℕ) : ZMod 3) = 0 := by
            rw [Nat.cast_sub (Nat.one_le_pow e p hp.pos), Nat.cast_pow, hpz, one_pow,
              Nat.cast_one, sub_self]
          rw [← hab] at h1
          exact (ZMod.natCast_eq_zero_iff _ 3).mp h1
        rcases (Nat.prime_three.dvd_mul).mp h3ab with h3d | h3d
        · exact absurd h3d h3a
        · exact absurd h3d h3b

end Usa2026P6
