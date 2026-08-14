/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Data.Int.Star
public import Mathlib.Data.Nat.Choose.Factorization
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.NumberTheory] }

/-!
USA Mathematical Olympiad 2016, Problem 2

Prove that for any positive integer k,

  (k²)! · ∏_{j=0}^{k-1} j!/(j + k)!

is an integer.
-/

namespace Usa2016P2

open Finset
open scoped Nat

snip begin

/-- If `F` is periodic with period `q`, then it is also periodic with period `a * q`. -/
lemma period_mul {q : ℕ} {F : ℕ → ℕ} (hF : ∀ j, F (j + q) = F j) (a j : ℕ) :
    F (j + a * q) = F j := by
  induction a with
  | zero => simp
  | succ a ih =>
    have h : j + (a + 1) * q = j + a * q + q := by ring
    rw [h, hF, ih]

/-- The sum of a `q`-periodic function over `range (a * q)` splits into `a` copies of
the full-period sum. -/
lemma sum_range_period_mul {q : ℕ} {F : ℕ → ℕ} (hF : ∀ j, F (j + q) = F j) (a : ℕ) :
    ∑ j ∈ Finset.range (a * q), F j = a * ∑ i ∈ Finset.range q, F i := by
  induction a with
  | zero => simp
  | succ a ih =>
    have h1 : (a + 1) * q = a * q + q := by ring
    rw [h1]
    have hsplit : ∑ j ∈ Finset.range (a * q + q), F j =
        ∑ j ∈ Finset.range (a * q), F j + ∑ i ∈ Finset.range q, F (a * q + i) := by
      rw [Finset.range_eq_Ico,
        ← Finset.sum_Ico_consecutive F (by omega : (0 : ℕ) ≤ a * q)
          (by omega : a * q ≤ a * q + q),
        ← Finset.range_eq_Ico, Finset.sum_Ico_eq_sum_range]
      have h2 : a * q + q - a * q = q := by omega
      rw [h2]
    rw [hsplit, ih]
    have h3 : ∑ i ∈ Finset.range q, F (a * q + i) = ∑ i ∈ Finset.range q, F i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [add_comm (a * q) i, period_mul hF a i]
    rw [h3]
    ring

/-- The sum of a `q`-periodic function over `range (a * q + b)` splits into full periods
plus a remainder sum. -/
lemma sum_range_period {q : ℕ} {F : ℕ → ℕ} (hF : ∀ j, F (j + q) = F j) (a b : ℕ) :
    ∑ j ∈ Finset.range (a * q + b), F j =
      a * (∑ i ∈ Finset.range q, F i) + ∑ i ∈ Finset.range b, F i := by
  have hsplit : ∑ j ∈ Finset.range (a * q + b), F j =
      ∑ j ∈ Finset.range (a * q), F j + ∑ i ∈ Finset.range b, F (a * q + i) := by
    rw [Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive F (by omega : (0 : ℕ) ≤ a * q)
        (by omega : a * q ≤ a * q + b),
      ← Finset.range_eq_Ico, Finset.sum_Ico_eq_sum_range]
    have h2 : a * q + b - a * q = b := by omega
    rw [h2]
  rw [hsplit, sum_range_period_mul hF a]
  have h3 : ∑ i ∈ Finset.range b, F (a * q + i) = ∑ i ∈ Finset.range b, F i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [add_comm (a * q) i, period_mul hF a i]
  rw [h3]

/-- The sum of a `q`-periodic function over one full period is shift invariant. -/
lemma sum_range_period_shift {q : ℕ} {F : ℕ → ℕ} (hF : ∀ j, F (j + q) = F j) (b : ℕ) :
    ∑ i ∈ Finset.range q, F (i + b) = ∑ i ∈ Finset.range q, F i := by
  have step : ∀ {G : ℕ → ℕ}, (∀ j, G (j + q) = G j) →
      ∑ i ∈ Finset.range q, G (i + 1) = ∑ i ∈ Finset.range q, G i := by
    intro G hG
    have h1 := Finset.sum_range_succ' G q
    have h2 := Finset.sum_range_succ G q
    have h3 : G q = G 0 := by simpa using hG 0
    rw [h3] at h2
    omega
  induction b generalizing F with
  | zero => simp
  | succ b ih =>
    have hG : ∀ j, F (j + q + 1) = F (j + 1) := by
      intro j
      rw [Nat.add_right_comm, hF (j + 1)]
    calc ∑ i ∈ Finset.range q, F (i + (b + 1))
        = ∑ i ∈ Finset.range q, (fun j => F (j + 1)) (i + b) := by
          apply Finset.sum_congr rfl
          intro i _
          exact congrArg F (by omega : i + (b + 1) = i + b + 1)
      _ = ∑ i ∈ Finset.range q, F (i + 1) := ih (F := fun j => F (j + 1)) hG
      _ = ∑ i ∈ Finset.range q, F i := step hF

/-- For `b ≤ q` and `m ≤ q`, the sum of `i` over `range b` is at most the sum of
`(i + m) % q`. -/
lemma sum_range_mod_add_ge {q b m : ℕ} (hb : b ≤ q) (hm : m ≤ q) :
    ∑ i ∈ Finset.range b, i ≤ ∑ i ∈ Finset.range b, (i + m) % q := by
  have key : ∀ i : ℕ, i < q → (((i + m) % q : ℕ) : ℤ) =
      (i : ℤ) + (m : ℤ) - (q : ℤ) * (if q ≤ i + m then 1 else 0) := by
    intro i hi
    by_cases h : q ≤ i + m
    · rw [ite_eq_left h]
      have h1 : (i + m) % q = i + m - q := by
        rw [Nat.mod_eq_sub_mod h]
        exact Nat.mod_eq_of_lt (by omega)
      rw [h1, Nat.cast_sub h, Nat.cast_add]
      ring
    · rw [ite_eq_right h]
      have h1 : (i + m) % q = i + m := Nat.mod_eq_of_lt (by omega)
      rw [h1, Nat.cast_add]
      ring
  have hsum : ∑ i ∈ Finset.range b, (((i + m) % q : ℕ) : ℤ) =
      ∑ i ∈ Finset.range b,
        ((i : ℤ) + (m : ℤ) - (q : ℤ) * (if q ≤ i + m then 1 else 0)) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    exact key i (by omega)
  have hℤ : ∑ i ∈ Finset.range b, (i : ℤ) ≤
      ∑ i ∈ Finset.range b, (((i + m) % q : ℕ) : ℤ) := by
    rw [hsum, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [← Finset.mul_sum, Finset.sum_boole]
    by_cases hbm : b + m ≤ q
    · have hempty : (Finset.range b).filter (fun i => q ≤ i + m) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro i hi
        rw [Finset.mem_filter, Finset.mem_range] at hi
        omega
      rw [hempty, Finset.card_empty, Nat.cast_zero, mul_zero, sub_zero]
      have hnonneg : (0 : ℤ) ≤ (b : ℤ) * m := by positivity
      linarith
    · have hfilter : (Finset.range b).filter (fun i => q ≤ i + m) =
          Finset.Ico (q - m) b := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
        constructor
        · rintro ⟨hi, hqi⟩
          exact ⟨by omega, hi⟩
        · rintro ⟨h1, h2⟩
          exact ⟨h2, by omega⟩
      have hle : q - m ≤ b := by omega
      rw [hfilter, Nat.card_Ico, Nat.cast_sub hle, Nat.cast_sub hm]
      have h1 : (0 : ℤ) ≤ (q : ℤ) - b := sub_nonneg.mpr (Nat.cast_le.mpr hb)
      have h2 : (0 : ℤ) ≤ (q : ℤ) - m := sub_nonneg.mpr (Nat.cast_le.mpr hm)
      have h3 : (0 : ℤ) ≤ ((q : ℤ) - b) * ((q : ℤ) - m) := mul_nonneg h1 h2
      have h4 : (b : ℤ) * m - q * ((b : ℤ) - ((q : ℤ) - m)) =
          ((q : ℤ) - b) * ((q : ℤ) - m) := by ring
      linarith
  have hcast : ((∑ i ∈ Finset.range b, i : ℕ) : ℤ) ≤
      ((∑ i ∈ Finset.range b, (i + m) % q : ℕ) : ℤ) := by
    rw [Nat.cast_sum, Nat.cast_sum]
    exact hℤ
  exact Nat.cast_le.mp hcast

/-- The sum of the remainders of `0, 1, …, k-1` modulo `q` is at most the sum of the
remainders of `n, n+1, …, n+k-1` modulo `q`. -/
lemma sum_mod_le_sum_add_mod (k n q : ℕ) (hq : 0 < q) :
    ∑ j ∈ Finset.range k, j % q ≤ ∑ j ∈ Finset.range k, (j + n) % q := by
  have hk : k = k / q * q + k % q := by
    have h := Nat.div_add_mod k q
    rw [mul_comm] at h
    exact h.symm
  have hF1 : ∀ j, (j + q) % q = j % q := fun j => Nat.add_mod_right j q
  have hF2 : ∀ j, (j + q + n) % q = (j + n) % q := by
    intro j
    rw [Nat.add_right_comm, Nat.add_mod_right]
  have hmod_self : ∀ b : ℕ, b ≤ q →
      ∑ i ∈ Finset.range b, i % q = ∑ i ∈ Finset.range b, i := by
    intro b hb
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    exact Nat.mod_eq_of_lt (by omega)
  have hshift : ∑ i ∈ Finset.range q, (i + n) % q = ∑ i ∈ Finset.range q, i := by
    have h1 : ∑ i ∈ Finset.range q, (i + n) % q = ∑ i ∈ Finset.range q, i % q :=
      sum_range_period_shift (F := fun j => j % q) hF1 n
    rw [h1]
    exact hmod_self q le_rfl
  have hrem : ∑ i ∈ Finset.range (k % q), (i + n) % q =
      ∑ i ∈ Finset.range (k % q), (i + n % q) % q := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    have h1 : i % q = i := Nat.mod_eq_of_lt (by have := Nat.mod_lt k hq; omega)
    conv_lhs => rw [Nat.add_mod, h1]
  have LHS : ∑ j ∈ Finset.range k, j % q =
      k / q * (∑ i ∈ Finset.range q, i % q) + ∑ i ∈ Finset.range (k % q), i % q := by
    conv_lhs => rw [hk]
    exact sum_range_period (F := fun j => j % q) hF1 (k / q) (k % q)
  have RHS : ∑ j ∈ Finset.range k, (j + n) % q =
      k / q * (∑ i ∈ Finset.range q, (i + n) % q) +
        ∑ i ∈ Finset.range (k % q), (i + n) % q := by
    conv_lhs => rw [hk]
    exact sum_range_period (F := fun j => (j + n) % q) hF2 (k / q) (k % q)
  calc ∑ j ∈ Finset.range k, j % q
      = k / q * (∑ i ∈ Finset.range q, i % q) + ∑ i ∈ Finset.range (k % q), i % q := LHS
    _ = k / q * (∑ i ∈ Finset.range q, i) + ∑ i ∈ Finset.range (k % q), i := by
        rw [hmod_self q le_rfl, hmod_self (k % q) (Nat.mod_lt k hq).le]
    _ ≤ k / q * (∑ i ∈ Finset.range q, i) + ∑ i ∈ Finset.range (k % q),
          (i + n % q) % q :=
        Nat.add_le_add_left
          (sum_range_mod_add_ge (Nat.mod_lt k hq).le (Nat.mod_lt n hq).le) _
    _ = k / q * (∑ i ∈ Finset.range q, (i + n) % q) +
          ∑ i ∈ Finset.range (k % q), (i + n) % q := by
        rw [← hshift, ← hrem]
    _ = ∑ j ∈ Finset.range k, (j + n) % q := RHS.symm

/-- For each `q > 0`, `∑ j ∈ range k, (j + k) / q ≤ k ^ 2 / q + ∑ j ∈ range k, j / q`.
This is the per-prime-power comparison in Legendre's formula for the problem. -/
lemma sum_add_div_le (k q : ℕ) (hq : 0 < q) :
    ∑ j ∈ Finset.range k, (j + k) / q ≤ k ^ 2 / q + ∑ j ∈ Finset.range k, j / q := by
  -- Cast to `ℤ` and use `q * (n / q) = n - n % q`.
  have hdiv : ∀ n : ℕ, (q : ℤ) * ((n / q : ℕ) : ℤ) = (n : ℤ) - ((n % q : ℕ) : ℤ) := by
    intro n
    have h2 : ((q * (n / q) + n % q : ℕ) : ℤ) = (n : ℤ) := by
      exact_mod_cast Nat.div_add_mod n q
    rw [Nat.cast_add, Nat.cast_mul] at h2
    linarith
  have hC : (∑ j ∈ Finset.range k, ((j % q : ℕ) : ℤ))
      ≤ ∑ j ∈ Finset.range k, (((j + k) % q : ℕ) : ℤ) := by
    have h := Nat.cast_le (α := ℤ).mpr (sum_mod_le_sum_add_mod k k q hq)
    rwa [Nat.cast_sum, Nat.cast_sum] at h
  have hmod : ((k ^ 2 % q : ℕ) : ℤ) ≤ (q : ℤ) - 1 := by
    have hlt : k ^ 2 % q < q := Nat.mod_lt _ hq
    omega
  have hsumk : (∑ j ∈ Finset.range k, (((j + k) : ℕ) : ℤ))
      = (∑ j ∈ Finset.range k, (j : ℤ)) + (k : ℤ) ^ 2 := by
    have hs : (∑ j ∈ Finset.range k, (((j + k) : ℕ) : ℤ))
        = ∑ j ∈ Finset.range k, ((j : ℤ) + (k : ℤ)) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      push_cast
      ring
    rw [hs, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  have key : (q : ℤ) * ((((k ^ 2 / q : ℕ) : ℤ) + ∑ j ∈ Finset.range k, ((j / q : ℕ) : ℤ))
        - ∑ j ∈ Finset.range k, (((j + k) / q : ℕ) : ℤ))
      = (∑ j ∈ Finset.range k, (((j + k) % q : ℕ) : ℤ))
        - (∑ j ∈ Finset.range k, ((j % q : ℕ) : ℤ)) - ((k ^ 2 % q : ℕ) : ℤ) := by
    have e1 : (q : ℤ) * ((((k ^ 2 / q : ℕ) : ℤ) + ∑ j ∈ Finset.range k, ((j / q : ℕ) : ℤ))
          - ∑ j ∈ Finset.range k, (((j + k) / q : ℕ) : ℤ))
        = (q : ℤ) * ((k ^ 2 / q : ℕ) : ℤ)
          + (∑ j ∈ Finset.range k, (q : ℤ) * ((j / q : ℕ) : ℤ))
          - ∑ j ∈ Finset.range k, (q : ℤ) * (((j + k) / q : ℕ) : ℤ) := by
      rw [mul_sub, mul_add, Finset.mul_sum, Finset.mul_sum]
    have e2 : (∑ j ∈ Finset.range k, (q : ℤ) * ((j / q : ℕ) : ℤ))
        = ∑ j ∈ Finset.range k, ((j : ℤ) - ((j % q : ℕ) : ℤ)) :=
      Finset.sum_congr rfl fun j _ => hdiv j
    have e3 : (∑ j ∈ Finset.range k, (q : ℤ) * (((j + k) / q : ℕ) : ℤ))
        = ∑ j ∈ Finset.range k, ((((j + k) : ℕ) : ℤ) - (((j + k) % q : ℕ) : ℤ)) :=
      Finset.sum_congr rfl fun j _ => hdiv (j + k)
    rw [e1, hdiv (k ^ 2), e2, e3, Finset.sum_sub_distrib, Finset.sum_sub_distrib, hsumk,
      Nat.cast_pow]
    ring
  have hBA : (0 : ℤ) ≤ (((k ^ 2 / q : ℕ) : ℤ) + ∑ j ∈ Finset.range k, ((j / q : ℕ) : ℤ))
      - ∑ j ∈ Finset.range k, (((j + k) / q : ℕ) : ℤ) := by
    by_contra hneg
    push Not at hneg
    have hle : (((k ^ 2 / q : ℕ) : ℤ) + ∑ j ∈ Finset.range k, ((j / q : ℕ) : ℤ))
        - ∑ j ∈ Finset.range k, (((j + k) / q : ℕ) : ℤ) ≤ -1 := by omega
    have hq0 : (0 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq.le
    have h3 : (q : ℤ) * ((((k ^ 2 / q : ℕ) : ℤ) + ∑ j ∈ Finset.range k, ((j / q : ℕ) : ℤ))
          - ∑ j ∈ Finset.range k, (((j + k) / q : ℕ) : ℤ)) ≤ -(q : ℤ) := by
      have hmul := mul_le_mul_of_nonneg_left hle hq0
      rwa [mul_neg, mul_one] at hmul
    have h4 : (1 : ℤ) - (q : ℤ) ≤ (q : ℤ) *
        ((((k ^ 2 / q : ℕ) : ℤ) + ∑ j ∈ Finset.range k, ((j / q : ℕ) : ℤ))
          - ∑ j ∈ Finset.range k, (((j + k) / q : ℕ) : ℤ)) := by
      linarith [key, hC, hmod]
    linarith
  rw [← Nat.cast_le (α := ℤ)]
  rw [Nat.cast_sum, Nat.cast_add, Nat.cast_sum]
  omega

snip end

problem usa2016_p2 (k : ℕ) (hk : 0 < k) :
    (∏ j ∈ Finset.range k, (j + k) !) ∣ (k ^ 2) ! * ∏ j ∈ Finset.range k, j ! := by
  -- It suffices to compare the factorizations at every prime.
  have hfact : ∀ n : ℕ, n ! ≠ 0 := Nat.factorial_ne_zero
  have hprod : (∏ j ∈ Finset.range k, j !) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => hfact j
  have hD : (∏ j ∈ Finset.range k, (j + k) !) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => hfact (j + k)
  rw [← Nat.factorization_le_iff_dvd hD (mul_ne_zero (hfact _) hprod), Finsupp.le_def]
  intro p
  by_cases hp : p.Prime
  · -- For a prime `p`, apply Legendre's formula with the uniform bound `B`.
    set B := Nat.log p (k ^ 2) + 1
    have hB : ∀ n : ℕ, n ≤ k ^ 2 →
        (n !).factorization p = ∑ i ∈ Finset.Ico 1 B, n / p ^ i :=
      fun n hn => Nat.factorization_factorial hp (Nat.lt_succ_of_le (Nat.log_mono_right hn))
    have h2k : 2 * k ≤ k ^ 2 + 1 := by
      have h1 : (0 : ℤ) ≤ ((k : ℤ) - 1) ^ 2 := sq_nonneg _
      have h2 : (2 * k : ℤ) ≤ (k : ℤ) ^ 2 + 1 := by nlinarith [h1]
      exact_mod_cast h2
    rw [Nat.factorization_mul (hfact _) hprod,
      Nat.factorization_prod fun j _ => hfact (j + k),
      Nat.factorization_prod fun j _ => hfact j, Finsupp.add_apply]
    have eLHS : (∑ j ∈ Finset.range k, ((j + k) !).factorization) p
        = ∑ j ∈ Finset.range k, ∑ i ∈ Finset.Ico 1 B, (j + k) / p ^ i := by
      rw [Finsupp.finsetSum_apply]
      refine Finset.sum_congr rfl fun j hj => hB (j + k) ?_
      have hjlt : j < k := Finset.mem_range.mp hj
      omega
    have eRHS : (∑ j ∈ Finset.range k, (j !).factorization) p
        = ∑ j ∈ Finset.range k, ∑ i ∈ Finset.Ico 1 B, j / p ^ i := by
      rw [Finsupp.finsetSum_apply]
      refine Finset.sum_congr rfl fun j hj => hB j ?_
      have hjlt : j < k := Finset.mem_range.mp hj
      have hkk : k ≤ k ^ 2 := by
        calc k = k * 1 := (mul_one k).symm
          _ ≤ k * k := Nat.mul_le_mul_left k hk
          _ = k ^ 2 := (pow_two k).symm
      omega
    rw [eLHS, eRHS, hB _ le_rfl, Finset.sum_comm,
      show (∑ j ∈ Finset.range k, ∑ i ∈ Finset.Ico 1 B, j / p ^ i)
        = ∑ i ∈ Finset.Ico 1 B, ∑ j ∈ Finset.range k, j / p ^ i from Finset.sum_comm,
      ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => sum_add_div_le k (p ^ i) (pow_pos hp.pos i)
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp,
      Nat.factorization_eq_zero_of_not_prime _ hp]

end Usa2016P2
