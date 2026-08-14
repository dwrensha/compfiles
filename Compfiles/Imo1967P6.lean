/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Data.Int.Star
public import Mathlib.Data.Rat.Star
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Tactic.IntervalCases
public import ProblemExtraction

@[expose] public section

problem_file {
  tags := [.Algebra]
  }

/-!
# International Mathematical Olympiad 1967, Problem 6

In a sports contest, there were m medals awarded on n successive days (n > 1).
On the first day, one medal and 1/7 of the remaining (m − 1) medals were awarded.
On the second day, two medals and 1/7 of the now remaining medals were awarded;
and so on. On the n-th and last day, the remaining n medals were awarded.
How many days did the contest last, and how many medals were awarded altogether?
-/

namespace Imo1967P6

/-- The process described in the problem, from the point of view of the medals
remaining: `r k` is the number of medals left at the start of day `k + 1`
(so `r 0 = m`). On day `k` (for `1 ≤ k ≤ n - 1`), `k` medals and one seventh
of the rest are awarded, which has to be a whole number of medals. On the last
day the remaining `n` medals are awarded, i.e. `r (n - 1) = n`. -/
abbrev MedalsProcess (m n : ℕ) (r : ℕ → ℤ) : Prop :=
    r 0 = ↑m ∧ r (n - 1) = ↑n ∧
      ∀ k, 1 ≤ k → k ≤ n - 1 →
        7 ∣ r (k - 1) - ↑k ∧ r k = r (k - 1) - (↑k + (r (k - 1) - ↑k) / 7)

snip begin

-- Solution formalized from https://prase.cz/kalva/imo/isoln/isoln676.html

/-- The day-`k` rule implies the recurrence `7 * r k = 6 * (r (k - 1) - k)`. -/
theorem rec_eq {r : ℕ → ℤ} {k : ℕ} (h7 : 7 ∣ r (k - 1) - ↑k)
    (hk : r k = r (k - 1) - (↑k + (r (k - 1) - ↑k) / 7)) :
    7 * r k = 6 * (r (k - 1) - ↑k) := by
  obtain ⟨c, hc⟩ := h7
  have hdiv : (r (k - 1) - ↑k) / 7 = c := by lia
  rw [hdiv] at hk
  linarith

/-- Solving the recurrence: after `k` days the number of remaining medals is
`(6/7)^k * (m - 36) + 36 - 6k`. -/
theorem closed_form {m n : ℕ} {r : ℕ → ℤ} (h0 : r 0 = ↑m)
    (hrec : ∀ k, 1 ≤ k → k ≤ n - 1 → 7 * r k = 6 * (r (k - 1) - ↑k)) :
    ∀ k, k ≤ n - 1 → (r k : ℚ) = (6 / 7 : ℚ) ^ k * (↑m - 36) + 36 - 6 * ↑k := by
  intro k
  induction k with
  | zero =>
    intro _
    rw [h0]
    push_cast
    ring
  | succ k ih =>
    intro hk
    have ih' := ih (by lia : k ≤ n - 1)
    have h2z := hrec (k + 1) (by lia) hk
    rw [Nat.add_sub_cancel] at h2z
    have h2q : (7 : ℚ) * (r (k + 1) : ℚ) = 6 * ((r k : ℚ) - (↑k + 1)) := by
      exact_mod_cast h2z
    have h3 : (r (k + 1) : ℚ) = (6 / 7 : ℚ) * ((r k : ℚ) - (↑k + 1)) := by
      linarith
    rw [h3, ih']
    push_cast
    ring

/-- Specializing the closed form at `k = n - 1` (where `r (n - 1) = n`) gives the
key Diophantine relation between `m` and `n`. -/
theorem key_eq {m n : ℕ} (hn : 1 < n) {r : ℕ → ℤ} (h0 : r 0 = ↑m)
    (hn1 : r (n - 1) = ↑n)
    (hrec : ∀ k, 1 ≤ k → k ≤ n - 1 → 7 * r k = 6 * (r (k - 1) - ↑k)) :
    (6 : ℤ) ^ (n - 1) * (↑m - 36) = 7 ^ n * (↑n - 6) := by
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by lia⟩
  have hcf := closed_form h0 hrec N le_rfl
  simp only [Nat.add_sub_cancel] at hn1 ⊢
  rw [hn1] at hcf
  push_cast at hcf
  have h3 : (6 / 7 : ℚ) ^ N * (↑m - 36) = 7 * (↑N - 5) := by linarith
  have e1 : (7 : ℚ) ^ N * (6 / 7) ^ N = 6 ^ N := by
    rw [← mul_pow]
    norm_num
  have h4 : (7 : ℚ) ^ N * ((6 / 7) ^ N * (↑m - 36)) = 7 ^ N * (7 * (↑N - 5)) := by
    rw [h3]
  rw [← mul_assoc, e1] at h4
  have hQ : (6 : ℚ) ^ N * (↑m - 36) = 7 ^ (N + 1) * (↑N - 5) := by
    rw [h4, pow_succ, mul_assoc]
  have hN5z : (↑(N + 1) : ℤ) - 6 = ↑N - 5 := by lia
  rw [hN5z]
  exact_mod_cast hQ

/-- The forward direction: the Diophantine relation forces `n = 6` and `m = 36`,
because `6 ^ (n - 1)` must divide `n - 6` while growing much faster. -/
theorem forward {m n : ℕ} (hn : 1 < n) (h : ∃ r : ℕ → ℤ, MedalsProcess m n r) :
    (m, n) = (36, 6) := by
  obtain ⟨r, h0, hn1, hrec⟩ := h
  have hrec7 : ∀ k, 1 ≤ k → k ≤ n - 1 → 7 * r k = 6 * (r (k - 1) - ↑k) :=
    fun k h1 h2 => rec_eq (hrec k h1 h2).1 (hrec k h1 h2).2
  have hkey := key_eq hn h0 hn1 hrec7
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by lia⟩
  have hN : 1 ≤ N := by lia
  simp only [Nat.add_sub_cancel] at hkey
  have hN5z : (↑(N + 1) : ℤ) - 6 = ↑N - 5 := by lia
  rw [hN5z] at hkey
  -- `6 ^ N` divides `N - 5`, since it is coprime to `7 ^ (N + 1)`.
  have hdvd : (6 : ℤ) ^ N ∣ (↑N - 5) := by
    have h1 : (6 : ℤ) ^ N ∣ 7 ^ (N + 1) * (↑N - 5) := ⟨↑m - 36, hkey.symm⟩
    have hcop : IsCoprime ((6 : ℤ) ^ N) (7 ^ (N + 1)) :=
      IsCoprime.pow (⟨-1, 1, by norm_num⟩ : IsCoprime (6 : ℤ) 7)
    exact hcop.dvd_of_dvd_mul_left h1
  -- but `|N - 5| < 6 ^ N` for `N ≥ 1`, which forces `N = 5`.
  have hbound : |(↑N : ℤ) - 5| < (6 : ℤ) ^ N := by
    rcases lt_or_ge N 5 with h | h
    · interval_cases N <;> norm_num
    · have h2 : (↑N : ℤ) < (6 : ℤ) ^ N := by
        have h3 : N < 6 ^ N := Nat.lt_pow_self (by norm_num)
        exact_mod_cast h3
      rw [abs_of_nonneg (by lia)]
      lia
  have hN5 : (↑N : ℤ) - 5 = 0 := Int.eq_zero_of_abs_lt_dvd hdvd hbound
  have hNeq : N = 5 := by
    have h4 : (↑N : ℤ) = 5 := by linarith
    exact_mod_cast h4
  subst hNeq
  have hm : (↑m : ℤ) = 36 := by
    have e : (↑(5 : ℕ) : ℤ) - 5 = 0 := by lia
    rw [e, mul_zero] at hkey
    rcases mul_eq_zero.mp hkey with h5 | h5
    · norm_num at h5
    · linarith
  have hm' : m = 36 := by exact_mod_cast hm
  subst hm'
  rfl

/-- The converse direction: with `m = 36` and `n = 6` exactly six medals are
awarded on each of the six days. -/
theorem backward : ∃ r : ℕ → ℤ, MedalsProcess 36 6 r := by
  refine ⟨fun k => if k ≤ 5 then 36 - 6 * (k : ℤ) else 0, ?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · intro k h1 h2
    have h2' : k ≤ 5 := h2
    interval_cases k <;> decide

snip end

determine solution : ℕ × ℕ := (36, 6)

problem imo1967_p6 (m n : ℕ) (hn : 1 < n) :
    (∃ r : ℕ → ℤ, MedalsProcess m n r) ↔ (m, n) = solution := by
  constructor
  · intro h
    rw [solution]
    exact forward hn h
  · intro h
    rw [solution, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact backward

end Imo1967P6
