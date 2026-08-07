/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karl Mehltretter, Kimi K3
-/

module

public import Mathlib.Tactic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Algebra] }

/-!
# USA Mathematical Olympiad 1984, Problem 5

P(x) is a polynomial of degree 3n such that

  P(0) = P(3) = ... = P(3n) = 2,
  P(1) = P(4) = ... = P(3n - 2) = 1,
  P(2) = P(5) = ... = P(3n - 1) = 0,
  and P(3n + 1) = 730.

Determine n.
-/

namespace Usa1984P5

open Polynomial

determine solution_value : ℕ := 4

snip begin

/- Proof sketch: since deg P = 3n < 3n + 1, the (3n+1)-th forward finite
difference of P at 0 vanishes, which gives a linear relation between
P(3n+1) = 730 and the values 2, 1, 0 at 0, ..., 3n.  Writing the periodic
values via a primitive cube root of unity ζ as
P(j) = 1 + (1-ζ)/3 · ζ^j + (1-ζ²)/3 · ζ^{2j} and using the binomial theorem,
the relation reduces to (-1)^(3n+1) · W = -2187 with
W = (1-ζ)^(3n+2) + (1-ζ²)^(3n+2).  Since (1-ζ)³ = 3(ζ²-ζ) and (ζ²-ζ)² = -3,
for n = 2s we get W = 3·(-27)^s, forcing 27^s = 729 = 27², so s = 2 and n = 4;
for n = 2s+1 we get W = (-27)^(s+1), forcing 27^(s+1) = 2187, impossible since
27² = 729 < 2187 < 19683 = 27³. -/

/-- The forward difference operator on real sequences. -/
def fwdDiff (f : ℕ → ℝ) : ℕ → ℝ := fun n ↦ f (n + 1) - f n

/-- The `m`-fold forward difference at `0` is the alternating binomial sum. -/
lemma fwdDiff_iter_zero (m : ℕ) (f : ℕ → ℝ) :
    fwdDiff^[m] f 0 = ∑ j ∈ Finset.range (m + 1), (-1 : ℝ) ^ (m - j) * (m.choose j : ℝ) * f j := by
  induction m generalizing f with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply, ih (fwdDiff f)]
    have step : ∀ j ∈ Finset.range (m + 1),
        (-1 : ℝ) ^ (m - j) * (m.choose j : ℝ) * fwdDiff f j
          = (-1 : ℝ) ^ (m - j) * (m.choose j : ℝ) * f (j + 1)
            - (-1 : ℝ) ^ (m - j) * (m.choose j : ℝ) * f j := by
      intro j _
      show (-1 : ℝ) ^ (m - j) * (m.choose j : ℝ) * (f (j + 1) - f j) = _
      ring
    rw [Finset.sum_congr rfl step, Finset.sum_sub_distrib]
    have rhs_eq : ∑ j ∈ Finset.range (m + 2),
        (-1 : ℝ) ^ (m + 1 - j) * ((m + 1).choose j : ℝ) * f j
        = (∑ j ∈ Finset.range (m + 1),
            (-1 : ℝ) ^ (m + 1 - (j + 1)) * ((m + 1).choose (j + 1) : ℝ) * f (j + 1))
          + (-1 : ℝ) ^ (m + 1) * f 0 := by
      simp only [Finset.sum_range_succ']
      rw [show (-1 : ℝ) ^ (m + 1 - 0) * ((m + 1).choose 0 : ℝ) * f 0
          = (-1 : ℝ) ^ (m + 1) * f 0 from by simp]
    rw [rhs_eq]
    have key : ∀ j ∈ Finset.range (m + 1),
        (-1 : ℝ) ^ (m + 1 - (j + 1)) * ((m + 1).choose (j + 1) : ℝ) * f (j + 1)
          = (-1 : ℝ) ^ (m - j) * (m.choose j : ℝ) * f (j + 1)
            + (-1 : ℝ) ^ (m - j) * (m.choose (j + 1) : ℝ) * f (j + 1) := by
      intro j hj
      rw [Finset.mem_range] at hj
      rw [Nat.choose_succ_succ]
      have e : m + 1 - (j + 1) = m - j := by omega
      rw [e]
      push_cast
      ring
    rw [Finset.sum_congr rfl key, Finset.sum_add_distrib]
    have reindex : ∑ j ∈ Finset.range (m + 1),
        (-1 : ℝ) ^ (m - j) * (m.choose (j + 1) : ℝ) * f (j + 1)
        = ∑ i ∈ Finset.range (m + 1), (-1 : ℝ) ^ (m + 1 - i) * (m.choose i : ℝ) * f i
          - (-1 : ℝ) ^ (m + 1) * f 0 := by
      have g_def : ∀ j ∈ Finset.range (m + 1),
          (-1 : ℝ) ^ (m - j) * (m.choose (j + 1) : ℝ) * f (j + 1)
            = (fun i ↦ (-1 : ℝ) ^ (m + 1 - i) * (m.choose i : ℝ) * f i) (j + 1) := by
        intro j _
        show (-1 : ℝ) ^ (m - j) * (m.choose (j + 1) : ℝ) * f (j + 1)
          = (-1 : ℝ) ^ (m + 1 - (j + 1)) * (m.choose (j + 1) : ℝ) * f (j + 1)
        rw [show m + 1 - (j + 1) = m - j from by omega]
      have hge := Finset.sum_congr rfl g_def
      rw [hge]
      have h1 := Finset.sum_range_succ'
        (fun i ↦ (-1 : ℝ) ^ (m + 1 - i) * (m.choose i : ℝ) * f i) (m + 1)
      have h2 := Finset.sum_range_succ
        (fun i ↦ (-1 : ℝ) ^ (m + 1 - i) * (m.choose i : ℝ) * f i) (m + 1)
      have hgm : (fun i ↦ (-1 : ℝ) ^ (m + 1 - i) * (m.choose i : ℝ) * f i) (m + 1) = 0 := by
        simp [Nat.choose_succ_self]
      have hg0 : (fun i ↦ (-1 : ℝ) ^ (m + 1 - i) * (m.choose i : ℝ) * f i) 0
          = (-1 : ℝ) ^ (m + 1) * f 0 := by
        simp
      linear_combination -h1 + h2 - hg0 + hgm
    rw [reindex]
    have gneg : ∀ i ∈ Finset.range (m + 1),
        (-1 : ℝ) ^ (m + 1 - i) * (m.choose i : ℝ) * f i
          = -((-1 : ℝ) ^ (m - i) * (m.choose i : ℝ) * f i) := by
      intro i hi
      rw [Finset.mem_range] at hi
      rw [show m + 1 - i = (m - i) + 1 from by omega, pow_succ]
      ring
    rw [Finset.sum_congr rfl gneg, Finset.sum_neg_distrib]
    ring

/-- The `m`-fold forward difference of a polynomial of degree `< m` vanishes. -/
lemma poly_fwdDiff (m : ℕ) (P : ℝ[X]) (hP : P.natDegree < m) (k : ℕ) :
    fwdDiff^[m] (fun j ↦ P.eval (j : ℝ)) k = 0 := by
  induction m generalizing P with
  | zero => simp at hP
  | succ m ih =>
    have hz : ∀ t : ℕ, fwdDiff^[t] (fun _ : ℕ ↦ (0 : ℝ)) k = 0 := by
      intro t
      induction t with
      | zero => rfl
      | succ t iht =>
        rw [Function.iterate_succ_apply,
          show fwdDiff (fun _ : ℕ ↦ (0 : ℝ)) = (fun _ : ℕ ↦ (0 : ℝ)) from by
            ext j; simp [fwdDiff]]
        exact iht
    by_cases hP0 : P = 0
    · subst hP0
      rw [show (fun (j : ℕ) ↦ (0 : ℝ[X]).eval (j : ℝ)) = (fun _ : ℕ ↦ (0 : ℝ)) from by ext j; simp]
      exact hz (m + 1)
    · by_cases hdeg0 : P.natDegree = 0
      · have hPc : P = C (P.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hdeg0
        rw [show (fun (j : ℕ) ↦ P.eval (j : ℝ)) = (fun _ : ℕ ↦ P.coeff 0) from by
          ext j
          rw [hPc]
          simp]
        rw [Function.iterate_succ_apply,
          show fwdDiff (fun _ : ℕ ↦ P.coeff 0) = (fun _ : ℕ ↦ (0 : ℝ)) from by
            ext j; simp [fwdDiff]]
        exact hz m
      · have hPm : P.natDegree ≤ m := by omega
        have hP1 : 1 ≤ P.natDegree := by omega
        have hm : 1 ≤ m := by omega
        have hcomp_deg : (P.comp (X + C 1)).natDegree = P.natDegree := by
          rw [Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C, mul_one]
        have hcomp_ne : P.comp (X + C 1) ≠ 0 := by
          intro hzero
          rw [hzero, Polynomial.natDegree_zero] at hcomp_deg
          omega
        have hcomp_lc : (P.comp (X + C 1)).leadingCoeff = P.leadingCoeff := by
          have hnd : (X + C (1 : ℝ)).natDegree ≠ 0 := by
            rw [Polynomial.natDegree_X_add_C]; norm_num
          rw [Polynomial.leadingCoeff_comp hnd,
            (Polynomial.monic_X_add_C (1 : ℝ)).leadingCoeff]
          simp
        have hdeg_lt : (P.comp (X + C 1) - P).degree < P.degree := by
          have hd : (P.comp (X + C 1)).degree = P.degree := by
            rw [Polynomial.degree_eq_natDegree hcomp_ne, Polynomial.degree_eq_natDegree hP0,
              hcomp_deg]
          have hlt := Polynomial.degree_sub_lt hd hcomp_ne hcomp_lc
          rwa [hd] at hlt
        have hQ : (P.comp (X + C 1) - P).natDegree < m := by
          rcases eq_or_ne (P.comp (X + C 1) - P) 0 with hz0 | hnz
          · rw [hz0, Polynomial.natDegree_zero]; omega
          · have h2 := (Polynomial.natDegree_lt_natDegree_iff hnz).mpr hdeg_lt
            omega
        rw [Function.iterate_succ_apply,
          show fwdDiff (fun (j : ℕ) ↦ P.eval (j : ℝ))
              = (fun (j : ℕ) ↦ (P.comp (X + C 1) - P).eval (j : ℝ)) from by
            ext j
            show P.eval ((j + 1 : ℕ) : ℝ) - P.eval (j : ℝ) = (P.comp (X + C 1) - P).eval (j : ℝ)
            rw [Polynomial.eval_sub, Polynomial.eval_comp]
            have e1 : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
            have e2 : (X + C (1 : ℝ)).eval (j : ℝ) = (j : ℝ) + 1 := by simp
            rw [e1, e2]]
        exact ih _ hQ

snip end

problem usa1984_p5 (n : ℕ) (hn : 0 < n) (P : ℝ[X])
    (hdeg : P.natDegree = 3 * n)
    (h0 : ∀ k ∈ Finset.range (n + 1), P.eval (((3 * k : ℕ) : ℝ)) = 2)
    (h1 : ∀ k ∈ Finset.range n, P.eval (((3 * k + 1 : ℕ) : ℝ)) = 1)
    (h2 : ∀ k ∈ Finset.range n, P.eval (((3 * k + 2 : ℕ) : ℝ)) = 0)
    (h730 : P.eval (((3 * n + 1 : ℕ) : ℝ)) = 730) :
    n = solution_value := by
  -- a primitive cube root of unity
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ 3 := ⟨_, Complex.isPrimitiveRoot_exp 3 (by norm_num)⟩
  have h3 : ζ ^ 3 = 1 := hζ.pow_eq_one
  have hgs : ∑ i ∈ Finset.range 3, ζ ^ i = 0 := hζ.geom_sum_eq_zero (by norm_num)
  have hsum : 1 + ζ + ζ ^ 2 = 0 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero] at hgs
    simp only [pow_zero, pow_one, zero_add] at hgs
    linear_combination hgs
  -- algebraic identities in ζ
  have h2a : (1 - ζ) ^ 2 = -3 * ζ := by linear_combination hsum
  have h2b : (1 - ζ ^ 2) ^ 2 = -3 * ζ ^ 2 := by linear_combination hsum + ζ * h3
  have hr2 : (ζ ^ 2 - ζ) ^ 2 = -3 := by linear_combination hsum + (ζ - 2) * h3
  have h3a : (1 - ζ) ^ 3 = 3 * (ζ ^ 2 - ζ) := by linear_combination -h3
  have h3b : (1 - ζ ^ 2) ^ 3 = -3 * (ζ ^ 2 - ζ) := by linear_combination (3 * ζ - 1 - ζ ^ 3) * h3
  have h9 : (3 * (ζ ^ 2 - ζ)) ^ 2 = -27 := by linear_combination 9 * hr2
  have h9' : (-3 * (ζ ^ 2 - ζ)) ^ 2 = -27 := by linear_combination 9 * hr2
  have h5a : (1 - ζ) ^ 5 = 9 * ζ ^ 2 - 9 := by
    have e : (1 - ζ) ^ 5 = (1 - ζ) ^ 3 * (1 - ζ) ^ 2 := by ring
    rw [e, h3a, h2a]
    linear_combination (-9) * h3
  have h5b : (1 - ζ ^ 2) ^ 5 = 9 * ζ - 9 := by
    have e : (1 - ζ ^ 2) ^ 5 = (1 - ζ ^ 2) ^ 3 * (1 - ζ ^ 2) ^ 2 := by ring
    rw [e, h3b, h2b]
    linear_combination (9 * ζ - 9) * h3
  have h2sum : (1 - ζ) ^ 2 + (1 - ζ ^ 2) ^ 2 = 3 := by linear_combination -hsum + ζ * h3
  have h5sum : (1 - ζ) ^ 5 + (1 - ζ ^ 2) ^ 5 = -27 := by
    rw [h5a, h5b]
    linear_combination 9 * hsum
  have hcross : (1 - ζ) / 3 * ζ + (1 - ζ ^ 2) / 3 * ζ ^ 2 = 0 := by
    linear_combination (-ζ / 3) * h3
  -- Step 1: the (3n+1)-th finite difference vanishes
  have hfd : ∑ j ∈ Finset.range (3 * n + 1 + 1),
      (-1 : ℝ) ^ (3 * n + 1 - j) * ((3 * n + 1).choose j : ℝ) * P.eval (j : ℝ) = 0 := by
    have h := poly_fwdDiff (3 * n + 1) P (by rw [hdeg]; omega) 0
    rw [fwdDiff_iter_zero] at h
    exact h
  -- peel off the last term (which is P(3n+1) = 730)
  have hsumℝ : ∑ j ∈ Finset.range (3 * n + 1),
      (-1 : ℝ) ^ (3 * n + 1 - j) * ((3 * n + 1).choose j : ℝ) * P.eval (j : ℝ) = -730 := by
    rw [Finset.sum_range_succ] at hfd
    simp only [Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one, one_mul, h730] at hfd
    linarith
  -- transport the relation to ℂ
  have hsumℂ : ∑ j ∈ Finset.range (3 * n + 1),
      (-1 : ℂ) ^ (3 * n + 1 - j) * ((3 * n + 1).choose j : ℂ) * (↑(P.eval (j : ℝ)) : ℂ)
        = -730 := by
    have h := congrArg Complex.ofReal hsumℝ
    push_cast at h
    exact h
  -- the periodic values in terms of ζ
  have hpt : ∀ j ∈ Finset.range (3 * n + 1),
      (↑(P.eval (j : ℝ)) : ℂ) = 1 + (1 - ζ) / 3 * ζ ^ j + (1 - ζ ^ 2) / 3 * ζ ^ (2 * j) := by
    intro j hj
    rw [Finset.mem_range] at hj
    set k := j / 3 with hk
    have hjk : j = 3 * k + j % 3 := by omega
    have hmod : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
    rcases hmod with h | h | h
    · have hjk0 : j = 3 * k := by omega
      have hk2 : k ∈ Finset.range (n + 1) := by rw [Finset.mem_range]; omega
      have hvc : (↑(P.eval (j : ℝ)) : ℂ) = 2 := by
        rw [show (j : ℝ) = ((3 * k : ℕ) : ℝ) from by rw [hjk0], h0 k hk2]
        simp
      have hzj : ζ ^ j = 1 := by rw [hjk0, pow_mul, h3, one_pow]
      have hz2j : ζ ^ (2 * j) = 1 := by
        rw [hjk0, show 2 * (3 * k) = 3 * (2 * k) from by ring, pow_mul, h3, one_pow]
      rw [hvc, hzj, hz2j]
      linear_combination (1 / 3) * hsum
    · have hjk1 : j = 3 * k + 1 := by omega
      have hk2 : k ∈ Finset.range n := by rw [Finset.mem_range]; omega
      have hvc : (↑(P.eval (j : ℝ)) : ℂ) = 1 := by
        rw [show (j : ℝ) = ((3 * k + 1 : ℕ) : ℝ) from by rw [hjk1], h1 k hk2]
        simp
      have hzj : ζ ^ j = ζ := by
        rw [hjk1, pow_add, pow_mul, h3, one_pow, one_mul, pow_one]
      have hz2j : ζ ^ (2 * j) = ζ ^ 2 := by
        rw [hjk1, show 2 * (3 * k + 1) = 3 * (2 * k) + 2 from by ring, pow_add, pow_mul, h3,
          one_pow, one_mul]
      rw [hvc, hzj, hz2j]
      linear_combination (ζ / 3) * h3
    · have hjk2 : j = 3 * k + 2 := by omega
      have hk2 : k ∈ Finset.range n := by rw [Finset.mem_range]; omega
      have hvc : (↑(P.eval (j : ℝ)) : ℂ) = 0 := by
        rw [show (j : ℝ) = ((3 * k + 2 : ℕ) : ℝ) from by rw [hjk2], h2 k hk2]
        simp
      have hzj : ζ ^ j = ζ ^ 2 := by
        rw [hjk2, pow_add, pow_mul, h3, one_pow, one_mul]
      have hz2j : ζ ^ (2 * j) = ζ := by
        rw [hjk2, show 2 * (3 * k + 2) = 3 * (2 * k + 1) + 1 from by ring, pow_add, pow_mul, h3,
          one_pow, one_mul, pow_one]
      rw [hvc, hzj, hz2j]
      linear_combination (-(1 / 3)) * hsum + (2 / 3) * h3
  -- sign bookkeeping
  have hsign : ∀ j ∈ Finset.range (3 * n + 1),
      (-1 : ℂ) ^ (3 * n + 1 - j) = (-1 : ℂ) ^ (3 * n + 1) * (-1) ^ j := by
    intro j hj
    rw [Finset.mem_range] at hj
    have h2j : (-1 : ℂ) ^ (2 * j) = 1 := by
      rw [pow_mul, show ((-1 : ℂ) ^ 2) = 1 from by norm_num, one_pow]
    calc (-1 : ℂ) ^ (3 * n + 1 - j) = (-1 : ℂ) ^ (3 * n + 1 - j) * (-1) ^ (2 * j) := by
            rw [h2j, mul_one]
      _ = (-1 : ℂ) ^ (3 * n + 1 - j + 2 * j) := by rw [← pow_add]
      _ = (-1 : ℂ) ^ (3 * n + 1 + j) := by
            rw [show 3 * n + 1 - j + 2 * j = 3 * n + 1 + j from by omega]
      _ = (-1 : ℂ) ^ (3 * n + 1) * (-1) ^ j := by rw [pow_add]
  -- truncated binomial sums
  have hS : ∀ x : ℂ, ∑ j ∈ Finset.range (3 * n + 1), ((3 * n + 1).choose j : ℂ) * x ^ j
      = (x + 1) ^ (3 * n + 1) - x ^ (3 * n + 1) := by
    intro x
    have h : (x + 1) ^ (3 * n + 1)
        = ∑ i ∈ Finset.range (3 * n + 1 + 1),
          x ^ i * 1 ^ (3 * n + 1 - i) * ((3 * n + 1).choose i : ℂ) := add_pow x 1 _
    rw [Finset.sum_range_succ, Nat.choose_self] at h
    simp only [one_pow, mul_one, Nat.cast_one] at h
    rw [Finset.sum_congr rfl (fun i _ ↦ mul_comm _ _)]
    linear_combination -h
  have hS0 : ∑ j ∈ Finset.range (3 * n + 1), ((3 * n + 1).choose j : ℂ) * (-1) ^ j
      = -(-1 : ℂ) ^ (3 * n + 1) := by
    have h := hS (-1)
    rwa [show (-1 : ℂ) + 1 = 0 from by ring, zero_pow (by omega : 3 * n + 1 ≠ 0), zero_sub] at h
  have hzpow : ζ ^ (3 * n + 1) = ζ := by
    rw [pow_succ, pow_mul, h3, one_pow, one_mul]
  have hzpow2 : (ζ ^ 2) ^ (3 * n + 1) = ζ ^ 2 := by
    rw [← pow_mul, show 2 * (3 * n + 1) = 3 * (2 * n) + 2 from by ring, pow_add, pow_mul, h3,
      one_pow, one_mul]
  have hS1 : ∑ j ∈ Finset.range (3 * n + 1), ((3 * n + 1).choose j : ℂ) * ((-1) * ζ) ^ j
      = (1 - ζ) ^ (3 * n + 1) - (-1 : ℂ) ^ (3 * n + 1) * ζ := by
    have h := hS ((-1) * ζ)
    rw [show (-1 : ℂ) * ζ + 1 = 1 - ζ from by ring, mul_pow, hzpow] at h
    exact h
  have hS2 : ∑ j ∈ Finset.range (3 * n + 1), ((3 * n + 1).choose j : ℂ) * ((-1) * ζ ^ 2) ^ j
      = (1 - ζ ^ 2) ^ (3 * n + 1) - (-1 : ℂ) ^ (3 * n + 1) * ζ ^ 2 := by
    have h := hS ((-1) * ζ ^ 2)
    rw [show (-1 : ℂ) * ζ ^ 2 + 1 = 1 - ζ ^ 2 from by ring, mul_pow, hzpow2] at h
    exact h
  -- substitute the values and split the sum
  have per : ∀ j ∈ Finset.range (3 * n + 1),
      (-1 : ℂ) ^ (3 * n + 1 - j) * ((3 * n + 1).choose j : ℂ) * (↑(P.eval (j : ℝ)) : ℂ)
        = (-1 : ℂ) ^ (3 * n + 1) * (((3 * n + 1).choose j : ℂ) * (-1) ^ j)
          + (-1 : ℂ) ^ (3 * n + 1) * ((1 - ζ) / 3 * (((3 * n + 1).choose j : ℂ) * ((-1) * ζ) ^ j))
          + (-1 : ℂ) ^ (3 * n + 1)
            * ((1 - ζ ^ 2) / 3 * (((3 * n + 1).choose j : ℂ) * ((-1) * ζ ^ 2) ^ j)) := by
    intro j hj
    rw [hpt j hj, hsign j hj]
    simp only [mul_pow, pow_mul]
    ring
  rw [Finset.sum_congr rfl per, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
    hS0, hS1, hS2] at hsumℂ
  have hpow1 : (1 - ζ) / 3 * (1 - ζ) ^ (3 * n + 1) = (1 - ζ) ^ (3 * n + 2) / 3 := by
    rw [show 3 * n + 2 = (3 * n + 1) + 1 from by ring, pow_succ]
    ring
  have hpow2 : (1 - ζ ^ 2) / 3 * (1 - ζ ^ 2) ^ (3 * n + 1) = (1 - ζ ^ 2) ^ (3 * n + 2) / 3 := by
    rw [show 3 * n + 2 = (3 * n + 1) + 1 from by ring, pow_succ]
    ring
  have step1 : (-1 : ℂ) ^ (3 * n + 1)
        * ((1 - ζ) / 3 * ((1 - ζ) ^ (3 * n + 1) - (-1 : ℂ) ^ (3 * n + 1) * ζ))
      = (-1 : ℂ) ^ (3 * n + 1) * ((1 - ζ) ^ (3 * n + 2) / 3)
        - (-1 : ℂ) ^ (3 * n + 1) * ((-1 : ℂ) ^ (3 * n + 1) * ((1 - ζ) / 3 * ζ)) := by
    linear_combination ((-1 : ℂ) ^ (3 * n + 1)) * hpow1
  have step2 : (-1 : ℂ) ^ (3 * n + 1)
        * ((1 - ζ ^ 2) / 3 * ((1 - ζ ^ 2) ^ (3 * n + 1) - (-1 : ℂ) ^ (3 * n + 1) * ζ ^ 2))
      = (-1 : ℂ) ^ (3 * n + 1) * ((1 - ζ ^ 2) ^ (3 * n + 2) / 3)
        - (-1 : ℂ) ^ (3 * n + 1) * ((-1 : ℂ) ^ (3 * n + 1) * ((1 - ζ ^ 2) / 3 * ζ ^ 2)) := by
    linear_combination ((-1 : ℂ) ^ (3 * n + 1)) * hpow2
  rw [step1, step2] at hsumℂ
  have hA2 : (-1 : ℂ) ^ (3 * n + 1) * (-1 : ℂ) ^ (3 * n + 1) = 1 := by
    rw [← mul_pow]; simp
  -- the key equation
  have hW : (-1 : ℂ) ^ (3 * n + 1) * ((1 - ζ) ^ (3 * n + 2) + (1 - ζ ^ 2) ^ (3 * n + 2))
      = -2187 := by
    linear_combination 3 * hsumℂ + (3 * ((-1 : ℂ) ^ (3 * n + 1)) ^ 2) * hcross + 3 * hA2
  -- parity case split
  rcases Nat.even_or_odd n with ⟨s, hs⟩ | ⟨s, hs⟩
  · -- n = s + s even
    subst hs
    have hA : (-1 : ℂ) ^ (3 * (s + s) + 1) = -1 := by
      rw [show 3 * (s + s) + 1 = 2 * (3 * s) + 1 from by ring, pow_add, pow_mul,
        show ((-1 : ℂ) ^ 2) = 1 from by norm_num, one_pow, one_mul, pow_one]
    have e1 : (1 - ζ) ^ (3 * (s + s) + 2) = (-27) ^ s * (1 - ζ) ^ 2 := by
      rw [show 3 * (s + s) + 2 = 3 * (2 * s) + 2 from by ring, pow_add, pow_mul (1 - ζ) 3 (2 * s),
        h3a, pow_mul (3 * (ζ ^ 2 - ζ)) 2 s, h9]
    have e2 : (1 - ζ ^ 2) ^ (3 * (s + s) + 2) = (-27) ^ s * (1 - ζ ^ 2) ^ 2 := by
      rw [show 3 * (s + s) + 2 = 3 * (2 * s) + 2 from by ring, pow_add,
        pow_mul (1 - ζ ^ 2) 3 (2 * s), h3b, pow_mul (-3 * (ζ ^ 2 - ζ)) 2 s, h9']
    rw [e1, e2, hA] at hW
    have hW' : (-27 : ℂ) ^ s * 3 = 2187 := by
      linear_combination -hW + (-(-27 : ℂ) ^ s) * h2sum
    have hC : (-27 : ℂ) ^ s = 729 := by linear_combination hW' / 3
    have hR : (-27 : ℝ) ^ s = 729 := by
      apply Complex.ofReal_injective
      push_cast
      exact hC
    have habs : (27 : ℝ) ^ s = 729 := by
      have h := congrArg (fun x : ℝ ↦ |x|) hR
      simp only [abs_pow, abs_neg] at h
      rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 27)] at h
      rwa [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 729)] at h
    have hs2 : s = 2 := by
      rcases Nat.lt_or_ge s 3 with hlt | hge
      · interval_cases s <;> norm_num at habs
        rfl
      · exfalso
        have h4 : (27 : ℝ) ^ 3 ≤ 27 ^ s := pow_le_pow_right₀ (by norm_num) hge
        norm_num at h4
        linarith
    rw [hs2]
  · -- n = 2s + 1 odd
    subst hs
    have hA : (-1 : ℂ) ^ (3 * (2 * s + 1) + 1) = 1 := by
      rw [show 3 * (2 * s + 1) + 1 = 2 * (3 * s + 2) from by ring, pow_mul,
        show ((-1 : ℂ) ^ 2) = 1 from by norm_num, one_pow]
    have e1 : (1 - ζ) ^ (3 * (2 * s + 1) + 2) = (-27) ^ s * (1 - ζ) ^ 5 := by
      rw [show 3 * (2 * s + 1) + 2 = 3 * (2 * s) + 5 from by ring, pow_add,
        pow_mul (1 - ζ) 3 (2 * s), h3a, pow_mul (3 * (ζ ^ 2 - ζ)) 2 s, h9]
    have e2 : (1 - ζ ^ 2) ^ (3 * (2 * s + 1) + 2) = (-27) ^ s * (1 - ζ ^ 2) ^ 5 := by
      rw [show 3 * (2 * s + 1) + 2 = 3 * (2 * s) + 5 from by ring, pow_add,
        pow_mul (1 - ζ ^ 2) 3 (2 * s), h3b, pow_mul (-3 * (ζ ^ 2 - ζ)) 2 s, h9']
    rw [e1, e2, hA] at hW
    have hC : (-27 : ℂ) ^ (s + 1) = -2187 := by
      linear_combination hW + (-(-27 : ℂ) ^ s) * h5sum
    have hR : (-27 : ℝ) ^ (s + 1) = -2187 := by
      apply Complex.ofReal_injective
      push_cast
      exact hC
    have habs : (27 : ℝ) ^ (s + 1) = 2187 := by
      have h := congrArg (fun x : ℝ ↦ |x|) hR
      simp only [abs_pow, abs_neg] at h
      rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 27)] at h
      rwa [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2187)] at h
    exfalso
    rcases Nat.lt_or_ge s 2 with hlt | hge
    · have h4 : (27 : ℝ) ^ (s + 1) ≤ 27 ^ 2 := pow_le_pow_right₀ (by norm_num) (by omega)
      norm_num at h4
      linarith
    · have h4 : (27 : ℝ) ^ 3 ≤ 27 ^ (s + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      norm_num at h4
      linarith

end Usa1984P5
