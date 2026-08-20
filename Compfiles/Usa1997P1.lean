/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Data.Int.Star
public import Mathlib.Data.Nat.Nth
public import Mathlib.Data.Nat.PrimeFin
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.NumberTheory] }

/-!
# USA Mathematical Olympiad 1997, Problem 1

Let p₁, p₂, p₃, ... be the prime numbers listed in increasing order, and let x₀
be a real number between 0 and 1. For positive integer k, define

    xₖ = 0,               if xₖ₋₁ = 0,
    xₖ = {pₖ / xₖ₋₁},     if xₖ₋₁ ≠ 0,

where {x} denotes the fractional part of x. (The fractional part of x is given
by x - ⌊x⌋, where ⌊x⌋ is the greatest integer less than or equal to x.)

Find, with proof, all x₀ satisfying 0 < x₀ < 1 for which the sequence
x₀, x₁, x₂, ... eventually becomes 0.
-/

namespace Usa1997P1

/-- The recursion from the problem, parametrized by the sequence `p : ℕ → ℕ`
of positive integers used as numerators, where `p k` is used at step `k + 1`.
The problem instantiates `p` to `Nat.nth Nat.Prime`, the increasing
enumeration of the primes, so that `p k` is the `(k + 1)`-th prime. -/
noncomputable def seq (p : ℕ → ℕ) (x₀ : ℝ) : ℕ → ℝ
  | 0 => x₀
  | k + 1 => if seq p x₀ k = 0 then 0 else Int.fract ((p k : ℝ) / seq p x₀ k)

/-- The answer to the problem: the sequence eventually becomes zero exactly
for the rational numbers in the open interval (0, 1). -/
determine solution_set : Set ℝ := Set.Ioo 0 1 ∩ Set.range ((↑) : ℚ → ℝ)

snip begin

lemma seq_zero (p : ℕ → ℕ) (x₀ : ℝ) : seq p x₀ 0 = x₀ := rfl

lemma seq_succ (p : ℕ → ℕ) (x₀ : ℝ) (k : ℕ) :
    seq p x₀ (k + 1) =
      if seq p x₀ k = 0 then 0 else Int.fract ((p k : ℝ) / seq p x₀ k) := rfl

/-- Shifting the starting value by one step is the same as shifting the
sequence of numerators. -/
lemma seq_shift (p : ℕ → ℕ) (x₀ : ℝ) :
    ∀ k : ℕ, seq (fun n ↦ p (n + 1)) (seq p x₀ 1) k = seq p x₀ (k + 1)
  | 0 => rfl
  | k + 1 => by
    rw [seq_succ (fun n ↦ p (n + 1)) (seq p x₀ 1) k, seq_shift p x₀ k,
      seq_succ p x₀ (k + 1)]

/-- First direction: starting from a positive rational `a / b`, the sequence
reaches zero, because the numerator strictly decreases at each nonzero step.
(The values `p k` only need to be positive integers; primality is irrelevant
for this direction.) -/
lemma terminates_of_rat :
    ∀ a : ℕ, 0 < a → ∀ p : ℕ → ℕ, (∀ k, 0 < p k) →
      ∀ b : ℕ, 0 < b → ∃ k, seq p ((a : ℝ) / b) k = 0 := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    intro ha p hp b hb
    have ha' : (a : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr ha.ne'
    have hb' : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hb.ne'
    have hx : (a : ℝ) / b ≠ 0 := div_ne_zero ha' hb'
    have h1 : seq p ((a : ℝ) / b) 1 = (((p 0 * b) % a : ℕ) : ℝ) / a := by
      rw [seq_succ, seq_zero, ite_eq_right hx]
      have e1 : (p 0 : ℝ) / ((a : ℝ) / b) = (((p 0 * b : ℕ) : ℝ)) / a := by
        rw [Nat.cast_mul]
        field_simp
      rw [e1]
      exact Int.fract_div_natCast_eq_div_natCast_mod
    by_cases hr : (p 0 * b) % a = 0
    · exact ⟨1, by rw [h1, hr]; simp⟩
    · have hrpos : 0 < (p 0 * b) % a := Nat.pos_of_ne_zero hr
      have hrlt : (p 0 * b) % a < a := Nat.mod_lt _ ha
      obtain ⟨k, hk⟩ := ih ((p 0 * b) % a) hrlt hrpos (fun n ↦ p (n + 1))
        (fun n ↦ hp (n + 1)) a ha
      refine ⟨k + 1, ?_⟩
      rw [← seq_shift, h1]
      exact hk

/-- Second direction: if the term at step `k + 1` is rational, then so is the
term at step `k`. -/
lemma rat_cast_of_seq_succ (p : ℕ → ℕ) (hp : ∀ k, 0 < p k) (x₀ : ℝ) (k : ℕ)
    (h : ∃ q : ℚ, seq p x₀ (k + 1) = (q : ℝ)) :
    ∃ q : ℚ, seq p x₀ k = (q : ℝ) := by
  by_cases hk : seq p x₀ k = 0
  · exact ⟨0, by simp [hk]⟩
  · obtain ⟨q, hq⟩ := h
    rw [seq_succ, ite_eq_right hk] at hq
    have hpa : (p k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hp k).ne'
    have ha0 : (p k : ℝ) / seq p x₀ k ≠ 0 := div_ne_zero hpa hk
    have hfloor : (p k : ℝ) / seq p x₀ k =
        (q : ℝ) + ⌊(p k : ℝ) / seq p x₀ k⌋ := by
      rw [← hq, Int.fract_add_floor]
    set c := q + (⌊(p k : ℝ) / seq p x₀ k⌋ : ℚ) with hc
    have ha_eq : (p k : ℝ) / seq p x₀ k = (c : ℝ) := by
      rw [hc]
      push_cast
      exact hfloor
    have hq0 : c ≠ 0 := by
      rw [← Rat.cast_ne_zero (α := ℝ), ← ha_eq]
      exact ha0
    refine ⟨(p k : ℚ) / c, ?_⟩
    have hsk : seq p x₀ k = (p k : ℝ) / ((p k : ℝ) / seq p x₀ k) := by
      field_simp
    rw [hsk, ha_eq]
    push_cast
    ring

/-- If some term of the sequence is rational, then the starting value is
rational (by downward induction). -/
lemma rat_cast_of_seq (p : ℕ → ℕ) (hp : ∀ k, 0 < p k) (x₀ : ℝ) :
    ∀ k : ℕ, (∃ q : ℚ, seq p x₀ k = (q : ℝ)) → ∃ q : ℚ, x₀ = (q : ℝ)
  | 0, h => h
  | k + 1, h => rat_cast_of_seq p hp x₀ k (rat_cast_of_seq_succ p hp x₀ k h)

snip end

problem usa1997_p1 (x₀ : ℝ) (hx₀ : x₀ ∈ Set.Ioo (0 : ℝ) 1) :
    (∃ k, seq (Nat.nth Nat.Prime) x₀ k = 0) ↔ x₀ ∈ solution_set := by
  have hp : ∀ k, 0 < Nat.nth Nat.Prime k := fun k ↦
    Nat.Prime.pos (Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime k)
  obtain ⟨hx0, hx1⟩ := hx₀
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨⟨hx0, hx1⟩, ?_⟩
    obtain ⟨q, hq⟩ := rat_cast_of_seq _ hp x₀ k ⟨0, by simp [hk]⟩
    exact ⟨q, hq.symm⟩
  · rintro ⟨⟨hx0', -⟩, q, rfl⟩
    have hqpos : (0 : ℚ) < q := Rat.cast_pos.mp hx0'
    have hnum : 0 < q.num := Rat.num_pos.mpr hqpos
    obtain ⟨a, ha⟩ : ∃ a : ℕ, q.num = a :=
      ⟨q.num.toNat, (Int.toNat_of_nonneg hnum.le).symm⟩
    have ha0 : 0 < a := Nat.cast_pos.mp (ha ▸ hnum)
    have hx0eq : (q : ℝ) = (a : ℝ) / q.den := by
      rw [Rat.cast_def]
      congr 1
      rw [← Int.cast_natCast, ← ha]
    obtain ⟨k, hk⟩ := terminates_of_rat a ha0 _ hp q.den q.den_pos
    exact ⟨k, by rw [hx0eq]; exact hk⟩

end Usa1997P1
