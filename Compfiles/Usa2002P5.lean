/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Data.Int.Star
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Ring
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.NumberTheory] }

/-!
# USA Mathematical Olympiad 2002, Problem 5

Let a, b be integers greater than 2. Prove that there exists a positive
integer k and a finite sequence n₁, n₂, ..., nₖ of positive integers such
that n₁ = a, nₖ = b, and nᵢ + nᵢ₊₁ divides nᵢnᵢ₊₁ for each i (1 ≤ i < k).
-/

namespace Usa2002P5

snip begin

/-
Proof idea (following J. Scholes' write-up on kalva).
Write `a ~ b` for `(a + b) ∣ a * b`. The basic links are:
* `t ~ t * (t - 1)` for `t > 1`, since `t + t * (t - 1) = t ^ 2`;
* `2 * t ~ t * (t - 2)` for `t > 2`, since `2 * t + t * (t - 2) = t ^ 2`;
* scaling: `a ~ b` implies `m * a ~ m * b` for `m > 0`.
From these, every `t > 2` links to `2 * t` via
  `t ~ t(t-1) ~ t(t-1)(t-2) ~ t(t-2) ~ 2t`,
and every `t > 3` links to `t - 1` via
  `t ~ t(t-1) ~ t(t-1)(t-2) ~ t(t-1)(t-2)(t-3) ~ 2(t-1)(t-2) ~ (t-1)(t-2) ~ (t-1)`,
where the step `2(t-1)(t-2) ~ (t-1)(t-2)` is the doubling link above expanded
as a sub-chain (it is NOT a single link, contrary to what kalva's compressed
write-up might suggest: e.g. 40 and 20 do not form a link). Hence every
integer `≥ 3` links to `3`, and any two integers greater than 2 link via `3`.
-/

/-- `Linked a b` means that `a` can be connected to `b` by a finite chain of
positive integers in which any two consecutive terms `x, y` satisfy
`x + y ∣ x * y`. -/
inductive Linked : ℤ → ℤ → Prop where
  | refl {a : ℤ} (ha : 0 < a) : Linked a a
  | snoc {a b c : ℤ} (hab : Linked a b) (hc : 0 < c) (hbc : b + c ∣ b * c) :
      Linked a c

namespace Linked

theorem pos_left {a b : ℤ} (h : Linked a b) : 0 < a := by
  induction h with
  | refl ha => exact ha
  | snoc _ _ _ ih => exact ih

theorem pos_right {a b : ℤ} (h : Linked a b) : 0 < b := by
  induction h with
  | refl ha => exact ha
  | snoc _ hc _ _ => exact hc

theorem trans {a b c : ℤ} (hab : Linked a b) (hbc : Linked b c) : Linked a c := by
  revert hab
  induction hbc with
  | refl _ => exact id
  | snoc _ hd hcd ih => exact fun hab => Linked.snoc (ih hab) hd hcd

theorem symm {a b : ℤ} (h : Linked a b) : Linked b a := by
  induction h with
  | refl ha => exact .refl ha
  | snoc hab hc hbc ih =>
    exact (Linked.snoc (Linked.refl hc) hab.pos_right
      (by rw [add_comm, mul_comm]; exact hbc)).trans ih

end Linked

/-- Basic link: `t ~ t * (t - 1)` for `1 < t`, as `t + t * (t - 1) = t ^ 2`. -/
theorem link_pred_mul {t : ℤ} (ht : 1 < t) : Linked t (t * (t - 1)) := by
  have h0 : (0 : ℤ) < t := by omega
  have h1 : (0 : ℤ) < t * (t - 1) := mul_pos h0 (by omega)
  exact .snoc (.refl h0) h1 ⟨t - 1, by ring⟩

/-- Basic link: `2 * t ~ t * (t - 2)` for `2 < t`, as `2 * t + t * (t - 2) = t ^ 2`. -/
theorem link_two_mul_pred {t : ℤ} (ht : 2 < t) : Linked (2 * t) (t * (t - 2)) := by
  have h0 : (0 : ℤ) < 2 * t := by omega
  have h1 : (0 : ℤ) < t * (t - 2) := mul_pos (by omega) (by omega)
  exact .snoc (.refl h0) h1 ⟨2 * (t - 2), by ring⟩

/-- Scaling: `a ~ b` implies `m * a ~ m * b` for `0 < m`. -/
theorem link_mul_left {m : ℤ} (hm : 0 < m) {a b : ℤ} (h : Linked a b) :
    Linked (m * a) (m * b) := by
  induction h with
  | refl ha => exact .refl (mul_pos hm ha)
  | snoc _ hc hbc ih =>
    refine .snoc ih (mul_pos hm hc) ?_
    obtain ⟨q, hq⟩ := hbc
    exact ⟨m * q, by linear_combination (m * m) * hq⟩

/-- Doubling: every `2 < t` links to `2 * t`. -/
theorem link_two_mul {t : ℤ} (ht : 2 < t) : Linked t (2 * t) := by
  have h1 : 1 < t := by omega
  -- `t ~ t * (t - 1)`
  have s1 : Linked t (t * (t - 1)) := link_pred_mul h1
  -- `t * (t - 1) ~ t * (t - 1) * (t - 2)`
  have s2 : Linked (t * (t - 1)) (t * (t - 1) * (t - 2)) := by
    have h := link_mul_left (show (0 : ℤ) < t by omega)
      (link_pred_mul (show 1 < t - 1 by omega))
    rwa [show t - 1 - 1 = t - 2 from by ring, ← mul_assoc] at h
  -- `t * (t - 1) * (t - 2) ~ t * (t - 2)`
  have s3 : Linked (t * (t - 1) * (t - 2)) (t * (t - 2)) := by
    have h := (link_mul_left (show (0 : ℤ) < t - 2 by omega) (link_pred_mul h1)).symm
    rwa [show (t - 2) * t = t * (t - 2) from by ring,
      show (t - 2) * (t * (t - 1)) = t * (t - 1) * (t - 2) from by ring] at h
  -- `t * (t - 2) ~ 2 * t`
  have s4 : Linked (t * (t - 2)) (2 * t) := (link_two_mul_pred ht).symm
  exact (((s1.trans s2).trans s3).trans s4)

/-- Reduction: every `3 < t` links to `t - 1`. -/
theorem link_pred {t : ℤ} (ht : 3 < t) : Linked t (t - 1) := by
  have h1 : 1 < t := by omega
  have hpm1 : Linked (t - 1) ((t - 1) * (t - 2)) := by
    have h := link_pred_mul (show 1 < t - 1 by omega)
    rwa [show t - 1 - 1 = t - 2 from by ring] at h
  have hpm2 : Linked (t - 2) ((t - 2) * (t - 3)) := by
    have h := link_pred_mul (show 1 < t - 2 by omega)
    rwa [show t - 2 - 1 = t - 3 from by ring] at h
  have hu2 : 2 < (t - 1) * (t - 2) := by
    have hpos : 0 < t * (t - 3) := mul_pos (by omega) (by omega)
    have heq : (t - 1) * (t - 2) = t * (t - 3) + 2 := by ring
    omega
  -- `t ~ t * (t - 1)`
  have e1 : Linked t (t * (t - 1)) := link_pred_mul h1
  -- `t * (t - 1) ~ t * (t - 1) * (t - 2)`
  have e2 : Linked (t * (t - 1)) (t * (t - 1) * (t - 2)) := by
    have h := link_mul_left (show (0 : ℤ) < t by omega) hpm1
    rwa [← mul_assoc] at h
  -- `t * (t - 1) * (t - 2) ~ t * (t - 1) * (t - 2) * (t - 3)`
  have e3 : Linked (t * (t - 1) * (t - 2)) (t * (t - 1) * (t - 2) * (t - 3)) := by
    have h := link_mul_left (mul_pos (show (0 : ℤ) < t by omega)
      (show (0 : ℤ) < t - 1 by omega)) hpm2
    rwa [← mul_assoc] at h
  -- `t * (t - 1) * (t - 2) * (t - 3) ~ 2 * ((t - 1) * (t - 2))`
  have e4 : Linked (t * (t - 1) * (t - 2) * (t - 3)) (2 * ((t - 1) * (t - 2))) := by
    have h := (link_two_mul_pred hu2).symm
    rwa [show (t - 1) * (t - 2) * ((t - 1) * (t - 2) - 2)
        = t * (t - 1) * (t - 2) * (t - 3) from by ring] at h
  -- `2 * ((t - 1) * (t - 2)) ~ (t - 1) * (t - 2)`, a whole sub-chain
  have e5 : Linked (2 * ((t - 1) * (t - 2))) ((t - 1) * (t - 2)) :=
    (link_two_mul hu2).symm
  -- `(t - 1) * (t - 2) ~ (t - 1)`
  have e6 : Linked ((t - 1) * (t - 2)) (t - 1) := hpm1.symm
  exact ((((e1.trans e2).trans e3).trans e4).trans e5).trans e6

/-- Every integer `≥ 3` links to `3`. -/
theorem linked_to_three : ∀ n : ℕ, ∀ t : ℤ, t = n + 3 → Linked t 3 := by
  intro n
  induction n with
  | zero =>
    intro t ht
    rw [show t = 3 from by omega]
    exact .refl (by norm_num)
  | succ n ih =>
    intro t ht
    exact (link_pred (t := t) (by omega)).trans (ih (t - 1) (by omega))

theorem linked_of_two_lt {t : ℤ} (ht : 2 < t) : Linked t 3 := by
  refine linked_to_three (t - 3).toNat t ?_
  have h : ((t - 3).toNat : ℤ) = t - 3 := Int.toNat_of_nonneg (by omega)
  omega

/-- Any two integers greater than `2` are linked (via `3`). -/
theorem linked_any {a b : ℤ} (ha : 2 < a) (hb : 2 < b) : Linked a b :=
  (linked_of_two_lt ha).trans (linked_of_two_lt hb).symm

/-- Unfold `Linked` into an explicit sequence. -/
theorem exists_seq_of_linked {a b : ℤ} (h : Linked a b) :
    ∃ k : ℕ, ∃ n : ℕ → ℤ, n 0 = a ∧ n k = b ∧
      (∀ i, i ≤ k → 0 < n i) ∧ ∀ i, i < k → n i + n (i + 1) ∣ n i * n (i + 1) := by
  induction h with
  | refl ha =>
    exact ⟨0, fun _ => a, rfl, rfl,
      fun i hi => by have h0 := Nat.eq_zero_of_le_zero hi; subst h0; exact ha,
      fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | snoc _ hc hbc ih =>
    rename_i _ c _
    obtain ⟨k, n, hn0, hnk, hpos, hlink⟩ := ih
    refine ⟨k + 1, Function.update n (k + 1) c, ?_, ?_, ?_, ?_⟩
    · rw [Function.update_of_ne (by omega)]
      exact hn0
    · rw [Function.update_self]
    · intro i hi
      by_cases hik : i = k + 1
      · subst hik
        rw [Function.update_self]
        exact hc
      · rw [Function.update_of_ne (by omega)]
        exact hpos i (by omega)
    · intro i hi
      by_cases hik : i = k
      · subst hik
        rw [Function.update_of_ne (by omega), Function.update_self, hnk]
        exact hbc
      · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact hlink i (by omega)

snip end

problem usa2002_p5 (a b : ℤ) (ha : 2 < a) (hb : 2 < b) :
    ∃ k : ℕ, ∃ n : ℕ → ℤ, n 0 = a ∧ n k = b ∧
      (∀ i, i ≤ k → 0 < n i) ∧ ∀ i, i < k → n i + n (i + 1) ∣ n i * n (i + 1) :=
  exists_seq_of_linked (linked_any ha hb)

end Usa2002P5
