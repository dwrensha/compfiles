/-
Copyright (c) 2024 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Algebra.Order.Positive.Field
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 1983, Problem 1

Let ℝ+ be the set of positive real numbers.

Determine all functions f : ℝ+ → ℝ+ which satisfy:
 i) f(xf(y)) = yf(x) for all x y ∈ ℝ+.
 ii) f(x) → 0 as x → ∞.
-/

namespace Imo1983P1

abbrev PosReal : Type := { x : ℝ // 0 < x }

notation "ℝ+" => PosReal

snip begin

-- suggested by spqcivitatum on twitch chat
lemma lemma1 (f : ℝ+ → ℝ+)
    (hi : ∀ x y, f (x * f y) = y * f x)
    (hii : ∀ ε, ∃ x, ∀ y, x < y → f y < ε) :
    f ∘ f = id ∧ ∀ x y, f (x * y) = f x * f y := by
  have h1 : f ∘ f = id := sorry
  refine ⟨h1, ?_⟩
  intro x y
  have h2 := hi x (f y)

  apply_fun (fun g ↦ g y) at h1
  change f (f y) = y at h1
  rw [h1] at h2
  rw [h2]
  exact mul_comm _ _

-- to show that f is an automorphism, we need to show that
-- it's a bijective and its a homomorphism (i.e. f (x*y) = f x * f y)

-- f 1 = 1
-- f (f y) = f (1 * f y) = y * f 1 = y
-- so f ∘ f = id
-- so f is bijective
--
-- homomorophism because:
-- ∀ x y,
-- f (x * y) = ... ? = f x * f y
-- hi x (f y) --> f

--
-- then f (x) = x^r for some r
-- (might need continuity actually for this step?)
-- "if f is a continuous automorphism, then ∃ r ≠ 0, f (x) = x^r"


snip end

determine SolutionSet : Set (ℝ+ → ℝ+) := { fun x ↦ 1 / x }

problem imo1983_p1 (f : ℝ+ → ℝ+) :
    f ∈ SolutionSet ↔
    ((∀ x y, f (x * f y) = y * f x) ∧
     (∀ ε, ∃ x, ∀ y, x < y → f y < ε)) := by
  -- following th einformal solution at
  -- https://artofproblemsolving.com/wiki/index.php/1983_IMO_Problems/Problem_1
  constructor
  · rintro rfl
    constructor
    · intro x y; field_simp
    · intro x
      use 1/x
      intro y hy
      dsimp
      exact div_lt_comm.mp hy
  rintro ⟨hi, hii⟩
  rw [Set.mem_singleton_iff]
  have h1 : f 1 = 1 := by
    have h2 := hi 1 1
    have h3 := hi 1 (f 1)
    simp only [one_mul] at h2 h3
    rw [h2, h2, self_eq_mul_right] at h3
    exact h3
  --have hi' : ∀ x, f (x * f x) = x * f x := fun x ↦ hi x x
  suffices h3 : ∀ a, f a = a → a = 1 by
    funext x
    exact eq_one_div_of_mul_eq_one_right (h3 (x * f x) (hi x x))
  intro a ha
  by_contra! H
  have hi1 : ∀ x, f (x * a) = a * f x := fun x ↦ by
    have := hi x a
    rwa [ha] at this
  have h4 : f (1 / a) = 1 / a := by
    have h5 := hi1 (1 / a)
    rw [one_div, mul_left_inv, h1, ← one_div] at h5
    replace h5 := div_eq_iff_eq_mul'.mpr h5
    exact h5.symm
  wlog H1 : 1 < a with h
  · refine h f hi hii h1 (1/a) h4 ?_ ?_ ?_ ?_
    · exact div_ne_one.mpr (Ne.symm H)
    · intro x
      have h7 := hi x (1/a)
      rwa [h4] at h7
    · simp [ha]
    · have h6 : a < 1 := by
        obtain h11 | h12 | h13 := lt_trichotomy a 1
        · exact h11
        · exact (H h12).elim
        · exact (H1 h13).elim
      exact one_lt_div'.mpr h6
  have h8 : f (a^2) = a^2 := by
    have h9 := hi1 a
    rw [ha] at h9
    rwa [←sq] at h9
  have hi2 : ∀ m, ∀ (x : ℝ+), f (x * a^m) = a^m * f x := by
    intro m
    induction' m with pm ih
    · intro x; simp
    · intro x
      rw [pow_succ]
      have h10 : x * (a * a ^ pm) = x * a^pm * a := by ac_rfl
      rw [h10]
      rw [hi1 (x * a^pm)]
      rw [ih x]
      ac_rfl
  have h9 : ∀ k, f (a^(2^k)) = a^(2^k) := by
    intro k
    induction' k with pk ih
    · simp [ha]
    · rw [pow_succ, mul_comm]
      rw [pow_mul]
      have h9 := hi1 (a ^ 2 ^ pk)
      --
      have h10 := hi2 (2 ^ pk) (a ^ 2 ^ pk)
      rw [←sq] at h10
      rw [h10, ih, sq]
  -- a > 1, so a^2^k approaches ∞ as k → ∞
  -- but a^2^k = f (a^2^k), so that contracts ii
  obtain ⟨x0, hx0⟩ := hii 1
  have h12 : ∃ k, x0 < a^2^k := by
    -- need 2 ^ k > logₐ x0
    -- k > log_2 logₐ x
    -- k = 1 + log_2 logₐ x
    --have : 1 + 2^k * ε  ≤ (1 + ε) ^ 2 ^ k
    obtain ⟨x, hx⟩ := x0
    obtain ⟨a, ha0⟩ := a
    use Nat.ceil (1 + Real.logb 2 (Real.logb a x))
    change x < a ^ 2 ^ ⌈1 + Real.logb 2 (Real.logb a x)⌉₊
    sorry
  obtain ⟨k0, hk1⟩ := h12
  have h13 := hx0 (a ^ 2 ^ k0) hk1
  rw [h9] at h13
  have h14 : 1 ≤ a ^ 2 ^ k0 := by
    have h15 : 2^k0 ≠ 0 := by positivity
    exact le_of_lt (one_lt_pow' H1 h15)
  rw [lt_iff_not_le] at h13
  contradiction
