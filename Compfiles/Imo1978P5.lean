/-
Copyright (c) 2025 Roozbeh Yousefzadeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Roozbeh Yousefzadeh
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 1978, Problem 5

Let a_k be a sequence of distinct positive integers for k = 1,2,3, ...

Prove that for all natural numbers n, we have:

sum_{k=1}^{n} a(k)/(k^2) >= sum_{k=1}^{n} (1/k).
-/

open Finset

namespace Imo1978P5

snip begin

/-
The partial sums of a sequence of distinct positive integers dominate the
triangular numbers: ∑_{k ≤ m} f k ≥ 1 + 2 + ⋯ + m. Combining this with
Abel summation against the decreasing weights 1/k² gives
∑ f k / k² ≥ ∑ k / k² = ∑ 1 / k.
-/

/-- A finset of `m` distinct positive integers sums to at least
`1 + 2 + ⋯ + m`. -/
lemma triangular_le_sum :
    ∀ (m : ℕ) (T : Finset ℕ), T.card = m → (∀ x ∈ T, 1 ≤ x) →
    ∑ k ∈ Icc 1 m, k ≤ ∑ x ∈ T, x := by
  intro m
  induction m with
  | zero => intro T _ _; simp
  | succ m ih =>
    intro T hcard hT
    have hne : T.Nonempty := Finset.card_pos.mp (by lia)
    have hM_mem := T.max'_mem hne
    have hM : m + 1 ≤ T.max' hne := by
      have h1 : T.card ≤ (Icc 1 (T.max' hne)).card := Finset.card_le_card
        (fun x hx => Finset.mem_Icc.mpr ⟨hT x hx, Finset.le_max' T x hx⟩)
      rw [hcard, Nat.card_Icc] at h1
      lia
    have herase : (T.erase (T.max' hne)).card = m := by
      rw [Finset.card_erase_of_mem hM_mem, hcard]
      lia
    rw [Finset.sum_Icc_succ_top (by lia), ← Finset.sum_erase_add T _ hM_mem]
    exact add_le_add
      (ih _ herase (fun x hx => hT x (Finset.mem_of_mem_erase hx))) hM

/-- The partial sums of a sequence of distinct positive integers dominate
the partial sums of the identity. -/
lemma triangular_le_partial_sum (f : ℕ → ℕ)
    (h₀ : ∀ m : ℕ, 0 < m → 0 < f m)
    (h₁ : ∀ p q : ℕ, 0 < p → 0 < q → p ≠ q → f p ≠ f q)
    (m : ℕ) :
    ∑ k ∈ Icc 1 m, k ≤ ∑ k ∈ Icc 1 m, f k := by
  have hinj : Set.InjOn f (Icc 1 m) := by
    intro p hp q hq hpq
    rw [Finset.coe_Icc, Set.mem_Icc] at hp hq
    by_contra hne
    exact h₁ p q (by lia) (by lia) hne hpq
  have hcard : ((Icc 1 m).image f).card = m := by
    rw [Finset.card_image_of_injOn hinj, Nat.card_Icc]
    lia
  have hpos : ∀ x ∈ (Icc 1 m).image f, 1 ≤ x := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    exact h₀ k (Finset.mem_Icc.mp hk).1
  calc ∑ k ∈ Icc 1 m, k
      ≤ ∑ x ∈ (Icc 1 m).image f, x := triangular_le_sum m _ hcard hpos
    _ = ∑ k ∈ Icc 1 m, f k := Finset.sum_image (fun p hp q hq => hinj hp hq)

/-- Abel summation comparison: if the partial sums of `h` are dominated by
the partial sums of `g`, then the same holds for sums weighted by any
nonnegative decreasing sequence `w`. -/
lemma abel_compare (n : ℕ) (w g h : ℕ → ℝ)
    (hw : ∀ k ∈ Icc 1 n, 0 ≤ w k)
    (hanti : ∀ j k : ℕ, 1 ≤ j → j ≤ k → k ≤ n → w k ≤ w j)
    (hps : ∀ m : ℕ, 1 ≤ m → m ≤ n → ∑ k ∈ Icc 1 m, h k ≤ ∑ k ∈ Icc 1 m, g k) :
    ∑ k ∈ Icc 1 n, w k * h k ≤ ∑ k ∈ Icc 1 n, w k * g k := by
  induction n generalizing w with
  | zero => simp
  | succ n ih =>
    have key : ∀ x : ℕ → ℝ, ∑ k ∈ Icc 1 (n + 1), w k * x k
        = (∑ k ∈ Icc 1 n, (w k - w (n + 1)) * x k)
          + w (n + 1) * ∑ k ∈ Icc 1 (n + 1), x k := by
      intro x
      rw [Finset.sum_Icc_succ_top (by lia), Finset.sum_Icc_succ_top (by lia)]
      simp only [sub_mul, Finset.sum_sub_distrib, mul_add, Finset.mul_sum]
      ring
    rw [key h, key g]
    have hterm : w (n + 1) * ∑ k ∈ Icc 1 (n + 1), h k
        ≤ w (n + 1) * ∑ k ∈ Icc 1 (n + 1), g k :=
      mul_le_mul_of_nonneg_left (hps (n + 1) (by lia) le_rfl)
        (hw (n + 1) (Finset.mem_Icc.mpr (by lia)))
    refine add_le_add (ih (fun k => w k - w (n + 1)) ?_ ?_ ?_) hterm
    · intro k hk
      rw [Finset.mem_Icc] at hk
      have := hanti k (n + 1) hk.1 (by lia) le_rfl
      linarith
    · intro j k hj hjk hkn
      have := hanti j k hj hjk (by lia)
      linarith
    · exact fun m h1 hm => hps m h1 (by lia)

snip end

problem imo_1978_p5
    (n : ℕ)
    (f : ℕ → ℕ)
    (h₀ : ∀ (m : ℕ), 0 < m → 0 < f m)
    (h₁ : ∀ (p q : ℕ), 0 < p → 0 < q → p ≠ q → f p ≠ f q)
    (h₂ : 0 < n) :
    ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / k ≤ ∑ k ∈ Finset.Icc 1 n, ((f k):ℝ) / k ^ 2 := by
  -- the proof does not need `h₂ : 0 < n`; this reference keeps the linter quiet
  have _ := h₂
  have key := abel_compare n (fun k => 1 / (k : ℝ) ^ 2) (fun k => (f k : ℝ))
    (fun k => (k : ℝ))
    (fun k _ => by positivity)
    (fun j k hj hjk _ => by
      have hj' : (0:ℝ) < j := by exact_mod_cast hj
      gcongr)
    (fun m _ _ => by
      have h := (Nat.cast_le (α := ℝ)).mpr (triangular_le_partial_sum f h₀ h₁ m)
      rwa [Nat.cast_sum, Nat.cast_sum] at h)
  calc ∑ k ∈ Icc 1 n, (1 : ℝ) / k
      = ∑ k ∈ Icc 1 n, 1 / (k : ℝ) ^ 2 * k := by
        refine Finset.sum_congr rfl fun x hx => ?_
        have hx1 : (1:ℝ) ≤ x := by exact_mod_cast (Finset.mem_Icc.mp hx).1
        field_simp
    _ ≤ ∑ k ∈ Icc 1 n, 1 / (k : ℝ) ^ 2 * f k := key
    _ = ∑ k ∈ Icc 1 n, ((f k):ℝ) / k ^ 2 := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [one_div_mul_eq_div]

end Imo1978P5
