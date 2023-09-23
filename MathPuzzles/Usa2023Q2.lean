/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Positive.Field
import Mathlib.Tactic

import MathPuzzles.Meta.ProblemExtraction

#[problem_setup]/-!
# USA Mathematical Olympiad 2023, Problem 2

Let ℝ+ be the set of positive real numbers.
Find all functions f: ℝ+ → ℝ+ that satisfy the equation

  f(x⬝y + f(x)) = x⬝f(y) + 2

for all x,y ∈ ℝ+.
-/

#[problem_setup] namespace Usa2023Q2

#[problem_setup]
abbrev PosReal : Type := { x : ℝ // 0 < x }

#[problem_setup]
notation "ℝ+" => PosReal

fill_in_the_blank solution_set : Set (ℝ+ → ℝ+) := { fun x ↦ x + 1 }

problem usa2023Q2 (f : ℝ+ → ℝ+) :
    f ∈ solution_set ↔
    ∀ x y, f (x * y + (f x)) = x * (f y) + ⟨2, two_pos⟩ := by
  constructor
  · intro hf
    rw [solution_set, Set.mem_singleton_iff] at hf
    intros x y
    rw [hf]
    dsimp only
    rw [mul_add, ←add_assoc (x*y), mul_one, add_assoc (x * y + x)]
    congr
    obtain ⟨x, hx⟩ := x
    obtain ⟨y, hx⟩ := y
    rw [Subtype.mk_eq_mk]
    norm_num
  · -- proof outline from Evan Chen
    -- https://web.evanchen.cc/exams/USAMO-2023-notes.pdf
    --
    -- It suffices to show that f must be a linear function.
    intro P
    suffices h : ∃ a b, f = fun x ↦ a * x + b by
      rw [solution_set, Set.mem_singleton_iff]
      obtain ⟨a, b, hab⟩ := h
      rw [hab] at P
      have P1 : ∀ x, a^2 * x + a * b + b = b * x + ⟨2, two_pos⟩ := by
        intro x
        have P2 := P x 1
        simp only at P2
        rw [←Subtype.coe_inj] at P2
        rw [←Subtype.coe_inj]
        simp only [mul_one, Positive.coe_add, Positive.val_mul] at P2
        simp only [Positive.coe_add, Positive.val_mul, Positive.val_pow]
        linarith
      sorry
    -- 1. prove that f is monotone ("weakly increasing")
    have h1 : Monotone f := by
      intros b a hab
      obtain hab | hab := eq_or_lt_of_le hab
      · rw [hab]
      by_contra H

      rw [not_le] at H
      -- choose y := (f b - f a) / (a - b)
      let ynum : ℝ+ := ⟨(f b).val - (f a).val, sub_pos.mpr H⟩
      let yden : ℝ+ := ⟨(a).val - (b).val, sub_pos.mpr hab⟩
      let y : ℝ+ := ynum / yden
      have hpa := P a y
      have hpb := P b y
      -- a * y + f(a) = a * (f b - f a) / (a - b) + f (a)
      --  ... = a * (f b - f a) / (a - b) + f (a) * (a - b) / (a - b)
      --  ... = [a * (f b - f a) + f (a) * (a - b)] / (a - b)
      --  ... = (a * f (b) - b * f (a)) / (a - b)
      have hpab : a * y + f a = b * y + f b := by
        apply mul_right_cancel (b := yden)
        rw [add_mul, add_mul]
        unfold_let y
        rw [mul_assoc a (ynum / yden) yden, div_mul_cancel']
        rw [mul_assoc b (ynum / yden) yden, div_mul_cancel']
        unfold_let ynum yden
        rw [←Subtype.coe_inj]
        simp only [Positive.coe_add, Positive.val_mul]
        ring
      rw [hpab] at hpa
      rw [hpa] at hpb
      -- ... gives a⬝f(y) + 2 = b⬝f(y) + 2, which is impossible
      replace hpb := add_right_cancel hpb
      apply_fun (fun x ↦ x.val) at hpb
      replace hpb : a.val * ↑(f y) = b.val * ↑(f y) := hpb
      have habv : b.val < a.val := hab
      have hfyp : 0 < (f y).val := (f y).prop
      have h10 : b.val * ↑(f y) < a.val * ↑(f y) :=
        (mul_lt_mul_right hfyp).mpr hab
      rw [hpb] at h10
      simp only [lt_self_iff_false] at h10
    -- 2. prove that |f (x) − (Kx + C)| ≤ 2, where K = 2/f(1)
    --    and C = f (f (1)) − 2 are constants
    -- 3. show that x⬝(K⬝y + K² − f (y)) = O(1) for all x,y
    -- 4. fix x and consider large y
    sorry
