/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Maar
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 1968, Problem 3

a, b, c are real with a non-zero. x1, x2, ... , xn satisfy the n equations:

        a x_i^2 + b x_i + c = x_{i+1}, for 1 ≤ i < n

        a x_n^2 + b x_n + c = x_1

Prove that the system has zero, 1 or >1 real solutions according as (b - 1)^2 - 4ac is <0, =0 or >0.
-/

namespace Imo1968P3

open Cardinal Finset

/- we define the solutionset as functions from ℕ to ℝ, that eventually vanish, as this allows summing over Finset.range
   as opposed to summing over Fin n -/

def solution_set (n : ℕ) (a b c : ℝ) : Set (ℕ → ℝ) := {x : ℕ → ℝ |
 (∀ i < n, a * (x i)^2 + b * (x i) + c = x (i+1)) ∧
 (a * (x n)^2 + b * (x n) + c = x 0) ∧ (∀ i > n, x i = 0)}

snip begin

def f (a b c : ℝ) : ℝ → ℝ := fun x ↦ a * x^2 + (b-1)* x + c

lemma f_continuous (a b c : ℝ) : Continuous (f a b c) := by
 show Continuous (fun x ↦ a * x^2 + (b-1)* x + c)
 apply Continuous.add
 · apply Continuous.add
   · apply Continuous.mul
     · exact continuous_const
     exact continuous_pow 2
   exact continuous_mul_left (b - 1)
 exact continuous_const

lemma IVT {g : ℝ → ℝ} (hg : Continuous g) {a b : ℝ} (ha : g a ≤ 0) (hb : g b ≥ 0) : ∃ z : ℝ, g z = 0 := by
  by_cases hab : a ≤ b
  · have cont_on : ContinuousOn g (Set.Icc a b) := hg.continuousOn
    have : 0 ∈ Set.Icc (g a) (g b) := Set.mem_Icc.mpr ⟨ha, hb⟩
    rcases intermediate_value_Icc hab (cont_on) this with ⟨z, _, gz_eq⟩
    exact ⟨z, gz_eq⟩
  have hba : b ≤ a := by linarith
  have cont_on : ContinuousOn g (Set.Icc b a) := hg.continuousOn
  have : 0 ∈ Set.Icc (g a) (g b) := Set.mem_Icc.mpr ⟨ha, hb⟩
  rcases intermediate_value_Icc' hba (cont_on) this with ⟨z, z_in, gz_eq⟩
  exact ⟨z, gz_eq⟩

lemma sol_structure_f (a b c : ℝ) (a_ne_zero : a ≠ 0) :
  (discrim a (b-1) c < 0 → ¬ ∃ x : ℝ, f a b c x = 0) ∧
  (discrim a (b-1) c = 0 → (∃ x : ℝ, f a b c x = 0 ∧ ∀ y : ℝ, f a b c y = 0 → y = x) ∧ ((∀ x : ℝ, f a b c x ≥ 0) ∨ ∀ x : ℝ, f a b c x ≤ 0)) ∧
  (discrim a (b-1) c > 0 → ∃ x y : ℝ, x≠y ∧ f a b c x = 0 ∧ f a b c y = 0) := by
  constructor
  · intro h
    push_neg
    intro x
    show a * x^2 + (b-1)* x + c ≠ 0
    rw [pow_two]
    intro hx
    apply (quadratic_eq_zero_iff_discrim_eq_sq a_ne_zero x).1 at hx
    have : discrim a (b-1) c ≥ 0 := by rw [hx]; exact sq_nonneg (2 * a * x + (b - 1))
    linarith
  constructor
  · intro h
    constructor
    · use -(b-1)/(2*a)
      constructor
      · show a * (-(b-1)/ (2 * a))^2 + (b-1) * (-(b-1)/ (2 * a)) + c = 0
        rw [pow_two]
        apply (quadratic_eq_zero_iff_discrim_eq_sq a_ne_zero (-(b-1) / (2 * a))).2
        rw [h]
        field_simp
        ring
      intro y hy
      apply (quadratic_eq_zero_iff_of_discrim_eq_zero a_ne_zero h y).1
      rw [← hy]
      unfold f
      ring
    have : ∀ x : ℝ, f a b c x = a * (x + (b-1)/ (2 * a))^2 := by
      intro x
      simp [f]
      have : c = (b-1)^2/(4*a) := by
        unfold discrim at h
        rw [sub_eq_zero] at h
        rw [h]
        field_simp
      rw [this]
      field_simp
      ring
    by_cases ha : a ≥ 0
    · left
      intro x
      rw [this x]
      apply mul_nonneg
      · exact ha
      exact sq_nonneg (x + (b - 1) / (2 * a))
    right
    intro x
    rw [this x]
    have : a ≤ 0 := by linarith
    apply mul_nonpos_iff.2
    right
    constructor
    · exact this
    exact sq_nonneg (x + (b - 1) / (2 * a))
  intro h
  have : ∃ s : ℝ, discrim a (b-1) c = s * s := by
    apply (isSquare_iff_exists_mul_self (discrim a (b - 1) c)).mp
    apply Real.isSquare_iff.mpr
    exact Std.le_of_lt h
  rcases this with ⟨s, hs⟩
  use (-b +1 + s) / (2 * a), (-b +1 - s) / (2 * a)
  constructor
  · have : s ≠ 0 := by
      rw [hs] at h
      exact mul_self_pos.mp h
    intro h
    field_simp at h
    apply this
    linarith
  constructor
  · unfold f
    rw[pow_two]
    apply (quadratic_eq_zero_iff a_ne_zero hs ((-b +1 + s) / (2 * a))).2
    left
    ring
  unfold f
  rw[pow_two]
  apply (quadratic_eq_zero_iff a_ne_zero hs ((-b +1 - s) / (2 * a))).2
  right
  ring

lemma solution (n : ℕ) {a b c y : ℝ} (h : f a b c y = 0) : (fun i ↦ if i ∈ range (n+1) then y else 0) ∈ solution_set n a b c := by
  let x := (fun i ↦ if i ∈ range (n+1) then y else 0)
  show x ∈ solution_set n a b c
  simp [solution_set]
  constructor
  · intro i hi
    have claim1 : x i = y := by simp [x]; intro h; linarith
    have claim2 : x (i+1) = y := by simp [x]; intro h; linarith
    calc a * x i ^ 2 + b * x i + c = f a b c (x i) + x i := by simp [f]; ring
      _ = f a b c y + y := by rw [claim1]
      _ = x (i+1) := by rw [h, zero_add, claim2]
  constructor
  · have claim1 : x n = y := by simp [x]
    have claim2 : x 0 = y := by simp [x]
    calc a * x n ^ 2 + b * x n + c = f a b c (x n) + x n := by simp [f]; ring
      _ = f a b c y + y := by rw [claim1]
      _ = x 0 := by rw [h, zero_add, claim2]
  intro i hi
  simp [x]
  intro hh
  linarith

lemma sum_sol {n : ℕ} (a b c : ℝ) (x : ℕ → ℝ) : x ∈ solution_set n a b c → ∑ i∈ range (n+1), f a b c (x i) = 0 := by
  intro h
  unfold f
  have := by calc
    ∑ i ∈ range (n+1), (a * x i ^ 2 + (b - 1) * x i + c) = ∑ i ∈ range (n+1), (a * x i ^ 2 + b * x i + c - x i) := by apply sum_congr (rfl); intro i _; ring
    _ = ∑ i ∈ range (n+1), (a * x i ^ 2 + b * x i + c) - ∑ i ∈ range (n+1), x i := sum_sub_distrib (fun i ↦ a * x i ^ 2 + b * x i + c) x
  rw [this]
  apply sub_eq_zero.mpr
  calc ∑ i ∈ range (n+1), (a * x i ^ 2 + b * x i + c) =  ∑ i ∈ range n, (a * x i ^ 2 + b * x i + c) + (a * x n ^ 2 + b * x n + c) := sum_range_succ (fun i ↦ a * x i ^ 2 + b * x i + c) n
    _ = ∑ i ∈ range n, (a * x i ^ 2 + b * x i + c) + x 0 := by rw [h.2.1]
    _ = ∑ i ∈ range n, x (i+1) + x 0 := by apply add_right_cancel_iff.mpr; apply Finset.sum_congr rfl; intro i hi; rw [h.1 i (mem_range.mp hi)]
    _ = ∑ i ∈ range (n+1), x i := Eq.symm (sum_range_succ' x n)

snip end

problem imo1968_p3 {n : ℕ} (a b c : ℝ) (a_ne_zero : a ≠ 0) :
  (discrim a (b-1) c < 0 → #(solution_set n a b c) = 0) ∧
  (discrim a (b-1) c = 0 → #(solution_set n a b c) = 1) ∧
  (discrim a (b-1) c > 0 → #(solution_set n a b c) > 1) := by
  constructor
  · intro h
    apply mk_emptyCollection_iff.mpr
    apply Set.subset_empty_iff.mp
    intro x hx
    exfalso
    have : (∀ y : ℝ, f a b c y > 0) ∨ (∀ y : ℝ, f a b c y < 0) := by
      by_contra!
      rcases this with ⟨⟨y1, hy1⟩, ⟨y2, hy2⟩⟩
      apply (sol_structure_f a b c a_ne_zero).1 h
      exact IVT (f_continuous a b c) hy1 hy2
    rcases this with hf|hf
    · have : ∑ i ∈ range (n+1), f a b c (x i) > 0 := by
        have : (0 : ℝ) = ∑ i ∈ range (n+1), 0 := Eq.symm sum_const_zero
        rw [this]
        refine sum_lt_sum_of_nonempty ?_ fun i a ↦ hf (x i)
        exact nonempty_range_add_one
      have := sum_sol a b c x hx
      linarith
    have : ∑ i ∈ range (n+1), f a b c (x i) < 0 := by
      have : (0 : ℝ) = ∑ i ∈ range (n+1), 0 := Eq.symm sum_const_zero
      rw [this]
      refine sum_lt_sum_of_nonempty ?_ fun i a ↦ hf (x i)
      exact nonempty_range_add_one
    have := sum_sol a b c x hx
    linarith
  constructor
  · intro h
    rcases ((sol_structure_f a b c a_ne_zero).2.1 h).1 with ⟨y, hy, claim1⟩
    let x : ℕ → ℝ := fun i ↦ if i ∈ range (n+1) then y else 0
    have hx : x ∈ solution_set n a b c := by apply solution _ hy
    have sol_unique : ∀ y ∈ solution_set n a b c, y = x := by
      intro z hz
      ext i
      unfold x
      by_cases hh : i ∈ range (n+1)
      · rw [if_pos hh]
        apply claim1
        by_contra!
        have claim3 := sum_sol a b c z hz
        rcases ((sol_structure_f a b c a_ne_zero).2.1 h).2 with claim2|claim2
        · have : f a b c (z i) > 0 := Std.lt_of_le_of_ne (claim2 (z i)) (id (Ne.symm this))
          have claim4 : ∑ i ∈ range (n + 1), f a b c (z i) > 0 := by
            apply (sum_pos_iff_of_nonneg fun x a ↦ claim2 (z x)).mpr
            use i
          linarith
        have : f a b c (z i) < 0 := Std.lt_of_le_of_ne (claim2 (z i)) (this)
        have claim4 : ∑ i ∈ range (n + 1), f a b c (z i) < 0 := by
          apply (sum_neg_iff_of_nonpos fun x a ↦ claim2 (z x)).mpr
          use i
        linarith
      rw [if_neg hh]
      apply hz.2.2 i
      by_contra!
      apply hh
      exact mem_range.2 (Order.lt_add_one_iff.mpr this)

    apply eq_one_iff_unique.mpr
    apply and_comm.1
    constructor
    · apply nonempty_subtype.mpr
      exact ⟨x, hx⟩
    apply subsingleton_iff.mpr
    intro s1 s2
    apply SetCoe.ext
    rw [sol_unique s1, sol_unique s2]
    · exact Subtype.coe_prop s2
    exact Subtype.coe_prop s1

  intro h
  rcases (sol_structure_f a b c a_ne_zero).2.2 h with ⟨y1, y2, hy_ne, hy1, hy2⟩
  let x1 := (fun i ↦ if i ∈ range (n+1) then y1 else 0)
  let x2 := (fun i ↦ if i ∈ range (n+1) then y2 else 0)
  have x1_sol : x1 ∈ solution_set n a b c := solution n hy1
  have x2_sol : x2 ∈ solution_set n a b c := solution n hy2
  apply one_lt_iff_nontrivial.mpr
  use ⟨x1, x1_sol⟩, ⟨x2, x2_sol⟩
  intro hh
  have : x1 = x2 := by calc x1 = (⟨x1, x1_sol⟩ : {z // z ∈ solution_set n a b c}).1 := rfl
    _ = (⟨x2, x2_sol⟩ : {z // z ∈ solution_set n a b c}).1 := by rw [hh]
    _ = x2 := rfl
  apply hy_ne
  calc y1 = x1 0 := by simp [x1]
    _ = x2 0 := by rw [this]
    _ = y2 := by simp [x2]

end Imo1968P3
