/-
Copyright (c) 2023 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Rydh
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 1975, Problem 6

Find all polynomials P, in two variables, with the following properties:

(i) for a positive integer n and all real t, x, y
  P(tx, ty) = tⁿP(x, y)
(that is, P is homogeneous of degree n),

(ii) for all real a, b, c,
  P(b + c, a) + P(c + a, b) + P(a + b, c) = 0,

(iii) P(1, 0) = 1.
-/

namespace Imo1975P6

open Polynomial
open Polynomial.Bivariate

determine solution_set : Set (ℝ[X][Y]) := {P | ∃ n : ℕ+, P = (C X - 2 * Y)*(C X + Y)^(n.val - 1)}

snip begin

lemma mul_pow_eq_pow_succ {n : ℕ+} {t : ℝ} : t * t^(n.val - 1) = t^n.val := by
  rw [←(pow_mul_comm' t (n.val - 1)), ←pow_succ, Nat.sub_add_cancel (Nat.succ_le_of_lt n.pos)]

lemma eq_if_continuous_and_eq_almost_everywhere {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ x : ℚ, f x = g x) : ∀ x, f x = g x := by
  have hrat : Set.range Rat.cast ⊆ {x | f x = g x} := fun x hx ↦ by grind
  have hclosure := (isClosed_eq hf hg).closure_subset_iff.mpr hrat
  exact fun _ ↦ hclosure (by simp [Rat.denseRange_cast.closure_eq])

lemma eq_if_continuous_and_eq_except_one_point {f g : ℝ → ℝ} {a : ℝ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ x, x ≠ a → f x = g x) : f = g := by
  have hDense : Dense {x | x ≠ a} := by
    have h : {x : ℝ | x ≠ a} = {a}ᶜ := by ext x; simp
    rw [h]
    exact dense_compl_singleton a
  exact Continuous.ext_on hDense hf hg h

lemma eq_if_evalEval_eq {P Q : ℝ[X][Y]} (h : ∀ x y, P.evalEval x y = Q.evalEval x y) : P = Q := by
  apply Polynomial.eq_of_infinite_eval_eq P Q
  refine Set.Infinite.mono ?_ (Set.infinite_range_of_injective Polynomial.C_injective)
  intro z hz
  rcases hz with ⟨y, rfl⟩
  exact Polynomial.funext (fun x ↦ h x y)

lemma aux₁ {n : ℕ} (h : 1 < n) : (2 : ℝ) ^ n + 2 * (-1)^n ≠ 0 := by
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · simpa using ne_of_gt (by positivity)
  · apply ne_of_gt
    rw [pow_add (-1), pow_mul]
    norm_num
    nth_rw 1 [← pow_one 2]
    exact pow_lt_pow_right₀ one_lt_two h

lemma aux₂ {a b c : ℝ} {n : ℕ} (h : b ≠ 0): a = b⁻¹^n * c → a * b^n = c := by
  intro h1
  rw [h1, mul_assoc, mul_comm, mul_assoc]
  aesop

lemma linear_int {f : ℝ → ℝ} (h : ∀ x y, f (x + y) = f x + f y) :
    ∀ (n : ℤ) {x : ℝ}, f (n * x) = n * f x := by
  intro n
  induction' n using Int.induction_on with n ih n ih
  · grind [h 0 0]
  all_goals
    intro x
    simp_all
    grind [h (n * x) x, h (-(n * x)) (-x), h x (-x), h 0 0]

lemma linear_inv {f : ℝ → ℝ} (h : ∀ (n : ℤ) {x : ℝ}, f (n * x) = n * f x) :
    ∀ (n : ℤ), f (1 / n) = (1 / n) * f 1 := by
  intro n
  by_cases hn : n = 0 <;> grind only

lemma linear_rat {f : ℝ → ℝ} (h : ∀ (n : ℤ) {x : ℝ}, f (n * x) = n * f x) :
    ∀ (x : ℚ), f x = f 1 * x := by
  intro x
  have h1 := h x.num (x := 1 / x.den)
  have h2 : ((x.den : ℤ) : ℝ) = (x.den : ℝ) := AddCommGroupWithOne.intCast_ofNat x.den
  have h3 : (x.num : ℝ) * (1 / x.den) = x := by rw [Field.ratCast_def x] ; ring
  rwa [h3, ←h2, linear_inv h x.den, ←mul_assoc, h2, h3, mul_comm] at h1

snip end

problem imo1975_p6 {P : ℝ[X][Y]} : P ∈ solution_set ↔
    (∃ n : ℕ+, ∀ t x y : ℝ, P.evalEval (t * x) (t * y) = t^n.val * P.evalEval x y)  ∧
    (∀ a b c : ℝ, P.evalEval (b+c) a + P.evalEval (c+a) b + P.evalEval (a+b) c = 0) ∧
    (P.evalEval 1 0 = 1) := by
  constructor
  · rintro ⟨n, hp⟩
    split_ands
    · use n
      intro t x y
      simp [hp, eval_X, evalEval]
      grind [LeftDistribClass.left_distrib t x y, mul_pow_eq_pow_succ, mul_pow]
    · intro a b c
      simp [hp, eval_X, evalEval]
      ring
    · simp [hp, evalEval_C, eval_X]

  · rintro ⟨h₁, h₂, h₃⟩
    obtain ⟨n, h₁⟩ := h₁

    have hQ_cont : ∀ Q : ℝ[X][Y], Continuous (fun x => (Q.evalEval (1-x) x)) := by
      intro Q
      induction Q using Polynomial.induction_on' with
      | add Q R hQcont hRcont => simpa [Polynomial.evalEval_add] using hQcont.add hRcont
      | monomial n p => simpa [Polynomial.evalEval, Polynomial.eval_monomial] using
            (p.continuous.comp (continuous_const.sub continuous_id)).mul (continuous_pow n)

    let f : ℝ → ℝ := fun x => (P.evalEval (1-x) x) - 1
    have hf_cont : Continuous f := by
      apply Continuous.sub _ continuous_const
      exact hQ_cont P

    have hf : ∀ x y, f (x + y) = f x + f y := by
      intro x y
      grind only [h₂ (x + y) (1 - (x + y)) 0, h₂ x y (1 - x - y)]
    replace hf : ∀ (n : ℤ) (x : ℝ), f (n * x) = n * f x := linear_int hf
    replace hf : ∀ (x : ℚ), f x = f 1 * x := linear_rat hf
    replace hf : ∀ (x : ℚ), f x = -3 * x := fun x ↦ by grind only [h₂ 0 1 0]
    replace hf : ∀ x, f x = -3 * x := eq_if_continuous_and_eq_almost_everywhere hf_cont (continuous_const.mul continuous_id) hf

    have hP_eval : ∀ b a, a ≠ -b → P.evalEval a b = (a - 2 * b) * (a + b)^(n.val - 1) := by
      intro b a hab
      let x := b / (a + b)
      let y := a / (a + b)
      have hfx : f x = (a + b)⁻¹^n.val * P.evalEval a b - 1 := by
        unfold f x
        simp
        have ha : 1 - b / (a + b) = (a + b)⁻¹ * a := by grind only
        have hb : b / (a + b) = (a + b)⁻¹ * b := by grind only
        rw [ha, hb, h₁ (a + b)⁻¹ a b]
        ring
      replace hfx : (-3 * x + 1) * (a + b)^n.val = P.evalEval a b := by
        rw [hf x] at hfx
        have : a + b ≠ 0 := by grind
        exact aux₂ this (add_eq_of_eq_sub hfx)
      grind only [mul_pow_eq_pow_succ]

    have hP_eval' : ∀ b a, P.evalEval a b = (a - 2 * b) * (a + b)^(n.val - 1) := by
      intro b a
      set f : ℝ → ℝ := fun x ↦ P.evalEval x b
      set g : ℝ → ℝ := fun x ↦ (x - 2 * b) * (x + b)^(n.val - 1)
      have hf_cont : Continuous f := (eval (C b) P).continuous
      have hg_cont : Continuous g := by continuity
      exact funext_iff.mp (eq_if_continuous_and_eq_except_one_point hf_cont hg_cont (hP_eval b)) a

    have hP : P = (C X - 2 * Y) * (C X + Y)^(n.val - 1) := by
      apply eq_if_evalEval_eq
      simp [hP_eval', evalEval]

    exact ⟨n, hP⟩

end Imo1975P6
