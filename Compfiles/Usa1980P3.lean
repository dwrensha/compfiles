/-
Copyright (c) 2026 pacmanboss256. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pacmanboss256
-/
import Mathlib

import ProblemExtraction

problem_file {
  tags := [.Algebra]
}

/-!
# USA Mathematical Olympiad 1980, Problem 3

A + B + C is an integral multiple of π. x, y, z are real numbers. If x sin A + y sin B + z sin C = x^2 sin 2A + y^2 sin 2B + z^2 sin 2C = 0, show that x^n sin nA + y^n sin n^B + z^n sin nC = 0 for any positive integer n.
-/

snip begin
-- Solution adapted from Art of Problem Solving.
-- The statement asks for positive integer n, but the proof also needs the base case of n = 0.
-- Note that the Newton Sum formula given on the site only holds for k > 0.
-- To account for this, we use base cases k ∈ Finset.range 4 for the induction.
open MvPolynomial Finset HasAntidiagonal
open Complex hiding sin
open scoped Real
open Real (sin)

noncomputable section

abbrev P (k: ℕ) : MvPolynomial (Fin 3) ℂ := psum (Fin 3) ℂ k

abbrev S (k : ℕ) : MvPolynomial (Fin 3) ℂ := esymm (Fin 3) ℂ k

def f (x y z A B C : ℝ) : Fin 3 → ℂ
| 0 => x * exp (A * I)
| 1 => y * exp (B * I)
| 2 => z * exp (C * I)

section end

variable {x y z α β γ : ℝ}

lemma movire (n : ℕ) (z : ℂ) : exp (z * I) ^ n = exp (↑n * z * I) := by
  simpa [cos_add_sin_I] using cos_add_sin_mul_I_pow n z

lemma P_def (k : ℕ) : P k = X 0 ^ k + X 1 ^ k + X 2 ^ k := by
  simp [P, psum, Fin.sum_univ_three]

lemma prod_f_im (habc: ∃ k : ℤ, α + β + γ = k * π) : (∏ i, f x y z α β γ i).im = 0 := by
  obtain ⟨k, h⟩ := habc
  refine sq_nonneg_iff.mp ?_
  simp only [f, Fin.prod_univ_three]
  -- need to do this awkward maneuver instead of using `suffices` to avoid invoking LE ℂ
  have :
    ↑x * exp (↑α * I) * (↑y * exp (↑β * I)) * (↑z * exp (↑γ * I))
      = ↑x * ↑y * ↑z * (exp (↑α * I) * exp (↑β * I) * exp (↑γ * I)) := by field_simp
  rw [this, mul_pow]
  norm_cast
  simp_rw [← exp_add, ← exp_nat_mul]
  rw [exp_eq_one_iff.mpr ⟨k, ?_⟩]
  · norm_cast; simpa using sq_nonneg _
  · simp_rw [← add_mul, ← ofReal_add, h]
    push_cast
    field_simp

lemma sum_f_im (h1: x*sin α + y*sin β + z*sin γ = 0) : (∑ i, f x y z α β γ i).im = 0 := by
  simp [Fin.sum_univ_three, f, h1]

lemma S_two : S 2 = C (1/2) * (S 1 * P 1 - P 2) := by
  apply_fun (C (2) * ·) using (by intro _ _; simp)
  have eq : ((2 : ℕ) : MvPolynomial (Fin 3) ℂ) = C 2 := by rfl
  have : filter (·.1 < 2) (antidiagonal 2) = {(0,2),(1,1)} := by
    simpa [Nat.antidiagonal_eq_image] using by decide
  simpa [↓← mul_assoc, ↓← C_mul, ← eq, P, S, ↓this, sub_eq_add_neg, Odd.neg_one_pow (Nat.odd_iff.mpr rfl : Odd 3)]
    using mul_esymm_eq_sum (Fin 3) ℂ 2

lemma S_more (k: ℕ) : S (k + 4) = 0 := by
  have : powersetCard (k + 4) (univ : Finset (Fin 3)) = ∅ := by simp
  simp [S, esymm, this]

lemma P_iff (n: ℕ) : x^n * sin (n*α) + y^n * sin (n*β) + z^n * sin (n*γ) = 0
  ↔ (eval (f x y z α β γ) (P n)).im = 0 := by
  simp [P_def, f, mul_pow, movire]
  norm_cast
  simp
  norm_cast
  simp [↓exp_ofReal_mul_I_im]

lemma P_three : P 3 = S 1 * P 2 - S 2 * P 1 + S 3 * 3 := by
  have newton := mul_esymm_eq_sum (Fin 3) ℂ 3
  have : filter (·.1 < 3) (antidiagonal 3) = {(0,3),(1,2),(2,1)} := by
    simpa [Nat.antidiagonal_eq_image] using by decide
  rw [this] at newton
  simp [Even.neg_one_pow (Nat.even_iff.mpr rfl : Even 4)] at newton
  ring_nf at newton ⊢
  simp [newton]
  ring

lemma P_more (k : ℕ) : P (k + 4) = S 1 * P (k + 3) - S 2 * P (k + 2) + S 3 * P (k + 1) := by
  have newton := mul_esymm_eq_sum (Fin 3) ℂ (k+4)
  let s₂ := filter (fun a => a.1 < k + 4) (antidiagonal (k + 4))
  let s₁ : Finset (ℕ × ℕ) := {(0,k+4),(1,k+3),(2,k+2),(3,k+1)}
  have : s₁ ⊆ s₂ := by
    dsimp [s₁, s₂]
    rw [Nat.antidiagonal_eq_image, subset_iff]
    simp_rw [mem_insert, mem_singleton]
    rintro ⟨a, b⟩ (h | h | h | h) <;> simp [h]

  let g (a : ℕ × ℕ) := (-1) ^ a.1 * esymm (Fin 3) ℂ a.1 * psum (Fin 3) ℂ a.2
  have h : ∀ x ∈ s₂ \ s₁, g x = 0 := by
    intro ⟨a, b⟩ hx
    rcases a with _ | _ | _ | _ | n
    on_goal 5 => simp [g, S_more]
    all_goals
      absurd hx
      simp [s₁, s₂]
    all_goals omega
  have := sum_subset_zero_on_sdiff this h (fun x h => rfl)
  dsimp [s₂, g] at this
  simp [S_more, ← this] at newton

  simp [← sub_eq_zero, s₁] at newton ⊢
  ring_nf at newton ⊢
  exact newton

lemma P_two_im (h2: x^2 * sin (2*α) + y^2 * sin (2*β) + z^2 * sin (2*γ) = 0) : ((eval <| f x y z α β γ) (P 2)).im = 0 := by
  simp only [P, psum, Fin.sum_univ_three, eval_add, eval_pow, eval_X, f, mul_pow, movire]
  simp_rw [← cos_add_sin_I]
  norm_cast
  simp [-ofReal_cos, -ofReal_sin]
  norm_cast
  linarith

lemma S_two_im (h1: x*sin α + y*sin β + z*sin γ = 0)
  (h2: x^2 * sin (2*α) + y^2 * sin (2*β) + z^2 * sin (2*γ) = 0)
  : ((eval <| f x y z α β γ) (S 2)).im = 0 := by
  simp [sum_f_im h1, S_two, P_two_im h2]

lemma S_three_im (habc: ∃ k : ℤ, α + β + γ = k * π) : ((eval <| f x y z α β γ) (S 3)).im = 0 := by
  have : powersetCard 3 (univ: Finset (Fin 3)) = {univ} := val_eq_singleton_iff.mp rfl
  simp [S, esymm, this, prod_f_im habc]
snip end

namespace Usa1980P3

open Real

problem usa1980_p3 (x y z A B C: ℝ) (habc: ∃ k : ℤ, A + B + C = k * π)
  (h1: x*sin A + y*sin B + z*sin C = 0)
  (h2: x^2 * sin (2*A) + y^2 * sin (2*B) + z^2 * sin (2*C) = 0)
  : ∀ n : ℕ, x^n * sin (n*A) + y^n * sin (n*B) + z^n * sin (n*C) = 0 := by
  simp_rw [P_iff]
  intro n
  induction n using Nat.stepInduction 4 with
  | base n hn =>
    rcases n with (rfl | rfl | rfl | rfl | _) <;> try lia
    · simp
    · simp [sum_f_im h1]
    · exact P_two_im h2
    · simp [sum_f_im h1, P_three, S_two_im h1 h2, S_three_im habc, P_two_im h2]
  | step n ih =>
    simp [sum_f_im h1, P_more, ih, S_two_im h1 h2, S_three_im habc]


end Usa1980P3
