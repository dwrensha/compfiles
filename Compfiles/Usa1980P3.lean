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
open MvPolynomial Real
-- Newton's Identities
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/MvPolynomial/Symmetric/NewtonIdentities.html#MvPolynomial.mul_esymm_eq_sum
-- MvPolynomial.mul_esymm_eq_sum
noncomputable section

abbrev P (k: ℕ) : MvPolynomial (Fin 3) ℂ := psum (Fin 3) ℂ k

abbrev S (k : ℕ) : MvPolynomial (Fin 3) ℂ := esymm (Fin 3) ℂ k

def f (x y z A B C : ℝ) : Fin 3 → ℂ
| 0 => x * Complex.exp (A * Complex.I)
| 1 => y * Complex.exp (B * Complex.I)
| 2 => z * Complex.exp (C * Complex.I)

end

variable {x y z A B C : ℝ}

lemma movire (n : ℕ) (z : ℂ) : Complex.exp (z * Complex.I) ^ n = Complex.exp (↑n * z * Complex.I) := by
  simpa [Complex.cos_add_sin_I] using Complex.cos_add_sin_mul_I_pow n z

lemma P_def (k : ℕ) : P k = X (0) ^ k + X (1) ^ k + X (2) ^ k := by
  simp [P, psum, Fin.sum_univ_three]


lemma prod_f_im (habc: ∃ k : ℤ, A + B + C = k * π) : (∏ i, f x y z A B C i).im = 0 := by
  obtain ⟨k, h⟩ := habc
  refine Complex.sq_nonneg_iff.mp ?_
  simp only [f, Fin.prod_univ_three]
  -- need to do this awkward maneuver instead of using `suffices` to avoid invoking LE ℂ
  have :
    ↑x * Complex.exp (↑A * Complex.I) * (↑y * Complex.exp (↑B * Complex.I)) * (↑z * Complex.exp (↑C * Complex.I))
      = ↑x * ↑y * ↑z * (Complex.exp (↑A * Complex.I) * Complex.exp (↑B * Complex.I) * Complex.exp (↑C * Complex.I)) := by field_simp
  rw [this, mul_pow]
  norm_cast
  simp_rw [← Complex.exp_add, ← Complex.exp_nat_mul]
  rw [Complex.exp_eq_one_iff.mpr ⟨k, ?_⟩]
  · norm_cast; simpa using sq_nonneg _
  · simp_rw [← add_mul, ← Complex.ofReal_add, h]
    push_cast
    field_simp

lemma sum_f_im (h1: x*sin A + y*sin B + z*sin C = 0) : (∑ i, f x y z A B C i).im = 0 := by
  simp [Fin.sum_univ_three, f, h1]

lemma S_two : (2: MvPolynomial (Fin 3) ℂ) * S 2 = (S 1 * P 1 - P 2) := by
  have : Finset.filter (·.1 < 2) (Finset.antidiagonal 2) = {(0,2),(1,1)} := by
    simpa [Finset.Nat.antidiagonal_eq_image] using by decide
  have newton := mul_esymm_eq_sum (Fin 3) ℂ 2
  rw [Odd.neg_one_pow (by decide)] at newton
  simpa [P, S, ↓this, sub_eq_add_neg] using newton

lemma S_more (k: ℕ) : S (k + 4) = 0 := by
  have : Finset.powersetCard (k + 4) (Finset.univ : Finset (Fin 3)) = ∅ := by simp
  simp [S, esymm, this]

open Real in
lemma P_iff {x y z A B C : ℝ} (n: ℕ) : x^n * sin (n*A) + y^n * sin (n*B) + z^n * sin (n*C) = 0
  ↔ (eval (f x y z A B C) (P n)).im = 0 := by
  simp [P_def, f, mul_pow, movire]
  norm_cast
  simp
  norm_cast
  simp [↓Complex.exp_ofReal_mul_I_im]

lemma P_three : P 3 = S 1 * P 2 - S 2 * P 1 + S 3 * 3 := by
  have prop := mul_esymm_eq_sum (Fin 3) ℂ 3
  have : Finset.filter (·.1 < 3) (Finset.antidiagonal 3) = {(0,3),(1,2),(2,1)} := by
    simpa [Finset.Nat.antidiagonal_eq_image] using by decide
  rw [this] at prop
  simp [Even.neg_one_pow (Nat.even_iff.mpr rfl : Even 4)] at prop
  ring_nf at prop ⊢
  simp [prop]
  ring

lemma P_more (k : ℕ) : P (k + 4) = S 1 * P (k + 3) - S 2 * P (k + 2) + S 3 * P (k + 1) := by
  have prop := mul_esymm_eq_sum (Fin 3) ℂ (k+4)
  let s₂ := Finset.filter (fun a => a.1 < k + 4) (Finset.antidiagonal (k + 4))
  let s₁ : Finset (ℕ × ℕ) := {(0,k+4),(1,k+3),(2,k+2),(3,k+1)}
  have : {(0,k+4),(1,k+3),(2,k+2),(3,k+1)} ⊆ s₂ := by
    dsimp [s₁, s₂]
    rw [Finset.Nat.antidiagonal_eq_image, Finset.subset_iff]
    simp_rw [Finset.mem_insert, Finset.mem_singleton]
    rintro ⟨a, b⟩ (h | h | h | h) <;> simp [h]

  let g (a : ℕ × ℕ) := (-1) ^ a.1 * esymm (Fin 3) ℂ a.1 * psum (Fin 3) ℂ a.2
  have h : ∀ x ∈ s₂ \ s₁, g x = 0 := by
    intro ⟨a, b⟩ hx
    simp [s₂, s₁, g] at hx ⊢
    rcases hx with ⟨⟨_, _⟩, _, _, _, _⟩
    left
    rcases a with n | n | n | n | n
    <;> simp_all
    <;> first | omega | rw [← S_more]
  have := Finset.sum_subset_zero_on_sdiff this h (fun x h => rfl)
  dsimp [s₂, g] at this
  simp [S_more, ← this] at prop

  simp at prop ⊢
  ring_nf at prop ⊢
  rw [sub_eq_zero] at prop
  rw [← prop]
  ring_nf

lemma P_two_im (h2: x^2 * sin (2*A) + y^2 * sin (2*B) + z^2 * sin (2*C) = 0) : ((eval <| f x y z A B C) (P 2)).im = 0 := by
  simp only [P, psum, Fin.sum_univ_three, eval_add, eval_pow, eval_X, f, mul_pow, movire]
  simp_rw [← Complex.cos_add_sin_I]
  norm_cast
  simp [-Complex.ofReal_cos, -Complex.ofReal_sin]
  norm_cast
  linarith

lemma S_two_im (h1: x*sin A + y*sin B + z*sin C = 0) (h2: x^2 * sin (2*A) + y^2 * sin (2*B) + z^2 * sin (2*C) = 0) : ((eval <| f x y z A B C) (S 2)).im = 0 := by
  have : (2 : MvPolynomial (Fin 3) ℂ) = MvPolynomial.C 2 := by rfl
  have : S 2 = MvPolynomial.C (1 / 2) * (2 * S 2) := by
    simp [this, ← mul_assoc, ← C_mul]
  rw [this]
  simp [sum_f_im h1, S_two, P_two_im h2]

lemma S_three_im (habc: ∃ k : ℤ, A + B + C = k * π) : ((eval <| f x y z A B C) (S 3)).im = 0 := by
  have : Finset.powersetCard 3 (Finset.univ: Finset (Fin 3)) = {Finset.univ} :=
    Finset.val_eq_singleton_iff.mp rfl
  simp [S, esymm, this, prod_f_im habc]

section end
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
