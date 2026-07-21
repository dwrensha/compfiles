/-
Copyright (c) 2026 pacmanboss256. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pacmanboss256
-/
import Mathlib.Tactic

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
open MvPolynomial
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

lemma P_def (k : ℕ) : P k = X (0) ^ k + X (1) ^ k + X (2) ^ k := by
  simp [P, psum, Fin.sum_univ_three]

lemma S_zero : S 0 = C 1 := by simp [S]

lemma S_one : S 1 = X (0) + X (1) + X (2) := by simp [S, Fin.sum_univ_three]

lemma S_two : S 2 = X (0) * X (1) + X (1) * X (2) + X (0) * X (2) := by
  simp [S, esymm]
  sorry

lemma S_three : S 3 = X (0) * X (1) * X (2) := by
  simp [S, esymm]
  have : Finset.powersetCard 3 (Finset.univ: Finset (Fin 3)) = {Finset.univ} :=
    Finset.val_eq_singleton_iff.mp rfl
  simp [this, Fin.prod_univ_three]

lemma S_more' (k: ℕ) : S (k + 4) = 0 := by
  have : Finset.powersetCard (k + 4) (Finset.univ : Finset (Fin 3)) = ∅ := by simp
  simp [S, esymm, this]

@[deprecated S_more']
lemma S_more (k: ℕ) (h: k > 3) : S k = 0 := by
  have : Finset.powersetCard k (Finset.univ : Finset (Fin 3)) = ∅ := by simp [h]
  simp [S, esymm, this]

lemma movire (n : ℕ) (z : ℂ) : Complex.exp (z * Complex.I) ^ n = Complex.exp (↑n * z * Complex.I) := by
  simpa [Complex.cos_add_sin_I] using Complex.cos_add_sin_mul_I_pow n z

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
    rw [Finset.Nat.antidiagonal_eq_image]
    simp [Finset.range, Finset.filter_insert, Finset.image, Finset.filter_singleton]
    decide
  rw [this] at prop
  unfold P S
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
    simp [s₂, s₁] at hx
    rcases hx with ⟨⟨_, _⟩, _, _, _, _⟩
    simp [g]
    left
    rcases a with n | n | n | n | n
    <;> simp_all
    <;> first | omega | rw [← S_more']
  have := Finset.sum_subset_zero_on_sdiff this h (fun x h => rfl)
  dsimp [s₂, g] at this
  simp [S_more'] at prop
  rw [← this] at prop

  unfold P S
  simp at prop ⊢
  ring_nf at prop ⊢
  rw [sub_eq_zero] at prop
  rw [← prop]
  ring_nf

lemma newton_sum (a b c : ℂ) (k : ℕ) :
  let p (k: ℕ) := a ^ k + b ^ k + c ^ k
  let s₁ := a + b + c
  let s₂ := a * b + b * c + a * c
  let s₃ := a * b * c
  p (k + 3) = s₁ * p (k + 2) - s₂ * p (k + 1) + s₃ * p k := by
  intro p s₁ s₂ s₃
  let σ := ({a, b, c} : Finset ℂ)
  let l := [a, b, c]
  have := psum_eq_mul_esymm_sub_sum (Fin 3) ℂ 3 (by lia)
  apply_fun (eval (l[·]) ·) at this
  have psum_3 (f : Fin 3 → ℂ) : eval f (psum (Fin 3) ℂ 3) = (f 0) ^ 3 + (f 1) ^ 3 + (f 2) ^ 3 := by
    sorry
  simp only [eval_sub, eval_mul, eval_pow, eval_neg, eval_sum, eval_prod, eval_X, RingHom.map_one, map_natCast] at this

  simp only [psum_3] at this
  simp only [esymm, l, psum] at this
  -- rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ] at this
  simp [Fin.sum_univ_three] at this
  rw [← Finset.univ_filter_card_eq] at this

  have : ∑ x : σ, (x : ℂ) ^ 3 = a ^ 3 + b ^ 3 + c ^ 3 := by calc
    ∑ x : σ, (x : ℂ) ^ 3
    _ = a ^ 3 + b ^ 3 + c ^ 3 := by
      unfold σ
      simp [Finset.image_image, Function.comp_def]
      rw [Finset.sum_insert, Finset.sum_insert]
      simp [← Finset.univ_eq_attach, add_assoc]
      simp
  sorry
section end
snip end

namespace Usa1980P3

open Real

problem usa1980_p3 (x y z A B C: ℝ) (habc: ∃ k : ℤ, A + B + C = k * π)
  (h1: x*sin A + y*sin B + z*sin C = 0)
  (h2: x^2 * sin (2*A) + y^2 * sin (2*B) + z^2 * sin (2*C) = 0)
  : ∀ n : ℕ, x^n * sin (n*A) + y^n * sin (n*B) + z^n * sin (n*C) = 0 := by
  have h_Movire := Complex.cos_add_sin_mul_I_pow
  simp_rw [Complex.cos_add_sin_I] at h_Movire
  let a := x * Complex.exp (A * Complex.I)
  let b := y * Complex.exp (B * Complex.I)
  let c := z * Complex.exp (C * Complex.I)
  -- We don't actually need to name these
  let s₁ := a + b + c
  let s₂ := a * b + b * c + c * a
  let s₃ := a * b * c
  lift s₃ to ℝ with s₃' hs₃
  · rcases habc with ⟨k, h⟩
    refine Complex.sq_nonneg_iff.mp ?_
    simp only [s₃, a, b, c]
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
  lift s₁ to ℝ with s₁' hs₁
  · simp only [s₁, a, b, c]
    rw [Complex.exp_eq_exp_re_mul_sin_add_cos (A * _),Complex.exp_eq_exp_re_mul_sin_add_cos (B * _), Complex.exp_eq_exp_re_mul_sin_add_cos (C * _)]
    simp [Complex.sin_ofReal_re, h1]
  lift a^2 + b^2 + c^2 to ℝ with s₄' hs₄
  · simp only [a, b, c, mul_pow, h_Movire]
    simp_rw [← Complex.cos_add_sin_I]
    norm_cast
    simp [-Complex.ofReal_cos, -Complex.ofReal_sin]
    norm_cast
    linarith
  lift s₂ to ℝ with s₂' hs₂
  · suffices h : s₂ = (s₁' ^ 2 - s₄') / 2 by rw [h]; norm_cast
    simp only [hs₁, s₁, s₂, hs₄]
    ring_nf
  let p (k : ℕ) := a ^ k + b ^ k + c ^ k
  let p' (k : ℕ) : MvPolynomial ({a, b, c}: Finset ℂ) ℂ := X ⟨a, by simp⟩ ^ k
  let σ := ({a, b, c} : Finset ℂ)
  -- we have defined p as a function ℂ → ℂ, and want to use the results of rings
  have m := ({a, b, c} : Multiset ℂ)
  have := m.esymm 3
  have sum (i : ℕ) : p (i+3) = s₁ * p (i+2) - s₂ * p (i+1) + s₃ * p i := by
    -- have := MvPolynomial.sum_antidiagonal_card_esymm_psum_eq_zero ({a, b, c} : Finset ℂ) ℂ
    -- have := psum_eq_mul_esymm_sub_sum σ ℂ 3 (by lia)
    -- apply_fun (eval (fun s => ↑s) ·) at this
    -- simp [esymm, σ, psum] at this
    -- simp at this
    -- rw [esymm_eq_multiset_esymm] at this

    -- rw [MvPolynomial.ext_iff] at this
    -- simp [Finset.sum] at this
    sorry
  have h_equiv (n : ℕ) : x^n * sin (n*A) + y^n * sin (n*B) + z^n * sin (n*C) = 0 ↔ (p n).im = 0 := by
    simp [p, a, b, c, mul_pow, h_Movire]
    norm_cast at ⊢
    simp
    norm_cast
    simp only [Complex.exp_ofReal_mul_I_im]
  intro n
  induction n using Nat.stepInduction 3 with
  | base n hn =>
    rcases n with (rfl | rfl | rfl | _) <;> try lia
    simp [↓h_equiv, p]
  | step n ih =>
    rw [h_equiv]
    norm_cast at ih
    simp_rw [h_equiv] at ih
    -- have := newton_sum a b c n
    -- simp at this
    -- simp only [p, this]
    -- rw [this]
    simpa [sum n, ← hs₁, ← hs₂, ← hs₃, ih] using Or.inr $ ih 0 (by lia)

end Usa1980P3
