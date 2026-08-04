/-
Copyright (c) 2025 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: pacmanboss256
-/

module

public import Mathlib.Tactic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Algebra] }
/-!
# USA Mathematical Olympiad 1976, Problem 5

If $P(x)$, $Q(x)$, $R(x)$, and $S(x)$ are all polynomials such that
\[P(x^5) + xQ(x^5) + x^2 R(x^5) = (x^4 + x^3 + x^2 + x +1) S(x),\]
prove that $x-1$ is a factor of $P(x)$.
-/

namespace USA1976P5
open Polynomial

snip begin
/-follows solutions 2 and 3 from https://artofproblemsolving.com/wiki/index.php?title=1976_USAMO_Problems/Problem_5-/
theorem cyclotomic_roots (P Q R S : ℂ[X]):  (∀x, P.eval (x^5) + x * Q.eval (x^5) + x^2 * R.eval (x^5) = (x^4 + x^3 + x^2 + x + 1) * (S.eval (x^5))) → P.eval (1) = 0 := by

    intro h
    let c5 := Polynomial.cyclotomic 5 ℂ
    have c5_eq: ∀x, c5.eval x = (x^4 + x^3 + x^2 + x + 1) := by
      intro x
      have : Fact (Nat.Prime 5) := by decide
      have a := Polynomial.cyclotomic_prime ℂ 5
      simp [c5, a, Finset.sum]
      repeat rw [← add_assoc]
    have prim_roots : c5.roots = (primitiveRoots 5 ℂ).val := by
      apply Polynomial.cyclotomic.roots_eq_primitiveRoots_val
    have five_pow : ∀(x:ℂ), IsPrimitiveRoot x 5 → x^5 = 1 := by
      intro x hx
      rwa [IsPrimitiveRoot.pow_eq_one_iff_dvd]

    have h' : ∀ (x : ℂ), IsPrimitiveRoot x 5 →
      ↑(eval 1 P) + x * ↑(eval 1 Q) + x ^ 2 * ↑(eval 1 R) = 0 := by
      intro x hr
      have hr_c := hr
      have right_zero: ∀(x: ℂ), IsPrimitiveRoot x 5 → (x ^ 4 + x ^ 3 + x ^ 2 + x + 1) * ↑(eval 1 S) = 0 := by
        intro x pr
        apply IsPrimitiveRoot.geom_sum_eq_zero at pr
        simp [Finset.sum, ← add_assoc] at pr
        rw [pr, zero_mul]
      specialize h x
      apply right_zero at hr
      rw [five_pow] at h
      · rw [hr] at h
        assumption
      assumption

    have hz: ∃(z: ℂ), IsPrimitiveRoot z 5 := by
      suffices hz : ∃z, z ∈ c5.roots
      · obtain ⟨z, hz0⟩ := hz
        use z
        rw [Polynomial.cyclotomic.roots_eq_primitiveRoots_val] at hz0
        simp at hz0
        assumption
      by_contra! hz'

      have hdeg : 0 < c5.degree := by
        apply Polynomial.degree_cyclotomic_pos
        decide
      have ex := Complex.exists_root hdeg
      obtain ⟨z, isroot⟩ := ex
      rw [← Polynomial.mem_roots] at isroot
      · tauto
      apply Polynomial.cyclotomic_ne_zero
    obtain ⟨z, hz⟩ := hz

    have hz2 : IsPrimitiveRoot (z^2) 5 :=  by
      apply IsPrimitiveRoot.pow_of_prime hz
      · decide
      decide
    have hz3 : IsPrimitiveRoot (z^3) 5 :=  by
      apply IsPrimitiveRoot.pow_of_prime hz
      · decide
      decide
    let a  := ↑(eval 1 P)
    let b := ↑(eval 1 Q)
    let c  := ↑(eval 1 R)
    let z₀ := z
    let z₁ := z^2
    let z₂ := z^3
    change ∀ (x : ℂ), IsPrimitiveRoot x 5 → a + x * b + x ^ 2 * c = 0 at h'
    have h1 := h' z₀ hz
    have h2 := h' z₁ hz2
    have h3 := h' z₂ hz3
    have h_eq_1 :b =  -(z₁ + z₀)*c:= by
      rw [← h1, add_assoc, add_assoc] at h2
      apply add_left_cancel at h2
      rw [← sub_neg_eq_add,← sub_neg_eq_add, sub_eq_sub_iff_sub_eq_sub,
        sub_neg_eq_add, neg_add_eq_sub, ← sub_mul, ← sub_mul] at h2
      nth_rw 2 [← neg_sub] at h2
      rw [sq_sub_sq, neg_mul_comm, mul_rotate, mul_assoc] at h2
      apply mul_left_cancel₀ at h2
      · rwa [neg_mul_comm, mul_comm] at h2
      rw [sub_ne_zero]
      simp [z₁,z₀]
      by_contra! hne
      apply eq_zero_or_one_of_sq_eq_self at hne
      rcases hne with zero | one
      · apply IsPrimitiveRoot.ne_zero hz
        · decide
        assumption
      apply IsPrimitiveRoot.ne_one hz
      · decide
      assumption


    have h_eq_2 :b =  -(z₂ + z₀)*c:= by
      rw [← h1, add_assoc, add_assoc] at h3
      apply add_left_cancel at h3
      rw [← sub_neg_eq_add,← sub_neg_eq_add, sub_eq_sub_iff_sub_eq_sub,
        sub_neg_eq_add, neg_add_eq_sub, ← sub_mul, ← sub_mul] at h3
      nth_rw 2 [← neg_sub] at h3
      rw [sq_sub_sq, neg_mul_comm, mul_rotate, mul_assoc] at h3
      apply mul_left_cancel₀ at h3
      · rwa [neg_mul_comm, mul_comm] at h3
      rw [sub_ne_zero]
      simp [z₂,z₀]
      by_contra! hne
      nth_rw 2 [← pow_one z] at hne
      linarith [IsPrimitiveRoot.pow_inj hz (by decide) (by decide) hne]



    rw [h_eq_1] at h_eq_2
    rw [mul_eq_mul_right_iff] at h_eq_2
    rcases h_eq_2 with wrong | zero
    · simp [z₁, z₂] at wrong
      have : z ^ 2 ≠ z ^ 3 := by
        by_contra! hn
        apply IsPrimitiveRoot.pow_inj hz at hn
        · simp at hn
        · decide
        decide
      contradiction
    simp [zero] at h_eq_1
    simp [zero, h_eq_1, a] at h1
    assumption



snip end

theorem Usa1976P5 (P Q R S : ℂ[X]) : (∀x, P.eval (x^5) + x * Q.eval (x^5) + x^2 * R.eval (x^5) = (x^4 + x^3 + x^2 + x + 1)* (S.eval (x^5))) → (X - C 1) ∣ P := by

  intro h
  have p1 := cyclotomic_roots P Q R S h
  rw [Polynomial.dvd_iff_isRoot]
  simp
  assumption

end USA1976P5
