/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pacmanboss256
-/

module

public import Mathlib.Tactic
public import ProblemExtraction

@[expose] public section

/-!
# USA Mathematical Olympiad 2007 P5
Prove that for every nonnegative integer n, the number 7^7^n + 1 is the product of at
least 2n + 3 (not necessarily distinct) primes.
-/

namespace USA2007P5
open Nat
snip begin
/-Proof ideas derived from an assortment of posts on https://artofproblemsolving.com/community/c6h145849p825508
  Proving the factorization in factor_poly_a in ℕ was my own, and several lemmas might be useful, such as any natural number having at least one prime factor and any composite having at least two. Factoring polynomials is a pain in Lean
-/


lemma factor_poly_a (t : ℤ) : t^7 + 1 = (t+1) * (t^6 - t^5 + t^4 - t^3 + t^2 - t + 1) := by ring_nf

lemma factor_poly_b (t : ℤ): (t^6 - t^5 + t^4 - t^3 + t^2 - t + 1) = (t+1)^6 - (7*t)*(t^2+t+1)^2  := by
  ring_nf

/-`ring` fails here for `ℕ`-/
lemma factor_poly_an (t : ℕ)(ht : t ≥ 7): t^7 + 1 = (t + 1) * (t^6 - t^5 + t^4 - t^3 + t^2 - t + 1) := by
  symm
  rw [(show (t + 1) * (t^6 - t^5 + t^4 - t^3 + t^2 - t + 1) = t * (t^6 - t^5 + t^4 - t^3 + t^2 - t + 1) + (t^6 - t^5 + t^4 - t^3 + t^2 - t + 1) by rw [add_mul, one_mul])]
  have f0 : t * ((t^6 - t^5) + (t^4 - t^3) + (t^2 - t) + 1) = t * (t^6 - t^5 + t^4 - t^3 + t^2 - t + 1) := by
    simp
    left
    rw [Nat.add_sub_assoc, Nat.add_sub_assoc]
    focus
      rw [pow_le_pow_iff_right₀]
      · decide
      linarith

    nth_rw 1 [← pow_one t]
    · rw [pow_le_pow_iff_right₀]
      · decide
      linarith

  have f1 : (t * ((t^6 - t^5) + (t^4 - t^3) + (t^2 - t) + 1)) + (t^6 - t^5 + t^4 - t^3 + t^2 - t + 1) = (t^7 - t^6 + t^5 - t^4 + t^3 - t^2 + t) + (t^6 - t^5 + t^4 - t^3 + t^2 - t + 1) := by
    simp
    repeat rw [mul_add]
    simp
    repeat rw [Nat.mul_sub]
    repeat rw [mul_comm, ← pow_succ]
    simp
    rw [← pow_two,Nat.add_sub_assoc,Nat.add_sub_assoc]
    focus
      rw [pow_le_pow_iff_right₀]
      · decide
      linarith
    focus
      rw [pow_le_pow_iff_right₀]
      · decide
      linarith
  rw [← f0, f1]
  induction' t with d hd
  · decide
  grind


/-same here-/
lemma factor_poly_bn (t : ℕ)(ht : t ≥ 7) : (t^6 - t^5 + t^4 - t^3 + t^2 - t + 1) = (t+1)^6 - (7*t)*(t^2+t+1)^2 := by
  induction' t with d hd
  · decide
  grind
snip end

problem usa2007_p5 (n : ℕ) : (primeFactorsList (7^(7^n)+1)).length ≥ 2*n + 3 := by
  induction n with
  | zero => simp
  | succ d hd =>
  have h0 : 7 ^ 7 ^ (d + 1) + 1 = (7^7^d)^7 +1 := by ring_nf
  let x := 7^(7^d)

  have hx : x ≥ 7 := by
    change 7^7^d ≥ 7
    induction' d with m hm
    · decide
    change 7^1 ≤ 7^7^(m+1)
    have hmpos: 0 < m+1:= by
      rw [← succ_eq_add_one]
      apply zero_lt_succ m
    rw [Nat.pow_le_pow_iff_right]
    · apply one_le_pow; decide
    decide

  rw [h0]
  change (x^7 + 1).primeFactorsList.length ≥ 2 * d + 5
  rw [factor_poly_an x hx]
  have ha : x+1 ≠ 0 := by linarith
  let p := (x ^ 6 - x ^ 5 + x ^ 4 - x ^ 3 + x ^ 2 - x + 1)
  have hb : p ≠ 0 := by unfold p; linarith
  have hfacs := Nat.perm_primeFactorsList_mul ha hb
  rw [List.Perm.length_eq hfacs, List.length_append]
  change (x + 1).primeFactorsList.length ≥ 2 * d + 3 at hd
  have f3: (x + 1).primeFactorsList.length + p.primeFactorsList.length ≥ 2*d+3 + p.primeFactorsList.length := by linarith
  have f4 : p.primeFactorsList.length ≥ 2 := by
    have l1 : p = (x+1)^6 - (7*x)*(x^2+x+1)^2 := by rw [← factor_poly_bn x hx]
    rw [l1]
    have hql_eq : (7*x) = 7^1 * 7^(7^d) := rfl
    have h_even : Even (1 + 7^d) := Odd.one_add <| Odd.pow <| odd_iff.mpr rfl
    have hq_sqrt: (7^1*7^7^d) = (7^((7^d+1)/2))^2 := by
      have hhalf : (7 ^ d + 1) / 2 + (7 ^ d + 1) / 2 = (7 ^ d + 1) := by
        rw [← two_mul]
        apply two_mul_div_two_of_even
        rwa [add_comm]

      rw [pow_two, ← pow_add, ← pow_add, pow_right_inj₀]
      · rw [hhalf, add_comm]
      · decide
      decide


    have hq_eq : (7^1*7^7^d)*(x^2+x+1)^2 = ((7^((7^d+1)/2)) * (x^2+x+1))^2 := by rw [hq_sqrt, mul_pow]

    have hsq : (x+1)^6 - (7*x)*(x^2+x+1)^2 =
    ((x+1)^3+(7 ^ ((7 ^ d + 1) / 2) * (x ^ 2 + x + 1))) * (((x+1)^3)-(7 ^ ((7 ^ d + 1) / 2) * (x ^ 2 + x + 1))) := by
      rw [ (show (x+1)^6 = ((x+1)^3)^2 by ring_nf)]
      rw [hql_eq, hq_sqrt, ← mul_pow]
      rw [Nat.sq_sub_sq]

    rw [hsq]
    have f5 : 7 ^ ((7 ^ d + 1) / 2) ≤ x := by
      change 7 ^ ((7 ^ d + 1) / 2) ≤ 7^(7^d)
      rw [Nat.pow_le_pow_iff_right]
      · grind
      decide

    let a₀ := (x + 1) ^ 3
    let b₀ := (x * (x ^ 2 + x + 1))
    let c₀ := (7^ ((7 ^ d + 1) / 2) * (x ^ 2 + x + 1))
    have tr1: a₀ - b₀ ≤ a₀ - c₀ := by
      suffices tr1' : c₀ ≤ b₀ from Nat.sub_le_sub_left tr1' a₀
      change 7^ ((7 ^ d + 1) / 2) * (x ^ 2 + x + 1) ≤ x * (x ^ 2 + x + 1)
      rw [mul_le_mul_iff_left₀]
      · exact f5
      grind

    have tr7 : a₀ - b₀ > 1 := by grind
    have tr8 : a₀ - c₀ > 1 := by linarith

    let s := (x + 1) ^ 3 + (7^((7 ^ d + 1) / 2)) * (x ^ 2 + x + 1)
    let q := (x + 1) ^ 3 - (7^((7 ^ d + 1) / 2)) * (x ^ 2 + x + 1)
    have tr3 : 1 < s := by grind
    have tr4 : 1 < q := by grind
    have tr3' : s ≠ 0 := by linarith
    have tr4' : q ≠ 0 := by linarith
    have hfac_second := Nat.perm_primeFactorsList_mul tr3' tr4'

    have f6 : (s*q).primeFactorsList.length = (s.primeFactorsList ++ q.primeFactorsList).length := by
      rw [← List.Perm.length_eq hfac_second]

    rw [f6, List.length_append]
    rw [← Nat.primeFactorsList_ne_nil] at tr3 tr4
    apply List.length_pos_of_ne_nil at tr3
    apply List.length_pos_of_ne_nil at tr4
    rw [zero_lt_iff, ← one_le_iff_ne_zero] at tr3 tr4
    omega
  omega


end USA2007P5
