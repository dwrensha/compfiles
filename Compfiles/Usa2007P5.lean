/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pacmanboss256
-/

module

public import Mathlib.Tactic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.NumberTheory] }

/-!
# USA Mathematical Olympiad 2007 P5
Prove that for every nonnegative integer n, the number 7^7^n + 1 is the product of at
least 2n + 3 (not necessarily distinct) primes.
-/

namespace USA2007P5
open Nat
snip begin
/-Proof ideas derived from an assortment of posts on https://artofproblemsolving.com/community/c6h145849p825508
  Several lemmas might be useful, such as any natural number having at least one prime factor and any composite having at least two.
-/

lemma factor_poly_an (t : ℕ) : t^7 + 1 = (t + 1) * ((t^6 - t^5) + (t^4 - t^3) + (t^2 - t) + 1) := by
  cases t
  · decide
  · grind [add_mul, Nat.mul_add, Nat.mul_sub]

lemma factor_poly_bn (t : ℕ) : ((t^6 - t^5) + (t^4 - t^3) + (t^2 - t) + 1) = (t+1)^6 - (7*t)*(t^2+t+1)^2 := by
  cases t
  · decide
  · lia

snip end

problem usa2007_p5 (n : ℕ) : 2*n + 3 ≤ (primeFactorsList (7^7^n+1)).length := by
  induction n with
  | zero => simp
  | succ d hd =>

  let x := 7^7^d
  have hx : 7 ≤ x := by
    rw [← pow_one 7, Nat.pow_le_pow_iff_right (by decide)]
    apply one_le_pow
    decide

  rw [pow_succ, pow_mul, factor_poly_an x]
  have ha : x+1 ≠ 0 := add_one_ne_zero _
  let p := (x ^ 6 - x ^ 5) + (x ^ 4 - x ^ 3) + (x ^ 2 - x) + 1
  have hb : p ≠ 0 := add_one_ne_zero _
  have hfacs := Nat.perm_primeFactorsList_mul ha hb
  rw [List.Perm.length_eq hfacs, List.length_append]

  change 2 * d + 3 ≤ (x + 1).primeFactorsList.length at hd
  suffices _ : p.primeFactorsList.length ≥ 2 by omega

  unfold p
  rw [factor_poly_bn x]
  have hql_eq : 7*x = 7^1 * 7^(7^d) := rfl
  have h_even : Even (7^d + 1) := Odd.add_one <| Odd.pow <| odd_iff.mpr rfl
  have hq_sqrt: 7^1*7^7^d = (7^((7^d+1)/2))^2 := by
    rw [← Nat.pow_mul, div_two_mul_two_of_even h_even, Nat.pow_add']
  rw [(show (x+1)^6 = ((x+1)^3)^2 by ring_nf)]
  rw [hql_eq, hq_sqrt, ← mul_pow, Nat.sq_sub_sq]

  let a₀ := (x + 1) ^ 3
  let b₀ := x * (x ^ 2 + x + 1)
  let c₀ := 7^ ((7 ^ d + 1) / 2) * (x ^ 2 + x + 1)
  have tr1: a₀ - b₀ ≤ a₀ - c₀ := by
    refine Nat.sub_le_sub_left ?_ a₀
    rw [mul_le_mul_iff_left₀ <| zero_lt_succ _, Nat.pow_le_pow_iff_right (by decide)]
    lia

  let s := a₀ + c₀
  let q := a₀ - c₀
  have tr3 : 1 < s := by lia
  have tr4 : 1 < q := by lia
  have tr3' : s ≠ 0 := by linarith
  have tr4' : q ≠ 0 := by linarith
  have hfac_second := Nat.perm_primeFactorsList_mul tr3' tr4'

  rw [List.Perm.length_eq hfac_second, List.length_append]
  rw [← Nat.primeFactorsList_ne_nil, ← List.length_pos_iff] at tr3 tr4
  omega


end USA2007P5
