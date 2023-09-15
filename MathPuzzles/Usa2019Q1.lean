/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Data.PNat.Basic
import Mathlib.Data.Nat.Parity

import Mathlib.Tactic

import MathPuzzles.Meta.Attributes

#[problem_setup]/-!
# USA Mathematical Olympiad 2019, Problem 1

Let ℕ+ be the set of positive integers.
A function f: ℕ+ → ℕ+ satisfies the equation

  fᶠ⁽ⁿ⁾(n) ⬝ f²(n) = n^2

for all positive integers n, where fᵏ(m) means f iterated k times on m.
Given this information, determine all possible values of f(1000).
-/

#[problem_setup] namespace Usa2019Q1

lemma f_injective
    (f : ℕ+ → ℕ+)
    (hf : ∀ n, f^[f n] n * f (f n) = n ^ 2) :
    f.Injective := by
  intros p q hpq
  -- If f(p)=f(q), then f^2(p)=f^2(q) and f^{f(p)}(p) = f^{f(q)}(q)
  have h1 : f^[2] p = f^[2] q := by
    apply_fun f at hpq
    exact hpq

  have h2 : ∀ n : ℕ+, f^[n] p = f^[n] q := by
    intro n
    obtain ⟨n, hn⟩ := n
    cases' n with n <;> aesop

  have h3 : f^[f p] p = f^[f q] q := by rw[hpq]; exact h2 (f q)

  -- ⇒ p^2 = f^2(p) ⬝ f^{f(p)}(p) = f^2(q) ⬝ f^{f(q)}(q) = q^2
  have h4 :=
    calc p^2
      = f^[f p] p * f^[2] p := (hf p).symm
    _ = f^[f q] q * f^[2] q := by rw[h3, h1]
    _ = q^2 := hf q

  -- ⇒ p = q
  obtain ⟨p, hp⟩ := p
  obtain ⟨q, hq⟩ := q
  congr
  apply_fun (fun x ↦ x.val) at h4
  rw[PNat.pow_coe, PNat.pow_coe, PNat.mk_coe, PNat.mk_coe] at h4
  rw[pow_left_inj (le_of_lt hp) (le_of_lt hq) zero_lt_two] at h4
  exact h4

lemma f_iterated_injective
    (f : ℕ+ → ℕ+)
    (hf : ∀ n, f^[f n] n * f (f n) = n ^ 2)
    (r : ℕ) :
    (f^[r]).Injective := by
  induction' r with r ih
  · simp[Function.injective_id]
  · have h1 : f.Injective := f_injective f hf
    rw[Function.iterate_succ]
    exact Function.Injective.comp ih h1

lemma lemma_1
    (f : ℕ+ → ℕ+)
    (hf : ∀ n, f^[f n] n * f (f n) = n ^ 2)
    (a b : ℕ+)
    (r : ℕ)
    (fab1 : f^[r] b = a)
    (fab2 : f a = a) :
    b = a := by
  have h1 : ∀ s, f^[s] a = a := fun s ↦ by
    induction' s with s ih
    · dsimp
    · aesop

  have h2 := calc f^[r] b
      = a := fab1
    _ = f^[r] a := (h1 r).symm

  -- which implies b=a by injectivity of f^r.
  exact f_iterated_injective f hf r h2

lemma lemma_2
    (f : ℕ+ → ℕ+)
    (hf : ∀ n, f^[f n] n * f (f n) = n ^ 2)
    (m : ℕ+)
    (hm1 : f^[2] m = f^[f m] m)
    (hm2 : f^[f m] m = m)
    (hm3 : Odd m.val) :
    f m = m := by
  -- Let f(m)=k.
  let k := f m
  -- Since f^2(m)=m, f(k)=m.
  have h1 : f k = m := by
    unfold_let k; dsimp at hm1 hm2; rw[hm1, hm2]

  -- So, f^2(k)=k.
  have h2 : f^[2] k = k := by dsimp; rw[h1]

  -- f^2(k) · f^{f(k)}(k) = k^2.

  -- Since k≠0, f^{f(k)}(k)=k.
  -- ⇒ f^m(k)=k
  -- ⇒ f^{gcd(m, 2)}(k)=k
  -- ⇒ f(k)=k
  sorry


#[solution_data]
def solution_set : Set ℕ+ := { x : ℕ+ | Even x }

#[problem_statement]
theorem usa2019Q1 (m : ℕ+) :
   m ∈ solution_set ↔
    (∃ f : ℕ+ → ℕ+,
      (∀ n, f^[f n] n * f (f n) = n ^ 2) ∧
      m = f 1000) := by
  -- (informal proof outline from artofproblemsolving.com)
  -- 0. prove that f is injective.
  -- 1. prove that if f^r(b)=a and f(a)=a, then b=a.
  -- 2. prove that if f^2(m)=f^{f(m)}(m)=m and m is odd, then f(m)=m.
  -- 3. prove by contradiction that f(m)=m for all odd m.
  -- 4. by injectivity, f(1000) is not odd.
  -- 5. prove that f(1000) can equal any even number.
  sorry
