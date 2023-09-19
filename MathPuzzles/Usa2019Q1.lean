/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Data.PNat.Basic
import Mathlib.Data.Nat.Parity

import Mathlib.Tactic

import MathPuzzles.Meta.ProblemExtraction

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
  have h3 : f^[f k] k * f^[2] k = k^2 := hf k
  rw[h2] at h3

  -- Since k≠0, f^{f(k)}(k)=k.
  have h4 : f^[f k] k = k := by
    rwa[sq k, mul_left_inj] at h3

  -- ⇒ f^m(k)=k
  rw[h1] at h4

  -- ⇒ f^{gcd(m, 2)}(k)=k
  -- ⇒ f(k)=k
  have h6 : ∀ r , f^[2*r] k = k := fun r ↦ by
    induction' r with r ih
    · simp
    · rw [Nat.mul_succ]
      rw [Function.iterate_add]
      change f^[2 * r] (f^[2] k) = k
      rw[h2]
      exact ih
  obtain ⟨m', hm'⟩ := hm3
  rw[hm', add_comm, Function.iterate_add, Function.iterate_one] at h4
  change f (f^[2 * m'] k) = k at h4
  rw[h6 m'] at h4

  rw[h1] at h4
  exact h4.symm

lemma pnat_odd_mul {a b c : ℕ+} (h : a * b = c * c) (hc : Odd c.val) :
    Odd a.val ∧ Odd b.val := by
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  obtain ⟨c, hc⟩ := c
  simp only [PNat.mk_coe]
  rw [PNat.mk_coe] at hc
  apply_fun (fun x ↦ x.val) at h
  dsimp at h
  have h1 : Odd (c * c) := Odd.mul hc hc
  rw [←h] at h1
  exact Nat.odd_mul.mp h1

lemma lemma_3
    (f : ℕ+ → ℕ+)
    (hf : ∀ n, f^[f n] n * f (f n) = n ^ 2)
    (m : ℕ+)
    (hm3 : Odd m.val) :
    f m = m := by
  -- Otherwise, let m be the least counterexample.
  -- Since f^2(m)⬝f^{f(m)}(m)=m^2, either
  --  (1) f^2(m) = k < m, contradicted by Lemma 1 since k is odd and therefore f(k)=k.
  --  (2) f^{f(m)}(m) = k<m, also contradicted by Lemma 1 by similar logic.
  --  (3) f^2(m)=m and f^{f(m)}(m)=m, which implies that f(m)=m by Lemma 2.

  induction' m using PNat.strongInductionOn with m2 ih

  have h1 := hf m2
  rw [sq] at h1
  obtain h2 | h2 := Classical.em (f^[2] m2 < m2)
  · let k := f^[2] m2
    have hkodd : Odd k.val := (pnat_odd_mul h1 hm3).2
    have h3 : f k = k := ih k h2 hkodd
    rw[lemma_1 f hf k m2 2 rfl h3]
    exact h3
  · obtain h4 | h4 := Classical.em (f^[f m2] m2 < m2)
    · let k := f^[f m2] m2
      have hkodd : Odd k.val := (pnat_odd_mul h1 hm3).1
      have h3 : f k = k := ih k h4 hkodd
      rw[lemma_1 f hf k m2 _ rfl h3]
      exact h3
    · have h5 : f^[2] m2 = m2 ∧ f^[f m2] m2 = m2 := by
         simp at h2 h4
         by_contra H
         rw [not_and_or] at H
         obtain h9 | h9 := H
         · replace h2 : m2 < f (f m2) := Ne.lt_of_le' h9 h2
           have h10 : m2 * m2 < f^[↑(f m2)] m2 * f (f m2) := mul_lt_mul_of_le_of_lt h4 h2
           rw [←h1] at h10
           exact LT.lt.false h10
         · replace h4 : m2 < f^[f m2] m2 := Ne.lt_of_le' h9 h4
           have h10 : m2 * m2 < f^[↑(f m2)] m2 * f (f m2) := mul_lt_mul_of_lt_of_le h4 h2
           rw [←h1] at h10
           exact LT.lt.false h10
      obtain ⟨h6, h7⟩ := h5
      have h8 : f^[2] m2 = f^[↑(f m2)] m2 := by rw[h7]; exact h6
      exact lemma_2 f hf _ h8 h7 hm3

fill_in_the_blank solution_set : Set ℕ+ := { x : ℕ+ | Even x.val }

problem usa2019Q1 (m : ℕ+) :
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
  constructor
  · intro hm
    simp only [solution_set, Set.mem_setOf_eq] at hm
    have : ∃ f : ℕ+ → ℕ+, f = fun x ↦ if x = m then 1000 else (if x = 1000 then m else x)
      := ⟨fun x ↦ if x = m then 1000 else (if x = 1000 then m else x), rfl⟩
    obtain ⟨f, hf⟩ := this
    have hmeq : m = f 1000 := by
      simp only [hf, ite_true]
      obtain heq | hne := eq_or_ne 1000 m
      · rw [heq]; simp
      · simp_rw[eq_false hne]
        simp
    have hmeq1 : f m = 1000 := by simp [hf]
    have hmsq : f^[2] m = m := by simp [hf]
    have hmsq' : f^[2] 1000 = 1000 := by simp [hf]

    use f
    constructor
    · intro n
      obtain heq | hne := eq_or_ne n 1000
      · rw [heq, ←hmeq, hmeq1]
        obtain ⟨m', hm'⟩ := hm
        rw [←Nat.two_mul] at hm'
        rw [hm', Function.iterate_mul, Function.iterate_fixed hmsq']
        simp only
      · obtain heq' | hne' := eq_or_ne n m
        · rw [heq', hmeq1]
          rw [← hmeq]
          convert_to f^[2 * 500] m * m = m ^ 2
          · congr
          · rw [Function.iterate_mul, Function.iterate_fixed hmsq]
            exact (sq m).symm
        · have hn : f n = n := by
            simp[hf]
            simp_rw[eq_false hne']
            simp only [ite_false, ite_eq_right_iff]; intro h2; exact (hne h2).elim
          rw[hn, hn]
          rw[Function.iterate_fixed hn]
          exact (sq n).symm
    · exact hmeq
  · intro h
    obtain ⟨f, hf1, hf2⟩ := h
    suffices h : Even m.val by exact h
    by_contra H
    have h1 : Odd m.val := Nat.odd_iff_not_even.mpr H
    have h2 := lemma_3 f hf1 m h1
    rw[hf2] at h2
    have h3 := f_injective f hf1 h2
    rw[hf2, h3] at h1
    simp only at h1
