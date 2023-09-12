/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Data.PNat.Defs
import Mathlib.Data.Nat.Parity

import Mathlib.Tactic

/-!
# USA Mathematical Olympiad 2019, Problem 1

Let ℕ+ be the set of positive integers.
A function f: ℕ+ → ℕ+ satisfies the equation

  fᶠ⁽ⁿ⁾(n) ⬝ f²(n) = n^2

for all positive integers n, where fᵏ(m) means f iterated k times on m.
Given this information, determine all possible values of f(1000).
-/

namespace Usa2019Q1

-- @[solution_data]
def solution_set : Set ℕ+ := { x : ℕ+ | Even x.val }

-- @[problem_statement]
theorem usa2019Q1 (m : ℕ+) :
   m ∈ solution_set ↔
    (∃ f : ℕ+ → ℕ+,
      (∀ n, f^[f n] n * f (f n) = n ^ 2) ∧
      m = f 1000) := by
  -- (informal proof outline from artofproblemsolving.com)
  -- 1. prove that f is injective.
  -- 2. prove that if f^r(b)=a and f(a)=a, then b=a.
  -- 3. prove that if f^2(m)=f^{f(m)}(m)=m and m is odd, then f(m)=m.
  -- 4. prove by contradiction that f(m)=m for all odd m.
  -- 5. by injectivity, f(1000) is not odd.
  -- 6. prove that f(1000) can equal any even number.
  sorry
