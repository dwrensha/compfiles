/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Data.Real.Basic

/-!
USA Mathematical Olympiad 2000, Problem 1

A function f : ℝ → ℝ is called "very convex" if it satisfies

  ∀ x y : ℝ, (f(x) + f(y))/2 ≥  f((x + y)/2) + |x - y|.

Show that there exist no very convex functions.
-/

namespace Usa2000Q1

theorem usa2000_q1 :
    ¬∃ f : ℝ → ℝ,
      ∀ x y : ℝ, f ((x + y) / 2) + |x - y| ≤ (f x + f y) / 2 := by
  -- Informal solution from artofproblemsolving.com
  -- Suppose, for the sake of contradiction, that f is very convex.
  -- Notice that f(x) is very convex if and only if f(x) + C is convex, where C
  -- is any constant. Thus, we can set f(0) = 0 for convenience.

  -- Suppose that f(1) = A and f(-1) = B.
  -- By the very convex condition, (f(0) + f(2⁻ⁿ))/2 ≥ f(2⁻⁽ⁿ⁺¹⁾) + 1/2ⁿ

  -- A straightforward induction shows that f(2⁻ⁿ) ≤ (A - 2n) / 2ⁿ
  -- for all nonnegative integers n.

  -- Using a similar line of reasoning as above, f(-2⁻ⁿ) ≤ (B - 2n)/2ⁿ.
  -- Therefore, for every nonnegative integer n, f(2⁻ⁿ) + f(-2⁻ⁿ) ≤ (A+B-4n)/2ⁿ.
  -- Now, we choose n large enough such that n > (A+B)/4 - 1.
  -- It follows that f(2⁻ⁿ) + f(-2⁻ⁿ) < 1/2ⁿ⁻².
  -- However, by the very convex condition, f(2⁻ⁿ) + f(-2⁻ⁿ) ≥ 1/2ⁿ⁻².
  -- This is a contradiction.
  sorry
