/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Data.Real.Basic

/-!
USA Mathematical Olympiad 2000, Problem 1

Show that there is no function f : ℝ → ℝ that satisfies

  ∀ x y : ℝ, (f(x) + f(y))/2 ≥  f((x + y)/2) + |x - y|

-/

namespace Usa2000Q1

theorem usa2000_q1 :
    ¬∃ f : ℝ → ℝ,
      ∀ x y : ℝ, f ((x + y) / 2) + |x - y| ≤ (f x + f y) / 2 := by
  sorry
