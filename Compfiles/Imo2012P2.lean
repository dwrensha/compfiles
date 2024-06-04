/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic
import Mathlib.Analysis.MeanInequalities

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 2012, Problem 2

Let a₂, a₃, ..., aₙ be positive reals with product 1, where n ≥ 3.
Show that
  (1 + a₂)²(1 + a₃)³...(1 + aₙ)ⁿ > nⁿ.
-/

namespace Imo2012P2

problem imo2012_p2 (n : ℕ) (hn : 3 ≤ n) (a : Finset.Icc 2 n → ℝ)
    (apos : ∀ i, 0 < a i) (aprod : ∏ i, a i = 1) :
    (n:ℝ)^n < ∏ i, (1 + a i)^i.val := by
  -- informal solution from
  -- https://web.evanchen.cc/exams/IMO-2012-notes.pdf
  have h1 : ∀ i : Finset.Icc 2 n,
      (1 + a i)^i.val ≤
        i.val ^ i.val / (i.val - 1) ^ (i.val - 1) * a i := by
    -- Real.geom_mean_le_arith_mean_weighted
    -- 1 = ∑ 1 / (i.val - 1)
    sorry
  sorry
