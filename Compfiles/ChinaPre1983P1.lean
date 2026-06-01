/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: sjfhsjfh
-/
import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# China Pre-CMO (National High School Math League, Second Round) 1983, Problem 1

求证: 对于任意 `x ∈ [-1, 1]`, 有 `arcsin x + arccos x = π/2`.

Prove that `arcsin x + arccos x = π/2` for all `x ∈ [-1, 1]`.
-/

namespace ChinaPre1983P1

open Real

problem chinaPre1983_p1 (x : ℝ) (hx : x ∈ Set.Icc (-1) 1)
  : arcsin x + arccos x = π/2 := by
  have _ := hx -- clear unused warning
  simp only [arccos, add_sub_cancel]

end ChinaPre1983P1
