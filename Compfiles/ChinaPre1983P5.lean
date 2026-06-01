/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: sjfhsjfh
-/
import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# China Pre-CMO (National High School Math League, Second Round) 1983, Problem 5

函数 `F(x) = |cos²x + 2 sin x cos x − sin²x + Ax + B|` 在 `0 ≤ x ≤ (3/2)π`
上的最大值 `M` 与参数 `A`, `B` 有关. 问 `A`, `B` 取什么值时 `M` 为最小? 证明你的结论.

Let `F(x) = |cos²x + 2 sin x cos x − sin²x + Ax + B|` for `0 ≤ x ≤ (3/2)π`.
Let `M(A, B)` be the maximum of `F(x)` on this interval.
For which values of `A` and `B` does `M(A, B)` attain its minimum? Prove your conclusion.
-/

namespace ChinaPre1983P5

open Real

noncomputable def F (A B x : ℝ) : ℝ :=
  |(cos x) ^ 2 + 2 * sin x * cos x - (sin x) ^ 2 + A * x + B|

noncomputable def M (A B : ℝ) : ℝ :=
  sSup (F A B '' Set.Icc 0 (3 / 2 * π))

determine optA : ℝ := 0

determine optB : ℝ := 0

problem chinaPre1983_p5
  : ∀ A B : ℝ, M optA optB ≤ M A B := by
  sorry

end ChinaPre1983P5
