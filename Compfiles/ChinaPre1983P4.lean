/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: sjfhsjfh
-/
import Mathlib

import ProblemExtraction

problem_file { tags := [.Geometry] }

/-!
# China Pre-CMO (National High School Math League, Second Round) 1983, Problem 4

在六条棱长分别为 `2`, `3`, `3`, `4`, `5`, `5` 的所有四面体中, 最大的体积是多少? 证明你的结论.

Among all tetrahedra whose six edge lengths are `2`, `3`, `3`, `4`, `5`, `5`,
what is the maximum volume? Prove your conclusion.
-/

open FiniteDimensional
open Module

variable {V : Type*} {Pt : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace Pt]
variable [NormedAddTorsor V Pt]

namespace ChinaPre1983P4

noncomputable def tetraVolume (A B C D : Pt) : ℝ :=
  let v₁ := B -ᵥ A
  let v₂ := C -ᵥ A
  let v₃ := D -ᵥ A
  let det := ‖v₁‖ ^ 2 * ‖v₂‖ ^ 2 * ‖v₃‖ ^ 2
    + 2 * inner ℝ v₁ v₂ * inner ℝ v₂ v₃ * inner ℝ v₃ v₁
    - ‖v₁‖ ^ 2 * (inner ℝ v₂ v₃) ^ 2
    - ‖v₂‖ ^ 2 * (inner ℝ v₃ v₁) ^ 2
    - ‖v₃‖ ^ 2 * (inner ℝ v₁ v₂) ^ 2
  Real.sqrt det / 6

determine maxVolume : ℝ := sorry

problem chinaPre1983_p4 [Fact (finrank ℝ V = 3)]
  : (∃ (A B C D : Pt),
      List.Perm [dist A B, dist A C, dist A D, dist B C, dist B D, dist C D]
        [2, 3, 3, 4, 5, 5] ∧
      tetraVolume A B C D = maxVolume) ∧
    ∀ (A B C D : Pt),
      List.Perm [dist A B, dist A C, dist A D, dist B C, dist B D, dist C D]
        [2, 3, 3, 4, 5, 5] →
      tetraVolume A B C D ≤ maxVolume := by
  sorry

end ChinaPre1983P4
