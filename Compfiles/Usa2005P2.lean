/-
Copyright (c) 2024 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file

/-!
# USA Mathematical Olympiad 2005, Problem 2

Prove that there do not exist integers x,y,z such that

        x⁶ + x³ + x³y + y = 147¹⁵⁷
        x³ + x³y + y² + y + z⁹ = 157¹⁴⁷.
-/

namespace Usa2005P2

problem usa2005_p2 :
    ¬∃ (x y z : ℤ),
       x^6 + x^3 + x^3 * y + y = 147^157 ∧
       x^3 + x^3 * y + y^2 + y + z^9 = 157^147 := by
  sorry
