/-
Copyright (c) 2026 pacmanboss256. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pacmanboss256
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file {
  tags := [.Algebra]
}

/-!
# USA Mathematical Olympiad 1991, Problem 4
let $ a =\frac{m^{m+1} + n^{n+1}}{m^m + n^n} $ where $\m$ and $n$ are positive integers. Prove that $a^m + a^n \geq m^m + n^n$.
-/

namespace Usa1991P4

problem usa1991_p4 (m n : ℕ) (a: ℝ)
  (ha : a = (m^(m+1)+ n^(n+1))/(m^m + n^n)) : a^m + a^n ≥ m^m + n^n
:=by sorry


end Usa1991P4
