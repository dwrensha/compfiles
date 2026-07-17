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
# USA Mathematical Olympiad 1975, Problem 1
a) Prove that
$[5x]+[5y]\ge [3x+y]+[3y+x]$,

where $x,y\ge 0$ and $[u]$ denotes the greatest integer $\le u$ (e.g., $[\sqrt{2}]=1$).

(b) Using (a) or otherwise, prove that
$\frac{(5m)!(5n)!}{m!n!(3m+n)!(3n+m)!}$

is integral for all positive integral $m$ and $n$.
-/

namespace Usa1975P1

problem usa1975_p1a (x y: ℝ) (hx : x > 0) (hy : y > 0) : ⌊5*x⌋₊+⌊5*y⌋ ≥ ⌊3*x+y⌋ + ⌊3*y + x⌋ :=
by sorry

open scoped Nat

problem usa1975_p1b (m n : ℕ) : (m ! * n ! * (3*m+n) ! * (3*n+m) !) ∣ ((5*m)! * (5*n)!) := by sorry

end Usa1975P1
