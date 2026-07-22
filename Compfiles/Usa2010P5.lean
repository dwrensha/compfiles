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
# USA Mathematical Olympiad 2010, Problem 5
Let $q = \dfrac{3p-5}{2}$ where $p$ is an odd prime, and let

\[S_q = \frac{1}{2\cdot 3 \cdot 4} + \frac{1}{5\cdot 6 \cdot 7} + \cdots + \frac{1}{q\cdot (q+1) \cdot (q+2)}.\]

Prove that if $\dfrac{1}{p}-2S_q = \dfrac{m}{n}$ for integers $m$ and $n$, then $m-n$ is divisible by $p$.
-/

namespace Usa2010P5

open Finset

problem usa2010_p5 (p q: ℕ) (hpp : Nat.Prime p) (hpo : Odd p) (hq : q = (3*p-5)/2)
 (S : (ℕ -> ℚ) := fun n ↦ ∑ k ∈ Finset.Icc 2 n, 1/(k*(k+1)*(k+2))) :
  ∃ (m n : ℕ), (1/p) - (2 * S (q)) = m/n → p ∣ (m-n) := by
  sorry
end Usa2010P5
