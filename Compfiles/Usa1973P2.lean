/-
Copyright (c) 2025 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shalev Wengrowsky
-/

import Mathlib.Data.Nat.Basic

import ProblemExtraction

problem_file { tags := [.Algebra, .NumberTheory] }

/-!
# USA Mathematical Olympiad 1973, Problem 2

The sequence an is defined by a1 = a2 = 1, an+2 = an+1 + 2an.
The sequence bn is defined by b1 = 1, b2 = 7, bn+2 = 2bn+1 + 3bn.

Show that the only integer in both sequences is 1.
-/

namespace Usa1973P2

-- reindexed to start at 0
def a : ℕ → ℕ
| 0 => 1
| 1 => 1
| n + 2 => a (n + 1) + 2 * a n

def b : ℕ → ℕ
| 0 => 1
| 1 => 7
| n + 2 => 2 * b (n + 1) + 3 * b n

problem usa1973_p2 (n m : ℕ) (h : a n = b m): a n = 1 := sorry
