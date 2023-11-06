/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file

/-!
# International Mathematical Olympiad 2001, Problem 6

Let k,l,m,n be positive integers with k > l > m > n and

   km + ln = (k + l - m + n)(-k + l + m + n).

Prove that kl + mn is not prime.
-/

namespace Imo2001P6

problem imo2001_p6 (k l m n : ℤ)
    (hkp : 0 < k) (hlp : 0 < l) (hmp : 0 < m) (hnp : 0 < n)
    (hkl : l < k) (hlm : m < l) (hmn : n < m)
    (h : k * m + l * n = (k + l - m + n) * (-k + l + m + n)) :
    ¬Prime (k * l + m * n) := by
  sorry
