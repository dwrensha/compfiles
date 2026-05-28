/-
Copyright (c) 2025 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shalev Wengrowsky
-/

import Mathlib.Probability.Distributions.Uniform

import ProblemExtraction

problem_file { tags := [.Combinatorics, .NumberTheory] }

/-!
# USA Mathematical Olympiad 1972, Problem 3

A random number selector can only select one of the nine integers 1, 2, ..., 9,
and it makes these selections with equal probability. Determine the probability
that after n selections, where n > 1, the product of the n numbers selected will
be divisible by 10.
-/

namespace Usa1972P3

abbrev Digit := Fin 9
abbrev DigitSeq (n : ℕ) := Fin n → Digit

noncomputable def unifDistN (n : ℕ) := PMF.uniformOfFintype (DigitSeq n)


def to_nat_digit : Digit → ℕ := fun d ↦ d + 1
def is_good_seq {n : ℕ} (s : DigitSeq n) := 10 ∣ ∏a, to_nat_digit (s a)
def good_seqs {n : ℕ} := {s : DigitSeq n | is_good_seq s}

noncomputable determine solution (n : ℕ) : ENNReal :=
  1 + (4 / 9) ^ n - (8 / 9) ^ n - (5 / 9) ^ n

problem usa1972_p3 (n : ℕ) (_hn : 1 < n) :
  (unifDistN n).toOuterMeasure good_seqs = solution n := sorry

end Usa1972P3
