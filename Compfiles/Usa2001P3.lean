/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw, Hongyu Ouyang
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# USA Mathematical Olympiad 2001, Problem 3

Let a,b,c ≥ 0 be real numbers satsifying

        a² + b² + c² + abc = 4.

Show that

        0 ≤ ab + bc + ca - abc ≤ 2.
-/

namespace Usa2001P3

@[reducible]
def f (a b c : ℝ) : ℝ := a^2 + b^2 + c^2 + a * b * c
@[reducible]
def g (a b c : ℝ) : ℝ := a * b + b * c + c * a - a * b * c

theorem feq (a b c : ℝ) : f a b c = a^2 + b^2 + c^2 + a * b * c := rfl
theorem geq (a b c : ℝ) : g a b c = a * b + b * c + c * a - a * b * c := rfl

lemma usa2001_p3_lemma (a b c : ℝ) (ha : 0 ≤ a) (_hb : 0 ≤ b) (_hc : 0 ≤ c)
    (h : a^2 + b^2 + c^2 + a * b * c = 4)
    (hbc : (b - 1) * (c - 1) ≥ 0) :
    a * b + b * c + c * a - a * b * c ≤ 2 := by
  have eq1 := calc
    (2 + a) * (2 - a) = 4 - a ^ 2 := by ring_nf
    _ = a ^ 2 + b ^ 2 + c ^ 2 + a * b * c - a ^ 2 := by rw [h]
    _ = (b ^ 2 + c ^ 2) + a * b * c := by ring_nf
    _ ≥ 2 * b * c + a * b * c := by rel [two_mul_le_add_sq b c]
    _ = (2 + a) * (b * c) := by ring_nf
  have a2gt0 : 2 + a > 0 := by linarith
  have bc := (mul_le_mul_left a2gt0).mp eq1
  calc
    a * b + b * c + c * a - a * b * c = a * b + b * c + a * c * (1 - b) := by ring_nf
    _ ≤ a * b + (2 - a) + a * c * (1 - b) := by gcongr
    _ = 2 - a * ((b - 1) * (c - 1)) := by ring_nf
    _ ≤ 2 - 0 := by gcongr; positivity
    _ = 2 := by norm_num

problem usa2001_p3 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a^2 + b^2 + c^2 + a * b * c = 4) :
    0 ≤ a * b + b * c + c * a - a * b * c ∧
    a * b + b * c + c * a - a * b * c ≤ 2 := by
  rw [←feq] at h
  rw [←geq]
  wlog ha1 : a≤1 generalizing a b c with Ha
  · by_cases hb1 : b ≤ 1
    rw [(by ring_nf : g a b c = g b a c)]
    exact Ha b a c hb ha hc (by rw [←h]; unfold f; ring_nf) hb1
    by_cases hc1 : c ≤ 1
    rw [(by ring_nf : g a b c = g c b a)]
    exact Ha c b a hc hb ha (by rw [←h]; unfold f; ring_nf) hc1
    apply False.elim (ne_of_not_le _ h)
    unfold f
    rw [not_le]
    rw [not_le] at ha1 hb1 hc1
    rw [(by norm_num : ((4 : ℝ) = 1 ^ 2 + 1 ^ 2 + 1 ^ 2 + 1 * 1 * 1))]
    gcongr
  constructor
  · unfold g
    have : (1 - a ≥ 0) := by linarith
    have : a * b + b * c + c * a - a * b * c = a * b + b * c * (1 - a) + c * a := by ring_nf
    rw [this]
    positivity
  · wlog hb1 : b ≤ 1 generalizing b c with Hb
    · by_cases hc1 : c ≤ 1
      · rw [(by ring_nf : g a b c = g a c b)]
        exact Hb c b hc hb (by rw [←h]; unfold f; ring_nf) hc1
      · apply usa2001_p3_lemma a b c ha hb hc h
        have : (b - 1 > 0) := by linarith
        have : (c - 1 > 0) := by linarith
        rw [not_le] at hb1 hc1
        positivity
    · rw [(by ring_nf : g a b c = g c a b)]
      apply usa2001_p3_lemma c a b hc ha hb (by rw [←h]; unfold f; ring_nf)
      rw [(by ring_nf : (a - 1) * (b - 1) = (1 - a) * (1 - b))]
      have : (1 - a ≥ 0) := by linarith
      have : (1 - b ≥ 0) := by linarith
      positivity
