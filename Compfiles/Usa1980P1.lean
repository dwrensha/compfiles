/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import ProblemExtraction

@[expose] public section

problem_file {
  tags := [.Algebra]
}

/-!
# USA Mathematical Olympiad 1980, Problem 1

A balance has unequal arms and pans of unequal weight. It is used to weigh
two objects of unequal weight. The first object balances against a weight A,
when placed in the left pan and against a weight a, when placed in the right
pan. The corresponding weights for the second object are B and b. A third
object balances against a weight C, when placed in the left pan. What is its
true weight?
-/

namespace Usa1980P1

open Real

noncomputable determine solution (A a B b C : ℝ) : ℝ :=
  C * sqrt ((a - b) / (A - B)) +
    (b * A - a * B) / ((A - B) * (sqrt ((a - b) / (A - B)) + 1))

snip begin

/-
The effect of the unequal arms and the pans of unequal weight is that there
are fixed constants `h` and `k` with `0 < h` such that an object of true
weight `x` placed in the left pan balances a weight `y` placed in the right
pan if and only if `x = h * y + k`. The solution determines `h` and `k` from
the data of the first two objects and then reads off the true weight
`x₃ = h * C + k` of the third object.
-/

/-- The two objects have unequal weights, so the weights `A` and `B` that
balance them from the left pan must differ. -/
lemma ne_of_balance {A B h k x₁ x₂ : ℝ}
    (h1 : x₁ = h * A + k) (h3 : x₂ = h * B + k) (hne : x₁ ≠ x₂) :
    A ≠ B := by
  intro hAB
  exact hne (by rw [h1, h3, hAB])

/-- Eliminating the true weights `x₁` and `x₂` gives `a - b = h ^ 2 * (A - B)`. -/
lemma h_sq {A a B b h k x₁ x₂ : ℝ}
    (h1 : x₁ = h * A + k) (h2 : a = h * x₁ + k)
    (h3 : x₂ = h * B + k) (h4 : b = h * x₂ + k) :
    h ^ 2 * (A - B) = a - b := by
  rw [h1] at h2
  rw [h3] at h4
  linear_combination h4 - h2

/-- The offset `k` is determined by `(h + 1) * k = a - h ^ 2 * A`. -/
lemma offset_eq {A a h k x₁ : ℝ}
    (h1 : x₁ = h * A + k) (h2 : a = h * x₁ + k) :
    (h + 1) * k = a - h ^ 2 * A := by
  rw [h1] at h2
  linear_combination -h2

snip end

problem usa1980_p1 {A a B b C h k x₁ x₂ x₃ : ℝ} (hh : 0 < h)
    (h1 : x₁ = h * A + k) (h2 : a = h * x₁ + k)
    (h3 : x₂ = h * B + k) (h4 : b = h * x₂ + k)
    (h5 : x₃ = h * C + k) (hne : x₁ ≠ x₂) :
    x₃ = solution A a B b C := by
  have hAB : A ≠ B := ne_of_balance h1 h3 hne
  have e2 : h ^ 2 * (A - B) = a - b := h_sq h1 h2 h3 h4
  have e1 : (h + 1) * k = a - h ^ 2 * A := offset_eq h1 h2
  have hsq : (a - b) / (A - B) = h ^ 2 := by
    rw [div_eq_iff (sub_ne_zero.mpr hAB)]
    exact e2.symm
  have hsqrt : sqrt ((a - b) / (A - B)) = h := by
    rw [hsq]
    exact Real.sqrt_sq (le_of_lt hh)
  have hk_eq : k = (b * A - a * B) / ((A - B) * (h + 1)) := by
    have hh1 : h + 1 ≠ 0 := by linarith
    rw [eq_div_iff (mul_ne_zero (sub_ne_zero.mpr hAB) hh1)]
    linear_combination (A - B) * e1 - A * e2
  unfold solution
  rw [hsqrt, h5, hk_eq]
  ring

end Usa1980P1
