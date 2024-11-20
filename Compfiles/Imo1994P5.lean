/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InternLM-MATH LEAN Formalizer v0.1, David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 1994, Problem 5

Let S be the set of all real numbers greater than -1.
Find all functions f : S→S such that f(x + f(y) + xf(y)) = y + f(x) + yf(x)
for all x and y, and f(x)/x is strictly increasing on each of the
intervals -1 < x < 0 and 0 < x.
-/

namespace Imo1994P5

def S := { x : ℝ // -1 < x }

abbrev op (f : S → S) (a b : S) : S :=
  ⟨a.val + (f b).val + a.val * (f b).val, by nlinarith [a.property, (f b).property]⟩

snip begin

lemma sol_prop {a : ℝ} (ha : -1 < a) : -1 < -a / (1 + a) :=
   (lt_div_iff₀ (show 0 < 1 + a by linarith)).mpr (by linarith)

snip end

determine solution_set : Set (S → S) := { fun x ↦ ⟨-x.val / (1 + x.val), sol_prop x.property⟩ }

problem imo1994_p5 (f : S → S) :
    f ∈ solution_set ↔
    ((∀ x y : S, f (op f x y) = op f y x) ∧
     (∀ x y : S, x.val ∈ Set.Ioo (-1) 0 → y.val ∈ Set.Ioo (-1) 0 →
        x.val < y.val → (f x).val / x.val < (f y).val / y.val) ∧
     (∀ x y : S, 0 < x.val → 0 < y.val →
        x.val < y.val → (f x).val / x.val < (f y).val / y.val)) := by
  constructor
  · intro hf
    simp only [Set.mem_singleton_iff] at hf
    rw [hf]
    refine ⟨?_, ?_, ?_⟩ <;> rintro ⟨x, hx⟩ ⟨y, hy⟩
    · simp only [neg_add_rev, op]
      rw [Subtype.mk_eq_mk]
      have h1 : 0 < 1 + y := by linarith
      have h2 : 0 < 1 + x := by linarith
      have h3 : 0 < 1 + y + (x * (1 + y) + -y + -(x * y)) := by linarith
      field_simp
      nlinarith
    · simp only [Set.mem_Ioo, and_imp]
      intro hx1 hx2 hy1 hy2 hxy
      have h1 : 0 < 1 + y := by linarith
      have h2 : 0 < 1 + x := by linarith
      have h5 : x ≠ 0 := by linarith
      have h6 : y ≠ 0 := by linarith
      simp only [div_div]
      rw [mul_comm, div_mul_eq_div_div, neg_div, div_self h5]
      rw [mul_comm, div_mul_eq_div_div]
      nth_rw 2 [neg_div]
      rw [div_self h6]
      rw [div_lt_div_iff₀ h2 h1]
      linarith
    · simp only [Set.mem_Ioo, and_imp]
      intro hx1 hy1 hxy
      have h1 : 0 < 1 + y := by linarith
      have h2 : 0 < 1 + x := by linarith
      have h5 : x ≠ 0 := by linarith
      have h6 : y ≠ 0 := by linarith
      simp only [div_div]
      rw [mul_comm, div_mul_eq_div_div, neg_div, div_self h5]
      rw [mul_comm, div_mul_eq_div_div]
      nth_rw 2 [neg_div]
      rw [div_self h6]
      rw [div_lt_div_iff₀ h2 h1]
      linarith
  sorry

end Imo1994P5
