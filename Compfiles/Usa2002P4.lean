/-
Copyright (c) 2025 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Chen
-/

import Mathlib.Tactic
import ProblemExtraction

problem_file {
  tags := [.Algebra]
  videos := ["https://youtu.be/JJubxpCN0fM"]
}

/-!
# USA Mathematical Olympiad 2002, Problem 4

Find all functions f : ℝ → ℝ such that for all x, y ∈ ℝ:
f(x² - y²) = x f(x) - y f(y).
-/

namespace Usa2002P4

def FE (f : ℝ → ℝ) : Prop :=
  ∀ x y, f (x^2 - y^2) = x * (f x) - y * (f y)

snip begin

-- Following https://web.evanchen.cc/exams/USAMO-2002-notes.pdf

-- f(0)=0
lemma f_zero {f : ℝ → ℝ} (hf : FE f):
    f 0 = 0 := by
  convert hf 0 0 <;> simp_all

-- f(x^2) = xf(x)
lemma squarish {f : ℝ → ℝ} (hf : FE f) (x : ℝ) :
    f (x^2) = x * f x := by
  have h := hf x 0
  rw [f_zero hf] at h
  simp_all

-- f(x^2) = f(x^2)-f(y^2)
lemma square_additive {f : ℝ → ℝ} (hf : FE f) (x : ℝ) (y : ℝ)  :
    f (x^2 - y^2) = f (x^2) - f (y^2) := by
  simp [squarish hf]
  apply hf

-- f is odd
lemma f_odd {f : ℝ → ℝ} (hf : FE f) (x : ℝ)  :
    -f x = f (-x) := by
  by_cases hx : x ≥ 0
  · have h := square_additive hf 0 (Real.sqrt x)
    simp_all [f_zero hf]
  · replace hx : - x ≥ 0 := by grind only
    have h := square_additive hf 0 (Real.sqrt (- x))
    simp_all [f_zero hf]

-- f(x+y) = f(x)+f(y) with x,y ≥ 0 first
lemma additive_pos {f : ℝ → ℝ} (hf : FE f) {x : ℝ} {y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y):
    f (x + y) = f x + f y := by
  have h := square_additive hf (Real.sqrt (x + y)) (Real.sqrt y)
  grind only [usr Real.sq_sqrt', = max_def]

-- Now show Cauchy FE holds with x,y not necessarily positive (lots of cases)
lemma additive {f : ℝ → ℝ} (hf : FE f) (x : ℝ) (y : ℝ)  :
    f (x + y) = f x + f y := by
  wlog hwlog : x ≤ y generalizing x y with H
  · have h := H y x
    simp [show y ≤ x by grind only] at h
    convert h using 1
    · rw [add_comm]
    · grind only
  by_cases hx : 0 ≤ x
  · exact additive_pos hf hx (show 0 ≤ y by grind only)
  · replace hx : 0 ≤ -x := by grind only
    by_cases hy : 0 ≤ y
    · by_cases hxy : 0 ≤ x + y
      · have h := additive_pos hf hxy hx
        rw [← f_odd hf] at h
        simp_all
      · have h := additive_pos hf (show 0 ≤ -(x+y) by grind only) hy
        simp at h
        rw [show -y+-x = -(x+y) by ring] at h
        rw [← f_odd hf x, ← f_odd hf (x+y)] at h
        linarith
    · have h := additive_pos hf hx (show 0 ≤ -y by grind only)
      rw [show -x+-y = -(x+y) by ring] at h
      rw [← f_odd hf x, ← f_odd hf y, ← f_odd hf (x+y)] at h
      linarith

-- Apply Cauchy four times to f
lemma four_additive {f : ℝ → ℝ} (hf : FE f) (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ) :
    f (a + b + c + d) = f a + f b + f c + f d := by
  have h1 := additive hf (a+b+c) d
  have h2 := additive hf (a+b) c
  have h3 := additive hf a b
  linarith

-- Show the FE implies f(x) = f(1)*x
lemma main_proof {f : ℝ → ℝ} (hf : FE f) (x : ℝ)  :
    f x = f 1 * x := by
  have h := squarish hf (x+1)
  rw [show (f (x+1)) = _ by exact additive hf x 1] at h
  rw [show (x+1)^2 = x^2 + x + x + 1 by ring] at h
  rw [four_additive hf] at h
  rw [squarish hf] at h
  grind only

snip end

determine solution_set : Set (ℝ → ℝ) := { f | ∃ c : ℝ, ∀ x, f x = c * x }

problem usa2002_p4 (f : ℝ → ℝ) :
    f ∈ solution_set ↔ FE f := by
  constructor
  · -- trivial direction: show that linear functions work
    unfold FE
    grind only [usr Set.mem_setOf_eq]
  · -- conversely, if f obeys the FE, then choose c = f(1)
    intro hf
    use (f 1) -- c = f(1)
    apply main_proof
    exact hf

end Usa2002P4
