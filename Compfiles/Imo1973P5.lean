/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InternLM-MATH LEAN Formalizer v0.1
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 1973, Problem 5

$G$ is a set of non-constant functions of the real variable $x$ of the form \[f(x) = ax + b, a \text{ and } b \text{ are real numbers,}\] and $G$ has the following properties:
(a) If $f$ and $g$ are in $G$, then $g \circ f$ is in $G$; here $(g \circ f)(x) = g[f(x)]$.
(b) If $f$ is in $G$, then its inverse $f^{-1}$ is in $G$; here the inverse of $f(x) = ax + b$ is $f^{-1}(x) = (x - b) / a$.
(c) For every $f$ in $G$, there exists a real number $x_f$ such that $f(x_f) = x_f$.
Prove that there exists a real number $k$ such that $f(k) = k$ for all $f$ in $G$.
-/

namespace Imo1973P5

problem imo1973_p5 {G : Set (ℝ → ℝ)}
  (hf: ∀ f : ℝ → ℝ, f ∈ G → (∃ a b : ℝ, a ≠ 0 ∧ ∀ x : ℝ, f x = a * x + b))
  (hG : ∀ f g : ℝ → ℝ, f ∈ G ∧ g ∈ G → g ∘ f ∈ G)
  (hinv : ∀ f : ℝ → ℝ, f ∈ G → (∀ x, f x ≠ 0) → f⁻¹ ∈ G)
  (hfix : ∀ f : ℝ → ℝ, f ∈ G → ∃ x, f x = x) : ∃ k : ℝ, ∀ f : ℝ → ℝ, f ∈ G → f k = k := by sorry
