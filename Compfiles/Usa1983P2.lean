/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pacmanboss256
-/

module

public import Mathlib.Tactic

public import Mathlib.Analysis.MeanInequalitiesPow

public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Algebra] }

/-!
# USA Mathematical Olympiad 1983, Problem 2

Prove that the zeros of

\[x^5+ax^4+bx^3+cx^2+dx+e=0\]

cannot all be real if $2a^2<5b$.
-/

namespace Usa1983P2
open Polynomial

snip begin
/- follows https://artofproblemsolving.com/wiki/index.php/1983_USAMO_Problems/Problem_2 -/
/- vieta formulas for a and b only, done very similarly to `Usa2014P1.lean` -/
lemma vieta {a b c d e : ℝ} {x : Fin 5 → ℝ}
  (hp: ((X - C (x 0)) * (X - C (x 1)) * (X - C (x 2)) * (X - C (x 3)) * (X - C (x 4))
    = X^5 + C a * X^4 + C b * X^3 + C c * X^2 + C d * X + C e)) :
    a = - ((x 0) + (x 1) + (x 2) + (x 3) + (x 4)) ∧
    b = (x 0)*(x 1) + (x 0)*(x 2) + (x 0)*(x 3) + (x 0)*(x 4)
      + (x 1)*(x 2) + (x 1)*(x 3) + (x 1)*(x 4)
      + (x 2)*(x 3) + (x 2)*(x 4) + (x 3)*(x 4)
      := by
  constructor
  · apply_fun (derivative^[4] · |>.eval 0) at hp
    linear_combination ( norm := (simp; ring) ) - hp / 24
  · apply_fun (derivative^[3] · |>.eval 0) at hp
    linear_combination ( norm := (simp; ring) ) - hp / 6

theorem ineqs (a b c d e : ℝ) (x : Fin 5 → ℝ)
  (hp: ((X - C (x 0)) * (X - C (x 1)) * (X - C (x 2)) * (X - C (x 3)) * (X - C (x 4))
    = X^5 + C a * X^4 + C b * X^3 + C c * X^2 + C d * X + C e)) :
      2*b ≤ (4*a^2)/5 := by
  obtain ⟨rfl, rfl⟩ := vieta hp
  calc
    _ = (x 0 + x 1 + x 2 + x 3 + x 4)^2 - ((x 0)^2 + (x 1)^2 + (x 2)^2 + (x 3)^2 + (x 4)^2) := by ring
    _ ≤ _ - (x 0 + x 1 + x 2 + x 3 + x 4) ^ 2 / 5 := by
      rw [sub_le_sub_iff_left, div_le_iff₀ (Nat.ofNat_pos : (0 : ℝ) < 5)]
      simpa [Finset.sum_range_succ, Fin.ofNat]
        using Finset.sum_mul_sq_le_sq_mul_sq (Finset.range 5) (x <| Fin.ofNat 5 ·) (fun _ ↦ (1 : ℝ))
    _ ≤ _ := by linarith

snip end

problem usa1983_p2 (a b c d e : ℝ) (x : Fin 5 → ℝ):
    2*a^2 < 5*b → ¬(((X - C (x 0)) * (X - C (x 1)) * (X - C (x 2)) * (X - C (x 3)) * (X - C (x 4))
    = X^5 + C a * X^4 + C b * X^3 + C c * X^2 + C d * X + C e)) := by
  contrapose!
  intro hp
  have h1 := ineqs a b c d e x hp
  linarith

end Usa1983P2
