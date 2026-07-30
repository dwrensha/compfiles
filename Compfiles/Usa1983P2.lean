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
/-follows https://artofproblemsolving.com/wiki/index.php/1983_USAMO_Problems/Problem_2-/
/-vieta formulas for a and b only, done very similarly to `Usa2014P1.lean`-/
lemma vieta (a b c d e : ℝ) (x : Fin 5 → ℝ)
  (hp: ((X - C (x 0)) * (X - C (x 1)) * (X - C (x 2)) * (X - C (x 3)) * (X - C (x 4))
    = X^5 + C a * X^4 + C b * X^3 + C c * X^2 + C d * X + C e)) :
    a = - ((x 0) + (x 1) + (x 2) + (x 3) + (x 4)) ∧
    b = (x 0)*(x 1) + (x 0)*(x 2) + (x 0)*(x 3) + (x 0)*(x 4)
      + (x 1)*(x 2) + (x 1)*(x 3) + (x 1)*(x 4)
      + (x 2)*(x 3) + (x 2)*(x 4) + (x 3)*(x 4)
      := by

      constructor
      · apply_fun (·.derivative.derivative.derivative.derivative.eval 0) at hp
        simp_all
        ring_nf at hp
        rw [neg_eq_zero_sub] at hp
        linarith
      apply_fun (·.derivative.derivative.derivative.eval 0) at hp
      simp at hp
      ring_nf at hp
      linarith

theorem ineqs (a b c d e : ℝ) (x : Fin 5 → ℝ)
  (hp: ((X - C (x 0)) * (X - C (x 1)) * (X - C (x 2)) * (X - C (x 3)) * (X - C (x 4))
    = X^5 + C a * X^4 + C b * X^3 + C c * X^2 + C d * X + C e)) :
      2*b ≤ (4*a^2)/5 := by
        have ⟨ha,hb⟩ := vieta a b c d e x hp
        have ha_sq : ((x 0) + (x 1) + (x 2) + (x 3) + (x 4))^2 = a^2 := by rw [ha]; ring_nf
        rw [hb]
        repeat rw [mul_add]
        rw [(show  2 * (x 0 * x 1) + 2 * (x 0 * x 2) + 2 * (x 0 * x 3) + 2 * (x 0 * x 4) + 2 * (x 1 * x 2) +
          2 * (x 1 * x 3) + 2 * (x 1 * x 4) + 2 * (x 2 * x 3) + 2 * (x 2 * x 4) + 2 * (x 3 * x 4)
          = ((x 0) + (x 1) + (x 2) + (x 3) + (x 4))^2 - ((x 0)^2 + (x 1)^2 + (x 2)^2 + (x 3)^2 + (x 4)^2)
          by ring_nf)]
        rw [ha_sq]

        have cauchy_schwarz: a ^ 2 - (1+1+1+1+1)*(x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 + x 4 ^ 2)/5 ≤ a^2 - ((x 0) + (x 1) + (x 2) + (x 3) + (x 4))^2 /5 := by
          rw [sub_le_sub_iff_left]
          have left_sum: (x 0 + x 1 + x 2 + x 3 + x 4) ^ 2 = (∑i ∈ Finset.range 5, 1 * (x (Fin.ofNat 5 i)))^2 := by
            simp [Finset.sum, Fin.ofNat]
            simp [add_comm]
            nth_rw 4 [add_comm]

          have right_sum : (1 + 1 + 1 + 1 + 1) * (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 + x 4 ^ 2) / 5 =
            (∑i ∈ Finset.range 5, 1) * (∑i ∈ Finset.range 5, (x (Fin.ofNat 5 i))^2)/5 := by
              simp [Finset.sum, Fin.ofNat]
              repeat rw [← add_assoc]
              field_simp
              simp [add_comm]
              repeat rw [← add_assoc]


          rw [left_sum, right_sum]

          let f : ℕ → ℝ := fun k ↦ (x (Fin.ofNat 5 k))
          let g : ℕ → ℝ := fun _ ↦ (1 : ℝ)
          have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range 5) f g
          dsimp only [f, g] at hcs
          simp [Finset.sum, Fin.ofNat]
          repeat rw [← add_assoc]
          simp [Finset.sum, Fin.ofNat] at hcs
          repeat rw [← add_assoc] at hcs
          rw [div_le_div_iff_of_pos_right, mul_comm]
          · apply hcs
          linarith

        have : a ^ 2 - (x 0 + x 1 + x 2 + x 3 + x 4) ^ 2 / 5 ≤ 4 * a^2/5 := by
          rw [ha_sq]
          ring_nf
          rfl
        linarith

snip end

problem usa1983_p2 (a b c d e : ℝ)(x : Fin 5 → ℝ):
    2*a^2 < 5*b → ¬(((X - C (x 0)) * (X - C (x 1)) * (X - C (x 2)) * (X - C (x 3)) * (X - C (x 4))
    = X^5 + C a * X^4 + C b * X^3 + C c * X^2 + C d * X + C e)) := by
  contrapose!
  intro hp
  have h1 := ineqs a b c d e x hp
  linarith

end Usa1983P2
