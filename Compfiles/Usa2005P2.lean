/-
Copyright (c) 2024 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

set_option backward.isDefEq.respectTransparency false

problem_file { tags := [.NumberTheory] }

/-!
# USA Mathematical Olympiad 2005, Problem 2

Prove that there do not exist integers x,y,z such that

        x⁶ + x³ + x³y + y = 147¹⁵⁷
        x³ + x³y + y² + y + z⁹ = 157¹⁴⁷.
-/

namespace Usa2005P2

snip begin

lemma lemma1 (x : ZMod 13) :
    x^3 = 0 ∨ x^3 = 1 ∨ x^3 = -1 ∨ x^3 = 5 ∨ x^3 = -5 := by
  reduce_mod_char
  fin_cases x <;> decide

snip end

problem usa2005_p2 :
    ¬∃ (x y z : ℤ),
       x^6 + x^3 + x^3 * y + y = 147^157 ∧
       x^3 + x^3 * y + y^2 + y + z^9 = 157^147 := by
  -- we follow
  -- https://artofproblemsolving.com/wiki/index.php/2005_USAMO_Problems/Problem_2
  push_neg
  intro x' y' z' h1 h2
  with_reducible generalize hM : ((147:ℤ) ^ 157) = M at h1
  with_reducible generalize hN : ((157:ℤ) ^ 147) = N at h2
  -- move into zmod 13
  apply_fun (fun x : ℤ ↦ (x : ZMod 13)) at h1 h2
  push_cast at h1 h2
  generalize (x' : ZMod 13) = x at *
  generalize (y' : ZMod 13) = y at *
  generalize (z' : ZMod 13) = z at *
  clear! x' y' z'
  rw [←hM] at h1; rw [←hN] at h2
  have h3 : (x^3 + y + 1)^2 + z^9 = 147^157 + 157^147 + 1 := by
    linear_combination h1 + h2
  have h4 : (x^3 + 1) * (x^3 + y) = 147^157 := by linear_combination h1
  reduce_mod_char at h3 h4
  have h7 : x^3 ≠ -1 := by
    by_contra! H
    rw [H] at h4
    norm_num at h4
    simp +arith +decide at h4
  have h8 : x^3 + y = 4 ∨ x^3 + y = 2 ∨ x^3 + y = 5 ∨ x^3 + y = -1 := by
    obtain h5 | h5 | h5 | h5 | h5 := lemma1 x
    · rw [h5] at h4 ⊢
      left
      linear_combination h4
    · rw [h5] at h4 ⊢
      right; left
      have h10 : 2 * (1 + y) = 2 * 2 := by linear_combination h4
      apply_fun (· * 7) at h10
      have h11 : 2 * (1 + y) * 7 = 14 * (1 + y) := by ring
      rw [h11] at h10
      reduce_mod_char at h10
      exact h10
    · exact (h7 h5).elim
    · rw [h5] at h4 ⊢
      have h10 : 6 * (5 + y) = 4 := by linear_combination h4
      apply_fun (11 * ·) at h10
      have h11 : 11 * (6 * (5 + y)) = 66 * (5 + y) := by ring
      rw [h11] at h10
      reduce_mod_char at h10
      right; right; left
      exact h10
    · rw [h5] at h4 ⊢
      have h10 : (-4) * (-5 + y) = 4 := by linear_combination h4
      apply_fun (3 * ·) at h10
      have h11 : 3 * ((-4) * (-5 + y)) = (-12) * (-5 + y) := by ring
      rw [h11] at h10
      right; right; right
      reduce_mod_char at h10 ⊢
      exact h10
  have h6 := lemma1 (z^3)
  rw [show (z^3)^3 = z^9 by ring] at h6
  obtain h9 | h9 | h9 | h9 := h8
      <;> obtain h6 | h6 | h6 | h6 | h6 := h6
      <;> simp (config := { decide := true }) [h6, h9] at h3


end Usa2005P2
