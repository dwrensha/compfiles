/-
Copyright (c) 2024 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongyu Ouyang
-/

import Lean.Parser.Tactic
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

import ProblemExtraction

open Lean.Parser.Tactic

problem_file { tags := [.Algebra, .Inequality] }

/-!
# USA Mathematical Olympiad 1974, Problem 2

Prove that if a, b, and c are positive real numbers, then
a^a * b^b * c^c ≥ (abc)^((a+b+c)/3)
-/

namespace Usa1974P2

snip begin

/-
if we have ⊢ a * x * y ≤ y * z * a
cancel_mul a do the following:
* move a to the right ⊢ x * y * a ≤ y * z * a
* gcongr ?_ * ?_      ⊢ x * y ≤ y * z    ∧     ⊢ a ≤ a
* swap ; rfl          ⊢ x * y ≤ y * z
note that gcongr can produce new goals x * y > 0 and y * z > 0 and a > 0, but luckily
in all our cases, gcongr can solve those by itself.
-/
syntax "cancel_mul" rwRuleSeq : tactic
macro_rules
  | `(tactic| cancel_mul [$rules,*]) => do
     let tacs ← rules.getElems.mapM fun rule =>
       `(tactic| (move_mul [$rule] ; gcongr ?_ * ?_ ; swap ; rfl))
     `(tactic| ($[$tacs]*))

lemma le_abcd : ∀ {a b c d : ℝ}, a > 0 → b > 0 → c > 0 → d > 0 → a * c ≤ b * d → d ≤ c → a ≤ b := by
  intro a b c d _ha hb hc _hd hacbd hcd
  apply le_of_mul_le_mul_of_pos_right _ hc
  trans b * d
  · assumption
  · simp only [mul_le_mul_left, hb, hcd]

lemma le_aabb_abba : ∀ {a b : ℝ}, a > 0 → b > 0 → a ≥ b → a ^ b * b ^ a ≤ a ^ a * b ^ b := by
  intro a b ha hb hab
  have da : a = a - b + b := by ring
  rw [(da ▸ rfl : a ^ a = a ^ (a - b + b))]
  rw [(da ▸ rfl : b ^ a = b ^ (a - b + b))]
  rw [Real.rpow_add ha]
  rw [Real.rpow_add hb]
  cancel_mul [b ^ b, a ^ b]
  apply Real.rpow_le_rpow
  · exact le_of_lt hb
  · assumption
  · apply sub_nonneg_of_le hab

lemma le_cabb_cbba : ∀ {a b c : ℝ}, a > 0 → b > 0 → c > 0 → a ≥ b → b ≥ c → c ^ a * b ^ b ≤ c ^ b * b ^ a := by
  intro a b c _ha hb hc hab hbc
  have da : a = a - b + b := by ring
  rw [da]
  rw [Real.rpow_add hc]
  rw [Real.rpow_add hb]
  cancel_mul [b ^ b, c ^ b]
  apply Real.rpow_le_rpow
  · exact le_of_lt hc
  · assumption
  · apply sub_nonneg_of_le hab

lemma le_acbb_bcab : ∀ {a b c : ℝ}, a > 0 → b > 0 → c > 0 → a ≥ b → b ≥ c → a ^ c * b ^ b ≤ b ^ c * a ^ b := by
  intro a b c ha hb _hc hab hbc
  have db : b = b - c + c := by ring
  rw [(db ▸ rfl : a ^ b = a ^ (b - c + c))]
  rw [(db ▸ rfl : b ^ b = b ^ (b - c + c))]
  rw [Real.rpow_add hb]
  rw [Real.rpow_add ha]
  cancel_mul [a ^ c, b ^ c]
  apply Real.rpow_le_rpow
  · exact le_of_lt hb
  · assumption
  · exact sub_nonneg_of_le hbc

lemma usa1974_p2_wlog :
    ∀ (a b c : ℝ), a > 0 → b > 0 → c > 0 → a ≥ b → b ≥ c → a^a * b^b * c^c ≥ (a*b*c)^((a+b+c)/3) := by
  intros a b c ha hb hc hab hbc
  have habc : a * b * c > 0 := Real.mul_pos (Real.mul_pos ha hb) hc
  have h : (a ^ a * b ^ b * c ^ c) * (a ^ b * b ^ c * c ^ a) * (a ^ c * b ^ a * c ^ b) = 
            (a * b * c) ^ (a + b + c) := by
    rw [Real.rpow_add]
    rw [Real.rpow_add]
    rw [Real.mul_rpow]
    rw [Real.mul_rpow]
    rw [Real.mul_rpow]
    rw [Real.mul_rpow]
    rw [Real.mul_rpow]
    rw [Real.mul_rpow]
    all_goals try positivity
    ring
  apply le_of_pow_le_pow_left (by decide : 3 ≠ 0) (by positivity)
  rw [←Real.rpow_nat_cast]
  rw [←(Real.rpow_mul (le_of_lt habc))]
  norm_num
  rw [←h]
  rw [pow_three']
  -- ⊢ a ^ a * b ^ b * c ^ c * (a ^ b * b ^ c * c ^ a) * (a ^ c * b ^ a * c ^ b) ≤
  --   a ^ a * b ^ b * c ^ c * (a ^ a * b ^ b * c ^ c) * (a ^ a * b ^ b * c ^ c)
  gcongr ?_ * ?_ * ?_
  · rfl
  · apply le_abcd _ _ _ _ _ (le_aabb_abba hb hc hbc) <;> try positivity
    apply le_abcd _ _ _ _ _ (le_aabb_abba ha hb hab) <;> try positivity
    cancel_mul [b ^ b, c ^ c, a ^ a, a ^ b, b ^ c]
    exact le_cabb_cbba ha hb hc hab hbc
  · apply le_abcd _ _ _ _ _ (le_aabb_abba hb hc hbc) <;> try positivity
    apply le_abcd _ _ _ _ _ (le_aabb_abba ha hb hab) <;> try positivity
    cancel_mul [b ^ b, c ^ c, a ^ a, b ^ a, c ^ b]
    exact le_acbb_bcab ha hb hc hab hbc

snip end

problem usa1974_p2 :
    ∀ (a b c : ℝ), a > 0 → b > 0 → c > 0 → a^a * b^b * c^c ≥ (a*b*c)^((a+b+c)/3) := by
  -- solution from
  -- https://artofproblemsolving.com/wiki/index.php/1974_USAMO_Problems/Problem_2
  intros a b c ha hb hc
  wlog hab : a ≥ b with Hab
  · move_add [←b]; move_mul [←b^b, ←b]
    refine Hab b a c hb ha hc (le_of_lt $ not_le.mp hab)
  · wlog hac : a ≥ c with Hac
    · move_add [←c]; move_mul [←c^c, ←c]
      have hca : c ≥ a := le_of_lt $ not_le.mp hac
      apply Hac c a b <;> try assumption
      trans a <;> assumption
    · wlog hbc : b ≥ c with Hbc
      · move_add [b]; move_mul [b^b, b]
        have hcb : c ≥ b := le_of_lt $ not_le.mp hbc
        apply Hbc a c b <;> try assumption
      · exact usa1974_p2_wlog a b c ha hb hc hab hbc
