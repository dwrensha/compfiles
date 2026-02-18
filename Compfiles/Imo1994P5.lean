/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InternLM-MATH LEAN Formalizer v0.1, David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

set_option backward.isDefEq.respectTransparency false

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
   (lt_div_iff₀ (show 0 < 1 + a by linarith)).mpr (by simp)

snip end

determine solution_set : Set (S → S) := { fun x ↦ ⟨-x.val / (1 + x.val), sol_prop x.property⟩ }

problem imo1994_p5 (f : S → S) :
    f ∈ solution_set ↔
    ((∀ x y : S, f (op f x y) = op f y x) ∧
     (∀ x y : S, x.val ∈ Set.Ioo (-1) 0 → y.val ∈ Set.Ioo (-1) 0 →
        x.val < y.val → (f x).val / x.val < (f y).val / y.val) ∧
     (∀ x y : S, 0 < x.val → 0 < y.val →
        x.val < y.val → (f x).val / x.val < (f y).val / y.val)) := by
  -- We follow https://prase.cz/kalva/imo/isoln/isoln945.html
  constructor
  · intro hf
    simp only [Set.mem_singleton_iff] at hf
    rw [hf]
    refine ⟨?_, ?_, ?_⟩ <;> rintro ⟨x, hx⟩ ⟨y, hy⟩
    · grind
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
    · simp only
      intro hx1 hy1 hxy
      have h1 : 0 < 1 + y := by positivity
      have h2 : 0 < 1 + x := by positivity
      have h5 : x ≠ 0 := by linarith
      have h6 : y ≠ 0 := by linarith
      simp only [div_div]
      rw [mul_comm, div_mul_eq_div_div, neg_div, div_self h5]
      rw [mul_comm, div_mul_eq_div_div]
      nth_rw 2 [neg_div]
      rw [div_self h6]
      rw [div_lt_div_iff₀ h2 h1]
      linarith
  rintro ⟨h1, h2, h3⟩
  simp only [Set.mem_singleton_iff]
  have h4 : ∀ a, f a = a → a = ⟨0, neg_one_lt_zero⟩ := by
    -- Suppose f(a) = a.
    intro a ha
    -- Then putting x = y = a in the relation given, we get f(b) = b, where b = 2a + a².
    have h1a := h1 a a
    dsimp only [op] at h1a
    simp_rw [ha] at h1a
    let b := a.val + a.val + a.val * a.val
    have hb : -1 < b := by unfold b; nlinarith [a.property]

    obtain haz | haz | haz := lt_trichotomy a.val 0
    · -- If -1 < a < 0, then -1 < b < a.
      have hai : a.val ∈ Set.Ioo (-1) 0 := ⟨a.property, haz⟩
      have hba : b < a.val := by
        unfold b
        nlinarith [a.property]
      have hbi : b ∈ Set.Ioo (-1) 0 := by
        refine ⟨hb, gt_trans haz hba⟩

      -- But f(a)/a = f(b)/b.
      have habf : (f a).val / a.val = (f ⟨b, hb⟩).val / b := by
        rw [ha]
        unfold b
        simp_rw [h1a]
        have haz : a.val ≠ 0 := by linarith
        have hbz : a.val + a.val + a.val * a.val ≠ 0 := by nlinarith [a.property]
        simp only [div_self haz]
        simp only [div_self hbz]
      -- Contradiction.
      specialize h2 ⟨b, hb⟩ a hbi hai hba
      order
    · obtain ⟨a, haa⟩ := a
      dsimp only at haz
      simp_rw [haz]
    · -- Similarly, if a > 0, then b > a, but f(a)/a = f(b)/b. Contradiction.
      have hai : a.val ∈ Set.Ioi 0 := haz
      have hba : a.val < b := by
        unfold b
        nlinarith

      have hbi : b ∈ Set.Ioi 0 := by
        simp only [Set.mem_Ioi]
        exact gt_trans hba haz

      -- But f(a)/a = f(b)/b.
      have habf : (f a).val / a.val = (f ⟨b, hb⟩).val / b := by
        rw [ha]
        unfold b
        simp_rw [h1a]
        have haz : a.val ≠ 0 := by positivity
        have hbz : a.val + a.val + a.val * a.val ≠ 0 := by positivity
        simp only [div_self haz]
        simp only [div_self hbz]

      specialize h3 a ⟨b, hb⟩ hai hbi hba
      order

  -- But putting x = y in the relation given we get f(k) = k for k = x + f(x) + xf(x).
  -- Hence for any x we have x + f(x) + xf(x) = 0.
  have h5 : ∀ x, op f x x = ⟨0, neg_one_lt_zero⟩ := by
    intro x
    exact h4 (op f x x) (h1 x x)

  ext x
  have h6 := h5 x
  unfold op at h6
  obtain ⟨x, hx⟩ := x
  rw [Subtype.mk_eq_mk] at h6
  dsimp only at h6
  have h7 : (f ⟨x, hx⟩).val = -x / (1 + x) := by
    have h8 : 0 < 1 + x := by linarith
    field_simp
    linarith
  rw [←Subtype.val_inj]
  dsimp only
  exact h7

end Imo1994P5
