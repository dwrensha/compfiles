/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Data.ZMod.Defs
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Algebra] }

/-!
# USA Mathematical Olympiad 2021, Problem 5

Let n ≥ 4 be an integer. Find all positive real solutions to the following
system of 2n equations:

  a₁ = 1/a₂ₙ + 1/a₂,
  a₂ = a₁ + a₃,
  a₃ = 1/a₂ + 1/a₄,
  a₄ = a₃ + a₅,
  a₅ = 1/a₄ + 1/a₆,
  a₆ = a₅ + a₇,
  ⋮
  a₂ₙ₋₁ = 1/a₂ₙ₋₂ + 1/a₂ₙ,
  a₂ₙ = a₂ₙ₋₁ + a₁.
-/

namespace Usa2021P5

snip begin

/-- Eliminating the odd-indexed variables from the system yields a relation
among the even-indexed variables alone:
`a k = 1 / a (k - 1) + 2 / a k + 1 / a (k + 1)`. -/
lemma even_relation {n : ℕ} {a b : ZMod n → ℝ}
    (h1 : ∀ k, a k = b k + b (k + 1))
    (h2 : ∀ k, b k = 1 / a (k - 1) + 1 / a k) (k : ZMod n) :
    a k = 1 / a (k - 1) + 2 / a k + 1 / a (k + 1) := by
  have e2 := h2 (k + 1)
  rw [add_sub_cancel_right] at e2
  conv_lhs => rw [h1 k, h2 k, e2]
  ring

snip end

/-- The unique solution of the system: the even-indexed terms equal `2` and the
odd-indexed terms equal `1`, i.e. `(a₁, a₂, a₃, a₄, …) = (1, 2, 1, 2, …)`.
The first component is the sequence of even-indexed terms and the second
component is the sequence of odd-indexed terms. -/
determine solution (n : ℕ) : (ZMod n → ℝ) × (ZMod n → ℝ) :=
  (fun _ => 2, fun _ => 1)

problem usa2021_p5 (n : ℕ) (hn : 4 ≤ n) (a b : ZMod n → ℝ)
    (ha : ∀ k, 0 < a k) (_hb : ∀ k, 0 < b k) :
    ((∀ k, a k = b k + b (k + 1)) ∧
     (∀ k, b k = 1 / a (k - 1) + 1 / a k)) ↔ (a, b) = solution n := by
  haveI : NeZero n := ⟨by omega⟩
  constructor
  · -- Suppose that `(a, b)` is a positive solution of the system.
    rintro ⟨h1, h2⟩
    -- Eliminate the odd-indexed variables.
    have key : ∀ k, a k = 1 / a (k - 1) + 2 / a k + 1 / a (k + 1) :=
      even_relation h1 h2
    -- Choose indices `i` and `j` where `a` attains its minimum resp. maximum.
    obtain ⟨i, -, hi⟩ := Finset.exists_min_image Finset.univ a
      (Finset.univ_nonempty_iff.mpr ⟨0⟩)
    obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ a
      (Finset.univ_nonempty_iff.mpr ⟨0⟩)
    have hmin : ∀ k, a i ≤ a k := fun k => hi k (Finset.mem_univ k)
    have hmax : ∀ k, a k ≤ a j := fun k => hj k (Finset.mem_univ k)
    -- The relation at `i` gives `2 / a i + 2 / a j ≤ a i` ...
    have hA : 2 / a i + 2 / a j ≤ a i := by
      have e1 := one_div_le_one_div_of_le (ha (i - 1)) (hmax (i - 1))
      have e2 := one_div_le_one_div_of_le (ha (i + 1)) (hmax (i + 1))
      calc 2 / a i + 2 / a j = 1 / a j + 2 / a i + 1 / a j := by ring
        _ ≤ 1 / a (i - 1) + 2 / a i + 1 / a (i + 1) :=
            add_le_add (add_le_add e1 (le_refl _)) e2
        _ = a i := (key i).symm
    -- ... while the relation at `j` gives `a j ≤ 2 / a i + 2 / a j`.
    have hB : a j ≤ 2 / a i + 2 / a j := by
      have e1 := one_div_le_one_div_of_le (ha i) (hmin (j - 1))
      have e2 := one_div_le_one_div_of_le (ha i) (hmin (j + 1))
      calc a j = 1 / a (j - 1) + 2 / a j + 1 / a (j + 1) := key j
        _ ≤ 1 / a i + 2 / a j + 1 / a i :=
            add_le_add (add_le_add e1 (le_refl _)) e2
        _ = 2 / a i + 2 / a j := by ring
    -- Hence `min = max`, so `a` is constant.
    have hEq : a i = a j := le_antisymm (hmin j) (hB.trans hA)
    have hconst : ∀ k, a k = a i := fun k =>
      le_antisymm ((hmax k).trans hEq.ge) (hmin k)
    -- The constant value `c` satisfies `c = 1 / c + 2 / c + 1 / c`, so `c = 2`.
    have k := key i
    rw [hconst (i - 1), hconst (i + 1)] at k
    have cne : a i ≠ 0 := ne_of_gt (ha i)
    have hsq : a i * a i = 4 := by
      field_simp at k
      linarith
    have hci : a i = 2 := by
      have h : a i ^ 2 = (2 : ℝ) ^ 2 := by rw [pow_two, pow_two, hsq]; norm_num
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h' | h'
      · exact h'
      · exfalso
        linarith [ha i]
    have ha2 : a = fun _ => 2 := funext fun k => (hconst k).trans hci
    -- And then `b k = 1 / 2 + 1 / 2 = 1` for every `k`.
    have hb1 : b = fun _ => 1 := by
      funext k
      rw [h2 k, ha2]
      norm_num
    rw [Prod.ext_iff]
    exact ⟨ha2, hb1⟩
  · -- Conversely, the claimed pair really is a solution.
    intro h
    obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp h
    constructor
    · intro k
      show (2 : ℝ) = 1 + 1
      norm_num
    · intro k
      show (1 : ℝ) = 1 / 2 + 1 / 2
      norm_num

end Usa2021P5
