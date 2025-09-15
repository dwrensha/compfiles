/-
Copyright (c) 2023 Gian Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Sanjaya
-/

import Mathlib.Algebra.Order.Positive.Field
import Mathlib.Tactic

import ProblemExtraction

problem_file {
  tags := [.Algebra],
  importedFrom :=
    "https://github.com/mortarsanjaya/imo-A-and-N/blob/main/src/IMO2008/A1/A1.lean",
}

/-!
# International Mathematical Olympiad 2008, Problem 4

Determine all functions f from the positive reals to the positive reals
such that

   (f(w)² + f(x)²) / (f(y)² + f(z)²) = (w² + x²) / (y² + z²)

for all positive real numbers w,x,y,z satisfying xw = yz.
-/

namespace Imo2008P4

abbrev PosReal : Type := { x : ℝ // 0 < x }

snip begin

lemma positive_pow_eq_pow
    {n : ℕ} (h : 0 < n) {a b : PosReal} : a ^ n = b ^ n ↔ a = b := by
  rw [← Subtype.coe_inj, Positive.val_pow, ← Subtype.coe_inj, Positive.val_pow]
  exact pow_left_inj₀ (le_of_lt a.2) (le_of_lt b.2) (Nat.ne_of_gt h)

-- In mathlib3, mul_two automatically worked on PosReal. In mathlib4 it does not.
-- See https://github.com/leanprover-community/mathlib4/blob/7cc262f36953b78637c096c4bc6634c2af0b2a0a/Mathlib/Algebra/Ring/Defs.lean#L176-L179.
lemma PosReal.mul_two (x : PosReal) : x * ⟨2, two_pos⟩ = x + x := by
  obtain ⟨x, hx⟩ := x
  rw [Subtype.ext_iff]
  simp [_root_.mul_two]

lemma PosReal.two_mul (x : PosReal) : ⟨2, two_pos⟩ * x = x + x := by
  obtain ⟨x, hx⟩ := x
  rw [Subtype.ext_iff]
  simp [_root_.two_mul]

snip end

determine solution_set : Set (PosReal → PosReal) := { f | f = id ∨ f = fun x ↦ 1 / x }

problem imo2008_p4 (f : PosReal → PosReal) :
    f ∈ solution_set ↔
      ∀ w x y z, w * x = y * z →
       ((f w)^2 + (f x)^2) * (y^2 + z^2) = (w^2 + x^2) * (f (y^2) + f (z^2)) := by
  refine ⟨fun h p q r s h0 ↦ ?_, fun h ↦ ?_⟩
  · rcases h with rfl | h'
    · rfl
    · have h : ∀ x, x * f x = 1 := fun x ↦ by simp [h']
      rw [← mul_right_inj (p ^ 2 * q ^ 2), ← mul_assoc, mul_add _ (f p ^ 2), mul_right_comm,
        ← mul_pow, h, mul_assoc, ← mul_pow q, h, one_pow, mul_one, one_mul, add_comm,
        mul_left_comm, mul_right_inj, ← mul_pow, h0, mul_pow, mul_add, mul_right_comm,
        h, one_mul, mul_assoc, h, mul_one, add_comm]
  · ---- Deduce `f(x^2) = f(x)^2` and `f(x) = x` or `x f(x) = 1`
    have h0 : ∀ x, f (x ^ 2) = f x ^ 2 := fun x ↦ by
      replace h := h x x x x rfl
      rwa [mul_comm, mul_right_inj, ←PosReal.two_mul, ←PosReal.two_mul,
           mul_right_inj, eq_comm] at h

    replace h := λ x y ↦ h (x ^ 2) (y ^ 2) (x * y) (x * y) (by rw [← sq, mul_pow])
    simp_rw [h0, ← PosReal.mul_two, ← mul_assoc, mul_left_inj, ← pow_mul, two_mul] at h
    replace h0 := h0 1
    rw [one_pow, sq, right_eq_mul] at h0
    have h1 : ∀ x, f x = x ∨ x * f x = 1 := by
      intro x; replace h := h x 1
      rw [mul_one, h0, one_pow, mul_comm, mul_add_one, add_one_mul, pow_add,
          pow_add, mul_assoc, ← mul_assoc, ← mul_pow, mul_comm] at h
      simp_rw [← Subtype.coe_inj, Positive.coe_add, Positive.val_mul] at h
      rw [← eq_sub_iff_add_eq, add_sub_right_comm, ← sub_eq_iff_eq_add, ← mul_sub_one,
          ← mul_sub_one, ← sub_eq_zero, ← sub_mul, mul_eq_zero] at h
      simp_rw [sub_eq_zero, Subtype.coe_inj, positive_pow_eq_pow two_pos] at h
      revert h; refine Or.imp_right (λ h ↦ ?_)
      rwa [eq_comm, ← Positive.val_one, Subtype.coe_inj,
           ← one_pow 2, eq_comm, positive_pow_eq_pow two_pos] at h

    ---- Finishing
    rw [Set.mem_setOf_eq, funext_iff]
    by_contra! h2
    rcases h2 with ⟨⟨a, h2⟩, bh3⟩
    have ⟨b, h3⟩ : ∃ b, b * f b ≠ 1 := by
      rw [@Function.ne_iff] at bh3
      obtain ⟨b, hb⟩ := bh3
      use b
      intro hbb
      apply_fun (· / b) at hbb
      rw [mul_div_cancel_left] at hbb
      contradiction
    have h4 := h1 b; rw [or_iff_left h3] at h4
    replace h := h a b; rw [h4] at h
    replace h4 := h1 (a * b)
    obtain h4 | h4 := h4
    · rw [h4, mul_left_inj, add_left_inj, show 2 + 2 = 4 by rfl] at h
      rw [positive_pow_eq_pow four_pos] at h
      exact h2 h

    replace h1 := h1 a
    dsimp at h2
    rw [or_iff_right h2] at h1
    rw [← mul_right_inj ((a * b) ^ 2), mul_left_comm _ _ (f _ ^ 2), ← mul_pow,
        h4, one_pow, mul_one, mul_comm _ ((a * b) ^ 2), ← mul_assoc, ← pow_add,
        mul_pow, mul_add, mul_right_comm, ← mul_pow, h1, one_pow, one_mul, add_comm,
        add_left_inj, ← mul_pow, ← mul_pow, show 2 + 2 = 4 by rfl,
        positive_pow_eq_pow four_pos, mul_assoc,
        mul_eq_left, ← sq, eq_comm, ← one_pow 2, positive_pow_eq_pow two_pos] at h

    apply h3; subst h; rw [one_mul, h0]


end Imo2008P4
