import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# IMO 1961 P2

Let $a, b, c$ be the sides of a triangle, and $T$ its area. Prove:
$$ a^2 + b^2 + c^2 \ge 4\sqrt{3} T $$
Equality holds if and only if the triangle is equilateral.

Weitzenböck's Inequality.

Authors:　lean-tom (with assistance from Gemini)

-/

namespace Imo1961P2

-- snip begin
/-!
## Proof strategy

We use Heron's formula to express the area $T$ in terms of the sides $a, b, c$.
The inequality is then equivalent to the algebraic inequality:
$$(a^2 + b^2 + c^2)^2 \ge 48 T^2$$
Substituting Heron's formula leads to a sum of squares identity.
-/


/--
Helper lemma: The key algebraic identity for Weitzenböck's inequality.
(a^2 + b^2 + c^2)^2 - 48 T^2 = 2((a^2-b^2)^2 + (b^2-c^2)^2 + (c^2-a^2)^2)
-/
lemma weitzenbock_identity (a b c T : ℝ)
    (h_area : 16 * T^2 = (a + b + c) * (a + b - c) * (a - b + c) * (-a + b + c)) :
    (a^2 + b^2 + c^2)^2 - 48 * T^2 =
    2 * ((a^2 - b^2)^2 + (b^2 - c^2)^2 + (c^2 - a^2)^2) := by
  have h48T : 48 * T^2 = 3 * (16 * T^2) := by ring
  rw [h48T, h_area]
  ring
/- snip end -/

/--
**IMO 1961 P2 (Inequality)**:
Using Heron's formula to characterize the area $T$, we prove the inequality.
-/
theorem imo1961_p2 (a b c T : ℝ)
    (h_pos_a : 0 < a) (h_pos_b : 0 < b) (h_pos_c : 0 < c)
    (h_area : 16 * T^2 = (a + b + c) * (a + b - c) * (a - b + c) * (-a + b + c)) :
    a^2 + b^2 + c^2 ≥ 4 * Real.sqrt 3 * T := by
  -- Convert to squared form
  apply nonneg_le_nonneg_of_sq_le_sq
  · positivity
  · ring_nf
    rw [Real.sq_sqrt (by norm_num)]
    ring_nf
    -- Use the algebraic identity
    have key_ident := weitzenbock_identity a b c T h_area
    -- Pass to nlinarith with the identity and non-negativity of squares
    linarith [key_ident, sq_nonneg (a^2 - b^2), sq_nonneg (b^2 - c^2), sq_nonneg (c^2 - a^2)]

/--
**IMO 1961 P2 (Equality Case)**:
Equality holds if and only if $a=b=c$.
-/
theorem imo1961_p2_eq_iff (a b c T : ℝ)
    (h_pos_a : 0 < a) (h_pos_b : 0 < b) (h_pos_c : 0 < c) (h_pos_T : 0 < T)
    (h_area : 16 * T^2 = (a + b + c) * (a + b - c) * (a - b + c) * (-a + b + c)) :
    a^2 + b^2 + c^2 = 4 * Real.sqrt 3 * T ↔ a = b ∧ b = c := by
  constructor
  · -- (→) If equality holds, then a=b=c
    intro h_eq
    have key_ident := weitzenbock_identity a b c T h_area
    -- Square the hypothesis
    have h_sq : (a^2 + b^2 + c^2)^2 = 48 * T^2 := by
      rw [h_eq, mul_pow, mul_pow, Real.sq_sqrt (by norm_num)]; ring
    -- Combine with identity
    rw [h_sq, sub_self] at key_ident
    symm at key_ident
    -- 2 * SumOfSquares = 0 implies each square is 0
    rcases (mul_eq_zero.mp key_ident) with (contra | h_sum)
    · norm_num at contra
    · rw [add_eq_zero_iff_of_nonneg (by positivity) (by positivity)] at h_sum
      rcases h_sum with ⟨h_ab_bc, h_ca⟩
      rw [add_eq_zero_iff_of_nonneg (by positivity) (by positivity)] at h_ab_bc
      rcases h_ab_bc with ⟨h_ab, h_bc⟩
      -- Extract a=b and b=c
      have ha : a = b := by
        rw [sq_eq_zero_iff, sub_eq_zero, sq_eq_sq_iff_eq_or_eq_neg] at h_ab
        cases h_ab <;> [assumption; linarith]
      have hb : b = c := by
        rw [sq_eq_zero_iff, sub_eq_zero, sq_eq_sq_iff_eq_or_eq_neg] at h_bc
        cases h_bc <;> [assumption; linarith]
      exact ⟨ha, hb⟩

  · -- (←) If a=b=c, then equality holds
    rintro ⟨rfl, rfl⟩
    -- Prove (3a^2)^2 = (4√3 T)^2
    ring_nf
    suffices (a^2 * 3)^2 = (√3 * T * 4)^2 by
      refine (sq_eq_sq_iff_eq_or_eq_neg.mp this).resolve_right ?_
      intro h_contra
      have : 0 < 3 * a^2 := by positivity
      have : 4 * Real.sqrt 3 * T > 0 := by positivity
      linarith
    -- Calculation
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by norm_num)]
    ring_nf
    ring_nf at h_area
    calc
      a ^ 4 * 9 = (a ^ 4 * 3) * 3  := by ring
      _         = (T^2 * 16) * 3   := by rw [h_area]
      _         = T ^ 2 * 48       := by ring

end Imo1961P2