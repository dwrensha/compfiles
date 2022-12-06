import Mathlib.Algebra.Group.Defs

/-
 Russian Mathematical Olympiad 1998, problem 42

 A binary operation ⋆ on real numbers has the property that
 (a ⋆ b) ⋆ c = a + b + c.

 Prove that a ⋆ b = a + b.

-/

-- Mathlib4 does not have real numbers yet, so instead we work in an arbitrary
-- additive group R.

variable (R : Type) [AddGroup R] (star : R → R → R)
local infixl:80 " ⋆ " => star

theorem russia1998_q42
  (stardef : ∀ a b c, a ⋆ b ⋆ c = a + b + c) :
  (∀ a b, a ⋆ b = a + b) :=
by sorry
