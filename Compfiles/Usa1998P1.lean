/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# USA Mathematical Olympiad 1998, Problem 1

Suppose that the set { 1, 2, ..., 1998 } has been partitioned into disjoint
pairs {aᵢ, bᵢ}, where 1 ≤ i ≤ 999, so that for all i, |aᵢ - bᵢ| = 1 or 6.

Prove that the sum

  |a₁ - b₁| + |a₂ - b₂| + ... + |a₉₉₉ - b₉₉₉|

ends in the digit 9.
-/

namespace Usa1998P1

snip begin

lemma zmod_eq (a b c : ℤ) : a ≡ b [ZMOD c] ↔ a % c = b % c := by rfl

lemma mod2_abs (a : ℤ) : |a| % 2 = a % 2 := by
  cases' abs_cases a with h h <;> rw [h.1]
  rw [Int.neg_emod_two]

-- For integers M,N we have |M-N| ≡ M-N ≡ M+N MOD 2.
lemma mod2_diff (a b : ℤ) : |a - b| % 2 = (a + b) % 2 := by
  rw [mod2_abs, Int.sub_eq_add_neg, Int.add_emod, Int.neg_emod_two, ←Int.add_emod]

lemma lemma0 (n : ℕ) : (∑ x ∈ Finset.Icc 1 (4 * n + 2), (x:ℤ) % 2) % 2 = 1 := by
  norm_cast
  induction n with
  | zero => simp_arith
  | succ n ih =>
    rw [show 4 * (n + 1) + 2 = (4 * n + 2) + 4 by omega]
    rw [Finset.sum_Icc_succ_top (by norm_num)]
    rw [Finset.sum_Icc_succ_top (by norm_num)]
    rw [Finset.sum_Icc_succ_top (by norm_num)]
    rw [Finset.sum_Icc_succ_top (by norm_num)]
    omega

snip end

/--
 `ab 0 i` is aᵢ and `ab 1 i` is `bᵢ`
-/
problem usa1998_p1
    (ab : Fin 2 → Fin 999 → Finset.Icc 1 1998)
    (hab : (ab.uncurry).Bijective)
    (habd : ∀ i : Fin 999,
              |(ab 0 i : ℤ) - (ab 1 i : ℤ)| = 1 ∨
              |(ab 0 i : ℤ) - (ab 1 i : ℤ)| = 6) :
    (∑ i : Fin 999, |(ab 0 i : ℤ) - (ab 1 i : ℤ)|) % 10 = 9 := by
  -- Informal solution from
  -- https://artofproblemsolving.com/wiki/index.php/1998_USAMO_Problems/Problem_1
  -- Notice that |aᵢ-bᵢ| ≡ 1 MOD 5,
  have h1 : ∀ i : Fin 999, |(ab 0 i : ℤ) - ab 1 i| % 5 = 1 % 5 := fun i ↦ by
    cases' habd i with habd habd
    · rw [habd]
    · rw [habd]; rfl

  -- so S=|a₁-b₁|+|a₂-b₂|+ ⋯ +|a₉₉₉ - b₉₉₉| ≡ 1+1+ ⋯ + 1 ≡ 999 ≡ 4 MOD 5.
  have h2 : (∑ i : Fin 999, |ab 0 i - ab 1 i|) ≡ 4 [ZMOD 5] :=
  by rw [zmod_eq, Finset.sum_int_mod, Fintype.sum_congr _ _ h1]
     rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
     decide

  --
  -- Also, for integers M,N we have |M-N| ≡ M-N ≡ M+N MOD 2.
  -- (see mod2_diff above).
  --
  -- Thus, we also have
  -- S ≡ a₁ + b₁ + a₂ + b₂ + ⋯ + a₉₉₉ + b₉₉₉ [MOD 2]
  --   ≡ 1 + 2 + ⋯ + 1998 [MOD 2]
  --   ≡ 999*1999 ≡ 1 [MOD 2]
  have h3 : ∑ i : Fin 999, |(ab 0 i : ℤ) - ab 1 i| ≡ 1 [ZMOD 2] := by
    rw [zmod_eq, Finset.sum_int_mod]
    have h4 : ∀ i : Fin 999,
        |(ab 0 i : ℤ) - ab 1 i| % 2 = ((ab 0 i % 2) + (ab 1 i % 2)) % 2 := by
      intro i
      rw [mod2_diff, Int.add_emod]

    rw [Fintype.sum_congr _ _ h4, ←Finset.sum_int_mod, Finset.sum_add_distrib]

    have h9 : ∑ x : Fin 999, ((ab 0 x : ℤ) % 2) + ∑ x : Fin 999, ((ab 1 x : ℤ) % 2) =
         ∑ x : Fin 2 × Fin 999, (↑↑(ab.uncurry x) % 2) := by
      rw [← Fin.sum_univ_two (f := fun i ↦ ∑ x : Fin 999, ((ab i x : ℤ) % 2)),
          ← Finset.univ_product_univ, ← Finset.sum_product']
      rfl

    have h10 : ∑ x : Fin 2 × Fin 999, ((ab.uncurry x : ℤ) % 2) =
              ∑ x : Finset.Icc 1 1998, (x : ℤ) % 2 :=
      by apply Fintype.sum_bijective _ hab
         · exact congr_fun rfl
    rw [h9, h10]
    simp only [Finset.univ_eq_attach, Int.one_emod_two,
               Finset.sum_attach (Finset.Icc 1 1998) (fun (x:ℕ) => (x : ℤ) % 2)]
    rw [lemma0 499]

  -- Combining these facts gives S ≡ 9 MOD 10.
  have hmn : Nat.Coprime (Int.natAbs 2) (Int.natAbs 5) := by norm_cast
  rw [show (9:ℤ) = 9 % 10 by decide,
      ← zmod_eq,
      show (10:ℤ) = 2 * 5 by norm_num]

  rw [←Int.modEq_and_modEq_iff_modEq_mul hmn, zmod_eq, zmod_eq, h3, h2]
  decide

end Usa1998P1
