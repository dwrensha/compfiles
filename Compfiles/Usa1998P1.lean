/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

import ProblemExtraction

problem_file

/-!
# USA Mathematical Olympiad 1998, Problem 1

Suppose that the set { 1, 2, ..., 1998 } has been partitioned into disjoint
pairs {aᵢ, bᵢ}, where 1 ≤ i ≤ 999, so that for all i, |aᵢ - bᵢ| = 1 or 6.

Prove that the sum

  |a₁ - b₁| + |a₂ - b₂| + ... + |a₉₉₉ - b₉₉₉|

ends in the digit 9.
-/

namespace Usa1998P1
open BigOperators

snip begin

lemma zmod_eq (a b c : ℤ) : a ≡ b [ZMOD c] ↔ a % c = b % c := by rfl

lemma mod2_abs (a : ℤ) : |a| % 2 = a % 2 := by
  cases' abs_cases a with h h <;> rw [h.1]
  rw [Int.neg_emod_two]

-- For integers M,N we have |M-N| ≡ M-N ≡ M+N MOD 2.
lemma mod2_diff (a b : ℤ) : |a - b| % 2 = (a + b) % 2 := by
  rw [mod2_abs, Int.sub_eq_add_neg, Int.add_emod, Int.neg_emod_two, ←Int.add_emod]

lemma lemma0 (n : ℕ) :
    (∑ x in (Finset.Ioc (4 * n + 2) (4 * n.succ + 2)), (x:ℤ) % 2) % 2 = 0 := by
  have h1 : 4 * n.succ + 2 = 4 * n + 2 + 1 + 1 + 1 + 1 := by linarith
  rw [h1]
  rw [Finset.sum_Ioc_succ_top (by norm_num), Finset.sum_Ioc_succ_top (by norm_num),
      Finset.sum_Ioc_succ_top (by norm_num), Finset.sum_Ioc_succ_top (by norm_num),
      Finset.Ioc_self, Finset.sum_empty, zero_add]
  norm_cast
  simp [Nat.add_mod, Nat.mul_mod]
  norm_num

lemma lemma1 (n : ℕ) :
    (∑ x in Finset.attach (Finset.Icc 1 (4 * n + 2)), ((x:ℕ):ℤ) % 2) % 2 = 1 % 2 := by
 induction' n with n ih
 · decide
 · rw [Finset.sum_attach (f := fun x ↦ (x:ℤ) %2) (s := Finset.Icc 1 (4 * n.succ + 2))]
   rw [Finset.sum_attach (f := fun x ↦ (x:ℤ) %2) (s := Finset.Icc 1 (4 * n + 2))] at ih
   let s1 := Finset.Icc 1 (4 * n + 2)
   let s2 := Finset.Ioc (4 * n + 2) (4 * n.succ + 2)
   have hd : Disjoint s1 s2 := by
      intro a hs1 hs2 b hb
      have hb1 := hs1 hb
      have hb2 := hs2 hb
      rw [Finset.mem_Icc] at hb1
      rw [Finset.mem_Ioc] at hb2
      linarith
   have hu : Finset.Icc 1 (4 * Nat.succ n + 2) = Finset.disjUnion s1 s2 hd := by
     ext a
     constructor
     · intro ha
       rw [Finset.mem_disjUnion]
       rw [Finset.mem_Icc] at ha ⊢
       rw [Finset.mem_Ioc]
       by_contra H
       rw [not_or, not_and_or, not_and_or, not_le, not_le, not_lt, not_le] at H
       obtain ⟨H1, H2⟩ := H
       cases' H1 with H11 H12 <;> cases' H2 with H21 H22 <;> linarith
     · intro ha
       rw [Finset.mem_disjUnion] at ha
       rw [Finset.mem_Icc] at ha ⊢
       rw [Finset.mem_Ioc] at ha
       cases' ha with ha1 ha2 <;> constructor <;> linarith
   rw [hu]
   rw [Finset.sum_disjUnion]
   rw [Int.add_emod]
   rw [ih]
   rw [lemma0 n]
   norm_num

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

      have h12 : (Finset.univ : Finset (Fin 2)) =
                  Finset.cons 0
                    (Finset.cons 1
                      {} (Finset.not_mem_empty _)) (by simp) := by simp (config := {decide := true})
      have h11 : ∑ x : Fin 999, ((ab 0 x : ℤ) % 2) + ∑ x : Fin 999, ((ab 1 x : ℤ) % 2) =
          ∑ x : Fin 2, ∑ y : Fin 999, ((ab x y : ℤ) % 2) := by
        rw [h12, Finset.sum_cons, Finset.sum_cons, Finset.sum_empty]
        ring

      rw [h11, ←Finset.sum_product']
      congr

    have h10 : ∑ x : Fin 2 × Fin 999, ((ab.uncurry x : ℤ) % 2) =
              ∑ x : Finset.Icc 1 1998, (x : ℤ) % 2 :=
      by apply Fintype.sum_bijective _ hab
         · exact congr_fun rfl
    rw [h9, h10]
    norm_num
    rw [lemma1 499]
    norm_num

  --
  -- Combining these facts gives S ≡ 9 MOD 10.
  have hmn : Nat.Coprime (Int.natAbs 2) (Int.natAbs 5) := by norm_cast
  rw [show (9:ℤ) = 9 % 10 by decide,
      ← zmod_eq,
      show (10:ℤ) = 2 * 5 by norm_num]

  rw [←Int.modEq_and_modEq_iff_modEq_mul hmn, zmod_eq, zmod_eq, h3, h2]
  decide
