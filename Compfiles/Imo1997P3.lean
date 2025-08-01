/-
Copyright (c) 2025 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/

import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Data.Real.Sign
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Tactic

import ProblemExtraction

problem_file {
  tags := [.Algebra]
  importedFrom :=
    "https://github.com/leanprover-community/mathlib4/pull/27159"
}

/-!
# International Mathematical Olympiad 1997, Problem 3

Let $x_1, x_2, \dots, x_n$ be real numbers satisfying the conditions
$|x_1 + x_2 + \cdots + x_n| = 1$ and
$|x_i| ≤ \frac{n+1}2$ for $i = 1, 2, \dots, n$. Show that there exists
a permutation $y_1, y_2, \dots, y_n$ of $x_1, x_2, \dots, x_n$ such
that $|y_1 + 2y_2 + \cdots + ny_n| ≤ \frac{n+1}2$.
-/

namespace Imo1997P3

snip begin

/-
# Solution
For a permutation $π$ let $S(π) = \sum_{i=1}^n i x_{π(i)}$. We wish to show that there exists $π$
with $|S(π)| ≤ \frac{n+1}2$.
Suppose the contrary, that all permutations satisfy $\frac{n+1}2 < |S(π)|$. Then we note that for
two permutations $π, π'$ differing by a swap of adjacent elements, say $x_k$ and $x_{k+1}$,
$|S(π) - S(π')| = |x_k - x_{k+1}| ≤ n + 1$. This being the size of the interval
$[-\frac{n+1}/2, \frac{n+1}/2]$ forbidden to the $|S(π)|$, $S(π)$ and $S(π')$ must be on the
same side of said interval, i.e. they have the same sign.
By induction all the $S(\pi)$ have the same sign.
But now consider the identity permutation $1$ and the reverse permutation $R$. We have
$|S(1) + S(R)| = |(1 + n)x_1 + \cdots + (n + 1)x_n| = (n + 1)|x_1 + \cdots + x_n| = n + 1$.
Since $S(1)$ and $S(R)$ have the same sign yet are strictly larger than $\frac{n+1}2$ in
absolute value, $|S(1) + S(R)| > n + 1$, which yields a contradiction. Therefore the initial
assumption that all permutations satisfy $\frac{n+1}2 < |S(π)|$ must be false; the result follows.
-/

def S {n : ℕ} (x : Fin n → ℝ) (p : Equiv.Perm (Fin n)) : ℝ :=
  ∑ i, (i + 1) * x (p i)

lemma sign_eq_of_abs_sub_le {a b c : ℝ} (ha : c / 2 < |a|) (hb : c / 2 < |b|) (hc : 0 < c)
    (hs : |a - b| ≤ c) : a.sign = b.sign := by
  rw [lt_abs] at ha hb
  rcases ha with ha | ha
  · rw [Real.sign_of_pos ((half_pos hc).trans ha)]
    rcases hb with hb | hb
    · rw [Real.sign_of_pos ((half_pos hc).trans hb)]
    · have m := add_lt_add ha hb; rw [add_halves, ← sub_eq_add_neg] at m
      exact absurd (le_of_abs_le hs) (not_le.mpr m)
  · rw [Real.sign_of_neg (neg_pos.mp <| (half_pos hc).trans ha)]
    rcases hb with hb | hb
    · have m := add_lt_add ha hb; rw [add_halves, ← sub_eq_neg_add, ← neg_sub, lt_neg] at m
      exact absurd (neg_le_of_abs_le hs) (not_le.mpr m)
    · rw [Real.sign_of_neg (neg_pos.mp <| (half_pos hc).trans hb)]

lemma lt_abs_add_of_sign_eq {a b c : ℝ} (ha : c / 2 < |a|) (hb : c / 2 < |b|) (hc : 0 < c)
    (hs : a.sign = b.sign) : c < |a + b| := by
  rw [lt_abs] at ha hb
  rcases ha with ha | ha
  · rw [Real.sign_of_pos ((half_pos hc).trans ha)] at hs
    rcases hb with hb | hb
    · have m := add_lt_add ha hb; rw [add_halves] at m
      exact m.trans_le (le_abs_self _)
    · rw [Real.sign_of_neg (neg_pos.mp <| (half_pos hc).trans hb)] at hs
      norm_num at hs
  · rw [Real.sign_of_neg (neg_pos.mp <| (half_pos hc).trans ha)] at hs
    rcases hb with hb | hb
    · rw [Real.sign_of_pos ((half_pos hc).trans hb)] at hs
      norm_num at hs
    · have m := add_lt_add ha hb; rw [add_halves, ← neg_add] at m
      exact m.trans_le (neg_le_abs _)

/-- For fixed nonempty `x`, assuming the opposite of what is to be proven,
the signs of `S x p` are all the same. -/
lemma sign_eq_of_contra {n : ℕ}
    {x : Fin (n + 1) → ℝ} (hx₂ : ∀ i, |x i| ≤ ((n + 1 : ℕ) + 1) / 2)
    (h : ∀ (p : Equiv.Perm (Fin (n + 1))), ((n + 1 : ℕ) + 1) / 2 < |S x p|) :
    ∀ p, (S x 1).sign = (S x p).sign := fun p ↦ by
  induction p using Submonoid.induction_of_closure_eq_top_right
    (Equiv.Perm.mclosure_swap_castSucc_succ n) with
  | one => rfl
  | mul_right p s sform ih =>
    suffices |S x p - S x (p * s)| ≤ (n + 1 : ℕ) + 1 by
      rw [ih]; exact sign_eq_of_abs_sub_le (h _) (h _) (by positivity) this
    rw [Set.mem_range] at sform; obtain ⟨i, hi⟩ := sform
    iterate 2 rw [S, ← Finset.sum_add_sum_compl {i.castSucc, i.succ}]
    have cg : ∑ j ∈ {i.castSucc, i.succ}ᶜ, (j + 1) * x ((p * s) j) =
        ∑ j ∈ {i.castSucc, i.succ}ᶜ, (j + 1) * x (p j) := by
      congr! 3 with j mj; rw [Equiv.Perm.mul_apply, ← hi]; congr
      rw [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at mj
      exact Equiv.swap_apply_of_ne_of_ne mj.1 mj.2
    rw [cg, add_sub_add_right_eq_sub,
      Finset.sum_pair (Fin.castSucc_lt_succ _).ne, Finset.sum_pair (Fin.castSucc_lt_succ _).ne,
      Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ← hi, Equiv.swap_apply_left,
      Equiv.swap_apply_right, add_comm, add_sub_add_comm, ← sub_mul, ← sub_mul, Fin.val_succ,
      Fin.coe_castSucc, Nat.cast_add, Nat.cast_one, add_sub_cancel_left, sub_add_cancel_left,
      one_mul, neg_one_mul]
    calc
      _ ≤ |x (p i.succ)| + |-x (p i.castSucc)| := abs_add_le ..
      _ ≤ ((n + 1 : ℕ) + 1) / 2 + ((n + 1 : ℕ) + 1) / 2 := by
        rw [abs_neg]; exact add_le_add (hx₂ _) (hx₂ _)
      _ = _ := add_halves _

lemma S_one_add_S_revPerm {n : ℕ}
    {x : Fin n → ℝ} (hx₁ : |∑ i, x i| = 1) : |S x 1 + S x Fin.revPerm| = n + 1 := by
  nth_rw 2 [S]; rw [← Fin.revPerm.sum_comp _ _ (by simp)]
  simp_rw [Fin.revPerm_apply, Fin.val_rev, Fin.rev_rev, S, Equiv.Perm.one_apply,
           ← Finset.sum_add_distrib, ← add_mul]
  have cg : ∑ i : Fin n, (i + 1 + ((n - (i + 1) : ℕ) + 1)) * x i = ∑ i, (n + 1) * x i := by
    congr! 2 with i; norm_cast; omega
  rw [cg, ← Finset.mul_sum, abs_mul, hx₁, mul_one]; exact abs_of_nonneg (by positivity)

snip end

problem imo1997_p3 {n : ℕ} {x : Fin n → ℝ} (hx₁ : |∑ i, x i| = 1)
    (hx₂ : ∀ i, |x i| ≤ (n + 1) / 2) :
    ∃ p : Equiv.Perm (Fin n), |∑ i, (i + 1) * x (p i)| ≤ (n + 1) / 2 := by
  match n with
  | 0 => simp
  | n + 1 =>
    by_contra! h
    exact (lt_abs_add_of_sign_eq (h _) (h _) (by positivity)
      (sign_eq_of_contra hx₂ h _)).ne' (S_one_add_S_revPerm hx₁)

end Imo1997P3
