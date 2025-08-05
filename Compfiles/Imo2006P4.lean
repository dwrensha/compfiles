/-
Copyright (c) 2025 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Project Numina Contributors
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file {
  tags := [.NumberTheory],
  importedFrom :=
    "https://huggingface.co/datasets/AI-MO/NuminaMath-LEAN",
}

/-!
# International Mathematical Olympiad 2006, Problem 4

Determine all pairs $(x, y)$ of integers satisfying the equation  $$ 1+2^{x}+2^{2 x+1}=y^{2} . $$
-/

namespace Imo2006P4

snip begin

/-
## Solution

The answer is $\{(0, 2), (0, -2), (4, 23), (4, -23)\}$.

-/

snip end

determine solution : Set (ℤ × ℤ) := {(0, 2), (0, -2), (4, 23), (4, -23)}

problem imo2006_p4 :
    {(x, y) : ℤ × ℤ | 1 + (2 : ℝ) ^ x + 2 ^ (2 * x + 1) = y ^ 2} =
    solution := by
  ext ⟨x, y⟩
  constructor <;> intro h
  · -- prove x is nonnegative
    simp at h
    have hxnonneg : x ≥ 0 := by
      by_contra hx
      push_neg at hx
      let k : ℕ := y.natAbs
      have hk1 : k < 2 := by
        suffices h : ((y.natAbs ^ 2 : ℤ) : ℝ) < (2 : ℝ) ^ 2
        · rw [Int.cast_pow] at h
          apply sq_lt_sq.mp at h
          norm_cast at h
        · rw [Int.natAbs_sq, Int.cast_pow, ←h]
          calc
            _ < (1 : ℝ) + 1 + 1 := by
              apply add_lt_add
              · apply add_lt_add_left
                apply zpow_lt_one_of_neg₀
                · norm_num
                · exact hx
              · apply zpow_lt_one_of_neg₀
                · norm_num
                · omega
            _ < 2 ^ 2 := by norm_num
      have hk2 : k > 1 := by
        suffices h : ((y.natAbs ^ 2 : ℤ) : ℝ) > (1 : ℝ) ^ 2
        · rw [Int.cast_pow] at h
          apply sq_lt_sq.mp at h
          norm_cast at h
        · rw [Int.natAbs_sq, Int.cast_pow, ←h, add_assoc]
          simp only [one_pow, gt_iff_lt, lt_add_iff_pos_right]
          positivity
      interval_cases k
    lift x to ℕ using hxnonneg
    norm_cast at h
    simp at h
    -- If $(x, y)$ is a solution then obviously $x \geq 0$ and $(x,-y)$ is a solution too.
    wlog hynonneg : y ≥ 0 with H
    · have : (1 + 2 ^ x + 2 ^ (2 * x + 1)) = (-y) ^ 2 := by simp; exact h
      have hy : -y ≥ 0 := by push_neg at hynonneg; apply neg_nonneg_of_nonpos; exact le_of_lt hynonneg
      apply H (-y) x this at hy
      simp at hy
      rcases hy with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
      all_goals simp [hx, ←hy]
    · lift y to ℕ using hynonneg
      norm_cast at h
      by_cases hx : x = 0
      · -- For $x=0$ we get the two solutions $(0,2)$ and $(0,-2)$.
        simp [hx] at h
        rw [show 4 = 2 ^ 2 by norm_num] at h
        apply sq_eq_sq₀ (by simp) (by simp) |>.mp at h
        simp [hx, ←h]
      · -- Now let $(x, y)$ be a solution with $x&gt;0$;
        -- without loss of generality confine attention to $y&gt;0$.
        have hxpos : x > 0 := by apply Nat.ne_zero_iff_zero_lt.mp hx
        have hypos : y > 0 := by by_contra hy; simp at hy; simp [hy] at h
        -- The equation rewritten as $$ 2^{x}\left(1+2^{x+1}\right)=(y-1)(y+1) $$
        have h : 2 ^ x * (2 ^ (x + 1) + 1) = (y - 1) * (y + 1) := by
          rw [Nat.sub_mul, Nat.mul_add, Nat.one_mul, Nat.mul_add, Nat.mul_one, Nat.mul_one, Nat.add_comm y 1, Nat.add_sub_add_right, ←sq, ←h]
          apply Nat.eq_sub_of_add_eq
          ring_nf
        -- shows that the factors $y-1$ and $y+1$ are even, exactly one of them divisible by 4 .
        have h2dvd : 2 ∣ y - 1 := by
          have : 2 ^ x ∣ (y - 1) * (y + 1) := by simp [←h]
          have : 2 ∣ y - 1 ∨ 2 ∣ (y + 1) := by
            refine (Nat.Prime.dvd_mul ?pp).mp ?_
            · norm_num
            · apply Nat.dvd_trans ?_ this
              exact dvd_pow_self 2 hx
          rcases this with h | h
          · exact h
          · rw [show y - 1 = y + 1 - 2 by simp]
            refine Nat.dvd_sub h ?inr.h₂
            simp
        have h8div : 2 ^ 3 ∣ (y - 1) * (y + 1) := by
          obtain ⟨s, hs⟩ := h2dvd
          have : y + 1 = 2 * (s + 1) := by
            trans y - 1 + 2
            · simp
              rw [Nat.sub_add_cancel]
              exact hypos
            · rw [hs]
              ring
          rw [hs, this]
          by_cases h : Even s
          · obtain ⟨t, hs⟩ := h
            use t * (s + 1)
            simp [hs]
            ring
          · simp at h
            have ⟨t, ht⟩ : Even (s + 1) := Odd.add_one h
            use s * t
            simp [ht]
            ring
        -- Hence $x \geq 3$ and one of these factors is divisible by $2^{x-1}$ but not by $2^{x}$.
        have hxge3 : x ≥ 3 := by
          rw [←h] at h8div
          have hco : (2 ^ 3).Coprime (2 ^ (x + 1) + 1) := by
            refine Nat.Coprime.pow_left 3 ?_
            refine Odd.coprime_two_left ?_
            refine Even.add_one ?_
            refine (Nat.even_pow' ?_).mpr ?_
            · simp
            · simp
          apply Nat.Coprime.dvd_mul_right hco |>.mp at h8div
          exact Nat.pow_dvd_pow_iff_le_right'.mp h8div
        -- So $$ y=2^{x-1} m+\epsilon, \quad m \text { odd }, \quad \epsilon= \pm 1 $$
        obtain ⟨m, hm, ε, hε, hy⟩ : ∃ m : ℕ, Odd m ∧ ∃ (ε : ℤ), (ε = 1 ∨ ε = -1) ∧ (y = 2 ^ (x - 1) * m + ε) := by
          let n₁ := (y - 1).factorization 2
          obtain ⟨t, ht⟩ : 2 ^ n₁ ∣ y - 1 := by exact Nat.ordProj_dvd (y - 1) 2
          have hysub : ¬y - 1 = 0 := by
            by_contra hsub
            simp [hsub] at h
          have ht' : Odd t := by
            by_contra ht'
            simp at ht'
            obtain ⟨r, hr⟩ := ht'
            rw [hr] at ht
            have : 2 ^ (n₁ + 1) ∣ y - 1 := by use r; simp [ht]; ring
            apply Nat.Prime.pow_dvd_iff_le_factorization (by norm_num) hysub |>.mp at this
            simp only [n₁, add_le_iff_nonpos_right, nonpos_iff_eq_zero, one_ne_zero] at this
          have ht'' : t ≠ 0 := Nat.ne_of_odd_add ht'
          have h1 : (2 ^ (x + 1) + 1).factorization 2 = 0 := by
            apply Nat.factorization_eq_zero_of_not_dvd
            apply Odd.not_two_dvd_nat
            rw [add_comm]
            apply Odd.add_even
            · simp
            · refine Nat.even_pow.mpr ?h.h.hb.a
              simp
          by_cases h₁ : n₁ > 1
          · have : y + 1 = 2 * (2 ^ (n₁ - 1) * t + 1) := by
              apply Nat.eq_add_of_sub_eq at ht
              rw [ht, mul_add]
              simp [←Nat.mul_assoc]
              left
              rw [←Nat.pow_add_one', Nat.sub_add_cancel]
              exact Nat.one_le_of_lt h₁
              exact hypos
            have h' : 2 ^ x * (2 ^ (x + 1) + 1) = 2 ^ (n₁ + 1) * (t * (2 ^ (n₁ - 1) * t + 1)) := by
              rw [h, this, ht]
              rw [Nat.pow_add_one]
              ring_nf
            apply congrArg (fun i => Nat.factorization i 2) at h'
            rw [Nat.factorization_mul (by positivity), Nat.factorization_mul (by positivity)] at h'
            · norm_num at h'
              have h2 : (t * (2 ^ (n₁ - 1) * t + 1)).factorization 2 = 0 := by
                apply Nat.factorization_eq_zero_of_not_dvd
                apply Odd.not_two_dvd_nat
                apply Odd.mul ht'
                rw [add_comm]
                apply Odd.add_even
                · simp
                · use 2 ^ (n₁ - 2) * t
                  rw [show n₁ - 1 = n₁ - 2 + 1 by simp; rw [Nat.sub_add_cancel]; exact h₁, Nat.pow_add_one']
                  ring
              apply Nat.eq_add_of_sub_eq at ht
              · simp [h1, h2] at h'
                use t, ht', 1
                simp [ht, h']
              · exact hypos
            · intro h'
              simp at h'
              simp [h'] at ht''
            · simp
          · simp at h₁
            interval_cases n₁
            · simp at ht
              have : Even (y - 1) := by exact (even_iff_exists_two_nsmul (y - 1)).mpr h2dvd
              rw [ht] at this
              have : ¬ Even t := by exact Nat.not_even_iff_odd.mpr ht'
              contradiction
            · simp at ht
              have : y + 1 = 2 * (t + 1) := by
                rw [mul_add, ←ht]
                simp
                rw [Nat.sub_add_cancel]
                exact hypos
              let n₂ := (t + 1).factorization 2
              obtain ⟨s, hs⟩ : 2 ^ n₂ ∣ t + 1 := by exact Nat.ordProj_dvd (t + 1) 2
              have hs' : Odd s := by
                by_contra hs'
                simp at hs'
                obtain ⟨r, hr⟩ := hs'
                rw [hr] at hs
                have : 2 ^ (n₂ + 1) ∣ t + 1 := by use r; simp [hs]; ring
                apply Nat.Prime.pow_dvd_iff_le_factorization (by norm_num) (by simp) |>.mp at this
                simp [n₂] at this
              have h' : 2 ^ x * (2 ^ (x + 1) + 1) = 2 ^ (n₂ + 2) * (t * s) := by
                rw [h, this, ht, hs]
                rw [Nat.pow_add_one]
                ring_nf
              apply congrArg (fun i => Nat.factorization i 2) at h'
              rw [Nat.factorization_mul (by apply pow_ne_zero; simp), Nat.factorization_mul (by apply pow_ne_zero; simp)] at h'
              · norm_num at h'
                have hmul : Odd (t * s) := by
                  exact Odd.mul ht' hs'
                have h2 : (t * s).factorization 2 = 0 := by
                  apply Nat.factorization_eq_zero_iff _ _ |>.mpr
                  right; left
                  exact Odd.not_two_dvd_nat hmul
                simp [h1, h2] at h'
                apply Nat.eq_add_of_sub_eq at ht
                · use s, hs', -1
                  simp [ht, h', pow_add]
                  rw [mul_comm _ 2, mul_assoc, show 2 ^ n₂ * (s : ℤ) = t + 1 by norm_cast; simp [hs]]
                  · ring
                · exact hypos
              · intro h'
                simp [ht''] at h'
                simp [h'] at hs'
              · simp
        -- Plugging this into the original equation we obtain
        -- $$ 2^{x}\left(1+2^{x+1}\right)=\left(2^{x-1} m+\epsilon\right)^{2}-1=2^{2 x-2} m^{2}+2^{x} m \epsilon, $$
        have h : 2 ^ x * (1 + 2 ^ (x + 1)) = 2 ^ (2 * x - 2) * m ^ 2 + 2 ^ x * m * ε := by
          trans (((y - 1) * (y + 1) : ℕ) : ℤ)
          · rw [←h]
            simp [add_comm]
          · rw [Nat.cast_mul, Nat.cast_sub]
            simp [hy]
            · trans (2 ^ (x - 1) * ↑m + ε) ^ 2 - 1
              · ring
              · ring_nf
                have : ε ^ 2 = 1 := sq_eq_one_iff.mpr hε
                simp [this]
                ring_nf
                congr 1
                · nth_rw 2 [show x = x - 1 + 1 by rw [Nat.sub_add_cancel]; exact hxpos]
                  rw [pow_add]
                  ring
                · congr
                  exact Nat.sub_one_mul _ _
            · exact hypos
        -- or, equivalently $$ 1+2^{x+1}=2^{x-2} m^{2}+m \epsilon.
        have h : 1 + 2 ^ (x + 1) = 2 ^ (x - 2) * m ^ 2 + m * ε := by
          calc
            _ = (2 : ℤ) ^ x * (1 + 2 ^ (x + 1)) / 2 ^ x := by
              rw [mul_div_cancel_left₀]
              positivity
            _ = (2 ^ x * 2 ^ (x - 2) * m ^ 2 + 2 ^ x * m * ε) / 2 ^ x := by rw [h]; congr; rw [←pow_add]; rw [←Nat.add_sub_assoc]; simp; ring_nf; exact Nat.le_of_succ_le hxge3
            _ = 2 ^ x * (2 ^ (x - 2) * m ^ 2 + m * ε) / 2 ^ x := by rw [mul_add, ←mul_assoc, ←mul_assoc]
            _ = _ := by simp
        -- $$ Therefore $$ 1-\epsilon m=2^{x-2}\left(m^{2}-8\right).
        have : 1 - m * ε = 2 ^ (x - 2) * (m ^ 2 - 8) := by
          rw [mul_sub]
          apply sub_eq_of_eq_add'
          rw [←add_sub_assoc]
          apply eq_sub_of_add_eq
          rw [add_comm (m * ε), ←h, show (8 : ℤ) = 2 ^ 3 by simp, ←pow_add]
          congr 2
          simp only [Nat.reduceEqDiff]
          rw [Nat.sub_add_cancel]
          exact Nat.le_of_succ_le hxge3
        have hmne1 : ¬ m = 1 := by
          intro h
          simp [h] at this
          rcases hε with hε | hε
          · simp [hε] at this
          · simp [hε] at this
            have : 2 ≤ (0 : ℤ) := by rw [this]; simp
            simp at this
        rcases hε with hε | hε
        · -- $$ For $\epsilon=1$ this yields $m^{2}-8 \leq 0$, i.e., $m=1$, which fails to satisfy (2).
          simp [hε] at this
          have hmnonpos : 1 - (m : ℤ) ≤ 0 := by simp; by_contra h; simp at h; simp [h] at hm
          rw [this] at hmnonpos
          have hm' : m ^ 2 - 8 ≤ (0 : ℤ) := by
            apply nonpos_of_mul_nonpos_right hmnonpos
            apply pow_pos
            simp
          simp at hm'
          norm_cast at hm'
          have hm' : m < 3 := by
            have : m ^ 2 < 3 ^ 2 := by apply lt_of_le_of_lt hm'; simp
            apply Nat.pow_lt_pow_iff_left ?_ |>.mp this
            simp
          have : m = 1 := by
            interval_cases m
            · simp at hm
            · simp
            · have : ¬ Odd 2 := by exact Nat.not_odd_iff.mpr rfl
              exact this.elim hm
          exact hmne1.elim this
        · -- For $\epsilon=-1$ equation (2) gives us $$ 1+m=2^{x-2}\left(m^{2}-8\right) \geq 2\left(m^{2}-8\right),
          simp [hε] at this
          have hle : 1 + (m : ℤ) ≥ 2 * (m ^ 2 - 8) := by
            rw [this]
            apply mul_le_mul
            · nth_rw 1 [show (2 : ℤ) = 2 ^ 1 by simp]
              apply pow_le_pow_right₀
              · simp
              · exact Nat.le_sub_of_add_le hxge3
            · simp
            · apply nonneg_of_mul_nonneg_right (a := 2 ^ (x - 2))
              · rw [←this]; exact Int.le.intro_sub (1 + m + 0) rfl
              · positivity
            · positivity
          -- $$ implying $2 m^{2}-m-17 \leq 0$. Hence $m \leq 3$;
          have : 2 * m ^ 2 - m - 17 ≤ (0 : ℤ) := by linarith only [hle]
          have : m ≤ 3 := by nlinarith only [h, hle]
          have : m = 1 ∨ m = 3 := by
            interval_cases m
            · simp at hm
            · simp
            · have : ¬ Odd 2 := by exact Nat.not_odd_iff.mpr rfl
              exact this.elim hm
            · simp
          -- on the other hand $m$ cannot be 1 by (2).
          simp [hmne1] at this
          -- Because $m$ is odd, we obtain $m=3$, leading to $x=4$.
          rw [hε, this, show (3 : ℕ) * (-1) = (-3 : ℤ) by rfl] at h
          simp at h
          have hx : x = 4 := by
            let t := 2 ^ (x - 2)
            have : (1 : ℤ) + 8 * t = t * 9 + (-3) := by
              simp [t]
              rw [←h]
              simp
              rw [show (8 : ℤ) = 2 ^ 3 by simp, ←pow_add]
              rw [←Nat.add_sub_assoc]
              · rw [show 3 = 1 + 2 by simp, Nat.add_comm, ←Nat.add_assoc]
                simp
              · exact Nat.le_of_succ_le hxge3
            have : (t : ℤ) = 4 := by linarith only [this]
            norm_cast at this
            simp [t] at this
            rw [show 4 = 2 ^ 2 by simp] at this
            apply Nat.pow_right_injective (by simp) at this
            apply Nat.sub_eq_iff_eq_add (by exact Nat.le_of_succ_le hxge3) |>.mp at this
            simp [this]
          -- From (1) we get $y=23$.
          simp [hx, hε, this] at hy
          norm_cast at hy
          -- These values indeed satisfy the given equation.
          -- Recall that then $y=-23$ is also good. T
          -- hus we have the complete list of solutions $(x, y):(0,2),(0,-2),(4,23),(4,-23)$.
          simp [hx, hy]
  · -- verify the answers
    simp at h ⊢
    rcases h with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
    all_goals simp [hx, hy]; norm_num


end Imo2006P4
