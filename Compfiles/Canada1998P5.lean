/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw, Kimi K3
-/

module

public import Mathlib.Tactic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Algebra] }

/-!
Canadian Mathematical Olympiad 1998, Problem 5

Let m be a positive integer. Define the sequence {aₙ} by a₀ = 0,
a₁ = m, and aₙ₊₁ = m²aₙ - aₙ₋₁ for n ≥ 1. Prove that an ordered pair
(a,b) of nonegative integers, with a ≤ b, is a solution of the equation

 (a² + b²) / (ab + 1) = m²

if an only if (a,b) = (aₙ,aₙ₊₁) for some n ≥ 0.
-/

namespace Canada1998P5

def A (m : ℕ) (hm : 0 < m) : ℕ → ℤ
| 0 => 0
| 1 => (↑m)
| n + 2 => (m : ℤ)^2 * A m hm (n + 1) - A m hm n

determine answer (m : ℕ) (hm : 0 < m) : Set (ℕ × ℕ) :=
  {p : ℕ × ℕ | ∃ n : ℕ, (p.1 : ℤ) = A m hm n ∧ (p.2 : ℤ) = A m hm (n + 1)}

problem canada1998_p5 (m : ℕ) (hm : 0 < m) (a b : ℕ) (hab : a ≤ b) :
    a^2 + b^2 = m^2 * (a * b + 1) ↔ (a, b) ∈ answer m hm := by
  change a^2 + b^2 = m^2 * (a * b + 1) ↔
     ∃ n : ℕ, (a:ℤ) = A m hm n ∧ (b:ℤ) = A m hm (n + 1)
  -- consecutive terms of the sequence satisfy the equation
  have hQ : ∀ n : ℕ, (A m hm n)^2 + (A m hm (n + 1))^2
      = (m:ℤ)^2 * (A m hm n * A m hm (n + 1) + 1) := by
    intro n
    induction n with
    | zero =>
      show (A m hm 0)^2 + (A m hm 1)^2 = (m:ℤ)^2 * (A m hm 0 * A m hm 1 + 1)
      rw [show A m hm 0 = 0 from rfl, show A m hm 1 = (m:ℤ) from rfl]
      ring
    | succ n ih =>
      show (A m hm (n + 1))^2 + (A m hm (n + 2))^2
          = (m:ℤ)^2 * (A m hm (n + 1) * A m hm (n + 2) + 1)
      rw [show A m hm (n + 2) = (m:ℤ)^2 * A m hm (n + 1) - A m hm n from rfl]
      linear_combination ih
  -- Vieta jumping: every solution is a pair of consecutive terms
  have key : ∀ a : ℕ, ∀ b : ℕ, a ≤ b → a^2 + b^2 = m^2 * (a * b + 1) →
      ∃ n : ℕ, (a:ℤ) = A m hm n ∧ (b:ℤ) = A m hm (n + 1) := by
    intro a
    induction a using Nat.strong_induction_on with
    | _ a ih =>
      intro b hab h
      rcases Nat.eq_zero_or_pos a with rfl | hapos
      · have h' : b ^ 2 = m ^ 2 := by simpa using h
        have h'' : (b:ℤ) ^ 2 = (m:ℤ) ^ 2 := by exact_mod_cast h'
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp h'' with hbz | hbz
        · have hbm : b = m := by exact_mod_cast hbz
          subst hbm
          exact ⟨0, rfl, rfl⟩
        · exfalso
          have hb0 : (0:ℤ) ≤ (b:ℤ) := by positivity
          have hm0 : (0:ℤ) < (m:ℤ) := by exact_mod_cast hm
          linarith
      · -- the Vieta root jump: replace b by m^2 * a - b
        have hℤ : (a:ℤ)^2 + (b:ℤ)^2 = (m:ℤ)^2 * ((a:ℤ) * (b:ℤ) + 1) := by
          exact_mod_cast h
        have haℤ : (0:ℤ) < (a:ℤ) := by exact_mod_cast hapos
        have hbℤ : (0:ℤ) < (b:ℤ) := by exact_mod_cast (lt_of_lt_of_le hapos hab)
        have hmℤ : (1:ℤ) ≤ (m:ℤ) := by exact_mod_cast hm
        have hroot : ((m:ℤ)^2 * (a:ℤ) - (b:ℤ))^2 + (a:ℤ)^2
            = (m:ℤ)^2 * (((m:ℤ)^2 * (a:ℤ) - (b:ℤ)) * (a:ℤ) + 1) := by
          linear_combination hℤ
        have hnonneg : 0 ≤ (m:ℤ)^2 * (a:ℤ) - (b:ℤ) := by
          by_contra hc
          push Not at hc
          have h1 : ((m:ℤ)^2 * (a:ℤ) - (b:ℤ)) * (a:ℤ) + 1 ≤ 0 := by
            nlinarith [haℤ, hc]
          have h2 : (m:ℤ)^2 * (((m:ℤ)^2 * (a:ℤ) - (b:ℤ)) * (a:ℤ) + 1) ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos (by positivity) h1
          nlinarith [hroot, sq_nonneg ((m:ℤ)^2 * (a:ℤ) - (b:ℤ)), haℤ]
        obtain ⟨b', hb'⟩ := Int.eq_ofNat_of_zero_le hnonneg
        have hroot' : b'^2 + a^2 = m^2 * (b' * a + 1) := by
          have h3 := hroot
          rw [hb'] at h3
          exact_mod_cast h3
        have hb'_lt : b' < a := by
          have hprod : (b:ℤ) * (b':ℤ) = (a:ℤ)^2 - (m:ℤ)^2 := by
            rw [← hb']
            linear_combination -hℤ
          have hlt : (b:ℤ) * (b':ℤ) < (b:ℤ) * (a:ℤ) := by
            rw [hprod]
            have hab2 : (a:ℤ) * (a:ℤ) ≤ (a:ℤ) * (b:ℤ) :=
              mul_le_mul_of_nonneg_left (by exact_mod_cast hab) haℤ.le
            have hm2 : (1:ℤ) ≤ (m:ℤ)^2 := one_le_pow₀ hmℤ
            nlinarith
          have hlt' : (b':ℤ) < (a:ℤ) := lt_of_mul_lt_mul_left hlt hbℤ.le
          exact_mod_cast hlt'
        obtain ⟨k, hk1, hk2⟩ := ih b' hb'_lt a hb'_lt.le hroot'
        refine ⟨k + 1, hk2, ?_⟩
        have hAk : A m hm (k + 1 + 1) = (m:ℤ)^2 * A m hm (k + 1) - A m hm k := rfl
        rw [hAk, ← hk1, ← hk2, ← hb']
        ring
  constructor
  · intro h
    exact key a b hab h
  · rintro ⟨n, ha, hb⟩
    have h2 : (a:ℤ)^2 + (b:ℤ)^2 = (m:ℤ)^2 * ((a:ℤ) * (b:ℤ) + 1) := by
      rw [ha, hb]
      exact hQ n
    exact_mod_cast h2



end Canada1998P5
