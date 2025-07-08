/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 1996, Problem 3

Let S denote the set of nonnegative integers. Find
all functions f from S to itself such that

 f(m + f(n)) = f(f(m)) + f(n)

for all m,n in S.
-/

namespace Imo1996P3

-- either the zero function or of the form
-- f(qk + r) = qk + (n r) k for 0 ≤ r < k

determine SolutionSet : Set (ℕ → ℕ) :=
--   {fun _ ↦ 0} ∪
   {f | ∃ k : ℕ, ∃ n : ℕ → ℕ, n 0 = 0 ∧
         f = fun x ↦ (x / k) * k + (n (x % k)) * k }

problem imo1996_p3 (f : ℕ → ℕ) :
    f ∈ SolutionSet ↔ ∀ m n, f (m + f n) = f (f m) + f n := by
  -- we follow the informal solution from
  -- https://prase.cz/kalva/imo/isoln/isoln963.html
  constructor
  · intro hf m n
    simp only [Set.mem_setOf_eq] at hf
    obtain ⟨k, n1, hn1, hf1⟩ := hf

    obtain hk0 | hkp := Nat.eq_zero_or_pos k
    · rw [hf1, hk0]; simp

    -- Let m = ak + r, n = bk + s, with 0 ≤ r, s < k.
    let a := m / k
    let r := m % k
    let b := n / k
    let s := n % k

    have h2 : ∀ x, k ∣ x → f x = x := fun x hx ↦ by
      rw [hf1]
      dsimp only
      rw [Nat.div_mul_cancel hx, Nat.dvd_iff_mod_eq_zero.mp hx, hn1]
      simp

    have h3 : ∀ x, k ∣ f x := fun x ↦ by
      rw [hf1]
      dsimp only
      rw [←Nat.add_mul]
      exact Nat.dvd_mul_left _ _

    -- Then f(f(m)) = f(m)
    have h1 : ∀ x, f (f x) = f x := fun x ↦ by grind

    -- f(m) = ak + (n r) k
    have h4 : f m = a * k + (n1 r) * k := by subst f; rfl

    -- and f(n) = bk + (n s) k
    have h5 : f n = b * k + (n1 s) * k := by subst f; rfl

    -- so f(m + f(n)) = ak + bk + nrk + nsk,
    have h6 : f (m + f n) = a * k + b * k + (n1 r) * k + (n1 s) * k := by
      -- todo: cleaner version that uses the above lemmas?
      rw [h5]
      rw [hf1]
      dsimp only
      rw [Nat.add_mod, Nat.add_mod (b * k)]
      simp only [Nat.mul_mod_left, add_zero, Nat.zero_mod,
                 dvd_refl, Nat.mod_mod_of_dvd]
      have h7 : k ∣ b * k + n1 s * k := by apply Nat.dvd_add <;> simp
      rw [Nat.add_div_of_dvd_left h7]
      rw [←Nat.add_mul b]
      rw [Nat.mul_div_left (b + n1 s) hkp, Nat.add_mul]
      ring

    -- and f(f(m)) + f(n) = ak + bk + nrk + nsk.
    have h8 : f (f m) + f n = a * k + b * k + (n1 r) * k + (n1 s) * k := by
      grind

    grind
  intro hf
  simp only [Set.mem_setOf_eq]
  sorry


end Imo1996P3
