/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry, .NumberTheory] }

/-!
# USA Mathematical Olympiad 1981, Problem 1

Prove that if n is not a multiple of 3, then the angle π/n can be
trisected with ruler and compasses.
-/

namespace Usa1981P1

open Real

snip begin

/-
Mathlib has no predicate for "constructible with ruler and compasses",
so we formalize the essential content of the claim. Trisecting the angle
π/n means constructing the angle π/(3n) = (π/n)/3. Any integer multiple
of a given angle can be marked off with ruler and compasses, the angle
π/3 is constructible (equilateral triangle), and constructible angles
can be added and subtracted. Hence it suffices (and this is the official
solution) to exhibit integers a and b with

    a·(π/n) + b·(π/3) = π/(3n),

which, after clearing denominators, is Bézout's identity 3a + nb = 1.
-/

/-- Bézout's identity for a natural number coprime to 3. -/
lemma bezout_of_not_three_dvd (n : ℕ) (h3 : ¬ 3 ∣ n) :
    ∃ a b : ℤ, 3 * a + (n : ℤ) * b = 1 := by
  have hcop : Nat.gcd 3 n = 1 := (Nat.prime_three.coprime_iff_not_dvd).mpr h3
  have h := Nat.gcd_eq_gcd_ab 3 n
  rw [hcop] at h
  exact ⟨Nat.gcdA 3 n, Nat.gcdB 3 n, by exact_mod_cast h.symm⟩

snip end

problem usa1981_p1 (n : ℕ) (h3 : ¬ 3 ∣ n) :
    ∃ a b : ℤ, a * (Real.pi / (n : ℝ)) + b * (Real.pi / 3) =
      Real.pi / (3 * (n : ℝ)) := by
  -- Note that `n ≠ 0` already follows from `h3`, since 3 ∣ 0.
  obtain ⟨a, b, hab⟩ := bezout_of_not_three_dvd n h3
  refine ⟨a, b, ?_⟩
  have hn' : (n : ℝ) ≠ 0 := by
    have h : n ≠ 0 := fun hn0 ↦ h3 (hn0 ▸ dvd_zero 3)
    exact_mod_cast h
  have habr : 3 * (a : ℝ) + (n : ℝ) * (b : ℝ) = 1 := by exact_mod_cast hab
  -- `field_simp` clears the denominators and also cancels the common
  -- factor π (using `Real.pi_ne_zero`), leaving Bézout's identity.
  field_simp [hn']
  linear_combination habr

end Usa1981P1
