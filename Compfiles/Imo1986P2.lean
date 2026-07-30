/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 1986, Problem 2

Given a point P₀ in the plane of the triangle A₁A₂A₃. Define Aₛ = Aₛ₋₃ for all
s ≥ 4. Construct a set of points P₁, P₂, P₃, ... such that Pₖ₊₁ is the image of
Pₖ under a rotation with center Aₖ₊₁ through 120° clockwise (for k = 0, 1, 2, ...).
Prove that if P₁₉₈₆ = P₀, then the triangle A₁A₂A₃ is equilateral.
-/

namespace Imo1986P2

/-- The multiplier `ω = exp(-2πi/3)`: multiplication by `ω` is the clockwise
rotation through 120° about the origin in the complex plane. -/
noncomputable def ω : ℂ := Complex.exp (↑(-(2 * Real.pi / 3)) * Complex.I)

/-- The clockwise rotation through 120° with center `a`, applied to the point `p`. -/
noncomputable def rot (a p : ℂ) : ℂ := a + ω * (p - a)

snip begin

/-- `ω` is a cube root of unity. -/
lemma omega_cubed : ω ^ 3 = 1 := by
  have h : ((3 : ℕ) : ℂ) * (↑(-(2 * Real.pi / 3)) * Complex.I) =
      (↑(-1 : ℤ) : ℂ) * (2 * ↑Real.pi * Complex.I) := by
    push_cast
    ring
  calc ω ^ 3 = Complex.exp (↑(3 : ℕ) * (↑(-(2 * Real.pi / 3)) * Complex.I)) :=
        (Complex.exp_nat_mul _ 3).symm
    _ = Complex.exp (↑(-1 : ℤ) * (2 * ↑Real.pi * Complex.I)) := by rw [h]
    _ = 1 := Complex.exp_int_mul_two_pi_mul_I _

/-- `ω` is not `1`: its real part is `-1/2`. -/
lemma omega_ne_one : ω ≠ 1 := by
  have hre : ω.re = Real.cos (2 * Real.pi / 3) := by
    show (Complex.exp (↑(-(2 * Real.pi / 3)) * Complex.I)).re = _
    rw [Complex.exp_ofReal_mul_I_re, Real.cos_neg]
  have hcos : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub,
      Real.cos_pi_div_three]
    norm_num
  intro h
  rw [h] at hre
  simp only [Complex.one_re] at hre
  rw [hcos] at hre
  norm_num at hre

/-- `ω` has norm `1`. -/
lemma omega_norm : ‖ω‖ = 1 := Complex.norm_exp_ofReal_mul_I _

/-- `ω` satisfies `ω² + ω + 1 = 0`. -/
lemma omega_sq_add : ω ^ 2 + ω + 1 = 0 := by
  have hfact : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by
    rw [show (ω - 1) * (ω ^ 2 + ω + 1) = ω ^ 3 - 1 by ring, omega_cubed, sub_self]
  rcases mul_eq_zero.mp hfact with h | h
  · exact absurd (sub_eq_zero.mp h) omega_ne_one
  · exact h

lemma one_sub_omega_ne : (1 : ℂ) - ω ≠ 0 := sub_ne_zero.mpr omega_ne_one.symm

/-- The composition of three successive clockwise 120° rotations about `a`, `b` and
`c` is a translation. -/
lemma rot_rot_rot (a b c p : ℂ) :
    rot c (rot b (rot a p)) = p + (1 - ω) * (ω ^ 2 * a + ω * b + c) := by
  show c + ω * ((b + ω * ((a + ω * (p - a)) - b)) - c) = _
  linear_combination p * omega_cubed

/-- A 3-periodic sequence repeats every three steps. -/
lemma apply_periodic (A : ℕ → ℂ) (hA : ∀ n, A (n + 3) = A n) (k m : ℕ) :
    A (3 * k + m) = A m := by
  induction k with
  | zero => simp
  | succ k ih =>
      have e : 3 * (k + 1) + m = 3 * k + m + 3 := by ring
      rw [e, hA, ih]

snip end

problem imo1986_p2
    (A : ℕ → ℂ) (hA : ∀ n, A (n + 3) = A n)
    (P : ℕ → ℂ) (hP : ∀ k, P (k + 1) = rot (A (k + 1)) (P k))
    (h : P 1986 = P 0) :
    dist (A 1) (A 2) = dist (A 2) (A 3) ∧ dist (A 2) (A 3) = dist (A 3) (A 1) := by
  -- Three successive steps of the iteration translate every point by a fixed vector.
  have step3 : ∀ k : ℕ, P (3 * (k + 1)) =
      P (3 * k) + (1 - ω) * (ω ^ 2 * A 1 + ω * A 2 + A 3) := by
    intro k
    have h1 : P (3 * k + 1) = rot (A 1) (P (3 * k)) := by
      have hPk := hP (3 * k)
      rwa [apply_periodic A hA k 1] at hPk
    have h2 : P (3 * k + 2) = rot (A 2) (P (3 * k + 1)) := by
      have hPk := hP (3 * k + 1)
      rw [show 3 * k + 1 + 1 = 3 * k + 2 by ring, apply_periodic A hA k 2] at hPk
      exact hPk
    have h3 : P (3 * k + 3) = rot (A 3) (P (3 * k + 2)) := by
      have hPk := hP (3 * k + 2)
      rw [show 3 * k + 2 + 1 = 3 * k + 3 by ring, apply_periodic A hA k 3] at hPk
      exact hPk
    rw [show 3 * (k + 1) = 3 * k + 3 by ring, h3, h2, h1,
      rot_rot_rot (A 1) (A 2) (A 3) (P (3 * k))]
  -- Hence `P (3k) = P 0 + k • v` for every `k`, where `v` is that fixed vector.
  have iter : ∀ k : ℕ,
      P (3 * k) = P 0 + ↑k * ((1 - ω) * (ω ^ 2 * A 1 + ω * A 2 + A 3)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [step3 k, ih]
        push_cast
        ring
  -- Since 1986 = 3 · 662 and `P 1986 = P 0`, the translation vector must vanish.
  have hX : (1 - ω) * (ω ^ 2 * A 1 + ω * A 2 + A 3) = 0 := by
    have h662 := iter 662
    rw [show 3 * 662 = 1986 by norm_num, h] at h662
    have hmul : ((662 : ℕ) : ℂ) * ((1 - ω) * (ω ^ 2 * A 1 + ω * A 2 + A 3)) = 0 := by
      linear_combination -h662
    exact (mul_eq_zero.mp hmul).resolve_left (by norm_num)
  have hS : ω ^ 2 * A 1 + ω * A 2 + A 3 = 0 :=
    (mul_eq_zero.mp hX).resolve_left one_sub_omega_ne
  have hA3 : A 3 = -(ω ^ 2 * A 1 + ω * A 2) := by linear_combination hS
  -- The remaining side differences are rotations of `A 1 - A 2`, so all three
  -- sides of the triangle have the same length.
  have h13 : A 1 - A 3 = ω * (A 2 - A 1) := by
    rw [hA3]
    linear_combination A 1 * omega_sq_add
  have h23 : A 2 - A 3 = ω ^ 2 * (A 1 - A 2) := by
    rw [hA3]
    linear_combination A 2 * omega_sq_add
  have e23 : dist (A 2) (A 3) = ‖A 1 - A 2‖ := by
    rw [Complex.dist_eq, h23, norm_mul, norm_pow, omega_norm, one_pow, one_mul]
  have e13 : dist (A 3) (A 1) = ‖A 1 - A 2‖ := by
    have e1 : A 3 - A 1 = -(A 1 - A 3) := by ring
    have e2 : A 2 - A 1 = -(A 1 - A 2) := by ring
    rw [Complex.dist_eq, e1, norm_neg, h13, norm_mul, omega_norm, one_mul, e2, norm_neg]
  constructor
  · rw [e23]
    exact Complex.dist_eq _ _
  · rw [e23, e13]

end Imo1986P2
