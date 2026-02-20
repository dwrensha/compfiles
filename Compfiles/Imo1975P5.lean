/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Constantin Seebach
-/

import Mathlib
import ProblemExtraction


problem_file

/-!
# International Mathematical Olympiad 1975, Problem 5

Determine, with proof, whether or not one can find $1975$ points on the circumference of a circle
with unit radius such that the distance between any two of them is a rational number.
-/

namespace Imo1975P5

determine constructible : Bool := true

snip begin


@[simp]
theorem Complex.mk_mem_unitSphere_iff (a b : ℝ) : Complex.mk a b ∈ Submonoid.unitSphere ℂ ↔ a^2+b^2=1 := by
  rw [Submonoid.unitSphere, <-Submonoid.mem_carrier, mem_sphere_iff_norm, sub_zero, <-sq_eq_sq₀,
    Complex.norm_eq_sqrt_sq_add_sq, Real.sq_sqrt, one_pow] <;> positivity


theorem not_irrational_add {b c : ℝ}: ¬Irrational b → ¬Irrational c → ¬Irrational (b + c) := by
  intro h1 h2
  apply not_imp_not.mpr (Irrational.add_cases)
  apply not_or_intro h1 h2

theorem not_irrational_sub {b c : ℝ} : ¬Irrational b → ¬Irrational c → ¬Irrational (b - c) := by
  intro h1 h2
  apply not_imp_not.mpr (Irrational.add_cases)
  apply not_or_intro h1 _
  rw [irrational_neg_iff]
  exact h2

theorem not_irrational_mul {b c : ℝ} : ¬Irrational b → ¬Irrational c → ¬Irrational (b * c) := by
  intro h1 h2
  apply not_imp_not.mpr (Irrational.mul_cases)
  apply not_or_intro h1 h2

theorem irrational_abs_iff {x : ℝ} : Irrational |x| ↔ Irrational x := by
  apply abs_by_cases (fun y => Irrational y ↔ Irrational x) Iff.rfl
  exact irrational_neg_iff


noncomputable def θ : ℝ := Real.arccos (4/5)

theorem sin_θ : Real.sin θ = (3/5:ℚ) := by
  unfold θ
  rw [Real.sin_arccos]
  field

theorem cos_θ : Real.cos θ = (4/5:ℚ) := by
  unfold θ
  rw [Real.cos_arccos] <;> linarith


noncomputable def P (n:ℕ) : Circle := {
  val := ⟨Real.cos (θ*2*n), Real.sin (θ*2*n)⟩
  property := by simp
}

theorem not_irrational_sin_θ_mul_and_not_irrational_cos_θ_mul (n : ℕ)
    : ¬ Irrational (Real.sin (θ*n)) ∧ ¬ Irrational (Real.cos (θ*n)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_add, mul_add, Real.sin_add, Real.cos_add]
    grind only [= cos_θ, = sin_θ, Rat.not_irrational, not_irrational_mul, not_irrational_add, not_irrational_sub]


theorem not_irrational_dist_P_P (i j : ℕ) : ¬ Irrational (dist (P i) (P j)) := by
  unfold P
  rw [Subtype.dist_eq, Complex.dist_mk, Real.cos_sub_cos, Real.sin_sub_sin, mul_right_comm]
  repeat rw [mul_pow]
  simp only [even_two, Even.neg_pow]
  rw [<-mul_add]
  simp only [Real.sin_sq_add_cos_sq, mul_one, Nat.ofNat_nonneg, pow_succ_nonneg, Real.sqrt_mul,
    Real.sqrt_sq]
  rw [Real.sqrt_sq_eq_abs]
  apply not_irrational_mul (not_irrational_ofNat _)
  rw [irrational_abs_iff, mul_right_comm _ 2 _, mul_right_comm _ 2 _, <-sub_mul, mul_div_cancel_right₀ _ (by simp), Real.sin_sub]
  apply not_irrational_sub <;> apply not_irrational_mul <;> simp [not_irrational_sin_θ_mul_and_not_irrational_cos_θ_mul]


theorem sin_mul_θ_ne_zero (n : ℕ) (hz : 1 ≤ n) : Real.sin (n * θ) ≠ 0 := by
  by_contra
  have := @niven_sin θ ?_ ?_
  · rw [sin_θ] at this
    simp at this
    grind only
  · rw [Real.sin_eq_zero_iff] at this
    let ⟨z, h⟩ := this
    use z/n
    rify
    have : 0 < (n:ℝ) := by
      rw [Nat.cast_pos]
      exact Nat.zero_lt_of_lt hz
    grind only
  · rw [sin_θ]
    use ?_


theorem P_injective : Function.Injective P := by
  intro i j e
  contrapose! e
  wlog w : j < i
  · rw [ne_comm]
    have := this e.symm
    grind only
  unfold P
  rw [Ne, Iff.not (Subtype.ext_iff)]
  simp only [Complex.mk.injEq, not_and]
  intro _
  suffices Real.sin (θ*2*(i-j)) ≠ 0 by
    grind only [mul_sub, Real.sin_sub]
  rw [mul_assoc, mul_comm]
  rw [show (2 * (i - j) : ℝ) = (2 * (i-j) : ℕ) by rw [Nat.cast_mul, Nat.cast_sub] <;> lia]
  apply sin_mul_θ_ne_zero
  lia


snip end

problem imo1975_p5 : constructible ↔
    ∃ p : Finset Circle, p.card = 1975 ∧ (SetLike.coe p).Pairwise (fun a b => ¬ Irrational (dist a b)) := by
  simp only [true_iff]
  use (Finset.range 1975).map ⟨P, P_injective⟩
  and_intros
  · simp
  · intro x hx y hy ne
    simp only [Finset.coe_map, Function.Embedding.coeFn_mk, Finset.coe_range, Set.mem_image, Set.mem_Iio] at hx hy
    grind only [not_irrational_dist_P_P]

end Imo1975P5
