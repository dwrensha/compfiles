/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 2002, Problem 5

Determine all functions f : ℝ → ℝ such that

  (f(x) + f(z))(f(y) + f(t)) = f(xy - zt) + f(xt + yz)

for all real numbers x,y,z,t.
-/

namespace Imo2002P5

snip begin

lemma extend_function_mono
    {u f : ℝ → ℝ}
    (u_mono : ∀ x y, 0 ≤ x → x ≤ y → u x ≤ u y)
    (f_cont : Continuous f)
    (h : ∀ x : ℚ, u x = f x)
    (x : ℝ) (xpos : 0 < x) :
    u x = f x := by
  by_contra! hx
  let ε : ℝ := |u x - f x|
  have hε : 0 < ε := abs_sub_pos.mpr hx

  -- then find a δ such that for all z, |z-x| < δ implies that
  -- |f z - f x| < ε.
  obtain ⟨δ, hδ0, hδ⟩ := Metric.continuous_iff.mp f_cont x ε hε
  obtain h1 | h2 | h3 := lt_trichotomy (u x) (f x)
  · -- pick a rational point less than x that's in the ball s,
    -- and greater than zero
    have : ∃ z : ℚ, (z:ℝ) < x ∧ dist (z:ℝ) x < δ ∧ 0 < (z:ℝ) := by
      obtain h3 | h4 := le_or_lt x δ
      · obtain ⟨z, hz1, hz2⟩ := exists_rat_btwn xpos
        refine ⟨z, hz2, ?_⟩
        rw [Real.dist_eq, abs_sub_comm, abs_of_pos (sub_pos.mpr hz2)]
        constructor
        · linarith
        · linarith
      have hxδ : x - δ < x := sub_lt_self x hδ0
      obtain ⟨z, hz1, hz2⟩ := exists_rat_btwn hxδ
      refine ⟨z, hz2, ?_⟩
      rw [Real.dist_eq, abs_sub_comm, abs_of_pos (sub_pos.mpr hz2)]
      constructor
      · linarith
      · linarith

    obtain ⟨z, h_z_lt_x, hxz, zpos⟩ := this
    -- then dist (f z) (f x) < ε.
    have hbzb := hδ z hxz
    rw [←h z] at hbzb
    have huzuy : u x < u z := by
      have hufp : u x - f x < 0 := by linarith
      have hua : ε = -(u x - f x) := abs_of_neg hufp
      rw [hua, Real.dist_eq] at hbzb
      obtain h5 | h6 := em (f x < u z)
      · linarith
      · have : u z - f x ≤ 0 := by linarith
        rw[abs_eq_neg_self.mpr this] at hbzb
        linarith
    -- so u(z) < u(x), contradicting u_mono.
    have := u_mono z x zpos.le h_z_lt_x.le
    linarith
  · exact hx h2
  · -- pick a rational point z greater than x that's in the ball s,
    have : ∃ z : ℚ, x < z ∧ dist (z:ℝ) x < δ := by
      have hxδ : x < x + δ := lt_add_of_pos_right x hδ0
      obtain ⟨z, hz1, hz2⟩ := exists_rat_btwn hxδ
      refine ⟨z, hz1, ?_⟩
      rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hz1)]
      exact sub_left_lt_of_lt_add hz2
    obtain ⟨z, h_x_lt_z, hxz⟩ := this
    -- then dist (f z) (f y) < ε.
    have hbzb := hδ z hxz
    rw [←h z] at hbzb
    have huzuy : u z < u x := by
      have hufp : 0 < u x - f x := by linarith
      have hua : ε = u x - f x := abs_of_pos hufp
      rw [hua, Real.dist_eq] at hbzb
      cases em (f x < u z)
      · have : 0 ≤ u z - f x := by linarith
        rw[abs_eq_self.mpr this] at hbzb
        linarith
      · linarith
    -- so u(z) < u(x), contradicting u_mono.
    have := u_mono x z xpos.le h_x_lt_z.le
    linarith

snip end

determine SolutionSet : Set (ℝ → ℝ) :=
  { fun x ↦ 0, fun x ↦ 1/2, fun x ↦ x^2 }

problem imo2002_p5 (f : ℝ → ℝ) :
    f ∈ SolutionSet ↔
    ∀ x y z t, (f x + f z) * (f y + f t) =
               f (x * y - z * t) + f (x * t + y * z) := by
  -- solution from https://web.evanchen.cc/exams/IMO-2002-notes.pdf
  simp only [Set.mem_insert_iff, one_div, Set.mem_singleton_iff]
  constructor
  · intro hf x y z t
    obtain rfl | rfl | rfl := hf
    · simp
    · norm_num1
    · ring
  intro hf
  have h1 : ∀ x, f x = f (-x) := fun x ↦ by
    have h2 := hf x 1 0 0
    have h3 := hf 0 0 1 x
    ring_nf at h2 h3
    linarith
  by_cases h2 : ∃ y, ∀ x, f x = y
  · -- f is constant
    obtain ⟨y, hy⟩ := h2
    have h3 := hf 0 0 0 0
    simp only [hy] at h3
    suffices h4 : y = 0 ∨ y = 1/2 by
      obtain rfl | rfl := h4
      · left; ext x
        exact hy x
      · right; left; ext x
        simp only [hy x, one_div]
    have h5 : y * (2 * y - 1) = 0 := by linarith only [h3]
    rw [mul_eq_zero] at h5
    cases' h5 with h6 h6
    · left; exact h6
    · right; linarith
  right; right
  push_neg at h2
  have h3 : f 0 = 0 := by
    obtain ⟨y1, hy1⟩ := h2 (1/2)
    have h4 := fun y t ↦ hf 0 y 0 t
    simp only [zero_mul, sub_self, mul_zero, add_zero] at h4
    have h5 : f y1 + f y1 ≠ 1 := by
      intro H
      apply_fun (·/2) at H
      field_simp at H
      have H' : f y1 = 1 /2 := by linarith
      contradiction
    contrapose! h5
    replace h5 : f 0 + f 0 ≠ 0 := by
      contrapose! h5; linarith only [h5]
    have h6 := h4 y1 y1
    rw [mul_eq_left₀ h5] at h6
    exact h6
  have h4 : ∀ x y, f (x * y) = f x * f y := fun x y ↦ by
    have h5 := hf x y 0 0
    simp only [mul_zero, sub_zero, add_zero, h3] at h5
    exact h5.symm
  have h5 : ∀ x, 0 ≤ f x := fun x ↦ by
    have h6 : f x = f |x| := by
      obtain h7 | h7 := abs_choice x
      · rw [h7]
      · rw [h7, h1]
    have h8 : |x| = (Real.sqrt |x|)^2 := by
      exact (Real.sq_sqrt (by positivity)).symm
    rw [h6, h8, sq, h4, ←sq]
    positivity
  have h6 : ∀ v u, 0 ≤ v → v ≤ u → f v ≤ f u := by
    intro v u hv0 hvu
    have h7 : ∀ x y, (f x + f y)^2 = f (x^2 + y^2) := fun x y ↦ by
      have h8 := hf x y y x
      have h9 : x * y - y * x = 0 := by ring
      rw [h9, h3, zero_add, ←sq, ←sq] at h8
      linarith only [h8]
    have h8 := h7 (Real.sqrt v) (Real.sqrt (u - v))
    have h9 : 0 ≤ u - v := sub_nonneg_of_le hvu
    rw [Real.sq_sqrt (by positivity)] at h8
    rw [Real.sq_sqrt (by positivity)] at h8
    rw [add_sub_cancel] at h8
    have h10 : (f √v) ^2 + (f √(u - v))^2 + 2 * f √v * f √(u - v) =
              (f √v + f √(u - v)) ^ 2 := by ring
    have h11 : (f √v) ^2 ≤ (f √v + f √(u - v)) ^ 2 := by
      rw[←h10]
      have h12 := h5 (√v)
      have h13 := h5 (√(u - v))
      nlinarith
    rw [h8, sq, ←h4, ←sq, Real.sq_sqrt (by positivity)] at h11
    exact h11
  ext x
  wlog h7 : 0 ≤ x generalizing x with H
  · have h8 := H (-x) (by linarith)
    rw [←h1] at h8
    rw [h8]
    exact neg_pow_two x
  -- For the rest of the proof we follow John Scholes
  -- https://prase.cz/kalva/imo/isoln/isoln025.html
  have h8 : f 1 = 1 := by
    have h9 := hf 0 1 1 1
    simp [h3, ←h1] at h9
    have h10 : f 1 + f 1 ≠ 0 := by
      intro H
      have h11 : f 1 = 0 := by linarith only [H]
      obtain ⟨y0, hy0⟩ := h2 0
      have h12 := hf 1 1 y0 0
      simp only [h11, zero_add, h3, zero_mul, mul_zero, one_mul, sub_zero] at h12
      exact hy0.symm h12
    exact (mul_eq_right₀ h10).mp h9
  have h9 : ∀ n : ℕ, f n = n^2 := fun n ↦ by
    induction' n using Nat.strongRecOn with n ih
    cases' n with n
    · simp [h3]
    cases' n with n
    · simp [h8]
    have h10 := hf n.succ 1 1 1
    have h12 := ih n.succ (Nat.lt.base _)
    have h11 := ih n (by omega)
    rw[h12] at h10
    simp [ih, h8, h11] at h10
    push_cast at h10 ⊢
    linarith only [h10]
  have h10 : ∀ z : ℤ, f z = z^2 := fun z ↦ by
    obtain ⟨m, rfl | hm⟩ := Int.eq_nat_or_neg z
    · norm_cast at h9 ⊢; rw [h9]
    · rw[hm]; push_cast; rw[←h1, h9]; simp only [even_two, Even.neg_pow]
  have h11 : ∀ q : ℚ, f q = q^2 := fun q ↦ by
    have h12 := h4 q q.den
    rw [h9] at h12
    have h13 : q * q.den = q.num := Rat.mul_den_eq_num q
    have h14 : (((q * (q.den : ℚ)):ℚ):ℝ) = (q:ℝ) * (q.den:ℝ) := by norm_cast
    rw [←h14, h13, Rat.cast_intCast] at h12
    rw [h10] at h12
    have h15 : (q:ℚ) = (q.num : ℝ) / (q.den : ℝ) := by
      norm_cast; exact (Rat.divInt_self q).symm
    have h16 : (q.num:ℝ)^2 / (q.den : ℝ)^2 = q^2 := by
      rw[h15]; field_simp
    rw [←h16]
    have h17 : (q.den : ℝ)^2 ≠ 0 := by positivity
    exact eq_div_of_mul_eq h17 h12.symm
  obtain rfl | h7' :=  h7.eq_or_gt
  · simp [h3]
  have h12 := extend_function_mono (f := fun x ↦ x^2) h6 (continuous_pow 2) h11 x h7'
  simp [h12]



end Imo2002P5
