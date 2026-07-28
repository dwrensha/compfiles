/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pacmanboss256
-/

module

public import Mathlib.Tactic

public import ProblemExtraction
import Mathlib.Analysis.SpecialFunctions.Log.Base

@[expose] public section

/-!
# USA Mathematical Olympiad 2016 P4
Find all functions f : ℝ → ℝ such that for all x, y ∈ ℝ:
(f(x)+xy) · f(x-3y) + (f(y)+xy) · f(3x-y) = (f(x+y))^2

-/

namespace USA2016P4
def f_good (f : ℝ → ℝ) : Prop :=  ∀ x y, (f x + x*y) * f (x - 3*y) + (f y + x * y) * f (3*x - y) = (f (x+y))^2

snip begin
/-roughly follows https://artofproblemsolving.com/wiki/index.php/2016_USAMO_Problems/Problem_4 and https://web.evanchen.cc/exams/USAMO-2016-notes.pdf
the hard part is proving no other solutions work
-/
variable (f: ℝ→ℝ) (hf : f_good f)
include f hf


theorem f_zero: f 0 = 0 := by
    specialize hf 0 0
    simp at hf
    rw [← pow_two, ← two_mul] at hf
    apply eq_zero_of_mul_eq_self_left (by norm_num) at hf
    rw [sq_eq_zero_iff] at hf
    assumption

theorem f_t_even : ∀t, f t ≠ 0 → f t = f (-t) := by
    intro t y_ne_zero
    have hf_c := hf
    specialize hf 0 t
    rw [f_zero f] at hf
    swap; · assumption
    simp at hf
    rw [pow_two] at hf
    rw [mul_eq_mul_left_iff] at hf
    obtain hl | hr := hf
    · symm
      assumption
    contradiction


lemma f_even_zero : ∀t, f t = 0 → f (-t) = 0 := by
    intro t
    have hf_c := hf
    specialize hf 0 (-t)
    rw [f_zero f] at hf
    swap; · assumption
    simp at hf
    rw [pow_two] at hf
    rw [mul_eq_mul_left_iff] at hf
    intro ftz
    obtain hl | hr := hf
    · rw [← hl]
      assumption
    assumption



theorem f_even : ∀t, f t = f (-t) := by
  intro t
  by_cases hfz : f t = 0
  · have hnfz := f_even_zero f hf t hfz
    rw [hfz, hnfz]
  push Not at hfz
  apply f_t_even at hfz
  · assumption
  assumption

theorem f_half_zero : ∀t, f t = 0 → f (t/2) = 0 := by
  intro t ftz
  have hf_c := hf
  specialize hf (3*(t/8)) (t/8)
  ring_nf at hf
  rw [f_zero f] at hf
  · simp at hf
    rw [← mul_rotate, ← add_mul] at hf
    ring_nf at hf
    rw [← mul_rotate, ← add_mul] at hf
    rw [ftz] at hf
    simp at hf
    rw [← div_eq_mul_inv] at hf
    symm at hf
    rw [sq_eq_zero_iff] at hf
    assumption
  assumption


lemma eq_2 (t:ℝ) : f t + f (-t) - 2 * t ^ 2 = 0 ∨ f (4 * t) = 0 := by
  have hf_c := hf
  specialize hf t (-t)
  simp at hf
  rw [f_zero f] at hf
  swap; · assumption
  ring_nf at hf
  nth_rw 6 [mul_comm] at hf
  rw [← mul_rotate] at hf
  have factor : ∀t, f t * f (t * 4) - 2 * t ^ 2 * f (t * 4) + f (-t) * f (t * 4) = (f t + f (-t) - 2*t^2) * f (4*t) := by
      intro t
      rw [← mul_sub_right_distrib, ← add_mul]
      ring_nf
  rw [factor, mul_eq_zero] at hf
  assumption

theorem hf_opts : ∀t, f t = t^2 ∨ f t = 0 := by
    intro t
    have eq_2 := eq_2 f hf t
    by_cases hf_zero : f t = 0
    · right; assumption
    push Not at hf_zero
    rcases eq_2 with sq | z
    · left
      apply f_t_even at hf_zero
      swap; · assumption
      rw [← hf_zero, ← two_mul, ← mul_sub] at sq
      simp at sq
      rw [sub_eq_zero] at sq
      assumption
    right
    have : f (2 * t) = 0 := by
      apply f_half_zero at z
      · ring_nf at z
        rw [mul_comm] at z
        assumption
      assumption
    apply f_half_zero at this
    swap; · assumption
    ring_nf at this
    assumption

lemma eq_3 : ∀t, (f t + 3*t^2) * f (t*8) = f (t*4)^2 := by
  intro t
  have hf_c := hf
  specialize hf (3*t) t
  ring_nf at hf
  rw [f_zero f] at hf
  swap; · assumption
  simp at hf
  rw [← mul_rotate, ← add_mul, add_comm] at hf
  assumption

theorem f_two_zero : ∀t, f t = 0 → f (2 * t) = 0 := by
  have l2 : ∀t, f (t * 4) = 0 → f (t * 8) = 0 := by
    intro t ftz
    have eq_3 := eq_3
    specialize eq_3 f
    simp [hf] at eq_3
    specialize eq_3 t
    simp [ftz] at eq_3
    rcases eq_3 with sq | triv
    · by_cases htz : t = 0
      · rw [htz]
        simp
        apply f_zero f hf
      push Not at htz
      apply f_half_zero at ftz
      · apply f_half_zero at ftz
        · ring_nf at ftz
          rw [ftz] at sq
          simp at sq
          contradiction
        assumption
      assumption
    assumption

  intro t
  specialize l2 (t/4)
  ring_nf at l2
  rw [mul_comm]
  exact l2

theorem f_ge_zero : ∀t, f t ≥ 0 := by
  intro t
  have hf_opts := hf_opts f hf t
  rcases hf_opts with hl | hr
  · rw [hl]
    apply sq_nonneg
  rw [hr]


/-if a ≠ 0 and f a = 0 then wlog a > 0-/
theorem ha_zero: ∀(_:ℝ), ((∃a, a ≠ 0 ∧ f a = 0)↔ ∃ a > 0, f a = 0) := by
  intro t
  constructor
  · intro h
    obtain ⟨a, a_ne_z, f_a_z⟩ := h
    have f_even_zero := f_even_zero f hf a
    have f_nega_z := f_even_zero f_a_z
    have fa_even : f a = f (-a) := by
      rw [← f_a_z] at f_nega_z
      symm
      assumption
    by_cases ha: a > 0
    · use a
    push Not at ha
    by_cases ha' : a < 0
    · use -a
      constructor
      · linarith
      assumption
    push Not at ha'
    have : a = 0 := by linarith
    contradiction
  intro h
  obtain ⟨a, a_pos, f_a_z⟩ := h
  use a
  constructor
  · linarith
  assumption

/-The main part, proving that if there is some nonzero a such that f a = 0 then we must have f b = 0 for all b-/
theorem f_eq_zero_if_not_sq : ∀(b:ℝ),(∃a, a≠0 ∧ f a = 0) → f b = 0 := by
    intro b
    by_cases hbz : b = 0
    · intro h
      rw [hbz]
      apply f_zero f hf
    wlog hb: 0 < b generalizing b with H
    · push Not at hb
      rw [← neg_zero, le_neg] at hb
      specialize H (-b)
      by_cases hb' : 0 < -b
      · apply H at hb'
        · intro ex
          apply hb' at ex
          rw [f_even f hf]
          assumption
        push Not
        rw [neg_ne_zero]
        assumption
      push Not at hb'
      simp at hb hb'
      have : b = 0 := by linarith
      contradiction

    intro h
    have ha_zero := ha_zero f hf b
    rw [ha_zero] at h
    obtain ⟨a, a_pos, f_a_zero⟩ := h
    have hab_pos : b/a > 0 := by
        apply div_pos
        · assumption
        assumption

    let c:ℝ := 2 * a * 2 ^ (⌈Real.logb 2 (b/a)⌉)

    have cb_pos : c > b := by
      have cbtrans : b < 2 * a * 2 ^ ((Real.logb 2 (b/a))) := by
        rw [← div_lt_iff₀', Real.rpow_logb]
        · field_simp; linarith
        · linarith
        · linarith
        · assumption
        linarith

      have ceil_trans :  2 * a * (2 ^ (Real.logb 2 (b/a))) ≤ 2 * a * (2 ^ (⌈Real.logb 2 (b/a)⌉)):= by
        rw [mul_le_mul_iff_right₀]
        · have : Real.logb 2 (b/a) ≤ ⌈Real.logb 2 (b/a)⌉ := by
           apply Int.le_ceil
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) at this
          rw [← Real.rpow_intCast]
          exact this
        linarith
      linarith

    have f_two_pow_zero : ∀(t: ℝ), ∀(n: ℤ), f t = 0 → (f (2^n * t) = 0):= by
      intro t n hft
      induction n using Int.induction_on with
      | zero => simp; assumption
      | succ i ih =>
        norm_cast
        rw [pow_add]
        simp
        nth_rw 2 [mul_comm]
        apply f_two_zero at ih
        · rw [← mul_assoc] at ih
          assumption
        assumption
      | pred i ih =>
        rw [← neg_add', zpow_neg]
        norm_cast
        rw [pow_add]
        push_cast
        rw [mul_inv, mul_rotate,inv_mul_eq_div]
        norm_cast at ih
        rw [zpow_neg, mul_comm] at ih
        norm_num at ih
        apply f_half_zero at ih
        · rw [mul_div_right_comm] at ih
          assumption
        assumption





    have f_c_zero : f c = 0 := by
      change f (2 * a * 2 ^ (⌈Real.logb 2 (b/a)⌉)) = 0
      have hh1 : f (a * 2 ^ (⌈Real.logb 2 (b/a)⌉)) = 0 := by
        specialize f_two_pow_zero a (⌈Real.logb 2 (b / a)⌉)
        apply f_two_pow_zero at f_a_zero
        rw [mul_comm]
        assumption
      apply f_two_zero at hh1
      · rw [← mul_assoc] at hh1
        assumption
      assumption

    have hf_c := hf
    specialize hf_c ((3*c+b)/4) ((c-b)/4)
    let x' := ((3*c+b)/4)
    let y' := ((c-b)/4)

    change (f x' + x'*y')* f ((3 * c + b) / 4 - 3 * ((c - b) / 4)) + (f y' + x'*y')* f (3*x' - y') = f ((3 * c + b) / 4 + (c - b) / 4) ^ 2 at hf_c
    ring_nf at hf_c
    rw [f_c_zero] at hf_c
    simp at hf_c
    rw [← add_mul,add_assoc,← add_mul] at hf_c
    have x_prime_pos : x' > 0 := by
      unfold x'
      linarith
    have y_prime_pos : y' > 0 := by
      unfold y'
      linarith
    have xyprime_pos : x'*y' > 0 := by apply Right.mul_pos x_prime_pos y_prime_pos
    have t1 : 0 ≤ (x' * y' + f y') * f (x' * 3 - y') := by
      rw [mul_nonneg_iff]
      left
      constructor
      · have t1: f y' ≥ 0 := by apply f_ge_zero f hf y'
        linarith
      apply f_ge_zero f hf (x'*3-y')

    have t2 : (f x' + x' * y') * f b ≤ (f x' + x' * y') * f b + (x' * y' + f y') * f (x' * 3 - y') := by linarith
    rw [hf_c] at t2
    have fb_zero : f b = 0 := by
      have lpos: (f x' + x' * y') > 0 := by
        have : f x' ≥ 0 := by apply f_ge_zero f hf x'
        linarith
      rw [mul_nonpos_iff] at t2
      rcases t2 with pos_neg | neg_pos
      · obtain ⟨_, fb_neg⟩ := pos_neg
        have fb_ge_zero : f b ≥ 0 := by apply f_ge_zero f hf b
        linarith
      obtain ⟨l,r⟩ := neg_pos
      apply not_le_of_gt at lpos
      contradiction
    assumption

determine solution_set : Set (ℝ → ℝ) := {fun t ↦ 0, fun t ↦ t^2}

snip end

omit hf in
problem usa2016p4:
    f ∈ solution_set ↔ f_good f := by
  constructor
  /- Prove solutions in set satisfy requirements-/
  · intro h_mem x y
    rcases h_mem with z | sq
    · simp [z]
    simp at sq
    simp [sq]
    ring_nf
  /-Prove no other solutions work, namely if not x^2 then it has to be the zero-/
  intro hf
  unfold f_good at hf
  have hf_c := hf
  simp

  have f_opts := hf_opts f hf
  have f_eq_zero_or_sq := f_eq_zero_if_not_sq f hf
  have f_zero := f_zero f hf
  by_cases hfun: f = fun _ ↦ 0
  · left
    assumption
  right
  funext w
  have eq_2 := eq_2 f hf w
  rw [← f_even f hf w] at eq_2
  ring_nf at eq_2
  rw [← sub_mul] at eq_2
  rcases eq_2 with sq | zero
  · rw [mul_eq_zero] at sq
    rcases sq with triv | imp
    · rw [sub_eq_zero] at triv
      assumption
    linarith
  by_cases hw : w = 0
  · simp [hw]
    assumption
  apply f_half_zero at zero
  · apply f_half_zero at zero
    · ring_nf at zero
      push Not at hw
      simp at f_eq_zero_or_sq
      rw [forall_comm] at f_eq_zero_or_sq
      specialize f_eq_zero_or_sq w
      simp [hw, zero] at f_eq_zero_or_sq
      by_contra hn'
      apply hfun
      funext n
      specialize f_eq_zero_or_sq n
      assumption
    assumption
  assumption

end USA2016P4
