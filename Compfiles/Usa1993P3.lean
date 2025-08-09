/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# USA Mathematical Olympiad 1993, Problem 3

Consider functions f : [0,1] → ℝ which satisfy

  (i)   f(x) ≥ 0 for all x ∈ [0,1]
  (ii)  f(1) = 1
  (iii) f(x) + f(y) ≤ f (x + y) whenever x, y and x + y are all in [0,1].

Determine the smallest constant c such that

       f(x) ≤ cx

for every function satisfying (i) - (iii) and every x ∈ [0,1].
-/

namespace Usa1993P3

snip begin

-- This lemma was proved automatically by Kimina-Prover 72B
theorem lemma1 (c1 : ℝ) :
  let f := fun x : (Set.Icc (0:ℝ) 1) ↦ if (x:ℝ) ≤ 1 / 2 then 0 else 1;
  (∀ (a : ℝ) (ha : 0 ≤ a ∧ a ≤ 1), f ⟨a, ha⟩ ≤ c1 * a) →
    (∀ (x : ↑(Set.Icc 0 1)), 0 ≤ f x) →
      f 1 = 1 → (∀ (x y : ↑(Set.Icc 0 1)) (h : (x:ℝ) + (y:ℝ) ∈ Set.Icc 0 1), f x + f y ≤ f ⟨↑x + ↑y, h⟩) → 2 ≤ c1 := by
  intro f h1 h2 h3 h4
  by_contra h
  push_neg at h
  have hc1 : c1 ≥ 0 := by
    have h1' := h1 (1 / 2 : ℝ) (by norm_num)
    have h5 : f ⟨(1 / 2 : ℝ), by norm_num⟩ = (0 : ℝ) := by
      simp [f]
    have h6 : (0 : ℝ) ≤ c1 * (1 / 2 : ℝ) := by
      have h7 : f ⟨(1 / 2 : ℝ), by norm_num⟩ ≤ c1 * (1 / 2 : ℝ) := by
        simpa using h1'
      rw [h5] at h7
      exact h7
    linarith
  have h9 : ∃ a : ℝ, a > (1 / 2 : ℝ) ∧ a ≤ (1 : ℝ) ∧ 1 > c1 * a := by
    use (1 + (2 - c1) / 4) / 2
    constructor
    · -- Show a > 1/2
      linarith
    constructor
    · -- Show a ≤ 1
      linarith
    · -- Show 1 > c1 * a
      linarith [sq_nonneg (c1 - 1), sq_nonneg ((1 + (2 - c1) / 4) / 2 - 1 / 2), hc1]
  rcases h9 with ⟨a, ha1, ha2, h10⟩
  have h1' := h1 a ⟨by linarith, ha2⟩
  have h5 : f ⟨a, ⟨by linarith, ha2⟩⟩ = 1 := by
    simp only [one_div, ite_eq_right_iff, zero_ne_one, imp_false, not_le, f]
    linarith
  have h6 : (1 : ℝ) ≤ c1 * a := by
    have h7 : f ⟨a, ⟨by linarith, ha2⟩⟩ ≤ c1 * a := by
      simpa using h1'
    rw [h5] at h7
    exact h7
  linarith

/-
This lemma was proved by GPT5, with some help from dwrensha to fix
up some errors.
-/
theorem lemma2 (f : ↑(Set.Icc 0 1) → ℝ) (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 1)
    (h1 : ∀ (x : ↑(Set.Icc 0 1)), 0 ≤ f x) (h2 : f 1 = 1)
    (h3 : ∀ (x y : ↑(Set.Icc 0 1)) (h : x.val + y.val ∈ Set.Icc 0 1),
               f x + f y ≤ f ⟨x.val + y.val, h⟩)
    (h4 : ∀ (x : ↑(Set.Icc (0:ℝ) 1)), 1 - x.val ∈ Set.Icc 0 1)
    (h5 : ∀ (x : ↑(Set.Icc (0:ℝ) 1)), f x + f ⟨1 - x.val, h4 x⟩ ≤ 1)
    (h6 : ∀ (x : ↑(Set.Icc (0:ℝ) 1)), f x ≤ 1) : f ⟨x, hx⟩ ≤ 2 * x := by
  classical
  -- First, show f(0) = 0 using h2, h5, and nonnegativity.
  have f0 : f ⟨0, by simp [Set.mem_Icc]⟩ = 0 := by
    have := h5 (1 : ↑(Set.Icc (0 : ℝ) 1))
    -- f 1 + f ⟨1-1, _⟩ ≤ 1  ⇒  1 + f 0 ≤ 1
    have : 1 + f ⟨0, by simp [Set.mem_Icc]⟩ ≤ 1 := by simpa [h2, sub_self] using this
    have h0le : f ⟨0, by simp [Set.mem_Icc]⟩ ≤ 0 := by linarith
    have h0ge : 0 ≤ f ⟨0, by simp [Set.mem_Icc]⟩ := h1 ⟨0, by simp [Set.mem_Icc]⟩
    exact le_antisymm h0le (by simpa using h0ge)

  -- Trivial case x = 0.
  by_cases hx0 : x = 0
  · subst hx0
    grind

  have hxpos : 0 < x := lt_of_le_of_ne' hx.1 hx0

  -- If x ≥ 1/2 the claim is immediate from h6.
  by_cases hxhalf : x ≤ (1 : ℝ) / 2
  · -- Small-x case: x ≤ 1/2. Set n = ⌊1/x⌋.
    let n : ℕ := Nat.floor (1 / x)

    -- n ≥ 1 because x ≤ 1 and x > 0 ⇒ 1 ≤ 1/x.
    have hn1 : 1 ≤ n := by
      have : (1 : ℝ) ≤ 1 / x := by
        -- for x > 0, 1 ≤ 1/x ↔ x ≤ 1
        bound
      exact (Nat.one_le_floor_iff (1 / x)).mpr this

    -- (n : ℝ) * x ≤ 1 (since n ≤ 1/x).
    have hnx_le1 : (n : ℝ) * x ≤ 1 := by
      have hnle : (n : ℝ) ≤ 1 / x := by
        have := Nat.floor_le (a := (1 / x)) (by positivity)
        grind
      exact (le_div_iff₀ hxpos).mp hnle

    -- (n : ℝ) * x ∈ [0,1].
    have hmem_nx : (n : ℝ) * x ∈ Set.Icc (0 : ℝ) 1 := by
      refine ⟨?_, hnx_le1⟩
      exact mul_nonneg (by exact_mod_cast (Nat.zero_le n)) hx.1

    -- 1 - (n : ℝ) * x ∈ [0,1].
    have hmem_one_minus : 1 - (n : ℝ) * x ∈ Set.Icc (0 : ℝ) 1 := by
      simp only [Set.mem_Icc, sub_nonneg, tsub_le_iff_right,
                 le_add_iff_nonneg_right] at hmem_nx ⊢
      grind

    -- Superadditivity iterated:  (n : ℝ) * f x ≤ f (n*x).
    have super_n : (n : ℝ) * f ⟨x, hx⟩ ≤ f ⟨(n : ℝ) * x, hmem_nx⟩ := by
      -- Prove by induction on n.
      revert hmem_nx
      refine Nat.rec ?base ?step n
      · intro _
        simp  -- n = 0
        grind
      · intro k ih hmem_k1
        -- split off the last x:  k*x ∈ [0,1] and (k+1)*x ∈ [0,1]
        have hmem_k : (k : ℝ) * x ∈ Set.Icc (0 : ℝ) 1 := by
          -- from (k+1)*x ≤ 1 we get k*x ≤ 1
          have hkp1_le1 : ((k : ℝ) + 1) * x ≤ 1 := by
            simpa [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, add_comm, add_left_comm, add_assoc,
                   mul_add, add_mul, one_mul]
              using hmem_k1.2
          have hk_le_hkp1 : (k : ℝ) * x ≤ ((k : ℝ) + 1) * x :=
            mul_le_mul_of_nonneg_right (by linarith : (k : ℝ) ≤ (k : ℝ) + 1) (le_of_lt hxpos)
          refine ⟨?_, hk_le_hkp1.trans hkp1_le1⟩
          exact mul_nonneg (by exact_mod_cast (Nat.zero_le k)) hx.1
        have sum_mem :
            (k : ℝ) * x + x ∈ Set.Icc (0 : ℝ) 1 := by
          -- this is exactly (k+1)*x ∈ [0,1]
          simpa [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, add_comm, add_left_comm, add_assoc,
                 mul_add, add_mul, one_mul]
            using hmem_k1
        have step1 :
            f ⟨(k : ℝ) * x, hmem_k⟩ + f ⟨x, hx⟩ ≤
            f ⟨(k : ℝ) * x + x, sum_mem⟩ :=
          h3 ⟨(k : ℝ) * x, hmem_k⟩ ⟨x, hx⟩ sum_mem
        have := ih (by grind)
        simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, add_mul]
        grind

    -- From h5 at n*x and nonnegativity, we get n*f(x) ≤ 1.
    have nfx_le_one : (n : ℝ) * f ⟨x, hx⟩ ≤ 1 := by
      have hsum : f ⟨(n : ℝ) * x, hmem_nx⟩ + f ⟨1 - (n : ℝ) * x, hmem_one_minus⟩ ≤ 1 :=
        h5 ⟨(n : ℝ) * x, hmem_nx⟩
      have fnonneg : 0 ≤ f ⟨1 - (n : ℝ) * x, hmem_one_minus⟩ := h1 _
      -- (n)*f(x) ≤ f(n*x) ≤ 1 - f(1 - n x) ≤ 1
      grind

    -- Divide by n > 0:  f(x) ≤ 1/n.
    have hfx_le_one_over_n : f ⟨x, hx⟩ ≤ 1 / (n : ℝ) := by
      have hnpos : 0 < (n : ℝ) := by exact_mod_cast lt_of_lt_of_le (by decide : (0 : ℕ) < 1) hn1
      -- a ≤ b/c  ↔  a*c ≤ b  (for c>0)
      exact (le_div_iff₀' hnpos).mpr nfx_le_one

    -- From 1/x < n + 1 (floor lemma), deduce 1/(n+1) < x, hence 2/(n+1) < 2x.
    have one_over_np1_lt_x : 1 / ((n : ℝ) + 1) < x := by
      have : 1 / x < (n : ℝ) + 1 := by
        simpa [n, Nat.cast_add, Nat.cast_one] using (Nat.lt_floor_add_one (1 / x))
      -- invert: 0 < 1/x and (1/x) < (n+1) ⇒ 1/(n+1) < x
      have hxinvpos : 0 < 1 / x := by simpa using inv_pos.mpr hxpos
      have hpp : 0 < ↑n + (1:ℝ)  := by positivity
      exact (one_div_lt hxpos hpp).mp this

    -- 1/n ≤ 2/(n+1)  (since n ≥ 1), and 2/(n+1) < 2x.
    have one_over_n_le_two_over_np1 : 1 / (n : ℝ) ≤ 2 / ((n : ℝ) + 1) := by
      -- Equivalent to: (n+1) ≤ 2n, which follows from 1 ≤ n.
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
      -- multiply both sides by 1/((n:ℝ)*((n:ℝ)+1)) > 0 to avoid case splits
      -- simpler: nlinarith does it directly
      have h' : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by nlinarith
      -- a/c ≤ b/d  with c,d>0  ↔  a*d ≤ b*c
      have hnpos : 0 < (n : ℝ) := by exact_mod_cast lt_of_lt_of_le (by decide : (0 : ℕ) < 1) hn1
      have hdenpos : 0 < (n : ℝ) + 1 := Nat.cast_add_one_pos n
      rw [div_le_div_iff₀ hnpos hdenpos]
      linarith
    have two_over_np1_le_twox : 2 / ((n : ℝ) + 1) ≤ 2 * x :=
      (le_of_lt (by
        have := one_over_np1_lt_x
        have hpos : 0 < (2 : ℝ) := by norm_num
        -- multiply the strict inequality by 2>0
        nth_rewrite 1 [show (2:ℝ) = 2 * 1 by norm_num]
        rw [mul_div_assoc]
        gcongr))

    -- Chain the estimates.
    exact
      (hfx_le_one_over_n.trans
        (one_over_n_le_two_over_np1.trans two_over_np1_le_twox))

  · -- Large-x case: x > 1/2, so 1 ≤ 2x and f x ≤ 1.
    have : (1 : ℝ) ≤ 2 * x := by
      have : (1 : ℝ) / 2 < x := lt_of_le_of_ne (le_of_not_ge hxhalf) (by grind)
      nlinarith
    have fx_le_one : f ⟨x, hx⟩ ≤ 1 := h6 ⟨x, hx⟩
    exact fx_le_one.trans this

snip end

def valid (f : Set.Icc (0 : ℝ) 1 → ℝ) : Prop :=
  (∀ x, 0 ≤ f x) ∧
  f 1 = 1 ∧
  ∀ x y, (h : x.val + y.val ∈ Set.Icc 0 1) → f x + f y ≤ f ⟨x.val + y.val, h⟩

determine min_c : ℝ := 2

problem usa1993_p5 :
    IsLeast {c | ∀ f, valid f → ∀ x, f x ≤ c * x } min_c := by
  simp only [Subtype.forall, Set.mem_Icc]
  constructor
  · simp only [Set.mem_setOf_eq]
    intro f hf x hx
    obtain ⟨h1, h2, h3⟩ := hf
    unfold min_c
    have h4 : ∀ x : Set.Icc (0:ℝ) 1, (1 - (x:ℝ)) ∈ Set.Icc (0:ℝ) 1 := by
       rintro ⟨x, hx⟩; exact unitInterval.mem_iff_one_sub_mem.mp hx
    have h5 : ∀ x, f x + f ⟨1 - x, h4 x⟩ ≤ 1 := by
      intro x
      specialize h3 x ⟨1 - x, h4 x⟩
      simp only [add_sub_cancel, Set.mem_Icc, zero_le_one, le_refl, and_self, Set.Icc.mk_one,
        forall_const] at h3
      grw [h3, h2]
    have h6 : ∀ x, f x ≤ 1 := fun x ↦ by
      specialize h5 x
      specialize h1 ⟨1 - x, h4 x⟩
      linarith
    have h8 : ∀ n : ℕ, ∀ x : Set.Icc (0:ℝ) (1/2^n), 2^n * (x : ℝ) ∈ Set.Icc (0:ℝ) 1 := by
      rintro n ⟨x, hx1, hx2⟩; clear h3; simp at hx ⊢
      refine ⟨hx1, ?_⟩
      grw [hx2]; simp
    exact lemma2 f x hx h1 h2 h3 h4 h5 h6
  · rw [mem_lowerBounds]
    intro c1 hc1
    simp only [Set.mem_setOf_eq] at hc1
    let f : Set.Icc (0 : ℝ) 1 → ℝ := fun x ↦ if x.val ≤ 1/2 then 0 else 1
    have hf : valid f := by
      refine ⟨?_, ?_, ?_⟩
      · intro x
        unfold f
        split <;> norm_num
      · unfold f; norm_num
      · intro x y hx
        obtain ⟨x, hxx⟩ := x
        obtain ⟨y, hyy⟩ := y
        simp only [Set.mem_Icc] at hx hxx hyy
        obtain ⟨hx1, hx2⟩ := hx
        unfold f
        split_ifs with h1 h2 h3 h4 h5 h6 <;> linarith
    specialize hc1 f hf
    obtain ⟨h1, h2, h3⟩ := hf
    exact lemma1 c1 hc1 h1 h2 h3


end Usa1993P3
