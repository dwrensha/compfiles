/-
Copyright (c) 2023 Gian Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Sanjaya
-/

import Mathlib.Algebra.Order.Positive.Field
import Mathlib.Data.Nat.Periodic
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 2009, Problem 5

Determine all functions f: ℤ>0 → ℤ>0 such that for all positive integers a and b,
the numbers

  a, f(b), and f(b + f(a) - 1)

form the sides of a nondegenerate triangle.
-/

namespace Imo2009P5

snip begin

-- Solution adapted from
-- https://github.com/mortarsanjaya/imo-A-and-N/blob/main/src/IMO2009/A3/A3.lean

section extra_lemmas

lemma exists_sup_fn_fin (f : ℕ → ℕ) (c : ℕ) : ∃ K : ℕ, ∀ n : ℕ, n < c → f n ≤ K := by
  induction' c with c ih
  · simp
  · obtain ⟨k, hk⟩ := ih
    use max k (f c)
    intro n hn
    obtain hlt | rfl := Nat.lt_succ_iff_lt_or_eq.mp hn <;> aesop

private lemma pnat_to_nat_prop {P : ℕ+ → Prop} :
  (∀ n : ℕ+, P n) ↔ (∀ n : ℕ, P n.succPNat) :=
  ⟨λ h n ↦ h n.succPNat, λ h n ↦ by rw [← PNat.succPNat_natPred n]; exact h _⟩

private lemma pnat_to_nat_prop2 {P : ℕ+ → ℕ+ → Prop} :
  (∀ m n : ℕ+, P m n) ↔ (∀ m n : ℕ, P m.succPNat n.succPNat) :=
  by rw [pnat_to_nat_prop]; refine forall_congr' (λ m ↦ ?_); rw [pnat_to_nat_prop]

private lemma succ_pnat_add_succ_pnat (m n : ℕ) :
  m.succPNat + n.succPNat = (m + n).succPNat + 1 :=
  by rw [← PNat.coe_inj, PNat.add_coe, PNat.add_coe, Nat.succPNat_coe, Nat.succPNat_coe,
         Nat.succPNat_coe, Nat.add_succ, Nat.succ_add]
     rfl

private lemma pnat_add_sub_cancel (m n : ℕ+) : m + n - n = m :=
  by rw [← add_right_inj n, PNat.add_sub_of_lt (n.lt_add_left m), add_comm]

end extra_lemmas

/-- Final solution, `nat` version -/
theorem final_solution_nat (f : ℕ → ℕ) :
  ((∀ x y : ℕ, f (y + f x) ≤ f y + x)
    ∧ (∀ x y : ℕ, x ≤ f y + f (y + f x))
    ∧ (∀ x y : ℕ, f y ≤ f (y + f x) + x))
      ↔ f = λ x ↦ x := by
  ---- First, the easier direction: `←`
  symm; constructor
  · rintro rfl
    refine ⟨λ x y ↦ le_refl (y + x), λ x y ↦ ?_, λ x y ↦ ?_⟩
    · rw [← add_assoc]; exact le_add_self
    rw [add_assoc]; exact le_self_add

  ---- For the harder case, first prove that `f(0) = 0`
  rintro ⟨h, h0, h1⟩
  replace h1 : f 0 = 0 := by
    contrapose! h0; rw [← zero_lt_iff] at h0
    obtain ⟨K, h2⟩ := exists_sup_fn_fin f (f 0)
    refine ⟨K + K + 1, 0, Nat.lt_succ_of_le (add_le_add (h2 0 h0) ?_)⟩
    rw [zero_add, ← Function.Periodic.map_mod_nat (λ y ↦ le_antisymm (h 0 y) (h1 0 y))]
    exact h2 _ (Nat.mod_lt (f (K + K + 1)) h0)

  ---- Now get `f(f(x)) = x` for all `x`
  replace h0 : ∀ x : ℕ, f (f x) = x := by
    intros x; apply le_antisymm
    replace h := h x 0
    rwa [h1, zero_add, zero_add] at h
    replace h0 := h0 x 0
    rwa [h1, zero_add, zero_add] at h0

  ---- Get `f(x + f(1)) ≤ f(x) + 1` and then `f(1) = 1`
  replace h := h 1
  have h2 : f 1 = 1 := by
    suffices this : ∀ n : ℕ, f (n * f 1) = n by
      replace this := congr_arg f (this (f 1))
      rw [h0, h0] at this
      exact Nat.eq_one_of_mul_eq_one_left this

    intro n
    induction' n using Nat.strong_induction_on with n n_ih
    cases' n with n
    · simp[h1]
    · replace h := h (n * f 1)
      rw [n_ih n n.lt_succ_self, ← add_one_mul, le_iff_eq_or_lt, Nat.lt_succ_iff] at h
      revert h; refine (or_iff_left_of_imp (λ h ↦ ?_)).mp
      replace n_ih := congr_arg f (n_ih _ (lt_of_le_of_lt h n.lt_succ_self))
      rw [h0, h0, mul_eq_mul_right_iff] at n_ih
      revert n_ih; refine (or_iff_left ?_).mp
      rw [← h1]; apply_fun f
      rw [h0, h0]; exact one_ne_zero

  ---- Finish
  funext x
  induction' x using Nat.strong_induction_on with x x_ih
  cases' x with x
  · exact h1
  replace h := h x
  rw [h2, x_ih x x.lt_succ_self, le_iff_eq_or_lt, Nat.lt_succ_iff] at h
  revert h; refine (or_iff_left_of_imp (λ h ↦ ?_)).mp
  replace x_ih := congr_arg f (x_ih _ (lt_of_le_of_lt h x.lt_succ_self))
  rwa [h0, h0] at x_ih

/-- Final solution, `pnat` version -/
theorem final_solution_pnat (f : ℕ+ → ℕ+) :
    ((∀ x y : ℕ+, f (y + f x - 1) < f y + x)
      ∧ (∀ x y : ℕ+, x < f y + f (y + f x - 1))
      ∧ (∀ x y : ℕ+, f y < f (y + f x - 1) + x))
        ↔ f = λ x ↦ x := by
  obtain ⟨g, rfl⟩ : ∃ g : ℕ → ℕ, f = λ x ↦ (g x.natPred).succPNat :=
    ⟨λ x ↦ (f x.succPNat).natPred,
      funext (λ x ↦ by rw [PNat.succPNat_natPred, PNat.succPNat_natPred])⟩
  simp_rw [pnat_to_nat_prop2, Function.funext_iff, pnat_to_nat_prop, Nat.natPred_succPNat,
           Nat.succPNat_inj, ← Function.funext_iff, succ_pnat_add_succ_pnat, pnat_add_sub_cancel,
           Nat.natPred_succPNat, PNat.lt_add_one_iff, Nat.succPNat_le_succPNat]
  exact final_solution_nat g

snip end

determine solution_set : Set (ℕ+ → ℕ+) := { id }

problem imo2009_p5 (f : ℕ+ → ℕ+) :
    f ∈ solution_set ↔
    ∀ a b, (f (b + f a - 1) < f b + a ∧
            a < f b + f (b + f a - 1) ∧
            f b < f (b + f a - 1) + a) := by
  have fsn := final_solution_pnat f
  constructor
  · rintro rfl a b
    obtain ⟨h1, h2, h3⟩ := fsn.mpr rfl
    exact ⟨h1 a b, h2 a b, h3 a b⟩
  · intro h
    rw [Set.mem_singleton_iff]
    apply fsn.mp
    refine ⟨?_,?_,?_⟩
    · intro a b; exact (h a b).1
    · intro a b; exact (h a b).2.1
    · intro a b; exact (h a b).2.2
