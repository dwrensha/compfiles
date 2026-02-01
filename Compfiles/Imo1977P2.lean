/-
Copyright (c) 2026 Constantin Seebach. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Constantin Seebach
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file

/-!
# International Mathematical Olympiad 1977, Problem 2

In a finite sequence of real numbers the sum of any seven successive terms is negative and the sum of any eleven successive terms is positive.
Determine the maximum number of terms in the sequence.

-/

namespace Imo1977P2

def sum_successive_terms {α : Type} [AddCommMonoid α] {n : ℕ} (s : Fin n → α) (start : Fin n) (count : ℕ) [NeZero count] (h : start+count-1 < n) : α :=
  ∑ i ∈ Finset.Icc start ⟨start+count-1, h⟩, s i


snip begin


open Matrix

@[coe]
def coeFunctionInt2Real {α : Type*} (f : α → ℤ) : (α → ℝ) := fun x => (f x).cast

instance {α : Type*} : Coe (α → ℤ) (α → ℝ) := {
  coe := coeFunctionInt2Real
}

theorem sum_successive_terms_intCast {n : ℕ} (s : Fin n → ℤ) (start : Fin n) (count : ℕ) [NeZero count] (h : start+count-1 < n) :
    sum_successive_terms s start count h = (sum_successive_terms s start count h : ℝ) := by
  unfold sum_successive_terms coeFunctionInt2Real
  simp

def example_16_int : Fin 16 → ℤ := ![5, 5, -13, 5, 5, 5, -13, 5, 5, -13, 5, 5, 5, -13, 5, 5]

def example_16 : Fin 16 → ℝ := (example_16_int : Fin 16 → ℝ)


snip end


determine max_num_terms : ℕ := 16

problem imo1977_p2 :
    Maximal (λn ↦ ∃ s : Fin n → ℝ, ∀ i0, (∀ h7, sum_successive_terms s i0 7 h7 < 0) ∧ (∀ h11, sum_successive_terms s i0 11 h11 > 0)) max_num_terms := by
  rw [maximal_iff_forall_gt]
  and_intros
  · use example_16
    intro i0
    and_intros <;> {
      intro _
      unfold example_16
      rw [<-sum_successive_terms_intCast]
      simp only [gt_iff_lt, Int.cast_pos, Int.cast_lt_zero]
      decide +revert
    }
  · intro n ngt
    have := NeZero.of_gt ngt
    simp only [Nat.add_one_sub_one, gt_iff_lt, not_exists, not_forall, not_and, not_lt]
    intro x
    by_contra! c

    let A : Matrix (Fin 7) (Fin 11) ℝ :=
      fun (i) (j) ↦ x ⟨i.val+j.val, by lia⟩

    have rneg : ∀ j, (1 ᵥ* A) j < 0 := by
      intro j
      unfold A
      rw [Matrix.vecMul_eq_sum]
      simp only [Finset.sum_apply]
      have := (c (j.castLT (by lia))).left (by rw [Fin.val_castLT]; lia)
      unfold sum_successive_terms at this
      apply this.trans_eq'
      apply Finset.sum_bij' (fun x h => ⟨x.val-j.val, by grind⟩) (fun y _ => ⟨j.val+y.val, by lia⟩) <;> {
        simp <;> grind only [= Fin.val_castLT, = Lean.Grind.toInt_fin, = Finset.mem_Icc]
      }

    have cpos : ∀ j, (A *ᵥ 1) j > 0 := by
      intro j
      unfold A
      rw [Matrix.mulVec_eq_sum]
      simp only [ Finset.sum_apply, gt_iff_lt]
      have := (c (j.castLT (by lia))).right (by rw [Fin.val_castLT]; lia)
      unfold sum_successive_terms at this
      apply this.trans_eq
      apply Finset.sum_bij' (fun x h => ⟨x.val-j.val, by grind⟩) (fun y _ => ⟨j.val+y.val, by lia⟩) <;> {
        simp <;> grind only [= Fin.val_castLT, = Lean.Grind.toInt_fin, = Finset.mem_Icc]
      }

    have : (1 ᵥ* A) ⬝ᵥ 1 < 0 := by
      rw [dotProduct_one]
      apply Fintype.sum_neg
      exact lt_of_strongLT rneg
    have : 0 < (1 ᵥ* A) ⬝ᵥ 1 := by
      rw [<-Matrix.dotProduct_mulVec, one_dotProduct]
      apply Fintype.sum_pos
      exact lt_of_strongLT cpos
    lia


end Imo1977P2
