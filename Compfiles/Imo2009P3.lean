/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 2009, Problem 3

Suppose that $s_1, s_2, s_3, \ldots$ is a strictly increasing sequence of
positive integers such that the subsequences
$$s_{s_1}, s_{s_2}, s_{s_3}, \ldots \quad\text{and}\quad s_{s_1+1}, s_{s_2+1}, s_{s_3+1}, \ldots$$
are both arithmetic progressions. Prove that the sequence
$s_1, s_2, s_3, \ldots$ is itself an arithmetic progression.
-/

namespace Imo2009P3

/-- A sequence `f : ℕ → ℕ` is an arithmetic progression. -/
def IsArithProg (f : ℕ → ℕ) : Prop := ∃ d : ℕ, ∀ n, f (n + 1) = f n + d

snip begin
-- Adapted from the solution by Alex Zhai presented by Evan Chen

lemma IsArithProg_iff {f: ℕ → ℕ} : IsArithProg f ↔ ∃ d r : ℕ, ∀ n, f n = d * n + r := by
  refine ⟨fun ⟨d, h⟩ => ⟨d, f 0, fun n => ?_⟩, fun ⟨d, r, h⟩ => ⟨d, fun n => by simp [h]; ring_nf⟩⟩
  induction n with
  | zero => simp
  | succ n ih => rw [h n, ih]; ring_nf

snip end

problem imo2009_p3 (s : ℕ → ℕ) (hs : StrictMono s) (hpos : ∀ i, 0 < s i)
    (h1 : IsArithProg (fun n ↦ s (s n)))
    (h2 : IsArithProg (fun n ↦ s (s n + 1))) :
    IsArithProg s := by
  -- it may be more helpful to define a function ℤ → ℤ to be easier to prove
  rw [IsArithProg_iff] at h1 h2 ⊢
  obtain ⟨D, A, h1⟩ := h1
  obtain ⟨D', B, h2⟩ := h2

  have h3 (n : ℕ) : s (s n) < s (s n + 1) := hs <| lt_add_one (s n)
  have h4 (n : ℕ) : s (s n + 1) ≤ s (s (n + 1)) :=
    hs.monotone <| Order.add_one_le_iff.mpr <| hs <| Nat.lt_add_one _
  have h3' (n : ℕ) := h3 n |>.trans_le <| h4 n
  simp_rw [h1, h2] at h3 h4
  have h5 : A < B := by simpa using h3 0
  have : D = D' := by
    refine Nat.le_antisymm (Nat.le_of_lt_succ ?_) ?_
    · rw [← mul_lt_mul_iff_of_pos_right (by lia: 0 < B - A), Nat.add_one_mul, ← Nat.add_sub_assoc h5.le, ← Nat.add_lt_iff_lt_sub_right]
      exact h3 (B - A)
    · have h7 : D > 0 := by simpa using h3 0 |>.trans_le <| h4 0
      have : D' * D + B < (D + 1) * D + B := (h4 D).trans_lt (by ring_nf; simpa)
      simpa [h7] using this

  let diff (n : ℕ) := s (n + 1) - s n
  have h_bddAbove : BddAbove (Set.range diff) := by
    use A
    simp_rw [mem_upperBounds, Set.mem_range]
    rintro _ ⟨y, rfl⟩
    unfold diff
    sorry
  have h_bddBelow : BddBelow (Set.range diff) := by sorry
  let M := iSup diff
  let m := iInf diff
  have ⟨a, ha⟩ : ∃ a, diff a = M := exists_eq_ciSup_of_not_isSuccLimit h_bddAbove Order.not_isSuccLimit_of_isSuccArchimedean
  have ⟨b, hb⟩ : ∃ b, diff b = m := exists_eq_ciInf_of_not_isPredLimit sorry Order.not_isPredLimit_of_isPredArchimedean
  have h_le_M (n : ℕ) : diff n ≤ M := le_csSup h_bddAbove <| Set.mem_range_self _
  have h_m_le (n : ℕ) : m ≤ diff n := csInf_le h_bddBelow <| Set.mem_range_self _



  have : ∑ i ∈ Finset.range (s (s (a+1)) - (s (s a))), diff (s (s a) + i) = D * M := by
    unfold diff
    simp_rw [add_assoc]
    rw [Finset.sum_range_tsub <| Monotone.covariant_of_const hs.monotone (s (s a)), add_zero]
    rw [Nat.add_sub_of_le <| h3' a |>.le, h1, h1, Nat.add_sub_add_right, ← Nat.mul_sub, mul_eq_mul_left_iff]
    left; exact ha
  have : M = m := by calc M
    _ = diff (s (s a)) := by
      symm
      contrapose! this
      refine Nat.ne_of_lt ?_
      calc
        ∑ i ∈ Finset.range (s (s (a + 1)) - s (s a)), diff (s (s a) + i)
        _ < ∑ i ∈ Finset.range (s (s (a + 1)) - s (s a)), M :=
          Finset.sum_lt_sum (by simp [h_le_M]) ⟨0, by simp [h3', h_le_M _ |>.lt_of_ne this]⟩
        _ = D * M := by simp [h1, Nat.add_sub_add_right, ← Nat.mul_sub]
    _ = diff (s (s b)) := by unfold diff; simp_rw [h2, h1 (s _)]; lia
    _ = m := by
      contrapose! this
      sorry
  have (n : ℕ) : diff n = m := by
    apply Nat.le_antisymm <;> simp [↓h_m_le, ← this, h_le_M]
  simp_rw [diff] at this
  refine ⟨m, s 0, fun n => ?_⟩
  induction n with
  | zero => simp
  | succ n ih =>
    suffices s (n + 1) = m + s n by linarith
    refine (Nat.sub_eq_iff_eq_add <| hs.monotone <| Nat.le_add_right _ _).mp (this n)

end Imo2009P3
