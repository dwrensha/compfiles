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
  rw [IsArithProg_iff] at h1 h2 ⊢
  obtain ⟨d, a, h1⟩ := h1
  obtain ⟨d', b, h2⟩ := h2
  have h3 (n : ℕ) : s (s n) < s (s n + 1) := hs <| lt_add_one (s n)
  have h4 (n : ℕ) : s (s n + 1) ≤ s (s (n + 1)) :=
    hs.monotone <| Order.add_one_le_iff.mpr <| hs <| Nat.lt_add_one _
  simp_rw [h1, h2] at h3 h4
  have h5 : a < b := by simpa using h3 0
  have : d = d' := by
    refine Nat.le_antisymm (Nat.le_of_lt_succ ?_) ?_
    · rw [← mul_lt_mul_iff_of_pos_right (by lia: 0 < b - a), Nat.add_one_mul, ← Nat.add_sub_assoc h5.le, ← Nat.add_lt_iff_lt_sub_right]
      exact h3 (b - a)
    · have h7 : d > 0 := by simpa using h3 0 |>.trans_le <| h4 0
      have : d' * d + b < (d + 1) * d + b := (h4 d).trans_lt (by ring_nf; simpa)
      simpa [h7] using this
  let diff (n : ℕ) := s (n + 1) - s n
  have := iSup s
  sorry

end Imo2009P3
