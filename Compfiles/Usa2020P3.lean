/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Liao
-/

import Mathlib
import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# USA Mathematical Olympiad 2020 Problem 3

Let p be an odd prime. An integer x is called a *quadratic non-residue* if p does not
divide x − t² for any integer t.

Denote by A the set of all integers a such that 1 ≤ a < p, and both a and 4 − a are
quadratic non-residues. Calculate the remainder when the product of the elements
of A is divided by p.
-/

namespace Usamo2020P3

open Finset ZMod

determine solution_val : ℕ := 2

snip begin

/-
Let B be the set of nonzero b ≠ 4 with both b and 4 - b squares, and C the set of
nonzero n ≠ 4 with n * (4 - n) a square. By multiplicativity of the quadratic
character, C is the disjoint union of A and B. The map n ↦ n * (4 - n) sends
C \ {2} to B, and the fiber over b is {2 + c, 2 - c} where c² = 4 - b, which has
product (2 + c) * (2 - c) = 4 - c² = b. Hence ∏ C \ {2} = ∏ B, and cancelling
∏ B ≠ 0 from ∏ A * ∏ B = ∏ C = 2 * ∏ C \ {2} gives ∏ A = 2.
-/

section

variable (p : ℕ) [hp : Fact (Nat.Prime p)] (hp2 : p ≠ 2)

private abbrev setA' : Finset (ZMod p) :=
  Finset.univ.filter (fun a => a ≠ 0 ∧ ¬IsSquare a ∧ ¬IsSquare (4 - a))

private abbrev setB' : Finset (ZMod p) :=
  Finset.univ.filter (fun b => b ≠ 0 ∧ b ≠ 4 ∧ IsSquare b ∧ IsSquare (4 - b))

private abbrev setC' : Finset (ZMod p) :=
  Finset.univ.filter (fun n => n ≠ 0 ∧ n ≠ 4 ∧ IsSquare (n * (4 - n)))

private lemma isSquare_mul_iff_same {a b : ZMod p} (ha : a ≠ 0) (hb : b ≠ 0) :
    IsSquare (a * b) ↔ (IsSquare a ∧ IsSquare b) ∨ (¬IsSquare a ∧ ¬IsSquare b) := by
  rw [← quadraticChar_one_iff_isSquare (mul_ne_zero ha hb),
      ← quadraticChar_one_iff_isSquare ha, ← quadraticChar_one_iff_isSquare hb, map_mul]
  rcases quadraticChar_dichotomy ha with h1 | h1 <;>
    rcases quadraticChar_dichotomy hb with h2 | h2 <;>
      norm_num [h1, h2]

private lemma setC_eq_union : setC' p = setA' p ∪ setB' p := by
  ext a
  simp only [setA', setB', setC', Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases ha : a = 0
  · simp [ha]
  by_cases ha4 : a = 4
  · simp [ha4]
  · rw [isSquare_mul_iff_same p ha (sub_ne_zero_of_ne (Ne.symm ha4))]
    tauto

private lemma disjoint_AB : Disjoint (setA' p) (setB' p) :=
  Finset.disjoint_filter.mpr fun _ _ _ _ => by aesop

include hp2 in
private lemma p_two_ne_zero : (2 : ZMod p) ≠ 0 :=
  Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])

include hp2 in
private lemma p_two_ne_four : (2 : ZMod p) ≠ 4 := fun h =>
  p_two_ne_zero p hp2 (by linear_combination -h)

include hp2 in
private lemma two_mem_setC : (2 : ZMod p) ∈ setC' p :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _, p_two_ne_zero p hp2, p_two_ne_four p hp2, 2, by ring⟩

private lemma map_mem_setB {n : ZMod p} (hn : n ∈ setC' p) (hn2 : n ≠ 2) :
    n * (4 - n) ∈ setB' p := by
  obtain ⟨-, hn0, hn4, hsq⟩ := Finset.mem_filter.mp hn
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    mul_ne_zero hn0 (sub_ne_zero_of_ne (Ne.symm hn4)),
    fun h => hn2 (sub_eq_zero.mp (sq_eq_zero_iff.mp (show (n - 2) ^ 2 = 0 by linear_combination -h))),
    hsq, 2 - n, by ring⟩

include hp2 in
private lemma fiber_prod {b : ZMod p} (hb : b ∈ setB' p) :
    ∏ n ∈ ((setC' p).erase 2).filter (fun m => m * (4 - m) = b), n = b := by
  obtain ⟨-, hb0, hb4, hsqb, c, hc⟩ := Finset.mem_filter.mp hb
  have hc0 : c ≠ 0 := by rintro rfl; exact hb4 (by linear_combination -hc)
  have h_roots : ∀ n : ZMod p, n * (4 - n) = b ↔ n = 2 + c ∨ n = 2 - c := by
    refine fun n => ⟨fun hn => ?_, by rintro (rfl | rfl) <;> linear_combination hc⟩
    have h0 : (n - (2 + c)) * (n - (2 - c)) = 0 := by linear_combination -hn + hc
    exact (mul_eq_zero.mp h0).imp sub_eq_zero.mp sub_eq_zero.mp
  have hmem : ∀ n : ZMod p, n * (4 - n) = b → n ∈ setC' p := by
    intro n hn
    have hn0 : n ≠ 0 := by rintro rfl; exact hb0 (by linear_combination -hn)
    have hn4 : n ≠ 4 := by rintro rfl; exact hb0 (by linear_combination -hn)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn0, hn4, hn.symm ▸ hsqb⟩
  have hfilter : ((setC' p).erase 2).filter (fun m => m * (4 - m) = b) = {2 + c, 2 - c} := by
    ext n
    rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, ← h_roots n]
    refine ⟨fun h => h.2, fun h => ⟨Finset.mem_erase.mpr ⟨?_, hmem n h⟩, h⟩⟩
    rintro rfl
    exact hb4 (by linear_combination -h)
  have hcc : 2 + c ≠ 2 - c := fun h =>
    mul_ne_zero (p_two_ne_zero p hp2) hc0 (by linear_combination h)
  rw [hfilter, Finset.prod_pair hcc]
  linear_combination hc

include hp2 in
private lemma prod_C_erase_eq_prod_B :
    ∏ n ∈ (setC' p).erase 2, n = ∏ b ∈ setB' p, b := by
  rw [← Finset.prod_fiberwise_of_maps_to
    (fun n hn => map_mem_setB p (Finset.mem_of_mem_erase hn) (Finset.ne_of_mem_erase hn))
    (fun n => n)]
  exact Finset.prod_congr rfl fun _ hb => fiber_prod p hp2 hb

private lemma prod_B_ne_zero : ∏ b ∈ setB' p, b ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ hb => (Finset.mem_filter.mp hb).2.1

end

snip end

problem usamo2020_p3 (p : ℕ) [hp : Fact (Nat.Prime p)] (hp2 : p ≠ 2) :
    ∏ a ∈ Finset.univ.filter (fun (a : ZMod p) => a ≠ 0 ∧ ¬IsSquare a ∧ ¬IsSquare (4 - a)), a = (solution_val : ZMod p) := by
  apply mul_left_cancel₀ (prod_B_ne_zero p)
  calc (∏ b ∈ setB' p, b) * ∏ a ∈ setA' p, a
      = ∏ n ∈ setC' p, n := by
        rw [setC_eq_union p, Finset.prod_union (disjoint_AB p), mul_comm]
    _ = 2 * ∏ n ∈ (setC' p).erase 2, n :=
        (Finset.mul_prod_erase _ _ (two_mem_setC p hp2)).symm
    _ = (∏ b ∈ setB' p, b) * (solution_val : ZMod p) := by
        rw [prod_C_erase_eq_prod_B p hp2, mul_comm]
        norm_num [solution_val]

end Usamo2020P3
