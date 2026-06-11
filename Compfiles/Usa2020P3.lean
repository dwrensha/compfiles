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

noncomputable section

variable (p : ℕ) [hp : Fact (Nat.Prime p)] (hp2 : p ≠ 2)

private abbrev setA' : Finset (ZMod p) :=
  Finset.univ.filter (fun a => a ≠ 0 ∧ ¬IsSquare a ∧ ¬IsSquare (4 - a))

private abbrev setB' : Finset (ZMod p) :=
  Finset.univ.filter (fun b => b ≠ 0 ∧ b ≠ 4 ∧ IsSquare b ∧ IsSquare (4 - b))

private abbrev setC' : Finset (ZMod p) :=
  Finset.univ.filter (fun n => n ≠ 0 ∧ n ≠ 4 ∧ IsSquare (n * (4 - n)))

include hp2 in
private lemma hp_odd : Odd p := by
  have hpp := hp.out
  rw [Nat.odd_iff]
  rcases hpp.eq_two_or_odd with rfl | h
  · exact absurd rfl hp2
  · exact h

private lemma isSquare_mul_iff_same {a b : ZMod p} (ha : a ≠ 0) (hb : b ≠ 0) :
    IsSquare (a * b) ↔ (IsSquare a ∧ IsSquare b) ∨ (¬IsSquare a ∧ ¬IsSquare b) := by
  by_cases ha : IsSquare a <;> by_cases hb : IsSquare b <;> simp_all +decide [isSquare_iff_exists_sq]
  · exact Exists.elim ha fun x hx => Exists.elim hb fun y hy => ⟨x * y, by rw [hx, hy, mul_pow]⟩
  · obtain ⟨r, rfl⟩ := ha
    intro x hx; exact hb (x / r) (by rw [div_pow, eq_div_iff ha]; linear_combination' hx)
  · rintro x hx; obtain ⟨r, rfl⟩ := hb; simp_all +decide
    exact ha (x / r) (by rw [div_pow, eq_div_iff (pow_ne_zero 2 hb)]; linear_combination' hx)
  · have h_prod_residue : legendreSym p a.val = -1 ∧ legendreSym p b.val = -1 → ∃ r : ZMod p, a * b = r ^ 2 := by
      intro h
      have h_prod_residue : legendreSym p (a.val * b.val) = 1 := by
        rw [legendreSym.mul]; aesop
      rw [legendreSym.eq_one_iff] at h_prod_residue
      · obtain ⟨r, hr⟩ := h_prod_residue; use r; simp_all +decide [sq]
      · simp_all +decide
    simp_all +decide [legendreSym.eq_neg_one_iff]
    exact h_prod_residue (fun ⟨x, hx⟩ => ha x <| by rw [hx, sq]) (fun ⟨x, hx⟩ => hb x <| by rw [hx, sq])

private lemma setC_eq_union :
    setC' p = setA' p ∪ setB' p := by
  ext a
  simp [setA', setB', setC']
  by_cases ha : a = 0 <;> by_cases hb : 4 - a = 0 <;> simp_all +decide [isSquare_mul_iff_same]
  · exact fun h => False.elim <| h <| by linear_combination' -hb
  · grind +ring

private lemma disjoint_AB :
    Disjoint (setA' p) (setB' p) := by
  exact Finset.disjoint_filter.mpr fun _ _ _ _ => by aesop

include hp2 in
private lemma p_two_ne_zero : (2 : ZMod p) ≠ 0 := by
  exact fun h => hp2 <| by rcases p with _ | _ | _ | p <;> cases h <;> trivial

include hp2 in
private lemma p_two_ne_four : (2 : ZMod p) ≠ 4 := by
  intro h; have := Fact.out (p := p.Prime); rcases p with _ | _ | _ | p | p | p <;> cases h
  · trivial
  · contradiction

include hp2 in
private lemma two_mem_setC : (2 : ZMod p) ∈ setC' p := by
  simp +decide [setC']
  grind +suggestions

private lemma map_mem_setB {n : ZMod p} (hn : n ∈ setC' p)
    (hn2 : n ≠ 2) : n * (4 - n) ∈ setB' p := by
  simp_all +decide [setB']
  refine' ⟨sub_ne_zero_of_ne <| by tauto, _, _⟩
  · grind +ring
  · exact ⟨2 - n, by ring⟩

include hp2 in
private lemma fiber_prod {b : ZMod p} (hb : b ∈ setB' p) :
    ∏ n ∈ ((setC' p).erase 2).filter (fun m => m * (4 - m) = b), n = b := by
  obtain ⟨c, hc⟩ : ∃ c : ZMod p, c ≠ 0 ∧ c^2 = 4 - b := by
    simp_all +decide [setB']
    obtain ⟨c, hc⟩ := hb.2.2.2; use c; simp_all +decide [sq, sub_eq_iff_eq_add]
  have h_roots : ∀ n : ZMod p, n * (4 - n) = b ↔ n = 2 + c ∨ n = 2 - c := by
    grind
  have h_prod : (2 + c) ∈ (setC' p).erase 2 ∧ (2 - c) ∈ (setC' p).erase 2 := by
    grind
  rw [show (Finset.filter (fun n => n * (4 - n) = b) ((setC' p).erase 2)) = {2 + c, 2 - c} from ?_, Finset.prod_pair]
  · linear_combination' -hc.2
  · simp_all +decide [sub_eq_add_neg]
    rw [eq_neg_iff_add_eq_zero]; simp_all +decide [← two_mul]
    exact p_two_ne_zero p hp2
  · grind

include hp2 in
private lemma prod_C_erase_eq_prod_B :
    ∏ n ∈ (setC' p).erase 2, n = ∏ b ∈ setB' p, b := by
  rw [← Finset.prod_congr rfl fun x hx => fiber_prod p hp2 hx]
  rw [← Finset.prod_biUnion]
  · congr
    ext m; simp [setC', setB']
    intro hm₁ hm₂ hm₃ hm₄; refine' ⟨⟨hm₂, sub_ne_zero_of_ne <| Ne.symm hm₃⟩, _, hm₄, _⟩ <;> simp_all +decide [isSquare_iff_exists_sq]
    · exact fun h => hm₁ <| mul_left_cancel₀ (sub_ne_zero_of_ne hm₁) <| by linear_combination' -h
    · exact ⟨2 - m, by ring⟩
  · exact fun x hx y hy hxy => Finset.disjoint_filter.2 fun z => by aesop

private lemma prod_B_ne_zero :
    ∏ b ∈ setB' p, b ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr fun x hx => by aesop

end

snip end

problem usamo2020_p3 (p : ℕ) [hp : Fact (Nat.Prime p)] (hp2 : p ≠ 2) :
    ∏ a ∈ Finset.univ.filter (fun (a : ZMod p) => a ≠ 0 ∧ ¬IsSquare a ∧ ¬IsSquare (4 - a)), a = (solution_val : ZMod p) := by
  have h_setA : Finset.univ.filter (fun (a : ZMod p) => a ≠ 0 ∧ ¬IsSquare a ∧ ¬IsSquare (4 - a)) = setA' p := rfl
  rw [h_setA]
  have h_union : ∏ n ∈ setC' p, n = (∏ a ∈ setA' p, a) * (∏ b ∈ setB' p, b) := by
    rw [← Finset.prod_union (disjoint_AB p), ← setC_eq_union]
  have h_two : 2 * ∏ n ∈ (setC' p).erase 2, n = ∏ n ∈ setC' p, n := by
    rw [← Finset.mul_prod_erase _ _ (two_mem_setC p hp2)]
  rw [h_union, mul_comm] at h_two
  exact mul_left_cancel₀ (show (∏ b ∈ setB' p, b) ≠ 0 from prod_B_ne_zero p) (by rw [prod_C_erase_eq_prod_B p hp2] at h_two; linear_combination h_two.symm)

end Usamo2020P3
