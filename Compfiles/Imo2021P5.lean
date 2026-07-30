/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Kimi K3
-/

module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Tactic.Cases
public import ProblemExtraction

@[expose] public section

problem_file {
  problemImportedFrom :=
    "https://github.com/jsm28/IMOLean/blob/main/IMO/IMO2021P5.lean"
}

/-!
# International Mathematical Olympiad 2021, Problem 5

Two squirrels, Bushy and Jumpy, have collected 2001 walnuts for winter.
Jumpy numbers the walnuts from 1 to 2021, and digs 2021 little holes
in a circular pattern around their favorite tree. The next morning,
Jumpy notices that Bushy had placed one walnut into each hole, but
had paid no attention to the numbering. Unhappy, Jumpy decides to
reorder the walnuts by performing a sequence of 2021 moves. In the kth
move, Jump swaps the positions of the two walnuts adjacent to walnut k.

Prove that there exists a value of k such that, on the kth move, Jumpy
swaps some walnuts a and b such that a < k < b.
-/

namespace Imo2021P5

/-- The arrangement of walnuts, as an equiv from holes to walnuts (0-based). -/
abbrev Position : Type := Fin 2021 ≃ Fin 2021

/-- The numbers of the walnuts swapped in move `k` (0-based), given the position. -/
def Position.swapped (p : Position) (k : Fin 2021) : Fin 2021 × Fin 2021 :=
  (p ((p.symm k) - 1), p ((p.symm k) + 1))

/-- A single move, on a pair of position and move number. -/
def move (p : Position × Fin 2021) : Position × Fin 2021 :=
  (p.1.trans (Equiv.swap (p.1.swapped p.2).1 (p.1.swapped p.2).2), p.2 + 1)

/-- The position after `n` moves. -/
def Position.nth (p : Position) (n : Fin 2021) : Position := (move^[n] (p, 0)).1

snip begin

/-- After `j` moves, color hole `x` red iff the walnut in it has number `< j`;
    otherwise the hole is black. -/
def coloring (p : Position) (j : ℕ) (x : Fin 2021) : Bool :=
  decide (((move^[j] (p, 0)).1 x).val < j)

/-- The number (mod 2) of adjacent pairs of holes that are both black. -/
def blackPairs (c : Fin 2021 → Bool) : ZMod 2 :=
  ∑ x : Fin 2021, cond (c x) 0 1 * cond (c (x + 1)) 0 1

theorem fin_val_one : (1 : Fin 2021).val = 1 := rfl

theorem fin_sub_one_add_one (h : Fin 2021) : h - 1 + 1 = h := by
  apply Fin.ext
  rw [Fin.val_add, Fin.val_sub, fin_val_one]
  omega

theorem fin_sub_one_ne_self (h : Fin 2021) : h - 1 ≠ h := by
  intro hc
  have hv := congrArg Fin.val hc
  rw [Fin.val_sub, fin_val_one] at hv
  omega

theorem fin_add_one_ne_self (h : Fin 2021) : h + 1 ≠ h := by
  intro hc
  have hv := congrArg Fin.val hc
  rw [Fin.val_add, fin_val_one] at hv
  omega

theorem fin_sub_one_ne_add_one (h : Fin 2021) : h - 1 ≠ h + 1 := by
  intro hc
  have hv := congrArg Fin.val hc
  rw [Fin.val_sub, Fin.val_add, fin_val_one] at hv
  omega

/-- The second component of the iterated move state is the move number. -/
theorem iterate_snd (p : Position) (j : ℕ) : ((move^[j] (p, 0)).2).val = j % 2021 := by
  induction' j with j ih
  · rfl
  · rw [Function.iterate_succ_apply']
    change ((move^[j] (p, 0)).2 + 1 : Fin 2021).val = (j + 1) % 2021
    rw [Fin.val_add, ih, fin_val_one]
    omega

/-- One step of the move process on the position component. -/
theorem iterate_fst_succ (p : Position) (j : ℕ) (hj : j < 2021) :
    (move^[j + 1] (p, 0)).1 = (move^[j] (p, 0)).1.trans
      (Equiv.swap
        ((move^[j] (p, 0)).1 ((move^[j] (p, 0)).1.symm ⟨j, hj⟩ - 1))
        ((move^[j] (p, 0)).1 ((move^[j] (p, 0)).1.symm ⟨j, hj⟩ + 1))) := by
  have h2 : (move^[j] (p, 0)).2 = ⟨j, hj⟩ :=
    Fin.ext (by rw [iterate_snd]; exact Nat.mod_eq_of_lt hj)
  rw [Function.iterate_succ_apply']
  conv_lhs => rw [show move^[j] (p, 0) = ((move^[j] (p, 0)).1, ⟨j, hj⟩) from Prod.ext rfl h2]
  rfl

/-- Flipping one black hole to red, where the two neighbors have the same color,
    does not change the number of black-black adjacent pairs, mod 2. -/
theorem blackPairs_update (c : Fin 2021 → Bool) (h : Fin 2021)
    (hh : c h = false) (hn : c (h - 1) = c (h + 1))
    (h1 : h - 1 ≠ h) (h2 : h + 1 ≠ h) :
    blackPairs (Function.update c h true) = blackPairs c := by
  unfold blackPairs
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
  have key : (∑ x ∈ ({h - 1, h} : Finset (Fin 2021)),
      (cond (Function.update c h true x) (0 : ZMod 2) 1 *
          cond (Function.update c h true (x + 1)) (0 : ZMod 2) 1 -
        cond (c x) (0 : ZMod 2) 1 * cond (c (x + 1)) (0 : ZMod 2) 1)) =
      ∑ x : Fin 2021,
        (cond (Function.update c h true x) (0 : ZMod 2) 1 *
            cond (Function.update c h true (x + 1)) (0 : ZMod 2) 1 -
          cond (c x) (0 : ZMod 2) 1 * cond (c (x + 1)) (0 : ZMod 2) 1) := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro x _ hx
    rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
    have hx1 : x + 1 ≠ h := by
      intro hc1
      apply hx.1
      rw [← hc1, add_sub_cancel_right]
    rw [Function.update_of_ne hx.2, Function.update_of_ne hx1, sub_self]
  rw [← key, Finset.sum_insert (by rw [Finset.mem_singleton]; exact h1),
    Finset.sum_singleton]
  have e1 : Function.update c h true (h - 1) = c (h - 1) := Function.update_of_ne h1 true c
  have e2 : Function.update c h true (h - 1 + 1) = true := by
    rw [fin_sub_one_add_one]; exact Function.update_self _ _ _
  have e3 : Function.update c h true h = true := Function.update_self _ _ _
  have e4 : Function.update c h true (h + 1) = c (h + 1) := Function.update_of_ne h2 true c
  rw [e1, e2, e3, e4, fin_sub_one_add_one, hh, ← hn]
  cases hb : c (h - 1) <;> simp; decide

/-- If there is no good move, then after move `j` the coloring is the previous
    coloring with the hole of walnut `j` flipped from black to red, and the two
    neighbors of that hole have the same color. -/
theorem coloring_succ (p : Position) (j : ℕ) (hj : j < 2021)
    (H : ∀ k : Fin 2021,
      ¬((((p.nth k).swapped k).1 < k ∧ k < ((p.nth k).swapped k).2) ∨
        (((p.nth k).swapped k).2 < k ∧ k < ((p.nth k).swapped k).1))) :
    (∀ x, coloring p (j + 1) x =
        Function.update (coloring p j) ((move^[j] (p, 0)).1.symm ⟨j, hj⟩) true x) ∧
      coloring p j ((move^[j] (p, 0)).1.symm ⟨j, hj⟩) = false ∧
      coloring p j ((move^[j] (p, 0)).1.symm ⟨j, hj⟩ - 1) =
        coloring p j ((move^[j] (p, 0)).1.symm ⟨j, hj⟩ + 1) := by
  generalize hQ : (move^[j] (p, 0)).1 = Q
  set k : Fin 2021 := ⟨j, hj⟩ with hk
  set h : Fin 2021 := Q.symm k with hhdef
  set a : Fin 2021 := Q (h - 1) with ha
  set b : Fin 2021 := Q (h + 1) with hb
  have hstep0 : (move^[j + 1] (p, 0)).1 = Q.trans (Equiv.swap a b) := by
    have hs := iterate_fst_succ p j hj
    rw [hQ, ← hk, ← hhdef, ← ha, ← hb] at hs
    exact hs
  have hQh : Q h = k := Equiv.apply_symm_apply Q k
  have hkv : k.val = j := rfl
  have h1 : h - 1 ≠ h := fin_sub_one_ne_self h
  have h2 : h + 1 ≠ h := fin_add_one_ne_self h
  have h3 : h - 1 ≠ h + 1 := fin_sub_one_ne_add_one h
  have hak : a ≠ k := by
    intro hc; rw [ha, ← hQh] at hc; exact h1 (Q.injective hc)
  have hbk : b ≠ k := by
    intro hc; rw [hb, ← hQh] at hc; exact h2 (Q.injective hc)
  have hab : a ≠ b := by
    intro hc; rw [ha, hb] at hc; exact h3 (Q.injective hc)
  have Hk0 : ¬((a < k ∧ k < b) ∨ (b < k ∧ k < a)) := by
    have hthis := H k
    simp only [Position.swapped] at hthis
    rw [show p.nth k = Q from hQ, ← hhdef, ← ha, ← hb] at hthis
    exact hthis
  have hside : a.val < j ↔ b.val < j := by
    have hav : a.val ≠ j := fun hc => hak (Fin.ext (hc.trans hkv.symm))
    have hbv : b.val ≠ j := fun hc => hbk (Fin.ext (hc.trans hkv.symm))
    simp only [Fin.lt_def] at Hk0
    rw [hkv] at Hk0
    omega
  refine ⟨?_, ?_, ?_⟩
  · intro x
    by_cases hxh : x = h
    · subst hxh
      rw [Function.update_self]
      show coloring p (j + 1) h = true
      simp only [coloring]
      rw [hstep0]
      show decide ((Equiv.swap a b (Q h)).val < j + 1) = true
      rw [hQh, Equiv.swap_apply_of_ne_of_ne (Ne.symm hak) (Ne.symm hbk), hkv,
        decide_eq_true_eq]
      exact Nat.lt_succ_self j
    · rw [Function.update_of_ne hxh]
      show coloring p (j + 1) x = coloring p j x
      simp only [coloring]
      rw [hstep0, hQ]
      show decide ((Equiv.swap a b (Q x)).val < j + 1) = decide ((Q x).val < j)
      by_cases hxa : Q x = a
      · rw [hxa, Equiv.swap_apply_left, decide_eq_decide]
        omega
      · by_cases hxb : Q x = b
        · rw [hxb, Equiv.swap_apply_right, decide_eq_decide]
          omega
        · rw [Equiv.swap_apply_of_ne_of_ne hxa hxb, decide_eq_decide]
          have hqx : (Q x).val ≠ j := by
            intro hc
            apply hxh
            have hqk : Q x = k := Fin.ext (hc.trans hkv.symm)
            rw [← hQh] at hqk
            exact Q.injective hqk
          omega
  · show coloring p j h = false
    simp only [coloring]
    rw [hQ, hQh, hkv, decide_eq_false_iff_not]
    exact lt_irrefl j
  · show coloring p j (h - 1) = coloring p j (h + 1)
    simp only [coloring]
    rw [hQ, ← ha, ← hb, decide_eq_decide]
    exact hside

snip end

problem imo2021_p5 (p : Position) :
    ∃ k, (((p.nth k).swapped k).1 < k ∧ k < ((p.nth k).swapped k).2) ∨
      (((p.nth k).swapped k).2 < k ∧ k < ((p.nth k).swapped k).1) := by
  by_contra H
  have H' : ∀ k : Fin 2021,
      ¬((((p.nth k).swapped k).1 < k ∧ k < ((p.nth k).swapped k).2) ∨
        (((p.nth k).swapped k).2 < k ∧ k < ((p.nth k).swapped k).1)) :=
    fun k hk => H ⟨k, hk⟩
  have hpre : ∀ j : ℕ, j < 2021 →
      blackPairs (coloring p (j + 1)) = blackPairs (coloring p j) := by
    intro j hj
    obtain ⟨hupd, hch, hnb⟩ := coloring_succ p j hj H'
    rw [show coloring p (j + 1)
        = Function.update (coloring p j) _ true from funext hupd]
    exact blackPairs_update _ _ hch hnb (fin_sub_one_ne_self _) (fin_add_one_ne_self _)
  have hbase : blackPairs (coloring p 0) = 1 := by
    show (∑ x : Fin 2021, cond (decide (((move^[0] (p, 0)).1 x).val < 0)) (0 : ZMod 2) 1 *
        cond (decide (((move^[0] (p, 0)).1 (x + 1)).val < 0)) (0 : ZMod 2) 1) = 1
    simp
    decide
  have hfinal : blackPairs (coloring p 2021) = 0 := by
    show (∑ x : Fin 2021, cond (decide (((move^[2021] (p, 0)).1 x).val < 2021)) (0 : ZMod 2) 1 *
        cond (decide (((move^[2021] (p, 0)).1 (x + 1)).val < 2021)) (0 : ZMod 2) 1) = 0
    apply Finset.sum_eq_zero
    intro x _
    rw [show decide (((move^[2021] (p, 0)).1 x).val < 2021) = true from by
        rw [decide_eq_true_eq]; exact Fin.is_lt _,
      show decide (((move^[2021] (p, 0)).1 (x + 1)).val < 2021) = true from by
        rw [decide_eq_true_eq]; exact Fin.is_lt _]
    simp
  have hind : ∀ j : ℕ, j ≤ 2021 → blackPairs (coloring p j) = 1 := by
    intro j hj
    induction' j with j ih
    · exact hbase
    · rw [hpre j (by omega)]
      exact ih (by omega)
  have hfinal1 : blackPairs (coloring p 2021) = 1 := hind 2021 (le_refl _)
  rw [hfinal] at hfinal1
  exact (show (0 : ZMod 2) ≠ 1 by decide) hfinal1

end Imo2021P5
