/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Data.Multiset.Sort
public import Mathlib.Data.Sym.Card
public import Mathlib.SetTheory.Cardinal.Finite
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 2015, Problem 4

Steve is piling m ≥ 1 indistinguishable stones on the squares of an n × n grid.
Each square can have an arbitrarily high pile of stones. After he finished piling
his stones in some manner, he can then perform stone moves, defined as follows.
Consider any four grid squares, which are corners of a rectangle, i.e. in positions
(i, k), (i, l), (j, k), (j, l) for some 1 ≤ i, j, k, l ≤ n, such that i < j and
k < l. A stone move consists of either removing one stone from each of (i, k) and
(j, l) and moving them to (i, l) and (j, k) respectively, or removing one stone
from each of (i, l) and (j, k) and moving them to (i, k) and (j, l) respectively.

Two ways of piling the stones are equivalent if they can be obtained from one
another by a sequence of stone moves. How many different non-equivalent ways can
Steve pile the stones on the grid?
-/

namespace Usa2015P4

determine solution : ℕ → ℕ → ℕ := fun m n ↦ (Nat.choose (m + n - 1) (n - 1)) ^ 2

snip begin

/-- A way of piling stones on the `n × n` grid is a multiset of `(row, column)`
pairs, one pair per stone. -/
abbrev Piling (n : ℕ) := Multiset (Fin n × Fin n)

/-- A single stone move: two stones lying in distinct rows and distinct columns
swap their columns. (The two kinds of moves described in the problem statement —
picking either pair of diagonally opposite corners of a rectangle — are both of
this form.) -/
def StoneMove {n : ℕ} (S T : Piling n) : Prop :=
  ∃ x₁ x₂ y₁ y₂ : Fin n, ∃ U : Piling n,
    x₁ ≠ x₂ ∧ y₁ ≠ y₂ ∧
    S = (x₁, y₁) ::ₘ (x₂, y₂) ::ₘ U ∧
    T = (x₁, y₂) ::ₘ (x₂, y₁) ::ₘ U

/-- Two pilings are equivalent if they are related by a sequence of stone moves. -/
inductive EquivPilings {n : ℕ} : Piling n → Piling n → Prop where
  | refl (S : Piling n) : EquivPilings S S
  | move {S T : Piling n} : StoneMove S T → EquivPilings S T
  | symm {S T : Piling n} : EquivPilings S T → EquivPilings T S
  | trans {S T U : Piling n} : EquivPilings S T → EquivPilings T U → EquivPilings S U

/-- The multiset of rows is invariant under a single stone move. -/
theorem StoneMove.fst {n : ℕ} {S T : Piling n} (h : StoneMove S T) :
    S.map Prod.fst = T.map Prod.fst := by
  obtain ⟨x₁, x₂, y₁, y₂, U, -, -, rfl, rfl⟩ := h
  simp [Multiset.map_cons]

/-- The multiset of columns is invariant under a single stone move. -/
theorem StoneMove.snd {n : ℕ} {S T : Piling n} (h : StoneMove S T) :
    S.map Prod.snd = T.map Prod.snd := by
  obtain ⟨x₁, x₂, y₁, y₂, U, -, -, rfl, rfl⟩ := h
  rw [Multiset.map_cons, Multiset.map_cons, Multiset.map_cons, Multiset.map_cons]
  exact Multiset.cons_swap y₁ y₂ _

/-- A stone move can be performed in the presence of an extra fixed stone. -/
theorem StoneMove.cons {n : ℕ} {S T : Piling n} (h : StoneMove S T) (p : Fin n × Fin n) :
    StoneMove (p ::ₘ S) (p ::ₘ T) := by
  obtain ⟨x₁, x₂, y₁, y₂, U, hx, hy, rfl, rfl⟩ := h
  refine ⟨x₁, x₂, y₁, y₂, p ::ₘ U, hx, hy, ?_, ?_⟩
  · rw [Multiset.cons_swap p (x₁, y₁) _, Multiset.cons_swap p (x₂, y₂) _]
  · rw [Multiset.cons_swap p (x₁, y₂) _, Multiset.cons_swap p (x₂, y₁) _]

/-- The multiset of rows is invariant under equivalence of pilings. -/
theorem EquivPilings.fst {n : ℕ} {S T : Piling n} (h : EquivPilings S T) :
    S.map Prod.fst = T.map Prod.fst := by
  induction h with
  | refl S => rfl
  | move h => exact h.fst
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The multiset of columns is invariant under equivalence of pilings. -/
theorem EquivPilings.snd {n : ℕ} {S T : Piling n} (h : EquivPilings S T) :
    S.map Prod.snd = T.map Prod.snd := by
  induction h with
  | refl S => rfl
  | move h => exact h.snd
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Equivalent pilings remain equivalent after adding an extra fixed stone. -/
theorem EquivPilings.cons {n : ℕ} {S T : Piling n} (h : EquivPilings S T)
    (p : Fin n × Fin n) : EquivPilings (p ::ₘ S) (p ::ₘ T) := by
  induction h with
  | refl S => exact .refl _
  | move h => exact .move (h.cons p)
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

/-- The hard direction: two pilings with the same signature (the same multiset of
rows and the same multiset of columns) are equivalent. Proved by strong induction
on the number of stones: pick a stone `s` of the first piling, find a stone `t` of
the second piling in the same row, and use one or two stone moves to put `t`'s
column right, then apply the induction hypothesis to the remaining stones. -/
theorem equivPilings_of_signature {n : ℕ} :
    ∀ k : ℕ, ∀ S T : Piling n,
      S.card = k → S.map Prod.fst = T.map Prod.fst → S.map Prod.snd = T.map Prod.snd →
      EquivPilings S T := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro S T hk hfst hsnd
    induction S using Multiset.induction_on with
    | empty =>
      have hT : T = 0 := by
        apply Multiset.card_eq_zero.mp
        rw [← Multiset.card_map Prod.fst, ← hfst]
        rfl
      rw [hT]
      exact EquivPilings.refl 0
    | cons s S' =>
      have hk' : S'.card < k := by
        have hc : (s ::ₘ S').card = S'.card + 1 := Multiset.card_cons s S'
        omega
      -- Find a stone `t` of `T` lying in the same row as `s`.
      have hsx : s.1 ∈ T.map Prod.fst := by
        rw [← hfst]
        exact Multiset.mem_map_of_mem _ (Multiset.mem_cons_self s S')
      rcases Multiset.mem_map.mp hsx with ⟨t, htT, ht1⟩
      rcases Multiset.exists_cons_of_mem htT with ⟨T', rfl⟩
      rw [Multiset.map_cons, Multiset.map_cons] at hfst
      rw [Multiset.map_cons, Multiset.map_cons] at hsnd
      -- hfst : s.1 ::ₘ S'.map fst = t.1 ::ₘ T'.map fst, and similarly for hsnd.
      rw [ht1] at hfst
      have hfst' : S'.map Prod.fst = T'.map Prod.fst := (Multiset.cons_inj_right s.1).mp hfst
      by_cases ht2 : t.2 = s.2
      · -- `t` already coincides with `s`; apply the induction hypothesis to the rest.
        have hts : t = s := Prod.ext ht1 ht2
        subst t
        have hsnd' : S'.map Prod.snd = T'.map Prod.snd := (Multiset.cons_inj_right s.2).mp hsnd
        exact EquivPilings.cons (ih S'.card hk' S' T' rfl hfst' hsnd') s
      · -- Find a stone `u` of `T'` lying in the same column as `s`.
        have hsy : s.2 ∈ T'.map Prod.snd := by
          have h : s.2 ∈ (t ::ₘ T').map Prod.snd := by
            rw [Multiset.map_cons, ← hsnd]
            exact Multiset.mem_cons_self s.2 _
          rw [Multiset.map_cons, Multiset.mem_cons] at h
          rcases h with h | h
          · exact absurd h.symm ht2
          · exact h
        rcases Multiset.mem_map.mp hsy with ⟨u, huT', hu2⟩
        rcases Multiset.exists_cons_of_mem huT' with ⟨U, rfl⟩
        rw [Multiset.map_cons] at hfst' hsnd
        -- hfst' : S'.map fst = u.1 ::ₘ U.map fst
        -- hsnd : s.2 ::ₘ S'.map snd = t.2 ::ₘ u.2 ::ₘ U.map snd
        by_cases hu1 : u.1 = s.1
        · -- `u` is also in the row of `s`. Either every stone of `T` lies in that
          -- row, in which case both pilings are determined by their columns, or some
          -- stone `w` lies in another row and we can fix `t` with one or two moves.
          by_cases hw : ∃ w ∈ U, w.1 ≠ s.1
          · rcases hw with ⟨w, hwU, hw1⟩
            rcases Multiset.exists_cons_of_mem hwU with ⟨W, rfl⟩
            rw [Multiset.map_cons] at hfst' hsnd
            by_cases hw2 : w.2 = s.2
            · -- One move on the stones `t` and `w` puts `t` in place.
              have hmove : StoneMove (t ::ₘ u ::ₘ w ::ₘ W) (s ::ₘ (w.1, t.2) ::ₘ u ::ₘ W) := by
                refine ⟨s.1, w.1, t.2, s.2, u ::ₘ W, fun h => hw1 h.symm, ht2, ?_, ?_⟩
                · rw [show t = (s.1, t.2) from Prod.ext ht1 rfl,
                    show w = (w.1, s.2) from Prod.ext rfl hw2,
                    Multiset.cons_swap u (w.1, s.2) _]
                · rfl
              have hsig1 : S'.map Prod.fst = ((w.1, t.2) ::ₘ u ::ₘ W).map Prod.fst := by
                rw [Multiset.map_cons, Multiset.map_cons, hfst']
                exact Multiset.cons_swap _ _ _
              have hsig2 : S'.map Prod.snd = ((w.1, t.2) ::ₘ u ::ₘ W).map Prod.snd := by
                rw [Multiset.map_cons, Multiset.map_cons]
                show S'.map Prod.snd = t.2 ::ₘ u.2 ::ₘ W.map Prod.snd
                rw [hu2, hw2, Multiset.cons_swap t.2 s.2 _] at hsnd
                rw [hu2]
                exact (Multiset.cons_inj_right s.2).mp hsnd
              have hih := ih S'.card hk' S' ((w.1, t.2) ::ₘ u ::ₘ W) rfl hsig1 hsig2
              exact (EquivPilings.cons hih s).trans ((EquivPilings.move hmove).symm)
            · -- Two moves: first swap the columns of `u` and `w`, then those of
              -- `t` and the stone that received `s`'s column.
              have hmove1 : StoneMove (t ::ₘ u ::ₘ w ::ₘ W)
                  ((s.1, w.2) ::ₘ (w.1, s.2) ::ₘ t ::ₘ W) := by
                refine ⟨s.1, w.1, s.2, w.2, t ::ₘ W, fun h => hw1 h.symm, fun h => hw2 h.symm, ?_, ?_⟩
                · rw [show u = (s.1, s.2) from Prod.ext hu1 hu2,
                    show w = (w.1, w.2) from rfl,
                    Multiset.cons_swap t (s.1, s.2) _, Multiset.cons_swap t (w.1, w.2) _]
                · rfl
              have hmove2 : StoneMove ((s.1, w.2) ::ₘ (w.1, s.2) ::ₘ t ::ₘ W)
                  (s ::ₘ (s.1, w.2) ::ₘ (w.1, t.2) ::ₘ W) := by
                refine ⟨s.1, w.1, t.2, s.2, (s.1, w.2) ::ₘ W, fun h => hw1 h.symm, ht2, ?_, ?_⟩
                · rw [show t = (s.1, t.2) from Prod.ext ht1 rfl,
                    Multiset.cons_swap (s.1, w.2) (w.1, s.2) _,
                    Multiset.cons_swap (s.1, w.2) (s.1, t.2) _,
                    Multiset.cons_swap (w.1, s.2) (s.1, t.2) _]
                · rw [show s = (s.1, s.2) from rfl, Multiset.cons_swap (s.1, w.2) (w.1, t.2) _]
              have hsig1 : S'.map Prod.fst = ((s.1, w.2) ::ₘ (w.1, t.2) ::ₘ W).map Prod.fst := by
                rw [Multiset.map_cons, Multiset.map_cons, hfst', hu1]
              have hsig2 : S'.map Prod.snd = ((s.1, w.2) ::ₘ (w.1, t.2) ::ₘ W).map Prod.snd := by
                rw [Multiset.map_cons, Multiset.map_cons]
                show S'.map Prod.snd = w.2 ::ₘ t.2 ::ₘ W.map Prod.snd
                rw [Multiset.cons_swap w.2 t.2 _]
                rw [hu2, Multiset.cons_swap t.2 s.2 _] at hsnd
                exact (Multiset.cons_inj_right s.2).mp hsnd
              have hih := ih S'.card hk' S' ((s.1, w.2) ::ₘ (w.1, t.2) ::ₘ W) rfl hsig1 hsig2
              exact (EquivPilings.cons hih s).trans
                (((EquivPilings.move hmove1).trans (EquivPilings.move hmove2)).symm)
          · -- Every stone of `T` lies in the row of `s`; the same holds for `S`
            -- (their rows form the same multiset), so both pilings are equal.
            push Not at hw
            have hT_all : ∀ p ∈ (t ::ₘ u ::ₘ U : Piling n), p.1 = s.1 := by
              intro p hp
              rw [Multiset.mem_cons, Multiset.mem_cons] at hp
              rcases hp with rfl | rfl | hp
              · exact ht1
              · exact hu1
              · exact hw p hp
            have hS_all : ∀ p ∈ (s ::ₘ S' : Piling n), p.1 = s.1 := by
              intro p hp
              have hmem : p.1 ∈ (s ::ₘ S' : Piling n).map Prod.fst :=
                Multiset.mem_map_of_mem _ hp
              rw [Multiset.map_cons, Multiset.mem_cons] at hmem
              rcases hmem with h | h
              · exact h
              · rw [hfst', Multiset.mem_cons] at h
                rcases h with h | h
                · exact h.trans hu1
                · rcases Multiset.mem_map.mp h with ⟨q, hqU, hq1⟩
                  exact hq1.symm.trans (hw q hqU)
            have hS_eq : (s ::ₘ S' : Piling n) =
                ((s ::ₘ S').map Prod.snd).map (Prod.mk s.1) := by
              rw [Multiset.map_map]
              conv_lhs => rw [← Multiset.map_id' (s ::ₘ S')]
              exact Multiset.map_congr rfl (fun p hp ↦ Prod.ext (hS_all p hp) rfl)
            have hT_eq : (t ::ₘ u ::ₘ U : Piling n) =
                ((t ::ₘ u ::ₘ U).map Prod.snd).map (Prod.mk s.1) := by
              rw [Multiset.map_map]
              conv_lhs => rw [← Multiset.map_id' (t ::ₘ u ::ₘ U)]
              exact Multiset.map_congr rfl (fun p hp ↦ Prod.ext (hT_all p hp) rfl)
            have hsnd0 : (s ::ₘ S' : Piling n).map Prod.snd =
                (t ::ₘ u ::ₘ U).map Prod.snd := by
              rw [Multiset.map_cons, Multiset.map_cons, Multiset.map_cons]
              exact hsnd
            rw [hS_eq, hT_eq, hsnd0]
            exact EquivPilings.refl _
        · -- `u` lies in another row: a single move on `t` and `u` puts `t` in place.
          have hmove : StoneMove (t ::ₘ u ::ₘ U) (s ::ₘ (u.1, t.2) ::ₘ U) := by
            refine ⟨s.1, u.1, t.2, s.2, U, fun h => hu1 h.symm, ht2, ?_, ?_⟩
            · rw [show t = (s.1, t.2) from Prod.ext ht1 rfl,
                show u = (u.1, s.2) from Prod.ext rfl hu2]
            · rfl
          have hsig1 : S'.map Prod.fst = ((u.1, t.2) ::ₘ U).map Prod.fst := by
            rw [Multiset.map_cons]
            exact hfst'
          have hsig2 : S'.map Prod.snd = ((u.1, t.2) ::ₘ U).map Prod.snd := by
            rw [Multiset.map_cons]
            show S'.map Prod.snd = t.2 ::ₘ U.map Prod.snd
            rw [hu2, Multiset.cons_swap t.2 s.2 _] at hsnd
            exact (Multiset.cons_inj_right s.2).mp hsnd
          have hih := ih S'.card hk' S' ((u.1, t.2) ::ₘ U) rfl hsig1 hsig2
          exact (EquivPilings.cons hih s).trans ((EquivPilings.move hmove).symm)

/-- Every signature is realized by at least one piling: sort the rows and the
columns and pair them up. -/
def pilingOf {n : ℕ} (X Y : Multiset (Fin n)) : Piling n :=
  (X.sort (· ≤ ·)).zip (Y.sort (· ≤ ·))

theorem pilingOf_fst {n : ℕ} {X Y : Multiset (Fin n)} (h : X.card = Y.card) :
    (pilingOf X Y).map Prod.fst = X := by
  have hl : (X.sort (· ≤ ·)).length ≤ (Y.sort (· ≤ ·)).length := by
    rw [Multiset.length_sort, Multiset.length_sort, h]
  rw [pilingOf, Multiset.map_coe, List.map_fst_zip hl, Multiset.sort_eq]

theorem pilingOf_snd {n : ℕ} {X Y : Multiset (Fin n)} (h : Y.card = X.card) :
    (pilingOf X Y).map Prod.snd = Y := by
  have hl : (Y.sort (· ≤ ·)).length ≤ (X.sort (· ≤ ·)).length := by
    rw [Multiset.length_sort, Multiset.length_sort, h]
  rw [pilingOf, Multiset.map_coe, List.map_snd_zip hl, Multiset.sort_eq]

theorem pilingOf_card {n : ℕ} {X Y : Multiset (Fin n)} (h : X.card = Y.card) :
    (pilingOf X Y).card = X.card := by
  rw [pilingOf, Multiset.coe_card, List.length_zip, Multiset.length_sort,
    Multiset.length_sort, h, min_self]

/-- The equivalence relation on pilings of `m` stones, as a `Setoid`. -/
instance pilingSetoid (m n : ℕ) : Setoid {S : Piling n // S.card = m} where
  r S T := EquivPilings S.1 T.1
  iseqv := {
    refl := fun S ↦ EquivPilings.refl S.1
    symm := fun h ↦ EquivPilings.symm h
    trans := fun h₁ h₂ ↦ EquivPilings.trans h₁ h₂
  }

/-- The non-equivalent pilings of `m` stones are in bijection with the pairs
`(X, Y)` of multisets of rows and columns of size `m`. -/
def quotientEquivSignatures (m n : ℕ) :
    Quotient (pilingSetoid m n) ≃ Sym (Fin n) m × Sym (Fin n) m where
  toFun := Quotient.lift
    (fun S : {S : Piling n // S.card = m} ↦
      (⟨S.1.map Prod.fst, by rw [Multiset.card_map]; exact S.2⟩,
       ⟨S.1.map Prod.snd, by rw [Multiset.card_map]; exact S.2⟩))
    (fun {A B} h ↦ Prod.ext (Subtype.ext (EquivPilings.fst h)) (Subtype.ext (EquivPilings.snd h)))
  invFun := fun ⟨X, Y⟩ ↦
    ⟦⟨pilingOf X.1 Y.1, by
      have h : X.1.card = Y.1.card := X.2.trans Y.2.symm
      rw [pilingOf_card h]; exact X.2⟩⟧
  left_inv := fun q ↦ by
    induction q using Quotient.inductionOn with
    | _ S =>
      apply Quot.sound
      have hcard : (S.1.map Prod.fst).card = (S.1.map Prod.snd).card := by
        rw [Multiset.card_map, Multiset.card_map]
      exact equivPilings_of_signature S.1.card _ S.1
        (by rw [pilingOf_card hcard, Multiset.card_map])
        (pilingOf_fst hcard) (pilingOf_snd hcard.symm)
  right_inv := fun ⟨X, Y⟩ ↦ by
    have hcard : X.1.card = Y.1.card := X.2.trans Y.2.symm
    exact Prod.ext (Subtype.ext (pilingOf_fst hcard)) (Subtype.ext (pilingOf_snd hcard.symm))

snip end

problem usa2015_p4 (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    Nat.card (Quotient (pilingSetoid m n)) = solution m n := by
  rw [Nat.card_congr (quotientEquivSignatures m n), Nat.card_prod,
    Nat.card_eq_fintype_card, Sym.card_sym_eq_choose, Fintype.card_fin]
  have hle : m ≤ n + m - 1 := by omega
  have hsub : n + m - 1 - m = n - 1 := by omega
  rw [← Nat.choose_symm hle, hsub, show n + m - 1 = m + n - 1 by omega]
  rw [show solution m n = ((m + n - 1).choose (n - 1)) ^ 2 from rfl, pow_two]

end Usa2015P4
