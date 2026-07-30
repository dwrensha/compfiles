/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.EuclideanDomain.Basic
public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Data.Int.Star
public import Mathlib.Data.Int.SuccPred
public import Mathlib.Data.Sym.Sym2
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.LinearCombination.Lemmas
public import ProblemExtraction

@[expose] public section

-- This file's proofs are memory-bound: asynchronous elaboration retains per-tactic
-- snapshots whose peak exceeds 4 GiB. Elaborating synchronously lowers peak RSS
-- at the cost of some wall-clock time.
set_option Elab.async false

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 2023, Problem 3

Consider an n-by-n board of unit squares for some odd positive integer n. We say
that a collection C of identical dominoes is a maximal grid-aligned configuration
on the board if C consists of (n² - 1)/2 dominoes where each domino covers exactly
two neighboring squares and the dominoes don't overlap: C then covers all but one
square on the board. We are allowed to slide (but not rotate) a domino on the board
to cover the uncovered square, resulting in a new maximal grid-aligned configuration
with another square uncovered. Let k(C) be the number of distinct maximal
grid-aligned configurations obtainable from C by repeatedly sliding dominoes.

Find all possible values of k(C) as a function of n.
-/

namespace Usa2023P3

snip begin

/-!
## Basic definitions

We model the board as the integer lattice points `Cell := ℤ × ℤ` inside
`[0, n-1] × [0, n-1]`.  A configuration is encoded as a function `f : Cell → Cell`
which pairs up the covered cells: `f` is an involution of the board with exactly
one fixed point (the uncovered square), and every non-fixed cell is mapped to an
adjacent cell.  Off the board, `f` is the identity.
-/

abbrev Cell := ℤ × ℤ

/-- The `n × n` board as a finite set of cells, for `n ≥ 1` the cells
`(x, y)` with `0 ≤ x, y ≤ n - 1`. -/
noncomputable def board (n : ℕ) : Finset Cell := Finset.Icc (0, 0) ((n : ℤ) - 1, (n : ℤ) - 1)

theorem mem_board {n : ℕ} {c : Cell} :
    c ∈ board n ↔ 0 ≤ c.1 ∧ c.1 ≤ (n : ℤ) - 1 ∧ 0 ≤ c.2 ∧ c.2 ≤ (n : ℤ) - 1 := by
  simp only [board, Finset.mem_Icc, Prod.le_def]
  omega

theorem board_eq_empty_of_zero {n : ℕ} (hn : n = 0) : board n = ∅ := by
  simp [board, hn]

/-- Two cells are (rook-)adjacent when they differ by exactly one in exactly
one coordinate. -/
def IsAdj (c d : Cell) : Prop :=
  (c.1 = d.1 ∧ |c.2 - d.2| = 1) ∨ (|c.1 - d.1| = 1 ∧ c.2 = d.2)

/-- A unit step vector. -/
def IsUnit (u : Cell) : Prop := u = (1, 0) ∨ u = (-1, 0) ∨ u = (0, 1) ∨ u = (0, -1)

theorem IsAdj.isUnit (c d : Cell) (h : IsAdj c d) : IsUnit (d - c) := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hdc : d - c = (0, d.2 - c.2) := by
      ext <;> simp [h1]
    have habs : |d.2 - c.2| = 1 := by rwa [abs_sub_comm]
    rcases eq_or_eq_neg_of_abs_eq habs with h | h
    · right; right; left; rw [hdc, h]
    · right; right; right; rw [hdc, h]
  · have hdc : d - c = (d.1 - c.1, 0) := by
      ext <;> simp [h2]
    have habs : |d.1 - c.1| = 1 := by rwa [abs_sub_comm]
    rcases eq_or_eq_neg_of_abs_eq habs with h | h
    · left; rw [hdc, h]
    · right; left; rw [hdc, h]

theorem IsUnit.neg {u : Cell} (hu : IsUnit u) : IsUnit (-u) := by
  rcases hu with rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inl rfl
  · exact Or.inr (Or.inr (Or.inr rfl))
  · exact Or.inr (Or.inr (Or.inl rfl))

theorem isAdj_iff_isUnit_sub (c d : Cell) : IsAdj c d ↔ IsUnit (d - c) := by
  constructor
  · exact IsAdj.isUnit c d
  · intro h
    have h1 : d.1 - c.1 = (d - c).1 := rfl
    have h2 : d.2 - c.2 = (d - c).2 := rfl
    rcases h with h | h | h | h
    · have h1' : d.1 - c.1 = 1 := by rw [h1, h]
      have h2' : d.2 - c.2 = 0 := by rw [h2, h]
      refine Or.inr ⟨?_, by omega⟩
      have h3 : c.1 - d.1 = -1 := by omega
      rw [h3]; simp
    · have h1' : d.1 - c.1 = -1 := by rw [h1, h]
      have h2' : d.2 - c.2 = 0 := by rw [h2, h]
      refine Or.inr ⟨?_, by omega⟩
      have h3 : c.1 - d.1 = 1 := by omega
      rw [h3]; simp
    · have h1' : d.1 - c.1 = 0 := by rw [h1, h]
      have h2' : d.2 - c.2 = 1 := by rw [h2, h]
      refine Or.inl ⟨by omega, ?_⟩
      have h3 : c.2 - d.2 = -1 := by omega
      rw [h3]; simp
    · have h1' : d.1 - c.1 = 0 := by rw [h1, h]
      have h2' : d.2 - c.2 = -1 := by rw [h2, h]
      refine Or.inl ⟨by omega, ?_⟩
      have h3 : c.2 - d.2 = 1 := by omega
      rw [h3]; simp

theorem isAdj_add_unit {u : Cell} (c : Cell) (hu : IsUnit u) : IsAdj c (c + u) := by
  rw [isAdj_iff_isUnit_sub]
  have : (c + u) - c = u := by ext <;> simp
  rw [this]
  exact hu

/-- A finite set closed under a fixed-point-free involution has even cardinal. -/
theorem even_card_of_fp_free_invol (f : Cell → Cell) :
    ∀ s : Finset Cell, (∀ c ∈ s, f c ∈ s) → (∀ c ∈ s, f (f c) = c) →
      (∀ c ∈ s, f c ≠ c) → Even s.card := by
  intro s
  induction s using Finset.strongInduction with
  | _ s IH =>
    intro hm hinv hfp
    by_cases he : s = ∅
    · rw [he]
      exact ⟨0, rfl⟩
    · obtain ⟨c, hc⟩ := Finset.nonempty_of_ne_empty he
      have hfc : f c ∈ s := hm c hc
      have hne : f c ≠ c := hfp c hc
      have hss : (s.erase c).erase (f c) ⊂ s := by
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨Finset.Subset.trans (Finset.erase_subset _ _) (Finset.erase_subset _ _), ?_⟩
        intro h
        have hmem : c ∈ (s.erase c).erase (f c) := by
          rw [h]
          exact hc
        simp at hmem
      have hm' : ∀ d ∈ (s.erase c).erase (f c), f d ∈ (s.erase c).erase (f c) := by
        intro d hd
        have hd1 : d ∈ s := (Finset.erase_subset _ _) ((Finset.erase_subset _ _) hd)
        have hdc : d ≠ c := (Finset.mem_erase.mp (Finset.mem_erase.mp hd).2).1
        have hdfc : d ≠ f c := (Finset.mem_erase.mp hd).1
        have hfd1 : f d ∈ s := hm d hd1
        have hfdc : f d ≠ c := by
          intro h
          have h1 := hinv d hd1
          rw [h] at h1
          exact hdfc h1.symm
        have hfdfc : f d ≠ f c := by
          intro h
          have h1 := hinv d hd1
          rw [h, hinv c hc] at h1
          exact hdc h1.symm
        exact Finset.mem_erase.mpr ⟨hfdfc, Finset.mem_erase.mpr ⟨hfdc, hfd1⟩⟩
      have hinv' : ∀ d ∈ (s.erase c).erase (f c), f (f d) = d := by
        intro d hd
        exact hinv d ((Finset.erase_subset _ _) ((Finset.erase_subset _ _) hd))
      have hfp' : ∀ d ∈ (s.erase c).erase (f c), f d ≠ d := by
        intro d hd
        exact hfp d ((Finset.erase_subset _ _) ((Finset.erase_subset _ _) hd))
      obtain ⟨k, hk⟩ := IH _ hss hm' hinv' hfp'
      have h2 : 2 ≤ s.card := by
        have hsub : ({c, f c} : Finset Cell) ⊆ s := by
          intro x hx
          simp at hx
          rcases hx with rfl | rfl
          · exact hc
          · exact hfc
        have hcard2 : ({c, f c} : Finset Cell).card = 2 := Finset.card_pair hne.symm
        calc 2 = ({c, f c} : Finset Cell).card := hcard2.symm
          _ ≤ s.card := Finset.card_le_card hsub
      have hcard : ((s.erase c).erase (f c)).card = s.card - 2 := by
        rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hne, hfc⟩),
          Finset.card_erase_of_mem hc]
        omega
      refine ⟨k + 1, ?_⟩
      rw [hk] at hcard
      omega

/-- A maximal grid-aligned configuration of dominoes on the `n × n` board,
encoded as an involution pairing covered cells with their domino partner. -/
structure Config (n : ℕ) where
  /-- The partner function. -/
  f : Cell → Cell
  /-- Off the board, `f` is the identity. -/
  hf_off : ∀ c, c ∉ board n → f c = c
  /-- `f` maps the board to itself. -/
  hf_map : ∀ c, c ∈ board n → f c ∈ board n
  /-- `f` is an involution on the board. -/
  hf_inv : ∀ c, c ∈ board n → f (f c) = c
  /-- Non-fixed cells are mapped to adjacent cells. -/
  hf_adj : ∀ c, c ∈ board n → f c ≠ c → IsAdj c (f c)
  /-- There is exactly one fixed point (the uncovered square). -/
  hf_fix : ∃! c, c ∈ board n ∧ f c = c

namespace Config

variable {n : ℕ} (C : Config n)

theorem hf_inv' (c : Cell) : C.f (C.f c) = c ∨ c ∉ board n := by
  by_cases hc : c ∈ board n
  · exact Or.inl (C.hf_inv c hc)
  · exact Or.inr hc

/-- The unique uncovered square. -/
noncomputable def empty : Cell := C.hf_fix.choose

theorem empty_mem : C.empty ∈ board n := (C.hf_fix.choose_spec.1).1

theorem empty_fixed : C.f C.empty = C.empty := (C.hf_fix.choose_spec.1).2

theorem unique_fixed {c : Cell} (hc : c ∈ board n) (hfc : C.f c = c) : c = C.empty :=
  C.hf_fix.choose_spec.2 c ⟨hc, hfc⟩

/-- A configuration is determined by its values on the board. -/
theorem ext {C₁ C₂ : Config n} (h : ∀ c ∈ board n, C₁.f c = C₂.f c) : C₁ = C₂ := by
  have hf : C₁.f = C₂.f := by
    funext c
    by_cases hc : c ∈ board n
    · exact h c hc
    · rw [C₁.hf_off c hc, C₂.hf_off c hc]
  cases C₁; cases C₂; congr

/-- A slide move: if the uncovered square is `e`, and the two cells `e + u`,
`e + 2u` are on the board with the domino `{e + u, e + 2u}` present, then that
domino may slide to `{e, e + u}`, leaving `e + 2u` uncovered. -/
def Slide (C C' : Config n) : Prop :=
  ∃ e u : Cell, IsUnit u ∧ C.f e = e ∧ (e + u) ∈ board n ∧ (e + 2 • u) ∈ board n ∧
    C.f (e + u) = e + 2 • u ∧
    ∀ c, C'.f c = if c = e then e + u
                  else if c = e + u then e
                  else if c = e + 2 • u then e + 2 • u
                  else C.f c

/-- Reachability by a sequence of slides. -/
def Reachable : Config n → Config n → Prop := Relation.ReflTransGen Slide

/-- `k(C)`: the number of configurations reachable from `C`. -/
noncomputable def kval : ℕ := Nat.card { C' : Config n // Reachable C C' }

end Config

/-!
## Finiteness
-/

/-- The function `C ↦ f|board` is injective. -/
theorem config_injective_restrict {n : ℕ} :
    Function.Injective (fun C : Config n => fun c : board n =>
      (⟨C.f c, C.hf_map c c.2⟩ : ↥(board n))) := by
  intro C₁ C₂ h
  apply Config.ext
  intro c hc
  exact congrArg Subtype.val (congrFun h ⟨c, hc⟩)

noncomputable instance {n : ℕ} : Fintype (Config n) := by
  classical
  exact Fintype.ofInjective _ config_injective_restrict

instance {n : ℕ} (C : Config n) : Finite { C' : Config n // C.Reachable C' } := by
  apply Finite.of_injective (fun c : { C' : Config n // C.Reachable C' } => (c.1 : Config n))
  intro a b h
  exact Subtype.ext h

theorem Config.kval_pos {n : ℕ} (C : Config n) : 1 ≤ C.kval := by
  unfold Config.kval
  have : Nonempty { C' : Config n // C.Reachable C' } := ⟨⟨C, Relation.ReflTransGen.refl⟩⟩
  exact Nat.card_pos_iff.mpr ⟨this, inferInstance⟩

/-!
## The arrow graph `G`

For a configuration `C` with uncovered square `e`, the *special* cells are the
cells of the board sharing the coordinate parities of `e`.  Every covered special
cell `s` carries a domino `{s, s + u}`; we draw an arrow `s ↦ s + 2u`, the next
cell with the same coordinate parities.  Sliding a domino reverses one arrow.
-/

namespace Config

variable {n : ℕ} (C : Config n)

/-- Special cells: board cells sharing both coordinate parities with the
uncovered square. -/
noncomputable def special : Finset Cell :=
  (board n).filter (fun c => c.1 % 2 = C.empty.1 % 2 ∧ c.2 % 2 = C.empty.2 % 2)

theorem mem_special {c : Cell} :
    c ∈ C.special ↔ c ∈ board n ∧ c.1 % 2 = C.empty.1 % 2 ∧ c.2 % 2 = C.empty.2 % 2 := by
  simp [special]

theorem empty_mem_special : C.empty ∈ C.special := by
  rw [mem_special]; exact ⟨C.empty_mem, rfl, rfl⟩

/-- The arrow target of a covered special cell `s`. -/
def arrow (s : Cell) : Cell := s + 2 • (C.f s - s)

theorem arrow_eq_self_of_not_covered {s : Cell} (hs : C.f s = s) : C.arrow s = s := by
  simp [arrow, hs]

theorem arrow_parity (s : Cell) :
    (C.arrow s).1 % 2 = s.1 % 2 ∧ (C.arrow s).2 % 2 = s.2 % 2 := by
  have h1 : (C.arrow s).1 = s.1 + 2 * ((C.f s).1 - s.1) := by
    simp [arrow]
  have h2 : (C.arrow s).2 = s.2 + 2 * ((C.f s).2 - s.2) := by
    simp [arrow]
  exact ⟨by rw [h1]; omega, by rw [h2]; omega⟩

/-- If `s` is covered and the arrow stays on the board, then the target is
special. -/
theorem arrow_mem_special {s : Cell} (hs : s ∈ C.special) (_hne : s ≠ C.empty)
    (harr : C.arrow s ∈ board n) : C.arrow s ∈ C.special := by
  rw [mem_special] at hs ⊢
  obtain ⟨h1, h2⟩ := C.arrow_parity s
  exact ⟨harr, by rw [h1]; exact hs.2.1, by rw [h2]; exact hs.2.2⟩

/-- The step from a covered special cell to its domino partner is a unit
vector. -/
theorem arrow_step_unit {s : Cell} (hs : s ∈ board n) (hne : C.f s ≠ s) :
    IsUnit (C.f s - s) := IsAdj.isUnit _ _ (C.hf_adj s hs hne)

/-- Adjacency in the arrow graph: `s` points to `t` or `t` points to `s`,
with the source a covered special cell and the target on the board. -/
def gAdj (s t : Cell) : Prop :=
  (s ∈ C.special ∧ s ≠ C.empty ∧ C.arrow s = t ∧ t ∈ board n) ∨
  (t ∈ C.special ∧ t ≠ C.empty ∧ C.arrow t = s ∧ s ∈ board n)

theorem gAdj_symm {s t : Cell} : C.gAdj s t → C.gAdj t s := fun h => h.symm

/-- Connectivity in the arrow graph. -/
def gConn : Cell → Cell → Prop := Relation.ReflTransGen (C.gAdj · ·)

/-- The component of the uncovered square in the arrow graph, as a finite set
of (special) cells. -/
noncomputable def comp : Finset Cell := by
  classical
  exact C.special.filter (fun s => C.gConn s C.empty)

theorem mem_comp {s : Cell} : s ∈ C.comp ↔ s ∈ C.special ∧ C.gConn s C.empty := by
  classical
  simp [comp]

theorem empty_mem_comp : C.empty ∈ C.comp := by
  rw [mem_comp]; exact ⟨C.empty_mem_special, Relation.ReflTransGen.refl⟩

theorem mem_board_of_mem_special {s : Cell} (hs : s ∈ C.special) : s ∈ board n :=
  ((mem_special C).mp hs).1

theorem mem_board_of_mem_comp {s : Cell} (hs : s ∈ C.comp) : s ∈ board n :=
  mem_board_of_mem_special C ((mem_comp C).mp hs).1

theorem gAdj_left_special {s t : Cell} (h : C.gAdj s t) : s ∈ C.special := by
  rcases h with ⟨hs, _, harr, _⟩ | ⟨ht, hne, harr, hs⟩
  · exact hs
  · rw [← harr]
    exact C.arrow_mem_special ht hne (harr ▸ hs)

theorem gAdj_right_special {s t : Cell} (h : C.gAdj s t) : t ∈ C.special :=
  C.gAdj_left_special h.symm

theorem gConn_special {s t : Cell} (h : C.gConn s t) : s ∈ C.special → t ∈ C.special := by
  induction h with
  | refl => exact id
  | tail _ hbc _ => exact fun _ => C.gAdj_right_special hbc

end Config

/-!
## Effect of a slide on the arrow graph
-/

namespace Config

variable {n : ℕ}

/-- The sliding update of a configuration. -/
def slideFun (C : Config n) (e u : Cell) : Cell → Cell :=
  fun c => if c = e then e + u
           else if c = e + u then e
           else if c = e + 2 • u then e + 2 • u
           else C.f c

theorem slideFun_valid {n : ℕ} (C : Config n) {e u : Cell} (hu : IsUnit u)
    (he : C.f e = e) (heb : e ∈ board n) (hu1 : e + u ∈ board n)
    (hu2 : e + 2 • u ∈ board n) (hdom : C.f (e + u) = e + 2 • u) :
    ∃ C' : Config n, C'.f = C.slideFun e u := by
  classical
  have hu0 : u ≠ 0 := by
    rcases hu with rfl | rfl | rfl | rfl <;> simp
  have hsub1 : ∀ a : Cell, (a + u) - a = u := by
    intro a; ext <;> simp [Prod.smul_mk, smul_eq_mul] <;> omega
  have hsub2 : ∀ a : Cell, (a + 2 • u) - (a + u) = u := by
    intro a; ext <;> simp [Prod.smul_mk, smul_eq_mul] <;> omega
  have hsub3 : ∀ a : Cell, (a + 2 • u) - a = 2 • u := by
    intro a; ext <;> simp [Prod.smul_mk, smul_eq_mul] <;> omega
  have hne : e + u ≠ e := by
    intro h
    have h1 := congrArg (fun c => c - e) h
    rw [hsub1, sub_self] at h1
    exact hu0 h1
  have hne2 : e + 2 • u ≠ e + u := by
    intro h
    have h1 := congrArg (fun c => c - (e + u)) h
    rw [hsub2, sub_self] at h1
    exact hu0 h1
  have hne3 : e + 2 • u ≠ e := by
    intro h
    have h1 := congrArg (fun c => c - e) h
    rw [hsub3, sub_self] at h1
    have h2 : u = 0 := by
      have ha := congrArg Prod.fst h1
      have hb := congrArg Prod.snd h1
      simp at ha hb
      ext <;> omega
    exact hu0 h2
  have hce : e = C.empty := C.unique_fixed heb he
  refine ⟨⟨C.slideFun e u, ?_, ?_, ?_, ?_, ?_⟩, rfl⟩
  · -- off board: identity
    intro c hc
    simp only [slideFun]
    have hc1 : c ≠ e := fun h => hc (h ▸ heb)
    have hc2 : c ≠ e + u := fun h => hc (h ▸ hu1)
    have hc3 : c ≠ e + 2 • u := fun h => hc (h ▸ hu2)
    rw [if_neg hc1, if_neg hc2, if_neg hc3]
    exact C.hf_off c hc
  · -- maps to board
    intro c hc
    simp only [slideFun]
    split_ifs with h1 h2 h3
    · exact hu1
    · exact heb
    · exact hu2
    · exact C.hf_map c hc
  · -- involutive
    intro c hc
    simp only [slideFun]
    by_cases h1 : c = e
    · subst h1
      rw [if_pos rfl, if_neg hne, if_pos rfl]
    · by_cases h2 : c = e + u
      · subst h2
        rw [if_neg h1, if_pos rfl, if_pos rfl]
      · by_cases h3 : c = e + 2 • u
        · subst h3
          rw [if_neg h1, if_neg h2, if_pos rfl, if_neg h1, if_neg h2, if_pos rfl]
        · have hfc1 : C.f c ≠ e := by
            intro h
            have h4 := C.hf_inv c hc
            rw [h, he] at h4
            exact h1 h4.symm
          have hfc2 : C.f c ≠ e + u := by
            intro h
            have h4 := C.hf_inv c hc
            rw [h, hdom] at h4
            exact h3 h4.symm
          have hfc3 : C.f c ≠ e + 2 • u := by
            intro h
            have h4 := C.hf_inv c hc
            rw [h] at h4
            have h5 : C.f (e + 2 • u) = e + u := by
              have h6 := C.hf_inv (e + u) hu1
              rw [hdom] at h6
              exact h6
            rw [h5] at h4
            exact h2 h4.symm
          rw [if_neg h1, if_neg h2, if_neg h3, if_neg hfc1, if_neg hfc2, if_neg hfc3]
          exact C.hf_inv c hc
  · -- adjacent
    intro c hc hfc
    simp only [slideFun] at hfc ⊢
    split_ifs at hfc ⊢ with h1 h2 h3
    · rw [← h1]
      exact isAdj_add_unit c hu
    · rw [h2, isAdj_iff_isUnit_sub]
      have h4 : e - (e + u) = -u := by ext <;> simp
      rw [h4]
      exact IsUnit.neg hu
    · exfalso; exact hfc h3.symm
    · exact C.hf_adj c hc hfc
  · -- unique fixed point
    refine ⟨e + 2 • u, ⟨hu2, by simp only [slideFun]; rw [if_neg hne3, if_neg hne2, if_true]⟩, ?_⟩
    intro c ⟨hc, hfc⟩
    simp only [slideFun] at hfc
    split_ifs at hfc with h1 h2 h3
    · subst h1
      exfalso; exact hne hfc
    · subst h2
      exfalso; exact hne hfc.symm
    · exact h3
    · have : c = C.empty := C.unique_fixed hc hfc
      rw [← hce] at this
      exact absurd this h1
end Config

namespace Config

variable {n : ℕ} (C C' : Config n)

/-- The empty cell of a slid configuration. -/
theorem slide_empty {e u : Cell} (hu : IsUnit u) (he : C.f e = e)
    (heb : e ∈ board n) (hu2 : e + 2 • u ∈ board n) (hupd : C'.f = C.slideFun e u) :
    C'.empty = e + 2 • u := by
  have hfix : C'.f (e + 2 • u) = e + 2 • u := by
    rw [hupd]
    simp only [slideFun]
    have hu0 : u ≠ 0 := by
      rcases hu with rfl | rfl | rfl | rfl <;> simp
    have hne3 : e + 2 • u ≠ e := by
      intro h
      have h1 := congrArg (fun c => c - e) h
      have h2 : (e + 2 • u) - e = 2 • u := by ext <;> simp [Prod.smul_mk, smul_eq_mul] <;> omega
      rw [h2, sub_self] at h1
      have h3 : u = 0 := by
        have ha := congrArg Prod.fst h1
        have hb := congrArg Prod.snd h1
        simp at ha hb
        ext <;> omega
      exact hu0 h3
    have hne2 : e + 2 • u ≠ e + u := by
      intro h
      have h1 := congrArg (fun c => c - (e + u)) h
      have h2 : (e + 2 • u) - (e + u) = u := by ext <;> simp [Prod.smul_mk, smul_eq_mul] <;> omega
      rw [h2, sub_self] at h1
      exact hu0 h1
    rw [if_neg hne3, if_neg hne2, if_true]
  have hmem : e + 2 • u ∈ board n := hu2
  exact (C'.unique_fixed hmem hfix).symm

/-- Sliding preserves the set of special cells. -/
theorem slide_special {e u : Cell} (hu : IsUnit u) (he : C.f e = e)
    (heb : e ∈ board n) (hu2 : e + 2 • u ∈ board n) (hupd : C'.f = C.slideFun e u) :
    C'.special = C.special := by
  have hempty : C'.empty = e + 2 • u := slide_empty C C' hu he heb hu2 hupd
  have hce : e = C.empty := C.unique_fixed heb he
  ext s
  simp only [special, Finset.mem_filter]
  rw [hempty]
  have hpar1 : (e + 2 • u).1 % 2 = e.1 % 2 := by
    have h1 : (e + 2 • u).1 = e.1 + 2 * u.1 := by simp [Prod.smul_mk, smul_eq_mul]
    rw [h1]; omega
  have hpar2 : (e + 2 • u).2 % 2 = e.2 % 2 := by
    have h1 : (e + 2 • u).2 = e.2 + 2 * u.2 := by simp [Prod.smul_mk, smul_eq_mul]
    rw [h1]; omega
  rw [hpar1, hpar2, hce]

/-- Arrows at cells other than the two involved in the slide are unchanged. -/
theorem slide_arrow_ne {e u : Cell} (hupd : C'.f = C.slideFun e u) {s : Cell}
    (hs1 : s ≠ e) (hs2 : s ≠ e + 2 • u) (hs3 : s ≠ e + u) :
    C'.arrow s = C.arrow s := by
  simp only [arrow, hupd, slideFun]
  rw [if_neg hs1, if_neg hs3, if_neg hs2]

theorem slide_arrow_e {e u : Cell} (hupd : C'.f = C.slideFun e u) :
    C'.arrow e = e + 2 • u := by
  simp only [arrow, hupd, slideFun, if_pos rfl]
  ext <;> simp [Prod.smul_mk, smul_eq_mul] <;> omega

/-- The arrow graph is unchanged by a slide (the edge is only reversed). -/
theorem slide_gAdj {e u : Cell} (hu : IsUnit u) (he : C.f e = e)
    (heb : e ∈ board n) (hu1 : e + u ∈ board n) (hu2 : e + 2 • u ∈ board n)
    (hdom : C.f (e + u) = e + 2 • u) (hupd : C'.f = C.slideFun e u) (s t : Cell) :
    C'.gAdj s t ↔ C.gAdj s t := by
  have hspecial : C'.special = C.special := slide_special C C' hu he heb hu2 hupd
  have hempty : C'.empty = e + 2 • u := slide_empty C C' hu he heb hu2 hupd
  have hce : e = C.empty := C.unique_fixed heb he
  have hu0 : u ≠ 0 := by
    rcases hu with rfl | rfl | rfl | rfl <;> simp
  have hne : e + u ≠ e := by
    intro h
    have h1 := congrArg (fun c => c - e) h
    have h2 : (e + u) - e = u := by ext <;> simp <;> omega
    rw [h2, sub_self] at h1
    exact hu0 h1
  have hne2 : e + 2 • u ≠ e + u := by
    intro h
    have h1 := congrArg (fun c => c - (e + u)) h
    have h2 : (e + 2 • u) - (e + u) = u := by ext <;> simp [Prod.smul_mk, smul_eq_mul] <;> omega
    rw [h2, sub_self] at h1
    exact hu0 h1
  have hne3 : e + 2 • u ≠ e := by
    intro h
    have h1 := congrArg (fun c => c - e) h
    have h2 : (e + 2 • u) - e = 2 • u := by ext <;> simp [Prod.smul_mk, smul_eq_mul] <;> omega
    rw [h2, sub_self] at h1
    have h3 : u = 0 := by
      have ha := congrArg Prod.fst h1
      have hb := congrArg Prod.snd h1
      simp at ha hb
      ext <;> omega
    exact hu0 h3
  have hfe2u : C.f (e + 2 • u) = e + u := by
    have := C.hf_inv (e + u) hu1
    rw [hdom] at this
    exact this
  have harr_e2u : C.arrow (e + 2 • u) = e := by
    simp only [arrow, hfe2u]
    ext <;> simp [Prod.smul_mk, smul_eq_mul] <;> omega
  have harr'_e : C'.arrow e = e + 2 • u := slide_arrow_e C C' hupd
  have hpar1 : (e + 2 • u).1 % 2 = e.1 % 2 := by
    have h1 : (e + 2 • u).1 = e.1 + 2 * u.1 := by simp [Prod.smul_mk, smul_eq_mul]
    rw [h1]; omega
  have hpar2 : (e + 2 • u).2 % 2 = e.2 % 2 := by
    have h1 : (e + 2 • u).2 = e.2 + 2 * u.2 := by simp [Prod.smul_mk, smul_eq_mul]
    rw [h1]; omega
  have he2u_special : e + 2 • u ∈ C.special := by
    rw [mem_special]
    refine ⟨hu2, by rw [hpar1, hce], by rw [hpar2, hce]⟩
  have hns : e + u ∉ C.special := by
    rw [mem_special]
    rintro ⟨-, h1, h2⟩
    have hce1 : C.empty.1 = e.1 := congrArg Prod.fst hce.symm
    have hce2 : C.empty.2 = e.2 := congrArg Prod.snd hce.symm
    rcases hu with rfl | rfl | rfl | rfl
    · rw [hce1] at h1
      have h3 : (e + ((1 : ℤ), (0 : ℤ))).1 % 2 = e.1 % 2 := h1
      simp at h3; omega
    · rw [hce1] at h1
      have h3 : (e + ((-1 : ℤ), (0 : ℤ))).1 % 2 = e.1 % 2 := h1
      simp at h3; omega
    · rw [hce2] at h2
      have h3 : (e + ((0 : ℤ), (1 : ℤ))).2 % 2 = e.2 % 2 := h2
      simp at h3; omega
    · rw [hce2] at h2
      have h3 : (e + ((0 : ℤ), (-1 : ℤ))).2 % 2 = e.2 % 2 := h2
      simp at h3; omega
  unfold gAdj
  rw [hspecial, hempty]
  constructor
  · rintro (⟨hs, hsne, harr, htb⟩ | ⟨ht, htne, harr, hsb⟩)
    · by_cases hse : s = e
      · subst hse
        rw [harr'_e] at harr
        subst harr
        exact Or.inr ⟨he2u_special, fun h => hne3 (h.trans hce.symm), harr_e2u, heb⟩
      · by_cases hse2 : s = e + 2 • u
        · subst hse2
          exact absurd rfl hsne
        · by_cases hseu : s = e + u
          · subst hseu
            exact absurd hs hns
          · rw [slide_arrow_ne C C' hupd hse hse2 hseu] at harr
            exact Or.inl ⟨hs, fun h => hse (h.trans hce.symm), harr, htb⟩
    · by_cases hte : t = e
      · subst hte
        rw [harr'_e] at harr
        subst harr
        exact Or.inl ⟨he2u_special, fun h => hne3 (h.trans hce.symm), harr_e2u, heb⟩
      · by_cases hte2 : t = e + 2 • u
        · subst hte2
          exact absurd rfl htne
        · by_cases hteu : t = e + u
          · subst hteu
            exact absurd ht hns
          · rw [slide_arrow_ne C C' hupd hte hte2 hteu] at harr
            exact Or.inr ⟨ht, fun h => hte (h.trans hce.symm), harr, hsb⟩
  · rintro (⟨hs, hsne, harr, htb⟩ | ⟨ht, htne, harr, hsb⟩)
    · by_cases hse2 : s = e + 2 • u
      · subst hse2
        rw [harr_e2u] at harr
        subst harr
        exact Or.inr ⟨hce.symm ▸ C.empty_mem_special, hne3.symm, harr'_e, hu2⟩
      · have hse : s ≠ e := fun h => hsne (h.trans hce)
        have hseu : s ≠ e + u := by
          intro h
          subst h
          exact hns hs
        rw [← slide_arrow_ne C C' hupd hse hse2 hseu] at harr
        exact Or.inl ⟨hs, hse2, harr, htb⟩
    · by_cases hte2 : t = e + 2 • u
      · subst hte2
        rw [harr_e2u] at harr
        subst harr
        exact Or.inl ⟨hce.symm ▸ C.empty_mem_special, hne3.symm, harr'_e, hu2⟩
      · have hte : t ≠ e := fun h => htne (h.trans hce)
        have hteu : t ≠ e + u := by
          intro h
          subst h
          exact hns ht
        rw [← slide_arrow_ne C C' hupd hte hte2 hteu] at harr
        exact Or.inr ⟨ht, hte2, harr, hsb⟩

/-- The component of the uncovered square is unchanged (as a set of cells). -/
theorem slide_comp {e u : Cell} (hu : IsUnit u) (he : C.f e = e)
    (heb : e ∈ board n) (hu1 : e + u ∈ board n) (hu2 : e + 2 • u ∈ board n)
    (hdom : C.f (e + u) = e + 2 • u) (hupd : C'.f = C.slideFun e u) :
    C'.comp = C.comp := by
  have hg : ∀ s t, C'.gAdj s t ↔ C.gAdj s t := slide_gAdj C C' hu he heb hu1 hu2 hdom hupd
  have hconn : ∀ s t, C'.gConn s t ↔ C.gConn s t := by
    intro s t
    constructor
    · intro h
      induction h with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ hbc ih => exact Relation.ReflTransGen.tail ih ((hg _ _).mp hbc)
    · intro h
      induction h with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ hbc ih => exact Relation.ReflTransGen.tail ih ((hg _ _).mpr hbc)
  have hspecial : C'.special = C.special := slide_special C C' hu he heb hu2 hupd
  have hempty : C'.empty = e + 2 • u := slide_empty C C' hu he heb hu2 hupd
  have hce : e = C.empty := C.unique_fixed heb he
  have hfe2u : C.f (e + 2 • u) = e + u := by
    have := C.hf_inv (e + u) hu1
    rw [hdom] at this
    exact this
  have harr_e2u : C.arrow (e + 2 • u) = e := by
    simp only [arrow, hfe2u]
    ext <;> simp [Prod.smul_mk, smul_eq_mul] <;> omega
  have hpar1 : (e + 2 • u).1 % 2 = e.1 % 2 := by
    have h1 : (e + 2 • u).1 = e.1 + 2 * u.1 := by simp [Prod.smul_mk, smul_eq_mul]
    rw [h1]; omega
  have hpar2 : (e + 2 • u).2 % 2 = e.2 % 2 := by
    have h1 : (e + 2 • u).2 = e.2 + 2 * u.2 := by simp [Prod.smul_mk, smul_eq_mul]
    rw [h1]; omega
  have he2u_special : e + 2 • u ∈ C.special := by
    rw [mem_special]
    refine ⟨hu2, by rw [hpar1, hce], by rw [hpar2, hce]⟩
  have hne3 : e + 2 • u ≠ e := by
    have hu0 : u ≠ 0 := by
      rcases hu with rfl | rfl | rfl | rfl <;> simp
    intro h
    have h1 := congrArg (fun c => c - e) h
    have h2 : (e + 2 • u) - e = 2 • u := by ext <;> simp [Prod.smul_mk, smul_eq_mul] <;> omega
    rw [h2, sub_self] at h1
    have h3 : u = 0 := by
      have ha := congrArg Prod.fst h1
      have hb := congrArg Prod.snd h1
      simp at ha hb
      ext <;> omega
    exact hu0 h3
  have hedge : C.gAdj (e + 2 • u) e :=
    Or.inl ⟨he2u_special, fun h => hne3 (h.trans hce.symm), harr_e2u, heb⟩
  ext s
  rw [mem_comp, mem_comp, hspecial]
  constructor
  · rintro ⟨hs, hc⟩
    refine ⟨hs, ?_⟩
    have hc1 : C.gConn s (e + 2 • u) := by
      rw [hempty] at hc
      exact (hconn _ _).mp hc
    have hc2 : C.gConn s e := Relation.ReflTransGen.tail hc1 hedge
    rwa [← hce]
  · rintro ⟨hs, hc⟩
    refine ⟨hs, ?_⟩
    have hc1 : C.gConn s (e + 2 • u) := by
      rw [← hce] at hc
      exact Relation.ReflTransGen.tail hc hedge.symm
    rw [← hempty] at hc1
    exact (hconn _ _).mpr hc1

end Config

/-!
## Arrow-graph distances and the flow to the uncovered square
-/

namespace Config

variable {n : ℕ} (C : Config n)

/-- Paths of exact length `k` in the arrow graph. -/
def gConnN : ℕ → Cell → Cell → Prop
  | 0, s, t => s = t
  | k + 1, s, t => ∃ m, C.gAdj s m ∧ gConnN k m t

theorem gConnN_zero {s t : Cell} : C.gConnN 0 s t ↔ s = t := Iff.rfl

theorem gConnN_succ {k : ℕ} {s t : Cell} :
    C.gConnN (k + 1) s t ↔ ∃ m, C.gAdj s m ∧ C.gConnN k m t := Iff.rfl

theorem gConnN_one {s t : Cell} : C.gConnN 1 s t ↔ C.gAdj s t := by
  constructor
  · rintro ⟨m, h, hm⟩
    rw [gConnN_zero] at hm
    rwa [hm] at h
  · intro h
    exact ⟨t, h, rfl⟩

theorem gConnN_trans {i j : ℕ} {s m t : Cell} :
    C.gConnN i s m → C.gConnN j m t → C.gConnN (i + j) s t := by
  induction i generalizing s with
  | zero =>
    intro h1 h2
    rw [gConnN_zero] at h1
    rw [Nat.zero_add]
    rwa [h1]
  | succ i ih =>
    intro h1 h2
    rw [gConnN_succ] at h1
    obtain ⟨m', h1, h1'⟩ := h1
    rw [Nat.succ_add]
    exact ⟨m', h1, ih h1' h2⟩

theorem gConnN_symm {k : ℕ} {s t : Cell} (h : C.gConnN k s t) : C.gConnN k t s := by
  induction k generalizing s t with
  | zero =>
    rw [gConnN_zero] at h ⊢
    exact h.symm
  | succ k ih =>
    rw [gConnN_succ] at h
    obtain ⟨m, h1, h2⟩ := h
    exact gConnN_trans C (ih h2) ((gConnN_one C).mpr h1.symm)

theorem gConnN_sound {k : ℕ} {s t : Cell} (h : C.gConnN k s t) : C.gConn s t := by
  induction k generalizing s with
  | zero =>
    rw [gConnN_zero] at h
    rw [h]
    exact Relation.ReflTransGen.refl
  | succ k ih =>
    rw [gConnN_succ] at h
    obtain ⟨m, h1, h2⟩ := h
    exact Relation.ReflTransGen.head h1 (ih h2)

theorem gConn_iff_exists {s t : Cell} : C.gConn s t ↔ ∃ k, C.gConnN k s t := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨0, rfl⟩
    | tail _ hbc ih =>
      obtain ⟨k, hk⟩ := ih
      exact ⟨k + 1, gConnN_trans C hk ((gConnN_one C).mpr hbc)⟩
  · rintro ⟨k, hk⟩
    exact gConnN_sound C hk

/-- The distance to the uncovered square in the arrow graph (junk value `0`
outside the component). -/
noncomputable def dist (s : Cell) : ℕ := by
  classical
  exact if h : ∃ k, C.gConnN k s C.empty then Nat.find h else 0

theorem dist_gConnN {s : Cell} (hs : s ∈ C.comp) : C.gConnN (C.dist s) s C.empty := by
  classical
  have h : ∃ k, C.gConnN k s C.empty := by
    rw [mem_comp] at hs
    exact (gConn_iff_exists C).mp hs.2
  simp only [dist, dif_pos h]
  exact Nat.find_spec h

theorem dist_min {s : Cell} (hs : s ∈ C.comp) {k : ℕ} (hk : C.gConnN k s C.empty) :
    C.dist s ≤ k := by
  classical
  have h : ∃ k, C.gConnN k s C.empty := ⟨k, hk⟩
  simp only [dist, dif_pos h]
  exact Nat.find_min' h hk

theorem dist_empty : C.dist C.empty = 0 := by
  classical
  have h : ∃ k, C.gConnN k C.empty C.empty := ⟨0, rfl⟩
  simp only [dist, dif_pos h]
  exact (Nat.find_eq_zero h).mpr rfl

theorem dist_eq_zero {s : Cell} (hs : s ∈ C.comp) (h0 : C.dist s = 0) : s = C.empty := by
  have h := dist_gConnN C hs
  rw [h0, gConnN_zero] at h
  exact h

theorem mem_comp_of_gAdj {s t : Cell} (h : C.gAdj s t) (hs : s ∈ C.comp) : t ∈ C.comp := by
  rw [mem_comp] at hs ⊢
  exact ⟨C.gAdj_right_special h, Relation.ReflTransGen.head h.symm hs.2⟩

theorem dist_step {s : Cell} (hs : s ∈ C.comp) (hne : s ≠ C.empty) :
    ∃ m, C.gAdj s m ∧ C.dist m = C.dist s - 1 := by
  have h0 : C.dist s ≠ 0 := fun h => hne (dist_eq_zero C hs h)
  have hpos : 0 < C.dist s := Nat.pos_of_ne_zero h0
  have hspec := dist_gConnN C hs
  have hrewrite : C.dist s - 1 + 1 = C.dist s := by omega
  rw [← hrewrite, gConnN_succ] at hspec
  obtain ⟨m, h1, h2⟩ := hspec
  have hmem : m ∈ C.comp := by
    rw [mem_comp]
    exact ⟨C.gAdj_right_special h1, gConnN_sound C h2⟩
  refine ⟨m, h1, ?_⟩
  have hle1 : C.dist m ≤ C.dist s - 1 := dist_min C hmem h2
  have hle2 : C.dist s ≤ C.dist m + 1 := by
    have hs' : C.gConnN (C.dist m + 1) s C.empty := by
      rw [gConnN_succ]
      exact ⟨m, h1, dist_gConnN C hmem⟩
    exact dist_min C hs hs'
  omega

theorem dist_le_adj {s t : Cell} (h : C.gAdj s t) (hs : s ∈ C.comp) (ht : t ∈ C.comp) :
    C.dist s ≤ C.dist t + 1 := by
  have hs' : C.gConnN (C.dist t + 1) s C.empty := by
    rw [gConnN_succ]
    exact ⟨t, h, dist_gConnN C ht⟩
  exact dist_min C hs hs'

/-!
## The flow to the uncovered square: counting argument
-/

/-- Two cells cannot point their arrows at each other. -/
theorem arrow_no_2cycle {s t : Cell} (hs : s ∈ board n) (ht : t ∈ board n)
    (h1 : C.arrow s = t) (h2 : C.arrow t = s) : s = t := by
  have e1 : 2 * ((C.f s).1 - s.1) = t.1 - s.1 := by
    have ht1 : t = s + 2 • (C.f s - s) := h1.symm
    have : t.1 = s.1 + 2 * ((C.f s).1 - s.1) := by
      rw [ht1]; simp [Prod.smul_mk, smul_eq_mul]
    omega
  have e2 : 2 * ((C.f t).1 - t.1) = s.1 - t.1 := by
    have hs1 : s = t + 2 • (C.f t - t) := h2.symm
    have : s.1 = t.1 + 2 * ((C.f t).1 - t.1) := by
      rw [hs1]; simp [Prod.smul_mk, smul_eq_mul]
    omega
  have e3 : 2 * ((C.f s).2 - s.2) = t.2 - s.2 := by
    have ht2 : t = s + 2 • (C.f s - s) := h1.symm
    have : t.2 = s.2 + 2 * ((C.f s).2 - s.2) := by
      rw [ht2]; simp [Prod.smul_mk, smul_eq_mul]
    omega
  have e4 : 2 * ((C.f t).2 - t.2) = s.2 - t.2 := by
    have hs2 : s = t + 2 • (C.f t - t) := h2.symm
    have : s.2 = t.2 + 2 * ((C.f t).2 - t.2) := by
      rw [hs2]; simp [Prod.smul_mk, smul_eq_mul]
    omega
  have hfs : C.f s = C.f t := by
    ext <;> omega
  have h1' := C.hf_inv s hs
  have h2' := C.hf_inv t ht
  rw [hfs] at h1'
  rw [h2'] at h1'
  exact h1'.symm

/-- Component vertices with an outgoing arrow. -/
noncomputable def compA : Finset Cell :=
  C.comp.filter (fun s => s ≠ C.empty ∧ C.arrow s ∈ board n)

/-- Component vertices (other than the empty cell) without an outgoing arrow. -/
noncomputable def compB : Finset Cell :=
  C.comp.filter (fun s => s ≠ C.empty ∧ C.arrow s ∉ board n)

theorem card_compA_add_card_compB : C.compA.card + C.compB.card = C.comp.card - 1 := by
  classical
  have h : C.compA ∪ C.compB = C.comp.erase C.empty := by
    ext s
    simp only [compA, compB, Finset.mem_filter, Finset.mem_union, Finset.mem_erase]
    constructor
    · rintro (⟨h1, h2, -⟩ | ⟨h1, h2, -⟩)
      · exact ⟨h2, h1⟩
      · exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩
      by_cases h3 : C.arrow s ∈ board n
      · exact Or.inl ⟨h2, h1, h3⟩
      · exact Or.inr ⟨h2, h1, h3⟩
  have hd : Disjoint C.compA C.compB := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    ext s
    simp only [compA, compB, Finset.mem_filter, Finset.mem_inter, Finset.notMem_empty,
      iff_false]
    tauto
  rw [← Finset.card_union_of_disjoint hd, h, Finset.card_erase_of_mem C.empty_mem_comp]

/-- The undirected edges of the component. -/
noncomputable def compE : Finset (Sym2 Cell) := by
  classical
  exact ((C.comp ×ˢ C.comp).filter (fun p => C.gAdj p.1 p.2)).image (fun p => Sym2.mk p.1 p.2)

/-- Arrows as undirected edges. -/
noncomputable def arrowEdges : Finset (Sym2 Cell) := by
  classical
  exact C.compA.image (fun s => Sym2.mk s (C.arrow s))

theorem card_arrowEdges : C.arrowEdges.card = C.compA.card := by
  classical
  unfold arrowEdges
  rw [Finset.card_image_iff.mpr (by
    intro s hs t ht hst
    simp only [compA, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe] at hs ht
    change Sym2.mk s (C.arrow s) = Sym2.mk t (C.arrow t) at hst
    rcases Sym2.mk_eq_mk_iff (p := (s, C.arrow s)) (q := (t, C.arrow t)).mp hst with h | h
    · exact congrArg Prod.fst h
    · have hsb : s ∈ board n := mem_board_of_mem_comp C hs.1
      have htb : t ∈ board n := mem_board_of_mem_comp C ht.1
      have h1 : C.arrow s = t := congrArg Prod.snd h
      have h2 : C.arrow t = s := (congrArg Prod.fst h).symm
      exact arrow_no_2cycle C hsb htb h1 h2)]

theorem compE_eq_arrowEdges : C.compE = C.arrowEdges := by
  classical
  ext e
  constructor
  · intro he
    simp only [compE, Finset.mem_image, Finset.mem_filter, Finset.mem_product] at he
    obtain ⟨p, ⟨hp, hg⟩, heq⟩ := he
    obtain ⟨hp1, hp2⟩ := hp
    rcases hg with ⟨hs', hsne, harr, htb⟩ | ⟨ht', htne, harr, hsb⟩
    · simp only [arrowEdges, Finset.mem_image]
      refine ⟨p.1, ?_, ?_⟩
      · simp only [compA, Finset.mem_filter]
        exact ⟨hp1, hsne, by rw [harr]; exact htb⟩
      · rw [← heq, harr]
    · simp only [arrowEdges, Finset.mem_image]
      refine ⟨p.2, ?_, ?_⟩
      · simp only [compA, Finset.mem_filter]
        exact ⟨hp2, htne, by rw [harr]; exact hsb⟩
      · rw [← heq, harr]
        exact Sym2.mk_eq_mk_iff (p := (p.2, p.1)) (q := p) |>.mpr (Or.inr rfl)
  · intro he
    simp only [arrowEdges, Finset.mem_image] at he
    obtain ⟨s, hs, heq⟩ := he
    simp only [compA, Finset.mem_filter] at hs
    obtain ⟨hsc, hsne, harr⟩ := hs
    have hga : C.gAdj s (C.arrow s) := Or.inl ⟨((mem_comp C).mp hsc).1, hsne, rfl, harr⟩
    have hmem : C.arrow s ∈ C.comp := mem_comp_of_gAdj C hga hsc
    rw [← heq]
    simp only [compE, Finset.mem_image, Finset.mem_filter, Finset.mem_product]
    exact ⟨(s, C.arrow s), ⟨⟨hsc, hmem⟩, hga⟩, rfl⟩

/-- The dist-edge choice function. -/
noncomputable def distNext (s : Cell) : Cell := by
  classical
  exact if h : s ∈ C.comp ∧ s ≠ C.empty then (C.dist_step h.1 h.2).choose else s

theorem distNext_spec {s : Cell} (hs : s ∈ C.comp) (hne : s ≠ C.empty) :
    C.gAdj s (C.distNext s) ∧ C.dist (C.distNext s) = C.dist s - 1 := by
  classical
  have h : s ∈ C.comp ∧ s ≠ C.empty := ⟨hs, hne⟩
  simp only [distNext, dif_pos h]
  exact (C.dist_step h.1 h.2).choose_spec

/-- Edges from each non-empty component vertex towards the empty cell. -/
noncomputable def distEdges : Finset (Sym2 Cell) := by
  classical
  exact (C.comp.erase C.empty).image (fun s => Sym2.mk s (C.distNext s))

theorem card_distEdges : C.distEdges.card = C.comp.card - 1 := by
  classical
  unfold distEdges
  rw [Finset.card_image_iff.mpr (by
    intro s hs t ht hst
    simp only [Finset.coe_erase, Set.mem_diff, Finset.mem_coe] at hs ht
    change Sym2.mk s (C.distNext s) = Sym2.mk t (C.distNext t) at hst
    rcases Sym2.mk_eq_mk_iff (p := (s, C.distNext s)) (q := (t, C.distNext t)).mp hst with h | h
    · exact congrArg Prod.fst h
    · have h1 : s = C.distNext t := congrArg Prod.fst h
      have h2 : C.distNext s = t := congrArg Prod.snd h
      have e1 := (distNext_spec C (Finset.mem_coe.mp ht.1) ht.2).2
      have e2 := (distNext_spec C (Finset.mem_coe.mp hs.1) hs.2).2
      rw [← h1] at e1
      rw [h2] at e2
      have hs0 : C.dist s ≠ 0 := fun h0 => hs.2 (dist_eq_zero C (Finset.mem_coe.mp hs.1) h0)
      omega)]
  exact Finset.card_erase_of_mem C.empty_mem_comp

theorem distEdges_subset_compE : C.distEdges ⊆ C.compE := by
  classical
  intro e he
  simp only [distEdges, Finset.mem_image, Finset.mem_erase] at he
  obtain ⟨s, ⟨hsne, hsc⟩, rfl⟩ := he
  have hspec := distNext_spec C hsc hsne
  have hga : C.gAdj s (C.distNext s) := hspec.1
  have hmem : C.distNext s ∈ C.comp := mem_comp_of_gAdj C hga hsc
  simp only [compE, Finset.mem_image, Finset.mem_filter, Finset.mem_product]
  exact ⟨(s, C.distNext s), ⟨⟨hsc, hmem⟩, hga⟩, rfl⟩

/-- Every non-empty component vertex has an on-board arrow. -/
theorem arrow_mem_board_of_mem_comp {s : Cell} (hs : s ∈ C.comp) (hne : s ≠ C.empty) :
    C.arrow s ∈ board n := by
  classical
  have hcard : C.compE.card ≥ C.comp.card - 1 := by
    calc C.compE.card ≥ C.distEdges.card := Finset.card_le_card (distEdges_subset_compE C)
    _ = C.comp.card - 1 := card_distEdges C
  have hsplit := card_compA_add_card_compB C
  rw [compE_eq_arrowEdges, card_arrowEdges] at hcard
  by_contra h
  have hmem : s ∈ C.compB := by
    simp only [compB, Finset.mem_filter]
    exact ⟨hs, hne, h⟩
  have hpos : 0 < C.compB.card := Finset.card_pos.mpr ⟨s, hmem⟩
  omega

/-- Iterating the arrow from any component vertex eventually reaches the
uncovered square.  (In particular the component is a tree rooted at the
uncovered square.) -/
theorem all_reachesEmpty {s : Cell} (hs : s ∈ C.comp) :
    ∃ k, (C.arrow)^[k] s = C.empty := by
  classical
  by_contra h
  push_neg at h
  have hstep : ∀ k, (C.arrow)^[k] s ∈ C.comp ∧ (C.arrow)^[k] s ≠ C.empty ∧
      C.arrow ((C.arrow)^[k] s) ∈ board n := by
    intro k
    induction k with
    | zero =>
      exact ⟨hs, h 0, arrow_mem_board_of_mem_comp C hs (h 0)⟩
    | succ k ih =>
      obtain ⟨hmem, hne, harr⟩ := ih
      have hga : C.gAdj ((C.arrow)^[k] s) ((C.arrow)^[k + 1] s) := by
        have h1 : (C.arrow)^[k + 1] s = C.arrow ((C.arrow)^[k] s) :=
          Function.iterate_succ_apply' _ _ _
        rw [h1]
        exact Or.inl ⟨(mem_comp C).mp hmem |>.1, hne, rfl, harr⟩
      have hmem' : (C.arrow)^[k + 1] s ∈ C.comp := mem_comp_of_gAdj C hga hmem
      exact ⟨hmem', h (k + 1), arrow_mem_board_of_mem_comp C hmem' (h (k + 1))⟩
  obtain ⟨i, j, hij, heq⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun k : ℕ => (⟨(C.arrow)^[k] s, (hstep k).1⟩ : ↥C.comp))
  have heq' : (C.arrow)^[i] s = (C.arrow)^[j] s := Subtype.ext_iff.mp heq
  suffices key : ∀ i j : ℕ, i < j → (C.arrow)^[i] s = (C.arrow)^[j] s → False by
    rcases lt_trichotomy i j with hlt | heq2 | hgt
    · exact key i j hlt heq'
    · exact absurd heq2 hij
    · exact key j i hgt heq'.symm
  intro i j hlt heq'
  -- the cycle set Z = {a_i, …, a_{j-1}}
  set a : ℕ → Cell := fun k => (C.arrow)^[k] s with ha
  obtain ⟨k, hkm, hkmax⟩ := Finset.exists_max_image (α := ℕ)
    ((Finset.Icc i (j - 1)).image a) (fun z => C.dist z) (by
      rw [Finset.Nonempty]
      refine ⟨a i, ?_⟩
      rw [Finset.mem_image]
      exact ⟨i, by rw [Finset.mem_Icc]; omega, rfl⟩)
  rw [Finset.mem_image] at hkm
  obtain ⟨kk, hkk, hkkz⟩ := hkm
  rw [← hkkz] at hkmax
  rw [Finset.mem_Icc] at hkk
  set z := a kk with hz
  have hzmem : z ∈ C.comp := (hstep kk).1
  have hzne : z ≠ C.empty := (hstep kk).2.1
  have hz0 : C.dist z ≠ 0 := fun h0 => hzne (dist_eq_zero C hzmem h0)
  have hzarr : C.arrow z ∈ board n := (hstep kk).2.2
  have hzk : C.arrow z = a (kk + 1) := by
    rw [hz, ha]
    exact (Function.iterate_succ_apply' _ _ _).symm
  -- predecessor of z in the cycle
  have hpred : ∃ p, p ∈ (Finset.Icc i (j - 1)).image a ∧ C.arrow p = z ∧ p ∈ C.comp := by
    by_cases hkk' : i < kk
    · refine ⟨a (kk - 1), ?_, ?_, (hstep (kk - 1)).1⟩
      · rw [Finset.mem_image]
        exact ⟨kk - 1, by rw [Finset.mem_Icc]; omega, rfl⟩
      · rw [hz]
        have h1 : kk - 1 + 1 = kk := by omega
        rw [← h1, ha]
        exact (Function.iterate_succ_apply' _ _ _).symm
    · have hkk'' : kk = i := by omega
      refine ⟨a (j - 1), ?_, ?_, (hstep (j - 1)).1⟩
      · rw [Finset.mem_image]
        exact ⟨j - 1, by rw [Finset.mem_Icc]; omega, rfl⟩
      · have h1 : (j - 1) + 1 = j := by omega
        have h2 : C.arrow (a (j - 1)) = (C.arrow)^[(j - 1) + 1] s :=
          (Function.iterate_succ_apply' _ _ _).symm
        rw [h2, h1, ← heq', ← hkk'']
  obtain ⟨p, hpz, hparr, hpmem⟩ := hpred
  have hpmax : C.dist p ≤ C.dist z := hkmax p hpz
  have hzmax : C.dist (C.arrow z) ≤ C.dist z := by
    apply hkmax
    rw [hzk, Finset.mem_image]
    by_cases hkj : kk + 1 ≤ j - 1
    · exact ⟨kk + 1, by rw [Finset.mem_Icc]; omega, rfl⟩
    · have hkj' : kk + 1 = j := by omega
      refine ⟨i, by rw [Finset.mem_Icc]; omega, ?_⟩
      rw [hkj']
      exact heq'
  have hga_z : C.gAdj z (C.arrow z) :=
    Or.inl ⟨(mem_comp C).mp hzmem |>.1, hzne, rfl, hzarr⟩
  have hpne : p ≠ C.empty := by
    have hpz' := hpz
    rw [Finset.mem_image] at hpz'
    obtain ⟨kp, hkp, hkpz⟩ := hpz'
    rw [← hkpz]
    exact (hstep kp).2.1
  have hparrb : C.arrow p ∈ board n := by
    rw [hparr]
    exact mem_board_of_mem_comp C hzmem
  have hga_p : C.gAdj p z :=
    Or.inl ⟨(mem_comp C).mp hpmem |>.1, hpne, hparr, mem_board_of_mem_comp C hzmem⟩
  have hcycle : C.arrow z ≠ p := by
    intro h
    have h2 := arrow_no_2cycle C (mem_board_of_mem_comp C hpmem)
      (mem_board_of_mem_comp C hzmem) hparr h
    rw [h2] at hparr
    have h3 : C.f z = z := by
      have h5 : 2 • (C.f z - z) = 0 := by
        apply add_left_injective z
        show 2 • (C.f z - z) + z = 0 + z
        rw [zero_add, add_comm]
        exact hparr
      have h8 := congrArg Prod.fst h5
      have h9 := congrArg Prod.snd h5
      simp [Prod.smul_mk] at h8 h9
      ext <;> omega
    exact hzne (C.unique_fixed (mem_board_of_mem_comp C hzmem) h3)
  -- the two cycle edges
  have hη1 : Sym2.mk z (C.arrow z) ∈ C.compE := by
    rw [compE_eq_arrowEdges]
    simp only [arrowEdges, Finset.mem_image]
    refine ⟨z, ?_, rfl⟩
    simp only [compA, Finset.mem_filter]
    exact ⟨hzmem, hzne, hzarr⟩
  have hη2 : Sym2.mk p z ∈ C.compE := by
    rw [compE_eq_arrowEdges]
    simp only [arrowEdges, Finset.mem_image]
    refine ⟨p, ?_, by rw [hparr]⟩
    simp only [compA, Finset.mem_filter]
    exact ⟨hpmem, hpne, hparrb⟩
  -- at least one of them is not a dist-edge
  have hnot : Sym2.mk z (C.arrow z) ∉ C.distEdges ∨ Sym2.mk p z ∉ C.distEdges := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨h1, h2⟩ := hcon
    have key1 : C.distNext z = C.arrow z := by
      simp only [distEdges, Finset.mem_image, Finset.mem_erase] at h1
      obtain ⟨v, ⟨hvne, hvc⟩, hv⟩ := h1
      have hmk := Sym2.mk_eq_mk_iff (p := (v, C.distNext v)) (q := (z, C.arrow z)).mp hv
      rcases hmk with hmk | hmk
      · have hv1 : v = z := congrArg Prod.fst hmk
        have hv2 : C.distNext v = C.arrow z := congrArg Prod.snd hmk
        rw [hv1] at hv2
        exact hv2
      · have hv1 : v = C.arrow z := congrArg Prod.fst hmk
        have hv2 : C.distNext v = z := congrArg Prod.snd hmk
        have e1 := (distNext_spec C hvc hvne).2
        rw [hv2, hv1] at e1
        omega
    have key2 : C.distNext z = p := by
      simp only [distEdges, Finset.mem_image, Finset.mem_erase] at h2
      obtain ⟨v, ⟨hvne, hvc⟩, hv⟩ := h2
      have hmk := Sym2.mk_eq_mk_iff (p := (v, C.distNext v)) (q := (p, z)).mp hv
      rcases hmk with hmk | hmk
      · have hv1 : v = p := congrArg Prod.fst hmk
        have hv2 : C.distNext v = z := congrArg Prod.snd hmk
        have e1 := (distNext_spec C hvc hvne).2
        rw [hv2, hv1] at e1
        omega
      · have hv1 : v = z := congrArg Prod.fst hmk
        have hv2 : C.distNext v = p := congrArg Prod.snd hmk
        rw [hv1] at hv2
        exact hv2
    rw [key1] at key2
    exact hcycle key2
  -- conclude: card compE > card distEdges, contradiction
  rcases hnot with hnot | hnot
  · have hsub : C.distEdges ⊂ C.compE :=
      (Finset.ssubset_iff_of_subset (distEdges_subset_compE C)).mpr
        ⟨Sym2.mk z (C.arrow z), hη1, hnot⟩
    have h1 : C.distEdges.card < C.compE.card := Finset.card_lt_card hsub
    rw [compE_eq_arrowEdges, card_arrowEdges, card_distEdges] at h1
    have hsplit := card_compA_add_card_compB C
    omega
  · have hsub : C.distEdges ⊂ C.compE :=
      (Finset.ssubset_iff_of_subset (distEdges_subset_compE C)).mpr
        ⟨Sym2.mk p z, hη2, hnot⟩
    have h1 : C.distEdges.card < C.compE.card := Finset.card_lt_card hsub
    rw [compE_eq_arrowEdges, card_arrowEdges, card_distEdges] at h1
    have hsplit := card_compA_add_card_compB C
    omega

end Config

/-!
## Reachability preserves the graph; `k(C)` equals the component size
-/

namespace Config

variable {n : ℕ} (C : Config n)

/-- Bundled facts about a slide step, including that `e ∈ board` (which follows
from the validity of the target configuration). -/
theorem slide_facts {C₁ C₂ : Config n} (h : C₁.Slide C₂) :
    ∃ e u, IsUnit u ∧ C₁.f e = e ∧ e = C₁.empty ∧ e ∈ board n ∧ (e + u) ∈ board n ∧
      (e + 2 • u) ∈ board n ∧ C₁.f (e + u) = e + 2 • u ∧ C₂.f = C₁.slideFun e u := by
  obtain ⟨e, u, hu, he, hu1, hu2, hdom, hupd⟩ := h
  have heb : e ∈ board n := by
    by_contra hb
    have h1 : C₂.f e = e := C₂.hf_off e hb
    have h2 : C₂.f e = e + u := by
      rw [hupd e, if_pos rfl]
    rw [h1] at h2
    have h3 : u = 0 := by
      have h4 := congrArg (fun c => c - e) h2
      simp at h4
      exact h4.symm
    rcases hu with rfl | rfl | rfl | rfl <;> simp at h3
  have hce : e = C₁.empty := C₁.unique_fixed heb he
  exact ⟨e, u, hu, he, hce, heb, hu1, hu2, hdom, funext hupd⟩

theorem gAdj_eq_of_reachable {C' : Config n} (h : C.Reachable C') (s t : Cell) :
    C'.gAdj s t ↔ C.gAdj s t := by
  induction h with
  | refl => exact Iff.rfl
  | tail hprev hstep ih =>
    obtain ⟨e, u, hu, he, hce, heb, hu1, hu2, hdom, hupd⟩ := slide_facts hstep
    exact (slide_gAdj _ _ hu he heb hu1 hu2 hdom hupd s t).trans ih

theorem special_eq_of_reachable {C' : Config n} (h : C.Reachable C') : C'.special = C.special := by
  induction h with
  | refl => rfl
  | tail hprev hstep ih =>
    obtain ⟨e, u, hu, he, hce, heb, hu1, hu2, hdom, hupd⟩ := slide_facts hstep
    rw [slide_special _ _ hu he heb hu2 hupd, ih]

theorem comp_eq_of_reachable {C' : Config n} (h : C.Reachable C') : C'.comp = C.comp := by
  induction h with
  | refl => rfl
  | tail hprev hstep ih =>
    obtain ⟨e, u, hu, he, hce, heb, hu1, hu2, hdom, hupd⟩ := slide_facts hstep
    rw [slide_comp _ _ hu he heb hu1 hu2 hdom hupd, ih]

/-- The number of arrow iterations needed to reach the uncovered square. -/
noncomputable def iterCount (s : Cell) : ℕ := by
  classical
  exact if h : ∃ k, (C.arrow)^[k] s = C.empty then Nat.find h else 0

theorem iterCount_spec {s : Cell} (hs : s ∈ C.comp) : (C.arrow)^[C.iterCount s] s = C.empty := by
  classical
  have h : ∃ k, (C.arrow)^[k] s = C.empty := all_reachesEmpty C hs
  simp only [iterCount, dif_pos h]
  exact Nat.find_spec h

theorem iterCount_min {s : Cell} (hs : s ∈ C.comp) {k : ℕ} (hk : (C.arrow)^[k] s = C.empty) :
    C.iterCount s ≤ k := by
  classical
  have h : ∃ k, (C.arrow)^[k] s = C.empty := ⟨k, hk⟩
  simp only [iterCount, dif_pos h]
  exact Nat.find_min' h hk

theorem iterCount_empty : C.iterCount C.empty = 0 := by
  classical
  have h : ∃ k, (C.arrow)^[k] C.empty = C.empty := ⟨0, rfl⟩
  simp only [iterCount, dif_pos h]
  exact (Nat.find_eq_zero h).mpr rfl

theorem iterCount_eq_zero {s : Cell} (hs : s ∈ C.comp) (h0 : C.iterCount s = 0) : s = C.empty := by
  have h := iterCount_spec C hs
  rw [h0] at h
  exact h

theorem iterCount_arrow {s : Cell} (hs : s ∈ C.comp) (hne : s ≠ C.empty) :
    C.iterCount (C.arrow s) = C.iterCount s - 1 := by
  classical
  have h0 : C.iterCount s ≠ 0 := fun h => hne (iterCount_eq_zero C hs h)
  have hpos : 0 < C.iterCount s := Nat.pos_of_ne_zero h0
  have hspec := iterCount_spec C hs
  have hrewrite : C.iterCount s - 1 + 1 = C.iterCount s := by omega
  have hspec' : (C.arrow)^[C.iterCount s - 1] (C.arrow s) = C.empty := by
    have h1 : (C.arrow)^[C.iterCount s - 1 + 1] s = C.empty := by
      rwa [← hrewrite] at hspec
    rwa [Function.iterate_succ_apply] at h1
  have hmem : C.arrow s ∈ C.comp := by
    have hga : C.gAdj s (C.arrow s) :=
      Or.inl ⟨(mem_comp C).mp hs |>.1, hne, rfl, arrow_mem_board_of_mem_comp C hs hne⟩
    exact mem_comp_of_gAdj C hga hs
  have hle1 : C.iterCount (C.arrow s) ≤ C.iterCount s - 1 := iterCount_min C hmem hspec'
  have hle2 : C.iterCount s ≤ C.iterCount (C.arrow s) + 1 := by
    have h2 : (C.arrow)^[C.iterCount (C.arrow s) + 1] s = C.empty := by
      rw [Function.iterate_succ_apply]
      exact iterCount_spec C hmem
    exact iterCount_min C hs h2
  omega

/-- The arrow of a reachable configuration is determined by its uncovered cell:
two reachable configurations with the same uncovered cell have the same arrows
on the whole component. -/
theorem arrow_eq_of_same_empty {C₁ C₂ : Config n} (h1 : C.Reachable C₁) (h2 : C.Reachable C₂)
    (he : C₁.empty = C₂.empty) {s : Cell} (hs : s ∈ C.comp) : C₂.arrow s = C₁.arrow s := by
  classical
  have key : ∀ k : ℕ, ∀ s ∈ C.comp, C₁.iterCount s ≤ k → C₂.arrow s = C₁.arrow s := by
    intro k
    induction k with
    | zero =>
      intro s hs hk
      have hsC1 : s ∈ C₁.comp := by rw [comp_eq_of_reachable C h1]; exact hs
      have h0 : C₁.iterCount s = 0 := Nat.le_zero.mp hk
      have hs1 : s = C₁.empty := iterCount_eq_zero C₁ hsC1 h0
      rw [hs1]
      have hf1 : C₁.f C₁.empty = C₁.empty := C₁.empty_fixed
      have hf2 : C₂.f C₁.empty = C₁.empty := he ▸ C₂.empty_fixed
      simp [arrow, hf1, hf2]
    | succ k ih =>
      intro s hs hk
      have hsC1 : s ∈ C₁.comp := by rw [comp_eq_of_reachable C h1]; exact hs
      have hsC2 : s ∈ C₂.comp := by rw [comp_eq_of_reachable C h2]; exact hs
      by_cases h0 : C₁.iterCount s = 0
      · have hs1 : s = C₁.empty := iterCount_eq_zero C₁ hsC1 h0
        rw [hs1]
        have hf1 : C₁.f C₁.empty = C₁.empty := C₁.empty_fixed
        have hf2 : C₂.f C₁.empty = C₁.empty := he ▸ C₂.empty_fixed
        simp [arrow, hf1, hf2]
      · have hne1 : s ≠ C₁.empty := fun h => h0 (h ▸ C₁.iterCount_empty)
        have hne2 : s ≠ C₂.empty := fun h => hne1 (by rw [h, he])
        -- t = arrow₁ s
        set t := C₁.arrow s with ht
        have htmem : t ∈ C.comp := by
          rw [← comp_eq_of_reachable C h1]
          have hga : C₁.gAdj s (C₁.arrow s) :=
            Or.inl ⟨(mem_comp C₁).mp hsC1 |>.1, hne1, rfl,
              arrow_mem_board_of_mem_comp C₁ hsC1 hne1⟩
          exact mem_comp_of_gAdj C₁ hga hsC1
        have htmemC1 : t ∈ C₁.comp := by rw [comp_eq_of_reachable C h1]; exact htmem
        have htcount : C₁.iterCount t = C₁.iterCount s - 1 := iterCount_arrow C₁ hsC1 hne1
        have hiht : C₂.arrow t = C₁.arrow t := ih t htmem (by omega)
        -- u = arrow₂ s
        set u := C₂.arrow s with hu
        -- show u = t
        by_contra hne
        -- edges
        have hg1 : C₁.gAdj s t :=
          Or.inl ⟨(mem_comp C₁).mp hsC1 |>.1, hne1, rfl,
            arrow_mem_board_of_mem_comp C₁ hsC1 hne1⟩
        have hg2 : C₂.gAdj s u :=
          Or.inl ⟨(mem_comp C₂).mp hsC2 |>.1, hne2, rfl,
            arrow_mem_board_of_mem_comp C₂ hsC2 hne2⟩
        have hg1' : C₁.gAdj s u := by
          have h := (gAdj_eq_of_reachable C h2 s u).mp hg2
          exact (gAdj_eq_of_reachable C h1 s u).mpr h
        have hg2' : C₂.gAdj s t := by
          have h := (gAdj_eq_of_reachable C h1 s t).mp hg1
          exact (gAdj_eq_of_reachable C h2 s t).mpr h
        -- from hg1': arrow₁ u = s (since arrow₁ s = t ≠ u)
        have harrow1 : C₁.arrow u = s := by
          rcases hg1' with ⟨-, -, harr, -⟩ | ⟨-, -, harr, -⟩
          · have hne' : u ≠ C₁.arrow s := by
              rw [← ht]; exact hne
            exact absurd harr hne'.symm
          · exact harr
        have hcount1 : C₁.iterCount u = C₁.iterCount s + 1 := by
          have humem : u ∈ C₂.comp := mem_comp_of_gAdj C₂ hg2 hsC2
          rw [comp_eq_of_reachable C h2] at humem
          rw [← comp_eq_of_reachable C h1] at humem
          have h1c : C₁.iterCount (C₁.arrow u) = C₁.iterCount u - 1 := by
            by_cases hz : u = C₁.empty
            · rw [hz, C₁.iterCount_empty]
              have h3 : C₁.arrow C₁.empty = C₁.empty :=
                arrow_eq_self_of_not_covered C₁ C₁.empty_fixed
              rw [h3, C₁.iterCount_empty]
            · exact iterCount_arrow C₁ humem hz
          rw [harrow1] at h1c
          omega
        -- from hg2': arrow₂ t = s (since arrow₂ s = u ≠ t)
        have harrow2 : C₂.arrow t = s := by
          rcases hg2' with ⟨-, -, harr, -⟩ | ⟨-, -, harr, -⟩
          · have hne' : C₂.arrow s ≠ t := by
              rw [← hu]; exact hne
            exact absurd harr hne' 
          · exact harr
        -- but by IH arrow₂ t = arrow₁ t, and arrow₁ t ≠ s
        have hne3 : C₁.arrow t ≠ s := by
          intro htz
          have h1c : C₁.iterCount (C₁.arrow t) = C₁.iterCount t - 1 := by
            by_cases hte : t = C₁.empty
            · rw [hte, C₁.iterCount_empty]
              have h3 : C₁.arrow C₁.empty = C₁.empty :=
                arrow_eq_self_of_not_covered C₁ C₁.empty_fixed
              rw [h3, C₁.iterCount_empty]
            · exact iterCount_arrow C₁ htmemC1 hte
          rw [htz] at h1c
          omega
        rw [hiht] at harrow2
        exact hne3 harrow2
  exact key (C₁.iterCount s) s hs le_rfl

end Config

/-!
## Frozen dominoes, the full equality, and the bijection `k(C) = |T|`
-/

namespace Config

variable {n : ℕ} (C : Config n)

/-- A unit step away from the uncovered cell is never special. -/
theorem add_unit_not_mem_special {e u : Cell} (hu : IsUnit u) (he : e = C.empty) :
    e + u ∉ C.special := by
  rw [mem_special]
  rintro ⟨-, h1, h2⟩
  rw [← he] at h1 h2
  rcases hu with rfl | rfl | rfl | rfl
  · have h3 : (e + ((1 : ℤ), (0 : ℤ))).1 % 2 = e.1 % 2 := h1
    simp at h3; omega
  · have h3 : (e + ((-1 : ℤ), (0 : ℤ))).1 % 2 = e.1 % 2 := h1
    simp at h3; omega
  · have h3 : (e + ((0 : ℤ), (1 : ℤ))).2 % 2 = e.2 % 2 := h2
    simp at h3; omega
  · have h3 : (e + ((0 : ℤ), (-1 : ℤ))).2 % 2 = e.2 % 2 := h2
    simp at h3; omega

/-- `e + 2u` is in the component (it is adjacent to the empty cell `e`). -/
theorem add_two_unit_mem_comp {e u : Cell} (hu : IsUnit u) (he : C.f e = e)
    (heb : e ∈ board n) (hu1 : e + u ∈ board n) (hu2 : e + 2 • u ∈ board n)
    (hdom : C.f (e + u) = e + 2 • u) : e + 2 • u ∈ C.comp := by
  have hce : e = C.empty := C.unique_fixed heb he
  have hfe2u : C.f (e + 2 • u) = e + u := by
    have := C.hf_inv (e + u) hu1
    rw [hdom] at this
    exact this
  have harr_e2u : C.arrow (e + 2 • u) = e := by
    simp only [arrow, hfe2u]
    ext <;> simp [Prod.smul_mk, smul_eq_mul] <;> omega
  have hpar1 : (e + 2 • u).1 % 2 = e.1 % 2 := by
    have h1 : (e + 2 • u).1 = e.1 + 2 * u.1 := by simp [Prod.smul_mk, smul_eq_mul]
    rw [h1]; omega
  have hpar2 : (e + 2 • u).2 % 2 = e.2 % 2 := by
    have h1 : (e + 2 • u).2 = e.2 + 2 * u.2 := by simp [Prod.smul_mk, smul_eq_mul]
    rw [h1]; omega
  have he2u_special : e + 2 • u ∈ C.special := by
    rw [mem_special]
    refine ⟨hu2, by rw [hpar1, hce], by rw [hpar2, hce]⟩
  have hne3 : e + 2 • u ≠ e := by
    have hu0 : u ≠ 0 := by
      rcases hu with rfl | rfl | rfl | rfl <;> simp
    intro h
    have h1 := congrArg (fun c => c - e) h
    have h2 : (e + 2 • u) - e = 2 • u := by ext <;> simp [Prod.smul_mk, smul_eq_mul] <;> omega
    rw [h2, sub_self] at h1
    have h3 : u = 0 := by
      have ha := congrArg Prod.fst h1
      have hb := congrArg Prod.snd h1
      simp at ha hb
      ext <;> omega
    exact hu0 h3
  have hedge : C.gAdj (e + 2 • u) e :=
    Or.inl ⟨he2u_special, fun h => hne3 (h.trans hce.symm), harr_e2u, heb⟩
  exact mem_comp_of_gAdj C hedge.symm (by
    rw [hce]
    exact C.empty_mem_comp)

/-- Frozen: special cells outside the component keep their partner. -/
theorem f_eq_of_reachable_outside_comp {C' : Config n} (h : C.Reachable C') {s : Cell}
    (hs : s ∈ C.special) (hout : s ∉ C.comp) : C'.f s = C.f s := by
  induction h with
  | refl => rfl
  | tail hprev hstep ih =>
    obtain ⟨e, u, hu, he, hce, heb, hu1, hu2, hdom, hupd⟩ := slide_facts hstep
    have hcomp_b := comp_eq_of_reachable C hprev
    have hspec_b := special_eq_of_reachable C hprev
    have he2 : e ∈ C.comp := by
      rw [hce, ← hcomp_b]
      exact empty_mem_comp _
    have hs1 : s ≠ e := by
      intro h
      rw [← h] at he2
      exact hout he2
    have hs2 : s ≠ e + u := by
      rw [← hspec_b] at hs
      have hns := add_unit_not_mem_special _ hu hce
      intro h
      rw [h] at hs
      exact hns hs
    have hs3 : s ≠ e + 2 • u := by
      have h1 : e + 2 • u ∈ C.comp := by
        rw [← hcomp_b]
        exact add_two_unit_mem_comp _ hu he heb hu1 hu2 hdom
      intro h
      rw [← h] at h1
      exact hout h1
    rw [hupd]
    simp only [slideFun, if_neg hs1, if_neg hs2, if_neg hs3]
    exact ih

/-- Frozen: a non-special cell whose partner is non-special is unchanged. -/
theorem f_eq_of_reachable_nonspecial {C' : Config n} (h : C.Reachable C') {c : Cell}
    (hc : c ∉ C.special) (hfc : C'.f c ∉ C.special) : C'.f c = C.f c := by
  induction h with
  | refl => rfl
  | tail hprev hstep ih =>
    obtain ⟨e, u, hu, he, hce, heb, hu1, hu2, hdom, hupd⟩ := slide_facts hstep
    have hspec_b := special_eq_of_reachable C hprev
    have hspec_C' := (slide_special _ _ hu he heb hu2 hupd).trans hspec_b
    have h1 : e ∈ C.special := by
      rw [hce, ← hspec_b]
      exact empty_mem_special _
    have hc1 : c ≠ e := by
      intro h
      rw [← h] at h1
      exact hc h1
    have hc2 : c ≠ e + u := by
      have hu0 : u ≠ 0 := by
        rcases hu with rfl | rfl | rfl | rfl <;> simp
      have hn : e + u ≠ e := by
        intro h3
        have h4 := congrArg (fun x => x - e) h3
        simp at h4
        exact hu0 h4
      intro h3
      rw [h3, hupd] at hfc
      simp only [slideFun, if_neg hn, if_pos rfl] at hfc
      exact hfc h1
    have hc3 : c ≠ e + 2 • u := by
      have h4 : e + 2 • u ∈ C.special := by
        have h5 : e + 2 • u ∈ C.comp := by
          rw [← comp_eq_of_reachable C hprev]
          exact add_two_unit_mem_comp _ hu he heb hu1 hu2 hdom
        exact (mem_comp C).mp h5 |>.1
      intro h5
      rw [← h5] at h4
      exact hc h4
    rw [hupd]
    simp only [slideFun, if_neg hc1, if_neg hc2, if_neg hc3]
    apply ih
    rw [hupd] at hfc
    simp only [slideFun, if_neg hc1, if_neg hc2, if_neg hc3] at hfc
    exact hfc

/-- On special cells, the partner is the same in all reachable configurations
with the same uncovered cell. -/
theorem f_eq_of_same_empty_on_special {C₁ C₂ : Config n} (h1 : C.Reachable C₁)
    (h2 : C.Reachable C₂) (he : C₁.empty = C₂.empty) {s : Cell} (hs : s ∈ C.special) :
    C₁.f s = C₂.f s := by
  by_cases hcomp : s ∈ C.comp
  · by_cases he1 : s = C₁.empty
    · rw [he1, C₁.empty_fixed, he, C₂.empty_fixed]
    · have harr := arrow_eq_of_same_empty C h1 h2 he hcomp
      have h1a : C₁.arrow s = s + 2 • (C₁.f s - s) := rfl
      have h2a : C₂.arrow s = s + 2 • (C₂.f s - s) := rfl
      rw [← harr, h2a, add_left_cancel_iff] at h1a
      have e1 : (C₁.f s).1 - s.1 = (C₂.f s).1 - s.1 := by
        have h4 := congrArg Prod.fst h1a
        simp at h4
        omega
      have e2 : (C₁.f s).2 - s.2 = (C₂.f s).2 - s.2 := by
        have h5 := congrArg Prod.snd h1a
        simp at h5
        omega
      ext <;> omega
  · rw [f_eq_of_reachable_outside_comp C h1 hs hcomp,
      f_eq_of_reachable_outside_comp C h2 hs hcomp]

/-- Two reachable configurations with the same uncovered cell are equal. -/
theorem f_eq_of_same_empty {C₁ C₂ : Config n} (h1 : C.Reachable C₁) (h2 : C.Reachable C₂)
    (he : C₁.empty = C₂.empty) (c : Cell) (hc : c ∈ board n) : C₁.f c = C₂.f c := by
  classical
  have key : ∀ s : Cell, s ∈ C.special → C₁.f s = C₂.f s :=
    fun s hs => f_eq_of_same_empty_on_special C h1 h2 he hs
  have hinj : ∀ x y : Cell, x ∈ board n → y ∈ board n → C₂.f x = C₂.f y → x = y := by
    intro x y hx hy hxy
    have h1' := C₂.hf_inv x hx
    have h2' := C₂.hf_inv y hy
    rw [hxy] at h1'
    rw [h1'] at h2'
    exact h2'
  have hinj1 : ∀ x y : Cell, x ∈ board n → y ∈ board n → C₁.f x = C₁.f y → x = y := by
    intro x y hx hy hxy
    have h1' := C₁.hf_inv x hx
    have h2' := C₁.hf_inv y hy
    rw [hxy] at h1'
    rw [h1'] at h2'
    exact h2'
  by_cases hspec : c ∈ C.special
  · exact key c hspec
  · by_cases hf1 : C₁.f c ∈ C.special
    · have heq : C₂.f (C₁.f c) = c := by
        have h := key (C₁.f c) hf1
        rw [C₁.hf_inv c hc] at h
        exact h.symm
      exact hinj (C₁.f c) (C₂.f c) (C₁.hf_map c hc) (C₂.hf_map c hc)
        (by rw [heq, C₂.hf_inv c hc])
    · have hf2 : C₂.f c ∉ C.special := by
        intro hf2
        have heq : C₁.f (C₂.f c) = c := by
          have h := f_eq_of_same_empty_on_special C h2 h1 he.symm hf2
          rw [C₂.hf_inv c hc] at h
          exact h.symm
        have heq2 : C₂.f c = C₁.f c :=
          hinj1 (C₂.f c) (C₁.f c) (C₂.hf_map c hc) (C₁.hf_map c hc)
            (by rw [heq, C₁.hf_inv c hc])
        exact hf1 (heq2 ▸ hf2)
      rw [f_eq_of_reachable_nonspecial C h1 hspec hf1,
        f_eq_of_reachable_nonspecial C h2 hspec hf2]

end Config

/-!
## Surjectivity and the bijection: `k(C)` equals the component size
-/

namespace Config

variable {n : ℕ} (C : Config n)

/-- Paths transfer across configurations with the same arrow graph. -/
theorem gConnN_of_gAdj_eq {C₁ C₂ : Config n} (h : ∀ x y, C₁.gAdj x y ↔ C₂.gAdj x y)
    {k : ℕ} {s t : Cell} (hk : C₂.gConnN k s t) : C₁.gConnN k s t := by
  induction k generalizing s with
  | zero => rwa [gConnN_zero] at hk ⊢
  | succ k ih =>
    rw [gConnN_succ] at hk ⊢
    obtain ⟨m, h1, h2⟩ := hk
    exact ⟨m, (h _ _).mpr h1, ih h2⟩

/-- One slide step: move the uncovered cell to a graph-neighbor. -/
theorem exists_slide_neighbor (D : Config n) {m : Cell} (hm : m ∈ D.comp)
    (hab : D.gAdj D.empty m) : ∃ D' : Config n, D.Slide D' ∧ D'.empty = m := by
  classical
  have hss : m ∈ D.special := gAdj_right_special D hab
  have hsm : m ≠ D.empty := by
    intro h
    rw [h] at hab
    rcases hab with ⟨-, hs1ne, -, -⟩ | ⟨-, hs2ne, -, -⟩
    · exact absurd rfl hs1ne
    · exact absurd rfl hs2ne
  have harrow : D.arrow m = D.empty := by
    rcases hab with ⟨-, hs1ne, -, -⟩ | ⟨-, -, harr, -⟩
    · exact absurd rfl hs1ne
    · exact harr
  have hsb : m ∈ board n := mem_board_of_mem_special D hss
  have hfne : D.f m ≠ m := by
    intro h
    have h4 : D.arrow m = m := by
      have h5 : D.arrow m = m + 2 • (D.f m - m) := rfl
      rw [h5, h]
      ext <;> simp
    rw [h4] at harrow
    exact hsm harrow
  have hw : IsUnit (D.f m - m) := arrow_step_unit D hsb hfne
  have h2w : 2 • (D.f m - m) = D.empty - m := by
    have h5 := congrArg Prod.fst harrow
    have h6 := congrArg Prod.snd harrow
    simp [arrow, Prod.smul_mk, Int.zsmul_eq_mul] at h5 h6
    ext <;> simp <;> omega
  have hmw : D.empty + -(D.f m - m) = D.f m := by
    have h5 := congrArg Prod.fst h2w
    have h6 := congrArg Prod.snd h2w
    simp [Prod.smul_mk, Int.zsmul_eq_mul] at h5 h6
    ext <;> simp <;> omega
  have hm2w : D.empty + 2 • -(D.f m - m) = m := by
    have h5 := congrArg Prod.fst h2w
    have h6 := congrArg Prod.snd h2w
    simp [Prod.smul_mk, Int.zsmul_eq_mul] at h5 h6
    ext <;> simp <;> omega
  have he : D.f D.empty = D.empty := D.empty_fixed
  have hmb : D.empty ∈ board n := D.empty_mem
  have hdom : D.f (D.empty + -(D.f m - m)) = D.empty + 2 • -(D.f m - m) := by
    rw [hmw, D.hf_inv m hsb, hm2w]
  have hu1 : D.empty + -(D.f m - m) ∈ board n := by
    rw [hmw]
    exact D.hf_map m hsb
  have hu2 : D.empty + 2 • -(D.f m - m) ∈ board n := by
    rw [hm2w]
    exact hsb
  obtain ⟨D', hf''⟩ := slideFun_valid D (IsUnit.neg hw) he hmb hu1 hu2 hdom
  have hstep : D.Slide D' :=
    ⟨D.empty, -(D.f m - m), IsUnit.neg hw, he, hu1, hu2, hdom,
      fun c => by simp only [hf'', slideFun]⟩
  refine ⟨D', hstep, ?_⟩
  have he2 : D'.empty = D.empty + 2 • -(D.f m - m) :=
    slide_empty D D' (IsUnit.neg hw) he hmb hu2 hf''
  rw [he2, hm2w]

/-- The uncovered cell can be slid along a path in the arrow graph. -/
theorem exists_reachable_empty_of_gConnN (D : Config n) {s : Cell} (hs : s ∈ D.comp)
    {k : ℕ} (hk : D.gConnN k D.empty s) :
    ∃ D' : Config n, D.Reachable D' ∧ D'.empty = s := by
  classical
  induction k generalizing D s hs with
  | zero =>
    rw [gConnN_zero] at hk
    exact ⟨D, Relation.ReflTransGen.refl, hk⟩
  | succ k ih =>
    rw [gConnN_succ] at hk
    obtain ⟨m, h1, h2⟩ := hk
    have hm2 : m ∈ D.comp := by
      rw [mem_comp]
      exact ⟨gAdj_right_special D h1,
        gConnN_sound D (gConnN_symm D ((gConnN_one D).mpr h1))⟩
    obtain ⟨D₁, hstep, hempty⟩ := exists_slide_neighbor D hm2 h1
    have hreach : D.Reachable D₁ := Relation.ReflTransGen.tail Relation.ReflTransGen.refl hstep
    have hk2 : D₁.gConnN k m s := by
      have h3 : ∀ x y, D₁.gAdj x y ↔ D.gAdj x y := gAdj_eq_of_reachable D hreach
      exact gConnN_of_gAdj_eq h3 h2
    have hsD : s ∈ D₁.comp := by
      rw [comp_eq_of_reachable D hreach]
      exact hs
    rw [← hempty] at hk2
    obtain ⟨D₂, hr2, hempty2⟩ := ih D₁ hsD hk2
    exact ⟨D₂, hreach.trans hr2, hempty2⟩

/-- The uncovered cell can be slid to any vertex of the component. -/
theorem exists_reachable_empty {s : Cell} (hs : s ∈ C.comp) :
    ∃ C' : Config n, C.Reachable C' ∧ C'.empty = s := by
  classical
  have h2 : C.gConn s C.empty := (mem_comp C).mp hs |>.2
  obtain ⟨k, hk0⟩ := (gConn_iff_exists C).mp h2
  exact exists_reachable_empty_of_gConnN C hs (gConnN_symm C hk0)

/-- The bijection between reachable configurations and component vertices
(given by the position of the uncovered cell). -/
noncomputable def reachableEquivComp : { C' : Config n // C.Reachable C' } ≃ ↥C.comp where
  toFun := fun C' => ⟨C'.1.empty, (comp_eq_of_reachable C C'.2) ▸ C'.1.empty_mem_comp⟩
  invFun := fun s => ⟨(exists_reachable_empty C s.2).choose,
    (exists_reachable_empty C s.2).choose_spec.1⟩
  left_inv := fun C' => by
    apply Subtype.ext
    apply Config.ext
    intro c hc
    have hspec := (exists_reachable_empty C
      ((comp_eq_of_reachable C C'.2) ▸ C'.1.empty_mem_comp)).choose_spec
    have h := f_eq_of_same_empty C C'.2 hspec.1 hspec.2.symm c hc
    exact h.symm
  right_inv := fun s => by
    apply Subtype.ext
    exact (exists_reachable_empty C s.2).choose_spec.2

/-- `k(C)` equals the size of the component of the uncovered square. -/
theorem kval_eq_comp_card : C.kval = C.comp.card := by
  classical
  unfold Config.kval
  rw [Nat.card_eq_fintype_card, Fintype.card_congr (reachableEquivComp C)]
  simp

end Config

/-!
## Counting: checkerboard argument and special-cell counts
-/

namespace Config

variable {n : ℕ} (C : Config n)

/-- Number of even integers in `Icc 0 (2m)`. -/
theorem card_Icc_emod_two_zero (m : ℕ) :
    ((Finset.Icc (0 : ℤ) (2 * m)).filter (fun x => x % 2 = 0)).card = m + 1 := by
  have h : (Finset.Icc (0 : ℤ) (2 * m)).filter (fun x => x % 2 = 0) =
      (Finset.Icc (0 : ℤ) m).map ⟨(fun x => 2 * x), fun a b h => by have h2 : 2 * a = 2 * b := h; omega⟩ := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_map]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      have h4 : 2 * (x / 2) = x := by omega
      exact ⟨x / 2, by omega, h4⟩
    · rintro ⟨a, ⟨h1, h2⟩, rfl⟩
      have h3 : (2 * a) % 2 = 0 := by omega
      have h4 : 0 ≤ 2 * a ∧ 2 * a ≤ 2 * ↑m := by omega
      exact ⟨h4, h3⟩
  rw [h, Finset.card_map]
  have : (Finset.Icc (0 : ℤ) (m : ℤ)).card = m + 1 := by
    rw [Int.card_Icc]
    simp
  exact this

/-- Number of odd integers in `Icc 0 (2m)`. -/
theorem card_Icc_emod_two_one (m : ℕ) :
    ((Finset.Icc (0 : ℤ) (2 * m)).filter (fun x => x % 2 = 1)).card = m := by
  have h : (Finset.Icc (0 : ℤ) (2 * m)).filter (fun x => x % 2 = 1) =
      (Finset.Icc (0 : ℤ) ((m : ℤ) - 1)).map ⟨(fun x => 2 * x + 1), fun a b h => by have h2 : 2 * a + 1 = 2 * b + 1 := h; omega⟩ := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_map]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      have h4 : 2 * ((x - 1) / 2) + 1 = x := by omega
      exact ⟨(x - 1) / 2, by omega, h4⟩
    · rintro ⟨a, ⟨h1, h2⟩, rfl⟩
      have h3 : (2 * a + 1) % 2 = 1 := by omega
      have h4 : 0 ≤ 2 * a + 1 ∧ 2 * a + 1 ≤ 2 * ↑m := by omega
      exact ⟨h4, h3⟩
  rw [h, Finset.card_map]
  have : (Finset.Icc (0 : ℤ) ((m : ℤ) - 1)).card = m := by
    rw [Int.card_Icc]
    simp
  exact this

/-- The board as a product of intervals. -/
theorem board_eq_prod (n : ℕ) :
    board n = (Finset.Icc (0 : ℤ) ((n : ℤ) - 1)) ×ˢ (Finset.Icc (0 : ℤ) ((n : ℤ) - 1)) := by
  ext ⟨x, y⟩
  simp only [board, Finset.mem_Icc, Finset.mem_product, Prod.le_def]
  constructor
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    exact ⟨⟨h1, h3⟩, ⟨h2, h4⟩⟩
  · rintro ⟨⟨h1, h3⟩, ⟨h2, h4⟩⟩
    exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩

/-- The special cells as a product of same-parity intervals. -/
theorem special_eq_prod :
    C.special =
      ((Finset.Icc (0 : ℤ) ((n : ℤ) - 1)).filter (fun x => x % 2 = C.empty.1 % 2)) ×ˢ
      ((Finset.Icc (0 : ℤ) ((n : ℤ) - 1)).filter (fun y => y % 2 = C.empty.2 % 2)) := by
  ext ⟨x, y⟩
  rw [mem_special, board_eq_prod]
  simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_Icc]
  tauto

/-- The parity of a cell (checkerboard color). -/
def color (c : Cell) : ℤ := (c.1 + c.2) % 2

theorem color_eq_zero_or_one (c : Cell) : color c = 0 ∨ color c = 1 := by
  unfold color
  omega

/-- Adjacent cells have different colors. -/
theorem color_adj_ne {c d : Cell} (h : IsAdj c d) : color c ≠ color d := by
  unfold color
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1]
    rcases eq_or_eq_neg_of_abs_eq h2 with h3 | h3
    · have h4 : c.2 = d.2 + 1 := by omega
      rw [h4]; omega
    · have h4 : c.2 = d.2 - 1 := by omega
      rw [h4]; omega
  · rcases eq_or_eq_neg_of_abs_eq h1 with h3 | h3
    · have h4 : c.1 = d.1 + 1 := by omega
      rw [h2, h4]; omega
    · have h4 : c.1 = d.1 - 1 := by omega
      rw [h2, h4]; omega

/-- Board cells of a given checkerboard color. -/
noncomputable def boardColor (n : ℕ) (k : ℤ) : Finset Cell :=
  (board n).filter (fun c => color c = k)

/-- The domino pairing is a bijection between covered color-0 and color-1 cells. -/
theorem card_color_covered_eq :
    ((boardColor n 0).erase C.empty).card = ((boardColor n 1).erase C.empty).card := by
  classical
  apply Finset.card_bij (fun c _ => C.f c)
  · intro c hc
    simp only [boardColor, Finset.mem_erase, Finset.mem_filter] at hc ⊢
    obtain ⟨hcne, hc1, hc2⟩ := hc
    have hf : C.f c ≠ c := by
      intro h
      exact hcne (C.unique_fixed hc1 h)
    have hfc : C.f (C.f c) = c := C.hf_inv c hc1
    have hfcne : C.f c ≠ C.empty := by
      intro h
      have hfc : C.f (C.f c) = c := C.hf_inv c hc1
      rw [h, C.empty_fixed] at hfc
      exact hcne hfc.symm
    have hcol : color (C.f c) ≠ color c := (color_adj_ne (C.hf_adj c hc1 hf)).symm
    refine ⟨hfcne, C.hf_map c hc1, ?_⟩
    rcases color_eq_zero_or_one (C.f c) with h | h
    · exact absurd h (by rw [hc2] at hcol; exact hcol)
    · exact h
  · intro c₁ hc1 c₂ hc2 h
    have h1 : c₁ ∈ board n := (Finset.mem_filter.mp (Finset.mem_erase.mp hc1).2).1
    have h2 : c₂ ∈ board n := (Finset.mem_filter.mp (Finset.mem_erase.mp hc2).2).1
    have hfc1 := C.hf_inv c₁ h1
    have hfc2 := C.hf_inv c₂ h2
    have h' : C.f c₁ = C.f c₂ := h
    rw [h'] at hfc1
    rw [hfc2] at hfc1
    exact hfc1.symm
  · intro c hc
    simp only [boardColor, Finset.mem_erase, Finset.mem_filter] at hc ⊢
    obtain ⟨hcne, hc1, hc2⟩ := hc
    refine ⟨C.f c, ?_, C.hf_inv c hc1⟩
    have hf : C.f c ≠ c := by
      intro h
      exact hcne (C.unique_fixed hc1 h)
    have hfcne : C.f c ≠ C.empty := by
      intro h
      have hfc : C.f (C.f c) = c := C.hf_inv c hc1
      rw [h] at hfc
      rw [C.empty_fixed] at hfc
      exact hcne hfc.symm
    have hcol : color (C.f c) ≠ color c := (color_adj_ne (C.hf_adj c hc1 hf)).symm
    refine ⟨hfcne, C.hf_map c hc1, ?_⟩
    rcases color_eq_zero_or_one (C.f c) with h | h
    · exact h
    · exact absurd h (by rw [hc2] at hcol; exact hcol)

/-- Color counts on the odd board: color 0 has one more cell than color 1. -/
theorem card_boardColor (hn : Odd n) :
    (boardColor n 0).card = (boardColor n 1).card + 1 := by
  classical
  obtain ⟨m, hm⟩ := hn
  subst hm
  have hb : board (2 * m + 1) =
      (Finset.Icc (0 : ℤ) (2 * (m : ℤ))) ×ˢ (Finset.Icc (0 : ℤ) (2 * (m : ℤ))) := by
    rw [board_eq_prod]
    congr 1 <;> norm_num
  have h0 : boardColor (2 * m + 1) 0 =
      ((Finset.Icc (0 : ℤ) (2 * (m : ℤ))).filter (fun x => x % 2 = 0) ×ˢ
        (Finset.Icc (0 : ℤ) (2 * (m : ℤ))).filter (fun y => y % 2 = 0)) ∪
      ((Finset.Icc (0 : ℤ) (2 * (m : ℤ))).filter (fun x => x % 2 = 1) ×ˢ
        (Finset.Icc (0 : ℤ) (2 * (m : ℤ))).filter (fun y => y % 2 = 1)) := by
    ext ⟨x, y⟩
    simp only [boardColor, hb, Finset.mem_filter, Finset.mem_product, Finset.mem_union,
      Finset.mem_Icc]
    unfold color
    constructor
    · rintro ⟨⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩, hk⟩
      have hx := hx1
      have hy := hy1
      have h : (x + y) % 2 = 0 := hk
      have hxp : x % 2 = 0 ∨ x % 2 = 1 := by omega
      have hyp : y % 2 = 0 ∨ y % 2 = 1 := by omega
      rcases hxp with hxp | hxp <;> rcases hyp with hyp | hyp
      · exact Or.inl ⟨⟨⟨hx, hx2⟩, hxp⟩, ⟨⟨hy, hy2⟩, hyp⟩⟩
      · exfalso; omega
      · exfalso; omega
      · exact Or.inr ⟨⟨⟨hx, hx2⟩, hxp⟩, ⟨⟨hy, hy2⟩, hyp⟩⟩
    · rintro (⟨⟨⟨hx, hx2⟩, hxp⟩, ⟨⟨hy, hy2⟩, hyp⟩⟩ | ⟨⟨⟨hx, hx2⟩, hxp⟩, ⟨⟨hy, hy2⟩, hyp⟩⟩)
      · refine ⟨⟨⟨hx, hx2⟩, ⟨hy, hy2⟩⟩, ?_⟩
        show (x + y) % 2 = 0
        omega
      · refine ⟨⟨⟨hx, hx2⟩, ⟨hy, hy2⟩⟩, ?_⟩
        show (x + y) % 2 = 0
        omega
  have h1 : boardColor (2 * m + 1) 1 =
      ((Finset.Icc (0 : ℤ) (2 * (m : ℤ))).filter (fun x => x % 2 = 0) ×ˢ
        (Finset.Icc (0 : ℤ) (2 * (m : ℤ))).filter (fun y => y % 2 = 1)) ∪
      ((Finset.Icc (0 : ℤ) (2 * (m : ℤ))).filter (fun x => x % 2 = 1) ×ˢ
        (Finset.Icc (0 : ℤ) (2 * (m : ℤ))).filter (fun y => y % 2 = 0)) := by
    ext ⟨x, y⟩
    simp only [boardColor, hb, Finset.mem_filter, Finset.mem_product, Finset.mem_union,
      Finset.mem_Icc]
    unfold color
    constructor
    · rintro ⟨⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩, hk⟩
      have hx := hx1
      have hy := hy1
      have h : (x + y) % 2 = 1 := hk
      have hxp : x % 2 = 0 ∨ x % 2 = 1 := by omega
      have hyp : y % 2 = 0 ∨ y % 2 = 1 := by omega
      rcases hxp with hxp | hxp <;> rcases hyp with hyp | hyp
      · exfalso; omega
      · exact Or.inl ⟨⟨⟨hx, hx2⟩, hxp⟩, ⟨⟨hy, hy2⟩, hyp⟩⟩
      · exact Or.inr ⟨⟨⟨hx, hx2⟩, hxp⟩, ⟨⟨hy, hy2⟩, hyp⟩⟩
      · exfalso; omega
    · rintro (⟨⟨⟨hx, hx2⟩, hxp⟩, ⟨⟨hy, hy2⟩, hyp⟩⟩ | ⟨⟨⟨hx, hx2⟩, hxp⟩, ⟨⟨hy, hy2⟩, hyp⟩⟩)
      · refine ⟨⟨⟨hx, hx2⟩, ⟨hy, hy2⟩⟩, ?_⟩
        show (x + y) % 2 = 1
        omega
      · refine ⟨⟨⟨hx, hx2⟩, ⟨hy, hy2⟩⟩, ?_⟩
        show (x + y) % 2 = 1
        omega
  rw [h0, h1]
  have hdj0 : Disjoint
      ((Finset.Icc (0 : ℤ) (2 * (m : ℤ))).filter (fun x => x % 2 = 0) ×ˢ
        (Finset.Icc (0 : ℤ) (2 * (m : ℤ))).filter (fun y => y % 2 = 0))
      ((Finset.Icc (0 : ℤ) (2 * (m : ℤ))).filter (fun x => x % 2 = 1) ×ˢ
        (Finset.Icc (0 : ℤ) (2 * (m : ℤ))).filter (fun y => y % 2 = 1)) := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    ext ⟨x, y⟩
    simp only [Finset.mem_inter, Finset.mem_product, Finset.mem_filter, Finset.notMem_empty,
      iff_false, not_and, Finset.mem_Icc]
    omega
  have hdj1 : Disjoint
      ((Finset.Icc (0 : ℤ) (2 * (m : ℤ))).filter (fun x => x % 2 = 0) ×ˢ
        (Finset.Icc (0 : ℤ) (2 * (m : ℤ))).filter (fun y => y % 2 = 1))
      ((Finset.Icc (0 : ℤ) (2 * (m : ℤ))).filter (fun x => x % 2 = 1) ×ˢ
        (Finset.Icc (0 : ℤ) (2 * (m : ℤ))).filter (fun y => y % 2 = 0)) := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    ext ⟨x, y⟩
    simp only [Finset.mem_inter, Finset.mem_product, Finset.mem_filter, Finset.notMem_empty,
      iff_false, not_and, Finset.mem_Icc]
    omega
  have hcz := card_Icc_emod_two_zero m
  have hco := card_Icc_emod_two_one m
  rw [Finset.card_union_of_disjoint hdj0, Finset.card_union_of_disjoint hdj1,
    Finset.card_product, Finset.card_product, Finset.card_product, Finset.card_product,
    hcz, hco]
  ring

/-- The uncovered cell lies on the majority color. -/
theorem empty_color_zero (hn : Odd n) : color C.empty = 0 := by
  classical
  have h1 := card_boardColor hn
  have h2 := card_color_covered_eq C
  rcases color_eq_zero_or_one C.empty with h | h
  · exact h
  · exfalso
    have hmem1 : C.empty ∈ boardColor n 1 := by
      rw [boardColor, Finset.mem_filter]
      exact ⟨C.empty_mem, h⟩
    have hnot0 : C.empty ∉ boardColor n 0 := by
      rw [boardColor, Finset.mem_filter]
      push_neg
      intro _
      rw [h]
      omega
    have hcard0 : (boardColor n 0).card = ((boardColor n 0).erase C.empty).card := by
      rw [Finset.erase_eq_of_notMem hnot0]
    have hcard1 : (boardColor n 1).card = ((boardColor n 1).erase C.empty).card + 1 := by
      rw [← Finset.card_erase_add_one hmem1]
    omega

end Config

/-!
## Special-cell and interior-cell counts
-/

namespace Config

variable {n : ℕ} (C : Config n)

/-- The two coordinates of the uncovered cell have the same parity. -/
theorem empty_parity_same (hn : Odd n) : C.empty.1 % 2 = C.empty.2 % 2 := by
  have h := empty_color_zero C hn
  unfold color at h
  omega

/-- The component of the uncovered square has either `((n+1)/2)²` or `((n-1)/2)²`
special cells. -/
theorem card_special_cases (hn : Odd n) :
    C.special.card = ((n + 1) / 2) ^ 2 ∨ C.special.card = ((n - 1) / 2) ^ 2 := by
  obtain ⟨m, hm⟩ := hn
  subst hm
  have hp := empty_parity_same C ⟨m, rfl⟩
  have hs : C.special =
      ((Finset.Icc (0 : ℤ) (2 * (m : ℤ))).filter (fun x => x % 2 = C.empty.1 % 2)) ×ˢ
      ((Finset.Icc (0 : ℤ) (2 * (m : ℤ))).filter (fun y => y % 2 = C.empty.2 % 2)) := by
    rw [special_eq_prod]
    congr 1 <;> congr 1 <;> norm_num
  rw [hs, Finset.card_product]
  have hp1 : C.empty.1 % 2 = 0 ∨ C.empty.1 % 2 = 1 := by omega
  rcases hp1 with hp1 | hp1
  · have hp2 : C.empty.2 % 2 = 0 := by rw [← hp]; exact hp1
    left
    have hf1 : (Finset.Icc (0 : ℤ) (2 * (m : ℤ))).filter (fun x => x % 2 = C.empty.1 % 2) =
        (Finset.Icc (0 : ℤ) (2 * (m : ℤ))).filter (fun x => x % 2 = 0) := by
      apply Finset.filter_congr
      intro x hx
      rw [hp1]
    have hf2 : (Finset.Icc (0 : ℤ) (2 * (m : ℤ))).filter (fun y => y % 2 = C.empty.2 % 2) =
        (Finset.Icc (0 : ℤ) (2 * (m : ℤ))).filter (fun y => y % 2 = 0) := by
      apply Finset.filter_congr
      intro y hy
      rw [hp2]
    rw [hf1, hf2, card_Icc_emod_two_zero]
    have h2 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
    rw [h2, sq]
  · have hp2 : C.empty.2 % 2 = 1 := by rw [← hp]; exact hp1
    right
    have hf1 : (Finset.Icc (0 : ℤ) (2 * (m : ℤ))).filter (fun x => x % 2 = C.empty.1 % 2) =
        (Finset.Icc (0 : ℤ) (2 * (m : ℤ))).filter (fun x => x % 2 = 1) := by
      apply Finset.filter_congr
      intro x hx
      rw [hp1]
    have hf2 : (Finset.Icc (0 : ℤ) (2 * (m : ℤ))).filter (fun y => y % 2 = C.empty.2 % 2) =
        (Finset.Icc (0 : ℤ) (2 * (m : ℤ))).filter (fun y => y % 2 = 1) := by
      apply Finset.filter_congr
      intro y hy
      rw [hp2]
    rw [hf1, hf2, card_Icc_emod_two_one]
    have h2 : (2 * m + 1 - 1) / 2 = m := by omega
    rw [h2, sq]

/-- Pinned count of special cells when the empty cell has even coordinates. -/
theorem card_special_big (hn : Odd n) (hp : C.empty.1 % 2 = 0) :
    C.special.card = ((n + 1) / 2) ^ 2 := by
  obtain ⟨m, hm⟩ := hn
  subst hm
  have hsame := empty_parity_same C ⟨m, rfl⟩
  have hp2 : C.empty.2 % 2 = 0 := by rw [← hsame]; exact hp
  have hs : C.special =
      ((Finset.Icc (0 : ℤ) (2 * (m : ℤ))).filter (fun x => x % 2 = C.empty.1 % 2)) ×ˢ
      ((Finset.Icc (0 : ℤ) (2 * (m : ℤ))).filter (fun y => y % 2 = C.empty.2 % 2)) := by
    rw [special_eq_prod]
    congr 1 <;> congr 1 <;> norm_num
  rw [hs, Finset.card_product]
  have hf1 : (Finset.Icc (0 : ℤ) (2 * (m : ℤ))).filter (fun x => x % 2 = C.empty.1 % 2) =
      (Finset.Icc (0 : ℤ) (2 * (m : ℤ))).filter (fun x => x % 2 = 0) := by
    apply Finset.filter_congr
    intro x hx
    rw [hp]
  have hf2 : (Finset.Icc (0 : ℤ) (2 * (m : ℤ))).filter (fun y => y % 2 = C.empty.2 % 2) =
      (Finset.Icc (0 : ℤ) (2 * (m : ℤ))).filter (fun y => y % 2 = 0) := by
    apply Finset.filter_congr
    intro y hy
    rw [hp2]
  rw [hf1, hf2, card_Icc_emod_two_zero]
  have h2 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
  rw [h2, sq]

/-- Pinned count of special cells when the empty cell has odd coordinates. -/
theorem card_special_small (hn : Odd n) (hp : C.empty.1 % 2 = 1) :
    C.special.card = ((n - 1) / 2) ^ 2 := by
  obtain ⟨m, hm⟩ := hn
  subst hm
  have hsame := empty_parity_same C ⟨m, rfl⟩
  have hp2 : C.empty.2 % 2 = 1 := by rw [← hsame]; exact hp
  have hs : C.special =
      ((Finset.Icc (0 : ℤ) (2 * (m : ℤ))).filter (fun x => x % 2 = C.empty.1 % 2)) ×ˢ
      ((Finset.Icc (0 : ℤ) (2 * (m : ℤ))).filter (fun y => y % 2 = C.empty.2 % 2)) := by
    rw [special_eq_prod]
    congr 1 <;> congr 1 <;> norm_num
  rw [hs, Finset.card_product]
  have hf1 : (Finset.Icc (0 : ℤ) (2 * (m : ℤ))).filter (fun x => x % 2 = C.empty.1 % 2) =
      (Finset.Icc (0 : ℤ) (2 * (m : ℤ))).filter (fun x => x % 2 = 1) := by
    apply Finset.filter_congr
    intro x hx
    rw [hp]
  have hf2 : (Finset.Icc (0 : ℤ) (2 * (m : ℤ))).filter (fun y => y % 2 = C.empty.2 % 2) =
      (Finset.Icc (0 : ℤ) (2 * (m : ℤ))).filter (fun y => y % 2 = 1) := by
    apply Finset.filter_congr
    intro y hy
    rw [hp2]
  rw [hf1, hf2, card_Icc_emod_two_one]
  have h2 : (2 * m + 1 - 1) / 2 = m := by omega
  rw [h2, sq]

/-- Number of even integers in `Icc 1 (2m - 1)`. -/
theorem card_Icc_one_emod_two_zero (m : ℕ) :
    ((Finset.Icc (1 : ℤ) (2 * (m : ℤ) - 1)).filter (fun x => x % 2 = 0)).card = m - 1 := by
  have h : (Finset.Icc (1 : ℤ) (2 * (m : ℤ) - 1)).filter (fun x => x % 2 = 0) =
      (Finset.Icc (1 : ℤ) ((m : ℤ) - 1)).map ⟨(fun x => 2 * x), fun a b h => by
        have h2 : 2 * a = 2 * b := h; omega⟩ := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_map]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      have h4 : 2 * (x / 2) = x := by omega
      exact ⟨x / 2, by omega, h4⟩
    · rintro ⟨a, ⟨h1, h2⟩, rfl⟩
      have h3 : (2 * a) % 2 = 0 := by omega
      have h4 : 1 ≤ 2 * a ∧ 2 * a ≤ 2 * ↑m - 1 := by omega
      exact ⟨h4, h3⟩
  rw [h, Finset.card_map]
  have : (Finset.Icc (1 : ℤ) ((m : ℤ) - 1)).card = m - 1 := by
    rw [Int.card_Icc]
    simp
  exact this

/-- Special cells not on the boundary of the board. -/
noncomputable def interior : Finset Cell :=
  C.special.filter (fun c => 0 < c.1 ∧ c.1 < (n : ℤ) - 1 ∧ 0 < c.2 ∧ c.2 < (n : ℤ) - 1)

theorem mem_interior {c : Cell} :
    c ∈ C.interior ↔
      c ∈ C.special ∧ 0 < c.1 ∧ c.1 < (n : ℤ) - 1 ∧ 0 < c.2 ∧ c.2 < (n : ℤ) - 1 := by
  simp [interior]

/-- In the big-parity case, the interior special cells number `((n-3)/2)²`. -/
theorem card_interior_big (hn : Odd n) (hbig : C.empty.1 % 2 = 0) :
    C.interior.card = ((n - 3) / 2) ^ 2 := by
  obtain ⟨m, hm⟩ := hn
  subst hm
  have hp2 : C.empty.2 % 2 = 0 := by rw [← empty_parity_same C ⟨m, rfl⟩]; exact hbig
  have h : C.interior =
      ((Finset.Icc (1 : ℤ) (2 * (m : ℤ) - 1)).filter (fun x => x % 2 = 0)) ×ˢ
      ((Finset.Icc (1 : ℤ) (2 * (m : ℤ) - 1)).filter (fun y => y % 2 = 0)) := by
    ext ⟨x, y⟩
    simp only [interior, Finset.mem_filter, mem_special, board_eq_prod, Finset.mem_product,
      Finset.mem_Icc]
    rw [hbig, hp2]
    constructor <;> intro h <;> omega
  rw [h, Finset.card_product, card_Icc_one_emod_two_zero]
  have h2 : (2 * m + 1 - 3) / 2 = m - 1 := by omega
  rw [h2, sq]

end Config

/-!
## Cycle extraction
-/

namespace Config

variable {n : ℕ} (C : Config n)

/-- In the big-parity case (uncovered cell at an even-even position), every covered
special cell has an on-board arrow. -/
theorem arrow_mem_board_big (hn : Odd n) (hbig : C.empty.1 % 2 = 0) {s : Cell}
    (hs : s ∈ C.special) (hne : s ≠ C.empty) : C.arrow s ∈ board n := by
  obtain ⟨m, hm⟩ := hn
  subst hm
  rw [mem_special] at hs
  obtain ⟨hsb, hp1, hp2⟩ := hs
  have hb := mem_board.mp hsb
  rw [hbig] at hp1
  have hp2' : C.empty.2 % 2 = 0 := by
    have h := empty_parity_same C ⟨m, rfl⟩
    omega
  rw [hp2'] at hp2
  have hfs : C.f s ≠ s := fun h => hne (C.unique_fixed hsb h)
  have hu := arrow_step_unit C hsb hfs
  have hfb : C.f s ∈ board (2 * m + 1) := C.hf_map s hsb
  have hfb' := mem_board.mp hfb
  rcases hu with h | h | h | h
  · -- u = (1, 0)
    have h1 : C.f s = (s.1 + 1, s.2) := by
      have h2 : C.f s - s = ((1 : ℤ), (0 : ℤ)) := h
      ext
      · have h3 := congrArg Prod.fst h2
        simp at h3
        omega
      · have h3 := congrArg Prod.snd h2
        simp at h3
        omega
    have h7 := congrArg Prod.fst h1
    simp at h7
    have h4 : s.1 + 2 ≤ 2 * (m : ℤ) := by omega
    have h5 : C.arrow s = (s.1 + 2, s.2) := by
      simp only [arrow]
      rw [h1]
      ext <;> simp [Prod.smul_mk, Int.zsmul_eq_mul] <;> omega
    rw [mem_board, h5]
    exact ⟨by omega, by omega, by omega, by omega⟩
  · -- u = (-1, 0)
    have h1 : C.f s = (s.1 - 1, s.2) := by
      have h2 : C.f s - s = ((-1 : ℤ), (0 : ℤ)) := h
      ext
      · have h3 := congrArg Prod.fst h2
        simp at h3
        omega
      · have h3 := congrArg Prod.snd h2
        simp at h3
        omega
    have h7 := congrArg Prod.fst h1
    simp at h7
    have h4 : 0 ≤ s.1 - 2 := by omega
    have h5 : C.arrow s = (s.1 - 2, s.2) := by
      simp only [arrow]
      rw [h1]
      ext <;> simp [Prod.smul_mk, Int.zsmul_eq_mul] <;> omega
    rw [mem_board, h5]
    exact ⟨by omega, by omega, by omega, by omega⟩
  · -- u = (0, 1)
    have h1 : C.f s = (s.1, s.2 + 1) := by
      have h2 : C.f s - s = ((0 : ℤ), (1 : ℤ)) := h
      ext
      · have h3 := congrArg Prod.fst h2
        simp at h3
        omega
      · have h3 := congrArg Prod.snd h2
        simp at h3
        omega
    have h7 := congrArg Prod.snd h1
    simp at h7
    have h4 : s.2 + 2 ≤ 2 * (m : ℤ) := by omega
    have h5 : C.arrow s = (s.1, s.2 + 2) := by
      simp only [arrow]
      rw [h1]
      ext <;> simp [Prod.smul_mk, Int.zsmul_eq_mul] <;> omega
    rw [mem_board, h5]
    exact ⟨by omega, by omega, by omega, by omega⟩
  · -- u = (0, -1)
    have h1 : C.f s = (s.1, s.2 - 1) := by
      have h2 : C.f s - s = ((0 : ℤ), (-1 : ℤ)) := h
      ext
      · have h3 := congrArg Prod.fst h2
        simp at h3
        omega
      · have h3 := congrArg Prod.snd h2
        simp at h3
        omega
    have h7 := congrArg Prod.snd h1
    simp at h7
    have h4 : 0 ≤ s.2 - 2 := by omega
    have h5 : C.arrow s = (s.1, s.2 - 2) := by
      simp only [arrow]
      rw [h1]
      ext <;> simp [Prod.smul_mk, Int.zsmul_eq_mul] <;> omega
    rw [mem_board, h5]
    exact ⟨by omega, by omega, by omega, by omega⟩

end Config

/-!
## The directed cycle outside the component
-/

namespace Config

variable {n : ℕ} (C : Config n)

theorem ne_empty_of_notMem_comp {s : Cell} (h : s ∉ C.comp) : s ≠ C.empty :=
  fun h' => h (h'.symm ▸ C.empty_mem_comp)

theorem empty_of_arrow_self {s : Cell} (hs : s ∈ C.special) (h : C.arrow s = s) :
    s = C.empty := by
  have h5 : C.f s = s := by
    have h6 : C.arrow s = s + 2 • (C.f s - s) := rfl
    rw [h] at h6
    have h7 : 2 • (C.f s - s) = 0 := by
      have h8 : s + 2 • (C.f s - s) = s + 0 := by
        rw [add_zero]
        exact h6.symm
      exact add_left_cancel_iff.mp h8
    have h8 := congrArg Prod.fst h7
    have h9 := congrArg Prod.snd h7
    simp [Prod.smul_mk, Int.zsmul_eq_mul] at h8 h9
    ext <;> omega
  exact C.unique_fixed (mem_board_of_mem_special C hs) h5

/-- Iterating the arrow from a special cell outside the component eventually
repeats, yielding a directed cycle. -/
theorem exists_directed_cycle (hn : Odd n) (hbig : C.empty.1 % 2 = 0) {s₀ : Cell}
    (hs0 : s₀ ∈ C.special) (hs0' : s₀ ∉ C.comp) :
    ∃ (m : ℕ) (z : Fin (m + 4) → Cell), Function.Injective z ∧
      (∀ i : Fin (m + 4), z i ∈ C.special ∧ z i ∉ C.comp) ∧
      (∀ i : Fin (m + 4), C.arrow (z i) = z (i + 1)) := by
  classical
  set a : ℕ → Cell := fun k => (C.arrow)^[k] s₀ with ha
  have hstep : ∀ k, a k ∈ C.special ∧ a k ∉ C.comp ∧ C.arrow (a k) ∈ board n := by
    intro k
    induction k with
    | zero => exact ⟨hs0, hs0', arrow_mem_board_big C hn hbig hs0 (ne_empty_of_notMem_comp C hs0')⟩
    | succ k ih =>
      obtain ⟨hmem, hnmem, harr⟩ := ih
      have hga : C.gAdj (a k) (a (k + 1)) := by
        have h1 : a (k + 1) = C.arrow (a k) := by
          rw [ha]
          exact Function.iterate_succ_apply' _ _ _
        rw [h1]
        exact Or.inl ⟨hmem, fun h => hnmem (h ▸ C.empty_mem_comp), rfl, harr⟩
      have hmem' : a (k + 1) ∈ C.special := by
        have h1 : a (k + 1) = C.arrow (a k) := by
          rw [ha]
          exact Function.iterate_succ_apply' _ _ _
        rw [h1]
        exact arrow_mem_special C hmem (fun h => hnmem (h ▸ C.empty_mem_comp)) harr
      have hnmem' : a (k + 1) ∉ C.comp := by
        intro h
        exact hnmem (mem_comp_of_gAdj C hga.symm h)
      have harr' : C.arrow (a (k + 1)) ∈ board n := by
        have h1 : a (k + 1) = C.arrow (a k) := by
          rw [ha]
          exact Function.iterate_succ_apply' _ _ _
        rw [h1] at hmem' hnmem' ⊢
        exact arrow_mem_board_big C hn hbig hmem' (ne_empty_of_notMem_comp C hnmem')
      exact ⟨hmem', hnmem', harr'⟩
  obtain ⟨i, j, hij, heq⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun k : ℕ => (⟨a k, (hstep k).1⟩ : ↥C.special))
  have heq' : a i = a j := Subtype.ext_iff.mp heq
  have hex : ∃ j, ∃ i, i < j ∧ a i = a j := by
    rcases lt_trichotomy i j with hlt | heq2 | hgt
    · exact ⟨j, i, hlt, heq'⟩
    · exact absurd heq2 hij
    · exact ⟨i, j, hgt, heq'.symm⟩
  set j := Nat.find hex with hjeq
  obtain ⟨i, hij, heq''⟩ := Nat.find_spec hex
  rw [← hjeq] at hij heq''
  -- the cycle a i, …, a (j - 1) has no internal repeats (minimality of `j`)
  have hnodup : ∀ p q : ℕ, i ≤ p → p < q → q ≤ j - 1 → a p ≠ a q := by
    intro p q hp hpq hq h
    have h1 : j ≤ q := Nat.find_min' hex ⟨p, hpq, h⟩
    omega
  -- L ≠ 1: no self-loops
  have hne1 : j - i ≠ 1 := by
    intro h
    have hj : j = i + 1 := by omega
    rw [hj] at heq''
    have h2 : a (i + 1) = C.arrow (a i) := by
      rw [ha]
      exact Function.iterate_succ_apply' _ _ _
    rw [h2] at heq''
    exact (hstep i).2.1 (empty_of_arrow_self C (hstep i).1 heq''.symm ▸ C.empty_mem_comp)
  -- L ≠ 2: no 2-cycles
  have hne2 : j - i ≠ 2 := by
    intro h
    have hj : j = i + 2 := by omega
    rw [hj] at heq''
    have h2 : C.arrow (a (i + 1)) = a i := by
      have h4 : a (i + 2) = C.arrow (a (i + 1)) := by
        rw [ha]
        exact Function.iterate_succ_apply' _ _ _
      rw [h4] at heq''
      exact heq''.symm
    have h3 : a (i + 1) = C.arrow (a i) := by
      rw [ha]
      exact Function.iterate_succ_apply' _ _ _
    have h4 : a i = a (i + 1) := arrow_no_2cycle C (mem_board_of_mem_special C (hstep i).1)
      (mem_board_of_mem_special C (hstep (i + 1)).1) h3.symm h2
    rw [← h4] at h3
    exact (hstep i).2.1 (empty_of_arrow_self C (hstep i).1 h3.symm ▸ C.empty_mem_comp)
  -- L ≠ 3: parity of coordinate sums
  have hne3 : j - i ≠ 3 := by
    intro h
    have hj : j = i + 3 := by omega
    rw [hj] at heq''
    have hΔ : ∀ k, ((a (i + k + 1)).1 + (a (i + k + 1)).2 =
        (a (i + k)).1 + (a (i + k)).2 +
          2 * (((C.f (a (i + k))).1 - (a (i + k)).1) + ((C.f (a (i + k))).2 - (a (i + k)).2))) := by
      intro k
      have h1 : a (i + k + 1) = C.arrow (a (i + k)) := by
        rw [ha]
        exact Function.iterate_succ_apply' _ _ _
      rw [h1]
      simp [arrow, Prod.smul_mk, Int.zsmul_eq_mul]
      ring
    have hσ : ∀ k, ((C.f (a (i + k))).1 - (a (i + k)).1) + ((C.f (a (i + k))).2 - (a (i + k)).2)
        = 1 ∨ ((C.f (a (i + k))).1 - (a (i + k)).1) + ((C.f (a (i + k))).2 - (a (i + k)).2)
        = -1 := by
      intro k
      have hne : C.f (a (i + k)) ≠ a (i + k) := by
        intro h0
        have h5 : a (i + k) = C.empty := C.unique_fixed (mem_board_of_mem_special C (hstep (i + k)).1) h0
        exact (hstep (i + k)).2.1 (h5 ▸ C.empty_mem_comp)
      have hu := arrow_step_unit C (mem_board_of_mem_special C (hstep (i + k)).1) hne
      rcases hu with h | h | h | h
      · left
        have h6 := congrArg Prod.fst h
        have h7 := congrArg Prod.snd h
        simp at h6 h7
        omega
      · right
        have h6 := congrArg Prod.fst h
        have h7 := congrArg Prod.snd h
        simp at h6 h7
        omega
      · left
        have h6 := congrArg Prod.fst h
        have h7 := congrArg Prod.snd h
        simp at h6 h7
        omega
      · right
        have h6 := congrArg Prod.fst h
        have h7 := congrArg Prod.snd h
        simp at h6 h7
        omega
    have hsum0 : (a (i + 1)).1 + (a (i + 1)).2 =
        (a i).1 + (a i).2 +
          2 * (((C.f (a i)).1 - (a i).1) + ((C.f (a i)).2 - (a i).2)) := hΔ 0
    have hsum1 : (a (i + 2)).1 + (a (i + 2)).2 =
        (a (i + 1)).1 + (a (i + 1)).2 +
          2 * (((C.f (a (i + 1))).1 - (a (i + 1)).1) + ((C.f (a (i + 1))).2 - (a (i + 1)).2)) :=
      hΔ 1
    have hsum2 : (a (i + 3)).1 + (a (i + 3)).2 =
        (a (i + 2)).1 + (a (i + 2)).2 +
          2 * (((C.f (a (i + 2))).1 - (a (i + 2)).1) + ((C.f (a (i + 2))).2 - (a (i + 2)).2)) :=
      hΔ 2
    have hσ0 : ((C.f (a i)).1 - (a i).1) + ((C.f (a i)).2 - (a i).2) = 1 ∨
        ((C.f (a i)).1 - (a i).1) + ((C.f (a i)).2 - (a i).2) = -1 := hσ 0
    have hσ1 : ((C.f (a (i + 1))).1 - (a (i + 1)).1) + ((C.f (a (i + 1))).2 - (a (i + 1)).2) = 1 ∨
        ((C.f (a (i + 1))).1 - (a (i + 1)).1) + ((C.f (a (i + 1))).2 - (a (i + 1)).2) = -1 := hσ 1
    have hσ2 : ((C.f (a (i + 2))).1 - (a (i + 2)).1) + ((C.f (a (i + 2))).2 - (a (i + 2)).2) = 1 ∨
        ((C.f (a (i + 2))).1 - (a (i + 2)).1) + ((C.f (a (i + 2))).2 - (a (i + 2)).2) = -1 := hσ 2
    have hcl : (a (i + 3)).1 + (a (i + 3)).2 = (a i).1 + (a i).2 := by
      rw [heq'']
    omega
  have hL : 4 ≤ j - i := by
    have h0 : i + 1 ≤ j := hij
    omega
  have hL' : j - i - 4 + 4 = j - i := by omega
  refine ⟨j - i - 4, fun k => a (i + k.val), ?_, ?_, ?_⟩
  · -- injective
    intro k₁ k₂ h
    have h1 : a (i + k₁.val) = a (i + k₂.val) := h
    have hk1 : i + k₁.val ≤ (Nat.find hex) - 1 := by
      have := Fin.is_lt k₁
      omega
    have hk2 : i + k₂.val ≤ (Nat.find hex) - 1 := by
      have := Fin.is_lt k₂
      omega
    by_cases he : i + k₁.val = i + k₂.val
    · exact Fin.ext (by omega)
    · rcases lt_trichotomy (i + k₁.val) (i + k₂.val) with hlt | heq2 | hgt
      · exact absurd h1 (hnodup (i + k₁.val) (i + k₂.val) (by omega) hlt hk2)
      · exact absurd heq2 he
      · exact absurd h1.symm (hnodup (i + k₂.val) (i + k₁.val) (by omega) hgt hk1)
  · -- special and outside the component
    intro k
    have hk : i + k.val ≤ (Nat.find hex) - 1 := by
      have := Fin.is_lt k
      omega
    exact ⟨(hstep (i + k.val)).1, (hstep (i + k.val)).2.1⟩
  · -- closure: arrow z k = z (k+1)
    intro k
    show C.arrow (a (i + k.val)) = a (i + (k + 1).val)
    by_cases hk : k = Fin.last (j - i - 4 + 3)
    · -- last vertex: wraps around to `a i`
      have hkv : k.val = j - i - 1 := by
        rw [hk]
        simp [Fin.val_last]
        omega
      have hv0 : (k + 1).val = 0 := by
        rw [hk, Fin.val_add_one]
        simp [Fin.val_last]
      have h2 : i + k.val = (Nat.find hex) - 1 := by omega
      have h3 : i + (k + 1).val = i := by
        rw [hv0]
        simp
      rw [h3, heq'', h2]
      have h5 : j - 1 + 1 = Nat.find hex := by omega
      have h6 : a j = (C.arrow)^[j - 1 + 1] s₀ := by
        rw [h5]
      rw [h6, Function.iterate_succ_apply']
    · -- ordinary vertex: index +1
      have h1 : (k + 1).val = k.val + 1 := by
        rw [Fin.val_add_one]
        simp only [hk, ↓reduceIte]
      have h2 : a (i + (k.val + 1)) = C.arrow (a (i + k.val)) := by
        show (C.arrow)^[i + k.val + 1] s₀ = C.arrow ((C.arrow)^[i + k.val] s₀)
        exact Function.iterate_succ_apply' _ _ _
      rw [h1]
      exact h2.symm

end Config

/-!
## The cycle as an `OrthoLoop`
-/

/-- The midpoint of the segment between two cells. -/
def midPt (p q : Cell) : Cell := ((p.1 + q.1) / 2, (p.2 + q.2) / 2)

theorem midPt_comm (p q : Cell) : midPt p q = midPt q p := by
  simp [midPt, add_comm]

section GeoClaim

open Finset

theorem ne_last_of_val_lt {n : ℕ} (i : Fin (n + 4)) (h : (i : ℕ) < n + 3) : i ≠ Fin.last (n + 3) := by
  intro hlast
  have hlv := congrArg Fin.val hlast
  rw [Fin.val_last] at hlv
  omega

theorem val_succ_of_not_last {n : ℕ} (i : Fin (n + 4)) (h : i ≠ Fin.last (n + 3)) :
    ((i + 1 : Fin (n + 4)) : ℕ) = ↑i + 1 := by
  have hvo := Fin.val_add_one i
  rw [if_neg h] at hvo
  exact hvo

theorem val_last_succ {n : ℕ} : ((Fin.last (n + 3) + 1 : Fin (n + 4)) : ℕ) = 0 := by
  have hvo := Fin.val_add_one (Fin.last (n + 3))
  rw [if_pos rfl] at hvo
  exact hvo

theorem lt_of_isLt_add {m n : ℕ} (i : Fin n) (h : n + 2 = m) : (i : ℕ) + 2 < m := by
  rw [← h]
  exact Nat.add_lt_add_right i.isLt 2


/-- Clamp of `t` to the band `[h, h+2]`, shifted: 0 below, 2 above. -/
def clamp2 (h t : ℤ) : ℤ := min (max (t - h) 0) 2

/-- A simple closed rectilinear loop: vertices `v₀,…,v_{n+3}` pairwise distinct,
each edge axis-aligned of length exactly 2, all vertices in one parity class
`(a, b) (mod 2)`, and non-adjacent edges disjoint (simplicity). -/
structure OrthoLoop where
  a : ℤ
  b : ℤ
  n : ℕ
  v : Fin (n + 4) → Cell
  inj : Function.Injective v
  step : ∀ i : Fin (n + 4),
    ((v (i + 1)).1 = (v i).1 ∧ (v (i + 1)).2 = (v i).2 + 2) ∨
    ((v (i + 1)).1 = (v i).1 ∧ (v (i + 1)).2 = (v i).2 - 2) ∨
    ((v (i + 1)).1 = (v i).1 + 2 ∧ (v (i + 1)).2 = (v i).2) ∨
    ((v (i + 1)).1 = (v i).1 - 2 ∧ (v (i + 1)).2 = (v i).2)
  par : ∀ i : Fin (n + 4), ((v i).1 : ZMod 2) = a ∧ ((v i).2 : ZMod 2) = b
  simple : ∀ i j : Fin (n + 4), i ≠ j → i + 1 ≠ j → i ≠ j + 1 →
    Disjoint ({v i, midPt (v i) (v (i + 1)), v (i + 1)} : Finset Cell)
      ({v j, midPt (v j) (v (j + 1)), v (j + 1)} : Finset Cell)

theorem add_one_ne_self {n : ℕ} (i : Fin (n + 4)) : i ≠ i + 1 := by
  intro h
  have hv := congrArg Fin.val h
  rw [Fin.val_add_one] at hv
  split at hv
  · rename_i hlast
    have : i = Fin.last (n + 3) := hlast
    rw [this, Fin.val_last] at hv
    omega
  · omega

theorem add_two_ne_self {n : ℕ} (i : Fin (n + 4)) : i ≠ i + 1 + 1 := by
  intro h
  have hv := congrArg Fin.val h
  have h1 := Fin.val_add_one (i + 1)
  have h2 := Fin.val_add_one i
  rw [h1, h2] at hv
  by_cases hi1 : i + 1 = Fin.last (n + 3)
  · rw [if_pos hi1] at hv
    have hv2 : ((i + 1 : Fin (n + 4)) : ℕ) = n + 3 := by rw [hi1]; exact Fin.val_last _
    rw [Fin.val_add_one] at hv2
    split at hv2
    · omega
    · omega
  · rw [if_neg hi1] at hv
    by_cases hi2 : i = Fin.last (n + 3)
    · rw [if_pos hi2, hi2, Fin.val_last] at hv
      omega
    · rw [if_neg hi2] at hv
      omega

namespace OrthoLoop

variable (W : OrthoLoop)

/-- Number of vertices of the loop. -/
def L : ℕ := W.n + 4

/-- First coordinate of vertex `i`. -/
abbrev x (i : Fin (W.n + 4)) : ℤ := (W.v i).1

/-- Second coordinate of vertex `i`. -/
abbrev y (i : Fin (W.n + 4)) : ℤ := (W.v i).2

/-- Edge `i` (from vertex `i` to vertex `i+1`) is vertical. -/
abbrev vert (i : Fin (W.n + 4)) : Prop := W.x (i + 1) = W.x i

/-- Lower end of the y-range of edge `i`. -/
abbrev lo (i : Fin (W.n + 4)) : ℤ := min (W.y i) (W.y (i + 1))

/-- Upper end of the y-range of edge `i`. -/
abbrev hi (i : Fin (W.n + 4)) : ℤ := max (W.y i) (W.y (i + 1))

/-- Midpoint of edge `i`. -/
abbrev mid (i : Fin (W.n + 4)) : Cell := midPt (W.v i) (W.v (i + 1))

/-- Lattice points on edge `i`: endpoints and midpoint. -/
abbrev edgePts (i : Fin (W.n + 4)) : Finset Cell := {W.v i, W.mid i, W.v (i + 1)}

/-- All lattice points on the loop. -/
def boundary : Finset Cell := Finset.univ.biUnion W.edgePts

/-- Crossing parity of `c`: number (mod 2) of vertical edges strictly to the
right of `c` whose half-open y-range `[lo, hi)` contains `c.2`. -/
def p2 (c : Cell) : ZMod 2 :=
  ∑ i : Fin (W.n + 4),
    if W.vert i ∧ c.1 < W.x i ∧ W.lo i ≤ c.2 ∧ c.2 < W.hi i then 1 else 0

/-- `c` is inside the loop (odd crossing parity). -/
def inside (c : Cell) : Prop := W.p2 c = 1

/-- Strictly interior lattice points. -/
def interior : Set Cell := {c | W.inside c ∧ c ∉ W.boundary}

/-- Shoelace sum. -/
def S : ℤ := ∑ i : Fin (W.n + 4), W.x i * (W.y (i + 1) - W.y (i - 1))

/-- Shoelace sum divided by 2 (signed area). -/
def T : ℤ := ∑ i : Fin (W.n + 4), W.x i * ((W.y (i + 1) - W.y (i - 1)) / 2)

/-- Number of strictly interior lattice points. -/
noncomputable def I : ℕ := W.interior.ncard

/-- The master parity proposition. -/
def P : Prop := (W.I : ZMod 2) = (W.T : ZMod 2) + (W.L : ZMod 2) + 1

/-! ### Basic coordinate API -/

theorem parX (i : Fin (W.n + 4)) : (W.x i : ZMod 2) = W.a := (W.par i).1

theorem parY (i : Fin (W.n + 4)) : (W.y i : ZMod 2) = W.b := (W.par i).2

theorem y_succ_cases (i : Fin (W.n + 4)) :
    W.y (i + 1) = W.y i + 2 ∨ W.y (i + 1) = W.y i - 2 ∨ W.y (i + 1) = W.y i := by
  rcases W.step i with ⟨-, hy⟩ | ⟨-, hy⟩ | ⟨-, hy⟩ | ⟨-, hy⟩ <;> tauto

theorem x_succ_cases (i : Fin (W.n + 4)) :
    W.x (i + 1) = W.x i ∨ W.x (i + 1) = W.x i + 2 ∨ W.x (i + 1) = W.x i - 2 := by
  rcases W.step i with ⟨hx, -⟩ | ⟨hx, -⟩ | ⟨hx, -⟩ | ⟨hx, -⟩ <;> tauto

theorem vert_cases (i : Fin (W.n + 4)) (h : W.vert i) :
    W.y (i + 1) = W.y i + 2 ∨ W.y (i + 1) = W.y i - 2 := by
  rcases W.step i with ⟨-, hy⟩ | ⟨-, hy⟩ | ⟨hx, -⟩ | ⟨hx, -⟩
  · exact Or.inl hy
  · exact Or.inr hy
  · exfalso; have h' : (W.v (i + 1)).1 = (W.v i).1 := h; omega
  · exfalso; have h' : (W.v (i + 1)).1 = (W.v i).1 := h; omega

theorem horiz_cases (i : Fin (W.n + 4)) (h : ¬ W.vert i) :
    (W.x (i + 1) = W.x i + 2 ∧ W.y (i + 1) = W.y i) ∨
    (W.x (i + 1) = W.x i - 2 ∧ W.y (i + 1) = W.y i) := by
  rcases W.step i with ⟨hx, -⟩ | ⟨hx, -⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact absurd hx h
  · exact absurd hx h
  · exact Or.inl ⟨hx, hy⟩
  · exact Or.inr ⟨hx, hy⟩

theorem vert_of_y_ne (i : Fin (W.n + 4)) (hne : W.y (i + 1) ≠ W.y i) : W.vert i := by
  by_contra hv
  rcases W.horiz_cases i hv with ⟨-, hy⟩ | ⟨-, hy⟩ <;> exact hne hy

theorem hi_eq_lo_add_two (i : Fin (W.n + 4)) (h : W.vert i) : W.hi i = W.lo i + 2 := by
  rcases W.vert_cases i h with hy | hy
  · show max (W.y i) (W.y (i + 1)) = min (W.y i) (W.y (i + 1)) + 2
    rw [hy, max_eq_right (by omega : W.y i ≤ W.y i + 2),
      min_eq_left (by omega : W.y i ≤ W.y i + 2)]
  · show max (W.y i) (W.y (i + 1)) = min (W.y i) (W.y (i + 1)) + 2
    rw [hy, max_eq_left (by omega : W.y i - 2 ≤ W.y i),
      min_eq_right (by omega : W.y i - 2 ≤ W.y i)]
    omega

theorem lo_parY (i : Fin (W.n + 4)) : (W.lo i : ZMod 2) = W.b := by
  rcases min_choice (W.y i) (W.y (i + 1)) with h | h
  · have h' : W.lo i = W.y i := h
    rw [h']; exact W.parY i
  · have h' : W.lo i = W.y (i + 1) := h
    rw [h']; exact W.parY _

theorem dvd_add_fst (i : Fin (W.n + 4)) : (2 : ℤ) ∣ (W.v i).1 + (W.v (i + 1)).1 := by
  have h1 : ((W.v i).1 : ZMod 2) = W.a := W.parX i
  have h2 : ((W.v (i + 1)).1 : ZMod 2) = W.a := W.parX (i + 1)
  have hz : (((W.v i).1 + (W.v (i + 1)).1 : ℤ) : ZMod 2) = 0 := by
    push_cast
    rw [h1, h2, ← two_mul]
    have h0 : (2 : ZMod 2) = 0 := by decide
    rw [h0, zero_mul]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz

theorem dvd_add_snd (i : Fin (W.n + 4)) : (2 : ℤ) ∣ (W.v i).2 + (W.v (i + 1)).2 := by
  have h1 : ((W.v i).2 : ZMod 2) = W.b := W.parY i
  have h2 : ((W.v (i + 1)).2 : ZMod 2) = W.b := W.parY (i + 1)
  have hz : (((W.v i).2 + (W.v (i + 1)).2 : ℤ) : ZMod 2) = 0 := by
    push_cast
    rw [h1, h2, ← two_mul]
    have h0 : (2 : ZMod 2) = 0 := by decide
    rw [h0, zero_mul]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz

/-- The midpoint of an edge never lies in the vertex parity class. -/
theorem mid_par (i : Fin (W.n + 4)) :
    ¬ (((W.mid i).1 : ZMod 2) = W.a ∧ ((W.mid i).2 : ZMod 2) = W.b) := by
  rintro ⟨h1, h2⟩
  have key : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases W.step i with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
  · have e2 : (W.mid i).2 = W.y i + 1 := by
      show ((W.v i).2 + (W.v (i + 1)).2) / 2 = (W.v i).2 + 1; omega
    rw [e2, Int.cast_add, W.parY i] at h2
    rcases key W.b with hb | hb <;> rw [hb] at h2 <;> · revert h2; decide
  · have e2 : (W.mid i).2 = W.y i - 1 := by
      show ((W.v i).2 + (W.v (i + 1)).2) / 2 = (W.v i).2 - 1; omega
    rw [e2, Int.cast_sub, W.parY i] at h2
    rcases key W.b with hb | hb <;> rw [hb] at h2 <;> · revert h2; decide
  · have e1 : (W.mid i).1 = W.x i + 1 := by
      show ((W.v i).1 + (W.v (i + 1)).1) / 2 = (W.v i).1 + 1; omega
    rw [e1, Int.cast_add, W.parX i] at h1
    rcases key W.a with ha | ha <;> rw [ha] at h1 <;> · revert h1; decide
  · have e1 : (W.mid i).1 = W.x i - 1 := by
      show ((W.v i).1 + (W.v (i + 1)).1) / 2 = (W.v i).1 - 1; omega
    rw [e1, Int.cast_sub, W.parX i] at h1
    rcases key W.a with ha | ha <;> rw [ha] at h1 <;> · revert h1; decide

/-- A vertex never equals an edge midpoint. -/
theorem vertex_ne_mid (k i : Fin (W.n + 4)) : W.v k ≠ W.mid i := by
  intro h
  exact W.mid_par i (h ▸ W.par k)

theorem vertex_mem_edgePts (k i : Fin (W.n + 4)) :
    W.v k ∈ W.edgePts i ↔ k = i ∨ k = i + 1 := by
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (h | h | h)
    · exact Or.inl (W.inj h)
    · exact absurd h (W.vertex_ne_mid k i)
    · exact Or.inr (W.inj h)
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr rfl)

theorem mid_mem_edgePts (i : Fin (W.n + 4)) : W.mid i ∈ W.edgePts i := by
  simp [Finset.mem_insert, Finset.mem_singleton]

/-- The midpoint map is injective. -/
theorem mid_inj : Function.Injective W.mid := by
  intro i j h
  by_contra hne
  have hd1 : (2 : ℤ) ∣ (W.v i).1 + (W.v (i + 1)).1 := W.dvd_add_fst i
  have hd2 : (2 : ℤ) ∣ (W.v i).2 + (W.v (i + 1)).2 := W.dvd_add_snd i
  have hd3 : (2 : ℤ) ∣ (W.v j).1 + (W.v (j + 1)).1 := W.dvd_add_fst j
  have hd4 : (2 : ℤ) ∣ (W.v j).2 + (W.v (j + 1)).2 := W.dvd_add_snd j
  have h1 : ((W.v i).1 + (W.v (i + 1)).1) / 2 = ((W.v j).1 + (W.v (j + 1)).1) / 2 :=
    congrArg Prod.fst h
  have h2 : ((W.v i).2 + (W.v (i + 1)).2) / 2 = ((W.v j).2 + (W.v (j + 1)).2) / 2 :=
    congrArg Prod.snd h
  have h3 : (W.v i).1 + (W.v (i + 1)).1 = (W.v j).1 + (W.v (j + 1)).1 := by omega
  have h4 : (W.v i).2 + (W.v (i + 1)).2 = (W.v j).2 + (W.v (j + 1)).2 := by omega
  by_cases ha : i + 1 = j
  · subst ha
    have hvv : W.v i = W.v (i + 1 + 1) := Prod.ext (by omega) (by omega)
    have hii := W.inj hvv
    exact absurd hii (add_two_ne_self i)
  · by_cases hb : j + 1 = i
    · subst hb
      have hvv : W.v j = W.v (j + 1 + 1) := Prod.ext (by omega) (by omega)
      have hjj := W.inj hvv
      exact absurd hjj (add_two_ne_self j)
    · have hd := W.simple i j hne ha (fun hji => hb hji.symm)
      have hm1 : W.mid i ∈ W.edgePts i := W.mid_mem_edgePts i
      have hm2 : W.mid i ∈ W.edgePts j := by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        exact Or.inr (Or.inl h)
      exact Finset.disjoint_left.mp hd hm1 hm2

theorem mem_boundary (c : Cell) :
    c ∈ W.boundary ↔ (∃ i, W.v i = c) ∨ (∃ i, W.mid i = c) := by
  simp only [boundary, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨i, h | h | h⟩
    · exact Or.inl ⟨i, h.symm⟩
    · exact Or.inr ⟨i, h.symm⟩
    · exact Or.inl ⟨i + 1, h.symm⟩
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact ⟨i, Or.inl rfl⟩
    · exact ⟨i, Or.inr (Or.inl rfl)⟩

theorem vertex_mem_boundary (i : Fin (W.n + 4)) : W.v i ∈ W.boundary := by
  rw [W.mem_boundary]; exact Or.inl ⟨i, rfl⟩

theorem mid_mem_boundary (i : Fin (W.n + 4)) : W.mid i ∈ W.boundary := by
  rw [W.mem_boundary]; exact Or.inr ⟨i, rfl⟩

theorem edgePts_rev (i : Fin (W.n + 4)) :
    ({W.v (i + 1), midPt (W.v (i + 1)) (W.v i), W.v i} : Finset Cell) = W.edgePts i := by
  ext c
  simp only [Finset.mem_insert, Finset.mem_singleton, OrthoLoop.edgePts, OrthoLoop.mid,
    midPt_comm]
  tauto

/-! ### Cyclic sums -/

theorem sum_cyclic_sub {n : ℕ} (f : Fin (n + 4) → ℤ) :
    ∑ i : Fin (n + 4), (f (i + 1) - f i) = 0 := by
  have h : ∑ i : Fin (n + 4), f (i + 1) = ∑ i : Fin (n + 4), f i := by
    have hc := Equiv.sum_comp (finRotate (n + 4)) f
    simp only [finRotate_apply] at hc
    rw [hc]
  rw [Finset.sum_sub_distrib, h, sub_self]

theorem sum_cyclic_sub' {n : ℕ} (f : Fin (n + 4) → ℤ) :
    ∑ i : Fin (n + 4), (f i - f (i - 1)) = 0 := by
  have h : ∑ i : Fin (n + 4), f (i - 1) = ∑ i : Fin (n + 4), f i := by
    have hc := Equiv.sum_comp (finRotate (n + 4)).symm f
    simp only [finRotate_symm_apply] at hc
    rw [hc]
  rw [Finset.sum_sub_distrib, h, sub_self]

/-- Crossing a horizontal level: up-transitions from `h` equal down-transitions
into `h`, for `h` in the vertex parity class. -/
theorem up_eq_down (h : ℤ) (hh : (h : ZMod 2) = W.b) :
    (univ.filter fun i => W.y i = h ∧ W.y (i + 1) = h + 2).card =
    (univ.filter fun i => W.y i = h + 2 ∧ W.y (i + 1) = h).card := by
  classical
  have hsum : ∑ i : Fin (W.n + 4), (clamp2 h (W.y (i + 1)) - clamp2 h (W.y i)) = 0 :=
    sum_cyclic_sub (fun i => clamp2 h (W.y i))
  have hpoint : ∀ i : Fin (W.n + 4),
      clamp2 h (W.y (i + 1)) - clamp2 h (W.y i) =
      2 * (if W.y i = h ∧ W.y (i + 1) = h + 2 then (1 : ℤ) else 0) -
      2 * (if W.y i = h + 2 ∧ W.y (i + 1) = h then (1 : ℤ) else 0) := by
    intro i
    have hpy : (W.y i : ZMod 2) = W.b := W.parY i
    have hy2 : (((W.y i - h : ℤ)) : ZMod 2) = 0 := by
      rw [Int.cast_sub, hpy, hh, sub_self]
    have hdeven : Even (W.y i - h) := by
      rw [even_iff_two_dvd]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hy2
    obtain ⟨k, hk⟩ := hdeven
    have hk2 : W.y i - h = 2 * k := by omega
    simp only [clamp2]
    rcases W.y_succ_cases i with hy1 | hy1 | hy1 <;> omega
  rw [Finset.sum_congr rfl (fun i _ => hpoint i)] at hsum
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_boole, Finset.sum_boole] at hsum
  omega

/-! ### Bounding box and far field -/

def maxX : ℤ := (univ.image W.x).max' (Finset.Nonempty.image univ_nonempty W.x)

def minX : ℤ := (univ.image W.x).min' (Finset.Nonempty.image univ_nonempty W.x)

def maxY : ℤ := (univ.image W.y).max' (Finset.Nonempty.image univ_nonempty W.y)

def minY : ℤ := (univ.image W.y).min' (Finset.Nonempty.image univ_nonempty W.y)

theorem x_le_maxX (i : Fin (W.n + 4)) : W.x i ≤ W.maxX :=
  Finset.le_max' _ _ (Finset.mem_image_of_mem W.x (Finset.mem_univ i))

theorem minX_le_x (i : Fin (W.n + 4)) : W.minX ≤ W.x i :=
  Finset.min'_le _ _ (Finset.mem_image_of_mem W.x (Finset.mem_univ i))

theorem y_le_maxY (i : Fin (W.n + 4)) : W.y i ≤ W.maxY :=
  Finset.le_max' _ _ (Finset.mem_image_of_mem W.y (Finset.mem_univ i))

theorem minY_le_y (i : Fin (W.n + 4)) : W.minY ≤ W.y i :=
  Finset.min'_le _ _ (Finset.mem_image_of_mem W.y (Finset.mem_univ i))

theorem exists_y_eq_maxY : ∃ i : Fin (W.n + 4), W.y i = W.maxY := by
  have h := (univ.image W.y).max'_mem (Finset.Nonempty.image univ_nonempty W.y)
  rw [Finset.mem_image] at h
  obtain ⟨i, -, hi⟩ := h
  exact ⟨i, hi⟩

theorem p2_eq_zero_of_maxX_le {c : Cell} (h : W.maxX ≤ c.1) : W.p2 c = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  rw [if_neg]
  rintro ⟨-, h2, -, -⟩
  have h3 := W.x_le_maxX i
  omega

theorem p2_eq_zero_of_minY {c : Cell} (h : c.2 < W.minY) : W.p2 c = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  rw [if_neg]
  rintro ⟨-, -, h2, -⟩
  have hlo : W.minY ≤ W.lo i := by
    show W.minY ≤ min (W.y i) (W.y (i + 1))
    rw [le_min_iff]
    exact ⟨W.minY_le_y i, W.minY_le_y (i + 1)⟩
  omega

theorem p2_eq_zero_of_maxY {c : Cell} (h : W.maxY ≤ c.2) : W.p2 c = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  rw [if_neg]
  rintro ⟨-, -, -, h2⟩
  have hhi : W.hi i ≤ W.maxY := by
    show max (W.y i) (W.y (i + 1)) ≤ W.maxY
    rw [max_le_iff]
    exact ⟨W.y_le_maxY i, W.y_le_maxY (i + 1)⟩
  omega

theorem zmod2_eq_of_add_add_zero {x y : ZMod 2} (h : x + y = 0) : x = y := by
  have key : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases key x with hx | hx <;> rcases key y with hy | hy <;> rw [hx, hy] at h ⊢ <;> · revert h; decide

theorem zmod2_ite_add {A B : Prop} [Decidable A] [Decidable B] (h : ¬ (A ∧ B)) :
    (if A ∨ B then (1 : ZMod 2) else 0) = (if A then 1 else 0) + (if B then 1 else 0) := by
  by_cases hA : A <;> by_cases hB : B <;> simp [hA, hB] <;> tauto

theorem up_add_down_zero (h : ℤ) :
    ((univ.filter fun i => W.y i = h ∧ W.y (i + 1) = h + 2).card : ZMod 2) +
    ((univ.filter fun i => W.y i = h + 2 ∧ W.y (i + 1) = h).card : ZMod 2) = 0 := by
  classical
  by_cases hh : (h : ZMod 2) = W.b
  · rw [W.up_eq_down h hh, ← two_mul]
    have h0 : (2 : ZMod 2) = 0 := by decide
    rw [h0, zero_mul]
  · have e1 : (univ.filter fun i => W.y i = h ∧ W.y (i + 1) = h + 2) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro i _
      rintro ⟨h1, -⟩
      exact hh (h1 ▸ W.parY i)
    have e2 : (univ.filter fun i => W.y i = h + 2 ∧ W.y (i + 1) = h) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro i _
      rintro ⟨h1, -⟩
      have hcast : ((h + 2 : ℤ) : ZMod 2) = (h : ZMod 2) := by
        rw [Int.cast_add, show ((2 : ℤ) : ZMod 2) = 0 by decide, add_zero]
      exact hh (hcast ▸ (h1 ▸ W.parY i))
    rw [e1, e2]
    simp

theorem p2_eq_zero_of_le_minX {c : Cell} (h : c.1 < W.minX) : W.p2 c = 0 := by
  classical
  have hx : ∀ i : Fin (W.n + 4), c.1 < W.x i := fun i => lt_of_lt_of_le h (W.minX_le_x i)
  have hdrop : ∀ i : Fin (W.n + 4),
      (if W.vert i ∧ c.1 < W.x i ∧ W.lo i ≤ c.2 ∧ c.2 < W.hi i then (1 : ZMod 2) else 0) =
      (if W.vert i ∧ W.lo i ≤ c.2 ∧ c.2 < W.hi i then 1 else 0) := by
    intro i
    apply if_congr _ rfl rfl
    constructor
    · rintro ⟨hv, -, h3, h4⟩
      exact ⟨hv, h3, h4⟩
    · rintro ⟨hv, h3, h4⟩
      exact ⟨hv, hx i, h3, h4⟩
  have hiff : ∀ i : Fin (W.n + 4),
      (W.vert i ∧ W.lo i ≤ c.2 ∧ c.2 < W.hi i) ↔
      (W.y i = c.2 ∧ W.y (i + 1) = c.2 + 2) ∨ (W.y i = c.2 + 2 ∧ W.y (i + 1) = c.2) ∨
      (W.y i = c.2 - 1 ∧ W.y (i + 1) = c.2 + 1) ∨ (W.y i = c.2 + 1 ∧ W.y (i + 1) = c.2 - 1) := by
    intro i
    constructor
    · rintro ⟨hv, h1, h2⟩
      rcases W.vert_cases i hv with hy | hy
      · have hlo : W.lo i = W.y i := by
          show min (W.y i) (W.y (i + 1)) = W.y i
          rw [hy]; exact min_eq_left (by omega)
        have hhi : W.hi i = W.y i + 2 := by
          show max (W.y i) (W.y (i + 1)) = W.y i + 2
          rw [hy]; exact max_eq_right (by omega)
        rw [hlo] at h1; rw [hhi] at h2
        have hc : c.2 = W.y i ∨ c.2 = W.y i + 1 := by omega
        rcases hc with h3 | h3
        · exact Or.inl ⟨h3.symm, by omega⟩
        · exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))
      · have hlo : W.lo i = W.y i - 2 := by
          show min (W.y i) (W.y (i + 1)) = W.y i - 2
          rw [hy]; exact min_eq_right (by omega)
        have hhi : W.hi i = W.y i := by
          show max (W.y i) (W.y (i + 1)) = W.y i
          rw [hy]; exact max_eq_left (by omega)
        rw [hlo] at h1; rw [hhi] at h2
        have hc : c.2 = W.y i - 2 ∨ c.2 = W.y i - 1 := by omega
        rcases hc with h3 | h3
        · exact Or.inr (Or.inl ⟨by omega, by omega⟩)
        · exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;>
      · have hv : W.vert i := W.vert_of_y_ne i (by omega)
        refine ⟨hv, ?_, ?_⟩
        · show min (W.y i) (W.y (i + 1)) ≤ c.2
          rw [h1, h2]; omega
        · show c.2 < max (W.y i) (W.y (i + 1))
          rw [h1, h2]; omega
  have hsplit : ∀ i : Fin (W.n + 4),
      (if (W.y i = c.2 ∧ W.y (i + 1) = c.2 + 2) ∨ (W.y i = c.2 + 2 ∧ W.y (i + 1) = c.2) ∨
       (W.y i = c.2 - 1 ∧ W.y (i + 1) = c.2 + 1) ∨ (W.y i = c.2 + 1 ∧ W.y (i + 1) = c.2 - 1)
       then (1 : ZMod 2) else 0) =
      (if W.y i = c.2 ∧ W.y (i + 1) = c.2 + 2 then 1 else 0) +
      ((if W.y i = c.2 + 2 ∧ W.y (i + 1) = c.2 then 1 else 0) +
      ((if W.y i = c.2 - 1 ∧ W.y (i + 1) = c.2 + 1 then 1 else 0) +
      (if W.y i = c.2 + 1 ∧ W.y (i + 1) = c.2 - 1 then 1 else 0))) := by
    intro i
    have hAB : ¬ ((W.y i = c.2 ∧ W.y (i + 1) = c.2 + 2) ∧
        (W.y i = c.2 + 2 ∧ W.y (i + 1) = c.2)) := by
      rintro ⟨⟨h1, -⟩, ⟨h2, -⟩⟩; omega
    have hAC : ¬ ((W.y i = c.2 ∧ W.y (i + 1) = c.2 + 2) ∧
        (W.y i = c.2 - 1 ∧ W.y (i + 1) = c.2 + 1)) := by
      rintro ⟨⟨h1, -⟩, ⟨h2, -⟩⟩; omega
    have hAD : ¬ ((W.y i = c.2 ∧ W.y (i + 1) = c.2 + 2) ∧
        (W.y i = c.2 + 1 ∧ W.y (i + 1) = c.2 - 1)) := by
      rintro ⟨⟨h1, -⟩, ⟨h2, -⟩⟩; omega
    have hBC : ¬ ((W.y i = c.2 + 2 ∧ W.y (i + 1) = c.2) ∧
        (W.y i = c.2 - 1 ∧ W.y (i + 1) = c.2 + 1)) := by
      rintro ⟨⟨h1, -⟩, ⟨h2, -⟩⟩; omega
    have hBD : ¬ ((W.y i = c.2 + 2 ∧ W.y (i + 1) = c.2) ∧
        (W.y i = c.2 + 1 ∧ W.y (i + 1) = c.2 - 1)) := by
      rintro ⟨⟨h1, -⟩, ⟨h2, -⟩⟩; omega
    have hCD : ¬ ((W.y i = c.2 - 1 ∧ W.y (i + 1) = c.2 + 1) ∧
        (W.y i = c.2 + 1 ∧ W.y (i + 1) = c.2 - 1)) := by
      rintro ⟨⟨h1, -⟩, ⟨h2, -⟩⟩; omega
    have hArest : ¬ ((W.y i = c.2 ∧ W.y (i + 1) = c.2 + 2) ∧
        ((W.y i = c.2 + 2 ∧ W.y (i + 1) = c.2) ∨ (W.y i = c.2 - 1 ∧ W.y (i + 1) = c.2 + 1) ∨
         (W.y i = c.2 + 1 ∧ W.y (i + 1) = c.2 - 1))) := by
      rintro ⟨h1, h2 | h2 | h2⟩
      · exact hAB ⟨h1, h2⟩
      · exact hAC ⟨h1, h2⟩
      · exact hAD ⟨h1, h2⟩
    have hBrest : ¬ ((W.y i = c.2 + 2 ∧ W.y (i + 1) = c.2) ∧
        ((W.y i = c.2 - 1 ∧ W.y (i + 1) = c.2 + 1) ∨ (W.y i = c.2 + 1 ∧ W.y (i + 1) = c.2 - 1))) := by
      rintro ⟨h1, h2 | h2⟩
      · exact hBC ⟨h1, h2⟩
      · exact hBD ⟨h1, h2⟩
    rw [zmod2_ite_add hArest, zmod2_ite_add hBrest, zmod2_ite_add hCD]
  rw [p2, Finset.sum_congr rfl (fun i _ => hdrop i),
    Finset.sum_congr rfl (fun i _ => if_congr (hiff i) rfl rfl),
    Finset.sum_congr rfl (fun i _ => hsplit i)]
  simp only [Finset.sum_add_distrib, Finset.sum_boole]
  have hAB := W.up_add_down_zero c.2
  have hCD := W.up_add_down_zero (c.2 - 1)
  rw [show c.2 - 1 + 2 = c.2 + 1 from by ring] at hCD
  linear_combination hAB + hCD

/-! ### Interior points are finite in number -/

noncomputable def box : Finset Cell := (Finset.Icc W.minX (W.maxX - 1)) ×ˢ (Finset.Icc W.minY (W.maxY - 1))

theorem mem_box_of_inside {c : Cell} (hc : W.inside c) : c ∈ W.box := by
  have hne : W.p2 c ≠ 0 := by
    rw [hc]
    exact one_ne_zero
  have h1 : W.minX ≤ c.1 := by
    by_contra hx
    exact hne (W.p2_eq_zero_of_le_minX (by omega))
  have h2 : c.1 ≤ W.maxX - 1 := by
    by_contra hx
    exact hne (W.p2_eq_zero_of_maxX_le (by omega))
  have h3 : W.minY ≤ c.2 := by
    by_contra hx
    exact hne (W.p2_eq_zero_of_minY (by omega))
  have h4 : c.2 ≤ W.maxY - 1 := by
    by_contra hx
    exact hne (W.p2_eq_zero_of_maxY (by omega))
  rw [box, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
  exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩

theorem interior_eq :
    W.interior = ↑(W.box.filter fun c => W.p2 c = 1 ∧ c ∉ W.boundary) := by
  ext c
  rw [interior, Finset.coe_filter]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨W.mem_box_of_inside h1, h1, h2⟩
  · rintro ⟨-, h1, h2⟩
    exact ⟨h1, h2⟩

theorem I_eq : W.I = (W.box.filter fun c => W.p2 c = 1 ∧ c ∉ W.boundary).card := by
  rw [I, interior_eq, Set.ncard_coe_finset]

/-! ### `L` is even and `T ≡ 0 (mod 2)` -/

theorem L_even : Even W.L := by
  classical
  have hone : ∀ i : Fin (W.n + 4), (1 : ℤ) =
      (if W.x (i + 1) = W.x i + 2 then 1 else 0) + (if W.x (i + 1) = W.x i - 2 then 1 else 0) +
      (if W.y (i + 1) = W.y i + 2 then 1 else 0) + (if W.y (i + 1) = W.y i - 2 then 1 else 0) := by
    intro i
    simp only [OrthoLoop.x, OrthoLoop.y]
    rcases W.step i with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> simp [hx, hy] <;> omega
  have hxpoint : ∀ i : Fin (W.n + 4), W.x (i + 1) - W.x i =
      2 * (if W.x (i + 1) = W.x i + 2 then (1 : ℤ) else 0) -
      2 * (if W.x (i + 1) = W.x i - 2 then (1 : ℤ) else 0) := by
    intro i
    simp only [OrthoLoop.x]
    rcases W.step i with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> simp [hx, hy] <;> omega
  have hypoint : ∀ i : Fin (W.n + 4), W.y (i + 1) - W.y i =
      2 * (if W.y (i + 1) = W.y i + 2 then (1 : ℤ) else 0) -
      2 * (if W.y (i + 1) = W.y i - 2 then (1 : ℤ) else 0) := by
    intro i
    simp only [OrthoLoop.y]
    rcases W.step i with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> simp [hx, hy] <;> omega
  have hx0 : ∑ i : Fin (W.n + 4), (W.x (i + 1) - W.x i) = 0 := sum_cyclic_sub _
  rw [Finset.sum_congr rfl (fun i _ => hxpoint i), Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, Finset.sum_boole, Finset.sum_boole] at hx0
  have hy0 : ∑ i : Fin (W.n + 4), (W.y (i + 1) - W.y i) = 0 := sum_cyclic_sub _
  rw [Finset.sum_congr rfl (fun i _ => hypoint i), Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, Finset.sum_boole, Finset.sum_boole] at hy0
  have hL : (W.L : ℤ) = ∑ _i : Fin (W.n + 4), (1 : ℤ) := by
    simp [L, Finset.card_univ, Fintype.card_fin]
  rw [Finset.sum_congr rfl (fun i _ => hone i)] at hL
  simp only [Finset.sum_add_distrib, Finset.sum_boole] at hL
  exact ⟨(univ.filter fun i => W.x (i + 1) = W.x i + 2).card +
    (univ.filter fun i => W.y (i + 1) = W.y i + 2).card, by omega⟩

theorem T_zmod : (W.T : ZMod 2) = 0 := by
  classical
  have hsum0 : ∑ i : Fin (W.n + 4), ((W.y (i + 1) - W.y (i - 1)) / 2 : ℤ) = 0 := by
    have hev : ∀ i : Fin (W.n + 4), Even (W.y (i + 1) - W.y (i - 1)) := by
      intro i
      have h1 : (W.y (i + 1) : ZMod 2) = W.b := W.parY (i + 1)
      have h2 : (W.y (i - 1) : ZMod 2) = W.b := W.parY (i - 1)
      have hy2 : (((W.y (i + 1) - W.y (i - 1) : ℤ)) : ZMod 2) = 0 := by
        rw [Int.cast_sub, h1, h2, sub_self]
      rw [even_iff_two_dvd]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hy2
    have h2 : ∑ i : Fin (W.n + 4), (2 * ((W.y (i + 1) - W.y (i - 1)) / 2) : ℤ) =
        ∑ i : Fin (W.n + 4), (W.y (i + 1) - W.y (i - 1)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Int.two_mul_ediv_two_of_even (hev i)]
    have h3 : ∑ i : Fin (W.n + 4), (W.y (i + 1) - W.y (i - 1)) = 0 := by
      have h4 : ∑ i : Fin (W.n + 4), W.y (i + 1) = ∑ i : Fin (W.n + 4), W.y i := by
        have hc := Equiv.sum_comp (finRotate (W.n + 4)) W.y
        simp only [finRotate_apply] at hc
        rw [hc]
      have h5 : ∑ i : Fin (W.n + 4), W.y (i - 1) = ∑ i : Fin (W.n + 4), W.y i := by
        have hc := Equiv.sum_comp (finRotate (W.n + 4)).symm W.y
        simp only [finRotate_symm_apply] at hc
        rw [hc]
      rw [Finset.sum_sub_distrib, h4, h5, sub_self]
    have h6 : 2 * ∑ i : Fin (W.n + 4), ((W.y (i + 1) - W.y (i - 1)) / 2 : ℤ) = 0 := by
      rw [Finset.mul_sum, h2, h3]
    omega
  have hper : ∀ i : Fin (W.n + 4),
      (W.x i : ZMod 2) * (((W.y (i + 1) - W.y (i - 1)) / 2 : ℤ) : ZMod 2) =
      (W.a : ZMod 2) * (((W.y (i + 1) - W.y (i - 1)) / 2 : ℤ) : ZMod 2) := by
    intro i
    rw [W.parX i]
  have hT2 : (W.T : ZMod 2) =
      (W.a : ZMod 2) * ((∑ i : Fin (W.n + 4), ((W.y (i + 1) - W.y (i - 1)) / 2) : ℤ) : ZMod 2) := by
    rw [T]
    push_cast
    rw [Finset.sum_congr rfl (fun i _ => hper i)]
    rw [← Finset.mul_sum, ← Int.cast_sum]
  rw [hT2, hsum0]
  simp

end OrthoLoop

/-! ### Fin equivalences -/

def finShift {n : ℕ} (k : Fin (n + 4)) : Fin (n + 4) ≃ Fin (n + 4) where
  toFun := fun i => i + k
  invFun := fun i => i - k
  left_inv := by intro i; show i + k - k = i; abel
  right_inv := by intro i; show i - k + k = i; abel

theorem finShift_apply {n : ℕ} (k i : Fin (n + 4)) : (finShift k) i = i + k := rfl

def finNeg {n : ℕ} : Fin (n + 4) ≃ Fin (n + 4) where
  toFun := fun i => -i
  invFun := fun i => -i
  left_inv := by intro i; show -(-i) = i; abel
  right_inv := by intro i; show -(-i) = i; abel

theorem finNeg_apply {n : ℕ} (i : Fin (n + 4)) : finNeg i = -i := rfl

def finNegShift {n : ℕ} : Fin (n + 4) ≃ Fin (n + 4) where
  toFun := fun i => -(i + 1)
  invFun := fun i => -(i + 1)
  left_inv := by
    intro i
    have e : (-(i + 1 : Fin (n + 4))) + 1 = -i := by abel
    show -(-(i + 1) + 1) = i
    rw [e]; abel
  right_inv := by
    intro i
    have e : (-(i + 1 : Fin (n + 4))) + 1 = -i := by abel
    show -(-(i + 1) + 1) = i
    rw [e]; abel

theorem finNegShift_apply {n : ℕ} (i : Fin (n + 4)) : finNegShift i = -(i + 1) := rfl

theorem image_univ_equiv {n : ℕ} (e : Fin (n + 4) ≃ Fin (n + 4)) (f : Fin (n + 4) → ℤ) :
    (univ.image fun i => f (e i)) = univ.image f := by
  ext z
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, h⟩; exact ⟨e i, h⟩
  · rintro ⟨i, h⟩; exact ⟨e.symm i, by rwa [e.apply_symm_apply]⟩

namespace OrthoLoop

variable (W : OrthoLoop)

/-! ### Rotation -/

/-- Cyclic rotation of the vertex list by `k`. -/
abbrev rotate (k : Fin (W.n + 4)) : OrthoLoop where
  a := W.a
  b := W.b
  n := W.n
  v := fun i => W.v (i + k)
  inj := W.inj.comp (finShift k).injective
  step := fun i => by
    have h := W.step (i + k)
    have e : (i + 1 : Fin (W.n + 4)) + k = (i + k) + 1 := by abel
    rw [e]
    exact h
  par := fun i => W.par (i + k)
  simple := fun i j hij hi1j hij1 => by
    have e1 : (i + 1 : Fin (W.n + 4)) + k = (i + k) + 1 := by abel
    have e2 : (j + 1 : Fin (W.n + 4)) + k = (j + k) + 1 := by abel
    have g1 : i + k ≠ j + k := fun h => hij ((finShift k).injective h)
    have g2 : (i + k) + 1 ≠ j + k := fun h => hi1j ((finShift k).injective (e1.trans h))
    have g3 : i + k ≠ (j + k) + 1 := fun h => hij1 ((finShift k).injective (h.trans e2.symm))
    rw [e1, e2]
    exact W.simple (i + k) (j + k) g1 g2 g3

theorem rotate_v (k : Fin (W.n + 4)) (i : Fin (W.n + 4)) : (W.rotate k).v i = W.v (i + k) := rfl

theorem rotate_x (k : Fin (W.n + 4)) (i : Fin (W.n + 4)) : (W.rotate k).x i = W.x (i + k) := rfl

theorem rotate_y (k : Fin (W.n + 4)) (i : Fin (W.n + 4)) : (W.rotate k).y i = W.y (i + k) := rfl

theorem rotate_vert (k : Fin (W.n + 4)) (i : Fin (W.n + 4)) :
    (W.rotate k).vert i ↔ W.vert (i + k) := by
  have e : (i + 1 : Fin (W.n + 4)) + k = (i + k) + 1 := by abel
  have hv1 : (W.rotate k).v (i + 1) = W.v ((i + k) + 1) := by rw [rotate_v, e]
  unfold OrthoLoop.vert OrthoLoop.x
  rw [hv1, rotate_v]

theorem rotate_lo (k : Fin (W.n + 4)) (i : Fin (W.n + 4)) :
    (W.rotate k).lo i = W.lo (i + k) := by
  have e : (i + 1 : Fin (W.n + 4)) + k = (i + k) + 1 := by abel
  have hv1 : (W.rotate k).v (i + 1) = W.v ((i + k) + 1) := by rw [rotate_v, e]
  unfold OrthoLoop.lo OrthoLoop.y
  rw [hv1, rotate_v]

theorem rotate_hi (k : Fin (W.n + 4)) (i : Fin (W.n + 4)) :
    (W.rotate k).hi i = W.hi (i + k) := by
  have e : (i + 1 : Fin (W.n + 4)) + k = (i + k) + 1 := by abel
  have hv1 : (W.rotate k).v (i + 1) = W.v ((i + k) + 1) := by rw [rotate_v, e]
  unfold OrthoLoop.hi OrthoLoop.y
  rw [hv1, rotate_v]

theorem rotate_edgePts (k : Fin (W.n + 4)) (i : Fin (W.n + 4)) :
    (W.rotate k).edgePts i = W.edgePts (i + k) := by
  have e : (i + 1 : Fin (W.n + 4)) + k = (i + k) + 1 := by abel
  have hv1 : (W.rotate k).v (i + 1) = W.v ((i + k) + 1) := by rw [rotate_v, e]
  unfold OrthoLoop.edgePts OrthoLoop.mid
  rw [hv1, rotate_v]

theorem rotate_boundary (k : Fin (W.n + 4)) : (W.rotate k).boundary = W.boundary := by
  ext c
  simp only [OrthoLoop.boundary, Finset.mem_biUnion, Finset.mem_univ, true_and, rotate_edgePts]
  constructor
  · rintro ⟨i, h⟩; exact ⟨i + k, h⟩
  · rintro ⟨i, h⟩; exact ⟨i - k, by rwa [show i - k + k = i from by abel]⟩

theorem rotate_p2 (k : Fin (W.n + 4)) (c : Cell) : (W.rotate k).p2 c = W.p2 c := by
  have hc := Equiv.sum_comp (finShift k)
    (fun i => if W.vert i ∧ c.1 < W.x i ∧ W.lo i ≤ c.2 ∧ c.2 < W.hi i then (1 : ZMod 2) else 0)
  simp only [finShift_apply] at hc
  unfold OrthoLoop.p2
  rw [← hc]
  apply Finset.sum_congr rfl
  intro i _
  apply if_congr _ rfl rfl
  have hv : (W.rotate k).vert i ↔ W.vert (i + k) := W.rotate_vert k i
  have hx : (W.rotate k).x i = W.x (i + k) := W.rotate_x k i
  have hl : (W.rotate k).lo i = W.lo (i + k) := W.rotate_lo k i
  have hh : (W.rotate k).hi i = W.hi (i + k) := W.rotate_hi k i
  rw [hx, hl, hh]
  exact and_congr hv (and_congr Iff.rfl (and_congr Iff.rfl Iff.rfl))

theorem rotate_interior (k : Fin (W.n + 4)) : (W.rotate k).interior = W.interior := by
  ext c
  simp only [OrthoLoop.interior, OrthoLoop.inside, rotate_p2, rotate_boundary, Set.mem_setOf_eq]

theorem rotate_I (k : Fin (W.n + 4)) : (W.rotate k).I = W.I := by
  simp only [OrthoLoop.I, rotate_interior]

theorem rotate_T (k : Fin (W.n + 4)) : (W.rotate k).T = W.T := by
  have hc := Equiv.sum_comp (finShift k) (fun i => W.x i * ((W.y (i + 1) - W.y (i - 1)) / 2))
  simp only [finShift_apply] at hc
  unfold OrthoLoop.T
  rw [← hc]
  apply Finset.sum_congr rfl
  intro i _
  have e1 : (i + 1 : Fin (W.n + 4)) + k = (i + k) + 1 := by abel
  have e2 : (i - 1 : Fin (W.n + 4)) + k = (i + k) - 1 := by abel
  have hv1 : (W.rotate k).v (i + 1) = W.v ((i + k) + 1) := by rw [rotate_v, e1]
  have hv2 : (W.rotate k).v (i - 1) = W.v ((i + k) - 1) := by rw [rotate_v, e2]
  unfold OrthoLoop.x OrthoLoop.y
  rw [hv1, hv2, rotate_v]

theorem rotate_L (k : Fin (W.n + 4)) : (W.rotate k).L = W.L := rfl

theorem rotate_P (k : Fin (W.n + 4)) : (W.rotate k).P ↔ W.P := by
  simp only [OrthoLoop.P, rotate_I, rotate_T, rotate_L]

theorem rotate_image_x (k : Fin (W.n + 4)) : (univ.image (W.rotate k).x) = univ.image W.x := by
  have h : (univ.image fun i => W.x (i + k)) = univ.image W.x := image_univ_equiv (finShift k) W.x
  rw [← h]

theorem rotate_image_y (k : Fin (W.n + 4)) : (univ.image (W.rotate k).y) = univ.image W.y := by
  have h : (univ.image fun i => W.y (i + k)) = univ.image W.y := image_univ_equiv (finShift k) W.y
  rw [← h]

theorem rotate_maxX (k : Fin (W.n + 4)) : (W.rotate k).maxX = W.maxX := by
  simp only [OrthoLoop.maxX, rotate_image_x]

theorem rotate_minX (k : Fin (W.n + 4)) : (W.rotate k).minX = W.minX := by
  simp only [OrthoLoop.minX, rotate_image_x]

theorem rotate_maxY (k : Fin (W.n + 4)) : (W.rotate k).maxY = W.maxY := by
  simp only [OrthoLoop.maxY, rotate_image_y]

theorem rotate_minY (k : Fin (W.n + 4)) : (W.rotate k).minY = W.minY := by
  simp only [OrthoLoop.minY, rotate_image_y]

/-! ### Reversal -/

/-- Reversal of the traversal direction. -/
abbrev reverse : OrthoLoop where
  a := W.a
  b := W.b
  n := W.n
  v := fun i => W.v (-i)
  inj := W.inj.comp finNeg.injective
  step := fun i => by
    have e : (-(i + 1 : Fin (W.n + 4))) + 1 = -i := by abel
    have h := W.step (-(i + 1))
    rw [e] at h
    rcases h with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exact Or.inr (Or.inl ⟨hx.symm, by omega⟩)
    · exact Or.inl ⟨hx.symm, by omega⟩
    · exact Or.inr (Or.inr (Or.inr ⟨by omega, hy.symm⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨by omega, hy.symm⟩))
  par := fun i => W.par (-i)
  simple := fun i j hij hi1j hij1 => by
    have e1 : (-(i + 1 : Fin (W.n + 4))) + 1 = -i := by abel
    have e2 : (-(j + 1 : Fin (W.n + 4))) + 1 = -j := by abel
    have hD : Disjoint (W.edgePts (-(i + 1))) (W.edgePts (-(j + 1))) := by
      apply W.simple
      · intro h
        apply hij
        have h2 : -(i + 1) + 1 = -(j + 1) + 1 := by rw [h]
        rw [e1, e2] at h2
        exact finNeg.injective h2
      · rw [e1]
        intro h
        apply hij1
        exact finNeg.injective h
      · rw [e2]
        intro h
        apply hi1j
        exact finNeg.injective h
    rw [← e1, ← e2, edgePts_rev W (-(i + 1)), edgePts_rev W (-(j + 1))]
    exact hD

theorem reverse_v (i : Fin (W.n + 4)) : W.reverse.v i = W.v (-i) := rfl

theorem reverse_x (i : Fin (W.n + 4)) : W.reverse.x i = W.x (-i) := rfl

theorem reverse_y (i : Fin (W.n + 4)) : W.reverse.y i = W.y (-i) := rfl

theorem reverse_vert (i : Fin (W.n + 4)) : W.reverse.vert i ↔ W.vert (-(i + 1)) := by
  have e : (-(i + 1 : Fin (W.n + 4))) + 1 = -i := by abel
  unfold OrthoLoop.vert OrthoLoop.x
  rw [reverse_v, reverse_v, e]
  exact eq_comm

theorem reverse_lo (i : Fin (W.n + 4)) : W.reverse.lo i = W.lo (-(i + 1)) := by
  have e : (-(i + 1 : Fin (W.n + 4))) + 1 = -i := by abel
  unfold OrthoLoop.lo OrthoLoop.y
  rw [reverse_v, reverse_v, e, min_comm]

theorem reverse_hi (i : Fin (W.n + 4)) : W.reverse.hi i = W.hi (-(i + 1)) := by
  have e : (-(i + 1 : Fin (W.n + 4))) + 1 = -i := by abel
  unfold OrthoLoop.hi OrthoLoop.y
  rw [reverse_v, reverse_v, e, max_comm]

theorem reverse_mid (i : Fin (W.n + 4)) : W.reverse.mid i = W.mid (-(i + 1)) := by
  have e : (-(i + 1 : Fin (W.n + 4))) + 1 = -i := by abel
  unfold OrthoLoop.mid
  rw [reverse_v, reverse_v, e, midPt_comm]

theorem reverse_edgePts (i : Fin (W.n + 4)) : W.reverse.edgePts i = W.edgePts (-(i + 1)) := by
  have e : (-(i + 1 : Fin (W.n + 4))) + 1 = -i := by abel
  unfold OrthoLoop.edgePts OrthoLoop.mid
  rw [reverse_v, reverse_v, e, midPt_comm]
  ext c
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

theorem reverse_boundary : W.reverse.boundary = W.boundary := by
  ext c
  simp only [OrthoLoop.boundary, Finset.mem_biUnion, Finset.mem_univ, true_and, reverse_edgePts]
  constructor
  · rintro ⟨i, h⟩; exact ⟨-(i + 1), h⟩
  · rintro ⟨i, h⟩
    exact ⟨-(i + 1), by
      have e : (-(-(i + 1) + 1 : Fin (W.n + 4))) = i := by
        have e1 : (-(i + 1 : Fin (W.n + 4))) + 1 = -i := by abel
        rw [e1]; abel
      rwa [e]⟩

theorem reverse_p2 (c : Cell) : W.reverse.p2 c = W.p2 c := by
  have hterm : ∀ i : Fin (W.n + 4),
      (if W.reverse.vert i ∧ c.1 < W.reverse.x i ∧ W.reverse.lo i ≤ c.2 ∧ c.2 < W.reverse.hi i
        then (1 : ZMod 2) else 0) =
      (if W.vert (-(i + 1)) ∧ c.1 < W.x (-(i + 1)) ∧ W.lo (-(i + 1)) ≤ c.2 ∧ c.2 < W.hi (-(i + 1))
        then 1 else 0) := by
    intro i
    have hv : W.reverse.vert i ↔ W.vert (-(i + 1)) := W.reverse_vert i
    have hl : W.reverse.lo i = W.lo (-(i + 1)) := W.reverse_lo i
    have hh : W.reverse.hi i = W.hi (-(i + 1)) := W.reverse_hi i
    apply if_congr _ rfl rfl
    rw [hv, hl, hh]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨h1, ?_, h3, h4⟩
      have e1 : (-(i + 1 : Fin (W.n + 4))) + 1 = -i := by abel
      have h1' : W.x ((-(i + 1 : Fin (W.n + 4))) + 1) = W.x (-(i + 1)) := h1
      rw [e1] at h1'
      have h2' : c.1 < W.x (-i) := h2
      rwa [h1'] at h2'
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨h1, ?_, h3, h4⟩
      have e1 : (-(i + 1 : Fin (W.n + 4))) + 1 = -i := by abel
      have h1' : W.x ((-(i + 1 : Fin (W.n + 4))) + 1) = W.x (-(i + 1)) := h1
      rw [e1] at h1'
      show c.1 < W.x (-i)
      rwa [h1']
  have hc := Equiv.sum_comp finNegShift
    (fun i => if W.vert i ∧ c.1 < W.x i ∧ W.lo i ≤ c.2 ∧ c.2 < W.hi i then (1 : ZMod 2) else 0)
  simp only [finNegShift_apply] at hc
  unfold OrthoLoop.p2
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  exact hc

theorem reverse_interior : W.reverse.interior = W.interior := by
  ext c
  simp only [OrthoLoop.interior, OrthoLoop.inside, reverse_p2, reverse_boundary, Set.mem_setOf_eq]

theorem reverse_I : W.reverse.I = W.I := by
  simp only [OrthoLoop.I, reverse_interior]

theorem reverse_T : W.reverse.T = -W.T := by
  have e1 : ∀ i : Fin (W.n + 4), -(i + 1 : Fin (W.n + 4)) = -i - 1 := fun i => by abel
  have e2 : ∀ i : Fin (W.n + 4), -(i - 1 : Fin (W.n + 4)) = -i + 1 := fun i => by abel
  have hterm : ∀ i : Fin (W.n + 4),
      W.reverse.x i * ((W.reverse.y (i + 1) - W.reverse.y (i - 1)) / 2) =
      -(W.x (-i) * ((W.y ((-i) + 1) - W.y ((-i) - 1)) / 2)) := by
    intro i
    simp only [OrthoLoop.x, OrthoLoop.y, reverse_v, e1 i, e2 i]
    have hev : Even ((W.v (-i + 1)).2 - (W.v (-i - 1)).2) := by
      have h1 : ((W.v (-i + 1)).2 : ZMod 2) = W.b := W.parY _
      have h2 : ((W.v (-i - 1)).2 : ZMod 2) = W.b := W.parY _
      rw [even_iff_two_dvd]
      have hz : (((W.v (-i + 1)).2 - (W.v (-i - 1)).2 : ℤ) : ZMod 2) = 0 := by
        rw [Int.cast_sub, h1, h2, sub_self]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
    obtain ⟨t, ht⟩ := hev
    have h2 : ((W.v (-i - 1)).2 - (W.v (-i + 1)).2) / 2 =
        -(((W.v (-i + 1)).2 - (W.v (-i - 1)).2) / 2) := by omega
    rw [h2, mul_neg]
  rw [OrthoLoop.T, Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_neg_distrib]
  rw [show -W.T = -(∑ i : Fin (W.n + 4), W.x i * ((W.y (i + 1) - W.y (i - 1)) / 2)) from rfl]
  congr 1
  have hc := Equiv.sum_comp finNeg (fun i => W.x i * ((W.y (i + 1) - W.y (i - 1)) / 2))
  simp only [finNeg_apply] at hc
  exact hc

theorem reverse_L : W.reverse.L = W.L := rfl

theorem reverse_P : W.reverse.P ↔ W.P := by
  have hT : (W.reverse.T : ZMod 2) = (W.T : ZMod 2) := by
    rw [reverse_T]
    push_cast
    have hneg : ∀ x : ZMod 2, -x = x := by decide
    rw [hneg]
  simp only [OrthoLoop.P, reverse_I, reverse_L, hT]

theorem reverse_image_x : (univ.image W.reverse.x) = univ.image W.x := by
  have h : (univ.image fun i => W.x (-i)) = univ.image W.x := image_univ_equiv finNeg W.x
  rw [← h]

theorem reverse_image_y : (univ.image W.reverse.y) = univ.image W.y := by
  have h : (univ.image fun i => W.y (-i)) = univ.image W.y := image_univ_equiv finNeg W.y
  rw [← h]

theorem reverse_maxX : W.reverse.maxX = W.maxX := by
  simp only [OrthoLoop.maxX, reverse_image_x]

theorem reverse_minX : W.reverse.minX = W.minX := by
  simp only [OrthoLoop.minX, reverse_image_x]

theorem reverse_maxY : W.reverse.maxY = W.maxY := by
  simp only [OrthoLoop.maxY, reverse_image_y]

theorem reverse_minY : W.reverse.minY = W.minY := by
  simp only [OrthoLoop.minY, reverse_image_y]

/-! ### The topmost-leftmost vertex -/

theorem exists_top_left : ∃ i₀ : Fin (W.n + 4),
    W.y i₀ = W.maxY ∧ ∀ j : Fin (W.n + 4), W.y j = W.maxY → W.x i₀ ≤ W.x j := by
  classical
  obtain ⟨i₀, hi₀⟩ := W.exists_y_eq_maxY
  let s := univ.filter fun i => W.y i = W.maxY
  have hs : s.Nonempty := ⟨i₀, mem_filter.mpr ⟨mem_univ i₀, hi₀⟩⟩
  obtain ⟨i₁, hi₁, hxi₁⟩ : ∃ i₁ ∈ s, W.x i₁ = (s.image W.x).min' (Finset.Nonempty.image hs W.x) := by
    have h := (s.image W.x).min'_mem (Finset.Nonempty.image hs W.x)
    rw [mem_image] at h
    exact h
  rw [mem_filter] at hi₁
  exact ⟨i₁, hi₁.2, fun j hj => by
    have hle : W.x i₁ ≤ W.x j := by
      rw [hxi₁]
      exact Finset.min'_le _ _ (mem_image_of_mem W.x (mem_filter.mpr ⟨mem_univ j, hj⟩))
    exact hle⟩

end OrthoLoop

/-! ### Small Fin arithmetic helpers -/

theorem val_zero_fin {n : ℕ} : ((0 : Fin (n + 4)) : ℕ) = 0 := by simp

theorem val_one_fin {n : ℕ} : ((1 : Fin (n + 4)) : ℕ) = 1 := by simp

theorem val_two_fin {n : ℕ} : ((2 : Fin (n + 4)) : ℕ) = 2 := by simp

theorem val_three_fin {n : ℕ} : ((3 : Fin (n + 4)) : ℕ) = 3 := by simp

theorem val_neg_one_fin {n : ℕ} : ((-1 : Fin (n + 4)) : ℕ) = n + 3 := by
  have hne : (1 : Fin (n + 4)) ≠ 0 := by
    intro h0
    have hv := congrArg Fin.val h0
    rw [val_one_fin] at hv
    simp at hv
  rw [Fin.val_neg, val_one_fin, if_neg hne]
  omega

theorem val_neg_two_fin {n : ℕ} : ((-2 : Fin (n + 4)) : ℕ) = n + 2 := by
  have hne : (2 : Fin (n + 4)) ≠ 0 := by
    intro h0
    have hv := congrArg Fin.val h0
    rw [val_two_fin] at hv
    simp at hv
  rw [Fin.val_neg, val_two_fin, if_neg hne]
  omega

theorem two_ne_zero_fin {n : ℕ} : (2 : Fin (n + 4)) ≠ 0 := by
  intro h
  have hv := congrArg Fin.val h
  rw [val_two_fin] at hv
  simp at hv

theorem one_ne_neg_one {n : ℕ} : (1 : Fin (n + 4)) ≠ -1 := by
  intro h
  have hv := congrArg Fin.val h
  rw [val_one_fin, val_neg_one_fin] at hv
  omega

theorem n_eq_zero_of_two_eq_neg_two {n : ℕ} (h : (2 : Fin (n + 4)) = -2) : n = 0 := by
  have hv := congrArg Fin.val h
  rw [val_two_fin, val_neg_two_fin] at hv
  omega

theorem three_ne_zero_fin {n : ℕ} : (3 : Fin (n + 4)) ≠ 0 := by
  intro h
  have hv := congrArg Fin.val h
  rw [val_three_fin] at hv
  simp at hv

theorem one_ne_two_fin {n : ℕ} : (1 : Fin (n + 4)) ≠ 2 := by
  intro h
  have hv := congrArg Fin.val h
  rw [val_one_fin, val_two_fin] at hv
  omega

theorem one_ne_three_fin {n : ℕ} : (1 : Fin (n + 4)) ≠ 3 := by
  intro h
  have hv := congrArg Fin.val h
  rw [val_one_fin, val_three_fin] at hv
  omega

theorem two_ne_three_fin {n : ℕ} : (2 : Fin (n + 4)) ≠ 3 := by
  intro h
  have hv := congrArg Fin.val h
  rw [val_two_fin, val_three_fin] at hv
  omega

theorem three_ne_one_fin {n : ℕ} : (3 : Fin (n + 4)) ≠ 1 := by
  intro h
  have hv := congrArg Fin.val h
  rw [val_three_fin, val_one_fin] at hv
  omega

namespace OrthoLoop

variable (W : OrthoLoop)

/-! ### The four surgery lemmas (proved in later sections) -/


/-- The vertex index type is exactly `{0,1,2,3}` when `n = 0`. -/
theorem univ_fin4' (W : OrthoLoop) (hn : W.n = 0) :
    (univ : Finset (Fin (W.n + 4))) = {0, 1, 2, 3} := by
  ext i
  simp only [mem_univ, mem_insert, mem_singleton, true_iff]
  have hi := i.isLt
  have hi4 : (i : ℕ) < 4 := by omega
  have hc : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3 := by omega
  rcases hc with h | h | h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext (by rw [h, val_one_fin])))
  · exact Or.inr (Or.inr (Or.inl (Fin.ext (by rw [h, val_two_fin]))))
  · exact Or.inr (Or.inr (Or.inr (Fin.ext (by rw [h, val_three_fin]))))

theorem sum_fin4' (W : OrthoLoop) (hn : W.n = 0) {M : Type*} [AddCommMonoid M]
    (f : Fin (W.n + 4) → M) : ∑ i : Fin (W.n + 4), f i = f 0 + f 1 + f 2 + f 3 := by
  rw [univ_fin4' W hn]
  rw [Finset.sum_insert (by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    push_neg
    refine ⟨?_, ?_, ?_⟩ <;>
      · intro h; have hv := congrArg Fin.val h
        simp only [val_zero_fin, val_one_fin, val_two_fin, val_three_fin] at hv
        omega),
    Finset.sum_insert (by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    push_neg
    refine ⟨?_, ?_⟩ <;>
      · intro h; have hv := congrArg Fin.val h
        simp only [val_zero_fin, val_one_fin, val_two_fin, val_three_fin] at hv
        omega),
    Finset.sum_insert (by
    simp only [Finset.mem_singleton]
    intro h; have hv := congrArg Fin.val h
    simp only [val_zero_fin, val_one_fin, val_two_fin, val_three_fin] at hv
    omega),
    Finset.sum_singleton]
  abel

theorem image_fin4' (W : OrthoLoop) (hn : W.n = 0) {M : Type*} [DecidableEq M]
    (f : Fin (W.n + 4) → M) : (univ.image f) = {f 0, f 1, f 2, f 3} := by
  rw [univ_fin4' W hn]
  simp [Finset.image_insert]

theorem maxX_fin4 (W : OrthoLoop) (hn : W.n = 0) :
    W.maxX = max (max (W.x 0) (W.x 1)) (max (W.x 2) (W.x 3)) := by
  unfold OrthoLoop.maxX
  apply le_antisymm
  · apply Finset.max'_le
    intro z hz
    rw [image_fin4' W hn] at hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl <;> simp
  · have h0 : W.x 0 ≤ (univ.image W.x).max' _ :=
      Finset.le_max' _ _ (mem_image_of_mem _ (mem_univ 0))
    have h1 : W.x 1 ≤ (univ.image W.x).max' _ :=
      Finset.le_max' _ _ (mem_image_of_mem _ (mem_univ 1))
    have h2 : W.x 2 ≤ (univ.image W.x).max' _ :=
      Finset.le_max' _ _ (mem_image_of_mem _ (mem_univ 2))
    have h3 : W.x 3 ≤ (univ.image W.x).max' _ :=
      Finset.le_max' _ _ (mem_image_of_mem _ (mem_univ 3))
    omega

theorem minX_fin4 (W : OrthoLoop) (hn : W.n = 0) :
    W.minX = min (min (W.x 0) (W.x 1)) (min (W.x 2) (W.x 3)) := by
  unfold OrthoLoop.minX
  apply le_antisymm
  · have h0 : (univ.image W.x).min' _ ≤ W.x 0 :=
      Finset.min'_le _ _ (mem_image_of_mem _ (mem_univ 0))
    have h1 : (univ.image W.x).min' _ ≤ W.x 1 :=
      Finset.min'_le _ _ (mem_image_of_mem _ (mem_univ 1))
    have h2 : (univ.image W.x).min' _ ≤ W.x 2 :=
      Finset.min'_le _ _ (mem_image_of_mem _ (mem_univ 2))
    have h3 : (univ.image W.x).min' _ ≤ W.x 3 :=
      Finset.min'_le _ _ (mem_image_of_mem _ (mem_univ 3))
    omega
  · apply Finset.le_min'
    intro z hz
    rw [image_fin4' W hn] at hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl <;> simp

theorem maxY_fin4 (W : OrthoLoop) (hn : W.n = 0) :
    W.maxY = max (max (W.y 0) (W.y 1)) (max (W.y 2) (W.y 3)) := by
  unfold OrthoLoop.maxY
  apply le_antisymm
  · apply Finset.max'_le
    intro z hz
    rw [image_fin4' W hn] at hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl <;> simp
  · have h0 : W.y 0 ≤ (univ.image W.y).max' _ :=
      Finset.le_max' _ _ (mem_image_of_mem _ (mem_univ 0))
    have h1 : W.y 1 ≤ (univ.image W.y).max' _ :=
      Finset.le_max' _ _ (mem_image_of_mem _ (mem_univ 1))
    have h2 : W.y 2 ≤ (univ.image W.y).max' _ :=
      Finset.le_max' _ _ (mem_image_of_mem _ (mem_univ 2))
    have h3 : W.y 3 ≤ (univ.image W.y).max' _ :=
      Finset.le_max' _ _ (mem_image_of_mem _ (mem_univ 3))
    omega

theorem minY_fin4 (W : OrthoLoop) (hn : W.n = 0) :
    W.minY = min (min (W.y 0) (W.y 1)) (min (W.y 2) (W.y 3)) := by
  unfold OrthoLoop.minY
  apply le_antisymm
  · have h0 : (univ.image W.y).min' _ ≤ W.y 0 :=
      Finset.min'_le _ _ (mem_image_of_mem _ (mem_univ 0))
    have h1 : (univ.image W.y).min' _ ≤ W.y 1 :=
      Finset.min'_le _ _ (mem_image_of_mem _ (mem_univ 1))
    have h2 : (univ.image W.y).min' _ ≤ W.y 2 :=
      Finset.min'_le _ _ (mem_image_of_mem _ (mem_univ 2))
    have h3 : (univ.image W.y).min' _ ≤ W.y 3 :=
      Finset.min'_le _ _ (mem_image_of_mem _ (mem_univ 3))
    omega
  · apply Finset.le_min'
    intro z hz
    rw [image_fin4' W hn] at hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl <;> simp

theorem square_interior_norm (W : OrthoLoop) (hn : W.n = 0) (x₀ y₀ sx sy : ℤ)
    (hsx : sx = 1 ∨ sx = -1) (hsy : sy = 1 ∨ sy = -1)
    (hv0 : W.v 0 = (x₀, y₀)) (hv1 : W.v 1 = (x₀ + 2 * sx, y₀))
    (hv2 : W.v 2 = (x₀ + 2 * sx, y₀ + 2 * sy)) (hv3 : W.v 3 = (x₀, y₀ + 2 * sy)) :
    (W.I : ZMod 2) = 1 := by
  classical
  have e01 : (0 + 1 : Fin (W.n + 4)) = 1 := by abel
  have e11 : (1 + 1 : Fin (W.n + 4)) = 2 := by abel
  have e21 : (2 + 1 : Fin (W.n + 4)) = 3 := by abel
  have e30 : (3 + 1 : Fin (W.n + 4)) = 0 := by rw [hn]; decide
  -- bounding box is 2×2
  have hminX : W.minX = x₀ + sx - 1 := by
    have h1 := minX_fin4 W hn
    simp only [OrthoLoop.x, hv0, hv1, hv2, hv3] at h1
    rcases hsx with hsx | hsx <;> omega
  have hmaxX : W.maxX = x₀ + sx + 1 := by
    have h1 := maxX_fin4 W hn
    simp only [OrthoLoop.x, hv0, hv1, hv2, hv3] at h1
    rcases hsx with hsx | hsx <;> omega
  have hminY : W.minY = y₀ + sy - 1 := by
    have h1 := minY_fin4 W hn
    simp only [OrthoLoop.y, hv0, hv1, hv2, hv3] at h1
    rcases hsy with hsy | hsy <;> omega
  have hmaxY : W.maxY = y₀ + sy + 1 := by
    have h1 := maxY_fin4 W hn
    simp only [OrthoLoop.y, hv0, hv1, hv2, hv3] at h1
    rcases hsy with hsy | hsy <;> omega
  have hDx : W.maxX = W.minX + 2 := by
    rcases hsx with hsx | hsx <;> omega
  have hDy : W.maxY = W.minY + 2 := by
    rcases hsy with hsy | hsy <;> omega
  -- the four cells of the box all have crossing parity 1
  have hp2 : ∀ c : Cell, (c.1 = W.minX ∨ c.1 = W.minX + 1) →
      (c.2 = W.minY ∨ c.2 = W.minY + 1) → W.p2 c = 1 := by
    intro c hx hy
    rw [OrthoLoop.p2, sum_fin4' W hn]
    -- edge 0 (v0→v1): horizontal
    have g0 : (if W.vert 0 ∧ c.1 < W.x 0 ∧ W.lo 0 ≤ c.2 ∧ c.2 < W.hi 0 then (1 : ZMod 2) else 0) = 0 := by
      rw [if_neg]
      rintro ⟨hv, -, -, -⟩
      have h : (W.v 1).1 = (W.v 0).1 := hv
      rw [hv1, hv0] at h
      simp at h
      rcases hsx with hsx | hsx <;> omega
    -- edge 2 (v2→v3): horizontal
    have g2 : (if W.vert 2 ∧ c.1 < W.x 2 ∧ W.lo 2 ≤ c.2 ∧ c.2 < W.hi 2 then (1 : ZMod 2) else 0) = 0 := by
      rw [if_neg]
      rintro ⟨hv, -, -, -⟩
      have h : (W.v 3).1 = (W.v 2).1 := hv
      rw [hv3, hv2] at h
      simp at h
      rcases hsx with hsx | hsx <;> omega
    -- edge 1 (v1→v2): vertical at x₀ + 2sx, y-range [minY, minY+2)
    have g1 : (if W.vert 1 ∧ c.1 < W.x 1 ∧ W.lo 1 ≤ c.2 ∧ c.2 < W.hi 1 then (1 : ZMod 2) else 0) =
        (if c.1 < x₀ + 2 * sx then (1 : ZMod 2) else 0) := by
      apply if_congr _ rfl rfl
      have hlo : W.lo 1 = W.minY := by
        show min (W.y 1) (W.y 2) = W.minY
        simp only [OrthoLoop.y, hv1, hv2]
        rw [hminY]
        rcases hsy with hsy | hsy <;> omega
      have hhi : W.hi 1 = W.minY + 2 := by
        show max (W.y 1) (W.y 2) = W.minY + 2
        simp only [OrthoLoop.y, hv1, hv2]
        rw [hminY]
        rcases hsy with hsy | hsy <;> omega
      have hvert : W.vert 1 := by
        show (W.v 2).1 = (W.v 1).1
        rw [hv2, hv1]
      rw [hlo, hhi]
      constructor
      · rintro ⟨-, h2, -, -⟩
        have h2' : c.1 < (W.v 1).1 := h2
        rwa [hv1] at h2'
      · intro h2
        refine ⟨hvert, ?_, ?_, ?_⟩
        · show c.1 < (W.v 1).1
          rw [hv1]
          exact h2
        · rcases hy with hy | hy <;> omega
        · rcases hy with hy | hy <;> omega
    -- edge 3 (v3→v0): vertical at x₀, y-range [minY, minY+2)
    have g3 : (if W.vert 3 ∧ c.1 < W.x 3 ∧ W.lo 3 ≤ c.2 ∧ c.2 < W.hi 3 then (1 : ZMod 2) else 0) =
        (if c.1 < x₀ then (1 : ZMod 2) else 0) := by
      apply if_congr _ rfl rfl
      have hlo : W.lo 3 = W.minY := by
        show min (W.y 3) (W.y (3 + 1)) = W.minY
        rw [e30]
        simp only [OrthoLoop.y, hv3, hv0]
        rw [hminY]
        rcases hsy with hsy | hsy <;> omega
      have hhi : W.hi 3 = W.minY + 2 := by
        show max (W.y 3) (W.y (3 + 1)) = W.minY + 2
        rw [e30]
        simp only [OrthoLoop.y, hv3, hv0]
        rw [hminY]
        rcases hsy with hsy | hsy <;> omega
      have hvert : W.vert 3 := by
        show (W.v (3 + 1)).1 = (W.v 3).1
        rw [e30, hv0, hv3]
      rw [hlo, hhi]
      constructor
      · rintro ⟨-, h2, -, -⟩
        have h2' : c.1 < (W.v 3).1 := h2
        rwa [hv3] at h2'
      · intro h2
        refine ⟨hvert, ?_, ?_, ?_⟩
        · show c.1 < (W.v 3).1
          rw [hv3]
          exact h2
        · rcases hy with hy | hy <;> omega
        · rcases hy with hy | hy <;> omega
    rw [g0, g2, g1, g3]
    -- exactly one of the two vertical edges lies strictly right of c
    have hcx : c.1 < x₀ + 2 * sx ∨ c.1 < x₀ := by
      rcases hx with hx | hx <;> rcases hsx with hsx | hsx <;> omega
    have hnx : ¬ (c.1 < x₀ + 2 * sx ∧ c.1 < x₀) := by
      rintro ⟨h1, h2⟩
      rcases hsx with hsx | hsx <;> rcases hx with hx | hx <;> omega
    by_cases hA : c.1 < x₀ + 2 * sx <;> by_cases hB : c.1 < x₀ <;>
      simp [hA, hB] <;> tauto
  -- the boundary consists of the 4 corners and 4 side midpoints
  have hbd : W.boundary = {(x₀, y₀), (x₀ + 2 * sx, y₀), (x₀ + 2 * sx, y₀ + 2 * sy),
      (x₀, y₀ + 2 * sy), (x₀ + sx, y₀), (x₀ + 2 * sx, y₀ + sy), (x₀ + sx, y₀ + 2 * sy),
      (x₀, y₀ + sy)} := by
    ext c
    rw [W.mem_boundary]
    constructor
    · rintro (⟨i, hi⟩ | ⟨i, hi⟩)
      · have hu := univ_fin4' W hn
        have hmem : i ∈ ({0, 1, 2, 3} : Finset (Fin (W.n + 4))) := by rw [← hu]; exact mem_univ i
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
        rcases hmem with rfl | rfl | rfl | rfl
        · rw [← hi, hv0]; simp
        · rw [← hi, hv1]; simp
        · rw [← hi, hv2]; simp
        · rw [← hi, hv3]; simp
      · have hu := univ_fin4' W hn
        have : i ∈ ({0, 1, 2, 3} : Finset (Fin (W.n + 4))) := by rw [← hu]; exact mem_univ i
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with rfl | rfl | rfl | rfl
        · -- mid 0 = (x₀ + sx, y₀)
          have hm : W.mid 0 = (x₀ + sx, y₀) := by
            show midPt (W.v 0) (W.v (0 + 1)) = (x₀ + sx, y₀)
            rw [e01, hv0, hv1]
            simp [midPt]
            constructor <;> omega
          rw [← hi, hm]
          simp
        · have hm : W.mid 1 = (x₀ + 2 * sx, y₀ + sy) := by
            show midPt (W.v 1) (W.v (1 + 1)) = (x₀ + 2 * sx, y₀ + sy)
            rw [e11, hv1, hv2]
            simp [midPt]
            constructor <;> omega
          rw [← hi, hm]
          simp
        · have hm : W.mid 2 = (x₀ + sx, y₀ + 2 * sy) := by
            show midPt (W.v 2) (W.v (2 + 1)) = (x₀ + sx, y₀ + 2 * sy)
            rw [e21, hv2, hv3]
            simp [midPt]
            constructor <;> omega
          rw [← hi, hm]
          simp
        · have hm : W.mid 3 = (x₀, y₀ + sy) := by
            show midPt (W.v 3) (W.v (3 + 1)) = (x₀, y₀ + sy)
            rw [e30, hv3, hv0]
            simp [midPt]
            constructor <;> omega
          rw [← hi, hm]
          simp
    · intro hc
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inl ⟨0, hv0⟩
      · exact Or.inl ⟨1, hv1⟩
      · exact Or.inl ⟨2, hv2⟩
      · exact Or.inl ⟨3, hv3⟩
      · right
        refine ⟨0, ?_⟩
        show midPt (W.v 0) (W.v (0 + 1)) = (x₀ + sx, y₀)
        rw [e01, hv0, hv1]
        simp [midPt]
        constructor <;> omega
      · right
        refine ⟨1, ?_⟩
        show midPt (W.v 1) (W.v (1 + 1)) = (x₀ + 2 * sx, y₀ + sy)
        rw [e11, hv1, hv2]
        simp [midPt]
        constructor <;> omega
      · right
        refine ⟨2, ?_⟩
        show midPt (W.v 2) (W.v (2 + 1)) = (x₀ + sx, y₀ + 2 * sy)
        rw [e21, hv2, hv3]
        simp [midPt]
        constructor <;> omega
      · right
        refine ⟨3, ?_⟩
        show midPt (W.v 3) (W.v (3 + 1)) = (x₀, y₀ + sy)
        rw [e30, hv3, hv0]
        simp [midPt]
        constructor <;> omega
  -- the box has exactly 4 cells
  have hbox : W.box = ({W.minX, W.minX + 1} ×ˢ {W.minY, W.minY + 1} : Finset Cell) := by
    unfold OrthoLoop.box
    rw [hDx, hDy]
    ext ⟨a, b⟩
    simp only [Finset.mem_product, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton,
      Prod.mk.injEq]
    constructor
    · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
      have ha : a = W.minX ∨ a = W.minX + 1 := by omega
      have hb : b = W.minY ∨ b = W.minY + 1 := by omega
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
        simp <;> omega
  -- the interior is exactly the center
  have hfilter : (W.box.filter fun c => W.p2 c = 1 ∧ c ∉ W.boundary) =
      {(W.minX + 1, W.minY + 1)} := by
    rw [hbox]
    ext c
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_insert, Finset.mem_singleton,
      Prod.mk.injEq]
    constructor
    · rintro ⟨⟨hx, hy⟩, hp, hb⟩
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · -- (minX, minY): the (-sx,-sy)-corner, on boundary
        exfalso
        apply hb
        rw [hbd]
        have hmc : c = (W.minX, W.minY) := Prod.ext hx hy
        rw [hmc, hminX, hminY]
        rcases hsx with hsx | hsx <;> rcases hsy with hsy | hsy <;>
          simp only [hsx, hsy, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] <;> omega
      · -- (minX, minY+1): vertical side midpoint, on boundary
        exfalso
        apply hb
        rw [hbd]
        have hmc : c = (W.minX, W.minY + 1) := Prod.ext hx hy
        rw [hmc, hminX, hminY]
        rcases hsx with hsx | hsx <;> rcases hsy with hsy | hsy <;>
          simp only [hsx, hsy, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] <;> omega
      · -- (minX+1, minY): horizontal side midpoint, on boundary
        exfalso
        apply hb
        rw [hbd]
        have hmc : c = (W.minX + 1, W.minY) := Prod.ext hx hy
        rw [hmc, hminX, hminY]
        rcases hsx with hsx | hsx <;> rcases hsy with hsy | hsy <;>
          simp only [hsx, hsy, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] <;> omega
      · exact Prod.ext hx hy
    · rintro ⟨rfl, rfl⟩
      refine ⟨⟨by right; rfl, by right; rfl⟩, hp2 _ (Or.inr rfl) (Or.inr rfl), ?_⟩
      rw [hbd]
      simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
      push_neg
      have hmx : W.minX + 1 = x₀ + sx := by
        rw [hminX]
        rcases hsx with hsx | hsx <;> omega
      have hmy : W.minY + 1 = y₀ + sy := by
        rw [hminY]
        rcases hsy with hsy | hsy <;> omega
      rw [hmx, hmy]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        · rcases hsx with hsx | hsx <;> rcases hsy with hsy | hsy <;>
            simp only [hsx, hsy, Prod.mk.injEq] <;> try omega
  rw [I_eq, hfilter]
  rw [Finset.card_singleton, Nat.cast_one]


/-! ### Shared surgery infrastructure -/

/-- Shoelace in edge form: `2T = Σᵢ (xᵢ yᵢ₊₁ − xᵢ₊₁ yᵢ)`. -/
theorem two_mul_T : 2 * W.T = ∑ i : Fin (W.n + 4), (W.x i * W.y (i + 1) - W.x (i + 1) * W.y i) := by
  classical
  have hev : ∀ i : Fin (W.n + 4), Even (W.y (i + 1) - W.y (i - 1)) := by
    intro i
    have h1 : (W.y (i + 1) : ZMod 2) = W.b := W.parY (i + 1)
    have h2 : (W.y (i - 1) : ZMod 2) = W.b := W.parY (i - 1)
    rw [even_iff_two_dvd]
    have hz : (((W.y (i + 1) - W.y (i - 1)) : ℤ) : ZMod 2) = 0 := by
      rw [Int.cast_sub, h1, h2, sub_self]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
  have h1 : 2 * W.T = ∑ i : Fin (W.n + 4), W.x i * (W.y (i + 1) - W.y (i - 1)) := by
    rw [OrthoLoop.T, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have h2 : 2 * (W.x i * ((W.y (i + 1) - W.y (i - 1)) / 2)) =
        W.x i * (2 * ((W.y (i + 1) - W.y (i - 1)) / 2)) := by ring
    rw [h2, Int.two_mul_ediv_two_of_even (hev i)]
  rw [h1]
  have h3 : ∑ i : Fin (W.n + 4), W.x (i + 1) * W.y i = ∑ i : Fin (W.n + 4), W.x i * W.y (i - 1) := by
    have hc := Equiv.sum_comp (finRotate (W.n + 4)) (fun i => W.x i * W.y (i - 1))
    simp only [finRotate_apply] at hc
    rw [← hc]
    apply Finset.sum_congr rfl
    intro i _
    have e : ((i : Fin (W.n + 4)) + 1) - 1 = i := by abel
    rw [e]
  have h4 : ∑ i : Fin (W.n + 4), W.x i * (W.y (i + 1) - W.y (i - 1)) =
      ∑ i : Fin (W.n + 4), (W.x i * W.y (i + 1) - W.x i * W.y (i - 1)) := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [h4, Finset.sum_sub_distrib, ← h3, ← Finset.sum_sub_distrib]

/-- Band equality: crossing parity is the same at levels `h` and `h+1` when
`h` is in the vertex parity class. -/
theorem p2_band (a h : ℤ) (hh : (h : ZMod 2) = W.b) :
    W.p2 (a, h) = W.p2 (a, h + 1) := by
  classical
  have hiff : ∀ i : Fin (W.n + 4),
      (W.vert i ∧ a < W.x i ∧ W.lo i ≤ h ∧ h < W.hi i) ↔
      (W.vert i ∧ a < W.x i ∧ W.lo i ≤ h + 1 ∧ h + 1 < W.hi i) := by
    intro i
    by_cases hv : W.vert i
    · rcases W.vert_cases i hv with hy | hy
      · have hlo : W.lo i = W.y i := by
          show min (W.y i) (W.y (i + 1)) = W.y i
          rw [hy]; exact min_eq_left (by omega)
        have hhi : W.hi i = W.y i + 2 := by
          show max (W.y i) (W.y (i + 1)) = W.y i + 2
          rw [hy]; exact max_eq_right (by omega)
        have hpar : (W.y i : ZMod 2) = W.b := W.parY i
        rw [hlo, hhi]
        constructor
        · rintro ⟨-, h2, h3, h4⟩
          refine ⟨hv, h2, ?_, ?_⟩ <;>
            · have hmod : (((W.y i - h : ℤ)) : ZMod 2) = 0 := by
                rw [Int.cast_sub, hpar, hh, sub_self]
              have hev : Even (W.y i - h) := by
                rw [even_iff_two_dvd]
                exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hmod
              obtain ⟨k, hk⟩ := hev
              omega
        · rintro ⟨-, h2, h3, h4⟩
          refine ⟨hv, h2, ?_, ?_⟩ <;>
            · have hmod : (((W.y i - h : ℤ)) : ZMod 2) = 0 := by
                rw [Int.cast_sub, hpar, hh, sub_self]
              have hev : Even (W.y i - h) := by
                rw [even_iff_two_dvd]
                exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hmod
              obtain ⟨k, hk⟩ := hev
              omega
      · have hlo : W.lo i = W.y i - 2 := by
          show min (W.y i) (W.y (i + 1)) = W.y i - 2
          rw [hy]; exact min_eq_right (by omega)
        have hhi : W.hi i = W.y i := by
          show max (W.y i) (W.y (i + 1)) = W.y i
          rw [hy]; exact max_eq_left (by omega)
        have hpar : (W.y (i + 1) : ZMod 2) = W.b := W.parY (i + 1)
        rw [hlo, hhi]
        constructor
        · rintro ⟨-, h2, h3, h4⟩
          refine ⟨hv, h2, ?_, ?_⟩ <;>
            · have hmod : (((W.y (i + 1) - h : ℤ)) : ZMod 2) = 0 := by
                rw [Int.cast_sub, hpar, hh, sub_self]
              have hev : Even (W.y (i + 1) - h) := by
                rw [even_iff_two_dvd]
                exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hmod
              obtain ⟨k, hk⟩ := hev
              omega
        · rintro ⟨-, h2, h3, h4⟩
          refine ⟨hv, h2, ?_, ?_⟩ <;>
            · have hmod : (((W.y (i + 1) - h : ℤ)) : ZMod 2) = 0 := by
                rw [Int.cast_sub, hpar, hh, sub_self]
              have hev : Even (W.y (i + 1) - h) := by
                rw [even_iff_two_dvd]
                exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hmod
              obtain ⟨k, hk⟩ := hev
              omega
    · simp [hv]
  unfold OrthoLoop.p2
  apply Finset.sum_congr rfl
  intro i _
  exact if_congr (hiff i) rfl rfl

/-- The total count of vertical edges spanning level `h` is even, so crossing
parity at `(a, h)` equals the count of such edges with `x ≤ a` (mod 2). -/
theorem p2_eq_spanning_le (a h : ℤ) (hh : (h : ZMod 2) = W.b) :
    W.p2 (a, h) = ((univ.filter fun i => W.vert i ∧ W.x i ≤ a ∧ W.lo i = h).card : ZMod 2) := by
  classical
  -- p2 (a+1, h) = #{vert, x > a, lo = h} (band condition collapses by parity)
  have hcond : ∀ i : Fin (W.n + 4),
      (W.vert i ∧ a < W.x i ∧ W.lo i ≤ h ∧ h < W.hi i) ↔
      (W.vert i ∧ a < W.x i ∧ W.lo i = h) := by
    intro i
    constructor
    · rintro ⟨hv, h1, h2, h3⟩
      have hhi : W.hi i = W.lo i + 2 := W.hi_eq_lo_add_two i hv
      rw [hhi] at h3
      have hpar := W.lo_parY i
      have hmod : (((W.lo i - h : ℤ)) : ZMod 2) = 0 := by
        rw [Int.cast_sub, hpar, hh, sub_self]
      have hev : Even (W.lo i - h) := by
        rw [even_iff_two_dvd]
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hmod
      obtain ⟨k, hk⟩ := hev
      have h4 : W.lo i = h := by omega
      exact ⟨hv, h1, h4⟩
    · rintro ⟨hv, h1, h2⟩
      have h4 : W.lo i ≤ h := by rw [h2]
      have h5 : h < W.hi i := by
        have hhi : W.hi i = W.lo i + 2 := W.hi_eq_lo_add_two i hv
        rw [hhi, h2]
        omega
      exact ⟨hv, h1, h4, h5⟩
  have hp : W.p2 (a, h) =
      ((univ.filter fun i => W.vert i ∧ a < W.x i ∧ W.lo i = h).card : ZMod 2) := by
    have hshow : W.p2 (a, h) =
        (∑ i : Fin (W.n + 4), if W.vert i ∧ a < W.x i ∧ W.lo i ≤ h ∧ h < W.hi i
          then (1 : ZMod 2) else 0) := rfl
    have hfe : (univ.filter fun i => W.vert i ∧ a < W.x i ∧ W.lo i ≤ h ∧ h < W.hi i) =
        (univ.filter fun i => W.vert i ∧ a < W.x i ∧ W.lo i = h) := by
      apply Finset.filter_congr
      intro i _
      exact hcond i
    rw [hshow, Finset.sum_boole, hfe]
  rw [hp]
  -- total = right + left, and total = up(h) + down(h) = 0 (mod 2)
  have hsplit : (univ.filter fun i => W.vert i ∧ W.lo i = h) =
      (univ.filter fun i => W.vert i ∧ a < W.x i ∧ W.lo i = h) ∪
      (univ.filter fun i => W.vert i ∧ W.x i ≤ a ∧ W.lo i = h) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and]
    constructor
    · intro hi
      by_cases h1 : a < W.x i
      · exact Or.inl ⟨hi.1, h1, hi.2⟩
      · exact Or.inr ⟨hi.1, by omega, hi.2⟩
    · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩) <;> exact ⟨h1, h3⟩
  have hdisj : Disjoint (univ.filter fun i => W.vert i ∧ a < W.x i ∧ W.lo i = h)
      (univ.filter fun i => W.vert i ∧ W.x i ≤ a ∧ W.lo i = h) := by
    rw [Finset.disjoint_left]
    intro i h1 h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    omega
  have hcard : ((univ.filter fun i => W.vert i ∧ W.lo i = h).card : ZMod 2) =
      ((univ.filter fun i => W.vert i ∧ a < W.x i ∧ W.lo i = h).card : ZMod 2) +
      ((univ.filter fun i => W.vert i ∧ W.x i ≤ a ∧ W.lo i = h).card : ZMod 2) := by
    rw [hsplit, Finset.card_union_of_disjoint hdisj]
    push_cast
    rfl
  -- total spanning = up(h) + down(h)
  have htotal : ((univ.filter fun i => W.vert i ∧ W.lo i = h).card : ZMod 2) =
      ((univ.filter fun i => W.y i = h ∧ W.y (i + 1) = h + 2).card : ZMod 2) +
      ((univ.filter fun i => W.y i = h + 2 ∧ W.y (i + 1) = h).card : ZMod 2) := by
    have hsp : ∀ i : Fin (W.n + 4),
        (if W.vert i ∧ W.lo i = h then (1 : ZMod 2) else 0) =
        (if W.y i = h ∧ W.y (i + 1) = h + 2 then 1 else 0) +
        (if W.y i = h + 2 ∧ W.y (i + 1) = h then 1 else 0) := by
      intro i
      by_cases hv : W.vert i
      · rcases W.vert_cases i hv with hy | hy
        · have hlo : W.lo i = W.y i := by
            show min (W.y i) (W.y (i + 1)) = W.y i
            rw [hy]; exact min_eq_left (by omega)
          rw [hlo]
          have eA : (W.y i = h ∧ W.y (i + 1) = h + 2) ↔ W.y i = h := by
            constructor
            · rintro ⟨h1, -⟩; exact h1
            · intro h1; exact ⟨h1, by omega⟩
          have eB : (W.y i = h + 2 ∧ W.y (i + 1) = h) ↔ False := by
            constructor
            · rintro ⟨h1, h2⟩; omega
            · exact False.elim
          rw [if_congr (and_iff_right hv) rfl rfl, if_congr eA rfl rfl, if_congr eB rfl rfl,
            if_false]
          simp
        · have hlo : W.lo i = W.y i - 2 := by
            show min (W.y i) (W.y (i + 1)) = W.y i - 2
            rw [hy]; exact min_eq_right (by omega)
          rw [hlo]
          have e1 : (W.vert i ∧ W.y i - 2 = h) ↔ W.y i = h + 2 := by
            constructor
            · rintro ⟨-, h1⟩; omega
            · intro h1; exact ⟨hv, by omega⟩
          have eA : (W.y i = h ∧ W.y (i + 1) = h + 2) ↔ False := by
            constructor
            · rintro ⟨h1, h2⟩; omega
            · exact False.elim
          have eB : (W.y i = h + 2 ∧ W.y (i + 1) = h) ↔ W.y i = h + 2 := by
            constructor
            · rintro ⟨h1, -⟩; exact h1
            · intro h1; exact ⟨h1, by omega⟩
          rw [if_congr e1 rfl rfl, if_congr eA rfl rfl, if_congr eB rfl rfl, if_false]
          simp
      · have hy : W.y (i + 1) = W.y i := by
          rcases W.horiz_cases i hv with ⟨-, hy⟩ | ⟨-, hy⟩ <;> exact hy
        have e1 : (W.vert i ∧ W.lo i = h) ↔ False := by
          constructor
          · rintro ⟨h1, -⟩; exact absurd h1 hv
          · exact False.elim
        have eA : (W.y i = h ∧ W.y (i + 1) = h + 2) ↔ False := by
          constructor
          · rintro ⟨h1, h2⟩; omega
          · exact False.elim
        have eB : (W.y i = h + 2 ∧ W.y (i + 1) = h) ↔ False := by
          constructor
          · rintro ⟨h1, h2⟩; omega
          · exact False.elim
        rw [if_congr e1 rfl rfl, if_congr eA rfl rfl, if_congr eB rfl rfl, if_false]
        simp
    have hsum : (∑ i : Fin (W.n + 4), (if W.vert i ∧ W.lo i = h then (1 : ZMod 2) else 0)) =
        (∑ i : Fin (W.n + 4), (if W.y i = h ∧ W.y (i + 1) = h + 2 then 1 else 0)) +
        (∑ i : Fin (W.n + 4), (if W.y i = h + 2 ∧ W.y (i + 1) = h then 1 else 0)) := by
      rw [Finset.sum_congr rfl (fun i _ => hsp i), Finset.sum_add_distrib]
    simp only [Finset.sum_boole] at hsum
    exact hsum
  have hzero := W.up_add_down_zero h
  -- assemble: right + left = total = 0 ⟹ right = left (mod 2)
  have h1 : ((univ.filter fun i => W.vert i ∧ a < W.x i ∧ W.lo i = h).card : ZMod 2) +
      ((univ.filter fun i => W.vert i ∧ W.x i ≤ a ∧ W.lo i = h).card : ZMod 2) = 0 := by
    rw [← hcard, htotal]
    exact hzero
  have h2 : ((univ.filter fun i => W.vert i ∧ a < W.x i ∧ W.lo i = h).card : ZMod 2) =
      ((univ.filter fun i => W.vert i ∧ W.x i ≤ a ∧ W.lo i = h).card : ZMod 2) :=
    zmod2_eq_of_add_add_zero h1
  rw [h2]

/-- Base case: a simple 4-loop is a 2×2 square. -/
theorem base_case (W : OrthoLoop) (hn : W.n = 0) : W.P := by
  classical
  have hT := W.T_zmod
  have hL : (W.L : ZMod 2) = 0 := by
    have h1 : W.L = 4 := by unfold OrthoLoop.L; rw [hn]
    rw [h1]; decide
  suffices hI : (W.I : ZMod 2) = 1 by
    show (W.I : ZMod 2) = (W.T : ZMod 2) + (W.L : ZMod 2) + 1
    rw [hI, hT, hL, add_zero, zero_add]
  have e01 : (0 + 1 : Fin (W.n + 4)) = 1 := by abel
  have e11 : (1 + 1 : Fin (W.n + 4)) = 2 := by abel
  have e21 : (2 + 1 : Fin (W.n + 4)) = 3 := by abel
  have e30 : (3 + 1 : Fin (W.n + 4)) = 0 := by rw [hn]; decide
  have hs0 := W.step 0
  rw [e01] at hs0
  have hs1 := W.step 1
  rw [e11] at hs1
  have hs2 := W.step 2
  rw [e21] at hs2
  have hs3 := W.step 3
  rw [e30] at hs3
  rcases hs0 with ⟨hx0, hy0⟩ | ⟨hx0, hy0⟩ | ⟨hx0, hy0⟩ | ⟨hx0, hy0⟩ <;>
  rcases hs1 with ⟨hx1, hy1⟩ | ⟨hx1, hy1⟩ | ⟨hx1, hy1⟩ | ⟨hx1, hy1⟩ <;>
  rcases hs2 with ⟨hx2, hy2⟩ | ⟨hx2, hy2⟩ | ⟨hx2, hy2⟩ | ⟨hx2, hy2⟩ <;>
  rcases hs3 with ⟨hx3, hy3⟩ | ⟨hx3, hy3⟩ | ⟨hx3, hy3⟩ | ⟨hx3, hy3⟩ <;>
  · first
    | exfalso; exact two_ne_zero_fin (W.inj (Prod.ext (by omega) (by omega)))
    | exfalso; exact three_ne_one_fin (W.inj (Prod.ext (by omega) (by omega)))
    | exfalso; omega
    | exact square_interior_norm W hn _ _ (1) (1) (Or.inl rfl) (Or.inl rfl)
        Prod.mk.eta.symm (Prod.ext (by omega) (by omega)) (Prod.ext (by omega) (by omega))
        (Prod.ext (by omega) (by omega))
    | exact square_interior_norm W hn _ _ (1) (-1) (Or.inl rfl) (Or.inr rfl)
        Prod.mk.eta.symm (Prod.ext (by omega) (by omega)) (Prod.ext (by omega) (by omega))
        (Prod.ext (by omega) (by omega))
    | exact square_interior_norm W hn _ _ (-1) (1) (Or.inr rfl) (Or.inl rfl)
        Prod.mk.eta.symm (Prod.ext (by omega) (by omega)) (Prod.ext (by omega) (by omega))
        (Prod.ext (by omega) (by omega))
    | exact square_interior_norm W hn _ _ (-1) (-1) (Or.inr rfl) (Or.inr rfl)
        Prod.mk.eta.symm (Prod.ext (by omega) (by omega)) (Prod.ext (by omega) (by omega))
        (Prod.ext (by omega) (by omega))
    | rw [← reverse_I]
      exact square_interior_norm W.reverse hn _ _ (1) (1) (Or.inl rfl) (Or.inl rfl)
        (by
          show W.reverse.v 0 = ((W.v 0).1, (W.v 0).2)
          show W.v (-(0 : Fin (W.n + 4))) = ((W.v 0).1, (W.v 0).2)
          rw [show (-(0 : Fin (W.n + 4))) = 0 from by abel])
        (by
          show W.reverse.v 1 = ((W.v 0).1 + 2 * (1), (W.v 0).2)
          show W.v (-(1 : Fin (W.n + 4))) = ((W.v 0).1 + 2 * (1), (W.v 0).2)
          rw [show (-(1 : Fin (W.n + 4))) = 3 from by rw [hn]; decide]
          exact Prod.ext (by omega) (by omega))
        (by
          show W.reverse.v 2 = ((W.v 0).1 + 2 * (1), (W.v 0).2 + 2 * (1))
          show W.v (-(2 : Fin (W.n + 4))) = ((W.v 0).1 + 2 * (1), (W.v 0).2 + 2 * (1))
          rw [show (-(2 : Fin (W.n + 4))) = 2 from by rw [hn]; decide]
          exact Prod.ext (by omega) (by omega))
        (by
          show W.reverse.v 3 = ((W.v 0).1, (W.v 0).2 + 2 * (1))
          show W.v (-(3 : Fin (W.n + 4))) = ((W.v 0).1, (W.v 0).2 + 2 * (1))
          rw [show (-(3 : Fin (W.n + 4))) = 1 from by rw [hn]; decide]
          exact Prod.ext (by omega) (by omega))
    | rw [← reverse_I]
      exact square_interior_norm W.reverse hn _ _ (1) (-1) (Or.inl rfl) (Or.inr rfl)
        (by
          show W.reverse.v 0 = ((W.v 0).1, (W.v 0).2)
          show W.v (-(0 : Fin (W.n + 4))) = ((W.v 0).1, (W.v 0).2)
          rw [show (-(0 : Fin (W.n + 4))) = 0 from by abel])
        (by
          show W.reverse.v 1 = ((W.v 0).1 + 2 * (1), (W.v 0).2)
          show W.v (-(1 : Fin (W.n + 4))) = ((W.v 0).1 + 2 * (1), (W.v 0).2)
          rw [show (-(1 : Fin (W.n + 4))) = 3 from by rw [hn]; decide]
          exact Prod.ext (by omega) (by omega))
        (by
          show W.reverse.v 2 = ((W.v 0).1 + 2 * (1), (W.v 0).2 + 2 * (-1))
          show W.v (-(2 : Fin (W.n + 4))) = ((W.v 0).1 + 2 * (1), (W.v 0).2 + 2 * (-1))
          rw [show (-(2 : Fin (W.n + 4))) = 2 from by rw [hn]; decide]
          exact Prod.ext (by omega) (by omega))
        (by
          show W.reverse.v 3 = ((W.v 0).1, (W.v 0).2 + 2 * (-1))
          show W.v (-(3 : Fin (W.n + 4))) = ((W.v 0).1, (W.v 0).2 + 2 * (-1))
          rw [show (-(3 : Fin (W.n + 4))) = 1 from by rw [hn]; decide]
          exact Prod.ext (by omega) (by omega))
    | rw [← reverse_I]
      exact square_interior_norm W.reverse hn _ _ (-1) (1) (Or.inr rfl) (Or.inl rfl)
        (by
          show W.reverse.v 0 = ((W.v 0).1, (W.v 0).2)
          show W.v (-(0 : Fin (W.n + 4))) = ((W.v 0).1, (W.v 0).2)
          rw [show (-(0 : Fin (W.n + 4))) = 0 from by abel])
        (by
          show W.reverse.v 1 = ((W.v 0).1 + 2 * (-1), (W.v 0).2)
          show W.v (-(1 : Fin (W.n + 4))) = ((W.v 0).1 + 2 * (-1), (W.v 0).2)
          rw [show (-(1 : Fin (W.n + 4))) = 3 from by rw [hn]; decide]
          exact Prod.ext (by omega) (by omega))
        (by
          show W.reverse.v 2 = ((W.v 0).1 + 2 * (-1), (W.v 0).2 + 2 * (1))
          show W.v (-(2 : Fin (W.n + 4))) = ((W.v 0).1 + 2 * (-1), (W.v 0).2 + 2 * (1))
          rw [show (-(2 : Fin (W.n + 4))) = 2 from by rw [hn]; decide]
          exact Prod.ext (by omega) (by omega))
        (by
          show W.reverse.v 3 = ((W.v 0).1, (W.v 0).2 + 2 * (1))
          show W.v (-(3 : Fin (W.n + 4))) = ((W.v 0).1, (W.v 0).2 + 2 * (1))
          rw [show (-(3 : Fin (W.n + 4))) = 1 from by rw [hn]; decide]
          exact Prod.ext (by omega) (by omega))
    | rw [← reverse_I]
      exact square_interior_norm W.reverse hn _ _ (-1) (-1) (Or.inr rfl) (Or.inr rfl)
        (by
          show W.reverse.v 0 = ((W.v 0).1, (W.v 0).2)
          show W.v (-(0 : Fin (W.n + 4))) = ((W.v 0).1, (W.v 0).2)
          rw [show (-(0 : Fin (W.n + 4))) = 0 from by abel])
        (by
          show W.reverse.v 1 = ((W.v 0).1 + 2 * (-1), (W.v 0).2)
          show W.v (-(1 : Fin (W.n + 4))) = ((W.v 0).1 + 2 * (-1), (W.v 0).2)
          rw [show (-(1 : Fin (W.n + 4))) = 3 from by rw [hn]; decide]
          exact Prod.ext (by omega) (by omega))
        (by
          show W.reverse.v 2 = ((W.v 0).1 + 2 * (-1), (W.v 0).2 + 2 * (-1))
          show W.v (-(2 : Fin (W.n + 4))) = ((W.v 0).1 + 2 * (-1), (W.v 0).2 + 2 * (-1))
          rw [show (-(2 : Fin (W.n + 4))) = 2 from by rw [hn]; decide]
          exact Prod.ext (by omega) (by omega))
        (by
          show W.reverse.v 3 = ((W.v 0).1, (W.v 0).2 + 2 * (-1))
          show W.v (-(3 : Fin (W.n + 4))) = ((W.v 0).1, (W.v 0).2 + 2 * (-1))
          rw [show (-(3 : Fin (W.n + 4))) = 1 from by rw [hn]; decide]
          exact Prod.ext (by omega) (by omega))

/-- Coordinates of an edge midpoint, by direction. -/
theorem mid_cases (W : OrthoLoop) (k : Fin (W.n + 4)) (c : Cell) (h : W.mid k = c) :
    ((W.v (k + 1)).1 = (W.v k).1 ∧ c.1 = (W.v k).1 ∧ (c.2 = (W.v k).2 + 1 ∨ c.2 = (W.v k).2 - 1)) ∨
    ((W.v (k + 1)).2 = (W.v k).2 ∧ c.2 = (W.v k).2 ∧ (c.1 = (W.v k).1 + 1 ∨ c.1 = (W.v k).1 - 1)) := by
  have hm1 : (W.mid k).1 = ((W.v k).1 + (W.v (k + 1)).1) / 2 := rfl
  have hm2 : (W.mid k).2 = ((W.v k).2 + (W.v (k + 1)).2) / 2 := rfl
  have hc1 : c.1 = (W.mid k).1 := congrArg Prod.fst h.symm
  have hc2 : c.2 = (W.mid k).2 := congrArg Prod.snd h.symm
  rcases W.step k with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact Or.inl ⟨hx, by omega, Or.inl (by omega)⟩
  · exact Or.inl ⟨hx, by omega, Or.inr (by omega)⟩
  · exact Or.inr ⟨hy, by omega, Or.inl (by omega)⟩
  · exact Or.inr ⟨hy, by omega, Or.inr (by omega)⟩

theorem peel_hpa (W : OrthoLoop) (x₀ ym : ℤ) (h0 : W.v 0 = (x₀, ym)) :
    (x₀ : ZMod 2) = W.a := by
  have h0x : (W.v 0).1 = x₀ := congrArg Prod.fst h0
  rw [← h0x]; exact W.parX 0

theorem peel_hpb (W : OrthoLoop) (x₀ ym : ℤ) (h0 : W.v 0 = (x₀, ym)) :
    (ym : ZMod 2) = W.b := by
  have h0y : (W.v 0).2 = ym := congrArg Prod.snd h0
  rw [← h0y]; exact W.parY 0

theorem peel_hn1' (W : OrthoLoop) (x₀ ym : ℤ) (hn1 : W.v (-1) = (x₀, ym - 2)) :
    W.v ⟨W.n + 3, by omega⟩ = (x₀, ym - 2) := by
  have e : (⟨W.n + 3, by omega⟩ : Fin (W.n + 4)) = (-1 : Fin (W.n + 4)) := by
    apply Fin.ext
    simp [val_neg_one_fin]
  rw [e]
  exact hn1

theorem peel_hkey : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide

theorem peel_hparx1 (W : OrthoLoop) (x₀ ym : ℤ) (h0 : W.v 0 = (x₀, ym)) :
    ((x₀ + 1 : ℤ) : ZMod 2) ≠ W.a := by
  rw [← peel_hpa W x₀ ym h0]
  push_cast
  rcases peel_hkey (x₀ : ZMod 2) with h | h <;> rw [h] <;> decide

theorem peel_hparx2 (W : OrthoLoop) (x₀ ym : ℤ) (h0 : W.v 0 = (x₀, ym)) :
    ((x₀ - 1 : ℤ) : ZMod 2) ≠ W.a := by
  rw [← peel_hpa W x₀ ym h0]
  push_cast
  rcases peel_hkey (x₀ : ZMod 2) with h | h <;> rw [h] <;> decide

theorem peel_hparx3 (W : OrthoLoop) (x₀ ym : ℤ) (h0 : W.v 0 = (x₀, ym)) :
    ((x₀ + 3 : ℤ) : ZMod 2) ≠ W.a := by
  rw [← peel_hpa W x₀ ym h0]
  push_cast
  rcases peel_hkey (x₀ : ZMod 2) with h | h <;> rw [h] <;> decide

theorem peel_hpary1 (W : OrthoLoop) (x₀ ym : ℤ) (h0 : W.v 0 = (x₀, ym)) :
    ((ym - 1 : ℤ) : ZMod 2) ≠ W.b := by
  rw [← peel_hpb W x₀ ym h0]
  push_cast
  rcases peel_hkey (ym : ZMod 2) with h | h <;> rw [h] <;> decide

theorem peel_hpary3 (W : OrthoLoop) (x₀ ym : ℤ) (h0 : W.v 0 = (x₀, ym)) :
    ((ym - 3 : ℤ) : ZMod 2) ≠ W.b := by
  rw [← peel_hpb W x₀ ym h0]
  push_cast
  rcases peel_hkey (ym : ZMod 2) with h | h <;> rw [h] <;> decide

theorem peel_hwrap_disjoint (W : OrthoLoop) (x₀ ym : ℤ) (h0 : W.v 0 = (x₀, ym))
    (hn1 : W.v (-1) = (x₀, ym - 2)) (h2 : W.v 2 = (x₀ + 2, ym - 2)) :
    ∀ (k : Fin (W.n + 4)), 3 ≤ (k : ℕ) → (k : ℕ) ≤ W.n + 1 →
      Disjoint ({(x₀, ym - 2), (x₀ + 1, ym - 2), (x₀ + 2, ym - 2)} : Finset Cell)
        (W.edgePts k) := by
  classical
  have hpa := peel_hpa W x₀ ym h0
  have hkey := peel_hkey
  have hparx1 := peel_hparx1 W x₀ ym h0
  have hparx2 := peel_hparx2 W x₀ ym h0
  have hparx3 := peel_hparx3 W x₀ ym h0
  have hpary1 := peel_hpary1 W x₀ ym h0
  have hpary3 := peel_hpary3 W x₀ ym h0
  have hn1' := peel_hn1' W x₀ ym hn1
  intro k hk3 hkn
  rw [Finset.disjoint_left]
  intro c hc hc'
  simp only [Finset.mem_insert, Finset.mem_singleton] at hc
  have hjd : ∀ (j : Fin (W.n + 4)), W.v j = (x₀, ym - 2) → (j : ℕ) = W.n + 3 := by
    intro j hj
    have hjk := W.inj (hj.trans hn1'.symm)
    have hv := congrArg Fin.val hjk
    have hvv : ((⟨W.n + 3, by omega⟩ : Fin (W.n + 4)) : ℕ) = W.n + 3 := rfl
    rw [hvv] at hv
    exact hv
  have hjr : ∀ (j : Fin (W.n + 4)), W.v j = (x₀ + 2, ym - 2) → (j : ℕ) = 2 := by
    intro j hj
    have hjk := W.inj (hj.trans h2.symm)
    have hv := congrArg Fin.val hjk
    rw [val_two_fin] at hv
    exact hv
  rcases hc with rfl | rfl | rfl
  · -- c = (x₀, ym−2) = d
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc'
    rcases hc' with h | h | h
    · -- vertex: j = k = n+3 contradicts hkn
      have hjk := hjd _ h.symm
      omega
    · -- midpoint
      rcases W.mid_cases k _ h.symm with ⟨hx, h1, h2 | h2⟩ | ⟨hy, h1, h2 | h2⟩
      · -- vertical: (W.v k).2 = ym−3, parity
        have hyk : (W.v k).2 = ym - 3 := by
          have hc2 : ((x₀, ym - 2) : Cell).2 = ym - 2 := rfl
          omega
        exact hpary3 (hyk ▸ W.parY k)
      · -- vertical: (W.v k).2 = ym−1, parity
        have hyk : (W.v k).2 = ym - 1 := by
          have hc2 : ((x₀, ym - 2) : Cell).2 = ym - 2 := rfl
          omega
        exact hpary1 (hyk ▸ W.parY k)
      · -- horizontal: (W.v k).1 = x₀−1, parity
        have h1' : (W.v k).1 = x₀ - 1 := by
          have hc1 : ((x₀, ym - 2) : Cell).1 = x₀ := rfl
          omega
        have hparx2 : ((x₀ - 1 : ℤ) : ZMod 2) ≠ W.a := by
          rw [← hpa]
          push_cast
          rcases hkey (x₀ : ZMod 2) with h2' | h2' <;> rw [h2'] <;> decide
        exact hparx2 (h1' ▸ W.parX k)
      · -- horizontal: (W.v k).1 = x₀+1, parity
        have h1' : (W.v k).1 = x₀ + 1 := by
          have hc1 : ((x₀, ym - 2) : Cell).1 = x₀ := rfl
          omega
        exact hparx1 (h1' ▸ W.parX k)
    · -- vertex k+1: k+1 = n+3 contradicts hkn
      have hjk := hjd _ h.symm
      have h1m : ((k + 1 : Fin (W.n + 4)) : ℕ) = (k : ℕ) + 1 := by
        rw [Fin.val_add, Fin.val_one']
        have h1 : 1 % (W.n + 4) = 1 := Nat.mod_eq_of_lt (by omega)
        rw [h1, Nat.mod_eq_of_lt (by omega : (k:ℕ) + 1 < W.n + 4)]
      have hjk2 := hjd (k + 1) h.symm
      rw [h1m] at hjk2
      omega
  · -- c = (x₀+1, ym−2)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc'
    rcases hc' with h | h | h
    · have hz : (W.v k).1 = x₀ + 1 := (congrArg Prod.fst h).symm
      exact hparx1 (hz ▸ W.parX k)
    · rcases W.mid_cases k _ h.symm with ⟨hx, h1, h2 | h2⟩ | ⟨hy, h1, h2 | h2⟩
      · have h1x : (W.v k).1 = x₀ + 1 := h1.symm
        exact hparx1 (h1x ▸ W.parX k)
      · have h1x : (W.v k).1 = x₀ + 1 := h1.symm
        exact hparx1 (h1x ▸ W.parX k)
      · -- horizontal: (W.v k).1 = x₀ ⟹ d ⟹ k = n+3
        have h1' : (W.v k).1 = x₀ := by
          have hc1 : ((x₀ + 1, ym - 2) : Cell).1 = x₀ + 1 := rfl
          omega
        have h2' : (W.v k).2 = ym - 2 := h1.symm
        have hkv : W.v k = (x₀, ym - 2) := Prod.ext h1' h2'
        have hjk := hjd _ hkv
        omega
      · -- horizontal: (W.v k).1 = x₀+2 ⟹ r′ ⟹ k = 2
        have h1' : (W.v k).1 = x₀ + 2 := by
          have hc1 : ((x₀ + 1, ym - 2) : Cell).1 = x₀ + 1 := rfl
          omega
        have h2' : (W.v k).2 = ym - 2 := h1.symm
        have hkv : W.v k = (x₀ + 2, ym - 2) := Prod.ext h1' h2'
        have hjk := hjr _ hkv
        omega
    · have hz : (W.v (k + 1)).1 = x₀ + 1 := (congrArg Prod.fst h).symm
      exact hparx1 (hz ▸ W.parX (k + 1))
  · -- c = (x₀+2, ym−2) = r′
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc'
    rcases hc' with h | h | h
    · have hjk := hjr _ h.symm
      omega
    · rcases W.mid_cases k _ h.symm with ⟨hx, h1, h2 | h2⟩ | ⟨hy, h1, h2 | h2⟩
      · have hyk : (W.v k).2 = ym - 3 := by
          have hc2 : ((x₀ + 2, ym - 2) : Cell).2 = ym - 2 := rfl
          omega
        exact hpary3 (hyk ▸ W.parY k)
      · have hyk : (W.v k).2 = ym - 1 := by
          have hc2 : ((x₀ + 2, ym - 2) : Cell).2 = ym - 2 := rfl
          omega
        exact hpary1 (hyk ▸ W.parY k)
      · have h1' : (W.v k).1 = x₀ + 1 := by
          have hc1 : ((x₀ + 2, ym - 2) : Cell).1 = x₀ + 2 := rfl
          omega
        exact hparx1 (h1' ▸ W.parX k)
      · have h1' : (W.v k).1 = x₀ + 3 := by
          have hc1 : ((x₀ + 2, ym - 2) : Cell).1 = x₀ + 2 := rfl
          omega
        have hparx3 : ((x₀ + 3 : ℤ) : ZMod 2) ≠ W.a := by
          rw [← hpa]
          push_cast
          rcases hkey (x₀ : ZMod 2) with h2' | h2' <;> rw [h2'] <;> decide
        exact hparx3 (h1' ▸ W.parX k)
    · have hjk2 := hjr (k + 1) h.symm
      have h1m : ((k + 1 : Fin (W.n + 4)) : ℕ) = (k : ℕ) + 1 := by
        rw [Fin.val_add, Fin.val_one']
        have h1 : 1 % (W.n + 4) = 1 := Nat.mod_eq_of_lt (by omega)
        rw [h1, Nat.mod_eq_of_lt (by omega : (k:ℕ) + 1 < W.n + 4)]
      rw [h1m] at hjk2
      omega

theorem peel_hseg_of (W : OrthoLoop) (hn : 2 ≤ W.n) :
    ∀ (t : Fin (W.n - 2 + 4)), (t : ℕ) < W.n + 1 →
      ({W.v ⟨↑t + 2, lt_of_isLt_add t (by omega)⟩, midPt (W.v ⟨↑t + 2, lt_of_isLt_add t (by omega)⟩)
        (W.v ⟨(((t + 1 : Fin (W.n - 2 + 4)) : ℕ)) + 2, lt_of_isLt_add (t + 1) (by omega)⟩),
        W.v ⟨(((t + 1 : Fin (W.n - 2 + 4)) : ℕ)) + 2, lt_of_isLt_add (t + 1) (by omega)⟩} : Finset Cell) =
      W.edgePts ⟨↑t + 2, lt_of_isLt_add t (by omega)⟩ := by
  classical
  intro t ht
  have e5 : ((t + 1 : Fin (W.n - 2 + 4)) : ℕ) = (↑t : ℕ) + 1 := by
    have hv1 : ((t + 1 : Fin (W.n - 2 + 4)) : ℕ) = ((↑t : ℕ) + 1) % (W.n - 2 + 4) := by
      rw [Fin.val_add, Fin.val_one']
      have h1m : 1 % (W.n - 2 + 4) = 1 := Nat.mod_eq_of_lt (by omega)
      rw [h1m]
    rw [hv1, Nat.mod_eq_of_lt (by omega : (↑t : ℕ) + 1 < W.n - 2 + 4)]
  have e6 : (⟨(((t + 1 : Fin (W.n - 2 + 4)) : ℕ)) + 2, lt_of_isLt_add (t + 1) (by omega)⟩ : Fin (W.n + 4)) =
      (⟨↑t + 2, lt_of_isLt_add t (by omega)⟩ : Fin (W.n + 4)) + 1 := by
    apply Fin.ext
    have hvL : ((⟨(((t + 1 : Fin (W.n - 2 + 4)) : ℕ)) + 2, lt_of_isLt_add (t + 1) (by omega)⟩ : Fin (W.n + 4)) : ℕ) =
        ((t + 1 : Fin (W.n - 2 + 4)) : ℕ) + 2 := rfl
    rw [hvL, e5, Fin.val_add, Fin.val_one']
    have h1m : 1 % (W.n + 4) = 1 := Nat.mod_eq_of_lt (by omega)
    have h2m : (↑t + 2 + 1) % (W.n + 4) = ↑t + 2 + 1 := Nat.mod_eq_of_lt (by omega : ↑t + 3 < W.n + 4)
    rw [h1m, h2m]
  show ({W.v ⟨↑t + 2, by omega⟩, midPt (W.v ⟨↑t + 2, by omega⟩)
      (W.v ⟨(((t + 1 : Fin (W.n - 2 + 4)) : ℕ)) + 2, by omega⟩),
      W.v ⟨(((t + 1 : Fin (W.n - 2 + 4)) : ℕ)) + 2, by omega⟩} : Finset Cell) =
    ({W.v ⟨↑t + 2, by omega⟩, midPt (W.v ⟨↑t + 2, by omega⟩) (W.v ((⟨↑t + 2, by omega⟩) + 1)),
      W.v ((⟨↑t + 2, by omega⟩) + 1)} : Finset Cell)
  rw [e6]

theorem peelLoop_inj (W : OrthoLoop) (hn : 2 ≤ W.n) :
    Function.Injective (fun j : Fin (W.n - 2 + 4) => W.v ⟨j + 2, by omega⟩) := by
  classical
  intro j j' h
  have h2 : W.v ⟨j + 2, by omega⟩ = W.v ⟨j' + 2, by omega⟩ := h
  have h3 := W.inj h2
  have hv := congrArg Fin.val h3
  have hv1 : ((⟨j + 2, by omega⟩ : Fin (W.n + 4)) : ℕ) = j + 2 := rfl
  have hv2 : ((⟨j' + 2, by omega⟩ : Fin (W.n + 4)) : ℕ) = j' + 2 := rfl
  rw [hv1, hv2] at hv
  have hjj : (j : ℕ) = (j' : ℕ) := by omega
  exact Fin.ext hjj

theorem peelLoop_step (W : OrthoLoop) (x₀ ym : ℤ)
    (h2 : W.v 2 = (x₀ + 2, ym - 2)) (hn1 : W.v (-1) = (x₀, ym - 2)) (hn : 2 ≤ W.n) :
    ∀ i : Fin (W.n - 2 + 4),
      (((fun j : Fin (W.n - 2 + 4) => W.v ⟨j + 2, by omega⟩) (i + 1)).1 = ((fun j : Fin (W.n - 2 + 4) => W.v ⟨j + 2, by omega⟩) i).1 ∧ ((fun j : Fin (W.n - 2 + 4) => W.v ⟨j + 2, by omega⟩) (i + 1)).2 = ((fun j : Fin (W.n - 2 + 4) => W.v ⟨j + 2, by omega⟩) i).2 + 2) ∨
      (((fun j : Fin (W.n - 2 + 4) => W.v ⟨j + 2, by omega⟩) (i + 1)).1 = ((fun j : Fin (W.n - 2 + 4) => W.v ⟨j + 2, by omega⟩) i).1 ∧ ((fun j : Fin (W.n - 2 + 4) => W.v ⟨j + 2, by omega⟩) (i + 1)).2 = ((fun j : Fin (W.n - 2 + 4) => W.v ⟨j + 2, by omega⟩) i).2 - 2) ∨
      (((fun j : Fin (W.n - 2 + 4) => W.v ⟨j + 2, by omega⟩) (i + 1)).1 = ((fun j : Fin (W.n - 2 + 4) => W.v ⟨j + 2, by omega⟩) i).1 + 2 ∧ ((fun j : Fin (W.n - 2 + 4) => W.v ⟨j + 2, by omega⟩) (i + 1)).2 = ((fun j : Fin (W.n - 2 + 4) => W.v ⟨j + 2, by omega⟩) i).2) ∨
      (((fun j : Fin (W.n - 2 + 4) => W.v ⟨j + 2, by omega⟩) (i + 1)).1 = ((fun j : Fin (W.n - 2 + 4) => W.v ⟨j + 2, by omega⟩) i).1 - 2 ∧ ((fun j : Fin (W.n - 2 + 4) => W.v ⟨j + 2, by omega⟩) (i + 1)).2 = ((fun j : Fin (W.n - 2 + 4) => W.v ⟨j + 2, by omega⟩) i).2) := by
  classical
  have hn1' := peel_hn1' W x₀ ym hn1
  beta_reduce
  intro j
  by_cases hj : (j : ℕ) + 1 < W.n - 2 + 4
  · have hstep := W.step ⟨j + 2, by omega⟩
    have e2 : (⟨j + 2, by omega⟩ : Fin (W.n + 4)) + 1 = ⟨j + 3, by omega⟩ := by
      apply Fin.ext
      rw [Fin.val_add, Fin.val_one']
      have hv1 : ((⟨j + 2, by omega⟩ : Fin (W.n + 4)) : ℕ) = j + 2 := rfl
      have hv2 : ((⟨j + 3, by omega⟩ : Fin (W.n + 4)) : ℕ) = j + 3 := rfl
      rw [hv1, hv2]
      have h1m : 1 % (W.n + 4) = 1 := Nat.mod_eq_of_lt (by omega)
      have h2m : (j + 2 + 1) % (W.n + 4) = j + 2 + 1 := Nat.mod_eq_of_lt (by omega)
      rw [h1m, h2m]
    rw [e2] at hstep
    have e : (j + 1 : Fin (W.n - 2 + 4)) = ⟨j + 1, by omega⟩ := by
      apply Fin.ext
      rw [Fin.val_add, Fin.val_one']
      have hv1 : ((⟨j + 1, by omega⟩ : Fin (W.n - 2 + 4)) : ℕ) = j + 1 := rfl
      rw [hv1]
      have h1m : 1 % (W.n - 2 + 4) = 1 := Nat.mod_eq_of_lt (by omega)
      have h2m : ((j : ℕ) + 1) % (W.n - 2 + 4) = (j : ℕ) + 1 := Nat.mod_eq_of_lt hj
      rw [h1m, h2m]
    rw [e]
    exact hstep
  · have hj2 : (j : ℕ) = W.n + 1 := by omega
    have e0 : (j + 1 : Fin (W.n - 2 + 4)) = 0 := by
      apply Fin.ext
      rw [Fin.val_add, Fin.val_one', val_zero_fin]
      have h1m : 1 % (W.n - 2 + 4) = 1 := Nat.mod_eq_of_lt (by omega)
      rw [h1m, hj2]
      have hself : (W.n + 1 + 1) % (W.n - 2 + 4) = 0 := by
        have hm : W.n + 1 + 1 = W.n - 2 + 4 := by omega
        rw [hm, Nat.mod_self]
      exact hself
    rw [e0]
    have hjd : W.v ⟨j + 2, by omega⟩ = (x₀, ym - 2) := by
      have hje : (⟨j + 2, by omega⟩ : Fin (W.n + 4)) = ⟨W.n + 3, by omega⟩ := by
        apply Fin.ext
        simp
        omega
      rw [hje]
      exact hn1'
    have e02 : (⟨(0 : Fin (W.n - 2 + 4)) + 2, by omega⟩ : Fin (W.n + 4)) = (2 : Fin (W.n + 4)) := by
      apply Fin.ext
      show ((⟨(0 : Fin (W.n - 2 + 4)) + 2, by omega⟩ : Fin (W.n + 4)) : ℕ) = ((2 : Fin (W.n + 4)) : ℕ)
      rw [val_two_fin]
      show ((0 : Fin (W.n - 2 + 4)) + 2 : ℕ) = 2
      rw [val_zero_fin]
    rw [e02, hjd, h2]
    exact Or.inr (Or.inr (Or.inl ⟨by simp, by simp⟩))

theorem peelLoop_par (W : OrthoLoop) (hn : 2 ≤ W.n) :
    ∀ i : Fin (W.n - 2 + 4), (((fun j : Fin (W.n - 2 + 4) => W.v ⟨j + 2, by omega⟩) i).1 : ZMod 2) = W.a ∧ (((fun j : Fin (W.n - 2 + 4) => W.v ⟨j + 2, by omega⟩) i).2 : ZMod 2) = W.b := by
  classical
  beta_reduce
  intro j
  exact W.par ⟨j + 2, by omega⟩

theorem peelLoop_simple (W : OrthoLoop) (x₀ ym : ℤ) (h0 : W.v 0 = (x₀, ym))
    (h2 : W.v 2 = (x₀ + 2, ym - 2)) (hn1 : W.v (-1) = (x₀, ym - 2)) (hn : 2 ≤ W.n) :
    ∀ i j : Fin (W.n - 2 + 4), i ≠ j → i + 1 ≠ j → i ≠ j + 1 →
      Disjoint ({(fun j : Fin (W.n - 2 + 4) => W.v ⟨j + 2, by omega⟩) i, midPt ((fun j : Fin (W.n - 2 + 4) => W.v ⟨j + 2, by omega⟩) i) ((fun j : Fin (W.n - 2 + 4) => W.v ⟨j + 2, by omega⟩) (i + 1)), (fun j : Fin (W.n - 2 + 4) => W.v ⟨j + 2, by omega⟩) (i + 1)} : Finset Cell)
        ({(fun j : Fin (W.n - 2 + 4) => W.v ⟨j + 2, by omega⟩) j, midPt ((fun j : Fin (W.n - 2 + 4) => W.v ⟨j + 2, by omega⟩) j) ((fun j : Fin (W.n - 2 + 4) => W.v ⟨j + 2, by omega⟩) (j + 1)), (fun j : Fin (W.n - 2 + 4) => W.v ⟨j + 2, by omega⟩) (j + 1)} : Finset Cell) := by
  classical
  have hn1' := peel_hn1' W x₀ ym hn1
  have hseg_of := peel_hseg_of W hn
  have hwrap_disjoint := peel_hwrap_disjoint W x₀ ym h0 hn1 h2
  beta_reduce
  intro i j hij hi1j hij1
  rw [Finset.disjoint_left]
  intro c hci hcj
  beta_reduce at hci hcj
  -- wrap-edge successor value (used in both wrap cases)
  by_cases hi : (i : ℕ) = W.n + 1
  · -- i is the wrap edge
    by_cases hj : (j : ℕ) = W.n + 1
    · exact absurd (Fin.ext (by omega : (i : ℕ) = (j : ℕ))) hij
    · -- i wrap, j interior
      have hi1 : ((i + 1 : Fin (W.n - 2 + 4)) : ℕ) = 0 := by
        have hv1 : ((i + 1 : Fin (W.n - 2 + 4)) : ℕ) = (↑i + 1) % (W.n - 2 + 4) := by
          rw [Fin.val_add, Fin.val_one']
          have h1m : 1 % (W.n - 2 + 4) = 1 := Nat.mod_eq_of_lt (by omega)
          rw [h1m]
        rw [hv1, hi]
        have hm : W.n + 1 + 1 = W.n - 2 + 4 := by omega
        rw [hm, Nat.mod_self]
      have hseg_i : ({W.v ⟨↑i + 2, by omega⟩, midPt (W.v ⟨↑i + 2, by omega⟩)
          (W.v ⟨(↑(i + 1 : Fin (W.n - 2 + 4))) + 2, by omega⟩),
          W.v ⟨(↑(i + 1 : Fin (W.n - 2 + 4))) + 2, by omega⟩} : Finset Cell) =
          {(x₀, ym - 2), (x₀ + 1, ym - 2), (x₀ + 2, ym - 2)} := by
        have e1 : W.v ⟨↑i + 2, by omega⟩ = (x₀, ym - 2) := by
          have e1a : (⟨↑i + 2, by omega⟩ : Fin (W.n + 4)) = ⟨W.n + 3, by omega⟩ := by
            apply Fin.ext
            simp
            omega
          rw [e1a]
          exact hn1'
        have e2 : W.v ⟨(↑(i + 1 : Fin (W.n - 2 + 4))) + 2, by omega⟩ = (x₀ + 2, ym - 2) := by
          have e2a : (⟨(↑(i + 1 : Fin (W.n - 2 + 4))) + 2, by omega⟩ : Fin (W.n + 4)) =
              (2 : Fin (W.n + 4)) := by
            apply Fin.ext
            show (⟨(↑(i + 1 : Fin (W.n - 2 + 4))) + 2, by omega⟩ : Fin (W.n + 4)).val =
              ((2 : Fin (W.n + 4)) : ℕ)
            show ((i + 1 : Fin (W.n - 2 + 4)) : ℕ) + 2 = ((2 : Fin (W.n + 4)) : ℕ)
            rw [hi1, val_two_fin]
          rw [e2a, h2]
        have e3 : midPt (x₀, ym - 2) (x₀ + 2, ym - 2) = (x₀ + 1, ym - 2) := by
          simp only [midPt, Prod.mk.injEq]
          constructor <;> omega
        rw [e1, e2, e3]
      rw [hseg_i] at hci
      have hseg_j := hseg_of j (by omega)
      rw [hseg_j] at hcj
      have hjb : (j : ℕ) ≠ 0 ∧ (j : ℕ) ≤ W.n - 1 := by
        constructor
        · intro h0
          have h10 : (i + 1 : Fin (W.n - 2 + 4)) = 0 := by
            apply Fin.ext
            rw [hi1, val_zero_fin]
          exact hi1j (h10.trans (Fin.ext h0).symm)
        · have hjn : (j : ℕ) ≠ W.n := by
            intro h0
            apply hij1
            have e1 : (j + 1 : Fin (W.n - 2 + 4)) = i := by
              apply Fin.ext
              rw [hi]
              have hv1 : ((j + 1 : Fin (W.n - 2 + 4)) : ℕ) = (↑j + 1) % (W.n - 2 + 4) := by
                rw [Fin.val_add, Fin.val_one']
                have h1m : 1 % (W.n - 2 + 4) = 1 := Nat.mod_eq_of_lt (by omega)
                rw [h1m]
              rw [hv1, h0]
              have hm : W.n - 2 + 4 = W.n + 2 := by omega
              rw [hm]
              exact Nat.mod_eq_of_lt (by omega)
            exact e1.symm
          have hjn1 : (j : ℕ) ≠ W.n + 1 := by
            intro h0
            exact hij (Fin.ext (by omega))
          omega
      have hk3 : (3 : ℕ) ≤ ↑j + 2 := by omega
      have hkn : ↑j + 2 ≤ W.n + 1 := by omega
      have hd := hwrap_disjoint ⟨↑j + 2, by omega⟩ hk3 hkn
      rw [Finset.disjoint_left] at hd
      exact hd hci hcj
  · by_cases hj : (j : ℕ) = W.n + 1
    · -- j wrap, i interior: symmetric
      have hj1 : ((j + 1 : Fin (W.n - 2 + 4)) : ℕ) = 0 := by
        have hv1 : ((j + 1 : Fin (W.n - 2 + 4)) : ℕ) = (↑j + 1) % (W.n - 2 + 4) := by
          rw [Fin.val_add, Fin.val_one']
          have h1m : 1 % (W.n - 2 + 4) = 1 := Nat.mod_eq_of_lt (by omega)
          rw [h1m]
        rw [hv1, hj]
        have hm : W.n + 1 + 1 = W.n - 2 + 4 := by omega
        rw [hm, Nat.mod_self]
      have hseg_j : ({W.v ⟨↑j + 2, by omega⟩, midPt (W.v ⟨↑j + 2, by omega⟩)
          (W.v ⟨(↑(j + 1 : Fin (W.n - 2 + 4))) + 2, by omega⟩),
          W.v ⟨(↑(j + 1 : Fin (W.n - 2 + 4))) + 2, by omega⟩} : Finset Cell) =
          {(x₀, ym - 2), (x₀ + 1, ym - 2), (x₀ + 2, ym - 2)} := by
        have e1 : W.v ⟨↑j + 2, by omega⟩ = (x₀, ym - 2) := by
          have e1a : (⟨↑j + 2, by omega⟩ : Fin (W.n + 4)) = ⟨W.n + 3, by omega⟩ := by
            apply Fin.ext
            simp
            omega
          rw [e1a]
          exact hn1'
        have e2 : W.v ⟨(↑(j + 1 : Fin (W.n - 2 + 4))) + 2, by omega⟩ = (x₀ + 2, ym - 2) := by
          have e2a : (⟨(↑(j + 1 : Fin (W.n - 2 + 4))) + 2, by omega⟩ : Fin (W.n + 4)) =
              (2 : Fin (W.n + 4)) := by
            apply Fin.ext
            show (⟨(↑(j + 1 : Fin (W.n - 2 + 4))) + 2, by omega⟩ : Fin (W.n + 4)).val =
              ((2 : Fin (W.n + 4)) : ℕ)
            show ((j + 1 : Fin (W.n - 2 + 4)) : ℕ) + 2 = ((2 : Fin (W.n + 4)) : ℕ)
            rw [hj1, val_two_fin]
          rw [e2a, h2]
        have e3 : midPt (x₀, ym - 2) (x₀ + 2, ym - 2) = (x₀ + 1, ym - 2) := by
          simp only [midPt, Prod.mk.injEq]
          constructor <;> omega
        rw [e1, e2, e3]
      rw [hseg_j] at hcj
      have hseg_i := hseg_of i (by omega)
      rw [hseg_i] at hci
      have hib : (i : ℕ) ≠ 0 ∧ (i : ℕ) ≤ W.n - 1 := by
        constructor
        · intro h0
          have h10 : (j + 1 : Fin (W.n - 2 + 4)) = 0 := by
            apply Fin.ext
            rw [hj1, val_zero_fin]
          exact hij1 ((Fin.ext h0).trans h10.symm)
        · have hin : (i : ℕ) ≠ W.n := by
            intro h0
            apply hi1j
            have e1 : (i + 1 : Fin (W.n - 2 + 4)) = j := by
              apply Fin.ext
              rw [hj]
              have hv1 : ((i + 1 : Fin (W.n - 2 + 4)) : ℕ) = (↑i + 1) % (W.n - 2 + 4) := by
                rw [Fin.val_add, Fin.val_one']
                have h1m : 1 % (W.n - 2 + 4) = 1 := Nat.mod_eq_of_lt (by omega)
                rw [h1m]
              rw [hv1, h0]
              have hm : W.n - 2 + 4 = W.n + 2 := by omega
              rw [hm]
              exact Nat.mod_eq_of_lt (by omega)
            exact e1
          omega
      have hk3 : (3 : ℕ) ≤ ↑i + 2 := by omega
      have hkn : ↑i + 2 ≤ W.n + 1 := by omega
      have hd := hwrap_disjoint ⟨↑i + 2, by omega⟩ hk3 hkn
      rw [Finset.disjoint_left] at hd
      exact hd hcj hci
    · -- both interior: W.simple applies
      have hseg_i := hseg_of i (by omega)
      have hseg_j := hseg_of j (by omega)
      rw [hseg_i] at hci
      rw [hseg_j] at hcj
      have hiI : (i : ℕ) ≤ W.n := by omega
      have hjI : (j : ℕ) ≤ W.n := by omega
      have g1 : (⟨i + 2, by omega⟩ : Fin (W.n + 4)) ≠ ⟨j + 2, by omega⟩ := by
        intro h
        apply hij
        have hv := congrArg Fin.val h
        have hv1 : ((⟨i + 2, by omega⟩ : Fin (W.n + 4)) : ℕ) = ↑i + 2 := rfl
        have hv2 : ((⟨j + 2, by omega⟩ : Fin (W.n + 4)) : ℕ) = ↑j + 2 := rfl
        rw [hv1, hv2] at hv
        exact Fin.ext (by omega)
      have g2 : (⟨i + 2, by omega⟩ : Fin (W.n + 4)) + 1 ≠ ⟨j + 2, by omega⟩ := by
        intro h
        apply hi1j
        have hv := congrArg Fin.val h
        have hv2 : ((⟨j + 2, by omega⟩ : Fin (W.n + 4)) : ℕ) = ↑j + 2 := rfl
        rw [hv2] at hv
        have hs1 : (((⟨i + 2, by omega⟩ : Fin (W.n + 4)) + 1 : Fin (W.n + 4)) : ℕ) = ↑i + 3 := by
          rw [Fin.val_add, Fin.val_one']
          have h1m : 1 % (W.n + 4) = 1 := Nat.mod_eq_of_lt (by omega)
          have h2m : (↑i + 2 + 1) % (W.n + 4) = ↑i + 2 + 1 :=
            Nat.mod_eq_of_lt (by omega : ↑i + 3 < W.n + 4)
          rw [h1m, h2m]
        rw [hs1] at hv
        have e5 : ((i + 1 : Fin (W.n - 2 + 4)) : ℕ) = ↑i + 1 := by
          have hv1 : ((i + 1 : Fin (W.n - 2 + 4)) : ℕ) = (↑i + 1) % (W.n - 2 + 4) := by
            rw [Fin.val_add, Fin.val_one']
            have h1m : 1 % (W.n - 2 + 4) = 1 := Nat.mod_eq_of_lt (by omega)
            rw [h1m]
          rw [hv1, Nat.mod_eq_of_lt (by omega : (↑i : ℕ) + 1 < W.n - 2 + 4)]
        exact Fin.ext (by rw [e5]; omega)
      have g3 : (⟨i + 2, by omega⟩ : Fin (W.n + 4)) ≠ ⟨j + 2, by omega⟩ + 1 := by
        intro h
        apply hij1
        have hv := congrArg Fin.val h
        have hv1 : ((⟨i + 2, by omega⟩ : Fin (W.n + 4)) : ℕ) = ↑i + 2 := rfl
        rw [hv1] at hv
        have hs1 : (((⟨j + 2, by omega⟩ : Fin (W.n + 4)) + 1 : Fin (W.n + 4)) : ℕ) = ↑j + 3 := by
          rw [Fin.val_add, Fin.val_one']
          have h1m : 1 % (W.n + 4) = 1 := Nat.mod_eq_of_lt (by omega)
          have h2m : (↑j + 2 + 1) % (W.n + 4) = ↑j + 2 + 1 :=
            Nat.mod_eq_of_lt (by omega : ↑j + 3 < W.n + 4)
          rw [h1m, h2m]
        rw [hs1] at hv
        have e5 : ((j + 1 : Fin (W.n - 2 + 4)) : ℕ) = ↑j + 1 := by
          have hv1 : ((j + 1 : Fin (W.n - 2 + 4)) : ℕ) = (↑j + 1) % (W.n - 2 + 4) := by
            rw [Fin.val_add, Fin.val_one']
            have h1m : 1 % (W.n - 2 + 4) = 1 := Nat.mod_eq_of_lt (by omega)
            rw [h1m]
          rw [hv1, Nat.mod_eq_of_lt (by omega : (↑j : ℕ) + 1 < W.n - 2 + 4)]
        exact Fin.ext (by rw [e5]; omega)
      have hd := W.simple ⟨↑i + 2, by omega⟩ ⟨↑j + 2, by omega⟩ g1 g2 g3
      rw [Finset.disjoint_left] at hd
      exact hd hci hcj

set_option maxHeartbeats 800000 in
theorem peelLoop_I (W : OrthoLoop) (x₀ ym : ℤ) (h0 : W.v 0 = (x₀, ym))
    (hmax : ∀ i, (W.v i).2 ≤ ym) (hmin : ∀ i, (W.v i).2 = ym → x₀ ≤ (W.v i).1)
    (h1 : W.v 1 = (x₀ + 2, ym)) (h2 : W.v 2 = (x₀ + 2, ym - 2))
    (hn1 : W.v (-1) = (x₀, ym - 2)) (hn : 2 ≤ W.n) :
    ({ a := W.a, b := W.b, n := W.n - 2, v := fun j : Fin (W.n - 2 + 4) => W.v ⟨j + 2, by omega⟩, inj := peelLoop_inj W hn, step := peelLoop_step W x₀ ym h2 hn1 hn, par := peelLoop_par W hn, simple := peelLoop_simple W x₀ ym h0 h2 hn1 hn } : OrthoLoop).I + 2 = W.I := by
  classical
  set W' := ({ a := W.a, b := W.b, n := W.n - 2, v := fun j : Fin (W.n - 2 + 4) => W.v ⟨j + 2, by omega⟩, inj := peelLoop_inj W hn, step := peelLoop_step W x₀ ym h2 hn1 hn, par := peelLoop_par W hn, simple := peelLoop_simple W x₀ ym h0 h2 hn1 hn } : OrthoLoop)
  have hWn : W'.n = W.n - 2 := rfl
  have h0x : (W.v 0).1 = x₀ := congrArg Prod.fst h0
  have h0y : (W.v 0).2 = ym := congrArg Prod.snd h0
  have h2x : (W.v 2).1 = x₀ + 2 := congrArg Prod.fst h2
  have h2y : (W.v 2).2 = ym - 2 := congrArg Prod.snd h2
  have hn1' := peel_hn1' W x₀ ym hn1
  have hdx : (W.v ⟨W.n + 3, by omega⟩).1 = x₀ := congrArg Prod.fst hn1'
  have hdy : (W.v ⟨W.n + 3, by omega⟩).2 = ym - 2 := congrArg Prod.snd hn1'
  have hpa := peel_hpa W x₀ ym h0
  have hpb := peel_hpb W x₀ ym h0
  have hkey := peel_hkey
  have hparx1 := peel_hparx1 W x₀ ym h0
  have hpary1 := peel_hpary1 W x₀ ym h0
  · -- I: W'.I + 2 = W.I
    have h1x : (W.v 1).1 = x₀ + 2 := congrArg Prod.fst h1
    have h1y : (W.v 1).2 = ym := congrArg Prod.snd h1
    have hjd : ∀ j : Fin (W.n + 4), W.v j = (x₀, ym - 2) → j = ⟨W.n + 3, by omega⟩ :=
      fun j hj => W.inj (hj.trans hn1'.symm)
    have h0xX : W.x 0 = x₀ := h0x
    have h0yX : W.y 0 = ym := h0y
    have h1xX : W.x 1 = x₀ + 2 := h1x
    have h1yX : W.y 1 = ym := h1y
    have h2xX : W.x 2 = x₀ + 2 := h2x
    have h2yX : W.y 2 = ym - 2 := h2y
    have hdxX : W.x ⟨W.n + 3, by omega⟩ = x₀ := hdx
    have hdyX : W.y ⟨W.n + 3, by omega⟩ = ym - 2 := hdy
    have hjr : ∀ j : Fin (W.n + 4), W.v j = (x₀ + 2, ym - 2) → j = 2 :=
      fun j hj => W.inj (hj.trans h2.symm)
    have hj0 : ∀ j : Fin (W.n + 4), W.v j = (x₀, ym) → j = 0 :=
      fun j hj => W.inj (hj.trans h0.symm)
    have hj1v : ∀ j : Fin (W.n + 4), W.v j = (x₀ + 2, ym) → j = 1 :=
      fun j hj => W.inj (hj.trans h1.symm)
    have eS_last : (⟨W.n + 3, by omega⟩ + 1 : Fin (W.n + 4)) = 0 := by
      apply Fin.ext
      rw [Fin.val_add, Fin.val_one']
      have h1m : 1 % (W.n + 4) = 1 := Nat.mod_eq_of_lt (by omega)
      rw [h1m, val_zero_fin]
      have hm : W.n + 3 + 1 = W.n + 4 := by omega
      rw [hm, Nat.mod_self]
    have hvd' : W'.v ⟨W.n + 1, by omega⟩ = (x₀, ym - 2) := by
      show W.v ⟨↑(⟨W.n + 1, by omega⟩ : Fin (W.n - 2 + 4)) + 2, by omega⟩ = (x₀, ym - 2)
      have e : (⟨↑(⟨W.n + 1, by omega⟩ : Fin (W.n - 2 + 4)) + 2, by omega⟩ : Fin (W.n + 4)) =
          ⟨W.n + 3, by omega⟩ := by
        apply Fin.ext
        show (↑(⟨W.n + 1, by omega⟩ : Fin (W.n - 2 + 4)) + 2 : ℕ) = W.n + 3
        show (W.n + 1) + 2 = W.n + 3
        omega
      rw [e]
      exact hn1'
    have hvr' : W'.v 0 = (x₀ + 2, ym - 2) := by
      show W.v ⟨↑(0 : Fin (W.n - 2 + 4)) + 2, by omega⟩ = (x₀ + 2, ym - 2)
      have e : (⟨↑(0 : Fin (W.n - 2 + 4)) + 2, by omega⟩ : Fin (W.n + 4)) = 2 := by
        apply Fin.ext
        show ((⟨↑(0 : Fin (W.n - 2 + 4)) + 2, by omega⟩ : Fin (W.n + 4)) : ℕ) =
          ((2 : Fin (W.n + 4)) : ℕ)
        rw [val_two_fin]
        show (↑(0 : Fin (W.n - 2 + 4)) + 2 : ℕ) = 2
        rw [val_zero_fin]
      rw [e]
      exact h2
    have hmid' : W'.mid ⟨W.n + 1, by omega⟩ = (x₀ + 1, ym - 2) := by
      show midPt (W'.v ⟨W.n + 1, by omega⟩) (W'.v (⟨W.n + 1, by omega⟩ + 1)) = (x₀ + 1, ym - 2)
      have eS : (⟨W.n + 1, by omega⟩ + 1 : Fin (W.n - 2 + 4)) = 0 := by
        apply Fin.ext
        rw [Fin.val_add, Fin.val_one']
        have h1m : 1 % (W.n - 2 + 4) = 1 := Nat.mod_eq_of_lt (by omega)
        rw [h1m, val_zero_fin]
        have hm : W.n + 1 + 1 = W.n - 2 + 4 := by omega
        rw [hm, Nat.mod_self]
      rw [eS, hvd', hvr']
      simp only [midPt, Prod.mk.injEq]
      constructor <;> omega
    have hbd : (x₀, ym - 2) ∈ W.boundary := by
      rw [← hn1']
      exact W.vertex_mem_boundary _
    have hbd' : (x₀, ym - 2) ∈ W'.boundary := by
      rw [← hvd']
      exact W'.vertex_mem_boundary _
    have hbm' : (x₀ + 1, ym - 2) ∈ W'.boundary := by
      rw [← hmid']
      exact W'.mid_mem_boundary _
    have hbx0 : (x₀, ym - 1) ∈ W.boundary := by
      have hm : W.mid ⟨W.n + 3, by omega⟩ = (x₀, ym - 1) := by
        show midPt (W.v ⟨W.n + 3, by omega⟩) (W.v (⟨W.n + 3, by omega⟩ + 1)) = (x₀, ym - 1)
        rw [eS_last, hn1', h0]
        simp only [midPt, Prod.mk.injEq]
        constructor <;> omega
      rw [← hm]
      exact W.mid_mem_boundary _
    -- flip formula
    have hflip : ∀ c : Cell, W.p2 c + W'.p2 c =
        (if c.1 < x₀ ∧ ym - 2 ≤ c.2 ∧ c.2 < ym then (1 : ZMod 2) else 0) +
        (if c.1 < x₀ + 2 ∧ ym - 2 ≤ c.2 ∧ c.2 < ym then (1 : ZMod 2) else 0) := by
      intro c
      let fW : ℕ → ZMod 2 := fun i =>
        if h : i < W.n + 4 then
          (if W.vert ⟨i, h⟩ ∧ c.1 < W.x ⟨i, h⟩ ∧ W.lo ⟨i, h⟩ ≤ c.2 ∧ c.2 < W.hi ⟨i, h⟩
            then (1 : ZMod 2) else 0)
        else 0
      let fW' : ℕ → ZMod 2 := fun j =>
        if h : j < W'.n + 4 then
          (if W'.vert ⟨j, h⟩ ∧ c.1 < W'.x ⟨j, h⟩ ∧ W'.lo ⟨j, h⟩ ≤ c.2 ∧ c.2 < W'.hi ⟨j, h⟩
            then (1 : ZMod 2) else 0)
        else 0
      have hfW : ∀ i : Fin (W.n + 4),
          (if W.vert i ∧ c.1 < W.x i ∧ W.lo i ≤ c.2 ∧ c.2 < W.hi i then (1 : ZMod 2) else 0) =
            fW ↑i := by
        intro i
        have hi : ↑i < W.n + 4 := i.isLt
        have hi2 : (⟨↑i, hi⟩ : Fin (W.n + 4)) = i := Fin.ext rfl
        show (if W.vert i ∧ c.1 < W.x i ∧ W.lo i ≤ c.2 ∧ c.2 < W.hi i then (1 : ZMod 2) else 0) =
          if h : ↑i < W.n + 4 then
            (if W.vert ⟨↑i, h⟩ ∧ c.1 < W.x ⟨↑i, h⟩ ∧ W.lo ⟨↑i, h⟩ ≤ c.2 ∧ c.2 < W.hi ⟨↑i, h⟩
              then (1 : ZMod 2) else 0)
          else 0
        rw [dif_pos hi, hi2]
      have hfW' : ∀ j : Fin (W'.n + 4),
          (if W'.vert j ∧ c.1 < W'.x j ∧ W'.lo j ≤ c.2 ∧ c.2 < W'.hi j then (1 : ZMod 2) else 0) =
            fW' ↑j := by
        intro j
        have hj : ↑j < W'.n + 4 := j.isLt
        have hj2 : (⟨↑j, hj⟩ : Fin (W'.n + 4)) = j := Fin.ext rfl
        show (if W'.vert j ∧ c.1 < W'.x j ∧ W'.lo j ≤ c.2 ∧ c.2 < W'.hi j then (1 : ZMod 2) else 0) =
          if h : ↑j < W'.n + 4 then
            (if W'.vert ⟨↑j, h⟩ ∧ c.1 < W'.x ⟨↑j, h⟩ ∧ W'.lo ⟨↑j, h⟩ ≤ c.2 ∧ c.2 < W'.hi ⟨↑j, h⟩
              then (1 : ZMod 2) else 0)
          else 0
        rw [dif_pos hj, hj2]
      have hsumW : W.p2 c = ∑ i ∈ Finset.range (W.n + 4), fW i := by
        show (∑ i : Fin (W.n + 4),
            (if W.vert i ∧ c.1 < W.x i ∧ W.lo i ≤ c.2 ∧ c.2 < W.hi i then (1 : ZMod 2) else 0)) = _
        rw [Finset.sum_congr rfl (fun i _ => hfW i)]
        exact Fin.sum_univ_eq_sum_range fW (W.n + 4)
      have hsumW' : W'.p2 c = ∑ i ∈ Finset.range (W'.n + 4), fW' i := by
        show (∑ i : Fin (W'.n + 4),
            (if W'.vert i ∧ c.1 < W'.x i ∧ W'.lo i ≤ c.2 ∧ c.2 < W'.hi i then (1 : ZMod 2) else 0)) = _
        rw [Finset.sum_congr rfl (fun i _ => hfW' i)]
        exact Fin.sum_univ_eq_sum_range fW' (W'.n + 4)
      have htail : ∀ j : ℕ, j < W.n + 1 → fW' j = fW (j + 2) := by
        intro j hj
        have hjW : j + 2 < W.n + 4 := by omega
        have hjW' : j < W'.n + 4 := by
          have hm : W'.n + 4 = W.n + 2 := by rw [hWn]; omega
          omega
        have e1 : W'.v ⟨j, hjW'⟩ = W.v ⟨j + 2, hjW⟩ := rfl
        have eS1 : (⟨j, hjW'⟩ + 1 : Fin (W'.n + 4)) =
            ⟨(j + 1) % (W'.n + 4), Nat.mod_lt _ (by omega)⟩ := by
          apply Fin.ext
          rw [Fin.val_add, Fin.val_one']
          have h1m : 1 % (W'.n + 4) = 1 := Nat.mod_eq_of_lt (by omega)
          rw [h1m]
        have eS2 : (⟨j + 2, hjW⟩ + 1 : Fin (W.n + 4)) =
            ⟨(j + 2 + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ := by
          apply Fin.ext
          rw [Fin.val_add, Fin.val_one']
          have h1m : 1 % (W.n + 4) = 1 := Nat.mod_eq_of_lt (by omega)
          rw [h1m]
        have e2 : W'.v ⟨(j + 1) % (W'.n + 4), Nat.mod_lt _ (by omega)⟩ =
            W.v ⟨(j + 2 + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ := by
          have hm : W'.n + 4 = W.n + 2 := by rw [hWn]; omega
          have e2a : (⟨(j + 1) % (W'.n + 4), Nat.mod_lt _ (by omega)⟩ : Fin (W'.n + 4)) =
              ⟨j + 1, by omega⟩ := by
            apply Fin.ext
            show (⟨(j + 1) % (W'.n + 4), Nat.mod_lt _ (by omega)⟩ : Fin (W'.n + 4)).val =
              (⟨j + 1, by omega⟩ : Fin (W'.n + 4)).val
            show (j + 1) % (W'.n + 4) = j + 1
            rw [hm]
            exact Nat.mod_eq_of_lt (by omega)
          have e2b : (⟨(j + 2 + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ : Fin (W.n + 4)) =
              ⟨j + 3, by omega⟩ := by
            apply Fin.ext
            show (⟨(j + 2 + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ : Fin (W.n + 4)).val =
              (⟨j + 3, by omega⟩ : Fin (W.n + 4)).val
            show (j + 2 + 1) % (W.n + 4) = j + 3
            exact Nat.mod_eq_of_lt (by omega)
          rw [e2a, e2b]
        show (if h : j < W'.n + 4 then
            (if W'.vert ⟨j, h⟩ ∧ c.1 < W'.x ⟨j, h⟩ ∧ W'.lo ⟨j, h⟩ ≤ c.2 ∧ c.2 < W'.hi ⟨j, h⟩
              then (1 : ZMod 2) else 0) else 0) =
          (if h : j + 2 < W.n + 4 then
            (if W.vert ⟨j + 2, h⟩ ∧ c.1 < W.x ⟨j + 2, h⟩ ∧ W.lo ⟨j + 2, h⟩ ≤ c.2 ∧ c.2 < W.hi ⟨j + 2, h⟩
              then (1 : ZMod 2) else 0) else 0)
        rw [dif_pos hjW', dif_pos hjW]
        have hiff : (W'.vert ⟨j, hjW'⟩ ∧ c.1 < W'.x ⟨j, hjW'⟩ ∧ W'.lo ⟨j, hjW'⟩ ≤ c.2 ∧
            c.2 < W'.hi ⟨j, hjW'⟩) ↔
            (W.vert ⟨j + 2, hjW⟩ ∧ c.1 < W.x ⟨j + 2, hjW⟩ ∧ W.lo ⟨j + 2, hjW⟩ ≤ c.2 ∧
            c.2 < W.hi ⟨j + 2, hjW⟩) := by
          show (((W'.v (⟨j, hjW'⟩ + 1)).1 = (W'.v ⟨j, hjW'⟩).1) ∧ c.1 < (W'.v ⟨j, hjW'⟩).1 ∧
              min ((W'.v ⟨j, hjW'⟩).2) ((W'.v (⟨j, hjW'⟩ + 1)).2) ≤ c.2 ∧
              c.2 < max ((W'.v ⟨j, hjW'⟩).2) ((W'.v (⟨j, hjW'⟩ + 1)).2)) ↔
            (((W.v (⟨j + 2, hjW⟩ + 1)).1 = (W.v ⟨j + 2, hjW⟩).1) ∧ c.1 < (W.v ⟨j + 2, hjW⟩).1 ∧
              min ((W.v ⟨j + 2, hjW⟩).2) ((W.v (⟨j + 2, hjW⟩ + 1)).2) ≤ c.2 ∧
              c.2 < max ((W.v ⟨j + 2, hjW⟩).2) ((W.v (⟨j + 2, hjW⟩ + 1)).2))
          rw [eS1, eS2, e1, e2]
        exact if_congr hiff rfl rfl
      have hfW0 : fW 0 = 0 := by
        have h0lt : 0 < W.n + 4 := by omega
        show (if h : 0 < W.n + 4 then
            (if W.vert ⟨0, h⟩ ∧ c.1 < W.x ⟨0, h⟩ ∧ W.lo ⟨0, h⟩ ≤ c.2 ∧ c.2 < W.hi ⟨0, h⟩
              then (1 : ZMod 2) else 0) else 0) = 0
        rw [dif_pos h0lt]
        apply if_neg
        intro hcon
        have hvert : W.x (⟨0, h0lt⟩ + 1) = W.x ⟨0, h0lt⟩ := hcon.1
        have e0 : (⟨0, h0lt⟩ : Fin (W.n + 4)) = 0 := Fin.ext rfl
        have e01 : (⟨0, h0lt⟩ + 1 : Fin (W.n + 4)) = 1 := by rw [e0]; exact zero_add 1
        rw [e01, e0] at hvert
        rw [h1xX, h0xX] at hvert
        omega
      have hfW1 : fW 1 = (if c.1 < x₀ + 2 ∧ ym - 2 ≤ c.2 ∧ c.2 < ym then (1 : ZMod 2) else 0) := by
        have h1lt : 1 < W.n + 4 := by omega
        show (if h : 1 < W.n + 4 then
            (if W.vert ⟨1, h⟩ ∧ c.1 < W.x ⟨1, h⟩ ∧ W.lo ⟨1, h⟩ ≤ c.2 ∧ c.2 < W.hi ⟨1, h⟩
              then (1 : ZMod 2) else 0) else 0) = _
        rw [dif_pos h1lt]
        have e1m : (⟨1, h1lt⟩ : Fin (W.n + 4)) = 1 := by
          apply Fin.ext
          show (1 : ℕ) = ((1 : Fin (W.n + 4)) : ℕ)
          rw [val_one_fin]
        have e11 : (1 + 1 : Fin (W.n + 4)) = 2 := by abel
        have hvert : W.vert ⟨1, h1lt⟩ := by
          show W.x (⟨1, h1lt⟩ + 1) = W.x ⟨1, h1lt⟩
          rw [e1m, e11, h2xX, h1xX]
        have hx1 : W.x ⟨1, h1lt⟩ = x₀ + 2 := by rw [e1m]; exact h1xX
        have hlo1 : W.lo ⟨1, h1lt⟩ = ym - 2 := by
          show min (W.y ⟨1, h1lt⟩) (W.y (⟨1, h1lt⟩ + 1)) = ym - 2
          rw [e1m, e11, h1yX, h2yX]
          exact min_eq_right (by omega)
        have hhi1 : W.hi ⟨1, h1lt⟩ = ym := by
          show max (W.y ⟨1, h1lt⟩) (W.y (⟨1, h1lt⟩ + 1)) = ym
          rw [e1m, e11, h1yX, h2yX]
          exact max_eq_left (by omega)
        have hiff : (W.vert ⟨1, h1lt⟩ ∧ c.1 < W.x ⟨1, h1lt⟩ ∧ W.lo ⟨1, h1lt⟩ ≤ c.2 ∧
            c.2 < W.hi ⟨1, h1lt⟩) ↔ (c.1 < x₀ + 2 ∧ ym - 2 ≤ c.2 ∧ c.2 < ym) := by
          rw [hx1, hlo1, hhi1, show W.vert ⟨1, h1lt⟩ = True from eq_true hvert, true_and]
        exact if_congr hiff rfl rfl
      have hfWlast : fW (W.n + 3) =
          (if c.1 < x₀ ∧ ym - 2 ≤ c.2 ∧ c.2 < ym then (1 : ZMod 2) else 0) := by
        have hlt : W.n + 3 < W.n + 4 := by omega
        show (if h : W.n + 3 < W.n + 4 then
            (if W.vert ⟨W.n + 3, h⟩ ∧ c.1 < W.x ⟨W.n + 3, h⟩ ∧ W.lo ⟨W.n + 3, h⟩ ≤ c.2 ∧
              c.2 < W.hi ⟨W.n + 3, h⟩ then (1 : ZMod 2) else 0) else 0) = _
        rw [dif_pos hlt]
        have hvert : W.vert ⟨W.n + 3, hlt⟩ := by
          show W.x (⟨W.n + 3, hlt⟩ + 1) = W.x ⟨W.n + 3, hlt⟩
          rw [eS_last, h0xX, hdxX]
        have hxl : W.x ⟨W.n + 3, hlt⟩ = x₀ := hdxX
        have hlol : W.lo ⟨W.n + 3, hlt⟩ = ym - 2 := by
          show min (W.y ⟨W.n + 3, hlt⟩) (W.y (⟨W.n + 3, hlt⟩ + 1)) = ym - 2
          rw [eS_last, hdyX, h0yX]
          exact min_eq_left (by omega)
        have hhil : W.hi ⟨W.n + 3, hlt⟩ = ym := by
          show max (W.y ⟨W.n + 3, hlt⟩) (W.y (⟨W.n + 3, hlt⟩ + 1)) = ym
          rw [eS_last, hdyX, h0yX]
          exact max_eq_right (by omega)
        have hiff : (W.vert ⟨W.n + 3, hlt⟩ ∧ c.1 < W.x ⟨W.n + 3, hlt⟩ ∧ W.lo ⟨W.n + 3, hlt⟩ ≤ c.2 ∧
            c.2 < W.hi ⟨W.n + 3, hlt⟩) ↔ (c.1 < x₀ ∧ ym - 2 ≤ c.2 ∧ c.2 < ym) := by
          rw [hxl, hlol, hhil, show W.vert ⟨W.n + 3, hlt⟩ = True from eq_true hvert, true_and]
        exact if_congr hiff rfl rfl
      have hfW'last : fW' (W.n + 1) = 0 := by
        have hlt : W.n + 1 < W'.n + 4 := by
          have hm : W'.n + 4 = W.n + 2 := by rw [hWn]; omega
          omega
        show (if h : W.n + 1 < W'.n + 4 then
            (if W'.vert ⟨W.n + 1, h⟩ ∧ c.1 < W'.x ⟨W.n + 1, h⟩ ∧ W'.lo ⟨W.n + 1, h⟩ ≤ c.2 ∧
              c.2 < W'.hi ⟨W.n + 1, h⟩ then (1 : ZMod 2) else 0) else 0) = 0
        rw [dif_pos hlt]
        apply if_neg
        intro hcon
        have hvert : W'.x (⟨W.n + 1, hlt⟩ + 1) = W'.x ⟨W.n + 1, hlt⟩ := hcon.1
        have eS : (⟨W.n + 1, hlt⟩ + 1 : Fin (W'.n + 4)) = 0 := by
          apply Fin.ext
          rw [Fin.val_add, Fin.val_one']
          have h1m : 1 % (W'.n + 4) = 1 := Nat.mod_eq_of_lt (by omega)
          rw [h1m, val_zero_fin]
          have hm : W.n + 1 + 1 = W'.n + 4 := by rw [hWn]; omega
          rw [hm, Nat.mod_self]
        have e1 : W'.x (⟨W.n + 1, hlt⟩ + 1) = x₀ + 2 := by
          rw [eS]
          show (W'.v 0).1 = x₀ + 2
          rw [hvr']
        have e2 : W'.x ⟨W.n + 1, hlt⟩ = x₀ := by
          show (W'.v ⟨W.n + 1, hlt⟩).1 = x₀
          rw [hvd']
        rw [e1, e2] at hvert
        omega
      have hW2 : W.p2 c = (∑ i ∈ Finset.range (W.n + 1), fW (i + 2)) + fW (W.n + 3) + fW 1 + fW 0 := by
        calc W.p2 c = ∑ i ∈ Finset.range (W.n + 4), fW i := hsumW
          _ = ∑ i ∈ Finset.range (W.n + 3), fW (i + 1) + fW 0 := Finset.sum_range_succ' fW (W.n + 3)
          _ = (∑ i ∈ Finset.range (W.n + 2), fW (i + 2)) + fW 1 + fW 0 := by
            rw [Finset.sum_range_succ']
          _ = (∑ i ∈ Finset.range (W.n + 1), fW (i + 2)) + fW (W.n + 3) + fW 1 + fW 0 := by
            rw [Finset.sum_range_succ]
      have hW'2 : W'.p2 c = (∑ i ∈ Finset.range (W.n + 1), fW' i) + fW' (W.n + 1) := by
        have hm : W'.n + 4 = W.n + 2 := by rw [hWn]; omega
        calc W'.p2 c = ∑ i ∈ Finset.range (W'.n + 4), fW' i := hsumW'
          _ = ∑ i ∈ Finset.range (W.n + 2), fW' i := by rw [hm]
          _ = (∑ i ∈ Finset.range (W.n + 1), fW' i) + fW' (W.n + 1) :=
            Finset.sum_range_succ fW' (W.n + 1)
      have hshared : (∑ i ∈ Finset.range (W.n + 1), fW' i) =
          (∑ i ∈ Finset.range (W.n + 1), fW (i + 2)) :=
        Finset.sum_congr rfl (fun j hj => htail j (Finset.mem_range.mp hj))
      rw [hW2, hW'2, hfW0, hfW1, hfWlast, hfW'last, hshared]
      have hclose : ∀ s a b : ZMod 2, (s + a + b + 0) + (s + 0) = a + b := by
        intro s a b
        rcases hkey s with hs | hs <;> rcases hkey a with ha | ha <;> rcases hkey b with hb | hb <;>
          rw [hs, ha, hb] <;> decide
      exact hclose _ _ _
    -- boundary implications
    have hB' : ∀ c : Cell, c ∈ W'.boundary → c ∈ W.boundary ∨ c = (x₀ + 1, ym - 2) := by
      intro c hc
      rw [W'.mem_boundary c] at hc
      rcases hc with ⟨j, hj⟩ | ⟨j, hj⟩
      · left
        rw [← hj]
        exact W.vertex_mem_boundary _
      · by_cases hjl : (j : ℕ) = W.n + 1
        · right
          have hje : j = ⟨W.n + 1, by omega⟩ := Fin.ext hjl
          have hv1 : W'.v j = (x₀, ym - 2) := by rw [hje]; exact hvd'
          have hv2 : W'.v (j + 1) = (x₀ + 2, ym - 2) := by
            have hje2 : j + 1 = (0 : Fin (W.n - 2 + 4)) := by
              apply Fin.ext
              rw [Fin.val_add, Fin.val_one']
              have h1m : 1 % (W.n - 2 + 4) = 1 := Nat.mod_eq_of_lt (by omega)
              rw [h1m, val_zero_fin, hjl]
              have hm : W.n + 1 + 1 = W.n - 2 + 4 := by omega
              rw [hm, Nat.mod_self]
            rw [hje2]
            exact hvr'
          have hm : W'.mid j = (x₀ + 1, ym - 2) := by
            show midPt (W'.v j) (W'.v (j + 1)) = (x₀ + 1, ym - 2)
            rw [hv1, hv2]
            simp only [midPt, Prod.mk.injEq]
            constructor <;> omega
          exact hj.symm.trans hm
        · left
          have hjlt : (j : ℕ) < W.n + 1 := by
            have hlt := j.isLt
            omega
          have e3 : (⟨↑(j + 1) + 2, lt_of_isLt_add (j + 1) (by rw [hWn]; omega)⟩ : Fin (W.n + 4)) =
              (⟨↑j + 2, lt_of_isLt_add j (by rw [hWn]; omega)⟩ : Fin (W.n + 4)) + 1 := by
            apply Fin.ext
            have hvL : ((⟨↑(j + 1) + 2, lt_of_isLt_add (j + 1) (by rw [hWn]; omega)⟩ : Fin (W.n + 4)) : ℕ) =
                ((j + 1 : Fin (W.n - 2 + 4)) : ℕ) + 2 := rfl
            have hv1 : ((j + 1 : Fin (W.n - 2 + 4)) : ℕ) = ↑j + 1 := by
              have hv1' : ((j + 1 : Fin (W.n - 2 + 4)) : ℕ) = (↑j + 1) % (W.n - 2 + 4) := by
                rw [Fin.val_add, Fin.val_one']
                have h1m : 1 % (W.n - 2 + 4) = 1 := Nat.mod_eq_of_lt (by omega)
                rw [h1m]
              rw [hv1', Nat.mod_eq_of_lt (by omega : (↑j : ℕ) + 1 < W.n - 2 + 4)]
            rw [hvL, hv1, Fin.val_add, Fin.val_one']
            have h1m : 1 % (W.n + 4) = 1 := Nat.mod_eq_of_lt (by omega)
            have h2m : (↑j + 2 + 1) % (W.n + 4) = ↑j + 2 + 1 :=
              Nat.mod_eq_of_lt (by omega : (↑j : ℕ) + 3 < W.n + 4)
            rw [h1m, h2m]
          have hm : W'.mid j = W.mid ⟨↑j + 2, by omega⟩ := by
            show midPt (W'.v j) (W'.v (j + 1)) =
              midPt (W.v ⟨↑j + 2, by omega⟩) (W.v (⟨↑j + 2, by omega⟩ + 1))
            rw [← e3]
          rw [hm] at hj
          rw [← hj]
          exact W.mid_mem_boundary _
    have hB : ∀ c : Cell, c ∈ W.boundary → c ∈ W'.boundary ∨
        c ∈ ({(x₀, ym), (x₀ + 2, ym), (x₀ + 1, ym), (x₀ + 2, ym - 1), (x₀, ym - 1)} : Finset Cell) := by
      intro c hc
      rw [W.mem_boundary c] at hc
      rcases hc with ⟨i, hi⟩ | ⟨i, hi⟩
      · by_cases h0i : i = 0
        · right
          rw [h0i, h0] at hi
          rw [← hi]
          exact Finset.mem_insert_self _ _
        · by_cases h1i : i = 1
          · right
            rw [h1i, h1] at hi
            rw [← hi]
            exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
          · left
            have hi0' : (i : ℕ) ≠ 0 := fun h => h0i (Fin.ext h)
            have hi1' : (i : ℕ) ≠ 1 := fun h => h1i (Fin.ext (by rw [val_one_fin]; exact h))
            have hve : W'.v ⟨(i : ℕ) - 2, by omega⟩ = c := by
              show W.v ⟨↑(⟨(i : ℕ) - 2, by omega⟩ : Fin (W.n - 2 + 4)) + 2, by omega⟩ = c
              have e : (⟨(i : ℕ) - 2 + 2, by omega⟩ : Fin (W.n + 4)) = i := by
                apply Fin.ext
                show (i : ℕ) - 2 + 2 = ↑i
                omega
              rw [e]
              exact hi
            rw [← hve]
            exact W'.vertex_mem_boundary _
      · by_cases h0i : i = 0
        · right
          have hm : W.mid i = (x₀ + 1, ym) := by
            show midPt (W.v i) (W.v (i + 1)) = (x₀ + 1, ym)
            rw [h0i]
            have e : (0 + 1 : Fin (W.n + 4)) = 1 := zero_add 1
            rw [e, h0, h1]
            simp only [midPt, Prod.mk.injEq]
            constructor <;> omega
          rw [hm] at hi
          rw [← hi]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
        · by_cases h1i : i = 1
          · right
            have hm : W.mid i = (x₀ + 2, ym - 1) := by
              show midPt (W.v i) (W.v (i + 1)) = (x₀ + 2, ym - 1)
              rw [h1i]
              have e : (1 + 1 : Fin (W.n + 4)) = 2 := by abel
              rw [e, h1, h2]
              simp only [midPt, Prod.mk.injEq]
              constructor <;> omega
            rw [hm] at hi
            rw [← hi]
            exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
              (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
          · by_cases hni : i = ⟨W.n + 3, by omega⟩
            · right
              have hm : W.mid i = (x₀, ym - 1) := by
                show midPt (W.v i) (W.v (i + 1)) = (x₀, ym - 1)
                rw [hni, eS_last, hn1', h0]
                simp only [midPt, Prod.mk.injEq]
                constructor <;> omega
              rw [hm] at hi
              rw [← hi]
              exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
                (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))))
            · left
              have hi0' : (i : ℕ) ≠ 0 := fun h => h0i (Fin.ext h)
              have hi1' : (i : ℕ) ≠ 1 := fun h => h1i (Fin.ext (by rw [val_one_fin]; exact h))
              have hin' : (i : ℕ) ≠ W.n + 3 := fun h => hni (Fin.ext h)
              have hi2 : 2 ≤ (i : ℕ) := by omega
              have hi3 : (i : ℕ) ≤ W.n + 2 := by
                have hlt := i.isLt
                omega
              have e1 : W'.v ⟨(i : ℕ) - 2, by omega⟩ = W.v i := by
                show W.v ⟨↑(⟨(i : ℕ) - 2, by omega⟩ : Fin (W.n - 2 + 4)) + 2, by omega⟩ = W.v i
                have e : (⟨(i : ℕ) - 2 + 2, by omega⟩ : Fin (W.n + 4)) = i := by
                  apply Fin.ext
                  show (i : ℕ) - 2 + 2 = ↑i
                  omega
                rw [e]
              have hv1 : ((⟨(i : ℕ) - 2, by omega⟩ + 1 : Fin (W.n - 2 + 4)) : ℕ) = (i : ℕ) - 1 := by
                have hv1' : ((⟨(i : ℕ) - 2, by omega⟩ + 1 : Fin (W.n - 2 + 4)) : ℕ) =
                    ((i : ℕ) - 2 + 1) % (W.n - 2 + 4) := by
                  rw [Fin.val_add, Fin.val_one']
                  have h1m : 1 % (W.n - 2 + 4) = 1 := Nat.mod_eq_of_lt (by omega)
                  rw [h1m]
                rw [hv1', Nat.mod_eq_of_lt (by omega : (i : ℕ) - 2 + 1 < W.n - 2 + 4)]
                omega
              have hbd2 : (⟨(i : ℕ) - 2, by omega⟩ + 1 : Fin (W.n - 2 + 4)).val + 2 < W.n + 4 := by
                rw [hv1]
                omega
              have e2 : W'.v (⟨(i : ℕ) - 2, by omega⟩ + 1) = W.v (i + 1) := by
                have e : (⟨(⟨(i : ℕ) - 2, by omega⟩ + 1 : Fin (W.n - 2 + 4)).val + 2, hbd2⟩ : Fin (W.n + 4)) =
                    i + 1 := by
                  apply Fin.ext
                  show (⟨(i : ℕ) - 2, by omega⟩ + 1 : Fin (W.n - 2 + 4)).val + 2 =
                    ((i + 1 : Fin (W.n + 4)) : ℕ)
                  rw [hv1]
                  have hv2 : ((i + 1 : Fin (W.n + 4)) : ℕ) = ↑i + 1 := by
                    have hv2' : ((i + 1 : Fin (W.n + 4)) : ℕ) = (↑i + 1) % (W.n + 4) := by
                      rw [Fin.val_add, Fin.val_one']
                      have h1m : 1 % (W.n + 4) = 1 := Nat.mod_eq_of_lt (by omega)
                      rw [h1m]
                    rw [hv2', Nat.mod_eq_of_lt (by omega : (↑i : ℕ) + 1 < W.n + 4)]
                  rw [hv2]
                  omega
                show W.v ⟨(⟨(i : ℕ) - 2, by omega⟩ + 1 : Fin (W.n - 2 + 4)).val + 2, hbd2⟩ = W.v (i + 1)
                rw [e]
              have hme : W'.mid ⟨(i : ℕ) - 2, by omega⟩ = c := by
                show midPt (W'.v ⟨(i : ℕ) - 2, by omega⟩) (W'.v (⟨(i : ℕ) - 2, by omega⟩ + 1)) = c
                rw [e1, e2]
                exact hi
              rw [← hme]
              exact W'.mid_mem_boundary _
    -- the two cells to be lost are not on W's boundary
    have hb1 : (x₀ + 1, ym - 2) ∉ W.boundary := by
      rw [W.mem_boundary (x₀ + 1, ym - 2)]
      push_neg
      constructor
      · intro i hcon
        have hxi : (W.v i).1 = x₀ + 1 := congrArg Prod.fst hcon
        exact hparx1 (hxi ▸ W.parX i)
      · intro i hcon
        rcases W.mid_cases i _ hcon with ⟨hx, h1c, h2c | h2c⟩ | ⟨hy, h1c, h2c | h2c⟩
        · have hc1 : ((x₀ + 1, ym - 2) : Cell).1 = x₀ + 1 := rfl
          have h1x' : (W.v i).1 = x₀ + 1 := by omega
          exact hparx1 (h1x' ▸ W.parX i)
        · have hc1 : ((x₀ + 1, ym - 2) : Cell).1 = x₀ + 1 := rfl
          have h1x' : (W.v i).1 = x₀ + 1 := by omega
          exact hparx1 (h1x' ▸ W.parX i)
        · have hc1 : ((x₀ + 1, ym - 2) : Cell).1 = x₀ + 1 := rfl
          have hc2 : ((x₀ + 1, ym - 2) : Cell).2 = ym - 2 := rfl
          have hvx : (W.v i).1 = x₀ := by omega
          have hvy : (W.v i).2 = ym - 2 := by omega
          have hvi : W.v i = (x₀, ym - 2) := Prod.ext hvx hvy
          have hi2 : i = ⟨W.n + 3, by omega⟩ := hjd i hvi
          have eS : i + 1 = (0 : Fin (W.n + 4)) := by rw [hi2]; exact eS_last
          have hwy : (W.v (i + 1)).2 = ym := by rw [eS]; exact h0y
          omega
        · have hc1 : ((x₀ + 1, ym - 2) : Cell).1 = x₀ + 1 := rfl
          have hc2 : ((x₀ + 1, ym - 2) : Cell).2 = ym - 2 := rfl
          have hvx : (W.v i).1 = x₀ + 2 := by omega
          have hvy : (W.v i).2 = ym - 2 := by omega
          have hvi : W.v i = (x₀ + 2, ym - 2) := Prod.ext hvx hvy
          have hi2 : i = 2 := hjr i hvi
          have hwy : (W.v (i + 1)).2 = ym - 2 := by rw [hy]; exact hvy
          have hmid1 : (W.mid i).1 = ((W.v i).1 + (W.v (i + 1)).1) / 2 := rfl
          have hmc1 : (W.mid i).1 = x₀ + 1 := congrArg Prod.fst hcon
          have hwx : (W.v (i + 1)).1 = x₀ := by
            obtain ⟨q, hq⟩ := W.dvd_add_fst i
            omega
          have hvd : W.v (i + 1) = (x₀, ym - 2) := Prod.ext hwx hwy
          have h3n : i + 1 = ⟨W.n + 3, by omega⟩ := hjd (i + 1) hvd
          rw [hi2] at h3n
          have hv := congrArg Fin.val h3n
          have hv3 : ((2 + 1 : Fin (W.n + 4)) : ℕ) = 3 := by
            rw [Fin.val_add, val_two_fin, Fin.val_one']
            have h1m : 1 % (W.n + 4) = 1 := Nat.mod_eq_of_lt (by omega)
            rw [h1m]
            exact Nat.mod_eq_of_lt (by omega)
          have hvR : ((⟨W.n + 3, by omega⟩ : Fin (W.n + 4)) : ℕ) = W.n + 3 := rfl
          rw [hv3, hvR] at hv
          omega
    have hb2 : (x₀ + 1, ym - 1) ∉ W.boundary := by
      rw [W.mem_boundary (x₀ + 1, ym - 1)]
      push_neg
      constructor
      · intro i hcon
        have hxi : (W.v i).1 = x₀ + 1 := congrArg Prod.fst hcon
        exact hparx1 (hxi ▸ W.parX i)
      · intro i hcon
        rcases W.mid_cases i _ hcon with ⟨hx, h1c, h2c | h2c⟩ | ⟨hy, h1c, h2c | h2c⟩
        · have hc1 : ((x₀ + 1, ym - 1) : Cell).1 = x₀ + 1 := rfl
          have h1x' : (W.v i).1 = x₀ + 1 := by omega
          exact hparx1 (h1x' ▸ W.parX i)
        · have hc1 : ((x₀ + 1, ym - 1) : Cell).1 = x₀ + 1 := rfl
          have h1x' : (W.v i).1 = x₀ + 1 := by omega
          exact hparx1 (h1x' ▸ W.parX i)
        · have hc2 : ((x₀ + 1, ym - 1) : Cell).2 = ym - 1 := rfl
          have hwy : (W.v i).2 = ym - 1 := by omega
          exact hpary1 (hwy ▸ W.parY i)
        · have hc2 : ((x₀ + 1, ym - 1) : Cell).2 = ym - 1 := rfl
          have hwy : (W.v i).2 = ym - 1 := by omega
          exact hpary1 (hwy ▸ W.parY i)
    -- classification of vertical edges spanning [ym-2, ym] with x ≤ x₀+2
    have hyi_gen : ∀ i : Fin (W.n + 4), W.vert i → W.lo i = ym - 2 →
        (W.y i = ym - 2 ∨ W.y i = ym) := by
      intro i hvert hlo
      rcases W.vert_cases i hvert with hy | hy
      · have h1 : W.lo i = W.y i := by
          show min (W.y i) (W.y (i + 1)) = W.y i
          rw [hy]
          exact min_eq_left (by omega)
        left
        rw [h1] at hlo
        exact hlo
      · have h1 : W.lo i = W.y (i + 1) := by
          show min (W.y i) (W.y (i + 1)) = W.y (i + 1)
          rw [hy]
          exact min_eq_right (by omega)
        right
        rw [h1] at hlo
        omega
    have hCE : ∀ i : Fin (W.n + 4), W.vert i → W.lo i = ym - 2 → W.x i ≤ x₀ + 2 →
        i = 1 ∨ i = ⟨W.n + 3, by omega⟩ := by
      intro i hvert hlo hxle
      have hhiM : max (W.y i) (W.y (i + 1)) = ym := by
        have h : max (W.y i) (W.y (i + 1)) = W.lo i + 2 := W.hi_eq_lo_add_two i hvert
        rw [hlo] at h
        rw [h]
        ring
      have hxge : x₀ ≤ W.x i := by
        rcases hyi_gen i hvert hlo with h | h
        · have htop : W.y (i + 1) = ym := by
            rcases W.vert_cases i hvert with hyc | hyc
            · rw [h] at hyc
              omega
            · have hle : W.y (i + 1) ≤ ym := hmax (i + 1)
              omega
          have h2 : x₀ ≤ W.x (i + 1) := hmin (i + 1) htop
          have h3 : W.x (i + 1) = W.x i := hvert
          rw [h3] at h2
          exact h2
        · exact hmin i h
      have hx12 : W.x i = x₀ ∨ W.x i = x₀ + 2 := by
        have hd2 : (2 : ℤ) ∣ (W.x i - x₀) := by
          have hm : ((W.x i - x₀ : ℤ) : ZMod 2) = 0 := by
            push_cast
            rw [W.parX i, hpa, sub_self]
          exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hm
        obtain ⟨t, ht⟩ := hd2
        omega
      rcases hx12 with hx | hx
      · rcases hyi_gen i hvert hlo with hy | hy
        · have hvi : W.v i = (x₀, ym - 2) := Prod.ext hx hy
          exact Or.inr (hjd i hvi)
        · have hvi : W.v i = (x₀, ym) := Prod.ext hx hy
          have hi0 : i = 0 := hj0 i hvi
          have hys : W.y (i + 1) = ym - 2 := by
            rcases W.vert_cases i hvert with hyc | hyc
            · have hle : W.y (i + 1) ≤ ym := hmax (i + 1)
              omega
            · omega
          have e : i + 1 = (1 : Fin (W.n + 4)) := by rw [hi0]; exact zero_add 1
          have hwy : W.y (i + 1) = ym := by rw [e]; exact h1yX
          omega
      · rcases hyi_gen i hvert hlo with hy | hy
        · have hvi : W.v i = (x₀ + 2, ym - 2) := Prod.ext hx hy
          have hi2 : i = 2 := hjr i hvi
          have hys : W.y (i + 1) = ym := by
            rcases W.vert_cases i hvert with hyc | hyc
            · rw [hy] at hyc
              omega
            · have hle : W.y i ≤ ym := hmax i
              omega
          have hvx : W.x (i + 1) = x₀ + 2 := by
            have h3 : W.x (i + 1) = W.x i := hvert
            rw [hx] at h3
            exact h3
          have hvi1 : W.v (i + 1) = (x₀ + 2, ym) := Prod.ext hvx hys
          have h31 : i + 1 = 1 := hj1v (i + 1) hvi1
          have hv := congrArg Fin.val h31
          have e : i + 1 = (3 : Fin (W.n + 4)) := by rw [hi2]; abel
          rw [e, val_three_fin, val_one_fin] at hv
          omega
        · have hvi : W.v i = (x₀ + 2, ym) := Prod.ext hx hy
          exact Or.inl (hj1v i hvi)
    have hF2 : (Finset.univ.filter fun i => W.vert i ∧ W.x i ≤ x₀ + 2 ∧ W.lo i = ym - 2) =
        ({1, ⟨W.n + 3, by omega⟩} : Finset (Fin (W.n + 4))) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hvert, hxle, hlo⟩
        exact hCE i hvert hlo hxle
      · rintro (rfl | rfl)
        · have e11 : (1 + 1 : Fin (W.n + 4)) = 2 := by abel
          refine ⟨?_, ?_, ?_⟩
          · show W.x (1 + 1) = W.x 1
            rw [e11, h2xX, h1xX]
          · rw [h1xX]
          · show min (W.y 1) (W.y (1 + 1)) = ym - 2
            rw [e11, h1yX, h2yX]
            exact min_eq_right (by omega)
        · refine ⟨?_, ?_, ?_⟩
          · show W.x (⟨W.n + 3, by omega⟩ + 1) = W.x ⟨W.n + 3, by omega⟩
            rw [eS_last, h0xX, hdxX]
          · rw [hdxX]
            omega
          · show min (W.y ⟨W.n + 3, by omega⟩) (W.y (⟨W.n + 3, by omega⟩ + 1)) = ym - 2
            rw [eS_last, hdyX, h0yX]
            exact min_eq_left (by omega)
    have hF0 : (Finset.univ.filter fun i => W.vert i ∧ W.x i ≤ x₀ ∧ W.lo i = ym - 2) =
        ({⟨W.n + 3, by omega⟩} : Finset (Fin (W.n + 4))) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨hvert, hxle, hlo⟩
        have h := hCE i hvert hlo (by omega)
        rcases h with h | h
        · rw [h, h1xX] at hxle
          omega
        · exact h
      · rintro rfl
        refine ⟨?_, ?_, ?_⟩
        · show W.x (⟨W.n + 3, by omega⟩ + 1) = W.x ⟨W.n + 3, by omega⟩
          rw [eS_last, h0xX, hdxX]
        · rw [hdxX]
        · show min (W.y ⟨W.n + 3, by omega⟩) (W.y (⟨W.n + 3, by omega⟩ + 1)) = ym - 2
          rw [eS_last, hdyX, h0yX]
          exact min_eq_left (by omega)
    have hF1 : (Finset.univ.filter fun i => W.vert i ∧ W.x i ≤ x₀ + 1 ∧ W.lo i = ym - 2) =
        ({⟨W.n + 3, by omega⟩} : Finset (Fin (W.n + 4))) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨hvert, hxle, hlo⟩
        have h := hCE i hvert hlo (by omega)
        rcases h with h | h
        · rw [h, h1xX] at hxle
          omega
        · exact h
      · rintro rfl
        refine ⟨?_, ?_, ?_⟩
        · show W.x (⟨W.n + 3, by omega⟩ + 1) = W.x ⟨W.n + 3, by omega⟩
          rw [eS_last, h0xX, hdxX]
        · rw [hdxX]
          omega
        · show min (W.y ⟨W.n + 3, by omega⟩) (W.y (⟨W.n + 3, by omega⟩ + 1)) = ym - 2
          rw [eS_last, hdyX, h0yX]
          exact min_eq_left (by omega)
    -- cell evaluations
    have hh2 : ((ym - 2 : ℤ) : ZMod 2) = W.b := by
      push_cast
      rw [show (2 : ZMod 2) = 0 from by decide, sub_zero]
      exact hpb
    have hev_d : W.p2 (x₀, ym - 2) = 1 := by
      rw [W.p2_eq_spanning_le x₀ (ym - 2) hh2, hF0, Finset.card_singleton, Nat.cast_one]
    have hev_dl : W.p2 (x₀ + 1, ym - 2) = 1 := by
      rw [W.p2_eq_spanning_le (x₀ + 1) (ym - 2) hh2, hF1, Finset.card_singleton, Nat.cast_one]
    have hne1n : (1 : Fin (W.n + 4)) ≠ ⟨W.n + 3, by omega⟩ := by
      intro h
      have hv := congrArg Fin.val h
      rw [val_one_fin] at hv
      have hvR : ((⟨W.n + 3, by omega⟩ : Fin (W.n + 4)) : ℕ) = W.n + 3 := rfl
      rw [hvR] at hv
      omega
    have hev_r : W.p2 (x₀ + 2, ym - 2) = 0 := by
      rw [W.p2_eq_spanning_le (x₀ + 2) (ym - 2) hh2, hF2, Finset.card_pair hne1n, Nat.cast_ofNat]
      decide
    have hband : ∀ a : ℤ, W.p2 (a, ym - 2) = W.p2 (a, ym - 1) := by
      intro a
      have h := W.p2_band a (ym - 2) hh2
      rw [show ym - 2 + 1 = (ym - 1 : ℤ) from by ring] at h
      exact h
    have hev_d1 : W.p2 (x₀, ym - 1) = 1 := by rw [← hband x₀]; exact hev_d
    have hev_dl1 : W.p2 (x₀ + 1, ym - 1) = 1 := by rw [← hband (x₀ + 1)]; exact hev_dl
    have hev_r1 : W.p2 (x₀ + 2, ym - 1) = 0 := by rw [← hband (x₀ + 2)]; exact hev_r
    have hflip1 : ∀ a : ℤ, W.p2 (a, ym - 1) + W'.p2 (a, ym - 1) =
        (if a < x₀ then (1 : ZMod 2) else 0) + (if a < x₀ + 2 then (1 : ZMod 2) else 0) := by
      intro a
      have h := hflip (a, ym - 1)
      have hc1 : ((a, ym - 1) : Cell).1 = a := rfl
      have hc2 : ((a, ym - 1) : Cell).2 = ym - 1 := rfl
      have hiff1 : ((a, ym - 1) : Cell).1 < x₀ ∧ ym - 2 ≤ ((a, ym - 1) : Cell).2 ∧
          ((a, ym - 1) : Cell).2 < ym ↔ a < x₀ := by
        constructor
        · intro hh; omega
        · intro hh; refine ⟨by omega, by omega, by omega⟩
      have hiff2 : ((a, ym - 1) : Cell).1 < x₀ + 2 ∧ ym - 2 ≤ ((a, ym - 1) : Cell).2 ∧
          ((a, ym - 1) : Cell).2 < ym ↔ a < x₀ + 2 := by
        constructor
        · intro hh; omega
        · intro hh; refine ⟨by omega, by omega, by omega⟩
      rw [if_congr hiff1 rfl rfl, if_congr hiff2 rfl rfl] at h
      exact h
    have hev_d1' : W'.p2 (x₀, ym - 1) = 0 := by
      have h := hflip1 x₀
      rw [hev_d1, if_neg (by omega : ¬ (x₀ : ℤ) < x₀),
        if_pos (by omega : (x₀ : ℤ) < x₀ + 2)] at h
      rcases hkey (W'.p2 (x₀, ym - 1)) with h0' | h1'
      · exact h0'
      · rw [h1'] at h
        exact absurd h (by decide)
    have hev_dl1' : W'.p2 (x₀ + 1, ym - 1) = 0 := by
      have h := hflip1 (x₀ + 1)
      rw [hev_dl1, if_neg (by omega : ¬ (x₀ + 1 : ℤ) < x₀),
        if_pos (by omega : (x₀ + 1 : ℤ) < x₀ + 2)] at h
      rcases hkey (W'.p2 (x₀ + 1, ym - 1)) with h0' | h1'
      · exact h0'
      · rw [h1'] at h
        exact absurd h (by decide)
    have hev_r1' : W'.p2 (x₀ + 2, ym - 1) = 0 := by
      have h := hflip1 (x₀ + 2)
      rw [hev_r1, if_neg (by omega : ¬ (x₀ + 2 : ℤ) < x₀),
        if_neg (by omega : ¬ (x₀ + 2 : ℤ) < x₀ + 2)] at h
      rcases hkey (W'.p2 (x₀ + 2, ym - 1)) with h0' | h1'
      · exact h0'
      · rw [h1'] at h
        exact absurd h (by decide)
    -- box monotonicity
    have hmaxYe : W.maxY = ym := by
      apply le_antisymm
      · apply Finset.max'_le
        intro y hy
        rw [Finset.mem_image] at hy
        obtain ⟨i, -, rfl⟩ := hy
        exact hmax i
      · have hm : W.y 0 ∈ Finset.univ.image W.y := Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
        have hle : W.y 0 ≤ W.maxY := Finset.le_max' _ _ hm
        exact le_trans (le_of_eq h0yX.symm) hle
    have hminXe : W.minX ≤ x₀ := by
      have hm : W.x 0 ∈ Finset.univ.image W.x := Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
      have hle := Finset.min'_le _ _ hm
      exact le_trans hle (le_of_eq h0xX)
    have hmaxXe : x₀ + 2 ≤ W.maxX := by
      have hm : W.x 1 ∈ Finset.univ.image W.x := Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩
      have hle := Finset.le_max' _ _ hm
      exact le_trans (le_of_eq h1xX.symm) hle
    have hminYe : W.minY ≤ ym - 2 := by
      have hm : W.y 2 ∈ Finset.univ.image W.y := Finset.mem_image.mpr ⟨2, Finset.mem_univ _, rfl⟩
      have hle := Finset.min'_le _ _ hm
      exact le_trans hle (le_of_eq h2yX)
    have himgx : Finset.univ.image W'.x ⊆ Finset.univ.image W.x := by
      intro y hy
      rw [Finset.mem_image] at hy ⊢
      obtain ⟨j, -, rfl⟩ := hy
      exact ⟨⟨↑j + 2, by omega⟩, Finset.mem_univ _, rfl⟩
    have himgy : Finset.univ.image W'.y ⊆ Finset.univ.image W.y := by
      intro y hy
      rw [Finset.mem_image] at hy ⊢
      obtain ⟨j, -, rfl⟩ := hy
      exact ⟨⟨↑j + 2, by omega⟩, Finset.mem_univ _, rfl⟩
    have hminX' : W.minX ≤ W'.minX := by
      have hm : W'.minX ∈ Finset.univ.image W.x := himgx (Finset.min'_mem _ _)
      exact Finset.min'_le _ _ hm
    have hmaxX' : W'.maxX ≤ W.maxX := by
      have hm : W'.maxX ∈ Finset.univ.image W.x := himgx (Finset.max'_mem _ _)
      exact Finset.le_max' _ _ hm
    have hminY' : W.minY ≤ W'.minY := by
      have hm : W'.minY ∈ Finset.univ.image W.y := himgy (Finset.min'_mem _ _)
      exact Finset.min'_le _ _ hm
    have hmaxY'' : W'.maxY ≤ W.maxY := by
      have hm : W'.maxY ∈ Finset.univ.image W.y := himgy (Finset.max'_mem _ _)
      exact Finset.le_max' _ _ hm
    have hmaxY' : W'.maxY ≤ ym := by rw [hmaxYe] at hmaxY''; exact hmaxY''
    -- the sum-of-indicators dichotomy
    have hzhelp : ∀ c : Cell,
        (if c.1 < x₀ ∧ ym - 2 ≤ c.2 ∧ c.2 < ym then (1 : ZMod 2) else 0) +
        (if c.1 < x₀ + 2 ∧ ym - 2 ≤ c.2 ∧ c.2 < ym then (1 : ZMod 2) else 0) = 1 →
        (c.1 = x₀ ∨ c.1 = x₀ + 1) ∧ (c.2 = ym - 2 ∨ c.2 = ym - 1) := by
      intro c h
      by_cases hP : ym - 2 ≤ c.2 ∧ c.2 < ym
      · obtain ⟨hP1, hP2⟩ := hP
        by_cases hcx0 : c.1 < x₀
        · have hcx2 : c.1 < x₀ + 2 := by omega
          rw [if_pos ⟨hcx0, hP1, hP2⟩, if_pos ⟨hcx2, hP1, hP2⟩] at h
          exact absurd h (by decide)
        · by_cases hcx2 : c.1 < x₀ + 2
          · rw [if_neg (fun hh => hcx0 hh.1), if_pos ⟨hcx2, hP1, hP2⟩] at h
            constructor <;> omega
          · rw [if_neg (fun hh => hcx0 hh.1), if_neg (fun hh => hcx2 hh.1)] at h
            exact absurd h (by decide)
      · rw [if_neg (fun hh => hP hh.2), if_neg (fun hh => hP hh.2)] at h
        exact absurd h (by decide)
    -- the interior-set equation
    have hset : W.box.filter (fun c => W.p2 c = 1 ∧ c ∉ W.boundary) =
        W'.box.filter (fun c => W'.p2 c = 1 ∧ c ∉ W'.boundary) ∪
        ({(x₀ + 1, ym - 2), (x₀ + 1, ym - 1)} : Finset Cell) := by
      apply Finset.ext
      intro c
      simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hbox, hp, hb⟩
        by_cases hc2x : c = (x₀ + 1, ym - 2) ∨ c = (x₀ + 1, ym - 1)
        · exact Or.inr hc2x
        · left
          push_neg at hc2x
          have hp2' : W'.p2 c = 1 := by
            have hf := hflip c
            rw [hp] at hf
            rcases hkey (W'.p2 c) with h0' | h1'
            · rw [h0', add_zero] at hf
              rcases hzhelp c hf.symm with ⟨hc1 | hc1, hc2 | hc2⟩
              · have hce : c = (x₀, ym - 2) := Prod.ext
                  (by have hh : ((x₀, ym - 2) : Cell).1 = x₀ := rfl; omega)
                  (by have hh : ((x₀, ym - 2) : Cell).2 = ym - 2 := rfl; omega)
                rw [hce] at hb
                exact absurd hbd hb
              · have hce : c = (x₀, ym - 1) := Prod.ext
                  (by have hh : ((x₀, ym - 1) : Cell).1 = x₀ := rfl; omega)
                  (by have hh : ((x₀, ym - 1) : Cell).2 = ym - 1 := rfl; omega)
                rw [hce] at hb
                exact absurd hbx0 hb
              · have hce : c = (x₀ + 1, ym - 2) := Prod.ext
                  (by have hh : ((x₀ + 1, ym - 2) : Cell).1 = x₀ + 1 := rfl; omega)
                  (by have hh : ((x₀ + 1, ym - 2) : Cell).2 = ym - 2 := rfl; omega)
                exact absurd hce hc2x.1
              · have hce : c = (x₀ + 1, ym - 1) := Prod.ext
                  (by have hh : ((x₀ + 1, ym - 1) : Cell).1 = x₀ + 1 := rfl; omega)
                  (by have hh : ((x₀ + 1, ym - 1) : Cell).2 = ym - 1 := rfl; omega)
                exact absurd hce hc2x.2
            · exact h1'
          have hbnd' : c ∉ W'.boundary := by
            intro hcb
            rcases hB' c hcb with hbb | hce
            · exact hb hbb
            · exact hc2x.1 hce
          have hbox' : c ∈ W'.box := by
            rw [box, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
            refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
            · by_contra hcc
              push_neg at hcc
              rw [W'.p2_eq_zero_of_le_minX hcc] at hp2'
              exact absurd hp2' (by decide)
            · by_contra hcc
              push_neg at hcc
              have h2 : W'.maxX ≤ c.1 := by omega
              rw [W'.p2_eq_zero_of_maxX_le h2] at hp2'
              exact absurd hp2' (by decide)
            · by_contra hcc
              push_neg at hcc
              rw [W'.p2_eq_zero_of_minY hcc] at hp2'
              exact absurd hp2' (by decide)
            · by_contra hcc
              push_neg at hcc
              have h2 : W'.maxY ≤ c.2 := by omega
              rw [W'.p2_eq_zero_of_maxY h2] at hp2'
              exact absurd hp2' (by decide)
          exact ⟨hbox', hp2', hbnd'⟩
      · rintro (⟨hbox, hp, hb⟩ | hc2x)
        · have hboxW : c ∈ W.box := by
            rw [box, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hbox ⊢
            obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hbox
            exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
          have hp2 : W.p2 c = 1 := by
            have hf := hflip c
            rw [hp] at hf
            rcases hkey (W.p2 c) with h0' | h1'
            · rw [h0', zero_add] at hf
              rcases hzhelp c hf.symm with ⟨hc1 | hc1, hc2 | hc2⟩
              · have hce : c = (x₀, ym - 2) := Prod.ext
                  (by have hh : ((x₀, ym - 2) : Cell).1 = x₀ := rfl; omega)
                  (by have hh : ((x₀, ym - 2) : Cell).2 = ym - 2 := rfl; omega)
                rw [hce] at hb
                exact absurd hbd' hb
              · have hce : c = (x₀, ym - 1) := Prod.ext
                  (by have hh : ((x₀, ym - 1) : Cell).1 = x₀ := rfl; omega)
                  (by have hh : ((x₀, ym - 1) : Cell).2 = ym - 1 := rfl; omega)
                rw [hce] at hp
                rw [hev_d1'] at hp
                exact absurd hp (by decide)
              · have hce : c = (x₀ + 1, ym - 2) := Prod.ext
                  (by have hh : ((x₀ + 1, ym - 2) : Cell).1 = x₀ + 1 := rfl; omega)
                  (by have hh : ((x₀ + 1, ym - 2) : Cell).2 = ym - 2 := rfl; omega)
                rw [hce] at hb
                exact absurd hbm' hb
              · have hce : c = (x₀ + 1, ym - 1) := Prod.ext
                  (by have hh : ((x₀ + 1, ym - 1) : Cell).1 = x₀ + 1 := rfl; omega)
                  (by have hh : ((x₀ + 1, ym - 1) : Cell).2 = ym - 1 := rfl; omega)
                rw [hce] at hp
                rw [hev_dl1'] at hp
                exact absurd hp (by decide)
            · exact h1'
          have hbnd : c ∉ W.boundary := by
            intro hcb
            rcases hB c hcb with hb' | h5
            · exact hb hb'
            · simp only [Finset.mem_insert, Finset.mem_singleton] at h5
              rcases h5 with hce | hce | hce | hce | hce
              · rw [hce] at hp
                have hz := W'.p2_eq_zero_of_maxY (c := (x₀, ym)) hmaxY'
                rw [hz] at hp
                exact absurd hp (by decide)
              · rw [hce] at hp
                have hz := W'.p2_eq_zero_of_maxY (c := (x₀ + 2, ym)) hmaxY'
                rw [hz] at hp
                exact absurd hp (by decide)
              · rw [hce] at hp
                have hz := W'.p2_eq_zero_of_maxY (c := (x₀ + 1, ym)) hmaxY'
                rw [hz] at hp
                exact absurd hp (by decide)
              · rw [hce] at hp
                rw [hev_r1'] at hp
                exact absurd hp (by decide)
              · rw [hce] at hp
                rw [hev_d1'] at hp
                exact absurd hp (by decide)
          exact ⟨hboxW, hp2, hbnd⟩
        · rcases hc2x with hce | hce
          · have hboxm : (x₀ + 1, ym - 2) ∈ W.box := by
              rw [box, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
              exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
            rw [hce]
            exact ⟨hboxm, hev_dl, hb1⟩
          · have hboxm : (x₀ + 1, ym - 1) ∈ W.box := by
              rw [box, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
              exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
            rw [hce]
            exact ⟨hboxm, hev_dl1, hb2⟩
    have hne12 : (x₀ + 1, ym - 2) ≠ (x₀ + 1, ym - 1) := by
      intro h
      have := (Prod.mk.injEq ..).mp h
      omega
    have hdisj : Disjoint (W'.box.filter fun c => W'.p2 c = 1 ∧ c ∉ W'.boundary)
        ({(x₀ + 1, ym - 2), (x₀ + 1, ym - 1)} : Finset Cell) := by
      rw [Finset.disjoint_left]
      intro c hc hc2
      rw [Finset.mem_filter] at hc
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc2
      rcases hc2 with hce | hce
      · rw [hce] at hc
        exact hc.2.2 hbm'
      · rw [hce] at hc
        rw [hev_dl1'] at hc
        exact absurd hc.2.1 (by decide)
    have hcard : (W.box.filter fun c => W.p2 c = 1 ∧ c ∉ W.boundary).card =
        (W'.box.filter fun c => W'.p2 c = 1 ∧ c ∉ W'.boundary).card + 2 := by
      rw [hset, Finset.card_union_of_disjoint hdisj, Finset.card_pair hne12]
    rw [W.I_eq, W'.I_eq, hcard]

set_option maxHeartbeats 800000 in
theorem peelLoop_T (W : OrthoLoop) (x₀ ym : ℤ) (h0 : W.v 0 = (x₀, ym))
    (h1 : W.v 1 = (x₀ + 2, ym)) (h2 : W.v 2 = (x₀ + 2, ym - 2))
    (hn1 : W.v (-1) = (x₀, ym - 2)) (hn : 2 ≤ W.n) :
    ({ a := W.a, b := W.b, n := W.n - 2, v := fun j : Fin (W.n - 2 + 4) => W.v ⟨j + 2, by omega⟩, inj := peelLoop_inj W hn, step := peelLoop_step W x₀ ym h2 hn1 hn, par := peelLoop_par W hn, simple := peelLoop_simple W x₀ ym h0 h2 hn1 hn } : OrthoLoop).T = W.T + 4 := by
  classical
  set W' := ({ a := W.a, b := W.b, n := W.n - 2, v := fun j : Fin (W.n - 2 + 4) => W.v ⟨j + 2, by omega⟩, inj := peelLoop_inj W hn, step := peelLoop_step W x₀ ym h2 hn1 hn, par := peelLoop_par W hn, simple := peelLoop_simple W x₀ ym h0 h2 hn1 hn } : OrthoLoop)
  have hWn : W'.n = W.n - 2 := rfl
  have hn1' := peel_hn1' W x₀ ym hn1
  · -- T: W'.T = W.T + 4
    -- natural-number indexed edge terms to ease sum manipulation
    let wW : ℕ → ℤ := fun i =>
      if h : i < W.n + 4 then (W.v ⟨i, h⟩).1 * (W.v ⟨(i + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩).2 -
        (W.v ⟨(i + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩).1 * (W.v ⟨i, h⟩).2 else 0
    let wW' : ℕ → ℤ := fun j =>
      if h : j < W'.n + 4 then (W'.v ⟨j, h⟩).1 * (W'.v ⟨(j + 1) % (W'.n + 4), Nat.mod_lt _ (by omega)⟩).2 -
        (W'.v ⟨(j + 1) % (W'.n + 4), Nat.mod_lt _ (by omega)⟩).1 * (W'.v ⟨j, h⟩).2 else 0
    have hwW : ∀ i : Fin (W.n + 4), W.x i * W.y (i + 1) - W.x (i + 1) * W.y i = wW ↑i := by
      intro i
      have hi : ↑i < W.n + 4 := i.isLt
      have h1 : (⟨(↑i + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ : Fin (W.n + 4)) = i + 1 := by
        apply Fin.ext
        rw [Fin.val_add, Fin.val_one']
        have h1m : 1 % (W.n + 4) = 1 := Nat.mod_eq_of_lt (by omega)
        rw [h1m]
      have hi2 : (⟨↑i, hi⟩ : Fin (W.n + 4)) = i := Fin.ext rfl
      show W.x i * W.y (i + 1) - W.x (i + 1) * W.y i =
        if h : ↑i < W.n + 4 then (W.v ⟨↑i, h⟩).1 * (W.v ⟨(↑i + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩).2 -
          (W.v ⟨(↑i + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩).1 * (W.v ⟨↑i, h⟩).2 else 0
      rw [dif_pos hi, hi2, h1, OrthoLoop.x, OrthoLoop.y]
    have hwW' : ∀ j : Fin (W'.n + 4), W'.x j * W'.y (j + 1) - W'.x (j + 1) * W'.y j = wW' ↑j := by
      intro j
      have hj : ↑j < W'.n + 4 := j.isLt
      have h1 : (⟨(↑j + 1) % (W'.n + 4), Nat.mod_lt _ (by omega)⟩ : Fin (W'.n + 4)) = j + 1 := by
        apply Fin.ext
        rw [Fin.val_add, Fin.val_one']
        have h1m : 1 % (W'.n + 4) = 1 := Nat.mod_eq_of_lt (by omega)
        rw [h1m]
      have hi2 : (⟨↑j, hj⟩ : Fin (W'.n + 4)) = j := Fin.ext rfl
      show W'.x j * W'.y (j + 1) - W'.x (j + 1) * W'.y j =
        if h : ↑j < W'.n + 4 then (W'.v ⟨↑j, h⟩).1 * (W'.v ⟨(↑j + 1) % (W'.n + 4), Nat.mod_lt _ (by omega)⟩).2 -
          (W'.v ⟨(↑j + 1) % (W'.n + 4), Nat.mod_lt _ (by omega)⟩).1 * (W'.v ⟨↑j, h⟩).2 else 0
      rw [dif_pos hj, hi2, h1, OrthoLoop.x, OrthoLoop.y]
    have hshift : ∀ j : ℕ, j < W.n + 1 → wW' j = wW (j + 2) := by
      intro j hj
      have hjW : j + 2 < W.n + 4 := by omega
      have hjW' : j < W'.n + 4 := by
        show j < W.n - 2 + 4
        omega
      show (if h : j < W'.n + 4 then (W'.v ⟨j, h⟩).1 * (W'.v ⟨(j + 1) % (W'.n + 4), Nat.mod_lt _ (by omega)⟩).2 -
          (W'.v ⟨(j + 1) % (W'.n + 4), Nat.mod_lt _ (by omega)⟩).1 * (W'.v ⟨j, h⟩).2 else 0)
        = if h : j + 2 < W.n + 4 then (W.v ⟨j + 2, h⟩).1 * (W.v ⟨(j + 2 + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩).2 -
          (W.v ⟨(j + 2 + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩).1 * (W.v ⟨j + 2, h⟩).2 else 0
      rw [dif_pos hjW', dif_pos hjW]
      have e1 : W'.v ⟨j, hjW'⟩ = W.v ⟨j + 2, hjW⟩ := rfl
      have e2 : W'.v ⟨(j + 1) % (W'.n + 4), Nat.mod_lt _ (by omega)⟩ = W.v ⟨(j + 2 + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ := by
        have hm : W'.n + 4 = W.n + 2 := by rw [hWn]; omega
        have e2a : (⟨(j + 1) % (W'.n + 4), Nat.mod_lt _ (by omega)⟩ : Fin (W'.n + 4)) = ⟨j + 1, by omega⟩ := by
          apply Fin.ext
          show (⟨(j + 1) % (W'.n + 4), Nat.mod_lt _ (by omega)⟩ : Fin (W'.n + 4)).val =
            (⟨j + 1, by omega⟩ : Fin (W'.n + 4)).val
          show (j + 1) % (W'.n + 4) = j + 1
          rw [hm]
          exact Nat.mod_eq_of_lt (by omega)
        have e2b : (⟨(j + 2 + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ : Fin (W.n + 4)) = ⟨j + 3, by omega⟩ := by
          apply Fin.ext
          show (⟨(j + 2 + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ : Fin (W.n + 4)).val =
            (⟨j + 3, by omega⟩ : Fin (W.n + 4)).val
          show (j + 2 + 1) % (W.n + 4) = j + 3
          rw [Nat.mod_eq_of_lt (by omega : j + 3 < W.n + 4)]
        rw [e2a, e2b]
      rw [e1, e2]
    have hwrap : wW' (W.n + 1) = x₀ * (ym - 2) - (x₀ + 2) * (ym - 2) := by
      have hj : W.n + 1 < W'.n + 4 := by
        show W.n + 1 < W.n - 2 + 4
        omega
      show (if h : W.n + 1 < W'.n + 4 then (W'.v ⟨W.n + 1, h⟩).1 *
          (W'.v ⟨(W.n + 1 + 1) % (W'.n + 4), Nat.mod_lt _ (by omega)⟩).2 -
          (W'.v ⟨(W.n + 1 + 1) % (W'.n + 4), Nat.mod_lt _ (by omega)⟩).1 * (W'.v ⟨W.n + 1, h⟩).2 else 0)
        = x₀ * (ym - 2) - (x₀ + 2) * (ym - 2)
      rw [dif_pos hj]
      have e1 : W'.v ⟨W.n + 1, hj⟩ = (x₀, ym - 2) := by
        show W.v ⟨(W.n + 1 : ℕ) + 2, by omega⟩ = (x₀, ym - 2)
        have e1a : (⟨(W.n + 1 : ℕ) + 2, by omega⟩ : Fin (W.n + 4)) = ⟨W.n + 3, by omega⟩ := by
          apply Fin.ext
          simp
        rw [e1a]
        exact hn1'
      have e2 : W'.v ⟨(W.n + 1 + 1) % (W'.n + 4), Nat.mod_lt _ (by omega)⟩ = (x₀ + 2, ym - 2) := by
        have hm : W'.n + 4 = W.n + 2 := by rw [hWn]; omega
        have hmod : (W.n + 1 + 1) % (W'.n + 4) = 0 := by
          rw [hm]
          have hm2 : W.n + 1 + 1 = W.n + 2 := by omega
          rw [hm2, Nat.mod_self]
        have e2a : (⟨(W.n + 1 + 1) % (W'.n + 4), Nat.mod_lt _ (by omega)⟩ : Fin (W'.n + 4)) = 0 := by
          apply Fin.ext
          show (⟨(W.n + 1 + 1) % (W'.n + 4), Nat.mod_lt _ (by omega)⟩ : Fin (W'.n + 4)).val =
            ((0 : Fin (W'.n + 4)) : ℕ)
          rw [val_zero_fin]
          show (W.n + 1 + 1) % (W'.n + 4) = 0
          rw [hm]
          have hm2 : W.n + 1 + 1 = W.n + 2 := by omega
          rw [hm2, Nat.mod_self]
        rw [e2a]
        have e2b : W'.v 0 = W.v 2 := rfl
        rw [e2b, h2]
      rw [e1, e2]
    have hw0 : wW 0 = x₀ * ym - (x₀ + 2) * ym := by
      have hi : (0 : ℕ) < W.n + 4 := by omega
      show (if h : (0 : ℕ) < W.n + 4 then (W.v ⟨0, h⟩).1 * (W.v ⟨(0 + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩).2 -
          (W.v ⟨(0 + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩).1 * (W.v ⟨0, h⟩).2 else 0)
        = x₀ * ym - (x₀ + 2) * ym
      rw [dif_pos hi]
      have e1 : W.v ⟨0, hi⟩ = (x₀, ym) := by
        have e1a : (⟨0, hi⟩ : Fin (W.n + 4)) = 0 := by
          apply Fin.ext
          simp [val_zero_fin]
        rw [e1a, h0]
      have e2 : W.v ⟨(0 + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ = (x₀ + 2, ym) := by
        have hmod : (0 + 1) % (W.n + 4) = 1 := by
          have : 1 < W.n + 4 := by omega
          exact Nat.mod_eq_of_lt this
        have e2a : (⟨(0 + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ : Fin (W.n + 4)) = 1 := by
          apply Fin.ext
          show (⟨(0 + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ : Fin (W.n + 4)).val =
            ((1 : Fin (W.n + 4)) : ℕ)
          rw [val_one_fin]
          show (0 + 1) % (W.n + 4) = 1
          exact Nat.mod_eq_of_lt (by omega)
        rw [e2a]
        have e2b : W.v 1 = (x₀ + 2, ym) := h1
        exact e2b
      rw [e1, e2]
    have hw1 : wW 1 = (x₀ + 2) * (ym - 2) - (x₀ + 2) * ym := by
      have hi : (1 : ℕ) < W.n + 4 := by omega
      show (if h : (1 : ℕ) < W.n + 4 then (W.v ⟨1, h⟩).1 * (W.v ⟨(1 + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩).2 -
          (W.v ⟨(1 + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩).1 * (W.v ⟨1, h⟩).2 else 0)
        = (x₀ + 2) * (ym - 2) - (x₀ + 2) * ym
      rw [dif_pos hi]
      have e1 : W.v ⟨1, hi⟩ = (x₀ + 2, ym) := by
        have e1a : (⟨1, hi⟩ : Fin (W.n + 4)) = 1 := by
          apply Fin.ext
          simp [val_one_fin]
        rw [e1a, h1]
      have e2 : W.v ⟨(1 + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ = (x₀ + 2, ym - 2) := by
        have hmod : (1 + 1) % (W.n + 4) = 2 := by
          have : 2 < W.n + 4 := by omega
          exact Nat.mod_eq_of_lt this
        have e2a : (⟨(1 + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ : Fin (W.n + 4)) = 2 := by
          apply Fin.ext
          show (⟨(1 + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ : Fin (W.n + 4)).val =
            ((2 : Fin (W.n + 4)) : ℕ)
          rw [val_two_fin]
          show (1 + 1) % (W.n + 4) = 2
          exact Nat.mod_eq_of_lt (by omega)
        rw [e2a, h2]
      rw [e1, e2]
    have hwlast : wW (W.n + 3) = x₀ * ym - x₀ * (ym - 2) := by
      have hi : W.n + 3 < W.n + 4 := by omega
      show (if h : W.n + 3 < W.n + 4 then (W.v ⟨W.n + 3, h⟩).1 *
          (W.v ⟨(W.n + 3 + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩).2 -
          (W.v ⟨(W.n + 3 + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩).1 * (W.v ⟨W.n + 3, h⟩).2 else 0)
        = x₀ * ym - x₀ * (ym - 2)
      rw [dif_pos hi]
      rw [hn1']
      have e2 : W.v ⟨(W.n + 3 + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ = (x₀, ym) := by
        have hmod : (W.n + 3 + 1) % (W.n + 4) = 0 := by
          have hm : W.n + 3 + 1 = W.n + 4 := by omega
          rw [hm, Nat.mod_self]
        have e2a : (⟨(W.n + 3 + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ : Fin (W.n + 4)) = 0 := by
          apply Fin.ext
          show (⟨(W.n + 3 + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ : Fin (W.n + 4)).val =
            ((0 : Fin (W.n + 4)) : ℕ)
          rw [val_zero_fin]
          show (W.n + 3 + 1) % (W.n + 4) = 0
          have hm : W.n + 3 + 1 = W.n + 4 := by omega
          rw [hm, Nat.mod_self]
        rw [e2a, h0]
      rw [e2]
    have h2W := W.two_mul_T
    have h2W' := W'.two_mul_T
    -- express both sums over ranges
    have hWsum : 2 * W.T = wW 0 + wW 1 + (∑ i ∈ Finset.range (W.n + 1), wW (i + 2)) + wW (W.n + 3) := by
      rw [h2W]
      have hss : ∑ i : Fin (W.n + 4), (W.x i * W.y (i + 1) - W.x (i + 1) * W.y i) =
          ∑ i : Fin (W.n + 4), wW ↑i := by
        apply Finset.sum_congr rfl
        intro i _
        exact hwW i
      rw [hss, Fin.sum_univ_eq_sum_range wW (W.n + 4)]
      rw [Finset.sum_range_succ, Finset.sum_range_succ', Finset.sum_range_succ']
      have e1 : (0 : ℕ) + 1 = 1 := rfl
      have e2 : ∀ i : ℕ, (i + 1) + 1 = i + 2 := fun i => by omega
      rw [e1]
      simp only [e2]
      abel
    have hW'sum : 2 * W'.T = (∑ i ∈ Finset.range (W.n + 1), wW' i) + wW' (W.n + 1) := by
      rw [h2W']
      have hss : ∑ j : Fin (W'.n + 4), (W'.x j * W'.y (j + 1) - W'.x (j + 1) * W'.y j) =
          ∑ j : Fin (W'.n + 4), wW' ↑j := by
        apply Finset.sum_congr rfl
        intro j _
        exact hwW' j
      rw [hss, Fin.sum_univ_eq_sum_range wW' (W'.n + 4)]
      have hL : W'.n + 4 = W.n + 2 := by rw [hWn]; omega
      rw [hL, Finset.sum_range_succ]
    have hmid : (∑ i ∈ Finset.range (W.n + 1), wW' i) = (∑ i ∈ Finset.range (W.n + 1), wW (i + 2)) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      exact hshift j hj
    have hT2 : 2 * W'.T = 2 * W.T + 8 := by
      rw [hW'sum, hWsum, hmid, hwrap, hw0, hw1, hwlast]
      ring
    omega

set_option maxHeartbeats 800000 in
/-- Case (B): peel off a convex 2×2 block, deleting `v` and `r`. -/
theorem peel_case (W : OrthoLoop) (x₀ ym : ℤ)
    (h0 : W.v 0 = (x₀, ym)) (hmax : ∀ i, (W.v i).2 ≤ ym)
    (hmin : ∀ i, (W.v i).2 = ym → x₀ ≤ (W.v i).1)
    (h1 : W.v 1 = (x₀ + 2, ym)) (h2 : W.v 2 = (x₀ + 2, ym - 2))
    (hn1 : W.v (-1) = (x₀, ym - 2)) (hn : 2 ≤ W.n)
    (hd : W.v (-2) ≠ (x₀ + 2, ym - 2)) :
    ∃ W' : OrthoLoop, W'.I + 2 = W.I ∧ W'.T = W.T + 4 ∧ W'.L + 2 = W.L := by
  classical
  refine ⟨({ a := W.a, b := W.b, n := W.n - 2, v := fun j : Fin (W.n - 2 + 4) => W.v ⟨j + 2, by omega⟩, inj := peelLoop_inj W hn, step := peelLoop_step W x₀ ym h2 hn1 hn, par := peelLoop_par W hn, simple := peelLoop_simple W x₀ ym h0 h2 hn1 hn } : OrthoLoop), peelLoop_I W x₀ ym h0 hmax hmin h1 h2 hn1 hn,
    peelLoop_T W x₀ ym h0 h1 h2 hn1 hn, ?_⟩
  show (W.n - 2 + 4) + 2 = W.n + 4
  omega

theorem push_hpa (W : OrthoLoop) (x₀ ym : ℤ) (h0 : W.v 0 = (x₀, ym)) :
    (x₀ : ZMod 2) = W.a := by
  have h0x : (W.v 0).1 = x₀ := congrArg Prod.fst h0
  rw [← h0x]; exact W.parX 0

theorem push_hpb (W : OrthoLoop) (x₀ ym : ℤ) (h0 : W.v 0 = (x₀, ym)) :
    (ym : ZMod 2) = W.b := by
  have h0y : (W.v 0).2 = ym := congrArg Prod.snd h0
  rw [← h0y]; exact W.parY 0

theorem push_hn1' (W : OrthoLoop) (x₀ ym : ℤ) (hn1 : W.v (-1) = (x₀, ym - 2)) :
    W.v ⟨W.n + 3, by omega⟩ = (x₀, ym - 2) := by
  have e : (⟨W.n + 3, by omega⟩ : Fin (W.n + 4)) = (-1 : Fin (W.n + 4)) := by
    apply Fin.ext
    simp [val_neg_one_fin]
  rw [e]
  exact hn1

theorem push_hkey : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide

theorem push_hparx1 (W : OrthoLoop) (x₀ ym : ℤ) (h0 : W.v 0 = (x₀, ym)) :
    ((x₀ + 1 : ℤ) : ZMod 2) ≠ W.a := by
  rw [← push_hpa W x₀ ym h0]
  push_cast
  rcases push_hkey (x₀ : ZMod 2) with h | h <;> rw [h] <;> decide

theorem push_hparx2 (W : OrthoLoop) (x₀ ym : ℤ) (h0 : W.v 0 = (x₀, ym)) :
    ((x₀ - 1 : ℤ) : ZMod 2) ≠ W.a := by
  rw [← push_hpa W x₀ ym h0]
  push_cast
  rcases push_hkey (x₀ : ZMod 2) with h | h <;> rw [h] <;> decide

theorem push_hparx3 (W : OrthoLoop) (x₀ ym : ℤ) (h0 : W.v 0 = (x₀, ym)) :
    ((x₀ + 3 : ℤ) : ZMod 2) ≠ W.a := by
  rw [← push_hpa W x₀ ym h0]
  push_cast
  rcases push_hkey (x₀ : ZMod 2) with h | h <;> rw [h] <;> decide

theorem push_hpary1 (W : OrthoLoop) (x₀ ym : ℤ) (h0 : W.v 0 = (x₀, ym)) :
    ((ym - 1 : ℤ) : ZMod 2) ≠ W.b := by
  rw [← push_hpb W x₀ ym h0]
  push_cast
  rcases push_hkey (ym : ZMod 2) with h | h <;> rw [h] <;> decide

theorem push_hpary3 (W : OrthoLoop) (x₀ ym : ℤ) (h0 : W.v 0 = (x₀, ym)) :
    ((ym - 3 : ℤ) : ZMod 2) ≠ W.b := by
  rw [← push_hpb W x₀ ym h0]
  push_cast
  rcases push_hkey (ym : ZMod 2) with h | h <;> rw [h] <;> decide

theorem push_hparyp1 (W : OrthoLoop) (x₀ ym : ℤ) (h0 : W.v 0 = (x₀, ym)) :
    ((ym + 1 : ℤ) : ZMod 2) ≠ W.b := by
  rw [← push_hpb W x₀ ym h0]
  push_cast
  rcases push_hkey (ym : ZMod 2) with h | h <;> rw [h] <;> decide

theorem push_eS_last (W : OrthoLoop) :
    (⟨W.n + 3, by omega⟩ + 1 : Fin (W.n + 4)) = 0 := by
  apply Fin.ext
  rw [Fin.val_add, Fin.val_one']
  have h1m : 1 % (W.n + 4) = 1 := Nat.mod_eq_of_lt (by omega)
  rw [h1m, val_zero_fin]
  have hm : W.n + 3 + 1 = W.n + 4 := by omega
  rw [hm, Nat.mod_self]

theorem push_h1ne0 (W : OrthoLoop) : (1 : Fin (W.n + 4)) ≠ 0 := by
  intro h
  have hv := congrArg Fin.val h
  rw [val_one_fin, val_zero_fin] at hv
  omega

theorem push_hn3ne (W : OrthoLoop) : (⟨W.n + 3, by omega⟩ : Fin (W.n + 4)) ≠ 0 := by
  intro h
  have hv := congrArg Fin.val h
  have hvL : ((⟨W.n + 3, by omega⟩ : Fin (W.n + 4)) : ℕ) = W.n + 3 := rfl
  rw [hvL, val_zero_fin] at hv
  omega

theorem push_hsucc_ne (W : OrthoLoop) :
    ∀ i : Fin (W.n + 4), i ≠ ⟨W.n + 3, by omega⟩ → i + 1 ≠ 0 := by
  intro i hin h0'
  have hi3 : (i : ℕ) = W.n + 3 := by
    have hv := congrArg Fin.val h0'
    rw [Fin.val_add, Fin.val_one'] at hv
    have h1m : 1 % (W.n + 4) = 1 := Nat.mod_eq_of_lt (by omega)
    rw [h1m, val_zero_fin] at hv
    have hilt := i.isLt
    by_cases hc : (i : ℕ) + 1 = W.n + 4
    · omega
    · rw [Nat.mod_eq_of_lt (by omega : (i : ℕ) + 1 < W.n + 4)] at hv
      omega
  exact hin (Fin.ext hi3)

theorem push_hE0 (W : OrthoLoop) (x₀ ym : ℤ) (h0 : W.v 0 = (x₀, ym))
    (h1 : W.v 1 = (x₀ + 2, ym)) (hr : ∀ i, W.v i ≠ (x₀ + 2, ym - 2)) :
    ∀ (k : Fin (W.n + 4)), 2 ≤ (k : ℕ) → (k : ℕ) ≤ W.n + 2 →
      Disjoint ({(x₀ + 2, ym - 2), (x₀ + 2, ym - 1), (x₀ + 2, ym)} : Finset Cell)
        (W.edgePts k) := by
  classical
  have hparx1 := push_hparx1 W x₀ ym h0
  have hparx3 := push_hparx3 W x₀ ym h0
  have hpary1 := push_hpary1 W x₀ ym h0
  have hpary3 := push_hpary3 W x₀ ym h0
  have hparyp1 := push_hparyp1 W x₀ ym h0
  have hjr1 : ∀ j : Fin (W.n + 4), W.v j = (x₀ + 2, ym) → j = 1 :=
    fun j hj => W.inj (hj.trans h1.symm)
  intro k hk2 hkn
  rw [Finset.disjoint_left]
  intro c hc hc'
  simp only [Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with rfl | rfl | rfl
  · -- c = r′
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc'
    rcases hc' with h | h | h
    · exact absurd h.symm (hr k)
    · rcases W.mid_cases k _ h.symm with ⟨hx, h1c, h2c | h2c⟩ | ⟨hy, h1c, h2c | h2c⟩
      · have hyk : (W.v k).2 = ym - 3 := by
          have hc2 : ((x₀ + 2, ym - 2) : Cell).2 = ym - 2 := rfl
          omega
        exact hpary3 (hyk ▸ W.parY k)
      · have hyk : (W.v k).2 = ym - 1 := by
          have hc2 : ((x₀ + 2, ym - 2) : Cell).2 = ym - 2 := rfl
          omega
        exact hpary1 (hyk ▸ W.parY k)
      · have h1' : (W.v k).1 = x₀ + 1 := by
          have hc1 : ((x₀ + 2, ym - 2) : Cell).1 = x₀ + 2 := rfl
          omega
        exact hparx1 (h1' ▸ W.parX k)
      · have h1' : (W.v k).1 = x₀ + 3 := by
          have hc1 : ((x₀ + 2, ym - 2) : Cell).1 = x₀ + 2 := rfl
          omega
        exact hparx3 (h1' ▸ W.parX k)
    · exact absurd h.symm (hr (k + 1))
  · -- c = (x₀+2, ym-1)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc'
    rcases hc' with h | h | h
    · have hyk : (W.v k).2 = ym - 1 := (congrArg Prod.snd h).symm
      exact hpary1 (hyk ▸ W.parY k)
    · rcases W.mid_cases k _ h.symm with ⟨hx, h1c, h2c | h2c⟩ | ⟨hy, h1c, h2c | h2c⟩
      · have hvy : (W.v k).2 = ym - 2 := by
          have hc2 : ((x₀ + 2, ym - 1) : Cell).2 = ym - 1 := rfl
          omega
        have hvx : (W.v k).1 = x₀ + 2 := h1c.symm
        exact absurd (Prod.ext hvx hvy) (hr k)
      · have hvy : (W.v k).2 = ym := by
          have hc2 : ((x₀ + 2, ym - 1) : Cell).2 = ym - 1 := rfl
          omega
        have hvx : (W.v k).1 = x₀ + 2 := h1c.symm
        have hk1 : k = 1 := hjr1 k (Prod.ext hvx hvy)
        have hv := congrArg Fin.val hk1
        rw [val_one_fin] at hv
        omega
      · have hyk : (W.v k).2 = ym - 1 := h1c.symm
        exact hpary1 (hyk ▸ W.parY k)
      · have hyk : (W.v k).2 = ym - 1 := h1c.symm
        exact hpary1 (hyk ▸ W.parY k)
    · have hyk : (W.v (k + 1)).2 = ym - 1 := (congrArg Prod.snd h).symm
      exact hpary1 (hyk ▸ W.parY (k + 1))
  · -- c = r
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc'
    rcases hc' with h | h | h
    · have hk1 : k = 1 := hjr1 k h.symm
      have hv := congrArg Fin.val hk1
      rw [val_one_fin] at hv
      omega
    · rcases W.mid_cases k _ h.symm with ⟨hx, h1c, h2c | h2c⟩ | ⟨hy, h1c, h2c | h2c⟩
      · have hyk : (W.v k).2 = ym - 1 := by
          have hc2 : ((x₀ + 2, ym) : Cell).2 = ym := rfl
          omega
        exact hpary1 (hyk ▸ W.parY k)
      · have hyk : (W.v k).2 = ym + 1 := by
          have hc2 : ((x₀ + 2, ym) : Cell).2 = ym := rfl
          omega
        exact hparyp1 (hyk ▸ W.parY k)
      · have h1' : (W.v k).1 = x₀ + 1 := by
          have hc1 : ((x₀ + 2, ym) : Cell).1 = x₀ + 2 := rfl
          omega
        exact hparx1 (h1' ▸ W.parX k)
      · have h1' : (W.v k).1 = x₀ + 3 := by
          have hc1 : ((x₀ + 2, ym) : Cell).1 = x₀ + 2 := rfl
          omega
        exact hparx3 (h1' ▸ W.parX k)
    · have hk1 : k + 1 = 1 := hjr1 (k + 1) h.symm
      have h1m : ((k + 1 : Fin (W.n + 4)) : ℕ) = (k : ℕ) + 1 := by
        rw [Fin.val_add, Fin.val_one']
        have h1p : 1 % (W.n + 4) = 1 := Nat.mod_eq_of_lt (by omega)
        rw [h1p, Nat.mod_eq_of_lt (by omega : (k : ℕ) + 1 < W.n + 4)]
      have hv := congrArg Fin.val hk1
      rw [h1m, val_one_fin] at hv
      omega

theorem push_hEn3 (W : OrthoLoop) (x₀ ym : ℤ) (h0 : W.v 0 = (x₀, ym))
    (hn1 : W.v (-1) = (x₀, ym - 2))
    (hr : ∀ i, W.v i ≠ (x₀ + 2, ym - 2)) :
    ∀ (k : Fin (W.n + 4)), 1 ≤ (k : ℕ) → (k : ℕ) ≤ W.n + 1 →
      Disjoint ({(x₀, ym - 2), (x₀ + 1, ym - 2), (x₀ + 2, ym - 2)} : Finset Cell)
        (W.edgePts k) := by
  classical
  have hparx1 := push_hparx1 W x₀ ym h0
  have hparx2 := push_hparx2 W x₀ ym h0
  have hparx3 := push_hparx3 W x₀ ym h0
  have hpary1 := push_hpary1 W x₀ ym h0
  have hpary3 := push_hpary3 W x₀ ym h0
  have hjd : ∀ j : Fin (W.n + 4), W.v j = (x₀, ym - 2) → j = ⟨W.n + 3, by omega⟩ :=
    fun j hj => W.inj (hj.trans (push_hn1' W x₀ ym hn1).symm)
  intro k hk1 hkn
  rw [Finset.disjoint_left]
  intro c hc hc'
  simp only [Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with rfl | rfl | rfl
  · -- c = d
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc'
    rcases hc' with h | h | h
    · have hkn3 : k = ⟨W.n + 3, by omega⟩ := hjd k h.symm
      have hv := congrArg Fin.val hkn3
      have hvR : ((⟨W.n + 3, by omega⟩ : Fin (W.n + 4)) : ℕ) = W.n + 3 := rfl
      rw [hvR] at hv
      omega
    · rcases W.mid_cases k _ h.symm with ⟨hx, h1c, h2c | h2c⟩ | ⟨hy, h1c, h2c | h2c⟩
      · have hyk : (W.v k).2 = ym - 3 := by
          have hc2 : ((x₀, ym - 2) : Cell).2 = ym - 2 := rfl
          omega
        exact hpary3 (hyk ▸ W.parY k)
      · have hyk : (W.v k).2 = ym - 1 := by
          have hc2 : ((x₀, ym - 2) : Cell).2 = ym - 2 := rfl
          omega
        exact hpary1 (hyk ▸ W.parY k)
      · have h1' : (W.v k).1 = x₀ - 1 := by
          have hc1 : ((x₀, ym - 2) : Cell).1 = x₀ := rfl
          omega
        exact hparx2 (h1' ▸ W.parX k)
      · have h1' : (W.v k).1 = x₀ + 1 := by
          have hc1 : ((x₀, ym - 2) : Cell).1 = x₀ := rfl
          omega
        exact hparx1 (h1' ▸ W.parX k)
    · have hkn3 : k + 1 = ⟨W.n + 3, by omega⟩ := hjd (k + 1) h.symm
      have h1m : ((k + 1 : Fin (W.n + 4)) : ℕ) = (k : ℕ) + 1 := by
        rw [Fin.val_add, Fin.val_one']
        have h1p : 1 % (W.n + 4) = 1 := Nat.mod_eq_of_lt (by omega)
        rw [h1p, Nat.mod_eq_of_lt (by omega : (k : ℕ) + 1 < W.n + 4)]
      have hv := congrArg Fin.val hkn3
      have hvR : ((⟨W.n + 3, by omega⟩ : Fin (W.n + 4)) : ℕ) = W.n + 3 := rfl
      rw [h1m, hvR] at hv
      omega
  · -- c = (x₀+1, ym-2)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc'
    rcases hc' with h | h | h
    · have hxi : (W.v k).1 = x₀ + 1 := (congrArg Prod.fst h).symm
      exact hparx1 (hxi ▸ W.parX k)
    · rcases W.mid_cases k _ h.symm with ⟨hx, h1c, h2c | h2c⟩ | ⟨hy, h1c, h2c | h2c⟩
      · have hxi : (W.v k).1 = x₀ + 1 := h1c.symm
        exact hparx1 (hxi ▸ W.parX k)
      · have hxi : (W.v k).1 = x₀ + 1 := h1c.symm
        exact hparx1 (hxi ▸ W.parX k)
      · have hvx : (W.v k).1 = x₀ := by
          have hc1 : ((x₀ + 1, ym - 2) : Cell).1 = x₀ + 1 := rfl
          omega
        have hvy : (W.v k).2 = ym - 2 := h1c.symm
        have hkn3 : k = ⟨W.n + 3, by omega⟩ := hjd k (Prod.ext hvx hvy)
        have hv := congrArg Fin.val hkn3
        have hvR : ((⟨W.n + 3, by omega⟩ : Fin (W.n + 4)) : ℕ) = W.n + 3 := rfl
        rw [hvR] at hv
        omega
      · have hvx : (W.v k).1 = x₀ + 2 := by
          have hc1 : ((x₀ + 1, ym - 2) : Cell).1 = x₀ + 1 := rfl
          omega
        have hvy : (W.v k).2 = ym - 2 := h1c.symm
        exact absurd (Prod.ext hvx hvy) (hr k)
    · have hxi : (W.v (k + 1)).1 = x₀ + 1 := (congrArg Prod.fst h).symm
      exact hparx1 (hxi ▸ W.parX (k + 1))
  · -- c = r′
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc'
    rcases hc' with h | h | h
    · exact absurd h.symm (hr k)
    · rcases W.mid_cases k _ h.symm with ⟨hx, h1c, h2c | h2c⟩ | ⟨hy, h1c, h2c | h2c⟩
      · have hyk : (W.v k).2 = ym - 3 := by
          have hc2 : ((x₀ + 2, ym - 2) : Cell).2 = ym - 2 := rfl
          omega
        exact hpary3 (hyk ▸ W.parY k)
      · have hyk : (W.v k).2 = ym - 1 := by
          have hc2 : ((x₀ + 2, ym - 2) : Cell).2 = ym - 2 := rfl
          omega
        exact hpary1 (hyk ▸ W.parY k)
      · have h1' : (W.v k).1 = x₀ + 1 := by
          have hc1 : ((x₀ + 2, ym - 2) : Cell).1 = x₀ + 2 := rfl
          omega
        exact hparx1 (h1' ▸ W.parX k)
      · have h1' : (W.v k).1 = x₀ + 3 := by
          have hc1 : ((x₀ + 2, ym - 2) : Cell).1 = x₀ + 2 := rfl
          omega
        exact hparx3 (h1' ▸ W.parX k)
    · exact absurd h.symm (hr (k + 1))

theorem pushLoop_inj (W : OrthoLoop) (x₀ ym : ℤ)
    (hr : ∀ i, W.v i ≠ (x₀ + 2, ym - 2)) :
    Function.Injective (Function.update W.v 0 (x₀ + 2, ym - 2)) := by
  classical
  intro i j h
  by_cases hi0 : i = 0
  · by_cases hj0 : j = 0
    · exact hi0.trans hj0.symm
    · rw [hi0, Function.update_self, Function.update_of_ne hj0] at h
      exact absurd h.symm (hr j)
  · by_cases hj0 : j = 0
    · rw [hj0, Function.update_self, Function.update_of_ne hi0] at h
      exact absurd h (hr i)
    · rw [Function.update_of_ne hi0, Function.update_of_ne hj0] at h
      exact W.inj h

theorem pushLoop_step (W : OrthoLoop) (x₀ ym : ℤ)
    (h1 : W.v 1 = (x₀ + 2, ym)) (hn1 : W.v (-1) = (x₀, ym - 2)) :
    ∀ i : Fin (W.n + 4),
      (((Function.update W.v 0 (x₀ + 2, ym - 2)) (i + 1)).1 = ((Function.update W.v 0 (x₀ + 2, ym - 2)) i).1 ∧ ((Function.update W.v 0 (x₀ + 2, ym - 2)) (i + 1)).2 = ((Function.update W.v 0 (x₀ + 2, ym - 2)) i).2 + 2) ∨
      (((Function.update W.v 0 (x₀ + 2, ym - 2)) (i + 1)).1 = ((Function.update W.v 0 (x₀ + 2, ym - 2)) i).1 ∧ ((Function.update W.v 0 (x₀ + 2, ym - 2)) (i + 1)).2 = ((Function.update W.v 0 (x₀ + 2, ym - 2)) i).2 - 2) ∨
      (((Function.update W.v 0 (x₀ + 2, ym - 2)) (i + 1)).1 = ((Function.update W.v 0 (x₀ + 2, ym - 2)) i).1 + 2 ∧ ((Function.update W.v 0 (x₀ + 2, ym - 2)) (i + 1)).2 = ((Function.update W.v 0 (x₀ + 2, ym - 2)) i).2) ∨
      (((Function.update W.v 0 (x₀ + 2, ym - 2)) (i + 1)).1 = ((Function.update W.v 0 (x₀ + 2, ym - 2)) i).1 - 2 ∧ ((Function.update W.v 0 (x₀ + 2, ym - 2)) (i + 1)).2 = ((Function.update W.v 0 (x₀ + 2, ym - 2)) i).2) := by
  classical
  have eS_last := push_eS_last W
  have h1ne0 := push_h1ne0 W
  have hn3ne := push_hn3ne W
  have hn1' := push_hn1' W x₀ ym hn1
  have hsucc_ne := push_hsucc_ne W
  intro i
  by_cases hi0 : i = 0
  · rw [hi0]
    have e1 : (0 + 1 : Fin (W.n + 4)) = 1 := zero_add 1
    rw [e1, Function.update_self, Function.update_of_ne h1ne0, h1]
    exact Or.inl ⟨by simp, by simp⟩
  · by_cases hin : i = ⟨W.n + 3, by omega⟩
    · rw [hin]
      rw [eS_last, Function.update_of_ne hn3ne, hn1', Function.update_self]
      exact Or.inr (Or.inr (Or.inl ⟨by simp, by simp⟩))
    · have hi1 : i + 1 ≠ 0 := hsucc_ne i hin
      rw [Function.update_of_ne hi0, Function.update_of_ne hi1]
      exact W.step i

theorem pushLoop_par (W : OrthoLoop) (x₀ ym : ℤ) (h0 : W.v 0 = (x₀, ym)) :
    ∀ i : Fin (W.n + 4), (((Function.update W.v 0 (x₀ + 2, ym - 2)) i).1 : ZMod 2) = W.a ∧ (((Function.update W.v 0 (x₀ + 2, ym - 2)) i).2 : ZMod 2) = W.b := by
  classical
  have hpa := push_hpa W x₀ ym h0
  have hpb := push_hpb W x₀ ym h0
  intro i
  by_cases hi0 : i = 0
  · rw [hi0, Function.update_self]
    constructor
    · push_cast
      rw [show (2 : ZMod 2) = 0 from by decide, add_zero]
      exact hpa
    · push_cast
      rw [show (2 : ZMod 2) = 0 from by decide, sub_zero]
      exact hpb
  · rw [Function.update_of_ne hi0]
    exact W.par i

theorem pushLoop_simple (W : OrthoLoop) (x₀ ym : ℤ) (h0 : W.v 0 = (x₀, ym))
    (h1 : W.v 1 = (x₀ + 2, ym)) (hn1 : W.v (-1) = (x₀, ym - 2))
    (hr : ∀ i, W.v i ≠ (x₀ + 2, ym - 2)) :
    ∀ i j : Fin (W.n + 4), i ≠ j → i + 1 ≠ j → i ≠ j + 1 →
      Disjoint ({(Function.update W.v 0 (x₀ + 2, ym - 2)) i, midPt ((Function.update W.v 0 (x₀ + 2, ym - 2)) i) ((Function.update W.v 0 (x₀ + 2, ym - 2)) (i + 1)), (Function.update W.v 0 (x₀ + 2, ym - 2)) (i + 1)} : Finset Cell)
        ({(Function.update W.v 0 (x₀ + 2, ym - 2)) j, midPt ((Function.update W.v 0 (x₀ + 2, ym - 2)) j) ((Function.update W.v 0 (x₀ + 2, ym - 2)) (j + 1)), (Function.update W.v 0 (x₀ + 2, ym - 2)) (j + 1)} : Finset Cell) := by
  classical
  have eS_last := push_eS_last W
  have h1ne0 := push_h1ne0 W
  have hn3ne := push_hn3ne W
  have hn1' := push_hn1' W x₀ ym hn1
  have hsucc_ne := push_hsucc_ne W
  have hE0 := push_hE0 W x₀ ym h0 h1 hr
  have hEn3 := push_hEn3 W x₀ ym h0 hn1 hr
  intro i j hij hi1j hij1
  rw [Finset.disjoint_left]
  intro c hci hcj
  beta_reduce at hci hcj
  have he0set : ({(Function.update W.v 0 (x₀ + 2, ym - 2)) 0,
      midPt ((Function.update W.v 0 (x₀ + 2, ym - 2)) 0)
        ((Function.update W.v 0 (x₀ + 2, ym - 2)) (0 + 1)),
      (Function.update W.v 0 (x₀ + 2, ym - 2)) (0 + 1)} : Finset Cell) =
      {(x₀ + 2, ym - 2), (x₀ + 2, ym - 1), (x₀ + 2, ym)} := by
    have e1 : (0 + 1 : Fin (W.n + 4)) = 1 := zero_add 1
    rw [e1, Function.update_self, Function.update_of_ne h1ne0, h1]
    rw [show midPt (x₀ + 2, ym - 2) (x₀ + 2, ym) = (x₀ + 2, ym - 1) from by
      simp only [midPt, Prod.mk.injEq]
      constructor <;> omega]
  have hen3set : ({(Function.update W.v 0 (x₀ + 2, ym - 2)) ⟨W.n + 3, by omega⟩,
      midPt ((Function.update W.v 0 (x₀ + 2, ym - 2)) ⟨W.n + 3, by omega⟩)
        ((Function.update W.v 0 (x₀ + 2, ym - 2)) (⟨W.n + 3, by omega⟩ + 1)),
      (Function.update W.v 0 (x₀ + 2, ym - 2)) (⟨W.n + 3, by omega⟩ + 1)} : Finset Cell) =
      {(x₀, ym - 2), (x₀ + 1, ym - 2), (x₀ + 2, ym - 2)} := by
    rw [eS_last, Function.update_self, Function.update_of_ne hn3ne, hn1']
    rw [show midPt (x₀, ym - 2) (x₀ + 2, ym - 2) = (x₀ + 1, ym - 2) from by
      simp only [midPt, Prod.mk.injEq]
      constructor <;> omega]
  have hshset : ∀ i : Fin (W.n + 4), i ≠ 0 → i ≠ ⟨W.n + 3, by omega⟩ →
      ({(Function.update W.v 0 (x₀ + 2, ym - 2)) i,
        midPt ((Function.update W.v 0 (x₀ + 2, ym - 2)) i)
          ((Function.update W.v 0 (x₀ + 2, ym - 2)) (i + 1)),
        (Function.update W.v 0 (x₀ + 2, ym - 2)) (i + 1)} : Finset Cell) = W.edgePts i := by
    intro i hi0 hin
    have hi1 : i + 1 ≠ 0 := hsucc_ne i hin
    rw [Function.update_of_ne hi0, Function.update_of_ne hi1]
  by_cases hi0 : i = 0
  · rw [hi0] at hci
    rw [he0set] at hci
    by_cases hj0 : j = 0
    · exact absurd (hi0.trans hj0.symm) hij
    · by_cases hjn : j = ⟨W.n + 3, by omega⟩
      · have hj1 : j + 1 = 0 := by rw [hjn]; exact eS_last
        exact absurd (hi0.trans hj1.symm) hij1
      · rw [hshset j hj0 hjn] at hcj
        have hj1 : j ≠ 1 := by
          intro h
          exact hi1j (by rw [hi0, h]; exact zero_add 1)
        have hj1' : (j : ℕ) ≠ 1 := by
          intro h
          exact hj1 (Fin.ext (by rw [h, val_one_fin]))
        have hj2 : 2 ≤ (j : ℕ) := by
          have hj0' : (j : ℕ) ≠ 0 := fun h => hj0 (Fin.ext h)
          omega
        have hj3 : (j : ℕ) ≤ W.n + 2 := by
          have hlt := j.isLt
          have hjn' : (j : ℕ) ≠ W.n + 3 := fun h => hjn (Fin.ext h)
          omega
        exact Finset.disjoint_left.mp (hE0 j hj2 hj3) hci hcj
  · by_cases hin : i = ⟨W.n + 3, by omega⟩
    · rw [hin] at hci
      rw [hen3set] at hci
      by_cases hj0 : j = 0
      · have hi1 : i + 1 = 0 := by rw [hin]; exact eS_last
        exact absurd (hi1.trans hj0.symm) hi1j
      · by_cases hjn : j = ⟨W.n + 3, by omega⟩
        · exact absurd (hin.trans hjn.symm) hij
        · rw [hshset j hj0 hjn] at hcj
          have hj2 : (j : ℕ) ≤ W.n + 1 := by
            have hlt := j.isLt
            have hjn' : (j : ℕ) ≠ W.n + 3 := fun h => hjn (Fin.ext h)
            have hjn2 : (j : ℕ) ≠ W.n + 2 := by
              intro h
              have hjj : j + 1 = ⟨W.n + 3, by omega⟩ := by
                apply Fin.ext
                rw [Fin.val_add, Fin.val_one']
                have h1m : 1 % (W.n + 4) = 1 := Nat.mod_eq_of_lt (by omega)
                rw [h1m, h]
                have hvR : ((⟨W.n + 3, by omega⟩ : Fin (W.n + 4)) : ℕ) = W.n + 3 := rfl
                rw [hvR]
                exact Nat.mod_eq_of_lt (by omega : W.n + 2 + 1 < W.n + 4)
              exact hij1 ((hjj.trans hin.symm).symm)
            omega
          have hj0' : 1 ≤ (j : ℕ) := by
            have hj0'' : (j : ℕ) ≠ 0 := fun h => hj0 (Fin.ext h)
            omega
          exact Finset.disjoint_left.mp (hEn3 j hj0' hj2) hci hcj
    · by_cases hj0 : j = 0
      · rw [hj0] at hcj
        rw [he0set] at hcj
        rw [hshset i hi0 hin] at hci
        have hi1 : i ≠ 1 := by
          intro h
          exact hij1 (by rw [h, hj0]; abel)
        have hi1' : (i : ℕ) ≠ 1 := by
          intro h
          exact hi1 (Fin.ext (by rw [h, val_one_fin]))
        have hi2 : 2 ≤ (i : ℕ) := by
          have hi0' : (i : ℕ) ≠ 0 := fun h => hi0 (Fin.ext h)
          omega
        have hi3 : (i : ℕ) ≤ W.n + 2 := by
          have hlt := i.isLt
          have hin' : (i : ℕ) ≠ W.n + 3 := fun h => hin (Fin.ext h)
          omega
        exact Finset.disjoint_left.mp (hE0 i hi2 hi3) hcj hci
      · by_cases hjn : j = ⟨W.n + 3, by omega⟩
        · rw [hjn] at hcj
          rw [hen3set] at hcj
          rw [hshset i hi0 hin] at hci
          have hi2 : (i : ℕ) ≤ W.n + 1 := by
            have hlt := i.isLt
            have hin' : (i : ℕ) ≠ W.n + 3 := fun h => hin (Fin.ext h)
            have hin2 : (i : ℕ) ≠ W.n + 2 := by
              intro h
              have hii : i + 1 = ⟨W.n + 3, by omega⟩ := by
                apply Fin.ext
                rw [Fin.val_add, Fin.val_one']
                have h1m : 1 % (W.n + 4) = 1 := Nat.mod_eq_of_lt (by omega)
                rw [h1m, h]
                have hvR : ((⟨W.n + 3, by omega⟩ : Fin (W.n + 4)) : ℕ) = W.n + 3 := rfl
                rw [hvR]
                exact Nat.mod_eq_of_lt (by omega : W.n + 2 + 1 < W.n + 4)
              exact hi1j (hii.trans hjn.symm)
            omega
          have hi0' : 1 ≤ (i : ℕ) := by
            have hi0'' : (i : ℕ) ≠ 0 := fun h => hi0 (Fin.ext h)
            omega
          exact Finset.disjoint_left.mp (hEn3 i hi0' hi2) hcj hci
        · rw [hshset i hi0 hin] at hci
          rw [hshset j hj0 hjn] at hcj
          exact Finset.disjoint_left.mp (W.simple i j hij hi1j hij1) hci hcj

set_option maxHeartbeats 800000 in
theorem pushLoop_I (W : OrthoLoop) (x₀ ym : ℤ) (h0 : W.v 0 = (x₀, ym))
    (hmax : ∀ i, (W.v i).2 ≤ ym) (hmin : ∀ i, (W.v i).2 = ym → x₀ ≤ (W.v i).1)
    (h1 : W.v 1 = (x₀ + 2, ym)) (h2 : W.v 2 = (x₀ + 4, ym))
    (hn1 : W.v (-1) = (x₀, ym - 2)) (hr : ∀ i, W.v i ≠ (x₀ + 2, ym - 2)) :
    ({ a := W.a, b := W.b, n := W.n, v := Function.update W.v 0 (x₀ + 2, ym - 2), inj := pushLoop_inj W x₀ ym hr, step := pushLoop_step W x₀ ym h1 hn1, par := pushLoop_par W x₀ ym h0, simple := pushLoop_simple W x₀ ym h0 h1 hn1 hr } : OrthoLoop).I + 4 = W.I := by
  classical
  set W' := ({ a := W.a, b := W.b, n := W.n, v := Function.update W.v 0 (x₀ + 2, ym - 2), inj := pushLoop_inj W x₀ ym hr, step := pushLoop_step W x₀ ym h1 hn1, par := pushLoop_par W x₀ ym h0, simple := pushLoop_simple W x₀ ym h0 h1 hn1 hr } : OrthoLoop)
  have hWn : W'.n = W.n := rfl
  have h0x : (W.v 0).1 = x₀ := congrArg Prod.fst h0
  have h0y : (W.v 0).2 = ym := congrArg Prod.snd h0
  have h1x : (W.v 1).1 = x₀ + 2 := congrArg Prod.fst h1
  have h1y : (W.v 1).2 = ym := congrArg Prod.snd h1
  have h2x : (W.v 2).1 = x₀ + 4 := congrArg Prod.fst h2
  have h2y : (W.v 2).2 = ym := congrArg Prod.snd h2
  have hn1' := push_hn1' W x₀ ym hn1
  have hdx : (W.v ⟨W.n + 3, by omega⟩).1 = x₀ := congrArg Prod.fst hn1'
  have hdy : (W.v ⟨W.n + 3, by omega⟩).2 = ym - 2 := congrArg Prod.snd hn1'
  have h0xX : W.x 0 = x₀ := h0x
  have h0yX : W.y 0 = ym := h0y
  have h1xX : W.x 1 = x₀ + 2 := h1x
  have h1yX : W.y 1 = ym := h1y
  have h2xX : W.x 2 = x₀ + 4 := h2x
  have hdxX : W.x ⟨W.n + 3, by omega⟩ = x₀ := hdx
  have hdyX : W.y ⟨W.n + 3, by omega⟩ = ym - 2 := hdy
  have hpa := push_hpa W x₀ ym h0
  have hpb := push_hpb W x₀ ym h0
  have hkey := push_hkey
  have hparx1 := push_hparx1 W x₀ ym h0
  have hparx3 := push_hparx3 W x₀ ym h0
  have hpary1 := push_hpary1 W x₀ ym h0
  have hpary3 := push_hpary3 W x₀ ym h0
  have hjd : ∀ j : Fin (W.n + 4), W.v j = (x₀, ym - 2) → j = ⟨W.n + 3, by omega⟩ :=
    fun j hj => W.inj (hj.trans hn1'.symm)
  have hj0 : ∀ j : Fin (W.n + 4), W.v j = (x₀, ym) → j = 0 :=
    fun j hj => W.inj (hj.trans h0.symm)
  have hjr1 : ∀ j : Fin (W.n + 4), W.v j = (x₀ + 2, ym) → j = 1 :=
    fun j hj => W.inj (hj.trans h1.symm)
  have eS_last := push_eS_last W
  have h1ne0 := push_h1ne0 W
  have hn3ne := push_hn3ne W
  have hsucc_ne := push_hsucc_ne W
  · -- I: W'.I + 4 = W.I
    -- flip formula
    have hflip : ∀ c : Cell, W.p2 c + W'.p2 c =
        (if c.1 < x₀ ∧ ym - 2 ≤ c.2 ∧ c.2 < ym then (1 : ZMod 2) else 0) +
        (if c.1 < x₀ + 2 ∧ ym - 2 ≤ c.2 ∧ c.2 < ym then (1 : ZMod 2) else 0) := by
      intro c
      let fW : ℕ → ZMod 2 := fun i =>
        if h : i < W.n + 4 then
          (if W.vert ⟨i, h⟩ ∧ c.1 < W.x ⟨i, h⟩ ∧ W.lo ⟨i, h⟩ ≤ c.2 ∧ c.2 < W.hi ⟨i, h⟩
            then (1 : ZMod 2) else 0)
        else 0
      let fW' : ℕ → ZMod 2 := fun j =>
        if h : j < W'.n + 4 then
          (if W'.vert ⟨j, h⟩ ∧ c.1 < W'.x ⟨j, h⟩ ∧ W'.lo ⟨j, h⟩ ≤ c.2 ∧ c.2 < W'.hi ⟨j, h⟩
            then (1 : ZMod 2) else 0)
        else 0
      have hfW : ∀ i : Fin (W.n + 4),
          (if W.vert i ∧ c.1 < W.x i ∧ W.lo i ≤ c.2 ∧ c.2 < W.hi i then (1 : ZMod 2) else 0) =
            fW ↑i := by
        intro i
        have hi : ↑i < W.n + 4 := i.isLt
        have hi2 : (⟨↑i, hi⟩ : Fin (W.n + 4)) = i := Fin.ext rfl
        show (if W.vert i ∧ c.1 < W.x i ∧ W.lo i ≤ c.2 ∧ c.2 < W.hi i then (1 : ZMod 2) else 0) =
          if h : ↑i < W.n + 4 then
            (if W.vert ⟨↑i, h⟩ ∧ c.1 < W.x ⟨↑i, h⟩ ∧ W.lo ⟨↑i, h⟩ ≤ c.2 ∧ c.2 < W.hi ⟨↑i, h⟩
              then (1 : ZMod 2) else 0)
          else 0
        rw [dif_pos hi, hi2]
      have hfW' : ∀ j : Fin (W'.n + 4),
          (if W'.vert j ∧ c.1 < W'.x j ∧ W'.lo j ≤ c.2 ∧ c.2 < W'.hi j then (1 : ZMod 2) else 0) =
            fW' ↑j := by
        intro j
        have hj : ↑j < W'.n + 4 := j.isLt
        have hj2 : (⟨↑j, hj⟩ : Fin (W'.n + 4)) = j := Fin.ext rfl
        show (if W'.vert j ∧ c.1 < W'.x j ∧ W'.lo j ≤ c.2 ∧ c.2 < W'.hi j then (1 : ZMod 2) else 0) =
          if h : ↑j < W'.n + 4 then
            (if W'.vert ⟨↑j, h⟩ ∧ c.1 < W'.x ⟨↑j, h⟩ ∧ W'.lo ⟨↑j, h⟩ ≤ c.2 ∧ c.2 < W'.hi ⟨↑j, h⟩
              then (1 : ZMod 2) else 0)
          else 0
        rw [dif_pos hj, hj2]
      have hsumW : W.p2 c = ∑ i ∈ Finset.range (W.n + 4), fW i := by
        show (∑ i : Fin (W.n + 4),
            (if W.vert i ∧ c.1 < W.x i ∧ W.lo i ≤ c.2 ∧ c.2 < W.hi i then (1 : ZMod 2) else 0)) = _
        rw [Finset.sum_congr rfl (fun i _ => hfW i)]
        exact Fin.sum_univ_eq_sum_range fW (W.n + 4)
      have hsumW' : W'.p2 c = ∑ i ∈ Finset.range (W'.n + 4), fW' i := by
        show (∑ i : Fin (W'.n + 4),
            (if W'.vert i ∧ c.1 < W'.x i ∧ W'.lo i ≤ c.2 ∧ c.2 < W'.hi i then (1 : ZMod 2) else 0)) = _
        rw [Finset.sum_congr rfl (fun i _ => hfW' i)]
        exact Fin.sum_univ_eq_sum_range fW' (W'.n + 4)
      have htail : ∀ j : ℕ, 1 ≤ j → j ≤ W.n + 2 → fW' j = fW j := by
        intro j hj1 hj2
        have hjW : j < W.n + 4 := by omega
        have hjW' : j < W'.n + 4 := by rw [hWn]; omega
        have e0 : (⟨j, hjW'⟩ : Fin (W'.n + 4)) ≠ 0 := by
          intro h0
          have hv := congrArg Fin.val h0
          have hvR : ((⟨j, hjW'⟩ : Fin (W'.n + 4)) : ℕ) = j := rfl
          rw [hvR, val_zero_fin] at hv
          omega
        have e1 : W'.v ⟨j, hjW'⟩ = W.v ⟨j, hjW⟩ := by
          show (Function.update W.v 0 (x₀ + 2, ym - 2)) ⟨j, hjW'⟩ = W.v ⟨j, hjW⟩
          rw [Function.update_of_ne e0]
        have eS1 : (⟨j, hjW'⟩ + 1 : Fin (W'.n + 4)) =
            ⟨(j + 1) % (W'.n + 4), Nat.mod_lt _ (by omega)⟩ := by
          apply Fin.ext
          rw [Fin.val_add, Fin.val_one']
          have h1m : 1 % (W'.n + 4) = 1 := Nat.mod_eq_of_lt (by omega)
          rw [h1m]
        have eS2 : (⟨j, hjW⟩ + 1 : Fin (W.n + 4)) =
            ⟨(j + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ := by
          apply Fin.ext
          rw [Fin.val_add, Fin.val_one']
          have h1m : 1 % (W.n + 4) = 1 := Nat.mod_eq_of_lt (by omega)
          rw [h1m]
        have e2 : W'.v ⟨(j + 1) % (W'.n + 4), Nat.mod_lt _ (by omega)⟩ =
            W.v ⟨(j + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ := by
          have e3 : (⟨(j + 1) % (W'.n + 4), Nat.mod_lt _ (by omega)⟩ : Fin (W'.n + 4)) =
              ⟨(j + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ := by
            apply Fin.ext
            show ((j + 1) % (W'.n + 4) : ℕ) = (j + 1) % (W.n + 4)
            rw [hWn]
          rw [e3]
          show (Function.update W.v 0 (x₀ + 2, ym - 2)) ⟨(j + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ =
            W.v ⟨(j + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩
          rw [Function.update_of_ne (by
            intro h0
            have hv := congrArg Fin.val h0
            have hvR : ((⟨(j + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ : Fin (W.n + 4)) : ℕ) =
              j + 1 := by
              show (j + 1) % (W.n + 4) = j + 1
              exact Nat.mod_eq_of_lt (by omega)
            rw [hvR, val_zero_fin] at hv
            omega)]
        show (if h : j < W'.n + 4 then
            (if W'.vert ⟨j, h⟩ ∧ c.1 < W'.x ⟨j, h⟩ ∧ W'.lo ⟨j, h⟩ ≤ c.2 ∧ c.2 < W'.hi ⟨j, h⟩
              then (1 : ZMod 2) else 0) else 0) =
          (if h : j < W.n + 4 then
            (if W.vert ⟨j, h⟩ ∧ c.1 < W.x ⟨j, h⟩ ∧ W.lo ⟨j, h⟩ ≤ c.2 ∧ c.2 < W.hi ⟨j, h⟩
              then (1 : ZMod 2) else 0) else 0)
        rw [dif_pos hjW', dif_pos hjW]
        have hiff : (W'.vert ⟨j, hjW'⟩ ∧ c.1 < W'.x ⟨j, hjW'⟩ ∧ W'.lo ⟨j, hjW'⟩ ≤ c.2 ∧
            c.2 < W'.hi ⟨j, hjW'⟩) ↔
            (W.vert ⟨j, hjW⟩ ∧ c.1 < W.x ⟨j, hjW⟩ ∧ W.lo ⟨j, hjW⟩ ≤ c.2 ∧ c.2 < W.hi ⟨j, hjW⟩) := by
          show (((W'.v (⟨j, hjW'⟩ + 1)).1 = (W'.v ⟨j, hjW'⟩).1) ∧ c.1 < (W'.v ⟨j, hjW'⟩).1 ∧
              min ((W'.v ⟨j, hjW'⟩).2) ((W'.v (⟨j, hjW'⟩ + 1)).2) ≤ c.2 ∧
              c.2 < max ((W'.v ⟨j, hjW'⟩).2) ((W'.v (⟨j, hjW'⟩ + 1)).2)) ↔
            (((W.v (⟨j, hjW⟩ + 1)).1 = (W.v ⟨j, hjW⟩).1) ∧ c.1 < (W.v ⟨j, hjW⟩).1 ∧
              min ((W.v ⟨j, hjW⟩).2) ((W.v (⟨j, hjW⟩ + 1)).2) ≤ c.2 ∧
              c.2 < max ((W.v ⟨j, hjW⟩).2) ((W.v (⟨j, hjW⟩ + 1)).2))
          rw [eS1, e1, e2]
        exact if_congr hiff rfl rfl
      have hfW0 : fW 0 = 0 := by
        have h0lt : 0 < W.n + 4 := by omega
        show (if h : 0 < W.n + 4 then
            (if W.vert ⟨0, h⟩ ∧ c.1 < W.x ⟨0, h⟩ ∧ W.lo ⟨0, h⟩ ≤ c.2 ∧ c.2 < W.hi ⟨0, h⟩
              then (1 : ZMod 2) else 0) else 0) = 0
        rw [dif_pos h0lt]
        apply if_neg
        intro hcon
        have hvert : W.x (⟨0, h0lt⟩ + 1) = W.x ⟨0, h0lt⟩ := hcon.1
        have e0 : (⟨0, h0lt⟩ : Fin (W.n + 4)) = 0 := Fin.ext rfl
        have e01 : (⟨0, h0lt⟩ + 1 : Fin (W.n + 4)) = 1 := by rw [e0]; exact zero_add 1
        rw [e01, e0] at hvert
        rw [h1xX, h0xX] at hvert
        omega
      have hfW'0 : fW' 0 = (if c.1 < x₀ + 2 ∧ ym - 2 ≤ c.2 ∧ c.2 < ym then (1 : ZMod 2) else 0) := by
        have hlt : 0 < W'.n + 4 := by rw [hWn]; omega
        show (if h : 0 < W'.n + 4 then
            (if W'.vert ⟨0, h⟩ ∧ c.1 < W'.x ⟨0, h⟩ ∧ W'.lo ⟨0, h⟩ ≤ c.2 ∧ c.2 < W'.hi ⟨0, h⟩
              then (1 : ZMod 2) else 0) else 0) = _
        rw [dif_pos hlt]
        have e0 : (⟨0, hlt⟩ : Fin (W'.n + 4)) = 0 := Fin.ext rfl
        have e01 : (⟨0, hlt⟩ + 1 : Fin (W'.n + 4)) = 1 := by rw [e0]; exact zero_add 1
        have hvert : W'.vert ⟨0, hlt⟩ := by
          show W'.x (⟨0, hlt⟩ + 1) = W'.x ⟨0, hlt⟩
          rw [e01, e0]
          show ((Function.update W.v 0 (x₀ + 2, ym - 2)) 1).1 =
            ((Function.update W.v 0 (x₀ + 2, ym - 2)) 0).1
          rw [Function.update_self, Function.update_of_ne h1ne0, h1]
        have hx1 : W'.x ⟨0, hlt⟩ = x₀ + 2 := by
          rw [e0]
          show ((Function.update W.v 0 (x₀ + 2, ym - 2)) 0).1 = x₀ + 2
          rw [Function.update_self]
        have hlo1 : W'.lo ⟨0, hlt⟩ = ym - 2 := by
          show min (W'.y ⟨0, hlt⟩) (W'.y (⟨0, hlt⟩ + 1)) = ym - 2
          rw [e01, e0]
          show min ((Function.update W.v 0 (x₀ + 2, ym - 2)) 0).2
            ((Function.update W.v 0 (x₀ + 2, ym - 2)) 1).2 = ym - 2
          rw [Function.update_self, Function.update_of_ne h1ne0, h1]
          exact min_eq_left (by omega)
        have hhi1 : W'.hi ⟨0, hlt⟩ = ym := by
          show max (W'.y ⟨0, hlt⟩) (W'.y (⟨0, hlt⟩ + 1)) = ym
          rw [e01, e0]
          show max ((Function.update W.v 0 (x₀ + 2, ym - 2)) 0).2
            ((Function.update W.v 0 (x₀ + 2, ym - 2)) 1).2 = ym
          rw [Function.update_self, Function.update_of_ne h1ne0, h1]
          exact max_eq_right (by omega)
        have hiff : (W'.vert ⟨0, hlt⟩ ∧ c.1 < W'.x ⟨0, hlt⟩ ∧ W'.lo ⟨0, hlt⟩ ≤ c.2 ∧
            c.2 < W'.hi ⟨0, hlt⟩) ↔ (c.1 < x₀ + 2 ∧ ym - 2 ≤ c.2 ∧ c.2 < ym) := by
          rw [hx1, hlo1, hhi1, show W'.vert ⟨0, hlt⟩ = True from eq_true hvert, true_and]
        exact if_congr hiff rfl rfl
      have hfWlast : fW (W.n + 3) =
          (if c.1 < x₀ ∧ ym - 2 ≤ c.2 ∧ c.2 < ym then (1 : ZMod 2) else 0) := by
        have hlt : W.n + 3 < W.n + 4 := by omega
        show (if h : W.n + 3 < W.n + 4 then
            (if W.vert ⟨W.n + 3, h⟩ ∧ c.1 < W.x ⟨W.n + 3, h⟩ ∧ W.lo ⟨W.n + 3, h⟩ ≤ c.2 ∧
              c.2 < W.hi ⟨W.n + 3, h⟩ then (1 : ZMod 2) else 0) else 0) = _
        rw [dif_pos hlt]
        have hvert : W.vert ⟨W.n + 3, hlt⟩ := by
          show W.x (⟨W.n + 3, hlt⟩ + 1) = W.x ⟨W.n + 3, hlt⟩
          rw [eS_last, h0xX, hdxX]
        have hxl : W.x ⟨W.n + 3, hlt⟩ = x₀ := hdxX
        have hlol : W.lo ⟨W.n + 3, hlt⟩ = ym - 2 := by
          show min (W.y ⟨W.n + 3, hlt⟩) (W.y (⟨W.n + 3, hlt⟩ + 1)) = ym - 2
          rw [eS_last, hdyX, h0yX]
          exact min_eq_left (by omega)
        have hhil : W.hi ⟨W.n + 3, hlt⟩ = ym := by
          show max (W.y ⟨W.n + 3, hlt⟩) (W.y (⟨W.n + 3, hlt⟩ + 1)) = ym
          rw [eS_last, hdyX, h0yX]
          exact max_eq_right (by omega)
        have hiff : (W.vert ⟨W.n + 3, hlt⟩ ∧ c.1 < W.x ⟨W.n + 3, hlt⟩ ∧ W.lo ⟨W.n + 3, hlt⟩ ≤ c.2 ∧
            c.2 < W.hi ⟨W.n + 3, hlt⟩) ↔ (c.1 < x₀ ∧ ym - 2 ≤ c.2 ∧ c.2 < ym) := by
          rw [hxl, hlol, hhil, show W.vert ⟨W.n + 3, hlt⟩ = True from eq_true hvert, true_and]
        exact if_congr hiff rfl rfl
      have hfW'last : fW' (W.n + 3) = 0 := by
        have hlt : W.n + 3 < W'.n + 4 := by rw [hWn]; omega
        show (if h : W.n + 3 < W'.n + 4 then
            (if W'.vert ⟨W.n + 3, h⟩ ∧ c.1 < W'.x ⟨W.n + 3, h⟩ ∧ W'.lo ⟨W.n + 3, h⟩ ≤ c.2 ∧
              c.2 < W'.hi ⟨W.n + 3, h⟩ then (1 : ZMod 2) else 0) else 0) = 0
        rw [dif_pos hlt]
        apply if_neg
        intro hcon
        have hvert : W'.x (⟨W.n + 3, hlt⟩ + 1) = W'.x ⟨W.n + 3, hlt⟩ := hcon.1
        have eS : (⟨W.n + 3, hlt⟩ + 1 : Fin (W'.n + 4)) = 0 := by
          apply Fin.ext
          rw [Fin.val_add, Fin.val_one']
          have h1m : 1 % (W'.n + 4) = 1 := Nat.mod_eq_of_lt (by omega)
          rw [h1m, val_zero_fin]
          have hm : W'.n + 4 = W.n + 4 := by rw [hWn]
          rw [hm]
          have hm2 : W.n + 3 + 1 = W.n + 4 := by omega
          rw [hm2, Nat.mod_self]
        have e1 : W'.x (⟨W.n + 3, hlt⟩ + 1) = x₀ + 2 := by
          rw [eS]
          show ((Function.update W.v 0 (x₀ + 2, ym - 2)) 0).1 = x₀ + 2
          rw [Function.update_self]
        have e2 : W'.x ⟨W.n + 3, hlt⟩ = x₀ := by
          show ((Function.update W.v 0 (x₀ + 2, ym - 2)) ⟨W.n + 3, hlt⟩).1 = x₀
          rw [Function.update_of_ne hn3ne]
          exact hdxX
        rw [e1, e2] at hvert
        omega
      have hW2 : W.p2 c = (∑ i ∈ Finset.range (W.n + 2), fW (i + 1)) + fW 0 + fW (W.n + 3) := by
        calc W.p2 c = ∑ i ∈ Finset.range (W.n + 4), fW i := hsumW
          _ = ∑ i ∈ Finset.range (W.n + 3), fW i + fW (W.n + 3) := Finset.sum_range_succ fW (W.n + 3)
          _ = (∑ i ∈ Finset.range (W.n + 2), fW (i + 1)) + fW 0 + fW (W.n + 3) := by
            rw [Finset.sum_range_succ']
      have hW'2 : W'.p2 c = (∑ i ∈ Finset.range (W.n + 2), fW' (i + 1)) + fW' 0 + fW' (W.n + 3) := by
        have hm : W'.n + 4 = W.n + 4 := by rw [hWn]
        calc W'.p2 c = ∑ i ∈ Finset.range (W'.n + 4), fW' i := hsumW'
          _ = ∑ i ∈ Finset.range (W.n + 4), fW' i := by rw [hm]
          _ = ∑ i ∈ Finset.range (W.n + 3), fW' i + fW' (W.n + 3) := Finset.sum_range_succ fW' (W.n + 3)
          _ = (∑ i ∈ Finset.range (W.n + 2), fW' (i + 1)) + fW' 0 + fW' (W.n + 3) := by
            rw [Finset.sum_range_succ']
      have hshared : (∑ i ∈ Finset.range (W.n + 2), fW' (i + 1)) =
          (∑ i ∈ Finset.range (W.n + 2), fW (i + 1)) :=
        Finset.sum_congr rfl (fun j hj => htail (j + 1) (by omega)
          (by rw [Finset.mem_range] at hj; omega))
      rw [hW2, hW'2, hfW0, hfW'0, hfWlast, hfW'last, hshared]
      have hclose : ∀ s a b : ZMod 2, (s + 0 + a) + (s + b + 0) = a + b := by
        intro s a b
        rcases hkey s with hs | hs <;> rcases hkey a with ha | ha <;> rcases hkey b with hb | hb <;>
          rw [hs, ha, hb] <;> decide
      exact hclose _ _ _
    -- classification of vertical edges spanning [ym-2, ym] with x ≤ x₀+2
    have hyi_gen : ∀ i : Fin (W.n + 4), W.vert i → W.lo i = ym - 2 →
        (W.y i = ym - 2 ∨ W.y i = ym) := by
      intro i hvert hlo
      rcases W.vert_cases i hvert with hy | hy
      · have h1 : W.lo i = W.y i := by
          show min (W.y i) (W.y (i + 1)) = W.y i
          rw [hy]
          exact min_eq_left (by omega)
        left
        rw [h1] at hlo
        exact hlo
      · have h1 : W.lo i = W.y (i + 1) := by
          show min (W.y i) (W.y (i + 1)) = W.y (i + 1)
          rw [hy]
          exact min_eq_right (by omega)
        right
        rw [h1] at hlo
        omega
    have hCE : ∀ i : Fin (W.n + 4), W.vert i → W.lo i = ym - 2 → W.x i ≤ x₀ + 2 →
        i = ⟨W.n + 3, by omega⟩ := by
      intro i hvert hlo hxle
      have hhiM : max (W.y i) (W.y (i + 1)) = ym := by
        have h : max (W.y i) (W.y (i + 1)) = W.lo i + 2 := W.hi_eq_lo_add_two i hvert
        rw [hlo] at h
        rw [h]
        ring
      have hxge : x₀ ≤ W.x i := by
        rcases hyi_gen i hvert hlo with h | h
        · have htop : W.y (i + 1) = ym := by
            rcases W.vert_cases i hvert with hyc | hyc
            · rw [h] at hyc
              omega
            · have hle : W.y (i + 1) ≤ ym := hmax (i + 1)
              omega
          have h2 : x₀ ≤ W.x (i + 1) := hmin (i + 1) htop
          have h3 : W.x (i + 1) = W.x i := hvert
          rw [h3] at h2
          exact h2
        · exact hmin i h
      have hx12 : W.x i = x₀ ∨ W.x i = x₀ + 2 := by
        have hd2 : (2 : ℤ) ∣ (W.x i - x₀) := by
          have hm : ((W.x i - x₀ : ℤ) : ZMod 2) = 0 := by
            push_cast
            rw [W.parX i, hpa, sub_self]
          exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hm
        obtain ⟨t, ht⟩ := hd2
        omega
      rcases hx12 with hx | hx
      · rcases hyi_gen i hvert hlo with hy | hy
        · exact hjd i (Prod.ext hx hy)
        · have hvi : W.v i = (x₀, ym) := Prod.ext hx hy
          have hi0 : i = 0 := hj0 i hvi
          have hys : W.y (i + 1) = ym - 2 := by
            rcases W.vert_cases i hvert with hyc | hyc
            · have hle : W.y (i + 1) ≤ ym := hmax (i + 1)
              omega
            · omega
          have e : i + 1 = (1 : Fin (W.n + 4)) := by rw [hi0]; exact zero_add 1
          have hwy : W.y (i + 1) = ym := by rw [e]; exact h1yX
          omega
      · rcases hyi_gen i hvert hlo with hy | hy
        · exact absurd (Prod.ext hx hy) (hr i)
        · have hvi : W.v i = (x₀ + 2, ym) := Prod.ext hx hy
          have hi1 : i = 1 := hjr1 i hvi
          have h3 : W.x (i + 1) = W.x i := hvert
          rw [hi1] at h3
          have e11 : (1 + 1 : Fin (W.n + 4)) = 2 := by abel
          rw [e11, h2xX, h1xX] at h3
          omega
    have hF : ∀ a : ℤ, x₀ ≤ a → a ≤ x₀ + 2 →
        (Finset.univ.filter fun i => W.vert i ∧ W.x i ≤ a ∧ W.lo i = ym - 2) =
        ({⟨W.n + 3, by omega⟩} : Finset (Fin (W.n + 4))) := by
      intro a ha0 ha2
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨hvert, hxle, hlo⟩
        exact hCE i hvert hlo (by omega)
      · rintro rfl
        refine ⟨?_, ?_, ?_⟩
        · show W.x (⟨W.n + 3, by omega⟩ + 1) = W.x ⟨W.n + 3, by omega⟩
          rw [eS_last, h0xX, hdxX]
        · rw [hdxX]
          omega
        · show min (W.y ⟨W.n + 3, by omega⟩) (W.y (⟨W.n + 3, by omega⟩ + 1)) = ym - 2
          rw [eS_last, hdyX, h0yX]
          exact min_eq_left (by omega)
    -- cell evaluations
    have hh2 : ((ym - 2 : ℤ) : ZMod 2) = W.b := by
      push_cast
      rw [show (2 : ZMod 2) = 0 from by decide, sub_zero]
      exact hpb
    have hev_d : W.p2 (x₀, ym - 2) = 1 := by
      rw [W.p2_eq_spanning_le x₀ (ym - 2) hh2, hF x₀ (by omega) (by omega),
        Finset.card_singleton, Nat.cast_one]
    have hev_dl : W.p2 (x₀ + 1, ym - 2) = 1 := by
      rw [W.p2_eq_spanning_le (x₀ + 1) (ym - 2) hh2, hF (x₀ + 1) (by omega) (by omega),
        Finset.card_singleton, Nat.cast_one]
    have hev_r : W.p2 (x₀ + 2, ym - 2) = 1 := by
      rw [W.p2_eq_spanning_le (x₀ + 2) (ym - 2) hh2, hF (x₀ + 2) (by omega) (by omega),
        Finset.card_singleton, Nat.cast_one]
    have hband : ∀ a : ℤ, W.p2 (a, ym - 2) = W.p2 (a, ym - 1) := by
      intro a
      have h := W.p2_band a (ym - 2) hh2
      rw [show ym - 2 + 1 = (ym - 1 : ℤ) from by ring] at h
      exact h
    have hev_d1 : W.p2 (x₀, ym - 1) = 1 := by rw [← hband x₀]; exact hev_d
    have hev_dl1 : W.p2 (x₀ + 1, ym - 1) = 1 := by rw [← hband (x₀ + 1)]; exact hev_dl
    have hev_r1 : W.p2 (x₀ + 2, ym - 1) = 1 := by rw [← hband (x₀ + 2)]; exact hev_r
    have hflip1 : ∀ a : ℤ, W.p2 (a, ym - 1) + W'.p2 (a, ym - 1) =
        (if a < x₀ then (1 : ZMod 2) else 0) + (if a < x₀ + 2 then (1 : ZMod 2) else 0) := by
      intro a
      have h := hflip (a, ym - 1)
      have hc1 : ((a, ym - 1) : Cell).1 = a := rfl
      have hc2 : ((a, ym - 1) : Cell).2 = ym - 1 := rfl
      have hiff1 : ((a, ym - 1) : Cell).1 < x₀ ∧ ym - 2 ≤ ((a, ym - 1) : Cell).2 ∧
          ((a, ym - 1) : Cell).2 < ym ↔ a < x₀ := by
        constructor
        · intro hh; omega
        · intro hh; refine ⟨by omega, by omega, by omega⟩
      have hiff2 : ((a, ym - 1) : Cell).1 < x₀ + 2 ∧ ym - 2 ≤ ((a, ym - 1) : Cell).2 ∧
          ((a, ym - 1) : Cell).2 < ym ↔ a < x₀ + 2 := by
        constructor
        · intro hh; omega
        · intro hh; refine ⟨by omega, by omega, by omega⟩
      rw [if_congr hiff1 rfl rfl, if_congr hiff2 rfl rfl] at h
      exact h
    have hev_d1' : W'.p2 (x₀, ym - 1) = 0 := by
      have h := hflip1 x₀
      rw [hev_d1, if_neg (by omega : ¬ (x₀ : ℤ) < x₀),
        if_pos (by omega : (x₀ : ℤ) < x₀ + 2)] at h
      rcases hkey (W'.p2 (x₀, ym - 1)) with h0' | h1'
      · exact h0'
      · rw [h1'] at h
        exact absurd h (by decide)
    have hev_dl1' : W'.p2 (x₀ + 1, ym - 1) = 0 := by
      have h := hflip1 (x₀ + 1)
      rw [hev_dl1, if_neg (by omega : ¬ (x₀ + 1 : ℤ) < x₀),
        if_pos (by omega : (x₀ + 1 : ℤ) < x₀ + 2)] at h
      rcases hkey (W'.p2 (x₀ + 1, ym - 1)) with h0' | h1'
      · exact h0'
      · rw [h1'] at h
        exact absurd h (by decide)
    -- boundary facts
    have hbd : (x₀, ym - 2) ∈ W.boundary := by
      rw [← hn1']
      exact W.vertex_mem_boundary _
    have hvd'n : W'.v ⟨W.n + 3, by omega⟩ = (x₀, ym - 2) := by
      show (Function.update W.v 0 (x₀ + 2, ym - 2)) ⟨W.n + 3, by omega⟩ = (x₀, ym - 2)
      rw [Function.update_of_ne hn3ne]
      exact hn1'
    have hbd' : (x₀, ym - 2) ∈ W'.boundary := by
      rw [← hvd'n]
      exact W'.vertex_mem_boundary _
    have hmidn' : W'.mid ⟨W.n + 3, by omega⟩ = (x₀ + 1, ym - 2) := by
      show midPt ((Function.update W.v 0 (x₀ + 2, ym - 2)) ⟨W.n + 3, by omega⟩)
        ((Function.update W.v 0 (x₀ + 2, ym - 2)) (⟨W.n + 3, by omega⟩ + 1)) = (x₀ + 1, ym - 2)
      rw [eS_last, Function.update_self, Function.update_of_ne hn3ne, hn1']
      simp only [midPt, Prod.mk.injEq]
      constructor <;> omega
    have hbm' : (x₀ + 1, ym - 2) ∈ W'.boundary := by
      rw [← hmidn']
      exact W'.mid_mem_boundary _
    have hbr'W : (x₀ + 2, ym - 2) ∈ W'.boundary := by
      have e : W'.v 0 = (x₀ + 2, ym - 2) := by
        show (Function.update W.v 0 (x₀ + 2, ym - 2)) 0 = (x₀ + 2, ym - 2)
        rw [Function.update_self]
      rw [← e]
      exact W'.vertex_mem_boundary _
    have hmid0' : W'.mid 0 = (x₀ + 2, ym - 1) := by
      show midPt ((Function.update W.v 0 (x₀ + 2, ym - 2)) 0)
        ((Function.update W.v 0 (x₀ + 2, ym - 2)) (0 + 1)) = (x₀ + 2, ym - 1)
      have e1 : (0 + 1 : Fin (W.n + 4)) = 1 := zero_add 1
      rw [e1, Function.update_self, Function.update_of_ne h1ne0, h1]
      simp only [midPt, Prod.mk.injEq]
      constructor <;> omega
    have hbm0' : (x₀ + 2, ym - 1) ∈ W'.boundary := by
      rw [← hmid0']
      exact W'.mid_mem_boundary _
    have hbx0 : (x₀, ym - 1) ∈ W.boundary := by
      have hm : W.mid ⟨W.n + 3, by omega⟩ = (x₀, ym - 1) := by
        show midPt (W.v ⟨W.n + 3, by omega⟩) (W.v (⟨W.n + 3, by omega⟩ + 1)) = (x₀, ym - 1)
        rw [eS_last, hn1', h0]
        simp only [midPt, Prod.mk.injEq]
        constructor <;> omega
      rw [← hm]
      exact W.mid_mem_boundary _
    -- the four lost cells are not on W's boundary
    have hbb1 : (x₀ + 1, ym - 2) ∉ W.boundary := by
      rw [W.mem_boundary (x₀ + 1, ym - 2)]
      push_neg
      constructor
      · intro i hcon
        have hxi : (W.v i).1 = x₀ + 1 := congrArg Prod.fst hcon
        exact hparx1 (hxi ▸ W.parX i)
      · intro i hcon
        rcases W.mid_cases i _ hcon with ⟨hx, h1c, h2c | h2c⟩ | ⟨hy, h1c, h2c | h2c⟩
        · have hc1 : ((x₀ + 1, ym - 2) : Cell).1 = x₀ + 1 := rfl
          have h1x' : (W.v i).1 = x₀ + 1 := by omega
          exact hparx1 (h1x' ▸ W.parX i)
        · have hc1 : ((x₀ + 1, ym - 2) : Cell).1 = x₀ + 1 := rfl
          have h1x' : (W.v i).1 = x₀ + 1 := by omega
          exact hparx1 (h1x' ▸ W.parX i)
        · have hc1 : ((x₀ + 1, ym - 2) : Cell).1 = x₀ + 1 := rfl
          have hc2 : ((x₀ + 1, ym - 2) : Cell).2 = ym - 2 := rfl
          have hvx : (W.v i).1 = x₀ := by omega
          have hvy : (W.v i).2 = ym - 2 := by omega
          have hwy : (W.v (i + 1)).2 = ym - 2 := by rw [hy]; exact hvy
          have hmid1 : (W.mid i).1 = ((W.v i).1 + (W.v (i + 1)).1) / 2 := rfl
          have hmc1 : (W.mid i).1 = x₀ + 1 := congrArg Prod.fst hcon
          have hwx : (W.v (i + 1)).1 = x₀ + 2 := by
            obtain ⟨q, hq⟩ := W.dvd_add_fst i
            omega
          have hvr : W.v (i + 1) = (x₀ + 2, ym - 2) := Prod.ext hwx hwy
          exact absurd hvr (hr (i + 1))
        · have hc1 : ((x₀ + 1, ym - 2) : Cell).1 = x₀ + 1 := rfl
          have hc2 : ((x₀ + 1, ym - 2) : Cell).2 = ym - 2 := rfl
          have hvx : (W.v i).1 = x₀ + 2 := by omega
          have hvy : (W.v i).2 = ym - 2 := by omega
          exact absurd (Prod.ext hvx hvy) (hr i)
    have hbb2 : (x₀ + 1, ym - 1) ∉ W.boundary := by
      rw [W.mem_boundary (x₀ + 1, ym - 1)]
      push_neg
      constructor
      · intro i hcon
        have hxi : (W.v i).1 = x₀ + 1 := congrArg Prod.fst hcon
        exact hparx1 (hxi ▸ W.parX i)
      · intro i hcon
        rcases W.mid_cases i _ hcon with ⟨hx, h1c, h2c | h2c⟩ | ⟨hy, h1c, h2c | h2c⟩
        · have hc1 : ((x₀ + 1, ym - 1) : Cell).1 = x₀ + 1 := rfl
          have h1x' : (W.v i).1 = x₀ + 1 := by omega
          exact hparx1 (h1x' ▸ W.parX i)
        · have hc1 : ((x₀ + 1, ym - 1) : Cell).1 = x₀ + 1 := rfl
          have h1x' : (W.v i).1 = x₀ + 1 := by omega
          exact hparx1 (h1x' ▸ W.parX i)
        · have hc2 : ((x₀ + 1, ym - 1) : Cell).2 = ym - 1 := rfl
          have hwy : (W.v i).2 = ym - 1 := by omega
          exact hpary1 (hwy ▸ W.parY i)
        · have hc2 : ((x₀ + 1, ym - 1) : Cell).2 = ym - 1 := rfl
          have hwy : (W.v i).2 = ym - 1 := by omega
          exact hpary1 (hwy ▸ W.parY i)
    have hbr' : (x₀ + 2, ym - 2) ∉ W.boundary := by
      rw [W.mem_boundary (x₀ + 2, ym - 2)]
      push_neg
      constructor
      · intro i hcon
        exact hr i hcon
      · intro i hcon
        rcases W.mid_cases i _ hcon with ⟨hx, h1c, h2c | h2c⟩ | ⟨hy, h1c, h2c | h2c⟩
        · have hyk : (W.v i).2 = ym - 3 := by
            have hc2 : ((x₀ + 2, ym - 2) : Cell).2 = ym - 2 := rfl
            omega
          exact hpary3 (hyk ▸ W.parY i)
        · have hyk : (W.v i).2 = ym - 1 := by
            have hc2 : ((x₀ + 2, ym - 2) : Cell).2 = ym - 2 := rfl
            omega
          exact hpary1 (hyk ▸ W.parY i)
        · have h1' : (W.v i).1 = x₀ + 1 := by
            have hc1 : ((x₀ + 2, ym - 2) : Cell).1 = x₀ + 2 := rfl
            omega
          exact hparx1 (h1' ▸ W.parX i)
        · have h1' : (W.v i).1 = x₀ + 3 := by
            have hc1 : ((x₀ + 2, ym - 2) : Cell).1 = x₀ + 2 := rfl
            omega
          exact hparx3 (h1' ▸ W.parX i)
    have hbrm : (x₀ + 2, ym - 1) ∉ W.boundary := by
      rw [W.mem_boundary (x₀ + 2, ym - 1)]
      push_neg
      constructor
      · intro i hcon
        have hyk : (W.v i).2 = ym - 1 := congrArg Prod.snd hcon
        exact hpary1 (hyk ▸ W.parY i)
      · intro i hcon
        rcases W.mid_cases i _ hcon with ⟨hx, h1c, h2c | h2c⟩ | ⟨hy, h1c, h2c | h2c⟩
        · have hvy : (W.v i).2 = ym - 2 := by
            have hc2 : ((x₀ + 2, ym - 1) : Cell).2 = ym - 1 := rfl
            omega
          have hvx : (W.v i).1 = x₀ + 2 := h1c.symm
          exact absurd (Prod.ext hvx hvy) (hr i)
        · have hvy : (W.v i).2 = ym := by
            have hc2 : ((x₀ + 2, ym - 1) : Cell).2 = ym - 1 := rfl
            omega
          have hvx : (W.v i).1 = x₀ + 2 := h1c.symm
          have hi1 : i = 1 := hjr1 i (Prod.ext hvx hvy)
          rw [hi1] at hx
          have e11 : (1 + 1 : Fin (W.n + 4)) = 2 := by abel
          rw [e11] at hx
          omega
        · have hyk : (W.v i).2 = ym - 1 := h1c.symm
          exact hpary1 (hyk ▸ W.parY i)
        · have hyk : (W.v i).2 = ym - 1 := h1c.symm
          exact hpary1 (hyk ▸ W.parY i)
    -- boundary implications
    have hB' : ∀ c : Cell, c ∈ W'.boundary → c ∈ W.boundary ∨
        c ∈ ({(x₀ + 1, ym - 2), (x₀ + 2, ym - 2), (x₀ + 2, ym - 1)} : Finset Cell) := by
      intro c hc
      rw [W'.mem_boundary c] at hc
      rcases hc with ⟨j, hj⟩ | ⟨j, hj⟩
      · have hj' : (Function.update W.v 0 (x₀ + 2, ym - 2)) j = c := hj
        by_cases hj0 : j = 0
        · right
          rw [hj0, Function.update_self] at hj'
          rw [← hj']
          exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
        · left
          rw [Function.update_of_ne hj0] at hj'
          rw [← hj']
          exact W.vertex_mem_boundary _
      · by_cases hj0 : j = 0
        · right
          have hm : W'.mid j = (x₀ + 2, ym - 1) := by
            rw [hj0]
            show midPt ((Function.update W.v 0 (x₀ + 2, ym - 2)) 0)
              ((Function.update W.v 0 (x₀ + 2, ym - 2)) (0 + 1)) = (x₀ + 2, ym - 1)
            have e1 : (0 + 1 : Fin (W.n + 4)) = 1 := zero_add 1
            rw [e1, Function.update_self, Function.update_of_ne h1ne0, h1]
            simp only [midPt, Prod.mk.injEq]
            constructor <;> omega
          have hce : c = (x₀ + 2, ym - 1) := hj.symm.trans hm
          rw [hce]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
        · by_cases hjn : j = ⟨W.n + 3, by omega⟩
          · right
            have hm : W'.mid j = (x₀ + 1, ym - 2) := by
              rw [hjn]
              show midPt ((Function.update W.v 0 (x₀ + 2, ym - 2)) ⟨W.n + 3, by omega⟩)
                ((Function.update W.v 0 (x₀ + 2, ym - 2)) (⟨W.n + 3, by omega⟩ + 1)) = (x₀ + 1, ym - 2)
              rw [eS_last, Function.update_self, Function.update_of_ne hn3ne, hn1']
              simp only [midPt, Prod.mk.injEq]
              constructor <;> omega
            have hce : c = (x₀ + 1, ym - 2) := hj.symm.trans hm
            rw [hce]
            exact Finset.mem_insert_self _ _
          · left
            have hi1 : j + 1 ≠ 0 := hsucc_ne j hjn
            have hm : W'.mid j = W.mid j := by
              show midPt ((Function.update W.v 0 (x₀ + 2, ym - 2)) j)
                ((Function.update W.v 0 (x₀ + 2, ym - 2)) (j + 1)) = midPt (W.v j) (W.v (j + 1))
              rw [Function.update_of_ne hj0, Function.update_of_ne hi1]
            rw [hm] at hj
            rw [← hj]
            exact W.mid_mem_boundary _
    have hB : ∀ c : Cell, c ∈ W.boundary → c ∈ W'.boundary ∨
        c ∈ ({(x₀, ym), (x₀ + 1, ym), (x₀, ym - 1)} : Finset Cell) := by
      intro c hc
      rw [W.mem_boundary c] at hc
      rcases hc with ⟨i, hi⟩ | ⟨i, hi⟩
      · by_cases hi0 : i = 0
        · right
          rw [hi0, h0] at hi
          rw [← hi]
          exact Finset.mem_insert_self _ _
        · left
          have hve : W'.v i = c := by
            show (Function.update W.v 0 (x₀ + 2, ym - 2)) i = c
            rw [Function.update_of_ne hi0]
            exact hi
          rw [← hve]
          exact W'.vertex_mem_boundary _
      · by_cases hi0 : i = 0
        · right
          have hm : W.mid i = (x₀ + 1, ym) := by
            rw [hi0]
            show midPt (W.v 0) (W.v (0 + 1)) = (x₀ + 1, ym)
            have e1 : (0 + 1 : Fin (W.n + 4)) = 1 := zero_add 1
            rw [e1, h0, h1]
            simp only [midPt, Prod.mk.injEq]
            constructor <;> omega
          rw [hm] at hi
          rw [← hi]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
        · by_cases hin : i = ⟨W.n + 3, by omega⟩
          · right
            have hm : W.mid i = (x₀, ym - 1) := by
              rw [hin]
              show midPt (W.v ⟨W.n + 3, by omega⟩) (W.v (⟨W.n + 3, by omega⟩ + 1)) = (x₀, ym - 1)
              rw [eS_last, hn1', h0]
              simp only [midPt, Prod.mk.injEq]
              constructor <;> omega
            rw [hm] at hi
            rw [← hi]
            exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
          · left
            have hi1 : i + 1 ≠ 0 := hsucc_ne i hin
            have hme : W'.mid i = c := by
              show midPt ((Function.update W.v 0 (x₀ + 2, ym - 2)) i)
                ((Function.update W.v 0 (x₀ + 2, ym - 2)) (i + 1)) = c
              rw [Function.update_of_ne hi0, Function.update_of_ne hi1]
              exact hi
            rw [← hme]
            exact W'.mid_mem_boundary _
    -- box monotonicity
    have hmaxYe : W.maxY = ym := by
      apply le_antisymm
      · apply Finset.max'_le
        intro y hy
        rw [Finset.mem_image] at hy
        obtain ⟨i, -, rfl⟩ := hy
        exact hmax i
      · have hm : W.y 0 ∈ Finset.univ.image W.y := Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
        have hle : W.y 0 ≤ W.maxY := Finset.le_max' _ _ hm
        exact le_trans (le_of_eq h0yX.symm) hle
    have hminXe : W.minX ≤ x₀ := by
      have hm : W.x 0 ∈ Finset.univ.image W.x := Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
      have hle := Finset.min'_le _ _ hm
      exact le_trans hle (le_of_eq h0xX)
    have hmaxXe : x₀ + 4 ≤ W.maxX := by
      have hm : W.x 2 ∈ Finset.univ.image W.x := Finset.mem_image.mpr ⟨2, Finset.mem_univ _, rfl⟩
      have hle := Finset.le_max' _ _ hm
      exact le_trans (le_of_eq h2xX.symm) hle
    have hminYe : W.minY ≤ ym - 2 := by
      have hm : W.y ⟨W.n + 3, by omega⟩ ∈ Finset.univ.image W.y :=
        Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
      have hle := Finset.min'_le _ _ hm
      exact le_trans hle (le_of_eq hdyX)
    have hminX' : W.minX ≤ W'.minX := by
      have hm : W'.minX ∈ Finset.univ.image W'.x := Finset.min'_mem _ _
      rw [Finset.mem_image] at hm
      obtain ⟨j, -, hj⟩ := hm
      by_cases hj0 : j = 0
      · have e : W'.minX = x₀ + 2 := by
          rw [← hj, hj0]
          show ((Function.update W.v 0 (x₀ + 2, ym - 2)) 0).1 = x₀ + 2
          rw [Function.update_self]
        rw [e]
        exact hminXe.trans (by omega)
      · have e : W'.minX = W.x j := by
          rw [← hj]
          show ((Function.update W.v 0 (x₀ + 2, ym - 2)) j).1 = W.x j
          rw [Function.update_of_ne hj0]
        rw [e]
        exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
    have hmaxX' : W'.maxX ≤ W.maxX := by
      have hm : W'.maxX ∈ Finset.univ.image W'.x := Finset.max'_mem _ _
      rw [Finset.mem_image] at hm
      obtain ⟨j, -, hj⟩ := hm
      by_cases hj0 : j = 0
      · have e : W'.maxX = x₀ + 2 := by
          rw [← hj, hj0]
          show ((Function.update W.v 0 (x₀ + 2, ym - 2)) 0).1 = x₀ + 2
          rw [Function.update_self]
        rw [e]
        exact le_trans (by omega : x₀ + 2 ≤ x₀ + 4) hmaxXe
      · have e : W'.maxX = W.x j := by
          rw [← hj]
          show ((Function.update W.v 0 (x₀ + 2, ym - 2)) j).1 = W.x j
          rw [Function.update_of_ne hj0]
        rw [e]
        exact Finset.le_max' _ _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
    have hminY' : W.minY ≤ W'.minY := by
      have hm : W'.minY ∈ Finset.univ.image W'.y := Finset.min'_mem _ _
      rw [Finset.mem_image] at hm
      obtain ⟨j, -, hj⟩ := hm
      by_cases hj0 : j = 0
      · have e : W'.minY = ym - 2 := by
          rw [← hj, hj0]
          show ((Function.update W.v 0 (x₀ + 2, ym - 2)) 0).2 = ym - 2
          rw [Function.update_self]
        rw [e]
        exact hminYe.trans (by omega)
      · have e : W'.minY = W.y j := by
          rw [← hj]
          show ((Function.update W.v 0 (x₀ + 2, ym - 2)) j).2 = W.y j
          rw [Function.update_of_ne hj0]
        rw [e]
        exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
    have hmaxY'' : W'.maxY ≤ W.maxY := by
      have hm : W'.maxY ∈ Finset.univ.image W'.y := Finset.max'_mem _ _
      rw [Finset.mem_image] at hm
      obtain ⟨j, -, hj⟩ := hm
      by_cases hj0 : j = 0
      · have e : W'.maxY = ym - 2 := by
          rw [← hj, hj0]
          show ((Function.update W.v 0 (x₀ + 2, ym - 2)) 0).2 = ym - 2
          rw [Function.update_self]
        rw [e]
        rw [hmaxYe]
        omega
      · have e : W'.maxY = W.y j := by
          rw [← hj]
          show ((Function.update W.v 0 (x₀ + 2, ym - 2)) j).2 = W.y j
          rw [Function.update_of_ne hj0]
        rw [e]
        exact Finset.le_max' _ _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
    have hmaxY' : W'.maxY ≤ ym := by rw [hmaxYe] at hmaxY''; exact hmaxY''
    -- the sum-of-indicators dichotomy
    have hzhelp : ∀ c : Cell,
        (if c.1 < x₀ ∧ ym - 2 ≤ c.2 ∧ c.2 < ym then (1 : ZMod 2) else 0) +
        (if c.1 < x₀ + 2 ∧ ym - 2 ≤ c.2 ∧ c.2 < ym then (1 : ZMod 2) else 0) = 1 →
        (c.1 = x₀ ∨ c.1 = x₀ + 1) ∧ (c.2 = ym - 2 ∨ c.2 = ym - 1) := by
      intro c h
      by_cases hP : ym - 2 ≤ c.2 ∧ c.2 < ym
      · obtain ⟨hP1, hP2⟩ := hP
        by_cases hcx0 : c.1 < x₀
        · have hcx2 : c.1 < x₀ + 2 := by omega
          rw [if_pos ⟨hcx0, hP1, hP2⟩, if_pos ⟨hcx2, hP1, hP2⟩] at h
          exact absurd h (by decide)
        · by_cases hcx2 : c.1 < x₀ + 2
          · rw [if_neg (fun hh => hcx0 hh.1), if_pos ⟨hcx2, hP1, hP2⟩] at h
            constructor <;> omega
          · rw [if_neg (fun hh => hcx0 hh.1), if_neg (fun hh => hcx2 hh.1)] at h
            exact absurd h (by decide)
      · rw [if_neg (fun hh => hP hh.2), if_neg (fun hh => hP hh.2)] at h
        exact absurd h (by decide)
    -- the interior-set equation
    have hset : W.box.filter (fun c => W.p2 c = 1 ∧ c ∉ W.boundary) =
        W'.box.filter (fun c => W'.p2 c = 1 ∧ c ∉ W'.boundary) ∪
        ({(x₀ + 1, ym - 2), (x₀ + 1, ym - 1), (x₀ + 2, ym - 2), (x₀ + 2, ym - 1)} : Finset Cell) := by
      apply Finset.ext
      intro c
      simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hbox, hp, hb⟩
        by_cases hc4 : c = (x₀ + 1, ym - 2) ∨ c = (x₀ + 1, ym - 1) ∨
            c = (x₀ + 2, ym - 2) ∨ c = (x₀ + 2, ym - 1)
        · exact Or.inr hc4
        · left
          push_neg at hc4
          have hp2' : W'.p2 c = 1 := by
            have hf := hflip c
            rw [hp] at hf
            rcases hkey (W'.p2 c) with h0' | h1'
            · rw [h0', add_zero] at hf
              rcases hzhelp c hf.symm with ⟨hc1 | hc1, hc2 | hc2⟩
              · have hce : c = (x₀, ym - 2) := Prod.ext
                  (by have hh : ((x₀, ym - 2) : Cell).1 = x₀ := rfl; omega)
                  (by have hh : ((x₀, ym - 2) : Cell).2 = ym - 2 := rfl; omega)
                rw [hce] at hb
                exact absurd hbd hb
              · have hce : c = (x₀, ym - 1) := Prod.ext
                  (by have hh : ((x₀, ym - 1) : Cell).1 = x₀ := rfl; omega)
                  (by have hh : ((x₀, ym - 1) : Cell).2 = ym - 1 := rfl; omega)
                rw [hce] at hb
                exact absurd hbx0 hb
              · have hce : c = (x₀ + 1, ym - 2) := Prod.ext
                  (by have hh : ((x₀ + 1, ym - 2) : Cell).1 = x₀ + 1 := rfl; omega)
                  (by have hh : ((x₀ + 1, ym - 2) : Cell).2 = ym - 2 := rfl; omega)
                exact absurd hce hc4.1
              · have hce : c = (x₀ + 1, ym - 1) := Prod.ext
                  (by have hh : ((x₀ + 1, ym - 1) : Cell).1 = x₀ + 1 := rfl; omega)
                  (by have hh : ((x₀ + 1, ym - 1) : Cell).2 = ym - 1 := rfl; omega)
                exact absurd hce hc4.2.1
            · exact h1'
          have hbnd' : c ∉ W'.boundary := by
            intro hcb
            rcases hB' c hcb with hbb | h3
            · exact hb hbb
            · simp only [Finset.mem_insert, Finset.mem_singleton] at h3
              rcases h3 with hce | hce | hce
              · exact absurd hce hc4.1
              · exact absurd hce hc4.2.2.1
              · exact absurd hce hc4.2.2.2
          have hbox' : c ∈ W'.box := by
            rw [box, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
            refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
            · by_contra hcc
              push_neg at hcc
              rw [W'.p2_eq_zero_of_le_minX hcc] at hp2'
              exact absurd hp2' (by decide)
            · by_contra hcc
              push_neg at hcc
              have h2 : W'.maxX ≤ c.1 := by omega
              rw [W'.p2_eq_zero_of_maxX_le h2] at hp2'
              exact absurd hp2' (by decide)
            · by_contra hcc
              push_neg at hcc
              rw [W'.p2_eq_zero_of_minY hcc] at hp2'
              exact absurd hp2' (by decide)
            · by_contra hcc
              push_neg at hcc
              have h2 : W'.maxY ≤ c.2 := by omega
              rw [W'.p2_eq_zero_of_maxY h2] at hp2'
              exact absurd hp2' (by decide)
          exact ⟨hbox', hp2', hbnd'⟩
      · rintro (⟨hbox, hp, hb⟩ | hc4)
        · have hboxW : c ∈ W.box := by
            rw [box, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hbox ⊢
            obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hbox
            exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
          have hp2 : W.p2 c = 1 := by
            have hf := hflip c
            rw [hp] at hf
            rcases hkey (W.p2 c) with h0' | h1'
            · rw [h0', zero_add] at hf
              rcases hzhelp c hf.symm with ⟨hc1 | hc1, hc2 | hc2⟩
              · have hce : c = (x₀, ym - 2) := Prod.ext
                  (by have hh : ((x₀, ym - 2) : Cell).1 = x₀ := rfl; omega)
                  (by have hh : ((x₀, ym - 2) : Cell).2 = ym - 2 := rfl; omega)
                rw [hce] at hb
                exact absurd hbd' hb
              · have hce : c = (x₀, ym - 1) := Prod.ext
                  (by have hh : ((x₀, ym - 1) : Cell).1 = x₀ := rfl; omega)
                  (by have hh : ((x₀, ym - 1) : Cell).2 = ym - 1 := rfl; omega)
                rw [hce] at hp
                rw [hev_d1'] at hp
                exact absurd hp (by decide)
              · have hce : c = (x₀ + 1, ym - 2) := Prod.ext
                  (by have hh : ((x₀ + 1, ym - 2) : Cell).1 = x₀ + 1 := rfl; omega)
                  (by have hh : ((x₀ + 1, ym - 2) : Cell).2 = ym - 2 := rfl; omega)
                rw [hce] at hb
                exact absurd hbm' hb
              · have hce : c = (x₀ + 1, ym - 1) := Prod.ext
                  (by have hh : ((x₀ + 1, ym - 1) : Cell).1 = x₀ + 1 := rfl; omega)
                  (by have hh : ((x₀ + 1, ym - 1) : Cell).2 = ym - 1 := rfl; omega)
                rw [hce] at hp
                rw [hev_dl1'] at hp
                exact absurd hp (by decide)
            · exact h1'
          have hbnd : c ∉ W.boundary := by
            intro hcb
            rcases hB c hcb with hb' | h3
            · exact hb hb'
            · simp only [Finset.mem_insert, Finset.mem_singleton] at h3
              rcases h3 with hce | hce | hce
              · rw [hce] at hp
                have hz := W'.p2_eq_zero_of_maxY (c := (x₀, ym)) hmaxY'
                rw [hz] at hp
                exact absurd hp (by decide)
              · rw [hce] at hp
                have hz := W'.p2_eq_zero_of_maxY (c := (x₀ + 1, ym)) hmaxY'
                rw [hz] at hp
                exact absurd hp (by decide)
              · rw [hce] at hp
                rw [hev_d1'] at hp
                exact absurd hp (by decide)
          exact ⟨hboxW, hp2, hbnd⟩
        · rcases hc4 with hce | hce | hce | hce
          · have hboxm : (x₀ + 1, ym - 2) ∈ W.box := by
              rw [box, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
              exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
            rw [hce]
            exact ⟨hboxm, hev_dl, hbb1⟩
          · have hboxm : (x₀ + 1, ym - 1) ∈ W.box := by
              rw [box, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
              exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
            rw [hce]
            exact ⟨hboxm, hev_dl1, hbb2⟩
          · have hboxm : (x₀ + 2, ym - 2) ∈ W.box := by
              rw [box, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
              exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
            rw [hce]
            exact ⟨hboxm, hev_r, hbr'⟩
          · have hboxm : (x₀ + 2, ym - 1) ∈ W.box := by
              rw [box, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
              exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
            rw [hce]
            exact ⟨hboxm, hev_r1, hbrm⟩
    have hdisj : Disjoint (W'.box.filter fun c => W'.p2 c = 1 ∧ c ∉ W'.boundary)
        ({(x₀ + 1, ym - 2), (x₀ + 1, ym - 1), (x₀ + 2, ym - 2), (x₀ + 2, ym - 1)} : Finset Cell) := by
      rw [Finset.disjoint_left]
      intro c hc hc2
      rw [Finset.mem_filter] at hc
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc2
      rcases hc2 with hce | hce | hce | hce
      · rw [hce] at hc
        exact hc.2.2 hbm'
      · rw [hce] at hc
        rw [hev_dl1'] at hc
        exact absurd hc.2.1 (by decide)
      · rw [hce] at hc
        exact hc.2.2 hbr'W
      · rw [hce] at hc
        exact hc.2.2 hbm0'
    have hne1e : (x₀ + 1, ym - 2) ∉
        ({(x₀ + 1, ym - 1), (x₀ + 2, ym - 2), (x₀ + 2, ym - 1)} : Finset Cell) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      push_neg
      refine ⟨?_, ?_, ?_⟩ <;>
        (intro h; have := (Prod.mk.injEq ..).mp h; omega)
    have hne2e : (x₀ + 1, ym - 1) ∉ ({(x₀ + 2, ym - 2), (x₀ + 2, ym - 1)} : Finset Cell) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      push_neg
      refine ⟨?_, ?_⟩ <;>
        (intro h; have := (Prod.mk.injEq ..).mp h; omega)
    have hne3e : (x₀ + 2, ym - 2) ∉ ({(x₀ + 2, ym - 1)} : Finset Cell) := by
      simp only [Finset.mem_singleton]
      intro h
      have := (Prod.mk.injEq ..).mp h
      omega
    have hcard : (W.box.filter fun c => W.p2 c = 1 ∧ c ∉ W.boundary).card =
        (W'.box.filter fun c => W'.p2 c = 1 ∧ c ∉ W'.boundary).card + 4 := by
      rw [hset, Finset.card_union_of_disjoint hdisj, Finset.card_insert_of_notMem hne1e,
        Finset.card_insert_of_notMem hne2e, Finset.card_insert_of_notMem hne3e,
        Finset.card_singleton]
    rw [W.I_eq, W'.I_eq, hcard]

set_option maxHeartbeats 800000 in
theorem pushLoop_T (W : OrthoLoop) (x₀ ym : ℤ) (h0 : W.v 0 = (x₀, ym))
    (h1 : W.v 1 = (x₀ + 2, ym)) (hn1 : W.v (-1) = (x₀, ym - 2))
    (hr : ∀ i, W.v i ≠ (x₀ + 2, ym - 2)) :
    ({ a := W.a, b := W.b, n := W.n, v := Function.update W.v 0 (x₀ + 2, ym - 2), inj := pushLoop_inj W x₀ ym hr, step := pushLoop_step W x₀ ym h1 hn1, par := pushLoop_par W x₀ ym h0, simple := pushLoop_simple W x₀ ym h0 h1 hn1 hr } : OrthoLoop).T = W.T + 4 := by
  classical
  set W' := ({ a := W.a, b := W.b, n := W.n, v := Function.update W.v 0 (x₀ + 2, ym - 2), inj := pushLoop_inj W x₀ ym hr, step := pushLoop_step W x₀ ym h1 hn1, par := pushLoop_par W x₀ ym h0, simple := pushLoop_simple W x₀ ym h0 h1 hn1 hr } : OrthoLoop)
  have hWn : W'.n = W.n := rfl
  have h1ne0 := push_h1ne0 W
  have hn3ne := push_hn3ne W
  have hn1' := push_hn1' W x₀ ym hn1
  · -- T: W'.T = W.T + 4
    let wW : ℕ → ℤ := fun i =>
      if h : i < W.n + 4 then (W.v ⟨i, h⟩).1 * (W.v ⟨(i + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩).2 -
        (W.v ⟨(i + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩).1 * (W.v ⟨i, h⟩).2 else 0
    let wW' : ℕ → ℤ := fun j =>
      if h : j < W'.n + 4 then (W'.v ⟨j, h⟩).1 * (W'.v ⟨(j + 1) % (W'.n + 4), Nat.mod_lt _ (by omega)⟩).2 -
        (W'.v ⟨(j + 1) % (W'.n + 4), Nat.mod_lt _ (by omega)⟩).1 * (W'.v ⟨j, h⟩).2 else 0
    have hwW : ∀ i : Fin (W.n + 4), W.x i * W.y (i + 1) - W.x (i + 1) * W.y i = wW ↑i := by
      intro i
      have hi : ↑i < W.n + 4 := i.isLt
      have h1 : (⟨(↑i + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ : Fin (W.n + 4)) = i + 1 := by
        apply Fin.ext
        rw [Fin.val_add, Fin.val_one']
        have h1m : 1 % (W.n + 4) = 1 := Nat.mod_eq_of_lt (by omega)
        rw [h1m]
      have hi2 : (⟨↑i, hi⟩ : Fin (W.n + 4)) = i := Fin.ext rfl
      show W.x i * W.y (i + 1) - W.x (i + 1) * W.y i =
        if h : ↑i < W.n + 4 then (W.v ⟨↑i, h⟩).1 * (W.v ⟨(↑i + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩).2 -
          (W.v ⟨(↑i + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩).1 * (W.v ⟨↑i, h⟩).2 else 0
      rw [dif_pos hi, hi2, h1, OrthoLoop.x, OrthoLoop.y]
    have hwW' : ∀ j : Fin (W'.n + 4), W'.x j * W'.y (j + 1) - W'.x (j + 1) * W'.y j = wW' ↑j := by
      intro j
      have hj : ↑j < W'.n + 4 := j.isLt
      have h1 : (⟨(↑j + 1) % (W'.n + 4), Nat.mod_lt _ (by omega)⟩ : Fin (W'.n + 4)) = j + 1 := by
        apply Fin.ext
        rw [Fin.val_add, Fin.val_one']
        have h1m : 1 % (W'.n + 4) = 1 := Nat.mod_eq_of_lt (by omega)
        rw [h1m]
      have hj2 : (⟨↑j, hj⟩ : Fin (W'.n + 4)) = j := Fin.ext rfl
      show W'.x j * W'.y (j + 1) - W'.x (j + 1) * W'.y j =
        if h : ↑j < W'.n + 4 then (W'.v ⟨↑j, h⟩).1 * (W'.v ⟨(↑j + 1) % (W'.n + 4), Nat.mod_lt _ (by omega)⟩).2 -
          (W'.v ⟨(↑j + 1) % (W'.n + 4), Nat.mod_lt _ (by omega)⟩).1 * (W'.v ⟨↑j, h⟩).2 else 0
      rw [dif_pos hj, hj2, h1, OrthoLoop.x, OrthoLoop.y]
    have hWsum : 2 * W.T = ∑ i ∈ Finset.range (W.n + 4), wW i := by
      rw [W.two_mul_T, Finset.sum_congr rfl (fun i _ => hwW i)]
      exact Fin.sum_univ_eq_sum_range wW (W.n + 4)
    have hW'sum : 2 * W'.T = ∑ i ∈ Finset.range (W'.n + 4), wW' i := by
      rw [W'.two_mul_T, Finset.sum_congr rfl (fun i _ => hwW' i)]
      exact Fin.sum_univ_eq_sum_range wW' (W'.n + 4)
    have hshift : ∀ j : ℕ, 1 ≤ j → j ≤ W.n + 2 → wW' j = wW j := by
      intro j hj1 hj2
      have hjW : j < W.n + 4 := by omega
      have hjW' : j < W'.n + 4 := by rw [hWn]; omega
      have e0 : (⟨j, hjW'⟩ : Fin (W'.n + 4)) ≠ 0 := by
        intro h0
        have hv := congrArg Fin.val h0
        have hvR : ((⟨j, hjW'⟩ : Fin (W'.n + 4)) : ℕ) = j := rfl
        rw [hvR, val_zero_fin] at hv
        omega
      have eS : (⟨(j + 1) % (W'.n + 4), Nat.mod_lt _ (by omega)⟩ : Fin (W'.n + 4)) ≠ 0 := by
        intro h0
        have hv := congrArg Fin.val h0
        have hvR : ((⟨(j + 1) % (W'.n + 4), Nat.mod_lt _ (by omega)⟩ : Fin (W'.n + 4)) : ℕ) = j + 1 := by
          show (j + 1) % (W'.n + 4) = j + 1
          rw [hWn]
          exact Nat.mod_eq_of_lt (by omega)
        rw [hvR, val_zero_fin] at hv
        omega
      have e1 : W'.v ⟨j, hjW'⟩ = W.v ⟨j, hjW⟩ := by
        show (Function.update W.v 0 (x₀ + 2, ym - 2)) ⟨j, hjW'⟩ = W.v ⟨j, hjW⟩
        rw [Function.update_of_ne e0]
      have e2 : W'.v ⟨(j + 1) % (W'.n + 4), Nat.mod_lt _ (by omega)⟩ =
          W.v ⟨(j + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ := by
        have e3 : (⟨(j + 1) % (W'.n + 4), Nat.mod_lt _ (by omega)⟩ : Fin (W'.n + 4)) =
            ⟨(j + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ := by
          apply Fin.ext
          show ((j + 1) % (W'.n + 4) : ℕ) = (j + 1) % (W.n + 4)
          rw [hWn]
        rw [e3]
        show (Function.update W.v 0 (x₀ + 2, ym - 2)) ⟨(j + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ =
          W.v ⟨(j + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩
        rw [Function.update_of_ne (by
          intro h0
          have hv := congrArg Fin.val h0
          have hvR : ((⟨(j + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ : Fin (W.n + 4)) : ℕ) = j + 1 := by
            show (j + 1) % (W.n + 4) = j + 1
            exact Nat.mod_eq_of_lt (by omega)
          rw [hvR, val_zero_fin] at hv
          omega)]
      show (if h : j < W'.n + 4 then (W'.v ⟨j, h⟩).1 * (W'.v ⟨(j + 1) % (W'.n + 4), Nat.mod_lt _ (by omega)⟩).2 -
          (W'.v ⟨(j + 1) % (W'.n + 4), Nat.mod_lt _ (by omega)⟩).1 * (W'.v ⟨j, h⟩).2 else 0) =
        (if h : j < W.n + 4 then (W.v ⟨j, h⟩).1 * (W.v ⟨(j + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩).2 -
          (W.v ⟨(j + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩).1 * (W.v ⟨j, h⟩).2 else 0)
      rw [dif_pos hjW', dif_pos hjW, e1, e2]
    have hw0 : wW 0 = x₀ * ym - (x₀ + 2) * ym := by
      have h0lt : 0 < W.n + 4 := by omega
      show (if h : 0 < W.n + 4 then (W.v ⟨0, h⟩).1 * (W.v ⟨(0 + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩).2 -
        (W.v ⟨(0 + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩).1 * (W.v ⟨0, h⟩).2 else 0) = _
      rw [dif_pos h0lt]
      have e0 : (⟨0, h0lt⟩ : Fin (W.n + 4)) = 0 := Fin.ext rfl
      have e1 : (⟨(0 + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ : Fin (W.n + 4)) = 1 := by
        apply Fin.ext
        show ((0 + 1) % (W.n + 4) : ℕ) = ((1 : Fin (W.n + 4)) : ℕ)
        rw [val_one_fin]
        exact Nat.mod_eq_of_lt (by omega)
      rw [e0, e1, h0, h1]
    have hw0' : wW' 0 = (x₀ + 2) * ym - (x₀ + 2) * (ym - 2) := by
      have h0lt : 0 < W'.n + 4 := by rw [hWn]; omega
      show (if h : 0 < W'.n + 4 then (W'.v ⟨0, h⟩).1 * (W'.v ⟨(0 + 1) % (W'.n + 4), Nat.mod_lt _ (by omega)⟩).2 -
        (W'.v ⟨(0 + 1) % (W'.n + 4), Nat.mod_lt _ (by omega)⟩).1 * (W'.v ⟨0, h⟩).2 else 0) = _
      rw [dif_pos h0lt]
      have e0 : (⟨0, h0lt⟩ : Fin (W'.n + 4)) = 0 := Fin.ext rfl
      have e1 : (⟨(0 + 1) % (W'.n + 4), Nat.mod_lt _ (by omega)⟩ : Fin (W'.n + 4)) = 1 := by
        apply Fin.ext
        show ((0 + 1) % (W'.n + 4) : ℕ) = ((1 : Fin (W'.n + 4)) : ℕ)
        rw [val_one_fin]
        rw [hWn]
        exact Nat.mod_eq_of_lt (by omega)
      rw [e0, e1]
      show ((Function.update W.v 0 (x₀ + 2, ym - 2)) 0).1 *
          ((Function.update W.v 0 (x₀ + 2, ym - 2)) 1).2 -
        ((Function.update W.v 0 (x₀ + 2, ym - 2)) 1).1 * ((Function.update W.v 0 (x₀ + 2, ym - 2)) 0).2 = _
      rw [Function.update_self, Function.update_of_ne h1ne0, h1]
    have hwlast : wW (W.n + 3) = x₀ * ym - x₀ * (ym - 2) := by
      have hlt : W.n + 3 < W.n + 4 := by omega
      show (if h : W.n + 3 < W.n + 4 then (W.v ⟨W.n + 3, h⟩).1 * (W.v ⟨(W.n + 3 + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩).2 -
        (W.v ⟨(W.n + 3 + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩).1 * (W.v ⟨W.n + 3, h⟩).2 else 0) = _
      rw [dif_pos hlt]
      have eS : (⟨(W.n + 3 + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ : Fin (W.n + 4)) = 0 := by
        apply Fin.ext
        show ((W.n + 3 + 1) % (W.n + 4) : ℕ) = ((0 : Fin (W.n + 4)) : ℕ)
        rw [val_zero_fin]
        have hm : W.n + 3 + 1 = W.n + 4 := by omega
        rw [hm, Nat.mod_self]
      rw [eS, hn1', h0]
    have hwlast' : wW' (W.n + 3) = x₀ * (ym - 2) - (x₀ + 2) * (ym - 2) := by
      have hlt : W.n + 3 < W'.n + 4 := by rw [hWn]; omega
      show (if h : W.n + 3 < W'.n + 4 then (W'.v ⟨W.n + 3, h⟩).1 * (W'.v ⟨(W.n + 3 + 1) % (W'.n + 4), Nat.mod_lt _ (by omega)⟩).2 -
        (W'.v ⟨(W.n + 3 + 1) % (W'.n + 4), Nat.mod_lt _ (by omega)⟩).1 * (W'.v ⟨W.n + 3, h⟩).2 else 0) = _
      rw [dif_pos hlt]
      have eS : (⟨(W.n + 3 + 1) % (W'.n + 4), Nat.mod_lt _ (by omega)⟩ : Fin (W'.n + 4)) = 0 := by
        apply Fin.ext
        show ((W.n + 3 + 1) % (W'.n + 4) : ℕ) = 0
        have hm : W'.n + 4 = W.n + 4 := by rw [hWn]
        rw [hm]
        have hm2 : W.n + 3 + 1 = W.n + 4 := by omega
        rw [hm2, Nat.mod_self]
      rw [eS]
      show ((Function.update W.v 0 (x₀ + 2, ym - 2)) ⟨W.n + 3, hlt⟩).1 *
          ((Function.update W.v 0 (x₀ + 2, ym - 2)) 0).2 -
        ((Function.update W.v 0 (x₀ + 2, ym - 2)) 0).1 * ((Function.update W.v 0 (x₀ + 2, ym - 2)) ⟨W.n + 3, hlt⟩).2 = _
      rw [Function.update_self, Function.update_of_ne hn3ne, hn1']
    have hW2 : 2 * W.T = (∑ i ∈ Finset.range (W.n + 2), wW (i + 1)) + wW 0 + wW (W.n + 3) := by
      calc 2 * W.T = ∑ i ∈ Finset.range (W.n + 4), wW i := hWsum
        _ = ∑ i ∈ Finset.range (W.n + 3), wW i + wW (W.n + 3) := Finset.sum_range_succ wW (W.n + 3)
        _ = (∑ i ∈ Finset.range (W.n + 2), wW (i + 1)) + wW 0 + wW (W.n + 3) := by
          rw [Finset.sum_range_succ']
    have hW'2 : 2 * W'.T = (∑ i ∈ Finset.range (W.n + 2), wW' (i + 1)) + wW' 0 + wW' (W.n + 3) := by
      have hm : W'.n + 4 = W.n + 4 := by rw [hWn]
      calc 2 * W'.T = ∑ i ∈ Finset.range (W'.n + 4), wW' i := hW'sum
        _ = ∑ i ∈ Finset.range (W.n + 4), wW' i := by rw [hm]
        _ = ∑ i ∈ Finset.range (W.n + 3), wW' i + wW' (W.n + 3) := Finset.sum_range_succ wW' (W.n + 3)
        _ = (∑ i ∈ Finset.range (W.n + 2), wW' (i + 1)) + wW' 0 + wW' (W.n + 3) := by
          rw [Finset.sum_range_succ']
    have hmid : (∑ i ∈ Finset.range (W.n + 2), wW' (i + 1)) = (∑ i ∈ Finset.range (W.n + 2), wW (i + 1)) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      exact hshift (j + 1) (by omega) (by omega)
    have hT2 : 2 * W'.T = 2 * W.T + 8 := by
      rw [hW'2, hW2, hmid, hw0, hw0', hwlast, hwlast']
      ring
    omega

set_option maxHeartbeats 800000 in
/-- Case (C1): push the corner in, replacing `v` by `r′`. -/
theorem push_case (W : OrthoLoop) (x₀ ym : ℤ)
    (h0 : W.v 0 = (x₀, ym)) (hmax : ∀ i, (W.v i).2 ≤ ym)
    (hmin : ∀ i, (W.v i).2 = ym → x₀ ≤ (W.v i).1)
    (h1 : W.v 1 = (x₀ + 2, ym)) (h2 : W.v 2 = (x₀ + 4, ym))
    (hn1 : W.v (-1) = (x₀, ym - 2))
    (hr : ∀ i, W.v i ≠ (x₀ + 2, ym - 2)) :
    ∃ W' : OrthoLoop, W'.I + 4 = W.I ∧ W'.T = W.T + 4 ∧ W'.L = W.L := by
  classical
  exact ⟨({ a := W.a, b := W.b, n := W.n, v := Function.update W.v 0 (x₀ + 2, ym - 2), inj := pushLoop_inj W x₀ ym hr, step := pushLoop_step W x₀ ym h1 hn1, par := pushLoop_par W x₀ ym h0, simple := pushLoop_simple W x₀ ym h0 h1 hn1 hr } : OrthoLoop), pushLoop_I W x₀ ym h0 hmax hmin h1 h2 hn1 hr,
    pushLoop_T W x₀ ym h0 h1 hn1 hr, rfl⟩


/-! ## Glue lemmas: invariance of the crossing parity under safe steps -/


theorem fin_add_one_sub_one {n : ℕ} (i : Fin (n + 4)) : (i + 1 : Fin (n + 4)) - 1 = i := by
  ext
  simp only [Fin.val_sub, Fin.val_add, Fin.val_one]
  have h := i.is_lt
  by_cases hlt : (i : ℕ) + 1 < n + 4
  · rw [Nat.mod_eq_of_lt hlt, show n + 4 - 1 + ((i : ℕ) + 1) = (i : ℕ) + (n + 4) by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt h]
  · have hge : (i : ℕ) + 1 = n + 4 := by omega
    rw [hge, Nat.mod_self, show n + 4 - 1 + 0 = n + 3 by omega,
      Nat.mod_eq_of_lt (show n + 3 < n + 4 by omega)]
    omega

theorem fin_sub_one_add_one {n : ℕ} (i : Fin (n + 4)) : (i - 1 : Fin (n + 4)) + 1 = i := by
  ext
  simp only [Fin.val_sub, Fin.val_add, Fin.val_one]
  have h := i.is_lt
  by_cases h0 : (i : ℕ) = 0
  · rw [h0, show n + 4 - 1 + 0 = n + 3 by omega, Nat.mod_eq_of_lt (show n + 3 < n + 4 by omega),
      show n + 3 + 1 = n + 4 by omega, Nat.mod_self]
  · have h1 : (n + 4 - 1 + (i : ℕ)) % (n + 4) = (i : ℕ) - 1 := by
      rw [show n + 4 - 1 + (i : ℕ) = ((i : ℕ) - 1) + (n + 4) by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
    rw [h1, show (i : ℕ) - 1 + 1 = (i : ℕ) by omega, Nat.mod_eq_of_lt h]

/-- `p2` shift by one in x: only vertical edges at the crossed x-level matter. -/
theorem p2_succ (W : OrthoLoop) (X y : ℤ) :
    W.p2 (X + 1, y) = W.p2 (X, y) +
      (∑ i : Fin (W.n + 4),
        if W.vert i ∧ W.x i = X + 1 ∧ W.lo i ≤ y ∧ y < W.hi i then (1 : ZMod 2) else 0) := by
  have e1 : W.p2 (X + 1, y) = ∑ i : Fin (W.n + 4),
      if W.vert i ∧ X + 1 < W.x i ∧ W.lo i ≤ y ∧ y < W.hi i then (1 : ZMod 2) else 0 := rfl
  have e2 : W.p2 (X, y) = ∑ i : Fin (W.n + 4),
      if W.vert i ∧ X < W.x i ∧ W.lo i ≤ y ∧ y < W.hi i then (1 : ZMod 2) else 0 := rfl
  rw [e1, e2, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h1 : W.vert i ∧ W.x i = X + 1 ∧ W.lo i ≤ y ∧ y < W.hi i
  · have h1c := h1
    obtain ⟨hv, hx, hlo, hhi⟩ := h1c
    have hf : ¬ (W.vert i ∧ X + 1 < W.x i ∧ W.lo i ≤ y ∧ y < W.hi i) := by
      intro h
      omega
    have hg : W.vert i ∧ X < W.x i ∧ W.lo i ≤ y ∧ y < W.hi i := ⟨hv, by omega, hlo, hhi⟩
    rw [if_neg hf, if_pos hg, if_pos h1]
    decide
  · rw [if_neg h1, add_zero]
    by_cases h2 : W.vert i ∧ X < W.x i ∧ W.lo i ≤ y ∧ y < W.hi i
    · have h3 : W.vert i ∧ X + 1 < W.x i ∧ W.lo i ≤ y ∧ y < W.hi i := by
        obtain ⟨hv, hx, hlo, hhi⟩ := h2
        refine ⟨hv, ?_, hlo, hhi⟩
        by_contra hlt
        push_neg at hlt
        have hxi : W.x i = X + 1 := by omega
        exact h1 ⟨hv, hxi, hlo, hhi⟩
      rw [if_pos h2, if_pos h3]
    · have h4 : ¬ (W.vert i ∧ X + 1 < W.x i ∧ W.lo i ≤ y ∧ y < W.hi i) := by
        intro h
        exact h2 ⟨h.1, by omega, h.2.2⟩
      rw [if_neg h2, if_neg h4]

/-- `p2` shift by minus one in x. -/
theorem p2_sub (W : OrthoLoop) (X y : ℤ) :
    W.p2 (X - 1, y) = W.p2 (X, y) +
      (∑ i : Fin (W.n + 4),
        if W.vert i ∧ W.x i = X ∧ W.lo i ≤ y ∧ y < W.hi i then (1 : ZMod 2) else 0) := by
  have e1 : W.p2 (X - 1, y) = ∑ i : Fin (W.n + 4),
      if W.vert i ∧ X - 1 < W.x i ∧ W.lo i ≤ y ∧ y < W.hi i then (1 : ZMod 2) else 0 := rfl
  have e2 : W.p2 (X, y) = ∑ i : Fin (W.n + 4),
      if W.vert i ∧ X < W.x i ∧ W.lo i ≤ y ∧ y < W.hi i then (1 : ZMod 2) else 0 := rfl
  rw [e1, e2, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h1 : W.vert i ∧ W.x i = X ∧ W.lo i ≤ y ∧ y < W.hi i
  · have h1c := h1
    obtain ⟨hv, hx, hlo, hhi⟩ := h1c
    have hf : W.vert i ∧ X - 1 < W.x i ∧ W.lo i ≤ y ∧ y < W.hi i := ⟨hv, by omega, hlo, hhi⟩
    have hg : ¬ (W.vert i ∧ X < W.x i ∧ W.lo i ≤ y ∧ y < W.hi i) := by
      intro h
      omega
    rw [if_pos hf, if_neg hg, if_pos h1]
    decide
  · rw [if_neg h1, add_zero]
    by_cases h2 : W.vert i ∧ X < W.x i ∧ W.lo i ≤ y ∧ y < W.hi i
    · have h3 : W.vert i ∧ X - 1 < W.x i ∧ W.lo i ≤ y ∧ y < W.hi i := by
        obtain ⟨hv, hx, hlo, hhi⟩ := h2
        exact ⟨hv, by omega, hlo, hhi⟩
      rw [if_pos h2, if_pos h3]
    · have h4 : ¬ (W.vert i ∧ X - 1 < W.x i ∧ W.lo i ≤ y ∧ y < W.hi i) := by
        intro h
        exact h2 ⟨h.1, by omega, h.2.2⟩
      rw [if_neg h2, if_neg h4]



/-- In `ZMod 2`, an indicator splits over an exclusive disjunction. -/
theorem zmod2_if_split {P P1 P2 : Prop} [Decidable P] [Decidable P1] [Decidable P2]
    (h : P ↔ P1 ∨ P2) (hx : ¬(P1 ∧ P2)) :
    (if P then (1 : ZMod 2) else 0) = (if P1 then 1 else 0) + (if P2 then 1 else 0) := by
  by_cases h1 : P1 <;> by_cases h2 : P2
  · exfalso
    exact hx ⟨h1, h2⟩
  · have hP : P := h.mpr (Or.inl h1)
    simp [hP, h1, h2]
  · have hP : P := h.mpr (Or.inr h2)
    simp [hP, h1, h2]
  · have hP : ¬ P := by
      intro hp
      rcases h.mp hp with g | g
      · exact h1 g
      · exact h2 g
    simp [hP, h1, h2]

/-- For a vertical edge, `lo = h` iff one endpoint is at height `h`. -/
theorem lo_eq_iff (W : OrthoLoop) (i : Fin (W.n + 4)) (hv : W.vert i) (h : ℤ) :
    W.lo i = h ↔ (W.y i = h ∧ W.y (i + 1) = h + 2) ∨ (W.y (i + 1) = h ∧ W.y i = h + 2) := by
  have hlo : W.lo i = min (W.y i) (W.y (i + 1)) := rfl
  rw [hlo]
  rcases W.vert_cases i hv with hy | hy
  · rw [hy]
    constructor
    · intro hh
      have hm : min (W.y i) (W.y i + 2) = W.y i := min_eq_left (by omega)
      rw [hm] at hh
      exact Or.inl ⟨hh, by omega⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · rw [h1]
        exact min_eq_left (by omega)
      · omega
  · rw [hy]
    constructor
    · intro hh
      have hm : min (W.y i) (W.y i - 2) = W.y i - 2 := min_eq_right (by omega)
      rw [hm] at hh
      exact Or.inr ⟨hh, by omega⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · omega
      · rw [h1]
        exact min_eq_right (by omega)

/-- For a vertical edge, `hi = h` iff one endpoint is at height `h`. -/
theorem hi_eq_iff (W : OrthoLoop) (i : Fin (W.n + 4)) (hv : W.vert i) (h : ℤ) :
    W.hi i = h ↔ (W.y i = h ∧ W.y (i + 1) = h - 2) ∨ (W.y (i + 1) = h ∧ W.y i = h - 2) := by
  have hhi : W.hi i = max (W.y i) (W.y (i + 1)) := rfl
  rw [hhi]
  rcases W.vert_cases i hv with hy | hy
  · rw [hy]
    constructor
    · intro hh
      have hm : max (W.y i) (W.y i + 2) = W.y i + 2 := max_eq_right (by omega)
      rw [hm] at hh
      exact Or.inr ⟨hh, by omega⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · omega
      · rw [h1]
        exact max_eq_right (by omega)
  · rw [hy]
    constructor
    · intro hh
      have hm : max (W.y i) (W.y i - 2) = W.y i := max_eq_left (by omega)
      rw [hm] at hh
      exact Or.inl ⟨hh, by omega⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · rw [h1]
        exact max_eq_left (by omega)
      · omega



/-- At a boundary-free point `(x₀, h)`, the numbers of vertical edges to the
right with lower/upper endpoint at height `h` are equal mod 2. -/
theorem corner_count_even (W : OrthoLoop) (x₀ h : ℤ)
    (hd : (x₀, h) ∉ W.boundary) :
    (∑ i : Fin (W.n + 4), if W.vert i ∧ x₀ < W.x i ∧ W.lo i = h then (1 : ZMod 2) else 0) +
    (∑ i : Fin (W.n + 4), if W.vert i ∧ x₀ < W.x i ∧ W.hi i = h then (1 : ZMod 2) else 0) = 0 := by
  classical
  -- Step 1: split the `lo`/`hi` conditions into endpoint conditions
  have splitA : ∀ i : Fin (W.n + 4),
      (if W.vert i ∧ x₀ < W.x i ∧ W.lo i = h then (1 : ZMod 2) else 0) =
      (if W.vert i ∧ W.y i = h ∧ W.y (i + 1) = h + 2 ∧ x₀ < W.x i then 1 else 0) +
      (if W.vert i ∧ W.y (i + 1) = h ∧ W.y i = h + 2 ∧ x₀ < W.x i then 1 else 0) := by
    intro i
    by_cases hv : W.vert i
    · apply zmod2_if_split
      · constructor
        · rintro ⟨-, hx, hlo⟩
          rw [W.lo_eq_iff i hv h] at hlo
          rcases hlo with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl ⟨hv, h1, h2, hx⟩
          · exact Or.inr ⟨hv, h1, h2, hx⟩
        · rintro (⟨-, h1, h2, hx⟩ | ⟨-, h1, h2, hx⟩)
          · exact ⟨hv, hx, (W.lo_eq_iff i hv h).mpr (Or.inl ⟨h1, h2⟩)⟩
          · exact ⟨hv, hx, (W.lo_eq_iff i hv h).mpr (Or.inr ⟨h1, h2⟩)⟩
      · rintro ⟨⟨-, h1, h2, -⟩, ⟨-, h3, h4, -⟩⟩
        omega
    · have hn1 : ¬ (W.vert i ∧ x₀ < W.x i ∧ W.lo i = h) := fun hc => hv hc.1
      have hn2 : ¬ (W.vert i ∧ W.y i = h ∧ W.y (i + 1) = h + 2 ∧ x₀ < W.x i) := fun hc => hv hc.1
      have hn3 : ¬ (W.vert i ∧ W.y (i + 1) = h ∧ W.y i = h + 2 ∧ x₀ < W.x i) := fun hc => hv hc.1
      rw [if_neg hn1, if_neg hn2, if_neg hn3, add_zero]
  have splitB : ∀ i : Fin (W.n + 4),
      (if W.vert i ∧ x₀ < W.x i ∧ W.hi i = h then (1 : ZMod 2) else 0) =
      (if W.vert i ∧ W.y i = h ∧ W.y (i + 1) = h - 2 ∧ x₀ < W.x i then 1 else 0) +
      (if W.vert i ∧ W.y (i + 1) = h ∧ W.y i = h - 2 ∧ x₀ < W.x i then 1 else 0) := by
    intro i
    by_cases hv : W.vert i
    · apply zmod2_if_split
      · constructor
        · rintro ⟨-, hx, hhi⟩
          rw [W.hi_eq_iff i hv h] at hhi
          rcases hhi with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl ⟨hv, h1, h2, hx⟩
          · exact Or.inr ⟨hv, h1, h2, hx⟩
        · rintro (⟨-, h1, h2, hx⟩ | ⟨-, h1, h2, hx⟩)
          · exact ⟨hv, hx, (W.hi_eq_iff i hv h).mpr (Or.inl ⟨h1, h2⟩)⟩
          · exact ⟨hv, hx, (W.hi_eq_iff i hv h).mpr (Or.inr ⟨h1, h2⟩)⟩
      · rintro ⟨⟨-, h1, h2, -⟩, ⟨-, h3, h4, -⟩⟩
        omega
    · have hn1 : ¬ (W.vert i ∧ x₀ < W.x i ∧ W.hi i = h) := fun hc => hv hc.1
      have hn2 : ¬ (W.vert i ∧ W.y i = h ∧ W.y (i + 1) = h - 2 ∧ x₀ < W.x i) := fun hc => hv hc.1
      have hn3 : ¬ (W.vert i ∧ W.y (i + 1) = h ∧ W.y i = h - 2 ∧ x₀ < W.x i) := fun hc => hv hc.1
      rw [if_neg hn1, if_neg hn2, if_neg hn3, add_zero]
  have hA : (∑ i : Fin (W.n + 4), if W.vert i ∧ x₀ < W.x i ∧ W.lo i = h then (1 : ZMod 2) else 0) =
      (∑ i : Fin (W.n + 4),
        ((if W.vert i ∧ W.y i = h ∧ W.y (i + 1) = h + 2 ∧ x₀ < W.x i then 1 else 0) +
         (if W.vert i ∧ W.y (i + 1) = h ∧ W.y i = h + 2 ∧ x₀ < W.x i then 1 else 0))) :=
    Finset.sum_congr rfl (fun i _ => splitA i)
  have hB : (∑ i : Fin (W.n + 4), if W.vert i ∧ x₀ < W.x i ∧ W.hi i = h then (1 : ZMod 2) else 0) =
      (∑ i : Fin (W.n + 4),
        ((if W.vert i ∧ W.y i = h ∧ W.y (i + 1) = h - 2 ∧ x₀ < W.x i then 1 else 0) +
         (if W.vert i ∧ W.y (i + 1) = h ∧ W.y i = h - 2 ∧ x₀ < W.x i then 1 else 0))) :=
    Finset.sum_congr rfl (fun i _ => splitB i)
  rw [Finset.sum_add_distrib] at hA hB
  rw [hA, hB]
  -- Step 2: reindex the `(i+1)`-endpoint sums
  have sh2 : (∑ i : Fin (W.n + 4),
      if W.vert i ∧ W.y (i + 1) = h ∧ W.y i = h + 2 ∧ x₀ < W.x i then (1 : ZMod 2) else 0) =
      ∑ i : Fin (W.n + 4),
        if W.vert (i - 1) ∧ W.y i = h ∧ W.y (i - 1) = h + 2 ∧ x₀ < W.x (i - 1) then 1 else 0 := by
    have h1 : (∑ i : Fin (W.n + 4),
        if W.vert i ∧ W.y (i + 1) = h ∧ W.y i = h + 2 ∧ x₀ < W.x i then (1 : ZMod 2) else 0) =
        ∑ i : Fin (W.n + 4),
          (fun j => if W.vert (j - 1) ∧ W.y j = h ∧ W.y (j - 1) = h + 2 ∧ x₀ < W.x (j - 1)
            then (1 : ZMod 2) else 0) (i + 1) := by
      apply Finset.sum_congr rfl
      intro i _
      have h2 : (i + 1 : Fin (W.n + 4)) - 1 = i := fin_add_one_sub_one i
      simp only [h2]
    rw [h1]
    exact Equiv.sum_comp (finShift 1)
      (fun j : Fin (W.n + 4) =>
        (if W.vert (j - 1) ∧ W.y j = h ∧ W.y (j - 1) = h + 2 ∧ x₀ < W.x (j - 1)
          then (1 : ZMod 2) else 0))
  have sh4 : (∑ i : Fin (W.n + 4),
      if W.vert i ∧ W.y (i + 1) = h ∧ W.y i = h - 2 ∧ x₀ < W.x i then (1 : ZMod 2) else 0) =
      ∑ i : Fin (W.n + 4),
        if W.vert (i - 1) ∧ W.y i = h ∧ W.y (i - 1) = h - 2 ∧ x₀ < W.x (i - 1) then 1 else 0 := by
    have h1 : (∑ i : Fin (W.n + 4),
        if W.vert i ∧ W.y (i + 1) = h ∧ W.y i = h - 2 ∧ x₀ < W.x i then (1 : ZMod 2) else 0) =
        ∑ i : Fin (W.n + 4),
          (fun j => if W.vert (j - 1) ∧ W.y j = h ∧ W.y (j - 1) = h - 2 ∧ x₀ < W.x (j - 1)
            then (1 : ZMod 2) else 0) (i + 1) := by
      apply Finset.sum_congr rfl
      intro i _
      have h2 : (i + 1 : Fin (W.n + 4)) - 1 = i := fin_add_one_sub_one i
      simp only [h2]
    rw [h1]
    exact Equiv.sum_comp (finShift 1)
      (fun j : Fin (W.n + 4) =>
        (if W.vert (j - 1) ∧ W.y j = h ∧ W.y (j - 1) = h - 2 ∧ x₀ < W.x (j - 1)
          then (1 : ZMod 2) else 0))
  rw [sh2, sh4]
  -- Step 3: per-vertex collapse to `ep i = [vert i] + [vert (i-1)]`
  have collapse : ∀ i : Fin (W.n + 4),
      ((if W.vert i ∧ W.y i = h ∧ W.y (i + 1) = h + 2 ∧ x₀ < W.x i then (1 : ZMod 2) else 0) +
      (if W.vert (i - 1) ∧ W.y i = h ∧ W.y (i - 1) = h + 2 ∧ x₀ < W.x (i - 1) then 1 else 0)) +
      ((if W.vert i ∧ W.y i = h ∧ W.y (i + 1) = h - 2 ∧ x₀ < W.x i then 1 else 0) +
      (if W.vert (i - 1) ∧ W.y i = h ∧ W.y (i - 1) = h - 2 ∧ x₀ < W.x (i - 1) then 1 else 0)) =
      if W.y i = h ∧ x₀ < W.x i then
        ((if W.vert i then (1 : ZMod 2) else 0) + (if W.vert (i - 1) then 1 else 0)) else 0 := by
    intro i
    by_cases hyh : W.y i = h ∧ x₀ < W.x i
    · obtain ⟨hy, hx⟩ := hyh
      rw [if_pos (show W.y i = h ∧ x₀ < W.x i from ⟨hy, hx⟩)]
      have c13 : (if W.vert i ∧ W.y i = h ∧ W.y (i + 1) = h + 2 ∧ x₀ < W.x i then (1 : ZMod 2) else 0) +
          (if W.vert i ∧ W.y i = h ∧ W.y (i + 1) = h - 2 ∧ x₀ < W.x i then 1 else 0) =
          if W.vert i then (1 : ZMod 2) else 0 := by
        by_cases hv : W.vert i
        · rcases W.vert_cases i hv with hy2 | hy2
          · have c1 : W.vert i ∧ W.y i = h ∧ W.y (i + 1) = h + 2 ∧ x₀ < W.x i :=
              ⟨hv, hy, by omega, hx⟩
            have c3 : ¬ (W.vert i ∧ W.y i = h ∧ W.y (i + 1) = h - 2 ∧ x₀ < W.x i) := by
              intro hc
              omega
            rw [if_pos c1, if_neg c3, if_pos hv, add_zero]
          · have c3 : W.vert i ∧ W.y i = h ∧ W.y (i + 1) = h - 2 ∧ x₀ < W.x i :=
              ⟨hv, hy, by omega, hx⟩
            have c1 : ¬ (W.vert i ∧ W.y i = h ∧ W.y (i + 1) = h + 2 ∧ x₀ < W.x i) := by
              intro hc
              omega
            rw [if_neg c1, if_pos c3, if_pos hv, zero_add]
        · have c1 : ¬ (W.vert i ∧ W.y i = h ∧ W.y (i + 1) = h + 2 ∧ x₀ < W.x i) := by
            intro hc
            exact hv hc.1
          have c3 : ¬ (W.vert i ∧ W.y i = h ∧ W.y (i + 1) = h - 2 ∧ x₀ < W.x i) := by
            intro hc
            exact hv hc.1
          rw [if_neg c1, if_neg c3, if_neg hv, add_zero]
      have c24 : (if W.vert (i - 1) ∧ W.y i = h ∧ W.y (i - 1) = h + 2 ∧ x₀ < W.x (i - 1) then (1 : ZMod 2) else 0) +
          (if W.vert (i - 1) ∧ W.y i = h ∧ W.y (i - 1) = h - 2 ∧ x₀ < W.x (i - 1) then 1 else 0) =
          if W.vert (i - 1) then (1 : ZMod 2) else 0 := by
        by_cases hv : W.vert (i - 1)
        · have h2 : (i - 1 : Fin (W.n + 4)) + 1 = i := fin_sub_one_add_one i
          have hvx : W.x ((i - 1) + 1) = W.x (i - 1) := hv
          rw [h2] at hvx
          have hxi : W.x (i - 1) = W.x i := hvx.symm
          have hvy : W.y ((i - 1) + 1) = W.y (i - 1) + 2 ∨ W.y ((i - 1) + 1) = W.y (i - 1) - 2 :=
            W.vert_cases (i - 1) hv
          rw [h2] at hvy
          rcases hvy with hy2 | hy2
          · have hy3 : W.y (i - 1) = h - 2 := by omega
            have hx2 : x₀ < W.x (i - 1) := by
              rw [hxi]
              exact hx
            have c4 : W.vert (i - 1) ∧ W.y i = h ∧ W.y (i - 1) = h - 2 ∧ x₀ < W.x (i - 1) :=
              ⟨hv, hy, hy3, hx2⟩
            have c2 : ¬ (W.vert (i - 1) ∧ W.y i = h ∧ W.y (i - 1) = h + 2 ∧ x₀ < W.x (i - 1)) := by
              intro hc
              omega
            rw [if_neg c2, if_pos c4, if_pos hv, zero_add]
          · have hy3 : W.y (i - 1) = h + 2 := by omega
            have hx2 : x₀ < W.x (i - 1) := by
              rw [hxi]
              exact hx
            have c2 : W.vert (i - 1) ∧ W.y i = h ∧ W.y (i - 1) = h + 2 ∧ x₀ < W.x (i - 1) :=
              ⟨hv, hy, hy3, hx2⟩
            have c4 : ¬ (W.vert (i - 1) ∧ W.y i = h ∧ W.y (i - 1) = h - 2 ∧ x₀ < W.x (i - 1)) := by
              intro hc
              omega
            rw [if_pos c2, if_neg c4, if_pos hv, add_zero]
        · have c2 : ¬ (W.vert (i - 1) ∧ W.y i = h ∧ W.y (i - 1) = h + 2 ∧ x₀ < W.x (i - 1)) := by
            intro hc
            exact hv hc.1
          have c4 : ¬ (W.vert (i - 1) ∧ W.y i = h ∧ W.y (i - 1) = h - 2 ∧ x₀ < W.x (i - 1)) := by
            intro hc
            exact hv hc.1
          rw [if_neg c2, if_neg c4, if_neg hv, add_zero]
      have hrw : ((if W.vert i ∧ W.y i = h ∧ W.y (i + 1) = h + 2 ∧ x₀ < W.x i then (1 : ZMod 2) else 0) +
          (if W.vert (i - 1) ∧ W.y i = h ∧ W.y (i - 1) = h + 2 ∧ x₀ < W.x (i - 1) then 1 else 0)) +
          ((if W.vert i ∧ W.y i = h ∧ W.y (i + 1) = h - 2 ∧ x₀ < W.x i then 1 else 0) +
          (if W.vert (i - 1) ∧ W.y i = h ∧ W.y (i - 1) = h - 2 ∧ x₀ < W.x (i - 1) then 1 else 0)) =
          ((if W.vert i ∧ W.y i = h ∧ W.y (i + 1) = h + 2 ∧ x₀ < W.x i then (1 : ZMod 2) else 0) +
          (if W.vert i ∧ W.y i = h ∧ W.y (i + 1) = h - 2 ∧ x₀ < W.x i then 1 else 0)) +
          ((if W.vert (i - 1) ∧ W.y i = h ∧ W.y (i - 1) = h + 2 ∧ x₀ < W.x (i - 1) then 1 else 0) +
          (if W.vert (i - 1) ∧ W.y i = h ∧ W.y (i - 1) = h - 2 ∧ x₀ < W.x (i - 1) then 1 else 0)) := by
        ring
      rw [hrw, c13, c24]
    · rw [if_neg (show ¬ (W.y i = h ∧ x₀ < W.x i) from hyh)]
      have t1 : ¬ (W.vert i ∧ W.y i = h ∧ W.y (i + 1) = h + 2 ∧ x₀ < W.x i) := by
        intro hc
        exact hyh ⟨hc.2.1, hc.2.2.2⟩
      have t3 : ¬ (W.vert i ∧ W.y i = h ∧ W.y (i + 1) = h - 2 ∧ x₀ < W.x i) := by
        intro hc
        exact hyh ⟨hc.2.1, hc.2.2.2⟩
      have t2 : ¬ (W.vert (i - 1) ∧ W.y i = h ∧ W.y (i - 1) = h + 2 ∧ x₀ < W.x (i - 1)) := by
        intro hc
        have h2 : (i - 1 : Fin (W.n + 4)) + 1 = i := fin_sub_one_add_one i
        have hvx : W.x ((i - 1) + 1) = W.x (i - 1) := hc.1
        rw [h2] at hvx
        exact hyh ⟨hc.2.1, hvx ▸ hc.2.2.2⟩
      have t4 : ¬ (W.vert (i - 1) ∧ W.y i = h ∧ W.y (i - 1) = h - 2 ∧ x₀ < W.x (i - 1)) := by
        intro hc
        have h2 : (i - 1 : Fin (W.n + 4)) + 1 = i := fin_sub_one_add_one i
        have hvx : W.x ((i - 1) + 1) = W.x (i - 1) := hc.1
        rw [h2] at hvx
        exact hyh ⟨hc.2.1, hvx ▸ hc.2.2.2⟩
      rw [if_neg t1, if_neg t2, if_neg t3, if_neg t4]
      ring
  -- Step 4: merge all four sums and collapse
  simp only [← Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl (fun i _ => collapse i)]
  -- Step 5: `ep` equals `hz` (horizontal-edge incidence) mod 2
  have ep_eq_hz : ∀ i : Fin (W.n + 4),
      (if W.y i = h ∧ x₀ < W.x i then ((if W.vert i then (1 : ZMod 2) else 0) + (if W.vert (i - 1) then 1 else 0)) else 0) =
      (if W.y i = h ∧ x₀ < W.x i then ((if ¬W.vert i then (1 : ZMod 2) else 0) + (if ¬W.vert (i - 1) then 1 else 0)) else 0) := by
    intro i
    by_cases ho : W.y i = h ∧ x₀ < W.x i
    · rw [if_pos ho, if_pos ho]
      by_cases hv : W.vert i
      · rw [if_pos (show W.vert i from hv), if_neg (show ¬¬W.vert i from not_not_intro hv)]
        by_cases hv2 : W.vert (i - 1)
        · rw [if_pos (show W.vert (i - 1) from hv2),
            if_neg (show ¬¬W.vert (i - 1) from not_not_intro hv2)]
          decide
        · rw [if_neg (show ¬W.vert (i - 1) from hv2),
            if_pos (show ¬W.vert (i - 1) from hv2)]
          decide
      · rw [if_neg (show ¬W.vert i from hv), if_pos (show ¬W.vert i from hv)]
        by_cases hv2 : W.vert (i - 1)
        · rw [if_pos (show W.vert (i - 1) from hv2),
            if_neg (show ¬¬W.vert (i - 1) from not_not_intro hv2)]
          decide
        · rw [if_neg (show ¬W.vert (i - 1) from hv2),
            if_pos (show ¬W.vert (i - 1) from hv2)]
          decide
    · rw [if_neg ho, if_neg ho]
  rw [Finset.sum_congr rfl (fun i _ => ep_eq_hz i)]
  -- Step 6: spread into two sums and reindex the second
  have spread : ∀ i : Fin (W.n + 4),
      (if W.y i = h ∧ x₀ < W.x i then ((if ¬W.vert i then (1 : ZMod 2) else 0) + (if ¬W.vert (i - 1) then 1 else 0)) else 0) =
      (if W.y i = h ∧ x₀ < W.x i ∧ ¬W.vert i then (1 : ZMod 2) else 0) +
      (if W.y i = h ∧ x₀ < W.x i ∧ ¬W.vert (i - 1) then 1 else 0) := by
    intro i
    by_cases hc : W.y i = h ∧ x₀ < W.x i
    · rw [if_pos hc]
      by_cases hv : W.vert i
      · rw [if_neg (show ¬¬W.vert i from not_not_intro hv),
          if_neg (show ¬(W.y i = h ∧ x₀ < W.x i ∧ ¬W.vert i) from fun h => h.2.2 hv)]
        by_cases hv2 : W.vert (i - 1)
        · rw [if_neg (show ¬¬W.vert (i - 1) from not_not_intro hv2),
            if_neg (show ¬(W.y i = h ∧ x₀ < W.x i ∧ ¬W.vert (i - 1)) from fun h => h.2.2 hv2)]
        · rw [if_pos (show ¬W.vert (i - 1) from hv2),
            if_pos (show W.y i = h ∧ x₀ < W.x i ∧ ¬W.vert (i - 1) from ⟨hc.1, hc.2, hv2⟩)]
      · rw [if_pos (show ¬W.vert i from hv),
          if_pos (show W.y i = h ∧ x₀ < W.x i ∧ ¬W.vert i from ⟨hc.1, hc.2, hv⟩)]
        by_cases hv2 : W.vert (i - 1)
        · rw [if_neg (show ¬¬W.vert (i - 1) from not_not_intro hv2),
            if_neg (show ¬(W.y i = h ∧ x₀ < W.x i ∧ ¬W.vert (i - 1)) from fun h => h.2.2 hv2)]
        · rw [if_pos (show ¬W.vert (i - 1) from hv2),
            if_pos (show W.y i = h ∧ x₀ < W.x i ∧ ¬W.vert (i - 1) from ⟨hc.1, hc.2, hv2⟩)]
    · rw [if_neg hc]
      have hn1 : ¬ (W.y i = h ∧ x₀ < W.x i ∧ ¬W.vert i) := fun h => hc ⟨h.1, h.2.1⟩
      have hn2 : ¬ (W.y i = h ∧ x₀ < W.x i ∧ ¬W.vert (i - 1)) := fun h => hc ⟨h.1, h.2.1⟩
      rw [if_neg hn1, if_neg hn2, add_zero]
  rw [Finset.sum_congr rfl (fun i _ => spread i), Finset.sum_add_distrib]
  have shz : (∑ i : Fin (W.n + 4), if W.y i = h ∧ x₀ < W.x i ∧ ¬W.vert (i - 1) then (1 : ZMod 2) else 0) =
      ∑ j : Fin (W.n + 4), if W.y (j + 1) = h ∧ x₀ < W.x (j + 1) ∧ ¬W.vert j then 1 else 0 := by
    have h1 : (∑ i : Fin (W.n + 4), if W.y i = h ∧ x₀ < W.x i ∧ ¬W.vert (i - 1) then (1 : ZMod 2) else 0) =
        ∑ i : Fin (W.n + 4),
          (fun j => if W.y (j + 1) = h ∧ x₀ < W.x (j + 1) ∧ ¬W.vert j then (1 : ZMod 2) else 0) (i - 1) := by
      apply Finset.sum_congr rfl
      intro i _
      have h2 : (i - 1 : Fin (W.n + 4)) + 1 = i := fin_sub_one_add_one i
      simp only [h2]
    rw [h1]
    apply Finset.sum_bij (fun a _ => a - 1)
    · intro a _
      simp
    · intro a _ b _ hab
      have h3 : (a - 1 : Fin (W.n + 4)) = (b - 1 : Fin (W.n + 4)) := hab
      have h4 : (a - 1 : Fin (W.n + 4)) + 1 = (b - 1 : Fin (W.n + 4)) + 1 := by rw [h3]
      rw [fin_sub_one_add_one a, fin_sub_one_add_one b] at h4
      exact h4
    · intro b _
      exact ⟨b + 1, Finset.mem_univ _, fin_add_one_sub_one b⟩
    · intro a _
      have h2 : (a - 1 : Fin (W.n + 4)) + 1 = a := fin_sub_one_add_one a
      simp only [h2]
  rw [shz]
  -- Step 7: horizontal edges have constant y; each edge contributes 0 mod 2
  have hz2 : ∀ j : Fin (W.n + 4),
      (if W.y (j + 1) = h ∧ x₀ < W.x (j + 1) ∧ ¬W.vert j then (1 : ZMod 2) else 0) =
      (if W.y j = h ∧ x₀ < W.x (j + 1) ∧ ¬W.vert j then 1 else 0) := by
    intro j
    by_cases hv : W.vert j
    · have hn : ¬ (W.y (j + 1) = h ∧ x₀ < W.x (j + 1) ∧ ¬W.vert j) := by
        intro hc
        exact hc.2.2 hv
      have hn2 : ¬ (W.y j = h ∧ x₀ < W.x (j + 1) ∧ ¬W.vert j) := by
        intro hc
        exact hc.2.2 hv
      rw [if_neg hn, if_neg hn2]
    · rcases W.horiz_cases j hv with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · rw [hy]
      · rw [hy]
  rw [Finset.sum_congr rfl (fun j _ => hz2 j), ← Finset.sum_add_distrib]
  have vanish : ∀ j : Fin (W.n + 4),
      (if W.y j = h ∧ x₀ < W.x j ∧ ¬W.vert j then (1 : ZMod 2) else 0) +
      (if W.y j = h ∧ x₀ < W.x (j + 1) ∧ ¬W.vert j then 1 else 0) = 0 := by
    intro j
    by_cases hv : W.vert j
    · have hn1 : ¬ (W.y j = h ∧ x₀ < W.x j ∧ ¬W.vert j) := fun hc => hc.2.2 hv
      have hn2 : ¬ (W.y j = h ∧ x₀ < W.x (j + 1) ∧ ¬W.vert j) := fun hc => hc.2.2 hv
      rw [if_neg hn1, if_neg hn2]
      ring
    · rcases W.horiz_cases j hv with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · by_cases hyh : W.y j = h
        · by_cases h1 : x₀ < W.x j
          · by_cases h2 : x₀ < W.x (j + 1)
            · rw [if_pos ⟨hyh, h1, hv⟩, if_pos ⟨hyh, h2, hv⟩]
              decide
            · exfalso
              have hxs : W.x j = x₀ ∨ W.x j + 1 = x₀ := by omega
              rcases hxs with hxs | hxs
              · have hvj : W.v j = (x₀, h) := by
                  ext
                  · exact hxs
                  · exact hyh
                exact hd (hvj ▸ W.vertex_mem_boundary j)
              · have hmid : W.mid j = (x₀, h) := by
                  have hr : W.mid j = ((W.x j + W.x (j + 1)) / 2, (W.y j + W.y (j + 1)) / 2) := rfl
                  rw [hr, hx, hy]
                  ext <;> simp <;> omega
                exact hd (hmid ▸ W.mid_mem_boundary j)
          · by_cases h2 : x₀ < W.x (j + 1)
            · exfalso
              have hxs : W.x j = x₀ ∨ W.x j + 1 = x₀ := by omega
              rcases hxs with hxs | hxs
              · have hvj : W.v j = (x₀, h) := by
                  ext
                  · exact hxs
                  · exact hyh
                exact hd (hvj ▸ W.vertex_mem_boundary j)
              · have hmid : W.mid j = (x₀, h) := by
                  have hr : W.mid j = ((W.x j + W.x (j + 1)) / 2, (W.y j + W.y (j + 1)) / 2) := rfl
                  rw [hr, hx, hy]
                  ext <;> simp <;> omega
                exact hd (hmid ▸ W.mid_mem_boundary j)
            · have hn1 : ¬ (W.y j = h ∧ x₀ < W.x j ∧ ¬W.vert j) := by
                intro hc
                exact h1 hc.2.1
              have hn2 : ¬ (W.y j = h ∧ x₀ < W.x (j + 1) ∧ ¬W.vert j) := by
                intro hc
                exact h2 hc.2.1
              rw [if_neg hn1, if_neg hn2]
              ring
        · have hn1 : ¬ (W.y j = h ∧ x₀ < W.x j ∧ ¬W.vert j) := by
            intro hc
            exact hyh hc.1
          have hn2 : ¬ (W.y j = h ∧ x₀ < W.x (j + 1) ∧ ¬W.vert j) := by
            intro hc
            exact hyh hc.1
          rw [if_neg hn1, if_neg hn2]
          ring
      · by_cases hyh : W.y j = h
        · by_cases h1 : x₀ < W.x (j + 1)
          · by_cases h2 : x₀ < W.x j
            · rw [if_pos ⟨hyh, h2, hv⟩, if_pos ⟨hyh, h1, hv⟩]
              decide
            · exfalso
              have hxs : W.x (j + 1) = x₀ ∨ W.x (j + 1) + 1 = x₀ := by omega
              rcases hxs with hxs | hxs
              · have hvj : W.v (j + 1) = (x₀, h) := by
                  ext
                  · exact hxs
                  · exact hy.trans hyh
                exact hd (hvj ▸ W.vertex_mem_boundary (j + 1))
              · have hmid : W.mid j = (x₀, h) := by
                  have hr : W.mid j = ((W.x j + W.x (j + 1)) / 2, (W.y j + W.y (j + 1)) / 2) := rfl
                  rw [hr, hx, hy]
                  ext <;> simp <;> omega
                exact hd (hmid ▸ W.mid_mem_boundary j)
          · by_cases h2 : x₀ < W.x j
            · exfalso
              have hxs : W.x (j + 1) = x₀ ∨ W.x (j + 1) + 1 = x₀ := by omega
              rcases hxs with hxs | hxs
              · have hvj : W.v (j + 1) = (x₀, h) := by
                  ext
                  · exact hxs
                  · exact hy.trans hyh
                exact hd (hvj ▸ W.vertex_mem_boundary (j + 1))
              · have hmid : W.mid j = (x₀, h) := by
                  have hr : W.mid j = ((W.x j + W.x (j + 1)) / 2, (W.y j + W.y (j + 1)) / 2) := rfl
                  rw [hr, hx, hy]
                  ext <;> simp <;> omega
                exact hd (hmid ▸ W.mid_mem_boundary j)
            · have hn1 : ¬ (W.y j = h ∧ x₀ < W.x j ∧ ¬W.vert j) := by
                intro hc
                exact h2 hc.2.1
              have hn2 : ¬ (W.y j = h ∧ x₀ < W.x (j + 1) ∧ ¬W.vert j) := by
                intro hc
                exact h1 hc.2.1
              rw [if_neg hn1, if_neg hn2]
              ring
        · have hn1 : ¬ (W.y j = h ∧ x₀ < W.x j ∧ ¬W.vert j) := by
            intro hc
            exact hyh hc.1
          have hn2 : ¬ (W.y j = h ∧ x₀ < W.x (j + 1) ∧ ¬W.vert j) := by
            intro hc
            exact hyh hc.1
          rw [if_neg hn1, if_neg hn2]
          ring
  rw [Finset.sum_congr rfl (fun j _ => vanish j)]
  simp



/-- `minY` is a lower bound for the lower end of every edge. -/
theorem minY_le_lo (W : OrthoLoop) (i : Fin (W.n + 4)) : W.minY ≤ W.lo i := by
  by_cases hv : W.vert i
  · rcases W.vert_cases i hv with hy | hy
    · have h1 : W.lo i = W.y i := by
        have h2 : W.lo i = min (W.y i) (W.y (i + 1)) := rfl
        rw [h2, hy]
        exact min_eq_left (by omega)
      rw [h1]
      exact W.minY_le_y i
    · have h1 : W.lo i = W.y (i + 1) := by
        have h2 : W.lo i = min (W.y i) (W.y (i + 1)) := rfl
        rw [h2, hy]
        exact min_eq_right (by omega)
      rw [h1]
      exact W.minY_le_y (i + 1)
  · have hy : W.y (i + 1) = W.y i := by
      rcases W.y_succ_cases i with h | h | h
      · exact absurd (W.vert_of_y_ne i (by omega)) hv
      · exact absurd (W.vert_of_y_ne i (by omega)) hv
      · exact h
    have h1 : W.lo i = W.y i := by
      have h2 : W.lo i = min (W.y i) (W.y (i + 1)) := rfl
      rw [h2, hy]
      exact min_eq_left (by omega)
    rw [h1]
    exact W.minY_le_y i

/-- Points on the bottom edge line but off the loop are outside. -/
theorem p2_eq_zero_of_minY_boundary (W : OrthoLoop) (x₀ : ℤ)
    (hd : (x₀, W.minY) ∉ W.boundary) : W.p2 (x₀, W.minY) = 0 := by
  classical
  -- no vertical edge has its upper end at `minY`
  have hB : (∑ i : Fin (W.n + 4), if W.vert i ∧ x₀ < W.x i ∧ W.hi i = W.minY then (1 : ZMod 2) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    by_cases hc : W.vert i ∧ x₀ < W.x i ∧ W.hi i = W.minY
    · obtain ⟨hv, -, hhi⟩ := hc
      exfalso
      have h1 := W.minY_le_lo i
      have h2 := W.hi_eq_lo_add_two i hv
      omega
    · exact if_neg hc
  -- `p2` at height `minY` counts only edges with `lo = minY`
  have hp : W.p2 (x₀, W.minY) =
      (∑ i : Fin (W.n + 4), if W.vert i ∧ x₀ < W.x i ∧ W.lo i = W.minY then (1 : ZMod 2) else 0) := by
    have e1 : W.p2 (x₀, W.minY) = ∑ i : Fin (W.n + 4),
        if W.vert i ∧ x₀ < W.x i ∧ W.lo i ≤ W.minY ∧ W.minY < W.hi i then (1 : ZMod 2) else 0 := rfl
    rw [e1]
    apply Finset.sum_congr rfl
    intro i _
    have hge := W.minY_le_lo i
    by_cases hv : W.vert i
    · have hhi := W.hi_eq_lo_add_two i hv
      by_cases hc : x₀ < W.x i ∧ W.lo i = W.minY
      · have cp : W.vert i ∧ x₀ < W.x i ∧ W.lo i ≤ W.minY ∧ W.minY < W.hi i :=
          ⟨hv, hc.1, by omega, by omega⟩
        have ca : W.vert i ∧ x₀ < W.x i ∧ W.lo i = W.minY := ⟨hv, hc.1, hc.2⟩
        rw [if_pos cp, if_pos ca]
      · have cnp : ¬ (W.vert i ∧ x₀ < W.x i ∧ W.lo i ≤ W.minY ∧ W.minY < W.hi i) := by
          intro h
          exact hc ⟨h.2.1, by omega⟩
        have cna : ¬ (W.vert i ∧ x₀ < W.x i ∧ W.lo i = W.minY) := by
          intro h
          exact hc ⟨h.2.1, h.2.2⟩
        rw [if_neg cnp, if_neg cna]
    · have cnp : ¬ (W.vert i ∧ x₀ < W.x i ∧ W.lo i ≤ W.minY ∧ W.minY < W.hi i) := by
        intro h
        exact hv h.1
      have cna : ¬ (W.vert i ∧ x₀ < W.x i ∧ W.lo i = W.minY) := by
        intro h
        exact hv h.1
      rw [if_neg cnp, if_neg cna]
  have hce := W.corner_count_even x₀ W.minY hd
  rw [hB, add_zero] at hce
  rw [hp]
  exact hce



/-- The crossing parity is invariant under a unit step that does not touch
the loop. -/
theorem p2_eq_of_unit_step (W : OrthoLoop) {c d : Cell}
    (hstep : (d.1 = c.1 + 1 ∧ d.2 = c.2) ∨ (d.1 = c.1 - 1 ∧ d.2 = c.2) ∨
             (d.1 = c.1 ∧ d.2 = c.2 + 1) ∨ (d.1 = c.1 ∧ d.2 = c.2 - 1))
    (hc : c ∉ W.boundary) (hd : d ∉ W.boundary) : W.p2 c = W.p2 d := by
  classical
  rcases hstep with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- rightward horizontal step
    have e : d = (c.1 + 1, c.2) := by ext <;> simp [h1, h2]
    rw [e, p2_succ]
    have hsum : (∑ i : Fin (W.n + 4),
        if W.vert i ∧ W.x i = c.1 + 1 ∧ W.lo i ≤ c.2 ∧ c.2 < W.hi i then (1 : ZMod 2) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      by_cases hc2 : W.vert i ∧ W.x i = c.1 + 1 ∧ W.lo i ≤ c.2 ∧ c.2 < W.hi i
      · obtain ⟨hv, hx, hlo, hhi⟩ := hc2
        exfalso
        have hbd : (c.1 + 1, c.2) ∈ W.boundary := by
          rw [W.mem_boundary (c.1 + 1, c.2)]
          have hhi2 := W.hi_eq_lo_add_two i hv
          have hy : c.2 = W.lo i ∨ c.2 = W.lo i + 1 := by omega
          rcases hy with hy | hy
          · left
            have hlo2 : W.lo i = min (W.y i) (W.y (i + 1)) := rfl
            rcases le_total (W.y i) (W.y (i + 1)) with hle | hle
            · have hm : W.y i = W.lo i := (min_eq_left hle).symm
              refine ⟨i, ?_⟩
              ext
              · show W.x i = c.1 + 1
                exact hx
              · show W.y i = c.2
                omega
            · have hm : W.y (i + 1) = W.lo i := (min_eq_right hle).symm
              have hxi : W.x (i + 1) = W.x i := hv
              refine ⟨i + 1, ?_⟩
              ext
              · show W.x (i + 1) = c.1 + 1
                omega
              · show W.y (i + 1) = c.2
                omega
          · right
            refine ⟨i, ?_⟩
            have h1 : W.mid i = ((W.x i + W.x (i + 1)) / 2, (W.y i + W.y (i + 1)) / 2) := rfl
            rw [h1]
            have hx2 : W.x (i + 1) = W.x i := hv
            have hy2 : W.y i + W.y (i + 1) = W.lo i + W.hi i := by
              have h3 : W.lo i = min (W.y i) (W.y (i + 1)) := rfl
              have h4 : W.hi i = max (W.y i) (W.y (i + 1)) := rfl
              rw [h3, h4, min_add_max]
            ext <;> simp <;> omega
        exact hd (e ▸ hbd)
      · exact if_neg hc2
    rw [hsum, add_zero]
  · -- leftward horizontal step
    have e : d = (c.1 - 1, c.2) := by ext <;> simp [h1, h2]
    rw [e, p2_sub]
    have hsum : (∑ i : Fin (W.n + 4),
        if W.vert i ∧ W.x i = c.1 ∧ W.lo i ≤ c.2 ∧ c.2 < W.hi i then (1 : ZMod 2) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      by_cases hc2 : W.vert i ∧ W.x i = c.1 ∧ W.lo i ≤ c.2 ∧ c.2 < W.hi i
      · obtain ⟨hv, hx, hlo, hhi⟩ := hc2
        exfalso
        have hbd : (c.1, c.2) ∈ W.boundary := by
          rw [W.mem_boundary (c.1, c.2)]
          have hhi2 := W.hi_eq_lo_add_two i hv
          have hy : c.2 = W.lo i ∨ c.2 = W.lo i + 1 := by omega
          rcases hy with hy | hy
          · left
            have hlo2 : W.lo i = min (W.y i) (W.y (i + 1)) := rfl
            rcases le_total (W.y i) (W.y (i + 1)) with hle | hle
            · have hm : W.y i = W.lo i := (min_eq_left hle).symm
              refine ⟨i, ?_⟩
              ext
              · show W.x i = c.1
                exact hx
              · show W.y i = c.2
                omega
            · have hm : W.y (i + 1) = W.lo i := (min_eq_right hle).symm
              have hxi : W.x (i + 1) = W.x i := hv
              refine ⟨i + 1, ?_⟩
              ext
              · show W.x (i + 1) = c.1
                omega
              · show W.y (i + 1) = c.2
                omega
          · right
            refine ⟨i, ?_⟩
            have h1 : W.mid i = ((W.x i + W.x (i + 1)) / 2, (W.y i + W.y (i + 1)) / 2) := rfl
            rw [h1]
            have hx2 : W.x (i + 1) = W.x i := hv
            have hy2 : W.y i + W.y (i + 1) = W.lo i + W.hi i := by
              have h3 : W.lo i = min (W.y i) (W.y (i + 1)) := rfl
              have h4 : W.hi i = max (W.y i) (W.y (i + 1)) := rfl
              rw [h3, h4, min_add_max]
            ext <;> simp <;> omega
        have hbd2 : c ∈ W.boundary := by
          have heta : c = (c.1, c.2) := rfl
          rw [heta]
          exact hbd
        exact hc hbd2
      · exact if_neg hc2
    rw [hsum, add_zero]
  · -- upward vertical step
    have e : d = (c.1, c.2 + 1) := by ext <;> simp [h1, h2]
    subst e
    have hsum : W.p2 (c.1, c.2 + 1) + W.p2 c = 0 := by
      have hid : W.p2 (c.1, c.2 + 1) + W.p2 c =
          (∑ i : Fin (W.n + 4),
            ((if W.vert i ∧ c.1 < W.x i ∧ W.lo i = c.2 + 1 then (1 : ZMod 2) else 0) +
             (if W.vert i ∧ c.1 < W.x i ∧ W.hi i = c.2 + 1 then 1 else 0))) := by
        have e1 : W.p2 (c.1, c.2 + 1) = ∑ i : Fin (W.n + 4),
            if W.vert i ∧ c.1 < W.x i ∧ W.lo i ≤ c.2 + 1 ∧ c.2 + 1 < W.hi i then (1 : ZMod 2) else 0 := rfl
        have e2 : W.p2 c = ∑ i : Fin (W.n + 4),
            if W.vert i ∧ c.1 < W.x i ∧ W.lo i ≤ c.2 ∧ c.2 < W.hi i then (1 : ZMod 2) else 0 := rfl
        rw [e1, e2, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        by_cases hc : W.vert i ∧ c.1 < W.x i
        · obtain ⟨hv, hx⟩ := hc
          have hhi2 := W.hi_eq_lo_add_two i hv
          have hA : (W.vert i ∧ c.1 < W.x i ∧ W.lo i ≤ c.2 + 1 ∧ c.2 + 1 < W.hi i) ↔
              W.lo i ≤ c.2 + 1 ∧ c.2 + 1 < W.hi i :=
            ⟨fun h => ⟨h.2.2.1, h.2.2.2⟩, fun h => ⟨hv, hx, h.1, h.2⟩⟩
          have hB : (W.vert i ∧ c.1 < W.x i ∧ W.lo i ≤ c.2 ∧ c.2 < W.hi i) ↔
              W.lo i ≤ c.2 ∧ c.2 < W.hi i :=
            ⟨fun h => ⟨h.2.2.1, h.2.2.2⟩, fun h => ⟨hv, hx, h.1, h.2⟩⟩
          have hC : (W.vert i ∧ c.1 < W.x i ∧ W.lo i = c.2 + 1) ↔ W.lo i = c.2 + 1 :=
            ⟨fun h => h.2.2, fun h => ⟨hv, hx, h⟩⟩
          have hD : (W.vert i ∧ c.1 < W.x i ∧ W.hi i = c.2 + 1) ↔ W.hi i = c.2 + 1 :=
            ⟨fun h => h.2.2, fun h => ⟨hv, hx, h⟩⟩
          simp only [hA, hB, hC, hD]
          by_cases l1 : W.lo i = c.2 + 1
          · have cA : W.lo i ≤ c.2 + 1 ∧ c.2 + 1 < W.hi i := by omega
            have cB : ¬(W.lo i ≤ c.2 ∧ c.2 < W.hi i) := by omega
            have cC : W.lo i = c.2 + 1 := l1
            have cD : ¬W.hi i = c.2 + 1 := by omega
            rw [if_pos cA, if_neg cB, if_pos cC, if_neg cD]
          · by_cases l2 : W.lo i = c.2
            · have cA : W.lo i ≤ c.2 + 1 ∧ c.2 + 1 < W.hi i := by omega
              have cB : W.lo i ≤ c.2 ∧ c.2 < W.hi i := by omega
              have cC : ¬W.lo i = c.2 + 1 := by omega
              have cD : ¬W.hi i = c.2 + 1 := by omega
              rw [if_pos cA, if_pos cB, if_neg cC, if_neg cD]
              decide
            · by_cases l3 : W.lo i = c.2 - 1
              · have cA : ¬(W.lo i ≤ c.2 + 1 ∧ c.2 + 1 < W.hi i) := by omega
                have cB : W.lo i ≤ c.2 ∧ c.2 < W.hi i := by omega
                have cC : ¬W.lo i = c.2 + 1 := by omega
                have cD : W.hi i = c.2 + 1 := by omega
                rw [if_neg cA, if_pos cB, if_neg cC, if_pos cD]
              · have cA : ¬(W.lo i ≤ c.2 + 1 ∧ c.2 + 1 < W.hi i) := by omega
                have cB : ¬(W.lo i ≤ c.2 ∧ c.2 < W.hi i) := by omega
                have cC : ¬W.lo i = c.2 + 1 := by omega
                have cD : ¬W.hi i = c.2 + 1 := by omega
                rw [if_neg cA, if_neg cB, if_neg cC, if_neg cD]
        · have hA : ¬ (W.vert i ∧ c.1 < W.x i ∧ W.lo i ≤ c.2 + 1 ∧ c.2 + 1 < W.hi i) := by
            intro h
            exact hc ⟨h.1, h.2.1⟩
          have hB : ¬ (W.vert i ∧ c.1 < W.x i ∧ W.lo i ≤ c.2 ∧ c.2 < W.hi i) := by
            intro h
            exact hc ⟨h.1, h.2.1⟩
          have hC : ¬ (W.vert i ∧ c.1 < W.x i ∧ W.lo i = c.2 + 1) := by
            intro h
            exact hc ⟨h.1, h.2.1⟩
          have hD : ¬ (W.vert i ∧ c.1 < W.x i ∧ W.hi i = c.2 + 1) := by
            intro h
            exact hc ⟨h.1, h.2.1⟩
          rw [if_neg hA, if_neg hB, if_neg hC, if_neg hD]
      rw [hid, Finset.sum_add_distrib]
      exact W.corner_count_even c.1 (c.2 + 1) hd
    exact (zmod2_eq_of_add_add_zero hsum).symm
  · -- downward vertical step
    have e : d = (c.1, c.2 - 1) := by ext <;> simp [h1, h2]
    subst e
    have hsum : W.p2 c + W.p2 (c.1, c.2 - 1) = 0 := by
      have hid : W.p2 c + W.p2 (c.1, c.2 - 1) =
          (∑ i : Fin (W.n + 4),
            ((if W.vert i ∧ c.1 < W.x i ∧ W.lo i = c.2 then (1 : ZMod 2) else 0) +
             (if W.vert i ∧ c.1 < W.x i ∧ W.hi i = c.2 then 1 else 0))) := by
        have e1 : W.p2 c = ∑ i : Fin (W.n + 4),
            if W.vert i ∧ c.1 < W.x i ∧ W.lo i ≤ c.2 ∧ c.2 < W.hi i then (1 : ZMod 2) else 0 := rfl
        have e2 : W.p2 (c.1, c.2 - 1) = ∑ i : Fin (W.n + 4),
            if W.vert i ∧ c.1 < W.x i ∧ W.lo i ≤ c.2 - 1 ∧ c.2 - 1 < W.hi i then (1 : ZMod 2) else 0 := rfl
        rw [e1, e2, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        by_cases hc : W.vert i ∧ c.1 < W.x i
        · obtain ⟨hv, hx⟩ := hc
          have hhi2 := W.hi_eq_lo_add_two i hv
          have hA : (W.vert i ∧ c.1 < W.x i ∧ W.lo i ≤ c.2 ∧ c.2 < W.hi i) ↔
              W.lo i ≤ c.2 ∧ c.2 < W.hi i :=
            ⟨fun h => ⟨h.2.2.1, h.2.2.2⟩, fun h => ⟨hv, hx, h.1, h.2⟩⟩
          have hB : (W.vert i ∧ c.1 < W.x i ∧ W.lo i ≤ c.2 - 1 ∧ c.2 - 1 < W.hi i) ↔
              W.lo i ≤ c.2 - 1 ∧ c.2 - 1 < W.hi i :=
            ⟨fun h => ⟨h.2.2.1, h.2.2.2⟩, fun h => ⟨hv, hx, h.1, h.2⟩⟩
          have hC : (W.vert i ∧ c.1 < W.x i ∧ W.lo i = c.2) ↔ W.lo i = c.2 :=
            ⟨fun h => h.2.2, fun h => ⟨hv, hx, h⟩⟩
          have hD : (W.vert i ∧ c.1 < W.x i ∧ W.hi i = c.2) ↔ W.hi i = c.2 :=
            ⟨fun h => h.2.2, fun h => ⟨hv, hx, h⟩⟩
          simp only [hA, hB, hC, hD]
          by_cases l1 : W.lo i = c.2
          · have cA : W.lo i ≤ c.2 ∧ c.2 < W.hi i := by omega
            have cB : ¬(W.lo i ≤ c.2 - 1 ∧ c.2 - 1 < W.hi i) := by omega
            have cC : W.lo i = c.2 := l1
            have cD : ¬W.hi i = c.2 := by omega
            rw [if_pos cA, if_neg cB, if_pos cC, if_neg cD]
          · by_cases l2 : W.lo i = c.2 - 1
            · have cA : W.lo i ≤ c.2 ∧ c.2 < W.hi i := by omega
              have cB : W.lo i ≤ c.2 - 1 ∧ c.2 - 1 < W.hi i := by omega
              have cC : ¬W.lo i = c.2 := by omega
              have cD : ¬W.hi i = c.2 := by omega
              rw [if_pos cA, if_pos cB, if_neg cC, if_neg cD]
              decide
            · by_cases l3 : W.lo i = c.2 - 2
              · have cA : ¬(W.lo i ≤ c.2 ∧ c.2 < W.hi i) := by omega
                have cB : W.lo i ≤ c.2 - 1 ∧ c.2 - 1 < W.hi i := by omega
                have cC : ¬W.lo i = c.2 := by omega
                have cD : W.hi i = c.2 := by omega
                rw [if_neg cA, if_pos cB, if_neg cC, if_pos cD]
              · have cA : ¬(W.lo i ≤ c.2 ∧ c.2 < W.hi i) := by omega
                have cB : ¬(W.lo i ≤ c.2 - 1 ∧ c.2 - 1 < W.hi i) := by omega
                have cC : ¬W.lo i = c.2 := by omega
                have cD : ¬W.hi i = c.2 := by omega
                rw [if_neg cA, if_neg cB, if_neg cC, if_neg cD]
        · have hA : ¬ (W.vert i ∧ c.1 < W.x i ∧ W.lo i ≤ c.2 ∧ c.2 < W.hi i) := by
            intro h
            exact hc ⟨h.1, h.2.1⟩
          have hB : ¬ (W.vert i ∧ c.1 < W.x i ∧ W.lo i ≤ c.2 - 1 ∧ c.2 - 1 < W.hi i) := by
            intro h
            exact hc ⟨h.1, h.2.1⟩
          have hC : ¬ (W.vert i ∧ c.1 < W.x i ∧ W.lo i = c.2) := by
            intro h
            exact hc ⟨h.1, h.2.1⟩
          have hD : ¬ (W.vert i ∧ c.1 < W.x i ∧ W.hi i = c.2) := by
            intro h
            exact hc ⟨h.1, h.2.1⟩
          rw [if_neg hA, if_neg hB, if_neg hC, if_neg hD]
      rw [hid, Finset.sum_add_distrib]
      exact W.corner_count_even c.1 c.2 hc
    exact zmod2_eq_of_add_add_zero hsum

/-- The crossing parity is invariant under a length-2 step whose midpoint and
endpoints avoid the loop. -/
theorem p2_eq_of_two_step (W : OrthoLoop) {c m d : Cell}
    (h1 : (m.1 = c.1 + 1 ∧ m.2 = c.2) ∨ (m.1 = c.1 - 1 ∧ m.2 = c.2) ∨
          (m.1 = c.1 ∧ m.2 = c.2 + 1) ∨ (m.1 = c.1 ∧ m.2 = c.2 - 1))
    (h2 : (d.1 = m.1 + 1 ∧ d.2 = m.2) ∨ (d.1 = m.1 - 1 ∧ d.2 = m.2) ∨
          (d.1 = m.1 ∧ d.2 = m.2 + 1) ∨ (d.1 = m.1 ∧ d.2 = m.2 - 1))
    (hc : c ∉ W.boundary) (hm : m ∉ W.boundary) (hd : d ∉ W.boundary) :
    W.p2 c = W.p2 d :=
  (W.p2_eq_of_unit_step h1 hc hm).trans (W.p2_eq_of_unit_step h2 hm hd)



/-- A point lying in the y-band of a vertical edge is on the loop. -/
theorem mem_boundary_of_mem_vert_band (W : OrthoLoop) (i : Fin (W.n + 4)) {q : Cell}
    (hv : W.vert i) (hx : q.1 = W.x i) (hlo : W.lo i ≤ q.2) (hhi : q.2 < W.hi i) :
    q ∈ W.boundary := by
  rw [W.mem_boundary q]
  have hhi2 := W.hi_eq_lo_add_two i hv
  have hy : q.2 = W.lo i ∨ q.2 = W.lo i + 1 := by omega
  rcases hy with hy | hy
  · left
    have hlo2 : W.lo i = min (W.y i) (W.y (i + 1)) := rfl
    rcases le_total (W.y i) (W.y (i + 1)) with hle | hle
    · have hm : W.y i = W.lo i := (min_eq_left hle).symm
      refine ⟨i, ?_⟩
      ext
      · show W.x i = q.1
        exact hx.symm
      · show W.y i = q.2
        omega
    · have hm : W.y (i + 1) = W.lo i := (min_eq_right hle).symm
      have hxi : W.x (i + 1) = W.x i := hv
      refine ⟨i + 1, ?_⟩
      ext
      · show W.x (i + 1) = q.1
        omega
      · show W.y (i + 1) = q.2
        omega
  · right
    refine ⟨i, ?_⟩
    have h1 : W.mid i = ((W.x i + W.x (i + 1)) / 2, (W.y i + W.y (i + 1)) / 2) := rfl
    rw [h1]
    have hx2 : W.x (i + 1) = W.x i := hv
    have hy2 : W.y i + W.y (i + 1) = W.lo i + W.hi i := by
      have h3 : W.lo i = min (W.y i) (W.y (i + 1)) := rfl
      have h4 : W.hi i = max (W.y i) (W.y (i + 1)) := rfl
      rw [h3, h4, min_add_max]
    ext <;> simp <;> omega

/-- Points on the left edge line but off the loop are outside. -/
theorem p2_eq_zero_of_minX_boundary (W : OrthoLoop) (y : ℤ)
    (hd : (W.minX, y) ∉ W.boundary) : W.p2 (W.minX, y) = 0 := by
  classical
  have h1 : W.minX = W.minX - 1 + 1 := by omega
  rw [h1, p2_succ]
  have hsum : (∑ i : Fin (W.n + 4),
      if W.vert i ∧ W.x i = W.minX - 1 + 1 ∧ W.lo i ≤ y ∧ y < W.hi i then (1 : ZMod 2) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    by_cases hc : W.vert i ∧ W.x i = W.minX - 1 + 1 ∧ W.lo i ≤ y ∧ y < W.hi i
    · obtain ⟨hv, hx, hlo, hhi⟩ := hc
      exfalso
      have h2 : (W.minX, y) = ((W.minX - 1 + 1), y) := by
        ext <;> simp <;> omega
      exact hd (h2 ▸ W.mem_boundary_of_mem_vert_band i hv (by omega) hlo hhi)
    · exact if_neg hc
  rw [hsum, add_zero]
  exact W.p2_eq_zero_of_le_minX (by omega)



set_option maxHeartbeats 3200000 in
/-- Case (C2): pinch, split along the chord `r–r′`. -/
theorem pinch_case (W : OrthoLoop) (x₀ ym : ℤ)
    (h0 : W.v 0 = (x₀, ym)) (hmax : ∀ i, (W.v i).2 ≤ ym)
    (hmin : ∀ i, (W.v i).2 = ym → x₀ ≤ (W.v i).1)
    (h1 : W.v 1 = (x₀ + 2, ym)) (h2 : W.v 2 = (x₀ + 4, ym))
    (hn1 : W.v (-1) = (x₀, ym - 2))
    (k : Fin (W.n + 4)) (hk : W.v k = (x₀ + 2, ym - 2))
    (hk4 : 4 ≤ (k : ℕ)) (hkn : (k : ℕ) ≤ W.n + 2) :
    ∃ W₁ W₂ : OrthoLoop, W.I = W₁.I + W₂.I + 1 ∧ W.T = W₁.T + W₂.T ∧ W.L = W₁.L + W₂.L - 2 := by
  classical
  have h0x : (W.v 0).1 = x₀ := congrArg Prod.fst h0
  have h0y : (W.v 0).2 = ym := congrArg Prod.snd h0
  have h1x : (W.v 1).1 = x₀ + 2 := congrArg Prod.fst h1
  have h1y : (W.v 1).2 = ym := congrArg Prod.snd h1
  have h2x : (W.v 2).1 = x₀ + 4 := congrArg Prod.fst h2
  have h2y : (W.v 2).2 = ym := congrArg Prod.snd h2
  have hkx : (W.v k).1 = x₀ + 2 := congrArg Prod.fst hk
  have hky : (W.v k).2 = ym - 2 := congrArg Prod.snd hk
  have hpa : (x₀ : ZMod 2) = W.a := by rw [← h0x]; exact W.parX 0
  have hpb : (ym : ZMod 2) = W.b := by rw [← h0y]; exact W.parY 0
  have hkey : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  have hparx1 : ((x₀ + 1 : ℤ) : ZMod 2) ≠ W.a := by
    rw [← hpa]
    push_cast
    rcases hkey (x₀ : ZMod 2) with h | h <;> rw [h] <;> decide
  have hparx3 : ((x₀ + 3 : ℤ) : ZMod 2) ≠ W.a := by
    rw [← hpa]
    push_cast
    rcases hkey (x₀ : ZMod 2) with h | h <;> rw [h] <;> decide
  have hpary1 : ((ym - 1 : ℤ) : ZMod 2) ≠ W.b := by
    rw [← hpb]
    push_cast
    rcases hkey (ym : ZMod 2) with h | h <;> rw [h] <;> decide
  have hpary3 : ((ym - 3 : ℤ) : ZMod 2) ≠ W.b := by
    rw [← hpb]
    push_cast
    rcases hkey (ym : ZMod 2) with h | h <;> rw [h] <;> decide
  have hn1' : W.v ⟨W.n + 3, by omega⟩ = (x₀, ym - 2) := by
    have e : (⟨W.n + 3, by omega⟩ : Fin (W.n + 4)) = (-1 : Fin (W.n + 4)) := by
      apply Fin.ext
      simp [val_neg_one_fin]
    rw [e]
    exact hn1
  -- uniqueness of the special vertices
  have hj0 : ∀ j : Fin (W.n + 4), W.v j = (x₀, ym) → j = 0 :=
    fun j hj => W.inj (hj.trans h0.symm)
  have hj1 : ∀ j : Fin (W.n + 4), W.v j = (x₀ + 2, ym) → j = 1 :=
    fun j hj => W.inj (hj.trans h1.symm)
  have hjr : ∀ j : Fin (W.n + 4), W.v j = (x₀ + 2, ym - 2) → j = k :=
    fun j hj => W.inj (hj.trans hk.symm)
  have hjd : ∀ j : Fin (W.n + 4), W.v j = (x₀, ym - 2) → j = ⟨W.n + 3, by omega⟩ :=
    fun j hj => W.inj (hj.trans hn1'.symm)
  -- the chord segment as a literal three-point set
  have hchord : ({(x₀ + 2, ym - 2), midPt (x₀ + 2, ym - 2) (x₀ + 2, ym),
      (x₀ + 2, ym)} : Finset Cell) =
      {(x₀ + 2, ym - 2), (x₀ + 2, ym - 1), (x₀ + 2, ym)} := by
    have hm : midPt (x₀ + 2, ym - 2) (x₀ + 2, ym) = (x₀ + 2, ym - 1) := by
      simp only [midPt, Prod.mk.injEq]
      constructor <;> omega
    rw [hm]
  have hchord_rev : ({(x₀ + 2, ym), midPt (x₀ + 2, ym) (x₀ + 2, ym - 2),
      (x₀ + 2, ym - 2)} : Finset Cell) =
      {(x₀ + 2, ym - 2), (x₀ + 2, ym - 1), (x₀ + 2, ym)} := by
    have hm : midPt (x₀ + 2, ym) (x₀ + 2, ym - 2) = (x₀ + 2, ym - 1) := by
      simp only [midPt, Prod.mk.injEq]
      constructor <;> omega
    rw [hm]
    ext c
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  -- the chord is disjoint from every W-edge with index ∉ {0, 1, k-1, k}
  have hchord_disj : ∀ (m : Fin (W.n + 4)), m ≠ 0 → m ≠ 1 → m ≠ k - 1 → m ≠ k →
      Disjoint ({(x₀ + 2, ym - 2), (x₀ + 2, ym - 1), (x₀ + 2, ym)} : Finset Cell)
        (W.edgePts m) := by
    intro m hm0 hm1 hmk1 hmk
    rw [Finset.disjoint_left]
    intro c hc hc'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl | rfl
    · -- c = r′ = (x₀+2, ym-2)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc'
      rcases hc' with h | h | h
      · exact hmk (hjr _ h.symm)
      · rcases W.mid_cases m _ h.symm with ⟨hx, g1, g2 | g2⟩ | ⟨hy, g1, g2 | g2⟩
        · have hyk : (W.v m).2 = ym - 3 := by
            have hc2 : ((x₀ + 2, ym - 2) : Cell).2 = ym - 2 := rfl
            omega
          exact hpary3 (hyk ▸ W.parY m)
        · have hyk : (W.v m).2 = ym - 1 := by
            have hc2 : ((x₀ + 2, ym - 2) : Cell).2 = ym - 2 := rfl
            omega
          exact hpary1 (hyk ▸ W.parY m)
        · have hxk : (W.v m).1 = x₀ + 1 := by
            have hc1 : ((x₀ + 2, ym - 2) : Cell).1 = x₀ + 2 := rfl
            omega
          exact hparx1 (hxk ▸ W.parX m)
        · have hxk : (W.v m).1 = x₀ + 3 := by
            have hc1 : ((x₀ + 2, ym - 2) : Cell).1 = x₀ + 2 := rfl
            omega
          exact hparx3 (hxk ▸ W.parX m)
      · apply hmk1
        have h2 := hjr _ h.symm
        rw [← h2]
        abel
    · -- c = m₀ = (x₀+2, ym-1)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc'
      rcases hc' with h | h | h
      · have hyk : (W.v m).2 = ym - 1 := (congrArg Prod.snd h).symm
        exact hpary1 (hyk ▸ W.parY m)
      · rcases W.mid_cases m _ h.symm with ⟨hx, g1, g2 | g2⟩ | ⟨hy, g1, g2 | g2⟩
        · have hvm : W.v m = (x₀ + 2, ym - 2) := by
            have hc2 : ((x₀ + 2, ym - 1) : Cell).2 = ym - 1 := rfl
            have hy2 : (W.v m).2 = ym - 2 := by omega
            exact Prod.ext g1.symm hy2
          exact hmk (hjr _ hvm)
        · have hvm : W.v m = (x₀ + 2, ym) := by
            have hc2 : ((x₀ + 2, ym - 1) : Cell).2 = ym - 1 := rfl
            have hy2 : (W.v m).2 = ym := by omega
            exact Prod.ext g1.symm hy2
          exact hm1 (hj1 _ hvm)
        · have hyk : (W.v m).2 = ym - 1 := by
            have hc2 : ((x₀ + 2, ym - 1) : Cell).2 = ym - 1 := rfl
            omega
          exact hpary1 (hyk ▸ W.parY m)
        · have hyk : (W.v m).2 = ym - 1 := by
            have hc2 : ((x₀ + 2, ym - 1) : Cell).2 = ym - 1 := rfl
            omega
          exact hpary1 (hyk ▸ W.parY m)
      · have hyk : (W.v (m + 1)).2 = ym - 1 := (congrArg Prod.snd h).symm
        exact hpary1 (hyk ▸ W.parY (m + 1))
    · -- c = r = (x₀+2, ym)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc'
      rcases hc' with h | h | h
      · exact hm1 (hj1 _ h.symm)
      · rcases W.mid_cases m _ h.symm with ⟨hx, g1, g2 | g2⟩ | ⟨hy, g1, g2 | g2⟩
        · have hyk : (W.v m).2 = ym - 1 := by
            have hc2 : ((x₀ + 2, ym) : Cell).2 = ym := rfl
            omega
          exact hpary1 (hyk ▸ W.parY m)
        · have hyk : (W.v m).2 = ym + 1 := by
            have hc2 : ((x₀ + 2, ym) : Cell).2 = ym := rfl
            omega
          have hle := hmax m
          omega
        · have hxk : (W.v m).1 = x₀ + 1 := by
            have hc1 : ((x₀ + 2, ym) : Cell).1 = x₀ + 2 := rfl
            omega
          exact hparx1 (hxk ▸ W.parX m)
        · have hxk : (W.v m).1 = x₀ + 3 := by
            have hc1 : ((x₀ + 2, ym) : Cell).1 = x₀ + 2 := rfl
            omega
          exact hparx3 (hxk ▸ W.parX m)
      · apply hm0
        have h2 := hj1 _ h.symm
        have h3 : m + 1 = (0 : Fin (W.n + 4)) + 1 := by rw [h2]; abel
        exact add_right_cancel_iff.mp h3
  -- successor vertex of an interior `W₁`-edge, in W-terms
  have hsucc1W : ∀ (t : Fin ((k : ℕ) - 4 + 4)), t ≠ Fin.last ((k : ℕ) - 4 + 3) →
      W.v ⟨(t + 1 : Fin ((k : ℕ) - 4 + 4)).val + 1,
        by have h := (t + 1 : Fin ((k : ℕ) - 4 + 4)).is_lt; omega⟩ =
      W.v ((⟨t.val + 1, by omega⟩ : Fin (W.n + 4)) + 1) := by
    intro t ht
    have htv : t.val + 1 < (k : ℕ) := by
      have hlt := t.is_lt
      have hnv : t.val ≠ (k : ℕ) - 4 + 3 := fun h => ht (Fin.ext h)
      omega
    apply congrArg W.v
    apply Fin.ext
    show (t + 1 : Fin ((k : ℕ) - 4 + 4)).val + 1 =
      ((⟨t.val + 1, by omega⟩ : Fin (W.n + 4)) + 1 : Fin (W.n + 4)).val
    have h3 : (t + 1 : Fin ((k : ℕ) - 4 + 4)).val = t.val + 1 := by
      rw [Fin.val_add, Fin.val_one']
      have h1m' : 1 % ((k : ℕ) - 4 + 4) = 1 := Nat.mod_eq_of_lt (by omega)
      have h2m' : (t.val + 1) % ((k : ℕ) - 4 + 4) = t.val + 1 := Nat.mod_eq_of_lt (by omega)
      rw [h1m', h2m']
    rw [h3, Fin.val_add, Fin.val_one']
    have hv1 : ((⟨t.val + 1, by omega⟩ : Fin (W.n + 4)) : ℕ) = t.val + 1 := rfl
    rw [hv1]
    have h1m : 1 % (W.n + 4) = 1 := Nat.mod_eq_of_lt (by omega)
    have h2m : (t.val + 1 + 1) % (W.n + 4) = t.val + 2 := Nat.mod_eq_of_lt (by omega)
    rw [h1m, h2m]
  -- segment of the `t`-th edge of `W₁` (interior `t`), in W-terms
  have hseg1W : ∀ (t : Fin ((k : ℕ) - 4 + 4)), t ≠ Fin.last ((k : ℕ) - 4 + 3) →
      ({W.v ⟨t.val + 1, by omega⟩, midPt (W.v ⟨t.val + 1, by omega⟩)
        (W.v ⟨(t + 1 : Fin ((k : ℕ) - 4 + 4)).val + 1, by have h := (t + 1 : Fin ((k : ℕ) - 4 + 4)).is_lt; omega⟩),
        W.v ⟨(t + 1 : Fin ((k : ℕ) - 4 + 4)).val + 1, by have h := (t + 1 : Fin ((k : ℕ) - 4 + 4)).is_lt; omega⟩} : Finset Cell) =
      W.edgePts ⟨t.val + 1, by omega⟩ := by
    intro t ht
    rw [hsucc1W t ht]
  -- the wrap edge of `W₁` is the chord segment
  have hchord1W : ({W.v ⟨(Fin.last ((k : ℕ) - 4 + 3)).val + 1, by omega⟩,
      midPt (W.v ⟨(Fin.last ((k : ℕ) - 4 + 3)).val + 1, by omega⟩)
        (W.v ⟨(Fin.last ((k : ℕ) - 4 + 3) + 1 : Fin ((k : ℕ) - 4 + 4)).val + 1,
          by have h := (Fin.last ((k : ℕ) - 4 + 3) + 1 : Fin ((k : ℕ) - 4 + 4)).is_lt; omega⟩),
      W.v ⟨(Fin.last ((k : ℕ) - 4 + 3) + 1 : Fin ((k : ℕ) - 4 + 4)).val + 1,
        by have h := (Fin.last ((k : ℕ) - 4 + 3) + 1 : Fin ((k : ℕ) - 4 + 4)).is_lt; omega⟩} : Finset Cell) =
      {(x₀ + 2, ym - 2), (x₀ + 2, ym - 1), (x₀ + 2, ym)} := by
    have e0 : (Fin.last ((k : ℕ) - 4 + 3) + 1 : Fin ((k : ℕ) - 4 + 4)) = 0 := Fin.ext val_last_succ
    have hlast : (⟨(Fin.last ((k : ℕ) - 4 + 3)).val + 1, by omega⟩ : Fin (W.n + 4)) = k := by
      apply Fin.ext
      show ((Fin.last ((k : ℕ) - 4 + 3)).val + 1 : ℕ) = (k : ℕ)
      rw [Fin.val_last]
      omega
    have p1 : W.v ⟨(Fin.last ((k : ℕ) - 4 + 3)).val + 1, by omega⟩ = (x₀ + 2, ym - 2) := by
      rw [hlast, hk]
    have p2 : W.v ⟨(Fin.last ((k : ℕ) - 4 + 3) + 1 : Fin ((k : ℕ) - 4 + 4)).val + 1, by omega⟩ =
        (x₀ + 2, ym) := by
      have e2 : (⟨(Fin.last ((k : ℕ) - 4 + 3) + 1 : Fin ((k : ℕ) - 4 + 4)).val + 1, by omega⟩ :
          Fin (W.n + 4)) = 1 := by
        apply Fin.ext
        show (Fin.last ((k : ℕ) - 4 + 3) + 1 : Fin ((k : ℕ) - 4 + 4)).val + 1 = ((1 : Fin (W.n + 4)) : ℕ)
        rw [val_last_succ, val_one_fin]
      rw [e2, h1]
    rw [p1, p2]
    exact hchord
  -- the right sub-loop `W₁`: vertices `v 1, …, v k`
  let W₁ : OrthoLoop := {
    a := W.a
    b := W.b
    n := (k : ℕ) - 4
    v := fun j => W.v ⟨j.val + 1, by omega⟩
    inj := by
      intro i j h
      have h2 := W.inj h
      have h3 := congrArg Fin.val h2
      have h4 : ((⟨j.val + 1, by omega⟩ : Fin (W.n + 4)) : ℕ) = j.val + 1 := rfl
      have h5 : ((⟨i.val + 1, by omega⟩ : Fin (W.n + 4)) : ℕ) = i.val + 1 := rfl
      rw [h4, h5] at h3
      exact Fin.ext (by omega)
    step := by
      intro i
      by_cases hi : i = Fin.last ((k : ℕ) - 4 + 3)
      · -- the chord edge, from `v k` back up to `v 1`
        rw [hi]
        have e0 : (Fin.last ((k : ℕ) - 4 + 3) + 1 : Fin ((k : ℕ) - 4 + 4)) =
            (0 : Fin ((k : ℕ) - 4 + 4)) := Fin.ext val_last_succ
        rw [e0]
        have hlast : (⟨(Fin.last ((k : ℕ) - 4 + 3)).val + 1, by omega⟩ : Fin (W.n + 4)) = k := by
          apply Fin.ext
          show ((Fin.last ((k : ℕ) - 4 + 3)).val + 1 : ℕ) = (k : ℕ)
          rw [Fin.val_last]
          omega
        have hv0 : (⟨(0 : Fin ((k : ℕ) - 4 + 4)).val + 1, by omega⟩ : Fin (W.n + 4)) = 1 := by
          apply Fin.ext
          show ((0 : Fin ((k : ℕ) - 4 + 4)).val + 1 : ℕ) = ((1 : Fin (W.n + 4)) : ℕ)
          rw [val_zero_fin, val_one_fin]
        have hs : W.v ⟨(Fin.last ((k : ℕ) - 4 + 3)).val + 1, by omega⟩ = W.v k := by
          rw [hlast]
        have hs0 : W.v ⟨(0 : Fin ((k : ℕ) - 4 + 4)).val + 1, by omega⟩ = W.v 1 := by
          rw [hv0]
        rw [hs, hs0, hk, h1]
        exact Or.inl ⟨by simp, by show (ym : ℤ) = ym - 2 + 2; omega⟩
      · -- an original edge of `W`
        have hiv : (i : ℕ) ≠ (k : ℕ) - 4 + 3 := by
          intro h
          exact hi (Fin.ext h)
        have e : (i + 1 : Fin ((k : ℕ) - 4 + 4)) = ⟨i.val + 1, by omega⟩ := by
          apply Fin.ext
          rw [Fin.val_add, Fin.val_one']
          have hv1 : ((⟨i.val + 1, by omega⟩ : Fin ((k : ℕ) - 4 + 4)) : ℕ) = i.val + 1 := rfl
          rw [hv1]
          have h1m : 1 % ((k : ℕ) - 4 + 4) = 1 := Nat.mod_eq_of_lt (by omega)
          have h2m : (i.val + 1) % ((k : ℕ) - 4 + 4) = i.val + 1 :=
            Nat.mod_eq_of_lt (by have := i.is_lt; omega)
          rw [h1m, h2m]
        rw [e]
        have hstep0 := W.step ⟨i.val + 1, by omega⟩
        have hidx : (⟨i.val + 1, by omega⟩ : Fin (W.n + 4)) + 1 = ⟨i.val + 2, by omega⟩ := by
          apply Fin.ext
          rw [Fin.val_add, Fin.val_one']
          have hv1 : ((⟨i.val + 1, by omega⟩ : Fin (W.n + 4)) : ℕ) = i.val + 1 := rfl
          have hv2 : ((⟨i.val + 2, by omega⟩ : Fin (W.n + 4)) : ℕ) = i.val + 2 := rfl
          rw [hv1, hv2]
          have h1m : 1 % (W.n + 4) = 1 := Nat.mod_eq_of_lt (by omega)
          have h2m : (i.val + 1 + 1) % (W.n + 4) = i.val + 2 :=
            Nat.mod_eq_of_lt (by have := i.is_lt; omega)
          rw [h1m, h2m]
        rw [hidx] at hstep0
        exact hstep0
    par := fun j => W.par ⟨j.val + 1, by omega⟩
    simple := by
      intro i j hij hi1j hij1
      rw [Finset.disjoint_left]
      intro c hci hcj
      beta_reduce at hci hcj
      by_cases hi : i = Fin.last ((k : ℕ) - 4 + 3)
      · by_cases hj : j = Fin.last ((k : ℕ) - 4 + 3)
        · exact absurd (hi.trans hj.symm) hij
        · -- i chord, j interior
          rw [hi, hchord1W] at hci
          rw [hseg1W j hj] at hcj
          have hj0 : j ≠ 0 := by
            intro h
            apply hi1j
            rw [hi, h]
            exact Fin.ext val_last_succ
          have hjk2 : (j : ℕ) ≠ (k : ℕ) - 2 := by
            intro h
            apply hij1
            rw [hi]
            apply Fin.ext
            show ((Fin.last ((k : ℕ) - 4 + 3)) : ℕ) = ((j + 1 : Fin ((k : ℕ) - 4 + 4)) : ℕ)
            rw [Fin.val_last, Fin.val_add, Fin.val_one']
            have h1m : 1 % ((k : ℕ) - 4 + 4) = 1 := Nat.mod_eq_of_lt (by omega)
            have h2m : (j.val + 1) % ((k : ℕ) - 4 + 4) = j.val + 1 :=
              Nat.mod_eq_of_lt (by have := j.is_lt; omega)
            rw [h1m, h2m]
            omega
          have hd := hchord_disj ⟨j.val + 1, by omega⟩ (by
            intro h
            have hv := congrArg Fin.val h
            have hv1 : ((⟨j.val + 1, by omega⟩ : Fin (W.n + 4)) : ℕ) = j.val + 1 := rfl
            rw [hv1, val_zero_fin] at hv
            omega) (by
            intro h
            have hv := congrArg Fin.val h
            have hv1 : ((⟨j.val + 1, by omega⟩ : Fin (W.n + 4)) : ℕ) = j.val + 1 := rfl
            rw [hv1, val_one_fin] at hv
            have hz : j.val = 0 := by omega
            exact hj0 (Fin.ext hz)) (by
            intro h
            have hv := congrArg Fin.val h
            have hv1 : ((⟨j.val + 1, by omega⟩ : Fin (W.n + 4)) : ℕ) = j.val + 1 := rfl
            rw [hv1] at hv
            have hv2 : ((k - 1 : Fin (W.n + 4)) : ℕ) = (k : ℕ) - 1 := by
              have h1k : (1 : Fin (W.n + 4)) ≤ k := by
                rw [Fin.le_def]
                have h1m : ((1 : Fin (W.n + 4)) : ℕ) = 1 := by
                  rw [Fin.val_one']
                  exact Nat.mod_eq_of_lt (by omega)
                rw [h1m]
                omega
              rw [Fin.sub_val_of_le h1k]
              have h1m : ((1 : Fin (W.n + 4)) : ℕ) = 1 := by
                rw [Fin.val_one']
                exact Nat.mod_eq_of_lt (by omega)
              rw [h1m]
            rw [hv2] at hv
            exact hjk2 (by omega)) (by
            intro h
            have hv := congrArg Fin.val h
            have hv1 : ((⟨j.val + 1, by omega⟩ : Fin (W.n + 4)) : ℕ) = j.val + 1 := rfl
            rw [hv1] at hv
            have hjv : (j : ℕ) ≠ (k : ℕ) - 4 + 3 := fun h => hj (Fin.ext h)
            have hjl := j.is_lt
            omega)
          rw [Finset.disjoint_left] at hd
          exact hd hci hcj
      · by_cases hj : j = Fin.last ((k : ℕ) - 4 + 3)
        · -- j chord, i interior: symmetric
          rw [hj, hchord1W] at hcj
          rw [hseg1W i hi] at hci
          have hi0 : i ≠ 0 := by
            intro h
            apply hij1
            rw [hj, h]
            exact (Fin.ext val_last_succ).symm
          have hik2 : (i : ℕ) ≠ (k : ℕ) - 2 := by
            intro h
            apply hi1j
            rw [hj]
            apply Fin.ext
            show ((i + 1 : Fin ((k : ℕ) - 4 + 4)) : ℕ) = ((Fin.last ((k : ℕ) - 4 + 3)) : ℕ)
            rw [Fin.val_last, Fin.val_add, Fin.val_one']
            have h1m : 1 % ((k : ℕ) - 4 + 4) = 1 := Nat.mod_eq_of_lt (by omega)
            have h2m : (i.val + 1) % ((k : ℕ) - 4 + 4) = i.val + 1 :=
              Nat.mod_eq_of_lt (by have := i.is_lt; omega)
            rw [h1m, h2m]
            omega
          have hd := hchord_disj ⟨i.val + 1, by omega⟩ (by
            intro h
            have hv := congrArg Fin.val h
            have hv1 : ((⟨i.val + 1, by omega⟩ : Fin (W.n + 4)) : ℕ) = i.val + 1 := rfl
            rw [hv1, val_zero_fin] at hv
            omega) (by
            intro h
            have hv := congrArg Fin.val h
            have hv1 : ((⟨i.val + 1, by omega⟩ : Fin (W.n + 4)) : ℕ) = i.val + 1 := rfl
            rw [hv1, val_one_fin] at hv
            have hz : i.val = 0 := by omega
            exact hi0 (Fin.ext hz)) (by
            intro h
            have hv := congrArg Fin.val h
            have hv1 : ((⟨i.val + 1, by omega⟩ : Fin (W.n + 4)) : ℕ) = i.val + 1 := rfl
            rw [hv1] at hv
            have hv2 : ((k - 1 : Fin (W.n + 4)) : ℕ) = (k : ℕ) - 1 := by
              have h1k : (1 : Fin (W.n + 4)) ≤ k := by
                rw [Fin.le_def]
                have h1m : ((1 : Fin (W.n + 4)) : ℕ) = 1 := by
                  rw [Fin.val_one']
                  exact Nat.mod_eq_of_lt (by omega)
                rw [h1m]
                omega
              rw [Fin.sub_val_of_le h1k]
              have h1m : ((1 : Fin (W.n + 4)) : ℕ) = 1 := by
                rw [Fin.val_one']
                exact Nat.mod_eq_of_lt (by omega)
              rw [h1m]
            rw [hv2] at hv
            exact hik2 (by omega)) (by
            intro h
            have hv := congrArg Fin.val h
            have hv1 : ((⟨i.val + 1, by omega⟩ : Fin (W.n + 4)) : ℕ) = i.val + 1 := rfl
            rw [hv1] at hv
            have hiv : (i : ℕ) ≠ (k : ℕ) - 4 + 3 := fun h => hi (Fin.ext h)
            have hil := i.is_lt
            omega)
          rw [Finset.disjoint_left] at hd
          exact hd hcj hci
        · -- both interior: W.simple applies
          rw [hseg1W i hi] at hci
          rw [hseg1W j hj] at hcj
          have g1 : (⟨i.val + 1, by omega⟩ : Fin (W.n + 4)) ≠ ⟨j.val + 1, by omega⟩ := by
            intro h
            have hv := congrArg Fin.val h
            have hv1 : ((⟨i.val + 1, by omega⟩ : Fin (W.n + 4)) : ℕ) = i.val + 1 := rfl
            have hv2 : ((⟨j.val + 1, by omega⟩ : Fin (W.n + 4)) : ℕ) = j.val + 1 := rfl
            rw [hv1, hv2] at hv
            exact hij (Fin.ext (by omega))
          have g2 : (⟨i.val + 1, by omega⟩ : Fin (W.n + 4)) + 1 ≠ ⟨j.val + 1, by omega⟩ := by
            intro h
            have hv := congrArg Fin.val h
            have hv2 : ((⟨j.val + 1, by omega⟩ : Fin (W.n + 4)) : ℕ) = j.val + 1 := rfl
            have hs1 : (((⟨i.val + 1, by omega⟩ : Fin (W.n + 4)) + 1 : Fin (W.n + 4)) : ℕ) =
                i.val + 2 := by
              rw [Fin.val_add, Fin.val_one']
              have h1m : 1 % (W.n + 4) = 1 := Nat.mod_eq_of_lt (by omega)
              have h2m : (i.val + 1 + 1) % (W.n + 4) = i.val + 2 :=
                Nat.mod_eq_of_lt (by have := i.is_lt; omega)
              rw [h1m, h2m]
            rw [hs1, hv2] at hv
            apply hi1j
            apply Fin.ext
            show ((i + 1 : Fin ((k : ℕ) - 4 + 4)) : ℕ) = j.val
            rw [Fin.val_add, Fin.val_one']
            have h1m : 1 % ((k : ℕ) - 4 + 4) = 1 := Nat.mod_eq_of_lt (by omega)
            have h2m : (i.val + 1) % ((k : ℕ) - 4 + 4) = i.val + 1 :=
              Nat.mod_eq_of_lt (by have := i.is_lt; omega)
            rw [h1m, h2m]
            omega
          have g3 : (⟨i.val + 1, by omega⟩ : Fin (W.n + 4)) ≠ ⟨j.val + 1, by omega⟩ + 1 := by
            intro h
            have hv := congrArg Fin.val h
            have hv1 : ((⟨i.val + 1, by omega⟩ : Fin (W.n + 4)) : ℕ) = i.val + 1 := rfl
            have hs1 : (((⟨j.val + 1, by omega⟩ : Fin (W.n + 4)) + 1 : Fin (W.n + 4)) : ℕ) =
                j.val + 2 := by
              rw [Fin.val_add, Fin.val_one']
              have h1m : 1 % (W.n + 4) = 1 := Nat.mod_eq_of_lt (by omega)
              have h2m : (j.val + 1 + 1) % (W.n + 4) = j.val + 2 :=
                Nat.mod_eq_of_lt (by have := j.is_lt; omega)
              rw [h1m, h2m]
            rw [hv1, hs1] at hv
            apply hij1
            apply Fin.ext
            show i.val = ((j + 1 : Fin ((k : ℕ) - 4 + 4)) : ℕ)
            rw [Fin.val_add, Fin.val_one']
            have h1m : 1 % ((k : ℕ) - 4 + 4) = 1 := Nat.mod_eq_of_lt (by omega)
            have h2m : (j.val + 1) % ((k : ℕ) - 4 + 4) = j.val + 1 :=
              Nat.mod_eq_of_lt (by have := j.is_lt; omega)
            rw [h1m, h2m]
            omega
          have hd := W.simple ⟨i.val + 1, by omega⟩ ⟨j.val + 1, by omega⟩ g1 g2 g3
          rw [Finset.disjoint_left] at hd
          exact hd hci hcj
  }
  -- successor vertex of an interior `W₂`-edge, in W-terms
  have hsucc2W : ∀ (t : Fin (W.n + 2 - (k : ℕ) + 4)), t ≠ Fin.last (W.n + 2 - (k : ℕ) + 3) →
      W.v ⟨((t + 1 : Fin (W.n + 2 - (k : ℕ) + 4)).val + k) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ =
      W.v ((⟨(t.val + k) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ : Fin (W.n + 4)) + 1) := by
    intro t ht
    have htv : t.val + 1 < W.n + 2 - (k : ℕ) + 4 := by
      have hlt := t.is_lt
      have hnv : t.val ≠ W.n + 2 - (k : ℕ) + 3 := fun h => ht (Fin.ext h)
      omega
    apply congrArg W.v
    apply Fin.ext
    show ((t + 1 : Fin (W.n + 2 - (k : ℕ) + 4)).val + k) % (W.n + 4) =
      ((⟨(t.val + k) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ : Fin (W.n + 4)) + 1 : Fin (W.n + 4)).val
    have h3 : (t + 1 : Fin (W.n + 2 - (k : ℕ) + 4)).val = t.val + 1 := by
      rw [Fin.val_add, Fin.val_one']
      have h1m' : 1 % (W.n + 2 - (k : ℕ) + 4) = 1 := Nat.mod_eq_of_lt (by omega)
      have h2m' : (t.val + 1) % (W.n + 2 - (k : ℕ) + 4) = t.val + 1 := Nat.mod_eq_of_lt htv
      rw [h1m', h2m']
    rw [h3, Fin.val_add, Fin.val_one']
    have h1m : 1 % (W.n + 4) = 1 := Nat.mod_eq_of_lt (by omega)
    rw [h1m]
    have hsum : t.val + 1 + k = t.val + k + 1 := by omega
    rw [hsum, Nat.add_mod (t.val + k) 1 (W.n + 4), Nat.mod_eq_of_lt (by omega : 1 < W.n + 4)]
  -- segment of the `t`-th edge of `W₂` (interior `t`), in W-terms
  have hseg2W : ∀ (t : Fin (W.n + 2 - (k : ℕ) + 4)), t ≠ Fin.last (W.n + 2 - (k : ℕ) + 3) →
      ({W.v ⟨(t.val + k) % (W.n + 4), Nat.mod_lt _ (by omega)⟩,
        midPt (W.v ⟨(t.val + k) % (W.n + 4), Nat.mod_lt _ (by omega)⟩)
        (W.v ⟨((t + 1 : Fin (W.n + 2 - (k : ℕ) + 4)).val + k) % (W.n + 4), Nat.mod_lt _ (by omega)⟩),
        W.v ⟨((t + 1 : Fin (W.n + 2 - (k : ℕ) + 4)).val + k) % (W.n + 4), Nat.mod_lt _ (by omega)⟩} :
        Finset Cell) =
      W.edgePts ⟨(t.val + k) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ := by
    intro t ht
    rw [hsucc2W t ht]
  -- midpoint of an interior `W₁`-edge, in W-terms
  have hmid1W : ∀ (t : Fin ((k : ℕ) - 4 + 4)), t ≠ Fin.last ((k : ℕ) - 4 + 3) →
      W₁.mid t = W.mid ⟨t.val + 1, by omega⟩ := by
    intro t ht
    show midPt (W₁.v t) (W₁.v (t + 1)) =
      midPt (W.v ⟨t.val + 1, by omega⟩) (W.v (⟨t.val + 1, by omega⟩ + 1))
    have e : W₁.v (t + 1) = W.v ((⟨t.val + 1, by omega⟩ : Fin (W.n + 4)) + 1) := hsucc1W t ht
    rw [e]
  -- midpoint of an interior `W₂`-edge, in W-terms
  -- the wrap edge of `W₂` is the chord segment (traversed downwards)
  have hchord2W : ({W.v ⟨((Fin.last (W.n + 2 - (k : ℕ) + 3)).val + k) % (W.n + 4),
      Nat.mod_lt _ (by omega)⟩,
      midPt (W.v ⟨((Fin.last (W.n + 2 - (k : ℕ) + 3)).val + k) % (W.n + 4), Nat.mod_lt _ (by omega)⟩)
        (W.v ⟨((Fin.last (W.n + 2 - (k : ℕ) + 3) + 1 : Fin (W.n + 2 - (k : ℕ) + 4)).val + k) % (W.n + 4),
          Nat.mod_lt _ (by omega)⟩),
      W.v ⟨((Fin.last (W.n + 2 - (k : ℕ) + 3) + 1 : Fin (W.n + 2 - (k : ℕ) + 4)).val + k) % (W.n + 4),
        Nat.mod_lt _ (by omega)⟩} : Finset Cell) =
      {(x₀ + 2, ym - 2), (x₀ + 2, ym - 1), (x₀ + 2, ym)} := by
    have e0 : (Fin.last (W.n + 2 - (k : ℕ) + 3) + 1 : Fin (W.n + 2 - (k : ℕ) + 4)) = 0 :=
      Fin.ext val_last_succ
    have hlast : (⟨((Fin.last (W.n + 2 - (k : ℕ) + 3)).val + k) % (W.n + 4),
        Nat.mod_lt _ (by omega)⟩ : Fin (W.n + 4)) = 1 := by
      apply Fin.ext
      show ((Fin.last (W.n + 2 - (k : ℕ) + 3)).val + k) % (W.n + 4) = ((1 : Fin (W.n + 4)) : ℕ)
      rw [Fin.val_last, val_one_fin]
      have e : W.n + 2 - (k : ℕ) + 3 + k = W.n + 5 := by omega
      rw [e]
      have e2 : W.n + 5 = 1 + (W.n + 4) := by omega
      rw [e2, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    have hv0 : (⟨((0 : Fin (W.n + 2 - (k : ℕ) + 4)).val + k) % (W.n + 4),
        Nat.mod_lt _ (by omega)⟩ : Fin (W.n + 4)) = k := by
      apply Fin.ext
      show ((0 : Fin (W.n + 2 - (k : ℕ) + 4)).val + k) % (W.n + 4) = (k : ℕ)
      rw [val_zero_fin, Nat.zero_add]
      exact Nat.mod_eq_of_lt k.isLt
    have p1 : W.v ⟨((Fin.last (W.n + 2 - (k : ℕ) + 3)).val + k) % (W.n + 4),
        Nat.mod_lt _ (by omega)⟩ = (x₀ + 2, ym) := by
      rw [hlast, h1]
    have p2 : W.v ⟨((Fin.last (W.n + 2 - (k : ℕ) + 3) + 1 : Fin (W.n + 2 - (k : ℕ) + 4)).val + k) %
        (W.n + 4), Nat.mod_lt _ (by omega)⟩ = (x₀ + 2, ym - 2) := by
      have e2 : (⟨((Fin.last (W.n + 2 - (k : ℕ) + 3) + 1 : Fin (W.n + 2 - (k : ℕ) + 4)).val + k) %
          (W.n + 4), Nat.mod_lt _ (by omega)⟩ : Fin (W.n + 4)) = k := by
        apply Fin.ext
        show ((Fin.last (W.n + 2 - (k : ℕ) + 3) + 1 : Fin (W.n + 2 - (k : ℕ) + 4)).val + k) %
          (W.n + 4) = (k : ℕ)
        rw [val_last_succ, Nat.zero_add]
        exact Nat.mod_eq_of_lt k.isLt
      rw [e2, hk]
    rw [p1, p2]
    exact hchord_rev
  -- the left sub-loop `W₂`: vertices `v k, …, v (n+3), v 0, v 1`
  let W₂ : OrthoLoop := {
    a := W.a
    b := W.b
    n := W.n + 2 - (k : ℕ)
    v := fun j => W.v ⟨(j.val + k) % (W.n + 4), Nat.mod_lt _ (by omega)⟩
    inj := by
      intro i j h
      have h2 := W.inj h
      have h3 := congrArg Fin.val h2
      have h4 : ((⟨(j.val + k) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ : Fin (W.n + 4)) : ℕ) =
          (j.val + k) % (W.n + 4) := rfl
      have h5 : ((⟨(i.val + k) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ : Fin (W.n + 4)) : ℕ) =
          (i.val + k) % (W.n + 4) := rfl
      rw [h4, h5] at h3
      have hi_lt := i.is_lt
      have hj_lt := j.is_lt
      have h6 : i.val = j.val := by
        by_cases hi1 : i.val + k < W.n + 4
        · rw [Nat.mod_eq_of_lt hi1] at h3
          by_cases hj1 : j.val + k < W.n + 4
          · rw [Nat.mod_eq_of_lt hj1] at h3
            omega
          · push_neg at hj1
            have h7 : (j.val + k) % (W.n + 4) = j.val + k - (W.n + 4) := by
              rw [Nat.mod_eq_sub_mod (by omega : W.n + 4 ≤ j.val + k)]
              exact Nat.mod_eq_of_lt (by omega)
            omega
        · push_neg at hi1
          have h7 : (i.val + k) % (W.n + 4) = i.val + k - (W.n + 4) := by
            rw [Nat.mod_eq_sub_mod (by omega : W.n + 4 ≤ i.val + k)]
            exact Nat.mod_eq_of_lt (by omega)
          by_cases hj1 : j.val + k < W.n + 4
          · rw [Nat.mod_eq_of_lt hj1] at h3
            omega
          · push_neg at hj1
            have h8 : (j.val + k) % (W.n + 4) = j.val + k - (W.n + 4) := by
              rw [Nat.mod_eq_sub_mod (by omega : W.n + 4 ≤ j.val + k)]
              exact Nat.mod_eq_of_lt (by omega)
            omega
      exact Fin.ext h6
    step := by
      intro i
      by_cases hi : i = Fin.last (W.n + 2 - (k : ℕ) + 3)
      · -- the chord edge, from `v 1` back down to `v k`
        rw [hi]
        have e0 : (Fin.last (W.n + 2 - (k : ℕ) + 3) + 1 : Fin (W.n + 2 - (k : ℕ) + 4)) =
            (0 : Fin (W.n + 2 - (k : ℕ) + 4)) := Fin.ext val_last_succ
        rw [e0]
        have hlast : (⟨((Fin.last (W.n + 2 - (k : ℕ) + 3)).val + k) % (W.n + 4),
            Nat.mod_lt _ (by omega)⟩ : Fin (W.n + 4)) = 1 := by
          apply Fin.ext
          show ((Fin.last (W.n + 2 - (k : ℕ) + 3)).val + k) % (W.n + 4) = ((1 : Fin (W.n + 4)) : ℕ)
          rw [Fin.val_last, val_one_fin]
          have e : W.n + 2 - (k : ℕ) + 3 + k = W.n + 5 := by omega
          rw [e]
          have e2 : W.n + 5 = 1 + (W.n + 4) := by omega
          rw [e2, Nat.add_mod_right]
          exact Nat.mod_eq_of_lt (by omega)
        have hv0 : (⟨((0 : Fin (W.n + 2 - (k : ℕ) + 4)).val + k) % (W.n + 4),
            Nat.mod_lt _ (by omega)⟩ : Fin (W.n + 4)) = k := by
          apply Fin.ext
          show ((0 : Fin (W.n + 2 - (k : ℕ) + 4)).val + k) % (W.n + 4) = (k : ℕ)
          rw [val_zero_fin, Nat.zero_add]
          exact Nat.mod_eq_of_lt k.isLt
        have hs : W.v ⟨((Fin.last (W.n + 2 - (k : ℕ) + 3)).val + k) % (W.n + 4),
            Nat.mod_lt _ (by omega)⟩ = W.v 1 := by
          rw [hlast]
        have hs0 : W.v ⟨((0 : Fin (W.n + 2 - (k : ℕ) + 4)).val + k) % (W.n + 4),
            Nat.mod_lt _ (by omega)⟩ = W.v k := by
          rw [hv0]
        rw [hs, hs0, h1, hk]
        exact Or.inr (Or.inl ⟨by simp, by show (ym - 2 : ℤ) = ym - 2; omega⟩)
      · -- an original edge of `W`
        have hiv : (i : ℕ) ≠ W.n + 2 - (k : ℕ) + 3 := by
          intro h
          exact hi (Fin.ext h)
        have e : (i + 1 : Fin (W.n + 2 - (k : ℕ) + 4)) = ⟨i.val + 1, by omega⟩ := by
          apply Fin.ext
          rw [Fin.val_add, Fin.val_one']
          have hv1 : ((⟨i.val + 1, by omega⟩ : Fin (W.n + 2 - (k : ℕ) + 4)) : ℕ) = i.val + 1 := rfl
          rw [hv1]
          have h1m : 1 % (W.n + 2 - (k : ℕ) + 4) = 1 := Nat.mod_eq_of_lt (by omega)
          have h2m : (i.val + 1) % (W.n + 2 - (k : ℕ) + 4) = i.val + 1 :=
            Nat.mod_eq_of_lt (by have := i.is_lt; omega)
          rw [h1m, h2m]
        rw [e]
        have hstep0 := W.step ⟨(i.val + k) % (W.n + 4), Nat.mod_lt _ (by omega)⟩
        have hidx : (⟨(i.val + k) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ + 1 : Fin (W.n + 4)) =
            ⟨(i.val + 1 + k) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ := by
          apply Fin.ext
          rw [Fin.val_add, Fin.val_one']
          have h1m : 1 % (W.n + 4) = 1 := Nat.mod_eq_of_lt (by omega)
          rw [h1m]
          show ((i.val + k) % (W.n + 4) + 1) % (W.n + 4) = (i.val + 1 + k) % (W.n + 4)
          have hsum : i.val + 1 + k = i.val + k + 1 := by omega
          rw [hsum, Nat.add_mod (i.val + k) 1 (W.n + 4), Nat.mod_eq_of_lt (by omega : 1 < W.n + 4)]
        rw [hidx] at hstep0
        have hvv : (⟨(i.val + 1 + k) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ : Fin (W.n + 4)) =
            ⟨((⟨i.val + 1, by omega⟩ : Fin (W.n + 2 - (k : ℕ) + 4)).val + k) % (W.n + 4),
            Nat.mod_lt _ (by omega)⟩ := by
          apply Fin.ext
          show (i.val + 1 + k) % (W.n + 4) = ((⟨i.val + 1, by omega⟩ : Fin (W.n + 2 - (k : ℕ) + 4)).val + k) % (W.n + 4)
          have hv1 : ((⟨i.val + 1, by omega⟩ : Fin (W.n + 2 - (k : ℕ) + 4)) : ℕ) = i.val + 1 := rfl
          rw [hv1]
        rw [hvv]
        exact hstep0
    par := fun j => W.par _
    simple := by
      intro i j hij hi1j hij1
      rw [Finset.disjoint_left]
      intro c hci hcj
      beta_reduce at hci hcj
      by_cases hi : i = Fin.last (W.n + 2 - (k : ℕ) + 3)
      · by_cases hj : j = Fin.last (W.n + 2 - (k : ℕ) + 3)
        · exact absurd (hi.trans hj.symm) hij
        · -- i chord, j interior
          rw [hi, hchord2W] at hci
          rw [hseg2W j hj] at hcj
          have hj0 : j ≠ 0 := by
            intro h
            apply hi1j
            rw [hi, h]
            exact Fin.ext val_last_succ
          have hjn : (j : ℕ) ≠ W.n + 2 - (k : ℕ) + 2 := by
            intro h
            apply hij1
            rw [hi]
            apply Fin.ext
            show ((Fin.last (W.n + 2 - (k : ℕ) + 3)) : ℕ) = ((j + 1 : Fin (W.n + 2 - (k : ℕ) + 4)) : ℕ)
            rw [Fin.val_last, Fin.val_add, Fin.val_one']
            have h1m : 1 % (W.n + 2 - (k : ℕ) + 4) = 1 := Nat.mod_eq_of_lt (by omega)
            have h2m : (j.val + 1) % (W.n + 2 - (k : ℕ) + 4) = j.val + 1 :=
              Nat.mod_eq_of_lt (by have := j.is_lt; omega)
            rw [h1m, h2m]
            omega
          have hjm : (⟨(j.val + k) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ : Fin (W.n + 4)) =
              ⟨j.val + k, by
                have hj0v : (j : ℕ) ≠ 0 := fun h => hj0 (Fin.ext h)
                have hjv : (j : ℕ) ≠ W.n + 2 - (k : ℕ) + 3 := fun h => hj (Fin.ext h)
                have hjl := j.is_lt
                omega⟩ := by
            apply Fin.ext
            show (j.val + k) % (W.n + 4) = j.val + k
            have hj0v : (j : ℕ) ≠ 0 := fun h => hj0 (Fin.ext h)
            have hjv : (j : ℕ) ≠ W.n + 2 - (k : ℕ) + 3 := fun h => hj (Fin.ext h)
            have hjl := j.is_lt
            exact Nat.mod_eq_of_lt (by omega)
          rw [hjm] at hcj
          have hbnd : j.val + k < W.n + 4 := by
            have hj0v : (j : ℕ) ≠ 0 := fun h => hj0 (Fin.ext h)
            have hjv : (j : ℕ) ≠ W.n + 2 - (k : ℕ) + 3 := fun h => hj (Fin.ext h)
            have hjl := j.is_lt
            omega
          have hd := hchord_disj ⟨j.val + k, hbnd⟩ (by
            intro h
            have hv := congrArg Fin.val h
            have hv1 : ((⟨j.val + k, hbnd⟩ : Fin (W.n + 4)) : ℕ) = j.val + k := rfl
            rw [hv1, val_zero_fin] at hv
            omega) (by
            intro h
            have hv := congrArg Fin.val h
            have hv1 : ((⟨j.val + k, hbnd⟩ : Fin (W.n + 4)) : ℕ) = j.val + k := rfl
            rw [hv1, val_one_fin] at hv
            omega) (by
            intro h
            have hv := congrArg Fin.val h
            have hv1 : ((⟨j.val + k, hbnd⟩ : Fin (W.n + 4)) : ℕ) = j.val + k := rfl
            rw [hv1] at hv
            have hv2 : ((k - 1 : Fin (W.n + 4)) : ℕ) = (k : ℕ) - 1 := by
              have h1k : (1 : Fin (W.n + 4)) ≤ k := by
                rw [Fin.le_def]
                have h1m : ((1 : Fin (W.n + 4)) : ℕ) = 1 := by
                  rw [Fin.val_one']
                  exact Nat.mod_eq_of_lt (by omega)
                rw [h1m]
                omega
              rw [Fin.sub_val_of_le h1k]
              have h1m : ((1 : Fin (W.n + 4)) : ℕ) = 1 := by
                rw [Fin.val_one']
                exact Nat.mod_eq_of_lt (by omega)
              rw [h1m]
            rw [hv2] at hv
            omega) (by
            intro h
            have hv := congrArg Fin.val h
            have hv1 : ((⟨j.val + k, hbnd⟩ : Fin (W.n + 4)) : ℕ) = j.val + k := rfl
            rw [hv1] at hv
            have hz : j.val = 0 := by omega
            exact hj0 (Fin.ext hz))
          rw [Finset.disjoint_left] at hd
          exact hd hci hcj
      · by_cases hj : j = Fin.last (W.n + 2 - (k : ℕ) + 3)
        · -- j chord, i interior: symmetric
          rw [hj, hchord2W] at hcj
          rw [hseg2W i hi] at hci
          have hi0 : i ≠ 0 := by
            intro h
            apply hij1
            rw [hj, h]
            exact (Fin.ext val_last_succ).symm
          have hin : (i : ℕ) ≠ W.n + 2 - (k : ℕ) + 2 := by
            intro h
            apply hi1j
            rw [hj]
            apply Fin.ext
            show ((i + 1 : Fin (W.n + 2 - (k : ℕ) + 4)) : ℕ) = ((Fin.last (W.n + 2 - (k : ℕ) + 3)) : ℕ)
            rw [Fin.val_last, Fin.val_add, Fin.val_one']
            have h1m : 1 % (W.n + 2 - (k : ℕ) + 4) = 1 := Nat.mod_eq_of_lt (by omega)
            have h2m : (i.val + 1) % (W.n + 2 - (k : ℕ) + 4) = i.val + 1 :=
              Nat.mod_eq_of_lt (by have := i.is_lt; omega)
            rw [h1m, h2m]
            omega
          have him : (⟨(i.val + k) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ : Fin (W.n + 4)) =
              ⟨i.val + k, by
                have hi0v : (i : ℕ) ≠ 0 := fun h => hi0 (Fin.ext h)
                have hiv : (i : ℕ) ≠ W.n + 2 - (k : ℕ) + 3 := fun h => hi (Fin.ext h)
                have hil := i.is_lt
                omega⟩ := by
            apply Fin.ext
            show (i.val + k) % (W.n + 4) = i.val + k
            have hi0v : (i : ℕ) ≠ 0 := fun h => hi0 (Fin.ext h)
            have hiv : (i : ℕ) ≠ W.n + 2 - (k : ℕ) + 3 := fun h => hi (Fin.ext h)
            have hil := i.is_lt
            exact Nat.mod_eq_of_lt (by omega)
          rw [him] at hci
          have hbnd : i.val + k < W.n + 4 := by
            have hi0v : (i : ℕ) ≠ 0 := fun h => hi0 (Fin.ext h)
            have hiv : (i : ℕ) ≠ W.n + 2 - (k : ℕ) + 3 := fun h => hi (Fin.ext h)
            have hil := i.is_lt
            omega
          have hd := hchord_disj ⟨i.val + k, hbnd⟩ (by
            intro h
            have hv := congrArg Fin.val h
            have hv1 : ((⟨i.val + k, hbnd⟩ : Fin (W.n + 4)) : ℕ) = i.val + k := rfl
            rw [hv1, val_zero_fin] at hv
            omega) (by
            intro h
            have hv := congrArg Fin.val h
            have hv1 : ((⟨i.val + k, hbnd⟩ : Fin (W.n + 4)) : ℕ) = i.val + k := rfl
            rw [hv1, val_one_fin] at hv
            omega) (by
            intro h
            have hv := congrArg Fin.val h
            have hv1 : ((⟨i.val + k, hbnd⟩ : Fin (W.n + 4)) : ℕ) = i.val + k := rfl
            rw [hv1] at hv
            have hv2 : ((k - 1 : Fin (W.n + 4)) : ℕ) = (k : ℕ) - 1 := by
              have h1k : (1 : Fin (W.n + 4)) ≤ k := by
                rw [Fin.le_def]
                have h1m : ((1 : Fin (W.n + 4)) : ℕ) = 1 := by
                  rw [Fin.val_one']
                  exact Nat.mod_eq_of_lt (by omega)
                rw [h1m]
                omega
              rw [Fin.sub_val_of_le h1k]
              have h1m : ((1 : Fin (W.n + 4)) : ℕ) = 1 := by
                rw [Fin.val_one']
                exact Nat.mod_eq_of_lt (by omega)
              rw [h1m]
            rw [hv2] at hv
            omega) (by
            intro h
            have hv := congrArg Fin.val h
            have hv1 : ((⟨i.val + k, hbnd⟩ : Fin (W.n + 4)) : ℕ) = i.val + k := rfl
            rw [hv1] at hv
            have hz : i.val = 0 := by omega
            exact hi0 (Fin.ext hz))
          rw [Finset.disjoint_left] at hd
          exact hd hcj hci
        · -- both interior: W.simple applies
          rw [hseg2W i hi] at hci
          rw [hseg2W j hj] at hcj
          have hi_lt := i.is_lt
          have hj_lt := j.is_lt
          have hiv : i.val ≠ W.n + 2 - (k : ℕ) + 3 := fun h => hi (Fin.ext h)
          have hjv : j.val ≠ W.n + 2 - (k : ℕ) + 3 := fun h => hj (Fin.ext h)
          have g1 : (⟨(i.val + k) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ : Fin (W.n + 4)) ≠
              ⟨(j.val + k) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ := by
            intro h
            have hv := congrArg Fin.val h
            have hv1 : ((⟨(i.val + k) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ : Fin (W.n + 4)) : ℕ) =
                (i.val + k) % (W.n + 4) := rfl
            have hv2 : ((⟨(j.val + k) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ : Fin (W.n + 4)) : ℕ) =
                (j.val + k) % (W.n + 4) := rfl
            rw [hv1, hv2] at hv
            by_cases ci : i.val + k < W.n + 4
            · rw [Nat.mod_eq_of_lt ci] at hv
              by_cases cj : j.val + k < W.n + 4
              · rw [Nat.mod_eq_of_lt cj] at hv
                exact hij (Fin.ext (by omega))
              · push_neg at cj
                have hm : (j.val + k) % (W.n + 4) = j.val + k - (W.n + 4) := by
                  rw [Nat.mod_eq_sub_mod (by omega : W.n + 4 ≤ j.val + k)]
                  exact Nat.mod_eq_of_lt (by omega)
                rw [hm] at hv
                omega
            · push_neg at ci
              have hm : (i.val + k) % (W.n + 4) = i.val + k - (W.n + 4) := by
                rw [Nat.mod_eq_sub_mod (by omega : W.n + 4 ≤ i.val + k)]
                exact Nat.mod_eq_of_lt (by omega)
              rw [hm] at hv
              by_cases cj : j.val + k < W.n + 4
              · rw [Nat.mod_eq_of_lt cj] at hv
                omega
              · push_neg at cj
                have hm2 : (j.val + k) % (W.n + 4) = j.val + k - (W.n + 4) := by
                  rw [Nat.mod_eq_sub_mod (by omega : W.n + 4 ≤ j.val + k)]
                  exact Nat.mod_eq_of_lt (by omega)
                rw [hm2] at hv
                exact hij (Fin.ext (by omega))
          have g2 : (⟨(i.val + k) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ : Fin (W.n + 4)) + 1 ≠
              ⟨(j.val + k) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ := by
            intro h
            have hv := congrArg Fin.val h
            have hv2 : ((⟨(j.val + k) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ : Fin (W.n + 4)) : ℕ) =
                (j.val + k) % (W.n + 4) := rfl
            have hs1 : (((⟨(i.val + k) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ : Fin (W.n + 4)) + 1 :
                Fin (W.n + 4)) : ℕ) = (i.val + 1 + k) % (W.n + 4) := by
              rw [Fin.val_add, Fin.val_one']
              have h1m : 1 % (W.n + 4) = 1 := Nat.mod_eq_of_lt (by omega)
              rw [h1m]
              show ((i.val + k) % (W.n + 4) + 1) % (W.n + 4) = (i.val + 1 + k) % (W.n + 4)
              have hsum : i.val + 1 + k = i.val + k + 1 := by omega
              rw [hsum, Nat.add_mod (i.val + k) 1 (W.n + 4), Nat.mod_eq_of_lt (by omega : 1 < W.n + 4)]
            rw [hs1, hv2] at hv
            by_cases ci : i.val + 1 + k < W.n + 4
            · rw [Nat.mod_eq_of_lt ci] at hv
              by_cases cj : j.val + k < W.n + 4
              · rw [Nat.mod_eq_of_lt cj] at hv
                apply hi1j
                apply Fin.ext
                show ((i + 1 : Fin (W.n + 2 - (k : ℕ) + 4)) : ℕ) = j.val
                rw [Fin.val_add, Fin.val_one']
                have h1m : 1 % (W.n + 2 - (k : ℕ) + 4) = 1 := Nat.mod_eq_of_lt (by omega)
                have h2m : (i.val + 1) % (W.n + 2 - (k : ℕ) + 4) = i.val + 1 :=
                  Nat.mod_eq_of_lt (by omega)
                rw [h1m, h2m]
                omega
              · push_neg at cj
                have hm : (j.val + k) % (W.n + 4) = j.val + k - (W.n + 4) := by
                  rw [Nat.mod_eq_sub_mod (by omega : W.n + 4 ≤ j.val + k)]
                  exact Nat.mod_eq_of_lt (by omega)
                rw [hm] at hv
                omega
            · push_neg at ci
              have hm : (i.val + 1 + k) % (W.n + 4) = i.val + 1 + k - (W.n + 4) := by
                rw [Nat.mod_eq_sub_mod (by omega : W.n + 4 ≤ i.val + 1 + k)]
                exact Nat.mod_eq_of_lt (by omega)
              rw [hm] at hv
              by_cases cj : j.val + k < W.n + 4
              · rw [Nat.mod_eq_of_lt cj] at hv
                omega
              · push_neg at cj
                have hm2 : (j.val + k) % (W.n + 4) = j.val + k - (W.n + 4) := by
                  rw [Nat.mod_eq_sub_mod (by omega : W.n + 4 ≤ j.val + k)]
                  exact Nat.mod_eq_of_lt (by omega)
                rw [hm2] at hv
                apply hi1j
                apply Fin.ext
                show ((i + 1 : Fin (W.n + 2 - (k : ℕ) + 4)) : ℕ) = j.val
                rw [Fin.val_add, Fin.val_one']
                have h1m : 1 % (W.n + 2 - (k : ℕ) + 4) = 1 := Nat.mod_eq_of_lt (by omega)
                have h2m : (i.val + 1) % (W.n + 2 - (k : ℕ) + 4) = i.val + 1 :=
                  Nat.mod_eq_of_lt (by omega)
                rw [h1m, h2m]
                omega
          have g3 : (⟨(i.val + k) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ : Fin (W.n + 4)) ≠
              ⟨(j.val + k) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ + 1 := by
            intro h
            have hv := congrArg Fin.val h
            have hv1 : ((⟨(i.val + k) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ : Fin (W.n + 4)) : ℕ) =
                (i.val + k) % (W.n + 4) := rfl
            have hs1 : (((⟨(j.val + k) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ : Fin (W.n + 4)) + 1 :
                Fin (W.n + 4)) : ℕ) = (j.val + 1 + k) % (W.n + 4) := by
              rw [Fin.val_add, Fin.val_one']
              have h1m : 1 % (W.n + 4) = 1 := Nat.mod_eq_of_lt (by omega)
              rw [h1m]
              show ((j.val + k) % (W.n + 4) + 1) % (W.n + 4) = (j.val + 1 + k) % (W.n + 4)
              have hsum : j.val + 1 + k = j.val + k + 1 := by omega
              rw [hsum, Nat.add_mod (j.val + k) 1 (W.n + 4), Nat.mod_eq_of_lt (by omega : 1 < W.n + 4)]
            rw [hv1, hs1] at hv
            by_cases ci : i.val + k < W.n + 4
            · rw [Nat.mod_eq_of_lt ci] at hv
              by_cases cj : j.val + 1 + k < W.n + 4
              · rw [Nat.mod_eq_of_lt cj] at hv
                apply hij1
                apply Fin.ext
                show i.val = ((j + 1 : Fin (W.n + 2 - (k : ℕ) + 4)) : ℕ)
                rw [Fin.val_add, Fin.val_one']
                have h1m : 1 % (W.n + 2 - (k : ℕ) + 4) = 1 := Nat.mod_eq_of_lt (by omega)
                have h2m : (j.val + 1) % (W.n + 2 - (k : ℕ) + 4) = j.val + 1 :=
                  Nat.mod_eq_of_lt (by omega)
                rw [h1m, h2m]
                omega
              · push_neg at cj
                have hm : (j.val + 1 + k) % (W.n + 4) = j.val + 1 + k - (W.n + 4) := by
                  rw [Nat.mod_eq_sub_mod (by omega : W.n + 4 ≤ j.val + 1 + k)]
                  exact Nat.mod_eq_of_lt (by omega)
                rw [hm] at hv
                omega
            · push_neg at ci
              have hm : (i.val + k) % (W.n + 4) = i.val + k - (W.n + 4) := by
                rw [Nat.mod_eq_sub_mod (by omega : W.n + 4 ≤ i.val + k)]
                exact Nat.mod_eq_of_lt (by omega)
              rw [hm] at hv
              by_cases cj : j.val + 1 + k < W.n + 4
              · rw [Nat.mod_eq_of_lt cj] at hv
                omega
              · push_neg at cj
                have hm2 : (j.val + 1 + k) % (W.n + 4) = j.val + 1 + k - (W.n + 4) := by
                  rw [Nat.mod_eq_sub_mod (by omega : W.n + 4 ≤ j.val + 1 + k)]
                  exact Nat.mod_eq_of_lt (by omega)
                rw [hm2] at hv
                apply hij1
                apply Fin.ext
                show i.val = ((j + 1 : Fin (W.n + 2 - (k : ℕ) + 4)) : ℕ)
                rw [Fin.val_add, Fin.val_one']
                have h1m : 1 % (W.n + 2 - (k : ℕ) + 4) = 1 := Nat.mod_eq_of_lt (by omega)
                have h2m : (j.val + 1) % (W.n + 2 - (k : ℕ) + 4) = j.val + 1 :=
                  Nat.mod_eq_of_lt (by omega)
                rw [h1m, h2m]
                omega
          have hd := W.simple _ _ g1 g2 g3
          rw [Finset.disjoint_left] at hd
          exact hd hci hcj
  }
  have hW1n : W₁.n = (k : ℕ) - 4 := rfl
  have hW2n : W₂.n = W.n + 2 - (k : ℕ) := rfl
  -- special vertices of the two sub-loops
  have hW₁last : W₁.v (Fin.last ((k : ℕ) - 4 + 3)) = (x₀ + 2, ym - 2) := by
    show W.v ⟨(Fin.last ((k : ℕ) - 4 + 3)).val + 1, by omega⟩ = (x₀ + 2, ym - 2)
    have hlast : (⟨(Fin.last ((k : ℕ) - 4 + 3)).val + 1, by omega⟩ : Fin (W.n + 4)) = k := by
      apply Fin.ext
      show ((Fin.last ((k : ℕ) - 4 + 3)).val + 1 : ℕ) = (k : ℕ)
      rw [Fin.val_last]
      omega
    rw [hlast, hk]
  have hW₁zero : W₁.v (0 : Fin (W₁.n + 4)) = (x₀ + 2, ym) := by
    show W.v ⟨(0 : Fin ((k : ℕ) - 4 + 4)).val + 1, by omega⟩ = (x₀ + 2, ym)
    have hv0 : (⟨(0 : Fin ((k : ℕ) - 4 + 4)).val + 1, by omega⟩ : Fin (W.n + 4)) = 1 := by
      apply Fin.ext
      show ((0 : Fin ((k : ℕ) - 4 + 4)).val + 1 : ℕ) = ((1 : Fin (W.n + 4)) : ℕ)
      rw [val_zero_fin, val_one_fin]
    rw [hv0, h1]
  have hW₁succ_last : (Fin.last ((k : ℕ) - 4 + 3) + 1 : Fin (W₁.n + 4)) = 0 :=
    Fin.ext val_last_succ
  have hW₂last : W₂.v (Fin.last (W.n + 2 - (k : ℕ) + 3)) = (x₀ + 2, ym) := by
    show W.v ⟨((Fin.last (W.n + 2 - (k : ℕ) + 3)).val + k) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ =
      (x₀ + 2, ym)
    have hlast : (⟨((Fin.last (W.n + 2 - (k : ℕ) + 3)).val + k) % (W.n + 4),
        Nat.mod_lt _ (by omega)⟩ : Fin (W.n + 4)) = 1 := by
      apply Fin.ext
      show ((Fin.last (W.n + 2 - (k : ℕ) + 3)).val + k) % (W.n + 4) = ((1 : Fin (W.n + 4)) : ℕ)
      rw [Fin.val_last, val_one_fin]
      have e : W.n + 2 - (k : ℕ) + 3 + k = W.n + 5 := by omega
      rw [e]
      have e2 : W.n + 5 = 1 + (W.n + 4) := by omega
      rw [e2, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hlast, h1]
  have hW₂zero : W₂.v (0 : Fin (W₂.n + 4)) = (x₀ + 2, ym - 2) := by
    show W.v ⟨((0 : Fin (W.n + 2 - (k : ℕ) + 4)).val + k) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ =
      (x₀ + 2, ym - 2)
    have hv0 : (⟨((0 : Fin (W.n + 2 - (k : ℕ) + 4)).val + k) % (W.n + 4),
        Nat.mod_lt _ (by omega)⟩ : Fin (W.n + 4)) = k := by
      apply Fin.ext
      show ((0 : Fin (W.n + 2 - (k : ℕ) + 4)).val + k) % (W.n + 4) = (k : ℕ)
      rw [val_zero_fin, Nat.zero_add]
      exact Nat.mod_eq_of_lt k.isLt
    rw [hv0, hk]
  have hW₂succ_last : (Fin.last (W.n + 2 - (k : ℕ) + 3) + 1 : Fin (W₂.n + 4)) = 0 :=
    Fin.ext val_last_succ
  have hmid2W : ∀ (t : Fin (W.n + 2 - (k : ℕ) + 4)), t ≠ Fin.last (W.n + 2 - (k : ℕ) + 3) →
      W₂.mid t = W.mid ⟨(t.val + k) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ := by
    intro t ht
    show midPt (W₂.v t) (W₂.v (t + 1)) =
      midPt (W.v ⟨(t.val + k) % (W.n + 4), Nat.mod_lt _ (by omega)⟩)
        (W.v (⟨(t.val + k) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ + 1))
    have e : W₂.v (t + 1) = W.v ((⟨(t.val + k) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ : Fin (W.n + 4)) + 1) :=
      hsucc2W t ht
    rw [e]
  refine ⟨W₁, W₂, ?_, ?_, ?_⟩
  · -- I: W.I = W₁.I + W₂.I + 1
    -- (a) the flip identity: crossing parity is additive over the split
    have hflip : ∀ c : Cell, W.p2 c = W₁.p2 c + W₂.p2 c := by
      intro c
      let fW : ℕ → ZMod 2 := fun i =>
        if h : i < W.n + 4 then
          (if W.vert ⟨i, h⟩ ∧ c.1 < W.x ⟨i, h⟩ ∧ W.lo ⟨i, h⟩ ≤ c.2 ∧ c.2 < W.hi ⟨i, h⟩
            then (1 : ZMod 2) else 0)
        else 0
      let fW₁ : ℕ → ZMod 2 := fun j =>
        if h : j < W₁.n + 4 then
          (if W₁.vert ⟨j, h⟩ ∧ c.1 < W₁.x ⟨j, h⟩ ∧ W₁.lo ⟨j, h⟩ ≤ c.2 ∧ c.2 < W₁.hi ⟨j, h⟩
            then (1 : ZMod 2) else 0)
        else 0
      let fW₂ : ℕ → ZMod 2 := fun j =>
        if h : j < W₂.n + 4 then
          (if W₂.vert ⟨j, h⟩ ∧ c.1 < W₂.x ⟨j, h⟩ ∧ W₂.lo ⟨j, h⟩ ≤ c.2 ∧ c.2 < W₂.hi ⟨j, h⟩
            then (1 : ZMod 2) else 0)
        else 0
      have hfW : ∀ i : Fin (W.n + 4),
          (if W.vert i ∧ c.1 < W.x i ∧ W.lo i ≤ c.2 ∧ c.2 < W.hi i then (1 : ZMod 2) else 0) =
            fW ↑i := by
        intro i
        have hi : ↑i < W.n + 4 := i.isLt
        have hi2 : (⟨↑i, hi⟩ : Fin (W.n + 4)) = i := Fin.ext rfl
        show (if W.vert i ∧ c.1 < W.x i ∧ W.lo i ≤ c.2 ∧ c.2 < W.hi i then (1 : ZMod 2) else 0) =
          if h : ↑i < W.n + 4 then
            (if W.vert ⟨↑i, h⟩ ∧ c.1 < W.x ⟨↑i, h⟩ ∧ W.lo ⟨↑i, h⟩ ≤ c.2 ∧ c.2 < W.hi ⟨↑i, h⟩
              then (1 : ZMod 2) else 0)
          else 0
        rw [dif_pos hi, hi2]
      have hfW₁ : ∀ j : Fin (W₁.n + 4),
          (if W₁.vert j ∧ c.1 < W₁.x j ∧ W₁.lo j ≤ c.2 ∧ c.2 < W₁.hi j then (1 : ZMod 2) else 0) =
            fW₁ ↑j := by
        intro j
        have hj : ↑j < W₁.n + 4 := j.isLt
        have hj2 : (⟨↑j, hj⟩ : Fin (W₁.n + 4)) = j := Fin.ext rfl
        show (if W₁.vert j ∧ c.1 < W₁.x j ∧ W₁.lo j ≤ c.2 ∧ c.2 < W₁.hi j then (1 : ZMod 2) else 0) =
          if h : ↑j < W₁.n + 4 then
            (if W₁.vert ⟨↑j, h⟩ ∧ c.1 < W₁.x ⟨↑j, h⟩ ∧ W₁.lo ⟨↑j, h⟩ ≤ c.2 ∧ c.2 < W₁.hi ⟨↑j, h⟩
              then (1 : ZMod 2) else 0)
          else 0
        rw [dif_pos hj, hj2]
      have hfW₂ : ∀ j : Fin (W₂.n + 4),
          (if W₂.vert j ∧ c.1 < W₂.x j ∧ W₂.lo j ≤ c.2 ∧ c.2 < W₂.hi j then (1 : ZMod 2) else 0) =
            fW₂ ↑j := by
        intro j
        have hj : ↑j < W₂.n + 4 := j.isLt
        have hj2 : (⟨↑j, hj⟩ : Fin (W₂.n + 4)) = j := Fin.ext rfl
        show (if W₂.vert j ∧ c.1 < W₂.x j ∧ W₂.lo j ≤ c.2 ∧ c.2 < W₂.hi j then (1 : ZMod 2) else 0) =
          if h : ↑j < W₂.n + 4 then
            (if W₂.vert ⟨↑j, h⟩ ∧ c.1 < W₂.x ⟨↑j, h⟩ ∧ W₂.lo ⟨↑j, h⟩ ≤ c.2 ∧ c.2 < W₂.hi ⟨↑j, h⟩
              then (1 : ZMod 2) else 0)
          else 0
        rw [dif_pos hj, hj2]
      have hsumW : W.p2 c = ∑ i ∈ Finset.range (W.n + 4), fW i := by
        show (∑ i : Fin (W.n + 4),
            (if W.vert i ∧ c.1 < W.x i ∧ W.lo i ≤ c.2 ∧ c.2 < W.hi i then (1 : ZMod 2) else 0)) = _
        rw [Finset.sum_congr rfl (fun i _ => hfW i)]
        exact Fin.sum_univ_eq_sum_range fW (W.n + 4)
      have hsumW₁ : W₁.p2 c = ∑ i ∈ Finset.range (W₁.n + 4), fW₁ i := by
        show (∑ i : Fin (W₁.n + 4),
            (if W₁.vert i ∧ c.1 < W₁.x i ∧ W₁.lo i ≤ c.2 ∧ c.2 < W₁.hi i then (1 : ZMod 2) else 0)) = _
        rw [Finset.sum_congr rfl (fun i _ => hfW₁ i)]
        exact Fin.sum_univ_eq_sum_range fW₁ (W₁.n + 4)
      have hsumW₂ : W₂.p2 c = ∑ i ∈ Finset.range (W₂.n + 4), fW₂ i := by
        show (∑ i : Fin (W₂.n + 4),
            (if W₂.vert i ∧ c.1 < W₂.x i ∧ W₂.lo i ≤ c.2 ∧ c.2 < W₂.hi i then (1 : ZMod 2) else 0)) = _
        rw [Finset.sum_congr rfl (fun i _ => hfW₂ i)]
        exact Fin.sum_univ_eq_sum_range fW₂ (W₂.n + 4)
      have htail1 : ∀ j : ℕ, j < (k : ℕ) - 1 → fW₁ j = fW (j + 1) := by
        intro j hj
        have hjW : j + 1 < W.n + 4 := by omega
        have hjW₁ : j < W₁.n + 4 := by rw [hW1n]; omega
        have e1 : W₁.v ⟨j, hjW₁⟩ = W.v ⟨j + 1, hjW⟩ := rfl
        have eS1 : (⟨j, hjW₁⟩ + 1 : Fin (W₁.n + 4)) = ⟨j + 1, by omega⟩ := by
          apply Fin.ext
          rw [Fin.val_add, Fin.val_one']
          have h1m : 1 % (W₁.n + 4) = 1 := Nat.mod_eq_of_lt (by rw [hW1n]; omega)
          have h2m : (j + 1) % (W₁.n + 4) = j + 1 := Nat.mod_eq_of_lt (by rw [hW1n]; omega)
          rw [h1m, h2m]
        have eS2 : (⟨j + 1, hjW⟩ + 1 : Fin (W.n + 4)) = ⟨j + 2, by omega⟩ := by
          apply Fin.ext
          rw [Fin.val_add, Fin.val_one']
          have h1m : 1 % (W.n + 4) = 1 := Nat.mod_eq_of_lt (by omega)
          have h2m : (j + 1 + 1) % (W.n + 4) = j + 2 := Nat.mod_eq_of_lt (by omega)
          rw [h1m, h2m]
        have e2 : W₁.v ⟨j + 1, by omega⟩ = W.v ⟨j + 2, by omega⟩ := rfl
        show (if h : j < W₁.n + 4 then
            (if W₁.vert ⟨j, h⟩ ∧ c.1 < W₁.x ⟨j, h⟩ ∧ W₁.lo ⟨j, h⟩ ≤ c.2 ∧ c.2 < W₁.hi ⟨j, h⟩
              then (1 : ZMod 2) else 0) else 0) =
          (if h : j + 1 < W.n + 4 then
            (if W.vert ⟨j + 1, h⟩ ∧ c.1 < W.x ⟨j + 1, h⟩ ∧ W.lo ⟨j + 1, h⟩ ≤ c.2 ∧ c.2 < W.hi ⟨j + 1, h⟩
              then (1 : ZMod 2) else 0) else 0)
        rw [dif_pos hjW₁, dif_pos hjW]
        have hiff : (W₁.vert ⟨j, hjW₁⟩ ∧ c.1 < W₁.x ⟨j, hjW₁⟩ ∧ W₁.lo ⟨j, hjW₁⟩ ≤ c.2 ∧
            c.2 < W₁.hi ⟨j, hjW₁⟩) ↔
            (W.vert ⟨j + 1, hjW⟩ ∧ c.1 < W.x ⟨j + 1, hjW⟩ ∧ W.lo ⟨j + 1, hjW⟩ ≤ c.2 ∧
            c.2 < W.hi ⟨j + 1, hjW⟩) := by
          show (((W₁.v (⟨j, hjW₁⟩ + 1)).1 = (W₁.v ⟨j, hjW₁⟩).1) ∧ c.1 < (W₁.v ⟨j, hjW₁⟩).1 ∧
              min ((W₁.v ⟨j, hjW₁⟩).2) ((W₁.v (⟨j, hjW₁⟩ + 1)).2) ≤ c.2 ∧
              c.2 < max ((W₁.v ⟨j, hjW₁⟩).2) ((W₁.v (⟨j, hjW₁⟩ + 1)).2)) ↔
            (((W.v (⟨j + 1, hjW⟩ + 1)).1 = (W.v ⟨j + 1, hjW⟩).1) ∧ c.1 < (W.v ⟨j + 1, hjW⟩).1 ∧
              min ((W.v ⟨j + 1, hjW⟩).2) ((W.v (⟨j + 1, hjW⟩ + 1)).2) ≤ c.2 ∧
              c.2 < max ((W.v ⟨j + 1, hjW⟩).2) ((W.v (⟨j + 1, hjW⟩ + 1)).2))
          rw [eS1, eS2, e1, e2]
        exact if_congr hiff rfl rfl
      have hchord1 : fW₁ ((k : ℕ) - 1) =
          (if c.1 < x₀ + 2 ∧ ym - 2 ≤ c.2 ∧ c.2 < ym then (1 : ZMod 2) else 0) := by
        have hlt : (k : ℕ) - 1 < W₁.n + 4 := by rw [hW1n]; omega
        show (if h : (k : ℕ) - 1 < W₁.n + 4 then
            (if W₁.vert ⟨(k : ℕ) - 1, h⟩ ∧ c.1 < W₁.x ⟨(k : ℕ) - 1, h⟩ ∧ W₁.lo ⟨(k : ℕ) - 1, h⟩ ≤ c.2 ∧
              c.2 < W₁.hi ⟨(k : ℕ) - 1, h⟩ then (1 : ZMod 2) else 0) else 0) = _
        rw [dif_pos hlt]
        have elast : (⟨(k : ℕ) - 1, hlt⟩ : Fin (W₁.n + 4)) = Fin.last ((k : ℕ) - 4 + 3) := by
          apply Fin.ext
          show (k : ℕ) - 1 = ((Fin.last ((k : ℕ) - 4 + 3)) : ℕ)
          rw [Fin.val_last]
          omega
        have hvert : W₁.vert ⟨(k : ℕ) - 1, hlt⟩ := by
          show (W₁.v (⟨(k : ℕ) - 1, hlt⟩ + 1)).1 = (W₁.v ⟨(k : ℕ) - 1, hlt⟩).1
          rw [elast, hW₁succ_last, hW₁zero, hW₁last]
        have hx1 : W₁.x ⟨(k : ℕ) - 1, hlt⟩ = x₀ + 2 := by
          rw [elast]
          exact congrArg Prod.fst hW₁last
        have hlo1 : W₁.lo ⟨(k : ℕ) - 1, hlt⟩ = ym - 2 := by
          show min ((W₁.v ⟨(k : ℕ) - 1, hlt⟩).2) ((W₁.v (⟨(k : ℕ) - 1, hlt⟩ + 1)).2) = ym - 2
          rw [elast, hW₁succ_last, hW₁zero, hW₁last]
          exact min_eq_left (by omega)
        have hhi1 : W₁.hi ⟨(k : ℕ) - 1, hlt⟩ = ym := by
          show max ((W₁.v ⟨(k : ℕ) - 1, hlt⟩).2) ((W₁.v (⟨(k : ℕ) - 1, hlt⟩ + 1)).2) = ym
          rw [elast, hW₁succ_last, hW₁zero, hW₁last]
          exact max_eq_right (by omega)
        have hiff : (W₁.vert ⟨(k : ℕ) - 1, hlt⟩ ∧ c.1 < W₁.x ⟨(k : ℕ) - 1, hlt⟩ ∧
            W₁.lo ⟨(k : ℕ) - 1, hlt⟩ ≤ c.2 ∧ c.2 < W₁.hi ⟨(k : ℕ) - 1, hlt⟩) ↔
            (c.1 < x₀ + 2 ∧ ym - 2 ≤ c.2 ∧ c.2 < ym) := by
          rw [hx1, hlo1, hhi1, show W₁.vert ⟨(k : ℕ) - 1, hlt⟩ = True from eq_true hvert, true_and]
        exact if_congr hiff rfl rfl
      have htail2 : ∀ j : ℕ, j < W.n + 4 - (k : ℕ) → fW₂ j = fW (j + (k : ℕ)) := by
        intro j hj
        have hjW : j + (k : ℕ) < W.n + 4 := by omega
        have hjW₂ : j < W₂.n + 4 := by rw [hW2n]; omega
        have e1 : W₂.v ⟨j, hjW₂⟩ = W.v ⟨j + (k : ℕ), hjW⟩ := by
          show W.v ⟨((⟨j, hjW₂⟩ : Fin (W₂.n + 4)).val + k) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ =
            W.v ⟨j + (k : ℕ), hjW⟩
          have e1a : (⟨((⟨j, hjW₂⟩ : Fin (W₂.n + 4)).val + k) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ :
              Fin (W.n + 4)) = ⟨j + (k : ℕ), hjW⟩ := by
            apply Fin.ext
            show ((⟨j, hjW₂⟩ : Fin (W₂.n + 4)).val + k) % (W.n + 4) = j + (k : ℕ)
            have hv1 : ((⟨j, hjW₂⟩ : Fin (W₂.n + 4)) : ℕ) = j := rfl
            rw [hv1]
            exact Nat.mod_eq_of_lt hjW
          rw [e1a]
        have eS1 : (⟨j, hjW₂⟩ + 1 : Fin (W₂.n + 4)) = ⟨j + 1, by omega⟩ := by
          apply Fin.ext
          rw [Fin.val_add, Fin.val_one']
          have h1m : 1 % (W₂.n + 4) = 1 := Nat.mod_eq_of_lt (by rw [hW2n]; omega)
          have h2m : (j + 1) % (W₂.n + 4) = j + 1 := Nat.mod_eq_of_lt (by rw [hW2n]; omega)
          rw [h1m, h2m]
        have eS2 : (⟨j + (k : ℕ), hjW⟩ + 1 : Fin (W.n + 4)) =
            ⟨(j + (k : ℕ) + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ := by
          apply Fin.ext
          rw [Fin.val_add, Fin.val_one']
          have h1m : 1 % (W.n + 4) = 1 := Nat.mod_eq_of_lt (by omega)
          rw [h1m]
        have e2 : W₂.v ⟨j + 1, by omega⟩ = W.v ⟨(j + (k : ℕ) + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ := by
          show W.v ⟨((⟨j + 1, by omega⟩ : Fin (W₂.n + 4)).val + k) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ = _
          have e2b : (⟨((⟨j + 1, by omega⟩ : Fin (W₂.n + 4)).val + k) % (W.n + 4),
              Nat.mod_lt _ (by omega)⟩ : Fin (W.n + 4)) =
              ⟨(j + (k : ℕ) + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ := by
            apply Fin.ext
            show ((⟨j + 1, by omega⟩ : Fin (W₂.n + 4)).val + k) % (W.n + 4) =
              (j + (k : ℕ) + 1) % (W.n + 4)
            have hv1 : ((⟨j + 1, by omega⟩ : Fin (W₂.n + 4)) : ℕ) = j + 1 := rfl
            rw [hv1]
            have hsum : j + 1 + k = j + (k : ℕ) + 1 := by omega
            rw [hsum]
          rw [e2b]
        show (if h : j < W₂.n + 4 then
            (if W₂.vert ⟨j, h⟩ ∧ c.1 < W₂.x ⟨j, h⟩ ∧ W₂.lo ⟨j, h⟩ ≤ c.2 ∧ c.2 < W₂.hi ⟨j, h⟩
              then (1 : ZMod 2) else 0) else 0) =
          (if h : j + (k : ℕ) < W.n + 4 then
            (if W.vert ⟨j + (k : ℕ), h⟩ ∧ c.1 < W.x ⟨j + (k : ℕ), h⟩ ∧ W.lo ⟨j + (k : ℕ), h⟩ ≤ c.2 ∧
              c.2 < W.hi ⟨j + (k : ℕ), h⟩ then (1 : ZMod 2) else 0) else 0)
        rw [dif_pos hjW₂, dif_pos hjW]
        have hiff : (W₂.vert ⟨j, hjW₂⟩ ∧ c.1 < W₂.x ⟨j, hjW₂⟩ ∧ W₂.lo ⟨j, hjW₂⟩ ≤ c.2 ∧
            c.2 < W₂.hi ⟨j, hjW₂⟩) ↔
            (W.vert ⟨j + (k : ℕ), hjW⟩ ∧ c.1 < W.x ⟨j + (k : ℕ), hjW⟩ ∧ W.lo ⟨j + (k : ℕ), hjW⟩ ≤ c.2 ∧
            c.2 < W.hi ⟨j + (k : ℕ), hjW⟩) := by
          show (((W₂.v (⟨j, hjW₂⟩ + 1)).1 = (W₂.v ⟨j, hjW₂⟩).1) ∧ c.1 < (W₂.v ⟨j, hjW₂⟩).1 ∧
              min ((W₂.v ⟨j, hjW₂⟩).2) ((W₂.v (⟨j, hjW₂⟩ + 1)).2) ≤ c.2 ∧
              c.2 < max ((W₂.v ⟨j, hjW₂⟩).2) ((W₂.v (⟨j, hjW₂⟩ + 1)).2)) ↔
            (((W.v (⟨j + (k : ℕ), hjW⟩ + 1)).1 = (W.v ⟨j + (k : ℕ), hjW⟩).1) ∧
              c.1 < (W.v ⟨j + (k : ℕ), hjW⟩).1 ∧
              min ((W.v ⟨j + (k : ℕ), hjW⟩).2) ((W.v (⟨j + (k : ℕ), hjW⟩ + 1)).2) ≤ c.2 ∧
              c.2 < max ((W.v ⟨j + (k : ℕ), hjW⟩).2) ((W.v (⟨j + (k : ℕ), hjW⟩ + 1)).2))
          rw [eS1, eS2, e1, e2]
        exact if_congr hiff rfl rfl
      have hwrap2 : fW₂ (W.n + 4 - (k : ℕ)) = fW 0 := by
        have hj : W.n + 4 - (k : ℕ) < W₂.n + 4 := by rw [hW2n]; omega
        have h0lt : 0 < W.n + 4 := by omega
        show (if h : W.n + 4 - (k : ℕ) < W₂.n + 4 then
            (if W₂.vert ⟨W.n + 4 - (k : ℕ), h⟩ ∧ c.1 < W₂.x ⟨W.n + 4 - (k : ℕ), h⟩ ∧
              W₂.lo ⟨W.n + 4 - (k : ℕ), h⟩ ≤ c.2 ∧ c.2 < W₂.hi ⟨W.n + 4 - (k : ℕ), h⟩
              then (1 : ZMod 2) else 0) else 0) =
          (if h : 0 < W.n + 4 then
            (if W.vert ⟨0, h⟩ ∧ c.1 < W.x ⟨0, h⟩ ∧ W.lo ⟨0, h⟩ ≤ c.2 ∧ c.2 < W.hi ⟨0, h⟩
              then (1 : ZMod 2) else 0) else 0)
        rw [dif_pos hj, dif_pos h0lt]
        have e1 : W₂.v ⟨W.n + 4 - (k : ℕ), hj⟩ = W.v ⟨0, h0lt⟩ := by
          show W.v ⟨((⟨W.n + 4 - (k : ℕ), hj⟩ : Fin (W₂.n + 4)).val + k) % (W.n + 4),
              Nat.mod_lt _ (by omega)⟩ = W.v ⟨0, h0lt⟩
          have e1a : (⟨((⟨W.n + 4 - (k : ℕ), hj⟩ : Fin (W₂.n + 4)).val + k) % (W.n + 4),
              Nat.mod_lt _ (by omega)⟩ : Fin (W.n + 4)) = ⟨0, h0lt⟩ := by
            apply Fin.ext
            show ((⟨W.n + 4 - (k : ℕ), hj⟩ : Fin (W₂.n + 4)).val + k) % (W.n + 4) = (0 : ℕ)
            have hv1 : ((⟨W.n + 4 - (k : ℕ), hj⟩ : Fin (W₂.n + 4)) : ℕ) = W.n + 4 - (k : ℕ) := rfl
            rw [hv1]
            have e : W.n + 4 - (k : ℕ) + k = W.n + 4 := by omega
            rw [e, Nat.mod_self]
          rw [e1a]
        have eS1 : (⟨W.n + 4 - (k : ℕ), hj⟩ + 1 : Fin (W₂.n + 4)) =
            ⟨W.n + 5 - (k : ℕ), by omega⟩ := by
          apply Fin.ext
          rw [Fin.val_add, Fin.val_one']
          have h1m : 1 % (W₂.n + 4) = 1 := Nat.mod_eq_of_lt (by rw [hW2n]; omega)
          have h2m : (W.n + 4 - (k : ℕ) + 1) % (W₂.n + 4) = W.n + 5 - (k : ℕ) := by
            rw [hW2n]
            have e : W.n + 4 - (k : ℕ) + 1 = W.n + 5 - (k : ℕ) := by omega
            rw [e]
            exact Nat.mod_eq_of_lt (by omega)
          rw [h1m, h2m]
        have eS2 : (⟨0, h0lt⟩ + 1 : Fin (W.n + 4)) = 1 := by
          apply Fin.ext
          rw [Fin.val_add, Fin.val_one']
          have h1m : 1 % (W.n + 4) = 1 := Nat.mod_eq_of_lt (by omega)
          rw [h1m]
          exact Nat.mod_eq_of_lt (show (1 : ℕ) < W.n + 4 by omega)
        have e2 : W₂.v ⟨W.n + 5 - (k : ℕ), by omega⟩ = W.v 1 := by
          show W.v ⟨((⟨W.n + 5 - (k : ℕ), by omega⟩ : Fin (W₂.n + 4)).val + k) % (W.n + 4),
              Nat.mod_lt _ (by omega)⟩ = W.v 1
          have e2b : (⟨((⟨W.n + 5 - (k : ℕ), by omega⟩ : Fin (W₂.n + 4)).val + k) % (W.n + 4),
              Nat.mod_lt _ (by omega)⟩ : Fin (W.n + 4)) = 1 := by
            apply Fin.ext
            show ((⟨W.n + 5 - (k : ℕ), by omega⟩ : Fin (W₂.n + 4)).val + k) % (W.n + 4) =
              ((1 : Fin (W.n + 4)) : ℕ)
            have hv1 : ((⟨W.n + 5 - (k : ℕ), by omega⟩ : Fin (W₂.n + 4)) : ℕ) = W.n + 5 - (k : ℕ) := rfl
            rw [hv1, val_one_fin]
            have e : W.n + 5 - (k : ℕ) + k = W.n + 5 := by omega
            rw [e]
            have e2 : W.n + 5 = 1 + (W.n + 4) := by omega
            rw [e2, Nat.add_mod_right]
            exact Nat.mod_eq_of_lt (by omega)
          rw [e2b]
        have hiff : (W₂.vert ⟨W.n + 4 - (k : ℕ), hj⟩ ∧ c.1 < W₂.x ⟨W.n + 4 - (k : ℕ), hj⟩ ∧
            W₂.lo ⟨W.n + 4 - (k : ℕ), hj⟩ ≤ c.2 ∧ c.2 < W₂.hi ⟨W.n + 4 - (k : ℕ), hj⟩) ↔
            (W.vert ⟨0, h0lt⟩ ∧ c.1 < W.x ⟨0, h0lt⟩ ∧ W.lo ⟨0, h0lt⟩ ≤ c.2 ∧ c.2 < W.hi ⟨0, h0lt⟩) := by
          show (((W₂.v (⟨W.n + 4 - (k : ℕ), hj⟩ + 1)).1 = (W₂.v ⟨W.n + 4 - (k : ℕ), hj⟩).1) ∧
              c.1 < (W₂.v ⟨W.n + 4 - (k : ℕ), hj⟩).1 ∧
              min ((W₂.v ⟨W.n + 4 - (k : ℕ), hj⟩).2) ((W₂.v (⟨W.n + 4 - (k : ℕ), hj⟩ + 1)).2) ≤ c.2 ∧
              c.2 < max ((W₂.v ⟨W.n + 4 - (k : ℕ), hj⟩).2) ((W₂.v (⟨W.n + 4 - (k : ℕ), hj⟩ + 1)).2)) ↔
            (((W.v (⟨0, h0lt⟩ + 1)).1 = (W.v ⟨0, h0lt⟩).1) ∧ c.1 < (W.v ⟨0, h0lt⟩).1 ∧
              min ((W.v ⟨0, h0lt⟩).2) ((W.v (⟨0, h0lt⟩ + 1)).2) ≤ c.2 ∧
              c.2 < max ((W.v ⟨0, h0lt⟩).2) ((W.v (⟨0, h0lt⟩ + 1)).2))
          rw [eS1, eS2, e1, e2]
        exact if_congr hiff rfl rfl
      have hchord2 : fW₂ (W.n + 5 - (k : ℕ)) =
          (if c.1 < x₀ + 2 ∧ ym - 2 ≤ c.2 ∧ c.2 < ym then (1 : ZMod 2) else 0) := by
        have hlt : W.n + 5 - (k : ℕ) < W₂.n + 4 := by rw [hW2n]; omega
        show (if h : W.n + 5 - (k : ℕ) < W₂.n + 4 then
            (if W₂.vert ⟨W.n + 5 - (k : ℕ), h⟩ ∧ c.1 < W₂.x ⟨W.n + 5 - (k : ℕ), h⟩ ∧
              W₂.lo ⟨W.n + 5 - (k : ℕ), h⟩ ≤ c.2 ∧ c.2 < W₂.hi ⟨W.n + 5 - (k : ℕ), h⟩
              then (1 : ZMod 2) else 0) else 0) = _
        rw [dif_pos hlt]
        have elast : (⟨W.n + 5 - (k : ℕ), hlt⟩ : Fin (W₂.n + 4)) = Fin.last (W.n + 2 - (k : ℕ) + 3) := by
          apply Fin.ext
          show W.n + 5 - (k : ℕ) = ((Fin.last (W.n + 2 - (k : ℕ) + 3)) : ℕ)
          rw [Fin.val_last]
          omega
        have hvert : W₂.vert ⟨W.n + 5 - (k : ℕ), hlt⟩ := by
          show (W₂.v (⟨W.n + 5 - (k : ℕ), hlt⟩ + 1)).1 = (W₂.v ⟨W.n + 5 - (k : ℕ), hlt⟩).1
          rw [elast, hW₂succ_last, hW₂zero, hW₂last]
        have hx1 : W₂.x ⟨W.n + 5 - (k : ℕ), hlt⟩ = x₀ + 2 := by
          rw [elast]
          exact congrArg Prod.fst hW₂last
        have hlo1 : W₂.lo ⟨W.n + 5 - (k : ℕ), hlt⟩ = ym - 2 := by
          show min ((W₂.v ⟨W.n + 5 - (k : ℕ), hlt⟩).2) ((W₂.v (⟨W.n + 5 - (k : ℕ), hlt⟩ + 1)).2) = ym - 2
          rw [elast, hW₂succ_last, hW₂zero, hW₂last]
          exact min_eq_right (by omega)
        have hhi1 : W₂.hi ⟨W.n + 5 - (k : ℕ), hlt⟩ = ym := by
          show max ((W₂.v ⟨W.n + 5 - (k : ℕ), hlt⟩).2) ((W₂.v (⟨W.n + 5 - (k : ℕ), hlt⟩ + 1)).2) = ym
          rw [elast, hW₂succ_last, hW₂zero, hW₂last]
          exact max_eq_left (by omega)
        have hiff : (W₂.vert ⟨W.n + 5 - (k : ℕ), hlt⟩ ∧ c.1 < W₂.x ⟨W.n + 5 - (k : ℕ), hlt⟩ ∧
            W₂.lo ⟨W.n + 5 - (k : ℕ), hlt⟩ ≤ c.2 ∧ c.2 < W₂.hi ⟨W.n + 5 - (k : ℕ), hlt⟩) ↔
            (c.1 < x₀ + 2 ∧ ym - 2 ≤ c.2 ∧ c.2 < ym) := by
          rw [hx1, hlo1, hhi1, show W₂.vert ⟨W.n + 5 - (k : ℕ), hlt⟩ = True from eq_true hvert, true_and]
        exact if_congr hiff rfl rfl
      have hW2 : W.p2 c = fW 0 + (∑ i ∈ Finset.range ((k : ℕ) - 1), fW (i + 1)) +
          (∑ i ∈ Finset.range (W.n + 4 - (k : ℕ)), fW (i + (k : ℕ))) := by
        rw [hsumW]
        have hsplit : W.n + 4 = (1 + ((k : ℕ) - 1)) + (W.n + 4 - (k : ℕ)) := by omega
        rw [show Finset.range (W.n + 4) = Finset.range ((1 + ((k : ℕ) - 1)) + (W.n + 4 - (k : ℕ))) from
          congrArg Finset.range hsplit, Finset.sum_range_add]
        have e1 : ∑ i ∈ Finset.range (1 + ((k : ℕ) - 1)), fW i =
            fW 0 + ∑ i ∈ Finset.range ((k : ℕ) - 1), fW (i + 1) := by
          have e : 1 + ((k : ℕ) - 1) = (k : ℕ) - 1 + 1 := by omega
          rw [e, Finset.sum_range_succ', add_comm]
        have e2 : (∑ i ∈ Finset.range (W.n + 4 - (k : ℕ)), fW (1 + ((k : ℕ) - 1) + i)) =
            ∑ i ∈ Finset.range (W.n + 4 - (k : ℕ)), fW (i + (k : ℕ)) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [show 1 + ((k : ℕ) - 1) + i = i + (k : ℕ) by omega]
        rw [e1, e2]
      have hW₁2 : W₁.p2 c = (∑ i ∈ Finset.range ((k : ℕ) - 1), fW₁ i) + fW₁ ((k : ℕ) - 1) := by
        rw [hsumW₁]
        have hm : W₁.n + 4 = (k : ℕ) - 1 + 1 := by rw [hW1n]; omega
        rw [hm, Finset.sum_range_succ]
      have hW₂2 : W₂.p2 c = (∑ i ∈ Finset.range (W.n + 4 - (k : ℕ)), fW₂ i) +
          fW₂ (W.n + 4 - (k : ℕ)) + fW₂ (W.n + 5 - (k : ℕ)) := by
        rw [hsumW₂]
        have hm : W₂.n + 4 = (W.n + 4 - (k : ℕ)) + 1 + 1 := by rw [hW2n]; omega
        rw [hm, Finset.sum_range_succ, Finset.sum_range_succ]
        have e : (W.n + 4 - (k : ℕ)) + 1 = W.n + 5 - (k : ℕ) := by omega
        rw [e]
      have hshared1 : (∑ i ∈ Finset.range ((k : ℕ) - 1), fW₁ i) =
          (∑ i ∈ Finset.range ((k : ℕ) - 1), fW (i + 1)) :=
        Finset.sum_congr rfl (fun j hj => htail1 j (Finset.mem_range.mp hj))
      have hshared2 : (∑ i ∈ Finset.range (W.n + 4 - (k : ℕ)), fW₂ i) =
          (∑ i ∈ Finset.range (W.n + 4 - (k : ℕ)), fW (i + (k : ℕ))) :=
        Finset.sum_congr rfl (fun j hj => htail2 j (Finset.mem_range.mp hj))
      rw [hW2, hW₁2, hW₂2, hshared1, hshared2, hchord1, hwrap2, hchord2]
      have hclose : ∀ s1 s2 a ch : ZMod 2, a + s1 + s2 = (s1 + ch) + ((s2 + a) + ch) := by
        intro s1 s2 a ch
        rcases hkey s1 with hs | hs <;> rcases hkey s2 with hs2 | hs2 <;>
          rcases hkey a with ha | ha <;> rcases hkey ch with hc | hc <;>
          rw [hs, hs2, ha, hc] <;> decide
      exact hclose _ _ _ _
    -- (b) boundary relations
    have hB1 : ∀ c : Cell, c ∈ W₁.boundary → c ∈ W.boundary ∨ c = (x₀ + 2, ym - 1) := by
      intro c hc
      rw [W₁.mem_boundary c] at hc
      rcases hc with ⟨j, hj⟩ | ⟨j, hj⟩
      · left
        rw [← hj]
        exact W.vertex_mem_boundary _
      · by_cases hjl : j = Fin.last ((k : ℕ) - 4 + 3)
        · right
          have hje : W₁.mid j = (x₀ + 2, ym - 1) := by
            rw [hjl]
            show midPt (W₁.v (Fin.last ((k : ℕ) - 4 + 3))) (W₁.v (Fin.last ((k : ℕ) - 4 + 3) + 1)) =
              (x₀ + 2, ym - 1)
            rw [hW₁succ_last, hW₁zero, hW₁last]
            simp only [midPt, Prod.mk.injEq]
            constructor <;> omega
          exact hj.symm.trans hje
        · left
          have hm : W₁.mid j = W.mid ⟨j.val + 1, by omega⟩ := hmid1W j hjl
          rw [hm] at hj
          rw [← hj]
          exact W.mid_mem_boundary _
    have hB2 : ∀ c : Cell, c ∈ W₂.boundary → c ∈ W.boundary ∨ c = (x₀ + 2, ym - 1) := by
      intro c hc
      rw [W₂.mem_boundary c] at hc
      rcases hc with ⟨j, hj⟩ | ⟨j, hj⟩
      · left
        rw [← hj]
        exact W.vertex_mem_boundary _
      · by_cases hjl : j = Fin.last (W.n + 2 - (k : ℕ) + 3)
        · right
          have hje : W₂.mid j = (x₀ + 2, ym - 1) := by
            rw [hjl]
            show midPt (W₂.v (Fin.last (W.n + 2 - (k : ℕ) + 3)))
              (W₂.v (Fin.last (W.n + 2 - (k : ℕ) + 3) + 1)) = (x₀ + 2, ym - 1)
            rw [hW₂succ_last, hW₂zero, hW₂last]
            simp only [midPt, Prod.mk.injEq]
            constructor <;> omega
          exact hj.symm.trans hje
        · left
          have hm : W₂.mid j = W.mid ⟨(j.val + k) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ :=
            hmid2W j hjl
          rw [hm] at hj
          rw [← hj]
          exact W.mid_mem_boundary _
    have hBW : ∀ c : Cell, c ∈ W.boundary → c ∈ W₁.boundary ∨ c ∈ W₂.boundary := by
      intro c hc
      rw [W.mem_boundary c] at hc
      rcases hc with ⟨i, hi⟩ | ⟨i, hi⟩
      · by_cases hcase : 1 ≤ (i : ℕ) ∧ (i : ℕ) ≤ (k : ℕ)
        · left
          have hve : W₁.v ⟨(i : ℕ) - 1, by omega⟩ = c := by
            show W.v ⟨(⟨(i : ℕ) - 1, by omega⟩ : Fin ((k : ℕ) - 4 + 4)).val + 1, by omega⟩ = c
            have e : (⟨(⟨(i : ℕ) - 1, by omega⟩ : Fin ((k : ℕ) - 4 + 4)).val + 1, by omega⟩ :
                Fin (W.n + 4)) = i := by
              apply Fin.ext
              show (⟨(i : ℕ) - 1, by omega⟩ : Fin ((k : ℕ) - 4 + 4)).val + 1 = ↑i
              have hv1 : ((⟨(i : ℕ) - 1, by omega⟩ : Fin ((k : ℕ) - 4 + 4)) : ℕ) = (i : ℕ) - 1 := rfl
              rw [hv1]
              omega
            rw [e]
            exact hi
          rw [← hve]
          exact W₁.vertex_mem_boundary _
        · right
          push_neg at hcase
          have hi2 : (i : ℕ) = 0 ∨ (k : ℕ) < (i : ℕ) := by
            by_cases h1 : 1 ≤ (i : ℕ)
            · exact Or.inr (hcase h1)
            · exact Or.inl (by omega)
          rcases hi2 with hi0 | hik
          · have hve : W₂.v ⟨W.n + 4 - (k : ℕ), by omega⟩ = c := by
              show W.v ⟨((⟨W.n + 4 - (k : ℕ), by omega⟩ : Fin (W₂.n + 4)).val + k) % (W.n + 4),
                  Nat.mod_lt _ (by omega)⟩ = c
              have e : (⟨((⟨W.n + 4 - (k : ℕ), by omega⟩ : Fin (W₂.n + 4)).val + k) % (W.n + 4),
                  Nat.mod_lt _ (by omega)⟩ : Fin (W.n + 4)) = i := by
                apply Fin.ext
                show ((⟨W.n + 4 - (k : ℕ), by omega⟩ : Fin (W₂.n + 4)).val + k) % (W.n + 4) = ↑i
                have hv1 : ((⟨W.n + 4 - (k : ℕ), by omega⟩ : Fin (W₂.n + 4)) : ℕ) =
                  W.n + 4 - (k : ℕ) := rfl
                rw [hv1, hi0]
                have e2 : W.n + 4 - (k : ℕ) + k = W.n + 4 := by omega
                rw [e2, Nat.mod_self]
              rw [e]
              exact hi
            rw [← hve]
            exact W₂.vertex_mem_boundary _
          · have hve : W₂.v ⟨(i : ℕ) - (k : ℕ), by omega⟩ = c := by
              show W.v ⟨((⟨(i : ℕ) - (k : ℕ), by omega⟩ : Fin (W₂.n + 4)).val + k) % (W.n + 4),
                  Nat.mod_lt _ (by omega)⟩ = c
              have e : (⟨((⟨(i : ℕ) - (k : ℕ), by omega⟩ : Fin (W₂.n + 4)).val + k) % (W.n + 4),
                  Nat.mod_lt _ (by omega)⟩ : Fin (W.n + 4)) = i := by
                apply Fin.ext
                show ((⟨(i : ℕ) - (k : ℕ), by omega⟩ : Fin (W₂.n + 4)).val + k) % (W.n + 4) = ↑i
                have hv1 : ((⟨(i : ℕ) - (k : ℕ), by omega⟩ : Fin (W₂.n + 4)) : ℕ) =
                  (i : ℕ) - (k : ℕ) := rfl
                rw [hv1]
                have e2 : (i : ℕ) - (k : ℕ) + k = i := by omega
                rw [e2]
                exact Nat.mod_eq_of_lt i.isLt
              rw [e]
              exact hi
            rw [← hve]
            exact W₂.vertex_mem_boundary _
      · by_cases hcase : 1 ≤ (i : ℕ) ∧ (i : ℕ) ≤ (k : ℕ) - 1
        · left
          have hme : W₁.mid ⟨(i : ℕ) - 1, by omega⟩ = c := by
            rw [hmid1W _ (by
              intro h
              have hv := congrArg Fin.val h
              rw [Fin.val_last] at hv
              have hv1 : ((⟨(i : ℕ) - 1, by omega⟩ : Fin ((k : ℕ) - 4 + 4)) : ℕ) = (i : ℕ) - 1 := rfl
              rw [hv1] at hv
              omega)]
            have e : (⟨(⟨(i : ℕ) - 1, by omega⟩ : Fin ((k : ℕ) - 4 + 4)).val + 1, by omega⟩ :
                Fin (W.n + 4)) = i := by
              apply Fin.ext
              show (⟨(i : ℕ) - 1, by omega⟩ : Fin ((k : ℕ) - 4 + 4)).val + 1 = ↑i
              have hv1 : ((⟨(i : ℕ) - 1, by omega⟩ : Fin ((k : ℕ) - 4 + 4)) : ℕ) = (i : ℕ) - 1 := rfl
              rw [hv1]
              omega
            rw [e]
            exact hi
          rw [← hme]
          exact W₁.mid_mem_boundary _
        · right
          push_neg at hcase
          have hi2 : (i : ℕ) = 0 ∨ (k : ℕ) ≤ (i : ℕ) := by
            by_cases h1 : 1 ≤ (i : ℕ)
            · exact Or.inr (by have h2 := hcase h1; omega)
            · exact Or.inl (by omega)
          rcases hi2 with hi0 | hik
          · have hme : W₂.mid ⟨W.n + 4 - (k : ℕ), by omega⟩ = c := by
              rw [hmid2W _ (by
                intro h
                have hv := congrArg Fin.val h
                rw [Fin.val_last] at hv
                have hv1 : ((⟨W.n + 4 - (k : ℕ), by omega⟩ : Fin (W₂.n + 4)) : ℕ) =
                  W.n + 4 - (k : ℕ) := rfl
                rw [hv1] at hv
                omega)]
              have e : (⟨((⟨W.n + 4 - (k : ℕ), by omega⟩ : Fin (W₂.n + 4)).val + k) % (W.n + 4),
                  Nat.mod_lt _ (by omega)⟩ : Fin (W.n + 4)) = i := by
                apply Fin.ext
                show ((⟨W.n + 4 - (k : ℕ), by omega⟩ : Fin (W₂.n + 4)).val + k) % (W.n + 4) = ↑i
                have hv1 : ((⟨W.n + 4 - (k : ℕ), by omega⟩ : Fin (W₂.n + 4)) : ℕ) =
                  W.n + 4 - (k : ℕ) := rfl
                rw [hv1, hi0]
                have e2 : W.n + 4 - (k : ℕ) + k = W.n + 4 := by omega
                rw [e2, Nat.mod_self]
              rw [e]
              exact hi
            rw [← hme]
            exact W₂.mid_mem_boundary _
          · have hme : W₂.mid ⟨(i : ℕ) - (k : ℕ), by omega⟩ = c := by
              rw [hmid2W _ (by
                intro h
                have hv := congrArg Fin.val h
                rw [Fin.val_last] at hv
                have hv1 : ((⟨(i : ℕ) - (k : ℕ), by omega⟩ : Fin (W₂.n + 4)) : ℕ) =
                  (i : ℕ) - (k : ℕ) := rfl
                rw [hv1] at hv
                omega)]
              have e : (⟨((⟨(i : ℕ) - (k : ℕ), by omega⟩ : Fin (W₂.n + 4)).val + k) % (W.n + 4),
                  Nat.mod_lt _ (by omega)⟩ : Fin (W.n + 4)) = i := by
                apply Fin.ext
                show ((⟨(i : ℕ) - (k : ℕ), by omega⟩ : Fin (W₂.n + 4)).val + k) % (W.n + 4) = ↑i
                have hv1 : ((⟨(i : ℕ) - (k : ℕ), by omega⟩ : Fin (W₂.n + 4)) : ℕ) =
                  (i : ℕ) - (k : ℕ) := rfl
                rw [hv1]
                have e2 : (i : ℕ) - (k : ℕ) + k = i := by omega
                rw [e2]
                exact Nat.mod_eq_of_lt i.isLt
              rw [e]
              exact hi
            rw [← hme]
            exact W₂.mid_mem_boundary _
    have hm01 : (x₀ + 2, ym - 1) ∈ W₁.boundary := by
      have hm : W₁.mid (Fin.last ((k : ℕ) - 4 + 3)) = (x₀ + 2, ym - 1) := by
        show midPt (W₁.v (Fin.last ((k : ℕ) - 4 + 3))) (W₁.v (Fin.last ((k : ℕ) - 4 + 3) + 1)) =
          (x₀ + 2, ym - 1)
        rw [hW₁succ_last, hW₁zero, hW₁last]
        simp only [midPt, Prod.mk.injEq]
        constructor <;> omega
      rw [← hm]
      exact W₁.mid_mem_boundary _
    have hm02 : (x₀ + 2, ym - 1) ∈ W₂.boundary := by
      have hm : W₂.mid (Fin.last (W.n + 2 - (k : ℕ) + 3)) = (x₀ + 2, ym - 1) := by
        show midPt (W₂.v (Fin.last (W.n + 2 - (k : ℕ) + 3)))
          (W₂.v (Fin.last (W.n + 2 - (k : ℕ) + 3) + 1)) = (x₀ + 2, ym - 1)
        rw [hW₂succ_last, hW₂zero, hW₂last]
        simp only [midPt, Prod.mk.injEq]
        constructor <;> omega
      rw [← hm]
      exact W₂.mid_mem_boundary _
    have hm0W : (x₀ + 2, ym - 1) ∉ W.boundary := by
      rw [W.mem_boundary (x₀ + 2, ym - 1)]
      push_neg
      constructor
      · intro i hcon
        have hyk : (W.v i).2 = ym - 1 := congrArg Prod.snd hcon
        exact hpary1 (hyk ▸ W.parY i)
      · intro i hcon
        rcases W.mid_cases i _ hcon with ⟨hx, g1, g2 | g2⟩ | ⟨hy, g1, g2 | g2⟩
        · -- vertical, (W.v i).2 = ym - 2: vertex is r′, successor would be r
          have hvm : W.v i = (x₀ + 2, ym - 2) := by
            have hy2 : (W.v i).2 = ym - 2 := by
              have hc2 : ((x₀ + 2, ym - 1) : Cell).2 = ym - 1 := rfl
              omega
            exact Prod.ext g1.symm hy2
          have hik : i = k := hjr _ hvm
          have hy2 : (W.v (i + 1)).2 = ym := by
            have hm2 : ((x₀ + 2, ym - 1) : Cell).2 = ((W.v i).2 + (W.v (i + 1)).2) / 2 := by
              have hr : (W.mid i).2 = ((W.v i).2 + (W.v (i + 1)).2) / 2 := rfl
              rw [hcon] at hr
              exact hr
            have hc2 : ((x₀ + 2, ym - 1) : Cell).2 = ym - 1 := rfl
            have hvi2 : (W.v i).2 = ym - 2 := by omega
            rw [hvi2] at hm2
            have hst := W.step i
            omega
          have hvi1 : W.v (i + 1) = (x₀ + 2, ym) := by
            have hx2 : (W.v (i + 1)).1 = x₀ + 2 := by
              have hc1 : ((x₀ + 2, ym - 1) : Cell).1 = x₀ + 2 := rfl
              omega
            exact Prod.ext hx2 hy2
          have hk1 : i + 1 = 1 := hj1 _ hvi1
          rw [hik] at hk1
          have hv := congrArg Fin.val hk1
          have hv1 : ((k + 1 : Fin (W.n + 4)) : ℕ) = (k : ℕ) + 1 := by
            rw [Fin.val_add, Fin.val_one']
            have h1m : 1 % (W.n + 4) = 1 := Nat.mod_eq_of_lt (by omega)
            have h2m : (k.val + 1) % (W.n + 4) = k.val + 1 :=
              Nat.mod_eq_of_lt (by have := k.isLt; omega)
            rw [h1m, h2m]
          rw [hv1, val_one_fin] at hv
          omega
        · -- vertical, (W.v i).2 = ym: vertex is r, but edge 1 is horizontal
          have hvm : W.v i = (x₀ + 2, ym) := by
            have hy2 : (W.v i).2 = ym := by
              have hc2 : ((x₀ + 2, ym - 1) : Cell).2 = ym - 1 := rfl
              omega
            exact Prod.ext g1.symm hy2
          have hi1 : i = 1 := hj1 _ hvm
          have h12 : (W.v (i + 1)).1 = (W.v i).1 := hx
          have e11 : (1 + 1 : Fin (W.n + 4)) = 2 := by abel
          rw [hi1, e11, h1x, h2x] at h12
          omega
        · -- horizontal: (W.v i).2 = ym - 1, parity
          have hyk : (W.v i).2 = ym - 1 := by
            have hc2 : ((x₀ + 2, ym - 1) : Cell).2 = ym - 1 := rfl
            omega
          exact hpary1 (hyk ▸ W.parY i)
        · have hyk : (W.v i).2 = ym - 1 := by
            have hc2 : ((x₀ + 2, ym - 1) : Cell).2 = ym - 1 := rfl
            omega
          exact hpary1 (hyk ▸ W.parY i)
    -- (c) the chain lemmas: the opposite sub-loop has zero crossing parity along a chain
    have hchain_not_b1 : ∀ (m : Fin (W.n + 4)), (m : ℕ) = 0 ∨ (k : ℕ) ≤ (m : ℕ) →
        ∀ c ∈ W.edgePts m, c ≠ (x₀ + 2, ym) → c ≠ (x₀ + 2, ym - 2) → c ∉ W₁.boundary := by
      intro m hm c hc hcr hcr' hc1
      rcases hB1 c hc1 with hcb | hce
      · -- c ∈ W.boundary, on both edge m and some W₁-part
        rw [W.mem_boundary c] at hcb
        rcases hcb with ⟨i, hi⟩ | ⟨i, hi⟩
        · -- c = W.v i: then i ∈ 1..k (as c ∈ W₁.boundary) and i ∈ {m, m+1}
          have hik : 1 ≤ (i : ℕ) ∧ (i : ℕ) ≤ (k : ℕ) := by
            have hcv : c ∈ W₁.boundary := hc1
            rw [W₁.mem_boundary c] at hcv
            rcases hcv with ⟨j, hj⟩ | ⟨j, hj⟩
            · have hje : i = ⟨j.val + 1, by omega⟩ := W.inj (hi.trans hj.symm)
              have hv := congrArg Fin.val hje
              have hv1 : ((⟨j.val + 1, by omega⟩ : Fin (W.n + 4)) : ℕ) = j.val + 1 := rfl
              rw [hv1] at hv
              have hjl := j.is_lt
              omega
            · by_cases hjl : j = Fin.last ((k : ℕ) - 4 + 3)
              · have hje : W₁.mid j = (x₀ + 2, ym - 1) := by
                  rw [hjl]
                  show midPt (W₁.v (Fin.last ((k : ℕ) - 4 + 3)))
                    (W₁.v (Fin.last ((k : ℕ) - 4 + 3) + 1)) = (x₀ + 2, ym - 1)
                  rw [hW₁succ_last, hW₁zero, hW₁last]
                  simp only [midPt, Prod.mk.injEq]
                  constructor <;> omega
                have hcy : (W.v i).2 = ym - 1 := by
                  have h2 : W.v i = (x₀ + 2, ym - 1) := hi.trans (hj.symm.trans hje)
                  exact congrArg Prod.snd h2
                exact absurd (hcy ▸ W.parY i) hpary1
              · have hje : W₁.mid j = W.mid ⟨j.val + 1, by omega⟩ := hmid1W j hjl
                have hvm : W.v i = W.mid ⟨j.val + 1, by omega⟩ := hi.trans (hj.symm.trans hje)
                exact absurd hvm (W.vertex_ne_mid _ _)
          have him : (i : ℕ) = (m : ℕ) ∨ (i : ℕ) = (m : ℕ) + 1 ∨ ((m : ℕ) + 1 = W.n + 4 ∧ (i : ℕ) = 0) := by
            have hmem : W.v i ∈ W.edgePts m := hi ▸ hc
            rw [W.vertex_mem_edgePts i m] at hmem
            rcases hmem with h | h
            · exact Or.inl (congrArg Fin.val h)
            · by_cases hml : m = Fin.last (W.n + 3)
              · right; right
                have hmv : (m : ℕ) = W.n + 3 := by rw [hml, Fin.val_last]
                have hiv : (i : ℕ) = 0 := by
                  have h1 : (m + 1 : Fin (W.n + 4)) = 0 := by rw [hml]; exact Fin.ext val_last_succ
                  rw [← h] at h1
                  exact congrArg Fin.val h1
                exact ⟨by omega, hiv⟩
              · right; left
                have h1v : ((m + 1 : Fin (W.n + 4)) : ℕ) = (m : ℕ) + 1 := val_succ_of_not_last m hml
                have hiv : (i : ℕ) = (m : ℕ) + 1 := by
                  have h2 := congrArg Fin.val h
                  rw [h1v] at h2
                  exact h2
                exact hiv
          rcases hm with hm0 | hmk
          · -- m = 0: i ∈ {0, 1}: i = 1 = r (excluded), i = 0 ∉ 1..k
            rw [hm0] at him
            rcases him with h | h | h
            · omega
            · have hiv : i = 1 := Fin.ext (by rw [h, val_one_fin])
              exact hcr (by rw [← hi, hiv, h1])
            · omega
          · -- k ≤ m: i ∈ {m, m+1} ∩ 1..k: i = k = r′ (excluded)
            rcases him with h | h | h
            · have hiv : i = k := Fin.ext (by omega)
              exact hcr' (by rw [← hi, hiv, hk])
            · have hiv : i = k := Fin.ext (by omega)
              exact hcr' (by rw [← hi, hiv, hk])
            · omega
        · -- c = W.mid i: then i = m, and i ∈ 1..k-1 or c = m₀
          have him : i = m := by
            have hmem : W.mid i ∈ W.edgePts m := hi ▸ hc
            simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
            rcases hmem with h | h | h
            · exact absurd h.symm (W.vertex_ne_mid _ _)
            · exact W.mid_inj h
            · exact absurd h.symm (W.vertex_ne_mid _ _)
          have hik : (1 ≤ (i : ℕ) ∧ (i : ℕ) ≤ (k : ℕ) - 1) ∨ W.mid i = (x₀ + 2, ym - 1) := by
            have hcv : c ∈ W₁.boundary := hc1
            rw [W₁.mem_boundary c] at hcv
            rcases hcv with ⟨j, hj⟩ | ⟨j, hj⟩
            · have hvm : W.mid i = W₁.v j := hi.trans hj.symm
              have hvm2 : W.mid i = W.v ⟨j.val + 1, by omega⟩ := hvm
              exact absurd hvm2.symm (W.vertex_ne_mid _ _)
            · by_cases hjl : j = Fin.last ((k : ℕ) - 4 + 3)
              · right
                have hje : W₁.mid j = (x₀ + 2, ym - 1) := by
                  rw [hjl]
                  show midPt (W₁.v (Fin.last ((k : ℕ) - 4 + 3)))
                    (W₁.v (Fin.last ((k : ℕ) - 4 + 3) + 1)) = (x₀ + 2, ym - 1)
                  rw [hW₁succ_last, hW₁zero, hW₁last]
                  simp only [midPt, Prod.mk.injEq]
                  constructor <;> omega
                exact hi.trans (hj.symm.trans hje)
              · left
                have hje : W₁.mid j = W.mid ⟨j.val + 1, by omega⟩ := hmid1W j hjl
                have hie : i = ⟨j.val + 1, by omega⟩ := W.mid_inj (hi.trans (hj.symm.trans hje))
                have hv := congrArg Fin.val hie
                have hv1 : ((⟨j.val + 1, by omega⟩ : Fin (W.n + 4)) : ℕ) = j.val + 1 := rfl
                rw [hv1] at hv
                have hjl2 := j.is_lt
                have hjv : (j : ℕ) ≠ (k : ℕ) - 4 + 3 := fun h => hjl (Fin.ext h)
                omega
          rcases hik with ⟨hi1, hi2⟩ | hm0
          · -- i ∈ 1..k-1 and i = m ∈ {0} ∪ [k, n+3]: impossible
            rcases hm with hm0 | hmk
            · rw [him, hm0] at hi1
              omega
            · rw [← him] at hmk
              omega
          · -- W.mid i = m₀: the chord midpoint is on no W-edge
            rw [hm0] at hi
            exact hm0W (hm0 ▸ W.mid_mem_boundary i)
      · -- c = m₀: not on any W-edge
        rw [hce] at hc
        exact hm0W (by
          show (x₀ + 2, ym - 1) ∈ W.boundary
          show (x₀ + 2, ym - 1) ∈ Finset.univ.biUnion W.edgePts
          exact Finset.mem_biUnion.mpr ⟨m, Finset.mem_univ _, hc⟩)
    -- unit-step shapes between a vertex and the midpoint of an edge
    have hstep_mv : ∀ (j : Fin (W.n + 4)),
        ((W.v (j + 1)).1 = (W.mid j).1 + 1 ∧ (W.v (j + 1)).2 = (W.mid j).2) ∨
        ((W.v (j + 1)).1 = (W.mid j).1 - 1 ∧ (W.v (j + 1)).2 = (W.mid j).2) ∨
        ((W.v (j + 1)).1 = (W.mid j).1 ∧ (W.v (j + 1)).2 = (W.mid j).2 + 1) ∨
        ((W.v (j + 1)).1 = (W.mid j).1 ∧ (W.v (j + 1)).2 = (W.mid j).2 - 1) := by
      intro j
      have hm1 : (W.mid j).1 = ((W.v j).1 + (W.v (j + 1)).1) / 2 := rfl
      have hm2 : (W.mid j).2 = ((W.v j).2 + (W.v (j + 1)).2) / 2 := rfl
      rcases W.step j with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> omega
    have hstep_vm : ∀ (j : Fin (W.n + 4)),
        ((W.mid j).1 = (W.v j).1 + 1 ∧ (W.mid j).2 = (W.v j).2) ∨
        ((W.mid j).1 = (W.v j).1 - 1 ∧ (W.mid j).2 = (W.v j).2) ∨
        ((W.mid j).1 = (W.v j).1 ∧ (W.mid j).2 = (W.v j).2 + 1) ∨
        ((W.mid j).1 = (W.v j).1 ∧ (W.mid j).2 = (W.v j).2 - 1) := by
      intro j
      have hm1 : (W.mid j).1 = ((W.v j).1 + (W.v (j + 1)).1) / 2 := rfl
      have hm2 : (W.mid j).2 = ((W.v j).2 + (W.v (j + 1)).2) / 2 := rfl
      rcases W.step j with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> omega
    -- top caps
    have hmaxY1 : W₁.maxY ≤ ym := by
      apply Finset.max'_le
      intro y hy
      rw [Finset.mem_image] at hy
      obtain ⟨i, -, rfl⟩ := hy
      exact hmax _
    have hmaxY2 : W₂.maxY ≤ ym := by
      apply Finset.max'_le
      intro y hy
      rw [Finset.mem_image] at hy
      obtain ⟨i, -, rfl⟩ := hy
      exact hmax _
    have hV0 : W₁.p2 (W.mid 0) = 0 := by
      have hm : W.mid 0 = (x₀ + 1, ym) := by
        show midPt (W.v 0) (W.v (0 + 1)) = (x₀ + 1, ym)
        have e : (0 + 1 : Fin (W.n + 4)) = 1 := zero_add 1
        rw [e, h0, h1]
        simp only [midPt, Prod.mk.injEq]
        constructor <;> omega
      rw [hm]
      exact W₁.p2_eq_zero_of_maxY hmaxY1
    have hV0' : W₂.p2 (W.mid 1) = 0 := by
      have hm : W.mid 1 = (x₀ + 3, ym) := by
        show midPt (W.v 1) (W.v (1 + 1)) = (x₀ + 3, ym)
        have e : (1 + 1 : Fin (W.n + 4)) = 2 := by abel
        rw [e, h1, h2]
        simp only [midPt, Prod.mk.injEq]
        constructor <;> omega
      rw [hm]
      exact W₂.p2_eq_zero_of_maxY hmaxY2
    -- boundary non-membership of chain points for `W₁`
    have hnb1_v : ∀ (i : Fin (W.n + 4)), (i : ℕ) = 0 ∨ (k : ℕ) < (i : ℕ) → W.v i ∉ W₁.boundary := by
      intro i hi
      have hcase : (i : ℕ) = 0 ∨ (k : ℕ) ≤ (i : ℕ) := by
        rcases hi with h | h
        · exact Or.inl h
        · exact Or.inr (by omega)
      exact hchain_not_b1 i hcase (W.v i) (by simp [Finset.mem_insert])
        (by intro h; have h2 : i = 1 := hj1 i h
            have hv := congrArg Fin.val h2
            rw [val_one_fin] at hv
            omega)
        (by intro h; have h2 : i = k := hjr i h
            have hv := congrArg Fin.val h2
            omega)
    have hnb1_m : ∀ (i : Fin (W.n + 4)), (i : ℕ) = 0 ∨ (k : ℕ) ≤ (i : ℕ) → W.mid i ∉ W₁.boundary := by
      intro i hi
      exact hchain_not_b1 i hi (W.mid i) (W.mid_mem_edgePts i)
        (by rw [← h1]; exact (W.vertex_ne_mid 1 i).symm)
        (by rw [← hk]; exact (W.vertex_ne_mid k i).symm)
    -- path constancy along the `W₂`-chain: `W₁.p2` vanishes from `mid ⟨n+3⟩` down to `mid ⟨k⟩`
    have hpath : ∀ s : ℕ, s ≤ W.n + 3 - (k : ℕ) →
        W₁.p2 (W.mid ⟨(k : ℕ) + (W.n + 3 - (k : ℕ) - s), by omega⟩) = 0 ∧
        W₁.p2 (W.v ⟨((k : ℕ) + (W.n + 3 - (k : ℕ) - s) + 1) % (W.n + 4),
          Nat.mod_lt _ (by omega)⟩) = 0 := by
      intro s
      induction s with
      | zero =>
        intro hs
        have hmid0 : (⟨(k : ℕ) + (W.n + 3 - (k : ℕ) - 0), by omega⟩ : Fin (W.n + 4)) =
            ⟨W.n + 3, by omega⟩ := by
          apply Fin.ext
          show (k : ℕ) + (W.n + 3 - (k : ℕ) - 0) = W.n + 3
          omega
        have hv0 : (⟨((k : ℕ) + (W.n + 3 - (k : ℕ) - 0) + 1) % (W.n + 4),
            Nat.mod_lt _ (by omega)⟩ : Fin (W.n + 4)) = 0 := by
          apply Fin.ext
          show ((k : ℕ) + (W.n + 3 - (k : ℕ) - 0) + 1) % (W.n + 4) = ((0 : Fin (W.n + 4)) : ℕ)
          rw [val_zero_fin]
          have e : (k : ℕ) + (W.n + 3 - (k : ℕ) - 0) + 1 = W.n + 4 := by omega
          rw [e, Nat.mod_self]
        rw [hmid0, hv0]
        have h1b : W.v (0 : Fin (W.n + 4)) ∉ W₁.boundary := by
          apply hchain_not_b1 0 (Or.inl rfl) (W.v 0) (by simp [Finset.mem_insert])
          · intro h
            have h2 : (W.v 0).1 = x₀ + 2 := congrArg Prod.fst h
            omega
          · intro h
            have h2 : (W.v 0).1 = x₀ + 2 := congrArg Prod.fst h
            omega
        have h2b : W.mid (0 : Fin (W.n + 4)) ∉ W₁.boundary :=
          hnb1_m 0 (Or.inl rfl)
        have e : (⟨W.n + 3, by omega⟩ + 1 : Fin (W.n + 4)) = 0 := by
          apply Fin.ext
          rw [Fin.val_add, Fin.val_one']
          have h1m : 1 % (W.n + 4) = 1 := Nat.mod_eq_of_lt (by omega)
          rw [h1m, val_zero_fin]
          have hm : W.n + 3 + 1 = W.n + 4 := by omega
          rw [hm, Nat.mod_self]
        have h3b : W.v (⟨W.n + 3, by omega⟩ + 1 : Fin (W.n + 4)) ∉ W₁.boundary := by
          rw [e]
          exact h1b
        have h4b : W.mid ⟨W.n + 3, by omega⟩ ∉ W₁.boundary :=
          hnb1_m ⟨W.n + 3, by omega⟩ (Or.inr (show (k : ℕ) ≤ W.n + 3 by omega))
        have hs1 : W₁.p2 (W.v (0 : Fin (W.n + 4))) = W₁.p2 (W.mid 0) :=
          W₁.p2_eq_of_unit_step (hstep_vm 0) h1b h2b
        have hs2 : W₁.p2 (W.mid ⟨W.n + 3, by omega⟩) = W₁.p2 (W.v (⟨W.n + 3, by omega⟩ + 1)) :=
          W₁.p2_eq_of_unit_step (hstep_mv ⟨W.n + 3, by omega⟩) h4b h3b
        exact ⟨by rw [hs2, e, hs1, hV0], by rw [hs1, hV0]⟩
      | succ s ih =>
        intro hs
        have ih' := ih (by omega)
        have hmidS : (⟨(k : ℕ) + (W.n + 3 - (k : ℕ) - (s + 1)), by omega⟩ : Fin (W.n + 4)) =
            ⟨(k : ℕ) + (W.n + 3 - (k : ℕ) - s) - 1, by omega⟩ := by
          apply Fin.ext
          show (k : ℕ) + (W.n + 3 - (k : ℕ) - (s + 1)) = (k : ℕ) + (W.n + 3 - (k : ℕ) - s) - 1
          omega
        have hvS : (⟨((k : ℕ) + (W.n + 3 - (k : ℕ) - (s + 1)) + 1) % (W.n + 4),
            Nat.mod_lt _ (by omega)⟩ : Fin (W.n + 4)) =
            ⟨(k : ℕ) + (W.n + 3 - (k : ℕ) - s), by omega⟩ := by
          apply Fin.ext
          show ((k : ℕ) + (W.n + 3 - (k : ℕ) - (s + 1)) + 1) % (W.n + 4) =
            (k : ℕ) + (W.n + 3 - (k : ℕ) - s)
          have e : (k : ℕ) + (W.n + 3 - (k : ℕ) - (s + 1)) + 1 = (k : ℕ) + (W.n + 3 - (k : ℕ) - s) := by
            omega
          rw [e]
          exact Nat.mod_eq_of_lt (by omega)
        rw [hmidS, hvS]
        have h1b : W.v ⟨(k : ℕ) + (W.n + 3 - (k : ℕ) - s), by omega⟩ ∉ W₁.boundary := by
          apply hnb1_v ⟨(k : ℕ) + (W.n + 3 - (k : ℕ) - s), by omega⟩
          right
          show (k : ℕ) < (k : ℕ) + (W.n + 3 - (k : ℕ) - s)
          omega
        have h2b : W.mid ⟨(k : ℕ) + (W.n + 3 - (k : ℕ) - s), by omega⟩ ∉ W₁.boundary :=
          hnb1_m ⟨(k : ℕ) + (W.n + 3 - (k : ℕ) - s), by omega⟩
            (Or.inr (show (k : ℕ) ≤ (k : ℕ) + (W.n + 3 - (k : ℕ) - s) by omega))
        have e : (⟨(k : ℕ) + (W.n + 3 - (k : ℕ) - s) - 1, by omega⟩ + 1 : Fin (W.n + 4)) =
            ⟨(k : ℕ) + (W.n + 3 - (k : ℕ) - s), by omega⟩ := by
          apply Fin.ext
          rw [Fin.val_add, Fin.val_one']
          have h1m : 1 % (W.n + 4) = 1 := Nat.mod_eq_of_lt (by omega)
          have hv1 : ((⟨(k : ℕ) + (W.n + 3 - (k : ℕ) - s) - 1, by omega⟩ : Fin (W.n + 4)) : ℕ) =
            (k : ℕ) + (W.n + 3 - (k : ℕ) - s) - 1 := rfl
          have hv2 : ((⟨(k : ℕ) + (W.n + 3 - (k : ℕ) - s), by omega⟩ : Fin (W.n + 4)) : ℕ) =
            (k : ℕ) + (W.n + 3 - (k : ℕ) - s) := rfl
          rw [h1m, hv1, hv2]
          have h2m : ((k : ℕ) + (W.n + 3 - (k : ℕ) - s) - 1 + 1) % (W.n + 4) =
            (k : ℕ) + (W.n + 3 - (k : ℕ) - s) := by
            have e2 : (k : ℕ) + (W.n + 3 - (k : ℕ) - s) - 1 + 1 = (k : ℕ) + (W.n + 3 - (k : ℕ) - s) := by
              omega
            rw [e2]
            exact Nat.mod_eq_of_lt (by omega)
          rw [h2m]
        have h3b : W.v (⟨(k : ℕ) + (W.n + 3 - (k : ℕ) - s) - 1, by omega⟩ + 1 : Fin (W.n + 4)) ∉
            W₁.boundary := by
          rw [e]
          exact h1b
        have h4b : W.mid ⟨(k : ℕ) + (W.n + 3 - (k : ℕ) - s) - 1, by omega⟩ ∉ W₁.boundary :=
          hnb1_m ⟨(k : ℕ) + (W.n + 3 - (k : ℕ) - s) - 1, by omega⟩
            (Or.inr (show (k : ℕ) ≤ (k : ℕ) + (W.n + 3 - (k : ℕ) - s) - 1 by omega))
        have hs1 : W₁.p2 (W.v ⟨(k : ℕ) + (W.n + 3 - (k : ℕ) - s), by omega⟩) =
            W₁.p2 (W.mid ⟨(k : ℕ) + (W.n + 3 - (k : ℕ) - s), by omega⟩) :=
          W₁.p2_eq_of_unit_step (hstep_vm _) h1b h2b
        have hs2 : W₁.p2 (W.mid ⟨(k : ℕ) + (W.n + 3 - (k : ℕ) - s) - 1, by omega⟩) =
            W₁.p2 (W.v (⟨(k : ℕ) + (W.n + 3 - (k : ℕ) - s) - 1, by omega⟩ + 1)) :=
          W₁.p2_eq_of_unit_step (hstep_mv _) h4b h3b
        exact ⟨by rw [hs2, e, hs1, ih'.1], by rw [hs1, ih'.1]⟩
    -- the chain lemma for `W₁` along the `W₂`-chain
    have hchain2 : ∀ (m : Fin (W.n + 4)), (m : ℕ) = 0 ∨ (k : ℕ) ≤ (m : ℕ) →
        ∀ c ∈ W.edgePts m, c ≠ (x₀ + 2, ym) → c ≠ (x₀ + 2, ym - 2) → W₁.p2 c = 0 := by
      intro m hm c hc hcr hcr'
      rcases hm with hm0 | hmk
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hc
        rcases hc with h | h | h
        · have him : m = 0 := Fin.ext hm0
          rw [h, him]
          have h1b : W.v (0 : Fin (W.n + 4)) ∉ W₁.boundary := by
            apply hchain_not_b1 0 (Or.inl rfl) (W.v 0) (by simp [Finset.mem_insert])
            · intro h2
              have h3 : (W.v 0).1 = x₀ + 2 := congrArg Prod.fst h2
              omega
            · intro h2
              have h3 : (W.v 0).1 = x₀ + 2 := congrArg Prod.fst h2
              omega
          have h2b : W.mid (0 : Fin (W.n + 4)) ∉ W₁.boundary := hnb1_m 0 (Or.inl rfl)
          have hs1 : W₁.p2 (W.v (0 : Fin (W.n + 4))) = W₁.p2 (W.mid 0) :=
            W₁.p2_eq_of_unit_step (hstep_vm 0) h1b h2b
          rw [hs1, hV0]
        · have him : m = 0 := Fin.ext hm0
          rw [h, him]
          exact hV0
        · have him : m = 0 := Fin.ext hm0
          have e : (0 + 1 : Fin (W.n + 4)) = 1 := zero_add 1
          rw [him, e] at h
          exact absurd (h.trans h1) hcr
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hc
        rcases hc with h | h | h
        · -- c = v m
          by_cases hmk2 : (m : ℕ) = (k : ℕ)
          · have hiv : m = k := Fin.ext hmk2
            rw [hiv] at h
            exact absurd (h.trans hk) hcr'
          · have hP2 := hpath (W.n + 3 - ((m : ℕ) - 1)) (by omega)
            have hP3 : W₁.p2 (W.v m) = 0 := by
              have h2 := hP2.2
              have he : (⟨((k : ℕ) + (W.n + 3 - (k : ℕ) - (W.n + 3 - ((m : ℕ) - 1))) + 1) % (W.n + 4),
                  Nat.mod_lt _ (by omega)⟩ : Fin (W.n + 4)) = m := by
                apply Fin.ext
                show ((k : ℕ) + (W.n + 3 - (k : ℕ) - (W.n + 3 - ((m : ℕ) - 1))) + 1) % (W.n + 4) = ↑m
                have e : (k : ℕ) + (W.n + 3 - (k : ℕ) - (W.n + 3 - ((m : ℕ) - 1))) + 1 = (m : ℕ) := by
                  omega
                rw [e]
                exact Nat.mod_eq_of_lt m.isLt
              rw [he] at h2
              exact h2
            rw [h]
            exact hP3
        · -- c = mid m
          have hP := hpath (W.n + 3 - (m : ℕ)) (by omega)
          have hP1 : W₁.p2 (W.mid m) = 0 := by
            have h1 := hP.1
            have he : (⟨(k : ℕ) + (W.n + 3 - (k : ℕ) - (W.n + 3 - (m : ℕ))), by omega⟩ : Fin (W.n + 4)) = m := by
              apply Fin.ext
              show (k : ℕ) + (W.n + 3 - (k : ℕ) - (W.n + 3 - (m : ℕ))) = ↑m
              omega
            rw [he] at h1
            exact h1
          rw [h]
          exact hP1
        · -- c = v (m+1)
          have hP := hpath (W.n + 3 - (m : ℕ)) (by omega)
          have hP2 : W₁.p2 (W.v (m + 1)) = 0 := by
            have h2 := hP.2
            have he : (⟨((k : ℕ) + (W.n + 3 - (k : ℕ) - (W.n + 3 - (m : ℕ))) + 1) % (W.n + 4),
                Nat.mod_lt _ (by omega)⟩ : Fin (W.n + 4)) = m + 1 := by
              apply Fin.ext
              show ((k : ℕ) + (W.n + 3 - (k : ℕ) - (W.n + 3 - (m : ℕ))) + 1) % (W.n + 4) =
                ((m + 1 : Fin (W.n + 4)) : ℕ)
              rw [Fin.val_add, Fin.val_one']
              have h1m : 1 % (W.n + 4) = 1 := Nat.mod_eq_of_lt (by omega)
              rw [h1m]
              have e : (k : ℕ) + (W.n + 3 - (k : ℕ) - (W.n + 3 - (m : ℕ))) + 1 = (m : ℕ) + 1 := by
                omega
              rw [e]
            rw [he] at h2
            exact h2
          rw [h]
          exact hP2
    -- the mirror: chain points of the `W₁`-chain are off `W₂`'s boundary
    have hchain_not_b2 : ∀ (m : Fin (W.n + 4)), 1 ≤ (m : ℕ) → (m : ℕ) ≤ (k : ℕ) - 1 →
        ∀ c ∈ W.edgePts m, c ≠ (x₀ + 2, ym) → c ≠ (x₀ + 2, ym - 2) → c ∉ W₂.boundary := by
      intro m hm1 hm2 c hc hcr hcr' hc2
      rcases hB2 c hc2 with hcb | hce
      · rw [W.mem_boundary c] at hcb
        rcases hcb with ⟨i, hi⟩ | ⟨i, hi⟩
        · have hik : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (k : ℕ) ≤ (i : ℕ) := by
            have hcv : c ∈ W₂.boundary := hc2
            rw [W₂.mem_boundary c] at hcv
            rcases hcv with ⟨j, hj⟩ | ⟨j, hj⟩
            · have hje : i = ⟨(j.val + k) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ :=
                W.inj (hi.trans hj.symm)
              have hv := congrArg Fin.val hje
              have hv1 : ((⟨(j.val + k) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ : Fin (W.n + 4)) : ℕ) =
                (j.val + k) % (W.n + 4) := rfl
              rw [hv1] at hv
              have hjl := j.is_lt
              by_cases cj : j.val + k < W.n + 4
              · rw [Nat.mod_eq_of_lt cj] at hv
                omega
              · push_neg at cj
                have hm : (j.val + k) % (W.n + 4) = j.val + k - (W.n + 4) := by
                  rw [Nat.mod_eq_sub_mod (by omega : W.n + 4 ≤ j.val + k)]
                  exact Nat.mod_eq_of_lt (by omega)
                rw [hm] at hv
                omega
            · by_cases hjl : j = Fin.last (W.n + 2 - (k : ℕ) + 3)
              · have hje : W₂.mid j = (x₀ + 2, ym - 1) := by
                  rw [hjl]
                  show midPt (W₂.v (Fin.last (W.n + 2 - (k : ℕ) + 3)))
                    (W₂.v (Fin.last (W.n + 2 - (k : ℕ) + 3) + 1)) = (x₀ + 2, ym - 1)
                  rw [hW₂succ_last, hW₂zero, hW₂last]
                  simp only [midPt, Prod.mk.injEq]
                  constructor <;> omega
                have hcy : (W.v i).2 = ym - 1 := by
                  have h2 : W.v i = (x₀ + 2, ym - 1) := hi.trans (hj.symm.trans hje)
                  exact congrArg Prod.snd h2
                exact absurd (hcy ▸ W.parY i) hpary1
              · have hje : W₂.mid j = W.mid ⟨(j.val + k) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ :=
                  hmid2W j hjl
                have hvm : W.v i = W.mid ⟨(j.val + k) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ :=
                  hi.trans (hj.symm.trans hje)
                exact absurd hvm (W.vertex_ne_mid _ _)
          have him : (i : ℕ) = (m : ℕ) ∨ (i : ℕ) = (m : ℕ) + 1 := by
            have hmem : W.v i ∈ W.edgePts m := hi ▸ hc
            rw [W.vertex_mem_edgePts i m] at hmem
            rcases hmem with h | h
            · exact Or.inl (congrArg Fin.val h)
            · have h1v : ((m + 1 : Fin (W.n + 4)) : ℕ) = (m : ℕ) + 1 := by
                have hml : m ≠ Fin.last (W.n + 3) := by
                  intro h
                  have hv := congrArg Fin.val h
                  rw [Fin.val_last] at hv
                  omega
                exact val_succ_of_not_last m hml
              have h2 := congrArg Fin.val h
              rw [h1v] at h2
              exact Or.inr h2
          rcases hik with hi0 | hi1 | hik
          · rcases him with h | h <;> omega
          · have hiv : i = 1 := Fin.ext (by rw [hi1, val_one_fin])
            exact hcr (by rw [← hi, hiv, h1])
          · rcases him with h | h
            · omega
            · have hiv : i = k := Fin.ext (by omega)
              exact hcr' (by rw [← hi, hiv, hk])
        · have him : i = m := by
            have hmem : W.mid i ∈ W.edgePts m := hi ▸ hc
            simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
            rcases hmem with h | h | h
            · exact absurd h.symm (W.vertex_ne_mid _ _)
            · exact W.mid_inj h
            · exact absurd h.symm (W.vertex_ne_mid _ _)
          have hik : ((i : ℕ) = 0 ∨ (k : ℕ) ≤ (i : ℕ)) ∨ W.mid i = (x₀ + 2, ym - 1) := by
            have hcv : c ∈ W₂.boundary := hc2
            rw [W₂.mem_boundary c] at hcv
            rcases hcv with ⟨j, hj⟩ | ⟨j, hj⟩
            · have hvm : W.mid i = W₂.v j := hi.trans hj.symm
              have hvm2 : W.mid i = W.v ⟨(j.val + k) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ := hvm
              exact absurd hvm2.symm (W.vertex_ne_mid _ _)
            · by_cases hjl : j = Fin.last (W.n + 2 - (k : ℕ) + 3)
              · right
                have hje : W₂.mid j = (x₀ + 2, ym - 1) := by
                  rw [hjl]
                  show midPt (W₂.v (Fin.last (W.n + 2 - (k : ℕ) + 3)))
                    (W₂.v (Fin.last (W.n + 2 - (k : ℕ) + 3) + 1)) = (x₀ + 2, ym - 1)
                  rw [hW₂succ_last, hW₂zero, hW₂last]
                  simp only [midPt, Prod.mk.injEq]
                  constructor <;> omega
                exact hi.trans (hj.symm.trans hje)
              · left
                have hje : W₂.mid j = W.mid ⟨(j.val + k) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ :=
                  hmid2W j hjl
                have hie : i = ⟨(j.val + k) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ :=
                  W.mid_inj (hi.trans (hj.symm.trans hje))
                have hv := congrArg Fin.val hie
                have hv1 : ((⟨(j.val + k) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ : Fin (W.n + 4)) : ℕ) =
                  (j.val + k) % (W.n + 4) := rfl
                rw [hv1] at hv
                have hjl2 := j.is_lt
                by_cases cj : j.val + k < W.n + 4
                · rw [Nat.mod_eq_of_lt cj] at hv
                  omega
                · push_neg at cj
                  have hm : (j.val + k) % (W.n + 4) = j.val + k - (W.n + 4) := by
                    rw [Nat.mod_eq_sub_mod (by omega : W.n + 4 ≤ j.val + k)]
                    exact Nat.mod_eq_of_lt (by omega)
                  rw [hm] at hv
                  have hjl' : (j : ℕ) ≠ W₂.n + 3 := by
                    intro hjv
                    apply hjl
                    apply Fin.ext
                    rw [Fin.val_last]
                    omega
                  omega
          rcases hik with ⟨hi0 | hmk⟩ | hm0
          · rw [him] at hi0
            omega
          · rw [him] at hmk
            omega
          · rw [hm0] at hi
            exact hm0W (hm0 ▸ W.mid_mem_boundary i)
      · rw [hce] at hc
        exact hm0W (by
          show (x₀ + 2, ym - 1) ∈ W.boundary
          show (x₀ + 2, ym - 1) ∈ Finset.univ.biUnion W.edgePts
          exact Finset.mem_biUnion.mpr ⟨m, Finset.mem_univ _, hc⟩)
    have hnb2_v : ∀ (i : Fin (W.n + 4)), 2 ≤ (i : ℕ) → (i : ℕ) ≤ (k : ℕ) - 1 →
        W.v i ∉ W₂.boundary := by
      intro i hi1 hi2
      exact hchain_not_b2 i (by omega) (by omega) (W.v i) (by simp [Finset.mem_insert])
        (by intro h; have h3 : i = 1 := hj1 i h
            have hv := congrArg Fin.val h3
            rw [val_one_fin] at hv
            omega)
        (by intro h; have h3 : i = k := hjr i h
            have hv := congrArg Fin.val h3
            omega)
    have hnb2_m : ∀ (i : Fin (W.n + 4)), 1 ≤ (i : ℕ) → (i : ℕ) ≤ (k : ℕ) - 1 →
        W.mid i ∉ W₂.boundary := by
      intro i hi1 hi2
      exact hchain_not_b2 i hi1 hi2 (W.mid i) (W.mid_mem_edgePts i)
        (by rw [← h1]; exact (W.vertex_ne_mid 1 i).symm)
        (by rw [← hk]; exact (W.vertex_ne_mid k i).symm)
    -- path constancy along the `W₁`-chain: `W₂.p2` vanishes from `mid 1` up to `mid ⟨k-1⟩`
    have hpath2 : ∀ s : ℕ, s ≤ (k : ℕ) - 3 →
        W₂.p2 (W.mid ⟨min (1 + s) ((k : ℕ) - 2), by omega⟩) = 0 ∧
        W₂.p2 (W.v ⟨min (1 + s + 1) ((k : ℕ) - 1), by omega⟩) = 0 := by
      intro s
      induction s with
      | zero =>
        intro hs
        have hmid0 : (⟨min (1 + 0) ((k : ℕ) - 2), by omega⟩ : Fin (W.n + 4)) = 1 := by
          apply Fin.ext
          show min (1 + 0) ((k : ℕ) - 2) = ((1 : Fin (W.n + 4)) : ℕ)
          rw [val_one_fin]
          omega
        have hv0 : (⟨min (1 + 0 + 1) ((k : ℕ) - 1), by omega⟩ : Fin (W.n + 4)) = 2 := by
          apply Fin.ext
          show min (1 + 0 + 1) ((k : ℕ) - 1) = ((2 : Fin (W.n + 4)) : ℕ)
          rw [val_two_fin]
          omega
        rw [hmid0, hv0]
        have h1b : W.mid (1 : Fin (W.n + 4)) ∉ W₂.boundary :=
          hnb2_m 1 (by rw [val_one_fin]) (by rw [val_one_fin]; omega)
        have h2b : W.v (⟨1, by omega⟩ + 1 : Fin (W.n + 4)) ∉ W₂.boundary := by
          have e : (⟨1, by omega⟩ + 1 : Fin (W.n + 4)) = 2 := by
            apply Fin.ext
            show ((⟨1, by omega⟩ : Fin (W.n + 4)) + 1 : Fin (W.n + 4)).val = ((2 : Fin (W.n + 4)) : ℕ)
            rw [Fin.val_add, Fin.val_one', val_two_fin]
            have h1m : 1 % (W.n + 4) = 1 := Nat.mod_eq_of_lt (by omega)
            have hv1 : ((⟨1, by omega⟩ : Fin (W.n + 4)) : ℕ) = 1 := rfl
            rw [h1m, hv1]
            exact Nat.mod_eq_of_lt (by omega)
          rw [e]
          apply hnb2_v 2 (by rw [val_two_fin]) (by rw [val_two_fin]; omega)
        have hs1 : W₂.p2 (W.mid (1 : Fin (W.n + 4))) = W₂.p2 (W.v (1 + 1)) :=
          W₂.p2_eq_of_unit_step (hstep_mv 1) h1b h2b
        have e2 : (1 + 1 : Fin (W.n + 4)) = 2 := by abel
        exact ⟨hV0', by rw [← e2, ← hs1, hV0']⟩
      | succ s ih =>
        intro hs
        have ih' := ih (by omega)
        have ih2 : W₂.p2 (W.v ⟨(1 + s) + 1, by omega⟩) = 0 := by
          have h := ih'.2
          have he : (⟨min (1 + s + 1) ((k : ℕ) - 1), by omega⟩ : Fin (W.n + 4)) =
              ⟨(1 + s) + 1, by omega⟩ := by
            apply Fin.ext
            show min (1 + s + 1) ((k : ℕ) - 1) = (1 + s) + 1
            omega
          rw [he] at h
          exact h
        have hmidS : (⟨min (1 + (s + 1)) ((k : ℕ) - 2), by omega⟩ : Fin (W.n + 4)) =
            ⟨(1 + s) + 1, by omega⟩ := by
          apply Fin.ext
          show min (1 + (s + 1)) ((k : ℕ) - 2) = (1 + s) + 1
          omega
        have hvS : (⟨min (1 + (s + 1) + 1) ((k : ℕ) - 1), by omega⟩ : Fin (W.n + 4)) =
            ⟨(1 + s) + 2, by omega⟩ := by
          apply Fin.ext
          show min (1 + (s + 1) + 1) ((k : ℕ) - 1) = (1 + s) + 2
          omega
        rw [hmidS, hvS]
        have h1b : W.v ⟨(1 + s) + 1, by omega⟩ ∉ W₂.boundary :=
          hnb2_v ⟨(1 + s) + 1, by omega⟩ (by show 2 ≤ (1 + s) + 1; omega)
            (by show (1 + s) + 1 ≤ (k : ℕ) - 1; omega)
        have h2b : W.mid ⟨(1 + s) + 1, by omega⟩ ∉ W₂.boundary :=
          hnb2_m ⟨(1 + s) + 1, by omega⟩ (by show 1 ≤ (1 + s) + 1; omega)
            (by show (1 + s) + 1 ≤ (k : ℕ) - 1; omega)
        have h3b : W.v (⟨(1 + s) + 1, by omega⟩ + 1 : Fin (W.n + 4)) ∉ W₂.boundary := by
          have e : (⟨(1 + s) + 1, by omega⟩ + 1 : Fin (W.n + 4)) = ⟨(1 + s) + 2, by omega⟩ := by
            apply Fin.ext
            rw [Fin.val_add, Fin.val_one']
            have h1m : 1 % (W.n + 4) = 1 := Nat.mod_eq_of_lt (by omega)
            have hv1 : ((⟨(1 + s) + 1, by omega⟩ : Fin (W.n + 4)) : ℕ) = (1 + s) + 1 := rfl
            have hv2 : ((⟨(1 + s) + 2, by omega⟩ : Fin (W.n + 4)) : ℕ) = (1 + s) + 2 := rfl
            rw [h1m, hv1, hv2]
            have h2m : ((1 + s) + 1 + 1) % (W.n + 4) = (1 + s) + 2 := by
              have e2 : (1 + s) + 1 + 1 = (1 + s) + 2 := by omega
              rw [e2]
              exact Nat.mod_eq_of_lt (by omega)
            rw [h2m]
          rw [e]
          apply hnb2_v ⟨(1 + s) + 2, by omega⟩ (by show 2 ≤ (1 + s) + 2; omega)
            (by show (1 + s) + 2 ≤ (k : ℕ) - 1; omega)
        have hs1 : W₂.p2 (W.v ⟨(1 + s) + 1, by omega⟩) = W₂.p2 (W.mid ⟨(1 + s) + 1, by omega⟩) :=
          W₂.p2_eq_of_unit_step (hstep_vm _) h1b h2b
        have hs2 : W₂.p2 (W.mid ⟨(1 + s) + 1, by omega⟩) =
            W₂.p2 (W.v (⟨(1 + s) + 1, by omega⟩ + 1)) :=
          W₂.p2_eq_of_unit_step (hstep_mv _) h2b h3b
        have e3 : (⟨(1 + s) + 2, by omega⟩ : Fin (W.n + 4)) =
            (⟨(1 + s) + 1, by omega⟩ + 1 : Fin (W.n + 4)) := by
          apply Fin.ext
          rw [Fin.val_add, Fin.val_one']
          have h1m : 1 % (W.n + 4) = 1 := Nat.mod_eq_of_lt (by omega)
          have hv1 : ((⟨(1 + s) + 1, by omega⟩ : Fin (W.n + 4)) : ℕ) = (1 + s) + 1 := rfl
          have hv2 : ((⟨(1 + s) + 2, by omega⟩ : Fin (W.n + 4)) : ℕ) = (1 + s) + 2 := rfl
          rw [h1m, hv1, hv2]
          have h2m : ((1 + s) + 1 + 1) % (W.n + 4) = (1 + s) + 2 := by
            have e2 : (1 + s) + 1 + 1 = (1 + s) + 2 := by omega
            rw [e2]
            exact Nat.mod_eq_of_lt (by omega)
          rw [h2m]
        rw [e3]
        exact ⟨by rw [← hs1, ih2], by rw [← hs2, ← hs1, ih2]⟩
    have hmid_k1 : W₂.p2 (W.mid ⟨(k : ℕ) - 1, by omega⟩) = 0 := by
      by_cases hk5 : 5 ≤ (k : ℕ)
      · have hP := hpath2 ((k : ℕ) - 4) (by omega)
        have hP2 : W₂.p2 (W.v ⟨(k : ℕ) - 2, by omega⟩) = 0 := by
          have h2 := hP.2
          have he : (⟨min (1 + ((k : ℕ) - 4) + 1) ((k : ℕ) - 1), by omega⟩ : Fin (W.n + 4)) =
              ⟨(k : ℕ) - 2, by omega⟩ := by
            apply Fin.ext
            show min (1 + ((k : ℕ) - 4) + 1) ((k : ℕ) - 1) = (k : ℕ) - 2
            omega
          rw [he] at h2
          exact h2
        have h1b : W.v ⟨(k : ℕ) - 2, by omega⟩ ∉ W₂.boundary :=
          hnb2_v ⟨(k : ℕ) - 2, by omega⟩ (by show 2 ≤ (k : ℕ) - 2; omega)
            (by show (k : ℕ) - 2 ≤ (k : ℕ) - 1; omega)
        have h2b : W.mid ⟨(k : ℕ) - 2, by omega⟩ ∉ W₂.boundary :=
          hnb2_m ⟨(k : ℕ) - 2, by omega⟩ (by show 1 ≤ (k : ℕ) - 2; omega)
            (by show (k : ℕ) - 2 ≤ (k : ℕ) - 1; omega)
        have hs1 : W₂.p2 (W.v ⟨(k : ℕ) - 2, by omega⟩) = W₂.p2 (W.mid ⟨(k : ℕ) - 2, by omega⟩) :=
          W₂.p2_eq_of_unit_step (hstep_vm _) h1b h2b
        have h3b : W.v (⟨(k : ℕ) - 2, by omega⟩ + 1 : Fin (W.n + 4)) ∉ W₂.boundary := by
          have e : (⟨(k : ℕ) - 2, by omega⟩ + 1 : Fin (W.n + 4)) = ⟨(k : ℕ) - 1, by omega⟩ := by
            apply Fin.ext
            rw [Fin.val_add, Fin.val_one']
            have h1m : 1 % (W.n + 4) = 1 := Nat.mod_eq_of_lt (by omega)
            have hv1 : ((⟨(k : ℕ) - 2, by omega⟩ : Fin (W.n + 4)) : ℕ) = (k : ℕ) - 2 := rfl
            have hv2 : ((⟨(k : ℕ) - 1, by omega⟩ : Fin (W.n + 4)) : ℕ) = (k : ℕ) - 1 := rfl
            rw [h1m, hv1, hv2]
            have h2m : ((k : ℕ) - 2 + 1) % (W.n + 4) = (k : ℕ) - 1 := by
              have e2 : (k : ℕ) - 2 + 1 = (k : ℕ) - 1 := by omega
              rw [e2]
              exact Nat.mod_eq_of_lt (by omega)
            rw [h2m]
          rw [e]
          apply hnb2_v ⟨(k : ℕ) - 1, by omega⟩ (by show 2 ≤ (k : ℕ) - 1; omega)
            (by show (k : ℕ) - 1 ≤ (k : ℕ) - 1; omega)
        have hs2 : W₂.p2 (W.mid ⟨(k : ℕ) - 2, by omega⟩) =
            W₂.p2 (W.v (⟨(k : ℕ) - 2, by omega⟩ + 1)) :=
          W₂.p2_eq_of_unit_step (hstep_mv _) h2b h3b
        have e3 : (⟨(k : ℕ) - 1, by omega⟩ : Fin (W.n + 4)) =
            (⟨(k : ℕ) - 2, by omega⟩ + 1 : Fin (W.n + 4)) := by
          apply Fin.ext
          rw [Fin.val_add, Fin.val_one']
          have h1m : 1 % (W.n + 4) = 1 := Nat.mod_eq_of_lt (by omega)
          have hv1 : ((⟨(k : ℕ) - 2, by omega⟩ : Fin (W.n + 4)) : ℕ) = (k : ℕ) - 2 := rfl
          have hv2 : ((⟨(k : ℕ) - 1, by omega⟩ : Fin (W.n + 4)) : ℕ) = (k : ℕ) - 1 := rfl
          rw [h1m, hv1, hv2]
          have h2m : ((k : ℕ) - 2 + 1) % (W.n + 4) = (k : ℕ) - 1 := by
            have e2 : (k : ℕ) - 2 + 1 = (k : ℕ) - 1 := by omega
            rw [e2]
            exact Nat.mod_eq_of_lt (by omega)
          rw [h2m]
        have h4b : W.mid (⟨(k : ℕ) - 2, by omega⟩ + 1 : Fin (W.n + 4)) ∉ W₂.boundary := by
          rw [← e3]
          exact hnb2_m ⟨(k : ℕ) - 1, by omega⟩ (by show 1 ≤ (k : ℕ) - 1; omega)
            (by show (k : ℕ) - 1 ≤ (k : ℕ) - 1; omega)
        have hs0 : W₂.p2 (W.v (⟨(k : ℕ) - 2, by omega⟩ + 1)) =
            W₂.p2 (W.mid (⟨(k : ℕ) - 2, by omega⟩ + 1)) :=
          W₂.p2_eq_of_unit_step (hstep_vm _) h3b h4b
        rw [e3, ← hs0, ← hs2, ← hs1, hP2]
      · have hke : (k : ℕ) = 4 := by omega
        have hP := hpath2 1 (by omega)
        have hP2 : W₂.p2 (W.v (3 : Fin (W.n + 4))) = 0 := by
          have h2 := hP.2
          have he : (⟨min (1 + 1 + 1) ((k : ℕ) - 1), by omega⟩ : Fin (W.n + 4)) =
              (3 : Fin (W.n + 4)) := by
            apply Fin.ext
            show min (1 + 1 + 1) ((k : ℕ) - 1) = ((3 : Fin (W.n + 4)) : ℕ)
            rw [val_three_fin]
            omega
          rw [he] at h2
          exact h2
        have hke2 : (⟨(k : ℕ) - 1, by omega⟩ : Fin (W.n + 4)) = (3 : Fin (W.n + 4)) := by
          apply Fin.ext
          show (k : ℕ) - 1 = ((3 : Fin (W.n + 4)) : ℕ)
          rw [val_three_fin]
          omega
        rw [hke2]
        have h1b : W.v (3 : Fin (W.n + 4)) ∉ W₂.boundary :=
          hnb2_v 3 (by rw [val_three_fin]; omega) (by rw [val_three_fin, hke])
        have h2b : W.mid (3 : Fin (W.n + 4)) ∉ W₂.boundary :=
          hnb2_m 3 (by rw [val_three_fin]; omega) (by rw [val_three_fin, hke])
        have hs1 : W₂.p2 (W.v (3 : Fin (W.n + 4))) = W₂.p2 (W.mid 3) :=
          W₂.p2_eq_of_unit_step (hstep_vm 3) h1b h2b
        rw [← hs1]
        exact hP2
    -- the chain lemma for `W₂` along the `W₁`-chain
    have hchain1 : ∀ (m : Fin (W.n + 4)), 1 ≤ (m : ℕ) → (m : ℕ) ≤ (k : ℕ) - 1 →
        ∀ c ∈ W.edgePts m, c ≠ (x₀ + 2, ym) → c ≠ (x₀ + 2, ym - 2) → W₂.p2 c = 0 := by
      intro m hm1 hm2 c hc hcr hcr'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with h | h | h
      · by_cases hm12 : (m : ℕ) = 1
        · have hiv : m = 1 := Fin.ext (by rw [hm12, val_one_fin])
          exact absurd (by rw [h, hiv, h1]) hcr
        · have hP := hpath2 ((m : ℕ) - 2) (by omega)
          have hP2 : W₂.p2 (W.v m) = 0 := by
            have h2 := hP.2
            have he : (⟨min (1 + ((m : ℕ) - 2) + 1) ((k : ℕ) - 1), by omega⟩ : Fin (W.n + 4)) = m := by
              apply Fin.ext
              show min (1 + ((m : ℕ) - 2) + 1) ((k : ℕ) - 1) = ↑m
              omega
            rw [he] at h2
            exact h2
          rw [h]
          exact hP2
      · by_cases hm2' : (m : ℕ) ≤ (k : ℕ) - 2
        · have hP := hpath2 ((m : ℕ) - 1) (by omega)
          have hP1 : W₂.p2 (W.mid m) = 0 := by
            have h1 := hP.1
            have he : (⟨min (1 + ((m : ℕ) - 1)) ((k : ℕ) - 2), by omega⟩ : Fin (W.n + 4)) = m := by
              apply Fin.ext
              show min (1 + ((m : ℕ) - 1)) ((k : ℕ) - 2) = ↑m
              omega
            rw [he] at h1
            exact h1
          rw [h]
          exact hP1
        · have hme : (m : ℕ) = (k : ℕ) - 1 := by omega
          have hiv : m = ⟨(k : ℕ) - 1, by omega⟩ := by
            apply Fin.ext
            show ↑m = (k : ℕ) - 1
            rw [hme]
          rw [h, hiv]
          exact hmid_k1
      · by_cases hm3 : (m : ℕ) + 1 = (k : ℕ)
        · have hiv : m + 1 = k := by
            apply Fin.ext
            rw [Fin.val_add, Fin.val_one']
            have h1m : 1 % (W.n + 4) = 1 := Nat.mod_eq_of_lt (by omega)
            have h2m : (m.val + 1) % (W.n + 4) = m.val + 1 :=
              Nat.mod_eq_of_lt (by have := m.isLt; omega)
            rw [h1m, h2m]
            omega
          exact absurd (by rw [h, hiv, hk]) hcr'
        · have hP := hpath2 ((m : ℕ) - 1) (by omega)
          have hP2 : W₂.p2 (W.v (m + 1)) = 0 := by
            have h2 := hP.2
            have he : (⟨min (1 + ((m : ℕ) - 1) + 1) ((k : ℕ) - 1), by omega⟩ : Fin (W.n + 4)) =
                m + 1 := by
              apply Fin.ext
              show min (1 + ((m : ℕ) - 1) + 1) ((k : ℕ) - 1) = ((m + 1 : Fin (W.n + 4)) : ℕ)
              rw [Fin.val_add, Fin.val_one']
              have h1m : 1 % (W.n + 4) = 1 := Nat.mod_eq_of_lt (by omega)
              have h2m : (m.val + 1) % (W.n + 4) = m.val + 1 :=
                Nat.mod_eq_of_lt (by have := m.isLt; omega)
              rw [h1m, h2m]
              omega
            rw [he] at h2
            exact h2
          rw [h]
          exact hP2
    -- (d) evaluations at the chord's lower endpoint level
    have hdx : W.x ⟨W.n + 3, by omega⟩ = x₀ := congrArg Prod.fst hn1'
    have hdy : W.y ⟨W.n + 3, by omega⟩ = ym - 2 := congrArg Prod.snd hn1'
    have hh2 : ((ym - 2 : ℤ) : ZMod 2) = W.b := by
      push_cast
      rw [show (2 : ZMod 2) = 0 from by decide, sub_zero]
      exact hpb
    have hyi_gen : ∀ i : Fin (W.n + 4), W.vert i → W.lo i = ym - 2 →
        (W.y i = ym - 2 ∨ W.y i = ym) := by
      intro i hvert hlo
      rcases W.vert_cases i hvert with hy | hy
      · have h1 : W.lo i = W.y i := by
          show min (W.y i) (W.y (i + 1)) = W.y i
          rw [hy]
          exact min_eq_left (by omega)
        left
        rw [h1] at hlo
        exact hlo
      · have h1 : W.lo i = W.y (i + 1) := by
          show min (W.y i) (W.y (i + 1)) = W.y (i + 1)
          rw [hy]
          exact min_eq_right (by omega)
        right
        rw [h1] at hlo
        omega
    have hCE : ∀ i : Fin (W.n + 4), W.vert i → W.lo i = ym - 2 → W.x i ≤ x₀ + 2 →
        i = ⟨W.n + 3, by omega⟩ := by
      intro i hvert hlo hxle
      have hhiM : max (W.y i) (W.y (i + 1)) = ym := by
        have h : max (W.y i) (W.y (i + 1)) = W.lo i + 2 := W.hi_eq_lo_add_two i hvert
        rw [hlo] at h
        rw [h]
        ring
      have hxge : x₀ ≤ W.x i := by
        rcases hyi_gen i hvert hlo with h | h
        · have htop : W.y (i + 1) = ym := by
            rcases W.vert_cases i hvert with hyc | hyc
            · rw [h] at hyc
              omega
            · have hle : W.y (i + 1) ≤ ym := hmax (i + 1)
              omega
          have h2 : x₀ ≤ W.x (i + 1) := hmin (i + 1) htop
          have h3 : W.x (i + 1) = W.x i := hvert
          rw [h3] at h2
          exact h2
        · exact hmin i h
      have hx12 : W.x i = x₀ ∨ W.x i = x₀ + 2 := by
        have hd2 : (2 : ℤ) ∣ (W.x i - x₀) := by
          have hm : ((W.x i - x₀ : ℤ) : ZMod 2) = 0 := by
            push_cast
            rw [W.parX i, hpa, sub_self]
          exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hm
        obtain ⟨t, ht⟩ := hd2
        omega
      rcases hx12 with hx | hx
      · rcases hyi_gen i hvert hlo with hy | hy
        · have hvi : W.v i = (x₀, ym - 2) := Prod.ext hx hy
          exact hjd i hvi
        · have hvi : W.v i = (x₀, ym) := Prod.ext hx hy
          have hi0 : i = 0 := hj0 i hvi
          have hys : W.y (i + 1) = ym - 2 := by
            rcases W.vert_cases i hvert with hyc | hyc
            · have hle : W.y (i + 1) ≤ ym := hmax (i + 1)
              omega
            · omega
          have e : i + 1 = (1 : Fin (W.n + 4)) := by rw [hi0]; exact zero_add 1
          have hwy : W.y (i + 1) = ym := by rw [e]; exact h1y
          omega
      · rcases hyi_gen i hvert hlo with hy | hy
        · have hvi : W.v i = (x₀ + 2, ym - 2) := Prod.ext hx hy
          have hi2 : i = k := hjr i hvi
          have hys : W.y (i + 1) = ym := by
            rcases W.vert_cases i hvert with hyc | hyc
            · rw [hy] at hyc
              omega
            · have hle : W.y i ≤ ym := hmax i
              omega
          have hvx : W.x (i + 1) = x₀ + 2 := by
            have h3 : W.x (i + 1) = W.x i := hvert
            rw [hx] at h3
            exact h3
          have hvi1 : W.v (i + 1) = (x₀ + 2, ym) := Prod.ext hvx hys
          have h31 : i + 1 = 1 := hj1 (i + 1) hvi1
          rw [hi2] at h31
          have hv := congrArg Fin.val h31
          have hv1 : ((k + 1 : Fin (W.n + 4)) : ℕ) = (k : ℕ) + 1 := by
            rw [Fin.val_add, Fin.val_one']
            have h1m : 1 % (W.n + 4) = 1 := Nat.mod_eq_of_lt (by omega)
            have h2m : (k.val + 1) % (W.n + 4) = k.val + 1 :=
              Nat.mod_eq_of_lt (by have := k.isLt; omega)
            rw [h1m, h2m]
          rw [hv1, val_one_fin] at hv
          omega
        · have hvi : W.v i = (x₀ + 2, ym) := Prod.ext hx hy
          have hi1 : i = 1 := hj1 i hvi
          have hys : W.y (i + 1) = ym - 2 := by
            rcases W.vert_cases i hvert with hyc | hyc
            · have hle : W.y (i + 1) ≤ ym := hmax (i + 1)
              omega
            · omega
          have e : i + 1 = (2 : Fin (W.n + 4)) := by rw [hi1]; abel
          have hwy : W.y (i + 1) = ym := by rw [e]; exact h2y
          omega
    have hF : (Finset.univ.filter fun i => W.vert i ∧ W.x i ≤ x₀ + 2 ∧ W.lo i = ym - 2) =
        ({⟨W.n + 3, by omega⟩} : Finset (Fin (W.n + 4))) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨hvert, hxle, hlo⟩
        exact hCE i hvert hlo hxle
      · rintro rfl
        refine ⟨?_, ?_, ?_⟩
        · show W.x (⟨W.n + 3, by omega⟩ + 1) = W.x ⟨W.n + 3, by omega⟩
          have eS : (⟨W.n + 3, by omega⟩ + 1 : Fin (W.n + 4)) = 0 := by
            apply Fin.ext
            rw [Fin.val_add, Fin.val_one']
            have h1m : 1 % (W.n + 4) = 1 := Nat.mod_eq_of_lt (by omega)
            rw [h1m, val_zero_fin]
            have hm : W.n + 3 + 1 = W.n + 4 := by omega
            rw [hm, Nat.mod_self]
          rw [eS]
          show (W.v 0).1 = (W.v ⟨W.n + 3, by omega⟩).1
          rw [h0x]
          exact hdx.symm
        · rw [hdx]
          omega
        · show min (W.y ⟨W.n + 3, by omega⟩) (W.y (⟨W.n + 3, by omega⟩ + 1)) = ym - 2
          have eS : (⟨W.n + 3, by omega⟩ + 1 : Fin (W.n + 4)) = 0 := by
            apply Fin.ext
            rw [Fin.val_add, Fin.val_one']
            have h1m : 1 % (W.n + 4) = 1 := Nat.mod_eq_of_lt (by omega)
            rw [h1m, val_zero_fin]
            have hm : W.n + 3 + 1 = W.n + 4 := by omega
            rw [hm, Nat.mod_self]
          rw [eS, hdy]
          show min (ym - 2) (W.v 0).2 = ym - 2
          rw [h0y]
          exact min_eq_left (by show ym - 2 ≤ ym; omega)
    have hevW : W.p2 (x₀ + 2, ym - 2) = 1 := by
      rw [W.p2_eq_spanning_le (x₀ + 2) (ym - 2) hh2, hF, Finset.card_singleton, Nat.cast_one]
    have hh2' : ((ym - 2 : ℤ) : ZMod 2) = W₁.b := hh2
    have hCE1 : ∀ j : Fin (W₁.n + 4), W₁.vert j → W₁.lo j = ym - 2 → W₁.x j ≤ x₀ + 2 →
        j = Fin.last ((k : ℕ) - 4 + 3) := by
      intro j hvert hlo hxle
      by_cases hjl : j = Fin.last ((k : ℕ) - 4 + 3)
      · exact hjl
      · exfalso
        have hvertW : W.vert ⟨j.val + 1, by omega⟩ := by
          have h1 : (W₁.v (j + 1)).1 = (W₁.v j).1 := hvert
          have e1 : W₁.v j = W.v ⟨j.val + 1, by omega⟩ := rfl
          have e2 : W₁.v (j + 1) = W.v (⟨j.val + 1, by omega⟩ + 1) := hsucc1W j hjl
          rw [e1, e2] at h1
          exact h1
        have hloW : W.lo ⟨j.val + 1, by omega⟩ = ym - 2 := by
          have h1 : min (W₁.y j) (W₁.y (j + 1)) = ym - 2 := hlo
          have e1 : W₁.y j = W.y ⟨j.val + 1, by omega⟩ := rfl
          have e2 : W₁.y (j + 1) = W.y (⟨j.val + 1, by omega⟩ + 1) := by
            show (W₁.v (j + 1)).2 = (W.v (⟨j.val + 1, by omega⟩ + 1)).2
            rw [hsucc1W j hjl]
          rw [e1, e2] at h1
          exact h1
        have hxW : W.x ⟨j.val + 1, by omega⟩ ≤ x₀ + 2 := hxle
        have hcl := hCE ⟨j.val + 1, by omega⟩ hvertW hloW hxW
        have hv := congrArg Fin.val hcl
        have hv1 : ((⟨j.val + 1, by omega⟩ : Fin (W.n + 4)) : ℕ) = j.val + 1 := rfl
        have hv2 : ((⟨W.n + 3, by omega⟩ : Fin (W.n + 4)) : ℕ) = W.n + 3 := rfl
        rw [hv1, hv2] at hv
        have hjl2 := j.is_lt
        omega
    have hF1 : (Finset.univ.filter fun j => W₁.vert j ∧ W₁.x j ≤ x₀ + 2 ∧ W₁.lo j = ym - 2) =
        ({Fin.last ((k : ℕ) - 4 + 3)} : Finset (Fin (W₁.n + 4))) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨hvert, hxle, hlo⟩
        exact hCE1 j hvert hlo hxle
      · rintro rfl
        refine ⟨?_, ?_, ?_⟩
        · show (W₁.v (Fin.last ((k : ℕ) - 4 + 3) + 1)).1 = (W₁.v (Fin.last ((k : ℕ) - 4 + 3))).1
          rw [hW₁succ_last, hW₁zero, hW₁last]
        · show (W₁.v (Fin.last ((k : ℕ) - 4 + 3))).1 ≤ x₀ + 2
          rw [hW₁last]
        · show min (W₁.y (Fin.last ((k : ℕ) - 4 + 3))) (W₁.y (Fin.last ((k : ℕ) - 4 + 3) + 1)) = ym - 2
          rw [hW₁succ_last]
          show min (W₁.v (Fin.last ((k : ℕ) - 4 + 3))).2 (W₁.v 0).2 = ym - 2
          rw [hW₁zero, hW₁last]
          exact min_eq_left (by show ym - 2 ≤ ym; omega)
    have hev1 : W₁.p2 (x₀ + 2, ym - 2) = 1 := by
      rw [W₁.p2_eq_spanning_le (x₀ + 2) (ym - 2) hh2', hF1, Finset.card_singleton, Nat.cast_one]
    have hev2 : W₂.p2 (x₀ + 2, ym - 2) = 0 := by
      have h := hflip (x₀ + 2, ym - 2)
      rw [hevW, hev1] at h
      rcases hkey (W₂.p2 (x₀ + 2, ym - 2)) with h0' | h1'
      · exact h0'
      · rw [h1'] at h
        exact absurd h (by decide)
    have hevm0 : W.p2 (x₀ + 2, ym - 1) = 1 := by
      have h := W.p2_band (x₀ + 2) (ym - 2) hh2
      rw [show ym - 2 + 1 = (ym - 1 : ℤ) from by ring] at h
      rw [← h]
      exact hevW
    -- crossing parity at a spanning level, counted to the right
    have hp2gt : ∀ (L : OrthoLoop) (a h : ℤ), ((h : ZMod 2) = L.b) →
        L.p2 (a, h) = ((Finset.univ.filter fun i => L.vert i ∧ a < L.x i ∧ L.lo i = h).card :
          ZMod 2) := by
      intro L a h hh
      have hcond : ∀ i : Fin (L.n + 4),
          (L.vert i ∧ a < L.x i ∧ L.lo i ≤ h ∧ h < L.hi i) ↔ (L.vert i ∧ a < L.x i ∧ L.lo i = h) := by
        intro i
        constructor
        · rintro ⟨hv, h1, h2, h3⟩
          have hhi : L.hi i = L.lo i + 2 := L.hi_eq_lo_add_two i hv
          rw [hhi] at h3
          have hpar := L.lo_parY i
          have hmod : (((L.lo i - h : ℤ)) : ZMod 2) = 0 := by
            rw [Int.cast_sub, hpar, hh, sub_self]
          have hev : Even (L.lo i - h) := by
            rw [even_iff_two_dvd]
            exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hmod
          obtain ⟨k, hk⟩ := hev
          have h4 : L.lo i = h := by omega
          exact ⟨hv, h1, h4⟩
        · rintro ⟨hv, h1, h2⟩
          have h4 : L.lo i ≤ h := by rw [h2]
          have h5 : h < L.hi i := by
            have hhi : L.hi i = L.lo i + 2 := L.hi_eq_lo_add_two i hv
            rw [hhi, h2]
            omega
          exact ⟨hv, h1, h4, h5⟩
      have hshow : L.p2 (a, h) =
          (∑ i : Fin (L.n + 4), if L.vert i ∧ a < L.x i ∧ L.lo i ≤ h ∧ h < L.hi i
            then (1 : ZMod 2) else 0) := rfl
      have hfe : (Finset.univ.filter fun i => L.vert i ∧ a < L.x i ∧ L.lo i ≤ h ∧ h < L.hi i) =
          (Finset.univ.filter fun i => L.vert i ∧ a < L.x i ∧ L.lo i = h) := by
        apply Finset.filter_congr
        intro i _
        exact hcond i
      rw [hshow, Finset.sum_boole, hfe]
    -- (e) the two interiors are disjoint off the boundary
    -- column reduction: a Bad point lies on the chord's column below r′
    have hcol : ∀ c : Cell, W₁.p2 c = 1 → W₂.p2 c = 1 → c ∉ W.boundary → c ≠ (x₀ + 2, ym - 1) →
        c.1 = x₀ + 2 ∧ c.2 < ym - 2 := by
      intro c hp1 hp2 hcb hcm0
      have h0 : W.p2 c = 0 := by
        have h := hflip c
        rw [hp1, hp2] at h
        rcases hkey (W.p2 c) with h0' | h1'
        · exact h0'
        · rw [h1'] at h
          exact absurd h (by decide)
      -- propagation of the (1,1,0) triple along a clean vertical segment
      have hprop : ∀ (t : ℕ) (y₀ : ℤ), c.2 + t ≤ y₀ →
          (∀ y : ℤ, c.2 ≤ y → y ≤ y₀ → (c.1, y) ∉ W.boundary ∧ (c.1, y) ≠ (x₀ + 2, ym - 1)) →
          W₁.p2 (c.1, c.2 + t) = 1 ∧ W₂.p2 (c.1, c.2 + t) = 1 ∧ W.p2 (c.1, c.2 + t) = 0 := by
        intro t y₀ ht hclean
        induction t with
        | zero =>
          have e : c.2 + ((0 : ℕ) : ℤ) = c.2 := by omega
          rw [e]
          exact ⟨hp1, hp2, h0⟩
        | succ t ih =>
          obtain ⟨g1, g2, g3⟩ := ih (by omega)
          have hc1 : (c.1, c.2 + t) ∉ W.boundary ∧ (c.1, c.2 + t) ≠ (x₀ + 2, ym - 1) := by
            by_cases hz : t = 0
            · rw [hz]
              have e : c.2 + ((0 : ℕ) : ℤ) = c.2 := by omega
              rw [e]
              exact ⟨hcb, hcm0⟩
            · exact hclean (c.2 + t) (by omega) (by omega)
          have hc2 : (c.1, c.2 + (t + 1)) ∉ W.boundary ∧ (c.1, c.2 + (t + 1)) ≠ (x₀ + 2, ym - 1) :=
            hclean (c.2 + (t + 1)) (by omega) (by omega)
          have hb1 : (c.1, c.2 + t) ∉ W₁.boundary := by
            intro h
            rcases hB1 _ h with hbb | hce
            · exact hc1.1 hbb
            · exact hc1.2 hce
          have hb2 : (c.1, c.2 + t) ∉ W₂.boundary := by
            intro h
            rcases hB2 _ h with hbb | hce
            · exact hc1.1 hbb
            · exact hc1.2 hce
          have hb1' : (c.1, c.2 + (t + 1)) ∉ W₁.boundary := by
            intro h
            rcases hB1 _ h with hbb | hce
            · exact hc2.1 hbb
            · exact hc2.2 hce
          have hb2' : (c.1, c.2 + (t + 1)) ∉ W₂.boundary := by
            intro h
            rcases hB2 _ h with hbb | hce
            · exact hc2.1 hbb
            · exact hc2.2 hce
          have hstep : (((c.1, c.2 + (t + 1)) : Cell).1 = (c.1, c.2 + t).1 ∧
              ((c.1, c.2 + (t + 1)) : Cell).2 = (c.1, c.2 + t).2 + 1) := by
            constructor
            · rfl
            · show c.2 + (t + 1) = c.2 + t + 1
              omega
          have hstep3 : (((c.1, c.2 + (t + 1)) : Cell).1 = (c.1, c.2 + t).1 + 1 ∧
              ((c.1, c.2 + (t + 1)) : Cell).2 = (c.1, c.2 + t).2) ∨
            (((c.1, c.2 + (t + 1)) : Cell).1 = (c.1, c.2 + t).1 - 1 ∧
              ((c.1, c.2 + (t + 1)) : Cell).2 = (c.1, c.2 + t).2) ∨
            (((c.1, c.2 + (t + 1)) : Cell).1 = (c.1, c.2 + t).1 ∧
              ((c.1, c.2 + (t + 1)) : Cell).2 = (c.1, c.2 + t).2 + 1) ∨
            (((c.1, c.2 + (t + 1)) : Cell).1 = (c.1, c.2 + t).1 ∧
              ((c.1, c.2 + (t + 1)) : Cell).2 = (c.1, c.2 + t).2 - 1) :=
            Or.inr (Or.inr (Or.inl hstep))
          have e1 := W₁.p2_eq_of_unit_step hstep3 hb1 hb1'
          have e2 := W₂.p2_eq_of_unit_step hstep3 hb2 hb2'
          have e3 := W.p2_eq_of_unit_step hstep3 hc1.1 hc2.1
          show W₁.p2 (c.1, c.2 + (↑t + 1)) = 1 ∧ W₂.p2 (c.1, c.2 + (↑t + 1)) = 1 ∧
            W.p2 (c.1, c.2 + (↑t + 1)) = 0
          rw [← e1, ← e2, ← e3]
          exact ⟨g1, g2, g3⟩
      have hcym : c.2 < ym := by
        by_contra hcc
        push_neg at hcc
        rw [W₁.p2_eq_zero_of_maxY (by omega : W₁.maxY ≤ c.2)] at hp1
        exact absurd hp1 (by decide)
      have hhit : ∃ y₀ : ℤ, c.2 < y₀ ∧ y₀ ≤ ym ∧
          ((c.1, y₀) ∈ W.boundary ∨ (c.1, y₀) = (x₀ + 2, ym - 1)) ∧
          (∀ y : ℤ, c.2 ≤ y → y < y₀ → (c.1, y) ∉ W.boundary ∧ (c.1, y) ≠ (x₀ + 2, ym - 1)) := by
        by_cases hex : ∃ y : ℤ, c.2 < y ∧ y ≤ ym ∧
            ((c.1, y) ∈ W.boundary ∨ (c.1, y) = (x₀ + 2, ym - 1))
        · have hne : ((Finset.Ioc c.2 ym).filter
              (fun y => (c.1, y) ∈ W.boundary ∨ (c.1, y) = (x₀ + 2, ym - 1))).Nonempty := by
            obtain ⟨y, hy1, hy2, hy3⟩ := hex
            rw [Finset.nonempty_iff_ne_empty]
            intro hnm
            rw [Finset.eq_empty_iff_forall_notMem] at hnm
            exact hnm y (by rw [Finset.mem_filter, Finset.mem_Ioc]; exact ⟨⟨hy1, hy2⟩, hy3⟩)
          obtain ⟨y₀, hy₀, hmin⟩ := Finset.exists_min_image _ id hne
          rw [Finset.mem_filter, Finset.mem_Ioc] at hy₀
          obtain ⟨⟨hy₀1, hy₀2⟩, hy₀3⟩ := hy₀
          refine ⟨y₀, hy₀1, hy₀2, hy₀3, ?_⟩
          intro y hy1 hy2
          by_cases hy3 : y = c.2
          · rw [hy3]
            exact ⟨hcb, hcm0⟩
          · have hnm : y ∉ (Finset.Ioc c.2 ym).filter
                (fun y => (c.1, y) ∈ W.boundary ∨ (c.1, y) = (x₀ + 2, ym - 1)) := by
              intro hmem
              have hle : y₀ ≤ y := hmin y hmem
              omega
            rw [Finset.mem_filter, Finset.mem_Ioc] at hnm
            push_neg at hnm
            exact hnm ⟨by omega, by omega⟩
        · push_neg at hex
          exfalso
          have htop := hprop (ym - c.2).toNat ym (by
            rw [Int.toNat_sub_of_le (by omega : c.2 ≤ ym)]
            omega) (by
            intro y hy1 hy2
            by_cases hye : y = c.2
            · rw [hye]
              exact ⟨hcb, hcm0⟩
            · exact hex y (by omega) (by omega))
          have he : c.2 + ((ym - c.2).toNat : ℤ) = ym := by
            rw [Int.toNat_sub_of_le (by omega : c.2 ≤ ym)]
            omega
          rw [he] at htop
          have hz := W₁.p2_eq_zero_of_maxY (c := (c.1, ym)) (by omega : W₁.maxY ≤ ym)
          rw [hz] at htop
          exact absurd htop.1 (by decide)
      obtain ⟨y₀, hy₀1, hy₀2, hy₀3, hclean⟩ := hhit
      -- the kill: a chain point with vanishing p2 cannot sit above a (1,1,0) segment
      have hkill : ∀ (L : OrthoLoop), L.b = W.b → L.p2 (c.1, y₀) = 0 → L.p2 (c.1, y₀ - 1) = 1 →
          (c.1, y₀) ∉ L.boundary → False := by
        intro L Lb hp0 hp1 hnb
        by_cases hpar : (y₀ : ZMod 2) = W.b
        · have hgt1 : L.p2 (c.1, y₀) =
              ((Finset.univ.filter fun i => L.vert i ∧ c.1 < L.x i ∧ L.lo i = y₀).card : ZMod 2) :=
            hp2gt L c.1 y₀ (by rw [Lb]; exact hpar)
          have hbb2 : ((y₀ - 2 : ℤ) : ZMod 2) = L.b := by
            rw [Lb]
            push_cast
            rw [show (2 : ZMod 2) = 0 from by decide, sub_zero]
            exact hpar
          have hgt2 : L.p2 (c.1, y₀ - 1) =
              ((Finset.univ.filter fun i => L.vert i ∧ c.1 < L.x i ∧ L.hi i = y₀).card : ZMod 2) := by
            have hb1 : L.p2 (c.1, y₀ - 1) = L.p2 (c.1, y₀ - 2) := by
              have h := L.p2_band c.1 (y₀ - 2) hbb2
              rw [show y₀ - 2 + 1 = (y₀ - 1 : ℤ) from by ring] at h
              exact h.symm
            rw [hb1]
            have hgt3 : L.p2 (c.1, y₀ - 2) =
                ((Finset.univ.filter fun i => L.vert i ∧ c.1 < L.x i ∧ L.lo i = y₀ - 2).card : ZMod 2) :=
              hp2gt L c.1 (y₀ - 2) hbb2
            rw [hgt3]
            have hfe : (Finset.univ.filter fun i => L.vert i ∧ c.1 < L.x i ∧ L.hi i = y₀) =
                (Finset.univ.filter fun i => L.vert i ∧ c.1 < L.x i ∧ L.lo i = y₀ - 2) := by
              ext i
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              constructor
              · rintro ⟨hv, h1, h2⟩
                have hhi : L.hi i = L.lo i + 2 := L.hi_eq_lo_add_two i hv
                exact ⟨hv, h1, by omega⟩
              · rintro ⟨hv, h1, h2⟩
                have hhi : L.hi i = L.lo i + 2 := L.hi_eq_lo_add_two i hv
                exact ⟨hv, h1, by omega⟩
            rw [hfe]
          have hce := L.corner_count_even c.1 y₀ hnb
          rw [hgt1] at hp0
          rw [hgt2] at hp1
          rw [Finset.sum_boole, Finset.sum_boole] at hce
          rw [hp0, hp1] at hce
          exact absurd hce (by decide)
        · have h2 : ((y₀ - 1 : ℤ) : ZMod 2) = W.b := by
            have h3 : (y₀ : ZMod 2) ≠ W.b := hpar
            have h4 : ((y₀ - 1 : ℤ) : ZMod 2) = (y₀ : ZMod 2) + 1 := by
              push_cast
              rcases hkey (y₀ : ZMod 2) with h | h <;> rw [h] <;> decide
            rw [h4]
            rcases hkey (y₀ : ZMod 2) with h5 | h5 <;> rcases hkey W.b with h6 | h6
            · rw [h5, h6] at h3
              exact absurd h3 (by decide)
            · rw [h5, h6]
              decide
            · rw [h5, h6]
              decide
            · rw [h5, h6] at h3
              exact absurd h3 (by decide)
          have hb1 : L.p2 (c.1, y₀ - 1) = L.p2 (c.1, y₀) := by
            have h := L.p2_band c.1 (y₀ - 1) (by rw [Lb]; exact h2)
            rw [show y₀ - 1 + 1 = (y₀ : ℤ) from by ring] at h
            exact h
          rw [hb1] at hp1
          rw [hp0] at hp1
          exact absurd hp1 (by decide)
      have htriple : W₁.p2 (c.1, y₀ - 1) = 1 ∧ W₂.p2 (c.1, y₀ - 1) = 1 ∧ W.p2 (c.1, y₀ - 1) = 0 := by
        have h := hprop (y₀ - 1 - c.2).toNat (y₀ - 1) (by
          rw [Int.toNat_sub_of_le (by omega : c.2 ≤ y₀ - 1)]
          omega) (by
          intro y hy1 hy2
          exact hclean y hy1 (by omega))
        have he : c.2 + ((y₀ - 1 - c.2).toNat : ℤ) = y₀ - 1 := by
          rw [Int.toNat_sub_of_le (by omega : c.2 ≤ y₀ - 1)]
          omega
        rw [he] at h
        exact h
      rcases hy₀3 with hq | hq
      · rw [W.mem_boundary (c.1, y₀)] at hq
        rcases hq with ⟨i, hi⟩ | ⟨i, hi⟩
        · -- q = W.v i
          by_cases hcase : 1 ≤ (i : ℕ) ∧ (i : ℕ) ≤ (k : ℕ) - 1
          · by_cases hi1 : i = 1
            · -- q = r: m₀ blocks
              have hqeq : (c.1, y₀) = (x₀ + 2, ym) := by rw [← hi, hi1, h1]
              have hc1 : c.1 = x₀ + 2 := congrArg Prod.fst hqeq
              have hym : y₀ = ym := congrArg Prod.snd hqeq
              have hm0in : (c.1, ym - 1) ∉ W.boundary ∧ (c.1, ym - 1) ≠ (x₀ + 2, ym - 1) :=
                hclean (ym - 1) (by omega) (by omega)
              rw [hc1] at hm0in
              exact absurd rfl hm0in.2
            · -- hchain1 kill
              have hp0 : W₂.p2 (c.1, y₀) = 0 := by
                rw [← hi]
                apply hchain1 i hcase.1 hcase.2 (W.v i) (by simp [Finset.mem_insert])
                · intro h
                  exact hi1 (hj1 i h)
                · intro h
                  have hiv : i = k := hjr i h
                  have hv := congrArg Fin.val hiv
                  omega
              exact (hkill W₂ rfl hp0 htriple.2.1 (by
                rw [← hi]
                apply hnb2_v i (by
                  have hne : (i : ℕ) ≠ 1 := by
                    intro h
                    apply hi1
                    apply Fin.ext
                    rw [val_one_fin]
                    exact h
                  omega) hcase.2)).elim
          · push_neg at hcase
            have hi2 : (i : ℕ) = 0 ∨ (k : ℕ) ≤ (i : ℕ) := by
              by_cases h1 : 1 ≤ (i : ℕ)
              · exact Or.inr (by have h2 := hcase h1; omega)
              · exact Or.inl (by omega)
            by_cases hik : i = k
            · -- q = r′: the column
              have hqeq : (c.1, y₀) = (x₀ + 2, ym - 2) := by rw [← hi, hik, hk]
              have hc1 : c.1 = x₀ + 2 := congrArg Prod.fst hqeq
              have hym : y₀ = ym - 2 := congrArg Prod.snd hqeq
              rw [hym] at hy₀1
              exact ⟨hc1, hy₀1⟩
            · -- hchain2 kill
              have hp0 : W₁.p2 (c.1, y₀) = 0 := by
                rw [← hi]
                apply hchain2 i hi2 (W.v i) (by simp [Finset.mem_insert])
                · intro h
                  have hiv : i = 1 := hj1 i h
                  have hv := congrArg Fin.val hiv
                  rw [val_one_fin] at hv
                  omega
                · intro h
                  exact hik (hjr i h)
              exact (hkill W₁ rfl hp0 htriple.1 (by
                rw [← hi]
                apply hnb1_v i (by
                  rcases hi2 with h | h
                  · exact Or.inl h
                  · exact Or.inr (by have h2 : (i : ℕ) ≠ (k : ℕ) := fun h3 => hik (Fin.ext h3); omega)))).elim
        · -- q = W.mid i
          by_cases hcase : 1 ≤ (i : ℕ) ∧ (i : ℕ) ≤ (k : ℕ) - 1
          · have hp0 : W₂.p2 (c.1, y₀) = 0 := by
              rw [← hi]
              apply hchain1 i hcase.1 hcase.2 (W.mid i) (W.mid_mem_edgePts i)
              · rw [← h1]; exact (W.vertex_ne_mid 1 i).symm
              · rw [← hk]; exact (W.vertex_ne_mid k i).symm
            exact (hkill W₂ rfl hp0 htriple.2.1 (by
              rw [← hi]
              apply hnb2_m i hcase.1 hcase.2)).elim
          · push_neg at hcase
            have hi2 : (i : ℕ) = 0 ∨ (k : ℕ) ≤ (i : ℕ) := by
              by_cases h1 : 1 ≤ (i : ℕ)
              · exact Or.inr (by have h2 := hcase h1; omega)
              · exact Or.inl (by omega)
            have hp0 : W₁.p2 (c.1, y₀) = 0 := by
              rw [← hi]
              apply hchain2 i hi2 (W.mid i) (W.mid_mem_edgePts i)
              · rw [← h1]; exact (W.vertex_ne_mid 1 i).symm
              · rw [← hk]; exact (W.vertex_ne_mid k i).symm
            exact (hkill W₁ rfl hp0 htriple.1 (by
              rw [← hi]
              apply hnb1_m i hi2)).elim
      · -- q = m₀: r′ blocks
        have hqeq : (c.1, y₀) = (x₀ + 2, ym - 1) := hq
        have hc1 : c.1 = x₀ + 2 := congrArg Prod.fst hqeq
        have hym : y₀ = ym - 1 := congrArg Prod.snd hqeq
        by_cases hcy : c.2 ≤ ym - 2
        · have hr'in : (c.1, ym - 2) ∉ W.boundary ∧ (c.1, ym - 2) ≠ (x₀ + 2, ym - 1) :=
            hclean (ym - 2) (by omega) (by omega)
          rw [hc1] at hr'in
          exact (hr'in.1 (by rw [← hk]; exact W.vertex_mem_boundary k)).elim
        · push_neg at hcy
          have hce : c = (x₀ + 2, ym - 1) := by
            have h2 : c.2 = ym - 1 := by omega
            exact Prod.ext hc1 h2
          exact absurd hce hcm0
    -- the disjointness itself
    have hBad : ∀ c : Cell, W₁.p2 c = 1 → W₂.p2 c = 1 →
        c ∈ W.boundary ∨ c = (x₀ + 2, ym - 1) := by
      intro c h1 h2
      by_contra hcon
      push_neg at hcon
      obtain ⟨hcb, hcm0⟩ := hcon
      -- Step A: a Bad point with y-coordinate ≢ b
      have hA : ∃ c' : Cell, W₁.p2 c' = 1 ∧ W₂.p2 c' = 1 ∧ c' ∉ W.boundary ∧
          c' ≠ (x₀ + 2, ym - 1) ∧ (c'.2 : ZMod 2) ≠ W.b := by
        by_cases hpar : (c.2 : ZMod 2) = W.b
        · have hnb : (c.1, c.2 + 1) ∉ W.boundary ∧ (c.1, c.2 + 1) ≠ (x₀ + 2, ym - 1) := by
            constructor
            · intro h
              rw [W.mem_boundary _] at h
              rcases h with ⟨i, hi⟩ | ⟨i, hi⟩
              · have hyk : (W.v i).2 = c.2 + 1 := congrArg Prod.snd hi
                have hpar2 : ((c.2 + 1 : ℤ) : ZMod 2) ≠ W.b := by
                  have h4 : ((c.2 + 1 : ℤ) : ZMod 2) = (c.2 : ZMod 2) + 1 := by
                    push_cast
                    rcases hkey (c.2 : ZMod 2) with h | h <;> rw [h] <;> decide
                  rw [h4, hpar]
                  rcases hkey W.b with h | h <;> rw [h] <;> decide
                exact hpar2 (hyk ▸ W.parY i)
              · rcases W.mid_cases i _ hi with ⟨hx, g1, g2 | g2⟩ | ⟨hy, g1, g2 | g2⟩
                · have hy2 : (W.v i).2 = c.2 := by
                    have hc2 : ((c.1, c.2 + 1) : Cell).2 = c.2 + 1 := rfl
                    omega
                  have hvm : W.v i = (c.1, c.2) := by
                    have hx2 : (W.v i).1 = c.1 := by
                      have hc1' : ((c.1, c.2 + 1) : Cell).1 = c.1 := rfl
                      omega
                    exact Prod.ext hx2 hy2
                  exact hcb (by
                    show (c.1, c.2) ∈ W.boundary
                    rw [← hvm]
                    exact W.vertex_mem_boundary i)
                · have hy2 : (W.v i).2 = c.2 + 2 := by
                    have hc2 : ((c.1, c.2 + 1) : Cell).2 = c.2 + 1 := rfl
                    omega
                  have hm2 : ((c.1, c.2 + 1) : Cell).2 = ((W.v i).2 + (W.v (i + 1)).2) / 2 := by
                    have hr : (W.mid i).2 = ((W.v i).2 + (W.v (i + 1)).2) / 2 := rfl
                    rw [hi] at hr
                    exact hr
                  rw [hy2] at hm2
                  have hy3 : (W.v (i + 1)).2 = c.2 := by
                    have hst := W.step i
                    omega
                  have hx3 : (W.v (i + 1)).1 = c.1 := by
                    have hc1' : ((c.1, c.2 + 1) : Cell).1 = c.1 := rfl
                    have hx4 : (W.v (i + 1)).1 = (W.v i).1 := hx
                    omega
                  have hvm2 : W.v (i + 1) = (c.1, c.2) := Prod.ext hx3 hy3
                  exact hcb (by
                    show (c.1, c.2) ∈ W.boundary
                    rw [← hvm2]
                    exact W.vertex_mem_boundary (i + 1))
                · have hyk : (W.v i).2 = c.2 + 1 := by
                    have hc2 : ((c.1, c.2 + 1) : Cell).2 = c.2 + 1 := rfl
                    omega
                  have hpar2 : ((c.2 + 1 : ℤ) : ZMod 2) ≠ W.b := by
                    have h4 : ((c.2 + 1 : ℤ) : ZMod 2) = (c.2 : ZMod 2) + 1 := by
                      push_cast
                      rcases hkey (c.2 : ZMod 2) with h | h <;> rw [h] <;> decide
                    rw [h4, hpar]
                    rcases hkey W.b with h | h <;> rw [h] <;> decide
                  exact hpar2 (hyk ▸ W.parY i)
                · have hyk : (W.v i).2 = c.2 + 1 := by
                    have hc2 : ((c.1, c.2 + 1) : Cell).2 = c.2 + 1 := rfl
                    omega
                  have hpar2 : ((c.2 + 1 : ℤ) : ZMod 2) ≠ W.b := by
                    have h4 : ((c.2 + 1 : ℤ) : ZMod 2) = (c.2 : ZMod 2) + 1 := by
                      push_cast
                      rcases hkey (c.2 : ZMod 2) with h | h <;> rw [h] <;> decide
                    rw [h4, hpar]
                    rcases hkey W.b with h | h <;> rw [h] <;> decide
                  exact hpar2 (hyk ▸ W.parY i)
            · intro h
              have h2 : c.2 + 1 = ym - 1 := by
                have h3 : ((c.1, c.2 + 1) : Cell).2 = ((x₀ + 2, ym - 1) : Cell).2 := by rw [h]
                exact h3
              have hc1 : c.1 = x₀ + 2 := by
                have h3 : ((c.1, c.2 + 1) : Cell).1 = ((x₀ + 2, ym - 1) : Cell).1 := by rw [h]
                exact h3
              have hce : c = (x₀ + 2, ym - 2) := by
                have h4 : c.2 = ym - 2 := by omega
                exact Prod.ext hc1 h4
              rw [hce] at hcb
              exact hcb (by rw [← hk]; exact W.vertex_mem_boundary k)
          obtain ⟨hnb1, hnb2⟩ := hnb
          have hstep : (((c.1, c.2 + 1) : Cell).1 = c.1 ∧ ((c.1, c.2 + 1) : Cell).2 = c.2 + 1) :=
            ⟨rfl, rfl⟩
          have hstep3 : (((c.1, c.2 + 1) : Cell).1 = c.1 + 1 ∧ ((c.1, c.2 + 1) : Cell).2 = c.2) ∨
            (((c.1, c.2 + 1) : Cell).1 = c.1 - 1 ∧ ((c.1, c.2 + 1) : Cell).2 = c.2) ∨
            (((c.1, c.2 + 1) : Cell).1 = c.1 ∧ ((c.1, c.2 + 1) : Cell).2 = c.2 + 1) ∨
            (((c.1, c.2 + 1) : Cell).1 = c.1 ∧ ((c.1, c.2 + 1) : Cell).2 = c.2 - 1) :=
            Or.inr (Or.inr (Or.inl hstep))
          have hb1 : c ∉ W₁.boundary := by
            intro h
            rcases hB1 _ h with hbb | hce
            · exact hcb hbb
            · exact hcm0 hce
          have hb2 : c ∉ W₂.boundary := by
            intro h
            rcases hB2 _ h with hbb | hce
            · exact hcb hbb
            · exact hcm0 hce
          have hb1' : (c.1, c.2 + 1) ∉ W₁.boundary := by
            intro h
            rcases hB1 _ h with hbb | hce
            · exact hnb1 hbb
            · exact hnb2 hce
          have hb2' : (c.1, c.2 + 1) ∉ W₂.boundary := by
            intro h
            rcases hB2 _ h with hbb | hce
            · exact hnb1 hbb
            · exact hnb2 hce
          have e1 := W₁.p2_eq_of_unit_step hstep3 hb1 hb1'
          have e2 := W₂.p2_eq_of_unit_step hstep3 hb2 hb2'
          have hpar2 : (((c.1, c.2 + 1) : Cell).2 : ZMod 2) ≠ W.b := by
            have h4 : ((c.2 + 1 : ℤ) : ZMod 2) = (c.2 : ZMod 2) + 1 := by
              push_cast
              rcases hkey (c.2 : ZMod 2) with h | h <;> rw [h] <;> decide
            rw [h4, hpar]
            rcases hkey W.b with h | h <;> rw [h] <;> decide
          exact ⟨(c.1, c.2 + 1), by rw [← e1]; exact h1, by rw [← e2]; exact h2, hnb1, hnb2, hpar2⟩
        · exact ⟨c, h1, h2, hcb, hcm0, hpar⟩
      obtain ⟨c', g1, g2, gb, gm, gpar⟩ := hA
      -- Step B: column reduction for c′
      have hcolc := hcol c' g1 g2 gb gm
      obtain ⟨hc1, hc2⟩ := hcolc
      -- Step C: neighbor-kill at c′
      have hnb1 : (c'.1 - 1, c'.2) ∉ W.boundary ∧ (c'.1 - 1, c'.2) ≠ (x₀ + 2, ym - 1) := by
        constructor
        · intro h
          rw [W.mem_boundary _] at h
          rcases h with ⟨i, hi⟩ | ⟨i, hi⟩
          · have hyk : (W.v i).2 = c'.2 := by rw [hi]
            exact gpar (hyk ▸ W.parY i)
          · rcases W.mid_cases i _ hi with ⟨hx, g1, g2 | g2⟩ | ⟨hy, g1, g2 | g2⟩
            · have hxk : (W.v i).1 = c'.1 - 1 := by
                have hc1' : ((c'.1 - 1, c'.2) : Cell).1 = c'.1 - 1 := rfl
                omega
              have hx2 : (W.v i).1 = x₀ + 1 := by rw [hc1] at hxk; omega
              exact hparx1 (hx2 ▸ W.parX i)
            · have hxk : (W.v i).1 = c'.1 - 1 := by
                have hc1' : ((c'.1 - 1, c'.2) : Cell).1 = c'.1 - 1 := rfl
                omega
              have hx2 : (W.v i).1 = x₀ + 1 := by rw [hc1] at hxk; omega
              exact hparx1 (hx2 ▸ W.parX i)
            · have hyk : (W.v i).2 = c'.2 := by
                have hc2' : ((c'.1 - 1, c'.2) : Cell).2 = c'.2 := rfl
                omega
              exact gpar (hyk ▸ W.parY i)
            · have hyk : (W.v i).2 = c'.2 := by
                have hc2' : ((c'.1 - 1, c'.2) : Cell).2 = c'.2 := rfl
                omega
              exact gpar (hyk ▸ W.parY i)
        · intro h
          have h2 : c'.1 - 1 = x₀ + 2 := by
            have h3 : ((c'.1 - 1, c'.2) : Cell).1 = ((x₀ + 2, ym - 1) : Cell).1 := by rw [h]
            exact h3
          omega
      have hb1' : c' ∉ W₁.boundary := by
        intro h
        rcases hB1 _ h with hbb | hce
        · exact gb hbb
        · exact gm hce
      have hb2' : c' ∉ W₂.boundary := by
        intro h
        rcases hB2 _ h with hbb | hce
        · exact gb hbb
        · exact gm hce
      have hnb1' : (c'.1 - 1, c'.2) ∉ W₁.boundary := by
        intro h
        rcases hB1 _ h with hbb | hce
        · exact hnb1.1 hbb
        · exact hnb1.2 hce
      have hnb2' : (c'.1 - 1, c'.2) ∉ W₂.boundary := by
        intro h
        rcases hB2 _ h with hbb | hce
        · exact hnb1.1 hbb
        · exact hnb1.2 hce
      have hstep : (((c'.1 - 1, c'.2) : Cell).1 = c'.1 - 1 ∧ ((c'.1 - 1, c'.2) : Cell).2 = c'.2) :=
        ⟨rfl, rfl⟩
      have hstep3 : (((c'.1 - 1, c'.2) : Cell).1 = c'.1 + 1 ∧ ((c'.1 - 1, c'.2) : Cell).2 = c'.2) ∨
        (((c'.1 - 1, c'.2) : Cell).1 = c'.1 - 1 ∧ ((c'.1 - 1, c'.2) : Cell).2 = c'.2) ∨
        (((c'.1 - 1, c'.2) : Cell).1 = c'.1 ∧ ((c'.1 - 1, c'.2) : Cell).2 = c'.2 + 1) ∨
        (((c'.1 - 1, c'.2) : Cell).1 = c'.1 ∧ ((c'.1 - 1, c'.2) : Cell).2 = c'.2 - 1) :=
        Or.inr (Or.inl hstep)
      have e1 := W₁.p2_eq_of_unit_step hstep3 hb1' hnb1'
      have e2 := W₂.p2_eq_of_unit_step hstep3 hb2' hnb2'
      have hcoln := hcol (c'.1 - 1, c'.2) (by rw [← e1]; exact g1) (by rw [← e2]; exact g2)
        hnb1.1 hnb1.2
      have habs : c'.1 - 1 = x₀ + 2 := hcoln.1
      omega
    -- (f) the interior-set equation
    have hbW1_aux : ∀ c : Cell, W₁.p2 c = 1 → c ∉ W₁.boundary → c ∉ W.boundary := by
      intro c hp hb h
      rw [W.mem_boundary c] at h
      rcases h with ⟨i, hi⟩ | ⟨i, hi⟩
      · by_cases hcase : 1 ≤ (i : ℕ) ∧ (i : ℕ) ≤ (k : ℕ)
        · have hve : W₁.v ⟨(i : ℕ) - 1, by omega⟩ = c := by
            show W.v ⟨(⟨(i : ℕ) - 1, by omega⟩ : Fin ((k : ℕ) - 4 + 4)).val + 1, by omega⟩ = c
            have e : (⟨(⟨(i : ℕ) - 1, by omega⟩ : Fin ((k : ℕ) - 4 + 4)).val + 1, by omega⟩ :
                Fin (W.n + 4)) = i := by
              apply Fin.ext
              show (⟨(i : ℕ) - 1, by omega⟩ : Fin ((k : ℕ) - 4 + 4)).val + 1 = ↑i
              have hv1 : ((⟨(i : ℕ) - 1, by omega⟩ : Fin ((k : ℕ) - 4 + 4)) : ℕ) = (i : ℕ) - 1 := rfl
              rw [hv1]
              omega
            rw [e]
            exact hi
          exact hb (by rw [← hve]; exact W₁.vertex_mem_boundary _)
        · push_neg at hcase
          have hi2 : (i : ℕ) = 0 ∨ (k : ℕ) < (i : ℕ) := by
            by_cases h1 : 1 ≤ (i : ℕ)
            · exact Or.inr (hcase h1)
            · exact Or.inl (by omega)
          have h0c : W₁.p2 c = 0 := by
            have hm : (i : ℕ) = 0 ∨ (k : ℕ) ≤ (i : ℕ) := by
              rcases hi2 with h | h
              · exact Or.inl h
              · exact Or.inr (by omega)
            apply hchain2 i hm c (by
              rw [← hi]
              exact W.vertex_mem_edgePts i i |>.mpr (Or.inl rfl))
            · intro hce3
              have hiv : i = 1 := hj1 i (by rw [hi]; exact hce3)
              have hv := congrArg Fin.val hiv
              rw [val_one_fin] at hv
              omega
            · intro hce3
              have hiv : i = k := hjr i (by rw [hi]; exact hce3)
              rw [hiv] at hi2
              omega
          rw [h0c] at hp
          exact absurd hp (by decide)
      · by_cases hcase : 1 ≤ (i : ℕ) ∧ (i : ℕ) ≤ (k : ℕ) - 1
        · have hme : W₁.mid ⟨(i : ℕ) - 1, by omega⟩ = c := by
            rw [hmid1W _ (by
              intro h
              have hv := congrArg Fin.val h
              rw [Fin.val_last] at hv
              have hv1 : ((⟨(i : ℕ) - 1, by omega⟩ : Fin ((k : ℕ) - 4 + 4)) : ℕ) = (i : ℕ) - 1 := rfl
              rw [hv1] at hv
              omega)]
            have e : (⟨(⟨(i : ℕ) - 1, by omega⟩ : Fin ((k : ℕ) - 4 + 4)).val + 1, by omega⟩ :
                Fin (W.n + 4)) = i := by
              apply Fin.ext
              show (⟨(i : ℕ) - 1, by omega⟩ : Fin ((k : ℕ) - 4 + 4)).val + 1 = ↑i
              have hv1 : ((⟨(i : ℕ) - 1, by omega⟩ : Fin ((k : ℕ) - 4 + 4)) : ℕ) = (i : ℕ) - 1 := rfl
              rw [hv1]
              omega
            rw [e]
            exact hi
          exact hb (by rw [← hme]; exact W₁.mid_mem_boundary _)
        · push_neg at hcase
          have hi2 : (i : ℕ) = 0 ∨ (k : ℕ) ≤ (i : ℕ) := by
            by_cases h1 : 1 ≤ (i : ℕ)
            · exact Or.inr (by have h2 := hcase h1; omega)
            · exact Or.inl (by omega)
          have h0c : W₁.p2 c = 0 := by
            apply hchain2 i hi2 c (by rw [← hi]; exact W.mid_mem_edgePts i)
            · intro hce3
              exact (W.vertex_ne_mid 1 i) (h1.trans (hce3.symm.trans hi.symm))
            · intro hce3
              exact (W.vertex_ne_mid k i) (hk.trans (hce3.symm.trans hi.symm))
          rw [h0c] at hp
          exact absurd hp (by decide)
    have hbW2_aux : ∀ c : Cell, W₂.p2 c = 1 → c ∉ W₂.boundary → c ∉ W.boundary := by
      intro c hp hb h
      rw [W.mem_boundary c] at h
      rcases h with ⟨i, hi⟩ | ⟨i, hi⟩
      · by_cases hcase : (i : ℕ) ≤ 1 ∨ (k : ℕ) ≤ (i : ℕ)
        · have hve : c ∈ W₂.boundary := by
            rw [← hi]
            rcases hcase with h | h
            · by_cases hi0 : (i : ℕ) = 0
              · have hve : W₂.v ⟨W.n + 4 - (k : ℕ), by omega⟩ = W.v i := by
                  show W.v ⟨((⟨W.n + 4 - (k : ℕ), by omega⟩ : Fin (W₂.n + 4)).val + k) % (W.n + 4),
                      Nat.mod_lt _ (by omega)⟩ = W.v i
                  have e : (⟨((⟨W.n + 4 - (k : ℕ), by omega⟩ : Fin (W₂.n + 4)).val + k) % (W.n + 4),
                      Nat.mod_lt _ (by omega)⟩ : Fin (W.n + 4)) = i := by
                    apply Fin.ext
                    show ((⟨W.n + 4 - (k : ℕ), by omega⟩ : Fin (W₂.n + 4)).val + k) % (W.n + 4) = ↑i
                    have hv1 : ((⟨W.n + 4 - (k : ℕ), by omega⟩ : Fin (W₂.n + 4)) : ℕ) =
                      W.n + 4 - (k : ℕ) := rfl
                    rw [hv1, hi0]
                    have e2 : W.n + 4 - (k : ℕ) + k = W.n + 4 := by omega
                    rw [e2, Nat.mod_self]
                  rw [e]
                rw [← hve]
                exact W₂.vertex_mem_boundary _
              · have hi1 : (i : ℕ) = 1 := by omega
                have hve : W₂.v ⟨W.n + 5 - (k : ℕ), by omega⟩ = W.v i := by
                  have e : (⟨W.n + 5 - (k : ℕ), by omega⟩ : Fin (W₂.n + 4)) =
                      Fin.last (W.n + 2 - (k : ℕ) + 3) := by
                    apply Fin.ext
                    show W.n + 5 - (k : ℕ) = ((Fin.last (W.n + 2 - (k : ℕ) + 3)) : ℕ)
                    rw [Fin.val_last]
                    omega
                  rw [e, hW₂last]
                  have hi1' : i = 1 := Fin.ext (by rw [hi1, val_one_fin])
                  have e2 : W.v 1 = W.v i := by rw [hi1']
                  exact h1.symm.trans e2
                rw [← hve]
                exact W₂.vertex_mem_boundary _
            · have hve : W₂.v ⟨(i : ℕ) - (k : ℕ), by omega⟩ = W.v i := by
                show W.v ⟨((⟨(i : ℕ) - (k : ℕ), by omega⟩ : Fin (W₂.n + 4)).val + k) % (W.n + 4),
                    Nat.mod_lt _ (by omega)⟩ = W.v i
                have e : (⟨((⟨(i : ℕ) - (k : ℕ), by omega⟩ : Fin (W₂.n + 4)).val + k) % (W.n + 4),
                    Nat.mod_lt _ (by omega)⟩ : Fin (W.n + 4)) = i := by
                  apply Fin.ext
                  show ((⟨(i : ℕ) - (k : ℕ), by omega⟩ : Fin (W₂.n + 4)).val + k) % (W.n + 4) = ↑i
                  have hv1 : ((⟨(i : ℕ) - (k : ℕ), by omega⟩ : Fin (W₂.n + 4)) : ℕ) =
                    (i : ℕ) - (k : ℕ) := rfl
                  rw [hv1]
                  have e2 : (i : ℕ) - (k : ℕ) + k = i := by omega
                  rw [e2]
                  exact Nat.mod_eq_of_lt i.isLt
                rw [e]
              rw [← hve]
              exact W₂.vertex_mem_boundary _
          exact hb hve
        · push_neg at hcase
          have h0c : W₂.p2 c = 0 := by
            apply hchain1 i (by omega) (by omega) c (by
              rw [← hi]
              exact W.vertex_mem_edgePts i i |>.mpr (Or.inl rfl))
            · intro hce3
              have hiv : i = 1 := hj1 i (by rw [hi]; exact hce3)
              have hv := congrArg Fin.val hiv
              rw [val_one_fin] at hv
              omega
            · intro hce3
              have hiv : i = k := hjr i (by rw [hi]; exact hce3)
              rw [hiv] at hcase
              omega
          rw [h0c] at hp
          exact absurd hp (by decide)
      · by_cases hcase : (i : ℕ) = 0 ∨ (k : ℕ) ≤ (i : ℕ)
        · have hme : c ∈ W₂.boundary := by
            rw [← hi]
            rcases hcase with h | h
            · have hme : W₂.mid ⟨W.n + 4 - (k : ℕ), by omega⟩ = W.mid i := by
                rw [hmid2W _ (by
                  intro h
                  have hv := congrArg Fin.val h
                  rw [Fin.val_last] at hv
                  have hv1 : ((⟨W.n + 4 - (k : ℕ), by omega⟩ : Fin (W₂.n + 4)) : ℕ) =
                    W.n + 4 - (k : ℕ) := rfl
                  rw [hv1] at hv
                  omega)]
                have e : (⟨((⟨W.n + 4 - (k : ℕ), by omega⟩ : Fin (W₂.n + 4)).val + k) % (W.n + 4),
                    Nat.mod_lt _ (by omega)⟩ : Fin (W.n + 4)) = i := by
                  apply Fin.ext
                  show ((⟨W.n + 4 - (k : ℕ), by omega⟩ : Fin (W₂.n + 4)).val + k) % (W.n + 4) = ↑i
                  have hv1 : ((⟨W.n + 4 - (k : ℕ), by omega⟩ : Fin (W₂.n + 4)) : ℕ) =
                    W.n + 4 - (k : ℕ) := rfl
                  rw [hv1, h]
                  have e2 : W.n + 4 - (k : ℕ) + k = W.n + 4 := by omega
                  rw [e2, Nat.mod_self]
                rw [e]
              rw [← hme]
              exact W₂.mid_mem_boundary _
            · have hme : W₂.mid ⟨(i : ℕ) - (k : ℕ), by omega⟩ = W.mid i := by
                rw [hmid2W _ (by
                  intro h2
                  have hv := congrArg Fin.val h2
                  rw [Fin.val_last] at hv
                  have hv1 : ((⟨(i : ℕ) - (k : ℕ), by omega⟩ : Fin (W₂.n + 4)) : ℕ) =
                    (i : ℕ) - (k : ℕ) := rfl
                  rw [hv1] at hv
                  omega)]
                have e : (⟨((⟨(i : ℕ) - (k : ℕ), by omega⟩ : Fin (W₂.n + 4)).val + k) % (W.n + 4),
                    Nat.mod_lt _ (by omega)⟩ : Fin (W.n + 4)) = i := by
                  apply Fin.ext
                  show ((⟨(i : ℕ) - (k : ℕ), by omega⟩ : Fin (W₂.n + 4)).val + k) % (W.n + 4) = ↑i
                  have hv1 : ((⟨(i : ℕ) - (k : ℕ), by omega⟩ : Fin (W₂.n + 4)) : ℕ) =
                    (i : ℕ) - (k : ℕ) := rfl
                  rw [hv1]
                  have e2 : (i : ℕ) - (k : ℕ) + k = i := by omega
                  rw [e2]
                  exact Nat.mod_eq_of_lt i.isLt
                rw [e]
              rw [← hme]
              exact W₂.mid_mem_boundary _
          exact hb hme
        · push_neg at hcase
          have h0c : W₂.p2 c = 0 := by
            apply hchain1 i (by omega) (by omega) c (by rw [← hi]; exact W.mid_mem_edgePts i)
            · intro hce3
              exact (W.vertex_ne_mid 1 i) (h1.trans (hce3.symm.trans hi.symm))
            · intro hce3
              exact (W.vertex_ne_mid k i) (hk.trans (hce3.symm.trans hi.symm))
          rw [h0c] at hp
          exact absurd hp (by decide)
    have hset : W.box.filter (fun c => W.p2 c = 1 ∧ c ∉ W.boundary) =
        W₁.box.filter (fun c => W₁.p2 c = 1 ∧ c ∉ W₁.boundary) ∪
        (W₂.box.filter (fun c => W₂.p2 c = 1 ∧ c ∉ W₂.boundary) ∪
        ({(x₀ + 2, ym - 1)} : Finset Cell)) := by
      apply Finset.ext
      intro c
      simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_singleton]
      constructor
      · rintro ⟨hbox, hp, hb⟩
        have hf := hflip c
        rw [hp] at hf
        rcases hkey (W₁.p2 c) with h1' | h1'
        · rw [h1', zero_add] at hf
          right
          left
          have hb2 : c ∉ W₂.boundary := by
            intro h
            rcases hB2 c h with hbb | hce
            · exact hb hbb
            · rw [hce] at h1'
              have hm : W₁.p2 (x₀ + 2, ym - 1) = 1 := by
                have hb3 := W₁.p2_band (x₀ + 2) (ym - 2) hh2'
                rw [show ym - 2 + 1 = (ym - 1 : ℤ) from by ring] at hb3
                rw [← hb3]
                exact hev1
              rw [hm] at h1'
              exact absurd h1' (by decide)
          have hbox2 : c ∈ W₂.box := W₂.mem_box_of_inside hf.symm
          exact ⟨hbox2, hf.symm, hb2⟩
        · by_cases hcm : c = (x₀ + 2, ym - 1)
          · exact Or.inr (Or.inr hcm)
          · left
            have hb1 : c ∉ W₁.boundary := by
              intro h
              rcases hB1 c h with hbb | hce
              · exact hb hbb
              · exact hcm hce
            have hbox1 : c ∈ W₁.box := W₁.mem_box_of_inside h1'
            exact ⟨hbox1, h1', hb1⟩
      · rintro (⟨hbox, hp, hb⟩ | ⟨hbox, hp, hb⟩ | hce)
        · have hp2 : W₂.p2 c = 0 := by
            by_contra h2'
            have h2'' : W₂.p2 c = 1 := by
              rcases hkey (W₂.p2 c) with h0' | h1'
              · exact absurd h0' h2'
              · exact h1'
            rcases hBad c hp h2'' with hbb | hce2
            · exact hbW1_aux c hp hb hbb
            · exact hb (by rw [hce2]; exact hm01)
          have hpW : W.p2 c = 1 := by
            have h := hflip c
            rw [hp, hp2] at h
            exact h
          have hbW : c ∉ W.boundary := hbW1_aux c hp hb
          have hboxW : c ∈ W.box := W.mem_box_of_inside hpW
          exact ⟨hboxW, hpW, hbW⟩
        · have hp1 : W₁.p2 c = 0 := by
            by_contra h1'
            have h1'' : W₁.p2 c = 1 := by
              rcases hkey (W₁.p2 c) with h0' | h1'
              · exact absurd h0' h1'
              · exact h1'
            rcases hBad c h1'' hp with hbb | hce2
            · exact hbW2_aux c hp hb hbb
            · exact hb (by rw [hce2]; exact hm02)
          have hpW : W.p2 c = 1 := by
            have h := hflip c
            rw [hp1, hp] at h
            exact h
          have hbW : c ∉ W.boundary := hbW2_aux c hp hb
          have hboxW : c ∈ W.box := W.mem_box_of_inside hpW
          exact ⟨hboxW, hpW, hbW⟩
        · rw [hce]
          have hboxm : (x₀ + 2, ym - 1) ∈ W.box := W.mem_box_of_inside hevm0
          exact ⟨hboxm, hevm0, hm0W⟩
    have hdisj1 : Disjoint (W₁.box.filter fun c => W₁.p2 c = 1 ∧ c ∉ W₁.boundary)
        (W₂.box.filter fun c => W₂.p2 c = 1 ∧ c ∉ W₂.boundary) := by
      rw [Finset.disjoint_left]
      intro c hc1 hc2
      rw [Finset.mem_filter] at hc1 hc2
      rcases hBad c hc1.2.1 hc2.2.1 with hbb | hce
      · exact hbW1_aux c hc1.2.1 hc1.2.2 hbb
      · exact hc1.2.2 (by rw [hce]; exact hm01)
    have hdisj2 : Disjoint ((W₁.box.filter fun c => W₁.p2 c = 1 ∧ c ∉ W₁.boundary) ∪
        (W₂.box.filter fun c => W₂.p2 c = 1 ∧ c ∉ W₂.boundary))
        ({(x₀ + 2, ym - 1)} : Finset Cell) := by
      rw [Finset.disjoint_left]
      intro c hc1 hc2
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter] at hc1
      rw [Finset.mem_singleton] at hc2
      rcases hc1 with hc1 | hc1
      · rw [hc2] at hc1
        exact hc1.2.2 hm01
      · rw [hc2] at hc1
        exact hc1.2.2 hm02
    have hcard : (W.box.filter fun c => W.p2 c = 1 ∧ c ∉ W.boundary).card =
        (W₁.box.filter fun c => W₁.p2 c = 1 ∧ c ∉ W₁.boundary).card +
        (W₂.box.filter fun c => W₂.p2 c = 1 ∧ c ∉ W₂.boundary).card + 1 := by
      rw [hset, ← Finset.union_assoc, Finset.card_union_of_disjoint hdisj2,
        Finset.card_union_of_disjoint hdisj1, Finset.card_singleton]
    rw [W.I_eq, W₁.I_eq, W₂.I_eq, hcard]
  · -- T: W.T = W₁.T + W₂.T
    let wW : ℕ → ℤ := fun i =>
      if h : i < W.n + 4 then (W.v ⟨i, h⟩).1 * (W.v ⟨(i + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩).2 -
        (W.v ⟨(i + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩).1 * (W.v ⟨i, h⟩).2 else 0
    let wW₁ : ℕ → ℤ := fun j =>
      if h : j < W₁.n + 4 then (W₁.v ⟨j, h⟩).1 * (W₁.v ⟨(j + 1) % (W₁.n + 4), Nat.mod_lt _ (by omega)⟩).2 -
        (W₁.v ⟨(j + 1) % (W₁.n + 4), Nat.mod_lt _ (by omega)⟩).1 * (W₁.v ⟨j, h⟩).2 else 0
    let wW₂ : ℕ → ℤ := fun j =>
      if h : j < W₂.n + 4 then (W₂.v ⟨j, h⟩).1 * (W₂.v ⟨(j + 1) % (W₂.n + 4), Nat.mod_lt _ (by omega)⟩).2 -
        (W₂.v ⟨(j + 1) % (W₂.n + 4), Nat.mod_lt _ (by omega)⟩).1 * (W₂.v ⟨j, h⟩).2 else 0
    have hwW : ∀ i : Fin (W.n + 4), W.x i * W.y (i + 1) - W.x (i + 1) * W.y i = wW ↑i := by
      intro i
      have hi : ↑i < W.n + 4 := i.isLt
      have h1 : (⟨(↑i + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ : Fin (W.n + 4)) = i + 1 := by
        apply Fin.ext
        rw [Fin.val_add, Fin.val_one']
        have h1m : 1 % (W.n + 4) = 1 := Nat.mod_eq_of_lt (by omega)
        rw [h1m]
      have hi2 : (⟨↑i, hi⟩ : Fin (W.n + 4)) = i := Fin.ext rfl
      show W.x i * W.y (i + 1) - W.x (i + 1) * W.y i =
        if h : ↑i < W.n + 4 then (W.v ⟨↑i, h⟩).1 * (W.v ⟨(↑i + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩).2 -
          (W.v ⟨(↑i + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩).1 * (W.v ⟨↑i, h⟩).2 else 0
      rw [dif_pos hi, hi2, h1, OrthoLoop.x, OrthoLoop.y]
    have hwW₁ : ∀ j : Fin (W₁.n + 4), W₁.x j * W₁.y (j + 1) - W₁.x (j + 1) * W₁.y j = wW₁ ↑j := by
      intro j
      have hj : ↑j < W₁.n + 4 := j.isLt
      have h1 : (⟨(↑j + 1) % (W₁.n + 4), Nat.mod_lt _ (by omega)⟩ : Fin (W₁.n + 4)) = j + 1 := by
        apply Fin.ext
        rw [Fin.val_add, Fin.val_one']
        have h1m : 1 % (W₁.n + 4) = 1 := Nat.mod_eq_of_lt (by rw [hW1n]; omega)
        rw [h1m]
      have hj2 : (⟨↑j, hj⟩ : Fin (W₁.n + 4)) = j := Fin.ext rfl
      show W₁.x j * W₁.y (j + 1) - W₁.x (j + 1) * W₁.y j =
        if h : ↑j < W₁.n + 4 then (W₁.v ⟨↑j, h⟩).1 * (W₁.v ⟨(↑j + 1) % (W₁.n + 4), Nat.mod_lt _ (by omega)⟩).2 -
          (W₁.v ⟨(↑j + 1) % (W₁.n + 4), Nat.mod_lt _ (by omega)⟩).1 * (W₁.v ⟨↑j, h⟩).2 else 0
      rw [dif_pos hj, hj2, h1, OrthoLoop.x, OrthoLoop.y]
    have hwW₂ : ∀ j : Fin (W₂.n + 4), W₂.x j * W₂.y (j + 1) - W₂.x (j + 1) * W₂.y j = wW₂ ↑j := by
      intro j
      have hj : ↑j < W₂.n + 4 := j.isLt
      have h1 : (⟨(↑j + 1) % (W₂.n + 4), Nat.mod_lt _ (by omega)⟩ : Fin (W₂.n + 4)) = j + 1 := by
        apply Fin.ext
        rw [Fin.val_add, Fin.val_one']
        have h1m : 1 % (W₂.n + 4) = 1 := Nat.mod_eq_of_lt (by rw [hW2n]; omega)
        rw [h1m]
      have hj2 : (⟨↑j, hj⟩ : Fin (W₂.n + 4)) = j := Fin.ext rfl
      show W₂.x j * W₂.y (j + 1) - W₂.x (j + 1) * W₂.y j =
        if h : ↑j < W₂.n + 4 then (W₂.v ⟨↑j, h⟩).1 * (W₂.v ⟨(↑j + 1) % (W₂.n + 4), Nat.mod_lt _ (by omega)⟩).2 -
          (W₂.v ⟨(↑j + 1) % (W₂.n + 4), Nat.mod_lt _ (by omega)⟩).1 * (W₂.v ⟨↑j, h⟩).2 else 0
      rw [dif_pos hj, hj2, h1, OrthoLoop.x, OrthoLoop.y]
    have hshift1 : ∀ j : ℕ, j < (k : ℕ) - 1 → wW₁ j = wW (j + 1) := by
      intro j hj
      have hjW : j + 1 < W.n + 4 := by omega
      have hjW₁ : j < W₁.n + 4 := by rw [hW1n]; omega
      show (if h : j < W₁.n + 4 then (W₁.v ⟨j, h⟩).1 * (W₁.v ⟨(j + 1) % (W₁.n + 4), Nat.mod_lt _ (by omega)⟩).2 -
          (W₁.v ⟨(j + 1) % (W₁.n + 4), Nat.mod_lt _ (by omega)⟩).1 * (W₁.v ⟨j, h⟩).2 else 0)
        = if h : j + 1 < W.n + 4 then (W.v ⟨j + 1, h⟩).1 * (W.v ⟨(j + 1 + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩).2 -
          (W.v ⟨(j + 1 + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩).1 * (W.v ⟨j + 1, h⟩).2 else 0
      rw [dif_pos hjW₁, dif_pos hjW]
      have e1 : W₁.v ⟨j, hjW₁⟩ = W.v ⟨j + 1, hjW⟩ := rfl
      have e2 : W₁.v ⟨(j + 1) % (W₁.n + 4), Nat.mod_lt _ (by omega)⟩ =
          W.v ⟨(j + 1 + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ := by
        have hm : W₁.n + 4 = (k : ℕ) := by rw [hW1n]; omega
        have e2a : (⟨(j + 1) % (W₁.n + 4), Nat.mod_lt _ (by omega)⟩ : Fin (W₁.n + 4)) =
            ⟨j + 1, by omega⟩ := by
          apply Fin.ext
          show (j + 1) % (W₁.n + 4) = j + 1
          rw [hm]
          exact Nat.mod_eq_of_lt (by omega)
        have e2b : (⟨(j + 1 + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ : Fin (W.n + 4)) =
            ⟨j + 2, by omega⟩ := by
          apply Fin.ext
          show (j + 1 + 1) % (W.n + 4) = j + 2
          exact Nat.mod_eq_of_lt (by omega)
        rw [e2a, e2b]
      rw [e1, e2]
    have hchord1 : wW₁ ((k : ℕ) - 1) = (x₀ + 2) * ym - (x₀ + 2) * (ym - 2) := by
      have hj : (k : ℕ) - 1 < W₁.n + 4 := by rw [hW1n]; omega
      show (if h : (k : ℕ) - 1 < W₁.n + 4 then (W₁.v ⟨(k : ℕ) - 1, h⟩).1 *
          (W₁.v ⟨((k : ℕ) - 1 + 1) % (W₁.n + 4), Nat.mod_lt _ (by omega)⟩).2 -
          (W₁.v ⟨((k : ℕ) - 1 + 1) % (W₁.n + 4), Nat.mod_lt _ (by omega)⟩).1 *
          (W₁.v ⟨(k : ℕ) - 1, h⟩).2 else 0) = _
      rw [dif_pos hj]
      have e1 : W₁.v ⟨(k : ℕ) - 1, hj⟩ = (x₀ + 2, ym - 2) := by
        have elast : (⟨(k : ℕ) - 1, hj⟩ : Fin (W₁.n + 4)) = Fin.last ((k : ℕ) - 4 + 3) := by
          apply Fin.ext
          show (k : ℕ) - 1 = ((Fin.last ((k : ℕ) - 4 + 3)) : ℕ)
          rw [Fin.val_last]
          omega
        rw [elast, hW₁last]
      have e2 : W₁.v ⟨((k : ℕ) - 1 + 1) % (W₁.n + 4), Nat.mod_lt _ (by omega)⟩ = (x₀ + 2, ym) := by
        have hm : W₁.n + 4 = (k : ℕ) := by rw [hW1n]; omega
        have hmod : ((k : ℕ) - 1 + 1) % (W₁.n + 4) = 0 := by
          rw [hm]
          have e : (k : ℕ) - 1 + 1 = (k : ℕ) := by omega
          rw [e, Nat.mod_self]
        have e2a : (⟨((k : ℕ) - 1 + 1) % (W₁.n + 4), Nat.mod_lt _ (by omega)⟩ : Fin (W₁.n + 4)) = 0 := by
          apply Fin.ext
          show ((k : ℕ) - 1 + 1) % (W₁.n + 4) = ((0 : Fin (W₁.n + 4)) : ℕ)
          rw [val_zero_fin]
          exact hmod
        rw [e2a, hW₁zero]
      rw [e1, e2]
    have hshift2 : ∀ j : ℕ, j < W.n + 4 - (k : ℕ) → wW₂ j = wW (j + (k : ℕ)) := by
      intro j hj
      have hjW : j + (k : ℕ) < W.n + 4 := by omega
      have hjW₂ : j < W₂.n + 4 := by rw [hW2n]; omega
      show (if h : j < W₂.n + 4 then (W₂.v ⟨j, h⟩).1 * (W₂.v ⟨(j + 1) % (W₂.n + 4), Nat.mod_lt _ (by omega)⟩).2 -
          (W₂.v ⟨(j + 1) % (W₂.n + 4), Nat.mod_lt _ (by omega)⟩).1 * (W₂.v ⟨j, h⟩).2 else 0)
        = if h : j + (k : ℕ) < W.n + 4 then (W.v ⟨j + (k : ℕ), h⟩).1 *
          (W.v ⟨(j + (k : ℕ) + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩).2 -
          (W.v ⟨(j + (k : ℕ) + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩).1 * (W.v ⟨j + (k : ℕ), h⟩).2 else 0
      rw [dif_pos hjW₂, dif_pos hjW]
      have e1 : W₂.v ⟨j, hjW₂⟩ = W.v ⟨j + (k : ℕ), hjW⟩ := by
        show W.v ⟨((⟨j, hjW₂⟩ : Fin (W₂.n + 4)).val + k) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ =
          W.v ⟨j + (k : ℕ), hjW⟩
        have e1a : (⟨((⟨j, hjW₂⟩ : Fin (W₂.n + 4)).val + k) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ :
            Fin (W.n + 4)) = ⟨j + (k : ℕ), hjW⟩ := by
          apply Fin.ext
          show ((⟨j, hjW₂⟩ : Fin (W₂.n + 4)).val + k) % (W.n + 4) = j + (k : ℕ)
          have hv1 : ((⟨j, hjW₂⟩ : Fin (W₂.n + 4)) : ℕ) = j := rfl
          rw [hv1]
          exact Nat.mod_eq_of_lt hjW
        rw [e1a]
      have e2 : W₂.v ⟨(j + 1) % (W₂.n + 4), Nat.mod_lt _ (by omega)⟩ =
          W.v ⟨(j + (k : ℕ) + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ := by
        have hm : W₂.n + 4 = W.n + 6 - (k : ℕ) := by rw [hW2n]; omega
        have e2a : (⟨(j + 1) % (W₂.n + 4), Nat.mod_lt _ (by omega)⟩ : Fin (W₂.n + 4)) =
            ⟨j + 1, by omega⟩ := by
          apply Fin.ext
          show (j + 1) % (W₂.n + 4) = j + 1
          rw [hm]
          exact Nat.mod_eq_of_lt (by omega)
        rw [e2a]
        show W.v ⟨((⟨j + 1, by omega⟩ : Fin (W₂.n + 4)).val + k) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ =
          W.v ⟨(j + (k : ℕ) + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩
        have e2b : (⟨((⟨j + 1, by omega⟩ : Fin (W₂.n + 4)).val + k) % (W.n + 4),
            Nat.mod_lt _ (by omega)⟩ : Fin (W.n + 4)) =
            ⟨(j + (k : ℕ) + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ := by
          apply Fin.ext
          show ((⟨j + 1, by omega⟩ : Fin (W₂.n + 4)).val + k) % (W.n + 4) =
            (j + (k : ℕ) + 1) % (W.n + 4)
          have hv1 : ((⟨j + 1, by omega⟩ : Fin (W₂.n + 4)) : ℕ) = j + 1 := rfl
          rw [hv1]
          have hsum : j + 1 + k = j + (k : ℕ) + 1 := by omega
          rw [hsum]
        rw [e2b]
      rw [e1, e2]
    have hwrap2 : wW₂ (W.n + 4 - (k : ℕ)) = wW 0 := by
      have hj : W.n + 4 - (k : ℕ) < W₂.n + 4 := by rw [hW2n]; omega
      have h0lt : 0 < W.n + 4 := by omega
      show (if h : W.n + 4 - (k : ℕ) < W₂.n + 4 then (W₂.v ⟨W.n + 4 - (k : ℕ), h⟩).1 *
          (W₂.v ⟨(W.n + 4 - (k : ℕ) + 1) % (W₂.n + 4), Nat.mod_lt _ (by omega)⟩).2 -
          (W₂.v ⟨(W.n + 4 - (k : ℕ) + 1) % (W₂.n + 4), Nat.mod_lt _ (by omega)⟩).1 *
          (W₂.v ⟨W.n + 4 - (k : ℕ), h⟩).2 else 0)
        = if h : 0 < W.n + 4 then (W.v ⟨0, h⟩).1 * (W.v ⟨(0 + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩).2 -
          (W.v ⟨(0 + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩).1 * (W.v ⟨0, h⟩).2 else 0
      rw [dif_pos hj, dif_pos h0lt]
      have e1 : W₂.v ⟨W.n + 4 - (k : ℕ), hj⟩ = W.v ⟨0, h0lt⟩ := by
        show W.v ⟨((⟨W.n + 4 - (k : ℕ), hj⟩ : Fin (W₂.n + 4)).val + k) % (W.n + 4),
            Nat.mod_lt _ (by omega)⟩ = W.v ⟨0, h0lt⟩
        have e1a : (⟨((⟨W.n + 4 - (k : ℕ), hj⟩ : Fin (W₂.n + 4)).val + k) % (W.n + 4),
            Nat.mod_lt _ (by omega)⟩ : Fin (W.n + 4)) = ⟨0, h0lt⟩ := by
          apply Fin.ext
          show ((⟨W.n + 4 - (k : ℕ), hj⟩ : Fin (W₂.n + 4)).val + k) % (W.n + 4) = (0 : ℕ)
          have hv1 : ((⟨W.n + 4 - (k : ℕ), hj⟩ : Fin (W₂.n + 4)) : ℕ) = W.n + 4 - (k : ℕ) := rfl
          rw [hv1]
          have e : W.n + 4 - (k : ℕ) + k = W.n + 4 := by omega
          rw [e, Nat.mod_self]
        rw [e1a]
      have e2 : W₂.v ⟨(W.n + 4 - (k : ℕ) + 1) % (W₂.n + 4), Nat.mod_lt _ (by omega)⟩ =
          W.v ⟨(0 + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ := by
        have hm : W₂.n + 4 = W.n + 6 - (k : ℕ) := by rw [hW2n]; omega
        have hmod : (W.n + 4 - (k : ℕ) + 1) % (W₂.n + 4) = W.n + 5 - (k : ℕ) := by
          rw [hm]
          have e : W.n + 4 - (k : ℕ) + 1 = W.n + 5 - (k : ℕ) := by omega
          rw [e]
          exact Nat.mod_eq_of_lt (by omega)
        have e2a : (⟨(W.n + 4 - (k : ℕ) + 1) % (W₂.n + 4), Nat.mod_lt _ (by omega)⟩ :
            Fin (W₂.n + 4)) = ⟨W.n + 5 - (k : ℕ), by omega⟩ := by
          apply Fin.ext
          show (W.n + 4 - (k : ℕ) + 1) % (W₂.n + 4) = W.n + 5 - (k : ℕ)
          exact hmod
        rw [e2a]
        show W.v ⟨((⟨W.n + 5 - (k : ℕ), by omega⟩ : Fin (W₂.n + 4)).val + k) % (W.n + 4),
            Nat.mod_lt _ (by omega)⟩ = _
        have e2b : (⟨((⟨W.n + 5 - (k : ℕ), by omega⟩ : Fin (W₂.n + 4)).val + k) % (W.n + 4),
            Nat.mod_lt _ (by omega)⟩ : Fin (W.n + 4)) =
            ⟨(0 + 1) % (W.n + 4), Nat.mod_lt _ (by omega)⟩ := by
          apply Fin.ext
          show ((⟨W.n + 5 - (k : ℕ), by omega⟩ : Fin (W₂.n + 4)).val + k) % (W.n + 4) =
            (0 + 1) % (W.n + 4)
          have hv1 : ((⟨W.n + 5 - (k : ℕ), by omega⟩ : Fin (W₂.n + 4)) : ℕ) = W.n + 5 - (k : ℕ) := rfl
          rw [hv1]
          have e : W.n + 5 - (k : ℕ) + k = W.n + 5 := by omega
          rw [e]
          have e2 : W.n + 5 = 1 + (W.n + 4) := by omega
          rw [e2, Nat.add_mod_right, Nat.zero_add]
        rw [e2b]
      rw [e1, e2]
    have hchord2 : wW₂ (W.n + 5 - (k : ℕ)) = (x₀ + 2) * (ym - 2) - (x₀ + 2) * ym := by
      have hj : W.n + 5 - (k : ℕ) < W₂.n + 4 := by rw [hW2n]; omega
      show (if h : W.n + 5 - (k : ℕ) < W₂.n + 4 then (W₂.v ⟨W.n + 5 - (k : ℕ), h⟩).1 *
          (W₂.v ⟨(W.n + 5 - (k : ℕ) + 1) % (W₂.n + 4), Nat.mod_lt _ (by omega)⟩).2 -
          (W₂.v ⟨(W.n + 5 - (k : ℕ) + 1) % (W₂.n + 4), Nat.mod_lt _ (by omega)⟩).1 *
          (W₂.v ⟨W.n + 5 - (k : ℕ), h⟩).2 else 0) = _
      rw [dif_pos hj]
      have e1 : W₂.v ⟨W.n + 5 - (k : ℕ), hj⟩ = (x₀ + 2, ym) := by
        have elast : (⟨W.n + 5 - (k : ℕ), hj⟩ : Fin (W₂.n + 4)) = Fin.last (W.n + 2 - (k : ℕ) + 3) := by
          apply Fin.ext
          show W.n + 5 - (k : ℕ) = ((Fin.last (W.n + 2 - (k : ℕ) + 3)) : ℕ)
          rw [Fin.val_last]
          omega
        rw [elast, hW₂last]
      have e2 : W₂.v ⟨(W.n + 5 - (k : ℕ) + 1) % (W₂.n + 4), Nat.mod_lt _ (by omega)⟩ =
          (x₀ + 2, ym - 2) := by
        have hm : W₂.n + 4 = W.n + 6 - (k : ℕ) := by rw [hW2n]; omega
        have hmod : (W.n + 5 - (k : ℕ) + 1) % (W₂.n + 4) = 0 := by
          rw [hm]
          have e : W.n + 5 - (k : ℕ) + 1 = W.n + 6 - (k : ℕ) := by omega
          rw [e, Nat.mod_self]
        have e2a : (⟨(W.n + 5 - (k : ℕ) + 1) % (W₂.n + 4), Nat.mod_lt _ (by omega)⟩ :
            Fin (W₂.n + 4)) = 0 := by
          apply Fin.ext
          show (W.n + 5 - (k : ℕ) + 1) % (W₂.n + 4) = ((0 : Fin (W₂.n + 4)) : ℕ)
          rw [val_zero_fin]
          exact hmod
        rw [e2a, hW₂zero]
      rw [e1, e2]
    have h2W := W.two_mul_T
    have h2W₁ := W₁.two_mul_T
    have h2W₂ := W₂.two_mul_T
    have hWsum : 2 * W.T = wW 0 + (∑ i ∈ Finset.range ((k : ℕ) - 1), wW (i + 1)) +
        (∑ i ∈ Finset.range (W.n + 4 - (k : ℕ)), wW (i + (k : ℕ))) := by
      rw [h2W]
      have hss : ∑ i : Fin (W.n + 4), (W.x i * W.y (i + 1) - W.x (i + 1) * W.y i) =
          ∑ i : Fin (W.n + 4), wW ↑i := Finset.sum_congr rfl (fun i _ => hwW i)
      rw [hss, Fin.sum_univ_eq_sum_range wW (W.n + 4)]
      have hsplit : W.n + 4 = (1 + ((k : ℕ) - 1)) + (W.n + 4 - (k : ℕ)) := by omega
      conv_lhs => rw [hsplit]
      rw [Finset.sum_range_add]
      have e1 : ∑ i ∈ Finset.range (1 + ((k : ℕ) - 1)), wW i =
          wW 0 + ∑ i ∈ Finset.range ((k : ℕ) - 1), wW (i + 1) := by
        have e : 1 + ((k : ℕ) - 1) = (k : ℕ) - 1 + 1 := by omega
        rw [e, Finset.sum_range_succ', add_comm]
      have e2 : (∑ i ∈ Finset.range (W.n + 4 - (k : ℕ)), wW (1 + ((k : ℕ) - 1) + i)) =
          ∑ i ∈ Finset.range (W.n + 4 - (k : ℕ)), wW (i + (k : ℕ)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [show 1 + ((k : ℕ) - 1) + i = i + (k : ℕ) by omega]
      rw [e1, e2]
    have hW₁sum : 2 * W₁.T = (∑ i ∈ Finset.range ((k : ℕ) - 1), wW₁ i) + wW₁ ((k : ℕ) - 1) := by
      rw [h2W₁]
      have hss : ∑ j : Fin (W₁.n + 4), (W₁.x j * W₁.y (j + 1) - W₁.x (j + 1) * W₁.y j) =
          ∑ j : Fin (W₁.n + 4), wW₁ ↑j := Finset.sum_congr rfl (fun j _ => hwW₁ j)
      rw [hss, Fin.sum_univ_eq_sum_range wW₁ (W₁.n + 4)]
      have hm : W₁.n + 4 = (k : ℕ) - 1 + 1 := by rw [hW1n]; omega
      rw [hm, Finset.sum_range_succ]
    have hW₂sum : 2 * W₂.T = (∑ i ∈ Finset.range (W.n + 4 - (k : ℕ)), wW₂ i) +
        wW₂ (W.n + 4 - (k : ℕ)) + wW₂ (W.n + 5 - (k : ℕ)) := by
      rw [h2W₂]
      have hss : ∑ j : Fin (W₂.n + 4), (W₂.x j * W₂.y (j + 1) - W₂.x (j + 1) * W₂.y j) =
          ∑ j : Fin (W₂.n + 4), wW₂ ↑j := Finset.sum_congr rfl (fun j _ => hwW₂ j)
      rw [hss, Fin.sum_univ_eq_sum_range wW₂ (W₂.n + 4)]
      have hm : W₂.n + 4 = (W.n + 4 - (k : ℕ)) + 1 + 1 := by rw [hW2n]; omega
      rw [hm, Finset.sum_range_succ, Finset.sum_range_succ]
      have e : (W.n + 4 - (k : ℕ)) + 1 = W.n + 5 - (k : ℕ) := by omega
      rw [e]
    have hmid1 : (∑ i ∈ Finset.range ((k : ℕ) - 1), wW₁ i) =
        (∑ i ∈ Finset.range ((k : ℕ) - 1), wW (i + 1)) :=
      Finset.sum_congr rfl (fun j hj => hshift1 j (Finset.mem_range.mp hj))
    have hmid2 : (∑ i ∈ Finset.range (W.n + 4 - (k : ℕ)), wW₂ i) =
        (∑ i ∈ Finset.range (W.n + 4 - (k : ℕ)), wW (i + (k : ℕ))) :=
      Finset.sum_congr rfl (fun j hj => hshift2 j (Finset.mem_range.mp hj))
    have hT2 : 2 * W₁.T + 2 * W₂.T = 2 * W.T := by
      rw [hW₁sum, hW₂sum, hWsum, hmid1, hmid2, hchord1, hwrap2, hchord2]
      ring
    omega
  · -- L: W.L = W₁.L + W₂.L - 2
    have hL1 : W₁.L = (k : ℕ) - 4 + 4 := rfl
    have hL2 : W₂.L = W.n + 2 - (k : ℕ) + 4 := rfl
    show W.n + 4 = _
    omega

/-! ### The induction step -/

theorem master_step_normalized (W : OrthoLoop) (x₀ ym : ℤ)
    (h0 : W.v 0 = (x₀, ym)) (hmax : ∀ i, (W.v i).2 ≤ ym)
    (hmin : ∀ i, (W.v i).2 = ym → x₀ ≤ (W.v i).1)
    (h1 : W.v 1 = (x₀ + 2, ym)) (hn1 : W.v (-1) = (x₀, ym - 2))
    (IH : ∀ W' : OrthoLoop, W'.I < W.I → W'.P) : W.P := by
  classical
  have h1x : (W.v 1).1 = x₀ + 2 := congrArg Prod.fst h1
  have h1y : (W.v 1).2 = ym := congrArg Prod.snd h1
  have hv2 : W.v 2 = (x₀ + 4, ym) ∨ W.v 2 = (x₀ + 2, ym - 2) := by
    have e11 : (1 + 1 : Fin (W.n + 4)) = 2 := by abel
    have hstep1 := W.step 1
    rw [e11] at hstep1
    rcases hstep1 with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exfalso
      have hm : (W.v 2).2 ≤ ym := hmax 2
      omega
    · exact Or.inr (Prod.ext (by omega) (by omega))
    · exact Or.inl (Prod.ext (by omega) (by omega))
    · exfalso
      have h0x : (W.v 0).1 = x₀ := congrArg Prod.fst h0
      have h0y : (W.v 0).2 = ym := congrArg Prod.snd h0
      have hv : W.v 2 = W.v 0 := Prod.ext (by omega) (by omega)
      have h20 := W.inj hv
      exact absurd h20 two_ne_zero_fin
  rcases hv2 with h2 | h2
  · -- v 2 = (x₀ + 4, ym): pinch or push
    by_cases hr : ∃ i, W.v i = (x₀ + 2, ym - 2)
    · obtain ⟨k, hk⟩ := hr
      have hk0 : k ≠ 0 := by
        intro hke
        rw [hke, h0] at hk
        have := (Prod.mk.injEq ..).mp hk
        omega
      have hk1 : k ≠ 1 := by
        intro hke
        rw [hke, h1] at hk
        have := (Prod.mk.injEq ..).mp hk
        omega
      have hk2 : k ≠ 2 := by
        intro hke
        rw [hke, h2] at hk
        have := (Prod.mk.injEq ..).mp hk
        omega
      have hk3 : k ≠ 3 := by
        intro hke
        have h2x : (W.v 2).1 = x₀ + 4 := congrArg Prod.fst h2
        have h2y : (W.v 2).2 = ym := congrArg Prod.snd h2
        have e21 : (2 + 1 : Fin (W.n + 4)) = 3 := by abel
        have hstep2 := W.step 2
        rw [e21] at hstep2
        rcases hstep2 with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
        · exfalso
          have hm : (W.v 3).2 ≤ ym := hmax 3
          omega
        · have hv3v : W.v 3 = (x₀ + 4, ym - 2) := Prod.ext (by omega) (by omega)
          rw [hke, hv3v] at hk
          have := (Prod.mk.injEq ..).mp hk
          omega
        · have hv3v : W.v 3 = (x₀ + 6, ym) := Prod.ext (by omega) (by omega)
          rw [hke, hv3v] at hk
          have := (Prod.mk.injEq ..).mp hk
          omega
        · have hv3v : W.v 3 = (x₀ + 2, ym) := Prod.ext (by omega) (by omega)
          have h31 : W.v 3 = W.v 1 := by rw [hv3v, h1]
          have h31' := W.inj h31
          have hv := congrArg Fin.val h31'
          rw [val_three_fin, val_one_fin] at hv
          omega
      have hk4 : 4 ≤ (k : ℕ) := by
        by_contra hlt
        push_neg at hlt
        have hc : (k : ℕ) = 0 ∨ (k : ℕ) = 1 ∨ (k : ℕ) = 2 ∨ (k : ℕ) = 3 := by omega
        rcases hc with hkv | hkv | hkv | hkv
        · exact hk0 (Fin.ext hkv)
        · exact hk1 (Fin.ext (by rw [hkv, val_one_fin]))
        · exact hk2 (Fin.ext (by rw [hkv, val_two_fin]))
        · exact hk3 (Fin.ext (by rw [hkv, val_three_fin]))
      have hkn3 : (k : ℕ) ≠ W.n + 3 := by
        intro hkv
        have hke : k = (-1 : Fin (W.n + 4)) := Fin.ext (by rw [hkv, val_neg_one_fin])
        rw [hke, hn1] at hk
        have := (Prod.mk.injEq ..).mp hk
        omega
      have hkle : (k : ℕ) ≤ W.n + 2 := by
        have hlt := k.isLt
        omega
      obtain ⟨W₁, W₂, hI, hT, hL⟩ := W.pinch_case x₀ ym h0 hmax hmin h1 h2 hn1 k hk hk4 hkle
      have hP1 := IH W₁ (by omega)
      have hP2 := IH W₂ (by omega)
      show (W.I : ZMod 2) = (W.T : ZMod 2) + (W.L : ZMod 2) + 1
      have eI : (W.I : ZMod 2) = (W₁.I : ZMod 2) + (W₂.I : ZMod 2) + 1 := by
        rw [hI]; push_cast; rfl
      have eT : (W.T : ZMod 2) = (W₁.T : ZMod 2) + (W₂.T : ZMod 2) := by
        rw [hT]; push_cast; rfl
      have eL : (W.L : ZMod 2) = (W₁.L : ZMod 2) + (W₂.L : ZMod 2) := by
        have hL2 : W.L + 2 = W₁.L + W₂.L := by
          have h1L : W₁.L = W₁.n + 4 := rfl
          have h2L : W₂.L = W₂.n + 4 := rfl
          omega
        have h1c : ((W.L + 2 : ℕ) : ZMod 2) = ((W₁.L + W₂.L : ℕ) : ZMod 2) := by rw [hL2]
        push_cast at h1c
        rw [show (2 : ZMod 2) = 0 from by decide, add_zero] at h1c
        exact h1c
      rw [eI, eT, eL, hP1, hP2]
      abel
    · have hr' : ∀ i, W.v i ≠ (x₀ + 2, ym - 2) := by
        intro i hi
        exact hr ⟨i, hi⟩
      obtain ⟨W', hI, hT, hL⟩ := W.push_case x₀ ym h0 hmax hmin h1 h2 hn1 hr'
      have hP' := IH W' (by omega)
      show (W.I : ZMod 2) = (W.T : ZMod 2) + (W.L : ZMod 2) + 1
      have eI : (W.I : ZMod 2) = (W'.I : ZMod 2) := by
        rw [← hI]; push_cast
        rw [show (4 : ZMod 2) = 0 from by decide, add_zero]
      have eT : (W.T : ZMod 2) = (W'.T : ZMod 2) := by
        rw [hT]; push_cast
        rw [show (4 : ZMod 2) = 0 from by decide, add_zero]
      have eL : (W.L : ZMod 2) = (W'.L : ZMod 2) := by rw [hL]
      rw [eI, eT, eL]
      exact hP'
  · -- v 2 = (x₀ + 2, ym - 2) = r′: peel or 4-cycle
    by_cases hd : W.v (-2) = (x₀ + 2, ym - 2)
    · have hn : W.n = 0 := by
        have h22 : (2 : Fin (W.n + 4)) = (-2 : Fin (W.n + 4)) := W.inj (by rw [h2, hd])
        exact n_eq_zero_of_two_eq_neg_two h22
      exact W.base_case hn
    · have hn2 : 2 ≤ W.n := by
        obtain ⟨m, hm⟩ := W.L_even
        by_contra hle
        push_neg at hle
        have hn0 : W.n = 0 := by
          have hLL : W.L = W.n + 4 := rfl
          omega
        have h22 : (2 : Fin (W.n + 4)) = (-2 : Fin (W.n + 4)) := by
          rw [hn0]
          decide
        have hvv : W.v 2 = W.v (-2) := congrArg W.v h22
        rw [h2] at hvv
        exact hd hvv.symm
      obtain ⟨W', hI, hT, hL⟩ := W.peel_case x₀ ym h0 hmax hmin h1 h2 hn1 hn2 hd
      have hP' := IH W' (by omega)
      show (W.I : ZMod 2) = (W.T : ZMod 2) + (W.L : ZMod 2) + 1
      have eI : (W.I : ZMod 2) = (W'.I : ZMod 2) := by
        rw [← hI]; push_cast
        rw [show (2 : ZMod 2) = 0 from by decide, add_zero]
      have eT : (W.T : ZMod 2) = (W'.T : ZMod 2) := by
        rw [hT]; push_cast
        rw [show (4 : ZMod 2) = 0 from by decide, add_zero]
      have eL : (W.L : ZMod 2) = (W'.L : ZMod 2) := by
        have h1c : ((W'.L + 2 : ℕ) : ZMod 2) = ((W.L : ℕ) : ZMod 2) := by rw [hL]
        push_cast at h1c
        rw [show (2 : ZMod 2) = 0 from by decide, add_zero] at h1c
        exact h1c.symm
      rw [eI, eT, eL]
      exact hP'

theorem master_step (W : OrthoLoop) (IH : ∀ W' : OrthoLoop, W'.I < W.I → W'.P) : W.P := by
  classical
  obtain ⟨i₀, hi₀y, hi₀x⟩ := W.exists_top_left
  apply (W.rotate_P i₀).mp
  have hv0 : (W.rotate i₀).v 0 = W.v i₀ := by
    show W.v ((0 : Fin (W.n + 4)) + i₀) = W.v i₀
    rw [show (0 : Fin (W.n + 4)) + i₀ = i₀ from by abel]
  have h0 : (W.rotate i₀).v 0 = ((W.v i₀).1, (W.v i₀).2) := by
    rw [hv0]
  have hmax : ∀ i : Fin (W.n + 4), ((W.rotate i₀).v i).2 ≤ (W.v i₀).2 := by
    intro i
    have h1 : ((W.rotate i₀).v i).2 ≤ (W.rotate i₀).maxY := (W.rotate i₀).y_le_maxY i
    rw [rotate_maxY] at h1
    have h2 : W.maxY = (W.v i₀).2 := hi₀y.symm
    rw [h2] at h1
    exact h1
  have hmin : ∀ i : Fin (W.n + 4),
      ((W.rotate i₀).v i).2 = (W.v i₀).2 → (W.v i₀).1 ≤ ((W.rotate i₀).v i).1 := by
    intro i hi
    have hiy : W.y (i + i₀) = W.maxY := by
      have h1 : ((W.rotate i₀).v i).2 = W.y (i + i₀) := rfl
      rw [← h1, hi]
      exact hi₀y
    exact hi₀x (i + i₀) hiy
  have h1case : (W.rotate i₀).v 1 = ((W.v i₀).1 + 2, (W.v i₀).2) ∨
      (W.rotate i₀).v 1 = ((W.v i₀).1, (W.v i₀).2 - 2) := by
    have h0x : ((W.rotate i₀).v 0).1 = (W.v i₀).1 := congrArg Prod.fst hv0
    have h0y : ((W.rotate i₀).v 0).2 = (W.v i₀).2 := congrArg Prod.snd hv0
    have e01 : (0 + 1 : Fin (W.n + 4)) = 1 := by abel
    have hstep0 := (W.rotate i₀).step 0
    rw [e01] at hstep0
    rcases hstep0 with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exfalso
      have hm : ((W.rotate i₀).v 1).2 ≤ (W.v i₀).2 := hmax 1
      omega
    · exact Or.inr (Prod.ext (by omega) (by omega))
    · exact Or.inl (Prod.ext (by omega) (by omega))
    · exfalso
      have hm : (W.v i₀).1 ≤ ((W.rotate i₀).v 1).1 := hmin 1 (by omega)
      omega
  have hn1case : (W.rotate i₀).v (-1) = ((W.v i₀).1 + 2, (W.v i₀).2) ∨
      (W.rotate i₀).v (-1) = ((W.v i₀).1, (W.v i₀).2 - 2) := by
    have h0x : ((W.rotate i₀).v 0).1 = (W.v i₀).1 := congrArg Prod.fst hv0
    have h0y : ((W.rotate i₀).v 0).2 = (W.v i₀).2 := congrArg Prod.snd hv0
    have e : (-1 + 1 : Fin (W.n + 4)) = 0 := by abel
    rcases (W.rotate i₀).step (-1) with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
    · rw [e] at hx hy
      exact Or.inr (Prod.ext (by omega) (by omega))
    · rw [e] at hx hy
      exfalso
      have hm : ((W.rotate i₀).v (-1)).2 ≤ (W.v i₀).2 := hmax (-1)
      omega
    · rw [e] at hx hy
      exfalso
      have hm : (W.v i₀).1 ≤ ((W.rotate i₀).v (-1)).1 := hmin (-1) (by omega)
      omega
    · rw [e] at hx hy
      exact Or.inl (Prod.ext (by omega) (by omega))
  rcases h1case with h1 | h1
  · have hn1 : (W.rotate i₀).v (-1) = ((W.v i₀).1, (W.v i₀).2 - 2) := by
      rcases hn1case with hn1e | hn1s
      · exfalso
        have hcon : (W.rotate i₀).v 1 = (W.rotate i₀).v (-1) := by rw [h1, hn1e]
        have hcon' := (W.rotate i₀).inj hcon
        exact one_ne_neg_one hcon'
      · exact hn1s
    exact (W.rotate i₀).master_step_normalized (W.v i₀).1 (W.v i₀).2 h0 hmax hmin h1 hn1
      (fun W' hW' => IH W' (by rwa [rotate_I] at hW'))
  · have hn1 : (W.rotate i₀).v (-1) = ((W.v i₀).1 + 2, (W.v i₀).2) := by
      rcases hn1case with hn1e | hn1s
      · exact hn1e
      · exfalso
        have hcon : (W.rotate i₀).v 1 = (W.rotate i₀).v (-1) := by rw [h1, hn1s]
        have hcon' := (W.rotate i₀).inj hcon
        exact one_ne_neg_one hcon'
    apply (W.rotate i₀).reverse_P.mp
    have hWs0 : (W.rotate i₀).reverse.v 0 = (W.rotate i₀).v 0 := by
      show (W.rotate i₀).v (-(0 : Fin (W.n + 4))) = (W.rotate i₀).v 0
      rw [show (-(0 : Fin (W.n + 4))) = 0 from by abel]
    have hWs0' : (W.rotate i₀).reverse.v 0 = ((W.v i₀).1, (W.v i₀).2) := by
      rw [hWs0, hv0]
    have hmax' : ∀ i : Fin (W.n + 4), ((W.rotate i₀).reverse.v i).2 ≤ (W.v i₀).2 := by
      intro i
      exact hmax (-i)
    have hmin' : ∀ i : Fin (W.n + 4),
        ((W.rotate i₀).reverse.v i).2 = (W.v i₀).2 → (W.v i₀).1 ≤ ((W.rotate i₀).reverse.v i).1 := by
      intro i hi
      exact hmin (-i) hi
    have hWs1 : (W.rotate i₀).reverse.v 1 = ((W.v i₀).1 + 2, (W.v i₀).2) := by
      have e1 : (-(1 : Fin (W.n + 4))) = (-1 : Fin (W.n + 4)) := by abel
      show (W.rotate i₀).v (-(1 : Fin (W.n + 4))) = ((W.v i₀).1 + 2, (W.v i₀).2)
      rw [e1]
      exact hn1
    have hWsn1 : (W.rotate i₀).reverse.v (-1) = ((W.v i₀).1, (W.v i₀).2 - 2) := by
      have e1 : (-(-1 : Fin (W.n + 4))) = (1 : Fin (W.n + 4)) := by abel
      show (W.rotate i₀).v (-(-1 : Fin (W.n + 4))) = ((W.v i₀).1, (W.v i₀).2 - 2)
      rw [e1]
      exact h1
    exact (W.rotate i₀).reverse.master_step_normalized (W.v i₀).1 (W.v i₀).2 hWs0' hmax' hmin'
      hWs1 hWsn1 (fun W' hW' => IH W' (by rwa [reverse_I, rotate_I] at hW'))

/-! ### The master proposition and the final theorem -/

theorem master_aux : ∀ N : ℕ, ∀ W : OrthoLoop, W.I ≤ N → W.P := by
  intro N
  induction N with
  | zero =>
    intro W h
    exact W.master_step (fun W' hW' => by omega)
  | succ N ihN =>
    intro W h
    exact W.master_step (fun W' hW' => ihN W' (by omega))

theorem master (W : OrthoLoop) : W.P := master_aux W.I W le_rfl

end OrthoLoop

/-- USAMO 2023 P3, key parity claim: the number of strictly interior lattice
points of a simple orthogonal loop (edge lengths 2, one vertex parity class)
is odd. -/
theorem odd_inside_count (W : OrthoLoop) :
    Odd {c : Cell | W.inside c ∧ c ∉ W.boundary}.ncard := by
  have hP : (W.I : ZMod 2) = (W.T : ZMod 2) + (W.L : ZMod 2) + 1 := W.master
  have hT := W.T_zmod
  have hL : (W.L : ZMod 2) = 0 := by
    obtain ⟨m, hm⟩ := W.L_even
    rw [hm]
    push_cast
    rw [← two_mul]
    have h0 : (2 : ZMod 2) = 0 := by decide
    rw [h0, zero_mul]
  rw [hT, hL, add_zero, zero_add] at hP
  have hmod : W.I % 2 = 1 := by
    have h3 : W.I % 2 = 1 % 2 := (ZMod.natCast_eq_natCast_iff W.I 1 2).mp hP
    rw [h3]
  rw [Nat.odd_iff]
  exact hmod

end GeoClaim

namespace Config

variable {n : ℕ} (C : Config n)


/-- The midpoint of a step equals the domino partner. -/
theorem midPt_eq_f {s : Cell} (hs : s ∈ board n) (hne : C.f s ≠ s) :
    midPt s (C.arrow s) = C.f s := by
  have hu := arrow_step_unit C hs hne
  have h1 : C.arrow s = s + 2 • (C.f s - s) := rfl
  rw [midPt, h1]
  ext <;> simp [Prod.smul_mk, Int.zsmul_eq_mul] <;> omega

/-- The partner at a special cell is not special (different parity in one
coordinate). -/
theorem f_not_mem_special {s : Cell} (hs : s ∈ C.special) (hne : C.f s ≠ s) :
    C.f s ∉ C.special := by
  rw [mem_special] at hs ⊢
  obtain ⟨hsb, hp1, hp2⟩ := hs
  have hu := arrow_step_unit C hsb hne
  rcases hu with h | h | h | h
  · -- u = (1, 0): parity of first coordinate flips
    have h1 : C.f s = (s.1 + 1, s.2) := by
      have h2 : C.f s - s = ((1 : ℤ), (0 : ℤ)) := h
      ext
      · have h3 := congrArg Prod.fst h2
        simp at h3
        omega
      · have h3 := congrArg Prod.snd h2
        simp at h3
        omega
    rw [h1]
    push_neg
    intro _
    simp
    omega
  · -- u = (-1, 0)
    have h1 : C.f s = (s.1 - 1, s.2) := by
      have h2 : C.f s - s = ((-1 : ℤ), (0 : ℤ)) := h
      ext
      · have h3 := congrArg Prod.fst h2
        simp at h3
        omega
      · have h3 := congrArg Prod.snd h2
        simp at h3
        omega
    rw [h1]
    push_neg
    intro _
    simp
    omega
  · -- u = (0, 1)
    have h1 : C.f s = (s.1, s.2 + 1) := by
      have h2 : C.f s - s = ((0 : ℤ), (1 : ℤ)) := h
      ext
      · have h3 := congrArg Prod.fst h2
        simp at h3
        omega
      · have h3 := congrArg Prod.snd h2
        simp at h3
        omega
    rw [h1]
    push_neg
    intro _
    simp
    omega
  · -- u = (0, -1)
    have h1 : C.f s = (s.1, s.2 - 1) := by
      have h2 : C.f s - s = ((0 : ℤ), (-1 : ℤ)) := h
      ext
      · have h3 := congrArg Prod.fst h2
        simp at h3
        omega
      · have h3 := congrArg Prod.snd h2
        simp at h3
        omega
    rw [h1]
    push_neg
    intro _
    simp
    omega

/-- Geometric bound: a directed arrow cycle that avoids the component of the
empty cell forces that component to be small. The proof packages the cycle as
an orthogonal lattice polygon and uses the interior-parity argument. -/
theorem comp_card_le_of_directed_cycle (hn : Odd n) (hbig : C.empty.1 % 2 = 0)
    {l : ℕ} {z : Fin (l + 4) → Cell} (hinj : Function.Injective z)
    (hzs : ∀ i : Fin (l + 4), z i ∈ C.special ∧ z i ∉ C.comp)
    (hzstep : ∀ i : Fin (l + 4), C.arrow (z i) = z (i + 1)) :
    C.comp.card ≤ ((n - 1) / 2) ^ 2 := by
  classical
  obtain ⟨m, hm⟩ := hn
  subst hm
  have hbig2 : C.empty.2 % 2 = 0 := by rw [← empty_parity_same C ⟨m, rfl⟩]; exact hbig
  have hsb : ∀ i : Fin (l + 4), z i ∈ board (2 * m + 1) :=
    fun i => mem_board_of_mem_special C (hzs i).1
  have hne : ∀ i : Fin (l + 4), C.f (z i) ≠ z i := by
    intro i h
    exact (hzs i).2 (C.unique_fixed (hsb i) h ▸ C.empty_mem_comp)
  have hmid : ∀ i : Fin (l + 4), midPt (z i) (z (i + 1)) = C.f (z i) := by
    intro i
    rw [← hzstep i]
    exact midPt_eq_f C (hsb i) (hne i)
  -- every edge of the cycle is a length-2 axis-aligned step
  have hstep : ∀ i : Fin (l + 4),
      ((z (i + 1)).1 = (z i).1 ∧ (z (i + 1)).2 = (z i).2 + 2) ∨
      ((z (i + 1)).1 = (z i).1 ∧ (z (i + 1)).2 = (z i).2 - 2) ∨
      ((z (i + 1)).1 = (z i).1 + 2 ∧ (z (i + 1)).2 = (z i).2) ∨
      ((z (i + 1)).1 = (z i).1 - 2 ∧ (z (i + 1)).2 = (z i).2) := by
    intro i
    have hu := arrow_step_unit C (hsb i) (hne i)
    have har : C.arrow (z i) = z (i + 1) := hzstep i
    have harr0 : C.arrow (z i) = z i + 2 • (C.f (z i) - z i) := rfl
    rcases hu with h | h | h | h
    · have h2 : C.arrow (z i) = ((z i).1 + 2, (z i).2) := by
        rw [harr0, h]
        ext <;> simp [Prod.smul_mk] <;> omega
      rw [har] at h2
      exact Or.inr (Or.inr (Or.inl ⟨by rw [h2], by rw [h2]⟩))
    · have h2 : C.arrow (z i) = ((z i).1 - 2, (z i).2) := by
        rw [harr0, h]
        ext <;> simp [Prod.smul_mk] <;> omega
      rw [har] at h2
      exact Or.inr (Or.inr (Or.inr ⟨by rw [h2], by rw [h2]⟩))
    · have h2 : C.arrow (z i) = ((z i).1, (z i).2 + 2) := by
        rw [harr0, h]
        ext <;> simp [Prod.smul_mk] <;> omega
      rw [har] at h2
      exact Or.inl ⟨by rw [h2], by rw [h2]⟩
    · have h2 : C.arrow (z i) = ((z i).1, (z i).2 - 2) := by
        rw [harr0, h]
        ext <;> simp [Prod.smul_mk] <;> omega
      rw [har] at h2
      exact Or.inr (Or.inl ⟨by rw [h2], by rw [h2]⟩)
  have hpar : ∀ i : Fin (l + 4), ((z i).1 : ZMod 2) = C.empty.1 ∧ ((z i).2 : ZMod 2) = C.empty.2 := by
    intro i
    have hsp := (mem_special C).mp (hzs i).1
    exact ⟨(ZMod.intCast_eq_intCast_iff' _ _ _).mpr hsp.2.1,
           (ZMod.intCast_eq_intCast_iff' _ _ _).mpr hsp.2.2⟩
  have hinjf : ∀ a b : Fin (l + 4), C.f (z a) = C.f (z b) → a = b := by
    intro a b h
    have h1 := C.hf_inv (z a) (hsb a)
    rw [h, C.hf_inv (z b) (hsb b)] at h1
    exact hinj h1.symm
  have hfs : ∀ k : Fin (l + 4), C.f (z k) ∉ C.special :=
    fun k => f_not_mem_special C (hzs k).1 (hne k)
  have hsimple : ∀ i j : Fin (l + 4), i ≠ j → i + 1 ≠ j → i ≠ j + 1 →
      Disjoint ({z i, midPt (z i) (z (i + 1)), z (i + 1)} : Finset Cell)
        ({z j, midPt (z j) (z (j + 1)), z (j + 1)} : Finset Cell) := by
    intro i j hij hij1 hij2
    rw [hmid i, hmid j, Finset.disjoint_left]
    intro w hw1 hw2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw1 hw2
    rcases hw1 with rfl | rfl | rfl <;> rcases hw2 with h2 | h2 | h2
    · exact absurd (hinj h2) hij
    · exact hfs j (h2 ▸ (hzs i).1)
    · exact absurd (hinj h2) hij2
    · exact hfs i (h2 ▸ (hzs j).1)
    · exact absurd (hinjf i j h2) hij
    · exact hfs i (h2 ▸ (hzs (j + 1)).1)
    · exact absurd (hinj h2) hij1
    · exact hfs j (h2 ▸ (hzs (i + 1)).1)
    · have h3 := hinj h2
      exact hij (by
        have h4 : (i + 1 : Fin (l + 4)) - 1 = (j + 1 : Fin (l + 4)) - 1 := by rw [h3]
        rwa [OrthoLoop.fin_add_one_sub_one i, OrthoLoop.fin_add_one_sub_one j] at h4)
  -- the orthogonal loop formed by the cycle
  set W : OrthoLoop := ⟨C.empty.1, C.empty.2, l, z, hinj, hstep, hpar, hsimple⟩ with hW
  -- the component does not meet the boundary of the loop
  have hbound : ∀ c ∈ W.boundary, c ∉ C.comp := by
    intro c hc hcm
    rw [W.mem_boundary c] at hc
    rcases hc with ⟨i, hi⟩ | ⟨i, hi⟩
    · have hvc : W.v i = z i := rfl
      rw [hvc] at hi
      exact (hzs i).2 (hi ▸ hcm)
    · have hmc : W.mid i = C.f (z i) := by
        have h1 : W.mid i = midPt (W.v i) (W.v (i + 1)) := rfl
        rw [h1]
        exact hmid i
      have hsp2 : C.f (z i) ∈ C.special := by
        have h3 : C.f (z i) ∈ C.comp := by
          have h4 : W.mid i ∈ C.comp := hi ▸ hcm
          rw [hmc] at h4
          exact h4
        exact ((mem_comp C).mp h3).1
      exact (hfs i) hsp2
  have hempty_out : C.empty ∉ W.boundary := fun h => hbound _ h C.empty_mem_comp
  -- vertex x-coordinates lie in the board range
  have hb1 : ∀ i : Fin (l + 4), 0 ≤ (z i).1 ∧ (z i).1 ≤ 2 * (m : ℤ) := by
    intro i
    have h := mem_board.mp (hsb i)
    constructor <;> omega
  have hb2 : ∀ i : Fin (l + 4), 0 ≤ (z i).2 ∧ (z i).2 ≤ 2 * (m : ℤ) := by
    intro i
    have h := mem_board.mp (hsb i)
    constructor <;> omega
  obtain ⟨i₀, hi₀⟩ : ∃ i, W.x i = W.minX := by
    have h1 : W.minX ∈ Finset.univ.image W.x := Finset.min'_mem _ _
    rw [Finset.mem_image] at h1
    obtain ⟨i, -, hi⟩ := h1
    exact ⟨i, hi⟩
  obtain ⟨i₁, hi₁⟩ : ∃ i, W.x i = W.maxX := by
    have h1 : W.maxX ∈ Finset.univ.image W.x := Finset.max'_mem _ _
    rw [Finset.mem_image] at h1
    obtain ⟨i, -, hi⟩ := h1
    exact ⟨i, hi⟩
  obtain ⟨j₀, hj₀⟩ : ∃ i, W.y i = W.minY := by
    have h1 : W.minY ∈ Finset.univ.image W.y := Finset.min'_mem _ _
    rw [Finset.mem_image] at h1
    obtain ⟨i, -, hi⟩ := h1
    exact ⟨i, hi⟩
  obtain ⟨j₁, hj₁⟩ : ∃ i, W.y i = W.maxY := by
    have h1 : W.maxY ∈ Finset.univ.image W.y := Finset.max'_mem _ _
    rw [Finset.mem_image] at h1
    obtain ⟨i, -, hi⟩ := h1
    exact ⟨i, hi⟩
  have hminx : 0 ≤ W.minX := by
    have hvc : W.x i₀ = (z i₀).1 := rfl
    rw [← hi₀, hvc]
    exact (hb1 i₀).1
  have hmaxx : W.maxX ≤ 2 * (m : ℤ) := by
    have hvc : W.x i₁ = (z i₁).1 := rfl
    rw [← hi₁, hvc]
    exact (hb1 i₁).2
  have hminy : 0 ≤ W.minY := by
    have hvc : W.y j₀ = (z j₀).2 := rfl
    rw [← hj₀, hvc]
    exact (hb2 j₀).1
  have hmaxy : W.maxY ≤ 2 * (m : ℤ) := by
    have hvc : W.y j₁ = (z j₁).2 := rfl
    rw [← hj₁, hvc]
    exact (hb2 j₁).2
  have hboxb : ∀ c ∈ W.box, c ∈ board (2 * m + 1) := by
    intro c hbx
    rw [OrthoLoop.box, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hbx
    rw [mem_board]
    omega
  -- the empty cell is strictly inside the loop
  have hinside : W.inside C.empty := by
    by_contra hnot
    have hc2 : W.p2 C.empty = 0 ∨ W.p2 C.empty = 1 := by
      have hgen : ∀ p : ZMod 2, p = 0 ∨ p = 1 := by
        intro p
        fin_cases p
        · exact Or.inl rfl
        · exact Or.inr rfl
      exact hgen _
    have hp0 : W.p2 C.empty = 0 := by
      rcases hc2 with h | h
      · exact h
      · exact absurd h hnot
    -- the interior set, as a finset
    set sset := W.box.filter (fun c => W.p2 c = 1 ∧ c ∉ W.boundary) with hss
    have hmap : ∀ c ∈ sset, C.f c ∈ sset := by
      intro c hcs
      rw [hss, Finset.mem_filter] at hcs ⊢
      obtain ⟨hbx, hp1, hnb⟩ := hcs
      have hcb : c ∈ board (2 * m + 1) := hboxb c hbx
      have hne2 : C.f c ≠ c := by
        intro h
        have h3 : c = C.empty := C.unique_fixed hcb h
        rw [h3] at hp1
        rw [hp0] at hp1
        simp at hp1
      have hnb2 : C.f c ∉ W.boundary := by
        intro h
        rw [W.mem_boundary (C.f c)] at h
        rcases h with ⟨i, hi⟩ | ⟨i, hi⟩
        · have hvc : W.v i = z i := rfl
          rw [hvc] at hi
          have hcm : c = W.mid i := by
            have h1 : c = C.f (z i) := by
              have h3 := C.hf_inv c hcb
              rw [← hi] at h3
              exact h3.symm
            have h2 : W.mid i = C.f (z i) := by
              have h4 : W.mid i = midPt (W.v i) (W.v (i + 1)) := rfl
              rw [h4]
              exact hmid i
            rw [h1, h2]
          exact hnb (hcm ▸ W.mid_mem_boundary i)
        · have hmc : W.mid i = C.f (z i) := by
            have h1 : W.mid i = midPt (W.v i) (W.v (i + 1)) := rfl
            rw [h1]
            exact hmid i
          rw [hmc] at hi
          have hcm : c = z i := by
            have h3 := C.hf_inv c hcb
            rw [← hi, C.hf_inv (z i) (hsb i)] at h3
            exact h3.symm
          exact hnb (hcm ▸ W.vertex_mem_boundary i)
      have hu := arrow_step_unit C hcb hne2
      have hst : ((C.f c).1 = c.1 + 1 ∧ (C.f c).2 = c.2) ∨ ((C.f c).1 = c.1 - 1 ∧ (C.f c).2 = c.2) ∨
          ((C.f c).1 = c.1 ∧ (C.f c).2 = c.2 + 1) ∨ ((C.f c).1 = c.1 ∧ (C.f c).2 = c.2 - 1) := by
        rcases hu with h | h | h | h
        · have h3 : C.f c - c = ((1 : ℤ), (0 : ℤ)) := h
          have h4 := congrArg Prod.fst h3
          have h5 := congrArg Prod.snd h3
          simp at h4 h5
          exact Or.inl ⟨by omega, by omega⟩
        · have h3 : C.f c - c = ((-1 : ℤ), (0 : ℤ)) := h
          have h4 := congrArg Prod.fst h3
          have h5 := congrArg Prod.snd h3
          simp at h4 h5
          exact Or.inr (Or.inl ⟨by omega, by omega⟩)
        · have h3 : C.f c - c = ((0 : ℤ), (1 : ℤ)) := h
          have h4 := congrArg Prod.fst h3
          have h5 := congrArg Prod.snd h3
          simp at h4 h5
          exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))
        · have h3 : C.f c - c = ((0 : ℤ), (-1 : ℤ)) := h
          have h4 := congrArg Prod.fst h3
          have h5 := congrArg Prod.snd h3
          simp at h4 h5
          exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))
      have hp2 : W.p2 (C.f c) = W.p2 c := (W.p2_eq_of_unit_step hst hnb hnb2).symm
      -- `C.f c` stays in the bounding box
      have hfbox : C.f c ∈ W.box := by
        rw [OrthoLoop.box, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
        rw [OrthoLoop.box, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hbx
        obtain ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩ := hbx
        have hpx : W.p2 (C.f c) = 1 := hp2 ▸ hp1
        have hx1' : W.minX ≤ (C.f c).1 := by
          by_contra h
          push_neg at h
          rw [W.p2_eq_zero_of_le_minX h] at hpx
          simp at hpx
        have hx2' : (C.f c).1 ≤ W.maxX - 1 := by
          by_contra h
          push_neg at h
          rw [W.p2_eq_zero_of_maxX_le (by omega)] at hpx
          simp at hpx
        have hy1' : W.minY ≤ (C.f c).2 := by
          by_contra h
          push_neg at h
          rw [W.p2_eq_zero_of_minY (by omega)] at hpx
          simp at hpx
        have hy2' : (C.f c).2 ≤ W.maxY - 1 := by
          by_contra h
          push_neg at h
          rw [W.p2_eq_zero_of_maxY (by omega)] at hpx
          simp at hpx
        rcases hst with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
          · refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> omega
      exact ⟨hfbox, hp2 ▸ hp1, hnb2⟩
    have hinv : ∀ c ∈ sset, C.f (C.f c) = c := by
      intro c hcs
      exact C.hf_inv c (hboxb c (Finset.mem_filter.mp hcs).1)
    have hfp : ∀ c ∈ sset, C.f c ≠ c := by
      intro c hcs h
      have hcb : c ∈ board (2 * m + 1) := hboxb c (Finset.mem_filter.mp hcs).1
      have h3 : c = C.empty := C.unique_fixed hcb h
      have h4 : W.p2 c = 1 := (Finset.mem_filter.mp hcs).2.1
      rw [h3] at h4
      rw [hp0] at h4
      simp at h4
    have heven : Even sset.card := even_card_of_fp_free_invol C.f sset hmap hinv hfp
    have hodd : Odd sset.card := by
      have h1 := odd_inside_count W
      have h2 : W.I = sset.card := by
        rw [hss]
        exact W.I_eq
      rw [← h2]
      exact h1
    exact (Nat.not_even_iff_odd.mpr hodd) heven
  -- every cell of the component is inside the loop
  have hcomp_in : ∀ s ∈ C.comp, W.inside s ∧ s ∉ W.boundary := by
    intro s hsc
    obtain ⟨hsp, hconn⟩ := (mem_comp C).mp hsc
    have hsb' : s ∉ W.boundary := fun h => hbound s h hsc
    refine ⟨?_, hsb'⟩
    have key : W.p2 s = W.p2 C.empty := by
      have gAdj_p2 : ∀ {a b : Cell}, C.gAdj a b → a ∈ C.comp → W.p2 a = W.p2 b := by
        intro a b hab ha
        have hstep2 : ∀ {u v : Cell}, u ∈ C.special → u ≠ C.empty → C.arrow u = v →
            u ∈ C.comp → v ∈ C.comp → W.p2 u = W.p2 v := by
          intro u v hu hun huv hcu hcv
          have hub := mem_board_of_mem_special C hu
          have hne3 : C.f u ≠ u := fun h => hun (C.unique_fixed hub h)
          have hu2 := arrow_step_unit C hub hne3
          have huB : u ∉ W.boundary := fun h => hbound u h hcu
          have hvB : v ∉ W.boundary := fun h => hbound v h hcv
          have hmu : C.f u ∉ W.boundary := by
            intro h
            rw [W.mem_boundary (C.f u)] at h
            rcases h with ⟨i, hi⟩ | ⟨i, hi⟩
            · have hvc : W.v i = z i := rfl
              rw [hvc] at hi
              exact (f_not_mem_special C hu hne3) (hi ▸ (hzs i).1)
            · have hmc : W.mid i = C.f (z i) := by
                have h1 : W.mid i = midPt (W.v i) (W.v (i + 1)) := rfl
                rw [h1]
                exact hmid i
              rw [hmc] at hi
              have h2 : u = z i := by
                have h3 := C.hf_inv u hub
                rw [← hi, C.hf_inv (z i) (hsb i)] at h3
                exact h3.symm
              exact (hzs i).2 (h2 ▸ hcu)
          have hst1 : ((C.f u).1 = u.1 + 1 ∧ (C.f u).2 = u.2) ∨ ((C.f u).1 = u.1 - 1 ∧ (C.f u).2 = u.2) ∨
              ((C.f u).1 = u.1 ∧ (C.f u).2 = u.2 + 1) ∨ ((C.f u).1 = u.1 ∧ (C.f u).2 = u.2 - 1) := by
            rcases hu2 with h | h | h | h
            · have h3 : C.f u - u = ((1 : ℤ), (0 : ℤ)) := h
              have h4 := congrArg Prod.fst h3
              have h5 := congrArg Prod.snd h3
              simp at h4 h5
              exact Or.inl ⟨by omega, by omega⟩
            · have h3 : C.f u - u = ((-1 : ℤ), (0 : ℤ)) := h
              have h4 := congrArg Prod.fst h3
              have h5 := congrArg Prod.snd h3
              simp at h4 h5
              exact Or.inr (Or.inl ⟨by omega, by omega⟩)
            · have h3 : C.f u - u = ((0 : ℤ), (1 : ℤ)) := h
              have h4 := congrArg Prod.fst h3
              have h5 := congrArg Prod.snd h3
              simp at h4 h5
              exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))
            · have h3 : C.f u - u = ((0 : ℤ), (-1 : ℤ)) := h
              have h4 := congrArg Prod.fst h3
              have h5 := congrArg Prod.snd h3
              simp at h4 h5
              exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))
          have hvv : v = u + 2 • (C.f u - u) := by
            have h1 : C.arrow u = u + 2 • (C.f u - u) := rfl
            rw [← h1]
            exact huv.symm
          have hst2 : (v.1 = (C.f u).1 + 1 ∧ v.2 = (C.f u).2) ∨ (v.1 = (C.f u).1 - 1 ∧ v.2 = (C.f u).2) ∨
              (v.1 = (C.f u).1 ∧ v.2 = (C.f u).2 + 1) ∨ (v.1 = (C.f u).1 ∧ v.2 = (C.f u).2 - 1) := by
            rcases hu2 with h | h | h | h
            · have h3 : C.f u - u = ((1 : ℤ), (0 : ℤ)) := h
              have hf : C.f u = u + ((1 : ℤ), (0 : ℤ)) := by
                have h4 := sub_eq_iff_eq_add.mp h3
                have h5 := congrArg Prod.fst h4
                have h6 := congrArg Prod.snd h4
                simp at h5 h6
                ext <;> simp <;> omega
              rw [hvv, hf]
              exact Or.inl ⟨by simp [Prod.smul_mk] <;> omega, by simp⟩
            · have h3 : C.f u - u = ((-1 : ℤ), (0 : ℤ)) := h
              have hf : C.f u = u + ((-1 : ℤ), (0 : ℤ)) := by
                have h4 := sub_eq_iff_eq_add.mp h3
                have h5 := congrArg Prod.fst h4
                have h6 := congrArg Prod.snd h4
                simp at h5 h6
                ext <;> simp <;> omega
              rw [hvv, hf]
              exact Or.inr (Or.inl ⟨by simp [Prod.smul_mk] <;> omega, by simp⟩)
            · have h3 : C.f u - u = ((0 : ℤ), (1 : ℤ)) := h
              have hf : C.f u = u + ((0 : ℤ), (1 : ℤ)) := by
                have h4 := sub_eq_iff_eq_add.mp h3
                have h5 := congrArg Prod.fst h4
                have h6 := congrArg Prod.snd h4
                simp at h5 h6
                ext <;> simp <;> omega
              rw [hvv, hf]
              exact Or.inr (Or.inr (Or.inl ⟨by simp, by simp [Prod.smul_mk] <;> omega⟩))
            · have h3 : C.f u - u = ((0 : ℤ), (-1 : ℤ)) := h
              have hf : C.f u = u + ((0 : ℤ), (-1 : ℤ)) := by
                have h4 := sub_eq_iff_eq_add.mp h3
                have h5 := congrArg Prod.fst h4
                have h6 := congrArg Prod.snd h4
                simp at h5 h6
                ext <;> simp <;> omega
              rw [hvv, hf]
              exact Or.inr (Or.inr (Or.inr ⟨by simp, by simp [Prod.smul_mk] <;> omega⟩))
          exact W.p2_eq_of_two_step hst1 hst2 huB hmu hvB
        have habc := hab
        rcases hab with ⟨hu, hun, huv, hb⟩ | ⟨hv, hvn, hvu, hb⟩
        · exact hstep2 hu hun huv ha (mem_comp_of_gAdj C habc ha)
        · exact (hstep2 hv hvn hvu (mem_comp_of_gAdj C habc ha) ha).symm
      have gconn_symm : ∀ {a b : Cell}, C.gConn a b → C.gConn b a := by
        intro a b h
        induction h with
        | refl => exact Relation.ReflTransGen.refl
        | tail _ hxy ih => exact Relation.ReflTransGen.head (C.gAdj_symm hxy) ih
      have key2 : ∀ a b : Cell, C.gConn a b → b ∈ C.comp → W.p2 a = W.p2 b := by
        intro a b hab2
        induction hab2 with
        | refl => intro _; rfl
        | tail hconn1 hxy ih =>
          intro hb2
          have hx : _ ∈ C.comp := mem_comp_of_gAdj C (C.gAdj_symm hxy) hb2
          exact (ih hx).trans (gAdj_p2 hxy hx)
      exact key2 s C.empty hconn C.empty_mem_comp
    show W.p2 s = 1
    rw [key]
    exact hinside
  -- hence every comp cell is an interior special cell
  have hsub : C.comp ⊆ C.interior := by
    intro s hsc
    obtain ⟨hins, hnb⟩ := hcomp_in s hsc
    have hsp := ((mem_comp C).mp hsc).1
    have hsp2 := (mem_special C).mp hsp
    have hbx := W.mem_box_of_inside hins
    rw [OrthoLoop.box, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hbx
    obtain ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩ := hbx
    rw [mem_interior]
    refine ⟨hsp, ?_, ?_, ?_, ?_⟩
    · have h1 : s.1 ≠ W.minX := by
        intro h
        have hse : s = (W.minX, s.2) := by
          ext
          · show s.1 = W.minX
            exact h
          · rfl
        rw [hse] at hnb
        have hins2 : W.p2 s = 1 := hins
        rw [hse] at hins2
        rw [W.p2_eq_zero_of_minX_boundary s.2 hnb] at hins2
        exact zero_ne_one hins2
      omega
    · have h1 : s.1 ≠ W.maxX - 1 := by
        intro h
        have h6 : ((s.1 : ℤ) : ZMod 2) = W.a :=
          (ZMod.intCast_eq_intCast_iff' _ _ _).mpr hsp2.2.1
        have h7 : (W.maxX : ZMod 2) = W.a := by
          have hvc : W.x i₁ = (z i₁).1 := rfl
          rw [← hi₁]
          exact W.parX i₁
        rw [h] at h6
        have h8 : (W.maxX - 1 : ℤ) % 2 = W.maxX % 2 := by
          have h9 : ((W.maxX - 1 : ℤ) : ZMod 2) = (W.maxX : ZMod 2) := by
            rw [h7]
            exact h6
          exact (ZMod.intCast_eq_intCast_iff' _ _ _).mp h9
        omega
      omega
    · have h1 : s.2 ≠ W.minY := by
        intro h
        have hse : s = (s.1, W.minY) := by
          ext
          · rfl
          · show s.2 = W.minY
            exact h
        rw [hse] at hnb
        have hins2 : W.p2 s = 1 := hins
        rw [hse] at hins2
        rw [W.p2_eq_zero_of_minY_boundary s.1 hnb] at hins2
        exact zero_ne_one hins2
      omega
    · have h1 : s.2 ≠ W.maxY - 1 := by
        intro h
        have h6 : ((s.2 : ℤ) : ZMod 2) = W.b :=
          (ZMod.intCast_eq_intCast_iff' _ _ _).mpr hsp2.2.2
        have h7 : (W.maxY : ZMod 2) = W.b := by
          have hvc : W.y j₁ = (z j₁).2 := rfl
          rw [← hj₁]
          exact W.parY j₁
        rw [h] at h6
        have h8 : (W.maxY - 1 : ℤ) % 2 = W.maxY % 2 := by
          have h9 : ((W.maxY - 1 : ℤ) : ZMod 2) = (W.maxY : ZMod 2) := by
            rw [h7]
            exact h6
          exact (ZMod.intCast_eq_intCast_iff' _ _ _).mp h9
        omega
      omega
  calc C.comp.card ≤ C.interior.card := Finset.card_le_card hsub
    _ = ((2 * m + 1 - 3) / 2) ^ 2 := card_interior_big C ⟨m, rfl⟩ hbig
    _ ≤ ((2 * m + 1 - 1) / 2) ^ 2 := by
        have h1 : (2 * m + 1 - 3) / 2 = m - 1 := by omega
        have h2 : (2 * m + 1 - 1) / 2 = m := by omega
        rw [h1, h2]
        exact Nat.pow_le_pow_left (Nat.sub_le m 1) 2

/-- If the component of the empty cell is not all of `special`, it is small. -/
theorem comp_card_le_of_not_full (hn : Odd n) (hbig : C.empty.1 % 2 = 0)
    (hne : C.comp ≠ C.special) : C.comp.card ≤ ((n - 1) / 2) ^ 2 := by
  have hsub : C.comp ⊆ C.special := by
    intro s hs
    exact ((mem_comp C).mp hs).1
  have hex : ∃ s₀ ∈ C.special, s₀ ∉ C.comp := by
    by_contra h
    push_neg at h
    exact hne (le_antisymm hsub h)
  obtain ⟨s₀, hs₀, hs₀'⟩ := hex
  obtain ⟨l, z, hinj, hzs, hzstep⟩ := exists_directed_cycle C hn hbig hs₀ hs₀'
  exact comp_card_le_of_directed_cycle C hn hbig hinj hzs hzstep

/-- Upper bound: `k(C)` is either at most `((n-1)/2)²` or exactly
`((n+1)/2)²`. -/
theorem kval_upper (hn : Odd n) :
    C.kval ≤ ((n - 1) / 2) ^ 2 ∨ C.kval = ((n + 1) / 2) ^ 2 := by
  classical
  rw [kval_eq_comp_card]
  by_cases hpar : C.empty.1 % 2 = 0
  · by_cases hfull : C.comp = C.special
    · right
      rw [hfull]
      exact card_special_big C hn hpar
    · left
      exact comp_card_le_of_not_full C hn hpar hfull
  · left
    have hp : C.empty.1 % 2 = 1 := by omega
    have hsub : C.comp ⊆ C.special := by
      intro s hs
      exact ((mem_comp C).mp hs).1
    calc C.comp.card ≤ C.special.card := Finset.card_le_card hsub
      _ = ((n - 1) / 2) ^ 2 := card_special_small C hn hp


end Config

/-!
## The snake construction (big component, `k = ((n+1)/2)²`)
-/

namespace Config

variable {n : ℕ}

/-- The snake configuration: uncovered corner, horizontal dominoes in the first
row, vertical dominoes everywhere else. -/
noncomputable def snakeF (n : ℕ) (c : Cell) : Cell :=
  if c ∈ board n then
    if c.2 = 0 then
      if c.1 = 0 then c
      else if c.1 % 2 = 0 then (c.1 - 1, (0 : ℤ))
      else (c.1 + 1, (0 : ℤ))
    else
      if c.2 % 2 = 0 then (c.1, c.2 - 1)
      else (c.1, c.2 + 1)
  else c

theorem snakeF_off (c : Cell) (hc : c ∉ board n) : snakeF n c = c := by
  simp only [snakeF, if_neg hc]

theorem snakeF_eq_of_y_zero (c : Cell) (hc : c ∈ board n) (h0 : c.1 = 0) (hy : c.2 = 0) :
    snakeF n c = c := by
  simp only [snakeF, if_pos hc, if_pos hy, if_pos h0]

theorem snakeF_eq_row0_even (c : Cell) (hc : c ∈ board n) (h0 : c.1 ≠ 0) (hy : c.2 = 0)
    (he : c.1 % 2 = 0) : snakeF n c = (c.1 - 1, (0 : ℤ)) := by
  simp only [snakeF, if_pos hc, if_pos hy, if_neg h0, if_pos he]

theorem snakeF_eq_row0_odd (c : Cell) (hc : c ∈ board n) (h0 : c.1 ≠ 0) (hy : c.2 = 0)
    (he : ¬c.1 % 2 = 0) : snakeF n c = (c.1 + 1, (0 : ℤ)) := by
  simp only [snakeF, if_pos hc, if_pos hy, if_neg h0, if_neg he]

theorem snakeF_eq_vert_even (c : Cell) (hc : c ∈ board n) (hy : ¬c.2 = 0)
    (he : c.2 % 2 = 0) : snakeF n c = (c.1, c.2 - 1) := by
  simp only [snakeF, if_pos hc, if_neg hy, if_pos he]

theorem snakeF_eq_vert_odd (c : Cell) (hc : c ∈ board n) (hy : ¬c.2 = 0)
    (he : ¬c.2 % 2 = 0) : snakeF n c = (c.1, c.2 + 1) := by
  simp only [snakeF, if_pos hc, if_neg hy, if_neg he]

/-- The snake configuration is valid. -/
theorem snakeF_valid (hn : Odd n) : ∃ C : Config n, C.f = snakeF n := by
  classical
  obtain ⟨m, hm⟩ := hn
  subst hm
  have hnl : (2 * m + 1 : ℤ) - 1 = 2 * (m : ℤ) := by omega
  refine ⟨⟨snakeF (2 * m + 1), ?_, ?_, ?_, ?_, ?_⟩, rfl⟩
  · -- off board: identity
    intro c hc
    exact snakeF_off c hc
  · -- maps to board
    intro c hc
    have hb := mem_board.mp hc
    simp only [snakeF, if_pos hc]
    by_cases hy : c.2 = 0
    · rw [if_pos hy]
      by_cases h0 : c.1 = 0
      · rw [if_pos h0]
        exact hc
      · rw [if_neg h0]
        by_cases he : c.1 % 2 = 0
        · rw [if_pos he]
          rw [mem_board]
          exact ⟨by omega, by omega, by omega, by omega⟩
        · rw [if_neg he]
          rw [mem_board]
          have h1 : c.1 % 2 = 1 := by omega
          exact ⟨by omega, by omega, by omega, by omega⟩
    · rw [if_neg hy]
      by_cases he : c.2 % 2 = 0
      · rw [if_pos he]
        rw [mem_board]
        have h1 : 2 ≤ c.2 := by omega
        exact ⟨by omega, by omega, by omega, by omega⟩
      · rw [if_neg he]
        rw [mem_board]
        have h1 : c.2 % 2 = 1 := by omega
        exact ⟨by omega, by omega, by omega, by omega⟩
  · -- involutive
    intro c hc
    have hb := mem_board.mp hc
    by_cases hy : c.2 = 0
    · by_cases h0 : c.1 = 0
      · rw [snakeF_eq_of_y_zero c hc h0 hy, snakeF_eq_of_y_zero c hc h0 hy]
      · by_cases he : c.1 % 2 = 0
        · rw [snakeF_eq_row0_even c hc h0 hy he]
          have h3 : (c.1 - 1, (0 : ℤ)) ∈ board (2 * m + 1) := by
            rw [mem_board]
            exact ⟨by omega, by omega, by omega, by omega⟩
          rw [snakeF_eq_row0_odd _ h3 (by omega) rfl (by omega)]
          ext <;> simp <;> omega
        · rw [snakeF_eq_row0_odd c hc h0 hy he]
          have h1 : c.1 % 2 = 1 := by omega
          have h3 : (c.1 + 1, (0 : ℤ)) ∈ board (2 * m + 1) := by
            rw [mem_board]
            exact ⟨by omega, by omega, by omega, by omega⟩
          have h4 : (c.1 + 1 : ℤ) % 2 = 0 := by omega
          rw [snakeF_eq_row0_even _ h3 (by omega) rfl h4]
          ext <;> simp <;> omega
    · by_cases he : c.2 % 2 = 0
      · rw [snakeF_eq_vert_even c hc hy he]
        have h3 : (c.1, c.2 - 1) ∈ board (2 * m + 1) := by
          rw [mem_board]
          exact ⟨by omega, by omega, by omega, by omega⟩
        rw [snakeF_eq_vert_odd _ h3 (by omega) (by omega)]
        ext <;> simp <;> omega
      · rw [snakeF_eq_vert_odd c hc hy he]
        have h1 : c.2 % 2 = 1 := by omega
        have h3 : (c.1, c.2 + 1) ∈ board (2 * m + 1) := by
          rw [mem_board]
          exact ⟨by omega, by omega, by omega, by omega⟩
        have h4 : (c.2 + 1 : ℤ) % 2 = 0 := by omega
        rw [snakeF_eq_vert_even _ h3 (by omega) h4]
        ext <;> simp <;> omega
  · -- adjacent
    intro c hc hfc
    by_cases hy : c.2 = 0
    · by_cases h0 : c.1 = 0
      · rw [snakeF_eq_of_y_zero c hc h0 hy] at hfc
        exact absurd rfl hfc
      · by_cases he : c.1 % 2 = 0
        · rw [snakeF_eq_row0_even c hc h0 hy he] at hfc ⊢
          have h1 : c.1 - (c.1 - 1) = 1 := by omega
          exact Or.inr ⟨by rw [h1]; simp, hy⟩
        · rw [snakeF_eq_row0_odd c hc h0 hy he] at hfc ⊢
          have h1 : c.1 - (c.1 + 1) = -1 := by omega
          exact Or.inr ⟨by rw [h1]; simp, hy⟩
    · by_cases he : c.2 % 2 = 0
      · rw [snakeF_eq_vert_even c hc hy he] at hfc ⊢
        have h1 : c.2 - (c.2 - 1) = 1 := by omega
        exact Or.inl ⟨rfl, by rw [h1]; simp⟩
      · rw [snakeF_eq_vert_odd c hc hy he] at hfc ⊢
        have h1 : c.2 - (c.2 + 1) = -1 := by omega
        exact Or.inl ⟨rfl, by rw [h1]; simp⟩
  · -- unique fixed point
    refine ⟨(0, 0), ⟨?_, ?_⟩, ?_⟩
    · rw [mem_board]
      exact ⟨by omega, by omega, by omega, by omega⟩
    · exact snakeF_eq_of_y_zero _ (by rw [mem_board]; exact ⟨by omega, by omega, by omega, by omega⟩)
        rfl rfl
    · intro c ⟨hc, hfc⟩
      have hb := mem_board.mp hc
      simp only [snakeF, if_pos hc] at hfc
      by_cases hy : c.2 = 0
      · rw [if_pos hy] at hfc
        by_cases h0 : c.1 = 0
        · ext <;> simp [h0, hy]
        · rw [if_neg h0] at hfc
          by_cases he : c.1 % 2 = 0
          · rw [if_pos he] at hfc
            have h1 : (c.1 - 1, (0 : ℤ)) = c := hfc
            have h2 := congrArg Prod.fst h1
            simp at h2
          · rw [if_neg he] at hfc
            have h1 : (c.1 + 1, (0 : ℤ)) = c := hfc
            have h2 := congrArg Prod.fst h1
            simp at h2
      · rw [if_neg hy] at hfc
        by_cases he : c.2 % 2 = 0
        · rw [if_pos he] at hfc
          have h1 : (c.1, c.2 - 1) = c := hfc
          have h2 := congrArg Prod.snd h1
          simp at h2
        · rw [if_neg he] at hfc
          have h1 : (c.1, c.2 + 1) = c := hfc
          have h2 := congrArg Prod.snd h1
          simp at h2

end Config

namespace Config

variable {n : ℕ}

/-- The snake configuration achieves the maximal value `k(C) = ((n+1)/2)²`:
its uncovered square is the origin, and every special cell is connected to it
in the arrow graph, so the component is the full set of special cells. -/
theorem snake_achieves (hn : Odd n) : ∃ C : Config n, C.kval = ((n + 1) / 2) ^ 2 := by
  obtain ⟨m, hm⟩ := hn
  subst hm
  obtain ⟨C, hCf⟩ := snakeF_valid ⟨m, rfl⟩
  refine ⟨C, ?_⟩
  have hnl : ((2 * m + 1 : ℕ) : ℤ) - 1 = 2 * (m : ℤ) := by omega
  -- board membership from coordinate bounds
  have hboard_of : ∀ {x y : ℤ}, 0 ≤ x → x ≤ 2 * (m : ℤ) → 0 ≤ y → y ≤ 2 * (m : ℤ) →
      (x, y) ∈ board (2 * m + 1) := by
    intro x y hx1 hx2 hy1 hy2
    rw [mem_board, hnl]
    exact ⟨hx1, hx2, hy1, hy2⟩
  -- the uncovered square is the origin
  have h00 : ((0, 0) : Cell) ∈ board (2 * m + 1) :=
    hboard_of le_rfl (by omega) le_rfl (by omega)
  have hf00 : C.f (0, 0) = (0, 0) := by
    rw [hCf]
    exact snakeF_eq_of_y_zero _ h00 rfl rfl
  have hEmpty : C.empty = (0, 0) := (C.unique_fixed h00 hf00).symm
  -- special cells are exactly the even-even board cells
  have hspec : ∀ {x y : ℤ}, (x, y) ∈ C.special ↔
      (x, y) ∈ board (2 * m + 1) ∧ x % 2 = 0 ∧ y % 2 = 0 := by
    intro x y
    rw [mem_special, hEmpty]
    simp
  -- arrows point straight down (resp. left) by two units
  have harrow_vert : ∀ {x y : ℤ}, (x, y) ∈ board (2 * m + 1) → 2 ≤ y → y % 2 = 0 →
      C.arrow (x, y) = (x, y - 2) := by
    intro x y hb hy1 hyp
    have hf : C.f (x, y) = (x, y - 1) := by
      rw [hCf]
      exact snakeF_eq_vert_even _ hb (by show ¬(y = 0); omega) hyp
    have h1 : C.arrow (x, y) = (x, y) + 2 • (C.f (x, y) - (x, y)) := rfl
    rw [h1, hf]
    ext <;> simp [Prod.smul_mk] <;> omega
  have harrow_horiz : ∀ {x : ℤ}, (x, 0) ∈ board (2 * m + 1) → 2 ≤ x → x % 2 = 0 →
      C.arrow (x, 0) = (x - 2, 0) := by
    intro x hb hx1 hxp
    have hf : C.f (x, 0) = (x - 1, 0) := by
      rw [hCf]
      exact snakeF_eq_row0_even _ hb (by show x ≠ 0; omega) rfl hxp
    have h1 : C.arrow (x, 0) = (x, 0) + 2 • (C.f (x, 0) - (x, 0)) := rfl
    rw [h1, hf]
    ext <;> simp [Prod.smul_mk] <;> omega
  -- the corresponding edges of the arrow graph
  have hgAdj_vert : ∀ {x y : ℤ}, (x, y) ∈ board (2 * m + 1) → 2 ≤ y → y % 2 = 0 → x % 2 = 0 →
      C.gAdj (x, y) (x, y - 2) := by
    intro x y hb hy1 hyp hxp
    have hne : (x, y) ≠ C.empty := by
      rw [hEmpty]
      intro h
      rw [Prod.mk.injEq] at h
      omega
    refine Or.inl ⟨?_, hne, harrow_vert hb hy1 hyp, ?_⟩
    · rw [hspec]
      exact ⟨hb, hxp, hyp⟩
    · rw [mem_board, hnl] at hb
      obtain ⟨hxb1, hxb2, -, hyb2⟩ := hb
      have hxb2' : x ≤ 2 * (m : ℤ) := hxb2
      have hyb2' : y ≤ 2 * (m : ℤ) := hyb2
      exact hboard_of hxb1 hxb2' (by omega) (by omega)
  have hgAdj_horiz : ∀ {x : ℤ}, (x, 0) ∈ board (2 * m + 1) → 2 ≤ x → x % 2 = 0 →
      C.gAdj (x, 0) (x - 2, 0) := by
    intro x hb hx1 hxp
    have hne : (x, 0) ≠ C.empty := by
      rw [hEmpty]
      intro h
      rw [Prod.mk.injEq] at h
      omega
    refine Or.inl ⟨?_, hne, harrow_horiz hb hx1 hxp, ?_⟩
    · rw [hspec]
      exact ⟨hb, hxp, by simp⟩
    · rw [mem_board, hnl] at hb
      obtain ⟨hxb1, hxb2, -, -⟩ := hb
      have hxb1' : 0 ≤ x := hxb1
      have hxb2' : x ≤ 2 * (m : ℤ) := hxb2
      exact hboard_of (by omega) (by omega) le_rfl (by omega)
  -- connectivity: first straight down to the bottom row, then left to the origin
  have hconn_vert : ∀ (k : ℕ), ∀ {x : ℤ}, 0 ≤ x → x ≤ 2 * (m : ℤ) → x % 2 = 0 →
      (k : ℤ) ≤ (m : ℤ) → C.gConn (x, 2 * (k : ℤ)) (x, 0) := by
    intro k
    induction k with
    | zero =>
      intro x _ _ _ _
      show C.gConn (x, 0) (x, 0)
      exact Relation.ReflTransGen.refl
    | succ k ih =>
      intro x hx1 hx2 hxp hkm
      have hkm' : (k : ℤ) ≤ (m : ℤ) := by omega
      have hstep : C.gAdj (x, 2 * (k : ℤ) + 2) (x, 2 * (k : ℤ)) := by
        have hb : (x, 2 * (k : ℤ) + 2) ∈ board (2 * m + 1) :=
          hboard_of hx1 hx2 (by omega) (by omega)
        have h := hgAdj_vert hb (by omega) (by omega) hxp
        rwa [show 2 * (k : ℤ) + 2 - 2 = 2 * (k : ℤ) by ring] at h
      have h1 : C.gConn (x, 2 * (k : ℤ) + 2) (x, 0) :=
        Relation.ReflTransGen.trans (Relation.ReflTransGen.single hstep) (ih hx1 hx2 hxp hkm')
      have h2 : 2 * ((k + 1 : ℕ) : ℤ) = 2 * (k : ℤ) + 2 := by push_cast; ring
      rwa [h2]
  have hconn_horiz : ∀ (j : ℕ), (j : ℤ) ≤ (m : ℤ) → C.gConn (2 * (j : ℤ), 0) (0, 0) := by
    intro j
    induction j with
    | zero =>
      intro _
      show C.gConn ((0 : ℤ), 0) (0, 0)
      exact Relation.ReflTransGen.refl
    | succ j ih =>
      intro hjm
      have hjm' : (j : ℤ) ≤ (m : ℤ) := by omega
      have hstep : C.gAdj (2 * (j : ℤ) + 2, 0) (2 * (j : ℤ), 0) := by
        have hb : (2 * (j : ℤ) + 2, 0) ∈ board (2 * m + 1) :=
          hboard_of (by omega) (by omega) le_rfl (by omega)
        have h := hgAdj_horiz hb (by omega) (by omega)
        rwa [show 2 * (j : ℤ) + 2 - 2 = 2 * (j : ℤ) by ring] at h
      have h1 : C.gConn (2 * (j : ℤ) + 2, 0) (0, 0) :=
        Relation.ReflTransGen.trans (Relation.ReflTransGen.single hstep) (ih hjm')
      have h2 : 2 * ((j + 1 : ℕ) : ℤ) = 2 * (j : ℤ) + 2 := by push_cast; ring
      rwa [h2]
  have hconn_all : ∀ {x y : ℤ}, (x, y) ∈ board (2 * m + 1) → x % 2 = 0 → y % 2 = 0 →
      C.gConn (x, y) C.empty := by
    intro x y hb hxp hyp
    rw [mem_board, hnl] at hb
    obtain ⟨hx1, hx2, hy1, hy2⟩ := hb
    have hx1' : 0 ≤ x := hx1
    have hx2' : x ≤ 2 * (m : ℤ) := hx2
    have hy1' : 0 ≤ y := hy1
    have hy2' : y ≤ 2 * (m : ℤ) := hy2
    have hconn1 : C.gConn (x, y) (x, 0) := by
      have h1 : y = 2 * (((y / 2).toNat : ℕ) : ℤ) := by omega
      rw [h1]
      exact hconn_vert (y / 2).toNat hx1' hx2' hxp (by omega)
    have hconn2 : C.gConn (x, 0) (0, 0) := by
      have h1 : x = 2 * (((x / 2).toNat : ℕ) : ℤ) := by omega
      rw [h1]
      exact hconn_horiz (x / 2).toNat (by omega)
    rw [hEmpty]
    exact Relation.ReflTransGen.trans hconn1 hconn2
  -- hence the component of the origin is the full set of special cells
  have hcomp : C.comp = C.special := by
    ext ⟨x, y⟩
    rw [mem_comp]
    constructor
    · exact fun h => h.1
    · intro hs
      rw [hspec] at hs
      obtain ⟨hb, hxp, hyp⟩ := hs
      refine ⟨?_, hconn_all hb hxp hyp⟩
      rw [hspec]
      exact ⟨hb, hxp, hyp⟩
  -- count the special cells
  have hcard : C.special.card = (m + 1) ^ 2 := by
    rw [special_eq_prod, hEmpty, hnl]
    have h1 : (Finset.Icc (0 : ℤ) (2 * (m : ℤ))).filter (fun x => x % 2 = ((0, 0) : Cell).1 % 2) =
        (Finset.Icc (0 : ℤ) (2 * (m : ℤ))).filter (fun x => x % 2 = 0) := by
      apply Finset.filter_congr
      intro x _
      simp
    -- `rw` matches up to reducible defeq, so this rewrites both filters
    -- (`(0, 0).1` and `(0, 0).2` both reduce to `0`)
    rw [h1, Finset.card_product, card_Icc_emod_two_zero, sq]
  rw [kval_eq_comp_card, hcomp, hcard]
  have h2 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
  rw [h2]

end Config

/-!
## The family construction (all values `1 ≤ k ≤ m²`)

We build, for each `1 ≤ t ≤ m²`, a configuration on the `(2m+1) × (2m+1)` board
whose component of the uncovered square has exactly `t` cells.  The uncovered
square is `E = (2m-1, 1)`; the special cells are the `m²` odd-odd cells, ordered
by a snake through the `m × m` array.  Cells in positions `< t` point backwards
along the snake (forming the component), the rest point forwards.
-/

/-- The position of a special cell in the snake order. -/
def famPos (m : ℕ) (c : Cell) : ℕ :=
  ((c.2 - 1) / 2).toNat * m +
    if ((c.2 - 1) / 2).toNat % 2 = 0 then m - 1 - ((c.1 - 1) / 2).toNat
    else ((c.1 - 1) / 2).toNat

theorem famPos_eq (m : ℕ) (i j : ℕ) :
    famPos m ((2 * (i : ℤ) + 1 : ℤ), (2 * (j : ℤ) + 1 : ℤ)) =
      j * m + if j % 2 = 0 then m - 1 - i else i := by
  have h2 : ((2 * (j : ℤ) + 1 : ℤ) - 1) / 2 = (j : ℤ) := by omega
  have h1 : ((2 * (i : ℤ) + 1 : ℤ) - 1) / 2 = (i : ℤ) := by omega
  unfold famPos
  simp only [h2, h1, Int.toNat_natCast]

theorem famPos_lt (m : ℕ) (i j : ℕ) (hi : i < m) (hj : j < m) :
    famPos m ((2 * (i : ℤ) + 1 : ℤ), (2 * (j : ℤ) + 1 : ℤ)) < m ^ 2 := by
  rw [famPos_eq]
  have hs : (if j % 2 = 0 then m - 1 - i else i) ≤ m - 1 := by split_ifs <;> omega
  have hjm : j * m ≤ (m - 1) * m := Nat.mul_le_mul_right m (by omega)
  have hle : j * m + (if j % 2 = 0 then m - 1 - i else i) ≤ (m - 1) * m + (m - 1) :=
    Nat.add_le_add hjm hs
  apply lt_of_le_of_lt hle
  cases m with
  | zero => omega
  | succ k =>
    simp only [Nat.add_sub_cancel]
    have h5 : (k + 1) ^ 2 = k * (k + 1) + (k + 1) := by ring
    rw [h5]
    exact Nat.add_lt_add_left (by omega) _

theorem famPos_mod (m : ℕ) (i j : ℕ) (hi : i < m) (hj : j < m) :
    famPos m ((2 * (i : ℤ) + 1 : ℤ), (2 * (j : ℤ) + 1 : ℤ)) % m =
      if j % 2 = 0 then m - 1 - i else i := by
  rw [famPos_eq]
  by_cases h : j % 2 = 0
  · rw [if_pos h, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt (by omega : m - 1 - i < m)]
  · rw [if_neg h, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hi]

theorem famPos_div (m : ℕ) (i j : ℕ) (hi : i < m) (hj : j < m) :
    famPos m ((2 * (i : ℤ) + 1 : ℤ), (2 * (j : ℤ) + 1 : ℤ)) / m = j := by
  rw [famPos_eq]
  by_cases h : j % 2 = 0
  · rw [if_pos h, mul_comm j m, Nat.mul_add_div (by omega : 0 < m),
      Nat.div_eq_of_lt (by omega : m - 1 - i < m), add_zero]
  · rw [if_neg h, mul_comm j m, Nat.mul_add_div (by omega : 0 < m), Nat.div_eq_of_lt hi,
      add_zero]

/-- Injectivity of the snake position on standard-form cells. -/
theorem famPos_inj (m : ℕ) {i₁ i₂ j₁ j₂ : ℕ} (hi₁ : i₁ < m) (hj₁ : j₁ < m)
    (hi₂ : i₂ < m) (hj₂ : j₂ < m)
    (h : famPos m ((2 * (i₁ : ℤ) + 1 : ℤ), (2 * (j₁ : ℤ) + 1 : ℤ)) =
      famPos m ((2 * (i₂ : ℤ) + 1 : ℤ), (2 * (j₂ : ℤ) + 1 : ℤ))) :
    i₁ = i₂ ∧ j₁ = j₂ := by
  have hdiv1 := famPos_div m i₁ j₁ hi₁ hj₁
  have hdiv2 := famPos_div m i₂ j₂ hi₂ hj₂
  have hmod1 := famPos_mod m i₁ j₁ hi₁ hj₁
  have hmod2 := famPos_mod m i₂ j₂ hi₂ hj₂
  have hj : j₁ = j₂ := by rw [← hdiv1, ← hdiv2, h]
  have hmod : (if j₁ % 2 = 0 then m - 1 - i₁ else i₁) =
      (if j₂ % 2 = 0 then m - 1 - i₂ else i₂) := by
    rw [← hmod1, ← hmod2, h]
  subst hj
  split_ifs at hmod
  · exact ⟨by omega, rfl⟩
  · exact ⟨hmod, rfl⟩

/-- The cell at a given snake position. -/
def famCell (m : ℕ) (p : ℕ) : Cell :=
  (if (p / m) % 2 = 0 then 2 * (m : ℤ) - 1 - 2 * ((p % m : ℕ) : ℤ)
   else 2 * ((p % m : ℕ) : ℤ) + 1,
   2 * ((p / m : ℕ) : ℤ) + 1)

theorem famCell_eq (m : ℕ) (p : ℕ) (hp : p < m ^ 2) (hm : 0 < m) :
    ∃ i j : ℕ, i < m ∧ j < m ∧
      famCell m p = ((2 * (i : ℤ) + 1 : ℤ), (2 * (j : ℤ) + 1 : ℤ)) ∧
      famPos m ((2 * (i : ℤ) + 1 : ℤ), (2 * (j : ℤ) + 1 : ℤ)) = p := by
  have hjm : p / m < m := by
    rw [Nat.div_lt_iff_lt_mul hm]
    have h6 : m ^ 2 = m * m := by ring
    rw [h6] at hp
    exact hp
  have hrm : p % m < m := Nat.mod_lt p hm
  by_cases hj : (p / m) % 2 = 0
  · refine ⟨m - 1 - p % m, p / m, by omega, hjm, ?_, ?_⟩
    · unfold famCell
      simp only [if_pos hj]
      have h7 : (2 * (m : ℤ) - 1 - 2 * ((p % m : ℕ) : ℤ)) =
          2 * ((m - 1 - p % m : ℕ) : ℤ) + 1 := by omega
      rw [h7]
    · rw [famPos_eq, if_pos hj]
      have h5 : m - 1 - (m - 1 - p % m) = p % m := by omega
      rw [h5]
      exact Nat.div_add_mod' p m
  · refine ⟨p % m, p / m, hrm, hjm, ?_, ?_⟩
    · unfold famCell
      simp only [if_neg hj]
    · rw [famPos_eq, if_neg hj]
      exact Nat.div_add_mod' p m

/-- The gap column: the unique unused in-row midpoint column
(only relevant when `t % m ≠ 0`). -/
def famGx (m t : ℕ) : ℤ :=
  if (t / m) % 2 = 0 then 2 * (m : ℤ) - 2 * ((t % m : ℕ) : ℤ) else 2 * ((t % m : ℕ) : ℤ)

theorem famGx_eq_of_even {m t : ℕ} (h : (t / m) % 2 = 0) :
    famGx m t = 2 * (m : ℤ) - 2 * ((t % m : ℕ) : ℤ) := by
  simp only [famGx, if_pos h]

theorem famGx_eq_of_odd {m t : ℕ} (h : ¬(t / m) % 2 = 0) :
    famGx m t = 2 * ((t % m : ℕ) : ℤ) := by
  simp only [famGx, if_neg h]

theorem famGx_mem {m t : ℕ} (hm : 0 < m) (hr : t % m ≠ 0) :
    2 ≤ famGx m t ∧ famGx m t ≤ 2 * (m : ℤ) - 2 ∧ ∃ k : ℤ, famGx m t = 2 * k := by
  have hrm : 1 ≤ t % m ∧ t % m ≤ m - 1 := by
    have hml := Nat.mod_lt t hm
    omega
  by_cases h : (t / m) % 2 = 0
  · rw [famGx_eq_of_even h]
    refine ⟨by omega, by omega, (m : ℤ) - ((t % m : ℕ) : ℤ), by ring⟩
  · rw [famGx_eq_of_odd h]
    refine ⟨by omega, by omega, ((t % m : ℕ) : ℤ), rfl⟩

/-- The row in which the column-0 edge cell is paired horizontally. -/
def famB0 (m t : ℕ) : ℕ :=
  if t % m = 0 then 0 else if t / m = 0 then 0 else if (t / m) % 2 = 0 then t / m else 0

/-- The row in which the column-`2m` edge cell is paired horizontally. -/
def famB1 (m t : ℕ) : ℕ :=
  if t % m = 0 then t / m else if t / m = 0 then 0 else if (t / m) % 2 = 0 then 0 else t / m

theorem famB0_eq_of_mod_zero {m t : ℕ} (h : t % m = 0) : famB0 m t = 0 := by
  simp only [famB0, if_pos h]

theorem famB1_eq_of_mod_zero {m t : ℕ} (h : t % m = 0) : famB1 m t = t / m := by
  simp only [famB1, if_pos h]

theorem famB0_eq_of_div_zero {m t : ℕ} (h1 : t % m ≠ 0) (h2 : t / m = 0) :
    famB0 m t = 0 := by
  simp only [famB0, if_neg h1, if_pos h2]

theorem famB1_eq_of_div_zero {m t : ℕ} (h1 : t % m ≠ 0) (h2 : t / m = 0) :
    famB1 m t = 0 := by
  simp only [famB1, if_neg h1, if_pos h2]

theorem famB0_eq_of_even {m t : ℕ} (h1 : t % m ≠ 0) (h2 : t / m ≠ 0)
    (h3 : (t / m) % 2 = 0) : famB0 m t = t / m := by
  simp only [famB0, if_neg h1, if_neg h2, if_pos h3]

theorem famB1_eq_of_even {m t : ℕ} (h1 : t % m ≠ 0) (h2 : t / m ≠ 0)
    (h3 : (t / m) % 2 = 0) : famB1 m t = 0 := by
  simp only [famB1, if_neg h1, if_neg h2, if_pos h3]

theorem famB0_eq_of_odd {m t : ℕ} (h1 : t % m ≠ 0) (h2 : t / m ≠ 0)
    (h3 : ¬(t / m) % 2 = 0) : famB0 m t = 0 := by
  simp only [famB0, if_neg h1, if_neg h2, if_neg h3]

theorem famB1_eq_of_odd {m t : ℕ} (h1 : t % m ≠ 0) (h2 : t / m ≠ 0)
    (h3 : ¬(t / m) % 2 = 0) : famB1 m t = t / m := by
  simp only [famB1, if_neg h1, if_neg h2, if_neg h3]

theorem famB0_le {m t : ℕ} : famB0 m t ≤ t / m := by
  unfold famB0
  split_ifs <;> simp

theorem famB1_le {m t : ℕ} : famB1 m t ≤ t / m := by
  unfold famB1
  split_ifs <;> simp

/-- The hole column in an even row: the vertical midpoint used by a turning
snake arrow. -/
def famHoleX (m : ℕ) (b : ℕ) : ℤ := if b % 2 = 1 then 1 else 2 * (m : ℤ) - 1

theorem famHoleX_eq_of_odd {m : ℕ} {b : ℕ} (h : b % 2 = 1) : famHoleX m b = 1 := by
  simp only [famHoleX, if_pos h]

theorem famHoleX_eq_of_even {m : ℕ} {b : ℕ} (h : ¬b % 2 = 1) :
    famHoleX m b = 2 * (m : ℤ) - 1 := by
  simp only [famHoleX, if_neg h]

/-- The escape column of an even row: the even cell of the row that is paired
vertically instead of horizontally. -/
def famEsc (m t : ℕ) (b : ℕ) : ℤ :=
  if t % m ≠ 0 ∧ b = t / m then famGx m t
  else if 1 ≤ b ∧ b * m ≠ t ∧ b % 2 = 1 then 2 * (m : ℤ)
  else if 1 ≤ b ∧ b * m ≠ t then 0
  else if b = famB0 m t then 2 * (m : ℤ)
  else 0

theorem famEsc_eq_gx {m t : ℕ} {b : ℕ} (h1 : t % m ≠ 0) (h2 : b = t / m) :
    famEsc m t b = famGx m t := by
  have h : t % m ≠ 0 ∧ b = t / m := ⟨h1, h2⟩
  simp only [famEsc, if_pos h]

theorem famEsc_eq_two_m_of_odd {m t : ℕ} {b : ℕ} (h : ¬(t % m ≠ 0 ∧ b = t / m))
    (hb : 1 ≤ b) (hm : b * m ≠ t) (ho : b % 2 = 1) :
    famEsc m t b = 2 * (m : ℤ) := by
  have h2 : 1 ≤ b ∧ b * m ≠ t ∧ b % 2 = 1 := ⟨hb, hm, ho⟩
  simp only [famEsc, if_neg h, if_pos h2]

theorem famEsc_eq_zero_of_even {m t : ℕ} {b : ℕ} (h : ¬(t % m ≠ 0 ∧ b = t / m))
    (hb : 1 ≤ b) (hm : b * m ≠ t) (ho : ¬b % 2 = 1) :
    famEsc m t b = 0 := by
  have h2 : ¬(1 ≤ b ∧ b * m ≠ t ∧ b % 2 = 1) := fun hh => ho hh.2.2
  have h3 : 1 ≤ b ∧ b * m ≠ t := ⟨hb, hm⟩
  simp only [famEsc, if_neg h, if_neg h2, if_pos h3]

theorem famEsc_eq_two_m_of_b0 {m t : ℕ} {b : ℕ} (h : ¬(t % m ≠ 0 ∧ b = t / m))
    (hh : ¬(1 ≤ b ∧ b * m ≠ t)) (h0 : b = famB0 m t) :
    famEsc m t b = 2 * (m : ℤ) := by
  have h2 : ¬(1 ≤ b ∧ b * m ≠ t ∧ b % 2 = 1) := fun hhh => hh ⟨hhh.1, hhh.2.1⟩
  have h3 : ¬(1 ≤ b ∧ b * m ≠ t) := hh
  simp only [famEsc, if_neg h, if_neg h2, if_neg h3, if_pos h0]

theorem famEsc_eq_zero {m t : ℕ} {b : ℕ} (h : ¬(t % m ≠ 0 ∧ b = t / m))
    (hh : ¬(1 ≤ b ∧ b * m ≠ t)) (h0 : b ≠ famB0 m t) :
    famEsc m t b = 0 := by
  have h2 : ¬(1 ≤ b ∧ b * m ≠ t ∧ b % 2 = 1) := fun hhh => hh ⟨hhh.1, hhh.2.1⟩
  have h3 : ¬(1 ≤ b ∧ b * m ≠ t) := hh
  simp only [famEsc, if_neg h, if_neg h2, if_neg h3, if_neg h0]

theorem famEsc_bounds {m t : ℕ} (hm : 0 < m) (b : ℕ) :
    0 ≤ famEsc m t b ∧ famEsc m t b ≤ 2 * (m : ℤ) := by
  unfold famEsc
  split_ifs with g1 g2 g3 g4
  · have hg := famGx_mem hm g1.1
    omega
  · omega
  · omega
  · omega
  · omega
/-- The pairing function of the family configuration. -/
noncomputable def famF (m t : ℕ) (c : Cell) : Cell :=
  if c ∈ board (2 * m + 1) then
    if c.2 % 2 = 1 then
      if c.1 % 2 = 1 then
        if famPos m c = 0 then c
        else if famPos m c < t then
          if famPos m c % m = 0 then (c.1, c.2 - 1)
          else if ((c.2 - 1) / 2).toNat % 2 = 0 then (c.1 + 1, c.2)
          else (c.1 - 1, c.2)
        else
          if famPos m c % m = m - 1 then (c.1, c.2 + 1)
          else if ((c.2 - 1) / 2).toNat % 2 = 0 then (c.1 - 1, c.2)
          else (c.1 + 1, c.2)
      else
        if c.1 = 0 then
          (0, if ((c.2 - 1) / 2).toNat < famB0 m t then c.2 - 1 else c.2 + 1)
        else if c.1 = 2 * (m : ℤ) then
          (2 * (m : ℤ), if ((c.2 - 1) / 2).toNat < famB1 m t then c.2 - 1 else c.2 + 1)
        else if t % m ≠ 0 ∧ ((c.2 - 1) / 2).toNat = t / m ∧ c.1 = famGx m t then
          (c.1, c.2 - 1)
        else if ((c.2 - 1) / 2).toNat % 2 = 0 then
          (if famPos m (c.1 - 1, c.2) < t then (c.1 - 1, c.2) else (c.1 + 1, c.2))
        else
          (if famPos m (c.1 + 1, c.2) < t then (c.1 + 1, c.2) else (c.1 - 1, c.2))
    else
      if c.1 % 2 = 0 then
        if c.1 = 0 then
          if (c.2 / 2).toNat = famB0 m t then (1, c.2)
          else if (c.2 / 2).toNat < famB0 m t then (0, c.2 + 1)
          else (0, c.2 - 1)
        else if c.1 = 2 * (m : ℤ) then
          if (c.2 / 2).toNat = famB1 m t then (2 * (m : ℤ) - 1, c.2)
          else if (c.2 / 2).toNat < famB1 m t then (2 * (m : ℤ), c.2 + 1)
          else (2 * (m : ℤ), c.2 - 1)
        else if t % m ≠ 0 ∧ (c.2 / 2).toNat = t / m ∧ c.1 = famGx m t then (c.1, c.2 + 1)
        else if c.1 < famEsc m t (c.2 / 2).toNat then (c.1 + 1, c.2)
        else (c.1 - 1, c.2)
      else
        if 1 ≤ (c.2 / 2).toNat ∧ (c.2 / 2).toNat * m ≠ t ∧ c.1 = famHoleX m (c.2 / 2).toNat then
          (if (c.2 / 2).toNat * m < t then (c.1, c.2 + 1) else (c.1, c.2 - 1))
        else if c.1 < famEsc m t (c.2 / 2).toNat then (c.1 - 1, c.2)
        else (c.1 + 1, c.2)
  else c

theorem famF_off {m t : ℕ} {c : Cell} (hc : c ∉ board (2 * m + 1)) : famF m t c = c := by
  simp only [famF, if_neg hc]

theorem famF_fixed_of_pos_zero {m t : ℕ} {c : Cell} (hc : c ∈ board (2 * m + 1))
    (hy : c.2 % 2 = 1) (hx : c.1 % 2 = 1) (h0 : famPos m c = 0) :
    famF m t c = c := by
  simp only [famF, if_pos hc, if_pos hy, if_pos hx, if_pos h0]

theorem famF_chain_turn {m t : ℕ} {c : Cell} (hc : c ∈ board (2 * m + 1))
    (hy : c.2 % 2 = 1) (hx : c.1 % 2 = 1) (h0 : famPos m c ≠ 0) (hlt : famPos m c < t)
    (hrs : famPos m c % m = 0) :
    famF m t c = (c.1, c.2 - 1) := by
  simp only [famF, if_pos hc, if_pos hy, if_pos hx, if_neg h0, if_pos hlt, if_pos hrs]

theorem famF_chain_even {m t : ℕ} {c : Cell} (hc : c ∈ board (2 * m + 1))
    (hy : c.2 % 2 = 1) (hx : c.1 % 2 = 1) (h0 : famPos m c ≠ 0) (hlt : famPos m c < t)
    (hrs : famPos m c % m ≠ 0) (hj : ((c.2 - 1) / 2).toNat % 2 = 0) :
    famF m t c = (c.1 + 1, c.2) := by
  simp only [famF, if_pos hc, if_pos hy, if_pos hx, if_neg h0, if_pos hlt, if_neg hrs,
    if_pos hj]

theorem famF_chain_odd {m t : ℕ} {c : Cell} (hc : c ∈ board (2 * m + 1))
    (hy : c.2 % 2 = 1) (hx : c.1 % 2 = 1) (h0 : famPos m c ≠ 0) (hlt : famPos m c < t)
    (hrs : famPos m c % m ≠ 0) (hj : ¬((c.2 - 1) / 2).toNat % 2 = 0) :
    famF m t c = (c.1 - 1, c.2) := by
  simp only [famF, if_pos hc, if_pos hy, if_pos hx, if_neg h0, if_pos hlt, if_neg hrs,
    if_neg hj]

theorem famF_nonchain_turn {m t : ℕ} {c : Cell} (hc : c ∈ board (2 * m + 1))
    (hy : c.2 % 2 = 1) (hx : c.1 % 2 = 1) (h0 : famPos m c ≠ 0) (hge : ¬famPos m c < t)
    (hre : famPos m c % m = m - 1) :
    famF m t c = (c.1, c.2 + 1) := by
  simp only [famF, if_pos hc, if_pos hy, if_pos hx, if_neg h0, if_neg hge, if_pos hre]

theorem famF_nonchain_even {m t : ℕ} {c : Cell} (hc : c ∈ board (2 * m + 1))
    (hy : c.2 % 2 = 1) (hx : c.1 % 2 = 1) (h0 : famPos m c ≠ 0) (hge : ¬famPos m c < t)
    (hre : famPos m c % m ≠ m - 1) (hj : ((c.2 - 1) / 2).toNat % 2 = 0) :
    famF m t c = (c.1 - 1, c.2) := by
  simp only [famF, if_pos hc, if_pos hy, if_pos hx, if_neg h0, if_neg hge, if_neg hre,
    if_pos hj]

theorem famF_nonchain_odd {m t : ℕ} {c : Cell} (hc : c ∈ board (2 * m + 1))
    (hy : c.2 % 2 = 1) (hx : c.1 % 2 = 1) (h0 : famPos m c ≠ 0) (hge : ¬famPos m c < t)
    (hre : famPos m c % m ≠ m - 1) (hj : ¬((c.2 - 1) / 2).toNat % 2 = 0) :
    famF m t c = (c.1 + 1, c.2) := by
  simp only [famF, if_pos hc, if_pos hy, if_pos hx, if_neg h0, if_neg hge, if_neg hre,
    if_neg hj]

theorem famF_col0_of_lt {m t : ℕ} {c : Cell} (hc : c ∈ board (2 * m + 1))
    (hy : c.2 % 2 = 1) (hx : ¬c.1 % 2 = 1) (h0 : c.1 = 0)
    (hj : ((c.2 - 1) / 2).toNat < famB0 m t) :
    famF m t c = (0, c.2 - 1) := by
  simp only [famF, if_pos hc, if_pos hy, if_neg hx, if_pos h0, if_pos hj]

theorem famF_col0_of_ge {m t : ℕ} {c : Cell} (hc : c ∈ board (2 * m + 1))
    (hy : c.2 % 2 = 1) (hx : ¬c.1 % 2 = 1) (h0 : c.1 = 0)
    (hj : ¬((c.2 - 1) / 2).toNat < famB0 m t) :
    famF m t c = (0, c.2 + 1) := by
  simp only [famF, if_pos hc, if_pos hy, if_neg hx, if_pos h0, if_neg hj]

theorem famF_colm_of_lt {m t : ℕ} {c : Cell} (hc : c ∈ board (2 * m + 1))
    (hy : c.2 % 2 = 1) (hx : ¬c.1 % 2 = 1) (h0 : c.1 ≠ 0) (hm : c.1 = 2 * (m : ℤ))
    (hj : ((c.2 - 1) / 2).toNat < famB1 m t) :
    famF m t c = (2 * (m : ℤ), c.2 - 1) := by
  simp only [famF, if_pos hc, if_pos hy, if_neg hx, if_neg h0, if_pos hm, if_pos hj]

theorem famF_colm_of_ge {m t : ℕ} {c : Cell} (hc : c ∈ board (2 * m + 1))
    (hy : c.2 % 2 = 1) (hx : ¬c.1 % 2 = 1) (h0 : c.1 ≠ 0) (hm : c.1 = 2 * (m : ℤ))
    (hj : ¬((c.2 - 1) / 2).toNat < famB1 m t) :
    famF m t c = (2 * (m : ℤ), c.2 + 1) := by
  simp only [famF, if_pos hc, if_pos hy, if_neg hx, if_neg h0, if_pos hm, if_neg hj]

theorem famF_gap_mid {m t : ℕ} {c : Cell} (hc : c ∈ board (2 * m + 1))
    (hy : c.2 % 2 = 1) (hx : ¬c.1 % 2 = 1) (h0 : c.1 ≠ 0) (hm : c.1 ≠ 2 * (m : ℤ))
    (hg : t % m ≠ 0 ∧ ((c.2 - 1) / 2).toNat = t / m ∧ c.1 = famGx m t) :
    famF m t c = (c.1, c.2 - 1) := by
  simp only [famF, if_pos hc, if_pos hy, if_neg hx, if_neg h0, if_neg hm, if_pos hg]

theorem famF_mid_even_of_lt {m t : ℕ} {c : Cell} (hc : c ∈ board (2 * m + 1))
    (hy : c.2 % 2 = 1) (hx : ¬c.1 % 2 = 1) (h0 : c.1 ≠ 0) (hm : c.1 ≠ 2 * (m : ℤ))
    (hg : ¬(t % m ≠ 0 ∧ ((c.2 - 1) / 2).toNat = t / m ∧ c.1 = famGx m t))
    (hj : ((c.2 - 1) / 2).toNat % 2 = 0) (hp : famPos m (c.1 - 1, c.2) < t) :
    famF m t c = (c.1 - 1, c.2) := by
  simp only [famF, if_pos hc, if_pos hy, if_neg hx, if_neg h0, if_neg hm, if_neg hg,
    if_pos hj, if_pos hp]

theorem famF_mid_even_of_ge {m t : ℕ} {c : Cell} (hc : c ∈ board (2 * m + 1))
    (hy : c.2 % 2 = 1) (hx : ¬c.1 % 2 = 1) (h0 : c.1 ≠ 0) (hm : c.1 ≠ 2 * (m : ℤ))
    (hg : ¬(t % m ≠ 0 ∧ ((c.2 - 1) / 2).toNat = t / m ∧ c.1 = famGx m t))
    (hj : ((c.2 - 1) / 2).toNat % 2 = 0) (hp : ¬famPos m (c.1 - 1, c.2) < t) :
    famF m t c = (c.1 + 1, c.2) := by
  simp only [famF, if_pos hc, if_pos hy, if_neg hx, if_neg h0, if_neg hm, if_neg hg,
    if_pos hj, if_neg hp]

theorem famF_mid_odd_of_lt {m t : ℕ} {c : Cell} (hc : c ∈ board (2 * m + 1))
    (hy : c.2 % 2 = 1) (hx : ¬c.1 % 2 = 1) (h0 : c.1 ≠ 0) (hm : c.1 ≠ 2 * (m : ℤ))
    (hg : ¬(t % m ≠ 0 ∧ ((c.2 - 1) / 2).toNat = t / m ∧ c.1 = famGx m t))
    (hj : ¬((c.2 - 1) / 2).toNat % 2 = 0) (hp : famPos m (c.1 + 1, c.2) < t) :
    famF m t c = (c.1 + 1, c.2) := by
  simp only [famF, if_pos hc, if_pos hy, if_neg hx, if_neg h0, if_neg hm, if_neg hg,
    if_neg hj, if_pos hp]

theorem famF_mid_odd_of_ge {m t : ℕ} {c : Cell} (hc : c ∈ board (2 * m + 1))
    (hy : c.2 % 2 = 1) (hx : ¬c.1 % 2 = 1) (h0 : c.1 ≠ 0) (hm : c.1 ≠ 2 * (m : ℤ))
    (hg : ¬(t % m ≠ 0 ∧ ((c.2 - 1) / 2).toNat = t / m ∧ c.1 = famGx m t))
    (hj : ¬((c.2 - 1) / 2).toNat % 2 = 0) (hp : ¬famPos m (c.1 + 1, c.2) < t) :
    famF m t c = (c.1 - 1, c.2) := by
  simp only [famF, if_pos hc, if_pos hy, if_neg hx, if_neg h0, if_neg hm, if_neg hg,
    if_neg hj, if_neg hp]

theorem famF_e0_eq {m t : ℕ} {c : Cell} (hc : c ∈ board (2 * m + 1))
    (hy : ¬c.2 % 2 = 1) (hx : c.1 % 2 = 0) (h0 : c.1 = 0)
    (hb : (c.2 / 2).toNat = famB0 m t) :
    famF m t c = (1, c.2) := by
  simp only [famF, if_pos hc, if_neg hy, if_pos hx, if_pos h0, if_pos hb]

theorem famF_e0_lt {m t : ℕ} {c : Cell} (hc : c ∈ board (2 * m + 1))
    (hy : ¬c.2 % 2 = 1) (hx : c.1 % 2 = 0) (h0 : c.1 = 0)
    (hb1 : (c.2 / 2).toNat ≠ famB0 m t) (hb2 : (c.2 / 2).toNat < famB0 m t) :
    famF m t c = (0, c.2 + 1) := by
  simp only [famF, if_pos hc, if_neg hy, if_pos hx, if_pos h0, if_neg hb1, if_pos hb2]

theorem famF_e0_gt {m t : ℕ} {c : Cell} (hc : c ∈ board (2 * m + 1))
    (hy : ¬c.2 % 2 = 1) (hx : c.1 % 2 = 0) (h0 : c.1 = 0)
    (hb1 : (c.2 / 2).toNat ≠ famB0 m t) (hb2 : ¬(c.2 / 2).toNat < famB0 m t) :
    famF m t c = (0, c.2 - 1) := by
  simp only [famF, if_pos hc, if_neg hy, if_pos hx, if_pos h0, if_neg hb1, if_neg hb2]

theorem famF_em_eq {m t : ℕ} {c : Cell} (hc : c ∈ board (2 * m + 1))
    (hy : ¬c.2 % 2 = 1) (hx : c.1 % 2 = 0) (h0 : c.1 ≠ 0) (hm : c.1 = 2 * (m : ℤ))
    (hb : (c.2 / 2).toNat = famB1 m t) :
    famF m t c = (2 * (m : ℤ) - 1, c.2) := by
  simp only [famF, if_pos hc, if_neg hy, if_pos hx, if_neg h0, if_pos hm, if_pos hb]

theorem famF_em_lt {m t : ℕ} {c : Cell} (hc : c ∈ board (2 * m + 1))
    (hy : ¬c.2 % 2 = 1) (hx : c.1 % 2 = 0) (h0 : c.1 ≠ 0) (hm : c.1 = 2 * (m : ℤ))
    (hb1 : (c.2 / 2).toNat ≠ famB1 m t) (hb2 : (c.2 / 2).toNat < famB1 m t) :
    famF m t c = (2 * (m : ℤ), c.2 + 1) := by
  simp only [famF, if_pos hc, if_neg hy, if_pos hx, if_neg h0, if_pos hm, if_neg hb1,
    if_pos hb2]

theorem famF_em_gt {m t : ℕ} {c : Cell} (hc : c ∈ board (2 * m + 1))
    (hy : ¬c.2 % 2 = 1) (hx : c.1 % 2 = 0) (h0 : c.1 ≠ 0) (hm : c.1 = 2 * (m : ℤ))
    (hb1 : (c.2 / 2).toNat ≠ famB1 m t) (hb2 : ¬(c.2 / 2).toNat < famB1 m t) :
    famF m t c = (2 * (m : ℤ), c.2 - 1) := by
  simp only [famF, if_pos hc, if_neg hy, if_pos hx, if_neg h0, if_pos hm, if_neg hb1,
    if_neg hb2]

theorem famF_gap_e {m t : ℕ} {c : Cell} (hc : c ∈ board (2 * m + 1))
    (hy : ¬c.2 % 2 = 1) (hx : c.1 % 2 = 0) (h0 : c.1 ≠ 0) (hm : c.1 ≠ 2 * (m : ℤ))
    (hg : t % m ≠ 0 ∧ (c.2 / 2).toNat = t / m ∧ c.1 = famGx m t) :
    famF m t c = (c.1, c.2 + 1) := by
  simp only [famF, if_pos hc, if_neg hy, if_pos hx, if_neg h0, if_neg hm, if_pos hg]

theorem famF_eint_of_lt {m t : ℕ} {c : Cell} (hc : c ∈ board (2 * m + 1))
    (hy : ¬c.2 % 2 = 1) (hx : c.1 % 2 = 0) (h0 : c.1 ≠ 0) (hm : c.1 ≠ 2 * (m : ℤ))
    (hg : ¬(t % m ≠ 0 ∧ (c.2 / 2).toNat = t / m ∧ c.1 = famGx m t))
    (he : c.1 < famEsc m t (c.2 / 2).toNat) :
    famF m t c = (c.1 + 1, c.2) := by
  simp only [famF, if_pos hc, if_neg hy, if_pos hx, if_neg h0, if_neg hm, if_neg hg,
    if_pos he]

theorem famF_eint_of_ge {m t : ℕ} {c : Cell} (hc : c ∈ board (2 * m + 1))
    (hy : ¬c.2 % 2 = 1) (hx : c.1 % 2 = 0) (h0 : c.1 ≠ 0) (hm : c.1 ≠ 2 * (m : ℤ))
    (hg : ¬(t % m ≠ 0 ∧ (c.2 / 2).toNat = t / m ∧ c.1 = famGx m t))
    (he : ¬c.1 < famEsc m t (c.2 / 2).toNat) :
    famF m t c = (c.1 - 1, c.2) := by
  simp only [famF, if_pos hc, if_neg hy, if_pos hx, if_neg h0, if_neg hm, if_neg hg,
    if_neg he]

theorem famF_hole_of_lt {m t : ℕ} {c : Cell} (hc : c ∈ board (2 * m + 1))
    (hy : ¬c.2 % 2 = 1) (hx : ¬c.1 % 2 = 0)
    (hh : 1 ≤ (c.2 / 2).toNat ∧ (c.2 / 2).toNat * m ≠ t ∧ c.1 = famHoleX m (c.2 / 2).toNat)
    (hb : (c.2 / 2).toNat * m < t) :
    famF m t c = (c.1, c.2 + 1) := by
  simp only [famF, if_pos hc, if_neg hy, if_neg hx, if_pos hh, if_pos hb]

theorem famF_hole_of_ge {m t : ℕ} {c : Cell} (hc : c ∈ board (2 * m + 1))
    (hy : ¬c.2 % 2 = 1) (hx : ¬c.1 % 2 = 0)
    (hh : 1 ≤ (c.2 / 2).toNat ∧ (c.2 / 2).toNat * m ≠ t ∧ c.1 = famHoleX m (c.2 / 2).toNat)
    (hb : ¬(c.2 / 2).toNat * m < t) :
    famF m t c = (c.1, c.2 - 1) := by
  simp only [famF, if_pos hc, if_neg hy, if_neg hx, if_pos hh, if_neg hb]

theorem famF_oint_of_lt {m t : ℕ} {c : Cell} (hc : c ∈ board (2 * m + 1))
    (hy : ¬c.2 % 2 = 1) (hx : ¬c.1 % 2 = 0)
    (hh : ¬(1 ≤ (c.2 / 2).toNat ∧ (c.2 / 2).toNat * m ≠ t ∧
      c.1 = famHoleX m (c.2 / 2).toNat))
    (he : c.1 < famEsc m t (c.2 / 2).toNat) :
    famF m t c = (c.1 - 1, c.2) := by
  simp only [famF, if_pos hc, if_neg hy, if_neg hx, if_neg hh, if_pos he]

theorem famF_oint_of_ge {m t : ℕ} {c : Cell} (hc : c ∈ board (2 * m + 1))
    (hy : ¬c.2 % 2 = 1) (hx : ¬c.1 % 2 = 0)
    (hh : ¬(1 ≤ (c.2 / 2).toNat ∧ (c.2 / 2).toNat * m ≠ t ∧
      c.1 = famHoleX m (c.2 / 2).toNat))
    (he : ¬c.1 < famEsc m t (c.2 / 2).toNat) :
    famF m t c = (c.1 + 1, c.2) := by
  simp only [famF, if_pos hc, if_neg hy, if_neg hx, if_neg hh, if_neg he]
theorem famEsc_even {m t : ℕ} (hm : 0 < m) (b : ℕ) : ∃ k : ℤ, famEsc m t b = 2 * k := by
  unfold famEsc
  split_ifs with g1 g2 g3 g4
  · exact (famGx_mem hm g1.1).2.2
  · exact ⟨(m : ℤ), rfl⟩
  · exact ⟨0, rfl⟩
  · exact ⟨(m : ℤ), rfl⟩
  · exact ⟨0, rfl⟩

theorem famB0_spec {m t : ℕ} :
    (t % m = 0 ∧ famB0 m t = 0) ∨ (t % m ≠ 0 ∧ t / m = 0 ∧ famB0 m t = 0) ∨
    (t % m ≠ 0 ∧ t / m ≠ 0 ∧ (t / m) % 2 = 0 ∧ famB0 m t = t / m) ∨
    (t % m ≠ 0 ∧ t / m ≠ 0 ∧ ¬(t / m) % 2 = 0 ∧ famB0 m t = 0) := by
  unfold famB0
  split_ifs with h1 h2 h3
  · exact Or.inl ⟨h1, rfl⟩
  · exact Or.inr (Or.inl ⟨h1, h2, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h1, h2, h3, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨h1, h2, h3, rfl⟩))

theorem famB1_spec {m t : ℕ} :
    (t % m = 0 ∧ famB1 m t = t / m) ∨ (t % m ≠ 0 ∧ t / m = 0 ∧ famB1 m t = 0) ∨
    (t % m ≠ 0 ∧ t / m ≠ 0 ∧ (t / m) % 2 = 0 ∧ famB1 m t = 0) ∨
    (t % m ≠ 0 ∧ t / m ≠ 0 ∧ ¬(t / m) % 2 = 0 ∧ famB1 m t = t / m) := by
  unfold famB1
  split_ifs with h1 h2 h3
  · exact Or.inl ⟨h1, rfl⟩
  · exact Or.inr (Or.inl ⟨h1, h2, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h1, h2, h3, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨h1, h2, h3, rfl⟩))

/-- In the row whose column-0 edge cell is paired horizontally, the escape
column exceeds 1. -/
theorem famEsc_gt_one_of_b0 {m t : ℕ} (hm : 0 < m) {b : ℕ} (hb : b = famB0 m t) :
    (1 : ℤ) < famEsc m t b := by
  have h0 : famEsc m t b ≠ 0 := by
    intro he0
    unfold famEsc at he0
    split_ifs at he0 with g1 g2 g3 g4
    · have hgx := famGx_mem hm g1.1
      omega
    · omega
    · rcases famB0_spec (m := m) (t := t) with h | h | h | h
      · omega
      · omega
      · exact ‹¬(t % m ≠ 0 ∧ b = t / m)› ⟨h.1, by rw [hb]; exact h.2.2.2⟩
      · omega
    · omega
  obtain ⟨k, hk⟩ := famEsc_even (t := t) hm b
  have hnn := (famEsc_bounds (t := t) hm b).1
  rw [hk] at h0 hnn ⊢
  omega

/-- In the row whose column-`2m` edge cell is paired horizontally, the escape
column is at most `2m - 2`. -/
theorem famEsc_lt_of_b1 {m t : ℕ} (hm : 0 < m) (ht : 1 ≤ t) {b : ℕ} (hb : b = famB1 m t) :
    famEsc m t b ≤ 2 * (m : ℤ) - 2 := by
  have h2m : famEsc m t b ≠ 2 * (m : ℤ) := by
    intro he2
    unfold famEsc at he2
    split_ifs at he2 with g1 g2 g3 g4
    · have hgx := famGx_mem hm g1.1
      omega
    · rcases famB1_spec (m := m) (t := t) with h | h | h | h
      · have hbm : b * m = t := by
          rw [hb, h.2]
          exact Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h.1)
        exact g2.2.1 hbm
      · have hb0 : b = 0 := by rw [hb]; exact h.2.2
        omega
      · have hb0 : b = 0 := by rw [hb]; exact h.2.2.2
        omega
      · exact ‹¬(t % m ≠ 0 ∧ b = t / m)› ⟨h.1, by rw [hb]; exact h.2.2.2⟩
    · omega
    · have hbb : famB1 m t = famB0 m t := by rw [← hb]; exact g4
      by_cases hr : t % m = 0
      · rw [famB0_eq_of_mod_zero hr, famB1_eq_of_mod_zero hr] at hbb
        have h0' : t = 0 := by
          have h9 := Nat.div_add_mod' t m
          rw [hbb, hr] at h9
          omega
        omega
      · by_cases hq : t / m = 0
        · rw [famB1_eq_of_div_zero hr hq] at hb
          exact ‹¬(t % m ≠ 0 ∧ b = t / m)› ⟨hr, by rw [hb]; exact hq.symm⟩
        · by_cases hp : (t / m) % 2 = 0
          · rw [famB0_eq_of_even hr hq hp, famB1_eq_of_even hr hq hp] at hbb
            exact hq hbb.symm
          · rw [famB0_eq_of_odd hr hq hp, famB1_eq_of_odd hr hq hp] at hbb
            exact hq hbb
    · omega
  obtain ⟨k, hk⟩ := famEsc_even (t := t) hm b
  have hle := (famEsc_bounds (t := t) hm b).2
  rw [hk] at h2m hle ⊢
  omega

/-- A special cell has the standard form `(2i+1, 2j+1)` with `i, j < m`. -/
theorem fam_odd_form {m : ℕ} {c : Cell} (hc : c ∈ board (2 * m + 1))
    (hx : c.1 % 2 = 1) (hy : c.2 % 2 = 1) :
    ∃ i j : ℕ, i < m ∧ j < m ∧ c = ((2 * (i : ℤ) + 1 : ℤ), (2 * (j : ℤ) + 1 : ℤ)) := by
  rw [mem_board] at hc
  exact ⟨((c.1 - 1) / 2).toNat, ((c.2 - 1) / 2).toNat, by omega, by omega,
    by ext <;> omega⟩

theorem isAdj_xplus (c : Cell) : IsAdj c (c.1 + 1, c.2) := by
  have h : c.1 - (c.1 + 1) = -1 := by omega
  exact Or.inr ⟨by rw [h]; simp, rfl⟩

theorem isAdj_xminus (c : Cell) : IsAdj c (c.1 - 1, c.2) := by
  have h : c.1 - (c.1 - 1) = 1 := by omega
  exact Or.inr ⟨by rw [h]; simp, rfl⟩

theorem isAdj_yplus (c : Cell) : IsAdj c (c.1, c.2 + 1) := by
  have h : c.2 - (c.2 + 1) = -1 := by omega
  exact Or.inl ⟨rfl, by rw [h]; simp⟩

theorem isAdj_yminus (c : Cell) : IsAdj c (c.1, c.2 - 1) := by
  have h : c.2 - (c.2 - 1) = 1 := by omega
  exact Or.inl ⟨rfl, by rw [h]; simp⟩
set_option maxHeartbeats 1000000 in
/-- The family construction is a valid configuration. -/
theorem famF_valid (m t : ℕ) (h1 : 1 ≤ t) (h2 : t ≤ m ^ 2) :
    ∃ C : Config (2 * m + 1), C.f = famF m t := by
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h
      simp at h2
      omega
    · exact h
  have hq : t / m ≤ m := by
    apply Nat.div_le_of_le_mul
    calc t ≤ m ^ 2 := h2
    _ = m * m := by ring
  have hqm : t / m < m ∨ t / m = m := by omega
  refine ⟨⟨famF m t, ?_, ?_, ?_, ?_, ?_⟩, rfl⟩
  · -- hf_off
    intro c hc
    exact famF_off hc
  · -- hf_map
    intro c hc
    by_cases hy : c.2 % 2 = 1
    · by_cases hx : c.1 % 2 = 1
      · -- special cells
        obtain ⟨i, j, hi, hj, rfl⟩ := fam_odd_form hc hx hy
        have hJ : ((((2 * (i : ℤ) + 1 : ℤ), (2 * (j : ℤ) + 1 : ℤ)).2 - 1) / 2).toNat = j := by
          have h5 : ((2 * (j : ℤ) + 1 : ℤ) - 1) / 2 = (j : ℤ) := by omega
          simp only [h5, Int.toNat_natCast]
        have hPm := famPos_mod m i j hi hj
        by_cases h0 : famPos m ((2 * (i : ℤ) + 1 : ℤ), (2 * (j : ℤ) + 1 : ℤ)) = 0
        · rw [famF_fixed_of_pos_zero hc hy hx h0]
          exact hc
        · by_cases hlt : famPos m ((2 * (i : ℤ) + 1 : ℤ), (2 * (j : ℤ) + 1 : ℤ)) < t
          · by_cases hrs : famPos m ((2 * (i : ℤ) + 1 : ℤ), (2 * (j : ℤ) + 1 : ℤ)) % m = 0
            · rw [famF_chain_turn hc hy hx h0 hlt hrs, mem_board]
              exact ⟨by omega, by omega, by omega, by omega⟩
            · by_cases hjp : j % 2 = 0
              · have hj' : ((((2 * (i : ℤ) + 1 : ℤ), (2 * (j : ℤ) + 1 : ℤ)).2 - 1) / 2).toNat % 2 = 0 := by
                  rw [hJ]; exact hjp
                rw [famF_chain_even hc hy hx h0 hlt hrs hj', mem_board]
                exact ⟨by omega, by omega, by omega, by omega⟩
              · have hj' : ¬((((2 * (i : ℤ) + 1 : ℤ), (2 * (j : ℤ) + 1 : ℤ)).2 - 1) / 2).toNat % 2 = 0 := by
                  rw [hJ]; exact hjp
                rw [famF_chain_odd hc hy hx h0 hlt hrs hj', mem_board]
                exact ⟨by omega, by omega, by omega, by omega⟩
          · by_cases hre : famPos m ((2 * (i : ℤ) + 1 : ℤ), (2 * (j : ℤ) + 1 : ℤ)) % m = m - 1
            · rw [famF_nonchain_turn hc hy hx h0 hlt hre, mem_board]
              exact ⟨by omega, by omega, by omega, by omega⟩
            · by_cases hjp : j % 2 = 0
              · have hj' : ((((2 * (i : ℤ) + 1 : ℤ), (2 * (j : ℤ) + 1 : ℤ)).2 - 1) / 2).toNat % 2 = 0 := by
                  rw [hJ]; exact hjp
                rw [famF_nonchain_even hc hy hx h0 hlt hre hj', mem_board]
                exact ⟨by omega, by omega, by omega, by omega⟩
              · have hj' : ¬((((2 * (i : ℤ) + 1 : ℤ), (2 * (j : ℤ) + 1 : ℤ)).2 - 1) / 2).toNat % 2 = 0 := by
                  rw [hJ]; exact hjp
                rw [famF_nonchain_odd hc hy hx h0 hlt hre hj', mem_board]
                exact ⟨by omega, by omega, by omega, by omega⟩
      · -- mixed cells in odd rows
        have h0 : (0 : ℤ) ≤ c.1 := (mem_board.mp hc).1
        have h1' : c.1 ≤ 2 * (m : ℤ) := by
          have := (mem_board.mp hc).2.1
          omega
        have h2' : (0 : ℤ) ≤ c.2 := (mem_board.mp hc).2.2.1
        have h3' : c.2 ≤ 2 * (m : ℤ) := by
          have := (mem_board.mp hc).2.2.2
          omega
        obtain ⟨j, hjm, hcy⟩ : ∃ j : ℕ, j ≤ m - 1 ∧ c.2 = 2 * (j : ℤ) + 1 :=
          ⟨((c.2 - 1) / 2).toNat, by omega, by omega⟩
        have hJ : ((c.2 - 1) / 2).toNat = j := by omega
        by_cases hx0 : c.1 = 0
        · by_cases hjb : j < famB0 m t
          · have hj' : ((c.2 - 1) / 2).toNat < famB0 m t := by rwa [hJ]
            rw [famF_col0_of_lt hc hy hx hx0 hj', mem_board]
            exact ⟨by omega, by omega, by omega, by omega⟩
          · have hj' : ¬((c.2 - 1) / 2).toNat < famB0 m t := by rwa [hJ]
            rw [famF_col0_of_ge hc hy hx hx0 hj', mem_board]
            exact ⟨by omega, by omega, by omega, by omega⟩
        · by_cases hxm : c.1 = 2 * (m : ℤ)
          · by_cases hjb : j < famB1 m t
            · have hj' : ((c.2 - 1) / 2).toNat < famB1 m t := by rwa [hJ]
              rw [famF_colm_of_lt hc hy hx hx0 hxm hj', mem_board]
              exact ⟨by omega, by omega, by omega, by omega⟩
            · have hj' : ¬((c.2 - 1) / 2).toNat < famB1 m t := by rwa [hJ]
              rw [famF_colm_of_ge hc hy hx hx0 hxm hj', mem_board]
              exact ⟨by omega, by omega, by omega, by omega⟩
          · by_cases hg : t % m ≠ 0 ∧ ((c.2 - 1) / 2).toNat = t / m ∧ c.1 = famGx m t
            · rw [famF_gap_mid hc hy hx hx0 hxm hg, mem_board]
              have hgx := famGx_mem hm hg.1
              exact ⟨by omega, by omega, by omega, by omega⟩
            · by_cases hjp : ((c.2 - 1) / 2).toNat % 2 = 0
              · by_cases hp : famPos m (c.1 - 1, c.2) < t
                · rw [famF_mid_even_of_lt hc hy hx hx0 hxm hg hjp hp, mem_board]
                  exact ⟨by omega, by omega, by omega, by omega⟩
                · rw [famF_mid_even_of_ge hc hy hx hx0 hxm hg hjp hp, mem_board]
                  exact ⟨by omega, by omega, by omega, by omega⟩
              · by_cases hp : famPos m (c.1 + 1, c.2) < t
                · rw [famF_mid_odd_of_lt hc hy hx hx0 hxm hg hjp hp, mem_board]
                  exact ⟨by omega, by omega, by omega, by omega⟩
                · rw [famF_mid_odd_of_ge hc hy hx hx0 hxm hg hjp hp, mem_board]
                  exact ⟨by omega, by omega, by omega, by omega⟩
    · -- even rows
      have hy0 : c.2 % 2 = 0 := by omega
      have h0 : (0 : ℤ) ≤ c.1 := (mem_board.mp hc).1
      have h1' : c.1 ≤ 2 * (m : ℤ) := by
        have := (mem_board.mp hc).2.1
        omega
      have h2' : (0 : ℤ) ≤ c.2 := (mem_board.mp hc).2.2.1
      have h3' : c.2 ≤ 2 * (m : ℤ) := by
        have := (mem_board.mp hc).2.2.2
        omega
      obtain ⟨b, hbm, hcy⟩ : ∃ b : ℕ, b ≤ m ∧ c.2 = 2 * (b : ℤ) :=
        ⟨(c.2 / 2).toNat, by omega, by omega⟩
      have hB : (c.2 / 2).toNat = b := by omega
      by_cases hx : c.1 % 2 = 0
      · by_cases hx0 : c.1 = 0
        · by_cases hb0 : b = famB0 m t
          · have hb' : (c.2 / 2).toNat = famB0 m t := by rwa [hB]
            rw [famF_e0_eq hc hy hx hx0 hb', mem_board]
            exact ⟨by omega, by omega, by omega, by omega⟩
          · by_cases hb1 : b < famB0 m t
            · have hb1' : (c.2 / 2).toNat ≠ famB0 m t := by rwa [hB]
              have hb2' : (c.2 / 2).toNat < famB0 m t := by rwa [hB]
              rw [famF_e0_lt hc hy hx hx0 hb1' hb2', mem_board]
              have hle := famB0_le (m := m) (t := t)
              exact ⟨by omega, by omega, by omega, by omega⟩
            · have hb1' : (c.2 / 2).toNat ≠ famB0 m t := by rwa [hB]
              have hb2' : ¬(c.2 / 2).toNat < famB0 m t := by rwa [hB]
              rw [famF_e0_gt hc hy hx hx0 hb1' hb2', mem_board]
              exact ⟨by omega, by omega, by omega, by omega⟩
        · by_cases hxm : c.1 = 2 * (m : ℤ)
          · by_cases hb0 : b = famB1 m t
            · have hb' : (c.2 / 2).toNat = famB1 m t := by rwa [hB]
              rw [famF_em_eq hc hy hx hx0 hxm hb', mem_board]
              exact ⟨by omega, by omega, by omega, by omega⟩
            · by_cases hb1 : b < famB1 m t
              · have hb1' : (c.2 / 2).toNat ≠ famB1 m t := by rwa [hB]
                have hb2' : (c.2 / 2).toNat < famB1 m t := by rwa [hB]
                rw [famF_em_lt hc hy hx hx0 hxm hb1' hb2', mem_board]
                have hle := famB1_le (m := m) (t := t)
                exact ⟨by omega, by omega, by omega, by omega⟩
              · have hb1' : (c.2 / 2).toNat ≠ famB1 m t := by rwa [hB]
                have hb2' : ¬(c.2 / 2).toNat < famB1 m t := by rwa [hB]
                rw [famF_em_gt hc hy hx hx0 hxm hb1' hb2', mem_board]
                exact ⟨by omega, by omega, by omega, by omega⟩
          · by_cases hg : t % m ≠ 0 ∧ (c.2 / 2).toNat = t / m ∧ c.1 = famGx m t
            · rw [famF_gap_e hc hy hx hx0 hxm hg, mem_board]
              have hgx := famGx_mem hm hg.1
              have hg2 : t / m < m := by
                rw [Nat.div_lt_iff_lt_mul hm]
                have h6 : m ^ 2 = m * m := by ring
                rw [h6] at h2
                rcases eq_or_lt_of_le h2 with h | h
                · exfalso
                  exact hg.1 (by rw [h]; simp)
                · exact h
              rw [hB] at hg
              exact ⟨by omega, by omega, by omega, by omega⟩
            · by_cases he : c.1 < famEsc m t b
              · have he' : c.1 < famEsc m t (c.2 / 2).toNat := by rwa [hB]
                rw [famF_eint_of_lt hc hy hx hx0 hxm hg he', mem_board]
                exact ⟨by omega, by omega, by omega, by omega⟩
              · have he' : ¬c.1 < famEsc m t (c.2 / 2).toNat := by rwa [hB]
                rw [famF_eint_of_ge hc hy hx hx0 hxm hg he', mem_board]
                exact ⟨by omega, by omega, by omega, by omega⟩
      · by_cases hh : 1 ≤ (c.2 / 2).toNat ∧ (c.2 / 2).toNat * m ≠ t ∧
            c.1 = famHoleX m (c.2 / 2).toNat
        · by_cases hbm' : (c.2 / 2).toNat * m < t
          · rw [famF_hole_of_lt hc hy hx hh hbm', mem_board]
            rw [hB] at hbm'
            have hbm2 : b < m := by
              by_contra hb3
              push Not at hb3
              have h4 : m * m ≤ b * m := Nat.mul_le_mul_right m hb3
              have h6 : m ^ 2 = m * m := by ring
              omega
            exact ⟨by omega, by omega, by omega, by omega⟩
          · rw [famF_hole_of_ge hc hy hx hh hbm', mem_board]
            rw [hB] at hh
            exact ⟨by omega, by omega, by omega, by omega⟩
        · by_cases he : c.1 < famEsc m t b
          · have he' : c.1 < famEsc m t (c.2 / 2).toNat := by rwa [hB]
            rw [famF_oint_of_lt hc hy hx hh he', mem_board]
            exact ⟨by omega, by omega, by omega, by omega⟩
          · have he' : ¬c.1 < famEsc m t (c.2 / 2).toNat := by rwa [hB]
            rw [famF_oint_of_ge hc hy hx hh he', mem_board]
            exact ⟨by omega, by omega, by omega, by omega⟩
  · -- hf_inv
    intro c hc
    by_cases hy : c.2 % 2 = 1
    · by_cases hx : c.1 % 2 = 1
      · obtain ⟨i, j, hi, hj, hcij⟩ := fam_odd_form hc hx hy
        have hx1 : c.1 = 2 * (i : ℤ) + 1 := by rw [hcij]
        have hx2 : c.2 = 2 * (j : ℤ) + 1 := by rw [hcij]
        have hJ : ((c.2 - 1) / 2).toNat = j := by rw [hx2]; omega
        have hP : famPos m c = j * m + if j % 2 = 0 then m - 1 - i else i := by
          rw [hcij]; exact famPos_eq m i j
        have hPm : famPos m c % m = if j % 2 = 0 then m - 1 - i else i := by
          rw [hcij]; exact famPos_mod m i j hi hj
        by_cases h0 : famPos m c = 0
        · rw [famF_fixed_of_pos_zero hc hy hx h0, famF_fixed_of_pos_zero hc hy hx h0]
        · by_cases hlt : famPos m c < t
          · by_cases hrs : famPos m c % m = 0
            · -- chain turn
              rw [famF_chain_turn hc hy hx h0 hlt hrs]
              have hP0' : famPos m c = j * m := by
                rw [hP]
                rw [hPm] at hrs
                split_ifs at hrs ⊢ <;> omega
              have hlt' : j * m < t := by rw [← hP0']; exact hlt
              have hj1 : 1 ≤ j := by
                rcases Nat.eq_zero_or_pos j with h | h
                · subst h
                  rw [hP0'] at h0
                  simp at h0
                · exact h
              have hv : (c.1, c.2 - 1) ∈ board (2 * m + 1) := by
                rw [mem_board]
                exact ⟨by omega, by omega, by omega, by omega⟩
              have hyv : ¬(c.1, c.2 - 1).2 % 2 = 1 := by
                show ¬(c.2 - 1) % 2 = 1
                omega
              have hxv : ¬(c.1, c.2 - 1).1 % 2 = 0 := by
                show ¬c.1 % 2 = 0
                omega
              have hBv : ((c.1, c.2 - 1).2 / 2).toNat = j := by
                show ((c.2 - 1) / 2).toNat = j
                omega
              by_cases hjp : j % 2 = 0
              · rw [hPm, if_pos hjp] at hrs
                have hi' : i = m - 1 := by omega
                have hhv : 1 ≤ ((c.1, c.2 - 1).2 / 2).toNat ∧
                    ((c.1, c.2 - 1).2 / 2).toNat * m ≠ t ∧
                    (c.1, c.2 - 1).1 = famHoleX m ((c.1, c.2 - 1).2 / 2).toNat := by
                  rw [hBv]
                  refine ⟨hj1, by omega, ?_⟩
                  show c.1 = famHoleX m j
                  rw [famHoleX_eq_of_even (by omega : ¬j % 2 = 1)]
                  omega
                have hbv : ((c.1, c.2 - 1).2 / 2).toNat * m < t := by
                  rw [hBv]
                  exact hlt'
                rw [famF_hole_of_lt hv hyv hxv hhv hbv]
                apply Prod.ext <;> omega
              · rw [hPm, if_neg hjp] at hrs
                have hi' : i = 0 := by omega
                have hhv : 1 ≤ ((c.1, c.2 - 1).2 / 2).toNat ∧
                    ((c.1, c.2 - 1).2 / 2).toNat * m ≠ t ∧
                    (c.1, c.2 - 1).1 = famHoleX m ((c.1, c.2 - 1).2 / 2).toNat := by
                  rw [hBv]
                  refine ⟨hj1, by omega, ?_⟩
                  show c.1 = famHoleX m j
                  rw [famHoleX_eq_of_odd (by omega : j % 2 = 1)]
                  omega
                have hbv : ((c.1, c.2 - 1).2 / 2).toNat * m < t := by
                  rw [hBv]
                  exact hlt'
                rw [famF_hole_of_lt hv hyv hxv hhv hbv]
                apply Prod.ext <;> omega
            · by_cases hjp : j % 2 = 0
              · -- chain, in-row, j even
                have hj' : ((c.2 - 1) / 2).toNat % 2 = 0 := by rw [hJ]; exact hjp
                rw [famF_chain_even hc hy hx h0 hlt hrs hj']
                rw [hPm, if_pos hjp] at hrs
                have hlt' : j * m + (m - 1 - i) < t := by
                  have h9 := hlt
                  rw [hP, if_pos hjp] at h9
                  exact h9
                have hv : (c.1 + 1, c.2) ∈ board (2 * m + 1) := by
                  rw [mem_board]
                  exact ⟨by omega, by omega, by omega, by omega⟩
                have hyv : (c.1 + 1, c.2).2 % 2 = 1 := by
                  show c.2 % 2 = 1
                  omega
                have hxv : ¬(c.1 + 1, c.2).1 % 2 = 1 := by
                  show ¬(c.1 + 1) % 2 = 1
                  omega
                have h0v : (c.1 + 1, c.2).1 ≠ 0 := by
                  show c.1 + 1 ≠ 0
                  omega
                have hmv : (c.1 + 1, c.2).1 ≠ 2 * (m : ℤ) := by
                  show c.1 + 1 ≠ 2 * (m : ℤ)
                  omega
                have hJv : (((c.1 + 1, c.2).2 - 1) / 2).toNat = j := by
                  show ((c.2 - 1) / 2).toNat = j
                  exact hJ
                have hgv : ¬(t % m ≠ 0 ∧ (((c.1 + 1, c.2).2 - 1) / 2).toNat = t / m ∧
                    (c.1 + 1, c.2).1 = famGx m t) := by
                  intro ⟨g1, g2, g3⟩
                  rw [hJv] at g2
                  have htm : (t / m) % 2 = 0 := by rw [← g2]; exact hjp
                  have g3' : c.1 + 1 = famGx m t := g3
                  rw [famGx_eq_of_even htm] at g3'
                  have hdm := Nat.div_add_mod' t m
                  rw [← g2] at hdm
                  have hrm : 1 ≤ t % m ∧ t % m ≤ m - 1 := by
                    have := Nat.mod_lt t hm
                    omega
                  omega
                have hjpv : (((c.1 + 1, c.2).2 - 1) / 2).toNat % 2 = 0 := by
                  rw [hJv]; exact hjp
                have hpv : famPos m ((c.1 + 1, c.2).1 - 1, (c.1 + 1, c.2).2) < t := by
                  have hve : ((c.1 + 1, c.2).1 - 1, (c.1 + 1, c.2).2) = c := by
                    apply Prod.ext <;> omega
                  rw [hve]
                  exact hlt
                rw [famF_mid_even_of_lt hv hyv hxv h0v hmv hgv hjpv hpv]
                apply Prod.ext <;> omega
              · -- chain, in-row, j odd
                have hj' : ¬((c.2 - 1) / 2).toNat % 2 = 0 := by rw [hJ]; exact hjp
                rw [famF_chain_odd hc hy hx h0 hlt hrs hj']
                rw [hPm, if_neg hjp] at hrs
                have hlt' : j * m + i < t := by
                  have h9 := hlt
                  rw [hP, if_neg hjp] at h9
                  exact h9
                have hv : (c.1 - 1, c.2) ∈ board (2 * m + 1) := by
                  rw [mem_board]
                  exact ⟨by omega, by omega, by omega, by omega⟩
                have hyv : (c.1 - 1, c.2).2 % 2 = 1 := by
                  show c.2 % 2 = 1
                  omega
                have hxv : ¬(c.1 - 1, c.2).1 % 2 = 1 := by
                  show ¬(c.1 - 1) % 2 = 1
                  omega
                have h0v : (c.1 - 1, c.2).1 ≠ 0 := by
                  show c.1 - 1 ≠ 0
                  omega
                have hmv : (c.1 - 1, c.2).1 ≠ 2 * (m : ℤ) := by
                  show c.1 - 1 ≠ 2 * (m : ℤ)
                  omega
                have hJv : (((c.1 - 1, c.2).2 - 1) / 2).toNat = j := by
                  show ((c.2 - 1) / 2).toNat = j
                  exact hJ
                have hgv : ¬(t % m ≠ 0 ∧ (((c.1 - 1, c.2).2 - 1) / 2).toNat = t / m ∧
                    (c.1 - 1, c.2).1 = famGx m t) := by
                  intro ⟨g1, g2, g3⟩
                  rw [hJv] at g2
                  have htm : ¬(t / m) % 2 = 0 := by rw [← g2]; exact hjp
                  have g3' : c.1 - 1 = famGx m t := g3
                  rw [famGx_eq_of_odd htm] at g3'
                  have hdm := Nat.div_add_mod' t m
                  rw [← g2] at hdm
                  have hrm : 1 ≤ t % m ∧ t % m ≤ m - 1 := by
                    have := Nat.mod_lt t hm
                    omega
                  omega
                have hjpv : ¬(((c.1 - 1, c.2).2 - 1) / 2).toNat % 2 = 0 := by
                  rw [hJv]; exact hjp
                have hpv : famPos m ((c.1 - 1, c.2).1 + 1, (c.1 - 1, c.2).2) < t := by
                  have hve : ((c.1 - 1, c.2).1 + 1, (c.1 - 1, c.2).2) = c := by
                    apply Prod.ext <;> omega
                  rw [hve]
                  exact hlt
                rw [famF_mid_odd_of_lt hv hyv hxv h0v hmv hgv hjpv hpv]
                apply Prod.ext <;> omega
          · by_cases hre : famPos m c % m = m - 1
            · -- nonchain turn
              rw [famF_nonchain_turn hc hy hx h0 hlt hre]
              have hP0' : famPos m c = j * m + (m - 1) := by
                rw [hP]
                rw [hPm] at hre
                split_ifs at hre ⊢ <;> omega
              have hge' : j * m + (m - 1) ≥ t := by rw [← hP0']; exact Nat.le_of_not_lt hlt
              have hjm1 : (j + 1) * m = j * m + m := by ring
              have hv : (c.1, c.2 + 1) ∈ board (2 * m + 1) := by
                rw [mem_board]
                exact ⟨by omega, by omega, by omega, by omega⟩
              have hyv : ¬(c.1, c.2 + 1).2 % 2 = 1 := by
                show ¬(c.2 + 1) % 2 = 1
                omega
              have hxv : ¬(c.1, c.2 + 1).1 % 2 = 0 := by
                show ¬c.1 % 2 = 0
                omega
              have hBv : ((c.1, c.2 + 1).2 / 2).toNat = j + 1 := by
                show ((c.2 + 1) / 2).toNat = j + 1
                omega
              have hbv : ¬((c.1, c.2 + 1).2 / 2).toNat * m < t := by
                rw [hBv]
                omega
              by_cases hjp : j % 2 = 0
              · rw [hPm, if_pos hjp] at hre
                have hi' : i = 0 := by omega
                have hhv : 1 ≤ ((c.1, c.2 + 1).2 / 2).toNat ∧
                    ((c.1, c.2 + 1).2 / 2).toNat * m ≠ t ∧
                    (c.1, c.2 + 1).1 = famHoleX m ((c.1, c.2 + 1).2 / 2).toNat := by
                  rw [hBv]
                  refine ⟨by omega, by omega, ?_⟩
                  show c.1 = famHoleX m (j + 1)
                  rw [famHoleX_eq_of_odd (by omega : (j + 1) % 2 = 1)]
                  omega
                rw [famF_hole_of_ge hv hyv hxv hhv hbv]
                apply Prod.ext <;> omega
              · rw [hPm, if_neg hjp] at hre
                have hi' : i = m - 1 := by omega
                have hhv : 1 ≤ ((c.1, c.2 + 1).2 / 2).toNat ∧
                    ((c.1, c.2 + 1).2 / 2).toNat * m ≠ t ∧
                    (c.1, c.2 + 1).1 = famHoleX m ((c.1, c.2 + 1).2 / 2).toNat := by
                  rw [hBv]
                  refine ⟨by omega, by omega, ?_⟩
                  show c.1 = famHoleX m (j + 1)
                  rw [famHoleX_eq_of_even (by omega : ¬(j + 1) % 2 = 1)]
                  omega
                rw [famF_hole_of_ge hv hyv hxv hhv hbv]
                apply Prod.ext <;> omega
            · by_cases hjp : j % 2 = 0
              · -- nonchain, in-row, j even
                have hj' : ((c.2 - 1) / 2).toNat % 2 = 0 := by rw [hJ]; exact hjp
                rw [famF_nonchain_even hc hy hx h0 hlt hre hj']
                rw [hPm, if_pos hjp] at hre
                have hge' : j * m + (m - 1 - i) ≥ t := by
                  have h9 := hlt
                  rw [hP, if_pos hjp] at h9
                  omega
                have hv : (c.1 - 1, c.2) ∈ board (2 * m + 1) := by
                  rw [mem_board]
                  exact ⟨by omega, by omega, by omega, by omega⟩
                have hyv : (c.1 - 1, c.2).2 % 2 = 1 := by
                  show c.2 % 2 = 1
                  omega
                have hxv : ¬(c.1 - 1, c.2).1 % 2 = 1 := by
                  show ¬(c.1 - 1) % 2 = 1
                  omega
                have h0v : (c.1 - 1, c.2).1 ≠ 0 := by
                  show c.1 - 1 ≠ 0
                  omega
                have hmv : (c.1 - 1, c.2).1 ≠ 2 * (m : ℤ) := by
                  show c.1 - 1 ≠ 2 * (m : ℤ)
                  omega
                have hJv : (((c.1 - 1, c.2).2 - 1) / 2).toNat = j := by
                  show ((c.2 - 1) / 2).toNat = j
                  exact hJ
                have hgv : ¬(t % m ≠ 0 ∧ (((c.1 - 1, c.2).2 - 1) / 2).toNat = t / m ∧
                    (c.1 - 1, c.2).1 = famGx m t) := by
                  intro ⟨g1, g2, g3⟩
                  rw [hJv] at g2
                  have htm : (t / m) % 2 = 0 := by rw [← g2]; exact hjp
                  have g3' : c.1 - 1 = famGx m t := g3
                  rw [famGx_eq_of_even htm] at g3'
                  have hdm := Nat.div_add_mod' t m
                  rw [← g2] at hdm
                  have hrm : 1 ≤ t % m ∧ t % m ≤ m - 1 := by
                    have := Nat.mod_lt t hm
                    omega
                  omega
                have hjpv : (((c.1 - 1, c.2).2 - 1) / 2).toNat % 2 = 0 := by
                  rw [hJv]; exact hjp
                have hpv : ¬famPos m ((c.1 - 1, c.2).1 - 1, (c.1 - 1, c.2).2) < t := by
                  have hve : ((c.1 - 1, c.2).1 - 1, (c.1 - 1, c.2).2) =
                      ((2 * ((i - 1 : ℕ) : ℤ) + 1 : ℤ), (2 * (j : ℤ) + 1 : ℤ)) := by
                    apply Prod.ext <;> omega
                  rw [hve, famPos_eq, if_pos hjp]
                  omega
                rw [famF_mid_even_of_ge hv hyv hxv h0v hmv hgv hjpv hpv]
                apply Prod.ext <;> omega
              · -- nonchain, in-row, j odd
                have hj' : ¬((c.2 - 1) / 2).toNat % 2 = 0 := by rw [hJ]; exact hjp
                rw [famF_nonchain_odd hc hy hx h0 hlt hre hj']
                rw [hPm, if_neg hjp] at hre
                have hge' : j * m + i ≥ t := by
                  have h9 := hlt
                  rw [hP, if_neg hjp] at h9
                  omega
                have hv : (c.1 + 1, c.2) ∈ board (2 * m + 1) := by
                  rw [mem_board]
                  exact ⟨by omega, by omega, by omega, by omega⟩
                have hyv : (c.1 + 1, c.2).2 % 2 = 1 := by
                  show c.2 % 2 = 1
                  omega
                have hxv : ¬(c.1 + 1, c.2).1 % 2 = 1 := by
                  show ¬(c.1 + 1) % 2 = 1
                  omega
                have h0v : (c.1 + 1, c.2).1 ≠ 0 := by
                  show c.1 + 1 ≠ 0
                  omega
                have hmv : (c.1 + 1, c.2).1 ≠ 2 * (m : ℤ) := by
                  show c.1 + 1 ≠ 2 * (m : ℤ)
                  omega
                have hJv : (((c.1 + 1, c.2).2 - 1) / 2).toNat = j := by
                  show ((c.2 - 1) / 2).toNat = j
                  exact hJ
                have hgv : ¬(t % m ≠ 0 ∧ (((c.1 + 1, c.2).2 - 1) / 2).toNat = t / m ∧
                    (c.1 + 1, c.2).1 = famGx m t) := by
                  intro ⟨g1, g2, g3⟩
                  rw [hJv] at g2
                  have htm : ¬(t / m) % 2 = 0 := by rw [← g2]; exact hjp
                  have g3' : c.1 + 1 = famGx m t := g3
                  rw [famGx_eq_of_odd htm] at g3'
                  have hdm := Nat.div_add_mod' t m
                  rw [← g2] at hdm
                  have hrm : 1 ≤ t % m ∧ t % m ≤ m - 1 := by
                    have := Nat.mod_lt t hm
                    omega
                  omega
                have hjpv : ¬(((c.1 + 1, c.2).2 - 1) / 2).toNat % 2 = 0 := by
                  rw [hJv]; exact hjp
                have hpv : ¬famPos m ((c.1 + 1, c.2).1 + 1, (c.1 + 1, c.2).2) < t := by
                  have hve : ((c.1 + 1, c.2).1 + 1, (c.1 + 1, c.2).2) =
                      ((2 * ((i + 1 : ℕ) : ℤ) + 1 : ℤ), (2 * (j : ℤ) + 1 : ℤ)) := by
                    apply Prod.ext <;> omega
                  rw [hve, famPos_eq, if_neg hjp]
                  omega
                rw [famF_mid_odd_of_ge hv hyv hxv h0v hmv hgv hjpv hpv]
                apply Prod.ext <;> omega
      · -- mixed cells in odd rows
        have hb1 : (0 : ℤ) ≤ c.1 := (mem_board.mp hc).1
        have hb2 : c.1 ≤ 2 * (m : ℤ) := by
          have h := (mem_board.mp hc).2.1
          omega
        have hb3 : (0 : ℤ) ≤ c.2 := (mem_board.mp hc).2.2.1
        have hb4 : c.2 ≤ 2 * (m : ℤ) := by
          have h := (mem_board.mp hc).2.2.2
          omega
        obtain ⟨j, hjm, hcy⟩ : ∃ j : ℕ, j ≤ m - 1 ∧ c.2 = 2 * (j : ℤ) + 1 :=
          ⟨((c.2 - 1) / 2).toNat, by omega, by omega⟩
        have hJ : ((c.2 - 1) / 2).toNat = j := by omega
        by_cases hx0 : c.1 = 0
        · by_cases hjb : j < famB0 m t
          · have hj' : ((c.2 - 1) / 2).toNat < famB0 m t := by rwa [hJ]
            rw [famF_col0_of_lt hc hy hx hx0 hj']
            have hv : ((0 : ℤ), c.2 - 1) ∈ board (2 * m + 1) := by
              rw [mem_board]
              exact ⟨by omega, by omega, by omega, by omega⟩
            have hyv : ¬((0 : ℤ), c.2 - 1).2 % 2 = 1 := by
              show ¬(c.2 - 1) % 2 = 1
              omega
            have hxv : ((0 : ℤ), c.2 - 1).1 % 2 = 0 := by
              show (0 : ℤ) % 2 = 0
              omega
            have h0v : ((0 : ℤ), c.2 - 1).1 = 0 := rfl
            have hBv : (((0 : ℤ), c.2 - 1).2 / 2).toNat = j := by
              show ((c.2 - 1) / 2).toNat = j
              omega
            have hb1v : (((0 : ℤ), c.2 - 1).2 / 2).toNat ≠ famB0 m t := by
              rw [hBv]
              omega
            have hb2v : (((0 : ℤ), c.2 - 1).2 / 2).toNat < famB0 m t := by
              rw [hBv]
              exact hjb
            rw [famF_e0_lt hv hyv hxv h0v hb1v hb2v]
            apply Prod.ext <;> omega
          · have hj' : ¬((c.2 - 1) / 2).toNat < famB0 m t := by rwa [hJ]
            rw [famF_col0_of_ge hc hy hx hx0 hj']
            have hv : ((0 : ℤ), c.2 + 1) ∈ board (2 * m + 1) := by
              rw [mem_board]
              exact ⟨by omega, by omega, by omega, by omega⟩
            have hyv : ¬((0 : ℤ), c.2 + 1).2 % 2 = 1 := by
              show ¬(c.2 + 1) % 2 = 1
              omega
            have hxv : ((0 : ℤ), c.2 + 1).1 % 2 = 0 := by
              show (0 : ℤ) % 2 = 0
              omega
            have h0v : ((0 : ℤ), c.2 + 1).1 = 0 := rfl
            have hBv : (((0 : ℤ), c.2 + 1).2 / 2).toNat = j + 1 := by
              show ((c.2 + 1) / 2).toNat = j + 1
              omega
            have hb1v : (((0 : ℤ), c.2 + 1).2 / 2).toNat ≠ famB0 m t := by
              rw [hBv]
              omega
            have hb2v : ¬(((0 : ℤ), c.2 + 1).2 / 2).toNat < famB0 m t := by
              rw [hBv]
              omega
            rw [famF_e0_gt hv hyv hxv h0v hb1v hb2v]
            apply Prod.ext <;> omega
        · by_cases hxm : c.1 = 2 * (m : ℤ)
          · by_cases hjb : j < famB1 m t
            · have hj' : ((c.2 - 1) / 2).toNat < famB1 m t := by rwa [hJ]
              rw [famF_colm_of_lt hc hy hx hx0 hxm hj']
              have hv : (2 * (m : ℤ), c.2 - 1) ∈ board (2 * m + 1) := by
                rw [mem_board]
                exact ⟨by omega, by omega, by omega, by omega⟩
              have hyv : ¬(2 * (m : ℤ), c.2 - 1).2 % 2 = 1 := by
                show ¬(c.2 - 1) % 2 = 1
                omega
              have hxv : (2 * (m : ℤ), c.2 - 1).1 % 2 = 0 := by
                show (2 * (m : ℤ)) % 2 = 0
                omega
              have h0v : (2 * (m : ℤ), c.2 - 1).1 ≠ 0 := by
                show 2 * (m : ℤ) ≠ 0
                omega
              have hBv : ((2 * (m : ℤ), c.2 - 1).2 / 2).toNat = j := by
                show ((c.2 - 1) / 2).toNat = j
                omega
              have hb1v : ((2 * (m : ℤ), c.2 - 1).2 / 2).toNat ≠ famB1 m t := by
                rw [hBv]
                omega
              have hb2v : ((2 * (m : ℤ), c.2 - 1).2 / 2).toNat < famB1 m t := by
                rw [hBv]
                exact hjb
              rw [famF_em_lt hv hyv hxv h0v rfl hb1v hb2v]
              apply Prod.ext <;> omega
            · have hj' : ¬((c.2 - 1) / 2).toNat < famB1 m t := by rwa [hJ]
              rw [famF_colm_of_ge hc hy hx hx0 hxm hj']
              have hv : (2 * (m : ℤ), c.2 + 1) ∈ board (2 * m + 1) := by
                rw [mem_board]
                exact ⟨by omega, by omega, by omega, by omega⟩
              have hyv : ¬(2 * (m : ℤ), c.2 + 1).2 % 2 = 1 := by
                show ¬(c.2 + 1) % 2 = 1
                omega
              have hxv : (2 * (m : ℤ), c.2 + 1).1 % 2 = 0 := by
                show (2 * (m : ℤ)) % 2 = 0
                omega
              have h0v : (2 * (m : ℤ), c.2 + 1).1 ≠ 0 := by
                show 2 * (m : ℤ) ≠ 0
                omega
              have hBv : ((2 * (m : ℤ), c.2 + 1).2 / 2).toNat = j + 1 := by
                show ((c.2 + 1) / 2).toNat = j + 1
                omega
              have hb1v : ((2 * (m : ℤ), c.2 + 1).2 / 2).toNat ≠ famB1 m t := by
                rw [hBv]
                omega
              have hb2v : ¬((2 * (m : ℤ), c.2 + 1).2 / 2).toNat < famB1 m t := by
                rw [hBv]
                omega
              rw [famF_em_gt hv hyv hxv h0v rfl hb1v hb2v]
              apply Prod.ext <;> omega
          · by_cases hg : t % m ≠ 0 ∧ ((c.2 - 1) / 2).toNat = t / m ∧ c.1 = famGx m t
            · rw [famF_gap_mid hc hy hx hx0 hxm hg]
              have hgx := famGx_mem hm hg.1
              rw [hJ] at hg
              have hv : (c.1, c.2 - 1) ∈ board (2 * m + 1) := by
                rw [mem_board]
                exact ⟨by omega, by omega, by omega, by omega⟩
              have hyv : ¬(c.1, c.2 - 1).2 % 2 = 1 := by
                show ¬(c.2 - 1) % 2 = 1
                omega
              have hxv : (c.1, c.2 - 1).1 % 2 = 0 := by
                show c.1 % 2 = 0
                rw [hg.2.2]
                omega
              have h0v : (c.1, c.2 - 1).1 ≠ 0 := by
                show c.1 ≠ 0
                rw [hg.2.2]
                omega
              have hmv : (c.1, c.2 - 1).1 ≠ 2 * (m : ℤ) := by
                show c.1 ≠ 2 * (m : ℤ)
                rw [hg.2.2]
                omega
              have hBv : ((c.1, c.2 - 1).2 / 2).toNat = j := by
                show ((c.2 - 1) / 2).toNat = j
                omega
              have hgv : t % m ≠ 0 ∧ ((c.1, c.2 - 1).2 / 2).toNat = t / m ∧
                  (c.1, c.2 - 1).1 = famGx m t := by
                refine ⟨hg.1, by rw [hBv]; exact hg.2.1, ?_⟩
                show c.1 = famGx m t
                exact hg.2.2
              rw [famF_gap_e hv hyv hxv h0v hmv hgv]
              apply Prod.ext <;> omega
            · by_cases hjp : ((c.2 - 1) / 2).toNat % 2 = 0
              · have hjp' : j % 2 = 0 := by rwa [hJ] at hjp
                by_cases hp : famPos m (c.1 - 1, c.2) < t
                · -- mid, j even, used by right cell (chain)
                  rw [famF_mid_even_of_lt hc hy hx hx0 hxm hg hjp hp]
                  obtain ⟨a, ha1, ha2, hxa⟩ : ∃ a : ℕ, 1 ≤ a ∧ a ≤ m - 1 ∧ c.1 = 2 * (a : ℤ) :=
                    ⟨(c.1 / 2).toNat, by omega, by omega, by omega⟩
                  have hve : (c.1 - 1, c.2) =
                      ((2 * ((a - 1 : ℕ) : ℤ) + 1 : ℤ), (2 * (j : ℤ) + 1 : ℤ)) := by
                    apply Prod.ext <;> omega
                  have hPv : famPos m (c.1 - 1, c.2) = j * m + (m - 1 - (a - 1)) := by
                    rw [hve, famPos_eq, if_pos hjp']
                  have hPmv : famPos m (c.1 - 1, c.2) % m = m - 1 - (a - 1) := by
                    rw [hve, famPos_mod m (a - 1) j (by omega) (by omega), if_pos hjp']
                  have hv : (c.1 - 1, c.2) ∈ board (2 * m + 1) := by
                    rw [mem_board]
                    exact ⟨by omega, by omega, by omega, by omega⟩
                  have hyv : (c.1 - 1, c.2).2 % 2 = 1 := by
                    show c.2 % 2 = 1
                    omega
                  have hxv : (c.1 - 1, c.2).1 % 2 = 1 := by
                    show (c.1 - 1) % 2 = 1
                    omega
                  have h0v : famPos m (c.1 - 1, c.2) ≠ 0 := by
                    rw [hPv]
                    omega
                  have hrsv : famPos m (c.1 - 1, c.2) % m ≠ 0 := by
                    rw [hPmv]
                    omega
                  have hjv : (((c.1 - 1, c.2).2 - 1) / 2).toNat % 2 = 0 := by
                    show ((c.2 - 1) / 2).toNat % 2 = 0
                    exact hjp
                  rw [famF_chain_even hv hyv hxv h0v hp hrsv hjv]
                  apply Prod.ext <;> omega
                · -- mid, j even, used by left cell (nonchain)
                  rw [famF_mid_even_of_ge hc hy hx hx0 hxm hg hjp hp]
                  obtain ⟨a, ha1, ha2, hxa⟩ : ∃ a : ℕ, 1 ≤ a ∧ a ≤ m - 1 ∧ c.1 = 2 * (a : ℤ) :=
                    ⟨(c.1 / 2).toNat, by omega, by omega, by omega⟩
                  have hve : (c.1 + 1, c.2) =
                      ((2 * (a : ℤ) + 1 : ℤ), (2 * (j : ℤ) + 1 : ℤ)) := by
                    apply Prod.ext <;> omega
                  have hPv : famPos m (c.1 + 1, c.2) = j * m + (m - 1 - a) := by
                    rw [hve, famPos_eq, if_pos hjp']
                  have hPmv : famPos m (c.1 + 1, c.2) % m = m - 1 - a := by
                    rw [hve, famPos_mod m a j (by omega) (by omega), if_pos hjp']
                  have hve2 : (c.1 - 1, c.2) =
                      ((2 * ((a - 1 : ℕ) : ℤ) + 1 : ℤ), (2 * (j : ℤ) + 1 : ℤ)) := by
                    apply Prod.ext <;> omega
                  have hPv2 : famPos m (c.1 - 1, c.2) = j * m + (m - a) := by
                    rw [hve2, famPos_eq, if_pos hjp']
                    have h9 : m - 1 - (a - 1) = m - a := by omega
                    rw [h9]
                  have hgev : ¬famPos m (c.1 + 1, c.2) < t := by
                    rw [hPv]
                    intro hlt2
                    rw [hPv2] at hp
                    have ht : t = j * m + (m - a) := by omega
                    have h1g : t % m ≠ 0 := by
                      rw [ht, add_comm (j * m) (m - a), mul_comm j m, Nat.add_mul_mod_self_left,
                        Nat.mod_eq_of_lt (by omega : m - a < m)]
                      omega
                    have h2g : ((c.2 - 1) / 2).toNat = t / m := by
                      rw [hJ, ht, add_comm (j * m) (m - a), mul_comm j m,
                        Nat.add_mul_div_left _ _ (by omega : 0 < m),
                        Nat.div_eq_of_lt (by omega : m - a < m), zero_add]
                    have htmj : t / m = j := by rw [← h2g, hJ]
                    have h3g : c.1 = famGx m t := by
                      rw [famGx_eq_of_even (by rw [htmj]; exact hjp')]
                      have htm2 : t % m = m - a := by
                        rw [ht, add_comm (j * m) (m - a), mul_comm j m,
                          Nat.add_mul_mod_self_left,
                          Nat.mod_eq_of_lt (by omega : m - a < m)]
                      rw [htm2]
                      omega
                    exact hg ⟨h1g, h2g, h3g⟩
                  have hv : (c.1 + 1, c.2) ∈ board (2 * m + 1) := by
                    rw [mem_board]
                    exact ⟨by omega, by omega, by omega, by omega⟩
                  have hyv : (c.1 + 1, c.2).2 % 2 = 1 := by
                    show c.2 % 2 = 1
                    omega
                  have hxv : (c.1 + 1, c.2).1 % 2 = 1 := by
                    show (c.1 + 1) % 2 = 1
                    omega
                  have h0v : famPos m (c.1 + 1, c.2) ≠ 0 := by
                    rw [hPv]
                    intro hz
                    have h9 := Nat.add_eq_zero_iff.mp hz
                    rw [Nat.mul_eq_zero] at h9
                    have hj0 : j = 0 := by omega
                    have ha' : a = m - 1 := by omega
                    rw [hj0, ha'] at hPv2
                    rw [hPv2] at hp
                    have ht1 : t = 1 := by
                      have h10 : (0 : ℕ) * m + (m - (m - 1)) = 1 := by
                        have h11 : m - (m - 1) = 1 := by omega
                        rw [h11]
                        simp
                      rw [h10] at hp
                      omega
                    have hm2 : 2 ≤ m := by omega
                    have h1g : t % m ≠ 0 := by
                      rw [ht1, Nat.mod_eq_of_lt (by omega : 1 < m)]
                      omega
                    have h2g : ((c.2 - 1) / 2).toNat = t / m := by
                      rw [hJ, hj0, ht1, Nat.div_eq_of_lt (by omega : 1 < m)]
                    have htm0 : (t / m) % 2 = 0 := by
                      rw [ht1, Nat.div_eq_of_lt (by omega : 1 < m)]
                    have h3g : c.1 = famGx m t := by
                      rw [famGx_eq_of_even htm0, ht1, Nat.mod_eq_of_lt (by omega : 1 < m)]
                      try omega
                    exact hg ⟨h1g, h2g, h3g⟩
                  have hrev : famPos m (c.1 + 1, c.2) % m ≠ m - 1 := by
                    rw [hPmv]
                    omega
                  have hjv : (((c.1 + 1, c.2).2 - 1) / 2).toNat % 2 = 0 := by
                    show ((c.2 - 1) / 2).toNat % 2 = 0
                    exact hjp
                  rw [famF_nonchain_even hv hyv hxv h0v hgev hrev hjv]
                  apply Prod.ext <;> omega
              · have hjp' : ¬j % 2 = 0 := by rwa [hJ] at hjp
                by_cases hp : famPos m (c.1 + 1, c.2) < t
                · -- mid, j odd, used by left cell (chain)
                  rw [famF_mid_odd_of_lt hc hy hx hx0 hxm hg hjp hp]
                  obtain ⟨a, ha1, ha2, hxa⟩ : ∃ a : ℕ, 1 ≤ a ∧ a ≤ m - 1 ∧ c.1 = 2 * (a : ℤ) :=
                    ⟨(c.1 / 2).toNat, by omega, by omega, by omega⟩
                  have hve : (c.1 + 1, c.2) =
                      ((2 * (a : ℤ) + 1 : ℤ), (2 * (j : ℤ) + 1 : ℤ)) := by
                    apply Prod.ext <;> omega
                  have hPv : famPos m (c.1 + 1, c.2) = j * m + a := by
                    rw [hve, famPos_eq, if_neg hjp']
                    try simp
                  have hPmv : famPos m (c.1 + 1, c.2) % m = a := by
                    rw [hve, famPos_mod m a j (by omega) (by omega), if_neg hjp']
                  have hv : (c.1 + 1, c.2) ∈ board (2 * m + 1) := by
                    rw [mem_board]
                    exact ⟨by omega, by omega, by omega, by omega⟩
                  have hyv : (c.1 + 1, c.2).2 % 2 = 1 := by
                    show c.2 % 2 = 1
                    omega
                  have hxv : (c.1 + 1, c.2).1 % 2 = 1 := by
                    show (c.1 + 1) % 2 = 1
                    omega
                  have h0v : famPos m (c.1 + 1, c.2) ≠ 0 := by
                    rw [hPv]
                    omega
                  have hrsv : famPos m (c.1 + 1, c.2) % m ≠ 0 := by
                    rw [hPmv]
                    omega
                  have hjv : ¬(((c.1 + 1, c.2).2 - 1) / 2).toNat % 2 = 0 := by
                    show ¬((c.2 - 1) / 2).toNat % 2 = 0
                    exact hjp
                  rw [famF_chain_odd hv hyv hxv h0v hp hrsv hjv]
                  apply Prod.ext <;> omega
                · -- mid, j odd, used by right cell (nonchain)
                  rw [famF_mid_odd_of_ge hc hy hx hx0 hxm hg hjp hp]
                  obtain ⟨a, ha1, ha2, hxa⟩ : ∃ a : ℕ, 1 ≤ a ∧ a ≤ m - 1 ∧ c.1 = 2 * (a : ℤ) :=
                    ⟨(c.1 / 2).toNat, by omega, by omega, by omega⟩
                  have hve : (c.1 - 1, c.2) =
                      ((2 * ((a - 1 : ℕ) : ℤ) + 1 : ℤ), (2 * (j : ℤ) + 1 : ℤ)) := by
                    apply Prod.ext <;> omega
                  have hPv : famPos m (c.1 - 1, c.2) = j * m + (a - 1) := by
                    rw [hve, famPos_eq, if_neg hjp']
                  have hPmv : famPos m (c.1 - 1, c.2) % m = a - 1 := by
                    rw [hve, famPos_mod m (a - 1) j (by omega) (by omega), if_neg hjp']
                  have hve2 : (c.1 + 1, c.2) =
                      ((2 * (a : ℤ) + 1 : ℤ), (2 * (j : ℤ) + 1 : ℤ)) := by
                    apply Prod.ext <;> omega
                  have hPv2 : famPos m (c.1 + 1, c.2) = j * m + a := by
                    rw [hve2, famPos_eq, if_neg hjp']
                  have hgev : ¬famPos m (c.1 - 1, c.2) < t := by
                    rw [hPv]
                    intro hlt2
                    rw [hPv2] at hp
                    have ht : t = j * m + a := by omega
                    have h1g : t % m ≠ 0 := by
                      rw [ht, add_comm (j * m) a, mul_comm j m, Nat.add_mul_mod_self_left,
                        Nat.mod_eq_of_lt (by omega : a < m)]
                      omega
                    have h2g : ((c.2 - 1) / 2).toNat = t / m := by
                      rw [hJ, ht, add_comm (j * m) a, mul_comm j m,
                        Nat.add_mul_div_left _ _ (by omega : 0 < m),
                        Nat.div_eq_of_lt (by omega : a < m), zero_add]
                    have htmj : t / m = j := by rw [← h2g, hJ]
                    have h3g : c.1 = famGx m t := by
                      rw [famGx_eq_of_odd (by rw [htmj]; exact hjp')]
                      have htm2 : t % m = a := by
                        rw [ht, add_comm (j * m) a, mul_comm j m, Nat.add_mul_mod_self_left,
                          Nat.mod_eq_of_lt (by omega : a < m)]
                      rw [htm2]
                      omega
                    exact hg ⟨h1g, h2g, h3g⟩
                  have hv : (c.1 - 1, c.2) ∈ board (2 * m + 1) := by
                    rw [mem_board]
                    exact ⟨by omega, by omega, by omega, by omega⟩
                  have hyv : (c.1 - 1, c.2).2 % 2 = 1 := by
                    show c.2 % 2 = 1
                    omega
                  have hxv : (c.1 - 1, c.2).1 % 2 = 1 := by
                    show (c.1 - 1) % 2 = 1
                    omega
                  have h0v : famPos m (c.1 - 1, c.2) ≠ 0 := by
                    rw [hPv]
                    omega
                  have hrev : famPos m (c.1 - 1, c.2) % m ≠ m - 1 := by
                    rw [hPmv]
                    omega
                  have hjv : ¬(((c.1 - 1, c.2).2 - 1) / 2).toNat % 2 = 0 := by
                    show ¬((c.2 - 1) / 2).toNat % 2 = 0
                    exact hjp
                  rw [famF_nonchain_odd hv hyv hxv h0v hgev hrev hjv]
                  apply Prod.ext <;> omega
    · -- even rows
      have hy0 : c.2 % 2 = 0 := by omega
      have hb1 : (0 : ℤ) ≤ c.1 := (mem_board.mp hc).1
      have hb2 : c.1 ≤ 2 * (m : ℤ) := by
        have h := (mem_board.mp hc).2.1
        omega
      have hb3 : (0 : ℤ) ≤ c.2 := (mem_board.mp hc).2.2.1
      have hb4 : c.2 ≤ 2 * (m : ℤ) := by
        have h := (mem_board.mp hc).2.2.2
        omega
      obtain ⟨b, hbm, hcy⟩ : ∃ b : ℕ, b ≤ m ∧ c.2 = 2 * (b : ℤ) :=
        ⟨(c.2 / 2).toNat, by omega, by omega⟩
      have hB : (c.2 / 2).toNat = b := by omega
      by_cases hx : c.1 % 2 = 0
      · by_cases hx0 : c.1 = 0
        · by_cases hb0 : b = famB0 m t
          · have hb' : (c.2 / 2).toNat = famB0 m t := by rwa [hB]
            rw [famF_e0_eq hc hy hx hx0 hb']
            have hv : ((1 : ℤ), c.2) ∈ board (2 * m + 1) := by
              rw [mem_board]
              exact ⟨by omega, by omega, by omega, by omega⟩
            have hyv : ¬((1 : ℤ), c.2).2 % 2 = 1 := by
              show ¬c.2 % 2 = 1
              exact hy
            have hxv : ¬((1 : ℤ), c.2).1 % 2 = 0 := by
              show ¬(1 : ℤ) % 2 = 0
              omega
            have hBv : (((1 : ℤ), c.2).2 / 2).toNat = b := by
              show (c.2 / 2).toNat = b
              exact hB
            have hhv : ¬(1 ≤ (((1 : ℤ), c.2).2 / 2).toNat ∧
                (((1 : ℤ), c.2).2 / 2).toNat * m ≠ t ∧
                ((1 : ℤ), c.2).1 = famHoleX m (((1 : ℤ), c.2).2 / 2).toNat) := by
              rw [hBv]
              intro ⟨g1, g2, g3⟩
              have g3' : (1 : ℤ) = famHoleX m b := g3
              by_cases hbo : b % 2 = 1
              · rw [famHoleX_eq_of_odd hbo] at g3'
                rcases famB0_spec (m := m) (t := t) with h | h | h | h
                · rw [hb0, h.2] at g1
                  omega
                · rw [hb0, h.2.2] at g1
                  omega
                · rw [hb0, h.2.2.2] at hbo
                  rw [h.2.2.1] at hbo
                  omega
                · rw [hb0, h.2.2.2] at g1
                  omega
              · rw [famHoleX_eq_of_even hbo] at g3'
                have hm1 : m = 1 := by omega
                subst hm1
                rw [famB0_eq_of_mod_zero (Nat.mod_one t)] at hb0
                omega
            have hev : ((1 : ℤ), c.2).1 < famEsc m t (((1 : ℤ), c.2).2 / 2).toNat := by
              rw [hBv]
              show (1 : ℤ) < famEsc m t b
              exact famEsc_gt_one_of_b0 hm hb0
            rw [famF_oint_of_lt hv hyv hxv hhv hev]
            apply Prod.ext <;> omega
          · by_cases hb1' : b < famB0 m t
            · have hb1'' : (c.2 / 2).toNat ≠ famB0 m t := by rwa [hB]
              have hb2'' : (c.2 / 2).toNat < famB0 m t := by rwa [hB]
              rw [famF_e0_lt hc hy hx hx0 hb1'' hb2'']
              have hv : ((0 : ℤ), c.2 + 1) ∈ board (2 * m + 1) := by
                rw [mem_board]
                have hle := famB0_le (m := m) (t := t)
                exact ⟨by omega, by omega, by omega, by omega⟩
              have hyv : ((0 : ℤ), c.2 + 1).2 % 2 = 1 := by
                show (c.2 + 1) % 2 = 1
                omega
              have hxv : ¬((0 : ℤ), c.2 + 1).1 % 2 = 1 := by
                show ¬(0 : ℤ) % 2 = 1
                omega
              have h0v : ((0 : ℤ), c.2 + 1).1 = 0 := rfl
              have hjv : ((((0 : ℤ), c.2 + 1).2 - 1) / 2).toNat < famB0 m t := by
                have h9 : ((((0 : ℤ), c.2 + 1).2 - 1) / 2).toNat = b := by
                  show ((c.2 + 1 - 1) / 2).toNat = b
                  omega
                rw [h9]
                exact hb1'
              rw [famF_col0_of_lt hv hyv hxv h0v hjv]
              apply Prod.ext <;> omega
            · have hb1'' : (c.2 / 2).toNat ≠ famB0 m t := by rwa [hB]
              have hb2'' : ¬(c.2 / 2).toNat < famB0 m t := by rwa [hB]
              rw [famF_e0_gt hc hy hx hx0 hb1'' hb2'']
              have hv : ((0 : ℤ), c.2 - 1) ∈ board (2 * m + 1) := by
                rw [mem_board]
                exact ⟨by omega, by omega, by omega, by omega⟩
              have hyv : ((0 : ℤ), c.2 - 1).2 % 2 = 1 := by
                show (c.2 - 1) % 2 = 1
                omega
              have hxv : ¬((0 : ℤ), c.2 - 1).1 % 2 = 1 := by
                show ¬(0 : ℤ) % 2 = 1
                omega
              have h0v : ((0 : ℤ), c.2 - 1).1 = 0 := rfl
              have hjv : ¬((((0 : ℤ), c.2 - 1).2 - 1) / 2).toNat < famB0 m t := by
                have h9 : ((((0 : ℤ), c.2 - 1).2 - 1) / 2).toNat = b - 1 := by
                  show ((c.2 - 1 - 1) / 2).toNat = b - 1
                  omega
                rw [h9]
                omega
              rw [famF_col0_of_ge hv hyv hxv h0v hjv]
              apply Prod.ext <;> omega
        · by_cases hxm : c.1 = 2 * (m : ℤ)
          · by_cases hb0 : b = famB1 m t
            · have hb' : (c.2 / 2).toNat = famB1 m t := by rwa [hB]
              rw [famF_em_eq hc hy hx hx0 hxm hb']
              have hv : (2 * (m : ℤ) - 1, c.2) ∈ board (2 * m + 1) := by
                rw [mem_board]
                exact ⟨by omega, by omega, by omega, by omega⟩
              have hyv : ¬(2 * (m : ℤ) - 1, c.2).2 % 2 = 1 := by
                show ¬c.2 % 2 = 1
                exact hy
              have hxv : ¬(2 * (m : ℤ) - 1, c.2).1 % 2 = 0 := by
                show ¬(2 * (m : ℤ) - 1) % 2 = 0
                omega
              have hBv : ((2 * (m : ℤ) - 1, c.2).2 / 2).toNat = b := by
                show (c.2 / 2).toNat = b
                exact hB
              have hhv : ¬(1 ≤ ((2 * (m : ℤ) - 1, c.2).2 / 2).toNat ∧
                  ((2 * (m : ℤ) - 1, c.2).2 / 2).toNat * m ≠ t ∧
                  (2 * (m : ℤ) - 1, c.2).1 = famHoleX m ((2 * (m : ℤ) - 1, c.2).2 / 2).toNat) := by
                rw [hBv]
                intro ⟨g1, g2, g3⟩
                have g3' : 2 * (m : ℤ) - 1 = famHoleX m b := g3
                by_cases hbo : b % 2 = 1
                · rw [famHoleX_eq_of_odd hbo] at g3'
                  have hm1 : m = 1 := by omega
                  subst hm1
                  rw [famB1_eq_of_mod_zero (Nat.mod_one t), Nat.div_one] at hb0
                  omega
                · rw [famHoleX_eq_of_even hbo] at g3'
                  rcases famB1_spec (m := m) (t := t) with h | h | h | h
                  · have hbm : b * m = t := by
                      rw [hb0, h.2]
                      exact Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h.1)
                    exact g2 hbm
                  · have hbz : b = 0 := by rw [hb0]; exact h.2.2
                    omega
                  · have hbz : b = 0 := by rw [hb0]; exact h.2.2.2
                    omega
                  · rw [hb0, h.2.2.2] at hbo
                    omega
              have hev : ¬(2 * (m : ℤ) - 1, c.2).1 < famEsc m t ((2 * (m : ℤ) - 1, c.2).2 / 2).toNat := by
                rw [hBv]
                show ¬2 * (m : ℤ) - 1 < famEsc m t b
                have hle := famEsc_lt_of_b1 hm h1 hb0
                omega
              rw [famF_oint_of_ge hv hyv hxv hhv hev]
              apply Prod.ext <;> omega
            · by_cases hb1' : b < famB1 m t
              · have hb1'' : (c.2 / 2).toNat ≠ famB1 m t := by rwa [hB]
                have hb2'' : (c.2 / 2).toNat < famB1 m t := by rwa [hB]
                rw [famF_em_lt hc hy hx hx0 hxm hb1'' hb2'']
                have hv : (2 * (m : ℤ), c.2 + 1) ∈ board (2 * m + 1) := by
                  rw [mem_board]
                  have hle := famB1_le (m := m) (t := t)
                  exact ⟨by omega, by omega, by omega, by omega⟩
                have hyv : (2 * (m : ℤ), c.2 + 1).2 % 2 = 1 := by
                  show (c.2 + 1) % 2 = 1
                  omega
                have hxv : ¬(2 * (m : ℤ), c.2 + 1).1 % 2 = 1 := by
                  show ¬(2 * (m : ℤ)) % 2 = 1
                  omega
                have h0v : (2 * (m : ℤ), c.2 + 1).1 ≠ 0 := by
                  show 2 * (m : ℤ) ≠ 0
                  omega
                have hjv : (((2 * (m : ℤ), c.2 + 1).2 - 1) / 2).toNat < famB1 m t := by
                  have h9 : (((2 * (m : ℤ), c.2 + 1).2 - 1) / 2).toNat = b := by
                    show ((c.2 + 1 - 1) / 2).toNat = b
                    omega
                  rw [h9]
                  exact hb1'
                rw [famF_colm_of_lt hv hyv hxv h0v rfl hjv]
                apply Prod.ext <;> omega
              · have hb1'' : (c.2 / 2).toNat ≠ famB1 m t := by rwa [hB]
                have hb2'' : ¬(c.2 / 2).toNat < famB1 m t := by rwa [hB]
                rw [famF_em_gt hc hy hx hx0 hxm hb1'' hb2'']
                have hv : (2 * (m : ℤ), c.2 - 1) ∈ board (2 * m + 1) := by
                  rw [mem_board]
                  exact ⟨by omega, by omega, by omega, by omega⟩
                have hyv : (2 * (m : ℤ), c.2 - 1).2 % 2 = 1 := by
                  show (c.2 - 1) % 2 = 1
                  omega
                have hxv : ¬(2 * (m : ℤ), c.2 - 1).1 % 2 = 1 := by
                  show ¬(2 * (m : ℤ)) % 2 = 1
                  omega
                have h0v : (2 * (m : ℤ), c.2 - 1).1 ≠ 0 := by
                  show 2 * (m : ℤ) ≠ 0
                  omega
                have hjv : ¬(((2 * (m : ℤ), c.2 - 1).2 - 1) / 2).toNat < famB1 m t := by
                  have h9 : (((2 * (m : ℤ), c.2 - 1).2 - 1) / 2).toNat = b - 1 := by
                    show ((c.2 - 1 - 1) / 2).toNat = b - 1
                    omega
                  rw [h9]
                  omega
                rw [famF_colm_of_ge hv hyv hxv h0v rfl hjv]
                rw [Prod.ext_iff]
                exact ⟨by omega, by omega⟩
          · by_cases hg : t % m ≠ 0 ∧ (c.2 / 2).toNat = t / m ∧ c.1 = famGx m t
            · rw [famF_gap_e hc hy hx hx0 hxm hg]
              have hgx := famGx_mem hm hg.1
              rw [hB] at hg
              have hg2 : t / m < m := by
                rw [Nat.div_lt_iff_lt_mul hm]
                have h6 : m ^ 2 = m * m := by ring
                rw [h6] at h2
                rcases eq_or_lt_of_le h2 with h | h
                · exfalso
                  exact hg.1 (by rw [h]; simp)
                · exact h
              have hv : (c.1, c.2 + 1) ∈ board (2 * m + 1) := by
                rw [mem_board]
                exact ⟨by omega, by omega, by omega, by omega⟩
              have hyv : (c.1, c.2 + 1).2 % 2 = 1 := by
                show (c.2 + 1) % 2 = 1
                omega
              have hxv : ¬(c.1, c.2 + 1).1 % 2 = 1 := by
                show ¬c.1 % 2 = 1
                rw [hg.2.2]
                omega
              have h0v : (c.1, c.2 + 1).1 ≠ 0 := by
                show c.1 ≠ 0
                rw [hg.2.2]
                omega
              have hmv : (c.1, c.2 + 1).1 ≠ 2 * (m : ℤ) := by
                show c.1 ≠ 2 * (m : ℤ)
                rw [hg.2.2]
                omega
              have hBv : (((c.1, c.2 + 1).2 - 1) / 2).toNat = b := by
                show ((c.2 + 1 - 1) / 2).toNat = b
                omega
              have hgv : t % m ≠ 0 ∧ (((c.1, c.2 + 1).2 - 1) / 2).toNat = t / m ∧
                  (c.1, c.2 + 1).1 = famGx m t := by
                refine ⟨hg.1, by rw [hBv]; exact hg.2.1, ?_⟩
                show c.1 = famGx m t
                exact hg.2.2
              rw [famF_gap_mid hv hyv hxv h0v hmv hgv]
              apply Prod.ext <;> omega
            · by_cases he : c.1 < famEsc m t b
              · have he' : c.1 < famEsc m t (c.2 / 2).toNat := by rwa [hB]
                rw [famF_eint_of_lt hc hy hx hx0 hxm hg he']
                have hv : (c.1 + 1, c.2) ∈ board (2 * m + 1) := by
                  rw [mem_board]
                  exact ⟨by omega, by omega, by omega, by omega⟩
                have hyv : ¬(c.1 + 1, c.2).2 % 2 = 1 := by
                  show ¬c.2 % 2 = 1
                  exact hy
                have hxv : ¬(c.1 + 1, c.2).1 % 2 = 0 := by
                  show ¬(c.1 + 1) % 2 = 0
                  omega
                have hBv : ((c.1 + 1, c.2).2 / 2).toNat = b := by
                  show (c.2 / 2).toNat = b
                  exact hB
                have hhv : ¬(1 ≤ ((c.1 + 1, c.2).2 / 2).toNat ∧
                    ((c.1 + 1, c.2).2 / 2).toNat * m ≠ t ∧
                    (c.1 + 1, c.2).1 = famHoleX m ((c.1 + 1, c.2).2 / 2).toNat) := by
                  rw [hBv]
                  intro ⟨g1, g2, g3⟩
                  have g3' : c.1 + 1 = famHoleX m b := g3
                  by_cases hbo : b % 2 = 1
                  · rw [famHoleX_eq_of_odd hbo] at g3'
                    omega
                  · rw [famHoleX_eq_of_even hbo] at g3'
                    by_cases hgap : t % m ≠ 0 ∧ b = t / m
                    · rw [famEsc_eq_gx hgap.1 hgap.2] at he
                      have hgx := famGx_mem hm hgap.1
                      omega
                    · rw [famEsc_eq_zero_of_even hgap g1 g2 hbo] at he
                      omega
                have hev : (c.1 + 1, c.2).1 < famEsc m t ((c.1 + 1, c.2).2 / 2).toNat := by
                  rw [hBv]
                  show c.1 + 1 < famEsc m t b
                  obtain ⟨k, hk⟩ := famEsc_even (t := t) hm b
                  rw [hk] at he ⊢
                  omega
                rw [famF_oint_of_lt hv hyv hxv hhv hev]
                apply Prod.ext <;> omega
              · have he' : ¬c.1 < famEsc m t (c.2 / 2).toNat := by rwa [hB]
                rw [famF_eint_of_ge hc hy hx hx0 hxm hg he']
                have hv : (c.1 - 1, c.2) ∈ board (2 * m + 1) := by
                  rw [mem_board]
                  exact ⟨by omega, by omega, by omega, by omega⟩
                have hyv : ¬(c.1 - 1, c.2).2 % 2 = 1 := by
                  show ¬c.2 % 2 = 1
                  exact hy
                have hxv : ¬(c.1 - 1, c.2).1 % 2 = 0 := by
                  show ¬(c.1 - 1) % 2 = 0
                  omega
                have hBv : ((c.1 - 1, c.2).2 / 2).toNat = b := by
                  show (c.2 / 2).toNat = b
                  exact hB
                have hhv : ¬(1 ≤ ((c.1 - 1, c.2).2 / 2).toNat ∧
                    ((c.1 - 1, c.2).2 / 2).toNat * m ≠ t ∧
                    (c.1 - 1, c.2).1 = famHoleX m ((c.1 - 1, c.2).2 / 2).toNat) := by
                  rw [hBv]
                  intro ⟨g1, g2, g3⟩
                  have g3' : c.1 - 1 = famHoleX m b := g3
                  by_cases hbo : b % 2 = 1
                  · rw [famHoleX_eq_of_odd hbo] at g3'
                    by_cases hgap : t % m ≠ 0 ∧ b = t / m
                    · rw [famEsc_eq_gx hgap.1 hgap.2] at he
                      have hgx := famGx_mem hm hgap.1
                      rw [famGx_eq_of_odd (by rw [← hgap.2]; omega)] at he hgx
                      have hr1 : t % m = 1 := by omega
                      have h3g : c.1 = famGx m t := by
                        rw [famGx_eq_of_odd (by rw [← hgap.2]; omega), hr1]
                        omega
                      exact hg ⟨hgap.1, by rw [hB]; exact hgap.2, h3g⟩
                    · rw [famEsc_eq_two_m_of_odd hgap g1 g2 hbo] at he
                      omega
                  · rw [famHoleX_eq_of_even hbo] at g3'
                    omega
                have hev : ¬(c.1 - 1, c.2).1 < famEsc m t ((c.1 - 1, c.2).2 / 2).toNat := by
                  rw [hBv]
                  show ¬c.1 - 1 < famEsc m t b
                  obtain ⟨k, hk⟩ := famEsc_even (t := t) hm b
                  have hne : c.1 ≠ famEsc m t b := by
                    intro hesc
                    unfold famEsc at hesc
                    split_ifs at hesc with g1 g2 g3 g4
                    · exact hg ⟨g1.1, by rw [hB]; exact g1.2, hesc⟩
                    · exact hxm hesc
                    · exact hx0 hesc
                    · exact hxm hesc
                    · exact hx0 hesc
                  rw [hk] at hne he ⊢
                  omega
                rw [famF_oint_of_ge hv hyv hxv hhv hev]
                apply Prod.ext <;> omega
      · by_cases hh : 1 ≤ (c.2 / 2).toNat ∧ (c.2 / 2).toNat * m ≠ t ∧
            c.1 = famHoleX m (c.2 / 2).toNat
        · rw [hB] at hh
          by_cases hbm' : (c.2 / 2).toNat * m < t
          · rw [hB] at hbm'
            have hh' : 1 ≤ (c.2 / 2).toNat ∧ (c.2 / 2).toNat * m ≠ t ∧
                c.1 = famHoleX m (c.2 / 2).toNat := by
              refine ⟨?_, ?_, ?_⟩ <;> rw [hB]
              · exact hh.1
              · exact hh.2.1
              · exact hh.2.2
            have hbm'' : (c.2 / 2).toNat * m < t := by rw [hB]; exact hbm'
            rw [famF_hole_of_lt hc hy hx hh' hbm'']
            have hbm2 : b < m := by
              by_contra hb3
              push Not at hb3
              have h4 : m * m ≤ b * m := Nat.mul_le_mul_right m hb3
              have h6 : m ^ 2 = m * m := by ring
              omega
            by_cases hbo : b % 2 = 1
            · rw [famHoleX_eq_of_odd hbo] at hh
              have hve : (c.1, c.2 + 1) =
                  ((2 * ((0 : ℕ) : ℤ) + 1 : ℤ), (2 * (b : ℤ) + 1 : ℤ)) := by
                apply Prod.ext <;> omega
              have hPv : famPos m (c.1, c.2 + 1) = b * m := by
                rw [hve, famPos_eq, if_neg (by omega : ¬b % 2 = 0)]
                try simp
              have hPmv : famPos m (c.1, c.2 + 1) % m = 0 := by
                rw [hve, famPos_mod m 0 b (by omega) (by omega), if_neg (by omega : ¬b % 2 = 0)]
                try simp
              have hv : (c.1, c.2 + 1) ∈ board (2 * m + 1) := by
                rw [mem_board]
                exact ⟨by omega, by omega, by omega, by omega⟩
              have hyv : (c.1, c.2 + 1).2 % 2 = 1 := by
                show (c.2 + 1) % 2 = 1
                omega
              have hxv : (c.1, c.2 + 1).1 % 2 = 1 := by
                show c.1 % 2 = 1
                rw [hh.2.2]
                omega
              have h0v : famPos m (c.1, c.2 + 1) ≠ 0 := by
                rw [hPv]
                intro hz
                rw [Nat.mul_eq_zero] at hz
                omega
              have hltv : famPos m (c.1, c.2 + 1) < t := by
                rw [hPv]
                exact hbm'
              rw [famF_chain_turn hv hyv hxv h0v hltv hPmv]
              apply Prod.ext <;> omega
            · rw [famHoleX_eq_of_even hbo] at hh
              have hve : (c.1, c.2 + 1) =
                  ((2 * ((m - 1 : ℕ) : ℤ) + 1 : ℤ), (2 * (b : ℤ) + 1 : ℤ)) := by
                apply Prod.ext <;> omega
              have hPv : famPos m (c.1, c.2 + 1) = b * m := by
                rw [hve, famPos_eq, if_pos (by omega : b % 2 = 0)]
                have h9 : m - 1 - (m - 1) = 0 := by omega
                rw [h9]
                simp
              have hPmv : famPos m (c.1, c.2 + 1) % m = 0 := by
                rw [hve, famPos_mod m (m - 1) b (by omega) (by omega), if_pos (by omega : b % 2 = 0)]
                have h9 : m - 1 - (m - 1) = 0 := by omega
                rw [h9]
              have hv : (c.1, c.2 + 1) ∈ board (2 * m + 1) := by
                rw [mem_board]
                exact ⟨by omega, by omega, by omega, by omega⟩
              have hyv : (c.1, c.2 + 1).2 % 2 = 1 := by
                show (c.2 + 1) % 2 = 1
                omega
              have hxv : (c.1, c.2 + 1).1 % 2 = 1 := by
                show c.1 % 2 = 1
                rw [hh.2.2]
                omega
              have h0v : famPos m (c.1, c.2 + 1) ≠ 0 := by
                rw [hPv]
                intro hz
                rw [Nat.mul_eq_zero] at hz
                omega
              have hltv : famPos m (c.1, c.2 + 1) < t := by
                rw [hPv]
                exact hbm'
              rw [famF_chain_turn hv hyv hxv h0v hltv hPmv]
              apply Prod.ext <;> omega
          · rw [hB] at hbm'
            have hh' : 1 ≤ (c.2 / 2).toNat ∧ (c.2 / 2).toNat * m ≠ t ∧
                c.1 = famHoleX m (c.2 / 2).toNat := by
              refine ⟨?_, ?_, ?_⟩ <;> rw [hB]
              · exact hh.1
              · exact hh.2.1
              · exact hh.2.2
            have hbm'' : ¬(c.2 / 2).toNat * m < t := by rw [hB]; exact hbm'
            rw [famF_hole_of_ge hc hy hx hh' hbm'']
            by_cases hbo : b % 2 = 1
            · rw [famHoleX_eq_of_odd hbo] at hh
              have hve : (c.1, c.2 - 1) =
                  ((2 * ((0 : ℕ) : ℤ) + 1 : ℤ), (2 * ((b - 1 : ℕ) : ℤ) + 1 : ℤ)) := by
                apply Prod.ext <;> omega
              have hPv : famPos m (c.1, c.2 - 1) = (b - 1) * m + (m - 1) := by
                rw [hve, famPos_eq, if_pos (by omega : (b - 1) % 2 = 0)]
                try simp
              have hPmv : famPos m (c.1, c.2 - 1) % m = m - 1 := by
                rw [hve, famPos_mod m 0 (b - 1) (by omega) (by omega), if_pos (by omega : (b - 1) % 2 = 0)]
                try simp
              have hv : (c.1, c.2 - 1) ∈ board (2 * m + 1) := by
                rw [mem_board]
                exact ⟨by omega, by omega, by omega, by omega⟩
              have hyv : (c.1, c.2 - 1).2 % 2 = 1 := by
                show (c.2 - 1) % 2 = 1
                omega
              have hxv : (c.1, c.2 - 1).1 % 2 = 1 := by
                show c.1 % 2 = 1
                rw [hh.2.2]
                omega
              have hex : (b - 1) * m + (m - 1) = b * m - 1 := by
                have hbm : m ≤ b * m := by
                  have h9 := Nat.mul_le_mul_right m hh.1
                  simp at h9
                  exact h9
                rw [Nat.sub_mul]
                simp
                omega
              have h0v : famPos m (c.1, c.2 - 1) ≠ 0 := by
                rw [hPv]
                intro hz
                have h9 := Nat.add_eq_zero_iff.mp hz
                rw [Nat.mul_eq_zero] at h9
                omega
              have hgev : ¬famPos m (c.1, c.2 - 1) < t := by
                rw [hPv]
                omega
              rw [famF_nonchain_turn hv hyv hxv h0v hgev hPmv]
              apply Prod.ext <;> omega
            · rw [famHoleX_eq_of_even hbo] at hh
              have hve : (c.1, c.2 - 1) =
                  ((2 * ((m - 1 : ℕ) : ℤ) + 1 : ℤ), (2 * ((b - 1 : ℕ) : ℤ) + 1 : ℤ)) := by
                apply Prod.ext <;> omega
              have hPv : famPos m (c.1, c.2 - 1) = (b - 1) * m + (m - 1) := by
                rw [hve, famPos_eq, if_neg (by omega : ¬(b - 1) % 2 = 0)]
                try simp
              have hPmv : famPos m (c.1, c.2 - 1) % m = m - 1 := by
                rw [hve, famPos_mod m (m - 1) (b - 1) (by omega) (by omega), if_neg (by omega : ¬(b - 1) % 2 = 0)]
              have hv : (c.1, c.2 - 1) ∈ board (2 * m + 1) := by
                rw [mem_board]
                exact ⟨by omega, by omega, by omega, by omega⟩
              have hyv : (c.1, c.2 - 1).2 % 2 = 1 := by
                show (c.2 - 1) % 2 = 1
                omega
              have hxv : (c.1, c.2 - 1).1 % 2 = 1 := by
                show c.1 % 2 = 1
                rw [hh.2.2]
                omega
              have hex : (b - 1) * m + (m - 1) = b * m - 1 := by
                have hbm : m ≤ b * m := by
                  have h9 := Nat.mul_le_mul_right m hh.1
                  simp at h9
                  exact h9
                rw [Nat.sub_mul]
                simp
                omega
              have h0v : famPos m (c.1, c.2 - 1) ≠ 0 := by
                rw [hPv]
                intro hz
                have h9 := Nat.add_eq_zero_iff.mp hz
                rw [Nat.mul_eq_zero] at h9
                omega
              have hgev : ¬famPos m (c.1, c.2 - 1) < t := by
                rw [hPv]
                omega
              rw [famF_nonchain_turn hv hyv hxv h0v hgev hPmv]
              apply Prod.ext <;> omega
        · by_cases he : c.1 < famEsc m t b
          · have he' : c.1 < famEsc m t (c.2 / 2).toNat := by rwa [hB]
            rw [famF_oint_of_lt hc hy hx hh he']
            by_cases hc1 : c.1 = 1
            · -- v.1 = 0: column-0 route
              have hv : (c.1 - 1, c.2) ∈ board (2 * m + 1) := by
                rw [mem_board]
                exact ⟨by omega, by omega, by omega, by omega⟩
              have hyv : ¬(c.1 - 1, c.2).2 % 2 = 1 := by
                show ¬c.2 % 2 = 1
                exact hy
              have hxv : (c.1 - 1, c.2).1 % 2 = 0 := by
                show (c.1 - 1) % 2 = 0
                omega
              have h0v : (c.1 - 1, c.2).1 = 0 := by
                show c.1 - 1 = 0
                omega
              have hbb : b = famB0 m t := by
                rw [hc1] at he
                unfold famEsc at he
                split_ifs at he with g1 g2 g3 g4
                · rcases famB0_spec (m := m) (t := t) with h | h | h | h
                  · exact absurd h.1 g1.1
                  · rw [h.2.2]
                    omega
                  · rw [h.2.2.2]
                    exact g1.2
                  · exfalso
                    apply hh
                    refine ⟨?_, ?_, ?_⟩
                    · rw [hB]
                      omega
                    · show (c.2 / 2).toNat * m ≠ t
                      rw [hB]
                      intro hbm
                      have hdm := Nat.div_add_mod' t m
                      rw [← g1.2, hbm] at hdm
                      exact g1.1 (by omega : t % m = 0)
                    · show c.1 = famHoleX m (c.2 / 2).toNat
                      rw [hB, famHoleX_eq_of_odd (m := m) (by rw [g1.2]; omega)]
                      omega
                · exfalso
                  apply hh
                  refine ⟨?_, ?_, ?_⟩
                  · rw [hB]
                    exact g2.1
                  · rw [hB]
                    exact g2.2.1
                  · rw [hB, famHoleX_eq_of_odd (m := m) g2.2.2]
                    omega
                · omega
                · exact g4
                · omega
              have hbv : ((c.1 - 1, c.2).2 / 2).toNat = famB0 m t := by
                show (c.2 / 2).toNat = famB0 m t
                rw [hB]
                exact hbb
              rw [famF_e0_eq hv hyv hxv h0v hbv]
              apply Prod.ext <;> omega
            · -- interior: eint route
              have hv : (c.1 - 1, c.2) ∈ board (2 * m + 1) := by
                rw [mem_board]
                exact ⟨by omega, by omega, by omega, by omega⟩
              have hyv : ¬(c.1 - 1, c.2).2 % 2 = 1 := by
                show ¬c.2 % 2 = 1
                exact hy
              have hxv : (c.1 - 1, c.2).1 % 2 = 0 := by
                show (c.1 - 1) % 2 = 0
                omega
              have h0v : (c.1 - 1, c.2).1 ≠ 0 := by
                show c.1 - 1 ≠ 0
                omega
              have hmv : (c.1 - 1, c.2).1 ≠ 2 * (m : ℤ) := by
                show c.1 - 1 ≠ 2 * (m : ℤ)
                omega
              have hgv : ¬(t % m ≠ 0 ∧ ((c.1 - 1, c.2).2 / 2).toNat = t / m ∧
                  (c.1 - 1, c.2).1 = famGx m t) := by
                intro ⟨g1, g2, g3⟩
                have g2' : (c.2 / 2).toNat = t / m := g2
                rw [hB] at g2'
                have g3' : c.1 - 1 = famGx m t := g3
                rw [famEsc_eq_gx g1 g2'] at he
                omega
              have hev : (c.1 - 1, c.2).1 < famEsc m t ((c.1 - 1, c.2).2 / 2).toNat := by
                have hBv : ((c.1 - 1, c.2).2 / 2).toNat = b := by
                  show (c.2 / 2).toNat = b
                  exact hB
                rw [hBv]
                show c.1 - 1 < famEsc m t b
                omega
              rw [famF_eint_of_lt hv hyv hxv h0v hmv hgv hev]
              apply Prod.ext <;> omega
          · have he' : ¬c.1 < famEsc m t (c.2 / 2).toNat := by rwa [hB]
            rw [famF_oint_of_ge hc hy hx hh he']
            by_cases hc1 : c.1 = 2 * (m : ℤ) - 1
            · -- v.1 = 2m: column-2m route
              have hv : (c.1 + 1, c.2) ∈ board (2 * m + 1) := by
                rw [mem_board]
                exact ⟨by omega, by omega, by omega, by omega⟩
              have hyv : ¬(c.1 + 1, c.2).2 % 2 = 1 := by
                show ¬c.2 % 2 = 1
                exact hy
              have hxv : (c.1 + 1, c.2).1 % 2 = 0 := by
                show (c.1 + 1) % 2 = 0
                omega
              have h0v : (c.1 + 1, c.2).1 ≠ 0 := by
                show c.1 + 1 ≠ 0
                omega
              have hbb : b = famB1 m t := by
                rw [hc1] at he
                unfold famEsc at he
                split_ifs at he with g1 g2 g3 g4
                · rcases famB1_spec (m := m) (t := t) with h | h | h | h
                  · exact absurd h.1 g1.1
                  · rw [h.2.2]
                    omega
                  · exfalso
                    apply hh
                    refine ⟨?_, ?_, ?_⟩
                    · rw [hB]
                      omega
                    · show (c.2 / 2).toNat * m ≠ t
                      rw [hB]
                      intro hbm
                      have hdm := Nat.div_add_mod' t m
                      rw [← g1.2, hbm] at hdm
                      exact g1.1 (by omega : t % m = 0)
                    · show c.1 = famHoleX m (c.2 / 2).toNat
                      rw [hB, famHoleX_eq_of_even (m := m) (by omega)]
                      omega
                  · rw [h.2.2.2]
                    exact g1.2
                · omega
                · exfalso
                  apply hh
                  refine ⟨?_, ?_, ?_⟩
                  · rw [hB]
                    exact g3.1
                  · rw [hB]
                    exact g3.2
                  · have hbo : ¬b % 2 = 1 :=
                      fun hb2 => ‹¬(1 ≤ b ∧ b * m ≠ t ∧ b % 2 = 1)› ⟨g3.1, g3.2, hb2⟩
                    rw [hB, famHoleX_eq_of_even (m := m) hbo]
                    omega
                · omega
                · rcases famB1_spec (m := m) (t := t) with h | h | h | h
                  · rw [h.2]
                    have hbo0 : b ≠ 0 := by
                      have h9 := famB0_eq_of_mod_zero h.1
                      rw [h9] at g4
                      exact g4
                    have hbm : b * m = t := by
                      by_contra hbm
                      exact ‹¬(1 ≤ b ∧ b * m ≠ t)› ⟨by omega, hbm⟩
                    have hbm2 : t / m = b := by rw [← hbm]; exact Nat.mul_div_cancel b (show 0 < m by omega)
                    rw [hbm2]
                  · exfalso
                    by_cases hbz : b = 0
                    · exact ‹¬(t % m ≠ 0 ∧ b = t / m)› ⟨h.1, by rw [hbz]; exact h.2.1.symm⟩
                    · have hbm : b * m = t := by
                        by_contra hbm
                        exact ‹¬(1 ≤ b ∧ b * m ≠ t)› ⟨by omega, hbm⟩
                      have hbm2 : t / m = b := by rw [← hbm]; exact Nat.mul_div_cancel b (show 0 < m by omega)
                      rw [h.2.1] at hbm2
                      omega
                  · by_cases hbz : b = 0
                    · rw [h.2.2.2, hbz]
                    · exfalso
                      have hbm : b * m = t := by
                        by_contra hbm
                        exact ‹¬(1 ≤ b ∧ b * m ≠ t)› ⟨by omega, hbm⟩
                      have hbm2 : t / m = b := by rw [← hbm]; exact Nat.mul_div_cancel b (show 0 < m by omega)
                      exact ‹¬(t % m ≠ 0 ∧ b = t / m)› ⟨h.1, hbm2.symm⟩
                  · exfalso
                    have hb1 : 1 ≤ b := by
                      by_contra hbz
                      have hb0' : b = 0 := by omega
                      rw [hb0'] at g4
                      exact g4 (famB0_eq_of_odd h.1 h.2.1 h.2.2.1).symm
                    have hbm : b * m = t := by
                      by_contra hbm
                      exact ‹¬(1 ≤ b ∧ b * m ≠ t)› ⟨hb1, hbm⟩
                    have hbm2 : t / m = b := by rw [← hbm]; exact Nat.mul_div_cancel b (show 0 < m by omega)
                    exact ‹¬(t % m ≠ 0 ∧ b = t / m)› ⟨h.1, hbm2.symm⟩
              have hbv : ((c.1 + 1, c.2).2 / 2).toNat = famB1 m t := by
                show (c.2 / 2).toNat = famB1 m t
                rw [hB]
                exact hbb
              have hmv : (c.1 + 1, c.2).1 = 2 * (m : ℤ) := by
                show c.1 + 1 = 2 * (m : ℤ)
                omega
              rw [famF_em_eq hv hyv hxv h0v hmv hbv]
              apply Prod.ext <;> omega
            · -- interior: eint route
              have hv : (c.1 + 1, c.2) ∈ board (2 * m + 1) := by
                rw [mem_board]
                exact ⟨by omega, by omega, by omega, by omega⟩
              have hyv : ¬(c.1 + 1, c.2).2 % 2 = 1 := by
                show ¬c.2 % 2 = 1
                exact hy
              have hxv : (c.1 + 1, c.2).1 % 2 = 0 := by
                show (c.1 + 1) % 2 = 0
                omega
              have h0v : (c.1 + 1, c.2).1 ≠ 0 := by
                show c.1 + 1 ≠ 0
                omega
              have hmv : (c.1 + 1, c.2).1 ≠ 2 * (m : ℤ) := by
                show c.1 + 1 ≠ 2 * (m : ℤ)
                omega
              have hgv : ¬(t % m ≠ 0 ∧ ((c.1 + 1, c.2).2 / 2).toNat = t / m ∧
                  (c.1 + 1, c.2).1 = famGx m t) := by
                intro ⟨g1, g2, g3⟩
                have g2' : (c.2 / 2).toNat = t / m := g2
                rw [hB] at g2'
                have g3' : c.1 + 1 = famGx m t := g3
                rw [famEsc_eq_gx g1 g2'] at he
                omega
              have hev : ¬(c.1 + 1, c.2).1 < famEsc m t ((c.1 + 1, c.2).2 / 2).toNat := by
                have hBv : ((c.1 + 1, c.2).2 / 2).toNat = b := by
                  show (c.2 / 2).toNat = b
                  exact hB
                rw [hBv]
                show ¬c.1 + 1 < famEsc m t b
                omega
              rw [famF_eint_of_ge hv hyv hxv h0v hmv hgv hev]
              apply Prod.ext <;> omega
  · -- hf_adj
    intro c hc hfc
    by_cases hy : c.2 % 2 = 1
    · by_cases hx : c.1 % 2 = 1
      · obtain ⟨i, j, hi, hj, rfl⟩ := fam_odd_form hc hx hy
        have hJ : ((((2 * (i : ℤ) + 1 : ℤ), (2 * (j : ℤ) + 1 : ℤ)).2 - 1) / 2).toNat = j := by
          have h5 : ((2 * (j : ℤ) + 1 : ℤ) - 1) / 2 = (j : ℤ) := by omega
          simp only [h5, Int.toNat_natCast]
        by_cases h0 : famPos m ((2 * (i : ℤ) + 1 : ℤ), (2 * (j : ℤ) + 1 : ℤ)) = 0
        · rw [famF_fixed_of_pos_zero hc hy hx h0] at hfc
          exact absurd rfl hfc
        · by_cases hlt : famPos m ((2 * (i : ℤ) + 1 : ℤ), (2 * (j : ℤ) + 1 : ℤ)) < t
          · by_cases hrs : famPos m ((2 * (i : ℤ) + 1 : ℤ), (2 * (j : ℤ) + 1 : ℤ)) % m = 0
            · rw [famF_chain_turn hc hy hx h0 hlt hrs] at hfc ⊢
              exact isAdj_yminus _
            · by_cases hjp : j % 2 = 0
              · have hj' : ((((2 * (i : ℤ) + 1 : ℤ), (2 * (j : ℤ) + 1 : ℤ)).2 - 1) / 2).toNat % 2 = 0 := by
                  rw [hJ]; exact hjp
                rw [famF_chain_even hc hy hx h0 hlt hrs hj'] at hfc ⊢
                exact isAdj_xplus _
              · have hj' : ¬((((2 * (i : ℤ) + 1 : ℤ), (2 * (j : ℤ) + 1 : ℤ)).2 - 1) / 2).toNat % 2 = 0 := by
                  rw [hJ]; exact hjp
                rw [famF_chain_odd hc hy hx h0 hlt hrs hj'] at hfc ⊢
                exact isAdj_xminus _
          · by_cases hre : famPos m ((2 * (i : ℤ) + 1 : ℤ), (2 * (j : ℤ) + 1 : ℤ)) % m = m - 1
            · rw [famF_nonchain_turn hc hy hx h0 hlt hre] at hfc ⊢
              exact isAdj_yplus _
            · by_cases hjp : j % 2 = 0
              · have hj' : ((((2 * (i : ℤ) + 1 : ℤ), (2 * (j : ℤ) + 1 : ℤ)).2 - 1) / 2).toNat % 2 = 0 := by
                  rw [hJ]; exact hjp
                rw [famF_nonchain_even hc hy hx h0 hlt hre hj'] at hfc ⊢
                exact isAdj_xminus _
              · have hj' : ¬((((2 * (i : ℤ) + 1 : ℤ), (2 * (j : ℤ) + 1 : ℤ)).2 - 1) / 2).toNat % 2 = 0 := by
                  rw [hJ]; exact hjp
                rw [famF_nonchain_odd hc hy hx h0 hlt hre hj'] at hfc ⊢
                exact isAdj_xplus _
      · have h21 : (0 : ℤ) ≤ c.2 := (mem_board.mp hc).2.2.1
        have h22 : c.2 ≤ 2 * (m : ℤ) := by
          have h := (mem_board.mp hc).2.2.2
          omega
        obtain ⟨j, hjm, hcy⟩ : ∃ j : ℕ, j ≤ m - 1 ∧ c.2 = 2 * (j : ℤ) + 1 :=
          ⟨((c.2 - 1) / 2).toNat, by omega, by omega⟩
        have hJ : ((c.2 - 1) / 2).toNat = j := by omega
        by_cases hx0 : c.1 = 0
        · by_cases hjb : j < famB0 m t
          · have hj' : ((c.2 - 1) / 2).toNat < famB0 m t := by rwa [hJ]
            rw [famF_col0_of_lt hc hy hx hx0 hj'] at hfc ⊢
            rw [show ((0 : ℤ), c.2 - 1) = (c.1, c.2 - 1) from by ext <;> simp [hx0]]
            exact isAdj_yminus _
          · have hj' : ¬((c.2 - 1) / 2).toNat < famB0 m t := by rwa [hJ]
            rw [famF_col0_of_ge hc hy hx hx0 hj'] at hfc ⊢
            rw [show ((0 : ℤ), c.2 + 1) = (c.1, c.2 + 1) from by ext <;> simp [hx0]]
            exact isAdj_yplus _
        · by_cases hxm : c.1 = 2 * (m : ℤ)
          · by_cases hjb : j < famB1 m t
            · have hj' : ((c.2 - 1) / 2).toNat < famB1 m t := by rwa [hJ]
              rw [famF_colm_of_lt hc hy hx hx0 hxm hj'] at hfc ⊢
              rw [show ((2 * (m : ℤ)), c.2 - 1) = (c.1, c.2 - 1) from by ext <;> simp [hxm]]
              exact isAdj_yminus _
            · have hj' : ¬((c.2 - 1) / 2).toNat < famB1 m t := by rwa [hJ]
              rw [famF_colm_of_ge hc hy hx hx0 hxm hj'] at hfc ⊢
              rw [show ((2 * (m : ℤ)), c.2 + 1) = (c.1, c.2 + 1) from by ext <;> simp [hxm]]
              exact isAdj_yplus _
          · by_cases hg : t % m ≠ 0 ∧ ((c.2 - 1) / 2).toNat = t / m ∧ c.1 = famGx m t
            · rw [famF_gap_mid hc hy hx hx0 hxm hg] at hfc ⊢
              exact isAdj_yminus _
            · by_cases hjp : ((c.2 - 1) / 2).toNat % 2 = 0
              · by_cases hp : famPos m (c.1 - 1, c.2) < t
                · rw [famF_mid_even_of_lt hc hy hx hx0 hxm hg hjp hp] at hfc ⊢
                  exact isAdj_xminus _
                · rw [famF_mid_even_of_ge hc hy hx hx0 hxm hg hjp hp] at hfc ⊢
                  exact isAdj_xplus _
              · by_cases hp : famPos m (c.1 + 1, c.2) < t
                · rw [famF_mid_odd_of_lt hc hy hx hx0 hxm hg hjp hp] at hfc ⊢
                  exact isAdj_xplus _
                · rw [famF_mid_odd_of_ge hc hy hx hx0 hxm hg hjp hp] at hfc ⊢
                  exact isAdj_xminus _
    · have hy0 : c.2 % 2 = 0 := by omega
      have h21 : (0 : ℤ) ≤ c.2 := (mem_board.mp hc).2.2.1
      have h22 : c.2 ≤ 2 * (m : ℤ) := by
        have h := (mem_board.mp hc).2.2.2
        omega
      obtain ⟨b, hbm, hcy⟩ : ∃ b : ℕ, b ≤ m ∧ c.2 = 2 * (b : ℤ) :=
        ⟨(c.2 / 2).toNat, by omega, by omega⟩
      have hB : (c.2 / 2).toNat = b := by omega
      by_cases hx : c.1 % 2 = 0
      · by_cases hx0 : c.1 = 0
        · by_cases hb0 : b = famB0 m t
          · have hb' : (c.2 / 2).toNat = famB0 m t := by rwa [hB]
            rw [famF_e0_eq hc hy hx hx0 hb'] at hfc ⊢
            rw [show ((1 : ℤ), c.2) = (c.1 + 1, c.2) from by ext <;> simp [hx0]]
            exact isAdj_xplus _
          · by_cases hb1 : b < famB0 m t
            · have hb1' : (c.2 / 2).toNat ≠ famB0 m t := by rwa [hB]
              have hb2' : (c.2 / 2).toNat < famB0 m t := by rwa [hB]
              rw [famF_e0_lt hc hy hx hx0 hb1' hb2'] at hfc ⊢
              rw [show ((0 : ℤ), c.2 + 1) = (c.1, c.2 + 1) from by ext <;> simp [hx0]]
              exact isAdj_yplus _
            · have hb1' : (c.2 / 2).toNat ≠ famB0 m t := by rwa [hB]
              have hb2' : ¬(c.2 / 2).toNat < famB0 m t := by rwa [hB]
              rw [famF_e0_gt hc hy hx hx0 hb1' hb2'] at hfc ⊢
              rw [show ((0 : ℤ), c.2 - 1) = (c.1, c.2 - 1) from by ext <;> simp [hx0]]
              exact isAdj_yminus _
        · by_cases hxm : c.1 = 2 * (m : ℤ)
          · by_cases hb0 : b = famB1 m t
            · have hb' : (c.2 / 2).toNat = famB1 m t := by rwa [hB]
              rw [famF_em_eq hc hy hx hx0 hxm hb'] at hfc ⊢
              rw [show ((2 * (m : ℤ)) - 1, c.2) = (c.1 - 1, c.2) from by ext <;> simp [hxm]]
              exact isAdj_xminus _
            · by_cases hb1 : b < famB1 m t
              · have hb1' : (c.2 / 2).toNat ≠ famB1 m t := by rwa [hB]
                have hb2' : (c.2 / 2).toNat < famB1 m t := by rwa [hB]
                rw [famF_em_lt hc hy hx hx0 hxm hb1' hb2'] at hfc ⊢
                rw [show ((2 * (m : ℤ)), c.2 + 1) = (c.1, c.2 + 1) from by ext <;> simp [hxm]]
                exact isAdj_yplus _
              · have hb1' : (c.2 / 2).toNat ≠ famB1 m t := by rwa [hB]
                have hb2' : ¬(c.2 / 2).toNat < famB1 m t := by rwa [hB]
                rw [famF_em_gt hc hy hx hx0 hxm hb1' hb2'] at hfc ⊢
                rw [show ((2 * (m : ℤ)), c.2 - 1) = (c.1, c.2 - 1) from by ext <;> simp [hxm]]
                exact isAdj_yminus _
          · by_cases hg : t % m ≠ 0 ∧ (c.2 / 2).toNat = t / m ∧ c.1 = famGx m t
            · rw [famF_gap_e hc hy hx hx0 hxm hg] at hfc ⊢
              exact isAdj_yplus _
            · by_cases he : c.1 < famEsc m t b
              · have he' : c.1 < famEsc m t (c.2 / 2).toNat := by rwa [hB]
                rw [famF_eint_of_lt hc hy hx hx0 hxm hg he'] at hfc ⊢
                exact isAdj_xplus _
              · have he' : ¬c.1 < famEsc m t (c.2 / 2).toNat := by rwa [hB]
                rw [famF_eint_of_ge hc hy hx hx0 hxm hg he'] at hfc ⊢
                exact isAdj_xminus _
      · by_cases hh : 1 ≤ (c.2 / 2).toNat ∧ (c.2 / 2).toNat * m ≠ t ∧
            c.1 = famHoleX m (c.2 / 2).toNat
        · by_cases hbm' : (c.2 / 2).toNat * m < t
          · rw [famF_hole_of_lt hc hy hx hh hbm'] at hfc ⊢
            exact isAdj_yplus _
          · rw [famF_hole_of_ge hc hy hx hh hbm'] at hfc ⊢
            exact isAdj_yminus _
        · by_cases he : c.1 < famEsc m t b
          · have he' : c.1 < famEsc m t (c.2 / 2).toNat := by rwa [hB]
            rw [famF_oint_of_lt hc hy hx hh he'] at hfc ⊢
            exact isAdj_xminus _
          · have he' : ¬c.1 < famEsc m t (c.2 / 2).toNat := by rwa [hB]
            rw [famF_oint_of_ge hc hy hx hh he'] at hfc ⊢
            exact isAdj_xplus _
  · -- hf_fix
    refine ⟨(2 * (m : ℤ) - 1, 1), ⟨?_, ?_⟩, ?_⟩
    · rw [mem_board]
      exact ⟨by omega, by omega, by omega, by omega⟩
    · have hEb : ((2 * (m : ℤ) - 1 : ℤ), (1 : ℤ)) ∈ board (2 * m + 1) := by
        rw [mem_board]
        exact ⟨by omega, by omega, by omega, by omega⟩
      have hpar1 : ((2 * (m : ℤ) - 1 : ℤ), (1 : ℤ)).1 % 2 = 1 := by omega
      have hpar2 : ((2 * (m : ℤ) - 1 : ℤ), (1 : ℤ)).2 % 2 = 1 := by omega
      have hP0 : famPos m ((2 * (m : ℤ) - 1 : ℤ), (1 : ℤ)) = 0 := by
        have hE : ((2 * (m : ℤ) - 1 : ℤ), (1 : ℤ)) =
            ((2 * ((m - 1 : ℕ) : ℤ) + 1 : ℤ), (2 * ((0 : ℕ) : ℤ) + 1 : ℤ)) := by
          ext <;> simp <;> omega
        rw [hE, famPos_eq]
        try simp
      exact famF_fixed_of_pos_zero hEb hpar2 hpar1 hP0
    · intro c ⟨hc, hfc⟩
      by_cases hy : c.2 % 2 = 1
      · by_cases hx : c.1 % 2 = 1
        · obtain ⟨i, j, hi, hj, rfl⟩ := fam_odd_form hc hx hy
          have hJ : ((((2 * (i : ℤ) + 1 : ℤ), (2 * (j : ℤ) + 1 : ℤ)).2 - 1) / 2).toNat = j := by
            have h5 : ((2 * (j : ℤ) + 1 : ℤ) - 1) / 2 = (j : ℤ) := by omega
            simp only [h5, Int.toNat_natCast]
          have hP := famPos_eq m i j
          by_cases h0 : famPos m ((2 * (i : ℤ) + 1 : ℤ), (2 * (j : ℤ) + 1 : ℤ)) = 0
          · rw [hP] at h0
            have hjz : j = 0 := by
              split_ifs at h0 <;> {
                have h9 : j * m = 0 := by omega
                rw [Nat.mul_eq_zero] at h9
                omega
              }
            subst hjz
            split_ifs at h0
            · have hi' : i = m - 1 := by omega
              subst hi'
              rw [Prod.ext_iff]
              exact ⟨by omega, by simp⟩
            · omega
          · exfalso
            by_cases hlt : famPos m ((2 * (i : ℤ) + 1 : ℤ), (2 * (j : ℤ) + 1 : ℤ)) < t
            · by_cases hrs : famPos m ((2 * (i : ℤ) + 1 : ℤ), (2 * (j : ℤ) + 1 : ℤ)) % m = 0
              · rw [famF_chain_turn hc hy hx h0 hlt hrs] at hfc
                rw [Prod.ext_iff] at hfc
                simp at hfc
                try omega
              · by_cases hjp : j % 2 = 0
                · have hj' : ((((2 * (i : ℤ) + 1 : ℤ), (2 * (j : ℤ) + 1 : ℤ)).2 - 1) / 2).toNat % 2 = 0 := by
                    rw [hJ]; exact hjp
                  rw [famF_chain_even hc hy hx h0 hlt hrs hj'] at hfc
                  rw [Prod.ext_iff] at hfc
                  simp at hfc
                  try omega
                · have hj' : ¬((((2 * (i : ℤ) + 1 : ℤ), (2 * (j : ℤ) + 1 : ℤ)).2 - 1) / 2).toNat % 2 = 0 := by
                    rw [hJ]; exact hjp
                  rw [famF_chain_odd hc hy hx h0 hlt hrs hj'] at hfc
                  rw [Prod.ext_iff] at hfc
                  simp at hfc
                  try omega
            · by_cases hre : famPos m ((2 * (i : ℤ) + 1 : ℤ), (2 * (j : ℤ) + 1 : ℤ)) % m = m - 1
              · rw [famF_nonchain_turn hc hy hx h0 hlt hre] at hfc
                rw [Prod.ext_iff] at hfc
                simp at hfc
                try omega
              · by_cases hjp : j % 2 = 0
                · have hj' : ((((2 * (i : ℤ) + 1 : ℤ), (2 * (j : ℤ) + 1 : ℤ)).2 - 1) / 2).toNat % 2 = 0 := by
                    rw [hJ]; exact hjp
                  rw [famF_nonchain_even hc hy hx h0 hlt hre hj'] at hfc
                  rw [Prod.ext_iff] at hfc
                  simp at hfc
                  try omega
                · have hj' : ¬((((2 * (i : ℤ) + 1 : ℤ), (2 * (j : ℤ) + 1 : ℤ)).2 - 1) / 2).toNat % 2 = 0 := by
                    rw [hJ]; exact hjp
                  rw [famF_nonchain_odd hc hy hx h0 hlt hre hj'] at hfc
                  rw [Prod.ext_iff] at hfc
                  simp at hfc
                  try omega
        · have h21 : (0 : ℤ) ≤ c.2 := (mem_board.mp hc).2.2.1
          have h22 : c.2 ≤ 2 * (m : ℤ) := by
            have h := (mem_board.mp hc).2.2.2
            omega
          obtain ⟨j, hjm, hcy⟩ : ∃ j : ℕ, j ≤ m - 1 ∧ c.2 = 2 * (j : ℤ) + 1 :=
            ⟨((c.2 - 1) / 2).toNat, by omega, by omega⟩
          have hJ : ((c.2 - 1) / 2).toNat = j := by omega
          exfalso
          by_cases hx0 : c.1 = 0
          · by_cases hjb : j < famB0 m t
            · have hj' : ((c.2 - 1) / 2).toNat < famB0 m t := by rwa [hJ]
              rw [famF_col0_of_lt hc hy hx hx0 hj'] at hfc
              rw [Prod.ext_iff] at hfc
              simp at hfc
              try omega
            · have hj' : ¬((c.2 - 1) / 2).toNat < famB0 m t := by rwa [hJ]
              rw [famF_col0_of_ge hc hy hx hx0 hj'] at hfc
              rw [Prod.ext_iff] at hfc
              simp at hfc
              try omega
          · by_cases hxm : c.1 = 2 * (m : ℤ)
            · by_cases hjb : j < famB1 m t
              · have hj' : ((c.2 - 1) / 2).toNat < famB1 m t := by rwa [hJ]
                rw [famF_colm_of_lt hc hy hx hx0 hxm hj'] at hfc
                rw [Prod.ext_iff] at hfc
                simp at hfc
                try omega
              · have hj' : ¬((c.2 - 1) / 2).toNat < famB1 m t := by rwa [hJ]
                rw [famF_colm_of_ge hc hy hx hx0 hxm hj'] at hfc
                rw [Prod.ext_iff] at hfc
                simp at hfc
                try omega
            · by_cases hg : t % m ≠ 0 ∧ ((c.2 - 1) / 2).toNat = t / m ∧ c.1 = famGx m t
              · rw [famF_gap_mid hc hy hx hx0 hxm hg] at hfc
                rw [Prod.ext_iff] at hfc
                simp at hfc
                try omega
              · by_cases hjp : ((c.2 - 1) / 2).toNat % 2 = 0
                · by_cases hp : famPos m (c.1 - 1, c.2) < t
                  · rw [famF_mid_even_of_lt hc hy hx hx0 hxm hg hjp hp] at hfc
                    rw [Prod.ext_iff] at hfc
                    simp at hfc
                    try omega
                  · rw [famF_mid_even_of_ge hc hy hx hx0 hxm hg hjp hp] at hfc
                    rw [Prod.ext_iff] at hfc
                    simp at hfc
                    try omega
                · by_cases hp : famPos m (c.1 + 1, c.2) < t
                  · rw [famF_mid_odd_of_lt hc hy hx hx0 hxm hg hjp hp] at hfc
                    rw [Prod.ext_iff] at hfc
                    simp at hfc
                    try omega
                  · rw [famF_mid_odd_of_ge hc hy hx hx0 hxm hg hjp hp] at hfc
                    rw [Prod.ext_iff] at hfc
                    simp at hfc
                    try omega
      · have hy0 : c.2 % 2 = 0 := by omega
        have h21 : (0 : ℤ) ≤ c.2 := (mem_board.mp hc).2.2.1
        have h22 : c.2 ≤ 2 * (m : ℤ) := by
          have h := (mem_board.mp hc).2.2.2
          omega
        obtain ⟨b, hbm, hcy⟩ : ∃ b : ℕ, b ≤ m ∧ c.2 = 2 * (b : ℤ) :=
          ⟨(c.2 / 2).toNat, by omega, by omega⟩
        have hB : (c.2 / 2).toNat = b := by omega
        exfalso
        by_cases hx : c.1 % 2 = 0
        · by_cases hx0 : c.1 = 0
          · by_cases hb0 : b = famB0 m t
            · have hb' : (c.2 / 2).toNat = famB0 m t := by rwa [hB]
              rw [famF_e0_eq hc hy hx hx0 hb'] at hfc
              rw [Prod.ext_iff] at hfc
              simp at hfc
              try omega
            · by_cases hb1 : b < famB0 m t
              · have hb1' : (c.2 / 2).toNat ≠ famB0 m t := by rwa [hB]
                have hb2' : (c.2 / 2).toNat < famB0 m t := by rwa [hB]
                rw [famF_e0_lt hc hy hx hx0 hb1' hb2'] at hfc
                rw [Prod.ext_iff] at hfc
                simp at hfc
                try omega
              · have hb1' : (c.2 / 2).toNat ≠ famB0 m t := by rwa [hB]
                have hb2' : ¬(c.2 / 2).toNat < famB0 m t := by rwa [hB]
                rw [famF_e0_gt hc hy hx hx0 hb1' hb2'] at hfc
                rw [Prod.ext_iff] at hfc
                simp at hfc
                try omega
          · by_cases hxm : c.1 = 2 * (m : ℤ)
            · by_cases hb0 : b = famB1 m t
              · have hb' : (c.2 / 2).toNat = famB1 m t := by rwa [hB]
                rw [famF_em_eq hc hy hx hx0 hxm hb'] at hfc
                rw [Prod.ext_iff] at hfc
                simp at hfc
                try omega
              · by_cases hb1 : b < famB1 m t
                · have hb1' : (c.2 / 2).toNat ≠ famB1 m t := by rwa [hB]
                  have hb2' : (c.2 / 2).toNat < famB1 m t := by rwa [hB]
                  rw [famF_em_lt hc hy hx hx0 hxm hb1' hb2'] at hfc
                  rw [Prod.ext_iff] at hfc
                  simp at hfc
                  try omega
                · have hb1' : (c.2 / 2).toNat ≠ famB1 m t := by rwa [hB]
                  have hb2' : ¬(c.2 / 2).toNat < famB1 m t := by rwa [hB]
                  rw [famF_em_gt hc hy hx hx0 hxm hb1' hb2'] at hfc
                  rw [Prod.ext_iff] at hfc
                  simp at hfc
                  try omega
            · by_cases hg : t % m ≠ 0 ∧ (c.2 / 2).toNat = t / m ∧ c.1 = famGx m t
              · rw [famF_gap_e hc hy hx hx0 hxm hg] at hfc
                rw [Prod.ext_iff] at hfc
                simp at hfc
                try omega
              · by_cases he : c.1 < famEsc m t b
                · have he' : c.1 < famEsc m t (c.2 / 2).toNat := by rwa [hB]
                  rw [famF_eint_of_lt hc hy hx hx0 hxm hg he'] at hfc
                  rw [Prod.ext_iff] at hfc
                  simp at hfc
                  try omega
                · have he' : ¬c.1 < famEsc m t (c.2 / 2).toNat := by rwa [hB]
                  rw [famF_eint_of_ge hc hy hx hx0 hxm hg he'] at hfc
                  rw [Prod.ext_iff] at hfc
                  simp at hfc
                  try omega
        · by_cases hh : 1 ≤ (c.2 / 2).toNat ∧ (c.2 / 2).toNat * m ≠ t ∧
              c.1 = famHoleX m (c.2 / 2).toNat
          · by_cases hbm' : (c.2 / 2).toNat * m < t
            · rw [famF_hole_of_lt hc hy hx hh hbm'] at hfc
              rw [Prod.ext_iff] at hfc
              simp at hfc
              try omega
            · rw [famF_hole_of_ge hc hy hx hh hbm'] at hfc
              rw [Prod.ext_iff] at hfc
              simp at hfc
              try omega
          · by_cases he : c.1 < famEsc m t b
            · have he' : c.1 < famEsc m t (c.2 / 2).toNat := by rwa [hB]
              rw [famF_oint_of_lt hc hy hx hh he'] at hfc
              rw [Prod.ext_iff] at hfc
              simp at hfc
              try omega
            · have he' : ¬c.1 < famEsc m t (c.2 / 2).toNat := by rwa [hB]
              rw [famF_oint_of_ge hc hy hx hh he'] at hfc
              rw [Prod.ext_iff] at hfc
              simp at hfc
              try omega
/-- The empty cell of the family configuration is `E = (2m-1, 1)`. -/
theorem fam_empty (m t : ℕ) (C : Config (2 * m + 1)) (hCf : C.f = famF m t) (hm : 0 < m)
    (ht : 1 ≤ t) :
    C.empty = (2 * (m : ℤ) - 1, 1) := by
  have hEb : ((2 * (m : ℤ) - 1 : ℤ), (1 : ℤ)) ∈ board (2 * m + 1) := by
    rw [mem_board]
    exact ⟨by omega, by omega, by omega, by omega⟩
  have hpar1 : ((2 * (m : ℤ) - 1 : ℤ), (1 : ℤ)).1 % 2 = 1 := by omega
  have hpar2 : ((2 * (m : ℤ) - 1 : ℤ), (1 : ℤ)).2 % 2 = 1 := by omega
  have hP0 : famPos m ((2 * (m : ℤ) - 1 : ℤ), (1 : ℤ)) = 0 := by
    have hE : ((2 * (m : ℤ) - 1 : ℤ), (1 : ℤ)) =
        ((2 * ((m - 1 : ℕ) : ℤ) + 1 : ℤ), (2 * ((0 : ℕ) : ℤ) + 1 : ℤ)) := by
      ext <;> dsimp only <;> omega
    rw [hE, famPos_eq]
    simp
  exact (C.unique_fixed hEb (by rw [hCf]; exact famF_fixed_of_pos_zero hEb hpar2 hpar1 hP0)).symm

/-- The special cells of the family configuration are the odd-odd cells. -/
theorem fam_special (m t : ℕ) {C : Config (2 * m + 1)} (hCf : C.f = famF m t) (hm : 0 < m)
    (ht : 1 ≤ t)
    {c : Cell} : c ∈ C.special ↔ c ∈ board (2 * m + 1) ∧ c.1 % 2 = 1 ∧ c.2 % 2 = 1 := by
  have h1 : ((2 * (m : ℤ) - 1 : ℤ), (1 : ℤ)).1 % 2 = 1 := by omega
  have h2 : ((2 * (m : ℤ) - 1 : ℤ), (1 : ℤ)).2 % 2 = 1 := by omega
  rw [Config.mem_special, fam_empty m t C hCf hm ht, h1, h2]

/-- The only special cell at snake position 0 is the empty cell. -/
theorem fam_eq_empty_of_pos_zero (m t : ℕ) (C : Config (2 * m + 1)) (hCf : C.f = famF m t)
    (hm : 0 < m)
    (ht : 1 ≤ t) {s : Cell} (hs : s ∈ C.special) (h0 : famPos m s = 0) : s = C.empty := by
  have hsb : s ∈ board (2 * m + 1) := Config.mem_board_of_mem_special C hs
  have hpar := (fam_special m t hCf hm ht).mp hs
  obtain ⟨i, j, hi, hj, hcij⟩ := fam_odd_form hsb hpar.2.1 hpar.2.2
  have hP := famPos_eq m i j
  rw [hcij] at h0
  rw [hP] at h0
  have hjz : j = 0 := by
    split_ifs at h0 <;> {
      have h9 : j * m = 0 := by omega
      rw [Nat.mul_eq_zero] at h9
      omega
    }
  subst hjz
  split_ifs at h0
  · have hi' : i = m - 1 := by omega
    subst hi'
    rw [hcij, fam_empty m t C hCf hm ht]
    ext <;> simp <;> omega
  · omega

/-- Arrows at covered special cells: chain cells point backwards along the
snake, non-chain cells point forwards (the last one points off the board). -/
theorem fam_arrow_snake (m t : ℕ) (C : Config (2 * m + 1)) (hCf : C.f = famF m t) (hm : 0 < m)
    (ht : 1 ≤ t)
    {s : Cell} (hs : s ∈ C.special) (h0 : famPos m s ≠ 0) :
    (famPos m s < t → C.arrow s ∈ board (2 * m + 1) ∧ famPos m (C.arrow s) + 1 = famPos m s) ∧
    (¬famPos m s < t → C.arrow s ∉ board (2 * m + 1) ∨ famPos m (C.arrow s) = famPos m s + 1) := by
  have hsb : s ∈ board (2 * m + 1) := Config.mem_board_of_mem_special C hs
  have hpar := (fam_special m t hCf hm ht).mp hs
  obtain ⟨i, j, hi, hj, hcij⟩ := fam_odd_form hsb hpar.2.1 hpar.2.2
  have hx1 : s.1 = 2 * (i : ℤ) + 1 := by rw [hcij]
  have hx2 : s.2 = 2 * (j : ℤ) + 1 := by rw [hcij]
  have hJ : ((s.2 - 1) / 2).toNat = j := by rw [hx2]; omega
  have hP : famPos m s = j * m + if j % 2 = 0 then m - 1 - i else i := by
    rw [hcij]; exact famPos_eq m i j
  have hPm : famPos m s % m = if j % 2 = 0 then m - 1 - i else i := by
    rw [hcij]; exact famPos_mod m i j hi hj
  have harrow : C.arrow s = s + 2 • (famF m t s - s) := by simp only [Config.arrow, hCf]
  constructor
  · intro hlt
    by_cases hrs : famPos m s % m = 0
    · -- chain turn: arrow points to the previous row
      have hP0' : famPos m s = j * m := by
        rw [hP]
        rw [hPm] at hrs
        split_ifs at hrs ⊢ <;> omega
      have hlt' : j * m < t := by rw [← hP0']; exact hlt
      have hj1 : 1 ≤ j := by
        rcases Nat.eq_zero_or_pos j with h | h
        · subst h
          rw [hP0'] at h0
          simp at h0
        · exact h
      have hkey : (j - 1) * m + (m - 1) + 1 = j * m := by
        have h1 : m - 1 + 1 = m := by omega
        have h2 : (j - 1) * m + m = j * m := by
          have h3 : (j - 1) * m + 1 * m = j * m := by
            rw [← Nat.add_mul, Nat.sub_add_cancel hj1]
          rwa [Nat.one_mul] at h3
        omega
      rw [famF_chain_turn hsb hpar.2.2 hpar.2.1 h0 hlt hrs] at harrow
      have harr : C.arrow s = (s.1, s.2 - 2) := by
        rw [harrow]
        ext <;> simp [Prod.smul_mk, smul_eq_mul] <;> omega
      refine ⟨by rw [harr, mem_board]; exact ⟨by omega, by omega, by omega, by omega⟩, ?_⟩
      by_cases hjp : j % 2 = 0
      · rw [hPm, if_pos hjp] at hrs
        have hi' : i = m - 1 := by omega
        have hve : (s.1, s.2 - 2) =
            ((2 * ((m - 1 : ℕ) : ℤ) + 1 : ℤ), (2 * ((j - 1 : ℕ) : ℤ) + 1 : ℤ)) := by
          ext <;> dsimp only <;> omega
        rw [harr, hve, famPos_eq, if_neg (by omega : ¬(j - 1) % 2 = 0), hP0']
        omega
      · rw [hPm, if_neg hjp] at hrs
        have hi' : i = 0 := by omega
        have hve : (s.1, s.2 - 2) =
            ((2 * ((0 : ℕ) : ℤ) + 1 : ℤ), (2 * ((j - 1 : ℕ) : ℤ) + 1 : ℤ)) := by
          ext <;> dsimp only <;> omega
        rw [harr, hve, famPos_eq, if_pos (by omega : (j - 1) % 2 = 0), hP0']
        omega
    · by_cases hjp : j % 2 = 0
      · -- chain, in-row, j even
        have hj' : ((s.2 - 1) / 2).toNat % 2 = 0 := by rw [hJ]; exact hjp
        rw [famF_chain_even hsb hpar.2.2 hpar.2.1 h0 hlt hrs hj'] at harrow
        rw [hPm, if_pos hjp] at hrs
        have harr : C.arrow s = (s.1 + 2, s.2) := by
          rw [harrow]
          ext <;> simp [Prod.smul_mk, smul_eq_mul] <;> omega
        have hve : (s.1 + 2, s.2) =
            ((2 * ((i + 1 : ℕ) : ℤ) + 1 : ℤ), (2 * (j : ℤ) + 1 : ℤ)) := by
          ext <;> dsimp only <;> omega
        refine ⟨by rw [harr, mem_board]; exact ⟨by omega, by omega, by omega, by omega⟩, ?_⟩
        rw [harr, hve, famPos_eq, if_pos hjp, hP, if_pos hjp]
        omega
      · -- chain, in-row, j odd
        have hj' : ¬((s.2 - 1) / 2).toNat % 2 = 0 := by rw [hJ]; exact hjp
        rw [famF_chain_odd hsb hpar.2.2 hpar.2.1 h0 hlt hrs hj'] at harrow
        rw [hPm, if_neg hjp] at hrs
        have harr : C.arrow s = (s.1 - 2, s.2) := by
          rw [harrow]
          ext <;> simp [Prod.smul_mk, smul_eq_mul] <;> omega
        have hve : (s.1 - 2, s.2) =
            ((2 * ((i - 1 : ℕ) : ℤ) + 1 : ℤ), (2 * (j : ℤ) + 1 : ℤ)) := by
          ext <;> dsimp only <;> omega
        refine ⟨by rw [harr, mem_board]; exact ⟨by omega, by omega, by omega, by omega⟩, ?_⟩
        rw [harr, hve, famPos_eq, if_neg hjp, hP, if_neg hjp]
        omega
  · intro hge
    by_cases hre : famPos m s % m = m - 1
    · -- nonchain turn: arrow points to the next row (possibly off the board)
      have hP0' : famPos m s = j * m + (m - 1) := by
        rw [hP]
        rw [hPm] at hre
        split_ifs at hre ⊢ <;> omega
      rw [famF_nonchain_turn hsb hpar.2.2 hpar.2.1 h0 hge hre] at harrow
      have harr : C.arrow s = (s.1, s.2 + 2) := by
        rw [harrow]
        ext <;> simp [Prod.smul_mk, smul_eq_mul] <;> omega
      by_cases hjm : j = m - 1
      · -- last row: arrow points off the board
        refine Or.inl ?_
        rw [harr]
        intro hmem
        rw [mem_board] at hmem
        omega
      · refine Or.inr ?_
        have hj2 : (j + 1) * m = j * m + (m - 1) + 1 := by
          have h1 : m - 1 + 1 = m := by omega
          have h2 : (j + 1) * m = j * m + m := by ring
          omega
        by_cases hjp : j % 2 = 0
        · rw [hPm, if_pos hjp] at hre
          have hi' : i = 0 := by omega
          have hve : (s.1, s.2 + 2) =
              ((2 * ((0 : ℕ) : ℤ) + 1 : ℤ), (2 * ((j + 1 : ℕ) : ℤ) + 1 : ℤ)) := by
            ext <;> dsimp only <;> omega
          rw [harr, hve, famPos_eq, if_neg (by omega : ¬(j + 1) % 2 = 0), hP0']
          omega
        · rw [hPm, if_neg hjp] at hre
          have hi' : i = m - 1 := by omega
          have hve : (s.1, s.2 + 2) =
              ((2 * ((m - 1 : ℕ) : ℤ) + 1 : ℤ), (2 * ((j + 1 : ℕ) : ℤ) + 1 : ℤ)) := by
            ext <;> dsimp only <;> omega
          rw [harr, hve, famPos_eq, if_pos (by omega : (j + 1) % 2 = 0), hP0']
          omega
    · by_cases hjp : j % 2 = 0
      · -- nonchain, in-row, j even
        have hj' : ((s.2 - 1) / 2).toNat % 2 = 0 := by rw [hJ]; exact hjp
        rw [famF_nonchain_even hsb hpar.2.2 hpar.2.1 h0 hge hre hj'] at harrow
        rw [hPm, if_pos hjp] at hre
        have harr : C.arrow s = (s.1 - 2, s.2) := by
          rw [harrow]
          ext <;> simp [Prod.smul_mk, smul_eq_mul] <;> omega
        have hve : (s.1 - 2, s.2) =
            ((2 * ((i - 1 : ℕ) : ℤ) + 1 : ℤ), (2 * (j : ℤ) + 1 : ℤ)) := by
          ext <;> dsimp only <;> omega
        refine Or.inr ?_
        rw [harr, hve, famPos_eq, if_pos hjp, hP, if_pos hjp]
        omega
      · -- nonchain, in-row, j odd
        have hj' : ¬((s.2 - 1) / 2).toNat % 2 = 0 := by rw [hJ]; exact hjp
        rw [famF_nonchain_odd hsb hpar.2.2 hpar.2.1 h0 hge hre hj'] at harrow
        rw [hPm, if_neg hjp] at hre
        have harr : C.arrow s = (s.1 + 2, s.2) := by
          rw [harrow]
          ext <;> simp [Prod.smul_mk, smul_eq_mul] <;> omega
        have hve : (s.1 + 2, s.2) =
            ((2 * ((i + 1 : ℕ) : ℤ) + 1 : ℤ), (2 * (j : ℤ) + 1 : ℤ)) := by
          ext <;> dsimp only <;> omega
        refine Or.inr ?_
        rw [harr, hve, famPos_eq, if_neg hjp, hP, if_neg hjp]
        omega

/-- Every chain cell is connected to the empty cell in the arrow graph. -/
theorem fam_conn_of_mem (m t : ℕ) (C : Config (2 * m + 1)) (hCf : C.f = famF m t) (hm : 0 < m)
    (ht : 1 ≤ t)
    {s : Cell} (hs : s ∈ C.special) (hlt : famPos m s < t) : C.gConn s C.empty := by
  have key : ∀ p : ℕ, ∀ s : Cell, s ∈ C.special → famPos m s < t → famPos m s = p →
      C.gConn s C.empty := by
    intro p
    induction p using Nat.strong_induction_on with
    | _ p ih =>
      intro s hs hlt hp
      by_cases h0 : famPos m s = 0
      · rw [fam_eq_empty_of_pos_zero m t C hCf hm ht hs h0]
        exact Relation.ReflTransGen.refl
      · have hne : s ≠ C.empty := by
          intro hse
          rw [fam_empty m t C hCf hm ht] at hse
          rw [hse] at h0
          exact h0 (by
            have hE : ((2 * (m : ℤ) - 1 : ℤ), (1 : ℤ)) =
                ((2 * ((m - 1 : ℕ) : ℤ) + 1 : ℤ), (2 * ((0 : ℕ) : ℤ) + 1 : ℤ)) := by
              ext <;> dsimp only <;> omega
            rw [hE, famPos_eq]
            simp)
        have hA := (fam_arrow_snake m t C hCf hm ht hs h0).1 hlt
        have harr_special : C.arrow s ∈ C.special := C.arrow_mem_special hs hne hA.1
        have hadj : C.gAdj s (C.arrow s) := Or.inl ⟨hs, hne, rfl, hA.1⟩
        have hconn : C.gConn (C.arrow s) C.empty :=
          ih (famPos m s - 1) (by omega) (C.arrow s) harr_special (by omega) (by omega)
        exact Relation.ReflTransGen.head hadj hconn
  exact key (famPos m s) s hs hlt rfl

/-- The answer: every value `1 ≤ k ≤ m²` is achieved. -/
theorem family_achieves (m t : ℕ) (h1 : 1 ≤ t) (h2 : t ≤ m ^ 2) :
    ∃ C : Config (2 * m + 1), C.kval = t := by
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h
      simp at h2
      omega
    · exact h
  obtain ⟨C, hCf⟩ := famF_valid m t h1 h2
  use C
  rw [Config.kval_eq_comp_card]
  have hE0 : famPos m ((2 * (m : ℤ) - 1 : ℤ), (1 : ℤ)) = 0 := by
    have hE : ((2 * (m : ℤ) - 1 : ℤ), (1 : ℤ)) =
        ((2 * ((m - 1 : ℕ) : ℤ) + 1 : ℤ), (2 * ((0 : ℕ) : ℤ) + 1 : ℤ)) := by
      ext <;> dsimp only <;> omega
    rw [hE, famPos_eq]
    simp
  have closure : ∀ {a b : Cell}, C.gAdj a b → famPos m b < t → famPos m a < t := by
    intro a b hab hb
    have ha_special : a ∈ C.special := C.gAdj_left_special hab
    rcases hab with ⟨ha, hane, harr, hbb⟩ | ⟨hb', hbne, harr, haa⟩
    · by_cases h0 : famPos m a = 0
      · exfalso
        exact hane (fam_eq_empty_of_pos_zero m t C hCf hm h1 ha h0)
      · by_cases hlt : famPos m a < t
        · exact hlt
        · exfalso
          rcases (fam_arrow_snake m t C hCf hm h1 ha h0).2 hlt with hoff | hfw
          · rw [harr] at hoff
            exact hoff hbb
          · rw [harr] at hfw
            omega
    · have h0 : famPos m b ≠ 0 := by
        intro h0
        exact hbne (fam_eq_empty_of_pos_zero m t C hCf hm h1 hb' h0)
      by_cases hlt : famPos m b < t
      · have hA := (fam_arrow_snake m t C hCf hm h1 hb' h0).1 hlt
        rw [harr] at hA
        obtain ⟨-, hA2⟩ := hA
        omega
      · exact absurd hb hlt
  have hcomp_subset : C.comp ⊆ C.special.filter (fun s => famPos m s < t) := by
    intro s hs
    rw [Config.mem_comp] at hs
    rw [Finset.mem_filter]
    refine ⟨hs.1, ?_⟩
    have hbase : famPos m C.empty < t := by
      rw [fam_empty m t C hCf hm h1, hE0]
      exact h1
    have hg := hs.2
    clear hs
    have key : ∀ a b : Cell, C.gConn a b → famPos m b < t → famPos m a < t := by
      intro a b hab
      induction hab with
      | refl => exact id
      | tail _ hbc ih => exact fun h => ih (closure hbc h)
    exact key s C.empty hg hbase
  have hsubset2 : C.special.filter (fun s => famPos m s < t) ⊆ C.comp := by
    intro s hs
    rw [Finset.mem_filter] at hs
    rw [Config.mem_comp]
    exact ⟨hs.1, fam_conn_of_mem m t C hCf hm h1 hs.1 hs.2⟩
  have hcomp_eq : C.comp = C.special.filter (fun s => famPos m s < t) :=
    Finset.Subset.antisymm hcomp_subset hsubset2
  rw [hcomp_eq]
  have hbij : (C.special.filter (fun s => famPos m s < t)).card = (Finset.range t).card := by
    apply Finset.card_bij (fun s _ => famPos m s)
    · intro s hs
      rw [Finset.mem_filter] at hs
      exact Finset.mem_range.mpr hs.2
    · intro s₁ hs₁ s₂ hs₂ heq
      rw [Finset.mem_filter] at hs₁ hs₂
      have hf1 := (fam_special m t hCf hm h1).mp hs₁.1
      have hf2 := (fam_special m t hCf hm h1).mp hs₂.1
      obtain ⟨i₁, j₁, hi₁, hj₁, hc1⟩ := fam_odd_form hf1.1 hf1.2.1 hf1.2.2
      obtain ⟨i₂, j₂, hi₂, hj₂, hc2⟩ := fam_odd_form hf2.1 hf2.2.1 hf2.2.2
      have heq2 : famPos m ((2 * (i₁ : ℤ) + 1 : ℤ), (2 * (j₁ : ℤ) + 1 : ℤ)) =
          famPos m ((2 * (i₂ : ℤ) + 1 : ℤ), (2 * (j₂ : ℤ) + 1 : ℤ)) := by
        rw [← hc1, ← hc2]
        exact heq
      have hinj := famPos_inj m hi₁ hj₁ hi₂ hj₂ heq2
      rw [hc1, hc2, hinj.1, hinj.2]
    · intro p hp
      rw [Finset.mem_range] at hp
      have hpm : p < m ^ 2 := by omega
      obtain ⟨i, j, hi, hj, hce, hcp⟩ := famCell_eq m p hpm hm
      refine ⟨famCell m p, ?_, by rw [hce]; exact hcp⟩
      rw [Finset.mem_filter]
      refine ⟨?_, by rw [hce, hcp]; exact hp⟩
      rw [fam_special m t hCf hm h1, hce, mem_board]
      exact ⟨⟨by omega, by omega, by omega, by omega⟩, by omega, by omega⟩
  rw [hbij, Finset.card_range]

snip end

/-- The answer: `k(C)` can be any value in `{1, …, ((n-1)/2)²}` together
with the single large value `((n+1)/2)²`. -/
determine solution_set (n : ℕ) : Set ℕ :=
  { k | 1 ≤ k ∧ k ≤ ((n - 1) / 2) ^ 2 } ∪ { ((n + 1) / 2) ^ 2 }

problem usa2023_p3 (n : ℕ) (hn : Odd n) :
    { k : ℕ | ∃ C : Config n, Config.kval C = k } = solution_set n := by
  obtain ⟨m, hm⟩ := hn
  subst hm
  ext k
  simp only [solution_set, Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨C, hC⟩
    rcases Config.kval_upper C ⟨m, rfl⟩ with h | h
    · left
      rw [hC] at h
      exact ⟨by rw [← hC]; exact Config.kval_pos C, h⟩
    · right
      rw [hC] at h
      exact h
  · rintro (⟨h1, h2⟩ | h3)
    · obtain ⟨C, hC⟩ := family_achieves m k h1 (by
        have hm2 : (2 * m + 1 - 1) / 2 = m := by omega
        rw [hm2] at h2
        exact h2)
      exact ⟨C, hC⟩
    · obtain ⟨C, hC⟩ := Config.snake_achieves ⟨m, rfl⟩
      rw [h3]
      exact ⟨C, hC⟩

end Usa2023P3
