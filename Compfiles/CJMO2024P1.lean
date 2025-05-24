/-
Copyright (c) 2025 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib
import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# Canadian Junior Math Olympiad 2024, Problem 1

https://cms.math.ca/wp-content/uploads/2024/04/cjmo2024-solutions-en.pdf

Centuries ago, the pirate Captain Blackboard buried a vast amount of treasure in a single
cell of a 2 × 4 grid-structured island. You and your crew have reached the island and have
brought special treasure detectors to find the cell with the treasure. For each detector, you can
set it up to scan a specific subgrid [a, b]×[c, d] with 1 ≤ a ≤ b ≤ 2 and 1 ≤ c ≤ d ≤ 4. Running
the detector will tell you whether the treasure is in the region or not, though it cannot say
where in the region the treasure was detected. You plan on setting up Q detectors, which may
only be run simultaneously after all Q detectors are ready. What is the minimum Q required
to guarantee your crew can determine the location of Blackboard’s legendary treasure?
-/

open Set

/-- A single cell of the `2 × 4` grid.
    We index rows with `Fin 2` and columns with `Fin 4`. -/
abbrev Cell : Type := Fin 2 × Fin 4

/-- An *axis-aligned detector*, defined by the set of cells it scans.
    (The usual rectangle parameters `[a,b] × [c,d]` are implicit in this set.) -/
structure Detector where
  cells : Finset Cell

namespace Detector

/-- Construct a detector from row bounds `a ≤ b` and column bounds `c ≤ d`. -/
def ofBounds
    (a b : Fin 2)
    (c d : Fin 4)
: Detector where
  cells := { p : Cell | a ≤ p.1 ∧ p.1 ≤ b ∧ c ≤ p.2 ∧ p.2 ≤ d }

end Detector

/-- The outcome vector produced by *Q* detectors for a hidden treasure cell. -/
def outcome {Q : ℕ} (D : Fin Q → Detector) (treasure : Cell) : List.Vector Bool Q :=
  List.Vector.ofFn (fun i ↦ treasure ∈ (D i).cells)

/-- A family of detectors *distinguishes* every treasure location
    if distinct cells yield distinct outcome vectors. -/
def Distinguishes {Q : ℕ} (D : Fin Q → Detector) : Prop :=
  ∀ {c₁ c₂ : Cell}, c₁ ≠ c₂ → outcome D c₁ ≠ outcome D c₂

/-- The minimum number of non-adaptive detectors needed to guarantee
    the treasure cell can be identified. -/
noncomputable def minQ : ℕ :=
  sInf {Q : ℕ | ∃ D : Fin Q → Detector, Distinguishes D}

def D (i : Fin 3): Detector :=
  match i with
  | 0 => Detector.ofBounds 0 0 0 3 -- first detector covers first row
    -- ┌───┬───┬───┬───┐
    -- │ X │ X │ X │ X │  (covers entire first row)
    -- ├───┼───┼───┼───┤
    -- │   │   │   │   │
    -- └───┴───┴───┴───┘
  | 1 => Detector.ofBounds 0 1 0 1 -- second detector covers first two colums
    -- ┌───┬───┬───┬───┐
    -- │ X │ X │   │   │  (covers first two columns of both rows)
    -- ├───┼───┼───┼───┤
    -- │ X │ X │   │   │
    -- └───┴───┴───┴───┘
  | 2 => Detector.ofBounds 0 1 1 2 -- third detector covers middle
    -- ┌───┬───┬───┬───┐
    -- │   │ X │ X │   │  (covers middle two columns of both rows)
    -- ├───┼───┼───┼───┤
    -- │   │ X │ X │   │
    -- └───┴───┴───┴───┘

lemma D_distinguishes : Distinguishes D := by
  intro c₁ c₂ h
  fin_cases c₁ <;> fin_cases c₂ <;>
  first | decide | exfalso; simp at h

noncomputable determine solution : ℕ := 3

/-- Exactly three detectors are necessary and sufficient to localize the treasure. -/
problem cjmo2024_p1 : minQ = solution := by
  have : minQ ≤ 3 := by
    unfold minQ
    apply Nat.sInf_le
    use D
    exact D_distinguishes

  have card_cell : Nat.card Cell = 8 := by simp
  have card_vec_2 : Nat.card (List.Vector Bool 2) = 4 := by simp

  have : 2 ∉ {Q : ℕ | ∃ D : Fin Q → Detector, Distinguishes D} := by
    intro h
    rcases h with ⟨D, hD⟩
    unfold Distinguishes at hD
    have : Set.InjOn (outcome D) ⊤ := by
      intro p _ q _ h
      cases (eq_or_ne p q)
      case inl h => exact h
      case inr h' =>
        specialize hD h'
        exact False.elim (hD h)

    have outcode_inj : Function.Injective (outcome D) := by
      intro p q h
      cases (eq_or_ne p q)
      case inl h => exact h
      case inr h' =>
        specialize hD h'
        exact False.elim (hD h)

    have prereq : (Nat.card (List.Vector Bool 2) = 0 → Nat.card Cell = 0) := by
      intro h
      rw [card_vec_2] at h
      exfalso
      norm_num at h

    have test3 := Finite.card_le_of_injective' outcode_inj prereq

    rw [card_cell] at test3
    rw [show Nat.card (List.Vector Bool 2) = 4 by simp] at test3

    linarith

  sorry
