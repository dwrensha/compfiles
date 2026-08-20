/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Data.Int.Star
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 2014, Problem 4

Let k be a positive integer. Two players A and B play a game on an infinite
grid of regular hexagons. Initially all the grid cells are empty. Then the
players alternately take turns with A moving first. In her move, A may choose
two adjacent hexagons in the grid which are empty and place a counter in both
of them. In his move, B may choose any counter on the board and remove it.
If at any time there are k consecutive grid cells in a line all of which
contain a counter, A wins. Find the minimum value of k for which A cannot
win in a finite number of moves, or prove that no such minimum value exists.
-/

namespace Usa2014P4

/-- A cell of the hexagonal grid, given in axial coordinates. -/
abbrev Cell := ℤ × ℤ

/-- The six unit steps between adjacent cells of the grid. -/
def offsets : Finset Cell := {(1, 0), (-1, 0), (0, 1), (0, -1), (1, -1), (-1, 1)}

/-- Two cells are adjacent when their difference is one of the six unit steps. -/
def Adj (c d : Cell) : Prop := (d.1 - c.1, d.2 - c.2) ∈ offsets

instance (c d : Cell) : Decidable (Adj c d) := by
  unfold Adj
  infer_instance

/-- The three (undirected) line directions of the grid. -/
def Dirs : Finset Cell := {(1, 0), (0, 1), (1, -1)}

/-- The cell reached from `p` by making `i` steps in direction `d`. -/
def step (p : Cell) (d : Cell) (i : ℕ) : Cell := (p.1 + (i : ℤ) * d.1, p.2 + (i : ℤ) * d.2)

/-- `A` has won on the board `s`: some line of `k` consecutive cells all carry
a counter. -/
def Winning (k : ℕ) (s : Finset Cell) : Prop :=
  ∃ d ∈ Dirs, ∃ p : Cell, ∀ i : ℕ, i < k → step p d i ∈ s

/-- A move of player `A`: place counters on two empty adjacent cells. -/
def AMove (s s' : Finset Cell) : Prop :=
  ∃ c₁ c₂ : Cell, c₁ ≠ c₂ ∧ Adj c₁ c₂ ∧ c₁ ∉ s ∧ c₂ ∉ s ∧ s' = insert c₁ (insert c₂ s)

/-- A move of player `B`: remove one counter from the board. -/
def BMove (s t : Finset Cell) : Prop := ∃ c ∈ s, t = s.erase c

/-- `AForce k s` means that from the board `s`, with `A` to move, `A` can force
a win in finitely many moves regardless of how `B` plays.  Since the witness is
an inductive tree covering all of `B`'s responses, every play following the
strategy ends in a win after finitely many moves. -/
inductive AForce (k : ℕ) : Finset Cell → Prop
  | of_win {s s'} : AMove s s' → Winning k s' → AForce k s
  | of_step {s s'} : AMove s s' → (∀ t, BMove s' t → AForce k t) → AForce k s

/-- `A` can win the game with parameter `k` in finitely many moves. -/
def ACanWin (k : ℕ) : Prop := AForce k ∅

snip begin

/-! ### The defense strategy of `B` for `k = 6` -/

/-- The shading of the grid used in `B`'s defense strategy for `k = 6`:
every third cell is shaded. -/
def shaded (c : Cell) : Prop := (c.1 - c.2) % 3 = 0

/-- Membership in `offsets` as an explicit case distinction. -/
lemma mem_offsets {v : Cell} :
    v ∈ offsets ↔ v = (1, 0) ∨ v = (-1, 0) ∨ v = (0, 1) ∨ v = (0, -1) ∨
      v = (1, -1) ∨ v = (-1, 1) := by
  unfold offsets
  simp only [Finset.mem_insert, Finset.mem_singleton]

/-- Membership in `Dirs` as an explicit case distinction. -/
lemma mem_Dirs {v : Cell} : v ∈ Dirs ↔ v = (1, 0) ∨ v = (0, 1) ∨ v = (1, -1) := by
  unfold Dirs
  simp only [Finset.mem_insert, Finset.mem_singleton]

/-- Adjacent cells are never both shaded: adjacent cells have different colors. -/
lemma adj_not_both_shaded {c d : Cell} (h : Adj c d) : ¬ (shaded c ∧ shaded d) := by
  unfold Adj at h; rw [mem_offsets] at h; unfold shaded
  rcases h with h | h | h | h | h | h <;> obtain ⟨h1, h2⟩ := Prod.ext_iff.mp h <;> lia

/-- The cells of a line are distinct. -/
lemma step_eq_of_eq {d : Cell} (hd : d ∈ Dirs) (p : Cell) {i j : ℕ}
    (h : step p d i = step p d j) : i = j := by
  rw [mem_Dirs] at hd; unfold step at h
  rcases hd with rfl | rfl | rfl <;> simp_all

/-- Any six consecutive cells in a line contain two distinct shaded cells. -/
lemma two_shaded_of_line {d : Cell} (hd : d ∈ Dirs) (p : Cell) :
    ∃ i j : ℕ, i < 6 ∧ j < 6 ∧
      shaded (step p d i) ∧ shaded (step p d j) ∧ step p d i ≠ step p d j := by
  have hδ : d.1 - d.2 = 1 ∨ d.1 - d.2 = -1 ∨ d.1 - d.2 = 2 := by
    rw [mem_Dirs] at hd; rcases hd with rfl | rfl | rfl <;> norm_num
  have e : ∀ i : ℕ, (step p d i).1 - (step p d i).2
      = (p.1 - p.2) + (i : ℤ) * (d.1 - d.2) := fun i => by unfold step; ring
  set i₀ := ((-((p.1 - p.2)) * (d.1 - d.2)) % 3).toNat with hi₀
  have hi₀z : (i₀ : ℤ) = (-(p.1 - p.2) * (d.1 - d.2)) % 3 :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))
  have hi₀lt : i₀ < 3 := by
    have h1 : 0 ≤ (-(p.1 - p.2) * (d.1 - d.2)) % 3 := Int.emod_nonneg _ (by norm_num)
    have h2 : (-(p.1 - p.2) * (d.1 - d.2)) % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
    lia
  refine ⟨i₀, i₀ + 3, by lia, by lia, ?_, ?_, ?_⟩
  · unfold shaded; rw [e]; rcases hδ with hδ | hδ | hδ <;> rw [hδ] at hi₀z ⊢ <;> lia
  · unfold shaded; rw [e]; rcases hδ with hδ | hδ | hδ <;> rw [hδ] at hi₀z ⊢ <;> lia
  · intro hcontra
    have := step_eq_of_eq hd p hcontra
    lia

/-- Player `B` has a strategy preventing `A` from ever getting six consecutive
cells in a line: `B` always removes a counter on a shaded cell. -/
theorem not_ACanWin_six : ¬ ACanWin 6 := by
  suffices key : ∀ s : Finset Cell, AForce 6 s → (∀ c ∈ s, ¬ shaded c) → False by
    exact fun h => key ∅ h (fun c hc => by simp at hc)
  intro s h
  induction h
  case of_win s s' m w =>
    intro Ps
    obtain ⟨c₁, c₂, hne, hadj, h1, h2, rfl⟩ := m
    obtain ⟨d, hd, p, hline⟩ := w
    obtain ⟨i, j, hi, hj, shi, shj, hneij⟩ := two_shaded_of_line hd p
    have hmi := hline i hi
    have hmj := hline j hj
    have hi' : step p d i = c₁ ∨ step p d i = c₂ := by
      rw [Finset.mem_insert, Finset.mem_insert] at hmi
      rcases hmi with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact (Ps _ h shi).elim
    have hj' : step p d j = c₁ ∨ step p d j = c₂ := by
      rw [Finset.mem_insert, Finset.mem_insert] at hmj
      rcases hmj with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact (Ps _ h shj).elim
    rcases hi' with rfl | rfl <;> rcases hj' with hjj | hjj
    · exact absurd hjj.symm hneij
    · exact absurd ⟨shi, hjj ▸ shj⟩ (adj_not_both_shaded hadj)
    · exact absurd ⟨hjj ▸ shj, shi⟩ (adj_not_both_shaded hadj)
    · exact absurd hjj.symm hneij
  case of_step s s' m h ih =>
    intro Ps
    obtain ⟨c₁, c₂, hne, hadj, h1, h2, rfl⟩ := m
    by_cases hs1 : shaded c₁
    · -- `B` removes the shaded counter `c₁`.
      have hs2 : ¬ shaded c₂ := fun hh => adj_not_both_shaded hadj ⟨hs1, hh⟩
      have hmem : c₁ ∈ insert c₁ (insert c₂ s) := by simp
      have herase : (insert c₁ (insert c₂ s)).erase c₁ = insert c₂ s :=
        Finset.erase_insert (by simp [hne, h1])
      exact ih (insert c₂ s) ⟨c₁, hmem, herase.symm⟩ (by
        intro c hc
        rw [Finset.mem_insert] at hc
        rcases hc with rfl | hc
        · exact hs2
        · exact Ps c hc)
    · by_cases hs2 : shaded c₂
      · -- `B` removes the shaded counter `c₂`.
        have hs1' : ¬ shaded c₁ := fun hh => adj_not_both_shaded hadj ⟨hh, hs2⟩
        have hmem : c₂ ∈ insert c₁ (insert c₂ s) := by simp
        have herase : (insert c₁ (insert c₂ s)).erase c₂ = insert c₁ s := by
          rw [Finset.erase_insert_of_ne hne, Finset.erase_insert h2]
        exact ih (insert c₁ s) ⟨c₂, hmem, herase.symm⟩ (by
          intro c hc
          rw [Finset.mem_insert] at hc
          rcases hc with rfl | hc
          · exact hs1'
          · exact Ps c hc)
      · -- `A` covered no shaded cell; `B` removes an arbitrary counter.
        exact ih (insert c₂ s) ⟨c₁, by simp, Finset.erase_insert (by simp [hne, h1]) |>.symm⟩
          (by
            intro c hc
            rw [Finset.mem_insert] at hc
            rcases hc with rfl | hc
            · exact hs2
            · exact Ps c hc)

/-! ### Transport of winning strategies along grid symmetries -/

/-- A line traversed in the opposite direction is still a line. -/
lemma winning_of_neg {k : ℕ} {s : Finset Cell} {d : Cell} (hd : d ∈ Dirs) {p : Cell}
    (h : ∀ i : ℕ, i < k → step p (-d) i ∈ s) : Winning k s := by
  rcases k with _ | k
  · exact ⟨d, hd, p, fun i hi => by lia⟩
  · refine ⟨d, hd, step p (-d) k, fun i hi => ?_⟩
    have hneg : (-d : Cell) = (-d.1, -d.2) := rfl
    have e : step (step p (-d) k) d i = step p (-d) (k - i) := by
      rw [hneg, Prod.ext_iff]
      unfold step
      rw [Nat.cast_sub (by lia : i ≤ k)]
      exact ⟨by ring, by ring⟩
    rw [e]
    exact h (k - i) (by lia)

/-- Generic transport of `AForce` along a map preserving the game structure. -/
lemma AForce_image {k : ℕ} {φ : Cell → Cell} (hφ : Function.Injective φ)
    (hφ_adj : ∀ c d, Adj (φ c) (φ d) ↔ Adj c d)
    (hφ_win : ∀ s, Winning k s → Winning k (s.image φ))
    {s : Finset Cell} (h : AForce k s) : AForce k (s.image φ) := by
  induction h
  case of_win s s' m w =>
    obtain ⟨c₁, c₂, hne, hadj, h1, h2, rfl⟩ := m
    have m' : AMove (s.image φ) (insert (φ c₁) (insert (φ c₂) (s.image φ))) := by
      refine ⟨φ c₁, φ c₂, fun h => hne (hφ h), (hφ_adj c₁ c₂).mpr hadj, ?_, ?_, rfl⟩
      · intro hmem
        obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hmem
        exact h1 (hφ hxy ▸ hx)
      · intro hmem
        obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hmem
        exact h2 (hφ hxy ▸ hx)
    apply AForce.of_win m'
    rw [← Finset.image_insert, ← Finset.image_insert]
    exact hφ_win _ w
  case of_step s s' m h ih =>
    obtain ⟨c₁, c₂, hne, hadj, h1, h2, rfl⟩ := m
    have m' : AMove (s.image φ) (insert (φ c₁) (insert (φ c₂) (s.image φ))) := by
      refine ⟨φ c₁, φ c₂, fun h => hne (hφ h), (hφ_adj c₁ c₂).mpr hadj, ?_, ?_, rfl⟩
      · intro hmem
        obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hmem
        exact h1 (hφ hxy ▸ hx)
      · intro hmem
        obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hmem
        exact h2 (hφ hxy ▸ hx)
    refine AForce.of_step m' ?_
    intro t' ht'
    obtain ⟨c', hc', rfl⟩ := ht'
    rw [Finset.mem_insert, Finset.mem_insert] at hc'
    have hc : ∃ c ∈ insert c₁ (insert c₂ s), φ c = c' := by
      rcases hc' with rfl | rfl | hmem
      · exact ⟨c₁, by simp, rfl⟩
      · exact ⟨c₂, by simp, rfl⟩
      · obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hmem
        exact ⟨x, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx), hxy⟩
    obtain ⟨c, hc, rfl⟩ := hc
    rw [← Finset.image_insert, ← Finset.image_insert, ← Finset.image_erase hφ]
    exact ih _ ⟨c, hc, rfl⟩

/-- Rotation by 60 degrees about the origin. -/
def rot (c : Cell) : Cell := (-c.2, c.1 + c.2)

lemma rot_injective : Function.Injective rot := by
  intro c d h
  unfold rot at h
  rw [Prod.ext_iff] at h
  obtain ⟨h1, h2⟩ := h
  have : c.2 = d.2 := by lia
  have : c.1 = d.1 := by lia
  exact Prod.ext ‹_› ‹_›

lemma adj_rot {c d : Cell} : Adj (rot c) (rot d) ↔ Adj c d := by
  have hset : offsets.image rot = offsets := by decide
  have hlin : ((rot d).1 - (rot c).1, (rot d).2 - (rot c).2)
      = rot (d.1 - c.1, d.2 - c.2) := by
    rw [Prod.ext_iff]; unfold rot; exact ⟨by ring, by ring⟩
  unfold Adj
  rw [hlin]
  constructor
  · intro h
    rw [← hset] at h
    obtain ⟨w, hw, hwv⟩ := Finset.mem_image.mp h
    rwa [rot_injective hwv] at hw
  · intro h
    rw [← hset]
    exact Finset.mem_image.mpr ⟨_, h, rfl⟩

lemma step_rot (p d : Cell) (i : ℕ) : step (rot p) (rot d) i = rot (step p d i) := by
  rw [Prod.ext_iff]; unfold step rot; exact ⟨by ring, by ring⟩

lemma winning_rot {k : ℕ} {s : Finset Cell} (h : Winning k s) : Winning k (s.image rot) := by
  obtain ⟨d, hd, p, hline⟩ := h
  rw [mem_Dirs] at hd
  rcases hd with rfl | rfl | rfl
  · refine ⟨(0, 1), by simp [Dirs], rot p, fun i hi => ?_⟩
    have h1 : (0, 1) = rot (1, 0) := by decide
    rw [h1, step_rot]
    exact Finset.mem_image.mpr ⟨_, hline i hi, rfl⟩
  · apply winning_of_neg (d := (1, -1)) (by simp [Dirs]) (p := rot p)
    intro i hi
    have h1 : (-(1, -1) : Cell) = rot (0, 1) := by decide
    have h2 : step (rot p) (-(1, -1)) i = rot (step p (0, 1) i) := by rw [h1, step_rot]
    rw [h2]
    exact Finset.mem_image.mpr ⟨_, hline i hi, rfl⟩
  · refine ⟨(1, 0), by simp [Dirs], rot p, fun i hi => ?_⟩
    have h1 : (1, 0) = rot (1, -1) := by decide
    rw [h1, step_rot]
    exact Finset.mem_image.mpr ⟨_, hline i hi, rfl⟩

lemma AForce_image_rot {k : ℕ} {s : Finset Cell} (h : AForce k s) :
    AForce k (s.image rot) :=
  AForce_image rot_injective (fun _ _ => adj_rot) (fun _ h => winning_rot h) h

/-- Rotation by an arbitrary multiple of 60 degrees. -/
lemma AForce_image_rotpow {k : ℕ} {s : Finset Cell} (j : ℕ) (h : AForce k s) :
    AForce k (s.image (rot^[j])) := by
  induction j with
  | zero => simpa using h
  | succ j ihj =>
    rw [Function.iterate_succ', ← Finset.image_image]
    exact AForce_image_rot ihj

/-- Translation by a fixed cell. -/
def transl (t : Cell) (c : Cell) : Cell := (c.1 + t.1, c.2 + t.2)

lemma transl_injective (t : Cell) : Function.Injective (transl t) := by
  intro c d h
  unfold transl at h
  rw [Prod.ext_iff] at h ⊢
  lia

lemma adj_transl (t : Cell) {c d : Cell} : Adj (transl t c) (transl t d) ↔ Adj c d := by
  have hlin : ((transl t d).1 - (transl t c).1, (transl t d).2 - (transl t c).2)
      = (d.1 - c.1, d.2 - c.2) := by
    rw [Prod.ext_iff]; unfold transl; exact ⟨by ring, by ring⟩
  unfold Adj
  rw [hlin]

lemma step_transl (t p d : Cell) (i : ℕ) : step (transl t p) d i = transl t (step p d i) := by
  rw [Prod.ext_iff]; unfold step transl; exact ⟨by ring, by ring⟩

lemma winning_transl {k : ℕ} (t : Cell) {s : Finset Cell} (h : Winning k s) :
    Winning k (s.image (transl t)) := by
  obtain ⟨d, hd, p, hline⟩ := h
  exact ⟨d, hd, transl t p, fun i hi => by
    rw [step_transl]; exact Finset.mem_image.mpr ⟨_, hline i hi, rfl⟩⟩

lemma AForce_image_transl {k : ℕ} (t : Cell) {s : Finset Cell} (h : AForce k s) :
    AForce k (s.image (transl t)) :=
  AForce_image (transl_injective t) (fun _ _ => adj_transl t) (fun _ h => winning_transl t h) h

/-- The point reflection swapping the two distinguished cells `x₀ = (1, 0)` and
`y₀ = (4, 0)` of the strategy below. -/
def mirror (c : Cell) : Cell := (5 - c.1, -c.2)

lemma mirror_injective : Function.Injective mirror := by
  intro c d h
  unfold mirror at h
  rw [Prod.ext_iff] at h ⊢
  lia

lemma adj_mirror {c d : Cell} : Adj (mirror c) (mirror d) ↔ Adj c d := by
  have hset : offsets.image (fun v : Cell => (-v.1, -v.2)) = offsets := by decide
  have hlin : ((mirror d).1 - (mirror c).1, (mirror d).2 - (mirror c).2)
      = (-(d.1 - c.1), -(d.2 - c.2)) := by
    rw [Prod.ext_iff]; unfold mirror; exact ⟨by ring, by ring⟩
  unfold Adj
  rw [hlin]
  constructor
  · intro h
    rw [← hset] at h
    obtain ⟨w, hw, hwv⟩ := Finset.mem_image.mp h
    have : w = (d.1 - c.1, d.2 - c.2) := by
      rw [Prod.ext_iff] at hwv ⊢
      simp_all
      lia
    rwa [this] at hw
  · intro h
    rw [← hset]
    exact Finset.mem_image.mpr ⟨_, h, rfl⟩

lemma winning_mirror {k : ℕ} {s : Finset Cell} (h : Winning k s) :
    Winning k (s.image mirror) := by
  obtain ⟨d, hd, p, hline⟩ := h
  apply winning_of_neg hd (p := mirror p)
  intro i hi
  have hneg : (-d : Cell) = (-d.1, -d.2) := rfl
  have e : step (mirror p) (-d) i = mirror (step p d i) := by
    rw [hneg, Prod.ext_iff]
    unfold step mirror
    exact ⟨by ring, by ring⟩
  rw [e]
  exact Finset.mem_image.mpr ⟨_, hline i hi, rfl⟩

lemma AForce_image_mirror {k : ℕ} {s : Finset Cell} (h : AForce k s) :
    AForce k (s.image mirror) :=
  AForce_image mirror_injective (fun _ _ => adj_mirror) (fun _ h => winning_mirror h) h

/-! ### The winning strategy of `A` for `k = 5`

The strategy follows the official solution: after establishing counters at the
distinguished cells `x₀ = (1, 0)` and `y₀ = (4, 0)` (with further counters at
`(0, 0)` and `(5, 0)` on the same line), `A` keeps replacing whichever of
`x₀`, `y₀` player `B` removes and fills one more neighbor slot each round,
until one of the two cells is completely surrounded, which produces an
unstoppable double threat. -/

/-- The first distinguished cell of the strategy. -/
def x₀ : Cell := (1, 0)

/-- The second distinguished cell of the strategy. -/
def y₀ : Cell := (4, 0)

/-- The neighbor slots of `x₀` (other than `(0, 0)` and the central cell `(2, 0)`)
that the strategy fills one by one. -/
def xSlots : Finset Cell := {(1, 1), (0, 1), (1, -1), (2, -1)}

/-- The neighbor slots of `y₀` (other than `(5, 0)` and the central cell `(3, 0)`)
that the strategy fills one by one. -/
def ySlots : Finset Cell := {(4, 1), (3, 1), (4, -1), (5, -1)}

/-- Five consecutive cells on the first axis give a win. -/
lemma winning_row0 (a : ℤ) {t : Finset Cell}
    (h0 : (a, 0) ∈ t) (h1 : (a + 1, 0) ∈ t) (h2 : (a + 2, 0) ∈ t)
    (h3 : (a + 3, 0) ∈ t) (h4 : (a + 4, 0) ∈ t) : Winning 5 t := by
  refine ⟨(1, 0), by decide, (a, 0), fun i hi => ?_⟩
  interval_cases i
  · rw [show step (a, 0) (1, 0) 0 = (a, 0) by simp [step]]
    exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

/-- The diagonal line through `(1, 1)` in direction `(1, -1)`. -/
lemma winning_diag {t : Finset Cell}
    (h0 : (1, 1) ∈ t) (h1 : (2, 0) ∈ t) (h2 : (3, -1) ∈ t)
    (h3 : (4, -2) ∈ t) (h4 : (5, -3) ∈ t) : Winning 5 t := by
  refine ⟨(1, -1), by decide, (1, 1), fun i hi => ?_⟩
  interval_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

/-- Completing the first five cells of row 0 wins immediately. -/
lemma win_now0 {s : Finset Cell} (h2 : (2, 0) ∉ s) (h3 : (3, 0) ∉ s)
    (h0 : (0, 0) ∈ s) (h1 : x₀ ∈ s) (h4 : y₀ ∈ s) : AForce 5 s := by
  apply AForce.of_win (s' := insert (2, 0) (insert (3, 0) s))
  · exact ⟨(2, 0), (3, 0), by decide, by decide, h2, h3, rfl⟩
  · apply winning_row0 0
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h0)
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h1)
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h4)

/-- Completing the cells `(1, 0)` to `(5, 0)` of row 0 wins immediately. -/
lemma win_now1 {s : Finset Cell} (h2 : (2, 0) ∉ s) (h3 : (3, 0) ∉ s)
    (h1 : x₀ ∈ s) (h4 : y₀ ∈ s) (h5 : (5, 0) ∈ s) : AForce 5 s := by
  apply AForce.of_win (s' := insert (2, 0) (insert (3, 0) s))
  · exact ⟨(2, 0), (3, 0), by decide, by decide, h2, h3, rfl⟩
  · apply winning_row0 1
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h1)
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h4)
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h5)

/-- The endgame position with `x₀` completely surrounded and filled: whatever
counter `B` removes, `A` wins. -/
lemma endgame_x_Bturn (Ny : Finset Cell) (hNy : Ny ⊆ ySlots) :
    ∀ t, BMove ({(0, 0), (5, 0)} ∪ xSlots ∪ Ny ∪ {(2, 0), x₀, y₀}) t → AForce 5 t := by
  intro t ht
  obtain ⟨c, hc, rfl⟩ := ht
  set S := ({(0, 0), (5, 0)} ∪ xSlots ∪ Ny ∪ {(2, 0), x₀, y₀} : Finset Cell) with hS
  have h00 : (0, 0) ∈ S := by simp [hS]
  have h50 : (5, 0) ∈ S := by simp [hS]
  have h20 : (2, 0) ∈ S := by simp [hS]
  have hx₀ : x₀ ∈ S := by simp [hS]
  have hy₀ : y₀ ∈ S := by simp [hS]
  have h11 : (1, 1) ∈ S := by simp [hS, xSlots]
  have h30n : (3, 0) ∉ S := by
    have h1 : (3, 0) ∉ ySlots := by decide
    have h2 : (3, 0) ∉ Ny := fun h => h1 (hNy h)
    simp [hS, h2, xSlots, x₀, y₀]
  have h31n : (3, -1) ∉ S := by
    have h1 : (3, -1) ∉ ySlots := by decide
    have h2 : (3, -1) ∉ Ny := fun h => h1 (hNy h)
    simp [hS, h2, xSlots, x₀, y₀]
  have h21n : (2, 1) ∉ S := by
    have h1 : (2, 1) ∉ ySlots := by decide
    have h2 : (2, 1) ∉ Ny := fun h => h1 (hNy h)
    simp [hS, h2, xSlots, x₀, y₀]
  have h60n : (6, 0) ∉ S := by
    have h1 : (6, 0) ∉ ySlots := by decide
    have h2 : (6, 0) ∉ Ny := fun h => h1 (hNy h)
    simp [hS, h2, xSlots, x₀, y₀]
  have h70n : (7, 0) ∉ S := by
    have h1 : (7, 0) ∉ ySlots := by decide
    have h2 : (7, 0) ∉ Ny := fun h => h1 (hNy h)
    simp [hS, h2, xSlots, x₀, y₀]
  have h42n : (4, -2) ∉ S := by
    have h1 : (4, -2) ∉ ySlots := by decide
    have h2 : (4, -2) ∉ Ny := fun h => h1 (hNy h)
    simp [hS, h2, xSlots, x₀, y₀]
  have h53n : (5, -3) ∉ S := by
    have h1 : (5, -3) ∉ ySlots := by decide
    have h2 : (5, -3) ∉ Ny := fun h => h1 (hNy h)
    simp [hS, h2, xSlots, x₀, y₀]
  rw [hS, Finset.mem_union, Finset.mem_union, Finset.mem_union] at hc
  rcases hc with ((hb | hx) | hn) | hce
  · -- `B` removes a base cell: `A` plays `(3, 0)`, `(2, 1)` and completes row 0.
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl
    · -- `c = (0, 0)`: complete the line `(1, 0)`–`(5, 0)`.
      have h3 : (3, 0) ∉ S.erase (0, 0) := fun h => h30n (Finset.mem_of_mem_erase h)
      have h21 : (2, 1) ∉ S.erase (0, 0) := fun h => h21n (Finset.mem_of_mem_erase h)
      have m : AMove (S.erase (0, 0)) (insert (3, 0) (insert (2, 1) (S.erase (0, 0)))) :=
        ⟨(3, 0), (2, 1), by decide, by decide, h3, h21, rfl⟩
      apply AForce.of_win m
      apply winning_row0 1
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨by decide, hx₀⟩))
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨by decide, h20⟩))
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨by decide, hy₀⟩))
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨by decide, h50⟩))
    · -- `c = (5, 0)`: complete the line `(0, 0)`–`(4, 0)`.
      have h3 : (3, 0) ∉ S.erase (5, 0) := fun h => h30n (Finset.mem_of_mem_erase h)
      have h21 : (2, 1) ∉ S.erase (5, 0) := fun h => h21n (Finset.mem_of_mem_erase h)
      have m : AMove (S.erase (5, 0)) (insert (3, 0) (insert (2, 1) (S.erase (5, 0)))) :=
        ⟨(3, 0), (2, 1), by decide, by decide, h3, h21, rfl⟩
      apply AForce.of_win m
      apply winning_row0 0
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨by decide, h00⟩))
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨by decide, hx₀⟩))
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨by decide, h20⟩))
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨by decide, hy₀⟩))
  · -- `B` removes a neighbor of `x₀`: `A` plays `(3, 0)`, `(2, 1)`, line `(0, 0)`–`(4, 0)`.
    have hne : ∀ w : Cell, w ∉ xSlots → w ≠ c := fun w hw heq => hw (heq ▸ hx)
    have h3 : (3, 0) ∉ S.erase c := fun h => h30n (Finset.mem_of_mem_erase h)
    have h21 : (2, 1) ∉ S.erase c := fun h => h21n (Finset.mem_of_mem_erase h)
    have m : AMove (S.erase c) (insert (3, 0) (insert (2, 1) (S.erase c))) :=
      ⟨(3, 0), (2, 1), by decide, by decide, h3, h21, rfl⟩
    apply AForce.of_win m
    apply winning_row0 0
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨hne _ (by decide), h00⟩))
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨hne _ (by decide), hx₀⟩))
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨hne _ (by decide), h20⟩))
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨hne _ (by decide), hy₀⟩))
  · -- `B` removes a neighbor of `y₀`: same answer.
    have hne : ∀ w : Cell, w ∉ ySlots → w ≠ c := fun w hw heq => hw (heq ▸ hNy hn)
    have h3 : (3, 0) ∉ S.erase c := fun h => h30n (Finset.mem_of_mem_erase h)
    have h21 : (2, 1) ∉ S.erase c := fun h => h21n (Finset.mem_of_mem_erase h)
    have m : AMove (S.erase c) (insert (3, 0) (insert (2, 1) (S.erase c))) :=
      ⟨(3, 0), (2, 1), by decide, by decide, h3, h21, rfl⟩
    apply AForce.of_win m
    apply winning_row0 0
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨hne _ (by decide), h00⟩))
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨hne _ (by decide), hx₀⟩))
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨hne _ (by decide), h20⟩))
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨hne _ (by decide), hy₀⟩))
  · -- `B` removes `(2, 0)`, `x₀` or `y₀`.
    simp only [Finset.mem_insert, Finset.mem_singleton] at hce
    rcases hce with rfl | rfl | rfl
    · -- `c = (2, 0)`: `A` refills it and completes row 0.
      have m : AMove (S.erase (2, 0)) (insert (2, 0) (insert (3, 0) (S.erase (2, 0)))) :=
        ⟨(2, 0), (3, 0), by decide, by decide, (by simp),
          (fun h => h30n (Finset.mem_of_mem_erase h)), rfl⟩
      apply AForce.of_win m
      apply winning_row0 0
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨by decide, h00⟩))
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨by decide, hx₀⟩))
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨by decide, hy₀⟩))
    · -- `c = x₀`: `A` plays the green pair `(3, 0)`, `(3, -1)`, creating a double threat.
      have h3 : (3, 0) ∉ S.erase x₀ := fun h => h30n (Finset.mem_of_mem_erase h)
      have h31 : (3, -1) ∉ S.erase x₀ := fun h => h31n (Finset.mem_of_mem_erase h)
      have m : AMove (S.erase x₀) (insert (3, 0) (insert (3, -1) (S.erase x₀))) :=
        ⟨(3, 0), (3, -1), by decide, by decide, h3, h31, rfl⟩
      apply AForce.of_step m
      intro u hu
      obtain ⟨v, hv, rfl⟩ := hu
      -- facts about the two possible answers
      have hT6 : (6, 0) ∉ insert (3, 0) (insert (3, -1) (S.erase x₀)) := by
        simp [Finset.mem_insert, Finset.mem_erase, h60n, x₀]
      have hT7 : (7, 0) ∉ insert (3, 0) (insert (3, -1) (S.erase x₀)) := by
        simp [Finset.mem_insert, Finset.mem_erase, h70n, x₀]
      have hT42 : (4, -2) ∉ insert (3, 0) (insert (3, -1) (S.erase x₀)) := by
        simp [Finset.mem_insert, Finset.mem_erase, h42n, x₀]
      have hT53 : (5, -3) ∉ insert (3, 0) (insert (3, -1) (S.erase x₀)) := by
        simp [Finset.mem_insert, Finset.mem_erase, h53n, x₀]
      rw [Finset.mem_insert, Finset.mem_insert] at hv
      rcases hv with rfl | rfl | hv
      · -- `v = (3, 0)`: the top diagonal threat wins.
        have m2 : AMove ((insert (3, 0) (insert (3, -1) (S.erase x₀))).erase (3, 0))
            (insert (4, -2) (insert (5, -3)
              ((insert (3, 0) (insert (3, -1) (S.erase x₀))).erase (3, 0)))) :=
          ⟨(4, -2), (5, -3), by decide, by decide,
            (fun h => hT42 (Finset.mem_of_mem_erase h)),
            (fun h => hT53 (Finset.mem_of_mem_erase h)), rfl⟩
        apply AForce.of_win m2
        apply winning_diag
        · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
            (Finset.mem_erase.mpr ⟨by decide, Finset.mem_insert_of_mem
              (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨by decide, h11⟩))⟩))
        · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
            (Finset.mem_erase.mpr ⟨by decide, Finset.mem_insert_of_mem
              (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨by decide, h20⟩))⟩))
        · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
            (Finset.mem_erase.mpr ⟨by decide, Finset.mem_insert_of_mem
              (Finset.mem_insert_self _ _)⟩))
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
      · -- `v = (3, -1)`: the right threat on row 0 wins.
        have m2 : AMove ((insert (3, 0) (insert (3, -1) (S.erase x₀))).erase (3, -1))
            (insert (6, 0) (insert (7, 0)
              ((insert (3, 0) (insert (3, -1) (S.erase x₀))).erase (3, -1)))) :=
          ⟨(6, 0), (7, 0), by decide, by decide,
            (fun h => hT6 (Finset.mem_of_mem_erase h)),
            (fun h => hT7 (Finset.mem_of_mem_erase h)), rfl⟩
        apply AForce.of_win m2
        apply winning_row0 2
        · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
            (Finset.mem_erase.mpr ⟨by decide, Finset.mem_insert_of_mem
              (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨by decide, h20⟩))⟩))
        · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
            (Finset.mem_erase.mpr ⟨by decide, Finset.mem_insert_self _ _⟩))
        · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
            (Finset.mem_erase.mpr ⟨by decide, Finset.mem_insert_of_mem
              (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨by decide, hy₀⟩))⟩))
        · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
            (Finset.mem_erase.mpr ⟨by decide, Finset.mem_insert_of_mem
              (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨by decide, h50⟩))⟩))
        · exact Finset.mem_insert_self _ _
      · -- `v` comes from the surrounded position itself.
        rw [Finset.mem_erase] at hv
        obtain ⟨hvx, hvS⟩ := hv
        have hvs : v ∈ {(0, 0), (5, 0)} ∪ xSlots ∪ Ny ∪ {(2, 0), x₀, y₀} := hvS
        rw [Finset.mem_union, Finset.mem_union, Finset.mem_union] at hvs
        -- the right threat, answered along row 0 from `(2, 0)`
        have right : ∀ v : Cell, (2, 0) ≠ v → (3, 0) ≠ v → y₀ ≠ v → (5, 0) ≠ v →
            AForce 5 ((insert (3, 0) (insert (3, -1) (S.erase x₀))).erase v) := by
          intro v h2 h3 h4 h5
          have m2 : AMove ((insert (3, 0) (insert (3, -1) (S.erase x₀))).erase v)
              (insert (6, 0) (insert (7, 0)
                ((insert (3, 0) (insert (3, -1) (S.erase x₀))).erase v))) :=
            ⟨(6, 0), (7, 0), by decide, by decide,
              (fun h => hT6 (Finset.mem_of_mem_erase h)),
              (fun h => hT7 (Finset.mem_of_mem_erase h)), rfl⟩
          apply AForce.of_win m2
          apply winning_row0 2
          · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
              (Finset.mem_erase.mpr ⟨h2, Finset.mem_insert_of_mem
                (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨by decide, h20⟩))⟩))
          · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
              (Finset.mem_erase.mpr ⟨h3, Finset.mem_insert_self _ _⟩))
          · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
              (Finset.mem_erase.mpr ⟨h4, Finset.mem_insert_of_mem
                (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨by decide, hy₀⟩))⟩))
          · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
              (Finset.mem_erase.mpr ⟨h5, Finset.mem_insert_of_mem
                (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨by decide, h50⟩))⟩))
          · exact Finset.mem_insert_self _ _
        -- the top threat, answered along the diagonal
        have top : ∀ v : Cell, (1, 1) ≠ v → (2, 0) ≠ v → (3, -1) ≠ v →
            AForce 5 ((insert (3, 0) (insert (3, -1) (S.erase x₀))).erase v) := by
          intro v h1 h2 h31
          have m2 : AMove ((insert (3, 0) (insert (3, -1) (S.erase x₀))).erase v)
              (insert (4, -2) (insert (5, -3)
                ((insert (3, 0) (insert (3, -1) (S.erase x₀))).erase v))) :=
            ⟨(4, -2), (5, -3), by decide, by decide,
              (fun h => hT42 (Finset.mem_of_mem_erase h)),
              (fun h => hT53 (Finset.mem_of_mem_erase h)), rfl⟩
          apply AForce.of_win m2
          apply winning_diag
          · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
              (Finset.mem_erase.mpr ⟨h1, Finset.mem_insert_of_mem
                (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨by decide, h11⟩))⟩))
          · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
              (Finset.mem_erase.mpr ⟨h2, Finset.mem_insert_of_mem
                (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨by decide, h20⟩))⟩))
          · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
              (Finset.mem_erase.mpr ⟨h31, Finset.mem_insert_of_mem
                (Finset.mem_insert_self _ _)⟩))
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
        rcases hvs with ((vb | vx) | vn) | vce
        · simp only [Finset.mem_insert, Finset.mem_singleton] at vb
          rcases vb with rfl | rfl
          · -- `v = (0, 0)`: the right threat wins.
            exact right (0, 0) (by decide) (by decide) (by decide) (by decide)
          · -- `v = (5, 0)`: the top threat wins.
            exact top (5, 0) (by decide) (by decide) (by decide)
        · -- `v` is a neighbor of `x₀`: the right threat wins.
          have hne : ∀ w : Cell, w ∉ xSlots → w ≠ v := fun w hw heq => hw (heq ▸ vx)
          exact right v (hne _ (by decide)) (hne _ (by decide)) (hne _ (by decide))
            (hne _ (by decide))
        · -- `v` is a neighbor of `y₀`: the right threat wins.
          have hne : ∀ w : Cell, w ∉ ySlots → w ≠ v := fun w hw heq => hw (heq ▸ hNy vn)
          exact right v (hne _ (by decide)) (hne _ (by decide)) (hne _ (by decide))
            (hne _ (by decide))
        · simp only [Finset.mem_insert, Finset.mem_singleton] at vce
          rcases vce with rfl | rfl | rfl
          · -- `v = (2, 0)`: the right threat wins along `(3, 0)`–`(7, 0)`.
            have m2 : AMove ((insert (3, 0) (insert (3, -1) (S.erase x₀))).erase (2, 0))
                (insert (6, 0) (insert (7, 0)
                  ((insert (3, 0) (insert (3, -1) (S.erase x₀))).erase (2, 0)))) :=
              ⟨(6, 0), (7, 0), by decide, by decide,
                (fun h => hT6 (Finset.mem_of_mem_erase h)),
                (fun h => hT7 (Finset.mem_of_mem_erase h)), rfl⟩
            apply AForce.of_win m2
            apply winning_row0 3
            · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
                (Finset.mem_erase.mpr ⟨by decide, Finset.mem_insert_self _ _⟩))
            · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
                (Finset.mem_erase.mpr ⟨by decide, Finset.mem_insert_of_mem
                  (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨by decide, hy₀⟩))⟩))
            · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
                (Finset.mem_erase.mpr ⟨by decide, Finset.mem_insert_of_mem
                  (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨by decide, h50⟩))⟩))
            · exact Finset.mem_insert_self _ _
            · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
          · -- `v = x₀` is impossible: `x₀` was already removed.
            exact absurd rfl hvx
          · -- `v = y₀`: the top threat wins.
            exact top y₀ (by decide) (by decide) (by decide)
    · -- `c = y₀`: `A` refills it and completes row 0.
      have m : AMove (S.erase y₀) (insert (3, 0) (insert (4, 0) (S.erase y₀))) :=
        ⟨(3, 0), (4, 0), by decide, by decide,
          (fun h => h30n (Finset.mem_of_mem_erase h)), (fun h => (Finset.mem_erase.mp h).1 rfl), rfl⟩
      apply AForce.of_win m
      apply winning_row0 0
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨by decide, h00⟩))
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨by decide, hx₀⟩))
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨by decide, h20⟩))
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)

/-- The mirrored endgame with `y₀` completely surrounded and filled. -/
lemma endgame_y_Bturn (Nx : Finset Cell) (hNx : Nx ⊆ xSlots) :
    ∀ t, BMove ({(0, 0), (5, 0)} ∪ ySlots ∪ Nx ∪ {(3, 0), x₀, y₀}) t → AForce 5 t := by
  intro t ht
  obtain ⟨c, hc, rfl⟩ := ht
  have hm : ∀ c : Cell, mirror (mirror c) = c := fun c => by
    unfold mirror
    rw [Prod.ext_iff]
    exact ⟨by ring, by ring⟩
  have hnn : (Nx.image mirror).image mirror = Nx := by
    rw [Finset.image_image]
    have hmid : mirror ∘ mirror = id := funext hm
    rw [hmid, Finset.image_id]
  have himg : ({(0, 0), (5, 0)} ∪ ySlots ∪ Nx ∪ {(3, 0), x₀, y₀} : Finset Cell)
      = (({(0, 0), (5, 0)} ∪ xSlots ∪ (Nx.image mirror) ∪ {(2, 0), x₀, y₀}).image mirror) := by
    rw [Finset.image_union, Finset.image_union, Finset.image_union]
    rw [show ({(0, 0), (5, 0)} : Finset Cell).image mirror = {(0, 0), (5, 0)} by decide]
    rw [show (xSlots.image mirror) = ySlots by decide]
    rw [hnn]
    rw [show ({(2, 0), x₀, y₀} : Finset Cell).image mirror = {(3, 0), x₀, y₀} by decide]
  have hNx' : Nx.image mirror ⊆ ySlots := by
    have h := Finset.image_subset_image hNx (f := mirror)
    rwa [show (xSlots.image mirror) = ySlots by decide] at h
  rw [himg] at hc
  obtain ⟨c₀, hc₀, rfl⟩ := Finset.mem_image.mp hc
  rw [himg, ← Finset.image_erase mirror_injective]
  exact AForce_image_mirror (endgame_x_Bturn (Nx.image mirror) hNx' _ ⟨c₀, hc₀, rfl⟩)

set_option maxHeartbeats 3200000 in
/-- The midgame invariant: with `(0, 0)` and `(5, 0)` occupied, exactly one of
`x₀`, `y₀` missing, and the filled neighbor slots `Nx ⊆ xSlots`, `Ny ⊆ ySlots`,
`A` can force a win.  `A` replaces the missing distinguished cell and fills one
more of its neighbor slots each round; `B` must remove one of the two
distinguished cells every round, so eventually one of them is completely
surrounded and the endgame lemmas apply. -/
lemma midphase : ∀ n : ℕ, ∀ Nx Ny P : Finset Cell,
    (xSlots.card - Nx.card) + (ySlots.card - Ny.card) = n →
    Nx ⊆ xSlots → Ny ⊆ ySlots → (P = {x₀} ∨ P = {y₀}) →
    AForce 5 ({(0, 0), (5, 0)} ∪ Nx ∪ Ny ∪ P) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Nx Ny P hmeas hNx hNy hP
    have hcardx : xSlots.card = 4 := by decide
    have hcardy : ySlots.card = 4 := by decide
    have hlex : Nx.card ≤ xSlots.card := Finset.card_le_card hNx
    have hley : Ny.card ≤ ySlots.card := Finset.card_le_card hNy
    rcases hP with rfl | rfl
    · -- #### `y₀` is missing; `A` replaces it.
      by_cases hfull : Ny = ySlots
      · -- All of `y₀`'s neighbor slots are filled: saturate `y₀` with `(3, 0)`.
        subst hfull
        have hymem : y₀ ∉ ({(0, 0), (5, 0)} ∪ Nx ∪ ySlots ∪ {x₀} : Finset Cell) := by
          have e1a : y₀ ≠ (0, 0) := by decide
          have e1b : y₀ ≠ (5, 0) := by decide
          have e2 : y₀ ∉ xSlots := by decide
          have e3 : y₀ ∉ ySlots := by decide
          have e4 : y₀ ≠ x₀ := by decide
          have e5 : y₀ ∉ Nx := fun h => e2 (hNx h)
          simp [Finset.mem_union, e1a, e1b, e5, e3, e4]
        have h3mem : (3, 0) ∉ ({(0, 0), (5, 0)} ∪ Nx ∪ ySlots ∪ {x₀} : Finset Cell) := by
          have e1a : (3, 0) ≠ (0, 0) := by decide
          have e1b : (3, 0) ≠ (5, 0) := by decide
          have e2 : (3, 0) ∉ xSlots := by decide
          have e3 : (3, 0) ∉ ySlots := by decide
          have e4 : (3, 0) ≠ x₀ := by decide
          have e5 : (3, 0) ∉ Nx := fun h => e2 (hNx h)
          simp [Finset.mem_union, e5, e3, e4]
        have m : AMove ({(0, 0), (5, 0)} ∪ Nx ∪ ySlots ∪ {x₀})
            (insert y₀ (insert (3, 0) ({(0, 0), (5, 0)} ∪ Nx ∪ ySlots ∪ {x₀}))) :=
          ⟨y₀, (3, 0), by decide, by decide, hymem, h3mem, rfl⟩
        apply AForce.of_step m
        intro t ht
        obtain ⟨c, hc, rfl⟩ := ht
        have e : insert y₀ (insert (3, 0) ({(0, 0), (5, 0)} ∪ Nx ∪ ySlots ∪ {x₀}))
            = {(0, 0), (5, 0)} ∪ ySlots ∪ Nx ∪ {(3, 0), x₀, y₀} := by
          simp only [Finset.insert_eq]
          ac_rfl
        rw [e] at hc ⊢
        exact endgame_y_Bturn Nx hNx _ ⟨c, hc, rfl⟩
      · -- Pick a fresh neighbor slot `sy` of `y₀` and play `y₀`, `sy`.
        have hss : Ny ⊂ ySlots := Finset.ssubset_iff_subset_ne.mpr ⟨hNy, hfull⟩
        have hlt : Ny.card < ySlots.card := Finset.card_lt_card hss
        obtain ⟨sy, hsy, hsyNy⟩ := Finset.exists_of_ssubset hss
        have hsy' := hsy
        simp only [ySlots, Finset.mem_insert, Finset.mem_singleton] at hsy'
        have hsyadj : Adj y₀ sy := by rcases hsy' with rfl | rfl | rfl | rfl <;> decide
        have hsyne : sy ≠ y₀ := by rcases hsy' with rfl | rfl | rfl | rfl <;> decide
        have hsynbase0 : sy ≠ (0, 0) := by
          rcases hsy' with rfl | rfl | rfl | rfl <;> decide
        have hsynbase5 : sy ≠ (5, 0) := by
          rcases hsy' with rfl | rfl | rfl | rfl <;> decide
        have hsynx : sy ∉ Nx := fun h => by
          have h1 : sy ∈ xSlots ∩ ySlots := Finset.mem_inter.mpr ⟨hNx h, hsy⟩
          have h2 : xSlots ∩ ySlots = ∅ := by decide
          rw [h2] at h1
          simp at h1
        have hsynx₀ : sy ≠ x₀ := by rcases hsy' with rfl | rfl | rfl | rfl <;> decide
        have hymem : y₀ ∉ ({(0, 0), (5, 0)} ∪ Nx ∪ Ny ∪ {x₀} : Finset Cell) := by
          have e1a : y₀ ≠ (0, 0) := by decide
          have e1b : y₀ ≠ (5, 0) := by decide
          have e2 : y₀ ∉ xSlots := by decide
          have e3 : y₀ ∉ ySlots := by decide
          have e4 : y₀ ≠ x₀ := by decide
          have e5 : y₀ ∉ Nx := fun h => e2 (hNx h)
          have e6 : y₀ ∉ Ny := fun h => e3 (hNy h)
          simp [Finset.mem_union, e1a, e1b, e5, e6, e4]
        have hsymem : sy ∉ ({(0, 0), (5, 0)} ∪ Nx ∪ Ny ∪ {x₀} : Finset Cell) := by
          simp [Finset.mem_union, hsynbase0, hsynbase5, hsynx, hsyNy, hsynx₀]
        have m : AMove ({(0, 0), (5, 0)} ∪ Nx ∪ Ny ∪ {x₀})
            (insert y₀ (insert sy ({(0, 0), (5, 0)} ∪ Nx ∪ Ny ∪ {x₀}))) :=
          ⟨y₀, sy, hsyne.symm, hsyadj, hymem, hsymem, rfl⟩
        apply AForce.of_step m
        intro t ht
        obtain ⟨c, hc, rfl⟩ := ht
        -- common facts for the immediate-win responses
        have h2B : (2, 0) ∉ insert y₀ (insert sy ({(0, 0), (5, 0)} ∪ Nx ∪ Ny ∪ {x₀})) := by
          have e1a : (2, 0) ≠ (0, 0) := by decide
          have e1b : (2, 0) ≠ (5, 0) := by decide
          have e2 : (2, 0) ∉ xSlots := by decide
          have e3 : (2, 0) ∉ ySlots := by decide
          have e4 : (2, 0) ≠ x₀ := by decide
          have e5 : (2, 0) ∉ Nx := fun h => e2 (hNx h)
          have e6 : (2, 0) ∉ Ny := fun h => e3 (hNy h)
          have e7 : (2, 0) ≠ sy := fun h => e3 (h ▸ hsy)
          have e8 : (2, 0) ≠ y₀ := by decide
          simp [Finset.mem_insert, Finset.mem_union,
            e8, e7, e5, e6, e4]
        have h3B : (3, 0) ∉ insert y₀ (insert sy ({(0, 0), (5, 0)} ∪ Nx ∪ Ny ∪ {x₀})) := by
          have e1a : (3, 0) ≠ (0, 0) := by decide
          have e1b : (3, 0) ≠ (5, 0) := by decide
          have e2 : (3, 0) ∉ xSlots := by decide
          have e3 : (3, 0) ∉ ySlots := by decide
          have e4 : (3, 0) ≠ x₀ := by decide
          have e5 : (3, 0) ∉ Nx := fun h => e2 (hNx h)
          have e6 : (3, 0) ∉ Ny := fun h => e3 (hNy h)
          have e7 : (3, 0) ≠ sy := fun h => e3 (h ▸ hsy)
          have e8 : (3, 0) ≠ y₀ := by decide
          simp [Finset.mem_insert, Finset.mem_union,
            e8, e7, e5, e6, e4]
        have inB00 : (0, 0) ∈ insert y₀ (insert sy ({(0, 0), (5, 0)} ∪ Nx ∪ Ny ∪ {x₀})) := by
          simp [Finset.mem_insert, Finset.mem_union]
        have inB50 : (5, 0) ∈ insert y₀ (insert sy ({(0, 0), (5, 0)} ∪ Nx ∪ Ny ∪ {x₀})) := by
          simp [Finset.mem_insert, Finset.mem_union]
        have inBx₀ : x₀ ∈ insert y₀ (insert sy ({(0, 0), (5, 0)} ∪ Nx ∪ Ny ∪ {x₀})) := by
          simp [Finset.mem_insert, Finset.mem_union]
        have inBy₀ : y₀ ∈ insert y₀ (insert sy ({(0, 0), (5, 0)} ∪ Nx ∪ Ny ∪ {x₀})) :=
          Finset.mem_insert_self _ _
        rw [Finset.mem_insert, Finset.mem_insert] at hc
        rcases hc with rfl | rfl | hc
        · -- `B` removes `y₀` again: the loop continues with `sy` filled.
          have e : (insert y₀ (insert sy ({(0, 0), (5, 0)} ∪ Nx ∪ Ny ∪ {x₀}))).erase y₀
              = {(0, 0), (5, 0)} ∪ Nx ∪ (insert sy Ny) ∪ {x₀} := by
            rw [Finset.erase_insert (by
              simp only [Finset.mem_insert, not_or]
              exact ⟨hsyne.symm, hymem⟩)]
            simp only [Finset.insert_eq]
            ac_rfl
          rw [e]
          apply ih (n - 1) (by lia) Nx (insert sy Ny) {x₀} _ hNx
            (Finset.insert_subset hsy hNy) (Or.inl rfl)
          have hcard : (insert sy Ny).card = Ny.card + 1 := Finset.card_insert_of_notMem hsyNy
          lia
        · -- `B` removes the fresh slot `sy`: `A` completes row 0 and wins.
          apply win_now0 (fun h => h2B (Finset.mem_of_mem_erase h))
            (fun h => h3B (Finset.mem_of_mem_erase h))
          · exact Finset.mem_erase.mpr ⟨fun h => hsynbase0 h.symm, inB00⟩
          · exact Finset.mem_erase.mpr ⟨hsynx₀.symm, inBx₀⟩
          · exact Finset.mem_erase.mpr ⟨hsyne.symm, inBy₀⟩
        · -- `B` removes something else.
          rw [Finset.mem_union, Finset.mem_union, Finset.mem_union] at hc
          rcases hc with ((hcbase | hcx) | hcy) | hcx₀
          · -- a base cell
            simp only [Finset.mem_insert, Finset.mem_singleton] at hcbase
            rcases hcbase with rfl | rfl
            · -- `(0, 0)`: complete the line `(1, 0)`–`(5, 0)`.
              apply win_now1 (s := (insert y₀ (insert sy ({(0, 0), (5, 0)} ∪ Nx ∪ Ny ∪ {x₀}))).erase (0, 0))
              · exact fun h => h2B (Finset.mem_of_mem_erase h)
              · exact fun h => h3B (Finset.mem_of_mem_erase h)
              · exact Finset.mem_erase.mpr ⟨by decide, inBx₀⟩
              · exact Finset.mem_erase.mpr ⟨by decide, inBy₀⟩
              · exact Finset.mem_erase.mpr ⟨by decide, inB50⟩
            · -- `(5, 0)`: complete the line `(0, 0)`–`(4, 0)`.
              apply win_now0 (s := (insert y₀ (insert sy ({(0, 0), (5, 0)} ∪ Nx ∪ Ny ∪ {x₀}))).erase (5, 0))
              · exact fun h => h2B (Finset.mem_of_mem_erase h)
              · exact fun h => h3B (Finset.mem_of_mem_erase h)
              · exact Finset.mem_erase.mpr ⟨by decide, inB00⟩
              · exact Finset.mem_erase.mpr ⟨by decide, inBx₀⟩
              · exact Finset.mem_erase.mpr ⟨by decide, inBy₀⟩
          · -- a filled neighbor slot of `x₀`
            apply win_now0 (s := (insert y₀ (insert sy ({(0, 0), (5, 0)} ∪ Nx ∪ Ny ∪ {x₀}))).erase c)
            · exact fun h => h2B (Finset.mem_of_mem_erase h)
            · exact fun h => h3B (Finset.mem_of_mem_erase h)
            · exact Finset.mem_erase.mpr ⟨fun h => (by decide : (0, 0) ∉ xSlots) (h ▸ hNx hcx), inB00⟩
            · exact Finset.mem_erase.mpr ⟨fun h => (by decide : x₀ ∉ xSlots) (h ▸ hNx hcx), inBx₀⟩
            · exact Finset.mem_erase.mpr ⟨fun h => (by decide : y₀ ∉ xSlots) (h ▸ hNx hcx), inBy₀⟩
          · -- a filled neighbor slot of `y₀`
            apply win_now0 (s := (insert y₀ (insert sy ({(0, 0), (5, 0)} ∪ Nx ∪ Ny ∪ {x₀}))).erase c)
            · exact fun h => h2B (Finset.mem_of_mem_erase h)
            · exact fun h => h3B (Finset.mem_of_mem_erase h)
            · exact Finset.mem_erase.mpr ⟨fun h => (by decide : (0, 0) ∉ ySlots) (h ▸ hNy hcy), inB00⟩
            · exact Finset.mem_erase.mpr ⟨fun h => (by decide : x₀ ∉ ySlots) (h ▸ hNy hcy), inBx₀⟩
            · exact Finset.mem_erase.mpr ⟨fun h => (by decide : y₀ ∉ ySlots) (h ▸ hNy hcy), inBy₀⟩
          · -- `x₀`: the loop continues on the other side.
            rw [Finset.mem_singleton] at hcx₀
            subst hcx₀
            have e : (insert y₀ (insert sy ({(0, 0), (5, 0)} ∪ Nx ∪ Ny ∪ {x₀}))).erase x₀
                = {(0, 0), (5, 0)} ∪ Nx ∪ (insert sy Ny) ∪ {y₀} := by
              rw [Finset.erase_insert_of_ne (by decide : y₀ ≠ x₀),
                Finset.erase_insert_of_ne hsynx₀,
                Finset.union_singleton,
                Finset.erase_insert (by
                  have ex1 : x₀ ≠ (0, 0) := by decide
                  have ex2 : x₀ ≠ (5, 0) := by decide
                  have ex3 : x₀ ∉ Nx := fun h => (by decide : x₀ ∉ xSlots) (hNx h)
                  have ex4 : x₀ ∉ Ny := fun h => (by decide : x₀ ∉ ySlots) (hNy h)
                  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or]
                  exact ⟨⟨⟨ex1, ex2⟩, ex3⟩, ex4⟩)]
              simp only [Finset.insert_eq]
              ac_rfl
            rw [e]
            apply ih (n - 1) (by lia) Nx (insert sy Ny) {y₀} _ hNx
              (Finset.insert_subset hsy hNy) (Or.inr rfl)
            have hcard : (insert sy Ny).card = Ny.card + 1 := Finset.card_insert_of_notMem hsyNy
            lia
    · -- #### `x₀` is missing; `A` replaces it.  (Mirror of the previous branch.)
      by_cases hfull : Nx = xSlots
      · -- All of `x₀`'s neighbor slots are filled: saturate `x₀` with `(2, 0)`.
        subst hfull
        have hxmem : x₀ ∉ ({(0, 0), (5, 0)} ∪ xSlots ∪ Ny ∪ {y₀} : Finset Cell) := by
          have e1a : x₀ ≠ (0, 0) := by decide
          have e1b : x₀ ≠ (5, 0) := by decide
          have e2 : x₀ ∉ xSlots := by decide
          have e3 : x₀ ∉ ySlots := by decide
          have e4 : x₀ ≠ y₀ := by decide
          have e6 : x₀ ∉ Ny := fun h => e3 (hNy h)
          simp [Finset.mem_union, e1a, e1b, e2, e6, e4]
        have h2mem : (2, 0) ∉ ({(0, 0), (5, 0)} ∪ xSlots ∪ Ny ∪ {y₀} : Finset Cell) := by
          have e1a : (2, 0) ≠ (0, 0) := by decide
          have e1b : (2, 0) ≠ (5, 0) := by decide
          have e2 : (2, 0) ∉ xSlots := by decide
          have e3 : (2, 0) ∉ ySlots := by decide
          have e4 : (2, 0) ≠ y₀ := by decide
          have e6 : (2, 0) ∉ Ny := fun h => e3 (hNy h)
          simp [Finset.mem_union, e2, e6, e4]
        have m : AMove ({(0, 0), (5, 0)} ∪ xSlots ∪ Ny ∪ {y₀})
            (insert x₀ (insert (2, 0) ({(0, 0), (5, 0)} ∪ xSlots ∪ Ny ∪ {y₀}))) :=
          ⟨x₀, (2, 0), by decide, by decide, hxmem, h2mem, rfl⟩
        apply AForce.of_step m
        intro t ht
        obtain ⟨c, hc, rfl⟩ := ht
        have e : insert x₀ (insert (2, 0) ({(0, 0), (5, 0)} ∪ xSlots ∪ Ny ∪ {y₀}))
            = {(0, 0), (5, 0)} ∪ xSlots ∪ Ny ∪ {(2, 0), x₀, y₀} := by
          simp only [Finset.insert_eq]
          ac_rfl
        rw [e] at hc ⊢
        exact endgame_x_Bturn Ny hNy _ ⟨c, hc, rfl⟩
      · -- Pick a fresh neighbor slot `sx` of `x₀` and play `x₀`, `sx`.
        have hss : Nx ⊂ xSlots := Finset.ssubset_iff_subset_ne.mpr ⟨hNx, hfull⟩
        have hlt : Nx.card < xSlots.card := Finset.card_lt_card hss
        obtain ⟨sx, hsx, hsxNx⟩ := Finset.exists_of_ssubset hss
        have hsx' := hsx
        simp only [xSlots, Finset.mem_insert, Finset.mem_singleton] at hsx'
        have hsxadj : Adj x₀ sx := by rcases hsx' with rfl | rfl | rfl | rfl <;> decide
        have hsxne : sx ≠ x₀ := by rcases hsx' with rfl | rfl | rfl | rfl <;> decide
        have hsxnbase0 : sx ≠ (0, 0) := by
          rcases hsx' with rfl | rfl | rfl | rfl <;> decide
        have hsxnbase5 : sx ≠ (5, 0) := by
          rcases hsx' with rfl | rfl | rfl | rfl <;> decide
        have hsxny : sx ∉ Ny := fun h => by
          have h1 : sx ∈ xSlots ∩ ySlots := Finset.mem_inter.mpr ⟨hsx, hNy h⟩
          have h2 : xSlots ∩ ySlots = ∅ := by decide
          rw [h2] at h1
          simp at h1
        have hsxny₀ : sx ≠ y₀ := by rcases hsx' with rfl | rfl | rfl | rfl <;> decide
        have hxmem : x₀ ∉ ({(0, 0), (5, 0)} ∪ Nx ∪ Ny ∪ {y₀} : Finset Cell) := by
          have e1a : x₀ ≠ (0, 0) := by decide
          have e1b : x₀ ≠ (5, 0) := by decide
          have e2 : x₀ ∉ xSlots := by decide
          have e3 : x₀ ∉ ySlots := by decide
          have e4 : x₀ ≠ y₀ := by decide
          have e5 : x₀ ∉ Nx := fun h => e2 (hNx h)
          have e6 : x₀ ∉ Ny := fun h => e3 (hNy h)
          simp [Finset.mem_union, e1a, e1b, e5, e6, e4]
        have hsxmem : sx ∉ ({(0, 0), (5, 0)} ∪ Nx ∪ Ny ∪ {y₀} : Finset Cell) := by
          simp [Finset.mem_union, hsxnbase0, hsxnbase5, hsxNx, hsxny, hsxny₀]
        have m : AMove ({(0, 0), (5, 0)} ∪ Nx ∪ Ny ∪ {y₀})
            (insert x₀ (insert sx ({(0, 0), (5, 0)} ∪ Nx ∪ Ny ∪ {y₀}))) :=
          ⟨x₀, sx, hsxne.symm, hsxadj, hxmem, hsxmem, rfl⟩
        apply AForce.of_step m
        intro t ht
        obtain ⟨c, hc, rfl⟩ := ht
        -- common facts for the immediate-win responses
        have h2B : (2, 0) ∉ insert x₀ (insert sx ({(0, 0), (5, 0)} ∪ Nx ∪ Ny ∪ {y₀})) := by
          have e1a : (2, 0) ≠ (0, 0) := by decide
          have e1b : (2, 0) ≠ (5, 0) := by decide
          have e2 : (2, 0) ∉ xSlots := by decide
          have e3 : (2, 0) ∉ ySlots := by decide
          have e4 : (2, 0) ≠ y₀ := by decide
          have e5 : (2, 0) ∉ Nx := fun h => e2 (hNx h)
          have e6 : (2, 0) ∉ Ny := fun h => e3 (hNy h)
          have e7 : (2, 0) ≠ sx := fun h => e2 (h ▸ hsx)
          have e8 : (2, 0) ≠ x₀ := by decide
          simp [Finset.mem_insert, Finset.mem_union,
            e8, e7, e5, e6, e4]
        have h3B : (3, 0) ∉ insert x₀ (insert sx ({(0, 0), (5, 0)} ∪ Nx ∪ Ny ∪ {y₀})) := by
          have e1a : (3, 0) ≠ (0, 0) := by decide
          have e1b : (3, 0) ≠ (5, 0) := by decide
          have e2 : (3, 0) ∉ xSlots := by decide
          have e3 : (3, 0) ∉ ySlots := by decide
          have e4 : (3, 0) ≠ y₀ := by decide
          have e5 : (3, 0) ∉ Nx := fun h => e2 (hNx h)
          have e6 : (3, 0) ∉ Ny := fun h => e3 (hNy h)
          have e7 : (3, 0) ≠ sx := fun h => e2 (h ▸ hsx)
          have e8 : (3, 0) ≠ x₀ := by decide
          simp [Finset.mem_insert, Finset.mem_union,
            e8, e7, e5, e6, e4]
        have inB00 : (0, 0) ∈ insert x₀ (insert sx ({(0, 0), (5, 0)} ∪ Nx ∪ Ny ∪ {y₀})) := by
          simp [Finset.mem_insert, Finset.mem_union]
        have inB50 : (5, 0) ∈ insert x₀ (insert sx ({(0, 0), (5, 0)} ∪ Nx ∪ Ny ∪ {y₀})) := by
          simp [Finset.mem_insert, Finset.mem_union]
        have inBy₀ : y₀ ∈ insert x₀ (insert sx ({(0, 0), (5, 0)} ∪ Nx ∪ Ny ∪ {y₀})) := by
          simp [Finset.mem_insert, Finset.mem_union]
        have inBx₀ : x₀ ∈ insert x₀ (insert sx ({(0, 0), (5, 0)} ∪ Nx ∪ Ny ∪ {y₀})) :=
          Finset.mem_insert_self _ _
        rw [Finset.mem_insert, Finset.mem_insert] at hc
        rcases hc with rfl | rfl | hc
        · -- `B` removes `x₀` again: the loop continues with `sx` filled.
          have e : (insert x₀ (insert sx ({(0, 0), (5, 0)} ∪ Nx ∪ Ny ∪ {y₀}))).erase x₀
              = {(0, 0), (5, 0)} ∪ (insert sx Nx) ∪ Ny ∪ {y₀} := by
            rw [Finset.erase_insert (by
              simp only [Finset.mem_insert, not_or]
              exact ⟨hsxne.symm, hxmem⟩)]
            simp only [Finset.insert_eq]
            ac_rfl
          rw [e]
          apply ih (n - 1) (by lia) (insert sx Nx) Ny {y₀} _
            (Finset.insert_subset hsx hNx) hNy (Or.inr rfl)
          have hcard : (insert sx Nx).card = Nx.card + 1 := Finset.card_insert_of_notMem hsxNx
          lia
        · -- `B` removes the fresh slot `sx`: `A` completes row 0 and wins.
          apply win_now0 (fun h => h2B (Finset.mem_of_mem_erase h))
            (fun h => h3B (Finset.mem_of_mem_erase h))
          · exact Finset.mem_erase.mpr ⟨fun h => hsxnbase0 h.symm, inB00⟩
          · exact Finset.mem_erase.mpr ⟨hsxne.symm, inBx₀⟩
          · exact Finset.mem_erase.mpr ⟨hsxny₀.symm, inBy₀⟩
        · -- `B` removes something else.
          rw [Finset.mem_union, Finset.mem_union, Finset.mem_union] at hc
          rcases hc with ((hcbase | hcx) | hcy) | hcy₀
          · -- a base cell
            simp only [Finset.mem_insert, Finset.mem_singleton] at hcbase
            rcases hcbase with rfl | rfl
            · -- `(0, 0)`: complete the line `(1, 0)`–`(5, 0)`.
              apply win_now1 (s := (insert x₀ (insert sx ({(0, 0), (5, 0)} ∪ Nx ∪ Ny ∪ {y₀}))).erase (0, 0))
              · exact fun h => h2B (Finset.mem_of_mem_erase h)
              · exact fun h => h3B (Finset.mem_of_mem_erase h)
              · exact Finset.mem_erase.mpr ⟨by decide, inBx₀⟩
              · exact Finset.mem_erase.mpr ⟨by decide, inBy₀⟩
              · exact Finset.mem_erase.mpr ⟨by decide, inB50⟩
            · -- `(5, 0)`: complete the line `(0, 0)`–`(4, 0)`.
              apply win_now0 (s := (insert x₀ (insert sx ({(0, 0), (5, 0)} ∪ Nx ∪ Ny ∪ {y₀}))).erase (5, 0))
              · exact fun h => h2B (Finset.mem_of_mem_erase h)
              · exact fun h => h3B (Finset.mem_of_mem_erase h)
              · exact Finset.mem_erase.mpr ⟨by decide, inB00⟩
              · exact Finset.mem_erase.mpr ⟨by decide, inBx₀⟩
              · exact Finset.mem_erase.mpr ⟨by decide, inBy₀⟩
          · -- a filled neighbor slot of `x₀`
            apply win_now0 (s := (insert x₀ (insert sx ({(0, 0), (5, 0)} ∪ Nx ∪ Ny ∪ {y₀}))).erase c)
            · exact fun h => h2B (Finset.mem_of_mem_erase h)
            · exact fun h => h3B (Finset.mem_of_mem_erase h)
            · exact Finset.mem_erase.mpr ⟨fun h => (by decide : (0, 0) ∉ xSlots) (h ▸ hNx hcx), inB00⟩
            · exact Finset.mem_erase.mpr ⟨fun h => (by decide : x₀ ∉ xSlots) (h ▸ hNx hcx), inBx₀⟩
            · exact Finset.mem_erase.mpr ⟨fun h => (by decide : y₀ ∉ xSlots) (h ▸ hNx hcx), inBy₀⟩
          · -- a filled neighbor slot of `y₀`
            apply win_now0 (s := (insert x₀ (insert sx ({(0, 0), (5, 0)} ∪ Nx ∪ Ny ∪ {y₀}))).erase c)
            · exact fun h => h2B (Finset.mem_of_mem_erase h)
            · exact fun h => h3B (Finset.mem_of_mem_erase h)
            · exact Finset.mem_erase.mpr ⟨fun h => (by decide : (0, 0) ∉ ySlots) (h ▸ hNy hcy), inB00⟩
            · exact Finset.mem_erase.mpr ⟨fun h => (by decide : x₀ ∉ ySlots) (h ▸ hNy hcy), inBx₀⟩
            · exact Finset.mem_erase.mpr ⟨fun h => (by decide : y₀ ∉ ySlots) (h ▸ hNy hcy), inBy₀⟩
          · -- `y₀`: the loop continues on the other side.
            rw [Finset.mem_singleton] at hcy₀
            subst hcy₀
            have e : (insert x₀ (insert sx ({(0, 0), (5, 0)} ∪ Nx ∪ Ny ∪ {y₀}))).erase y₀
                = {(0, 0), (5, 0)} ∪ (insert sx Nx) ∪ Ny ∪ {x₀} := by
              rw [Finset.erase_insert_of_ne (by decide : x₀ ≠ y₀),
                Finset.erase_insert_of_ne hsxny₀,
                Finset.union_singleton,
                Finset.erase_insert (by
                  have ex1 : y₀ ≠ (0, 0) := by decide
                  have ex2 : y₀ ≠ (5, 0) := by decide
                  have ex3 : y₀ ∉ Nx := fun h => (by decide : y₀ ∉ xSlots) (hNx h)
                  have ex4 : y₀ ∉ Ny := fun h => (by decide : y₀ ∉ ySlots) (hNy h)
                  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or]
                  exact ⟨⟨⟨ex1, ex2⟩, ex3⟩, ex4⟩)]
              simp only [Finset.insert_eq]
              ac_rfl
            rw [e]
            apply ih (n - 1) (by lia) (insert sx Nx) Ny {x₀} _
              (Finset.insert_subset hsx hNx) hNy (Or.inl rfl)
            have hcard : (insert sx Nx).card = Nx.card + 1 := Finset.card_insert_of_notMem hsxNx
            lia
/-- With counters on two adjacent cells of a line, `A` places the mirror pair
two spaces down the same line, reaching the midgame invariant. -/
lemma canonical_pair : AForce 5 ({(0, 0), (1, 0)}) := by
  have m : AMove ({(0, 0), (1, 0)}) ({(0, 0), (1, 0), (4, 0), (5, 0)}) :=
    ⟨(4, 0), (5, 0), by decide, by decide, by decide, by decide, by decide⟩
  apply AForce.of_step m
  intro t ht
  obtain ⟨c, hc, rfl⟩ := ht
  simp only [Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · -- `B` removes `(0, 0)`: `A` completes `(1, 0)`–`(5, 0)` and wins.
    have e : ({(0, 0), (1, 0), (4, 0), (5, 0)} : Finset Cell).erase (0, 0)
        = {(1, 0), (4, 0), (5, 0)} := by decide
    rw [e]
    apply win_now1 <;> decide
  · -- `B` removes `x₀`: the midgame invariant with `y₀` missing.
    have e : ({(0, 0), (1, 0), (4, 0), (5, 0)} : Finset Cell).erase (1, 0)
        = {(0, 0), (5, 0)} ∪ ∅ ∪ ∅ ∪ {y₀} := by decide
    rw [e]
    exact midphase 8 ∅ ∅ {y₀} (by decide) (by simp) (by simp) (Or.inr rfl)
  · -- `B` removes `y₀`: the midgame invariant with `x₀` missing.
    have e : ({(0, 0), (1, 0), (4, 0), (5, 0)} : Finset Cell).erase (4, 0)
        = {(0, 0), (5, 0)} ∪ ∅ ∪ ∅ ∪ {x₀} := by decide
    rw [e]
    exact midphase 8 ∅ ∅ {x₀} (by decide) (by simp) (by simp) (Or.inl rfl)
  · -- `B` removes `(5, 0)`: `A` completes `(0, 0)`–`(4, 0)` and wins.
    have e : ({(0, 0), (1, 0), (4, 0), (5, 0)} : Finset Cell).erase (5, 0)
        = {(0, 0), (1, 0), (4, 0)} := by decide
    rw [e]
    apply win_now0 <;> decide

/-- With two counters on adjacent cells, `A` wins (transport of the canonical
configuration along a grid symmetry). -/
lemma adjacent_pair {P Q : Cell} (_hne : P ≠ Q) (hadj : Adj P Q) :
    AForce 5 ({P, Q}) := by
  unfold Adj at hadj
  rw [mem_offsets] at hadj
  have hrot : ∃ j : ℕ, rot^[j] (1, 0) = (Q.1 - P.1, Q.2 - P.2) := by
    rcases hadj with h | h | h | h | h | h
    · exact ⟨0, h.symm⟩
    · exact ⟨3, by rw [show rot^[3] (1, 0) = (-1, 0) from rfl]; exact h.symm⟩
    · exact ⟨1, by rw [show rot^[1] (1, 0) = (0, 1) from rfl]; exact h.symm⟩
    · exact ⟨4, by rw [show rot^[4] (1, 0) = (0, -1) from rfl]; exact h.symm⟩
    · exact ⟨5, by rw [show rot^[5] (1, 0) = (1, -1) from rfl]; exact h.symm⟩
    · exact ⟨2, by rw [show rot^[2] (1, 0) = (-1, 1) from rfl]; exact h.symm⟩
  obtain ⟨j, hj⟩ := hrot
  have hQ : transl P (rot^[j] (1, 0)) = Q := by
    rw [hj]
    unfold transl
    rw [Prod.ext_iff]
    exact ⟨by ring, by ring⟩
  have hP' : transl P (0, 0) = P := by unfold transl; simp
  have himg : ({P, Q} : Finset Cell)
      = (({(0, 0), (1, 0)} : Finset Cell).image (rot^[j])).image (transl P) := by
    have hz : rot^[j] (0, 0) = (0, 0) := Function.iterate_fixed (by decide) j
    rw [Finset.image_insert, Finset.image_singleton, hz, Finset.image_insert,
      Finset.image_singleton, hP', hQ]
  rw [himg]
  exact AForce_image_transl P (AForce_image_rotpow j canonical_pair)

/-- `A` wins for `k = 5`, following the official solution: after two rounds a
pair of adjacent counters remains, from which the strategy above wins. -/
theorem ACanWin_five : ACanWin 5 := by
  unfold ACanWin
  apply AForce.of_step (s' := ({(0, 0), (1, 0)} : Finset Cell))
  · exact ⟨(0, 0), (1, 0), by decide, by decide, by decide, by decide, rfl⟩
  · intro t ht
    obtain ⟨c, hc, rfl⟩ := ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl
    · -- one counter at `(1, 0)`: `A` builds the triangle `(0, 0)`, `(0, 1)`.
      have e : ({(0, 0), (1, 0)} : Finset Cell).erase (0, 0) = {(1, 0)} := by decide
      rw [e]
      apply AForce.of_step (s' := ({(1, 0), (0, 0), (0, 1)} : Finset Cell))
      · exact ⟨(0, 0), (0, 1), by decide, by decide, by decide, by decide, by decide⟩
      · intro t ht
        obtain ⟨c, hc, rfl⟩ := ht
        simp only [Finset.mem_insert, Finset.mem_singleton] at hc
        rcases hc with rfl | rfl | rfl
        · have e : ({(1, 0), (0, 0), (0, 1)} : Finset Cell).erase (1, 0)
              = {(0, 0), (0, 1)} := by decide
          rw [e]
          exact adjacent_pair (by decide) (by decide)
        · have e : ({(1, 0), (0, 0), (0, 1)} : Finset Cell).erase (0, 0)
              = {(1, 0), (0, 1)} := by decide
          rw [e]
          exact adjacent_pair (by decide) (by decide)
        · have e : ({(1, 0), (0, 0), (0, 1)} : Finset Cell).erase (0, 1)
              = {(1, 0), (0, 0)} := by decide
          rw [e]
          exact adjacent_pair (by decide) (by decide)
    · -- one counter at `(0, 0)`: `A` builds the triangle `(1, 0)`, `(0, 1)`.
      have e : ({(0, 0), (1, 0)} : Finset Cell).erase (1, 0) = {(0, 0)} := by decide
      rw [e]
      apply AForce.of_step (s' := ({(0, 0), (1, 0), (0, 1)} : Finset Cell))
      · exact ⟨(1, 0), (0, 1), by decide, by decide, by decide, by decide, by decide⟩
      · intro t ht
        obtain ⟨c, hc, rfl⟩ := ht
        simp only [Finset.mem_insert, Finset.mem_singleton] at hc
        rcases hc with rfl | rfl | rfl
        · have e : ({(0, 0), (1, 0), (0, 1)} : Finset Cell).erase (0, 0)
              = {(1, 0), (0, 1)} := by decide
          rw [e]
          exact adjacent_pair (by decide) (by decide)
        · have e : ({(0, 0), (1, 0), (0, 1)} : Finset Cell).erase (1, 0)
              = {(0, 0), (0, 1)} := by decide
          rw [e]
          exact adjacent_pair (by decide) (by decide)
        · have e : ({(0, 0), (1, 0), (0, 1)} : Finset Cell).erase (0, 1)
              = {(0, 0), (1, 0)} := by decide
          rw [e]
          exact adjacent_pair (by decide) (by decide)

/-- If `A` can force a win with target `l`, `A` can also force a win with any
smaller target `k ≤ l` (a line of `l` consecutive cells contains a line of `k`). -/
lemma AForce_mono {k l : ℕ} (hkl : k ≤ l) {s : Finset Cell} (h : AForce l s) :
    AForce k s := by
  induction h
  case of_win s s' m w =>
    obtain ⟨d, hd, p, hline⟩ := w
    exact AForce.of_win m ⟨d, hd, p, fun i hi => hline i (by lia)⟩
  case of_step s s' m h ih =>
    exact AForce.of_step m ih

snip end

determine solution : ℕ := 6

problem usa2014_p4 : IsLeast {k : ℕ | 0 < k ∧ ¬ ACanWin k} solution := by
  constructor
  · exact ⟨by norm_num, not_ACanWin_six⟩
  · rintro k ⟨_hk0, hk⟩
    show 6 ≤ k
    by_contra hlt
    push Not at hlt
    have hwin : ACanWin k := AForce_mono (by lia : k ≤ 5) ACanWin_five
    exact hk hwin

end Usa2014P4
