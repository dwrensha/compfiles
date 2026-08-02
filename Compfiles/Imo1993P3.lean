/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Olympiad 1993, Problem 3

On an infinite chessboard a game is played as follows. At the start n² pieces are arranged
in an n × n block of adjoining squares, one piece on each square. A move in the game is a jump
in a horizontal or vertical direction over an adjacent occupied square to an unoccupied square
immediately beyond. The piece which has been jumped over is removed. Find those values of n
for which the game can end with only one piece remaining on the board.
-/

namespace Imo1993P3

open Finset

/-- The four unit directions in which a jump is allowed. -/
abbrev dirs : Finset (ℤ × ℤ) := {(1, 0), (-1, 0), (0, 1), (0, -1)}

/-- The initial position: an n × n block of occupied squares. -/
noncomputable def initPos (n : ℕ) : Finset (ℤ × ℤ) := Ico 0 (n : ℤ) ×ˢ Ico 0 (n : ℤ)

lemma mem_initPos {n : ℕ} {c : ℤ × ℤ} :
    c ∈ initPos n ↔ 0 ≤ c.1 ∧ c.1 < (n : ℤ) ∧ 0 ≤ c.2 ∧ c.2 < (n : ℤ) := by
  simp [initPos, Finset.mem_product, Finset.mem_Ico]
  omega

/-- A single move: the piece at `c` jumps over the adjacent piece at `c + d`
 onto the empty square `c + d + d`; the jumped-over piece is removed. -/
def IsMove (s s' : Finset (ℤ × ℤ)) : Prop :=
  ∃ c d : ℤ × ℤ, d ∈ dirs ∧ c ∈ s ∧ c + d ∈ s ∧ c + d + d ∉ s ∧
    s' = insert (c + d + d) ((s.erase c).erase (c + d))

/-- Reachability by a sequence of moves. -/
inductive Reachable : Finset (ℤ × ℤ) → Finset (ℤ × ℤ) → Prop
  | refl (s) : Reachable s s
  | step {s t r : Finset (ℤ × ℤ)} : IsMove s t → Reachable t r → Reachable s r

theorem Reachable.trans {s t r : Finset (ℤ × ℤ)} (h1 : Reachable s t) :
    Reachable t r → Reachable s r := by
  induction h1 with
  | refl => exact id
  | step hm hr ih => exact fun h2 => Reachable.step hm (ih h2)

/-- The game is solvable for `n` if the n × n block can be reduced to a single piece. -/
def Solvable (n : ℕ) : Prop := ∃ c : ℤ × ℤ, Reachable (initPos n) {c}

determine SolutionSet : Set ℕ := {n | 0 < n ∧ ¬ 3 ∣ n}

-- snip begin

/-! ## The parity invariant (impossibility for `3 ∣ n`) -/

/-- Weight functions on the exponents: cells with `(i + j) % 3 = r` get weight
 `1` for the two classes in question and `0` for the remaining one. -/
def g1 (k : ℤ) : ZMod 2 := if k % 3 = 2 then 0 else 1

def g2 (k : ℤ) : ZMod 2 := if k % 3 = 0 then 0 else 1

/-- The total weight of a position. -/
def Wt (g : ℤ → ZMod 2) (s : Finset (ℤ × ℤ)) : ZMod 2 := ∑ c ∈ s, g (c.1 + c.2)

lemma g1_sum3 (t : ℤ) : g1 t + g1 (t + 1) + g1 (t + 2) = 0 := by
  have e1 : (t + 1) % 3 = (t % 3 + 1) % 3 := by omega
  have e2 : (t + 2) % 3 = (t % 3 + 2) % 3 := by omega
  have h : t % 3 = 0 ∨ t % 3 = 1 ∨ t % 3 = 2 := by omega
  rcases h with h | h | h <;> simp only [g1, h, e1, e2] <;> norm_num <;> decide

lemma g2_sum3 (t : ℤ) : g2 t + g2 (t + 1) + g2 (t + 2) = 0 := by
  have e1 : (t + 1) % 3 = (t % 3 + 1) % 3 := by omega
  have e2 : (t + 2) % 3 = (t % 3 + 2) % 3 := by omega
  have h : t % 3 = 0 ∨ t % 3 = 1 ∨ t % 3 = 2 := by omega
  rcases h with h | h | h <;> simp only [g2, h, e1, e2] <;> norm_num <;> decide

lemma zmod2_self_add (x : ZMod 2) : x + x = 0 := by
  have htwo : (2 : ZMod 2) = 0 := by decide
  rw [← two_mul, htwo, zero_mul]

/-- A move changes the weight by `g x + g (x+δ) + g (x+2δ) = 0`. -/
lemma Wt_move {g : ℤ → ZMod 2} (hg : ∀ t : ℤ, g t + g (t + 1) + g (t + 2) = 0)
    {s s' : Finset (ℤ × ℤ)} (h : IsMove s s') : Wt g s' = Wt g s := by
  obtain ⟨c, d, hd, hc, hcd, hn, rfl⟩ := h
  obtain ⟨c1, c2⟩ := c
  obtain ⟨d1, d2⟩ := d
  simp only [Prod.mk_add_mk] at hc hcd hn ⊢
  have hδ : d1 + d2 = 1 ∨ d1 + d2 = -1 := by
    simp only [dirs, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hd
    rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num
  have hne1 : ((c1 + d1, c2 + d2) : ℤ × ℤ) ≠ ((c1, c2) : ℤ × ℤ) := by
    intro h
    injection h with h1 h2
    omega
  have hm2 : ((c1 + d1, c2 + d2) : ℤ × ℤ) ∈ s.erase ((c1, c2) : ℤ × ℤ) :=
    Finset.mem_erase.mpr ⟨hne1, hcd⟩
  have hnm : ((c1 + d1 + d1, c2 + d2 + d2) : ℤ × ℤ) ∉
      (s.erase ((c1, c2) : ℤ × ℤ)).erase ((c1 + d1, c2 + d2) : ℤ × ℤ) :=
    fun hh => hn (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hh))
  have e1 := Finset.sum_erase_add _ (fun c : ℤ × ℤ => g (c.1 + c.2)) hc
  have e2 := Finset.sum_erase_add _ (fun c : ℤ × ℤ => g (c.1 + c.2)) hm2
  have key : g (c1 + c2) + g (c1 + d1 + (c2 + d2)) + g (c1 + d1 + d1 + (c2 + d2 + d2)) = 0 := by
    rw [show c1 + d1 + (c2 + d2) = (c1 + c2) + (d1 + d2) by ring,
      show c1 + d1 + d1 + (c2 + d2 + d2) = (c1 + c2) + (d1 + d2) + (d1 + d2) by ring]
    rcases hδ with h | h
    · rw [h, show (c1 + c2) + 1 + 1 = (c1 + c2) + 2 by ring]
      exact hg _
    · have hgg := hg ((c1 + c2) - 2)
      rw [show (c1 + c2) - 2 + 2 = c1 + c2 by ring] at hgg
      rw [h, show (c1 + c2) + -1 + -1 = (c1 + c2) - 2 by ring,
        show (c1 + c2) + -1 = (c1 + c2) - 2 + 1 by ring]
      linear_combination hgg
  simp only [Wt]
  rw [Finset.sum_insert hnm]
  dsimp only at e1 e2 ⊢
  rw [← e1, ← e2]
  have key2 : g (c1 + d1 + d1 + (c2 + d2 + d2)) = g (c1 + c2) + g (c1 + d1 + (c2 + d2)) := by
    calc g (c1 + d1 + d1 + (c2 + d2 + d2))
        = g (c1 + d1 + d1 + (c2 + d2 + d2)) +
            ((g (c1 + c2) + g (c1 + d1 + (c2 + d2))) +
              (g (c1 + c2) + g (c1 + d1 + (c2 + d2)))) := by
          rw [zmod2_self_add, add_zero]
      _ = (g (c1 + c2) + g (c1 + d1 + (c2 + d2)) + g (c1 + d1 + d1 + (c2 + d2 + d2))) +
            (g (c1 + c2) + g (c1 + d1 + (c2 + d2))) := by ring
      _ = 0 + (g (c1 + c2) + g (c1 + d1 + (c2 + d2))) := by rw [key]
      _ = g (c1 + c2) + g (c1 + d1 + (c2 + d2)) := by rw [zero_add]
  rw [key2]
  ring

lemma Wt_reachable {g : ℤ → ZMod 2} (hg : ∀ t : ℤ, g t + g (t + 1) + g (t + 2) = 0)
    {s t : Finset (ℤ × ℤ)} (h : Reachable s t) : Wt g s = Wt g t := by
  induction h with
  | refl => rfl
  | step hm _ ih => exact (Wt_move hg hm).symm.trans ih

/-- The sum of a period-3 weight with zero triple-sum over `3m` consecutive integers is zero. -/
lemma gsum_interval {g : ℤ → ZMod 2} (hg : ∀ t : ℤ, g t + g (t + 1) + g (t + 2) = 0)
    (a : ℤ) (m : ℕ) : ∑ k ∈ Finset.Ico a (a + 3 * (m : ℤ)), g k = 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hcast : (3 : ℤ) * ((m + 1 : ℕ) : ℤ) = 3 * (m : ℤ) + 3 := by push_cast; ring
    have hsplit : Finset.Ico a (a + 3 * (m : ℤ) + 3) =
        Finset.Ico a (a + 3 * (m : ℤ)) ∪ Finset.Ico (a + 3 * (m : ℤ)) (a + 3 * (m : ℤ) + 3) :=
      (Finset.Ico_union_Ico_eq_Ico
        (show a ≤ a + 3 * (m : ℤ) by have := Int.natCast_nonneg m; linarith)
        (show a + 3 * (m : ℤ) ≤ a + 3 * (m : ℤ) + 3 by linarith)).symm
    rw [hcast, show a + (3 * (m : ℤ) + 3) = a + 3 * (m : ℤ) + 3 by ring, hsplit,
      Finset.sum_union ?hdisj, ih, zero_add]
    · have hset : Finset.Ico (a + 3 * (m : ℤ)) (a + 3 * (m : ℤ) + 3) =
          {a + 3 * (m : ℤ), a + 3 * (m : ℤ) + 1, a + 3 * (m : ℤ) + 2} := by
        ext x
        simp only [Finset.mem_Ico, Finset.mem_insert, Finset.mem_singleton]
        omega
      rw [hset,
        Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
        Finset.sum_insert (by simp only [Finset.mem_singleton]; omega), Finset.sum_singleton,
        ← add_assoc]
      exact hg _
    · rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [Finset.mem_Ico] at hx1 hx2
      omega

/-- The weight of the initial `3m × 3m` block is zero. -/
lemma Wt_init {g : ℤ → ZMod 2} (hg : ∀ t : ℤ, g t + g (t + 1) + g (t + 2) = 0) (m : ℕ) :
    Wt g (initPos (3 * m)) = 0 := by
  have hN : ((3 * m : ℕ) : ℤ) = 3 * (m : ℤ) := by push_cast; ring
  simp only [Wt, initPos, hN]
  rw [Finset.sum_product]
  apply Finset.sum_eq_zero
  intro i _
  show ∑ j ∈ Finset.Ico 0 (3 * (m : ℤ)), g (i + j) = 0
  rw [Finset.sum_Ico_add, show (0 : ℤ) + i = i by ring,
    show 3 * (m : ℤ) + i = i + 3 * (m : ℤ) by ring]
  exact gsum_interval hg i m

/-- If `3 ∣ n` the game cannot end with one piece: the two weights of the initial
 block are `(0, 0)`, but the weights of a single piece are never `(0, 0)`. -/
lemma not_solvable_of_three_dvd {n : ℕ} (h3 : 3 ∣ n) : ¬ Solvable n := by
  obtain ⟨m, rfl⟩ := h3
  rintro ⟨c, hc⟩
  have h1 := Wt_reachable g1_sum3 hc
  have h2 := Wt_reachable g2_sum3 hc
  rw [Wt_init g1_sum3 m] at h1
  rw [Wt_init g2_sum3 m] at h2
  simp only [Wt, Finset.sum_singleton] at h1 h2
  have hx : (c.1 + c.2) % 3 = 2 := by
    simp only [g1] at h1
    split_ifs at h1 with hh
    · exact hh
    · exact absurd h1.symm (by decide)
  simp only [g2, hx] at h2
  norm_num at h2

/-! ## The purge lemma (three pieces in a line can be removed using a catalyst) -/

/-- Arithmetic facts about two perpendicular unit directions. -/
lemma unit_facts {u w : ℤ × ℤ} (hu : u ∈ dirs) (hw : w ∈ dirs)
    (hperp : u.1 * w.1 + u.2 * w.2 = 0) :
    (u.1 ≠ 0 ∨ u.2 ≠ 0) ∧ (w.1 ≠ 0 ∨ w.2 ≠ 0) ∧ ¬ (u.1 = w.1 ∧ u.2 = w.2) ∧
      ¬ (u.1 = -w.1 ∧ u.2 = -w.2) ∧ ¬ (u.1 + u.1 = w.1 ∧ u.2 + u.2 = w.2) ∧
      ¬ (u.1 + u.1 = -w.1 ∧ u.2 + u.2 = -w.2) := by
  simp only [dirs, Finset.mem_insert, Finset.mem_singleton] at hu hw
  rcases hu with rfl | rfl | rfl | rfl <;>
    rcases hw with rfl | rfl | rfl | rfl <;> simp at hperp ⊢

/-- The key purge: three consecutive pieces `p, p + u, p + u + u` in a line can be
 removed from the board (everything else unchanged) using a catalyst piece at `p + w`
 provided the square `p - w` is empty. The sequence is:
 `p + w` jumps over `p` to `p - w`; `p + u + u` jumps over `p + u` to `p`;
 `p - w` jumps over `p` to `p + w`. -/
lemma purge {s : Finset (ℤ × ℤ)} {p u w : ℤ × ℤ}
    (hu : u ∈ dirs) (hw : w ∈ dirs) (hperp : u.1 * w.1 + u.2 * w.2 = 0)
    (hp : p ∈ s) (hpu : p + u ∈ s) (hp2 : p + u + u ∈ s) (hpw : p + w ∈ s)
    (hnw : p - w ∉ s) :
    Reachable s (s \ {p, p + u, p + u + u}) := by
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := unit_facts hu hw hperp
  obtain ⟨px, py⟩ := p
  obtain ⟨ne_pw_p, ne_p_mw, ne_p_pw, ne_u_p, ne_u_pw, ne_uu_p, ne_uu_pw, ne_uu_mw, ne_mw_u,
      ne_mw_uu, ne_pw_u, ne_pw_uu, ne_pw_mw⟩ :
      ((px, py) + w ≠ (px, py)) ∧ ((px, py) ≠ (px, py) - w) ∧ ((px, py) ≠ (px, py) + w) ∧
      ((px, py) + u ≠ (px, py)) ∧ ((px, py) + u ≠ (px, py) + w) ∧
      ((px, py) + u + u ≠ (px, py)) ∧ ((px, py) + u + u ≠ (px, py) + w) ∧
      ((px, py) + u + u ≠ (px, py) - w) ∧ ((px, py) - w ≠ (px, py) + u) ∧
      ((px, py) - w ≠ (px, py) + u + u) ∧ ((px, py) + w ≠ (px, py) + u) ∧
      ((px, py) + w ≠ (px, py) + u + u) ∧ ((px, py) + w ≠ (px, py) - w) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [ne_eq, Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
        Prod.fst_neg, Prod.snd_neg] <;> omega
  have m1 : IsMove s (insert ((px, py) - w) ((s.erase ((px, py) + w)).erase (px, py))) := by
    refine ⟨(px, py) + w, -w, ?_, hpw, ?_, ?_, ?_⟩
    · simp only [dirs, Finset.mem_insert, Finset.mem_singleton] at hw ⊢
      rcases hw with rfl | rfl | rfl | rfl <;> simp
    · rw [show (px, py) + w + -w = (px, py) by abel]
      exact hp
    · rw [show (px, py) + w + -w + -w = (px, py) - w by abel]
      exact hnw
    · rw [show (px, py) + w + -w + -w = (px, py) - w by abel,
        show (px, py) + w + -w = (px, py) by abel]
  have m2 : IsMove (insert ((px, py) - w) ((s.erase ((px, py) + w)).erase (px, py)))
      (insert (px, py) (((insert ((px, py) - w) ((s.erase ((px, py) + w)).erase (px, py))).erase
        ((px, py) + u + u)).erase ((px, py) + u))) := by
    refine ⟨(px, py) + u + u, -u, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [dirs, Finset.mem_insert, Finset.mem_singleton] at hu ⊢
      rcases hu with rfl | rfl | rfl | rfl <;> simp
    · rw [Finset.mem_insert]
      right
      rw [Finset.mem_erase, Finset.mem_erase]
      exact ⟨ne_uu_p, ne_uu_pw, hp2⟩
    · rw [show (px, py) + u + u + -u = (px, py) + u by abel, Finset.mem_insert]
      right
      rw [Finset.mem_erase, Finset.mem_erase]
      exact ⟨ne_u_p, ne_u_pw, hpu⟩
    · rw [show (px, py) + u + u + -u + -u = (px, py) by abel, Finset.mem_insert]
      intro hh
      rcases hh with h | h
      · exact ne_p_mw h
      · rw [Finset.mem_erase] at h
        exact h.1 rfl
    · rw [show (px, py) + u + u + -u + -u = (px, py) by abel,
        show (px, py) + u + u + -u = (px, py) + u by abel]
  have m3 : IsMove (insert (px, py) (((insert ((px, py) - w) ((s.erase ((px, py) + w)).erase
        (px, py))).erase ((px, py) + u + u)).erase ((px, py) + u)))
      (insert ((px, py) + w) (((insert (px, py) (((insert ((px, py) - w) ((s.erase ((px, py) + w)).erase
        (px, py))).erase ((px, py) + u + u)).erase ((px, py) + u))).erase ((px, py) - w)).erase
        (px, py))) := by
    refine ⟨(px, py) - w, w, hw, ?_, ?_, ?_, ?_⟩
    · rw [Finset.mem_insert]
      right
      rw [Finset.mem_erase, Finset.mem_erase]
      exact ⟨ne_mw_u, ne_mw_uu, by rw [Finset.mem_insert]; left; rfl⟩
    · rw [show (px, py) - w + w = (px, py) by abel, Finset.mem_insert]
      left
      rfl
    · rw [show (px, py) - w + w + w = (px, py) + w by abel, Finset.mem_insert]
      intro hh
      rcases hh with h | h
      · exact ne_pw_p h
      rw [Finset.mem_erase, Finset.mem_erase, Finset.mem_insert] at h
      rcases h with ⟨-, ⟨-, h | h⟩⟩
      · exact ne_pw_mw h
      rw [Finset.mem_erase, Finset.mem_erase] at h
      exact h.2.1 rfl
    · rw [show (px, py) - w + w + w = (px, py) + w by abel,
        show (px, py) - w + w = (px, py) by abel]
  have h123 : Reachable s (insert ((px, py) + w) (((insert (px, py) (((insert ((px, py) - w)
      ((s.erase ((px, py) + w)).erase (px, py))).erase ((px, py) + u + u)).erase
      ((px, py) + u))).erase ((px, py) - w)).erase (px, py))) :=
    Reachable.step m1 (Reachable.step m2 (Reachable.step m3 (Reachable.refl _)))
  have final : insert ((px, py) + w) (((insert (px, py) (((insert ((px, py) - w)
      ((s.erase ((px, py) + w)).erase (px, py))).erase ((px, py) + u + u)).erase
      ((px, py) + u))).erase ((px, py) - w)).erase (px, py)) =
      s \ {(px, py), (px, py) + u, (px, py) + u + u} := by
    have ec : ∀ (t : Finset (ℤ × ℤ)) (a b : ℤ × ℤ), (t.erase a).erase b = (t.erase b).erase a := by
      intro t a b
      ext x
      simp only [Finset.mem_erase]
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h2, h1, h3⟩
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h2, h1, h3⟩
    have hn1 : (px, py) ∉ (((insert ((px, py) - w) ((s.erase ((px, py) + w)).erase (px, py))).erase
        ((px, py) + u + u)).erase ((px, py) + u)).erase ((px, py) - w) := by
      intro h
      rw [Finset.mem_erase] at h
      obtain ⟨-, h⟩ := h
      rw [Finset.mem_erase, Finset.mem_erase, Finset.mem_insert] at h
      obtain ⟨-, ⟨-, h | h⟩⟩ := h
      · exact ne_p_mw h
      rw [Finset.mem_erase, Finset.mem_erase] at h
      exact h.1 rfl
    have hn2 : (px, py) - w ∉ (((s.erase ((px, py) + w)).erase (px, py)).erase
        ((px, py) + u + u)).erase ((px, py) + u) := by
      intro h
      rw [Finset.mem_erase, Finset.mem_erase, Finset.mem_erase, Finset.mem_erase] at h
      exact hnw h.2.2.2.2
    rw [Finset.erase_insert_of_ne ne_p_mw, Finset.erase_insert hn1,
      Finset.erase_insert_of_ne ne_mw_uu, Finset.erase_insert_of_ne ne_mw_u,
      Finset.erase_insert hn2, ec _ ((px, py) + u + u) ((px, py) + u), ec _ (px, py) ((px, py) + u),
      ec _ ((px, py) + w) ((px, py) + u), ec _ ((px, py) + w) (px, py),
      ec _ ((px, py) + w) ((px, py) + u + u), ec _ ((px, py) + u) (px, py),
      Finset.insert_erase (Finset.mem_erase.mpr ⟨ne_pw_uu, Finset.mem_erase.mpr
        ⟨ne_pw_u, Finset.mem_erase.mpr ⟨ne_pw_p, hpw⟩⟩⟩)]
    ext x
    simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨h4, fun h => h.elim (fun hh => h3 hh) (fun h => h.elim (fun hh => h2 hh)
        (fun hh => h1 hh))⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun hh => h2 (Or.inr (Or.inr hh)), fun hh => h2 (Or.inr (Or.inl hh)),
        fun hh => h2 (Or.inl hh), h1⟩
  rw [final] at h123
  exact h123

/-! ## The sweep: reducing an (n+3) × (n+3) block to an n × n block -/

/-- After clearing `k` columns of the top strip: the board below row `n` plus
 columns `k, k+1, ...` of the whole square. -/
noncomputable def stateA (n k : ℕ) : Finset (ℤ × ℤ) :=
  (initPos (n + 3)).filter (fun c => c.2 < (n : ℤ) ∨ (k : ℤ) ≤ c.1)

/-- After clearing `k` rows of the right strip. -/
noncomputable def stateB (n k : ℕ) : Finset (ℤ × ℤ) :=
  (initPos (n + 3)).filter
    (fun c => (c.1 < (n : ℤ) ∧ c.2 < (n : ℤ)) ∨ ((n : ℤ) ≤ c.1 ∧ c.2 ≤ (n : ℤ) + 2 - (k : ℤ)))

/-- After clearing the bottom of column `n + 2` as well. -/
noncomputable def stateC (n : ℕ) : Finset (ℤ × ℤ) :=
  (initPos (n + 3)).filter
    (fun c => (c.1 < (n : ℤ) ∧ c.2 < (n : ℤ)) ∨ ((n : ℤ) ≤ c.1 ∧ c.1 ≤ (n : ℤ) + 1 ∧ c.2 ≤ 2))

/-- After clearing the bottom of columns `n + 1, n + 2`. -/
noncomputable def stateD (n : ℕ) : Finset (ℤ × ℤ) :=
  (initPos (n + 3)).filter
    (fun c => (c.1 < (n : ℤ) ∧ c.2 < (n : ℤ)) ∨ (c.1 = (n : ℤ) ∧ c.2 ≤ 2))

/-- One step of phase 1: purge the vertical triple in column `k` of the top strip,
 using the piece at `(k+1, n)` as catalyst. -/
lemma phase1_step (n k : ℕ) (hk : k < n) : Reachable (stateA n k) (stateA n (k + 1)) := by
  have h := purge (s := stateA n k) (p := ((k : ℤ), (n : ℤ))) (u := ((0 : ℤ), (1 : ℤ)))
    (w := ((1 : ℤ), (0 : ℤ))) (by decide) (by decide) (by decide)
    (by simp only [stateA, mem_initPos, Finset.mem_filter, Prod.mk_add_mk, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]; omega) (by simp only [stateA, mem_initPos, Finset.mem_filter, Prod.mk_add_mk, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]; omega)
    (by simp only [stateA, mem_initPos, Finset.mem_filter, Prod.mk_add_mk, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]; omega) (by simp only [stateA, mem_initPos, Finset.mem_filter, Prod.mk_add_mk, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]; omega)
    (by simp only [stateA, mem_initPos, Finset.mem_filter, Prod.mk_add_mk, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]; omega)
  rw [show stateA n (k + 1) = stateA n k \ {((k : ℤ), (n : ℤ)), ((k : ℤ), (n : ℤ)) + ((0 : ℤ), (1 : ℤ)),
      ((k : ℤ), (n : ℤ)) + ((0 : ℤ), (1 : ℤ)) + ((0 : ℤ), (1 : ℤ))} by
    ext ⟨a, b⟩
    simp only [stateA, mem_initPos, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_insert,
      Finset.mem_singleton, ne_eq, Prod.ext_iff, Prod.mk_add_mk, Prod.fst_add, Prod.snd_add,
      Prod.fst_sub, Prod.snd_sub]
    omega]
  exact h

/-- Phase 1: clear the top strip, one column at a time. -/
lemma phase1 (n : ℕ) (k : ℕ) (hk : k ≤ n) : Reachable (initPos (n + 3)) (stateA n k) := by
  induction k with
  | zero =>
    rw [show stateA n 0 = initPos (n + 3) by
      ext ⟨a, b⟩
      simp only [stateA, mem_initPos, Finset.mem_filter, Prod.mk_add_mk, Prod.fst_add,
        Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
      omega]
    exact Reachable.refl _
  | succ k ih => exact (ih (Nat.le_of_succ_le hk)).trans (phase1_step n k hk)

/-- One step of phase 2a: purge the horizontal triple in row `n + 2 - k` of the right
 strip, using the piece at `(n, n + 1 - k)` as catalyst. -/
lemma phase2a_step (n k : ℕ) (hk : k < n) : Reachable (stateB n k) (stateB n (k + 1)) := by
  have h := purge (s := stateB n k) (p := ((n : ℤ), (n : ℤ) + 2 - (k : ℤ))) (u := ((1 : ℤ), (0 : ℤ)))
    (w := ((0 : ℤ), (-1 : ℤ))) (by decide) (by decide) (by decide)
    (by simp only [stateB, mem_initPos, Finset.mem_filter, Prod.mk_add_mk, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]; omega) (by simp only [stateB, mem_initPos, Finset.mem_filter, Prod.mk_add_mk, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]; omega)
    (by simp only [stateB, mem_initPos, Finset.mem_filter, Prod.mk_add_mk, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]; omega) (by simp only [stateB, mem_initPos, Finset.mem_filter, Prod.mk_add_mk, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]; omega)
    (by simp only [stateB, mem_initPos, Finset.mem_filter, Prod.mk_add_mk, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]; omega)
  rw [show stateB n (k + 1) = stateB n k \ {((n : ℤ), (n : ℤ) + 2 - (k : ℤ)),
      ((n : ℤ), (n : ℤ) + 2 - (k : ℤ)) + ((1 : ℤ), (0 : ℤ)),
      ((n : ℤ), (n : ℤ) + 2 - (k : ℤ)) + ((1 : ℤ), (0 : ℤ)) + ((1 : ℤ), (0 : ℤ))} by
    ext ⟨a, b⟩
    simp only [stateB, mem_initPos, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_insert,
      Finset.mem_singleton, ne_eq, Prod.ext_iff, Prod.mk_add_mk, Prod.fst_add, Prod.snd_add,
      Prod.fst_sub, Prod.snd_sub]
    omega]
  exact h

/-- Phase 2a: clear the right strip rows from top to bottom, down to row 3. -/
lemma phase2a (n : ℕ) (k : ℕ) (hk : k ≤ n) : Reachable (initPos (n + 3)) (stateB n k) := by
  induction k with
  | zero =>
    rw [show stateB n 0 = stateA n n by
      ext ⟨a, b⟩
      simp only [stateA, stateB, mem_initPos, Finset.mem_filter, Prod.mk_add_mk, Prod.fst_add,
        Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
      omega]
    exact phase1 n n le_rfl
  | succ k ih => exact (ih (Nat.le_of_succ_le hk)).trans (phase2a_step n k hk)

/-- Phase 2b: clear the remaining 3 × 3 corner, finishing with a purge whose
 catalyst lies inside the target n × n block. -/
lemma phase2b (n : ℕ) (hn : 1 ≤ n) : Reachable (stateB n n) (initPos n) := by
  have h1 := purge (s := stateB n n) (p := (((n : ℤ) + 2), (0 : ℤ))) (u := ((0 : ℤ), (1 : ℤ)))
    (w := ((-1 : ℤ), (0 : ℤ))) (by decide) (by decide) (by decide)
    (by simp only [stateB, mem_initPos, Finset.mem_filter, Prod.mk_add_mk, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]; omega) (by simp only [stateB, mem_initPos, Finset.mem_filter, Prod.mk_add_mk, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]; omega)
    (by simp only [stateB, mem_initPos, Finset.mem_filter, Prod.mk_add_mk, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]; omega) (by simp only [stateB, mem_initPos, Finset.mem_filter, Prod.mk_add_mk, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]; omega)
    (by simp only [stateB, mem_initPos, Finset.mem_filter, Prod.mk_add_mk, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]; omega)
  rw [show stateB n n \ {((n : ℤ) + 2, (0 : ℤ)), ((n : ℤ) + 2, (0 : ℤ)) + ((0 : ℤ), (1 : ℤ)),
      ((n : ℤ) + 2, (0 : ℤ)) + ((0 : ℤ), (1 : ℤ)) + ((0 : ℤ), (1 : ℤ))} = stateC n by
    ext ⟨a, b⟩
    simp only [stateB, stateC, mem_initPos, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_insert,
      Finset.mem_singleton, ne_eq, Prod.ext_iff, Prod.mk_add_mk, Prod.fst_add, Prod.snd_add,
      Prod.fst_sub, Prod.snd_sub]
    omega] at h1
  have h2 := purge (s := stateC n) (p := (((n : ℤ) + 1), (0 : ℤ))) (u := ((0 : ℤ), (1 : ℤ)))
    (w := ((-1 : ℤ), (0 : ℤ))) (by decide) (by decide) (by decide)
    (by simp only [stateC, mem_initPos, Finset.mem_filter, Prod.mk_add_mk, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]; omega) (by simp only [stateC, mem_initPos, Finset.mem_filter, Prod.mk_add_mk, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]; omega)
    (by simp only [stateC, mem_initPos, Finset.mem_filter, Prod.mk_add_mk, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]; omega) (by simp only [stateC, mem_initPos, Finset.mem_filter, Prod.mk_add_mk, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]; omega)
    (by simp only [stateC, mem_initPos, Finset.mem_filter, Prod.mk_add_mk, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]; omega)
  rw [show stateC n \ {((n : ℤ) + 1, (0 : ℤ)), ((n : ℤ) + 1, (0 : ℤ)) + ((0 : ℤ), (1 : ℤ)),
      ((n : ℤ) + 1, (0 : ℤ)) + ((0 : ℤ), (1 : ℤ)) + ((0 : ℤ), (1 : ℤ))} = stateD n by
    ext ⟨a, b⟩
    simp only [stateC, stateD, mem_initPos, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_insert,
      Finset.mem_singleton, ne_eq, Prod.ext_iff, Prod.mk_add_mk, Prod.fst_add, Prod.snd_add,
      Prod.fst_sub, Prod.snd_sub]
    omega] at h2
  have h3 := purge (s := stateD n) (p := ((n : ℤ), (0 : ℤ))) (u := ((0 : ℤ), (1 : ℤ)))
    (w := ((-1 : ℤ), (0 : ℤ))) (by decide) (by decide) (by decide)
    (by simp only [stateD, mem_initPos, Finset.mem_filter, Prod.mk_add_mk, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, true_and, and_true, or_true, or_false, false_or, and_false, false_and, true_or, not_true, not_false]; omega) (by simp only [stateD, mem_initPos, Finset.mem_filter, Prod.mk_add_mk, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, true_and, and_true, or_true, or_false, false_or, and_false, false_and, true_or, not_true, not_false]; omega)
    (by simp only [stateD, mem_initPos, Finset.mem_filter, Prod.mk_add_mk, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]; omega) (by simp only [stateD, mem_initPos, Finset.mem_filter, Prod.mk_add_mk, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]; omega)
    (by simp only [stateD, mem_initPos, Finset.mem_filter, Prod.mk_add_mk, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]; omega)
  rw [show stateD n \ {((n : ℤ), (0 : ℤ)), ((n : ℤ), (0 : ℤ)) + ((0 : ℤ), (1 : ℤ)),
      ((n : ℤ), (0 : ℤ)) + ((0 : ℤ), (1 : ℤ)) + ((0 : ℤ), (1 : ℤ))} = initPos n by
    ext ⟨a, b⟩
    simp only [stateD, mem_initPos, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_insert,
      Finset.mem_singleton, ne_eq, Prod.ext_iff, Prod.mk_add_mk, Prod.fst_add, Prod.snd_add,
      Prod.fst_sub, Prod.snd_sub]
    omega] at h3
  exact h1.trans (h2.trans h3)

/-- Reduction: if the game is solvable for `n ≥ 1`, it is solvable for `n + 3`. -/
lemma reduction (n : ℕ) (hn : 1 ≤ n) (h : Solvable n) : Solvable (n + 3) := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, (phase2a n n le_rfl).trans ((phase2b n hn).trans hc)⟩

/-- The 1 × 1 board is trivially solved. -/
lemma solvable_one : Solvable 1 := by
  refine ⟨((0 : ℤ), (0 : ℤ)), ?_⟩
  rw [show initPos 1 = {((0 : ℤ), (0 : ℤ))} by
    ext ⟨a, b⟩
    simp only [mem_initPos, Finset.mem_singleton, ne_eq, Prod.ext_iff]
    omega]
  exact Reachable.refl _

/-- The 2 × 2 board is solved in three moves. -/
lemma solvable_two : Solvable 2 := by
  refine ⟨((2 : ℤ), (2 : ℤ)), ?_⟩
  have m1 : IsMove (initPos 2)
      (insert ((2 : ℤ), (0 : ℤ)) (((initPos 2).erase ((0 : ℤ), (0 : ℤ))).erase ((1 : ℤ), (0 : ℤ)))) := by
    refine ⟨((0 : ℤ), (0 : ℤ)), ((1 : ℤ), (0 : ℤ)), by decide, ?_, ?_, ?_, ?_⟩
    · simp only [mem_initPos, Prod.mk_add_mk]; omega
    · simp only [mem_initPos, Prod.mk_add_mk]; omega
    · simp only [mem_initPos, Prod.mk_add_mk]; omega
    · ext ⟨a, b⟩
      simp only [mem_initPos, Finset.mem_insert, Finset.mem_erase, ne_eq, Prod.ext_iff,
        Prod.mk_add_mk, Prod.fst_add, Prod.snd_add, Finset.mem_singleton]
      omega
  have m2 : IsMove
      (insert ((2 : ℤ), (0 : ℤ)) (((initPos 2).erase ((0 : ℤ), (0 : ℤ))).erase ((1 : ℤ), (0 : ℤ))))
      (insert ((2 : ℤ), (1 : ℤ)) (((insert ((2 : ℤ), (0 : ℤ)) (((initPos 2).erase
        ((0 : ℤ), (0 : ℤ))).erase ((1 : ℤ), (0 : ℤ)))).erase ((0 : ℤ), (1 : ℤ))).erase
        ((1 : ℤ), (1 : ℤ)))) := by
    refine ⟨((0 : ℤ), (1 : ℤ)), ((1 : ℤ), (0 : ℤ)), by decide, ?_, ?_, ?_, ?_⟩
    · simp only [mem_initPos, Finset.mem_insert, Finset.mem_erase, ne_eq, Prod.ext_iff,
        Prod.mk_add_mk, Prod.fst_add, Prod.snd_add]; omega
    · simp only [mem_initPos, Finset.mem_insert, Finset.mem_erase, ne_eq, Prod.ext_iff,
        Prod.mk_add_mk, Prod.fst_add, Prod.snd_add]; omega
    · simp only [mem_initPos, Finset.mem_insert, Finset.mem_erase, ne_eq, Prod.ext_iff,
        Prod.mk_add_mk, Prod.fst_add, Prod.snd_add]; omega
    · ext ⟨a, b⟩
      simp only [mem_initPos, Finset.mem_insert, Finset.mem_erase, ne_eq, Prod.ext_iff,
        Prod.mk_add_mk, Prod.fst_add, Prod.snd_add, Finset.mem_singleton]
      omega
  have m3 : IsMove
      (insert ((2 : ℤ), (1 : ℤ)) (((insert ((2 : ℤ), (0 : ℤ)) (((initPos 2).erase
        ((0 : ℤ), (0 : ℤ))).erase ((1 : ℤ), (0 : ℤ)))).erase ((0 : ℤ), (1 : ℤ))).erase
        ((1 : ℤ), (1 : ℤ))))
      {((2 : ℤ), (2 : ℤ))} := by
    refine ⟨((2 : ℤ), (0 : ℤ)), ((0 : ℤ), (1 : ℤ)), by decide, ?_, ?_, ?_, ?_⟩
    · simp only [mem_initPos, Finset.mem_insert, Finset.mem_erase, ne_eq, Prod.ext_iff,
        Finset.mem_singleton, Prod.mk_add_mk, Prod.fst_add, Prod.snd_add, true_and, and_true, or_true, or_false, false_or, and_false, false_and, true_or, not_true, not_false]; omega
    · simp only [mem_initPos, Finset.mem_insert, Finset.mem_erase, ne_eq, Prod.ext_iff,
        Finset.mem_singleton, Prod.mk_add_mk, Prod.fst_add, Prod.snd_add, true_and, and_true, or_true, or_false, false_or, and_false, false_and, true_or, not_true, not_false]; omega
    · simp only [mem_initPos, Finset.mem_insert, Finset.mem_erase, ne_eq, Prod.ext_iff,
        Prod.mk_add_mk, Prod.fst_add, Prod.snd_add]; omega
    · ext ⟨a, b⟩
      simp only [mem_initPos, Finset.mem_insert, Finset.mem_erase, ne_eq, Prod.ext_iff,
        Prod.mk_add_mk, Prod.fst_add, Prod.snd_add, Finset.mem_singleton]
      omega
  exact Reachable.step m1 (Reachable.step m2 (Reachable.step m3 (Reachable.refl _)))

lemma solvable_three_mul_add_one (m : ℕ) : Solvable (3 * m + 1) := by
  induction m with
  | zero => exact solvable_one
  | succ m ih =>
    have h := reduction (3 * m + 1) (by omega) ih
    rw [show 3 * m + 1 + 3 = 3 * (m + 1) + 1 by ring] at h
    exact h

lemma solvable_three_mul_add_two (m : ℕ) : Solvable (3 * m + 2) := by
  induction m with
  | zero => exact solvable_two
  | succ m ih =>
    have h := reduction (3 * m + 2) (by omega) ih
    rw [show 3 * m + 2 + 3 = 3 * (m + 1) + 2 by ring] at h
    exact h

lemma solvable_of_pos_not_three_dvd (n : ℕ) (h0 : 0 < n) (h3 : ¬ 3 ∣ n) : Solvable n := by
  have hmod : n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases hmod with h | h
  · have e : n = 3 * (n / 3) + 1 := by omega
    rw [e]
    exact solvable_three_mul_add_one (n / 3)
  · have e : n = 3 * (n / 3) + 2 := by omega
    rw [e]
    exact solvable_three_mul_add_two (n / 3)

-- snip end

problem imo1993_p3 (n : ℕ) : Solvable n ↔ n ∈ SolutionSet := by
  simp only [SolutionSet, Set.mem_setOf_eq]
  constructor
  · intro h
    have h3 : ¬ 3 ∣ n := fun hd => not_solvable_of_three_dvd hd h
    have h0 : 0 < n := by
      by_contra h0
      push_neg at h0
      rw [Nat.le_zero] at h0
      subst h0
      exact h3 ⟨0, by simp⟩
    exact ⟨h0, h3⟩
  · rintro ⟨h0, h3⟩
    exact solvable_of_pos_not_three_dvd n h0 h3

end Imo1993P3
