/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Data.Finset.Fin
public import Mathlib.Data.Nat.SuccPred
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic.Ring
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Olympiad 2017, Problem 5

Fix `N ≥ 1`. A collection of `N (N + 1)` soccer players of distinct heights
stand in a row. Sir Alex wishes to remove `N (N − 1)` players from this row
to obtain a new row of `2N` players in which the following `N` conditions
hold: no one stands between the two tallest players, no one stands between
the third and fourth tallest players, ..., no one stands between the two
shortest players. Prove that this is possible.
-/

namespace Imo2017P5

open Finset

snip begin

/-!
### The combinatorial heart of the proof

We follow the argument from Evan Chen's *IMO 2017 Solution Notes*:
colour the row with `N` colours (height groups), each colour used at least
`N + 1` times. Scan from the left until some colour appears twice; keep that
pair (it becomes adjacent at the far left of the new row), delete everyone
scanned and everyone else with that colour, and apply induction to what
remains.
-/

/-- Prepend the kept pair `s₀ < t₀` in front of the inductively chosen
subsequence `g`. -/
def prepend (N M : ℕ) (s₀ t₀ : Fin M) (g : Fin (2 * N) ↪o Fin M) (x : Fin (2 * N + 2)) :
    Fin M :=
  if h₀ : x.val = 0 then s₀
  else if h₁ : x.val = 1 then t₀
  else g ⟨x.val - 2, by omega⟩

theorem prepend_zero (N M : ℕ) (s₀ t₀ : Fin M) (g : Fin (2 * N) ↪o Fin M)
    (h : 0 < 2 * N + 2) : prepend N M s₀ t₀ g ⟨0, h⟩ = s₀ := by
  unfold prepend
  exact dif_pos rfl

theorem prepend_one (N M : ℕ) (s₀ t₀ : Fin M) (g : Fin (2 * N) ↪o Fin M)
    (h : 1 < 2 * N + 2) : prepend N M s₀ t₀ g ⟨1, h⟩ = t₀ := by
  unfold prepend
  rw [dif_neg (show ¬(1 : ℕ) = 0 by norm_num), dif_pos rfl]

theorem prepend_two (N M : ℕ) (s₀ t₀ : Fin M) (g : Fin (2 * N) ↪o Fin M)
    (x : Fin (2 * N + 2)) (hx : 2 ≤ x.val) :
    prepend N M s₀ t₀ g x = g ⟨x.val - 2, by omega⟩ := by
  unfold prepend
  rw [dif_neg (show ¬x.val = 0 by omega), dif_neg (show ¬x.val = 1 by omega)]

theorem prepend_strictMono (N M : ℕ) {s₀ t₀ : Fin M} (hst : s₀ < t₀)
    (g : Fin (2 * N) ↪o Fin M) (hg : ∀ j, t₀ < g j) :
    StrictMono (prepend N M s₀ t₀ g) := by
  intro x y hxy
  rcases x with ⟨x, hx⟩
  rcases y with ⟨y, hy⟩
  have hxy' : x < y := hxy
  by_cases hx0 : x = 0
  · subst hx0
    by_cases hy1 : y = 1
    · subst hy1
      rw [prepend_zero, prepend_one]
      exact hst
    · have hy2 : 2 ≤ y := by omega
      rw [prepend_zero, prepend_two _ _ _ _ _ _ hy2]
      exact lt_trans hst (hg _)
  · by_cases hx1 : x = 1
    · subst hx1
      have hy2 : 2 ≤ y := by omega
      rw [prepend_one, prepend_two _ _ _ _ _ _ hy2]
      exact hg _
    · have hx2 : 2 ≤ x := by omega
      by_cases hy1 : y = 1
      · exfalso; omega
      · have hy2 : 2 ≤ y := by omega
        rw [prepend_two _ _ _ _ _ _ hx2, prepend_two _ _ _ _ _ _ hy2]
        apply g.strictMono
        show x - 2 < y - 2
        omega

/-- Evan Chen's scan argument, by induction on the number of colours.

Given a row of `M` people coloured by `c : Fin M → Fin N`, every colour
appearing at least `N + 1` times, one can select a subsequence of `2N`
people containing exactly two people of each colour, and such that the two
people of any given colour stand next to each other in the subsequence. -/
theorem aux : ∀ (N M : ℕ) (c : Fin M → Fin N),
    (∀ k, N + 1 ≤ (univ.filter fun i ↦ c i = k).card) →
    ∃ f : Fin (2 * N) ↪o Fin M,
      (∀ k, (univ.filter fun i ↦ c (f i) = k).card = 2) ∧
      ∀ i j, c (f i) = c (f j) → i = j ∨ i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  intro N
  induction N with
  | zero =>
    intro M c _
    exact ⟨OrderEmbedding.ofStrictMono (fun i : Fin 0 ↦ i.elim0) (fun i ↦ i.elim0),
      fun k ↦ k.elim0, fun i ↦ i.elim0⟩
  | succ N ih =>
    intro M c hcard
    -- The row has at least `N + 2` people.
    have hM : N + 2 ≤ M :=
      calc N + 2 ≤ (univ.filter fun i ↦ c i = (0 : Fin (N + 1))).card := hcard 0
        _ ≤ (univ : Finset (Fin M)).card := card_le_card (filter_subset _ _)
        _ = M := by simp
    -- Scanning from the left, two of the first `N + 2` people share a colour.
    obtain ⟨x, -, y, -, hxy, hcxy⟩ :=
      exists_ne_map_eq_of_card_lt_of_maps_to
        (s := (univ : Finset (Fin (N + 2)))) (t := (univ : Finset (Fin (N + 1))))
        (f := fun i ↦ c (i.castLE hM)) (by simp) (fun a _ ↦ mem_univ _)
    have key : ∃ s t : Fin M, s < t ∧ c s = c t := by
      rcases lt_or_gt_of_ne hxy with h | h
      · exact ⟨x.castLE hM, y.castLE hM, h, hcxy⟩
      · exact ⟨y.castLE hM, x.castLE hM, h, hcxy.symm⟩
    -- Take the leftmost repeated second element `t₀`, and its partner `s₀`.
    let S : Finset (Fin M) := univ.filter fun t ↦ ∃ s, s < t ∧ c s = c t
    have hS : S.Nonempty := by
      obtain ⟨s, t, hst, hct⟩ := key
      exact ⟨t, mem_filter.2 ⟨mem_univ _, s, hst, hct⟩⟩
    set t₀ := S.min' hS with ht₀
    obtain ⟨s₀, hs₀, hcs₀⟩ := (mem_filter.1 (min'_mem S hS)).2
    -- All colours strictly before `t₀` are distinct.
    have hA : ∀ i j : Fin M, i < t₀ → j < t₀ → c i = c j → i = j := by
      intro i j hi hj hc
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · have hle := min'_le S j (mem_filter.2 ⟨mem_univ _, i, h, hc⟩)
        exact absurd hle (not_le_of_gt hj)
      · have hle := min'_le S i (mem_filter.2 ⟨mem_univ _, j, h, hc.symm⟩)
        exact absurd hle (not_le_of_gt hi)
    -- The common colour of the kept pair.
    let p : Fin (N + 1) := c s₀
    have hpc : c s₀ = p := rfl
    have hpt₀ : c t₀ = p := hcs₀.symm
    -- The remaining row: positions past `t₀` whose colour is not `p`.
    let R : Finset (Fin M) := univ.filter fun i ↦ t₀ < i ∧ c i ≠ p
    let e : Fin R.card ↪o Fin M := R.orderEmbOfFin rfl
    have he : ∀ i, e i ∈ R := fun i ↦ R.orderEmbOfFin_mem rfl i
    have hsurj : ∀ x ∈ R, ∃ i, e i = x := by
      intro x hx
      have hsub : univ.map e.toEmbedding ⊆ R := by
        intro y hy
        rw [mem_map] at hy
        obtain ⟨i, -, rfl⟩ := hy
        exact he i
      have hcard_eq : (univ.map e.toEmbedding).card = R.card := by
        rw [card_map, card_univ, Fintype.card_fin]
      have hR : univ.map e.toEmbedding = R := eq_of_subset_of_card_le hsub hcard_eq.ge
      rw [← hR] at hx
      rw [mem_map] at hx
      obtain ⟨i, -, hi⟩ := hx
      exact ⟨i, hi⟩
    -- Reindex the remaining colours as `Fin N` via `succAbove`.
    have hne : ∀ i, c (e i) ≠ p := fun i ↦ (mem_filter.1 (he i)).2.2
    let c' : Fin R.card → Fin N := fun i ↦ Classical.choose (Fin.exists_succAbove_eq (hne i))
    have hc' : ∀ i, p.succAbove (c' i) = c (e i) :=
      fun i ↦ Classical.choose_spec (Fin.exists_succAbove_eq (hne i))
    -- Each remaining colour still appears at least `N + 1` times.
    have hcard' : ∀ k : Fin N, N + 1 ≤ (univ.filter fun i ↦ c' i = k).card := by
      intro k
      let q := p.succAbove k
      have hq : q ≠ p := Fin.succAbove_ne _ _
      have hbij : (univ.filter fun i ↦ c' i = k).card =
          (R.filter fun i ↦ c i = q).card := by
        apply Finset.card_bij (fun i _ ↦ e i)
        · intro i hi
          rw [mem_filter] at hi ⊢
          exact ⟨he i, by rw [← hc' i, hi.2]⟩
        · intro i _ j _ hij
          exact e.injective hij
        · intro j hj
          rw [mem_filter] at hj
          obtain ⟨i, hi⟩ := hsurj j hj.1
          refine ⟨i, ?_, hi⟩
          have hsq : p.succAbove (c' i) = p.succAbove k := by rw [hc' i, hi]; exact hj.2
          exact mem_filter.2 ⟨mem_univ _, Fin.succAbove_right_injective hsq⟩
      rw [hbij]
      have hsub2 : univ.filter (fun i ↦ c i = q) ⊆
          (univ.filter fun i ↦ t₀ < i ∧ c i = q) ∪
            (univ.filter fun i ↦ i ≤ t₀ ∧ c i = q) := by
        intro i hi
        rw [mem_filter] at hi
        rcases lt_or_ge t₀ i with h | h
        · exact mem_union_left _ (mem_filter.2 ⟨mem_univ _, h, hi.2⟩)
        · exact mem_union_right _ (mem_filter.2 ⟨mem_univ _, h, hi.2⟩)
      have hsmall : (univ.filter fun i ↦ i ≤ t₀ ∧ c i = q).card ≤ 1 := by
        rw [card_le_one]
        intro a ha b hb
        rw [mem_filter] at ha hb
        have ha' : a < t₀ := by
          rcases ha.2.1.lt_or_eq with h | h
          · exact h
          · exact absurd (hpt₀.symm.trans (h ▸ ha.2.2)) (Ne.symm hq)
        have hb' : b < t₀ := by
          rcases hb.2.1.lt_or_eq with h | h
          · exact h
          · exact absurd (hpt₀.symm.trans (h ▸ hb.2.2)) (Ne.symm hq)
        exact hA a b ha' hb' (ha.2.2.trans hb.2.2.symm)
      have h3 : R.filter (fun i ↦ c i = q) = univ.filter fun i ↦ t₀ < i ∧ c i = q := by
        ext i
        constructor
        · intro hi
          have hiR := mem_filter.1 hi
          have hiR' := mem_filter.1 hiR.1
          exact mem_filter.2 ⟨mem_univ _, hiR'.2.1, hiR.2⟩
        · intro hi
          have hi' := mem_filter.1 hi
          exact mem_filter.2 ⟨mem_filter.2 ⟨mem_univ _, hi'.2.1, hi'.2.2 ▸ hq⟩, hi'.2.2⟩
      have h1 := hcard q
      have h2 : (univ.filter fun i ↦ c i = q).card ≤
          (univ.filter fun i ↦ t₀ < i ∧ c i = q).card + 1 :=
        calc (univ.filter fun i ↦ c i = q).card
            ≤ ((univ.filter fun i ↦ t₀ < i ∧ c i = q) ∪
                (univ.filter fun i ↦ i ≤ t₀ ∧ c i = q)).card := card_le_card hsub2
          _ ≤ (univ.filter fun i ↦ t₀ < i ∧ c i = q).card +
                (univ.filter fun i ↦ i ≤ t₀ ∧ c i = q).card := card_union_le _ _
          _ ≤ (univ.filter fun i ↦ t₀ < i ∧ c i = q).card + 1 :=
              Nat.add_le_add_left hsmall _
      rw [h3]
      omega
    -- Apply the induction hypothesis to the remaining row.
    obtain ⟨f', hfcard, hfadj⟩ := ih R.card c' hcard'
    let g : Fin (2 * N) ↪o Fin M := f'.trans e
    have hgc : ∀ j, c (g j) = p.succAbove (c' (f' j)) := fun j ↦ (hc' (f' j)).symm
    have hgt : ∀ j, t₀ < g j := fun j ↦ (mem_filter.1 (he (f' j))).2.1
    -- Prepend the pair `s₀, t₀`.
    have hf : StrictMono (prepend N M s₀ t₀ g) := prepend_strictMono N M hs₀ g hgt
    let femb : Fin (2 * (N + 1)) ↪o Fin M := OrderEmbedding.ofStrictMono _ hf
    have hfe : ∀ i, femb i = prepend N M s₀ t₀ g i := fun i ↦ rfl
    refine ⟨femb, ?_, ?_⟩
    · -- Exactly two selected people of each colour.
      intro k
      by_cases hkp : k = p
      · subst hkp
        have hset : univ.filter (fun i ↦ c (femb i) = p) = {⟨0, by omega⟩, ⟨1, by omega⟩} := by
          ext i
          rcases i with ⟨i, hi⟩
          rw [mem_filter, mem_insert, mem_singleton]
          by_cases hi0 : i = 0
          · subst hi0
            refine ⟨fun _ ↦ Or.inl rfl, fun _ ↦ ?_⟩
            rw [hfe, prepend_zero, hpc]
            exact ⟨mem_univ _, rfl⟩
          · by_cases hi1 : i = 1
            · subst hi1
              refine ⟨fun _ ↦ Or.inr rfl, fun _ ↦ ?_⟩
              rw [hfe, prepend_one, hpt₀]
              exact ⟨mem_univ _, rfl⟩
            · have hi2 : 2 ≤ i := by omega
              rw [hfe, prepend_two _ _ _ _ _ _ hi2, hgc]
              constructor
              · intro h
                exact absurd h.2 (Fin.succAbove_ne _ _)
              · rintro (h | h)
                · have : i = 0 := congrArg Fin.val h
                  omega
                · have : i = 1 := congrArg Fin.val h
                  omega
        rw [hset]
        exact card_pair_eq_two_iff.2 (by simp)
      · obtain ⟨k', hk'⟩ := Fin.exists_succAbove_eq hkp
        let emb2 : Fin (2 * N) ↪ Fin (2 * (N + 1)) :=
          ⟨fun j ↦ ⟨j.val + 2, by omega⟩, fun a b h ↦ by
            have hv : a.val + 2 = b.val + 2 := congrArg Fin.val h
            exact Fin.ext (by omega)⟩
        have hset : univ.filter (fun i ↦ c (femb i) = k) =
            (univ.filter fun j ↦ c' (f' j) = k').map emb2 := by
          ext i
          rcases i with ⟨i, hi⟩
          simp only [mem_filter, mem_univ, true_and, mem_map]
          by_cases hi0 : i = 0
          · subst hi0
            constructor
            · intro h
              rw [hfe, prepend_zero, hpc] at h
              exact absurd h.symm hkp
            · rintro ⟨j, -, hj⟩
              have hv : j.val + 2 = 0 := congrArg Fin.val hj
              omega
          · by_cases hi1 : i = 1
            · subst hi1
              constructor
              · intro h
                rw [hfe, prepend_one, hpt₀] at h
                exact absurd h.symm hkp
              · rintro ⟨j, -, hj⟩
                have hv : j.val + 2 = 1 := congrArg Fin.val hj
                omega
            · have hi2 : 2 ≤ i := by omega
              constructor
              · intro h
                rw [hfe, prepend_two _ _ _ _ _ ⟨i, hi⟩ hi2, hgc] at h
                refine ⟨⟨i - 2, by omega⟩, ?_, Fin.ext (show (i - 2) + 2 = i by omega)⟩
                rw [← hk'] at h
                exact Fin.succAbove_right_injective h
              · rintro ⟨j, hj, hji⟩
                have hjv : j.val + 2 = i := congrArg Fin.val hji
                rw [hfe, prepend_two _ _ _ _ _ ⟨i, hi⟩ hi2, hgc]
                have hjeq : (⟨i - 2, by omega⟩ : Fin (2 * N)) = j :=
                  Fin.ext (show i - 2 = j.val by omega)
                rw [hjeq, hj, hk']
        rw [hset, card_map]
        exact hfcard k'
    · -- Same colour implies adjacent (or equal) positions.
      intro i j hij
      rcases i with ⟨i, hi⟩
      rcases j with ⟨j, hj⟩
      by_cases hi0 : i = 0
      · subst hi0
        by_cases hj0 : j = 0
        · subst hj0
          left; rfl
        · by_cases hj1 : j = 1
          · subst hj1
            right; left; rfl
          · exfalso
            have hj2 : 2 ≤ j := by omega
            rw [hfe, hfe, prepend_zero, prepend_two _ _ _ _ _ ⟨j, hj⟩ hj2, hpc, hgc] at hij
            exact absurd hij (Fin.ne_succAbove _ _)
      · by_cases hi1 : i = 1
        · subst hi1
          by_cases hj0 : j = 0
          · subst hj0
            right; right; rfl
          · by_cases hj1 : j = 1
            · subst hj1
              left; rfl
            · exfalso
              have hj2 : 2 ≤ j := by omega
              rw [hfe, hfe, prepend_one, prepend_two _ _ _ _ _ ⟨j, hj⟩ hj2, hpt₀, hgc] at hij
              exact absurd hij (Fin.ne_succAbove _ _)
        · have hi2 : 2 ≤ i := by omega
          by_cases hj0 : j = 0
          · subst hj0
            exfalso
            rw [hfe, hfe, prepend_two _ _ _ _ _ ⟨i, hi⟩ hi2, prepend_zero, hgc, hpc] at hij
            exact absurd hij (Fin.succAbove_ne _ _)
          · by_cases hj1 : j = 1
            · subst hj1
              exfalso
              rw [hfe, hfe, prepend_two _ _ _ _ _ ⟨i, hi⟩ hi2, prepend_one, hgc, hpt₀] at hij
              exact absurd hij (Fin.succAbove_ne _ _)
            · have hj2 : 2 ≤ j := by omega
              rw [hfe, hfe, prepend_two _ _ _ _ _ ⟨i, hi⟩ hi2, prepend_two _ _ _ _ _ ⟨j, hj⟩ hj2,
                hgc, hgc] at hij
              have hci := Fin.succAbove_right_injective hij
              obtain h | h | h := hfadj _ _ hci
              · left
                have hv : i - 2 = j - 2 := congrArg Fin.val h
                have heq : i = j := by omega
                subst heq
                rfl
              · right; left
                have hv : i - 2 + 1 = j - 2 := h
                show i + 1 = j
                omega
              · right; right
                have hv : j - 2 + 1 = i - 2 := h
                show j + 1 = i
                omega

/-- Colouring by height: `c i` is the index of the block of `N + 1`
consecutive height ranks containing the player at position `i`. -/
theorem main_aux (N : ℕ) (hN : 1 ≤ N) (a : Fin (N * (N + 1)) → ℕ)
    (ha : Function.Injective a) :
    ∃ f : Fin (2 * N) ↪o Fin (N * (N + 1)), ∀ k : Fin N, ∀ i j : Fin (2 * N),
      (univ.filter fun t ↦ a (f t) > a (f i)).card = 2 * k.val →
      (univ.filter fun t ↦ a (f t) > a (f j)).card = 2 * k.val + 1 →
      i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  -- `ρ i` is the number of players shorter than player `i`.
  let ρ : Fin (N * (N + 1)) → ℕ := fun i ↦ (univ.filter fun t ↦ a t < a i).card
  have hρlt : ∀ i, ρ i < N * (N + 1) := by
    intro i
    have h : (univ.filter fun t ↦ a t < a i).card < (univ : Finset (Fin (N * (N + 1)))).card := by
      apply card_lt_card
      rw [filter_ssubset]
      exact ⟨i, mem_univ _, by simp⟩
    rwa [card_univ, Fintype.card_fin] at h
  have hρmono : ∀ i j, a i ≤ a j → ρ i ≤ ρ j := by
    intro i j hij
    apply card_le_card
    intro t ht
    rw [mem_filter] at ht ⊢
    exact ⟨mem_univ _, lt_of_lt_of_le ht.2 hij⟩
  have hρlt' : ∀ i j, a i < a j → ρ i < ρ j := by
    intro i j hij
    apply card_lt_card
    rw [ssubset_iff_subset_ne]
    refine ⟨?_, ?_⟩
    · intro t ht
      rw [mem_filter] at ht ⊢
      exact ⟨mem_univ _, lt_trans ht.2 hij⟩
    · intro hcon
      have hi : i ∈ univ.filter (fun t ↦ a t < a j) := mem_filter.2 ⟨mem_univ _, hij⟩
      rw [← hcon] at hi
      rw [mem_filter] at hi
      exact absurd hi.2 (lt_irrefl _)
  have hρinj : Function.Injective ρ := by
    intro i j hij
    by_contra hne
    rcases lt_or_gt_of_ne (fun h ↦ hne (ha h)) with h | h
    · have := hρlt' i j h
      omega
    · have := hρlt' j i h
      omega
  have hρbij : Function.Bijective fun i : Fin (N * (N + 1)) ↦ (⟨ρ i, hρlt i⟩ : Fin (N * (N + 1))) :=
    Finite.injective_iff_bijective.1 (fun i j h ↦ hρinj (congrArg Fin.val h))
  -- The colouring: block of `N + 1` consecutive ranks.
  let c : Fin (N * (N + 1)) → Fin N := fun i ↦
    ⟨ρ i / (N + 1), by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      exact hρlt i⟩
  have hc_le : ∀ i j, a i < a j → c i ≤ c j := by
    intro i j hij
    show ρ i / (N + 1) ≤ ρ j / (N + 1)
    exact Nat.div_le_div_right (hρmono i j hij.le)
  have hc_lt : ∀ i j, c i < c j → a i < a j := by
    intro i j hij
    by_contra h
    push Not at h
    have h1 : ρ j / (N + 1) ≤ ρ i / (N + 1) := Nat.div_le_div_right (hρmono j i h)
    exact absurd hij (not_lt_of_ge h1)
  -- Each colour is used exactly `N + 1` times.
  have hcard : ∀ k : Fin N, N + 1 ≤ (univ.filter fun i ↦ c i = k).card := by
    intro k
    have hset : (univ.filter fun i ↦ c i = k).card = N + 1 := by
      have hbij : (univ.filter fun i ↦ c i = k).card =
          (univ.filter fun r : Fin (N * (N + 1)) ↦ r.val / (N + 1) = k.val).card := by
        apply Finset.card_bij (fun i _ ↦ (⟨ρ i, hρlt i⟩ : Fin (N * (N + 1))))
        · intro i hi
          rw [mem_filter] at hi ⊢
          exact ⟨mem_univ _, congrArg Fin.val hi.2⟩
        · intro i _ j _ h
          exact hρinj (congrArg Fin.val h)
        · intro r hr
          obtain ⟨i, hi⟩ := hρbij.2 r
          refine ⟨i, ?_, hi⟩
          rw [mem_filter] at hr ⊢
          refine ⟨mem_univ _, ?_⟩
          have hρi : ρ i = r.val := congrArg Fin.val hi
          have hval : (c i).val = k.val := by
            show ρ i / (N + 1) = k.val
            rw [hρi]
            exact hr.2
          exact Fin.ext hval
      rw [hbij]
      have hset2 : univ.filter (fun r : Fin (N * (N + 1)) ↦ r.val / (N + 1) = k.val) =
          (Finset.Ico (k.val * (N + 1)) ((k.val + 1) * (N + 1))).attachFin (by
            intro m hm
            rw [mem_Ico] at hm
            calc m < (k.val + 1) * (N + 1) := hm.2
              _ ≤ N * (N + 1) := by
                gcongr
                exact Nat.succ_le_of_lt k.isLt) := by
        ext r
        rw [mem_attachFin, mem_Ico, mem_filter]
        constructor
        · intro hr
          refine ⟨?_, ?_⟩
          · rw [← hr.2]
            exact Nat.div_mul_le_self _ _
          · have h2 : r.val < (r.val / (N + 1) + 1) * (N + 1) := by
              calc r.val = (N + 1) * (r.val / (N + 1)) + r.val % (N + 1) :=
                    (Nat.div_add_mod _ _).symm
                _ < (N + 1) * (r.val / (N + 1)) + (N + 1) := by
                  have := Nat.mod_lt r.val (show 0 < N + 1 by omega)
                  omega
                _ = (r.val / (N + 1) + 1) * (N + 1) := by ring
            rw [hr.2] at h2
            exact h2
        · intro hr
          refine ⟨mem_univ _, ?_⟩
          have h1 : k.val ≤ r.val / (N + 1) := by
            rw [Nat.le_div_iff_mul_le (by omega)]
            exact hr.1
          have h2 : r.val / (N + 1) < k.val + 1 := by
            rw [Nat.div_lt_iff_lt_mul (by omega)]
            exact hr.2
          omega
      rw [hset2, card_attachFin, Nat.card_Ico]
      have : (k.val + 1) * (N + 1) = k.val * (N + 1) + (N + 1) := by ring
      rw [this, Nat.add_sub_cancel_left]
    rw [hset]
  -- Apply the combinatorial lemma.
  obtain ⟨f, hfcard, hfadj⟩ := aux N (N * (N + 1)) c hcard
  refine ⟨f, ?_⟩
  intro k i j hi hj
  -- The number of selected players taller than `l` equals
  -- twice the number of blocks above `l`, plus at most one (its block-mate).
  have key : ∀ l : Fin (2 * N),
      (univ.filter fun t ↦ a (f t) > a (f l)).card =
        2 * (N - 1 - (c (f l)).val) +
          (univ.filter fun t ↦ c (f t) = c (f l) ∧ a (f t) > a (f l)).card := by
    intro l
    have hdisj : univ.filter (fun t ↦ a (f t) > a (f l)) =
        univ.filter (fun t ↦ c (f l) < c (f t) ∧ a (f t) > a (f l)) ∪
          univ.filter (fun t ↦ c (f t) = c (f l) ∧ a (f t) > a (f l)) := by
      ext t
      simp only [mem_filter, mem_univ, true_and, mem_union]
      constructor
      · intro h
        have hc := hc_le (f l) (f t) h
        rcases lt_or_eq_of_le hc with h1 | h1
        · exact Or.inl ⟨h1, h⟩
        · exact Or.inr ⟨h1.symm, h⟩
      · rintro (⟨-, h⟩ | ⟨-, h⟩) <;> exact h
    have hdj : Disjoint
        (univ.filter fun t ↦ c (f l) < c (f t) ∧ a (f t) > a (f l))
        (univ.filter fun t ↦ c (f t) = c (f l) ∧ a (f t) > a (f l)) := by
      rw [Finset.disjoint_left]
      intro t ht1 ht2
      rw [mem_filter] at ht1 ht2
      exact absurd (ht2.2.1 ▸ ht1.2.1) (lt_irrefl _)
    have hpart1 : (univ.filter fun t ↦ c (f l) < c (f t) ∧ a (f t) > a (f l)).card =
        2 * (N - 1 - (c (f l)).val) := by
      have hset : univ.filter (fun t ↦ c (f l) < c (f t) ∧ a (f t) > a (f l)) =
          univ.filter fun t ↦ c (f l) < c (f t) := by
        ext t
        simp only [mem_filter, mem_univ, true_and]
        exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, hc_lt (f l) (f t) h⟩⟩
      have hfiber : ∀ k' ∈ univ.filter (fun k' : Fin N ↦ c (f l) < k'),
          ((univ.filter fun t ↦ c (f l) < c (f t)).filter fun t ↦ c (f t) = k').card = 2 := by
        intro k' hk'
        rw [mem_filter] at hk'
        have hfs : (univ.filter fun t ↦ c (f l) < c (f t)).filter (fun t ↦ c (f t) = k') =
            univ.filter fun t ↦ c (f t) = k' := by
          ext t
          simp only [mem_filter, mem_univ, true_and]
          exact ⟨fun h ↦ h.2, fun h ↦ ⟨h ▸ hk'.2, h⟩⟩
        rw [hfs]
        exact hfcard k'
      have hT : (univ.filter fun k' : Fin N ↦ c (f l) < k').card = N - 1 - (c (f l)).val := by
        have hsetT : univ.filter (fun k' : Fin N ↦ c (f l) < k') =
            (Finset.Ico ((c (f l)).val + 1) N).attachFin (fun m hm ↦ (mem_Ico.1 hm).2) := by
          ext r
          rw [mem_attachFin, mem_Ico, mem_filter]
          constructor
          · intro hr
            exact ⟨Nat.succ_le_iff.2 hr.2, r.isLt⟩
          · intro hr
            exact ⟨mem_univ _, Nat.succ_le_iff.1 hr.1⟩
        rw [hsetT, card_attachFin, Nat.card_Ico]
        omega
      calc (univ.filter fun t ↦ c (f l) < c (f t) ∧ a (f t) > a (f l)).card
          = (univ.filter fun t ↦ c (f l) < c (f t)).card := by rw [hset]
        _ = ∑ k' ∈ univ.filter (fun k' : Fin N ↦ c (f l) < k'),
              ((univ.filter fun t ↦ c (f l) < c (f t)).filter fun t ↦ c (f t) = k').card :=
            card_eq_sum_card_fiberwise (f := fun t ↦ c (f t)) (by
              intro x hx
              have hx' := (mem_filter.1 (Finset.mem_coe.1 hx)).2
              exact Finset.mem_coe.2 (mem_filter.2 ⟨mem_univ _, hx'⟩))
        _ = ∑ k' ∈ univ.filter (fun k' : Fin N ↦ c (f l) < k'), 2 :=
            Finset.sum_congr rfl hfiber
        _ = 2 * (N - 1 - (c (f l)).val) := by
            rw [sum_const, nsmul_eq_mul, hT]
            push_cast
            ring
    rw [hdisj, card_union_eq_card_add_card.2 hdj, hpart1]
  have heps : ∀ l : Fin (2 * N),
      (univ.filter fun t ↦ c (f t) = c (f l) ∧ a (f t) > a (f l)).card ≤ 1 := by
    intro l
    have hsub : univ.filter (fun t ↦ c (f t) = c (f l) ∧ a (f t) > a (f l)) ⊆
        (univ.filter fun t ↦ c (f t) = c (f l)).erase l := by
      intro t ht
      rw [mem_filter] at ht
      rw [mem_erase, mem_filter]
      exact ⟨fun h ↦ absurd (h ▸ ht.2.2) (lt_irrefl _), mem_univ _, ht.2.1⟩
    calc (univ.filter fun t ↦ c (f t) = c (f l) ∧ a (f t) > a (f l)).card
        ≤ ((univ.filter fun t ↦ c (f t) = c (f l)).erase l).card := card_le_card hsub
      _ = (univ.filter fun t ↦ c (f t) = c (f l)).card - 1 :=
          card_erase_of_mem (mem_filter.2 ⟨mem_univ _, rfl⟩)
      _ = 2 - 1 := by rw [hfcard]
      _ = 1 := rfl
  -- Put everything together.
  have hei := heps i
  have hej := heps j
  rw [key i] at hi
  rw [key j] at hj
  have hcij : c (f i) = c (f j) := by
    have h1 : N - 1 - (c (f i)).val = k.val := by
      have hci := (c (f i)).isLt
      have hkv := k.isLt
      omega
    have h2 : N - 1 - (c (f j)).val = k.val := by
      have hcj := (c (f j)).isLt
      have hkv := k.isLt
      omega
    apply Fin.ext
    have hci := (c (f i)).isLt
    have hcj := (c (f j)).isLt
    omega
  obtain h | h | h := hfadj i j hcij
  · subst h
    omega
  · exact Or.inl h
  · exact Or.inr h

snip end

problem imo2017_p5 (N : ℕ) (hN : 1 ≤ N) (a : Fin (N * (N + 1)) → ℕ)
    (ha : Function.Injective a) :
    ∃ f : Fin (2 * N) ↪o Fin (N * (N + 1)), ∀ k : Fin N, ∀ i j : Fin (2 * N),
      (Finset.univ.filter fun t ↦ a (f t) > a (f i)).card = 2 * k.val →
      (Finset.univ.filter fun t ↦ a (f t) > a (f j)).card = 2 * k.val + 1 →
      i.val + 1 = j.val ∨ j.val + 1 = i.val :=
  main_aux N hN a ha

end Imo2017P5
