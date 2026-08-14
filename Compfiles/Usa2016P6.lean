/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Data.Finset.Option
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Pigeonhole
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 2016, Problem 6

Integers n and k are given, with n ≥ k ≥ 2. You play the following game against
an evil wizard. The wizard has 2n cards; for each i = 1, ..., n, there are two
cards labeled i. Initially, the wizard places all cards face down in a row, in
unknown order. You may repeatedly make moves of the following form: you point to
any k of the cards. The wizard then turns those cards face up. If any two of the
cards match, the game is over and you win. Otherwise, you must look away, while
the wizard arbitrarily permutes the k chosen cards and then turns them back
face-down. Then, it is your turn again.

We say this game is winnable if there exist some positive integer m and some
strategy that is guaranteed to win in at most m moves, no matter how the wizard
responds. For which values of n and k is the game winnable?
-/

namespace Usa2016P6

open Finset

/-! ## The game model -/

/-- An arrangement of the `2n` cards: the label shown at each position. -/
abbrev Arrangement (n : ℕ) := Fin (2 * n) → Fin n

/-- An arrangement is valid when each of the `n` labels appears exactly twice. -/
def Arrangement.Valid {n : ℕ} (a : Arrangement n) : Prop :=
  ∀ ℓ : Fin n, (univ.filter fun i ↦ a i = ℓ).card = 2

/-- An observation made by the player: the set of queried positions, together
with the labels that were revealed (`none` outside the queried set). -/
abbrev Observation (n : ℕ) := Finset (Fin (2 * n)) × (Fin (2 * n) → Option (Fin n))

/-- A player strategy: from the list of past observations, choose the next set
of positions to query. -/
abbrev Strategy (n : ℕ) := List (Observation n) → Finset (Fin (2 * n))

/-- A strategy is valid for the parameter `k` if it always queries exactly `k`
cards. -/
def Strategy.Valid {n : ℕ} (σ : Strategy n) (k : ℕ) : Prop :=
  ∀ h, (σ h).card = k

/-- The revealed labels, hidden (`none`) outside the queried set. -/
def reveal {n : ℕ} (a : Arrangement n) (Q : Finset (Fin (2 * n))) :
    Fin (2 * n) → Option (Fin n) :=
  fun i ↦ if i ∈ Q then some (a i) else none

/-- A wizard: an initial arrangement of the cards, and a way to permute the
queried cards after each unsuccessful query. -/
structure Wizard (n : ℕ) where
  init : Arrangement n
  perm : List (Observation n) → Finset (Fin (2 * n)) → Equiv.Perm (Fin (2 * n))

/-- A wizard plays legitimately if the initial arrangement has two cards of each
label and each permutation only moves the currently queried cards. -/
def Wizard.Valid {n : ℕ} (W : Wizard n) : Prop :=
  W.init.Valid ∧ ∀ h Q i, i ∉ Q → W.perm h Q i = i

/-- The state of play: the current arrangement, the past observations, and
whether the player has already won. -/
structure PlayState (n : ℕ) where
  arr : Arrangement n
  hist : List (Observation n)
  won : Bool

/-- One round of the game. -/
def step {n : ℕ} (σ : Strategy n) (W : Wizard n) (s : PlayState n) : PlayState n :=
  if s.won then s
  else
    let Q := σ s.hist
    if (Q.image s.arr).card = Q.card then
      { arr := s.arr ∘ W.perm s.hist Q
      , hist := s.hist ++ [(Q, reveal s.arr Q)]
      , won := false }
    else { s with won := true }

/-- The state after `m` rounds of play. -/
def play {n : ℕ} (σ : Strategy n) (W : Wizard n) : ℕ → PlayState n
  | 0 => { arr := W.init, hist := [], won := false }
  | m + 1 => step σ W (play σ W m)

/-- The game is winnable if some valid strategy guarantees a win within `m`
moves against every legitimate wizard. -/
def Winnable (n k : ℕ) : Prop :=
  ∃ m ≥ 1, ∃ σ : Strategy n, σ.Valid k ∧ ∀ W : Wizard n, W.Valid → (play σ W m).won

snip begin

lemma play_succ {n : ℕ} (σ : Strategy n) (W : Wizard n) (m : ℕ) :
    play σ W (m + 1) = step σ W (play σ W m) := rfl

lemma step_of_won {n : ℕ} {σ : Strategy n} {W : Wizard n} {s : PlayState n}
    (h : s.won) : step σ W s = s := by
  unfold step
  rw [ite_eq_left h]

lemma won_mono {n : ℕ} {σ : Strategy n} {W : Wizard n} {t u : ℕ}
    (h : (play σ W t).won) (hu : t ≤ u) : (play σ W u).won := by
  induction hu with
  | refl => exact h
  | step _ ih => rw [play_succ, step_of_won ih, ih]

lemma image_eq_of_perm_fix {ι : Type*} [DecidableEq ι] {τ : Equiv.Perm ι}
    {Q : Finset ι} (h : ∀ i, i ∉ Q → τ i = i) : Q.image τ = Q := by
  ext x
  simp only [mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    by_contra hx
    have h1 : τ (τ y) = τ y := h (τ y) hx
    have h2 : τ y = y := τ.injective h1
    rw [h2] at hx
    exact hx hy
  · intro hx
    refine ⟨τ.symm x, ?_, τ.apply_symm_apply x⟩
    by_contra hsym
    have h1 : τ (τ.symm x) = τ.symm x := h (τ.symm x) hsym
    rw [τ.apply_symm_apply] at h1
    rw [← h1] at hsym
    exact hsym hx

/-- The labels revealed in an observation on a given set of positions. -/
def obsValues {n : ℕ} (o : Observation n) (s : Finset (Fin (2 * n))) : Finset (Fin n) :=
  s.biUnion fun i ↦ (o.2 i).toFinset

lemma obsValues_eq_image {n : ℕ} {a : Arrangement n} {Q s : Finset (Fin (2 * n))}
    (hs : s ⊆ Q) : obsValues (Q, reveal a Q) s = s.image a := by
  ext ℓ
  simp only [obsValues, mem_biUnion, Option.mem_toFinset, Option.mem_def, mem_image]
  constructor
  · rintro ⟨i, hi, hri⟩
    rw [reveal, ite_eq_left (hs hi)] at hri
    exact ⟨i, hi, Option.some.inj hri⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, by rw [reveal, ite_eq_left (hs hi)]⟩

/-! ## The winning strategy for `k < n` -/

/-- The window of `k` consecutive positions starting at `j`
(the empty set if it does not fit). -/
def window (n k j : ℕ) : Finset (Fin (2 * n)) :=
  if h : j + k ≤ 2 * n then
    (range k).attach.image fun ⟨t, ht⟩ ↦ ⟨j + t, by have : t < k := mem_range.1 ht; lia⟩
  else ∅

lemma card_window {n k j : ℕ} (h : j + k ≤ 2 * n) : (window n k j).card = k := by
  rw [window, dite_eq_left h, card_image_of_injOn, card_attach, card_range]
  intro ⟨a, ha⟩ _ ⟨b, hb⟩ _ hab
  simp only [Fin.mk.injEq] at hab
  have : a = b := by lia
  subst this
  rfl

lemma mem_window {n k j : ℕ} (h : j + k ≤ 2 * n) {x : Fin (2 * n)} :
    x ∈ window n k j ↔ j ≤ x.val ∧ x.val < j + k := by
  rw [window, dite_eq_left h]
  simp only [mem_image, mem_attach, true_and, Subtype.exists]
  constructor
  · rintro ⟨t, ht, rfl⟩
    have : t < k := mem_range.1 ht
    simp only
    lia
  · rintro ⟨h1, h2⟩
    exact ⟨x.val - j, by rw [mem_range]; lia,
      Fin.ext (by simp only; lia)⟩

/-- The `k - 1` positions strictly between `i` and `i + k`
(the empty set if they do not fit). -/
def midWindow (n k i : ℕ) : Finset (Fin (2 * n)) :=
  if h : i + k ≤ 2 * n then
    (range (k - 1)).attach.image fun ⟨t, ht⟩ ↦ ⟨i + 1 + t, by
      have : t < k - 1 := mem_range.1 ht; lia⟩
  else ∅

lemma card_midWindow {n k i : ℕ} (h : i + k ≤ 2 * n) : (midWindow n k i).card = k - 1 := by
  rw [midWindow, dite_eq_left h, card_image_of_injOn, card_attach, card_range]
  intro ⟨a, ha⟩ _ ⟨b, hb⟩ _ hab
  simp only [Fin.mk.injEq] at hab
  have : a = b := by lia
  subst this
  rfl

lemma mem_midWindow {n k i : ℕ} (h : i + k ≤ 2 * n) {x : Fin (2 * n)} :
    x ∈ midWindow n k i ↔ i < x.val ∧ x.val < i + k := by
  rw [midWindow, dite_eq_left h]
  simp only [mem_image, mem_attach, true_and, Subtype.exists]
  constructor
  · rintro ⟨t, ht, rfl⟩
    have : t < k - 1 := mem_range.1 ht
    simp only
    lia
  · rintro ⟨h1, h2⟩
    exact ⟨x.val - (i + 1), by rw [mem_range]; lia,
      Fin.ext (by simp only; lia)⟩

lemma midWindow_subset_window {n k i : ℕ} (h : i + k ≤ 2 * n) :
    midWindow n k i ⊆ window n k i := by
  intro x hx
  rw [mem_midWindow h] at hx
  rw [mem_window h]
  lia

lemma midWindow_subset_window_succ {n k i : ℕ} (h : i + k ≤ 2 * n) (h' : i + 1 + k ≤ 2 * n) :
    midWindow n k i ⊆ window n k (i + 1) := by
  intro x hx
  rw [mem_midWindow h] at hx
  rw [mem_window h']
  lia

/-- The label the player can deduce at position `i`, computed from observations
`i` and `i + 1` (junk value `0` when those observations are not available). -/
noncomputable def labelAt (n k : ℕ) [NeZero n] (hist : List (Observation n)) (i : ℕ) :
    Fin n :=
  if h : i + 1 < hist.length ∧ i + k ≤ 2 * n then
    let S := obsValues (hist.get ⟨i, Nat.lt_of_succ_lt h.1⟩) (window n k i)
    let T := obsValues (hist.get ⟨i + 1, h.1⟩) (midWindow n k i)
    if h₂ : (S \ T).Nonempty then h₂.choose else 0
  else 0

/-- The position in the row corresponding to a deduced-label index. -/
def posOf (n k : ℕ) (p : Fin (2 * n - k)) : Fin (2 * n) :=
  ⟨p.val, lt_of_lt_of_le p.isLt (Nat.sub_le (2 * n) k)⟩

lemma posOf_val (n k : ℕ) (p : Fin (2 * n - k)) : (posOf n k p).val = p.val := rfl

lemma posOf_ne {n k : ℕ} {p q : Fin (2 * n - k)} (h : p ≠ q) : posOf n k p ≠ posOf n k q := by
  intro e
  apply h
  apply Fin.ext
  have h2 := congrArg Fin.val e
  rw [posOf_val, posOf_val] at h2
  exact h2

lemma pairSet_exists {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n)
    {p q : Fin (2 * n - k)} (hpq : p ≠ q) :
    ∃ s : Finset (Fin (2 * n)), s.card = k ∧ posOf n k p ∈ s ∧ posOf n k q ∈ s := by
  obtain ⟨u, hu1, hu2⟩ := exists_subset_card_eq (s := univ \ {posOf n k p, posOf n k q})
    (n := k - 2) (by
      rw [card_sdiff, card_univ, Fintype.card_fin, inter_univ,
        card_insert_of_notMem (by simp only [mem_singleton]; exact posOf_ne hpq),
        card_singleton]
      lia)
  have hdis : Disjoint ({posOf n k p, posOf n k q} : Finset (Fin (2 * n))) u := by
    rw [Finset.disjoint_left]
    intro x hxP hxu
    exact (mem_sdiff.1 (hu1 hxu)).2 hxP
  refine ⟨{posOf n k p, posOf n k q} ∪ u, ?_, mem_union_left _ (mem_insert_self _ _),
    mem_union_left _ (mem_insert_of_mem (mem_singleton_self _))⟩
  rw [card_union_of_disjoint hdis,
    card_insert_of_notMem (by simp only [mem_singleton]; exact posOf_ne hpq),
    card_singleton, hu2]
  lia

/-- A set of `k` positions containing the two given (distinct) positions. -/
noncomputable def pairSet (n k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n)
    (p q : Fin (2 * n - k)) (hpq : p ≠ q) : Finset (Fin (2 * n)) :=
  (pairSet_exists hk hkn hpq).choose

lemma pairSet_card {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n)
    {p q : Fin (2 * n - k)} (hpq : p ≠ q) : (pairSet n k hk hkn p q hpq).card = k :=
  (pairSet_exists hk hkn hpq).choose_spec.1

lemma posOf_mem_pairSet {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n)
    {p q : Fin (2 * n - k)} (hpq : p ≠ q) : posOf n k p ∈ pairSet n k hk hkn p q hpq :=
  (pairSet_exists hk hkn hpq).choose_spec.2.1

lemma posOf_mem_pairSet' {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n)
    {p q : Fin (2 * n - k)} (hpq : p ≠ q) : posOf n k q ∈ pairSet n k hk hkn p q hpq :=
  (pairSet_exists hk hkn hpq).choose_spec.2.2

/-- The winning strategy: slide a window of `k` positions across the row, then
query two positions that are known to carry the same label. -/
noncomputable def winStrat (n k : ℕ) [NeZero n] (hk : 2 ≤ k) (hkn : k ≤ n) :
    Strategy n :=
  fun hist ↦
    if hist.length + k ≤ 2 * n then
      window n k hist.length
    else if h₂ : ∃ p q : Fin (2 * n - k), p ≠ q ∧
        labelAt n k hist p.val = labelAt n k hist q.val then
      pairSet n k hk hkn h₂.choose h₂.choose_spec.choose h₂.choose_spec.choose_spec.1
    else window n k 0

lemma winStrat_valid (n k : ℕ) [NeZero n] (hk : 2 ≤ k) (hkn : k ≤ n) :
    (winStrat n k hk hkn).Valid k := by
  intro hist
  unfold winStrat
  split
  · next h => exact card_window h
  · split
    · exact pairSet_card hk hkn _
    · exact card_window (by lia)

/-- The winning strategy specialized to `k < n`. -/
noncomputable abbrev slideStrat (n k : ℕ) [NeZero n] (hk : 2 ≤ k) (hkn : k < n) : Strategy n :=
  winStrat n k hk (le_of_lt hkn)

lemma step_apply_of_not_won {n : ℕ} {σ : Strategy n} {W : Wizard n} {s : PlayState n}
    (hw : ¬ s.won) :
    step σ W s = if ((σ s.hist).image s.arr).card = (σ s.hist).card then
      { arr := s.arr ∘ W.perm s.hist (σ s.hist)
      , hist := s.hist ++ [(σ s.hist, reveal s.arr (σ s.hist))]
      , won := false }
    else { s with won := true } := by
  unfold step
  rw [ite_eq_right hw]

lemma slideStrat_of_lt {n k : ℕ} [NeZero n] (hk : 2 ≤ k) (hkn : k < n)
    {hist : List (Observation n)} (h : hist.length + k ≤ 2 * n) :
    slideStrat n k hk hkn hist = window n k hist.length := by
  simp only [slideStrat, winStrat]
  rw [ite_eq_left h]

lemma slideStrat_of_ge {n k : ℕ} [NeZero n] (hk : 2 ≤ k) (hkn : k < n)
    {hist : List (Observation n)} (h : 2 * n < hist.length + k)
    (h₂ : ∃ p q : Fin (2 * n - k), p ≠ q ∧
      labelAt n k hist p.val = labelAt n k hist q.val) :
    slideStrat n k hk hkn hist =
      pairSet n k hk (le_of_lt hkn) h₂.choose h₂.choose_spec.choose
        h₂.choose_spec.choose_spec.1 := by
  simp only [slideStrat, winStrat]
  rw [ite_eq_right (by lia), dite_eq_left h₂]

/-- Facts about the play of the sliding strategy, while no win has occurred. -/
lemma slide_play_facts {n k : ℕ} [NeZero n] (hk : 2 ≤ k) (hkn : k < n)
    (W : Wizard n) (_hW : W.Valid)
    (hM : ¬ (play (slideStrat n k hk hkn) W (2 * n - k + 1)).won)
    (j : ℕ) (hj : j ≤ 2 * n - k + 1) :
    (play (slideStrat n k hk hkn) W j).won = false ∧
    ((play (slideStrat n k hk hkn) W j).hist).length = j ∧
    (∀ i (_hi : i < j), ((play (slideStrat n k hk hkn) W j).hist)[i]? =
      some (window n k i, reveal ((play (slideStrat n k hk hkn) W i).arr) (window n k i))) ∧
    (∀ j' (_hj' : j' < j),
      ((window n k j').image (play (slideStrat n k hk hkn) W j').arr).card = k) := by
  induction j with
  | zero => exact ⟨rfl, rfl, fun i hi => by lia, fun j' hj' => by lia⟩
  | succ j ih =>
    have hjM : j ≤ 2 * n - k + 1 := by lia
    obtain ⟨won_j, len_j, hist_j, inj_j⟩ := ih hjM
    have nwonj : ¬ (play (slideStrat n k hk hkn) W j).won := Bool.eq_false_iff.1 won_j
    have hbj : j + k ≤ 2 * n := by lia
    have hQ : (slideStrat n k hk hkn) (play (slideStrat n k hk hkn) W j).hist =
        window n k j := by
      have e := slideStrat_of_lt hk hkn (hist := (play (slideStrat n k hk hkn) W j).hist)
        (by rw [len_j]; lia)
      rw [len_j] at e
      exact e
    have hinj : ((window n k j).image (play (slideStrat n k hk hkn) W j).arr).card = k := by
      by_contra hne
      have hcond : ¬ ((window n k j).image (play (slideStrat n k hk hkn) W j).arr).card =
          (window n k j).card := by
        rw [card_window hbj]
        exact hne
      have hwon : (play (slideStrat n k hk hkn) W (j + 1)).won = true := by
        rw [play_succ, step_apply_of_not_won nwonj, hQ, ite_eq_right hcond]
      exact hM (won_mono hwon (by lia))
    have heq : play (slideStrat n k hk hkn) W (j + 1) =
        { arr := (play (slideStrat n k hk hkn) W j).arr ∘
            W.perm (play (slideStrat n k hk hkn) W j).hist (window n k j)
        , hist := (play (slideStrat n k hk hkn) W j).hist ++
            [(window n k j, reveal (play (slideStrat n k hk hkn) W j).arr (window n k j))]
        , won := false } := by
      rw [play_succ, step_apply_of_not_won nwonj, hQ]
      rw [ite_eq_left (by rw [card_window hbj]; exact hinj)]
    refine ⟨by rw [heq], (by rw [heq]; simp [len_j]), ?_, ?_⟩
    · intro i hi
      rw [heq]
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.1 hi) with hi' | hi''
      · rw [List.getElem?_append_left (by lia)]
        exact hist_j i hi'
      · subst hi''
        rw [List.getElem?_append_right (by lia), len_j, Nat.sub_self,
          List.getElem?_cons_zero]
    · intro j' hj'
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.1 hj') with hj'' | hj''
      · exact inj_j j' hj''
      · subst hj''
        exact hinj

/-- The arrangement one step later, while no win has occurred. -/
lemma slide_arr_step {n k : ℕ} [NeZero n] (hk : 2 ≤ k) (hkn : k < n)
    (W : Wizard n) (hW : W.Valid)
    (hM : ¬ (play (slideStrat n k hk hkn) W (2 * n - k + 1)).won)
    (j : ℕ) (hj : j < 2 * n - k + 1) :
    (play (slideStrat n k hk hkn) W (j + 1)).arr =
      (play (slideStrat n k hk hkn) W j).arr ∘
        W.perm (play (slideStrat n k hk hkn) W j).hist (window n k j) := by
  have won_j := (slide_play_facts hk hkn W hW hM j (by lia)).1
  have len_j := (slide_play_facts hk hkn W hW hM j (by lia)).2.1
  have inj_j := (slide_play_facts hk hkn W hW hM (j + 1) (by lia)).2.2.2 j
    (Nat.lt_succ_self j)
  have hbj : j + k ≤ 2 * n := by lia
  have hQ : (slideStrat n k hk hkn) (play (slideStrat n k hk hkn) W j).hist =
      window n k j := by
    have e := slideStrat_of_lt hk hkn (hist := (play (slideStrat n k hk hkn) W j).hist)
      (by rw [len_j]; lia)
    rw [len_j] at e
    exact e
  rw [play_succ, step_apply_of_not_won (Bool.eq_false_iff.1 won_j), hQ,
    ite_eq_left (by rw [card_window hbj]; exact inj_j)]

/-- Once determined, the label at position `x` never changes again. -/
lemma slide_arr_frozen {n k : ℕ} [NeZero n] (hk : 2 ≤ k) (hkn : k < n)
    (W : Wizard n) (hW : W.Valid)
    (hM : ¬ (play (slideStrat n k hk hkn) W (2 * n - k + 1)).won)
    (x : Fin (2 * n)) (hx : x.val < 2 * n - k)
    (j : ℕ) (hj1 : x.val + 1 ≤ j) (hj2 : j ≤ 2 * n - k + 1) :
    (play (slideStrat n k hk hkn) W j).arr x =
      (play (slideStrat n k hk hkn) W (x.val + 1)).arr x := by
  induction hj1 with
  | refl => rfl
  | step hle ih =>
    rename_i m
    rw [Nat.succ_eq_add_one] at hj2 ⊢
    have hstep := slide_arr_step hk hkn W hW hM m (by lia)
    have e1 : (play (slideStrat n k hk hkn) W (m + 1)).arr x =
        (play (slideStrat n k hk hkn) W m).arr x := by
      rw [hstep]
      have hfix : W.perm (play (slideStrat n k hk hkn) W m).hist (window n k m) x = x := by
        apply hW.2
        rw [mem_window (by lia : m + k ≤ 2 * n)]
        have hle2 : x.val + 1 ≤ m := hle
        lia
      rw [Function.comp_apply, hfix]
    rw [e1, ih (by lia)]

/-- The label computed from the observations is the actual label. -/
lemma slide_labelAt_eq {n k : ℕ} [NeZero n] (hk : 2 ≤ k) (hkn : k < n)
    (W : Wizard n) (hW : W.Valid)
    (hM : ¬ (play (slideStrat n k hk hkn) W (2 * n - k + 1)).won)
    (x : Fin (2 * n)) (hx : x.val < 2 * n - k) :
    labelAt n k ((play (slideStrat n k hk hkn) W (2 * n - k + 1)).hist) x.val =
      (play (slideStrat n k hk hkn) W (x.val + 1)).arr x := by
  obtain ⟨won_M, len_M, hist_M, inj_M⟩ :=
    slide_play_facts hk hkn W hW hM (2 * n - k + 1) (le_refl _)
  set i := x.val with hi_def
  have hbi : i + k ≤ 2 * n := by lia
  have hbi1 : i + 1 + k ≤ 2 * n := by lia
  have hcond : i + 1 < ((play (slideStrat n k hk hkn) W (2 * n - k + 1)).hist).length ∧
      i + k ≤ 2 * n := by
    rw [len_M]
    lia
  have get_i : ((play (slideStrat n k hk hkn) W (2 * n - k + 1)).hist).get
      ⟨i, Nat.lt_of_succ_lt hcond.1⟩ =
      (window n k i, reveal ((play (slideStrat n k hk hkn) W i).arr) (window n k i)) := by
    have h := hist_M i (by lia)
    rw [List.getElem?_eq_getElem (Nat.lt_of_succ_lt hcond.1)] at h
    exact Option.some.inj h
  have get_i1 : ((play (slideStrat n k hk hkn) W (2 * n - k + 1)).hist).get
      ⟨i + 1, hcond.1⟩ =
      (window n k (i + 1), reveal ((play (slideStrat n k hk hkn) W (i + 1)).arr)
        (window n k (i + 1))) := by
    have h := hist_M (i + 1) (by lia)
    rw [List.getElem?_eq_getElem hcond.1] at h
    exact Option.some.inj h
  have hinj_i := inj_M i (by lia)
  have hinj_i1 := inj_M (i + 1) (by lia)
  have harr := slide_arr_step hk hkn W hW hM i (by lia)
  have hS : (window n k i).image (play (slideStrat n k hk hkn) W (i + 1)).arr =
      (window n k i).image (play (slideStrat n k hk hkn) W i).arr := by
    rw [harr, ← image_image, image_eq_of_perm_fix (hW.2 _ _)]
  have hinjOn_i : Set.InjOn (play (slideStrat n k hk hkn) W i).arr ↑(window n k i) := by
    rw [← card_image_iff, hinj_i, card_window hbi]
  have hinjOn_succ : Set.InjOn (play (slideStrat n k hk hkn) W (i + 1)).arr
      ↑(window n k i) := by
    rw [← card_image_iff, hS, hinj_i, card_window hbi]
  have hinjOn_succ1 : Set.InjOn (play (slideStrat n k hk hkn) W (i + 1)).arr
      ↑(window n k (i + 1)) := by
    rw [← card_image_iff, hinj_i1, card_window hbi1]
  have hSeq : obsValues (((play (slideStrat n k hk hkn) W (2 * n - k + 1)).hist).get
      ⟨i, Nat.lt_of_succ_lt hcond.1⟩) (window n k i) =
      (window n k i).image (play (slideStrat n k hk hkn) W i).arr := by
    rw [get_i]
    exact obsValues_eq_image (subset_refl _)
  have hTeq : obsValues (((play (slideStrat n k hk hkn) W (2 * n - k + 1)).hist).get
      ⟨i + 1, hcond.1⟩) (midWindow n k i) =
      (midWindow n k i).image (play (slideStrat n k hk hkn) W (i + 1)).arr := by
    rw [get_i1]
    exact obsValues_eq_image (midWindow_subset_window_succ hbi hbi1)
  have hTsub : (midWindow n k i).image (play (slideStrat n k hk hkn) W (i + 1)).arr ⊆
      (window n k i).image (play (slideStrat n k hk hkn) W i).arr := by
    rw [← hS]
    exact image_mono (f := (play (slideStrat n k hk hkn) W (i + 1)).arr)
      (midWindow_subset_window hbi)
  have hTcard : ((midWindow n k i).image
      (play (slideStrat n k hk hkn) W (i + 1)).arr).card = k - 1 := by
    rw [card_image_iff.2 (hinjOn_succ1.mono (midWindow_subset_window_succ hbi hbi1)),
      card_midWindow hbi]
  have hcard1 : (((window n k i).image (play (slideStrat n k hk hkn) W i).arr) \
      ((midWindow n k i).image (play (slideStrat n k hk hkn) W (i + 1)).arr)).card = 1 := by
    rw [card_sdiff, inter_eq_left.2 hTsub, hinj_i, hTcard]
    lia
  obtain ⟨a, ha⟩ := card_eq_one.1 hcard1
  have hmem_S : (play (slideStrat n k hk hkn) W (i + 1)).arr x ∈
      (window n k i).image (play (slideStrat n k hk hkn) W i).arr := by
    rw [← hS]
    apply mem_image_of_mem
    rw [mem_window hbi]
    lia
  have hnmem_T : ¬ (play (slideStrat n k hk hkn) W (i + 1)).arr x ∈
      (midWindow n k i).image (play (slideStrat n k hk hkn) W (i + 1)).arr := by
    intro hmem
    obtain ⟨y, hy, hyv⟩ := mem_image.1 hmem
    have hyw : y ∈ window n k i := midWindow_subset_window hbi hy
    have hxw : x ∈ window n k i := by rw [mem_window hbi]; lia
    have heq : y = x := hinjOn_succ hyw hxw hyv
    rw [heq, mem_midWindow hbi] at hy
    lia
  have hmem_diff : (play (slideStrat n k hk hkn) W (i + 1)).arr x ∈
      (window n k i).image (play (slideStrat n k hk hkn) W i).arr \
      (midWindow n k i).image (play (slideStrat n k hk hkn) W (i + 1)).arr :=
    mem_sdiff.2 ⟨hmem_S, hnmem_T⟩
  rw [ha] at hmem_diff
  have hax : (play (slideStrat n k hk hkn) W (i + 1)).arr x = a := mem_singleton.1 hmem_diff
  unfold labelAt
  rw [dite_eq_left hcond]
  dsimp only
  rw [hSeq, hTeq, ha, dite_eq_left (singleton_nonempty a)]
  have hspec := (singleton_nonempty a).choose_spec
  rw [mem_singleton] at hspec
  rw [hspec]
  exact hax.symm

/-- The sliding strategy wins within `2n - k + 2` moves. -/
lemma slideStrat_wins {n k : ℕ} [NeZero n] (hk : 2 ≤ k) (hkn : k < n)
    (W : Wizard n) (hW : W.Valid) :
    (play (slideStrat n k hk hkn) W (2 * n - k + 2)).won := by
  by_cases hM : (play (slideStrat n k hk hkn) W (2 * n - k + 1)).won
  · exact won_mono hM (by lia)
  · have histMlen := (slide_play_facts hk hkn W hW hM (2 * n - k + 1) (le_refl _)).2.1
    have hpg : ∃ p q : Fin (2 * n - k), p ≠ q ∧
        labelAt n k ((play (slideStrat n k hk hkn) W (2 * n - k + 1)).hist) p.val =
        labelAt n k ((play (slideStrat n k hk hkn) W (2 * n - k + 1)).hist) q.val := by
      have hcard : Fintype.card (Fin n) < Fintype.card (Fin (2 * n - k)) := by
        rw [Fintype.card_fin, Fintype.card_fin]
        lia
      obtain ⟨x, y, hxy, hlab⟩ := Fintype.exists_ne_map_eq_of_card_lt
        (fun i : Fin (2 * n - k) ↦
          labelAt n k ((play (slideStrat n k hk hkn) W (2 * n - k + 1)).hist) i.val)
        hcard
      exact ⟨x, y, hxy, hlab⟩
    set p := hpg.choose with hp_def
    set q := hpg.choose_spec.choose with hq_def
    set hpq : p ≠ q := hpg.choose_spec.choose_spec.1 with hpq_def
    have hlab : labelAt n k ((play (slideStrat n k hk hkn) W (2 * n - k + 1)).hist) p.val =
        labelAt n k ((play (slideStrat n k hk hkn) W (2 * n - k + 1)).hist) q.val :=
      hpg.choose_spec.choose_spec.2
    have hQ : (slideStrat n k hk hkn) (play (slideStrat n k hk hkn) W (2 * n - k + 1)).hist =
        pairSet n k hk (le_of_lt hkn) p q hpq :=
      slideStrat_of_ge hk hkn (by rw [histMlen]; lia) hpg
    have harrp : (play (slideStrat n k hk hkn) W (2 * n - k + 1)).arr (posOf n k p) =
        labelAt n k ((play (slideStrat n k hk hkn) W (2 * n - k + 1)).hist) p.val := by
      have h1 := slide_labelAt_eq hk hkn W hW hM (posOf n k p) (by
        rw [posOf_val]; exact p.isLt)
      have h2 := slide_arr_frozen hk hkn W hW hM (posOf n k p) (by
        rw [posOf_val]; exact p.isLt) (2 * n - k + 1) (by
        rw [posOf_val]; have := p.isLt; lia) (le_refl _)
      exact h2.trans h1.symm
    have harrq : (play (slideStrat n k hk hkn) W (2 * n - k + 1)).arr (posOf n k q) =
        labelAt n k ((play (slideStrat n k hk hkn) W (2 * n - k + 1)).hist) q.val := by
      have h1 := slide_labelAt_eq hk hkn W hW hM (posOf n k q) (by
        rw [posOf_val]; exact q.isLt)
      have h2 := slide_arr_frozen hk hkn W hW hM (posOf n k q) (by
        rw [posOf_val]; exact q.isLt) (2 * n - k + 1) (by
        rw [posOf_val]; have := q.isLt; lia) (le_refl _)
      exact h2.trans h1.symm
    have hcond : ¬ ((pairSet n k hk (le_of_lt hkn) p q hpq).image
        (play (slideStrat n k hk hkn) W (2 * n - k + 1)).arr).card =
        (pairSet n k hk (le_of_lt hkn) p q hpq).card := by
      have hninj : ¬ Set.InjOn (play (slideStrat n k hk hkn) W (2 * n - k + 1)).arr
          ↑(pairSet n k hk (le_of_lt hkn) p q hpq) := by
        intro hinj
        have e1 : (play (slideStrat n k hk hkn) W (2 * n - k + 1)).arr (posOf n k p) =
            (play (slideStrat n k hk hkn) W (2 * n - k + 1)).arr (posOf n k q) := by
          rw [harrp, harrq, hlab]
        exact posOf_ne hpq (hinj (posOf_mem_pairSet hk (le_of_lt hkn) hpq)
          (posOf_mem_pairSet' hk (le_of_lt hkn) hpq) e1)
      exact fun h ↦ hninj (card_image_iff.1 h)
    have hwin : (play (slideStrat n k hk hkn) W (2 * n - k + 1 + 1)).won = true := by
      rw [play_succ,
        step_apply_of_not_won
          (Bool.eq_false_iff.1 (slide_play_facts hk hkn W hW hM (2 * n - k + 1)
            (le_refl _)).1),
        hQ, ite_eq_right hcond]
    exact hwin


/-! ## The wizard's evasive strategy for `k = n` -/

lemma exists_perm_injOn {n : ℕ} (a : Fin (2 * n) → Fin n)
    (hvalid : ∀ ℓ : Fin n, (univ.filter fun i ↦ a i = ℓ).card = 2)
    {S Q : Finset (Fin (2 * n))} (hS : S.card = n) (hQ : Q.card = n)
    (hSa : Set.InjOn a ↑S) (hQa : Set.InjOn a ↑Q)
    (Qn : Finset (Fin (2 * n))) (hQn : Qn.card = n) :
    ∃ τ : Equiv.Perm (Fin (2 * n)), (∀ i, i ∉ Q → τ i = i) ∧ Set.InjOn (a ∘ τ) ↑Qn := by
  have hcardn : Fintype.card (Fin n) = n := Fintype.card_fin n
  have hcard2n : Fintype.card (Fin (2 * n)) = 2 * n := Fintype.card_fin (2 * n)
  have huniv : (univ : Finset (Fin n)).card = n := by rw [Finset.card_univ, hcardn]
  -- Step 1: `a` maps both `S` and `Q` onto `univ`.
  have hSimg : S.image a = univ :=
    Finset.eq_univ_of_card _ ((Finset.card_image_iff.mpr hSa).trans (hS.trans hcardn.symm))
  have hQimg : Q.image a = univ :=
    Finset.eq_univ_of_card _ ((Finset.card_image_iff.mpr hQa).trans (hQ.trans hcardn.symm))
  -- Step 2: `a` also maps `Sᶜ` onto `univ`.
  have hScimg : Sᶜ.image a = univ := by
    rw [Finset.eq_univ_iff_forall]
    intro ℓ
    have hℓS : ℓ ∈ S.image a := by rw [hSimg]; exact Finset.mem_univ ℓ
    obtain ⟨i, hiS, hi⟩ := Finset.mem_image.mp hℓS
    have h2card : 1 < (univ.filter fun i ↦ a i = ℓ).card := by
      have hv := hvalid ℓ
      lia
    obtain ⟨j, hjf, hji⟩ := Finset.exists_mem_ne h2card i
    have hj : a j = ℓ := (Finset.mem_filter.mp hjf).2
    have hjS : j ∉ S := fun hjS' => hji ((hSa hiS hjS' (hi.trans hj.symm)).symm)
    exact Finset.mem_image.mpr ⟨j, Finset.mem_compl.mpr hjS, hj⟩
  have hSc : Sᶜ.card = n := by rw [Finset.card_compl, hcard2n, hS]; lia
  have hScInj : Set.InjOn a ↑Sᶜ :=
    Finset.card_image_iff.mp (by rw [hScimg, huniv]; exact hSc.symm)
  -- Step 3: `a` maps `Qᶜ` onto `univ`, and is injective on it.
  have hdisj : Disjoint ((S ∩ Q).image a) ((Sᶜ ∩ Q).image a) := by
    rw [Finset.disjoint_left]
    rintro ℓ h1 h2
    obtain ⟨i, hi, hiℓ⟩ := Finset.mem_image.mp h1
    obtain ⟨j, hj, hjℓ⟩ := Finset.mem_image.mp h2
    rw [Finset.mem_inter] at hi hj
    have hij : i = j := hQa hi.2 hj.2 (hiℓ.trans hjℓ.symm)
    subst hij
    exact (Finset.mem_compl.mp hj.1) hi.1
  have hQcimg : Qᶜ.image a = univ := by
    rw [Finset.eq_univ_iff_forall]
    intro ℓ
    have hℓSc : ℓ ∈ Sᶜ.image a := by rw [hScimg]; exact Finset.mem_univ ℓ
    obtain ⟨j, hjSc, hj⟩ := Finset.mem_image.mp hℓSc
    by_cases hjq : j ∈ Q
    · have hℓS : ℓ ∈ S.image a := by rw [hSimg]; exact Finset.mem_univ ℓ
      obtain ⟨i, hiS, hi⟩ := Finset.mem_image.mp hℓS
      by_cases hiq : i ∈ Q
      · have hA1 : ℓ ∈ (S ∩ Q).image a := Finset.mem_image.mpr ⟨i, Finset.mem_inter.mpr ⟨hiS, hiq⟩, hi⟩
        have hA2 : ℓ ∈ (Sᶜ ∩ Q).image a :=
          Finset.mem_image.mpr ⟨j, Finset.mem_inter.mpr ⟨hjSc, hjq⟩, hj⟩
        exact absurd hA2 (Finset.disjoint_left.mp hdisj hA1)
      · exact Finset.mem_image.mpr ⟨i, Finset.mem_compl.mpr hiq, hi⟩
    · exact Finset.mem_image.mpr ⟨j, Finset.mem_compl.mpr hjq, hj⟩
  have hQc : Qᶜ.card = n := by rw [Finset.card_compl, hcard2n, hQ]; lia
  have hQcInj : Set.InjOn a ↑Qᶜ :=
    Finset.card_image_iff.mp (by rw [hQcimg, huniv]; exact hQc.symm)
  -- Step 4: the set `T` of labels already hit by `Qn \ Q`, and card computations.
  set T : Finset (Fin n) := (Qn \ Q).image a with hT
  have hsub : (↑(Qn \ Q) : Set (Fin (2 * n))) ⊆ ↑Qᶜ := by
    intro x hx
    rw [Finset.mem_coe, Finset.mem_sdiff] at hx
    rw [Finset.mem_coe, Finset.mem_compl]
    exact hx.2
  have hTcard : T.card = (Qn \ Q).card := Finset.card_image_iff.mpr (Set.InjOn.mono hsub hQcInj)
  have h1 : (Q \ Qn).card = n - (Q ∩ Qn).card := by rw [Finset.card_sdiff, hQ, inter_comm Qn Q]
  have h2 : (Qn \ Q).card = n - (Q ∩ Qn).card := by rw [Finset.card_sdiff, hQn]
  have hTcard2 : T.card = n - (Q ∩ Qn).card := hTcard.trans h2
  have hQQnT : (Q \ Qn).card = T.card := h1.trans hTcard2.symm
  have hcle : (Q ∩ Qn).card ≤ n := by
    have hle := Finset.card_le_card (Finset.inter_subset_left : Q ∩ Qn ⊆ Q)
    lia
  have hcunivT : (Q ∩ Qn).card = (univ \ T).card := by
    rw [Finset.card_univ_sdiff, hcardn, hTcard2]
    lia
  -- Step 5: the "target labeling" `d`, which is bijective on `Q`.
  have e1 : ↥(Q ∩ Qn) ≃ ↥(univ \ T) :=
    Fintype.equivOfCardEq (by rw [Fintype.card_coe, Fintype.card_coe]; exact hcunivT)
  have e2 : ↥(Q \ Qn) ≃ ↥T :=
    Fintype.equivOfCardEq (by rw [Fintype.card_coe, Fintype.card_coe]; exact hQQnT)
  set d : Fin (2 * n) → Fin n := fun i =>
    if h : i ∈ Q ∩ Qn then (e1 ⟨i, h⟩ : Fin n)
    else if h' : i ∈ Q \ Qn then (e2 ⟨i, h'⟩ : Fin n)
    else a i with hd
  have hdQinj : Function.Injective (fun i : ↥Q => d i) := by
    rintro ⟨i, hiQ⟩ ⟨j, hjQ⟩ hij
    have hij' : d i = d j := hij
    by_cases hic : i ∈ Q ∩ Qn
    · have hdi : d i = (e1 ⟨i, hic⟩ : Fin n) := dite_eq_left hic
      by_cases hjc : j ∈ Q ∩ Qn
      · have hdj : d j = (e1 ⟨j, hjc⟩ : Fin n) := dite_eq_left hjc
        rw [hdi, hdj] at hij'
        have hval : i = j := congrArg Subtype.val (e1.injective (Subtype.ext hij'))
        exact Subtype.ext hval
      · have hj2 : j ∈ Q \ Qn := Finset.mem_sdiff.mpr ⟨hjQ, fun hjn => hjc (Finset.mem_inter.mpr ⟨hjQ, hjn⟩)⟩
        have hdj : d j = (e2 ⟨j, hj2⟩ : Fin n) := by
          calc d j = (if h' : j ∈ Q \ Qn then (e2 ⟨j, h'⟩ : Fin n) else a j) := dite_eq_right hjc
            _ = (e2 ⟨j, hj2⟩ : Fin n) := dite_eq_left hj2
        rw [hdi, hdj] at hij'
        have hA : (e1 ⟨i, hic⟩ : Fin n) ∈ univ \ T := (e1 ⟨i, hic⟩).property
        rw [hij'] at hA
        exact absurd (e2 ⟨j, hj2⟩).property (Finset.mem_sdiff.mp hA).2
    · have hi2 : i ∈ Q \ Qn := Finset.mem_sdiff.mpr ⟨hiQ, fun hin => hic (Finset.mem_inter.mpr ⟨hiQ, hin⟩)⟩
      have hdi : d i = (e2 ⟨i, hi2⟩ : Fin n) := by
        calc d i = (if h' : i ∈ Q \ Qn then (e2 ⟨i, h'⟩ : Fin n) else a i) := dite_eq_right hic
          _ = (e2 ⟨i, hi2⟩ : Fin n) := dite_eq_left hi2
      by_cases hjc : j ∈ Q ∩ Qn
      · have hdj : d j = (e1 ⟨j, hjc⟩ : Fin n) := dite_eq_left hjc
        rw [hdi, hdj] at hij'
        have hA : (e1 ⟨j, hjc⟩ : Fin n) ∈ univ \ T := (e1 ⟨j, hjc⟩).property
        rw [← hij'] at hA
        exact absurd (e2 ⟨i, hi2⟩).property (Finset.mem_sdiff.mp hA).2
      · have hj2 : j ∈ Q \ Qn := Finset.mem_sdiff.mpr ⟨hjQ, fun hjn => hjc (Finset.mem_inter.mpr ⟨hjQ, hjn⟩)⟩
        have hdj : d j = (e2 ⟨j, hj2⟩ : Fin n) := by
          calc d j = (if h' : j ∈ Q \ Qn then (e2 ⟨j, h'⟩ : Fin n) else a j) := dite_eq_right hjc
            _ = (e2 ⟨j, hj2⟩ : Fin n) := dite_eq_left hj2
        rw [hdi, hdj] at hij'
        have hval : i = j := congrArg Subtype.val (e2.injective (Subtype.ext hij'))
        exact Subtype.ext hval
  have hdQsurj : Function.Surjective (fun i : ↥Q => d i) := by
    intro ℓ
    by_cases hℓ : ℓ ∈ T
    · obtain ⟨⟨i, hi2⟩, hie⟩ := e2.surjective ⟨ℓ, hℓ⟩
      have hiQ : i ∈ Q := (Finset.mem_sdiff.mp hi2).1
      have hic : i ∉ Q ∩ Qn := fun h => (Finset.mem_sdiff.mp hi2).2 (Finset.mem_inter.mp h).2
      have hdi : d i = (e2 ⟨i, hi2⟩ : Fin n) := by
        calc d i = (if h' : i ∈ Q \ Qn then (e2 ⟨i, h'⟩ : Fin n) else a i) := dite_eq_right hic
          _ = (e2 ⟨i, hi2⟩ : Fin n) := dite_eq_left hi2
      refine ⟨⟨i, hiQ⟩, ?_⟩
      show d i = ℓ
      rw [hdi]
      exact congrArg Subtype.val hie
    · have hℓ' : ℓ ∈ univ \ T := Finset.mem_sdiff.mpr ⟨Finset.mem_univ ℓ, hℓ⟩
      obtain ⟨⟨i, hic⟩, hie⟩ := e1.surjective ⟨ℓ, hℓ'⟩
      have hiQ : i ∈ Q := (Finset.mem_inter.mp hic).1
      have hdi : d i = (e1 ⟨i, hic⟩ : Fin n) := dite_eq_left hic
      refine ⟨⟨i, hiQ⟩, ?_⟩
      show d i = ℓ
      rw [hdi]
      exact congrArg Subtype.val hie
  -- Step 6: a permutation `g` of `Q` under which `a` realizes `d`.
  have hainj : Function.Injective (fun i : ↥Q => a i) := by
    rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
    exact Subtype.ext (hQa hi hj hij)
  have hasurj : Function.Surjective (fun i : ↥Q => a i) := by
    intro ℓ
    have hℓ : ℓ ∈ Q.image a := by rw [hQimg]; exact Finset.mem_univ ℓ
    obtain ⟨i, hiQ, hi⟩ := Finset.mem_image.mp hℓ
    exact ⟨⟨i, hiQ⟩, hi⟩
  set dEquiv : ↥Q ≃ Fin n := Equiv.ofBijective _ ⟨hdQinj, hdQsurj⟩ with hdEquivEq
  set aEquiv : ↥Q ≃ Fin n := Equiv.ofBijective _ ⟨hainj, hasurj⟩ with haEquivEq
  set g : Equiv.Perm ↥Q := dEquiv.trans aEquiv.symm with hgEq
  have haapp : ∀ i : ↥Q, aEquiv i = a i := fun i => by rw [haEquivEq]; rfl
  have hdapp : ∀ i : ↥Q, dEquiv i = d i := fun i => by rw [hdEquivEq]; rfl
  have hgprop : ∀ i : ↥Q, a (g i : Fin (2 * n)) = d i := by
    intro i
    have h1 : g i = aEquiv.symm (dEquiv i) := by rw [hgEq, Equiv.trans_apply]
    calc a (g i : Fin (2 * n)) = aEquiv (g i) := (haapp (g i)).symm
      _ = aEquiv (aEquiv.symm (dEquiv i)) := by rw [← h1]
      _ = dEquiv i := Equiv.apply_symm_apply aEquiv (dEquiv i)
      _ = d i := hdapp i
  -- Step 7: extend `g` to a permutation of `Fin (2 * n)` fixing everything outside `Q`.
  set τ : Equiv.Perm (Fin (2 * n)) := Equiv.Perm.extendDomain g (Equiv.refl ↥Q) with hτEq
  have hτfix : ∀ i, i ∉ Q → τ i = i := by
    intro i hi
    rw [hτEq]
    exact Equiv.Perm.extendDomain_apply_not_subtype g (Equiv.refl ↥Q) hi
  have hτQ : ∀ i : Fin (2 * n), i ∈ Q → a (τ i) = d i := by
    intro i hi
    have h1 : τ i = (g ⟨i, hi⟩ : Fin (2 * n)) := by
      rw [hτEq]
      exact Equiv.Perm.extendDomain_apply_subtype g (Equiv.refl ↥Q) hi
    rw [h1]
    exact hgprop ⟨i, hi⟩
  -- Step 8: `a ∘ τ` maps `Qn` onto `univ`, hence is injective on `Qn`.
  refine ⟨τ, hτfix, ?_⟩
  rw [← Finset.card_image_iff, hQn]
  have himg : Qn.image (a ∘ τ) = univ := by
    rw [Finset.eq_univ_iff_forall]
    intro ℓ
    by_cases hℓ : ℓ ∈ T
    · rw [hT] at hℓ
      obtain ⟨i, hi, hiℓ⟩ := Finset.mem_image.mp hℓ
      rw [Finset.mem_sdiff] at hi
      exact Finset.mem_image.mpr ⟨i, hi.1, by rw [Function.comp_apply, hτfix i hi.2]; exact hiℓ⟩
    · have hℓ' : ℓ ∈ univ \ T := Finset.mem_sdiff.mpr ⟨Finset.mem_univ ℓ, hℓ⟩
      obtain ⟨⟨i, hic⟩, hie⟩ := e1.surjective ⟨ℓ, hℓ'⟩
      refine Finset.mem_image.mpr ⟨i, (Finset.mem_inter.mp hic).2, ?_⟩
      rw [Function.comp_apply, hτQ i (Finset.mem_inter.mp hic).1]
      have hdi : d i = (e1 ⟨i, hic⟩ : Fin n) := dite_eq_left hic
      rw [hdi]
      exact congrArg Subtype.val hie
  rw [himg]
  exact huniv


/-- The equivalence between the first query and the labels. -/
noncomputable def initEquiv₁ {n : ℕ} (σ : Strategy n) (hσ : σ.Valid n) : ↥(σ []) ≃ Fin n :=
  Fintype.equivOfCardEq (by rw [Fintype.card_coe, hσ, Fintype.card_fin])

/-- The equivalence between the complement of the first query and the labels. -/
noncomputable def initEquiv₂ {n : ℕ} (σ : Strategy n) (hσ : σ.Valid n) : ↥(σ [])ᶜ ≃ Fin n :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_coe, card_compl, hσ, Fintype.card_fin (2 * n), Fintype.card_fin n]; lia)

/-- The wizard's initial arrangement: a bijection of each of `σ []` and its
complement onto the labels. -/
noncomputable def initArr {n : ℕ} (σ : Strategy n) (hσ : σ.Valid n) : Arrangement n :=
  fun i ↦ if h : i ∈ σ [] then initEquiv₁ σ hσ ⟨i, h⟩ else initEquiv₂ σ hσ ⟨i, mem_compl.2 h⟩

lemma initArr_apply_of_mem {n : ℕ} {σ : Strategy n} {hσ : σ.Valid n} {i : Fin (2 * n)}
    (hi : i ∈ σ []) : initArr σ hσ i = initEquiv₁ σ hσ ⟨i, hi⟩ := dite_eq_left hi

lemma initArr_apply_of_notMem {n : ℕ} {σ : Strategy n} {hσ : σ.Valid n} {i : Fin (2 * n)}
    (hi : i ∉ σ []) : initArr σ hσ i = initEquiv₂ σ hσ ⟨i, mem_compl.2 hi⟩ := dite_eq_right hi

lemma initArr_valid {n : ℕ} (σ : Strategy n) (hσ : σ.Valid n) : (initArr σ hσ).Valid := by
  intro ℓ
  have hfiber : (univ.filter fun i ↦ initArr σ hσ i = ℓ) =
      {((initEquiv₁ σ hσ).symm ℓ).val, ((initEquiv₂ σ hσ).symm ℓ).val} := by
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
    by_cases hi : i ∈ σ []
    · rw [initArr_apply_of_mem hi]
      constructor
      · intro h
        left
        have h1 : (⟨i, hi⟩ : ↥(σ [])) = (initEquiv₁ σ hσ).symm ℓ :=
          (initEquiv₁ σ hσ).injective (by
            rw [h]
            exact ((initEquiv₁ σ hσ).apply_symm_apply ℓ).symm)
        exact congrArg Subtype.val h1
      · rintro (rfl | rfl)
        · rw [show (⟨_, hi⟩ : ↥(σ [])) = (initEquiv₁ σ hσ).symm ℓ from Subtype.ext rfl]
          exact (initEquiv₁ σ hσ).apply_symm_apply ℓ
        · exfalso
          exact (mem_compl.1 ((initEquiv₂ σ hσ).symm ℓ).2) hi
    · rw [initArr_apply_of_notMem hi]
      constructor
      · intro h
        right
        have h1 : (⟨i, mem_compl.2 hi⟩ : ↥(σ [])ᶜ) = (initEquiv₂ σ hσ).symm ℓ :=
          (initEquiv₂ σ hσ).injective (by
            rw [h]
            exact ((initEquiv₂ σ hσ).apply_symm_apply ℓ).symm)
        exact congrArg Subtype.val h1
      · rintro (rfl | rfl)
        · exfalso
          exact hi ((initEquiv₁ σ hσ).symm ℓ).2
        · exact (Equiv.eq_symm_apply (initEquiv₂ σ hσ)).mp rfl
  rw [hfiber, card_insert_of_notMem (by
    simp only [mem_singleton]
    intro heq
    have ha : ((initEquiv₁ σ hσ).symm ℓ).val ∈ σ [] := ((initEquiv₁ σ hσ).symm ℓ).2
    rw [heq] at ha
    exact (mem_compl.1 ((initEquiv₂ σ hσ).symm ℓ).2) ha), card_singleton]

lemma initArr_injOn {n : ℕ} (σ : Strategy n) (hσ : σ.Valid n) :
    Set.InjOn (initArr σ hσ) ↑(σ []) ∧ Set.InjOn (initArr σ hσ) ↑(σ [])ᶜ := by
  constructor
  · intro i hi j hj hij
    rw [initArr_apply_of_mem (mem_coe.1 hi), initArr_apply_of_mem (mem_coe.1 hj)] at hij
    exact congrArg Subtype.val ((initEquiv₁ σ hσ).injective hij)
  · intro i hi j hj hij
    rw [initArr_apply_of_notMem (mem_compl.1 (mem_coe.1 hi)),
      initArr_apply_of_notMem (mem_compl.1 (mem_coe.1 hj))] at hij
    exact congrArg Subtype.val ((initEquiv₂ σ hσ).injective hij)

/-- The permutation the wizard uses in response to the query `σ l`:
it keeps the next query free of matches. -/
noncomputable def permOf {n : ℕ} (σ : Strategy n) (_hσ : σ.Valid n)
    (l : List (Observation n)) (a : Arrangement n) : Equiv.Perm (Fin (2 * n)) :=
  if h : ∃ τ : Equiv.Perm (Fin (2 * n)), (∀ i, i ∉ σ l → τ i = i) ∧
      Set.InjOn (a ∘ τ) ↑(σ (l ++ [(σ l, reveal a (σ l))])) then
    h.choose
  else 1

/-- Auxiliary for `wizArr`, recursing on the reversed history. -/
noncomputable def wizArrAux {n : ℕ} (σ : Strategy n) (hσ : σ.Valid n) :
    List (Observation n) → Arrangement n
  | [] => initArr σ hσ
  | _ :: r => wizArrAux σ hσ r ∘ permOf σ hσ r.reverse (wizArrAux σ hσ r)

/-- The arrangement after the given history, when the wizard plays `permOf`. -/
noncomputable def wizArr {n : ℕ} (σ : Strategy n) (hσ : σ.Valid n)
    (l : List (Observation n)) : Arrangement n :=
  wizArrAux σ hσ l.reverse

lemma wizArr_nil {n : ℕ} (σ : Strategy n) (hσ : σ.Valid n) :
    wizArr σ hσ [] = initArr σ hσ := rfl

lemma wizArr_append {n : ℕ} (σ : Strategy n) (hσ : σ.Valid n)
    (l : List (Observation n)) (obs : Observation n) :
    wizArr σ hσ (l ++ [obs]) = wizArr σ hσ l ∘ permOf σ hσ l (wizArr σ hσ l) := by
  simp only [wizArr, List.reverse_append, List.reverse_singleton, List.singleton_append,
    wizArrAux, List.reverse_reverse]

/-- The wizard that evades the player forever when `k = n`. -/
noncomputable def evasiveWizard {n : ℕ} (σ : Strategy n) (hσ : σ.Valid n) : Wizard n where
  init := initArr σ hσ
  perm := fun l Q ↦ if Q = σ l then permOf σ hσ l (wizArr σ hσ l) else 1

lemma evasiveWizard_valid {n : ℕ} (σ : Strategy n) (hσ : σ.Valid n) :
    (evasiveWizard σ hσ).Valid := by
  refine ⟨initArr_valid σ hσ, ?_⟩
  intro l Q i hi
  show (if Q = σ l then permOf σ hσ l (wizArr σ hσ l) else 1) i = i
  split
  · next hQ =>
    subst hQ
    show (if h : ∃ τ : Equiv.Perm (Fin (2 * n)), (∀ i, i ∉ σ l → τ i = i) ∧
        Set.InjOn ((wizArr σ hσ l) ∘ τ) ↑(σ (l ++ [(σ l, reveal (wizArr σ hσ l) (σ l))])) then
        h.choose else 1) i = i
    split
    · next hex => exact hex.choose_spec.1 i hi
    · rfl
  · rfl

/-- The history after `j` rounds against the evasive wizard. -/
noncomputable def evasiveHist {n : ℕ} (σ : Strategy n) (hσ : σ.Valid n) :
    ℕ → List (Observation n)
  | 0 => []
  | j + 1 => evasiveHist σ hσ j ++
      [(σ (evasiveHist σ hσ j), reveal (wizArr σ hσ (evasiveHist σ hσ j))
        (σ (evasiveHist σ hσ j)))]

/-- The invariant maintained by the evasive wizard: the current arrangement is
valid, and injective both on the last query and on the next query. -/
lemma evasive_inv {n : ℕ} (σ : Strategy n) (hσ : σ.Valid n) (j : ℕ) :
    (wizArr σ hσ (evasiveHist σ hσ j)).Valid ∧
    Set.InjOn (wizArr σ hσ (evasiveHist σ hσ j)) ↑(σ ((evasiveHist σ hσ j).dropLast)) ∧
    Set.InjOn (wizArr σ hσ (evasiveHist σ hσ j)) ↑(σ (evasiveHist σ hσ j)) := by
  induction j with
  | zero =>
    exact ⟨initArr_valid σ hσ, (initArr_injOn σ hσ).1, (initArr_injOn σ hσ).1⟩
  | succ j ih =>
    obtain ⟨hvalid, hinjS, hinjQ⟩ := ih
    set l := evasiveHist σ hσ j with ldef
    set a := wizArr σ hσ l with adef
    have hhist : evasiveHist σ hσ (j + 1) = l ++
        [(σ l, reveal a (σ l))] := rfl
    have harr : wizArr σ hσ (evasiveHist σ hσ (j + 1)) = a ∘ permOf σ hσ l a := by
      rw [hhist]
      exact wizArr_append σ hσ l _
    have hex : ∃ τ : Equiv.Perm (Fin (2 * n)), (∀ i, i ∉ σ l → τ i = i) ∧
        Set.InjOn (a ∘ τ) ↑(σ (l ++ [(σ l, reveal a (σ l))])) :=
      exists_perm_injOn a hvalid (hσ l.dropLast) (hσ l) hinjS hinjQ _ (hσ _)
    have hτ : permOf σ hσ l a = hex.choose := dite_eq_left hex
    rw [harr, hτ]
    refine ⟨?_, ?_, ?_⟩
    · intro ℓ
      have hfib : (univ.filter fun i ↦ (a ∘ hex.choose) i = ℓ) =
          (univ.filter fun i ↦ a i = ℓ).image hex.choose.symm := by
        ext x
        simp only [mem_filter, mem_univ, true_and, mem_image, Function.comp_apply]
        constructor
        · intro hx
          exact ⟨hex.choose x, hx, by simp⟩
        · rintro ⟨y, hy, rfl⟩
          rw [hex.choose.apply_symm_apply]
          exact hy
      rw [hfib, card_image_of_injective _ (Equiv.injective _), hvalid ℓ]
    · rw [hhist, List.dropLast_concat]
      have hfix : ∀ i, i ∉ σ l → hex.choose i = i := hex.choose_spec.1
      have himg : (σ l).image (a ∘ hex.choose) = univ := by
        rw [← image_image, image_eq_of_perm_fix hfix]
        exact eq_univ_of_card _ ((card_image_iff.mpr hinjQ).trans (by
          rw [hσ l, Fintype.card_fin]))
      rw [← card_image_iff, himg, card_univ, Fintype.card_fin, hσ l]
    · exact hex.choose_spec.2

/-- Playing against the evasive wizard, the player never wins. -/
lemma evasive_play {n : ℕ} (σ : Strategy n) (hσ : σ.Valid n) (m : ℕ) :
    play σ (evasiveWizard σ hσ) m =
      { arr := wizArr σ hσ (evasiveHist σ hσ m)
      , hist := evasiveHist σ hσ m
      , won := false } := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hinj : Set.InjOn (wizArr σ hσ (evasiveHist σ hσ m)) ↑(σ (evasiveHist σ hσ m)) :=
      (evasive_inv σ hσ m).2.2
    rw [play_succ, ih, step_apply_of_not_won (by simp),
      ite_eq_left (card_image_iff.mpr hinj)]
    have hperm : (evasiveWizard σ hσ).perm (evasiveHist σ hσ m) (σ (evasiveHist σ hσ m)) =
        permOf σ hσ (evasiveHist σ hσ m) (wizArr σ hσ (evasiveHist σ hσ m)) := ite_eq_left rfl
    have hhist : evasiveHist σ hσ (m + 1) = evasiveHist σ hσ m ++
        [(σ (evasiveHist σ hσ m), reveal (wizArr σ hσ (evasiveHist σ hσ m))
          (σ (evasiveHist σ hσ m)))] := rfl
    dsimp only
    rw [hperm, hhist, wizArr_append]

/-- When `k = n`, no strategy can guarantee a win: the game is not winnable. -/
lemma not_winnable_of_eq {n : ℕ} (σ : Strategy n) (hσ : σ.Valid n) :
    ∃ W : Wizard n, W.Valid ∧ ∀ m, (play σ W m).won = false :=
  ⟨evasiveWizard σ hσ, evasiveWizard_valid σ hσ, fun m ↦ by rw [evasive_play σ hσ m]⟩

snip end

determine answer : ℕ → ℕ → Prop := fun n k ↦ k < n

problem usa2016_p6 (n k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n) : Winnable n k ↔ answer n k := by
  show Winnable n k ↔ k < n
  constructor
  · rintro ⟨m, hm, σ, hσ, hwin⟩
    by_contra hnk
    have hkn' : k = n := by lia
    subst hkn'
    obtain ⟨W, hW, hnot⟩ := not_winnable_of_eq σ hσ
    have h1 := hwin W hW
    rw [hnot m] at h1
    exact Bool.noConfusion h1
  · intro h
    have : NeZero n := ⟨by lia⟩
    exact ⟨2 * n - k + 2, by lia, slideStrat n k hk h, winStrat_valid n k hk (le_of_lt h),
      fun W hW ↦ slideStrat_wins hk h W hW⟩

end Usa2016P6
