/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.NormNum
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 1986, Problem 2

Five professors attended a lecture. Each fell asleep just twice. For each pair
there was a moment when both were asleep. Show that there was a moment when
three of them were asleep.
-/

namespace Usa1986P2

/-- Each professor `p : Fin 5` takes two naps, and nap `k : Fin 2` of professor
`p` is the closed interval `[s p k, e p k]`. Professor `p` is asleep at time
`t` if `t` belongs to one of these two nap intervals. -/
def Asleep (s e : Fin 5 → Fin 2 → ℝ) (p : Fin 5) (t : ℝ) : Prop :=
  ∃ k : Fin 2, s p k ≤ t ∧ t ≤ e p k

snip begin

/-- The ten pairs of professors, as the 2-element subsets of `Fin 5`. -/
def pairs : Finset (Finset (Fin 5)) := Finset.powersetCard 2 Finset.univ

/-- The type of pairs of professors. -/
abbrev PairSet := { A : Finset (Fin 5) // A ∈ pairs }

variable {s e : Fin 5 → Fin 2 → ℝ}

open Classical in
/-- Candidate "first moments" for a set `A` of professors: nap-start times of
members of `A` at which every member of `A` is asleep. -/
noncomputable def cands (s e : Fin 5 → Fin 2 → ℝ) (A : Finset (Fin 5)) : Finset ℝ :=
  Finset.filter (fun u ↦ ∀ p ∈ A, Asleep s e p u)
    (A.biUnion fun p ↦ Finset.image (s p) Finset.univ)

/-- Membership in `cands`: a nap-start time of a member of `A` at which every
member of `A` is asleep. -/
lemma mem_cands {A : Finset (Fin 5)} {u : ℝ} :
    u ∈ cands s e A ↔
      (∃ p ∈ A, ∃ k : Fin 2, s p k = u) ∧ ∀ p ∈ A, Asleep s e p u := by
  unfold cands
  simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ,
    true_and]

/-- If all members of a nonempty set `A` of professors are asleep at time `t`,
then some nap-start time `u ≤ t` of a member of `A` is already a moment when
all members of `A` are asleep. -/
lemma exists_mem_cands_le {A : Finset (Fin 5)} (hA : A.Nonempty) {t : ℝ}
    (ht : ∀ p ∈ A, Asleep s e p t) : ∃ u ∈ cands s e A, u ≤ t := by
  classical
  have ht' : ∀ p : A, ∃ k : Fin 2, s p.1 k ≤ t ∧ t ≤ e p.1 k := fun p ↦ ht p.1 p.2
  choose k hk₁ hk₂ using ht'
  obtain ⟨p₀, -, hmax⟩ :=
    A.attach.exists_max_image (fun p ↦ s p.1 (k p)) (Finset.attach_nonempty_iff.mpr hA)
  refine ⟨s p₀.1 (k p₀), mem_cands.mpr ⟨⟨p₀.1, p₀.2, k p₀, rfl⟩, fun p hp ↦
    ⟨k ⟨p, hp⟩, hmax ⟨p, hp⟩ (Finset.mem_attach _ _), (hk₁ p₀).trans (hk₂ ⟨p, hp⟩)⟩⟩, hk₁ p₀⟩

/-- The first moment at which all members of `A` are simultaneously asleep. -/
noncomputable def f (s e : Fin 5 → Fin 2 → ℝ) (A : Finset (Fin 5))
    (h : (cands s e A).Nonempty) : ℝ := (cands s e A).min' h

/-- All members of `A` are asleep at the first common moment. -/
lemma f_asleep {A : Finset (Fin 5)} {h : (cands s e A).Nonempty} :
    ∀ p ∈ A, Asleep s e p (f s e A h) := by
  have hm : (cands s e A).min' h ∈ cands s e A := Finset.min'_mem _ h
  exact (mem_cands.mp hm).2

/-- The first common moment is a nap-start time of some member of `A`. -/
lemma f_mem {A : Finset (Fin 5)} {h : (cands s e A).Nonempty} :
    ∃ p ∈ A, ∃ k : Fin 2, f s e A h = s p k := by
  have hm : (cands s e A).min' h ∈ cands s e A := Finset.min'_mem _ h
  obtain ⟨p, hp, k, hkp⟩ := (mem_cands.mp hm).1
  exact ⟨p, hp, k, hkp.symm⟩

/-- The first common moment is at most any moment at which all members of `A`
are asleep. -/
lemma f_le {A : Finset (Fin 5)} (hA : A.Nonempty) {h : (cands s e A).Nonempty}
    {t : ℝ} (ht : ∀ p ∈ A, Asleep s e p t) : f s e A h ≤ t := by
  obtain ⟨u, hu, hut⟩ := exists_mem_cands_le hA ht
  exact (Finset.min'_le _ _ hu).trans hut

/-- Pairs of professors have candidate first moments. -/
lemma cands_nonempty
    (hsleep : ∀ p q : Fin 5, p ≠ q → ∃ t, Asleep s e p t ∧ Asleep s e q t)
    {A : Finset (Fin 5)} (hA : A.card = 2) : (cands s e A).Nonempty := by
  obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.mp hA
  obtain ⟨t, hpt, hqt⟩ := hsleep p q hpq
  have ht : ∀ r ∈ ({p, q} : Finset (Fin 5)), Asleep s e r t := by
    intro r hr
    rw [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact hpt
    · exact hqt
  obtain ⟨u, hu, -⟩ := exists_mem_cands_le ⟨p, Finset.mem_insert_self p {q}⟩ ht
  exact ⟨u, hu⟩

/-- The first moment when both members of a pair `A` are asleep. -/
noncomputable def F
    (hsleep : ∀ p q : Fin 5, p ≠ q → ∃ t, Asleep s e p t ∧ Asleep s e q t)
    (A : PairSet) : ℝ :=
  f s e A.1 (cands_nonempty hsleep (Finset.mem_powersetCard.mp A.2).2)

/-- Both members of a pair are asleep at the pair's first common moment. -/
lemma F_asleep
    (hsleep : ∀ p q : Fin 5, p ≠ q → ∃ t, Asleep s e p t ∧ Asleep s e q t)
    (A : PairSet) {p : Fin 5} (hp : p ∈ A.1) : Asleep s e p (F hsleep A) :=
  f_asleep p hp

/-- A pair's first common moment is a falling-asleep event: it is the start
time of a nap of one of the two members. -/
lemma F_mem
    (hsleep : ∀ p q : Fin 5, p ≠ q → ∃ t, Asleep s e p t ∧ Asleep s e q t)
    (A : PairSet) : ∃ p ∈ A.1, ∃ k : Fin 2, F hsleep A = s p k :=
  f_mem

snip end

problem usa1986_p2 (s e : Fin 5 → Fin 2 → ℝ)
    (hsleep : ∀ p q : Fin 5, p ≠ q → ∃ t, Asleep s e p t ∧ Asleep s e q t) :
    ∃ t : ℝ, ∃ p q r : Fin 5, p ≠ q ∧ p ≠ r ∧ q ≠ r ∧
      Asleep s e p t ∧ Asleep s e q t ∧ Asleep s e r t := by
  classical
  -- There are ten pairs of professors.
  have hcard_pairs : pairs.card = 10 := by
    rw [pairs, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    decide
  by_cases hinj : ∀ A B : PairSet, F hsleep A = F hsleep B → A = B
  swap
  · -- If two different pairs have the same first common moment, then at that
    -- moment at least three professors are asleep.
    push Not at hinj
    obtain ⟨A, B, hFAB, hAB⟩ := hinj
    have hA2 : A.1.card = 2 := (Finset.mem_powersetCard.mp A.2).2
    have hB2 : B.1.card = 2 := (Finset.mem_powersetCard.mp B.2).2
    obtain ⟨p, q, hpq, hAeq⟩ := Finset.card_eq_two.mp hA2
    have hBsub : ¬ B.1 ⊆ A.1 := fun hsub ↦ hAB (Subtype.ext
      (Finset.eq_of_subset_of_card_le hsub (Nat.le_of_eq (hA2.trans hB2.symm))).symm)
    rw [Finset.not_subset] at hBsub
    obtain ⟨r, hrB, hrA⟩ := hBsub
    rw [hAeq, Finset.mem_insert, Finset.mem_singleton] at hrA
    push Not at hrA
    have hpmem : p ∈ A.1 := by rw [hAeq]; exact Finset.mem_insert_self _ _
    have hqmem : q ∈ A.1 := by
      rw [hAeq]; exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))
    have hrasleep : Asleep s e r (F hsleep A) := hFAB ▸ F_asleep hsleep B hrB
    exact ⟨F hsleep A, p, q, r, hpq, hrA.1.symm, hrA.2.symm,
      F_asleep hsleep A hpmem, F_asleep hsleep A hqmem, hrasleep⟩
  · -- Otherwise the ten first moments are all distinct. The following counting
    -- argument (kalva) then gives a contradiction: the ten moments are ten
    -- distinct falling-asleep events, but the earliest of them uses up two of
    -- the ten available events, leaving only eight later events for nine
    -- later moments.
    exfalso
    set S := pairs.attach.image (F hsleep) with hSdef
    have hInjOn : Set.InjOn (F hsleep) ↑pairs.attach := fun A _ B _ h ↦ hinj A B h
    have hS_card : S.card = 10 := by
      rw [hSdef, Finset.card_image_of_injOn hInjOn, Finset.card_attach, hcard_pairs]
    have hS_ne : S.Nonempty := by rw [← Finset.card_pos, hS_card]; norm_num
    -- The earliest of the ten moments.
    have hS_ne' : (pairs.attach.image (F hsleep)).Nonempty := hSdef ▸ hS_ne
    obtain ⟨A₀, -, hA₀⟩ := Finset.mem_image.mp (Finset.min'_mem _ hS_ne')
    have hA₀' : F hsleep A₀ = S.min' hS_ne := hA₀
    have hA₀2 : A₀.1.card = 2 := (Finset.mem_powersetCard.mp A₀.2).2
    obtain ⟨p₀, q₀, hp₀q₀, hA₀eq⟩ := Finset.card_eq_two.mp hA₀2
    have hp₀mem : p₀ ∈ A₀.1 := by rw [hA₀eq]; exact Finset.mem_insert_self _ _
    have hq₀mem : q₀ ∈ A₀.1 := by
      rw [hA₀eq]; exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))
    have hp₀asleep : Asleep s e p₀ (S.min' hS_ne) := hA₀' ▸ F_asleep hsleep A₀ hp₀mem
    have hq₀asleep : Asleep s e q₀ (S.min' hS_ne) := hA₀' ▸ F_asleep hsleep A₀ hq₀mem
    obtain ⟨k₀, hk₀le, -⟩ := hp₀asleep
    obtain ⟨l₀, hl₀le, -⟩ := hq₀asleep
    -- Each of the ten moments is a falling-asleep event (professor, nap).
    have key : ∀ A : PairSet, ∃ pk : Fin 5 × Fin 2, F hsleep A = s pk.1 pk.2 := by
      intro A
      obtain ⟨p, -, k, hk⟩ := F_mem hsleep A
      exact ⟨(p, k), hk⟩
    choose g hg using key
    -- The nine later moments give nine distinct events.
    set T := (pairs.attach.erase A₀).image g with hTdef
    have hg_inj : Set.InjOn g ↑(pairs.attach.erase A₀) := by
      intro A _ B _ hAB
      exact hinj A B (by rw [hg A, hg B, hAB])
    have hA₀mem : A₀ ∈ pairs.attach := Finset.mem_attach _ _
    have hT_card : T.card = 9 := by
      have h2 := Finset.card_erase_of_mem hA₀mem
      rw [Finset.card_attach, hcard_pairs] at h2
      have h3 := Finset.card_image_of_injOn hg_inj
      rw [hTdef, h3]
      omega
    -- All nine happen strictly after the earliest moment.
    have hT_gt : ∀ pk : Fin 5 × Fin 2, pk ∈ T → S.min' hS_ne < s pk.1 pk.2 := by
      intro pk hpk
      rw [hTdef, Finset.mem_image] at hpk
      obtain ⟨A, hAerase, hgA⟩ := hpk
      rw [← hgA, ← hg A]
      refine lt_of_le_of_ne (Finset.min'_le S _ ?_) ?_
      · rw [hSdef, Finset.mem_image]
        exact ⟨A, Finset.mem_attach _ _, rfl⟩
      · rw [← hA₀']
        exact fun h ↦ (Finset.mem_erase.mp hAerase).1 (hinj A A₀ h.symm)
    -- The two falling-asleep events at or before the earliest moment are
    -- therefore different from all nine.
    have hnotT : ∀ (p : Fin 5) (k : Fin 2), s p k ≤ S.min' hS_ne → (p, k) ∉ T :=
      fun p k hple hmem ↦ absurd (hT_gt (p, k) hmem) (not_lt.mpr hple)
    -- That makes eleven distinct falling-asleep events, but there are only
    -- ten (five professors, two naps each): contradiction.
    have hcardU : (insert (p₀, k₀) (insert (q₀, l₀) T)).card = 11 := by
      have hn1 : (q₀, l₀) ∉ T := hnotT q₀ l₀ hl₀le
      have hn2 : (p₀, k₀) ∉ insert (q₀, l₀) T := by
        rw [Finset.mem_insert]; push Not
        exact ⟨fun h ↦ hp₀q₀ (Prod.ext_iff.mp h).1, hnotT p₀ k₀ hk₀le⟩
      have h1 := Finset.card_insert_of_notMem hn2
      have h2 := Finset.card_insert_of_notMem hn1
      omega
    have hle := Finset.card_le_card
      (Finset.subset_univ (insert (p₀, k₀) (insert (q₀, l₀) T)))
    rw [hcardU, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_fin] at hle
    omega

end Usa1986P2
