/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import ProblemExtraction

@[expose] public section

problem_file {
  tags := [.Combinatorics]
}

/-!
# International Mathematical Olympiad 2007, Problem 3

In a mathematical competition some competitors are (mutual) friends.
Call a group of competitors a clique if each two of them are friends.
Given that the largest size of a clique is even, prove that the
competitors can be arranged into two rooms such that the largest size
of a clique contained in one room is the same as the largest size of
a clique contained in the other room.
-/

namespace Imo2007P3

/-- The largest size of a clique of the graph `G` all of whose vertices lie in `A`. -/
noncomputable def maxCliqueCard {V : Type*} (G : SimpleGraph V) (A : Finset V) : ℕ :=
  sSup {n : ℕ | ∃ s : Finset V, s ⊆ A ∧ G.IsClique s ∧ s.card = n}

snip begin

section

variable {V : Type*} (G : SimpleGraph V)

lemma bddAbove_cliqueCard {A : Finset V} :
    BddAbove {n : ℕ | ∃ s : Finset V, s ⊆ A ∧ G.IsClique s ∧ s.card = n} :=
  ⟨A.card, fun n hn ↦ by
    obtain ⟨s, hsA, -, rfl⟩ := hn
    exact Finset.card_le_card hsA⟩

lemma nonempty_cliqueCard {A : Finset V} :
    {n : ℕ | ∃ s : Finset V, s ⊆ A ∧ G.IsClique s ∧ s.card = n}.Nonempty :=
  ⟨0, ∅, Finset.empty_subset A, by rw [Finset.coe_empty]; exact Set.pairwise_empty G.Adj,
    Finset.card_empty⟩

lemma card_le_maxCliqueCard {A s : Finset V} (hsA : s ⊆ A) (hsc : G.IsClique s) :
    s.card ≤ maxCliqueCard G A :=
  le_csSup (bddAbove_cliqueCard G) ⟨s, hsA, hsc, rfl⟩

lemma maxCliqueCard_le {A : Finset V} {n : ℕ}
    (h : ∀ s : Finset V, s ⊆ A → G.IsClique s → s.card ≤ n) :
    maxCliqueCard G A ≤ n := by
  apply csSup_le (nonempty_cliqueCard G)
  rintro m ⟨s, hsA, hsc, rfl⟩
  exact h s hsA hsc

lemma maxCliqueCard_le_card {A : Finset V} : maxCliqueCard G A ≤ A.card :=
  maxCliqueCard_le G fun _ hsA _ ↦ Finset.card_le_card hsA

lemma maxCliqueCard_eq_card_of_isClique {A : Finset V} (hA : G.IsClique A) :
    maxCliqueCard G A = A.card :=
  le_antisymm (maxCliqueCard_le_card G) (card_le_maxCliqueCard G (Finset.Subset.refl A) hA)

lemma maxCliqueCard_mono {A B : Finset V} (hAB : A ⊆ B) :
    maxCliqueCard G A ≤ maxCliqueCard G B :=
  maxCliqueCard_le G fun _ hsA hsc ↦ card_le_maxCliqueCard G (hsA.trans hAB) hsc

lemma isClique_of_subset {s t : Finset V} (hst : s ⊆ t) (ht : G.IsClique t) :
    G.IsClique s :=
  ht.subset (Finset.coe_subset.mpr hst)

lemma isClique_union {s t : Finset V} (hs : G.IsClique s) (ht : G.IsClique t)
    (hst : ∀ x ∈ s, ∀ y ∈ t, x ≠ y → G.Adj x y) : G.IsClique (s ∪ t) := by
  intro x hx y hy hxy
  rw [Set.mem_union] at hx hy
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact hs hx hy hxy
  · exact hst x hx y hy hxy
  · exact (hst y hy x hx hxy.symm).symm
  · exact ht hx hy hxy

lemma maxCliqueCard_insert_le [DecidableEq V] {A : Finset V} (x : V) :
    maxCliqueCard G (insert x A) ≤ maxCliqueCard G A + 1 := by
  apply maxCliqueCard_le G
  intro s hsA hsc
  by_cases hx : x ∈ s
  · have h1 : s.erase x ⊆ A := by
      intro y hy
      have hyx : y ≠ x := (Finset.mem_erase.mp hy).1
      have hy2 : y ∈ insert x A := hsA (Finset.mem_of_mem_erase hy)
      rcases Finset.mem_insert.mp hy2 with h | h
      · exact absurd h hyx
      · exact h
    have h2 := card_le_maxCliqueCard G h1 (isClique_of_subset G (Finset.erase_subset x s) hsc)
    have h3 : s.card = (s.erase x).card + 1 := (Finset.card_erase_add_one hx).symm
    omega
  · have h1 : s ⊆ A := by
      intro y hy
      rcases Finset.mem_insert.mp (hsA hy) with h | h
      · exact absurd (h ▸ hy) hx
      · exact h
    exact (card_le_maxCliqueCard G h1 hsc).trans (by omega)

lemma maxCliqueCard_erase_le [DecidableEq V] {A : Finset V} (x : V) :
    maxCliqueCard G A ≤ maxCliqueCard G (A.erase x) + 1 := by
  by_cases hx : x ∈ A
  · have h := maxCliqueCard_insert_le G x (A := A.erase x)
    rwa [Finset.insert_erase hx] at h
  · rw [Finset.erase_eq_of_notMem hx]
    omega

lemma exists_isClique_card_eq {A : Finset V} :
    ∃ s : Finset V, s ⊆ A ∧ G.IsClique s ∧ s.card = maxCliqueCard G A := by
  obtain ⟨s, hsA, hsc, hs⟩ := Nat.sSup_mem (nonempty_cliqueCard G) (bddAbove_cliqueCard G)
  exact ⟨s, hsA, hsc, hs⟩

end

snip end

problem imo2007_p3 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hG : Even (maxCliqueCard G Finset.univ)) :
    ∃ A B : Finset V, Disjoint A B ∧ A ∪ B = Finset.univ ∧
      maxCliqueCard G A = maxCliqueCard G B := by
  obtain ⟨r, hr⟩ := hG
  rw [← Nat.two_mul] at hr
  obtain ⟨K, -, hKc, hKcard⟩ := exists_isClique_card_eq G (A := Finset.univ)
  have hK : K.card = 2 * r := hKcard.trans hr
  -- Step 1: move vertices of the maximal clique `K` into the second room one at a
  -- time, and stop at the first moment the second room is at least as good.
  have hr_mem : ∃ T : Finset V, T ⊆ K ∧ T.card = r ∧
      maxCliqueCard G (K \ T) ≤ maxCliqueCard G (K \ T)ᶜ := by
    obtain ⟨T, hTK, hTcard⟩ := Finset.exists_subset_card_eq (s := K) (n := r) (by omega)
    refine ⟨T, hTK, hTcard, ?_⟩
    have h1 : maxCliqueCard G (K \ T) = (K \ T).card :=
      maxCliqueCard_eq_card_of_isClique G (isClique_of_subset G Finset.sdiff_subset hKc)
    rw [h1, Finset.card_sdiff_of_subset hTK, hTcard, hK]
    have hTsub : T ⊆ (K \ T)ᶜ := by
      intro x hx
      rw [Finset.mem_compl, Finset.mem_sdiff]
      push Not
      exact fun _ ↦ hx
    have hle := card_le_maxCliqueCard G hTsub (isClique_of_subset G hTK hKc)
    omega
  have hex : ∃ j : ℕ, ∃ T : Finset V, T ⊆ K ∧ T.card = j ∧
      maxCliqueCard G (K \ T) ≤ maxCliqueCard G (K \ T)ᶜ := ⟨r, hr_mem⟩
  obtain ⟨T, hTK, hTcard, hTineq⟩ := Nat.find_spec hex
  have htle : Nat.find hex ≤ r := Nat.find_min' hex hr_mem
  have hTcard_le : T.card ≤ r := hTcard ▸ htle
  -- The clique number of the second room overshoots by at most one.
  have hkey : maxCliqueCard G (K \ T)ᶜ ≤ maxCliqueCard G (K \ T) + 1 := by
    rcases eq_or_ne (Nat.find hex) 0 with ht0 | ht0
    · have hTe : T = ∅ := Finset.card_eq_zero.mp (ht0 ▸ hTcard)
      subst hTe
      rw [Finset.sdiff_empty]
      have h1 : maxCliqueCard G K = K.card := maxCliqueCard_eq_card_of_isClique G hKc
      have h2 := maxCliqueCard_mono G (Finset.subset_univ Kᶜ)
      omega
    · obtain ⟨x, hxT⟩ := Finset.card_pos.mp (by omega : 0 < T.card)
      have hT'K : T.erase x ⊆ K := (Finset.erase_subset x T).trans hTK
      have hT'card : (T.erase x).card = Nat.find hex - 1 := by
        rw [Finset.card_erase_of_mem hxT, hTcard]
      have hlt : Nat.find hex - 1 < Nat.find hex := by omega
      have hnot := Nat.find_min hex hlt
      push Not at hnot
      specialize hnot (T.erase x) hT'K hT'card
      have hKT' : K \ T.erase x = insert x (K \ T) := by
        ext y
        simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]
        constructor
        · rintro ⟨hyK, hy⟩
          by_cases hyx : y = x
          · exact Or.inl hyx
          · exact Or.inr ⟨hyK, fun hyT ↦ hy ⟨hyx, hyT⟩⟩
        · rintro (rfl | ⟨hyK, hyT⟩)
          · exact ⟨hTK hxT, fun h ↦ h.1 rfl⟩
          · exact ⟨hyK, fun h ↦ hyT h.2⟩
      rw [hKT', Finset.compl_insert] at hnot
      have hA := maxCliqueCard_insert_le G x (A := K \ T)
      have hB := maxCliqueCard_erase_le G x (A := (K \ T)ᶜ)
      omega
  have hcases : maxCliqueCard G (K \ T)ᶜ = maxCliqueCard G (K \ T) ∨
      maxCliqueCard G (K \ T)ᶜ = maxCliqueCard G (K \ T) + 1 := by omega
  rcases hcases with hEq | hLt
  · -- The two rooms already have equal clique numbers.
    refine ⟨K \ T, (K \ T)ᶜ, ?_, Finset.union_compl _, hEq.symm⟩
    rw [Finset.disjoint_left]
    intro x hx hxc
    exact (Finset.mem_compl.mp hxc) hx
  · -- Step 2: the clique number of the second room is exactly one larger.
    set A := K \ T with hAdef
    have hAK : A ⊆ K := by rw [hAdef]; exact Finset.sdiff_subset
    have hAc : G.IsClique A := isClique_of_subset G hAK hKc
    have hωA : maxCliqueCard G A = A.card := maxCliqueCard_eq_card_of_isClique G hAc
    have hAcard : A.card = 2 * r - T.card := by
      rw [hAdef, Finset.card_sdiff_of_subset hTK, hK]
    rw [hωA] at hLt
    by_cases h2a : ∃ x : V, x ∈ Aᶜ ∩ K ∧ maxCliqueCard G (Aᶜ.erase x) = A.card + 1
    · -- A vertex of `K` can be moved back to the first room without loss.
      obtain ⟨x, hxBK, hxB⟩ := h2a
      rw [Finset.mem_inter] at hxBK
      have hxA : x ∉ A := Finset.mem_compl.mp hxBK.1
      refine ⟨insert x A, Aᶜ.erase x, ?_, ?_, ?_⟩
      · rw [Finset.disjoint_left]
        intro y hy hye
        rw [Finset.mem_erase] at hye
        rcases Finset.mem_insert.mp hy with rfl | hyA
        · exact hye.1 rfl
        · exact (Finset.mem_compl.mp hye.2) hyA
      · ext y
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_erase, Finset.mem_univ]
        refine iff_true_intro ?_
        by_cases hyA : y ∈ A
        · exact Or.inl (Or.inr hyA)
        · by_cases hyx : y = x
          · exact Or.inl (Or.inl hyx)
          · exact Or.inr ⟨hyx, Finset.mem_compl.mpr hyA⟩
      · have h1 : G.IsClique ↑(insert x A) :=
          isClique_of_subset G (Finset.insert_subset hxBK.2 hAK) hKc
        rw [maxCliqueCard_eq_card_of_isClique G h1, Finset.card_insert_of_notMem hxA]
        exact hxB.symm
    · -- Step 3: every `(A.card + 1)`-clique of the second room uses all of `Aᶜ ∩ K`;
      -- destroy them all by moving a minimal set of vertices outside `K` back.
      push Not at h2a
      have h2b : ∀ x ∈ Aᶜ ∩ K, maxCliqueCard G (Aᶜ.erase x) ≤ A.card := by
        intro x hx
        have h1 := maxCliqueCard_mono G (Finset.erase_subset x Aᶜ)
        have h2 := h2a x hx
        omega
      classical
      set 𝒞 := Aᶜ.powerset.filter (fun C : Finset V ↦ G.IsClique C ∧ C.card = A.card + 1)
        with h𝒞def
      have h𝒞sub : ∀ C ∈ 𝒞, C ⊆ Aᶜ := by
        intro C hC
        rw [h𝒞def, Finset.mem_filter] at hC
        exact Finset.mem_powerset.mp hC.1
      have h𝒞c : ∀ C ∈ 𝒞, G.IsClique C := by
        intro C hC
        rw [h𝒞def, Finset.mem_filter] at hC
        exact hC.2.1
      have h𝒞card : ∀ C ∈ 𝒞, C.card = A.card + 1 := by
        intro C hC
        rw [h𝒞def, Finset.mem_filter] at hC
        exact hC.2.2
      have hBK : Aᶜ ∩ K = T := by
        ext y
        simp only [Finset.mem_inter, Finset.mem_compl, hAdef, Finset.mem_sdiff]
        constructor
        · rintro ⟨hy1, hy2⟩
          by_contra hyT
          exact hy1 ⟨hy2, hyT⟩
        · intro hyT
          exact ⟨fun h ↦ h.2 hyT, hTK hyT⟩
      -- Every clique in `𝒞` has a vertex outside `K`, since `A.card + 1 > T.card`.
      have hgreen : ∀ C ∈ 𝒞, (C \ K).Nonempty := by
        intro C hC
        have hCB := h𝒞sub C hC
        have hCcard := h𝒞card C hC
        by_contra hne
        rw [Finset.not_nonempty_iff_eq_empty] at hne
        have hCK : C ⊆ K := by
          intro x hx
          by_contra hxK
          exact Finset.notMem_empty x (hne ▸ Finset.mem_sdiff.mpr ⟨hx, hxK⟩)
        have h2 := Finset.card_le_card (Finset.subset_inter hCB hCK)
        rw [hBK, hCcard] at h2
        omega
      -- A minimal hitting set of `𝒞` consisting of vertices outside `K`.
      set HS := (Aᶜ \ K).powerset.filter
        (fun Blue : Finset V ↦ ∀ C ∈ 𝒞, (C ∩ Blue).Nonempty) with hHSdef
      have hHSne : HS.Nonempty := by
        refine ⟨Aᶜ \ K, ?_⟩
        rw [hHSdef, Finset.mem_filter, Finset.mem_powerset]
        refine ⟨Finset.Subset.refl _, fun C hC ↦ ?_⟩
        obtain ⟨x, hx⟩ := hgreen C hC
        rw [Finset.mem_sdiff] at hx
        exact ⟨x, Finset.mem_inter.mpr ⟨hx.1,
          Finset.mem_sdiff.mpr ⟨h𝒞sub C hC hx.1, hx.2⟩⟩⟩
      obtain ⟨Blue, hBlue, hBlueMin⟩ := Finset.exists_min_image HS Finset.card hHSne
      rw [hHSdef, Finset.mem_filter, Finset.mem_powerset] at hBlue
      obtain ⟨hBlueSub, hBlueHit⟩ := hBlue
      have hBlueB : Blue ⊆ Aᶜ := hBlueSub.trans Finset.sdiff_subset
      -- Minimality: removing any vertex of `Blue` leaves some clique of `𝒞` unhit.
      have hBlueMin' : ∀ b ∈ Blue, ∃ C ∈ 𝒞, C ∩ (Blue.erase b) = ∅ := by
        intro b hb
        by_contra hcon
        push Not at hcon
        have hmem : Blue.erase b ∈ HS := by
          rw [hHSdef, Finset.mem_filter, Finset.mem_powerset]
          refine ⟨(Finset.erase_subset b Blue).trans hBlueSub, fun C hC ↦ ?_⟩
          exact hcon C hC
        have hle := hBlueMin (Blue.erase b) hmem
        have hpos : 0 < Blue.card := Finset.card_pos.mpr ⟨b, hb⟩
        rw [Finset.card_erase_of_mem hb] at hle
        omega
      -- In particular `Blue` is nonempty, since `𝒞` is nonempty.
      have hBlueNe : Blue.Nonempty := by
        obtain ⟨C₀, hC₀sub, hC₀c, hC₀card⟩ := exists_isClique_card_eq G (A := Aᶜ)
        have hC₀mem : C₀ ∈ 𝒞 := by
          rw [h𝒞def, Finset.mem_filter, Finset.mem_powerset]
          exact ⟨hC₀sub, hC₀c, hC₀card.trans hLt⟩
        obtain ⟨x, hx⟩ := hBlueHit C₀ hC₀mem
        exact ⟨x, (Finset.mem_inter.mp hx).2⟩
      -- Each `b ∈ Blue` lies in a clique of `𝒞`, which must contain `Aᶜ ∩ K`.
      have hCb : ∀ b ∈ Blue, ∃ C ∈ 𝒞, b ∈ C ∧ Aᶜ ∩ K ⊆ C := by
        intro b hb
        obtain ⟨C, hC, hCemp⟩ := hBlueMin' b hb
        refine ⟨C, hC, ?_, ?_⟩
        · obtain ⟨y, hy⟩ := hBlueHit C hC
          rw [Finset.mem_inter] at hy
          by_contra hbC
          have hyx : y ≠ b := fun h ↦ hbC (h ▸ hy.1)
          have hye : y ∈ C ∩ Blue.erase b :=
            Finset.mem_inter.mpr ⟨hy.1, Finset.mem_erase.mpr ⟨hyx, hy.2⟩⟩
          rw [hCemp] at hye
          exact Finset.notMem_empty _ hye
        · intro y hy
          by_contra hyC
          have h1 : C ⊆ Aᶜ.erase y := by
            intro z hz
            rw [Finset.mem_erase]
            exact ⟨fun h ↦ hyC (h ▸ hz), h𝒞sub C hC hz⟩
          have h2 := card_le_maxCliqueCard G h1 (h𝒞c C hC)
          have h3 := h2b y hy
          have h4 := h𝒞card C hC
          omega
      -- Hence every blue vertex is adjacent to all of `Aᶜ ∩ K`.
      have hBlueAdj : ∀ b ∈ Blue, ∀ y ∈ Aᶜ ∩ K, b ≠ y → G.Adj b y := by
        intro b hb y hy hby
        obtain ⟨C, hC, hbC, hsub⟩ := hCb b hb
        exact h𝒞c C hC hbC (hsub hy) hby
      -- The first room `A ∪ Blue` still has clique number `A.card`.
      have hω1 : maxCliqueCard G (A ∪ Blue) = A.card := by
        apply le_antisymm
        · apply maxCliqueCard_le G
          intro D hD hDc
          by_contra hDcard
          rw [not_le] at hDcard
          obtain ⟨D', hD'D, hD'card⟩ :=
            Finset.exists_subset_card_eq (n := A.card + 1) (s := D) (by omega)
          have hD'c : G.IsClique D' := isClique_of_subset G hD'D hDc
          have hD'AB : D' ⊆ A ∪ Blue := hD'D.trans hD
          -- Otherwise `D' ∪ (Aᶜ ∩ K)` would be a clique of size `2 * r + 1`.
          have hK' : G.IsClique ↑(Aᶜ ∩ K) :=
            isClique_of_subset G Finset.inter_subset_right hKc
          have hbig : G.IsClique ↑(D' ∪ (Aᶜ ∩ K)) := by
            rw [Finset.coe_union]
            apply isClique_union G hD'c hK'
            intro x hx y hy hxy
            rcases Finset.mem_union.mp (hD'AB hx) with hxA | hxB
            · exact hKc (hAK hxA) (Finset.mem_inter.mp hy).2 hxy
            · exact hBlueAdj x hxB y hy hxy
          have hdisj : Disjoint D' (Aᶜ ∩ K) := by
            rw [Finset.disjoint_left]
            intro x hx hx2
            rcases Finset.mem_union.mp (hD'AB hx) with hxA | hxB
            · exact (Finset.mem_compl.mp (Finset.mem_inter.mp hx2).1) hxA
            · exact (Finset.mem_sdiff.mp (hBlueSub hxB)).2 (Finset.mem_inter.mp hx2).2
          have hle := card_le_maxCliqueCard G (Finset.subset_univ (D' ∪ (Aᶜ ∩ K))) hbig
          rw [Finset.card_union_of_disjoint hdisj, hD'card, hBK] at hle
          omega
        · rw [← hωA]
          exact maxCliqueCard_mono G Finset.subset_union_left
      -- The second room `Aᶜ \ Blue` has clique number exactly `A.card`.
      have hω2 : maxCliqueCard G (Aᶜ \ Blue) = A.card := by
        apply le_antisymm
        · apply maxCliqueCard_le G
          intro D hD hDc
          by_contra hDcard
          rw [not_le] at hDcard
          obtain ⟨D', hD'D, hD'card⟩ :=
            Finset.exists_subset_card_eq (n := A.card + 1) (s := D) (by omega)
          have hD'c : G.IsClique D' := isClique_of_subset G hD'D hDc
          have hD'mem : D' ∈ 𝒞 := by
            rw [h𝒞def, Finset.mem_filter, Finset.mem_powerset]
            exact ⟨(hD'D.trans hD).trans Finset.sdiff_subset, hD'c, hD'card⟩
          obtain ⟨x, hx⟩ := hBlueHit D' hD'mem
          rw [Finset.mem_inter] at hx
          have hx3 : x ∈ Aᶜ \ Blue := hD (hD'D hx.1)
          exact (Finset.mem_sdiff.mp hx3).2 hx.2
        · obtain ⟨b, hbB⟩ := hBlueNe
          obtain ⟨C, hC, hCemp⟩ := hBlueMin' b hbB
          have hCsub : C ⊆ insert b (Aᶜ \ Blue) := by
            intro x hx
            rw [Finset.mem_insert]
            by_cases hxb : x = b
            · exact Or.inl hxb
            · have hxB : x ∉ Blue := fun hB ↦
                Finset.notMem_empty x (hCemp ▸ Finset.mem_inter.mpr
                  ⟨hx, Finset.mem_erase.mpr ⟨hxb, hB⟩⟩)
              exact Or.inr (Finset.mem_sdiff.mpr ⟨h𝒞sub C hC hx, hxB⟩)
          have h1 := card_le_maxCliqueCard G hCsub (h𝒞c C hC)
          have h2 := maxCliqueCard_insert_le G b (A := Aᶜ \ Blue)
          have h3 := h𝒞card C hC
          omega
      exact ⟨A ∪ Blue, Aᶜ \ Blue, by
        rw [Finset.disjoint_left]
        intro x hx hx2
        rcases Finset.mem_union.mp hx with hxA | hxB
        · exact (Finset.mem_compl.mp (Finset.mem_sdiff.mp hx2).1) hxA
        · exact (Finset.mem_sdiff.mp hx2).2 hxB, by
        have h1 : Blue ∪ Aᶜ \ Blue = Aᶜ := Finset.union_sdiff_of_subset hBlueB
        calc A ∪ Blue ∪ (Aᶜ \ Blue)
            = A ∪ (Blue ∪ Aᶜ \ Blue) := by rw [Finset.union_assoc]
          _ = A ∪ Aᶜ := by rw [h1]
          _ = Finset.univ := Finset.union_compl A, by
        rw [hω1, hω2]⟩

end Imo2007P3
