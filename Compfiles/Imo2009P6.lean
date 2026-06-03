/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic
import Mathlib.Data.Fin.Tuple.Sort

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Olympiad 2009, Problem 6

Let a₁, a₂, ..., aₙ be distinct positive integers and let M
be a set of n - 1 positive integers not containing
s = a₁ + a₂ + ... + aₙ. A grasshopper is to jump along the
real axis, starting at the point 0 and making n jumps to
the right with lengths a₁, a₂, ..., aₙ in some order. Prove
that the order can be chosen in such a way that the
grasshopper never lands on any point in M.
-/

namespace Imo2009P6

snip begin

lemma lemma1 (n : ℕ) (a : Fin n → ℤ) :
    ∃ p : Equiv.Perm (Fin n),
        ∀ i j, i ≤ j → a (p i) ≤ a (p j) :=
  ⟨Tuple.sort a, fun _ _ hij ↦ Tuple.monotone_sort a hij⟩

lemma lemma2 (n : ℕ) (a : Fin n → ℤ)
    (ainj : a.Injective) :
    ∃ p : Equiv.Perm (Fin n),
        ∀ i j, i < j → (a ∘ p) i < (a ∘ p) j := by
  obtain ⟨p, hp⟩ := lemma1 n a
  refine ⟨p, ?_⟩
  intro i j hij
  have h0 := ne_of_lt hij
  have h2 := hp i j (le_of_lt hij)
  have h3 : p i ≠ p j := by
    intro hh; rw [EmbeddingLike.apply_eq_iff_eq] at hh; exact h0 hh
  exact lt_of_le_of_ne h2 fun a ↦ h3 (ainj a)

def embedFinLE {m n : ℕ} (hmn : m ≤ n) : Fin m ↪ Fin n :=
  ⟨fun x ↦ ⟨x, by lia⟩,
   by intro x y hxy; dsimp at hxy; apply_fun (·.val) at hxy
      exact Fin.eq_of_val_eq hxy⟩


noncomputable abbrev extendPerm {m n : ℕ} (f : Equiv.Perm (Fin m)) (h : m ≤ n) :
    Equiv.Perm (Fin n) :=
  let f' : Fin n → Fin n :=
     fun (x : Fin n) ↦ if h1 : x < m then ⟨f ⟨x, h1⟩, by lia⟩ else x
  have hf' : f'.Injective := by
    intro x y hxy
    simp only [f'] at hxy
    split_ifs at hxy with h1 h2 h3
    · simp only [Fin.mk.injEq] at hxy
      have h1 := Fin.eq_of_val_eq hxy
      aesop
    · have : f' y = y := by
        dsimp [f']; simp only [dite_eq_right_iff]
        intro hh
        exact (h2 hh).elim
      aesop
    · aesop
    · aesop
  Equiv.ofBijective f' (Finite.injective_iff_bijective.mp hf')

lemma extendPerm_apply_of_lt {m n : ℕ} (f : Equiv.Perm (Fin m)) (h : m ≤ n)
    (x : Fin n) (hx : (x : ℕ) < m) :
    extendPerm f h x = ⟨f ⟨x, hx⟩, by omega⟩ := by
  simp [extendPerm, hx]

lemma extendPerm_apply_of_not_lt {m n : ℕ} (f : Equiv.Perm (Fin m)) (h : m ≤ n)
    (x : Fin n) (hx : ¬ (x : ℕ) < m) :
    extendPerm f h x = x := by
  simp [extendPerm, hx]

theorem imo2009_p6_aux1 (n : ℕ) (hn : 0 < n)
    (a : Fin n → ℤ)
    (ainj : a.Injective)
    (apos : ∀ i, 0 < a i)
    (asorted : ∀ i j, i < j → a i < a j)
    (M : Finset ℤ)
    (Mpos : ∀ m ∈ M, 0 < m)
    (Mcard : M.card ≤ n - 1)
    (hM : ∑ i, a i ∉ M)
    : ∃ p : Equiv.Perm (Fin n),
          ∀ i : Fin n, ∑ j ∈ Finset.filter (· ≤ i) Finset.univ, a (p j) ∉ M := by
  revert a M hn
  induction' n using Nat.strongRecOn with n ih
  intro hn a ainj apos asorted M Mpos Mcard
  let x := ∑ i ∈ Finset.filter (·.val < n-1) Finset.univ, a i
  -- four cases: split on whether x ∈ M and whether
  -- there is any y > x such that y ∈ M.
  by_cases h1 : x ∈ M <;> by_cases h2 : ∃ y, x < y ∧ y ∈ M
  · sorry
  · -- `x` is the rightmost mine.  Solve the first `n - 1` jumps after erasing
    -- `x`, then swap the last small jump with the largest jump.
    intro hM
    let n' := n - 1
    by_cases hn' : n' = 0
    · have hx0 : x = 0 := by
        have hn1 : n = 1 := by omega
        subst hn1
        change (∑ i ∈ Finset.filter (fun i : Fin 1 => (i : ℕ) < 0) Finset.univ, a i) = 0
        simp
      have := Mpos x h1
      omega
    · have hn'pos : 0 < n' := Nat.pos_of_ne_zero hn'
      let a' := fun i : Fin n' ↦ a ⟨i, by omega⟩
      have ainj' : a'.Injective := by
        intro i j hij
        have h11 : a ⟨i, by omega⟩ = a ⟨j, by omega⟩ := by
          simpa [a'] using hij
        have h12 := congrArg Fin.val (@ainj ⟨i, by omega⟩ ⟨j, by omega⟩ h11)
        dsimp at h12
        exact Fin.eq_of_val_eq h12
      have apos' : ∀ (i : Fin n'), 0 < a' i := fun i ↦ apos ⟨i.val, by omega⟩
      have asorted' : ∀ (i j : Fin n'), i < j → a' i < a' j := by
        intro i j hij
        exact asorted ⟨i, by omega⟩ ⟨j, by omega⟩ hij
      let M' := M.erase x
      have Mpos' : ∀ m ∈ M', 0 < m := by
        intro m hm
        exact Mpos m (Finset.mem_of_mem_erase hm)
      have Mcard' : M'.card ≤ n' - 1 := by
        have hxcard : M'.card + 1 = M.card := by
          exact Finset.card_erase_add_one h1
        omega
      have hsumx : ∑ i : Fin n', a' i = x := by
        let f : Fin n' ↪ Fin n := embedFinLE (Nat.sub_le _ _)
        have h40 : (Finset.univ (α := Fin n')).map f =
             Finset.filter (·.val < n - 1) Finset.univ := by
          ext z
          rw [Finset.mem_map, Finset.mem_filter]
          constructor
          · rintro ⟨y, hy1, hy2⟩
            simp only [Finset.mem_univ, true_and]
            rw [←hy2]
            exact y.2
          · rintro ⟨_, hz⟩
            use ⟨z.val, by omega⟩
            simp [f, embedFinLE]
        unfold x
        rw [← h40, Finset.sum_map]
        congr
      have hM' : ∑ i : Fin n', a' i ∉ M' := by
        rw [hsumx]
        exact Finset.notMem_erase x M
      obtain ⟨p', hp'⟩ := ih n' (by omega) hn'pos a' ainj' apos' asorted' M' Mpos' Mcard' hM'
      let p0 : Equiv.Perm (Fin n) := extendPerm p' (Nat.sub_le n 1)
      let posSmall : Fin n := ⟨n' - 1, by omega⟩
      let lastFull : Fin n := ⟨n - 1, by omega⟩
      let p : Equiv.Perm (Fin n) := (Equiv.swap posSmall lastFull).trans p0
      refine ⟨p, ?_⟩
      intro i
      by_cases hi_last : i = lastFull
      · subst hi_last
        have hfilter : Finset.filter (fun x ↦ x ≤ lastFull) Finset.univ =
            Finset.univ (α := Fin n) := by
          ext z
          rw [Finset.mem_filter]
          exact ⟨fun hz ↦ hz.1, fun _ ↦ ⟨Finset.mem_univ _, by
            show z.val ≤ lastFull.val
            dsimp [lastFull]
            omega⟩⟩
        rw [hfilter]
        have pb : p.toFun.Bijective := EquivLike.bijective p
        have hsum : (∑ j : Fin n, a (p j)) = ∑ j : Fin n, a j := by
          simpa using Function.Bijective.sum_comp pb (fun j ↦ a j)
        rw [hsum]
        exact hM
      · by_cases hi_before : i.val < n' - 1
        · let i' : Fin n' := ⟨i.val, by omega⟩
          have hprefix :
              ∑ j ∈ Finset.filter (· ≤ i) Finset.univ, a (p j) =
                ∑ j ∈ Finset.filter (· ≤ i') Finset.univ, a' (p' j) := by
            have hmap : (Finset.univ.filter (· ≤ i')).map (embedFinLE (Nat.sub_le n 1)) =
                Finset.univ.filter (· ≤ i) := by
              ext z
              rw [Finset.mem_map, Finset.mem_filter]
              constructor
              · rintro ⟨y, hy1, hy2⟩
                simp only [Finset.mem_univ, true_and]
                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy1
                simp only [embedFinLE] at hy2
                rw [← hy2]
                exact hy1
              · rintro ⟨hz1, hz2⟩
                use ⟨z, by omega⟩
                simp only [Finset.mem_filter, embedFinLE]
                dsimp
                simp only [eq_self, and_true, Finset.mem_univ, true_and]
                exact hz2
            rw [← hmap, Finset.sum_map]
            apply Finset.sum_congr rfl
            intro j hj
            have hjle : (j : ℕ) ≤ i.val := by
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
              exact hj
            have hne_pos : (embedFinLE (Nat.sub_le n 1) j : Fin n) ≠ posSmall := by
              intro hEq
              have hval := congrArg Fin.val hEq
              dsimp [embedFinLE, posSmall, n'] at hval
              omega
            have hne_last : (embedFinLE (Nat.sub_le n 1) j : Fin n) ≠ lastFull := by
              intro hEq
              have hval := congrArg Fin.val hEq
              dsimp [embedFinLE, lastFull, n'] at hval
              omega
            change a (p0 ((Equiv.swap posSmall lastFull) (embedFinLE (Nat.sub_le n 1) j))) =
              a' (p' j)
            rw [Equiv.swap_apply_of_ne_of_ne hne_pos hne_last]
            have hlt_small : ((embedFinLE (Nat.sub_le n 1) j : Fin n) : ℕ) < n' := by
              dsimp [embedFinLE, n']
              omega
            rw [extendPerm_apply_of_lt p' (Nat.sub_le n 1) _ hlt_small]
            simp [a', embedFinLE]
          have hnot_erase : ∑ j ∈ Finset.filter (· ≤ i) Finset.univ, a (p j) ∉ M' := by
            simpa [hprefix]
              using hp' i'
          have hltx : ∑ j ∈ Finset.filter (· ≤ i) Finset.univ, a (p j) < x := by
            rw [hprefix]
            let k : Fin n' := ⟨i.val + 1, by omega⟩
            let S : Finset (Fin n') := Finset.filter (· ≤ i') Finset.univ
            have hknot : k ∉ S := by
              simp [S, k, i']
            have hsubset : insert k S ⊆ (Finset.univ : Finset (Fin n')) := by
              intro z hz
              simp
            have hle : ∑ j ∈ insert k S, a' (p' j) ≤ ∑ j : Fin n', a' (p' j) := by
              exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
                intro z hz1 hz2
                exact le_of_lt (apos' (p' z)))
            have hsum_perm : (∑ j : Fin n', a' (p' j)) = ∑ j : Fin n', a' j := by
              have pb' : p'.toFun.Bijective := EquivLike.bijective p'
              simpa using Function.Bijective.sum_comp pb' (fun j ↦ a' j)
            have hinsert : ∑ j ∈ insert k S, a' (p' j) = a' (p' k) + ∑ j ∈ S, a' (p' j) := by
              rw [Finset.sum_insert hknot]
            have hposk : 0 < a' (p' k) := apos' (p' k)
            rw [hinsert, hsum_perm, hsumx] at hle
            change ∑ j ∈ S, a' (p' j) < x
            omega
          intro hmem
          have heq : ∑ j ∈ Finset.filter (· ≤ i) Finset.univ, a (p j) = x :=
            Finset.eq_of_mem_of_notMem_erase hmem hnot_erase
          omega
        · have hi_pos : i = posSmall := by
            apply Fin.ext
            have hi_ne_last : i.val ≠ n - 1 := by
              intro hval
              apply hi_last
              apply Fin.ext
              simpa [lastFull] using hval
            dsimp [posSmall, n']
            omega
          subst hi_pos
          let lastSmall' : Fin n' := ⟨n' - 1, by omega⟩
          let P : Finset (Fin n) := Finset.filter (· ≤ posSmall) Finset.univ
          let Sprev : Finset (Fin n') := Finset.filter (· < lastSmall') Finset.univ
          have hPpos : posSmall ∈ P := by simp [P]
          have hp_pos : p posSmall = lastFull := by
            have hnotlt : ¬ ((lastFull : Fin n) : ℕ) < n' := by
              dsimp [lastFull, n']
              omega
            change p0 ((Equiv.swap posSmall lastFull) posSmall) = lastFull
            rw [Equiv.swap_apply_left]
            exact extendPerm_apply_of_not_lt p' (Nat.sub_le n 1) lastFull hnotlt
          have hmap_prev : Sprev.map (embedFinLE (Nat.sub_le n 1)) = P.erase posSmall := by
            ext z
            rw [Finset.mem_map, Finset.mem_erase]
            constructor
            · rintro ⟨j, hjS, hjz⟩
              have hjlt : j < lastSmall' := by simpa [Sprev] using hjS
              constructor
              · intro hzpos
                have hval := congrArg Fin.val (hjz.trans hzpos)
                have hjlt_val : j.val < n' - 1 := by
                  change j.val < lastSmall'.val at hjlt
                  dsimp [lastSmall'] at hjlt
                  exact hjlt
                dsimp [embedFinLE, posSmall, n'] at hval
                omega
              · rw [← hjz]
                simp only [P, Finset.mem_filter, Finset.mem_univ, true_and]
                have hjlt_val : j.val < n' - 1 := by
                  change j.val < lastSmall'.val at hjlt
                  dsimp [lastSmall'] at hjlt
                  exact hjlt
                change j.val ≤ n' - 1
                omega
            · rintro ⟨hz_ne, hzP⟩
              simp only [P, Finset.mem_filter, Finset.mem_univ, true_and] at hzP
              have hzle : z.val ≤ n' - 1 := by
                change z.val ≤ posSmall.val at hzP
                dsimp [posSmall, n'] at hzP
                exact hzP
              use ⟨z.val, by omega⟩
              constructor
              · simp only [Sprev, Finset.mem_filter, Finset.mem_univ, true_and]
                have hz_ne_val : z.val ≠ n' - 1 := by
                  intro hzv
                  apply hz_ne
                  apply Fin.ext
                  simpa [posSmall] using hzv
                change z.val < n' - 1
                omega
              · apply Fin.ext
                rfl
          have hprefix_decomp :
              ∑ j ∈ Finset.filter (· ≤ posSmall) Finset.univ, a (p j) =
                a lastFull + ∑ j ∈ Sprev, a' (p' j) := by
            change ∑ j ∈ P, a (p j) = a lastFull + ∑ j ∈ Sprev, a' (p' j)
            rw [← Finset.add_sum_erase P (fun j => a (p j)) hPpos]
            rw [hp_pos]
            congr 1
            rw [← hmap_prev, Finset.sum_map]
            apply Finset.sum_congr rfl
            intro j hj
            have hjlt : (j : ℕ) < n' - 1 := by
              simp only [Sprev, Finset.mem_filter, Finset.mem_univ, true_and] at hj
              dsimp [lastSmall', n'] at hj
              exact hj
            have hne_pos : (embedFinLE (Nat.sub_le n 1) j : Fin n) ≠ posSmall := by
              intro hEq
              have hval := congrArg Fin.val hEq
              dsimp [embedFinLE, posSmall, n'] at hval
              omega
            have hne_last : (embedFinLE (Nat.sub_le n 1) j : Fin n) ≠ lastFull := by
              intro hEq
              have hval := congrArg Fin.val hEq
              dsimp [embedFinLE, lastFull, n'] at hval
              omega
            change a (p0 ((Equiv.swap posSmall lastFull) (embedFinLE (Nat.sub_le n 1) j))) =
              a' (p' j)
            rw [Equiv.swap_apply_of_ne_of_ne hne_pos hne_last]
            have hlt_small : ((embedFinLE (Nat.sub_le n 1) j : Fin n) : ℕ) < n' := by
              dsimp [embedFinLE, n']
              omega
            rw [extendPerm_apply_of_lt p' (Nat.sub_le n 1) _ hlt_small]
            simp [a', embedFinLE]
          have hsmall_decomp :
              x = ∑ j ∈ Sprev, a' (p' j) + a' (p' lastSmall') := by
            have htotal_perm : (∑ j : Fin n', a' (p' j)) = x := by
              have pb' : p'.toFun.Bijective := EquivLike.bijective p'
              have hsum : (∑ j : Fin n', a' (p' j)) = ∑ j : Fin n', a' j := by
                simpa using Function.Bijective.sum_comp pb' (fun j ↦ a' j)
              rw [hsum, hsumx]
            have herase : (Finset.univ.erase lastSmall') = Sprev := by
              ext z
              rw [Finset.mem_erase]
              simp only [Sprev, Finset.mem_filter, Finset.mem_univ, true_and]
              constructor
              · rintro ⟨hz_ne, -⟩
                have hz_ne_val : z.val ≠ n' - 1 := by
                  intro hzv
                  apply hz_ne
                  apply Fin.ext
                  simpa [lastSmall'] using hzv
                dsimp [lastSmall']
                omega
              · intro hzlt
                constructor
                · intro hz_eq
                  have hval := congrArg Fin.val hz_eq
                  dsimp [lastSmall'] at hval hzlt
                  omega
                · simp
            have hsplit := Finset.sum_erase_add (s := (Finset.univ : Finset (Fin n')))
              (a := lastSmall') (f := fun j => a' (p' j)) (by simp)
            rw [herase] at hsplit
            omega
          have hbig : a' (p' lastSmall') < a lastFull := by
            let idxFull : Fin n := ⟨((p' lastSmall' : Fin n') : ℕ), by
              have hlt := (p' lastSmall').isLt
              dsimp [n'] at hlt ⊢
              omega⟩
            have hlt_fin : idxFull < lastFull := by
              change ((p' lastSmall' : Fin n') : ℕ) < n - 1
              have hlt := (p' lastSmall').isLt
              dsimp [n'] at hlt
              omega
            simpa [a', idxFull] using asorted idxFull lastFull hlt_fin
          have hgtx : x < ∑ j ∈ Finset.filter (· ≤ posSmall) Finset.univ, a (p j) := by
            rw [hprefix_decomp, hsmall_decomp]
            omega
          intro hmem
          exact h2 ⟨_, hgtx, hmem⟩
  · -- x has no mine, and there is a mine past x.
    -- Then there are at most n − 2 mines in [0, x] and
    -- so we use induction to reach x, then leap from x to s and win
    obtain ⟨y, hy1, hy2⟩ := h2
    let M' := M.filter (fun z ↦ z ≤ x)
    have hyM' : y ∉ M' := by
      intro hy
      rw [Finset.mem_filter] at hy
      lia
    have h3 : M'.card ≤ n - 2 := by
      let M'' := Finset.cons y M' hyM'
      have h4 : M'' ⊆ M := by
        intro a ha
        rw [Finset.mem_cons] at ha
        obtain rfl | ha := ha
        · exact hy2
        · exact Finset.mem_of_mem_filter a ha
      have h4' : M''.card ≤ M.card := Finset.card_le_card h4
      have h5 : M''.card = M'.card + 1 := Finset.card_cons hyM'
      have h6 : M'.card + 1 ≤ M.card := by lia
      lia
    intro hM
    obtain h7 | h7 := Nat.eq_zero_or_pos M'.card
    · refine ⟨Equiv.refl _, ?_⟩
      intro i
      obtain hi1 | hi2 := Classical.em (i.val < n-1)
      · let z := ∑ j ∈ Finset.filter (· ≤ i) Finset.univ, a j
        have h9 : z ≤ x := by
          have h49 : ∀ i, 0 ≤ a i := by intro i; exact le_of_lt (apos i)
          have h50 : Finset.filter (fun x ↦ x ≤ i) Finset.univ ⊆
                     Finset.filter (fun x ↦ ↑x < n - 1) Finset.univ := by
            intro x hx
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
            lia
          exact Finset.sum_le_sum_of_subset_of_nonneg h50 fun i_1 a a ↦ h49 i_1
        intro h10
        change z ∈ M at h10
        have h11 : z ∈ M' := by
          rw [Finset.mem_filter]
          exact ⟨h10, h9⟩
        rw [Finset.card_eq_zero] at h7
        have h12 := Finset.notMem_empty z
        rw [h7] at h11
        exact h12 h11
      · have h9 : i.val + 1 = n := by lia
        have h10 : Finset.filter (fun x ↦ x ≤ i) Finset.univ =
                    Finset.univ (α := Fin n) := by
          ext x
          rw [Finset.mem_filter]
          suffices x ≤ i from and_iff_left_of_imp fun a ↦ this
          lia
        rw [h10]
        exact hM
    let n' := n - 1
    let a' := fun i : Fin n' ↦ a ⟨i, by lia⟩
    have ainj' : a'.Injective := by
      intro i j hij
      have h11 : a ⟨i, by lia⟩ = a ⟨j, by lia⟩ := by
        simp only [a'] at hij
        exact hij
      have h12 := congrArg Fin.val (@ainj ⟨i, by lia⟩ ⟨j, by lia⟩ h11)
      dsimp at h12
      exact Fin.eq_of_val_eq h12
    have apos' : ∀ (i : Fin n'), 0 < a' i :=
      fun i ↦ apos ⟨i.val, by lia⟩
    have asorted' : ∀ (i j : Fin n'), i < j → a' i < a' j := by
      intro i j hij
      exact asorted ⟨i, by lia⟩ ⟨j, by lia⟩ hij
    have Mpos' : (∀ m ∈ M', 0 < m) := by
      intro m hm
      rw [Finset.mem_filter] at hm
      exact Mpos m hm.1
    have hM' : ∑ i : Fin n', a' i ∉ M' := by
      have h14 : ∑ i : Fin n', a' i = x := by
        let f : Fin n' ↪ Fin n := embedFinLE (Nat.sub_le _ _)
        have h40 : (Finset.univ (α := Fin n')).map f =
             Finset.filter (·.val < n - 1) Finset.univ := by
          ext x
          rw [Finset.mem_map, Finset.mem_filter]
          constructor
          · rintro ⟨y, hy1, hy2⟩
            simp only [Finset.mem_univ, true_and]
            rw [←hy2]
            obtain ⟨y', hy'⟩ := y
            exact hy'
          · rintro ⟨_, h41⟩
            use ⟨x.val, by lia⟩
            simp [f, embedFinLE]
        unfold x
        rw [←h40, Finset.sum_map]
        congr
      rw [←h14] at h1
      rw [Finset.mem_filter]
      push Not
      intro h15
      exact (h1 h15).elim
    obtain ⟨p', hp⟩ :=
      ih n' (by lia) (by lia) a' ainj' apos' asorted' M' Mpos' (by lia) hM'
    clear ih
    let p : Equiv.Perm (Fin n) := extendPerm p' (Nat.sub_le n 1)
    refine ⟨p, ?_⟩
    intro i
    by_cases h30 : i.val < n'
    · let i' : Fin n' := ⟨i.val, h30⟩
      have h31 := hp i'
      rw [Finset.mem_filter] at h31
      have h35 : n' ≤ n := Nat.sub_le n 1
      have h33 : ∑ j ∈ Finset.filter (· ≤ i') Finset.univ, a' (p' j) =
                 ∑ j ∈ Finset.filter (· ≤ i) Finset.univ, a (p j) := by
        have h36 : (Finset.univ.filter (· ≤ i')).map (embedFinLE h35) =
                     Finset.univ.filter (· ≤ i) := by
          ext x
          rw [Finset.mem_map, Finset.mem_filter]
          constructor
          · rintro ⟨y, hy1, hy2⟩
            simp only [Finset.mem_univ, true_and]
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy1
            simp only [embedFinLE] at hy2
            rw [←hy2]
            dsimp
            exact hy1
          · rintro ⟨hx1, hx2⟩
            use ⟨x, by lia⟩
            simp only [Finset.mem_filter, embedFinLE]
            dsimp
            simp only [eq_self, and_true, Finset.mem_univ, true_and]
            exact hx2
        rw [← h36]
        simp [embedFinLE, a', p]
      rw [h33] at h31
      have h34 : ∑ j ∈ Finset.filter (· ≤ i) Finset.univ, a (p j) ≤ x := by
        rw [←h33]
        have h36 : Finset.filter (· ≤ i') Finset.univ ⊆ Finset.univ := by
          intro j hj
          simp
        have h38 : ∑ j ∈ Finset.filter (· ≤ i') Finset.univ, a' (p' j) ≤
            ∑ j : Fin n', a' (p' j) := by
          simpa [Finset.sum_filter] using
            (Finset.sum_le_sum_of_subset_of_nonneg h36 (by
              intro j hj1 hj2
              exact le_of_lt (apos' (p' j))))
        have pb' : p'.toFun.Bijective := EquivLike.bijective p'
        have h39 : (∑ j : Fin n', a' (p' j)) = ∑ j : Fin n', a' j := by
          simpa using (Function.Bijective.sum_comp pb' (fun j ↦ a' j))
        have h40 : (∑ j : Fin n', a' j) = x := by
          let f : Fin n' ↪ Fin n := embedFinLE (Nat.sub_le _ _)
          have h41 : (Finset.univ (α := Fin n')).map f =
             Finset.filter (·.val < n - 1) Finset.univ := by
            ext z
            rw [Finset.mem_map, Finset.mem_filter]
            constructor
            · rintro ⟨y, hy1, hy2⟩
              simp only [Finset.mem_univ, true_and]
              rw [←hy2]
              obtain ⟨y', hy'⟩ := y
              exact hy'
            · rintro ⟨_, hz⟩
              use ⟨z.val, by lia⟩
              simp [f, embedFinLE]
          unfold x
          rw [←h41, Finset.sum_map]
          congr
        calc
          ∑ j ∈ Finset.filter (· ≤ i') Finset.univ, a' (p' j) ≤
              ∑ j : Fin n', a' (p' j) := h38
          _ = ∑ j : Fin n', a' j := h39
          _ = x := h40
      intro H
      exact (h31 ⟨H, h34⟩).elim
    · have h31 : i.val = n' := by lia
      have h32 : ∑ j ∈ Finset.filter (fun x ↦ x ≤ i) Finset.univ, a (p j) =
                 ∑ i : Fin n, a i := by
        have pb : p.toFun.Bijective := EquivLike.bijective p
        rw [←Function.Bijective.sum_comp pb (fun j ↦ a j)]
        have h33 : i.val + 1 = n := by lia
        have h10 : Finset.filter (fun x ↦ x ≤ i) Finset.univ =
                    Finset.univ (α := Fin n) := by
          ext x
          rw [Finset.mem_filter]
          suffices x ≤ i from and_iff_left_of_imp fun a ↦ this
          lia
        rw [h10]
        dsimp
      rw [h32]
      exact hM
  · sorry

-- The problem with an additional assumption that a is sorted.
theorem imo2009_p6_aux2 (n : ℕ) (hn : 0 < n)
    (a : Fin n → ℤ)
    (ainj : a.Injective)
    (apos : ∀ i, 0 < a i)
    (asorted : ∀ i j, i < j → a i < a j)
    (M : Finset ℤ)
    (Mpos : ∀ m ∈ M, 0 < m)
    (Mcard : M.card = n - 1)
    (hM : ∑ i, a i ∉ M)
    : ∃ p : Equiv.Perm (Fin n),
          ∀ i : Fin n, ∑ j ∈ Finset.univ.filter (· ≤ i), a (p j) ∉ M := by
  have Mcard' := Mcard.le
  exact imo2009_p6_aux1 n hn a ainj apos asorted M Mpos Mcard' hM

snip end

problem imo2009_p6 (n : ℕ) (hn : 0 < n)
    (a : Fin n → ℤ)
    (ainj : a.Injective)
    (apos : ∀ i, 0 < a i)
    (M : Finset ℤ)
    (Mpos : ∀ m ∈ M, 0 < m)
    (Mcard : M.card = n - 1)
    (hM : ∑ i, a i ∉ M)
    : ∃ p : Equiv.Perm (Fin n),
        ∀ i : Fin n,
          ∑ j ∈ Finset.univ.filter (· ≤ i), a (p j) ∉ M := by
  obtain ⟨ps, hps⟩ := lemma2 n a ainj
  have ainj' : (a ∘ ps).Injective := (Equiv.injective_comp ps a).mpr ainj
  have apos' : ∀ (i : Fin n), 0 < (a ∘ ps) i := by
    intro i
    exact apos (ps i)
  have hM' : ∑ i : Fin n, (a ∘ ps) i ∉ M := by
    let ps' := ps.invFun
    have h0 : ps'.Bijective := by aesop
    have h3 : ∀ x, ps (ps' x) = x := Equiv.right_inv _
    have h3' : ∀ x, a (ps.toFun (ps' x)) = a x := by
      intro x
      exact congrArg a (ainj (congrArg a (h3 x)))
    have h1 : Finset.map ⟨ps', h0.1⟩ Finset.univ = Finset.univ := by simp
    rw [←h1]
    rw [Finset.sum_map, Function.Embedding.coeFn_mk]
    simp_rw [Function.comp_apply]
    dsimp at h3' ⊢
    rw [Fintype.sum_congr _ _ h3']
    exact hM
  obtain ⟨p', hp⟩ :=
    imo2009_p6_aux2 n hn (a ∘ ps) ainj' apos' hps M Mpos Mcard hM'
  exact ⟨p'.trans ps, hp⟩

end Imo2009P6
