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

lemma sum_perm {α β : Type*} [Fintype α] [AddCommMonoid β]
    (p : Equiv.Perm α) (f : α → β) :
    (∑ i, f (p i)) = ∑ i, f i := by
  have hp : p.toFun.Bijective := EquivLike.bijective p
  simpa using Function.Bijective.sum_comp hp f

lemma filter_le_last {n : ℕ} (last : Fin n) (hlast : last.val = n - 1) :
    Finset.filter (fun i : Fin n => i ≤ last) Finset.univ = Finset.univ := by
  ext i
  rw [Finset.mem_filter]
  constructor
  · exact fun h => h.1
  · intro _
    refine ⟨Finset.mem_univ _, ?_⟩
    change i.val ≤ last.val
    omega

lemma prefix_last_perm {β : Type*} [AddCommMonoid β] {n : ℕ}
    (f : Fin n → β) (p : Equiv.Perm (Fin n)) (last : Fin n) (hlast : last.val = n - 1) :
    (∑ j ∈ Finset.filter (fun j : Fin n => j ≤ last) Finset.univ, f (p j)) = ∑ j, f j := by
  rw [filter_le_last last hlast]
  exact sum_perm p f

lemma sum_init {β : Type*} [AddCommMonoid β] {n : ℕ} (f : Fin n → β) :
    (∑ i : Fin (n - 1), f ⟨i, by omega⟩) =
      ∑ i ∈ Finset.filter (fun i : Fin n => (i : ℕ) < n - 1) Finset.univ, f i := by
  let e : Fin (n - 1) ↪ Fin n := embedFinLE (Nat.sub_le n 1)
  have hmap : (Finset.univ (α := Fin (n - 1))).map e =
      Finset.filter (fun i : Fin n => (i : ℕ) < n - 1) Finset.univ := by
    ext z
    rw [Finset.mem_map, Finset.mem_filter]
    constructor
    · rintro ⟨w, -, hwz⟩
      simp only [Finset.mem_univ, true_and]
      rw [← hwz]
      exact w.2
    · rintro ⟨-, hz⟩
      use ⟨z.val, by omega⟩
      simp [e, embedFinLE]
  rw [← hmap, Finset.sum_map]
  congr

lemma sum_init_of_eq {β : Type*} [AddCommMonoid β] {n k : ℕ} (hk : k = n - 1)
    (f : Fin n → β) :
    (∑ i : Fin k, f ⟨i, by omega⟩) =
      ∑ i ∈ Finset.filter (fun i : Fin n => (i : ℕ) < n - 1) Finset.univ, f i := by
  subst k
  exact sum_init f

lemma sum_init_add_last {β : Type*} [AddCommMonoid β] {n : ℕ}
    (f : Fin n → β) (last : Fin n) (hlast : last.val = n - 1) :
    (∑ i : Fin n, f i) = (∑ i : Fin (n - 1), f ⟨i, by omega⟩) + f last := by
  have hsplit := Finset.sum_erase_add (s := (Finset.univ : Finset (Fin n)))
    (a := last) (f := f) (by simp)
  have herase : (Finset.univ.erase last) =
      Finset.filter (fun i : Fin n => (i : ℕ) < n - 1) Finset.univ := by
    ext z
    rw [Finset.mem_erase, Finset.mem_filter]
    constructor
    · rintro ⟨hz_ne, -⟩
      constructor
      · simp
      · have hz_ne_val : z.val ≠ n - 1 := by
          intro hzv
          apply hz_ne
          apply Fin.ext
          omega
        omega
    · rintro ⟨-, hzlt⟩
      constructor
      · intro hz_eq
        have hval := congrArg Fin.val hz_eq
        omega
      · simp
  rw [herase] at hsplit
  rw [← sum_init f] at hsplit
  exact hsplit.symm

lemma init_injective {n : ℕ} {a : Fin n → ℤ} (ainj : a.Injective) :
    (fun i : Fin (n - 1) => a ⟨i, by omega⟩).Injective := by
  intro i j hij
  have h := congrArg Fin.val (@ainj ⟨i, by omega⟩ ⟨j, by omega⟩ hij)
  exact Fin.eq_of_val_eq (by simpa using h)

lemma init_pos {n : ℕ} {a : Fin n → ℤ} (apos : ∀ i, 0 < a i) :
    ∀ i : Fin (n - 1), 0 < a ⟨i, by omega⟩ := by
  intro i
  exact apos ⟨i.val, by omega⟩

lemma init_sorted {n : ℕ} {a : Fin n → ℤ}
    (asorted : ∀ i j, i < j → a i < a j) :
    ∀ i j : Fin (n - 1), i < j → a ⟨i, by omega⟩ < a ⟨j, by omega⟩ := by
  intro i j hij
  exact asorted ⟨i, by omega⟩ ⟨j, by omega⟩ hij

lemma prefix_extendPerm {β : Type*} [AddCommMonoid β] {m n : ℕ}
    (f : Fin n → β) (p : Equiv.Perm (Fin m)) (hmn : m ≤ n)
    (i : Fin n) (hi : i.val < m) :
    (∑ j ∈ Finset.filter (fun j : Fin n => j ≤ i) Finset.univ, f (extendPerm p hmn j)) =
      ∑ j ∈ Finset.filter (fun j : Fin m => j ≤ (⟨i.val, hi⟩ : Fin m)) Finset.univ,
        f ⟨p j, by omega⟩ := by
  let i' : Fin m := ⟨i.val, hi⟩
  let emb : Fin m ↪ Fin n := embedFinLE hmn
  have hmap : (Finset.univ.filter (· ≤ i')).map emb =
      Finset.univ.filter (· ≤ i) := by
    ext z
    rw [Finset.mem_map, Finset.mem_filter]
    constructor
    · rintro ⟨j, hj, hjz⟩
      simp only [Finset.mem_univ, true_and]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      rw [← hjz]
      exact hj
    · rintro ⟨-, hzle⟩
      use ⟨z.val, by omega⟩
      simp only [Finset.mem_filter, emb, embedFinLE]
      dsimp
      simp only [eq_self, and_true, Finset.mem_univ, true_and]
      exact hzle
  rw [← hmap, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro j hj
  have hjlt : ((emb j : Fin n) : ℕ) < m := by
    dsimp [emb, embedFinLE]
    exact j.isLt
  rw [extendPerm_apply_of_lt p hmn (emb j) hjlt]
  simp [emb, embedFinLE]

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
  by_cases h2 : ∃ y, x < y ∧ y ∈ M
  · by_cases h1 : x ∈ M
    · intro hM
      obtain ⟨y, hyx, hyM⟩ := h2
      have hn3 : 3 ≤ n := by
        have hxy : x ≠ y := by omega
        have hpair : ({x, y} : Finset ℤ) ⊆ M := by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl
          · exact h1
          · exact hyM
        have hcard2 : 2 ≤ M.card := by
          have hcardpair : ({x, y} : Finset ℤ).card = 2 := by simp [hxy]
          rw [← hcardpair]
          exact Finset.card_le_card hpair
        omega
      let n1 := n - 1
      let m := n - 2
      let s : ℤ := ∑ i : Fin n, a i
      let lastFull : Fin n := ⟨n - 1, by omega⟩
      let small : Fin n1 → Fin n := fun i => ⟨i.val, by omega⟩
      have hsmall_pos : ∀ i : Fin n1, 0 < a (small i) := fun i => apos (small i)
      have hlast_gt_small : ∀ i : Fin n1, a (small i) < a lastFull := by
        intro i
        have hlt : small i < lastFull := by
          change (small i).val < lastFull.val
          dsimp [small, lastFull, n1]
          exact i.isLt
        exact asorted (small i) lastFull hlt
      have hs_eq : s = x + a lastFull := by
        unfold s x
        rw [sum_init_add_last a lastFull (by dsimp [lastFull])]
        rw [sum_init]
      have hchoose : ∃ r : Fin n1, x - a (small r) ∉ M ∧ s - a (small r) ∉ M := by
        let Bad : Finset (Fin n1) := Finset.univ.filter fun i =>
          x - a (small i) ∈ M ∨ s - a (small i) ∈ M
        have hBad_card : Bad.card ≤ n - 2 := by
          let badVal : Fin n1 → ℤ := fun i =>
            if x - a (small i) ∈ M then x - a (small i) else s - a (small i)
          have hmaps : ∀ i ∈ Bad, badVal i ∈ M.erase x := by
            intro i hi
            simp only [Bad, Finset.mem_filter, Finset.mem_univ, true_and] at hi
            dsimp [badVal]
            by_cases hb : x - a (small i) ∈ M
            · rw [if_pos hb]
              rw [Finset.mem_erase]
              constructor
              · have hpos := hsmall_pos i
                omega
              · exact hb
            · rw [if_neg hb]
              rw [Finset.mem_erase]
              constructor
              · have hgt := hlast_gt_small i
                rw [hs_eq]
                omega
              · exact hi.resolve_left hb
          have hinj : Set.InjOn badVal (Bad : Set (Fin n1)) := by
            intro i hi j hj hij
            dsimp [badVal] at hij
            by_cases hiL : x - a (small i) ∈ M <;> by_cases hjL : x - a (small j) ∈ M
            · rw [if_pos hiL, if_pos hjL] at hij
              have haeq : a (small i) = a (small j) := by omega
              exact Fin.eq_of_val_eq (by
                have hsmall_eq := congrArg Fin.val (ainj haeq)
                simpa [small] using hsmall_eq)
            · rw [if_pos hiL, if_neg hjL] at hij
              have hposi := hsmall_pos i
              have hgtj := hlast_gt_small j
              rw [hs_eq] at hij
              omega
            · rw [if_neg hiL, if_pos hjL] at hij
              have hgti := hlast_gt_small i
              have hposj := hsmall_pos j
              rw [hs_eq] at hij
              omega
            · rw [if_neg hiL, if_neg hjL] at hij
              have haeq : a (small i) = a (small j) := by omega
              exact Fin.eq_of_val_eq (by
                have hsmall_eq := congrArg Fin.val (ainj haeq)
                simpa [small] using hsmall_eq)
          have hle_erase : Bad.card ≤ (M.erase x).card := by
            apply Finset.card_le_card_of_injOn badVal hmaps hinj
          have herase_card : (M.erase x).card + 1 = M.card := Finset.card_erase_add_one h1
          omega
        by_contra hnone
        push Not at hnone
        have hBad_univ : Bad = Finset.univ := by
          ext i
          simp only [Bad, Finset.mem_filter, Finset.mem_univ, true_and]
          refine iff_true_intro ?_
          by_cases hxmem : x - a (small i) ∈ M
          · exact Or.inl hxmem
          · exact Or.inr ((hnone i) hxmem)
        have hcard_univ : Bad.card = n1 := by rw [hBad_univ, Finset.card_univ, Fintype.card_fin]
        omega
      obtain ⟨r, hrx, hrs⟩ := hchoose
      let smallM : Fin (m + 1) → Fin n := fun i => ⟨i.val, by omega⟩
      let rCast : Fin (m + 1) := ⟨r.val, by omega⟩
      let restEmb : Fin m → Fin n1 := fun j => ⟨(rCast.succAbove j).val, by omega⟩
      let restSmall : Fin m → Fin n := fun j => small (restEmb j)
      let b : Fin m → ℤ := fun j => a (restSmall j)
      have hmpos : 0 < m := by omega
      have hrest_ne : ∀ j, restEmb j ≠ r := by
        intro j h
        have h' : rCast.succAbove j = rCast := by
          apply Fin.ext
          have hv := congrArg Fin.val h
          dsimp [restEmb, rCast] at hv ⊢
          exact hv
        exact Fin.succAbove_ne rCast j h'
      have hrest_inj : Function.Injective restEmb := by
        intro i j hij
        apply Fin.succAbove_right_injective (p := rCast)
        apply Fin.ext
        have hv := congrArg Fin.val hij
        dsimp [restEmb] at hv ⊢
        exact hv
      have hrest_mono : ∀ {i j : Fin m}, i < j → restEmb i < restEmb j := by
        intro i j hij
        have hs : rCast.succAbove i < rCast.succAbove j := (Fin.strictMono_succAbove rCast) hij
        change (restEmb i).val < (restEmb j).val
        dsimp [restEmb]
        exact hs
      have binj : b.Injective := by
        intro i j hij
        have hsmall_eq : restSmall i = restSmall j := ainj hij
        have hrest_eq : restEmb i = restEmb j := by
          apply Fin.ext
          have hv := congrArg Fin.val hsmall_eq
          simpa [restSmall, small] using hv
        exact hrest_inj hrest_eq
      have bpos : ∀ i, 0 < b i := fun i => apos (restSmall i)
      have bsorted : ∀ i j, i < j → b i < b j := by
        intro i j hij
        exact asorted (restSmall i) (restSmall j) (hrest_mono hij)
      have hsum_m1 : ∑ i : Fin (m + 1), a (smallM i) = x := by
        simpa [x, smallM] using sum_init_of_eq (n := n) (k := m + 1) (by omega) a
      have hsum_rest : ∑ j : Fin m, b j = x - a (small r) := by
        have hsplit := Fin.sum_univ_succAbove (fun i : Fin (m + 1) => a (smallM i)) rCast
        rw [hsum_m1] at hsplit
        have hrval : smallM rCast = small r := by
          apply Fin.ext
          dsimp [smallM, small, rCast]
        have htail : (∑ i : Fin m, a (smallM (rCast.succAbove i))) = ∑ j : Fin m, b j := by
          apply Finset.sum_congr rfl
          intro j hj
          simp [b, restSmall, restEmb, smallM, small]
        rw [hrval, htail] at hsplit
        omega
      let t : ℤ := x - a (small r)
      let M' := M.filter (fun z => z ≤ t)
      have Mpos' : ∀ z ∈ M', 0 < z := by
        intro z hz
        exact Mpos z (Finset.mem_of_mem_filter z hz)
      have Mcard' : M'.card ≤ m - 1 := by
        have hxM' : x ∉ M' := by
          intro hx
          rw [Finset.mem_filter] at hx
          have hpos := hsmall_pos r
          dsimp [t] at hx
          omega
        have hyM' : y ∉ M' := by
          intro hy
          rw [Finset.mem_filter] at hy
          have hpos := hsmall_pos r
          dsimp [t] at hy
          omega
        have hy_not_cons : y ∉ Finset.cons x M' hxM' := by
          intro hyc
          rw [Finset.mem_cons] at hyc
          rcases hyc with hy_eq | hyin
          · omega
          · exact hyM' hyin
        let M'' := Finset.cons y (Finset.cons x M' hxM') hy_not_cons
        have hsub : M'' ⊆ M := by
          intro z hz
          rw [Finset.mem_cons] at hz
          rcases hz with rfl | hz
          · exact hyM
          · rw [Finset.mem_cons] at hz
            rcases hz with rfl | hz
            · exact h1
            · exact (Finset.mem_filter.mp hz).1
        have hle : M''.card ≤ M.card := Finset.card_le_card hsub
        have hc : M''.card = M'.card + 2 := by
          dsimp [M'']
          rw [Finset.card_cons, Finset.card_cons]
        omega
      have hM' : ∑ j : Fin m, b j ∉ M' := by
        rw [hsum_rest]
        intro ht
        exact hrx (Finset.mem_of_mem_filter _ ht)
      obtain ⟨p', hp'⟩ := ih m (by omega) hmpos b binj bpos bsorted M' Mpos' Mcard' hM'
      let pSmallFun : Fin n1 → Fin n1 := fun i =>
        if hi : i.val < m then restEmb (p' ⟨i.val, hi⟩) else r
      have hpSmallFun_inj : pSmallFun.Injective := by
        intro i j hij
        dsimp [pSmallFun] at hij
        by_cases hi : i.val < m <;> by_cases hj : j.val < m
        · simp [hi, hj] at hij
          have hrest_eq : p' ⟨i.val, hi⟩ = p' ⟨j.val, hj⟩ := hrest_inj hij
          have hidx : (⟨i.val, hi⟩ : Fin m) = ⟨j.val, hj⟩ := p'.injective hrest_eq
          apply Fin.ext
          exact congrArg (fun z : Fin m => z.val) hidx
        · simp [hi, hj] at hij
          exact (hrest_ne (p' ⟨i.val, hi⟩) hij).elim
        · simp [hi, hj] at hij
          exact (hrest_ne (p' ⟨j.val, hj⟩) hij.symm).elim
        · apply Fin.ext
          omega
      let pSmall : Equiv.Perm (Fin n1) := Equiv.ofBijective pSmallFun
        (Finite.injective_iff_bijective.mp hpSmallFun_inj)
      have hpSmall_before (i : Fin n1) (hi : i.val < m) :
          pSmall i = restEmb (p' ⟨i.val, hi⟩) := by
        simp [pSmall, Equiv.ofBijective_apply, pSmallFun, hi]
      have hpSmall_last (i : Fin n1) (hi : ¬ i.val < m) : pSmall i = r := by
        simp [pSmall, Equiv.ofBijective_apply, pSmallFun, hi]
      let p0 : Equiv.Perm (Fin n) := extendPerm pSmall (Nat.sub_le n 1)
      let secondLast : Fin n := ⟨m, by omega⟩
      let p : Equiv.Perm (Fin n) := (Equiv.swap secondLast lastFull).trans p0
      have hp_before (j : Fin n) (hj : j.val < m) : p j = restSmall (p' ⟨j.val, hj⟩) := by
        have hne_second : j ≠ secondLast := by
          intro h
          have hv := congrArg Fin.val h
          dsimp [secondLast] at hv
          omega
        have hne_last : j ≠ lastFull := by
          intro h
          have hv := congrArg Fin.val h
          dsimp [lastFull] at hv
          omega
        change p0 ((Equiv.swap secondLast lastFull) j) = restSmall (p' ⟨j.val, hj⟩)
        rw [Equiv.swap_apply_of_ne_of_ne hne_second hne_last]
        have hjn1 : (j : ℕ) < n1 := by omega
        rw [extendPerm_apply_of_lt pSmall (Nat.sub_le n 1) j hjn1]
        apply Fin.ext
        have hjsmall : (⟨j.val, hjn1⟩ : Fin n1).val < m := by simpa
        have hps := hpSmall_before ⟨j.val, hjn1⟩ hjsmall
        have hv := congrArg Fin.val hps
        dsimp [restSmall, small] at hv ⊢
        exact hv
      have hp_second : p secondLast = lastFull := by
        change p0 ((Equiv.swap secondLast lastFull) secondLast) = lastFull
        rw [Equiv.swap_apply_left]
        have hnlt : ¬ ((lastFull : Fin n) : ℕ) < n1 := by
          dsimp [lastFull, n1]
          omega
        exact extendPerm_apply_of_not_lt pSmall (Nat.sub_le n 1) lastFull hnlt
      have hp_last : p lastFull = small r := by
        change p0 ((Equiv.swap secondLast lastFull) lastFull) = small r
        rw [Equiv.swap_apply_right]
        have hlt : ((secondLast : Fin n) : ℕ) < n1 := by
          dsimp [secondLast, n1, m]
          omega
        rw [extendPerm_apply_of_lt pSmall (Nat.sub_le n 1) secondLast hlt]
        apply Fin.ext
        have hnot : ¬ (⟨secondLast.val, hlt⟩ : Fin n1).val < m := by
          dsimp [secondLast]
          omega
        have hps := hpSmall_last ⟨secondLast.val, hlt⟩ hnot
        have hv := congrArg Fin.val hps
        dsimp [small] at hv ⊢
        exact hv
      refine ⟨p, ?_⟩
      intro i
      by_cases hi_before : i.val < m
      · let i' : Fin m := ⟨i.val, hi_before⟩
        have hprefix :
            ∑ j ∈ Finset.filter (· ≤ i) Finset.univ, a (p j) =
              ∑ j ∈ Finset.filter (· ≤ i') Finset.univ, b (p' j) := by
          let embM : Fin m ↪ Fin n := embedFinLE (by omega)
          have hmap : (Finset.univ.filter (· ≤ i')).map embM =
              Finset.univ.filter (· ≤ i) := by
            ext z
            rw [Finset.mem_map, Finset.mem_filter]
            constructor
            · rintro ⟨j, hj, hjz⟩
              simp only [Finset.mem_univ, true_and]
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
              rw [← hjz]
              exact hj
            · rintro ⟨-, hzle⟩
              use ⟨z.val, by omega⟩
              simp only [Finset.mem_filter, embM, embedFinLE]
              dsimp
              simp only [eq_self, and_true, Finset.mem_univ, true_and]
              exact hzle
          rw [← hmap, Finset.sum_map]
          apply Finset.sum_congr rfl
          intro j hj
          have hjlt : ((embM j : Fin n) : ℕ) < m := by
            dsimp [embM, embedFinLE]
            exact j.isLt
          rw [hp_before (embM j) hjlt]
          simp [b, embM, embedFinLE]
        have hnotM' : ∑ j ∈ Finset.filter (· ≤ i) Finset.univ, a (p j) ∉ M' := by
          simpa [hprefix] using hp' i'
        have hle_t : ∑ j ∈ Finset.filter (· ≤ i) Finset.univ, a (p j) ≤ t := by
          rw [hprefix]
          have hsubset : Finset.filter (· ≤ i') Finset.univ ⊆ (Finset.univ : Finset (Fin m)) := by
            intro z hz
            simp
          have hle_total :
              ∑ j ∈ Finset.filter (· ≤ i') Finset.univ, b (p' j) ≤ ∑ j : Fin m, b (p' j) := by
            exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
              intro z hz1 hz2
              exact le_of_lt (bpos (p' z)))
          have hsum_perm : (∑ j : Fin m, b (p' j)) = ∑ j : Fin m, b j := sum_perm p' b
          calc
            ∑ j ∈ Finset.filter (· ≤ i') Finset.univ, b (p' j) ≤ ∑ j : Fin m, b (p' j) := hle_total
            _ = ∑ j : Fin m, b j := hsum_perm
            _ = t := by rw [hsum_rest]
        intro hmem
        exact hnotM' (Finset.mem_filter.mpr ⟨hmem, hle_t⟩)
      · by_cases hi_second_val : i.val = m
        · have hi_second : i = secondLast := by
            apply Fin.ext
            simpa [secondLast] using hi_second_val
          subst hi_second
          let P : Finset (Fin n) := Finset.filter (· ≤ secondLast) Finset.univ
          have hPsecond : secondLast ∈ P := by simp [P]
          have hprefix_second :
              ∑ j ∈ Finset.filter (· ≤ secondLast) Finset.univ, a (p j) =
                a lastFull + ∑ j : Fin m, b (p' j) := by
            change ∑ j ∈ P, a (p j) = a lastFull + ∑ j : Fin m, b (p' j)
            let embM : Fin m ↪ Fin n := embedFinLE (by omega)
            have hmap_all : (Finset.univ (α := Fin m)).map embM = P.erase secondLast := by
              ext z
              rw [Finset.mem_map, Finset.mem_erase]
              constructor
              · rintro ⟨j, -, hjz⟩
                constructor
                · intro hzsecond
                  have hv := congrArg Fin.val (hjz.trans hzsecond)
                  dsimp [embM, embedFinLE, secondLast, m] at hv
                  omega
                · rw [← hjz]
                  simp only [P, Finset.mem_filter, Finset.mem_univ, true_and]
                  change j.val ≤ secondLast.val
                  dsimp [secondLast, m]
                  omega
              · rintro ⟨hz_ne, hzP⟩
                simp only [P, Finset.mem_filter, Finset.mem_univ, true_and] at hzP
                use ⟨z.val, by
                  have hz_ne_val : z.val ≠ m := by
                    intro hzv
                    apply hz_ne
                    apply Fin.ext
                    simpa [secondLast] using hzv
                  change z.val ≤ secondLast.val at hzP
                  dsimp [secondLast, m] at hzP
                  omega⟩
                constructor
                · simp
                · apply Fin.ext
                  rfl
            rw [← Finset.add_sum_erase P (fun j => a (p j)) hPsecond]
            rw [hp_second]
            congr 1
            rw [← hmap_all, Finset.sum_map]
            apply Finset.sum_congr rfl
            intro j hj
            have hjlt : ((embM j : Fin n) : ℕ) < m := by
              dsimp [embM, embedFinLE]
              exact j.isLt
            rw [hp_before (embM j) hjlt]
            simp [b, embM, embedFinLE]
          have hsum_perm : (∑ j : Fin m, b (p' j)) = ∑ j : Fin m, b j := sum_perm p' b
          have hvalue : ∑ j ∈ Finset.filter (· ≤ secondLast) Finset.univ, a (p j) = s - a (small r) := by
            rw [hprefix_second, hsum_perm, hsum_rest]
            rw [hs_eq]
            omega
          rw [hvalue]
          exact hrs
        · have hi_last : i = lastFull := by
            apply Fin.ext
            have hival_lt := i.isLt
            dsimp [lastFull, m] at hival_lt ⊢
            omega
          subst hi_last
          rw [prefix_last_perm a p lastFull (by dsimp [lastFull])]
          exact hM
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
      have ainj' : a'.Injective := by simpa [a', n'] using init_injective (a := a) ainj
      have apos' : ∀ (i : Fin n'), 0 < a' i := by simpa [a', n'] using init_pos (a := a) apos
      have asorted' : ∀ (i j : Fin n'), i < j → a' i < a' j := by
        simpa [a', n'] using init_sorted (a := a) asorted
      have Mpos' : (∀ m ∈ M', 0 < m) := by
        intro m hm
        rw [Finset.mem_filter] at hm
        exact Mpos m hm.1
      have hM' : ∑ i : Fin n', a' i ∉ M' := by
        have h14 : ∑ i : Fin n', a' i = x := by
          simpa [a', x, n'] using sum_init a
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
          simpa [a', p] using (prefix_extendPerm a p' (Nat.sub_le n 1) i h30).symm
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
          have h39 : (∑ j : Fin n', a' (p' j)) = ∑ j : Fin n', a' j := sum_perm p' a'
          have h40 : (∑ j : Fin n', a' j) = x := by
            simpa [a', x, n'] using sum_init a
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
          exact prefix_last_perm a p i (by omega)
        rw [h32]
        exact hM
  · intro hM
    by_cases hMempty : M = ∅
    · refine ⟨Equiv.refl _, ?_⟩
      intro i
      rw [hMempty]
      exact Finset.notMem_empty _
    · have hnonempty : M.Nonempty := Finset.nonempty_iff_ne_empty.mpr hMempty
      let z : ℤ := M.max' hnonempty
      have hzM : z ∈ M := Finset.max'_mem M hnonempty
      have hzmax : ∀ w ∈ M, w ≤ z := by
        intro w hw
        exact Finset.le_max' M w hw
      have hcard_pos : 0 < M.card := Finset.card_pos.mpr hnonempty
      have hn2 : 2 ≤ n := by omega
      let n' := n - 1
      have hn'pos : 0 < n' := by omega
      let a' := fun i : Fin n' => a ⟨i, by omega⟩
      have ainj' : a'.Injective := by simpa [a', n'] using init_injective (a := a) ainj
      have apos' : ∀ (i : Fin n'), 0 < a' i := by simpa [a', n'] using init_pos (a := a) apos
      have asorted' : ∀ (i j : Fin n'), i < j → a' i < a' j := by
        simpa [a', n'] using init_sorted (a := a) asorted
      let M' := M.erase z
      have Mpos' : ∀ m ∈ M', 0 < m := by
        intro m hm
        exact Mpos m (Finset.mem_of_mem_erase hm)
      have Mcard' : M'.card ≤ n' - 1 := by
        have hzcard : M'.card + 1 = M.card := Finset.card_erase_add_one hzM
        omega
      have hsumx : ∑ i : Fin n', a' i = x := by
        simpa [a', x, n'] using sum_init a
      have hM' : ∑ i : Fin n', a' i ∉ M' := by
        rw [hsumx]
        intro hx
        rw [Finset.mem_erase] at hx
        obtain ⟨hxne, hxM⟩ := hx
        have hxz : x ≤ z := Finset.le_max' M x hxM
        have hzx : z ≤ x := by
          by_contra hzx
          exact h2 ⟨z, not_le.mp hzx, hzM⟩
        exact hxne (le_antisymm hxz hzx)
      obtain ⟨p', hp'⟩ := ih n' (by omega) hn'pos a' ainj' apos' asorted' M' Mpos' Mcard' hM'
      let lastFull : Fin n := ⟨n - 1, by omega⟩
      let p0 : Equiv.Perm (Fin n) := extendPerm p' (Nat.sub_le n 1)
      by_cases hhit : ∃ k : Fin n', ∑ j ∈ Finset.filter (· ≤ k) Finset.univ, a' (p' j) = z
      · obtain ⟨k, hk⟩ := hhit
        let hitFull : Fin n := ⟨k.val, by omega⟩
        let p : Equiv.Perm (Fin n) := (Equiv.swap hitFull lastFull).trans p0
        have hp_hit : p hitFull = lastFull := by
          change p0 ((Equiv.swap hitFull lastFull) hitFull) = lastFull
          rw [Equiv.swap_apply_left]
          have hnlt : ¬ ((lastFull : Fin n) : ℕ) < n' := by
            dsimp [lastFull, n']
            omega
          exact extendPerm_apply_of_not_lt p' (Nat.sub_le n 1) lastFull hnlt
        let Sprev : Finset (Fin n') := Finset.filter (· < k) Finset.univ
        have hrec_decomp : z = ∑ j ∈ Sprev, a' (p' j) + a' (p' k) := by
          have hkmem : k ∈ Finset.filter (· ≤ k) (Finset.univ : Finset (Fin n')) := by simp
          have hsplit := Finset.sum_erase_add
            (s := Finset.filter (· ≤ k) (Finset.univ : Finset (Fin n')))
            (a := k) (f := fun j => a' (p' j)) hkmem
          have herase : (Finset.filter (· ≤ k) (Finset.univ : Finset (Fin n'))).erase k = Sprev := by
            ext q
            rw [Finset.mem_erase]
            simp only [Sprev, Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · rintro ⟨hqne, hqle⟩
              exact lt_of_le_of_ne hqle hqne
            · intro hqlt
              exact ⟨ne_of_lt hqlt, le_of_lt hqlt⟩
          rw [herase] at hsplit
          omega
        let P : Finset (Fin n) := Finset.filter (· ≤ hitFull) Finset.univ
        have hPhit : hitFull ∈ P := by simp [P]
        have hprefix_hit :
            ∑ j ∈ Finset.filter (· ≤ hitFull) Finset.univ, a (p j) =
              a lastFull + ∑ j ∈ Sprev, a' (p' j) := by
          change ∑ j ∈ P, a (p j) = a lastFull + ∑ j ∈ Sprev, a' (p' j)
          let emb : Fin n' ↪ Fin n := embedFinLE (Nat.sub_le n 1)
          have hmap_prev : Sprev.map emb = P.erase hitFull := by
            ext q
            rw [Finset.mem_map, Finset.mem_erase]
            constructor
            · rintro ⟨j, hjS, hjq⟩
              have hjlt : j < k := by simpa [Sprev] using hjS
              constructor
              · intro hqhit
                have hv := congrArg Fin.val (hjq.trans hqhit)
                dsimp [emb, embedFinLE, hitFull] at hv
                have hvlt : j.val < k.val := by exact hjlt
                omega
              · rw [← hjq]
                simp only [P, Finset.mem_filter, Finset.mem_univ, true_and]
                change j.val ≤ hitFull.val
                dsimp [hitFull]
                exact le_of_lt hjlt
            · rintro ⟨hq_ne, hqP⟩
              simp only [P, Finset.mem_filter, Finset.mem_univ, true_and] at hqP
              have hqle : q.val ≤ k.val := by
                change q.val ≤ hitFull.val at hqP
                dsimp [hitFull] at hqP
                exact hqP
              use ⟨q.val, by omega⟩
              constructor
              · simp only [Sprev, Finset.mem_filter, Finset.mem_univ, true_and]
                have hq_ne_val : q.val ≠ k.val := by
                  intro hqv
                  apply hq_ne
                  apply Fin.ext
                  simpa [hitFull] using hqv
                change q.val < k.val
                omega
              · apply Fin.ext
                rfl
          rw [← Finset.add_sum_erase P (fun j => a (p j)) hPhit]
          rw [hp_hit]
          congr 1
          rw [← hmap_prev, Finset.sum_map]
          apply Finset.sum_congr rfl
          intro j hj
          have hjlt : j < k := by simpa [Sprev] using hj
          have hne_hit : (emb j : Fin n) ≠ hitFull := by
            intro h
            have hv := congrArg Fin.val h
            dsimp [emb, embedFinLE, hitFull] at hv
            have hvlt : j.val < k.val := by exact hjlt
            omega
          have hne_last : (emb j : Fin n) ≠ lastFull := by
            intro h
            have hv := congrArg Fin.val h
            dsimp [emb, embedFinLE, lastFull, n'] at hv
            omega
          change a (p0 ((Equiv.swap hitFull lastFull) (emb j))) = a' (p' j)
          rw [Equiv.swap_apply_of_ne_of_ne hne_hit hne_last]
          have hjn' : ((emb j : Fin n) : ℕ) < n' := by
            dsimp [emb, embedFinLE, n']
            exact j.isLt
          rw [extendPerm_apply_of_lt p' (Nat.sub_le n 1) (emb j) hjn']
          simp [a', emb, embedFinLE]
        have hbig : a' (p' k) < a lastFull := by
          let idxFull : Fin n := ⟨((p' k : Fin n') : ℕ), by
            have hlt := (p' k).isLt
            dsimp [n'] at hlt ⊢
            omega⟩
          have hlt_fin : idxFull < lastFull := by
            change ((p' k : Fin n') : ℕ) < n - 1
            have hlt := (p' k).isLt
            dsimp [n'] at hlt
            omega
          simpa [a', idxFull] using asorted idxFull lastFull hlt_fin
        have hhit_gt : z < ∑ j ∈ Finset.filter (· ≤ hitFull) Finset.univ, a (p j) := by
          rw [hprefix_hit, hrec_decomp]
          omega
        refine ⟨p, ?_⟩
        intro i
        by_cases hi_last : i = lastFull
        · subst hi_last
          rw [prefix_last_perm a p lastFull (by dsimp [lastFull])]
          exact hM
        · by_cases hi_before : i.val < k.val
          · let i' : Fin n' := ⟨i.val, by omega⟩
            have hik : i' < k := by
              change i.val < k.val
              exact hi_before
            have hprefix :
                ∑ j ∈ Finset.filter (· ≤ i) Finset.univ, a (p j) =
                  ∑ j ∈ Finset.filter (· ≤ i') Finset.univ, a' (p' j) := by
              let emb : Fin n' ↪ Fin n := embedFinLE (Nat.sub_le n 1)
              have hmap : (Finset.univ.filter (· ≤ i')).map emb =
                  Finset.univ.filter (· ≤ i) := by
                ext q
                rw [Finset.mem_map, Finset.mem_filter]
                constructor
                · rintro ⟨j, hj, hjq⟩
                  simp only [Finset.mem_univ, true_and]
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
                  rw [← hjq]
                  exact hj
                · rintro ⟨-, hqle⟩
                  use ⟨q.val, by omega⟩
                  simp only [Finset.mem_filter, emb, embedFinLE]
                  dsimp
                  simp only [eq_self, and_true, Finset.mem_univ, true_and]
                  exact hqle
              rw [← hmap, Finset.sum_map]
              apply Finset.sum_congr rfl
              intro j hj
              have hjle : j ≤ i' := by
                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
                exact hj
              have hne_hit : (emb j : Fin n) ≠ hitFull := by
                intro h
                have hv := congrArg Fin.val h
                dsimp [emb, embedFinLE, hitFull] at hv
                have hjlt : j.val < k.val := lt_of_le_of_lt hjle hik
                omega
              have hne_last : (emb j : Fin n) ≠ lastFull := by
                intro h
                have hv := congrArg Fin.val h
                dsimp [emb, embedFinLE, lastFull, n'] at hv
                omega
              change a (p0 ((Equiv.swap hitFull lastFull) (emb j))) = a' (p' j)
              rw [Equiv.swap_apply_of_ne_of_ne hne_hit hne_last]
              have hjn' : ((emb j : Fin n) : ℕ) < n' := by
                dsimp [emb, embedFinLE, n']
                exact j.isLt
              rw [extendPerm_apply_of_lt p' (Nat.sub_le n 1) (emb j) hjn']
              simp [a', emb, embedFinLE]
            have hnotM' : ∑ j ∈ Finset.filter (· ≤ i) Finset.univ, a (p j) ∉ M' := by
              simpa [hprefix] using hp' i'
            have hlt_z : ∑ j ∈ Finset.filter (· ≤ i') Finset.univ, a' (p' j) < z := by
              let Si : Finset (Fin n') := Finset.filter (· ≤ i') Finset.univ
              let Sk : Finset (Fin n') := Finset.filter (· ≤ k) Finset.univ
              have hknot : k ∉ Si := by
                simp only [Si, Finset.mem_filter, Finset.mem_univ, true_and]
                exact not_le_of_gt hik
              have hsubset : insert k Si ⊆ Sk := by
                intro q hq
                simp only [Finset.mem_insert, Si, Sk, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
                rcases hq with rfl | hq
                · exact le_rfl
                · exact le_trans hq (le_of_lt hik)
              have hle : ∑ j ∈ insert k Si, a' (p' j) ≤ ∑ j ∈ Sk, a' (p' j) := by
                exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
                  intro q hq1 hq2
                  exact le_of_lt (apos' (p' q)))
              have hinsert : ∑ j ∈ insert k Si, a' (p' j) = a' (p' k) + ∑ j ∈ Si, a' (p' j) := by
                rw [Finset.sum_insert hknot]
              rw [hinsert, hk] at hle
              have hposk := apos' (p' k)
              change ∑ j ∈ Si, a' (p' j) < z
              omega
            intro hmem
            have heqz : ∑ j ∈ Finset.filter (· ≤ i) Finset.univ, a (p j) = z :=
              Finset.eq_of_mem_of_notMem_erase hmem hnotM'
            rw [hprefix] at heqz
            omega
          · have hle_hit_i : hitFull ≤ i := by
              change hitFull.val ≤ i.val
              dsimp [hitFull]
              omega
            have hprefix_ge :
                ∑ j ∈ Finset.filter (· ≤ hitFull) Finset.univ, a (p j) ≤
                  ∑ j ∈ Finset.filter (· ≤ i) Finset.univ, a (p j) := by
              have hsubset : Finset.filter (· ≤ hitFull) Finset.univ ⊆
                  Finset.filter (· ≤ i) Finset.univ := by
                intro q hq
                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
                exact le_trans hq hle_hit_i
              exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
                intro q hq1 hq2
                exact le_of_lt (apos (p q)))
            have hgtz : z < ∑ j ∈ Finset.filter (· ≤ i) Finset.univ, a (p j) := by
              omega
            intro hmem
            have hle := hzmax _ hmem
            omega
      · let p : Equiv.Perm (Fin n) := p0
        refine ⟨p, ?_⟩
        intro i
        by_cases hi : i.val < n'
        · let i' : Fin n' := ⟨i.val, hi⟩
          have hprefix :
              ∑ j ∈ Finset.filter (· ≤ i) Finset.univ, a (p j) =
                ∑ j ∈ Finset.filter (· ≤ i') Finset.univ, a' (p' j) := by
            simpa [a', p, p0] using prefix_extendPerm a p' (Nat.sub_le n 1) i hi
          have hnotM' : ∑ j ∈ Finset.filter (· ≤ i) Finset.univ, a (p j) ∉ M' := by
            simpa [hprefix] using hp' i'
          intro hmem
          have heqz : ∑ j ∈ Finset.filter (· ≤ i) Finset.univ, a (p j) = z :=
            Finset.eq_of_mem_of_notMem_erase hmem hnotM'
          apply hhit
          exact ⟨i', by simpa [hprefix] using heqz⟩
        · have hi_last : i = lastFull := by
            apply Fin.ext
            have hival := i.isLt
            dsimp [lastFull, n'] at hival ⊢
            omega
          subst hi_last
          rw [prefix_last_perm a p lastFull (by dsimp [lastFull])]
          exact hM

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
