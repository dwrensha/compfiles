/-
Copyright (c) 2024 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic
import Mathlib.Data.Set.Card

import ProblemExtraction

set_option backward.isDefEq.respectTransparency false

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Olympiad 2008, Problem 5

Let n and k be positive integers with k ≥ n and k - n an even number.
There are 2n lamps labelled 1, 2, ..., 2n each of which can be
either on or off. Initially all the lamps are off. We consider
sequences of steps: at each step one of the lamps is switched (from
on to off or from off to on). Let N be the number of such sequences
consisting of k steps and resulting in the state where lamps 1 through
n are all on, and lamps n + 1 through 2n are all off. Let M be the
number of such sequences consisting of k steps, resulting in the state
where lamps 1 through n are all on, and lamps n + 1 through 2n are all off,
but where none of the lamps n + 1 through 2n is ever switched on.

Determine N/M.
-/

namespace Imo2008P5

abbrev Sequence (n k : ℕ) := Fin k → Fin (2 * n)

abbrev NSequence (n k : ℕ) (f : Sequence n k) : Prop :=
  (∀ i < n, Odd (Nat.card { j | f j = i })) ∧
  (∀ i, n ≤ i → i < 2 * n → Even (Nat.card { j | f j = i }))

abbrev MSequence (n k : ℕ) (f : Sequence n k) : Prop :=
  NSequence n k f ∧
  (∀ i : Fin (2 * n), n ≤ i → ∀ j : Fin k, f j ≠ i)

snip begin

-- We follow the informal solution from
-- https://web.evanchen.cc/exams/IMO-2008-notes.pdf

/-- If g reduces f mod n (mapping [0,n) to itself and [n,2n) to [0,n) by subtracting n),
then the fiber of g at i < n is the disjoint union of the fibers of f at i and n+i. -/
private lemma fiber_ncard_of_mod_n {n k : ℕ} {f g : Fin k → Fin (2 * n)}
    (hg : ∀ j, (g j).val = if (f j).val < n then (f j).val else (f j).val - n)
    (i : ℕ) (hi : i < n) :
    Set.ncard {j | (g j).val = i} =
      Set.ncard {j | (f j).val = i} + Set.ncard {j | (f j).val = n + i} := by
  have hsplit : {j | (g j).val = i} = {j | (f j).val = i} ∪ {j | (f j).val = n + i} := by
    ext j; simp only [Set.mem_setOf, Set.mem_union, hg]
    split_ifs with h <;> constructor <;> intro hj <;> lia
  have hdisj : Disjoint {j | (f j).val = i} {j | (f j).val = n + i} :=
    Set.disjoint_left.mpr fun j h1 h2 => by simp only [Set.mem_setOf] at h1 h2; lia
  rw [hsplit, Set.ncard_union_eq hdisj]

def ψ (n k : ℕ) : { f // NSequence n k f } → { f // MSequence n k f } :=
  fun ⟨f, hf1, hf2⟩ ↦
    let f' := fun ii : Fin k ↦
         if hfi : f ii < n then f ii else ⟨f ii - n, by lia⟩
    have mf' : MSequence n k f' := by
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro i hi
        have hred : ∀ j, (f' j).val = if (f j).val < n then (f j).val else (f j).val - n := by
          intro j; dsimp [f']; split_ifs <;> simp
        rw [Nat.card_coe_set_eq, fiber_ncard_of_mod_n hred i hi]
        have h6 := hf1 i hi; rw [Nat.card_coe_set_eq] at h6
        have h10 := hf2 (n + i) (by lia) (by lia); rw [Nat.card_coe_set_eq] at h10
        exact Odd.add_even h6 h10
      · intro i hi1 _
        have h6 : ∀ j, ↑(f' j) ≠ i := by
          intro j
          dsimp [f']
          split_ifs with h10
          · lia
          · dsimp; lia
        use 0
        dsimp
        rw [Nat.card_eq_fintype_card, Fintype.card_eq_zero_iff, isEmpty_subtype]
        exact h6
      · intro i hi j
        dsimp only [f']
        split_ifs with h3
        · lia
        · intro h4
          apply_fun (·.val) at h4
          dsimp only at h4
          lia
    ⟨f', mf'⟩

private lemma symmDiff_singleton_card_parity {α : Type} [DecidableEq α]
    (a : α) (s : Finset α) :
    Even s.card ↔ Odd (symmDiff s {a}).card := by
  by_cases ha : a ∈ s
  · have : symmDiff s {a} = s.erase a := by ext x; simp [Finset.mem_symmDiff]; aesop
    rw [this, Finset.card_erase_of_mem ha]
    have := Finset.card_pos.mpr ⟨a, ha⟩
    constructor <;> rintro ⟨k, hk⟩
    · exact ⟨k - 1, by lia⟩
    · exact ⟨k + 1, by lia⟩
  · have : symmDiff s {a} = insert a s := by ext x; simp [Finset.mem_symmDiff]; aesop
    rw [this, Finset.card_insert_of_notMem ha]
    exact ⟨Even.add_one, fun ⟨k, hk⟩ => ⟨k, by lia⟩⟩

lemma even_subsets_card {α : Type} [Fintype α] :
    Fintype.card {s : Finset α // Even (Finset.card s) } = 2^(Fintype.card α - 1) := by
  classical
  obtain h | h := Nat.eq_zero_or_pos (Fintype.card α)
  · have hemp : IsEmpty α := Fintype.card_eq_zero_iff.mp h
    simp only [h, Nat.zero_sub, pow_zero, Fintype.card_eq_one_iff]
    exact ⟨⟨∅, ⟨0, rfl⟩⟩, fun ⟨s, _⟩ => by congr 1; exact Finset.eq_empty_of_isEmpty s⟩
  · obtain ⟨a⟩ : Nonempty α := Fintype.card_pos_iff.mp h
    have hbij : Fintype.card {s : Finset α // Even s.card} =
                Fintype.card {s : Finset α // ¬ Even s.card} := by
      apply Fintype.card_of_bijective (f := fun ⟨s, hs⟩ =>
        ⟨symmDiff s {a}, by rwa [Nat.not_even_iff_odd, ← symmDiff_singleton_card_parity]⟩)
      constructor
      · rintro ⟨s₁, h₁⟩ ⟨s₂, h₂⟩ heq
        simp only [Subtype.mk.injEq] at heq ⊢
        have : symmDiff (symmDiff s₁ {a}) {a} = symmDiff (symmDiff s₂ {a}) {a} := by rw [heq]
        rwa [symmDiff_assoc, symmDiff_self, symmDiff_bot,
             symmDiff_assoc, symmDiff_self, symmDiff_bot] at this
      · rintro ⟨t, ht⟩
        rw [Nat.not_even_iff_odd] at ht
        refine ⟨⟨symmDiff t {a}, ?_⟩, by simp⟩
        rwa [symmDiff_singleton_card_parity, symmDiff_assoc, symmDiff_self, symmDiff_bot]
    have hsum : Fintype.card {s : Finset α // Even s.card} +
                Fintype.card {s : Finset α // ¬ Even s.card} =
                Fintype.card (Finset α) := by
      have := @Fintype.card_subtype_compl (Finset α) _ (fun s => Even s.card) _ _
      have := Fintype.card_subtype_le (fun s : Finset α => Even s.card)
      lia
    rw [Fintype.card_finset] at hsum
    have h1 : 2 ^ Fintype.card α = 2 * 2 ^ (Fintype.card α - 1) := by
      cases hn : Fintype.card α with
      | zero => lia
      | succ m => simp [pow_succ, mul_comm]
    lia

lemma claim (n k : ℕ) (hn : 0 < n) (hnk : n ≤ k) (_he : Even (k - n))
    (f : {b : Sequence n k // MSequence n k b }) :
    Set.ncard {g | ψ n k g = f} = 2^(k - n) := by
  classical
  let c : Fin n → ℕ := fun i ↦ Nat.card { j | f.val j = ⟨i, by lia⟩ }
  have hcp : ∀ i : Fin n, 0 < c i := by
    intro i
    obtain ⟨⟨hN, _⟩, _⟩ := f.property
    have hN' := hN i.val (Fin.is_lt i)
    apply Odd.pos
    convert hN' using 1
    apply congrArg Nat.card
    apply congrArg Subtype
    funext j
    exact propext ⟨fun h => congrArg Fin.val h, fun h => Fin.ext h⟩
  have hM : ∀ j : Fin k, (f.val j).val < n := by
    intro j
    obtain ⟨_, hM⟩ := f.property
    by_contra h; push_neg at h; exact hM (f.val j) h j rfl
  have hc : ∑ i : Fin n, c i = k := by
    obtain ⟨⟨_, _⟩, hMseq⟩ := f.property
    let g : Fin k → Fin n := fun j ↦ ⟨(f.val j).val, hM j⟩
    have hceq : ∀ i : Fin n, c i = Nat.card { j | g j = i } := by
      intro i; apply congrArg Nat.card; apply congrArg Subtype
      funext j; simp only [g, Set.mem_setOf_eq, Fin.ext_iff]
    simp_rw [hceq, Nat.card_eq_fintype_card]
    conv_lhs =>
      arg 2; ext i; rw [show Fintype.card ↑{j | g j = i} = Fintype.card {j // g j = i} from rfl]
    rw [← Fintype.card_sigma, Fintype.card_congr (Equiv.sigmaFiberEquiv g), Fintype.card_fin]
  let S : Type :=
    (i : Fin n) →
      {s : Finset { j : Fin k | f.val j = ⟨i, by lia⟩} // Even (Finset.card s) }

  let selected (cs : S) (i : Fin n) : Set (Fin k) :=
    Subtype.val '' (↑((cs i).1) : Set { j : Fin k | f.val j = ⟨i, by lia⟩ })

  let p : S → {g | ψ n k g = f} :=
    fun cs ↦
       let g1 : Fin k → Fin (2 * n) :=
         fun j ↦
           let y : Fin (2 * n) := f.val j
           let y' : Fin n := ⟨y.val, hM j⟩
           if j ∈ selected cs y' then ⟨y.val + n, by
             have hy : y.val < n := hM j
             lia⟩ else y
       let hg1 : NSequence n k g1 := by
         obtain ⟨⟨hN, _⟩, _⟩ := f.property
         have hsel_subset : ∀ i : Fin n, selected cs i ⊆ {j : Fin k | ↑(f.val j) = (i : ℕ)} := by
           intro i j hj
           rcases hj with ⟨x, hx, rfl⟩
           exact congrArg Fin.val x.2
         have hsel_even : ∀ i : Fin n, Even (Set.ncard (selected cs i)) := by
           intro i
           have : Set.ncard (selected cs i) = ((cs i).1).card := by
             dsimp [selected]
             rw [Set.ncard_image_of_injective _ Subtype.val_injective, Set.ncard_coe_finset]
           rw [this]; exact (cs i).2
         have hhigh : ∀ i : Fin n, {j : Fin k | ↑(g1 j) = n + i} = selected cs i := by
           intro i; ext j; simp only [Set.mem_setOf]
           constructor
           · intro hj
             let y' : Fin n := ⟨(f.val j).val, hM j⟩
             by_cases hmem : j ∈ selected cs y'
             · have hg1v : (g1 j).val = (f.val j).val + n := by simp [g1, y', hmem]
               have : (f.val j).val = i := by lia
               have : y' = i := Fin.ext this
               simpa [this] using hmem
             · have : (f.val j).val = n + ↑i := by simpa [g1, y', hmem] using hj
               exact absurd (this ▸ hM j) (by lia)
           · intro hj
             have hfj : (f.val j).val = i := hsel_subset i hj
             have : (⟨(f.val j).val, hM j⟩ : Fin n) = i := Fin.ext hfj
             have hmem : j ∈ selected cs ⟨(f.val j).val, hM j⟩ := by simpa [this] using hj
             have : (g1 j).val = (f.val j).val + n := by simp [g1, hmem]
             lia
         have hred : ∀ j, (f.val j).val =
             if (g1 j).val < n then (g1 j).val else (g1 j).val - n := by
           intro j; simp only [g1]; split_ifs with hmem <;> simp_all
         refine ⟨?_, ?_⟩
         · intro i hi
           let i' : Fin n := ⟨i, hi⟩
           have hcard := fiber_ncard_of_mod_n (f := g1) (g := f.val) hred i hi
           rw [Nat.card_coe_set_eq, show Set.ncard {j | (g1 j).val = i} =
             Set.ncard {j | (f.val j).val = i} - Set.ncard {j | (g1 j).val = n + i} by lia]
           exact Nat.Odd.sub_even (by lia)
             (by rw [← Nat.card_coe_set_eq]; exact hN i hi)
             (by rw [hhigh i']; exact hsel_even i')
         · intro i hi1 hi2
           let i' : Fin n := ⟨i - n, by lia⟩
           have hi' : n + ↑i' = i := Nat.add_sub_of_le hi1
           rw [show {j : Fin k | ↑(g1 j) = i} = {j | ↑(g1 j) = n + ↑i'} from by
             ext j; simp [hi'], Nat.card_coe_set_eq, hhigh i']
           exact hsel_even i'
       let hgg : ψ n k ⟨g1, hg1⟩ = f := by
         rcases hg1 with ⟨hg1a, hg1b⟩
         apply Subtype.ext; funext j; apply Fin.ext
         simp only [ψ]
         let y' : Fin n := ⟨(f.val j).val, hM j⟩
         by_cases hmem : j ∈ selected cs y'
         · have hg1v : (g1 j).val = (f.val j).val + n := by simp [g1, y', hmem]
           have hnot : ¬ (g1 j).val < n := by lia
           simp [hg1v]
         · simp [g1, y', hmem, hM j]
       ⟨⟨g1, hg1⟩, hgg⟩
  have Scard : Fintype.card S = ∏ i : Fin n, 2 ^ (c i - 1) := by
    unfold S
    rw [Fintype.card_pi]
    apply Fintype.prod_congr
    intro a
    rw [even_subsets_card]
    congr 1; congr 1
    dsimp only [c]
    rw [Nat.card_eq_fintype_card]
  have Scard' : Fintype.card S = 2^(k-n) := by
    rw [Scard]
    have h1 : ∏ i : Fin n, 2 ^ (c i - 1) = 2 ^ (∑ i : Fin n, (c i - 1)) :=
      Finset.prod_pow_eq_pow_sum _ _ _
    rw [h1, pow_right_inj₀ zero_lt_two (by norm_num)]
    suffices ∑ i : Fin n, (c i - 1) + n = k - n + n by lia
    rw [Nat.sub_add_cancel hnk]
    have h2 : n = ∑ i : Fin n, 1 := by simp
    simp_rw [h2]
    rw [←Finset.sum_add_distrib]
    have h3 : ∀ x ∈ Finset.univ (α := Fin n), c x - 1 + 1 = c x := by
      intro x hx
      exact Nat.sub_add_cancel (hcp x)
    rw [Finset.sum_congr rfl h3]
    exact hc
  have h1 : p.Bijective := by
    constructor
    · intro x y hxy
      let toggle : S → Fin k → Fin (2 * n) := fun cs j =>
        if j ∈ selected cs ⟨(f.val j).val, hM j⟩ then
          (⟨(f.val j).val + n, by
            have hy : (f.val j).val < n := hM j
            lia⟩ : Fin (2 * n))
        else f.val j
      have hxy' : toggle x = toggle y := by
        have hxy0 := congrArg (fun z : {g | ψ n k g = f} => (z.1).1) hxy
        simpa [p, toggle] using hxy0
      have hsel_subset : ∀ cs : S, ∀ i : Fin n, selected cs i ⊆ {j : Fin k | ↑(f.val j) = (i : ℕ)} := by
        intro cs i j hj
        rcases hj with ⟨x, hx, rfl⟩
        exact congrArg Fin.val x.2
      have hsel_eq : ∀ i : Fin n, selected x i = selected y i := by
        intro i; ext j; constructor <;> intro hj <;> by_contra hj₂
        · have hfi := hsel_subset x i hj
          have hij : (⟨(f.val j).val, hM j⟩ : Fin n) = i := Fin.ext hfi
          have : (toggle x j).val = (toggle y j).val := congrArg (fun h => (h j).val) hxy'
          simp [toggle, hij, hj, hj₂] at this; lia
        · have hfi := hsel_subset y i hj
          have hij : (⟨(f.val j).val, hM j⟩ : Fin n) = i := Fin.ext hfi
          have : (toggle x j).val = (toggle y j).val := congrArg (fun h => (h j).val) hxy'
          simp [toggle, hij, hj, hj₂] at this; lia
      have hi2n : ∀ i : Fin n, (i : ℕ) < 2 * n := fun i => by lia
      have hmem_selected : ∀ cs : S, ∀ i : Fin n, ∀ ji : {j : Fin k | f.val j = ⟨i, hi2n i⟩},
          ji ∈ (cs i).1 ↔ ji.1 ∈ selected cs i :=
        fun cs i ji => ⟨fun h => ⟨ji, h, rfl⟩, fun ⟨u, hu, huv⟩ => (Subtype.ext huv) ▸ hu⟩
      funext i; apply Subtype.ext; ext ji
      exact (hmem_selected x i ji).trans <|
        (by simpa [hsel_eq i] using (hmem_selected y i ji).symm)
    · rintro ⟨g, hg⟩
      rcases g with ⟨gfun, hgN⟩
      rcases hgN with ⟨hgN1, hgN2⟩
      have hgψ : ψ n k ⟨gfun, ⟨hgN1, hgN2⟩⟩ = f := by
        simpa [Set.mem_setOf] using hg
      have hlow_or_high : ∀ j : Fin k,
          (gfun j).val = (f.val j).val ∨ (gfun j).val = (f.val j).val + n := by
        intro j
        have hEq : ((ψ n k ⟨gfun, ⟨hgN1, hgN2⟩⟩).val j).val = (f.val j).val :=
          congrArg (fun h => ((h.val j).val)) hgψ
        by_cases hlt : (gfun j).val < n
        · left; simpa [ψ, hlt] using hEq
        · right; have : (gfun j).val - n = (f.val j).val := by simpa [ψ, hlt] using hEq
          lia
      have hfi_of_high : ∀ (i : Fin n) (j : Fin k),
          (gfun j).val = n + i → f.val j = ⟨i, by lia⟩ := by
        intro i j hj; apply Fin.ext; dsimp
        rcases hlow_or_high j with hlow | hhigh
        · exfalso; have := hM j; lia
        · lia
      let a : S := fun i ↦
        let s : Finset { j : Fin k | f.val j = ⟨i, by lia⟩ } :=
          Finset.univ.filter (fun ji => (gfun ji.1).val = n + i)
        have hsEven : Even s.card := by
          have hbij : Function.Bijective
              (fun x : {x // x ∈ s} =>
                (⟨x.1.1, (Finset.mem_filter.mp x.2).2⟩ :
                  {j : Fin k // (gfun j).val = n + i})) := by
            constructor
            · intro x y hxy; exact Subtype.ext (Subtype.ext (by simpa using congrArg (·.1) hxy))
            · intro y
              exact ⟨⟨⟨y.1, hfi_of_high i y.1 y.2⟩, by simp [s, y.2]⟩, Subtype.ext rfl⟩
          have : s.card = Nat.card {j : Fin k | (gfun j).val = n + i} := by
            rw [Nat.card_eq_fintype_card, ← show Fintype.card {x // x ∈ s} = s.card from by simp]
            exact Fintype.card_of_bijective hbij
          rw [this]; exact hgN2 (n + i) (by lia) (by lia)
        ⟨s, hsEven⟩
      refine ⟨a, ?_⟩
      have hselA : ∀ (i : Fin n) (j : Fin k), j ∈ selected a i ↔ (gfun j).val = n + i := by
        intro i j
        constructor
        · intro hj
          rcases hj with ⟨ji, hji, rfl⟩
          simpa [a] using hji
        · intro hj
          refine ⟨⟨j, hfi_of_high i j hj⟩, ?_, rfl⟩
          simp [a, hj]
      apply Subtype.ext
      apply Subtype.ext
      funext j
      apply Fin.ext
      let i' : Fin n := ⟨(f.val j).val, hM j⟩
      by_cases hhigh : (gfun j).val = (f.val j).val + n
      · have hmem : j ∈ selected a i' := by
          apply (hselA i' j).2
          simpa [i', Nat.add_comm] using hhigh
        have hpv : (((p a).1).1 j).val = (f.val j).val + n := by
          simp [p, i', hmem]
        simpa [hhigh] using hpv
      · have hmem : ¬ j ∈ selected a i' := by
          intro hm
          have : (gfun j).val = (f.val j).val + n := by
            have hm' := (hselA i' j).1 hm
            simpa [i', Nat.add_comm] using hm'
          exact hhigh this
        have hlow : (gfun j).val = (f.val j).val := by
          rcases hlow_or_high j with hlow | hhigh'
          · exact hlow
          · exact False.elim (hhigh hhigh')
        have hpv : (((p a).1).1 j).val = (f.val j).val := by
          simp [p, i', hmem]
        simpa [hlow] using hpv
  have h2 : Fintype.card S = Fintype.card {g | ψ n k g = f} :=
    Fintype.card_of_bijective h1
  nth_rewrite 2 [←Nat.card_eq_fintype_card] at h2
  rw [Nat.card_coe_set_eq] at h2
  rw [←h2, Scard']

lemma lemma1 (α : Type) (A B : Set α) (hA : A.Finite) (hB : B.Finite)
    (f : {x // A x} → {x // B x})
    (n : Nat) (h1 : ∀ b, Set.ncard { a | f a = b } = n)
    : B.ncard * n = A.ncard := by
  classical
  haveI hfa : Fintype {x // A x} := hA.fintype
  haveI hfb : Fintype {x // B x} := hB.fintype
  haveI : ∀ b, Fintype { a : {x // A x} // f a = b } := fun b =>
    have : Fintype { x // A x } := hfa; setFintype fun x ↦ f x = b
  have h2 : ∀ b, Fintype.card { a : {x // A x} // f a = b } = n := by
    intro b; rw [Fintype.card_eq_nat_card]; exact_mod_cast h1 b
  have key : Fintype.card {x // A x} = Fintype.card {x // B x} * n := by
    conv_lhs => rw [← Fintype.card_congr (Equiv.sigmaFiberEquiv f), Fintype.card_sigma]
    rw [Finset.sum_congr rfl (fun b _ => h2 b), Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq (s := A)]
  change Nat.card {x // B x} * n = Nat.card {x // A x}
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  lia

snip end

determine solution (n k : ℕ) : ℚ := 2 ^ (k - n)

problem imo2008_p5 (n k : ℕ) (hn : 0 < n)
    (hnk : n ≤ k) (he : Even (k - n))
    : Set.ncard (MSequence n k) * solution n k = Set.ncard (NSequence n k) := by
  have hA : Set.Finite { f | NSequence n k f } := Set.toFinite _
  have hB : Set.Finite { f | MSequence n k f } := Set.toFinite _
  have h1 := lemma1 (Sequence n k) (NSequence n k) (MSequence n k) hA hB (ψ n k)
              (2 ^ (k - n))
              (claim n k hn hnk he)
  rw [←h1]
  push_cast
  rfl


end Imo2008P5
