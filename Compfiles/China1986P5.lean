/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: sjfhsjfh
-/
import Mathlib

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# China Mathematical Olympiad 1986, Problem 5

给定序列 1, 1, 2, 2, 3, 3, …, 1986, 1986，能否把这些数重排成一行，使得
两个 1 之间夹着一个数，两个 2 之间夹着两个数，…，两个 1986 之间夹着一千九百八十六个数？
请证明你的结论。

Given a sequence 1, 1, 2, 2, 3, 3, …, 1986, 1986, determine, with proof,
if we can rearrange the sequence so that for any integer 1 ≤ k ≤ 1986
there are exactly k numbers between the two "k"s.
-/

namespace China1986P5

def rawList {n : ℕ} : Fin (2 * n) → ℕ := fun n ↦ n / 2 + 1

snip begin

def isLangford {n : ℕ} (f : Equiv.Perm (Fin (2 * n))) :=
  ∀ k, 1 ≤ k → k ≤ n → ∃ i j : Fin (2 * n),
    (i < j ∧ rawList (f i) = k ∧ rawList (f j) = k ∧ j.val = i.val + (k + 1))

lemma rawListIcc {n : ℕ} (k : Fin (2 * n)) : 1 ≤ rawList k ∧ rawList k ≤ n := by
  simp only [rawList, le_add_iff_nonneg_left, zero_le, Order.add_one_le_iff, true_and]
  omega

lemma mul_two_add_one {n : ℕ} (k : Fin n)
  : 2 * k + 1 < 2 * n := by omega

lemma count_odd (n : ℕ) : ({i | Odd i.val} : Finset (Fin n)).card = n / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
  rewrite [Finset.card_eq_sum_ones, Finset.sum_filter] at ⊢ ih
  rewrite [Fin.sum_univ_eq_sum_range (fun n ↦ if Odd n then 1 else 0)] at ⊢ ih
  rewrite [Finset.sum_range_succ, ih]
  rcases Nat.even_or_odd n with (h | h)
  <;> simp [h, ← Nat.not_even_iff_odd]
  <;> rewrite [← Nat.mul_left_inj Nat.zero_lt_two.ne']
  · rewrite [Nat.add_left_inj.mp <| Nat.div_two_mul_two_add_one_of_odd <| Even.add_one h]
    exact Nat.div_two_mul_two_of_even h
  · rewrite [Nat.div_two_mul_two_of_even <| Odd.add_one h, add_mul, mul_two 1,
      ← add_assoc, Nat.div_two_mul_two_add_one_of_odd h]; rfl

lemma count_odd' (n : ℕ) : ({i | Odd i.val} : Finset (Fin (2 * n))).card = n := by
  rewrite [← Finset.card_fin n, eq_comm]
  refine Finset.card_bij (fun k hk ↦ ⟨2 * k.val + 1, by simp; exact mul_two_add_one k⟩)
    (by
      intro _ _; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact Even.add_one <| even_two_mul _)
    (by simp; exact fun _ _ k ↦ Fin.eq_of_val_eq k)
    (by
      intro b hb; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      obtain ⟨c, hc⟩ := hb; simp only [Finset.card_univ, Finset.mem_univ, exists_const]
      obtain ⟨b, hb⟩ := b; simp only at hc
      simp only [Finset.card_univ, Fintype.card_fin] at hb
      use ⟨c, by omega⟩
      refine Fin.eq_of_val_eq ?_; simp only [hc])

def equiv_of_raw {n : ℕ}
  : Equiv (Fin (2 * n)) (Fin n × Fin 2) := .mk
  (fun (⟨k, hk⟩ : Fin (2 * n)) ↦ ⟨⟨k / 2, by omega⟩, ⟨k % 2, by omega⟩⟩)
  (fun ⟨⟨i, hi⟩, ⟨idx, hidx⟩⟩ ↦ ⟨i * 2 + idx, by omega⟩)
  (by intro ⟨k, hk⟩; simp only [Fin.mk.injEq]; omega)
  (by intro ⟨⟨i, hi⟩, ⟨idx, hidx⟩⟩; simp; omega)

lemma even_raw {n : ℕ} {i : Fin (2 * n)}
  : Even (rawList i) ↔ Odd (equiv_of_raw i).fst.val := by
  simp only [rawList, equiv_of_raw, Equiv.coe_fn_mk, Nat.even_add_one, Nat.not_even_iff_odd]

lemma odd_raw {n : ℕ} {i : Fin (2 * n)}
  : Odd (rawList i) ↔ Even (equiv_of_raw i).fst.val := by
  simp only [rawList, equiv_of_raw, Equiv.coe_fn_mk, Nat.odd_add_one, Nat.not_odd_iff_even]

lemma rawList_eq_fst_add_one {n : ℕ} {k : Fin (2 * n)}
  : rawList k = (equiv_of_raw k).fst + 1:= by
  simp only [rawList, equiv_of_raw, Equiv.coe_fn_mk]

lemma eq_fst_of_eq_raw {n : ℕ} {k1 k2 : Fin (2 * n)}
  (h : rawList k1 = rawList k2)
  : (equiv_of_raw k1).1 = (equiv_of_raw k2).1 := by
  simp only [equiv_of_raw, Equiv.coe_fn_mk, Fin.mk.injEq]
  simpa only [rawList, Nat.add_right_cancel_iff] using h

lemma eq_of_ne_of_ne {α : Type*} {a b c : α × Fin 2}
  (hab : a.fst = b.fst) (hbc : b.fst = c.fst)
  (hab' : a ≠ b) (hbc' : b ≠ c) : a = c := by
  obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b; obtain ⟨c1, c2⟩ := c
  fin_cases a2 <;> fin_cases b2 <;> fin_cases c2 <;> simp_all only [ne_eq]

lemma eq_or_eq_of_ne_of_ne {α : Type*} {a b c d : α × Fin 2}
  (hab : a.fst = b.fst) (hcb : c.fst = b.fst) (hdb : d.fst = b.fst)
  (hab' : a ≠ b) (hcd' : c ≠ d) : a = c ∧ b = d ∨ a = d ∧ b = c := by
  obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b
  obtain ⟨c1, c2⟩ := c; obtain ⟨d1, d2⟩ := d
  fin_cases a2 <;> fin_cases b2 <;> fin_cases c2 <;> fin_cases d2
  <;> simp_all only [ne_eq, not_true, true_and, true_or, or_true]

lemma isLangford_odd_count_even_even {n : ℕ}
  {f : Equiv.Perm (Fin (2 * n))} (h : isLangford f)
  : ({i | Odd i.val ∧ Even (rawList (f i))} : Finset (Fin (2 * n))).card = n / 2 := by
  rewrite [← count_odd n]
  refine Set.BijOn.finsetCard_eq (fun k ↦ (equiv_of_raw (f k)).fst) ⟨?mpst, ?inj, ?surj⟩
  case mpst =>
    simp [Set.MapsTo, equiv_of_raw, rawList, ← Nat.not_even_iff_odd]; intro _ _ h
    exact Nat.even_add_one.mp h
  case inj =>
    simp [Set.InjOn, rawList]; intro k1 hk1o hk1 k2 hk2o hk2 heq
    obtain ⟨hfk2l, hfk2r⟩ := rawListIcc (f k2)
    obtain ⟨i, j, ⟨hij, hrfi2, hrfj2, hijeq⟩⟩ := h (rawList (f k2)) hfk2l hfk2r
    by_contra! h : k1 ≠ k2
    have := eq_or_eq_of_ne_of_ne heq (eq_fst_of_eq_raw hrfi2) (eq_fst_of_eq_raw hrfj2)
      (by simp only [ne_eq, EmbeddingLike.apply_eq_iff_eq, h, not_false_iff])
      (by simp only [ne_eq, EmbeddingLike.apply_eq_iff_eq, hij.ne, not_false_iff])
    simp only [EmbeddingLike.apply_eq_iff_eq] at this
    rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 h2
    · simp only [hijeq, Nat.odd_add, hk1o, true_iff] at hk2o; absurd hk2o
      simp only [rawList, Nat.not_even_iff_odd, hk2, Even.add_one]
    · simp only [hijeq, Nat.odd_add, hk2o, true_iff] at hk1o; absurd hk1o
      simp only [rawList, Nat.not_even_iff_odd, hk2, Even.add_one]
  case surj =>
    simp [Set.SurjOn, equiv_of_raw, rawList]; intro l hl
    simp only [Set.mem_image, Set.mem_setOf] at ⊢ hl
    have hl' : Even (l.val + 1) := Odd.add_one hl
    obtain ⟨i, j, ⟨hij, hrfi2, hrfj2, hijeq⟩⟩ := h (l + 1) (by omega) (by omega)
    by_cases! h : Odd j.val
    · use j; unfold rawList at hrfj2; simp only [h, true_and, hrfj2, hl']
      simp only [Nat.add_right_cancel_iff] at hrfj2; simp only [hrfj2]
    · simp only [hijeq, Nat.odd_add' (m := ↑i), hl,
        Odd.add_one, Even.add_one, true_iff, Nat.not_even_iff_odd] at h
      use i; unfold rawList at hrfi2; simp only [h, true_and, hrfi2, hl']
      simp only [Nat.add_right_cancel_iff] at hrfi2; simp only [hrfi2]

lemma fin_two_eq_zero_or_one (b : Fin 2) : b = 0 ∨ b = 1 := by
  fin_cases b <;> simp

lemma odd_and_even_fst {n : ℕ}
  {f : Equiv.Perm (Fin (2 * n))} (h : isLangford f) (k : Fin (2 * n))
  : Odd k.val ∧ Odd (rawList (f k))
    ↔ Odd (f⁻¹ (equiv_of_raw.symm ⟨(equiv_of_raw (f k)).fst, 0⟩)).val
      ∧ Even ((equiv_of_raw (f k)).fst.val) := by
  simp only [rawList_eq_fst_add_one, Nat.odd_add_one, Nat.not_odd_iff_even]
  simp only [Equiv.Perm.coe_inv, and_congr_left_iff]; intro he
  obtain ⟨hfkl, hfkr⟩ := rawListIcc (f k)
  obtain ⟨i, j, ⟨hij, hrfik, hrfjk, hijeq⟩⟩ := h (rawList (f k)) hfkl hfkr
  simp only [rawList_eq_fst_add_one, Nat.add_right_cancel_iff] at hrfik hrfjk hijeq
  simp only [Fin.val_eq_val] at hrfik hrfjk
  by_cases! hkj : k = j
  · subst hkj; simp only [hijeq, he, Nat.odd_add, Nat.even_add_one, not_not, iff_true]
    by_cases! hsnd : (equiv_of_raw (f i)).snd = 0
    · rewrite [← hsnd, ← hrfik]; simp only [Prod.mk.eta, Equiv.symm_apply_apply]
    by_cases! hsnd' : (equiv_of_raw (f k)).snd = 0
    · rewrite [← hsnd']; simp only [Prod.mk.eta, Equiv.symm_apply_apply]
      rewrite [hijeq, Nat.odd_add]; simp only [Nat.even_add_one, not_not, he, iff_true]
    absurd hij.ne; rewrite [← Equiv.apply_eq_iff_eq f,
      ← Equiv.apply_eq_iff_eq equiv_of_raw, Prod.eq_iff_fst_eq_snd_eq]
    simp [hrfik, fin_two_eq_zero_or_one _ |>.resolve_left, hsnd, hsnd']
  have hik : i = k := by
    simpa only [EmbeddingLike.apply_eq_iff_eq] using eq_of_ne_of_ne
      (Eq.trans hrfik hrfjk.symm) hrfjk (by simp [hij.ne]) (by simp [hkj.symm])
  subst hik
  by_cases! hsnd : (equiv_of_raw (f i)).snd = 0
  · rewrite [← hsnd]; simp only [Prod.mk.eta, Equiv.symm_apply_apply]
  by_cases! hsnd' : (equiv_of_raw (f j)).snd = 0
  · rewrite [← hsnd', ← hrfjk]; simp only [Prod.mk.eta, Equiv.symm_apply_apply]
    rewrite [hijeq, Nat.odd_add]; simp only [Nat.even_add_one, not_not, he, iff_true]
  absurd hij.ne; rewrite [← Equiv.apply_eq_iff_eq f,
    ← Equiv.apply_eq_iff_eq equiv_of_raw, Prod.eq_iff_fst_eq_snd_eq]
  simp [hrfjk, fin_two_eq_zero_or_one _ |>.resolve_left, hsnd, hsnd']

lemma pair_card_even {α : Type*} (p : α → Prop)
  [Fintype (α × Fin 2)] [DecidableEq (α × Fin 2)] [DecidablePred p]
  : Even ({t | p t.fst} : Finset (α × Fin 2)).card := by
  refine Finset.exists_disjoint_union_of_even_card_iff _ |>.mpr ?_
  use ({t | p t.fst ∧ t.snd = 0} : Finset (α × Fin 2))
  use ({t | p t.fst ∧ t.snd = 1} : Finset (α × Fin 2))
  rewrite [← Finset.filter_or, Finset.disjoint_filter]
  simp only [← and_or_left, fin_two_eq_zero_or_one]
  simp only [Finset.mem_univ, true_and, and_true, true_imp_iff]
  refine ⟨?_, ?_⟩
  · intro (a, b); simp only [Fin.isValue, not_and, and_imp]
    intro _ hb _; subst hb; exact Fin.zero_ne_one
  refine Set.BijOn.finsetCard_eq (fun (k, _) ↦ (k, 1)) ⟨?mpst, ?inj, ?surj⟩
  <;> simp [Set.MapsTo, Set.InjOn, Set.SurjOn]
  intro t; simp; intro ht1 ht2; use t.fst; simp only [ht1, true_and]
  rewrite [Prod.eq_iff_fst_eq_snd_eq]; simp only [ht2, true_and]

lemma isLangford_odd_count_odd_even {n : ℕ}
  {f : Equiv.Perm (Fin (2 * n))} (h : isLangford f)
  : Even ({i | Odd i.val ∧ Odd (rawList (f i))} : Finset (Fin (2 * n))).card := by
  simp only [odd_and_even_fst h]
  rewrite [show ({x | Odd (f⁻¹ (equiv_of_raw.symm ((equiv_of_raw (f x)).fst, 0))).val
      ∧ Even (equiv_of_raw (f x)).fst.val} : Finset _).card
    = ({p | Odd (f⁻¹ (equiv_of_raw.symm (p.fst, 0))).val
      ∧ Even p.fst.val } : Finset (Fin n × Fin 2)).card by
    refine Set.BijOn.finsetCard_eq (fun k ↦ (equiv_of_raw (f k))) ⟨?mpst, ?inj, ?surj⟩
    <;> simp [Set.MapsTo, Set.InjOn, Set.SurjOn]
    intro p; simp; intro hp1 hp2; use f.symm (equiv_of_raw.symm p); simp [hp1, hp2]]
  exact pair_card_even fun fst ↦
    Odd (f.symm (equiv_of_raw.symm (fst, 0))).val ∧ Even fst.val

lemma mod_4_of_isLangford {n : ℕ}
  : (∃ f, isLangford (n := n) f) → (n % 4 = 0 ∨ n % 4 = 3) := by
  intro ⟨f, hf⟩
  suffices h : ∃ m, n = n / 2 + 2 * m by
    obtain ⟨m, hm⟩ := h
    have : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
    rcases this with (h | h | h | h)
    <;> obtain ⟨l, hl⟩ := Nat.mod_eq_iff.mp h |>.resolve_left (by norm_num) |>.right
    <;> rewrite [h] <;> rewrite [hl] at hm <;> simp
    <;> rewrite [mul_comm 4 l, show l * 4 = l * 2 * 2 by omega] at hm
    <;> norm_num at hm
    · have : Odd ((l * 2 * 2 + 1) / 2 + 2 * m) := by use l * 2; rw [← hm, mul_comm]
      absurd Nat.not_even_iff_odd.mpr <| Nat.odd_add.mp this |>.mpr <| even_two_mul m
      use l * 2; omega
    · have : Even (l * 2 + 1 + 2 * m) := by rewrite [← hm]; use l * 2 + 1; omega
      absurd this; omega
  obtain ⟨m, hm⟩ := isLangford_odd_count_odd_even hf
  use m; rewrite [two_mul, ← hm, ← isLangford_odd_count_even_even hf]
  nth_rewrite 1 [← count_odd' n]
  have h_disj : Disjoint ({i | Odd i.val ∧ Odd (rawList (f i))} : Finset _)
    ({i | Odd i.val ∧ Even (rawList (f i))} : Finset _) := by
    refine Finset.disjoint_filter.mpr fun i ↦ ?_
    simp only [Finset.mem_univ, not_and, Nat.not_even_iff_odd, and_imp, forall_const]
    exact fun _ x _ ↦ x
  have h_disjUnion : ({i | Odd i.val} : Finset (Fin (2 * n)))
    = ({i | Odd i.val ∧ Odd (rawList (f i))} : Finset (Fin (2 * n))).disjUnion
      ({i | Odd i.val ∧ Even (rawList (f i))} : Finset (Fin (2 * n))) h_disj := by
    rewrite [Finset.disjUnion_eq_union]; ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    refine ⟨?_, ?_⟩
    · intro h; simp [h]; exact Nat.even_or_odd (rawList (f i)) |>.symm
    · intro h; rcases h with (h | h) <;> exact h.left
  rewrite [h_disjUnion, add_comm]
  exact Finset.card_disjUnion _ _ h_disj

snip end

determine answer : Prop := False

problem china1986_p5 : (∃ f : Equiv.Perm (Fin (2 * 1986)),
  ∀ k, 1 ≤ k → k ≤ 1986 → ∃ i j : Fin (2 * 1986),
    (i < j ∧ rawList (f i) = k ∧ rawList (f j) = k ∧ j.val = i.val + (k + 1)))
      = answer := by
  change (∃ f : Equiv.Perm (Fin (2 * 1986)), isLangford f) = False
  rewrite [eq_iff_iff, iff_false]
  refine mt mod_4_of_isLangford ?_
  norm_num

end China1986P5
