/-
Copyright (c) 2025 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Benpigchu
-/
import Mathlib


/-!
# International Mathematical Olympiad 2022, Problem 1

The bank of Oslo issues two types of coin: aluminum (denoted A)
and bronze (denoted B). Marianne has n aluminum coins and n bronze
coins arranged in a row in some arbitrary initial order. A chain
is any subsequence of consecutive coins of the same type. Given a
fixed positive integer k ≤ 2n, Gilberty repeatedly performs the
following operation: he identifies the longest chain containing
the kth coin from the left and moves all the coins in that chain
to the left end of the row. For example, if n = 4 and k = 4, the
process starting from the ordering AABBBABA would be

  AABBBABA → BBBAAABA → AAABBBBA → BBBBAAAA → ⋯.

Find all pairs (n,k) with 1 ≤ k ≤ 2n such that for every initial
ordering, at some moment in the process, the leftmost n coins
will all be of the same type.
-/

open scoped Finset

namespace Imo2022P1

/-- The two types of coins. -/
inductive Coin : Type where
  | A : Coin
  | B : Coin
deriving DecidableEq

/-- A row of coins. -/
abbrev Row (n : ℕ) : Type := Fin (2 * n) → Coin

/-- The property of a row having `n` of each kind of coin. -/
def Row.valid {n : ℕ} (c : Row n) : Prop := #{i | c i = Coin.A} = n

/-- The first coin in the chain containing coin `k` (zero-based). -/
def Row.chainLeft {n : ℕ} (c : Row n) (k : Fin (2 * n)) : Fin (2 * n) :=
  {j ∈ Finset.Iic k | ∀ i, j ≤ i → i ≤ k → c i = c k}.min' ⟨k, by
    simp only [Finset.mem_filter, Finset.mem_Iic, le_refl, true_and]
    rintro i hki hik
    rw [le_antisymm hki hik]⟩

/-- The last coin in the chain containing coin `k` (zero-based). -/
def Row.chainRight {n : ℕ} (c : Row n) (k : Fin (2 * n)) : Fin (2 * n) :=
  {j ∈ Finset.Ici k | ∀ i, k ≤ i → i ≤ j → c i = c k}.max' ⟨k, by
    simp only [Finset.mem_filter, Finset.mem_Ici, le_refl, true_and]
    rintro i hki hik
    rw [le_antisymm hki hik]⟩

/-- Move coins `a` through `b` to the left of the row. -/
def Row.move {n : ℕ} (c : Row n) (a b : Fin (2 * n)) : Row n :=
  fun i ↦ if b < i then c i else c ⟨(((i : ℕ) + (a : ℕ)) % ((b : ℕ) + 1)),
    (Nat.mod_lt _ (by lia)).trans_le (by lia)⟩

/-- The operation moving the chain containing coin `k` (zero-based). -/
def Row.operation {n : ℕ} (k : Fin (2 * n)) (c : Row n) : Row n :=
  c.move (c.chainLeft k) (c.chainRight k)

/-- The operation moving the chain containing coin `k` (one-based). -/
def Row.operationOneBased {n k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ 2 * n) (c : Row n) :
    Row n :=
  c.operation ⟨k - 1, by lia⟩

/-- The property of a row having leftmost `n` coin with the same type. -/
def Row.leftmostNSame {n : ℕ} (c : Row n) := ∀ j₁ j₂ : Fin (2 * n),
  (j₁ : ℕ) < n → (j₂ : ℕ) < n → c j₁ = c j₂

lemma Nat.ceilDiv_two_add_floorDiv_two (n : Nat) : n ⌈/⌉ 2 + n ⌊/⌋ 2 = n := by
  rw [Nat.ceilDiv_eq_add_pred_div, Nat.floorDiv_eq_div]
  lia

def Coin.flip : Coin → Coin
  | A => B
  | B => A

lemma Coin.flip_eq_iff (c c' : Coin) : c.flip = c' ↔ c ≠ c' := by
  cases c <;> cases c' <;> decide

def isValidRow (l : List Coin) := 2 * (l.count Coin.A) = l.length

universe u

lemma List.count_ofFn {α : Type u} [DecidableEq α] {n : ℕ} (f : Fin n → α) (a : α)
  : #{i | f i = a} = List.count a (List.ofFn f) := by
    induction' n with n h
    · rw [List.ofFn_zero, List.count_nil]
      rw [Finset.card_eq_zero]
      apply Finset.eq_empty_of_isEmpty
    · rw [List.ofFn_succ, List.count_cons, ← h]
      rw [← Finset.card_filter_add_card_filter_not (fun i ↦ i ≠ 0)]
      rw [Finset.filter_filter, Finset.filter_filter]
      congr 1
      · have h : ({i | f i = a ∧ i ≠ 0} : Finset _) = Finset.image Fin.succ {i | f i.succ = a} := by
          ext x
          simp
          constructor
          · rintro ⟨hxa, hx⟩
            rcases Fin.exists_succ_eq_of_ne_zero hx with ⟨x', hxx'⟩
            use x'
            rw [hxx', hxa]
            constructor <;> rfl
          · rintro ⟨x', hxa, hx⟩
            rw [← hx, and_iff_right hxa]
            apply Fin.succ_ne_zero
        rw [h]
        apply Finset.card_image_of_injective
        apply Fin.succ_injective
      · by_cases! h' : f 0 = a
        · rw [beq_of_eq h', if_pos rfl, Finset.card_eq_one]
          use 0
          rw [Finset.eq_singleton_iff_unique_mem]
          simp
          exact h'
        · rw [beq_false_of_ne h', if_neg Bool.false_ne_true, Finset.card_eq_zero]
          rw [Finset.eq_empty_iff_forall_notMem]
          intro i
          simp
          intro hi
          contrapose h'
          rw [h'] at hi
          exact hi

lemma List.sum_rotate {α : Type u} [AddCommMonoid α] (l : List α) {n : ℕ} : (l.rotate n).sum = l.sum := by
  apply List.Perm.sum_eq
  apply List.rotate_perm

lemma List.splitBy_append' {α : Type u} {r : α → α → Bool} {a b : List α} (hab : ∃ x ∈ a.getLast?, ∃ y ∈ b.head?, r x y = true)
  : List.splitBy r (a ++ b) = (List.splitBy r a).dropLast ++ [(List.splitBy r a).getLast?.getD [] ++ (List.splitBy r b).head?.getD []] ++ (List.splitBy r b).tail := by
    rcases hab with ⟨p, hp, q, hq, hpq⟩
    have ha : a ≠ [] := by
      contrapose! hp
      rw [hp, List.getLast?_nil]
      apply Option.not_mem_none
    have hb : b ≠ [] := by
      contrapose! hq
      rw [hq, List.head?_nil]
      apply Option.not_mem_none
    rw [Option.mem_def, ← List.getLast_eq_iff_getLast?_eq_some ha] at hp
    rw [Option.mem_def, ← List.head_eq_iff_head?_eq_some hb] at hq
    have ha' : (List.splitBy r a) ≠ [] := by
      rw [List.splitBy_eq_nil.ne]
      exact ha
    have hb' : (List.splitBy r b) ≠ [] := by
      rw [List.splitBy_eq_nil.ne]
      exact hb
    rw [List.getLast?_eq_some_getLast ha', Option.getD_some]
    rw [List.head?_eq_some_head hb', Option.getD_some]
    rw [List.splitBy_eq_iff]
    constructorm* _ ∧ _
    · rw [List.flatten_append, List.flatten_append, List.flatten_singleton]
      rw [← @List.flatten_singleton _ ((List.splitBy r a).getLast ha')]
      rw [← @List.flatten_singleton _ ((List.splitBy r b).head hb')]
      rw [← List.flatten_append, ← List.flatten_append, ← List.flatten_append]
      rw [← List.append_assoc, List.append_assoc]
      rw [List.dropLast_concat_getLast, List.singleton_append, List.cons_head_tail]
      rw [List.flatten_append, List.flatten_splitBy, List.flatten_splitBy]
    · rw [List.mem_append, List.mem_append, List.mem_singleton]
      push_neg
      constructorm* _ ∧ _
      · have h := List.nil_notMem_splitBy r a
        contrapose! h
        apply List.mem_of_mem_dropLast h
      · symm
        apply List.append_ne_nil_of_left_ne_nil
        have h := List.nil_notMem_splitBy r a
        contrapose! h
        rw [← h]
        apply List.getLast_mem
      · have h := List.nil_notMem_splitBy r b
        contrapose! h
        apply List.mem_of_mem_tail h
    · intro l hl
      rw [List.mem_append, List.mem_append, List.mem_singleton] at hl
      casesm* _ ∨ _
      · apply @List.isChain_of_mem_splitBy _ _ r a
        apply List.mem_of_mem_dropLast hl
      · rw [hl, List.isChain_append]
        constructorm* _ ∧ _
        · apply @List.isChain_of_mem_splitBy _ _ r a
          apply List.getLast_mem
        · apply @List.isChain_of_mem_splitBy _ _ r b
          apply List.head_mem
        · intro p' hp' q' hq'
          have ha'' : (List.splitBy r a).getLast ha' ≠ [] := by
            contrapose! hp'
            rw [hp', List.getLast?_nil]
            apply Option.not_mem_none
          have hb'' : (List.splitBy r b).head hb' ≠ [] := by
            contrapose! hq'
            rw [hq', List.head?_nil]
            apply Option.not_mem_none
          rw [Option.mem_def, ← List.getLast_eq_iff_getLast?_eq_some ha''] at hp'
          rw [Option.mem_def, ← List.head_eq_iff_head?_eq_some hb''] at hq'
          rw [List.getLast_getLast_eq_getLast_flatten] at hp'
          rw [List.head_head_eq_head_flatten] at hq'
          simp only [List.flatten_splitBy] at hp' hq'
          rw [← hp', ← hq', hp, hq]
          exact hpq
      · apply @List.isChain_of_mem_splitBy _ _ r b
        apply List.mem_of_mem_tail hl
    · rw [List.isChain_append, List.isChain_append]
      constructorm* _ ∧ _
      · apply List.IsChain.dropLast
        apply List.isChain_getLast_head_splitBy
      · apply List.isChain_singleton
      · have h := List.isChain_getLast_head_splitBy r a
        rw [← List.dropLast_append_getLast ha', List.isChain_append] at h
        intro x hx y hy
        have hy' : (List.splitBy r a).getLast ha' ∈ [(List.splitBy r a).getLast ha'].head? := by
          rw [List.head?_singleton, Option.mem_some]
        have h' := h.right.right x hx ((List.splitBy r a).getLast ha') hy'
        rw [List.head?_singleton, Option.mem_some] at hy
        rcases h' with ⟨h'x, h'y', h'xy'⟩
        use h'x
        have h'y : y ≠ [] := by
          rw [← hy]
          apply List.append_ne_nil_of_left_ne_nil
          exact h'y'
        use h'y
        have h_eq : ((List.splitBy r a).getLast ha').head h'y' = y.head h'y := by
          simp only [← hy]
          rw [List.head_append_left h'y']
        rw [h_eq] at h'xy'
        exact h'xy'
      · apply List.IsChain.tail
        apply List.isChain_getLast_head_splitBy
      · have h := List.isChain_getLast_head_splitBy r b
        rw [← List.cons_head_tail hb', List.isChain_cons] at h
        intro x hx y hy
        have h' := h.left y hy
        rw [List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.mem_some] at hx
        rcases h' with ⟨h'x', h'y, h'x'y⟩
        have h'x : x ≠ [] := by
          rw [← hx]
          apply List.append_ne_nil_of_right_ne_nil
          exact h'x'
        use h'x
        use h'y
        have h_eq : ((List.splitBy r b).head hb').getLast h'x' = x.getLast h'x := by
          simp only [← hx]
          rw [List.getLast_append_right h'x']
        rw [h_eq] at h'x'y
        exact h'x'y

lemma Row.valid_iff_isValidRow_ofFn {n : ℕ}  (c : Row n)
  : c.valid ↔ isValidRow (List.ofFn c) := by
    rw [Row.valid, isValidRow, List.length_ofFn, mul_eq_mul_left_iff, or_iff_left (by norm_num)]
    rw [List.count_ofFn]

def List.chainLeft {α : Type u} [DecidableEq α] (l : List α) (k : Fin l.length) : Fin l.length :=
  {j ∈ Finset.Iic k | ∀ i, j ≤ i → i ≤ k → l.get i = l.get k}.min' ⟨k, by
    simp only [Finset.mem_filter, Finset.mem_Iic, le_refl, true_and]
    rintro i hki hik
    rw [le_antisymm hki hik]⟩

lemma Row.chainLeft_eq_chainLeft_ofFn {n : ℕ} (c : Row n) (k : Fin (2 * n))
  : c.chainLeft k = (Fin.cast (by rw [List.length_ofFn]) (List.chainLeft (List.ofFn c) (Fin.cast (by rw [List.length_ofFn]) k))) := by
    have h_cast : (List.ofFn c).length = 2 * n := by rw [List.length_ofFn]
    rw [Row.chainLeft, List.chainLeft]
    set f := Fin.cast h_cast with hf
    have hf' : Monotone f := by
      rw [hf]
      apply StrictMono.monotone
      apply Fin.cast_strictMono
    rw [← Finset.min'_image hf' _ (by
      rw [Finset.image_nonempty]
      use Fin.cast (by rw [List.length_ofFn]) k
      simp only [Finset.mem_filter, Finset.mem_Iic, le_refl, true_and]
      rintro i hki hik
      rw [le_antisymm hki hik])]
    congr
    ext j
    simp
    constructor
    · rintro ⟨hjk, hjk'⟩
      use Fin.cast h_cast.symm j
      constructorm* _ ∧ _
      · rw [Fin.cast_le_cast]
        exact hjk
      · intro i hi hi'
        rw [← Fin.leftInverse_cast h_cast i, Fin.cast_le_cast] at hi hi'
        have hi'' := hjk' (Fin.cast h_cast i) hi hi'
        rw [← hi'']
        rfl
      · rw [hf, Fin.cast_cast, Fin.cast_eq_self]
    · rintro ⟨j', ⟨hj', hjk⟩, hjk'⟩
      rw [← hjk', hf]
      constructor
      · rw [← Fin.rightInverse_cast h_cast k, Fin.cast_le_cast]
        exact hj'
      · intro i hi hi'
        rw [← Fin.rightInverse_cast h_cast i, Fin.cast_le_cast] at hi
        rw [← Fin.rightInverse_cast h_cast i, ← Fin.rightInverse_cast h_cast k, Fin.cast_le_cast] at hi'
        have hi'' := hjk (Fin.cast h_cast.symm i) hi hi'
        rw [← hi'']
        rfl

lemma List.chainLeft_le {α : Type u} [DecidableEq α] (l : List α) (k : Fin l.length)
  : List.chainLeft l k ≤ k := by
    rw [List.chainLeft]
    apply Finset.min'_le
    simp only [Finset.mem_filter, Finset.mem_Iic, le_refl, true_and]
    rintro i hki hik
    rw [le_antisymm hki hik]

def List.chainRight {α : Type u} [DecidableEq α] (l : List α) (k : Fin l.length) : Fin l.length :=
  {j ∈ Finset.Ici k | ∀ i, k ≤ i → i ≤ j → l.get i = l.get k}.max' ⟨k, by
    simp only [Finset.mem_filter, Finset.mem_Ici, le_refl, true_and]
    rintro i hki hik
    rw [le_antisymm hki hik]⟩

lemma Row.chainRight_eq_chainRight_ofFn {n : ℕ} (c : Row n) (k : Fin (2 * n))
  : c.chainRight k = (Fin.cast (by rw [List.length_ofFn]) (List.chainRight (List.ofFn c) (Fin.cast (by rw [List.length_ofFn]) k))) := by
    have h_cast : (List.ofFn c).length = 2 * n := by rw [List.length_ofFn]
    rw [Row.chainRight, List.chainRight]
    set f := Fin.cast h_cast with hf
    have hf' : Monotone f := by
      rw [hf]
      apply StrictMono.monotone
      apply Fin.cast_strictMono
    rw [← Finset.max'_image hf' _ (by
      rw [Finset.image_nonempty]
      use Fin.cast (by rw [List.length_ofFn]) k
      simp only [Finset.mem_filter, Finset.mem_Ici, le_refl, true_and]
      rintro i hki hik
      rw [le_antisymm hki hik])]
    congr
    ext j
    simp
    constructor
    · rintro ⟨hjk, hjk'⟩
      use Fin.cast h_cast.symm j
      constructorm* _ ∧ _
      · rw [Fin.cast_le_cast]
        exact hjk
      · intro i hi hi'
        rw [← Fin.leftInverse_cast h_cast i, Fin.cast_le_cast] at hi hi'
        have hi'' := hjk' (Fin.cast h_cast i) hi hi'
        rw [← hi'']
        rfl
      · rw [hf, Fin.cast_cast, Fin.cast_eq_self]
    · rintro ⟨j', ⟨hj', hjk⟩, hjk'⟩
      rw [← hjk', hf]
      constructor
      · rw [← Fin.rightInverse_cast h_cast k, Fin.cast_le_cast]
        exact hj'
      · intro i hi hi'
        rw [← Fin.rightInverse_cast h_cast i, Fin.cast_le_cast] at hi'
        rw [← Fin.rightInverse_cast h_cast i, ← Fin.rightInverse_cast h_cast k, Fin.cast_le_cast] at hi
        have hi'' := hjk (Fin.cast h_cast.symm i) hi hi'
        rw [← hi'']
        rfl

lemma List.le_chainRight {α : Type u} [DecidableEq α] (l : List α) (k : Fin l.length)
  : k ≤ List.chainRight l k := by
    rw [List.chainRight]
    apply Finset.le_max'
    simp only [Finset.mem_filter, Finset.mem_Ici, le_refl, true_and]
    rintro i hki hik
    rw [le_antisymm hki hik]

lemma List.chainLeft_le_chainRight {α : Type u} [DecidableEq α] (l : List α) (k : Fin l.length)
  : List.chainLeft l k ≤ List.chainRight l k := by
    apply le_trans (List.chainLeft_le l k) (List.le_chainRight l k)

def List.move {α : Type u} (a b : ℕ): List α → List α
  := fun l ↦ (l.drop a).take (b + 1 - a) ++ l.take a ++ l.drop (b + 1)

lemma List.length_move {α : Type u} {a b : ℕ} (hab : a ≤ b) (l : List α)
  : (List.move a b l).length = l.length := by
  rw [List.move, List.length_append, List.length_append]
  nth_rw 4 [← List.take_append_drop a l]
  rw [List.length_append]
  nth_rw 2 [← List.take_append_drop (b + 1 - a) (List.drop a l)]
  rw [List.length_append, List.drop_drop]
  have h : (a + (b + 1 - a)) = b + 1 := by
    apply Nat.add_sub_cancel'
    lia
  rw [h]
  abel

lemma List.count_move {α : Type u} [DecidableEq α] {a b : ℕ} (hab : a ≤ b) (l : List α) (x : α)
  : (List.move a b l).count x = l.count x := by
  rw [List.move, List.count_append, List.count_append]
  nth_rw 4 [← List.take_append_drop a l]
  rw [List.count_append]
  nth_rw 2 [← List.take_append_drop (b + 1 - a) (List.drop a l)]
  rw [List.count_append, List.drop_drop]
  have h : (a + (b + 1 - a)) = b + 1 := by
    apply Nat.add_sub_cancel'
    lia
  rw [h]
  abel

lemma Row.ofFn_move_eq_move_ofFn {n : ℕ} (c : Row n) {a b : Fin (2 * n)} (hab : a ≤ b)
  : List.ofFn (c.move a b) = List.move a b (List.ofFn c) := by
    rw [← List.ofFn_get (List.move a b (List.ofFn c))]
    have h_cast : (List.move a b (List.ofFn c)).length = 2 * n := by
      rw [List.length_move hab, List.length_ofFn]
    rw [List.ofFn_congr h_cast]
    rw [List.ofFn_inj]
    ext i
    simp only [Row.move, List.move]
    have hi := Fin.is_lt i
    have ha := Fin.is_lt a
    have hb := Fin.is_lt b
    rw [List.get_eq_getElem?]
    symm
    rw [Option.get_of_eq_some]
    rw [Fin.getElem?_fin, Fin.val_cast]
    rw [List.getElem?_append, List.getElem?_append]
    rw [List.length_append]
    have h₁ : (List.take (↑a) (List.ofFn c)).length = ↑a := by
      apply List.length_take_of_le
      rw [List.length_ofFn]
      lia
    have h₂ : (List.take (↑b + 1 - ↑a) (List.drop (↑a) (List.ofFn c))).length = ↑b + 1 - ↑a := by
      apply List.length_take_of_le
      rw [List.length_drop, List.length_ofFn]
      lia
    rw [h₁, h₂]
    by_cases hbi : b.val < i.val
    · rw [if_pos (Fin.lt_def.mpr hbi)]
      rw [if_neg (by lia : ¬↑i < ↑b + 1 - ↑a + ↑a)]
      rw [List.getElem?_drop, (by lia : ↑b + 1 + (↑i - (↑b + 1 - ↑a + ↑a)) = ↑i)]
      rw [List.getElem?_ofFn, dif_pos hi]
    · rw [if_neg (Fin.lt_def.not.mpr hbi)]
      rw [if_pos (by lia : ↑i < ↑b + 1 - ↑a + ↑a)]
      by_cases hbai : i.val < b.val + 1 - a.val
      · rw [if_pos hbai]
        rw [List.getElem?_take, if_pos hbai]
        rw [List.getElem?_drop, List.getElem?_ofFn]
        rw [dif_pos (by lia : ↑a + ↑i < 2 * n)]
        congr
        rw [add_comm]
        symm
        rw [Nat.mod_eq_of_lt (by lia)]
      · rw [if_neg hbai]
        rw [List.getElem?_take, if_pos (by lia : ↑i - (↑b + 1 - ↑a) < ↑a)]
        rw [List.getElem?_ofFn, dif_pos (by lia : ↑i - (↑b + 1 - ↑a) < 2 * n)]
        congr
        rw [Nat.mod_eq_sub_mod (by lia), Nat.mod_eq_of_lt (by lia)]
        lia

def List.operation {α : Type u} [DecidableEq α] (l : List α) (k : Fin l.length) : List α :=
  List.move (List.chainLeft l k) (List.chainRight l k) l

lemma Row.ofFn_operation_eq_operation_ofFn {n : ℕ} (k : Fin (2 * n)) (c : Row n)
  : List.ofFn (c.operation k) = List.operation (List.ofFn c) (Fin.cast (by rw [List.length_ofFn]) k) := by
    have h : c.chainLeft k ≤ c.chainRight k := by
      rw [Row.chainLeft_eq_chainLeft_ofFn, Row.chainRight_eq_chainRight_ofFn]
      rw [Fin.cast_le_cast]
      apply List.chainLeft_le_chainRight
    rw [List.operation, Row.operation, Row.ofFn_move_eq_move_ofFn c h]
    rw [Row.chainLeft_eq_chainLeft_ofFn, Row.chainRight_eq_chainRight_ofFn]
    rfl

def List.operationOneBased {α : Type u} [DecidableEq α] (l : List α) {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ l.length):
    List α :=
  List.operation l ⟨k - 1, by lia⟩

lemma Row.ofFn_operationOneBased_eq_operationOneBased_ofFn {n k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ 2 * n) (c : Row n)
  : List.ofFn (c.operationOneBased hk1 hkn) = List.operationOneBased (List.ofFn c) hk1 (by
    rw [List.length_ofFn]
    exact hkn
  ) := by
    rw [List.operationOneBased, Row.operationOneBased, Row.ofFn_operation_eq_operation_ofFn]
    rfl

lemma Row.operationOneBased_valid  {n k: ℕ} {c : Row n} (hc : c.valid) (hk1 : 1 ≤ k) (hkn : k ≤ 2 * n)
  : (Row.operationOneBased hk1 hkn c).valid := by
    rw [Row.valid_iff_isValidRow_ofFn, Row.ofFn_operationOneBased_eq_operationOneBased_ofFn]
    rw [List.operationOneBased, List.operation, isValidRow, List.length_move (List.chainLeft_le_chainRight _ _)]
    rw [List.count_move (List.chainLeft_le_chainRight _ _)]
    rw [Row.valid_iff_isValidRow_ofFn, isValidRow] at hc
    exact hc

lemma Row.operationOneBased_iterate_valid  {n k: ℕ} {c : Row n} (hc : c.valid) (hk1 : 1 ≤ k) (hkn : k ≤ 2 * n) (i : ℕ)
  : ((Row.operationOneBased hk1 hkn)^[i] c).valid := by
    apply Function.Iterate.rec
    · exact hc
    · intro a ha
      apply Row.operationOneBased_valid ha

lemma Row.leftmostNSame_iff_of_valid {n : ℕ} {c : Row n} (hc : c.valid):
  c.leftmostNSame ↔ ∃ coin : Coin , ∀ i, c i = coin ↔ i < n := by
    rw [Row.leftmostNSame]
    constructor
    · intro h
      by_cases! hn : n ≠ 0
      · have : NeZero (2 * n) := ⟨by positivity⟩
        use c 0
        rw [Row.valid] at hc
        have hA := @Finset.card_filter_add_card_filter_not _ Finset.univ (fun i ↦ c i = Coin.A) _ _
        rw [Finset.card_fin, hc] at hA
        simp only [two_mul] at hA
        rw [Nat.add_right_inj] at hA
        have hB : #{i | c i = Coin.B} = n := by
          simp only [← hA]
          congr
          ext i
          rw [← ne_eq, ne_comm, ← Coin.flip_eq_iff, Coin.flip, eq_comm]
        have h' : ({i | c i = c 0} : Finset _) = (Finset.Iio (⟨n, by lia⟩)) := by
          apply Finset.eq_of_superset_of_card_ge
          · intro i hi
            simp at hi ⊢
            apply h _ _ hi (by lia)
          · apply le_of_eq
            rw [Fin.card_Iio, Fin.val_mk]
            by_cases! h' : c 0 = Coin.A
            · rw [h']
              exact hc
            · symm at h'
              rw [← Coin.flip_eq_iff, Coin.flip] at h'
              rw [← h']
              exact hB
        rw [← Finset.filter_gt_eq_Iio, Finset.filter_inj'] at h'
        intro i
        rw [h' (Finset.mem_univ i), Fin.lt_def]
      · use Coin.A
        intro i
        rw [hn, mul_zero] at i
        apply Fin.elim0
        exact i
    · rintro ⟨coin, h⟩ j₁ j₂ hj₁ hj₂
      rw [← h] at hj₁ hj₂
      rw [hj₁, hj₂]

def List.segments {α : Type u} [DecidableEq α] : List α → List (List α)
  := fun l ↦ (l.splitBy (· == ·))

lemma List.exists_replicate_of_isChain_beq {α : Type u} [DecidableEq α] {l : List α}
  (hl : List.IsChain (fun x y ↦ (x == y) = true) l) (hl' : l ≠ [])
  : ∃ n : ℕ, ∃ i : α, l = List.replicate n i := by
    induction' l with a as h
    · contrapose! hl'
      rfl
    · by_cases! has : as = []
      · rw [has]
        use 1
        use a
        rw [List.replicate_one]
      · rw [List.isChain_cons] at hl
        rcases h hl.right has with ⟨n, i, hni⟩
        use n + 1
        use a
        have hn : ¬n = 0  := by
          contrapose! has
          rw [hni, has, List.replicate_zero]
        have hi' : i ∈ as.head? := by
          rw [hni]
          rw [List.head?_replicate, if_neg hn]
          apply Option.mem_some_self
        have has' := hl.left i hi'
        rw [beq_iff_eq] at has'
        rw [← has'] at hni
        rw [List.replicate_succ, hni]

lemma segments_getElem?_map_eq (l : List Coin) (i : ℕ) (hi : i < (List.segments l).length)
  : ((List.segments l)[i]?.bind fun x ↦ x.head?) = Option.map (fun x ↦ if Even i then x else x.flip) l.head? := by
    by_cases! hl : l = []
    · rw [hl, List.segments, List.splitBy_nil, List.getElem?_nil, List.head?_nil]
      rw [Option.map_none, Option.bind_none]
    · rw [List.head?_eq_some_head hl, Option.map_some, List.segments]
      have h_mem := List.nil_notMem_splitBy (fun x1 x2 ↦ x1 == x2) l
      induction' i with i h
      · rw [← List.head?_eq_getElem?, if_pos Even.zero]
        have h : (List.splitBy (fun x1 x2 ↦ x1 == x2) l) ≠ [] := by
          rw [List.splitBy_eq_nil.ne]
          exact hl
        have h' : ((List.splitBy (fun x1 x2 ↦ x1 == x2) l).head h) ≠ [] := by
          contrapose! h_mem
          rw [← h_mem]
          apply List.head_mem
        rw [List.head?_eq_some_head h, Option.bind_some, List.head?_eq_some_head h']
        have h'' : (List.splitBy (fun x1 x2 ↦ x1 == x2) l).flatten ≠ [] := by
          rw [List.flatten_splitBy]
          exact hl
        rw [Option.some_inj, ← List.head_flatten_eq_head_head h'']
        congr
        apply List.flatten_splitBy
      · have hi' : i < (List.segments l).length := by
          lia
        have h' := h hi'
        have h_chain := List.isChain_getLast_head_splitBy (fun x1 x2 ↦ x1 == x2) l
        rw [List.isChain_iff_getElem] at h_chain
        rw [List.segments] at hi hi'
        rcases h_chain i hi with ⟨h_l, h_r, h''⟩
        rw [List.getElem?_eq_getElem hi]
        rw [List.getElem?_eq_getElem (by lia)] at h'
        rw [Option.bind_some] at h' ⊢
        rw [beq_eq_false_iff_ne] at h''
        have h_repl := List.exists_replicate_of_isChain_beq (List.isChain_of_mem_splitBy (List.getElem_mem hi')) h_l
        have h_repr := List.exists_replicate_of_isChain_beq (List.isChain_of_mem_splitBy (List.getElem_mem hi)) h_r
        rcases h_repl with ⟨nl, il, hnil⟩
        rcases h_repr with ⟨nr, ir, hnir⟩
        simp only [hnir] at ⊢ h''
        simp only [hnil] at h' h''
        rw [List.getLast_replicate, List.head_replicate, ← Coin.flip_eq_iff] at h''
        rw [hnil, (List.replicate_eq_nil_iff il).ne] at h_l
        rw [hnir, (List.replicate_eq_nil_iff ir).ne] at h_r
        rw [List.head?_replicate] at ⊢ h'
        rw [if_neg h_r]
        rw [if_neg h_l] at h'
        rw [Option.some_inj] at ⊢ h'
        rw [← h'', h']
        by_cases! hi' : Even i
        · rw [if_pos hi']
          have hi'' : ¬Even (i + 1) := by
            rw [Nat.even_add_one, not_not]
            exact hi'
          rw [if_neg hi'']
        · rw [if_neg hi']
          have hi'' : Even (i + 1) := by
            rw [Nat.even_add_one]
            exact hi'
          rw [if_pos hi'']
          rw [Coin.flip_eq_iff, ne_eq, Coin.flip_eq_iff, ne_eq, not_not]

def List.blocks {α : Type u} [DecidableEq α] : List α → List ℕ
  := fun l ↦ (List.segments l).map List.length

lemma List.isChain_beq_replicate {α : Type u} [DecidableEq α] (n : ℕ) (i : α)
  : List.IsChain (fun x y ↦ (x == y) = true) (List.replicate n i) := by
    apply List.isChain_replicate_of_rel
    apply beq_self_eq_true

lemma List.sum_blocks {α : Type u} [DecidableEq α] (l : List α)
  : List.sum (List.blocks l) = l.length := by
    rw [List.blocks, List.segments, ← List.length_flatten, List.flatten_splitBy]

lemma List.zero_lt_of_mem_blocks {α : Type u} [DecidableEq α] (l : List α) (x : ℕ) (h : x ∈ List.blocks l)
  : 0 < x := by
  rw [List.blocks, List.mem_map] at h
  rcases h with ⟨l', hl', hl'x⟩
  apply List.ne_nil_of_mem_splitBy at hl'
  contrapose! hl'
  rw [Nat.le_zero] at hl'
  rw [hl', List.length_eq_zero_iff] at hl'x
  exact hl'x

lemma blocks_semi_inj_helper {a b: List (List Coin)}
  (hab : a.map List.length = b.map List.length)
  (hab' : (a.head?.bind fun l' ↦ l'.head?) = (b.head?.bind fun l' ↦ l'.head?))
  (ha₁ : [] ∉ a) (hb₁ : [] ∉ b)
  (ha₂ : ∀ l ∈ a, List.IsChain (fun x y ↦ (x == y) = true) l)
  (hb₂ : ∀ l ∈ b, List.IsChain (fun x y ↦ (x == y) = true) l)
  (ha₃ : List.IsChain (fun x y ↦ ∃ (hx : x ≠ []) (hy : y ≠ []), (x.getLast hx == y.head hy) = false) a)
  (hb₃ : List.IsChain (fun x y ↦ ∃ (hx : x ≠ []) (hy : y ≠ []), (x.getLast hx == y.head hy) = false) b)
  : a = b := by
    induction' a with m ms h generalizing b
    · rw [List.map_nil] at hab
      symm at hab
      rw [List.map_eq_nil_iff] at hab
      rw [hab]
    · have hb : b ≠ [] := by
        intro hb'
        rw [hb'] at hab
        rw [List.map_nil, List.map_eq_nil_iff] at hab
        contrapose! hab
        apply List.cons_ne_nil
      rcases List.exists_cons_of_ne_nil hb with ⟨n, ns, hbn⟩
      rw [hbn] at hb₁ hb₂ hb₃ hab hab' ⊢
      rw [List.head?_cons, List.head?_cons, Option.bind_some, Option.bind_some] at hab'
      rw [List.mem_cons, not_or, ← ne_eq] at ha₁ hb₁
      have hm := List.exists_replicate_of_isChain_beq (ha₂ m (List.mem_cons_self)) ha₁.left.symm
      have hn := List.exists_replicate_of_isChain_beq (hb₂ n (List.mem_cons_self)) hb₁.left.symm
      rcases hm with ⟨p, s, hmps⟩
      rcases hn with ⟨q, t, hnqt⟩
      have hp : ¬p = 0 := by
        contrapose! +distrib ha₁
        left
        rw [hmps, ha₁, List.replicate_zero]
      have hq : ¬q = 0 := by
        contrapose! +distrib hb₁
        left
        rw [hnqt, hb₁, List.replicate_zero]
      have h₁ : s = t := by
        rw [hmps, hnqt, List.head?_replicate, List.head?_replicate] at hab'
        rw [if_neg hp, if_neg hq, Option.some_inj] at hab'
        exact hab'
      rw [List.map_cons, List.map_cons, List.cons_eq_cons] at hab
      have h₂ : p = q := by
        apply And.left at hab
        rw [hmps, hnqt, List.length_replicate, List.length_replicate] at hab
        exact hab
      have h₃ : m = n := by
        rw [hmps, hnqt, h₁, h₂]
      rw [List.isChain_cons] at ha₃ hb₃
      have hmsns' : ms = [] ↔ ns = [] := by
        apply And.right at hab
        constructor <;> intro h' <;> rw [h', List.map_nil] at hab
        · symm at hab
          rw [List.map_eq_nil_iff] at hab
          exact hab
        · rw [List.map_eq_nil_iff] at hab
          exact hab
      have hms' : ∀ {h' : ms ≠ []}, (ms.head h').head? = s.flip := by
        intro h'
        rcases ha₃.left (ms.head h') (List.head_mem_head? h') with ⟨hm', hms'', h''⟩
        rw [beq_eq_false_iff_ne, ← Coin.flip_eq_iff] at h''
        simp only [hmps] at h''
        rw [List.getLast_replicate] at h''
        symm at h''
        rw [List.head_eq_iff_head?_eq_some] at h''
        exact h''
      have hns' : ∀ {h' : ns ≠ []}, (ns.head h').head? = t.flip := by
        intro h'
        rcases hb₃.left (ns.head h') (List.head_mem_head? h') with ⟨hn', hns'', h''⟩
        rw [beq_eq_false_iff_ne, ← Coin.flip_eq_iff] at h''
        simp only [hnqt] at h''
        rw [List.getLast_replicate] at h''
        symm at h''
        rw [List.head_eq_iff_head?_eq_some] at h''
        exact h''
      have hmsns : (ms.head?.bind fun l' ↦ l'.head?) = (ns.head?.bind fun l' ↦ l'.head?) := by
        by_cases! h' : ms = []
        · rw [h']
          rw [hmsns'] at h'
          rw [h']
        · rw [List.head?_eq_some_head h', List.head?_eq_some_head (hmsns'.ne.mp h')]
          rw [Option.bind_some, Option.bind_some]
          rw [hms', hns', h₁]
      have hms : ∀ l ∈ ms, List.IsChain (fun x y ↦ (x == y) = true) l := by
        intro l hl
        apply ha₂
        apply List.mem_cons_of_mem
        exact hl
      have hns : ∀ l ∈ ns, List.IsChain (fun x y ↦ (x == y) = true) l := by
        intro l hl
        apply hb₂
        apply List.mem_cons_of_mem
        exact hl
      have h₄ := h hab.right hmsns ha₁.right hb₁.right hms hns ha₃.right hb₃.right
      rw [h₃, h₄]

lemma List.head?_flatten_of_nil_not_mem {α : Type u} {l : List (List α)} (hl : [] ∉ l)
  : l.flatten.head? = l.head?.bind (fun l' ↦ l'.head?) := by
    by_cases! hl' : l = []
    · rw [hl', List.flatten_nil, List.head?_nil, List.head?_nil, Option.bind_none]
    · rcases List.exists_cons_of_ne_nil hl' with ⟨a, as, has⟩
      rw [has, List.flatten_cons, List.head?_cons, Option.bind_some, List.head?_append]
      apply Option.or_eq_left_of_isSome
      rw [List.isSome_head?]
      contrapose! hl
      rw [← hl, has]
      apply List.mem_cons_self

lemma blocks_semi_inj {a b : List Coin} (hab : List.blocks a = List.blocks b)
  (hab' : a.head? = b.head?) : a = b := by
  rw [List.blocks, List.blocks, List.segments, List.segments] at hab
  set a' := List.splitBy (fun x1 x2 ↦ x1 == x2) a with ha'
  set b' := List.splitBy (fun x1 x2 ↦ x1 == x2) b with hb'
  symm at ha' hb'
  rw [List.splitBy_eq_iff] at ha' hb'
  rcases ha' with ⟨ha₀, ha₁, ha₂, ha₃⟩
  rcases hb' with ⟨hb₀, hb₁, hb₂, hb₃⟩
  rw [ha₀, hb₀, List.head?_flatten_of_nil_not_mem ha₁, List.head?_flatten_of_nil_not_mem hb₁] at hab'
  rw [ha₀, hb₀, blocks_semi_inj_helper hab hab' ha₁ hb₁ ha₂ hb₂ ha₃ hb₃]

def Row.blocks {n : ℕ} (c : Row n) : List ℕ := List.blocks (List.ofFn c)

lemma Row.sum_blocks {n : ℕ} (c : Row n)
  : List.sum (Row.blocks c) = 2 * n := by
    rw [Row.blocks, List.sum_blocks, List.length_ofFn]

def listOfBlocks (l : List ℕ) (head : Coin) : List Coin
  := match l with
    | [] => []
    | a::as => List.replicate a head ++ listOfBlocks as (Coin.flip head)

lemma List.head?_listOfBlocks (l : List ℕ) (head : Coin) (hl : l ≠ []) (hl' : 0 < l.head hl)
  : (listOfBlocks l head).head? = some head := by
    rw [List.ne_nil_iff_exists_cons] at hl
    rcases hl with ⟨a, as, has⟩
    simp [has] at hl'
    have h : List.replicate a head ≠ [] := by
      rw [(List.replicate_eq_nil_iff _).ne]
      lia
    rw [has, listOfBlocks, List.head?_append_of_ne_nil _ h]
    rw [List.head?_replicate, if_neg (by lia)]

lemma List.blocks_listOfBlock (l : List ℕ) (head : Coin) (hl : ∀ x ∈ l, 0 < x)
  : List.blocks (listOfBlocks l head) = l := by
    induction' l with a as h generalizing head
    · rw [listOfBlocks, List.blocks, List.segments, List.splitBy_nil, List.map_nil]
    · have ha' : 0 < a := by
        apply hl
        apply List.mem_cons_self
      have has' : ∀ x ∈ as, 0 < x := by
        intro x hx
        apply hl
        apply List.mem_cons_of_mem
        exact hx
      have has := h head.flip has'
      rw [List.blocks, List.segments] at has
      rw [listOfBlocks, List.blocks, List.segments]
      have h_mem_head : ∀ y ∈ (listOfBlocks as head.flip).head?, as ≠ [] := by
        intro y hy
        contrapose hy
        rw [hy, listOfBlocks, List.head?_nil]
        apply Option.not_mem_none
      have has'' : ∀ has''' : as ≠ [], 0 < as.head has''' := by
        intro has'''
        apply has'
        apply List.head_mem
      have h' : ∀ x ∈ (List.replicate a head).getLast?, ∀ y ∈ (listOfBlocks as head.flip).head?, (x == y) = false := by
        intro x hx y hy
        rcases List.mem_getLast?_eq_getLast hx with ⟨h_rep', hx'⟩
        rw [hx']
        rw [List.getLast_replicate]
        rw [List.head?_listOfBlocks as head.flip (h_mem_head y hy) (has'' (h_mem_head y hy)), Option.mem_some] at hy
        rw [← hy, beq_eq_false_iff_ne, ← (Coin.flip_eq_iff _ _)]
      have h_rep : List.replicate a head ≠ [] := by
        rw [(List.replicate_eq_nil_iff _).ne, Nat.ne_zero_iff_zero_lt]
        apply ha'
      have h'' : (List.replicate a head).splitBy (· == ·) = [List.replicate a head] := by
        apply List.splitBy_of_isChain h_rep
        apply List.isChain_beq_replicate
      rw [List.splitBy_append h', h'', ← has, List.map_append, List.map_singleton]
      rw [List.singleton_append, List.length_replicate]
      congr

lemma List.listOfBlocks_blocks (l : List Coin)
  : ∃ coin : Coin, listOfBlocks (List.blocks l) (coin) = l := by
    by_cases! hl : l = []
    · use Coin.A
      rw [hl, List.blocks, List.segments, List.splitBy_nil, List.map_nil, listOfBlocks]
    · use l.head hl
      have h' : ¬blocks l = [] := by
        rw [List.blocks, List.segments]
        rw [List.map_eq_nil_iff]
        rw [List.splitBy_eq_nil]
        exact hl
      have h'' :  0 < (blocks l).head h' := by
        simp [List.blocks]
        rw [← Nat.ne_zero_iff_zero_lt]
        rw [List.length_eq_zero_iff.ne]
        apply List.ne_nil_of_mem_splitBy (List.head_mem _)
      have h''' : ∀ x ∈ List.blocks l, 0 < x := by
        intro x hx
        apply List.zero_lt_of_mem_blocks l x hx
      have h := List.blocks_listOfBlock (List.blocks l) (l.head hl) h'''
      apply blocks_semi_inj h
      rw [List.head?_listOfBlocks _ _ h' h'']
      rw [List.head?_eq_some_head hl]

lemma listOfBlocks_length (l : List ℕ) (head : Coin)
  : (listOfBlocks l head).length = l.sum := by
    induction' l with a as h generalizing head
    · rw [listOfBlocks, List.length_nil, List.sum_nil]
    · rw [listOfBlocks, List.length_append, List.sum_cons]
      rw [List.length_replicate, h head.flip]

def Row.ofBlocks {n : ℕ} (l : List ℕ) (head : Coin) (hl : l.sum = 2 * n)
  : Row n := by
    have h : 2 * n = (listOfBlocks l head).length  := by
      rw [← hl, ← listOfBlocks_length l head]
    use fun i ↦ (listOfBlocks l head).get (Fin.cast h i)

lemma Row.blocks_ofBlocks {n : ℕ} (l : List ℕ) (head : Coin) (hl : l.sum = 2 * n) (hl' : ∀ x ∈ l, 0 < x)
  : (Row.ofBlocks l head hl).blocks = l := by
    nth_rw 2 [← List.blocks_listOfBlock l head hl']
    rw [← List.ofFn_get (listOfBlocks l head), Row.ofBlocks, Row.blocks]
    congr 1
    apply List.ofFn_congr
    rw [listOfBlocks_length, hl]

lemma Row.ofBlocks_blocks {n : ℕ} (c : Row n)
  : ∃ coin : Coin, Row.ofBlocks c.blocks (coin) c.sum_blocks = c := by
  rcases List.listOfBlocks_blocks (List.ofFn c) with ⟨coin, h⟩
  use coin
  simp [Row.ofBlocks, Row.blocks, h]

lemma ofFn_ofBlocks {n : ℕ} (l : List ℕ) (head : Coin) (hl : l.sum = 2 * n)
  : List.ofFn (Row.ofBlocks l head hl) = listOfBlocks l head := by
    have h' : 2 * n = (listOfBlocks l head).length := by
      rw [listOfBlocks_length]
      exact hl.symm
    have h : List.ofFn (Row.ofBlocks l head hl) = List.ofFn (listOfBlocks l head).get := by
      rw [List.ofFn_congr h']
      congr
    rw [h, List.ofFn_get]

def List.alternateSum {α : Type u} [Add α] [Zero α] (l : List α) (head : Bool) : α
  := match l with
    | [] => 0
    | a::as => (if head then a else 0) + List.alternateSum as !head

lemma List.alternateSum_pos_of_nat (l : List ℕ) (head : Bool)
  (hl : ∀ x ∈ l, 0 < x) (hl': 2 ≤ l.length)
  : 0 < List.alternateSum l head := by
    have h := List.exists_cons_of_length_pos (by lia : 0 < l.length)
    rcases h with ⟨a, as, haas⟩
    rw [haas] at hl' ⊢ hl
    rw [List.length_cons] at hl'
    have h' := List.exists_cons_of_length_pos (by lia : 0 < as.length)
    rcases h' with ⟨b, bs, hbbs⟩
    rw [hbbs] at hl' ⊢ hl
    rw [List.alternateSum, List.alternateSum]
    rcases head <;> simp <;> left <;> apply hl <;> simp

lemma List.lt_alternateSum_of_nat_mem (l : List ℕ) (x : ℕ) (h : x ∈ l)
  (hl : ∀ x ∈ l, 0 < x) (hl': 4 ≤ l.length)
  : x < max (List.alternateSum l true) (List.alternateSum l false) := by
    induction' l with a as haas
    · contrapose! h
      apply List.not_mem_nil
    · by_cases h4 : (a :: as).length = 4
      · rw [List.length_eq_four] at h4
        rcases h4 with ⟨a', b, c, d, habcd⟩
        rw [List.cons_eq_cons] at habcd
        rw [habcd.right] at ⊢ h hl
        repeat rw [List.alternateSum]
        rw [Bool.not_true, Bool.not_false, Bool.not_true, Bool.not_false]
        rw [if_pos rfl, if_pos rfl, if_pos rfl, if_pos rfl]
        repeat rw [if_neg Bool.false_eq_true_eq_False]
        abel_nf
        rw [lt_max_iff]
        simp at h
        have ha := hl a (by simp)
        have hb := hl b (by simp)
        have hc := hl c (by simp)
        have hd := hl d (by simp)
        rcases h with h|h|h|h <;> lia
      · rw [List.mem_cons] at h
        rw [List.length_cons] at h4 hl'
        have hl'' : ∀ x ∈ as, 0 < x := by
            intro x hx
            apply hl
            apply List.mem_cons_of_mem
            exact hx
        rcases h with h|h
        · rw [List.alternateSum, if_pos rfl, h]
          apply lt_max_of_lt_left
          rw [Nat.lt_add_right_iff_pos]
          apply List.alternateSum_pos_of_nat _ _ hl'' (by lia)
        · apply lt_of_lt_of_le (haas h hl'' (by lia))
          rw [max_comm]
          apply max_le_max
          · rw [List.alternateSum, Bool.not_true]
            apply Nat.le_add_left
          · rw [List.alternateSum, Bool.not_false]
            apply Nat.le_add_left

lemma List.sum_eq_alternateSum_add_alternateSum {α : Type u} [AddCommMonoid α]
  (l : List α) (head : Bool)
  : List.sum l = List.alternateSum l head + List.alternateSum l !head := by
    induction' l with a as h generalizing head
    · rw [List.alternateSum, List.alternateSum, List.sum_nil]
      abel
    · rw [List.alternateSum, List.alternateSum, List.sum_cons, h !head]
      by_cases! h' : head = true
      · rw [h', if_pos (by decide), if_neg (by decide)]
        abel
      · rw [← Bool.eq_false_iff] at h'
        rw [h', if_neg (by decide), if_pos (by decide)]
        abel

lemma count_ListOfBlocks_eq_alternateSum (l : List ℕ) (head : Coin)
  : List.count Coin.A (listOfBlocks l head) = List.alternateSum l (head = Coin.A) := by
    induction' l with a as h generalizing head
    · rw [List.alternateSum, listOfBlocks, List.count_nil]
    · rw [List.alternateSum, listOfBlocks, List.count_append, h head.flip]
      rw [← decide_not]
      simp only [← ne_eq, Coin.flip_eq_iff]
      rw [add_left_inj, List.count_replicate, beq_eq_decide]

lemma Row.ofBlocks_valid_iff_alternateSum_eq {n : ℕ} (l : List ℕ) (head : Coin) (hl : l.sum = 2 *n) (head' : Bool)
  : (Row.ofBlocks l head hl).valid ↔ List.alternateSum l head' = n := by
    rw [Row.valid_iff_isValidRow_ofFn, ofFn_ofBlocks, isValidRow, listOfBlocks_length, hl]
    rw [mul_eq_mul_left_iff, or_iff_left (by norm_num), count_ListOfBlocks_eq_alternateSum]
    by_cases! h : decide (head = Coin.A) = head'
    · rw [h]
    · rw [← Bool.eq_not] at h
      rw [h]
      rw [List.sum_eq_alternateSum_add_alternateSum l head'] at hl
      constructor <;> intro h' <;> rw [h', two_mul] at hl
      · exact add_right_cancel hl
      · exact add_left_cancel hl

lemma Row.blocks_eq_iff {n : ℕ} [inst : NeZero n] (c : Row n) :
  c.blocks = [n, n] ↔ (∃ coin, ∀ (i : Fin (2 * n)), c i = coin ↔ ↑i < n) := by
  constructor
  · intro h
    rcases Row.ofBlocks_blocks c with ⟨coin, hc'⟩
    rw [ofBlocks] at hc'
    use coin
    intro i
    rw [← hc']
    simp [h, listOfBlocks, List.getElem_append]
    constructor
    · intro h'
      contrapose! h'
      rw [and_iff_right h']
      symm
      rw [← Coin.flip_eq_iff _ _]
    · intro h' h''
      lia
  · rintro ⟨coin, h'⟩
    have h'' : (List.ofFn c).length = 2 * n := by
      rw [List.length_ofFn]
    have h''' : (List.replicate n coin ++ List.replicate n coin.flip).length = 2 * n := by
      rw [List.length_append, List.length_replicate, List.length_replicate, two_mul]
    have h : List.ofFn c = List.replicate n coin ++ List.replicate n coin.flip := by
      rw [List.ext_getElem?_iff]
      intro i
      rw [List.getElem?_append, List.length_replicate]
      rw [List.getElem?_replicate, List.getElem?_replicate, List.getElem?_ofFn]
      by_cases! hi : i < 2 * n
      · by_cases! hi' : i < n
        · rw [dif_pos (by lia), if_pos (by lia), if_pos (by lia), Option.some_inj]
          rw [h' ⟨i, hi⟩]
          lia
        · rw [dif_pos (by lia), if_neg (by lia), if_pos (by lia), Option.some_inj]
          symm
          rw [Coin.flip_eq_iff]
          symm
          rw [ne_eq, (h' ⟨i, hi⟩).not]
          lia
      · rw [dif_neg (by lia), if_neg (by lia), if_neg (by lia)]
    have h' : ∀ x ∈ (List.replicate n coin).getLast?, ∀ y ∈ (List.replicate n coin.flip).head?, (x == y) = false := by
      intro x hx y hy
      rw [List.getLast?_replicate, if_neg inst.ne, Option.mem_some] at hx
      rw [List.head?_replicate, if_neg inst.ne, Option.mem_some] at hy
      rw [← hx, ← hy, beq_eq_false_iff_ne, ← Coin.flip_eq_iff]
    rw [Row.blocks, h, List.blocks, List.segments, List.splitBy_append h']
    rw [List.splitBy_of_isChain ((List.replicate_eq_nil_iff _).ne.mpr inst.ne) (List.isChain_beq_replicate _ _)]
    rw [List.splitBy_of_isChain ((List.replicate_eq_nil_iff _).ne.mpr inst.ne) (List.isChain_beq_replicate _ _)]
    rw [List.map_append, List.map_singleton, List.map_singleton, List.length_replicate, List.length_replicate, List.singleton_append]

lemma Row.leftmostNSame_iff_length_blocks_ofFn_of_valid {n : ℕ} [NeZero n] {c : Row n} (hc : c.valid)
  : c.leftmostNSame ↔ (c.blocks).length = 2 := by
    rw [Row.leftmostNSame_iff_of_valid hc, ← Row.blocks_eq_iff c]
    constructor
    · intro h
      rw [h, List.length_cons, List.length_singleton]
    · intro h
      rw [List.length_eq_two] at h
      rcases h with ⟨p, q, hpq⟩
      rcases Row.ofBlocks_blocks c with ⟨coin, hc'⟩
      rw [← hc'] at hc
      have hp := (Row.ofBlocks_valid_iff_alternateSum_eq _ coin (Row.sum_blocks _) true).mp hc
      have hq := (Row.ofBlocks_valid_iff_alternateSum_eq _ coin (Row.sum_blocks _) false).mp hc
      rw [hpq, List.alternateSum, List.alternateSum, List.alternateSum] at hp hq
      simp at hp hq
      rw [hp, hq] at hpq
      exact hpq

lemma List.blocks_take {α : Type u} [DecidableEq α] (l : List α) (k : ℕ)
  : List.blocks (l.take ((List.blocks l).take k).sum) = (List.blocks l).take k := by
    rw [List.blocks, List.blocks, List.segments, List.segments, ← List.map_take]
    congr
    rw [List.splitBy_eq_iff]
    constructorm* _ ∧ _
    · rw [← List.take_sum_flatten, List.map_take, List.flatten_splitBy]
    · intro h
      have h' := List.mem_of_mem_take h
      contrapose! h'
      apply List.nil_notMem_splitBy
    · intro l' h
      have h' := List.mem_of_mem_take h
      apply List.isChain_of_mem_splitBy h'
    · apply List.IsChain.take
      apply List.isChain_getLast_head_splitBy

lemma List.blocks_drop {α : Type u} [DecidableEq α] (l : List α) (k : ℕ)
  : List.blocks (l.drop ((List.blocks l).take k).sum) = (List.blocks l).drop k := by
    rw [List.blocks, List.blocks, List.segments, List.segments, ← List.map_drop]
    congr
    rw [List.splitBy_eq_iff]
    constructorm* _ ∧ _
    · rw [← List.drop_sum_flatten, List.flatten_splitBy]
    · intro h
      have h' := List.mem_of_mem_drop h
      contrapose! h'
      apply List.nil_notMem_splitBy
    · intro l' h
      have h' := List.mem_of_mem_drop h
      apply List.isChain_of_mem_splitBy h'
    · apply List.IsChain.drop
      apply List.isChain_getLast_head_splitBy

lemma List.blocks_drop_take {α : Type u} [DecidableEq α] (l : List α) (p q : ℕ)
  : List.blocks ((l.drop ((List.blocks l).take p).sum).take (((List.blocks l).drop p).take q).sum) = ((List.blocks l).drop p).take q := by
    rw [← List.blocks_drop, ← List.blocks_take]
    congr
    rw [List.blocks_take]

lemma List.blocks_append {α : Type u} [DecidableEq α] {a b : List α} (hab : ∀ x ∈ a.getLast?, ∀ y ∈ b.head?, (x == y) = false)
  : List.blocks (a ++ b) = List.blocks a ++ List.blocks b := by
    rw [List.blocks, List.segments, List.splitBy_append hab]
    rw [List.blocks, List.blocks, List.segments, List.segments, List.map_append]

lemma List.length_blocks_append_lt_of {α : Type u} [DecidableEq α] {a b : List α} (hab : ∃ x ∈ a.getLast?, ∃ y ∈ b.head?, (x == y) = true)
  : (List.blocks (a ++ b)).length < (List.blocks a).length + (List.blocks b).length := by
    rw [List.blocks, List.length_map, List.segments, List.splitBy_append' hab]
    rw [List.length_append, List.length_append, List.length_singleton]
    rw [List.length_dropLast, List.length_tail]
    rw [List.blocks, List.length_map, List.segments]
    rw [List.blocks, List.length_map, List.segments]
    rcases hab with ⟨p, hp, q, hq, hpq⟩
    have ha : a ≠ [] := by
      contrapose! hp
      rw [hp, List.getLast?_nil]
      apply Option.not_mem_none
    have hb : b ≠ [] := by
      contrapose! hq
      rw [hq, List.head?_nil]
      apply Option.not_mem_none
    have ha' : (List.splitBy (fun x1 x2 ↦ x1 == x2) a) ≠ [] := by
      rw [List.splitBy_eq_nil.ne]
      exact ha
    have hb' : (List.splitBy (fun x1 x2 ↦ x1 == x2) b) ≠ [] := by
      rw [List.splitBy_eq_nil.ne]
      exact hb
    rw [← List.length_pos_iff_ne_nil] at ha' hb'
    simp only [BEq.beq]
    lia

lemma List.length_blocks_append_le {α : Type u} [DecidableEq α] {a b : List α}
  : (List.blocks (a ++ b)).length ≤ (List.blocks a).length + (List.blocks b).length := by
    by_cases! h : ∃ x ∈ a.getLast?, ∃ y ∈ b.head?, (x == y) = true
    · apply le_of_lt
      apply List.length_blocks_append_lt_of
      exact h
    · have h' : ∀ x ∈ a.getLast?, ∀ y ∈ b.head?, (x == y) = false := by
        intro x hx y hy
        rw [Bool.eq_false_iff]
        exact h x hx y hy
      rw [List.blocks_append h', List.length_append]

def indexInBlock (l : List ℕ) (k : ℕ) :=
  {i ∈ Finset.Iic l.length | (l.take i).sum ≤ k }.max' ⟨0, by simp⟩

lemma indexInBlock_eq_length_sub_one_of (l : List ℕ) (hl :l ≠ [])
  (k : ℕ) (hk : l.sum ≤ k + l.getLast hl) (hk' : k < l.sum)
  : indexInBlock l k = l.length - 1 := by
    rw [indexInBlock, Finset.max'_eq_iff]
    simp
    constructor
    · have h := List.sum_take_add_sum_drop l (l.length - 1)
      rw [List.drop_length_sub_one hl, List.sum_singleton] at h
      lia
    · intro j hj₁ hj₂
      have hl' :  0 < l.length := by
        rw [List.length_pos_iff]
        exact hl
      rw [Nat.le_sub_one_iff_lt hl']
      apply lt_of_le_of_ne hj₁
      contrapose! hj₂
      rw [hj₂, List.take_length]
      apply hk'

def List.blockIndex {α : Type u} [DecidableEq α] (l : List α) (k : Fin l.length) :=
  indexInBlock (List.blocks l) k

lemma List.blockIndex_lt {α : Type u} [DecidableEq α] (l : List α) (k : Fin l.length)
  : blockIndex l k < (blocks l).length := by
    rw [List.blockIndex, indexInBlock, Finset.max'_lt_iff]
    intro x hx
    simp at hx
    apply lt_of_le_of_ne hx.left
    contrapose! +distrib hx
    right
    rw [hx, List.take_length, List.sum_blocks]
    lia

lemma List.sum_take_blockIndex_blocks_le {α : Type u} [DecidableEq α] (l : List α) (k : Fin l.length)
  : (List.take (blockIndex l k) (blocks l)).sum ≤ k := by
    set i := (blockIndex l k) with hi
    rw [List.blockIndex, indexInBlock] at hi
    symm at hi
    rw [Finset.max'_eq_iff] at hi
    simp at hi
    exact hi.left.right

lemma List.lt_sum_take_succ_blockIndex_blocks {α : Type u} [DecidableEq α] (l : List α) (k : Fin l.length)
  : k < (List.take (blockIndex l k + 1) (blocks l)).sum := by
    set i := (blockIndex l k) with hi
    have hi' := hi
    rw [List.blockIndex, indexInBlock] at hi
    symm at hi
    rw [Finset.max'_eq_iff] at hi
    simp at hi
    contrapose! hi
    intro h
    use i + 1
    constructorm* _ ∧ _
    · rw [hi', Nat.succ_le_iff]
      apply List.blockIndex_lt
    · exact hi
    · lia

lemma List.some_get_eq_head?_get?_segments_blockIndex {α : Type u} [DecidableEq α] (l : List α) (k : Fin l.length)
  : some (l.get k) = (List.segments l)[List.blockIndex l k]?.bind (fun x ↦ x.head?) := by
    have h_lt := List.blockIndex_lt l k
    rw [List.blocks, List.length_map] at h_lt
    have h_get : some ((segments l).get ⟨blockIndex l k, h_lt⟩) = (List.segments l)[List.blockIndex l k]? := by
      rw [List.get_eq_getElem? (List.segments l) ⟨List.blockIndex l k, h_lt⟩]
      rw [Option.some_get, Fin.getElem?_fin, Fin.val_mk]
    rw [← h_get, Option.bind_some]
    have h_l_eq : l = ((segments l).take (blockIndex l k)).flatten ++ ((segments l).get ⟨blockIndex l k, h_lt⟩) ++ ((segments l).drop (blockIndex l k + 1)).flatten := by
      simp only [List.segments]
      nth_rw 1 [← List.flatten_splitBy (fun x1 x2 ↦ x1 == x2) l]
      nth_rw 1 [← List.take_append_drop (blockIndex l k + 1) (List.splitBy (fun x1 x2 ↦ x1 == x2) l)]
      rw [List.flatten_append]
      congr 1
      rw [List.take_add_one, List.flatten_append]
      congr 1
      simp only [List.segments] at h_get
      rw [← h_get, Option.toList_some, List.flatten_singleton]
    rw [List.get_eq_getElem?, Option.some_get, Fin.getElem?_fin]
    nth_rw 1 [h_l_eq]
    have h_left : ↑k < ((List.take (blockIndex l k) (segments l)).flatten ++ (segments l).get ⟨blockIndex l k, h_lt⟩).length := by
      set i := blockIndex l k with hi
      symm at hi
      rw [List.blockIndex, indexInBlock, Finset.max'_eq_iff] at hi
      simp [List.blocks] at hi
      rw [← @List.flatten_singleton _ ((segments l).get ⟨blockIndex l k, h_lt⟩)]
      rw [← Option.toList_some, h_get, ← List.flatten_append, ← List.take_add_one]
      contrapose! +distrib hi
      right
      use (blockIndex l k + 1)
      constructorm* _ ∧ _
      · lia
      · rw [List.length_flatten, List.map_take] at hi
        exact hi
      · lia
    have h_right : (List.take (blockIndex l k) (segments l)).flatten.length ≤ ↑k := by
      set i := blockIndex l k with hi
      symm at hi
      rw [List.blockIndex, indexInBlock, Finset.max'_eq_iff] at hi
      simp [List.blocks] at hi
      rw [List.length_flatten, List.map_take]
      exact hi.left.right
    rw [List.getElem?_append_left h_left, List.getElem?_append_right h_right]
    have h_rep : ∃ n : ℕ, ∃ i : α, (segments l).get ⟨blockIndex l k, h_lt⟩ = List.replicate n i := by
      simp only [List.segments]
      apply List.exists_replicate_of_isChain_beq
      · apply @List.isChain_of_mem_splitBy _ _ _ l
        apply List.get_mem
      · apply @List.ne_nil_of_mem_splitBy _ _ (fun x1 x2 ↦ x1 == x2) l
        apply List.get_mem
    rcases h_rep with ⟨n, i, hni⟩
    rw [hni, List.head?_replicate, List.getElem?_replicate]
    have hn : ((segments l).get ⟨blockIndex l k, h_lt⟩).length = n := by
      rw [hni, List.length_replicate]
    rw [← hn]
    have h_if₁ : ↑k - (List.take (blockIndex l k) (segments l)).flatten.length <
      ((segments l).get ⟨blockIndex l k, h_lt⟩).length := by
        rw [List.length_append] at h_left
        lia
    have h_if₂ : ¬((segments l).get ⟨blockIndex l k, h_lt⟩).length = 0 :=
      Nat.ne_zero_of_lt h_if₁
    rw [if_pos h_if₁, if_neg h_if₂]

lemma some_get_eq_head?_bind_get?_segments_blockIndex (l : List Coin) (k : Fin l.length)
  : some (l.get k) = l.head?.map (fun x ↦ if Even (List.blockIndex l k) then x else x.flip) := by
    rw [List.some_get_eq_head?_get?_segments_blockIndex]
    have h := List.blockIndex_lt l k
    rw [List.blocks, List.length_map] at h
    rw [segments_getElem?_map_eq _ _ h]

lemma List.head?_get?_segments_blockIndex_ne_of {α : Type u} [DecidableEq α] (l : List α) (a b : ℕ)
  (hab : b = a + 1) (hb : b < (List.segments l).length)
  : (List.segments l)[a]?.bind (fun x ↦ x.head?) ≠ (List.segments l)[b]?.bind (fun x ↦ x.head?) := by
    have ha : a < (List.segments l).length := by lia
    have h_geta : some ((segments l).get ⟨a, ha⟩) = (List.segments l)[a]? := by
      rw [List.get_eq_getElem? (List.segments l) ⟨a, ha⟩]
      rw [Option.some_get, Fin.getElem?_fin, Fin.val_mk]
    have h_getb : some ((segments l).get ⟨b, hb⟩) = (List.segments l)[b]? := by
      rw [List.get_eq_getElem? (List.segments l) ⟨b, hb⟩]
      rw [Option.some_get, Fin.getElem?_fin, Fin.val_mk]
    rw [← h_geta, ← h_getb, Option.bind_some, Option.bind_some]
    have h_repa : ∃ n : ℕ, ∃ i : α, (segments l).get ⟨a, ha⟩ = List.replicate n i := by
      simp only [List.segments]
      apply List.exists_replicate_of_isChain_beq
      · apply @List.isChain_of_mem_splitBy _ _ _ l
        apply List.get_mem
      · apply @List.ne_nil_of_mem_splitBy _ _ (fun x1 x2 ↦ x1 == x2) l
        apply List.get_mem
    have h_repb : ∃ n : ℕ, ∃ i : α, (segments l).get ⟨b, hb⟩ = List.replicate n i := by
      simp only [List.segments]
      apply List.exists_replicate_of_isChain_beq
      · apply @List.isChain_of_mem_splitBy _ _ _ l
        apply List.get_mem
      · apply @List.ne_nil_of_mem_splitBy _ _ (fun x1 x2 ↦ x1 == x2) l
        apply List.get_mem
    rcases h_repa with ⟨na, ia, hnia⟩
    rcases h_repb with ⟨nb, ib, hnib⟩
    rw [hnia, hnib, List.head?_replicate, List.head?_replicate]
    have h_na : ¬na = 0 := by
      rw [← @List.length_replicate _ na ia, ← ne_eq, Nat.ne_zero_iff_zero_lt]
      rw [List.length_pos_iff, ← hnia]
      simp only [List.segments]
      apply @List.ne_nil_of_mem_splitBy _ _ (fun x1 x2 ↦ x1 == x2) l
      apply List.get_mem
    have h_nb : ¬nb = 0 := by
      rw [← @List.length_replicate _ nb ib, ← ne_eq, Nat.ne_zero_iff_zero_lt]
      rw [List.length_pos_iff, ← hnib]
      simp only [List.segments]
      apply @List.ne_nil_of_mem_splitBy _ _ (fun x1 x2 ↦ x1 == x2) l
      apply List.get_mem
    rw [if_neg h_na, if_neg h_nb, Option.some_inj.ne]
    simp only [List.segments] at hnia hnib hb
    have h := List.isChain_getLast_head_splitBy (fun x1 x2 ↦ x1 == x2) l
    rw [List.isChain_iff_getElem] at h
    rcases h a (by lia) with ⟨h'a, h'b, h'⟩
    rw [List.get_eq_getElem] at hnia hnib
    simp at hnia hnib
    simp [hab] at hnib
    simp [hnia, hnib] at h'
    exact h'

lemma List.chainLeft_eq {α : Type u} [DecidableEq α] (l : List α) (k : Fin l.length)
  : List.chainLeft l k = (List.take (List.blockIndex l k) (List.blocks l)).sum := by
    rw [chainLeft]
    have h := List.sum_take_blockIndex_blocks_le l k
    have h_mk : (List.take (List.blockIndex l k) (blocks l)).sum < l.length := by lia
    rw [← Fin.val_mk h_mk, Fin.val_inj, Finset.min'_eq_iff]
    constructor
    · simp only [Finset.mem_filter, Finset.mem_Iic]
      constructor
      · rw [← Fin.val_fin_le, Fin.val_mk]
        exact h
      · intro i hi₁ hi₂
        rw [← Option.some_inj, List.some_get_eq_head?_get?_segments_blockIndex, List.some_get_eq_head?_get?_segments_blockIndex]
        congr 2
        rw [List.blockIndex, indexInBlock, Finset.max'_eq_iff]
        simp
        constructorm* _ ∧ _
        · apply le_of_lt
          apply List.blockIndex_lt
        · grind only [= Lean.Grind.toInt_fin]
        · intro j hj₁ hj₂
          set m := List.blockIndex l k with hm
          symm at hm
          rw [List.blockIndex, indexInBlock, Finset.max'_eq_iff] at hm
          simp at hm
          apply hm.right j hj₁ (by lia)
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_Iic] at hi
      rcases hi with ⟨hi₁, hi₂⟩
      contrapose! hi₂
      use ⟨(List.take (blockIndex l k) (blocks l)).sum - 1, by lia⟩
      constructorm* _ ∧ _
      · grind only [= Lean.Grind.toInt_fin]
      · grind only [= Lean.Grind.toInt_fin]
      · rw [← Option.some_inj.ne, List.some_get_eq_head?_get?_segments_blockIndex, List.some_get_eq_head?_get?_segments_blockIndex]
        apply List.head?_get?_segments_blockIndex_ne_of
        · have h : 0 < (List.take (blockIndex l k) (blocks l)).sum := by
              grind only [=Lean.Grind.toInt_fin]
          have h' : 1 ≤ blockIndex l k := by
            rw [Nat.one_le_iff_ne_zero]
            contrapose! h
            rw [h, List.take_zero, List.sum_nil]
          apply Nat.eq_add_of_sub_eq
          · exact h'
          · symm
            rw [blockIndex, indexInBlock, Finset.max'_eq_iff]
            simp
            constructorm* _ ∧ _
            · apply le_of_lt
              apply lt_trans (List.blockIndex_lt l k)
              lia
            · apply Nat.le_sub_of_add_le
              rw [← List.sum_take_add_sum_drop (List.take (blockIndex l k) (blocks l)) (blockIndex l k - 1)]
              rw [List.take_take, min_eq_left (by lia), Nat.add_le_add_iff_left]
              rw [Nat.one_le_iff_ne_zero, Nat.ne_zero_iff_zero_lt]
              apply List.sum_pos
              · intro x hx
                apply List.zero_lt_of_mem_blocks l
                apply List.mem_of_mem_take (List.mem_of_mem_drop hx)
              · rw [List.ne_nil_iff_length_pos, List.length_drop, List.length_take]
                have h'' : blockIndex l k ≤ (blocks l).length := by
                  apply le_of_lt
                  apply List.blockIndex_lt
                rw [min_eq_left h'']
                lia
            · intro j hj₁ hj₂
              apply Nat.le_sub_of_add_le
              rw [Nat.le_sub_iff_add_le (by lia)] at hj₂
              rw [Nat.succ_le_iff] at ⊢ hj₂
              contrapose! hj₂
              rw [← List.sum_take_add_sum_drop (List.take j (blocks l)) (blockIndex l k)]
              rw [List.take_take, min_eq_left hj₂]
              apply Nat.le_add_right
        · have h := List.blockIndex_lt l k
          rw [List.blocks, List.length_map] at h
          exact h

lemma List.chainRight_succ_eq {α : Type u} [DecidableEq α] (l : List α) (k : Fin l.length)
  : List.chainRight l k + 1 = (List.take (List.blockIndex l k + 1) (List.blocks l)).sum := by
    symm
    have h_sum := List.lt_sum_take_succ_blockIndex_blocks l k
    have h_sub : 0 < (List.take (blockIndex l k + 1) (blocks l)).sum := by lia
    apply Nat.eq_add_of_sub_eq h_sub
    symm
    rw [chainRight]
    have h_sum' : (List.take (blockIndex l k + 1) (blocks l)).sum ≤ l.length := by
      rw [← List.sum_blocks, ← List.sum_take_add_sum_drop (blocks l) (blockIndex l k + 1)]
      apply Nat.le_add_right
    have h_mk : (List.take (blockIndex l k + 1) (blocks l)).sum - 1 < l.length := by lia
    rw [← Fin.val_mk h_mk, Fin.val_inj, Finset.max'_eq_iff]
    constructor
    · simp only [Finset.mem_filter, Finset.mem_Ici]
      constructor
      · rw [← Fin.val_fin_le]
        lia
      · intro i hi₁ hi₂
        rw [← Option.some_inj, List.some_get_eq_head?_get?_segments_blockIndex, List.some_get_eq_head?_get?_segments_blockIndex]
        congr 2
        rw [List.blockIndex, indexInBlock, Finset.max'_eq_iff]
        simp
        constructorm* _ ∧ _
        · apply le_of_lt
          apply List.blockIndex_lt
        · set m := List.blockIndex l k with hm
          symm at hm
          rw [List.blockIndex, indexInBlock, Finset.max'_eq_iff] at hm
          simp at hm
          lia
        · intro j hj₁ hj₂
          contrapose! hj₂
          rw [← Nat.add_one_le_iff] at hj₂
          have h : (List.take (blockIndex l k + 1) (blocks l)).sum ≤ (List.take j (blocks l)).sum := by
            rw [← List.sum_take_add_sum_drop (List.take j (blocks l)) (blockIndex l k + 1)]
            rw [List.take_take, min_eq_left hj₂]
            apply Nat.le_add_right
          grind only [= Lean.Grind.toInt_fin]
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_Ici] at hi
      rcases hi with ⟨hi₁, hi₂⟩
      contrapose! hi₂
      have h_use : (List.take (blockIndex l k + 1) (blocks l)).sum < l.length := by grind only [= Lean.Grind.toInt_fin]
      use ⟨(List.take (blockIndex l k + 1) (blocks l)).sum, h_use⟩
      constructorm* _ ∧ _
      · grind only [= Lean.Grind.toInt_fin]
      · grind only [= Lean.Grind.toInt_fin]
      · rw [← Option.some_inj.ne, List.some_get_eq_head?_get?_segments_blockIndex, List.some_get_eq_head?_get?_segments_blockIndex]
        symm
        have h : blockIndex l ⟨(List.take (blockIndex l k + 1) (blocks l)).sum, h_use⟩ = blockIndex l k + 1 := by
          rw [blockIndex, indexInBlock, Finset.max'_eq_iff]
          simp
          constructor
          · apply List.blockIndex_lt
          · intro j hj₁ hj₂
            contrapose! hj₂
            rw [← List.sum_take_add_sum_drop (List.take j (blocks l)) (blockIndex l k + 1)]
            rw [List.take_take, min_eq_left_of_lt hj₂, lt_add_iff_pos_right]
            apply List.sum_pos
            · intro x hx
              apply List.zero_lt_of_mem_blocks l
              apply List.mem_of_mem_take (List.mem_of_mem_drop hx)
            · rw [List.ne_nil_iff_length_pos, List.length_drop, List.length_take]
              rw [min_eq_left hj₁]
              lia
        apply List.head?_get?_segments_blockIndex_ne_of
        · exact h
        · rw [h]
          have h' := List.blockIndex_lt l k
          have h_length : (segments l).length = (blocks l).length := by
            rw [List.blocks, List.length_map]
          rw [h_length]
          apply lt_of_le_of_ne (by lia)
          have h'' := h_use
          contrapose! h''
          rw [h'', List.take_length, List.sum_blocks]

lemma List.blocks_operation_left_segment {α : Type u} [DecidableEq α] (l : List α) (k : Fin l.length)
  : List.blocks (l.take (List.chainLeft l k)) = (List.blocks l).take (List.blockIndex l k) := by
    rw [← List.blocks_take]
    congr
    apply List.chainLeft_eq

lemma List.blocks_operation_right_segment {α : Type u} [DecidableEq α] (l : List α) (k : Fin l.length)
  : List.blocks (l.drop (List.chainRight l k + 1)) = (List.blocks l).drop (List.blockIndex l k + 1) := by
    rw [← List.blocks_drop]
    congr
    apply List.chainRight_succ_eq

lemma List.blocks_operation_middle_segment {α : Type u} [DecidableEq α] (l : List α) (k : Fin l.length)
  : List.blocks ((l.drop (List.chainLeft l k)).take (List.chainRight l k + 1 - List.chainLeft l k)) = ((List.blocks l).drop (List.blockIndex l k)).take 1 := by
    rw [← List.blocks_drop_take]
    congr
    · rw [List.chainLeft_eq, List.chainRight_succ_eq, Nat.sub_eq_of_eq_add']
      rw [← List.sum_take_add_sum_drop (List.take (blockIndex l k + 1) (blocks l)) (List.blockIndex l k)]
      congr 1
      · rw [List.take_take]
        congr
        exact Nat.min_add_right_self
      · rw [List.drop_take]
        lia
    · apply List.chainLeft_eq

lemma List.blocks_operation_left_head? {α : Type u} [DecidableEq α] (l : List α) (k : Fin l.length) (h : (List.chainLeft l k).val ≠ 0)
  : (l.take (List.chainLeft l k)).head? = l.head? := by
    rw [List.head?_take, if_neg h]

lemma List.blocks_operation_left_getLast? (l : List Coin) (k : Fin l.length) (h : (List.chainLeft l k).val ≠ 0)
  : (l.take (List.chainLeft l k)).getLast? = l.head?.map (fun x ↦ if Even (blockIndex l k) then x.flip else x) := by
    rw [List.getLast?_take, if_neg h]
    have h_mk : (chainLeft l k).val - 1 < l.length := by
      lia
    have h_get : some (l.get ⟨(chainLeft l k).val - 1, h_mk⟩) = l[(chainLeft l k).val - 1]? := by
      rw [List.get_eq_getElem?]
      rw [Option.some_get, Fin.getElem?_fin, Fin.val_mk]
    rw [← h_get, Option.some_or]
    rw [some_get_eq_head?_bind_get?_segments_blockIndex]
    congr
    ext x
    rw [← ite_not]
    congr
    have h_block : 1 ≤ blockIndex l k := by
      rw [chainLeft_eq] at h
      contrapose! h
      rw [Nat.lt_one_iff] at h
      rw [h, List.take_zero, List.sum_nil]
    have h_blocks' := List.blockIndex_lt l k
    have h_eq : blockIndex l ⟨↑(chainLeft l k) - 1, h_mk⟩ = blockIndex l k - 1 := by
      simp only [chainLeft_eq]
      rw [blockIndex, indexInBlock, Finset.max'_eq_iff]
      simp
      constructorm* _ ∧ _
      · lia
      · apply Nat.le_sub_one_of_lt
        rw [← List.sum_take_add_sum_drop (List.take (blockIndex l k) (blocks l)) (blockIndex l k - 1)]
        rw [List.take_take, min_eq_left (by lia), Nat.lt_add_right_iff_pos]
        apply List.sum_pos
        · intro x hx
          apply zero_lt_of_mem_blocks l
          apply List.mem_of_mem_take (List.mem_of_mem_drop hx)
        · rw [List.ne_nil_iff_length_pos, List.length_drop, List.length_take]
          rw [min_eq_left_of_lt h_blocks']
          lia
      · intro j hj₁ hj₂
        apply Nat.le_sub_one_of_lt
        contrapose! hj₂
        apply Nat.sub_one_lt_of_le
        · apply List.sum_pos
          · intro x hx
            apply zero_lt_of_mem_blocks l
            apply List.mem_of_mem_take hx
          · rw [List.ne_nil_iff_length_pos, List.length_take]
            rw [min_eq_left_of_lt h_blocks']
            lia
        · rw [← List.sum_take_add_sum_drop (List.take j (blocks l)) (blockIndex l k)]
          rw [List.take_take, min_eq_left (by lia)]
          apply Nat.le_add_right
    rw [h_eq, Nat.even_sub h_block]
    norm_num

lemma List.blocks_operation_right_head? (l : List Coin) (k : Fin l.length) (h : (List.chainRight l k).val ≠ l.length - 1)
  : (l.drop (List.chainRight l k + 1)).head? = l.head?.map (fun x ↦ if Even (blockIndex l k) then x.flip else x) := by
    rw [List.head?_drop]
    have h_mk : (chainRight l k).val + 1 < l.length := by
      lia
    have h_get : some (l.get (⟨(chainRight l k).val + 1, h_mk⟩)) = l[(chainRight l k).val + 1]? := by
      rw [List.get_eq_getElem?]
      rw [Option.some_get, Fin.getElem?_fin, Fin.val_mk]
    rw [← h_get, some_get_eq_head?_bind_get?_segments_blockIndex]
    congr
    ext x
    rw [← ite_not]
    congr
    have h_blocks' := List.blockIndex_lt l k
    have h_eq : blockIndex l ⟨↑(chainRight l k) + 1, h_mk⟩ = blockIndex l k + 1 := by
      simp only [chainRight_succ_eq]
      rw [blockIndex, indexInBlock, Finset.max'_eq_iff]
      simp
      constructorm* _ ∧ _
      · exact h_blocks'
      · intro j hj₁ hj₂
        contrapose! hj₂
        rw [← List.sum_take_add_sum_drop (List.take j (blocks l)) (blockIndex l k + 1)]
        rw [List.take_take, min_eq_left (by lia), Nat.lt_add_right_iff_pos]
        apply List.sum_pos
        · intro x hx
          apply zero_lt_of_mem_blocks l
          apply List.mem_of_mem_take (List.mem_of_mem_drop hx)
        · rw [List.ne_nil_iff_length_pos, List.length_drop, List.length_take]
          rw [min_eq_left hj₁]
          lia
    rw [h_eq, Nat.even_add_one, not_not]

lemma List.blocks_operation_middle_getLast? (l : List Coin) (k : Fin l.length)
  : ((l.drop (List.chainLeft l k)).take (List.chainRight l k + 1 - List.chainLeft l k)).getLast? = l.head?.map (fun x ↦ if Even (blockIndex l k) then x else x.flip) := by
    have h_lr := List.chainLeft_le_chainRight l k
    have h_ne : ¬(chainRight l k).val + 1 - (chainLeft l k).val = 0 := by
      lia
    rw [List.getLast?_take, if_neg h_ne]
    rw [List.getElem?_drop, Nat.sub_right_comm, Nat.add_sub_cancel, ← Nat.add_sub_assoc (by lia), Nat.add_sub_cancel_left]
    rw [← Fin.getElem?_fin]
    have h_get : some (l.get (chainRight l k)) = l[chainRight l k]? := by
      rw [List.get_eq_getElem? l (chainRight l k)]
      rw [Option.some_get, Fin.getElem?_fin, Fin.val_mk]
    rw [← h_get, Option.some_or]
    rw [some_get_eq_head?_bind_get?_segments_blockIndex]
    congr
    ext x
    congr 2
    have h := List.chainRight_succ_eq l k
    have h_lt := blockIndex_lt l k
    set m := List.blockIndex l k with hm
    symm at hm
    rw [List.blockIndex, indexInBlock, Finset.max'_eq_iff] at hm
    simp at hm
    rw [blockIndex, indexInBlock, Finset.max'_eq_iff]
    simp
    constructorm* _ ∧ _
    · exact hm.left.left
    · rw [← Nat.lt_add_one_iff, h, List.take_add, List.sum_append, Nat.lt_add_right_iff_pos]
      apply List.sum_pos
      · intro x hx
        apply zero_lt_of_mem_blocks l
        apply List.mem_of_mem_drop (List.mem_of_mem_take hx)
      · rw [← List.length_pos_iff_ne_nil, List.length_take, List.length_drop]
        apply lt_min (by norm_num)
        lia
    · intro j hj₁ hj₂
      contrapose! hj₂
      rw [← Nat.add_one_le_iff] at ⊢ hj₂
      rw [h, ← List.sum_take_add_sum_drop (List.take j (blocks l)) (m + 1)]
      rw [List.take_take, min_eq_left hj₂]
      apply Nat.le_add_right

lemma Row.blocks_operationOneBased_eq_blocks_of
  {n k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ 2 * n) {c : Row n}
  {blocks : List ℕ} (hc : c.blocks = blocks) (hk : indexInBlock blocks (k - 1) = 0)
  : ((Row.operationOneBased hk1 hkn) c).blocks = blocks := by
    rw [Row.blocks, ofFn_operationOneBased_eq_operationOneBased_ofFn]
    rw [List.operationOneBased, List.operation, List.move]
    have h_mk : k - 1 < (List.ofFn c).length := by
      rw [List.length_ofFn]
      lia
    have h := List.blocks_operation_left_segment (List.ofFn c) ⟨k - 1, h_mk⟩
    rw [Row.blocks] at hc
    rw [List.blockIndex, hc, Fin.val_mk, hk, List.take_zero, List.blocks] at h
    rw [List.map_eq_nil_iff, List.segments, List.splitBy_eq_nil] at h
    rw [h, List.append_nil, ← List.nil_append (List.take _ _), ← h]
    have h_le : (List.chainLeft (List.ofFn c) ⟨k - 1, h_mk⟩).val ≤ (List.chainRight (List.ofFn c) ⟨k - 1, h_mk⟩).val + 1 := by
      apply Nat.le_add_right_of_le
      apply List.chainLeft_le_chainRight
    rw [List.take_drop, ← Nat.add_sub_assoc h_le, Nat.add_sub_cancel_left]
    nth_rw 1 [← min_eq_left h_le]
    rw [← List.take_take, List.take_append_drop, List.take_append_drop]
    exact hc

lemma Row.blocks_operationOneBased_iterate_eq_blocks_of
  {n k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ 2 * n) {i : ℕ} {c : Row n}
  {blocks : List ℕ}(hc : c.blocks = blocks) (hk : indexInBlock blocks (k - 1) = 0)
  : ((Row.operationOneBased hk1 hkn)^[i] c).blocks = blocks := by
    induction' i with i hi
    · rw [Function.iterate_zero, id]
      exact hc
    · rw [Function.iterate_succ_apply']
      apply Row.blocks_operationOneBased_eq_blocks_of hk1 hkn hi hk

lemma Row.blocks_operationOneBased_eq_rotate_one_blocks_of
  {n k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ 2 * n) {c : Row n}
  {blocks : List ℕ} (h_blocks : Even blocks.length) (hc : c.blocks = blocks) (hk : indexInBlock blocks (k - 1) = blocks.length - 1)
  : ((Row.operationOneBased hk1 hkn) c).blocks = (blocks.reverse.rotate 1).reverse := by
    rw [Row.blocks, ofFn_operationOneBased_eq_operationOneBased_ofFn]
    rw [List.operationOneBased, List.operation, List.move]
    have h_mk : k - 1 < (List.ofFn c).length := by
      rw [List.length_ofFn]
      lia
    have h := List.blocks_operation_right_segment (List.ofFn c) ⟨k - 1, h_mk⟩
    rw [Row.blocks] at hc
    have h_block_length : 1 ≤ blocks.length := by
      rw [Nat.one_le_iff_ne_zero, List.length_eq_zero_iff.ne, ← hc]
      rw [List.blocks, List.map_eq_nil_iff.ne, List.segments, List.splitBy_eq_nil.ne]
      rw [← List.length_pos_iff_ne_nil, List.length_ofFn]
      lia
    have h_block_length' : 2 ≤ blocks.length := by
      by_cases! h' : 1 = blocks.length
      · contrapose! h_blocks
        rw [← h']
        norm_num
      · lia
    rw [List.blockIndex, hc, Fin.val_mk, hk, Nat.sub_add_cancel h_block_length, List.drop_length, List.blocks] at h
    rw [List.map_eq_nil_iff, List.segments, List.splitBy_eq_nil] at h
    rw [h, List.append_nil]
    have h_chainLeft : (List.chainLeft (List.ofFn c) ⟨k - 1, h_mk⟩).val ≠ 0 := by
      rw [List.chainLeft_eq, Nat.ne_zero_iff_zero_lt]
      apply List.sum_pos
      · intro x hx
        apply List.zero_lt_of_mem_blocks (List.ofFn c)
        apply List.mem_of_mem_take hx
      · rw [← List.length_eq_zero_iff.ne, List.length_take]
        rw [List.blockIndex, hc, Fin.val_mk, hk, Nat.ne_zero_iff_zero_lt, lt_min_iff]
        lia
    have h_blocks' : ¬Even (blocks.length - 1) := by
      rw [Nat.not_even_iff_odd, Nat.odd_sub h_block_length]
      norm_num
      exact h_blocks
    have h_ne : ∀ x ∈ (List.take (↑(List.chainRight (List.ofFn c) ⟨k - 1, h_mk⟩) + 1 - ↑(List.chainLeft (List.ofFn c) ⟨k - 1, h_mk⟩))
      (List.drop (↑(List.chainLeft (List.ofFn c) ⟨k - 1, h_mk⟩)) (List.ofFn c))).getLast?,
      ∀ y ∈ (List.take (↑(List.chainLeft (List.ofFn c) ⟨k - 1, h_mk⟩)) (List.ofFn c)).head?, (x == y) = false := by
      intro x hx y hy
      rw [List.blocks_operation_left_head? _ _ h_chainLeft] at hy
      rw [List.blocks_operation_middle_getLast?] at hx
      rw [Option.mem_def] at hx hy
      rw [hy, Option.map_some, List.blockIndex, Fin.val_mk, hc, hk] at hx
      rw [if_neg h_blocks', Option.some_inj, Coin.flip_eq_iff] at hx
      exact beq_false_of_ne hx.symm
    rw [List.blocks_append h_ne, List.blocks_operation_left_segment, List.blocks_operation_middle_segment]
    rw [← List.take_append_drop (List.blockIndex (List.ofFn c) ⟨k - 1, h_mk⟩) blocks, hc]
    rw [List.reverse_append]
    have h_length : (List.drop (List.blockIndex (List.ofFn c) ⟨k - 1, h_mk⟩) blocks).reverse.length = 1 := by
      rw [List.length_reverse, List.length_drop, List.blockIndex, hc, Fin.val_mk, hk]
      rw [Nat.sub_sub_eq_min, min_eq_right h_block_length]
    nth_rw 6 [← h_length]
    rw [List.rotate_append_length_eq, List.reverse_append, List.reverse_reverse, List.reverse_reverse]
    rw [List.length_reverse] at h_length
    nth_rw 1 [← h_length]
    rw [List.take_length]

lemma Row.blocks_operationOneBased_iterate_eq_rotate_blocks_of
  {n k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ 2 * n) {i : ℕ} {c : Row n}
  {blocks : List ℕ} (h_blocks : Even blocks.length) (hc : c.blocks = blocks) (hk : ∀ x ∈ blocks, 2 * n < x + k)
  : ((Row.operationOneBased hk1 hkn)^[i] c).blocks = (blocks.reverse.rotate i).reverse := by
    induction' i with i hi
    · rw [Function.iterate_zero, id, List.rotate_zero, List.reverse_reverse]
      exact hc
    · rw [Function.iterate_succ_apply']
      have h_length : (blocks.reverse.rotate i).reverse.length = blocks.length := by
        rw [List.length_reverse, List.length_rotate, List.length_reverse]
      have h_blocks' : (blocks.reverse.rotate i).reverse ≠ [] := by
        rw [← List.length_pos_iff_ne_nil, h_length, ← hc, Row.blocks, List.blocks, List.length_map, List.segments]
        rw [List.length_pos_iff, List.splitBy_eq_nil.ne, ← List.length_pos_iff]
        rw [List.length_ofFn]
        lia
      have h_sum : (blocks.reverse.rotate i).reverse.sum = 2 * n := by
        rw [List.sum_reverse, List.sum_rotate, List.sum_reverse, ← hc, Row.sum_blocks]
      have h' : k - 1 < (blocks.reverse.rotate i).reverse.sum := by
        rw [h_sum]
        lia
      have h'' : (blocks.reverse.rotate i).reverse.getLast h_blocks' ∈ blocks := by
        rw [← List.mem_reverse, ← @List.mem_rotate _ _ _ i, ← List.mem_reverse]
        apply List.getLast_mem
      have hk := hk _ h''
      have h : indexInBlock (blocks.reverse.rotate i).reverse (k - 1) = (blocks.reverse.rotate i).reverse.length - 1 := by
        apply indexInBlock_eq_length_sub_one_of _ h_blocks' _ _ h'
        rw [h_sum]
        lia
      have h' : Even (blocks.reverse.rotate i).reverse.length := by
        rw [h_length]
        exact h_blocks
      rw [Row.blocks_operationOneBased_eq_rotate_one_blocks_of hk1 hkn h' hi h ]
      rw [List.reverse_reverse, List.rotate_rotate]

lemma Row.length_blocks_operationOneBased_lt_of_odd_last
  {n k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ 2 * n) {c : Row n}
  {blocks : List ℕ} (h_blocks : Odd blocks.length) (h_blocks' : 2 ≤ blocks.length) (hc : c.blocks = blocks) (hk : indexInBlock blocks (k - 1) = blocks.length - 1)
  : ((Row.operationOneBased hk1 hkn) c).blocks.length < blocks.length := by
    rw [Row.blocks, ofFn_operationOneBased_eq_operationOneBased_ofFn]
    rw [List.operationOneBased, List.operation, List.move]
    have h_mk : k - 1 < (List.ofFn c).length := by
      rw [List.length_ofFn]
      lia
    have h := List.blocks_operation_right_segment (List.ofFn c) ⟨k - 1, h_mk⟩
    rw [Row.blocks] at hc
    rw [List.blockIndex, hc, Fin.val_mk, hk, Nat.sub_add_cancel (by lia), List.drop_length, List.blocks] at h
    rw [List.map_eq_nil_iff, List.segments, List.splitBy_eq_nil] at h
    rw [h, List.append_nil]
    have h_ofFn_c : (List.ofFn c) ≠ [] := by
      rw [List.ne_nil_iff_length_pos, List.length_ofFn]
      lia
    have h_chainLeft : (List.chainLeft (List.ofFn c) ⟨k - 1, h_mk⟩).val ≠ 0 := by
      rw [List.chainLeft_eq, Nat.ne_zero_iff_zero_lt]
      apply List.sum_pos
      · intro x hx
        apply List.zero_lt_of_mem_blocks (List.ofFn c)
        apply List.mem_of_mem_take hx
      · rw [← List.length_eq_zero_iff.ne, List.length_take]
        rw [List.blockIndex, hc, Fin.val_mk, hk, Nat.ne_zero_iff_zero_lt, lt_min_iff]
        lia
    have h_blocks' : Even (blocks.length - 1) := by
      rw [Nat.even_sub (by lia)]
      norm_num
      exact h_blocks
    have h_eq : ∃ x ∈ (List.take (↑(List.chainRight (List.ofFn c) ⟨k - 1, h_mk⟩) + 1 - ↑(List.chainLeft (List.ofFn c) ⟨k - 1, h_mk⟩))
      (List.drop (↑(List.chainLeft (List.ofFn c) ⟨k - 1, h_mk⟩)) (List.ofFn c))).getLast?,
      ∃ y ∈ (List.take (↑(List.chainLeft (List.ofFn c) ⟨k - 1, h_mk⟩)) (List.ofFn c)).head?, (x == y) = true := by
      use if Even (List.blockIndex (List.ofFn c) ⟨k - 1, h_mk⟩) then (List.ofFn c).head h_ofFn_c else ((List.ofFn c).head h_ofFn_c).flip
      constructor
      · rw [List.blocks_operation_middle_getLast?, List.head?_eq_some_head h_ofFn_c]
        rw [Option.map_some, Option.mem_some]
      · use (List.ofFn c).head h_ofFn_c
        constructor
        · rw [List.blocks_operation_left_head? _ _ (by lia), List.head?_eq_some_head h_ofFn_c]
          rw [Option.mem_some]
        · rw [List.blockIndex, hc, hk, if_pos h_blocks', beq_iff_eq]
    apply lt_of_lt_of_le (List.length_blocks_append_lt_of h_eq)
    rw [List.blocks_operation_left_segment, List.blocks_operation_middle_segment]
    rw [List.length_take, List.length_take, List.blockIndex, hc, hk]
    apply le_trans (add_le_add_left (min_le_left _ _) _)
    apply le_trans (add_le_add_right (min_le_left _ _) _)
    lia

lemma Row.length_blocks_operationOneBased_lt_of_middle
  {n k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ 2 * n) {c : Row n}
  {blocks : List ℕ} (hc : c.blocks = blocks) (hk₁ : indexInBlock blocks (k - 1) ≠ 0) (hk₂ : indexInBlock blocks (k - 1) ≠ blocks.length - 1)
  : ((Row.operationOneBased hk1 hkn) c).blocks.length < blocks.length := by
    rw [Row.blocks] at hc
    have h_mk : k - 1 < (List.ofFn c).length := by
      rw [List.length_ofFn]
      lia
    rw [Row.blocks, ofFn_operationOneBased_eq_operationOneBased_ofFn]
    rw [List.operationOneBased, List.operation, List.move, List.append_assoc]
    apply lt_of_le_of_lt (List.length_blocks_append_le)
    rw [List.blocks_operation_middle_segment, List.length_take]
    apply lt_of_le_of_lt (add_le_add_left (min_le_left _ _) _)
    have h_ofFn_c : (List.ofFn c) ≠ [] := by
      rw [List.ne_nil_iff_length_pos, List.length_ofFn]
      lia
    have h_blocks := List.blockIndex_lt (List.ofFn c) ⟨k - 1, h_mk⟩
    rw [List.blockIndex, Fin.val_mk, hc] at h_blocks
    have h_chainLeft : (List.chainLeft (List.ofFn c) ⟨k - 1, h_mk⟩).val ≠ 0 := by
      rw [List.chainLeft_eq, Nat.ne_zero_iff_zero_lt]
      apply List.sum_pos
      · intro x hx
        apply List.zero_lt_of_mem_blocks (List.ofFn c)
        apply List.mem_of_mem_take hx
      · rw [← List.length_eq_zero_iff.ne, List.length_take]
        rw [List.blockIndex, hc, Fin.val_mk, min_eq_left_of_lt h_blocks]
        lia
    have h_chainRight : (List.chainRight (List.ofFn c) ⟨k - 1, h_mk⟩).val ≠ (List.ofFn c).length - 1 := by
      rw [← (@Nat.add_left_inj _ _ 1).ne, List.chainRight_succ_eq, Nat.sub_add_cancel (by lia)]
      simp only [← List.sum_blocks]
      rw [← List.sum_take_add_sum_drop (List.blocks (List.ofFn c)) (List.blockIndex (List.ofFn c) ⟨k - 1, h_mk⟩ + 1)]
      symm
      rw [Nat.add_eq_left.ne, Nat.ne_zero_iff_zero_lt]
      apply List.sum_pos
      · intro x hx
        apply List.zero_lt_of_mem_blocks (List.ofFn c)
        apply List.mem_of_mem_drop hx
      · rw [← List.length_eq_zero_iff.ne, List.length_drop]
        rw [List.blockIndex, hc, Fin.val_mk]
        lia
    have h_eq : ∃ x ∈ (List.take (↑(List.chainLeft (List.ofFn c) ⟨k - 1, h_mk⟩)) (List.ofFn c)).getLast?,
      ∃ y ∈ (List.drop (↑(List.chainRight (List.ofFn c) ⟨k - 1, h_mk⟩) + 1) (List.ofFn c)).head?, (x == y) = true := by
        use if Even (List.blockIndex (List.ofFn c) ⟨k - 1, h_mk⟩) then ((List.ofFn c).head h_ofFn_c).flip else (List.ofFn c).head h_ofFn_c
        constructor
        · rw [List.blocks_operation_left_getLast? _ _ h_chainLeft, List.head?_eq_some_head h_ofFn_c]
          rw [Option.map_some, Option.mem_some]
        · use if Even (List.blockIndex (List.ofFn c) ⟨k - 1, h_mk⟩) then ((List.ofFn c).head h_ofFn_c).flip else (List.ofFn c).head h_ofFn_c
          constructor
          · rw [List.blocks_operation_right_head? _ _ h_chainRight, List.head?_eq_some_head h_ofFn_c]
            rw [Option.map_some, Option.mem_some]
          · rw [beq_iff_eq]
    apply lt_of_lt_of_le (add_lt_add_right (List.length_blocks_append_lt_of h_eq) _)
    rw [List.blocks_operation_left_segment, List.length_take]
    rw [List.blocks_operation_right_segment, List.length_drop]
    rw [hc, List.blockIndex, add_left_comm]
    apply le_trans (add_le_add_left (min_le_left _ _) _)
    have h := List.blockIndex_lt (List.ofFn c) ⟨k - 1, h_mk⟩
    rw [hc, List.blockIndex] at h
    lia

lemma Row.exists_length_blocks_operationOneBased_iterate_lt_of
  {n k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ 2 * n) {c : Row n}
  {blocks : List ℕ} (h_blocks : Even blocks.length)
  (hc : c.blocks = blocks) (h_blocks' : ∀ x ∈ blocks, x ≤ k - 1)
  {m : ℕ} (hm : blocks.reverse.findIdx? (fun x ↦ x + k ≤ 2 * n) = some m)
  : ∃ i, ((Row.operationOneBased hk1 hkn)^[i] c).blocks.length < c.blocks.length := by
  induction' m with m h generalizing blocks c
  · use 1
    rw [Function.iterate_one]
    rw [List.findIdx?_eq_some_iff_getElem] at hm
    rcases hm with ⟨h_length, h_last, h_no⟩
    rw [decide_eq_true_iff, List.getElem_zero, List.head_reverse] at h_last
    have h_blocks'' : c.blocks ≠ [] := by
      rw [Row.blocks, List.blocks, List.map_eq_nil_iff.ne, List.segments]
      rw [List.splitBy_eq_nil.ne, List.ofFn_eq_nil_iff.ne]
      lia
    have h₁ : indexInBlock c.blocks (k - 1) ≠ 0 := by
      rw [indexInBlock, ne_eq, Finset.max'_eq_iff]
      simp
      use 1
      constructorm* _ ∧ _
      · rw [Nat.one_le_iff_ne_zero, List.length_eq_zero_iff.ne]
        exact h_blocks''
      · rw [List.take_one, List.head?_eq_some_head h_blocks'']
        rw [Option.toList_some, List.sum_singleton]
        apply h_blocks'
        rw [← hc]
        apply List.head_mem
      · norm_num
    have h_sum := Row.sum_blocks c
    have h₂ : indexInBlock c.blocks (k - 1) ≠ c.blocks.length - 1 := by
      contrapose! h_last
      rw [indexInBlock, Finset.max'_eq_iff] at h_last
      simp at h_last
      rw [← List.sum_take_add_sum_drop c.blocks (c.blocks.length - 1)] at h_sum
      rw [List.drop_length_sub_one h_blocks'', List.sum_singleton] at h_sum
      lia
    apply Row.length_blocks_operationOneBased_lt_of_middle _ _ rfl h₁ h₂
  · rw [List.findIdx?_eq_some_iff_getElem] at hm
    rcases hm with ⟨h_length, h_some, h_no⟩
    have h_blocks'' : blocks ≠ [] := by
      rw [← hc, Row.blocks, List.blocks, List.map_eq_nil_iff.ne, List.segments]
      rw [List.splitBy_eq_nil.ne, List.ofFn_eq_nil_iff.ne]
      lia
    have h_last := h_no 0 (by lia)
    rw [decide_eq_true_iff, List.getElem_zero, List.head_reverse] at h_last
    have h₁ : indexInBlock blocks (k - 1) = blocks.length - 1 := by
      apply indexInBlock_eq_length_sub_one_of _ h_blocks''
      · simp only [← hc, Row.sum_blocks]
        lia
      · rw [← hc, Row.sum_blocks]
        lia
    have h' := Row.blocks_operationOneBased_eq_rotate_one_blocks_of hk1 hkn h_blocks hc h₁
    have h_rot_blocks : Even (blocks.reverse.rotate 1).reverse.length := by
      rw [List.length_reverse, List.length_rotate, List.length_reverse]
      exact h_blocks
    have h_rot_blocks' : ∀ x ∈ (blocks.reverse.rotate 1).reverse, x ≤ k - 1 := by
      intro x hx
      apply h_blocks'
      rw [List.mem_reverse, List.mem_rotate, List.mem_reverse] at hx
      exact hx
    have hm' : m < (blocks.reverse.rotate 1).length := by
      rw [List.length_rotate]
      lia
    have h_rot_m : (blocks.reverse.rotate 1).reverse.reverse.findIdx? (fun x ↦ x + k ≤ 2 * n) = some m := by
      rw [List.reverse_reverse ,List.findIdx?_eq_some_iff_getElem]
      use hm'
      constructor
      · rw [List.getElem_rotate]
        simp only [Nat.mod_eq_of_lt h_length]
        exact h_some
      · intro j hj
        rw [List.getElem_rotate]
        simp only [Nat.mod_eq_of_lt (by lia : j + 1 < blocks.reverse.length)]
        apply h_no (j + 1)
        lia
    have h'' := h h_rot_blocks h' h_rot_blocks' h_rot_m
    rcases h'' with ⟨i, hi⟩
    use i + 1
    rw [Function.iterate_add_apply, Function.iterate_one]
    apply lt_of_lt_of_le hi
    rw [h', List.length_reverse, List.length_rotate, List.length_reverse, hc]

lemma Row.exists_length_blocks_operationOneBased_iterate_lt
  {n k : ℕ} (hn : 0 < n) (hk₁ : n ≤ k) (hk₂ : k ≤ 3 * n ⌈/⌉ 2)
  {c : Row n} (hc : c.valid) (hc' : 2 < c.blocks.length)
  : ∃ i, ((Row.operationOneBased (by lia : 1 ≤ k) (by rw [Nat.ceilDiv_eq_add_pred_div] at hk₂; lia))^[i] c).blocks.length < c.blocks.length := by
    rcases Row.ofBlocks_blocks c with ⟨head, h_head⟩
    have h₁ : indexInBlock c.blocks (k - 1) ≠ 0 := by
      rw [indexInBlock, ne_eq, Finset.max'_eq_iff]
      simp
      use 1
      constructorm* _ ∧ _
      · lia
      · rw [← h_head, Row.ofBlocks_valid_iff_alternateSum_eq _ _ _ true] at hc
        have h := List.take_append_drop 3 c.blocks
        rcases (@List.length_eq_three _ (List.take 3 c.blocks)).mp (by rw [List.length_take, min_eq_left (by lia)]) with ⟨p, q, r, hpqr⟩
        rw [← h, hpqr] at ⊢ hc
        rw [List.cons_append, List.cons_append, List.cons_append] at hc
        rw [List.alternateSum, List.alternateSum, List.alternateSum] at hc
        rw [if_pos rfl, if_neg (by decide), if_pos (by decide), zero_add] at hc
        rw [List.take_one, List.cons_append, List.head?_cons, Option.toList_some, List.sum_singleton]
        rw [Nat.le_sub_one_iff_lt (by lia)]
        apply lt_of_le_of_lt' hk₁
        rw [← hc, Nat.lt_add_right_iff_pos]
        apply Nat.add_pos_left
        rw [Row.blocks] at hpqr
        apply List.zero_lt_of_mem_blocks (List.ofFn c)
        apply @List.mem_of_mem_take _ 3
        rw [hpqr]
        apply List.mem_cons_of_mem
        apply List.mem_cons_of_mem
        apply List.mem_singleton_self
      · norm_num
    by_cases! h₂ : indexInBlock c.blocks (k - 1) = c.blocks.length - 1
    · by_cases! h₃ : Odd c.blocks.length
      · use 1
        rw [Function.iterate_one]
        apply Row.length_blocks_operationOneBased_lt_of_odd_last _ _ h₃ (by lia) rfl h₂
      · rw [Nat.not_odd_iff_even] at h₃
        have h_mem : ∀ x ∈ c.blocks, 0 < x := by
          intro x hx
          rw [Row.blocks] at hx
          apply List.zero_lt_of_mem_blocks (List.ofFn c) _ hx
        have h_length' : c.blocks.length ≠ 3 := by
          contrapose! h₃
          rw [h₃]
          norm_num
        have h_length : 4 ≤ c.blocks.length := by
          lia
        have h_sum := Row.sum_blocks c
        have h₄ : ∀ x ∈ c.blocks, x ≤ k - 1 := by
          intro x hx
          apply Nat.le_sub_one_of_lt
          apply lt_of_lt_of_le (List.lt_alternateSum_of_nat_mem _ _ hx h_mem h_length)
          rw [← h_head] at hc
          rw [(Row.ofBlocks_valid_iff_alternateSum_eq _ _ h_sum true).mp hc]
          rw [(Row.ofBlocks_valid_iff_alternateSum_eq _ _ h_sum false).mp hc]
          rw [max_self]
          exact hk₁
        have h_c : c.blocks ≠ [] := by
          rw [List.ne_nil_iff_length_pos]
          lia
        have h_exists : ∃ x ∈ c.blocks.reverse, decide (x + k ≤ 2 * n) = true := by
          use c.blocks.min h_c
          constructor
          · rw [List.mem_reverse]
            apply List.min_mem
          · rw [decide_eq_true_iff]
            apply le_trans (add_le_add_left (List.min_le_sum_div_length_nat h_c) _)
            rw [h_sum]
            apply le_trans (add_le_add_left (Nat.div_le_div_left h_length (by norm_num)) _)
            rw [Nat.ceilDiv_eq_add_pred_div] at hk₂
            lia
        have h₅ := List.findIdx?_eq_some_of_exists h_exists
        apply Row.exists_length_blocks_operationOneBased_iterate_lt_of _ _ h₃ rfl h₄ h₅
    · use 1
      rw [Function.iterate_one]
      apply Row.length_blocks_operationOneBased_lt_of_middle _ _ rfl h₁ h₂

lemma Row.exists_length_blocks_operationOneBased_iterate_eq_two
  {n k : ℕ} (hn : 0 < n) (hk₁ : n ≤ k) (hk₂ : k ≤ 3 * n ⌈/⌉ 2)
  {c : Row n} (hc : c.valid) {l : ℕ} (hl : l = c.blocks.length)
  : ∃ i, ((Row.operationOneBased (by lia : 1 ≤ k) (by rw [Nat.ceilDiv_eq_add_pred_div] at hk₂; lia))^[i] c).blocks.length = 2 := by
    induction' l using Nat.strong_induction_on with l h generalizing c
    by_cases! hl' : l ≤ 2
    · use 0
      rw [Function.iterate_zero, id]
      rw [hl] at hl'
      apply le_antisymm hl'
      rcases Row.ofBlocks_blocks c with ⟨head, h_head⟩
      rw [← h_head, Row.ofBlocks_valid_iff_alternateSum_eq _ _ _ false] at hc
      contrapose! hc
      by_cases! hc'' : c.blocks.length = 0
      · rw [List.length_eq_zero_iff] at hc''
        rw [hc'', List.alternateSum]
        lia
      · have hc''' : c.blocks.length = 1 := by
          lia
        rw [List.length_eq_one_iff] at hc'''
        rcases hc''' with ⟨i, hi⟩
        rw [hi, List.alternateSum, List.alternateSum, if_neg (by decide)]
        lia
    · rw [hl] at hl'
      have h' := Row.exists_length_blocks_operationOneBased_iterate_lt hn hk₁ hk₂ hc hl'
      rcases h' with ⟨i, hi⟩
      set c' := ((operationOneBased (by lia : 1 ≤ k) (by rw [Nat.ceilDiv_eq_add_pred_div] at hk₂; lia))^[i] c) with hc'
      rw [← hl] at hi
      have h'c' : c'.valid := by
        rw [hc']
        apply Row.operationOneBased_iterate_valid hc
      have h'' := h c'.blocks.length hi h'c' rfl
      rcases h'' with ⟨j, hj⟩
      use j + i
      rw [Function.iterate_add_apply]
      rw [← hc', hj]


/-- The answer to be determined. -/
abbrev answer : Set (ℕ × ℕ) := {(n, k) : ℕ × ℕ | 0 < n ∧ n ≤ k ∧ k ≤ 3 * n ⌈/⌉ 2}

theorem imo2022_p1 : {(n, k) | ∃ hk1 : 1 ≤ k, ∃ hkn : k ≤ 2 * n, ∀ c : Row n, c.valid →
    ∃ i, ((Row.operationOneBased hk1 hkn)^[i] c).leftmostNSame} =
    answer := by
  rw [answer]
  ext ⟨n, k⟩
  dsimp
  constructor
  · intro h
    contrapose! +distrib h
    intro hk1 hkn
    have hn : 0 < n := by lia
    have : NeZero n := NeZero.of_pos hn
    have hcounter {c : Row n} (hc : c.valid)
      (hlen : ∀ i, ((Row.operationOneBased hk1 hkn)^[i] c).blocks.length ≠ 2) :
      ∃ c : Row n, c.valid ∧ ∀ i, ¬ ((Row.operationOneBased hk1 hkn)^[i] c).leftmostNSame := by
        refine ⟨c, hc, ?_⟩
        intro i hi
        have hic := Row.operationOneBased_iterate_valid hc hk1 hkn i
        rw [Row.leftmostNSame_iff_length_blocks_ofFn_of_valid hic] at hi
        exact hlen i hi
    rw [or_iff_right (show ¬ n ≤ 0 by lia)] at h
    rcases h with h | h
    · set blocks := [k, n, n - k] with h_blocks
      have h_blocks' : blocks.sum = 2 * n := by
        rw [h_blocks, List.sum_cons, List.sum_pair]
        lia
      set c := Row.ofBlocks blocks Coin.A h_blocks' with hc
      have hc' : c.valid := by
        rw [hc, Row.ofBlocks_valid_iff_alternateSum_eq blocks Coin.A h_blocks' false]
        simp [h_blocks, List.alternateSum]
      refine hcounter hc' ?_
      intro i
      have h_blocks'' : ∀ x ∈ blocks, 0 < x := by
        intro x hx
        rw [h_blocks] at hx
        simp at hx
        rcases hx with rfl | rfl | rfl <;> lia
      have h_fixed : ((Row.operationOneBased hk1 hkn)^[i] c).blocks = blocks := by
        apply Row.blocks_operationOneBased_iterate_eq_blocks_of hk1 hkn
        · rw [hc]
          exact Row.blocks_ofBlocks _ _ h_blocks' h_blocks''
        · rw [indexInBlock, Finset.max'_eq_iff]
          simp
          intro j hj₁ hj₂
          contrapose! hj₂
          rw [Nat.sub_lt_iff_lt_add hk1, Nat.lt_succ_iff]
          rw [← Nat.one_le_iff_ne_zero] at hj₂
          rw [← List.sum_take_add_sum_drop (List.take j blocks) 1]
          rw [List.take_take, min_eq_left hj₂]
          apply le_add_of_le_left
          rw [h_blocks, List.take_succ_cons, List.take_zero, List.sum_singleton]
      simp [h_fixed, h_blocks]
    · set blocks := [n ⌈/⌉ 2, n ⌈/⌉ 2, n ⌊/⌋ 2, n ⌊/⌋ 2] with h_blocks
      have h_blocks' : blocks.sum = 2 * n := by
        rw [h_blocks, List.sum_cons, List.sum_cons, List.sum_pair]
        nth_rw 5 [← Nat.ceilDiv_two_add_floorDiv_two n]
        ring
      set c := Row.ofBlocks blocks Coin.A h_blocks' with hc
      have hc' : c.valid := by
        rw [hc, Row.ofBlocks_valid_iff_alternateSum_eq blocks Coin.A h_blocks' false]
        simp [h_blocks, List.alternateSum, -Nat.floorDiv_eq_div]
        exact Nat.ceilDiv_two_add_floorDiv_two n
      refine hcounter hc' ?_
      intro i
      have h_blocks'' : ∀ x ∈ blocks, 0 < x := by
        intro x hx
        rw [h_blocks] at hx
        simp at hx
        rw [Nat.ceilDiv_eq_add_pred_div] at h
        rcases hx with rfl | rfl
        · rw [Nat.ceilDiv_eq_add_pred_div]
          lia
        · lia
      have h_large : ∀ x ∈ blocks, 2 * n < x + k := by
        intro x hx
        rw [h_blocks] at hx
        simp at hx
        rw [Nat.ceilDiv_eq_add_pred_div] at h
        rcases hx with rfl | rfl
        · rw [Nat.ceilDiv_eq_add_pred_div]
          lia
        · lia
      have h_rotate : ((Row.operationOneBased hk1 hkn)^[i] c).blocks = (blocks.reverse.rotate i).reverse := by
        apply Row.blocks_operationOneBased_iterate_eq_rotate_blocks_of hk1 hkn
        · rw [h_blocks, List.length_cons, List.length_cons, List.length_cons, List.length_singleton]
          norm_num
        · rw [hc]
          exact Row.blocks_ofBlocks _ _ h_blocks' h_blocks''
        · exact h_large
      simp [h_rotate, h_blocks]
  · rintro ⟨hn, hk₁, hk₂⟩
    have hk1 : 1 ≤ k := by lia
    have hkn : k ≤ 2 * n := by
      apply le_trans hk₂
      rw [ceilDiv_le_iff_le_mul (by norm_num)]
      lia
    use hk1
    use hkn
    intro c hc
    rcases Row.exists_length_blocks_operationOneBased_iterate_eq_two hn hk₁ hk₂ hc rfl with ⟨i, hi⟩
    refine ⟨i, ?_⟩
    have hic := Row.operationOneBased_iterate_valid hc hk1 hkn i
    have hnz : NeZero n := NeZero.of_pos hn
    rw [Row.leftmostNSame_iff_length_blocks_ofFn_of_valid hic]
    exact hi

end Imo2022P1
