/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Ring
public import ProblemExtraction

@[expose] public section

problem_file {
  tags := [.Combinatorics]
}

/-!
# USA Mathematical Olympiad 2010, Problem 2

There are $n$ students standing in a circle, one behind the other. The students
have heights $h_1 < h_2 < \dots < h_n$. If a student with height $h_k$ is
standing directly behind a student with height $h_{k-2}$ or less, the two
students are permitted to switch places. Prove that it is not possible to make
more than $\binom{n}{3}$ such switches before reaching a position in which no
further switches are possible.
-/

namespace Usa2010P2

snip begin

/-!
## Model

We label the students by their height rank, i.e. by an element of `Fin n`
(student `i` has height `h_{i+1}`).  Since the heights are strictly increasing,
only the relative order of the heights matters.

The circle is modeled by positions in `ZMod n`: position `p + 1` is directly
behind position `p`.  A configuration is an equivalence `e : Fin n ≃ ZMod n`
assigning to each student their position.

A sequence of switches is a list of positions `ps : List (ZMod n)`; the switch
at position `p` exchanges the students at positions `p` (in front) and `p + 1`
(directly behind), and it is permitted exactly when the rank of the student in
front plus two is at most the rank of the student behind
(i.e. the student behind has height `h_k` and the student in front has height
at most `h_{k-2}`).
-/

/-- A sequence of permitted switches starting from configuration `e`. -/
def Legal {n : ℕ} : (Fin n ≃ ZMod n) → List (ZMod n) → Prop
  | _, [] => True
  | e, p :: ps =>
      (e.symm p).val + 2 ≤ (e.symm (p + 1)).val ∧
      Legal (e.trans (Equiv.swap p (p + 1))) ps

/-- The sequence of pairs of students that switch places: each entry is
`(student in front, student behind)`, with front rank `<` behind rank. -/
def evPairs {n : ℕ} : (Fin n ≃ ZMod n) → List (ZMod n) → List (Fin n × Fin n)
  | _, [] => []
  | e, p :: ps =>
      (e.symm p, e.symm (p + 1)) :: evPairs (e.trans (Equiv.swap p (p + 1))) ps

/-- The cyclic-order state of a triple of students: going backwards from `a`
we meet `b` before meeting `c`. -/
def StateA {n : ℕ} (e : Fin n ≃ ZMod n) (a b c : Fin n) : Prop :=
  (e b - e a).val < (e c - e a).val

instance {n : ℕ} (e : Fin n ≃ ZMod n) (a b c : Fin n) : Decidable (StateA e a b c) :=
  inferInstanceAs (Decidable ((e b - e a).val < (e c - e a).val))

/-! ### Elementary facts about `ZMod.val` -/

lemma val_one' {n : ℕ} (hn : 2 ≤ n) : (1 : ZMod n).val = 1 := by
  have : NeZero n := ⟨by omega⟩
  rw [← Nat.cast_one]
  exact ZMod.val_natCast_of_lt (by omega)

lemma val_neg_one' {n : ℕ} (hn : 1 ≤ n) : (-1 : ZMod n).val = n - 1 := by
  have : NeZero n := ⟨by omega⟩
  have h : (-1 : ZMod n) = ((n - 1 : ℕ) : ZMod n) := by
    rw [Nat.cast_sub hn, Nat.cast_one, ZMod.natCast_self, zero_sub]
  rw [h]
  exact ZMod.val_natCast_of_lt (by omega)

lemma val_add_one' {n : ℕ} (hn : 2 ≤ n) (x : ZMod n) (hx : x ≠ -1) :
    (x + 1).val = x.val + 1 := by
  have : NeZero n := ⟨by omega⟩
  have h1 : x.val < n := ZMod.val_lt x
  have h2 : x.val ≠ n - 1 := by
    intro hbad
    exact hx (ZMod.val_injective n (by rw [val_neg_one' (by omega : 1 ≤ n)]; omega))
  rw [ZMod.val_add, val_one' hn, Nat.mod_eq_of_lt (by omega)]

lemma val_sub_one' {n : ℕ} (hn : 1 ≤ n) (x : ZMod n) (hx : x ≠ 0) :
    (x - 1).val = x.val - 1 := by
  have : NeZero n := ⟨by omega⟩
  have h1 : x.val ≠ 0 := by
    intro hbad
    exact hx ((ZMod.val_eq_zero x).mp hbad)
  have h2 : x.val < n := ZMod.val_lt x
  rw [sub_eq_add_neg, ZMod.val_add, val_neg_one' hn,
    show x.val + (n - 1) = x.val - 1 + n by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)]

lemma val_sub_ne_of_ne {n : ℕ} [NeZero n] {q r s : ZMod n} (h : q ≠ r) :
    (q - s).val ≠ (r - s).val := by
  intro hbad
  exact h (sub_left_inj.mp (ZMod.val_injective n hbad))

lemma val_sub_pos_of_ne {n : ℕ} [NeZero n] {q r : ZMod n} (h : q ≠ r) :
    1 ≤ (q - r).val := by
  have h1 : q - r ≠ 0 := sub_ne_zero_of_ne h
  have h2 : (q - r).val ≠ 0 := fun hbad => h1 ((ZMod.val_eq_zero _).mp hbad)
  exact Nat.one_le_iff_ne_zero.mpr h2

lemma eq_of_sub_eq_neg_one {n : ℕ} {q r : ZMod n} (h : q - r = -1) : r = q + 1 := by
  have h2 : q = -1 + r := sub_eq_iff_eq_add.mp h
  have h3 : q + 1 = r := by rw [h2]; ring
  exact h3.symm

/-! ### The cyclic-order state of a triple under one switch -/

/-- L1: if `b` is directly behind `a`, then going backwards from `a` we meet
`b` before any third student `c`. -/
lemma stateA_of_pair {n : ℕ} (hn : 2 ≤ n) {a b c : Fin n} {e : Fin n ≃ ZMod n} {p : ZMod n}
    (hea : e a = p) (heb : e b = p + 1) (hac : a ≠ c) (hbc : b ≠ c) :
    StateA e a b c := by
  have : NeZero n := ⟨by omega⟩
  have h1 : (e b - e a).val = 1 := by
    rw [heb, hea, add_sub_cancel_left]
    exact val_one' hn
  have h2 : 2 ≤ (e c - e a).val := by
    have hne0 := val_sub_pos_of_ne (fun hbad : e c = e a => hac (e.injective hbad).symm)
    have hne1 : (e c - e a).val ≠ 1 := by
      intro hbad
      have heq : e c - e a = 1 := ZMod.val_injective n (by rw [val_one' hn]; exact hbad)
      have : e c = e b := by
        have ht : e c = 1 + e a := sub_eq_iff_eq_add.mp heq
        rw [ht, hea, heb, add_comm]
      exact hbc (e.injective this).symm
    omega
  unfold StateA
  rw [h1]
  exact h2

/-- L2: if `b` is directly behind `c`, the triple is not in state A. -/
lemma not_stateA_of_pair {n : ℕ} (hn : 2 ≤ n) {a b c : Fin n} {e : Fin n ≃ ZMod n} {p : ZMod n}
    (hec : e c = p) (heb : e b = p + 1) (hab : a ≠ b) :
    ¬ StateA e a b c := by
  have : NeZero n := ⟨by omega⟩
  have h : (e c - e a).val < (e b - e a).val := by
    have h1 : e b - e a = (e c - e a) + 1 := by rw [heb, hec]; ring
    have hne : e c - e a ≠ -1 := by
      intro hbad
      rw [hbad, neg_add_cancel] at h1
      exact hab (e.injective (sub_eq_zero.mp h1)).symm
    rw [h1, val_add_one' hn _ hne]
    exact Nat.lt_succ_self _
  intro hA
  unfold StateA at hA
  exact (not_lt_of_gt h) hA

/-- L3: after `b` (behind) and `a` (front) switch, the triple is not in state A. -/
lemma not_stateA_swap {n : ℕ} (hn : 2 ≤ n) {a b c : Fin n} {e : Fin n ≃ ZMod n} {p : ZMod n}
    (hea : e a = p) (heb : e b = p + 1) (hca : c ≠ a) (hcb : c ≠ b) :
    ¬ StateA (e.trans (Equiv.swap p (p + 1))) a b c := by
  have : NeZero n := ⟨by omega⟩
  have h1 : (e.trans (Equiv.swap p (p + 1))) a = p + 1 := by
    rw [Equiv.trans_apply, hea]
    exact Equiv.swap_apply_left _ _
  have h2 : (e.trans (Equiv.swap p (p + 1))) b = p := by
    rw [Equiv.trans_apply, heb]
    exact Equiv.swap_apply_right _ _
  have hcp : e c ≠ p := fun hbad => hca (e.injective (hbad.trans hea.symm))
  have hcq : e c ≠ p + 1 := fun hbad => hcb (e.injective (hbad.trans heb.symm))
  have h3 : (e.trans (Equiv.swap p (p + 1))) c = e c := by
    rw [Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne hcp hcq]
  have h6 : (p : ZMod n) - (p + 1) = -1 := by ring
  have h5 : (e c - (p + 1)).val ≠ n - 1 := by
    intro hbad
    have heq : e c - (p + 1) = p - (p + 1) := by
      apply ZMod.val_injective n
      rw [h6, val_neg_one' (by omega : 1 ≤ n)]
      exact hbad
    exact hcp (sub_left_inj.mp heq)
  intro hA
  unfold StateA at hA
  rw [h1, h2, h3, h6, val_neg_one' (by omega : 1 ≤ n)] at hA
  have h7 : (e c - (p + 1)).val < n := ZMod.val_lt _
  omega

/-- L4: after `b` (behind) and `c` (front) switch, the triple is in state A. -/
lemma stateA_swap {n : ℕ} (hn : 2 ≤ n) {a b c : Fin n} {e : Fin n ≃ ZMod n} {p : ZMod n}
    (hec : e c = p) (heb : e b = p + 1) (hac : a ≠ c) (hab : a ≠ b) :
    StateA (e.trans (Equiv.swap p (p + 1))) a b c := by
  have : NeZero n := ⟨by omega⟩
  have h1 : (e.trans (Equiv.swap p (p + 1))) c = p + 1 := by
    rw [Equiv.trans_apply, hec]
    exact Equiv.swap_apply_left _ _
  have h2 : (e.trans (Equiv.swap p (p + 1))) b = p := by
    rw [Equiv.trans_apply, heb]
    exact Equiv.swap_apply_right _ _
  have hap : e a ≠ p := fun hbad => hac (e.injective (hbad.trans hec.symm))
  have haq : e a ≠ p + 1 := fun hbad => hab (e.injective (hbad.trans heb.symm))
  have h3 : (e.trans (Equiv.swap p (p + 1))) a = e a := by
    rw [Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne hap haq]
  unfold StateA
  rw [h2, h3, h1]
  have h4 : ((p : ZMod n) + 1 - e a) = (p - e a) + 1 := by ring
  have hne : p - e a ≠ -1 := by
    intro hbad
    have hcon : e a = p + 1 := eq_of_sub_eq_neg_one hbad
    exact haq hcon
  rw [h4, val_add_one' hn _ hne]
  exact Nat.lt_succ_self _

/-- L5: a permitted switch that involves neither the pair `(a, b)` nor the pair
`(c, b)` preserves the cyclic-order state of the triple `{a, c, b}`. -/
lemma stateA_swap_iff {n : ℕ} (hn : 2 ≤ n) {a b c : Fin n} {e : Fin n ≃ ZMod n} {p : ZMod n}
    (hc : c.val = a.val + 1) (hab : a.val + 2 ≤ b.val) (hcb : c.val < b.val)
    (hleg : (e.symm p).val + 2 ≤ (e.symm (p + 1)).val)
    (hJ : (e.symm p, e.symm (p + 1)) ≠ (a, b))
    (hM : (e.symm p, e.symm (p + 1)) ≠ (c, b)) :
    StateA (e.trans (Equiv.swap p (p + 1))) a b c ↔ StateA e a b c := by
  have : NeZero n := ⟨by omega⟩
  have hbval : b.val < n := b.isLt
  have hac : a ≠ c := by
    intro hbad
    rw [hbad] at hc
    omega
  have hab' : a ≠ b := by
    intro hbad
    rw [hbad] at hab
    omega
  have hcb' : c ≠ b := by
    intro hbad
    rw [hbad] at hcb
    exact lt_irrefl _ hcb
  have hune : (e b - e a).val ≠ (e c - e a).val :=
    val_sub_ne_of_ne (fun hbad => hcb' (e.injective hbad).symm)
  have hu1 : 1 ≤ (e b - e a).val := val_sub_pos_of_ne (fun hbad => hab' (e.injective hbad).symm)
  have hv1 : 1 ≤ (e c - e a).val := val_sub_pos_of_ne (fun hbad => hac (e.injective hbad).symm)
  set e₁ := e.trans (Equiv.swap p (p + 1)) with he₁
  have hu'ne : (e₁ b - e₁ a).val ≠ (e₁ c - e₁ a).val :=
    val_sub_ne_of_ne (fun hbad => hcb' (e₁.injective hbad).symm)
  have hye : e (e.symm p) = p := Equiv.apply_symm_apply _ _
  have hxe : e (e.symm (p + 1)) = p + 1 := Equiv.apply_symm_apply _ _
  unfold StateA
  by_cases hya : e.symm p = a
  · -- `a` is in front and moves one step backwards; both distances drop by one
    have hea : e a = p := by rw [← hya]; exact hye
    have hxb : e.symm (p + 1) ≠ b := fun hbad =>
      hJ (by rw [Prod.mk.injEq]; exact ⟨hya, hbad⟩)
    have hxc : e.symm (p + 1) ≠ c := by
      intro hbad
      rw [hya, hbad, hc] at hleg
      omega
    have hbn : e b ≠ p := fun hbad => hab' (e.injective (hbad.trans hea.symm)).symm
    have hbq : e b ≠ p + 1 := fun hbad => hxb (e.injective (hbad.trans hxe.symm)).symm
    have hcn : e c ≠ p := fun hbad => hac (e.injective (hbad.trans hea.symm)).symm
    have hcq : e c ≠ p + 1 := fun hbad => hxc (e.injective (hbad.trans hxe.symm)).symm
    have h1 : e₁ a = p + 1 := by rw [he₁, Equiv.trans_apply, hea]; exact Equiv.swap_apply_left _ _
    have h2 : e₁ b = e b := by rw [he₁, Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne hbn hbq]
    have h3 : e₁ c = e c := by rw [he₁, Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne hcn hcq]
    rw [h1, h2, h3]
    have hb0 : e b - p ≠ 0 := sub_ne_zero_of_ne hbn
    have hc0 : e c - p ≠ 0 := sub_ne_zero_of_ne hcn
    have hrb : (e b - (p + 1) : ZMod n) = (e b - p) - 1 := by rw [sub_sub]
    have hrc : (e c - (p + 1) : ZMod n) = (e c - p) - 1 := by rw [sub_sub]
    rw [hrb, hrc, val_sub_one' (by omega : 1 ≤ n) _ hb0, val_sub_one' (by omega : 1 ≤ n) _ hc0,
      hea]
    have hub : 1 ≤ (e b - p).val := val_sub_pos_of_ne hbn
    have huc : 1 ≤ (e c - p).val := val_sub_pos_of_ne hcn
    omega
  · by_cases hyb : e.symm p = b
    · -- `b` is in front and moves one step backwards; the distance to `b` grows by one
      have heb : e b = p := by rw [← hyb]; exact hye
      have hxa : e.symm (p + 1) ≠ a := by
        intro hbad
        rw [hyb, hbad] at hleg
        omega
      have hxc : e.symm (p + 1) ≠ c := by
        intro hbad
        rw [hyb, hbad] at hleg
        omega
      have han : e a ≠ p := fun hbad => hab' (e.injective (hbad.trans heb.symm))
      have haq : e a ≠ p + 1 := fun hbad => hxa (e.injective (hbad.trans hxe.symm)).symm
      have hcn : e c ≠ p := fun hbad => hcb' (e.injective (hbad.trans heb.symm))
      have hcq : e c ≠ p + 1 := fun hbad => hxc (e.injective (hbad.trans hxe.symm)).symm
      have h1 : e₁ b = p + 1 := by rw [he₁, Equiv.trans_apply, heb]; exact Equiv.swap_apply_left _ _
      have h2 : e₁ a = e a := by rw [he₁, Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne han haq]
      have h3 : e₁ c = e c := by rw [he₁, Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne hcn hcq]
      rw [h1, h2, h3]
      have hrel : ((p : ZMod n) + 1 - e a) = (e b - e a) + 1 := by rw [heb]; ring
      have hne : e b - e a ≠ -1 := by
        intro hbad
        have hcon := eq_of_sub_eq_neg_one hbad
        rw [heb] at hcon
        exact haq hcon
      rw [hrel, val_add_one' hn _ hne]
      have hu'ne' := hu'ne
      rw [h1, h2, h3, hrel, val_add_one' hn _ hne] at hu'ne'
      omega
    · by_cases hyc : e.symm p = c
      · -- `c` is in front and moves one step backwards; the distance to `c` grows by one
        have hec : e c = p := by rw [← hyc]; exact hye
        have hxa : e.symm (p + 1) ≠ a := by
          intro hbad
          rw [hyc, hbad, hc] at hleg
          omega
        have hxb : e.symm (p + 1) ≠ b := fun hbad =>
          hM (by rw [Prod.mk.injEq]; exact ⟨hyc, hbad⟩)
        have han : e a ≠ p := fun hbad => hac (e.injective (hbad.trans hec.symm))
        have haq : e a ≠ p + 1 := fun hbad => hxa (e.injective (hbad.trans hxe.symm)).symm
        have hbn : e b ≠ p := fun hbad => hcb' (e.injective (hbad.trans hec.symm)).symm
        have hbq : e b ≠ p + 1 := fun hbad => hxb (e.injective (hbad.trans hxe.symm)).symm
        have h1 : e₁ c = p + 1 := by rw [he₁, Equiv.trans_apply, hec]; exact Equiv.swap_apply_left _ _
        have h2 : e₁ a = e a := by rw [he₁, Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne han haq]
        have h3 : e₁ b = e b := by rw [he₁, Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne hbn hbq]
        rw [h1, h2, h3]
        have hrel : ((p : ZMod n) + 1 - e a) = (e c - e a) + 1 := by rw [hec]; ring
        have hne : e c - e a ≠ -1 := by
          intro hbad
          have hcon := eq_of_sub_eq_neg_one hbad
          rw [hec] at hcon
          exact haq hcon
        rw [hrel, val_add_one' hn _ hne]
        have hu'ne' := hu'ne
        rw [h1, h2, h3, hrel, val_add_one' hn _ hne] at hu'ne'
        omega
      · by_cases hxa : e.symm (p + 1) = a
        · -- `a` is behind and moves one step forwards; both distances grow by one
          have hea : e a = p + 1 := by rw [← hxa]; exact hxe
          have hyb : e.symm p ≠ b := by
            intro hbad
            rw [hbad, hxa] at hleg
            omega
          have hyc : e.symm p ≠ c := by
            intro hbad
            rw [hbad, hxa, hc] at hleg
            omega
          have hbn : e b ≠ p := fun hbad => hyb (e.injective (hbad.trans hye.symm)).symm
          have hbnq : e b ≠ p + 1 := fun hbad => hab' (e.injective (hbad.trans hea.symm)).symm
          have hcn : e c ≠ p := fun hbad => hyc (e.injective (hbad.trans hye.symm)).symm
          have hcnq : e c ≠ p + 1 := fun hbad => hac (e.injective (hbad.trans hea.symm)).symm
          have h1 : e₁ a = p := by rw [he₁, Equiv.trans_apply, hea]; exact Equiv.swap_apply_right _ _
          have h2 : e₁ b = e b := by
            rw [he₁, Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne hbn hbnq]
          have h3 : e₁ c = e c := by
            rw [he₁, Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne hcn hcnq]
          rw [h1, h2, h3]
          have hrelb : (e b - p : ZMod n) = (e b - e a) + 1 := by rw [hea]; ring
          have hrelc : (e c - p : ZMod n) = (e c - e a) + 1 := by rw [hea]; ring
          have hneb : e b - e a ≠ -1 := by
            intro hbad
            have hcon := eq_of_sub_eq_neg_one hbad
            rw [hea] at hcon
            have hb_eq : e b = p := (add_right_cancel_iff.mp hcon).symm
            exact hbn hb_eq
          have hnec : e c - e a ≠ -1 := by
            intro hbad
            have hcon := eq_of_sub_eq_neg_one hbad
            rw [hea] at hcon
            have hc_eq : e c = p := (add_right_cancel_iff.mp hcon).symm
            exact hcn hc_eq
          rw [hrelb, hrelc, val_add_one' hn _ hneb, val_add_one' hn _ hnec]
          omega
        · by_cases hxb : e.symm (p + 1) = b
          · -- `b` is behind and moves one step forwards; the distance to `b` drops by one
            have heb : e b = p + 1 := by rw [← hxb]; exact hxe
            have hya' : e.symm p ≠ a := fun hbad =>
              hJ (by rw [Prod.mk.injEq]; exact ⟨hbad, hxb⟩)
            have hyc' : e.symm p ≠ c := fun hbad =>
              hM (by rw [Prod.mk.injEq]; exact ⟨hbad, hxb⟩)
            have han : e a ≠ p := fun hbad => hya' (e.injective (hbad.trans hye.symm)).symm
            have haq : e a ≠ p + 1 := fun hbad => hab' (e.injective (hbad.trans heb.symm))
            have hcn : e c ≠ p := fun hbad => hyc' (e.injective (hbad.trans hye.symm)).symm
            have hcq : e c ≠ p + 1 := fun hbad => hcb' (e.injective (hbad.trans heb.symm))
            have h1 : e₁ b = p := by rw [he₁, Equiv.trans_apply, heb]; exact Equiv.swap_apply_right _ _
            have h2 : e₁ a = e a := by
              rw [he₁, Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne han haq]
            have h3 : e₁ c = e c := by
              rw [he₁, Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne hcn hcq]
            rw [h1, h2, h3]
            have hrel : (p - e a : ZMod n) = (e b - e a) - 1 := by rw [heb]; ring
            have hb0 : e b - e a ≠ 0 := sub_ne_zero_of_ne (fun hbad => hab' (e.injective hbad).symm)
            rw [hrel, val_sub_one' (by omega : 1 ≤ n) _ hb0]
            have hu'ne' := hu'ne
            rw [h1, h2, h3, hrel, val_sub_one' (by omega : 1 ≤ n) _ hb0] at hu'ne'
            omega
          · by_cases hxc : e.symm (p + 1) = c
            · -- `c` is behind and moves one step forwards; the distance to `c` drops by one
              have hec : e c = p + 1 := by rw [← hxc]; exact hxe
              have hya' : e.symm p ≠ a := by
                intro hbad
                rw [hbad, hxc, hc] at hleg
                omega
              have hyb' : e.symm p ≠ b := by
                intro hbad
                rw [hbad, hxc] at hleg
                omega
              have han : e a ≠ p := fun hbad => hya' (e.injective (hbad.trans hye.symm)).symm
              have haq : e a ≠ p + 1 := fun hbad => hac (e.injective (hbad.trans hec.symm))
              have hbn : e b ≠ p := fun hbad => hyb' (e.injective (hbad.trans hye.symm)).symm
              have hbq : e b ≠ p + 1 := fun hbad => hcb' (e.injective (hbad.trans hec.symm)).symm
              have h1 : e₁ c = p := by
                rw [he₁, Equiv.trans_apply, hec]; exact Equiv.swap_apply_right _ _
              have h2 : e₁ a = e a := by
                rw [he₁, Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne han haq]
              have h3 : e₁ b = e b := by
                rw [he₁, Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne hbn hbq]
              rw [h1, h2, h3]
              have hrel : (p - e a : ZMod n) = (e c - e a) - 1 := by rw [hec]; ring
              have hc0 : e c - e a ≠ 0 := sub_ne_zero_of_ne (fun hbad => hac (e.injective hbad).symm)
              rw [hrel, val_sub_one' (by omega : 1 ≤ n) _ hc0]
              have hu'ne' := hu'ne
              rw [h1, h2, h3, hrel, val_sub_one' (by omega : 1 ≤ n) _ hc0] at hu'ne'
              omega
            · -- the switch does not involve the triple at all
              have han : e a ≠ p := fun hbad => hya (e.injective (hbad.trans hye.symm)).symm
              have haq : e a ≠ p + 1 := fun hbad => hxa (e.injective (hbad.trans hxe.symm)).symm
              have hbn : e b ≠ p := fun hbad => hyb (e.injective (hbad.trans hye.symm)).symm
              have hbq : e b ≠ p + 1 := fun hbad => hxb (e.injective (hbad.trans hxe.symm)).symm
              have hcn : e c ≠ p := fun hbad => hyc (e.injective (hbad.trans hye.symm)).symm
              have hcq : e c ≠ p + 1 := fun hbad => hxc (e.injective (hbad.trans hxe.symm)).symm
              have h1 : e₁ a = e a := by
                rw [he₁, Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne han haq]
              have h2 : e₁ b = e b := by
                rw [he₁, Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne hbn hbq]
              have h3 : e₁ c = e c := by
                rw [he₁, Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne hcn hcq]
              rw [h1, h2, h3]

/-- The student of rank one higher than `a` (well-defined when `a` is not the
tallest student).  Defined as a literal so that `(fsucc a h).val` is
definitionally `a.val + 1`. -/
def fsucc {n : ℕ} (a : Fin n) (h : a.val + 1 < n) : Fin n := ⟨a.val + 1, h⟩

/-- Every recorded switch has front rank + 2 ≤ behind rank. -/
lemma evPairs_le {n : ℕ} {e : Fin n ≃ ZMod n} {ps : List (ZMod n)} (hL : Legal e ps) :
    ∀ pr ∈ evPairs e ps, pr.1.val + 2 ≤ pr.2.val := by
  induction ps generalizing e with
  | nil => intro pr hmem; exact (List.not_mem_nil hmem).elim
  | cons p ps ih =>
    simp only [Legal] at hL
    obtain ⟨hfront, hrest⟩ := hL
    intro pr hmem
    simp only [evPairs, List.mem_cons] at hmem
    rcases hmem with h | h
    · rw [h]
      exact hfront
    · exact ih hrest pr h

/-- Every recorded switch has front rank < behind rank. -/
lemma evPairs_lt {n : ℕ} {e : Fin n ≃ ZMod n} {ps : List (ZMod n)} (hL : Legal e ps) :
    ∀ pr ∈ evPairs e ps, pr.1 < pr.2 := by
  intro pr hmem
  have h := evPairs_le hL pr hmem
  exact Fin.lt_def.mpr (by omega)

lemma length_evPairs {n : ℕ} (e : Fin n ≃ ZMod n) (ps : List (ZMod n)) :
    (evPairs e ps).length = ps.length := by
  induction ps generalizing e with
  | nil => rfl
  | cons p ps ih => simp only [evPairs, List.length_cons, ih]

/-- The length of a list of pairs with `fst < snd` equals the sum of the
counts over all such pairs. -/
lemma length_eq_sum_count {n : ℕ} (L : List (Fin n × Fin n))
    (hL : ∀ pr ∈ L, pr.1 < pr.2) :
    L.length = ∑ pr ∈ (Finset.univ.filter (fun pr : Fin n × Fin n => pr.1 < pr.2)),
      L.count pr := by
  induction L with
  | nil => simp
  | cons x xs ih =>
    have hx : x.1 < x.2 := hL x List.mem_cons_self
    have hxs : ∀ pr ∈ xs, pr.1 < pr.2 := fun pr h => hL pr (List.mem_cons_of_mem _ h)
    rw [List.length_cons, ih hxs]
    have hsplit : (∑ pr ∈ Finset.univ.filter (fun pr : Fin n × Fin n => pr.1 < pr.2),
        (x :: xs).count pr) =
        (∑ pr ∈ Finset.univ.filter (fun pr : Fin n × Fin n => pr.1 < pr.2), xs.count pr) +
        (∑ pr ∈ Finset.univ.filter (fun pr : Fin n × Fin n => pr.1 < pr.2),
          (if x == pr then 1 else 0)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro pr _
      exact List.count_cons
    have hsum1 : (∑ pr ∈ Finset.univ.filter (fun pr : Fin n × Fin n => pr.1 < pr.2),
        (if x == pr then 1 else 0)) = 1 := by
      have e1 : (∑ pr ∈ Finset.univ.filter (fun pr : Fin n × Fin n => pr.1 < pr.2),
          (if x == pr then 1 else 0)) =
          ∑ pr ∈ Finset.univ.filter (fun pr : Fin n × Fin n => pr.1 < pr.2),
            (if pr = x then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro pr _
        by_cases h : pr = x
        · subst h
          simp
        · rw [if_neg h]
          have h2 : (x == pr) = false := beq_eq_false_iff_ne.mpr (fun h3 => h h3.symm)
          simp [h2]
      rw [e1, Finset.sum_ite_eq']
      simp [hx]
    rw [hsplit, hsum1]

/-- The key alternation lemma.  Along any legal sequence of switches, the
switches of the pair `(a, b)` and those of the pair `(a+1, b)` alternate, and
every switch of `(a, b)` after the first one is preceded by a switch of
`(a+1, b)`.  Consequently the two displayed inequalities hold (the first
conjunct applies when the initial cyclic-order state is A, the second when it
is not). -/
lemma alternation {n : ℕ} (hn : 2 ≤ n) (a b : Fin n) (hab : a.val + 2 ≤ b.val)
    (ha : a.val + 1 < n) :
    ∀ (e : Fin n ≃ ZMod n) (ps : List (ZMod n)), Legal e ps →
      (StateA e a b (fsucc a ha) →
        (evPairs e ps).count (a, b) ≤ (evPairs e ps).count (fsucc a ha, b) + 1 ∧
        (evPairs e ps).count (fsucc a ha, b) ≤ (evPairs e ps).count (a, b)) ∧
      (¬ StateA e a b (fsucc a ha) →
        (evPairs e ps).count (a, b) ≤ (evPairs e ps).count (fsucc a ha, b) ∧
        (evPairs e ps).count (fsucc a ha, b) ≤ (evPairs e ps).count (a, b) + 1) := by
  have : NeZero n := ⟨by omega⟩
  have hbval : b.val < n := b.isLt
  have hac : a ≠ fsucc a ha := by
    intro hbad
    have : a.val = a.val + 1 := congrArg Fin.val hbad
    omega
  have hac' : fsucc a ha ≠ a := hac.symm
  have hbc : b ≠ fsucc a ha := by
    intro hbad
    have : b.val = a.val + 1 := congrArg Fin.val hbad
    omega
  have hbc' : fsucc a ha ≠ b := hbc.symm
  have hcb : (fsucc a ha).val < b.val := by simp [fsucc]; omega
  intro e ps
  induction ps generalizing e with
  | nil =>
    intro hL
    simp only [evPairs, List.count_nil]
    exact ⟨fun _ => ⟨Nat.zero_le _, Nat.le_refl 0⟩, fun _ => ⟨Nat.le_refl 0, Nat.zero_le _⟩⟩
  | cons p ps ih =>
    intro hL
    simp only [Legal] at hL
    obtain ⟨hfront, hrest⟩ := hL
    have hIH := ih _ hrest
    have hye : e (e.symm p) = p := Equiv.apply_symm_apply _ _
    have hxe : e (e.symm (p + 1)) = p + 1 := Equiv.apply_symm_apply _ _
    have evp : evPairs e (p :: ps) =
        (e.symm p, e.symm (p + 1)) :: evPairs (e.trans (Equiv.swap p (p + 1))) ps := by
      simp only [evPairs]
    by_cases hJ : (e.symm p, e.symm (p + 1)) = (a, b)
    · -- the head switch is the pair `(a, b)`
      have hMne : (e.symm p, e.symm (p + 1)) ≠ (fsucc a ha, b) := fun hbad =>
        hac ((congrArg Prod.fst hJ).symm.trans (congrArg Prod.fst hbad))
      have hya : e.symm p = a := congrArg Prod.fst hJ
      have hxb : e.symm (p + 1) = b := congrArg Prod.snd hJ
      have hea : e a = p := by rw [← hya]; exact hye
      have heb : e b = p + 1 := by rw [← hxb]; exact hxe
      have hAe : StateA e a b (fsucc a ha) := stateA_of_pair hn hea heb hac hbc
      have hA1 : ¬ StateA (e.trans (Equiv.swap p (p + 1))) a b (fsucc a ha) :=
        not_stateA_swap hn hea heb hac' hbc'
      have hcJ : (evPairs e (p :: ps)).count (a, b) =
          (evPairs (e.trans (Equiv.swap p (p + 1))) ps).count (a, b) + 1 := by
        rw [evp, hJ, List.count_cons_self]
      have hcM : (evPairs e (p :: ps)).count (fsucc a ha, b) =
          (evPairs (e.trans (Equiv.swap p (p + 1))) ps).count (fsucc a ha, b) := by
        rw [evp, List.count_cons_of_ne hMne]
      refine ⟨fun _ => ?_, fun hbad => absurd hAe hbad⟩
      rw [hcJ, hcM]
      obtain ⟨h1, h2⟩ := hIH.2 hA1
      omega
    · by_cases hM : (e.symm p, e.symm (p + 1)) = (fsucc a ha, b)
      · -- the head switch is the pair `(a+1, b)`
        have hyc : e.symm p = fsucc a ha := congrArg Prod.fst hM
        have hxb : e.symm (p + 1) = b := congrArg Prod.snd hM
        have hec : e (fsucc a ha) = p := by rw [← hyc]; exact hye
        have heb : e b = p + 1 := by rw [← hxb]; exact hxe
        have hab' : a ≠ b := fun hbad => by rw [hbad] at hab; omega
        have hnAe : ¬ StateA e a b (fsucc a ha) := not_stateA_of_pair hn hec heb hab'
        have hA1 : StateA (e.trans (Equiv.swap p (p + 1))) a b (fsucc a ha) :=
          stateA_swap hn hec heb hac hab'
        have hcJ : (evPairs e (p :: ps)).count (a, b) =
            (evPairs (e.trans (Equiv.swap p (p + 1))) ps).count (a, b) := by
          rw [evp, List.count_cons_of_ne hJ]
        have hcM : (evPairs e (p :: ps)).count (fsucc a ha, b) =
            (evPairs (e.trans (Equiv.swap p (p + 1))) ps).count (fsucc a ha, b) + 1 := by
          rw [evp, hM, List.count_cons_self]
        refine ⟨fun hbad => absurd hbad hnAe, fun _ => ?_⟩
        rw [hcJ, hcM]
        obtain ⟨h1, h2⟩ := hIH.1 hA1
        omega
      · -- the head switch involves no pair of the triple
        have hiff := stateA_swap_iff hn rfl hab hcb hfront hJ hM
        have hcJ : (evPairs e (p :: ps)).count (a, b) =
            (evPairs (e.trans (Equiv.swap p (p + 1))) ps).count (a, b) := by
          rw [evp, List.count_cons_of_ne hJ]
        have hcM : (evPairs e (p :: ps)).count (fsucc a ha, b) =
            (evPairs (e.trans (Equiv.swap p (p + 1))) ps).count (fsucc a ha, b) := by
          rw [evp, List.count_cons_of_ne hM]
        rw [hcJ, hcM]
        constructor
        · intro hA
          exact hIH.1 (hiff.mpr hA)
        · intro hnA
          exact hIH.2 (fun h => hnA (hiff.mp h))

/-- The number of times a fixed pair of students `(a, b)` can switch is at
most `b.val - a.val - 1`.  Proof by induction on the difference of the ranks,
using the alternation lemma. -/
lemma count_bound {n : ℕ} (hn : 2 ≤ n) (d : ℕ) :
    ∀ (a b : Fin n) (e : Fin n ≃ ZMod n) (ps : List (ZMod n)), Legal e ps →
      b.val - a.val = d → (evPairs e ps).count (a, b) ≤ d - 1 := by
  induction d with
  | zero =>
    intro a b e ps hL hd
    have h0 : (evPairs e ps).count (a, b) = 0 := by
      rw [List.count_eq_zero]
      intro hmem
      have h2 : a.val + 2 ≤ b.val := evPairs_le hL _ hmem
      omega
    rw [h0]
  | succ k ih =>
    intro a b e ps hL hd
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      have h0 : (evPairs e ps).count (a, b) = 0 := by
        rw [List.count_eq_zero]
        intro hmem
        have h2 : a.val + 2 ≤ b.val := evPairs_le hL _ hmem
        omega
      rw [h0]
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
      have hab : a.val + 2 ≤ b.val := by omega
      have ha : a.val + 1 < n := by have := b.isLt; omega
      have halt := alternation hn a b hab ha e ps hL
      have h1 : (evPairs e ps).count (a, b) ≤ (evPairs e ps).count (fsucc a ha, b) + 1 := by
        by_cases hA : StateA e a b (fsucc a ha)
        · exact (halt.1 hA).1
        · exact (halt.2 hA).1.trans (Nat.le_add_right _ _)
      have hfs : (fsucc a ha).val = a.val + 1 := rfl
      have h2 := ih (fsucc a ha) b e ps hL (by rw [hfs]; omega)
      omega

lemma sum_range_choose_two (n : ℕ) : ∑ k ∈ Finset.range n, k.choose 2 = n.choose 3 := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, Nat.choose_succ_succ', add_comm]

lemma inner_sum (k : ℕ) : ∑ i ∈ Finset.range k, (k - i - 1) = k.choose 2 := by
  have e1 : ∑ i ∈ Finset.range k, (k - i - 1) = ∑ i ∈ Finset.range k, (k - 1 - i) := by
    apply Finset.sum_congr rfl
    intro i _
    omega
  have e2 := Finset.sum_range_reflect (fun j : ℕ => j) k
  rw [e1, e2, Finset.sum_range_id, Nat.choose_two_right]

lemma sum_Iio_val {n : ℕ} (b : Fin n) : ∑ a ∈ Finset.Iio b, (b.val - a.val - 1) = b.val.choose 2 := by
  rw [← inner_sum]
  have h1 : (Finset.Iio b).map Fin.valEmbedding = Finset.range b.val := by
    rw [Fin.map_valEmbedding_Iio]
    exact Nat.Iio_eq_range _
  rw [← h1, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro a _
  rfl

lemma pair_sum_choose3 {n : ℕ} :
    ∑ pr ∈ (Finset.univ.filter (fun pr : Fin n × Fin n => pr.1 < pr.2)),
      (pr.2.val - pr.1.val - 1) = n.choose 3 := by
  have step1 : ∑ pr ∈ (Finset.univ.filter (fun pr : Fin n × Fin n => pr.1 < pr.2)),
      (pr.2.val - pr.1.val - 1) = ∑ b : Fin n, ∑ a ∈ Finset.Iio b, (b.val - a.val - 1) := by
    rw [Finset.sum_filter, ← Finset.univ_product_univ, Finset.sum_product, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    have hIio : Finset.Iio b = Finset.univ.filter (· < b) := by
      ext a
      simp
    rw [hIio, Finset.sum_filter]
  have step2 : (∑ b : Fin n, ∑ a ∈ Finset.Iio b, (b.val - a.val - 1)) =
      ∑ b : Fin n, b.val.choose 2 :=
    Finset.sum_congr rfl (fun b _ => sum_Iio_val b)
  have step3 : (∑ b : Fin n, b.val.choose 2) = n.choose 3 := by
    have h := Fin.sum_univ_eq_sum_range (fun k => k.choose 2) n
    rw [show (∑ b : Fin n, b.val.choose 2) = ∑ i : Fin n, (fun k => k.choose 2) i.val from rfl,
      h, sum_range_choose_two]
  rw [step1, step2, step3]

snip end

/-- **USAMO 2010 Problem 2.**
There are `n` students standing in a circle, one behind the other, with
heights `h₁ < h₂ < ⋯ < hₙ`.  If a student with height `hₖ` is standing
directly behind a student with height `hₖ₋₂` or less, the two students are
permitted to switch places.  Then it is not possible to make more than
`C(n, 3)` such switches.

We model the circle by positions in `ZMod n` (position `p + 1` is directly
behind position `p`), the students by their height ranks in `Fin n`, and a
sequence of switches by the list of positions at which they occur; `Legal`
asserts that every switch is permitted. -/
problem usa2010_p2 {n : ℕ} (e : Fin n ≃ ZMod n) (ps : List (ZMod n)) (h : Legal e ps) :
    ps.length ≤ n.choose 3 := by
  rcases lt_or_ge n 3 with hn | hn
  · -- with fewer than 3 students no switch is ever permitted
    cases ps with
    | nil => exact Nat.zero_le _
    | cons p ps =>
      exfalso
      simp only [Legal] at h
      obtain ⟨h1, -⟩ := h
      have h2 : (e.symm (p + 1)).val < n := (e.symm (p + 1)).isLt
      omega
  · have h2 : 2 ≤ n := by omega
    rw [← length_evPairs e ps, length_eq_sum_count _ (evPairs_lt h)]
    calc ∑ pr ∈ Finset.univ.filter (fun pr : Fin n × Fin n => pr.1 < pr.2),
          (evPairs e ps).count pr
        ≤ ∑ pr ∈ Finset.univ.filter (fun pr : Fin n × Fin n => pr.1 < pr.2),
          (pr.2.val - pr.1.val - 1) := by
          apply Finset.sum_le_sum
          intro pr hpr
          rw [Finset.mem_filter] at hpr
          obtain ⟨_, hplt⟩ := hpr
          have hbound := count_bound h2 (pr.2.val - pr.1.val) pr.1 pr.2 e ps h rfl
          rwa [Prod.mk.eta] at hbound
      _ = n.choose 3 := pair_sum_choose3

end Usa2010P2
