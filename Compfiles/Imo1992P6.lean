/-
Copyright (c) 2026 Constantin Seebach. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Constantin Seebach
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file

/-!
# International Mathematical Olympiad 1992, Problem 6

For each positive integer $n$, $S(n)$ is defined to be the greatest integer such that, for every positive integer $k \le S(n)$, $n^{2}$ can be written as the sum of $k$ positive squares.

(a) Prove that $S(n) \le n^{2}-14$ for each $n \ge 4$.

(b) Find an integer $n$ such that $S(n)=n^{2}-14$.

(c) Prove that there are infinitely many integers $n$ such that $S(n)=n^{2}-14$.
-/

namespace Imo1992P6

/--
$z$ can be written as the sum of $k$ positive squares.
-/
def is_sum_of_pos_squares (z k : ℕ) : Prop := ∃ s : (Fin k → ℕ), z = ∑ i, (s i)^2 ∧ ∀ i, 0 < s i


/--
Auxiliary definition: S(n) will be defined as the greatest integer of the set S_set(n).
-/
def S_set (n : ℕ+) := { z : ℕ+ | ∀ k, k ≤ z → is_sum_of_pos_squares (n^2) k }

/-!
The definition of $S(n)$ in the problem statement hides a lot of complexity. The following lemmas are needed to write down $S(n)$ in a well-defined way.
-/

lemma S_set_Nonempty (n : ℕ+) : Set.Nonempty (S_set n) := by
  apply Set.nonempty_of_mem (x:=1)
  simp_rw [S_set, is_sum_of_pos_squares]
  intro k kle1
  use λi => n
  simp_all

lemma S_set_bounded (n) : ∀ k ∈ S_set n, k ≤ n^2 := by
  simp_rw [S_set, is_sum_of_pos_squares, Set.mem_setOf_eq]
  intro k kh
  let kh := kh k
  simp only [le_refl, forall_const] at kh
  let ⟨s,sh1, sh2⟩ := kh
  rw [<-PNat.coe_le_coe]
  norm_cast at sh1
  rw [sh1]
  calc
    _ = ∑ i : Fin k, 1 := by simp
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      exact Nat.one_le_pow 2 (s i) (sh2 i)

lemma S_set_Finite (n) : Set.Finite (S_set n) := by
  apply Set.Finite.of_finite_image (f:=Subtype.val)
  · refine Set.finite_iff_bddAbove.mpr ?_
    refine bddAbove_def.mpr ?_
    use n^2
    simp only [Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right,
      forall_exists_index]
    intro y ypos h
    norm_cast
    let := (S_set_bounded n ⟨y, ypos⟩) h
    simp_all only [PNat.pow_coe, ge_iff_le]
    exact this
  · simp

noncomputable def S (n : ℕ+) := (Set.Finite.exists_maximal (S_set_Finite n) (S_set_Nonempty n)).choose

snip begin

/-!
We roughly follow the proof from https://prase.cz/kalva/imo/isoln/isoln926.html. Note that it is quite lacking in details.

But first some general theorems that I wish were in Mathlib.
-/

namespace Multiset

theorem map_sub_of_injective {α β : Type} [DecidableEq α] [DecidableEq β] (f : α → β) (inj : Function.Injective f) (s t) : Multiset.map f (s - t) = Multiset.map f s - Multiset.map f t := by
  revert s
  revert t
  apply Multiset.induction
  · simp
  · intro a t ih s
    simp only [Multiset.sub_cons, Multiset.map_cons]
    rw [ih]
    congr
    rw [Multiset.map_erase _ inj]

theorem sum_sub {α : Type} [DecidableEq α] [AddCommMonoid α] (s t : Multiset α) (h : t ≤ s) : (s - t).sum + t.sum = s.sum := by
  revert s
  revert t
  apply Multiset.induction
  · simp
  · intro a t ih s h
    simp only [Multiset.sub_cons, Multiset.sum_cons]
    nth_rw 2 [add_comm]
    rw [<-add_assoc, ih]
    · rw [add_comm, Multiset.sum_erase]
      apply Multiset.mem_of_le h (by simp)
    · rw [Multiset.le_iff_exists_add] at h
      obtain ⟨u, uh⟩ := h
      rw [uh]
      simp

end Multiset


namespace Nat

theorem sub_mod {a b c : Nat} (h : b ≤ a) : (a - b) % c = (a - b % c) % c := by
  nth_rw 3 [Nat.mod_eq_sub_div_mul]
  rw [Nat.sub_sub_right, Nat.sub_add_comm]
  · exact (Nat.add_mul_mod_self_right (a - b) (b / c) c).symm
  · exact h
  · exact Nat.div_mul_le_self b c

theorem sub_mod_eq_add_mod {a b c : Nat} (h : b ≤ a) (cnz : c ≠ 0) : (a - b) % c = (a + (c - b % c)) % c := by
  rw [<-Nat.add_sub_assoc, Nat.sub_add_comm, Nat.add_mod_right]
  · exact sub_mod h
  · trans b
    · exact Nat.mod_le b c
    · exact h
  apply le_of_lt
  apply Nat.mod_lt
  exact Nat.zero_lt_of_ne_zero cnz

end Nat


lemma S_spec (n : ℕ+) : Maximal (fun z : ℕ+ => ∀ k, k ≤ z → is_sum_of_pos_squares (n^2) k) (S n) := by
  exact Exists.choose_spec _


theorem imo1992_p6_a : ∀ n ≥ 4, S n ≤ n^2-14 := by
  by_contra! c
  obtain ⟨n, nge, h⟩ := c
  have nge : 14 < n ^ 2 := by
    simp at nge
    suffices 4^2 ≤ n^2 by
      rw [<-PNat.coe_le_coe] at this
      rw [<-PNat.coe_lt_coe]
      apply Nat.lt_of_add_one_le
      simp_all
      exact Nat.le_of_add_left_le this
    exact pow_le_pow_left' nge 2
  have nge' : 13 < n^2 := by
    trans 14
    · simp
    · exact nge
  have c : is_sum_of_pos_squares (n^2) (n^2-13) := by
    have : (n.val ^ 2 - 13) = (n ^ 2 - 13).val := by
      rw [PNat.sub_coe]
      simp [nge']
    rw [this]
    apply (S_spec n).prop (n^2-13)
    rw [<-PNat.coe_lt_coe, PNat.sub_coe] at h
    rw [<-PNat.coe_le_coe, PNat.sub_coe]
    simp [nge, nge'] at h ⊢
    rw [Nat.sub_lt_iff_lt_add] at h
    · exact Nat.le_of_lt_succ h
    · exact nge'
  unfold is_sum_of_pos_squares at c
  obtain ⟨s, sh1, sh2⟩ := c
  have slt4 : ∀ i, s i < 4 := by
    by_contra! c
    obtain ⟨j, h⟩ := c
    have : n^2 > n^2 := by
      calc
        _ = ∑ i, s i ^ 2 := sh1
        _ = ∑ i ∈ Finset.univ \ {j}, s i ^ 2 + s j ^ 2 := by
          rw [<-Finset.sum_eq_sum_diff_singleton_add]
          apply Finset.mem_univ
        _ ≥ ∑ i ∈ Finset.univ \ {j}, 1 + s j ^ 2 := by
          rw [ge_iff_le, add_le_add_iff_right]
          apply Finset.sum_le_sum
          intro i _
          have : 1 = 1^2 := by rfl
          rw [this]
          apply pow_left_mono 2
          apply sh2
        _ = n^2 - 14 + s j ^ 2 := by
          rw [Finset.sum_const, smul_eq_mul, mul_one, Nat.add_right_cancel_iff, Finset.card_sdiff,
              Finset.card_univ, Fintype.card_fin, Finset.inter_univ, Finset.card_singleton]
          omega
        _ ≥ n ^ 2 - 14 + 16 := by
          simp
          have : 16 = 4^2 := by simp
          rw [this]
          apply pow_left_mono 2
          exact h
        _ > _ := by
          rw [<-Nat.sub_add_comm]
          · simp
            rw [<-PNat.pow_coe, PNat.val]
            simp
          · exact nge'
    simp at this
  let V : Type := Finset.Ioo 0 4
  let s' (i) : V := ⟨s i, by {
    simp
    and_intros
    · exact sh2 i
    · exact slt4 i
  }⟩
  have sh1' : n ^ 2 = ∑ i, (s' i).val ^ 2 := by
    unfold s'
    exact sh1

  have h1 : n ^ 2 - 13 = ∑ j, ∑ i with s' i = j, (1:ℕ) := by
    rw [Finset.sum_fiberwise]
    simp

  obtain ⟨a, b, abh⟩ : ∃ a b, 13 = 3*a + 8*b := by
    let a := Finset.card {i | s i = 2}
    let b := Finset.card {i | s i = 3}
    use a, b
    suffices n^2 = (n^2 - 13) + 3*a + 8*b by
      zify at this
      rw [Nat.cast_sub (Nat.le_of_add_left_le nge)] at this
      simp only [Nat.cast_pow, Nat.cast_ofNat] at this
      omega
    calc
      _ = ∑ i, (s' i).val ^ 2 := by
        nth_rw 1 [sh1']
      _ = ∑ j, ∑ i with s' i = j, (s' i).val ^ 2 := by
        rw [Finset.sum_fiberwise]
      _ = ∑ j, Finset.card {i | s' i = j} * j.val ^ 2 := by
        congr
        ext j
        rw [Finset.sum_const_nat]
        grind only [= Finset.mem_filter]
      _ = ∑ j ∈ {1,2,3}, Finset.card {i | (s i) = j} * j ^ 2 := by
        apply Finset.sum_bij' (i:=fun (x _) => x.val) (j:= fun (x h) => ⟨x, by grind⟩)
        all_goals simp
        intro i
        apply Or.inl
        unfold s'
        congr
        funext j
        simp
        obtain ⟨val, property⟩ := i
        simp_all
        simp_all only [Subtype.mk.injEq, s', V]
      _ = ∑ j ∈ {1,2,3}, Finset.card {i | s i = j} + ∑ j ∈ {1,2,3}, Finset.card {i | s i = j} * (j ^ 2 - 1) := by
        rw [<-Finset.sum_add_distrib]
        nth_rw 1 [<-Finset.sum_attach]
        nth_rw 2 [<-Finset.sum_attach]
        congr
        funext j
        rw [Nat.mul_sub, Nat.mul_one, Nat.add_sub_cancel']
        apply Nat.le_mul_of_pos_right
        decide +revert
      _ = (n^2-13) + ∑ j ∈ {1,2,3}, Finset.card {i | s i = j} * (j ^ 2 - 1) := by
        congr
        simp_rw [h1]
        apply Finset.sum_bij (fun i hi => ⟨i, by decide +revert⟩)
        · simp
        · intro x1 _ x2 _ e
          grind
        · intro y _
          use y.val
          simp
        · intro i ih
          unfold s'
          simp
          congr
          grind
      _ = (n^2-13) + Finset.card {i | s i = 2} * (2 ^ 2 - 1) + Finset.card {i | s i = 3} * (3 ^ 2 - 1) := by
        simp only [Finset.mem_insert, OfNat.one_ne_ofNat, Finset.mem_singleton, or_self,
          not_false_eq_true, Finset.sum_insert, one_pow, tsub_self, mul_zero, Nat.reduceEqDiff,
          Nat.reducePow, Nat.add_one_sub_one, Finset.sum_singleton, zero_add]
        rw [Nat.add_assoc]
      _ = _ := by
        unfold a b
        ring
  grind => lia


def complete (n : ℕ+) : Prop := S n = n^2 - 14

theorem complete_iff_sos (n : ℕ+) (nge : 4 ≤ n) : complete n ↔ ∀ k, k ≤ n^2 - 14 → is_sum_of_pos_squares (n^2) k := by
  constructor
  · intro Sdef
    let := (S_spec n).prop
    rw [Sdef] at this
    apply this
  · intro h
    suffices S n ≥ n^2 - 14 by apply eq_of_le_of_ge (imo1992_p6_a _ nge) this
    contrapose! h
    let := (S_spec n).not_prop_of_gt h
    rw [not_forall] at this
    grind


def msos.sq_sum (C : Multiset ℕ+) : ℕ := (C.map (fun x => x.val^2)).sum

def msos.mk (L : List (ℕ × ℕ+)) : Multiset ℕ+ := (L.map (fun ⟨c,x⟩ => Multiset.replicate c x)).foldr (· + ·) ∅

theorem msos.is_sum_of_pos_squares (C : Multiset ℕ+) : is_sum_of_pos_squares (msos.sq_sum C) C.card := by
  revert C
  apply Multiset.induction
  · unfold sq_sum
    use fun _ => 0
    simp
  · intro head C ih
    let ⟨s, ⟨sh1, sh2⟩⟩ := ih
    let s' (i : Fin (head ::ₘ C).card) : ℕ :=
      if b : i < C.card then
        s (i.castLT b)
      else
        head
    use s'
    unfold sq_sum at sh1 ⊢
    and_intros
    · unfold s'
      simp_rw [dite_pow]
      rw [Multiset.map_cons, Multiset.sum_cons]
      · rw [Finset.sum_dite, sh1, add_comm]
        congr 1
        · apply Finset.sum_bij (fun a b => ⟨a.castLE (by simp), by grind⟩)
          · simp
          · simp
          · simp
            intro i ib
            use ⟨i, by simp [ib]⟩
            simp
          · intro i _
            simp only [zero_le, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_left_inj₀]
            exact rfl
        · simp only [Finset.univ_eq_attach, Finset.sum_const, Finset.card_attach, not_lt,
            smul_eq_mul, ne_eq, Nat.pow_eq_zero, PNat.ne_zero, OfNat.ofNat_ne_zero, not_false_eq_true,
            and_true, right_eq_mul₀]
          rw [Finset.card_eq_one]
          have : NeZero (head ::ₘ C).card := by rw [Multiset.card_cons]; exact instNeZeroNatHAdd_1
          use ⊤
          apply Finset.eq_singleton_iff_unique_mem.mpr
          and_intros
          · simp
          · intro x xh
            rw [eq_top_iff]
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at xh
            refine Fin.le_def.mpr ?_
            trans C.card <;> simp [xh]
    · intro i
      unfold s'
      split_ifs with ib
      · apply sh2
      · simp


def msos.shift (C: Multiset ℕ+) (i : ℕ+) (a : ℕ) :=
  C - Multiset.replicate (4*a) i + Multiset.replicate a (2*i)


theorem msos.card_shift (C:Multiset ℕ+) (i : ℕ+) (a : ℕ) (h4 : 4*a ≤ C.count i) : (msos.shift C i a).card + 3*a = C.card := by
  unfold msos.shift
  simp only [Multiset.card_add, Multiset.card_replicate]
  rw [Multiset.card_sub, Multiset.card_replicate]
  · zify
    rw [Nat.cast_sub]
    · grind
    · trans Multiset.count i C
      · exact h4
      · exact Multiset.count_le_card i C
  · exact Multiset.le_count_iff_replicate_le.mp h4


theorem msos.sq_sum_shift (C:Multiset ℕ+) (i : ℕ+) (a : ℕ) (h4 : 4*a ≤ C.count i) : msos.sq_sum (msos.shift C i a) = msos.sq_sum C := by
  unfold sq_sum msos.shift
  rw [Multiset.map_add, Multiset.map_replicate, Multiset.map_sub_of_injective, Multiset.sum_add]
  · rw [Multiset.map_replicate, Multiset.sum_replicate]
    rw [<-Multiset.sum_sub (Multiset.map (fun x ↦ x.val ^ 2) C) (Multiset.replicate (4 * a) (i.val ^ 2))]
    · simp only [PNat.mul_coe, PNat.val_ofNat, smul_eq_mul, Multiset.sum_replicate,
        Nat.add_left_cancel_iff]
      grind
    · rw [Multiset.le_iff_count]
      intro x
      rw [Multiset.count_replicate]
      split_ifs with h
      · rw [<-h, Multiset.count_map_eq_count' (fun (y:ℕ+) ↦ y.val ^ 2)]
        · exact h4
        · intro x1 x2 e
          simp_all
      · simp
  · intro x1 x2 e
    simp_all


def msos.repeat_shift (C:Multiset ℕ+) : Multiset ℕ+ :=
  let C' := C.filter (4 ≤ C.count ·)
  if he : C' = ∅ then
    C
  else
    let i := C'.toFinset.min' (Multiset.toFinset_nonempty.mpr he)
    let a := (C.count i)/4
    msos.repeat_shift (msos.shift C i a)
  termination_by C.card
  decreasing_by
    expose_names
    rw [<-Nat.add_lt_add_iff_right (k:=3*a), msos.card_shift]
    · unfold a
      simp only [lt_add_iff_pos_right, Nat.ofNat_pos, mul_pos_iff_of_pos_left, Nat.div_pos_iff, true_and]
      suffices i ∈ C'.toFinset by simp_all only [Multiset.toFinset_filter, Finset.mem_filter, Multiset.mem_toFinset, C', i]
      unfold i
      exact Finset.min'_mem C'.toFinset (Multiset.toFinset_nonempty.mpr he)
    · rw [Nat.mul_comm]
      apply Nat.div_mul_le_self


theorem msos.repeat_shift.forall (C:Multiset ℕ+) :
    ∀ b ≤ (C.card - (msos.repeat_shift C).card)/3, ∃ C', msos.sq_sum C' = msos.sq_sum C ∧ C'.card + 3*b = C.card := by
  fun_induction msos.repeat_shift
  · expose_names
    intro b bh
    simp only [tsub_self, Nat.zero_div, nonpos_iff_eq_zero] at bh
    use x
    simp [bh]
  · expose_names
    intro b bh
    by_cases bb : 4 * b ≤ Multiset.count i x
    · use shift x i b
      and_intros
      · apply sq_sum_shift _ _ _ bb
      · apply card_shift _ _ _ bb
    · have : a < b := by
        unfold a
        grind
      have : b - a ≤ ((shift x i a).card - (repeat_shift (shift x i a)).card) / 3 := by
        simp
        nth_rw 1 [<-msos.card_shift _ i a] at bh <;> grind
      obtain ⟨y, yh1, yh2⟩ := ih1 (b-a) this
      rw [<-add_left_inj (3*a), msos.card_shift] at yh2
      · use y
        rw [yh1, sq_sum_shift] <;> and_intros <;> grind
      · grind


theorem msos.card_repeat_shift_le_card (C:Multiset ℕ+) : (msos.repeat_shift C).card ≤ C.card := by
  fun_induction msos.repeat_shift
  · trivial
  · expose_names
    apply le_trans _ (le_of_eq (card_shift x i a _))
    · exact Nat.le_add_right_of_le ih1
    · apply Nat.mul_div_le


theorem msos.card_repeat_shift_le (C:Multiset ℕ+) : (msos.repeat_shift C).card ≤ C.card - (C.count 1)/4*3 := by
  fun_cases msos.repeat_shift
  · expose_names
    unfold C' at h
    simp only [Multiset.empty_eq_zero, Multiset.filter_eq_nil, not_le] at h
    have : Multiset.count 1 C / 4 = 0 := by
      rw [Nat.div_eq_zero_iff]
      apply Or.inr
      by_cases e : 1 ∈ C
      · apply h _ e
      · rw [Multiset.count_eq_zero.mpr]
        · simp
        · exact e
    simp [this]
  · expose_names
    trans (shift C i a).card
    · apply card_repeat_shift_le_card
    · apply Nat.le_sub_of_add_le
      have : Multiset.count 1 C / 4 ≤ Multiset.count i C / 4 := by
        by_cases c : 4 ≤ Multiset.count 1 C
        · have : i = 1 := by
            unfold i
            rw [Finset.min'_eq_iff]
            and_intros
            · unfold C'
              simp only [Multiset.toFinset_filter, Finset.mem_filter, Multiset.mem_toFinset, c,
                and_true]
              rw [<-Multiset.one_le_count_iff_mem]
              exact Nat.one_le_of_lt c
            · simp
          rw [this]
        · rw [not_le] at c
          rw [Nat.div_eq_of_lt c]
          apply zero_le
      trans (shift C i a).card + Multiset.count i C / 4 * 3
      · rw [add_le_add_iff_left, mul_le_mul_iff_left₀ (by simp)]
        exact this
      · rw [mul_comm]
        unfold a
        rw [card_shift]
        exact Nat.mul_div_le _ _


theorem is_sum_of_pos_squares_by_repeat_shift (C:Multiset ℕ+) :
    ∀ k ∈ Finset.Icc (msos.repeat_shift C).card C.card, k%3 = C.card%3 → is_sum_of_pos_squares (msos.sq_sum C) k := by
  intro k kbs kmod
  let b := (C.card - k)/3
  obtain ⟨C', h1, h2⟩ := msos.repeat_shift.forall C b (by {
    unfold b
    apply Nat.div_le_div_right
    let := (Finset.mem_Icc.mp kbs).left
    omega
  })
  have : k = C'.card := by
    unfold b at h2
    rw [mul_comm, Nat.div_mul_cancel] at h2
    · zify at h2
      rw [Nat.cast_sub] at h2
      · grind
      · exact (Finset.mem_Icc.mp kbs).right
    · omega
  rw [this, <-h1]
  apply msos.is_sum_of_pos_squares


@[simp]
theorem msos.card_mk (L : List (ℕ × ℕ+)) : (msos.mk L).card = (L.map (·.1)).sum := by
  induction L with
  | nil =>
    unfold mk
    simp
  | cons a L ih =>
    unfold mk at ih ⊢
    simp only at ih ⊢
    rw [List.map_cons, List.foldr_cons, Multiset.card_add]
    rw [ih]
    simp


@[simp]
theorem msos.sq_sum_mk (L : List (ℕ × ℕ+)) : msos.sq_sum (msos.mk L) = (L.map (fun ⟨c,i⟩ => c * i.val^2)).sum := by
  induction L with
  | nil =>
    unfold mk sq_sum
    simp
  | cons a L ih =>
    unfold mk sq_sum at ih ⊢
    simp only [List.map_cons, List.foldr_cons, Multiset.map_add,
      Multiset.map_replicate, Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul, List.sum_cons,
      Nat.add_left_cancel_iff]
    rw [ih]


@[simp]
theorem msos.count_mk (L : List (ℕ × ℕ+)) (a : ℕ+) : Multiset.count a (msos.mk L) = ((L.filter (·.2 == a)).map (·.1)).sum := by
  induction L with
  | nil =>
    unfold mk
    simp
  | cons b L ih =>
    rw [List.filter_cons]
    by_cases c : b.2 = a
    · simp only [c, BEq.rfl, ↓reduceIte, List.map_cons, List.sum_cons]
      rw [<-ih]
      unfold mk
      rw [<-c]
      simp
    · simp only [beq_iff_eq, c, reduceIte]
      rw [<-ih]
      unfold mk
      simp only [Multiset.empty_eq_zero, List.map_cons, List.foldr_cons, Multiset.count_add,
        Nat.add_eq_right, Multiset.count_eq_zero]
      rw [Multiset.mem_replicate]
      contrapose! c
      exact Eq.symm c.2


theorem sos_13_0mod3 : ∀ k:ℕ, k≠0 → k ≤ 13^2-14 → k%3=0 → is_sum_of_pos_squares (13^2) k := by
  intro k knz kle kmod
  by_cases lb : 9 ≤ k
  · let C := msos.mk [(151,1), (2, 3)]
    have s : msos.sq_sum C = 13^2 := by native_decide
    rw [<-s]
    apply is_sum_of_pos_squares_by_repeat_shift
    · rw [Finset.mem_Icc]
      and_intros
      · have : (msos.repeat_shift C).card = 9 := by native_decide
        rw [this]
        assumption
      · unfold C
        simp
        omega
    · unfold C
      rw [kmod]
      simp
  · have : k=3 ∨ k=6 := by omega
    apply this.by_cases
    · intro keq
      let C := msos.mk [(1,3), (1, 4), (1,12)]
      have : msos.sq_sum C = 13^2 := by native_decide
      rw [<-this]
      have : C.card = k := by unfold C; rw [keq]; simp
      rw [<-this]
      apply msos.is_sum_of_pos_squares
    · intro keq
      let C := msos.mk [(4,2), (1, 3), (1,12)]
      have : msos.sq_sum C = 13^2 := by native_decide
      rw [<-this]
      have : C.card = k := by unfold C; rw [keq]; simp
      rw [<-this]
      apply msos.is_sum_of_pos_squares

theorem sos_13_1mod3 : ∀ k:ℕ, k ≤ 13^2-14 → k%3=1 → is_sum_of_pos_squares (13^2) k := by
  intro k kle kmod
  by_cases lb : 7 ≤ k
  · let C := msos.mk [(149,1), (5, 2)]
    have s : msos.sq_sum C = 13^2 := by native_decide
    rw [<-s]
    apply is_sum_of_pos_squares_by_repeat_shift
    · rw [Finset.mem_Icc]
      and_intros
      · have : (msos.repeat_shift C).card = 7 := by native_decide
        rw [this]
        assumption
      · unfold C
        simp
        omega
    · unfold C
      rw [kmod]
      simp
  · have : k=1 ∨ k=4 := by omega
    apply this.by_cases
    · intro keq
      let C := msos.mk [(1,13)]
      have : msos.sq_sum C = 13^2 := by native_decide
      rw [<-this]
      have : C.card = k := by unfold C; rw [keq]; simp
      rw [<-this]
      apply msos.is_sum_of_pos_squares
    · intro keq
      let C := msos.mk [(1,1), (1, 2), (1,8), (1,10)]
      have : msos.sq_sum C = 13^2 := by native_decide
      rw [<-this]
      have : C.card = k := by unfold C; rw [keq]; simp
      rw [<-this]
      apply msos.is_sum_of_pos_squares

theorem sos_13_2mod3 : ∀ k:ℕ, k ≤ 13^2-14 → k%3=2 → is_sum_of_pos_squares (13^2) k := by
  intro k kle kmod
  by_cases lb : 5 ≤ k
  · let C := msos.mk [(152, 1), (2, 2), (1,3)]
    have s : msos.sq_sum C = 13^2 := by native_decide
    rw [<-s]
    apply is_sum_of_pos_squares_by_repeat_shift
    · rw [Finset.mem_Icc]
      and_intros
      · have : (msos.repeat_shift C).card = 5 := by native_decide
        rw [this]
        assumption
      · unfold C
        simp
        omega
    · unfold C
      rw [kmod]
      simp
  · have keq : k=2 := by omega
    let C := msos.mk [(1,5), (1,12)]
    have : msos.sq_sum C = 13^2 := by native_decide
    rw [<-this]
    have : C.card = k := by unfold C; rw [keq]; simp
    rw [<-this]
    apply msos.is_sum_of_pos_squares

theorem complete_13 : complete 13 := by
  rw [complete_iff_sos _ (by simp)]
  intro k kb
  have : k.val%3 = 0 ∨ k.val%3 = 1 ∨ k.val%3 = 2 := by omega
  apply this.elim3
  · apply sos_13_0mod3 _ (by grind) kb
  · apply sos_13_1mod3 _ kb
  · apply sos_13_2mod3 _ kb


theorem sos_mul_const (z k m : ℕ) (mpos : 0 < m) (h : is_sum_of_pos_squares z k) : is_sum_of_pos_squares (z*m^2) k := by
  let ⟨s, sh1, sb⟩ := h
  use fun i => m * s i
  and_intros
  · simp_rw [mul_pow]
    rw [<-Finset.mul_sum, <-sh1, mul_comm]
  · intro i
    simp [sb i, mpos]

theorem sos_add (z1 z2 k1 k2: ℕ) (h1 : is_sum_of_pos_squares z1 k1) (h2 : is_sum_of_pos_squares z2 k2) : is_sum_of_pos_squares (z1+z2) (k1+k2) := by
  let ⟨s1, s1h, s1b⟩ := h1
  let ⟨s2, s2h, s2b⟩ := h2
  use fun i => if a : i < k1 then s1 ⟨i.val, a⟩ else s2 ⟨i.val-k1, by grind⟩
  and_intros
  · simp only [dite_pow, Finset.sum_dite]
    congr
    · rw [s1h]
      apply Finset.sum_nbij' (fun i => ⟨⟨i.val, by grind⟩, by simp⟩) (fun j => ⟨j.val.val, by grind⟩) <;> simp
    · simp_rw [s2h]
      apply Finset.sum_nbij' (fun i => ⟨⟨i.val+k1, by grind⟩, by simp⟩) (fun j => ⟨j.val.val-k1, by grind⟩) <;> simp
      intro i b
      apply Fin.eq_of_val_eq
      simp only
      exact Nat.sub_add_cancel b
  · intro i
    simp only
    split_ifs
    · exact s1b _
    · exact s2b _

theorem sos_mul (z1 z2 k1 k2: ℕ) (h1 : is_sum_of_pos_squares z1 k1) (h2 : is_sum_of_pos_squares z2 k2) : is_sum_of_pos_squares (z1*z2) (k1*k2) := by
  let ⟨s1, s1h, s1b⟩ := h1
  let ⟨s2, s2h, s2b⟩ := h2
  have equi : Fin (k1*k2) ≃ Fin k1 × Fin k2 := finProdFinEquiv.symm
  let f (i j) := (s1 i) * (s2 j)
  use fun x => Function.uncurry f (equi x)
  and_intros
  · rw [s1h, s2h]
    rw [Finset.sum_mul_sum]
    have : ∀ i, ∀ j, s1 i ^ 2 * s2 j ^ 2 = f i j ^ 2 := by
      unfold f
      simp_rw [mul_pow, implies_true]
    simp_rw [this]
    rw [<-Finset.sum_fiberwise (ι:=Fin (k1*k2)) _ (fun x => (equi x).1)]
    congr
    funext i
    rw [Eq.comm]
    apply Finset.sum_bij (fun x h => (equi x).2)
    · simp
    · intro x1 x1h x2 x2h e
      apply equi.injective
      rw [Prod.eq_iff_fst_eq_snd_eq]
      apply And.intro _ e
      grind
    · intro j _
      use equi.symm ⟨i, j⟩
      simp
    · intro x xh
      simp only [zero_le, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_left_inj₀]
      grind
  · unfold f
    intro i
    apply Nat.mul_pos
    · apply s1b
    · apply s2b

theorem sos_split (z k: ℕ) (kb : 1 ≤ k) (h : is_sum_of_pos_squares z k) : ∃ d, 0 < d ∧ d^2 ≤ z ∧ is_sum_of_pos_squares (z-d^2) (k-1) ∧ is_sum_of_pos_squares (d^2) 1 := by
  let ⟨s, sh, sb⟩ := h
  use s ⟨k-1, by grind⟩
  and_intros
  · apply sb
  · rw [sh]
    apply Finset.single_le_sum_of_canonicallyOrdered (f:=fun i => (s i)^2)
    simp
  · use fun i => s (i.castLT (by grind))
    and_intros
    · simp
      rw [Nat.sub_eq_iff_eq_add]
      · rw [sh]
        rw [<-Finset.sum_erase_add (a:=⟨k-1, by grind⟩) _ _ (by simp)]
        rw [Nat.add_right_cancel_iff]
        apply Finset.sum_bij' (fun i _ => ⟨i.val, by grind⟩) (fun i _ => i.castLT (by grind)) <;> simp
        intro i
        unfold Fin.castLT
        grind
      · rw [sh]
        apply Finset.single_le_sum_of_canonicallyOrdered (f:=fun i => (s i)^2)
        simp
    · apply fun _ => sb _
  · use fun _ => s ⟨k-1, by grind⟩
    and_intros
    · simp
    · apply fun _ => sb _


theorem complete_mul (n1 n2) (lb1 : 13 ≤ n1) (lb2 : 13 ≤ n2) (n1h : complete n1) (n2h : complete n2) : complete (n1*n2) := by
  let k1 : ℕ+ := n1 ^ 2 - 14
  let k2 : ℕ+ := n2 ^ 2 - 14
  have n1n2_lb : 13*13 ≤ n1*n2 := mul_le_mul' lb1 lb2
  have n1n2_lb' : 13*13 ≤ n1.val*n2.val := mul_le_mul' lb1 lb2
  rw [complete_iff_sos _ (by {
    trans 13*13
    · exact right_eq_inf.mp rfl
    · exact n1n2_lb
  })]
  intro k kb
  by_cases c : k1*k2 ≤ k
  · generalize Ndef : ((n1 * n2).val ^ 2) = N
    have N_lb : (13*13)^2 ≤ N := by
      rw [<-Ndef, PNat.mul_coe]
      exact Nat.pow_le_pow_left n1n2_lb 2
    have h14 : 3*N ≤ 4 * (n1 ^ 2 - 14).val * (n2 ^ 2 - 14).val := by
      qify
      repeat rw [PNat.sub_coe, ite_eq_left_iff.mpr, Nat.cast_sub]
      · simp only [PNat.pow_coe, Nat.cast_pow, PNat.val_ofNat, Nat.cast_ofNat]
        ring_nf
        have : n1.val ^ 2 * n2.val ^ 2 = (N : ℚ) := by
          rw [<-Ndef]
          simp [mul_pow]
        rw [this]
        suffices n1 ^ 2 * 56 + n2 ^ 2 * 56 ≤ 784 + (N : ℚ) by linarith
        suffices N/(n1^2) * 56 + N/(n2^2) * 56 ≤ 784 + (N : ℚ) by
          rw [<-Ndef] at this ⊢
          simp only [PNat.mul_coe, mul_pow, Nat.cast_mul, Nat.cast_pow, ne_eq, OfNat.ofNat_ne_zero,
            not_false_eq_true, pow_eq_zero_iff, Nat.cast_eq_zero, PNat.ne_zero, mul_div_cancel_left₀,
            isUnit_iff_ne_zero, IsUnit.mul_div_cancel_right] at this
          simp only [PNat.mul_coe, Nat.cast_pow, Nat.cast_mul, ge_iff_le]
          linarith
        calc
          _ ≤ ↑N / 13 ^ 2 * 56 + ↑N / 13 ^ 2 * 56 := by
            apply add_le_add <;> {
              rw [mul_le_mul_iff_left₀ (by simp)]
              apply div_le_div_of_nonneg_left
              · simp
              · simp
              · apply pow_left_monotoneOn
                · simp
                · simp
                · apply Nat.ofNat_le_cast.mpr
                  rw [<-PNat.val_ofNat, PNat.coe_le_coe]
                  simp [lb1, lb2]
            }
          _ ≤ (N : ℚ) := by
            ring_nf
            rw [<-mul_div_assoc, div_le_iff₀]
            · apply Rat.mul_le_mul_of_nonneg_left rfl
              simp
            · simp
          _ ≤ 784 + ↑N := by
            simp
      · trans 13^2
        · simp
        · apply pow_left_mono
          exact lb2
      · intro h
        contrapose! h
        rw [<-PNat.coe_lt_coe]
        apply Nat.lt_of_succ_le
        trans 13^2
        · simp
        · apply pow_left_mono
          exact lb2
      · trans 13^2
        · simp
        · apply pow_left_mono
          exact lb1
      · intro h
        contrapose! h
        rw [<-PNat.coe_lt_coe]
        apply Nat.lt_of_succ_le
        trans 13^2
        · simp
        · apply pow_left_mono
          exact lb1
    let C1 : Multiset ℕ+ := msos.mk [(N-17,1), (2,2), (1,3)]
    have C1_card : C1.card = N-14 := by
      unfold C1
      simp only [msos.card_mk, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, Nat.reduceAdd]
      rw [<-Nat.sub_add_comm]
      · simp
      · apply le_trans (by simp) N_lb
    have C1_sq_sum : msos.sq_sum C1 = N := by
      unfold C1
      simp only [msos.sq_sum_mk, List.map_cons, PNat.val_ofNat, one_pow, mul_one, Nat.reducePow,
        Nat.reduceMul, one_mul, List.map_nil, List.sum_cons, List.sum_nil, add_zero, Nat.reduceAdd]
      apply Nat.sub_add_cancel
      · apply le_trans (by simp) N_lb
    let C2 : Multiset ℕ+ := msos.mk [(N-20,1), (5,2)]
    have C2_card : C2.card = N-15 := by
      unfold C2
      simp only [msos.card_mk, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      rw [<-Nat.sub_add_comm]
      · simp
      · apply le_trans (by simp) N_lb
    have C2_sq_sum : msos.sq_sum C2 = N := by
      unfold C2
      simp only [msos.sq_sum_mk, List.map_cons, PNat.val_ofNat, one_pow, mul_one, Nat.reducePow,
        Nat.reduceMul, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      apply Nat.sub_add_cancel
      · apply le_trans (by simp) N_lb
    let C3 : Multiset ℕ+ := msos.mk [(N-18,1), (2,3)]
    have C3_card : C3.card = N-16 := by
      unfold C3
      simp only [msos.card_mk, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      rw [<-Nat.sub_add_comm]
      · simp
      · apply le_trans (by simp) N_lb
    have C3_sq_sum : msos.sq_sum C3 = N := by
      unfold C3
      simp only [msos.sq_sum_mk, List.map_cons, PNat.val_ofNat, one_pow, mul_one, Nat.reducePow,
        Nat.reduceMul, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      apply Nat.sub_add_cancel
      · apply le_trans (by simp) N_lb
    have kb' : k ≤ N - 14 := by
      rw [<-PNat.coe_le_coe] at kb
      rw [<-Ndef]
      rw [PNat.sub_coe, ite_eq_left_iff.mpr] at kb
      · exact kb
      · intro h
        contrapose h
        apply PNat.add_one_le_iff.mp
        rw [<-PNat.coe_le_coe]
        trans (13*13)^2
        · simp
        · rw [PNat.pow_coe, PNat.mul_coe]
          exact Nat.pow_le_pow_left n1n2_lb 2
    unfold k1 k2 at c
    rw [<-PNat.coe_le_coe, PNat.mul_coe] at c
    have : k.val%3 = (N-14)%3 ∨ k.val%3 = (N-15)%3 ∨ k.val%3 = (N-16)%3 := by omega
    apply this.elim3
    · rw [<-C1_card, <-C1_sq_sum]
      apply is_sum_of_pos_squares_by_repeat_shift
      rw [Finset.mem_Icc]
      and_intros
      · apply le_trans _ c
        apply le_trans (msos.card_repeat_shift_le _)
        rw [C1_card]
        unfold C1
        simp only [msos.count_mk, BEq.rfl, List.filter_cons_of_pos, beq_iff_eq, PNat.ofNat_inj,
          OfNat.ofNat_ne_one, not_false_eq_true, List.filter_cons_of_neg, List.filter_nil,
          List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, tsub_le_iff_right]
        apply le_of_mul_le_mul_left (a:=4) _ (by simp)
        rw [mul_add, mul_add, <-mul_assoc]
        rw [<-add_le_add_iff_left N] at h14
        trans N+3*N
        · grind
        · apply le_trans h14
          omega
      · rw [C1_card]
        exact kb'
    · rw [<-C2_card, <-C2_sq_sum]
      intro m
      apply is_sum_of_pos_squares_by_repeat_shift _ _ _ m
      rw [Finset.mem_Icc]
      and_intros
      · apply le_trans _ c
        apply le_trans (msos.card_repeat_shift_le _)
        rw [C2_card]
        unfold C2
        simp only [msos.count_mk, BEq.rfl, List.filter_cons_of_pos, beq_iff_eq, PNat.ofNat_inj,
          OfNat.ofNat_ne_one, not_false_eq_true, List.filter_cons_of_neg, List.filter_nil,
          List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, tsub_le_iff_right]
        apply le_of_mul_le_mul_left (a:=4) _ (by simp)
        rw [mul_add, mul_add, <-mul_assoc]
        rw [<-add_le_add_iff_left N] at h14
        trans N+3*N
        · grind
        · apply le_trans h14
          omega
      · rw [C2_card] at m ⊢
        omega
    · rw [<-C3_card, <-C3_sq_sum]
      intro m
      apply is_sum_of_pos_squares_by_repeat_shift _ _ _ m
      rw [Finset.mem_Icc]
      and_intros
      · apply le_trans _ c
        apply le_trans (msos.card_repeat_shift_le _)
        rw [C3_card]
        unfold C3
        simp only [msos.count_mk, BEq.rfl, List.filter_cons_of_pos, beq_iff_eq, PNat.ofNat_inj,
          OfNat.ofNat_ne_one, not_false_eq_true, List.filter_cons_of_neg, List.filter_nil,
          List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, tsub_le_iff_right]
        apply le_of_mul_le_mul_left (a:=4) _ (by simp)
        rw [mul_add, mul_add, <-mul_assoc]
        rw [<-add_le_add_iff_left N] at h14
        trans N+3*N
        · grind
        · apply le_trans h14
          omega
      · rw [C3_card] at m ⊢
        omega
  · rw [complete_iff_sos] at n1h n2h
    · simp at c
      obtain ⟨u,v,hk, ub, vb⟩ : ∃ u v : ℕ+, k = (u.val-1)*k2+v ∧ u ≤ k1 ∧ v ≤ k2 := by
        use ⟨k.natPred/k2.val+1, by simp⟩
        use ⟨k - (k.natPred/k2.val)*k2, by {
          simp only [tsub_pos_iff_lt]
          apply lt_of_le_of_lt (b:=k.natPred)
          · exact Nat.div_mul_le_self k.natPred ↑k2
          · simp [PNat.natPred]
        }⟩
        and_intros
        · simp only [PNat.mk_coe, add_tsub_cancel_right]
          rw [Nat.add_sub_cancel']
          trans k.natPred
          · apply Nat.div_mul_le_self
          · simp [PNat.natPred]
        · rw [<-PNat.coe_le_coe, PNat.mk_coe]
          have : k/k2.val < k1 := by
            apply Nat.lt_of_mul_lt_mul_right (a:=k2)
            apply lt_of_le_of_lt (b:=k.val)
            · exact Nat.div_mul_le_self ↑k ↑k2
            · exact Nat.lt_of_succ_le c
          trans ↑k / ↑k2 + 1
          · rw [add_le_add_iff_right]
            apply Nat.div_le_div_right
            simp [PNat.natPred]
          · exact Order.add_one_le_iff.mpr this
        · rw [<-PNat.coe_le_coe]
          simp only [PNat.mk_coe, tsub_le_iff_right, PNat.natPred]
          rw [Nat.div_mul_self_eq_mod_sub_self]
          rw [<-Nat.add_sub_assoc, Nat.sub_add_comm, <-Nat.sub_le_iff_le_add, Nat.sub_sub_self, Nat.le_sub_iff_add_le, Nat.one_add_le_iff]
          · apply Nat.mod_lt
            simp
          · apply le_of_lt
            apply Nat.mod_lt
            simp
          · exact NeZero.one_le
          · apply le_of_lt
            apply Nat.mod_lt
            simp
          · apply Nat.mod_le
      obtain ⟨d, dpos, db, dh1, dh2⟩ := sos_split (n1 ^ 2) u u.prop (n1h u ub)
      have : (n1 * n2).val ^ 2 = (n1^2-d^2) * n2^2 + d^2*n2^2 := by
        rw [Nat.sub_mul, PNat.mul_coe, mul_pow, Nat.sub_add_cancel]
        exact Nat.mul_le_mul_right (↑n2 ^ 2) db
      rw [this, hk]
      apply sos_add
      · apply sos_mul
        · apply dh1
        · apply n2h
          rfl
      · rw [mul_comm]
        apply sos_mul_const
        · exact dpos
        · apply n2h v
          exact vb
    · trans 13 <;> simp [lb2]
    · trans 13 <;> simp [lb1]


theorem imo1992_p6_c : {n | S n = n^2 - 14}.Infinite := by
  suffices ∀ e > 0, complete (13^e) by
    unfold complete at this
    refine Set.infinite_of_forall_exists_gt ?_
    intro a
    use 13^a.val
    and_intros
    · apply this
      simp
    · calc
        _ < 13*a := by
          simp_all only [lt_mul_iff_one_lt_left', PNat.ofNat_lt_ofNat, Nat.one_lt_ofNat]
        _ ≤ _ := by
          apply Nat.mul_le_pow
          exact Nat.add_one_add_one_ne_one
  intro e
  apply Nat.le_induction
  · simp [complete_13]
  · intro e' e'pos ih
    rw [pow_add]
    apply complete_mul
    · nth_rw 1 [<-pow_one 13]
      apply pow_right_monotone (by simp)
      exact Nat.one_le_of_lt e'pos
    · simp
    · exact ih
    · simp [complete_13]

snip end


determine imo1992_p6_b : ℕ+ := 13

problem imo1992_p6 : (∀ n ≥ 4, S n ≤ n^2-14) ∧ (S imo1992_p6_b = imo1992_p6_b^2 - 14) ∧ ({n | S n = n^2 - 14}.Infinite) := by
  and_intros
  · exact imo1992_p6_a
  · exact complete_13
  · exact imo1992_p6_c


end Imo1992P6
