/-
Copyright (c) 2026 Constantin Seebach. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Constantin Seebach
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file {
  tags := [.Algebra]
}

/-!
# International Mathematical Olympiad 2005, Problem 2

Let $a_1, a_2, \dots$ be a sequence of integers with infinitely many positive and negative terms.
Suppose that for every positive integer $n$ the numbers $a_1, a_2, \dots, a_n$ leave $n$ different remainders upon division by $n$.
Prove that every integer occurs exactly once in the sequence.
-/

namespace Imo2005P2


snip begin

/-
We follow the proof from https://artofproblemsolving.com/wiki/index.php/2005_IMO_Problems/Problem_2
-/

def prefix_max (a : ℕ → ℤ) (n : ℕ) (npos : 0 < n) : ℤ :=
  Finset.max' ((Finset.range n).image (fun i => a i)) (by {
    simp only [Finset.image_nonempty, Finset.nonempty_range_iff, ne_eq]
    exact Nat.ne_zero_of_lt npos
  })

def prefix_min (a : ℕ → ℤ) (n : ℕ) (npos : 0 < n) : ℤ :=
  Finset.min' ((Finset.range n).image (fun i => a i)) (by {
    simp only [Finset.image_nonempty, Finset.nonempty_range_iff, ne_eq]
    exact Nat.ne_zero_of_lt npos
  })

def consecutive {S : Type} [SetLike S ℤ] (s : S) : Prop := ∀ (a b c : ℤ), a < b → b < c → a ∈ s → c ∈ s → b ∈ s

theorem consecutive' {S : Type} [SetLike S ℤ] {s : S} (h : consecutive s) : ∀ (a b c : ℤ), a ≤ b → b ≤ c → a ∈ s → c ∈ s → b ∈ s := by
  unfold consecutive at h
  grind only

theorem consecutive_insert_max' (s : Finset ℤ) (hne : s.Nonempty) (hc : consecutive s) : consecutive (insert (s.max' hne + 1) s) := by
  intro a b c h1 h2 u1 u2
  by_cases m : c < s.max' hne + 1
  · suffices b ∈ s by exact Finset.mem_insert_of_mem this
    apply hc a b c h1 h2 <;> grind only [= Finset.mem_insert]
  · have : c = s.max' hne + 1 := by
      simp at m
      simp at u2
      apply u2.by_cases (by simp)
      intro h
      have : s.max' hne < c := by exact (Finset.max'_lt_iff s hne).mpr m
      rw [Finset.max'_lt_iff s hne (x:=c)] at this
      grind only [this _ h]
    subst this
    by_cases m' : b = s.max' hne
    · subst m'
      simp only [Finset.mem_insert, left_eq_add, one_ne_zero, false_or]
      exact Finset.max'_mem s hne
    have : b < s.max' hne := by omega
    suffices b ∈ s by exact Finset.mem_insert_of_mem this
    apply hc a b (s.max' hne) h1 this
    · grind
    · exact Finset.max'_mem s hne

theorem consecutive_insert_min' (s : Finset ℤ) (hne : s.Nonempty) (hc : consecutive s) : consecutive (insert (s.min' hne - 1) s) := by
  intro a b c h1 h2 u1 u2
  by_cases m : s.min' hne - 1 < a
  · suffices b ∈ s by exact Finset.mem_insert_of_mem this
    apply hc a b c h1 h2 <;> grind only [= Finset.mem_insert]
  · have : a = s.min' hne - 1 := by
      simp at m
      simp at u1
      apply u1.by_cases (by simp)
      intro h
      have : a < s.min' hne := by exact (Finset.lt_min'_iff s hne).mpr m
      rw [Finset.lt_min'_iff s hne (x:=a)] at this
      grind only [this _ h]
    subst this
    by_cases m' : b = s.min' hne
    · subst m'
      refine Finset.mem_insert_of_mem ?_
      exact Finset.min'_mem s hne
    have : s.min' hne < b := by omega
    suffices b ∈ s by exact Finset.mem_insert_of_mem this
    apply hc (s.min' hne) b c this h2
    · exact Finset.min'_mem s hne
    · grind

theorem a_injective (a : ℕ → ℤ) (rem : ∀ n > 0, ((Finset.range n).image (fun i => a i % n)).card = n) : Function.Injective a := by
  intro i1 i2 e
  contrapose! rem
  let B := 1 + max i1 i2
  use B, (by unfold B; simp)
  nth_rw 3 [<-Finset.card_range B]
  rw [ne_eq, Finset.card_image_iff]
  rw [Set.InjOn]
  simp only [Finset.coe_range, Set.mem_Iio, not_forall, exists_prop]
  use i1, ?_, i2, ?_, ?_
  · unfold B
    omega
  · unfold B
    omega
  · rw [e]

theorem mod_nonzero (a : ℕ → ℤ) (rem : ∀ n > 0, ((Finset.range n).image (fun i => a i % n)).card = n) (a0 : a 0 = 0)
: ∀ n > 0, ∀ d > n, ¬ a n % d = 0 := by
  intro n npos d dgt
  contrapose! rem
  use d, (by grind)
  nth_rw 3 [<-Finset.card_range d]
  rw [ne_eq, Finset.card_image_iff]
  rw [Set.InjOn]
  simp only [Finset.coe_range, Set.mem_Iio, not_forall, exists_prop]
  use 0, ?_, n, ?_, ?_
  · exact Nat.ne_of_lt npos
  · grind
  · exact dgt
  · rw [rem, a0]
    simp

theorem abs_bound (a : ℕ → ℤ) (rem : ∀ n > 0, ((Finset.range n).image (fun i => a i % n)).card = n) (a0 : a 0 = 0)
: ∀ n, |a n| ≤ n := by
  intro n
  by_cases nz : n = 0
  · subst nz
    rw [a0]
    simp
  by_contra! c
  have : ¬ a n % (a n).natAbs = 0 := by
    apply mod_nonzero a rem a0 n
    · exact Nat.zero_lt_of_ne_zero nz
    · grind
  simp only [Nat.cast_natAbs, Int.cast_abs, Int.cast_eq, Int.emod_abs, EuclideanDomain.mod_self,
    not_true_eq_false] at this

theorem an_inductive' (a : ℕ → ℤ) (rem : ∀ n > 0, ((Finset.range n).image (fun i => a i % n)).card = n) (a0 : a 0 = 0)
: ∀ n, consecutive ((Finset.range n).image (fun i => a i)) ∧ ∀ npos: n > 0, (a n = prefix_max a n npos + 1 ∨ a n = prefix_min a n npos - 1) := by
  intro n
  induction n with
  | zero =>
    unfold consecutive
    simp
  | succ n ih =>
    rw [show ∀ (a b : Prop), a ∧ b ↔ a ∧ (a → b) by grind only]
    and_intros
    · have : Finset.image (fun i ↦ a i) (Finset.range (n + 1)) = insert (a n) (Finset.image (fun i ↦ a i) (Finset.range n)) := by
        rw [Finset.insert_eq]
        ext x
        simp only [Finset.mem_image, Finset.mem_range, Order.lt_add_one_iff, Finset.singleton_union,
          Finset.mem_insert]
        grind
      rw [this]
      by_cases npos : 0 < n
      · apply (ih.right npos).by_cases
        · intro h
          rw [h]
          apply consecutive_insert_max'
          apply ih.left
        · intro h
          rw [h]
          apply consecutive_insert_min'
          apply ih.left
      · simp only [not_lt, nonpos_iff_eq_zero] at npos
        subst npos
        intro x y z
        grind

    · intro con npos'
      have notmod' : ∀ i ≤ n, ¬ a i = (a (n+1) : ZMod (n+2)) := by
        intro i ilen
        contrapose! rem
        use n+2, (by simp)
        nth_rw 3 [<-Finset.card_range (n+2)]
        rw [ne_eq, Finset.card_image_iff]
        rw [Set.InjOn]
        simp
        use i, (by grind), n+1, (by simp)
        and_intros
        · rw [ZMod.intCast_eq_intCast_iff] at rem
          exact Int.ModEq.eq rem
        · grind only

      let modset := Finset.image (fun i ↦ a i % ↑(n+2)) (Finset.range (n+2))

      have modset_Ico : modset = Finset.Ico (α:=ℤ) 0 (n+2) := by
        unfold modset
        rw [<-Finset.eq_iff_card_le_of_subset]
        · rw [rem]
          repeat simp
        · refine Finset.image_subset_iff.mpr ?_
          intro i _
          rw [Finset.mem_Ico]
          and_intros
          · apply Int.emod_nonneg
            omega
          · apply Int.emod_lt_of_pos
            omega

      have hmodmax : (prefix_max a (n + 1) npos' + 1).cast = (a (n + 1) : ZMod (n+2)) := by
        have : (a (n+1) - 1) % (n+2) ∈ modset := by
          rw [modset_Ico, Finset.mem_Ico]
          and_intros
          · apply Int.emod_nonneg
            omega
          · apply Int.emod_lt_of_pos
            omega
        unfold modset at this
        simp only [Nat.cast_add, Nat.cast_ofNat, Finset.mem_image, Finset.mem_range] at this
        let ⟨i, h1, h2⟩ := this
        rw [<-Int.ModEq] at h2
        rw [show @Nat.cast ℤ _ n + 2 = (n+2).cast by simp] at h2
        rw [<-ZMod.intCast_eq_intCast_iff] at h2
        have h1 : i < n+1 := by
          by_contra
          have : i = n+1 := by omega
          subst i
          rw [<-sub_eq_zero] at h2
          simp only [Int.cast_sub, Int.cast_one, sub_sub_cancel] at h2
          rw [ZMod.one_eq_zero_iff] at h2
          grind only
        have : a i + 1 = (a (n + 1) : ZMod (n+2)) := by
          rw [h2]
          simp
        rw [<-this]
        simp only [Int.cast_add, Int.cast_one, add_left_inj]
        unfold prefix_max
        let := Finset.max'_mem (Finset.image (fun i ↦ a i) (Finset.range (n + 1))) (by simp)
        simp only [Finset.mem_image, Finset.mem_range, Order.lt_add_one_iff] at this
        let ⟨j, jb, jh⟩ := this
        rw [<-jh]
        congr
        by_contra c
        let := consecutive' con (a i) (a i + 1) (a j) (by simp) ?_ ?_ ?_
        · simp only [Finset.mem_image, Finset.mem_range, Order.lt_add_one_iff] at this
          let ⟨k, kh1, kh2⟩ := this
          contrapose! notmod'
          use k, kh1
          rw [kh2, Int.cast_add, h2]
          simp
        · rw [jh]
          rw [Order.add_one_le_iff]
          apply Finset.lt_max'_of_mem_erase_max'
          simp only [Finset.mem_erase, ne_eq, Finset.mem_image, Finset.mem_range,
            Order.lt_add_one_iff]
          rw [<-jh]
          and_intros
          · rw [Eq.comm]
            exact Ne.intro fun x ↦ c (a_injective _ rem x)
          · use i
            simp only [and_true]
            exact Nat.le_of_lt_succ h1
        · simp only [Finset.mem_image, Finset.mem_range, Order.lt_add_one_iff]
          use i
          simp [Nat.le_of_lt_succ h1]
        · simp only [Finset.mem_image, Finset.mem_range, Order.lt_add_one_iff]
          use j

      have hmodmin : (prefix_min a (n + 1) npos' - 1).cast = (a (n + 1) : ZMod (n+2)) := by
        have : (a (n+1) + 1) % (n+2) ∈ modset := by
          rw [modset_Ico, Finset.mem_Ico]
          and_intros
          · apply Int.emod_nonneg
            omega
          · apply Int.emod_lt_of_pos
            omega
        unfold modset at this
        simp only [Nat.cast_add, Nat.cast_ofNat, Finset.mem_image, Finset.mem_range] at this
        let ⟨i, h1, h2⟩ := this
        rw [<-Int.ModEq] at h2
        rw [show @Nat.cast ℤ _ n + 2 = (n+2).cast by simp] at h2
        rw [<-ZMod.intCast_eq_intCast_iff] at h2
        have h1 : i < n+1 := by
          by_contra
          have : i = n+1 := by omega
          subst i
          rw [<-sub_eq_zero] at h2
          simp only [Int.cast_add, Int.cast_one, sub_add_cancel_left, neg_eq_zero] at h2
          rw [ZMod.one_eq_zero_iff] at h2
          grind only
        have : a i - 1 = (a (n + 1) : ZMod (n+2)) := by
          rw [h2]
          simp
        rw [<-this]
        simp only [Int.cast_sub, Int.cast_one, sub_left_inj]
        unfold prefix_min
        let := Finset.min'_mem (Finset.image (fun i ↦ a i) (Finset.range (n + 1))) (by simp)
        simp only [Finset.mem_image, Finset.mem_range, Order.lt_add_one_iff] at this
        let ⟨j, jb, jh⟩ := this
        rw [<-jh]
        congr
        by_contra c
        let := consecutive' con (a j) (a i - 1) (a i) ?_ (by simp) ?_ ?_
        · simp only [Finset.mem_image, Finset.mem_range, Order.lt_add_one_iff] at this
          let ⟨k, kh1, kh2⟩ := this
          contrapose! notmod'
          use k, kh1
          rw [kh2, Int.cast_sub, h2]
          simp
        · rw [jh]
          rw [Order.le_sub_one_iff]
          apply Finset.min'_lt_of_mem_erase_min'
          simp only [Finset.mem_erase, ne_eq, Finset.mem_image, Finset.mem_range,
            Order.lt_add_one_iff]
          rw [<-jh]
          and_intros
          · rw [Eq.comm]
            exact Ne.intro fun x ↦ c (a_injective _ rem x)
          · use i
            simp only [and_true]
            exact Nat.le_of_lt_succ h1
        · simp only [Finset.mem_image, Finset.mem_range, Order.lt_add_one_iff]
          use j
        · simp only [Finset.mem_image, Finset.mem_range, Order.lt_add_one_iff]
          use i
          simp [Nat.le_of_lt_succ h1]

      by_cases pos : a (n+1) > 0
      · apply Or.inl
        have : (@Int.cast (ZMod (n+2)) _ (a (n + 1))).cast = a (n+1) := by
          have : (@Int.cast (ZMod (n+2)) _ (a (n + 1))) = ⟨(a (n+1)).toNat, by {
            rw [Nat.lt_add_one_iff]
            zify
            trans |a (n+1)|
            · simp only [Int.ofNat_toNat, sup_le_iff, abs_nonneg, and_true]
              exact le_abs_self _
            · apply abs_bound _ rem a0
          }⟩ := by
            rw [ZMod.intCast_eq_iff]
            use 0
            simp only [ZMod.natCast_val, Nat.cast_add, Nat.cast_ofNat, mul_zero, add_zero]
            rw [ZMod.cast_eq_val]
            unfold ZMod.val
            simp only [Int.ofNat_toNat, left_eq_sup]
            exact Int.le_of_lt pos
          rw [this]
          rw [ZMod.cast_eq_val]
          unfold ZMod.val
          simp only [Int.ofNat_toNat, sup_eq_left, ge_iff_le]
          exact Int.le_of_lt pos
        rw [ZMod.intCast_eq_iff] at hmodmax
        let ⟨k, kh⟩ := hmodmax
        simp only [ZMod.natCast_val, Nat.cast_add, Nat.cast_ofNat] at kh
        rw [this] at kh
        rw [kh]
        let := Finset.max'_mem (Finset.image (fun i ↦ a i) (Finset.range (n + 1))) (by simp)
        simp only [Finset.mem_image, Finset.mem_range, Order.lt_add_one_iff] at this
        let ⟨j, jb, jh⟩ := this
        unfold prefix_max at kh
        rw [<-jh, Int.sub_eq_iff_eq_add.symm] at kh
        have nkneg : ¬ k < 0 := by
          have : _ := abs_bound _ rem a0 (n+1)
          rw [<-kh] at this
          rw [abs_le] at this
          let := this.right
          have : a j ≥ 0 := by
            rw [jh]
            apply Finset.le_max'
            simp only [Finset.mem_image, Finset.mem_range, Order.lt_add_one_iff]
            use 0
            simp [a0]
          have : - ↑(n + 1) ≤ (↑n + 2) * k := by omega
          contrapose! this
          suffices (↑n + 2) * k ≤ (↑n + 2) * (-1) by omega
          rw [mul_le_mul_iff_of_pos_left]
          · exact Int.add_le_zero_iff_le_neg.mp this
          · exact Int.sign_eq_one_iff_pos.mp rfl
        have nkpos : ¬ k > 0 := by
          rw [<-kh] at pos
          simp at pos
          have : a j ≤ j := by
            have : _ := abs_bound _ rem a0 j
            rw [abs_le] at this
            exact this.right
          have : (n + 2) * k ≤ n := by omega
          contrapose! this
          apply Int.lt_of_add_one_le
          trans n+2
          · simp
          · nth_rw 1 [<-mul_one (n.cast+2)]
            rw [mul_le_mul_iff_of_pos_left]
            · exact Int.le_of_sub_one_lt this
            · exact Int.sign_eq_one_iff_pos.mp rfl
        grind only
      · apply Or.inr
        have neg : a (n+1) < 0 := by
          let := a_injective a rem
          grind only
        have : (@Int.cast (ZMod (n+2)) _ (a (n + 1))).cast = n+2 + a (n+1) := by
          have : (@Int.cast (ZMod (n+2)) _ (a (n + 1))) = ⟨(n+2 + a (n+1)).toNat, by {
            rw [Nat.lt_add_one_iff]
            zify
            simp only [Int.ofNat_toNat, sup_le_iff]
            and_intros
            · linarith
            · exact Int.zero_le_ofNat (n + 1)
          }⟩ := by
            rw [ZMod.intCast_eq_iff]
            use -1
            simp
            rw [ZMod.cast_eq_val]
            unfold ZMod.val
            simp
            rw [max_eq_left]
            · linarith
            · let := abs_le.mp (abs_bound _ rem a0 (n+1))
              omega
          rw [this]
          rw [ZMod.cast_eq_val]
          unfold ZMod.val
          simp only [Int.ofNat_toNat, sup_eq_left, ge_iff_le]
          let := abs_le.mp (abs_bound _ rem a0 (n+1))
          omega
        rw [ZMod.intCast_eq_iff] at hmodmin
        let ⟨k, kh⟩ := hmodmin
        simp only [ZMod.natCast_val, Nat.cast_add, Nat.cast_ofNat] at kh
        rw [this] at kh
        rw [kh]
        let := Finset.min'_mem (Finset.image (fun i ↦ a i) (Finset.range (n + 1))) (by simp)
        simp only [Finset.mem_image, Finset.mem_range, Order.lt_add_one_iff] at this
        let ⟨j, jb, jh⟩ := this
        unfold prefix_min at kh
        rw [<-jh] at kh
        have kh : a j - 1 - (↑n + 2) * (k+1) = a (n + 1) := by linarith
        suffices k = -1 by subst k; linarith
        have nkpos : ¬ k+1 > 0 := by
          have : _ := abs_bound _ rem a0 (n+1)
          rw [<-kh] at this
          rw [abs_le] at this
          let ⟨h1, h2⟩ := this
          have : a j ≤ 0 := by
            rw [jh]
            apply Finset.min'_le
            simp only [Finset.mem_image, Finset.mem_range, Order.lt_add_one_iff]
            use 0
            simp [a0]
          have : - ↑(n + 1) ≤ - 1 - (↑n + 2) * (k + 1) := by omega
          contrapose! this
          suffices - (↑n + 2) * (k + 1) ≤ -↑(n + 1) by linarith
          suffices ↑(n + 2) * 1 ≤ ↑(n + 2) * (k + 1) by simp only [Nat.cast_add, Nat.cast_ofNat] at this; omega
          rw [mul_le_mul_iff_of_pos_left]
          · exact Int.le_of_sub_one_lt this
          · exact Int.sign_eq_one_iff_pos.mp rfl
        have nkneg : ¬ k+1 < 0 := by
          rw [<-kh] at neg
          simp at neg
          have : a j ≥ -j := by
            have : _ := abs_bound _ rem a0 j
            rw [abs_le] at this
            omega
          have : (n + 2) * (k+1) ≥ -n := by omega
          contrapose! this
          apply Int.lt_of_le_sub_one
          trans -n-2
          · suffices (↑n + 2) * (k + 1) ≤ (↑n + 2) * (-1) by linarith
            rw [mul_le_mul_iff_of_pos_left]
            · exact Int.add_le_zero_iff_le_neg.mp this
            · exact Int.sign_eq_one_iff_pos.mp rfl
          · simp
        grind only

snip end


problem imo2005_p2 (a : ℕ → ℤ)
  (pos_inf : Set.Infinite {a i | (i) (_: 0 < a i)})
  (neg_inf : Set.Infinite {a i | (i) (_: a i < 0)})
  (rem : ∀ n > 0, ((Finset.range n).image (fun i => a i % n)).card = n)
    : ∀ z : ℤ, ∃! i, a i = z := by
  wlog a0 : a 0 = 0
  · let a' (i) := a i - a 0
    have : _ := this a' ?_ ?_ ?_ ?_
    · intro z
      unfold a' at this
      let := this (z - a 0)
      simp only [sub_left_inj] at this
      exact this
    · unfold a'
      apply Set.infinite_of_not_bddAbove
      have : Set.Infinite ((·.toNat) '' {a i | (i) (pos: 0 < a i)}) := by
        refine Set.Infinite.image ?_ pos_inf
        intro x1 h1 x2 h2 e
        grind
      let := Set.Infinite.not_bddAbove this
      rw [not_bddAbove_iff] at this ⊢
      intro b
      let ⟨y, yh⟩ := this (b.natAbs + (a 0).natAbs)
      use y - a 0
      simp only [exists_prop, Set.mem_image, Set.mem_setOf_eq, exists_exists_and_eq_and,
        Int.sub_pos, sub_left_inj] at yh ⊢
      let ⟨⟨i, h1, h2⟩, h3⟩ := yh
      and_intros
      · use i
        and_intros
        · grind only
        · grind only
      · grind only
    · unfold a'
      apply Set.infinite_of_not_bddBelow
      have : Set.Infinite ((fun x => (-x).toNat) '' {a i | (i) (neg: a i < 0)}) := by
        refine Set.Infinite.image ?_ neg_inf
        intro x1 h1 x2 h2 e
        grind
      let := Set.Infinite.not_bddAbove this
      rw [not_bddAbove_iff] at this
      rw [not_bddBelow_iff] at ⊢
      intro b
      let ⟨y, yh⟩ := this (b.natAbs + (a 0).natAbs)
      use -y - a 0
      simp only [exists_prop, Set.mem_image, Set.mem_setOf_eq, exists_exists_and_eq_and, sub_neg,
        sub_left_inj] at yh ⊢
      let ⟨⟨i, h1, h2⟩, h3⟩ := yh
      and_intros
      · use i
        and_intros
        · grind only
        · grind only
      · grind only
    · intro n npos
      nth_rw 3 [<-rem n npos]
      apply Finset.card_bij (fun x h => (x + a 0)%n)
      · simp
        intro x xltn
        use x
        and_intros
        · exact xltn
        · unfold a'
          simp
      · unfold a'
        simp only [Finset.mem_image, Finset.mem_range, forall_exists_index, and_imp,
          forall_apply_eq_imp_iff₂, Int.emod_add_emod, sub_add_cancel]
        intro x1 _ x2 _ e
        rw [Int.sub_emod, Int.sub_emod]
        rw [e]
        simp
      · simp only [Finset.mem_image, Finset.mem_range, exists_prop, exists_exists_and_eq_and,
          Int.emod_add_emod, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
        intro x xltn
        use x
        and_intros
        · exact xltn
        · unfold a'
          simp
    · unfold a'
      simp

  suffices Function.Surjective a by
    apply Function.Bijective.existsUnique
    and_intros
    · exact a_injective a rem
    · exact this

  intro z
  let con (n) := (an_inductive' a rem a0 n).left
  have : z = 0 ∨ z < 0 ∨ 0 < z := by grind only
  apply this.elim3
  · intro zz
    subst zz
    use 0
  · intro zneg
    obtain ⟨i, ih⟩ : ∃ i, a i < z := by
      have : Set.Infinite ((fun x => (-x).toNat) '' {a i | (i) (neg: a i < 0)}) := by
        refine Set.Infinite.image ?_ neg_inf
        intro x1 h1 x2 h2 e
        grind
      let := Set.Infinite.not_bddAbove this
      rw [not_bddAbove_iff] at this
      let ⟨y, yh1, yh2⟩ := this (-z).toNat
      simp only [exists_prop, Set.mem_image, Set.mem_setOf_eq, exists_exists_and_eq_and] at yh1
      let ⟨i, ih⟩ := yh1
      use i
      omega
    let := (con (i+1)) (a i) z 0 ?_ ?_ ?_ ?_
    · simp only [Finset.mem_image, Finset.mem_range, Order.lt_add_one_iff] at this
      grind only
    · exact ih
    · exact zneg
    · rw [Finset.mem_image]
      use i
      simp
    · rw [Finset.mem_image]
      use 0
      simp [a0]
  · intro zpos
    obtain ⟨i, ih⟩ : ∃ i, z < a i := by
      have : Set.Infinite ((·.toNat) '' {a i | (i) (pos: 0 < a i)}) := by
        refine Set.Infinite.image ?_ pos_inf
        intro x1 h1 x2 h2 e
        grind
      let := Set.Infinite.not_bddAbove this
      rw [not_bddAbove_iff] at this
      let ⟨y, yh1, yh2⟩ := this z.toNat
      simp only [exists_prop, Set.mem_image, Set.mem_setOf_eq, exists_exists_and_eq_and] at yh1
      let ⟨i, ih⟩ := yh1
      use i
      omega
    let := (con (i+1)) 0 z (a i) ?_ ?_ ?_ ?_
    · simp only [Finset.mem_image, Finset.mem_range, Order.lt_add_one_iff] at this
      grind only
    · exact zpos
    · exact ih
    · rw [Finset.mem_image]
      use 0
      simp [a0]
    · rw [Finset.mem_image]
      use i
      simp


end Imo2005P2
