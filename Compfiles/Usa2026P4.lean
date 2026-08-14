/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Liao
-/

module

public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Data.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics, .NumberTheory] }

/-!
# USA Mathematical Olympiad 2026, Problem 4

A positive integer n is called solitary if, for any non-negative integers a and b such
that a + b = n, either a or b contains the digit "1".
Determine, with proof, the number of solitary integers less than 10^2026.
-/

namespace Usa2026P4

open Classical

determine solution : ℕ := 2^2026 - 1

def has_digit_one (n : ℕ) : Prop :=
  1 ∈ Nat.digits 10 n

def is_solitary (n : ℕ) : Prop :=
  0 < n ∧ ∀ a b : ℕ, a + b = n → has_digit_one a ∨ has_digit_one b

snip begin
-- We follow Solution 1 by sillybone and Hpenguin from Art of Problem Solving.

lemma digit_squeeze {m k : ℕ} (hm : m ∈ Set.Ico (10 ^ k) (2 * 10 ^ k)) : 1 ∈ Nat.digits 10 m := by
  induction k generalizing m with
  | zero =>
    have ⟨_, _⟩ := hm
    interval_cases m
    rw [Nat.digits_of_lt 10 1 Nat.one_ne_zero (by decide)]
    exact List.mem_singleton_self _
  | succ k ih =>
    rw [Set.mem_Ico] at hm
    rw [Nat.digits_def' (by decide) (by omega)]
    exact List.mem_cons_of_mem _ <| @ih (m/10) (by grind)

lemma digits_last_mem {m k : ℕ} (h1 : 0 < m) (h2 : 10 ^ k ≤ m) (h3 : m / 10 ^ k < 10) : m / (10 ^ k) ∈ Nat.digits 10 m := by
  induction k generalizing m with
  | zero =>
    simp only [pow_zero, Nat.div_one]
    rw [Nat.digits_def' (by decide) h1]
    rw [Nat.mod_eq_of_lt (by omega)]
    exact List.mem_cons_self
  | succ k ih =>
    rw [Nat.digits_def' (by decide) h1]
    refine List.mem_cons_of_mem _ ?_
    rw [pow_succ', ← Nat.div_div_eq_div_mul]
    exact @ih (m / 10) (by grind) (by omega)
      (by rwa [Nat.div_div_eq_div_mul, ← pow_succ'])

lemma digits_last_mem₃ {a k : ℕ} : Nat.digits 10 (a % 10 ^ k) ++ [a / 10 ^ k % 10] = Nat.digits 10 (a % 10 ^ (k + 1)) := by
  induction k with
  | zero =>
    wlog! w : a % 10 ≠ 0
    simp
    simp [Nat.mod_one]
    rw [Nat.digits_of_lt 10 (a % 10) ?_ (show a % 10 < 10 by omega)]
    sorry
  | succ => sorry

lemma digits_div_subset' (a k : ℕ) : Nat.digits 10 (a % 10 ^ (k + 1)) <+: Nat.digits 10 a := by
  wlog! h : a % 10 ^ (k + 1) ≠ 0
  · simp [h]
  induction k with
  | zero =>
    rw [Nat.digits_def']
    simp [Nat.mod_one]
  | succ k ih =>
    rw [ih]

    nth_rw 2 [Nat.digits_def' (by decide)]
    rw [List.append_cons]
    rw [Nat.div_div_eq_div_mul, ← pow_succ]
    rw [List.append_left_inj]
    sorry

lemma digits_div_subset (a k : ℕ) : Nat.digits 10 (a % 10 ^ (k + 1)) ⊆ Nat.digits 10 a := by
  wlog! h : a % 10 ^ (k + 1) ≠ 0
  · simp [h]
  induction k with
  | zero =>
    rw [Nat.digits_def' (by decide) (by omega)]
    simp
    rw [Nat.digits_def' (by decide) (by omega)]
    exact List.mem_cons_self
  | succ k ih =>
    specialize ih sorry
    rw [Nat.digits_def' (by decide)]
    refine List.cons_subset.mpr ⟨?_, ?_⟩
    rw [Nat.mod_mod_of_dvd]

    rw [Nat.digits_def' (by decide)]
    · exact List.mem_cons_self
    · rw [Nat.ne_zero_iff_zero_lt] at h
      cases a
      · simp at h
      · simp
    · exact dvd_of_mul_left_eq _ rfl

    nth_rw 2 [Nat.digits_def' (by decide)]
    refine List.subset_cons_of_subset (a % 10) ?_

    convert ih
    rw [@Nat.mod_pow_succ]
    rw [Nat.digits_def' (by decide)] at ih
    all_goals sorry

lemma solitary_form (k : ℕ) : is_solitary (2 * 10 ^ k - 1) := by
  refine ⟨by grind, fun a b h => ?_⟩
  wlog! w : b ≤ a
  · exact this k b a (by rwa [add_comm]) w.le |>.symm
  have h1 : 10 ^ k ≤ a := by omega
  have : a ≤ 2 * 10 ^ k - 1 := by omega
  have h2 : a < 2 * 10 ^ k := (Nat.le_sub_one_iff_lt <| Nat.pos_of_neZero _).mp this
  exact Or.inl <| digit_squeeze ⟨h1, h2⟩

lemma solitary_one : is_solitary 1 := solitary_form 0

lemma solitary_iff (n k : ℕ) (hn1 : 0 < n) (hn2 : n < 10 ^ k) : is_solitary n ↔ is_solitary (2 * 10 ^ k + n) := by
  contrapose!
  constructor
  · intro hn hm
    unfold is_solitary at hn
    push Not at hn
    rcases hn hn1 with ⟨a, b, rfl, ha, hb⟩
    have ha' : ¬ has_digit_one (a + 2 * 10 ^ k) := by
      have h : (Nat.digits 10 a).length ≤ k := (Nat.digits_length_le_iff (by decide) a).mpr (by omega)
      rcases Nat.exists_eq_add_of_le h with ⟨l, hl⟩
      rw [mul_comm, has_digit_one, hl, ← Nat.digits_append_zeroes_append_digits (by decide) zero_lt_two]
      simpa [has_digit_one] using ha
    have := hm.2 (a + 2 * 10 ^ k) b (by omega)
    lia
  · intro hm hn
    unfold is_solitary at hm
    push Not at hm
    rcases hm <| Nat.add_pos_right _ hn1 with ⟨a, b, h, ha, hb⟩
    clear hm
    let a' := a % (10 ^ (k+1))
    let b' := b % (10 ^ (k+1))
    set x := a / (10 ^ k) with hxdef
    set y := b / (10 ^ k) with hydef
    -- In this step, AoPS claims a, b ≠ 1, but we actually want x, y ≠ 1.
    wlog! w : x ≤ y generalizing a b
    · apply this b a (by rwa [add_comm]) hb ha hydef hxdef w.le
    have : a ≤ 2 * 10 ^ k + n := by omega
    have : x ≤ 2 := calc
      _ ≤ a / 10 ^ k + b / 10 ^ k := Nat.le_add_right _ _
      _ ≤ (a + b) / 10 ^ k := Nat.div_add_div_le_add_div
      _ = (2 * 10 ^ k + n) / 10 ^ k := by rw [h]
      _ = _ := by simp [Nat.add_div, Nat.div_eq_of_lt, Nat.mod_eq_of_lt, hn2]
    have : x + y = 2 := calc a / 10 ^ k + b / 10 ^ k
      _ = (a + b) / 10 ^ k := by
        refine Eq.symm (Nat.add_div_eq_of_add_mod_lt ?_)
        sorry
      _ = (2 * 10 ^ k + n) / 10 ^ k := by rw [h]
      _ = _ := by simp [Nat.add_div, Nat.div_eq_of_lt, Nat.mod_eq_of_lt, hn2]

    interval_cases hx: x
    · have hy : y = 2 := by omega
      have := calc a' + b'
        _ = 2 * 10 ^ k + n - x * (10 ^ k) - y * (10 ^ k) := by
          simp [hx, hy]
          sorry
        _ = n := by simp [hx, hy]
      have hab := hn.2 a' b' this
      clear * - ha hb hab
      wlog ha' : has_digit_one a' generalizing a b
      · exact this b a hb ha hab.symm <| hab.resolve_left ha'
      clear * - ha' ha
      exact ha <| digits_div_subset a k ha'
    · clear hx
      absurd ha
      unfold has_digit_one
      rw [hxdef]
      refine @digits_last_mem a k ?_ ?_ (by rw [← hxdef]; decide)
      · rw [Nat.div_eq_sub_mod_div, Nat.eq_div_iff_mul_eq_left (Nat.ne_zero_of_lt hn2) (Nat.dvd_sub_mod a)] at hxdef
        omega
      · rw [← Nat.one_le_div_iff (Nat.zero_lt_of_lt hn2), hxdef]
    · omega

lemma nines (k a : ℕ) : a ∈ Nat.digits 10 ((10 ^ (k + 1)) - 1) ↔ a = 9 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.digits_def' (by decide) (by grind)]
    have (n : ℕ) : 9 = (10 ^ (n + 1 + 1) - 1) % 10 := by
      rw [← Nat.add_mod_right, ← Nat.sub_add_comm <| Nat.one_le_pow' _ _]
      simp [Nat.add_mod, Nat.pow_mod]
    constructor
    · rw [List.mem_cons]
      rintro (h | h)
      · rwa [this]
      · have (n : ℕ) : (10 ^ (n + 1 + 1) - 1) / 10 = 10 ^ (n + 1) - 1 := by omega
        rw [this] at h
        exact ih.mp h
    · rintro rfl
      refine List.mem_cons.mpr <| Or.inl <| this _

lemma solitary_range {m k : ℕ} (hm : m ∈ Finset.Ico (10 ^ k) (10 ^ (k + 1))) :
    is_solitary m ↔ m = 2 * 10 ^ k - 1 ∨ (∃ n ∈ Finset.Ico 1 (10 ^ k), is_solitary n ∧ m = 2 * 10 ^ k + n) := by
  wlog! w : k ≠ 0
  · subst w
    simp [is_solitary] at hm ⊢

    sorry

  constructor
  · contrapose!
    rintro ⟨hm1, hm2⟩
    rw [Finset.mem_Ico] at hm
    zify at hm1 hm2
    push_cast [Int.natCast_pred_of_pos, Nat.pos_of_neZero] at hm1
    -- by lemma 2, we know that 2 is not the leading digit of m
    intro solitary
    have : m < 2 * 10 ^ k ∨ (3 * 10 ^ k) ≤ m := by
      contrapose! hm2
      have h2 : 1 ≤ 2 * 10 ^ k := by omega
      zify [h2] at hm2
      use m - 2 * 10 ^ k
      rw [@solitary_iff _ k, Finset.mem_Ico]
      zify [hm2.left, h2]
      rw [Nat.add_sub_of_le (by exact_mod_cast hm2.left)]
      simp [solitary]
      constructor

      sorry
      omega
      rw [@Nat.sub_pos_iff_lt]
      zify
      have : (m : ℤ) ≠ 2 * 10 ^ k := by
        norm_cast
        -- nicer to have k + 1 here
        rintro rfl
        absurd solitary
        unfold is_solitary
        push Not
        intro h
        use 0, (2 * 10 ^ k)
        simp [has_digit_one, Nat.mul_mod, Nat.pow_mod, Nat.zero_mod, Nat.zero_pow (Nat.ne_zero_iff_zero_lt.mp w)]

        all_goals sorry
      exact hm2.left.lt_of_ne this.symm
      zify [hm2.left]; omega

    -- move inequalities to b

    have (n m : ℤ) : n ≠ m ↔ n - ((10 ^ k : ℤ) - 1) ≠ m - ((10 ^ k : ℤ) - 1) := by simp
    rw [this, sub_sub_sub_cancel_right, two_mul, Int.add_sub_cancel] at hm1
    conv at hm2 => enter [2, 2, 2]; rw [this]


    sorry
  · simp only [Finset.mem_Ico]
    rintro (rfl | ⟨n, ⟨npos, hnk⟩, hn, rfl⟩)
    · exact solitary_form k
    · exact solitary_iff n k npos hnk |>.mp hn

lemma solitary_count (k : ℕ) : Finset.card { x ∈ (Finset.Ico 1 (10^k)) | is_solitary x } = 2 ^ k - 1 := by
  -- #count_heartbeats! 1 in -- 10333
  induction k with
  | zero => simp
  | succ k ih =>
    -- this should really be a calc block...
    have : { x ∈ (Finset.Ico 1 (10^(k + 1))) | is_solitary x }
        = { x ∈ (Finset.Ico 1 (10^k)) | is_solitary x } ∪ { x ∈ (Finset.Ico (10^k) (10^(k+1))) | is_solitary x } := by
      rw [← Finset.filter_union, Finset.Ico_union_Ico_eq_Ico]
      · grind
      · exact Nat.pow_le_pow_right (by decide) (Nat.le_succ _)
    rw [this, Finset.card_union_of_disjoint <| Finset.disjoint_filter_filter <| Finset.Ico_disjoint_Ico_consecutive _ _ _]
    have : {x ∈ Finset.Ico (10 ^ k) (10 ^ (k + 1)) | is_solitary x} =
        {2 * 10 ^ k - 1} ∪ { m ∈ Finset.Ico (10 ^ k) (10 ^ (k + 1)) | ∃ n ∈ Finset.Ico 1 (10 ^ k), is_solitary n ∧ m = 2 * 10 ^ k + n }
          := by
      ext m
      simp only [Finset.mem_filter, Finset.singleton_union, Finset.mem_insert]
      constructor
      · rintro ⟨hm, hm2⟩
        rw [solitary_range hm] at hm2
        simpa [hm] using hm2
      · rintro (rfl | ⟨hm, hm2⟩)
        · grind [solitary_form]
        · simp [solitary_range hm, ↓hm2, hm]
    rw [this, Finset.card_union_of_disjoint (by simp; omega)]
    have : { x ∈ (Finset.Ico 1 (10^k)) | is_solitary x }.card
        = {m ∈ Finset.Ico (10 ^ k) (10 ^ (k + 1)) | ∃ n ∈ Finset.Ico 1 (10 ^ k), is_solitary n ∧ m = 2 * 10 ^ k + n}.card := by
      refine Finset.card_nbij (2 * 10 ^ k + ·) (by intro n; grind) (by simp) (by intro a; simp; grind)
    rw [← this, ih, Finset.card_singleton]
    grind

snip end

problem usa2026_p4 :
    (Finset.filter is_solitary (Finset.Ico 1 (10^2026))).card = solution := by
  apply solitary_count

end Usa2026P4
