/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Liao, hillosanation
-/

module

public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Data.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.List.DropRight

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

open Nat List

lemma digits_def' : ∀ {n : ℕ} (_ : 0 < n), digits 10 n = (n % 10) :: digits 10 (n / 10) :=
  Nat.digits_def' (by decide)

lemma digits_ofDigits (L : List ℕ) (w₁ : ∀ l ∈ L, l < 10) (w₂ : ∀ h : L ≠ [], L.getLast h ≠ 0) : digits 10 (ofDigits 10 L) = L :=
  Nat.digits_ofDigits _ (by decide) L w₁ w₂

lemma digits_ofDigits' (L : List ℕ) (w₁ : ∀ l ∈ L, l < 10)
    : digits 10 (ofDigits 10 L) = rdropWhile (· = 0) L := by
  induction L using reverseRec with
  | nil => simp
  | append_singleton xs x ih =>
    by_cases hx : x = 0
    · subst hx
      rw [rdropWhile_concat_pos _ _ _ rfl, ← ih (fun x mem ↦ w₁ _ <| mem_append_left _ mem), ofDigits_append_zero]
    · rw [rdropWhile_concat_neg _ _ _ (by simp [hx])]
      refine digits_ofDigits _ w₁ fun _ => ?_
      rw [getLast_concat]
      exact hx

lemma not_solitary_two_zeros {k : ℕ} : ¬ is_solitary (2 * 10 ^ k) := by
  rw [is_solitary]
  push Not
  intro _
  use (2 * 10 ^ k), 0
  and_intros
  · rfl
  · induction k with
    | zero => simp [has_digit_one]
    | succ k ih =>
      specialize ih (by omega)
      simp [has_digit_one, mul_mod, Nat.pow_mod]
      rw [Nat.pow_add_one, Nat.mul_div_assoc 2 (Nat.dvd_mul_left _ _), mul_div_left _ (by decide)]
      rwa [has_digit_one] at ih
  · simp [has_digit_one]

lemma digit_squeeze {m k : ℕ} (hm : m ∈ Set.Ico (10 ^ k) (2 * 10 ^ k)) : 1 ∈ digits 10 m := by
  induction k generalizing m with
  | zero =>
    have ⟨_, _⟩ := hm
    interval_cases m
    exact mem_of_elem_eq_true rfl
  | succ k ih =>
    rw [Set.mem_Ico] at hm
    rw [digits_def' (by omega)]
    exact mem_cons_of_mem _ <| @ih (m/10) (by grind)

lemma digits_last_mem {m k : ℕ} (h2 : 10 ^ k ≤ m) (h3 : m / 10 ^ k < 10) : m / (10 ^ k) ∈ digits 10 m := by
  induction k generalizing m with
  | zero =>
    have h1 := calc
      0 < 10 ^ 0 := pos_of_neZero _
      _ ≤ m := h2
    simp only [pow_zero, Nat.div_one]
    rw [digits_def' h1, mod_eq_of_lt (by omega)]
    exact mem_cons_self
  | succ k ih =>
    have h1 := calc
      0 < 10 ^ (k + 1) := pos_of_neZero _
      _ ≤ m := h2
    rw [digits_def' h1]
    refine mem_cons_of_mem _ ?_
    rw [pow_succ', ← Nat.div_div_eq_div_mul]
    exact @ih (m / 10) (by omega) (by rwa [Nat.div_div_eq_div_mul, ← pow_succ'])

lemma zero_lt_mod_ne_zero {a k : ℕ} (ha: a % k ≠ 0) : 0 < a := by
  rw [pos_iff_ne_zero]
  apply_fun (· % k)
  exact ha

lemma digits_div_subset (a k : ℕ) : digits 10 (a % 10 ^ (k + 1)) ⊆ digits 10 a := by
  induction k generalizing a with
  | zero =>
    by_cases! h : a % 10 ^ (0 + 1) = 0
    · simp [↓h]
    rw [digits_def' (by omega)]
    simp
    rw [digits_def' (by omega)]
    exact mem_cons_self
  | succ k ih =>
    by_cases! h : a % 10 ^ (k + 1 + 1) = 0
    · simp [h]
    rw [digits_def' (Nat.ne_zero_iff_zero_lt.mp h)]
    refine cons_subset.mpr ⟨?_, ?_⟩
    · rw [mod_mod_of_dvd]
      · rw [digits_def' (zero_lt_mod_ne_zero h)]
        exact mem_cons_self
      · exact dvd_of_mul_left_eq _ rfl
    · rw [pow_succ, mod_mul_left_div_self, digits_def' (zero_lt_mod_ne_zero h)]
      exact subset_cons_of_subset _ <| ih (a / 10)

lemma chop_off_leading {m k : ℕ} (hm : m ∈ Finset.Ico (10 ^ k) (10 ^ (k + 1)))
    : m = ofDigits 10 ((digits 10 m).take k ++ [m / 10 ^ k]) := by
  rw [Finset.mem_Ico] at hm
  induction k generalizing m with
  | zero =>
    rw [digits_of_lt 10 m (by omega) (by omega)]
    simp
  | succ k ih =>
    rw [digits_def' (by omega), take_succ_cons, cons_append, ofDigits_cons]
    specialize @ih (m / 10) (by omega)
    rw [Nat.div_div_eq_div_mul, ← pow_add_one'] at ih
    rw [← ih]
    omega

lemma solitary_form (k : ℕ) : is_solitary (2 * 10 ^ k - 1) := by
  refine ⟨by grind, fun a b h => ?_⟩
  wlog! w : b ≤ a
  · exact this k b a (by rwa [add_comm]) w.le |>.symm
  have : a ≤ 2 * 10 ^ k - 1 := le.intro h
  exact Or.inl <| digit_squeeze ⟨by omega, (Nat.le_sub_one_iff_lt <| pos_of_neZero _).mp this⟩

lemma solitary_extend {n : ℕ} (hn1 : 0 < n) {k : ℕ} (hn2 : n < 10 ^ k) : is_solitary n ↔ is_solitary (2 * 10 ^ k + n) := by
  contrapose!
  constructor
  · intro hn hm
    unfold is_solitary at hn
    push Not at hn
    rcases hn hn1 with ⟨a, b, rfl, ha, hb⟩
    have ha' : ¬ has_digit_one (a + 2 * 10 ^ k) := by
      have h : (digits 10 a).length ≤ k := (digits_length_le_iff (by decide) a).mpr (by omega)
      rcases Nat.exists_eq_add_of_le h with ⟨l, hl⟩
      rw [mul_comm, has_digit_one, hl, ← digits_append_zeroes_append_digits (by decide) zero_lt_two]
      simpa [has_digit_one] using ha
    have := hm.2 (a + 2 * 10 ^ k) b (by omega)
    lia
  · wlog! hk : k ≠ 0
    · rw [hk] at hn2
      interval_cases n
    intro hm hn
    unfold is_solitary at hm
    push Not at hm
    rcases hm <| Nat.add_pos_right _ hn1 with ⟨a, b, h, ha, hb⟩
    clear hm
    let a' := a % (10 ^ k)
    let b' := b % (10 ^ k)
    set x := a / (10 ^ k) with hxdef
    set y := b / (10 ^ k) with hydef
    -- In this step, AoPS claims `a, b ≠ 1`, but we actually want `x, y ≠ 1`, which we know from a and b not having the digit `1`.
    wlog! w : x ≤ y generalizing a b
    · apply this b a (by rwa [add_comm]) hb ha hydef hxdef w.le
    have sum_le : x + y ≤ 2 := calc
      _ ≤ (a + b) / 10 ^ k := Nat.div_add_div_le_add_div
      _ = (2 * 10 ^ k + n) / 10 ^ k := by rw [h]
      _ = _ := by simp [Nat.add_div, Nat.div_eq_of_lt, Nat.mod_eq_of_lt, hn2]
    have : x ≤ 2 := calc
      _ ≤ a / 10 ^ k + b / 10 ^ k := Nat.le_add_right _ _
      _ ≤ 2 := sum_le
    -- with the constraints above, we can assume the the case of `x = 0, y = 2`.
    interval_cases hx : x
    · have hy : y = 2 := by
        rw [zero_add] at sum_le
        interval_cases hy : y
        · apply_fun (· / 10 ^ k) at h
          rw [add_comm _ n, add_mul_div_right _ _ (pos_of_neZero _)] at h
          simp [Nat.add_div (pos_of_neZero _), ← hxdef, ← hydef, ite_eq_iff] at h
        · absurd hb
          unfold has_digit_one
          rw [hydef]
          refine digits_last_mem ?_ (by rw [← hydef]; decide)
          rw [div_eq_sub_mod_div, eq_div_iff_mul_eq_left (ne_zero_of_lt hn2) (dvd_sub_mod b)] at hydef
          omega
        · rfl
      replace h := calc 2 * 10 ^ k + n
        _ = a + b := h.symm
        _ = 10 ^ k * (a / 10 ^ k) + a % 10 ^ k + 10 ^ k * (b / 10 ^ k) + b % 10 ^ k := by
          simp [div_add_mod, add_assoc]
        _ = 2 * 10 ^ k + (a' + b') := by
          simp [← hxdef, ← hydef, hy, a', b']
          ring
      rw [add_right_inj] at h
      have hab := hn.2 a' b' h.symm
      clear * - ha hb hab hk
      wlog ha' : has_digit_one a' generalizing a b
      · exact this b a hb ha hab.symm <| hab.resolve_left ha'
      clear * - ha' ha hk
      cases k with
      | zero => contradiction
      | succ k => exact ha <| digits_div_subset a k ha'
    · clear hx
      absurd ha
      unfold has_digit_one
      rw [hxdef]
      refine digits_last_mem ?_ (by rw [← hxdef]; decide)
      rw [div_eq_sub_mod_div, eq_div_iff_mul_eq_left (ne_zero_of_lt hn2) (dvd_sub_mod a)] at hxdef
      omega
    · omega

lemma nines (k : ℕ) : 10 ^ k - 1 = ofDigits 10 (replicate k 9) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [add_comm, replicate_add, replicate_one, ofDigits_append]
    simp [← ih]
    grind

abbrev correction (m k : ℕ) :=
  digits 10 (m - (10 ^ k - 1)) |>.map (if · = 1 then 1 else 0) |>.take k |> ofDigits 10

lemma correction_le {m k : ℕ} (hm : m ∈ Finset.Ico (10 ^ k) (10 ^ (k + 1))) : correction m k ≤ ofDigits 10 (replicate k 9) := by
  cases k with
  | zero => rfl
  | succ k =>
    rw [← nines, Nat.le_sub_one_iff_lt <| pos_of_neZero _]
    calc correction m (k + 1)
      _ < 10 ^ _ :=
        ofDigits_lt_base_pow_length (by decide) (by grind)
      _ ≤ 10 ^ (k + 1) := by
        rw [Nat.pow_le_pow_iff_right (by decide)]
        apply length_take_le

lemma nines_sub_correction {m k : ℕ} (hm : m ∈ Finset.Ico (10 ^ k) (10 ^ (k + 1))) : ofDigits 10 (replicate k 9) - correction m k =
    ((take k (digits 10 (m - (10 ^ k - 1))) |>.map (if · = 1 then 8 else 9)) ++ replicate (k - (digits 10 (m - (10 ^ k - 1))).length) 9 |> ofDigits 10) := by
  rw [Nat.sub_eq_iff_eq_add (correction_le hm), correction]
  nth_rw 3 [← @ofDigits_append_replicate_zero _ (k - (digits 10 (m - (10 ^ k - 1))).length)]
  rw [ofDigits_add_ofDigits_eq_ofDigits_zipWith_of_length_eq (by simp)]
  simp [zipWith_append, ← take_zipWith, ite_add_ite]
  congr
  omega

lemma nines_sub_correction_not_has_digit_one {m k : ℕ} (hm : m ∈ Finset.Ico (10 ^ k) (10 ^ (k + 1))) : ¬has_digit_one (10 ^ k - 1 - correction m k) := by
  cases k with
  | zero => simp [has_digit_one]
  | succ k =>
    rw [nines, nines_sub_correction hm]
    simp [has_digit_one]
    rw [digits_ofDigits]
    · refine not_mem_append ?_ (by simp)
      have : 1 ∉ map (fun x ↦ if x = 1 then 8 else 9) (digits 10 (m - (10 ^ (k + 1) - 1))) := by
        simp [mem_map, ite_eq_iff]
      contrapose this
      exact mem_of_mem_take this
    · grind
    intro h -- makes simp a bit quicker
    by_cases h2 : replicate (k + 1 - (digits 10 (m - (10 ^ (k + 1) - 1))).length) 9 = []
    · simp [h2, getLast_take, ite_eq_iff]
    · simp [h2]

lemma mem_digits_split {a k : ℕ} (h : a < 10 ^ k) {b : ℕ} (hb₂ : 0 < b)
    : 1 ∉ digits 10 a ∧ 1 ∉ digits 10 b ↔ 1 ∉ digits 10 (a + 10 ^ k * b) := by
  have := @digits_append_zeroes_append_digits 10 (k - (digits 10 a).length) b a (by decide) hb₂
  rw [Nat.add_sub_of_le <| digits_length_le_iff (by decide) a |>.mpr h] at this
  rw [← this]
  simp

lemma one_not_mem_bumped (m k : ℕ) : 1 ∉
    digits 10 (ofDigits 10 (take k (map (fun a ↦ a + if a = 1 then 1 else 0) (digits 10 (m - (10 ^ k - 1)))))) := by
  rw [digits_ofDigits']
  · rw [rdropWhile, mem_reverse]
    have h := calc
      dropWhile (fun x ↦ decide (x = 0)) (take k (map (fun a ↦ a + if a = 1 then 1 else 0) (digits 10 (m - (10 ^ k - 1))))).reverse
      _ ⊆ reverse _ := dropWhile_subset _
      _ ⊆ _ := reverse_subset.mpr fun ⦃a⦄ ↦ id
    grind
  · intro x hx
    apply mem_of_mem_take at hx
    rw [mem_map] at hx
    obtain ⟨a, mem, rfl⟩ := hx
    have := digits_lt_base (by decide) mem
    split_ifs <;> omega

lemma add_correction_not_has_digit_one {m k : ℕ} (hm : m ∈ Finset.Ico (10 ^ k) (10 ^ (k + 1)))
    (h : ((m - (10 ^ k - 1)) / 10 ^ k) ≠ 1) : ¬has_digit_one (m - (10 ^ k - 1) + correction m k) := by
  rw [has_digit_one, correction]
  by_cases h_mem : m - (10 ^ k - 1) ∈ Finset.Ico (10 ^ k) (10 ^ (k + 1))
  · nth_rw 1 [chop_off_leading h_mem]
    rw [Finset.mem_Ico] at h_mem
    rw [ofDigits_append]
    nth_rw 2 [add_comm]
    rw [add_assoc, ofDigits_add_ofDigits_eq_ofDigits_zipWith_of_length_eq (by simp),
      ← take_zipWith, zipWith_map_right, zipWith_self]
    rw [add_comm, ← mem_digits_split]
    constructor
    · exact one_not_mem_bumped m k
    · rw [digits_ofDigits]
      · grind
      · intro x hx
        rw [mem_singleton] at hx
        obtain ⟨a, mem, rfl⟩ := hx
        rw [Nat.div_lt_iff_lt_mul <| pos_of_neZero _, ← pow_succ']
        exact h_mem.2
      · intro h
        simp_all
    · calc
        _ < 10 ^ _ := by
          refine ofDigits_lt_base_pow_length (by decide) fun x mem => ?_
          apply mem_of_mem_take at mem
          rw [mem_map] at mem
          obtain ⟨x, hx, rfl⟩ := mem
          have := digits_lt_base (by decide) hx
          split_ifs <;> omega
        _ ≤ _ := Nat.pow_le_pow_right (Nat.zero_lt_succ _) (by simp)
    · simp_all
  · replace h_mem : m - (10 ^ k - 1) < 10 ^ k := by
      rw [Finset.mem_Ico] at h_mem hm
      omega
    have length := digits_length_le_iff (by decide) _ |>.mpr h_mem
    nth_rw 1 [← ofDigits_digits 10 (m - _)]
    rw [ofDigits_add_ofDigits_eq_ofDigits_zipWith_of_length_eq (by simp [length])]
    nth_rw 1 [take_self_eq_iff _ |>.mpr length]
    rw [← take_zipWith, zipWith_map_right, zipWith_self]
    exact one_not_mem_bumped m k

-- by lemma 2, we know that 2 is not the leading digit of m
lemma leading_ne_one {m k : ℕ} (solitary : is_solitary m)
  (hm : m ∈ Finset.Ico (10 ^ k) (10 ^ (k + 1))) (hm1 : m ≠ 2 * 10 ^ k - 1)
  (hm2 : ∀ n ∈ Finset.Ico 1 (10 ^ k), is_solitary n → m ≠ 2 * 10 ^ k + n)
    : (m - (10 ^ k - 1)) / 10 ^ k ≠ 1 := by
  rw [Finset.mem_Ico] at hm
  have m_ne : m ≠ 2 * 10 ^ k := by
    contrapose solitary with h
    rw [h]
    exact not_solitary_two_zeros
  have : m < 2 * 10 ^ k ∨ (3 * 10 ^ k) ≤ m := by
    contrapose! hm2
    use m - 2 * 10 ^ k
    rw [@solitary_extend _ (by lia) k (by lia), Finset.mem_Ico, add_sub_of_le hm2.left]
    lia
  -- move inequalities to b
  replace : m - (10 ^ k - 1) < 10 ^ k ∨ 2 * 10 ^ k < m - (10 ^ k - 1) := by lia
  rcases this with this | this
  · rw [← Nat.div_lt_one_iff (pos_of_neZero _)] at this
    exact Ne.symm (Nat.ne_of_lt' this)
  · suffices h : 2 ≤ (m - (10 ^ k - 1)) / 10 ^ k from Nat.ne_of_lt' h
    rw [Nat.le_div_iff_mul_le (pos_of_neZero _)]
    exact this.le

lemma solitary_iff {m k : ℕ} (hm : m ∈ Finset.Ico (10 ^ k) (10 ^ (k + 1))) :
    is_solitary m ↔ m = 2 * 10 ^ k - 1 ∨ (∃ n ∈ Finset.Ico 1 (10 ^ k), is_solitary n ∧ m = 2 * 10 ^ k + n) := by
  constructor
  · contrapose!
    rintro ⟨hm1, hm2⟩ solitary
    -- nudge all ones in b by taking from a
    absurd solitary
    unfold is_solitary
    push Not
    intro _
    let corr := correction m k
    use 10 ^ k - 1 - corr, m - (10 ^ k - 1) + corr
    and_intros
    · rw [Finset.mem_Ico] at hm
      rw [Nat.add_left_comm, Nat.sub_add_cancel ?_, Nat.sub_add_cancel (by omega)]
      rw [← Finset.mem_Ico] at hm
      rw [nines]
      exact correction_le hm
    · exact nines_sub_correction_not_has_digit_one hm
    · refine add_correction_not_has_digit_one hm
        <| leading_ne_one solitary hm hm1 hm2
  · simp only [Finset.mem_Ico]
    rintro (rfl | ⟨n, ⟨npos, hnk⟩, hn, rfl⟩)
    · exact solitary_form k
    · exact solitary_extend npos hnk |>.mp hn

lemma solitary_count (k : ℕ) : Finset.card { x ∈ Finset.Ico 1 (10^k) | is_solitary x } = 2 ^ k - 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    -- this should really be a calc block...
    have : { x ∈ (Finset.Ico 1 (10^(k + 1))) | is_solitary x }
        = { x ∈ (Finset.Ico 1 (10^k)) | is_solitary x } ∪ { x ∈ (Finset.Ico (10^k) (10^(k+1))) | is_solitary x } := by
      rw [← Finset.filter_union, Finset.Ico_union_Ico_eq_Ico]
      · exact one_le_pow' _ _
      · exact Nat.pow_le_pow_right (by decide) (Nat.le_succ _)
    rw [this, Finset.card_union_of_disjoint <| Finset.disjoint_filter_filter <| Finset.Ico_disjoint_Ico_consecutive ..]
    clear this
    have : {x ∈ Finset.Ico (10 ^ k) (10 ^ (k + 1)) | is_solitary x} =
        {2 * 10 ^ k - 1} ∪ { m ∈ Finset.Ico (10 ^ k) (10 ^ (k + 1)) | ∃ n ∈ Finset.Ico 1 (10 ^ k), is_solitary n ∧ m = 2 * 10 ^ k + n }
          := by
      ext m
      simp only [Finset.mem_filter, Finset.singleton_union, Finset.mem_insert]
      constructor
      · rintro ⟨hm, hm2⟩
        rw [solitary_iff hm] at hm2
        simpa [hm] using hm2
      · rintro (rfl | ⟨hm, hm2⟩)
        · grind [solitary_form]
        · simp [solitary_iff hm, ↓hm2, hm]
    rw [this, Finset.card_union_of_disjoint (by grind [Finset.disjoint_singleton_left])]
    clear this
    have : { x ∈ (Finset.Ico 1 (10^k)) | is_solitary x }.card
        = {m ∈ Finset.Ico (10 ^ k) (10 ^ (k + 1)) | ∃ n ∈ Finset.Ico 1 (10 ^ k), is_solitary n ∧ m = 2 * 10 ^ k + n}.card :=
        Finset.card_nbij (2 * 10 ^ k + ·) (by intro n; grind) (by simp) (by intro a; simp; grind)
    grind

snip end

problem usa2026_p4 :
    (Finset.filter is_solitary (Finset.Ico 1 (10^2026))).card = solution := by
  apply solitary_count

end Usa2026P4
